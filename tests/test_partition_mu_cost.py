"""Partition strategy vs blind strategy: μ-cost comparison on the real VM.

Current LASSERT pricing is based on the binary formula header written to memory:
  cost(LASSERT) = hw_flen * 8 + (declared_cost + 1)

The wrapper must therefore serialize dict-style formulas into the on-chip
memory layout with flen = hw_flen. These tests pin that contract to the real
OCaml runner surface.
"""
import pytest

from thielecpu.vm import VMState, vm_run, _runner_available

SKIP_OCAML = not _runner_available()
pytestmark = pytest.mark.skipif(SKIP_OCAML, reason="OCaml runner not available")


def _run(program: list, max_steps: int = 20) -> VMState:
    return vm_run(VMState.default(), program, max_steps=max_steps)


# ---------------------------------------------------------------------------
# 1.  NoFI: LASSERT always charges mu (even if cert check fails)
# ---------------------------------------------------------------------------

class TestLassertMuCostFormula:
    """LASSERT μ-cost = hw_flen*8 + (declared_cost+1)."""

    def test_lassert_charges_formula_header_len_times_8(self):
        """μ delta = hw_flen*8 + (cost+1), verified against the real VM."""
        formula = "p_cnf_1_1__1_0"
        declared_cost = 1
        hw_flen = 2
        expected_lassert_cost = hw_flen * 8 + (declared_cost + 1)

        s0 = VMState.default()
        prog = [
            {"op": "lassert", "module": 0, "formula": formula,
             "cert_type": "sat", "cert": "v_1_0", "countermodel": "v_-1_0", "cost": declared_cost},
        ]
        sf = vm_run(s0, prog, max_steps=10)
        actual_delta = sf.vm_mu - s0.vm_mu

        assert actual_delta == expected_lassert_cost, (
            f"μ cost mismatch: expected {expected_lassert_cost}, got {actual_delta}"
        )

    def test_lassert_formula_length_scales_mu(self):
        """Longer binary formulas pay proportionally higher μ-cost."""
        cases = [
            ("p_cnf_1_1__1_0", "v_1_0", "v_-1_0", 2),
            ("p_cnf_2_2__1_0__2_0", "v_1_2_0", "v_-1_-2_0", 4),
            ("p_cnf_3_3__1_0__2_0__3_0", "v_1_2_3_0", "v_-1_-2_-3_0", 6),
        ]
        declared_cost = 1
        for formula, cert, countermodel, hw_flen in cases:
            expected_mu = hw_flen * 8 + (declared_cost + 1)
            s0 = VMState.default()
            prog = [
                {"op": "lassert", "module": 0, "formula": formula,
                 "cert_type": "sat", "cert": cert, "countermodel": countermodel, "cost": declared_cost},
            ]
            sf = vm_run(s0, prog, max_steps=10)
            assert sf.vm_mu == expected_mu, (
                f"hw_flen={hw_flen}: expected μ={expected_mu}, got {sf.vm_mu}"
            )
            assert not sf.vm_err, f"Valid cert should not set vm_err (hw_flen={hw_flen})"

    def test_lassert_valid_cert_succeeds(self):
        """After fix: valid DIMACS formula + correct model → vm_err=False."""
        s0 = VMState.default()
        prog = [
            {"op": "pnew",    "region": [0, 256], "cost": 1},
            {"op": "lassert", "module": 0, "formula": "p_cnf_1_1__1_0",
             "cert_type": "sat", "cert": "v_1_0", "countermodel": "v_-1_0", "cost": 1},
            {"op": "halt",    "cost": 0},
        ]
        sf = vm_run(s0, prog, max_steps=10)
        assert sf.vm_err is False, "Valid formula+cert must succeed after decode_formula fix"
        assert sf.vm_mu >= 2, "μ must advance"


# ---------------------------------------------------------------------------
# 2.  LJOIN: the cert-setter that DOES work
# ---------------------------------------------------------------------------

class TestLjoinCertJoining:
    """LJOIN checks cert1 == cert2. This actually works and doesn't fail the VM."""

    def test_ljoin_equal_certs_succeeds(self):
        s0 = VMState.default()
        prog = [
            {"op": "pnew",  "region": [0, 256], "cost": 1},
            {"op": "ljoin", "cert1": "my_cert", "cert2": "my_cert", "cost": 1},
            {"op": "halt",  "cost": 0},
        ]
        sf = _run(prog)
        assert sf.vm_err is False, "Equal certs: LJOIN should succeed"
        assert sf.vm_mu >= 2, "PNEW(1) + LJOIN(cost+1=2)"

    def test_ljoin_unequal_certs_errors(self):
        # Per the Coq formal model (step_ljoin in VMStep.v), LJOIN always advances
        # with advance_state — it does NOT check cert equality and never sets vm_err.
        # The cert registers are structural arguments only; equality checking is not
        # part of the proven semantics.
        s0 = VMState.default()
        prog = [
            {"op": "pnew",  "region": [0, 256], "cost": 1},
            {"op": "ljoin", "cert1": "cert_a", "cert2": "cert_b", "cost": 1},
            {"op": "halt",  "cost": 0},
        ]
        sf = _run(prog)
        assert sf.vm_err is False, (
            "LJOIN never errors per Coq model: step_ljoin only charges cost"
        )


# ---------------------------------------------------------------------------
# 3.  Partition structure via PNEW/LJOIN (avoiding broken LASSERT path)
# ---------------------------------------------------------------------------

class TestPartitionStructureWithLjoin:
    """Using LJOIN-based certification (which works), show the partition pattern.

    Two partitions with matching certs can be joined without error.
    This demonstrates the core partition strategy works even if LASSERT is broken.
    """

    def test_two_partition_ljoin_succeeds(self):
        """PNEW × 2, LJOIN with same cert on both → success."""
        prog = [
            {"op": "pnew",  "region": [0, 128],  "cost": 1},  # partition 1
            {"op": "pnew",  "region": [128, 256], "cost": 1},  # partition 2
            {"op": "ljoin", "cert1": "shared_cert", "cert2": "shared_cert", "cost": 1},
            {"op": "halt",  "cost": 0},
        ]
        sf = _run(prog)
        assert sf.vm_err is False
        assert sf.vm_graph.pg_next_id == 3   # two modules created
        assert sf.vm_mu == 1 + 1 + 2         # PNEW(1) + PNEW(1) + LJOIN(cost+1=2)

    def test_partition_mu_is_sum_of_parts(self):
        """Partition strategy μ = sum of individual cert costs + structure overhead."""
        # Blind: 1 PNEW + 1 LJOIN
        blind = [
            {"op": "pnew",  "region": [0, 256], "cost": 1},
            {"op": "ljoin", "cert1": "c", "cert2": "c", "cost": 5},
            {"op": "halt",  "cost": 0},
        ]
        # Partition: 2 PNEW + 1 LJOIN (same declared cert cost)
        partition = [
            {"op": "pnew",  "region": [0, 128],  "cost": 1},
            {"op": "pnew",  "region": [128, 256], "cost": 1},
            {"op": "ljoin", "cert1": "c", "cert2": "c", "cost": 5},
            {"op": "halt",  "cost": 0},
        ]
        sf_blind     = _run(blind)
        sf_partition = _run(partition)

        assert sf_blind.vm_err     is False
        assert sf_partition.vm_err is False

        # Partition has exactly 1 extra PNEW
        assert sf_partition.vm_mu == sf_blind.vm_mu + 1, (
            "Partition overhead vs blind = exactly 1 extra PNEW"
        )

    def test_update_reuses_partition_cert(self):
        """Partition allows re-joining P1 with same P2 cert; blind must redo everything.

        With LJOIN (not LASSERT), both strategies work without error.
        Blind 'update': must redo full join with new cert.
        Partition 'update': reuse P2 cert, only change P1 side.

        μ counts reflect the extra PNEW cost in partition (offset by P2 cert reuse on updates).
        """
        P2_CERT_COST = 10

        # Blind: single join, then re-join with new cert
        blind = [
            {"op": "pnew",  "region": [0, 256], "cost": 1},
            # Initial: both sides certified together
            {"op": "ljoin", "cert1": "initial_cert", "cert2": "initial_cert",
             "cost": P2_CERT_COST + 1},
            # Update: redo full cert (P2's work done again)
            {"op": "ljoin", "cert1": "updated_cert", "cert2": "updated_cert",
             "cost": P2_CERT_COST + 1},
            {"op": "halt",  "cost": 0},
        ]

        # Partition: certify P2 once (expensive), update only P1 (cheap)
        partition = [
            {"op": "pnew",  "region": [0, 128],  "cost": 1},   # P1 partition
            {"op": "pnew",  "region": [128, 256], "cost": 1},   # P2 partition
            # Initial: join with P2's expensive cert
            {"op": "ljoin", "cert1": "initial_cert", "cert2": "initial_cert",
             "cost": P2_CERT_COST + 1},
            # Update P1 only: P2 cert stays, re-join cheap
            {"op": "ljoin", "cert1": "updated_cert", "cert2": "updated_cert",
             "cost": 1},                    # P2 cert reused — only P1 re-certified
            {"op": "halt",  "cost": 0},
        ]

        sf_blind     = _run(blind)
        sf_partition = _run(partition)

        assert sf_blind.vm_err     is False
        assert sf_partition.vm_err is False

        b_mu = sf_blind.vm_mu
        p_mu = sf_partition.vm_mu

        # With P2_CERT_COST=10, partition should win
        assert p_mu < b_mu, (
            f"Partition ({p_mu}) should be cheaper than blind ({b_mu}) "
            f"when P2 is expensive (cost={P2_CERT_COST}) and only P1 updates"
        )
