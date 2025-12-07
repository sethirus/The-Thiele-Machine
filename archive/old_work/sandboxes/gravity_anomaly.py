# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""Toy two-body simulation using time-dilation from µ-density as gravity.

This version removes the Newtonian force shortcut. Mass is still derived from
the VM µ-ledger (irreversible opcode count), but "gravity" emerges from
gradients of local processing load (time dilation): regions with higher µ slow
time, so trajectories refract towards them. The cold body runs a reversible
XOR loop (zero µ cost), while the hot body runs an EMIT loop (positive µ cost
per step) so it naturally becomes a time-slowing attractor.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Iterable, List

from thielecpu.isa import Opcode, decode, encode

# Reversible ops are free; irreversible ops charge one bit of µ in this toy
# mapping from instruction semantics to thermodynamic weight. This mirrors the
# MuLedgerConservation convention where EMIT (and other irreversible effects)
# pay at least one bit.
INSTRUCTION_COSTS = {
    Opcode.XOR_SWAP: 0.0,
    Opcode.XOR_ADD: 0.0,
    Opcode.EMIT: 1.0,
    Opcode.HALT: 0.0,
}

TIME_STEP = 0.1
# Weak-field time-dilation scaling: tau = 1 / (1 + ALPHA * Phi)
ALPHA = 1.0


@dataclass
class Body:
    name: str
    x: float
    y: float
    vx: float
    vy: float
    mu_mass: float
    program: bytes
    pc: int = 0
    mu: float = 0.0

    @property
    def base_mass(self) -> float:
        return 1.0

    def pos(self) -> tuple[float, float]:
        return (self.x, self.y)

    def step_program(self) -> None:
        """Execute one instruction from the program and update µ-derived mass."""

        if not self.program:
            return

        pc = self.pc % (len(self.program) // 4)
        word = self.program[pc * 4 : pc * 4 + 4]
        op, _a, _b = decode(word)
        self.pc = pc + 1

        # Add µ strictly from opcode irreversibility; operands do not inject
        # arbitrary mass.
        self.mu += INSTRUCTION_COSTS.get(op, 0.0)

        if op == Opcode.HALT:
            # Hold position on HALT but keep mass derived from whatever µ accrued
            self.pc = pc  # freeze the PC

        # Mass is base + ledger
        self.mu_mass = self.base_mass + self.mu


def compute_potential(x: float, y: float, bodies: Iterable[Body], exclude: Body | None = None) -> float:
    """Compute the µ-density scalar field Phi at (x, y)."""

    phi = 0.0
    for body in bodies:
        if body is exclude:
            continue
        dx = x - body.x
        dy = y - body.y
        dist = math.hypot(dx, dy)
        # Softened potential to avoid singularities
        phi += body.mu_mass / (dist + 0.1)
    return phi


def time_dilation(x: float, y: float, bodies: Iterable[Body], exclude: Body | None = None) -> float:
    phi = compute_potential(x, y, bodies, exclude=exclude)
    return 1.0 / (1.0 + ALPHA * phi)


def step(bodies: Iterable[Body]) -> None:
    body_list = list(bodies)

    # 1) Run programs to update µ and derived masses
    for body in body_list:
        body.step_program()

    # 2) Follow gradients of the time-dilation field (weak-field limit)
    epsilon = 0.01
    for body in body_list:
        tau_center = time_dilation(body.x, body.y, body_list, exclude=body)
        tau_x = time_dilation(body.x + epsilon, body.y, body_list, exclude=body)
        tau_y = time_dilation(body.x, body.y + epsilon, body_list, exclude=body)

        grad_tau_x = (tau_x - tau_center) / epsilon
        grad_tau_y = (tau_y - tau_center) / epsilon

        # Geodesics curve toward slower-time regions; in this toy model the
        # acceleration follows the gradient of the refractive index n = 1/tau.
        accel_x = -grad_tau_x
        accel_y = -grad_tau_y

        body.vx += accel_x * TIME_STEP
        body.vy += accel_y * TIME_STEP
        body.x += body.vx * TIME_STEP
        body.y += body.vy * TIME_STEP


def simulate(steps: int = 200) -> list[Body]:
    # Cold: reversible XOR_SWAP loop (cost-free)
    cold_program_words: List[bytes] = [encode(Opcode.XOR_SWAP, 0, 0)]
    cold = Body(
        name="cold",
        x=-1.0,
        y=0.0,
        vx=0.0,
        vy=0.0,
        mu_mass=1.0,
        program=b"".join(cold_program_words),
    )

    # Hot: EMIT loop that burns µ (cost 1 per step) to grow mass linearly
    hot_program_words: List[bytes] = [encode(Opcode.EMIT, 0, 0)]
    hot = Body(
        name="hot",
        x=1.0,
        y=0.0,
        vx=0.0,
        vy=0.0,
        mu_mass=1.0,
        program=b"".join(hot_program_words),
    )

    bodies = [cold, hot]
    for _ in range(steps):
        step(bodies)
    return bodies


if __name__ == "__main__":
    final_bodies = simulate()
    for body in final_bodies:
        r = math.hypot(body.x, body.y)
        print(
            f"{body.name}: pos=({body.x:.3f}, {body.y:.3f}), "
            f"vel=({body.vx:.3f}, {body.vy:.3f}), r={r:.3f}"
        )
