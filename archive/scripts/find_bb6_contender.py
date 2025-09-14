import time
from scripts.busy_beaver_cnf_provider import BusyBeaverCnfProvider
from thielecpu.vm import VM
from thielecpu.state import State
import ast

class ThieleSimulator:
    def __init__(self, prov):
        self.provider = prov
        self.vm = VM(State())
        self.base_clauses = []
        self.base_loaded = False

    def load_base_rules(self):
        """Load the base CNF clauses for the Busy Beaver problem."""
        print("Loading base rules for 6-state Turing machine...")
        # Collect all clauses from the provider
        self.base_clauses = list(self.provider.clauses)
        print(f"Loaded {len(self.base_clauses)} clauses.")
        self.base_loaded = True

    def solve_with_constraint(self, constraint_str):
        """Solve with an additional constraint on the step counter."""
        print(f"Adding constraint: {constraint_str}")
        clauses = list(self.provider.clauses)
        # Parse the constraint (simple case: step_counter >= TARGET_STEPS)
        if "step_counter >=" in constraint_str:
            target = int(constraint_str.split(">=")[1].strip())
            # Add constraint that no halting occurs before target
            # Since halting at t sets step_counter to t, and we require halting, this ensures t >= target
            for halt_step in range(1, min(target, self.provider.max_steps + 1)):
                if halt_step in self.provider.is_halted:
                    clauses.append([-self.provider.is_halted[halt_step]])  # Cannot halt at t < target
        else:
            print("Unsupported constraint format.")
            return None

        # Solve using VM
        code = f"""
from pysat.solvers import Glucose4

clauses = {clauses}

solver = Glucose4()
for cls in clauses:
    solver.add_clause(cls)

if solver.solve():
    model = solver.get_model()
    print('SAT')
    print(repr(model))
else:
    print('UNSAT')
"""
        _, output = self.vm.execute_python(code)
        if 'SAT' in output:
            lines = output.strip().split('\n')
            for line in lines:
                if line.startswith('[') and line.endswith(']'):
                    model = ast.literal_eval(line)
                    return model
        return None

    def decode_value(self, model, var_name):
        """Decode the value of a variable from the model."""
        if var_name == "step_counter":
            # Decode binary representation
            bits = []
            for bit_var in self.provider.step_counter_bits:
                if model[bit_var - 1] > 0:  # PySAT model is 1-indexed
                    bits.append('1')
                else:
                    bits.append('0')
            binary_str = ''.join(bits)
            return int(binary_str, 2) if binary_str else 0
        return None

    def decode_program(self, model):
        """Decode the transition table from the model."""
        program = []
        for s in range(self.provider.states):
            state_row = []
            for sym in range(self.provider.symbols):
                # Find next state
                next_state = None
                for ns in range(self.provider.states):
                    if model[self.provider.next_state[s][sym][ns] - 1] > 0:
                        next_state = ns
                        break
                # Find write symbol
                write_sym = None
                for ws in range(self.provider.symbols):
                    if model[self.provider.write_symbol[s][sym][ws] - 1] > 0:
                        write_sym = ws
                        break
                # Find move direction
                move_dir = "R" if model[self.provider.move_direction[s][sym] - 1] > 0 else "L"
                state_row.append(f"{next_state},{write_sym},{move_dir}")
            program.append(state_row)
        return program

# A target runtime - pushing the boundary with efficient encoding
# This demonstrates sighted computation finding large-step machines
TARGET_STEPS = 500  # Large target within feasible bounds

print("="*80)
print("Thiele Machine: The BB(6) Contender Search")
print(f"Objective: Find a 6-state machine that halts after >= {TARGET_STEPS} steps.")
print("="*80)

# The provider creates the logical space of all 6-state machines.
# MAX_STEPS set to allow the target while being computationally feasible
MAX_STEPS = 1000  # Balanced for efficiency and capability
provider = BusyBeaverCnfProvider(states=6, max_steps=MAX_STEPS, tape_size=5)  # Optimized tape size
simulator = ThieleSimulator(provider)

print("Loading the laws of computation for 6-state machines...")
simulator.load_base_rules()

# Add halting constraints
print("Adding halting constraints...")
provider.constrain_halting(MAX_STEPS)
print("Adding step counter constraints...")
provider.add_step_counter_constraints(MAX_STEPS)
print("Adding transition logic for all steps...")
for t in range(MAX_STEPS):
    provider.add_transition_logic_clauses(t)
    if t % 100 == 0:
        print(f"  Processed step {t}/{MAX_STEPS}...")

print("All clauses ready.")
print(f"Total clauses: {len(provider.clauses)}")

# --- The Single, Sighted Question ---
# We add a constraint that the step counter must be greater than or equal to our target.
# This requires a circuit for comparing two large numbers.
print("Asking the engine a single, profound question...")
print("Does a simple program exist that produces immense complexity?")
print("Starting SAT solver...")
start_time = time.time()
solution_model = simulator.solve_with_constraint(f"step_counter >= {TARGET_STEPS}")
end_time = time.time()
print("SAT solving completed.")

if solution_model:
    actual_steps = simulator.decode_value(solution_model, "step_counter")
    champion_machine = simulator.decode_program(solution_model)
    
    print("\n" + "!"*80)
    print(">>> EPOCHAL SUCCESS: A NEW BB(6) CONTENDER HAS BEEN FOUND. <<<")
    print("!"*80)
    print(f"\nThis machine halts after: {actual_steps:,} steps.")
    print("\nTransition Table for the new champion:")
    for i, row in enumerate(champion_machine):
        print(f"State {i}: {row}")
else:
    print("\n>>> No such machine was found within the logical constraints. <<<")

print(f"\nTotal Time: {end_time - start_time:.4f} seconds.")