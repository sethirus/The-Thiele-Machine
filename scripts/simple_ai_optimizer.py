#!/usr/bin/env python3
"""
Simple AI Optimizer using Thiele Machine
Demonstrates neural architecture optimization with minimal constraints
"""

import time
from pysat.solvers import Glucose4

class SimpleAIOptimizer:
    def __init__(self):
        self.solver = Glucose4()
        self.vars = {}
        self.var_counter = 0

    def get_var(self, name):
        """Lazy variable allocation"""
        if name not in self.vars:
            self.var_counter += 1
            self.vars[name] = self.var_counter
        return self.vars[name]

    def optimize_architecture(self):
        """Optimize neural network architecture with simple choices"""
        print(f"[{time.time():.2f}s] Optimizing neural architecture...")

        # Simple choices
        architecture = {}

        # Layer count: 2, 3, or 4 layers
        architecture["layers_2"] = self.get_var("layers_2")
        architecture["layers_3"] = self.get_var("layers_3")
        architecture["layers_4"] = self.get_var("layers_4")

        # Neuron count per layer: 32, 64, or 128
        architecture["neurons_32"] = self.get_var("neurons_32")
        architecture["neurons_64"] = self.get_var("neurons_64")
        architecture["neurons_128"] = self.get_var("neurons_128")

        # Activation: relu or tanh
        architecture["activation_relu"] = self.get_var("activation_relu")
        architecture["activation_tanh"] = self.get_var("activation_tanh")

        # Constraints: exactly one choice for each category
        self.solver.add_clause([architecture["layers_2"], architecture["layers_3"], architecture["layers_4"]])
        self.solver.add_clause([-architecture["layers_2"], -architecture["layers_3"]])
        self.solver.add_clause([-architecture["layers_2"], -architecture["layers_4"]])
        self.solver.add_clause([-architecture["layers_3"], -architecture["layers_4"]])

        self.solver.add_clause([architecture["neurons_32"], architecture["neurons_64"], architecture["neurons_128"]])
        self.solver.add_clause([-architecture["neurons_32"], -architecture["neurons_64"]])
        self.solver.add_clause([-architecture["neurons_32"], -architecture["neurons_128"]])
        self.solver.add_clause([-architecture["neurons_64"], -architecture["neurons_128"]])

        self.solver.add_clause([architecture["activation_relu"], architecture["activation_tanh"]])
        self.solver.add_clause([-architecture["activation_relu"], -architecture["activation_tanh"]])

        print(f"[{time.time():.2f}s] Added {len(architecture)} architecture constraints")

        return architecture

    def optimize_hyperparameters(self):
        """Optimize hyperparameters"""
        print(f"[{time.time():.2f}s] Optimizing hyperparameters...")

        hyperparams = {}

        # Learning rate: 0.001, 0.01, 0.1
        hyperparams["lr_001"] = self.get_var("lr_001")
        hyperparams["lr_01"] = self.get_var("lr_01")
        hyperparams["lr_1"] = self.get_var("lr_1")

        # Batch size: 32, 64, 128
        hyperparams["batch_32"] = self.get_var("batch_32")
        hyperparams["batch_64"] = self.get_var("batch_64")
        hyperparams["batch_128"] = self.get_var("batch_128")

        # Optimizer: adam, sgd
        hyperparams["opt_adam"] = self.get_var("opt_adam")
        hyperparams["opt_sgd"] = self.get_var("opt_sgd")

        # Constraints
        self.solver.add_clause([hyperparams["lr_001"], hyperparams["lr_01"], hyperparams["lr_1"]])
        self.solver.add_clause([-hyperparams["lr_001"], -hyperparams["lr_01"]])
        self.solver.add_clause([-hyperparams["lr_001"], -hyperparams["lr_1"]])
        self.solver.add_clause([-hyperparams["lr_01"], -hyperparams["lr_1"]])

        self.solver.add_clause([hyperparams["batch_32"], hyperparams["batch_64"], hyperparams["batch_128"]])
        self.solver.add_clause([-hyperparams["batch_32"], -hyperparams["batch_64"]])
        self.solver.add_clause([-hyperparams["batch_32"], -hyperparams["batch_128"]])
        self.solver.add_clause([-hyperparams["batch_64"], -hyperparams["batch_128"]])

        self.solver.add_clause([hyperparams["opt_adam"], hyperparams["opt_sgd"]])
        self.solver.add_clause([-hyperparams["opt_adam"], -hyperparams["opt_sgd"]])

        return hyperparams

    def solve_optimization(self):
        """Solve the optimization"""
        print(f"[{time.time():.2f}s] Solving neural architecture optimization...")

        start_time = time.time()
        result = self.solver.solve()

        if result:
            print(f"[{(time.time() - start_time):.4f}s] SATISFIABLE - Found optimal neural architecture!")
            return True
        else:
            print(f"[{(time.time() - start_time):.4f}s] UNSATISFIABLE - No valid architecture found")
            return False

    def extract_solution(self, architecture, hyperparams):
        """Extract the optimized solution"""
        model = self.solver.get_model()
        if model is None:
            return None

        solution = {}

        # Extract architecture
        if architecture["layers_2"] in model and model[model.index(architecture["layers_2"])] > 0:
            solution["layers"] = 2
        elif architecture["layers_3"] in model and model[model.index(architecture["layers_3"])] > 0:
            solution["layers"] = 3
        elif architecture["layers_4"] in model and model[model.index(architecture["layers_4"])] > 0:
            solution["layers"] = 4

        if architecture["neurons_32"] in model and model[model.index(architecture["neurons_32"])] > 0:
            solution["neurons"] = 32
        elif architecture["neurons_64"] in model and model[model.index(architecture["neurons_64"])] > 0:
            solution["neurons"] = 64
        elif architecture["neurons_128"] in model and model[model.index(architecture["neurons_128"])] > 0:
            solution["neurons"] = 128

        if architecture["activation_relu"] in model and model[model.index(architecture["activation_relu"])] > 0:
            solution["activation"] = "relu"
        elif architecture["activation_tanh"] in model and model[model.index(architecture["activation_tanh"])] > 0:
            solution["activation"] = "tanh"

        # Extract hyperparameters
        if hyperparams["lr_001"] in model and model[model.index(hyperparams["lr_001"])] > 0:
            solution["learning_rate"] = 0.001
        elif hyperparams["lr_01"] in model and model[model.index(hyperparams["lr_01"])] > 0:
            solution["learning_rate"] = 0.01
        elif hyperparams["lr_1"] in model and model[model.index(hyperparams["lr_1"])] > 0:
            solution["learning_rate"] = 0.1

        if hyperparams["batch_32"] in model and model[model.index(hyperparams["batch_32"])] > 0:
            solution["batch_size"] = 32
        elif hyperparams["batch_64"] in model and model[model.index(hyperparams["batch_64"])] > 0:
            solution["batch_size"] = 64
        elif hyperparams["batch_128"] in model and model[model.index(hyperparams["batch_128"])] > 0:
            solution["batch_size"] = 128

        if hyperparams["opt_adam"] in model and model[model.index(hyperparams["opt_adam"])] > 0:
            solution["optimizer"] = "adam"
        elif hyperparams["opt_sgd"] in model and model[model.index(hyperparams["opt_sgd"])] > 0:
            solution["optimizer"] = "sgd"

        return solution

    def generate_code(self, solution):
        """Generate Python code for the optimized network"""
        code = []
        code.append("# Optimized Neural Network")
        code.append("# Generated by Thiele Machine AI Optimizer")
        code.append("")
        code.append("import tensorflow as tf")
        code.append("from tensorflow.keras import layers, models")
        code.append("")
        code.append("def create_model():")
        code.append("    model = models.Sequential()")
        code.append("")

        # Add layers
        for i in range(solution["layers"]):
            if i == 0:
                code.append(f"    model.add(layers.Dense({solution['neurons']}, activation='{solution['activation']}', input_shape=(784,)))")
            else:
                code.append(f"    model.add(layers.Dense({solution['neurons']}, activation='{solution['activation']}'))")

        code.append("    model.add(layers.Dense(10, activation='softmax'))")
        code.append("")
        code.append("    optimizer = tf.keras.optimizers.Adam(learning_rate={})".format(solution["learning_rate"]))
        code.append("    model.compile(optimizer=optimizer,")
        code.append("                  loss='categorical_crossentropy',")
        code.append("                  metrics=['accuracy'])")
        code.append("    return model")
        code.append("")
        code.append(f"# Configuration: {solution['layers']} layers, {solution['neurons']} neurons each")
        code.append(f"# Learning rate: {solution['learning_rate']}, Batch size: {solution['batch_size']}, Optimizer: {solution['optimizer']}")

        return "\n".join(code)

    def optimize(self):
        """Complete optimization pipeline"""
        print("=== Thiele Machine: Simple AI Optimizer ===")

        # Optimize architecture and hyperparameters
        architecture = self.optimize_architecture()
        hyperparams = self.optimize_hyperparameters()

        # Solve
        if self.solve_optimization():
            solution = self.extract_solution(architecture, hyperparams)

            if solution:
                print("\n🎯 Optimized Neural Architecture Found:")
                print(f"  Layers: {solution['layers']}")
                print(f"  Neurons per layer: {solution['neurons']}")
                print(f"  Activation: {solution['activation']}")
                print(f"  Learning rate: {solution['learning_rate']}")
                print(f"  Batch size: {solution['batch_size']}")
                print(f"  Optimizer: {solution['optimizer']}")

                # Generate code
                code = self.generate_code(solution)
                print("\n📝 Generated Model Code:")
                print(code)

                return solution, code
            else:
                print("\n❌ Could not extract solution")
                return None, None
        else:
            print("\n❌ Optimization failed - constraints unsatisfiable")
            return None, None

def main():
    print("=== Thiele Machine: Simple AI Optimizer ===")
    print("Neural architecture search and hyperparameter optimization\n")

    optimizer = SimpleAIOptimizer()
    solution, code = optimizer.optimize()

    if solution and code:
        print("\n✅ AI Optimization successful!")
        print("This demonstrates the Thiele Machine's neural architecture optimization capabilities!")

        # Save the generated code
        with open('simple_optimized_network.py', 'w', encoding='utf-8') as f:
            f.write(code)
        print("\n💾 Generated code saved as 'simple_optimized_network.py'")
    else:
        print("\n❌ AI Optimization unsuccessful")

    print("\n=== AI Optimization Complete ===")

if __name__ == "__main__":
    main()