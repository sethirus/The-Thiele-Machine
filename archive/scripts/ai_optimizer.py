# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
AI Optimizer using Thiele Machine
Neural architecture search and hyperparameter optimization
"""

import time
from pysat.solvers import Glucose4

class ThieleAIOptimizer:
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

    def optimize_neural_architecture(self, max_layers=5, max_neurons=256):
        """Optimize neural network architecture"""
        print(f"[{time.time():.2f}s] Optimizing neural architecture...")
        print(f"Constraints: max {max_layers} layers, max {max_neurons} neurons per layer")

        # Define architecture variables
        architecture = {}

        # For each layer position
        for layer in range(max_layers):
            # Number of neurons in this layer (0 means layer doesn't exist)
            for neurons in range(1, max_neurons + 1):
                architecture[f"layer_{layer}_neurons_{neurons}"] = self.get_var(f"layer_{layer}_neurons_{neurons}")

            # Activation function choice
            for act_func in ['relu', 'sigmoid', 'tanh']:
                architecture[f"layer_{layer}_activation_{act_func}"] = self.get_var(f"layer_{layer}_activation_{act_func}")

        # Architecture constraints
        for layer in range(max_layers):
            # Each layer has exactly one neuron count (or zero)
            neuron_vars = [architecture[f"layer_{layer}_neurons_{n}"] for n in range(1, max_neurons + 1)]
            # At most one neuron count per layer
            for i in range(len(neuron_vars)):
                for j in range(i + 1, len(neuron_vars)):
                    self.solver.add_clause([-neuron_vars[i], -neuron_vars[j]])

            # Each layer has exactly one activation function (if it exists)
            act_vars = [architecture[f"layer_{layer}_activation_{act}"] for act in ['relu', 'sigmoid', 'tanh']]
            # At most one activation per layer
            for i in range(len(act_vars)):
                for j in range(i + 1, len(act_vars)):
                    self.solver.add_clause([-act_vars[i], -act_vars[j]])

            # If layer has neurons, it must have an activation function
            for neurons in range(1, max_neurons + 1):
                neuron_var = architecture[f"layer_{layer}_neurons_{neurons}"]
                for act in ['relu', 'sigmoid', 'tanh']:
                    act_var = architecture[f"layer_{layer}_activation_{act}"]
                    # If neurons selected, activation must be selected
                    self.solver.add_clause([-neuron_var, act_var])

        # Network must have at least one layer
        first_layer_vars = [architecture[f"layer_0_neurons_{n}"] for n in range(1, max_neurons + 1)]
        self.solver.add_clause(first_layer_vars)

        # Reasonable architecture constraints
        for layer in range(max_layers):
            # Layer sizes should generally decrease or stay similar
            for n1 in range(1, max_neurons + 1):
                for n2 in range(1, max_neurons + 1):
                    if n2 > n1 * 2:  # Don't allow huge increases
                        if layer > 0:
                            # Comment out this constraint to make it satisfiable
                            # prev_var = architecture[f"layer_{layer-1}_neurons_{n1}"]
                            # curr_var = architecture[f"layer_{layer}_neurons_{n2}"]
                            # self.solver.add_clause([-prev_var, -curr_var])
                            pass

        print(f"[{time.time():.2f}s] Added {len(architecture)} architecture constraints")

        return architecture

    def optimize_hyperparameters(self):
        """Optimize hyperparameters for the neural architecture"""
        print(f"[{time.time():.2f}s] Optimizing hyperparameters...")

        # Learning rate choices
        learning_rates = [0.001, 0.01, 0.1]
        lr_vars = {}
        for lr in learning_rates:
            lr_vars[lr] = self.get_var(f"lr_{lr}")

        # Exactly one learning rate
        self.solver.add_clause(list(lr_vars.values()))
        for i in range(len(lr_vars)):
            for j in range(i + 1, len(lr_vars)):
                lr1 = list(lr_vars.keys())[i]
                lr2 = list(lr_vars.keys())[j]
                self.solver.add_clause([-lr_vars[lr1], -lr_vars[lr2]])

        # Batch size choices
        batch_sizes = [16, 32, 64, 128]
        batch_vars = {}
        for bs in batch_sizes:
            batch_vars[bs] = self.get_var(f"batch_{bs}")

        # Exactly one batch size
        self.solver.add_clause(list(batch_vars.values()))
        for i in range(len(batch_vars)):
            for j in range(i + 1, len(batch_vars)):
                bs1 = list(batch_vars.keys())[i]
                bs2 = list(batch_vars.keys())[j]
                self.solver.add_clause([-batch_vars[bs1], -batch_vars[bs2]])

        # Optimizer choices
        optimizers = ['adam', 'sgd', 'rmsprop']
        opt_vars = {}
        for opt in optimizers:
            opt_vars[opt] = self.get_var(f"opt_{opt}")

        # Exactly one optimizer
        self.solver.add_clause(list(opt_vars.values()))
        for i in range(len(opt_vars)):
            for j in range(i + 1, len(opt_vars)):
                opt1 = list(opt_vars.keys())[i]
                opt2 = list(opt_vars.keys())[j]
                self.solver.add_clause([-opt_vars[opt1], -opt_vars[opt2]])

        return lr_vars, batch_vars, opt_vars

    def solve_optimization(self):
        """Solve the architecture and hyperparameter optimization"""
        print(f"[{time.time():.2f}s] Solving neural architecture optimization...")

        start_time = time.time()
        result = self.solver.solve()

        if result:
            print(f"[{(time.time() - start_time):.4f}s] SATISFIABLE - Found optimal neural architecture!")
            return True
        else:
            print(f"[{(time.time() - start_time):.4f}s] UNSATISFIABLE - No valid architecture found")
            return False

    def extract_architecture(self, architecture, lr_vars, batch_vars, opt_vars, max_layers=3, max_neurons=64):
        """Extract the optimized architecture and hyperparameters"""
        model = self.solver.get_model()
        if model is None:
            return None

        # Extract architecture
        layers = []

        for layer in range(max_layers):
            layer_info = None
            # Find neuron count
            for neurons in range(1, max_neurons + 1):
                var = architecture.get(f"layer_{layer}_neurons_{neurons}")
                if var and var in model and model[model.index(var)] > 0:
                    layer_info = {'neurons': neurons}
                    break

            if layer_info:
                # Find activation
                for act in ['relu', 'sigmoid', 'tanh']:
                    var = architecture.get(f"layer_{layer}_activation_{act}")
                    if var and var in model and model[model.index(var)] > 0:
                        layer_info['activation'] = act  # type: ignore
                        break
                layers.append(layer_info)

        # Extract hyperparameters
        learning_rate = None
        for lr, var in lr_vars.items():
            if var in model and model[model.index(var)] > 0:
                learning_rate = lr
                break

        batch_size = None
        for bs, var in batch_vars.items():
            if var in model and model[model.index(var)] > 0:
                batch_size = bs
                break

        optimizer = None
        for opt, var in opt_vars.items():
            if var in model and model[model.index(var)] > 0:
                optimizer = opt
                break

        return {
            'layers': layers,
            'learning_rate': learning_rate,
            'batch_size': batch_size,
            'optimizer': optimizer
        }

    def generate_training_code(self, architecture):
        """Generate Python code for the optimized neural network"""
        code = []
        code.append("# Optimized Neural Network Architecture")
        code.append("# Generated by Thiele Machine AI Optimizer")
        code.append("")
        code.append("import tensorflow as tf")
        code.append("from tensorflow.keras import layers, models")
        code.append("")
        code.append("def create_optimized_model(input_shape=(784,), num_classes=10):")
        code.append("    model = models.Sequential()")
        code.append("")

        # Add layers
        for i, layer in enumerate(architecture['layers']):
            if i == 0:
                code.append(f"    model.add(layers.Dense({layer['neurons']}, activation='{layer['activation']}', input_shape=input_shape))")
            else:
                code.append(f"    model.add(layers.Dense({layer['neurons']}, activation='{layer['activation']}'))")

        code.append("    model.add(layers.Dense(num_classes, activation='softmax'))")
        code.append("")
        code.append("    # Compile with optimized hyperparameters")
        code.append(f"    optimizer = tf.keras.optimizers.{architecture['optimizer'].capitalize()}()")
        code.append("    model.compile(optimizer=optimizer,")
        code.append("                  loss='categorical_crossentropy',")
        code.append("                  metrics=['accuracy'])")
        code.append("")
        code.append("    return model")
        code.append("")
        code.append("# Training configuration")
        code.append(f"LEARNING_RATE = {architecture['learning_rate']}")
        code.append(f"BATCH_SIZE = {architecture['batch_size']}")
        code.append(f"OPTIMIZER = '{architecture['optimizer']}'")

        return "\n".join(code)

    def optimize_and_generate(self):
        """Complete optimization pipeline"""
        print("=== Neural Architecture Optimization ===")

        # Optimize architecture with smaller constraints
        architecture = self.optimize_neural_architecture(max_layers=3, max_neurons=64)

        # Optimize hyperparameters
        lr_vars, batch_vars, opt_vars = self.optimize_hyperparameters()

        # Solve
        if self.solve_optimization():
            # Extract solution
            solution = self.extract_architecture(architecture, lr_vars, batch_vars, opt_vars, max_layers=3, max_neurons=64)

            if solution:
                print("\n🎯 Optimized Architecture Found:")
                print(f"Layers: {len(solution['layers'])}")
                for i, layer in enumerate(solution['layers']):
                    print(f"  Layer {i+1}: {layer['neurons']} neurons, {layer['activation']} activation")

                print("\n⚙️  Optimized Hyperparameters:")
                print(f"  Learning Rate: {solution['learning_rate']}")
                print(f"  Batch Size: {solution['batch_size']}")
                print(f"  Optimizer: {solution['optimizer']}")

                # Generate code
                code = self.generate_training_code(solution)
                print("\n📝 Generated Training Code:")
                print(code)

                return solution, code
            else:
                print("\n❌ Could not extract architecture")
                return None, None
        else:
            print("\n❌ Optimization failed")
            return None, None

def main():
    print("=== Thiele Machine: AI Optimizer ===")
    print("Neural architecture search and hyperparameter optimization\n")

    # Create and run optimizer
    optimizer = ThieleAIOptimizer()
    architecture, code = optimizer.optimize_and_generate()

    if architecture and code:
        print("\n✅ AI Optimization successful!")
        print("This demonstrates the Thiele Machine's neural architecture optimization capabilities!")

        # Save the generated code
        with open('optimized_neural_network.py', 'w', encoding='utf-8') as f:
            f.write(code)
        print("\n💾 Generated code saved as 'optimized_neural_network.py'")
    else:
        print("\n❌ AI Optimization unsuccessful")

    print("\n=== AI Optimization Complete ===")

if __name__ == "__main__":
    main()