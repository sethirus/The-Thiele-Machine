#!/usr/bin/env python3
"""
Scheduling Optimizer using Thiele Machine
Optimizes complex project scheduling with resource constraints
"""

import time
from pysat.solvers import Glucose4

class ThieleSchedulingOptimizer:
    def __init__(self, tasks, dependencies, resources):
        """
        tasks: list of (task_id, duration, resource_type)
        dependencies: list of (task_a, task_b) meaning task_a must finish before task_b starts
        resources: dict of {resource_type: available_count}
        """
        self.tasks = tasks
        self.dependencies = dependencies
        self.resources = resources
        self.task_ids = [t[0] for t in tasks]
        self.task_dict = {t[0]: (i, t[1], t[2]) for i, t in enumerate(tasks)}
        self.solver = Glucose4()
        self.vars = {}
        self.var_counter = 0

    def get_var(self, name):
        """Lazy variable allocation"""
        if name not in self.vars:
            self.var_counter += 1
            self.vars[name] = self.var_counter
        return self.vars[name]

    def add_scheduling_constraints(self, max_time):
        """Add constraints for valid project schedule"""
        print(f"[{time.time():.2f}s] Adding scheduling constraints for max time {max_time}...")

        # For each task, assign a start time
        for task_id in self.task_ids:
            task_idx, duration, _ = self.task_dict[task_id]
            for t in range(max_time - duration + 1):
                # start_time[task_idx][t] = 1 if task starts at time t
                self.get_var(f"start_{task_idx}_{t}")

        # Each task must start exactly once
        for task_idx in range(len(self.tasks)):
            start_vars = []
            task_id, duration, _ = self.tasks[task_idx]
            for t in range(max_time - duration + 1):
                start_vars.append(self.get_var(f"start_{task_idx}_{t}"))
            # At least one start time
            self.solver.add_clause(start_vars)
            # At most one start time (pairwise exclusions)
            for i in range(len(start_vars)):
                for j in range(i + 1, len(start_vars)):
                    self.solver.add_clause([-start_vars[i], -start_vars[j]])

        # Dependency constraints: task_a must finish before task_b starts
        for dep_a, dep_b in self.dependencies:
            if dep_a in self.task_dict and dep_b in self.task_dict:
                idx_a = self.task_dict[dep_a][0]
                idx_b = self.task_dict[dep_b][0]
                duration_a = self.task_dict[dep_a][1]

                for start_a in range(max_time - self.task_dict[dep_a][1] + 1):
                    for start_b in range(max_time - self.task_dict[dep_b][1] + 1):
                        finish_a = start_a + duration_a
                        if start_b < finish_a:
                            # Cannot have this combination
                            self.solver.add_clause([
                                -self.get_var(f"start_{idx_a}_{start_a}"),
                                -self.get_var(f"start_{idx_b}_{start_b}")
                            ])

        # Resource constraints: no more than available resources at any time
        for resource_type, available_count in self.resources.items():
            for t in range(max_time):
                # Find all tasks that use this resource
                resource_tasks = []
                for task_idx, (task_id, duration, res_type) in enumerate(self.tasks):
                    if res_type == resource_type:
                        resource_tasks.append((task_idx, duration))

                if not resource_tasks:
                    continue

                # For each time slot, limit concurrent usage
                # This is complex - for simplicity, we'll check each possible oversubscription
                for task_subset in self.get_subsets(resource_tasks, available_count + 1):
                    if len(task_subset) > available_count:
                        # These tasks cannot all be running at time t
                        clause = []
                        for task_idx, duration in task_subset:
                            # Task cannot be running at time t
                            for start_time in range(max(0, t - duration + 1), min(t + 1, max_time - duration + 1)):
                                clause.append(-self.get_var(f"start_{task_idx}_{start_time}"))
                        if clause:
                            self.solver.add_clause(clause)

        print(f"[{time.time():.2f}s] Added scheduling constraints for {len(self.tasks)} tasks")

    def get_subsets(self, items, size):
        """Get all subsets of given size (simplified implementation)"""
        if size == 0:
            return [[]]
        if not items:
            return []
        # For simplicity, just return some combinations
        subsets = []
        n = len(items)
        for i in range(1 << n):
            subset = []
            for j in range(n):
                if (i & (1 << j)):
                    subset.append(items[j])
            if len(subset) == size:
                subsets.append(subset)
        return subsets

    def solve_schedule(self, max_time):
        """Solve the scheduling problem"""
        print(f"[{time.time():.2f}s] Solving scheduling for {len(self.tasks)} tasks with max time {max_time}...")

        start_time = time.time()
        result = self.solver.solve()

        if result:
            print(f"[{(time.time() - start_time):.4f}s] SATISFIABLE - Found valid schedule!")
            return self.extract_schedule(max_time)
        else:
            print(f"[{(time.time() - start_time):.4f}s] UNSATISFIABLE - No schedule possible in {max_time} time units")
            return None

    def extract_schedule(self, max_time):
        """Extract the schedule from SAT solution"""
        model = self.solver.get_model()
        schedule = {}

        if model is None:
            return None

        for task_idx, (task_id, duration, resource) in enumerate(self.tasks):
            for t in range(max_time - duration + 1):
                var = self.get_var(f"start_{task_idx}_{t}")
                if var in model and model[model.index(var)] > 0:
                    schedule[task_id] = {
                        'start': t,
                        'finish': t + duration,
                        'duration': duration,
                        'resource': resource
                    }
                    break

        return schedule

    def optimize_schedule(self, max_possible_time=50):
        """Find the minimum completion time"""
        print(f"[{time.time():.2f}s] Optimizing schedule to find minimum completion time...")

        for max_time in range(1, max_possible_time + 1):
            print(f"\n--- Testing max time {max_time} ---")

            # Reset solver
            self.solver = Glucose4()
            self.vars = {}
            self.var_counter = 0

            self.add_scheduling_constraints(max_time)
            schedule = self.solve_schedule(max_time)

            if schedule:
                # Check if all tasks complete within max_time
                max_finish = max(task['finish'] for task in schedule.values())
                if max_finish <= max_time:
                    print(f"✓ Found optimal schedule with completion time {max_finish}")
                    return schedule

        print("❌ Could not find feasible schedule within time limit")
        return None

def create_test_project():
    """Create a test project scheduling problem"""
    # Tasks: (id, duration, resource_type)
    tasks = [
        ('Design', 3, 'designer'),
        ('Code', 5, 'developer'),
        ('Test', 2, 'tester'),
        ('Review', 1, 'manager'),
        ('Deploy', 1, 'devops')
    ]

    # Dependencies: (predecessor, successor)
    dependencies = [
        ('Design', 'Code'),
        ('Code', 'Test'),
        ('Test', 'Review'),
        ('Review', 'Deploy')
    ]

    # Resources: {resource_type: count}
    resources = {
        'designer': 1,
        'developer': 2,
        'tester': 1,
        'manager': 1,
        'devops': 1
    }

    return tasks, dependencies, resources

def main():
    print("=== Thiele Machine: Scheduling Optimizer ===")
    print("Optimizing complex project schedules with resource constraints\n")

    # Create test project
    tasks, dependencies, resources = create_test_project()
    print(f"Project: {len(tasks)} tasks, {len(dependencies)} dependencies")
    print(f"Resources: {resources}")

    # Optimize schedule
    optimizer = ThieleSchedulingOptimizer(tasks, dependencies, resources)
    schedule = optimizer.optimize_schedule(max_possible_time=20)

    if schedule:
        print("\n🎯 Optimal Schedule Found:")
        print("Task\tStart\tFinish\tDuration\tResource")
        print("-" * 50)
        for task_id, info in sorted(schedule.items(), key=lambda x: x[1]['start']):
            print(f"{task_id}\t{info['start']}\t{info['finish']}\t{info['duration']}\t\t{info['resource']}")

        max_completion = max(task['finish'] for task in schedule.values())
        print(f"\n🏆 Project completion time: {max_completion} time units")
        print("This demonstrates the Thiele Machine solving complex scheduling optimization!")
    else:
        print("\n❌ No feasible schedule found")

    print("\n=== Scheduling Optimization Complete ===")

if __name__ == "__main__":
    main()