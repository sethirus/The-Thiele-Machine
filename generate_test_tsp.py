#!/usr/bin/env python3
"""
Generate small TSP test instances for testing the Thiele Machine TSP solver.
"""

import random
from pathlib import Path

def generate_tsp_instance(num_cities, filename):
    """Generate a TSPLIB-format TSP instance with random coordinates."""

    # Generate random coordinates (latitude/longitude-like)
    cities = []
    for i in range(1, num_cities + 1):
        # Generate coordinates in a reasonable range
        lat = random.uniform(30, 50)  # Roughly US latitude range
        lon = random.uniform(-120, -70)  # Roughly US longitude range
        cities.append((i, lat, lon))

    # Write TSPLIB format
    with open(filename, 'w', encoding='utf-8') as f:
        f.write("NAME: test_tsp\n")
        f.write("TYPE: TSP\n")
        f.write("COMMENT: Generated test instance\n")
        f.write(f"DIMENSION: {num_cities}\n")
        f.write("EDGE_WEIGHT_TYPE: GEO\n")
        f.write("NODE_COORD_SECTION\n")

        for city_id, lat, lon in cities:
            f.write(f"{city_id} {lat:.6f} {lon:.6f}\n")

        f.write("EOF\n")

    print(f"Generated {filename} with {num_cities} cities")

def main():
    """Generate test instances of various sizes."""
    test_dir = Path("test_tsp_instances")
    test_dir.mkdir(exist_ok=True)

    # Generate test instances
    sizes = [5, 6, 7, 8]
    for size in sizes:
        filename = test_dir / f"test_{size}cities.tsp"
        generate_tsp_instance(size, filename)

    print(f"\nGenerated test instances in {test_dir}/")
    print("You can now test the TSP solver with these smaller instances.")

if __name__ == "__main__":
    main()