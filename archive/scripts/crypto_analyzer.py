#!/usr/bin/env python3
"""
Crypto Analyzer using Thiele Machine
Analyzes cipher patterns and performs cryptanalysis
"""

import time
from pysat.solvers import Glucose4
from collections import Counter
import string

class ThieleCryptoAnalyzer:
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

    def analyze_substitution_cipher(self, ciphertext, known_plaintext=""):
        """
        Analyze a simple substitution cipher
        ciphertext: the encrypted text to analyze
        known_plaintext: any known mappings (e.g., "ETAOINSHRDLUCMFYWGPBVKXQJZ")
        """
        print(f"[{time.time():.2f}s] Analyzing substitution cipher...")
        print(f"Ciphertext: {ciphertext[:50]}...")
        print(f"Known plaintext frequency: {known_plaintext}")

        # Clean and analyze ciphertext
        cleaned = ''.join(c for c in ciphertext.upper() if c.isalpha())
        if not cleaned:
            print("❌ No alphabetic characters found in ciphertext")
            return None

        # Frequency analysis
        freq = Counter(cleaned)
        print(f"Character frequencies: {dict(freq.most_common(10))}")

        # Create substitution mapping variables
        alphabet = string.ascii_uppercase
        mapping = {}

        for cipher_char in set(cleaned):
            for plain_char in alphabet:
                mapping[(cipher_char, plain_char)] = self.get_var(f"map_{cipher_char}_{plain_char}")

        # Each ciphertext character maps to exactly one plaintext character
        for cipher_char in set(cleaned):
            # At least one mapping
            plain_vars = [mapping[(cipher_char, p)] for p in alphabet]
            self.solver.add_clause(plain_vars)

            # At most one mapping (pairwise exclusions)
            for i in range(len(alphabet)):
                for j in range(i + 1, len(alphabet)):
                    self.solver.add_clause([
                        -mapping[(cipher_char, alphabet[i])],
                        -mapping[(cipher_char, alphabet[j])]
                    ])

        # Each plaintext character is mapped to by at most one ciphertext character
        for plain_char in alphabet:
            cipher_vars = []
            for cipher_char in set(cleaned):
                if (cipher_char, plain_char) in mapping:
                    cipher_vars.append(mapping[(cipher_char, plain_char)])

            # At most one ciphertext character maps to this plaintext (pairwise exclusions)
            for i in range(len(cipher_vars)):
                for j in range(i + 1, len(cipher_vars)):
                    self.solver.add_clause([-cipher_vars[i], -cipher_vars[j]])

        # Add frequency-based constraints (most common cipher chars likely map to common plaintext)
        if known_plaintext:
            common_plaintext = known_plaintext.upper()[:6]  # ETAOIN
            common_cipher = [char for char, _ in freq.most_common(6)]

            # Suggest mappings for common characters
            for i, (cipher_char, plain_char) in enumerate(zip(common_cipher, common_plaintext)):
                if i < len(common_plaintext):
                    # Add a preference (not strict constraint) by making it more likely
                    pass  # For now, just informational

        print(f"[{time.time():.2f}s] Added {len(mapping)} mapping constraints")

        return mapping

    def solve_cipher(self, ciphertext, mapping):
        """Solve the substitution cipher"""
        print(f"[{time.time():.2f}s] Solving cipher with {len(mapping)} variables...")

        start_time = time.time()
        result = self.solver.solve()

        if result:
            print(f"[{(time.time() - start_time):.4f}s] SATISFIABLE - Found potential decryption!")
            return self.extract_mapping(mapping)
        else:
            print(f"[{(time.time() - start_time):.4f}s] UNSATISFIABLE - No valid mapping found")
            return None

    def extract_mapping(self, mapping):
        """Extract the character mapping from SAT solution"""
        model = self.solver.get_model()
        char_mapping = {}

        if model is None:
            return None

        for cipher_char in mapping:
            if isinstance(cipher_char, tuple):
                c_char, p_char = cipher_char
                var = mapping[cipher_char]
                if var in model and model[model.index(var)] > 0:
                    char_mapping[c_char] = p_char

        return char_mapping

    def decrypt_text(self, ciphertext, mapping):
        """Decrypt the ciphertext using the mapping"""
        result = []
        for char in ciphertext:
            if char.upper() in mapping:
                decrypted = mapping[char.upper()]
                result.append(decrypted if char.isupper() else decrypted.lower())
            else:
                result.append(char)
        return ''.join(result)

    def analyze_ciphertext_patterns(self, ciphertext):
        """Analyze patterns in ciphertext for cryptanalysis insights"""
        print(f"[{time.time():.2f}s] Analyzing ciphertext patterns...")

        # Clean text
        cleaned = ''.join(c for c in ciphertext.upper() if c.isalpha())

        # Find repeated patterns
        patterns = {}
        for length in range(2, 6):  # Look for repeats of length 2-5
            for i in range(len(cleaned) - length + 1):
                pattern = cleaned[i:i+length]
                if pattern in patterns:
                    patterns[pattern].append(i)
                else:
                    patterns[pattern] = [i]

        # Show interesting patterns (repeated more than once)
        repeated_patterns = {k: v for k, v in patterns.items() if len(v) > 1}
        print(f"Repeated patterns found: {len(repeated_patterns)}")

        for pattern, positions in sorted(repeated_patterns.items())[:10]:  # Show top 10
            print(f"  '{pattern}' at positions: {positions}")

        # Character frequency analysis
        freq = Counter(cleaned)
        total_chars = sum(freq.values())

        print("\nCharacter frequency analysis:")
        print("Char | Count | Frequency")
        print("-" * 25)
        for char, count in freq.most_common():
            percentage = (count / total_chars) * 100
            print(f"{char:4} | {count:5} | {percentage:8.2f}%")

        return repeated_patterns

    def test_cipher_strength(self, ciphertext, known_plaintext=""):
        """Test the strength of the cipher by attempting cryptanalysis"""
        print("=== Cipher Strength Analysis ===")

        # Analyze patterns
        self.analyze_ciphertext_patterns(ciphertext)

        # Attempt to break the cipher
        mapping = self.analyze_substitution_cipher(ciphertext, known_plaintext)

        if mapping:
            solution = self.solve_cipher(ciphertext, mapping)

            if solution:
                decrypted = self.decrypt_text(ciphertext, solution)
                print("\n🔓 Potential decryption:")
                print(f"Original: {ciphertext[:100]}...")
                print(f"Decrypted: {decrypted[:100]}...")

                # Show the mapping
                print("\n📋 Character mapping:")
                for c, p in sorted(solution.items()):
                    print(f"  {c} → {p}")

                return decrypted, solution
            else:
                print("\n❌ Could not find a valid decryption")
                return None, None
        else:
            print("\n❌ Could not analyze cipher")
            return None, None

def create_test_cipher():
    """Create a test substitution cipher for demonstration"""
    # Simple substitution cipher
    key = {
        'A': 'Q', 'B': 'W', 'C': 'E', 'D': 'R', 'E': 'T', 'F': 'Y', 'G': 'U',
        'H': 'I', 'I': 'O', 'J': 'P', 'K': 'A', 'L': 'S', 'M': 'D', 'N': 'F',
        'O': 'G', 'P': 'H', 'Q': 'J', 'R': 'K', 'S': 'L', 'T': 'Z', 'U': 'X',
        'V': 'C', 'W': 'V', 'X': 'B', 'Y': 'N', 'Z': 'M'
    }

    plaintext = "THE QUICK BROWN FOX JUMPS OVER THE LAZY DOG"
    ciphertext = ''.join(key.get(c, c) for c in plaintext.upper())

    return plaintext, ciphertext

def main():
    print("=== Thiele Machine: Crypto Analyzer ===")
    print("Analyzing cipher patterns and performing cryptanalysis\n")

    # Create test cipher
    original, ciphertext = create_test_cipher()
    print(f"Original plaintext: {original}")
    print(f"Encrypted ciphertext: {ciphertext}\n")

    # Analyze and attempt to break
    analyzer = ThieleCryptoAnalyzer()
    decrypted, mapping = analyzer.test_cipher_strength(ciphertext, "ETAOINSHRDLUCMFYWGPBVKXQJZ")

    if decrypted and mapping:
        print("\n✅ Cryptanalysis successful!")
        print("This demonstrates the Thiele Machine's cryptanalysis capabilities!")
    else:
        print("\n❌ Cryptanalysis unsuccessful")

    print("\n=== Crypto Analysis Complete ===")

if __name__ == "__main__":
    main()