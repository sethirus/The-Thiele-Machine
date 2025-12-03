# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
The Forge: Grammar-Guided Discovery Engine

This module implements grammar-guided genetic programming for discovering
physical equations from data without being explicitly programmed with
complex operators like Laplacian or Hamiltonian.
"""

from forge.grammar_crawler import GrammarCrawler, Equation, EquationNode

__all__ = ['GrammarCrawler', 'Equation', 'EquationNode']
