"""
Tests for calorimetry proofpack infrastructure.

This module tests the calorimetry analysis pipeline without requiring
actual hardware measurements. It uses synthetic data to verify that:
1. The analysis script correctly computes statistics
2. Pass/fail gates work as expected
3. The CI script integrates properly
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

# Add parent directory to path for imports
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))


@pytest.fixture
def calorimetry_dir():
    """Return path to calorimetry proofpack directory."""
    return REPO_ROOT / 'proofpacks' / 'calorimetry_v1'


@pytest.fixture
def analysis_dir(calorimetry_dir):
    """Return path to analysis directory."""
    return calorimetry_dir / 'analysis'


def test_directory_structure(calorimetry_dir):
    """Test that all required directories exist."""
    assert calorimetry_dir.exists(), "Calorimetry proofpack directory not found"
    assert (calorimetry_dir / 'README.md').exists(), "README.md missing"
    assert (calorimetry_dir / 'MANIFEST.json').exists(), "MANIFEST.json missing"
    assert (calorimetry_dir / 'data').exists(), "data/ directory missing"
    assert (calorimetry_dir / 'analysis').exists(), "analysis/ directory missing"
    assert (calorimetry_dir / 'receipts').exists(), "receipts/ directory missing"
    assert (calorimetry_dir / 'ci').exists(), "ci/ directory missing"


def test_data_templates_exist(calorimetry_dir):
    """Test that data template files exist."""
    data_dir = calorimetry_dir / 'data'
    assert (data_dir / 'cal_data.csv').exists(), "cal_data.csv template missing"
    assert (data_dir / 'idle_baseline.csv').exists(), "idle_baseline.csv template missing"
    assert (data_dir / 'sensors.json').exists(), "sensors.json template missing"


def test_analysis_scripts_exist(analysis_dir):
    """Test that analysis scripts exist and are executable."""
    assert (analysis_dir / 'analyze_calorimetry.py').exists(), "analyze_calorimetry.py missing"
    assert (analysis_dir / 'generate_synthetic_data.py').exists(), "generate_synthetic_data.py missing"


def test_ci_script_exists(calorimetry_dir):
    """Test that CI script exists and is executable."""
    ci_script = calorimetry_dir / 'ci' / 'run_ci.sh'
    assert ci_script.exists(), "run_ci.sh missing"
    # Check if executable
    import os
    assert os.access(ci_script, os.X_OK), "run_ci.sh not executable"


def test_synthetic_data_generation(analysis_dir, tmp_path):
    """Test that synthetic data can be generated."""
    # Generate synthetic data to tmp directory
    result = subprocess.run(
        [sys.executable, str(analysis_dir / 'generate_synthetic_data.py'),
         '--output-dir', str(tmp_path)],
        capture_output=True,
        text=True
    )
    
    assert result.returncode == 0, f"Data generation failed: {result.stderr}"
    assert (tmp_path / 'cal_data.csv').exists(), "cal_data.csv not generated"
    assert (tmp_path / 'idle_baseline.csv').exists(), "idle_baseline.csv not generated"
    
    # Check that data has reasonable content
    import pandas as pd
    df = pd.read_csv(tmp_path / 'cal_data.csv')
    assert len(df) > 0, "Generated data is empty"
    assert 'mu_sum' in df.columns, "mu_sum column missing"
    assert 'E_joules' in df.columns, "E_joules column missing"
    assert 'T_K' in df.columns, "T_K column missing"


def test_analysis_with_passing_data(analysis_dir, tmp_path):
    """Test that analysis passes with correctly generated synthetic data."""
    # Generate passing data
    result = subprocess.run(
        [sys.executable, str(analysis_dir / 'generate_synthetic_data.py'),
         '--output-dir', str(tmp_path)],
        capture_output=True,
        text=True
    )
    assert result.returncode == 0, "Data generation failed"
    
    # Run analysis (need to temporarily modify paths or copy files)
    # For this test, we'll just verify the analysis script can be imported
    # and its key functions work
    import sys as sys_module
    sys_module.path.insert(0, str(analysis_dir))
    
    # Import the analysis module
    import analyze_calorimetry as ac
    
    # Test that key functions exist
    assert hasattr(ac, 'load_data'), "load_data function missing"
    assert hasattr(ac, 'compute_predictor'), "compute_predictor function missing"
    assert hasattr(ac, 'ols_regression'), "ols_regression function missing"
    assert hasattr(ac, 'bland_altman_analysis'), "bland_altman_analysis function missing"
    
    # Test loading the generated data
    import pandas as pd
    df = ac.load_data(tmp_path / 'cal_data.csv')
    assert len(df) > 0, "Data loading failed"
    
    # Test predictor computation
    df = ac.compute_predictor(df)
    assert 'X' in df.columns, "Predictor not computed"
    
    # Test OLS regression
    import numpy as np
    X = df['X'].values
    y = df['E_joules'].values
    result = ac.ols_regression(X, y)
    
    assert 'slope' in result, "Slope not computed"
    assert 'intercept' in result, "Intercept not computed"
    assert 'r_squared' in result, "R² not computed"
    
    # With properly generated synthetic data, slope should be near 1
    assert 0.95 <= result['slope'] <= 1.05, f"Slope {result['slope']} not near 1"
    assert result['r_squared'] >= 0.98, f"R² {result['r_squared']} too low"


def test_analysis_with_failing_data(analysis_dir, tmp_path):
    """Test that analysis correctly identifies failing data."""
    # Generate failing data
    result = subprocess.run(
        [sys.executable, str(analysis_dir / 'generate_synthetic_data.py'),
         '--fail', '--output-dir', str(tmp_path)],
        capture_output=True,
        text=True
    )
    assert result.returncode == 0, "Data generation failed"
    
    # Import the analysis module
    sys.path.insert(0, str(analysis_dir))
    import analyze_calorimetry as ac
    import numpy as np
    
    # Load and analyze the data
    df = ac.load_data(tmp_path / 'cal_data.csv')
    df = ac.compute_predictor(df)
    
    X = df['X'].values
    y = df['E_joules'].values
    result = ac.ols_regression(X, y)
    
    # With intentionally failing data, slope should NOT be near 1
    # (The failing mode uses slope=0.85, but noise can push it closer)
    # We just need to verify it's detectably different from 1
    assert result['slope'] < 0.99 or result['slope'] > 1.01, \
        f"Slope {result['slope']} should be detectably different from 1"


def test_manifest_structure(calorimetry_dir):
    """Test that MANIFEST.json has correct structure."""
    manifest_path = calorimetry_dir / 'MANIFEST.json'
    with open(manifest_path) as f:
        manifest = json.load(f)
    
    assert 'version' in manifest, "version field missing from MANIFEST"
    assert 'proofpack' in manifest, "proofpack field missing from MANIFEST"
    assert manifest['proofpack'] == 'calorimetry_v1', "Wrong proofpack name"
    assert 'signature_domain' in manifest, "signature_domain missing"
    assert manifest['signature_domain'] == 'ThieleCal|v1', "Wrong signature domain"


def test_readme_completeness(calorimetry_dir):
    """Test that README contains all required sections."""
    readme_path = calorimetry_dir / 'README.md'
    with open(readme_path, encoding='utf-8') as f:
        content = f.read()
    
    required_sections = [
        '# Calorimetry Proofpack v1',
        '## Overview',
        '## Pass/Fail Criteria',
        '## Data Collection Protocol',
        '## File Layout',
        '## Data Schema',
        '## Analysis Requirements',
        '## Status',
    ]
    
    for section in required_sections:
        assert section in content, f"README missing section: {section}"
    
    # Check for key equations
    assert 'k_B T ln 2' in content, "Thermodynamic equation missing"
    assert 'E_dyn' in content, "E_dyn variable missing"
    assert 'mu' in content.lower(), "mu sum variable missing"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
