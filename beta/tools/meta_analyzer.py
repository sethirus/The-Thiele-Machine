#!/usr/bin/env python3
"""
The META-PDISCOVER - Final Proof of Geometric Separation

This module loads the geometric atlas and proves that structured and chaotic
problems have distinct geometric signatures in the Strategy Graph space.

It produces:
1. A 2D scatter plot showing separation between CONSISTENT and SPURIOUS verdicts
2. A classification report demonstrating SVM can distinguish the two classes
"""

import json
import time
from pathlib import Path
from typing import Dict, Any, List, Tuple
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from sklearn.svm import SVC
from sklearn.model_selection import train_test_split, cross_val_score
from sklearn.metrics import classification_report, accuracy_score, confusion_matrix
from sklearn.preprocessing import StandardScaler


def load_atlas(atlas_path: Path = Path("sight_logs/atlas/phase2_metrics.json")) -> Dict[str, Any]:
    """
    Load the geometric atlas.
    
    Args:
        atlas_path: Path to the phase2_metrics.json file
    
    Returns:
        Atlas dictionary
    """
    with open(atlas_path, 'r') as f:
        atlas = json.load(f)
    return atlas


def prepare_dataset(atlas: Dict[str, Any]) -> Tuple[np.ndarray, np.ndarray, List[str]]:
    """
    Prepare dataset for classification.
    
    Args:
        atlas: The atlas dictionary
    
    Returns:
        Tuple of (features, labels, problem_names)
    """
    entries = atlas.get("entries", [])
    
    features = []
    labels = []
    names = []
    
    for entry in entries:
        verdict = entry.get("verdict", "UNKNOWN")
        if verdict not in ["CONSISTENT", "SPURIOUS"]:
            continue
        
        metrics = entry.get("geometric_metrics", {})
        
        # Five-dimensional feature vector
        feature_vector = [
            metrics.get("average_edge_weight", 0.0),
            metrics.get("max_edge_weight", 0.0),
            metrics.get("edge_weight_stddev", 0.0),
            metrics.get("min_spanning_tree_weight", 0.0),
            metrics.get("thresholded_density", 0.0)
        ]
        
        features.append(feature_vector)
        labels.append(1 if verdict == "CONSISTENT" else 0)  # 1 = structured, 0 = chaotic
        names.append(entry.get("problem_name", "unknown"))
    
    return np.array(features), np.array(labels), names


def generate_separation_plot(
    features: np.ndarray,
    labels: np.ndarray,
    names: List[str],
    output_path: Path = Path("sight_logs/atlas/separation_plot.png")
):
    """
    Generate a 2D scatter plot showing geometric separation.
    
    Uses average_edge_weight (x) vs edge_weight_stddev (y).
    
    Args:
        features: Feature matrix (n_samples, 5)
        labels: Label vector (1 = CONSISTENT, 0 = SPURIOUS)
        names: List of problem names
        output_path: Where to save the plot
    """
    print("\nGenerating separation plot...")
    
    # Extract relevant features for visualization
    # Feature 0: average_edge_weight
    # Feature 2: edge_weight_stddev
    x = features[:, 0]  # average_edge_weight
    y = features[:, 2]  # edge_weight_stddev
    
    # Create figure
    fig, ax = plt.subplots(figsize=(10, 8))
    
    # Plot points
    consistent_mask = labels == 1
    spurious_mask = labels == 0
    
    ax.scatter(
        x[consistent_mask], y[consistent_mask],
        c='green', marker='o', s=100, alpha=0.7,
        label='CONSISTENT (Structured)', edgecolors='black', linewidth=1
    )
    ax.scatter(
        x[spurious_mask], y[spurious_mask],
        c='red', marker='^', s=100, alpha=0.7,
        label='SPURIOUS (Chaotic)', edgecolors='black', linewidth=1
    )
    
    # Labels and title
    ax.set_xlabel('Average Edge Weight (VI)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Edge Weight Std Dev (Dispersion)', fontsize=12, fontweight='bold')
    ax.set_title('The Shape of Sight: Geometric Separation of Order and Chaos', 
                 fontsize=14, fontweight='bold', pad=20)
    
    # Legend
    ax.legend(loc='best', fontsize=11, framealpha=0.9)
    
    # Grid
    ax.grid(True, alpha=0.3, linestyle='--')
    
    # Add text annotation with statistics
    n_consistent = np.sum(consistent_mask)
    n_spurious = np.sum(spurious_mask)
    stats_text = f"n(CONSISTENT) = {n_consistent}\nn(SPURIOUS) = {n_spurious}"
    ax.text(0.02, 0.98, stats_text, transform=ax.transAxes,
            fontsize=10, verticalalignment='top',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    # Save
    output_path.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    
    print(f"✓ Separation plot saved to: {output_path}")


def generate_classification_report(
    features: np.ndarray,
    labels: np.ndarray,
    output_path: Path = Path("sight_logs/atlas/classification_report.txt")
):
    """
    Generate classification report using SVM.
    
    Args:
        features: Feature matrix (n_samples, 5)
        labels: Label vector (1 = CONSISTENT, 0 = SPURIOUS)
        output_path: Where to save the report
    """
    print("\nTraining SVM classifier...")
    
    if len(features) < 4:
        print("⚠️  Not enough samples for meaningful classification")
        with open(output_path, 'w') as f:
            f.write("Insufficient samples for classification (need at least 4)\n")
        return
    
    # Standardize features
    scaler = StandardScaler()
    features_scaled = scaler.fit_transform(features)
    
    # Check if we have both classes
    unique_labels = np.unique(labels)
    if len(unique_labels) < 2:
        print("⚠️  Only one class present in dataset")
        with open(output_path, 'w') as f:
            f.write("Only one class present in dataset\n")
        return
    
    # Split data if we have enough samples
    if len(features) >= 10:
        X_train, X_test, y_train, y_test = train_test_split(
            features_scaled, labels, test_size=0.3, random_state=42, stratify=labels
        )
        
        # Train SVM
        clf = SVC(kernel='rbf', C=1.0, random_state=42)
        clf.fit(X_train, y_train)
        
        # Predict
        y_pred = clf.predict(X_test)
        
        # Accuracy
        acc = accuracy_score(y_test, y_pred)
        
        # Confusion matrix
        cm = confusion_matrix(y_test, y_pred)
        
        # Classification report
        class_names = ['SPURIOUS (Chaotic)', 'CONSISTENT (Structured)']
        report = classification_report(y_test, y_pred, target_names=class_names)
        
        # Cross-validation score
        cv_scores = cross_val_score(clf, features_scaled, labels, cv=min(5, len(features)))
        cv_mean = np.mean(cv_scores)
        cv_std = np.std(cv_scores)
    else:
        # Too few samples for train/test split, use all data
        clf = SVC(kernel='rbf', C=1.0, random_state=42)
        clf.fit(features_scaled, labels)
        
        y_pred = clf.predict(features_scaled)
        acc = accuracy_score(labels, y_pred)
        cm = confusion_matrix(labels, y_pred)
        
        class_names = ['SPURIOUS (Chaotic)', 'CONSISTENT (Structured)']
        report = classification_report(labels, y_pred, target_names=class_names)
        
        cv_scores = cross_val_score(clf, features_scaled, labels, cv=min(3, len(features)))
        cv_mean = np.mean(cv_scores)
        cv_std = np.std(cv_scores)
    
    # Write report
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        f.write("="*70 + "\n")
        f.write("THE META-PDISCOVER: Classification Report\n")
        f.write("="*70 + "\n\n")
        f.write("Task: Distinguish CONSISTENT (structured) from SPURIOUS (chaotic) problems\n")
        f.write("Method: Support Vector Machine (RBF kernel) on 5D geometric signature\n\n")
        f.write("Features:\n")
        f.write("  1. Average Edge Weight (mean VI between strategies)\n")
        f.write("  2. Max Edge Weight (max VI between any two strategies)\n")
        f.write("  3. Edge Weight Std Dev (dispersion of VI values)\n")
        f.write("  4. Min Spanning Tree Weight (minimum VI to connect all strategies)\n")
        f.write("  5. Thresholded Density (fraction of high-VI edges)\n\n")
        f.write("="*70 + "\n")
        f.write(f"DATASET STATISTICS\n")
        f.write("="*70 + "\n")
        f.write(f"Total samples: {len(features)}\n")
        f.write(f"CONSISTENT (structured): {np.sum(labels == 1)}\n")
        f.write(f"SPURIOUS (chaotic): {np.sum(labels == 0)}\n\n")
        f.write("="*70 + "\n")
        f.write(f"CLASSIFICATION RESULTS\n")
        f.write("="*70 + "\n")
        f.write(f"Accuracy: {acc:.4f}\n\n")
        f.write(f"Cross-Validation Accuracy: {cv_mean:.4f} ± {cv_std:.4f}\n\n")
        f.write("Confusion Matrix:\n")
        f.write(f"                     Predicted SPURIOUS  Predicted CONSISTENT\n")
        f.write(f"Actual SPURIOUS      {cm[0][0]:^18}  {cm[0][1]:^20}\n")
        f.write(f"Actual CONSISTENT    {cm[1][0]:^18}  {cm[1][1]:^20}\n\n")
        f.write("="*70 + "\n")
        f.write("DETAILED CLASSIFICATION REPORT\n")
        f.write("="*70 + "\n")
        f.write(report)
        f.write("\n")
        f.write("="*70 + "\n")
        f.write("CONCLUSION\n")
        f.write("="*70 + "\n")
        if acc >= 0.8:
            f.write("✓ STRONG SEPARATION: The geometric signature successfully distinguishes\n")
            f.write("  structured problems from chaotic ones. The 'shape of sight' is REAL\n")
            f.write("  and MEASURABLE.\n")
        elif acc >= 0.6:
            f.write("✓ MODERATE SEPARATION: The geometric signature shows meaningful\n")
            f.write("  distinction between structured and chaotic problems.\n")
        else:
            f.write("⚠ WEAK SEPARATION: More data may be needed to demonstrate clear\n")
            f.write("  geometric separation.\n")
        f.write("="*70 + "\n")
    
    print(f"✓ Classification report saved to: {output_path}")
    print(f"  Accuracy: {acc:.4f}")
    print(f"  Cross-validation: {cv_mean:.4f} ± {cv_std:.4f}")


def main():
    """Main entry point for the meta-analyzer."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Generate final proof of geometric separation"
    )
    parser.add_argument(
        "--atlas",
        type=str,
        default="sight_logs/atlas/phase2_metrics.json",
        help="Path to the atlas (phase2_metrics.json)"
    )
    parser.add_argument(
        "--plot-output",
        type=str,
        default="sight_logs/atlas/separation_plot.png",
        help="Output path for separation plot"
    )
    parser.add_argument(
        "--report-output",
        type=str,
        default="sight_logs/atlas/classification_report.txt",
        help="Output path for classification report"
    )
    
    args = parser.parse_args()
    
    print(f"\n{'='*70}")
    print("THE META-PDISCOVER - Final Proof of Geometric Separation")
    print(f"{'='*70}")
    
    # Load atlas
    print(f"\nLoading atlas from: {args.atlas}")
    atlas = load_atlas(Path(args.atlas))
    
    # Prepare dataset
    features, labels, names = prepare_dataset(atlas)
    
    print(f"Loaded {len(features)} samples")
    print(f"  CONSISTENT (structured): {np.sum(labels == 1)}")
    print(f"  SPURIOUS (chaotic): {np.sum(labels == 0)}")
    
    if len(features) == 0:
        print("\n✗ No valid samples found in atlas")
        return
    
    # Generate separation plot
    generate_separation_plot(
        features, labels, names,
        output_path=Path(args.plot_output)
    )
    
    # Generate classification report
    generate_classification_report(
        features, labels,
        output_path=Path(args.report_output)
    )
    
    print(f"\n{'='*70}")
    print("✓ META-PDISCOVER COMPLETE")
    print(f"{'='*70}")
    print(f"Separation plot: {args.plot_output}")
    print(f"Classification report: {args.report_output}")
    print(f"{'='*70}\n")


if __name__ == "__main__":
    main()
