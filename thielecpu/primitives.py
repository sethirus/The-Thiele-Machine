#!/usr/bin/env python3
"""
Primitive Building Blocks for Evolutionary Strategy Synthesis

This module defines the fundamental mathematical primitives that compose
graph partitioning strategies. These primitives are the "DNA" of sight.
"""

from typing import Any, Callable, Dict, List
from dataclasses import dataclass
import networkx as nx
import numpy as np


@dataclass
class Primitive:
    """Base class for all computational primitives."""
    name: str
    arity: int  # Number of inputs
    func: Callable
    
    def __call__(self, *args):
        return self.func(*args)


# ============================================================================
# GRAPH PRIMITIVES
# ============================================================================

def prim_get_nodes(G: nx.Graph) -> List[int]:
    """Extract list of all nodes from graph."""
    return sorted(G.nodes())


def prim_get_edges(G: nx.Graph) -> List[tuple]:
    """Extract list of all edges from graph."""
    return list(G.edges())


def prim_node_degree(G: nx.Graph, node: int, weight: str = 'weight') -> float:
    """Get weighted degree of a node."""
    return float(G.degree(node, weight=weight))


def prim_adjacency_matrix(G: nx.Graph, nodelist: List[int]) -> np.ndarray:
    """Convert graph to adjacency matrix."""
    return nx.to_numpy_array(G, nodelist=nodelist, weight='weight')


def prim_laplacian_matrix(G: nx.Graph, nodelist: List[int]) -> np.ndarray:
    """Compute graph Laplacian matrix."""
    return nx.laplacian_matrix(G, nodelist=nodelist, weight='weight').toarray()


# ============================================================================
# MATRIX DECOMPOSITION PRIMITIVES
# ============================================================================

def prim_eigendecomposition(matrix: np.ndarray) -> tuple:
    """Compute eigenvalues and eigenvectors."""
    try:
        eigenvalues, eigenvectors = np.linalg.eigh(matrix)
        return eigenvalues, eigenvectors
    except np.linalg.LinAlgError:
        # Fallback for singular matrices
        n = matrix.shape[0]
        return np.zeros(n), np.eye(n)


def prim_svd(matrix: np.ndarray) -> tuple:
    """Compute singular value decomposition."""
    try:
        U, s, Vt = np.linalg.svd(matrix)
        return U, s, Vt
    except np.linalg.LinAlgError:
        n = matrix.shape[0]
        return np.eye(n), np.zeros(min(matrix.shape)), np.eye(matrix.shape[1])


def prim_get_eigenvector(eigenvectors: np.ndarray, index: int) -> np.ndarray:
    """Extract specific eigenvector by index."""
    if index < eigenvectors.shape[1]:
        return eigenvectors[:, index]
    return np.zeros(eigenvectors.shape[0])


# ============================================================================
# CLUSTERING PRIMITIVES
# ============================================================================

def prim_kmeans_1d(values: np.ndarray, k: int, seed: int = 42) -> np.ndarray:
    """1D k-means clustering on values."""
    from sklearn.cluster import KMeans
    if len(values) < k:
        return np.arange(len(values))
    
    kmeans = KMeans(n_clusters=k, random_state=seed, n_init=10)
    labels = kmeans.fit_predict(values.reshape(-1, 1))
    return labels


def prim_threshold_partition(values: np.ndarray, threshold: float) -> np.ndarray:
    """Binary partition based on threshold."""
    return (values > threshold).astype(int)


def prim_quantile_partition(values: np.ndarray, n_partitions: int) -> np.ndarray:
    """Partition based on quantiles."""
    if len(values) == 0:
        return np.array([])
    
    quantiles = np.linspace(0, 1, n_partitions + 1)[1:-1]
    thresholds = np.quantile(values, quantiles)
    
    labels = np.zeros(len(values), dtype=int)
    for i, t in enumerate(thresholds):
        labels[values > t] = i + 1
    
    return labels


# ============================================================================
# COMMUNITY DETECTION PRIMITIVES
# ============================================================================

def prim_modularity_score(G: nx.Graph, partition: Dict[int, int]) -> float:
    """Calculate modularity score of a partition."""
    try:
        from networkx.algorithms import community as nx_comm
        # Convert partition dict to list of sets
        communities = {}
        for node, comm_id in partition.items():
            if comm_id not in communities:
                communities[comm_id] = set()
            communities[comm_id].add(node)
        
        community_list = list(communities.values())
        return nx_comm.modularity(G, community_list, weight='weight')
    except (ImportError, AttributeError, ValueError):
        return 0.0


def prim_greedy_modularity(G: nx.Graph) -> Dict[int, int]:
    """Greedy modularity community detection."""
    try:
        from networkx.algorithms import community
        communities = community.greedy_modularity_communities(G, weight='weight')
        
        partition = {}
        for partition_id, comm in enumerate(communities):
            for node in comm:
                partition[node] = partition_id
        
        return partition
    except (ImportError, AttributeError):
        return {node: 0 for node in G.nodes()}


# ============================================================================
# SORTING AND RANKING PRIMITIVES
# ============================================================================

def prim_sort_by_value(nodes: List[int], values: Dict[int, float], reverse: bool = False) -> List[int]:
    """Sort nodes by their associated values."""
    return sorted(nodes, key=lambda n: values.get(n, 0), reverse=reverse)


def prim_rank_values(values: np.ndarray) -> np.ndarray:
    """Convert values to ranks (0 to n-1)."""
    return np.argsort(np.argsort(values))


def prim_normalize(values: np.ndarray) -> np.ndarray:
    """Normalize values to [0, 1] range."""
    if len(values) == 0:
        return values
    
    min_val, max_val = values.min(), values.max()
    if max_val == min_val:
        return np.zeros_like(values)
    
    return (values - min_val) / (max_val - min_val)


# ============================================================================
# ASSIGNMENT PRIMITIVES
# ============================================================================

def prim_round_robin_assign(nodes: List[int], k: int) -> Dict[int, int]:
    """Assign nodes to k partitions round-robin."""
    partition = {}
    for i, node in enumerate(nodes):
        partition[node] = i % k
    
    return partition


def prim_balanced_assign(nodes: List[int], k: int) -> Dict[int, int]:
    """Assign nodes to k partitions in balanced way."""
    partition = {}
    for i, node in enumerate(sorted(nodes)):
        partition[node] = i % k
    
    return partition


def prim_greedy_assign(nodes: List[int], values: Dict[int, float], k: int) -> Dict[int, int]:
    """Greedily assign high-value nodes to different partitions."""
    sorted_nodes = prim_sort_by_value(nodes, values, reverse=True)
    partition = {}
    
    for i, node in enumerate(sorted_nodes):
        partition[node] = i % k
    
    return partition


# ============================================================================
# RIEMANN HYPOTHESIS SEARCH PRIMITIVES
# ============================================================================

try:
    from thielecpu.riemann_primitives import (
        prim_zeta,
        prim_zeta_magnitude,
        prim_grid_search,
        prim_refine_zero,
        prim_is_on_critical_line,
        prim_verify_counterexample,
        prim_adaptive_search,
        prim_structured_search
    )
    RIEMANN_AVAILABLE = True
except ImportError:
    RIEMANN_AVAILABLE = False


# ============================================================================
# PRIMITIVE REGISTRY
# ============================================================================

PRIMITIVES = {
    # Graph operations
    'GET_NODES': Primitive('GET_NODES', 1, prim_get_nodes),
    'GET_EDGES': Primitive('GET_EDGES', 1, prim_get_edges),
    'NODE_DEGREE': Primitive('NODE_DEGREE', 2, prim_node_degree),
    'ADJACENCY_MATRIX': Primitive('ADJACENCY_MATRIX', 2, prim_adjacency_matrix),
    'LAPLACIAN_MATRIX': Primitive('LAPLACIAN_MATRIX', 2, prim_laplacian_matrix),
    
    # Matrix operations
    'EIGENDECOMP': Primitive('EIGENDECOMP', 1, prim_eigendecomposition),
    'SVD': Primitive('SVD', 1, prim_svd),
    'GET_EIGENVECTOR': Primitive('GET_EIGENVECTOR', 2, prim_get_eigenvector),
    
    # Clustering
    'KMEANS_1D': Primitive('KMEANS_1D', 3, prim_kmeans_1d),
    'THRESHOLD_PARTITION': Primitive('THRESHOLD_PARTITION', 2, prim_threshold_partition),
    'QUANTILE_PARTITION': Primitive('QUANTILE_PARTITION', 2, prim_quantile_partition),
    
    # Community detection
    'MODULARITY_SCORE': Primitive('MODULARITY_SCORE', 2, prim_modularity_score),
    'GREEDY_MODULARITY': Primitive('GREEDY_MODULARITY', 1, prim_greedy_modularity),
    
    # Sorting and ranking
    'SORT_BY_VALUE': Primitive('SORT_BY_VALUE', 3, prim_sort_by_value),
    'RANK_VALUES': Primitive('RANK_VALUES', 1, prim_rank_values),
    'NORMALIZE': Primitive('NORMALIZE', 1, prim_normalize),
    
    # Assignment
    'ROUND_ROBIN_ASSIGN': Primitive('ROUND_ROBIN_ASSIGN', 2, prim_round_robin_assign),
    'BALANCED_ASSIGN': Primitive('BALANCED_ASSIGN', 2, prim_balanced_assign),
    'GREEDY_ASSIGN': Primitive('GREEDY_ASSIGN', 3, prim_greedy_assign),
}

# Add Riemann primitives if available
if RIEMANN_AVAILABLE:
    PRIMITIVES.update({
        'ZETA': Primitive('ZETA', 1, prim_zeta),
        'ZETA_MAG': Primitive('ZETA_MAG', 1, prim_zeta_magnitude),
        'GRID_SEARCH': Primitive('GRID_SEARCH', 5, prim_grid_search),
        'REFINE_ZERO': Primitive('REFINE_ZERO', 1, prim_refine_zero),
        'IS_ON_CRITICAL_LINE': Primitive('IS_ON_CRITICAL_LINE', 1, prim_is_on_critical_line),
        'VERIFY_COUNTEREXAMPLE': Primitive('VERIFY_COUNTEREXAMPLE', 1, prim_verify_counterexample),
        'ADAPTIVE_SEARCH': Primitive('ADAPTIVE_SEARCH', 3, prim_adaptive_search),
        'STRUCTURED_SEARCH': Primitive('STRUCTURED_SEARCH', 3, prim_structured_search),
    })



def get_primitive(name: str) -> Primitive:
    """Get primitive by name."""
    if name not in PRIMITIVES:
        raise ValueError(f"Unknown primitive: {name}")
    return PRIMITIVES[name]


def list_primitives() -> List[str]:
    """List all available primitive names."""
    return sorted(PRIMITIVES.keys())
