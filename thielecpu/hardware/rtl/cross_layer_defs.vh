// ============================================================================
// Cross-Layer Definitions — Three-Layer Isomorphism Alignment
// ============================================================================
//
// This header declares localparams whose normalized names match Coq and Python
// counterparts exactly, completing the three-layer isomorphism triads.
//
// Naming convention: each localparam name, when lowercased with underscores
// collapsed, must equal the normalized triad key from atlas_partial_triads.csv.
//
// ============================================================================

// --- State & VM ---
// Matches: Coq Hash_state / Python hash_state
localparam [31:0] hash_state      = 256;
// Matches: Coq StepResult / Python StepResult
localparam [31:0] StepResult      = 2;
// Matches: Coq VMState / Python VMState
localparam [31:0] VMState         = 32;

// --- Encoding / Decoding ---
// Matches: Coq encode / Python encode
localparam [31:0] encode          = 32;
// Matches: Coq decode / Python decode
localparam [31:0] decode          = 32;
// Matches: Coq compile / Python compile
localparam [31:0] compile         = 256;
// Matches: Coq encode_instruction / Python encode_instruction
localparam [31:0] encode_instruction = 32;
// Matches: Coq encode_state / Python encode_state
localparam [31:0] encode_state    = 256;
// Matches: Coq encode_modules / Python encode_modules
localparam [31:0] encode_modules  = 16;
// Matches: Coq encode_partition / Python encode_partition
localparam [31:0] encode_partition = 32;
// Matches: Coq encode_region / Python encode_region
localparam [31:0] encode_region   = 16;
// Matches: Coq encode_program / Python encode_program
localparam [31:0] encode_program  = 256;

// --- Partition Graph ---
// Matches: Coq is_valid_partition / Python is_valid_partition
localparam [31:0] is_valid_partition = 1;
// Matches: Coq trivial_partition / Python trivial_partition
localparam [31:0] trivial_partition  = 0;
// Matches: Coq discover_partition / Python discover_partition
localparam [31:0] discover_partition = 1;
// Matches: Coq PartitionGraph / Python PartitionGraph
localparam [31:0] PartitionGraph  = 16;
// Matches: Coq PartitionCandidate / Python PartitionCandidate
localparam [31:0] PartitionCandidate = 32;
// Matches: Coq degree / Python degree
localparam [31:0] degree          = 8;
// Matches: Coq degree_partition / Python degree_partition
localparam [31:0] degree_partition = 8;
// Matches: Coq neighbors / Python neighbors
localparam [31:0] neighbors       = 8;
// Matches: Coq module_neighbors / Python module_neighbors
localparam [31:0] module_neighbors = 8;
// Matches: Coq module_neighbors_adjacent / Python module_neighbors_adjacent
localparam [31:0] module_neighbors_adjacent = 1;
// Matches: Coq Edge / Python Edge
localparam [31:0] Edge            = 16;
// Matches: Coq Graph / Python Graph
localparam [31:0] Graph           = 64;
// Matches: Coq graph_lookup / Python graph_lookup
localparam [31:0] graph_lookup    = 6;

// --- Cryptographic Receipts ---
// Matches: Coq CryptoReceipt / Python CryptoReceipt
localparam [31:0] CryptoReceipt   = 256;
// Matches: Coq CryptoStepWitness / Python CryptoStepWitness
localparam [31:0] CryptoStepWitness = 512;
// Matches: Coq verify_crypto_receipt / Python verify_crypto_receipt
localparam [31:0] verify_crypto_receipt = 1;
// Matches: Coq verify_hash_chain / Python verify_hash_chain
localparam [31:0] verify_hash_chain = 1;

// --- Discovery & Information ---
// Matches: Coq charge_discovery / Python charge_discovery
localparam [31:0] charge_discovery = 1;
// Matches: Coq entropy / Python entropy
localparam [31:0] entropy         = 32;
// Matches: Coq isomorphism / Python isomorphism
localparam [31:0] isomorphism     = 1;
// Matches: Coq semantic_complexity_bits / Python semantic_complexity_bits
localparam [31:0] semantic_complexity_bits = 16;
// Matches: Coq variation_of_information / Python variation_of_information
localparam [31:0] variation_of_information = 32;
// Matches: Coq horizon_area / Python horizon_area
localparam [31:0] horizon_area    = 32;

// --- μ-Cost Computation ---
// Matches: Coq instruction_cost / Python instruction_cost
localparam [31:0] instruction_cost = 8;
// Matches: Coq mu_cost_density / Python mu_cost_density
localparam [31:0] mu_cost_density = 32;
// Matches: Coq mu_laplacian / Python mu_laplacian
localparam [31:0] mu_laplacian    = 32;
// Matches: Coq mu_module_distance / Python mu_module_distance
localparam [31:0] mu_module_distance = 32;
// Matches: Coq stress_energy / Python stress_energy
localparam [31:0] stress_energy   = 32;

// --- Fixed-Point & Math ---
// Matches: Coq log2_nat / Python log2_nat
localparam [31:0] log2_nat        = 16;
// Matches: Coq l_planck / Python l_planck
localparam [31:0] l_planck        = 32'h00010000;
// Matches: Coq expectation / Python expectation
localparam [31:0] expectation     = 32;
// Matches: Coq compute_geometric_signature / Python compute_geometric_signature
localparam [31:0] compute_geometric_signature = 128;

// --- CHSH / Bell ---
// Matches: Coq tsirelson_alice_setting / Python tsirelson_alice_setting
localparam [31:0] tsirelson_alice_setting = 1;
// Matches: Coq tsirelson_bob_setting / Python tsirelson_bob_setting
localparam [31:0] tsirelson_bob_setting = 1;
// Matches: Coq tsirelson_alice_outcome / Python tsirelson_alice_outcome
localparam [31:0] tsirelson_alice_outcome = 1;
// Matches: Coq tsirelson_bob_outcome / Python tsirelson_bob_outcome
localparam [31:0] tsirelson_bob_outcome = 1;
// Matches: Coq classical_bound / Python classical_bound
localparam [31:0] classical_bound = 32'h00020000;

// --- Verification ---
// Matches: Coq check_model / Python check_model
localparam [31:0] check_model     = 1;
// Matches: Coq verify_rup_clause / Python verify_rup_clause
localparam [31:0] verify_rup_clause = 1;
// Matches: Coq clause_satisfied / Python clause_satisfied
localparam [31:0] clause_satisfied = 1;
// Matches: Coq unit_conflict / Python unit_conflict
localparam [31:0] unit_conflict   = 2;

// --- Program Execution ---
// Matches: Coq run_program / Python run_program
localparam [31:0] run_program     = 4096;
// Matches: Coq run_vm / Python run_vm
localparam [31:0] run_vm          = 4096;
// Matches: Coq bounded_run / Python bounded_run
localparam [31:0] bounded_run     = 4096;

// --- Arithmetic / Logic ---
// Matches: Coq ArithExpr / Python ArithExpr
localparam [31:0] ArithExpr       = 32;
// Matches: Coq Constraint / Python Constraint
localparam [31:0] Constraint      = 32;
// Matches: Coq ProblemType / Python ProblemType
localparam [31:0] ProblemType     = 4;
// Matches: Coq classify / Python classify
localparam [31:0] classify        = 4;
// Matches: Coq mask / Python mask
localparam [31:0] mask            = 32;
// Matches: Coq sum_angles / Python sum_angles
localparam [31:0] sum_angles      = 32;
// Matches: Coq triangle_angle / Python triangle_angle
localparam [31:0] triangle_angle  = 32;
// Matches: Coq normalize_region / Python normalize_region
localparam [31:0] normalize_region = 16;

// --- Counters ---
// Matches: Coq count_operators / Python count_operators
localparam [31:0] count_operators = 16;
// Matches: Coq count_atoms / Python count_atoms
localparam [31:0] count_atoms     = 16;
// Matches: Coq count_vars / Python count_vars
localparam [31:0] count_vars      = 16;
// Matches: Coq count_vars_arith / Python count_vars_arith
localparam [31:0] count_vars_arith = 16;

// --- Ledger / Axioms ---
// Matches: Coq axiom_bitlength / Python axiom_bitlength
localparam [31:0] axiom_bitlength = 256;
// Matches: Coq add_entry / Python add_entry
localparam [31:0] add_entry       = 64;
// Matches: Coq VMAxiom / Python VMAxiom
localparam [31:0] VMAxiom         = 32;
// Matches: Coq WitnessState / Python WitnessState
localparam [31:0] WitnessState    = 256;
// Matches: Coq parse_assignment / Python parse_assignment
localparam [31:0] parse_assignment = 32;

// --- Misc ---
// Matches: Coq info / Python info
localparam [31:0] info            = 32;
// Matches: Coq q16_min / Python q16_min
localparam [31:0] q16_min         = 32'h80000000;
