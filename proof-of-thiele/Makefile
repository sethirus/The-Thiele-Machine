PYTHON ?= python3
ROOT := $(abspath ..)
DATA := $(ROOT)/experiments/20251101_070033_ci_fix

.PHONY: all containment separation cost-model receipts isomorphism

all: containment separation cost-model receipts isomorphism

containment:
	$(ROOT)/coq/verify_subsumption.sh

separation:
	PYTHONPATH=$(ROOT) $(PYTHON) $(ROOT)/proof-of-thiele/02_separation/validate_tseitin_scaling.py $(DATA)

cost-model:
	PYTHONPATH=$(ROOT) $(PYTHON) $(ROOT)/proof-of-thiele/03_cost_model/verify_mu_ledger.py $(DATA)

receipts:
	PYTHONPATH=$(ROOT) $(PYTHON) $(ROOT)/proof-of-thiele/04_receipts/verify_receipts.py $(DATA)

isomorphism:
	PYTHONPATH=$(ROOT) $(PYTHON) $(ROOT)/proof-of-thiele/05_isomorphism/check_isomorphism_ledger.py
