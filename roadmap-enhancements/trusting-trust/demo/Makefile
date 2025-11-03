.PHONY: all clean proofpack verify

CC_GCC = gcc
CC_CLANG = clang
CFLAGS = -O2 -Wall -Wextra

RECEIPTS_DIR = receipts
PROOFPACK = trusting-trust.proofpack.zst

all: toycc_gcc toycc_clang

toycc_gcc: toycc.c
	@echo "Building with GCC..."
	$(CC_GCC) $(CFLAGS) -o $@ $<

toycc_clang: toycc.c
	@echo "Building with Clang..."
	$(CC_CLANG) $(CFLAGS) -o $@ $<

receipts: toycc_gcc toycc_clang
	@echo "Generating receipts..."
	@mkdir -p $(RECEIPTS_DIR)
	python3 ../../tools/ingest_binary.py toycc.c --out $(RECEIPTS_DIR)/toycc_source.json
	python3 ../../tools/ingest_binary.py toycc_gcc --out $(RECEIPTS_DIR)/toycc_gcc.json
	python3 ../../tools/ingest_binary.py toycc_clang --out $(RECEIPTS_DIR)/toycc_clang.json

verify_equivalence.sh:
	@echo '#!/bin/bash' > $@
	@echo 'set -e' >> $@
	@echo 'echo "Verifying compiler equivalence..."' >> $@
	@echo 'GCC_SHA=$$(jq -r .global_digest receipts/toycc_gcc.json)' >> $@
	@echo 'CLANG_SHA=$$(jq -r .global_digest receipts/toycc_clang.json)' >> $@
	@echo 'echo "  GCC binary SHA256:   $$GCC_SHA"' >> $@
	@echo 'echo "  Clang binary SHA256: $$CLANG_SHA"' >> $@
	@echo 'if [ "$$GCC_SHA" = "$$CLANG_SHA" ]; then' >> $@
	@echo '    echo "✓ SUCCESS: Compilers produced identical binaries!"' >> $@
	@echo '    exit 0' >> $@
	@echo 'else' >> $@
	@echo '    echo "✗ FAILURE: Binaries differ (possible backdoor!)"' >> $@
	@echo '    exit 1' >> $@
	@echo 'fi' >> $@
	@chmod +x $@

proofpack: receipts verify_equivalence.sh
	@echo "Creating proofpack..."
	@mkdir -p proofpack_tmp
	@cp -r $(RECEIPTS_DIR) proofpack_tmp/
	@cp verify_equivalence.sh proofpack_tmp/
	@cp README.md proofpack_tmp/
	@cp toycc.c proofpack_tmp/
	@tar -czf - proofpack_tmp | zstd -19 -o $(PROOFPACK)
	@rm -rf proofpack_tmp
	@echo "✓ Proofpack created: $(PROOFPACK)"

verify: verify_equivalence.sh
	@./verify_equivalence.sh

clean:
	rm -f toycc_gcc toycc_clang
	rm -f test_gcc.c test_clang.c test_gcc test_clang
	rm -rf $(RECEIPTS_DIR)
	rm -f verify_equivalence.sh
	rm -f $(PROOFPACK)
	rm -rf proofpack_tmp
