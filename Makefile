.PHONY: rocq clean

ROCQC=rocq compile
ROCQFLAGS=-R src ""

rocq:
	$(ROCQC) $(ROCQFLAGS) src/Map.v
	$(ROCQC) $(ROCQFLAGS) src/VarSets.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Syntax.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Security.v
	$(ROCQC) $(ROCQFLAGS) src/Language/EvalContext.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Analysis.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Semantics.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Properties.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Main.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Optimizations/Safe/Unskip.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Optimizations/Unsafe/DSE.v
	$(ROCQC) $(ROCQFLAGS) src/Language/Optimizations/Safe/DSE.v
	$(ROCQC) $(ROCQFLAGS) src/Examples/Programs.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/SecLookup.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/VarSetAgreement.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/UnskipProofs.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/UnsafeDSEProofs.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/EvalEquivalence.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/Noninference.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/SecEnvSubtyping.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/SafeDSEProofs.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/SafeDSESecurityProof.v
	@echo "Running Tests ..."
	@for file in src/Examples/*.v; do \
		echo "Compiling $$file"; \
		$(ROCQC) $(ROCQFLAGS) "$$file"; \
	done


clean:
	find src \( -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" -o -name "*.aux" -o -name ".*.aux" -o -name ".*.cache" \) -delete
