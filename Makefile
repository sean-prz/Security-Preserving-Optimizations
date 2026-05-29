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
	$(ROCQC) $(ROCQFLAGS) src/Proofs/Analysis/LivenessProofs.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/unskip/Soundness.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/unskip/Noninference.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/unskip/SecretPreservation.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/unskip/Core.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/unsafe_DSE/Soundness.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/unsafe_DSE/NotSecure.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/EvalEquivalence.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/Noninference.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/NoninferenceSec.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/SecEnvSubtyping.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/safe_DSE/SecretPreservation.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/safe_DSE/Soundness.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/safe_DSE/Noninference.v
	$(ROCQC) $(ROCQFLAGS) src/Proofs/safe_DSE/Core.v
	@echo "Running Tests ..."
	@for file in src/Examples/*.v; do \
		echo "Compiling $$file"; \
		$(ROCQC) $(ROCQFLAGS) "$$file"; \
	done


clean:
	find src \( -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" -o -name "*.aux" -o -name ".*.aux" -o -name ".*.cache" \) -delete
