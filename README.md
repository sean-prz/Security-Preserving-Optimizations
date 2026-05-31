# Security-Preserving Optimizations

This repository presents a Rocq formalization designed to verify compiler
optimizations that preserve both functional behavior and security properties.
The project extends a Software Foundations-style IMP language with traces,
secret/public state predicates, liveness analysis, and optimization passes for
dead-store elimination and `Skip` cleanup.

The two main security goals are:

- preserving deliberate sensitive-memory clears, so an optimizer cannot remove
  security-relevant assignments only because they are functionally dead;
- preserving non-interference-style constant-time behavior, so observable traces
  remain independent of secret inputs.

## Build

The main entrypoint is:

```sh
make rocq
```

## Codebase Structure

```text
src/
├── Map.v
├── VarSets.v
├── Language/
│   ├── Syntax.v
│   ├── Security.v
│   ├── EvalContext.v
│   ├── Analysis.v
│   ├── Semantics.v
│   ├── Properties.v
│   ├── Main.v
│   └── Optimizations/
│       ├── Secure/
│       │   ├── DSE.v
│       │   └── Unskip.v
│       └── Insecure/
│           └── DSE.v
├── Proofs/
│   ├── Analysis/
│   ├── secure_DSE/
│   ├── insecure_DSE/
│   └── unskip/
└── Examples/
```

### Core Language

- `src/Map.v` defines the finite-map interface and implementation.
- `src/VarSets.v` defines finite sets of variables used by analysis and proofs. ([MSetWeakLists](https://rocq-prover.org/doc/v8.9/stdlib/Coq.MSets.MSetWeakList.html)
- `src/Language/Syntax.v` defines variables, expressions, commands, notation,
  and function environments.
- `src/Language/Security.v` defines security environments and secret/public
  agreement predicates.
- `src/Language/EvalContext.v` defines evaluation contexts and trace events.
- `src/Language/Semantics.v` defines the big-step semantics.
- `src/Language/Properties.v` defines semantic and security properties.
- `src/Language/Main.v` re-exports the main language modules.

### Optimizations

- `src/Language/Optimizations/Insecure/DSE.v` implements a baseline dead-store
  elimination pass that is useful for showing what can go wrong.
- `src/Language/Optimizations/Secure/DSE.v` implements the security-aware DSE
  pass.
- `src/Language/Optimizations/Secure/Unskip.v` removes redundant `Skip`
  commands while preserving the relevant properties.

### Proofs And Examples

- `src/Proofs/` contains the proof development for semantic equivalence,
  non-interference, security environment reasoning, liveness analysis, secure DSE,
  insecure DSE, and `unskip`.
- `src/Examples/` contains executable examples and checks for traces, program
  security, DSE behavior, and security units.

## Report

The project report is available at
[`Report/6 - Security-Preserving Optimizations.pdf`](Report/6%20-%20Security-Preserving%20Optimizations.pdf).
