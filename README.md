# itp-project


```text
src/
├── Map.v
├── Language/
│   ├── Syntax.v
│   ├── Semantics.v
│   ├── Security.v
│   └── Main.v
├── optimizations/
├── proofs/
└── examples/
```
```
Map → VarSets → Syntax → Security (+ interp_sec -  needs Syntax + Security types)
                              └─→ EvalContext.v (contexts, trace_event, notations)
                                       └─→ Semantics (eval, eval_sec)
                                                └─→ Properties (ct_cmd, security props)
                                                         └─→ Main.v (re-exports all above)
                         └─→ Analysis.v (program, liveness  - needs Syntax + VarSets)
                                  └─ ├─→ Optimizations/Unsafe/DSE.v
                                           └─→ Optimizations/Safe/DSE.v
                                  └─→ Examples/, Proofs/ (import Language.Main + Language.Analysis)
```

notes CCP:
scope: petit language, petit set de propriétés. coeur du projet (estimer moitié du temps proj) + stretch goals (rendre language + complexe, propriétés + complexes)
ex. imp. -> .

checker que constant time reste, par rapport aux inputs.
autres props


jasmin https://arxiv.org/pdf/2511.11292


