# Lean Theorem Map

Audit date: 2026-05-14.

Command:

```bash
lake build
```

Current source search:

```bash
rg -n "\bsorry\b|admit|trivial" Lean/PMM_FP Lean/PMM_FP.lean
```

The current Lean source contains no active unfinished proof bodies using
Lean's standard proof-gap keywords. One historical mention appears in a
comment in `BoundedDensity.lean`.

## Mapping

| Paper statement | Lean file | Role |
|---|---|---|
| Basis sets `P_a`, `P_b` | `Setup.lean` | definitions |
| Fractional basis functions | `Setup.lean` | definitions |
| PMM-FP estimators | `Estimator.lean` | estimator interface |
| BD0 condition | `BoundedDensity.lean` | condition for negative powers |
| Consistency structure | `Consistency.lean` | conditional theorem bundle |
| Asymptotic-normality structure | `AsymptoticNormality.lean` | conditional theorem bundle |
| Variance reduction | `VarianceReduction.lean` | algebraic core of `g_2` |
| Higher-order progression | `HigherOrder.lean` | conditional theorem bundle |
| BIC model selection | `ModelSelection.lean` | conditional theorem bundle |

## Interpretation

The Lean layer is a formal consistency layer for definitions,
algebraic identities and conditional theorem structure. The submitted
paper should not claim that the external M-estimator CLT, Edgeworth
expansion machinery, or all statistical regularity theory are fully
machine-proved in Lean.
