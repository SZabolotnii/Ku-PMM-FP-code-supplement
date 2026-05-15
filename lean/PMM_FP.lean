import PMM_FP.Setup
import PMM_FP.Estimator
import PMM_FP.BoundedDensity
import PMM_FP.MEstimatorTools
import PMM_FP.Consistency
import PMM_FP.AsymptoticNormality
import PMM_FP.VarianceReduction
import PMM_FP.HigherOrder
import PMM_FP.ModelSelection

/-!
# PMM_FP — точка входу

Формальна верифікація теорем для статті:

> *Polynomial Maximization Method with Fractional Polynomial Basis:
> A Frequentist Bridge to Bayesian Fractional Polynomials*

Структура двох паралельних треків:

* **Трек (a) PMM-FP_pos:** базис `P_a = {0, 0.5, 1, 2, 3}`, K = 10,
  без додаткових припущень понад `E[ξ^4] < ∞`.
* **Трек (b) PMM-FP_full:** базис `P_b = {-2, -1, -0.5, 0, 0.5, 1, 2, 3}`,
  K = 16 (дзеркало Hubin et al. 2026), з умовою BD0
  (bounded density near zero + `E[|ξ|^{-2}] < ∞`).

Кожна теорема має дві версії: `T_X_pos` (для треку a) і `T_X_full` (для треку b).
-/
