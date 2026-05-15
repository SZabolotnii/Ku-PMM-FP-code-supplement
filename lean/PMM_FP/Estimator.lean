import PMM_FP.Setup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open scoped BigOperators

namespace PMM_FP

/-!
# Estimator — означення оцінювача PMM-FP (signed-parity B2 convention)

Дано вибірку `{(x_v, y_v)}_{v=1..n}` і **підмножину степенів** `P ⊆ ℝ`
(`P_a`, `P_b` або `P_b_weak`). У моделі $y_v = R(\theta, x_v) + \xi_v$ маємо
дві паралельні конвенції базису:

1. **Регресорний базис** на `x > 0`: `η_i = β_0 + Σ_k γ_k β_k · fpBasis p_k x_i`
   (Royston-Altman). Використовується для побудови дизайн-матриці.
2. **Score базис** на залишку `ξ ∈ ℝ`: signed-parity `g_p^±(ξ)`
   (Kunchenko). Використовується у стохастичному поліномі
   `ψ_h^FP(ξ) = Σ h_i (g_i(ξ) − E[g_i(ξ)])`.

Оцінювач PMM-FP порядку `s ∈ {2, 3}` мінімізує функціонал
Кунченка з центрованими корелянтами `fpCorrelant` зі `Setup.lean` (на score-базисі).

Файл містить **означення** оцінювача; властивості — у `Consistency.lean`,
`AsymptoticNormality.lean`, `VarianceReduction.lean`.
-/

/-- Структура даних: вибірка `(x_v, y_v)`. -/
structure Sample (n : ℕ) where
  x : Fin n → ℝ
  y : Fin n → ℝ

/-- Структура моделі: вибрані індекси базисних функцій. -/
structure ModelChoice (P : List ℝ) where
  selected : Finset (Fin P.length)
  size_bound : selected.card ≤ 4  -- обмеження D2 з decisions.md
  deriving DecidableEq

/-- Результат PMM-FP — оцінки коефіцієнтів `β_0, ..., β_K` і обраної моделі.
    `P` — це підмножина степенів (`P_a`, `P_b`, або `P_b_weak`); реальний
    signed-parity score базис будується автоматично з `P` через `gpSigned`
    (див. `basisA`/`basisB`/`basisB_weak` у `Setup.lean`).

    Тут залишено `noncomputable` із заглушкою: повна реалізація потребує
    розв'язку нелінійної системи Ньютона-Рафсона `F · h* = b` і виходить
    за межі формалізації цього файлу. -/
noncomputable def pmmFP
    (P : List ℝ)
    (_s : ℕ)
    {n : ℕ}
    (_data : Sample n)
    (_model : ModelChoice P) : (Fin P.length → ℝ) :=
  fun _ => 0  -- TODO: повна реалізація через розв'язок системи F·h* = b

/-- Окремий випадок: PMM-FP порядку 2 на треку (a) (basisA, 9 елементів). -/
noncomputable def pmmFP_pos {n : ℕ} (data : Sample n) (model : ModelChoice P_a) :
    (Fin P_a.length → ℝ) :=
  pmmFP P_a 2 data model

/-- Окремий випадок: PMM-FP порядку 2 на треку (b) повному (basisB, 15 елементів). -/
noncomputable def pmmFP_full {n : ℕ} (data : Sample n) (model : ModelChoice P_b) :
    (Fin P_b.length → ℝ) :=
  pmmFP P_b 2 data model

/-- Окремий випадок: PMM-FP порядку 2 на треку (b) зм'якшеному (basisB_weak,
    11 елементів — D12). Менш жорстка BD0_weak умова. -/
noncomputable def pmmFP_full_weak {n : ℕ} (data : Sample n) (model : ModelChoice P_b_weak) :
    (Fin P_b_weak.length → ℝ) :=
  pmmFP P_b_weak 2 data model

/-- OLS-FP як baseline: розв'язок нормальних рівнянь на FP-базисі. -/
noncomputable def olsFP
    (P : List ℝ)
    {n : ℕ}
    (_data : Sample n)
    (_model : ModelChoice P) : (Fin P.length → ℝ) :=
  fun _ => 0  -- TODO: стандартний OLS

end PMM_FP
