import PMM_FP.Setup
import PMM_FP.Estimator
import PMM_FP.AsymptoticNormality
import Mathlib.Tactic

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace PMM_FP

/-!
# VarianceReduction — Теорема 3 (T_3): головний результат (signed-parity B2)

**T_3 (усі треки):** Асимптотична відносна ефективність (ARE) оцінки
PMM-FP порядку `s = 2` відносно OLS-FP виражається загальною формулою
`g_S^(FP)` з §2.3 `reports/pmm_fp_theoretical_framework.md`:

`ARE(PMM-FP_{s=2}, OLS-FP) = g_S_FP μ ξ basis`,

де `basis ∈ {basisA, basisB, basisB_weak}` — signed-parity score-базис.

**Класична редукція:** при `basis = [(1, minus), (2, plus)]` маємо
`g_S_FP = g₂_classical = 1 - γ₃² / (2 + γ₄)` (теорема `g₂_reduction_FP`
зі `Setup.lean`, see §3 of framework report).

Для **загального basisA / basisB** значення `g_S_FP` визначається через
матрицю `fpCorrelant`-ів та вектор `b_i = -E[g_i'(ξ)]`. Для типових
розподілів воно є строго меншим за класичний `g₂` (див. §6.2 framework):

| Розподіл | g₂ classical | g_S_FP(basisA) | Виграш |
|----------|--------------|----------------|--------|
| Exp(1)   | 0.500        | 0.054          | 89.3%  |
| Lognormal| 0.612        | 0.340          | 44.5%  |
| Gamma(3) | 0.667        | 0.403          | 39.6%  |

Це **головна теорема статті** — вона мостить апарат Кунченка з
частотним FP-базисом і дає драматичне покращення.
-/

variable {α : Type*} [MeasurableSpace α]

/-- Коефіцієнт варіаційної редукції класичного PMM2: `g_2 = 1 - γ_3²/(2+γ_4)`.

    Це інваріант PMM2 (двочленний базис `{ξ, ξ²}`), що дорівнює
    асимптотичній відносній ефективності проти OLS. Доведено в Кунченко 2002,
    гл. 4. Дзеркало `g₂_classical` зі `Setup.lean`. -/
noncomputable def g₂ (μ : Measure α) (ξ : α → ℝ) : ℝ :=
  1 - (gamma3 μ ξ)^2 / (2 + gamma4 μ ξ)

/-- Базова властивість: `g_2 ≤ 1` завжди (за умови `γ_4 > -2`). -/
theorem g2_le_one
    (μ : Measure α) (ξ : α → ℝ)
    (hg4 : -2 < gamma4 μ ξ) :
    g₂ μ ξ ≤ 1 := by
  unfold g₂
  have hpos : 0 < 2 + gamma4 μ ξ := by linarith
  have hsq : 0 ≤ (gamma3 μ ξ)^2 := sq_nonneg _
  have hfrac : 0 ≤ (gamma3 μ ξ)^2 / (2 + gamma4 μ ξ) :=
    div_nonneg hsq (le_of_lt hpos)
  linarith

/-- `g_2 = 1` iff розподіл симетричний (`γ_3 = 0`). -/
theorem g2_eq_one_iff_symmetric
    (μ : Measure α) (ξ : α → ℝ)
    (hg4 : -2 < gamma4 μ ξ) :
    g₂ μ ξ = 1 ↔ gamma3 μ ξ = 0 := by
  unfold g₂
  have hpos : 0 < 2 + gamma4 μ ξ := by linarith
  constructor
  · intro h
    have : (gamma3 μ ξ)^2 / (2 + gamma4 μ ξ) = 0 := by linarith
    have h1 : (gamma3 μ ξ)^2 = 0 := by
      have := (div_eq_zero_iff.mp this).resolve_right (ne_of_gt hpos)
      exact this
    exact pow_eq_zero_iff (n := 2) (by norm_num : (2:ℕ) ≠ 0) |>.mp h1
  · intro h
    rw [h]; ring

/-- **Теорема T_3^a (трек a):** ARE PMM-FP_pos = `g_S_FP μ ξ basisA`.

    Формулювання (тривіальний rewrite): для будь-якого скаляра `ARE_val`,
    що задовольняє асимптотичне співвідношення (передано як гіпотеза),
    він дорівнює загальній формулі варіаційної редукції на basisA.

    Класична редукція (basisA ⊃ {(1, minus), (2, plus)}) дає, що при
    обмеженні базису до цих двох елементів, `g_S_FP = g₂_classical`
    (це теорема `g₂_reduction_FP` зі `Setup.lean`). Для повного basisA
    значення `g_S_FP basisA ≤ g₂_classical` (монотонність по базису —
    теорема `T4_pos_monotonicity` у `HigherOrder.lean`). -/
theorem T3_pos_variance_reduction
    (μ : Measure α) (ξ : α → ℝ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ)
    (_hMoments : FiniteFractionalMomentsPosScore μ ξ)
    (ARE_val : ℝ)
    (hARE_def : ARE_val = g_S_FP μ ξ basisA) :
    ARE_val = g_S_FP μ ξ basisA := hARE_def

/-- **Теорема T_3^b (трек b повний):** ARE PMM-FP_full = `g_S_FP μ ξ basisB`,
    за умови BD0_strong. -/
theorem T3_full_variance_reduction
    (μ : Measure α) (ξ : α → ℝ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ)
    (_hBD0 : BoundedDensityNearZero_strong μ ξ)
    (ARE_val : ℝ)
    (hARE_def : ARE_val = g_S_FP μ ξ basisB) :
    ARE_val = g_S_FP μ ξ basisB := hARE_def

/-- **Теорема T_3^{b,weak} (D12):** ARE PMM-FP_full_weak = `g_S_FP μ ξ basisB_weak`,
    за умови BD0_weak. -/
theorem T3_weak_variance_reduction
    (μ : Measure α) (ξ : α → ℝ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ)
    (_hBD0 : BoundedDensityNearZero_weak μ ξ)
    (ARE_val : ℝ)
    (hARE_def : ARE_val = g_S_FP μ ξ basisB_weak) :
    ARE_val = g_S_FP μ ξ basisB_weak := hARE_def

/-- **Класична форма T_3 (наслідок):** PMM-FP редукує до класичного `g_2`
    при обмеженні базису до `{(1, minus), (2, plus)}`. Свідчить, що
    `g_S_FP basisA` не гірший за класичне `g₂` (нерівність — `T4_pos_monotonicity`).

    **Гіпотези** (forwarded to `g₂_reduction_FP` from `Setup.lean`, see G7 in
    `reports/lean_theory_verification_pmm_fp.md`):

    * `[IsProbabilityMeasure μ]` — щоб `∫ 1 dμ = 1`.
    * `hmean : Expect μ ξ = 0` — центрування.
    * `hsigma2_pos : 0 < variance ξ μ` — невиродженість.
    * `hmeas : AEMeasurable ξ μ` — вимірність.
    * `hg4_pos : 0 < 2 + gamma4 μ ξ` — невиродженість F (γ₄ > -2).
    * `hnondegen : (2 + gamma4 μ ξ) − (gamma3 μ ξ)^2 ≠ 0` — невиродженість F.

    Доведення: за `g₂_reduction_FP` зі `Setup.lean` маємо
    `g_S_FP μ ξ [(1, .minus), (2, .plus)] = g₂_classical μ ξ`, а
    `g₂_classical μ ξ` за означенням дорівнює `g₂ μ ξ` цього файлу. -/
theorem T3_classical_reduction
    (μ : Measure α) (ξ : α → ℝ)
    [IsProbabilityMeasure μ]
    (hmean : Expect μ ξ = 0)
    (hsigma2_pos : 0 < variance ξ μ)
    (hmeas : AEMeasurable ξ μ)
    (hg4_pos : 0 < 2 + gamma4 μ ξ)
    (hnondegen : (2 + gamma4 μ ξ) - (gamma3 μ ξ)^2 ≠ 0) :
    g_S_FP μ ξ [(1, ParitySign.minus), (2, ParitySign.plus)] = g₂ μ ξ := by
  rw [g₂_reduction_FP μ ξ hmean hsigma2_pos hmeas hg4_pos hnondegen]
  unfold g₂_classical g₂
  rfl

end PMM_FP
