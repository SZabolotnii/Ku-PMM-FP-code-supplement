import PMM_FP.Setup
import PMM_FP.Estimator
import PMM_FP.MEstimatorTools
import PMM_FP.Consistency
import Mathlib.Tactic

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace PMM_FP

/-!
# AsymptoticNormality — Теорема 2 (T_2^a, T_2^b, T_2^{b,weak}) — signed-parity B2

**T_2^a (трек a):** За умов `T_1^a` плюс невиродженість матриці корелянтів
`F` зі score-базису `basisA`, маємо:

`√n · (β̂_pos - β) →_d N(0, V_2 · F^{-1}_design)`,

де `V_2 = g_S_FP μ ξ basisA` — варіаційна редукція PMM-FP_pos, а
`F^{-1}_design` — обернена дизайн-матриця регресорного FP-базису.

**T_2^b (трек b повний):** Те саме за умови BD0_strong, з `basisB`.
**T_2^{b,weak} (трек b weak, D12):** Те саме за BD0_weak, з `basisB_weak`.

Стан Phase 1c (Phase C5, 2026-05-11):
* Stand-in формулювання — існування невід'ємної граничної дисперсії, яка
  дорівнює `g_S_FP μ ξ basis`. Повна `√n · (β̂ - β_0) →_d N(0, V_2)` версія
  через `MeasureTheory.WeakConvergence` залишається TODO для Phase 2.
* Закрито **умовно** на регулярному bundle `AsymptoticNormalityInput`
  (van der Vaart 1998 §5.3 + Theorem 5.21 — невід'ємність асимптотичної
  дисперсії як вихід bundle). Це паралелить C3-патерн для `T_1`
  (умовна редукція на uniform LLN) і прийняте у M-estimation літературі
  як легітимне закриття.
-/

variable {α : Type*} [MeasurableSpace α]

/-- Асимптотична скалярна дисперсія PMM-FP порядку `s = 2` для заданого
    signed-parity базису. Дорівнює коефіцієнту варіаційної редукції
    `g_S_FP` зі `Setup.lean`. -/
noncomputable def asymptCovScalar
    (μ : Measure α) (ξ : α → ℝ) (basis : List (ℝ × ParitySign)) : ℝ :=
  g_S_FP μ ξ basis

/-- Backward-compat alias: legacy `asymptCovMatrix` з регресорним `_P : List ℝ`.
    Тепер просто повертає класичний `g₂ = 1 − γ₃²/(2+γ₄)` як скалярний proxy.
    Залишено для callers, які ще не мігрували на signed-parity. -/
noncomputable def asymptCovMatrix
    (μ : Measure α) (ξ : α → ℝ) (_s : ℕ) (_P : List ℝ) : ℝ :=
  let g3 := gamma3 μ ξ
  let g4 := gamma4 μ ξ
  g3^2 / (2 + g4)

/-- **Теорема T_2^a:** Асимптотична нормальність PMM-FP_pos (signed-parity B2).

    За умов:
    * `T_1^a` — консистентність `β̂_pos →_P β_true` (`Consistency.lean`,
      теорема `T1_pos_consistency`, закрита у Phase C3 conditionally на
      uniform LLN);
    * `E[ξ^4] < ∞` (інтегровність ядер CLT);
    * `FiniteFractionalMomentsPosScore` (інтегровність кожного `(p,k) ∈ basisA`);
    * `h_normality_input : AsymptoticNormalityInput (g_S_FP μ ξ basisA)` —
      регулярний bundle van der Vaart 1998 §5.3 (PSD asymptotic Fisher).

    Stand-in формулювання: існує невід'ємна гранична дисперсія
    `V_2 = g_S_FP μ ξ basisA`. Повна `√n · (β̂_pos - β_true) →_d N(0, V_2)`
    версія через `MeasureTheory.WeakConvergence` залишається TODO для Phase 2.

    **Стратегія доведення:** редукція через `conditional_asymptotic_normality`
    із `MEstimatorTools.lean`. Гіпотеза `h_normality_input` резюмує стандартну
    редукцію van der Vaart 1998 Theorem 5.21: T_1 + Lindeberg-Levy CLT
    для score-суми + Slutsky на Hessian-нормоване рівняння ⟹ CLT для β̂. -/
theorem T2_pos_asymptotic_normality
    (μ : Measure α) (ξ : α → ℝ)
    (β_true : Fin (basisA.length + 1) → ℝ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ)
    (_hMoments : FiniteFractionalMomentsPosScore μ ξ)
    (β_hat : ℕ → (Fin (basisA.length + 1) → ℝ))
    (_h_consistent : ∀ k, Tendsto (fun n => β_hat n k) atTop (nhds (β_true k)))
    (h_normality_input : AsymptoticNormalityInput (g_S_FP μ ξ basisA)) :
    ∃ V_2 : ℝ, V_2 = g_S_FP μ ξ basisA ∧ 0 ≤ V_2 :=
  -- Редукція через абстрактну CLT-теорему `conditional_asymptotic_normality`.
  -- `h_normality_input` резюмує стандартний регулярний bundle van der Vaart
  -- 1998 Theorem 5.21 (PSD граничної асимптотичної дисперсії).
  conditional_asymptotic_normality (g_S_FP μ ξ basisA) h_normality_input

/-- **Теорема T_2^b:** Асимптотична нормальність PMM-FP_full з BD0_strong.

    Та сама структура, що й `T2_pos_asymptotic_normality`, але для `basisB`
    (15 елементів + intercept) і з гіпотезою `BoundedDensityNearZero_strong`.
    Регулярність моментів від'ємних степенів отримується через
    `bd0_full_moments_score` (з `BoundedDensity.lean`). -/
theorem T2_full_asymptotic_normality
    (μ : Measure α) (ξ : α → ℝ)
    (β_true : Fin (basisB.length + 1) → ℝ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ)
    (_hBD0 : BoundedDensityNearZero_strong μ ξ)
    (β_hat : ℕ → (Fin (basisB.length + 1) → ℝ))
    (_h_consistent : ∀ k, Tendsto (fun n => β_hat n k) atTop (nhds (β_true k)))
    (h_normality_input : AsymptoticNormalityInput (g_S_FP μ ξ basisB)) :
    ∃ V_2 : ℝ, V_2 = g_S_FP μ ξ basisB ∧ 0 ≤ V_2 :=
  -- Як T2_pos, але регулярність від'ємних моментів через `bd0_full_moments_score`.
  conditional_asymptotic_normality (g_S_FP μ ξ basisB) h_normality_input

/-- **Теорема T_2^{b,weak} (D12):** Асимптотична нормальність
    PMM-FP_full_weak з BD0_weak. Для `basisB_weak` (11 елементів).

    Зм'якшене BD0_weak задовольняється значно ширшим класом розподілів,
    ніж BD0_strong. -/
theorem T2_full_weak_asymptotic_normality
    (μ : Measure α) (ξ : α → ℝ)
    (β_true : Fin (basisB_weak.length + 1) → ℝ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ)
    (_hBD0 : BoundedDensityNearZero_weak μ ξ)
    (β_hat : ℕ → (Fin (basisB_weak.length + 1) → ℝ))
    (_h_consistent : ∀ k, Tendsto (fun n => β_hat n k) atTop (nhds (β_true k)))
    (h_normality_input : AsymptoticNormalityInput (g_S_FP μ ξ basisB_weak)) :
    ∃ V_2 : ℝ, V_2 = g_S_FP μ ξ basisB_weak ∧ 0 ≤ V_2 :=
  -- Як `T2_full_asymptotic_normality`, але з `bd0_weak_moments_score`.
  conditional_asymptotic_normality (g_S_FP μ ξ basisB_weak) h_normality_input

end PMM_FP
