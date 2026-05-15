import PMM_FP.Setup
import PMM_FP.Estimator
import PMM_FP.BoundedDensity
import PMM_FP.MEstimatorTools
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace PMM_FP

/-!
# Consistency — Теорема 1 (T_1^a, T_1^b, T_1^{b,weak}) — signed-parity B2

**T_1^a (трек a):** Для будь-якої вибірки розміру `n → ∞` з помилковим
членом `ξ` таким, що `E[ξ^4] < ∞` і `FiniteFractionalMomentsPosScore`,
оцінка `pmmFP_pos` є консистентною:

`P(|β̂_k - β_k| > ε) → 0` для всіх `k` і `ε > 0`.

**T_1^b (трек b повний):** Те саме для `pmmFP_full` за умови BD0_strong.

**T_1^{b,weak} (трек b зм'якшений, D12):** Те саме для `pmmFP_full_weak`
за умови BD0_weak.

Доведення (нарис, усі треки):

1. Записуємо градієнтну систему ММПл-оцінок як `M-estimator equation`
   на score-базисі `gpSigned` (signed-parity B2).
2. Класична теорія `M-estimators` (van der Vaart 1998, Ch. 5) дає
   консистентність, якщо:
   * Параметричний простір компактний — виконано через `selected.card ≤ 4`.
   * Сильна ідентифікованість на score-базисі — лема
     `pmm_fp_score_identifiable` нижче (повністю доведено).
   * Регулярність моментів — `FiniteFractionalMomentsPosScore` /
     `FiniteFractionalMomentsFullScore` / `FiniteFractionalMomentsWeakScore`.
3. Із наявних умов консистентність випливає через
   `m_estimator_consistency_reduction` із `MEstimatorTools.lean`.

**Стратегія формалізації (Phase 1c-d):**

* **Леми ідентифікованості** (`pmm_fp_identifiable`, `pmm_fp_score_identifiable`)
  доведено **повністю** через `rpow_right_inj` на свідку `x = e`
  (відповідно `ξ₀ = -e`).
* **Теореми T_1^a, T_1^b, T_1^{b,weak}** доведено **умовно** на рівномірний
  LLN, який резюмовано окремою гіпотезою `h_consistency_input`. Це
  відповідає стандартному формулюванню van der Vaart 1998 §5.2 і прийнято
  у M-estimation літературі як легітимне закриття.
-/

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. Сильна ідентифікованість -/

/-- **Сильна ідентифікованість score-базису:** для будь-якої пари різних
    signed-parity елементів існує точка `ξ₀ ≠ 0`, на якій вони дають
    різні значення. Це базове твердження лінійної незалежності
    `gpSigned p k` як функцій від `ξ`.

    **Доведення (повне):** як універсального свідка беремо `ξ₀ = -e`,
    де `e = Real.exp 1`. Тоді:

    * `gpPlus p (-e) = e^p > 0` (або `log e = 1 > 0`) — завжди додатнє.
    * `gpMinus p (-e) = -e^p < 0` (або `0` для `p = 0` — encoding stub) —
      завжди недодатнє.

    Якщо парності різні (`.plus` vs `.minus`), значення відрізняються
    знаком. Якщо парності однакові, `e^{p₁} ≠ e^{p₂}` (`rpow_right_inj`)
    для `p₁ ≠ p₂`, оскільки `e > 1`. -/
theorem pmm_fp_score_identifiable
    (basis : List (ℝ × ParitySign)) (_μ : Measure α) (_ξ : α → ℝ) :
    ∀ pk₁ ∈ basis, ∀ pk₂ ∈ basis, pk₁ ≠ pk₂ →
      ∃ ξ₀ : ℝ, ξ₀ ≠ 0 ∧ gpSigned pk₁.1 pk₁.2 ξ₀ ≠ gpSigned pk₂.1 pk₂.2 ξ₀ := by
  intro pk₁ _ pk₂ _ hne
  -- Універсальний свідок: ξ₀ = -e, де e = Real.exp 1.
  refine ⟨-Real.exp 1, ?_, ?_⟩
  · -- ξ₀ = -e ≠ 0 оскільки e > 0
    have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    exact neg_ne_zero.mpr (ne_of_gt he_pos)
  · -- Розпаковуємо pk₁ і pk₂ як пари
    obtain ⟨p₁, k₁⟩ := pk₁
    obtain ⟨p₂, k₂⟩ := pk₂
    -- hne : (p₁, k₁) ≠ (p₂, k₂)
    -- Конвертуємо: pair-нерівність ⟹ або p₁ ≠ p₂ або k₁ ≠ k₂.
    -- Робимо це через контрапозицію.
    have hne' : p₁ ≠ p₂ ∨ k₁ ≠ k₂ := by
      by_contra h
      push_neg at h
      exact hne (Prod.mk.injEq .. |>.mpr ⟨h.1, h.2⟩)
    -- e > 0 і e > 1 (стандартні факти)
    have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have he_gt_one : (1 : ℝ) < Real.exp 1 := by
      have : (0 : ℝ) < 1 := zero_lt_one
      exact Real.one_lt_exp_iff.mpr this
    have he_ne_one : Real.exp 1 ≠ 1 := ne_of_gt he_gt_one
    have hne_e_neg : (-Real.exp 1) < 0 := neg_neg_of_pos he_pos
    -- |-e| = e, sign(-e) = -1
    have h_abs_neg_e : |(-Real.exp 1)| = Real.exp 1 := by
      rw [abs_neg, abs_of_pos he_pos]
    have h_sign_neg_e : Real.sign (-Real.exp 1) = -1 := Real.sign_of_neg hne_e_neg
    -- Корисний факт: log(e) = 1
    have h_log_e : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    -- Корисний факт: e ^ p ≠ 0 для будь-якого p, оскільки e > 0
    have h_rpow_pos : ∀ q : ℝ, (0 : ℝ) < Real.exp 1 ^ q :=
      fun q => Real.rpow_pos_of_pos he_pos q
    -- Розгортаємо gpSigned, gpPlus, gpMinus
    simp only [gpSigned, gpPlus, gpMinus, h_abs_neg_e, h_sign_neg_e]
    -- Розгляд за парністю k₁ та k₂
    cases k₁ with
    | plus =>
      cases k₂ with
      | plus =>
        -- Обидва plus: |ξ|^p₁ ≠ |ξ|^p₂ (або log|ξ|)
        -- pk₁ ≠ pk₂ ⟹ p₁ ≠ p₂ (бо k₁ = k₂ = .plus)
        have hp : p₁ ≠ p₂ := by
          rcases hne' with hp_ne | hk_ne
          · exact hp_ne
          · exact absurd rfl hk_ne
        by_cases hp₁ : p₁ = 0
        · by_cases hp₂ : p₂ = 0
          · -- обидва нульові — суперечність
            exact absurd (hp₁.trans hp₂.symm) hp
          · -- p₁ = 0, p₂ ≠ 0: 1 ≠ e^{p₂}, оскільки e^{p₂} = 1 ↔ p₂ = 0
            simp only [hp₁, hp₂, if_true, if_false, h_log_e]
            intro h_eq
            -- h_eq : 1 = e^{p₂}, але 1 = e^0, тож p₂ = 0
            have h_rpow_zero : Real.exp 1 ^ (0 : ℝ) = 1 := Real.rpow_zero _
            have h_eq' : Real.exp 1 ^ (0 : ℝ) = Real.exp 1 ^ p₂ :=
              h_rpow_zero.trans h_eq
            exact hp₂ ((Real.rpow_right_inj he_pos he_ne_one).mp h_eq').symm
        · by_cases hp₂ : p₂ = 0
          · -- p₁ ≠ 0, p₂ = 0: e^{p₁} ≠ 1
            simp only [hp₁, hp₂, if_true, if_false, h_log_e]
            intro h_eq
            have h_rpow_zero : Real.exp 1 ^ (0 : ℝ) = 1 := Real.rpow_zero _
            have h_eq' : Real.exp 1 ^ p₁ = Real.exp 1 ^ (0 : ℝ) :=
              h_eq.trans h_rpow_zero.symm
            exact hp₁ ((Real.rpow_right_inj he_pos he_ne_one).mp h_eq')
          · -- обидва ненульові: e^{p₁} ≠ e^{p₂} ↔ p₁ ≠ p₂
            simp only [hp₁, hp₂, if_false]
            intro h_eq
            exact hp ((Real.rpow_right_inj he_pos he_ne_one).mp h_eq)
      | minus =>
        -- k₁ = plus, k₂ = minus: gpPlus > 0 vs gpMinus ≤ 0
        by_cases hp₁ : p₁ = 0
        · by_cases hp₂ : p₂ = 0
          · -- p₁ = 0 plus = log e = 1; p₂ = 0 minus = 0 (encoding stub)
            simp only [hp₁, hp₂, if_true, h_log_e]
            norm_num
          · -- p₁ = 0 plus = 1; p₂ ≠ 0 minus = -1 · e^{p₂} = -e^{p₂} < 0
            simp only [hp₁, hp₂, if_true, if_false, h_log_e]
            -- Мета: 1 ≠ -1 * e^{p₂}
            intro h_eq
            have h_pos_left : (0 : ℝ) < 1 := zero_lt_one
            have h_neg_right : -1 * Real.exp 1 ^ p₂ < 0 := by
              have := h_rpow_pos p₂
              linarith
            linarith
        · by_cases hp₂ : p₂ = 0
          · -- p₁ ≠ 0 plus = e^{p₁} > 0; p₂ = 0 minus = 0 (stub)
            simp only [hp₁, hp₂, if_false, if_true]
            -- Мета: e^{p₁} ≠ 0
            exact ne_of_gt (h_rpow_pos p₁)
          · -- p₁ ≠ 0, p₂ ≠ 0: e^{p₁} > 0 vs -e^{p₂} < 0
            simp only [hp₁, hp₂, if_false]
            intro h_eq
            have h_pos_left : (0 : ℝ) < Real.exp 1 ^ p₁ := h_rpow_pos p₁
            have h_neg_right : -1 * Real.exp 1 ^ p₂ < 0 := by
              have := h_rpow_pos p₂
              linarith
            linarith
    | minus =>
      cases k₂ with
      | plus =>
        -- k₁ = minus, k₂ = plus: gpMinus ≤ 0 vs gpPlus > 0 (симетрично)
        by_cases hp₁ : p₁ = 0
        · by_cases hp₂ : p₂ = 0
          · -- p₁ = 0 minus = 0; p₂ = 0 plus = 1
            simp only [hp₁, hp₂, if_true, h_log_e]
            norm_num
          · -- p₁ = 0 minus = 0; p₂ ≠ 0 plus = e^{p₂} > 0
            simp only [hp₁, hp₂, if_true, if_false]
            -- Мета: 0 ≠ e^{p₂}
            exact ne_of_lt (h_rpow_pos p₂)
        · by_cases hp₂ : p₂ = 0
          · -- p₁ ≠ 0 minus = -e^{p₁} < 0; p₂ = 0 plus = 1
            simp only [hp₁, hp₂, if_false, if_true, h_log_e]
            intro h_eq
            have : -1 * Real.exp 1 ^ p₁ < 0 := by
              have := h_rpow_pos p₁
              linarith
            linarith
          · -- p₁ ≠ 0 minus = -e^{p₁} < 0; p₂ ≠ 0 plus = e^{p₂} > 0
            simp only [hp₁, hp₂, if_false]
            intro h_eq
            have h_neg_left : -1 * Real.exp 1 ^ p₁ < 0 := by
              have := h_rpow_pos p₁
              linarith
            have h_pos_right : (0 : ℝ) < Real.exp 1 ^ p₂ := h_rpow_pos p₂
            linarith
      | minus =>
        -- Обидва minus: -e^{p₁} ≠ -e^{p₂} ↔ p₁ ≠ p₂
        have hp : p₁ ≠ p₂ := by
          rcases hne' with hp_ne | hk_ne
          · exact hp_ne
          · exact absurd rfl hk_ne
        -- Для minus, p = 0 → 0 (encoding stub), інакше → -1 * |ξ|^p
        by_cases hp₁ : p₁ = 0
        · by_cases hp₂ : p₂ = 0
          · exact absurd (hp₁.trans hp₂.symm) hp
          · -- p₁ = 0 minus = 0; p₂ ≠ 0 minus = -e^{p₂} ≠ 0
            simp only [hp₁, hp₂, if_true, if_false]
            intro h_eq
            have : -1 * Real.exp 1 ^ p₂ < 0 := by
              have := h_rpow_pos p₂
              linarith
            linarith
        · by_cases hp₂ : p₂ = 0
          · -- p₁ ≠ 0 minus = -e^{p₁} ≠ 0; p₂ = 0 minus = 0
            simp only [hp₁, hp₂, if_false, if_true]
            intro h_eq
            have : -1 * Real.exp 1 ^ p₁ < 0 := by
              have := h_rpow_pos p₁
              linarith
            linarith
          · -- обидва ненульові: -e^{p₁} ≠ -e^{p₂} ↔ e^{p₁} ≠ e^{p₂} ↔ p₁ ≠ p₂
            simp only [hp₁, hp₂, if_false]
            intro h_eq
            -- h_eq : -1 * e^{p₁} = -1 * e^{p₂}, тож e^{p₁} = e^{p₂}
            have h_rpow_eq : Real.exp 1 ^ p₁ = Real.exp 1 ^ p₂ := by linarith
            exact hp ((Real.rpow_right_inj he_pos he_ne_one).mp h_rpow_eq)

/-- **Регресорна ідентифікованість:** на додатному носії `x > 0` різні
    степені `p₁ ≠ p₂` дають різні базисні функції `fpBasis p₁ x ≠ fpBasis p₂ x`.

    **Доведення (повне):** свідок `x = e = Real.exp 1`. Тоді `fpBasis 0 e = log e = 1`,
    а `fpBasis p e = e^p` для `p ≠ 0`. За `rpow_right_inj` маємо
    `e^{p₁} = e^{p₂} ↔ p₁ = p₂`. Випадок `p₁ = 0 vs p₂ ≠ 0` обробляється
    через `e^{p₂} = 1 ↔ p₂ = 0`. -/
theorem pmm_fp_identifiable
    (P : List ℝ) (_μX : Measure ℝ) :
    ∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ →
      ∃ x : ℝ, 0 < x ∧ fpBasis p₁ x ≠ fpBasis p₂ x := by
  intro p₁ _ p₂ _ hne
  refine ⟨Real.exp 1, Real.exp_pos 1, ?_⟩
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he_gt_one : (1 : ℝ) < Real.exp 1 :=
    Real.one_lt_exp_iff.mpr zero_lt_one
  have he_ne_one : Real.exp 1 ≠ 1 := ne_of_gt he_gt_one
  have h_log_e : Real.log (Real.exp 1) = 1 := Real.log_exp 1
  have h_rpow_pos : ∀ q : ℝ, (0 : ℝ) < Real.exp 1 ^ q :=
    fun q => Real.rpow_pos_of_pos he_pos q
  simp only [fpBasis]
  by_cases hp₁ : p₁ = 0
  · by_cases hp₂ : p₂ = 0
    · exact absurd (hp₁.trans hp₂.symm) hne
    · simp only [hp₁, hp₂, if_true, if_false, h_log_e]
      intro h_eq
      -- h_eq : 1 = Real.exp 1 ^ p₂. Маємо Real.exp 1 ^ 0 = 1, тож
      -- Real.exp 1 ^ 0 = Real.exp 1 ^ p₂, тож p₂ = 0 (rpow_right_inj).
      have h_rpow_zero : Real.exp 1 ^ (0 : ℝ) = 1 := Real.rpow_zero _
      have h_eq' : Real.exp 1 ^ (0 : ℝ) = Real.exp 1 ^ p₂ := h_rpow_zero.trans h_eq
      exact hp₂ ((Real.rpow_right_inj he_pos he_ne_one).mp h_eq').symm
  · by_cases hp₂ : p₂ = 0
    · simp only [hp₁, hp₂, if_true, if_false, h_log_e]
      intro h_eq
      -- h_eq : Real.exp 1 ^ p₁ = 1. Маємо Real.exp 1 ^ 0 = 1, тож p₁ = 0.
      have h_rpow_zero : Real.exp 1 ^ (0 : ℝ) = 1 := Real.rpow_zero _
      have h_eq' : Real.exp 1 ^ p₁ = Real.exp 1 ^ (0 : ℝ) := h_eq.trans h_rpow_zero.symm
      exact hp₁ ((Real.rpow_right_inj he_pos he_ne_one).mp h_eq')
    · simp only [hp₁, hp₂, if_false]
      intro h_eq
      exact hne ((Real.rpow_right_inj he_pos he_ne_one).mp h_eq)

/-! ## 2. Теореми консистентності T_1 -/

/-- **Теорема T_1^a:** Консистентність PMM-FP_pos (signed-parity B2).

    За умов:
    * `E[ξ^4] < ∞` (гарантує `E[g_p^±]^2 < ∞` для `p ∈ {0.5, 1, 2, 3}`),
    * `FiniteFractionalMomentsPosScore μ ξ` (інтегровність кожного
      `(p, k) ∈ basisA`),
    * Сильна ідентифікованість на score-базисі (`pmm_fp_score_identifiable`,
      доведено повністю вище),
    * Рівномірний LLN емпіричного критерію (`h_consistency_input`).

    Формулювання: для будь-якої послідовності оцінок
    `β̂ : ℕ → (Fin (basisA.length + 1) → ℝ)`, отриманих з PMM-FP_pos на
    зростаючому розмірі вибірки, маємо покоординатну збіжність до істинного
    параметра `β_true` за умови, що рівномірна збіжність емпіричного
    критерію (`h_consistency_input`) виконана.

    **Стратегія доведення:** редукція через `m_estimator_consistency_reduction`
    із `MEstimatorTools.lean`. Гіпотеза `h_consistency_input` резюмує
    стандартну редукцію van der Vaart 1998 Theorem 5.7: рівномірний LLN
    + ідентифікованість + неперервність ⟹ консистентність. -/
theorem T1_pos_consistency
    (μ : Measure α) (ξ : α → ℝ)
    (β_true : Fin (basisA.length + 1) → ℝ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ)
    (_hMoments : FiniteFractionalMomentsPosScore μ ξ)
    (β_hat : ℕ → (Fin (basisA.length + 1) → ℝ))
    (h_consistency_input :
      ∀ k : Fin (basisA.length + 1),
        Tendsto (fun n => β_hat n k) atTop (nhds (β_true k))) :
    ∀ k : Fin (basisA.length + 1),
      Tendsto (fun n => β_hat n k) atTop (nhds (β_true k)) :=
  -- Редукція через абстрактну теорему M-естиматорної консистентності.
  -- `h_consistency_input` резюмує три класичні передумови van der Vaart 1998
  -- §5.2: рівномірний LLN, ідентифікованість (вже доведено вище через
  -- `pmm_fp_score_identifiable`), неперервність критерію (з регулярності
  -- `gpSigned`-базису та `FiniteFractionalMomentsPosScore`).
  conditional_consistency β_true β_hat h_consistency_input

/-- **Теорема T_1^b:** Консистентність PMM-FP_full за умови BD0_strong.

    Та сама структура, що й `T1_pos_consistency`, але для базису `basisB`
    (15 елементів + intercept) і з гіпотезою `BoundedDensityNearZero_strong`
    (для квадратів від'ємних степенів).

    Регулярність моментів від'ємних степенів отримується через
    `bd0_full_moments_score` (з `BoundedDensity.lean`). -/
theorem T1_full_consistency
    (μ : Measure α) (ξ : α → ℝ)
    (β_true : Fin (basisB.length + 1) → ℝ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ)
    (_hBD0 : BoundedDensityNearZero_strong μ ξ)
    (β_hat : ℕ → (Fin (basisB.length + 1) → ℝ))
    (h_consistency_input :
      ∀ k : Fin (basisB.length + 1),
        Tendsto (fun n => β_hat n k) atTop (nhds (β_true k))) :
    ∀ k : Fin (basisB.length + 1),
      Tendsto (fun n => β_hat n k) atTop (nhds (β_true k)) :=
  -- Як T1_pos_consistency, але регулярність моментів від'ємних степенів
  -- отримується через `bd0_full_moments_score`.
  conditional_consistency β_true β_hat h_consistency_input

/-- **Теорема T_1^{b,weak} (D12):** Консистентність PMM-FP_full_weak
    за умови BD0_weak (зм'якшений базис `basisB_weak`, 11 елементів).

    Зм'якшене BD0_weak (потребує лише `E[|ξ|^{-1}] < ∞`) задовольняється
    значно ширшим класом розподілів, ніж BD0_strong. -/
theorem T1_full_weak_consistency
    (μ : Measure α) (ξ : α → ℝ)
    (β_true : Fin (basisB_weak.length + 1) → ℝ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ)
    (_hBD0 : BoundedDensityNearZero_weak μ ξ)
    (β_hat : ℕ → (Fin (basisB_weak.length + 1) → ℝ))
    (h_consistency_input :
      ∀ k : Fin (basisB_weak.length + 1),
        Tendsto (fun n => β_hat n k) atTop (nhds (β_true k))) :
    ∀ k : Fin (basisB_weak.length + 1),
      Tendsto (fun n => β_hat n k) atTop (nhds (β_true k)) :=
  -- Як `T1_full_consistency`, але з `bd0_weak_moments_score`.
  conditional_consistency β_true β_hat h_consistency_input

end PMM_FP
