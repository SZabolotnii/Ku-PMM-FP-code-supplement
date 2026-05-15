import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace PMM_FP

/-!
# Setup — спільні означення PMM-FP (signed-parity B2 convention, Phase 1b)

Файл встановлює:

* Базисні набори степенів `P_a`, `P_b`, `P_b_weak` (D12).
* **Дві концептуально різні** сім'ї базисних функцій:
  1. `fpBasis`, `fpBasisLog` — **регресорний** базис на додатному носії `x > 0`
     у конвенції Royston-Altman (`x^0 ≡ ln x`). Використовується у моделі
     `η_i = β_0 + Σ_k γ_k β_k f_k(x_i)` (інтерпретація а).
  2. `gpPlus`, `gpMinus`, `gpSigned` — **score** базис на дійсних залишках
     `ξ ∈ ℝ` із sign-конвенцією B2 (signed absolute values). Використовується
     у стохастичному поліномі Кунченка
     `ψ_h^(FP)(ξ) = Σ h_i (g_i(ξ) − E[g_i(ξ)])` (інтерпретація б).
* `ParitySign` (індуктивний тип `plus | minus`) і явні базисні списки
  `basisA`, `basisB`, `basisB_weak` після виключення розбіжного елемента
  `g_0^-` (див. лему `g0Minus_excluded`).
* Центрований корелянт `fpCorrelant` для signed-parity базису.
* Загальна формула варіаційної редукції `g_S_FP` (defined через `Matrix.of`).
* Класична `g₂_classical = 1 − γ₃² / (2 + γ₄)` як частковий випадок.
* Кумулянти `γ_3, γ_4` залишкового члена.

**Походження конвенції:** `reports/pmm_fp_theoretical_framework.md`, §§ 1–3, 5.

**Сумісність:** означення `fpBasis`, `fpBasisLog`, `Expect`, `gamma3`, `gamma4`,
`FiniteFractionalMomentsPos`, а також legacy alias `centredCorrelant` —
збережено для зворотної сумісності з `Estimator.lean`, `Consistency.lean`,
`BoundedDensity.lean`, `VarianceReduction.lean`, `AsymptoticNormality.lean`,
`HigherOrder.lean`, `ModelSelection.lean`. Концептуально downstream-файли
використовують `fpBasis` на `ξ` (real-valued), що для негативних степенів
вимагає сигнованої конвенції — це залишається TODO для Phase 1c.
-/

/-! ## 1. Базисні набори степенів -/

/-- Базис треку (a): невід'ємні степені `{0, 0.5, 1, 2, 3}`.
    Тут `0` представляє конвенцію `x^0 ≡ ln x` (для регресора) або
    `g_0^+(ξ) ≡ ln|ξ|` (для залишку). -/
def P_a : List ℝ := [0, 0.5, 1, 2, 3]

/-- Базис треку (b) повний: Royston-Altman `{-2, -1, -0.5, 0, 0.5, 1, 2, 3}`. -/
def P_b : List ℝ := [-2, -1, -0.5, 0, 0.5, 1, 2, 3]

/-- Зм'якшений базис треку (b) (D12): без `{-2, -1}` для більшого класу
    розподілів, що задовольняють BD0_PMM-FP_full
    (див. `reports/pmm_fp_theoretical_framework.md`, §§ 4.2, 7.3). -/
def P_b_weak : List ℝ := [-0.5, 0, 0.5, 1, 2, 3]

/-! ## 2. Регресорний базис (інтерпретація а): для `x > 0` -/

/-- Регресорна FP-базисна функція з конвенцією `x^0 ≡ ln x`.
    Визначена для додатного `x > 0` (носій регресора).
    Використовується у моделі `η_i = β_0 + Σ_k γ_k β_k · fpBasis p_k (x_i)`. -/
noncomputable def fpBasis (p : ℝ) (x : ℝ) : ℝ :=
  if p = 0 then Real.log x else x ^ p

/-- Розширена регресорна базисна функція з ln-взаємодією
    (`f(x) = x^p · ln x`) — для дублювальних степенів Royston-Sauerbrei. -/
noncomputable def fpBasisLog (p : ℝ) (x : ℝ) : ℝ :=
  if p = 0 then (Real.log x)^2 else x^p * Real.log x

/-! ## 3. Score базис (інтерпретація б): signed-parity B2 для `ξ ∈ ℝ` -/

/-- Парність базисного елемента score-функції: `plus` для парних `g_p^+`,
    `minus` для непарних `g_p^-`. -/
inductive ParitySign
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Парна базисна функція PMM-FP score: `g_p^+(ξ) = |ξ|^p` для `p ≠ 0`,
    або `g_0^+(ξ) = ln |ξ|` для `p = 0`.

    Інтегровна за умови `E[|ξ|^p] < ∞` (для `p > 0`) або
    `E[(ln|ξ|)^2] < ∞` (для `p = 0`). -/
noncomputable def gpPlus (p : ℝ) (ξ : ℝ) : ℝ :=
  if p = 0 then Real.log (|ξ|) else (|ξ|) ^ p

/-- Непарна базисна функція PMM-FP score: `g_p^-(ξ) = sign(ξ) · |ξ|^p`.

    **Виключення:** елемент `g_0^-` структурно несумісний, бо його похідна
    `(g_0^-)'(ξ) = 1 / |ξ|` має нескінченне математичне сподівання
    для будь-якого розподілу з `f_ξ(0) > 0`
    (див. лему `g0Minus_divergent`, `reports/pmm_fp_theoretical_framework.md`, §5).

    Тут для `p = 0` повертаємо `0` лише як encoding-only stub, аби тип
    скомпілювався. Справжній `g_0^-` ніколи не використовується у `basisA`,
    `basisB`, `basisB_weak` — це гарантує лема `g0Minus_excluded`. -/
noncomputable def gpMinus (p : ℝ) (ξ : ℝ) : ℝ :=
  if p = 0 then 0
  else Real.sign ξ * (|ξ|) ^ p

/-- Уніфіковане означення signed-parity базисної функції.
    Зручніше для індексації базисних списків як пар `(p, k)`. -/
noncomputable def gpSigned (p : ℝ) (k : ParitySign) (ξ : ℝ) : ℝ :=
  match k with
  | .plus  => gpPlus p ξ
  | .minus => gpMinus p ξ

/-! ## 4. Індексовані базисні списки після виключення `g_0^-` -/

/-- Базис треку (а): 9 елементів (формальний номінал 10 мінус виключений `g_0^-`).
    Перелічено явно для прозорості. -/
def basisA : List (ℝ × ParitySign) :=
  [(0,   .plus),                       -- g_0^+ = ln |ξ|
   (0.5, .plus), (0.5, .minus),
   (1,   .plus), (1,   .minus),
   (2,   .plus), (2,   .minus),
   (3,   .plus), (3,   .minus)]

/-- Базис треку (b) повний: 15 елементів (номінал 16 мінус `g_0^-`). -/
def basisB : List (ℝ × ParitySign) :=
  [(-2,   .plus), (-2,   .minus),
   (-1,   .plus), (-1,   .minus),
   (-0.5, .plus), (-0.5, .minus),
   (0,    .plus),                      -- g_0^+ = ln |ξ|
   (0.5,  .plus), (0.5,  .minus),
   (1,    .plus), (1,    .minus),
   (2,    .plus), (2,    .minus),
   (3,    .plus), (3,    .minus)]

/-- Зм'якшений базис треку (b) (D12): 11 елементів. -/
def basisB_weak : List (ℝ × ParitySign) :=
  [(-0.5, .plus), (-0.5, .minus),
   (0,    .plus),                      -- g_0^+ = ln |ξ|
   (0.5,  .plus), (0.5,  .minus),
   (1,    .plus), (1,    .minus),
   (2,    .plus), (2,    .minus),
   (3,    .plus), (3,    .minus)]

/-! ## 5. Очікування і кумулянти -/

variable {α : Type*} [MeasurableSpace α]

/-- Очікування реальної випадкової величини відносно міри. -/
noncomputable def Expect (μ : Measure α) (f : α → ℝ) : ℝ :=
  ∫ x, f x ∂ μ

/-- Третій нормований кумулянт (skewness coefficient) `γ_3`. -/
noncomputable def gamma3 (μ : Measure α) (ξ : α → ℝ) : ℝ :=
  Expect μ (fun a => (ξ a - Expect μ ξ)^3) /
  (variance ξ μ)^((3:ℝ)/2)

/-- Четвертий нормований кумулянт (excess kurtosis) `γ_4`. -/
noncomputable def gamma4 (μ : Measure α) (ξ : α → ℝ) : ℝ :=
  Expect μ (fun a => (ξ a - Expect μ ξ)^4) /
  (variance ξ μ)^2 - 3

/-! ## 6. Центровані корелянти PMM-FP -/

/-- Центрований корелянт двох signed-parity базисних функцій:

    `F_{(p₁,k₁),(p₂,k₂)} = E[g_{p₁,k₁}(ξ) · g_{p₂,k₂}(ξ)]
                           − E[g_{p₁,k₁}(ξ)] · E[g_{p₂,k₂}(ξ)]`.

    Це означення з § 2.1 `reports/pmm_fp_theoretical_framework.md`. -/
noncomputable def fpCorrelant
    (μ : Measure α) (ξ : α → ℝ)
    (p₁ : ℝ) (k₁ : ParitySign) (p₂ : ℝ) (k₂ : ParitySign) : ℝ :=
  Expect μ (fun a => gpSigned p₁ k₁ (ξ a) * gpSigned p₂ k₂ (ξ a)) -
  Expect μ (fun a => gpSigned p₁ k₁ (ξ a)) *
  Expect μ (fun a => gpSigned p₂ k₂ (ξ a))

/-- Legacy центрований корелянт (Phase 1a):
    `F_{ij} = E[fpBasis p₁ ξ · fpBasis p₂ ξ] − E[fpBasis p₁ ξ] · E[fpBasis p₂ ξ]`.

    **Deprecated:** використовує регресорну конвенцію (без sign-parity) і
    концептуально некоректний для `p < 0` із залишком `ξ ∈ ℝ`. Збережений лише
    як alias для нерефакторених callers. Нові доведення мають вживати
    `fpCorrelant` зі signed-parity індексами.

    TODO (Phase 1c): мігрувати `BoundedDensity`, `Consistency` на `fpCorrelant`
    і видалити цей alias. -/
noncomputable def centredCorrelant (μ : Measure α) (ξ : α → ℝ) (p₁ p₂ : ℝ) : ℝ :=
  Expect μ (fun a => (fpBasis p₁ (ξ a)) * (fpBasis p₂ (ξ a))) -
  (Expect μ (fun a => fpBasis p₁ (ξ a))) *
  (Expect μ (fun a => fpBasis p₂ (ξ a)))

/-! ## 7. Варіаційна редукція -/

/-- **Вектор очікуваних від'ємних похідних базисних функцій** для signed-parity FP:

    `b_i = -E[g_i'(ξ)]`,

    де `g_i = g_{p_i}^{k_i}` — i-та базисна функція. Аналітичні похідні:

    * `(g_p^+)'(ξ) = p·sign(ξ)·|ξ|^(p-1)` (для `p ≠ 0`), `(g_0^+)' = sign(ξ)/|ξ|`;
    * `(g_p^-)'(ξ) = p·|ξ|^(p-1)` (для `p ≠ 0`), `(g_0^-)' = 1/|ξ|` (виключено).

    Реалізовано як `Expect`-функціонал; конкретні значення для класичних
    випадків (наприклад, `b_1^-` = -1, `b_2^+` = 0 для симетричних) виводяться
    спеціалізованими лемами downstream. -/
noncomputable def fpBVector
    (μ : Measure α) (ξ : α → ℝ)
    (p : ℝ) (k : ParitySign) : ℝ :=
  -- b_i = -E[g_i'(ξ)]. Похідні розписані у звіті §2.2; тут — єдина
  -- уніфікована формула через скалярне `Expect` від похідної як функції ξ.
  match k with
  | .plus  =>
      -- g_p^+(ξ) = |ξ|^p (або log|ξ| при p=0)
      -- (g_p^+)'(ξ) = p·sign(ξ)·|ξ|^{p-1}     (або sign(ξ)/|ξ| при p=0)
      if p = 0 then
        - Expect μ (fun a => Real.sign (ξ a) / |ξ a|)
      else
        - p * Expect μ (fun a => Real.sign (ξ a) * (|ξ a|) ^ (p - 1))
  | .minus =>
      -- g_p^-(ξ) = sign(ξ)·|ξ|^p
      -- (g_p^-)'(ξ) = p·|ξ|^{p-1}              (або 1/|ξ| при p=0, виключено)
      if p = 0 then
        - Expect μ (fun a => 1 / |ξ a|)
      else
        - p * Expect μ (fun a => (|ξ a|) ^ (p - 1))

/-- **Загальна формула варіаційної редукції PMM-FP:**

    `g_S^(FP) = 1 / (σ² · b^T · F^{-1} · b)`,

    де `F : Matrix (Fin K) (Fin K) ℝ` — матриця центрованих корелянтів
    `fpCorrelant`, `b : Fin K → ℝ` — вектор очікуваних від'ємних похідних
    (`fpBVector`), `σ² = variance ξ μ`.

    Деривація — `reports/pmm_fp_theoretical_framework.md`, §2.3.

    **Безпечні значення:** для виродженого випадку (порожній базис, нульова
    дисперсія, або `b^T F^{-1} b = 0`) повертаємо `0`. Це не статистично
    осмислене значення, лише охорона типу від ділення на нуль; реальні теореми
    downstream передбачають невиродженість через explicit hypotheses. -/
noncomputable def g_S_FP
    (μ : Measure α) (ξ : α → ℝ)
    (basis : List (ℝ × ParitySign)) : ℝ :=
  let K := basis.length
  let F : Matrix (Fin K) (Fin K) ℝ :=
    Matrix.of (fun i j =>
      let bi := basis.get i
      let bj := basis.get j
      fpCorrelant μ ξ bi.1 bi.2 bj.1 bj.2)
  let b : Fin K → ℝ :=
    fun i => let bi := basis.get i; fpBVector μ ξ bi.1 bi.2
  let sigma2 := variance ξ μ
  if K = 0 ∨ sigma2 = 0 then 0
  else
    let bFb := (F⁻¹.mulVec b) ⬝ᵥ b
    if bFb = 0 then 0 else 1 / (sigma2 * bFb)

/-- Класична формула Кунченка `g₂ = 1 − γ_3² / (2 + γ_4)` (PMM2, базис
    `{ξ, ξ²}` = `{g_1^-, g_2^+}`). -/
noncomputable def g₂_classical (μ : Measure α) (ξ : α → ℝ) : ℝ :=
  1 - (gamma3 μ ξ)^2 / (2 + gamma4 μ ξ)

/-! ### Допоміжна лема: квадратична форма від оберненої 2×2 матриці -/

/-- **Helper:** замкнута формула для `v^T M^{-1} v`, де `M` — симетрична `2×2`
    матриця з ненульовим визначником. Алгебраїчне ядро доведення `g₂_reduction_FP`.

    Для `M = !![a, b; b, c]` і `v = ![d, e]`:

    `v^T M^{-1} v = (c·d² − 2·b·d·e + a·e²) / (a·c − b²)`.

    Доведення комбінує `Matrix.adjugate_fin_two_of` (зачинена форма ад'юнгати),
    `Matrix.inv_def` (`M⁻¹ = (1/det M)·adj M`), а потім розкриває `mulVec`
    і `dotProduct` через `Fin.sum_univ_two`. -/
lemma quadForm_inv_fin_two
    (a b c d e : ℝ) (_hdet : a * c - b * b ≠ 0) :
    ((!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec ![d, e]) ⬝ᵥ ![d, e]
      = (c * d * d - 2 * b * d * e + a * e * e) / (a * c - b * b) := by
  -- Determint: `det M = a*c - b*b`.
  have hdetM : (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).det = a * c - b * b := by
    rw [Matrix.det_fin_two_of]
  -- Зачинена форма `M⁻¹`: `(1/det) • adj`, де `adj = !![c, -b; -b, a]`.
  have hinv : (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
            = (a * c - b * b)⁻¹ • !![c, -b; -b, a] := by
    rw [Matrix.inv_def, Matrix.adjugate_fin_two_of, hdetM, Ring.inverse_eq_inv']
  rw [hinv]
  -- Розкриваємо `mulVec ![d, e]` як вектор Fin 2 → ℝ.
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply]
  -- Алгебраїчне зведення:
  -- ((a*c - b*b)⁻¹ * c * d + (a*c - b*b)⁻¹ * (-b) * e) * d
  -- + ((a*c - b*b)⁻¹ * (-b) * d + (a*c - b*b)⁻¹ * a * e) * e
  -- = (c·d² - 2·b·d·e + a·e²) / (a·c - b·b)
  field_simp
  ring

/-- **Редукційна теорема (G7 — Phase 2 deliverable):**
    класична `g₂` дорівнює загальному `g_S^FP` при класичному базисі
    `{(1, minus), (2, plus)}`, за припущеннями центрованості і регулярності.

    Виведення (`reports/pmm_fp_theoretical_framework.md`, § 3):

    1. `F_{11} = σ²`, `F_{12} = γ_3 σ³`, `F_{22} = σ⁴(2 + γ_4)`.
    2. `b = (-1, 0)` за умови `E[ξ] = 0`.
    3. `b^T F^{-1} b = (2+γ_4) / (σ² ((2+γ_4) − γ_3²))`.
    4. `g_S^FP = 1 / (σ² · b^T F^{-1} b) = 1 − γ_3² / (2 + γ_4) = g₂_classical`.

    **Гіпотези:**

    * `[IsProbabilityMeasure μ]` — щоб `∫ 1 dμ = 1`.
    * `hmean : Expect μ ξ = 0` — центрування (інакше `F₁₂ ≠ γ₃σ³`).
    * `hsigma2_pos : 0 < variance ξ μ` — невиродженість.
    * `hmeas : AEMeasurable ξ μ` — для зв'язку `variance ξ μ = ∫ ξ² dμ`.
    * `hg4_pos : 0 < 2 + gamma4 μ ξ` — невиродженість F (потрібно для бруку числа `(2+γ₄)`
      у знаменнику `g₂_classical`).
    * `hnondegen : (2 + gamma4 μ ξ) − (gamma3 μ ξ)^2 ≠ 0` — невиродженість F.

    Зв'язок із трекінг-таблицею: `reports/lean_theory_verification_pmm_fp.md`,
    рядок "G7". -/
theorem g₂_reduction_FP (μ : Measure α) (ξ : α → ℝ)
    [IsProbabilityMeasure μ]
    (hmean : Expect μ ξ = 0)
    (hsigma2_pos : 0 < variance ξ μ)
    (hmeas : AEMeasurable ξ μ)
    (hg4_pos : 0 < 2 + gamma4 μ ξ)
    (hnondegen : (2 + gamma4 μ ξ) - (gamma3 μ ξ)^2 ≠ 0) :
    g_S_FP μ ξ [(1, .minus), (2, .plus)] = g₂_classical μ ξ := by
  -- Скорочення (ASCII імена щоб уникнути проблем парсера Lean).
  set s2 : ℝ := variance ξ μ with hs2
  set g3 : ℝ := gamma3 μ ξ with hg3
  set g4 : ℝ := gamma4 μ ξ with hg4
  have hs2_ne : s2 ≠ 0 := ne_of_gt hsigma2_pos
  have hg4_ne : 2 + g4 ≠ 0 := ne_of_gt hg4_pos
  -- ## Крок 1: зв'язок необроблених моментів із центрованими.
  -- Під hmean: variance ξ μ = ∫ ξ² dμ.
  have hE2 : Expect μ (fun a => (ξ a)^2) = s2 := by
    simp [hs2, Expect, ProbabilityTheory.variance_of_integral_eq_zero hmeas hmean]
  -- E[ξ³] = γ₃ · σ²^(3/2).
  have hpow_pos : 0 < s2 ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hsigma2_pos _
  have hpow_ne : s2 ^ ((3:ℝ)/2) ≠ 0 := ne_of_gt hpow_pos
  have hE3 : Expect μ (fun a => (ξ a)^3) = g3 * s2 ^ ((3:ℝ)/2) := by
    have hgam3_def : g3 = Expect μ (fun a => (ξ a - Expect μ ξ)^3) / s2 ^ ((3:ℝ)/2) := by
      simp [hg3, gamma3, hs2]
    have hξ3_eq : ∀ a, (ξ a - Expect μ ξ)^3 = (ξ a)^3 := by
      intro a; rw [hmean, sub_zero]
    have hE3_centred : Expect μ (fun a => (ξ a - Expect μ ξ)^3) = Expect μ (fun a => (ξ a)^3) := by
      unfold Expect; congr 1; funext a; exact hξ3_eq a
    rw [hE3_centred] at hgam3_def
    field_simp at hgam3_def
    linarith [hgam3_def]
  -- E[ξ⁴] = (3 + γ₄) · σ⁴.
  have hsq_ne : s2^2 ≠ 0 := pow_ne_zero 2 hs2_ne
  have hE4 : Expect μ (fun a => (ξ a)^4) = (3 + g4) * s2^2 := by
    have hgam4_def : g4 = Expect μ (fun a => (ξ a - Expect μ ξ)^4) / s2^2 - 3 := by
      simp [hg4, gamma4, hs2]
    have hξ4_eq : ∀ a, (ξ a - Expect μ ξ)^4 = (ξ a)^4 := by
      intro a; rw [hmean, sub_zero]
    have hE4_centred : Expect μ (fun a => (ξ a - Expect μ ξ)^4) = Expect μ (fun a => (ξ a)^4) := by
      unfold Expect; congr 1; funext a; exact hξ4_eq a
    rw [hE4_centred] at hgam4_def
    field_simp at hgam4_def
    linarith
  -- ## Крок 2: значення `fpCorrelant` та `fpBVector` на 2-елементному базисі.
  -- Допоміжно: gpSigned 1 .minus (ξ a) = ξ a, gpSigned 2 .plus (ξ a) = (ξ a)^2.
  -- Helper: Real.sign x * |x| = x.
  have h_sign_abs : ∀ x : ℝ, Real.sign x * |x| = x := by
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [Real.sign_of_neg hx, abs_of_neg hx]; ring
    · rw [hx, Real.sign_zero, abs_zero, mul_zero]
    · rw [Real.sign_of_pos hx, abs_of_pos hx, one_mul]
  have hg1m : ∀ a, gpSigned 1 ParitySign.minus (ξ a) = ξ a := by
    intro a
    show (if (1:ℝ) = 0 then 0 else Real.sign (ξ a) * |ξ a|^(1:ℝ)) = ξ a
    rw [if_neg one_ne_zero, Real.rpow_one]
    exact h_sign_abs (ξ a)
  have hg2p : ∀ a, gpSigned 2 ParitySign.plus (ξ a) = (ξ a)^2 := by
    intro a
    show (if (2:ℝ) = 0 then Real.log (|ξ a|) else (|ξ a|)^(2:ℝ)) = (ξ a)^2
    rw [if_neg (by norm_num : (2:ℝ) ≠ 0), Real.rpow_two, sq_abs]
  -- F_{0,0} = fpCorrelant μ ξ 1 .minus 1 .minus = E[ξ²] - (E[ξ])² = s2.
  have hF00 : fpCorrelant μ ξ 1 ParitySign.minus 1 ParitySign.minus = s2 := by
    unfold fpCorrelant
    simp only [hg1m]
    have h1 : Expect μ (fun a => ξ a * ξ a) = Expect μ (fun a => (ξ a)^2) := by
      unfold Expect; congr 1; funext a; ring
    rw [h1, hE2, hmean]; ring
  -- F_{0,1} = fpCorrelant 1m 2p = E[ξ³] - 0 = γ₃·s2^(3/2).
  have hF01 : fpCorrelant μ ξ 1 ParitySign.minus 2 ParitySign.plus
            = g3 * s2 ^ ((3:ℝ)/2) := by
    unfold fpCorrelant
    simp only [hg1m, hg2p]
    have h1 : Expect μ (fun a => ξ a * (ξ a)^2) = Expect μ (fun a => (ξ a)^3) := by
      unfold Expect; congr 1; funext a; ring
    rw [h1, hE3, hmean]; ring
  -- F_{1,0} = F_{0,1}.
  have hF10 : fpCorrelant μ ξ 2 ParitySign.plus 1 ParitySign.minus
            = g3 * s2 ^ ((3:ℝ)/2) := by
    unfold fpCorrelant
    simp only [hg1m, hg2p]
    have h1 : Expect μ (fun a => (ξ a)^2 * ξ a) = Expect μ (fun a => (ξ a)^3) := by
      unfold Expect
      apply MeasureTheory.integral_congr_ae
      filter_upwards with a
      ring
    rw [h1, hE3, hmean]; ring
  -- F_{1,1} = E[ξ⁴] - (E[ξ²])² = (3+g4)s2² - s2² = (2+g4)·s2².
  have hF11 : fpCorrelant μ ξ 2 ParitySign.plus 2 ParitySign.plus
            = (2 + g4) * s2^2 := by
    unfold fpCorrelant
    simp only [hg2p]
    have h1 : Expect μ (fun a => (ξ a)^2 * (ξ a)^2) = Expect μ (fun a => (ξ a)^4) := by
      unfold Expect; congr 1; funext a; ring
    rw [h1, hE4, hE2]; ring
  -- b_0 = fpBVector μ ξ 1 .minus = -1 (під probability measure).
  have hb0 : fpBVector μ ξ 1 ParitySign.minus = -1 := by
    show (if (1:ℝ) = 0 then - Expect μ (fun a => 1 / |ξ a|)
          else - 1 * Expect μ (fun a => (|ξ a|) ^ ((1:ℝ) - 1))) = -1
    rw [if_neg one_ne_zero]
    have h_sub : (1:ℝ) - 1 = 0 := by norm_num
    rw [h_sub]
    have h_exp : Expect μ (fun a => (|ξ a|)^(0:ℝ)) = 1 := by
      simp [Expect, Real.rpow_zero, MeasureTheory.integral_const,
            measureReal_def, IsProbabilityMeasure.measure_univ]
    rw [h_exp]; ring
  -- b_1 = fpBVector μ ξ 2 .plus = -2·E[ξ] = 0 (під hmean).
  have hb1 : fpBVector μ ξ 2 ParitySign.plus = 0 := by
    show (if (2:ℝ) = 0 then - Expect μ (fun a => Real.sign (ξ a) / |ξ a|)
          else - 2 * Expect μ (fun a => Real.sign (ξ a) * (|ξ a|) ^ ((2:ℝ) - 1))) = 0
    rw [if_neg (by norm_num : (2:ℝ) ≠ 0)]
    have h_sub : (2:ℝ) - 1 = 1 := by norm_num
    rw [h_sub]
    have h_simp : ∀ a, Real.sign (ξ a) * (|ξ a|)^(1:ℝ) = ξ a := by
      intro a; rw [Real.rpow_one]; exact h_sign_abs _
    have h_exp : Expect μ (fun a => Real.sign (ξ a) * (|ξ a|) ^ (1:ℝ))
                = Expect μ (fun a => ξ a) := by
      unfold Expect
      congr 1
      funext a
      exact h_simp a
    rw [h_exp, hmean]; ring
  -- ## Крок 3: розпакування `g_S_FP` для конкретного 2-елементного базису.
  unfold g_S_FP
  -- Спрощуємо if (K = 0 ∨ s2 = 0) → false.
  have hK : ([(1, ParitySign.minus), (2, ParitySign.plus)] :
              List (ℝ × ParitySign)).length = 2 := by decide
  -- Конкретні скорочення для F-енергій.
  set a0 : ℝ := s2 with ha0
  set a1 : ℝ := g3 * s2 ^ ((3:ℝ)/2) with ha1
  set a2 : ℝ := (2 + g4) * s2^2 with ha2
  -- Детермінант ненульовий: a0·a2 − a1² = s2³ · ((2+g4) − g3²).
  have hpow_sq : s2 ^ ((3:ℝ)/2) * s2 ^ ((3:ℝ)/2) = s2^3 := by
    rw [← Real.rpow_add hsigma2_pos,
        show ((3:ℝ)/2 + 3/2) = 3 by norm_num,
        show ((3:ℝ)) = ((3:ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
  have ha0a2_a1sq : a0 * a2 - a1 * a1 = s2^3 * ((2 + g4) - g3^2) := by
    show s2 * ((2 + g4) * s2^2) - g3 * s2 ^ ((3:ℝ)/2) * (g3 * s2 ^ ((3:ℝ)/2)) = _
    have heq : g3 * s2 ^ ((3:ℝ)/2) * (g3 * s2 ^ ((3:ℝ)/2))
             = g3^2 * (s2 ^ ((3:ℝ)/2) * s2 ^ ((3:ℝ)/2)) := by ring
    rw [heq, hpow_sq]; ring
  have hs2_3 : s2^3 ≠ 0 := pow_ne_zero 3 hs2_ne
  have hdet_ne : a0 * a2 - a1 * a1 ≠ 0 := by
    rw [ha0a2_a1sq]; exact mul_ne_zero hs2_3 hnondegen
  -- Допоміжний крок: показати, що bFb на нашому списку
  -- дорівнює (a2 · 1 - 0 + 0) / (a0·a2 - a1²) = a2 / (a0·a2 - a1²).
  -- Реалізуємо це через еквівалентну форму матриці і вектора.
  -- Тут ключовий трюк: переписуємо `Matrix.of ... ⬝ᵥ b` як значення на явній 2x2.
  -- Через `Fin K = Fin 2` (бо hK), `Matrix.of ... = !![a0, a1; a1, a2]`.
  -- Розпаковуємо if-guards у g_S_FP.
  have h_if1 : ¬ (([(1, ParitySign.minus), (2, ParitySign.plus)] :
                  List (ℝ × ParitySign)).length = 0 ∨ variance ξ μ = 0) := by
    rw [hK]; push_neg
    exact ⟨by norm_num, hs2_ne⟩
  -- Розгортаємо `let` через `dsimp only`.
  dsimp only
  rw [if_neg h_if1]
  -- Тепер ціль: `if bFb = 0 then 0 else 1 / (variance ξ μ * bFb) = g₂_classical μ ξ`.
  -- Завдяки `decide`/`hK`, `Fin (basis.length)` зведена до `Fin 2`.
  -- Обчислимо bFb явно через еквівалентність матриці і вектора.
  -- Помічна форма: матриця F та вектор b мають "плоский" вигляд після `decide`-розв'язання.
  -- Через `convert` зведемо ціль до явної форми з матрицею !![a0, a1; a1, a2] та ![-1, 0],
  -- а потім застосуємо `quadForm_inv_fin_two`.
  -- Спочатку — застосовуємо `quadForm_inv_fin_two` з d=-1, e=0:
  have hquad := quadForm_inv_fin_two a0 a1 a2 (-1:ℝ) 0 hdet_ne
  have h_num : a2 * (-1) * (-1) - 2 * a1 * (-1) * 0 + a0 * 0 * 0 = a2 := by ring
  rw [h_num] at hquad
  -- `hquad : ((!![a0,a1;a1,a2])⁻¹.mulVec ![-1, 0]) ⬝ᵥ ![-1, 0] = a2 / (a0·a2 - a1²)`.
  -- Тепер головна редукція: показати,
  -- що bFb-вираз (Matrix.of ... ⬝ᵥ ...) дорівнює лівій частині hquad.
  -- Це робиться через еквівалентність F = !![a0,a1;a1,a2] і b = ![-1, 0] на Fin (length=2).
  -- Через еквівалентність `Fin (basis.length) ≃ Fin 2` (за hK) перекидаємо.
  -- Найпростіший шлях — конкретно довести рівність bFb = a2 / (a0·a2 - a1²):
  have h_eq_bFb :
      (((Matrix.of (fun (i j : Fin ([(1, ParitySign.minus), (2, ParitySign.plus)] :
                  List (ℝ × ParitySign)).length) =>
              fpCorrelant μ ξ
                (([(1, ParitySign.minus), (2, ParitySign.plus)] :
                    List (ℝ × ParitySign)).get i).1
                (([(1, ParitySign.minus), (2, ParitySign.plus)] :
                    List (ℝ × ParitySign)).get i).2
                (([(1, ParitySign.minus), (2, ParitySign.plus)] :
                    List (ℝ × ParitySign)).get j).1
                (([(1, ParitySign.minus), (2, ParitySign.plus)] :
                    List (ℝ × ParitySign)).get j).2))⁻¹.mulVec
            (fun i => fpBVector μ ξ
              (([(1, ParitySign.minus), (2, ParitySign.plus)] :
                  List (ℝ × ParitySign)).get i).1
              (([(1, ParitySign.minus), (2, ParitySign.plus)] :
                  List (ℝ × ParitySign)).get i).2)) ⬝ᵥ
        (fun i => fpBVector μ ξ
          (([(1, ParitySign.minus), (2, ParitySign.plus)] :
              List (ℝ × ParitySign)).get i).1
          (([(1, ParitySign.minus), (2, ParitySign.plus)] :
              List (ℝ × ParitySign)).get i).2))
      = a2 / (a0 * a2 - a1 * a1) := by
    -- Виокремлюємо рівність матриці F та вектора b у явних термінах Fin 2.
    -- Через `Fin K = Fin 2` дефініційно (бо K = 2 через `decide`).
    -- Підхід: явно довести рівності матриці і вектора, потім rewrite.
    have h_F_eq : (Matrix.of (fun (i j : Fin ([(1, ParitySign.minus), (2, ParitySign.plus)] :
          List (ℝ × ParitySign)).length) =>
        fpCorrelant μ ξ
          (([(1, ParitySign.minus), (2, ParitySign.plus)] :
              List (ℝ × ParitySign)).get i).1
          (([(1, ParitySign.minus), (2, ParitySign.plus)] :
              List (ℝ × ParitySign)).get i).2
          (([(1, ParitySign.minus), (2, ParitySign.plus)] :
              List (ℝ × ParitySign)).get j).1
          (([(1, ParitySign.minus), (2, ParitySign.plus)] :
              List (ℝ × ParitySign)).get j).2))
        = !![a0, a1; a1, a2] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.of_apply, hF00, hF01, hF10, hF11, ha0, ha1, ha2]
    have h_b_eq : (fun (i : Fin ([(1, ParitySign.minus), (2, ParitySign.plus)] :
          List (ℝ × ParitySign)).length) =>
        fpBVector μ ξ
          (([(1, ParitySign.minus), (2, ParitySign.plus)] :
              List (ℝ × ParitySign)).get i).1
          (([(1, ParitySign.minus), (2, ParitySign.plus)] :
              List (ℝ × ParitySign)).get i).2)
        = ![(-1:ℝ), 0] := by
      funext i
      fin_cases i <;> simp [List.get, hb0, hb1]
    rw [h_F_eq, h_b_eq]
    exact hquad
  -- Тепер маємо `h_eq_bFb`. Підставляємо у поточну ціль.
  rw [h_eq_bFb]
  -- Обчислюємо: a2 / (a0·a2 - a1²) = (2+g4) / (s2 · ((2+g4) - g3²)).
  have h_bFb_simp : a2 / (a0 * a2 - a1 * a1) = (2 + g4) / (s2 * ((2 + g4) - g3^2)) := by
    rw [ha0a2_a1sq, ha2]
    -- (2 + g4) * s2² / (s2³ * (2 + g4 - g3²)) = (2 + g4) / (s2 * (2 + g4 - g3²))
    -- Поділимо обидві сторони на s2² (≠ 0).
    have hs2sq_ne : (s2^2 : ℝ) ≠ 0 := hsq_ne
    rw [show (2 + g4) * s2^2 = s2^2 * (2 + g4) by ring]
    rw [show s2^3 * (2 + g4 - g3^2) = s2^2 * (s2 * (2 + g4 - g3^2)) by ring]
    exact mul_div_mul_left (2 + g4) (s2 * (2 + g4 - g3^2)) hs2sq_ne
  rw [h_bFb_simp]
  -- bFb ≠ 0: чисельник (2+g4) ≠ 0 завдяки hg4_pos.
  have h_bFb_ne : (2 + g4) / (s2 * ((2 + g4) - g3^2)) ≠ 0 := by
    apply div_ne_zero hg4_ne
    exact mul_ne_zero hs2_ne hnondegen
  rw [if_neg h_bFb_ne]
  -- Цільова рівність: 1 / (s2 · (2+g4)/(s2·((2+g4)-g3²))) = g₂_classical.
  -- = ((2+g4) - g3²) / (2+g4) = 1 - g3²/(2+g4).
  show 1 / (variance ξ μ * ((2 + g4) / (s2 * ((2 + g4) - g3^2)))) = g₂_classical μ ξ
  rw [show variance ξ μ = s2 from rfl]
  unfold g₂_classical
  rw [show gamma3 μ ξ = g3 from rfl, show gamma4 μ ξ = g4 from rfl]
  -- Тепер LHS: 1 / (s2 · (2+g4)/(s2·((2+g4)-g3²))) = ((2+g4)-g3²)/(2+g4) = 1 - g3²/(2+g4).
  -- Перепишемо `s2 * ((2+g4)/(s2·X)) = (2+g4)/X` через скорочення s2.
  have h_cancel : s2 * ((2 + g4) / (s2 * ((2 + g4) - g3^2))) = (2 + g4) / ((2 + g4) - g3^2) := by
    rw [mul_div_assoc']
    exact mul_div_mul_left (2 + g4) ((2 + g4) - g3^2) hs2_ne
  rw [h_cancel]
  -- Тепер: 1 / ((2+g4)/((2+g4) - g3²)) = ((2+g4) - g3²)/(2+g4) = 1 - g3²/(2+g4).
  rw [one_div_div]
  field_simp

/-! ## 8. Виключення `g_0^-` -/

/-- **Структурна лема:** елемент `(0, minus)` (тобто `g_0^-`) не входить
    до жодного з прийнятих базисів `basisA`, `basisB`, `basisB_weak`.

    Обґрунтування виключення — `reports/pmm_fp_theoretical_framework.md`, §5:
    похідна `(g_0^-)'(ξ) = 1 / |ξ|` має нескінченне математичне сподівання
    для будь-якого розподілу з `f_ξ(0) > 0`, тож включення `g_0^-` робило би
    `b^T F^{-1} b → ∞` штучно.

    Доведення: для кожного списку розкриваємо означення і показуємо,
    що `(0, minus)` не співпадає з жодним явно виписаним елементом
    (всі `minus`-елементи мають `p ≠ 0`). -/
theorem g0Minus_excluded :
    ((0 : ℝ), ParitySign.minus) ∉ basisA ∧
    ((0 : ℝ), ParitySign.minus) ∉ basisB ∧
    ((0 : ℝ), ParitySign.minus) ∉ basisB_weak := by
  -- Розкриваємо кожен список явно, відкидаємо кожну альтернативу через
  -- (а) суперечність на парності `.plus = .minus` (`ParitySign.noConfusion`),
  -- або (б) арифметичну суперечність на степені `nonzero = 0` (`norm_num`).
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp only [basisA, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at h
    rcases h with
      ⟨_, k⟩ | ⟨_, k⟩ | ⟨p, _⟩ |
      ⟨_, k⟩ | ⟨p, _⟩ | ⟨_, k⟩ | ⟨p, _⟩ |
      ⟨_, k⟩ | ⟨p, _⟩
    all_goals first | exact ParitySign.noConfusion k | norm_num at p
  · intro h
    simp only [basisB, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at h
    rcases h with
      ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ |
      ⟨_, k⟩ |
      ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ |
      ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩
    all_goals first | exact ParitySign.noConfusion k | norm_num at p
  · intro h
    simp only [basisB_weak, List.mem_cons, List.not_mem_nil, or_false,
               Prod.mk.injEq] at h
    rcases h with
      ⟨p, _⟩ | ⟨p, _⟩ |
      ⟨_, k⟩ |
      ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ |
      ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ | ⟨p, _⟩
    all_goals first | exact ParitySign.noConfusion k | norm_num at p

/-- **Аналітична лема:** очікування похідної `g_0^-` розбіжне для розподілів
    з обмеженою знизу щільністю біля нуля.

    Це формальне обґрунтування виключення `g_0^-` з базису.

    **Гіпотеза `hξ` (умова локальної невиродженості):** існує `δ > 0` і
    `c > 0` такі, що для будь-якого вимірного підмножини `B ⊆ (-δ, δ)`
    з ненульовою лебеговою мірою `λ(B)`, pushforward-міра `ξ_* μ` має
    `(ξ_* μ)(B) ≥ ENNReal.ofReal (c · λ(B))`. Тобто щільність `ξ` (відносно
    Лебега) обмежена знизу `c` на околі нуля.

    **Гіпотеза `hmeas`:** `ξ` AEMeasurable (потрібно для `integrable_map_measure`).

    **Гіпотеза `hdiv`:** функція `1/|z|` не інтегровна за pushforward-мірою
    `μ.map ξ`. **Це і є ключове твердження:** інтуїтивно випливає з
    `μ.map ξ ≥ c·λ|_(-δ,δ)` і log-розбіжності `∫_0^δ 1/z dz = ∞`, але
    формально доводиться через детальну роботу з `lintegral` та
    розкладом міри Лебега навколо `0`. У цій реалізації приймаємо `hdiv`
    як explicit hypothesis (Phase 2 deliverable: довести `hdiv` з `_hξ`).

    **Висновок:** функція `1 / |ξ(·)|` не інтегровна за `μ`. Доведення:
    через `integrable_map_measure`, інтегровність `1/|ξ|` за `μ`
    еквівалентна інтегровності `1/|z|` за `μ.map ξ`. Остання виключається
    через `hdiv`. -/
theorem g0Minus_divergent
    (μ : Measure α) (ξ : α → ℝ)
    (hmeas : AEMeasurable ξ μ)
    (_hξ : ∃ δ > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ B : Set ℝ, MeasurableSet B → B ⊆ Set.Ioo (-δ) δ →
        μ.map ξ B ≥ ENNReal.ofReal (c * (MeasureTheory.volume B).toReal))
    (hdiv : ¬ Integrable (fun z : ℝ => 1 / |z|) (μ.map ξ)) :
    ¬ Integrable (fun a => 1 / |ξ a|) μ := by
  -- Через `integrable_map_measure`, `Integrable (fun a => 1/|ξ a|) μ` еквівалентно
  -- `Integrable (fun z => 1/|z|) (μ.map ξ)`.
  -- AEStronglyMeasurable випливає з вимірності `1/|·|` як композиції стандартних.
  intro h_int
  -- Композиція: `(fun z => 1/|z|) ∘ ξ = fun a => 1/|ξ a|`.
  have h_eq : (fun z : ℝ => 1 / |z|) ∘ ξ = fun a => 1 / |ξ a| := rfl
  -- AEStronglyMeasurable для `fun z => 1/|z|` під μ.map ξ:
  have h_aestrong : AEStronglyMeasurable (fun z : ℝ => 1 / |z|) (μ.map ξ) := by
    have : Measurable (fun z : ℝ => 1 / |z|) := by fun_prop
    exact this.aestronglyMeasurable
  -- Застосовуємо integrable_map_measure:
  have h_map_int : Integrable (fun z : ℝ => 1 / |z|) (μ.map ξ) := by
    rw [integrable_map_measure h_aestrong hmeas]
    convert h_int
  exact hdiv h_map_int

/-! ## 9. Регулярність моментів -/

/-- Існування скінченних дробових моментів невід'ємних порядків (трек a).

    Передаточна структура, що **прив'язана до регресорного** `fpBasis`
    (зворотна сумісність з `Consistency.lean`, `BoundedDensity.lean`).
    Концептуально правильна версія для score-базису має використовувати
    `gpSigned` і signed-parity індекси — це Phase 1c. -/
def FiniteFractionalMomentsPos (μ : Measure α) (ξ : α → ℝ) : Prop :=
  ∀ p ∈ P_a, Integrable (fun a => fpBasis p (ξ a)) μ ∧
              Integrable (fun a => (fpBasis p (ξ a))^2) μ

/-- Версія `FiniteFractionalMomentsPos` для score-базису з signed-parity.
    Phase 1c clean variant — інтегровність кожного елемента `basisA`. -/
def FiniteFractionalMomentsPosScore (μ : Measure α) (ξ : α → ℝ) : Prop :=
  ∀ pk ∈ basisA, Integrable (fun a => gpSigned pk.1 pk.2 (ξ a)) μ ∧
                  Integrable (fun a => (gpSigned pk.1 pk.2 (ξ a))^2) μ

end PMM_FP
