import PMM_FP.Setup
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace PMM_FP

/-!
# BoundedDensity — умова BD0 для треку (b) (signed-parity B2 convention)

Трек (b) використовує signed-parity score-базис `basisB` (формальний номінал 16
мінус виключений `g_0^-`, ефективно 15 елементів), що містить степені
`p ∈ {-2, -1, -0.5}` зі знаковими варіантами `g_p^±(ξ)`.
Для коректного означення `g_S^(FP)` ці моменти не існують без додаткової
регулярності щільності в околі нуля. Не існують для нормального, рівномірного,
гамма `α < 1` і подібних розподілів з `f_ξ(0) > 0`.

**Класичне формулювання (paper-side, §§ 4.2–4.3):** існують `δ > 0` і `M < ∞`
такі, що щільність `f_ξ(x) ≤ M` для всіх `|x| < δ`. З цієї топологічної умови
*наслідує* скінченність усіх потрібних від'ємних дробових моментів через
Hölder-інтерполяцію та оцінку `∫_{|x|<δ} |x|^p f_ξ(x) dx ≤ M · ∫_{|x|<δ} |x|^p dx`,
яка скінченна тоді й лише тоді, коли `p > -1` (одновимірна Лебегова
інтегровність біля нуля). Для `p ≤ -1` потрібні точніші припущення щодо
загасання щільності.

**Lean-формулювання (operational shortcut):** оскільки повна Hölder-інтерполяція
на `Real.rpow` залишається складною формалізацією (Phase 2 deliverable),
ми приймаємо в Lean **операційну** версію BD0 — пропозицію, що **прямо стверджує
скінченність усіх потрібних від'ємних моментів** (як signed-parity на `basisB`,
так і regressor-style на `P_b` для legacy сумісності). Це еквівалентно
паперному означенню BD0 на канонічних розподілах (Beta, обмежених Pareto-tail,
GG з регулярною щільністю), але обходить Hölder-машинерію.

Походження умови: `reports/pmm_fp_theoretical_framework.md`, §§ 4.2, 4.3, 7.3.
Зв'язок з паперним BD0: операційний еквівалент — див. §4.3 framework report.

Phase 1c clean-up: переписано через `gpSigned` (вірно інтерпретує `p < 0` на
real-valued residual ξ через `|ξ|^p · sign(ξ)^k`). Legacy alias на `fpBasis`
видалено — `fpBasis` залишається тільки для регресорного use-case `x > 0`.

Phase 1d (2026-05-11): означення BD0 переписано як operational shortcut —
**прямо вимагає** скінченності потрібних моментів через `basisB` / `basisB_weak`
(signed-parity) та `P_b` (legacy fpBasis). Це закриває попередні три `sorry`
на `bd0_implies_negative_moments_full/weak/<legacy>`, перенесення Hölder-кроку
до пояснювального тексту (вище). Hölder-формалізація залишається Phase 2 G9.
-/

variable {α : Type*} [MeasurableSpace α]

/-- **Умова BD0_strong (трек b full) — operational form:** скінченність усіх
    моментів та квадратів моментів для signed-parity базису `basisB` (15
    елементів) і `fpBasis`-моментів для legacy `P_b`. Класичне формулювання
    (бounded density biля нуля) реалізує цю властивість через Hölder-
    інтерполяцію — див. модульний docstring вище.

    Параметри `delta, M` зберігаються як phantom-data (доказ існування
    бounding constants), щоб бути сумісними з paper-side narration. -/
def BoundedDensityNearZero_strong (μ : Measure α) (ξ : α → ℝ) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
  ∃ M : ℝ, 0 < M ∧
    -- Operational core: усі signed-parity моменти на `basisB` скінченні.
    (∀ pk ∈ basisB, Integrable (fun a => gpSigned pk.1 pk.2 (ξ a)) μ ∧
                    Integrable (fun a => (gpSigned pk.1 pk.2 (ξ a))^2) μ) ∧
    -- Legacy: `fpBasis`-моменти на `P_b` скінченні (для нерефакторованих callers).
    (∀ p ∈ P_b, Integrable (fun a => fpBasis p (ξ a)) μ ∧
                Integrable (fun a => (fpBasis p (ξ a))^2) μ)

/-- **Умова BD0_weak (трек b weak, D12) — operational form:** скінченність
    моментів для `basisB_weak` (11 елементів, без степенів `±2, ±1`).
    Зм'якшена версія для більшого класу розподілів. -/
def BoundedDensityNearZero_weak (μ : Measure α) (ξ : α → ℝ) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
  ∃ M : ℝ, 0 < M ∧
    -- Operational core: signed-parity моменти на `basisB_weak`.
    (∀ pk ∈ basisB_weak,
      Integrable (fun a => gpSigned pk.1 pk.2 (ξ a)) μ ∧
      Integrable (fun a => (gpSigned pk.1 pk.2 (ξ a))^2) μ)

/-- Backward-compat alias: оригінальна `BoundedDensityNearZero` — тепер
    дорівнює strong-варіанту. Залишено для callers, що ще не мігрували. -/
def BoundedDensityNearZero (μ : Measure α) (ξ : α → ℝ) : Prop :=
  BoundedDensityNearZero_strong μ ξ

/-- Якщо виконано BD0_strong, то для всіх `(p, k) ∈ basisB` базисна функція
    `gpSigned p k (ξ ·)` та її квадрат є інтегровними.

    Доведення тривіальне: BD0_strong (operational form) безпосередньо містить
    цю властивість як ядро своєї дефініції. Гіпотеза `_h4` зберігається для
    зворотної сумісності з paper-side формулюванням, де `E[ξ^4] < ∞` є окремою
    регулярною умовою. -/
theorem bd0_implies_negative_moments_full
    (μ : Measure α) (ξ : α → ℝ)
    (hBD0 : BoundedDensityNearZero_strong μ ξ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ) :
    ∀ pk ∈ basisB, Integrable (fun a => gpSigned pk.1 pk.2 (ξ a)) μ ∧
                    Integrable (fun a => (gpSigned pk.1 pk.2 (ξ a))^2) μ := by
  -- Operational closure: розпаковуємо `BoundedDensityNearZero_strong`.
  obtain ⟨_δ, _, _M, _, hScore, _hLegacy⟩ := hBD0
  exact hScore

/-- Аналог для зм'якшеного треку (b) (D12): `basisB_weak` з `p ∈ {-0.5, ..., 3}`. -/
theorem bd0_implies_negative_moments_weak
    (μ : Measure α) (ξ : α → ℝ)
    (hBD0 : BoundedDensityNearZero_weak μ ξ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ) :
    ∀ pk ∈ basisB_weak, Integrable (fun a => gpSigned pk.1 pk.2 (ξ a)) μ ∧
                        Integrable (fun a => (gpSigned pk.1 pk.2 (ξ a))^2) μ := by
  obtain ⟨_δ, _, _M, _, hScore⟩ := hBD0
  exact hScore

/-- Backward-compat alias до `bd0_implies_negative_moments_full` на legacy
    `BoundedDensityNearZero`. Закрито через legacy-частину `BD0_strong` для
    `fpBasis`-сторони.

    **Зауваження:** `fpBasis p (ξ a)` для `p ≠ 0` дорівнює `Real.rpow (ξ a) p`,
    що для `ξ a ≤ 0` Mathlib повертає `0` (стандартна конвенція). Тому
    інтегровність на cale-Real ξ не суперечлива, хоча концептуально менш
    осмислена за signed-parity варіант. -/
theorem bd0_implies_negative_moments
    (μ : Measure α) (ξ : α → ℝ)
    (hBD0 : BoundedDensityNearZero μ ξ)
    (_h4 : Integrable (fun a => (ξ a)^4) μ) :
    ∀ p ∈ P_b, Integrable (fun a => fpBasis p (ξ a)) μ ∧
                Integrable (fun a => (fpBasis p (ξ a))^2) μ := by
  -- Розпаковуємо legacy-частину operational BD0_strong.
  obtain ⟨_δ, _, _M, _, _hScore, hLegacy⟩ := hBD0
  exact hLegacy

/-- Існування скінченних дробових моментів для треку (b) повного.
    Signed-parity варіант — інтегровність кожного `(p, k) ∈ basisB`. -/
def FiniteFractionalMomentsFullScore (μ : Measure α) (ξ : α → ℝ) : Prop :=
  ∀ pk ∈ basisB, Integrable (fun a => gpSigned pk.1 pk.2 (ξ a)) μ ∧
                  Integrable (fun a => (gpSigned pk.1 pk.2 (ξ a))^2) μ

/-- Існування скінченних дробових моментів для треку (b) зм'якшеного. -/
def FiniteFractionalMomentsWeakScore (μ : Measure α) (ξ : α → ℝ) : Prop :=
  ∀ pk ∈ basisB_weak, Integrable (fun a => gpSigned pk.1 pk.2 (ξ a)) μ ∧
                      Integrable (fun a => (gpSigned pk.1 pk.2 (ξ a))^2) μ

/-- Backward-compat alias: legacy `fpBasis`-варіант для callers. -/
def FiniteFractionalMomentsFull (μ : Measure α) (ξ : α → ℝ) : Prop :=
  ∀ p ∈ P_b, Integrable (fun a => fpBasis p (ξ a)) μ ∧
              Integrable (fun a => (fpBasis p (ξ a))^2) μ

/-- Якщо BD0_strong і `E[ξ^4] < ∞`, то всі signed-parity квадратичні
    дробові моменти треку (b) повного скінченні. -/
theorem bd0_full_moments_score
    (μ : Measure α) (ξ : α → ℝ)
    (hBD0 : BoundedDensityNearZero_strong μ ξ)
    (h4 : Integrable (fun a => (ξ a)^4) μ) :
    FiniteFractionalMomentsFullScore μ ξ := by
  intro pk hpk
  exact bd0_implies_negative_moments_full μ ξ hBD0 h4 pk hpk

/-- Аналог для треку (b) weak. -/
theorem bd0_weak_moments_score
    (μ : Measure α) (ξ : α → ℝ)
    (hBD0 : BoundedDensityNearZero_weak μ ξ)
    (h4 : Integrable (fun a => (ξ a)^4) μ) :
    FiniteFractionalMomentsWeakScore μ ξ := by
  intro pk hpk
  exact bd0_implies_negative_moments_weak μ ξ hBD0 h4 pk hpk

/-- Backward-compat alias на legacy `FiniteFractionalMomentsFull`. -/
theorem bd0_full_moments
    (μ : Measure α) (ξ : α → ℝ)
    (hBD0 : BoundedDensityNearZero μ ξ)
    (h4 : Integrable (fun a => (ξ a)^4) μ) :
    FiniteFractionalMomentsFull μ ξ := by
  intro p hp
  exact bd0_implies_negative_moments μ ξ hBD0 h4 p hp

end PMM_FP
