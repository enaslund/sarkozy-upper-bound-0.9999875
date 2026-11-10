module

public import Sarkozy.MiddleRecords.RectStar

/-!
# Orthogonal channels of the matching law (`lem:record:e-orthogonal`(a), (b))

`paper/sections/21_middle_records.tex`, `subsec:record:e_side`, `lem:record:e-orthogonal`. The
empty half law `ν_E` is uniform on the triples of distinct labels (`nuE`, the average `E_{ν_E}`).
The pair-star map `(𝒯_E g)(x) = E_t χ(t - x₁) χ(t - x₀) g(t)` (`TE`) depends on `(x₀, x₁)` only.

* **(a)** `‖𝒯_E g‖²_{ν_E} ≤ q(1 - 2q)/(1 - q) ‖g‖²` on mean-zero `g` (`TE_norm_le`), and
  `q(1 - 2q)/(1 - q) ≤ q` (`TE_const_le`); for independent labels the Gram is exactly `q(1 - 2q)`
  (`Sarkozy.MiddleRecords.pairStar_gram_meanZero`). The density of the pair `(x₀, x₁)` of `ν_E`
  relative to two independent labels is `1/(1 - q)`.
* **(b)**, the three identities: with the kernel `𝖢𝖣 = χ(y₀ - x₁) χ(y₁ - x₀)` acting on
  `L²(ν_E)` by `(K f)(x) = E_{y ∼ ν_E} K(x, y) f(y)`,
  `𝖢𝖣 V₀ = 𝖢𝖣 V₁ = -u 𝒯_E` with `u = 1/(p - 1)` (`CD_V0`, `CD_V1`, for every `g`), and
  `𝖢𝖣 V₂ = 2𝒯_E/((p - 1)(p - 2))` on mean-zero `g` (`CD_V2`), at every half `x` (three distinct
  labels).

**Not formalized:** the bound `‖𝖢𝖣 H‖ ≤ e_E` of (b) and part (c).
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-- The average over the empty half law `ν_E` (uniform on distinct triples). -/
noncomputable def nuE (G : F → F → F → ℝ) : ℝ :=
  (qF * (qF - 1) * (qF - 2))⁻¹ *
    ∑ a, ∑ b, ∑ c, if a ≠ b ∧ a ≠ c ∧ b ≠ c then G a b c else 0

/-- **The pair-star map** `(𝒯_E g)(x₀, x₁) = E_t χ(t - x₁) χ(t - x₀) g(t)`. -/
noncomputable def TE (g : F → ℝ) (x₀ x₁ : F) : ℝ :=
  qF⁻¹ * ∑ t, (χ (t - x₁) : ℝ) * (χ (t - x₀) : ℝ) * g t

theorem TE_eq_rectOp (h3 : Fintype.card F % 4 = 3) (g : F → ℝ) (x₀ x₁ : F) :
    TE g x₀ x₁ = rectOp 0 0 1 g x₁ x₀ := by
  unfold TE rectOp
  congr 1
  refine sum_congr rfl fun t _ => ?_
  rw [rectStar_pairStar h3]

omit [Field F] in
/-- Summing out the third label: for `a ≠ b`, `#{c ∉ {a, b}} = p - 2`. -/
theorem sum_third (a b : F) (hab : a ≠ b) :
    ∑ c : F, (if a ≠ c ∧ b ≠ c then (1 : ℝ) else 0) = qF - 2 := by
  have e : ∀ c : F, (if a ≠ c ∧ b ≠ c then (1 : ℝ) else 0) =
      1 - (if c = a then 1 else 0) - (if c = b then 1 else 0) := by
    intro c
    by_cases ha : c = a
    · subst ha; simp [hab]
    · by_cases hb : c = b
      · subst hb; simp [ha, Ne.symm ha]
      · simp [ha, hb, Ne.symm ha, Ne.symm hb]
  simp only [e, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, sum_ite_eq',
    mem_univ, ↓reduceIte]
  ring

omit [Field F] in
/-- `E_{ν_E}` of a function of the first two labels. -/
theorem nuE_pair (G : F → F → ℝ) (hp : 3 ≤ qF) :
    nuE (fun a b _ => G a b) = (qF * (qF - 1))⁻¹ *
      ∑ a, ∑ b, if a ≠ b then G a b else 0 := by
  unfold nuE
  have e : ∀ a b : F, ∑ c : F, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then G a b else 0) =
      (if a ≠ b then G a b else 0) * (qF - 2) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [ite_eq_left hab, ← sum_third a b hab, mul_sum]
      refine sum_congr rfl fun c _ => ?_
      by_cases hc : a ≠ c ∧ b ≠ c
      · rw [ite_eq_left (show a ≠ b ∧ a ≠ c ∧ b ≠ c from ⟨hab, hc⟩), ite_eq_left hc, mul_one]
      · rw [ite_eq_right (fun h => hc ⟨h.2.1, h.2.2⟩), ite_eq_right hc, mul_zero]
  simp only [e, ← sum_mul]
  have h2 : qF - 2 ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp

/-! ## (a) -/

/-- **`lem:record:e-orthogonal`(a)**: `‖𝒯_E g‖²_{ν_E} ≤ q(1 - 2q)/(1 - q) ‖g‖²` on mean-zero `g`,
`q = 1/p`. -/
theorem TE_norm_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hp : 3 ≤ qF)
    (g : F → ℝ) (hg : ∑ t, g t = 0) :
    nuE (fun a b _ => TE g a b ^ 2) ≤
      qF⁻¹ * (1 - 2 * qF⁻¹) / (1 - qF⁻¹) * unifNormSq g := by
  rw [nuE_pair _ hp]
  have h0 : 0 < qF := by linarith
  have h1 : 0 < qF - 1 := by linarith
  -- drop the restriction `a ≠ b`
  have hdrop : ∑ a, ∑ b, (if a ≠ b then TE g a b ^ 2 else 0) ≤ ∑ a, ∑ b, TE g a b ^ 2 := by
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
    split_ifs
    · exact le_refl _
    · exact sq_nonneg _
  -- the full sum is the rectangular-star Gram `(0, 0, 1)`
  have hfull : ∑ a, ∑ b, TE g a b ^ 2 = qF ^ 2 * rectNormSq 0 0 1 g := by
    unfold rectNormSq
    rw [show qF ^ 2 * (qF⁻¹ ^ 2 * ∑ u, ∑ v, rectOp 0 0 1 g u v ^ 2) =
      ∑ u, ∑ v, rectOp 0 0 1 g u v ^ 2 by field_simp]
    rw [sum_comm]
    exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by rw [TE_eq_rectOp h3]
  rw [rect_gram_meanZero hF 0 0 1 g hg] at hfull
  have hu : 0 ≤ unifNormSq g := by
    unfold unifNormSq; positivity
  calc (qF * (qF - 1))⁻¹ * ∑ a, ∑ b, (if a ≠ b then TE g a b ^ 2 else 0)
      ≤ (qF * (qF - 1))⁻¹ * ∑ a, ∑ b, TE g a b ^ 2 :=
        mul_le_mul_of_nonneg_left hdrop (by positivity)
    _ = qF⁻¹ * (1 - 2 * qF⁻¹) / (1 - qF⁻¹) * unifNormSq g := by
        rw [hfull]
        have hq1 : 1 - qF⁻¹ ≠ 0 := by
          have : qF⁻¹ ≤ 1 / 3 := by
            rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
          intro h; linarith
        field_simp
        ring

/-- `q(1 - 2q)/(1 - q) ≤ q` for `0 ≤ q < 1`, so `‖𝒯_E‖ ≤ r` on mean-zero functions. -/
theorem TE_const_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : q * (1 - 2 * q) / (1 - q) ≤ q := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-! ## (b) -/

/-- **`lem:record:e-orthogonal`(b): `𝖢𝖣 V₀ = -u 𝒯_E`**, `u = 1/(p - 1)`: for every half `x`
(`x₀ ≠ x₁`) and every `g`, `E_{y ∼ ν_E}[χ(y₀ - x₁) χ(y₁ - x₀) g(y₀)] = -(𝒯_E g)(x)/(p - 1)`. -/
theorem CD_V0 (hF : ringChar F ≠ 2) (hp : 3 ≤ qF) (g : F → ℝ) (x₀ x₁ : F) :
    nuE (fun a b _ => (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g a) = -(TE g x₀ x₁ / (qF - 1)) := by
  rw [nuE_pair _ hp]
  have e : ∀ a, ∑ b, (if a ≠ b then (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g a else 0) =
      -((χ (a - x₁) : ℝ) * (χ (a - x₀) : ℝ) * g a) := by
    intro a
    have : ∀ b, (if a ≠ b then (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g a else 0) =
        (χ (a - x₁) : ℝ) * g a * (χ (b - x₀) : ℝ) -
          (if b = a then (χ (a - x₁) : ℝ) * g a * (χ (b - x₀) : ℝ) else 0) := by
      intro b
      by_cases hb : b = a
      · subst hb; simp
      · rw [ite_eq_left (Ne.symm hb), ite_eq_right hb]; ring
    simp only [this, sum_sub_distrib, ← mul_sum, sumR_chi_shift hF x₀, sum_ite_eq', mem_univ,
      ↓reduceIte]
    ring
  simp only [e, sum_neg_distrib]
  unfold TE
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp

/-- **`lem:record:e-orthogonal`(b): `𝖢𝖣 V₁ = -u 𝒯_E`**:
`E_{y ∼ ν_E}[χ(y₀ - x₁) χ(y₁ - x₀) g(y₁)] = -(𝒯_E g)(x)/(p - 1)`. -/
theorem CD_V1 (hF : ringChar F ≠ 2) (hp : 3 ≤ qF) (g : F → ℝ) (x₀ x₁ : F) :
    nuE (fun a b _ => (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g b) = -(TE g x₀ x₁ / (qF - 1)) := by
  rw [nuE_pair _ hp, sum_comm]
  have e : ∀ b, ∑ a, (if a ≠ b then (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g b else 0) =
      -((χ (b - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g b) := by
    intro b
    have : ∀ a, (if a ≠ b then (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g b else 0) =
        (χ (b - x₀) : ℝ) * g b * (χ (a - x₁) : ℝ) -
          (if a = b then (χ (b - x₀) : ℝ) * g b * (χ (a - x₁) : ℝ) else 0) := by
      intro a
      by_cases ha : a = b
      · subst ha; simp
      · rw [ite_eq_left ha, ite_eq_right ha]; ring
    simp only [this, sum_sub_distrib, ← mul_sum, sumR_chi_shift hF x₁, sum_ite_eq', mem_univ,
      ↓reduceIte]
    ring
  simp only [e, sum_neg_distrib]
  unfold TE
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp

/-- The inner sum of `𝖢𝖣 V₂`: for `x₀ ≠ x₁`,
`∑_{y₀ ≠ y₁, both ≠ t} χ(y₀ - x₁) χ(y₁ - x₀) = 1 + 2 χ(t - x₁) χ(t - x₀)`. -/
theorem sum_CD_avoid (hF : ringChar F ≠ 2) {x₀ x₁ : F}
    (hx : x₀ ≠ x₁) (t : F) :
    ∑ a, ∑ b, (if a ≠ b ∧ a ≠ t ∧ b ≠ t then (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) else 0) =
      1 + 2 * ((χ (t - x₁) : ℝ) * (χ (t - x₀) : ℝ)) := by
  -- inner sum over `b` for fixed `a`
  have e : ∀ a, ∑ b, (if a ≠ b ∧ a ≠ t ∧ b ≠ t then (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) else 0) =
      if a = t then 0 else
        -((χ (a - x₁) : ℝ) * (χ (t - x₀) : ℝ)) - (χ (a - x₁) : ℝ) * (χ (a - x₀) : ℝ) := by
    intro a
    by_cases hat : a = t
    · subst hat
      rw [ite_eq_left rfl]
      exact sum_eq_zero fun b _ => by rw [ite_eq_right (fun h => h.2.1 rfl)]
    · rw [ite_eq_right hat]
      have : ∀ b, (if a ≠ b ∧ a ≠ t ∧ b ≠ t then (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) else 0) =
          (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) -
            (if b = a then (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) else 0) -
            (if b = t then (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) else 0) := by
        intro b
        by_cases hba : b = a
        · subst hba; simp [hat]
        · by_cases hbt : b = t
          · subst hbt; simp [hba]
          · rw [ite_eq_left (show a ≠ b ∧ a ≠ t ∧ b ≠ t from ⟨Ne.symm hba, hat, hbt⟩),
              ite_eq_right hba, ite_eq_right hbt]
            ring
      simp only [this, sum_sub_distrib, ← mul_sum, sumR_chi_shift hF x₀, sum_ite_eq', mem_univ,
        ↓reduceIte]
      ring
  simp only [e]
  have hite : ∀ G : F → ℝ, ∑ a, (if a = t then 0 else G a) = ∑ a, G a - G t := by
    intro G
    have : ∀ a, (if a = t then 0 else G a) = G a - (if a = t then G a else 0) := by
      intro a; split_ifs <;> simp
    simp only [this, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [hite]
  have h1 : ∑ a, -((χ (a - x₁) : ℝ) * (χ (t - x₀) : ℝ)) = 0 := by
    rw [sum_neg_distrib, ← sum_mul, sumR_chi_shift hF x₁, zero_mul, neg_zero]
  have h2 : ∑ a, (χ (a - x₁) : ℝ) * (χ (a - x₀) : ℝ) = -1 := by
    rw [sumR_chi_chi hF x₁ x₀, ite_eq_right (Ne.symm hx)]
    ring
  rw [sum_sub_distrib, h1, h2]
  ring

/-- **`lem:record:e-orthogonal`(b): `𝖢𝖣 V₂ = 2𝒯_E/((p - 1)(p - 2))` on mean-zero `g`**: for every
half `x` (`x₀ ≠ x₁`), `E_{y ∼ ν_E}[χ(y₀ - x₁) χ(y₁ - x₀) g(y₂)] = 2(𝒯_E g)(x)/((p - 1)(p - 2))`. -/
theorem CD_V2 (hF : ringChar F ≠ 2) (hp : 3 ≤ qF) (g : F → ℝ)
    (hg : ∑ t, g t = 0) {x₀ x₁ : F} (hx : x₀ ≠ x₁) :
    nuE (fun a b c => (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g c) =
      2 * TE g x₀ x₁ / ((qF - 1) * (qF - 2)) := by
  unfold nuE
  -- move the sum over `c` outside
  have hswap : ∑ a, ∑ b, ∑ c, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then
      (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g c else 0) =
      ∑ c, g c * ∑ a, ∑ b, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then
        (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) else 0) := by
    calc ∑ a, ∑ b, ∑ c, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then
          (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g c else 0)
        = ∑ a, ∑ c, ∑ b, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then
          (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g c else 0) :=
          sum_congr rfl fun a _ => sum_comm
      _ = ∑ c, ∑ a, ∑ b, (if a ≠ b ∧ a ≠ c ∧ b ≠ c then
          (χ (a - x₁) : ℝ) * (χ (b - x₀) : ℝ) * g c else 0) := sum_comm
      _ = _ := by
          refine sum_congr rfl fun c _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun a _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun b _ => ?_
          split_ifs <;> ring
  rw [hswap]
  simp only [sum_CD_avoid hF hx]
  have e : ∀ c, g c * (1 + 2 * ((χ (c - x₁) : ℝ) * (χ (c - x₀) : ℝ))) =
      g c + 2 * ((χ (c - x₁) : ℝ) * (χ (c - x₀) : ℝ) * g c) := by
    intro c; ring
  simp only [e, sum_add_distrib, ← mul_sum, hg, zero_add]
  unfold TE
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h2 : qF - 2 ≠ 0 := by intro h; linarith
  field_simp

end Sarkozy.MiddleRecords
