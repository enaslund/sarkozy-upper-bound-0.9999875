module

public import Sarkozy.NormBoundsPaper2.PrimeLaws
public import Sarkozy.NormBoundsPaper2.Sectors
public import Sarkozy.JointRows.PaleyGauss
public import Sarkozy.MiddleRecords.MergePrices

@[expose] public section

/-!
# The prime bounds of the first-coordinate merge (NB2)

`paper/sections/21_middle_records.tex`, proof of `lem:merge-repair`, paragraph "The source and the
first-coordinate law":

* **`src_form_le`**: `‖D_p − J‖ = d_p` in form version, `|⟨u, D_p v⟩| ≤ d_p ‖u‖ ‖v‖` for mean-zero
  `u, v ∈ L²(m_p)`, `d_p = 2/(p − 2)` (`PairAlgebra.T_bilin`); **`src_centred`**: the centred norm
  of the source is `≤ d_p`;
* "The normalized strict Paley operator `P` has symmetric part `J − η^G_p (I − J)` … and centered
  norm `ρ_p`. Since `P^s_p = V₀ P V₀^*`":
  - `first_form`: `⟨u, P^s v⟩ = p⁻¹ ∑_{a,c} k_P(c − a) ū(a) v̄(c)`, `ū = V₀^* u`;
  - **`paley_norm`**: `∑_a (∑_c k_P(c − a) h(c))² = ρ_p² ∑ h²` for `∑ h = 0` (`p ≡ 3 (4)`), from
    JointRows' `Φ̂* = −Φ̂`, `Φ̂² = −(I − J)`;
  - **`first_centred`**: the centred norm of `P^s` is `≤ ρ_p`;
  - **`first_sym_le`**: `|Sym⟨u, P^s v⟩| ≤ η^G_p ‖u‖ ‖v‖` on mean-zero functions (the symmetric
    part of `k_P` is `k_D`, eigenvalue `−η^G_p`);
* **`first_single`**: the prime symmetric difference, `|Sym⟨u, (P^s − D_p) v⟩| ≤ (d_p + η^G_p)
  ‖u‖ ‖v‖`.

Here `‖u‖² = ∑_x m_p(x) u(x)²` with `m_p = mP p`, the actual half law.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper2

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.SignedGram
open Sarkozy.NormBoundsPaper (kD kP sum_kP sum_kD p_gt_one)
open Sarkozy.JointRows.PaleyGauss (chiR paley paley_anti paley_sq)
open Sarkozy.MiddleRecords (dG etaG)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-! ## Centred norms from form bounds -/

section Generic

variable {B : Type} [Fintype B] [DecidableEq B]

omit [DecidableEq B] in
/-- **A centred norm from a mean-zero form bound** (for a coupling with both marginals `μ`). -/
theorem centredNorm_of_form {μ : B → ℝ} {C : Matrix B B ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (hC : ∀ a b, 0 ≤ C a b) (hrow : ∀ a, ∑ b, C a b = μ a) (hcol : ∀ b, ∑ a, C a b = μ b)
    {d : ℝ} (hd : 0 ≤ d)
    (hform : ∀ u v : B → ℝ, ∑ a, μ a * u a = 0 → ∑ a, μ a * v a = 0 →
      |u ⬝ᵥ (C *ᵥ v)| ≤ d * Real.sqrt (∑ a, μ a * u a ^ 2) * Real.sqrt (∑ a, μ a * v a ^ 2)) :
    CentredNorm μ C d := by
  intro f hf
  set w := condM C μ *ᵥ f
  have hw : ∀ b, μ b * w b = (C *ᵥ f) b := by
    intro b
    simp only [w, Matrix.mulVec, dotProduct, mul_sum]
    exact sum_congr rfl fun a _ => by rw [← mul_assoc, mul_condM hC hrow]
  have hnorm : ∑ b, μ b * w b ^ 2 = w ⬝ᵥ (C *ᵥ f) := by
    simp only [dotProduct]
    exact sum_congr rfl fun b _ => by rw [← hw b]; ring
  have hw0 : ∑ b, μ b * w b = 0 := by
    simp only [hw, Matrix.mulVec, dotProduct]
    rw [sum_comm]
    simp only [← sum_mul, hcol]
    exact hf
  have h := hform w f hw0 hf
  rw [← hnorm] at h
  set W := ∑ b, μ b * w b ^ 2
  set S := ∑ a, μ a * f a ^ 2
  have hW : 0 ≤ W := sum_nonneg fun b _ => mul_nonneg (hμ b) (sq_nonneg _)
  have hS : 0 ≤ S := sum_nonneg fun a _ => mul_nonneg (hμ a) (sq_nonneg _)
  have hsW := Real.sq_sqrt hW
  have hsS := Real.sq_sqrt hS
  have h1 : Real.sqrt W ≤ d * Real.sqrt S := by
    rcases (Real.sqrt_nonneg W).lt_or_eq with hp | hz
    · have : Real.sqrt W * Real.sqrt W ≤ d * Real.sqrt W * Real.sqrt S := by
        rw [Real.mul_self_sqrt hW]; exact (le_abs_self W).trans h
      nlinarith
    · rw [← hz]; exact mul_nonneg hd (Real.sqrt_nonneg _)
  have h2 := mul_self_le_mul_self (Real.sqrt_nonneg W) h1
  rw [Real.mul_self_sqrt hW] at h2
  calc W ≤ d * Real.sqrt S * (d * Real.sqrt S) := h2
    _ = d ^ 2 * (Real.sqrt S * Real.sqrt S) := by ring
    _ = d ^ 2 * S := by rw [Real.mul_self_sqrt hS]

end Generic

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem sum_pair (H : ZMod p × ZMod p → ℝ) : ∑ x, H x = ∑ a, ∑ a₁, H (a, a₁) :=
  Fintype.sum_prod_type H

/-! ## The source -/

omit [Fact p.Prime] in
theorem off_mul_self (x : ZMod p × ZMod p) : off x * off x = off x := by
  unfold off; split_ifs <;> norm_num

omit [Fact p.Prime] in
theorem ind4_off (x y : ZMod p × ZMod p) : off x * off y * ind4 x y = ind4 x y := by
  unfold ind4
  have h1 := off_mul_self x
  have h2 := off_mul_self y
  calc off x * off y * (off x * off y * ((1 - dl y.1 x.1 - dl y.1 x.2) *
        (1 - dl y.2 x.1 - dl y.2 x.2)))
      = (off x * off x) * (off y * off y) * ((1 - dl y.1 x.1 - dl y.1 x.2) *
        (1 - dl y.2 x.1 - dl y.2 x.2)) := by ring
    _ = _ := by rw [h1, h2]

theorem card_zmod_real : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]

variable (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)

/-- **`‖D_p − J‖ ≤ d_p`** (form version, on mean-zero functions of `L²(m_p)`). -/
theorem src_form_le (hp : 5 ≤ p) (u v : ZMod p × ZMod p → ℝ) (hu : ∑ x, mP p x * u x = 0)
    (hv : ∑ x, mP p x * v x = 0) :
    |u ⬝ᵥ (srcC hne *ᵥ v)| ≤ dG p * Real.sqrt (∑ x, mP p x * u x ^ 2) *
      Real.sqrt (∑ x, mP p x * v x ^ 2) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  set N : ℝ := (p : ℝ) * ((p : ℝ) - 1)
  have hN : 0 < N := by simp only [N]; nlinarith
  set g : ZMod p × ZMod p → ℝ := fun x => off x * u x
  set h : ZMod p × ZMod p → ℝ := fun x => off x * v x
  have hg : OffDiag g := fun a => by simp [g, off]
  have hh : OffDiag h := fun a => by simp [h, off]
  have hmP : ∀ x, mP p x = off x / N := fun x => mP_eq_off x
  have hg0 : ∑ x, g x = 0 := by
    have : ∑ x, g x = N * ∑ x, mP p x * u x := by
      rw [mul_sum]
      exact sum_congr rfl fun x _ => by rw [hmP]; simp only [g]; field_simp
    rw [this, hu, mul_zero]
  have hh0 : ∑ x, h x = 0 := by
    have : ∑ x, h x = N * ∑ x, mP p x * v x := by
      rw [mul_sum]
      exact sum_congr rfl fun x _ => by rw [hmP]; simp only [h]; field_simp
    rw [this, hv, mul_zero]
  have hg2 : ∑ x, g x ^ 2 = N * ∑ x, mP p x * u x ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [hmP]
    have := off_mul_self x
    simp only [g]
    field_simp
    linear_combination u x ^ 2 * this
  have hh2 : ∑ x, h x ^ 2 = N * ∑ x, mP p x * v x ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [hmP]
    have := off_mul_self x
    simp only [h]
    field_simp
    linear_combination v x ^ 2 * this
  have hcard : 4 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  have hT := T_bilin hcard hg hh hg0 hh0
  rw [card_zmod_real, hg2, hh2] at hT
  have hTuv : T g h = ∑ x, ∑ y, u x * ind4 x y * v y := by
    unfold T
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    have := ind4_off x y
    calc g x * ind4 x y * h y = u x * (off x * off y * ind4 x y) * v y := by
          simp only [g, h]; ring
      _ = _ := by rw [this]
  have hform : u ⬝ᵥ (srcC hne *ᵥ v) =
      T g h / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * ((p : ℝ) - 3)) := by
    rw [hTuv]
    simp only [dotProduct, Matrix.mulVec, srcC_eq hne hp, sum_div, mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    ring
  set Su := ∑ x, mP p x * u x ^ 2
  set Sv := ∑ x, mP p x * v x ^ 2
  have hSu : 0 ≤ Su := sum_nonneg fun x _ => mul_nonneg (mP_nonneg x) (sq_nonneg _)
  have hSv : 0 ≤ Sv := sum_nonneg fun x _ => mul_nonneg (mP_nonneg x) (sq_nonneg _)
  rw [Real.sqrt_mul hN.le, Real.sqrt_mul hN.le] at hT
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have hD : 0 < (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * ((p : ℝ) - 3) := by
    have : 0 < ((p : ℝ) - 2) * ((p : ℝ) - 3) := by nlinarith
    nlinarith
  rw [hform, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have e : dG (p : ℝ) * Real.sqrt Su * Real.sqrt Sv *
      ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * ((p : ℝ) - 3)) =
      2 * ((p : ℝ) - 3) * (Real.sqrt N * Real.sqrt Su) * (Real.sqrt N * Real.sqrt Sv) := by
    have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
    calc dG (p : ℝ) * Real.sqrt Su * Real.sqrt Sv *
          ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * ((p : ℝ) - 3))
        = 2 * ((p : ℝ) - 3) * N * (Real.sqrt Su * Real.sqrt Sv) := by
          unfold dG; simp only [N]; field_simp
      _ = _ := by linear_combination (-(2 * ((p : ℝ) - 3) * Real.sqrt Su * Real.sqrt Sv)) * hsN
  rw [e]
  exact hT

theorem src_coupling_row (x : ZMod p × ZMod p) : ∑ y, srcC hne x y = mP p x :=
  (srcC_coupling hne x).1

theorem src_coupling_col (y : ZMod p × ZMod p) : ∑ x, srcC hne x y = mP p y :=
  (srcC_coupling hne y).2

/-- **The centred norm of the source is at most `d_p`.** -/
theorem src_centred (hp : 5 ≤ p) : CentredNorm (mP p) (srcC hne) (dG p) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  refine centredNorm_of_form mP_nonneg (srcC_nonneg hne) (src_coupling_row hne)
    (src_coupling_col hne) ?_ fun u v hu hv => src_form_le hne hp u v hu hv
  unfold dG
  exact div_nonneg (by norm_num) (by linarith)

/-! ## The first-coordinate replacement -/

/-- `V₀^* u`, the conditional mean over the second label: `ū(a) = ∑_{a₁} k_D(a₁ − a) u(a, a₁)`. -/
noncomputable def bar (u : ZMod p × ZMod p → ℝ) (a : ZMod p) : ℝ :=
  ∑ a₁, kD p (a₁ - a) * u (a, a₁)

theorem kD_nonneg (d : ZMod p) : 0 ≤ kD p d := by
  unfold kD
  have : (1 : ℝ) < p := p_gt_one
  split_ifs
  · exact le_rfl
  · exact (one_div_pos.mpr (by linarith)).le

theorem sum_bar (u : ZMod p × ZMod p → ℝ) : ∑ a, bar u a = p * ∑ x, mP p x * u x := by
  have hp : (p : ℝ) ≠ 0 := by have := p_gt_one (p := p); linarith
  rw [sum_pair, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [bar, mul_sum]
  refine sum_congr rfl fun a₁ _ => ?_
  unfold mP
  field_simp

theorem bar_sq_le (u : ZMod p × ZMod p → ℝ) :
    ∑ a, bar u a ^ 2 ≤ p * ∑ x, mP p x * u x ^ 2 := by
  have hp : (p : ℝ) ≠ 0 := by have := p_gt_one (p := p); linarith
  have hJ : ∀ a, bar u a ^ 2 ≤ ∑ a₁, kD p (a₁ - a) * u (a, a₁) ^ 2 := by
    intro a
    unfold bar
    have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun a₁ => Real.sqrt (kD p (a₁ - a)))
      (fun a₁ => Real.sqrt (kD p (a₁ - a)) * u (a, a₁))
    have e1 : ∀ a₁, Real.sqrt (kD p (a₁ - a)) * (Real.sqrt (kD p (a₁ - a)) * u (a, a₁)) =
        kD p (a₁ - a) * u (a, a₁) := fun a₁ => by
      rw [← mul_assoc, Real.mul_self_sqrt (kD_nonneg _)]
    have e2 : ∀ a₁, Real.sqrt (kD p (a₁ - a)) ^ 2 = kD p (a₁ - a) :=
      fun a₁ => Real.sq_sqrt (kD_nonneg _)
    have e3 : ∀ a₁, (Real.sqrt (kD p (a₁ - a)) * u (a, a₁)) ^ 2 =
        kD p (a₁ - a) * u (a, a₁) ^ 2 := fun a₁ => by rw [mul_pow, e2]
    simp only [e1, e2, e3] at h
    rw [sum_shift, sum_kD, one_mul] at h
    exact h
  calc ∑ a, bar u a ^ 2 ≤ ∑ a, ∑ a₁, kD p (a₁ - a) * u (a, a₁) ^ 2 := sum_le_sum fun a _ => hJ a
    _ = _ := by
      rw [sum_pair, mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun a₁ _ => ?_
      unfold mP
      field_simp

variable (hF : ringChar (ZMod p) ≠ 2)

/-- **The first-coordinate form**: `⟨u, P^s v⟩ = p⁻¹ ∑_a ū(a) ∑_c k_P(c − a) v̄(c)`. -/
theorem first_form (u v : ZMod p × ZMod p → ℝ) :
    u ⬝ᵥ (firstC hF *ᵥ v) = (1 / (p : ℝ)) * ∑ a, bar u a * ∑ c, kP p (c - a) * bar v c := by
  simp only [dotProduct, Matrix.mulVec, firstC_eq, sum_pair, bar, Finset.sum_mul_sum]
  simp only [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  refine sum_congr rfl fun a₁ _ => ?_
  refine sum_congr rfl fun c _ => sum_congr rfl fun c₁ _ => ?_
  ring

/-- `k_P = k_D + χ/(p − 1)`. -/
theorem kP_eq (d : ZMod p) : kP p d = kD p d + chiR p d / ((p : ℝ) - 1) := by
  unfold kP kD chiR
  by_cases hd : d = 0
  · subst hd
    simp
  · rcases quadraticChar_dichotomy hd with h | h
    · simp only [h, hd, ↓reduceIte, Int.cast_one]
      ring
    · have : (-1 : ℤ) ≠ 1 := by norm_num
      simp only [h, hd, ↓reduceIte, Int.cast_neg, Int.cast_one]
      norm_num
      ring

/-- **The Paley norm**: `‖K_P h‖² = ρ_p² ‖h‖²` on mean-zero functions (`p ≡ 3 (4)`). -/
theorem paley_norm (h3 : p % 4 = 3) (h : ZMod p → ℝ) (h0 : ∑ c, h c = 0) :
    ∑ a, (∑ c, kP p (c - a) * h c) ^ 2 = ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2 * ∑ a, h a ^ 2 := by
  have hp1 : (1 : ℝ) < p := p_gt_one
  have hp0 : (0 : ℝ) < p := by linarith
  have hq : (p : ℝ) - 1 ≠ 0 := by linarith
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hs0 : Real.sqrt p ≠ 0 := by positivity
  have hK : ∀ a, ∑ c, kP p (c - a) * h c = (-h a + Real.sqrt p * paley p h a) / ((p : ℝ) - 1) := by
    intro a
    have hD : ∑ c, kD p (c - a) * h c = -h a / ((p : ℝ) - 1) := by
      unfold kD
      have : ∀ c, (if c - a = 0 then (0 : ℝ) else 1 / ((p : ℝ) - 1)) * h c =
          h c / ((p : ℝ) - 1) - (if c = a then h a / ((p : ℝ) - 1) else 0) := by
        intro c
        by_cases hc : c = a
        · subst hc; simp
        · have : c - a ≠ 0 := sub_ne_zero.mpr hc
          simp only [this, hc, ↓reduceIte]
          ring
      rw [sum_congr rfl fun c _ => this c, sum_sub_distrib, sum_ite_eq']
      simp only [mem_univ, ↓reduceIte]
      rw [show ∑ c, h c / ((p : ℝ) - 1) = (∑ c, h c) / ((p : ℝ) - 1) by
        simp only [div_eq_mul_inv, sum_mul], h0]
      ring
    simp only [kP_eq, add_mul, sum_add_distrib, hD, paley]
    rw [show ∑ c, chiR p (c - a) / ((p : ℝ) - 1) * h c =
      (∑ c, chiR p (c - a) * h c) / ((p : ℝ) - 1) by
        simp only [div_eq_mul_inv, sum_mul]
        exact sum_congr rfl fun c _ => by ring]
    have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
    field_simp
    linear_combination (-(∑ x, chiR p (x - a) * h x)) * hs2
  have hanti : ∑ a, h a * paley p h a = 0 := by
    have := paley_anti h3 h h
    have e : ∑ t, paley p h t * h t = ∑ t, h t * paley p h t :=
      sum_congr rfl fun t _ => mul_comm _ _
    linarith
  have hiso : ∑ a, paley p h a ^ 2 = ∑ a, h a ^ 2 := by
    have := paley_anti h3 (paley p h) h
    simp only [paley_sq h3, h0, zero_div, sub_zero] at this
    rw [show ∑ a, paley p h a ^ 2 = ∑ t, paley p h t * paley p h t from
      sum_congr rfl fun t _ => sq _, this]
    simp only [neg_mul, sum_neg_distrib, neg_neg]
    exact sum_congr rfl fun t _ => (sq _).symm
  simp only [hK, div_pow]
  rw [← sum_div]
  have e : ∀ a, (-h a + Real.sqrt p * paley p h a) ^ 2 =
      h a ^ 2 - 2 * Real.sqrt p * (h a * paley p h a) + p * paley p h a ^ 2 := by
    intro a
    have : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
    linear_combination (paley p h a) ^ 2 * this
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hanti, hiso]
  field_simp
  ring

theorem sum_bar_eq_zero {u : ZMod p × ZMod p → ℝ} (hu : ∑ x, mP p x * u x = 0) :
    ∑ a, bar u a = 0 := by
  rw [sum_bar, hu, mul_zero]

/-- **The first-coordinate form on mean-zero functions**: `|⟨u, P^s v⟩| ≤ ρ_p ‖u‖ ‖v‖`. -/
theorem first_form_le (h3 : p % 4 = 3) (u v : ZMod p × ZMod p → ℝ)
    (hv : ∑ x, mP p x * v x = 0) :
    |u ⬝ᵥ (firstC hF *ᵥ v)| ≤ Real.sqrt (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2) *
      Real.sqrt (∑ x, mP p x * u x ^ 2) * Real.sqrt (∑ x, mP p x * v x ^ 2) := by
  have hp1 : (1 : ℝ) < p := p_gt_one
  have hp0 : (0 : ℝ) < p := by linarith
  rw [first_form]
  set K := fun a => ∑ c, kP p (c - a) * bar v c
  have hKn := paley_norm h3 (bar v) (sum_bar_eq_zero hv)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ (bar u) K
  have hcs' := Real.sum_mul_le_sqrt_mul_sqrt univ (fun a => -bar u a) K
  have habs : |∑ a, bar u a * K a| ≤ Real.sqrt (∑ a, bar u a ^ 2) * Real.sqrt (∑ a, K a ^ 2) := by
    rw [abs_le]
    refine ⟨?_, hcs⟩
    simp only [neg_sq, neg_mul, sum_neg_distrib] at hcs'
    linarith
  set ρ2 := ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2
  have hρ2 : 0 ≤ ρ2 := by positivity
  have hK : Real.sqrt (∑ a, K a ^ 2) = Real.sqrt ρ2 * Real.sqrt (∑ a, bar v a ^ 2) := by
    rw [show ∑ a, K a ^ 2 = ρ2 * ∑ a, bar v a ^ 2 from hKn, Real.sqrt_mul hρ2]
  have hu2 := bar_sq_le u
  have hv2 := bar_sq_le v
  have hSu : 0 ≤ ∑ x, mP p x * u x ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (mP_nonneg x) (sq_nonneg _)
  have hSv : 0 ≤ ∑ x, mP p x * v x ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (mP_nonneg x) (sq_nonneg _)
  have su : Real.sqrt (∑ a, bar u a ^ 2) ≤ Real.sqrt p * Real.sqrt (∑ x, mP p x * u x ^ 2) := by
    rw [← Real.sqrt_mul hp0.le]; exact Real.sqrt_le_sqrt hu2
  have sv : Real.sqrt (∑ a, bar v a ^ 2) ≤ Real.sqrt p * Real.sqrt (∑ x, mP p x * v x ^ 2) := by
    rw [← Real.sqrt_mul hp0.le]; exact Real.sqrt_le_sqrt hv2
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (p : ℝ))]
  calc 1 / (p : ℝ) * |∑ a, bar u a * K a|
      ≤ 1 / (p : ℝ) * (Real.sqrt (∑ a, bar u a ^ 2) *
          (Real.sqrt ρ2 * Real.sqrt (∑ a, bar v a ^ 2))) :=
        mul_le_mul_of_nonneg_left (habs.trans (le_of_eq (by rw [hK]))) (by positivity)
    _ ≤ 1 / (p : ℝ) * ((Real.sqrt p * Real.sqrt (∑ x, mP p x * u x ^ 2)) *
          (Real.sqrt ρ2 * (Real.sqrt p * Real.sqrt (∑ x, mP p x * v x ^ 2)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul su (mul_le_mul_of_nonneg_left sv
          (Real.sqrt_nonneg _)) (by positivity) (by positivity)) (by positivity)
    _ = Real.sqrt ρ2 * Real.sqrt (∑ x, mP p x * u x ^ 2) * Real.sqrt (∑ x, mP p x * v x ^ 2) *
          (Real.sqrt p * Real.sqrt p / p) := by ring
    _ = _ := by rw [hsq, div_self hp0.ne', mul_one]

theorem first_coupling_row (hp2 : p ≠ 2) (x : ZMod p × ZMod p) : ∑ y, firstC hF x y = mP p x :=
  (firstC_coupling hF hp2 x).1

theorem first_coupling_col (hp2 : p ≠ 2) (y : ZMod p × ZMod p) :
    ∑ x, firstC hF x y = mP p y :=
  (firstC_coupling hF hp2 y).2

/-- **The centred norm of the first-coordinate replacement is at most `ρ_p`.** -/
theorem first_centred (h3 : p % 4 = 3) :
    CentredNorm (mP p) (firstC hF) (Real.sqrt (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2)) := by
  have hp2 : p ≠ 2 := by omega
  exact centredNorm_of_form mP_nonneg (firstC_nonneg hF) (first_coupling_row hF hp2)
    (first_coupling_col hF hp2) (Real.sqrt_nonneg _) fun u v _ hv => first_form_le hF h3 u v hv

/-- `½(k_P(d) + k_P(−d)) = k_D(d)` for `p ≡ 3 (4)`. -/
theorem kP_sym (h3 : p % 4 = 3) (d : ZMod p) : kP p d + kP p (-d) = 2 * kD p d := by
  rw [kP_eq, kP_eq]
  have hχ : chiR p (-d) = -chiR p d := Sarkozy.JointRows.PaleyGauss.chiR_neg h3 d
  have hD : kD p (-d) = kD p d := by
    unfold kD
    by_cases hd : d = 0
    · subst hd
      simp
    · have : -d ≠ 0 := neg_ne_zero.mpr hd
      simp only [hd, this, ↓reduceIte]
  rw [hχ, hD]
  ring

/-- **The symmetric part of the first-coordinate replacement on mean-zero functions**:
`|½(⟨u, P^s v⟩ + ⟨v, P^s u⟩)| ≤ η^G_p ‖u‖ ‖v‖` (the symmetric part of `k_P` is `k_D`, whose
eigenvalue on mean-zero functions is `−η^G_p`). -/
theorem first_sym_le (h3 : p % 4 = 3) (u v : ZMod p × ZMod p → ℝ)
    (hv : ∑ x, mP p x * v x = 0) :
    |(1 / 2) * (u ⬝ᵥ (firstC hF *ᵥ v)) + (1 / 2) * (v ⬝ᵥ (firstC hF *ᵥ u))| ≤
      etaG p * Real.sqrt (∑ x, mP p x * u x ^ 2) * Real.sqrt (∑ x, mP p x * v x ^ 2) := by
  have hp1 : (1 : ℝ) < p := p_gt_one
  have hp0 : (0 : ℝ) < p := by linarith
  have hq : (p : ℝ) - 1 ≠ 0 := by linarith
  have hsym : (1 / 2) * (u ⬝ᵥ (firstC hF *ᵥ v)) + (1 / 2) * (v ⬝ᵥ (firstC hF *ᵥ u)) =
      -(1 / ((p : ℝ) * ((p : ℝ) - 1))) * ∑ a, bar u a * bar v a := by
    rw [first_form, first_form]
    have e : ∑ a, bar v a * ∑ c, kP p (c - a) * bar u c =
        ∑ a, bar u a * ∑ c, kP p (a - c) * bar v c := by
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun a _ => sum_congr rfl fun c _ => by ring
    rw [e]
    have e2 : ∀ a, (1 / 2 : ℝ) * (∑ c, kP p (c - a) * bar v c) +
        (1 / 2) * (∑ c, kP p (a - c) * bar v c) = ∑ c, kD p (c - a) * bar v c := by
      intro a
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun c _ => ?_
      have := kP_sym h3 (c - a)
      rw [neg_sub] at this
      linear_combination (1 / 2 * bar v c) * this
    have e3 : ∀ a, ∑ c, kD p (c - a) * bar v c = -bar v a / ((p : ℝ) - 1) := by
      intro a
      unfold kD
      have : ∀ c, (if c - a = 0 then (0 : ℝ) else 1 / ((p : ℝ) - 1)) * bar v c =
          bar v c / ((p : ℝ) - 1) - (if c = a then bar v a / ((p : ℝ) - 1) else 0) := by
        intro c
        by_cases hc : c = a
        · subst hc; simp
        · have : c - a ≠ 0 := sub_ne_zero.mpr hc
          simp only [this, hc, ↓reduceIte]
          ring
      rw [sum_congr rfl fun c _ => this c, sum_sub_distrib, sum_ite_eq']
      simp only [mem_univ, ↓reduceIte]
      rw [show ∑ c, bar v c / ((p : ℝ) - 1) = (∑ c, bar v c) / ((p : ℝ) - 1) by
        simp only [div_eq_mul_inv, sum_mul], sum_bar_eq_zero hv]
      ring
    have e4 : (1 / 2 : ℝ) * (1 / (p : ℝ) * ∑ a, bar u a * ∑ c, kP p (c - a) * bar v c) +
        (1 / 2) * (1 / (p : ℝ) * ∑ a, bar u a * ∑ c, kP p (a - c) * bar v c) =
        1 / (p : ℝ) * ∑ a, bar u a * ((1 / 2 : ℝ) * (∑ c, kP p (c - a) * bar v c) +
          (1 / 2) * (∑ c, kP p (a - c) * bar v c)) := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      ring_nf
    rw [e4]
    simp only [e2, e3]
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    field_simp
  rw [hsym, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((p : ℝ) * ((p : ℝ) - 1)))]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ (bar u) (bar v)
  have hcs' := Real.sum_mul_le_sqrt_mul_sqrt univ (fun a => -bar u a) (bar v)
  have habs : |∑ a, bar u a * bar v a| ≤
      Real.sqrt (∑ a, bar u a ^ 2) * Real.sqrt (∑ a, bar v a ^ 2) := by
    rw [abs_le]
    refine ⟨?_, hcs⟩
    simp only [neg_sq, neg_mul, sum_neg_distrib] at hcs'
    linarith
  have su : Real.sqrt (∑ a, bar u a ^ 2) ≤ Real.sqrt p * Real.sqrt (∑ x, mP p x * u x ^ 2) := by
    rw [← Real.sqrt_mul hp0.le]; exact Real.sqrt_le_sqrt (bar_sq_le u)
  have sv : Real.sqrt (∑ a, bar v a ^ 2) ≤ Real.sqrt p * Real.sqrt (∑ x, mP p x * v x ^ 2) := by
    rw [← Real.sqrt_mul hp0.le]; exact Real.sqrt_le_sqrt (bar_sq_le v)
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  calc 1 / ((p : ℝ) * ((p : ℝ) - 1)) * |∑ a, bar u a * bar v a|
      ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) * ((Real.sqrt p * Real.sqrt (∑ x, mP p x * u x ^ 2)) *
          (Real.sqrt p * Real.sqrt (∑ x, mP p x * v x ^ 2))) :=
        mul_le_mul_of_nonneg_left (habs.trans (mul_le_mul su sv (Real.sqrt_nonneg _)
          (by positivity))) (by positivity)
    _ = Real.sqrt (∑ x, mP p x * u x ^ 2) * Real.sqrt (∑ x, mP p x * v x ^ 2) *
          (Real.sqrt p * Real.sqrt p) / ((p : ℝ) * ((p : ℝ) - 1)) := by ring
    _ = _ := by
      rw [hsq]
      unfold etaG
      field_simp

/-- **The prime symmetric difference of the first-coordinate merge** (singleton supports):
`|Sym⟨u, (P^s − D_p) v⟩| ≤ (d_p + η^G_p) ‖u‖ ‖v‖` on mean-zero functions. -/
theorem first_single (hp : 5 ≤ p) (h3 : p % 4 = 3) (u v : ZMod p × ZMod p → ℝ)
    (hu : ∑ x, mP p x * u x = 0) (hv : ∑ x, mP p x * v x = 0) :
    |chg1 (firstC hF) (srcC hne) (1 / 2) (1 / 2) 1 u v| ≤
      (dG p + etaG p) * Real.sqrt (∑ x, mP p x * u x ^ 2) *
        Real.sqrt (∑ x, mP p x * v x ^ 2) := by
  unfold chg1
  have h1 := first_sym_le hF h3 u v hv
  have h2 := src_form_le hne hp u v hu hv
  rw [one_mul]
  calc |1 / 2 * (u ⬝ᵥ (firstC hF *ᵥ v)) + 1 / 2 * (v ⬝ᵥ (firstC hF *ᵥ u)) -
        u ⬝ᵥ (srcC hne *ᵥ v)|
      ≤ |1 / 2 * (u ⬝ᵥ (firstC hF *ᵥ v)) + 1 / 2 * (v ⬝ᵥ (firstC hF *ᵥ u))| +
        |u ⬝ᵥ (srcC hne *ᵥ v)| := abs_sub _ _
    _ ≤ _ := by linarith

end Prime

end Sarkozy.NormBoundsPaper2
