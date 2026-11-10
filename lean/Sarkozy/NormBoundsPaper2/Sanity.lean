module

public import Sarkozy.NormBoundsPaper2.MirrorBlock

@[expose] public section

/-!
# Non-vacuity and sharpness checks for `Sarkozy.NormBoundsPaper2`

* **The three prime couplings are probability laws with the actual half law as both marginals**
  (`sanity_src_mass`, `sanity_first_mass`, `sanity_mir_mass`): the old record (V1's `E` law), the
  first-coordinate replacement (V3's `firstLaw`) and the mirror-edge replacement (V3's
  `mirrorLaw`), read at the two pairs, have total mass one. So the identifications `srcC_eq`,
  `firstC_eq`, `mirC_eq` are not degenerate, and the marginals used in every norm are the actual
  ones (the 1 November pattern does not occur).
* **The source constant is sharp** (`sanity_src_sharp`): on `f(x) = u(x₀) + u(x₁)` with
  `∑ u = 0`, `T(f, f) = −2(p − 3) ∑ f²` (the eigenvalue `−2/(p − 2)` of `D_p`), so `T_bilin`
  (hence `d_p` in `src_form_le`) cannot be improved.
* The numerical side conditions hold at the paper's thresholds: `merge_numbers` at `b = 7`,
  `mirror_multi_sym`, `mirror_multi_skew`, `alpha_le` at `b = 2^24` (`sanity_numbers`).
* The new structures add no hypothesis: `NormBoundsRest2` is a verbatim copy of four fields of
  HN's `NormBoundsRest` (itself a copy of B8's `NormBounds`); the theorems
  `merge2_sym_paper`, `mirror_sym_paper`, `mirror_skew_paper` have no hypothesis beyond the block's
  (`ClassThreeBlock`, `MiddleNonempty`) and `7 ≤ b ≤ p` (resp. `2^24 ≤ b ≤ p`), all discharged at
  the paper's partition (`blockLeast_facts24`, used in `specRest_of_rest2`).
-/

namespace Sarkozy.NormBoundsPaper2

open Finset
open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVRecords
open Sarkozy.MiddleRecords (dG etaG sG aG)
open Sarkozy.NormBoundsPaper (rho)

section Mass

variable {p : ℕ} [Fact p.Prime]

theorem sanity_src_mass (hp : 5 ≤ p)
    (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) :
    ∑ x, ∑ y, srcC hne x y = 1 := by
  have _ := hp
  rw [sum_congr rfl fun x _ => src_coupling_row hne x, sum_mP]

theorem sanity_first_mass (hF : ringChar (ZMod p) ≠ 2) (hp2 : p ≠ 2) :
    ∑ x, ∑ y, firstC hF x y = 1 := by
  rw [sum_congr rfl fun x _ => first_coupling_row hF hp2 x, sum_mP]

theorem sanity_mir_mass (hm : (injLabellings (ZMod p) mirrorGraph).Nonempty) (hp : 7 ≤ p)
    (h3 : p % 4 = 3) : ∑ x, ∑ y, mirC hm x y = 1 := by
  rw [sum_congr rfl fun x _ => (mirC_coupling hm hp h3 x).1, sum_mP]

end Mass

section Sharp

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The source constant is attained**: on `f(x) = [x₀ ≠ x₁](u(x₀) + u(x₁))` with `∑ u = 0`,
`T(f, f) = −2(n − 3) ∑ f²`. -/
theorem sanity_src_sharp (u : X → ℝ) (hu : ∑ a, u a = 0) :
    T (fun x => off x * (u x.1 + u x.2)) (fun x => off x * (u x.1 + u x.2)) =
      -(2 * ((Fintype.card X : ℝ) - 3) *
        ∑ x : X × X, (off x * (u x.1 + u x.2)) ^ 2) := by
  set f : X × X → ℝ := fun x => off x * (u x.1 + u x.2)
  set n : ℝ := (Fintype.card X : ℝ)
  have hf : OffDiag f := fun a => by simp [f, off]
  have hoff : ∀ a b : X, off (a, b) = 1 - (if a = b then 1 else 0) := fun a b => by
    unfold off; split_ifs <;> simp
  have hsum0 : ∑ x, f x = 0 := by
    simp only [f, Fintype.sum_prod_type, hoff, sub_mul, one_mul, sum_sub_distrib, ite_mul,
      zero_mul, sum_ite_eq, mem_univ, ↓reduceIte, sum_add_distrib, sum_const, card_univ,
      nsmul_eq_mul, ← mul_sum, hu, mul_zero]
    ring
  -- the row sums `u_f(a) = 2(n − 2) u(a)`
  have hus : ∀ a, us f a = 2 * (n - 2) * u a := by
    intro a
    simp only [us, f, hoff, sub_mul, one_mul, sum_add_distrib, sum_sub_distrib, ite_mul, zero_mul,
      sum_ite_eq, sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul, hu]
    simp only [n]
    ring
  have hsq : ∑ x, f x ^ 2 = 2 * (n - 2) * ∑ a, u a ^ 2 := by
    have e : ∀ a b : X, f (a, b) ^ 2 = (u a + u b) ^ 2 - (if a = b then 4 * u a ^ 2 else 0) := by
      intro a b
      simp only [f, hoff]
      split_ifs with h
      · subst h; ring
      · ring
    simp only [Fintype.sum_prod_type, e, sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
    have e2 : ∀ a b : X, (u a + u b) ^ 2 = u a ^ 2 + u b ^ 2 + 2 * (u a * u b) := fun a b => by
      ring
    simp only [e2, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum, hu, mul_zero,
      add_zero]
    simp only [n]
    ring
  have hswap : ∑ x, f x * f (x.2, x.1) = ∑ x, f x ^ 2 := by
    refine sum_congr rfl fun x _ => ?_
    simp only [f, off, eq_comm (a := x.2), add_comm (u x.2)]
    ring
  rw [T_eq hf hf, hsum0, zero_mul, zero_sub, hswap]
  simp only [hus]
  have h3 : ∑ x, f x * f x = ∑ x, f x ^ 2 := sum_congr rfl fun x _ => (sq _).symm
  rw [h3, hsq]
  have e3 : ∑ a, 2 * (n - 2) * u a * (2 * (n - 2) * u a) = 4 * (n - 2) ^ 2 * ∑ a, u a ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun a _ => by ring
  rw [e3]
  ring

end Sharp

/-- The numerical side conditions at the paper's thresholds. -/
theorem sanity_numbers :
    (0 ≤ dG 7 ∧ dG 7 ≤ 1 ∧ rho 7 ^ 2 + dG 7 ^ 2 ≤ dG 7 + etaG 7) ∧
      ((|(1 / 2 : ℝ)| + |(1 / 2 : ℝ)|) * (2 / Real.sqrt (2 ^ 24)) ^ 2 + |(1 : ℝ)| * dG (2 ^ 24) ^ 2
        ≤ sG (2 ^ 24)) ∧
      ((|(1 / 2 : ℝ)| + |-(1 / 2 : ℝ)|) * (2 / Real.sqrt (2 ^ 24)) ^ 2 +
        |(0 : ℝ)| * dG (2 ^ 24) ^ 2 ≤ aG (2 ^ 24)) ∧
      dG (2 ^ 24) + sG (2 ^ 24) + aG (2 ^ 24) ≤ 2 / Real.sqrt (2 ^ 24) :=
  ⟨merge_numbers le_rfl, mirror_multi_sym le_rfl, mirror_multi_skew le_rfl,
    alpha_le (by linarith [sqrt_ge_of (b := 2 ^ 24) le_rfl])⟩

end Sarkozy.NormBoundsPaper2
