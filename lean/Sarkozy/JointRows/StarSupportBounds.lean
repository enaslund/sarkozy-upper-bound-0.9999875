module

public import Sarkozy.JointRows.StarTermBounds

/-! The centre multiplier only needs a bound on the support of its coordinate law. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks

variable {p : ℕ} [Fact p.Prime]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

theorem block_coordinate_ne_zero (νp : X → FiniteLaw (ZMod p)) (x : X → ZMod p)
    (hx : (blockLaw νp).weight x ≠ 0) (i : X) : (νp i).weight (x i) ≠ 0 := by
  intro hi
  exact hx (prod_eq_zero (mem_univ i) hi)

theorem bform_congr_left_support (νp : X → FiniteLaw (ZMod p))
    (νq : Y → FiniteLaw (ZMod p))
    (K L : (X → ZMod p) → (Y → ZMod p) → ℝ)
    (h : ∀ x, (blockLaw νp).weight x ≠ 0 → ∀ y, K x y = L x y)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    bform νp νq K f g = bform νp νq L f g := by
  unfold bform FiniteLaw.expect
  apply sum_congr rfl
  intro x _
  by_cases hx : (blockLaw νp).weight x = 0
  · simp [hx]
  · congr 1
    apply sum_congr rfl
    intro y _
    dsimp only
    rw [h x hx y]

theorem rowStar_multiplier_bound_support (hp : p ≠ 2)
    (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (i : X) (T : Finset Y) (hT : T.Nonempty) (a : ZMod p → ℝ)
    {κ b : ℝ} (hk : 0 ≤ κ) (hb : 0 ≤ b)
    (ha : ∀ t, (νp i).weight t ≠ 0 → |a t| ≤ b)
    (hdensX : ∀ t, (νp i).weight t ≤ κ / p)
    (hdensY : ∀ j ∈ T, ∀ t, (νq j).weight t ≤ κ / p)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    |bform νp νq (fun x y => a (x i) * ∏ j ∈ T, phi (νq j) (x i) (y j)) f g| ≤
      κ * (Real.sqrt p)⁻¹ * b * nrm (blockLaw νp) f * nrm (blockLaw νq) g := by
  let a' : ZMod p → ℝ := fun t => if (νp i).weight t = 0 then 0 else a t
  have ha' : ∀ t, |a' t| ≤ b := by
    intro t
    dsimp [a']
    split_ifs with ht
    · simpa only [abs_zero] using hb
    · exact ha t ht
  have heq := bform_congr_left_support νp νq
    (fun x y => a (x i) * ∏ j ∈ T, phi (νq j) (x i) (y j))
    (fun x y => a' (x i) * ∏ j ∈ T, phi (νq j) (x i) (y j))
    (fun x hx _ => by simp only [a', block_coordinate_ne_zero νp x hx i, ite_false]) f g
  rw [heq]
  exact rowStar_multiplier_bound hp νp νq i T hT a' hk hb ha' hdensX hdensY f g

end Sarkozy.JointRows.StarOps
