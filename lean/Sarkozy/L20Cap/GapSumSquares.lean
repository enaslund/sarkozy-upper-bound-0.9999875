module

public import Sarkozy.L20Cap.GapSplit

/-! An orthogonal domain split gives a sum-of-squares rectangle bound. -/

@[expose] public section

namespace Sarkozy.L20Cap

open Sarkozy.Cuts Sarkozy.Recentering

theorem two_block_sum_squares {X Y : Type*} [Fintype X] [Fintype Y]
    (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) {τ l c : ℝ}
    (hc : 0 ≤ c) (hprice : τ ^ 2 + l ^ 2 ≤ c ^ 2)
    (f₁ f₂ : Y → ℝ) (horth : ip β f₁ f₂ = 0)
    (h₁ : nrm α (recOp β A f₁) ≤ τ * nrm β f₁)
    (h₂ : nrm α (recOp β A f₂) ≤ l * nrm β f₂) :
    nrm α (recOp β A (fun y => f₁ y + f₂ y)) ≤
      c * nrm β (fun y => f₁ y + f₂ y) := by
  have hadd : nrm α (recOp β A (fun y => f₁ y + f₂ y)) ≤
      τ * nrm β f₁ + l * nrm β f₂ := by
    rw [recOp_add]
    exact (nrm_add_le _ _ _).trans (add_le_add h₁ h₂)
  have hsquare := pow_le_pow_left₀ (nrm_nonneg _ _) hadd 2
  have hnorm := nrm_sq_add β f₁ f₂
  rw [horth] at hnorm
  have hprice' := mul_le_mul_of_nonneg_right hprice
    (show 0 ≤ nrm β f₁ ^ 2 + nrm β f₂ ^ 2 by positivity)
  apply nrm_le_of_sq_le _ _ hc
  nlinarith [sq_nonneg (τ * nrm β f₂ - l * nrm β f₁)]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Nonempty (PairT F)] [Nonempty (CoreT F)]

theorem pair_ranges_sum_squares (h5 : 5 ≤ Fintype.card F) {τ l c : ℝ}
    (hc : 0 ≤ c) (hprice : τ ^ 2 + l ^ 2 ≤ c ^ 2)
    (hA : ∀ h : F → ℝ, ∑ z, h z = 0 →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h)) ≤
        τ * nrm (pairLaw (F := F)) (vOp h))
    (hB : ∀ g : PairT F → ℝ, (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc g) ≤
        l * nrm (pairLaw (F := F)) g)
    (f : PairT F → ℝ) :
    nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc f) ≤
      c * nrm (pairLaw (F := F)) f := by
  let f₀ : PairT F → ℝ := fun b => f b - (pairLaw (F := F)).expect f
  let h := hProj f₀
  let g : PairT F → ℝ := fun b => f₀ b - vOp h b
  have hh : ∑ z, h z = 0 := hProj_mean f₀
  have horth : ∀ h' : F → ℝ, ∑ z, h' z = 0 →
      ip (pairLaw (F := F)) (vOp h') g = 0 :=
    fun h' hh' => pair_split h5 f₀ h' hh'
  have hg : (pairLaw (F := F)).expect g = 0 := by
    dsimp only [g, f₀]
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_sub, FiniteLaw.expect_const,
      expect_vOp h hh]
    ring
  have he : f₀ = fun b => vOp h b + g b := by funext b; dsimp [g]; ring
  have hb := two_block_sum_squares coreLaw pairLaw Rc hc hprice
    (vOp h) g (horth h hh) (hA h hh) (hB g hg horth)
  rw [← he] at hb
  change nrm coreLaw (recOp pairLaw Rc (fun b => f b - pairLaw.expect f)) ≤ _ at hb
  rw [Rc_sub_const] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (nrm_sub_mean_le _ f) hc)

end Sarkozy.L20Cap
