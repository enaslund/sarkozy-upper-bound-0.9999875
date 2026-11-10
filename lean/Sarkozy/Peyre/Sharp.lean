module

public import Sarkozy.Peyre.Correlation

/-!
# Peyre's tensorization in finite form, VIII: the role of conditioning

`rem:peyre:sharp` (ii) of Appendix B: the conditional hypothesis of `thm:peyre-finite`
cannot be replaced by bounds on unconditional pairwise correlations.  Let `X₁, X₂` be
independent uniform bits and `Y = X₁ + X₂ mod 2`.  Then `ρ(X₁;Y) = ρ(X₂;Y) = 0`, but
`ρ((X₁,X₂);Y) = 1`, and `ρ(X₂;Y | X₁ = x) = 1`.

Besides recording the remark, this checks that `maxCorr` is not degenerate: it takes the
values `0` and `1` on explicit examples.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

open Sarkozy

/-- The uniform law on two bits. -/
noncomputable def bitsLaw : FiniteLaw (Bool × Bool) where
  weight _ := 1 / 4
  nonneg _ := by norm_num
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
      nsmul_eq_mul]
    norm_num

theorem bitsLaw_expect (u : Bool × Bool → ℝ) :
    bitsLaw.expect u =
      (u (true, true) + u (true, false) + u (false, true) + u (false, false)) / 4 := by
  simp only [FiniteLaw.expect, bitsLaw, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- `Y = X₁ + X₂ mod 2`. -/
def bitsXor (ω : Bool × Bool) : Bool := xor ω.1 ω.2

/-- `ρ(X₁; Y) = 0`. -/
theorem maxCorr_fst_xor : maxCorr bitsLaw (fun ω : Bool × Bool => ω.1) bitsXor = 0 := by
  apply le_antisymm _ (maxCorr_nonneg _ _ _)
  apply maxCorr_le_of_corrLe le_rfl
  intro f g hf _
  rw [bitsLaw_expect] at hf
  simp only at hf
  rw [bitsLaw_expect]
  simp only [bitsXor, Bool.true_xor, Bool.false_xor, Bool.not_true, Bool.not_false,
    zero_mul]
  have h0 : f true = - f false := by linarith
  rw [h0]
  ring_nf
  simp

/-- `ρ(X₂; Y) = 0`. -/
theorem maxCorr_snd_xor : maxCorr bitsLaw (fun ω : Bool × Bool => ω.2) bitsXor = 0 := by
  apply le_antisymm _ (maxCorr_nonneg _ _ _)
  apply maxCorr_le_of_corrLe le_rfl
  intro f g hf _
  rw [bitsLaw_expect] at hf
  simp only at hf
  rw [bitsLaw_expect]
  simp only [bitsXor, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
    zero_mul]
  have h0 : f true = - f false := by linarith
  rw [h0]
  ring_nf
  simp

/-- `ρ((X₁, X₂); Y) = 1`: `Y` is a non-constant function of `(X₁, X₂)`. -/
theorem maxCorr_pair_xor : maxCorr bitsLaw (fun ω : Bool × Bool => ω) bitsXor = 1 := by
  apply le_antisymm (maxCorr_le_one _ _ _)
  have hmem : (1 : ℝ) ∈ corrSet bitsLaw (fun ω : Bool × Bool => ω) bitsXor := by
    refine ⟨fun ω => if xor ω.1 ω.2 then 1 else -1, fun b => if b then 1 else -1,
      ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [bitsLaw_expect]
      simp [bitsXor]
      try norm_num
  exact le_csSup (corrSet_bddAbove _ _ _) hmem

/-- `ρ(X₂; Y | X₁ = x) = 1`: given `X₁`, the variable `Y` determines `X₂`. -/
theorem maxCorr_snd_xor_cond (x : Bool)
    (h : 0 < prob bitsLaw (fun ω : Bool × Bool => ω.1 = x)) :
    maxCorr (condLaw bitsLaw (fun ω : Bool × Bool => ω.1 = x) h)
      (fun ω : Bool × Bool => ω.2) bitsXor = 1 := by
  apply le_antisymm (maxCorr_le_one _ _ _)
  have hp : prob bitsLaw (fun ω : Bool × Bool => ω.1 = x) = 1 / 2 := by
    unfold prob
    rw [bitsLaw_expect]
    cases x <;> simp [ind_of_pos, ind_of_neg] <;> norm_num
  have hce : ∀ u : Bool × Bool → ℝ,
      (condLaw bitsLaw (fun ω : Bool × Bool => ω.1 = x) h).expect u =
        (u (x, true) + u (x, false)) / 2 := by
    intro u
    rw [cond_expect, hp, bitsLaw_expect]
    cases x <;> simp [ind_of_pos, ind_of_neg] <;> ring
  have hmem : (1 : ℝ) ∈ corrSet (condLaw bitsLaw (fun ω : Bool × Bool => ω.1 = x) h)
      (fun ω : Bool × Bool => ω.2) bitsXor := by
    refine ⟨fun b => if b then 1 else -1, fun c => if xor x c then 1 else -1,
      ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hce]
      cases x <;> simp [bitsXor]
  exact le_csSup (corrSet_bddAbove _ _ _) hmem

end Sarkozy.Peyre
