module

public import Sarkozy.ComparisonLawPaper.Assembly
public import Sarkozy.PartVLaws.PaperPrefix

@[expose] public section

/-!
# Acceptance at a class-three block (`def:cp4`(a))

At a class-three block `𝔅` of the paper every prime has `e_p = 1` and modulus `p`, so the acceptance
clause of `def:cp4`(a) ("nonzero, of even valuation `2j < e_p`, with a square unit part") is
`χ_p(z_{v_e} - z_{u_e}) = 1` at every prime of the block (`paperPrefixAccepted_inr_iff`). This is
the form in which W8's `upperNu_component_accepts` (`prop:record:upper`(i), upper blocks) and
`subsec:middle-comparison` (middle blocks, "each accepts the six queries") state it; W8's report
(integration note 5) asked for this bridge.
-/

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.BlockFrame Sarkozy.CancellationSteps Sarkozy.PartVLaws

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

omit [Fintype B] [DecidableEq B] in
/-- The exponent of a coordinate of a class-three block is `e_p = 1`. -/
theorem paperEP_of_inr {b : B} (i : BlockIdx (paperAtomMap blockOf) (.inr b)) :
    paperEP i.1 = 1 := by
  have hj : i.1.1 % 4 ≠ 1 := paperAtomMap_inr blockOf i.2
  unfold paperEP
  simp only [hj, ↓reduceIte]

omit [Fintype B] [DecidableEq B] in
/-- **Acceptance at a class-three block is a nonzero square at every prime** (`def:cp4`(a) with
`e_p = 1`): `prefixAccepted … (.inr b) x y` (`paperPrefixAccepted`) iff `y_p - x_p` is a nonzero
square at every
coordinate `p` of the block. -/
theorem paperPrefixAccepted_inr_iff {b : B}
    (x y : BlockRes paperM0 (paperAtomMap blockOf) (.inr b)) :
    prefixAccepted paperM0 (paperAtomMap blockOf) paperPP paperEP (.inr b) x y ↔
      ∀ i, y i - x i ≠ 0 ∧ IsSquare (y i - x i) := by
  constructor
  · intro h i
    obtain ⟨hne, jj, hjj, r, _, hr, heq⟩ := h i
    rw [paperEP_of_inr blockOf i] at hjj
    have hjj0 : jj = 0 := by omega
    refine ⟨hne, ?_⟩
    rw [heq, hjj0, mul_zero, pow_zero, one_mul]
    exact hr
  · intro h i
    obtain ⟨hne, hsq⟩ := h i
    have hj : i.1.1 % 4 ≠ 1 := paperAtomMap_inr blockOf i.2
    have : Fact (paperM0 i.1).Prime := ⟨by rw [paperM0_cls3 hj]; exact paperJ0_prime i.1⟩
    refine ⟨hne, 0, by rw [paperEP_of_inr blockOf i]; norm_num, y i - x i, ?_, hsq, by simp⟩
    exact isUnit_iff_ne_zero.mpr hne

end Sarkozy.ComparisonLawPaper
