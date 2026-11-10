module

public import Sarkozy.PartVLaws.PieceCaps
public import Sarkozy.PartVLaws.InvariantBackground
public import Sarkozy.PartVLaws.PadicPrice

@[expose] public section

/-!
# Non-vacuity checks for the group-A files of `Sarkozy.PartVLaws`

* `PieceCell` (`PieceCaps.lean`) is a structure with proof fields: `toyCell` is an instance (the
  primes `[3]` of a cell `[x_j, 4)`, `n = ⌊L / log 4⌋`), and `toy_piece_caps` applies `piece_caps`
  to a piece with one exact block `[2]` (`𝔲(2) = 2⁴⁰`, so `log 2 < 𝔲(2)/2⁴⁰ = 1`) and that cell:
  all its hypotheses are discharged.
* `LawsInvariant` (`InvariantBackground.lean`) is discharged for the paper's laws themselves
  (`upperBlockFieldLaws_two_inv`, `tailFieldLaws_two_inv`, …), which exist at every large prime
  under H1 (V1's `upperNonempty_of_large`, `tailNonempty_of_large`); `toy_tail_inv` restates it
  at `p = 5` with nonemptiness as the only hypothesis.
* `PadicPrice.lean` introduces no hypothesis bundle; the depth tails are admissible
  (`isDepthTail_oddTail`, `isDepthTail_twoTail`), and `toy_Mpad` evaluates `M_pad` with no odd
  prime (`Q = 3`), where it is `K^{a/36} L_{2,m}`.
-/

namespace Sarkozy.PartVLaws.SanityA

open Finset Sarkozy.PartV

/-- A toy cell: the single prime `3` below `x_{j+1} = 4`. -/
noncomputable def toyCell : PieceCell :=
  PieceCell.ofCard [3] 4 (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    norm_num) (by norm_num)

/-- **`piece_caps` with every hypothesis discharged** on a toy piece. -/
theorem toy_piece_caps :
    (∀ b ∈ [[2]], (b.map fun p : ℕ => Real.log (p : ℝ)).sum ≤
      pieceCap (fun _ => 2 ^ 40) [[2]] [toyCell]) ∧
    (∀ c ∈ [toyCell], ∀ m, ((cellBlock c.ps c.n m).map fun p : ℕ => Real.log (p : ℝ)).sum ≤
      pieceCap (fun _ => 2 ^ 40) [[2]] [toyCell]) ∧
    pieceCap (fun _ => 2 ^ 40) [[2]] [toyCell] ≤ middleBudget := by
  refine piece_caps _ _ _ (fun b hb p hp => ?_) (fun b hb => ?_) (fun c hc => ?_)
  · simp only [List.mem_singleton] at hb
    subst hb
    simp only [List.mem_singleton] at hp
    subst hp
    have h := Real.log_two_lt_d9
    norm_num
    linarith
  · simp only [List.mem_singleton] at hb
    subst hb
    unfold blockU integerBudget middleBudget
    norm_num
  · simp only [List.mem_singleton] at hc
    subst hc
    exact PieceCell.ofCard_R_le _ _ _ _

/-- The tail laws satisfy `LawsInvariant` at `p = 5` as soon as they are defined. -/
theorem toy_tail_inv [Fact (Nat.Prime 5)] (hne : TailNonempty 5) :
    LawsInvariant (tailFieldLaws 5 hne).two ∧ LawsInvariant (tailFieldLaws 5 hne).one :=
  ⟨tailFieldLaws_two_inv 5 hne, tailFieldLaws_one_inv 5 hne⟩

/-- With no odd prime below `Q = 3`, `M_pad(K) = K^{a/36} L_{2,m}`. -/
theorem toy_Mpad (a : ℝ) (m : ℕ) (K : ℝ) :
    Mpad a m 3 K = K ^ (a / 36) * Ltwo m ((2 : ℝ) ^ (a / 18)) := by
  have h : indexPrimes 3 = ∅ := by decide
  rw [Mpad, h, prod_empty, mul_one]

end Sarkozy.PartVLaws.SanityA
