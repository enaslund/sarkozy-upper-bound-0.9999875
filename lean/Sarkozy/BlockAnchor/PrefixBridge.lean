module

public import Sarkozy.BlockAnchor.Paper
public import Sarkozy.PartVLaws.PaperPrefix

@[expose] public section

/-!
# The block laws of the prefix from V2's atoms (`def:cp1`, `def:construction`(b))

V2's `PartVLaws.PaperPrefix` cuts the fixed primes by the atom map `paperAtomMap blockOf`
(each square-clique prime `{p}` its own atom, each class-three prime to its block `blockOf j`) and
gives the atom laws `paperAtomLaw Bk`: V1's prefix laws at the atoms `{p}`, with (R1)–(R3)
proved, and the block laws of `Bk : PaperBlockAtoms blockOf`. With the block assignment
`blk := paperAtomMap blockOf`, these are exactly the fields `μ₀`, `rp₀`, `inv₀`, `unif₀` of
`BlockAnchor.BlockPaperData` (the alphabets agree by definition). So on the block atoms D1's open
prefix fields reduce to V2's block-atom inputs (`PaperBlockAtoms`): the square-clique atoms `{p}`
are proved.

This file depends on V2's `PaperPrefix.lean` (in progress on 2 November) and is not imported by
`Sarkozy.BlockAnchor.All`.
-/

namespace Sarkozy.BlockAnchor

open Sarkozy.BlockFrame CancellationSteps

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-- The block laws of the prefix from V2's atom laws. -/
noncomputable def v2BlockLaws (Bk : PartVLaws.PaperBlockAtoms blockOf) :
    ∀ β, FiniteLaw (Slot → BlockRes paperM0 (PartVLaws.paperAtomMap blockOf) β) :=
  PartVLaws.paperAtomLaw Bk

omit [Fintype B] in
theorem v2BlockLaws_rp (Bk : PartVLaws.PaperBlockAtoms blockOf) :
    ∀ β, TheoremC.FamilyReflectionPositive (signedIntegral (v2BlockLaws blockOf Bk β).weight)
  | .inl q => PartVLaws.prefixAtom_rp blockOf q
  | .inr b => Bk.rp b

omit [Fintype B] in
theorem v2BlockLaws_unif (Bk : PartVLaws.PaperBlockAtoms blockOf) :
    ∀ β, HasUniformMarginals (v2BlockLaws blockOf Bk β)
  | .inl q => PartVLaws.prefixAtom_unif blockOf q
  | .inr b => Bk.unif b

omit [Fintype B] in
theorem v2BlockLaws_inv (Bk : PartVLaws.PaperBlockAtoms blockOf) :
    ∀ β (a : ∀ i, (ZMod (blockModuli paperM0 (PartVLaws.paperAtomMap blockOf) β i))ˣ)
      (b : BlockRes paperM0 (PartVLaws.paperAtomMap blockOf) β),
      (∀ i, IsSquare ((a i : ZMod (blockModuli paperM0 (PartVLaws.paperAtomMap blockOf) β i)))) →
        ∀ F : (Slot → BlockRes paperM0 (PartVLaws.paperAtomMap blockOf) β) → ℝ,
          (v2BlockLaws blockOf Bk β).expect (fun z => F (fun v =>
              PaperFrame.piAffineEquiv (blockModuli paperM0 (PartVLaws.paperAtomMap blockOf) β) a b
                (z v))) =
            (v2BlockLaws blockOf Bk β).expect F
  | .inl q, a, b, ha, F => PartVLaws.prefixAtom_inv blockOf q a b ha F
  | .inr c, a, b, ha, F => Bk.inv c a b ha F

end Sarkozy.BlockAnchor
