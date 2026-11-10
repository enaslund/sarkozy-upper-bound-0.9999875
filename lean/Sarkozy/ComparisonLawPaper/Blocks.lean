module

public import Sarkozy.ComparisonLawPaper.Upper
public import Sarkozy.ComparisonLawPaper.Acceptance
public import Sarkozy.FirstStagePaper.Paper

@[expose] public section

/-!
# (CP4) at the class-three blocks, by their specification

A class-three block of the paper is an upper block or a middle block (V2's `PaperBlockSpec`). Its
(CP4) inputs `BlockInputs hW In S` depend on the specification `S`:

* an **upper block** (`.upper U`): W8's construction, with the inputs `UpperAtomInputs` (the
  replacing laws and the brackets of the changed records) on the block's primes, at the band's
  weights `U.W` and scale `U.r`; `UpperAtomInputs.toAtom` gives the atom, with V1's law
  `upperBlockReference` (the paper's `μ_𝔅`, which is the law of V2's `upperBlockAtom`);
* a **middle block** (any of the three roots): the atom data `AtomComparison` relative to A1's
  first-stage law `λ_𝔅 = ρ + δ_E` (`lem:middle-comparison-prices`, not constructed in Lean).

`BlockInputs.toAtom` gives in each case the `AtomComparison` relative to `λ_𝔅` (`specLam`), with
the acceptance relation of `def:cp4`(a) (for an upper block from `paperPrefixAccepted_inr_iff`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.BlockFrame Sarkozy.CancellationSteps
open Sarkozy.FirstStagePaper
open Sarkozy.PartVLaws (PaperBlockSpec UpperBlockInputs paperAtomMap blockPrimes)

/-- **Weakening the acceptance relation** of atom data (the prices are unchanged). -/
def AtomComparison.mono {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {lam : SlotMeasure X}
    {acc acc' : X → X → Prop} {E : Type} {Q : Queries E} (C : AtomComparison lam acc Q)
    (h : ∀ x y, acc x y → acc' x y) : AtomComparison lam acc' Q where
  I := C.I
  c := C.c
  w := C.w
  law := C.law
  w_pos := C.w_pos
  mass_pos := C.mass_pos
  accept i z hz e := h _ _ (C.accept i z hz e)
  unif := C.unif
  T := C.T
  Δ := C.Δ
  change := C.change
  D := C.D
  D_prob := C.D_prob
  D_diag := C.D_diag
  D_unif := C.D_unif
  πt := C.πt
  πt_nonneg := C.πt_nonneg
  bracket := C.bracket

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- The first-stage law `λ_𝔅 = ρ + δ_E` of a class-three block with specification `S` (A1's
`specStage`). -/
noncomputable abbrev specLam (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (S : PaperBlockSpec blockOf b) :
    SlotMeasure (BlockRes paperM0 (paperAtomMap blockOf) (.inr b)) :=
  (specStage hW In S).ρ + ∑ i, ((specStage hW In S).κ' i - (specStage hW In S).κ i)

omit [Fintype B] in
/-- On an upper block the first-stage law is the reference `μ_𝔅` (not a first-stage atom). -/
theorem specLam_upper (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (U : UpperBlockInputs blockOf b) :
    specLam hW In (.upper U) = signedIntegral ((PaperBlockSpec.upper U).toAtom hW).law.weight := by
  change signedIntegral _ + ∑ i : Empty, _ = _
  rw [Finset.univ_eq_empty, sum_empty, add_zero]

omit [Fintype B] in
/-- The labelling sets of an upper block are nonempty (under H1, `upperNonempty_explicit`). -/
theorem upperNe (hW : Target.Weil) {b : B} (U : UpperBlockInputs blockOf b) :
    PartV.UpperNonempty (blockPrimes blockOf b) :=
  PartVLaws.upperNonempty_explicit _
    (fun j => Labellings.weilBound_of_target hW _ (PartVLaws.blockPrimes_ne_two blockOf b U.hp j))
    U.hp

/-- **The (CP4) inputs of a class-three block, by its specification**: `UpperAtomInputs` on an upper
block (W8's construction), the atom data relative to A1's `λ_𝔅` on a middle block. -/
def BlockInputs (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B} :
    PaperBlockSpec blockOf b → Type 1
  | .upper U => ULift (UpperAtomInputs (blockPrimes blockOf b) (upperNe hW U) U.W U.r)
  | .middleUniform M => AtomComparison (specLam hW In (.middleUniform M))
      (prefixAccepted paperM0 (paperAtomMap blockOf) paperPP paperEP (.inr b))
      MainAnchor.paperQueries
  | .middleIndividual M => AtomComparison (specLam hW In (.middleIndividual M))
      (prefixAccepted paperM0 (paperAtomMap blockOf) paperPP paperEP (.inr b))
      MainAnchor.paperQueries
  | .middleCoherent M => AtomComparison (specLam hW In (.middleCoherent M))
      (prefixAccepted paperM0 (paperAtomMap blockOf) paperPP paperEP (.inr b))
      MainAnchor.paperQueries

omit [Fintype B] in
/-- The law of an upper block's atom is V1's `upperBlockReference`. -/
theorem upper_lam_eq (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (U : UpperBlockInputs blockOf b) :
    signedIntegral (PartV.upperBlockReference (blockPrimes blockOf b) (upperNe hW U) U.W
      U.hr.le).weight = specLam hW In (.upper U) := by
  rw [specLam_upper]
  rfl

/-- **The `AtomComparison` of a class-three block**, relative to `λ_𝔅`, from its inputs. -/
noncomputable def BlockInputs.toAtom (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B} :
    (S : PaperBlockSpec blockOf b) → BlockInputs hW In S →
      AtomComparison (specLam hW In S)
        (prefixAccepted paperM0 (paperAtomMap blockOf) paperPP paperEP (.inr b))
        MainAnchor.paperQueries
  | .upper U, D => ((UpperAtomInputs.toAtom D.down U.hr).mono
      (fun x y h => (paperPrefixAccepted_inr_iff blockOf x y).mpr h)).congrLam
        (upper_lam_eq hW In U)
  | .middleUniform _, C => C
  | .middleIndividual _, C => C
  | .middleCoherent _, C => C

end Sarkozy.ComparisonLawPaper
