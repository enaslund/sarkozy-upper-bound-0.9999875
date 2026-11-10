module

public import Sarkozy.MainFinal3.Main

@[expose] public section

/-!
# The prefix sums of (CP6) and (CP8)(c), split by atom type

`paper/sections/24_matching_mean.tex`, `prop:record:matching`(ii) and "The matching exponent";
`def:cp8`(c); `lem:frontier:iidenergy`(ii),(iii); `prop:record:upper`(ii).

E2's `EnvelopePartsE2` has two sums over the prefix atoms `β ∈ PrefixCoord ⊕ Blk` (square-clique
atoms, then class-three blocks, upper or middle):

* `hothT`: the records not replaced at the prefix atoms, plus `T_K`, plus `11/10⁷⁰`, fit in `T`;
* `hCLpre`: `∑_β q_β^{1/4}(s_β + a_β) ≤ σ_pre` at every scale.

This file:

* `pre_total`: at a prefix atom and **every scale**, `s_β + a_β` is the atom's own price
  `(Ci.pre β).sprice + (Ci.pre β).aprice` at `paperSelAt · a_T`, which does not depend on the
  scale; `pre_total_clique` (`= λ^ex_p(1) q_p^{2a}`), `pre_total_block`.
* **`hCLpre_proved`**: `hCLpre` holds with `σ_pre := σpreOf C`, the scale-independent weighted
  prefix price (the weights `q_β = oneWeight` do not depend on the scale either). All three atom
  types are covered: (CP8)(c) asks only for a bound uniform in the scale, and the prefix is a fixed
  finite set of atoms with fixed prices. No numerical value of `σ_pre` is used downstream
  (`EnvelopesPaper.summabilityOf` only adds it to the bound of (CP8)(c)).
* **`hothT_of_mid`**: `hothT` from
  - the clique part, `∑_p λ^ex_p(1) q_p^{2a} ≤ 12/2^{534}` (C10; nothing is replaced at a
    square-clique atom, K2's `toPrefix_repl_off`);
  - the upper part, `∑_{𝔅 upper}(s_𝔅 + a_𝔅) ≤ Uup` (nothing is replaced at an upper block): K1's
    `upper_le` from the per-record bounds `SA.hR` (`UpperRecs`) and E2's band charges
    `bandBound a_T` from `thm:bmor`, with `Uup` the explicit band sum that also occurs in `SA.hsum`;
  - the middle part, the one remaining input `hmid`: the records not replaced at the middle
    blocks, plus `T_K`, plus the numbers `12/2^{534} + Uup + 11/10⁷⁰`, fit in `T`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvPrefix

open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperAtom paperAtomMap PrefixCoord)
open Sarkozy.ComparisonLawPaper (specUpper)
open Sarkozy.PaperNumbers (paperCell)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs paperCell}

/-! ## The prefix prices do not depend on the scale -/

/-- **At a prefix atom, `s_β + a_β` at every scale is the atom's own price** (`def:cp4`(b): the
prices `π̃ q_β^{2a}` of B2's per-atom data `Ci.pre β`). -/
theorem pre_total (C : ComparisonParts hW hMR hFour A) (L : ℕ) (β : PaperAtom Blk) :
    symTotal (C.CL.π L) (.inl β) + skewTotal (C.CL.π L) (.inl β) =
      (C.Ci.pre β).sprice (paperSelAt (paperAtomMap bOf) targetDecay β) +
        (C.Ci.pre β).aprice (paperSelAt (paperAtomMap bOf) targetDecay β) := by
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  rfl

/-- At a square-clique atom: `s_p + a_p = λ^ex_p(1) q_p^{2a}` (`lem:frontier:iidenergy`(ii)). -/
theorem pre_price_clique (C : ComparisonParts hW hMR hFour A) (q : PrefixCoord) :
    (C.Ci.pre (.inl q)).sprice (paperSelAt (paperAtomMap bOf) targetDecay (.inl q)) +
      (C.Ci.pre (.inl q)).aprice (paperSelAt (paperAtomMap bOf) targetDecay (.inl q)) =
      C.Ci.cliquePrice q := by
  unfold ComparisonLawPaper.ComparisonInputs.pre
  rw [ComparisonLawPaper.AtomComparison.congrLam_sprice,
    ComparisonLawPaper.AtomComparison.congrLam_aprice,
    ComparisonLawPaper.DeletionInputs.toAtom_sprice,
    ComparisonLawPaper.DeletionInputs.toAtom_aprice, add_zero]
  rfl

/-- At a class-three block: `s_𝔅 + a_𝔅` is B2's `blockPrice`. -/
theorem pre_price_block (C : ComparisonParts hW hMR hFour A) (b : Blk) :
    (C.Ci.pre (.inr b)).sprice (paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) +
      (C.Ci.pre (.inr b)).aprice (paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) =
      C.Ci.blockPrice b := rfl

/-! ## (CP8)(c) at the prefix atoms -/

/-- **The weighted prefix price** `∑_β q_β^{1/4}(s_β + a_β)`, at the scale-independent prices. -/
noncomputable def σpreOf (C : ComparisonParts hW hMR hFour A) : ℝ :=
  ∑ β : PaperAtom Blk, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP 0
      (.inl β) ^ ((1 : ℝ) / 4) *
    ((C.Ci.pre β).sprice (paperSelAt (paperAtomMap bOf) targetDecay β) +
      (C.Ci.pre β).aprice (paperSelAt (paperAtomMap bOf) targetDecay β))

/-- **(CP8)(c) at the prefix atoms, proved** (`def:cp8`(c)): at every scale the weighted (CP4)
price of the prefix atoms equals `σpreOf C`; the prefix atoms, their weights `q_β` and their
prices do not depend on the scale. -/
theorem hCLpre_proved (C : ComparisonParts hW hMR hFour A) (L : ℕ) :
    ∑ β, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L
        (.inl β) ^ ((1 : ℝ) / 4) *
      (symTotal (C.CL.π L) (.inl β) + skewTotal (C.CL.π L) (.inl β)) ≤ σpreOf C := by
  refine le_of_eq (Finset.sum_congr rfl fun β _ => ?_)
  rw [pre_total C L β]
  rfl

/-! ## (CP6) at the prefix atoms -/

/-- **The upper band sum** `∑_β ∑_d (c^s_{β,d} + c^a_{β,d}) 𝒰_{β,d}` at E2's band charges
`𝒰 = bandBound a_T` (the term of `SA.hsum` for the upper blocks). -/
noncomputable def Uup (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) : ℝ :=
  ∑ β, ∑ d ∈ upperDegrees,
    ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
        NumericalFields.bandBound targetDecay d β +
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
        NumericalFields.bandBound targetDecay d β)

/-- **The upper blocks' (CP4) price** from the per-record bounds and `thm:bmor`
(`prop:record:upper`(ii); K1's `upper_le`, E2's `upperBand_le_bandBound`). -/
theorem upper_price_le (hB : Target.BMOR) (C : ComparisonParts hW hMR hFour A)
    (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i)
    (hR : C.UpperRecs hW A Cs Ca hCs hCa) :
    ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), C.Ci.blockPrice b ≤
      Uup Cs Ca hCs hCa :=
  C.upper_le Cs Ca hCs hCa hR (fun β d => NumericalFields.bandBound targetDecay d β)
    (fun β d => NumericalFields.bandBound targetDecay d β)
    (fun β d _ => NumericalFields.upperBand_le_bandBound hB hW A β d)
    (fun β d _ => NumericalFields.upperBand_le_bandBound hB hW A β d)

/-- The middle part of `hothT`: the records not replaced at the middle blocks. -/
noncomputable def midOthers (C : ComparisonParts2 hW hMR hFour A)
    (MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn paperCell) (paperGi hW A)) C.toK1.CL (fun β => midAtom hW A β = true))
    (L : ℕ) : ℝ :=
  ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = false),
    ∑ t ∈ univ \ MR.toPrefix.repl L (.inl (.inr b)),
      (C.toK1.CL.π L (.inl (.inr b)) t .sym + C.toK1.CL.π L (.inl (.inr b)) t .skew)

/-- **E2's `hothT` from its middle part** (`prop:record:matching`(ii), "The matching exponent"):
the square-clique atoms (C10's bound `12/2^{534}`) and the upper blocks (`upper_price_le`) are
proved; nothing is replaced there (`toPrefix_repl_off`). -/
theorem hothT_of_mid (hB : Target.BMOR) (C : ComparisonParts2 hW hMR hFour A)
    (hq : ∑ q, C.toK1.Ci.cliquePrice q ≤ 12 / 2 ^ 534)
    (MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn paperCell) (paperGi hW A)) C.toK1.CL (fun β => midAtom hW A β = true))
    (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i)
    (hR : C.toK1.UpperRecs hW A Cs Ca hCs hCa)
    (hmid : ∀ L, midOthers C MR L + max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup Cs Ca hCs hCa + 11 / 10 ^ 70) ≤ targetLedger.T) (L : ℕ) :
    (∑ β, ∑ t ∈ univ \ MR.toPrefix.repl L (.inl β),
      (C.toK1.CL.π L (.inl β) t .sym + C.toK1.CL.π L (.inl β) t .skew)) +
        max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β) + 11 / 10 ^ 70 ≤
      targetLedger.T := by
  -- at an atom where nothing is replaced, the sum is the full price
  have hfull : ∀ β : PaperAtom Blk, midAtom hW A β = false →
      ∑ t ∈ univ \ MR.toPrefix.repl L (.inl β),
        (C.toK1.CL.π L (.inl β) t .sym + C.toK1.CL.π L (.inl β) t .skew) =
      (C.toK1.Ci.pre β).sprice (paperSelAt (paperAtomMap bOf) targetDecay β) +
        (C.toK1.Ci.pre β).aprice (paperSelAt (paperAtomMap bOf) targetDecay β) := by
    intro β hβ
    rw [MidRefinement.toPrefix_repl_off MR L β (by rw [hβ]; decide), sdiff_empty,
      sum_add_distrib]
    exact pre_total C.toK1 L β
  have hcl : ∑ q : PrefixCoord, ∑ t ∈ univ \ MR.toPrefix.repl L (.inl (.inl q)),
      (C.toK1.CL.π L (.inl (.inl q)) t .sym + C.toK1.CL.π L (.inl (.inl q)) t .skew) =
      ∑ q, C.toK1.Ci.cliquePrice q :=
    sum_congr rfl fun q _ => (hfull (.inl q) rfl).trans (pre_price_clique C.toK1 q)
  have hsplit : ∑ b : Blk, ∑ t ∈ univ \ MR.toPrefix.repl L (.inl (.inr b)),
      (C.toK1.CL.π L (.inl (.inr b)) t .sym + C.toK1.CL.π L (.inl (.inr b)) t .skew) =
      ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), C.toK1.Ci.blockPrice b +
        midOthers C MR L := by
    rw [← sum_filter_add_sum_filter_not univ (fun b => specUpper (specF hW A b) = true)]
    refine congrArg₂ (· + ·) (sum_congr rfl fun b hb => ?_) ?_
    · have hu := (mem_filter.mp hb).2
      refine (hfull (.inr b) ?_).trans (pre_price_block C.toK1 b)
      simp only [midAtom, hu, Bool.not_true]
    · unfold midOthers
      refine sum_congr (filter_congr fun b _ => ?_) fun _ _ => rfl
      simp only [Bool.not_eq_true]
  have hup := upper_price_le hB C.toK1 Cs Ca hCs hCa hR
  rw [Fintype.sum_sum_type, hcl, hsplit]
  have := hmid L
  generalize (12 : ℝ) / 2 ^ 534 = c at hq this
  linarith

end Sarkozy.EnvPrefix
