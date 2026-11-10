module

public import Sarkozy.MainFinalF1.K3
public import Sarkozy.EnvPrefix.All

@[expose] public section

/-!
# `EnvPrefix`'s layer at `f1Cell` (F1P)

`EnvPrefix/Prices.lean` and the block-data part of `EnvPrefix/Main.lean` with `paperCell` replaced
by `f1Cell`: the prefix prices (`pre_total`, `pre_price_clique`, `pre_price_block`), (CP8)(c) at
the prefix atoms proved (`σpreOf`, `hCLpre_proved`), the upper blocks' price from `thm:bmor`
(`upper_price_le`, through `upperBand_le_bandBound` at `f1Cell`), `midOthers`, `hothT_of_mid`
(`prop:record:matching`(ii), `def:cp6`, `def:cp8`(c)), `envOf`, `FinalBlockData3b` and its `toMF3`
map. `EnvPrefix.Uup` is partition-independent and reused. Every proof is verbatim up to the cell.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperAtom paperAtomMap PrefixCoord)
open Sarkozy.ComparisonLawPaper (specUpper)
open Sarkozy.MainFinal (PrimeCertificates BlockAnalytic hCF)
open Sarkozy.MainFinal2 (PrimeCertificates2 MidRefinement)
open Sarkozy.EnvPrefix (Uup)
open Sarkozy.AnalyticCells (f1Cell)

section Prices

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}


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

/-- **The upper blocks' (CP4) price** from the per-record bounds and `thm:bmor`
(`prop:record:upper`(ii); K1's `upper_le`, E2's `upperBand_le_bandBound`). -/
theorem upper_price_le (hB : Target.BMOR) (C : ComparisonParts hW hMR hFour A)
    (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i)
    (hR : C.UpperRecs hW A Cs Ca hCs hCa) :
    ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), C.Ci.blockPrice b ≤
      Uup Cs Ca hCs hCa :=
  C.upper_le Cs Ca hCs hCa hR (fun β d => NumericalFields.bandBound targetDecay d β)
    (fun β d => NumericalFields.bandBound targetDecay d β)
    (fun β d _ => upperBand_le_bandBound hB hW A β d)
    (fun β d _ => upperBand_le_bandBound hB hW A β d)

/-- The middle part of `hothT`: the records not replaced at the middle blocks. -/
noncomputable def midOthers (C : ComparisonParts2 hW hMR hFour A)
    (MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn f1Cell) (paperGi hW A)) C.toK1.CL (fun β => midAtom hW A β = true))
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
      (paperIn f1Cell) (paperGi hW A)) C.toK1.CL (fun β => midAtom hW A β = true))
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

end Prices

/-! ## The block data (`EnvPrefix/Main.lean`) -/

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **E2's `EnvelopePartsE2` from the middle part** (`hothT_of_mid`, `hCLpre_proved`). -/
noncomputable def envOf (hB : Target.BMOR) {A : PaperAnalyticInputs f1Cell}
    (C : ComparisonParts3 hW hMR hFour A)
    (MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn f1Cell) (paperGi hW A)) C.toK2.toK1.CL (fun β => midAtom hW A β = true))
    (S : SAParts3 hW hMR hFour A C)
    (hmid : ∀ L, midOthers C.toK2 MR L + max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup S.Cs S.Ca S.hCs S.hCa + 11 / 10 ^ 70) ≤ targetLedger.T) :
    EnvelopePartsE2 hW hMR hFour A C.toK2 where
  MR := MR
  hothT := hothT_of_mid hB C.toK2 C.cliquePrice_le MR S.Cs S.Ca S.hCs S.hCa S.hR hmid
  σpre := σpreOf C.toK2.toK1
  hCLpre := hCLpre_proved C.toK2.toK1

/-- **The block data with the prefix parts of (CP6), (CP8)(c) reduced.** 4 fields. -/
structure FinalBlockData3b (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs (as in `MainFinal3`). -/
  Cmp : ComparisonParts3 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The prefix refinement on the middle blocks (`prop:record:matching`(i), `prop:signed-sides`;
  K2's `MR`). *Open*. -/
  MR : MidRefinement
    (gramBracketTarget bOf hW (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA))
      (hCF hW hMR hFour) (paperIn f1Cell)
      (paperGi hW (analyticInputs (PC.toPC hW hMR hFour) BA)))
    Cmp.toK2.toK1.CL (fun β => midAtom hW (analyticInputs (PC.toPC hW hMR hFour) BA) β = true)

/-- `MainFinal3`'s block data (E2's (CP6) inputs by `envOf`). -/
noncomputable def FinalBlockData3b.toMF3 (hB : Target.BMOR) (D : FinalBlockData3b hW hMR hFour)
    (S : SAParts3 hW hMR hFour (analyticInputs (D.PC.toPC hW hMR hFour) D.BA) D.Cmp)
    (hmid : ∀ L, midOthers D.Cmp.toK2 D.MR L +
      max (∑ β, D.MR.toPrefix.KL β) (∑ β, D.MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup S.Cs S.Ca S.hCs S.hCa + 11 / 10 ^ 70) ≤ targetLedger.T) :
    FinalBlockData3 hW hMR hFour where
  PC := D.PC
  BA := D.BA
  Cmp := D.Cmp
  Env := envOf hB D.Cmp D.MR S hmid


end Sarkozy.MainFinalF1
