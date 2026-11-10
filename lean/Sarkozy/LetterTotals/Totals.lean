module

public import Sarkozy.LetterTotals.Split

@[expose] public section

/-!
# The symmetric and the skew formal totals, bounded apart (HX)

HX, 8 November 2026. Continuation of `Split.lean`: the upper blocks by bands per change type, and
the two totals of the comparison law at every scale.

* `upper_sum_le` (B2's `upper_blocks_le_of_bands` for one price function, `thm:bmor`), and
  **`upper_parts_le`**: `∑_{𝔅 upper} s_𝔅 ≤ upperS`, `∑_{𝔅 upper} a_𝔅 ≤ upperA`
  (`prop:record:upper`(ii), W8's ledger at the band weights, the band charges `bandBound a_T`);
* `upperS_add_upperA`: `upperS + upperA = Uup` (the upper term of `hSA`);
* **`symTotal_le`**: `∑_𝔟 s_𝔟 ≤ H + upperS + middleS κ + S_tail` at every scale `L`;
* **`skewTotal_le`**: `∑_𝔟 a_𝔟 ≤ H + upperA + middleA κ + A_tail` at every scale `L`.

The hypotheses are those of K1's `SAExplicit_fullF1` without its numerical inequality: the clique
bound, the upper per-record bounds `UpperRecs`, the middle norm sizes `MiddleNorms`, and
nonnegative piece constants. The tail atoms enter through the fields `tail_S`, `tail_A` of the
comparison law (its totals `S`, `A`, `comparisonLawTarget_S`, `_A`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.LetterTotals

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec paperAtomMap PaperAtom PrefixCoord)
open Sarkozy.UpperComparison (upperFate upperLedger polyEval upperDegrees band_sum_le)
open Sarkozy.ComparisonLawPaper (BlockInputs specUpper upperBand blockSel)
open Sarkozy.MainFinal (MiddleConsts specUpper_prices_le)
open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk bandIdx paperSpec_upper_facts
  blockSite_of_upper upperBand_le_bandBound)
open Sarkozy.NumericalFields (KappaNonneg bandBound)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.EnvPrefix (Uup)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-! ## The upper blocks, per change type -/

/-- The symmetric upper total `∑_β ∑_d c^s_{β,d} 𝒰_{β,d}` at W8's ledger and the band charges
`bandBound a_T`. -/
noncomputable def upperS (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) : ℝ :=
  ∑ β, ∑ d ∈ upperDegrees,
    (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
      bandBound targetDecay d β

/-- The skew upper total `∑_β ∑_d c^a_{β,d} 𝒰_{β,d}`. -/
noncomputable def upperA (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) : ℝ :=
  ∑ β, ∑ d ∈ upperDegrees,
    (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
      bandBound targetDecay d β

/-- The two upper totals add up to `Uup`, the upper term of `hSA`'s numerical inequality. -/
theorem upperS_add_upperA (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) :
    upperS Cs Ca hCs hCa + upperA Cs Ca hCs hCa = Uup Cs Ca hCs hCa := by
  unfold upperS upperA Uup
  rw [← sum_add_distrib]
  refine sum_congr rfl fun β _ => ?_
  rw [← sum_add_distrib]

/-- **The upper blocks by bands, for one price function** (B2's `upper_blocks_le_of_bands` for a
single price, with E2's band charges from `thm:bmor`). -/
theorem upper_sum_le (hB : Target.BMOR) (f : Blk → ℝ) (c : Fin 310 → ℕ → ℝ)
    (hc : ∀ β, ∀ d ∈ upperDegrees, 0 ≤ c β d)
    (hf : ∀ b, specUpper (specF hW A b) = true →
      f b ≤ polyEval (c (bandIdx b)) (BlockSpecPaper.blockScale b) * blockSel bOf b) :
    ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), f b ≤
      ∑ β, ∑ d ∈ upperDegrees, c β d * bandBound targetDecay d β := by
  rw [← sum_fiberwise_of_maps_to (g := bandIdx) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_le_sum fun β _ => ?_
  refine band_sum_le (upperBand (specF hW A) bandIdx β) BlockSpecPaper.blockScale (blockSel bOf)
    f (c β) (fun d => bandBound targetDecay d β) (hc β)
    (fun d _ => upperBand_le_bandBound hB hW A β d) (fun b hb => ?_)
  unfold ComparisonLawPaper.upperBand at hb
  rw [mem_filter, mem_filter] at hb
  have := hf b hb.1.2
  rwa [hb.2] at this

/-- **`prop:record:upper`(ii) per change type**: `∑_{𝔅 upper} s_𝔅 ≤ upperS` and
`∑_{𝔅 upper} a_𝔅 ≤ upperA`, from the per-record bounds `UpperRecs` (K1's `specUpper_prices_le`)
and the band charges of `thm:bmor`. -/
theorem upper_parts_le (hB : Target.BMOR) (C : ComparisonParts hW hMR hFour A)
    (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i)
    (hR : C.UpperRecs hW A Cs Ca hCs hCa) :
    ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true),
        (C.Ci.blockAtom b).sprice (blockSel bOf b) ≤ upperS Cs Ca hCs hCa ∧
      ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true),
        (C.Ci.blockAtom b).aprice (blockSel bOf b) ≤ upperA Cs Ca hCs hCa := by
  have hsel : ∀ b : Blk, 0 ≤ blockSel bOf b := fun b =>
    le_trans zero_le_one (one_le_paperSelAt (paperAtomMap bOf) targetDecay_nonneg _)
  have hP : ∀ b, specUpper (specF hW A b) = true →
      (C.Ci.blockAtom b).sprice (blockSel bOf b) ≤
          polyEval (upperLedger (UpperRecords.bandWeights (bandIdx b))
            (Cs (bandIdx b)) (Ca (bandIdx b)) (hCs (bandIdx b)) (hCa (bandIdx b))).coefS
            (BlockSpecPaper.blockScale b) * blockSel bOf b ∧
        (C.Ci.blockAtom b).aprice (blockSel bOf b) ≤
          polyEval (upperLedger (UpperRecords.bandWeights (bandIdx b))
            (Cs (bandIdx b)) (Ca (bandIdx b)) (hCs (bandIdx b)) (hCa (bandIdx b))).coefA
            (BlockSpecPaper.blockScale b) * blockSel bOf b := by
    intro b hb
    have hs := blockSite_of_upper b hb
    obtain ⟨eS, eA, eR⟩ := paperSpec_upper_facts hW A b (bandIdx b) hs (Cs (bandIdx b))
      (Ca (bandIdx b)) (hCs (bandIdx b)) (hCa (bandIdx b))
    have h := specUpper_prices_le hW (paperIn f1Cell) (Cs (bandIdx b)) (Ca (bandIdx b))
      (hCs (bandIdx b)) (hCa (bandIdx b)) (hsel b) (specF hW A b) (C.blk b) hb
      (hR b (bandIdx b) hs)
    rw [eS, eA, eR] at h
    exact h
  exact ⟨upper_sum_le hB _ _ (fun β d _ => UpperComparison.RecordLedger.coefS_nonneg _ d)
      fun b hb => (hP b hb).1,
    upper_sum_le hB _ _ (fun β d _ => UpperComparison.RecordLedger.coefA_nonneg _ d)
      fun b hb => (hP b hb).2⟩

/-! ## The two totals of the comparison law -/

/-- The prefix atoms' selection factors are nonnegative. -/
theorem sel_nonneg (β : PaperAtom Blk) : 0 ≤ paperSelAt (paperAtomMap bOf) targetDecay β :=
  le_trans zero_le_one (one_le_paperSelAt (paperAtomMap bOf) targetDecay_nonneg _)

/-- **The symmetric formal total, bounded alone** (`def:cp4`(b), `def:closing-quantities`): at
every scale, `∑_𝔟 s_𝔟 ≤ H + upperS + middleS κ + S_tail`. -/
theorem symTotal_le (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (C : ComparisonParts hW hMR hFour A) {H : ℝ} (hq : ∑ q, C.Ci.cliquePrice q ≤ H)
    (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i)
    (hR : C.UpperRecs hW A Cs Ca hCs hCa) (κ : Fin 33 → MiddleConsts)
    (hκ : ∀ i, KappaNonneg (κ i)) (hN : C.MiddleNorms hW A κ) (L : ℕ) :
    ∑ b, symTotal (C.CL.π L) b ≤ H + upperS Cs Ca hCs hCa + middleS κ + C.Ci.St := by
  have h1 : ∑ b, symTotal (C.CL.π L) b ≤ C.CL.S := C.CL.S_total L
  have h2 : C.CL.S = ∑ β, (C.Ci.pre β).sprice (paperSelAt (paperAtomMap bOf) targetDecay β) +
      C.Ci.St := ComparisonLawPaper.comparisonLawTarget_S _ _ _ _ _
  have hcl : ∀ q : PrefixCoord,
      (C.Ci.pre (.inl q)).sprice (paperSelAt (paperAtomMap bOf) targetDecay (.inl q)) ≤
        C.Ci.cliquePrice q := fun q => by
    have e := MainFinalF1.pre_price_clique C q
    have := (C.Ci.pre (.inl q)).aprice_nonneg (sel_nonneg (.inl q))
    linarith
  have hup := (upper_parts_le hB C Cs Ca hCs hCa hR).1
  have hmid := middle_sprice_le hB hRR C κ hκ hN
  have hsplit := sum_filter_add_sum_filter_not univ (fun b => specUpper (specF hW A b) = true)
    (fun b => (C.Ci.blockAtom b).sprice (blockSel bOf b))
  have hblk : ∑ b : Blk, (C.Ci.pre (.inr b)).sprice
      (paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) =
      ∑ b : Blk, (C.Ci.blockAtom b).sprice (blockSel bOf b) := rfl
  have h3 : ∑ β : PaperAtom Blk, (C.Ci.pre β).sprice (paperSelAt (paperAtomMap bOf) targetDecay β) =
      ∑ q : PrefixCoord, (C.Ci.pre (.inl q)).sprice
          (paperSelAt (paperAtomMap bOf) targetDecay (.inl q)) +
        ∑ b : Blk, (C.Ci.pre (.inr b)).sprice
          (paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) :=
    Fintype.sum_sum_type _
  rw [h2, h3, hblk, ← hsplit] at h1
  have := sum_le_sum fun q (_ : q ∈ (univ : Finset PrefixCoord)) => hcl q
  linarith

/-- **The skew formal total, bounded alone**: at every scale,
`∑_𝔟 a_𝔟 ≤ H + upperA + middleA κ + A_tail`. -/
theorem skewTotal_le (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (C : ComparisonParts hW hMR hFour A) {H : ℝ} (hq : ∑ q, C.Ci.cliquePrice q ≤ H)
    (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i)
    (hR : C.UpperRecs hW A Cs Ca hCs hCa) (κ : Fin 33 → MiddleConsts)
    (hκ : ∀ i, KappaNonneg (κ i)) (hN : C.MiddleNorms hW A κ) (L : ℕ) :
    ∑ b, skewTotal (C.CL.π L) b ≤ H + upperA Cs Ca hCs hCa + middleA κ + C.Ci.At := by
  have h1 : ∑ b, skewTotal (C.CL.π L) b ≤ C.CL.A := C.CL.A_total L
  have h2 : C.CL.A = ∑ β, (C.Ci.pre β).aprice (paperSelAt (paperAtomMap bOf) targetDecay β) +
      C.Ci.At := ComparisonLawPaper.comparisonLawTarget_A _ _ _ _ _
  have hcl : ∀ q : PrefixCoord,
      (C.Ci.pre (.inl q)).aprice (paperSelAt (paperAtomMap bOf) targetDecay (.inl q)) ≤
        C.Ci.cliquePrice q := fun q => by
    have e := MainFinalF1.pre_price_clique C q
    have := (C.Ci.pre (.inl q)).sprice_nonneg (sel_nonneg (.inl q))
    linarith
  have hup := (upper_parts_le hB C Cs Ca hCs hCa hR).2
  have hmid := middle_aprice_le hB hRR C κ hκ hN
  have hsplit := sum_filter_add_sum_filter_not univ (fun b => specUpper (specF hW A b) = true)
    (fun b => (C.Ci.blockAtom b).aprice (blockSel bOf b))
  have hblk : ∑ b : Blk, (C.Ci.pre (.inr b)).aprice
      (paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) =
      ∑ b : Blk, (C.Ci.blockAtom b).aprice (blockSel bOf b) := rfl
  have h3 : ∑ β : PaperAtom Blk, (C.Ci.pre β).aprice (paperSelAt (paperAtomMap bOf) targetDecay β) =
      ∑ q : PrefixCoord, (C.Ci.pre (.inl q)).aprice
          (paperSelAt (paperAtomMap bOf) targetDecay (.inl q)) +
        ∑ b : Blk, (C.Ci.pre (.inr b)).aprice
          (paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) :=
    Fintype.sum_sum_type _
  rw [h2, h3, hblk, ← hsplit] at h1
  have := sum_le_sum fun q (_ : q ∈ (univ : Finset PrefixCoord)) => hcl q
  linarith

end Sarkozy.LetterTotals
