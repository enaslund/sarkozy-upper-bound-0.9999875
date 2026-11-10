module

public import Sarkozy.MainFinal.MiddlePrices

@[expose] public section





open Finset
open scoped BigOperators

namespace Sarkozy.MainFinal

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec paperAtomMap)
open Sarkozy.UpperComparison (upperFate upperLedger polyEval upperDegrees)
open Sarkozy.MiddleComparison (SpecData SpecInputs)
open Sarkozy.ComparisonLawPaper (BlockInputs specUpper SAExplicit upperBand blockSel)

/-! ## Any block specification -/

/-- The prices are unchanged by weakening the acceptance relation. -/
theorem mono_sprice {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {lam : SlotMeasure X}
    {acc acc' : X → X → Prop} {E : Type} {Q : Queries E}
    (C : ComparisonLawPaper.AtomComparison lam acc Q) (h : ∀ x y, acc x y → acc' x y) (sel : ℝ) :
    (C.mono h).sprice sel = C.sprice sel := rfl

/-- The prices are unchanged by weakening the acceptance relation. -/
theorem mono_aprice {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {lam : SlotMeasure X}
    {acc acc' : X → X → Prop} {E : Type} {Q : Queries E}
    (C : ComparisonLawPaper.AtomComparison lam acc Q) (h : ∀ x y, acc x y → acc' x y) (sel : ℝ) :
    (C.mono h).aprice sel = C.aprice sel := rfl

section Generic

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B} (hW : Target.Weil)
  (In : FirstStageInputs blockOf)

/-- **The per-record bounds of an upper block** (`prop:record:upper`(i)): every changed record
`ρ` has `π^s_ρ ≤ C^s_ρ(r)/P_μ(r)` and `π^a_ρ ≤ C^a_ρ(r)/P_μ(r)`, with W8's ledger at the block's
weights and the record coefficients `Cs`, `Ca` (`True` on a middle block). *Hypothesis*
(analytic: `prop:forest-records`, `prop:dense-comparison`(b), `prop:le-mixture`). -/
def SpecUpperRec {b : B} (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i) :
    (S : PaperBlockSpec blockOf b) → SpecData hW In S → Prop
  | .upper U, D =>
    (∀ ρ, upperFate ρ = .changed →
      D.down.π ρ .sym ≤ (upperLedger U.W Cs Ca hCs hCa).symCoef U.r ρ / upPoly U.W U.r) ∧
    (∀ ρ, upperFate ρ = .changed →
      D.down.π ρ .skew ≤ (upperLedger U.W Cs Ca hCs hCa).skewCoef U.r ρ / upPoly U.W U.r)
  | .middleUniform _, _ => True
  | .middleIndividual _, _ => True
  | .middleCoherent _, _ => True

variable {hW In}

/-- W8's symmetric ledger coefficients of an upper specification (`0` on a middle block). -/
noncomputable def specCoefS {b : B} (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i)
    (hCa : ∀ i, 0 ≤ Ca i) : PaperBlockSpec blockOf b → ℕ → ℝ
  | .upper U => (upperLedger U.W Cs Ca hCs hCa).coefS
  | .middleUniform _ => fun _ => 0
  | .middleIndividual _ => fun _ => 0
  | .middleCoherent _ => fun _ => 0

/-- W8's skew ledger coefficients of an upper specification (`0` on a middle block). -/
noncomputable def specCoefA {b : B} (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i)
    (hCa : ∀ i, 0 ≤ Ca i) : PaperBlockSpec blockOf b → ℕ → ℝ
  | .upper U => (upperLedger U.W Cs Ca hCs hCa).coefA
  | .middleUniform _ => fun _ => 0
  | .middleIndividual _ => fun _ => 0
  | .middleCoherent _ => fun _ => 0

/-- The scale of an upper specification (`0` on a middle block). -/
noncomputable def specR {b : B} : PaperBlockSpec blockOf b → ℝ
  | .upper U => U.r
  | .middleUniform _ => 0
  | .middleIndividual _ => 0
  | .middleCoherent _ => 0

omit [Fintype B] in
variable (hW In) in
/-- The symmetric price of an upper block's atom is that of B2's `UpperAtomInputs.toAtom`. -/
theorem upper_sprice_eq {b : B} (U : PartVLaws.UpperBlockInputs blockOf b)
    (D : SpecData hW In (.upper U)) (sel : ℝ) :
    (BlockInputs.toAtom hW In (.upper U) (SpecInputs.toBlockInputs hW In (.upper U)
      (SpecData.toSpecInputs hW In (.upper U) D))).sprice sel =
      (D.down.toAtom U.hr).sprice sel :=
  (ComparisonLawPaper.AtomComparison.congrLam_sprice _ (ComparisonLawPaper.upper_lam_eq hW In U)
    sel).trans (mono_sprice _ _ sel)

omit [Fintype B] in
variable (hW In) in
/-- The skew price of an upper block's atom is that of B2's `UpperAtomInputs.toAtom`. -/
theorem upper_aprice_eq {b : B} (U : PartVLaws.UpperBlockInputs blockOf b)
    (D : SpecData hW In (.upper U)) (sel : ℝ) :
    (BlockInputs.toAtom hW In (.upper U) (SpecInputs.toBlockInputs hW In (.upper U)
      (SpecData.toSpecInputs hW In (.upper U) D))).aprice sel =
      (D.down.toAtom U.hr).aprice sel :=
  (ComparisonLawPaper.AtomComparison.congrLam_aprice _ (ComparisonLawPaper.upper_lam_eq hW In U)
    sel).trans (mono_aprice _ _ sel)

omit [Fintype B] in
variable (hW In) in
/-- **`prop:record:upper`(i) for an upper block of any specification**: the per-record bounds give
the ledger polynomials (B2's `prices_le_poly`). -/
theorem specUpper_prices_le {b : B} (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i)
    (hCa : ∀ i, 0 ≤ Ca i) {sel : ℝ} (hsel : 0 ≤ sel) :
    ∀ (S : PaperBlockSpec blockOf b) (R : SpecData hW In S), specUpper S = true →
      SpecUpperRec hW In Cs Ca hCs hCa S R →
      (BlockInputs.toAtom hW In S (SpecInputs.toBlockInputs hW In S
          (SpecData.toSpecInputs hW In S R))).sprice sel ≤
          polyEval (specCoefS Cs Ca hCs hCa S) (specR S) * sel ∧
        (BlockInputs.toAtom hW In S (SpecInputs.toBlockInputs hW In S
          (SpecData.toSpecInputs hW In S R))).aprice sel ≤
          polyEval (specCoefA Cs Ca hCs hCa S) (specR S) * sel
  | .upper U, D, _, ⟨hs, ha⟩ => by
    have h := D.down.prices_le_poly U.hr Cs Ca hCs hCa hs ha hsel
    exact ⟨(upper_sprice_eq hW In U D sel).trans_le h.1,
      (upper_aprice_eq hW In U D sel).trans_le h.2⟩
  | .middleUniform _, _, h, _ => (Bool.false_ne_true h).elim
  | .middleIndividual _, _, h, _ => (Bool.false_ne_true h).elim
  | .middleCoherent _, _, h, _ => (Bool.false_ne_true h).elim

end Generic

/-! ## The paper's blocks -/

section Paper

open Sarkozy.PaperNumbers (paperCell)

/-- The band of a block (`0` for a block of a middle piece, which is never used). -/
noncomputable def bandIdx (b : Blk) : Fin 310 :=
  match blockSite b with
  | .inr k => k
  | .inl _ => 0

variable (hW : Target.Weil) (A : PaperAnalyticInputs paperCell)

theorem siteSpec_upper_facts (b : Blk) (k : Fin 310) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i)
    (hCa : ∀ i, 0 ≤ Ca i) : ∀ s (hs : blockSite b = s), s = .inr k →
      specCoefS Cs Ca hCs hCa (siteSpec hW A b s hs) =
        (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefS ∧
      specCoefA Cs Ca hCs hCa (siteSpec hW A b s hs) =
        (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefA ∧
      specR (siteSpec hW A b s hs) = BlockSpecPaper.blockScale b
  | .inr j, _, h => by
    obtain rfl : j = k := Sum.inr.inj h
    exact ⟨rfl, rfl, rfl⟩
  | .inl _, _, h => absurd h (by simp)

theorem paperSpec_upper_facts (b : Blk) (k : Fin 310) (hs : blockSite b = .inr k)
    (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i) :
    specCoefS Cs Ca hCs hCa (specF hW A b) =
        (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefS ∧
      specCoefA Cs Ca hCs hCa (specF hW A b) =
        (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefA ∧
      specR (specF hW A b) = BlockSpecPaper.blockScale b :=
  siteSpec_upper_facts hW A b k Cs Ca hCs hCa _ rfl hs

/-- **The per-record bounds of every upper block of the combined data**, with per-band record
coefficients `Cs k`, `Ca k`. *Hypothesis* (analytic, `prop:record:upper`(i)). -/
def ComparisonParts.UpperRecs {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) (Cs Ca : Fin 310 → UpIdx → ℝ)
    (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i) : Prop :=
  ∀ b k, blockSite b = .inr k →
    SpecUpperRec hW (paperIn paperCell) (Cs k) (Ca k) (hCs k) (hCa k) (specF hW A b) (C.blk b)

variable {hW A}

/-- A block whose specification is upper lies in a band. -/
theorem blockSite_of_upper (b : Blk) (hb : specUpper (specF hW A b) = true) :
    blockSite b = .inr (bandIdx b) := by
  unfold bandIdx
  rcases h : blockSite b with i | k
  · exact absurd hb (by rw [(paperSpec_facts hW A b i h ⟨0, 0, 0, 0, 0⟩ 0 0).1]; simp)
  · rfl

theorem ComparisonParts.upper_le {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) (Cs Ca : Fin 310 → UpIdx → ℝ)
    (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i) (hR : C.UpperRecs hW A Cs Ca hCs hCa)
    (US UA : Fin 310 → ℕ → ℝ)
    (hUS : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
      blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ US β d)
    (hUA : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
      blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ UA β d) :
    ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), C.Ci.blockPrice b ≤
      ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefS d * US β d +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefA d * UA β d) := by
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
    have h := specUpper_prices_le hW (paperIn paperCell) (Cs (bandIdx b)) (Ca (bandIdx b))
      (hCs (bandIdx b)) (hCa (bandIdx b)) (hsel b) (specF hW A b) (C.blk b) hb
      (hR b (bandIdx b) hs)
    rw [eS, eA, eR] at h
    exact h
  exact ComparisonLawPaper.upper_blocks_le_of_bands C.Ci bandIdx univ (fun _ _ => mem_univ _)
    BlockSpecPaper.blockScale
    (fun β => (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
      (hCa β)).coefS)
    (fun β => (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
      (hCa β)).coefA) US UA
    (fun β _ d _ => UpperComparison.RecordLedger.coefS_nonneg _ d)
    (fun β _ d _ => UpperComparison.RecordLedger.coefA_nonneg _ d)
    (fun β _ => hUS β) (fun β _ => hUA β) (fun b hb => (hP b hb).1) (fun b hb => (hP b hb).2)

/-- **`hSA` in explicit form, every range reduced** (`def:closing-quantities`, `def:cp4`(b);
`lem:frontier:iidenergy`(iii), `prop:record:upper`(i),(ii), `lem:middle-comparison-prices`,
`lem:record:block-charge`, `lem:tail-prices`(iv)): B2's `SAExplicit` for the combined data from
* the square-clique bound `∑_p λ^ex_p(1) q_p^{2a} ≤ H` (*analytic*);
* the per-record bounds of the upper blocks (`UpperRecs`, *analytic*) with per-band record
  coefficients, and the band charges `𝒰^s`, `𝒰^a` (*numerical*);
* the norm sizes of the middle blocks (`MiddleNorms`, *analytic*) with the piece constants `κ`,
  N1's 66 certificates (through H2) and the signs of `K_d(i)` (*numerical*);
* the numerical inequality `H + ∑_β ∑_d (c^s 𝒰^s + c^a 𝒰^a) + ∑_i (K₂ c₂ + (K₃ + K₄ X_i^{-1/2} +
  K₅ X_i^{-1}) c₃) + S_tail + A_tail ≤ S^{ledger} + A^{ledger}`. -/
theorem ComparisonParts.SAExplicit_full (hBMOR : Target.BMOR) (NC : NumericalCertificates)
    {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) {H : ℝ} (hq : ∑ q, C.Ci.cliquePrice q ≤ H)
    (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i)
    (hR : C.UpperRecs hW A Cs Ca hCs hCa) (US UA : Fin 310 → ℕ → ℝ)
    (hUS : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
      blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ US β d)
    (hUA : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
      blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ UA β d)
    (κ : Fin 33 → MiddleConsts) (hN : C.MiddleNorms hW A κ)
    (hK : ∀ i, 0 ≤ midK2 κ i ∧ 0 ≤ midK3 κ i ∧ 0 ≤ midK4 i ∧ 0 ≤ midK5 i)
    (hsum : H + ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefS d * US β d +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefA d * UA β d) +
      ∑ i : Fin 33, (midK2 κ i * (PaperNumbers.chargeC2 i : ℝ) +
        (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
          (PaperNumbers.chargeC3 i : ℝ)) + (C.St + C.At) ≤ targetLedger.S + targetLedger.A) :
    SAExplicit C.Ci :=
  C.SAExplicit_N1 hBMOR NC hq (C.upper_le Cs Ca hCs hCa hR US UA hUS hUA) κ hN hK hsum

end Paper

end Sarkozy.MainFinal
