module

public import Sarkozy.UpperRepair.Paper

@[expose] public section

/-!
# How much the upper repair constants may exceed the paper's: `hsum` with scaled ledgers

`paper/sections/26_upper_comparison.tex`, `def:upper-comparison` (the state ledgers `Λ^s`, `Λ^a`),
and HS's proof of `SA.hsum` (`lean/Sarkozy/HsumProof/`). HS's `PaperLedgers` asks the per-record
coefficients `Cs`, `Ca` to have state sums at most the paper's ledgers. D1 (§12) estimated that
repair constants up to about `1.5×` the paper's fit a redesigned closing (`Θ_A`, run R2). For the
formal closing of `main_goal_f1d` the room in `hsum` is computed here, not estimated:

* `ScaledLedgers c Cs Ca`: the state sums are at most `c` times the paper's ledgers;
* `coefS_scale`, `coefA_scale`: W8's ledger coefficients scale at most linearly (the deleted
  records' part is fixed and nonnegative), for `c ≥ 1`;
* **`band_le_scaled`**, **`upperPart_le_scaled`**: the upper part of `hsum` is at most
  `c · 21/1000` (HS's `band_le` and `round_sum`, with the factor `c`);
* **`hsum_scaled`**: `SAPartsTC.hsum` at `κ = paperKappa` for every `1 ≤ c ≤ 7/4` (the budget
  `0.037 ≥ (7/4)·0.021` at `a_G`, RG; it was `5/2` with E3's `0.0526 ≥ (5/2)·0.021` at `a_T`);
* `UpperRepairDataS`, `toCmp`, `upperRecs`; `FinalBlockData3s`, `saOfS` (TC's `SAPartsTC`, all
  nine fields); **`MainFinalObligations3s`**, `to3e`; **`main_target_f1_final3s`**,
  **`main_goal_f1s`**.

So in `hsum` the repair constants of every changed record may be up to **`7/4`** times the paper's
(in every state ledger of every band). The data structure `UpperRepairDataS` asks for `c ≤ 5/4`
(RG, after RB's check of CM's `hCv`, which fails at `c = 7/4`). `hmid` contains the same
coefficients (`Uup Cs Ca`) and is
open; its room is not computed here.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes UpperBlockInputs)
open Sarkozy.ComparisonLawPaper (upperNe)
open Sarkozy.MainFinal (PrimeCertificates BlockAnalytic hCF SpecUpperRec midK2 midK3 midK4 midK5
  pieceScale)
open Sarkozy.MainFinal2 (PrimeCertificates2 MidRefinement SharpParts2)
open Sarkozy.EnvPrefix (Uup)
open Sarkozy.NumericalFields (bandBound)
open Sarkozy.AnalyticCells (f1Cell f1c2 f1c3)
open Sarkozy.MainFinalF1 (analyticInputs specF SpecNormBounds Blk bOf UpperSpec SignedSpec
  midAtom bandIdx)
open Sarkozy.MainFinalF1b (ClassPartsE4B)
open Sarkozy.MainFinalF1c (ComparisonPartsTC SAPartsTC FinalBlockData3e MainFinalObligations3e
  midOthersK1 tailStTC tailAtTC main_target_f1_final3e)
open Sarkozy.MainFinalF1d (budget_closes_TC)
open Sarkozy.HsumProof (PaperLedgers paperKappa paperKappa_nonneg upperBudget upperPart
  middlePart middlePart_paperKappa ledS ledA changedOf cSQ cAQ coefS_le coefA_le roundQ
  round_sum bandCheck bandCheck_all bandTot aT aT_cast UBQ bandBound_le_UBQ)

/-! ## Scaled ledgers -/

/-- **The coefficients have at most `c` times the paper's state ledgers.** -/
def ScaledLedgers (c : ℝ) (Cs Ca : Fin 310 → UpIdx → ℝ) : Prop :=
  ∀ k t, (∑ ρ ∈ changedOf t, Cs k ρ ≤ c * (ledS k t : ℝ)) ∧
    ∑ ρ ∈ changedOf t, Ca k ρ ≤ c * (ledA k t : ℝ)

theorem scaledLedgers_one {Cs Ca : Fin 310 → UpIdx → ℝ} (h : PaperLedgers Cs Ca) :
    ScaledLedgers 1 Cs Ca := fun k t => by
  rw [one_mul, one_mul]
  exact h k t

/-- W8's symmetric ledger coefficient scales at most linearly, for `c ≥ 1`. -/
theorem coefS_scale (W : UpperWeights) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i)
    (hCa : ∀ i, 0 ≤ Ca i) {c : ℝ} (hc : 1 ≤ c) (d : ℕ) :
    (upperLedger W Cs Ca hCs hCa).coefS d ≤
      c * (upperLedger W (fun ρ => Cs ρ / c) (fun ρ => Ca ρ / c)
        (fun i => div_nonneg (hCs i) (by linarith))
        (fun i => div_nonneg (hCa i) (by linarith))).coefS d := by
  have hc0 : (0 : ℝ) < c := by linarith
  unfold RecordLedger.coefS RecordLedger.changed RecordLedger.deleted
  change ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .changed).filter
      (fun ρ => upperDeg ρ + 1 = d), upperWeight W ρ * Cs ρ +
    ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .deleted).filter
      (fun ρ => upperDeg ρ = d), upperWeight W ρ ≤
    c * (∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .changed).filter
      (fun ρ => upperDeg ρ + 1 = d), upperWeight W ρ * (Cs ρ / c) +
    ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .deleted).filter
      (fun ρ => upperDeg ρ = d), upperWeight W ρ)
  have hD0 : 0 ≤ ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .deleted).filter
      (fun ρ => upperDeg ρ = d), upperWeight W ρ :=
    Finset.sum_nonneg fun ρ _ => (upperLedger W Cs Ca hCs hCa).w_nonneg ρ
  have e : ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .changed).filter
      (fun ρ => upperDeg ρ + 1 = d), upperWeight W ρ * Cs ρ =
      c * ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .changed).filter
      (fun ρ => upperDeg ρ + 1 = d), upperWeight W ρ * (Cs ρ / c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    field_simp
  rw [e]
  nlinarith

/-- W8's skew ledger coefficient scales linearly. -/
theorem coefA_scale (W : UpperWeights) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i)
    (hCa : ∀ i, 0 ≤ Ca i) {c : ℝ} (hc : 1 ≤ c) (d : ℕ) :
    (upperLedger W Cs Ca hCs hCa).coefA d =
      c * (upperLedger W (fun ρ => Cs ρ / c) (fun ρ => Ca ρ / c)
        (fun i => div_nonneg (hCs i) (by linarith))
        (fun i => div_nonneg (hCa i) (by linarith))).coefA d := by
  have hc0 : (0 : ℝ) < c := by linarith
  unfold RecordLedger.coefA RecordLedger.changed
  change ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .changed).filter
      (fun ρ => upperDeg ρ + 1 = d), upperWeight W ρ * Ca ρ =
    c * ∑ ρ ∈ (univ.filter fun ρ : UpIdx => upperFate ρ = .changed).filter
      (fun ρ => upperDeg ρ + 1 = d), upperWeight W ρ * (Ca ρ / c)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  field_simp

/-- **The terms of one band with scaled ledgers** are at most `c · roundQ` (HS's `band_le`). -/
theorem band_le_scaled (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) {c : ℝ} (hc : 1 ≤ c) (hL : ScaledLedgers c Cs Ca) (β : Fin 310) :
    ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
            bandBound targetDecay d β +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
            bandBound targetDecay d β) ≤ c * (roundQ β : ℝ) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hc := bandCheck_all β
  simp only [bandCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hok, hUB0⟩, htot⟩ := hc
  have hLs : ∀ t, ∑ ρ ∈ changedOf t, Cs β ρ / c ≤ (ledS β t : ℝ) := fun t => by
    rw [← Finset.sum_div, div_le_iff₀ hc0, mul_comm]
    exact (hL β t).1
  have hLa : ∀ t, ∑ ρ ∈ changedOf t, Ca β ρ / c ≤ (ledA β t : ℝ) := fun t => by
    rw [← Finset.sum_div, div_le_iff₀ hc0, mul_comm]
    exact (hL β t).2
  have hterm : ∀ d ∈ upperDegrees,
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
            bandBound targetDecay d β +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
            bandBound targetDecay d β ≤
        c * ((cSQ β d : ℝ) * (UBQ aT β d : ℝ) + (cAQ β d : ℝ) * (UBQ aT β d : ℝ)) := by
    intro d hd
    have hd' : d ∈ Finset.Icc 3 7 := hd
    have hd2 : 2 ≤ d := by
      have := (Finset.mem_Icc.mp hd').1
      omega
    have hb := bandBound_le_UBQ aT β hok hd2
    rw [aT_cast] at hb
    have hU0 : (0 : ℝ) ≤ (UBQ aT β d : ℝ) := by exact_mod_cast hUB0 d hd'
    have hS := coefS_le β (fun ρ => Cs β ρ / c) (fun ρ => Ca β ρ / c)
      (fun i => div_nonneg (hCs β i) hc0.le) (fun i => div_nonneg (hCa β i) hc0.le) hLs hd'
    have hA := coefA_le β (fun ρ => Cs β ρ / c) (fun ρ => Ca β ρ / c)
      (fun i => div_nonneg (hCs β i) hc0.le) (fun i => div_nonneg (hCa β i) hc0.le) hLa d
    have hS' := (coefS_scale (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β) hc d).trans
      (mul_le_mul_of_nonneg_left hS hc0.le)
    have hA' := (coefA_scale (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β) hc
      d).trans_le
      (mul_le_mul_of_nonneg_left hA hc0.le)
    have hS0 := RecordLedger.coefS_nonneg
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)) d
    have hA0 := RecordLedger.coefA_nonneg
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)) d
    have h1 := (mul_le_mul_of_nonneg_left hb hS0).trans (mul_le_mul_of_nonneg_right hS' hU0)
    have h2 := (mul_le_mul_of_nonneg_left hb hA0).trans (mul_le_mul_of_nonneg_right hA' hU0)
    nlinarith
  refine (sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have e : ∑ d ∈ upperDegrees, ((cSQ β d : ℝ) * (UBQ aT β d : ℝ) +
      (cAQ β d : ℝ) * (UBQ aT β d : ℝ)) = (bandTot β : ℝ) := by
    unfold bandTot
    push_cast
    rfl
  rw [e]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast htot) hc0.le

/-- **The upper part of `hsum` with scaled ledgers**: at most `c · 21/1000`. -/
theorem upperPart_le_scaled (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) {c : ℝ} (hc : 1 ≤ c) (hL : ScaledLedgers c Cs Ca) :
    upperPart Cs Ca hCs hCa ≤ c * (21 / 1000) := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  unfold upperPart
  calc _ ≤ ∑ β : Fin 310, c * (roundQ β : ℝ) :=
        sum_le_sum fun β _ => band_le_scaled Cs Ca hCs hCa hc hL β
    _ = c * ∑ β : Fin 310, (roundQ β : ℝ) := by rw [Finset.mul_sum]
    _ ≤ c * (21 / 1000) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        have h := round_sum
        have h' : ((∑ β : Fin 310, roundQ β : ℚ) : ℝ) ≤ ((21 / 1000 : ℚ) : ℝ) := by
          exact_mod_cast h
        simpa using h'

/-- **`SAPartsTC.hsum` at `κ = paperKappa` with ledgers scaled by `c ≤ 7/4`.** -/
theorem hsum_scaled (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) {c : ℝ} (hc : 1 ≤ c) (hc' : c ≤ 7 / 4)
    (hL : ScaledLedgers c Cs Ca) :
    12 / 2 ^ 534 + ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
            bandBound targetDecay d β +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
            bandBound targetDecay d β) +
      ∑ i : Fin 33, (midK2 paperKappa i * f1c2 i +
        (midK3 paperKappa i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i) +
        (tailStTC + tailAtTC) ≤ targetLedger.S + targetLedger.A := by
  have h := budget_closes_TC
  have hU := upperPart_le_scaled Cs Ca hCs hCa hc hL
  have hU' : upperPart Cs Ca hCs hCa ≤ upperBudget := by
    refine hU.trans ?_
    unfold upperBudget
    nlinarith
  have hM := middlePart_paperKappa
  unfold upperPart at hU'
  unfold middlePart at hM
  generalize (12 : ℝ) / 2 ^ 534 = c' at h ⊢
  generalize tailStTC + tailAtTC = τ at h ⊢
  linarith

/-! ## The inputs and the obligations -/

/-- **`UpperRepairData` with ledgers scaled by `c ∈ [1, 5/4]`** (`hLed` replaced by
`ScaledLedgers c`; RG: `5/4`, as `UpperCapsPaper.UpperRecordTables.hc'`, for CM's `hCv`; `hsum`
alone allows `c ≤ 7/4`, `hsum_scaled`). -/
structure UpperRepairDataS (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell) where
  /-- The scale of the ledgers. Data. -/
  c : ℝ
  hc : 1 ≤ c
  hc' : c ≤ 5 / 4
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- The state sums are at most `c` times the paper's ledgers. Finite. -/
  hLed : ScaledLedgers c Cs Ca
  /-- The replacing laws of the changed records at every upper block. *Open* (analytic). -/
  rep : ∀ (b : Blk) (U : UpperBlockInputs bOf b), specF hW A b = .upper U →
    BlockRepl (blockPrimes bOf b) (upperNe hW U)
  /-- `C^s_ρ ≤ Cs_{k,ρ} r_𝔅`. *Open* (numerical). -/
  hs : ∀ b U (h : specF hW A b = .upper U) ρ, upperFate ρ = .changed →
    (rep b U h).coef ρ .sym ≤ Cs (bandIdx b) ρ * U.r
  /-- `C^a_ρ ≤ Ca_{k,ρ} r_𝔅`. *Open* (numerical). -/
  ha : ∀ b U (h : specF hW A b = .upper U) ρ, upperFate ρ = .changed →
    (rep b U h).coef ρ .skew ≤ Ca (bandIdx b) ρ * U.r

variable {hW : Target.Weil}

namespace UpperRepairDataS

variable {A : PaperAnalyticInputs f1Cell}

/-- `UpperRepairData` is the case `c = 1`. -/
noncomputable def ofData (D : UpperRepairData hW A) : UpperRepairDataS hW A where
  c := 1
  hc := le_rfl
  hc' := by norm_num
  Cs := D.Cs
  Ca := D.Ca
  hCs := D.hCs
  hCa := D.hCa
  hLed := scaledLedgers_one D.hLed
  rep := D.rep
  hs := D.hs
  ha := D.ha

/-- TC's `ComparisonPartsTC` from the replacing laws. -/
noncomputable def toCmp (D : UpperRepairDataS hW A) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) : ComparisonPartsTC hW hMR hFour A where
  blkU b := specU (specF hW A b) (D.rep b)

/-- `SA.hR` for `toCmp`, proved. -/
theorem upperRecs (D : UpperRepairDataS hW A) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) : (D.toCmp hMR hFour).toK1.UpperRecs hW A D.Cs D.Ca D.hCs D.hCa := by
  intro b k hs
  have hk := UpperRepairData.bandIdx_eq hs
  refine MainFinalF1c.specUpperRec_at hW (paperIn f1Cell) _ _ _ _ (specF hW A b) _
    (specU_rec (D.Cs k) (D.Ca k) (D.hCs k) (D.hCa k) (specF hW A b) (D.rep b) ?_)
  intro U h
  refine ⟨fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · have := D.hs b U h ρ hρ
    rwa [hk] at this
  · have := D.ha b U h ρ hρ
    rwa [hk] at this

end UpperRepairDataS

variable {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- The block data with the scaled upper inputs. 4 fields. -/
structure FinalBlockData3s (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  PC : PrimeCertificates2
  BA : BlockAnalytic
  /-- The replacing laws of the upper blocks, ledgers scaled by `c ≤ 5/4`. *Open*. -/
  Up : UpperRepairDataS hW (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- K2's `MR`. *Open*. -/
  MR : MidRefinement
    (gramBracketTarget bOf hW (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA))
      (hCF hW hMR hFour) (paperIn f1Cell)
      (paperGi hW (analyticInputs (PC.toPC hW hMR hFour) BA)))
    (Up.toCmp hMR hFour).toK1.CL
    (fun β => midAtom hW (analyticInputs (PC.toPC hW hMR hFour) BA) β = true)

namespace FinalBlockData3s

/-- TC's `FinalBlockData3e`. -/
noncomputable def to3e (D : FinalBlockData3s hW hMR hFour) : FinalBlockData3e hW hMR hFour where
  PC := D.PC
  BA := D.BA
  Cmp := D.Up.toCmp hMR hFour
  MR := D.MR

/-- **TC's `SAPartsTC`, all nine fields**: the data from `Up`, `hR` proved, `κ = paperKappa`,
`hsum` by `hsum_scaled`; only the middle norm bounds `hN` are taken. -/
noncomputable def saOfS (D : FinalBlockData3s hW hMR hFour)
    (hN : ∀ b i, blockSite b = .inl i →
      SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
        (specF hW (analyticInputs (D.PC.toPC hW hMR hFour) D.BA) b) (D.to3e.Cmp.blk b)) :
    SAPartsTC hW hMR hFour (analyticInputs (D.to3e.PC.toPC hW hMR hFour) D.to3e.BA)
      D.to3e.Cmp where
  Cs := D.Up.Cs
  Ca := D.Up.Ca
  hCs := D.Up.hCs
  hCa := D.Up.hCa
  hR := D.Up.upperRecs hMR hFour
  κ := paperKappa
  hκ := paperKappa_nonneg
  hκP i := MainFinalF1c.KappaLe.refl (paperKappa i)
  hN := hN
  hsum := hsum_scaled D.Up.Cs D.Up.Ca D.Up.hCs D.Up.hCa D.Up.hc (D.Up.hc'.trans (by norm_num))
    D.Up.hLed

end FinalBlockData3s

/-- **The obligations with scaled upper ledgers**: as `MainFinalObligations3g`, with `Dv.Up`
allowing state ledgers up to `5/4` times the paper's. 5 fields. -/
structure MainFinalObligations3s (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  Dv : FinalBlockData3s hW hMR hFour
  /-- The middle norm bounds at the paper's constants. *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b)
      (specF hW (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) b) (Dv.to3e.Cmp.blk b)
  /-- The middle part of `hothT`. *Open*. -/
  hmid : ∀ L, midOthersK1 Dv.to3e.Cmp.toK1 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Uup Dv.Up.Cs Dv.Up.Ca Dv.Up.hCs Dv.Up.hCa + (tailStTC + tailAtTC)) ≤
      targetLedger.T
  Cls : ClassPartsE4B (Dv.to3e.toK1 hB (Dv.saOfS hN) hmid).data
  Sh : SharpParts2 (Dv.to3e.toK1 hB (Dv.saOfS hN) hmid).toJoint

/-- TC's `MainFinalObligations3e`. -/
noncomputable def MainFinalObligations3s.to3e {hB : Target.BMOR}
    (O : MainFinalObligations3s hW hMR hFour hB) : MainFinalObligations3e hW hMR hFour hB where
  Dv := O.Dv.to3e
  SA := O.Dv.saOfS O.hN
  hmid := O.hmid
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement with scaled upper ledgers** (`thm:main` at `ε = a_T/71`; TC's
`main_target_f1_final3e`). -/
theorem main_target_f1_final3s (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3s hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_final3e hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O.to3e

/-- **`main_target_f1_final3s` at the owner's goal exponent** `N^{0.99999}`. -/
theorem main_goal_f1s (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3s hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  Target.sarkozyBound_mono TargetGoal.epsGoal_le_targetSaving
    (main_target_f1_final3s hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O)

end Sarkozy.UpperRepair
