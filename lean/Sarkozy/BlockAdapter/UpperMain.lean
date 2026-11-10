module

public import Sarkozy.BlockAdapter.Upper
public import Sarkozy.BlockAdapter.Main

@[expose] public section

/-!
# The main statement with the upper root envelopes of coordinate `0` from per-prime certificates

`paper/sections/25_upper_reference.tex`, `lem:upper-reference-rp`(ii), (V1), `cert:upper-root-caps`;
B1's `UpperBandLemma` (`BlockSpecPaper/Lemmas.lean`).

* `ChamberCutCap f' Λ g B p`: the per-prime bounds `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` of the cut
  operator of `chamberData f' Λ` (for `f' = L`, `Λ = ℤ/2` the cut `LL20`);
* `UpperBandRootCap k f' Λ d`: constants `(g, B, X)` with `1 < X ≤ X_k`, `g X^{-1/2} < 1`,
  `g e^{B L_k/(X log X)} ≤ d` and `ChamberCutCap` at every class-three prime of band `k`.
  *Hypothesis* (`cert:upper-root-caps`; the upper records store only the caps `d`);
* `UpperRootCaps k`: these for the ordinary caps `d` (two layers) and the reserved caps (one layer)
  at the three field types. *Hypothesis*;
* `UpperBandRest k`: B1's `UpperBandLemma k` without the fields `root20`, `root10` (7 of 9 fields).
  *Hypothesis*;
* `upperBandLemma_of_rest`: `UpperBandLemma k` from `UpperBandRest k` and `UpperRootCaps k`;
* `main_target_paper_joint_B6_upper0`: the main statement with the middle reductions of
  `Main.lean` and this upper reduction (`UpperSwap.lean` reduces further:
  `main_target_paper_joint_B6`).
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.PartVLaws.FieldGraphs Sarkozy.BlockSpecPaper

/-! ## The per-prime and per-band certificates -/

/-- **The per-prime cap of the chamber cut `ϑ₀` of `G_{Lφ}`** at `p` (`chamberData f' Λ`). -/
def ChamberCutCap (f' : FieldTy) (Λ : Type) [Fintype Λ] [DecidableEq Λ] (g B : ℝ) (p : ℕ)
    [Fact p.Prime] : Prop :=
  ∀ (hneL : (injLabellings (ZMod p) (chamberGraph f' Λ)).Nonempty)
    (v : EuclideanSpace ℝ ((chamberData f' Λ).cut.Half → ZMod p)),
    -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (chamberData f' Λ) hneL v⟫_ℝ ∧
      ⟪v, Spectral.cutOp (chamberData f' Λ) hneL v⟫_ℝ ≤ (1 + B / p) * ‖v‖ ^ 2

/-- **The root-cap certificate of band `k` at the field type `f'`** for the cap `d`
(`cert:upper-root-caps`): per-prime constants `(g, B)` and a threshold `X ≤ X_k` whose block
cap `g e^{B L_k/(X log X)}` is at most `d`, with the per-prime bounds at every class-three prime of
the band. *Hypothesis*. -/
def UpperBandRootCap (k : Fin 310) (f' : FieldTy) (Λ : Type) [Fintype Λ] [DecidableEq Λ]
    (d : ℝ) : Prop :=
  ∃ g B X : ℝ, 0 ≤ g ∧ 0 ≤ B ∧ 1 < X ∧ X ≤ (bandOf k).1 ∧ g * (√X)⁻¹ < 1 ∧
    g * Real.exp (B * (UpperRecords.CompletionData.record k).budget / (X * Real.log X)) ≤ d ∧
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → (bandOf k).1 ≤ p → p < (bandOf k).2 →
      ChamberCutCap f' Λ g B p

/-- **The coordinate-`0` root certificates of band `k`**: two layers at the ordinary caps, one
layer at the reserved caps, for the three field types. *Hypothesis*. -/
def UpperRootCaps (k : Fin 310) : Prop :=
  ∀ f' : FieldTy, UpperBandRootCap k f' (ZMod 2) (UpperRecords.bandOrd k f').d ∧
    UpperBandRootCap k f' Unit (UpperRecords.bandRes k f').d

/-- **`lem:upper-reference-rp`(ii) on band `k` without the coordinate-`0` root envelopes**: the
fields `root21`, `root11`, `rows20`, `rows21`, `rows10`, `rows11`, `caps` of `ValidInputs`.
*Hypothesis* (spectral). -/
def UpperBandRest (k : Fin 310) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2) →
    (∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget) →
    (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ (hne : UpperNonempty pr) (hW' : ∀ i, WeilBound (ZMod (pr i)))
      (hp' : ∀ i, (2 : ℝ) ^ 20 ≤ pr i),
      (∀ f', RootEnv (rowD1 (lam2 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).two1 f')) (UpperRecords.bandOrd k f').d
          ((b : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
      (∀ f', RootEnv (rowD1 (lam1 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).one1 f')) (UpperRecords.bandRes k f').d
          ((b : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
      (∀ f', ValidRows (rowD0 (lam2 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).two0 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandOrd k f').f (UpperRecords.bandOrd k f').h
          (UpperRecords.bandOrd k f').M) ∧
      (∀ f', ValidRows (rowD1 (lam2 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).two1 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandOrd k f').f (UpperRecords.bandOrd k f').h
          (UpperRecords.bandOrd k f').M) ∧
      (∀ f', ValidRows (rowD0 (lam1 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).one0 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandRes k f').f (UpperRecords.bandRes k f').h
          (UpperRecords.bandRes k f').M) ∧
      (∀ f', ValidRows (rowD1 (lam1 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).one1 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandRes k f').f (UpperRecords.bandRes k f').h
          (UpperRecords.bandRes k f').M) ∧
      UpperLayerCaps (upperBlockFieldLaws pr hne) (UpperRecords.bandCap k)
        ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-! ## The root fields from the certificates -/

theorem rootEnv_mono {𝔛 : Type} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛) {d d' r : ℝ}
    (hr : 0 ≤ r) (hd : d ≤ d') (h : RootEnv D d r) : RootEnv D d' r :=
  Reserved.below_mono_coeff (chamberCut 0) D.compF0_positive (mul_le_mul_of_nonneg_right hd hr) h

section Fields

variable {k : Fin 310} {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
  [∀ j, Fact (pr j).Prime] (b : ℕ)

omit [Fintype ι] [DecidableEq ι] [∀ j, Fact (pr j).Prime] in
theorem band_side {X : ℝ} (hXk : X ≤ (bandOf k).1)
    (hband : ∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2) (hb' : ∃ j, pr j = b) :
    X ≤ b := by
  obtain ⟨j₀, hj₀⟩ := hb'
  have h : ((bandOf k).1 : ℝ) ≤ b := by
    rw [← hj₀]
    exact_mod_cast (hband j₀).1
  linarith

theorem gp_side {g X : ℝ} (hg : 0 ≤ g) (hX : 1 < X) (hgX : g * (√X)⁻¹ < 1) {p : ℝ}
    (hp : X ≤ p) : g * (√p)⁻¹ < 1 := by
  have hs : √X ≤ √p := Real.sqrt_le_sqrt hp
  have hsX : 0 < √X := Real.sqrt_pos.mpr (by linarith)
  have hinv : (√p)⁻¹ ≤ (√X)⁻¹ := inv_anti₀ hsX hs
  have := mul_le_mul_of_nonneg_left hinv hg
  linarith

/-- **`root20` of band `k` from the certificates.** -/
theorem upper_root20_of_cert (f' : FieldTy) (hC : UpperBandRootCap k f' (ZMod 2)
      (UpperRecords.bandOrd k f').d) (h3 : ∀ j, pr j % 4 = 3)
    (hband : ∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2)
    (hbud : ∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget)
    (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b) (hne : UpperNonempty pr)
    (hRow : RowHyp0 (lam2 (upperBlockFieldLaws pr hne)) f') :
    RootEnv (rowD0 (lam2 (upperBlockFieldLaws pr hne)) f' hRow) (UpperRecords.bandOrd k f').d
      ((b : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨g, B, X, hg, hB, hX, hXk, hgX, hcap, hcert⟩ := hC
  rw [rpow_neg_half_eq]
  refine rootEnv_mono _ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hcap ?_
  exact upper_root20_of_cutCaps pr hne f' hRow hg hB hX (band_side pr b hXk hband hb')
    (fun j => by exact_mod_cast hb j) hbud
    (fun j => gp_side hg hX hgX (le_trans hXk (by exact_mod_cast (hband j).1)))
    (fun j v => (hcert (pr j) (h3 j) (hband j).1 (hband j).2 _ v).1)
    (fun j v => (hcert (pr j) (h3 j) (hband j).1 (hband j).2 _ v).2)

/-- **`root10` of band `k` from the certificates.** -/
theorem upper_root10_of_cert (f' : FieldTy) (hC : UpperBandRootCap k f' Unit
      (UpperRecords.bandRes k f').d) (h3 : ∀ j, pr j % 4 = 3)
    (hband : ∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2)
    (hbud : ∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget)
    (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b) (hne : UpperNonempty pr)
    (hRow : RowHyp0 (lam1 (upperBlockFieldLaws pr hne)) f') :
    RootEnv (rowD0 (lam1 (upperBlockFieldLaws pr hne)) f' hRow) (UpperRecords.bandRes k f').d
      ((b : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨g, B, X, hg, hB, hX, hXk, hgX, hcap, hcert⟩ := hC
  rw [rpow_neg_half_eq]
  refine rootEnv_mono _ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hcap ?_
  exact upper_root10_of_cutCaps pr hne f' hRow hg hB hX (band_side pr b hXk hband hb')
    (fun j => by exact_mod_cast hb j) hbud
    (fun j => gp_side hg hX hgX (le_trans hXk (by exact_mod_cast (hband j).1)))
    (fun j v => (hcert (pr j) (h3 j) (hband j).1 (hband j).2 _ v).1)
    (fun j v => (hcert (pr j) (h3 j) (hband j).1 (hband j).2 _ v).2)

end Fields

/-- **B1's `UpperBandLemma k` from the rest and the coordinate-`0` root certificates.** -/
theorem upperBandLemma_of_rest {k : Fin 310} (hR : UpperBandRest k) (hC : UpperRootCaps k) :
    UpperBandLemma k := by
  intro ι _ _ pr _ b hinj h3 hband hbud hb hb' hne hW' hp'
  obtain ⟨r21, r11, w20, w21, w10, w11, caps⟩ := hR ι pr b hinj h3 hband hbud hb hb' hne hW' hp'
  exact
    { root20 := fun f' => upper_root20_of_cert pr b f' (hC f').1 h3 hband hbud hb hb' hne _
      root21 := r21
      root10 := fun f' => upper_root10_of_cert pr b f' (hC f').2 h3 hband hbud hb hb' hne _
      root11 := r11
      rows20 := w20
      rows21 := w21
      rows10 := w10
      rows11 := w11
      caps := caps }

/-! ## The main statement -/

/-- **The main statement at `ε = a_T/71`, joint form, with the block adapter**
(`thm:main` at `ε = a_T/71`, `cor:joint-closing`, `def:construction`(b) in the ALLp
configuration, `lem:front12:reference`(i),(ii), `lem:upper-reference-rp`(ii)).

Remaining, besides the literature hypotheses:
* the data `cell` and `PaperBudget cell` (combinatorial);
* upper bands (310): `hUR` (`UpperBandRest`: 7 of the 9 fields of `ValidInputs`) and `hUC`
  (`UpperRootCaps`: per-prime certificates of the chamber cuts with the per-band constants,
  `cert:upper-root-caps`);
* middle pieces: `hMB`, `hIB` (block-level: rows; F21 at `k_D`; on `2³⁶`, `2⁴⁰` the L20
  envelope and L21 cap of the individual root) and the per-prime certificates `h20` (L20, 31
  uniform pieces), `h10` (L10, 33 pieces), `h21` (L21, 31 uniform pieces); E21 is proved;
* B1's 11 joint obligations `O`. -/
theorem main_target_paper_joint_B6_upper0 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ) (hbud : PaperBudget cell)
    (hUR : ∀ k, UpperBandRest k) (hUC : ∀ k, UpperRootCaps k)
    (hMB : ∀ i, allpIndividual i = none → MiddleUniformBlockInputs i)
    (hIB : ∀ i u, allpIndividual i = some u → MiddleIndividualBlockInputs i u)
    (h20 : ∀ i, allpIndividual i = none → MiddleRootCaps (Fin 2) 0 i)
    (h10 : ∀ i, MiddleRootCaps (Fin 1) 1 i)
    (h21 : ∀ i, allpIndividual i = none → MiddleL21Caps i)
    (O : B1JointFinalObligations cell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_B6 hbud (fun k => upperBandLemma_of_rest (hUR k) (hUC k)) hMB hIB h20
        h10 h21 middleE21Caps_proved)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR cell _ O

end Sarkozy.BlockAdapter
