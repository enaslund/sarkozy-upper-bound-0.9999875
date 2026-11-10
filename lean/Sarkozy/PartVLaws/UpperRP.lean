module

public import Sarkozy.PartVLaws.UpperBridge
public import Sarkozy.FiveType.Graded

@[expose] public section

/-!
# Reflection positivity of the upper reference (`lem:upper-reference-rp`(i))

`paper/sections/25_upper_reference.tex`, `subsec:upper-reference-rp`: the validity conditions
(V1)–(V3) and `lem:upper-reference-rp`(i); `paper/sections/17_completion_repair.tex`,
`lem:five-type`(b),(c),(d),(e),(f).

**The argument** (the paper's proof of (i), "Chamber cuts" and "The reserved cut"):
* `upperTilde_eq_paired` writes `μ̃_𝔅` as C1's two-coordinate paired measure
  `∑_𝔱 w_𝔱 r^{deg 𝔱} π_{𝔱,2} + r ∑_𝔱 v_𝔱 r^{deg 𝔱} Diag_ι(π_{𝔱,1})`;
* the slice of a coordinate `c` at the type `𝔱'` of the other coordinate carries the weights
  `w_𝔱 r^{deg 𝔱} = r^{deg 𝔱'} · (a_𝔰 r^{deg 𝔰})` (`slice0_weights`, `slice1_weights`), so the
  factor `r^{deg 𝔱'}` does not matter (`rpAll_Q_smul`);
* each slice five-type measure is reflection positive at every chamber cut by `lem:five-type`(b),
  (c) or (f) (`sliceRP_of_valid`, from `ValidRows`, the paper's (V2), and `RootEnv`, (V1),
  and the four graded slice conditions `SliceGates` of `eq:upper-slice`);
* `lem:five-type`(d) (`two_coordinate_rp`) gives the chamber cuts of both coordinates for both
  layer sets, and `Diag_ι` carries the one-layer part (`Reserved.diag_positive_cut0/1`);
* the reserved cut `ι` is V1's fold pairing (`upperTilde_reserved_positive`) under the layer caps
  (V3) and the domination `v_𝔱 ≥ k_𝔱 w_𝔱` (`eq:independent-fold-domination`).

**Headline.** `upperReference_familyPositive`: under the datum hypotheses (`RowHyp0/1`, i.e. the
row data form five-type data), (V1)–(V3) and the 105 gates, the upper reference is reflection
positive at every cut of the family `𝔉` (`TheoremC.FamilyReflectionPositive`, (R2)). The
measure, invariance and marginal claims of (i) are V1's (`upperTilde_mass`,
`upperReference_invariant`, `upperReference_uniform`). Admissibility is not formalized (it is
structural in `TheoremC`).

**Hypotheses.** (V1) the root envelopes, (V2) the row bounds and (V3) the layer caps are the
spectral inputs of section 25 (the spectral criterion and the certificates), stated here as
named `Prop`s. The datum hypotheses are discharged for the paper's laws in
`Sarkozy.PartVLaws.UpperGraphs` (exchangeability and `𝒢₆` from `lem:upper-geometry`(b), the
`Γ`-support from the extension counts of `lem:graphs:sequential` under H1).
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-! ## Homogeneity of the slice conditions -/

theorem Q_const_mul (D : Datum 𝔛) (c : ℝ) (a : Ty → ℝ) :
    D.Q (fun t => c * a t) = c • D.Q a := by
  unfold Datum.Q
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_smul]

/-- **The slice conditions are homogeneous**: a nonnegative factor does not change reflection
positivity of a five-type measure. -/
theorem rpAll_Q_smul (D : Datum 𝔛) {c : ℝ} (hc : 0 ≤ c) {a : Ty → ℝ} (h : RPAll (D.Q a)) :
    RPAll (D.Q (fun t => c * a t)) := by
  intro i
  rw [Q_const_mul]
  exact (h i).smul hc

/-- The slice of the coordinate `0` at `t₁`: `w_{(t₀,t₁)} r^{deg t₀ + deg t₁} =
r^{deg t₁} (w_{(t₀,t₁)} r^{deg t₀})`. -/
theorem slice0_weights (w : Ty → Ty → ℝ) (r : ℝ) (t1 : Ty) :
    (fun t0 => w t0 t1 * r ^ stateDeg t0 t1) =
      fun t0 => r ^ t1.deg * graded (fun s => w s t1) r t0 := by
  funext t0
  simp only [stateDeg, graded, pow_add]
  ring

/-- The slice of the coordinate `1` at `t₀`. -/
theorem slice1_weights (w : Ty → Ty → ℝ) (r : ℝ) (t0 : Ty) :
    (fun t1 => w t0 t1 * r ^ stateDeg t0 t1) =
      fun t1 => r ^ t0.deg * graded (fun s => w t0 s) r t1 := by
  funext t1
  simp only [stateDeg, graded, pow_add]
  ring

/-! ## Valid rows (V2) and the slice criterion -/

/-- **The graded slice conditions** `eq:upper-slice`: `a_D ≥ d a_L`, `a_S ≥ M a_D`,
`a_R ≥ f a_D + h a_S`, `a_C a_S ≥ a_R²`. -/
def SliceGates (d f h M : ℝ) (a : Ty → ℝ) : Prop :=
  d * a .L ≤ a .D ∧ M * a .D ≤ a .S ∧ f * a .D + h * a .S ≤ a .R ∧ a .R ^ 2 ≤ a .C * a .S

/-- **Valid rows** (`subsec:upper-reference-rp`, (V2)): at every value `b` of the middle object,
the rows satisfy, with graded coefficients at most `(f, h)` and the mean allowance `M`, the
hypotheses of `lem:five-type`(b), of (c) or of (f). -/
def ValidRows (D : Datum 𝔛) (r f h M : ℝ) : Prop :=
  -- (b) the full-norm criterion
  (0 ≤ f ∧ 1 ≤ M ∧ ∀ b, D.nu.weight b ≠ 0 →
      NormBound (D.nub b) (D.TF b) (f * r) ∧ NormBound (D.nub b) (D.TE b) (h * r)) ∨
  -- (c) the Schur criterion, with the fold data of `K_b = T_F^b`
  (∃ H β qperp tY : ℝ, 0 ≤ qperp ∧ 0 < tY ∧ tY ≤ H⁻¹ ∧ H + tY ≤ M ∧
      (qperp + β ^ 2 / tY) / r ≤ f ∧ ∀ b, D.nu.weight b ≠ 0 →
        ExactMarginals (D.nub b) (D.TE b) ∧ NormBound (D.nub b) (D.TE b) (h * r) ∧
          FoldData (D.nub b) (D.TF b) H β qperp) ∨
  -- (f) the joint Schur criterion, with the joint data of `K_b`
  (∃ H υ εT kJ tY : ℝ, 0 ≤ h ∧ 0 ≤ εT ∧ 0 < tY ∧ tY ≤ H⁻¹ ∧ H + tY ≤ M ∧
      fJ H kJ h r εT tY υ ≤ f ∧ ∀ b, D.nu.weight b ≠ 0 →
        ExactMarginals (D.nub b) (D.TE b) ∧
          Nonempty (JointData (D.nub b) (D.TE b) (D.TF b) H υ εT (h * r) (kJ * r)))

/-- **The root envelope** (`subsec:upper-reference-rp`, (V1)) of a five-type datum at `ϑ₀`:
`Π_L ⪰_{ϑ₀} -d r Π_{F₀}` (V1's `PartV.RootEnvelope`, for data on any finite set). -/
def RootEnv (D : Datum 𝔛) (d r : ℝ) : Prop :=
  (chamberCut 0).Below (-(d * r) • D.compF 0) D.compL

/-- **A slice of valid rows is reflection positive at every chamber cut** (`lem:five-type`(b),
(c) or (f) in graded form): the root envelope `Π_L ⪰_{ϑ₀} -d r Π_{F₀}` (V1), valid rows (V2)
and the four slice conditions give `𝒬_{graded a r} ⪰ 0` at every `ϑ_i`. -/
theorem sliceRP_of_valid (D : Datum 𝔛) {r d f h M : ℝ} (hr : 0 < r) {a : Ty → ℝ}
    (ha : ∀ t, 0 ≤ a t) (haD : 0 < a .D) (hrows : ValidRows D r f h M)
    (hroot : RootEnv D d r) (hg : SliceGates d f h M a) :
    RPAll (D.Q (graded a r)) := by
  obtain ⟨hd, hM, hR, hC⟩ := hg
  have hroot' : a .L = 0 ∨ ((chamberCut 0).Below (-(d * r) • D.compF 0) D.compL ∧
      d * a .L ≤ a .D) := Or.inr ⟨hroot, hd⟩
  rcases hrows with ⟨hf, hM1, hb⟩ | ⟨H, β, qperp, tY, hq, htY, htH, hHM, hfal, hb⟩ |
      ⟨H, υ, εT, kJ, tY, hh, hεT, htY, htH, hHM, hfJ, hb⟩
  · refine D.full_norm_rp_graded ha hr hf (fun b hb' => (hb b hb').1) (fun b hb' => (hb b hb').2)
      ?_ hR hC hroot'
    nlinarith [haD]
  · refine D.schur_rp_graded ha haD hr hq (fun b hb' => (hb b hb').1)
      (fun b hb' => (hb b hb').2.1) (fun b hb' => (hb b hb').2.2) htY htH ?_ ?_ hC hroot'
    · nlinarith [haD]
    · nlinarith [haD, ha .S]
  · refine D.joint_rp_graded ha haD hr hh hεT (fun b hb' => (hb b hb').1)
      (fun b hb' => ((hb b hb').2).some) htY htH ?_ ?_ hC hroot'
    · nlinarith [haD]
    · nlinarith [haD, ha .S]

/-! ## The chamber cuts of the upper reference -/

section Chamber

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The datum hypotheses of an upper block** (`subsec:upper-rows`: "the two-layer row data of
`c` at `𝔣(𝔱')` form a five-type datum", and the same for the one-layer rows), for both
coordinates and every field type. -/
structure UpperDatumHyp (F : UpperFieldLaws X) : Prop where
  two0 : ∀ f', RowHyp0 (lam2 F) f'
  two1 : ∀ f', RowHyp1 (lam2 F) f'
  one0 : ∀ f', RowHyp0 (lam1 F) f'
  one1 : ∀ f', RowHyp1 (lam1 F) f'

/-- The two-layer slice weights of the coordinate `0` at `t₁` and of the coordinate `1` at
`t₀`, and the one-layer ones. -/
def sliceW0 (W : UpperWeights) (t1 : Ty) : Ty → ℝ := fun s => wTy W s t1
def sliceW1 (W : UpperWeights) (t0 : Ty) : Ty → ℝ := fun s => wTy W t0 s
def sliceV0 (W : UpperWeights) (t1 : Ty) : Ty → ℝ := fun s => vTy W s t1
def sliceV1 (W : UpperWeights) (t0 : Ty) : Ty → ℝ := fun s => vTy W t0 s

/-- **Chamber cuts of both coordinates** (`lem:upper-reference-rp`(i), "Chamber cuts", via
`lem:five-type`(d),(e)): if every slice five-type measure of the two-layer and of the one-layer
row data is reflection positive at every chamber cut, then `μ̃_𝔅` is reflection positive at
every `ϑ_{0,a}` and every `ϑ_{1,a}`. -/
theorem upperTilde_chamber_positive (F : UpperFieldLaws X) (W : UpperWeights) {r : ℝ}
    (hr : 0 ≤ r) (H : UpperDatumHyp F)
    (s20 : ∀ t1, RPAll ((rowD0 (lam2 F) (fieldOf t1) (H.two0 _)).Q (graded (sliceW0 W t1) r)))
    (s21 : ∀ t0, RPAll ((rowD1 (lam2 F) (fieldOf t0) (H.two1 _)).Q (graded (sliceW1 W t0) r)))
    (s10 : ∀ t1, RPAll ((rowD0 (lam1 F) (fieldOf t1) (H.one0 _)).Q (graded (sliceV0 W t1) r)))
    (s11 : ∀ t0, RPAll ((rowD1 (lam1 F) (fieldOf t0) (H.one1 _)).Q (graded (sliceV1 W t0) r)))
    (i : ZMod 6) :
    (firstChamberCut i).Positive (upperTilde F W r) ∧
      (secondChamberCut i).Positive (upperTilde F W r) := by
  have h2 := two_coordinate_rp (lam2 F) (fun t0 t1 => wTy W t0 t1 * r ^ stateDeg t0 t1)
    (fun f' => rowD0 (lam2 F) f' (H.two0 f')) (fun f' => rowD1 (lam2 F) f' (H.two1 f'))
    (fun f' => rowDatum0 _ f' _) (fun f' => rowDatum1 _ f' _)
    (fun t1 => by
      rw [slice0_weights]
      exact rpAll_Q_smul _ (pow_nonneg hr _) (s20 t1))
    (fun t0 => by
      rw [slice1_weights]
      exact rpAll_Q_smul _ (pow_nonneg hr _) (s21 t0)) i
  have h1 := two_coordinate_rp (lam1 F) (fun t0 t1 => vTy W t0 t1 * r ^ stateDeg t0 t1)
    (fun f' => rowD0 (lam1 F) f' (H.one0 f')) (fun f' => rowD1 (lam1 F) f' (H.one1 f'))
    (fun f' => rowDatum0 _ f' _) (fun f' => rowDatum1 _ f' _)
    (fun t1 => by
      rw [slice0_weights]
      exact rpAll_Q_smul _ (pow_nonneg hr _) (s10 t1))
    (fun t0 => by
      rw [slice1_weights]
      exact rpAll_Q_smul _ (pow_nonneg hr _) (s11 t0)) i
  rw [upperTilde_eq_paired]
  exact ⟨h2.1.add ((Reserved.diag_positive_cut0 i h1.1).smul hr),
    h2.2.add ((Reserved.diag_positive_cut1 i h1.2).smul hr)⟩

/-- **`lem:upper-reference-rp`(i), (R2) at every cut of `𝔉`, from the slice positivity**: with
the chamber cuts of `upperTilde_chamber_positive` and V1's fold pairing at `ι` (layer caps and
`v_𝔱 ≥ k_𝔱 w_𝔱`), the upper reference `μ_𝔅 = μ̃_𝔅 / P_μ(r)` is reflection positive at every
cut of the family. -/
theorem upperReference_familyPositive_of_slices (F : UpperFieldLaws X) (W : UpperWeights)
    {r : ℝ} (hr : 0 ≤ r) (H : UpperDatumHyp F)
    (s20 : ∀ t1, RPAll ((rowD0 (lam2 F) (fieldOf t1) (H.two0 _)).Q (graded (sliceW0 W t1) r)))
    (s21 : ∀ t0, RPAll ((rowD1 (lam2 F) (fieldOf t0) (H.two1 _)).Q (graded (sliceW1 W t0) r)))
    (s10 : ∀ t1, RPAll ((rowD0 (lam1 F) (fieldOf t1) (H.one0 _)).Q (graded (sliceV0 W t1) r)))
    (s11 : ∀ t0, RPAll ((rowD1 (lam1 F) (fieldOf t0) (H.one1 _)).Q (graded (sliceV1 W t0) r)))
    (k : PType → PType → ℝ) (hcap : UpperLayerCaps F k r)
    (hdom : ∀ t₀ t₁, k t₀ t₁ * W.w t₀ t₁ ≤ W.v t₀ t₁) :
    TheoremC.FamilyReflectionPositive (signedIntegral (upperReference F W hr).weight) := by
  have hP : 0 ≤ (upPoly W r)⁻¹ := inv_nonneg.mpr (le_trans zero_le_one (one_le_upPoly W hr))
  intro c hc
  rw [upperReference_eq]
  rcases hc with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact (upperTilde_chamber_positive F W hr H s20 s21 s10 s11 a).1.smul hP
  · exact (upperTilde_chamber_positive F W hr H s20 s21 s10 s11 a).2.smul hP
  · exact (upperTilde_reserved_positive F W k hr hcap hdom).smul hP

/-! ## Valid inputs (V1)–(V3) -/

/-- **The inputs of an upper band are valid** (`subsec:upper-reference-rp`, (V1)–(V3)), for the
ordinary inputs `ord` (two-layer rows) and the reserved inputs `res` (one-layer rows), each an
input `(d, f, h, M)` per field type, and the caps `k_𝔱`:
* (V1) `root…`: the root envelope `Π_L ⪰_{ϑ₀} -d_φ r Π_{F₀}` of the row data at each field type
  `φ`, for both coordinates and both layer sets;
* (V2) `rows…`: the row data are valid (`ValidRows`) with the coefficients of `φ`;
* (V3) `caps`: every two-layer component satisfies `Π_{𝔱,φ} ⪰_ι -k_𝔱 r Diag_ι(Π⁽¹⁾_{𝔱,φ})`. -/
structure ValidInputs (F : UpperFieldLaws X) (H : UpperDatumHyp F) (r : ℝ)
    (ord res : FieldTy → CompletionInput) (k : PType → PType → ℝ) : Prop where
  root20 : ∀ f', RootEnv (rowD0 (lam2 F) f' (H.two0 f')) (ord f').d r
  root21 : ∀ f', RootEnv (rowD1 (lam2 F) f' (H.two1 f')) (ord f').d r
  root10 : ∀ f', RootEnv (rowD0 (lam1 F) f' (H.one0 f')) (res f').d r
  root11 : ∀ f', RootEnv (rowD1 (lam1 F) f' (H.one1 f')) (res f').d r
  rows20 : ∀ f', ValidRows (rowD0 (lam2 F) f' (H.two0 f')) r (ord f').f (ord f').h (ord f').M
  rows21 : ∀ f', ValidRows (rowD1 (lam2 F) f' (H.two1 f')) r (ord f').f (ord f').h (ord f').M
  rows10 : ∀ f', ValidRows (rowD0 (lam1 F) f' (H.one0 f')) r (res f').f (res f').h (res f').M
  rows11 : ∀ f', ValidRows (rowD1 (lam1 F) f' (H.one1 f')) r (res f').f (res f').h (res f').M
  caps : UpperLayerCaps F k r

/-- **The weight conditions on an upper band**, in the coordinates of `Ty`: the slice gates of
`eq:upper-slice` for the two-layer weights with the ordinary inputs and for the one-layer
weights with the reserved inputs, each at the field type of the other coordinate, the
domination `eq:independent-fold-domination`, and positivity of the `D` weights of every slice
(used by (c) and (f)). For the tail datum this is `tailDatum_gates` (`tailWeightsOK`). -/
structure WeightsOK (W : UpperWeights) (ord res : FieldTy → CompletionInput)
    (k : PType → PType → ℝ) : Prop where
  g20 : ∀ t1, SliceGates (ord (fieldOf t1)).d (ord (fieldOf t1)).f (ord (fieldOf t1)).h
    (ord (fieldOf t1)).M (sliceW0 W t1)
  g21 : ∀ t0, SliceGates (ord (fieldOf t0)).d (ord (fieldOf t0)).f (ord (fieldOf t0)).h
    (ord (fieldOf t0)).M (sliceW1 W t0)
  g10 : ∀ t1, SliceGates (res (fieldOf t1)).d (res (fieldOf t1)).f (res (fieldOf t1)).h
    (res (fieldOf t1)).M (sliceV0 W t1)
  g11 : ∀ t0, SliceGates (res (fieldOf t0)).d (res (fieldOf t0)).f (res (fieldOf t0)).h
    (res (fieldOf t0)).M (sliceV1 W t0)
  dom : ∀ t₀ t₁, k t₀ t₁ * W.w t₀ t₁ ≤ W.v t₀ t₁
  posW : ∀ t₀ t₁, 0 < W.w t₀ t₁
  posV : ∀ t₀ t₁, 0 < W.v t₀ t₁

/-- **`lem:upper-reference-rp`(i), reflection positivity**: if the inputs of an upper band are
valid on a block (`ValidInputs`, (V1)–(V3)), the row data form five-type data
(`UpperDatumHyp`), and the weights satisfy the gates of the band (`WeightsOK`), then `μ_𝔅` is
reflection positive at every cut of `𝔉` (the chamber cuts of both coordinates and `ι`). -/
theorem upperReference_familyPositive (F : UpperFieldLaws X) (W : UpperWeights) {r : ℝ}
    (hr : 0 < r) (H : UpperDatumHyp F) {ord res : FieldTy → CompletionInput}
    {k : PType → PType → ℝ} (hV : ValidInputs F H r ord res k) (hW : WeightsOK W ord res k) :
    TheoremC.FamilyReflectionPositive (signedIntegral (upperReference F W hr.le).weight) := by
  refine upperReference_familyPositive_of_slices F W hr.le H ?_ ?_ ?_ ?_ k hV.caps hW.dom
  · intro t1
    exact sliceRP_of_valid _ hr (fun s => (hW.posW _ _).le) (hW.posW _ _) (hV.rows20 _)
      (hV.root20 _) (hW.g20 t1)
  · intro t0
    exact sliceRP_of_valid _ hr (fun s => (hW.posW _ _).le) (hW.posW _ _) (hV.rows21 _)
      (hV.root21 _) (hW.g21 t0)
  · intro t1
    exact sliceRP_of_valid _ hr (fun s => (hW.posV _ _).le) (hW.posV _ _) (hV.rows10 _)
      (hV.root10 _) (hW.g10 t1)
  · intro t0
    exact sliceRP_of_valid _ hr (fun s => (hW.posV _ _).le) (hW.posV _ _) (hV.rows11 _)
      (hV.root11 _) (hW.g11 t0)

end Chamber

end Sarkozy.PartVLaws
