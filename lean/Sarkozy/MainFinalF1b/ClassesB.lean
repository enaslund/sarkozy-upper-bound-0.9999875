module

public import Sarkozy.MainFinalF1b.E1

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1b

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetLedger)

section Generic

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The class energies, indexed by the class data alone** (`thm:envelopes`(i),
`cor:envelope-costs`, `lem:bracket-energy`): B10's `ClassEnergyData` without `consistent`, `errK`,
`errw` (FA2 P2: they do not enter `JB`). *Hypotheses*: `energy` (analytic), `upper` (analytic). -/
structure ClassEnergyDataB (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (cd : ClassData D.CL) where
  /-- The labelled positive diagonals of the envelopes. -/
  Θ : ℕ → Type
  [ΘFintype : ∀ L, Fintype (Θ L)]
  /-- Their energies at a counterexample, and their upper prices. -/
  Z : ∀ L, Finset ℤ → Θ L → ℝ
  u : ∀ L, Θ L → ℝ
  /-- The weight of the class `i` on the diagonal `j`, nonnegative. -/
  wc : ∀ L, cd.ι L → Θ L → ℝ
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- The evaluated residual of a selection (the parts of its class bound not on a diagonal). -/
  ρ : ∀ L, Choice (D.CL.T L) → ℝ
  /-- **The class bounds at energy level**, robustly and uniformly in the classes. -/
  energy : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (∀ i, ∑ ω ∈ cd.clsSel L i, |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
        ∑ j, wc L i j * Z L A j +
          ∑ ω ∈ cd.clsSel L i, ((ρ L ω + ε L * monomial (D.CL.π L) ω) * D.Y L A + r L A ω)) ∧
      ∑ ω ∈ cd.sel L, r L A ω ≤ remainder c L A
  /-- The error weights of the upper prices. -/
  v : ∀ L, Θ L → ℝ
  /-- **The upper prices of the diagonals** (`lem:bracket-energy`, (E1)). -/
  upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
    ∃ r : ∀ L, Finset ℤ → Θ L → ℝ, (∀ L A j, 0 ≤ r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ j, Z L A j ≤ (u L j + ε₃ L * v L j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ j, (∑ i, wc L i j) * r L A j ≤ remainder c₃ L A)

attribute [instance] ClassEnergyDataB.ΘFintype

namespace ClassEnergyDataB

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {cd : ClassData D.CL}
  (ED : ClassEnergyDataB D cd)

/-- The diagonal weights `w_j = ∑_i w_{ij}`. -/
noncomputable def w (L : ℕ) (j : ED.Θ L) : ℝ := ∑ i, ED.wc L i j

/-- The comparison constant off the diagonals:
`κ_L = ∑_{ω in no class} B π_ω + ∑_{ω in a class} ρ_ω`. -/
noncomputable def κ (L : ℕ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
    (if cd.cls L ω = none then D.B * monomial (D.CL.π L) ω else ED.ρ L ω)

omit [DecidableEq P] in
/-- **The term-level comparison bound** (`lem:record:record-expansion`(ii) at energy level): from
the class bounds at energy level and (E1) off the classes,
`∑_ω |I_ω| ≤ ∑_j w_j Z_j + (κ_L + o(1)) Y + rem`. -/
theorem terms (hE1 : D.EnvelopeBoundNonneg) :
    ∃ ε₁ : ℕ → ℝ, Tendsto ε₁ atTop (𝓝 0) ∧ ∃ c₁ : ℝ, 0 ≤ c₁ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
            |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
          ∑ j, ED.w L j * ED.Z L A j + (ED.κ L + ε₁ L) * D.Y L A + remainder c₁ L A := by
  obtain ⟨εE, hεE0, hεE, cE, hcE, rE, hrE0, hE1a, hE1b⟩ := hE1
  obtain ⟨ε, hε, c, hc, r, hr0, hcb⟩ := ED.energy
  set X : ℝ := Real.exp D.CL.S * Real.cosh D.CL.A - 1 with hX
  refine ⟨fun L => (εE L + |ε L|) * X, ?_, cE + c, add_nonneg hcE hc, ?_⟩
  · have h := (hεE.add hε.abs).mul_const X
    simpa only [abs_zero, add_zero, zero_mul] using h
  filter_upwards [hE1a, hE1b, hcb] with L h1 h2 h3
  intro C hC hind A hA hcount
  have hE := h1 C hC hind A hA hcount
  have hrsum := h2 C hC hind A hA hcount
  obtain ⟨hcls, hrcls⟩ := h3 C hC hind A hA hcount
  have hY : 0 < D.Y L A := TheoremCParam.counterexample_pos hC hcount
  have hπ : ∀ b t e, 0 ≤ D.CL.π L b t e := fun b t e =>
    mul_nonneg (D.CL.πt_nonneg L b t e) (D.selectionFactor_nonneg L b)
  set sel := univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω) with hsel
  have hfree : ∀ ω ∈ sel, cd.cls L ω = none →
      |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
        (D.B + εE L) * monomial (D.CL.π L) ω * D.Y L A +
          monomial (D.CL.πt L) ω * rE L A ω := by
    intro ω hω _
    have hω' : IsSelection ω := (mem_filter.mp hω).2
    have h1' : |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
        monomial (D.CL.πt L) ω *
          diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) :=
      abs_term_le_envelope (c := reservedCut) (N := D.GB.N L) (D := D.CL.D L)
        (D.GB.bracket L) (D.CL.bracket L) (blockLift m₀ blk p L A) ω
    have hm : 0 ≤ monomial (D.CL.πt L) ω := monomial_nonneg (D.CL.πt_nonneg L) ω
    have h2' := mul_le_mul_of_nonneg_left (hE ω hω') hm
    have hmono : monomial (D.CL.π L) ω =
        monomial (D.CL.πt L) ω * ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b :=
      monomial_mul_selectionFactor _ _ ω
    calc |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω|
        ≤ _ := h1'
      _ ≤ _ := h2'
      _ = (D.B + εE L) * monomial (D.CL.π L) ω * D.Y L A +
            monomial (D.CL.πt L) ω * rE L A ω := by rw [hmono]; ring
  have hsplit := sum_abs_le_split sel (cd.cls L)
    (fun ω => |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω|)
    (fun ω => monomial (D.CL.π L) ω) (ED.ρ L) (fun ω => monomial (D.CL.πt L) ω * rE L A ω)
    (r L A) (ED.wc L) (ED.Z L A) (B := D.B) (εE := εE L) (ε := ε L) (Y := D.Y L A)
    (fun ω => monomial_nonneg hπ ω)
    (fun ω => mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (hrE0 L A ω))
    (hr0 L A) hY.le (hεE0 L) hfree hcls
  -- the monomials and the remainders
  have hS : ∑ b, symTotal (D.CL.π L) b ≤ D.CL.S := D.CL.S_total L
  have hA' : ∑ b, skewTotal (D.CL.π L) b ≤ D.CL.A := D.CL.A_total L
  have hA0 : 0 ≤ ∑ b, skewTotal (D.CL.π L) b :=
    sum_nonneg fun b _ => sum_nonneg fun t _ => hπ b t _
  have hmon : ∑ ω ∈ sel, monomial (D.CL.π L) ω ≤ X := by
    have h1 := sum_monomial_selections_le (T := D.CL.T L) hπ
    have h2 := exp_mul_cosh_le_of_le hS hA0 hA'
    rw [hX]
    linarith
  have hz0 : 0 ≤ εE L + |ε L| := add_nonneg (hεE0 L) (abs_nonneg _)
  have hmonY : (εE L + |ε L|) * (∑ ω ∈ sel, monomial (D.CL.π L) ω) * D.Y L A ≤
      (εE L + |ε L|) * X * D.Y L A :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmon hz0) hY.le
  have hrem : ∑ ω ∈ sel, (monomial (D.CL.πt L) ω * rE L A ω + r L A ω) ≤
      remainder cE L A + remainder c L A := by
    rw [sum_add_distrib]
    exact add_le_add hrsum hrcls
  rw [JointClosing.remainder_add]
  have hw : ∑ j, (∑ i, ED.wc L i j) * ED.Z L A j = ∑ j, ED.w L j * ED.Z L A j := rfl
  unfold κ
  linarith

end ClassEnergyDataB

/-- **The combined gate** (`cor:joint-closing`; E4's `AllocJ` at `ClassEnergyDataB`):
`Δ ≤ ∑_j b_j u_j + 63 (𝓔 − κ_L − ∑_j w_j u_j)` at every scale. -/
def AllocJB {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {cd : ClassData D.CL}
    (ED : ClassEnergyDataB D cd) (b : ∀ L, ED.Θ L → ℝ) : Prop :=
  ∀ L, ledgerDelta targetLedger ≤
    ∑ j, b L j * ED.u L j + 63 * (targetLedger.E - (ED.κ L + ∑ j, ED.w L j * ED.u L j))


omit [DecidableEq P] in
/-- **`JB` from the class bounds and the combined gate** (`cor:joint-closing` at `k = 6`,
`eq:final-joint-closing`): B4's `jointBound_target_of_classEnergy` with (G1) and (G2) replaced by
`AllocJ`. Neither the polynomial data nor `B ≤ B^{ledger}` is used: their role is inside the proof
of `AllocJ` (in the paper, the completion of the residual series). -/
theorem jointBound_allocJB (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hcard : Fintype.card E = 6) {cd : ClassInputsPaper.ClassData D.CL}
    (ED : ClassEnergyDataB D cd) (hE1 : D.EnvelopeBoundNonneg)
    (b v : ∀ L, ED.Θ L → ℝ)
    (hmean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, b L j * ED.Z L A j - remainder c₂ L A ≤
          (energyMean (blockLift m₀ blk p) D.ME.ML L A +
            energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2)
    (hupper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
      (∀ L, ∑ j, (63 * ED.w L j - b L j) * v L j ≤ V) ∧ ∃ r : ∀ L, Finset ℤ → ED.Θ L → ℝ,
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∀ j, ED.Z L A j ≤ (ED.u L j + ε₃ L * v L j) * D.Y L A + r L A j) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ j, (63 * ED.w L j - b L j) * r L A j ≤ remainder c₃ L A))
    (hresid : ∀ L j, b L j ≤ 63 * ED.w L j) (halloc : AllocJB ED b) :
    JointBound D targetLedger.jointConstant := by
  have h63 : (2 : ℝ) ^ Fintype.card E - 1 = 63 := by rw [hcard]; norm_num
  have h64 : (2 : ℝ) ^ Fintype.card E = 64 := by rw [hcard]; norm_num
  refine jointBound_of_classes_gate D ED.Θ ED.Z ED.w b ED.u v ED.κ targetLedger.m₁
    (ED.terms hE1) hmean (by rw [h63]; exact hupper) (by rw [h63]; exact hresid) ?_
  intro L
  rw [h63, h64]
  have hg := jointConstant_gate targetLedger
  have h2 := halloc L
  have e : ∑ i, (63 * ED.w L i - b L i) * ED.u L i =
      63 * ∑ i, ED.w L i * ED.u L i - ∑ i, b L i * ED.u L i := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e]
  unfold ledgerDelta at h2
  norm_num at hg
  linarith



omit [DecidableEq P] in
/-- **K2's field 45 along the paper's labels** (E4's `resid_of_labels` at `ClassEnergyDataB`). -/
theorem resid_of_labelsB {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassInputsPaper.ClassData D.CL} {ED : ClassEnergyDataB D cd}
    (b : ∀ L, ED.Θ L → ℝ) (lab : ∀ L, ED.Θ L → PaperDiag)
    (hb : ∀ L j, b L j ≤ diagB (lab L j)) (hw : ∀ L j, (diagW (lab L j) : ℝ) ≤ ED.w L j) :
    ∀ L j, b L j ≤ 63 * ED.w L j := by
  intro L j
  have h1 : ((diagB (lab L j) + 2366 / 100 : ℚ) : ℝ) < ((63 * diagW (lab L j) : ℚ) : ℝ) := by
    exact_mod_cast diag_resid (lab L j)
  push_cast at h1
  linarith [hb L j, hw L j]

/-- **The joint mean allocation in the paper's form** (`cor:joint-closing`,
`prop:joint-middle-mean`, `prop:joint-upper-mean`): B10's `MeanData` with the allocation gate
replaced by the combined residual gate `AllocJ`. *Hypotheses*: `mean` (J2,
`prop:record:mean-credit`), `hV`, `resid`, `alloc` (`AllocJ`). -/
structure MeanDataJB {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassInputsPaper.ClassData D.CL} (ED : ClassEnergyDataB D cd) where
  b : ∀ L, ED.Θ L → ℝ
  b_nonneg : ∀ L j, 0 ≤ b L j
  mean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, b L j * ED.Z L A j - remainder c₂ L A ≤
        (energyMean (blockLift m₀ blk p) D.ME.ML L A +
          energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2
  V : ℝ
  hV : ∀ L, ∑ j, (63 * ED.w L j - b L j) * ED.v L j ≤ V
  resid : ∀ L j, b L j ≤ 63 * ED.w L j
  /-- **The combined gate** `Δ ≤ ∑ b u + 63(𝓔 − κ_L − ∑ w u)`. -/
  alloc : AllocJB ED b

namespace MeanDataJB

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
  {cd : ClassInputsPaper.ClassData D.CL} {ED : ClassEnergyDataB D cd}


omit [DecidableEq P] in
/-- (J3) from the upper prices of `ED` (B10's `MeanData.upper`, same proof). -/
theorem upper (MJ : MeanDataJB ED) :
    ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
    (∀ L, ∑ j, (63 * ED.w L j - MJ.b L j) * ED.v L j ≤ V) ∧
    ∃ r : ∀ L, Finset ℤ → ED.Θ L → ℝ,
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ j, ED.Z L A j ≤ (ED.u L j + ε₃ L * ED.v L j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ j, (63 * ED.w L j - MJ.b L j) * r L A j ≤ remainder c₃ L A) := by
  obtain ⟨ε₃, hε₃0, hε₃, c₃, hc₃, r, hr0, hU, hUr⟩ := ED.upper
  refine ⟨ε₃, hε₃0, hε₃, MJ.V, 63 * c₃, by positivity, MJ.hV, r, hU, ?_⟩
  filter_upwards [hUr] with L hL
  intro C hC hind A hA hcount
  have h := hL C hC hind A hA hcount
  have hle : ∑ j, (63 * ED.w L j - MJ.b L j) * r L A j ≤
      63 * ∑ j, (∑ i, ED.wc L i j) * r L A j := by
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    have := mul_nonneg (MJ.b_nonneg L j) (hr0 L A j)
    have e : ED.w L j = ∑ i, ED.wc L i j := rfl
    rw [e]
    nlinarith
  have e3 : remainder (63 * c₃) L A = 63 * remainder c₃ L A := by
    unfold remainder
    ring
  rw [e3]
  linarith

omit [DecidableEq P] in
/-- **`JB` from the class data with the combined gate** (`cor:joint-closing`,
`eq:final-joint-closing`): `jointBound_target_allocJ` at `ED.toCI`, `ED.toCE`. -/
theorem jointBound (MJ : MeanDataJB ED) (hcard : Fintype.card E = 6)
    (hE1 : D.EnvelopeBoundNonneg) : JointBound D targetLedger.jointConstant :=
  jointBound_allocJB D hcard ED hE1 MJ.b ED.v MJ.mean MJ.upper MJ.resid MJ.alloc

/-- **`MeanDataJ` with fields 44 and 45 proved**: the paper's mean coefficients along a labelling
by `PaperDiag`, `V := 63 N W V_v` (`hV_of_bounds`), `resid` by `resid_of_labels`. *Hypotheses*:
`mean` (analytic), `alloc` (`AllocJ`), and the bounds. -/
noncomputable def ofE4 (ED : ClassEnergyDataB D cd) (lab : ∀ L, ED.Θ L → PaperDiag)
    (hw : ∀ L j, (diagW (lab L j) : ℝ) ≤ ED.w L j)
    (N : ℕ) (W Vv : ℝ) (hW : 0 ≤ W) (hVv : 0 ≤ Vv) (hcard : ∀ L, Fintype.card (ED.Θ L) ≤ N)
    (hwW : ∀ L j, ED.w L j ≤ W) (hv0 : ∀ L j, 0 ≤ ED.v L j) (hvV : ∀ L j, ED.v L j ≤ Vv)
    (mean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, (diagB (lab L j) : ℝ) * ED.Z L A j -
            remainder c₂ L A ≤
          (energyMean (blockLift m₀ blk p) D.ME.ML L A +
            energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2)
    (alloc : AllocJB ED fun L j => (diagB (lab L j) : ℝ)) :
    MeanDataJB ED where
  b L j := (diagB (lab L j) : ℝ)
  b_nonneg L j := by exact_mod_cast diagB_nonneg (lab L j)
  mean := mean
  V := 63 * N * W * Vv
  hV := hV_of_bounds ED.w (fun L j => (diagB (lab L j) : ℝ)) ED.v N W Vv hW hVv hcard hwW
    (fun L j => by exact_mod_cast diagB_nonneg (lab L j)) hv0 hvV
  resid := resid_of_labelsB _ lab (fun _ _ => le_rfl) hw
  alloc := alloc

end MeanDataJB




end Generic

end Sarkozy.MainFinalF1b
