module

public import Sarkozy.ClassData.JointGate

@[expose] public section

/-!
# B10's `MeanData` with the relaxed allocation (field 46 in the paper's form)

`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`; `paper/sections/24a_joint_mean.tex`,
`prop:joint-middle-mean`, `prop:joint-upper-mean`, "Residual coefficients".

* **`MeanDataJ ED`**: B10's `MeanData ED` with `alloc` replaced by `AllocJ` (the combined gate
  `63 κ_L + ∑ (63 w − b) u ≤ 63 𝓔 − 64 Δ` of `cor:joint-closing`).
* **`MeanDataJ.ofMeanData`**: every B10 `MeanData` gives one, given `PD` and `B ≤ B^{ledger}` (so
  this is a weakening).
* **`MeanDataJ.jointBound`**: `JB` (`cor:joint-closing`) from `MeanDataJ` and (E1); the same
  conclusion as B10's `MeanData.jointBound`.
* **`MeanDataJ.ofE4`**: with the paper's mean coefficients along a labelling by `PaperDiag`, with
  fields 44 (`hV`) and 45 (`resid`) proved.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassData

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.Comparison Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetLedger)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The joint mean allocation in the paper's form** (`cor:joint-closing`,
`prop:joint-middle-mean`, `prop:joint-upper-mean`): B10's `MeanData` with the allocation gate
replaced by the combined residual gate `AllocJ`. *Hypotheses*: `mean` (J2,
`prop:record:mean-credit`), `hV`, `resid`, `alloc` (`AllocJ`). -/
structure MeanDataJ {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassInputsPaper.ClassData D.CL} (ED : ClassEnergyData D cd) where
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
  alloc : AllocJ ED.toCE b

namespace MeanDataJ

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
  {cd : ClassInputsPaper.ClassData D.CL} {ED : ClassEnergyData D cd}

omit [DecidableEq P] in
/-- B10's `MeanData` gives a `MeanDataJ` (`allocJ_of_alloc`): the combined gate is weaker. -/
noncomputable def ofMeanData (PD : PolynomialData ED.toCI) (hB : D.B ≤ targetLedger.B)
    (MD : MeanData ED) : MeanDataJ ED where
  b := MD.b
  b_nonneg := MD.b_nonneg
  mean := MD.mean
  V := MD.V
  hV := MD.hV
  resid := MD.resid
  alloc := allocJ_of_alloc ED.toCE PD hB MD.b MD.alloc

omit [DecidableEq P] in
/-- (J3) from the upper prices of `ED` (B10's `MeanData.upper`, same proof). -/
theorem upper (MJ : MeanDataJ ED) :
    ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
    (∀ L, ∑ j, (63 * ED.toCE.w L j - MJ.b L j) * ED.v L j ≤ V) ∧
    ∃ r : ∀ L, Finset ℤ → ED.Θ L → ℝ,
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ j, ED.toCE.Z L A j ≤ (ED.toCE.u L j + ε₃ L * ED.v L j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ j, (63 * ED.toCE.w L j - MJ.b L j) * r L A j ≤ remainder c₃ L A) := by
  obtain ⟨ε₃, hε₃0, hε₃, c₃, hc₃, r, hr0, hU, hUr⟩ := ED.upper
  refine ⟨ε₃, hε₃0, hε₃, MJ.V, 63 * c₃, by positivity, MJ.hV, r, hU, ?_⟩
  filter_upwards [hUr] with L hL
  intro C hC hind A hA hcount
  have h := hL C hC hind A hA hcount
  have hle : ∑ j, (63 * ED.toCE.w L j - MJ.b L j) * r L A j ≤
      63 * ∑ j, (∑ i, ED.wc L i j) * r L A j := by
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    have := mul_nonneg (MJ.b_nonneg L j) (hr0 L A j)
    have e : ED.toCE.w L j = ∑ i, ED.wc L i j := rfl
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
theorem jointBound (MJ : MeanDataJ ED) (hcard : Fintype.card E = 6)
    (hE1 : D.EnvelopeBoundNonneg) : JointBound D targetLedger.jointConstant :=
  jointBound_target_allocJ D hcard ED.toCE hE1 MJ.b ED.v MJ.mean MJ.upper MJ.resid MJ.alloc

/-- **`MeanDataJ` with fields 44 and 45 proved**: the paper's mean coefficients along a labelling
by `PaperDiag`, `V := 63 N W V_v` (`hV_of_bounds`), `resid` by `resid_of_labels`. *Hypotheses*:
`mean` (analytic), `alloc` (`AllocJ`), and the bounds. -/
noncomputable def ofE4 (ED : ClassEnergyData D cd) (lab : ∀ L, ED.Θ L → PaperDiag)
    (hw : ∀ L j, (diagW (lab L j) : ℝ) ≤ ED.w L j)
    (N : ℕ) (W Vv : ℝ) (hW : 0 ≤ W) (hVv : 0 ≤ Vv) (hcard : ∀ L, Fintype.card (ED.Θ L) ≤ N)
    (hwW : ∀ L j, ED.w L j ≤ W) (hv0 : ∀ L j, 0 ≤ ED.v L j) (hvV : ∀ L j, ED.v L j ≤ Vv)
    (mean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, (diagB (lab L j) : ℝ) * ED.Z L A j -
            remainder c₂ L A ≤
          (energyMean (blockLift m₀ blk p) D.ME.ML L A +
            energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2)
    (alloc : AllocJ ED.toCE fun L j => (diagB (lab L j) : ℝ)) :
    MeanDataJ ED where
  b L j := (diagB (lab L j) : ℝ)
  b_nonneg L j := by exact_mod_cast diagB_nonneg (lab L j)
  mean := mean
  V := 63 * N * W * Vv
  hV := hV_of_bounds ED.w (fun L j => (diagB (lab L j) : ℝ)) ED.v N W Vv hW hVv hcard hwW
    (fun L j => by exact_mod_cast diagB_nonneg (lab L j)) hv0 hvV
  resid := resid_of_labels _ lab (fun _ _ => le_rfl) hw
  alloc := alloc

end MeanDataJ

end Sarkozy.ClassData
