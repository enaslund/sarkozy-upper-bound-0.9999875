module

public import Sarkozy.ClassData.Gates
public import Sarkozy.MainFinal2.Bundles

@[expose] public section

/-!
# Constructors for K2's `ClassEnergySteps` and B10's `MeanData` with fields 41, 42, 44, 45 done

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i), `cor:envelope-costs`;
`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean`;
`paper/sections/11_comparison_proof.tex`,
`cor:joint-closing`.

* **`ClassEnergySteps.ofE4`**: K2's `ClassEnergySteps D cd` from the diagonals, the operator
  steps `ops` (analytic), `ConsistentInputs` (analytic; field 41 follows by
  `ConsistentInputs.consistent`, with `classCost ≤ C_n` kernel-checked), the price comparison
  `hyπ` (field 42 follows by `errw_of_inputs`, with `v = u` and `errK = 3 · eUhi · K_π`) and the
  upper prices `upper` in relative form (`v = u`; analytic).
* **`MeanData.ofE4`**: B10's `MeanData ED` with `b` the paper's mean coefficients along a labelling
  of the diagonals by `PaperDiag` (`b_nonneg` and field 45 `resid` proved, `resid_of_labels`),
  `V := 63 · N · W · V_v` with field 44 `hV` proved (`hV_of_bounds`), and the analytic `mean`
  and field 46 `alloc` as inputs. (See the report for why `alloc` is kept as an input.)
-/

open Filter Finset
open scoped Topology

namespace Sarkozy.ClassData

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.MainFinal2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Comparison (remainder energyMean)
open Sarkozy.BlockFrame
open Sarkozy.Param (Params)
open Sarkozy.TargetLedger (targetLedger)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **K2's `ClassEnergySteps` with fields 41 and 42 proved** from their analytic inputs.
*Hypotheses*: `ops` (B11's operator steps), `H` (`ConsistentInputs`: background gate, remainder
bound, price identities, variance classes), `hyπ` (`mono(y^arm) ≤ K_π π`), `upper`
(`lem:bracket-energy` with `v = u`). -/
noncomputable def ClassEnergySteps.ofE4 {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    (cd : ClassInputsPaper.ClassData D.CL) (Θ : ℕ → Type) [∀ L, Fintype (Θ L)]
    (Z : ∀ L, Finset ℤ → Θ L → ℝ) (u : ∀ L, Θ L → ℝ) (wc : ∀ L, cd.ι L → Θ L → ℝ)
    (wc_nonneg : ∀ L i j, 0 ≤ wc L i j) (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd Θ Z wc ρ) (H : ConsistentInputs cd Θ wc u ρ) (Kπ : ℝ) (hK : 0 ≤ Kπ)
    (hyπ : ∀ L (n : {n // n ∈ cd.N}), ∀ ω ∈ cd.clsSel L (.inl n),
      mono (cd.yarm L) (selMono ω) ≤ Kπ * monomial (D.CL.π L) ω)
    (upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
      ∃ r : ∀ L, Finset ℤ → Θ L → ℝ, (∀ L A j, 0 ≤ r L A j) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∀ j, Z L A j ≤ (u L j + ε₃ L * u L j) * D.Y L A + r L A j) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ j, (∑ i, wc L i j) * r L A j ≤ remainder c₃ L A)) :
    ClassEnergySteps D cd where
  Θ := Θ
  Z := Z
  u := u
  wc := wc
  wc_nonneg := wc_nonneg
  ρ := ρ
  ops := ops
  consistent := H.consistent
  v := u
  errK := 3 * (eUhi : ℝ) * Kπ
  errw := errw_of_inputs H Kπ hK hyπ
  upper := upper

/-- **B10's `MeanData` with fields 44 and 45 proved** (`cor:joint-closing`,
`prop:joint-middle-mean`): the retained mean coefficients are the paper's (`diagB`) along a
labelling `lab` of the diagonals, whose weights are at least the paper's (`hw`); the gate `V` is
`63 N W V_v` from uniform bounds. *Hypotheses*: `mean` (J2, `prop:record:mean-credit`; analytic),
`alloc` (field 46), and the bounds `hcard`, `hwW`, `hv0`, `hvV`. -/
noncomputable def MeanData.ofE4 {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassInputsPaper.ClassData D.CL} (ED : ClassEnergyData D cd)
    (lab : ∀ L, ED.Θ L → PaperDiag) (hw : ∀ L j, (diagW (lab L j) : ℝ) ≤ ED.w L j)
    (N : ℕ) (W Vv : ℝ) (hW : 0 ≤ W) (hVv : 0 ≤ Vv) (hcard : ∀ L, Fintype.card (ED.Θ L) ≤ N)
    (hwW : ∀ L j, ED.w L j ≤ W) (hv0 : ∀ L j, 0 ≤ ED.v L j) (hvV : ∀ L j, ED.v L j ≤ Vv)
    (mean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, (diagB (lab L j) : ℝ) * ED.Z L A j -
            remainder c₂ L A ≤
          (energyMean (blockLift m₀ blk p) D.ME.ML L A +
            energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2)
    (alloc : ∀ L, ledgerDelta targetLedger ≤ ∑ j, (diagB (lab L j) : ℝ) * ED.u L j) :
    MeanData ED where
  b L j := (diagB (lab L j) : ℝ)
  b_nonneg L j := by exact_mod_cast diagB_nonneg (lab L j)
  mean := mean
  V := 63 * N * W * Vv
  hV := hV_of_bounds ED.w (fun L j => (diagB (lab L j) : ℝ)) ED.v N W Vv hW hVv hcard hwW
    (fun L j => by exact_mod_cast diagB_nonneg (lab L j)) hv0 hvV
  resid := resid_of_labels _ lab (fun _ _ => le_rfl) hw
  alloc := alloc

end Sarkozy.ClassData
