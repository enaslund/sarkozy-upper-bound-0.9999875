module

public import Sarkozy.ClassData.Gates

@[expose] public section

/-!
# The joint mean allocation as the paper states it: the combined residual gate (field 46)

`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`; `paper/sections/24a_joint_mean.tex`,
`prop:joint-middle-mean` (proof, last paragraph), `prop:joint-upper-mean`;
`paper/sections/32_four_routes_closing.tex`, `eq:final-joint-closing`.

B4's `jointBound_of_classes` asks for two separate gates at every scale:
(G1) `κ'_L + ∑_j w_j u_j ≤ 𝓔` and (G2) `Δ ≤ ∑_j b_j u_j` (B10's `MeanData.alloc`, K2's field 46).
The paper proves neither (G2) nor a lower bound for an isolated upper-priced mean term
(`prop:joint-middle-mean`: "they are not separate lower bounds obtained by substituting upper prices
in a mean energy"). It proves the **combined** inequality: the residual series `∑ (63c − b) u` over
the labelled diagonals, whose coefficients are nonnegative, is at most its completion with repeated
block labels, and the completion equals `63 𝓔 − 64Δ` with `Δ` the exponential series of
`prop:joint-middle-mean`. Over distinct labels `∑ b u` is in general *strictly below* the completed
mean series (e.g. `∑_{B<B'} x_B x_{B'} < x²/2`), so (G2) at the ledger's `Δ` is a strengthening
(see the report).

Here:
* **`jointBound_of_classes_gate`**: B4's theorem with (G1), (G2), `hH` replaced by the combined gate
  `(2^k − 1) κ'_L + ∑ ((2^k − 1) w − b) u ≤ 2^k H − 1 + m₁` (B4's `JointAllocL.gate`). The
  comparison step is B4's, copied verbatim.
* **`G1_Psi`**: B4's `ClassEnergyInputs.G1` stopped one step earlier, at the completion polynomial:
  `κ_L + ∑ w u ≤ Ψ_L(π̂, ŷ)` (`(PD.U L).Psi`).
* **`AllocJ`**: the combined gate in allocation form,
  `Δ ≤ ∑_j b_j u_j + 63 (𝓔 − κ_L − ∑_j w_j u_j)`; **`jointBound_target_allocJ`** proves `JB` from
  it (without `PD` and `hB`, whose role moves into the proof of the gate).
* **`AllocJΨ`**: the intermediate form `Δ ≤ ∑_j b_j u_j + 63 (𝓔 − Ψ_L)`, which keeps `PD` in the
  chain. B10's `alloc` ⇒ `AllocJΨ` ⇒ `AllocJ` (`allocJΨ_of_alloc`, `allocJ_of_allocJΨ`,
  `allocJ_of_alloc`), so nothing is lost.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassData

open Sarkozy.ClassBoundsPaper
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetLedger)

attribute [local instance] TheoremCBlock.ClassBounds.ιFintype TheoremCBlock.ClassBounds.ιDecEq
  TheoremCBlock.ClassBounds.JauxFintype TheoremCBlock.ClassBounds.JauxDecEq

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`JointBound` from the class bounds and the combined residual gate** (`cor:joint-closing`):
B4's `jointBound_of_classes` with (G1), (G2) and the closing gate replaced by the single gate of
B4's `JointAllocL`. -/
theorem jointBound_of_classes_gate (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {H : ℝ}
    (ι : ℕ → Type) [∀ L, Fintype (ι L)] (Z : ∀ L, Finset ℤ → ι L → ℝ) (w b u v : ∀ L, ι L → ℝ)
    (κ' : ℕ → ℝ) (m₁ : ℝ)
    (hterms : ∃ ε₁ : ℕ → ℝ, Tendsto ε₁ atTop (𝓝 0) ∧ ∃ c₁ : ℝ, 0 ≤ c₁ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
            |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
          ∑ i, w L i * Z L A i + (κ' L + ε₁ L) * D.Y L A + remainder c₁ L A)
    (hmean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        (m₁ - ε₂ L) * D.Y L A + ∑ i, b L i * Z L A i - remainder c₂ L A ≤
          (energyMean (blockLift m₀ blk p) D.ME.ML L A +
            energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2)
    (hupper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
      (∀ L, ∑ i, ((2 ^ Fintype.card E - 1) * w L i - b L i) * v L i ≤ V) ∧
      ∃ r : ∀ L, Finset ℤ → ι L → ℝ,
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∀ i, Z L A i ≤ (u L i + ε₃ L * v L i) * D.Y L A + r L A i) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ i, ((2 ^ Fintype.card E - 1) * w L i - b L i) * r L A i ≤ remainder c₃ L A))
    (hresid : ∀ L i, b L i ≤ (2 ^ Fintype.card E - 1) * w L i)
    (hgate : ∀ L, (2 ^ Fintype.card E - 1) * κ' L +
      ∑ i, ((2 ^ Fintype.card E - 1) * w L i - b L i) * u L i ≤
        2 ^ Fintype.card E * H - 1 + m₁) :
    JointBound D H := by
  have hk : (0 : ℝ) ≤ 2 ^ Fintype.card E - 1 := by
    have : (1 : ℝ) ≤ 2 ^ Fintype.card E := one_le_pow₀ (by norm_num)
    linarith
  refine JointAllocL.jointBound (D := D) (H := H)
    { ι := ι, Z := Z, c := fun L i => (2 ^ Fintype.card E - 1) * w L i, b := b,
      κ := fun L => (2 ^ Fintype.card E - 1) * κ' L, m₁ := m₁, comparison := ?_, mean := hmean,
      u := u, v := v, upper := hupper, resid_nonneg := hresid, gate := hgate }
  · obtain ⟨ε₁, hε₁, c₁, hc₁, h1⟩ := hterms
    have hlim : Tendsto (fun L => (2 ^ Fintype.card E - 1) * ε₁ L) atTop (𝓝 0) := by
      simpa using hε₁.const_mul ((2 : ℝ) ^ Fintype.card E - 1)
    refine ⟨fun L => (2 ^ Fintype.card E - 1) * ε₁ L, hlim, (2 ^ Fintype.card E - 1) * c₁,
      mul_nonneg hk hc₁, ?_⟩
    unfold Param.AtCounterexamples at h1 ⊢
    filter_upwards [h1] with L hL
    intro C hC hkk A hAd hY
    have e1 := hL C hC hkk A hAd hY
    have hexp := energy_sub_eq_sum_selections reservedCut (D.nu_eq L) (D.GB.lam_sym L)
      (fun b t => isSymmetricAt_symPart _ _) (fun b t => isSkewAt_skewPart _ _)
      (blockLift m₀ blk p L A)
    have hnueq : energyComparison D.CL.ν (blockLift m₀ blk p) L A =
        diagonalIntegral (tensorLaw (D.CL.ν L)) (blockLift m₀ blk p L A) :=
      Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
    have hlameq : energyFirst D.FS.lam (blockLift m₀ blk p) L A =
        diagonalIntegral (tensorLaw (D.FS.lam L)) (blockLift m₀ blk p L A) :=
      Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
    have hdiff : energyFirst D.FS.lam (blockLift m₀ blk p) L A -
        energyComparison D.CL.ν (blockLift m₀ blk p) L A ≤
        ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
          |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| := by
      rw [hnueq, hlameq]
      have h' : diagonalIntegral (tensorLaw (D.FS.lam L)) (blockLift m₀ blk p L A) -
          diagonalIntegral (tensorLaw (D.CL.ν L)) (blockLift m₀ blk p L A) =
          -∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
            term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω := by
        rw [← hexp]
        ring
      rw [h']
      exact (neg_le_abs _).trans (Finset.abs_sum_le_sum_abs _ _)
    have hstep := mul_le_mul_of_nonneg_left (hdiff.trans e1) hk
    have e2 : (2 ^ Fintype.card E - 1) * (∑ i, w L i * Z L A i + (κ' L + ε₁ L) * D.Y L A +
        remainder c₁ L A) = ∑ i, (2 ^ Fintype.card E - 1) * w L i * Z L A i +
        ((2 ^ Fintype.card E - 1) * κ' L + (2 ^ Fintype.card E - 1) * ε₁ L) * D.Y L A +
        (2 ^ Fintype.card E - 1) * remainder c₁ L A := by
      rw [mul_add, mul_add, mul_sum]
      simp only [mul_assoc]
      ring
    rw [remainder_smul]
    linarith

omit [DecidableEq P] in
/-- **(G1) at the completion polynomial** (B4's `ClassEnergyInputs.G1`, stopped before
`Psi_le_E`): `κ_L + ∑_j w_j u_j ≤ Ψ_L(π̂, ŷ)` (`prop:closing-data`(d),
`lem:record:record-expansion`). -/
theorem G1_Psi {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {CI : ClassInputs D.CL}
    (CE : ClassEnergyInputs D CI) (PD : PolynomialData CI) (hB : D.B ≤ targetLedger.B)
    (L : ℕ) : CE.κ L + ∑ j, CE.w L j * CE.u L j ≤ (PD.U L).Psi := by
  classical
  refine le_trans ?_ (CI.sum_le_upper (hB.trans (le_of_eq PD.hBp.symm)) (PD.U L))
  set sel := univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω)
  set cls := CI.toClassBounds.cls L
  have hW : ∑ j, CE.w L j * CE.u L j = ∑ i, ∑ j, CE.wc L i j * CE.u L j := by
    unfold ClassEnergyInputs.w
    rw [sum_comm]
    exact sum_congr rfl fun j _ => by rw [sum_mul]
  have hκ := sum_split_classes sel cls
    (fun ω => if cls ω = none then D.B * monomial (D.CL.π L) ω else CE.ρ L ω)
  have hΨs := sum_split_classes sel cls
    (fun ω => if cls ω = none then D.B * monomial (D.CL.π L) ω else CI.toClassBounds.phi L ω)
  have h0 : ∀ g g' : Choice (D.CL.T L) → ℝ,
      ∑ ω ∈ sel.filter (fun ω => cls ω = none), (if cls ω = none then g ω else g' ω) =
        ∑ ω ∈ sel.filter (fun ω => cls ω = none), g ω :=
    fun g g' => sum_congr rfl fun ω hω => by rw [ite_eq_left (mem_filter.mp hω).2]
  have hi : ∀ (g g' : Choice (D.CL.T L) → ℝ) i,
      ∑ ω ∈ sel.filter (fun ω => cls ω = some i), (if cls ω = none then g ω else g' ω) =
        ∑ ω ∈ sel.filter (fun ω => cls ω = some i), g' ω :=
    fun g g' i => sum_congr rfl fun ω hω => by
      rw [ite_eq_right (by rw [(mem_filter.mp hω).2]; exact Option.some_ne_none i)]
  unfold ClassEnergyInputs.κ
  rw [hκ, hΨs, h0, h0, Finset.sum_congr rfl fun i _ => hi _ _ i,
    Finset.sum_congr rfl fun i _ => hi _ _ i, hW]
  have hc : ∑ i, ∑ ω ∈ sel.filter (fun ω => cls ω = some i), CE.ρ L ω +
      ∑ i, ∑ j, CE.wc L i j * CE.u L j ≤
      ∑ i, ∑ ω ∈ sel.filter (fun ω => cls ω = some i), CI.toClassBounds.phi L ω := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun i _ => by linarith [CE.consistent L i]
  linarith

/-- **The joint allocation in the paper's form** (field 46 as proved in `prop:joint-middle-mean`,
`prop:joint-upper-mean`, `cor:joint-closing`): the combined residual gate at every scale,
`64(Δ_α + Δ_M + Δ_O + Δ_K + Δ_u − R_u) ≤ ∑_j b_j u_j + 63 (𝓔 − κ_L − ∑_j w_j u_j)`, i.e.
`63 κ_L + ∑_j (63 w_j − b_j) u_j ≤ 63 𝓔 − 64 Δ`. -/
def AllocJ {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {CI : ClassInputs D.CL}
    (CE : ClassEnergyInputs D CI) (b : ∀ L, CE.Θ L → ℝ) : Prop :=
  ∀ L, ledgerDelta targetLedger ≤
    ∑ j, b L j * CE.u L j + 63 * (targetLedger.E - (CE.κ L + ∑ j, CE.w L j * CE.u L j))

/-- **The allocation with the completion slack of the polynomial**: `Δ ≤ ∑_j b_j u_j +
63 (𝓔 − Ψ_L)`, with `Ψ_L` the complete polynomial of `PD` at the upper prices. Between B10's
`alloc` and `AllocJ`. -/
def AllocJΨ {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {CI : ClassInputs D.CL}
    (CE : ClassEnergyInputs D CI) (PD : PolynomialData CI) (b : ∀ L, CE.Θ L → ℝ) : Prop :=
  ∀ L, ledgerDelta targetLedger ≤ ∑ j, b L j * CE.u L j + 63 * (targetLedger.E - (PD.U L).Psi)

omit [DecidableEq P] in
/-- B10's `MeanData.alloc` (B4's (G2)) implies `AllocJΨ`, as `Ψ_L ≤ 𝓔`. -/
theorem allocJΨ_of_alloc {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {CI : ClassInputs D.CL} (CE : ClassEnergyInputs D CI) (PD : PolynomialData CI)
    (b : ∀ L, CE.Θ L → ℝ) (halloc : ∀ L, ledgerDelta targetLedger ≤ ∑ j, b L j * CE.u L j) :
    AllocJΨ CE PD b := fun L => by
  have := PD.Psi_le_E L
  linarith [halloc L]

omit [DecidableEq P] in
/-- `AllocJΨ` implies `AllocJ`, as `κ_L + ∑ w u ≤ Ψ_L` (`G1_Psi`). -/
theorem allocJ_of_allocJΨ {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {CI : ClassInputs D.CL} (CE : ClassEnergyInputs D CI) (PD : PolynomialData CI)
    (hB : D.B ≤ targetLedger.B) (b : ∀ L, CE.Θ L → ℝ) (halloc : AllocJΨ CE PD b) :
    AllocJ CE b := fun L => by
  have := G1_Psi CE PD hB L
  linarith [halloc L]

omit [DecidableEq P] in
/-- B10's `MeanData.alloc` (B4's (G2)) implies `AllocJ`: the combined gate is weaker. -/
theorem allocJ_of_alloc {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {CI : ClassInputs D.CL} (CE : ClassEnergyInputs D CI) (PD : PolynomialData CI)
    (hB : D.B ≤ targetLedger.B) (b : ∀ L, CE.Θ L → ℝ)
    (halloc : ∀ L, ledgerDelta targetLedger ≤ ∑ j, b L j * CE.u L j) : AllocJ CE b :=
  allocJ_of_allocJΨ CE PD hB b (allocJΨ_of_alloc CE PD b halloc)

omit [DecidableEq P] in
/-- **`JB` from the class bounds and the combined gate** (`cor:joint-closing` at `k = 6`,
`eq:final-joint-closing`): B4's `jointBound_target_of_classEnergy` with (G1) and (G2) replaced by
`AllocJ`. Neither the polynomial data nor `B ≤ B^{ledger}` is used: their role is inside the proof
of `AllocJ` (in the paper, the completion of the residual series). -/
theorem jointBound_target_allocJ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hcard : Fintype.card E = 6) {CI : ClassInputs D.CL}
    (CE : ClassEnergyInputs D CI) (hE1 : D.EnvelopeBoundNonneg)
    (b v : ∀ L, CE.Θ L → ℝ)
    (hmean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, b L j * CE.Z L A j - remainder c₂ L A ≤
          (energyMean (blockLift m₀ blk p) D.ME.ML L A +
            energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2)
    (hupper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
      (∀ L, ∑ j, (63 * CE.w L j - b L j) * v L j ≤ V) ∧ ∃ r : ∀ L, Finset ℤ → CE.Θ L → ℝ,
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∀ j, CE.Z L A j ≤ (CE.u L j + ε₃ L * v L j) * D.Y L A + r L A j) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ j, (63 * CE.w L j - b L j) * r L A j ≤ remainder c₃ L A))
    (hresid : ∀ L j, b L j ≤ 63 * CE.w L j) (halloc : AllocJ CE b) :
    JointBound D targetLedger.jointConstant := by
  have h63 : (2 : ℝ) ^ Fintype.card E - 1 = 63 := by rw [hcard]; norm_num
  have h64 : (2 : ℝ) ^ Fintype.card E = 64 := by rw [hcard]; norm_num
  refine jointBound_of_classes_gate D CE.Θ CE.Z CE.w b CE.u v CE.κ targetLedger.m₁
    (CE.terms hE1) hmean (by rw [h63]; exact hupper) (by rw [h63]; exact hresid) ?_
  intro L
  rw [h63, h64]
  have hg := jointConstant_gate targetLedger
  have h2 := halloc L
  have e : ∑ i, (63 * CE.w L i - b L i) * CE.u L i =
      63 * ∑ i, CE.w L i * CE.u L i - ∑ i, b L i * CE.u L i := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e]
  unfold ledgerDelta at h2
  norm_num at hg
  linarith

end Sarkozy.ClassData
