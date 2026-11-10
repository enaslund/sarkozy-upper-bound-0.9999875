module

public import Sarkozy.ClassBoundsPaper.Joint
public import Sarkozy.ClassBoundsPaper.ClassSplit
public import Sarkozy.TheoremCBlock.Classes

@[expose] public section

/-!
# The joint bound from the class bounds at energy level

`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`; `paper/sections/23_envelopes.tex`,
`thm:envelopes`(i), `cor:envelope-costs`; `paper/sections/10_comparison_lemmas.tex`,
`lem:record:record-expansion`(ii); `paper/sections/28_closing.tex`, `prop:closing-data`(d).

For the joint closing the class bounds are needed **at energy level**: the terms of a class `𝒞_i`
are bounded by energies `Z_j` of labelled positive diagonals (the diagonals of the envelope of the
class, shared with the mean expansion) with weights `w_{ij}`, plus an evaluated residual `ρ_ω`;
their evaluated form `φ_ω` (the class bound of `ClassInputs`) dominates `∑_j w_{ij} u_j + ∑ ρ_ω` at
the upper prices `u_j` of the diagonals.

* `ClassEnergyInputs D CI`: these data for the classes of `CI : ClassInputs D.CL` (*hypotheses*:
  `energy` is `thm:envelopes`(i) and `cor:envelope-costs` at energy level, robustly;
  `consistent` is the evaluation of the envelope energies at the upper prices).
* **`ClassEnergyInputs.terms`**: with (E1) (`EnvelopeBoundNonneg`) for the selections in no class,
  the term-level comparison bound `hterms` of `jointBound_target`, with weights
  `w_j = ∑_i w_{ij}` and constant `κ_L = ∑_{ω in no class} B π_ω + ∑_{ω in a class} ρ_ω`.
* **`ClassEnergyInputs.G1`**: (G1) of `jointBound_target`, from the upper data `PD` of the class
  polynomial and `hB` (`PolynomialData.hΨ`, with `consistent`).
* **`jointBound_target_of_classEnergy`**: `JointBound D targetLedger.jointConstant` from `CI`, `PD`,
  `CE`, (E1), `hB`, the mean expansion (J2) with `m₁`, the upper prices (J3), the residual gates
  `b_j ≤ 63 w_j` and the joint mean allocations `∑_j b_j u_j ≥ 64(Δ_mid + Δ_u − R_u)` (G2).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassBoundsPaper

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

/-- **The class bounds at energy level** (`thm:envelopes`(i), `cor:envelope-costs`, for the joint
closing `cor:joint-closing`), for the classes of `CI`. *Hypotheses*. -/
structure ClassEnergyInputs (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (CI : ClassInputs D.CL) where
  /-- The labelled positive diagonals of the envelopes. -/
  Θ : ℕ → Type
  [ΘFintype : ∀ L, Fintype (Θ L)]
  /-- Their energies at a counterexample, and their upper prices. -/
  Z : ∀ L, Finset ℤ → Θ L → ℝ
  u : ∀ L, Θ L → ℝ
  /-- The weight of the class `i` on the diagonal `j`. -/
  wc : ∀ L, CI.toClassBounds.ι L → Θ L → ℝ
  /-- The evaluated residual of a selection (the parts of its class bound not on a diagonal). -/
  ρ : ∀ L, Choice (D.CL.T L) → ℝ
  /-- **The class bounds at energy level**, robustly and uniformly in the classes. -/
  energy : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (∀ i, ∑ ω ∈ (univ.filter fun ω : Choice (D.CL.T L) => IsSelection ω).filter
          (fun ω => CI.toClassBounds.cls L ω = some i),
            |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
        ∑ j, wc L i j * Z L A j +
          ∑ ω ∈ (univ.filter fun ω : Choice (D.CL.T L) => IsSelection ω).filter
              (fun ω => CI.toClassBounds.cls L ω = some i),
            ((ρ L ω + ε L * monomial (D.CL.π L) ω) * D.Y L A + r L A ω)) ∧
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), r L A ω ≤ remainder c L A
  /-- **The evaluation at the upper prices** is at most the class bound of `CI`. -/
  consistent : ∀ L i, ∑ j, wc L i j * u L j +
      ∑ ω ∈ (univ.filter fun ω : Choice (D.CL.T L) => IsSelection ω).filter
        (fun ω => CI.toClassBounds.cls L ω = some i), ρ L ω ≤
    ∑ ω ∈ (univ.filter fun ω : Choice (D.CL.T L) => IsSelection ω).filter
        (fun ω => CI.toClassBounds.cls L ω = some i), CI.toClassBounds.phi L ω

attribute [instance] ClassEnergyInputs.ΘFintype

namespace ClassEnergyInputs

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {CI : ClassInputs D.CL}
  (CE : ClassEnergyInputs D CI)

/-- The diagonal weights `w_j = ∑_i w_{ij}` of the comparison. -/
noncomputable def w (L : ℕ) (j : CE.Θ L) : ℝ := ∑ i, CE.wc L i j

/-- The comparison constant off the diagonals:
`κ_L = ∑_{ω in no class} B π_ω + ∑_{ω in a class} ρ_ω`. -/
noncomputable def κ (L : ℕ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
    (if CI.toClassBounds.cls L ω = none then D.B * monomial (D.CL.π L) ω else CE.ρ L ω)

omit [DecidableEq P] in
/-- **The term-level comparison bound** (`lem:record:record-expansion`(ii) at energy level): from
the class bounds at energy level and (E1) off the classes,
`∑_ω |I_ω| ≤ ∑_j w_j Z_j + (κ_L + o(1)) Y + rem`. -/
theorem terms (hE1 : D.EnvelopeBoundNonneg) :
    ∃ ε₁ : ℕ → ℝ, Tendsto ε₁ atTop (𝓝 0) ∧ ∃ c₁ : ℝ, 0 ≤ c₁ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
            |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
          ∑ j, CE.w L j * CE.Z L A j + (CE.κ L + ε₁ L) * D.Y L A + remainder c₁ L A := by
  obtain ⟨εE, hεE0, hεE, cE, hcE, rE, hrE0, hE1a, hE1b⟩ := hE1
  obtain ⟨ε, hε, c, hc, r, hr0, hcb⟩ := CE.energy
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
  have hfree : ∀ ω ∈ sel, CI.toClassBounds.cls L ω = none →
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
  have hsplit := sum_abs_le_split sel (CI.toClassBounds.cls L)
    (fun ω => |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω|)
    (fun ω => monomial (D.CL.π L) ω) (CE.ρ L) (fun ω => monomial (D.CL.πt L) ω * rE L A ω)
    (r L A) (CE.wc L) (CE.Z L A) (B := D.B) (εE := εE L) (ε := ε L) (Y := D.Y L A)
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
  have hw : ∑ j, (∑ i, CE.wc L i j) * CE.Z L A j = ∑ j, CE.w L j * CE.Z L A j := rfl
  unfold κ
  linarith

omit [DecidableEq P] in
/-- **(G1) from the class polynomial** (`prop:closing-data`(d)): for `B ≤ targetLedger.B` (`hB`),
`κ_L + ∑_j w_j u_j ≤ 𝓔`, since by `consistent` it is at most the class sum of `hΨ`, which
`PolynomialData.hΨ` bounds by `targetLedger.E`. -/
theorem G1 (PD : PolynomialData CI) (hB : D.B ≤ targetLedger.B) (L : ℕ) :
    CE.κ L + ∑ j, CE.w L j * CE.u L j ≤ targetLedger.E := by
  classical
  refine le_trans ?_ (PD.hΨ hB L)
  set sel := univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω)
  set cls := CI.toClassBounds.cls L
  have hW : ∑ j, CE.w L j * CE.u L j = ∑ i, ∑ j, CE.wc L i j * CE.u L j := by
    unfold w
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
  unfold κ
  rw [hκ, hΨs, h0, h0, Finset.sum_congr rfl fun i _ => hi _ _ i,
    Finset.sum_congr rfl fun i _ => hi _ _ i, hW]
  have hc : ∑ i, ∑ ω ∈ sel.filter (fun ω => cls ω = some i), CE.ρ L ω +
      ∑ i, ∑ j, CE.wc L i j * CE.u L j ≤
      ∑ i, ∑ ω ∈ sel.filter (fun ω => cls ω = some i), CI.toClassBounds.phi L ω := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun i _ => by linarith [CE.consistent L i]
  linarith

end ClassEnergyInputs

omit [DecidableEq P] in
/-- **`JB` for the paper's data from the class bounds** (`cor:joint-closing` at `k = 6`,
`H = targetLedger.jointConstant`): from the class inputs `CI` and upper data `PD` (whose `hΨ` gives
(G1)), the class bounds at energy level `CE`, (E1), `hB`, the mean expansion (J2) with the
one-block credit `targetLedger.m₁` and the retained energies `b_j Z_j` (`prop:record:mean-credit`),
the upper prices (J3) (`lem:bracket-energy`, (E1)), the residual gates `b_j ≤ 63 w_j` (the 192
residuals of `cert:four-routes-closing`) and the joint mean allocations
`∑_j b_j u_j ≥ 64(Δ_α + Δ_M + Δ_O + Δ_K + Δ_u − R_u)` (`prop:joint-middle-mean`,
`prop:joint-upper-mean`). -/
theorem jointBound_target_of_classEnergy (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hcard : Fintype.card E = 6) {CI : ClassInputs D.CL} (PD : PolynomialData CI)
    (CE : ClassEnergyInputs D CI) (hE1 : D.EnvelopeBoundNonneg) (hB : D.B ≤ targetLedger.B)
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
    (hresid : ∀ L j, b L j ≤ 63 * CE.w L j)
    (hG2 : ∀ L, ledgerDelta targetLedger ≤ ∑ j, b L j * CE.u L j) :
    JointBound D targetLedger.jointConstant :=
  jointBound_target D hcard CE.Θ CE.Z CE.w b CE.u v CE.κ (CE.terms hE1) hmean hupper hresid
    (CE.G1 PD hB) hG2

end Sarkozy.ClassBoundsPaper

namespace Sarkozy.ClassBoundsPaper

open Filter Finset
open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

attribute [local instance] TheoremCBlock.ClassBounds.ιFintype TheoremCBlock.ClassBounds.ιDecEq
  TheoremCBlock.ClassBounds.JauxFintype TheoremCBlock.ClassBounds.JauxDecEq

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **Non-vacuity of `ClassEnergyInputs`**: the class bounds at energy level with no shared
diagonal are exactly the evaluated class bounds of `CI` (`ρ_ω = φ_ω`); so `ClassEnergyInputs D CI`
is inhabited whenever `CI` is. In the joint closing the paper uses shared diagonals, without which
the allocation `MeanAllocation.alloc` cannot hold (its right side would be `0`). -/
noncomputable def ClassEnergyInputs.ofClassInputs
    (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (CI : ClassInputs D.CL) :
    ClassEnergyInputs D CI where
  Θ _ := Empty
  ΘFintype _ := inferInstanceAs (Fintype Empty)
  Z _ _ j := j.elim
  u _ j := j.elim
  wc _ _ j := j.elim
  ρ L ω := CI.toClassBounds.phi L ω
  energy := by
    obtain ⟨ε, hε, c, hc, r, hr, H⟩ := CI.robustNonneg
    refine ⟨ε, hε, c, hc, r, hr, ?_⟩
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] using H
  consistent L i := by simp

end Sarkozy.ClassBoundsPaper
