module

public import Sarkozy.PaperFrame.Reference
public import Sarkozy.RecordExpansion.SharpFirst

@[expose] public section

/-!
# The first comparison `Y_λ ≥ (1 - L₀ - o(1)) Y` (`lem:record:first-stage`)

`lem:record:first-stage` (`paper/sections/10_comparison_lemmas.tex`), in the robust form of
the field `firstStage` of `Sarkozy.Comparison.ClosingEstimates`: at every least normalized
counterexample `(L, A)` of every sufficiently large scale, uniformly in the induction constant,

  `(1 - L₀ - ε(L) L₀) Y - c L^{-σ} α ≤ Y_λ`,   `L₀ = e^P 𝔗(d, v)` (`firstStageCost`).

The atoms, alphabets and lift are those of an arbitrary atom frame
(`Sarkozy/Comparison/ConcreteFrame.lean`); the energies are `energyFirst` (`Y = Y_μ`, `Y_λ`).

* **Step 1** (`Y_ρ ≥ Y`): `μ_𝔟 ⪰_{ϑ₀} 0` at every atom ((R2) of (CP1) at the cut `ϑ₀` of
  (CP2)(a)) and `ρ_𝔟 ⪰_{ϑ₀} μ_𝔟` ((CP2)(a); `ρ_𝔟 = μ_𝔟` off the first-stage atoms). This is
  WP-R's `first_stage_step_one`, inside `Sarkozy.RecordExpansion.first_stage_lower_bound`.
* **Step 2** (`|Y_λ - Y_ρ| ≤ (L₀ + o(1)) Y`): `λ_𝔟 = ρ_𝔟 + ∑_i δ_{𝔟,i}` with the tagged record
  differences of (CP2)(b), summed by `lem:sharp-first` into `K e^{P_L} 𝔗(d_L, v_L)` (WP-R's
  `abs_energy_sub_le_sharpFirst`), with `K = (1 + ε(L)) Y`. The totals over the atoms of the
  scale are at most the totals `P`, `d_j`, `v_j` over all atoms, and `𝔗` is nondecreasing in
  every argument (`rem:cp:tags`, `tagSeries_mono`), so the cost is at most `L₀`.

Hypotheses that remain:

* `hterm`, the per-term bounds of `lem:sharp-first`: for every nonempty choice `σ` of
  differences and every tag `j` present in it,
  `|Y_σ| ≤ (1 + ε(L)) Y · wt_j(σ) + r_σ`. In the paper they come from the folded-energy bound
  `lem:record:folded-energy` (here `Sarkozy.Comparison.abs_term_le_folded`), followed by
  `prop:record:density-structured` for the two folded energies, with
  `Sarkozy.Structured.sqrt_mul_sqrt_le_of_folded` for the geometric mean. That chain is not
  yet connected in Lean.
* `hr`, the aggregate of the remainders `r_σ`: the large-union terms (`q_E > N^τ`) of
  `lem:record:density-lp` and the remainders of the structured-energy estimate, bounded by a
  density-linear remainder `c L^{-σ} α`.
-/

open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.TheoremC

open Sarkozy.Comparison Sarkozy.RecordExpansion

/-- The cost `L₀ = e^P 𝔗(d, v)` of the first stage (CP2), with `P` the total variation price
of `ρ - μ` and `d_j`, `v_j` the tag totals of the sharp and variation prices. -/
noncomputable def firstStageCost {Tag : Type*} [Fintype Tag] [DecidableEq Tag]
    (P : ℝ) (dT vT : Tag → ℝ) : ℝ :=
  Real.exp P * tagSeries dT vT

theorem firstStageCost_nonneg {Tag : Type*} [Fintype Tag] [DecidableEq Tag] (P : ℝ)
    {dT vT : Tag → ℝ} (hd : ∀ j, 0 ≤ dT j) (hv : ∀ j, 0 ≤ vT j) :
    0 ≤ firstStageCost P dT vT :=
  mul_nonneg (Real.exp_pos P).le (tagSeries_nonneg hd hv)

/-- The relative error `ε(L) L₀` of the first comparison tends to zero with `ε`. -/
theorem firstStage_error_tendsto {Tag : Type*} [Fintype Tag] [DecidableEq Tag] (P : ℝ)
    (dT vT : Tag → ℝ) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun L => ε L * firstStageCost P dT vT) atTop (𝓝 0) := by
  simpa only [zero_mul] using hε.mul_const (firstStageCost P dT vT)

/-- The tag totals of nonnegative prices are nonnegative. -/
theorem tagTotal_nonneg {J : Type*} [Fintype J] {I : J → Type*} [∀ b, Fintype (I b)]
    {Tag : Type*} [DecidableEq Tag] (tag : ∀ b, I b → Tag) {d : ∀ b, I b → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (j : Tag) : 0 ≤ tagTotal tag d j := by
  unfold tagTotal
  refine sum_nonneg fun b _ => sum_nonneg fun i _ => ?_
  split_ifs
  · exact hd b i
  · exact le_rfl

/-- At a counterexample the reference energy is nonnegative: it exceeds
`C L^{-a} α^θ ≥ 0`. -/
theorem energy_nonneg_of_counter {Y : ℕ → Finset ℤ → ℝ} {C : ℝ} (hC : 1 ≤ C) {L : ℕ}
    {A : Finset ℤ}
    (h : C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A) :
    0 ≤ Y L A := by
  have h1 : 0 ≤ C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg L) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)
  linarith

variable {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
  {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]

/-- The frame energy is the diagonal multilinear average of the tensor product. -/
theorem energyFirst_eq_diagonalIntegral (κ : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ) (L : ℕ) (A : Finset ℤ) :
    energyFirst κ F L A = diagonalIntegral (tensorLaw (κ L)) (F L A) :=
  Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _

/-- **`lem:record:first-stage`, robust form** (the field `firstStage` of
`ClosingEstimates`, with `εfirst L = ε(L) L₀`). Step 1 is (R2) of (CP1) at `ϑ₀` and
(CP2)(a); Step 2 is the summation of `lem:sharp-first` over the tagged differences of
(CP2)(b), with the per-term bounds `hterm` (`K = (1 + ε(L)) Y`) and the aggregate remainder
`hr` as hypotheses. The totals at every scale are at most the totals `P`, `dT`, `vT`. -/
theorem firstStage_estimate (ϑ₀ : ReflectionCut Slot)
    (μ ρ lam : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ) (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)
    (hμ : ∀ L b, ϑ₀.Positive (μ L b)) (hρ : ∀ L b, ϑ₀.Below (μ L b) (ρ L b))
    {I : ∀ L, Atom L → Type} [∀ L b, Fintype (I L b)] [∀ L b, DecidableEq (I L b)]
    (δ : ∀ L b, I L b → ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (hlam : ∀ L b, lam L b = ρ L b + ∑ i, δ L b i)
    {Tag : Type} [Fintype Tag] [DecidableEq Tag] (tag : ∀ L b, I L b → Tag)
    (d v : ∀ L b, I L b → ℝ) (hd : ∀ L b i, 0 ≤ d L b i) (hv : ∀ L b i, 0 ≤ v L b i)
    (pv : ∀ L, Atom L → ℝ) (hpv : ∀ L b, 0 ≤ pv L b)
    {P : ℝ} {dT vT : Tag → ℝ} (hP : ∀ L, ∑ b, pv L b ≤ P)
    (hdT : ∀ L j, tagTotal (tag L) (d L) j ≤ dT j)
    (hvT : ∀ L j, tagTotal (tag L) (v L) j ≤ vT j)
    (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L)
    (r : ∀ L, Finset ℤ → (∀ b, Option (I L b)) → ℝ) (c : ℝ)
    (hterm : AtCounterexamples (energyFirst μ F) fun L A =>
      ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (tag L) σ j →
        |diagonalIntegral (tensorLaw (fun b => (σ b).elim (ρ L b) (δ L b))) (F L A)| ≤
          (1 + ε L) * energyFirst μ F L A * tagWeight (tag L) (d L) (v L) (pv L) j σ +
            r L A σ)
    (hr : AtCounterexamples (energyFirst μ F) fun L A =>
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I L b)) => σ ≠ fun _ => none), r L A σ ≤
        remainder c L A) :
    AtCounterexamples (energyFirst μ F) fun L A =>
      (1 - firstStageCost P dT vT - ε L * firstStageCost P dT vT) * energyFirst μ F L A -
          remainder c L A ≤ energyFirst lam F L A := by
  filter_upwards [hterm, hr] with L hterm' hr'
  intro C hC hind A hA hcounter
  have hY : 0 ≤ energyFirst μ F L A := energy_nonneg_of_counter hC hcounter
  have hK : 0 ≤ (1 + ε L) * energyFirst μ F L A :=
    mul_nonneg (by linarith [hε0 L]) hY
  -- Steps 1 and 2 at the scale `L`
  have hmain := first_stage_lower_bound ϑ₀ (μ L) (ρ L) (hμ L) (hρ L) (δ L) (F L A) (tag L)
    (hd L) (hv L) (hpv L) hK (r L A) (hterm' C hC hind A hA hcounter)
  have hlamL : (fun b => ρ L b + ∑ i, δ L b i) = lam L := funext fun b => (hlam L b).symm
  rw [hlamL, ← energyFirst_eq_diagonalIntegral, ← energyFirst_eq_diagonalIntegral] at hmain
  -- the cost at the scale `L` is at most `L₀`
  have hdL : ∀ j, 0 ≤ tagTotal (tag L) (d L) j := tagTotal_nonneg (tag L) (hd L)
  have hvL : ∀ j, 0 ≤ tagTotal (tag L) (v L) j := tagTotal_nonneg (tag L) (hv L)
  have hcost : Real.exp (∑ b, pv L b) * tagSeries (tagTotal (tag L) (d L)) (tagTotal (tag L) (v L)) ≤
      firstStageCost P dT vT :=
    mul_le_mul (Real.exp_le_exp.mpr (hP L)) (tagSeries_mono hdL hvL (hdT L) (hvT L))
      (tagSeries_nonneg hdL hvL) (Real.exp_pos P).le
  have hKcost := mul_le_mul_of_nonneg_left hcost hK
  have hrem := hr' C hC hind A hA hcounter
  have hexpand : (1 - firstStageCost P dT vT - ε L * firstStageCost P dT vT) *
      energyFirst μ F L A = energyFirst μ F L A -
        (1 + ε L) * energyFirst μ F L A * firstStageCost P dT vT := by
    ring
  rw [hexpand]
  have hassoc : (1 + ε L) * energyFirst μ F L A * Real.exp (∑ b, pv L b) *
      tagSeries (tagTotal (tag L) (d L)) (tagTotal (tag L) (v L)) =
      (1 + ε L) * energyFirst μ F L A * (Real.exp (∑ b, pv L b) *
        tagSeries (tagTotal (tag L) (d L)) (tagTotal (tag L) (v L))) := by
    ring
  rw [hassoc] at hmain
  linarith

end Sarkozy.TheoremC
