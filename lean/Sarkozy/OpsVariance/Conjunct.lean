module

public import Sarkozy.OpsVariance.Steps

@[expose] public section

/-!
# The variance conjunct of `ClassStepsOps.H`

`paper/sections/22_variance.tex`, `prop:background-variance`(a), `lem:var-gain`(b),
`cor:var-classes`; `paper/sections/09_comparison_theorem.tex`, `def:robust`.

`ClassStepsOps.H` (`MainFinal2/Bundles.lean`) asks, at every least counterexample,

`∀ v : cd.V L, Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt L A) (monomial π) (ρ L) (rr L A)
  (∑ j, wc L (.inr v) j * Z L A j) (D.Y L A) (z L) K)`,

with one `z → 0`, one `K`, and remainders `rr` shared with the degree classes. This file gives that
conjunct, with exactly this statement:

* **`varConjunct`**: for any class data `cd` and any choice `cr L v : Bool` of the classes that take
  the variance credit. The no-credit classes need only (E1) for the envelopes of the selections
  (`hE`, the components of `ComparisonData.EnvelopeBoundNonneg`), `B π ≤ ρ` and the remainder
  budget; the credit classes need in addition the zero marginals of their record changes (`hzm`),
  the comparison `hJN` and the restoration bound `hres` (`varStepsAt_credit`);
* **`varConjunct_noCredit`**: the case `cr = false`;
* `hrr_sum_le`: the remainders `π̃_ω r_E(ω)` of the variance selections add up to at most the
  envelope remainder budget `∑_ω π̃_ω r_E(ω) ≤ c_E L^{-σ} α` of (E1).

`z ≥ ε_E` (`hzE`) and `K ≥ 3` (`hK`) are the only conditions on the shared numbers.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame
open Sarkozy.Param (Params)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

omit [DecidableEq P] in
theorem isSelection_of_mem_clsSel {cd : ClassData D.CL} {L : ℕ} {i : cd.ι L}
    {ω : Choice (D.CL.T L)} (hω : ω ∈ cd.clsSel L i) : IsSelection ω :=
  (mem_filter.mp (mem_filter.mp hω).1).2

omit [DecidableEq P] in
/-- (E1) at the shared error `z ≥ ε_E`. -/
theorem env_le_of_le {L : ℕ} {A : Finset ℤ} {ω : Choice (D.CL.T L)} {εE z r : ℝ}
    (hY : 0 ≤ D.Y L A) (hzE : εE ≤ z)
    (h : envEnergy D L A ω ≤ (D.B + εE) * selProd D L ω * D.Y L A + r) :
    envEnergy D L A ω ≤ (D.B + z) * selProd D L ω * D.Y L A + r := by
  have h1 : (D.B + εE) * selProd D L ω * D.Y L A ≤ (D.B + z) * selProd D L ω * D.Y L A :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (selProd_nonneg L ω)) hY
  linarith

omit [DecidableEq P] in
/-- **The variance conjunct of `ClassStepsOps.H`** for any class data `cd`, with the classes
`cr L v = true` taking the variance credit `[b̃_v − R_*]_+` (`prop:background-variance`(a),
`lem:var-gain`(b)) and the others the cost `B` (`g = 0`). Inputs:
* `hE`: (E1) for the envelopes of the selections, at `ε_E ≤ z` (the components of
  `ComparisonData.EnvelopeBoundNonneg`; proved at the paper's data, `envelopeBoundNonneg_front`).
  Kind R, proved;
* on the credit classes (`Steps.lean`, `varStepsAt_credit`):
  - `hz0`: the record changes annihilate the constants (`eq:record:zero-marginal`). Kind R;
  - `hJN`: `Y[J_X ⊗ Ñ] ≥ Y[J_X ⊗ Ñ₀] − (R_err + z) C_X Y − r_J`
    (`lem:record:variance-interface`(ii),
    the last bound of (E1) at `J_X`). Kind R;
  - `hres`: `∑_R π̃ Y[J_X ⊗ Ñ₀] ≥ (b̃ − z)(∑_R π) Y − r₀` (`lem:record:restoration`,
    `lem:var-gain`(a), `prop:background-variance`(a)). Kind C;
* `hρ`: the residuals carry the class cost (evaluation, shared with `hρ`/`hcomp` of the
  obligations);
* `hrr`: the remainders `rr` dominate the class remainders (shared with the degree classes);
* `hWZ`: the diagonal part of a variance class is nonnegative (`hWZ_agg` at the obligations). -/
theorem varConjunct (cd : ClassData D.CL) {Θ : ℕ → Type} [∀ L, Fintype (Θ L)]
    (Z : ∀ L, Finset ℤ → Θ L → ℝ) (wc : ∀ L, cd.ι L → Θ L → ℝ)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ) (z : ℕ → ℝ) (K : ℝ)
    (rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    {εE : ℕ → ℝ} {rE : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ}
    (hE : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ ω : Choice (D.CL.T L), IsSelection ω →
        envEnergy D L A ω ≤ (D.B + εE L) * selProd D L ω * D.Y L A + rE L A ω))
    (hzE : ∀ L, εE L ≤ z L) (hz0 : ∀ L, 0 ≤ z L) (hK : 3 ≤ K)
    (cr : ∀ L, cd.V L → Bool) (bt : ∀ L, cd.V L → ℝ) (Rstar : ℝ) (hRs : D.GB.Rerr ≤ Rstar)
    (rJ : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) (r₀ : ∀ L, Finset ℤ → cd.V L → ℝ)
    (hr₀ : ∀ L A v, 0 ≤ r₀ L A v) (hrJ : ∀ L A ω, 0 ≤ rJ L A ω)
    (hzm : ∀ L (v : cd.V L), cr L v = true → ∀ ω ∈ cd.clsSel L (.inr v),
      RecordsZeroMarginal D L ω)
    (hJN : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ v : cd.V L,
      cr L v = true → ∀ ω ∈ cd.clsSel L (.inr v),
        varJ0 D L A ω (envM D L ω) - (D.GB.Rerr + z L) * selProd D L ω * D.Y L A - rJ L A ω ≤
          varJ D L A ω (envM D L ω)))
    (hres : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ v : cd.V L,
      cr L v = true →
        (bt L v - z L) * (∑ ω ∈ cd.clsSel L (.inr v), monomial (D.CL.π L) ω) * D.Y L A -
            r₀ L A v ≤
          ∑ ω ∈ cd.clsSel L (.inr v), monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω)))
    (hρ : ∀ L (v : cd.V L), ∀ ω ∈ cd.clsSel L (.inr v),
      (D.B - (if cr L v then max 0 (bt L v - Rstar) else 0)) * monomial (D.CL.π L) ω ≤ ρ L ω)
    (hrr : ∀ L A (v : cd.V L),
      ∑ ω ∈ cd.clsSel L (.inr v),
          monomial (D.CL.πt L) ω * (rE L A ω + (if cr L v then rJ L A ω else 0)) +
        (if cr L v then r₀ L A v else 0) ≤ ∑ ω ∈ cd.clsSel L (.inr v), rr L A ω)
    (hWZ : ∀ L A (v : cd.V L), 0 ≤ ∑ j, wc L (.inr v) j * Z L A j) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A => ∀ v : cd.V L,
      Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := D) L A)
        (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A) (∑ j, wc L (.inr v) j * Z L A j)
        (D.Y L A) (z L) K) := by
  filter_upwards [hE, hJN, hres] with L hEL hJNL hresL
  intro C hC hind A hA hcount v
  have hY : 0 ≤ D.Y L A := (TheoremCParam.counterexample_pos hC hcount).le
  have hEv : ∀ ω ∈ cd.clsSel L (.inr v),
      envEnergy D L A ω ≤ (D.B + z L) * selProd D L ω * D.Y L A + rE L A ω := fun ω hω =>
    env_le_of_le hY (hzE L) (hEL C hC hind A hA hcount ω (isSelection_of_mem_clsSel hω))
  have hρv := hρ L v
  have hrrv := hrr L A v
  cases hv : cr L v
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, sub_zero, add_zero] at hρv hrrv
    exact varStepsAt_noCredit _ (ρ L) (rr L A) (rE L A) (hz0 L) hY hEv (hWZ L A v) hρv hK hrrv
  · simp only [hv, ↓reduceIte] at hρv hrrv
    exact varStepsAt_credit _ (fun ω hω => isSelection_of_mem_clsSel hω) (ρ L) (rr L A) (rE L A)
      (rJ L A) (r₀ L A v) Rstar (bt L v) (hr₀ L A v) (fun ω _ => hrJ L A ω) hRs (hzm L v hv) hEv
      (hJNL C hC hind A hA hcount v hv) (hresL C hC hind A hA hcount v hv) (hWZ L A v) hρv hK
      hrrv

omit [DecidableEq P] in
/-- **The variance conjunct with no credit** (`varConjunct` at `cr = false`): from (E1) for the
envelopes of the selections alone, with `B π_ω ≤ ρ_ω` and `∑_R π̃ r_E ≤ ∑_R rr` on every variance
class. -/
theorem varConjunct_noCredit (cd : ClassData D.CL) {Θ : ℕ → Type} [∀ L, Fintype (Θ L)]
    (Z : ∀ L, Finset ℤ → Θ L → ℝ) (wc : ∀ L, cd.ι L → Θ L → ℝ)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ) (z : ℕ → ℝ) (K : ℝ)
    (rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    {εE : ℕ → ℝ} {rE : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ}
    (hE : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ ω : Choice (D.CL.T L), IsSelection ω →
        envEnergy D L A ω ≤ (D.B + εE L) * selProd D L ω * D.Y L A + rE L A ω))
    (hzE : ∀ L, εE L ≤ z L) (hz0 : ∀ L, 0 ≤ z L) (hK : 3 ≤ K)
    (hρ : ∀ L (v : cd.V L), ∀ ω ∈ cd.clsSel L (.inr v), D.B * monomial (D.CL.π L) ω ≤ ρ L ω)
    (hrr : ∀ L A (v : cd.V L), ∑ ω ∈ cd.clsSel L (.inr v), monomial (D.CL.πt L) ω * rE L A ω ≤
      ∑ ω ∈ cd.clsSel L (.inr v), rr L A ω)
    (hWZ : ∀ L A (v : cd.V L), 0 ≤ ∑ j, wc L (.inr v) j * Z L A j) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A => ∀ v : cd.V L,
      Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := D) L A)
        (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A) (∑ j, wc L (.inr v) j * Z L A j)
        (D.Y L A) (z L) K) := by
  filter_upwards [hE] with L hEL
  intro C hC hind A hA hcount v
  have hY : 0 ≤ D.Y L A := (TheoremCParam.counterexample_pos hC hcount).le
  exact varStepsAt_noCredit _ (ρ L) (rr L A) (rE L A) (hz0 L) hY
    (fun ω hω => env_le_of_le hY (hzE L)
      (hEL C hC hind A hA hcount ω (isSelection_of_mem_clsSel hω)))
    (hWZ L A v) (hρ L v) hK (hrr L A v)

omit [DecidableEq P] in
/-- **The remainder budget of the variance classes** (for the field `hrr` of `VarStepsAt` and the
third conjunct of `ClassStepsOps.H`): the remainders `π̃_ω r_E(ω)` of the selections
of the variance classes add up to at most those of all selections, which (E1) bounds by
`c_E L^{-σ} α` (`EnvelopeBoundNonneg`, second conjunct). -/
theorem hrr_sum_le (cd : ClassData D.CL) (L : ℕ) (rE : Choice (D.CL.T L) → ℝ)
    (hrE : ∀ ω, 0 ≤ rE ω) :
    ∑ v : cd.V L, ∑ ω ∈ cd.clsSel L (.inr v), monomial (D.CL.πt L) ω * rE ω ≤
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * rE ω := by
  classical
  have hnn : ∀ ω, 0 ≤ monomial (D.CL.πt L) ω * rE ω := fun ω =>
    mul_nonneg (monomial_πt_nonneg L ω) (hrE ω)
  -- the variance classes are disjoint subsets of the selections
  have hdisj : ((univ : Finset (cd.V L)) : Set (cd.V L)).PairwiseDisjoint
      (fun v => cd.clsSel L (.inr v)) := by
    intro v _ w _ hvw
    rw [Function.onFun, disjoint_left]
    intro ω hv hw
    have h1 := (mem_filter.mp hv).2
    have h2 := (mem_filter.mp hw).2
    rw [h1] at h2
    exact hvw (Sum.inr_injective (Option.some_injective _ h2))
  rw [← sum_biUnion hdisj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    obtain ⟨v, _, hv⟩ := mem_biUnion.mp hω
    exact (mem_filter.mp hv).1
  · intro ω _ _
    exact hnn ω

end Sarkozy.OpsVariance
