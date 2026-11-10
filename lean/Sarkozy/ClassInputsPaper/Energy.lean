module

public import Sarkozy.ClassInputsPaper.FromEnergy
public import Sarkozy.ClassInputsPaper.Steps

@[expose] public section

/-!
# The class bounds at energy level from the steps, class by class

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i), `cor:envelope-costs`;
`paper/sections/22_variance.tex`, `cor:var-classes`, `lem:var-gain`, `cor:variance:final`(i);
`paper/sections/09_comparison_theorem.tex`, `def:robust`.

`ClassEnergyData.energy` asks, uniformly in the classes of the construction, for
`∑_{𝒞_i} |I_ω| ≤ ∑_j w_{ij} Z_j + ∑_{𝒞_i} ((ρ_ω + ε π_ω) Y + r_ω)`. Here it is reduced, class by
class, to the steps of the paper's proofs:

* a degree class `𝒞_n` (one of the 49 degree vectors of the sixteen envelope classes) by Steps 1–4
  of `thm:envelopes`(i) (`EnvStepsAt`, `Steps.lean`);
* a variance class by the class-cost step of `prop:background-variance`(a) / `lem:var-gain`(b)
  (`VarStepsAt`).

`ClassStepsAt` selects the form by the kind of the class; **`energy_of_steps`** proves the energy
field from `StepsFamily` (the steps at every counterexample, with one uniform `z → 0`, one `K`,
and remainders `rr ≥ 0` with `∑ rr ≤ c L^{-σ} α`). `ClassEnergyData.ofSteps` is the constructor.

For `consistent`:
* `phi_inl`, `phi_inr`: on a degree class `φ_ω = C_n π^arm + B'(π^{lead+rem} − π^lead)` (WP-R's
  `replacementBound`), on a variance class `φ_ω = vcost(ω) π_ω`;
* `consistent_inl`: from `consistent_degree` (the background gate, the price identities and
  `classCost ≤ C_n`);
* `consistent_inr`: a variance class with no weight on the diagonals and `ρ ≤ vcost π`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassInputsPaper

open Sarkozy.ClassBoundsPaper
open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Envelopes (classCost)

section Phi

variable {a : ℝ} {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R} {CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS}

namespace ClassData

variable (cd : ClassData CL)

/-- **The class bound on a degree class** (`thm:envelopes`(i), `cor:envelope-costs`;
WP-R's `replacementBound`): `φ_ω = C_n π^arm_ω + B'(π^{lead+rem}_ω − π^lead_ω)`. -/
theorem phi_inl {L : ℕ} {n : {n // n ∈ cd.N}} {ω : Choice (CL.T L)}
    (hω : ω ∈ cd.clsSel L (Sum.inl n)) :
    cd.φ L ω = cd.C n * mono (cd.yarm L) (selMono ω) +
      cd.Bp * (mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω) -
        mono (cd.ylead L) (selMono ω)) := by
  classical
  have hsel : IsSelection ω := (mem_filter.mp (mem_filter.mp hω).1).2
  have hc : paperCls cd.N (cd.kind L) (cd.vcls L) ω = some (Sum.inl n) := (mem_filter.mp hω).2
  unfold paperCls at hc
  simp only [hsel, ↓reduceIte] at hc
  split_ifs at hc with hm
  · simp only [Option.some.injEq, Sum.inl.injEq] at hc
    have hdeg : degreeOf (cd.kind L) (selMono ω) = n.val := by rw [← hc]
    unfold ClassData.φ replacedBound
    simp only [hm, ↓reduceIte]
    rw [hdeg]
    rfl
  · simp at hc

/-- **The class bound on a variance class** (`cor:var-classes`, `cor:variance:final`(i)):
`φ_ω = vcost(ω) π_ω`. -/
theorem phi_inr {L : ℕ} {v : cd.V L} {ω : Choice (CL.T L)}
    (hω : ω ∈ cd.clsSel L (Sum.inr v)) :
    cd.φ L ω = cd.vcost L ω * monomial (CL.π L) ω := by
  classical
  have hsel : IsSelection ω := (mem_filter.mp (mem_filter.mp hω).1).2
  have hc : paperCls cd.N (cd.kind L) (cd.vcls L) ω = some (Sum.inr v) := (mem_filter.mp hω).2
  unfold paperCls at hc
  simp only [hsel, ↓reduceIte] at hc
  split_ifs at hc with hm
  · simp at hc
  · unfold ClassData.φ replacedBound
    simp only [hm, ↓reduceIte]

end ClassData

end Phi

section Family

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} (cd : ClassData D.CL)

/-- **The steps of the class bound of the class `i` at one counterexample**: Steps 1–4 of
`thm:envelopes`(i) on a degree class (`EnvStepsAt`), the class-cost step of
`prop:background-variance`(a) on a variance class (`VarStepsAt`). -/
def ClassStepsAt (L : ℕ) (A : Finset ℤ) (i : cd.ι L) (WZ : ℝ) (ρ rr : Choice (D.CL.T L) → ℝ)
    (z K : ℝ) : Prop :=
  match i with
  | .inl n => Nonempty (EnvStepsAt (cd.clsSel L (.inl n))
      (fun ω => term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω)
      (fun ω => monomial (D.CL.π L) ω) ρ rr WZ (D.Y L A) z K)
  | .inr v => Nonempty (VarStepsAt (cd.clsSel L (.inr v))
      (fun ω => term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω)
      (fun ω => monomial (D.CL.π L) ω) ρ rr WZ (D.Y L A) z K)

omit [DecidableEq P] in
theorem ClassStepsAt.bound {cd : ClassData D.CL} {L : ℕ} {A : Finset ℤ} {i : cd.ι L} {WZ : ℝ}
    {ρ rr : Choice (D.CL.T L) → ℝ} {z K : ℝ} (H : ClassStepsAt cd L A i WZ ρ rr z K)
    (hY : 0 ≤ D.Y L A) (hz : 0 ≤ z) :
    ∑ ω ∈ cd.clsSel L i, |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
      WZ + ∑ ω ∈ cd.clsSel L i, ((ρ ω + z * K * monomial (D.CL.π L) ω) * D.Y L A + rr ω) := by
  rcases i with n | v
  · obtain ⟨S⟩ := H
    exact S.bound hY hz
  · obtain ⟨S⟩ := H
    exact S.bound hY hz

/-- **The steps of all class bounds, uniformly** (`def:robust`): at every counterexample, the steps
of every class with one `z_L → 0`, one `K` and remainders `rr ≥ 0` with `∑ rr ≤ c L^{-σ} α`. -/
def StepsFamily (Θ : ℕ → Type) [∀ L, Fintype (Θ L)] (Z : ∀ L, Finset ℤ → Θ L → ℝ)
    (wc : ∀ L, cd.ι L → Θ L → ℝ) (ρ : ∀ L, Choice (D.CL.T L) → ℝ) : Prop :=
  ∃ z : ℕ → ℝ, (∀ L, 0 ≤ z L) ∧ Tendsto z atTop (𝓝 0) ∧ ∃ K c : ℝ, 0 ≤ c ∧
    ∃ rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ, (∀ L A ω, 0 ≤ rr L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (∀ i, ClassStepsAt cd L A i (∑ j, wc L i j * Z L A j) (ρ L) (rr L A) (z L) K) ∧
      ∑ ω ∈ cd.sel L, rr L A ω ≤ remainder c L A

omit [DecidableEq P] in
/-- **The class bounds at energy level from the steps** (`thm:envelopes`(i), `cor:envelope-costs`,
`cor:var-classes`, `def:robust`): the field `energy` of `ClassEnergyData`, with `ε_L = z_L K`. -/
theorem energy_of_steps (Θ : ℕ → Type) [∀ L, Fintype (Θ L)] (Z : ∀ L, Finset ℤ → Θ L → ℝ)
    (wc : ∀ L, cd.ι L → Θ L → ℝ) (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (H : StepsFamily cd Θ Z wc ρ) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (∀ i, ∑ ω ∈ cd.clsSel L i, |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
        ∑ j, wc L i j * Z L A j +
          ∑ ω ∈ cd.clsSel L i, ((ρ L ω + ε L * monomial (D.CL.π L) ω) * D.Y L A + r L A ω)) ∧
      ∑ ω ∈ cd.sel L, r L A ω ≤ remainder c L A := by
  obtain ⟨z, hz0, hz, K, c, hc, rr, hrr0, H⟩ := H
  refine ⟨fun L => z L * K, ?_, c, hc, rr, hrr0, ?_⟩
  · simpa using hz.mul_const K
  filter_upwards [H] with L hL
  intro C hC hind A hA hcount
  obtain ⟨hst, hrs⟩ := hL C hC hind A hA hcount
  have hY : 0 < D.Y L A := TheoremCParam.counterexample_pos hC hcount
  exact ⟨fun i => (hst i).bound hY.le (hz0 L), hrs⟩

/-- **`ClassEnergyData` from the steps**: `energy := energy_of_steps`. -/
noncomputable def ClassEnergyData.ofSteps (Θ : ℕ → Type) [∀ L, Fintype (Θ L)]
    (Z : ∀ L, Finset ℤ → Θ L → ℝ) (u : ∀ L, Θ L → ℝ) (wc : ∀ L, cd.ι L → Θ L → ℝ)
    (wc_nonneg : ∀ L i j, 0 ≤ wc L i j) (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (hsteps : StepsFamily cd Θ Z wc ρ)
    (consistent : ∀ L i, ∑ j, wc L i j * u L j + ∑ ω ∈ cd.clsSel L i, ρ L ω ≤
      ∑ ω ∈ cd.clsSel L i, cd.φ L ω)
    (v : ∀ L, Θ L → ℝ) (errK : ℝ)
    (errw : ∀ L i, ∑ j, wc L i j * v L j ≤ errK * ∑ ω ∈ cd.clsSel L i, monomial (D.CL.π L) ω)
    (upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
      ∃ r : ∀ L, Finset ℤ → Θ L → ℝ, (∀ L A j, 0 ≤ r L A j) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∀ j, Z L A j ≤ (u L j + ε₃ L * v L j) * D.Y L A + r L A j) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ j, (∑ i, wc L i j) * r L A j ≤ remainder c₃ L A)) :
    ClassEnergyData D cd where
  Θ := Θ
  Z := Z
  u := u
  wc := wc
  wc_nonneg := wc_nonneg
  ρ := ρ
  energy := energy_of_steps cd Θ Z wc ρ hsteps
  consistent := consistent
  v := v
  errK := errK
  errw := errw
  upper := upper

omit [DecidableEq P] in
/-- **The consistency of a degree class** (`thm:envelopes`(i), `cor:envelope-costs`,
`lem:oct24:invariant-background`(v)), from `consistent_degree` with
`π^arm = mono y^arm`, `π^{lead+rem} = mono(y^lead + y^rem)`, `π^lead = mono y^lead`. -/
theorem consistent_inl {Θ : Type} [Fintype Θ] (L : ℕ) (n : {n // n ∈ cd.N}) (wc u : Θ → ℝ)
    (ρ wt CX υ : Choice (D.CL.T L) → ℝ) {κH κb M Minv U0 tU Rerr tδ B : ℝ}
    (hbg : ∑ j, wc j * u j ≤ (κH * Real.exp U0 - (κH - κb) * Real.exp tU) *
      ∑ ω ∈ cd.clsSel L (.inl n), mono (cd.yarm L) (selMono ω))
    (hρ : ∑ ω ∈ cd.clsSel L (.inl n), ρ ω ≤
      (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω) +
        B * (∑ ω ∈ cd.clsSel L (.inl n), wt ω * υ ω * CX ω))
    (harm : ∀ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω = mono (cd.yarm L) (selMono ω))
    (hυ0 : ∀ ω ∈ cd.clsSel L (.inl n), 0 ≤ wt ω * υ ω * CX ω)
    (hυ : ∀ ω ∈ cd.clsSel L (.inl n), wt ω * υ ω * CX ω ≤
      mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω) - mono (cd.ylead L) (selMono ω))
    (hB : B ≤ cd.Bp) (hB0 : 0 ≤ B) (hC : classCost κH κb M Minv U0 tU Rerr tδ ≤ cd.C n) :
    ∑ j, wc j * u j + ∑ ω ∈ cd.clsSel L (.inl n), ρ ω ≤
      ∑ ω ∈ cd.clsSel L (.inl n), cd.φ L ω := by
  rw [sum_congr rfl fun ω hω => cd.phi_inl hω]
  exact consistent_degree _ ρ (fun ω => mono (cd.yarm L) (selMono ω))
    (fun ω => mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω))
    (fun ω => mono (cd.ylead L) (selMono ω)) wt CX υ hbg hρ harm
    (fun ω _ => mono_nonneg (cd.yarm_nonneg L) _) hυ0 hυ hB hB0 hC

omit [DecidableEq P] in
/-- **The consistency of a variance class** (`cor:var-classes`, `cor:variance:final`(i)): with no
weight on the diagonals and `ρ_ω ≤ vcost(ω) π_ω`. -/
theorem consistent_inr {Θ : Type} [Fintype Θ] (L : ℕ) (v : cd.V L) (wc u : Θ → ℝ)
    (ρ : Choice (D.CL.T L) → ℝ) (hwc : ∀ j, wc j = 0)
    (hρ : ∀ ω ∈ cd.clsSel L (.inr v), ρ ω ≤ cd.vcost L ω * monomial (D.CL.π L) ω) :
    ∑ j, wc j * u j + ∑ ω ∈ cd.clsSel L (.inr v), ρ ω ≤
      ∑ ω ∈ cd.clsSel L (.inr v), cd.φ L ω := by
  rw [sum_congr rfl fun ω hω => cd.phi_inr hω]
  simp only [hwc, zero_mul, sum_const_zero, zero_add]
  exact sum_le_sum hρ

end Family

end Sarkozy.ClassInputsPaper
