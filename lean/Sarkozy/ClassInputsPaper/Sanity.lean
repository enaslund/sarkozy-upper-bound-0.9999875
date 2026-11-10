module

public import Sarkozy.ClassInputsPaper.Energy

@[expose] public section

/-!
# Non-vacuity of B10's new inputs

* `ClassEnergyData.ofRobust`, **`classEnergyData_nonempty_iff`**: `ClassEnergyData D cd` is
  inhabited exactly when the robust evaluated class bounds `cd.Robust` hold (with no diagonals,
  `ρ = φ`, `errK = 0`, `upper` trivial). So its fields are jointly satisfiable whenever B4's
  `ClassInputs` is, and they are not weaker than `ClassInputs.robust`.
* `toyEnvSteps`: the steps of `thm:envelopes`(i) for a one-selection class with a nonzero term
  `I = 3/4`, nonzero leading and remainder energies, a nonzero coupling mass and a nonzero
  energy on the diagonals; `toyEnvSteps_bound` is tight (`3/4 ≤ 1/4 + 1/2`).
* `toyVarSteps`: the class-cost step for a one-selection variance class with `I = 1/2`, a nonzero
  restoration bound and the gain `[b̃ − R_*]_+ = 1/2` used; `toyVarSteps_bound` is tight.
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

section Data

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **`ClassEnergyData` from the robust evaluated class bounds**, with no diagonal. -/
noncomputable def ClassEnergyData.ofRobust (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (cd : ClassData D.CL) (hR : cd.Robust) : ClassEnergyData D cd where
  Θ _ := Empty
  ΘFintype _ := inferInstanceAs (Fintype Empty)
  Z _ _ j := j.elim
  u _ j := j.elim
  wc _ _ j := j.elim
  wc_nonneg _ _ j := j.elim
  ρ L ω := cd.φ L ω
  energy := by
    obtain ⟨ε, hε, c, hc, r, hr, H⟩ := hR
    refine ⟨ε, hε, c, hc, r, hr, ?_⟩
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] using H
  consistent L i := by simp
  v _ j := j.elim
  errK := 0
  errw L i := by simp
  upper := ⟨fun _ => 0, fun _ => le_rfl, tendsto_const_nhds, 0, le_rfl, fun _ _ j => j.elim,
    fun _ _ j => j.elim, Eventually.of_forall fun _ _ _ _ _ _ _ j => j.elim,
    Eventually.of_forall fun L _ _ _ A _ _ => by simp [remainder]⟩

omit [DecidableEq P] in
/-- **`ClassEnergyData D cd` is inhabited exactly when `cd.Robust` holds.** -/
theorem classEnergyData_nonempty_iff (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (cd : ClassData D.CL) : Nonempty (ClassEnergyData D cd) ↔ cd.Robust :=
  ⟨fun ⟨ED⟩ => ED.robust, fun hR => ⟨ClassEnergyData.ofRobust D cd hR⟩⟩

end Data

/-! ## Toy instances of the steps -/

/-- **A one-selection degree class satisfying Steps 1–4** with `I = 3/4`, `Lead = 1/2`,
`Rem = 1/4`, `υ = 1/4`, `B = 1`, `M = 1`, `R_err = 1/4`, `W_Z = 1/4`, `ρ = 1/2`, `K = 3`. -/
noncomputable def toyEnvSteps :
    EnvStepsAt (univ : Finset Unit) (fun _ => 3 / 4) (fun _ => 1) (fun _ => 1 / 2) (fun _ => 0)
      (1 / 4) 1 0 3 where
  Lead _ := 1 / 2
  Rem _ := 1 / 4
  YN _ := 1 / 2
  YN0 _ := 1 / 4
  υ _ := 1 / 4
  Mω _ := 1
  Mh _ := 0
  wt _ := 1
  CX _ := 1
  r₁ _ := 0
  r₃ _ := 0
  r₄ := 0
  B := 1
  M := 1
  Minv := 0
  Rerr := 1 / 4
  tU := 0
  tδ := 0
  hwt _ _ := zero_le_one
  hR := by norm_num
  htδ := le_rfl
  hI _ _ := by norm_num
  step1 _ _ := by norm_num [abs_of_pos]
  step2 _ _ := by norm_num [abs_of_pos]
  step3 _ _ := by norm_num
  step4 := by norm_num
  hM := by simp
  hMinv := by simp
  hρ := by norm_num
  hπ _ _ := by norm_num
  hrr := by simp

theorem toyEnvSteps_bound :
    ∑ ω ∈ (univ : Finset Unit), |(fun _ => (3 / 4 : ℝ)) ω| ≤
      1 / 4 + ∑ ω ∈ (univ : Finset Unit),
        (((fun _ => (1 / 2 : ℝ)) ω + 0 * 3 * (fun _ => (1 : ℝ)) ω) * 1 + (fun _ => (0 : ℝ)) ω) :=
  toyEnvSteps.bound zero_le_one le_rfl

/-- **A one-selection variance class satisfying the class-cost step** with `I = 1/2`,
`DN = 1`, `JN = JO = 1/2`, `B = 1`, `b̃ = 1/2`, `R_* = 0`, `ρ = 1/2`, `K = 3`. -/
noncomputable def toyVarSteps :
    VarStepsAt (univ : Finset Unit) (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1 / 2) (fun _ => 0)
      0 1 0 3 where
  DN _ := 1
  JN _ := 1 / 2
  JO _ := 1 / 2
  γ _ := 1
  CX _ := 1
  rD _ := 0
  rJ _ := 0
  r₀ := 0
  Bf := 1
  Rerr := 0
  Rstar := 0
  bt := 1 / 2
  hγ _ _ := zero_le_one
  hCX _ _ := zero_le_one
  hr₀ := le_rfl
  hrJ _ _ := le_rfl
  hRs := le_rfl
  hI _ _ := by norm_num [abs_of_pos]
  hJN0 _ _ := by norm_num
  hDN _ _ := by norm_num
  hJN _ _ := by norm_num
  hres := by norm_num
  hWZ := le_rfl
  hρ := by norm_num
  hπ _ _ := by norm_num
  hrr := by simp

theorem toyVarSteps_bound :
    ∑ ω ∈ (univ : Finset Unit), |(fun _ => (1 / 2 : ℝ)) ω| ≤
      0 + ∑ ω ∈ (univ : Finset Unit),
        (((fun _ => (1 / 2 : ℝ)) ω + 0 * 3 * (fun _ => (1 : ℝ)) ω) * 1 + (fun _ => (0 : ℝ)) ω) :=
  toyVarSteps.bound zero_le_one le_rfl

end Sarkozy.ClassInputsPaper
