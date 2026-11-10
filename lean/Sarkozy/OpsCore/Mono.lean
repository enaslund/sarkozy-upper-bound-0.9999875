module

public import Sarkozy.MainFinal2.Bundles
public import Sarkozy.Companion.ClassFields

@[expose] public section

/-!
# Monotonicity of the class steps in their budgets (OPS-L)

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i); `paper/sections/22_variance.tex`,
`prop:background-variance`(a).

The data of `ops` enter B11's `DegreeOps` only through the right sides of Step 4 (`WZ`), of the
residual identification `hρ` (`∑ ρ`) and of the remainders `hrr` (`∑ rr`); they enter B10's
`VarStepsAt` only through `0 ≤ WZ`, `hρ` and `hrr`. So both are monotone in these budgets:

* `DegreeOps.mono`, `VarStepsAt.mono`: a larger `WZ`, a larger class sum of `ρ` and of `rr`;
* `ClassStepsOps.mono`: `ops` for one choice of `Θ, Z, wc, ρ` gives `ops` for any other with
  larger diagonal budgets (at the counterexamples) and larger class sums of `ρ`;
* `ClassStepsOps.ofResidual`: in particular `ops` at any `ρ` with `ρ ≤ r π` on the class
  selections (`ResidualId`) gives `ops` at `ρ = r π`. This is the losslessness of fixing `ρ`.
-/

open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.ClassInputsPaper Sarkozy.EnvelopeSteps Sarkozy.MainFinal2
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-- **`DegreeOps` is monotone in its budgets**: Step 4's right side `WZ`, the class sum of the
residuals `ρ` and the class sum of the remainders `rr`. -/
def DegreeOps.mono {V : Type} [Fintype V] [DecidableEq V] {c : ReflectionCut V} {Ω : Type*}
    {𝒞 : Finset Ω} {I π ρ rr : Ω → ℝ} {WZ Y z K : ℝ} (H : DegreeOps c 𝒞 I π ρ rr WZ Y z K)
    {ρ' rr' : Ω → ℝ} {WZ' : ℝ} (hWZ : WZ ≤ WZ') (hρ : ∑ ω ∈ 𝒞, ρ ω ≤ ∑ ω ∈ 𝒞, ρ' ω)
    (hrr : ∑ ω ∈ 𝒞, rr ω ≤ ∑ ω ∈ 𝒞, rr' ω) : DegreeOps c 𝒞 I π ρ' rr' WZ' Y z K :=
  { H with
    step4 := H.step4.trans (by linarith)
    hρ := H.hρ.trans hρ
    hrr := H.hrr.trans hrr }

/-- **`VarStepsAt` is monotone in its budgets** (`WZ` enters only through `0 ≤ WZ`). -/
def VarStepsAt.mono {Ω : Type*} {R : Finset Ω} {I π ρ rr : Ω → ℝ} {WZ Y z K : ℝ}
    (H : VarStepsAt R I π ρ rr WZ Y z K) {ρ' rr' : Ω → ℝ} {WZ' : ℝ} (hWZ : 0 ≤ WZ')
    (hρ : ∑ ω ∈ R, ρ ω ≤ ∑ ω ∈ R, ρ' ω) (hrr : ∑ ω ∈ R, rr ω ≤ ∑ ω ∈ R, rr' ω) :
    VarStepsAt R I π ρ' rr' WZ' Y z K :=
  { H with
    hWZ := hWZ
    hρ := H.hρ.trans hρ
    hrr := H.hrr.trans hrr }

section Ops

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {cd : ClassData D.CL}

omit [DecidableEq P] in
/-- **`ops` is monotone in its data**: if at every counterexample the diagonal budget of every
degree class is at least the old one and that of every variance class is nonnegative, and the
class sums of the residuals are at least the old ones, then `ops` for the old data gives `ops`
for the new. -/
theorem ClassStepsOps.mono {Θ Θ' : ℕ → Type} [∀ L, Fintype (Θ L)] [∀ L, Fintype (Θ' L)]
    {Z : ∀ L, Finset ℤ → Θ L → ℝ} {Z' : ∀ L, Finset ℤ → Θ' L → ℝ}
    {wc : ∀ L, cd.ι L → Θ L → ℝ} {wc' : ∀ L, cd.ι L → Θ' L → ℝ}
    {ρ ρ' : ∀ L, Choice (D.CL.T L) → ℝ} (O : ClassStepsOps cd Θ Z wc ρ)
    (hWZ : Param.AtCounterexamples (Param.Params.ofDecay a) D.Y fun L A =>
      (∀ n : {n // n ∈ cd.N}, ∑ j, wc L (.inl n) j * Z L A j ≤ ∑ j, wc' L (.inl n) j * Z' L A j) ∧
      (∀ v : cd.V L, 0 ≤ ∑ j, wc' L (.inr v) j * Z' L A j))
    (hρ : ∀ L (i : cd.ι L), ∑ ω ∈ cd.clsSel L i, ρ L ω ≤ ∑ ω ∈ cd.clsSel L i, ρ' L ω) :
    Nonempty (ClassStepsOps cd Θ' Z' wc' ρ') := by
  refine ⟨⟨O.z, O.hz0, O.hz, O.K, O.c₀, O.hc₀, O.rr, O.hrr0, ?_⟩⟩
  filter_upwards [O.H, hWZ] with L hL hW
  intro C hC hind A hA hcount
  obtain ⟨hdeg, hvar, hrs⟩ := hL C hC hind A hA hcount
  obtain ⟨hWd, hWv⟩ := hW C hC hind A hA hcount
  refine ⟨fun n => ?_, fun v => ?_, hrs⟩
  · obtain ⟨Hn⟩ := hdeg n
    exact ⟨DegreeOps.mono Hn (hWd n) (hρ L _) le_rfl⟩
  · obtain ⟨Hv⟩ := hvar v
    exact ⟨VarStepsAt.mono Hv (hWv v) (hρ L _) le_rfl⟩

end Ops

section Residual

open Sarkozy.MeanCredit Sarkozy.Companion
open Sarkozy.CancellationSteps (PaperJ0)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {D : CD blockOf} {cd : ClassData D.CL}

/-- **The residuals at their bound**: `ρ_ω = r_ω π_ω` (`cor:envelope-costs`). -/
noncomputable def rhoOf (r : ∀ L, Choice (D.CL.T L) → ℝ) (L : ℕ) (ω : Choice (D.CL.T L)) : ℝ :=
  r L ω * monomial (D.CL.π L) ω

/-- `hρ` holds at `ρ = r π` (with equality). -/
theorem residualId_rhoOf (r : ∀ L, Choice (D.CL.T L) → ℝ) : ResidualId D cd (rhoOf r) r :=
  fun _ _ _ _ => le_rfl

/-- On a class, `ResidualId` bounds the class sum of `ρ` by that of `r π`. -/
theorem sum_le_rhoOf {ρ r : ∀ L, Choice (D.CL.T L) → ℝ} (hρ : ResidualId D cd ρ r) (L : ℕ)
    (i : cd.ι L) : ∑ ω ∈ cd.clsSel L i, ρ L ω ≤ ∑ ω ∈ cd.clsSel L i, rhoOf r L ω := by
  refine sum_le_sum fun ω hω => ?_
  have hω' := mem_filter.mp hω
  refine hρ L ω hω'.1 ?_
  rw [hω'.2]
  exact Option.some_ne_none i

/-- **Fixing `ρ := r π` is lossless**: `ops` at any `ρ` with `ResidualId ρ r` gives `ops` at
`r π` (same `Θ`, `Z`, `wc`). -/
theorem ClassStepsOps.ofResidual {Θ : ℕ → Type} [∀ L, Fintype (Θ L)]
    {Z : ∀ L, Finset ℤ → Θ L → ℝ} {wc : ∀ L, cd.ι L → Θ L → ℝ}
    {ρ r : ∀ L, Choice (D.CL.T L) → ℝ} (O : ClassStepsOps cd Θ Z wc ρ)
    (hρ : ResidualId D cd ρ r) : Nonempty (ClassStepsOps cd Θ Z wc (rhoOf r)) := by
  refine ⟨⟨O.z, O.hz0, O.hz, O.K, O.c₀, O.hc₀, O.rr, O.hrr0, ?_⟩⟩
  filter_upwards [O.H] with L hL
  intro C hC hind A hA hcount
  obtain ⟨hdeg, hvar, hrs⟩ := hL C hC hind A hA hcount
  refine ⟨fun n => ?_, fun v => ?_, hrs⟩
  · obtain ⟨Hn⟩ := hdeg n
    exact ⟨DegreeOps.mono Hn le_rfl (sum_le_rhoOf hρ L _) le_rfl⟩
  · obtain ⟨Hv⟩ := hvar v
    exact ⟨VarStepsAt.mono Hv Hv.hWZ (sum_le_rhoOf hρ L _) le_rfl⟩

end Residual

end Sarkozy.OpsCore
