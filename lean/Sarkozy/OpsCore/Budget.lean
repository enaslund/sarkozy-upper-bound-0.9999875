module

public import Sarkozy.OpsCore.Evals

@[expose] public section

/-!
# The per-class budget as one per-selection inequality (OPS-L)

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i) (the class bound
`φ_ω = C_n π^arm_ω + B'(π^{lead+rem}_ω − π^lead_ω)`, `eq:envelope-class-bound`),
`cor:envelope-costs`; `paper/sections/24a_joint_mean.tex`, the residual table;
`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`.

`exists_spill` reduces the inputs `hbg`, `hρ` of `DegreeInputs` to one class-total inequality.
Here it is reduced further, to a statement about the class data `cd` and the labels alone:

* **`PhiBudget cd labS labK r`** (the remaining evaluation, kind F): every class selection's
  class bound `φ_ω` (`cd.φ`: the class costs `C_n`, the constant `B'` and the auxiliary prices
  `y^arm, y^lead, y^rem` of `cd`, evaluated with the selection's prices at the goal exponent
  `a_T`) is at most its budget `(δ_ω + r_ω) π_ω`, with `δ_ω = diagW(labK(labS ω))` and `r_ω` the
  residual coefficient. With `hcomp` (`r_ω + δ_ω ≤ c(deg ω)`) it says `φ_ω ≤ c(deg ω) π_ω`;
* **`classTotal_of_phiBudget`**: the class total of `exists_spill` from `PhiBudget`, E4's gate
  `classCost ≤ C_n` and the identification of the raw-arm and remainder weights with the
  auxiliary prices (B10's `consistent_degree`);
* **`hbg_hρ_of_phiBudget`**: hence `hbg`, `hρ` with some spill;
* **`phiBudget_of_monomials`**: `PhiBudget` from its monomial form, per degree class
  (`C_n π^arm + B'(π^{lead+rem} − π^lead) ≤ (δ + r)π`) and per variance class
  (`vcost ≤ δ + r`).

At the rebase the constants of `cd` are those of `κ′` (the obligations' data). `PhiBudget` is then
a monomial inequality per selection; it is finite once `r_ω`, `δ_ω` depend only on the class
type and the label (as in the residual table).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.EnvelopeSteps Sarkozy.Envelopes
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.MeanCredit Sarkozy.ClassData
open Sarkozy.CancellationSteps (PaperJ0)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {D : CD blockOf} {cd : ClassData D.CL} {K : Type} [Fintype K] [DecidableEq K]

/-- **The per-selection budget** (kind F, evaluation): every class selection's class bound is at
most its budget `(δ_ω + r_ω) π_ω`. -/
def PhiBudget (cd : ClassData D.CL) (labS : ∀ L, Choice (D.CL.T L) → Option K)
    (labK : K → PaperDiag) (r : ∀ L, Choice (D.CL.T L) → ℝ) : Prop :=
  ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none →
    cd.φ L ω ≤ (delta labS labK L ω + r L ω) * monomial (D.CL.π L) ω

omit [Fintype K] [DecidableEq K] in
/-- **The class total from the per-selection budget** (with E4's gate and B10's
`consistent_degree`): for a degree class with the Step 4 background coefficient `κ` and the
coupling constants of `classCost`, `(κ + M R_err − M^inv e^{tU} tδ) ∑ π̃ C_X + B ∑ π̃ υ C_X ≤
∑_𝒞 δ_ω π_ω + ∑_𝒞 r_ω π_ω`. -/
theorem classTotal_of_phiBudget {labS : ∀ L, Choice (D.CL.T L) → Option K}
    {labK : K → PaperDiag} {r : ∀ L, Choice (D.CL.T L) → ℝ} (hP : PhiBudget cd labS labK r)
    (L : ℕ) (n : {n // n ∈ cd.N}) (wt CX υ : Choice (D.CL.T L) → ℝ)
    {κH κb M Minv U0 tU Rerr tδ Bc : ℝ}
    (harm : ∀ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω = mono (cd.yarm L) (selMono ω))
    (hυ0 : ∀ ω ∈ cd.clsSel L (.inl n), 0 ≤ wt ω * υ ω * CX ω)
    (hυ : ∀ ω ∈ cd.clsSel L (.inl n), wt ω * υ ω * CX ω ≤
      mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω) - mono (cd.ylead L) (selMono ω))
    (hB : Bc ≤ cd.Bp) (hB0 : 0 ≤ Bc) (hC : classCost κH κb M Minv U0 tU Rerr tδ ≤ cd.C n) :
    ((κH * Real.exp U0 - (κH - κb) * Real.exp tU) + (M * Rerr - Minv * Real.exp tU * tδ)) *
        (∑ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω) +
      Bc * (∑ ω ∈ cd.clsSel L (.inl n), wt ω * υ ω * CX ω) ≤
      (∑ ω ∈ cd.clsSel L (.inl n), delta labS labK L ω * monomial (D.CL.π L) ω) +
        ∑ ω ∈ cd.clsSel L (.inl n), rhoOf r L ω := by
  set 𝒞 := cd.clsSel L (.inl n)
  set κ := κH * Real.exp U0 - (κH - κb) * Real.exp tU
  set Mc := M * Rerr - Minv * Real.exp tU * tδ
  have hsarm : ∑ ω ∈ 𝒞, wt ω * CX ω = ∑ ω ∈ 𝒞, mono (cd.yarm L) (selMono ω) :=
    sum_congr rfl harm
  -- B10's consistency with `WU := κ ∑ π^arm` and `ρ' := Mc π̃ C_X + B π̃ υ C_X`
  have hcons := consistent_degree 𝒞 (fun ω => Mc * (wt ω * CX ω) + Bc * (wt ω * υ ω * CX ω))
    (fun ω => mono (cd.yarm L) (selMono ω))
    (fun ω => mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω))
    (fun ω => mono (cd.ylead L) (selMono ω)) wt CX υ (WU := κ * ∑ ω ∈ 𝒞,
      mono (cd.yarm L) (selMono ω)) (κH := κH) (κb := κb) (U0 := U0) (tU := tU) le_rfl
    (by rw [sum_add_distrib, ← mul_sum, ← mul_sum]) harm
    (fun ω _ => mono_nonneg (cd.yarm_nonneg L) _) hυ0 hυ hB hB0 hC
  have hphi : ∑ ω ∈ 𝒞, (cd.C n * mono (cd.yarm L) (selMono ω) +
      cd.Bp * (mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω) -
        mono (cd.ylead L) (selMono ω))) = ∑ ω ∈ 𝒞, cd.φ L ω :=
    sum_congr rfl fun ω hω => (cd.phi_inl hω).symm
  have hbud : ∑ ω ∈ 𝒞, cd.φ L ω ≤ ∑ ω ∈ 𝒞, (delta labS labK L ω + r L ω) *
      monomial (D.CL.π L) ω := by
    refine sum_le_sum fun ω hω => ?_
    have hω' := mem_filter.mp hω
    refine hP L ω hω'.1 ?_
    rw [hω'.2]
    exact Option.some_ne_none _
  have esplit : ∑ ω ∈ 𝒞, (delta labS labK L ω + r L ω) * monomial (D.CL.π L) ω =
      (∑ ω ∈ 𝒞, delta labS labK L ω * monomial (D.CL.π L) ω) + ∑ ω ∈ 𝒞, rhoOf r L ω := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by unfold rhoOf; ring
  have hρsum : ∑ ω ∈ 𝒞, (Mc * (wt ω * CX ω) + Bc * (wt ω * υ ω * CX ω)) =
      Mc * (∑ ω ∈ 𝒞, wt ω * CX ω) + Bc * (∑ ω ∈ 𝒞, wt ω * υ ω * CX ω) := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [hρsum, hphi] at hcons
  rw [← esplit, ← hsarm] at *
  nlinarith [hcons, hbud]

omit [Fintype K] [DecidableEq K] in
/-- **`hbg` and `hρ` of `DegreeInputs` from the per-selection budget**: if Step 4 ends at
`κ (∑ π̃ C_X) Y` with `∑ π̃ C_X > 0`, there is a spill with which both hold. -/
theorem hbg_hρ_of_phiBudget {labS : ∀ L, Choice (D.CL.T L) → Option K}
    {labK : K → PaperDiag} {r : ∀ L, Choice (D.CL.T L) → ℝ} (hP : PhiBudget cd labS labK r)
    (L : ℕ) (n : {n // n ∈ cd.N}) (wt CX υ : Choice (D.CL.T L) → ℝ)
    {κH κb M Minv U0 tU Rerr tδ Bc Y Wbg : ℝ}
    (harm : ∀ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω = mono (cd.yarm L) (selMono ω))
    (hυ0 : ∀ ω ∈ cd.clsSel L (.inl n), 0 ≤ wt ω * υ ω * CX ω)
    (hυ : ∀ ω ∈ cd.clsSel L (.inl n), wt ω * υ ω * CX ω ≤
      mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω) - mono (cd.ylead L) (selMono ω))
    (hB : Bc ≤ cd.Bp) (hB0 : 0 ≤ Bc) (hC : classCost κH κb M Minv U0 tU Rerr tδ ≤ cd.C n)
    (hS : 0 < ∑ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω)
    (hbg : Wbg ≤ (κH * Real.exp U0 - (κH - κb) * Real.exp tU) *
      (∑ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω) * Y) :
    ∃ spill : ℝ, Wbg ≤ (∑ ω ∈ cd.clsSel L (.inl n), delta labS labK L ω *
        monomial (D.CL.π L) ω) * Y + spill * (∑ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω) * Y ∧
      (M * Rerr - Minv * Real.exp tU * tδ + spill) *
          (∑ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω) +
        Bc * (∑ ω ∈ cd.clsSel L (.inl n), wt ω * υ ω * CX ω) ≤
        ∑ ω ∈ cd.clsSel L (.inl n), rhoOf r L ω :=
  exists_spill hS hbg (classTotal_of_phiBudget hP L n wt CX υ harm hυ0 hυ hB hB0 hC)

omit [Fintype K] [DecidableEq K] in
/-- **`PhiBudget` in monomial form** (the shape of the finite check): on a degree class `n`,
`C_n π^arm_ω + B'(π^{lead+rem}_ω − π^lead_ω) ≤ (δ_ω + r_ω) π_ω` (the auxiliary monomials of `cd`);
on a variance class, `vcost(ω) π_ω ≤ (δ_ω + r_ω) π_ω`. -/
theorem phiBudget_of_monomials {labS : ∀ L, Choice (D.CL.T L) → Option K}
    {labK : K → PaperDiag} {r : ∀ L, Choice (D.CL.T L) → ℝ}
    (hdeg : ∀ L (n : {n // n ∈ cd.N}), ∀ ω ∈ cd.clsSel L (.inl n),
      cd.C n * mono (cd.yarm L) (selMono ω) +
          cd.Bp * (mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω) -
            mono (cd.ylead L) (selMono ω)) ≤
        (delta labS labK L ω + r L ω) * monomial (D.CL.π L) ω)
    (hvar : ∀ L (v : cd.V L), ∀ ω ∈ cd.clsSel L (.inr v),
      cd.vcost L ω * monomial (D.CL.π L) ω ≤
        (delta labS labK L ω + r L ω) * monomial (D.CL.π L) ω) :
    PhiBudget cd labS labK r := by
  intro L ω hω hc
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hc
  have hmem : ω ∈ cd.clsSel L i := mem_filter.mpr ⟨hω, hi⟩
  rcases i with n | v
  · rw [cd.phi_inl hmem]
    exact hdeg L n ω hmem
  · rw [cd.phi_inr hmem]
    exact hvar L v ω hmem

end Sarkozy.OpsCore
