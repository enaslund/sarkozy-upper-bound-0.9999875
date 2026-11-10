module

public import Sarkozy.OpsCore.Budget

@[expose] public section




open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.EnvelopeSteps Sarkozy.Envelopes
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.MeanCredit Sarkozy.MeanCredit2 Sarkozy.ClassData Sarkozy.Companion
open Sarkozy.CancellationSteps (PaperJ0)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {D : CD blockOf} {cd : ClassData D.CL} {K : Type}

/-- **The per-class budget**: at every scale, the class bounds of a degree class sum to at most
its budget `∑_𝒞 (δ_ω + r_ω) π_ω`. -/
def PhiBudgetClass (cd : ClassData D.CL) (labS : ∀ L, Choice (D.CL.T L) → Option K)
    (labK : K → PaperDiag) (r : ∀ L, Choice (D.CL.T L) → ℝ) : Prop :=
  ∀ L (n : {n // n ∈ cd.N}), ∑ ω ∈ cd.clsSel L (.inl n), cd.φ L ω ≤
    ∑ ω ∈ cd.clsSel L (.inl n), (delta labS labK L ω + r L ω) * monomial (D.CL.π L) ω

/-- The per-selection budget implies the per-class one. -/
theorem phiBudgetClass_of_phiBudget {labS : ∀ L, Choice (D.CL.T L) → Option K}
    {labK : K → PaperDiag} {r : ∀ L, Choice (D.CL.T L) → ℝ} (hP : PhiBudget cd labS labK r) :
    PhiBudgetClass cd labS labK r := by
  intro L n
  refine sum_le_sum fun ω hω => ?_
  have hω' := mem_filter.mp hω
  refine hP L ω hω'.1 ?_
  rw [hω'.2]
  exact Option.some_ne_none _

/-- **The class total from the per-class budget**: the conclusion of `classTotal_of_phiBudget`
(B10's `consistent_degree`, E4's gate `classCost ≤ C_n`) under the weaker hypothesis. -/
theorem classTotal_of_phiBudgetClass {labS : ∀ L, Choice (D.CL.T L) → Option K}
    {labK : K → PaperDiag} {r : ∀ L, Choice (D.CL.T L) → ℝ} (hP : PhiBudgetClass cd labS labK r)
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
  have hbud := hP L n
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

/-- **`hbg` and `hρ` of `DegreeInputs` from the per-class budget** (as `hbg_hρ_of_phiBudget`). -/
theorem hbg_hρ_of_phiBudgetClass {labS : ∀ L, Choice (D.CL.T L) → Option K}
    {labK : K → PaperDiag} {r : ∀ L, Choice (D.CL.T L) → ℝ} (hP : PhiBudgetClass cd labS labK r)
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
  exists_spill hS hbg (classTotal_of_phiBudgetClass hP L n wt CX υ harm hυ0 hυ hB hB0 hC)

/-! ### The residual coefficients read off `hcomp`'s `c` -/

/-- **The residual coefficient of a selection read off the comparison coefficient**:
`r_ω := c(deg ω) − δ_ω`, the largest value `hcomp` allows on a class selection. -/
noncomputable def rComp {Λ : Type} [DecidableEq Λ] (ℓ : ∀ L, Entry (D.CL.T L) → Λ) (c : (Λ → ℕ) → ℝ)
    (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag) (L : ℕ)
    (ω : Choice (D.CL.T L)) : ℝ :=
  c (deg (ℓ L) ω) - delta labS labK L ω

/-- **`hcomp` with `r := rComp`**: it holds as soon as it holds off the classes (`B + δ ≤ c`);
on the classes it is an equality. -/
theorem compId_rComp {Lt : Type} [DecidableEq Lt] {ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ Lt}
    {c : (MLetter ⊕ Lt → ℕ) → ℝ} {labS : ∀ L, Choice (D.CL.T L) → Option K}
    {labK : K → PaperDiag}
    (hoff : ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω = none →
      D.B + delta labS labK L ω ≤ c (deg (ℓ L) ω)) :
    CompId D cd labS labK ℓ c (rComp ℓ c labS labK) := by
  intro L ω hω
  by_cases h : cd.cls L ω = none
  · simp only [h, ↓reduceIte]
    exact hoff L ω hω h
  · simp only [h, ↓reduceIte, rComp, delta, sub_add_cancel, le_refl]

/-- **The class budget at `r := rComp` is the comparison of the class bounds with `c`**:
`∑_𝒞 φ_ω ≤ ∑_𝒞 c(deg ω) π_ω` at every scale and degree class. -/
theorem phiBudgetClass_rComp_iff {Λ : Type} [DecidableEq Λ] {ℓ : ∀ L, Entry (D.CL.T L) → Λ}
    {c : (Λ → ℕ) → ℝ} {labS : ∀ L, Choice (D.CL.T L) → Option K} {labK : K → PaperDiag} :
    PhiBudgetClass cd labS labK (rComp ℓ c labS labK) ↔
      ∀ L (n : {n // n ∈ cd.N}), ∑ ω ∈ cd.clsSel L (.inl n), cd.φ L ω ≤
        ∑ ω ∈ cd.clsSel L (.inl n), c (deg (ℓ L) ω) * monomial (D.CL.π L) ω := by
  have h : ∀ L (ω : Choice (D.CL.T L)),
      (delta labS labK L ω + rComp ℓ c labS labK L ω) = c (deg (ℓ L) ω) := fun L ω => by
    unfold rComp; ring
  simp only [PhiBudgetClass, h]

end Sarkozy.OpsCore
