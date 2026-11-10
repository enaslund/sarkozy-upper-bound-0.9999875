module

public import Sarkozy.EnvelopeSteps.StepsOneTwo
public import Sarkozy.EnvelopeSteps.MaskLift
public import Sarkozy.ClassInputsPaper.Energy

@[expose] public section

/-!
# `ClassEnergyData.ofSteps` from operator data (`thm:envelopes`(i), Steps 1–2 proved)

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i) and its proof; B10's
`ClassInputsPaper.ClassEnergyData.ofSteps` (`paper/sections/09_comparison_theorem.tex`,
`def:robust`).

* **`DegreeOps`**: the data of Steps 1–4 of one degree class at one counterexample, with Steps 1
  and 2 given by **operator** data on the actual half spaces (objects `Obj ω`, half marginal
  `m_ω`, placement `φ_ω`, the energy functionals `Eλ_ω`, `EN_ω` with (P5), the operators `L_ω`,
  `Υ_ω`, `D_ω`), and the rest as in B10's `EnvStepsAt`; `DegreeOps.toEnvSteps` proves B10's
  `step1`, `step2` (`envStepsOfOperators`).
* **`hdom_of_mask`**: the domination input of `DegreeOps` (`±L_ω ⪯ D_ω`) from the lifting step
  `mask_lift` (`lem:oct24:mask-schur`(a)), given the kernels of `L_ω` and `D_ω` relative to `m_ω`.
* **`classStepsAt_inl`**, **`classStepsAt_inr`**: B10's `ClassStepsAt` for a degree class from
  `DegreeOps`, for a variance class from `VarStepsAt` (e.g. B10's `VarStepsAt.ofRecords`).
* **`stepsFamily_of_ops`**: B10's `StepsFamily` from these at every counterexample.
* **`classEnergyData_ofOps`**: `ClassEnergyData.ofSteps` with this `StepsFamily`.
-/

open Filter Finset
open scoped Topology BigOperators Kronecker Matrix

namespace Sarkozy.EnvelopeSteps

open Sarkozy.ClassInputsPaper

/-- **The data of Steps 1–4 of one degree class**, Steps 1–2 as operator inequalities. The fields
are those of `envStepsOfOperators`. -/
structure DegreeOps {V : Type} [Fintype V] [DecidableEq V] (c : ReflectionCut V) {Ω : Type*}
    (𝒞 : Finset Ω) (I π ρ rr : Ω → ℝ) (WZ Y z K : ℝ) where
  Obj : Ω → Type
  instFO : ∀ ω, Fintype (Obj ω)
  instDO : ∀ ω, DecidableEq (Obj ω)
  Lab : Ω → Type
  instFL : ∀ ω, Fintype (Lab ω)
  instDL : ∀ ω, DecidableEq (Lab ω)
  /-- The energy functionals `κ ↦ Y_{κ ⊗ λ_{-X}}` and `κ ↦ Y_{κ ⊗ Ñ_{-X}}`, with (P5). -/
  Elam : ∀ ω, (((V → Lab ω) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ
  EN : ∀ ω, (((V → Lab ω) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ
  hE : ∀ ω ∈ 𝒞, P5 c (Elam ω) (EN ω)
  /-- The actual half marginals and the placements. -/
  m : ∀ ω, Obj ω → ℝ
  φ : ∀ ω, Obj ω → (c.Half → Lab ω)
  /-- The leading star tensor, the remainder and the envelope. -/
  Lop : ∀ ω, (Obj ω → ℝ) →ₗ[ℝ] (Obj ω → ℝ)
  Υop : ∀ ω, (Obj ω → ℝ) →ₗ[ℝ] (Obj ω → ℝ)
  Dop : ∀ ω, (Obj ω → ℝ) →ₗ[ℝ] (Obj ω → ℝ)
  /-- `lem:oct24:mask-schur`(a): `±L_ω ⪯ D_ω`. -/
  hdom : ∀ ω ∈ 𝒞, OpLE (m ω) (Lop ω) (Dop ω) ∧ OpLE (m ω) (-Lop ω) (Dop ω)
  /-- `eq:oct24:star-tensor-error`: `Υ_ω` symmetric with `‖Υ_ω‖ ≤ υ_ω`. -/
  υ : Ω → ℝ
  hυ : ∀ ω ∈ 𝒞, 0 ≤ υ ω
  hΥsym : ∀ ω ∈ 𝒞, ∀ f g, ip (m ω) f (Υop ω g) = ip (m ω) g (Υop ω f)
  hΥ : ∀ ω ∈ 𝒞, ∀ f, |ip (m ω) f (Υop ω f)| ≤ υ ω * ip (m ω) f f
  /-- (E1) for the diagonal `Diag_ω`. -/
  B : ℝ
  CX : Ω → ℝ
  r₁' : Ω → ℝ
  hE1 : ∀ ω ∈ 𝒞, EN ω (c.diagonalLaw (push (m ω) (φ ω))) ≤ (B + z) * CX ω * Y + r₁' ω
  /-- (N4). -/
  wt : Ω → ℝ
  hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω
  hI : ∀ ω ∈ 𝒞, I ω = wt ω * (Elam ω (place c (m ω) (φ ω) (Lop ω)) +
    Elam ω (place c (m ω) (φ ω) (Υop ω)))
  /-- Steps 3–4 and the evaluations, as in `EnvStepsAt`. -/
  YN0 : Ω → ℝ
  Mω : Ω → ℝ
  Mh : Ω → ℝ
  r₃ : Ω → ℝ
  r₄ : ℝ
  M : ℝ
  Minv : ℝ
  Rerr : ℝ
  tU : ℝ
  tδ : ℝ
  hR : 0 ≤ Rerr
  htδ : 0 ≤ tδ
  step3 : ∀ ω ∈ 𝒞, EN ω (place c (m ω) (φ ω) (Dop ω)) ≤
    YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX ω * Y + r₃ ω
  step4 : ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤ WZ + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y + r₄
  hM : ∑ ω ∈ 𝒞, wt ω * CX ω * Mω ω ≤ M * ∑ ω ∈ 𝒞, wt ω * CX ω
  hMinv : Minv * ∑ ω ∈ 𝒞, wt ω * CX ω ≤ ∑ ω ∈ 𝒞, wt ω * CX ω * Mh ω
  hρ : (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, wt ω * CX ω) +
    B * (∑ ω ∈ 𝒞, wt ω * υ ω * CX ω) ≤ ∑ ω ∈ 𝒞, ρ ω
  hπ : ∀ ω ∈ 𝒞, wt ω * (2 + υ ω) * CX ω ≤ K * π ω
  hrr : ∑ ω ∈ 𝒞, wt ω * (υ ω * r₁' ω + r₃ ω) + r₄ ≤ ∑ ω ∈ 𝒞, rr ω

attribute [instance] DegreeOps.instFO DegreeOps.instDO DegreeOps.instFL DegreeOps.instDL

/-- **B10's `EnvStepsAt` from `DegreeOps`**, with `step1` and `step2` proved. -/
noncomputable def DegreeOps.toEnvSteps {V : Type} [Fintype V] [DecidableEq V]
    {c : ReflectionCut V} {Ω : Type*} {𝒞 : Finset Ω} {I π ρ rr : Ω → ℝ} {WZ Y z K : ℝ}
    (H : DegreeOps c 𝒞 I π ρ rr WZ Y z K) : EnvStepsAt 𝒞 I π ρ rr WZ Y z K :=
  envStepsOfOperators 𝒞 I π ρ rr c H.Obj H.Lab H.Elam H.EN H.hE H.m H.φ H.Lop H.Υop H.Dop H.hdom H.υ
    H.hυ H.hΥsym H.hΥ H.B H.CX H.r₁' H.hE1 H.wt H.hwt H.hI H.YN0 H.Mω H.Mh H.r₃ H.r₄ H.M H.Minv
    H.Rerr H.tU H.tδ H.hR H.htδ H.step3 H.step4 H.hM H.hMinv H.hρ H.hπ H.hrr

/-- **The domination input from the lifting step** (`lem:oct24:mask-schur`(a), Step 2 of
`thm:envelopes`): with the leading star tensor written as `∑_s c_s Ξ_s T_s Ξ_s^*` over the singleton
sectors, the joint spectral condition `hspec` (move 1), the enlargement `hLift` (move 4), and the
kernels of `Lead`, `Lop` relative to `m` equal to these matrices, `±Lead ⪯ Lop` in `L²(m)`. -/
theorem hdom_of_mask {O W S : Type*} [Fintype O] [DecidableEq O] [Fintype W] [DecidableEq W]
    [Fintype S] {Z : S → Type*} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (D : Matrix W W ℝ) (T : ∀ s, Matrix (W × Z s) (W × Z s) ℝ) (cs : S → ℝ)
    (hc0 : ∀ s, 0 ≤ cs s) (hc1 : ∀ s, cs s ≤ 1)
    (hspec : ∀ s, (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ) + T s).PosSemidef ∧
      (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ) - T s).PosSemidef)
    (Ξ : ∀ s, Matrix O (W × Z s) ℝ) (Lift : Matrix O O ℝ)
    (hLift : (Lift - ∑ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ).PosSemidef)
    {m : O → ℝ} {Lead Lop : (O → ℝ) →ₗ[ℝ] (O → ℝ)}
    (hL : ∀ x y, kern m Lead x y = (∑ s, cs s • (Ξ s * T s * (Ξ s)ᴴ)) x y)
    (hLop : ∀ x y, kern m Lop x y = Lift x y) :
    OpLE m Lead Lop ∧ OpLE m (-Lead) Lop := by
  obtain ⟨hp, hm⟩ := mask_lift D T cs hc0 hc1 hspec Ξ Lift hLift
  exact opLE_of_mask hL hLop hp hm

section Family

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

open Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame
  Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} (cd : ClassData D.CL)
  {V : Type} [Fintype V] [DecidableEq V] (c : ReflectionCut V)

/-- The term `I_ω` of a selection. -/
noncomputable abbrev termAt (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) : ℝ :=
  term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω

omit [DecidableEq P] in
/-- **B10's `ClassStepsAt` for a degree class from `DegreeOps`.** -/
theorem classStepsAt_inl (L : ℕ) (A : Finset ℤ) (n : {n // n ∈ cd.N}) (WZ : ℝ)
    (ρ rr : Choice (D.CL.T L) → ℝ) (z K : ℝ)
    (H : DegreeOps c (cd.clsSel L (.inl n)) (termAt (D := D) L A)
      (fun ω => monomial (D.CL.π L) ω) ρ rr WZ (D.Y L A) z K) :
    ClassStepsAt cd L A (.inl n) WZ ρ rr z K :=
  ⟨H.toEnvSteps⟩

omit [DecidableEq P] in
/-- **B10's `ClassStepsAt` for a variance class from `VarStepsAt`.** -/
theorem classStepsAt_inr (L : ℕ) (A : Finset ℤ) (v : cd.V L) (WZ : ℝ)
    (ρ rr : Choice (D.CL.T L) → ℝ) (z K : ℝ)
    (H : VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := D) L A)
      (fun ω => monomial (D.CL.π L) ω) ρ rr WZ (D.Y L A) z K) :
    ClassStepsAt cd L A (.inr v) WZ ρ rr z K :=
  ⟨H⟩

omit [DecidableEq P] in
/-- **B10's `StepsFamily` from operator data**: at every counterexample, `DegreeOps` for every
degree class, `VarStepsAt` for every variance class, and the remainders. -/
theorem stepsFamily_of_ops (Θ : ℕ → Type) [∀ L, Fintype (Θ L)] (Z : ∀ L, Finset ℤ → Θ L → ℝ)
    (wc : ∀ L, cd.ι L → Θ L → ℝ) (ρ : ∀ L, Choice (D.CL.T L) → ℝ) (z : ℕ → ℝ)
    (hz0 : ∀ L, 0 ≤ z L) (hz : Tendsto z atTop (𝓝 0)) (K c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) (hrr0 : ∀ L A ω, 0 ≤ rr L A ω)
    (H : Param.AtCounterexamples (Param.Params.ofDecay a) D.Y fun L A =>
      (∀ n : {n // n ∈ cd.N}, Nonempty (DegreeOps c (cd.clsSel L (.inl n)) (termAt (D := D) L A)
        (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A) (∑ j, wc L (.inl n) j * Z L A j)
        (D.Y L A) (z L) K)) ∧
      (∀ v : cd.V L, Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := D) L A)
        (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A) (∑ j, wc L (.inr v) j * Z L A j)
        (D.Y L A) (z L) K)) ∧
      ∑ ω ∈ cd.sel L, rr L A ω ≤ Comparison.remainder c₀ L A) :
    StepsFamily cd Θ Z wc ρ := by
  refine ⟨z, hz0, hz, K, c₀, hc₀, rr, hrr0, ?_⟩
  filter_upwards [H] with L hL
  intro C hC hind A hA hcount
  obtain ⟨hdeg, hvar, hrs⟩ := hL C hC hind A hA hcount
  refine ⟨fun i => ?_, hrs⟩
  rcases i with n | v
  · obtain ⟨Hn⟩ := hdeg n
    exact classStepsAt_inl cd c L A n _ _ _ _ _ Hn
  · obtain ⟨Hv⟩ := hvar v
    exact classStepsAt_inr cd L A v _ _ _ _ _ Hv

omit [DecidableEq P] in
/-- **`ClassEnergyData.ofSteps` from operator data**: B10's constructor with the `StepsFamily` of
`stepsFamily_of_ops` (Steps 1–2 of every degree class proved from the operator inequalities). -/
noncomputable def classEnergyData_ofOps (Θ : ℕ → Type) [∀ L, Fintype (Θ L)]
    (Z : ∀ L, Finset ℤ → Θ L → ℝ) (u : ∀ L, Θ L → ℝ) (wc : ∀ L, cd.ι L → Θ L → ℝ)
    (wc_nonneg : ∀ L i j, 0 ≤ wc L i j) (ρ : ∀ L, Choice (D.CL.T L) → ℝ) (z : ℕ → ℝ)
    (hz0 : ∀ L, 0 ≤ z L) (hz : Tendsto z atTop (𝓝 0)) (K c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) (hrr0 : ∀ L A ω, 0 ≤ rr L A ω)
    (H : Param.AtCounterexamples (Param.Params.ofDecay a) D.Y fun L A =>
      (∀ n : {n // n ∈ cd.N}, Nonempty (DegreeOps c (cd.clsSel L (.inl n)) (termAt (D := D) L A)
        (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A) (∑ j, wc L (.inl n) j * Z L A j)
        (D.Y L A) (z L) K)) ∧
      (∀ v : cd.V L, Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := D) L A)
        (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A) (∑ j, wc L (.inr v) j * Z L A j)
        (D.Y L A) (z L) K)) ∧
      ∑ ω ∈ cd.sel L, rr L A ω ≤ Comparison.remainder c₀ L A)
    (consistent : ∀ L i, ∑ j, wc L i j * u L j + ∑ ω ∈ cd.clsSel L i, ρ L ω ≤
      ∑ ω ∈ cd.clsSel L i, cd.φ L ω)
    (v : ∀ L, Θ L → ℝ) (errK : ℝ)
    (errw : ∀ L i, ∑ j, wc L i j * v L j ≤ errK * ∑ ω ∈ cd.clsSel L i, monomial (D.CL.π L) ω)
    (upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
      ∃ r : ∀ L, Finset ℤ → Θ L → ℝ, (∀ L A j, 0 ≤ r L A j) ∧
      Param.AtCounterexamples (Param.Params.ofDecay a) D.Y (fun L A =>
        ∀ j, Z L A j ≤ (u L j + ε₃ L * v L j) * D.Y L A + r L A j) ∧
      Param.AtCounterexamples (Param.Params.ofDecay a) D.Y (fun L A =>
        ∑ j, (∑ i, wc L i j) * r L A j ≤ Comparison.remainder c₃ L A)) :
    ClassEnergyData D cd :=
  ClassEnergyData.ofSteps cd Θ Z u wc wc_nonneg ρ
    (stepsFamily_of_ops cd c Θ Z wc ρ z hz0 hz K c₀ hc₀ rr hrr0 H) consistent v errK errw upper

end Family

end Sarkozy.EnvelopeSteps
