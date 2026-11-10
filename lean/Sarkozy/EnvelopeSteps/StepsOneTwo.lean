module

public import Sarkozy.EnvelopeSteps.JointEnergy
public import Sarkozy.ClassInputsPaper.Steps

@[expose] public section

/-!
# Steps 1 and 2 of `thm:envelopes`(i) from operator inequalities

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 1 (remainders) and Step 2
(domination); (P5) and (E1) of `paper/sections/10_comparison_lemmas.tex`.

B10's `ClassInputsPaper.EnvStepsAt` takes Steps 1 and 2 as inequalities between real numbers:
`|Rem_ω| ≤ υ_ω (B + z) C_X Y + r₁` and `|Lead_ω| ≤ YN_ω`. In the paper:

* Step 1: `Υ_ω` is self-adjoint with `‖Υ_ω‖ ≤ υ_ω`, so `υ_ω Diag_ω ± [Υ_ω]_ω ⪰_ι 0`, and (P5),
  (E1) give `|Y_{[Υ_ω]_ω ⊗ λ_{-X}}| ≤ υ_ω Y^Ñ[Diag_ω] ≤ υ_ω (B + o(1)) C_X Y`;
* Step 2: `±L_ω ⪯ D_ω` (`lem:oct24:mask-schur`(a)), so `[D_ω]_ω ± [L_ω]_ω ⪰_ι 0`, and (P5) gives
  `|Y_{[L_ω]_ω ⊗ λ_{-X}}| ≤ Y^Ñ[[D_ω]_ω]`.

This file proves both from the placement map (`Placement.lean`), for any two energy functionals
`Elam` (`λ` outside `X`) and `EN` (`Ñ` outside `X`), linear in the law, with (P5): `κ ± ζ ⪰_c 0`
gives `|Elam ζ| ≤ EN κ` (for the joint energies of `PaperEnergy.lean` this is `jointEnergy_P5`, from
the brackets `(Ñ_𝔅 λ_𝔅; λ_𝔅 Ñ_𝔅) ⪰ 0` of (CP3)):

* **`abs_le_of_dom`** (Step 2): `±L ⪯ D` in `L²(m)` gives `|Elam[L]_ω| ≤ EN[D]_ω`;
* **`abs_le_of_norm`** (Step 1): `|⟨f, Υ f⟩_m| ≤ υ ⟨f, f⟩_m` for a symmetric `Υ` gives
  `|Elam[Υ]_ω| ≤ υ EN[Diag_ι(φ_* m)]`;
* **`envStepsOfOperators`**: B10's `EnvStepsAt` with `Lead_ω = Elam_ω[L_ω]_ω`,
  `Rem_ω = Elam_ω[Υ_ω]_ω`, `YN_ω = EN_ω[D_ω]_ω` and the fields `step1`, `step2` **proved** from
  the operator inequalities, (P5) and (E1) for the diagonal `Diag_ω`;
* **`step3_of_couplings`** (Step 3, the coupling expansion of `lem:orbit-coupon`(i), without the
  orbit improvement): `D = ∑ c(C) C` and per-coupling errors give
  `Y^Ñ[[D]] ≤ Y^{Ñ₀}[[D]] + M(D) e + ∑ |c(C)| r_C`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

open Sarkozy.RecordExpansion

variable {O : Type*} [Fintype O] [DecidableEq O]
  {V X : Type*} [Fintype V] [DecidableEq V]

/-- **(P5) of the energy toolkit** (`paper/sections/10_comparison_lemmas.tex`, `it:record:P5`,
"± tensorization") as a property of two energy functionals, `Elam = Y_{· ⊗ λ_{-X}}` and
`EN = Y^Ñ[·] = Y_{· ⊗ Ñ_{-X}}`: if `κ ± ζ ⪰_c 0`, then `|Elam ζ| ≤ EN κ`. -/
def P5 (c : ReflectionCut V) (Elam EN : (((V → X) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ κ ζ, c.Positive (κ + ζ) → c.Positive (κ - ζ) → |Elam ζ| ≤ EN κ

/-- **Step 2 of `thm:envelopes`** (domination): if `L ⪯ D` and `-L ⪯ D` in `L²(m)`, then
`|Y_{[L]_ω ⊗ λ_{-X}}| ≤ Y^Ñ[[D]_ω]` for energy functionals with (P5). -/
theorem abs_le_of_dom (c : ReflectionCut V) {Elam EN : (((V → X) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ}
    (hE : P5 c Elam EN) {m : O → ℝ} (φ : O → (c.Half → X)) {L D : (O → ℝ) →ₗ[ℝ] (O → ℝ)}
    (h₁ : OpLE m L D) (h₂ : OpLE m (-L) D) :
    |Elam (place c m φ L)| ≤ EN (place c m φ D) := by
  have hp : c.Positive (place c m φ D + place c m φ L) := by
    have h := place_positive c φ h₂
    rw [place_sub, ← neg_one_smul ℝ L, place_smul,
      neg_one_smul ℝ (place c m φ L), sub_neg_eq_add] at h
    exact h
  have hm : c.Positive (place c m φ D - place c m φ L) := by
    have h := place_positive c φ h₁
    rwa [place_sub] at h
  exact hE _ _ hp hm

omit [DecidableEq O] in
/-- A symmetric operator with `|⟨f, Υ f⟩_m| ≤ υ ⟨f, f⟩_m` lies between `±υ I`. -/
theorem opLE_of_form_bound {m : O → ℝ} {Υ : (O → ℝ) →ₗ[ℝ] (O → ℝ)} {υ : ℝ}
    (hsym : ∀ f g, ip m f (Υ g) = ip m g (Υ f)) (hb : ∀ f, |ip m f (Υ f)| ≤ υ * ip m f f) :
    OpLE m Υ (υ • LinearMap.id) ∧ OpLE m (-Υ) (υ • LinearMap.id) := by
  have hid : ∀ f g, ip m f g = ip m g f := fun f g => by
    unfold ip; exact sum_congr rfl fun x _ => by ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro f g
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, ip_sub_right,
      ip_smul_right, hsym f g, hid f g]
  · intro f
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, ip_sub_right,
      ip_smul_right]
    linarith [(abs_le.mp (hb f)).2]
  · intro f g
    simp only [sub_neg_eq_add, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      ip_add_right, ip_smul_right, hsym f g, hid f g]
  · intro f
    simp only [sub_neg_eq_add, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      ip_add_right, ip_smul_right]
    linarith [(abs_le.mp (hb f)).1]

variable [Fintype X] [DecidableEq X]

/-- **Step 1 of `thm:envelopes`** (remainders): a symmetric `Υ` with
`|⟨f, Υ f⟩_m| ≤ υ ‖f‖²_m` (`‖Υ‖ ≤ υ`, `eq:oct24:star-tensor-error`) has
`|Y_{[Υ]_ω ⊗ λ_{-X}}| ≤ υ Y^Ñ[Diag_ι(φ_* m)]` for energy functionals with (P5). -/
theorem abs_le_of_norm (c : ReflectionCut V) {Elam EN : (((V → X) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ}
    (hE : P5 c Elam EN) {m : O → ℝ} (φ : O → (c.Half → X)) {Υ : (O → ℝ) →ₗ[ℝ] (O → ℝ)} {υ : ℝ}
    (hsym : ∀ f g, ip m f (Υ g) = ip m g (Υ f)) (hb : ∀ f, |ip m f (Υ f)| ≤ υ * ip m f f) :
    |Elam (place c m φ Υ)| ≤ υ * EN (c.diagonalLaw (push m φ)) := by
  obtain ⟨h₁, h₂⟩ := opLE_of_form_bound hsym hb
  have h := abs_le_of_dom c hE φ h₁ h₂
  rwa [place_smul, place_id, map_smul, smul_eq_mul] at h

open Sarkozy.ClassInputsPaper

/-- **B10's `EnvStepsAt` with Steps 1 and 2 proved from operator inequalities**
(`thm:envelopes`(i), Steps 1–2). Per selection `ω` of the class: objects `Obj ω` with the half
marginal `m ω ≥ 0`, the placement `φ ω`, the energy functionals `Elam ω`, `EN ω` with (P5), the
operators `L_ω` (leading star tensor), `Υ_ω` (remainder) and `D_ω` (envelope) on `L²(m_ω)`, and

* `hdom`: `±L_ω ⪯ D_ω` (the conclusion of `lem:oct24:mask-schur`(a) in the chart of `ω`);
* `hΥ`: `Υ_ω` symmetric with `|⟨f, Υ_ω f⟩| ≤ υ_ω ‖f‖²` (`eq:oct24:star-tensor-error`);
* `hE1`: (E1) for the diagonal, `EN_ω[Diag_ω] ≤ (B + z) C_X Y + r₁'_ω`, with `υ_ω ≥ 0`;
* `hI`: (N4), `I_ω = π̃_ω (Elam_ω[L_ω]_ω + Elam_ω[Υ_ω]_ω)`.

Then `Lead_ω = Elam_ω[L_ω]_ω`, `Rem_ω = Elam_ω[Υ_ω]_ω`, `YN_ω = EN_ω[D_ω]_ω`, `r₁ = υ r₁'`, and
`step1`, `step2` are proved (`abs_le_of_norm`, `abs_le_of_dom`). Steps 3–4 and the evaluations
are passed through. -/
noncomputable def envStepsOfOperators {Ω : Type*} (𝒞 : Finset Ω) (I π ρ rr : Ω → ℝ)
    {WZ Y z K : ℝ} {V : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)
    (Obj : Ω → Type*) [∀ ω, Fintype (Obj ω)] [∀ ω, DecidableEq (Obj ω)]
    (Lab : Ω → Type*) [∀ ω, Fintype (Lab ω)] [∀ ω, DecidableEq (Lab ω)]
    (Elam EN : ∀ ω, (((V → Lab ω) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ) (hE : ∀ ω ∈ 𝒞, P5 c (Elam ω) (EN ω))
    (m : ∀ ω, Obj ω → ℝ) (φ : ∀ ω, Obj ω → (c.Half → Lab ω))
    (Lop Υop Dop : ∀ ω, (Obj ω → ℝ) →ₗ[ℝ] (Obj ω → ℝ))
    (hdom : ∀ ω ∈ 𝒞, OpLE (m ω) (Lop ω) (Dop ω) ∧ OpLE (m ω) (-Lop ω) (Dop ω))
    (υ : Ω → ℝ) (hυ : ∀ ω ∈ 𝒞, 0 ≤ υ ω)
    (hΥsym : ∀ ω ∈ 𝒞, ∀ f g, ip (m ω) f (Υop ω g) = ip (m ω) g (Υop ω f))
    (hΥ : ∀ ω ∈ 𝒞, ∀ f, |ip (m ω) f (Υop ω f)| ≤ υ ω * ip (m ω) f f)
    (B : ℝ) (CX r₁' : Ω → ℝ)
    (hE1 : ∀ ω ∈ 𝒞, EN ω (c.diagonalLaw (push (m ω) (φ ω))) ≤ (B + z) * CX ω * Y + r₁' ω)
    (wt : Ω → ℝ) (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω)
    (hI : ∀ ω ∈ 𝒞, I ω = wt ω * (Elam ω (place c (m ω) (φ ω) (Lop ω)) +
      Elam ω (place c (m ω) (φ ω) (Υop ω))))
    (YN0 Mω Mh r₃ : Ω → ℝ) (r₄ M Minv Rerr tU tδ : ℝ) (hR : 0 ≤ Rerr) (htδ : 0 ≤ tδ)
    (step3 : ∀ ω ∈ 𝒞, EN ω (place c (m ω) (φ ω) (Dop ω)) ≤
      YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX ω * Y + r₃ ω)
    (step4 : ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤ WZ + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y + r₄)
    (hM : ∑ ω ∈ 𝒞, wt ω * CX ω * Mω ω ≤ M * ∑ ω ∈ 𝒞, wt ω * CX ω)
    (hMinv : Minv * ∑ ω ∈ 𝒞, wt ω * CX ω ≤ ∑ ω ∈ 𝒞, wt ω * CX ω * Mh ω)
    (hρ : (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, wt ω * CX ω) +
      B * (∑ ω ∈ 𝒞, wt ω * υ ω * CX ω) ≤ ∑ ω ∈ 𝒞, ρ ω)
    (hπ : ∀ ω ∈ 𝒞, wt ω * (2 + υ ω) * CX ω ≤ K * π ω)
    (hrr : ∑ ω ∈ 𝒞, wt ω * (υ ω * r₁' ω + r₃ ω) + r₄ ≤ ∑ ω ∈ 𝒞, rr ω) :
    EnvStepsAt 𝒞 I π ρ rr WZ Y z K where
  Lead ω := Elam ω (place c (m ω) (φ ω) (Lop ω))
  Rem ω := Elam ω (place c (m ω) (φ ω) (Υop ω))
  YN ω := EN ω (place c (m ω) (φ ω) (Dop ω))
  YN0 := YN0
  υ := υ
  Mω := Mω
  Mh := Mh
  wt := wt
  CX := CX
  r₁ ω := υ ω * r₁' ω
  r₃ := r₃
  r₄ := r₄
  B := B
  M := M
  Minv := Minv
  Rerr := Rerr
  tU := tU
  tδ := tδ
  hwt := hwt
  hR := hR
  htδ := htδ
  hI := hI
  step1 ω hω := by
    have h := abs_le_of_norm c (hE ω hω) (φ ω) (hΥsym ω hω) (hΥ ω hω)
    have h2 := mul_le_mul_of_nonneg_left (hE1 ω hω) (hυ ω hω)
    calc |Elam ω (place c (m ω) (φ ω) (Υop ω))|
        ≤ υ ω * EN ω (c.diagonalLaw (push (m ω) (φ ω))) := h
      _ ≤ υ ω * ((B + z) * CX ω * Y + r₁' ω) := h2
      _ = υ ω * (B + z) * CX ω * Y + υ ω * r₁' ω := by ring
  step2 ω hω := abs_le_of_dom c (hE ω hω) (φ ω) (hdom ω hω).1 (hdom ω hω).2
  step3 := step3
  step4 := step4
  hM := hM
  hMinv := hMinv
  hρ := hρ
  hπ := hπ
  hrr := hrr

/-! ## Step 3: the coupling expansion -/

section Step3

variable {O : Type*} [Fintype O] [DecidableEq O] {V X : Type*} [Fintype V] [DecidableEq V]

/-- The placement as a linear map in the operator. -/
noncomputable def placeL (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X)) :
    ((O → ℝ) →ₗ[ℝ] (O → ℝ)) →ₗ[ℝ] (((V → X) → ℝ) →ₗ[ℝ] ℝ) where
  toFun := place c m φ
  map_add' := place_add c m φ
  map_smul' a K := place_smul c m φ a K

/-- **Step 3 of `thm:envelopes`, the coupling expansion** (`lem:orbit-coupon`(i) at the placements,
without the orbit improvement): if `D = ∑_C c(C) C` and every placed coupling has
`|Y^Ñ[[C]] − Y^{Ñ₀}[[C]]| ≤ e + r_C` (`e = R_err C_X Y`, from (E1) for the admissible probability
measures `[C]_ω`), then `Y^Ñ[[D]] ≤ Y^{Ñ₀}[[D]] + M(D) e + ∑ |c(C)| r_C` with the coupling mass
`M(D) = ∑ |c(C)|`. -/
theorem step3_of_couplings (c : ReflectionCut V) (EN EN0 : (((V → X) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (m : O → ℝ) (φ : O → (c.Half → X)) {ι : Type*} (s : Finset ι) (coef : ι → ℝ)
    (Cop : ι → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (Dop : (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hD : Dop = ∑ i ∈ s, coef i • Cop i) (e : ℝ) (r : ι → ℝ)
    (herr : ∀ i ∈ s, |EN (place c m φ (Cop i)) - EN0 (place c m φ (Cop i))| ≤ e + r i) :
    EN (place c m φ Dop) ≤ EN0 (place c m φ Dop) + (∑ i ∈ s, |coef i|) * e +
      ∑ i ∈ s, |coef i| * r i := by
  have hpl : place c m φ Dop = ∑ i ∈ s, coef i • place c m φ (Cop i) := by
    change placeL c m φ Dop = _
    rw [hD, map_sum]
    exact sum_congr rfl fun i _ => map_smul _ _ _
  rw [hpl, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  have key : ∀ i ∈ s, coef i * EN (place c m φ (Cop i)) ≤
      coef i * EN0 (place c m φ (Cop i)) + |coef i| * e + |coef i| * r i := by
    intro i hi
    have h1 := herr i hi
    have h2 : coef i * (EN (place c m φ (Cop i)) - EN0 (place c m φ (Cop i))) ≤
        |coef i| * (e + r i) := by
      calc coef i * (EN (place c m φ (Cop i)) - EN0 (place c m φ (Cop i)))
          ≤ |coef i * (EN (place c m φ (Cop i)) - EN0 (place c m φ (Cop i)))| := le_abs_self _
        _ = |coef i| * |EN (place c m φ (Cop i)) - EN0 (place c m φ (Cop i))| := abs_mul _ _
        _ ≤ |coef i| * (e + r i) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    nlinarith
  have hs := sum_le_sum key
  simp only [sum_add_distrib, ← sum_mul] at hs
  linarith

end Step3

end Sarkozy.EnvelopeSteps
