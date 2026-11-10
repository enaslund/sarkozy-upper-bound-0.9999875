module

public import Sarkozy.SpectralD.CxRealization

@[expose] public section

/-!
# `cor:spec2:coupling` in the complex realization: `hTF` and the Step-2 vector

`paper/sections/14_spectral.tex`, `cor:spec2:coupling`, Steps 1 and 2. Fork B's
`PaleyB.coupling_block_concrete` proves `eq:spec:coupling` in an abstract complex Hilbert space,
with two inputs left: the realization `hTF` (`‖Op F_V‖² = ∑_x μ(x)|Op F_V(x)|²`) and the Step-2
vector `v ∈ 𝒱` with `v̂(ξ) = 𝐐(ξ)ĝ(ξ)`, `⟪v, Op F_V⟫ = ∑_ξ|𝐐ĝ|²`,
`‖v‖² ≤ (1 + ε_V)∑_ξ|𝐐ĝ|²`. In the complex realization of `CxRealization`
(`T = kernelOpC μ k`, `𝒱 = degSpace μ`) and for the cut law `Λ(x, x') = μ(x)μ(x')k(x, x')`
(`cutLaw`):

* `inner_l2MapC_kernelOpC`: `⟪l2MapC f, T l2MapC g⟫ = E_Λ[f̄(x) g(x')]` (`lem:spec:cutkernel`(b),
  complex form);
* `hTF_degMap`: `hTF`, with `Op F_V = opFun μ k F_V`;
* `stepTwoVec`, `stepTwo_mem`, `stepTwo_inner`, `stepTwo_norm`: the Step-2 vector and its three
  properties (`lem:spec:degone`(a) via WP-K's `degone_bilinear`, (c) via `coupling_hvnorm`);
* `opFun_degFun_eq`: instance (A), `Op F_V = ϱ · 𝒫F_V` with `ϱ = Op 1` (`rhoK`) and the
  conditional laws `P_k(a | x)` of `x'_k` given `x` under `Λ` (`condP`);
* `coupling_block_cx`: `eq:spec:coupling` in the complex realization, with `hTF` and the Step-2
  inputs discharged.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The cut law `Λ(x, x') = μ(x) μ(x') k(x, x')` of the kernel `k` relative to `μ ⊗ μ`. -/
noncomputable def cutLaw (μ : (U → ZMod p) → ℝ) (k : (U → ZMod p) → (U → ZMod p) → ℝ)
    (z : (U → ZMod p) × (U → ZMod p)) : ℝ :=
  μ z.1 * μ z.2 * k z.1 z.2

/-- `⟪l2MapC f, T (l2MapC g)⟫ = E_Λ[f̄(x) g(x')]`. -/
theorem inner_l2MapC_kernelOpC (μ : (U → ZMod p) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ) (f g : (U → ZMod p) → ℂ) :
    ⟪l2MapC μ f, kernelOpC μ k (l2MapC μ g)⟫_ℂ =
      ∑ z, (cutLaw μ k z : ℂ) * (conj (f z.1) * g z.2) := by
  rw [kernelOpC_l2MapC μ hμ, inner_l2MapC μ hμ, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  unfold opFun cutLaw
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun x' _ => ?_
  push_cast
  ring

/-- **`hTF` of `coupling_block_concrete`**: `‖T F_V‖² = ∑_x μ(x) |Op F_V(x)|²`. -/
theorem hTF_degMap (μ : (U → ZMod p) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ) (g : U → ZMod p → ℂ) :
    ‖kernelOpC μ k (degMap μ g)‖ ^ 2 = ∑ x, μ x * ‖opFun μ k (degFun g) x‖ ^ 2 := by
  rw [degMap_apply, kernelOpC_l2MapC μ hμ, norm_l2MapC_sq μ hμ]

/-! ## The Step-2 vector -/

/-- The Step-2 functions `h_l = ∑_ξ (𝐐(ξ)ĝ(ξ))_l e_ξ`, so that `ĥ(ξ) = 𝐐(ξ)ĝ(ξ)`. -/
noncomputable def stepTwoFun (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (g : U → ZMod p → ℂ) :
    U → ZMod p → ℂ :=
  fun l a => ∑ ξ, mulV (degoneQ Λ ξ) (fun m => fcoef (g m) ξ) l * ech ξ a

theorem fcoef_stepTwoFun (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (g : U → ZMod p → ℂ) (l : U)
    (ξ : ZMod p) :
    fcoef (stepTwoFun Λ g l) ξ = mulV (degoneQ Λ ξ) (fun m => fcoef (g m) ξ) l :=
  fcoef_trig (fun η => mulV (degoneQ Λ η) (fun m => fcoef (g m) η) l) ξ

lemma mulV_ghat_zero (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) {g : U → ZMod p → ℂ}
    (hg : ∀ k, ∑ a, g k a = 0) (l : U) :
    mulV (degoneQ Λ 0) (fun m => fcoef (g m) (0 : ZMod p)) l = 0 := by
  unfold mulV
  refine sum_eq_zero fun m _ => ?_
  show degoneQ Λ 0 l m * fcoef (g m) 0 = 0
  rw [fcoef_zero, hg m, mul_zero, mul_zero]

theorem stepTwoFun_mean (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) {g : U → ZMod p → ℂ}
    (hg : ∀ k, ∑ a, g k a = 0) (l : U) : ∑ a, stepTwoFun Λ g l a = 0 := by
  unfold stepTwoFun
  rw [sum_comm]
  have h : ∀ ξ : ZMod p, ∑ a, mulV (degoneQ Λ ξ) (fun m => fcoef (g m) ξ) l * ech ξ a =
      mulV (degoneQ Λ ξ) (fun m => fcoef (g m) ξ) l * (if ξ = 0 then (p : ℂ) else 0) := by
    intro ξ; rw [← mul_sum, sum_ech]
  rw [sum_congr rfl fun ξ _ => h ξ]
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [mulV_ghat_zero Λ hg l, zero_mul]

/-- **The Step-2 vector** `v = l2MapC(∑_l h_l(x_l))`, `ĥ(ξ) = 𝐐(ξ)ĝ(ξ)`. -/
noncomputable def stepTwoVec (μ : (U → ZMod p) → ℝ) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (g : U → ZMod p → ℂ) : EuclideanSpace ℂ (U → ZMod p) :=
  degMap μ (stepTwoFun Λ g)

/-- **`hv`**: the Step-2 vector lies in `𝒱`. -/
theorem stepTwo_mem (μ : (U → ZMod p) → ℝ) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    {g : U → ZMod p → ℂ} (hg : ∀ k, ∑ a, g k a = 0) :
    stepTwoVec μ Λ g ∈ degSpace μ :=
  degMap_mem μ (stepTwoFun_mean Λ hg)

/-- **`hvT`**: `⟪v, T F_V⟫ = ∑_{ξ ≠ 0} |𝐐(ξ)ĝ(ξ)|²` (`lem:spec:degone`(a)). -/
theorem stepTwo_inner (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ) (hΛ1 : ∑ z, cutLaw μ k z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ k (affLab s c z.1, affLab s c z.2) = cutLaw μ k z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (a b : U), cutLaw μ k z ≠ 0 → z.1 a ≠ z.2 b)
    {g : U → ZMod p → ℂ} (hg : ∀ k, ∑ a, g k a = 0) :
    ⟪stepTwoVec μ (cutLaw μ k) g, kernelOpC μ k (degMap μ g)⟫_ℂ =
      ((∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        Sarkozy.Spectral.sqn ((degoneQ (cutLaw μ k) ξ : Matrix U U ℂ) *ᵥ
          (fun m => fcoef (g m) ξ)) : ℝ) : ℂ) := by
  simp only [mulVec_eq_mulV]
  unfold stepTwoVec
  rw [degMap_apply, degMap_apply, inner_l2MapC_kernelOpC μ hμ k]
  unfold degFun
  rw [degone_bilinear hp2 (cutLaw μ k) hΛ1 hΛinv hΛinj _ g
    (stepTwoFun_mean (cutLaw μ k) hg) hg]
  push_cast
  refine sum_congr rfl fun ξ _ => ?_
  unfold Sarkozy.Spectral.sqn
  push_cast
  refine sum_congr rfl fun l _ => ?_
  rw [fcoef_stepTwoFun]
  have e : ∀ A : ℂ, ∑ m, A * degoneQ (cutLaw μ k) ξ l m * fcoef (g m) ξ =
      A * mulV (degoneQ (cutLaw μ k) ξ) (fun m => fcoef (g m) ξ) l := by
    intro A
    unfold mulV
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  rw [e, Complex.conj_mul']

/-- **`hvnorm`**: `‖v‖² ≤ (1 + ε_V) ∑_{ξ ≠ 0} |𝐐(ξ)ĝ(ξ)|²` (`lem:spec:degone`(c)). -/
theorem stepTwo_norm (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {εV : ℝ} (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV)
    (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) {g : U → ZMod p → ℂ} (hg : ∀ k, ∑ a, g k a = 0) :
    ‖stepTwoVec μ Λ g‖ ^ 2 ≤ (1 + εV) * ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
      Sarkozy.Spectral.sqn ((degoneQ Λ ξ : Matrix U U ℂ) *ᵥ (fun m => fcoef (g m) ξ)) := by
  simp only [mulVec_eq_mulV]
  set c : ZMod p → U → ℂ := fun ξ => mulV (degoneQ Λ ξ) (fun m => fcoef (g m) ξ) with hc
  have hc0 : ∀ l, c 0 l = 0 := fun l => mulV_ghat_zero Λ hg l
  have h := coupling_hvnorm hp2 μ hμ1 hinv hinj hN c hc0
  have hv : ‖stepTwoVec μ Λ g‖ ^ 2 = ∑ x, μ x * ‖∑ ξ, ∑ l, c ξ l * ech ξ (x l)‖ ^ 2 := by
    unfold stepTwoVec
    rw [degMap_apply, norm_l2MapC_sq μ hμ0]
    refine sum_congr rfl fun x _ => ?_
    congr 2
    unfold degFun stepTwoFun
    rw [sum_comm]
  rw [hv]
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [← sum_filter_add_sum_filter_not univ (fun ξ : ZMod p => ξ ≠ 0)]
  have hz : ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ¬ ξ ≠ 0), Sarkozy.Spectral.sqn (c ξ) = 0 := by
    refine sum_eq_zero fun ξ hξ => ?_
    have : ξ = 0 := by simpa using hξ
    subst this
    unfold Sarkozy.Spectral.sqn
    simp [hc0]
  rw [hz, add_zero]

/-! ## Instance (A): `Op F_V = ϱ · 𝒫F_V` -/

/-- `ϱ(x) = (Op 1)(x) = ∑_{x'} μ(x') k(x, x')`. -/
noncomputable def rhoK (μ : (U → ZMod p) → ℝ) (k : (U → ZMod p) → (U → ZMod p) → ℝ)
    (x : U → ZMod p) : ℝ :=
  ∑ x', μ x' * k x x'

/-- The conditional law `P_i(a | x)` of `x'_i` given `x` under `Λ`. -/
noncomputable def condP (μ : (U → ZMod p) → ℝ) (k : (U → ZMod p) → (U → ZMod p) → ℝ) (i : U)
    (x : U → ZMod p) (a : ZMod p) : ℝ :=
  (∑ x', if x' i = a then μ x' * k x x' else 0) / rhoK μ k x

/-- **Instance (A) of `def:coupling-data`**: `Op F_V(x) = ϱ(x) 𝒫F_V(x)`, with `𝒫F_V(x) =
∑_i ∑_a P_i(a | x) g_i(a)` (`condField`), for a nonnegative kernel. -/
theorem opFun_degFun_eq (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ) (hk0 : ∀ x x', 0 ≤ k x x') (g : U → ZMod p → ℂ)
    (x : U → ZMod p) :
    opFun μ k (degFun g) x = (rhoK μ k x : ℂ) * condField (condP μ k) g x := by
  by_cases hρ : rhoK μ k x = 0
  · have h0 : ∀ x', μ x' * k x x' = 0 := by
      intro x'
      have hnn : ∀ y ∈ (univ : Finset (U → ZMod p)), 0 ≤ μ y * k x y :=
        fun y _ => mul_nonneg (hμ0 y) (hk0 x y)
      exact (sum_eq_zero_iff_of_nonneg hnn).mp hρ x' (mem_univ _)
    rw [hρ]
    unfold opFun
    simp only [Complex.ofReal_zero, zero_mul]
    refine sum_eq_zero fun x' _ => ?_
    have : (μ x' : ℂ) * (k x x' : ℂ) = 0 := by exact_mod_cast h0 x'
    rw [this, zero_mul]
  · have hR : ∀ i a, ((condP μ k i x a : ℝ) : ℂ) * (rhoK μ k x : ℂ) =
        ((∑ x', if x' i = a then μ x' * k x x' else 0 : ℝ) : ℂ) := by
      intro i a
      unfold condP
      rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hρ]
    calc opFun μ k (degFun g) x
        = ∑ i, ∑ x', ((μ x' * k x x' : ℝ) : ℂ) * g i (x' i) := by
          unfold opFun degFun
          simp only [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun i _ => sum_congr rfl fun x' _ => by push_cast; ring
      _ = ∑ i, ∑ a, ((∑ x', if x' i = a then μ x' * k x x' else 0 : ℝ) : ℂ) * g i a := by
          refine sum_congr rfl fun i _ => ?_
          simp only [Complex.ofReal_sum, sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun x' _ => ?_
          rw [sum_eq_single (x' i)]
          · simp only [↓reduceIte]
          · intro b _ hb
            have hne : ¬ (x' i = b) := Ne.symm hb
            simp only [hne, ↓reduceIte, Complex.ofReal_zero, zero_mul]
          · intro h; exact absurd (mem_univ _) h
      _ = (rhoK μ k x : ℂ) * condField (condP μ k) g x := by
          unfold condField
          rw [mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun a _ => ?_
          rw [← hR i a]
          ring

/-! ## `eq:spec:coupling` in the complex realization -/

/-- The form `qX ξ x = x^*𝐇⁺x − |𝐀₀(ξ)x|²` of `RouteAInputs.coupling`. -/
noncomputable def qXcx (Adj : U → U → Prop) [DecidableRel Adj] (N : U → Finset U)
    (ς : U → U → ZMod p) (ξ : ZMod p) (x : U → ℂ) : ℝ :=
  Sarkozy.Spectral.qform (PaleyB.hplusM Adj N ς : Matrix U U ℂ) x x -
    Sarkozy.Spectral.sqn ((azero ς ξ : Matrix U U ℂ) *ᵥ x)

/-- `η_B` of `eq:spec:etaB`. -/
noncomputable def etaBcx (p : ℕ) (R Λp εH θ ρ ΓE lamH ζ Λnc εV ΛD η : ℝ) : ℝ :=
  (R * p / ((p : ℝ) - 1) - 1) * Λp +
    R * p / ((p : ℝ) - 1) * (εH + rp p * θ * ρ + (2 * Real.sqrt (ΓE * (lamH + εH)) + ΓE) +
      (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc) + εV * ΛD ^ 2 + 2 * ΛD * η

/-- The conclusion of `cor:spec2:coupling` for every degree-one `F_V` of the complex
realization: `‖(I − Π_𝒱)T F_V‖² ≤ r²∑_{ξ≠0}(qX ξ ĝ(ξ) + η_B|ĝ(ξ)|²)`. -/
def CouplingBoundCx (μ : (U → ZMod p) → ℝ) (k : (U → ZMod p) → (U → ZMod p) → ℝ)
    (qX : ZMod p → (U → ℂ) → ℝ) (ηB : ℝ) : Prop :=
  ∀ g : U → ZMod p → ℂ, (∀ l, ∑ a, g l a = 0) →
    ‖kernelOpC μ k (degMap μ g) -
        (degSpace μ).starProjection (kernelOpC μ k (degMap μ g))‖ ^ 2 ≤
      rp p ^ 2 * ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        (qX ξ (fun l => fcoef (g l) ξ) + ηB * Sarkozy.Spectral.sqn (fun l => fcoef (g l) ξ))

/-- **`cor:spec2:coupling`, `eq:spec:coupling`, in the complex realization**: fork B's
`coupling_block_concrete` with `T = kernelOpC μ k`, `𝒱 = degSpace μ`, `F = l2MapC F_V`, the
realization `hTF` (`hTF_degMap`) and the Step-2 vector (`stepTwoVec`: `stepTwo_mem`,
`stepTwo_inner`, `stepTwo_norm`) discharged, for every mean-zero `g`. The remaining hypotheses
are those of `coupling_block_concrete` on the coupling data `D` of instance (A) (with
`hA : Op F_V = ϱ · 𝒫F_V`, see `opFun_degFun_eq`), the cut law (`degone_bilinear`) and the
certified numbers. -/
theorem couplingBound_cx (Adj : U → U → Prop) [DecidableRel Adj] (hp2 : p ≠ 2)
    (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ) (hΛ1 : ∑ z, cutLaw μ k z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ k (affLab s c z.1, affLab s c z.2) = cutLaw μ k z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (a b : U), cutLaw μ k z ≠ 0 → z.1 a ≠ z.2 b)
    {N : U → Finset U} {ς : U → U → ZMod p} {Iplus : Finset (U → ZMod p)}
    (D : CouplingData p U N ς Iplus μ) (ϱ : (U → ZMod p) → ℝ) (hϱ0 : ∀ x, 0 ≤ ϱ x) {R : ℝ}
    (hR : ∀ x, ϱ x ≤ R) (hνϱ : ∀ x, D.ν x = μ x * ϱ x)
    (hA : ∀ g : U → ZMod p → ℂ, (∀ l, ∑ a, g l a = 0) →
      ∀ x, opFun μ k (degFun g) x = (ϱ x : ℂ) * condField D.P g x)
    {ΓE lamH εH : ℝ} (hΓ0 : 0 ≤ ΓE) (hΛ0 : 0 ≤ lamH + εH)
    (hΓ : ∀ w : U → ℂ, ∑ x, D.ν x * l2sq (fun a => ∑ l, w l *
      ((p : ℂ) * (D.P l x a : ℂ) - starProd N ς l x a)) ≤ ΓE * ∑ l, ‖w l‖ ^ 2)
    (Dj : U → ℝ) (hpiv : ∀ j x t, D.ν x ≠ 0 → condLaw D.ν j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ l, ((2 : ℝ) ^ (N l).card - 1) * ∑ l', ((2 : ℝ) ^ (N l').card - 1) ≤ ρ)
    {ζ Λnc Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset U, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ D.ν J‖ ≤ ζ * rp p)
    (hHt : ∀ w : U → ℂ, (qform (gramΓ D.ν (psiField D.P)) w).re ≤
      (qform (PaleyB.modelHC N ς) w).re + εH * ∑ l, ‖w l‖ ^ 2)
    (hlam : ∀ w : U → ℂ, (qform (PaleyB.modelHC N ς) w).re ≤ lamH * ∑ l, ‖w l‖ ^ 2)
    (hnc : ∀ w : U → ℂ, PaleyB.hncQ Adj N ς w ≤ Λnc * ∑ l, ‖w l‖ ^ 2)
    (hplus : ∀ w : U → ℂ, (qform (PaleyB.modelHC N ς) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj N ς w ≤ Λp * ∑ l, ‖w l‖ ^ 2)
    {ΛD η εV : ℝ} (hΛD : 0 ≤ ΛD) (hη : 0 ≤ η) (hDE : NormLe (deltaE ς) ΛD)
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (errQ (cutLaw μ k) ς ξ) η)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV) (hεV : 0 ≤ εV) :
    CouplingBoundCx μ k (qXcx Adj N ς)
      (etaBcx p R Λp εH θ ρ ΓE lamH ζ Λnc εV ΛD η) := by
  intro g hg
  have h := PaleyB.coupling_block_concrete Adj (kernelOpC μ k) (degSpace μ) (degMap μ g) D hp2
    hμ0 hμ1 ϱ hϱ0 hR hνϱ g hg (opFun μ k (degFun g)) (hA g hg) (hTF_degMap μ hμ0 k g)
    hΓ0 hΛ0 hΓ Dj hpiv hθ0 hθ hρ hζ0 hζ hHt hlam hnc hplus (cutLaw μ k) hΛD hη hDE hE
    (stepTwoVec μ (cutLaw μ k) g) (stepTwo_mem μ (cutLaw μ k) hg)
    (stepTwo_inner hp2 μ hμ0 k hΛ1 hΛinv hΛinj hg)
    (stepTwo_norm hp2 μ hμ0 hμ1 hinv hinj hN (cutLaw μ k) hg) hεV
  exact h

end Sarkozy.SpectralD.Cx
