module

public import Sarkozy.SpectralD.CouplingBlock
public import Sarkozy.Spectral.GlueCut

@[expose] public section

/-!
# The complex realization of `L²(μ)` and the degree-one space (`lem:spec:degone`)

`paper/sections/14_spectral.tex`, Conventions and `subsec:spec:degone`: "inner products are
conjugate-linear in the first variable"; `𝒱 = ∑_k 𝒱_k` with `𝒱_k = {g(x_k) : g ∈ L²_0(𝔽_p)}`;
the Fourier coefficients `ĝ(ξ)` of `F_V = ∑_k g_k(x_k)` are complex.

WP-A's spectral criterion (`Sarkozy.Spectral.RouteAInputs`) works over any `RCLike 𝕜`; WP-A
realized the cut operator over `ℝ` (`Spectral.kernelOp`, `Spectral.cutOp` on
`EuclideanSpace ℝ Ω`, `InfluenceGlue.l2Map`). This file builds the complex realization:

* `l2MapC μ f = (√μ(x) f(x))_x ∈ EuclideanSpace ℂ Ω`, with `⟪l2MapC f, l2MapC g⟫ = E_μ f̄ g`
  (`inner_l2MapC`);
* `kernelOpC μ k`, the operator with matrix `√μ(x) k(x, x') √μ(x')`; on functions it is
  `(Op f)(x) = ∑_{x'} μ(x') k(x, x') f(x')` (`kernelOpC_l2MapC`); it is symmetric for symmetric
  real `k` (`kernelOpC_isSymmetric`);
* the embedding `embedR` of WP-A's real realization: coordinatewise `ℝ → ℂ`; it carries
  `l2Map` to `l2MapC`, `kernelOp` to `kernelOpC` and `cutOp` to `cutOpC`, and preserves inner
  products (`inner_embedR`), so every real quadratic form of WP-A's realization is the real part
  of the complex one (`re_inner_embedR_kernelOp`, `re_inner_embedR_cutOp`);
* for labellings `x : U → 𝔽_p`, the degree-one space `degSpace μ = {l2MapC(∑_k g_k(x_k)) : g_k
  mean zero}` (`𝒱`), a chosen representation `degRep μ v` of each `v ∈ 𝒱` and the coefficient
  map `degCoef μ v ξ = ĝ(ξ)` (`coef` of `RouteAInputs`). Every identity of `lem:spec:degone`
  holds for any representation, so the choice is harmless.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate InnerProductSpace

section Realization

variable {Ω : Type*} [Fintype Ω]

/-- **The complex realization** `f ↦ (√μ(x) f(x))_x` of `L²(μ)`. -/
noncomputable def l2MapC (μ : Ω → ℝ) : (Ω → ℂ) →ₗ[ℂ] EuclideanSpace ℂ Ω where
  toFun f := WithLp.toLp 2 (fun x => ((√(μ x) : ℝ) : ℂ) * f x)
  map_add' f g := by
    ext x
    simp [mul_add]
  map_smul' c f := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.smul_apply]
    ring

omit [Fintype Ω] in
theorem l2MapC_ofLp (μ : Ω → ℝ) (f : Ω → ℂ) (x : Ω) :
    (l2MapC μ f).ofLp x = ((√(μ x) : ℝ) : ℂ) * f x := rfl

lemma ofReal_sqrt_mul_self {a : ℝ} (ha : 0 ≤ a) : ((√a : ℝ) : ℂ) * ((√a : ℝ) : ℂ) = (a : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha]

/-- `⟪l2MapC f, l2MapC g⟫ = E_μ f̄ g`. -/
theorem inner_l2MapC (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (f g : Ω → ℂ) :
    ⟪l2MapC μ f, l2MapC μ g⟫_ℂ = ∑ x, (μ x : ℂ) * (conj (f x) * g x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine sum_congr rfl fun x _ => ?_
  simp only [l2MapC_ofLp, Pi.star_apply, RCLike.star_def, map_mul, Complex.conj_ofReal]
  have h := ofReal_sqrt_mul_self (hμ x)
  calc ((√(μ x) : ℝ) : ℂ) * g x * (((√(μ x) : ℝ) : ℂ) * conj (f x))
      = (((√(μ x) : ℝ) : ℂ) * ((√(μ x) : ℝ) : ℂ)) * (conj (f x) * g x) := by ring
    _ = (μ x : ℂ) * (conj (f x) * g x) := by rw [h]

/-- `‖l2MapC f‖² = E_μ |f|²`. -/
theorem norm_l2MapC_sq (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (f : Ω → ℂ) :
    ‖l2MapC μ f‖ ^ 2 = ∑ x, μ x * ‖f x‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_l2MapC μ hμ f f, RCLike.re_to_complex,
    Complex.re_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The kernel operator on functions: `(Op f)(x) = ∑_{x'} μ(x') k(x, x') f(x')`. -/
noncomputable def opFun (μ : Ω → ℝ) (k : Ω → Ω → ℝ) (f : Ω → ℂ) (x : Ω) : ℂ :=
  ∑ x', (μ x' : ℂ) * (k x x' : ℂ) * f x'

/-- **The kernel operator** on `EuclideanSpace ℂ Ω`: matrix `√μ(x) k(x, x') √μ(x')`. -/
noncomputable def kernelOpC (μ : Ω → ℝ) (k : Ω → Ω → ℝ) :
    EuclideanSpace ℂ Ω →ₗ[ℂ] EuclideanSpace ℂ Ω where
  toFun v := WithLp.toLp 2 (fun x => ∑ x', ((√(μ x) * k x x' * √(μ x') : ℝ) : ℂ) * v.ofLp x')
  map_add' u v := by
    ext x
    simp [mul_add, sum_add_distrib]
  map_smul' c v := by
    ext x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun x' _ => by ring

theorem kernelOpC_ofLp (μ : Ω → ℝ) (k : Ω → Ω → ℝ) (v : EuclideanSpace ℂ Ω) (x : Ω) :
    (kernelOpC μ k v).ofLp x = ∑ x', ((√(μ x) * k x x' * √(μ x') : ℝ) : ℂ) * v.ofLp x' := rfl

/-- **The operator on functions**: `kernelOpC (l2MapC f) = l2MapC (Op f)`. -/
theorem kernelOpC_l2MapC (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (k : Ω → Ω → ℝ) (f : Ω → ℂ) :
    kernelOpC μ k (l2MapC μ f) = l2MapC μ (opFun μ k f) := by
  ext x
  rw [kernelOpC_ofLp, l2MapC_ofLp]
  unfold opFun
  rw [mul_sum]
  refine sum_congr rfl fun x' _ => ?_
  rw [l2MapC_ofLp]
  have h := ofReal_sqrt_mul_self (hμ x')
  push_cast
  calc ((√(μ x) : ℝ) : ℂ) * (k x x' : ℂ) * ((√(μ x') : ℝ) : ℂ) * (((√(μ x') : ℝ) : ℂ) * f x')
      = ((√(μ x) : ℝ) : ℂ) * ((((√(μ x') : ℝ) : ℂ) * ((√(μ x') : ℝ) : ℂ)) * (k x x' : ℂ) * f x') :=
        by ring
    _ = ((√(μ x) : ℝ) : ℂ) * ((μ x' : ℂ) * (k x x' : ℂ) * f x') := by rw [h]

/-- `⟪u, kernelOpC v⟫ = ∑_{x,x'} ū_x m(x, x') v_{x'}`. -/
theorem inner_kernelOpC (μ : Ω → ℝ) (k : Ω → Ω → ℝ) (u v : EuclideanSpace ℂ Ω) :
    ⟪u, kernelOpC μ k v⟫_ℂ =
      ∑ x, ∑ x', conj (u.ofLp x) * ((√(μ x) * k x x' * √(μ x') : ℝ) : ℂ) * v.ofLp x' := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine sum_congr rfl fun x _ => ?_
  simp only [kernelOpC_ofLp, Pi.star_apply, RCLike.star_def, sum_mul]
  exact sum_congr rfl fun x' _ => by ring

/-- **`symm`**: `kernelOpC μ k` is symmetric for symmetric real `k`. -/
theorem kernelOpC_isSymmetric (μ : Ω → ℝ) (k : Ω → Ω → ℝ) (hk : ∀ x x', k x x' = k x' x) :
    (kernelOpC μ k).IsSymmetric := by
  intro u v
  rw [← inner_conj_symm, inner_kernelOpC, inner_kernelOpC, map_sum, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun x' _ => ?_
  rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, hk x x']
  push_cast
  ring

/-! ## The real realization embeds -/

/-- **The embedding** of WP-A's real realization: `v ↦ (v_x : ℂ)_x`. -/
noncomputable def embedR : EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℂ Ω where
  toFun v := WithLp.toLp 2 (fun x => ((v.ofLp x : ℝ) : ℂ))
  map_add' u v := by
    ext x
    simp
  map_smul' c v := by
    ext x
    simp

omit [Fintype Ω] in
theorem embedR_ofLp (v : EuclideanSpace ℝ Ω) (x : Ω) : (embedR v).ofLp x = ((v.ofLp x : ℝ) : ℂ) :=
  rfl

/-- `⟪embedR u, embedR v⟫_ℂ = ⟪u, v⟫_ℝ`. -/
theorem inner_embedR (u v : EuclideanSpace ℝ Ω) :
    ⟪embedR u, embedR v⟫_ℂ = ((⟪u, v⟫_ℝ : ℝ) : ℂ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  push_cast
  refine sum_congr rfl fun x _ => ?_
  simp only [embedR_ofLp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal, star_trivial]

theorem norm_embedR (v : EuclideanSpace ℝ Ω) : ‖embedR v‖ = ‖v‖ := by
  have h2 : ‖embedR v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_embedR, RCLike.re_to_complex, Complex.ofReal_re,
      real_inner_self_eq_norm_sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- `embedR ∘ l2Map = l2MapC ∘ (ℝ → ℂ)`. -/
theorem embedR_l2Map (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    embedR (InfluenceGlue.l2Map μ f) = l2MapC μ.weight (fun x => ((f x : ℝ) : ℂ)) := by
  ext x
  rw [embedR_ofLp, InfluenceGlue.l2Map_ofLp, l2MapC_ofLp]
  push_cast
  rfl

/-- `embedR ∘ kernelOp = kernelOpC ∘ embedR`. -/
theorem embedR_kernelOp (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) (v : EuclideanSpace ℝ Ω) :
    embedR (Spectral.kernelOp μ k v) = kernelOpC μ.weight k (embedR v) := by
  ext x
  rw [embedR_ofLp, Spectral.kernelOp_ofLp, kernelOpC_ofLp]
  push_cast
  refine sum_congr rfl fun x' _ => ?_
  rw [embedR_ofLp]

/-- **Real forms are real parts of complex forms**:
`re⟪embedR v, kernelOpC (embedR v)⟫ = ⟪v, kernelOp v⟫`. -/
theorem re_inner_embedR_kernelOp (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) (u v : EuclideanSpace ℝ Ω) :
    ⟪embedR u, kernelOpC μ.weight k (embedR v)⟫_ℂ = ((⟪u, Spectral.kernelOp μ k v⟫_ℝ : ℝ) : ℂ) := by
  rw [← embedR_kernelOp, inner_embedR]

end Realization

/-! ## The cut operator acting on complex functions -/

section Cut

variable {U : Type*} [Fintype U] [DecidableEq U] (D : Cuts.SpecData U)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The complex cut operator** `Op = T_{K/Z}` on `EuclideanSpace ℂ (U⁺ → F)`. -/
noncomputable def cutOpC (hne : (Labellings.injLabellings F D.G).Nonempty) :
    EuclideanSpace ℂ (D.cut.Half → F) →ₗ[ℂ] EuclideanSpace ℂ (D.cut.Half → F) :=
  kernelOpC (D.halfLaw hne).weight (fun x x' => D.cutK x x' / D.cutZ hne)

/-- The constants `1 ∈ L²(μ)`, complex realization. -/
noncomputable def cutOneC (hne : (Labellings.injLabellings F D.G).Nonempty) :
    EuclideanSpace ℂ (D.cut.Half → F) :=
  l2MapC (D.halfLaw hne).weight (fun _ => 1)

/-- **WP-A's real cut realization embeds**: `embedR ∘ cutOp = cutOpC ∘ embedR`. -/
theorem embedR_cutOp (hne : (Labellings.injLabellings F D.G).Nonempty)
    (v : EuclideanSpace ℝ (D.cut.Half → F)) :
    embedR (Spectral.cutOp D hne v) = cutOpC D hne (embedR v) :=
  embedR_kernelOp _ _ v

theorem embedR_cutOne (hne : (Labellings.injLabellings F D.G).Nonempty) :
    embedR (Spectral.cutOne D hne) = cutOneC D hne := by
  unfold Spectral.cutOne cutOneC
  rw [embedR_l2Map]
  push_cast
  rfl

/-- The real quadratic form of WP-A's `cutOp` is the complex one on embedded vectors. -/
theorem inner_embedR_cutOp (hne : (Labellings.injLabellings F D.G).Nonempty)
    (u v : EuclideanSpace ℝ (D.cut.Half → F)) :
    ⟪embedR u, cutOpC D hne (embedR v)⟫_ℂ = ((⟪u, Spectral.cutOp D hne v⟫_ℝ : ℝ) : ℂ) :=
  re_inner_embedR_kernelOp _ _ u v

/-- **`symm`** for the complex cut operator. -/
theorem cutOpC_isSymmetric (hne : (Labellings.injLabellings F D.G).Nonempty) :
    (cutOpC D hne).IsSymmetric :=
  kernelOpC_isSymmetric _ _ fun x x' => by rw [D.cutK_symm]

end Cut

/-! ## The degree-one space -/

section DegreeOne

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- `F_V(x) = ∑_k g_k(x_k)`. -/
noncomputable def degFun (g : U → ZMod p → ℂ) (x : U → ZMod p) : ℂ := ∑ k, g k (x k)

/-- The mean-zero tuples `(g_k)_k`, `g_k ∈ L²_0(𝔽_p)`. -/
def meanZero (p : ℕ) [Fact p.Prime] (U : Type*) [Fintype U] : Submodule ℂ (U → ZMod p → ℂ) where
  carrier := {g | ∀ k, ∑ a, g k a = 0}
  add_mem' {g h} hg hh k := by
    simp only [Pi.add_apply, sum_add_distrib, hg k, hh k, add_zero]
  zero_mem' k := by simp
  smul_mem' c g hg k := by
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum, hg k, mul_zero]

/-- `g ↦ F_V` as a linear map. -/
noncomputable def degFunLin : (U → ZMod p → ℂ) →ₗ[ℂ] ((U → ZMod p) → ℂ) where
  toFun g := degFun g
  map_add' g h := by
    funext x
    simp only [degFun, Pi.add_apply, sum_add_distrib]
  map_smul' c g := by
    funext x
    simp only [degFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]

/-- The synthesis `g ↦ l2MapC (∑_k g_k(x_k))`. -/
noncomputable def degMap (μ : (U → ZMod p) → ℝ) :
    (U → ZMod p → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (U → ZMod p) :=
  (l2MapC μ).comp degFunLin

omit [Fact p.Prime] [DecidableEq U] in
theorem degMap_apply (μ : (U → ZMod p) → ℝ) (g : U → ZMod p → ℂ) :
    degMap μ g = l2MapC μ (degFun g) := rfl

/-- **The degree-one space** `𝒱` in the complex realization. -/
noncomputable def degSpace (μ : (U → ZMod p) → ℝ) : Submodule ℂ (EuclideanSpace ℂ (U → ZMod p)) :=
  (meanZero p U).map (degMap μ)

omit [DecidableEq U] in
theorem degMap_mem (μ : (U → ZMod p) → ℝ) {g : U → ZMod p → ℂ} (hg : ∀ k, ∑ a, g k a = 0) :
    degMap μ g ∈ degSpace μ :=
  Submodule.mem_map_of_mem (p := meanZero p U) hg

/-- A chosen representation `v = l2MapC(∑_k g_k(x_k))` of `v ∈ 𝒱` (`0` off `𝒱`). -/
noncomputable def degRep (μ : (U → ZMod p) → ℝ) (v : EuclideanSpace ℂ (U → ZMod p)) :
    U → ZMod p → ℂ := by
  classical exact if h : v ∈ degSpace μ then Classical.choose (Submodule.mem_map.mp h) else 0

omit [DecidableEq U] in
theorem degRep_spec (μ : (U → ZMod p) → ℝ) {v : EuclideanSpace ℂ (U → ZMod p)}
    (hv : v ∈ degSpace μ) :
    (∀ k, ∑ a, degRep μ v k a = 0) ∧ degMap μ (degRep μ v) = v := by
  have e : degRep μ v = Classical.choose (Submodule.mem_map.mp hv) := by
    unfold degRep
    simp only [hv, ↓reduceDIte]
  rw [e]
  exact Classical.choose_spec (Submodule.mem_map.mp hv)

/-- **The coefficient map** `coef v ξ = ĝ(ξ)` of `RouteAInputs`. -/
noncomputable def degCoef (μ : (U → ZMod p) → ℝ) (v : EuclideanSpace ℂ (U → ZMod p))
    (ξ : ZMod p) (k : U) : ℂ :=
  fcoef (degRep μ v k) ξ

omit [DecidableEq U] in
theorem degCoef_zero (μ : (U → ZMod p) → ℝ) {v : EuclideanSpace ℂ (U → ZMod p)}
    (hv : v ∈ degSpace μ) (k : U) : degCoef μ v 0 k = 0 := by
  unfold degCoef
  rw [fcoef_zero, (degRep_spec μ hv).1 k, mul_zero]

end DegreeOne

end Sarkozy.SpectralD.Cx
