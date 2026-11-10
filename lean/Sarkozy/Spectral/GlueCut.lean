module

public import Sarkozy.Cuts.CutKernel
public import Sarkozy.InfluenceGlue.L2
public import Sarkozy.Spectral.RouteA

/-!
# Glue, II: the cut operator of `lem:spec:cutkernel` as an operator on `L²(μ)`

WP-P's `Sarkozy.Cuts.SpecData.cutForm` states the cut operator `A = T_{K/Z}` of
`lem:spec:cutkernel` (b) as a bilinear form on functions, `kernelForm μ μ (K/Z)`, for the half
law `μ = λ(G⁺)` (`halfLaw`). The spectral criterion of `Sarkozy.Spectral` needs an operator
`T : H →ₗ H` on an inner product space. This file supplies the operator.

* `kernelOp μ k`: the operator on `EuclideanSpace ℝ Ω` with matrix `√μ(x) k(x, x') √μ(x')`. The
  isometry `InfluenceGlue.l2Map` (`f ↦ (√μ(x) f(x))_x`) carries `L²(μ)` onto its range, and
  `inner_l2Map_kernelOp` gives `⟪l2Map f, kernelOp μ k (l2Map g)⟫ = kernelForm μ μ k f g`.
* `kernelOp_isSymmetric`: `T` is symmetric when `k` is.
* `cutOp D hne = kernelOp (halfLaw) (K/Z)` and `cutOne = l2Map μ 1`. From WP-P's results:
  - `cutOp_isSymmetric` (`cutK_symm`) is the field `symm` of `RouteAInputs`;
  - `norm_cutOne` is `norm_one`;
  - `cutOp_mean` (`expect_cut_form` with `F = H = 1`) is `rho_mean`, `⟪1, Op 1⟫ = 1`;
  - `cutOp_form` gives `⟪l2Map f, Op (l2Map f)⟫ = cutForm f f = E_λ[f(x) f(x')]`, which carries
    the conclusions of the criterion back to functions;
  - `cutOp_one_right` gives `⟪l2Map f, Op 1⟫ = E_λ f(x)`, so `⟪1, Op v⟫ = E_λ v(x')`, the
    identity behind `rho_V`.

The realization is real (`𝕜 = ℝ`). The Fourier analysis of the degree-one block uses complex
coefficients; see the report for this mismatch.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.Spectral

open Sarkozy Sarkozy.InfluenceGlue Sarkozy.Cuts

variable {Ω : Type*} [Fintype Ω]

/-- The operator of the kernel `k` relative to `μ ⊗ μ`, on `EuclideanSpace ℝ Ω`. -/
noncomputable def kernelOp (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) :
    EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ Ω where
  toFun v := WithLp.toLp 2 (fun x => ∑ x', √(μ.weight x) * k x x' * √(μ.weight x') * v.ofLp x')
  map_add' u v := by
    ext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x' _ => by ring

theorem kernelOp_ofLp (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) (v : EuclideanSpace ℝ Ω) (x : Ω) :
    (kernelOp μ k v).ofLp x = ∑ x', √(μ.weight x) * k x x' * √(μ.weight x') * v.ofLp x' := rfl

theorem inner_kernelOp (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) (u v : EuclideanSpace ℝ Ω) :
    ⟪u, kernelOp μ k v⟫_ℝ =
      ∑ x, ∑ x', u.ofLp x * (√(μ.weight x) * k x x' * √(μ.weight x')) * v.ofLp x' := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [kernelOp_ofLp, star_trivial, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x' _ => by ring

/-- **The form of `kernelOp`**: `⟪l2Map f, kernelOp μ k (l2Map g)⟫ = kernelForm μ μ k f g`. -/
theorem inner_l2Map_kernelOp (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) (f g : Ω → ℝ) :
    ⟪l2Map μ f, kernelOp μ k (l2Map μ g)⟫_ℝ = kernelForm μ μ k f g := by
  rw [inner_kernelOp, kernelForm_apply]
  simp only [FiniteLaw.expect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  simp only [l2Map_ofLp]
  have h1 := Real.mul_self_sqrt (μ.nonneg x)
  have h2 := Real.mul_self_sqrt (μ.nonneg x')
  calc √(μ.weight x) * f x * (√(μ.weight x) * k x x' * √(μ.weight x')) *
        (√(μ.weight x') * g x')
      = (√(μ.weight x) * √(μ.weight x)) * ((√(μ.weight x') * √(μ.weight x')) *
          (f x * k x x' * g x')) := by ring
    _ = μ.weight x * (f x * (μ.weight x' * (k x x' * g x'))) := by rw [h1, h2]; ring

/-- `kernelOp μ k` is symmetric when `k` is. -/
theorem kernelOp_isSymmetric (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ)
    (hk : ∀ x x', k x x' = k x' x) : (kernelOp μ k).IsSymmetric := by
  intro u v
  rw [real_inner_comm, inner_kernelOp, inner_kernelOp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  rw [hk x x']
  ring

section Cut

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The cut operator** `Op = T_{K/Z}` on `L²(μ)`, `μ = λ(G⁺)`, realized on
`EuclideanSpace ℝ (U⁺ → F)`. -/
noncomputable def cutOp (hne : (Labellings.injLabellings F D.G).Nonempty) :
    EuclideanSpace ℝ (D.cut.Half → F) →ₗ[ℝ] EuclideanSpace ℝ (D.cut.Half → F) :=
  kernelOp (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne)

/-- The constants `1 ∈ L²(μ)`. -/
noncomputable def cutOne (hne : (Labellings.injLabellings F D.G).Nonempty) :
    EuclideanSpace ℝ (D.cut.Half → F) :=
  l2Map (D.halfLaw hne) (fun _ => 1)

/-- `⟪l2Map f, Op (l2Map g)⟫ = cutForm f g = E_λ[f(x) g(x')]` (`lem:spec:cutkernel` (b)). -/
theorem cutOp_form (hne : (Labellings.injLabellings F D.G).Nonempty) (f g : (D.cut.Half → F) → ℝ) :
    ⟪l2Map (D.halfLaw hne) f, cutOp D hne (l2Map (D.halfLaw hne) g)⟫_ℝ = D.cutForm hne f g ∧
      D.cutForm hne f g =
        (Labellings.graphLaw D.G hne).expect (fun y => f (D.halfL y) * g (D.halfR y)) :=
  ⟨inner_l2Map_kernelOp _ _ f g, (D.expect_cut_form hne f g).symm⟩

/-- **`symm`**: the cut operator is symmetric (`cutK_symm`). -/
theorem cutOp_isSymmetric (hne : (Labellings.injLabellings F D.G).Nonempty) :
    (cutOp D hne).IsSymmetric :=
  kernelOp_isSymmetric (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne) fun x x' => by
    rw [D.cutK_symm]

/-- **`norm_one`**: `‖1‖_μ = 1`. -/
theorem norm_cutOne (hne : (Labellings.injLabellings F D.G).Nonempty) : ‖cutOne D hne‖ = 1 := by
  unfold cutOne
  have h1 := norm_l2Map_sq (D.halfLaw hne) (fun _ => (1 : ℝ))
  simp only [one_pow, FiniteLaw.expect_const] at h1
  have h0 := norm_nonneg (l2Map (D.halfLaw hne) (fun _ => (1 : ℝ)))
  nlinarith [h1, h0]

/-- **`rho_mean`**: `⟪1, Op 1⟫ = E_λ[1] = 1`. -/
theorem cutOp_mean (hne : (Labellings.injLabellings F D.G).Nonempty) :
    ⟪cutOne D hne, cutOp D hne (cutOne D hne)⟫_ℝ = 1 := by
  rw [cutOne, (cutOp_form D hne _ _).1, (cutOp_form D hne _ _).2]
  simp

/-- `⟪l2Map f, Op 1⟫ = E_λ f(x)` and `⟪1, Op (l2Map h)⟫ = E_λ h(x')`: the identities behind
`rho_V` (`⟪1, Op v⟫ = E_λ v(x') = E_{m_p} v = 0` on the degree-one space). -/
theorem cutOp_one_right (hne : (Labellings.injLabellings F D.G).Nonempty)
    (f h : (D.cut.Half → F) → ℝ) :
    ⟪l2Map (D.halfLaw hne) f, cutOp D hne (cutOne D hne)⟫_ℝ =
        (Labellings.graphLaw D.G hne).expect (fun y => f (D.halfL y)) ∧
      ⟪cutOne D hne, cutOp D hne (l2Map (D.halfLaw hne) h)⟫_ℝ =
        (Labellings.graphLaw D.G hne).expect (fun y => h (D.halfR y)) := by
  constructor
  · rw [cutOne, (cutOp_form D hne _ _).1, (cutOp_form D hne _ _).2]
    simp
  · rw [cutOne, (cutOp_form D hne _ _).1, (cutOp_form D hne _ _).2]
    simp

end Cut

end Sarkozy.Spectral
