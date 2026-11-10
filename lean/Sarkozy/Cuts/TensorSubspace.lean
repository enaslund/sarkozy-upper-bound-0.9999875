module

public import Sarkozy.Cuts.TensorSupport

/-!
# Cuts, VIII‴: tensor products of subspaces (`lem:spec:tensorcomp` (b))

`13_cuts_correlations.tex`, `lem:spec:tensorcomp` (b), second statement, for proper subspaces
`𝒱_p ⊆ L²(μ_p)`. The caps `-g p^{-1/2} ‖F‖² ≤ ⟨F, A_p F⟩ ≤ (1 + c⁺/p) ‖F‖²` are assumed only for
`F ∈ 𝒱_p`. The conclusion is the lower bound for every `F ∈ ⊗_p 𝒱_p`, the span of the products
`∏_p f_p(x_p)` with `f_p ∈ 𝒱_p` (`tensorSpan`).

The paper compresses `A_p` to `C_p = P_p A_p P_p` on `𝒱_p` and applies (a) to the `C_p`. Here the
same vertex expansion as in `Sarkozy.Cuts.tensor_lower` is run in the coordinates of a basis
`(e_{p,k})_k` of each `𝒱_p`. The basis need not be orthonormal: its Gram matrix
`γ_p(k, l) = ⟨e_{p,k}, e_{p,l}⟩` (the inner product of `𝒱_p` in these coordinates) takes the
place of the identity, and `m_p(k, l) = ⟨e_{p,k}, A_p e_{p,l}⟩` is the form of the compression
`C_p` in the same coordinates. No orthogonal projection is constructed.

* `tensor_quad_rel`: the expansion for kernels relative to Gram kernels. If `m_i + g_i γ_i ⪰ 0`
  and `(1 + b_i) γ_i - m_i ⪰ 0`, then `⊗_i m_i + M ⊗_i γ_i ⪰ 0` whenever
  `M ≥ g_i ∏_{j ≠ i} (1 + b_j)` for every `i`.
* `tensorSpan`, `mem_tensorSpan_iff_basis`: `⊗_i 𝒱_i`, and the expansion of its elements in the
  product basis.
* `kernelForm_pi_prod`, `ip_pi_prod`: the form of a product kernel, and the inner product, on
  products of functions.
* `tensor_lower_sub`: `lem:spec:tensorcomp` (a) on `⊗_i 𝒱_i`, with the caps assumed on `𝒱_i`
  only.
* `SpecData.block_cut_lower_sub`: `lem:spec:tensorcomp` (b), second statement, for subspaces;
  `SpecData.block_cut_lower_sub_single`: the bound `-g p^{-1/2} ‖F‖²` for a single prime.
* `funOf`, `comp_mem_tensorSpan`: the last sentence of (b). The functions of `(π_p(x_p))_p` form
  a subspace of `⊗_p 𝒱_p`, where `𝒱_p` is the space of functions of `π_p(x_p)`; with `π_p` the
  restriction of the labelling to `A`, this gives the functions of `x_A`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Labellings

section Rel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ι → Type*} [∀ i, Fintype (K i)]
  [∀ i, DecidableEq (K i)]

/-- **The vertex expansion relative to Gram kernels.** Let `m_i`, `γ_i` be real kernels on finite
sets `K_i` with `m_i + g_i γ_i ⪰ 0` and `(1 + b_i) γ_i - m_i ⪰ 0` (positive semidefinite
matrices), `b_i ≥ 0`, `0 ≤ g_i ≤ 1 + b_i`. If `M ≥ 0` and `M ≥ g_i ∏_{j ≠ i} (1 + b_j)` for all `i`,
then `⊗_i m_i + M ⊗_i γ_i ⪰ 0`. -/
theorem tensor_quad_rel (m γ : ∀ i, K i → K i → ℝ) (g b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hg0 : ∀ i, 0 ≤ g i) (hgb : ∀ i, g i ≤ 1 + b i)
    (hlow : ∀ i, QuadNonneg (fun k l => m i k l + g i * γ i k l))
    (hup : ∀ i, QuadNonneg (fun k l => (1 + b i) * γ i k l - m i k l))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, g i * ∏ j ∈ Finset.univ.erase i, (1 + b j) ≤ M)
    (v : (∀ i, K i) → ℝ) :
    0 ≤ ∑ k, ∑ l, v k * ((∏ i, m i (k i) (l i)) + M * ∏ i, γ i (k i) (l i)) * v l := by
  classical
  set a : ι → ℝ := fun i => 1 + b i
  set w : ι → ℝ := fun i => a i + g i
  have hw : ∀ i, 0 < w i := fun i => by
    simp only [w, a]
    linarith [hb0 i, hg0 i]
  set Lm : ∀ i, K i → K i → ℝ := fun i k l => m i k l + g i * γ i k l
  set Lp : ∀ i, K i → K i → ℝ := fun i k l => a i * γ i k l - m i k l
  have hc : ∀ i (k l : K i), m i k l = (a i * Lm i k l + (-g i) * Lp i k l) / w i := by
    intro i k l
    rw [eq_div_iff (hw i).ne']
    simp only [Lm, Lp, w]
    ring
  have hid : ∀ i (k l : K i), γ i k l = (Lm i k l + Lp i k l) / w i := by
    intro i k l
    rw [eq_div_iff (hw i).ne']
    simp only [Lm, Lp, w]
    ring
  have hexp : ∀ k l : (∀ i, K i), (∏ i, m i (k i) (l i)) + M * ∏ i, γ i (k i) (l i) =
      (∏ i, (w i)⁻¹) * ∑ S ∈ (Finset.univ : Finset ι).powerset,
        ((∏ i ∈ S, a i) * (∏ i ∈ Finset.univ \ S, (-g i)) + M) *
          ((∏ i ∈ S, Lm i (k i) (l i)) * ∏ i ∈ Finset.univ \ S, Lp i (k i) (l i)) := by
    intro k l
    have h1 : ∏ i, m i (k i) (l i) = (∏ i, (w i)⁻¹) *
        ∏ i, (a i * Lm i (k i) (l i) + (-g i) * Lp i (k i) (l i)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [hc]; field_simp [(hw i).ne'])
    have h2 : ∏ i, γ i (k i) (l i) = (∏ i, (w i)⁻¹) *
        ∏ i, (Lm i (k i) (l i) + Lp i (k i) (l i)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [hid]; field_simp [(hw i).ne'])
    rw [h1, h2, Finset.prod_add, Finset.prod_add, mul_left_comm M, ← mul_add, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  set κ : Finset ι → ℝ := fun S => (∏ i ∈ S, a i) * (∏ i ∈ Finset.univ \ S, (-g i)) + M with hκ
  set KS : Finset ι → (∀ i, K i) → (∀ i, K i) → ℝ := fun S k l =>
    (∏ i ∈ S, Lm i (k i) (l i)) * ∏ i ∈ Finset.univ \ S, Lp i (k i) (l i) with hKS
  set Wc := ∏ i, (w i)⁻¹
  have hsum : ∑ k, ∑ l, v k * ((∏ i, m i (k i) (l i)) + M * ∏ i, γ i (k i) (l i)) * v l =
      ∑ S ∈ (Finset.univ : Finset ι).powerset, Wc * (κ S * ∑ k, ∑ l, v k * KS S k l * v l) := by
    have e1 : ∀ k l, v k * ((∏ i, m i (k i) (l i)) + M * ∏ i, γ i (k i) (l i)) * v l =
        ∑ S ∈ (Finset.univ : Finset ι).powerset, Wc * (κ S * (v k * KS S k l * v l)) := by
      intro k l
      rw [hexp k l, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      simp only [κ, KS]
      ring
    simp only [e1]
    simp only [Finset.mul_sum]
    conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hsum]
  refine Finset.sum_nonneg (fun S _ => ?_)
  have hWc : 0 ≤ Wc := Finset.prod_nonneg (fun i _ => (inv_pos.mpr (hw i)).le)
  refine mul_nonneg hWc (mul_nonneg (vertex_coeff_nonneg a g hg0 hgb hM0 hM S) ?_)
  have hq := (QuadNonneg.prod Finset.univ (fun i => if i ∈ S then Lm i else Lp i)
    (fun i _ => by
      by_cases hi : i ∈ S
      · simp only [hi, ite_true]; exact hlow i
      · simp only [hi, ite_false]; exact hup i)).2 v
  refine le_of_le_of_eq hq (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_)))
  have e : ∏ i, (if i ∈ S then Lm i else Lp i) (k i) (l i) = KS S k l := by
    rw [← Finset.prod_sdiff (Finset.subset_univ S), mul_comm]
    simp only [KS]
    congr 1
    · exact Finset.prod_congr rfl (fun i hi => by simp only [hi, ite_true])
    · exact Finset.prod_congr rfl (fun i hi => by
        simp only [(Finset.mem_sdiff.mp hi).2, ite_false])
  beta_reduce
  rw [e]

end Rel

section Sub

variable {ι : Type*} {Ω : ι → Type*}

/-- The tensor product `⊗_i 𝒱_i` of subspaces `𝒱_i` of the functions on `Ω_i`: the span of the
products `x ↦ ∏_i f_i(x_i)` with `f_i ∈ 𝒱_i`. -/
def tensorSpan [Fintype ι] (V : ∀ i, Submodule ℝ (Ω i → ℝ)) : Submodule ℝ ((∀ i, Ω i) → ℝ) :=
  Submodule.span ℝ {Fn | ∃ f : ∀ i, Ω i → ℝ, (∀ i, f i ∈ V i) ∧ Fn = fun x => ∏ i, f i (x i)}

/-- The basis vector `e_{i,k}` of `𝒱_i` (a basis from `Module.finBasis`), as a function. -/
noncomputable def subBasis [∀ i, Fintype (Ω i)] (V : ∀ i, Submodule ℝ (Ω i → ℝ)) (i : ι)
    (k : Fin (Module.finrank ℝ (V i))) : Ω i → ℝ :=
  ((Module.finBasis ℝ (V i) k : V i) : Ω i → ℝ)

theorem subBasis_mem [∀ i, Fintype (Ω i)] (V : ∀ i, Submodule ℝ (Ω i → ℝ)) (i : ι)
    (k : Fin (Module.finrank ℝ (V i))) : subBasis V i k ∈ V i :=
  (Module.finBasis ℝ (V i) k).2

/-- Every element of `𝒱_i` is a combination of the basis vectors. -/
theorem subBasis_expand [∀ i, Fintype (Ω i)] (V : ∀ i, Submodule ℝ (Ω i → ℝ)) (i : ι)
    {f : Ω i → ℝ} (hf : f ∈ V i) :
    f = ∑ k, (Module.finBasis ℝ (V i)).repr ⟨f, hf⟩ k • subBasis V i k := by
  have h := (Module.finBasis ℝ (V i)).sum_repr ⟨f, hf⟩
  have h2 := congrArg (fun z : V i => (z : Ω i → ℝ)) h
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  exact h2.symm

/-- **The product basis of `⊗_i 𝒱_i`.** Every `F ∈ ⊗_i 𝒱_i` is a combination
`F = ∑_k α_k ∏_i e_{i,k_i}` of the products of basis vectors. -/
theorem mem_tensorSpan_iff_basis [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Ω i)]
    (V : ∀ i, Submodule ℝ (Ω i → ℝ)) {Fn : (∀ i, Ω i) → ℝ}
    (hF : Fn ∈ tensorSpan V) :
    ∃ α : (∀ i, Fin (Module.finrank ℝ (V i))) → ℝ,
      Fn = ∑ k, α k • (fun x => ∏ i, subBasis V i (k i) (x i)) := by
  set E : (∀ i, Fin (Module.finrank ℝ (V i))) → ((∀ i, Ω i) → ℝ) :=
    fun k x => ∏ i, subBasis V i (k i) (x i) with hE
  have hle : tensorSpan V ≤ Submodule.span ℝ (Set.range E) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    have hprod : (fun x => ∏ i, f i (x i)) =
        ∑ k : (∀ i, Fin (Module.finrank ℝ (V i))),
          (∏ i, (Module.finBasis ℝ (V i)).repr ⟨f i, hf i⟩ (k i)) • E k := by
      funext x
      have hfx : ∀ i, f i (x i) =
          ∑ k, (Module.finBasis ℝ (V i)).repr ⟨f i, hf i⟩ k * subBasis V i k (x i) := by
        intro i
        conv_lhs => rw [subBasis_expand V i (hf i)]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [hfx, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hE]
      rw [Fintype.prod_sum]
      exact Finset.sum_congr rfl (fun k _ => Finset.prod_mul_distrib)
    rw [SetLike.mem_coe, hprod]
    exact Submodule.sum_mem _ (fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hle hF)
  exact ⟨α, hα.symm⟩

/-- The quadratic form of a bilinear map at a combination `∑_k v_k e_k`. -/
theorem bilin_sum_sum {Z K' : Type*} [Fintype K'] (B : (Z → ℝ) →ₗ[ℝ] (Z → ℝ) →ₗ[ℝ] ℝ)
    (e : K' → Z → ℝ) (v : K' → ℝ) :
    B (∑ k, v k • e k) (∑ l, v l • e l) = ∑ k, ∑ l, v k * B (e k) (e l) * v l := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))

/-- The inner product of `L²(μ)` as a bilinear map. -/
noncomputable def ipBil {Z : Type*} [Fintype Z] (μ : FiniteLaw Z) :
    (Z → ℝ) →ₗ[ℝ] (Z → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f h => ip μ f h)
    (fun f₁ f₂ h => ip_add_left μ f₁ f₂ h)
    (fun c f h => ip_smul_left μ c f h)
    (fun f h₁ h₂ => by rw [ip_comm, ip_comm μ f h₁, ip_comm μ f h₂]; exact ip_add_left μ h₁ h₂ f)
    (fun c f h => by rw [ip_comm, ip_comm μ f h]; exact ip_smul_left μ c h f)

theorem ipBil_apply {Z : Type*} [Fintype Z] (μ : FiniteLaw Z) (f h : Z → ℝ) :
    ipBil μ f h = ip μ f h := rfl

/-- The form of a product kernel on products of functions factorizes:
`⟨⊗_i f_i, (⊗_i C_i)(⊗_i h_i)⟩ = ∏_i ⟨f_i, C_i h_i⟩`. -/
theorem kernelForm_pi_prod [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Ω i)) (c : ∀ i, Ω i → Ω i → ℝ)
    (f h : ∀ i, Ω i → ℝ) :
    kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun x y => ∏ i, c i (x i) (y i))
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, h i (y i)) =
      ∏ i, kernelForm (μ i) (μ i) (c i) (f i) (h i) := by
  rw [kernelForm_apply]
  have inner : ∀ x : (∀ i, Ω i), (FiniteLaw.pi μ).expect
      (fun y => (∏ i, c i (x i) (y i)) * ∏ i, h i (y i)) =
        ∏ i, (μ i).expect (fun y => c i (x i) y * h i y) := by
    intro x
    rw [← FiniteLaw.expect_pi_product]
    congr 1
    funext y
    rw [Finset.prod_mul_distrib]
  simp only [inner]
  rw [show (fun x : (∀ i, Ω i) => (∏ i, f i (x i)) *
      ∏ i, (μ i).expect (fun y => c i (x i) y * h i y)) =
      fun x => ∏ i, (f i (x i) * (μ i).expect (fun y => c i (x i) y * h i y)) from
    funext fun x => Finset.prod_mul_distrib.symm]
  refine (FiniteLaw.expect_pi_product μ
    (fun i z => f i z * (μ i).expect (fun y => c i z y * h i y))).trans ?_
  exact Finset.prod_congr rfl (fun i _ => (kernelForm_apply _ _ _ _ _).symm)

/-- `⟨⊗_i f_i, ⊗_i h_i⟩ = ∏_i ⟨f_i, h_i⟩`. -/
theorem ip_pi_prod [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Ω i)] (μ : ∀ i, FiniteLaw (Ω i))
    (f h : ∀ i, Ω i → ℝ) :
    ip (FiniteLaw.pi μ) (fun x => ∏ i, f i (x i)) (fun y => ∏ i, h i (y i)) =
      ∏ i, ip (μ i) (f i) (h i) := by
  unfold ip
  rw [← FiniteLaw.expect_pi_product]
  congr 1
  funext x
  rw [Finset.prod_mul_distrib]

/-- **`lem:spec:tensorcomp` (a), (b) on tensor products of subspaces.** Let `𝒱_i ⊆ L²(μ_i)` be
subspaces and `C_i` the self-adjoint operators with symmetric kernels `c_i`. Suppose
`-g_i ‖f‖² ≤ ⟨f, C_i f⟩ ≤ (1 + b_i)‖f‖²` for `f ∈ 𝒱_i` only, with `b_i ≥ 0` and
`0 ≤ g_i ≤ 1 + b_i`. Then `⟨F, (⊗_i C_i) F⟩ ≥ -M ‖F‖²` for every `F ∈ ⊗_i 𝒱_i`, whenever
`M ≥ g_i ∏_{j ≠ i} (1 + b_j)` for all `i`. -/
theorem tensor_lower_sub [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Ω i)) (c : ∀ i, Ω i → Ω i → ℝ)
    (hcs : ∀ i x y, c i x y = c i y x) (V : ∀ i, Submodule ℝ (Ω i → ℝ)) (g b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hg0 : ∀ i, 0 ≤ g i) (hgb : ∀ i, g i ≤ 1 + b i)
    (hlow : ∀ i, ∀ f ∈ V i, -g i * nrm (μ i) f ^ 2 ≤ kernelForm (μ i) (μ i) (c i) f f)
    (hup : ∀ i, ∀ f ∈ V i, kernelForm (μ i) (μ i) (c i) f f ≤ (1 + b i) * nrm (μ i) f ^ 2)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, g i * ∏ j ∈ Finset.univ.erase i, (1 + b j) ≤ M)
    {Fn : (∀ i, Ω i) → ℝ} (hF : Fn ∈ tensorSpan V) :
    -M * nrm (FiniteLaw.pi μ) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun x y => ∏ i, c i (x i) (y i)) Fn Fn := by
  classical
  obtain ⟨α, hα⟩ := mem_tensorSpan_iff_basis V hF
  set e := subBasis V with he
  set m : ∀ i, Fin (Module.finrank ℝ (V i)) → Fin (Module.finrank ℝ (V i)) → ℝ :=
    fun i k l => kernelForm (μ i) (μ i) (c i) (e i k) (e i l) with hm
  set γ : ∀ i, Fin (Module.finrank ℝ (V i)) → Fin (Module.finrank ℝ (V i)) → ℝ :=
    fun i k l => ip (μ i) (e i k) (e i l) with hγ
  have hcs' : ∀ i x y, c i y x = c i x y := fun i x y => (hcs i x y).symm
  have hmsym : ∀ i k l, m i k l = m i l k := fun i k l =>
    kernelForm_symm (μ i) (c i) (hcs' i) _ _
  have hγsym : ∀ i k l, γ i k l = γ i l k := fun i k l => ip_comm (μ i) _ _
  -- the caps in the basis coordinates
  have hcomb : ∀ i (v : Fin (Module.finrank ℝ (V i)) → ℝ), (∑ k, v k • e i k) ∈ V i :=
    fun i v => Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (subBasis_mem V i k))
  have hmq : ∀ i (v : Fin (Module.finrank ℝ (V i)) → ℝ),
      ∑ k, ∑ l, v k * m i k l * v l = kernelForm (μ i) (μ i) (c i) (∑ k, v k • e i k)
        (∑ k, v k • e i k) := fun i v => (bilin_sum_sum _ (e i) v).symm
  have hγq : ∀ i (v : Fin (Module.finrank ℝ (V i)) → ℝ),
      ∑ k, ∑ l, v k * γ i k l * v l = nrm (μ i) (∑ k, v k • e i k) ^ 2 := fun i v => by
    rw [nrm_sq_eq, ← ipBil_apply, bilin_sum_sum]
    rfl
  have hlow' : ∀ i, QuadNonneg (fun k l => m i k l + g i * γ i k l) := by
    intro i
    refine ⟨fun k l => by beta_reduce; rw [hmsym i k l, hγsym i k l], fun v => ?_⟩
    have e1 : ∑ k, ∑ l, v k * (m i k l + g i * γ i k l) * v l =
        (∑ k, ∑ l, v k * m i k l * v l) + g i * ∑ k, ∑ l, v k * γ i k l * v l := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    rw [e1, hmq, hγq]
    linarith [hlow i _ (hcomb i v)]
  have hup' : ∀ i, QuadNonneg (fun k l => (1 + b i) * γ i k l - m i k l) := by
    intro i
    refine ⟨fun k l => by beta_reduce; rw [hmsym i k l, hγsym i k l], fun v => ?_⟩
    have e1 : ∑ k, ∑ l, v k * ((1 + b i) * γ i k l - m i k l) * v l =
        (1 + b i) * (∑ k, ∑ l, v k * γ i k l * v l) - ∑ k, ∑ l, v k * m i k l * v l := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    rw [e1, hmq, hγq]
    linarith [hup i _ (hcomb i v)]
  have key := tensor_quad_rel m γ g b hb0 hg0 hgb hlow' hup' hM0 hM α
  -- the two forms of `F` in the product basis
  set E : (∀ i, Fin (Module.finrank ℝ (V i))) → ((∀ i, Ω i) → ℝ) :=
    fun k x => ∏ i, e i (k i) (x i) with hE
  have hFE : Fn = ∑ k, α k • E k := hα
  have hform : kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun x y => ∏ i, c i (x i) (y i))
      Fn Fn = ∑ k, ∑ l, α k * (∏ i, m i (k i) (l i)) * α l := by
    rw [hFE, bilin_sum_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show E k = fun x => ∏ i, e i (k i) (x i) from rfl,
      show E l = fun y => ∏ i, e i (l i) (y i) from rfl, kernelForm_pi_prod]
  have hnrm : nrm (FiniteLaw.pi μ) Fn ^ 2 = ∑ k, ∑ l, α k * (∏ i, γ i (k i) (l i)) * α l := by
    rw [nrm_sq_eq, ← ipBil_apply, hFE, bilin_sum_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [ipBil_apply, show E k = fun x => ∏ i, e i (k i) (x i) from rfl,
      show E l = fun y => ∏ i, e i (l i) (y i) from rfl, ip_pi_prod]
  have hsplit : ∑ k, ∑ l, α k * ((∏ i, m i (k i) (l i)) + M * ∏ i, γ i (k i) (l i)) * α l =
      (∑ k, ∑ l, α k * (∏ i, m i (k i) (l i)) * α l) +
        M * ∑ k, ∑ l, α k * (∏ i, γ i (k i) (l i)) * α l := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  rw [hsplit, ← hform, ← hnrm] at key
  linarith

end Sub

section Functions

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}

/-- The space of functions of `π(x)` on `Ω'` (for `π : Ω' → Λ`): the range of `φ ↦ φ ∘ π`. -/
def funOf {Ω' Λ : Type*} (π : Ω' → Λ) : Submodule ℝ (Ω' → ℝ) :=
  LinearMap.range (LinearMap.funLeft ℝ ℝ π)

theorem comp_mem_funOf {Ω' Λ : Type*} (π : Ω' → Λ) (φ : Λ → ℝ) : (fun x => φ (π x)) ∈ funOf π :=
  ⟨φ, rfl⟩

/-- **`lem:spec:tensorcomp` (b), last sentence.** Every function of `(π_i(x_i))_i` lies in
`⊗_i 𝒱_i`, where `𝒱_i` is the space of functions of `π_i(x_i)` on `Ω_i`. For `A ⊆ U⁺` and
`π_p(x_p) = x_{A,p}` (the restriction of the labelling to `A`), these are the functions of `x_A`,
so (b) applies to the compression to the functions of the labels of a vertex set. -/
theorem comp_mem_tensorSpan {Λ : ι → Type*} [∀ i, Fintype (Λ i)] [∀ i, DecidableEq (Λ i)]
    (π : ∀ i, Ω i → Λ i) (Φ : (∀ i, Λ i) → ℝ) :
    (fun x => Φ (fun i => π i (x i))) ∈ tensorSpan (fun i => funOf (π i)) := by
  classical
  have e : (fun x : (∀ i, Ω i) => Φ (fun i => π i (x i))) =
      ∑ a : (∀ i, Λ i),
        Φ a • (fun x => ∏ i, (fun z => if π i z = a i then (1 : ℝ) else 0) (x i)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.prod_boole]
    have h : ∀ a : (∀ i, Λ i), (∀ i, π i (x i) = a i) ↔ (fun i => π i (x i)) = a :=
      fun a => funext_iff.symm
    simp only [h, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
  rw [e]
  refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact ⟨fun i z => if π i z = a i then (1 : ℝ) else 0,
    fun i => comp_mem_funOf (π i) (fun l => if l = a i then (1 : ℝ) else 0), rfl⟩

end Functions

namespace SpecData

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)

/-- **`lem:spec:tensorcomp` (b), second statement, for subspaces.** Let `B` be a block (index set
`ι`, fields `F i` with `p i = |F i| ≥ b > 0`), and for each `i` let `𝒱_i ⊆ L²(μ_i)` be a subspace on
which `-g p^{-1/2} ‖H‖² ≤ ⟨H, A_p H⟩ ≤ (1 + c⁺/p) ‖H‖²`, with `g p^{-1/2} < 1`. Then for every
`F ∈ ⊗_i 𝒱_i`, `⟨F, 𝖠_B F⟩ = E_{λ_B(G)}[F(x) F(x')] ≥ -(g/√b) ∏_p (1 + c⁺/p) ‖F‖²_{μ_B}`. -/
theorem block_cut_lower_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*}
    [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (hne : ∀ i, (injLabellings (F i) D.G).Nonempty) (p : ι → ℝ) {g cplus bmin : ℝ}
    (hg : 0 ≤ g) (hcp : 0 ≤ cplus) (hb : 0 < bmin) (hpb : ∀ i, bmin ≤ p i)
    (hgp : ∀ i, g * (√(p i))⁻¹ < 1) (V : ∀ i, Submodule ℝ ((D.cut.Half → F i) → ℝ))
    (hlow : ∀ i, ∀ Hf ∈ V i,
      -(g * (√(p i))⁻¹) * nrm (D.halfLaw (hne i)) Hf ^ 2 ≤ D.cutForm (hne i) Hf Hf)
    (hup : ∀ i, ∀ Hf ∈ V i,
      D.cutForm (hne i) Hf Hf ≤ (1 + cplus / p i) * nrm (D.halfLaw (hne i)) Hf ^ 2)
    {Fn : (∀ i, D.cut.Half → F i) → ℝ} (hF : Fn ∈ tensorSpan V) :
    -(g * (√bmin)⁻¹ * ∏ i, (1 + cplus / p i)) *
        nrm (FiniteLaw.pi (fun i => D.halfLaw (hne i))) Fn ^ 2 ≤
      (FiniteLaw.pi (fun i => graphLaw D.G (hne i))).expect
        (fun y => Fn (fun i => D.halfL (y i)) * Fn (fun i => D.halfR (y i))) := by
  rw [D.block_cut_form hne Fn Fn]
  have hp0 : ∀ i, 0 < p i := fun i => lt_of_lt_of_le hb (hpb i)
  have hb0 : ∀ i, 0 ≤ cplus / p i := fun i => div_nonneg hcp (hp0 i).le
  have hgi0 : ∀ i, 0 ≤ g * (√(p i))⁻¹ := fun i =>
    mul_nonneg hg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hgle : ∀ i, g * (√(p i))⁻¹ ≤ g * (√bmin)⁻¹ := fun i =>
    mul_le_mul_of_nonneg_left (inv_anti₀ (Real.sqrt_pos.mpr hb) (Real.sqrt_le_sqrt (hpb i))) hg
  refine tensor_lower_sub (fun i => D.halfLaw (hne i)) (fun i x x' => D.cutK x x' / D.cutZ (hne i))
    (fun i x y => by rw [D.cutK_symm]) V (fun i => g * (√(p i))⁻¹) (fun i => cplus / p i) hb0 hgi0
    (fun i => by linarith [hgp i, hb0 i]) hlow hup ?_ (fun i => ?_) hF
  · exact mul_nonneg (mul_nonneg hg (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      (Finset.prod_nonneg (fun i _ => by linarith [hb0 i]))
  · exact (tensorcomp_scalar Finset.univ (fun i => cplus / p i) (fun i _ => hb0 i)
      (Finset.mem_univ i) (hgi0 i) (hgle i)).1

/-- **`lem:spec:tensorcomp` (b), a single prime.** If `B = {p}`, the bound of
`block_cut_lower_sub` is `-g p^{-1/2} ‖F‖²`. -/
theorem block_cut_lower_sub_single {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (hne : ∀ i, (injLabellings (F i) D.G).Nonempty) (p : ι → ℝ) {g cplus : ℝ}
    (hg : 0 ≤ g) (hcp : 0 ≤ cplus) (hp : ∀ i, 0 < p i)
    (hgp : ∀ i, g * (√(p i))⁻¹ < 1) (V : ∀ i, Submodule ℝ ((D.cut.Half → F i) → ℝ))
    (hlow : ∀ i, ∀ Hf ∈ V i,
      -(g * (√(p i))⁻¹) * nrm (D.halfLaw (hne i)) Hf ^ 2 ≤ D.cutForm (hne i) Hf Hf)
    (hup : ∀ i, ∀ Hf ∈ V i,
      D.cutForm (hne i) Hf Hf ≤ (1 + cplus / p i) * nrm (D.halfLaw (hne i)) Hf ^ 2)
    {Fn : (∀ i, D.cut.Half → F i) → ℝ} (hF : Fn ∈ tensorSpan V) :
    -(g * (√(p default))⁻¹) * nrm (FiniteLaw.pi (fun i => D.halfLaw (hne i))) Fn ^ 2 ≤
      (FiniteLaw.pi (fun i => graphLaw D.G (hne i))).expect
        (fun y => Fn (fun i => D.halfL (y i)) * Fn (fun i => D.halfR (y i))) := by
  rw [D.block_cut_form hne Fn Fn]
  have hb0 : ∀ i, 0 ≤ cplus / p i := fun i => div_nonneg hcp (hp i).le
  have hgi0 : ∀ i, 0 ≤ g * (√(p i))⁻¹ := fun i =>
    mul_nonneg hg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  refine tensor_lower_sub (fun i => D.halfLaw (hne i)) (fun i x x' => D.cutK x x' / D.cutZ (hne i))
    (fun i x y => by rw [D.cutK_symm]) V (fun i => g * (√(p i))⁻¹) (fun i => cplus / p i) hb0 hgi0
    (fun i => by linarith [hgp i, hb0 i]) hlow hup (hgi0 default) (fun i => ?_) hF
  have he : (Finset.univ : Finset ι).erase i = ∅ := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.notMem_empty, iff_false,
      not_not]
    exact Subsingleton.elim j i
  rw [he, Finset.prod_empty, mul_one, Subsingleton.elim i default]

end SpecData

end Sarkozy.Cuts
