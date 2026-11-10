module

public import Sarkozy.ProbabilityProducts
public import Mathlib.LinearAlgebra.BilinearForm.Basic

@[expose] public section

/-!
# The coupled index and the signed index form

Paper labels: `def:hyb:coupled` (a)–(d) and `eq:record:expansion`
(`paper/sections/09_comparison_theorem.tex`, subsection "Queries and the
random interval-and-residue index").

The development is abstract in the following precise sense.

* The queries form an arbitrary finite type `E`; query `e` carries a finite
  nonempty index space `Ωe e`.  The paper's index space is the constant family
  `Ωe e = ZMod K × ZMod M₀` (interval coordinate `b_e` and residue `s_e`), and
  the index space `Ω = ∏ₑ Ωe e` carries the uniform law (`def:hyb:coupled`(a)).
  The Chinese-remainder splitting of `ZMod M₀` into prime-power coordinates
  (second sentence of (a)) is not formalized here; nothing below uses it.
* Slots form an arbitrary finite type `V` (the plus half `V₊` of the paper),
  labels an arbitrary type `H` (the paper's `G_N`). The two ends of the
  queries are given by maps `u w : E → V` (the paper's `u_e` and `ι v_e`);
  the mean identity needs them injective (pairwise disjoint endpoints).
  The slot functions are arbitrary `g : ∀ e, Ωe e → H → ℝ` and `F : H → ℝ`
  (in the paper, `g e (b,s) = g^{I_b,M₀,s}` and `F = F_A`).
* The transition `T_e` is an arbitrary kernel on `Ωe e`; the doubly stochastic
  property is a separate predicate (`DoublyStochastic`), used only where it
  is needed.  The specific transition of (c), the interval shift `b ↦ b+1`
  tensored with convolution by an arbitrary increment law on `ZMod M₀`, is
  defined in `shiftConvKernel` and proved doubly stochastic; `convKernel_crt`
  shows that for an increment combined by an additive isomorphism
  `ZMod M₀ ≃+ ∏_p ZMod p^{h_p}` from independent coordinate increments, the
  convolution is the tensor product of the coordinate convolutions.
* The cut form `Q_κ` is replaced by an arbitrary real bilinear form on the
  half-functions; `Q_κ` of `05_positivity.tex` is bilinear, and `Y_κ` is
  `Q_κ(X̄,X̄)` by the bilinear identity `eq:cc:bilinear`.  The operator
  expansion and the identity `I_{κ,∅} = Y_κ` hold for every bilinear form.
* Tensor products of kernels act on the index variable pointwise in the
  field labels (`kernelOp`), as stated in (d).

Main results: `prod_signedKernel` and `kernelOp_signed_expansion` (the
expansion of `𝒯 = ⊗ₑ(2Pₑ - Tₑ)`), `signedForm_expansion`
(`eq:record:expansion`, first identity), `expect_halfFunction` (`E X = X̄`),
`kernelOp_uniform` (`⊗ₑ Pₑ` is the full average), `coupledForm_empty`
(`I_{κ,∅} = Y_κ`) and `signedForm_eq` (both identities together); for (a)
and (c): `uniform_pi_eq_pi_uniform`, `expect_uniform_pi_prod`,
`expect_uniform_prod`, `shiftConvKernel_doublyStochastic`,
`kernelApply_shiftConv`, `convKernel_crt`, `uniformKernel_doublyStochastic`,
`expect_kernelOp` (doubly stochastic transitions keep the index uniform).
`cutForm` exhibits the paper's cut forms `Q_κ` as bilinear forms.

This file is new work for the paper; no upstream OpenAI file was adapted.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.Functional

/-! ### Kernels on one index space -/

section SingleKernel

variable {Ω : Type*} [Fintype Ω]

/-- The operator of a kernel on a finite index set:
`(K f)(t) = ∑ t', K t t' f t'`. -/
noncomputable def kernelApply (K : Ω → Ω → ℝ) (f : Ω → ℝ) (t : Ω) : ℝ :=
  ∑ t', K t t' * f t'

/-- A doubly stochastic kernel: nonnegative entries, unit row sums (a Markov
operator, fixing constants) and unit column sums (preserving the uniform
law). -/
structure DoublyStochastic (K : Ω → Ω → ℝ) : Prop where
  nonneg : ∀ t t', 0 ≤ K t t'
  row_sum : ∀ t, ∑ t', K t t' = 1
  col_sum : ∀ t', ∑ t, K t t' = 1

variable (Ω) in
/-- The kernel of the averaging operator `P_e` (`def:hyb:coupled`(c)). -/
noncomputable def uniformKernel (_t _t' : Ω) : ℝ := (Fintype.card Ω : ℝ)⁻¹

theorem uniformKernel_doublyStochastic [Nonempty Ω] :
    DoublyStochastic (uniformKernel Ω) := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _), fun _ => ?_, fun _ => ?_⟩ <;>
    simp [uniformKernel, hc]

/-- `P_e` averages over the whole index. -/
theorem kernelApply_uniform [Nonempty Ω] (f : Ω → ℝ) (t : Ω) :
    kernelApply (uniformKernel Ω) f t = (FiniteLaw.uniform Ω).expect f := by
  rw [FiniteLaw.expect_uniform]
  simp only [kernelApply, uniformKernel, ← Finset.mul_sum]
  ring

/-- A kernel with unit row sums fixes constants. -/
theorem kernelApply_const {K : Ω → Ω → ℝ} (hK : ∀ t, ∑ t', K t t' = 1) (c : ℝ) (t : Ω) :
    kernelApply K (fun _ => c) t = c := by
  simp only [kernelApply, ← Finset.sum_mul, hK, one_mul]

/-- A kernel with unit column sums preserves the uniform expectation. -/
theorem expect_kernelApply [Nonempty Ω] {K : Ω → Ω → ℝ} (hK : ∀ t', ∑ t, K t t' = 1)
    (f : Ω → ℝ) :
    (FiniteLaw.uniform Ω).expect (kernelApply K f) = (FiniteLaw.uniform Ω).expect f := by
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  simp only [kernelApply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hK, one_mul]

end SingleKernel

/-! ### The transition of `def:hyb:coupled`(c) -/

section ShiftConvolution

variable {K M : ℕ} [NeZero K] [NeZero M]

/-- The interval shift `b ↦ b + 1` on `ZMod K`, as a kernel. -/
noncomputable def shiftKernel (b b' : ZMod K) : ℝ := if b' = b + 1 then 1 else 0

/-- Convolution by the law `μ` of the increment `r`: `s ↦ s + r`, on any
finite additive group (in the paper, `ZMod M₀` or one of its prime-power
coordinates). -/
noncomputable def convKernel {A : Type*} [AddGroup A] [Fintype A] (μ : FiniteLaw A)
    (s s' : A) : ℝ :=
  μ.weight (s' - s)

/-- The transition `T_e` of `def:hyb:coupled`(c) on `Ω_e = ZMod K × ZMod M₀`:
the tensor product of the interval shift and the convolution by the
increment law `μ` (the law of the CRT combination `r_e` of the square
increments `r_{e,p}`; any law on `ZMod M₀` is allowed here). -/
noncomputable def shiftConvKernel (μ : FiniteLaw (ZMod M)) (ω ω' : ZMod K × ZMod M) : ℝ :=
  shiftKernel ω.1 ω'.1 * convKernel μ ω.2 ω'.2

theorem shiftKernel_doublyStochastic : DoublyStochastic (shiftKernel (K := K)) := by
  refine ⟨fun _ _ => by unfold shiftKernel; split <;> norm_num, fun b => ?_, fun b' => ?_⟩
  · simp [shiftKernel]
  · have h (b : ZMod K) : (b' = b + 1) ↔ b = b' - 1 := by
      constructor <;> intro h <;> subst h <;> ring
    simp only [shiftKernel, h]
    simp

theorem convKernel_doublyStochastic {A : Type*} [AddGroup A] [Fintype A]
    (μ : FiniteLaw A) : DoublyStochastic (convKernel μ) := by
  refine ⟨fun _ _ => μ.nonneg _, fun s => ?_, fun s' => ?_⟩
  · simp only [convKernel]
    rw [← μ.total]
    exact Fintype.sum_equiv (Equiv.subRight s) _ _ (fun _ => rfl)
  · simp only [convKernel]
    rw [← μ.total]
    exact Fintype.sum_equiv (Equiv.subLeft s') _ _ (fun _ => rfl)

/-- Product kernels of doubly stochastic kernels are doubly stochastic. -/
theorem DoublyStochastic.prod {α β : Type*} [Fintype α] [Fintype β]
    {K₁ : α → α → ℝ} {K₂ : β → β → ℝ} (h₁ : DoublyStochastic K₁)
    (h₂ : DoublyStochastic K₂) :
    DoublyStochastic (fun (ω ω' : α × β) => K₁ ω.1 ω'.1 * K₂ ω.2 ω'.2) := by
  refine ⟨fun ω ω' => mul_nonneg (h₁.nonneg _ _) (h₂.nonneg _ _), fun ω => ?_, fun ω' => ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, h₂.row_sum, mul_one, h₁.row_sum]
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, h₂.col_sum, mul_one, h₁.col_sum]

/-- "All the coordinate transitions are doubly stochastic" (`def:hyb:coupled`(c)). -/
theorem shiftConvKernel_doublyStochastic (μ : FiniteLaw (ZMod M)) :
    DoublyStochastic (shiftConvKernel (K := K) μ) :=
  DoublyStochastic.prod shiftKernel_doublyStochastic (convKernel_doublyStochastic μ)

/-- The Markov operator of the transition:
`T_e f(b,s) = E_r f(b+1, s+r)`. -/
theorem kernelApply_shiftConv (μ : FiniteLaw (ZMod M)) (f : ZMod K × ZMod M → ℝ)
    (b : ZMod K) (s : ZMod M) :
    kernelApply (shiftConvKernel μ) f (b, s) = μ.expect (fun r => f (b + 1, s + r)) := by
  unfold kernelApply FiniteLaw.expect
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (b + 1)]
  · simp only [shiftConvKernel, shiftKernel, convKernel, ↓reduceIte, one_mul]
    exact Fintype.sum_equiv (Equiv.subRight s) _ _ (fun s' => by simp)
  · intro b' _ hb'
    simp [shiftConvKernel, shiftKernel, hb']
  · simp

/-- The Chinese-remainder form of the convolution (`def:hyb:coupled`(c)):
if the increment is `r = φ⁻¹((r_p)_p)` for independent coordinate increments
`r_p ∼ ν_p` and an additive isomorphism `φ : A ≃+ ∏_p B_p` (for instance
`ZMod.prodEquivPi` for `ZMod M₀`), then the convolution kernel by `r` is the
tensor product of the coordinate convolution kernels. -/
theorem convKernel_crt {A : Type*} [AddGroup A] [Fintype A] [DecidableEq A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*} [∀ i, AddGroup (B i)]
    [∀ i, Fintype (B i)] (φ : A ≃+ (∀ i, B i)) (ν : ∀ i, FiniteLaw (B i)) (s s' : A) :
    convKernel ((FiniteLaw.pi ν).map φ.symm) s s' =
      ∏ i, convKernel (ν i) (φ s i) (φ s' i) := by
  simp only [convKernel, FiniteLaw.map, FiniteLaw.pi]
  rw [Finset.sum_eq_single (φ (s' - s))]
  · simp [map_sub]
  · intro ω _ hω
    have h : ¬ φ.symm ω = s' - s := by
      intro h
      apply hω
      rw [← h, AddEquiv.apply_symm_apply]
    simp only [h, ite_false]
  · simp

end ShiftConvolution

/-! ### Uniform expectations on the product index space -/

section UniformProduct

theorem expect_uniform_prod {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α × β → ℝ) :
    (FiniteLaw.uniform (α × β)).expect f =
      (FiniteLaw.uniform α).expect (fun a => (FiniteLaw.uniform β).expect (fun b => f (a, b))) := by
  simp only [FiniteLaw.expect_uniform, Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul,
    ← Finset.sum_div]
  rw [div_div, mul_comm (Fintype.card β : ℝ)]

/-- Two finite laws with the same weights are equal. -/
theorem finiteLaw_ext {Ω : Type*} [Fintype Ω] {μ ν : FiniteLaw Ω}
    (h : ∀ ω, μ.weight ω = ν.weight ω) : μ = ν := by
  cases μ
  cases ν
  have hw := funext h
  simp only at hw
  subst hw
  rfl

variable {E : Type*} [Fintype E] [DecidableEq E] {Ωe : E → Type*}
  [∀ e, Fintype (Ωe e)] [∀ e, Nonempty (Ωe e)]

/-- Independence of the coordinates of a uniform index: the expectation of a
product of functions of distinct coordinates is the product of their
expectations. -/
theorem expect_uniform_pi_prod (f : ∀ e, Ωe e → ℝ) :
    (FiniteLaw.uniform (∀ e, Ωe e)).expect (fun ω => ∏ e, f e (ω e)) =
      ∏ e, (FiniteLaw.uniform (Ωe e)).expect (f e) := by
  simp only [FiniteLaw.expect_uniform, Fintype.card_pi, Nat.cast_prod]
  rw [Finset.prod_div_distrib, Fintype.prod_sum]

/-- `def:hyb:coupled`(a): the uniform law on `Ω = ∏ₑ Ωₑ` is the law of
independent uniform coordinates. -/
theorem uniform_pi_eq_pi_uniform :
    FiniteLaw.uniform (∀ e, Ωe e) = FiniteLaw.pi (fun e => FiniteLaw.uniform (Ωe e)) := by
  apply finiteLaw_ext
  intro ω
  simp [FiniteLaw.uniform, FiniteLaw.pi, Fintype.card_pi, Finset.prod_inv_distrib]

end UniformProduct

/-! ### Tensor products of kernels on the index space -/

section Tensor

variable {E : Type*} [Fintype E] [DecidableEq E] {Ωe : E → Type*}
  [∀ e, Fintype (Ωe e)]

/-- The tensor product `⊗ₑ Kₑ` of kernels, acting on a function of the index
`ω = (ωₑ)ₑ`. Applied to half-functions it acts on the index variable, pointwise
in the field labels (`def:hyb:coupled`(d)). -/
noncomputable def kernelOp (K : ∀ e, Ωe e → Ωe e → ℝ) (Φ : (∀ e, Ωe e) → ℝ)
    (ω : ∀ e, Ωe e) : ℝ :=
  ∑ ω', (∏ e, K e (ω e) (ω' e)) * Φ ω'

/-- On product functions the tensor product acts factor by factor. -/
theorem kernelOp_prod (K : ∀ e, Ωe e → Ωe e → ℝ) (φ : ∀ e, Ωe e → ℝ) (ω : ∀ e, Ωe e) :
    kernelOp K (fun ω' => ∏ e, φ e (ω' e)) ω = ∏ e, kernelApply (K e) (φ e) (ω e) := by
  simp only [kernelOp, kernelApply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun e t => K e (ω e) t * φ e t)).symm

/-- The kernel of `⊗_{e∈S} Tₑ ⊗_{e∉S} Pₑ`. -/
noncomputable def mixedKernel (T : ∀ e, Ωe e → Ωe e → ℝ) (S : Finset E) (e : E) :
    Ωe e → Ωe e → ℝ :=
  if e ∈ S then T e else uniformKernel (Ωe e)

/-- The kernel of `2Pₑ - Tₑ`; the signed operator is `𝒯 = ⊗ₑ(2Pₑ - Tₑ)`. -/
noncomputable def signedKernel (T : ∀ e, Ωe e → Ωe e → ℝ) (e : E) (t t' : Ωe e) : ℝ :=
  2 * uniformKernel (Ωe e) t t' - T e t t'

/-- The kernel identity behind `eq:record:expansion`:
`∏ₑ(2Pₑ - Tₑ) = ∑_S (-1)^{|S|} 2^{k-|S|} ∏_{e∈S}Tₑ ∏_{e∉S}Pₑ`. -/
theorem prod_signedKernel (T : ∀ e, Ωe e → Ωe e → ℝ) (ω ω' : ∀ e, Ωe e) :
    ∏ e, signedKernel T e (ω e) (ω' e) =
      ∑ S : Finset E, (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
        ∏ e, mixedKernel T S e (ω e) (ω' e) := by
  have h := Fintype.prod_add (fun e => -T e (ω e) (ω' e))
    (fun e => 2 * uniformKernel (Ωe e) (ω e) (ω' e))
  simp only [signedKernel]
  simp only [neg_add_eq_sub] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro S _
  have hmix : ∏ e, mixedKernel T S e (ω e) (ω' e) =
      (∏ e ∈ S, T e (ω e) (ω' e)) * ∏ e ∈ Sᶜ, uniformKernel (Ωe e) (ω e) (ω' e) := by
    rw [← Finset.prod_mul_prod_compl S]
    congr 1
    · exact Finset.prod_congr rfl (fun e he => by simp [mixedKernel, he])
    · exact Finset.prod_congr rfl (fun e he => by
        simp [mixedKernel, Finset.mem_compl.mp he])
  rw [hmix, Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_compl]
  ring

/-- The operator expansion of `𝒯 = ⊗ₑ(2Pₑ - Tₑ)` (`def:hyb:coupled`(d)). -/
theorem kernelOp_signed_expansion (T : ∀ e, Ωe e → Ωe e → ℝ) (Φ : (∀ e, Ωe e) → ℝ)
    (ω : ∀ e, Ωe e) :
    kernelOp (signedKernel T) Φ ω =
      ∑ S : Finset E, (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
        kernelOp (mixedKernel T S) Φ ω := by
  simp only [kernelOp, prod_signedKernel, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro ω' _
  ring

/-- With no transitions, `⊗ₑ Pₑ` is the full uniform average over the index. -/
theorem kernelOp_uniform [∀ e, Nonempty (Ωe e)] (T : ∀ e, Ωe e → Ωe e → ℝ)
    (Φ : (∀ e, Ωe e) → ℝ) (ω : ∀ e, Ωe e) :
    kernelOp (mixedKernel T ∅) Φ ω = (FiniteLaw.uniform (∀ e, Ωe e)).expect Φ := by
  rw [FiniteLaw.expect_uniform]
  simp only [kernelOp, mixedKernel, Finset.notMem_empty, ite_false, uniformKernel,
    ← Finset.mul_sum]
  rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib, div_eq_inv_mul]

/-- Transitions with unit column sums preserve the uniform law of the index
(so the coupled index `ω'` is uniform when `ω` is). -/
theorem expect_kernelOp [∀ e, Nonempty (Ωe e)] {K : ∀ e, Ωe e → Ωe e → ℝ}
    (hK : ∀ e t', ∑ t, K e t t' = 1) (Φ : (∀ e, Ωe e) → ℝ) :
    (FiniteLaw.uniform (∀ e, Ωe e)).expect (kernelOp K Φ) =
      (FiniteLaw.uniform (∀ e, Ωe e)).expect Φ := by
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  simp only [kernelOp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω' _
  rw [← Finset.sum_mul]
  have h := Fintype.prod_sum (fun e t => K e t (ω' e))
  simp only [hK, Finset.prod_const_one] at h
  rw [← h, one_mul]

omit [Fintype E] in
/-- If every `Tₑ` is doubly stochastic, so is every coordinate of the mixed
kernels. -/
theorem mixedKernel_doublyStochastic [∀ e, Nonempty (Ωe e)] {T : ∀ e, Ωe e → Ωe e → ℝ}
    (hT : ∀ e, DoublyStochastic (T e)) (S : Finset E) (e : E) :
    DoublyStochastic (mixedKernel T S e) := by
  unfold mixedKernel
  split
  · exact hT e
  · exact uniformKernel_doublyStochastic

end Tensor

/-! ### Half-functions (`def:hyb:coupled`(b)) -/

section HalfFunctions

variable {E : Type*} [Fintype E] [DecidableEq E] {Ωe : E → Type*}
  [∀ e, Fintype (Ωe e)] {V : Type*} [Fintype V] [DecidableEq V] {H : Type*}

/-- The half-function carrying the indexed inputs at the query ends
(`def:hyb:coupled`(b)):
`halfFunction ends g F ω x = ∏ₑ g e (ωₑ) (x (ends e)) · ∏_{v ∉ ends(E)} F (x v)`.
With `ends = u` this is `X_ω`, with `ends = ι ∘ v` it is `Y_ω`. -/
noncomputable def halfFunction (ends : E → V) (g : ∀ e, Ωe e → H → ℝ) (F : H → ℝ)
    (ω : ∀ e, Ωe e) (x : V → H) : ℝ :=
  (∏ e, g e (ω e) (x (ends e))) * ∏ v ∈ (univ.image ends)ᶜ, F (x v)

/-- The unindexed half-function `X̄(x) = ∏_{v ∈ V₊} F(x_v)`. -/
noncomputable def fullHalf (F : H → ℝ) (x : V → H) : ℝ := ∏ v, F (x v)

/-- The mean identity `E X = X̄`: if every index averages its input to `F`
and the ends are distinct, the uniform average of the half-function over the
independent indices is `X̄` (`eq:record:expansion`, second identity). -/
theorem expect_halfFunction [∀ e, Nonempty (Ωe e)] {ends : E → V}
    (hends : Function.Injective ends) {g : ∀ e, Ωe e → H → ℝ} {F : H → ℝ}
    (hmean : ∀ e y, (FiniteLaw.uniform (Ωe e)).expect (fun t => g e t y) = F y)
    (x : V → H) :
    (FiniteLaw.uniform (∀ e, Ωe e)).expect (fun ω => halfFunction ends g F ω x) =
      fullHalf F x := by
  unfold halfFunction
  rw [(FiniteLaw.uniform (∀ e, Ωe e)).expect_mul_const (fun ω => ∏ e, g e (ω e) (x (ends e)))]
  have h := expect_uniform_pi_prod (fun e t => g e t (x (ends e)))
  simp only [hmean] at h
  rw [h, ← Finset.prod_image (f := fun v => F (x v)) (fun a _ b _ hab => hends hab)]
  exact Finset.prod_mul_prod_compl _ _

/-- `(⊗ₑ Pₑ Y)_ω = E Y = X̄` for every index `ω`. -/
theorem kernelOp_uniform_halfFunction [∀ e, Nonempty (Ωe e)] {ends : E → V}
    (hends : Function.Injective ends) {g : ∀ e, Ωe e → H → ℝ} {F : H → ℝ}
    (hmean : ∀ e y, (FiniteLaw.uniform (Ωe e)).expect (fun t => g e t y) = F y)
    (T : ∀ e, Ωe e → Ωe e → ℝ) (ω : ∀ e, Ωe e) (x : V → H) :
    kernelOp (mixedKernel T ∅) (fun ω' => halfFunction ends g F ω' x) ω = fullHalf F x := by
  rw [kernelOp_uniform, expect_halfFunction hends hmean]

end HalfFunctions

/-! ### The coupled forms and the signed index form (`def:hyb:coupled`(d)) -/

section Forms

/-- Finite expectations commute with finite sums. -/
theorem expect_finset_sum {Ω ι : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (s : Finset ι)
    (f : ι → Ω → ℝ) : μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  unfold FiniteLaw.expect
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- A bilinear form commutes with expectations in its first argument. -/
theorem expect_bilin_left {Z Ω : Type*} [Fintype Ω] (Q : LinearMap.BilinForm ℝ (Z → ℝ))
    (μ : FiniteLaw Ω) (X : Ω → Z → ℝ) (y : Z → ℝ) :
    μ.expect (fun ω => Q (X ω) y) = Q (fun x => μ.expect (fun ω => X ω x)) y := by
  have h : (fun x => μ.expect (fun ω => X ω x)) = ∑ ω, μ.weight ω • X ω := by
    funext x
    simp [FiniteLaw.expect, Finset.sum_apply]
  rw [h, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rfl

variable {E : Type*} [Fintype E] [DecidableEq E] {Ωe : E → Type*}
  [∀ e, Fintype (Ωe e)] [∀ e, Nonempty (Ωe e)]
  {V : Type*} [Fintype V] [DecidableEq V] {H : Type*}

/-- The coupled form
`I_{κ,S} = E_ω Q(X_ω, (⊗_{e∈S} Tₑ ⊗_{e∉S} Pₑ Y)_ω)` of `def:hyb:coupled`(d),
for an arbitrary bilinear form `Q` on half-functions in place of `Q_κ`. -/
noncomputable def coupledForm (Q : LinearMap.BilinForm ℝ ((V → H) → ℝ)) (u w : E → V)
    (g : ∀ e, Ωe e → H → ℝ) (F : H → ℝ) (T : ∀ e, Ωe e → Ωe e → ℝ) (S : Finset E) : ℝ :=
  (FiniteLaw.uniform (∀ e, Ωe e)).expect (fun ω =>
    Q (halfFunction u g F ω)
      (fun x => kernelOp (mixedKernel T S) (fun ω' => halfFunction w g F ω' x) ω))

/-- The signed index form `J_κ = E_ω Q(X_ω, (𝒯Y)_ω)`, `𝒯 = ⊗ₑ(2Pₑ - Tₑ)`
(`def:hyb:coupled`(d)). -/
noncomputable def signedForm (Q : LinearMap.BilinForm ℝ ((V → H) → ℝ)) (u w : E → V)
    (g : ∀ e, Ωe e → H → ℝ) (F : H → ℝ) (T : ∀ e, Ωe e → Ωe e → ℝ) : ℝ :=
  (FiniteLaw.uniform (∀ e, Ωe e)).expect (fun ω =>
    Q (halfFunction u g F ω)
      (fun x => kernelOp (signedKernel T) (fun ω' => halfFunction w g F ω' x) ω))

/-- `eq:record:expansion`, first identity:
`J_κ = ∑_{S ⊆ E} (-1)^{|S|} 2^{k-|S|} I_{κ,S}`, for every bilinear form and
every family of kernels. -/
theorem signedForm_expansion (Q : LinearMap.BilinForm ℝ ((V → H) → ℝ)) (u w : E → V)
    (g : ∀ e, Ωe e → H → ℝ) (F : H → ℝ) (T : ∀ e, Ωe e → Ωe e → ℝ) :
    signedForm Q u w g F T =
      ∑ S : Finset E, (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
        coupledForm Q u w g F T S := by
  unfold signedForm coupledForm
  have hfun (ω : ∀ e, Ωe e) :
      (fun x => kernelOp (signedKernel T) (fun ω' => halfFunction w g F ω' x) ω) =
        ∑ S : Finset E, ((-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card)) •
          (fun x => kernelOp (mixedKernel T S) (fun ω' => halfFunction w g F ω' x) ω) := by
    funext x
    rw [kernelOp_signed_expansion, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  simp only [hfun, map_sum, map_smul, smul_eq_mul]
  rw [expect_finset_sum]
  simp only [FiniteLaw.expect_const_mul]

/-- `eq:record:expansion`, second identity: `I_{κ,∅} = Y_κ`, where
`Y_κ = Q_κ(X̄, X̄)` by the bilinear identity `eq:cc:bilinear`. The hypotheses
are the per-query mean identity (`lem:twointerval`(iii) in the application)
and the distinctness of the ends `u_e`, respectively `ι v_e`. -/
theorem coupledForm_empty (Q : LinearMap.BilinForm ℝ ((V → H) → ℝ)) {u w : E → V}
    (hu : Function.Injective u) (hw : Function.Injective w)
    {g : ∀ e, Ωe e → H → ℝ} {F : H → ℝ}
    (hmean : ∀ e y, (FiniteLaw.uniform (Ωe e)).expect (fun t => g e t y) = F y)
    (T : ∀ e, Ωe e → Ωe e → ℝ) :
    coupledForm Q u w g F T ∅ = Q (fullHalf F) (fullHalf F) := by
  unfold coupledForm
  have hY (ω : ∀ e, Ωe e) :
      (fun x => kernelOp (mixedKernel T ∅) (fun ω' => halfFunction w g F ω' x) ω) =
        fullHalf F := by
    funext x
    exact kernelOp_uniform_halfFunction hw hmean T ω x
  simp only [hY]
  rw [expect_bilin_left]
  have hX : (fun x => (FiniteLaw.uniform (∀ e, Ωe e)).expect
      (fun ω => halfFunction u g F ω x)) = fullHalf F :=
    funext (fun x => expect_halfFunction hu hmean x)
  rw [hX]

/-- The two identities of `eq:record:expansion` together:
`J_κ = ∑_{S ≠ ∅} (-1)^{|S|} 2^{k-|S|} I_{κ,S} + 2^k Y_κ`. -/
theorem signedForm_eq (Q : LinearMap.BilinForm ℝ ((V → H) → ℝ)) {u w : E → V}
    (hu : Function.Injective u) (hw : Function.Injective w)
    {g : ∀ e, Ωe e → H → ℝ} {F : H → ℝ}
    (hmean : ∀ e y, (FiniteLaw.uniform (Ωe e)).expect (fun t => g e t y) = F y)
    (T : ∀ e, Ωe e → Ωe e → ℝ) :
    signedForm Q u w g F T =
      ∑ S ∈ univ.erase (∅ : Finset E), (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
        coupledForm Q u w g F T S +
      2 ^ Fintype.card E * Q (fullHalf F) (fullHalf F) := by
  rw [signedForm_expansion, ← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset E)),
    coupledForm_empty Q hu hw hmean T]
  simp

/-- The cut form of a finite signed weight: `Q(X,Y) = ∑_{x,y} X(x) C(x,y) Y(y)`.
The paper's `Q_κ(X,Y) = ⟨X, C_ϑ(κ)Y⟩` (`05_positivity.tex`) is `cutForm` of the
cut matrix `C_ϑ(κ)`, so every statement above applies to it. -/
noncomputable def cutForm {Z : Type*} [Fintype Z] (C : Z → Z → ℝ) :
    LinearMap.BilinForm ℝ (Z → ℝ) :=
  LinearMap.mk₂ ℝ (fun X Y => ∑ x, ∑ y, X x * C x y * Y y)
    (fun X₁ X₂ Y => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c X Y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring)))
    (fun X Y₁ Y₂ => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c X Y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring)))

theorem cutForm_apply {Z : Type*} [Fintype Z] (C : Z → Z → ℝ) (X Y : Z → ℝ) :
    cutForm C X Y = ∑ x, ∑ y, X x * C x y * Y y := rfl

end Forms

end Sarkozy.Functional
