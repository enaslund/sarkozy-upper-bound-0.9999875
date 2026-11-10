module

public import Sarkozy.Cuts.Schur

/-!
# Cuts, VIII′: the tensor spectrum bound (`lem:spec:tensorcomp` (a), (b))

`13_cuts_correlations.tex`, `lem:spec:tensorcomp` (a), (b). Let `(Ω_i, μ_i)` be finite probability
spaces with full support, and let `C_i` be the self-adjoint operator on `L²(μ_i)` with the
symmetric kernel `c_i` relative to `μ_i ⊗ μ_i`. Suppose its spectrum lies in `[-g_i, 1 + b_i]`,
stated as the numerical-range bound `-g_i ‖f‖² ≤ ⟨f, C_i f⟩ ≤ (1 + b_i) ‖f‖²`, with `b_i ≥ 0` and
`0 ≤ g_i ≤ 1 + b_i`. The tensor product `⊗_i C_i` on `L²(⊗_i μ_i)` has the kernel
`∏_i c_i(a_i, b_i)`.

* `tensor_lower`: `⊗_i C_i ⪰ -M I` whenever `M ≥ g_i ∏_{j ≠ i} (1 + b_j)` for every `i`; with
  `tensorcomp_scalar` this also gives `⪰ -(max_i g_i) exp(∑_i b_i) I`.

The proof avoids eigenvalues. Write `C_i = (a_i L⁻_i - g_i L⁺_i)/w_i` and `I = (L⁻_i + L⁺_i)/w_i`,
where `L⁻_i = C_i + g_i ⪰ 0`, `L⁺_i = a_i - C_i ⪰ 0`, `a_i = 1 + b_i` and `w_i = a_i + g_i`.
Expanding the products, `⊗_i C_i + M` is a combination of the positive semidefinite tensors
`⊗_i L^{±}_i` (Schur product theorem). The coefficients are `∏_i v_i + M ≥ 0`, where `v_i` runs
over the vertices `a_i`, `-g_i` of the box.

* `tensorcomp_block`: (b), first statement, for the caps `-g p^{-1/2} ≤ T_p ≤ 1 + c⁺/p`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Matrix

/-- A real symmetric kernel with nonnegative quadratic form (a positive semidefinite matrix). -/
def QuadNonneg {T : Type*} [Fintype T] (k : T → T → ℝ) : Prop :=
  (∀ x y, k x y = k y x) ∧ ∀ v : T → ℝ, 0 ≤ ∑ x, ∑ y, v x * k x y * v y

theorem QuadNonneg.posSemidef {T : Type*} [Fintype T] {k : T → T → ℝ} (h : QuadNonneg k) :
    (Matrix.of k).PosSemidef :=
  posSemidef_of_quad (fun i j => by simp only [Matrix.of_apply]; exact h.1 i j) h.2

theorem QuadNonneg.of_posSemidef {T : Type*} [Fintype T] {k : T → T → ℝ}
    (h : (Matrix.of k).PosSemidef) : QuadNonneg k := by
  refine ⟨fun x y => ?_, fun v => quad_nonneg_of_posSemidef h v⟩
  have := h.1.apply x y
  simp only [Matrix.of_apply, star_trivial] at this
  exact this.symm

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
  [∀ i, DecidableEq (Ω i)]

/-- Pulling a positive semidefinite kernel back along a coordinate keeps it positive
semidefinite. -/
theorem QuadNonneg.pullback {i : ι} {k : Ω i → Ω i → ℝ} (h : QuadNonneg k) :
    QuadNonneg (fun a b : (∀ j, Ω j) => k (a i) (b i)) := by
  classical
  refine ⟨fun a b => h.1 _ _, fun v => ?_⟩
  set V : Ω i → ℝ := fun x => ∑ a ∈ Finset.univ.filter (fun a : (∀ j, Ω j) => a i = x), v a
  have key : ∑ a, ∑ b, v a * k (a i) (b i) * v b = ∑ x, ∑ y, V x * k x y * V y := by
    symm
    calc ∑ x, ∑ y, V x * k x y * V y
        = ∑ x, ∑ a ∈ Finset.univ.filter (fun a : (∀ j, Ω j) => a i = x),
            ∑ y, ∑ b ∈ Finset.univ.filter (fun b : (∀ j, Ω j) => b i = y),
              v a * k (a i) (b i) * v b := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp only [V, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
          rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]
      _ = ∑ a, ∑ y, ∑ b ∈ Finset.univ.filter (fun b : (∀ j, Ω j) => b i = y),
            v a * k (a i) (b i) * v b :=
          Finset.sum_fiberwise Finset.univ (fun a : (∀ j, Ω j) => a i)
            (fun a => ∑ y, ∑ b ∈ Finset.univ.filter (fun b : (∀ j, Ω j) => b i = y),
              v a * k (a i) (b i) * v b)
      _ = ∑ a, ∑ b, v a * k (a i) (b i) * v b := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          exact Finset.sum_fiberwise Finset.univ (fun b : (∀ j, Ω j) => b i)
            (fun b => v a * k (a i) (b i) * v b)
  rw [key]
  exact h.2 V

omit [∀ i, DecidableEq (Ω i)] in
theorem quadNonneg_one : QuadNonneg (fun _ _ : (∀ j, Ω j) => (1 : ℝ)) := by
  refine ⟨fun _ _ => rfl, fun v => ?_⟩
  have : ∑ x, ∑ y, v x * (1 : ℝ) * v y = (∑ x, v x) ^ 2 := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]
  exact sq_nonneg _

/-- Tensor products of positive semidefinite kernels are positive semidefinite. -/
theorem QuadNonneg.prod (s : Finset ι) (m : ∀ i, Ω i → Ω i → ℝ)
    (hm : ∀ i ∈ s, QuadNonneg (m i)) :
    QuadNonneg (fun a b : (∀ j, Ω j) => ∏ i ∈ s, m i (a i) (b i)) := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact quadNonneg_one
  | insert j s hj ih =>
      have h1 := (hm j (Finset.mem_insert_self j s)).pullback (Ω := Ω)
      have h2 := ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))
      have hh := (h1.posSemidef).hadamard h2.posSemidef
      have e : (Matrix.of fun a b : (∀ j, Ω j) => m j (a j) (b j)) ⊙
          (Matrix.of fun a b : (∀ j, Ω j) => ∏ i ∈ s, m i (a i) (b i)) =
          Matrix.of fun a b : (∀ j, Ω j) => ∏ i ∈ insert j s, m i (a i) (b i) := by
        ext a b
        simp only [hadamard_apply, Matrix.of_apply, Finset.prod_insert hj]
      rw [e] at hh
      exact QuadNonneg.of_posSemidef hh

/-- The vertex coefficients `∏_{i∈S} a_i ∏_{i∉S} (-g_i) + M` are nonnegative. -/
theorem vertex_coeff_nonneg (a g : ι → ℝ) (hg0 : ∀ i, 0 ≤ g i) (hga : ∀ i, g i ≤ a i)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, g i * ∏ j ∈ Finset.univ.erase i, a j ≤ M)
    (S : Finset ι) :
    0 ≤ (∏ i ∈ S, a i) * (∏ i ∈ Finset.univ \ S, (-g i)) + M := by
  have ha0 : ∀ i, 0 ≤ a i := fun i => (hg0 i).trans (hga i)
  by_cases hS : Finset.univ \ S = ∅
  · rw [hS, Finset.prod_empty, mul_one]
    exact add_nonneg (Finset.prod_nonneg (fun i _ => ha0 i)) hM0
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have habs : |(∏ i ∈ S, a i) * (∏ i ∈ Finset.univ \ S, (-g i))| ≤
        g i₀ * ∏ j ∈ Finset.univ.erase i₀, a j := by
      rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
      simp only [abs_neg]
      rw [← Finset.mul_prod_erase (Finset.univ \ S) _ hi₀]
      have hS' : S ⊆ Finset.univ.erase i₀ := fun x hx => Finset.mem_erase.mpr
        ⟨fun h => (Finset.mem_sdiff.mp hi₀).2 (h ▸ hx), Finset.mem_univ _⟩
      have hsplit : ∏ j ∈ Finset.univ.erase i₀, a j =
          (∏ j ∈ S, a j) * ∏ j ∈ (Finset.univ.erase i₀) \ S, a j := by
        rw [← Finset.prod_sdiff hS', mul_comm]
      have hsub : (Finset.univ \ S).erase i₀ = (Finset.univ.erase i₀) \ S := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and]
        tauto
      rw [hsplit, hsub, abs_of_nonneg (hg0 i₀)]
      have h1 : ∏ x ∈ S, |a x| = ∏ x ∈ S, a x :=
        Finset.prod_congr rfl (fun x _ => abs_of_nonneg (ha0 x))
      have h2 : ∏ x ∈ (Finset.univ.erase i₀) \ S, |g x| ≤ ∏ x ∈ (Finset.univ.erase i₀) \ S, a x :=
        Finset.prod_le_prod₀ (fun x _ => abs_nonneg _)
          (fun x _ => by rw [abs_of_nonneg (hg0 x)]; exact hga x)
      rw [h1]
      have hP : 0 ≤ ∏ x ∈ S, a x := Finset.prod_nonneg (fun x _ => ha0 x)
      have hQ : 0 ≤ ∏ x ∈ (Finset.univ.erase i₀) \ S, |g x| :=
        Finset.prod_nonneg (fun x _ => abs_nonneg _)
      calc (∏ x ∈ S, a x) * (g i₀ * ∏ x ∈ (Finset.univ.erase i₀) \ S, |g x|)
          ≤ (∏ x ∈ S, a x) * (g i₀ * ∏ x ∈ (Finset.univ.erase i₀) \ S, a x) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (hg0 i₀)) hP
        _ = g i₀ * ((∏ x ∈ S, a x) * ∏ x ∈ (Finset.univ.erase i₀) \ S, a x) := by ring
    have := hM i₀
    linarith [neg_abs_le ((∏ i ∈ S, a i) * (∏ i ∈ Finset.univ \ S, (-g i)))]

/-- The identity kernel of `L²(μ)` relative to `μ ⊗ μ`. -/
noncomputable def idKernel {T : Type*} [Fintype T] [DecidableEq T] (μ : FiniteLaw T) (x y : T) :
    ℝ :=
  if x = y then 1 / μ.weight x else 0

/-- A kernel with nonnegative form on `L²(μ)` (full support) is a positive semidefinite matrix. -/
theorem quadNonneg_of_form {T : Type*} [Fintype T] (μ : FiniteLaw T) (hμ : ∀ x, 0 < μ.weight x)
    (k : T → T → ℝ) (hsym : ∀ x y, k x y = k y x) (hk : ∀ f, 0 ≤ kernelForm μ μ k f f) :
    QuadNonneg k := by
  refine ⟨hsym, fun v => ?_⟩
  have h := hk (fun x => v x / μ.weight x)
  rw [kernelForm_quad] at h
  refine le_of_le_of_eq h (Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_)))
  have h1 : μ.weight x * (v x / μ.weight x) = v x := by field_simp [(hμ x).ne']
  have h2 : μ.weight y * (v y / μ.weight y) = v y := by field_simp [(hμ y).ne']
  rw [h1, h2]

theorem kernelForm_idKernel {T : Type*} [Fintype T] [DecidableEq T] (μ : FiniteLaw T)
    (hμ : ∀ x, 0 < μ.weight x) (f h : T → ℝ) :
    kernelForm μ μ (idKernel μ) f h = ip μ f h := by
  simp only [kernelForm, LinearMap.mk₂_apply, idKernel, ip, FiniteLaw.expect]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  field_simp [(hμ x).ne']

/-- **`lem:spec:tensorcomp` (a).** If `-g_i ‖f‖² ≤ ⟨f, C_i f⟩ ≤ (1 + b_i)‖f‖²` with `b_i ≥ 0` and
`0 ≤ g_i ≤ 1 + b_i`, then `⟨F, (⊗_i C_i) F⟩ ≥ -M ‖F‖²` whenever
`M ≥ g_i ∏_{j ≠ i} (1 + b_j)` for all `i`. -/
theorem tensor_lower (μ : ∀ i, FiniteLaw (Ω i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (c : ∀ i, Ω i → Ω i → ℝ) (hcs : ∀ i x y, c i x y = c i y x) (g b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hg0 : ∀ i, 0 ≤ g i) (hgb : ∀ i, g i ≤ 1 + b i)
    (hlow : ∀ i f, -g i * nrm (μ i) f ^ 2 ≤ kernelForm (μ i) (μ i) (c i) f f)
    (hup : ∀ i f, kernelForm (μ i) (μ i) (c i) f f ≤ (1 + b i) * nrm (μ i) f ^ 2)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, g i * ∏ j ∈ Finset.univ.erase i, (1 + b j) ≤ M)
    (Fn : (∀ i, Ω i) → ℝ) :
    -M * nrm (FiniteLaw.pi μ) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun x y => ∏ i, c i (x i) (y i)) Fn Fn := by
  classical
  set a : ι → ℝ := fun i => 1 + b i
  set w : ι → ℝ := fun i => a i + g i
  have hw : ∀ i, 0 < w i := fun i => by
    simp only [w, a]
    linarith [hb0 i, hg0 i]
  -- the two positive parts
  set Lm : ∀ i, Ω i → Ω i → ℝ := fun i x y => c i x y + g i * idKernel (μ i) x y
  set Lp : ∀ i, Ω i → Ω i → ℝ := fun i x y => a i * idKernel (μ i) x y - c i x y
  have hidsym : ∀ i (x y : Ω i), idKernel (μ i) x y = idKernel (μ i) y x := by
    intro i x y
    unfold idKernel
    by_cases h : x = y
    · subst h; rfl
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  have hLm : ∀ i, QuadNonneg (Lm i) := by
    intro i
    refine quadNonneg_of_form (μ i) (hμ i) (Lm i) (fun x y => ?_) (fun f => ?_)
    · simp only [Lm, hcs i x y, hidsym i x y]
    · have e : kernelForm (μ i) (μ i) (Lm i) f f = kernelForm (μ i) (μ i) (c i) f f +
          g i * kernelForm (μ i) (μ i) (idKernel (μ i)) f f := by
        simp only [kernelForm, LinearMap.mk₂_apply, Lm, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
      rw [e, kernelForm_idKernel (μ i) (hμ i), ← nrm_sq_eq]
      linarith [hlow i f]
  have hLp : ∀ i, QuadNonneg (Lp i) := by
    intro i
    refine quadNonneg_of_form (μ i) (hμ i) (Lp i) (fun x y => ?_) (fun f => ?_)
    · simp only [Lp, hcs i x y, hidsym i x y]
    · have e : kernelForm (μ i) (μ i) (Lp i) f f =
          a i * kernelForm (μ i) (μ i) (idKernel (μ i)) f f -
            kernelForm (μ i) (μ i) (c i) f f := by
        simp only [kernelForm, LinearMap.mk₂_apply, Lp, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
      rw [e, kernelForm_idKernel (μ i) (hμ i), ← nrm_sq_eq]
      linarith [hup i f]
  -- the kernel identity
  have hc : ∀ i (x y : Ω i), c i x y = (a i * Lm i x y + (-g i) * Lp i x y) / w i := by
    intro i x y
    rw [eq_div_iff (hw i).ne']
    simp only [Lm, Lp, w]
    ring
  have hid : ∀ i (x y : Ω i), idKernel (μ i) x y = (Lm i x y + Lp i x y) / w i := by
    intro i x y
    rw [eq_div_iff (hw i).ne']
    simp only [Lm, Lp, w]
    ring
  -- the expansion over vertices
  have hexp : ∀ x y : (∀ i, Ω i), (∏ i, c i (x i) (y i)) + M * ∏ i, idKernel (μ i) (x i) (y i) =
      (∏ i, (w i)⁻¹) * ∑ S ∈ (Finset.univ : Finset ι).powerset,
        ((∏ i ∈ S, a i) * (∏ i ∈ Finset.univ \ S, (-g i)) + M) *
          ((∏ i ∈ S, Lm i (x i) (y i)) * ∏ i ∈ Finset.univ \ S, Lp i (x i) (y i)) := by
    intro x y
    have h1 : ∏ i, c i (x i) (y i) = (∏ i, (w i)⁻¹) *
        ∏ i, (a i * Lm i (x i) (y i) + (-g i) * Lp i (x i) (y i)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [hc]; field_simp [(hw i).ne'])
    have h2 : ∏ i, idKernel (μ i) (x i) (y i) = (∏ i, (w i)⁻¹) *
        ∏ i, (Lm i (x i) (y i) + Lp i (x i) (y i)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [hid]; field_simp [(hw i).ne'])
    rw [h1, h2, Finset.prod_add, Finset.prod_add, mul_left_comm M, ← mul_add, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  -- the quadratic forms
  set ν := FiniteLaw.pi μ
  have hνw : ∀ x : (∀ i, Ω i), ν.weight x = ∏ i, (μ i).weight (x i) := fun x => rfl
  have hidpi : ∀ x y : (∀ i, Ω i), ∏ i, idKernel (μ i) (x i) (y i) = idKernel ν x y := by
    intro x y
    unfold idKernel
    by_cases hxy : x = y
    · subst hxy
      rw [ite_eq_left rfl, Finset.prod_congr rfl (fun i _ => ite_eq_left rfl),
        Finset.prod_div_distrib, Finset.prod_const_one, hνw]
    · rw [ite_eq_right hxy]
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra h
        push Not at h
        exact hxy (funext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  have hνpos : ∀ x, 0 < ν.weight x := fun x => by
    rw [hνw]
    exact Finset.prod_pos (fun i _ => hμ i (x i))
  have hnorm : M * nrm ν Fn ^ 2 = kernelForm ν ν (fun x y => M * ∏ i, idKernel (μ i) (x i) (y i))
      Fn Fn := by
    have e : (fun x y : (∀ i, Ω i) => M * ∏ i, idKernel (μ i) (x i) (y i)) =
        fun x y => M * idKernel ν x y := by
      funext x y
      rw [hidpi]
    rw [e, nrm_sq_eq, ← kernelForm_idKernel ν hνpos]
    simp only [kernelForm, LinearMap.mk₂_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
  set κ : Finset ι → ℝ := fun S => (∏ i ∈ S, a i) * (∏ i ∈ Finset.univ \ S, (-g i)) + M with hκ
  set K : Finset ι → (∀ i, Ω i) → (∀ i, Ω i) → ℝ := fun S x y =>
    (∏ i ∈ S, Lm i (x i) (y i)) * ∏ i ∈ Finset.univ \ S, Lp i (x i) (y i) with hK
  set Wc := ∏ i, (w i)⁻¹
  have hsum : kernelForm ν ν (fun x y => ∏ i, c i (x i) (y i)) Fn Fn + M * nrm ν Fn ^ 2 =
      Wc * ∑ S ∈ (Finset.univ : Finset ι).powerset,
        κ S * ∑ x, ∑ y, (ν.weight x * Fn x) * K S x y * (ν.weight y * Fn y) := by
    rw [hnorm, kernelForm_quad, kernelForm_quad, ← Finset.sum_add_distrib]
    have step1 : ∀ x, (∑ y, (ν.weight x * Fn x) * (∏ i, c i (x i) (y i)) * (ν.weight y * Fn y)) +
        (∑ y, (ν.weight x * Fn x) * (M * ∏ i, idKernel (μ i) (x i) (y i)) * (ν.weight y * Fn y)) =
        ∑ y, ∑ S ∈ (Finset.univ : Finset ι).powerset,
          Wc * (κ S * ((ν.weight x * Fn x) * K S x y * (ν.weight y * Fn y))) := by
      intro x
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      have h := hexp x y
      have e : (ν.weight x * Fn x) * (∏ i, c i (x i) (y i)) * (ν.weight y * Fn y) +
          (ν.weight x * Fn x) * (M * ∏ i, idKernel (μ i) (x i) (y i)) * (ν.weight y * Fn y) =
          (ν.weight x * Fn x) * ((∏ i, c i (x i) (y i)) + M * ∏ i, idKernel (μ i) (x i) (y i)) *
            (ν.weight y * Fn y) := by ring
      rw [e, h]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      ring
    simp only [step1]
    rw [Finset.mul_sum]
    simp only [Finset.mul_sum]
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have hterm : ∀ S ∈ (Finset.univ : Finset ι).powerset,
      0 ≤ κ S * ∑ x, ∑ y, (ν.weight x * Fn x) * K S x y * (ν.weight y * Fn y) := by
    intro S _
    refine mul_nonneg (vertex_coeff_nonneg a g hg0 hgb hM0 hM S) ?_
    have hq := (QuadNonneg.prod Finset.univ (fun i => if i ∈ S then Lm i else Lp i)
      (fun i _ => by
        by_cases hi : i ∈ S
        · simp only [hi, ite_true]; exact hLm i
        · simp only [hi, ite_false]; exact hLp i)).2 (fun x => ν.weight x * Fn x)
    refine le_of_le_of_eq hq (Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_)))
    have e : ∏ i, (if i ∈ S then Lm i else Lp i) (x i) (y i) = K S x y := by
      rw [← Finset.prod_sdiff (Finset.subset_univ S), mul_comm]
      simp only [K]
      congr 1
      · exact Finset.prod_congr rfl (fun i hi => by simp only [hi, ite_true])
      · exact Finset.prod_congr rfl (fun i hi => by
          simp only [(Finset.mem_sdiff.mp hi).2, ite_false])
    show ν.weight x * Fn x * (∏ i, (if i ∈ S then Lm i else Lp i) (x i) (y i)) *
      (ν.weight y * Fn y) = _
    rw [e]
  have hwpos : 0 ≤ Wc := Finset.prod_nonneg (fun i _ => (inv_pos.mpr (hw i)).le)
  have := mul_nonneg hwpos (Finset.sum_nonneg hterm)
  rw [← hsum] at this
  linarith

end Tensor

/-- **`lem:spec:tensorcomp` (b), first statement.** For `-g p^{-1/2} ⪯ T_p ⪯ (1 + c⁺/p)` with
`g p^{-1/2} < 1` at every prime `p` of a block `B` with `p ≥ b`:
`⊗_p T_p ⪰ -(g/√b) ∏_p (1 + c⁺/p) I`. -/
theorem tensorcomp_block {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)] (μ : ∀ i, FiniteLaw (Ω i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (c : ∀ i, Ω i → Ω i → ℝ) (hcs : ∀ i x y, c i x y = c i y x)
    (p : ι → ℝ) {g cplus bmin : ℝ} (hg : 0 ≤ g) (hcp : 0 ≤ cplus) (hb : 0 < bmin)
    (hpb : ∀ i, bmin ≤ p i) (hgp : ∀ i, g * (√(p i))⁻¹ < 1)
    (hlow : ∀ i f, -(g * (√(p i))⁻¹) * nrm (μ i) f ^ 2 ≤ kernelForm (μ i) (μ i) (c i) f f)
    (hup : ∀ i f, kernelForm (μ i) (μ i) (c i) f f ≤ (1 + cplus / p i) * nrm (μ i) f ^ 2)
    (Fn : (∀ i, Ω i) → ℝ) :
    -(g * (√bmin)⁻¹ * ∏ i, (1 + cplus / p i)) * nrm (FiniteLaw.pi μ) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun x y => ∏ i, c i (x i) (y i)) Fn Fn := by
  have hp0 : ∀ i, 0 < p i := fun i => lt_of_lt_of_le hb (hpb i)
  have hb0 : ∀ i, 0 ≤ cplus / p i := fun i => div_nonneg hcp (hp0 i).le
  have hgi0 : ∀ i, 0 ≤ g * (√(p i))⁻¹ := fun i =>
    mul_nonneg hg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hgle : ∀ i, g * (√(p i))⁻¹ ≤ g * (√bmin)⁻¹ := fun i =>
    mul_le_mul_of_nonneg_left (inv_anti₀ (Real.sqrt_pos.mpr hb) (Real.sqrt_le_sqrt (hpb i))) hg
  refine tensor_lower μ hμ c hcs (fun i => g * (√(p i))⁻¹) (fun i => cplus / p i) hb0 hgi0
    (fun i => by linarith [hgp i, hb0 i]) hlow hup ?_ (fun i => ?_) Fn
  · exact mul_nonneg (mul_nonneg hg (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      (Finset.prod_nonneg (fun i _ => by linarith [hb0 i]))
  · exact (tensorcomp_scalar Finset.univ (fun i => cplus / p i) (fun i _ => hb0 i)
      (Finset.mem_univ i) (hgi0 i) (hgle i)).1

end Sarkozy.Cuts
