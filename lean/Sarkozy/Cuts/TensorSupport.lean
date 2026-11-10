module

public import Sarkozy.Cuts.TensorSpectrum
public import Sarkozy.Cuts.CutBlock

/-!
# Cuts, VIII″: the tensor bound without full support, and the block cut operators

`13_cuts_correlations.tex`, `lem:spec:tensorcomp` (b), for spectral data with `𝒱_p = L²(μ_p)`.
The half law `μ_p` is supported on `I⁺`. So `tensor_lower` (full support) is first transferred to
laws with arbitrary support, by restricting every factor to its support (`restrictLaw`).

* `sum_supp`, `sum_pi_supp`: sums against a law (or a product law) only see its support.
* `tensor_lower_gen`: `lem:spec:tensorcomp` (a) for factor laws of arbitrary support.
* `block_cut_lower`: `lem:spec:tensorcomp` (b) for spectral data. If at every prime of a block
  (`p ≥ b`) the cut operator satisfies `-g p^{-1/2} ⪯ A_p ⪯ 1 + c⁺/p` on `L²(μ_p)`, then
  `E_{λ_B(G)}[F(x) F(x')] ≥ -(g/√b) ∏_p (1 + c⁺/p) ‖F‖²_{μ_B}`.

The compression to proper subspaces `𝒱_p ⊊ L²(μ_p)` is `Sarkozy.Cuts.SpecData.block_cut_lower_sub`
(in `Sarkozy.Cuts.TensorSubspace`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Labellings

section Supp

/-- The support of a law, as a type. -/
abbrev Supp {T : Type*} [Fintype T] (μ : FiniteLaw T) := {x : T // 0 < μ.weight x}

/-- Sums against a law only see its support. -/
theorem sum_supp {T : Type*} [Fintype T] (μ : FiniteLaw T) (G : T → ℝ) :
    ∑ a : Supp μ, μ.weight a.1 * G a.1 = ∑ x, μ.weight x * G x := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x => 0 < μ.weight x))
    (fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun x => μ.weight x * G x)]
  refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
  have h0 : μ.weight x = 0 := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
    exact le_antisymm hx (μ.nonneg x)
  rw [h0, zero_mul]

/-- The restriction of a law to its support (full support). -/
noncomputable def restrictLaw {T : Type*} [Fintype T] (μ : FiniteLaw T) : FiniteLaw (Supp μ) where
  weight x := μ.weight x.1
  nonneg x := le_of_lt x.2
  total := by
    have := sum_supp μ (fun _ => 1)
    simp only [mul_one] at this
    rw [this, μ.total]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
  [∀ i, DecidableEq (Ω i)]

omit [∀ i, DecidableEq (Ω i)] in
/-- Sums against a product law only see the product of the supports. -/
theorem sum_pi_supp (μ : ∀ i, FiniteLaw (Ω i)) (G : (∀ i, Ω i) → ℝ) :
    ∑ z : (∀ i, Supp (μ i)), (∏ i, (μ i).weight (z i).1) * G (fun i => (z i).1) =
      ∑ x, (∏ i, (μ i).weight (x i)) * G x := by
  classical
  set T := Finset.univ.filter (fun x : (∀ i, Ω i) => ∀ i, 0 < (μ i).weight (x i))
  have h1 : ∑ x ∈ T, (∏ i, (μ i).weight (x i)) * G x = ∑ x, (∏ i, (μ i).weight (x i)) * G x := by
    refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_lt] at hx
    obtain ⟨i, hi⟩ := hx
    have h0 : (μ i).weight (x i) = 0 := le_antisymm hi ((μ i).nonneg _)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]
  rw [← h1]
  symm
  refine Finset.sum_bij' (fun x hx => fun i => ⟨x i, (Finset.mem_filter.mp hx).2 i⟩)
    (fun z _ => fun i => (z i).1) ?_ ?_ ?_ ?_ ?_
  · intro x _
    exact Finset.mem_univ _
  · intro z _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (z i).2⟩
  · intro x _
    rfl
  · intro z _
    rfl
  · intro x _
    rfl

omit [∀ i, DecidableEq (Ω i)] in
/-- The tensor form only sees the product of the supports. -/
theorem kernelForm_pi_supp (μ : ∀ i, FiniteLaw (Ω i)) (C : (∀ i, Ω i) → (∀ i, Ω i) → ℝ)
    (Fn Hn : (∀ i, Ω i) → ℝ) :
    kernelForm (FiniteLaw.pi (fun i => restrictLaw (μ i))) (FiniteLaw.pi (fun i => restrictLaw (μ i)))
        (fun z z' => C (fun i => (z i).1) (fun i => (z' i).1))
        (fun z => Fn (fun i => (z i).1)) (fun z => Hn (fun i => (z i).1)) =
      kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) C Fn Hn := by
  simp only [kernelForm, LinearMap.mk₂_apply]
  have e1 : ∀ z : (∀ i, Supp (μ i)), ∑ z' : (∀ i, Supp (μ i)),
      (FiniteLaw.pi (fun i => restrictLaw (μ i))).weight z *
        (FiniteLaw.pi (fun i => restrictLaw (μ i))).weight z' * Fn (fun i => (z i).1) *
          C (fun i => (z i).1) (fun i => (z' i).1) * Hn (fun i => (z' i).1) =
      (∏ i, (μ i).weight (z i).1) * ∑ y, (∏ i, (μ i).weight (y i)) *
        (Fn (fun i => (z i).1) * C (fun i => (z i).1) y * Hn y) := by
    intro z
    rw [← sum_pi_supp μ (fun y => Fn (fun i => (z i).1) * C (fun i => (z i).1) y * Hn y),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z' _ => ?_)
    change (∏ i, (μ i).weight (z i).1) * (∏ i, (μ i).weight (z' i).1) * _ * _ * _ = _
    ring
  simp only [e1]
  rw [sum_pi_supp μ (fun x => ∑ y, (∏ i, (μ i).weight (y i)) * (Fn x * C x y * Hn y))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  change _ = (∏ i, (μ i).weight (x i)) * (∏ i, (μ i).weight (y i)) * Fn x * C x y * Hn y
  ring

omit [∀ i, DecidableEq (Ω i)] in
theorem nrm_pi_supp (μ : ∀ i, FiniteLaw (Ω i)) (Fn : (∀ i, Ω i) → ℝ) :
    nrm (FiniteLaw.pi (fun i => restrictLaw (μ i))) (fun z => Fn (fun i => (z i).1)) =
      nrm (FiniteLaw.pi μ) Fn := by
  unfold nrm ip
  congr 1
  exact sum_pi_supp μ (fun x => Fn x * Fn x)

end Supp

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
  [∀ i, DecidableEq (Ω i)]

/-- The extension by zero of a function on the support. -/
noncomputable def extSupp {T : Type*} [Fintype T] (μ : FiniteLaw T) (f : Supp μ → ℝ) : T → ℝ :=
  fun x => by classical exact if h : 0 < μ.weight x then f ⟨x, h⟩ else 0

theorem extSupp_val {T : Type*} [Fintype T] (μ : FiniteLaw T) (f : Supp μ → ℝ) (a : Supp μ) :
    extSupp μ f a.1 = f a := by
  simp only [extSupp, dite_eq_left a.2]

theorem kernelForm_restrict {T : Type*} [Fintype T] (μ : FiniteLaw T) (c : T → T → ℝ)
    (f : Supp μ → ℝ) :
    kernelForm (restrictLaw μ) (restrictLaw μ) (fun a b => c a.1 b.1) f f =
      kernelForm μ μ c (extSupp μ f) (extSupp μ f) := by
  rw [kernelForm_apply, kernelForm_apply]
  unfold FiniteLaw.expect
  have e1 : ∀ a : Supp μ, ∑ b : Supp μ, (restrictLaw μ).weight b * (c a.1 b.1 * f b) =
      ∑ y, μ.weight y * (c a.1 y * extSupp μ f y) := by
    intro a
    rw [← sum_supp μ (fun y => c a.1 y * extSupp μ f y)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [extSupp_val]
    rfl
  simp only [e1]
  rw [← sum_supp μ (fun x => extSupp μ f x * ∑ y, μ.weight y * (c x y * extSupp μ f y))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [extSupp_val]
  rfl

theorem nrm_restrict {T : Type*} [Fintype T] (μ : FiniteLaw T) (f : Supp μ → ℝ) :
    nrm (restrictLaw μ) f = nrm μ (extSupp μ f) := by
  unfold nrm ip
  congr 1
  unfold FiniteLaw.expect
  rw [← sum_supp μ (fun x => extSupp μ f x * extSupp μ f x)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [extSupp_val]
  rfl

/-- **`lem:spec:tensorcomp` (a)**, for factor laws of arbitrary support. -/
theorem tensor_lower_gen (μ : ∀ i, FiniteLaw (Ω i)) (c : ∀ i, Ω i → Ω i → ℝ)
    (hcs : ∀ i x y, c i x y = c i y x) (g b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hg0 : ∀ i, 0 ≤ g i) (hgb : ∀ i, g i ≤ 1 + b i)
    (hlow : ∀ i f, -g i * nrm (μ i) f ^ 2 ≤ kernelForm (μ i) (μ i) (c i) f f)
    (hup : ∀ i f, kernelForm (μ i) (μ i) (c i) f f ≤ (1 + b i) * nrm (μ i) f ^ 2)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, g i * ∏ j ∈ Finset.univ.erase i, (1 + b j) ≤ M)
    (Fn : (∀ i, Ω i) → ℝ) :
    -M * nrm (FiniteLaw.pi μ) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun x y => ∏ i, c i (x i) (y i)) Fn Fn := by
  classical
  have h := tensor_lower (fun i => restrictLaw (μ i)) (fun i x => x.2)
    (fun i a b => c i a.1 b.1) (fun i a b => hcs i a.1 b.1) g b hb0 hg0 hgb
    (fun i f => by
      rw [kernelForm_restrict, nrm_restrict]
      exact hlow i _)
    (fun i f => by
      rw [kernelForm_restrict, nrm_restrict]
      exact hup i _)
    hM0 hM (fun z => Fn (fun i => (z i).1))
  rw [nrm_pi_supp] at h
  have e := kernelForm_pi_supp μ (fun x y => ∏ i, c i (x i) (y i)) Fn Fn
  rw [← e]
  exact h

end General

namespace SpecData

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)

/-- **`lem:spec:tensorcomp` (b), for spectral data.** Let `B` be a block (index set `ι`, fields
`F i`, with `p i = |F i| ≥ b > 0`). If the cut operators satisfy
`-g p^{-1/2} ‖H‖² ≤ ⟨H, A_p H⟩ ≤ (1 + c⁺/p) ‖H‖²` on `L²(μ_p)`, with `g p^{-1/2} < 1`, then
`E_{λ_B(G)}[F(x) F(x')] ≥ -(g/√b) ∏_p (1 + c⁺/p) ‖F‖²_{μ_B}`. -/
theorem block_cut_lower {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*}
    [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (hne : ∀ i, (injLabellings (F i) D.G).Nonempty) (p : ι → ℝ) {g cplus bmin : ℝ}
    (hg : 0 ≤ g) (hcp : 0 ≤ cplus) (hb : 0 < bmin) (hpb : ∀ i, bmin ≤ p i)
    (hgp : ∀ i, g * (√(p i))⁻¹ < 1)
    (hlow : ∀ i Hf, -(g * (√(p i))⁻¹) * nrm (D.halfLaw (hne i)) Hf ^ 2 ≤ D.cutForm (hne i) Hf Hf)
    (hup : ∀ i Hf, D.cutForm (hne i) Hf Hf ≤ (1 + cplus / p i) * nrm (D.halfLaw (hne i)) Hf ^ 2)
    (Fn : (∀ i, D.cut.Half → F i) → ℝ) :
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
  refine tensor_lower_gen (fun i => D.halfLaw (hne i)) (fun i x x' => D.cutK x x' / D.cutZ (hne i))
    (fun i x y => by rw [D.cutK_symm]) (fun i => g * (√(p i))⁻¹) (fun i => cplus / p i) hb0 hgi0
    (fun i => by linarith [hgp i, hb0 i]) hlow hup ?_ (fun i => ?_) Fn
  · exact mul_nonneg (mul_nonneg hg (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      (Finset.prod_nonneg (fun i _ => by linarith [hb0 i]))
  · exact (tensorcomp_scalar Finset.univ (fun i => cplus / p i) (fun i _ => hb0 i)
      (Finset.mem_univ i) (hgi0 i) (hgle i)).1

end SpecData

end Sarkozy.Cuts
