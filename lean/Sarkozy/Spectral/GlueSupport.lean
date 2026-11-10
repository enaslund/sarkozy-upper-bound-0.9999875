module

public import Sarkozy.Cuts.TensorSpectrum
public import Sarkozy.Comparison.Recentering

/-!
# Glue, VIII: WP-P's tensor step without full support

WP-P's `Sarkozy.Cuts.tensorcomp_block` (`lem:spec:tensorcomp` (b), kernel form) assumes that
every law `μ_i` has full support. The half law `λ(G⁺)` is supported on `I⁺` only.
`tensorcomp_block_supp` is the same statement without that hypothesis. It restricts each `μ_i`
to its support (`restrictLaw`), applies `tensorcomp_block` there, and transfers back:
* `expect_restrict`: `E_{μ|supp} g = E_μ g`;
* `expect_pi_restrict`: the same for the product law.

So WP-P's tensor bound applies to the cut laws as they are.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Spectral

open Sarkozy Sarkozy.Cuts

open Classical in
/-- A finite law restricted to its support (a law with full support). -/
noncomputable def restrictLaw {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) :
    FiniteLaw {x : Ω // 0 < μ.weight x} where
  weight x := μ.weight x.1
  nonneg x := μ.nonneg x.1
  total := by
    rw [← μ.total, ← Finset.sum_subtype (univ.filter fun x => 0 < μ.weight x)
      (fun x => by simp) (fun x => μ.weight x)]
    refine Finset.sum_filter_of_ne fun x _ hx => ?_
    exact lt_of_le_of_ne (μ.nonneg x) (Ne.symm hx)

open Classical in
/-- `E_{μ|supp} (g ∘ val) = E_μ g`. -/
theorem expect_restrict {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (g : Ω → ℝ) :
    (restrictLaw μ).expect (fun x => g x.1) = μ.expect g := by
  unfold FiniteLaw.expect
  change ∑ x : {x : Ω // 0 < μ.weight x}, μ.weight x.1 * g x.1 = _
  rw [← Finset.sum_subtype (univ.filter fun x => 0 < μ.weight x) (fun x => by simp)
    (fun x => μ.weight x * g x)]
  refine Finset.sum_filter_of_ne fun x _ hx => ?_
  have hw : μ.weight x ≠ 0 := fun h => hx (by rw [h, zero_mul])
  exact lt_of_le_of_ne (μ.nonneg x) (Ne.symm hw)

open Classical in
/-- The same for products: `E_{⊗ μ_i|supp} (G ∘ val) = E_{⊗ μ_i} G`. -/
theorem expect_pi_restrict {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (μ : ∀ i, FiniteLaw (Ω i)) (G : (∀ i, Ω i) → ℝ) :
    (FiniteLaw.pi fun i => restrictLaw (μ i)).expect (fun x => G (fun i => (x i).1)) =
      (FiniteLaw.pi μ).expect G := by
  unfold FiniteLaw.expect
  refine Finset.sum_of_injOn (fun x i => (x i).1) ?_ (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro x _ y _ hxy
    funext i
    exact Subtype.ext (congrFun hxy i)
  · intro y _ hy
    have : ∃ i, ¬ 0 < (μ i).weight (y i) := by
      by_contra h
      push Not at h
      exact hy ⟨fun i => ⟨y i, h i⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
    obtain ⟨i, hi⟩ := this
    have h0 : (μ i).weight (y i) = 0 := le_antisymm (not_lt.mp hi) ((μ i).nonneg _)
    change (∏ j, (μ j).weight (y j)) * G y = 0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]
  · intro x _
    rfl

open Classical in
/-- **`tensorcomp_block` without full support.** The same conclusion as WP-P's
`Sarkozy.Cuts.tensorcomp_block`, with the hypothesis `∀ i x, 0 < (μ i).weight x` dropped. -/
theorem tensorcomp_block_supp {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)] (μ : ∀ i, FiniteLaw (Ω i))
    (c : ∀ i, Ω i → Ω i → ℝ) (hc : ∀ i x y, c i x y = c i y x) (p : ι → ℝ) {g cplus bmin : ℝ}
    (hg : 0 ≤ g) (hcplus : 0 ≤ cplus) (hbmin : 0 < bmin) (hbp : ∀ i, bmin ≤ p i)
    (hgp : ∀ i, g * (√(p i))⁻¹ < 1)
    (hlow : ∀ i (f : Ω i → ℝ), -(g * (√(p i))⁻¹) * Recentering.nrm (μ i) f ^ 2 ≤
      kernelForm (μ i) (μ i) (c i) f f)
    (hup : ∀ i (f : Ω i → ℝ), kernelForm (μ i) (μ i) (c i) f f ≤
      (1 + cplus / p i) * Recentering.nrm (μ i) f ^ 2)
    (Fn : (∀ i, Ω i) → ℝ) :
    -(g * (√bmin)⁻¹ * ∏ i, (1 + cplus / p i)) * Recentering.nrm (FiniteLaw.pi μ) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun x y => ∏ i, c i (x i) (y i)) Fn Fn := by
  -- forms and norms only see the support
  have hform : ∀ i (f : Ω i → ℝ), kernelForm (restrictLaw (μ i)) (restrictLaw (μ i))
      (fun x y => c i x.1 y.1) (fun x => f x.1) (fun x => f x.1) =
      kernelForm (μ i) (μ i) (c i) f f := by
    intro i f
    rw [kernelForm_apply, kernelForm_apply]
    rw [show (fun x : {x : Ω i // 0 < (μ i).weight x} => f x.1 * (restrictLaw (μ i)).expect
        (fun y => c i x.1 y.1 * f y.1)) = fun x => (fun x => f x * (μ i).expect
          (fun y => c i x y * f y)) x.1 from funext fun x => by
      rw [expect_restrict (μ i) (fun y => c i x.1 y * f y)]]
    exact expect_restrict (μ i) (fun x => f x * (μ i).expect (fun y => c i x y * f y))
  have hnrm : ∀ i (f : Ω i → ℝ),
      Recentering.nrm (restrictLaw (μ i)) (fun x => f x.1) = Recentering.nrm (μ i) f := by
    intro i f
    unfold Recentering.nrm Recentering.ip
    rw [expect_restrict (μ i) (fun x => f x * f x)]
  -- every function on the support is the restriction of a function on `Ω i`
  have hext : ∀ i (f' : {x : Ω i // 0 < (μ i).weight x} → ℝ),
      ∃ f : Ω i → ℝ, (fun x => f x.1) = f' := fun i f' =>
    ⟨fun x => if h : 0 < (μ i).weight x then f' ⟨x, h⟩ else 0,
      funext fun x => by simp [x.2]⟩
  have hlow' : ∀ i (f' : {x : Ω i // 0 < (μ i).weight x} → ℝ),
      -(g * (√(p i))⁻¹) * Recentering.nrm (restrictLaw (μ i)) f' ^ 2 ≤
        kernelForm (restrictLaw (μ i)) (restrictLaw (μ i)) (fun x y => c i x.1 y.1) f' f' := by
    intro i f'
    obtain ⟨f, rfl⟩ := hext i f'
    rw [hform, hnrm]
    exact hlow i f
  have hup' : ∀ i (f' : {x : Ω i // 0 < (μ i).weight x} → ℝ),
      kernelForm (restrictLaw (μ i)) (restrictLaw (μ i)) (fun x y => c i x.1 y.1) f' f' ≤
        (1 + cplus / p i) * Recentering.nrm (restrictLaw (μ i)) f' ^ 2 := by
    intro i f'
    obtain ⟨f, rfl⟩ := hext i f'
    rw [hform, hnrm]
    exact hup i f
  have h := tensorcomp_block (fun i => restrictLaw (μ i)) (fun i x => x.2)
    (fun i x y => c i x.1 y.1) (fun i x y => hc i x.1 y.1) p hg hcplus hbmin hbp hgp hlow' hup'
    (fun x => Fn (fun i => (x i).1))
  -- transfer back to `⊗ μ_i`
  have hF : kernelForm (FiniteLaw.pi fun i => restrictLaw (μ i))
      (FiniteLaw.pi fun i => restrictLaw (μ i)) (fun x y => ∏ i, c i (x i).1 (y i).1)
      (fun x => Fn (fun i => (x i).1)) (fun x => Fn (fun i => (x i).1)) =
      kernelForm (FiniteLaw.pi μ) (FiniteLaw.pi μ) (fun x y => ∏ i, c i (x i) (y i)) Fn Fn := by
    rw [kernelForm_apply, kernelForm_apply]
    rw [show (fun x : (∀ i, {x : Ω i // 0 < (μ i).weight x}) => Fn (fun i => (x i).1) *
        (FiniteLaw.pi fun i => restrictLaw (μ i)).expect
          (fun y => (∏ i, c i (x i).1 (y i).1) * Fn (fun i => (y i).1))) =
        fun x => (fun x => Fn x * (FiniteLaw.pi μ).expect (fun y => (∏ i, c i (x i) (y i)) *
          Fn y)) (fun i => (x i).1) from funext fun x => by
      rw [expect_pi_restrict μ (fun y => (∏ i, c i (x i).1 (y i)) * Fn y)]]
    exact expect_pi_restrict μ
      (fun x => Fn x * (FiniteLaw.pi μ).expect (fun y => (∏ i, c i (x i) (y i)) * Fn y))
  have hN : Recentering.nrm (FiniteLaw.pi fun i => restrictLaw (μ i))
      (fun x => Fn (fun i => (x i).1)) =
      Recentering.nrm (FiniteLaw.pi μ) Fn := by
    unfold Recentering.nrm Recentering.ip
    rw [expect_pi_restrict μ (fun x => Fn x * Fn x)]
  rw [hF, hN] at h
  exact h

end Sarkozy.Spectral
