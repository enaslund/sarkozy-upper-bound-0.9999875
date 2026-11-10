module

public import Sarkozy.Mixing.PairSupport

@[expose] public section

/-!
# Step 1 of `lem:record:density-can`: the pair decomposition

`paper/sections/08_scale_comparison.tex`, proof of `lem:record:density-can`, Step 1. Condition
on the prefix labels `x ∼ ϱ_pre`; by hypothesis (a) of the lemma, `lem:tr:pairsupport` applies to
the tail factors, giving for every `x`
`|∫ φ_x W_x|² ≤ ‖W_x‖₂² [T₀^{-2γ} ‖φ_x‖₂² + ∑_{q_U ≤ T₀} q_U^{-2γ} ‖E_U φ_x‖₂²]`;
integrating over `x` with Cauchy–Schwarz,
`|∫ ∏_w G_w dϱ| ≤ (∫ ‖W_x‖₂²)^{1/2} (T₀^{-2γ} ∫ ‖φ_x‖₂² + ∑_{q_U ≤ T₀} q_U^{-2γ} ∫ ‖E_U φ_x‖₂²)^{1/2}`.

`step1_pair_decomposition` is this, with `lem:tr:pairsupport` the theorem
`Sarkozy.Mixing.pair_support_decay` of WP-S (abstract form: pair alphabets `A j` (the sets
`Ω_p`), other-slot alphabets `B j`, joint laws `κ j` with uniform pair marginal, contracting
mean-zero functions by `q_j^{-γ}`). The prefix integral is a `FiniteLaw`; `step1_integrate` is
the Cauchy–Schwarz step.

New material for this paper.
-/

namespace Sarkozy.Cancellation

open Finset
open scoped Matrix
open Sarkozy.Mixing

/-- **Integration over the prefix labels** (Step 1): if `|I_x|² ≤ W_x R_x` for every `x`, then
`|E_x I_x|² ≤ (E_x W_x)(E_x R_x)`. -/
lemma step1_integrate {X : Type*} [Fintype X] (μ : FiniteLaw X) (I Wsq R : X → ℝ)
    (hW : ∀ x, 0 ≤ Wsq x) (hR : ∀ x, 0 ≤ R x) (h : ∀ x, I x ^ 2 ≤ Wsq x * R x) :
    (μ.expect I) ^ 2 ≤ μ.expect Wsq * μ.expect R := by
  unfold FiniteLaw.expect
  have habs : ∀ x, |I x| ≤ Real.sqrt (Wsq x) * Real.sqrt (R x) := by
    intro x
    rw [← Real.sqrt_mul (hW x)]
    exact Real.abs_le_sqrt (h x)
  have h1 : |∑ x, μ.weight x * I x| ≤
      ∑ x, Real.sqrt (μ.weight x * Wsq x) * Real.sqrt (μ.weight x * R x) := by
    calc |∑ x, μ.weight x * I x| ≤ ∑ x, |μ.weight x * I x| := abs_sum_le_sum_abs _ _
      _ = ∑ x, μ.weight x * |I x| := by
          apply sum_congr rfl
          intro x _
          rw [abs_mul, abs_of_nonneg (μ.nonneg x)]
      _ ≤ ∑ x, μ.weight x * (Real.sqrt (Wsq x) * Real.sqrt (R x)) :=
          sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (habs x) (μ.nonneg x))
      _ = _ := by
          apply sum_congr rfl
          intro x _
          rw [Real.sqrt_mul (μ.nonneg x), Real.sqrt_mul (μ.nonneg x),
            show Real.sqrt (μ.weight x) * Real.sqrt (Wsq x) *
                (Real.sqrt (μ.weight x) * Real.sqrt (R x)) =
              (Real.sqrt (μ.weight x)) ^ 2 * (Real.sqrt (Wsq x) * Real.sqrt (R x)) by ring,
            Real.sq_sqrt (μ.nonneg x)]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun x => Real.sqrt (μ.weight x * Wsq x))
    (fun x => Real.sqrt (μ.weight x * R x))
  have hs1 : ∀ x, (Real.sqrt (μ.weight x * Wsq x)) ^ 2 = μ.weight x * Wsq x :=
    fun x => Real.sq_sqrt (mul_nonneg (μ.nonneg x) (hW x))
  have hs2 : ∀ x, (Real.sqrt (μ.weight x * R x)) ^ 2 = μ.weight x * R x :=
    fun x => Real.sq_sqrt (mul_nonneg (μ.nonneg x) (hR x))
  simp only [hs1, hs2] at h2
  have hA : 0 ≤ ∑ x, μ.weight x * Wsq x := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hW x))
  have hB : 0 ≤ ∑ x, μ.weight x * R x := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hR x))
  calc (∑ x, μ.weight x * I x) ^ 2 = |∑ x, μ.weight x * I x| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∑ x, μ.weight x * Wsq x) * Real.sqrt (∑ x, μ.weight x * R x)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

lemma expect_affine {X ι : Type*} [Fintype X] (μ : FiniteLaw X) (S : Finset ι) (c : ℝ)
    (d : ι → ℝ) (f : X → ℝ) (g : ι → X → ℝ) :
    μ.expect (fun x => c * f x + ∑ U ∈ S, d U * g U x) =
      c * μ.expect f + ∑ U ∈ S, d U * μ.expect (g U) := by
  unfold FiniteLaw.expect
  simp only [mul_add, sum_add_distrib, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro x _
    ring
  · rw [sum_comm]
    apply sum_congr rfl
    intro U _
    apply sum_congr rfl
    intro x _
    ring

section PairSupport

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)]

/-- **Step 1 of `lem:record:density-can` (the pair decomposition).** For the prefix law `μ`
(`ϱ_pre`), the tail laws `κ j` (`ϱ_p` read as a joint law of the pair `(u, v)`, with values in
`A j = Ω_p`, and of the other slots, `B j`), satisfying hypothesis (a) of the lemma (uniform pair
marginal, mean-zero contraction by `q_j^{-γ}`), and for every prefix label `x` the pair factor
`φ_x` and the product `W_x` of the other factors:
`|∫_x ∫ φ_x W_x|² ≤ (∫_x ‖W_x‖₂²) (T₀^{-2γ} ∫_x ‖φ_x‖₂² + ∑_{q_U ≤ T₀} q_U^{-2γ} ∫_x ‖E_U φ_x‖₂²)`,
`‖φ_x‖₂` for `⊗_p Unif(Ω_p)` and `‖W_x‖₂` for the law of the other slots. -/
theorem step1_pair_decomposition {X : Type*} [Fintype X] (μ : FiniteLaw X)
    (κ : ∀ j, FiniteLaw (A j × B j))
    (hsrc : ∀ j a, srcWeight (κ j) a = (Fintype.card (A j) : ℝ)⁻¹) (q : K → ℕ)
    (hq : ∀ j, 0 < q j) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j, ContractsMeanZero (κ j) ((q j : ℝ) ^ (-γ))) {T₀ : ℝ} (hT₀ : 1 ≤ T₀)
    (φ : X → (∀ j, A j) → ℝ) (W : X → (∀ j, B j) → ℝ) :
    (μ.expect fun x => ∑ b, tgtWeight (prodJoint κ) b * condOp (prodJoint κ) (φ x) b * W x b) ^ 2 ≤
      (μ.expect fun x => ∑ b, tgtWeight (prodJoint κ) b * W x b ^ 2) *
        (T₀ ^ (-2 * γ) *
            (μ.expect fun x => (FiniteLaw.uniform (∀ j, A j)).expect (fun a => φ x a ^ 2)) +
          ∑ U ∈ univ.filter (fun U : K → Bool => supportConductor q U ≤ T₀),
            supportConductor q U ^ (-2 * γ) *
              (μ.expect fun x => (FiniteLaw.uniform (∀ j, A j)).expect
                (fun a => (condProjOn A U *ᵥ φ x) a ^ 2))) := by
  set R : X → ℝ := fun x => T₀ ^ (-2 * γ) *
      (FiniteLaw.uniform (∀ j, A j)).expect (fun a => φ x a ^ 2) +
    ∑ U ∈ univ.filter (fun U : K → Bool => supportConductor q U ≤ T₀),
      supportConductor q U ^ (-2 * γ) *
        (FiniteLaw.uniform (∀ j, A j)).expect (fun a => (condProjOn A U *ᵥ φ x) a ^ 2) with hR
  have hW0 : ∀ x, 0 ≤ ∑ b, tgtWeight (prodJoint κ) b * W x b ^ 2 := fun x =>
    sum_nonneg (fun b _ => mul_nonneg (tgtWeight_nonneg _ _) (sq_nonneg _))
  have hR0 : ∀ x, 0 ≤ R x := by
    intro x
    apply add_nonneg
    · exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
        ((FiniteLaw.uniform _).expect_nonneg (fun a => sq_nonneg _))
    · apply sum_nonneg
      intro U _
      exact mul_nonneg (Real.rpow_nonneg (supportConductor_pos hq U).le _)
        ((FiniteLaw.uniform _).expect_nonneg (fun a => sq_nonneg _))
  have h := step1_integrate μ _ _ R hW0 hR0
    (fun x => pair_support_decay κ hsrc q hq hγ hmix hT₀ (φ x) (W x))
  refine h.trans (le_of_eq ?_)
  congr 1
  exact expect_affine μ _ _ _
    (fun x => (FiniteLaw.uniform (∀ j, A j)).expect (fun a => φ x a ^ 2))
    (fun U x => (FiniteLaw.uniform (∀ j, A j)).expect (fun a => (condProjOn A U *ᵥ φ x) a ^ 2))

end PairSupport

end Sarkozy.Cancellation
