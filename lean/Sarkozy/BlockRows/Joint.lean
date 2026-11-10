module

public import Sarkozy.BlockRows.Product
public import Sarkozy.JointRows.Discharge

@[expose] public section

/-!
# Block rows, IV: product kernels and the transport of joint data

`paper/sections/17_completion_repair.tex`, `cor:joint-completion-blocks` (its hypothesis "a
five-type datum whose conditional kernels at `b` are products over the primes of `𝔅`").

* `kernelOf_prod`: the kernel `T^ξ = kernelOf π_E π ξ` of a product law is the product of the
  one-prime kernels;
* `expect_equiv`, `kf_equiv`, `nrm_equiv`, `kone_equiv`, `kone'_equiv`, `eform_equiv`: the forms
  of `FiveType` are invariant under a relabelling `e : 𝔛 ≃ 𝔜` that carries the law and the kernels;
* `JointData.transport`: the joint data of `lem:five-type`(f) are carried along such a relabelling
  (so the block joint data of `joint_completion_blocks'`, stated on `∏_p X_p`, give joint data of
  the block datum, whose objects carry block labels).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockRows

open Sarkozy Sarkozy.FiveType Sarkozy.PartV

/-! ## The kernel of a product law -/

section Kernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (Y i)] {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- **The kernel of a product law is the product of the one-prime kernels**, at `ξ ∈ supp ν`. -/
theorem kernelOf_prod {s : 𝔛 ≃ ∀ i, Y i} {πE πF : FiniteLaw (Fin 3 → 𝔛)}
    {πEp πFp : ∀ i, FiniteLaw (Fin 3 → Y i)} (hE : IsProd3 s πE πEp) (hF : IsProd3 s πF πFp)
    {ξ : 𝔛} (hξ : (nuOf πE).weight ξ ≠ 0) (x y : 𝔛) :
    kernelOf πE πF ξ x y = ∏ i, kernelOf (πEp i) (πFp i) (s ξ i) (s x i) (s y i) := by
  have hD : (nuOf πE).weight ξ * (nubOf πE ξ).weight x * (nubOf πE ξ).weight y =
      ∏ i, ((nuOf (πEp i)).weight (s ξ i) * (nubOf (πEp i) (s ξ i)).weight (s x i) *
        (nubOf (πEp i) (s ξ i)).weight (s y i)) := by
    rw [nu_prod hE, nub_prod hE hξ, nub_prod hE hξ, ← prod_mul_distrib, ← prod_mul_distrib]
  unfold kernelOf
  rw [hD]
  split_ifs with h0
  · obtain ⟨i, -, hi⟩ := prod_eq_zero_iff.mp h0
    exact (Finset.prod_eq_zero (i := i) (mem_univ i) (by rw [hi]; simp)).symm
  · have hi : ∀ i, (nuOf (πEp i)).weight (s ξ i) * (nubOf (πEp i) (s ξ i)).weight (s x i) *
        (nubOf (πEp i) (s ξ i)).weight (s y i) ≠ 0 := fun i =>
      prod_ne_zero_iff.mp h0 i (mem_univ i)
    rw [hF.weight3, ← prod_div_distrib]
    exact prod_congr rfl fun i _ => by simp only [hi i, ↓reduceIte]

end Kernel

/-! ## Relabelling -/

section Equiv

variable {𝔛 𝔜 : Type*} [Fintype 𝔛] [Fintype 𝔜] (e : 𝔛 ≃ 𝔜) {μ : FiniteLaw 𝔛}
  {μ' : FiniteLaw 𝔜}

theorem expect_equiv (hμ : ∀ x, μ.weight x = μ'.weight (e x)) (Φ : 𝔛 → ℝ) :
    μ.expect Φ = μ'.expect (fun y => Φ (e.symm y)) := by
  unfold FiniteLaw.expect
  exact Fintype.sum_equiv e _ _ fun x => by simp only [hμ, e.symm_apply_apply]

theorem nrm_equiv (hμ : ∀ x, μ.weight x = μ'.weight (e x)) (Φ : 𝔛 → ℝ) :
    nrm μ Φ = nrm μ' (fun y => Φ (e.symm y)) := by
  unfold nrm ip
  rw [expect_equiv e hμ]

theorem kf_equiv (hμ : ∀ x, μ.weight x = μ'.weight (e x)) {T : 𝔛 → 𝔛 → ℝ}
    {T' : 𝔜 → 𝔜 → ℝ} (hT : ∀ x y, T x y = T' (e x) (e y)) (Φ Ψ : 𝔛 → ℝ) :
    kf μ T Φ Ψ = kf μ' T' (fun y => Φ (e.symm y)) (fun y => Ψ (e.symm y)) := by
  unfold kf
  refine Fintype.sum_equiv e _ _ fun x => ?_
  refine Fintype.sum_equiv e _ _ fun y => ?_
  simp only [hμ, hT, e.symm_apply_apply]

theorem kone_equiv (hμ : ∀ x, μ.weight x = μ'.weight (e x)) {T : 𝔛 → 𝔛 → ℝ}
    {T' : 𝔜 → 𝔜 → ℝ} (hT : ∀ x y, T x y = T' (e x) (e y)) (x : 𝔛) :
    kone μ T x = kone μ' T' (e x) := by
  unfold kone
  exact Fintype.sum_equiv e _ _ fun y => by rw [hμ, hT]

theorem kone'_equiv (hμ : ∀ x, μ.weight x = μ'.weight (e x)) {T : 𝔛 → 𝔛 → ℝ}
    {T' : 𝔜 → 𝔜 → ℝ} (hT : ∀ x y, T x y = T' (e x) (e y)) (y : 𝔛) :
    kone' μ T y = kone' μ' T' (e y) := by
  unfold kone'
  exact Fintype.sum_equiv e _ _ fun x => by rw [hμ, hT]

theorem eform_equiv (hμ : ∀ x, μ.weight x = μ'.weight (e x)) {T : 𝔛 → 𝔛 → ℝ}
    {T' : 𝔜 → 𝔜 → ℝ} (hT : ∀ x y, T x y = T' (e x) (e y)) (Φ : 𝔛 → ℝ) :
    eform μ T Φ = eform μ' T' (fun y => Φ (e.symm y)) := by
  unfold eform
  rw [kf_equiv e hμ hT, expect_equiv e hμ]

/-- **The joint data of `lem:five-type`(f) are carried along a relabelling** that carries the
reference law, the matching kernel and the fold kernel. -/
noncomputable def JointData.transport (hμ : ∀ x, μ.weight x = μ'.weight (e x))
    {TE K : 𝔛 → 𝔛 → ℝ} {TE' K' : 𝔜 → 𝔜 → ℝ} (hTE : ∀ x y, TE x y = TE' (e x) (e y))
    (hK : ∀ x y, K x y = K' (e x) (e y)) {H υ εT εE κJ : ℝ}
    (J : JointData μ' TE' K' H υ εT εE κJ) : JointData μ TE K H υ εT εE κJ where
  m := J.m
  φ0 x := J.φ0 (e x)
  φ2 x := J.φ2 (e x)
  C x y := J.C (e x) (e y)
  R x y := J.R (e x) (e y)
  decomp x y := by rw [hK, J.decomp]
  m_lower := J.m_lower
  m_upper := J.m_upper
  mean0 := by
    rw [expect_equiv e hμ]
    simpa only [e.apply_symm_apply] using J.mean0
  mean2 := by
    rw [expect_equiv e hμ]
    simpa only [e.apply_symm_apply] using J.mean2
  dev0 := by
    rw [nrm_equiv e hμ]
    simpa only [e.apply_symm_apply] using J.dev0
  dev2 := by
    rw [nrm_equiv e hμ]
    simpa only [e.apply_symm_apply] using J.dev2
  annC := ⟨fun x hx => by
      rw [kone_equiv e hμ (fun _ _ => rfl)]
      exact J.annC.1 (e x) (by rwa [← hμ]),
    fun y hy => by
      rw [kone'_equiv e hμ (fun _ _ => rfl)]
      exact J.annC.2 (e y) (by rwa [← hμ])⟩
  annR := ⟨fun x hx => by
      rw [kone_equiv e hμ (fun _ _ => rfl)]
      exact J.annR.1 (e x) (by rwa [← hμ]),
    fun y hy => by
      rw [kone'_equiv e hμ (fun _ _ => rfl)]
      exact J.annR.2 (e y) (by rwa [← hμ])⟩
  normR Φ Ψ := by
    rw [kf_equiv e hμ (fun _ _ => rfl), nrm_equiv e hμ Φ, nrm_equiv e hμ Ψ]
    exact J.normR _ _
  lowerE Φ := by
    rw [eform_equiv e hμ hTE, nrm_equiv e hμ Φ]
    exact J.lowerE _
  joint Φ Ψ := by
    rw [eform_equiv e hμ hTE, eform_equiv e hμ hTE, kf_equiv e hμ (fun _ _ => rfl),
      nrm_equiv e hμ Φ, nrm_equiv e hμ Ψ]
    exact J.joint _ _

end Equiv

end Sarkozy.BlockRows
