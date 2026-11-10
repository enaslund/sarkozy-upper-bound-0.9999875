module

public import Sarkozy.Extraction.KernelAcyclic
public import Sarkozy.Extraction.KernelTwoCycles
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset





@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Spectral

open Sarkozy Sarkozy.Influence

/-- **Cauchy–Schwarz with an operator bound.** -/
theorem bilinear_of_opBound {X Y : Type*} [Fintype X] [Fintype Y] (A : X → Y → ℝ) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (h : OpBound univ univ A Λ) (f : X → ℝ) (g : Y → ℝ) :
    |∑ x, ∑ y, f x * A x y * g y| ≤ Λ * Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ y, g y ^ 2) := by
  have e : ∑ x, ∑ y, f x * A x y * g y = ∑ x, f x * ∑ y, A x y * g y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [e]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ f (fun x => ∑ y, A x y * g y)
  have hop := h g
  have h2 : (∑ x, f x * ∑ y, A x y * g y) ^ 2 ≤
      (Λ * Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ y, g y ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun y _ => sq_nonneg _)]
    calc (∑ x, f x * ∑ y, A x y * g y) ^ 2
        ≤ (∑ x, f x ^ 2) * ∑ x, (∑ y, A x y * g y) ^ 2 := hcs
      _ ≤ (∑ x, f x ^ 2) * (Λ ^ 2 * ∑ y, g y ^ 2) :=
          mul_le_mul_of_nonneg_left hop (Finset.sum_nonneg fun x _ => sq_nonneg _)
      _ = Λ ^ 2 * (∑ x, f x ^ 2) * ∑ y, g y ^ 2 := by ring
  exact (abs_le_of_sq_le_sq' h2 (by positivity)).2 |> fun h' =>
    abs_le.mpr ⟨(abs_le_of_sq_le_sq' h2 (by positivity)).1, h'⟩

/-- `∑_x (∏_i ρ_i(x_i))² a(x)² ≤ ∏_i ∑_t ρ_i(t)²` when `|a| ≤ 1`. -/
theorem sum_prod_sq_le {k : ℕ} {F : Type*} [Fintype F] (ρ : Fin k → F → ℝ)
    (a : (Fin k → F) → ℝ) (ha : ∀ x, |a x| ≤ 1) :
    ∑ x : Fin k → F, ((∏ i, ρ i (x i)) * a x) ^ 2 ≤ ∏ i, ∑ t, ρ i t ^ 2 := by
  rw [Fintype.prod_sum (fun i t => ρ i t ^ 2)]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [mul_pow, ← Finset.prod_pow]
  have h1 : a x ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (abs_nonneg _) (ha x) 2
    rwa [sq_abs, one_pow] at this
  have h0 : 0 ≤ ∏ i, ρ i (x i) ^ 2 := Finset.prod_nonneg fun i _ => sq_nonneg _
  calc (∏ i, ρ i (x i) ^ 2) * a x ^ 2 ≤ (∏ i, ρ i (x i) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = ∏ i, ρ i (x i) ^ 2 := mul_one _

/-- **Cauchy–Schwarz with an operator bound on a block** `R × C`. -/
theorem bilinear_of_opBound_on {X Y : Type*} (R : Finset X) (C : Finset Y) (A : X → Y → ℝ)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (h : OpBound R C A Λ) (f : X → ℝ) (g : Y → ℝ) :
    |∑ x ∈ R, ∑ y ∈ C, f x * A x y * g y| ≤
      Λ * Real.sqrt (∑ x ∈ R, f x ^ 2) * Real.sqrt (∑ y ∈ C, g y ^ 2) := by
  have e : ∑ x ∈ R, ∑ y ∈ C, f x * A x y * g y = ∑ x ∈ R, f x * ∑ y ∈ C, A x y * g y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [e]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq R f (fun x => ∑ y ∈ C, A x y * g y)
  -- the operator bound applies to `g` restricted to `C`
  have hop := h g
  have h2 : (∑ x ∈ R, f x * ∑ y ∈ C, A x y * g y) ^ 2 ≤
      (Λ * Real.sqrt (∑ x ∈ R, f x ^ 2) * Real.sqrt (∑ y ∈ C, g y ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun y _ => sq_nonneg _)]
    calc (∑ x ∈ R, f x * ∑ y ∈ C, A x y * g y) ^ 2
        ≤ (∑ x ∈ R, f x ^ 2) * ∑ x ∈ R, (∑ y ∈ C, A x y * g y) ^ 2 := hcs
      _ ≤ (∑ x ∈ R, f x ^ 2) * (Λ ^ 2 * ∑ y ∈ C, g y ^ 2) :=
          mul_le_mul_of_nonneg_left hop (Finset.sum_nonneg fun x _ => sq_nonneg _)
      _ = Λ ^ 2 * (∑ x ∈ R, f x ^ 2) * ∑ y ∈ C, g y ^ 2 := by ring
  exact abs_le.mpr ⟨(abs_le_of_sq_le_sq' h2 (by positivity)).1,
    (abs_le_of_sq_le_sq' h2 (by positivity)).2⟩

variable {p : ℕ} [Fact p.Prime]

/-- **The matching bound, acyclic case** (`lem:push:localvariance` (b)(i) with `b = 0`, from
`lem:matching:kernel` (a), `Extraction.witnessKernel_opBound`). -/
theorem glue_matching_acyclic (hp2 : p ≠ 2) {k : ℕ} {𝒦 : Finset (Fin k × Fin k)}
    {ς : Fin k → Fin k → ZMod p} (hdiag : ∀ i, (i, i) ∈ 𝒦) (hς : ∀ i l, ς i l = 1 ∨ ς i l = -1)
    (hacyc : Extraction.IsAcyclicWitness 𝒦) (ρ σ : Fin k → ZMod p → ℝ)
    (a b : (Fin k → ZMod p) → ℝ) (ha : ∀ x, |a x| ≤ 1) (hb : ∀ y, |b y| ≤ 1) :
    |∑ x, ∑ y, ((∏ i, ρ i (x i)) * a x) * Extraction.witnessKernel 𝒦 ς x y *
        (b y * ∏ l, σ l (y l))| ≤
      Real.sqrt p ^ k * Real.sqrt (∏ i, ∑ t, ρ i t ^ 2) * Real.sqrt (∏ l, ∑ t, σ l t ^ 2) := by
  have hop := Extraction.witnessKernel_opBound hp2 hdiag hς hacyc
  have h := bilinear_of_opBound _ (by positivity) hop (fun x => (∏ i, ρ i (x i)) * a x)
    (fun y => b y * ∏ l, σ l (y l))
  refine h.trans ?_
  have hf := sum_prod_sq_le ρ a ha
  have hg : ∑ y : Fin k → ZMod p, (b y * ∏ l, σ l (y l)) ^ 2 ≤ ∏ l, ∑ t, σ l t ^ 2 := by
    have := sum_prod_sq_le σ b hb
    refine (Finset.sum_le_sum fun y _ => ?_).trans this
    rw [mul_comm]
  have hΛ : 0 ≤ Real.sqrt p ^ k := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hf) hΛ)
    (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg _) (by positivity)

/-- **The matching bound with two-vertex components** (`lem:push:localvariance` (b)(i), any `b`,
from `lem:matching:kernel` (b), `Extraction.witnessKernel_opBound_twoCycles`; the four-cycle
bound is a hypothesis there). -/
theorem glue_matching_twoCycles (hp2 : p ≠ 2) (h4 : Extraction.FourCycleBound p) {k : ℕ}
    {𝒦 : Finset (Fin k × Fin k)} {ς : Fin k → Fin k → ZMod p} (hdiag : ∀ i, (i, i) ∈ 𝒦)
    (hς : ∀ e ∈ 𝒦, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1)
    (hcomp : ∀ i, (Extraction.twoCycleComponent 𝒦 i).card ≤ 2)
    {R C : Finset (Fin k → ZMod p)}
    (hR : ∀ x ∈ R, ∀ i l, i ≠ l → Extraction.twoCycleMutual 𝒦 i l → x i ≠ x l)
    (hC : ∀ y ∈ C, ∀ i l, i ≠ l → Extraction.twoCycleMutual 𝒦 i l → y i ≠ y l)
    (ρ σ : Fin k → ZMod p → ℝ) (a b : (Fin k → ZMod p) → ℝ) (ha : ∀ x, |a x| ≤ 1)
    (hb : ∀ y, |b y| ≤ 1) :
    |∑ x ∈ R, ∑ y ∈ C, ((∏ i, ρ i (x i)) * a x) * Extraction.witnessKernel 𝒦 ς x y *
        (b y * ∏ l, σ l (y l))| ≤
      2 ^ Extraction.twoCycleCount 𝒦 * Real.sqrt p ^ k * Real.sqrt (∏ i, ∑ t, ρ i t ^ 2) *
        Real.sqrt (∏ l, ∑ t, σ l t ^ 2) := by
  have hop := Extraction.witnessKernel_opBound_twoCycles hp2 h4 hdiag hς hcomp hR hC
  have h := bilinear_of_opBound_on R C _ (by positivity) hop (fun x => (∏ i, ρ i (x i)) * a x)
    (fun y => b y * ∏ l, σ l (y l))
  refine h.trans ?_
  have hf : ∑ x ∈ R, ((∏ i, ρ i (x i)) * a x) ^ 2 ≤ ∏ i, ∑ t, ρ i t ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) fun x _ _ =>
      sq_nonneg _).trans (sum_prod_sq_le ρ a ha)
  have hg : ∑ y ∈ C, (b y * ∏ l, σ l (y l)) ^ 2 ≤ ∏ l, ∑ t, σ l t ^ 2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) fun y _ _ =>
      sq_nonneg _).trans ?_
    refine (Finset.sum_le_sum fun y _ => ?_).trans (sum_prod_sq_le σ b hb)
    rw [mul_comm]
  have hΛ : 0 ≤ 2 ^ Extraction.twoCycleCount 𝒦 * Real.sqrt p ^ k := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hf) hΛ)
    (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg _) (by positivity)

end Sarkozy.Spectral
