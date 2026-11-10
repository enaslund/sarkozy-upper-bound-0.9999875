module

public import Sarkozy.JointRows.StarDictionaryAllPrimes

/-! The pure and complementary-mean star decomposition in either prime class. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.JointRows.PaleyGauss

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem chiR_neg_all (t : ZMod p) : chiR p (-t) = chiR p (-1) * chiR p t := by
  rw [show -t = (-1) * t by ring, chiR_mul]

theorem abs_chiR_le_one (t : ZMod p) : |chiR p t| ≤ 1 := by
  rcases quadraticChar_isQuadratic (ZMod p) t with h | h | h <;>
    simp [chiR, h]

noncomputable def rowParityCoef (D : X → X → ℝ) (i : X) (T : Finset X) : ℝ :=
  chiR p (-1) ^ T.card * ∏ j ∈ T, D i j

noncomputable def meanKernelPrime (νp : X → FiniteLaw (ZMod p)) (D : X → X → ℝ)
    (𝒮 : Finset (Finset X)) (x y : X → ZMod p) : ℝ :=
  (∑ i, ∑ T ∈ 𝒮, rowParityCoef (p := p) D i T *
    ((∏ j ∈ T, (mchi (νp j) (x i) + phi (νp j) (x i) (y j))) -
      ∏ j ∈ T, phi (νp j) (x i) (y j))) +
    ∑ j, ∑ S ∈ 𝒮, coefB D j S *
      ((∏ i ∈ S, (mchi (νp i) (y j) + phi (νp i) (y j) (x i))) -
        ∏ i ∈ S, phi (νp i) (y j) (x i))

omit [DecidableEq X] in
theorem starKernel_eq_prime (νp : X → FiniteLaw (ZMod p)) (D : X → X → ℝ)
    (𝒮 : Finset (Finset X)) (x y : X → ZMod p) :
    starKernel D 𝒮 x y = pureKernel νp νp D 𝒮 (rowParityCoef (p := p) D) 𝒮
      (coefB D) x y + meanKernelPrime νp D 𝒮 x y := by
  have hrow : ∀ i (T : Finset X), ∏ j ∈ T, (D i j * chiR p (y j - x i)) =
      rowParityCoef (p := p) D i T *
        ∏ j ∈ T, (mchi (νp j) (x i) + phi (νp j) (x i) (y j)) := by
    intro i T
    have h1 : ∀ j, D i j * chiR p (y j - x i) =
        (chiR p (-1) * D i j) *
          (mchi (νp j) (x i) + phi (νp j) (x i) (y j)) := by
      intro j
      rw [← chiR_eq_mchi_add_phi, show y j - x i = -(x i - y j) by ring,
        chiR_neg_all]
      ring
    rw [prod_congr rfl fun j _ => h1 j, prod_mul_distrib]
    simp only [rowParityCoef, prod_mul_distrib, prod_const]
  have hcol : ∀ j (S : Finset X), ∏ i ∈ S, (D i j * chiR p (y j - x i)) =
      coefB D j S * ∏ i ∈ S, (mchi (νp i) (y j) + phi (νp i) (y j) (x i)) := by
    intro j S
    rw [prod_congr rfl fun i _ => by rw [chiR_eq_mchi_add_phi (νp i)], prod_mul_distrib]
    rfl
  unfold starKernel pureKernel meanKernelPrime
  simp only [hrow, hcol, mul_sub, sum_sub_distrib]
  ring

end Sarkozy.JointRows.StarOps
