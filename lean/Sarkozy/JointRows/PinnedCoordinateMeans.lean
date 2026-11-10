module

public import Sarkozy.JointRows.PinnedCoordinateCounts
public import Sarkozy.JointRows.StarParity

/-! Small character means for the actual uniform allowed-coordinate laws. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.PinCoordinate

open Finset Sarkozy.Labellings Sarkozy.JointRows.StarOps Sarkozy.JointRows.PaleyGauss

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem expect_unifOn {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Finset Ω) (hA : A.Nonempty) (f : Ω → ℝ) :
    (Coll.unifOn A hA).expect f = (∑ a ∈ A, f a) / A.card := by
  simp only [FiniteLaw.expect, Coll.unifOn, ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter, ← mul_sum, div_eq_mul_inv, mul_comm]

variable {p : ℕ} [Fact p.Prime]

theorem mchi_unifOn_le (A : Finset (ZMod p)) (hA : A.Nonempty) (t : ZMod p) :
    |mchi (Coll.unifOn A hA) t| ≤
      |((∑ a ∈ A, quadraticChar (ZMod p) (a - t) : ℤ) : ℝ)| / A.card := by
  have hpoint (a : ZMod p) : chiR p (t - a) = chiR p (-1) * chiR p (a - t) := by
    rw [show t - a = -(a - t) by ring, chiR_neg_all]
  unfold mchi
  rw [expect_unifOn, abs_div, abs_of_nonneg (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [sum_congr rfl (fun a _ => hpoint a), ← mul_sum, abs_mul]
  have heq : ∑ a ∈ A, chiR p (a - t) =
      ((∑ a ∈ A, quadraticChar (ZMod p) (a - t) : ℤ) : ℝ) := by
    simp only [chiR, Int.cast_sum]
  rw [heq]
  exact (mul_le_mul_of_nonneg_right (abs_chiR_le_one _) (abs_nonneg _)).trans_eq
    (one_mul _)

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem mean_bound (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (β : I → ZMod p) (hβ : Function.Injective β)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (M : Finset (ZMod p)) (hM : ∀ i, β i ∈ M)
    (hI : Fintype.card I ≤ 4) (hz : M.card ≤ 12)
    (hA : (admissible β s M).Nonempty) (t : ZMod p) (ht : t ∉ M) :
    |mchi (Coll.unifOn (admissible β s M) hA) t| ≤ 1024 * (Real.sqrt p)⁻¹ := by
  have hl := card_lower hp hW β hβ s hs M hM hI hz
  have hu := character_sum_small hW β hβ s hs M hM hI hz t ht
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hA0 : (0 : ℝ) < (admissible β s M).card := by exact_mod_cast card_pos.mpr hA
  have hl' : (p : ℝ) / 2 ≤ 2 ^ Fintype.card I * (admissible β s M).card := by
    have hnum : (1 : ℝ) / 2 ≤ 1 - (2 : ℝ)⁻¹ ^ 50 := by norm_num
    nlinarith
  have hrp : (Real.sqrt p)⁻¹ * p = Real.sqrt p := by
    calc
      _ = (Real.sqrt p)⁻¹ * (Real.sqrt p) ^ 2 := by rw [Real.sq_sqrt hp0.le]
      _ = _ := by field_simp
  apply (mchi_unifOn_le _ hA t).trans
  rw [div_le_iff₀ hA0]
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 ^ Fintype.card I)).mp
  calc
    _ ≤ 512 * Real.sqrt p := hu
    _ = (1024 * (Real.sqrt p)⁻¹) * ((p : ℝ) / 2) := by nlinarith [hrp]
    _ ≤ (1024 * (Real.sqrt p)⁻¹) *
        (2 ^ Fintype.card I * (admissible β s M).card) :=
      mul_le_mul_of_nonneg_left hl' (by positivity)
    _ = _ := by ring

theorem mean_tail (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (β : I → ZMod p) (hβ : Function.Injective β)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (M : Finset (ZMod p)) (hM : ∀ i, β i ∈ M)
    (hI : Fintype.card I ≤ 4) (hz : M.card ≤ 12)
    (hA : (admissible β s M).Nonempty) (t : ZMod p) (ht : t ∉ M) :
    |mchi (Coll.unifOn (admissible β s M) hA) t| ≤ (2 : ℝ)⁻¹ ^ 80 := by
  calc
    _ ≤ 1024 * (Real.sqrt p)⁻¹ := mean_bound hp hW β hβ s hs M hM hI hz hA t ht
    _ ≤ 1024 * (2 : ℝ)⁻¹ ^ 256 :=
      mul_le_mul_of_nonneg_left (SpectralD.tail_rp_le hp) (by norm_num)
    _ ≤ _ := by norm_num

end Sarkozy.JointRows.PinCoordinate
