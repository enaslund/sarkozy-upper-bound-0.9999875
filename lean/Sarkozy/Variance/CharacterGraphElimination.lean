module

public import Sarkozy.Variance.CharacterGraphBasic

/-! Exact leaf, repeated-edge, and degree-two elimination of character-graph moments. -/

@[expose] public section

namespace Sarkozy.Variance.CharacterGraph

open Finset Sarkozy.L20Cap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem moment_identify (a b : ι) (hab : a ≠ b) (G : List (ι × ι)) :
    (labelLaw ι F).expect (fun x => if x a = x b then edgeProd F G x else 0) =
      (Fintype.card F : ℝ)⁻¹ * moment F (identify a b G) := by
  rw [label_expect_identify a b hab]
  unfold moment
  congr 1
  exact (labelLaw ι F).expect_congr fun x => (edgeProd_identify F a b G x).symm

theorem moment_double (a b : ι) (hab : a ≠ b) (G : List (ι × ι)) :
    moment F ((a, b) :: (a, b) :: G) =
      moment F G - (Fintype.card F : ℝ)⁻¹ * moment F (identify a b G) := by
  have hpoint (x : ι → F) : edgeProd F ((a, b) :: (a, b) :: G) x =
      edgeProd F G x - if x a = x b then edgeProd F G x else 0 := by
    by_cases h : x a = x b
    · simp only [edgeProd, h, sub_self, chi_zero, zero_mul, ite_true]
    · have hs := chi_sq_of_ne (sub_ne_zero.mpr (Ne.symm h))
      simp only [edgeProd, ite_eq_right h, sub_zero]
      rw [← mul_assoc, ← pow_two, hs, one_mul]
  unfold moment at ⊢
  rw [show edgeProd F ((a, b) :: (a, b) :: G) =
    fun x => edgeProd F G x - if x a = x b then edgeProd F G x else 0 from funext hpoint]
  rw [FiniteLaw.expect_sub, moment_identify F a b hab G]
  rfl

theorem moment_leaf (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1)
    (v a : ι) (hva : v ≠ a) (G : List (ι × ι)) (hG : Avoids G v) :
    moment F ((v, a) :: G) = 0 := by
  unfold moment
  rw [label_expect_update v]
  have hinner (x : ι → F) : (FiniteLaw.uniform F).expect
      (fun t => edgeProd F ((v, a) :: G) (Function.update x v t)) = 0 := by
    simp only [edgeProd, Function.update_of_ne (Ne.symm hva), Function.update_self,
      edgeProd_update F G v hG, FiniteLaw.expect_mul_const]
    have hz : (FiniteLaw.uniform F).expect (fun t => chi (x a - t)) = 0 := by
      simp_rw [chi_sub_comm hm1 (x a), FiniteLaw.expect_uniform, sum_neg_distrib,
        sum_chi_shift hF, neg_zero, zero_div]
    rw [hz, zero_mul]
  simp_rw [hinner]
  rw [FiniteLaw.expect_const]

theorem moment_degree_two (hF : ringChar F ≠ 2) (v a b : ι)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (G : List (ι × ι)) (hG : Avoids G v) :
    moment F ((v, a) :: (v, b) :: G) =
      (Fintype.card F : ℝ)⁻¹ * (moment F (identify a b G) - moment F G) := by
  have hp : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinner (x : ι → F) : (FiniteLaw.uniform F).expect
      (fun t => edgeProd F ((v, a) :: (v, b) :: G) (Function.update x v t)) =
        (if x a = x b then edgeProd F G x else 0) -
          (Fintype.card F : ℝ)⁻¹ * edgeProd F G x := by
    simp only [edgeProd, Function.update_of_ne (Ne.symm hva),
      Function.update_of_ne (Ne.symm hvb), Function.update_self, edgeProd_update F G v hG,
      ← mul_assoc, FiniteLaw.expect_mul_const, FiniteLaw.expect_uniform, sum_chi_rev hF]
    by_cases h : x a = x b <;> simp only [h, ite_true, ite_false] <;> field_simp
    ring
  unfold moment at ⊢
  rw [label_expect_update v]
  simp_rw [hinner]
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const_mul, moment_identify F a b hab G]
  unfold moment
  ring

end Sarkozy.Variance.CharacterGraph
