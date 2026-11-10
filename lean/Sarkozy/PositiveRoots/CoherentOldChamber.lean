module

public import Sarkozy.PositiveRoots.CoherentParameters
public import Sarkozy.PositiveRoots.FiniteMatrixBound
public import Sarkozy.L20Cap.StarMatrix

/-! Identify the untilted coherent chamber matrix with the proved L20 star matrix. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentOldChamber

open Finset Sarkozy.SpectralD Sarkozy.SpectralC Sarkozy.L20Cap
open Sarkozy.SpectralD.StarMatrix

def idxSupport : Idx → Finset (Fin 6) := Sum.elim singleton Subtype.val

def index (a : Idx) : Fin 64 :=
  ⟨(∑ i ∈ idxSupport a, 2 ^ i.val) % 64, Nat.mod_lt _ (by decide)⟩

theorem index_injective : Function.Injective index := by decide +kernel

def embedding : Idx ↪ Fin 64 := ⟨index, index_injective⟩

theorem support_index : ∀ a, CoherentMatrix.support (index a) = idxSupport a := by
  decide +kernel

theorem index_coverage : ∀ i : Fin 64, i ∈ univ.map embedding ↔ i ≠ 0 := by
  decide +kernel

theorem sign_eq : ∀ i j, CoherentMatrix.sign i j = D20Z i j := by decide +kernel

theorem old_restricted (a b : Idx) :
    CoherentParameters.old .chamber (index a) (index b) = softM D20 a b := by
  have hr (S : {S // S ∈ supports (Fin 6)}) : 2 ≤ S.val.card :=
    two_le_card_of_mem S.property
  have hg (z : ℤ) : gaussian z 0 = (z : ℂ) := by
    apply Complex.ext <;> simp [gaussian]
  rcases a with i | S <;> rcases b with j | T
  all_goals
    simp only [CoherentParameters.old, CoherentEndpoint.starReal,
      CoherentEndpoint.starImag, CoherentEndpoint.sign, support_index,
      idxSupport, Sum.elim_inl, Sum.elim_inr, card_singleton, sign_eq,
      show ¬ (2 : ℕ) ≤ 1 by decide, false_and, and_false, ite_false,
      and_self, ite_true, sum_singleton, add_zero, zero_add]
  · apply Complex.ext <;> simp [gaussian, softM, matI, starM0, starM1, D20]
  · have hT := hr T
    have hprod : (∏ b ∈ T.val, D20Z b i) = (-1) ^ T.val.card * ∏ b ∈ T.val, D20Z i b := by
      calc
        _ = ∏ b ∈ T.val, -D20Z i b := prod_congr rfl (fun b _ => D20Z_antisymm i b)
        _ = _ := prod_neg _
    simp only [show T.val.card ≠ 1 by omega, hT, true_and, and_true, ite_true, ite_false]
    rw [hprod]
    simp only [softM, matI, starM0, starM1, softL_D20, Complex.ofReal_zero,
      mul_zero, add_zero]
    rw [hg]
    push_cast
    rfl
  · have hS := hr S
    simp only [show S.val.card ≠ 1 by omega, hS, and_true, ite_true, ite_false]
    simp only [softM, matI, starM0, starM1, softR_D20, Complex.ofReal_zero,
      mul_zero, add_zero]
    rw [hg]
    push_cast
    rfl
  · have hS := hr S
    have hT := hr T
    simp only [show S.val.card ≠ 1 by omega, show T.val.card ≠ 1 by omega,
      and_false, false_and, ite_false, add_zero]
    apply Complex.ext <;> simp [gaussian, softM, matI, starM0, starM1]

theorem old_zero (i j : Fin 64)
    (h : i ∉ univ.map embedding ∨ j ∉ univ.map embedding) :
    CoherentParameters.old .chamber i j = 0 := by
  have hi : i = 0 ∨ j = 0 := by simpa only [index_coverage, not_not] using h
  rcases hi with rfl | rfl <;> apply Complex.ext <;>
    simp [CoherentParameters.old, CoherentEndpoint.starReal, CoherentEndpoint.starImag,
      CoherentMatrix.support, gaussian]

theorem old_chamber_bound (x : Fin 64 → ℂ) :
    -Real.sqrt 30 * ∑ i, ‖x i‖ ^ 2 ≤
      (qform (CoherentParameters.old .chamber) x).re := by
  apply lower_bound_of_restriction _ embedding (Real.sqrt_nonneg _) old_zero _ x
  intro y
  change -Real.sqrt 30 * ∑ i, ‖y i‖ ^ 2 ≤
    (qform (fun i j => CoherentParameters.old .chamber (index i) (index j)) y).re
  simp_rw [old_restricted]
  have h := normLe_softM_D20 y y
  change ‖qform (softM D20) y‖ ≤ Real.sqrt 30 * vnorm y * vnorm y at h
  rw [mul_assoc, ← pow_two, vnorm_sq] at h
  have hn := Complex.re_le_norm (-(qform (softM D20) y))
  simp only [Complex.neg_re, norm_neg] at hn
  linarith

end Sarkozy.PositiveRoots.CoherentOldChamber
