module

public import Sarkozy.F3Kernel.WeightBounds

/-!
# Exact rational arithmetic at the production anchor

The stored production factor tables use the anchor `2^60`. The `rP3` filenames of the
refiner inputs change the optimization parameter only, not this numerical anchor.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

def productionAnchor : ℕ := 2 ^ 60

theorem productionAnchor_pos : (0 : ℝ) < productionAnchor := by
  norm_num [productionAnchor]

theorem sqrt_productionAnchor : Real.sqrt (productionAnchor : ℝ) = 2 ^ 30 := by
  apply (Real.sqrt_eq_iff_mul_self_eq productionAnchor_pos.le (by positivity)).mpr
  norm_num [productionAnchor]

def rationalGraded (t m : ℕ) : ℚ :=
  (if t = 0 then 0 else ((t : ℚ) - 3) * 2 ^ (t - 1) + 2) / 2 ^ 30 +
    ((if t = 0 then 0 else 2 ^ (t - 1) - 1) + 2 ^ t * m) / 2 ^ 60

theorem rationalGraded_eq (t m : ℕ) :
    (rationalGraded t m : ℝ) = grGraded productionAnchor t m := by
  rw [gp_grGraded_eq productionAnchor_pos, sqrt_productionAnchor]
  unfold rationalGraded gradedA gradedB
  split_ifs <;> push_cast <;> ring

theorem rationalGraded10_lt_one : (rationalGraded 10 36 : ℝ) < 1 := by
  norm_num [rationalGraded]

theorem gpEhat_le_rational (H : OrientedGraph (Fin 36))
    (hd : univ.sup (rowsDeg0 H) ≤ 10) :
    gpEhat H productionAnchor 36 ≤ (rationalGraded 10 36 : ℝ) := by
  rw [rationalGraded_eq]
  exact (grErr_graded productionAnchor_pos 36).mono 36 (by norm_num) _ _ hd

theorem gpEhat_anchor_lt_one (H : OrientedGraph (Fin 36))
    (hd : univ.sup (rowsDeg0 H) ≤ 10) : gpEhat H productionAnchor 36 < 1 :=
  (gpEhat_le_rational H hd).trans_lt rationalGraded10_lt_one

def rationalFactor (s m B : ℕ) : ℚ :=
  (1 + rationalGraded s m + 2 ^ s * B / 2 ^ 60) / (1 - rationalGraded 10 36)

theorem rationalFactor_cast (s m B : ℕ) :
    (rationalFactor s m B : ℝ) =
      (1 + grGraded productionAnchor s m +
        (Real.sqrt (productionAnchor : ℝ))⁻¹ ^ 2 * 2 ^ s * B) /
          (1 - (rationalGraded 10 36 : ℝ)) := by
  unfold rationalFactor
  push_cast
  rw [rationalGraded_eq, sqrt_productionAnchor]
  ring

theorem anchor_factor_bound (H : OrientedGraph (Fin 36))
    (hd : univ.sup (rowsDeg0 H) ≤ 10) (s m B : ℕ) {S : ℝ} (hS : S ≤ B) :
    (1 + grGraded productionAnchor s m +
      (Real.sqrt (productionAnchor : ℝ))⁻¹ ^ 2 * 2 ^ s * S) /
        (1 - gpEhat H productionAnchor 36) ≤ (rationalFactor s m B : ℝ) := by
  rw [rationalFactor_cast]
  have he := gpEhat_le_rational H hd
  have hden := rationalGraded10_lt_one
  have he0 := gp_grGraded_nonneg productionAnchor_pos s (Nat.cast_nonneg m)
  apply div_le_div₀
  · positivity
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hS
      (by positivity : (0 : ℝ) ≤ (Real.sqrt (productionAnchor : ℝ))⁻¹ ^ 2 * 2 ^ s))
  · linarith
  · linarith

theorem grLeafFm_anchor_le (H : OrientedGraph (Fin 36)) (sgn : Fin 36 → Fin 36 → ℤ)
    (hd : univ.sup (rowsDeg0 H) ≤ 10) (s B : ℕ)
    (hB : leafS H sgn (weightM H sgn) s ≤ B) :
    grLeafFm H sgn (grGraded productionAnchor) productionAnchor 36
      (gpEhat H productionAnchor 36) s ≤ (rationalFactor s 36 B : ℝ) :=
  anchor_factor_bound H hd s 36 B hB

theorem grLeafFrho_anchor_le (H : OrientedGraph (Fin 36)) (sgn : Fin 36 → Fin 36 → ℤ)
    (hd : univ.sup (rowsDeg0 H) ≤ 10) (s B : ℕ)
    (hB : leafS H sgn (weightRho H sgn) s ≤ B) :
    grLeafFrho H sgn (grGraded productionAnchor) productionAnchor 36
      (gpEhat H productionAnchor 36) s ≤ (rationalFactor s 72 B : ℝ) := by
  simpa only [grLeafFrho, Nat.cast_ofNat, show (2 : ℝ) * 36 = 72 by norm_num] using
    anchor_factor_bound H hd s 72 B hB

end Sarkozy.F3Kernel
