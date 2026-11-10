module

public import Sarkozy.PrimeGram.BlockRef

@[expose] public section

/-!
# Non-vacuity of the collision input (PG)

`CollisionBound` (`lem:record:conditional-collision`(d), the one input left of `lem:old-f-law`(f))
holds on the paper's objects with the crude constant `c_col = 4p/(1 - e₀)`
(**`collisionBound_crude`**: `0 ≤ 𝖢_rem ≤ 4` pointwise and Cauchy–Schwarz). So the hypothesis is
satisfiable; its content is the paper's constant `c_col ≈ 5.6` (`c_col q` instead of `4/(1 - e₀)`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents
  Sarkozy.SignedEstimates Sarkozy.MiddleRecords

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

theorem abs_chi_le (a : F) : |(χ a : ℝ)| ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · rcases chiR_ne_cases ha with h | h <;> rw [h] <;> norm_num

theorem Crem_bounds (x y : Fin 3 → F) : 0 ≤ Crem x y ∧ Crem x y ≤ 4 := by
  unfold Crem chA chB Icr
  have hA := abs_le.mp (abs_chi_le (y 2 - x 0))
  have hB := abs_le.mp (abs_chi_le (x 2 - y 0))
  have h1 : 0 ≤ (1 + (χ (y 2 - x 0) : ℝ)) * (1 + (χ (x 2 - y 0) : ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : (1 + (χ (y 2 - x 0) : ℝ)) * (1 + (χ (x 2 - y 0) : ℝ)) ≤ 4 := by nlinarith
  split_ifs <;> constructor <;> linarith

theorem hfI_nonneg' (x : Fin 3 → F) : 0 ≤ hfI x := by
  unfold hfI; split_ifs <;> norm_num

theorem sum_hf_abs_sq (hR : ringChar F ≠ 2) (h19 : 19 ≤ Fintype.card F) (f : (Fin 3 → F) → ℝ) :
    (∑ x, hfI x * |f x| / Hcard (F := F)) ^ 2 ≤ Enu (fun x => f x ^ 2) := by
  have hH := Hcard_pos (F := F) hR h19
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun x => hfI (F := F) x) (fun x => hfI x * |f x|)
  have e1 : ∑ x, hfI (F := F) x * (hfI x * |f x|) = ∑ x, hfI x * |f x| :=
    sum_congr rfl fun x _ => by rw [← mul_assoc, hfI_sq]
  have e2 : ∑ x, hfI (F := F) x ^ 2 = Hcard (F := F) := by
    unfold Hcard Hset hfI
    rw [Finset.card_filter]
    push_cast
    exact sum_congr rfl fun x _ => by split_ifs <;> norm_num
  have e3 : ∑ x, (hfI (F := F) x * |f x|) ^ 2 = ∑ x, hfI x * f x ^ 2 :=
    sum_congr rfl fun x _ => by rw [mul_pow, sq (hfI x), hfI_sq, sq_abs]
  rw [e1, e2, e3] at hcs
  unfold Enu
  rw [← sum_div, ← sum_div, div_pow, div_le_div_iff₀ (pow_pos hH 2) hH]
  nlinarith [hcs]

/-- **Non-vacuity of `CollisionBound`**: it holds with `c_col = 4p/(1 - e₀)`. -/
theorem collisionBound_crude (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)
    (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F) :
    CollisionBound hF (4 * qF / (1 - e0 qF)) := by
  intro f g _ _
  have hH := Hcard_pos (F := F) hR h19
  have he1 := e0_lt_one (F := F) h19
  have h1e : 0 < 1 - e0 qF := by linarith
  have hq : (0 : ℝ) < qF := by
    have : (19 : ℝ) ≤ qF := by exact_mod_cast h19
    linarith
  set a := ∑ x, hfI x * |f x| / Hcard (F := F)
  set b := ∑ y, hfI y * |g y| / Hcard (F := F)
  have ha : 0 ≤ a := sum_nonneg fun x _ => div_nonneg (mul_nonneg (hfI_nonneg' x)
    (abs_nonneg _)) hH.le
  have hb : 0 ≤ b := sum_nonneg fun y _ => div_nonneg (mul_nonneg (hfI_nonneg' y)
    (abs_nonneg _)) hH.le
  -- `|E₂ 𝖢_rem f g| ≤ 4 a b`
  have h1 : |E2 Crem f g| ≤ 4 * (a * b) := by
    unfold E2
    have : a * b = ∑ x, ∑ y, hfI x * hfI y * |f x| * |g y| / Hcard (F := F) ^ 2 := by
      simp only [a, b]
      rw [sum_mul]
      refine sum_congr rfl fun x _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun y _ => ?_
      field_simp
    rw [this, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y _ => ?_)
    obtain ⟨c0, c4⟩ := Crem_bounds x y
    have hx := hfI_nonneg' x
    have hy := hfI_nonneg' y
    rw [abs_div, abs_of_pos (pow_pos hH 2), abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg c0]
    have hP : 0 ≤ hfI x * hfI y * |f x| * |g y| := by positivity
    rw [show 4 * (hfI x * hfI y * |f x| * |g y| / Hcard (F := F) ^ 2) =
      hfI x * hfI y * |f x| * |g y| * 4 / Hcard (F := F) ^ 2 by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left c4 hP) (pow_pos hH 2).le
  -- `a ≤ √(E_ν f²) ≤ ‖f‖/√(1 - e₀)`
  have hsf : a ≤ √(1 / (1 - e0 qF)) * √(mip (m0 hF).weight f f) := by
    rw [← Real.sqrt_mul (div_nonneg zero_le_one h1e.le)]
    calc a = √(a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ √(Enu (fun x => f x ^ 2)) := Real.sqrt_le_sqrt (sum_hf_abs_sq hR h19 f)
      _ ≤ _ := Real.sqrt_le_sqrt (by rw [one_div_mul_eq_div]; exact Enu_sq hF hR h3 h19 f)
  have hsg : b ≤ √(1 / (1 - e0 qF)) * √(mip (m0 hF).weight g g) := by
    rw [← Real.sqrt_mul (div_nonneg zero_le_one h1e.le)]
    calc b = √(b ^ 2) := (Real.sqrt_sq hb).symm
      _ ≤ √(Enu (fun x => g x ^ 2)) := Real.sqrt_le_sqrt (sum_hf_abs_sq hR h19 g)
      _ ≤ _ := Real.sqrt_le_sqrt (by rw [one_div_mul_eq_div]; exact Enu_sq hF hR h3 h19 g)
  have hss : √(1 / (1 - e0 qF)) * √(1 / (1 - e0 qF)) = 1 / (1 - e0 qF) :=
    Real.mul_self_sqrt (div_nonneg zero_le_one h1e.le)
  have hab : a * b ≤ 1 / (1 - e0 qF) *
      (√(mip (m0 hF).weight f f) * √(mip (m0 hF).weight g g)) := by
    calc a * b ≤ (√(1 / (1 - e0 qF)) * √(mip (m0 hF).weight f f)) *
          (√(1 / (1 - e0 qF)) * √(mip (m0 hF).weight g g)) :=
          mul_le_mul hsf hsg hb (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = (√(1 / (1 - e0 qF)) * √(1 / (1 - e0 qF))) *
          (√(mip (m0 hF).weight f f) * √(mip (m0 hF).weight g g)) := by ring
      _ = _ := by rw [hss]
  have e : 4 * qF / (1 - e0 qF) * qF⁻¹ = 4 * (1 / (1 - e0 qF)) := by
    field_simp
  rw [e, mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left hab (by norm_num))

end Sarkozy.PrimeGram
