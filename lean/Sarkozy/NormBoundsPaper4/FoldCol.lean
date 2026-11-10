module

public import Sarkozy.PrimeGram.SanityRef
public import Sarkozy.NormBoundsPaper2.PairAlgebra
public import Sarkozy.SignedDecomp.Paper

@[expose] public section

/-!
# A collision bound for the reference fold record, from the nine coincidences (FD)

`paper/sections/21_middle_records.tex`, `lem:old-f-law`(b), `lem:record:conditional-collision`(d):
the collision part `𝖢_rem = (1 − I_×)(1 + 𝖠)(1 + 𝖡)` of the reference kernel `Ψ₀`.

The paper's sharp `c_col ≈ 5.62` (PG's hypothesis `CollisionBound`, the 18 sign patterns of
`lem:record:conditional-collision`(d)) is not needed for the *fold norm families* `Fs`, `Fa`: there
the collision part only enters the centred norm of the reference record on sectors of at least
two primes, `(Γ_A + e_o r) r`, where a constant `c_col` up to several thousand is still enough.
This file proves the crude bound
* **`collisionBound_nine`**: `CollisionBound hF (36 p³/(|H_F|(1 − e₀)))`, i.e.
  `c_col = 72p²/((p − 1)(p − 2)(1 − e₀))` (about `72`), by the Schur test with
  `0 ≤ 𝖢_rem ≤ 4(1 − I_×) ≤ 4 ∑_{i,j}[x_i = y_j]` and the row sums `∑_y [x_i = y_j] = p²`;
* `collisionBound_mono`; **`collisionBound_73`**: `c_col = 73` for `p ≥ 2^24`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.PrimeGram Sarkozy.SignedComponents Sarkozy.SignedEstimates
open Sarkozy.Labellings Sarkozy.PartV Sarkozy.MiddleRecords
open Sarkozy.NormBoundsPaper2 (abs_le_of_scaled)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "qF" => (Fintype.card F : ℝ)

/-- `∑_{i,j} [x_i = y_j]`. -/
noncomputable def coF (x y : Fin 3 → F) : ℝ := ∑ i, ∑ j, if x i = y j then 1 else 0

omit [Field F] [Fintype F] in
theorem coF_nonneg (x y : Fin 3 → F) : 0 ≤ coF x y :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num

omit [Field F] [Fintype F] in
theorem one_sub_Icr_le (x y : Fin 3 → F) : 1 - Icr x y ≤ coF x y := by
  unfold Icr
  split_ifs with h
  · simp only [sub_self]; exact coF_nonneg x y
  · push Not at h
    obtain ⟨i, j, hij⟩ := h
    have h1 := single_le_sum (f := fun j' => if x i = y j' then (1 : ℝ) else 0)
      (fun j' _ => by split_ifs <;> norm_num) (mem_univ j)
    have h2 := single_le_sum (f := fun i' => ∑ j', if x i' = y j' then (1 : ℝ) else 0)
      (fun i' _ => sum_nonneg fun j' _ => by split_ifs <;> norm_num) (mem_univ i)
    have hval : (if x i = y j then (1 : ℝ) else 0) = 1 := by simp [hij]
    unfold coF
    linarith

theorem Crem_le (x y : Fin 3 → F) : Crem x y ≤ 4 * coF x y := by
  unfold Crem
  have hA := abs_chi_le (F := F) (y 2 - x 0)
  have hB := abs_chi_le (F := F) (x 2 - y 0)
  rw [abs_le] at hA hB
  have h0 : 0 ≤ (1 + (quadraticChar F (y 2 - x 0) : ℝ)) * (1 + (quadraticChar F (x 2 - y 0) : ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  have h4 : (1 + (quadraticChar F (y 2 - x 0) : ℝ)) * (1 + (quadraticChar F (x 2 - y 0) : ℝ)) ≤ 4 :=
    by nlinarith
  have hI : 0 ≤ 1 - Icr x y := by unfold Icr; split_ifs <;> norm_num
  have hI1 : 1 - Icr x y ≤ coF x y := one_sub_Icr_le x y
  unfold PrimeGram.chA PrimeGram.chB
  nlinarith

theorem fibre_count (j : Fin 3) (a : F) :
    ∑ y : Fin 3 → F, (if y j = a then (1 : ℝ) else 0) = qF ^ 2 := by
  have hinv : ∀ a' : F, ∑ y : Fin 3 → F, (if y j = a' then (1 : ℝ) else 0) =
      ∑ y : Fin 3 → F, (if y j = a then (1 : ℝ) else 0) := by
    intro a'
    refine Fintype.sum_equiv (Equiv.addRight (fun _ => a - a')) _ _ fun y => ?_
    simp only [Equiv.coe_addRight, Pi.add_apply]
    by_cases h : y j = a'
    · simp [h]
    · have : y j + (a - a') ≠ a := fun e => h (by linear_combination e)
      simp [h, this]
  have htot : ∑ a' : F, ∑ y : Fin 3 → F, (if y j = a' then (1 : ℝ) else 0) = qF ^ 3 := by
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte, sum_const, card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  simp only [hinv, sum_const, card_univ, nsmul_eq_mul] at htot
  have hq : (0 : ℝ) < qF := by exact_mod_cast Fintype.card_pos
  have : qF * ∑ y : Fin 3 → F, (if y j = a then (1 : ℝ) else 0) = qF * qF ^ 2 := by
    rw [htot]; ring
  exact mul_left_cancel₀ hq.ne' this

theorem row_coF (x : Fin 3 → F) : ∑ y, coF x y = 9 * qF ^ 2 := by
  unfold coF
  rw [sum_comm]
  have h : ∀ i j : Fin 3, ∑ y : Fin 3 → F, (if x i = y j then (1 : ℝ) else 0) = qF ^ 2 :=
    fun i j => by
      rw [← fibre_count j (x i)]
      exact sum_congr rfl fun y _ => by simp only [eq_comm]
  rw [sum_congr rfl fun i _ => (sum_comm).trans (sum_congr rfl fun j _ => h i j)]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem col_coF (y : Fin 3 → F) : ∑ x, coF x y = 9 * qF ^ 2 := by
  unfold coF
  rw [sum_comm]
  have h : ∀ i j : Fin 3, ∑ x : Fin 3 → F, (if x i = y j then (1 : ℝ) else 0) = qF ^ 2 :=
    fun i j => fibre_count i (y j)
  rw [sum_congr rfl fun i _ => (sum_comm).trans (sum_congr rfl fun j _ => h i j)]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

section Bound

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)
  (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)

include hR h3 h19 in
/-- **The collision bound from the nine coincidences**: `c_col = 36p³/(|H_F|(1 − e₀))`. -/
theorem collisionBound_nine :
    CollisionBound hF (36 * qF ^ 3 / (Hcard (F := F) * (1 - e0 qF))) := by
  intro f g _ _
  have hH := Hcard_pos (F := F) hR h19
  have he1 := e0_lt_one (F := F) h19
  have h1e : 0 < 1 - e0 qF := by linarith
  have hq : (0 : ℝ) < qF := by
    have : (19 : ℝ) ≤ qF := by exact_mod_cast h19
    linarith
  -- Schur: `∑∑ hfI hfI |f||g| coF ≤ 9 p² √(∑ hfI f²) √(∑ hfI g²)`
  set Nf := ∑ x, hfI x * f x ^ 2
  set Ng := ∑ y, hfI y * g y ^ 2
  have hNf : 0 ≤ Nf := sum_nonneg fun x _ => mul_nonneg (hfI_nonneg' x) (sq_nonneg _)
  have hNg : 0 ≤ Ng := sum_nonneg fun y _ => mul_nonneg (hfI_nonneg' y) (sq_nonneg _)
  have hS : |∑ x, ∑ y, hfI x * hfI y * f x * g y * Crem x y| ≤
      4 * (9 * qF ^ 2) * Real.sqrt Nf * Real.sqrt Ng := by
    have hc : 0 ≤ 4 * (9 * qF ^ 2) := by positivity
    refine abs_le_of_scaled (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hc fun t ht => ?_
    rw [Real.sq_sqrt hNf, Real.sq_sqrt hNg]
    have hpt : ∀ x y, |hfI x * hfI y * f x * g y * Crem x y| ≤
        4 * coF x y * (t / 2 * (hfI x * f x ^ 2) + 1 / (2 * t) * (hfI y * g y ^ 2)) := by
      intro x y
      obtain ⟨c0, -⟩ := Crem_bounds x y
      have c4 := Crem_le x y
      have hx := hfI_nonneg' x
      have hy := hfI_nonneg' y
      have hx2 : hfI x * hfI x = hfI x := hfI_sq x
      have hy2 : hfI y * hfI y = hfI y := hfI_sq y
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg hy,
        abs_of_nonneg c0]
      have hco := coF_nonneg x y
      have key : hfI x * hfI y * (|f x| * |g y|) ≤
          t / 2 * (hfI x * f x ^ 2) + 1 / (2 * t) * (hfI y * g y ^ 2) := by
        have h0 : 0 ≤ (t * hfI x * |f x| - hfI y * |g y|) ^ 2 := sq_nonneg _
        have e : t / 2 * (hfI x * f x ^ 2) + 1 / (2 * t) * (hfI y * g y ^ 2) =
            (t ^ 2 * (hfI x * hfI x) * |f x| ^ 2 + (hfI y * hfI y) * |g y| ^ 2) / (2 * t) := by
          rw [hx2, hy2, sq_abs, sq_abs]; field_simp
        rw [e, le_div_iff₀ (by positivity)]
        nlinarith
      calc hfI x * hfI y * |f x| * |g y| * Crem x y
          = Crem x y * (hfI x * hfI y * (|f x| * |g y|)) := by ring
        _ ≤ (4 * coF x y) * (hfI x * hfI y * (|f x| * |g y|)) :=
            mul_le_mul_of_nonneg_right c4 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)
    calc |∑ x, ∑ y, hfI x * hfI y * f x * g y * Crem x y|
        ≤ ∑ x, ∑ y, 4 * coF x y * (t / 2 * (hfI x * f x ^ 2) + 1 / (2 * t) * (hfI y * g y ^ 2)) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ =>
            (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y _ => hpt x y))
      _ = 4 * (t / 2 * ∑ x, hfI x * f x ^ 2 * ∑ y, coF x y +
          1 / (2 * t) * ∑ y, hfI y * g y ^ 2 * ∑ x, coF x y) := by
          simp only [mul_add, sum_add_distrib, mul_sum]
          congr 1
          · exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
          · rw [sum_comm]; exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => by ring
      _ = 4 * (9 * qF ^ 2) / 2 * (t * Nf + Ng / t) := by
          simp only [row_coF, col_coF, ← sum_mul]
          field_simp
          rfl
  -- normalize
  have hE : E2 Crem f g =
      (∑ x, ∑ y, hfI x * hfI y * f x * g y * Crem x y) / Hcard (F := F) ^ 2 := by
    unfold E2; rw [sum_div]; exact sum_congr rfl fun x _ => by rw [sum_div]
  have hf : Real.sqrt Nf ≤ Real.sqrt (Hcard (F := F) / (1 - e0 qF)) *
      Real.sqrt (mip (m0 hF).weight f f) := by
    rw [← Real.sqrt_mul (div_nonneg hH.le h1e.le)]
    refine Real.sqrt_le_sqrt ?_
    have := Enu_sq hF hR h3 h19 f
    unfold Enu at this
    rw [← sum_div, div_le_div_iff₀ hH h1e] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ h1e]
    linarith
  have hg : Real.sqrt Ng ≤ Real.sqrt (Hcard (F := F) / (1 - e0 qF)) *
      Real.sqrt (mip (m0 hF).weight g g) := by
    rw [← Real.sqrt_mul (div_nonneg hH.le h1e.le)]
    refine Real.sqrt_le_sqrt ?_
    have := Enu_sq hF hR h3 h19 g
    unfold Enu at this
    rw [← sum_div, div_le_div_iff₀ hH h1e] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ h1e]
    linarith
  have hss : Real.sqrt (Hcard (F := F) / (1 - e0 qF)) * Real.sqrt (Hcard (F := F) / (1 - e0 qF))
      = Hcard (F := F) / (1 - e0 qF) := Real.mul_self_sqrt (div_nonneg hH.le h1e.le)
  rw [hE, abs_div, abs_of_pos (pow_pos hH 2), div_le_iff₀ (pow_pos hH 2)]
  have hP : 0 ≤ 4 * (9 * qF ^ 2) := by positivity
  calc _ ≤ 4 * (9 * qF ^ 2) * Real.sqrt Nf * Real.sqrt Ng := hS
    _ ≤ 4 * (9 * qF ^ 2) * (Real.sqrt (Hcard (F := F) / (1 - e0 qF)) *
          Real.sqrt (mip (m0 hF).weight f f)) * (Real.sqrt (Hcard (F := F) / (1 - e0 qF)) *
          Real.sqrt (mip (m0 hF).weight g g)) := by
        gcongr
    _ = 4 * (9 * qF ^ 2) * (Real.sqrt (Hcard (F := F) / (1 - e0 qF)) *
          Real.sqrt (Hcard (F := F) / (1 - e0 qF))) * (Real.sqrt (mip (m0 hF).weight f f) *
          Real.sqrt (mip (m0 hF).weight g g)) := by ring
    _ = _ := by
        rw [hss]
        field_simp
        ring

end Bound

theorem collisionBound_mono (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) {c c' : ℝ}
    (h : CollisionBound hF c) (hc : c ≤ c') : CollisionBound hF c' := by
  intro f g hf hg
  refine (h f g hf hg).trans ?_
  have hq : (0 : ℝ) ≤ qF⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have := mul_nonneg (Real.sqrt_nonneg (mip (m0 hF).weight f f))
    (Real.sqrt_nonneg (mip (m0 hF).weight g g))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hq) this

/-- **`c_col = 73` for `p ≥ 2^24`.** -/
theorem collisionBound_73 (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)
    (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h24 : 2 ^ 24 ≤ Fintype.card F) :
    CollisionBound hF 73 := by
  have h19 : 19 ≤ Fintype.card F := le_trans (by norm_num) h24
  refine collisionBound_mono hF (collisionBound_nine hF hR h3 h19) ?_
  rw [Hcard_eq hR]
  have hq : (2 : ℝ) ^ 24 ≤ qF := by exact_mod_cast h24
  have he := Sarkozy.SignedDecomp.e0_lt hq
  have he0 := e0_nonneg (F := F) h19
  have h1 : 0 < qF - 1 := by linarith
  have h2 : 0 < qF - 2 := by linarith
  have h1e : 999 / 1000 ≤ 1 - e0 qF := by linarith
  have hA : 0 ≤ qF * (qF - 1) * (qF - 2) := by positivity
  rw [div_le_iff₀ (by
    have : 0 < 1 - e0 qF := by linarith
    positivity)]
  have k1 : 73 * (qF * (qF - 1) * (qF - 2) / 2) * (999 / 1000) ≤
      73 * (qF * (qF - 1) * (qF - 2) / 2) * (1 - e0 qF) :=
    mul_le_mul_of_nonneg_left h1e (by positivity)
  have k2 : 36 * qF ^ 3 ≤ 73 * (qF * (qF - 1) * (qF - 2) / 2) * (999 / 1000) := by
    have hq0 : 0 ≤ qF := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hq (mul_nonneg hq0 hq0)]
  linarith

end Sarkozy.NormBoundsPaper4
