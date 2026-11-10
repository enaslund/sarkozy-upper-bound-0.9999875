module

public import Sarkozy.SignedComponents.Estimates

@[expose] public section

/-!
# Character sums over one label and over the fold halves (E1)

`paper/sections/21_middle_records.tex`, `subsec:middle-records:notation`, `lem:paley-triple`(a),(b)
(`paper/sections/12_labellings.tex`).

The elementary sums behind the explicit Paley counts of `lem:signed-components`(b) and
`lem:old-f-law`(a), with `χ` read in `ℝ`:

* `chiR_cases`, `chiR_sq` (`χ(a)² = 1 - [a = 0]`), `chiR_swap` (`χ(-1) = -1`);
* `sumR_chi`, `sumR_chi_mul` (`∑_z χ(z - a) χ(z - b) = p[a = b] - 1`, `lem:paley-triple`(b));
* `sum_excl2` (a sum over the labels other than two), `sum_out`, `sum_in` (a sum over the out- or
  in-neighbours of a label, through `2·1[χ(z - c) = 1] = 1 + χ(z - c) - [z = c]`);
* **`sumHF`**: a sum over the halves `H_F` as the iterated sum over `y₀`, then `y₂` with
  `y₀ → y₂`, then `y₁ ∉ {y₀, y₂}`;
* **`Hcard_eq`**: `|H_F| = p(p - 1)(p - 2)/2` (`subsec:middle-records:notation`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedEstimates

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-! ## One label -/

theorem chiR_cases (a : F) : (χ a : ℝ) = 0 ∨ (χ a : ℝ) = 1 ∨ (χ a : ℝ) = -1 := by
  rcases chi_cases a with h | h | h <;> simp [h]

theorem chiR_sq (a : F) : (χ a : ℝ) * χ a = 1 - (if a = 0 then 1 else 0) := by
  by_cases ha : a = 0
  · simp [ha]
  · have h := quadraticChar_sq_one ha
    have h' : ((χ a : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast h
    simp only [ha, ↓reduceIte, sub_zero]
    rw [← sq, h']

theorem chiR_sq_ne {a : F} (ha : a ≠ 0) : (χ a : ℝ) * χ a = 1 := by
  rw [chiR_sq]; simp [ha]

theorem chiR_eq_zero {a : F} : (χ a : ℝ) = 0 ↔ a = 0 := by
  rw [Int.cast_eq_zero, quadraticChar_eq_zero_iff]

theorem chiR_ne_cases {a : F} (ha : a ≠ 0) : (χ a : ℝ) = 1 ∨ (χ a : ℝ) = -1 := by
  rcases quadraticChar_dichotomy ha with h | h <;> simp [h]

theorem chiR_swap (h3 : Fintype.card F % 4 = 3) (a b : F) : (χ (a - b) : ℝ) = -χ (b - a) := by
  rw [chi_swap h3 a b]; push_cast; ring

theorem sumR_chi (hR : ringChar F ≠ 2) (a : F) : ∑ z, (χ (z - a) : ℝ) = 0 := by
  have h := sum_chi_shift hR a
  exact_mod_cast h

theorem sumR_chi_mul (hR : ringChar F ≠ 2) (a b : F) :
    ∑ z, (χ (z - a) : ℝ) * χ (z - b) = (if a = b then (Fintype.card F : ℝ) else 0) - 1 := by
  have h := sum_chi_mul_chi hR a b
  have h' : ((∑ t, χ (t - a) * χ (t - b) : ℤ) : ℝ) =
      (((if a = b then (Fintype.card F : ℤ) else 0) - 1 : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  rw [h']

theorem sumR_chi_mul_ne (hR : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ z, (χ (z - a) : ℝ) * χ (z - b) = -1 := by
  rw [sumR_chi_mul hR]; simp [hab]

omit [Field F] in
/-- A sum over the labels other than `c ≠ z`. -/
theorem sum_excl2 {c z : F} (hcz : c ≠ z) (K : ℝ) (g : F → ℝ) :
    ∑ w, (if w ≠ c ∧ w ≠ z then K * g w else 0) = K * (∑ w, g w - g c - g z) := by
  have e : ∀ w, (if w ≠ c ∧ w ≠ z then K * g w else 0) =
      K * g w - (if c = w then K * g w else 0) - (if z = w then K * g w else 0) := by
    intro w
    by_cases h1 : w = c
    · subst h1; simp [hcz, Ne.symm hcz]
    · by_cases h2 : w = z
      · subst h2; simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  simp only [e, sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← mul_sum]
  ring

/-- **A sum over the out-neighbours of `c`**: `2·1[χ(z - c) = 1] = 1 + χ(z - c) - [z = c]`. -/
theorem sum_out (c : F) (g : F → ℝ) :
    ∑ z, (if χ (z - c) = 1 then g z else 0) =
      (∑ z, g z + ∑ z, (χ (z - c) : ℝ) * g z - g c) / 2 := by
  have e : ∀ z, (if χ (z - c) = 1 then g z else 0) =
      (g z + (χ (z - c) : ℝ) * g z - (if c = z then g z else 0)) / 2 := by
    intro z
    by_cases hz : z = c
    · subst hz; simp
    · have hne : z - c ≠ 0 := sub_ne_zero.mpr hz
      rcases quadraticChar_dichotomy hne with h | h <;> simp [h, Ne.symm hz]
  rw [sum_congr rfl fun z _ => e z, ← sum_div, sum_sub_distrib, sum_add_distrib, sum_ite_eq]
  simp

/-- **A sum over the in-neighbours of `c`.** -/
theorem sum_in (h3 : Fintype.card F % 4 = 3) (c : F) (g : F → ℝ) :
    ∑ z, (if χ (c - z) = 1 then g z else 0) =
      (∑ z, g z - ∑ z, (χ (z - c) : ℝ) * g z - g c) / 2 := by
  have e : ∀ z, (if χ (c - z) = 1 then g z else 0) =
      (g z - (χ (z - c) : ℝ) * g z - (if c = z then g z else 0)) / 2 := by
    intro z
    by_cases hz : z = c
    · subst hz; simp
    · have hne : z - c ≠ 0 := sub_ne_zero.mpr hz
      have hsw := chi_swap h3 c z
      rcases quadraticChar_dichotomy hne with h | h <;> rw [hsw, h] <;>
        simp [Ne.symm hz]
  rw [sum_congr rfl fun z _ => e z, ← sum_div, sum_sub_distrib, sum_sub_distrib, sum_ite_eq]
  simp

omit [Field F] [DecidableEq F] in
theorem sum_ite_congr {P : F → Prop} [DecidablePred P] {A G : F → ℝ}
    (h : ∀ z, P z → A z = G z) :
    ∑ z, (if P z then A z else 0) = ∑ z, (if P z then G z else 0) :=
  sum_congr rfl fun z _ => by split_ifs with hz <;> simp [h z, hz]

/-! ## The halves -/

/-- The triples as `(y₀, y₂, y₁)`. -/
def tri : F × F × F ≃ (Fin 3 → F) where
  toFun t := ![t.1, t.2.2, t.2.1]
  invFun y := (y 0, y 2, y 1)
  left_inv _ := rfl
  right_inv y := by funext i; fin_cases i <;> rfl

theorem HF_tri (c w z : F) : HF ![c, w, z] ↔ χ (z - c) = 1 ∧ w ≠ c ∧ w ≠ z := by
  unfold HF
  constructor
  · rintro ⟨hi, he⟩
    refine ⟨he, fun e => ?_, fun e => ?_⟩
    · exact absurd (@hi 1 0 (by simp [e])) (by decide)
    · exact absurd (@hi 1 2 (by simp [e])) (by decide)
  · rintro ⟨he, h1, h2⟩
    have hcz : c ≠ z := by
      rintro rfl
      rw [sub_self, quadraticChar_zero] at he
      exact zero_ne_one he
    exact ⟨injective_three (Ne.symm h1) hcz h2, he⟩

/-- **A sum over the halves `H_F`**: `y₀ = c`, then `y₂ = z` with `c → z`, then
`y₁ = w ∉ {c, z}`. -/
theorem sumHF (f : (Fin 3 → F) → ℝ) :
    ∑ y, (if HF y then f y else 0) =
      ∑ c, ∑ z, if χ (z - c) = 1 then ∑ w, (if w ≠ c ∧ w ≠ z then f ![c, w, z] else 0)
        else 0 := by
  rw [← Equiv.sum_comp tri, Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun z _ => ?_
  split_ifs with hz
  · refine sum_congr rfl fun w _ => ?_
    change (if HF ![c, w, z] then f ![c, w, z] else 0) = _
    simp only [HF_tri, hz, true_and]
  · refine sum_eq_zero fun w _ => ?_
    change (if HF ![c, w, z] then f ![c, w, z] else 0) = 0
    have hn : ¬ HF ![c, w, z] := by rw [HF_tri]; exact fun h => hz h.1
    simp only [hn, ↓reduceIte]

theorem HF_ne {x : Fin 3 → F} (hx : HF x) : x 0 ≠ x 1 ∧ x 0 ≠ x 2 ∧ x 1 ≠ x 2 :=
  ⟨fun e => absurd (hx.1 e) (by decide), fun e => absurd (hx.1 e) (by decide),
    fun e => absurd (hx.1 e) (by decide)⟩

theorem ne_of_chi_one {a b : F} (h : χ (a - b) = 1) : a ≠ b := by
  rintro rfl
  rw [sub_self, quadraticChar_zero] at h
  exact zero_ne_one h

/-- **`|H_F| = p(p - 1)(p - 2)/2`.** -/
theorem Hcard_eq (hR : ringChar F ≠ 2) :
    Hcard (F := F) = (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) *
      ((Fintype.card F : ℝ) - 2) / 2 := by
  have e : Hcard (F := F) = ∑ y : Fin 3 → F, (if HF y then (fun _ => (1 : ℝ)) y else 0) := by
    unfold Hcard Hset
    rw [card_filter]
    push_cast
    rfl
  rw [e, sumHF]
  have h1 : ∀ c, ∑ z, (if χ (z - c) = 1 then
      ∑ w, (if w ≠ c ∧ w ≠ z then (fun _ => (1 : ℝ)) ![c, w, z] else 0) else 0) =
      ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) / 2 := by
    intro c
    rw [sum_ite_congr (G := fun _ => (Fintype.card F : ℝ) - 2) (fun z hz => by
      have := sum_excl2 (ne_of_chi_one hz).symm 1 (fun _ => (1 : ℝ))
      simp only [one_mul, mul_one] at this
      simp only [this, sum_const, card_univ, nsmul_eq_mul, mul_one]
      ring)]
    rw [sum_out]
    simp only [sum_const, card_univ, nsmul_eq_mul, ← sum_mul, sumR_chi hR]
    ring
  simp only [h1, sum_const, card_univ, nsmul_eq_mul]
  ring

end Sarkozy.SignedEstimates
