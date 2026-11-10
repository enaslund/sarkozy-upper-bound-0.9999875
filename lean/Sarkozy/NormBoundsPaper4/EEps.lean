module

public import Sarkozy.NormBoundsPaper4.EOrthB

@[expose] public section

/-!
# The coincidence remainder `ε_E` (`lem:record:e-law`(d); FD)

`paper/sections/21_middle_records.tex`, `lem:record:e-law`(d) and its proof: "Write
`1 − I_× = ∑_{i,j} δ_{ij} − ε_E`. Then `ε_E ≥ 0`, `‖ε_E‖ ≤ 18q²/(1 − q)` … With `κ = ∑δ_{ij}`,
`ε_E = κ − 1_{κ≥1}` is bounded by the sum of `δ_{ij}δ_{i'j'}` over the 18 compatible pairs, and
given `x` two prescribed labels of `y` at two prescribed positions have probability
`1/(p(p − 1))`; the Schur test gives the bound."

* `Ai x y i = ∑_j [x_i = y_j]` (`0` or `1` for injective `y`, `Ai_cases`);
* `ind6_prod`: for injective halves `I_× = ∏_i (1 − A_i)`; `coinc = ∑_i A_i`;
* **`epsE_le`**: `|ε_E(x, y)| ≤ [x inj][y inj] ∑_{i<k} A_i A_k` (the compatible pairs);
* the Schur sums `row_pairs`, `col_pairs` (`≤ 18(p − 2)`, from `cnt_one`, `cnt_two`);
* **`ePrime_eps`**: the field `eps` of `EPrimeInputs`; **`ePrimeInputs`**: both fields, so
  **`eOrthPaperInput`**: NB3's `EOrthPaperInput` (`lem:record:e-orthogonal`(c) at the paper's
  `s^E_p`) **is proved**.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.NormBoundsPaper3
open Sarkozy.NormBoundsPaper2 (abs_le_of_scaled)

variable {p : ℕ} [Fact p.Prime]

local notation "T3" => (ZMod p × ZMod p) × ZMod p

/-- `A_i = ∑_j [x_i = y_j]`. -/
noncomputable def Ai (x y : T3) (i : Fin 3) : ℝ := ∑ j, dl (crd i x) (crd j y)

omit [Fact p.Prime] in
theorem dl_nonneg (a b : ZMod p) : 0 ≤ dl a b := by unfold dl; split_ifs <;> norm_num

omit [Fact p.Prime] in
theorem Ai_nonneg (x y : T3) (i : Fin 3) : 0 ≤ Ai x y i :=
  sum_nonneg fun _ _ => dl_nonneg _ _

omit [Fact p.Prime] in
theorem Ai_le_one (x y : T3) (hy : Inj3 y) (i : Fin 3) : Ai x y i ≤ 1 := by
  obtain ⟨h01, h20, h21⟩ := hy
  unfold Ai dl
  simp only [Fin.sum_univ_three, crd0, crd1, crd2]
  by_cases a : crd i x = y.1.1
  · simp [a, h01, Ne.symm h20]
  · by_cases b : crd i x = y.1.2
    · simp [b, Ne.symm h01, Ne.symm h21]
    · by_cases c : crd i x = y.2
      · simp [c, h20, h21]
      · simp [a, b, c]

omit [Fact p.Prime] in
theorem crd_ne (x : T3) (hx : Inj3 x) {i k : Fin 3} (hik : i ≠ k) : crd i x ≠ crd k x := by
  obtain ⟨h01, h20, h21⟩ := hx
  fin_cases i <;> fin_cases k
  all_goals first | exact absurd rfl hik | exact h01 | exact fun e => h01 e.symm | exact h20 |
    exact fun e => h20 e.symm | exact h21 | exact fun e => h21 e.symm

omit [Fact p.Prime] in
theorem coinc_Ai (x y : T3) : coinc x y = Ai x y 0 + Ai x y 1 + Ai x y 2 := by
  rw [coinc_eq]; unfold Ai; rw [Fin.sum_univ_three]

omit [Fact p.Prime] in
theorem asm_fst (x y : T3) (i : Fin 3) : asm x y (i, 0) = crd i x := rfl

omit [Fact p.Prime] in
theorem asm_snd (x y : T3) (j : Fin 3) : asm x y (j, 1) = crd j y := rfl

omit [Fact p.Prime] in
/-- `I_× = ∏_i (1 − A_i)` for injective halves. -/
theorem ind6_prod (x y : T3) (hx : Inj3 x) (hy : Inj3 y) :
    ind6 x y = (1 - Ai x y 0) * (1 - Ai x y 1) * (1 - Ai x y 2) := by
  by_cases hz : Function.Injective (asm x y)
  · have h0 : ∀ i, Ai x y i = 0 := fun i => by
      unfold Ai
      refine sum_eq_zero fun j _ => ?_
      have : crd i x ≠ crd j y := fun e => by
        have := hz (show asm x y (i, 0) = asm x y (j, 1) by rw [asm_fst, asm_snd, e])
        simp at this
      simp [dl, this]
    simp [ind6, hz, h0]
  · have hex : ∃ i j, crd i x = crd j y := by
      by_contra hne
      push Not at hne
      exact hz (inj_asm x y hx hy (hne 0 0) (hne 0 1) (hne 0 2) (hne 1 0) (hne 1 1) (hne 1 2)
        (hne 2 0) (hne 2 1) (hne 2 2))
    obtain ⟨i, j, hij⟩ := hex
    have h1 : Ai x y i = 1 := by
      refine le_antisymm (Ai_le_one x y hy i) ?_
      unfold Ai
      calc (1 : ℝ) = dl (crd i x) (crd j y) := by simp [dl, hij]
        _ ≤ ∑ j', dl (crd i x) (crd j' y) :=
          single_le_sum (f := fun j' => dl (crd i x) (crd j' y)) (fun j' _ => dl_nonneg _ _)
            (mem_univ j)
    simp only [ind6, hz, ↓reduceIte]
    fin_cases i <;> simp_all

omit [Fact p.Prime] in
/-- **`|ε_E| ≤ [x inj][y inj] ∑_{i<k} A_i A_k`** (the 18 compatible coincidence pairs). -/
theorem epsE_le (x y : T3) :
    |epsE x y| ≤ ind3 x * ind3 y *
      (Ai x y 0 * Ai x y 1 + Ai x y 0 * Ai x y 2 + Ai x y 1 * Ai x y 2) := by
  by_cases hx : Inj3 x
  · by_cases hy : Inj3 y
    · have i1 : ind3 x = 1 := by simp [ind3, hx]
      have i2 : ind3 y = 1 := by simp [ind3, hy]
      unfold epsE
      rw [ind6_prod x y hx hy, coinc_Ai, i1, i2]
      have a0 := Ai_nonneg x y 0
      have a1 := Ai_nonneg x y 1
      have a2 := Ai_nonneg x y 2
      have b0 := Ai_le_one x y hy 0
      have b1 := Ai_le_one x y hy 1
      have b2 := Ai_le_one x y hy 2
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg (mul_nonneg a0 a1) a2, mul_nonneg a0 a1,
          mul_le_mul_of_nonneg_left b2 (mul_nonneg a0 a1)]
      · nlinarith [mul_nonneg (mul_nonneg a0 a1) a2]
    · have i2 : ind3 y = 0 := by simp [ind3, hy]
      have h6 : ind6 x y = 0 := le_antisymm (by simpa [i2] using ind6_le x y) (ind6_nonneg x y)
      simp [epsE, h6, i2]
  · have i1 : ind3 x = 0 := by simp [ind3, hx]
    have h6 : ind6 x y = 0 := le_antisymm (by simpa [i1] using ind6_le x y) (ind6_nonneg x y)
    simp [epsE, h6, i1]

/-! ## The Schur sums -/

omit [Fact p.Prime] in
theorem dl_comm (a b : ZMod p) : dl a b = dl b a := by
  unfold dl
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

theorem sum_dl_dl (a b : ZMod p) : ∑ s, dl a s * dl b s = dl a b := by
  unfold dl
  by_cases h : a = b
  · subst h; simp
  · simp only [mul_ite, mul_one, mul_zero, h, ↓reduceIte]
    rw [sum_eq_zero]
    intro s _
    split_ifs with h1 h2 <;> simp_all

theorem sum_dl_left (a : ZMod p) : ∑ s, dl a s = 1 := by unfold dl; simp

theorem sum_dl_right (a : ZMod p) : ∑ s, dl s a = 1 := by unfold dl; simp

theorem row_term (hp : 3 ≤ p) (x : T3) (hx : Inj3 x) {i k : Fin 3} (hik : i ≠ k) (j l : Fin 3) :
    ∑ y : T3, ind3 y * (dl (crd i x) (crd j y) * dl (crd k x) (crd l y)) ≤
      if j = l then 0 else (p : ℝ) - 2 := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  by_cases hjl : j = l
  · subst hjl
    simp only [↓reduceIte]
    have h := cnt_one j (fun s => dl (crd i x) s * dl (crd k x) s)
    rw [sum_dl_dl] at h
    have hz : dl (crd i x) (crd k x) = 0 := by simp [dl, crd_ne x hx hik]
    rw [hz, mul_zero] at h
    exact le_of_eq h
  · simp only [hjl, ↓reduceIte]
    rw [cnt_two hjl (fun s => dl (crd i x) s) (fun s => dl (crd k x) s), sum_dl_left,
      sum_dl_left, sum_dl_dl]
    have := dl_nonneg (crd i x) (crd k x)
    nlinarith

theorem col_term (hp : 3 ≤ p) (y : T3) {i k : Fin 3} (hik : i ≠ k) (j l : Fin 3) :
    ∑ x : T3, ind3 x * (dl (crd i x) (crd j y) * dl (crd k x) (crd l y)) ≤
      if j = l then 0 else (p : ℝ) - 2 := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  rw [cnt_two hik (fun s => dl s (crd j y)) (fun s => dl s (crd l y)), sum_dl_right,
    sum_dl_right]
  have e : ∑ t, dl t (crd j y) * dl t (crd l y) = dl (crd j y) (crd l y) := by
    rw [← sum_dl_dl]; exact sum_congr rfl fun t _ => by rw [dl_comm t, dl_comm t]
  rw [e]
  by_cases hjl : j = l
  · subst hjl; simp [dl]
  · simp only [hjl, ↓reduceIte]
    have := dl_nonneg (crd j y) (crd l y)
    nlinarith

omit [Fact p.Prime] in
theorem pairs_expand (x y : T3) (i k : Fin 3) :
    Ai x y i * Ai x y k = ∑ j, ∑ l, dl (crd i x) (crd j y) * dl (crd k x) (crd l y) := by
  unfold Ai; rw [sum_mul_sum]

theorem sum_offdiag (c : ℝ) : ∑ j : Fin 3, ∑ l : Fin 3, (if j = l then 0 else c) = 6 * c := by
  simp [Fin.sum_univ_three]; ring

/-- The kernel of the Schur test. -/
noncomputable def Kp (x y : T3) : ℝ :=
  ind3 x * ind3 y * (Ai x y 0 * Ai x y 1 + Ai x y 0 * Ai x y 2 + Ai x y 1 * Ai x y 2)

omit [Fact p.Prime] in
theorem Kp_nonneg (x y : T3) : 0 ≤ Kp x y := by
  unfold Kp
  have := Ai_nonneg x y 0
  have := Ai_nonneg x y 1
  have := Ai_nonneg x y 2
  have := ind3_nonneg x
  have := ind3_nonneg y
  positivity

theorem pair_sum_le_row (hp : 3 ≤ p) (x : T3) (hx : Inj3 x) {i k : Fin 3} (hik : i ≠ k) :
    ∑ y, ind3 y * (Ai x y i * Ai x y k) ≤ 6 * ((p : ℝ) - 2) := by
  simp only [pairs_expand, mul_sum]
  rw [sum_comm]
  calc _ = ∑ j, ∑ l, ∑ y : T3, ind3 y * (dl (crd i x) (crd j y) * dl (crd k x) (crd l y)) := by
        refine sum_congr rfl fun j _ => ?_; rw [sum_comm]
    _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, (if j = l then 0 else (p : ℝ) - 2) :=
        sum_le_sum fun j _ => sum_le_sum fun l _ => row_term hp x hx hik j l
    _ = _ := sum_offdiag _

theorem pair_sum_le_col (hp : 3 ≤ p) (y : T3) {i k : Fin 3} (hik : i ≠ k) :
    ∑ x, ind3 x * (Ai x y i * Ai x y k) ≤ 6 * ((p : ℝ) - 2) := by
  simp only [pairs_expand, mul_sum]
  rw [sum_comm]
  calc _ = ∑ j, ∑ l, ∑ x : T3, ind3 x * (dl (crd i x) (crd j y) * dl (crd k x) (crd l y)) := by
        refine sum_congr rfl fun j _ => ?_; rw [sum_comm]
    _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, (if j = l then 0 else (p : ℝ) - 2) :=
        sum_le_sum fun j _ => sum_le_sum fun l _ => col_term hp y hik j l
    _ = _ := sum_offdiag _

theorem row_pairs (hp : 3 ≤ p) (x : T3) : ∑ y, Kp x y ≤ 18 * ((p : ℝ) - 2) * ind3 x := by
  by_cases hx : Inj3 x
  · have i1 : ind3 x = 1 := by simp [ind3, hx]
    have e : ∑ y, Kp x y = ∑ y, ind3 y * (Ai x y 0 * Ai x y 1) +
        ∑ y, ind3 y * (Ai x y 0 * Ai x y 2) + ∑ y, ind3 y * (Ai x y 1 * Ai x y 2) := by
      unfold Kp; rw [i1, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun y _ => by ring
    rw [e, i1]
    have := pair_sum_le_row hp x hx (show (0 : Fin 3) ≠ 1 by decide)
    have := pair_sum_le_row hp x hx (show (0 : Fin 3) ≠ 2 by decide)
    have := pair_sum_le_row hp x hx (show (1 : Fin 3) ≠ 2 by decide)
    linarith
  · have i1 : ind3 x = 0 := by simp [ind3, hx]
    simp [Kp, i1]

theorem col_pairs (hp : 3 ≤ p) (y : T3) : ∑ x, Kp x y ≤ 18 * ((p : ℝ) - 2) * ind3 y := by
  by_cases hy : Inj3 y
  · have i2 : ind3 y = 1 := by simp [ind3, hy]
    have e : ∑ x, Kp x y = ∑ x, ind3 x * (Ai x y 0 * Ai x y 1) +
        ∑ x, ind3 x * (Ai x y 0 * Ai x y 2) + ∑ x, ind3 x * (Ai x y 1 * Ai x y 2) := by
      unfold Kp; rw [i2, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [e, i2]
    have := pair_sum_le_col hp y (show (0 : Fin 3) ≠ 1 by decide)
    have := pair_sum_le_col hp y (show (0 : Fin 3) ≠ 2 by decide)
    have := pair_sum_le_col hp y (show (1 : Fin 3) ≠ 2 by decide)
    linarith
  · have i2 : ind3 y = 0 := by simp [ind3, hy]
    simp [Kp, i2]

/-- **The field `eps` of `EPrimeInputs`** (`lem:record:e-law`(d), Schur). -/
theorem ePrime_eps (hp : 3 ≤ p) (u v : T3 → ℝ) :
    |Ef u v| ≤ 18 * ((p : ℝ) - 2) * Real.sqrt (Nq u) * Real.sqrt (Nq v) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hR : 0 ≤ 18 * ((p : ℝ) - 2) := by linarith
  refine abs_le_of_scaled (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hR fun t ht => ?_
  rw [Real.sq_sqrt (Nq_nonneg u), Real.sq_sqrt (Nq_nonneg v)]
  have h1 : |Ef u v| ≤ ∑ x, ∑ y, Kp x y * (|u x| * |v y|) := by
    unfold Ef
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ =>
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y _ => ?_))
    rw [abs_mul, abs_mul]
    have := epsE_le x y
    have h0 : 0 ≤ |u x| * |v y| := by positivity
    calc |epsE x y| * |u x| * |v y| = |epsE x y| * (|u x| * |v y|) := by ring
      _ ≤ Kp x y * (|u x| * |v y|) := mul_le_mul_of_nonneg_right this h0
  have h2 : ∀ x y, Kp x y * (|u x| * |v y|) ≤
      Kp x y * (t / 2 * u x ^ 2 + 1 / (2 * t) * v y ^ 2) := fun x y => by
    refine mul_le_mul_of_nonneg_left ?_ (Kp_nonneg x y)
    have : 0 ≤ (t * |u x| - |v y|) ^ 2 := sq_nonneg _
    rw [show t / 2 * u x ^ 2 + 1 / (2 * t) * v y ^ 2 =
      (t ^ 2 * |u x| ^ 2 + |v y| ^ 2) / (2 * t) by rw [sq_abs, sq_abs]; field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : ∑ x, ∑ y, Kp x y * (t / 2 * u x ^ 2 + 1 / (2 * t) * v y ^ 2) =
      t / 2 * ∑ x, u x ^ 2 * ∑ y, Kp x y + 1 / (2 * t) * ∑ y, v y ^ 2 * ∑ x, Kp x y := by
    simp only [mul_add, sum_add_distrib, mul_sum]
    congr 1
    · exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
    · rw [sum_comm]; exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => by ring
  have h4 : ∑ x, u x ^ 2 * ∑ y, Kp x y ≤ 18 * ((p : ℝ) - 2) * Nq u := by
    unfold Nq; rw [mul_sum]
    exact sum_le_sum fun x _ => by
      have := mul_le_mul_of_nonneg_left (row_pairs hp x) (sq_nonneg (u x))
      linarith
  have h5 : ∑ y, v y ^ 2 * ∑ x, Kp x y ≤ 18 * ((p : ℝ) - 2) * Nq v := by
    unfold Nq; rw [mul_sum]
    exact sum_le_sum fun y _ => by
      have := mul_le_mul_of_nonneg_left (col_pairs hp y) (sq_nonneg (v y))
      linarith
  calc |Ef u v| ≤ ∑ x, ∑ y, Kp x y * (|u x| * |v y|) := h1
    _ ≤ ∑ x, ∑ y, Kp x y * (t / 2 * u x ^ 2 + 1 / (2 * t) * v y ^ 2) :=
        sum_le_sum fun x _ => sum_le_sum fun y _ => h2 x y
    _ = _ := h3
    _ ≤ t / 2 * (18 * ((p : ℝ) - 2) * Nq u) + 1 / (2 * t) * (18 * ((p : ℝ) - 2) * Nq v) :=
        add_le_add (mul_le_mul_of_nonneg_left h4 (by positivity))
          (mul_le_mul_of_nonneg_left h5 (by positivity))
    _ = 18 * ((p : ℝ) - 2) / 2 * (t * Nq u + Nq v / t) := by field_simp

/-- **Both one-prime inputs hold** at every prime `p ≡ 3 (mod 4)`, `p ≥ 7`. -/
theorem ePrimeInputs (h3 : p % 4 = 3) (hp : 7 ≤ p) : EPrimeInputs p where
  eps := ePrime_eps (by omega)
  cd := fun c hc w => ePrime_cd h3 hp c hc w

/-- **`lem:record:e-orthogonal`(c) at one prime, proved**: `‖Sym(K₁ − K^E_0)‖ ≤ s^E_p` at every
prime `p ≡ 3 (mod 4)`, `p ≥ 10`, with NB3's transcription `sEpaper` of the paper's `s^E_p`. -/
theorem eorth_prime_paper (h3 : p % 4 = 3) (hp : 10 ≤ p) :
    EOrthPrime p (sEpaper (1 / (p : ℝ)) (1 / Real.sqrt p)) :=
  eorth_prime hp h3 (ePrimeInputs h3 (by omega))

/-- **NB3's `EOrthPaperInput` is proved.** -/
theorem eOrthPaperInput : EOrthPaperInput := fun p _ h3 hp =>
  eorth_prime_paper h3 (by omega)

end Sarkozy.NormBoundsPaper4
