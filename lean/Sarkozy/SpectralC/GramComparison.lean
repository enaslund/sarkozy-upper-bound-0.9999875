module

public import Sarkozy.SpectralC.MatrixNorms

@[expose] public section

/-!
# The Gram comparison (`lem:spec2:gram`)

`paper/sections/14_spectral.tex`, `lem:spec2:gram`. For labellings `x` and the allowed sets
`Φ_k(x)` (`allowedSet`), the model fields are `ψ_k(x, ·) = (p/|Φ_k(x)|) 𝟙_{Φ_k(x)} − 1`
(`psiM`), with `⟨ψ_k, ψ_l⟩ = p|Φ_k ∩ Φ_l|/(|Φ_k||Φ_l|) − 1` (`ip_psiM`). The star Gram model is
`𝐇_kl = ∏_{j ∈ N(k) ∩ N(l)} (1 + χ(ς_jk ς_jl)) − 1` (`modelH`, `eq:spec:H`); distinct `k, l`
are consistent if `χ(ς_jk ς_jl) ≠ −1` for all common neighbours `j` (`Consistent`).

* Inconsistent pairs have disjoint allowed sets (`allowedSet_disjoint`), and `𝐇_kl = −1`;
  consistent pairs have `𝐇_kl = 2^{|N(k) ∩ N(l)|} − 1`, and `𝐇_kk = 2^{r_k} − 1`.
* With the counts of `lem:extension`(coarse) as hypotheses
  (`|Φ_k(x)| ∈ p2^{-r_k}[1 − ê_k, 1 + ê_k]`, `|Φ_k(x) ∩ Φ_l(x)| ∈ p2^{-u_kl}[1 − e_u, 1 + e_u]`
  for consistent `k ≠ l`), `|⟨ψ_k, ψ_l⟩ − 𝐇_kl| ≤ β_kl` pointwise (`psiM_model_bound`, with
  `β` of `eq:spec:beta`, `betaG`), and the Schur test (Gershgorin) gives
  `‖𝐇⁰ − 𝐇‖ ≤ ε'_H` (`gram_model`), hence `𝐇⁰ ⪯ 𝐇 + ε'_H I`.

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The model field `ψ_k(x, a) = (p/|Φ_k(x)|) 𝟙_{Φ_k(x)}(a) − 1`. -/
noncomputable def psiM (N : U → Finset U) (ς : U → U → ZMod p) (x : U → ZMod p) (k : U)
    (a : ZMod p) : ℝ :=
  (p : ℝ) / (allowedSet N ς k x).card * (if a ∈ allowedSet N ς k x then 1 else 0) - 1

/-- `𝐇⁰_kl = E_ν⟨ψ_k, ψ_l⟩`. -/
noncomputable def gramH0 (ν : (U → ZMod p) → ℝ) (N : U → Finset U) (ς : U → U → ZMod p)
    (k l : U) : ℝ :=
  ∑ x, ν x * ((p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * psiM N ς x l a)

/-- The star Gram model `𝐇_kl = ∏_{j ∈ N(k) ∩ N(l)} (1 + χ(ς_jk ς_jl)) − 1` (`eq:spec:H`). -/
noncomputable def modelH (N : U → Finset U) (ς : U → U → ZMod p) (k l : U) : ℝ :=
  ∏ j ∈ N k ∩ N l, (1 + (quadraticChar (ZMod p) (ς j k * ς j l) : ℝ)) - 1

/-- Distinct `k, l` are consistent if `χ(ς_jk ς_jl) ≠ −1` for every `j ∈ N(k) ∩ N(l)`. -/
def Consistent (N : U → Finset U) (ς : U → U → ZMod p) (k l : U) : Prop :=
  ∀ j ∈ N k ∩ N l, quadraticChar (ZMod p) (ς j k * ς j l) ≠ -1

instance (N : U → Finset U) (ς : U → U → ZMod p) (k l : U) :
    Decidable (Consistent N ς k l) := by
  unfold Consistent; infer_instance

omit [Fintype U] in
lemma consistent_comm (N : U → Finset U) (ς : U → U → ZMod p) (k l : U) :
    Consistent N ς k l ↔ Consistent N ς l k := by
  unfold Consistent
  rw [inter_comm]
  simp only [mul_comm (ς _ k)]

/-- `β_kl` of `eq:spec:beta` (with `β_kk = 2^{r_k} ê_k/(1 − ê_k)` and `β_kl = 0` for
inconsistent `k ≠ l`); `e t = e_t(p, n)`. -/
noncomputable def betaG (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ) (k l : U) : ℝ :=
  if k = l then 2 ^ (N k).card * e (N k).card / (1 - e (N k).card)
  else if Consistent N ς k l then
    2 ^ (N k ∩ N l).card *
      max ((1 + e (N k ∪ N l).card) / ((1 - e (N k).card) * (1 - e (N l).card)) - 1)
        (1 - (1 - e (N k ∪ N l).card) / ((1 + e (N k).card) * (1 + e (N l).card)))
  else 0

omit [Fact p.Prime] in
lemma sum_ind (A : Finset (ZMod p)) [Fintype (ZMod p)] :
    ∑ a, (if a ∈ A then (1 : ℝ) else 0) = A.card := by
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one]

omit [Fact p.Prime] in
lemma sum_ind_mul_ind (A B : Finset (ZMod p)) [Fintype (ZMod p)] :
    ∑ a, (if a ∈ A then (1 : ℝ) else 0) * (if a ∈ B then 1 else 0) = (A ∩ B).card := by
  have h : ∀ a, (if a ∈ A then (1 : ℝ) else 0) * (if a ∈ B then 1 else 0) =
      if a ∈ A ∩ B then 1 else 0 := by
    intro a
    by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp [hA, hB]
  rw [sum_congr rfl fun a _ => h a, sum_ind]

/-- `⟨ψ_k, ψ_l⟩ = p|Φ_k ∩ Φ_l|/(|Φ_k||Φ_l|) − 1`. -/
lemma ip_psiM (N : U → Finset U) (ς : U → U → ZMod p) (x : U → ZMod p) (k l : U)
    (hk : (allowedSet N ς k x).card ≠ 0) (hl : (allowedSet N ς l x).card ≠ 0) :
    (p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * psiM N ς x l a =
      (p : ℝ) * (allowedSet N ς k x ∩ allowedSet N ς l x).card /
        ((allowedSet N ς k x).card * (allowedSet N ς l x).card) - 1 := by
  unfold psiM
  set A := allowedSet N ς k x
  set B := allowedSet N ς l x
  have hexp : ∀ a, ((p : ℝ) / A.card * (if a ∈ A then 1 else 0) - 1) *
      ((p : ℝ) / B.card * (if a ∈ B then 1 else 0) - 1) =
      (p : ℝ) / A.card * ((p : ℝ) / B.card) *
        ((if a ∈ A then 1 else 0) * (if a ∈ B then 1 else 0)) -
        (p : ℝ) / A.card * (if a ∈ A then 1 else 0) -
        (p : ℝ) / B.card * (if a ∈ B then 1 else 0) + 1 := by
    intro a; ring
  rw [sum_congr rfl fun a _ => hexp a, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum, sum_ind_mul_ind, sum_ind, sum_ind, sum_const, card_univ,
    ZMod.card, nsmul_eq_mul, mul_one]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hA : (A.card : ℝ) ≠ 0 := by exact_mod_cast hk
  have hB : (B.card : ℝ) ≠ 0 := by exact_mod_cast hl
  field_simp
  ring

/-- Inconsistent pairs have disjoint allowed sets. -/
lemma allowedSet_disjoint (N : U → Finset U) (ς : U → U → ZMod p) (x : U → ZMod p) (k l : U)
    (h : ¬ Consistent N ς k l) : allowedSet N ς k x ∩ allowedSet N ς l x = ∅ := by
  unfold Consistent at h
  push Not at h
  obtain ⟨j, hj, hχ⟩ := h
  rw [mem_inter] at hj
  apply eq_empty_of_forall_notMem
  intro a ha
  rw [mem_inter] at ha
  unfold allowedSet at ha
  rw [mem_filter, mem_filter] at ha
  obtain ⟨h1, h1'⟩ := ha.1.2.2 j hj.1
  obtain ⟨h2, h2'⟩ := ha.2.2.2 j hj.2
  have hd : a - x j ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h1; exact h1 rfl
  have hsq : IsSquare (ς j k * (a - x j) * (ς j l * (a - x j))) := h1'.mul h2'
  have hne : ς j k * (a - x j) * (ς j l * (a - x j)) ≠ 0 := mul_ne_zero h1 h2
  have h3 := (quadraticChar_one_iff_isSquare hne).mpr hsq
  have h4 : ς j k * (a - x j) * (ς j l * (a - x j)) = ς j k * ς j l * (a - x j) ^ 2 := by ring
  rw [h4, map_mul, quadraticChar_sq_one' hd, mul_one, hχ] at h3
  exact absurd h3 (by decide)

omit [Fintype U] in
lemma modelH_of_not_consistent (N : U → Finset U) (ς : U → U → ZMod p) (k l : U)
    (h : ¬ Consistent N ς k l) : modelH N ς k l = -1 := by
  unfold Consistent at h
  push Not at h
  obtain ⟨j, hj, hχ⟩ := h
  unfold modelH
  rw [prod_eq_zero hj (by rw [hχ]; push_cast; ring), zero_sub]

omit [Fintype U] in
lemma modelH_of_consistent (N : U → Finset U) (ς : U → U → ZMod p)
    (hςN : ∀ k, ∀ j ∈ N k, ς j k ≠ 0) (k l : U) (h : Consistent N ς k l) :
    modelH N ς k l = 2 ^ (N k ∩ N l).card - 1 := by
  unfold modelH
  congr 1
  rw [← prod_const]
  apply prod_congr rfl
  intro j hj
  have hj' := mem_inter.mp hj
  have hne : ς j k * ς j l ≠ 0 := mul_ne_zero (hςN k j hj'.1) (hςN l j hj'.2)
  rcases quadraticChar_dichotomy hne with h1 | h1
  · rw [h1]; push_cast; ring
  · exact absurd h1 (h j hj)

omit [Fintype U] in
lemma modelH_diag (N : U → Finset U) (ς : U → U → ZMod p)
    (hςN : ∀ k, ∀ j ∈ N k, ς j k ≠ 0) (k : U) : modelH N ς k k = 2 ^ (N k).card - 1 := by
  have h : Consistent N ς k k := by
    intro j hj
    rw [inter_self] at hj
    rw [← sq, quadraticChar_sq_one' (hςN k j hj)]
    decide
  rw [modelH_of_consistent N ς hςN k k h, inter_self]

/-! ## Real inequalities for the counts -/

lemma norm_bounds {P R a e : ℝ} (hP : 0 < P) (hR : 0 < R) (h1 : P / R * (1 - e) ≤ a)
    (h2 : a ≤ P / R * (1 + e)) : 1 - e ≤ a * R / P ∧ a * R / P ≤ 1 + e := by
  constructor
  · rw [le_div_iff₀ hP]
    have := mul_le_mul_of_nonneg_right h1 hR.le
    calc (1 - e) * P = P / R * (1 - e) * R := by field_simp
      _ ≤ a * R := this
  · rw [div_le_iff₀ hP]
    have := mul_le_mul_of_nonneg_right h2 hR.le
    calc a * R ≤ P / R * (1 + e) * R := this
      _ = (1 + e) * P := by field_simp

lemma ratio_bounds {α β γ ek el eu : ℝ} (hk1 : 0 < 1 - ek) (hl1 : 0 < 1 - el)
    (hα1 : 1 - ek ≤ α) (hα2 : α ≤ 1 + ek) (hβ1 : 1 - el ≤ β) (hβ2 : β ≤ 1 + el)
    (hγ0 : 0 ≤ γ) (hγ1 : 1 - eu ≤ γ) (hγ2 : γ ≤ 1 + eu) :
    γ / (α * β) ≤ (1 + eu) / ((1 - ek) * (1 - el)) ∧
      (1 - eu) / ((1 + ek) * (1 + el)) ≤ γ / (α * β) := by
  have hα : 0 < α := lt_of_lt_of_le hk1 hα1
  have hβ : 0 < β := lt_of_lt_of_le hl1 hβ1
  have hαβ : 0 < α * β := mul_pos hα hβ
  have hD1 : 0 < (1 - ek) * (1 - el) := mul_pos hk1 hl1
  have hD1le : (1 - ek) * (1 - el) ≤ α * β := mul_le_mul hα1 hβ1 hl1.le hα.le
  have hD2le : α * β ≤ (1 + ek) * (1 + el) := mul_le_mul hα2 hβ2 hβ.le (by linarith)
  constructor
  · calc γ / (α * β) ≤ (1 + eu) / (α * β) := div_le_div_of_nonneg_right hγ2 hαβ.le
      _ ≤ (1 + eu) / ((1 - ek) * (1 - el)) :=
          div_le_div_of_nonneg_left (by linarith) hD1 hD1le
  · by_cases hu : 1 - eu ≤ 0
    · exact (div_nonpos_of_nonpos_of_nonneg hu (by nlinarith)).trans (div_nonneg hγ0 hαβ.le)
    · push Not at hu
      calc (1 - eu) / ((1 + ek) * (1 + el)) ≤ (1 - eu) / (α * β) :=
            div_le_div_of_nonneg_left hu.le hαβ hD2le
        _ ≤ γ / (α * β) := div_le_div_of_nonneg_right hγ1 hαβ.le

lemma diag_ratio {α ek : ℝ} (hk0 : 0 ≤ ek) (hk1 : 0 < 1 - ek) (hα1 : 1 - ek ≤ α)
    (hα2 : α ≤ 1 + ek) : |1 / α - 1| ≤ ek / (1 - ek) := by
  have hα : 0 < α := lt_of_lt_of_le hk1 hα1
  rw [abs_le]
  constructor
  · have h1 : 1 / (1 + ek) ≤ 1 / α := one_div_le_one_div_of_le hα hα2
    have h2 : 1 / (1 + ek) - 1 = -(ek / (1 + ek)) := by field_simp; ring
    have h3 : ek / (1 + ek) ≤ ek / (1 - ek) := div_le_div_of_nonneg_left hk0 hk1 (by linarith)
    linarith
  · have h1 : 1 / α ≤ 1 / (1 - ek) := one_div_le_one_div_of_le hk1 hα1
    have h2 : 1 / (1 - ek) - 1 = ek / (1 - ek) := by field_simp; ring
    linarith

/-- The off-diagonal count bound: `|pm/(ab) − c| ≤ c · max(…)` when `R_k R_l = R_u c`. -/
lemma offdiag_count_bound {P a b m Rk Rl Ru c ek el eu : ℝ} (hP : 0 < P) (hRk : 0 < Rk)
    (hRl : 0 < Rl) (hRu : 0 < Ru) (hc : 0 < c) (hRR : Rk * Rl = Ru * c)
    (hk1 : 0 < 1 - ek) (hl1 : 0 < 1 - el) (hm0 : 0 ≤ m)
    (ha1 : P / Rk * (1 - ek) ≤ a) (ha2 : a ≤ P / Rk * (1 + ek))
    (hb1 : P / Rl * (1 - el) ≤ b) (hb2 : b ≤ P / Rl * (1 + el))
    (hm1 : P / Ru * (1 - eu) ≤ m) (hm2 : m ≤ P / Ru * (1 + eu)) :
    |P * m / (a * b) - c| ≤
      c * max ((1 + eu) / ((1 - ek) * (1 - el)) - 1) (1 - (1 - eu) / ((1 + ek) * (1 + el))) := by
  obtain ⟨hα1, hα2⟩ := norm_bounds hP hRk ha1 ha2
  obtain ⟨hβ1, hβ2⟩ := norm_bounds hP hRl hb1 hb2
  obtain ⟨hγ1, hγ2⟩ := norm_bounds hP hRu hm1 hm2
  have hγ0 : 0 ≤ m * Ru / P := by positivity
  obtain ⟨hup, hlo⟩ := ratio_bounds hk1 hl1 hα1 hα2 hβ1 hβ2 hγ0 hγ1 hγ2
  have ha : 0 < a := lt_of_lt_of_le (by positivity) ha1
  have hb : 0 < b := lt_of_lt_of_le (by positivity) hb1
  have hX : P * m / (a * b) = c * ((m * Ru / P) / ((a * Rk / P) * (b * Rl / P))) := by
    have e1 : (m * Ru / P) / ((a * Rk / P) * (b * Rl / P)) = m * Ru * P / (a * b * (Rk * Rl)) := by
      field_simp
    rw [e1, hRR]
    field_simp
  rw [hX, abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left hlo hc.le
    have hmax := le_max_right ((1 + eu) / ((1 - ek) * (1 - el)) - 1)
      (1 - (1 - eu) / ((1 + ek) * (1 + el)))
    nlinarith
  · have := mul_le_mul_of_nonneg_left hup hc.le
    have hmax := le_max_left ((1 + eu) / ((1 - ek) * (1 - el)) - 1)
      (1 - (1 - eu) / ((1 + ek) * (1 + el)))
    nlinarith

/-! ## The model bound -/

/-- The counts of `lem:extension`(coarse) at `x`: `|Φ_k(x)| ∈ p2^{-r_k}[1 − ê_k, 1 + ê_k]`. -/
def CountsOK (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ) (x : U → ZMod p) : Prop :=
  (∀ k, (p : ℝ) / 2 ^ (N k).card * (1 - e (N k).card) ≤ (allowedSet N ς k x).card ∧
      ((allowedSet N ς k x).card : ℝ) ≤ (p : ℝ) / 2 ^ (N k).card * (1 + e (N k).card)) ∧
  (∀ k l, k ≠ l → Consistent N ς k l →
      (p : ℝ) / 2 ^ (N k ∪ N l).card * (1 - e (N k ∪ N l).card) ≤
        (allowedSet N ς k x ∩ allowedSet N ς l x).card ∧
      ((allowedSet N ς k x ∩ allowedSet N ς l x).card : ℝ) ≤
        (p : ℝ) / 2 ^ (N k ∪ N l).card * (1 + e (N k ∪ N l).card))

lemma card_allowedSet_pos (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (he1 : ∀ k, e (N k).card < 1) (x : U → ZMod p) (hx : CountsOK N ς e x) (k : U) :
    (allowedSet N ς k x).card ≠ 0 := by
  have hP : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : (0 : ℝ) < (p : ℝ) / 2 ^ (N k).card * (1 - e (N k).card) := by
    have := he1 k
    have : (0 : ℝ) < 1 - e (N k).card := by linarith
    positivity
  have h2 := lt_of_lt_of_le h1 (hx.1 k).1
  exact_mod_cast h2.ne'

/-- **The model, pointwise**: `|⟨ψ_k, ψ_l⟩ − 𝐇_kl| ≤ β_kl` at every `x` with the counts of
`lem:extension`(coarse). -/
lemma psiM_model_bound (N : U → Finset U) (ς : U → U → ZMod p)
    (hςN : ∀ k, ∀ j ∈ N k, ς j k ≠ 0) (e : ℕ → ℝ) (he0 : ∀ t, 0 ≤ e t)
    (he1 : ∀ k, e (N k).card < 1) (x : U → ZMod p) (hx : CountsOK N ς e x) (k l : U) :
    |(p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * psiM N ς x l a - modelH N ς k l| ≤ betaG N ς e k l := by
  have hP : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hk0 := card_allowedSet_pos N ς e he1 x hx k
  have hl0 := card_allowedSet_pos N ς e he1 x hx l
  rw [ip_psiM N ς x k l hk0 hl0]
  unfold betaG
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl, modelH_diag N ς hςN k, inter_self]
    have ha0 : ((allowedSet N ς k x).card : ℝ) ≠ 0 := by exact_mod_cast hk0
    have hR : (0 : ℝ) < 2 ^ (N k).card := by positivity
    obtain ⟨hα1, hα2⟩ := norm_bounds hP hR (hx.1 k).1 (hx.1 k).2
    have hk1 : 0 < 1 - e (N k).card := by linarith [he1 k]
    have hd := diag_ratio (he0 _) hk1 hα1 hα2
    have hid : (p : ℝ) * ((allowedSet N ς k x).card : ℝ) /
        (((allowedSet N ς k x).card : ℝ) * ((allowedSet N ς k x).card : ℝ)) - 1 -
          (2 ^ (N k).card - 1) =
        2 ^ (N k).card * (1 / (((allowedSet N ς k x).card : ℝ) * 2 ^ (N k).card / p) - 1) := by
      field_simp
      ring
    rw [hid, abs_mul, abs_of_pos hR]
    exact (mul_le_mul_of_nonneg_left hd hR.le).trans_eq (mul_div_assoc _ _ _).symm
  · rw [ite_eq_right hkl]
    by_cases hc : Consistent N ς k l
    · rw [ite_eq_left hc, modelH_of_consistent N ς hςN k l hc]
      have hRR : (2 : ℝ) ^ (N k).card * 2 ^ (N l).card =
          2 ^ (N k ∪ N l).card * 2 ^ (N k ∩ N l).card := by
        rw [← pow_add, ← pow_add, card_union_add_card_inter]
      have hk1 : 0 < 1 - e (N k).card := by linarith [he1 k]
      have hl1 : 0 < 1 - e (N l).card := by linarith [he1 l]
      have hb := offdiag_count_bound hP (by positivity) (by positivity) (by positivity)
        (by positivity) hRR hk1 hl1 (Nat.cast_nonneg _) (hx.1 k).1 (hx.1 k).2 (hx.1 l).1
        (hx.1 l).2 (hx.2 k l hkl hc).1 (hx.2 k l hkl hc).2
      have hid : (p : ℝ) * ((allowedSet N ς k x ∩ allowedSet N ς l x).card : ℝ) /
          (((allowedSet N ς k x).card : ℝ) * (allowedSet N ς l x).card) - 1 -
          (2 ^ (N k ∩ N l).card - 1) =
          (p : ℝ) * ((allowedSet N ς k x ∩ allowedSet N ς l x).card : ℝ) /
          (((allowedSet N ς k x).card : ℝ) * (allowedSet N ς l x).card) -
            2 ^ (N k ∩ N l).card := by ring
      rw [hid]
      exact hb
    · rw [ite_eq_right hc, modelH_of_not_consistent N ς k l hc,
        allowedSet_disjoint N ς x k l hc]
      simp

lemma betaG_nonneg (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ) (he0 : ∀ t, 0 ≤ e t)
    (he1 : ∀ k, e (N k).card < 1) (k l : U) : 0 ≤ betaG N ς e k l := by
  unfold betaG
  have hk1 : 0 < 1 - e (N k).card := by linarith [he1 k]
  have hl1 : 0 < 1 - e (N l).card := by linarith [he1 l]
  split_ifs with h1 h2
  · have := he0 (N k).card
    positivity
  · apply mul_nonneg (by positivity)
    apply le_max_of_le_left
    have hD : 0 < (1 - e (N k).card) * (1 - e (N l).card) := mul_pos hk1 hl1
    have hD1 : (1 - e (N k).card) * (1 - e (N l).card) ≤ 1 := by
      have := he0 (N k).card
      have := he0 (N l).card
      nlinarith
    rw [sub_nonneg, le_div_iff₀ hD]
    linarith [he0 (N k ∪ N l).card]
  · exact le_refl 0

lemma betaG_symm (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ) (k l : U) :
    betaG N ς e k l = betaG N ς e l k := by
  unfold betaG
  by_cases h : k = l
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    by_cases hc : Consistent N ς k l
    · rw [ite_eq_left hc, ite_eq_left ((consistent_comm N ς k l).mp hc), inter_comm, union_comm,
        mul_comm (1 - e (N k).card), mul_comm (1 + e (N k).card)]
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((consistent_comm N ς k l).mpr h'))]

/-- **`lem:spec2:gram`, the model**: `‖𝐇⁰ − 𝐇‖ ≤ ε'_H` (`ρ` bounds the row sums of `β`), given
the counts of `lem:extension`(coarse) on the support of `ν`. In particular `𝐇⁰ ⪯ 𝐇 + ε'_H I`
(`re_qform_le_of_normLe`). -/
theorem gram_model (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (N : U → Finset U) (ς : U → U → ZMod p) (hςN : ∀ k, ∀ j ∈ N k, ς j k ≠ 0)
    (e : ℕ → ℝ) (he0 : ∀ t, 0 ≤ e t) (he1 : ∀ k, e (N k).card < 1)
    (hcount : ∀ x, ν x ≠ 0 → CountsOK N ς e x) {ρ : ℝ}
    (hrow : ∀ k, ∑ l, betaG N ς e k l ≤ ρ) :
    NormLe (fun k l => ((gramH0 ν N ς k l - modelH N ς k l : ℝ) : ℂ)) ρ := by
  apply normLe_schur _ (betaG N ς e) (betaG_nonneg N ς e he0 he1) (betaG_symm N ς e) _ hrow
  intro k l
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hsplit : gramH0 ν N ς k l - modelH N ς k l =
      ∑ x, ν x * ((p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * psiM N ς x l a - modelH N ς k l) := by
    unfold gramH0
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hν1, one_mul]
  rw [hsplit]
  calc |∑ x, ν x * ((p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * psiM N ς x l a - modelH N ς k l)|
      ≤ ∑ x, ν x * betaG N ς e k l := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (hν0 x)]
        by_cases hx : ν x = 0
        · rw [hx, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (psiM_model_bound N ς hςN e he0 he1 x (hcount x hx) k l)
            (hν0 x)
    _ = betaG N ς e k l := by rw [← sum_mul, hν1, one_mul]

omit [DecidableEq U] in
/-- A two-sided norm bound gives the order relation: `A ⪯ B + ρI` when `‖A − B‖ ≤ ρ`. -/
theorem re_qform_le_of_normLe {A B : U → U → ℂ} {ρ : ℝ}
    (h : NormLe (fun k l => A k l - B k l) ρ) (w : U → ℂ) :
    (qform A w).re ≤ (qform B w).re + ρ * ∑ k, ‖w k‖ ^ 2 := by
  have h1 : qform A w = qform B w + bform (fun k l => A k l - B k l) w w := by
    unfold qform bform
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun l _ => by ring
  have h2 := h w w
  rw [mul_assoc, show vnorm w * vnorm w = ∑ k, ‖w k‖ ^ 2 from
    Real.mul_self_sqrt (sum_nonneg fun _ _ => sq_nonneg _)] at h2
  rw [h1, Complex.add_re]
  have h3 := Complex.re_le_norm (bform (fun k l => A k l - B k l) w w)
  linarith

/-! ## The deviations -/

/-- `D_k(x, a) = pP_k(a | x) − (p/|Φ_k(x)|) 𝟙_{Φ_k(x)}(a)`, so that `Ψ_k = ψ_k + D_k`
(`D_k = (1 + ψ_k)δ_k` in the paper). -/
noncomputable def devD (N : U → Finset U) (ς : U → U → ZMod p)
    (P : U → (U → ZMod p) → ZMod p → ℝ) (x : U → ZMod p) (k : U) (a : ZMod p) : ℝ :=
  (p : ℝ) * P k x a -
    (p : ℝ) / (allowedSet N ς k x).card * (if a ∈ allowedSet N ς k x then 1 else 0)

/-- `H̃_kl = E_ν⟨Ψ_k, Ψ_l⟩`, `Ψ_k = pP_k − 1` (real form of `gramΓ ν (psiField P)`). -/
noncomputable def gramT (ν : (U → ZMod p) → ℝ) (P : U → (U → ZMod p) → ZMod p → ℝ)
    (k l : U) : ℝ :=
  ∑ x, ν x * ((p : ℝ)⁻¹ * ∑ a, ((p : ℝ) * P k x a - 1) * ((p : ℝ) * P l x a - 1))

/-- The matrix bounding `|X_kl| + |X_lk| + |Y_kl|`: `2^{r_k}δ'^2_k/(1 − ê_k)` on the diagonal,
`Υ_kl(δ'_k + δ'_l + δ'_kδ'_l)` for consistent `k ≠ l`, `0` otherwise; its maximal row sum is
`ε_X`. -/
noncomputable def bX (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ) (Rp : U → ℝ)
    (k l : U) : ℝ :=
  if k = l then 2 ^ (N k).card * (Rp k - 1) ^ 2 / (1 - e (N k).card)
  else if Consistent N ς k l then
    2 ^ (N k ∩ N l).card * (1 + e (N k ∪ N l).card) /
        ((1 - e (N k).card) * (1 - e (N l).card)) *
      ((Rp k - 1) + (Rp l - 1) + (Rp k - 1) * (Rp l - 1))
  else 0

lemma gramΓ_psiField_eq (ν : (U → ZMod p) → ℝ) (P : U → (U → ZMod p) → ZMod p → ℝ)
    (k l : U) : gramΓ ν (psiField P) k l = ((gramT ν P k l : ℝ) : ℂ) := by
  unfold gramΓ psiField gramT
  push_cast
  refine sum_congr rfl fun x _ => ?_
  congr 2
  refine sum_congr rfl fun a _ => ?_
  simp [map_sub, Complex.conj_ofReal]

/-- The matrix entries `X = p|Φ_k ∩ Φ_l|/(|Φ_k||Φ_l|)`. -/
noncomputable def ovl (N : U → Finset U) (ς : U → U → ZMod p) (x : U → ZMod p) (k l : U) : ℝ :=
  (p : ℝ) * (allowedSet N ς k x ∩ allowedSet N ς l x).card /
    (((allowedSet N ς k x).card : ℝ) * (allowedSet N ς l x).card)

lemma ovl_nonneg (N : U → Finset U) (ς : U → U → ZMod p) (x : U → ZMod p) (k l : U) :
    0 ≤ ovl N ς x k l := by
  unfold ovl; positivity

lemma ovl_comm (N : U → Finset U) (ς : U → U → ZMod p) (x : U → ZMod p) (k l : U) :
    ovl N ς x k l = ovl N ς x l k := by
  unfold ovl; rw [inter_comm, mul_comm (((allowedSet N ς k x).card : ℝ))]

section Deviations

variable (N : U → Finset U) (ς : U → U → ZMod p) (P : U → (U → ZMod p) → ZMod p → ℝ)
  (Rp : U → ℝ) (x : U → ZMod p)

lemma devD_off (hPsupp : ∀ k a, a ∉ allowedSet N ς k x → P k x a = 0) (k : U) (a : ZMod p)
    (ha : a ∉ allowedSet N ς k x) : devD N ς P x k a = 0 := by
  unfold devD; rw [hPsupp k a ha, ite_eq_right ha]; ring

lemma sum_devD (hP1 : ∀ k, ∑ a, P k x a = 1) (k : U) (hk : (allowedSet N ς k x).card ≠ 0) :
    ∑ a, devD N ς P x k a = 0 := by
  unfold devD
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hP1 k, sum_ind]
  have : ((allowedSet N ς k x).card : ℝ) ≠ 0 := by exact_mod_cast hk
  field_simp
  ring

lemma abs_devD_le (hRp : ∀ k, 1 ≤ Rp k) (hPsupp : ∀ k a, a ∉ allowedSet N ς k x → P k x a = 0)
    (hPdens : ∀ k, ∀ a ∈ allowedSet N ς k x,
      (Rp k)⁻¹ ≤ P k x a * (allowedSet N ς k x).card ∧ P k x a * (allowedSet N ς k x).card ≤ Rp k)
    (k : U) (hk : (allowedSet N ς k x).card ≠ 0) (a : ZMod p) :
    |devD N ς P x k a| ≤
      (p : ℝ) / (allowedSet N ς k x).card * (Rp k - 1) * (if a ∈ allowedSet N ς k x then 1 else 0) := by
  by_cases ha : a ∈ allowedSet N ς k x
  · rw [ite_eq_left ha, mul_one]
    have hc : ((allowedSet N ς k x).card : ℝ) ≠ 0 := by exact_mod_cast hk
    have hc0 : (0 : ℝ) < (allowedSet N ς k x).card := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hid : devD N ς P x k a = (p : ℝ) / (allowedSet N ς k x).card *
        (P k x a * (allowedSet N ς k x).card - 1) := by
      unfold devD; rw [ite_eq_left ha]; field_simp
    have hR := hRp k
    obtain ⟨h1, h2⟩ := hPdens k a ha
    have h3 : 1 - Rp k ≤ (Rp k)⁻¹ - 1 := by
      have hRpos : 0 < Rp k := by linarith
      have : (Rp k - 1) * (1 - (Rp k)⁻¹) = Rp k + (Rp k)⁻¹ - 2 := by field_simp; ring
      have h4 : (Rp k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr h4)]
    have hP : (0 : ℝ) ≤ (p : ℝ) / (allowedSet N ς k x).card := by positivity
    rw [hid, abs_mul, abs_of_nonneg hP]
    apply mul_le_mul_of_nonneg_left _ hP
    rw [abs_le]; constructor <;> linarith
  · rw [devD_off N ς P x hPsupp k a ha, ite_eq_right ha, abs_zero, mul_zero]

lemma ip_psiM_devD (hP1 : ∀ k, ∑ a, P k x a = 1) (k l : U)
    (hk : (allowedSet N ς k x).card ≠ 0) (hl : (allowedSet N ς l x).card ≠ 0) :
    (p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * devD N ς P x l a =
      ((allowedSet N ς k x).card : ℝ)⁻¹ * ∑ a ∈ allowedSet N ς k x, devD N ς P x l a := by
  unfold psiM
  have h1 : ∀ a, ((p : ℝ) / (allowedSet N ς k x).card * (if a ∈ allowedSet N ς k x then 1 else 0)
      - 1) * devD N ς P x l a = (p : ℝ) / (allowedSet N ς k x).card *
        (if a ∈ allowedSet N ς k x then devD N ς P x l a else 0) - devD N ς P x l a := by
    intro a; split_ifs <;> ring
  rw [sum_congr rfl fun a _ => h1 a, sum_sub_distrib, ← mul_sum, sum_devD N ς P x hP1 l hl,
    sub_zero, sum_ite_mem, univ_inter]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

lemma abs_ip_psiM_devD (hRp : ∀ k, 1 ≤ Rp k) (hP1 : ∀ k, ∑ a, P k x a = 1)
    (hPsupp : ∀ k a, a ∉ allowedSet N ς k x → P k x a = 0)
    (hPdens : ∀ k, ∀ a ∈ allowedSet N ς k x,
      (Rp k)⁻¹ ≤ P k x a * (allowedSet N ς k x).card ∧ P k x a * (allowedSet N ς k x).card ≤ Rp k)
    (k l : U) (hk : (allowedSet N ς k x).card ≠ 0) (hl : (allowedSet N ς l x).card ≠ 0) :
    |(p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * devD N ς P x l a| ≤ ovl N ς x k l * (Rp l - 1) := by
  rw [ip_psiM_devD N ς P x hP1 k l hk hl]
  have hc0 : (0 : ℝ) < (allowedSet N ς k x).card := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [abs_mul, abs_of_pos (inv_pos.mpr hc0)]
  calc ((allowedSet N ς k x).card : ℝ)⁻¹ * |∑ a ∈ allowedSet N ς k x, devD N ς P x l a|
      ≤ ((allowedSet N ς k x).card : ℝ)⁻¹ * ∑ a ∈ allowedSet N ς k x,
          (p : ℝ) / (allowedSet N ς l x).card * (Rp l - 1) *
            (if a ∈ allowedSet N ς l x then 1 else 0) := by
        apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hc0).le
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ =>
          abs_devD_le N ς P Rp x hRp hPsupp hPdens l hl a)
    _ = ovl N ς x k l * (Rp l - 1) := by
        rw [← mul_sum, sum_ite_mem, sum_const, nsmul_eq_mul, mul_one]
        unfold ovl
        have hl' : ((allowedSet N ς l x).card : ℝ) ≠ 0 := by exact_mod_cast hl
        field_simp

lemma ip_psiM_devD_self (hP1 : ∀ k, ∑ a, P k x a = 1)
    (hPsupp : ∀ k a, a ∉ allowedSet N ς k x → P k x a = 0) (k : U)
    (hk : (allowedSet N ς k x).card ≠ 0) :
    (p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * devD N ς P x k a = 0 := by
  rw [ip_psiM_devD N ς P x hP1 k k hk hk]
  have : ∑ a ∈ allowedSet N ς k x, devD N ς P x k a = ∑ a, devD N ς P x k a :=
    sum_subset (subset_univ _) fun a _ ha => devD_off N ς P x hPsupp k a ha
  rw [this, sum_devD N ς P x hP1 k hk, mul_zero]

lemma abs_ip_devD_devD (hRp : ∀ k, 1 ≤ Rp k)
    (hPsupp : ∀ k a, a ∉ allowedSet N ς k x → P k x a = 0)
    (hPdens : ∀ k, ∀ a ∈ allowedSet N ς k x,
      (Rp k)⁻¹ ≤ P k x a * (allowedSet N ς k x).card ∧ P k x a * (allowedSet N ς k x).card ≤ Rp k)
    (k l : U) (hk : (allowedSet N ς k x).card ≠ 0) (hl : (allowedSet N ς l x).card ≠ 0) :
    |(p : ℝ)⁻¹ * ∑ a, devD N ς P x k a * devD N ς P x l a| ≤
      ovl N ς x k l * ((Rp k - 1) * (Rp l - 1)) := by
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  rw [abs_mul, abs_of_pos hp0]
  have hRk := hRp k
  have hRl := hRp l
  calc (p : ℝ)⁻¹ * |∑ a, devD N ς P x k a * devD N ς P x l a|
      ≤ (p : ℝ)⁻¹ * ∑ a, ((p : ℝ) / (allowedSet N ς k x).card * (Rp k - 1) *
          (if a ∈ allowedSet N ς k x then 1 else 0)) *
          ((p : ℝ) / (allowedSet N ς l x).card * (Rp l - 1) *
          (if a ∈ allowedSet N ς l x then 1 else 0)) := by
        apply mul_le_mul_of_nonneg_left _ hp0.le
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (abs_devD_le N ς P Rp x hRp hPsupp hPdens k hk a)
          (abs_devD_le N ς P Rp x hRp hPsupp hPdens l hl a) (abs_nonneg _)
          (by have : (0 : ℝ) ≤ Rp k - 1 := by linarith
              split_ifs <;> positivity)
    _ = ovl N ς x k l * ((Rp k - 1) * (Rp l - 1)) := by
        have h1 : ∀ a, ((p : ℝ) / (allowedSet N ς k x).card * (Rp k - 1) *
            (if a ∈ allowedSet N ς k x then 1 else 0)) *
            ((p : ℝ) / (allowedSet N ς l x).card * (Rp l - 1) *
            (if a ∈ allowedSet N ς l x then 1 else 0)) =
            (p : ℝ) / (allowedSet N ς k x).card * (Rp k - 1) *
              ((p : ℝ) / (allowedSet N ς l x).card * (Rp l - 1)) *
              ((if a ∈ allowedSet N ς k x then 1 else 0) *
                (if a ∈ allowedSet N ς l x then 1 else 0)) := by intro a; ring
        rw [sum_congr rfl fun a _ => h1 a, ← mul_sum, sum_ind_mul_ind]
        unfold ovl
        have hk' : ((allowedSet N ς k x).card : ℝ) ≠ 0 := by exact_mod_cast hk
        have hl' : ((allowedSet N ς l x).card : ℝ) ≠ 0 := by exact_mod_cast hl
        have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
        field_simp

end Deviations

/-! ## Bounds for the overlaps `X = p|Φ_k ∩ Φ_l|/(|Φ_k||Φ_l|)` -/

lemma ovl_diag_le (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (he1 : ∀ k, e (N k).card < 1) (x : U → ZMod p) (hx : CountsOK N ς e x) (k : U) :
    ovl N ς x k k ≤ 2 ^ (N k).card / (1 - e (N k).card) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hk0 := card_allowedSet_pos N ς e he1 x hx k
  have hc0 : (0 : ℝ) < (allowedSet N ς k x).card := by exact_mod_cast Nat.pos_of_ne_zero hk0
  have hR : (0 : ℝ) < 2 ^ (N k).card := by positivity
  have hk1 : 0 < 1 - e (N k).card := by linarith [he1 k]
  obtain ⟨hα1, _⟩ := norm_bounds hP hR (hx.1 k).1 (hx.1 k).2
  unfold ovl
  rw [inter_self, div_le_div_iff₀ (mul_pos hc0 hc0) hk1]
  rw [le_div_iff₀ hP] at hα1
  nlinarith

lemma ovl_consistent_le (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (he1 : ∀ k, e (N k).card < 1) (x : U → ZMod p) (hx : CountsOK N ς e x) (k l : U)
    (hkl : k ≠ l) (hc : Consistent N ς k l) :
    ovl N ς x k l ≤ 2 ^ (N k ∩ N l).card * (1 + e (N k ∪ N l).card) /
      ((1 - e (N k).card) * (1 - e (N l).card)) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hRk : (0 : ℝ) < 2 ^ (N k).card := by positivity
  have hRl : (0 : ℝ) < 2 ^ (N l).card := by positivity
  have hRu : (0 : ℝ) < 2 ^ (N k ∪ N l).card := by positivity
  have hcc : (0 : ℝ) < 2 ^ (N k ∩ N l).card := by positivity
  have hRR : (2 : ℝ) ^ (N k).card * 2 ^ (N l).card =
      2 ^ (N k ∪ N l).card * 2 ^ (N k ∩ N l).card := by
    rw [← pow_add, ← pow_add, card_union_add_card_inter]
  have hk1 : 0 < 1 - e (N k).card := by linarith [he1 k]
  have hl1 : 0 < 1 - e (N l).card := by linarith [he1 l]
  obtain ⟨hα1, hα2⟩ := norm_bounds hP hRk (hx.1 k).1 (hx.1 k).2
  obtain ⟨hβ1, hβ2⟩ := norm_bounds hP hRl (hx.1 l).1 (hx.1 l).2
  obtain ⟨hγ1, hγ2⟩ := norm_bounds hP hRu (hx.2 k l hkl hc).1 (hx.2 k l hkl hc).2
  have hγ0 : 0 ≤ ((allowedSet N ς k x ∩ allowedSet N ς l x).card : ℝ) *
      2 ^ (N k ∪ N l).card / p := by positivity
  obtain ⟨hup, _⟩ := ratio_bounds hk1 hl1 hα1 hα2 hβ1 hβ2 hγ0 hγ1 hγ2
  have ha : (0 : ℝ) < (allowedSet N ς k x).card :=
    lt_of_lt_of_le (by have := hk1; positivity) (hx.1 k).1
  have hb : (0 : ℝ) < (allowedSet N ς l x).card :=
    lt_of_lt_of_le (by have := hl1; positivity) (hx.1 l).1
  have hX : ovl N ς x k l = 2 ^ (N k ∩ N l).card *
      ((((allowedSet N ς k x ∩ allowedSet N ς l x).card : ℝ) * 2 ^ (N k ∪ N l).card / p) /
        ((((allowedSet N ς k x).card : ℝ) * 2 ^ (N k).card / p) *
          (((allowedSet N ς l x).card : ℝ) * 2 ^ (N l).card / p))) := by
    unfold ovl
    have e1 : (((allowedSet N ς k x ∩ allowedSet N ς l x).card : ℝ) * 2 ^ (N k ∪ N l).card / p) /
        ((((allowedSet N ς k x).card : ℝ) * 2 ^ (N k).card / p) *
          (((allowedSet N ς l x).card : ℝ) * 2 ^ (N l).card / p)) =
        ((allowedSet N ς k x ∩ allowedSet N ς l x).card : ℝ) * 2 ^ (N k ∪ N l).card * p /
          (((allowedSet N ς k x).card : ℝ) * (allowedSet N ς l x).card *
            (2 ^ (N k).card * 2 ^ (N l).card)) := by
      field_simp
    rw [e1, hRR]
    field_simp
  rw [hX]
  exact (mul_le_mul_of_nonneg_left hup hcc.le).trans_eq (mul_div_assoc _ _ _).symm

lemma ovl_of_not_consistent (N : U → Finset U) (ς : U → U → ZMod p) (x : U → ZMod p) (k l : U)
    (hc : ¬ Consistent N ς k l) : ovl N ς x k l = 0 := by
  unfold ovl; rw [allowedSet_disjoint N ς x k l hc]; simp

/-- **The deviations, pointwise**: `|⟨Ψ_k, Ψ_l⟩ − ⟨ψ_k, ψ_l⟩| ≤ bX_kl` at every `x` with the
counts of `lem:extension`(coarse) and the conditions of `def:coupling-data` on `P(· | x)`. -/
lemma deviation_bound (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ)
    (he1 : ∀ k, e (N k).card < 1) (P : U → (U → ZMod p) → ZMod p → ℝ)
    (Rp : U → ℝ) (hRp : ∀ k, 1 ≤ Rp k) (x : U → ZMod p) (hx : CountsOK N ς e x)
    (hP1 : ∀ k, ∑ a, P k x a = 1) (hPsupp : ∀ k a, a ∉ allowedSet N ς k x → P k x a = 0)
    (hPdens : ∀ k, ∀ a ∈ allowedSet N ς k x,
      (Rp k)⁻¹ ≤ P k x a * (allowedSet N ς k x).card ∧ P k x a * (allowedSet N ς k x).card ≤ Rp k)
    (k l : U) :
    |(p : ℝ)⁻¹ * ∑ a, ((p : ℝ) * P k x a - 1) * ((p : ℝ) * P l x a - 1) -
      (p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * psiM N ς x l a| ≤ bX N ς e Rp k l := by
  have hk0 := card_allowedSet_pos N ς e he1 x hx k
  have hl0 := card_allowedSet_pos N ς e he1 x hx l
  have hsplit : (p : ℝ)⁻¹ * ∑ a, ((p : ℝ) * P k x a - 1) * ((p : ℝ) * P l x a - 1) -
      (p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * psiM N ς x l a =
      (p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * devD N ς P x l a +
      (p : ℝ)⁻¹ * ∑ a, psiM N ς x l a * devD N ς P x k a +
      (p : ℝ)⁻¹ * ∑ a, devD N ς P x k a * devD N ς P x l a := by
    rw [← mul_sub, ← mul_add, ← mul_add, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    unfold psiM devD
    ring
  rw [hsplit]
  have hRk := hRp k
  have hRl := hRp l
  have h1 := abs_ip_psiM_devD N ς P Rp x hRp hP1 hPsupp hPdens k l hk0 hl0
  have h2 := abs_ip_psiM_devD N ς P Rp x hRp hP1 hPsupp hPdens l k hl0 hk0
  have h3 := abs_ip_devD_devD N ς P Rp x hRp hPsupp hPdens k l hk0 hl0
  rw [ovl_comm N ς x l k] at h2
  have htri := abs_add_three ((p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * devD N ς P x l a)
    ((p : ℝ)⁻¹ * ∑ a, psiM N ς x l a * devD N ς P x k a)
    ((p : ℝ)⁻¹ * ∑ a, devD N ς P x k a * devD N ς P x l a)
  unfold bX
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl, ip_psiM_devD_self N ς P x hP1 hPsupp k hk0, zero_add, zero_add]
    have hd := ovl_diag_le N ς e he1 x hx k
    have hk1 : 0 < 1 - e (N k).card := by linarith [he1 k]
    calc |(p : ℝ)⁻¹ * ∑ a, devD N ς P x k a * devD N ς P x k a|
        ≤ ovl N ς x k k * ((Rp k - 1) * (Rp k - 1)) := h3
      _ ≤ 2 ^ (N k).card / (1 - e (N k).card) * ((Rp k - 1) * (Rp k - 1)) :=
          mul_le_mul_of_nonneg_right hd (mul_self_nonneg _)
      _ = 2 ^ (N k).card * (Rp k - 1) ^ 2 / (1 - e (N k).card) := by ring
  · rw [ite_eq_right hkl]
    by_cases hc : Consistent N ς k l
    · rw [ite_eq_left hc]
      have hu := ovl_consistent_le N ς e he1 x hx k l hkl hc
      have hS : 0 ≤ (Rp k - 1) + (Rp l - 1) + (Rp k - 1) * (Rp l - 1) := by
        have : 0 ≤ (Rp k - 1) * (Rp l - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      calc _ ≤ _ := htri
        _ ≤ ovl N ς x k l * (Rp l - 1) + ovl N ς x k l * (Rp k - 1) +
            ovl N ς x k l * ((Rp k - 1) * (Rp l - 1)) := add_le_add (add_le_add h1 h2) h3
        _ = ovl N ς x k l * ((Rp k - 1) + (Rp l - 1) + (Rp k - 1) * (Rp l - 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hu hS
    · rw [ite_eq_right hc]
      rw [ovl_of_not_consistent N ς x k l hc] at h1 h2 h3
      simp only [zero_mul] at h1 h2 h3
      linarith [htri]

lemma bX_nonneg (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ) (he0 : ∀ t, 0 ≤ e t)
    (he1 : ∀ k, e (N k).card < 1) (Rp : U → ℝ) (hRp : ∀ k, 1 ≤ Rp k) (k l : U) :
    0 ≤ bX N ς e Rp k l := by
  unfold bX
  have hk1 : 0 < 1 - e (N k).card := by linarith [he1 k]
  have hl1 : 0 < 1 - e (N l).card := by linarith [he1 l]
  have hRk : 0 ≤ Rp k - 1 := by linarith [hRp k]
  have hRl : 0 ≤ Rp l - 1 := by linarith [hRp l]
  split_ifs
  · positivity
  · have := he0 (N k ∪ N l).card
    positivity
  · exact le_refl 0

lemma bX_symm (N : U → Finset U) (ς : U → U → ZMod p) (e : ℕ → ℝ) (Rp : U → ℝ) (k l : U) :
    bX N ς e Rp k l = bX N ς e Rp l k := by
  unfold bX
  by_cases h : k = l
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    by_cases hc : Consistent N ς k l
    · rw [ite_eq_left hc, ite_eq_left ((consistent_comm N ς k l).mp hc), inter_comm, union_comm,
        mul_comm (1 - e (N k).card)]
      ring
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((consistent_comm N ς k l).mpr h'))]

/-- **`lem:spec2:gram`**: `‖H̃ − 𝐇‖ ≤ ε'_H + ε_X` for coupling data (in the form of laws `ν`,
`P_k(· | x)` with the conditions of `def:coupling-data` on the support of `ν`), given the counts of
`lem:extension`(coarse) on the support of `ν`; `ρ` and `ρX` bound the row sums of `β` and of
`bX`. Hence `H̃ ⪯ 𝐇 + ε_H I` (`re_qform_le_of_normLe`). Here `H̃ = gramΓ ν (psiField P)`, the
matrix of `couplingM`. -/
theorem gram_comparison (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (N : U → Finset U) (ς : U → U → ZMod p) (hςN : ∀ k, ∀ j ∈ N k, ς j k ≠ 0)
    (e : ℕ → ℝ) (he0 : ∀ t, 0 ≤ e t) (he1 : ∀ k, e (N k).card < 1)
    (hcount : ∀ x, ν x ≠ 0 → CountsOK N ς e x)
    (P : U → (U → ZMod p) → ZMod p → ℝ) (Rp : U → ℝ) (hRp : ∀ k, 1 ≤ Rp k)
    (hP1 : ∀ x, ν x ≠ 0 → ∀ k, ∑ a, P k x a = 1)
    (hPsupp : ∀ x, ν x ≠ 0 → ∀ k a, a ∉ allowedSet N ς k x → P k x a = 0)
    (hPdens : ∀ x, ν x ≠ 0 → ∀ k, ∀ a ∈ allowedSet N ς k x,
      (Rp k)⁻¹ ≤ P k x a * (allowedSet N ς k x).card ∧ P k x a * (allowedSet N ς k x).card ≤ Rp k)
    {ρ ρX : ℝ} (hrow : ∀ k, ∑ l, betaG N ς e k l ≤ ρ) (hrowX : ∀ k, ∑ l, bX N ς e Rp k l ≤ ρX) :
    NormLe (fun k l => gramΓ ν (psiField P) k l - (modelH N ς k l : ℂ)) (ρ + ρX) := by
  have hX : NormLe (fun k l => ((gramT ν P k l - gramH0 ν N ς k l : ℝ) : ℂ)) ρX := by
    apply normLe_schur _ (bX N ς e Rp) (bX_nonneg N ς e he0 he1 Rp hRp) (bX_symm N ς e Rp) _
      hrowX
    intro k l
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hsplit : gramT ν P k l - gramH0 ν N ς k l =
        ∑ x, ν x * ((p : ℝ)⁻¹ * ∑ a, ((p : ℝ) * P k x a - 1) * ((p : ℝ) * P l x a - 1) -
          (p : ℝ)⁻¹ * ∑ a, psiM N ς x k a * psiM N ς x l a) := by
      unfold gramT gramH0
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [hsplit]
    calc _ ≤ ∑ x, ν x * bX N ς e Rp k l := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg (hν0 x)]
          by_cases hx : ν x = 0
          · rw [hx, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (deviation_bound N ς e he1 P Rp hRp x
              (hcount x hx) (hP1 x hx) (hPsupp x hx) (hPdens x hx) k l) (hν0 x)
      _ = bX N ς e Rp k l := by rw [← sum_mul, hν1, one_mul]
  have hM := gram_model ν hν0 hν1 N ς hςN e he0 he1 hcount hrow
  have hsum := normLe_add hX hM
  have hfun : (fun k l => gramΓ ν (psiField P) k l - (modelH N ς k l : ℂ)) =
      (fun k l => ((gramT ν P k l - gramH0 ν N ς k l : ℝ) : ℂ) +
        ((gramH0 ν N ς k l - modelH N ς k l : ℝ) : ℂ)) := by
    funext k l
    rw [gramΓ_psiField_eq]
    push_cast
    ring
  rw [hfun, add_comm ρ ρX]
  exact hsum

/-- **`lem:spec2:gram`, instance (B)**: for the uniform laws on the allowed sets, `Ψ_k = ψ_k`, so
`H̃ = 𝐇⁰` (and `ε_X = 0`). -/
theorem gramT_uniform (ν : (U → ZMod p) → ℝ) (N : U → Finset U) (ς : U → U → ZMod p)
    (P : U → (U → ZMod p) → ZMod p → ℝ)
    (hunif : ∀ x, ν x ≠ 0 → ∀ k a, P k x a =
      ((allowedSet N ς k x).card : ℝ)⁻¹ * (if a ∈ allowedSet N ς k x then 1 else 0))
    (k l : U) : gramT ν P k l = gramH0 ν N ς k l := by
  unfold gramT gramH0
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : ν x = 0
  · rw [hx, zero_mul, zero_mul]
  · congr 2
    refine sum_congr rfl fun a _ => ?_
    unfold psiM
    rw [hunif x hx k a, hunif x hx l a]
    ring

end Sarkozy.SpectralC
