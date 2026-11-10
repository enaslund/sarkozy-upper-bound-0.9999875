module

public import Sarkozy.Variance.WeightedMoment
public import Sarkozy.Variance.RootMarginal
public import Sarkozy.TraceMixing.Paley

@[expose] public section

/-!
# The concrete moment `E[P_adm 𝒲²]/p²`

`paper/sections/22_variance.tex`, `lem:record:weighted-moment` and `lem:record:root-marginal`(ii).
This file states the certificate identity
`cert:record:weighted-identity` for the concrete character sum
`E[P_adm 𝒲²]/p² = p⁻⁶ ∑_{x ∈ 𝔽_p⁴} P_adm(x) 𝒲(x)²` (`eAdm`, with `P_adm` = `pAdm` and
`𝒲` = `RootMarginal.softW`), as the `Prop` `WeightedIdentity`, and derives from it
the conclusions below. The identity is proved in `Sarkozy.Variance.WeightedIdentity`
for primes congruent to three modulo four; that module also supplies versions of
these conclusions with the certificate parameter discharged.

* `weightedMoment_concrete`: (a) `E[P_adm 𝒲²]/p² ≤ 10q + 24qr + 4q² + 14q³`, and, with H3
  (`Target.AhlgrenOno`), (b) `≤ 5q + 34qr + 11q³`;
* `weightedMoment_nAdm`: `16 · #adm = p(p-1)(p-3)(p-7)` for `p ≡ 3 (mod 4)`: the admissible event
  (`x₁ ≠ x₂`, `x₃ ≠ x₄`, `x₁, x₂ → x₃, x₄`) has probability `Z₄/16` (`lem:paley-triple`(a), via
  `TraceMixing.card_common_out`);
* `weightedMoment_adm_moment_le`: under the uniform law on the admissible quadruples,
  `E (𝒲/p)² ≤ E[P_adm 𝒲²]/(p² Z₄)` (`P_adm ≥ 0`, `P_adm = 16` on the admissible event);
* `weightedMoment_hmom`: the moment hypothesis `hmom` of `RootMarginal.rootMarginal_ii_second`,
  `E_adm (𝒲/p)² ≤ (5q + 34qr + 11q³)/Z₄`, for `p ≡ 3 (mod 4)`, `p > 7`, from H3 and the
  certificate identity.

* `weightedMoment_sum_fibre`: a uniform law whose labels are admissible with fibres of constant
  size over the admissible quadruples induces the uniform law on them;
* **`rootMarginal_ii_second_complete`**: the second bound `χ_p ≤ D_full²/L_low²` of
  `lem:record:root-marginal`(ii) with every character-sum input discharged (H1, H3 and the
  certificate identity are the literature and certificate inputs); the remaining hypotheses are
  the constant fibre size and the even-component sandwich `hs`;
* `HalfConf p`, the support of `λ_{F,p}` (six distinct labels with `y_{0,ℓ} → y_{2,ℓ'}`), with
  `weightedMoment_halfConf_fibre_card` (each admissible quadruple has `(p-4)(p-5)` completions)
  and **`rootMarginal_ii_second_lamF`**: the second bound of (ii) for the uniform law on
  `HalfConf p`, whose only non-literature hypotheses are the certificate identity and `hs`;
  `weightedMoment_halfConf_nonempty` (non-vacuity: `HalfConf p` is nonempty for every prime
  `p ≡ 3 (mod 4)`, `p > 7`).
-/

namespace Sarkozy.Variance.WeightedMoment

open Finset
open scoped BigOperators

section Adm

variable (p : ℕ) [Fact p.Prime]

/-- `P_adm(x) = ∏_{i ∈ {1,2}, k ∈ {3,4}} (1 + χ(x_k - x_i))`. -/
def pAdm (x₁ x₂ x₃ x₄ : ZMod p) : ℤ :=
  (1 + quadraticChar (ZMod p) (x₃ - x₁)) * (1 + quadraticChar (ZMod p) (x₄ - x₁)) *
    (1 + quadraticChar (ZMod p) (x₃ - x₂)) * (1 + quadraticChar (ZMod p) (x₄ - x₂))

/-- `E[P_adm 𝒲²]/p²` for independent uniform `x ∈ 𝔽_p⁴`, with `𝒲` the signed count of
`lem:record:weighted-moment` (`RootMarginal.softW`, signs `(-1,-1,1,1)`). -/
noncomputable def eAdm : ℝ :=
  ((∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
    pAdm p x₁ x₂ x₃ x₄ * RootMarginal.softW x₁ x₂ x₃ x₄ ^ 2 : ℤ) : ℝ) / ((p : ℝ) ^ 4 * (p : ℝ) ^ 2)

/-- **`cert:record:weighted-identity`**. Proved for `p ≡ 3 (mod 4)` by
`weightedIdentity_verified` in `Sarkozy.Variance.WeightedIdentity`. -/
def WeightedIdentity : Prop :=
  eAdm p = (4 + 8 * (1 / (p : ℝ))) * mG5 p + mG12 p + 24 * mG10 p + 5 * (1 / (p : ℝ)) -
    4 * (1 / (p : ℝ)) ^ 2 + 14 * (1 / (p : ℝ)) ^ 3 - 15 * (1 / (p : ℝ)) ^ 4

/-- **`lem:record:weighted-moment`, (a) and (b), at the concrete moment `E[P_adm 𝒲²]/p²`.** For an
odd prime, the certificate identity alone gives (a); with H3 it gives (b). -/
theorem weightedMoment_concrete (hp2 : p ≠ 2) (hid : WeightedIdentity p) {r : ℝ}
    (hr : r * Real.sqrt p = 1) :
    eAdm p ≤ 10 * (1 / (p : ℝ)) + 24 * (1 / (p : ℝ)) * r + 4 * (1 / (p : ℝ)) ^ 2 +
      14 * (1 / (p : ℝ)) ^ 3 ∧
    (Target.AhlgrenOno → eAdm p ≤ 5 * (1 / (p : ℝ)) + 34 * (1 / (p : ℝ)) * r +
      11 * (1 / (p : ℝ)) ^ 3) :=
  ⟨weightedMoment_a_final p hp2 rfl hr hid,
    fun hAO => (weightedMoment_b_final p hAO hp2 rfl hr hid).2⟩

/-- Admissible ordered quadruples: `x₁ ≠ x₂`, `x₃ ≠ x₄` and `x₁, x₂ → x₃, x₄`. -/
def IsAdm (x₁ x₂ x₃ x₄ : ZMod p) : Prop :=
  x₁ ≠ x₂ ∧ x₃ ≠ x₄ ∧ quadraticChar (ZMod p) (x₃ - x₁) = 1 ∧
    quadraticChar (ZMod p) (x₄ - x₁) = 1 ∧ quadraticChar (ZMod p) (x₃ - x₂) = 1 ∧
    quadraticChar (ZMod p) (x₄ - x₂) = 1

instance (x₁ x₂ x₃ x₄ : ZMod p) : Decidable (IsAdm p x₁ x₂ x₃ x₄) := by
  unfold IsAdm
  infer_instance

/-- The number of admissible ordered quadruples. -/
def nAdm : ℤ := ∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
  if IsAdm p x₁ x₂ x₃ x₄ then 1 else 0

theorem weightedMoment_isAdm_eq (x₁ x₂ x₃ x₄ : ZMod p) :
    (if IsAdm p x₁ x₂ x₃ x₄ then (1 : ℤ) else 0) =
      if x₁ = x₂ then 0 else
        (if quadraticChar (ZMod p) (x₃ - x₁) = 1 ∧ quadraticChar (ZMod p) (x₃ - x₂) = 1
          then 1 else 0) *
        (if quadraticChar (ZMod p) (x₄ - x₁) = 1 ∧ quadraticChar (ZMod p) (x₄ - x₂) = 1
          then 1 else 0) -
        (if x₃ = x₄ then
          (if quadraticChar (ZMod p) (x₃ - x₁) = 1 ∧ quadraticChar (ZMod p) (x₃ - x₂) = 1
            then 1 else 0) else 0) := by
  unfold IsAdm
  by_cases h12 : x₁ = x₂
  · simp [h12]
  by_cases h34 : x₃ = x₄
  · subst h34
    simp only [h12, ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte, not_false_eq_true]
    split_ifs <;> simp
  · simp only [h12, h34, ne_eq, not_false_eq_true, true_and, ↓reduceIte, sub_zero]
    split_ifs <;> simp_all

/-- **The admissible quadruples**: `16 · #adm = p(p-1)(p-3)(p-7)` for `p ≡ 3 (mod 4)`, i.e. the
admissible event has probability `p(p-1)k_p(k_p-1)/p⁴ = Z₄/16` (`k_p = (p-3)/4`,
`lem:paley-triple`(a)). -/
theorem weightedMoment_nAdm (h3 : p % 4 = 3) :
    16 * nAdm p = (p : ℤ) * ((p : ℤ) - 1) * ((p : ℤ) - 3) * ((p : ℤ) - 7) := by
  have hp2 : p ≠ 2 := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hc3 : Fintype.card (ZMod p) % 4 = 3 := by rw [ZMod.card]; exact h3
  have hinner : ∀ x₁ x₂ : ZMod p, 16 * (∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
      if IsAdm p x₁ x₂ x₃ x₄ then (1 : ℤ) else 0) =
      if x₁ = x₂ then 0 else ((p : ℤ) - 3) * ((p : ℤ) - 7) := by
    intro x₁ x₂
    simp only [weightedMoment_isAdm_eq]
    by_cases h12 : x₁ = x₂
    · simp [h12]
    simp only [h12, ↓reduceIte]
    set c : ZMod p → ℤ := fun x => if quadraticChar (ZMod p) (x - x₁) = 1 ∧
      quadraticChar (ZMod p) (x - x₂) = 1 then 1 else 0 with hc
    have hsum : 4 * ∑ x, c x = (p : ℤ) - 3 := by
      have h := TraceMixing.card_common_out hF hc3 h12
      rw [ZMod.card] at h
      rw [← h, hc]
      congr 1
      rw [Finset.sum_boole]
    have e : ∑ x₃ : ZMod p, ∑ x₄ : ZMod p, (c x₃ * c x₄ - if x₃ = x₄ then c x₃ else 0) =
        (∑ x, c x) * (∑ x, c x) - ∑ x, c x := by
      simp only [sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
      rw [sum_mul_sum]
    rw [e]
    nlinarith [hsum]
  have : (16 : ℤ) * nAdm p = ∑ x₁ : ZMod p, ∑ x₂ : ZMod p,
      16 * (∑ x₃ : ZMod p, ∑ x₄ : ZMod p, if IsAdm p x₁ x₂ x₃ x₄ then (1 : ℤ) else 0) := by
    unfold nAdm
    rw [mul_sum]
    apply sum_congr rfl
    intro x₁ _
    rw [mul_sum]
  rw [this]
  simp only [hinner]
  have hif : ∀ x₁ x₂ : ZMod p, (if x₁ = x₂ then (0 : ℤ) else ((p : ℤ) - 3) * ((p : ℤ) - 7)) =
      ((p : ℤ) - 3) * ((p : ℤ) - 7) - if x₁ = x₂ then ((p : ℤ) - 3) * ((p : ℤ) - 7) else 0 := by
    intro x₁ x₂
    split_ifs <;> ring
  simp only [hif, sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, sum_ite_eq,
    mem_univ, ↓reduceIte]
  ring

theorem weightedMoment_pAdm_nonneg (x₁ x₂ x₃ x₄ : ZMod p) : 0 ≤ pAdm p x₁ x₂ x₃ x₄ := by
  have h : ∀ a : ZMod p, 0 ≤ 1 + quadraticChar (ZMod p) a := by
    intro a
    rcases weightedMoment_chi_vals p a with h | h | h <;> rw [h] <;> norm_num
  unfold pAdm
  have := h (x₃ - x₁)
  have := h (x₄ - x₁)
  have := h (x₃ - x₂)
  have := h (x₄ - x₂)
  positivity

/-- On the admissible event `P_adm = 16`, and `P_adm ≥ 0` everywhere, so
`16 ∑_{adm} 𝒲² ≤ ∑_x P_adm 𝒲²`. -/
theorem weightedMoment_adm_sum_le :
    16 * (∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
      if IsAdm p x₁ x₂ x₃ x₄ then RootMarginal.softW x₁ x₂ x₃ x₄ ^ 2 else 0) ≤
    ∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
      pAdm p x₁ x₂ x₃ x₄ * RootMarginal.softW x₁ x₂ x₃ x₄ ^ 2 := by
  simp only [mul_sum]
  apply sum_le_sum
  intro x₁ _
  apply sum_le_sum
  intro x₂ _
  apply sum_le_sum
  intro x₃ _
  apply sum_le_sum
  intro x₄ _
  split_ifs with h
  · obtain ⟨-, -, a, b, c, d⟩ := h
    have : pAdm p x₁ x₂ x₃ x₄ = 16 := by
      unfold pAdm
      rw [a, b, c, d]
      norm_num
    rw [this]
  · rw [mul_zero]
    exact mul_nonneg (weightedMoment_pAdm_nonneg p x₁ x₂ x₃ x₄) (sq_nonneg _)

/-- **The transfer to the admissible quadruples** (proof of `lem:record:root-marginal`(ii)):
under the uniform law on the admissible ordered quadruples, for `p ≡ 3 (mod 4)`, `p > 7`,
`E_adm (𝒲/p)² ≤ E[P_adm 𝒲²]/(p² Z₄)`. -/
theorem weightedMoment_adm_moment_le (h3 : p % 4 = 3) (h7 : 7 < p) :
    (∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
      if IsAdm p x₁ x₂ x₃ x₄ then ((RootMarginal.softW x₁ x₂ x₃ x₄ : ℝ) / p) ^ 2 else 0) /
        (nAdm p : ℝ) ≤ eAdm p / RootMarginal.Z4 (1 / (p : ℝ)) := by
  have hp7 : (7 : ℝ) < p := by exact_mod_cast h7
  have hp0 : (0 : ℝ) < p := by linarith
  have hN : (16 : ℝ) * nAdm p = (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 3) * ((p : ℝ) - 7) := by
    exact_mod_cast weightedMoment_nAdm p h3
  have hNpos : (0 : ℝ) < nAdm p := by
    have : 0 < (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 3) * ((p : ℝ) - 7) := by
      have h1 : 0 < (p : ℝ) - 1 := by linarith
      have h2 : 0 < (p : ℝ) - 3 := by linarith
      have h3' : 0 < (p : ℝ) - 7 := by linarith
      positivity
    linarith
  have hZ : RootMarginal.Z4 (1 / (p : ℝ)) = ((p : ℝ) - 1) * ((p : ℝ) - 3) * ((p : ℝ) - 7) /
      (p : ℝ) ^ 3 := by
    unfold RootMarginal.Z4
    field_simp
  have hS := weightedMoment_adm_sum_le p
  have hS' : 16 * ((∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
      if IsAdm p x₁ x₂ x₃ x₄ then RootMarginal.softW x₁ x₂ x₃ x₄ ^ 2 else 0 : ℤ) : ℝ) ≤
      ((∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
        pAdm p x₁ x₂ x₃ x₄ * RootMarginal.softW x₁ x₂ x₃ x₄ ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast hS
  have hL : (∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
      if IsAdm p x₁ x₂ x₃ x₄ then ((RootMarginal.softW x₁ x₂ x₃ x₄ : ℝ) / p) ^ 2 else 0) =
      ((∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
        if IsAdm p x₁ x₂ x₃ x₄ then RootMarginal.softW x₁ x₂ x₃ x₄ ^ 2 else 0 : ℤ) : ℝ) /
        (p : ℝ) ^ 2 := by
    push_cast
    rw [sum_div]
    apply sum_congr rfl
    intro x₁ _
    rw [sum_div]
    apply sum_congr rfl
    intro x₂ _
    rw [sum_div]
    apply sum_congr rfl
    intro x₃ _
    rw [sum_div]
    apply sum_congr rfl
    intro x₄ _
    split_ifs
    · rw [div_pow]
    · rw [zero_div]
  rw [hL, hZ]
  unfold eAdm
  set A := ((∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
      if IsAdm p x₁ x₂ x₃ x₄ then RootMarginal.softW x₁ x₂ x₃ x₄ ^ 2 else 0 : ℤ) : ℝ)
  set B := ((∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
      pAdm p x₁ x₂ x₃ x₄ * RootMarginal.softW x₁ x₂ x₃ x₄ ^ 2 : ℤ) : ℝ)
  have hq1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hq3 : (0 : ℝ) < (p : ℝ) - 3 := by linarith
  have hq7 : (0 : ℝ) < (p : ℝ) - 7 := by linarith
  rw [div_div, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hK : 0 < ((p : ℝ) - 1) * ((p : ℝ) - 3) * ((p : ℝ) - 7) := by positivity
  have hn' : (nAdm p : ℝ) = (p : ℝ) * (((p : ℝ) - 1) * ((p : ℝ) - 3) * ((p : ℝ) - 7)) / 16 := by
    linarith [hN]
  calc A * (((p : ℝ) - 1) * ((p : ℝ) - 3) * ((p : ℝ) - 7))
      ≤ B / 16 * (((p : ℝ) - 1) * ((p : ℝ) - 3) * ((p : ℝ) - 7)) :=
        mul_le_mul_of_nonneg_right (by linarith) hK.le
    _ = B / ((p : ℝ) ^ 4 * (p : ℝ) ^ 2) * (p : ℝ) ^ 3 * ((p : ℝ) ^ 2 * (nAdm p : ℝ)) := by
        rw [hn']
        field_simp

/-- **`hmom` of `lem:record:root-marginal`(ii), discharged**: under H3 and the certificate identity,
for `p ≡ 3 (mod 4)`, `p > 7`, the uniform law on the admissible quadruples has
`E (𝒲/p)² ≤ (5q + 34qr + 11q³)/Z₄`. -/
theorem weightedMoment_hmom (h3 : p % 4 = 3) (h7 : 7 < p) (hAO : Target.AhlgrenOno)
    (hid : WeightedIdentity p) {r : ℝ} (hr : r * Real.sqrt p = 1) :
    (∑ x₁ : ZMod p, ∑ x₂ : ZMod p, ∑ x₃ : ZMod p, ∑ x₄ : ZMod p,
      if IsAdm p x₁ x₂ x₃ x₄ then ((RootMarginal.softW x₁ x₂ x₃ x₄ : ℝ) / p) ^ 2 else 0) /
        (nAdm p : ℝ) ≤
      (5 * (1 / (p : ℝ)) + 34 * (1 / (p : ℝ)) * r + 11 * (1 / (p : ℝ)) ^ 3) /
        RootMarginal.Z4 (1 / (p : ℝ)) := by
  have hp2 : p ≠ 2 := by omega
  have hp7 : (7 : ℝ) < p := by exact_mod_cast h7
  have hZ : 0 < RootMarginal.Z4 (1 / (p : ℝ)) := by
    unfold RootMarginal.Z4
    have h1 : 1 / (p : ℝ) < 1 / 7 := one_div_lt_one_div_of_lt (by norm_num) hp7
    have h0 : 0 < 1 / (p : ℝ) := by positivity
    have : 0 < 1 - 1 / (p : ℝ) := by linarith
    have : 0 < 1 - 3 * (1 / (p : ℝ)) := by linarith
    have : 0 < 1 - 7 * (1 / (p : ℝ)) := by linarith
    positivity
  refine (weightedMoment_adm_moment_le p h3 h7).trans ?_
  exact div_le_div_of_nonneg_right ((weightedMoment_concrete p hp2 hid hr).2 hAO) hZ.le

end Adm

/-! ### Fibres over the admissible quadruples, and the second bound of (ii) in full -/

section Fibre

variable (p : ℕ) [Fact p.Prime]

/-- Summing over a finite type `S` whose labels `x(y)` are admissible, with fibres of constant
size `m` over the admissible quadruples. -/
theorem weightedMoment_sum_fibre {S : Type*} [Fintype S] (x₁ x₂ x₃ x₄ : S → ZMod p) {m : ℕ}
    (hadm : ∀ y, IsAdm p (x₁ y) (x₂ y) (x₃ y) (x₄ y))
    (hfib : ∀ a b c d : ZMod p, IsAdm p a b c d →
      (univ.filter fun y => x₁ y = a ∧ x₂ y = b ∧ x₃ y = c ∧ x₄ y = d).card = m)
    (f : ZMod p → ZMod p → ZMod p → ZMod p → ℝ) :
    ∑ y, f (x₁ y) (x₂ y) (x₃ y) (x₄ y) =
      (m : ℝ) * ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p,
        if IsAdm p a b c d then f a b c d else 0 := by
  classical
  set g : S → ZMod p × ZMod p × ZMod p × ZMod p := fun y => (x₁ y, x₂ y, x₃ y, x₄ y)
  have h1 : ∑ y, f (x₁ y) (x₂ y) (x₃ y) (x₄ y) =
      ∑ q : ZMod p × ZMod p × ZMod p × ZMod p,
        ((univ.filter fun y => g y = q).card : ℝ) * f q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    rw [← Finset.sum_fiberwise univ g (fun y => f (x₁ y) (x₂ y) (x₃ y) (x₄ y))]
    apply sum_congr rfl
    intro q _
    rw [sum_congr rfl (g := fun _ => f q.1 q.2.1 q.2.2.1 q.2.2.2), sum_const, nsmul_eq_mul]
    intro y hy
    rw [mem_filter] at hy
    simp only [← hy.2, g]
  have h2 : ∀ q : ZMod p × ZMod p × ZMod p × ZMod p,
      ((univ.filter fun y => g y = q).card : ℝ) * f q.1 q.2.1 q.2.2.1 q.2.2.2 =
      (m : ℝ) * (if IsAdm p q.1 q.2.1 q.2.2.1 q.2.2.2 then f q.1 q.2.1 q.2.2.1 q.2.2.2 else 0) := by
    intro q
    obtain ⟨a, b, c, d⟩ := q
    have hset : (univ.filter fun y => g y = (a, b, c, d)) =
        univ.filter fun y => x₁ y = a ∧ x₂ y = b ∧ x₃ y = c ∧ x₄ y = d := by
      ext y
      simp [g, Prod.ext_iff]
    rw [hset]
    by_cases h : IsAdm p a b c d
    · simp only [h, ↓reduceIte, hfib a b c d h]
    · have : (univ.filter fun y => x₁ y = a ∧ x₂ y = b ∧ x₃ y = c ∧ x₄ y = d) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro y _ hy
        obtain ⟨e1, e2, e3, e4⟩ := hy
        apply h
        rw [← e1, ← e2, ← e3, ← e4]
        exact hadm y
      simp only [this, card_empty, Nat.cast_zero, zero_mul, h, ↓reduceIte, mul_zero]
  rw [h1]
  simp only [h2]
  rw [← mul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro b _
  rw [Fintype.sum_prod_type]

/-- **`lem:record:root-marginal`(ii), second bound, with every character-sum input discharged.**
At a prime `p ≡ 3 (mod 4)`, `p > 7`, assume H1 (`Labellings.WeilBound (ZMod p)`), H3
(`Target.AhlgrenOno`) and the certificate identity (`WeightedIdentity p`,
`cert:record:weighted-identity`). Let `S` carry the uniform law `μ` and four labels `x(y)` that
are admissible, with fibres of constant size `m` over the admissible quadruples (under `λ_{F,p}`
every admissible quadruple has `(p-4)(p-5)` completions); let `n = |signed neighbourhood| - n₁`
with `n₁ ∈ {0,1,2}`, and let `ς` satisfy the even-component sandwich (the remaining
**hypothesis** `hs`). Then `χ²(ν ‖ μ) ≤ D_full²/L_low²` for `ν = ς μ / E_μ ς`, `q = 1/p`,
`r = p^{-1/2}`. -/
theorem rootMarginal_ii_second_complete (h3 : p % 4 = 3) (h7 : 7 < p)
    (hW : Labellings.WeilBound (ZMod p)) (hAO : Target.AhlgrenOno) (hid : WeightedIdentity p)
    {S : Type*} [Fintype S] (μ : FiniteLaw S) (hunif : ∀ y, μ.weight y = 1 / Fintype.card S)
    {q r : ℝ} (hq : q = 1 / (p : ℝ)) (hr : r * Real.sqrt p = 1)
    (hlow : RootMarginal.LowerFactors q r)
    (x₁ x₂ x₃ x₄ : S → ZMod p) (hadm : ∀ y, IsAdm p (x₁ y) (x₂ y) (x₃ y) (x₄ y)) {m : ℕ}
    (hfib : ∀ a b c d : ZMod p, IsAdm p a b c d →
      (univ.filter fun y => x₁ y = a ∧ x₂ y = b ∧ x₃ y = c ∧ x₄ y = d).card = m)
    (n₁ n s : S → ℝ) (hn₁ : ∀ y, n₁ y = 0 ∨ n₁ y = 1 ∨ n₁ y = 2)
    (hn : ∀ y, n y = ((RootMarginal.signedNbhd (x₁ y) (x₂ y) (x₃ y) (x₄ y)).card : ℝ) - n₁ y)
    (hs : ∀ y, (1 - 24 * RootMarginal.aP q r) * (n y * (n y - 1) / ((p : ℝ) / 16) ^ 2) ≤ s y ∧
      s y ≤ n y * (n y - 1) / ((p : ℝ) / 16) ^ 2) :
    chiSq (fun y => μ.weight y * s y / ∑ z, μ.weight z * s z) μ.weight ≤
      RootMarginal.Dfull q r ^ 2 / RootMarginal.Llow q r ^ 2 := by
  have hp2 : p ≠ 2 := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hc3 : Fintype.card (ZMod p) % 4 = 3 := by rw [ZMod.card]; exact h3
  have hm := TraceMixing.chi_neg_one_of_three (F := ZMod p) hc3
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  obtain ⟨y₀⟩ : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := μ.total
    simp at this
  have hS0 : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨y₀⟩
  have hpos : ∀ y, 0 < μ.weight y := fun y => by rw [hunif]; positivity
  -- the moment hypothesis, from the fibres
  have hcardS : (Fintype.card S : ℝ) = (m : ℝ) * (nAdm p : ℝ) := by
    have h := weightedMoment_sum_fibre p x₁ x₂ x₃ x₄ hadm hfib (fun _ _ _ _ => (1 : ℝ))
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
    rw [h]
    unfold nAdm
    push_cast
    rfl
  have hmom : μ.expect (fun y => ((RootMarginal.softW (x₁ y) (x₂ y) (x₃ y) (x₄ y) : ℝ) /
      (Fintype.card (ZMod p) : ℝ)) ^ 2) ≤
      (5 * q + 34 * q * r + 11 * q ^ 3) / RootMarginal.Z4 q := by
    rw [hcard]
    have h := weightedMoment_sum_fibre p x₁ x₂ x₃ x₄ hadm hfib
      (fun a b c d => ((RootMarginal.softW a b c d : ℝ) / p) ^ 2)
    have hE : μ.expect (fun y => ((RootMarginal.softW (x₁ y) (x₂ y) (x₃ y) (x₄ y) : ℝ) /
        (p : ℝ)) ^ 2) = (∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p,
          if IsAdm p a b c d then ((RootMarginal.softW a b c d : ℝ) / p) ^ 2 else 0) /
          (nAdm p : ℝ) := by
      unfold FiniteLaw.expect
      simp only [hunif]
      rw [← mul_sum, h, hcardS]
      have hm0 : (m : ℝ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hcardS
        linarith
      field_simp
    rw [hE, hq]
    exact weightedMoment_hmom p h3 h7 hAO hid hr
  refine RootMarginal.rootMarginal_ii_second_of_labels hF hm hW μ hpos (by rw [hcard]; exact hq)
    (by rw [hcard]; exact hr) hlow x₁ x₂ x₃ x₄ ?_ ?_ n₁ n s hn₁ hn hmom (by rw [hcard]; exact hs)
  · intro y
    obtain ⟨h12, h34, a13, a14, a23, a24⟩ := hadm y
    have ne : ∀ u v : ZMod p, quadraticChar (ZMod p) (v - u) = 1 → u ≠ v := by
      intro u v h huv
      rw [huv, sub_self, quadraticChar_zero] at h
      exact zero_ne_one h
    exact ⟨h12, ne _ _ a13, ne _ _ a14, ne _ _ a23, ne _ _ a24, h34⟩
  · intro y
    obtain ⟨-, -, a13, a14, a23, -⟩ := hadm y
    exact ⟨a13, a14, a23⟩

end Fibre

/-! ### The support of `λ_{F,p}` and its fibres -/

section LamF

variable (p : ℕ) [Fact p.Prime]

/-- Six labels `(y_{0,0}, y_{0,1}, y_{1,0}, y_{1,1}, y_{2,0}, y_{2,1})` at one prime. -/
abbrev Six := ZMod p × ZMod p × ZMod p × ZMod p × ZMod p × ZMod p

/-- The support of the two-layer `F` law `λ_{F,p}` (`subsec:variance:eligible`): six distinct
labels with `y_{0,ℓ} → y_{2,ℓ'}` for all `ℓ, ℓ'`. -/
def IsHalf (y : Six p) : Prop :=
  [y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2].Nodup ∧
    quadraticChar (ZMod p) (y.2.2.2.2.1 - y.1) = 1 ∧
    quadraticChar (ZMod p) (y.2.2.2.2.2 - y.1) = 1 ∧
    quadraticChar (ZMod p) (y.2.2.2.2.1 - y.2.1) = 1 ∧
    quadraticChar (ZMod p) (y.2.2.2.2.2 - y.2.1) = 1

instance : DecidablePred (IsHalf p) := fun y => by
  unfold IsHalf
  infer_instance

/-- The half configurations at the fold chamber, the support of `λ_{F,p}`. -/
abbrev HalfConf := {y : Six p // IsHalf p y}

/-- The four labels `x(y) = (y_{0,0}, y_{0,1}, y_{2,0}, y_{2,1})` are admissible. -/
theorem weightedMoment_halfConf_adm (y : HalfConf p) :
    IsAdm p y.1.1 y.1.2.1 y.1.2.2.2.2.1 y.1.2.2.2.2.2 := by
  obtain ⟨⟨a, b, u, v, c, d⟩, hnd, h1, h2, h3, h4⟩ := y
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hnd
  exact ⟨hnd.1.1, hnd.2.2.2.2, h1, h2, h3, h4⟩

theorem weightedMoment_ne_of_chi {u v : ZMod p} (h : quadraticChar (ZMod p) (v - u) = 1) :
    u ≠ v := by
  intro huv
  rw [huv, sub_self, quadraticChar_zero] at h
  exact zero_ne_one h

/-- **The fibres of `λ_{F,p}` over the admissible quadruples**: each admissible quadruple
`(a, b, c, d)` has the completions `(y_{1,0}, y_{1,1})`, the ordered pairs of distinct labels
outside `{a, b, c, d}`. -/
theorem weightedMoment_halfConf_fibre (a b c d : ZMod p) (h : IsAdm p a b c d) :
    (univ.filter fun y : HalfConf p => y.1.1 = a ∧ y.1.2.1 = b ∧ y.1.2.2.2.2.1 = c ∧
      y.1.2.2.2.2.2 = d).card =
      ((univ \ ({a, b, c, d} : Finset (ZMod p))).offDiag).card := by
  obtain ⟨hab, hcd, hac, had, hbc, hbd⟩ := h
  have nac := weightedMoment_ne_of_chi p hac
  have nad := weightedMoment_ne_of_chi p had
  have nbc := weightedMoment_ne_of_chi p hbc
  have nbd := weightedMoment_ne_of_chi p hbd
  refine card_bij' (fun y _ => (y.1.2.2.1, y.1.2.2.2.1))
    (fun uv huv => ⟨(a, b, uv.1, uv.2, c, d), by
      rw [mem_offDiag, mem_sdiff, mem_sdiff] at huv
      obtain ⟨⟨-, hu⟩, ⟨-, hv⟩, huv⟩ := huv
      simp only [mem_insert, mem_singleton, not_or] at hu hv
      refine ⟨?_, hac, had, hbc, hbd⟩
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      exact ⟨⟨hab, fun e => hu.1 e.symm, fun e => hv.1 e.symm, nac, nad⟩,
        ⟨fun e => hu.2.1 e.symm, fun e => hv.2.1 e.symm, nbc, nbd⟩, ⟨huv, hu.2.2.1, hu.2.2.2⟩,
        ⟨hv.2.2.1, hv.2.2.2⟩, hcd⟩⟩) ?_ ?_ ?_ ?_
  · intro y hy
    revert hy
    obtain ⟨⟨a', b', u, v, c', d'⟩, hnd, -⟩ := y
    intro hy
    rw [mem_filter] at hy
    obtain ⟨-, e1, e2, e3, e4⟩ := hy
    simp only at e1 e2 e3 e4
    subst e1 e2 e3 e4
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true] at hnd
    rw [mem_offDiag, mem_sdiff, mem_sdiff]
    simp only [mem_univ, true_and, mem_insert, mem_singleton, not_or]
    exact ⟨⟨fun e => hnd.1.2.1 e.symm, fun e => hnd.2.1.1 e.symm, hnd.2.2.1.2.1,
      hnd.2.2.1.2.2⟩, ⟨fun e => hnd.1.2.2.1 e.symm, fun e => hnd.2.1.2.1 e.symm,
      hnd.2.2.2.1.1, hnd.2.2.2.1.2⟩, hnd.2.2.1.1⟩
  · intro uv _
    simp
  · intro y hy
    revert hy
    obtain ⟨⟨a', b', u, v, c', d'⟩, -⟩ := y
    intro hy
    rw [mem_filter] at hy
    obtain ⟨-, e1, e2, e3, e4⟩ := hy
    apply Subtype.ext
    simp only at e1 e2 e3 e4
    subst e1 e2 e3 e4
    rfl
  · intro uv _
    rfl

/-- The fibre size of `λ_{F,p}` over an admissible quadruple: `(p-4)² - (p-4) = (p-4)(p-5)`. -/
theorem weightedMoment_halfConf_fibre_card (a b c d : ZMod p) (h : IsAdm p a b c d) :
    (univ.filter fun y : HalfConf p => y.1.1 = a ∧ y.1.2.1 = b ∧ y.1.2.2.2.2.1 = c ∧
      y.1.2.2.2.2.2 = d).card = (p - 4) * (p - 4) - (p - 4) := by
  rw [weightedMoment_halfConf_fibre p a b c d h, offDiag_card]
  obtain ⟨hab, hcd, hac, had, hbc, hbd⟩ := h
  have nac := weightedMoment_ne_of_chi p hac
  have nad := weightedMoment_ne_of_chi p had
  have nbc := weightedMoment_ne_of_chi p hbc
  have nbd := weightedMoment_ne_of_chi p hbd
  have hT : ({a, b, c, d} : Finset (ZMod p)).card = 4 :=
    RootMarginal.rootMarginal_card_four hab nac nad nbc nbd hcd
  rw [card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card, hT]

/-- **`lem:record:root-marginal`(ii), second bound, for the half law of the root against
`λ_{F,p}` itself.** `μ` is the uniform law on the half configurations `HalfConf p` (the support
of `λ_{F,p}`). With H1, H3 and the certificate identity, for `p ≡ 3 (mod 4)`, `p > 7`, and the
lower factors at `(1/p, p^{-1/2})`: if `n = |signed neighbourhood of (y_{0,0}, y_{0,1}, y_{2,0},
y_{2,1})| - n₁`, `n₁ ∈ {0,1,2}`, and `ς` satisfies the even-component sandwich (the remaining
**hypothesis** `hs`, from the odd-component counts), then `χ²(ν ‖ λ_{F,p}) ≤ D_full²/L_low²`. -/
theorem rootMarginal_ii_second_lamF (h3 : p % 4 = 3) (h7 : 7 < p)
    (hW : Labellings.WeilBound (ZMod p)) (hAO : Target.AhlgrenOno) (hid : WeightedIdentity p)
    (μ : FiniteLaw (HalfConf p)) (hunif : ∀ y, μ.weight y = 1 / Fintype.card (HalfConf p))
    {q r : ℝ} (hq : q = 1 / (p : ℝ)) (hr : r * Real.sqrt p = 1)
    (hlow : RootMarginal.LowerFactors q r) (n₁ n s : HalfConf p → ℝ)
    (hn₁ : ∀ y, n₁ y = 0 ∨ n₁ y = 1 ∨ n₁ y = 2)
    (hn : ∀ y, n y = ((RootMarginal.signedNbhd y.1.1 y.1.2.1 y.1.2.2.2.2.1
      y.1.2.2.2.2.2).card : ℝ) - n₁ y)
    (hs : ∀ y, (1 - 24 * RootMarginal.aP q r) * (n y * (n y - 1) / ((p : ℝ) / 16) ^ 2) ≤ s y ∧
      s y ≤ n y * (n y - 1) / ((p : ℝ) / 16) ^ 2) :
    chiSq (fun y => μ.weight y * s y / ∑ z, μ.weight z * s z) μ.weight ≤
      RootMarginal.Dfull q r ^ 2 / RootMarginal.Llow q r ^ 2 :=
  rootMarginal_ii_second_complete p h3 h7 hW hAO hid μ hunif hq hr hlow
    (fun y => y.1.1) (fun y => y.1.2.1) (fun y => y.1.2.2.2.2.1) (fun y => y.1.2.2.2.2.2)
    (weightedMoment_halfConf_adm p) (weightedMoment_halfConf_fibre_card p) n₁ n s hn₁ hn hs

/-- **Non-vacuity**: the support of `λ_{F,p}` is nonempty for every prime `p ≡ 3 (mod 4)`,
`p > 7` (two common out-neighbours `c ≠ d` of `0, 1`, by `lem:paley-triple`(a), and two further
labels). -/
theorem weightedMoment_halfConf_nonempty (h3 : p % 4 = 3) (h7 : 7 < p) :
    Nonempty (HalfConf p) := by
  have hp2 : p ≠ 2 := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hc3 : Fintype.card (ZMod p) % 4 = 3 := by rw [ZMod.card]; exact h3
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  have hC := TraceMixing.card_common_out hF hc3 h01
  rw [ZMod.card] at hC
  set C := univ.filter fun x : ZMod p =>
    quadraticChar (ZMod p) (x - 0) = 1 ∧ quadraticChar (ZMod p) (x - 1) = 1 with hCdef
  have hC2 : 1 < C.card := by
    have : (11 : ℤ) ≤ p := by
      have : 11 ≤ p := by omega
      exact_mod_cast this
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := one_lt_card.mp hC2
  rw [hCdef, mem_filter] at hc hd
  obtain ⟨-, hc0, hc1⟩ := hc
  obtain ⟨-, hd0, hd1⟩ := hd
  have nc0 := weightedMoment_ne_of_chi p hc0
  have nd0 := weightedMoment_ne_of_chi p hd0
  have nc1 := weightedMoment_ne_of_chi p hc1
  have nd1 := weightedMoment_ne_of_chi p hd1
  set R := univ \ ({0, 1, c, d} : Finset (ZMod p)) with hRdef
  have hR2 : 1 < R.card := by
    rw [hRdef, card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
    have : ({0, 1, c, d} : Finset (ZMod p)).card ≤ 4 := card_le_four
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hR2
  rw [hRdef, mem_sdiff] at hu hv
  simp only [mem_insert, mem_singleton, not_or] at hu hv
  obtain ⟨-, hu0, hu1, huc, hud⟩ := hu
  obtain ⟨-, hv0, hv1, hvc, hvd⟩ := hv
  refine ⟨⟨(0, 1, u, v, c, d), ?_, by simpa using hc0, by simpa using hd0, hc1, hd1⟩⟩
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true]
  exact ⟨⟨h01, fun e => hu0 e.symm, fun e => hv0 e.symm, nc0, nd0⟩,
    ⟨fun e => hu1 e.symm, fun e => hv1 e.symm, nc1, nd1⟩, ⟨huv, huc, hud⟩, ⟨hvc, hvd⟩, hcd⟩

end LamF

end Sarkozy.Variance.WeightedMoment
