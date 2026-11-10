module

public import Sarkozy.PartVLaws.Labellable

@[expose] public section

/-!
# Completion counts are nearly constant at large primes (`lem:graphs:sequential`(b))

`paper/sections/12_labellings.tex`, `lem:graphs:sequential`(b) (the density form: completion
counts of two feasible labellings of `A` differ by at most the factor `upper/lower`), with an
explicit factor at the tail primes.

* `upperProd_le_pow`: if every one-step ratio `stepUpper/stepLower` is at most `ρ`, the upper
  product along an ordering of `k` vertices is at most `ρ^k` times the lower product.
* `stepUpper_le_explicit`: at every `q` with `√q ≥ 2²⁵⁶` (every tail prime `q ≥ P₄ = 2⁵¹²`), for
  `t ≤ 20` earlier neighbours and `n ≤ 72` vertices, `ρ = 1 + 2⁻²⁰⁰` works.
* **`extCount_le_ratio`**: two feasible labellings of the same set `A` have completion counts
  within the factor `ρ^k`, `k = |W \ A|`, under Weil's bound.

These are the count-type inputs of the marginal ratios of the Schur rows (`FoldMarginals.lean`:
`m_b`, `T_F^b 𝟙`, `(T_F^b)^* 𝟙` are ratios of such counts).
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings

section Generic

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **The upper product is at most `ρ^k` times the lower product** when every one-step ratio with
at most `D` earlier neighbours is at most `ρ`. -/
theorem upperProd_le_pow (G : OrientedGraph W) {q : ℝ} (hq : 0 ≤ q) (n D : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hdeg : ∀ v, nbrCount G univ v ≤ D)
    (hstep : ∀ t ≤ D, stepUpper q t ≤ ρ * stepLower q n t) :
    ∀ (l : List W) (A : Finset W), upperProd G q A l ≤ ρ ^ l.length * lowerProd G q n A l
  | [], _ => by simp [upperProd, lowerProd]
  | v :: l, A => by
      simp only [upperProd, lowerProd, List.length_cons, pow_succ]
      have h1 := hstep _ ((nbrCount_le_univ G A v).trans (hdeg v))
      have h2 := upperProd_le_pow G hq n D hρ hdeg hstep l (insert v A)
      have hU : 0 ≤ upperProd G q (insert v A) l := upperProd_nonneg G hq l _
      have hS : 0 ≤ stepLower q n (nbrCount G A v) := le_max_left _ _
      have hL : 0 ≤ lowerProd G q n (insert v A) l := lowerProd_nonneg G q n l _
      calc stepUpper q (nbrCount G A v) * upperProd G q (insert v A) l
          ≤ (ρ * stepLower q n (nbrCount G A v)) *
              (ρ ^ l.length * lowerProd G q n (insert v A) l) :=
            mul_le_mul h1 h2 hU (mul_nonneg hρ hS)
        _ = ρ ^ l.length * ρ *
              (stepLower q n (nbrCount G A v) * lowerProd G q n (insert v A) l) := by
            ring

/-- **Completion counts of two feasible labellings of `A` are within the factor `ρ^k`**
(`lem:graphs:sequential`(b)), `k = |W \ A|`, under Weil's bound. -/
theorem extCount_le_ratio {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hW : WeilBound F)
    (G : OrientedGraph W) {D : ℕ} (hdeg : ∀ v, nbrCount G univ v ≤ D) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hstep : ∀ t ≤ D, stepUpper (Fintype.card F) t ≤
      ρ * stepLower (Fintype.card F) (Fintype.card W) t)
    {A : Finset W} {x x' : W → F} (hx : Feasible F G A x) (hx' : Feasible F G A x') :
    (extCount G A x : ℝ) ≤ ρ ^ (univ \ A).card * extCount G A x' := by
  classical
  set l := (univ \ A).toList with hl
  have hnd : l.Nodup := Finset.nodup_toList _
  have hcov : ∀ w, w ∈ A ∨ w ∈ l := fun w => by
    by_cases hw : w ∈ A
    · exact Or.inl hw
    · exact Or.inr (Finset.mem_toList.mpr (by simp [hw]))
  have hdisj : ∀ w ∈ l, w ∉ A := fun w hw => by
    have := Finset.mem_toList.mp hw
    simpa using this
  have hlen : l.length = (univ \ A).card := Finset.length_toList _
  obtain ⟨-, hU⟩ := extCount_bounds hW G (le_refl _) l A x hnd hcov hdisj hx
  obtain ⟨hL, -⟩ := extCount_bounds hW G (le_refl _) l A x' hnd hcov hdisj hx'
  have hPL := upperProd_le_pow G (Nat.cast_nonneg _) (Fintype.card W) D hρ hdeg hstep l A
  rw [hlen] at hPL
  calc (extCount G A x : ℝ) ≤ upperProd G (Fintype.card F) A l := hU
    _ ≤ ρ ^ (univ \ A).card * lowerProd G (Fintype.card F) (Fintype.card W) A l := hPL
    _ ≤ ρ ^ (univ \ A).card * extCount G A x' :=
        mul_le_mul_of_nonneg_left hL (pow_nonneg hρ _)

end Generic

/-! ## The explicit factor at the tail primes -/

/-- **The one-step ratio at the tail primes**: for `√q ≥ 2²⁵⁶`, `t ≤ 20` and `n ≤ 72`,
`(q + 𝔈_t)/2^t ≤ (1 + 2⁻²⁰⁰) · (q - 𝔈_t - 2^t n)/2^t`. -/
theorem stepUpper_le_explicit {q : ℝ} (hs : (2 : ℝ) ^ 256 ≤ Real.sqrt q) {n : ℕ} (hn : n ≤ 72)
    {t : ℕ} (ht : t ≤ 20) : stepUpper q t ≤ (1 + 1 / 2 ^ 200) * stepLower q n t := by
  set s := Real.sqrt q with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg q
  have hq0 : 0 ≤ q := by
    by_contra h
    push Not at h
    have : s = 0 := Real.sqrt_eq_zero'.mpr h.le
    have h256 : (0 : ℝ) < 2 ^ 256 := by positivity
    linarith
  have hsq : s * s = q := Real.mul_self_sqrt hq0
  have hA := gradedA_le_twenty ht
  have hB := gradedB_le_twenty ht
  have hA0 := gradedA_nonneg t
  have hB0 := gradedB_nonneg t
  have h2t : (2 : ℝ) ^ t ≤ 2 ^ 20 := pow_le_pow_right₀ (by norm_num) ht
  have h2t0 : (0 : ℝ) < 2 ^ t := by positivity
  have hn' : (n : ℝ) ≤ 72 := by exact_mod_cast hn
  have hc : (2 : ℝ) ^ t * n ≤ 2 ^ 20 * 72 :=
    mul_le_mul h2t hn' (Nat.cast_nonneg _) (by norm_num)
  have hc0 : 0 ≤ (2 : ℝ) ^ t * n := mul_nonneg h2t0.le (Nat.cast_nonneg _)
  -- `𝔈_t ≤ 2²⁵ s`
  have hE : softError q t ≤ 2 ^ 25 * s := by
    unfold softError
    rw [← hsdef]
    have h1 : gradedA t * s ≤ 8912898 * s := mul_le_mul_of_nonneg_right hA hs0
    have h2 : (524287 : ℝ) ≤ 2 ^ 24 * s := by
      have : (2 : ℝ) ^ 24 * 1 ≤ 2 ^ 24 * s :=
        mul_le_mul_of_nonneg_left (le_trans (by norm_num) hs) (by norm_num)
      linarith
    nlinarith
  have hE0 : 0 ≤ softError q t := softError_nonneg q t
  -- the key inequality `2𝔈_t + 2^t n ≤ 2⁻²⁰⁰ (q - 𝔈_t - 2^t n)`
  have hbig : (2 : ℝ) ^ 28 ≤ s := le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hs
  have hkey : q + softError q t ≤ (1 + 1 / 2 ^ 200) * (q - softError q t - 2 ^ t * n) := by
    have hcs : (2 : ℝ) ^ t * n ≤ 2 ^ 27 := le_trans hc (by norm_num)
    -- `q - 𝔈 - c ≥ s²/2` and `2𝔈 + c ≤ 2²⁸ s`
    have hlow : s * s / 2 ≤ q - softError q t - 2 ^ t * n := by
      have : 2 ^ 25 * s + 2 ^ 27 ≤ s * s / 2 := by nlinarith
      linarith
    have hup : 2 * softError q t + 2 ^ t * n ≤ 2 ^ 28 * s := by nlinarith
    have hss : (2 : ℝ) ^ 28 * s * 2 ^ 201 ≤ s * s := by
      have : (2 : ℝ) ^ 28 * 2 ^ 201 ≤ s := le_trans (by norm_num) hs
      nlinarith
    have : 2 * softError q t + 2 ^ t * n ≤ (1 / 2 ^ 200) * (q - softError q t - 2 ^ t * n) := by
      have h3 : (1 / 2 ^ 200 : ℝ) * (s * s / 2) ≤ (1 / 2 ^ 200) * (q - softError q t - 2 ^ t * n) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      have h4 : (2 : ℝ) ^ 28 * s ≤ (1 / 2 ^ 200) * (s * s / 2) := by
        rw [show (1 / 2 ^ 200 : ℝ) * (s * s / 2) = s * s / 2 ^ 201 by ring]
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
    nlinarith
  unfold stepUpper stepLower
  have hpos : 0 < (q - softError q t - 2 ^ t * n) / 2 ^ t := by
    apply div_pos _ h2t0
    nlinarith
  rw [max_eq_right hpos.le, mul_div_assoc']
  exact div_le_div_of_nonneg_right hkey h2t0.le

/-- **The one-step ratio at the tail primes, `ρ = 1 + 2²⁸/√q`**: for `√q ≥ 2²⁵⁶`, `t ≤ 20` and
`n ≤ 72`, `(q + 𝔈_t)/2^t ≤ (1 + 2²⁸/√q) · (q - 𝔈_t - 2^t n)/2^t`. The factor tends to `1` like
`q^{-1/2}`, as the counts of `lem:graphs:sequential` do. -/
theorem stepUpper_le_sqrt {q : ℝ} (hs : (2 : ℝ) ^ 256 ≤ Real.sqrt q) {n : ℕ} (hn : n ≤ 72)
    {t : ℕ} (ht : t ≤ 20) : stepUpper q t ≤ (1 + 2 ^ 28 / Real.sqrt q) * stepLower q n t := by
  set s := Real.sqrt q with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg q
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hq0 : 0 ≤ q := by
    by_contra h
    push Not at h
    have : s = 0 := Real.sqrt_eq_zero'.mpr h.le
    linarith
  have hsq : s * s = q := Real.mul_self_sqrt hq0
  have hA := gradedA_le_twenty ht
  have hB := gradedB_le_twenty ht
  have h2t : (2 : ℝ) ^ t ≤ 2 ^ 20 := pow_le_pow_right₀ (by norm_num) ht
  have h2t0 : (0 : ℝ) < 2 ^ t := by positivity
  have hn' : (n : ℝ) ≤ 72 := by exact_mod_cast hn
  have hc : (2 : ℝ) ^ t * n ≤ 2 ^ 20 * 72 :=
    mul_le_mul h2t hn' (Nat.cast_nonneg _) (by norm_num)
  have hc0 : 0 ≤ (2 : ℝ) ^ t * n := mul_nonneg h2t0.le (Nat.cast_nonneg _)
  have hE : softError q t ≤ 2 ^ 25 * s := by
    unfold softError
    rw [← hsdef]
    have h1 : gradedA t * s ≤ 8912898 * s := mul_le_mul_of_nonneg_right hA hs0
    have h2 : (524287 : ℝ) ≤ 2 ^ 24 * s := by
      have : (2 : ℝ) ^ 24 * 1 ≤ 2 ^ 24 * s :=
        mul_le_mul_of_nonneg_left (le_trans (by norm_num) hs) (by norm_num)
      linarith
    nlinarith
  have hE0 : 0 ≤ softError q t := softError_nonneg q t
  have hbig : (2 : ℝ) ^ 28 ≤ s := le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hs
  have hcs : (2 : ℝ) ^ t * n ≤ s / 2 := by
    have : (2 : ℝ) ^ 20 * 72 ≤ 2 ^ 28 / 2 := by norm_num
    linarith
  have hlow : s * s / 2 ≤ q - softError q t - 2 ^ t * n := by
    have : 2 ^ 25 * s + s / 2 ≤ s * s / 2 := by nlinarith
    linarith
  have hup : 2 * softError q t + 2 ^ t * n ≤ 2 ^ 27 * s := by nlinarith
  have hrhs : 2 ^ 27 * s ≤ (2 ^ 28 / s) * (q - softError q t - 2 ^ t * n) := by
    have h1 : (2 ^ 28 / s) * (s * s / 2) = 2 ^ 27 * s := by
      field_simp
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hkey : q + softError q t ≤ (1 + 2 ^ 28 / s) * (q - softError q t - 2 ^ t * n) := by
    nlinarith
  unfold stepUpper stepLower
  have hpos : 0 < (q - softError q t - 2 ^ t * n) / 2 ^ t := by
    apply div_pos _ h2t0
    nlinarith
  rw [max_eq_right hpos.le, mul_div_assoc']
  exact div_le_div_of_nonneg_right hkey h2t0.le

/-- `(1 + ε)^n ≤ 1 + 2nε` when `nε ≤ 1/2`. -/
theorem one_add_pow_le {ε : ℝ} (hε : 0 ≤ ε) : ∀ n : ℕ, (n : ℝ) * ε ≤ 1 / 2 →
    (1 + ε) ^ n ≤ 1 + 2 * n * ε
  | 0, _ => by simp
  | n + 1, h => by
      have hn : (n : ℝ) * ε ≤ 1 / 2 := by
        have : (n : ℝ) * ε ≤ ((n + 1 : ℕ) : ℝ) * ε :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hε
        linarith
      have ih := one_add_pow_le hε n hn
      rw [pow_succ]
      push_cast at h ⊢
      have h1 : (1 + ε) ^ n * (1 + ε) ≤ (1 + 2 * n * ε) * (1 + ε) :=
        mul_le_mul_of_nonneg_right ih (by linarith)
      nlinarith

end Sarkozy.PartVLaws
