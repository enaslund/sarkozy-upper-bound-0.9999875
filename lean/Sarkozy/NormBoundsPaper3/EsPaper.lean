module

public import Sarkozy.NormBoundsPaper3.Final

@[expose] public section

/-!
# The one-prime matching input at the paper's constant `s^E_p` (NB3)

`paper/sections/21_middle_records.tex`, `lem:record:e-orthogonal`(c): "`‖Sym(K₁ − K^E_0)‖ ≤ s^E_p`,
where `s^E_p = 𝔰_p + 2e_E/(1 − 2q) + q²/((1 − q)(1 − 2q)) + 18q²/((1 − q)(1 − 9q))`", with
`𝔰_p = q/(1 − q)·[(1 + √2)/(1 − 9q) + 7q/(Z(1 − 9q)(1 − 2q))]` (`lem:record:e-law`(d)),
`e_E = qr/((1 − q)(1 − 3q))^{1/2}·(2 + 4q²/(1 − 2q)²)^{1/2}` (`lem:record:e-orthogonal`(b)) and
`Z = (1 − q)(1 − 2q)`; `lem:record:exact-marginal-e`(i): "Each of `s^E_p/r`, … is a nondecreasing
function of `(q, r)`"; (ii): "`s_E(X) = s^E/r`" at `(q_X, r_X)`, `r_X = 1/⌊√X⌋`.

* `frakS`, `eEc`, **`sEpaper q r`**: the paper's `𝔰_p`, `e_E`, `s^E_p` as functions of `(q, r)`;
* **`EOrthPaperInput`**: `lem:record:e-orthogonal`(c) verbatim, `EOrthPrime p (s^E_p)` at every
  prime `p ≡ 3 (mod 4)`, `p ≥ 2^20` (the paper states (c) for `p ≥ 19`; only the range of
  `lem:record:exact-marginal-e`, `p ≥ 2^20`, is assumed, which is weaker). *Hypothesis.*
* `sEpaper_le`: for `q ≤ Q ≤ 10⁻⁶`, `r ≤ R`, `r² = q`, `s^E(q, r) ≤ r·Gu(Q, R)` (the
  monotonicity of (i), with `√2 ≤ 1.4142135624` and the factor of `e_E` at most `1.4143`);
* **`kSE_ge_paper`**: the table value `s_E(X_i)` of `paperKappa` is at least `Gu(1/X_i, 1/⌊√X_i⌋)`
  at the 33 piece starts (exact rational check; this checks the `s_E` column of
  `cert:signed-local`'s table in Lean);
* **`esPrimeInput_of_paper`**: NB3's `EsPrimeInput paperKappa` from `EOrthPaperInput`.
-/

namespace Sarkozy.NormBoundsPaper3

open Finset
open scoped BigOperators

open Sarkozy.PartV
open Sarkozy.HsumProof (paperKappa kSE)

/-- The paper's `𝔰_p` (`lem:record:e-law`(d)), `Z = (1 − q)(1 − 2q)`. -/
noncomputable def frakS (q : ℝ) : ℝ :=
  q / (1 - q) * ((1 + Real.sqrt 2) / (1 - 9 * q) +
    7 * q / ((1 - q) * (1 - 2 * q) * (1 - 9 * q) * (1 - 2 * q)))

/-- The paper's `e_E` (`lem:record:e-orthogonal`(b)). -/
noncomputable def eEc (q r : ℝ) : ℝ :=
  q * r / Real.sqrt ((1 - q) * (1 - 3 * q)) * Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2)

/-- **The paper's `s^E_p`** (`lem:record:e-orthogonal`(c)). -/
noncomputable def sEpaper (q r : ℝ) : ℝ :=
  frakS q + 2 * eEc q r / (1 - 2 * q) + q ^ 2 / ((1 - q) * (1 - 2 * q)) +
    18 * q ^ 2 / ((1 - q) * (1 - 9 * q))

/-- **`lem:record:e-orthogonal`(c), verbatim** (in the form `EOrthPrime`): at every prime
`p ≡ 3 (mod 4)`, `p ≥ 2^20`, `‖Sym(K₁ − K^E_0)‖ ≤ s^E_p` on `L²(ν_E)`, `q = 1/p`,
`r = p^{-1/2}`. The paper states (c) for `p ≥ 19`; only `p ≥ 2^20` (the range of
`lem:record:exact-marginal-e`) is assumed. *Hypothesis.* -/
def EOrthPaperInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → 2 ^ 20 ≤ p →
    EOrthPrime p (sEpaper (1 / (p : ℝ)) (1 / Real.sqrt p))

/-- The rational upper bound of `√2`. -/
def s2u : ℚ := 14142135624 / 10 ^ 10

/-- The rational upper bound of the factor of `e_E`. -/
def tau_u : ℚ := 14143 / 10000

/-- The majorant `Gu(Q, R)` of `s^E/r`. -/
def GuQ (Q R : ℚ) : ℚ :=
  R * ((1 / (1 - Q)) * ((1 + s2u) / (1 - 9 * Q) +
      7 * Q / ((1 - Q) * (1 - 2 * Q) * (1 - 9 * Q) * (1 - 2 * Q)))) +
    2 * Q * tau_u / (1 - 2 * Q) + Q * R / ((1 - Q) * (1 - 2 * Q)) +
    18 * Q * R / ((1 - Q) * (1 - 9 * Q))

theorem sqrt2_le : Real.sqrt 2 ≤ (s2u : ℝ) := by
  rw [Real.sqrt_le_left (by unfold s2u; positivity)]
  unfold s2u; push_cast; norm_num

theorem tau_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 10 ^ 6) :
    Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) / Real.sqrt ((1 - q) * (1 - 3 * q)) ≤
      (tau_u : ℝ) := by
  have hB : 0 < (1 - q) * (1 - 3 * q) := by nlinarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have hA : 2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2 ≤ 2 + 1 / 10 ^ 10 := by
    have : 4 * q ^ 2 / (1 - 2 * q) ^ 2 ≤ 1 / 10 ^ 10 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hB)]
  have ht : (0 : ℝ) ≤ tau_u := by unfold tau_u; positivity
  calc Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) ≤ Real.sqrt ((tau_u : ℝ) ^ 2 *
        ((1 - q) * (1 - 3 * q))) := by
        refine Real.sqrt_le_sqrt (hA.trans ?_)
        unfold tau_u; push_cast; nlinarith
    _ = (tau_u : ℝ) * Real.sqrt ((1 - q) * (1 - 3 * q)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht]

/-- **The monotonicity of `lem:record:exact-marginal-e`(i)** in the form used: `s^E(q, r) ≤
r · Gu(Q, R)` for `0 < q ≤ Q ≤ 10⁻⁶`, `0 < r ≤ R`, `r² = q`. -/
theorem sEpaper_le {q r : ℝ} {Q R : ℚ} (hq0 : 0 < q) (hqQ : q ≤ Q) (hQ : (Q : ℝ) ≤ 1 / 10 ^ 6)
    (hr0 : 0 < r) (hrR : r ≤ R) (hrq : r * r = q) :
    sEpaper q r ≤ r * (GuQ Q R : ℝ) := by
  have hQ0 : (0 : ℝ) < Q := hq0.trans_le hqQ
  have hR0 : (0 : ℝ) < R := hr0.trans_le hrR
  have h1q : 0 < 1 - q := by linarith
  have h2q : 0 < 1 - 2 * q := by linarith
  have h3q : 0 < 1 - 3 * q := by linarith
  have h9q : 0 < 1 - 9 * q := by linarith
  have h1Q : (0 : ℝ) < 1 - Q := by linarith
  have h2Q : (0 : ℝ) < 1 - 2 * Q := by linarith
  have h9Q : (0 : ℝ) < 1 - 9 * Q := by linarith
  have hs2 := sqrt2_le
  have hs20 : (0 : ℝ) ≤ s2u := by unfold s2u; positivity
  -- the four terms
  have t1 : frakS q ≤ r * (R * ((1 / (1 - Q)) * ((1 + s2u) / (1 - 9 * Q) +
      7 * Q / ((1 - Q) * (1 - 2 * Q) * (1 - 9 * Q) * (1 - 2 * Q))))) := by
    have e : frakS q = r * (r * ((1 / (1 - q)) * ((1 + Real.sqrt 2) / (1 - 9 * q) +
        7 * q / ((1 - q) * (1 - 2 * q) * (1 - 9 * q) * (1 - 2 * q))))) := by
      unfold frakS; rw [← hrq]; field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left (mul_le_mul hrR ?_ (by positivity) hR0.le) hr0.le
    refine mul_le_mul (one_div_le_one_div_of_le h1Q (by linarith)) (add_le_add ?_ ?_)
      (by positivity) (by positivity)
    · exact div_le_div₀ (by positivity) (by linarith) h9Q (by linarith)
    · refine div_le_div₀ (by positivity) (by linarith) (by positivity) ?_
      have a1 : (1 - (Q : ℝ)) ≤ 1 - q := by linarith
      have a2 : (1 - 2 * (Q : ℝ)) ≤ 1 - 2 * q := by linarith
      have a9 : (1 - 9 * (Q : ℝ)) ≤ 1 - 9 * q := by linarith
      gcongr
  have t2 : 2 * eEc q r / (1 - 2 * q) ≤ r * (2 * Q * tau_u / (1 - 2 * Q)) := by
    have hτ := tau_le hq0.le (hqQ.trans hQ)
    have e : 2 * eEc q r / (1 - 2 * q) = r * (2 * q * (Real.sqrt (2 + 4 * q ^ 2 /
        (1 - 2 * q) ^ 2) / Real.sqrt ((1 - q) * (1 - 3 * q))) / (1 - 2 * q)) := by
      unfold eEc; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hr0.le
    have hτ0 : 0 ≤ Real.sqrt (2 + 4 * q ^ 2 / (1 - 2 * q) ^ 2) /
        Real.sqrt ((1 - q) * (1 - 3 * q)) := by positivity
    refine div_le_div₀ (by unfold tau_u; positivity) ?_ h2Q (by linarith)
    exact mul_le_mul (by linarith) hτ hτ0 (by positivity)
  have t3 : q ^ 2 / ((1 - q) * (1 - 2 * q)) ≤ r * (Q * R / ((1 - Q) * (1 - 2 * Q))) := by
    have e : q ^ 2 / ((1 - q) * (1 - 2 * q)) = r * (q * r / ((1 - q) * (1 - 2 * q))) := by
      rw [← hrq]; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hr0.le
    refine div_le_div₀ (by positivity) (mul_le_mul hqQ hrR hr0.le hQ0.le) (by positivity) ?_
    exact mul_le_mul (by linarith) (by linarith) h2Q.le h1q.le
  have t4 : 18 * q ^ 2 / ((1 - q) * (1 - 9 * q)) ≤ r * (18 * Q * R / ((1 - Q) * (1 - 9 * Q))) := by
    have e : 18 * q ^ 2 / ((1 - q) * (1 - 9 * q)) = r * (18 * q * r / ((1 - q) * (1 - 9 * q))) := by
      rw [← hrq]; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hr0.le
    refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
    · have := mul_le_mul hqQ hrR hr0.le hQ0.le
      nlinarith
    · exact mul_le_mul (by linarith) (by linarith) h9Q.le h1q.le
  unfold sEpaper
  have : r * (GuQ Q R : ℝ) = r * (R * ((1 / (1 - Q)) * ((1 + s2u) / (1 - 9 * Q) +
      7 * Q / ((1 - Q) * (1 - 2 * Q) * (1 - 9 * Q) * (1 - 2 * Q))))) +
      r * (2 * Q * tau_u / (1 - 2 * Q)) + r * (Q * R / ((1 - Q) * (1 - 2 * Q))) +
      r * (18 * Q * R / ((1 - Q) * (1 - 9 * Q))) := by
    unfold GuQ; push_cast; ring
  rw [this]
  linarith

/-- `⌊√X_i⌋` at the 33 piece starts. -/
def kTab : List ℕ := [4466, 4664, 4870, 5042, 5086, 5311, 5792, 6316, 6888, 7512, 8192, 8933,
  9741, 10623, 11585, 12633, 13777, 15024, 16384, 17866, 19483, 21247, 23170, 25267, 27554, 30048,
  32768, 46340, 65536, 131072, 262144, 1048576, 5931641]

/-- `k_i = ⌊√X_i⌋` (only `1 ≤ k_i`, `k_i² ≤ X_i` are used). -/
def kSq (i : Fin 33) : ℕ := kTab.getD i.val 1

theorem kSq_facts : ∀ i : Fin 33, 1 ≤ kSq i ∧ kSq i * kSq i ≤ pieceStart i := by
  decide +kernel

/-- **The `s_E` column of the table is above the paper's `s_E(X_i)`** (its majorant `Gu`). -/
theorem kSE_ge_paper : ∀ i : Fin 33,
    GuQ (1 / (pieceStart i : ℚ)) (1 / (kSq i : ℚ)) ≤ kSE i := by
  decide +kernel

/-- **NB3's `EsPrimeInput paperKappa` from `lem:record:e-orthogonal`(c).** -/
theorem esPrimeInput_of_paper (hEO : EOrthPaperInput) : EsPrimeInput paperKappa := by
  intro i p _ h3 hp
  have hX : (19951586 : ℕ) ≤ pieceStart i := pieceStart_ge_Q3 i
  have hp20 : 2 ^ 20 ≤ p := le_trans (by norm_num) (hX.trans hp)
  refine (hEO p h3 hp20).mono ?_
  obtain ⟨hk1, hk2⟩ := kSq_facts i
  have hXr : (19951586 : ℝ) ≤ pieceStart i := by exact_mod_cast hX
  have hpr : (pieceStart i : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hk1r : (1 : ℝ) ≤ kSq i := by exact_mod_cast hk1
  have hk2r : (kSq i : ℝ) * kSq i ≤ pieceStart i := by exact_mod_cast hk2
  -- `q = 1/p ≤ 1/X`, `r = p^{-1/2} ≤ 1/k`
  have hqQ : 1 / (p : ℝ) ≤ ((1 / (pieceStart i : ℚ) : ℚ) : ℝ) := by
    push_cast
    exact one_div_le_one_div_of_le (by linarith) hpr
  have hQ : ((1 / (pieceStart i : ℚ) : ℚ) : ℝ) ≤ 1 / 10 ^ 6 := by
    push_cast
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hrR : 1 / Real.sqrt p ≤ ((1 / (kSq i : ℚ) : ℚ) : ℝ) := by
    push_cast
    refine one_div_le_one_div_of_le (by linarith) ?_
    have hk0 : (0 : ℝ) ≤ kSq i := by linarith
    calc (kSq i : ℝ) = Real.sqrt ((kSq i : ℝ) * kSq i) := (Real.sqrt_mul_self hk0).symm
      _ ≤ Real.sqrt p := Real.sqrt_le_sqrt (hk2r.trans hpr)
  have hrq : 1 / Real.sqrt p * (1 / Real.sqrt p) = 1 / (p : ℝ) := by
    rw [one_div_mul_one_div, hss]
  have hle := sEpaper_le (one_div_pos.mpr hp0) hqQ hQ (one_div_pos.mpr hsp) hrR hrq
  have hG : ((GuQ (1 / (pieceStart i : ℚ)) (1 / (kSq i : ℚ)) : ℚ) : ℝ) ≤ (paperKappa i).sE := by
    change _ ≤ ((kSE i : ℚ) : ℝ)
    exact_mod_cast kSE_ge_paper i
  calc sEpaper (1 / (p : ℝ)) (1 / Real.sqrt p) ≤
        1 / Real.sqrt p * ((GuQ (1 / (pieceStart i : ℚ)) (1 / (kSq i : ℚ)) : ℚ) : ℝ) := hle
    _ ≤ 1 / Real.sqrt p * (paperKappa i).sE :=
        mul_le_mul_of_nonneg_left hG (one_div_pos.mpr hsp).le
    _ = (paperKappa i).sE * (1 / Real.sqrt p) := by ring

end Sarkozy.NormBoundsPaper3
