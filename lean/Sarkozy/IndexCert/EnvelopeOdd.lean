module

public import Sarkozy.IndexCert.EnvelopeBasics

@[expose] public section

/-!
# `lem:imp:padic-envelope` at an odd prime

`paper/sections/27_tail_index.tex`, `lem:imp:padic-envelope`, odd `p`: for `x` uniform among the
residues of `ℤ/p^{2m}ℤ` with `p^m ∤ x` and `T f(s) = E f(s + x²)`, on the exact-depth space
`ran Π_l` of the residue chain, `‖T f‖ ≤ δ_l ‖f‖` with the paper's tails
`δ_0 = 1`, `δ_l = (p^{-l/2} + e_p)/(1 - e_p)` (`1 ≤ l < 2m`), `δ_{2m} = 0`, `e_p = p^{-m}`
(V2-A's `PartVLaws.oddTail p m`): `odd_envelope`.

The paper evaluates the quadratic Gauss multipliers (`G_k = p^{-1} G_{k-2}`, `|G_1| = p^{-1/2}`).
The proof here uses no characters:
* for the unconditioned law (`x` uniform on `ℤ/p^hℤ`, `S f(s) = ∑_x f(s + x²)`),
  `∑_s (S f)(s)² = ∑_d ∑_t f(t) ∑_x f(t + d² + 2dx)` (`sq_sum_identity`); the inner sum is
  `p^h f(t)` when `p^l ∣ d` (periodicity) and `0` otherwise (`sum_mul_eq_zero`, since `2d` has
  valuation `< l`), so `‖S f‖² = p^h p^{h-l} ‖f‖²`, i.e. `|G_l|² = p^{-l}` (`odd_sq_sum`);
* the excluded roots (`p^m ∣ x`) have square `≡ 0 (mod p^l)`, so the conditioned transition is
  `(S f - p^{h-m} f)/|A|` (`odd_sqSum_split`), and Cauchy–Schwarz gives the tail;
* at the top `l = 2m`: averaging over `x ↦ x + p^m k` gives `∑_{x ∈ A} f(s + x²) = 0`
  (`odd_top_sum`), the paper's "at the even top conductor the multiplier is exactly zero".
-/

namespace Sarkozy.IndexCert

open Finset Sarkozy.IndexSupport
open scoped Matrix BigOperators

theorem dot_self_eq {ι : Type*} [Fintype ι] (v : ι → ℝ) : v ⬝ᵥ v = ∑ i, v i ^ 2 := by
  simp only [dotProduct, sq]

section Level0

variable {p h : ℕ} [NeZero (p ^ h)]

/-- **Depth `0`**: the transition of a probability law fixes the constants. -/
theorem conv_level_zero (μ : FiniteLaw (ZMod (p ^ h))) {f : ZMod (p ^ h) → ℝ}
    (hf : (Chain.residues p h).diff 0 *ᵥ f = f) : convMatrix μ.weight *ᵥ f = f := by
  have hper := periodic_of_cond (Nat.zero_le h) (cond_of_diff_ge (Nat.zero_le h) le_rfl
    (Nat.zero_le h) hf)
  funext s
  rw [convMatrix_mulVec]
  have : ∀ r, μ.weight r * f (s + r) = μ.weight r * f s := fun r => by
    rw [hper s r (by rw [pow_zero]; exact one_dvd _)]
  rw [sum_congr rfl fun r _ => this r, ← sum_mul, μ.total, one_mul]

end Level0

section Odd

variable {p h : ℕ} [NeZero (p ^ h)]

theorem coprime_two_pow (hp : p.Prime) (hp2 : p ≠ 2) (l : ℕ) : Nat.Coprime (p ^ l) 2 :=
  Nat.Coprime.pow_left l ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

theorem not_dvd_two_mul (hp : p.Prime) (hp2 : p ≠ 2) {l : ℕ} (hl : l ≤ h) {d : ZMod (p ^ h)}
    (hd : ¬ p ^ l ∣ d.val) : ¬ p ^ l ∣ (2 * d).val := by
  intro h2
  apply hd
  rw [two_mul, dvd_val_add_iff hl, ← two_mul] at h2
  exact Nat.Coprime.dvd_of_dvd_mul_left (coprime_two_pow hp hp2 l) h2

/-- **`|G_l|² = p^{-l}`, character-free**: on `ran Π_l` (`1 ≤ l ≤ h`, `p` odd),
`∑_s (∑_x f(s + x²))² = p^h p^{h-l} ∑_s f(s)²`. -/
theorem odd_sq_sum (hp : p.Prime) (hp2 : p ≠ 2) {l : ℕ} (hl : l ≤ h)
    {f : ZMod (p ^ h) → ℝ} (hf : (Chain.residues p h).diff l *ᵥ f = f) :
    ∑ s, (∑ x, f (s + x ^ 2)) ^ 2 = (p : ℝ) ^ h * (p : ℝ) ^ (h - l) * ∑ t, f t ^ 2 := by
  rw [sq_sum_identity]
  have hper := periodic_of_cond hl (cond_of_diff_ge hl le_rfl hl hf)
  have hzero : ∀ j < l, (Chain.residues p h).cond j *ᵥ f = 0 :=
    fun j hj => cond_of_diff_lt hl hj hf
  have hK : ∀ d t, f t * ∑ x, f (t + d ^ 2 + 2 * d * x) =
      if p ^ l ∣ d.val then (p : ℝ) ^ h * f t ^ 2 else 0 := by
    intro d t
    split_ifs with hd
    · have : ∀ x, f (t + d ^ 2 + 2 * d * x) = f t := by
        intro x
        rw [show t + d ^ 2 + 2 * d * x = t + d * (d + 2 * x) by ring]
        exact hper t _ (dvd_val_mul hl hd _)
      rw [sum_congr rfl fun x _ => this x, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      push_cast
      ring
    · rw [sum_mul_eq_zero hp hl hzero (not_dvd_two_mul hp hp2 hl hd) (t + d ^ 2), mul_zero]
  simp only [hK]
  have hd : ∀ d : ZMod (p ^ h), (∑ t, if p ^ l ∣ d.val then (p : ℝ) ^ h * f t ^ 2 else 0) =
      if p ^ l ∣ d.val then (p : ℝ) ^ h * ∑ t, f t ^ 2 else 0 := by
    intro d
    split_ifs
    · rw [mul_sum]
    · rw [sum_const_zero]
  simp only [hd]
  rw [← sum_filter, sum_const, card_dvd_val hp.pos hl, nsmul_eq_mul]
  push_cast
  ring

omit [NeZero (p ^ h)] in
/-- `x ∉ A` (`p^m ∣ x`) has `p^l ∣ x²` for `l ≤ h ≤ 2m`. -/
theorem dvd_val_sq_of_dvd {m l : ℕ} (hl : l ≤ h) (hlm : l ≤ 2 * m) {x : ZMod (p ^ h)}
    (hx : p ^ m ∣ x.val) : p ^ l ∣ (x ^ 2).val := by
  rw [sq, ZMod.val_mul, Nat.dvd_mod_iff (Nat.pow_dvd_pow p hl)]
  have : p ^ (2 * m) ∣ x.val * x.val := by
    rw [two_mul, pow_add]
    exact Nat.mul_dvd_mul hx hx
  exact (Nat.pow_dvd_pow p hlm).trans this

/-- **The excluded roots** (`p^m ∣ x`, square `≡ 0 (mod p^l)`): for `l ≤ min(h, 2m)` on `ran Π_l`,
`∑_{x ∈ A} f(s + x²) = ∑_x f(s + x²) - p^{h-m} f(s)`, `A = lowValuation p h m`. -/
theorem sqSum_split (hp : 0 < p) {m l : ℕ} (hm : m ≤ h) (hl : l ≤ h) (hlm : l ≤ 2 * m)
    {f : ZMod (p ^ h) → ℝ} (hf : (Chain.residues p h).diff l *ᵥ f = f) (s : ZMod (p ^ h)) :
    ∑ x ∈ PartV.lowValuation p h m, f (s + x ^ 2) =
      ∑ x, f (s + x ^ 2) - (p : ℝ) ^ (h - m) * f s := by
  have hper := periodic_of_cond hl (cond_of_diff_ge hl le_rfl hl hf)
  have hsplit := sum_filter_add_sum_filter_not univ (fun x : ZMod (p ^ h) => ¬ p ^ m ∣ x.val)
    (fun x => f (s + x ^ 2))
  have hc : ∑ x ∈ univ.filter (fun x : ZMod (p ^ h) => ¬ ¬ p ^ m ∣ x.val), f (s + x ^ 2) =
      (p : ℝ) ^ (h - m) * f s := by
    simp only [not_not]
    have : ∀ x ∈ univ.filter (fun x : ZMod (p ^ h) => p ^ m ∣ x.val), f (s + x ^ 2) = f s := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      exact hper s _ (dvd_val_sq_of_dvd hl hlm hx)
    rw [sum_congr rfl this, sum_const, card_dvd_val hp hm, nsmul_eq_mul]
    push_cast
    ring
  unfold PartV.lowValuation
  linarith

omit [NeZero (p ^ h)] in
/-- `p^m < p^h` for `m < h`, so `(p^m : ℤ/p^hℤ).val = p^m`. -/
theorem val_natCast_pow (hp : 1 < p) {m : ℕ} (hmh : m < h) :
    (((p ^ m : ℕ) : ZMod (p ^ h))).val = p ^ m := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp hmh)]

/-- **The top level at an odd prime** (`h = 2m`): on `ran Π_{2m}`,
`∑_{x ∈ A} f(s + x²) = 0` — the multiplier at the even top conductor is exactly zero. -/
theorem odd_top_sum (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m) (hh : h = 2 * m)
    {f : ZMod (p ^ h) → ℝ} (hf : (Chain.residues p h).diff h *ᵥ f = f) (s : ZMod (p ^ h)) :
    ∑ x ∈ PartV.lowValuation p h m, f (s + x ^ 2) = 0 := by
  set A := PartV.lowValuation p h m with hA
  set P : ZMod (p ^ h) := ((p ^ m : ℕ) : ZMod (p ^ h)) with hP
  have hmh : m < h := by omega
  have hzero : ∀ j < h, (Chain.residues p h).cond j *ᵥ f = 0 :=
    fun j hj => cond_of_diff_lt le_rfl hj hf
  have hPval : P.val = p ^ m := val_natCast_pow hp.one_lt hmh
  have hP2 : P ^ 2 = 0 := by
    rw [hP, ← Nat.cast_pow, ← pow_mul, show m * 2 = h by omega, ZMod.natCast_self]
  have hPk : ∀ k, p ^ m ∣ (P * k).val := fun k => dvd_val_mul hmh.le (by rw [hPval]) k
  have hmemA : ∀ x, x ∈ A ↔ ¬ p ^ m ∣ x.val := by
    intro x
    simp only [hA, PartV.lowValuation, mem_filter, mem_univ, true_and]
  have hshiftA : ∀ k x, x ∈ A → x + P * k ∈ A := by
    intro k x hx
    rw [hmemA] at hx ⊢
    rwa [dvd_val_add_iff hmh.le, Nat.dvd_add_left (hPk k)]
  have hshiftA' : ∀ k x, x ∈ A → x - P * k ∈ A := by
    intro k x hx
    rw [hmemA] at hx ⊢
    intro h1
    apply hx
    have := (dvd_val_add_iff hmh.le (x - P * k) (P * k)).mpr (Nat.dvd_add h1 (hPk k))
    rwa [sub_add_cancel] at this
  -- each translate gives the same sum
  have htrans : ∀ k, ∑ x ∈ A, f (s + x ^ 2) = ∑ x ∈ A, f (s + (x + P * k) ^ 2) := by
    intro k
    exact (Finset.sum_nbij' (· + P * k) (· - P * k) (fun x hx => hshiftA k x hx)
      (fun x hx => hshiftA' k x hx) (fun x _ => by simp) (fun x _ => by simp)
      (fun x _ => rfl)).symm
  -- the inner sums vanish
  have hinner : ∀ x ∈ A, ∑ k, f (s + (x + P * k) ^ 2) = 0 := by
    intro x hx
    have hsq : ∀ k, s + (x + P * k) ^ 2 = s + x ^ 2 + (P * (2 * x)) * k := by
      intro k
      have : (x + P * k) ^ 2 = x ^ 2 + (P * (2 * x)) * k + P ^ 2 * k ^ 2 := by ring
      rw [this, hP2, zero_mul, add_zero, add_assoc]
    simp only [hsq]
    apply sum_mul_eq_zero hp le_rfl hzero
    intro hdvd
    rw [hmemA] at hx
    apply hx
    rw [ZMod.val_mul, hPval, Nat.dvd_mod_iff dvd_rfl] at hdvd
    have hdvd' : p ^ m * p ^ m ∣ p ^ m * (2 * x).val := by
      rw [← pow_add, show m + m = h by omega]
      exact hdvd
    have h2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos m) hdvd'
    rw [two_mul, dvd_val_add_iff hmh.le, ← two_mul] at h2
    exact Nat.Coprime.dvd_of_dvd_mul_left (coprime_two_pow hp hp2 m) h2
  have htot : (p : ℝ) ^ h * ∑ x ∈ A, f (s + x ^ 2) = 0 := by
    have : ∑ _k : ZMod (p ^ h), ∑ x ∈ A, f (s + x ^ 2) = 0 := by
      rw [sum_congr rfl fun k _ => htrans k, sum_comm]
      exact sum_eq_zero hinner
    rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul] at this
    exact_mod_cast this
  have hpos : (0 : ℝ) < (p : ℝ) ^ h := pow_pos (by exact_mod_cast hp.pos) h
  rcases mul_eq_zero.mp htot with h0 | h0
  · exact absurd h0 hpos.ne'
  · exact h0

/-- `(p^{-l/2})² = p^{-l}`. -/
theorem rpow_neg_half_sq {x : ℝ} (hx : 0 < x) (l : ℕ) :
    (x ^ (-(l : ℝ) / 2)) ^ 2 = (x ^ l)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, show -(l : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(l : ℝ) by
    push_cast; ring, Real.rpow_neg hx.le, Real.rpow_natCast]

/-- **`lem:imp:padic-envelope` at an odd prime** (`h = 2m`, `m ≥ 1`): on the exact-depth
space `ran Π_l` the transition of the square-increment law (V1's `squareIncrementLaw p h m`) is
bounded by the paper's tail `δ_l = PartVLaws.oddTail p m l`. -/
theorem odd_envelope (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m) (hh : h = 2 * m)
    (hne : (PartV.lowValuation p h m).Nonempty) {l : ℕ} (hl : l ≤ h)
    {f : ZMod (p ^ h) → ℝ} (hf : (Chain.residues p h).diff l *ᵥ f = f) :
    (convMatrix (PartV.squareIncrementLaw p h m hne).weight *ᵥ f) ⬝ᵥ
      (convMatrix (PartV.squareIncrementLaw p h m hne).weight *ᵥ f) ≤
      PartVLaws.oddTail p m l ^ 2 * (f ⬝ᵥ f) := by
  set μ := PartV.squareIncrementLaw p h m hne
  set A := PartV.lowValuation p h m
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hmh : m ≤ h := by omega
  -- the transition
  have hT : ∀ s, (convMatrix μ.weight *ᵥ f) s = (A.card : ℝ)⁻¹ * ∑ x ∈ A, f (s + x ^ 2) :=
    fun s => conv_squareIncrement_mulVec hne f s
  -- `|A| = p^h - p^{h-m}`
  have hcardA : (A.card : ℝ) = (p : ℝ) ^ h - (p : ℝ) ^ (h - m) := by
    have h1 := card_dvd_val (h := h) hp.pos hmh
    have h2 := card_filter_add_card_filter_not (s := univ)
      (fun x : ZMod (p ^ h) => ¬ p ^ m ∣ x.val)
    simp only [not_not, h1, card_univ, ZMod.card] at h2
    have h3 : A.card + p ^ (h - m) = p ^ h := h2
    have h4 : ((A.card + p ^ (h - m) : ℕ) : ℝ) = ((p ^ h : ℕ) : ℝ) := by rw [h3]
    push_cast at h4
    linarith
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · -- depth `0`
    rw [conv_level_zero μ hf]
    simp only [PartVLaws.oddTail, ↓reduceIte, one_pow, one_mul, le_refl]
  by_cases htop : l = h
  · -- the top level
    subst htop
    have h0 : convMatrix μ.weight *ᵥ f = 0 := by
      funext s
      rw [hT, odd_top_sum hp hp2 hm hh hf s, mul_zero, Pi.zero_apply]
    rw [h0]
    simp only [PartVLaws.oddTail, show l ≠ 0 by omega, ↓reduceIte, show ¬ l < 2 * m by omega,
      zero_dotProduct, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      le_refl]
  · -- `1 ≤ l < 2m`
    have hlt : l < 2 * m := by omega
    set e := PartVLaws.topErr p m with he
    have he_eq : e = ((p : ℝ) ^ m)⁻¹ := rfl
    set r := (p : ℝ) ^ (-(l : ℝ) / 2) with hr
    have hr0 : 0 ≤ r := Real.rpow_nonneg hp0.le _
    have hr2 : r ^ 2 = ((p : ℝ) ^ l)⁻¹ := rpow_neg_half_sq hp0 l
    set n : ℝ := (p : ℝ) ^ h with hn
    have hn0 : 0 < n := pow_pos hp0 h
    set c : ℝ := (p : ℝ) ^ (h - m) with hc
    have hc0 : 0 ≤ c := (pow_pos hp0 _).le
    -- `‖S f‖ ≤ (n r) ‖f‖`
    have hS : ∑ s, (∑ x, f (s + x ^ 2)) ^ 2 ≤ (n * r) ^ 2 * ∑ t, f t ^ 2 := by
      rw [odd_sq_sum hp hp2 hl hf, mul_pow, hr2]
      have : (p : ℝ) ^ h * (p : ℝ) ^ (h - l) = n ^ 2 * ((p : ℝ) ^ l)⁻¹ := by
        rw [hn, sq, mul_assoc, ← pow_sub₀ _ hp0.ne' hl]
      rw [this]
    have hSA := sum_sub_sq_le (fun s => ∑ x, f (s + x ^ 2)) f
      (mul_nonneg hn0.le hr0) hc0 hS
    have hsplit : ∀ s, ∑ x ∈ A, f (s + x ^ 2) = ∑ x, f (s + x ^ 2) - c * f s :=
      fun s => sqSum_split hp.pos hmh hl (by omega) hf s
    -- assemble
    have hA0 : (0 : ℝ) < A.card := by
      exact_mod_cast card_pos.mpr hne
    have hcn : c = n * e := by
      rw [hc, hn, he_eq, ← pow_sub₀ _ hp0.ne' hmh]
    have htail : PartVLaws.oddTail p m l = (r + e) / (1 - e) := by
      simp only [PartVLaws.oddTail, show l ≠ 0 by omega, ↓reduceIte, hlt]
      rfl
    have he1 : e < 1 := by
      rw [he_eq]
      exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega))
    have hcardA' : (A.card : ℝ) = n * (1 - e) := by rw [hcardA, hcn]; ring
    rw [dot_self_eq, dot_self_eq, htail]
    simp only [hT, mul_pow, ← mul_sum, hsplit]
    rw [hcardA', inv_pow, div_pow]
    have hden : 0 < n * (1 - e) := mul_pos hn0 (by linarith)
    have key : ((n * (1 - e)) ^ 2)⁻¹ * ∑ s, (∑ x, f (s + x ^ 2) - c * f s) ^ 2 ≤
        ((n * (1 - e)) ^ 2)⁻¹ * ((n * r + c) ^ 2 * ∑ t, f t ^ 2) :=
      mul_le_mul_of_nonneg_left hSA (inv_nonneg.mpr (sq_nonneg _))
    refine key.trans (le_of_eq ?_)
    rw [hcn]
    field_simp

end Odd

end Sarkozy.IndexCert
