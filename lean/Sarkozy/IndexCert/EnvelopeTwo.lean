module

public import Sarkozy.IndexCert.EnvelopeOdd

@[expose] public section

/-!
# `lem:imp:padic-envelope` at `p = 2`

`paper/sections/27_tail_index.tex`, `lem:imp:padic-envelope`, `p = 2`: for `x` uniform among the
residues of `ℤ/2^{2m+1}ℤ` with `2^m ∤ x` and `T f(s) = E f(s + x²)`, on the exact-depth space
`ran Π_l`, `‖T f‖ ≤ δ_l ‖f‖` with the paper's 2-adic tails (V2-A's `PartVLaws.twoTail m`):
`δ_0 = 1`, `δ_1 = δ_2 = (2^{-1/2} + e)/(1 - e)`, `δ_l = (2^{-(l-1)/2} + e)/(1 - e)`
(`3 ≤ l ≤ 2m`), `δ_{2m+1} = e/(1 - e)`, `e = 2^{-m}`: `two_envelope`.

As at odd primes (`EnvelopeOdd.lean`) the proof is character-free:
* depth `1`: `x² ≡ x (mod 2)`, so `∑_x f(s + x²) = ∑_x f(s + x) = 0` (the paper's `G_1 = 0`);
* `2 ≤ l ≤ 2m`: `∑_s (∑_x f(s + x²))² = 2^h 2^{h-(l-1)} ∑ f²` (`two_sq_sum`), the paper's
  `|G_l| = 2^{-(l-1)/2}`; the excluded roots have square `≡ 0 (mod 2^{2m})`;
* the top `l = 2m + 1`: the roots of valuation `≤ m - 2` cancel under `x ↦ x + 2^{m+1}k`, and the
  roots of valuation exactly `m - 1` all have square `2^{2m-2}` (odd squares are `1 mod 8`), so
  `T f(s) = (e/(1 - e)) f(s + 2^{2m-2})` (`two_top_sum`); the paper's "their top phases cancel in
  equal numbers" is the count `#{x : v(x) = m - 1} = 2^{m+1}` used here.
-/

namespace Sarkozy.IndexCert

open Finset Sarkozy.IndexSupport
open scoped Matrix BigOperators

section Assembly

variable {p h : ℕ} [NeZero (p ^ h)]

/-- `|A| = p^h - p^{h-m}` for `A = lowValuation p h m`. -/
theorem card_lowValuation (hp : 0 < p) {m : ℕ} (hmh : m ≤ h) :
    ((PartV.lowValuation p h m).card : ℝ) = (p : ℝ) ^ h - (p : ℝ) ^ (h - m) := by
  have h1 := card_dvd_val (h := h) hp hmh
  have h2 := card_filter_add_card_filter_not (s := univ)
    (fun x : ZMod (p ^ h) => ¬ p ^ m ∣ x.val)
  simp only [not_not, h1, card_univ, ZMod.card] at h2
  have h3 : (PartV.lowValuation p h m).card + p ^ (h - m) = p ^ h := h2
  have h4 : (((PartV.lowValuation p h m).card + p ^ (h - m) : ℕ) : ℝ) = ((p ^ h : ℕ) : ℝ) := by
    rw [h3]
  push_cast at h4
  linarith

/-- **Assembly**: from `‖S f‖ ≤ p^h r ‖f‖` for the unconditioned sum `S f(s) = ∑_x f(s + x²)`
and the excluded-root identity, the conditioned transition is bounded by `(r + e)/(1 - e)`,
`e = p^{-m}`. -/
theorem assemble (hp : 1 < p) {m : ℕ} (hm : 1 ≤ m) (hmh : m ≤ h)
    (hne : (PartV.lowValuation p h m).Nonempty) {f : ZMod (p ^ h) → ℝ} {r : ℝ} (hr0 : 0 ≤ r)
    (hS : ∑ s, (∑ x, f (s + x ^ 2)) ^ 2 ≤ ((p : ℝ) ^ h * r) ^ 2 * ∑ t, f t ^ 2)
    (hsplit : ∀ s, ∑ x ∈ PartV.lowValuation p h m, f (s + x ^ 2) =
      ∑ x, f (s + x ^ 2) - (p : ℝ) ^ (h - m) * f s) :
    (convMatrix (PartV.squareIncrementLaw p h m hne).weight *ᵥ f) ⬝ᵥ
      (convMatrix (PartV.squareIncrementLaw p h m hne).weight *ᵥ f) ≤
      ((r + PartVLaws.topErr p m) / (1 - PartVLaws.topErr p m)) ^ 2 * (f ⬝ᵥ f) := by
  have hcardA0 := card_lowValuation (h := h) (m := m) (by omega : 0 < p) hmh
  have hT : ∀ s, (convMatrix (PartV.squareIncrementLaw p h m hne).weight *ᵥ f) s =
      ((PartV.lowValuation p h m).card : ℝ)⁻¹ *
        ∑ x ∈ PartV.lowValuation p h m, f (s + x ^ 2) :=
    fun s => conv_squareIncrement_mulVec hne f s
  set A := PartV.lowValuation p h m
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  set e := PartVLaws.topErr p m with he
  have he_eq : e = ((p : ℝ) ^ m)⁻¹ := rfl
  set n : ℝ := (p : ℝ) ^ h with hn
  have hn0 : 0 < n := pow_pos hp0 h
  set c : ℝ := (p : ℝ) ^ (h - m) with hc
  have hc0 : 0 ≤ c := (pow_pos hp0 _).le
  have hcn : c = n * e := by rw [hc, hn, he_eq, ← pow_sub₀ _ hp0.ne' hmh]
  have he1 : e < 1 := by
    rw [he_eq]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by exact_mod_cast hp) (by omega))
  have hcardA : (A.card : ℝ) = n * (1 - e) := by rw [hcardA0, hcn]; ring
  have hSA := sum_sub_sq_le (fun s => ∑ x, f (s + x ^ 2)) f (mul_nonneg hn0.le hr0) hc0 hS
  rw [dot_self_eq, dot_self_eq]
  simp only [hT, mul_pow, ← mul_sum, hsplit]
  rw [hcardA, inv_pow, div_pow]
  have key : ((n * (1 - e)) ^ 2)⁻¹ * ∑ s, (∑ x, f (s + x ^ 2) - c * f s) ^ 2 ≤
      ((n * (1 - e)) ^ 2)⁻¹ * ((n * r + c) ^ 2 * ∑ t, f t ^ 2) :=
    mul_le_mul_of_nonneg_left hSA (inv_nonneg.mpr (sq_nonneg _))
  refine key.trans (le_of_eq ?_)
  have h1e : 0 < 1 - e := by linarith
  rw [hcn]
  field_simp

end Assembly

section Two

variable {h : ℕ} [NeZero (2 ^ h)]

omit [NeZero (2 ^ h)] in
theorem two_dvd_val_add_iff (hh : 1 ≤ h) (a b : ZMod (2 ^ h)) :
    2 ∣ (a + b).val ↔ 2 ∣ a.val + b.val := by
  have := dvd_val_add_iff (p := 2) (j := 1) hh a b
  rwa [pow_one] at this

omit [NeZero (2 ^ h)] in
theorem two_dvd_val_two_mul (hh : 1 ≤ h) (x : ZMod (2 ^ h)) : 2 ∣ (2 * x).val := by
  rw [two_mul, two_dvd_val_add_iff hh]
  exact ⟨x.val, by ring⟩

/-- **`|G_l|² = 2^{-(l-1)}`, character-free**: on `ran Π_l` (`2 ≤ l ≤ h`),
`∑_s (∑_x f(s + x²))² = 2^h 2^{h-(l-1)} ∑_s f(s)²`. -/
theorem two_sq_sum {l : ℕ} (hl2 : 2 ≤ l) (hl : l ≤ h) {f : ZMod (2 ^ h) → ℝ}
    (hf : (Chain.residues 2 h).diff l *ᵥ f = f) :
    ∑ s, (∑ x, f (s + x ^ 2)) ^ 2 = (2 : ℝ) ^ h * (2 : ℝ) ^ (h - (l - 1)) * ∑ t, f t ^ 2 := by
  rw [sq_sum_identity]
  have hper := periodic_of_cond hl (cond_of_diff_ge hl le_rfl hl hf)
  have hzero : ∀ j < l, (Chain.residues 2 h).cond j *ᵥ f = 0 :=
    fun j hj => cond_of_diff_lt hl hj hf
  have hh1 : 1 ≤ h := by omega
  have hpow : (2 : ℕ) ^ l = 2 ^ (l - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hK : ∀ d t, f t * ∑ x, f (t + d ^ 2 + 2 * d * x) =
      if 2 ^ (l - 1) ∣ d.val then (2 : ℝ) ^ h * f t ^ 2 else 0 := by
    intro d t
    split_ifs with hd
    · have h2d : 2 ∣ d.val := (dvd_pow_self 2 (by omega : l - 1 ≠ 0)).trans hd
      have : ∀ x, f (t + d ^ 2 + 2 * d * x) = f t := by
        intro x
        rw [show t + d ^ 2 + 2 * d * x = t + d * (d + 2 * x) by ring]
        apply hper
        rw [ZMod.val_mul, Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 hl), hpow]
        apply Nat.mul_dvd_mul hd
        rw [two_dvd_val_add_iff hh1]
        exact Nat.dvd_add h2d (two_dvd_val_two_mul hh1 x)
      rw [sum_congr rfl fun x _ => this x, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      push_cast
      ring
    · rw [sum_mul_eq_zero Nat.prime_two hl hzero ?_ (t + d ^ 2), mul_zero]
      intro h2
      apply hd
      rw [two_mul, dvd_val_add_iff hl, ← two_mul] at h2
      have h3 : 2 * 2 ^ (l - 1) ∣ 2 * d.val := by
        rw [← pow_succ', show l - 1 + 1 = l by omega]
        exact h2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  simp only [hK]
  have hd : ∀ d : ZMod (2 ^ h), (∑ t, if 2 ^ (l - 1) ∣ d.val then (2 : ℝ) ^ h * f t ^ 2 else 0) =
      if 2 ^ (l - 1) ∣ d.val then (2 : ℝ) ^ h * ∑ t, f t ^ 2 else 0 := by
    intro d
    split_ifs
    · rw [mul_sum]
    · rw [sum_const_zero]
  simp only [hd]
  rw [← sum_filter, sum_const, card_dvd_val (by norm_num) (by omega : l - 1 ≤ h), nsmul_eq_mul]
  push_cast
  ring

/-- **Depth `1` at `2`** (the paper's `G_1 = 0`): on `ran Π_1`, `∑_x f(s + x²) = 0`. -/
theorem two_sum_level_one (hh : 1 ≤ h) {f : ZMod (2 ^ h) → ℝ}
    (hf : (Chain.residues 2 h).diff 1 *ᵥ f = f) (s : ZMod (2 ^ h)) :
    ∑ x, f (s + x ^ 2) = 0 := by
  have hper := periodic_of_cond hh (cond_of_diff_ge hh le_rfl hh hf)
  have hzero : ∀ j < 1, (Chain.residues 2 h).cond j *ᵥ f = 0 :=
    fun j hj => cond_of_diff_lt hh hj hf
  have h1lt : 1 < 2 ^ h := Nat.one_lt_two_pow (by omega)
  have hval1 : (1 : ZMod (2 ^ h)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1lt]
  have hx : ∀ x : ZMod (2 ^ h), f (s + x ^ 2) = f (s + 1 * x) := by
    intro x
    rw [show s + x ^ 2 = (s + 1 * x) + x * (x - 1) by ring]
    apply hper
    rw [pow_one, ZMod.val_mul, Nat.dvd_mod_iff (dvd_pow_self 2 (by omega))]
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · have h1 : (1 : ZMod (2 ^ h)).val ≤ x.val := by
        rw [hval1]
        exact ZMod.val_pos.mpr hx0
      rw [ZMod.val_sub h1, hval1]
      exact (Nat.even_mul_pred_self x.val).two_dvd
  rw [sum_congr rfl fun x _ => hx x]
  exact sum_mul_eq_zero Nat.prime_two hh hzero (by rw [hval1, pow_one]; norm_num) s

/-- **The top level at `2`** (`h = 2m + 1`, `m ≥ 2`): on `ran Π_h`,
`∑_{x ∈ A} f(s + x²) = 2^{h-m} f(s + 2^{2m-2})`. -/
theorem two_top_sum {m : ℕ} (hm : 2 ≤ m) (hh : h = 2 * m + 1) {f : ZMod (2 ^ h) → ℝ}
    (hf : (Chain.residues 2 h).diff h *ᵥ f = f) (s : ZMod (2 ^ h)) :
    ∑ x ∈ PartV.lowValuation 2 h m, f (s + x ^ 2) =
      (2 : ℝ) ^ (h - m) * f (s + ((2 ^ (2 * m - 2) : ℕ) : ZMod (2 ^ h))) := by
  set A := PartV.lowValuation 2 h m with hA
  set Q : ZMod (2 ^ h) := ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ h)) with hQ
  have hmh : m + 1 < h := by omega
  have hzero : ∀ j < h, (Chain.residues 2 h).cond j *ᵥ f = 0 :=
    fun j hj => cond_of_diff_lt le_rfl hj hf
  have hQval : Q.val = 2 ^ (m + 1) := val_natCast_pow (by norm_num) hmh
  have hQ2 : Q ^ 2 = 0 := by
    rw [hQ, ← Nat.cast_pow, ← pow_mul, show (m + 1) * 2 = h + 1 by omega, pow_succ,
      Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hQk : ∀ j ≤ m + 1, ∀ k, 2 ^ j ∣ (Q * k).val := fun j hj k =>
    dvd_val_mul (by omega) (by rw [hQval]; exact Nat.pow_dvd_pow 2 hj) k
  have hmemA : ∀ x, x ∈ A ↔ ¬ 2 ^ m ∣ x.val := by
    intro x
    simp only [hA, PartV.lowValuation, mem_filter, mem_univ, true_and]
  have hsplit := sum_filter_add_sum_filter_not A (fun x : ZMod (2 ^ h) => ¬ 2 ^ (m - 1) ∣ x.val)
    (fun x => f (s + x ^ 2))
  set B₁ := A.filter (fun x : ZMod (2 ^ h) => ¬ 2 ^ (m - 1) ∣ x.val) with hB₁
  set B₂ := A.filter (fun x : ZMod (2 ^ h) => ¬ ¬ 2 ^ (m - 1) ∣ x.val) with hB₂
  have hmem₁ : ∀ x, x ∈ B₁ ↔ ¬ 2 ^ m ∣ x.val ∧ ¬ 2 ^ (m - 1) ∣ x.val := by
    intro x
    rw [hB₁, mem_filter, hmemA]
  -- the roots of valuation `≤ m - 2` cancel
  have hshift : ∀ k, ∀ x ∈ B₁, x + Q * k ∈ B₁ := by
    intro k x hx
    rw [hmem₁] at hx ⊢
    rw [dvd_val_add_iff (by omega), Nat.dvd_add_left (hQk m (by omega) k),
      dvd_val_add_iff (by omega), Nat.dvd_add_left (hQk (m - 1) (by omega) k)]
    exact hx
  have hshift' : ∀ k, ∀ x ∈ B₁, x - Q * k ∈ B₁ := by
    intro k x hx
    rw [hmem₁] at hx ⊢
    constructor
    · intro h1
      apply hx.1
      have := (dvd_val_add_iff (by omega) (x - Q * k) (Q * k)).mpr
        (Nat.dvd_add h1 (hQk m (by omega) k))
      rwa [sub_add_cancel] at this
    · intro h1
      apply hx.2
      have := (dvd_val_add_iff (by omega) (x - Q * k) (Q * k)).mpr
        (Nat.dvd_add h1 (hQk (m - 1) (by omega) k))
      rwa [sub_add_cancel] at this
  have htrans : ∀ k, ∑ x ∈ B₁, f (s + x ^ 2) = ∑ x ∈ B₁, f (s + (x + Q * k) ^ 2) := by
    intro k
    exact (Finset.sum_nbij' (· + Q * k) (· - Q * k) (fun x hx => hshift k x hx)
      (fun x hx => hshift' k x hx) (fun x _ => by simp) (fun x _ => by simp)
      (fun x _ => rfl)).symm
  have hinner : ∀ x ∈ B₁, ∑ k, f (s + (x + Q * k) ^ 2) = 0 := by
    intro x hx
    have hsq : ∀ k, s + (x + Q * k) ^ 2 = s + x ^ 2 + (Q * (2 * x)) * k := by
      intro k
      have : (x + Q * k) ^ 2 = x ^ 2 + (Q * (2 * x)) * k + Q ^ 2 * k ^ 2 := by ring
      rw [this, hQ2, zero_mul, add_zero, add_assoc]
    simp only [hsq]
    apply sum_mul_eq_zero Nat.prime_two le_rfl hzero
    intro hdvd
    rw [hmem₁] at hx
    apply hx.2
    rw [ZMod.val_mul, hQval, Nat.dvd_mod_iff dvd_rfl] at hdvd
    have hdvd' : 2 ^ (m + 1) * 2 ^ m ∣ 2 ^ (m + 1) * (2 * x).val := by
      rw [← pow_add, show m + 1 + m = h by omega]
      exact hdvd
    have h2 := Nat.dvd_of_mul_dvd_mul_left (by positivity) hdvd'
    rw [two_mul, dvd_val_add_iff (by omega), ← two_mul] at h2
    have h3 : 2 * 2 ^ (m - 1) ∣ 2 * x.val := by
      rw [← pow_succ', show m - 1 + 1 = m by omega]
      exact h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  have hB₁zero : ∑ x ∈ B₁, f (s + x ^ 2) = 0 := by
    have : ∑ _k : ZMod (2 ^ h), ∑ x ∈ B₁, f (s + x ^ 2) = 0 := by
      rw [sum_congr rfl fun k _ => htrans k, sum_comm]
      exact sum_eq_zero hinner
    rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul] at this
    have hpos : (0 : ℝ) < ((2 ^ h : ℕ) : ℝ) := by positivity
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hpos.ne'
    · exact h0
  -- the roots of valuation exactly `m - 1` have square `2^{2m-2}`
  have hsq2 : ∀ x ∈ B₂, x ^ 2 = ((2 ^ (2 * m - 2) : ℕ) : ZMod (2 ^ h)) := by
    intro x hx
    rw [hB₂, mem_filter, hmemA, not_not] at hx
    obtain ⟨hx1, ⟨o, ho⟩⟩ := hx
    have ho2 : o % 2 = 1 := by
      by_contra hc
      apply hx1
      obtain ⟨o', ho'⟩ : 2 ∣ o := Nat.dvd_of_mod_eq_zero (by omega)
      refine ⟨o', ?_⟩
      rw [ho, ho', show 2 ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega]
      ring
    have h8 := Sarkozy.PaperData.odd_mul_self_mod_eight ho2
    apply ZMod.val_injective
    rw [sq, ZMod.val_mul, ho, ZMod.val_natCast]
    have hprod : 2 ^ (m - 1) * o * (2 ^ (m - 1) * o) = 2 ^ (2 * m - 2) * (o * o) := by
      rw [show 2 * m - 2 = (m - 1) + (m - 1) by omega, pow_add]
      ring
    have hdiv := Nat.div_add_mod (o * o) 8
    rw [h8] at hdiv
    rw [hprod, ← hdiv, mul_add, mul_one, ← mul_assoc,
      show 2 ^ (2 * m - 2) * 8 = 2 ^ h by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega,
      Nat.mul_add_mod]
  have hB₂sum : ∑ x ∈ B₂, f (s + x ^ 2) =
      (B₂.card : ℝ) * f (s + ((2 ^ (2 * m - 2) : ℕ) : ZMod (2 ^ h))) := by
    rw [sum_congr rfl fun x hx => by rw [hsq2 x hx], sum_const, nsmul_eq_mul]
  -- `#B₂ = 2^{h-m}`
  have hcard₂ : B₂.card = 2 ^ (h - m) := by
    have e1 := card_dvd_val (h := h) (p := 2) (by norm_num) (by omega : m - 1 ≤ h)
    have e2 := card_dvd_val (h := h) (p := 2) (by norm_num) (by omega : m ≤ h)
    have e3 := card_filter_add_card_filter_not
      (s := univ.filter (fun d : ZMod (2 ^ h) => 2 ^ (m - 1) ∣ d.val))
      (fun x : ZMod (2 ^ h) => 2 ^ m ∣ x.val)
    have f1 : (univ.filter (fun d : ZMod (2 ^ h) => 2 ^ (m - 1) ∣ d.val)).filter
        (fun x : ZMod (2 ^ h) => 2 ^ m ∣ x.val) =
        univ.filter (fun d : ZMod (2 ^ h) => 2 ^ m ∣ d.val) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      exact fun hx => (Nat.pow_dvd_pow 2 (by omega)).trans hx
    have f2 : (univ.filter (fun d : ZMod (2 ^ h) => 2 ^ (m - 1) ∣ d.val)).filter
        (fun x : ZMod (2 ^ h) => ¬ 2 ^ m ∣ x.val) = B₂ := by
      ext x
      rw [hB₂, mem_filter, mem_filter, mem_filter, hmemA, not_not]
      simp only [mem_univ, true_and]
      exact and_comm
    rw [f1, f2, e1, e2] at e3
    have e4 : 2 ^ (h - (m - 1)) = 2 * 2 ^ (h - m) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e4] at e3
    omega
  rw [← hsplit, hB₁zero, zero_add, hB₂sum, hcard₂]
  push_cast
  ring

/-- **`lem:imp:padic-envelope` at `2`** (`h = 2m + 1`, `m ≥ 2`): on the exact-depth space
`ran Π_l` the transition of the square-increment law (V1's `squareIncrementLaw 2 h m`) is bounded
by the paper's tail `δ_l = PartVLaws.twoTail m l`. -/
theorem two_envelope_aux {m : ℕ} (hm : 2 ≤ m) (hh : h = 2 * m + 1)
    (hne : (PartV.lowValuation 2 h m).Nonempty) {l : ℕ} (hl : l ≤ h)
    {f : ZMod (2 ^ h) → ℝ} (hf : (Chain.residues 2 h).diff l *ᵥ f = f) :
    (convMatrix (PartV.squareIncrementLaw 2 h m hne).weight *ᵥ f) ⬝ᵥ
      (convMatrix (PartV.squareIncrementLaw 2 h m hne).weight *ᵥ f) ≤
      PartVLaws.twoTail m l ^ 2 * (f ⬝ᵥ f) := by
  have hmh : m ≤ h := by omega
  have he0 : 0 ≤ PartVLaws.topErr 2 m := (PartVLaws.topErr_pos (by norm_num) m).le
  have he1 : PartVLaws.topErr 2 m < 1 := by
    unfold PartVLaws.topErr
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (by omega))
  have hsplit : ∀ {l : ℕ}, l ≤ h → l ≤ 2 * m → (Chain.residues 2 h).diff l *ᵥ f = f →
      ∀ s, ∑ x ∈ PartV.lowValuation 2 h m, f (s + x ^ 2) =
        ∑ x, f (s + x ^ 2) - ((2 : ℕ) : ℝ) ^ (h - m) * f s :=
    fun hl hlm hf s => sqSum_split (by norm_num) hmh hl hlm hf s
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rw [conv_level_zero _ hf]
    simp only [PartVLaws.twoTail, ↓reduceIte, one_pow, one_mul, le_refl]
  by_cases hl1 : l = 1
  · subst hl1
    have hS : ∑ s, (∑ x, f (s + x ^ 2)) ^ 2 ≤ (((2 : ℕ) : ℝ) ^ h * 0) ^ 2 * ∑ t, f t ^ 2 := by
      simp only [two_sum_level_one (by omega) hf, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, sum_const_zero, mul_zero, zero_mul, le_refl]
    have h := assemble (p := 2) (by norm_num) (by omega) hmh hne le_rfl hS
      (hsplit hl (by omega) hf)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by rw [dot_self_eq]; positivity))
    have htail : PartVLaws.twoTail m 1 = ((2 : ℝ) ^ (-(1 : ℝ) / 2) + PartVLaws.topErr 2 m) /
        (1 - PartVLaws.topErr 2 m) := by
      simp only [PartVLaws.twoTail, one_ne_zero, ↓reduceIte, Nat.one_le_ofNat]
    rw [htail]
    have hd : 0 < 1 - PartVLaws.topErr 2 m := by linarith
    have hr : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    apply pow_le_pow_left₀ (div_nonneg (by simpa using he0) hd.le)
    apply div_le_div_of_nonneg_right _ hd.le
    linarith
  by_cases htop : l = h
  · subst htop
    have hT : ∀ s, (convMatrix (PartV.squareIncrementLaw 2 l m hne).weight *ᵥ f) s =
        ((PartV.lowValuation 2 l m).card : ℝ)⁻¹ *
          ((2 : ℝ) ^ (l - m) * f (s + ((2 ^ (2 * m - 2) : ℕ) : ZMod (2 ^ l)))) := by
      intro s
      rw [conv_squareIncrement_mulVec hne f s, two_top_sum hm hh hf s]
    have hcardA := card_lowValuation (h := l) (p := 2) (by norm_num) hmh
    have htail : PartVLaws.twoTail m l = PartVLaws.topErr 2 m / (1 - PartVLaws.topErr 2 m) := by
      rw [hh]
      simp only [PartVLaws.twoTail, show 2 * m + 1 ≠ 0 by omega, ↓reduceIte,
        show ¬ 2 * m + 1 ≤ 2 by omega, lt_irrefl]
    rw [dot_self_eq, dot_self_eq, htail]
    simp only [hT, mul_pow]
    rw [← mul_sum, ← mul_sum]
    have hre : ∑ s, f (s + ((2 ^ (2 * m - 2) : ℕ) : ZMod (2 ^ l))) ^ 2 = ∑ t, f t ^ 2 :=
      Fintype.sum_equiv (Equiv.addRight _) _ _ (fun s => rfl)
    rw [hre, hcardA]
    have he : PartVLaws.topErr 2 m = ((2 : ℝ) ^ m)⁻¹ := by unfold PartVLaws.topErr; norm_num
    have hpow : (2 : ℝ) ^ l = 2 ^ m * 2 ^ (l - m) := by
      rw [← pow_add]; congr 1; omega
    rw [he]
    push_cast
    rw [hpow]
    apply le_of_eq
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have h2lm : (0 : ℝ) < 2 ^ (l - m) := by positivity
    have hm1 : (1 : ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) (by omega)
    have hne1 : (2 : ℝ) ^ m - 1 ≠ 0 := by linarith
    have hne2 : (2 : ℝ) ^ m * 2 ^ (l - m) - 2 ^ (l - m) ≠ 0 := by nlinarith
    field_simp
  · -- `2 ≤ l ≤ 2m`
    have hl2 : 2 ≤ l := by omega
    have hlm : l ≤ 2 * m := by omega
    set r : ℝ := (2 : ℝ) ^ (-((l - 1 : ℕ) : ℝ) / 2) with hr
    have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
    have hr2 : r ^ 2 = ((2 : ℝ) ^ (l - 1))⁻¹ := rpow_neg_half_sq (by norm_num) (l - 1)
    have hS : ∑ s, (∑ x, f (s + x ^ 2)) ^ 2 ≤ (((2 : ℕ) : ℝ) ^ h * r) ^ 2 * ∑ t, f t ^ 2 := by
      rw [two_sq_sum hl2 hl hf, mul_pow, hr2]
      apply le_of_eq
      push_cast
      have : (2 : ℝ) ^ (h - (l - 1)) = 2 ^ h * ((2 : ℝ) ^ (l - 1))⁻¹ := by
        rw [pow_sub₀ _ (by norm_num) (by omega : l - 1 ≤ h)]
      rw [this]
      ring
    have h := assemble (p := 2) (by norm_num) (by omega) hmh hne hr0 hS (hsplit hl hlm hf)
    refine h.trans (le_of_eq ?_)
    congr 2
    have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    by_cases hl2' : l = 2
    · subst hl2'
      simp only [PartVLaws.twoTail, show (2 : ℕ) ≠ 0 by norm_num, ↓reduceIte, le_refl, hr]
      norm_num
    · simp only [PartVLaws.twoTail, show l ≠ 0 by omega, ↓reduceIte, show ¬ l ≤ 2 by omega,
        show l < 2 * m + 1 by omega, hr, hcast]

omit [NeZero (2 ^ h)] in
/-- **`lem:imp:padic-envelope` at `2`**, for a prime variable `p = 2`. -/
theorem two_envelope {p : ℕ} [NeZero (p ^ h)] (hp : p = 2) {m : ℕ} (hm : 2 ≤ m)
    (hh : h = 2 * m + 1) (hne : (PartV.lowValuation p h m).Nonempty) {l : ℕ} (hl : l ≤ h)
    {f : ZMod (p ^ h) → ℝ} (hf : (Chain.residues p h).diff l *ᵥ f = f) :
    (convMatrix (PartV.squareIncrementLaw p h m hne).weight *ᵥ f) ⬝ᵥ
      (convMatrix (PartV.squareIncrementLaw p h m hne).weight *ᵥ f) ≤
      PartVLaws.twoTail m l ^ 2 * (f ⬝ᵥ f) := by
  subst hp
  exact two_envelope_aux hm hh hne hl hf

end Two

end Sarkozy.IndexCert
