module

public import Sarkozy.Kernel.RootDatum
public import Sarkozy.Kernel.CoefficientIdentity

@[expose] public section

/-!
# Root classes at finite conductor depth

This module constructs the root-class data `RootClassDatum D r` of `RootDatum.lean`
(paper: `lem:kernel-depth-classes`, and the local rule `lem:record:prime-power-lift`(a)
of Appendix C) for

* nonvanishing square classes `r` modulo `D` (`def:nonvanishing-square-class`),
  `rootClassDatum_of_nonvanishing`, and
* strict square classes modulo `8d`, `d` odd (`def:strict-square-class`),
  `rootClassDatum_of_strict`.

Local rule. Let `p` be prime, `h = v_p(D)`, and let `b`, `e` satisfy `e ≤ h < 2e`,
`p^h ∣ b² - r`, `2b = p^(h-e) u` with `p ∤ u`. Then every `m ≡ b (mod p^e)` has
`m² ≡ r (mod p^h)` (`local_root_sq`), and for `k > h`, `p ∤ x`, the phases
`e(x m²/p^k)` sum to zero over this class modulo `p^k` (`local_class_sum_zero`):
writing `m = b + p^e t`, `m² = r + p^h φ(t)` with `φ(t) = w + u t + p^(2e-h) t²`, and
`φ` permutes `ℤ/p^nℤ` because its derivative is a unit (`poly_injective`).

The local roots are obtained by Hensel lifting (`hensel_odd`, `hensel_two`): at odd `p`
the root is `p^j c` with `c² ≡ u (mod p^(h-2j))`, period exponent `e = h - j`; at `2`
it is `2^j c`, `c` odd, period exponent `e = h - j - 1`. The global class is the Chinese
remainder combination of the local ones.

New material for this paper.
-/

namespace Sarkozy

section
open Finset
open scoped BigOperators
namespace Kernel

/-! ## The polynomial permutation and the vanishing character sum -/

lemma poly_injective (p n : ℕ) [Fact p.Prime] (w u v : ZMod (p ^ n)) (hu : IsUnit u)
    (hv : ∃ y : ZMod (p ^ n), v = (p : ZMod (p ^ n)) * y) :
    Function.Injective (fun t : ZMod (p ^ n) => w + u * t + v * t ^ 2) := by
  intro t₁ t₂ heq
  obtain ⟨y, rfl⟩ := hv
  have h1 : (t₁ - t₂) * (u + (p : ZMod (p ^ n)) * y * (t₁ + t₂)) = 0 := by
    have := heq
    simp only at this
    linear_combination this
  have hnil : IsNilpotent ((p : ZMod (p ^ n)) * y * (t₁ + t₂)) := by
    refine ⟨n, ?_⟩
    rw [mul_assoc, mul_pow]
    have : ((p : ZMod (p ^ n))) ^ n = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [this, zero_mul]
  have hunit : IsUnit (u + (p : ZMod (p ^ n)) * y * (t₁ + t₂)) :=
    hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
  have h2 : t₁ - t₂ = 0 := by
    have := congrArg (· * (hunit.unit⁻¹ : (ZMod (p ^ n))ˣ).val) h1
    simp only [zero_mul, mul_assoc, IsUnit.mul_val_inv, mul_one] at this
    exact this
  exact sub_eq_zero.mp h2

lemma isCoprime_of_not_dvd (p : ℕ) [Fact p.Prime] (u : ℤ) (hpu : ¬ (p : ℤ) ∣ u) :
    IsCoprime (p : ℤ) u :=
  (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))).mpr hpu

lemma isUnit_intCast_of_not_dvd (p n : ℕ) [Fact p.Prime] (u : ℤ) (hpu : ¬ (p : ℤ) ∣ u) :
    IsUnit (u : ZMod (p ^ n)) := by
  have hc : IsCoprime ((p : ℤ) ^ n) u := (isCoprime_of_not_dvd p u hpu).pow_left
  obtain ⟨s, t, hst⟩ := hc
  refine isUnit_iff_exists_inv.mpr ⟨(t : ZMod (p ^ n)), ?_⟩
  have h := congrArg (fun z : ℤ => (z : ZMod (p ^ n))) hst
  push_cast at h
  have h0 : ((p : ZMod (p ^ n))) ^ n = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [h0, mul_zero, zero_add] at h
  linear_combination h

lemma sum_zmod_eq_sum_range (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    ∑ x : ZMod q, f x = ∑ m ∈ range q, f (m : ZMod q) := by
  have h := expect_zmod_range f
  unfold periodicMean at h
  rw [expect_eq_sum_div_card, card_univ, ZMod.card] at h
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp at h
  linear_combination h

lemma expPhase_int_div (z : ℤ) (q : ℕ) [NeZero q] :
    expPhase ((z : ℝ) / q) = ZMod.stdAddChar (z : ZMod q) := by
  rw [ZMod.stdAddChar_coe]
  unfold expPhase
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The sum of `e(x φ(t)/p^n)` over a full period vanishes when `φ` permutes residues. -/
lemma poly_phase_sum_zero (p n : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (w u v x : ℤ)
    (hpu : ¬ (p : ℤ) ∣ u) (hpv : (p : ℤ) ∣ v) (hpx : ¬ (p : ℤ) ∣ x) :
    ∑ t ∈ range (p ^ n), expPhase ((x : ℝ) * ((w + u * t + v * t ^ 2 : ℤ) : ℝ) / (p ^ n : ℕ)) = 0 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  set ψ : AddChar (ZMod (p ^ n)) ℂ := ZMod.stdAddChar with hψ
  have hterm : ∀ t : ℕ, expPhase ((x : ℝ) * ((w + u * t + v * t ^ 2 : ℤ) : ℝ) / (p ^ n : ℕ)) =
      (fun s : ZMod (p ^ n) => ψ (s * (x : ZMod (p ^ n))))
        ((w : ZMod (p ^ n)) + (u : ZMod (p ^ n)) * (t : ZMod (p ^ n)) +
          (v : ZMod (p ^ n)) * (t : ZMod (p ^ n)) ^ 2) := by
    intro t
    have h := expPhase_int_div ((w + u * t + v * t ^ 2) * x) (p ^ n)
    rw [show ((x : ℝ) * ((w + u * t + v * t ^ 2 : ℤ) : ℝ) / (p ^ n : ℕ)) =
      (((w + u * t + v * t ^ 2) * x : ℤ) : ℝ) / (p ^ n : ℕ) by push_cast; ring, h]
    simp only [hψ]
    push_cast
    rfl
  simp_rw [hterm]
  rw [← sum_zmod_eq_sum_range (p ^ n) (fun t : ZMod (p ^ n) =>
    (fun s : ZMod (p ^ n) => ψ (s * (x : ZMod (p ^ n))))
      ((w : ZMod (p ^ n)) + (u : ZMod (p ^ n)) * t + (v : ZMod (p ^ n)) * t ^ 2))]
  have hinj := poly_injective p n (w : ZMod (p ^ n)) (u : ZMod (p ^ n)) (v : ZMod (p ^ n))
    (isUnit_intCast_of_not_dvd p n u hpu)
    (by
      obtain ⟨y, hy⟩ := hpv
      exact ⟨(y : ZMod (p ^ n)), by rw [hy]; push_cast; ring⟩)
  rw [Fintype.sum_bijective _ hinj.bijective_of_finite
    (fun t => (fun s : ZMod (p ^ n) => ψ (s * (x : ZMod (p ^ n))))
      ((w : ZMod (p ^ n)) + (u : ZMod (p ^ n)) * t + (v : ZMod (p ^ n)) * t ^ 2))
    (fun s => ψ (s * (x : ZMod (p ^ n)))) (fun _ => rfl)]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (p ^ n))]
  have hx0 : (x : ZMod (p ^ n)) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have hpn : (p : ℤ) ∣ (p : ℤ) ^ n := dvd_pow_self _ (by omega : n ≠ 0)
    have h' : (p : ℤ) ^ n ∣ x := by exact_mod_cast h
    exact hpx (hpn.trans h')
  rw [ite_eq_right hx0]
  simp

/-! ## The local rule at one prime -/

/-- The square identity behind the local rule: for `m = b + p^e t`,
`m² - r = (b² - r) + p^h (u t + p^(2e-h) t²)`. -/
lemma local_square_identity (p h e : ℕ) (b r u t : ℤ) (heh : e ≤ h) (he2 : h ≤ 2 * e)
    (hu : 2 * b = (p : ℤ) ^ (h - e) * u) :
    (b + (p : ℤ) ^ e * t) ^ 2 - r = (b ^ 2 - r) + (p : ℤ) ^ h * (u * t + (p : ℤ) ^ (2 * e - h) * t ^ 2) := by
  have hpow1 : (p : ℤ) ^ h = (p : ℤ) ^ (h - e) * (p : ℤ) ^ e := by
    rw [← pow_add]; congr 1; omega
  have hpow2 : (p : ℤ) ^ h * (p : ℤ) ^ (2 * e - h) = (p : ℤ) ^ e * (p : ℤ) ^ e := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  linear_combination ((p : ℤ) ^ e * t) * hu - (u * t) * hpow1 - t ^ 2 * hpow2

/-- The root property of the local class (`lem:kernel-depth-classes`): every `m ≡ b`
modulo `p^e` squares to `r` modulo `p^h`. -/
lemma local_root_sq (p h e : ℕ) (b r u : ℤ) (heh : e ≤ h) (he2 : h ≤ 2 * e)
    (hb : (p : ℤ) ^ h ∣ b ^ 2 - r) (hu : 2 * b = (p : ℤ) ^ (h - e) * u) (m : ℤ)
    (hm : m ≡ b [ZMOD (p : ℤ) ^ e]) : (p : ℤ) ^ h ∣ m ^ 2 - r := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hm.symm
  have hm' : m = b + (p : ℤ) ^ e * t := by linarith
  rw [hm', local_square_identity p h e b r u t heh he2 hu]
  exact dvd_add hb (dvd_mul_right _ _)

/-- The class condition is inherited by every representative `b'` of the class `b mod p^e`. -/
lemma local_unit_shift (p h e : ℕ) [Fact p.Prime] (b u : ℤ) (heh : e ≤ h) (he2 : h + 1 ≤ 2 * e)
    (hu : 2 * b = (p : ℤ) ^ (h - e) * u) (hpu : ¬ (p : ℤ) ∣ u) (q : ℤ) :
    2 * (b - (p : ℤ) ^ e * q) = (p : ℤ) ^ (h - e) * (u - 2 * (p : ℤ) ^ (2 * e - h) * q) ∧
      ¬ (p : ℤ) ∣ (u - 2 * (p : ℤ) ^ (2 * e - h) * q) := by
  have hpow : (p : ℤ) ^ e = (p : ℤ) ^ (h - e) * (p : ℤ) ^ (2 * e - h) := by
    rw [← pow_add]; congr 1; omega
  constructor
  · rw [mul_sub, hu, hpow]; ring
  · intro hdiv
    apply hpu
    have h1 : (p : ℤ) ∣ 2 * (p : ℤ) ^ (2 * e - h) * q := by
      apply Dvd.dvd.mul_right
      apply Dvd.dvd.mul_left
      exact dvd_pow_self _ (by omega)
    have := dvd_add hdiv h1
    simpa using this

/-- The local rule (`lem:record:prime-power-lift`(a)): for `k > h` and `p ∤ x`, the phases
`e(x m²/p^k)` sum to zero over the residues `m mod p^k` of the class `b mod p^e`. -/
lemma local_class_sum_zero (p : ℕ) [Fact p.Prime] (h e k : ℕ) (b r u x : ℤ)
    (heh : e ≤ h) (he2 : h + 1 ≤ 2 * e) (hhk : h < k)
    (hb : (p : ℤ) ^ h ∣ b ^ 2 - r) (hu : 2 * b = (p : ℤ) ^ (h - e) * u) (hpu : ¬ (p : ℤ) ∣ u)
    (hpx : ¬ (p : ℤ) ∣ x) :
    ∑ m ∈ range (p ^ k), (if (m : ℤ) ≡ b [ZMOD (p : ℤ) ^ e] then (1 : ℂ) else 0) *
      expPhase ((x : ℝ) * (m : ℝ) ^ 2 / (p ^ k : ℕ)) = 0 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpe : 0 < p ^ e := pow_pos (by omega) e
  have hpeZ : (0 : ℤ) < (p : ℤ) ^ e := by exact_mod_cast hpe
  -- the least nonnegative representative
  set b₀ : ℕ := (b % (p : ℤ) ^ e).toNat with hb₀def
  have hb₀Z : (b₀ : ℤ) = b % (p : ℤ) ^ e := Int.toNat_of_nonneg (Int.emod_nonneg _ hpeZ.ne')
  have hb₀lt : b₀ < p ^ e := by
    have h1 : b % (p : ℤ) ^ e < (p : ℤ) ^ e := Int.emod_lt_of_pos _ hpeZ
    have h2 : (b₀ : ℤ) < ((p ^ e : ℕ) : ℤ) := by rw [hb₀Z]; push_cast; exact h1
    exact_mod_cast h2
  set q : ℤ := b / (p : ℤ) ^ e with hqdef
  have hbq : (b₀ : ℤ) = b - (p : ℤ) ^ e * q := by rw [hb₀Z, Int.emod_def]
  obtain ⟨hu₀, hpu₀⟩ := local_unit_shift p h e b u heh he2 hu hpu q
  rw [← hbq] at hu₀
  set u₀ := u - 2 * (p : ℤ) ^ (2 * e - h) * q with hu₀def
  have hb₀mod : (b₀ : ℤ) ≡ b [ZMOD (p : ℤ) ^ e] := by
    rw [hb₀Z]; exact Int.mod_modEq b _
  have hb₀sq : (p : ℤ) ^ h ∣ (b₀ : ℤ) ^ 2 - r :=
    local_root_sq p h e b r u heh (by omega) hb hu _ hb₀mod
  obtain ⟨w, hw⟩ := hb₀sq
  -- reindex the class by `m = b₀ + p^e t`
  have hreindex : ∑ m ∈ range (p ^ k), (if (m : ℤ) ≡ b [ZMOD (p : ℤ) ^ e] then (1 : ℂ) else 0) *
      expPhase ((x : ℝ) * (m : ℝ) ^ 2 / (p ^ k : ℕ)) =
      ∑ t ∈ range (p ^ (k - e)),
        expPhase ((x : ℝ) * (((b₀ + p ^ e * t : ℕ) : ℝ)) ^ 2 / (p ^ k : ℕ)) := by
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_nbij (fun t => b₀ + p ^ e * t)
    · intro t ht
      rw [mem_range] at ht
      rw [mem_filter, mem_range]
      constructor
      · have hk : p ^ k = p ^ e * p ^ (k - e) := by rw [← pow_add]; congr 1; omega
        rw [hk]
        calc b₀ + p ^ e * t < p ^ e + p ^ e * t := by omega
          _ = p ^ e * (t + 1) := by ring
          _ ≤ p ^ e * p ^ (k - e) := Nat.mul_le_mul_left _ ht
      · push_cast
        calc (b₀ : ℤ) + (p : ℤ) ^ e * t ≡ b₀ + 0 [ZMOD (p : ℤ) ^ e] := by
              apply Int.ModEq.add_left
              exact (Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))
          _ = b₀ := by ring
          _ ≡ b [ZMOD (p : ℤ) ^ e] := hb₀mod
    · intro t₁ _ t₂ _ heq
      simp only at heq
      have := Nat.eq_of_mul_eq_mul_left hpe (by omega : p ^ e * t₁ = p ^ e * t₂)
      exact this
    · intro m hm
      rw [mem_coe, mem_filter, mem_range] at hm
      obtain ⟨hmk, hmb⟩ := hm
      have hmod : m % p ^ e = b₀ := by
        have h1 : ((m : ℤ)) % (p : ℤ) ^ e = b % (p : ℤ) ^ e := hmb
        have h2 : ((m % p ^ e : ℕ) : ℤ) = (m : ℤ) % (p : ℤ) ^ e := by push_cast; rfl
        have h3 : ((m % p ^ e : ℕ) : ℤ) = (b₀ : ℤ) := by rw [h2, h1, hb₀Z]
        exact_mod_cast h3
      refine ⟨m / p ^ e, ?_, ?_⟩
      · rw [coe_range, Set.mem_Iio]
        have hk : p ^ k = p ^ e * p ^ (k - e) := by rw [← pow_add]; congr 1; omega
        rw [Nat.div_lt_iff_lt_mul hpe]
        rw [hk] at hmk
        linarith [hmk]
      · simp only
        rw [← hmod]
        exact Nat.mod_add_div m (p ^ e)
    · intro t _
      rfl
  rw [hreindex]
  -- the phase in terms of the quadratic polynomial `φ`
  set n := k - h with hndef
  have hn1 : 1 ≤ n := by omega
  have hphase : ∀ t : ℕ,
      expPhase ((x : ℝ) * (((b₀ + p ^ e * t : ℕ) : ℝ)) ^ 2 / (p ^ k : ℕ)) =
        expPhase ((x : ℝ) * (r : ℝ) / (p ^ k : ℕ)) *
          expPhase ((x : ℝ) * ((w + u₀ * t + (p : ℤ) ^ (2 * e - h) * t ^ 2 : ℤ) : ℝ) / (p ^ n : ℕ)) := by
    intro t
    have hid := local_square_identity p h e (b₀ : ℤ) r u₀ (t : ℤ) heh (by omega) hu₀
    rw [hw] at hid
    have hidR : (((b₀ + p ^ e * t : ℕ) : ℝ)) ^ 2 =
        (r : ℝ) + ((p : ℝ) ^ h) * ((w + u₀ * t + (p : ℤ) ^ (2 * e - h) * t ^ 2 : ℤ) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hid
      push_cast at this ⊢
      linarith
    rw [← expPhase_add]
    congr 1
    rw [hidR]
    have hpk : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ h * ((p ^ n : ℕ) : ℝ) := by
      push_cast
      rw [← pow_add]
      congr 1
      omega
    have hph : (p : ℝ) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have hpn : ((p ^ n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast pow_ne_zero n (Fact.out : p.Prime).ne_zero
    rw [hpk]
    field_simp
  simp_rw [hphase]
  rw [← mul_sum]
  -- periodicity in `t` with period `p^n`
  have hper : Function.Periodic (fun t : ℕ =>
      expPhase ((x : ℝ) * ((w + u₀ * t + (p : ℤ) ^ (2 * e - h) * t ^ 2 : ℤ) : ℝ) / (p ^ n : ℕ)))
      (p ^ n) := by
    intro t
    simp only
    have hpn : ((p ^ n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast pow_ne_zero n (Fact.out : p.Prime).ne_zero
    have he : (x : ℝ) * ((w + u₀ * ((t + p ^ n : ℕ) : ℤ) + (p : ℤ) ^ (2 * e - h) *
        ((t + p ^ n : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) / (p ^ n : ℕ) =
        (x : ℝ) * ((w + u₀ * t + (p : ℤ) ^ (2 * e - h) * t ^ 2 : ℤ) : ℝ) / (p ^ n : ℕ) +
          ((x * (u₀ + (p : ℤ) ^ (2 * e - h) * (2 * t + p ^ n)) : ℤ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [he, expPhase_add, expPhase_int, mul_one]
  have hsplit : p ^ (k - e) = p ^ n * p ^ (h - e) := by rw [← pow_add]; congr 1; omega
  rw [hsplit, periodic_sum_multiple _ _ _ hper]
  rw [poly_phase_sum_zero p n hn1 w u₀ ((p : ℤ) ^ (2 * e - h)) x hpu₀
    (dvd_pow_self _ (by omega)) hpx]
  simp

/-! ## Hensel lifting of square roots of units -/

/-- Hensel lifting at an odd prime (the remark after `def:strict-square-class`): a unit
that is a square modulo `p` is a square of a unit modulo every power of `p`. -/
lemma hensel_odd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (u : ℤ) (hpu : ¬ (p : ℤ) ∣ u)
    (hsq : IsSquare (u : ZMod p)) :
    ∀ n : ℕ, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ (p : ℤ) ^ (n + 1) ∣ c ^ 2 - u := by
  intro n
  induction n with
  | zero =>
    obtain ⟨y, hy⟩ := hsq
    refine ⟨(y.val : ℤ), ?_, ?_⟩
    · intro hc
      apply hpu
      have h1 : ((y.val : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
      have h2 : y = 0 := by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val] at h1
        exact h1
      have h3 : (u : ZMod p) = 0 := by rw [hy, h2, mul_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h3
    · rw [zero_add, pow_one]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [ZMod.natCast_zmod_val, hy]
      ring
  | succ n ih =>
    obtain ⟨c, hpc, w, hw⟩ := ih
    have hc0 : ((c : ZMod p)) ≠ 0 := fun h => hpc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this
      exact hp2 this
    set t : ℤ := (((-(w : ZMod p)) * (2 * (c : ZMod p))⁻¹).val : ℤ) with htdef
    have ht : (((w + 2 * c * t : ℤ)) : ZMod p) = 0 := by
      push_cast
      rw [htdef, Int.cast_natCast, ZMod.natCast_zmod_val]
      have h2c : (2 * (c : ZMod p)) ≠ 0 := mul_ne_zero h20 hc0
      field_simp
      ring
    obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ht
    refine ⟨c + (p : ℤ) ^ (n + 1) * t, ?_, ?_⟩
    · intro hdiv
      apply hpc
      have h1 : (p : ℤ) ∣ (p : ℤ) ^ (n + 1) * t := Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
      have := dvd_sub hdiv h1
      simpa using this
    · refine ⟨z + (p : ℤ) ^ n * t ^ 2, ?_⟩
      have hp : (p : ℤ) ^ (n + 1 + 1) = (p : ℤ) ^ (n + 1) * p := by ring
      have h2 : (c + (p : ℤ) ^ (n + 1) * t) ^ 2 - u =
          (p : ℤ) ^ (n + 1) * ((w + 2 * c * t) + (p : ℤ) ^ (n + 1) * t ^ 2) := by
        linear_combination hw
      rw [h2, hz]
      ring

/-- Lifting at `2` (the remark after `def:nonvanishing-square-class`): every `u ≡ 1 mod 8`
is the square of an odd integer modulo every power `2^(n+3)`. -/
lemma hensel_two (u : ℤ) (hu : u ≡ 1 [ZMOD 8]) :
    ∀ n : ℕ, ∃ c : ℤ, ¬ (2 : ℤ) ∣ c ∧ (2 : ℤ) ^ (n + 3) ∣ c ^ 2 - u := by
  intro n
  induction n with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    have h := Int.modEq_iff_dvd.mp hu
    norm_num
    exact h
  | succ n ih =>
    obtain ⟨c, hc, w, hw⟩ := ih
    by_cases hw2 : (2 : ℤ) ∣ w
    · obtain ⟨w', hw'⟩ := hw2
      refine ⟨c, hc, w', ?_⟩
      rw [hw, hw']
      ring
    · refine ⟨c + 2 ^ (n + 2), ?_, ?_⟩
      · intro h
        apply hc
        have h1 : (2 : ℤ) ∣ 2 ^ (n + 2) := dvd_pow_self _ (by omega)
        have := dvd_sub h h1
        simpa using this
      · have hcw : (2 : ℤ) ∣ w + c := by
          have hwo : Odd w := Int.not_even_iff_odd.mp (fun he => hw2 (even_iff_two_dvd.mp he))
          have hco : Odd c := Int.not_even_iff_odd.mp (fun he => hc (even_iff_two_dvd.mp he))
          exact even_iff_two_dvd.mp (hwo.add_odd hco)
        obtain ⟨z, hz⟩ := hcw
        refine ⟨z + 2 ^ n, ?_⟩
        have h2 : (c + 2 ^ (n + 2)) ^ 2 - u = 2 ^ (n + 3) * (w + c) + 2 ^ (2 * n + 4) := by
          linear_combination hw
        rw [h2, hz]
        ring

/-! ## Local root data of a nonvanishing square class -/

/-- The local root class at a prime `p ∣ D` of a nonvanishing square class
(`lem:kernel-depth-classes`): a root `b`, a period exponent `e`, and the unit `u` with
`2b = p^(h-e) u`, where `h = v_p(D)`. -/
lemma exists_local_root (D : ℕ) (r : ℤ) (hr : IsNonvanishingSquareClass D r) (p : ℕ)
    (hp : p.Prime) (hpD : p ∣ D) :
    ∃ e : ℕ, ∃ b u : ℤ, e ≤ D.factorization p ∧ D.factorization p + 1 ≤ 2 * e ∧
      (p : ℤ) ^ (D.factorization p) ∣ b ^ 2 - r ∧
      2 * b = (p : ℤ) ^ (D.factorization p - e) * u ∧ ¬ (p : ℤ) ∣ u := by
  have := Fact.mk hp
  obtain ⟨j, u, hpu, hru, hcond⟩ := hr.2 p hp hpD
  set h := D.factorization p with hhdef
  have hru' : (p : ℤ) ^ h ∣ (p : ℤ) ^ (2 * j) * u - r := Int.ModEq.dvd hru
  by_cases hp2 : p = 2
  · rw [ite_eq_left hp2] at hcond
    obtain ⟨hj, hu8⟩ := hcond
    have hj' : 2 * j + 3 ≤ h := by rw [hhdef, hp2]; exact hj
    clear hj
    obtain ⟨c, hc, hcu⟩ := hensel_two u hu8 (h - 2 * j - 3)
    have hexp : h - 2 * j - 3 + 3 = h - 2 * j := by omega
    rw [hexp] at hcu
    have hp2Z : (p : ℤ) = 2 := by exact_mod_cast hp2
    refine ⟨h - j - 1, (p : ℤ) ^ j * c, c, by omega, by omega, ?_, ?_, ?_⟩
    · have hsplit : ((p : ℤ) ^ j * c) ^ 2 - r = (p : ℤ) ^ (2 * j) * (c ^ 2 - u) +
          ((p : ℤ) ^ (2 * j) * u - r) := by ring
      rw [hsplit]
      apply dvd_add _ hru'
      have hpow : (p : ℤ) ^ h = (p : ℤ) ^ (2 * j) * (p : ℤ) ^ (h - 2 * j) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow, hp2Z]
      exact mul_dvd_mul_left _ hcu
    · have hexp2 : h - (h - j - 1) = j + 1 := by omega
      rw [hexp2, hp2Z]
      ring
    · rw [hp2Z]; exact hc
  · rw [ite_eq_right hp2] at hcond
    obtain ⟨hj, hsq⟩ := hcond
    obtain ⟨c, hpc, hcu⟩ := hensel_odd p hp2 u hpu hsq (h - 2 * j - 1)
    have hexp : h - 2 * j - 1 + 1 = h - 2 * j := by omega
    rw [hexp] at hcu
    refine ⟨h - j, (p : ℤ) ^ j * c, 2 * c, by omega, by omega, ?_, ?_, ?_⟩
    · have hsplit : ((p : ℤ) ^ j * c) ^ 2 - r = (p : ℤ) ^ (2 * j) * (c ^ 2 - u) +
          ((p : ℤ) ^ (2 * j) * u - r) := by ring
      rw [hsplit]
      apply dvd_add _ hru'
      have hpow : (p : ℤ) ^ h = (p : ℤ) ^ (2 * j) * (p : ℤ) ^ (h - 2 * j) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      exact mul_dvd_mul_left _ hcu
    · have hexp2 : h - (h - j) = j := by omega
      rw [hexp2]
      ring
    · intro hdiv
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpZ.dvd_or_dvd hdiv with h2 | h2
      · have h2' : p ∣ 2 := by exact_mod_cast h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')
      · exact hpc h2

/-! ## The global root class -/

lemma modEq_base_iff {M base A m : ℕ} {B : ℤ} (hbase : base ≡ A [MOD M])
    (hA : (A : ℤ) ≡ B [ZMOD (M : ℤ)]) :
    m ≡ base [MOD M] ↔ (m : ℤ) ≡ B [ZMOD (M : ℤ)] := by
  constructor
  · intro h
    have h1 : m ≡ A [MOD M] := h.trans hbase
    exact (Int.natCast_modEq_iff.mpr h1).trans hA
  · intro h
    have h1 : (m : ℤ) ≡ A [ZMOD (M : ℤ)] := h.trans hA.symm
    exact (Int.natCast_modEq_iff.mp h1).trans hbase.symm

lemma prod_primeFactors_pow_factorization (D : ℕ) (hD : D ≠ 0) :
    ∏ p ∈ D.primeFactors, p ^ D.factorization p = D := by
  rw [← Nat.support_factorization]
  exact Nat.prod_factorization_pow_eq_self hD

/-- The phase `e(z m²/q)` with integer `z` is `q`-periodic in `m`. -/
lemma expPhase_int_sq_periodic (z : ℤ) (q : ℕ) (hq : 0 < q) :
    Function.Periodic (fun m : ℕ => expPhase ((z : ℝ) * (m : ℝ) ^ 2 / (q : ℝ))) q := by
  intro m
  simp only
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : (z : ℝ) * (((m + q : ℕ) : ℝ)) ^ 2 / (q : ℝ) =
      (z : ℝ) * (m : ℝ) ^ 2 / (q : ℝ) + ((z * (2 * m + q) : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [he, expPhase_add, expPhase_int, mul_one]

/-- The indicator of a class modulo `M` is `T`-periodic when `M ∣ T`. -/
lemma class_indicator_periodic (M T base : ℕ) (c : ℂ) (hMT : M ∣ T) :
    Function.Periodic (fun m : ℕ => if m ≡ base [MOD M] then c else 0) T := by
  intro m
  simp only
  have hmod : m + T ≡ m [MOD M] := by
    have h0 : T ≡ 0 [MOD M] := Nat.modEq_zero_iff_dvd.mpr hMT
    simpa using Nat.ModEq.add_left m h0
  have hiff : (m + T ≡ base [MOD M]) ↔ (m ≡ base [MOD M]) :=
    ⟨fun h => hmod.symm.trans h, fun h => hmod.trans h⟩
  by_cases h : m ≡ base [MOD M]
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

/-- **Root classes of nonvanishing square classes** (`lem:kernel-depth-classes`): for a
nonvanishing square class `r` modulo `D` there is a root class `m₀ mod D'`, `D' ∣ D`,
with the root property and the vanishing of the higher local character means. -/
theorem rootClassDatum_of_nonvanishing (D : ℕ) (hD : 0 < D) (r : ℤ)
    (hr : IsNonvanishingSquareClass D r) : Nonempty (RootClassDatum D r) := by
  classical
  have hloc : ∀ p ∈ D.primeFactors, ∃ e : ℕ, ∃ b u : ℤ, e ≤ D.factorization p ∧
      D.factorization p + 1 ≤ 2 * e ∧ (p : ℤ) ^ (D.factorization p) ∣ b ^ 2 - r ∧
      2 * b = (p : ℤ) ^ (D.factorization p - e) * u ∧ ¬ (p : ℤ) ∣ u :=
    fun p hp => exists_local_root D r hr p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  choose! e b u he using hloc
  set S := D.primeFactors with hS
  set s : ℕ → ℕ := fun p => p ^ e p with hsdef
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hs0 : ∀ p ∈ S, s p ≠ 0 := fun p hp => pow_ne_zero _ (hprime p hp).ne_zero
  have hspair : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime s) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
  set a : ℕ → ℕ := fun p => (b p % (p : ℤ) ^ e p).toNat with hadef
  have ha : ∀ p ∈ S, (a p : ℤ) ≡ b p [ZMOD ((s p : ℕ) : ℤ)] := by
    intro p hp
    have hpos : (0 : ℤ) < (p : ℤ) ^ e p := pow_pos (by exact_mod_cast (hprime p hp).pos) _
    have h1 : (a p : ℤ) = b p % (p : ℤ) ^ e p := Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')
    rw [h1]
    exact Int.mod_modEq _ _
  set base := Nat.chineseRemainderOfFinset a s S hs0 hspair with hbase
  have hclass : ∀ p ∈ S, ∀ m : ℕ, m ≡ base.1 [MOD s p] ↔ (m : ℤ) ≡ b p [ZMOD (p : ℤ) ^ e p] := by
    intro p hp m
    have h := modEq_base_iff (m := m) (base.2 p hp) (ha p hp)
    rw [h]
    rfl
  have hDprod := prod_primeFactors_pow_factorization D hD.ne'
  refine ⟨⟨∏ p ∈ S, s p, base.1, ?_, ?_, ?_, ?_⟩⟩
  · exact prod_pos (fun p hp => Nat.pos_of_ne_zero (hs0 p hp))
  · conv_rhs => rw [← hDprod]
    exact prod_dvd_prod_of_dvd _ _ (fun p hp => pow_dvd_pow p (he p hp).1)
  · intro m hm
    have hloc : ∀ p ∈ S, ((p ^ D.factorization p : ℕ) : ℤ) ∣ (m : ℤ) ^ 2 - r := by
      intro p hp
      obtain ⟨heh, he2, hbp, hup, _⟩ := he p hp
      have hmp : m ≡ base.1 [MOD s p] := Nat.ModEq.of_dvd (dvd_prod_of_mem s hp) hm
      push_cast
      exact local_root_sq p (D.factorization p) (e p) (b p) r (u p) heh (by omega) hbp hup _
        ((hclass p hp m).mp hmp)
    have hcop : (S : Set ℕ).Pairwise
        (Function.onFun IsCoprime fun p => ((p ^ D.factorization p : ℕ) : ℤ)) := by
      intro p hp q hq hpq
      exact Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow _ _
        ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq))
    have h := Finset.prod_dvd_of_coprime hcop hloc
    rw [← Nat.cast_prod, hDprod] at h
    exact h
  · intro α hα hnd
    have hden0 : α.den ≠ 0 := α.den_nz
    obtain ⟨p, hpk⟩ : ∃ p, D.factorization p < α.den.factorization p := by
      by_contra hcon
      push Not at hcon
      exact hnd ((Nat.factorization_le_iff_dvd hden0 hD.ne').mp (Finsupp.le_def.mpr hcon))
    have hpos : α.den.factorization p ≠ 0 := by omega
    have hpd : p ∣ α.den := Nat.dvd_of_factorization_pos hpos
    have hpp : p.Prime := by
      by_contra hnp
      exact hpos (Nat.factorization_eq_zero_of_not_prime _ hnp)
    have hpD : p ∣ D := hα p hpp hpd
    have hpS : p ∈ S := Nat.mem_primeFactors.mpr ⟨hpp, hpD, hD.ne'⟩
    have := Fact.mk hpp
    obtain ⟨heh, he2, hbp, hup, hpu⟩ := he p hpS
    set k := α.den.factorization p with hkdef
    set hh := D.factorization p with hhdef
    -- the denominator `α.den = p^k Q`
    set Q := α.den / p ^ k with hQdef
    have hQ : p ^ k * Q = α.den := Nat.ordProj_mul_ordCompl_eq_self α.den p
    have hcopQ : Nat.Coprime p Q := Nat.coprime_ordCompl hpp hden0
    have hQ0 : 0 < Q := Nat.ordCompl_pos p hden0
    -- the period `s p * P'`
    set P' := ∏ q ∈ S.erase p, s q with hP'def
    have hP : ∏ q ∈ S, s q = s p * P' := (Finset.mul_prod_erase S s hpS).symm
    have hcopP : Nat.Coprime p P' := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hqp : q ≠ p := Finset.ne_of_mem_erase hq
      have hqS : q ∈ S := Finset.mem_of_mem_erase hq
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hpp (hprime q hqS)).mpr hqp.symm)
    have hP0 : 0 < P' := prod_pos (fun q hq => Nat.pos_of_ne_zero (hs0 q (Finset.mem_of_mem_erase hq)))
    have hpk0 : 0 < p ^ k := pow_pos hpp.pos k
    -- Bezout
    have hcopZ : IsCoprime ((p : ℤ) ^ k) (Q : ℤ) := by
      have h1 : Nat.Coprime (p ^ k) Q := Nat.Coprime.pow_left k hcopQ
      have h2 := Nat.isCoprime_iff_coprime.mpr h1
      push_cast at h2
      exact h2
    obtain ⟨σ, τ, hστ⟩ := hcopZ
    set x : ℤ := α.num * τ with hxdef
    set y : ℤ := α.num * σ with hydef
    have hαxy : (α : ℝ) = (x : ℝ) / ((p ^ k : ℕ) : ℝ) + (y : ℝ) / (Q : ℝ) := by
      have hα' : (α : ℝ) = (α.num : ℝ) / (α.den : ℝ) := by
        rw [Rat.cast_def]
      have hστR : (σ : ℝ) * (p : ℝ) ^ k + (τ : ℝ) * (Q : ℝ) = 1 := by exact_mod_cast hστ
      have hpkR : ((p ^ k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpk0.ne'
      have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ0.ne'
      have hden : (α.den : ℝ) = ((p ^ k : ℕ) : ℝ) * (Q : ℝ) := by
        rw [← hQ]; push_cast; ring
      rw [hα', hden, div_add_div _ _ hpkR hQR]
      congr 1
      rw [hxdef, hydef]
      push_cast
      linear_combination (-(α.num : ℝ)) * hστR
    have hpx : ¬ (p : ℤ) ∣ x := by
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
      intro hdiv
      rcases hpZ.dvd_or_dvd hdiv with h1 | h1
      · have h2 : p ∣ α.num.natAbs := Int.natCast_dvd.mp h1
        have h3 := Nat.dvd_gcd h2 hpd
        rw [α.reduced.gcd_eq_one] at h3
        exact hpp.one_lt.ne' (Nat.dvd_one.mp h3)
      · apply hpZ.not_dvd_one
        have hk1 : 1 ≤ k := by omega
        have h4 : (p : ℤ) ∣ σ * (p : ℤ) ^ k := Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
        have h5 : (p : ℤ) ∣ τ * (Q : ℤ) := Dvd.dvd.mul_right h1 _
        rw [← hστ]
        exact dvd_add h4 h5
    -- the factorization of the summand
    set fp : ℕ → ℂ := fun m => (if m ≡ base.1 [MOD s p] then ((s p : ℕ) : ℂ) else 0) *
      expPhase ((x : ℝ) * (m : ℝ) ^ 2 / ((p ^ k : ℕ) : ℝ)) with hfpdef
    set f' : ℕ → ℂ := fun m => (if m ≡ base.1 [MOD P'] then ((P' : ℕ) : ℂ) else 0) *
      expPhase ((y : ℝ) * (m : ℝ) ^ 2 / (Q : ℝ)) with hf'def
    have hcop_sP : Nat.Coprime (s p) P' := Nat.Coprime.pow_left _ hcopP
    have hfac : ∀ m : ℕ, classWeight (∏ q ∈ S, s q) base.1 m * expPhase ((α : ℝ) * (m : ℝ) ^ 2) =
        fp m * f' m := by
      intro m
      have hph : expPhase ((α : ℝ) * (m : ℝ) ^ 2) =
          expPhase ((x : ℝ) * (m : ℝ) ^ 2 / ((p ^ k : ℕ) : ℝ)) *
            expPhase ((y : ℝ) * (m : ℝ) ^ 2 / (Q : ℝ)) := by
        rw [← expPhase_add, hαxy]
        congr 1
        ring
      unfold classWeight
      rw [hP, hph]
      have hiff := Nat.modEq_and_modEq_iff_modEq_mul (a := m) (b := base.1) hcop_sP
      simp only [hfpdef, hf'def]
      by_cases h1 : m ≡ base.1 [MOD s p] <;> by_cases h2 : m ≡ base.1 [MOD P']
      · rw [ite_eq_left (hiff.mp ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2]
        push_cast
        ring
      · rw [ite_eq_right (fun h => h2 (hiff.mpr h).2), ite_eq_left h1, ite_eq_right h2]
        ring
      · rw [ite_eq_right (fun h => h1 (hiff.mpr h).1), ite_eq_right h1, ite_eq_left h2]
        ring
      · rw [ite_eq_right (fun h => h1 (hiff.mpr h).1), ite_eq_right h1, ite_eq_right h2]
        ring
    have hspk : s p ∣ p ^ k := pow_dvd_pow p (by omega)
    have hper_p : Function.Periodic fp (p ^ k) :=
      (class_indicator_periodic (s p) (p ^ k) base.1 ((s p : ℕ) : ℂ) hspk).mul
        (expPhase_int_sq_periodic x (p ^ k) hpk0)
    have hper' : Function.Periodic f' (P' * Q) := by
      have h1 := class_indicator_periodic P' (P' * Q) base.1 ((P' : ℕ) : ℂ) (dvd_mul_right _ _)
      have h2 : Function.Periodic (fun m : ℕ => expPhase ((y : ℝ) * (m : ℝ) ^ 2 / (Q : ℝ))) (P' * Q) :=
        periodic_mul_of_dvd (expPhase_int_sq_periodic y Q hQ0) (dvd_mul_left _ _)
      exact h1.mul h2
    have hperf : Function.Periodic (fun m => fp m * f' m) (p ^ k * (P' * Q)) :=
      (periodic_mul_of_dvd hper_p (dvd_mul_right _ _)).mul
        (periodic_mul_of_dvd hper' (dvd_mul_left _ _))
    have hfeq : (fun m => classWeight (∏ q ∈ S, s q) base.1 m * expPhase ((α : ℝ) * (m : ℝ) ^ 2)) =
        fun m => fp m * f' m := funext hfac
    rw [hfeq]
    have hdvd : p ^ k * (P' * Q) ∣ α.den * ∏ q ∈ S, s q := by
      rw [hP, ← hQ]
      exact ⟨s p, by ring⟩
    have hne : α.den * ∏ q ∈ S, s q ≠ 0 :=
      Nat.mul_ne_zero hden0 (Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr hs0)).ne'
    rw [periodicMean_of_dvd _ (p ^ k * (P' * Q)) _ hne hdvd hperf]
    have : NeZero (p ^ k) := ⟨hpk0.ne'⟩
    have : NeZero (P' * Q) := ⟨(Nat.mul_pos hP0 hQ0).ne'⟩
    have hcop_all : Nat.Coprime (p ^ k) (P' * Q) :=
      Nat.Coprime.pow_left k (Nat.Coprime.mul_right hcopP hcopQ)
    rw [periodicMean_mul_coprime hcop_all fp f' hper_p hper']
    have hzero : periodicMean fp (p ^ k) = 0 := by
      unfold periodicMean
      have hsum : ∑ m ∈ range (p ^ k), fp m = ((s p : ℕ) : ℂ) *
          ∑ m ∈ range (p ^ k), (if (m : ℤ) ≡ b p [ZMOD (p : ℤ) ^ e p] then (1 : ℂ) else 0) *
            expPhase ((x : ℝ) * (m : ℝ) ^ 2 / ((p ^ k : ℕ) : ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro m _
        simp only [hfpdef]
        by_cases hm : m ≡ base.1 [MOD s p]
        · rw [ite_eq_left hm, ite_eq_left ((hclass p hpS m).mp hm)]
          ring
        · rw [ite_eq_right hm, ite_eq_right (fun h => hm ((hclass p hpS m).mpr h))]
          ring
      rw [hsum, local_class_sum_zero p hh (e p) k (b p) r (u p) x heh he2 hpk hbp hup hpu hpx]
      simp
    rw [hzero, zero_mul]

/-- Strict square classes modulo `8d` are nonvanishing square classes (`j = 0` at every
prime; the paper's remark after `def:nonvanishing-square-class`). -/
lemma isNonvanishing_of_strict (d : ℕ) (hd : Odd d) (r : ℤ) (hr : IsStrictSquareClass d r) :
    IsNonvanishingSquareClass (8 * d) r := by
  have hd0 : d ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hd
  have h8d : 0 < 8 * d := by positivity
  have h3 : 3 ≤ (8 * d).factorization 2 := by
    have h := (Nat.factorization_le_iff_dvd (by norm_num : (8 : ℕ) ≠ 0) h8d.ne').mpr
      (Dvd.intro d rfl)
    have h8 : (8 : ℕ).factorization 2 = 3 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.prime_two.factorization_self]
      rfl
    have := Finsupp.le_def.mp h 2
    omega
  refine ⟨h3, ?_⟩
  intro p hp hpD
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨0, r, ?_, by simp [Int.ModEq.refl], ?_⟩
    · intro h2
      have h1 : (8 : ℤ) ∣ r - 1 := (Int.ModEq.dvd hr.1.symm)
      have h2' : (2 : ℤ) ∣ r - 1 := (show (2 : ℤ) ∣ 8 by norm_num).trans h1
      have : (2 : ℤ) ∣ r - (r - 1) := dvd_sub (by exact_mod_cast h2) h2'
      norm_num at this
    · rw [ite_eq_left rfl]
      exact ⟨by omega, hr.1⟩
  · have hpd : p ∣ d := by
      have hc : Nat.Coprime p 8 := by
        have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
        simpa using this.pow_right 3
      exact hc.dvd_of_dvd_mul_left hpD
    obtain ⟨hr0, hrsq⟩ := hr.2 p hp hpd
    refine ⟨0, r, ?_, by simp [Int.ModEq.refl], ?_⟩
    · intro h
      exact hr0 ((ZMod.intCast_zmod_eq_zero_iff_dvd r p).mpr h)
    · rw [ite_eq_right hp2]
      exact ⟨by simpa using hp.factorization_pos_of_dvd h8d.ne' hpD, hrsq⟩

/-- **Root classes of strict square classes** (`lem:kernel-depth-classes` for the case of
`prop:record:kernel20`(i)): for `d` odd and `r` a strict square class modulo `8d` there is
a root class with the properties of `RootClassDatum`. -/
theorem rootClassDatum_of_strict (d : ℕ) (hd : Odd d) (r : ℤ)
    (hr : IsStrictSquareClass d r) : Nonempty (RootClassDatum (8 * d) r) := by
  have hd0 : d ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hd
  exact rootClassDatum_of_nonvanishing (8 * d) (by positivity) r (isNonvanishing_of_strict d hd r hr)

end Kernel
end
end Sarkozy
