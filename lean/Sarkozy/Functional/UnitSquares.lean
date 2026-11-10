module

public import Sarkozy.ProbabilityProducts
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

/-!
# Square classes and the unit squares modulo `8 d₀`

This file formalizes `def:strict-square-class` and `def:nonvanishing-square-class`
(`04_notation.tex`) and `lem:func:unitsq` (`09_comparison_theorem.tex`).

* `unitSquares n`: the squares of the unit group `(ZMod n)^×`; for a prime `p` these
  are the nonzero squares `Q_p` (`mem_unitSquares_prime`), and
  `card_unitSquares_prime`: `|Q_p| = (p - 1)/2` for odd `p`.
* `IsStrictSquareClass d r` (`D = 8d`): `r ≡ 1 (mod 8)` and `r` is a nonzero square
  modulo every prime dividing `d`.
* `IsNonvanishingSquareClass D r`: the prime-power coordinate conditions of
  `def:nonvanishing-square-class`, read on the canonical representative of the
  reduction of `r` modulo `p^{h_p}`. "Square unit part" at an odd prime is read as
  "the unit part is a nonzero square modulo `p`"; by Hensel's lemma (the remark after
  the definition, not formalized here) this is the same as being a square modulo
  `p^{h_p - 2j_p}`. `isNonvanishingSquareClass_of_strict`: strict square classes with
  `v₂(D) = 3` are a special case.
* `lem:func:unitsq`(i): `mem_unitSquares_iff` (the set description, for `d₀` odd and
  squarefree) and `isStrictSquareClass_of_mem_unitSquares`.
* `lem:func:unitsq`(ii): `unitCRT` is the Chinese remainder isomorphism
  `ZMod (8 d₀) ≃+* ∏_{i} ZMod (m_i)` with moduli `m_none = 8`, `m_p = p` (`p ∣ d₀`);
  `unitCRT_apply` identifies its coordinates with the reductions;
  `map_unitSquares_unitCRT` (it maps the unit squares onto the product of the
  coordinate sets), `uniformOn_unitSquares_map` (the uniform law on `Q(M₀)` is carried
  to the product of the uniform laws, with the point mass at `1` in `ZMod 8`,
  `uniformOn_unitSquares_eight`), `card_unitSquares_eight_mul`
  (`|Q(M₀)| = ∏_{p ∣ d₀} (p-1)/2`) and `unitSquares_three` (the factor at `3` is the
  point mass at `1`). `uniformOn_unitSquares_map_coordLaw` states (ii) with the explicit
  coordinate laws `unitSquareCoordLaw` (point mass at `1` at the coordinate `8`), and
  `expect_uniformOn_unitSquares` is its expectation form.
* The Hensel-lifting remarks after the two definitions (square roots modulo full
  prime-power coordinates; strict square classes are the unit squares for non-squarefree
  `d`) are not formalized; `lem:func:unitsq` needs only the squarefree case.

No upstream code is adapted.
-/

open Finset

namespace Sarkozy.Functional

/-! ## Squares of units -/

/-- `x` is the square of a unit. -/
def IsUnitSquare {R : Type*} [Monoid R] (x : R) : Prop := ∃ u : Rˣ, (u : R) ^ 2 = x

/-- The squares of the unit group `(ZMod n)^×`; for a prime `p` this is `Q_p`. -/
def unitSquares (n : ℕ) [NeZero n] : Finset (ZMod n) :=
  (univ : Finset (ZMod n)ˣ).image fun u : (ZMod n)ˣ => (u : ZMod n) ^ 2

theorem mem_unitSquares {n : ℕ} [NeZero n] (x : ZMod n) :
    x ∈ unitSquares n ↔ IsUnitSquare x := by
  simp [unitSquares, IsUnitSquare]

theorem isUnitSquare_map_iff {R S : Type*} [Monoid R] [Monoid S] (e : R ≃* S) (x : R) :
    IsUnitSquare (e x) ↔ IsUnitSquare x := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨Units.map e.symm.toMonoidHom v, ?_⟩
    rw [Units.coe_map, MulEquiv.coe_toMonoidHom, ← map_pow, hv, MulEquiv.symm_apply_apply]
  · rintro ⟨u, hu⟩
    refine ⟨Units.map e.toMonoidHom u, ?_⟩
    rw [← hu]
    simp

theorem isUnitSquare_pi_iff {ι : Type*} {R : ι → Type*} [∀ i, Monoid (R i)]
    (y : ∀ i, R i) : IsUnitSquare y ↔ ∀ i, IsUnitSquare (y i) := by
  constructor
  · rintro ⟨u, hu⟩ i
    refine ⟨MulEquiv.piUnits u i, ?_⟩
    rw [← hu]
    rfl
  · intro h
    choose v hv using h
    refine ⟨MulEquiv.piUnits.symm v, ?_⟩
    funext i
    exact hv i

/-- `Q_p` is the set of nonzero squares of `𝔽_p`. -/
theorem isUnitSquare_prime_iff {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    IsUnitSquare x ↔ x ≠ 0 ∧ IsSquare x := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨pow_ne_zero 2 u.ne_zero, ⟨u, sq _⟩⟩
  · rintro ⟨hx, s, rfl⟩
    have hs : s ≠ 0 := by rintro rfl; exact hx (mul_zero 0)
    exact ⟨Units.mk0 s hs, by simp [sq]⟩

theorem mem_unitSquares_prime {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    x ∈ unitSquares p ↔ x ≠ 0 ∧ IsSquare x := by
  rw [mem_unitSquares, isUnitSquare_prime_iff]

theorem one_mem_unitSquares (n : ℕ) [NeZero n] : (1 : ZMod n) ∈ unitSquares n :=
  (mem_unitSquares _).mpr ⟨1, by simp⟩

theorem unitSquares_nonempty (n : ℕ) [NeZero n] : (unitSquares n).Nonempty :=
  ⟨1, one_mem_unitSquares n⟩

/-- Every unit modulo `8` squares to `1`, so `Q(8) = {1}`. -/
theorem unitSquares_eight : unitSquares 8 = {1} := by
  have key : ∀ y z : ZMod 8, y * z = 1 → y ^ 2 = 1 := by decide
  ext x
  rw [mem_unitSquares, mem_singleton]
  constructor
  · rintro ⟨u, rfl⟩
    exact key (u : ZMod 8) ((u⁻¹ : (ZMod 8)ˣ) : ZMod 8) u.mul_inv
  · rintro rfl
    exact ⟨1, by simp⟩

/-- `Q_3 = {1}`. -/
theorem unitSquares_three : unitSquares 3 = {1} := by
  have key : ∀ y z : ZMod 3, y * z = 1 → y ^ 2 = 1 := by decide
  ext x
  rw [mem_unitSquares, mem_singleton]
  constructor
  · rintro ⟨u, rfl⟩
    exact key (u : ZMod 3) ((u⁻¹ : (ZMod 3)ˣ) : ZMod 3) u.mul_inv
  · rintro rfl
    exact ⟨1, by simp⟩

/-- `|Q_p| = (p - 1)/2` for an odd prime `p`: squaring is two-to-one on `𝔽_p^×`. -/
theorem card_unitSquares_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (unitSquares p).card = (p - 1) / 2 := by
  have hfib : ∀ x ∈ unitSquares p,
      ((univ : Finset (ZMod p)ˣ).filter fun u : (ZMod p)ˣ => (u : ZMod p) ^ 2 = x).card = 2 := by
    intro x hx
    obtain ⟨u, hu⟩ := (mem_unitSquares x).mp hx
    have hne : u ≠ -u := by
      intro h
      have h2 : (2 : ZMod p) * u = 0 := by
        have := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) h
        simp only [Units.val_neg] at this
        linear_combination this
      have h20 : (2 : ZMod p) = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h u.ne_zero
      have : (p : ℕ) ∣ 2 := by
        exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h20)
      have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this
      exact hp2 this
    have hset : ((univ : Finset (ZMod p)ˣ).filter fun v : (ZMod p)ˣ => (v : ZMod p) ^ 2 = x) =
        {u, -u} := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      rw [← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj]
      exact Units.sq_eq_sq_iff_eq_or_eq_neg
    rw [hset, card_pair hne]
  have hcard := card_eq_sum_card_image (fun u : (ZMod p)ˣ => (u : ZMod p) ^ 2) univ
  rw [card_univ, ZMod.card_units p] at hcard
  have hsum : (∑ b ∈ (univ : Finset (ZMod p)ˣ).image (fun u : (ZMod p)ˣ => (u : ZMod p) ^ 2),
      ((univ : Finset (ZMod p)ˣ).filter fun a : (ZMod p)ˣ => (a : ZMod p) ^ 2 = b).card) =
      ∑ _b ∈ unitSquares p, 2 := sum_congr rfl hfib
  rw [hsum, sum_const, smul_eq_mul] at hcard
  omega

/-! ## Strict and nonvanishing square classes -/

/-- `def:strict-square-class`: for `D = 8 d` (`d` odd), a residue `r` modulo `D` is a
strict square class if `r ≡ 1 (mod 8)` and `r` is a nonzero square modulo every prime
dividing `d`. Reductions are read on the canonical representative `r.val`. -/
def IsStrictSquareClass (d : ℕ) (r : ZMod (8 * d)) : Prop :=
  ((r.val : ℕ) : ZMod 8) = 1 ∧
    ∀ p : ℕ, p.Prime → p ∣ d → ((r.val : ℕ) : ZMod p) ≠ 0 ∧ IsSquare ((r.val : ℕ) : ZMod p)

/-- The canonical representative of the reduction of `r` modulo the full prime-power
coordinate `p ^ v_p(D)`. -/
def coordinateRep (D p : ℕ) (r : ZMod D) : ℕ := r.val % p ^ D.factorization p

/-- `def:nonvanishing-square-class`: `D = 2^{h₂} ∏ p^{h_p}` with `h₂ ≥ 3`. At each odd
`p ∣ D` the reduction of `r` modulo `p^{h_p}` is nonzero, of even valuation `2j_p`
(necessarily `< h_p`) and with unit part a nonzero square modulo `p`; at `2` it is
nonzero, of even valuation `2j₂` with `h₂ - 2j₂ ≥ 3`, and its unit part is `≡ 1 (mod 8)`. -/
def IsNonvanishingSquareClass (D : ℕ) (r : ZMod D) : Prop :=
  3 ≤ D.factorization 2 ∧
    ∀ p ∈ D.primeFactors,
      coordinateRep D p r ≠ 0 ∧ Even (padicValNat p (coordinateRep D p r)) ∧
        (if p = 2 then
          padicValNat 2 (coordinateRep D 2 r) + 3 ≤ D.factorization 2 ∧
            coordinateRep D 2 r / 2 ^ padicValNat 2 (coordinateRep D 2 r) % 8 = 1
        else
          IsSquare (((coordinateRep D p r / p ^ padicValNat p (coordinateRep D p r) : ℕ)) :
            ZMod p) ∧
          ((coordinateRep D p r / p ^ padicValNat p (coordinateRep D p r) : ℕ) : ZMod p) ≠ 0)

/-- Strict square classes with `v₂(D) = 3` are nonvanishing square classes
(the remark after `def:nonvanishing-square-class`). -/
theorem isNonvanishingSquareClass_of_strict {d : ℕ} (hd : Odd d) (r : ZMod (8 * d))
    (hr : IsStrictSquareClass d r) : IsNonvanishingSquareClass (8 * d) r := by
  have hd0 : d ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hd)
  have h2d : ¬ 2 ∣ d := by
    rintro ⟨k, rfl⟩
    exact (Nat.not_even_iff_odd.mpr hd) ⟨k, by ring⟩
  have hfac2 : (8 * d).factorization 2 = 3 := by
    rw [Nat.factorization_mul (by norm_num) hd0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h2d,
      show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.prime_two.factorization_pow]
    simp
  refine ⟨hfac2.ge, ?_⟩
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  by_cases hp2 : p = 2
  · subst hp2
    have h8 : r.val % 8 = 1 := by
      have := hr.1
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at this
      simpa using this
    have hrep : coordinateRep (8 * d) 2 r = 1 := by
      simp only [coordinateRep, hfac2]
      simpa using h8
    rw [hrep]
    simp [hfac2]
  · have hpd : p ∣ d := by
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h8 | h
      · have : p ∣ 2 ^ 3 := by simpa using h8
        exact absurd (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two |>.mp
          (hpp.dvd_of_dvd_pow this)) hp2
      · exact h
    obtain ⟨hne, hsq⟩ := hr.2 p hpp hpd
    have hk : 1 ≤ (8 * d).factorization p :=
      (hpp.dvd_iff_one_le_factorization (by positivity)).mp (Nat.dvd_of_mem_primeFactors hp)
    set x := coordinateRep (8 * d) p r with hx
    have hcast : ((x : ℕ) : ZMod p) = ((r.val : ℕ) : ZMod p) := by
      have hdvd : p ∣ p ^ (8 * d).factorization p := dvd_pow_self p (by omega)
      rw [hx, coordinateRep, ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hdvd]
    have hxp : ¬ p ∣ x := by
      intro h
      apply hne
      rw [← hcast]
      exact (ZMod.natCast_eq_zero_iff x p).mpr h
    have hx0 : x ≠ 0 := by rintro h; exact hxp (h ▸ dvd_zero p)
    have hv : padicValNat p x = 0 := padicValNat.eq_zero_of_not_dvd hxp
    refine ⟨hx0, by rw [hv]; exact ⟨0, rfl⟩, ?_⟩
    rw [ite_eq_right hp2]
    rw [hv, pow_zero, Nat.div_one, hcast]
    exact ⟨hsq, hne⟩

/-! ## The Chinese remainder decomposition of `ZMod (8 d₀)` -/

variable (d0 : ℕ)

/-- The coordinate moduli of `ZMod (8 d₀) ≅ ZMod 8 × ∏_{p ∣ d₀} 𝔽_p`. -/
def unitModulus : Option d0.primeFactors → ℕ
  | none => 8
  | some p => p

instance unitModulus_neZero (i : Option d0.primeFactors) : NeZero (unitModulus d0 i) := by
  cases i with
  | none => exact show NeZero 8 from ⟨by norm_num⟩
  | some p => exact ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩

instance unitModulus_fact_prime (p : d0.primeFactors) :
    Fact ((unitModulus d0 (some p)).Prime) :=
  ⟨Nat.prime_of_mem_primeFactors p.2⟩

theorem unitModulus_pairwise_coprime (hodd : Odd d0) :
    Pairwise (Function.onFun Nat.Coprime (unitModulus d0)) := by
  intro i j hij
  have h8 : ∀ p : d0.primeFactors, Nat.Coprime 8 p := by
    intro p
    have hpp := Nat.prime_of_mem_primeFactors p.2
    have hp2 : (p : ℕ) ≠ 2 := by
      intro h
      have h2 : 2 ∣ d0 := h ▸ Nat.dvd_of_mem_primeFactors p.2
      obtain ⟨k, hk⟩ := h2
      rcases hodd with ⟨m, hm⟩
      omega
    have : Nat.Coprime (2 ^ 3) p :=
      Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hpp).mpr (Ne.symm hp2))
    simpa using this
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some q => exact h8 q
  | some p =>
    cases j with
    | none => exact (h8 p).symm
    | some q =>
      have hpq : (p : ℕ) ≠ q := fun h => hij (congrArg some (Subtype.ext h))
      exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
        (Nat.prime_of_mem_primeFactors q.2)).mpr hpq

theorem prod_unitModulus (hsf : Squarefree d0) : ∏ i, unitModulus d0 i = 8 * d0 := by
  rw [Fintype.prod_option]
  change 8 * ∏ p : d0.primeFactors, (p : ℕ) = 8 * d0
  rw [Finset.prod_coe_sort d0.primeFactors (fun p => p), Nat.prod_primeFactors_of_squarefree hsf]

/-- The Chinese remainder isomorphism of `lem:func:unitsq`(ii),
`ZMod (8 d₀) ≃+* ZMod 8 × ∏_{p ∣ d₀} 𝔽_p` (the factor `ZMod 8` is the coordinate `none`). -/
noncomputable def unitCRT (hodd : Odd d0) (hsf : Squarefree d0) :
    ZMod (8 * d0) ≃+* ∀ i, ZMod (unitModulus d0 i) :=
  (ZMod.ringEquivCongr (prod_unitModulus d0 hsf).symm).trans
    (ZMod.prodEquivPi (unitModulus d0) (unitModulus_pairwise_coprime d0 hodd))

theorem unitModulus_dvd (hsf : Squarefree d0) (i : Option d0.primeFactors) :
    unitModulus d0 i ∣ 8 * d0 := by
  rw [← prod_unitModulus d0 hsf]
  exact Finset.dvd_prod_of_mem _ (mem_univ i)

/-- The coordinates of `unitCRT` are the reductions modulo `8` and modulo `p`. -/
theorem unitCRT_apply (hodd : Odd d0) (hsf : Squarefree d0) (r : ZMod (8 * d0))
    (i : Option d0.primeFactors) :
    unitCRT d0 hodd hsf r i = ((r.val : ℕ) : ZMod (unitModulus d0 i)) := by
  have hd0 : d0 ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hodd
  have : NeZero (8 * d0) := ⟨by positivity⟩
  have h := RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun i => ZMod (unitModulus d0 i)) i).comp (unitCRT d0 hodd hsf).toRingHom)
    (ZMod.castHom (unitModulus_dvd d0 hsf i) (ZMod (unitModulus d0 i)))) r
  simp only [RingHom.comp_apply, Pi.evalRingHom_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, ZMod.castHom_apply] at h
  rw [h, ZMod.cast_eq_val]

/-! ## `lem:func:unitsq` -/

section UnitSquares

variable {d0}

instance neZero_eight_mul [NeZero d0] : NeZero (8 * d0) := ⟨by
  have := NeZero.ne d0
  positivity⟩

theorem isUnitSquare_unitCRT_iff (hodd : Odd d0) (hsf : Squarefree d0) (r : ZMod (8 * d0)) :
    IsUnitSquare r ↔ ∀ i, IsUnitSquare (((r.val : ℕ) : ZMod (unitModulus d0 i))) := by
  rw [← isUnitSquare_map_iff (unitCRT d0 hodd hsf).toMulEquiv r, isUnitSquare_pi_iff]
  apply forall_congr'
  intro i
  change IsUnitSquare (unitCRT d0 hodd hsf r i) ↔ _
  rw [unitCRT_apply]

/-- `lem:func:unitsq`(i): for `d₀` odd and squarefree, `r` is the square of a unit
modulo `M₀ = 8 d₀` exactly when `r ≡ 1 (mod 8)` and `r mod p ∈ Q_p` (a nonzero square)
for every prime `p ∣ d₀`. -/
theorem mem_unitSquares_iff [NeZero d0] (hodd : Odd d0) (hsf : Squarefree d0)
    (r : ZMod (8 * d0)) :
    r ∈ unitSquares (8 * d0) ↔
      ((r.val : ℕ) : ZMod 8) = 1 ∧
        ∀ p : ℕ, p.Prime → p ∣ d0 →
          ((r.val : ℕ) : ZMod p) ≠ 0 ∧ IsSquare ((r.val : ℕ) : ZMod p) := by
  rw [mem_unitSquares, isUnitSquare_unitCRT_iff hodd hsf, Option.forall]
  apply and_congr
  · change IsUnitSquare (((r.val : ℕ) : ZMod 8)) ↔ _
    rw [← mem_unitSquares, unitSquares_eight, mem_singleton]
  · constructor
    · intro h p hp hpd
      have hpm : p ∈ d0.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, NeZero.ne d0⟩
      have : Fact p.Prime := ⟨hp⟩
      exact (isUnitSquare_prime_iff _).mp (h ⟨p, hpm⟩)
    · intro h p
      have hpp := Nat.prime_of_mem_primeFactors p.2
      have : Fact (p : ℕ).Prime := ⟨hpp⟩
      change IsUnitSquare (((r.val : ℕ) : ZMod (p : ℕ)))
      exact (isUnitSquare_prime_iff _).mpr (h p hpp (Nat.dvd_of_mem_primeFactors p.2))

/-- `lem:func:unitsq`(i): every element of `Q(M₀)` is a strict square class modulo `M₀`;
for squarefree `d₀` the converse holds as well. -/
theorem isStrictSquareClass_iff_mem_unitSquares [NeZero d0] (hodd : Odd d0)
    (hsf : Squarefree d0) (r : ZMod (8 * d0)) :
    IsStrictSquareClass d0 r ↔ r ∈ unitSquares (8 * d0) :=
  (mem_unitSquares_iff hodd hsf r).symm

theorem isStrictSquareClass_of_mem_unitSquares [NeZero d0] (hodd : Odd d0)
    (hsf : Squarefree d0) {r : ZMod (8 * d0)} (hr : r ∈ unitSquares (8 * d0)) :
    IsStrictSquareClass d0 r :=
  (isStrictSquareClass_iff_mem_unitSquares hodd hsf r).mpr hr

/-- `lem:func:unitsq`(ii): the Chinese remainder isomorphism maps `Q(M₀)` onto the
product of the coordinate sets `Q(8) = {1}` and `Q_p`, `p ∣ d₀`. -/
theorem map_unitSquares_unitCRT [NeZero d0] (hodd : Odd d0) (hsf : Squarefree d0) :
    (unitSquares (8 * d0)).map (unitCRT d0 hodd hsf).toEquiv.toEmbedding =
      Fintype.piFinset fun i => unitSquares (unitModulus d0 i) := by
  ext y
  rw [mem_map_equiv, Fintype.mem_piFinset, mem_unitSquares]
  rw [← isUnitSquare_map_iff (unitCRT d0 hodd hsf).toMulEquiv, isUnitSquare_pi_iff]
  apply forall_congr'
  intro i
  rw [mem_unitSquares]
  change IsUnitSquare ((unitCRT d0 hodd hsf) ((unitCRT d0 hodd hsf).symm y) i) ↔ _
  rw [RingEquiv.apply_symm_apply]

/-- `lem:func:unitsq`(ii): `|Q(M₀)| = ∏_{p ∣ d₀} (p - 1)/2`. -/
theorem card_unitSquares_eight_mul [NeZero d0] (hodd : Odd d0) (hsf : Squarefree d0) :
    (unitSquares (8 * d0)).card = ∏ p ∈ d0.primeFactors, (p - 1) / 2 := by
  have h := congrArg Finset.card (map_unitSquares_unitCRT hodd hsf)
  rw [card_map, Fintype.card_piFinset, Fintype.prod_option] at h
  rw [h]
  have h8 : (unitSquares (unitModulus d0 none)).card = 1 := by
    change (unitSquares 8).card = 1
    rw [unitSquares_eight, card_singleton]
  rw [h8, one_mul, ← Finset.prod_coe_sort d0.primeFactors (fun p => (p - 1) / 2)]
  apply prod_congr rfl
  intro p _
  have hp2 : unitModulus d0 (some p) ≠ 2 := by
    intro h2
    have h2d : 2 ∣ d0 := h2 ▸ Nat.dvd_of_mem_primeFactors p.2
    obtain ⟨k, hk⟩ := h2d
    rcases hodd with ⟨m, hm⟩
    omega
  exact card_unitSquares_prime hp2

end UnitSquares

/-! ## Uniform laws on finite sets -/

/-- The uniform probability on a nonempty finite set `S`. -/
noncomputable def uniformOn {X : Type*} [Fintype X] [DecidableEq X] (S : Finset X)
    (hS : S.Nonempty) : FiniteLaw X where
  weight x := if x ∈ S then ((S.card : ℝ))⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  total := by
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    have : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
    field_simp

theorem finiteLaw_eq_of_weight_eq {Ω : Type*} [Fintype Ω] {μ ν : FiniteLaw Ω}
    (h : ∀ ω, μ.weight ω = ν.weight ω) : μ = ν := by
  cases μ
  cases ν
  congr
  funext ω
  exact h ω

theorem uniformOn_congr {X : Type*} [Fintype X] [DecidableEq X] {S S' : Finset X}
    (hS : S.Nonempty) (hS' : S'.Nonempty) (h : S = S') : uniformOn S hS = uniformOn S' hS' := by
  subst h
  rfl

theorem uniformOn_singleton {X : Type*} [Fintype X] [DecidableEq X] (x : X) :
    uniformOn {x} (singleton_nonempty x) = FiniteLaw.point x := by
  apply finiteLaw_eq_of_weight_eq
  intro y
  simp [uniformOn, FiniteLaw.point]

/-- The uniform law is carried by a bijection to the uniform law on the image. -/
theorem uniformOn_map_equiv {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (e : X ≃ Y) (S : Finset X) (hS : S.Nonempty) :
    (uniformOn S hS).map e = uniformOn (S.map e.toEmbedding) (hS.map) := by
  apply finiteLaw_eq_of_weight_eq
  intro y
  change (∑ x, if e x = y then (uniformOn S hS).weight x else 0) = _
  simp_rw [← Equiv.eq_symm_apply]
  rw [Finset.sum_ite_eq' univ (e.symm y), ite_eq_left (mem_univ _)]
  simp only [uniformOn, mem_map_equiv, card_map]

/-- The uniform law on a product set is the product of the uniform laws. -/
theorem uniformOn_piFinset {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] (T : ∀ i, Finset (X i))
    (hT : ∀ i, (T i).Nonempty) :
    uniformOn (Fintype.piFinset T) (Fintype.piFinset_nonempty.mpr hT) =
      FiniteLaw.pi fun i => uniformOn (T i) (hT i) := by
  apply finiteLaw_eq_of_weight_eq
  intro y
  change (if y ∈ Fintype.piFinset T then (((Fintype.piFinset T).card : ℝ))⁻¹ else 0) =
    ∏ i, if y i ∈ T i then (((T i).card : ℝ))⁻¹ else 0
  rw [Finset.prod_ite_zero]
  by_cases hy : y ∈ Fintype.piFinset T
  · have hy' := Fintype.mem_piFinset.mp hy
    rw [ite_eq_left hy, ite_eq_left (fun i _ => hy' i), Fintype.card_piFinset]
    push_cast
    rw [prod_inv_distrib]
  · have hy' : ¬ ∀ i ∈ univ, y i ∈ T i :=
      fun h => hy (Fintype.mem_piFinset.mpr (fun i => h i (mem_univ i)))
    rw [ite_eq_right hy, ite_eq_right hy']

/-- `lem:func:unitsq`(ii): under the Chinese remainder isomorphism, the uniform
probability on `Q(M₀)` is the product of the uniform probabilities on the coordinate
sets: the point mass at `1` in `ZMod 8` (`uniformOn_unitSquares_eight`) and the
uniform probabilities on `Q_p`, `p ∣ d₀`. -/
theorem uniformOn_unitSquares_map {d0 : ℕ} [NeZero d0] (hodd : Odd d0) (hsf : Squarefree d0) :
    (uniformOn (unitSquares (8 * d0)) (unitSquares_nonempty _)).map
        (unitCRT d0 hodd hsf).toEquiv =
      FiniteLaw.pi fun i => uniformOn (unitSquares (unitModulus d0 i)) (unitSquares_nonempty _) := by
  rw [uniformOn_map_equiv, ← uniformOn_piFinset (fun i => unitSquares (unitModulus d0 i))
    (fun i => unitSquares_nonempty _)]
  exact uniformOn_congr _ _ (map_unitSquares_unitCRT hodd hsf)

/-- The factor at `8`: the uniform law on `Q(8)` is the point mass at `1`. -/
theorem uniformOn_unitSquares_eight :
    uniformOn (unitSquares 8) (unitSquares_nonempty 8) = FiniteLaw.point 1 := by
  have h : ∀ (S : Finset (ZMod 8)) (hS : S.Nonempty) (hS1 : S = {1}),
      uniformOn S hS = FiniteLaw.point 1 := by
    intro S hS hS1
    subst hS1
    exact uniformOn_singleton 1
  exact h _ _ unitSquares_eight

/-- The factor at `3` (when `3 ∣ d₀`): the uniform law on `Q_3` is the point mass at `1`. -/
theorem uniformOn_unitSquares_three :
    uniformOn (unitSquares 3) (unitSquares_nonempty 3) = FiniteLaw.point 1 := by
  have h : ∀ (S : Finset (ZMod 3)) (hS : S.Nonempty) (hS1 : S = {1}),
      uniformOn S hS = FiniteLaw.point 1 := by
    intro S hS hS1
    subst hS1
    exact uniformOn_singleton 1
  exact h _ _ unitSquares_three

/-- The coordinate laws of `lem:func:unitsq`(ii): the point mass at `1` in `ZMod 8` and
the uniform probability on `Q_p` at each prime `p ∣ d₀`. -/
noncomputable def unitSquareCoordLaw (d0 : ℕ) : ∀ i, FiniteLaw (ZMod (unitModulus d0 i))
  | none => FiniteLaw.point (1 : ZMod 8)
  | some p => uniformOn (unitSquares (unitModulus d0 (some p))) (unitSquares_nonempty _)

/-- `lem:func:unitsq`(ii): under the Chinese remainder isomorphism
`ZMod M₀ ≅ ZMod 8 × ∏_{p ∣ d₀} 𝔽_p`, the uniform probability on `Q(M₀)` is the product
of the point mass at `1` in `ZMod 8` and the uniform probabilities on the sets `Q_p`. -/
theorem uniformOn_unitSquares_map_coordLaw {d0 : ℕ} [NeZero d0] (hodd : Odd d0)
    (hsf : Squarefree d0) :
    (uniformOn (unitSquares (8 * d0)) (unitSquares_nonempty _)).map
        (unitCRT d0 hodd hsf).toEquiv = FiniteLaw.pi (unitSquareCoordLaw d0) := by
  have h : (fun i => uniformOn (unitSquares (unitModulus d0 i)) (unitSquares_nonempty _)) =
      unitSquareCoordLaw d0 := by
    funext i
    cases i with
    | none => exact uniformOn_unitSquares_eight
    | some p => rfl
  rw [uniformOn_unitSquares_map hodd hsf, h]

/-- If `3 ∣ d₀`, the coordinate law at `3` is the point mass at `1`. -/
theorem unitSquareCoordLaw_three {d0 : ℕ} (h3 : 3 ∈ d0.primeFactors) :
    unitSquareCoordLaw d0 (some ⟨3, h3⟩) = FiniteLaw.point 1 :=
  uniformOn_unitSquares_three

/-- `lem:func:unitsq`(ii), expectation form: for every `f`, the uniform average of
`f ∘ CRT` over `Q(M₀)` is the average of `f` under the product law. -/
theorem expect_uniformOn_unitSquares {d0 : ℕ} [NeZero d0] (hodd : Odd d0)
    (hsf : Squarefree d0) (f : (∀ i, ZMod (unitModulus d0 i)) → ℝ) :
    (uniformOn (unitSquares (8 * d0)) (unitSquares_nonempty _)).expect
        (fun r => f (unitCRT d0 hodd hsf r)) =
      (FiniteLaw.pi fun i => uniformOn (unitSquares (unitModulus d0 i))
        (unitSquares_nonempty _)).expect f := by
  rw [← uniformOn_unitSquares_map hodd hsf, FiniteLaw.expect_map]
  rfl

end Sarkozy.Functional
