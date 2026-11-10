module

public import Sarkozy.CancellationSteps.OtherSlots
public import Sarkozy.PartV.Parameters

/-!
# `lem:record:density-can` for the paper's construction

`paper/sections/06_lifts_sectors.tex`, `def:record:functional`(a);
`paper/sections/18_design.tex`, `def:record:parameters`(c) and `def:construction`(a).

The data of WP-FI's `TheoremC.DensityCancellation` for the paper's construction, built from V1's
`Sarkozy.PartV.Parameters`:
* the fixed coordinates `J₀ = 𝒫₁ ∪ 𝒫₃` (`paperFixedPrimes`): the prefix primes
  (`PartV.IsPrefixPrime`, exponent `e_p = 2𝔪 = PartV.prefixExponent`) and the class-three
  primes of `[Q₃, P₄)` (`PartV.IsMiddlePrime`, `PartV.IsUpperPrime`, exponent `1`);
* the tail `𝒯_N` at the scale `L`, `N = KL` (`paperTailPrimes`): the primes `P₄ ≤ p ≤ N^β`,
  `β = 1/20` (`Functional.paperCutoff`);
* the small modulus `M₀ = ∏_q pr_q^{h_q}` over `2` (exponent `2m_ext + 1`) and the primes
  `p ≡ 3 (4)` below `Q₃` (exponent `2m_ext`), the factors of V1's `PartV.M0`
  (`prod_insert_two_subtype` is the identity for an abstract set; instantiating it at
  `PartV.smallModulusOddPrimes` makes the kernel unfold the primes below `Q₃` and time out, as
  V1 notes for `M0`);
* `P₅ = 2^{65536}` (`PartV.P5`).

Proved: the six facts that `densityCancellation_of_data` needs, and so
**`densityCancellation_paper`**, WP-FI's `DensityCancellation` for these data, with no
hypothesis. The three facts that WP-FI's `StandingData` does not record are `paper_h64`,
`paper_hcopE` and `paper_hcover`. `paper_standing_fields` checks the structural fields of
`StandingData` for the same data.

`prime_lt_P4_dispatch`: every prime below `P₄` divides `M₀` or is a fixed coordinate, and not both.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset

/-! ## The fixed coordinates `𝒫₁ ∪ 𝒫₃` -/

/-- The primes of the fixed coordinates `𝒫₁ ∪ 𝒫₃` (`def:record:functional`(a)): the primes
below `P₄` with `p ≡ 1 (4)`, or with `p ≡ 3 (4)` and `p ≥ Q₃`. -/
def paperFixedPrimes : Finset ℕ :=
  (range PartV.P4).filter fun q => q.Prime ∧ (q % 4 = 1 ∨ (q % 4 = 3 ∧ PartV.Q3 ≤ q))

/-- The fixed coordinates are V1's prefix, middle and upper primes. -/
theorem mem_paperFixedPrimes {q : ℕ} :
    q ∈ paperFixedPrimes ↔
      PartV.IsPrefixPrime q ∨ PartV.IsMiddlePrime q ∨ PartV.IsUpperPrime q := by
  unfold paperFixedPrimes PartV.IsPrefixPrime PartV.IsMiddlePrime PartV.IsUpperPrime
  rw [mem_filter, mem_range]
  have hQP : PartV.Q3 < PartV.P3 := PartV.Q3_lt_P3
  have hPP : PartV.P3 < PartV.P4 := PartV.P3_lt_P4
  constructor
  · rintro ⟨hlt, hp, h | ⟨h, hq⟩⟩
    · exact Or.inl ⟨hp, h, hlt⟩
    · by_cases h3 : q < PartV.P3
      · exact Or.inr (Or.inl ⟨hp, h, hq, h3⟩)
      · exact Or.inr (Or.inr ⟨hp, h, by omega, hlt⟩)
  · rintro (⟨hp, h, hlt⟩ | ⟨hp, h, hq, h3⟩ | ⟨hp, h, h3, hlt⟩)
    · exact ⟨hlt, hp, Or.inl h⟩
    · exact ⟨by omega, hp, Or.inr ⟨h, hq⟩⟩
    · exact ⟨hlt, hp, Or.inr ⟨h, by omega⟩⟩

/-- The index type of the fixed coordinates. -/
abbrev PaperJ0 : Type := {q // q ∈ paperFixedPrimes}

theorem paperJ0_prime (i : PaperJ0) : (i.1).Prime := (mem_filter.mp i.2).2.1

theorem paperJ0_lt_P4 (i : PaperJ0) : i.1 < PartV.P4 := mem_range.mp (mem_filter.mp i.2).1

/-- The prime of a fixed coordinate. -/
def paperPP (i : PaperJ0) : ℕ := i.1

/-- The exponent `e_p` (`def:record:functional`(a), `def:record:parameters`(c)): `2𝔪 = 16384` at
a prefix prime (`p ≡ 1 (4)`), `1` at a class-three prime. -/
def paperEP (i : PaperJ0) : ℕ := if i.1 % 4 = 1 then PartV.prefixExponent else 1

theorem one_le_paperEP (i : PaperJ0) : 1 ≤ paperEP i := by
  unfold paperEP PartV.prefixExponent PartV.digitPairs
  split_ifs <;> norm_num

/-- The modulus `p^{e_p}` of a fixed coordinate. -/
def paperM0 (i : PaperJ0) : ℕ := paperPP i ^ paperEP i

instance (i : PaperJ0) : NeZero (paperM0 i) := ⟨pow_ne_zero _ (paperJ0_prime i).ne_zero⟩

/-! ## The tail `𝒯_N` -/

/-- The tail primes at the scale `L` (`def:construction`(a), `def:record:functional`(a)):
`P₄ ≤ p ≤ N^β`, `N = KL`, `β = 1/20`. -/
noncomputable def paperTailPrimes (L : ℕ) : Finset ℕ :=
  (range (⌊Functional.paperCutoff (blockScale * L)⌋₊ + 1)).filter
    fun q => q.Prime ∧ PartV.P4 ≤ q

theorem mem_paperTailPrimes {L q : ℕ} :
    q ∈ paperTailPrimes L ↔
      q.Prime ∧ PartV.P4 ≤ q ∧ (q : ℝ) ≤ Functional.paperCutoff (blockScale * L) := by
  have h0 : 0 ≤ Functional.paperCutoff (blockScale * L) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold paperTailPrimes
  rw [mem_filter, mem_range, Nat.lt_add_one_iff, Nat.le_floor_iff h0]
  tauto

/-- The index type of the tail at the scale `L`. -/
abbrev PaperJt (L : ℕ) : Type := {q // q ∈ paperTailPrimes L}

/-- The tail prime of a tail coordinate. -/
def paperTail (L : ℕ) (j : PaperJt L) : ℕ := j.1

theorem paperTail_prime {L : ℕ} (j : PaperJt L) : (paperTail L j).Prime :=
  (mem_paperTailPrimes.mp j.2).1

instance (L : ℕ) (j : PaperJt L) : Fact (paperTail L j).Prime := ⟨paperTail_prime j⟩

instance (L : ℕ) (j : PaperJt L) : NeZero (paperTail L j) := ⟨(paperTail_prime j).ne_zero⟩

/-! ## The small modulus `M₀` -/

/-- The primes of `M₀` (`def:record:parameters`(c)): `2` and the primes `p ≡ 3 (4)` below
`Q₃`. -/
def paperSmallPrimes : Finset ℕ := insert 2 PartV.smallModulusOddPrimes

theorem mem_paperSmallPrimes {q : ℕ} : q ∈ paperSmallPrimes ↔ PartV.IsSmallModulusPrime q := by
  unfold paperSmallPrimes PartV.IsSmallModulusPrime
  rw [mem_insert, PartV.mem_smallModulusOddPrimes]
  constructor
  · rintro (rfl | ⟨hp, h, hq⟩)
    · exact ⟨Nat.prime_two, Or.inl rfl⟩
    · exact ⟨hp, Or.inr ⟨h, hq⟩⟩
  · rintro ⟨hp, rfl | ⟨h, hq⟩⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hp, h, hq⟩

/-- The index type of the primes of `M₀`. -/
abbrev PaperP : Type := {q // q ∈ paperSmallPrimes}

/-- The prime of an index of `M₀`. -/
def paperPr (q : PaperP) : ℕ := q.1

/-- The exponent of `M₀` at a prime: `2m_ext + 1 = 129` at `2`, `2m_ext = 128` otherwise. -/
def paperH (q : PaperP) : ℕ := if q.1 = 2 then 2 * PartV.mExt + 1 else 2 * PartV.mExt

theorem paperPr_prime (q : PaperP) : (paperPr q).Prime := (mem_paperSmallPrimes.mp q.2).1

theorem one_le_paperH (q : PaperP) : 1 ≤ paperH q := by
  unfold paperH PartV.mExt
  split_ifs <;> norm_num

instance (q : PaperP) : NeZero (paperPr q ^ paperH q) :=
  ⟨pow_ne_zero _ (paperPr_prime q).ne_zero⟩

/-- `∏_{q ∈ {2} ∪ s} q^{h_q} = 2^{2m+1} ∏_{q ∈ s} q^{2m}` for a set `s` not containing `2`. -/
theorem prod_insert_two_subtype (s : Finset ℕ) (hs : ∀ q ∈ s, q ≠ 2) (m : ℕ) :
    ∏ q : {q // q ∈ insert 2 s}, q.1 ^ (if q.1 = 2 then 2 * m + 1 else 2 * m) =
      2 ^ (2 * m + 1) * ∏ q ∈ s, q ^ (2 * m) := by
  refine (prod_coe_sort (insert 2 s) fun q => q ^ (if q = 2 then 2 * m + 1 else 2 * m)).trans ?_
  rw [prod_insert fun h => hs 2 h rfl]
  simp only [↓reduceIte]
  congr 1
  exact prod_congr rfl fun q hq => by simp only [hs q hq, ↓reduceIte]

/-! ## The six facts -/

/-- `P₅ ≥ 64` for `P₅ = 2^{65536}`. -/
theorem paper_h64 : 64 ≤ PartV.P5 := by
  decide +kernel

/-- **`M₀` is coprime to every coordinate modulus** (`def:record:functional`: "the small modulus is
coprime to `D_{𝒫_N}`"). -/
theorem paper_hcop0 (L : ℕ) (c : PaperJ0 ⊕ PaperJt L) :
    Nat.Coprime (IndexSupport.modulus paperPr paperH)
      (Functional.joinModuli paperM0 (paperTail L) c) := by
  apply Nat.Coprime.prod_left
  intro q _
  have hq : PartV.IsSmallModulusPrime q.1 := mem_paperSmallPrimes.mp q.2
  obtain ⟨h1, h2, h3, h4⟩ := (PartV.prime_range_disjoint q.1).1 hq
  apply Nat.Coprime.pow_left
  rcases c with i | j
  · show Nat.Coprime q.1 (i.1 ^ paperEP i)
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_primes hq.1 (paperJ0_prime i)]
    intro heq
    have hi := mem_paperFixedPrimes.mp i.2
    rw [← heq] at hi
    rcases hi with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  · show Nat.Coprime q.1 j.1
    rw [Nat.coprime_primes hq.1 (mem_paperTailPrimes.mp j.2).1]
    intro heq
    exact h4 ⟨hq.1, heq ▸ (mem_paperTailPrimes.mp j.2).2.1⟩

/-- **The coordinate moduli are pairwise coprime**: distinct fixed primes, distinct tail primes,
and every fixed prime is below `P₄`, every tail prime at least `P₄`. -/
theorem paper_hcopE (L : ℕ) (a b : PaperJ0 ⊕ PaperJt L) (hab : a ≠ b) :
    Nat.Coprime (Functional.joinModuli paperM0 (paperTail L) a)
      (Functional.joinModuli paperM0 (paperTail L) b) := by
  have hP4 : ∀ (i : PaperJ0) (j : PaperJt L), i.1 ≠ j.1 := fun i j h =>
    absurd (paperJ0_lt_P4 i) (not_lt.mpr (h ▸ (mem_paperTailPrimes.mp j.2).2.1))
  rcases a with i | j <;> rcases b with i' | j'
  · show Nat.Coprime (i.1 ^ paperEP i) (i'.1 ^ paperEP i')
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (paperJ0_prime i) (paperJ0_prime i')).mpr
      fun h => hab (congrArg Sum.inl (Subtype.ext h)))
  · show Nat.Coprime (i.1 ^ paperEP i) j'.1
    exact Nat.Coprime.pow_left _
      ((Nat.coprime_primes (paperJ0_prime i) (paperTail_prime j')).mpr (hP4 i j'))
  · show Nat.Coprime j.1 (i'.1 ^ paperEP i')
    exact Nat.Coprime.pow_right _
      ((Nat.coprime_primes (paperTail_prime j) (paperJ0_prime i')).mpr fun h => hP4 i' j h.symm)
  · show Nat.Coprime j.1 j'.1
    exact (Nat.coprime_primes (paperTail_prime j) (paperTail_prime j')).mpr
      fun h => hab (congrArg Sum.inr (Subtype.ext h))

/-- `N^{1/40} ≤ N^{1/20} = N^β`. -/
theorem rpow_fortieth_le_paperCutoff (N : ℕ) :
    (N : ℝ) ^ (1 / 40 : ℝ) ≤ Functional.paperCutoff N := by
  unfold Functional.paperCutoff Functional.liftExponent
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Nat.cast_zero, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
  · exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN) (by norm_num)

/-- **Coverage**: every prime `ℓ ≤ N^{1/40}` divides `M₀` or a fixed modulus, or is a tail prime.
By V1's `prime_range_cover`, `ℓ` is a small-modulus, prefix, middle, upper or tail prime; in the
last case `P₄ ≤ ℓ ≤ N^{1/40} ≤ N^β`, so `ℓ ∈ 𝒯_N`. -/
theorem paper_hcover (L ℓ : ℕ) (hℓ : ℓ.Prime)
    (hle : (ℓ : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ)) :
    ℓ ∣ IndexSupport.modulus paperPr paperH ∨ (∃ i, ℓ ∣ paperM0 i) ∨
      ∃ j, paperTail L j = ℓ := by
  have hfix : PartV.IsPrefixPrime ℓ ∨ PartV.IsMiddlePrime ℓ ∨ PartV.IsUpperPrime ℓ →
      ∃ i, ℓ ∣ paperM0 i := fun h =>
    ⟨⟨ℓ, mem_paperFixedPrimes.mpr h⟩,
      dvd_pow_self ℓ (Nat.one_le_iff_ne_zero.mp (one_le_paperEP _))⟩
  rcases PartV.prime_range_cover hℓ with h | h | h | h | h
  · left
    have hmem : ℓ ∈ paperSmallPrimes := mem_paperSmallPrimes.mpr h
    exact (dvd_pow_self ℓ (Nat.one_le_iff_ne_zero.mp (one_le_paperH ⟨ℓ, hmem⟩))).trans
      (dvd_prod_of_mem (fun q : PaperP => paperPr q ^ paperH q) (mem_univ (⟨ℓ, hmem⟩ : PaperP)))
  · exact Or.inr (Or.inl (hfix (Or.inl h)))
  · exact Or.inr (Or.inl (hfix (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inl (hfix (Or.inr (Or.inr h))))
  · exact Or.inr (Or.inr
      ⟨⟨ℓ, mem_paperTailPrimes.mpr ⟨hℓ, h.2, hle.trans (rpow_fortieth_le_paperCutoff _)⟩⟩, rfl⟩)

/-! ## The density cancellation for the paper's data -/

open TheoremC in
/-- **`lem:record:density-can` for the paper's construction, with no hypothesis**: WP-FI's
`DensityCancellation` for the coordinates `𝒫₁ ∪ 𝒫₃` with `e_p = 2𝔪` on `𝒫₁` and `1` on `𝒫₃`,
the tail `𝒯_N = {P₄ ≤ p ≤ N^β}`, the small modulus `M₀` of `def:record:parameters`(c)
and `P₅ = 2^{65536}`. -/
theorem densityCancellation_paper :
    DensityCancellation paperM0 paperTail paperPr paperH PartV.P5 paperPP paperEP :=
  densityCancellation_of_data paperM0 paperTail paperPr paperH PartV.P5 paperPP paperEP
    (fun _ => Subtype.val_injective) paper_h64 paper_hcop0 paper_hcopE
    (fun i => ⟨paperJ0_prime i, one_le_paperEP i, rfl⟩) paper_hcover

/-- **The structural fields of `StandingData` (`def:cp0`) hold for the paper's data**: prefix
moduli prime powers, distinct prime tail coordinates, `M₀ = ∏ pr_q^{h_q}` with distinct primes
`pr_q`, `h_2 = 129 ≥ 3`, and `M₀` coprime to every coordinate modulus. -/
theorem paper_standing_fields :
    (∀ i, (paperPP i).Prime ∧ 1 ≤ paperEP i ∧ paperM0 i = paperPP i ^ paperEP i) ∧
    (∀ L j, (paperTail L j).Prime) ∧ (∀ L, Function.Injective (paperTail L)) ∧
    (∀ q, (paperPr q).Prime) ∧ Function.Injective paperPr ∧
    (∃ q, paperPr q = 2 ∧ 3 ≤ paperH q) ∧
    (∀ L k, Nat.Coprime (IndexSupport.modulus paperPr paperH)
      (Functional.joinModuli paperM0 (paperTail L) k)) :=
  ⟨fun i => ⟨paperJ0_prime i, one_le_paperEP i, rfl⟩, fun _ j => paperTail_prime j,
    fun _ => Subtype.val_injective, paperPr_prime, Subtype.val_injective,
    ⟨⟨2, mem_insert_self _ _⟩, rfl, by unfold paperH PartV.mExt; norm_num⟩, paper_hcop0⟩

/-! ## Every prime below `P₄` is dispatched -/

/-- **Every prime below `P₄` divides `M₀` or is a fixed coordinate, and not both**
(`def:record:parameters`(c), `tab:ranges`): V1's ranges `IsSmallModulusPrime`, `IsPrefixPrime`,
`IsMiddlePrime`, `IsUpperPrime` cover the primes below `P₄`, and only the tail range reaches
`P₄`. -/
theorem prime_lt_P4_dispatch {ℓ : ℕ} (hℓ : ℓ.Prime) (hlt : ℓ < PartV.P4) :
    (ℓ ∈ paperSmallPrimes ∨ ℓ ∈ paperFixedPrimes) ∧
      ¬ (ℓ ∈ paperSmallPrimes ∧ ℓ ∈ paperFixedPrimes) := by
  rw [mem_paperSmallPrimes, mem_paperFixedPrimes]
  refine ⟨?_, ?_⟩
  · rcases PartV.prime_range_cover hℓ with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact absurd h.2 (not_le.mpr hlt)
  · rintro ⟨hs, hf⟩
    obtain ⟨h1, h2, h3, -⟩ := (PartV.prime_range_disjoint ℓ).1 hs
    rcases hf with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h

end Sarkozy.CancellationSteps
