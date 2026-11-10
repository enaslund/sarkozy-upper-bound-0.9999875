module

public import Sarkozy.Functional.Model
public import Sarkozy.FourierArithmetic.PrefixedModel

@[expose] public section

/-!
# The paper's lift as a prefixed residue model

The paper's group `G_N = X_{𝒫_N}` splits as a fixed prefix times a tail of prime
coordinates (`e_p = 1`). The prefix moduli are arbitrary. Two choices of split
are both covered:
- `𝒫₁ | 𝒫₃ ∪ 𝒯_N`: the clique prefix with moduli `p^{e_p}`, and all
  `e_p = 1` primes in the tail;
- `𝒫₁ ∪ 𝒫₃ | 𝒯_N`: all primes below `P₄` in the fixed prefix, with moduli
  `p^{e_p}` on `𝒫₁` and `p` on `𝒫₃`. This split matches a reference law that
  is a product over the atoms, since the middle and upper block laws are not
  products over the primes of a block.

Its retained characters are those with total conductor `q(ξ) ≤ Q`; since the
conductor is multiplicative over the two factors and the conductor of a tail
character is the product of the primes of its exact support, the retained set
is exactly the project's `prefixCharacters` with the character-dependent tail
supports `{U : q(χ) ∏_{p ∈ U} p ≤ Q}` (`complexLift_prefix_eq_wholeLift`).

Consequently the paper's functional, with the prefix/tail splitting, is an
instance of `PrefixedResidueModel`, for which the Fourier-lift moment estimate
is a theorem of the project; the endgame then holds with the moment hypothesis
for the lift discharged (`paperPrefixed_powerSavingBound`). The coordinates are
indexed by `J₀ ⊕ J L` (prefix ⊕ tail); `splitEquiv` identifies the group on the
disjoint union with the product of the two groups.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate Topology

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

/-! ### The splitting of the coordinates into prefix and tail -/

section Split

variable {J₀ J : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
  (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)]

/-- The moduli on the disjoint union of prefix and tail coordinates. -/
def joinModuli : J₀ ⊕ J → ℕ := Sum.elim m₀ p

instance joinModuli_neZero : ∀ k, NeZero (joinModuli m₀ p k)
  | Sum.inl i => inferInstanceAs (NeZero (m₀ i))
  | Sum.inr j => inferInstanceAs (NeZero (p j))

/-- `∏_{J₀ ⊕ J} ZMod = (∏_{J₀} ZMod) × (∏_J ZMod)`. -/
def splitEquiv : ResidueSpace (joinModuli m₀ p) ≃+ ResidueSpace m₀ × ResidueSpace p where
  toFun z := (fun i => z (Sum.inl i), fun j => z (Sum.inr j))
  invFun w := fun k => match k with
    | Sum.inl i => w.1 i
    | Sum.inr j => w.2 j
  left_inv z := by funext k; cases k <;> rfl
  right_inv w := rfl
  map_add' z w := rfl

omit [DecidableEq J₀] [DecidableEq J] in
theorem prodChar_split (a z : ResidueSpace (joinModuli m₀ p)) :
    prodChar (joinModuli m₀ p) a z =
      prodChar m₀ (splitEquiv m₀ p a).1 (splitEquiv m₀ p z).1 *
        prodChar p (splitEquiv m₀ p a).2 (splitEquiv m₀ p z).2 := by
  unfold prodChar
  rw [Fintype.prod_sum_type]
  rfl

omit [DecidableEq J₀] [DecidableEq J] [∀ i, NeZero (m₀ i)] [∀ j, NeZero (p j)] in
theorem conductor_split (a : ResidueSpace (joinModuli m₀ p)) :
    conductor (joinModuli m₀ p) a =
      conductor m₀ (splitEquiv m₀ p a).1 * conductor p (splitEquiv m₀ p a).2 := by
  unfold conductor
  rw [Fintype.prod_sum_type]
  rfl

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
  [∀ i, NeZero (m₀ i)] [∀ j, NeZero (p j)] in
theorem splitEquiv_integerResidue (n : ℤ) :
    splitEquiv m₀ p (integerResidue (joinModuli m₀ p) n) =
      ((integerResidue m₀).prod (integerResidue p)) n := rfl

/-- At a prime coordinate the local denominator is `1` or `p`. -/
theorem addOrderOf_zmod_prime {q : ℕ} (hq : q.Prime) (x : ZMod q) :
    addOrderOf x = if x = 0 then 1 else q := by
  have : NeZero q := ⟨hq.ne_zero⟩
  split_ifs with hx
  · rw [hx, addOrderOf_zero]
  · have hd : addOrderOf x ∣ q := by
      simpa only [ZMod.card] using (addOrderOf_dvd_card (x := x))
    rcases (Nat.dvd_prime hq).mp hd with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hx
    · exact h

omit [DecidableEq J] [∀ j, NeZero (p j)] in
/-- On prime coordinates the conductor is the product of the primes of the
exact support (the paper's `q_U`). -/
theorem conductor_eq_supportDenominator (hp : ∀ j, (p j).Prime)
    (a : ResidueSpace p) [∀ j, NeZero (p j)] :
    conductor p a = supportDenominator p a := by
  unfold conductor supportDenominator primeSupport
  rw [prod_filter]
  apply prod_congr rfl
  intro j _
  rw [addOrderOf_zmod_prime (hp j)]
  by_cases h : a j = 0 <;> simp [h]

end Split

/-! ### The retained characters as prefix characters with tail supports -/

section Characters

variable {J₀ J : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
  (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)]

/-- The label of a character of the prefix group (inverse of `productCharacter`). -/
noncomputable def prefixLabel (χ : AddChar (ResidueSpace m₀) ℂ) : ResidueSpace m₀ :=
  Function.invFun (productCharacter m₀) χ

theorem prefixLabel_productCharacter (a : ResidueSpace m₀) :
    prefixLabel m₀ (productCharacter m₀ a) = a :=
  Function.leftInverse_invFun (productCharacter_injective m₀) a

/-- All characters of the prefix group. -/
noncomputable def prefixSetAll : Finset (AddChar (ResidueSpace m₀) ℂ) :=
  univ.image (productCharacter m₀)

/-- The tail supports allowed with the prefix character `χ`:
`{U : q(χ) ∏_{p ∈ U} p ≤ Q}`. -/
noncomputable def tailSupports (Q : ℝ) (χ : AddChar (ResidueSpace m₀) ℂ) : Finset (Finset J) :=
  univ.filter fun U => ((conductor m₀ (prefixLabel m₀ χ) * ∏ j ∈ U, p j : ℕ) : ℝ) ≤ Q

/-- The retained characters of `X_pre × X_tail` (total conductor `≤ Q`) are the
prefix characters with the tail supports `tailSupports`; hence the paper's lift
`F_A` is the project's prefixed `complexLift`. -/
theorem complexLift_prefix_eq_wholeLift (hp : ∀ j, (p j).Prime) (Q : ℝ) (N : ℕ)
    {A : Finset ℤ} (hA : A ⊆ Icc 1 (N : ℤ)) (z : ResidueSpace (joinModuli m₀ p)) :
    complexLift ((integerResidue m₀).prod (integerResidue p)) N A
        (prefixCharacters p (prefixSetAll m₀) (tailSupports m₀ p Q)) (splitEquiv m₀ p z) =
      wholeLift (joinModuli m₀ p) Q N A z := by
  unfold complexLift
  rw [sum_prefixCharacters, prefixSetAll,
    sum_image (fun a _ b _ h => productCharacter_injective m₀ h)]
  unfold wholeLift lift liftOn retained
  rw [sum_filter]
  rw [← (splitEquiv m₀ p).toEquiv.symm.sum_comp, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a₀ _
  rw [supportFrequencies, sum_filter]
  apply sum_congr rfl
  intro a _
  set b := (splitEquiv m₀ p).toEquiv.symm (a₀, a) with hb
  have hsplit : splitEquiv m₀ p b = (a₀, a) := (splitEquiv m₀ p).toEquiv.apply_symm_apply _
  have hmem : primeSupport p a ∈ tailSupports m₀ p Q (productCharacter m₀ a₀) ↔
      (conductor (joinModuli m₀ p) b : ℝ) ≤ Q := by
    simp only [tailSupports, mem_filter, mem_univ, true_and, prefixLabel_productCharacter]
    rw [conductor_split, hsplit]
    simp only
    rw [conductor_eq_supportDenominator p hp a, supportDenominator]
  have hcoeff : fourierCoefficient ((integerResidue m₀).prod (integerResidue p)) N A
      (prefixCharacter p (productCharacter m₀ a₀) a) =
      intervalCoeff (joinModuli m₀ p) (Icc 1 (N : ℤ)) (indicator A) b := by
    rw [fourierCoefficient, intervalCoeff, card_Icc_one, div_eq_inv_mul]
    congr 1
    simp only [indicator, ite_mul, one_mul, zero_mul]
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hA]
    apply sum_congr rfl
    intro n _
    rw [prodChar_split, hsplit, splitEquiv_integerResidue]
    rfl
  have hval : prefixCharacter p (productCharacter m₀ a₀) a (splitEquiv m₀ p z) =
      prodChar (joinModuli m₀ p) b z := by
    rw [prodChar_split, hsplit]
    rfl
  by_cases h : (conductor (joinModuli m₀ p) b : ℝ) ≤ Q
  · rw [ite_eq_left (hmem.mpr h), ite_eq_left h, hcoeff, hval]
  · rw [ite_eq_right (fun h' => h (hmem.mp h')), ite_eq_right h]

end Characters

/-! ### Transfer of the endgame hypotheses between functionals -/

section Transfer

/-- Two functionals that agree on all admissible sets satisfy the same raw
comparison hypothesis. -/
theorem rawComparison_congr {Y Y' : ℕ → Finset ℤ → ℝ}
    (h : ∀ L A, Admissible (blockScale * L) A → Y L A = Y' L A) {q : ℕ → ℝ} {E : ℝ}
    (hY : RawComparison Y q E) : RawComparison Y' q E := by
  unfold RawComparison at hY ⊢
  filter_upwards [hY] with L hL C hC hind A hA
  have hind' : ∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt Y C k := by
    intro k hk hkL B hB
    rw [h k B hB]
    exact hind k hk hkL B hB
  rw [← h L A hA]
  exact hL C hC hind' A hA

theorem globalMomentBound_congr {Y Y' : ℕ → Finset ℤ → ℝ}
    (h : ∀ L A, Admissible (blockScale * L) A → Y L A = Y' L A) {M : ℝ}
    (hY : GlobalMomentBound Y M) : GlobalMomentBound Y' M := by
  intro L hL A hA
  rw [← h L A hA]
  exact hY L hL A hA

end Transfer

/-! ### The paper's functional as a `PrefixedResidueModel` -/

section Model

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The paper's model with a prefix/tail splitting: prefix group
`X₀ = ∏_{J₀} ZMod (m₀ i)` (a fixed family, e.g. `X_{𝒫₁}` or `X_{𝒫₁ ∪ 𝒫₃}`), tail
group `∏_{J L} ZMod (p L j)` (the remaining primes of `𝒫_N`), all prefix
characters, the
tail supports `{U : q(χ) ∏_U p ≤ N^β}`, cutoff `⌊N^β⌋`, and reference laws on
`(X₀ × X_tail)^V`. -/
noncomputable def paperPrefixedModel
    (law : ∀ L, FiniteLaw (Slot → ResidueSpace m₀ × ResidueSpace (p L))) :
    PrefixedResidueModel p (ResidueSpace m₀) where
  prefixResidue := integerResidue m₀
  prefixSet := prefixSetAll m₀
  supports L := tailSupports m₀ (p L) (paperCutoff (blockScale * L))
  cutoff L := ⌊paperCutoff (blockScale * L)⌋₊
  law := law

/-- The paper's functional `Y(L, A) = Λ_{μ_N}(F_A)`, with `G_N` written as the
product `X₀ × X_tail` (`F_A` transported along `splitEquiv`). -/
noncomputable def prefixedFunctional
    (law : ∀ L, FiniteLaw (Slot → ResidueSpace m₀ × ResidueSpace (p L))) (L : ℕ)
    (A : Finset ℤ) : ℝ :=
  referenceEnergy (law L) (fun w => (wholeLift (joinModuli m₀ (p L))
    (paperCutoff (blockScale * L)) (blockScale * L) A ((splitEquiv m₀ (p L)).symm w)).re)

/-- The energy of the prefixed model is the paper's functional on `[N]`. -/
theorem paperPrefixedModel_energy (hp : ∀ L j, (p L j).Prime)
    (law : ∀ L, FiniteLaw (Slot → ResidueSpace m₀ × ResidueSpace (p L))) (L : ℕ)
    {A : Finset ℤ} (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ)) :
    (paperPrefixedModel m₀ p law).toFourierModel.energy L A = prefixedFunctional m₀ p law L A := by
  unfold FourierModel.energy prefixedFunctional
  congr 1
  funext w
  have h := complexLift_prefix_eq_wholeLift m₀ (p L) (hp L) (paperCutoff (blockScale * L))
    (blockScale * L) hA ((splitEquiv m₀ (p L)).symm w)
  rw [AddEquiv.apply_symm_apply] at h
  rw [← h]
  rfl

theorem cutoff_pow_le {N : ℕ} : ⌊paperCutoff N⌋₊ ^ 20 ≤ N := by
  have h0 : (0 : ℝ) ≤ paperCutoff N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h1 : (⌊paperCutoff N⌋₊ : ℝ) ≤ paperCutoff N := Nat.floor_le h0
  have h2 : (⌊paperCutoff N⌋₊ : ℝ) ^ 20 ≤ paperCutoff N ^ 20 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h1 20
  have h3 : paperCutoff N ^ 20 = N := by
    unfold paperCutoff liftExponent
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  rw [h3] at h2
  exact_mod_cast h2

/-- The arithmetic conditions of the prefixed residue model hold for the paper's
cutoff `⌊N^{1/20}⌋`, when the tail moduli are distinct primes. -/
theorem paperPrefixedModel_arithmetic (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (law : ∀ L, FiniteLaw (Slot → ResidueSpace m₀ × ResidueSpace (p L))) :
    (paperPrefixedModel m₀ p law).Arithmetic p (ResidueSpace m₀) := by
  intro L hL
  have hN : 1 ≤ blockScale * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by norm_num [blockScale]) (by omega))
  have hQ := one_le_paperCutoff hN
  have hc1 : 1 ≤ ⌊paperCutoff (blockScale * L)⌋₊ := Nat.one_le_floor_iff _ |>.mpr hQ
  have hc20 := cutoff_pow_le (N := blockScale * L)
  set c := ⌊paperCutoff (blockScale * L)⌋₊ with hc
  have hc2 : c ^ 2 ≤ c ^ 20 := Nat.pow_le_pow_right hc1 (by norm_num)
  have hc5 : c ^ 5 ≤ c ^ 20 := Nat.pow_le_pow_right hc1 (by norm_num)
  refine ⟨?_, hinj L, hc1, ?_, ?_, ?_⟩
  · intro i j hij
    exact (Nat.coprime_primes (hp L i) (hp L j)).mpr (fun h => hij (hinj L h))
  · intro χ _ U hU
    simp only [paperPrefixedModel, tailSupports, mem_filter, mem_univ, true_and] at hU
    apply Nat.le_floor
    have hcond := conductor_pos m₀ (prefixLabel m₀ χ)
    have : ((∏ j ∈ U, p L j : ℕ) : ℝ) ≤
        ((conductor m₀ (prefixLabel m₀ χ) * ∏ j ∈ U, p L j : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left _ hcond
    exact this.trans hU
  · change 2 * c ≤ blockScale * L + 1
    nlinarith
  · change c ^ 5 ≤ blockScale * L + 1
    omega

/-- The endgame for the paper's functional `Y` with the clique prefix and prime
tail: the Fourier-lift moment hypothesis is discharged by the project's prefixed
residue-model theorem. Remaining hypotheses: the tail moduli are distinct
primes; uniform marginals, reflection positivity and the mixed `L^36` bound of
the reference laws; the raw comparison for `Y`; the ledger. -/
theorem paperPrefixed_powerSavingBound (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (law : ∀ L, FiniteLaw (Slot → ResidueSpace m₀ × ResidueSpace (p L)))
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (law L))
    (hrp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (law L).weight))
    {l : ClosingLedger} (hledger : l.Bounds) {C E : ℝ} {q : ℕ → ℝ}
    (hC : 0 < C) (hE : 0 ≤ E)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (law L) 36 C)
    (hrec : RawComparison (prefixedFunctional m₀ p law) q E)
    (hq : Filter.Tendsto q Filter.atTop (𝓝 l.theta)) : PowerSavingBound := by
  have hprefix : (1 : AddChar (ResidueSpace m₀) ℂ) ∈ (paperPrefixedModel m₀ p law).prefixSet :=
    mem_image.mpr ⟨0, mem_univ _, productCharacter_zero m₀⟩
  have hzero : ∀ L : ℕ, 1 ≤ L → (∅ : Finset (J L)) ∈ (paperPrefixedModel m₀ p law).supports L 1 := by
    intro L hL
    have hN : 1 ≤ blockScale * L :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by norm_num [blockScale]) (by omega))
    simp only [paperPrefixedModel, tailSupports, mem_filter, mem_univ, true_and, prod_empty,
      mul_one]
    have h1 : prefixLabel m₀ 1 = 0 := by
      rw [← productCharacter_zero m₀, prefixLabel_productCharacter]
    rw [h1, conductor_zero, Nat.cast_one]
    exact one_le_paperCutoff hN
  have hrec' : RawComparison (paperPrefixedModel m₀ p law).toFourierModel.energy q E :=
    rawComparison_congr (fun L A hA => (paperPrefixedModel_energy m₀ p hp law L hA.1).symm) hrec
  exact (paperPrefixedModel m₀ p law).powerSavingBound p (ResidueSpace m₀)
    (paperPrefixedModel_arithmetic m₀ p hp hinj law) hprefix hzero hm hrp hledger hC hE hmixed
    hrec' hq

end Model

end Sarkozy.Functional
