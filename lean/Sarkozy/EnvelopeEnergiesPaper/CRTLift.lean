module

public import Sarkozy.Functional.Conductor

@[expose] public section

/-!
# The lift under the Chinese remainder theorem

`def:record:functional`(b),(c): the lift `𝓛_{I,N} f = ∑_{q(ξ) ≤ Q} f̂_I(ξ) e(·ξ)` on a group
`∏_j ℤ/m_jℤ` with pairwise coprime moduli depends only on the order `D = ∏_j m_j` of the group:
the characters are the `ξ ∈ D⁻¹ℤ/ℤ`, the conductor is the reduced denominator of `ξ`
(`Functional.conductor_eq_den`), and `e(nξ)` is read at the residue of `n`. This file proves it:

* `lift_integerResidue_eq`: the normal form `𝓛_{I,N} f(n mod m) = ∑_{t ∈ ℤ/D} T_D(t)`, with
  terms that depend only on `D`, through the bijection `a ↦ ∑_j a_j (D/m_j) mod D` between the
  labels and `ℤ/D` (`crtIndex_bijective`);
* **`lift_comp_eq`**: for two families of pairwise coprime moduli with the same product and any
  map `φ` of the groups that sends the residue of every integer to the residue of the same
  integer, `𝓛 f ∘ φ = 𝓛 f`. This is the transport of the lift along the Chinese remainder
  theorem, used in `BlockCRT` to read the paper's block atoms `BlockRes β ≅ ℤ/D_β` as cyclic
  coordinates.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.FourierArithmetic Sarkozy.Functional

section CRT

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The integer numerator `∑_j a_j (D/m_j)` of the frequency `ξ = ∑_j a_j/m_j` of the label `a`
over the common denominator `D`. -/
noncomputable def crtNum (D : ℕ) (a : ResidueSpace m) : ℕ := ∑ j, (a j).val * (D / m j)

/-- The label of `a` in `ℤ/D`: the class of its numerator. -/
noncomputable def crtIndex (D : ℕ) (a : ResidueSpace m) : ZMod D := (crtNum m D a : ZMod D)

omit [DecidableEq J] in
/-- `ξ_a = crtNum(a)/D` when every `m_j` divides `D`. -/
theorem frequency_eq_crtNum {D : ℕ} [NeZero D] (hdvd : ∀ j, m j ∣ D) (a : ResidueSpace m) :
    frequency m a = (crtNum m D a : ℚ) / D := by
  unfold frequency crtNum
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hm : (m j : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne (m j)
  obtain ⟨k, hk⟩ := hdvd j
  have hk' : D / m j = k := by
    rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne (m j)))]
  have hk0 : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := by
      rintro rfl
      exact NeZero.ne D (by rw [hk, mul_zero])
    exact_mod_cast this
  rw [hk', hk]
  push_cast
  field_simp

omit [DecidableEq J] in
/-- `ξ_a = t/D + q` with `t = (crtIndex a).val` and an integer `q`. -/
theorem frequency_eq_index_add {D : ℕ} [NeZero D] (hdvd : ∀ j, m j ∣ D) (a : ResidueSpace m) :
    frequency m a = ((crtIndex m D a).val : ℚ) / D + ((crtNum m D a / D : ℕ) : ℚ) := by
  rw [frequency_eq_crtNum m hdvd, crtIndex, ZMod.val_natCast]
  have hD : (D : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne D
  have h := Nat.div_add_mod (crtNum m D a) D
  conv_lhs => rw [← h]
  push_cast
  field_simp
  ring

omit [DecidableEq J] in
/-- The conductor of `a` is the reduced denominator of `t/D`, `t = crtIndex a`. -/
theorem conductor_eq_index_den (hcop : Pairwise fun i j => (m i).Coprime (m j)) {D : ℕ}
    [NeZero D] (hdvd : ∀ j, m j ∣ D) (a : ResidueSpace m) :
    conductor m a = (((crtIndex m D a).val : ℚ) / D).den := by
  rw [conductor_eq_den m hcop, frequency_eq_index_add m hdvd, Rat.add_natCast_den]

omit [DecidableEq J] [∀ j, NeZero (m j)] in
/-- The real frequency angle is the rational frequency. -/
theorem frequencyAngle_eq_frequency (a : ResidueSpace m) :
    frequencyAngle m a = ((frequency m a : ℚ) : ℝ) := by
  unfold frequencyAngle frequency
  push_cast
  rfl

omit [DecidableEq J] in
/-- `e(nξ_a) = e(n t/D)`, `t = crtIndex a`. -/
theorem prodChar_integerResidue_eq_index {D : ℕ} [NeZero D] (hdvd : ∀ j, m j ∣ D)
    (a : ResidueSpace m) (n : ℤ) :
    prodChar m a (integerResidue m n) =
      expPhase (n * (((crtIndex m D a).val : ℝ) / D)) := by
  rw [prodChar_integerResidue_eq_expPhase, frequencyAngle_eq_frequency,
    frequency_eq_index_add m hdvd]
  push_cast
  rw [mul_add, expPhase_add]
  have h : expPhase ((n : ℝ) * ((crtNum m D a / D : ℕ) : ℝ)) = 1 := by
    have h' := expPhase_int (n * ((crtNum m D a / D : ℕ) : ℤ))
    rwa [Int.cast_mul, Int.cast_natCast] at h'
  rw [h, mul_one]

omit [DecidableEq J] in
/-- The residues of the integers fill a group with pairwise coprime moduli (CRT). -/
theorem integerResidue_surjective (hcop : Pairwise fun i j => (m i).Coprime (m j)) :
    Function.Surjective (integerResidue m) := by
  intro z
  have : NeZero (∏ i, m i) := ⟨Finset.prod_ne_zero_iff.mpr fun j _ => NeZero.ne (m j)⟩
  refine ⟨(((ZMod.prodEquivPi m hcop).symm z).val : ℤ), ?_⟩
  funext j
  have hz := congrFun ((ZMod.prodEquivPi m hcop).apply_symm_apply z) j
  rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply, ZMod.cast_eq_val] at hz
  change (((((ZMod.prodEquivPi m hcop).symm z).val : ℤ)) : ZMod (m j)) = z j
  rw [Int.cast_natCast]
  exact hz

/-- **The labels are `ℤ/D`**: for pairwise coprime moduli with product `D`, `a ↦ crtIndex a` is a
bijection. -/
theorem crtIndex_bijective (hcop : Pairwise fun i j => (m i).Coprime (m j)) {D : ℕ} [NeZero D]
    (hD : ∏ j, m j = D) : Function.Bijective (crtIndex m D) := by
  have hdvd : ∀ j, m j ∣ D := fun j => by rw [← hD]; exact Finset.dvd_prod_of_mem m (mem_univ j)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => ?_, ?_⟩
  · apply frequencyAngle_separates m hcop a b
    rw [frequencyAngle_eq_frequency, frequencyAngle_eq_frequency, frequency_eq_index_add m hdvd,
      frequency_eq_index_add m hdvd, hab]
    have e : (((((crtIndex m D b).val : ℚ) / D + ((crtNum m D a / D : ℕ) : ℚ) : ℚ) : ℝ) -
        ((((crtIndex m D b).val : ℚ) / D + ((crtNum m D b / D : ℕ) : ℚ) : ℚ) : ℝ)) =
        ((((crtNum m D a / D : ℕ) : ℤ) - ((crtNum m D b / D : ℕ) : ℤ) : ℤ) : ℝ) := by
      simp only [Int.cast_sub, Int.cast_natCast, Rat.cast_add, Rat.cast_div, Rat.cast_natCast]
      ring
    rw [e, expPhase_int]
  · rw [Fintype.card_pi, ZMod.card]
    simp only [ZMod.card]
    exact hD

/-- The term of the normal form at `t ∈ ℤ/D`: the coefficient of `e(·t/D)` in `𝓛_{I,N} f`,
evaluated at the residue of `k`, when the reduced denominator of `t/D` is at most `Q`. -/
noncomputable def crtTerm (D : ℕ) [NeZero D] (Q : ℝ) (I : Finset ℤ) (f : ℤ → ℂ) (k : ℤ)
    (t : ZMod D) : ℂ :=
  if (((((t.val : ℚ) / D).den : ℕ) : ℝ) ≤ Q) then
    ((I.card : ℂ)⁻¹ * ∑ n ∈ I, f n * conj (expPhase (n * ((t.val : ℝ) / D)))) *
      expPhase (k * ((t.val : ℝ) / D))
  else 0

/-- **The normal form of the lift** (`def:record:functional`(b),(c)): for pairwise coprime moduli
with product `D`, `𝓛_{I,N} f(k mod m) = ∑_{t ∈ ℤ/D} T_D(t)`; the right side depends on the moduli
only through `D`. -/
theorem lift_integerResidue_eq (hcop : Pairwise fun i j => (m i).Coprime (m j)) {D : ℕ}
    [NeZero D] (hD : ∏ j, m j = D) (Q : ℝ) (I : Finset ℤ) (f : ℤ → ℂ) (k : ℤ) :
    Functional.lift m Q I f (integerResidue m k) = ∑ t : ZMod D, crtTerm D Q I f k t := by
  have hdvd : ∀ j, m j ∣ D := fun j => by rw [← hD]; exact Finset.dvd_prod_of_mem m (mem_univ j)
  unfold Functional.lift liftOn retained
  rw [Finset.sum_filter]
  rw [← (Equiv.ofBijective _ (crtIndex_bijective m hcop hD)).sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.ofBijective_apply, crtTerm, ← conductor_eq_index_den m hcop hdvd a]
  split_ifs
  · unfold intervalCoeff
    simp only [prodChar_integerResidue_eq_index m hdvd]
  · rfl

end CRT

/-- **The lift is invariant under the Chinese remainder theorem.** Let `m`, `m'` be families of
pairwise coprime moduli with the same product, and `φ : ∏ ℤ/m'_j → ∏ ℤ/m_i` any map sending the
residue of every integer to the residue of the same integer (for instance the CRT isomorphism of
`ZMod.prodEquivPi`, coordinate by coordinate). Then `𝓛_{I,N} f ∘ φ = 𝓛_{I,N} f`
(`def:record:functional`(b),(c)). -/
theorem lift_comp_eq {J J' : Type*} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
    (m : J → ℕ) [∀ j, NeZero (m j)] (m' : J' → ℕ) [∀ j, NeZero (m' j)]
    (hcop : Pairwise fun i j => (m i).Coprime (m j))
    (hcop' : Pairwise fun i j => (m' i).Coprime (m' j)) (hD : ∏ j, m j = ∏ j, m' j)
    (φ : ResidueSpace m' → ResidueSpace m)
    (hφ : ∀ k : ℤ, φ (integerResidue m' k) = integerResidue m k)
    (Q : ℝ) (I : Finset ℤ) (f : ℤ → ℂ) (y : ResidueSpace m') :
    Functional.lift m Q I f (φ y) = Functional.lift m' Q I f y := by
  have : NeZero (∏ j, m' j) := ⟨Finset.prod_ne_zero_iff.mpr fun j _ => NeZero.ne (m' j)⟩
  obtain ⟨k, rfl⟩ := integerResidue_surjective m' hcop' y
  rw [hφ, lift_integerResidue_eq m hcop hD, lift_integerResidue_eq m' hcop' rfl]

end Sarkozy.EnvelopeEnergiesPaper
