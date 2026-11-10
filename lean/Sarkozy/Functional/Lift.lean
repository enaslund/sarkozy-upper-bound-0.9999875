module

public import Sarkozy.FourierArithmetic.CharacterBridge
public import Sarkozy.FourierSymmetry

@[expose] public section

/-!
# Characters, conductors and the lift (`def:record:functional`)

This module formalizes parts (b), (c), (e) (the lift `F_A`) and (f) (the
inputs) of `def:record:functional` (`paper/sections/06_lifts_sectors.tex`),
for an arbitrary finite product of cyclic groups `X = ∏_j ZMod (m j)` (the
existing `FourierArithmetic.ResidueSpace m`). The paper's groups
`X_S = ∏_{p ∈ S} ℤ/p^{e_p}ℤ` are the instances `m = PrimePowerFamily.modulus`,
for an arbitrary finite set `S` of primes and arbitrary exponents `e_p ≥ 1`
(prime powers such as the clique exponents `e_p = 2·8192` are included). No
specific prime set of the paper is constructed, and no assumption excluding
them is made: they are finite sets of primes.

Representation choices (each equivalent to the paper's wording):

* A character of `X` is labelled by its coordinate tuple `a`, acting by
  `z ↦ prodChar m a z = ∏_j e(a_j z_j / m_j) = e(z·ξ)`, `ξ = ∑_j a_j/m_j`.
  The paper identifies the character with `ξ ∈ ℚ/ℤ`; for an integer `n`,
  `e(nξ)` is `prodChar m a (integerResidue m n)`.
* The conductor is `∏_j addOrderOf (a j)`, the product of the local reduced
  denominators `m_j / gcd(m_j, a_j)`. For prime-power moduli this is the
  paper's formula `∏_p p^(e_p − min(v_p(a_p), e_p))` (`conductor_primePower`).
* A function `f : I → ℂ` on a finite set `I ⊆ ℤ` is a function `ℤ → ℂ` of
  which only the values on `I` are used, so the restriction `(·)|_I` is
  implicit. The definitions do not need `I` to be an interval.

The lift of `def:record:functional`(c) is `lift m Q I f`, a sum over the
retained characters `retained m Q = {a : conductor a ≤ Q}`. With the paper's
`N`, `G_N` and `Q = N^β` it is `𝓛_{I,N}`. We prove the reality of lifts of
real functions, the mean identity, and the identification of the
whole-interval lift `F_A` with the project's `Sarkozy.fourierLift`
(`ofReal_fourierLift_eq_wholeLift`), so that the existing `FourierModel`
endgame can be instantiated with the paper's lift.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

/-! ### Characters and conductors -/

section Conductor

variable {J : Type*} [Fintype J] (m : J → ℕ)

/-- The conductor `q(ξ)` of the character with coordinate tuple `a`
(`def:record:functional`(b)): the product over the coordinates of the additive
order of `a j` in `ZMod (m j)`, that is, of the local reduced denominator of
`a_j / m_j`. -/
noncomputable def conductor (a : ResidueSpace m) : ℕ := ∏ j, addOrderOf (a j)

@[simp] theorem conductor_zero : conductor m 0 = 1 := by
  simp [conductor]

theorem conductor_neg (a : ResidueSpace m) : conductor m (-a) = conductor m a := by
  simp only [conductor, Pi.neg_apply, addOrderOf_neg]

omit [Fintype J] in
/-- Multiplying a coordinate by a unit does not change its local denominator. -/
theorem addOrderOf_unit_mul (j : J) (u : (ZMod (m j))ˣ) (x : ZMod (m j)) :
    addOrderOf ((u : ZMod (m j)) * x) = addOrderOf x := by
  have hinj : Function.Injective (AddMonoidHom.mulLeft (u : ZMod (m j))) := by
    intro x y h
    simpa only [AddMonoidHom.coe_mulLeft, Units.mul_right_inj] using h
  exact addOrderOf_injective (AddMonoidHom.mulLeft (u : ZMod (m j))) hinj x

/-- Multiplication by units, coordinatewise, preserves conductors. -/
theorem conductor_unit_mul (u : ∀ j, (ZMod (m j))ˣ) (a : ResidueSpace m) :
    conductor m (fun j => (u j : ZMod (m j)) * a j) = conductor m a := by
  simp only [conductor, addOrderOf_unit_mul]

variable [∀ j, NeZero (m j)]

theorem conductor_pos (a : ResidueSpace m) : 0 < conductor m a :=
  prod_pos fun j _ => addOrderOf_pos (a j)

omit [Fintype J] in
/-- Each local denominator divides the coordinate modulus. -/
theorem addOrderOf_dvd_modulus (j : J) (x : ZMod (m j)) : addOrderOf x ∣ m j := by
  simpa only [ZMod.card] using (addOrderOf_dvd_card (x := x))

/-- The conductor divides the full order `D = ∏_j m_j` of the group. -/
theorem conductor_dvd_prod (a : ResidueSpace m) : conductor m a ∣ ∏ j, m j :=
  prod_dvd_prod_of_dvd _ _ fun j _ => addOrderOf_dvd_modulus m j (a j)

/-- For an integer `n`, `e(-nξ)` is the conjugate of `e(nξ)`. -/
theorem prodChar_integerResidue_neg (a : ResidueSpace m) (n : ℤ) :
    prodChar m a (integerResidue m (-n)) = conj (prodChar m a (integerResidue m n)) := by
  rw [map_neg, prodChar_symm, prodChar_neg, prodChar_symm]

end Conductor

/-! ### Interval coefficients, retained characters and the lift -/

section Lift

variable {J : Type*} [Fintype J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The interval Fourier coefficient `f̂_I(ξ) = |I|⁻¹ ∑_{n ∈ I} f(n) e(−nξ)`
(`def:record:functional`(c)). -/
noncomputable def intervalCoeff (I : Finset ℤ) (f : ℤ → ℂ) (a : ResidueSpace m) : ℂ :=
  (I.card : ℂ)⁻¹ * ∑ n ∈ I, f n * conj (prodChar m a (integerResidue m n))

/-- The lift on an arbitrary finite set `T` of character labels,
`z ↦ ∑_{a ∈ T} f̂_I(a) e(z·a)`. -/
noncomputable def liftOn (T : Finset (ResidueSpace m)) (I : Finset ℤ) (f : ℤ → ℂ)
    (z : ResidueSpace m) : ℂ :=
  ∑ a ∈ T, intervalCoeff m I f a * prodChar m a z

/-- The coefficient at the trivial character is the mean over `I`. -/
theorem intervalCoeff_zero (I : Finset ℤ) (f : ℤ → ℂ) :
    intervalCoeff m I f 0 = (I.card : ℂ)⁻¹ * ∑ n ∈ I, f n := by
  simp [intervalCoeff]

/-- For a real function, the coefficient at `-ξ` is the conjugate of that at `ξ`. -/
theorem intervalCoeff_neg_of_real (I : Finset ℤ) (f : ℤ → ℂ)
    (hf : ∀ n, conj (f n) = f n) (a : ResidueSpace m) :
    intervalCoeff m I f (-a) = conj (intervalCoeff m I f a) := by
  simp only [intervalCoeff, map_mul, map_inv₀, map_natCast, map_sum, hf,
    prodChar_neg, Complex.conj_conj]

/-- The complex conjugate of a lift of a real function, over a label set closed
under negation, is the lift itself. -/
theorem conj_liftOn_of_real (T : Finset (ResidueSpace m)) (hT : ∀ a ∈ T, -a ∈ T)
    (I : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ n, conj (f n) = f n) (z : ResidueSpace m) :
    conj (liftOn m T I f z) = liftOn m T I f z := by
  unfold liftOn
  rw [map_sum]
  calc
    _ = ∑ a ∈ T, intervalCoeff m I f (-a) * prodChar m (-a) z := by
      apply sum_congr rfl
      intro a _
      rw [map_mul, intervalCoeff_neg_of_real m I f hf, prodChar_neg]
    _ = _ := by
      apply sum_nbij (fun a => -a)
      · exact hT
      · intro a _ b _ h
        exact neg_injective h
      · intro b hb
        exact ⟨-b, hT b hb, neg_neg b⟩
      · intro a _
        rfl

/-- The mean of a lift is its coefficient at the trivial character. -/
theorem expect_liftOn [DecidableEq J] (T : Finset (ResidueSpace m)) (I : Finset ℤ)
    (f : ℤ → ℂ) :
    (𝔼 z, liftOn m T I f z) =
      if (0 : ResidueSpace m) ∈ T then intervalCoeff m I f 0 else 0 := by
  unfold liftOn
  rw [expect_sum_comm]
  simp_rw [← mul_expect, prodChar_expect, mul_ite, mul_one, mul_zero]
  exact sum_ite_eq' T 0 _

/-- The lift is linear in the coefficient vector, hence in the input. -/
theorem liftOn_add (T : Finset (ResidueSpace m)) (I : Finset ℤ) (f g : ℤ → ℂ)
    (z : ResidueSpace m) :
    liftOn m T I (f + g) z = liftOn m T I f z + liftOn m T I g z := by
  simp only [liftOn, intervalCoeff, Pi.add_apply, add_mul, sum_add_distrib, mul_add]

theorem liftOn_smul (T : Finset (ResidueSpace m)) (I : Finset ℤ) (c : ℂ) (f : ℤ → ℂ)
    (z : ResidueSpace m) : liftOn m T I (fun n => c * f n) z = c * liftOn m T I f z := by
  unfold liftOn intervalCoeff
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  have h : (∑ n ∈ I, c * f n * conj (prodChar m a (integerResidue m n))) =
      c * ∑ n ∈ I, f n * conj (prodChar m a (integerResidue m n)) := by
    rw [mul_sum]; exact sum_congr rfl (fun n _ => by ring)
  rw [h]; ring

variable [DecidableEq J]

/-- The retained characters `Ξ = {ξ : q(ξ) ≤ Q}` (`def:record:functional`(c));
they depend neither on the interval nor on the input. -/
noncomputable def retained (Q : ℝ) : Finset (ResidueSpace m) :=
  univ.filter fun a => (conductor m a : ℝ) ≤ Q

/-- The lift `𝓛_{I,N} f` of `def:record:functional`(c), with cutoff `Q`
(the paper's `Q = N^β`) on the group `∏_j ZMod (m j)` (the paper's `G_N`). -/
noncomputable def lift (Q : ℝ) (I : Finset ℤ) (f : ℤ → ℂ) (z : ResidueSpace m) : ℂ :=
  liftOn m (retained m Q) I f z

theorem mem_retained {Q : ℝ} {a : ResidueSpace m} :
    a ∈ retained m Q ↔ (conductor m a : ℝ) ≤ Q := by
  simp [retained]

theorem zero_mem_retained {Q : ℝ} (hQ : 1 ≤ Q) : (0 : ResidueSpace m) ∈ retained m Q := by
  simpa [mem_retained] using hQ

/-- `def:record:functional`(c): the retained set is closed under negation. -/
theorem neg_mem_retained {Q : ℝ} {a : ResidueSpace m} (ha : a ∈ retained m Q) :
    -a ∈ retained m Q := by
  rw [mem_retained, conductor_neg]
  exact (mem_retained m).mp ha

/-- `def:record:functional`(c): the lift of a real function is real. -/
theorem conj_lift_of_real (Q : ℝ) (I : Finset ℤ) (f : ℤ → ℂ)
    (hf : ∀ n, conj (f n) = f n) (z : ResidueSpace m) :
    conj (lift m Q I f z) = lift m Q I f z :=
  conj_liftOn_of_real m _ (fun _ ha => neg_mem_retained m ha) I f hf z

theorem lift_im_eq_zero_of_real (Q : ℝ) (I : Finset ℤ) (f : ℤ → ℂ)
    (hf : ∀ n, conj (f n) = f n) (z : ResidueSpace m) : (lift m Q I f z).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_lift_of_real m Q I f hf z)

theorem ofReal_re_lift_of_real (Q : ℝ) (I : Finset ℤ) (f : ℤ → ℂ)
    (hf : ∀ n, conj (f n) = f n) (z : ResidueSpace m) :
    ((lift m Q I f z).re : ℂ) = lift m Q I f z :=
  Complex.conj_eq_iff_re.mp (conj_lift_of_real m Q I f hf z)

/-- The mean identity (`def:record:functional`, "Support components"):
`E_z 𝓛_{I,N} f(z) = f̂_I(0) = E_I f`, since `q(0) = 1 ≤ Q`. -/
theorem expect_lift {Q : ℝ} (hQ : 1 ≤ Q) (I : Finset ℤ) (f : ℤ → ℂ) :
    (𝔼 z, lift m Q I f z) = (I.card : ℂ)⁻¹ * ∑ n ∈ I, f n := by
  unfold lift
  rw [expect_liftOn, ite_eq_left (zero_mem_retained m hQ), intervalCoeff_zero]

/-! ### Indicators, the whole-interval lift and the inputs -/

/-- The indicator `1_A`. -/
noncomputable def indicator (A : Finset ℤ) (n : ℤ) : ℂ := if n ∈ A then 1 else 0

/-- The input function `D₀ · 1_{n ≡ s (mod D₀)} · 1_A(n)` of
`def:record:functional`(f). -/
noncomputable def inputFun (D0 : ℕ) (s : ZMod D0) (A : Finset ℤ) (n : ℤ) : ℂ :=
  if (n : ZMod D0) = s ∧ n ∈ A then (D0 : ℂ) else 0

/-- `F_A = 𝓛_{[N],N} 1_A` (`def:record:functional`(e)), `[N] = {1, …, N}`. -/
noncomputable def wholeLift (Q : ℝ) (N : ℕ) (A : Finset ℤ) (z : ResidueSpace m) : ℂ :=
  lift m Q (Icc 1 (N : ℤ)) (indicator A) z

/-- The inputs `g^{I,D₀,s} = 𝓛_{I,N}((D₀ 1_{n≡s (D₀)} 1_A)|_I)` of
`def:record:functional`(f). -/
noncomputable def input (Q : ℝ) (I : Finset ℤ) (D0 : ℕ) (s : ZMod D0) (A : Finset ℤ)
    (z : ResidueSpace m) : ℂ :=
  lift m Q I (inputFun D0 s A) z

theorem conj_indicator (A : Finset ℤ) (n : ℤ) : conj (indicator A n) = indicator A n := by
  unfold indicator; split_ifs <;> simp

theorem conj_inputFun (D0 : ℕ) (s : ZMod D0) (A : Finset ℤ) (n : ℤ) :
    conj (inputFun D0 s A n) = inputFun D0 s A n := by
  unfold inputFun; split_ifs <;> simp

/-- The lift `F_A` is real. -/
theorem wholeLift_real (Q : ℝ) (N : ℕ) (A : Finset ℤ) (z : ResidueSpace m) :
    ((wholeLift m Q N A z).re : ℂ) = wholeLift m Q N A z :=
  ofReal_re_lift_of_real m Q _ _ (conj_indicator A) z

/-- The inputs `g^{I,D₀,s}` are real. -/
theorem input_real (Q : ℝ) (I : Finset ℤ) (D0 : ℕ) (s : ZMod D0) (A : Finset ℤ)
    (z : ResidueSpace m) :
    ((input m Q I D0 s A z).re : ℂ) = input m Q I D0 s A z :=
  ofReal_re_lift_of_real m Q _ _ (conj_inputFun D0 s A) z

/-- The mean of `F_A` is the density `|A|/N` (for `A ⊆ [N]`). -/
theorem expect_wholeLift {Q : ℝ} (hQ : 1 ≤ Q) (N : ℕ) {A : Finset ℤ}
    (hA : A ⊆ Icc 1 (N : ℤ)) :
    (𝔼 z, wholeLift m Q N A z) = (density N A : ℂ) := by
  unfold wholeLift
  rw [expect_lift m hQ]
  have hs : (∑ n ∈ Icc 1 (N : ℤ), indicator A n) = (A.card : ℂ) := by
    simp only [indicator]
    rw [sum_ite_mem, inter_eq_right.mpr hA]
    simp
  rw [hs, density]
  simp [div_eq_inv_mul]

/-! ### Identification with the project's `fourierLift` -/

/-- The retained characters as a set of additive characters. -/
noncomputable def retainedCharacters (Q : ℝ) : Finset (AddChar (ResidueSpace m) ℂ) :=
  (retained m Q).image (productCharacter m)

theorem retainedCharacters_one {Q : ℝ} (hQ : 1 ≤ Q) :
    (1 : AddChar (ResidueSpace m) ℂ) ∈ retainedCharacters m Q :=
  mem_image.mpr ⟨0, zero_mem_retained m hQ, productCharacter_zero m⟩

theorem retainedCharacters_inv (Q : ℝ) :
    ∀ χ ∈ retainedCharacters m Q, χ⁻¹ ∈ retainedCharacters m Q := by
  intro χ hχ
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hχ
  exact mem_image.mpr ⟨-a, neg_mem_retained m ha, productCharacter_neg m a⟩

theorem card_Icc_one (N : ℕ) : (Icc 1 (N : ℤ)).card = N := by
  simp

omit [DecidableEq J] in
/-- For `A ⊆ [N]` the coefficient of `F_A` is the project's `fourierCoefficient`. -/
theorem fourierCoefficient_eq_intervalCoeff (N : ℕ) {A : Finset ℤ}
    (hA : A ⊆ Icc 1 (N : ℤ)) (a : ResidueSpace m) :
    fourierCoefficient (integerResidue m) N A (productCharacter m a) =
      intervalCoeff m (Icc 1 (N : ℤ)) (indicator A) a := by
  rw [fourierCoefficient, intervalCoeff, card_Icc_one, div_eq_inv_mul]
  congr 1
  simp only [indicator, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hA]
  rfl

/-- The whole-interval lift `F_A` is the project's `complexLift` for the
natural residue map and the retained characters. -/
theorem complexLift_eq_wholeLift (Q : ℝ) (N : ℕ) {A : Finset ℤ}
    (hA : A ⊆ Icc 1 (N : ℤ)) (z : ResidueSpace m) :
    complexLift (integerResidue m) N A (retainedCharacters m Q) z = wholeLift m Q N A z := by
  rw [complexLift, retainedCharacters,
    sum_image (fun a _ b _ h => productCharacter_injective m h)]
  apply sum_congr rfl
  intro a _
  rw [fourierCoefficient_eq_intervalCoeff m N hA]
  rfl

/-- The project's real `fourierLift` (as used by `FourierModel.energy`) with
`ρ = integerResidue m` and the retained characters is exactly `F_A`. -/
theorem ofReal_fourierLift_eq_wholeLift (Q : ℝ) (N : ℕ) {A : Finset ℤ}
    (hA : A ⊆ Icc 1 (N : ℤ)) (z : ResidueSpace m) :
    (fourierLift (integerResidue m) N A (retainedCharacters m Q) z : ℂ) =
      wholeLift m Q N A z := by
  rw [ofReal_fourierLift _ _ _ _ (retainedCharacters_inv m Q), complexLift_eq_wholeLift m Q N hA]

theorem fourierLift_eq_re_wholeLift (Q : ℝ) (N : ℕ) {A : Finset ℤ}
    (hA : A ⊆ Icc 1 (N : ℤ)) (z : ResidueSpace m) :
    fourierLift (integerResidue m) N A (retainedCharacters m Q) z = (wholeLift m Q N A z).re := by
  rw [fourierLift, complexLift_eq_wholeLift m Q N hA]

end Lift

/-! ### Prime-power coordinates: the groups `X_S` of `def:record:functional` -/

/-- A finite set `S` of primes with exponents `e_p ≥ 1` (`def:record:functional`):
the coordinates of `X_S = ∏_{p ∈ S} ℤ/p^{e_p}ℤ`. Any finite set of primes is
allowed, e.g. the paper's `𝒫_N = 𝒫₁ ∪ 𝒫₃ ∪ 𝒯_N` with `e_p = 2 m_p` on `𝒫₁`. -/
structure PrimePowerFamily where
  primes : Finset ℕ
  exponent : ℕ → ℕ
  prime : ∀ p ∈ primes, p.Prime
  exponent_pos : ∀ p ∈ primes, 1 ≤ exponent p

namespace PrimePowerFamily

variable (F : PrimePowerFamily)

/-- The coordinate moduli `p^{e_p}`, `p ∈ S`. -/
def modulus (j : F.primes) : ℕ := (j : ℕ) ^ F.exponent j

theorem modulus_def (j : F.primes) : F.modulus j = (j : ℕ) ^ F.exponent j := rfl

theorem prime_coe (j : F.primes) : (j : ℕ).Prime := F.prime j j.2

instance (j : F.primes) : NeZero (F.modulus j) :=
  ⟨pow_ne_zero _ (F.prime_coe j).ne_zero⟩

/-- The group `X_S`. -/
abbrev Group : Type := ResidueSpace F.modulus

theorem two_le_modulus (j : F.primes) : 2 ≤ F.modulus j := by
  have hp := (F.prime_coe j).two_le
  have he := F.exponent_pos j j.2
  calc 2 ≤ (j : ℕ) := hp
    _ = (j : ℕ) ^ 1 := (pow_one _).symm
    _ ≤ (j : ℕ) ^ F.exponent j := Nat.pow_le_pow_right (by omega) he

/-- Distinct primes give coprime coordinate moduli. -/
theorem modulus_coprime : Pairwise fun i j => (F.modulus i).Coprime (F.modulus j) := by
  intro i j hij
  have hne : (i : ℕ) ≠ j := fun h => hij (Subtype.ext h)
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (F.prime_coe i) (F.prime_coe j)).mpr hne)

theorem modulus_injective : Function.Injective F.modulus := by
  intro i j h
  by_contra hij
  have hc : (F.modulus i).Coprime (F.modulus j) := F.modulus_coprime hij
  rw [h, Nat.coprime_self] at hc
  have := F.two_le_modulus j
  omega

/-- The full order `D_S = |X_S| = ∏_{p ∈ S} p^{e_p}`. -/
theorem card_group : Fintype.card F.Group = ∏ p ∈ F.primes, p ^ F.exponent p := by
  rw [Fintype.card_pi, ← prod_coe_sort F.primes]
  exact prod_congr rfl fun j _ => ZMod.card _

/-- `min(v_p(x), e_p)` for `x ∈ ℤ/p^{e_p}ℤ` represented in `[0, p^{e_p})`, with
the paper's convention `v_p(0) = +∞`. -/
noncomputable def depth (j : F.primes) (x : ZMod (F.modulus j)) : ℕ :=
  if x = 0 then F.exponent j else min (padicValNat j x.val) (F.exponent j)

theorem depth_le (j : F.primes) (x : ZMod (F.modulus j)) : F.depth j x ≤ F.exponent j := by
  unfold depth; split_ifs <;> omega

/-- The local reduced denominator at a prime-power coordinate. -/
theorem addOrderOf_eq (j : F.primes) (x : ZMod (F.modulus j)) :
    addOrderOf x = (j : ℕ) ^ (F.exponent j - F.depth j x) := by
  have hp := F.prime_coe j
  have := Fact.mk hp
  have hn : F.modulus j ≠ 0 := NeZero.ne _
  by_cases hx : x = 0
  · subst hx
    simp [depth]
  · have h1 : addOrderOf x = F.modulus j / (F.modulus j).gcd x.val := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      exact ZMod.addOrderOf_coe _ hn
    rw [h1]
    have hv : x.val ≠ 0 := (ZMod.val_ne_zero x).mpr hx
    obtain ⟨k, hk, hg⟩ := (Nat.dvd_prime_pow hp).mp
      (Nat.gcd_dvd_left (F.modulus j) x.val)
    have hk' : k = min (padicValNat j x.val) (F.exponent j) := by
      apply le_antisymm
      · apply le_min _ hk
        apply (padicValNat_dvd_iff_le hv).mp
        rw [← hg]
        exact Nat.gcd_dvd_right _ _
      · have hdvd : (j : ℕ) ^ min (padicValNat j x.val) (F.exponent j) ∣ (j : ℕ) ^ k := by
          rw [← hg]
          apply Nat.dvd_gcd
          · exact Nat.pow_dvd_pow _ (min_le_right _ _)
          · exact (Nat.pow_dvd_pow _ (min_le_left _ _)).trans pow_padicValNat_dvd
        exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
    rw [hg, modulus_def, Nat.pow_div hk hp.pos, depth, ite_eq_right hx, hk']

/-- `def:record:functional`(b): the conductor on `X_S` is
`q(ξ) = ∏_{p ∈ S} p^{e_p − min(v_p(a_p), e_p)}`. -/
theorem conductor_primePower (a : F.Group) :
    conductor F.modulus a = ∏ j : F.primes, (j : ℕ) ^ (F.exponent j - F.depth j (a j)) := by
  unfold conductor
  exact prod_congr rfl fun j _ => F.addOrderOf_eq j (a j)

end PrimePowerFamily

end Sarkozy.Functional
