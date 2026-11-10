module

public import Sarkozy.Functional.IndexAverages
public import Sarkozy.Functional.SquareStep

@[expose] public section

/-!
# Exact fibres and the square step (`lem:record:fibre-scale`)

`lem:record:fibre-scale` of `paper/sections/08_scale_comparison.tex`:
(a) the exact-fibre formula for the coefficients of a specialized lift,
(b) the square-step model `g̃` of a specialized input, and (d) the scale
bounds.

Setting. The coordinates are an arbitrary finite type `J` with moduli `m`;
`E : Finset J` is the set of coordinates of the selected atoms and its
complement plays the role of `𝒮` (the coordinates of the remaining atoms).
A function on `X_𝒮` is represented by a function on the whole group that
does not depend on the coordinates in `E`, and a character of `X_𝒮` by a
label `a` with `a j = 0` for `j ∈ E`; then the Fourier coefficient on `X_𝒮`
is the coefficient `groupCoeff` on the whole group. The specialization
`(𝓛_{I,N} f)(z, ·)` is `y ↦ 𝓛_{I,N} f (coordinateFreeze m E z y)`.

The fibre `x ≡ 𝔞 (mod D)` of the paper (`D = D₀ D_E`, `𝔞` the CRT class of
`s mod D₀` and of `z` on `E`) is written as the conjunction of the
congruences `x ≡ s (mod D₀)` and `x ≡ z_j (mod m_j)`, `j ∈ E`; by the Chinese
remainder theorem this is the same set of integers. The paper's `J_𝔞` is
correspondingly `{j ∈ [R] : j + c_I` lies in the fibre`}`.

Upstream: the square-step bijection follows the idea of
`OAI/Combinatorics/SquareDifference/ResidueLift.lean`
(`squareStep_padded_sum`, `fiber_squareStep_lift`, `liftPiece_frozen_complete`),
rewritten for one-based intervals, a general square step `R` (not only `D²`)
and prime-power coordinates.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

section Fibre

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The Fourier coefficient of a function on the group,
`Ĝ(ξ) = E_z G(z) e(−z·ξ)` (`def:record:functional`(b)). -/
noncomputable def groupCoeff (G : ResidueSpace m → ℂ) (a : ResidueSpace m) : ℂ :=
  𝔼 y, G y * conj (prodChar m a y)

omit [Fintype J] [∀ j, NeZero (m j)] in
/-- The part of a label on the coordinates of `E`. -/
def restrictIn (E : Finset J) (b : ResidueSpace m) : ResidueSpace m :=
  fun j => if j ∈ E then b j else 0

omit [Fintype J] [∀ j, NeZero (m j)] in
/-- The part of a label off the coordinates of `E` (a character of `X_𝒮`). -/
def restrictOut (E : Finset J) (b : ResidueSpace m) : ResidueSpace m :=
  fun j => if j ∈ E then 0 else b j

omit [Fintype J] [∀ j, NeZero (m j)] in
theorem restrictIn_add_restrictOut (E : Finset J) (b : ResidueSpace m) :
    restrictIn m E b + restrictOut m E b = b := by
  funext j
  simp only [restrictIn, restrictOut, Pi.add_apply]
  split_ifs <;> simp

/-- The character at a frozen point splits into its parts on `E` and off `E`. -/
theorem prodChar_coordinateFreeze (E : Finset J) (b z y : ResidueSpace m) :
    prodChar m b (coordinateFreeze m E z y) =
      prodChar m (restrictIn m E b) z * prodChar m (restrictOut m E b) y := by
  unfold prodChar coordinateFreeze restrictIn restrictOut
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  split_ifs <;> simp [AddChar.map_zero_eq_one]

/-- The coefficient of a specialized lift, before using completeness. -/
theorem groupCoeff_liftOn_freeze (T : Finset (ResidueSpace m)) (I : Finset ℤ) (f : ℤ → ℂ)
    (E : Finset J) (z a : ResidueSpace m) :
    groupCoeff m (fun y => liftOn m T I f (coordinateFreeze m E z y)) a =
      ∑ b ∈ T, intervalCoeff m I f b * prodChar m (restrictIn m E b) z *
        (if restrictOut m E b = a then 1 else 0) := by
  unfold groupCoeff liftOn
  simp_rw [sum_mul]
  rw [expect_sum_comm]
  apply sum_congr rfl
  intro b _
  simp_rw [prodChar_coordinateFreeze]
  have h : ∀ y, intervalCoeff m I f b * (prodChar m (restrictIn m E b) z *
      prodChar m (restrictOut m E b) y) * conj (prodChar m a y) =
      (intervalCoeff m I f b * prodChar m (restrictIn m E b) z) *
        (prodChar m (restrictOut m E b) y * conj (prodChar m a y)) := fun y => by ring
  simp_rw [h]
  rw [← mul_expect, prodChar_orthogonal]

/-- A label that agrees with `a` off `E` has conductor at most `D_E · q(a)`. -/
theorem conductor_le_of_restrictOut {E : Finset J} {a b : ResidueSpace m}
    (ha : ∀ j ∈ E, a j = 0) (hb : restrictOut m E b = a) :
    conductor m b ≤ (∏ j ∈ E, m j) * conductor m a := by
  unfold conductor
  have hterm : ∀ j, addOrderOf (b j) ≤ (if j ∈ E then m j else 1) * addOrderOf (a j) := by
    intro j
    by_cases hj : j ∈ E
    · rw [ha j hj, addOrderOf_zero, mul_one, ite_eq_left hj]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) (addOrderOf_dvd_modulus m j _)
    · have : b j = a j := by
        have h := congrFun hb j
        simpa only [restrictOut, ite_eq_right hj] using h
      rw [this, ite_eq_right hj, one_mul]
  calc
    _ ≤ ∏ j, (if j ∈ E then m j else 1) * addOrderOf (a j) :=
      prod_le_prod fun j _ => hterm j
    _ = _ := by rw [prod_mul_distrib, Fintype.prod_ite_mem]

/-- Completeness of the selected group: summing the characters of `X_E` gives
`D_E · 1_{w ≡ 0 on E}`, written over the labels that agree with `a` off `E`. -/
theorem sum_restrictOut_eq {E : Finset J} {a : ResidueSpace m} (ha : ∀ j ∈ E, a j = 0)
    (w : ResidueSpace m) :
    (∑ b : ResidueSpace m,
        if restrictOut m E b = a then prodChar m (restrictIn m E b) w else 0) =
      if ∀ j ∈ E, w j = 0 then ((∏ j ∈ E, m j : ℕ) : ℂ) else 0 := by
  have hterm : ∀ b : ResidueSpace m,
      (if restrictOut m E b = a then prodChar m (restrictIn m E b) w else 0) =
        ∏ j, (if j ∈ E then ZMod.stdAddChar (b j * w j) else if b j = a j then (1 : ℂ) else 0) := by
    intro b
    by_cases hb : restrictOut m E b = a
    · rw [ite_eq_left hb]
      unfold prodChar restrictIn
      apply prod_congr rfl
      intro j _
      by_cases hj : j ∈ E
      · simp [hj]
      · have : b j = a j := by
          have h := congrFun hb j
          simpa only [restrictOut, ite_eq_right hj] using h
        simp [hj, this, AddChar.map_zero_eq_one]
    · rw [ite_eq_right hb]
      have hex : ∃ j, j ∉ E ∧ b j ≠ a j := by
        by_contra hne
        apply hb
        funext j
        by_cases hj : j ∈ E
        · simp [restrictOut, hj, ha j hj]
        · have : b j = a j := by
            by_contra h'
            exact hne ⟨j, hj, h'⟩
          simp [restrictOut, hj, this]
      obtain ⟨j, hj, hne⟩ := hex
      symm
      apply prod_eq_zero (mem_univ j)
      simp [hj, hne]
  have hps := Fintype.prod_sum (fun (j : J) (t : ZMod (m j)) =>
    if j ∈ E then ZMod.stdAddChar (t * w j) else if t = a j then (1 : ℂ) else 0)
  rw [sum_congr rfl (fun b _ => hterm b), ← hps]
  have hfac : ∀ j, (∑ t : ZMod (m j),
      (if j ∈ E then ZMod.stdAddChar (t * w j) else if t = a j then (1 : ℂ) else 0)) =
        if j ∈ E then (if w j = 0 then (m j : ℂ) else 0) else 1 := by
    intro j
    by_cases hj : j ∈ E
    · simp only [ite_eq_left hj]
      have h := prime_char_expect m j (w j)
      rw [expect_eq_sum_div_card, card_univ, ZMod.card] at h
      have hm : (m j : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne (m j)
      simp_rw [mul_comm _ (w j)]
      rw [div_eq_iff hm] at h
      rw [h]
      split_ifs <;> simp
    · simp only [ite_eq_right hj]
      rw [sum_ite_eq']
      simp
  simp_rw [hfac]
  rw [Fintype.prod_ite_mem, prod_ite_zero]
  push_cast
  split_ifs <;> rfl

/-- `lem:record:fibre-scale`(a), exact fibre: if `q(ξ) D_E ≤ Q`, the coefficient
at the character `ξ` of `X_𝒮` of the specialization `(𝓛_{I,N} f)(z,·)` is
`(D_E/|I|) ∑_{x ∈ I, x ≡ z (D_E)} f(x) e(−xξ)`. -/
theorem groupCoeff_lift_freeze {Q : ℝ} (I : Finset ℤ) (f : ℤ → ℂ) (E : Finset J)
    (z a : ResidueSpace m) (ha : ∀ j ∈ E, a j = 0)
    (hQ : (conductor m a : ℝ) * (∏ j ∈ E, m j : ℕ) ≤ Q) :
    groupCoeff m (fun y => lift m Q I f (coordinateFreeze m E z y)) a =
      ((∏ j ∈ E, m j : ℕ) : ℂ) * (I.card : ℂ)⁻¹ *
        ∑ x ∈ I.filter (fun x => ∀ j ∈ E, (x : ZMod (m j)) = z j),
          f x * conj (prodChar m a (integerResidue m x)) := by
  unfold lift
  rw [groupCoeff_liftOn_freeze]
  -- extend the sum to all labels: every label agreeing with `a` off `E` is retained
  have hsub : ∑ b ∈ retained m Q, intervalCoeff m I f b * prodChar m (restrictIn m E b) z *
      (if restrictOut m E b = a then 1 else 0) =
      ∑ b, intervalCoeff m I f b * prodChar m (restrictIn m E b) z *
        (if restrictOut m E b = a then 1 else 0) := by
    apply sum_subset (subset_univ _)
    intro b _ hb
    have hne : restrictOut m E b ≠ a := by
      intro hb'
      apply hb
      rw [mem_retained]
      have h1 := conductor_le_of_restrictOut m ha hb'
      have h2 : ((conductor m b : ℕ) : ℝ) ≤ ((∏ j ∈ E, m j) * conductor m a : ℕ) := by
        exact_mod_cast h1
      push_cast at h2 hQ ⊢
      linarith
    rw [ite_eq_right hne, mul_zero]
  rw [hsub]
  -- expand the coefficients and exchange the sums
  have hexp : ∀ b : ResidueSpace m, intervalCoeff m I f b * prodChar m (restrictIn m E b) z *
      (if restrictOut m E b = a then 1 else 0) =
      (I.card : ℂ)⁻¹ * ∑ x ∈ I, f x * conj (prodChar m a (integerResidue m x)) *
        (if restrictOut m E b = a then
          prodChar m (restrictIn m E b) (z - integerResidue m x) else 0) := by
    intro b
    by_cases hb : restrictOut m E b = a
    · simp only [ite_eq_left hb, mul_one]
      unfold intervalCoeff
      rw [mul_assoc, sum_mul]
      congr 1
      apply sum_congr rfl
      intro x _
      have hsplit : prodChar m b (integerResidue m x) =
          prodChar m (restrictIn m E b) (integerResidue m x) * prodChar m a (integerResidue m x) := by
        conv_lhs => rw [← restrictIn_add_restrictOut m E b]
        rw [prodChar_add, hb]
      rw [hsplit, prodChar_sub_right, map_mul]
      ring
    · simp only [ite_eq_right hb, mul_zero, sum_const_zero]
  simp_rw [hexp]
  rw [← mul_sum, sum_comm]
  simp_rw [← mul_sum]
  simp_rw [sum_restrictOut_eq m ha]
  rw [sum_filter, mul_sum, mul_sum]
  apply sum_congr rfl
  intro x _
  have hiff : (∀ j ∈ E, (z - integerResidue m x) j = 0) ↔
      ∀ j ∈ E, (x : ZMod (m j)) = z j := by
    apply forall₂_congr
    intro j _
    change z j - (x : ZMod (m j)) = 0 ↔ _
    rw [sub_eq_zero, eq_comm]
  by_cases hx : ∀ j ∈ E, (x : ZMod (m j)) = z j
  · rw [ite_eq_left (hiff.mpr hx), ite_eq_left hx]
    ring
  · rw [ite_eq_right (fun h => hx (hiff.mp h)), ite_eq_right hx]
    ring

/-- The fibre condition `x ≡ 𝔞 (mod D)`, written as `x ≡ s (mod D₀)` and
`x ≡ z_j (mod m_j)` for `j ∈ E`. -/
def InFibre (E : Finset J) (z : ResidueSpace m) {D0 : ℕ} (s : ZMod D0) (x : ℤ) : Prop :=
  (x : ZMod D0) = s ∧ ∀ j ∈ E, (x : ZMod (m j)) = z j

instance (E : Finset J) (z : ResidueSpace m) {D0 : ℕ} (s : ZMod D0) :
    DecidablePred (InFibre m E z s) := fun _ => by unfold InFibre; infer_instance

/-- `lem:record:fibre-scale`(a), second formula: for `g = g^{I,D₀,s}`,
`ĝ(z,·)(ξ) = (D/|I|) ∑_{x ∈ A ∩ I, x ≡ 𝔞 (D)} e(−xξ)` with `D = D₀ D_E`. -/
theorem groupCoeff_input_freeze {Q : ℝ} (I : Finset ℤ) {D0 : ℕ} (s : ZMod D0)
    (A : Finset ℤ) (E : Finset J) (z a : ResidueSpace m) (ha : ∀ j ∈ E, a j = 0)
    (hQ : (conductor m a : ℝ) * (∏ j ∈ E, m j : ℕ) ≤ Q) :
    groupCoeff m (fun y => input m Q I D0 s A (coordinateFreeze m E z y)) a =
      ((D0 * ∏ j ∈ E, m j : ℕ) : ℂ) * (I.card : ℂ)⁻¹ *
        ∑ x ∈ (A ∩ I).filter (InFibre m E z s), conj (prodChar m a (integerResidue m x)) := by
  unfold input
  rw [groupCoeff_lift_freeze m I _ E z a ha hQ]
  rw [sum_filter, sum_filter, mul_sum, mul_sum]
  rw [← sum_subset (inter_subset_right (s₁ := A) (s₂ := I))]
  · apply sum_congr rfl
    intro x hx
    have hxA : x ∈ A := (mem_inter.mp hx).1
    unfold inputFun InFibre
    by_cases hs : (x : ZMod D0) = s
    · by_cases hz : ∀ j ∈ E, (x : ZMod (m j)) = z j
      · rw [ite_eq_left hz, ite_eq_left (show (x : ZMod D0) = s ∧ x ∈ A from ⟨hs, hxA⟩),
          ite_eq_left (show (x : ZMod D0) = s ∧ ∀ j ∈ E, (x : ZMod (m j)) = z j from ⟨hs, hz⟩)]
        push_cast
        ring
      · simp [hz]
    · simp [hs]
  · intro x hxI hx
    have hxA : x ∉ A := fun h => hx (mem_inter.mpr ⟨h, hxI⟩)
    simp [inputFun, hxA]

end Fibre

/-! ### The square step (`lem:record:fibre-scale`(b)) -/

section SquareStep

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- `J_𝔞 = {j ∈ [R] : j ≡ 𝔞 − c_I (mod D)}`: the residues `j ∈ [R]` with
`j + c_I` in the fibre. -/
def stepResidues (E : Finset J) (z : ResidueSpace m) {D0 : ℕ} (s : ZMod D0) (R : ℕ) (c : ℤ) :
    Finset ℤ :=
  (Icc 1 (R : ℤ)).filter fun j => InFibre m E z s (j + c)

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- `A'_j = {n' ∈ [n] : R n' + c_j ∈ A_I}` with `c_j = j − R` and
`A_I = (A ∩ I) − c_I`, i.e. `R n' + c_j + c_I ∈ A ∩ I`. -/
def stepChild (A I : Finset ℤ) (R n : ℕ) (c j : ℤ) : Finset ℤ :=
  (Icc 1 (n : ℤ)).filter fun n' => (R : ℤ) * n' + (j - R) + c ∈ A ∩ I

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- `T_j(y) = R⁻¹(y − c_I − c_j)`, coordinatewise; only the coordinates off
`E` matter, where `R` is a unit. -/
noncomputable def stepMap (R : ℕ) (c j : ℤ) (y : ResidueSpace m) : ResidueSpace m :=
  fun k => (R : ZMod (m k))⁻¹ * (y k - ((c + (j - R) : ℤ) : ZMod (m k)))

/-- The retained characters of `X_𝒮` with cutoff `Q'` (the paper's `n^β`). -/
noncomputable def retainedOff (E : Finset J) (Q' : ℝ) : Finset (ResidueSpace m) :=
  univ.filter fun a => (∀ i ∈ E, a i = 0) ∧ (conductor m a : ℝ) ≤ Q'

/-- `h_j = 𝓛^𝒮_{[n],Q'} 1_{A'_j}`, the lift on `X_𝒮` with cutoff `Q'`. -/
noncomputable def stepLift (E : Finset J) (Q' : ℝ) (B : Finset ℤ) (n : ℕ)
    (y : ResidueSpace m) : ℂ :=
  liftOn m (retainedOff m E Q') (Icc 1 (n : ℤ)) (indicator B) y

/-- The square-step model `g̃ = (λD/R) ∑_{j ∈ J_𝔞} h_j ∘ T_j`, with
`λ = Rn/|I|`, `|I| = M`, `D = D₀ D_E`. -/
noncomputable def squareStepModel (E : Finset J) (z : ResidueSpace m) {D0 : ℕ} (s : ZMod D0)
    (A I : Finset ℤ) (c : ℤ) (M R n : ℕ) (Q' : ℝ) (y : ResidueSpace m) : ℂ :=
  ((R * n : ℂ) / M) * ((D0 * ∏ j ∈ E, m j : ℕ) : ℂ) / R *
    ∑ j ∈ stepResidues m E z s R c, stepLift m E Q' (stepChild A I R n c j) n (stepMap m R c j y)

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- Each `A'_j` is square-difference-free: two elements of `A'_j` differing by
`k²` give two elements of `A` differing by `R k² = (r k)²`. -/
theorem stepChild_free {A : Finset ℤ} (hA : IsSquareDifferenceFree A) (I : Finset ℤ)
    {R r : ℕ} (hR : R = r ^ 2) (hr : 1 ≤ r) (n : ℕ) (c j : ℤ) :
    IsSquareDifferenceFree (stepChild A I R n c j) := by
  intro x hx y hy k hk he
  have hx' := (mem_inter.mp (mem_filter.mp hx).2).1
  have hy' := (mem_inter.mp (mem_filter.mp hy).2).1
  apply hA _ hx' _ hy' (r * k) (Nat.one_le_iff_ne_zero.mpr (by positivity))
  rw [hR]
  push_cast
  calc ((r : ℤ) ^ 2 * x + (j - (r : ℤ) ^ 2) + c) - ((r : ℤ) ^ 2 * y + (j - (r : ℤ) ^ 2) + c)
      = (r : ℤ) ^ 2 * (x - y) := by ring
    _ = _ := by rw [he]; ring

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- Each `T_j` has the form of (R3): `R⁻¹` is a square unit modulo every
coordinate modulus coprime to `R`, and `T_j(y) = R⁻¹ y + t` coordinatewise. -/
theorem stepMap_squareUnit {R r : ℕ} (hR : R = r ^ 2) (k : J) (hk : R.Coprime (m k)) :
    IsUnit ((R : ZMod (m k))⁻¹) ∧ IsSquare ((R : ZMod (m k))⁻¹) := by
  have hu : (R : ZMod (m k)) * (R : ZMod (m k))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R hk
  refine ⟨IsUnit.of_mul_eq_one_right _ hu, ?_⟩
  have hrk : r.Coprime (m k) := by
    rw [hR] at hk
    exact Nat.Coprime.coprime_dvd_left (dvd_pow_self r two_ne_zero) hk
  have hv : (r : ZMod (m k)) * (r : ZMod (m k))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one r hrk
  refine ⟨(r : ZMod (m k))⁻¹, ?_⟩
  have hR' : (R : ZMod (m k)) = (r : ZMod (m k)) * r := by rw [hR]; push_cast; ring
  calc (R : ZMod (m k))⁻¹
      = (R : ZMod (m k))⁻¹ * ((r : ZMod (m k)) * (r : ZMod (m k))⁻¹) ^ 2 := by rw [hv]; ring
    _ = (R : ZMod (m k))⁻¹ * (R : ZMod (m k)) * ((r : ZMod (m k))⁻¹ * (r : ZMod (m k))⁻¹) := by
        rw [hR']; ring
    _ = _ := by rw [mul_comm _ (R : ZMod (m k)), hu, one_mul]

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
theorem stepMap_apply (R : ℕ) (c j : ℤ) (y : ResidueSpace m) (k : J) :
    stepMap m R c j y k =
      (R : ZMod (m k))⁻¹ * y k + (-(R : ZMod (m k))⁻¹ * ((c + (j - R) : ℤ) : ZMod (m k))) := by
  simp only [stepMap]; ring

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- Translating by a multiple of `R` does not change the fibre, when `D₀ ∣ R`
and every `m_i ∣ R`, `i ∈ E`. -/
theorem inFibre_add_mul {E : Finset J} {z : ResidueSpace m} {D0 : ℕ} {s : ZMod D0} {R : ℕ}
    (hD0 : D0 ∣ R) (hE : ∀ i ∈ E, m i ∣ R) (x t : ℤ) :
    InFibre m E z s (x + R * t) ↔ InFibre m E z s x := by
  unfold InFibre
  have h0 : (R : ZMod D0) = 0 := (CharP.cast_eq_zero_iff (ZMod D0) D0 R).mpr hD0
  have hi : ∀ i ∈ E, (R : ZMod (m i)) = 0 := fun i hi =>
    (CharP.cast_eq_zero_iff (ZMod (m i)) (m i) R).mpr (hE i hi)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun i hi' => ?_⟩
    · have := h1; push_cast at this; rw [h0, zero_mul, add_zero] at this; exact this
    · have := h2 i hi'; push_cast at this; rw [hi i hi', zero_mul, add_zero] at this
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun i hi' => ?_⟩
    · push_cast; rw [h0, zero_mul, add_zero]; exact h1
    · push_cast; rw [hi i hi', zero_mul, add_zero]; exact h2 i hi'

omit [∀ j, NeZero (m j)] in
/-- The square-step bijection `(n', j) ↦ R n' + c_j + c_I`, from
`{(j, n') : j ∈ J_𝔞, n' ∈ A'_j}` onto the fibre `{x ∈ A ∩ I : x ≡ 𝔞 (D)}`
(`lem:record:fibre-scale`(b), proof). Here `I = c + [M]` and `M ≤ R n`. -/
theorem sum_stepChild {E : Finset J} {z : ResidueSpace m} {D0 : ℕ} {s : ZMod D0}
    (A : Finset ℤ) (c : ℤ) {M R n : ℕ} (hR : 1 ≤ R) (hMR : M ≤ R * n)
    (hD0 : D0 ∣ R) (hE : ∀ i ∈ E, m i ∣ R) {β : Type*} [AddCommMonoid β] (φ : ℤ → β) :
    ∑ j ∈ stepResidues m E z s R c,
        ∑ n' ∈ stepChild A (Icc (c + 1) (c + M)) R n c j, φ ((R : ℤ) * n' + (j - R) + c) =
      ∑ x ∈ (A ∩ Icc (c + 1) (c + M)).filter (InFibre m E z s), φ x := by
  rw [sum_sigma']
  have hR0 : (R : ℤ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
  have hRpos : (0 : ℤ) < R := by exact_mod_cast (show 0 < R by omega)
  apply sum_nbij' (fun p => (R : ℤ) * p.2 + (p.1 - R) + c)
    (fun x => ⟨(x - c - 1) % R + 1, (x - c - 1) / R + 1⟩)
  · intro p hp
    obtain ⟨hj, hn⟩ := mem_sigma.mp hp
    obtain ⟨hj1, hjF⟩ := mem_filter.mp hj
    obtain ⟨_, hnA⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hnA, ?_⟩
    have := (inFibre_add_mul m hD0 hE (p.1 + c) (p.2 - 1)).mpr hjF
    have e : (R : ℤ) * p.2 + (p.1 - R) + c = p.1 + c + R * (p.2 - 1) := by ring
    rw [e]
    exact this
  · intro x hx
    obtain ⟨hxAI, hxF⟩ := mem_filter.mp hx
    obtain ⟨hxA, hxI⟩ := mem_inter.mp hxAI
    obtain ⟨hx1, hx2⟩ := mem_Icc.mp hxI
    have hmod0 := Int.emod_nonneg (x - c - 1) hR0
    have hmodR := Int.emod_lt_of_pos (x - c - 1) hRpos
    have hdiv := Int.mul_ediv_add_emod (x - c - 1) (R : ℤ)
    have hq0 : 0 ≤ (x - c - 1) / (R : ℤ) := Int.ediv_nonneg (by omega) hRpos.le
    generalize hr0 : (x - c - 1) % (R : ℤ) = r0 at *
    generalize hq : (x - c - 1) / (R : ℤ) = q at *
    have hqn : q < n := by
      have h2 : x - c - 1 < (R : ℤ) * n := by
        have : (M : ℤ) ≤ (R : ℤ) * n := by exact_mod_cast hMR
        omega
      by_contra hcon
      push Not at hcon
      have : (R : ℤ) * n ≤ (R : ℤ) * q := mul_le_mul_of_nonneg_left hcon hRpos.le
      omega
    have hrecon : (R : ℤ) * (q + 1) + (r0 + 1 - R) + c = x := by
      linear_combination hdiv
    refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩, ?_⟩,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩, ?_⟩⟩
    · dsimp only
      have hx' : r0 + 1 + c + R * q = x := by linear_combination hdiv
      rw [← inFibre_add_mul m hD0 hE _ q, hx']
      exact hxF
    · simp only
      rw [hrecon]; exact hxAI
  · intro p hp
    obtain ⟨hj, hn⟩ := mem_sigma.mp hp
    obtain ⟨hj1, _⟩ := mem_filter.mp hj
    obtain ⟨hn1, _⟩ := mem_filter.mp hn
    obtain ⟨hj1a, hj1b⟩ := mem_Icc.mp hj1
    obtain ⟨hn1a, _⟩ := mem_Icc.mp hn1
    have he : (R : ℤ) * p.2 + (p.1 - R) + c - c - 1 = (p.1 - 1) + R * (p.2 - 1) := by ring
    have hm : ((R : ℤ) * p.2 + (p.1 - R) + c - c - 1) % R = p.1 - 1 := by
      rw [he, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have hd : ((R : ℤ) * p.2 + (p.1 - R) + c - c - 1) / R = p.2 - 1 := by
      rw [he, Int.add_mul_ediv_left _ _ hR0, Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      ring
    rw [hm, hd]
    simp
  · intro x hx
    have hdiv := Int.mul_ediv_add_emod (x - c - 1) (R : ℤ)
    simp only
    linear_combination hdiv
  · intro p _
    rfl

omit [∀ j, NeZero (m j)] in
/-- The fibre identity of `lem:record:fibre-scale`(b):
`∑_{j ∈ J_𝔞} |A'_j| = #{x ∈ A ∩ I : x ≡ 𝔞 (D)}`. -/
theorem sum_card_stepChild {E : Finset J} {z : ResidueSpace m} {D0 : ℕ} {s : ZMod D0}
    (A : Finset ℤ) (c : ℤ) {M R n : ℕ} (hR : 1 ≤ R) (hMR : M ≤ R * n)
    (hD0 : D0 ∣ R) (hE : ∀ i ∈ E, m i ∣ R) :
    ∑ j ∈ stepResidues m E z s R c, (stepChild A (Icc (c + 1) (c + M)) R n c j).card =
      ((A ∩ Icc (c + 1) (c + M)).filter (InFibre m E z s)).card := by
  have h := sum_stepChild m (E := E) (z := z) (s := s) A c hR hMR hD0 hE (fun _ => (1 : ℕ))
  simpa only [sum_const, smul_eq_mul, mul_one] using h

theorem card_Icc_shift (c : ℤ) (M : ℕ) : (Icc (c + 1) (c + M)).card = M := by
  rw [Int.card_Icc]
  have : c + M + 1 - (c + 1) = (M : ℤ) := by ring
  rw [this, Int.toNat_natCast]

omit [∀ j, NeZero (m j)] in
/-- `lem:record:fibre-scale`(b), density identity:
`(D/R) ∑_{j ∈ J_𝔞} α_j = α_f/λ`, with `α_j = |A'_j|/n`,
`α_f = (D/|I|) #{x ∈ A ∩ I : x ≡ 𝔞 (D)}` and `λ = Rn/|I|`. -/
theorem stepChild_density {E : Finset J} {z : ResidueSpace m} {D0 : ℕ} {s : ZMod D0}
    (A : Finset ℤ) (c : ℤ) {M R n : ℕ} (hM : 1 ≤ M) (hR : 1 ≤ R) (hMR : M ≤ R * n)
    (hD0 : D0 ∣ R) (hE : ∀ i ∈ E, m i ∣ R) :
    ((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) / R *
        ∑ j ∈ stepResidues m E z s R c,
          ((stepChild A (Icc (c + 1) (c + M)) R n c j).card : ℝ) / n =
      (((D0 * ∏ j ∈ E, m j : ℕ) : ℝ) / M *
          ((A ∩ Icc (c + 1) (c + M)).filter (InFibre m E z s)).card) /
        ((R * n : ℝ) / M) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; omega
    · exact h
  rw [← sum_div, ← Nat.cast_sum, sum_card_stepChild m A c hR hMR hD0 hE]
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

/-- Linearity of the group Fourier coefficient. -/
theorem groupCoeff_const_mul_sum {ι : Type*} (S : Finset ι) (C : ℂ)
    (G : ι → ResidueSpace m → ℂ) (a : ResidueSpace m) :
    groupCoeff m (fun y => C * ∑ i ∈ S, G i y) a = C * ∑ i ∈ S, groupCoeff m (G i) a := by
  unfold groupCoeff
  simp_rw [mul_sum, sum_mul]
  rw [expect_sum_comm]
  apply sum_congr rfl
  intro i _
  rw [mul_expect]
  apply expect_congr rfl
  intro y _
  ring

omit [DecidableEq J] in
/-- Characters at a coordinatewise product: `e((u y)·b) = e(y·(u b))`. -/
theorem prodChar_mul_right (b u y : ResidueSpace m) :
    prodChar m b (fun k => u k * y k) = prodChar m (fun k => u k * b k) y := by
  unfold prodChar
  apply prod_congr rfl
  intro k _
  ring_nf

/-- The coefficient of `h_j ∘ T_j` at a character `ξ` of `X_𝒮` with `q(ξ) ≤ Q'`:
`n⁻¹ ∑_{n' ∈ A'_j} e(−(R n' + c_j + c_I) ξ)` (proof of `lem:record:fibre-scale`(b)). -/
theorem groupCoeff_stepLift_comp {E : Finset J} {Q' : ℝ} (B : Finset ℤ) (n R : ℕ) (c j : ℤ)
    (hcop : ∀ k ∉ E, R.Coprime (m k)) (a : ResidueSpace m) (ha : ∀ i ∈ E, a i = 0)
    (haQ : (conductor m a : ℝ) ≤ Q') :
    groupCoeff m (fun y => stepLift m E Q' B n (stepMap m R c j y)) a =
      ((Icc 1 (n : ℤ)).card : ℂ)⁻¹ * ∑ n' ∈ Icc 1 (n : ℤ),
        indicator B n' * conj (prodChar m a (integerResidue m ((R : ℤ) * n' + (j - R) + c))) := by
  set rinv : ResidueSpace m := fun k => (R : ZMod (m k))⁻¹ with hrinv
  set Rv : ResidueSpace m := fun k => (R : ZMod (m k)) with hRv
  set w : ResidueSpace m := integerResidue m (c + (j - R)) with hw
  have hstep : ∀ y, stepMap m R c j y = fun k => rinv k * (y - w) k := by
    intro y; rfl
  have hRinv : ∀ k ∉ E, (R : ZMod (m k)) * (R : ZMod (m k))⁻¹ = 1 :=
    fun k hk => ZMod.coe_mul_inv_eq_one R (hcop k hk)
  -- expand the coefficient
  have hexp : groupCoeff m (fun y => stepLift m E Q' B n (stepMap m R c j y)) a =
      ∑ b ∈ retainedOff m E Q', intervalCoeff m (Icc 1 (n : ℤ)) (indicator B) b *
        conj (prodChar m (fun k => rinv k * b k) w) *
          (if (fun k => rinv k * b k) = a then 1 else 0) := by
    unfold groupCoeff stepLift liftOn
    simp_rw [sum_mul]
    rw [expect_sum_comm]
    apply sum_congr rfl
    intro b _
    simp_rw [hstep, prodChar_mul_right, prodChar_sub_right]
    have h : ∀ y, intervalCoeff m (Icc 1 (n : ℤ)) (indicator B) b *
        (prodChar m (fun k => rinv k * b k) y * conj (prodChar m (fun k => rinv k * b k) w)) *
          conj (prodChar m a y) =
        (intervalCoeff m (Icc 1 (n : ℤ)) (indicator B) b *
          conj (prodChar m (fun k => rinv k * b k) w)) *
          (prodChar m (fun k => rinv k * b k) y * conj (prodChar m a y)) := fun y => by ring
    simp_rw [h]
    rw [← mul_expect, prodChar_orthogonal]
  rw [hexp]
  -- the only contributing label is `R a`
  have hRa_mem : (fun k => Rv k * a k) ∈ retainedOff m E Q' := by
    simp only [retainedOff, mem_filter, mem_univ, true_and]
    refine ⟨fun i hi => by simp [ha i hi], ?_⟩
    have hc : conductor m (fun k => Rv k * a k) = conductor m a := by
      unfold conductor
      apply prod_congr rfl
      intro k _
      by_cases hk : k ∈ E
      · simp [ha k hk]
      · show addOrderOf (Rv k * a k) = addOrderOf (a k)
        have hu : IsUnit (Rv k) := IsUnit.of_mul_eq_one _ (hRinv k hk)
        obtain ⟨u, hu'⟩ := hu
        rw [← hu']
        exact addOrderOf_unit_mul m k u (a k)
    rw [hc]; exact haQ
  have hinv_Ra : (fun k => rinv k * (fun k => Rv k * a k) k) = a := by
    funext k
    by_cases hk : k ∈ E
    · simp [ha k hk]
    · simp only [hrinv, hRv]
      rw [← mul_assoc, mul_comm _ (R : ZMod (m k)), hRinv k hk, one_mul]
  rw [sum_eq_single (fun k => Rv k * a k)]
  · rw [hinv_Ra, ite_eq_left rfl, mul_one]
    unfold intervalCoeff
    rw [mul_assoc, sum_mul]
    congr 1
    apply sum_congr rfl
    intro x _
    have h1 : prodChar m (fun k => Rv k * a k) (integerResidue m x) =
        prodChar m a (integerResidue m ((R : ℤ) * x)) := by
      unfold prodChar
      apply prod_congr rfl
      intro k _
      simp only [hRv, integerResidue, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      push_cast
      ring_nf
    have h2 : integerResidue m ((R : ℤ) * x + (j - R) + c) =
        integerResidue m ((R : ℤ) * x) + w := by
      rw [hw, ← map_add]; ring_nf
    rw [h1, h2, prodChar_add_right, map_mul (starRingEnd ℂ)]
    ring
  · intro b hb hne
    have hne' : (fun k => rinv k * b k) ≠ a := by
      intro hba
      apply hne
      have hbE : ∀ i ∈ E, b i = 0 := by
        have := (mem_filter.mp hb).2.1
        exact this
      funext k
      by_cases hk : k ∈ E
      · simp [hbE k hk, ha k hk]
      · have hk' : rinv k * b k = a k := congrFun hba k
        show b k = Rv k * a k
        rw [← hk']
        simp only [hRv, hrinv]
        rw [← mul_assoc, hRinv k hk, one_mul]
    rw [ite_eq_right hne', mul_zero]
  · intro h
    exact absurd hRa_mem h

/-- `lem:record:fibre-scale`(b), coefficient agreement: if `q(ξ) ≤ H`,
`H ≤ Q'` (the paper's `H ≤ n^β`) and `H D_E ≤ Q`, then the square-step model
`g̃` and the specialized input `g(z,·)` have the same Fourier coefficient at
every character `ξ` of `X_𝒮`. Here `I = c + [M]`, and `R` is any positive
integer divisible by `D₀` and by the moduli of `E`, coprime to the other
moduli, with `M ≤ Rn` (all true for the paper's `R = sq(D)`,
`n = K⌈M/(KR)⌉`, see `groupCoeff_squareStepModel_sq`). -/
theorem groupCoeff_squareStepModel {Q Q' H : ℝ} {E : Finset J} {z : ResidueSpace m}
    {D0 : ℕ} {s : ZMod D0} (A : Finset ℤ) (c : ℤ) {M R n : ℕ} (hM : 1 ≤ M) (hR : 1 ≤ R)
    (hMR : M ≤ R * n) (hD0 : D0 ∣ R) (hE : ∀ i ∈ E, m i ∣ R)
    (hcop : ∀ k ∉ E, R.Coprime (m k)) (hHQ' : H ≤ Q')
    (hHQ : H * (∏ j ∈ E, m j : ℕ) ≤ Q) (a : ResidueSpace m) (ha : ∀ i ∈ E, a i = 0)
    (haH : (conductor m a : ℝ) ≤ H) :
    groupCoeff m (squareStepModel m E z s A (Icc (c + 1) (c + M)) c M R n Q') a =
      groupCoeff m
        (fun y => input m Q (Icc (c + 1) (c + M)) D0 s A (coordinateFreeze m E z y)) a := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; omega
    · exact h
  have hQa : (conductor m a : ℝ) * (∏ j ∈ E, m j : ℕ) ≤ Q := by
    have : (0 : ℝ) ≤ (∏ j ∈ E, m j : ℕ) := Nat.cast_nonneg _
    nlinarith
  rw [groupCoeff_input_freeze m _ s A E z a ha hQa, card_Icc_shift]
  unfold squareStepModel
  rw [groupCoeff_const_mul_sum]
  simp_rw [groupCoeff_stepLift_comp m _ n R c _ hcop a ha (haH.trans hHQ')]
  have hind : ∀ j, (∑ n' ∈ Icc 1 (n : ℤ),
      indicator (stepChild A (Icc (c + 1) (c + M)) R n c j) n' *
        conj (prodChar m a (integerResidue m ((R : ℤ) * n' + (j - R) + c)))) =
      ∑ n' ∈ stepChild A (Icc (c + 1) (c + M)) R n c j,
        conj (prodChar m a (integerResidue m ((R : ℤ) * n' + (j - R) + c))) := by
    intro j
    simp only [indicator, ite_mul, one_mul, zero_mul]
    rw [sum_ite_mem, inter_eq_right.mpr
      (show stepChild A (Icc (c + 1) (c + M)) R n c j ⊆ Icc 1 (n : ℤ) from filter_subset _ _)]
  simp_rw [hind, ← mul_sum]
  rw [sum_stepChild m A c hR hMR hD0 hE (fun x => conj (prodChar m a (integerResidue m x))),
    card_Icc_one]
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

/-! ### The paper's square step `R = sq(D)` and the scales (`lem:record:fibre-scale`(d)) -/

/-- `ℓ = ⌈|I|/(KR)⌉` (`lem:record:fibre-scale`(b)), with `|I| = M`. -/
def stepScale (K M R : ℕ) : ℕ := (M + K * R - 1) / (K * R)

/-- `n = Kℓ ∈ [|I|/R, |I|/R + K)`, i.e. `M ≤ Rn < M + KR`. -/
theorem stepScale_bounds {K M R : ℕ} (hK : 1 ≤ K) (hR : 1 ≤ R) :
    M ≤ R * (K * stepScale K M R) ∧ R * (K * stepScale K M R) < M + K * R := by
  unfold stepScale
  have hP : 0 < K * R := Nat.mul_pos (by omega) (by omega)
  have h1 := Nat.div_add_mod (M + K * R - 1) (K * R)
  have h2 := Nat.mod_lt (M + K * R - 1) hP
  have h3 : R * (K * ((M + K * R - 1) / (K * R))) = K * R * ((M + K * R - 1) / (K * R)) := by
    ring
  rw [h3]
  constructor <;> omega

/-- `lem:record:fibre-scale`(d): `1 ≤ λ < 1 + KR/|I|` for `λ = Rn/|I|`, and
`ℓ ≥ |I|/(KR)`, which is `L/ξ_I` with `ξ_I = (N/|I|)R` when `N = KL`. -/
theorem stepScale_lambda {K M R : ℕ} (hK : 1 ≤ K) (hR : 1 ≤ R) (hM : 1 ≤ M) :
    1 ≤ (R * (K * stepScale K M R) : ℝ) / M ∧
      (R * (K * stepScale K M R) : ℝ) / M < 1 + (K * R : ℝ) / M ∧
      (M : ℝ) / (K * R) ≤ stepScale K M R := by
  obtain ⟨h1, h2⟩ := stepScale_bounds (M := M) hK hR
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hKR : (0 : ℝ) < (K : ℝ) * R := by
    have : (0 : ℝ) < K := by exact_mod_cast hK
    have : (0 : ℝ) < R := by exact_mod_cast hR
    positivity
  have h1' : (M : ℝ) ≤ R * (K * stepScale K M R) := by exact_mod_cast h1
  have h2' : (R * (K * stepScale K M R) : ℝ) < M + K * R := by exact_mod_cast h2
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hM']; linarith
  · rw [div_lt_iff₀ hM', add_mul, one_mul, div_mul_cancel₀ _ hM'.ne']; linarith
  · rw [div_le_iff₀ hKR]; nlinarith

/-- `lem:record:fibre-scale`(d), `ℓ ≥ L/ξ_I` with `ξ_I = (N/|I|)R`, `N = KL`. -/
theorem stepScale_ge_scale {K L M R : ℕ} (hK : 1 ≤ K) (hL : 1 ≤ L) (hR : 1 ≤ R) (hM : 1 ≤ M) :
    (L : ℝ) / (((K * L : ℕ) : ℝ) / M * R) ≤ stepScale K M R := by
  have h := (stepScale_lambda hK hR hM).2.2
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have heq : (L : ℝ) / (((K * L : ℕ) : ℝ) / M * R) = (M : ℝ) / (K * R) := by
    push_cast
    field_simp
  rw [heq]; exact h

/-- `lem:record:fibre-scale`(d): `ℓ < L`, unless `D = 1` and `I = [N]`.
Here `|I| ∈ {N, L}` (`I ∈ 𝓘_L`), `R = sq(D)`, `K ≥ 2` and `L ≥ 2`; `D = 1`
means `E = ∅` and `D₀ = 1` (see `prod_eq_one_iff_empty`). -/
theorem stepScale_lt {K L M D : ℕ} (hK : 2 ≤ K) (hL : 2 ≤ L) (hD : 1 ≤ D)
    (hM : M = K * L ∨ M = L) (hne : ¬(D = 1 ∧ M = K * L)) :
    stepScale K M (leastSquare D) < L := by
  unfold stepScale
  have hRpos := leastSquare_pos D
  apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by omega) hRpos)).mpr
  have hML : M ≤ K * L := by
    rcases hM with h | h
    · omega
    · rw [h]; nlinarith
  by_cases hD1 : D = 1
  · have hML' : M = L := by
      rcases hM with h | h
      · exact absurd ⟨hD1, h⟩ hne
      · exact h
    subst hD1
    rw [leastSquare_one, hML']
    have h1 : 2 * L ≤ K * L := Nat.mul_le_mul_right L hK
    have h2 : K * 2 ≤ K * L := Nat.mul_le_mul_left K hL
    have h3 : L * (K * 1) = K * L := by ring
    omega
  · have h4 := four_le_leastSquare (show 1 < D by omega)
    set R := leastSquare D
    have h5 : R + L < R * L := by
      nlinarith [Nat.mul_le_mul (le_refl R) hL, Nat.mul_le_mul h4 (le_refl L)]
    have h6 : K * (R + L) < K * (R * L) := Nat.mul_lt_mul_of_pos_left h5 (by omega)
    have h7 : L * (K * R) = K * (R * L) := by ring
    have h8 : K * (R + L) = K * R + K * L := by ring
    omega

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- `D = D₀ D_E = 1` exactly when `D₀ = 1` and `E = ∅`, when all moduli are `≥ 2`. -/
theorem prod_eq_one_iff_empty {E : Finset J} (hm : ∀ j, 2 ≤ m j) {D0 : ℕ} :
    D0 * ∏ j ∈ E, m j = 1 ↔ D0 = 1 ∧ E = ∅ := by
  constructor
  · intro h
    have h0 := Nat.eq_one_of_mul_eq_one_right h
    have h1 := Nat.eq_one_of_mul_eq_one_left h
    refine ⟨h0, ?_⟩
    by_contra hE
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hE
    have : m j ∣ ∏ j ∈ E, m j := Finset.dvd_prod_of_mem m hj
    rw [h1] at this
    have := hm j
    have := Nat.le_of_dvd one_pos ‹m j ∣ 1›
    omega
  · rintro ⟨rfl, rfl⟩
    simp

omit [Fintype J] [DecidableEq J] in
/-- The paper's square step `R = sq(D)` satisfies the hypotheses of
`groupCoeff_squareStepModel`, when `D₀` is coprime to all coordinate moduli and
the moduli are pairwise coprime. -/
theorem leastSquare_step_conditions {E : Finset J} {D0 : ℕ} (hD0 : 1 ≤ D0)
    (hcop0 : ∀ k, D0.Coprime (m k)) (hpair : Pairwise fun i j => (m i).Coprime (m j)) :
    1 ≤ leastSquare (D0 * ∏ j ∈ E, m j) ∧
      D0 ∣ leastSquare (D0 * ∏ j ∈ E, m j) ∧
      (∀ i ∈ E, m i ∣ leastSquare (D0 * ∏ j ∈ E, m j)) ∧
      (∀ k ∉ E, (leastSquare (D0 * ∏ j ∈ E, m j)).Coprime (m k)) := by
  have hD : D0 * ∏ j ∈ E, m j ≠ 0 :=
    Nat.mul_ne_zero (by omega) (prod_ne_zero_iff.mpr fun j _ => NeZero.ne (m j))
  have hdvd := dvd_leastSquare hD
  refine ⟨leastSquare_pos _, (dvd_mul_right D0 _).trans hdvd,
    fun i hi => ((Finset.dvd_prod_of_mem m hi).trans (dvd_mul_left _ D0)).trans hdvd, ?_⟩
  intro k hk
  apply coprime_leastSquare_of_coprime
  apply Nat.Coprime.mul_left (hcop0 k)
  apply Nat.Coprime.prod_left
  intro j hj
  exact hpair (fun h => hk (h ▸ hj))

/-- `lem:record:fibre-scale`(b) with the paper's parameters: `R = sq(D)`,
`D = D₀ D_E`, `ℓ = ⌈|I|/(KR)⌉`, `n = Kℓ`; then `g̃` and `g(z,·)` have the same
coefficient at every character `ξ` of `X_𝒮` with `q(ξ) ≤ H`, if `H ≤ Q'`
(the paper's `n^β`) and `H D_E ≤ Q`. -/
theorem groupCoeff_squareStepModel_sq {Q Q' H : ℝ} {E : Finset J} {z : ResidueSpace m}
    {D0 : ℕ} {s : ZMod D0} {K : ℕ} (hK : 1 ≤ K) (hD0 : 1 ≤ D0)
    (hcop0 : ∀ k, D0.Coprime (m k)) (hpair : Pairwise fun i j => (m i).Coprime (m j))
    (A : Finset ℤ) (c : ℤ) {M : ℕ} (hM : 1 ≤ M) (hHQ' : H ≤ Q')
    (hHQ : H * (∏ j ∈ E, m j : ℕ) ≤ Q) (a : ResidueSpace m) (ha : ∀ i ∈ E, a i = 0)
    (haH : (conductor m a : ℝ) ≤ H) :
    groupCoeff m (squareStepModel m E z s A (Icc (c + 1) (c + M)) c M
        (leastSquare (D0 * ∏ j ∈ E, m j))
        (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, m j))) Q') a =
      groupCoeff m
        (fun y => input m Q (Icc (c + 1) (c + M)) D0 s A (coordinateFreeze m E z y)) a := by
  obtain ⟨hR, hdvd0, hdvdE, hcop⟩ := leastSquare_step_conditions m (E := E) hD0 hcop0 hpair
  exact groupCoeff_squareStepModel m A c hM hR (stepScale_bounds hK hR).1 hdvd0 hdvdE hcop
    hHQ' hHQ a ha haH

end SquareStep

end Sarkozy.Functional
