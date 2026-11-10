module

public import Sarkozy.Functional.Averaging
public import Sarkozy.Functional.PrefixModel

@[expose] public section

/-!
# Restoration of the square-step pieces (`lem:record:fibre-scale`(c))

`lem:record:fibre-scale`(c) states `Z_𝒮(h_j) ≤ Y(ℓ, A'_j)`. Its proof has three
steps:
1. `h_j` is the average `E_{E'} u_j` of the full lift `u_j` over the
   coordinates of `E'` (`Averaging.expect_lift_freeze`);
2. averaging over atoms does not increase `Z` (`lem:record:holder`(d));
3. Fubini for the product of atom laws, and the identification of the atom laws
   at the scales `ℓ` and `L` by (R1).

This module proves step 2 for the paper's energies and combines it with step 1.
- `referenceEnergy_average_le`: for a law that is reflection positive at the
  sorting cuts, a convex combination of functions of equal energy has at most
  that energy. The proof is multilinear expansion plus the signed Hölder
  inequality `slot_signed_holder`.
- `referenceEnergy_translate`: under a law invariant under a simultaneous
  translation of all slots (the case `r_p = 1` of (R3)), translates have equal
  energy.
- `referenceEnergy_stepLift_le`: `Z_μ(h_j) ≤ Z_μ(u_j)`, where `u_j` is the
  lift of `1_{A'_j}` with the same cutoff on all coordinates. This is
  `Z(E_{E'} u_j) ≤ Z(u_j)`.
- `referenceEnergy_comp_fst`: Fubini for a product law. A function of the
  first factor has the energy of the first factor's law.

Not formalized here is the two-scale bookkeeping: identifying the coordinates of
`G_n` (scale `ℓ`) with a factor of `G_N`, and the atom laws at the two scales.
With it, `Z_{μ_N}(u_j) = Y(ℓ, A'_j)` follows from `referenceEnergy_comp_fst`.
The paper's `lem:record:holder`(d) is also proved, in a general seminorm
form, in another worker's `Sarkozy/Reflection/Seminorm.lean`. The direct proof
here avoids depending on it.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

/-- `lem:record:holder`(d), the averaging step: under a law reflection positive
at the sorting cuts, a convex combination of functions of equal energy `M` has
energy at most `M`. -/
theorem referenceEnergy_average_le {X : Type*} [Fintype X] (μ : FiniteLaw (Slot → X))
    (hp : SlotReflectionPositive (signedIntegral μ.weight)) {T : Type*} [Fintype T]
    [DecidableEq T] (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) (hsum : ∑ t, w t = 1) (g : T → X → ℝ)
    {M : ℝ} (hM : ∀ t, referenceEnergy μ (g t) = M) :
    referenceEnergy μ (fun x => ∑ t, w t * g t x) ≤ M := by
  set L := signedIntegral μ.weight
  have hM0 : 0 ≤ M := by
    by_cases hT : Nonempty T
    · obtain ⟨t⟩ := hT
      rw [← hM t]
      exact referenceEnergy_nonneg μ hp (g t)
    · have : ∑ t, w t = 0 := by
        rw [not_nonempty_iff] at hT
        simp
      linarith
  -- multilinear expansion
  have hexp : referenceEnergy μ (fun x => ∑ t, w t * g t x) =
      ∑ τ : Slot → T, (∏ v, w (τ v)) * multilinearIntegral L (fun v => g (τ v)) := by
    rw [referenceEnergy_eq_diagonal]
    unfold diagonalIntegral multilinearIntegral
    have hz : (fun z : Slot → X => ∏ v, ∑ t, w t * g t (z v)) =
        ∑ τ : Slot → T, (∏ v, w (τ v)) • (fun z : Slot → X => ∏ v, g (τ v) (z v)) := by
      funext z
      rw [Fintype.prod_sum (fun v t => w t * g t (z v)), Finset.sum_apply]
      apply sum_congr rfl
      intro τ _
      simp only [Pi.smul_apply, smul_eq_mul, prod_mul_distrib]
    rw [hz, map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  rw [hexp]
  have hbound : ∀ τ : Slot → T, multilinearIntegral L (fun v => g (τ v)) ≤ M := by
    intro τ
    refine (le_abs_self _).trans ((slot_signed_holder hp _).trans_eq ?_)
    have he : ∀ v, diagonalIntegral L (g (τ v)) = M := fun v => by
      rw [← referenceEnergy_eq_diagonal]; exact hM (τ v)
    simp only [he, prod_const, card_univ, card_slot]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0]
    norm_num
  calc
    ∑ τ : Slot → T, (∏ v, w (τ v)) * multilinearIntegral L (fun v => g (τ v))
        ≤ ∑ τ : Slot → T, (∏ v, w (τ v)) * M := by
          apply sum_le_sum
          intro τ _
          exact mul_le_mul_of_nonneg_left (hbound τ) (prod_nonneg fun v _ => hw (τ v))
    _ = M := by
      rw [← sum_mul]
      have h1 : ∑ τ : Slot → T, ∏ v, w (τ v) = ∏ _v : Slot, ∑ t, w t :=
        (Fintype.prod_sum (fun _ t => w t)).symm
      rw [h1, hsum, prod_const_one, one_mul]

/-- Translates have equal energy under a law invariant under the simultaneous
translation of all slots by `s` (the case `r_p = 1` of (R3)). -/
theorem referenceEnergy_translate {G : Type*} [AddCommGroup G] [Fintype G]
    (μ : FiniteLaw (Slot → G)) (s : G)
    (hinv : ∀ F : (Slot → G) → ℝ, μ.expect (fun z => F (fun v => z v + s)) = μ.expect F)
    (u : G → ℝ) : referenceEnergy μ (fun y => u (y + s)) = referenceEnergy μ u :=
  hinv (fun z => ∏ v, u (z v))

/-- Fubini for a product law: a function of the first factor has the energy of
the first factor's law (`lem:record:holder`(d), second sentence). -/
theorem referenceEnergy_comp_fst {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (μa : FiniteLaw (Slot → X)) (μb : FiniteLaw (Slot → Y)) (f : X → ℝ) :
    referenceEnergy ((μa.product μb).map (fun p => fun v => (p.1 v, p.2 v)))
        (fun x => f x.1) = referenceEnergy μa f := by
  unfold referenceEnergy
  rw [FiniteLaw.expect_map, FiniteLaw.expect_product]
  simp only [Function.comp, FiniteLaw.expect_const]

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

omit [Fintype J] [∀ j, NeZero (m j)] in
/-- Freezing at a translated point is a translation by the part on `W`. -/
theorem coordinateFreeze_add (W : Finset J) (t y : ResidueSpace m) :
    coordinateFreeze m W (t + y) y = y + restrictIn m W t := by
  funext j
  simp only [coordinateFreeze, restrictIn, Pi.add_apply]
  split_ifs <;> simp [add_comm]

/-- The average over the coordinates of `W` is an average of translates by
elements supported on `W`. -/
theorem expect_freeze_eq_translates (W : Finset J) (u : ResidueSpace m → ℂ)
    (y : ResidueSpace m) :
    (𝔼 t, u (coordinateFreeze m W t y)) = 𝔼 t, u (y + restrictIn m W t) := by
  apply Fintype.expect_equiv (Equiv.subRight y)
  intro t
  have h := coordinateFreeze_add m W (t - y) y
  rw [sub_add_cancel] at h
  simp only [Equiv.subRight_apply]
  rw [h]

omit [Fintype J] [∀ j, NeZero (m j)] in
theorem restrictIn_supported (W : Finset J) (t : ResidueSpace m) :
    ∀ j ∉ W, restrictIn m W t j = 0 := by
  intro j hj
  simp [restrictIn, hj]

/-- `lem:record:fibre-scale`(c), averaging step: `Z_μ(h_j) ≤ Z_μ(u_j)`, where
`h_j = E_E u_j` is the square-step piece and `u_j` is the lift of `1_{A'_j}` with
the same cutoff on all coordinates. The law must be reflection positive at the
sorting cuts and invariant under the simultaneous translations supported on `E`
((R2), and (R3) with `r_p = 1`). -/
theorem referenceEnergy_stepLift_le (μ : FiniteLaw (Slot → ResidueSpace m))
    (hp : SlotReflectionPositive (signedIntegral μ.weight)) (E : Finset J)
    (hinv : ∀ s : ResidueSpace m, (∀ j ∉ E, s j = 0) →
      ∀ F : (Slot → ResidueSpace m) → ℝ, μ.expect (fun z => F (fun v => z v + s)) = μ.expect F)
    (Q' : ℝ) (B : Finset ℤ) (n : ℕ) :
    referenceEnergy μ (fun y => (stepLift m E Q' B n y).re) ≤
      referenceEnergy μ (fun y => (lift m Q' (Icc 1 (n : ℤ)) (indicator B) y).re) := by
  set u : ResidueSpace m → ℂ := fun y => lift m Q' (Icc 1 (n : ℤ)) (indicator B) y
  have hstep : ∀ y, (stepLift m E Q' B n y).re =
      ∑ t : ResidueSpace m, (Fintype.card (ResidueSpace m) : ℝ)⁻¹ * (u (y + restrictIn m E t)).re := by
    intro y
    have h1 := expect_lift_freeze m Q' (Icc 1 (n : ℤ)) (indicator B) E y
    rw [expect_freeze_eq_translates m E (fun y => lift m Q' (Icc 1 (n : ℤ)) (indicator B) y) y]
      at h1
    unfold stepLift
    rw [← h1, expect_eq_sum_div_card, card_univ]
    rw [show ((∑ t : ResidueSpace m, u (y + restrictIn m E t)) / (Fintype.card (ResidueSpace m) : ℂ))
        = (((Fintype.card (ResidueSpace m) : ℝ)⁻¹ : ℝ) : ℂ) *
            ∑ t : ResidueSpace m, u (y + restrictIn m E t) by
      push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
  have hfun : (fun y => (stepLift m E Q' B n y).re) = fun y =>
      ∑ t : ResidueSpace m, (Fintype.card (ResidueSpace m) : ℝ)⁻¹ * (u (y + restrictIn m E t)).re :=
    funext hstep
  rw [hfun]
  apply referenceEnergy_average_le μ hp (fun _ => (Fintype.card (ResidueSpace m) : ℝ)⁻¹)
    (fun _ => by positivity)
  · rw [sum_const, card_univ, nsmul_eq_mul]
    have : (Fintype.card (ResidueSpace m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · intro t
    exact referenceEnergy_translate μ (restrictIn m E t)
      (hinv _ (restrictIn_supported m E t)) (fun y => (u y).re)

/-! ### Two scales: adding coordinates of large modulus -/

section TwoScales

variable {J₀ J : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
  (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)]

omit [DecidableEq J] in
/-- A nonzero label on coordinates all of whose nonzero elements have order `> Q`
has conductor `> Q`. -/
theorem lt_conductor_of_ne_zero {Q : ℝ}
    (hlarge : ∀ k (x : ZMod (p k)), x ≠ 0 → Q < addOrderOf x) {t : ResidueSpace p}
    (ht : t ≠ 0) : Q < conductor p t := by
  obtain ⟨k, hk⟩ : ∃ k, t k ≠ 0 := by
    by_contra h
    push Not at h
    exact ht (funext h)
  have h1 : addOrderOf (t k) ≤ conductor p t := by
    unfold conductor
    exact Finset.single_le_prod (fun i _ => Nat.one_le_iff_ne_zero.mpr
      (addOrderOf_pos (t i)).ne') (mem_univ k)
  exact (hlarge k (t k) hk).trans_le (by exact_mod_cast h1)

/-- The paper's remark in the proof of `lem:record:fibre-scale`(c): a character
with `q ≤ Q` involves only primes `≤ Q`. Hence adjoining coordinates whose nonzero
elements all have order `> Q` (tail primes `> Q`) does not change the lift with
cutoff `Q`: the lift on `G_N` is the lift on `G_n`, read on the `G_n`-coordinates. -/
theorem lift_join_eq_of_large {Q : ℝ}
    (hlarge : ∀ k (x : ZMod (p k)), x ≠ 0 → Q < addOrderOf x) (I : Finset ℤ) (f : ℤ → ℂ)
    (z : ResidueSpace (joinModuli m₀ p)) :
    lift (joinModuli m₀ p) Q I f z = lift m₀ Q I f (splitEquiv m₀ p z).1 := by
  unfold lift liftOn retained
  rw [sum_filter, sum_filter]
  rw [← (splitEquiv m₀ p).toEquiv.symm.sum_comp, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [sum_eq_single (0 : ResidueSpace p)]
  · have hs : splitEquiv m₀ p ((splitEquiv m₀ p).toEquiv.symm (a, 0)) = (a, 0) :=
      (splitEquiv m₀ p).toEquiv.apply_symm_apply _
    have hcond : conductor (joinModuli m₀ p) ((splitEquiv m₀ p).toEquiv.symm (a, 0)) =
        conductor m₀ a := by
      rw [conductor_split, hs]
      simp
    rw [hcond]
    by_cases ha : (conductor m₀ a : ℝ) ≤ Q
    · rw [ite_eq_left ha, ite_eq_left ha]
      have hval : ∀ w : ResidueSpace (joinModuli m₀ p),
          prodChar (joinModuli m₀ p) ((splitEquiv m₀ p).toEquiv.symm (a, 0)) w =
            prodChar m₀ a (splitEquiv m₀ p w).1 := by
        intro w
        rw [prodChar_split, hs]
        simp
      rw [hval]
      congr 1
      unfold intervalCoeff
      congr 1
      apply sum_congr rfl
      intro n _
      rw [hval, splitEquiv_integerResidue]
      rfl
    · rw [ite_eq_right ha, ite_eq_right ha]
  · intro t _ ht
    have hlt := lt_conductor_of_ne_zero p hlarge ht
    have hs : splitEquiv m₀ p ((splitEquiv m₀ p).toEquiv.symm (a, t)) = (a, t) :=
      (splitEquiv m₀ p).toEquiv.apply_symm_apply _
    have hcond : ¬ (conductor (joinModuli m₀ p) ((splitEquiv m₀ p).toEquiv.symm (a, t)) : ℝ) ≤ Q := by
      rw [conductor_split, hs]
      intro hle
      have h1 : (conductor p t : ℝ) ≤ (conductor m₀ a * conductor p t : ℕ) := by
        exact_mod_cast Nat.le_mul_of_pos_left _ (conductor_pos m₀ a)
      linarith
    exact ite_eq_right hcond
  · intro h; exact absurd (mem_univ _) h

/-- `lem:record:fibre-scale`(c) for a product law. The data:
- `G_N = G_n × X_extra` with `X_extra` the extra coordinates, all of whose nonzero
  elements have order `> Q'` (tail primes in `(n^β, N^β]`);
- the law `μ_N` is the product of the scale-`n` law `μ_n` and a law on the extra
  coordinates, by the definition of `μ_N` as a product of atom laws and (R1);
- `μ_N` is reflection positive at the sorting cuts, (R2);
- `μ_N` is invariant under the simultaneous translations supported on `E`,
  (R3) with `r_p = 1`.

Then `Z_{μ_N}(h_j) ≤ Λ_{μ_n}(F_{A'_j})`. With `Q' = n^β` and `μ_n` the reference law
at the scale `ℓ` (`n = Kℓ`), the right side is `Y(ℓ, A'_j)`. Since `h_j` does not
depend on the coordinates of `E` (`stepLift_congr`), `Z_{μ_N}(h_j)` is the
paper's `Z_𝒮(h_j)` for a product of the atom laws, by `referenceEnergy_comp_fst`. -/
theorem referenceEnergy_stepLift_le_scale
    (μn : FiniteLaw (Slot → ResidueSpace m₀)) (ν : FiniteLaw (Slot → ResidueSpace p))
    (μN : FiniteLaw (Slot → ResidueSpace (joinModuli m₀ p)))
    (hprod : ∀ F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ, μN.expect F =
      (μn.product ν).expect (fun w => F (fun v => (splitEquiv m₀ p).symm (w.1 v, w.2 v))))
    (hp : SlotReflectionPositive (signedIntegral μN.weight)) (E : Finset (J₀ ⊕ J))
    (hinv : ∀ s : ResidueSpace (joinModuli m₀ p), (∀ k ∉ E, s k = 0) →
      ∀ F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ,
        μN.expect (fun z => F (fun v => z v + s)) = μN.expect F)
    {Q' : ℝ} (hlarge : ∀ k (x : ZMod (p k)), x ≠ 0 → Q' < addOrderOf x) (B : Finset ℤ) (n : ℕ) :
    referenceEnergy μN (fun y => (stepLift (joinModuli m₀ p) E Q' B n y).re) ≤
      referenceEnergy μn (fun x => (wholeLift m₀ Q' n B x).re) := by
  refine (referenceEnergy_stepLift_le (joinModuli m₀ p) μN hp E hinv Q' B n).trans_eq ?_
  unfold referenceEnergy
  rw [hprod, FiniteLaw.expect_product]
  have hconst : ∀ a : Slot → ResidueSpace m₀, ν.expect (fun b : Slot → ResidueSpace p =>
      ∏ v, (lift (joinModuli m₀ p) Q' (Icc 1 (n : ℤ)) (indicator B)
        ((splitEquiv m₀ p).symm (a v, b v))).re) = ∏ v, (wholeLift m₀ Q' n B (a v)).re := by
    intro a
    have : ∀ b : Slot → ResidueSpace p, (∏ v, (lift (joinModuli m₀ p) Q' (Icc 1 (n : ℤ))
        (indicator B) ((splitEquiv m₀ p).symm (a v, b v))).re) =
          ∏ v, (wholeLift m₀ Q' n B (a v)).re := by
      intro b
      apply prod_congr rfl
      intro v _
      rw [lift_join_eq_of_large m₀ p hlarge, AddEquiv.apply_symm_apply]
      rfl
    simp only [this, FiniteLaw.expect_const]
  simp only [hconst]

end TwoScales

end Sarkozy.Functional
