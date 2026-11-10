module

public import Sarkozy.FourierArithmetic.ResidueMoments

/-!
# Lift moments retaining the input L2 mass

The square-function recurrence starts at the first moment, rather than at the
zeroth moment. This retains the input mass and is the improvement needed by
the paper's global second-density estimate. The constants used here are
deliberately coarser than the displayed paper constants; their growth is still
exponential in the maximum support size, hence subpower in the cutoff.
-/

@[expose] public section

open Finset Complex Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology

namespace Sarkozy.FourierArithmetic

theorem square_moment_mass_bound {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (U : I → Finset J) (f : I → (∀ j, X j) → ℝ)
    (hf : ∀ i, ∀ x y, (∀ j ∈ U i, x j = y j) → f i x = f i y)
    (k : ℕ) (hk : ∀ i, (U i).card ≤ k)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hcond : ∀ (W : Finset J) x,
      (𝔼 y, ∑ i, f i (hybrid (fun j => decide (j ∈ W)) x y) ^ 2) ≤ A * D ^ W.card)
    (r : ℕ) (hr : 1 ≤ r) :
    (𝔼 x, (∑ i, f i x ^ 2) ^ r) ≤
      (A * D ^ (r * k)) ^ (r - 1) * (𝔼 x, ∑ i, f i x ^ 2) := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  let B : ℝ := A * D ^ (r * k)
  have hB : 0 ≤ B := mul_nonneg hA (pow_nonneg hD0 _)
  have hmass : 0 ≤ 𝔼 x, ∑ i, f i x ^ 2 :=
    expect_nonneg (fun x _ => sum_nonneg (fun i _ => sq_nonneg _))
  have hind (t : ℕ) (ht : t < r) :
      (𝔼 x, (∑ i, f i x ^ 2) ^ (t + 1)) ≤ B ^ t * (𝔼 x, ∑ i, f i x ^ 2) := by
    induction t with
    | zero => simp only [zero_add, pow_one, pow_zero, one_mul, le_refl]
    | succ t ih =>
      have hi := ih (by omega)
      have hstep := square_moment_step U f hf k hk A D hA hD hcond (t + 1)
      apply hstep.trans
      have hcoef : A * D ^ ((t + 1) * k) ≤ B :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.mul_le_mul_right k (by omega))) hA
      calc
        _ ≤ B * (B ^ t * (𝔼 x, ∑ i, f i x ^ 2)) :=
          mul_le_mul hcoef hi
            (expect_nonneg (fun x _ => pow_nonneg (sum_nonneg (fun i _ => sq_nonneg _)) _)) hB
        _ = B ^ (t + 1) * (𝔼 x, ∑ i, f i x ^ 2) := by rw [pow_succ]; ring
  simpa only [Nat.sub_add_cancel hr, B] using hind (r - 1) (by omega)

variable {J : Type*} [Fintype J] (p : J → ℕ) [∀ j, NeZero (p j)]

theorem liftPiece_moment_mass [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀ U ∈ F, ∏ j ∈ U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (hsmall : 2 * (Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ) ^ 5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ n < L, |f n| ≤ M) (k : ℕ) (hk : ∀ U ∈ F, U.card ≤ k)
    (r : ℕ) (hr : 1 ≤ r) :
    (𝔼 x, (∑ U ∈ F, liftPiece p L f U x) ^ (2 * r)) ≤
      (((4 : ℝ) * 2 ^ (2 * r)) ^ k) ^ r *
        (4 * M ^ 2 * 5 ^ (r * k)) ^ (r - 1) *
          (𝔼 x, ∑ U ∈ F, liftPiece p L f U x ^ 2) := by
  classical
  apply (symmetrization_moment F (liftPiece p L f)
    (fun U _ => liftPiece_exactSupport p L f U) k hk r hr).trans
  have he (x : ResidueSpace p) : (∑ U ∈ F, liftPiece p L f U x ^ 2) =
      ∑ U : F, liftPiece p L f U.val x ^ 2 := (sum_coe_sort F _).symm
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [he]
  apply square_moment_mass_bound (fun U : F => U.val) (fun U => liftPiece p L f U.val)
    (fun U x y hxy => exactSupport_congr U.val _ (liftPiece_exactSupport p L f U.val) x y hxy)
    k (fun U => hk U.val U.property) (4 * M ^ 2) 5 (by positivity) (by norm_num) _ r hr
  intro W x
  have h := liftPiece_conditional_square_sum p hp F Q hQ hden L hL hsmall hsmall' f M hM hf W x
  have hh (y : ResidueSpace p) : coordinateFreeze p W x y =
      hybrid (fun j => decide (j ∈ W)) x y := by
    ext j
    simp [coordinateFreeze, hybrid]
  simp_rw [hh] at h
  simpa only [he] using h

theorem gateCoefficient_empty_gram [DecidableEq J] {I : Type*} [Fintype I] [DecidableEq I]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (a : I → ResidueSpace p) (hinj : Function.Injective a) (Q : ℕ) (hQ : 0 < Q)
    (ha : ∀ i, supportDenominator p (a i) ≤ Q)
    (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ) (z : ResidueSpace p) :
    (∑ i, ‖gateCoefficient p L (fun n => (f n : ℂ)) ∅ z (a i)‖ ^ 2) ≤
      (1 + (Q : ℝ) ^ 4 / (2 * L)) * ((L : ℝ)⁻¹ * ∑ n ∈ range L, f n ^ 2) := by
  have h := arithmetic_phase_analysis p hp a hinj Q hQ ha 1 (fun _ => Nat.coprime_one_left _)
    L (fun n => (f n : ℂ))
  simp only [Nat.cast_one, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have he (i : I) : gateCoefficient p L (fun n => (f n : ℂ)) ∅ z (a i) =
      (L : ℂ)⁻¹ * ∑ n : Fin L, (f n : ℂ) * expPhase (-(n : ℝ) * frequencyAngle p (a i)) := by
    simp only [gateCoefficient, exactGate, prod_empty, Complex.ofReal_one, mul_one]
    rw [Fin.sum_univ_eq_sum_range
      (fun n : ℕ => (f n : ℂ) * expPhase (-(n : ℝ) * frequencyAngle p (a i))) L]
  simp only [he, norm_mul, norm_inv, Complex.norm_natCast, mul_pow, ← mul_sum]
  have hL' : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  calc
    _ ≤ (L : ℝ)⁻¹ ^ 2 * ((L + (Q : ℝ) ^ 4 / 2) * ∑ n : Fin L, f n ^ 2) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => f n ^ 2) L]
      field_simp

theorem liftPiece_square_sum_gram [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀ U ∈ F, ∏ j ∈ U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ) :
    (𝔼 x, ∑ U ∈ F, liftPiece p L f U x ^ 2) ≤
      (1 + (Q : ℝ) ^ 4 / (2 * L)) * ((L : ℝ)⁻¹ * ∑ n ∈ range L, f n ^ 2) := by
  classical
  let Ω : Finset (ResidueSpace p) := univ.filter (fun a => primeSupport p a ∈ F)
  have ha (a : Ω) : supportDenominator p a.val ≤ Q :=
    hden (primeSupport p a.val) (mem_filter.mp a.property).2
  have hgram := gateCoefficient_empty_gram p hp (fun a : Ω => a.val)
    Subtype.val_injective Q hQ ha L hL f 0
  rw [sum_coe_sort Ω (fun a => ‖gateCoefficient p L (fun n => (f n : ℂ)) ∅ 0 a‖ ^ 2)] at hgram
  have hparse (U : Finset J) : (𝔼 x, liftPiece p L f U x ^ 2) =
      ∑ a ∈ univ.filter (fun a => primeSupport p a = U),
        ‖gateCoefficient p L (fun n => (f n : ℂ)) ∅ 0 a‖ ^ 2 := by
    have hfreeze (x : ResidueSpace p) : coordinateFreeze p ∅ 0 x = x := by
      ext j
      simp only [coordinateFreeze, Finset.notMem_empty, ite_false]
    simpa only [hfreeze, sdiff_empty, inter_empty]
      using liftPiece_conditional_parseval p L f U ∅ 0
  rw [expect_sum_comm]
  simp only [hparse]
  rw [sum_fiberwise_eq_sum_filter]
  exact hgram

theorem gram_factor_le_two {L Q : ℕ} (hL : 0 < L) (hQ : 0 < Q)
    (hsmall : (Q : ℝ) ^ 5 ≤ L) : 1 + (Q : ℝ) ^ 4 / (2 * L) ≤ 2 := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq4 : (Q : ℝ) ^ 4 ≤ L :=
    (pow_le_pow_right₀ hQ1 (by decide : 4 ≤ 5)).trans hsmall
  have hL' : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hfrac : (Q : ℝ) ^ 4 / (2 * L) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  linarith

noncomputable def massMomentBase (r : ℕ) : ℝ :=
  ((4 : ℝ) * 2 ^ (2 * r)) ^ r * 5 ^ (r * (r - 1))

theorem massMomentBase_one_le (r : ℕ) : 1 ≤ massMomentBase r := by
  unfold massMomentBase
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_pow₀
    have htwo : (1 : ℝ) ≤ 2 ^ (2 * r) := one_le_pow₀ (by norm_num)
    linarith
  · exact one_le_pow₀ (by norm_num)

theorem liftPiece_moment_density_degree [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀ U ∈ F, ∏ j ∈ U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (hsmall : 2 * (Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ) ^ 5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ n < L, |f n| ≤ M) (k : ℕ) (hk : ∀ U ∈ F, U.card ≤ k)
    (r : ℕ) (hr : 1 ≤ r) :
    (𝔼 x, (∑ U ∈ F, liftPiece p L f U x) ^ (2 * r)) ≤
      2 * 4 ^ (r - 1) * massMomentBase r ^ k * M ^ (2 * (r - 1)) *
        ((L : ℝ)⁻¹ * ∑ n ∈ range L, f n ^ 2) := by
  have hmass : 0 ≤ (L : ℝ)⁻¹ * ∑ n ∈ range L, f n ^ 2 := by positivity
  have hgram := (liftPiece_square_sum_gram p hp F Q hQ hden L hL f).trans
    (mul_le_mul_of_nonneg_right (gram_factor_le_two hL hQ hsmall') hmass)
  apply (liftPiece_moment_mass p hp F Q hQ hden L hL hsmall hsmall' f M hM hf k hk r hr).trans
  apply (mul_le_mul_of_nonneg_left hgram (by positivity)).trans_eq
  unfold massMomentBase
  simp only [mul_pow, ← pow_mul]
  ring_nf

/-- Uniform subpower moments retaining the actual input square mass.
The constant is independent of the finite alphabet of moduli, the cutoff,
the support family, the interval length, and the input function. -/
theorem uniform_lift_moment_density (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀ j, NeZero (p j)], (Pairwise fun i j => (p i).Coprime (p j)) → Function.Injective p →
      ∀ (F : Finset (Finset J)) (Q : ℕ), 0 < Q → (∀ U ∈ F, ∏ j ∈ U, p j ≤ Q) →
      ∀ L : ℕ, 0 < L → 2 * (Q : ℝ) ≤ L → (Q : ℝ) ^ 5 ≤ L →
      ∀ (f : ℕ → ℝ) (M : ℝ), 0 ≤ M → (∀ n < L, |f n| ≤ M) →
      (𝔼 x, (∑ U ∈ F, liftPiece p L f U x) ^ (2 * r)) ≤
        C * (Q : ℝ) ^ ε * M ^ (2 * (r - 1)) * ((L : ℝ)⁻¹ * ∑ n ∈ range L, f n ^ 2) := by
  let B := massMomentBase r
  have hB : 1 ≤ B := massMomentBase_one_le r
  obtain ⟨T, hT⟩ := exists_nat_power_threshold B ε hε
  refine ⟨2 * 4 ^ (r - 1) * B ^ T, by positivity, ?_⟩
  intro J _ _ p _ hp hinj F Q hQ hden L hL hsmall hsmall' f M hM hf
  by_cases hF : F.Nonempty
  · obtain ⟨U, hU, hk⟩ := exists_mem_eq_sup F hF Finset.card
    let k := F.sup Finset.card
    have hcard : ∀ U ∈ F, U.card ≤ k := fun U hU => le_sup hU
    have hb : B ^ k ≤ B ^ T * (Q : ℝ) ^ ε := by
      rw [show k = U.card from hk]
      apply (exponential_support_bound U p hinj.injOn
        (fun i _ => Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p i)))
        B hB ε hε.le T hT).trans
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hB) _)
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      exact_mod_cast hden U hU
    have hm := liftPiece_moment_density_degree p hp F Q hQ hden L hL hsmall hsmall'
      f M hM hf k hcard r hr
    apply hm.trans
    have hmass : 0 ≤ (L : ℝ)⁻¹ * ∑ n ∈ range L, f n ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
        (by positivity : (0 : ℝ) ≤ 2 * 4 ^ (r - 1))) (pow_nonneg hM (2 * (r - 1)))) hmass
    convert hmul using 1; ring
  · simp only [not_nonempty_iff_eq_empty.mp hF, sum_empty, zero_pow (by omega : 2 * r ≠ 0),
      Fintype.expect_const]
    positivity

end Sarkozy.FourierArithmetic
