module

public import Sarkozy.L20Cap.BalancedCharges
public import Sarkozy.L20Cap.BalancedErrors
public import Sarkozy.L20Cap.BalancedPolynomial

/-! Assemble the incident-weight bounds into the paper's `D_bal`. -/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy.Extraction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem balanced_single_numerator (hm1 : quadraticChar F (-1) = -1)
    {Q : ℝ} (hQ : 0 < Q) (x : CoreT F × PairT F) (f : ℕ → ℝ) :
    (∑ i, ∑ j, (Real.sqrt Q)⁻¹ ^ 2 * collisionAlphaTilde G6 D20Z (labels x) i j *
      ∏ ℓ ∈ univ.erase i, f (collisionT G6 D20Z balancedOrd i j ℓ)) =
      2 * (balancedA Q x + balancedC Q x) * (f 3 ^ 2 * f 4 ^ 3) +
        2 * balancedB Q x * (f 2 * f 3 ^ 2 * f 4 ^ 2) := by
  let g : Fin 6 → ℝ := fun i =>
    if i ∈ balancedPair then f 2 * f 3 ^ 2 * f 4 ^ 2 else f 3 ^ 2 * f 4 ^ 3
  have ht : ∀ i j,
      (Real.sqrt Q)⁻¹ ^ 2 * collisionAlphaTilde G6 D20Z (labels x) i j *
        (∏ ℓ ∈ univ.erase i, f (collisionT G6 D20Z balancedOrd i j ℓ)) =
      (Real.sqrt Q)⁻¹ ^ 2 * collisionAlphaTilde G6 D20Z (labels x) i j * g i := by
    intro i j
    by_cases h : collisionGamma G6 D20Z i j
    · rw [balanced_product f i j h]
    · simp only [collisionAlphaTilde, h, ↓reduceIte, mul_zero, zero_mul]
  simp_rw [ht]
  have hs : (∑ i, ∑ j,
      (Real.sqrt Q)⁻¹ ^ 2 * collisionAlphaTilde G6 D20Z (labels x) i j * g i) =
      ∑ i, collisionRhoTilde G6 D20Z Q (labels x) i * g i := by
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_mul, ← mul_sum]
    rfl
  rw [hs]
  simp_rw [balancedRho_eq hm1 hQ]
  norm_num [Fin.sum_univ_six, g, balancedPair]
  ring

theorem balanced_incident1_eq (hm1 : quadraticChar F (-1) = -1)
    {Q : ℝ} (hQ : 0 < Q) (x : CoreT F × PairT F) :
    collisionSignedIncident1 G6 D20Z balancedOrd Q 6 (labels x) =
      (Lamc (Real.sqrt Q)⁻¹ Q⁻¹)⁻¹ *
        (2 * (balancedA Q x + balancedC Q x) *
            ((1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 3) ^ 2 * (1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 4) ^ 3) +
          2 * balancedB Q x * ((1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 2) *
            (1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 3) ^ 2 * (1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 4) ^ 2)) := by
  unfold collisionSignedIncident1
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 6 = 12 by norm_num]
  rw [balanced_single_numerator hm1 hQ x (fun j => 1 + coarseError j Q 12),
    balanced_Lint hQ]
  simp only [balanced_Ec hQ]

theorem balanced_incident1_le (hm1 : quadraticChar F (-1) = -1)
    {Q : ℝ} (hQ : 64 ≤ Q) (x : CoreT F × PairT F) (hx : Avoid x) :
    collisionSignedIncident1 G6 D20Z balancedOrd Q 6 (labels x) ≤
      (Lamc (Real.sqrt Q)⁻¹ Q⁻¹)⁻¹ * Sc (Real.sqrt Q)⁻¹ Q⁻¹ := by
  have hQ0 : 0 < Q := by linarith
  rw [balanced_incident1_eq hm1 hQ0]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (balanced_Lamc_pos hQ).le)
  have hc : 2 * (balancedA Q x + balancedC Q x) ≤ 32 * Q⁻¹ := by
    linarith [balancedAC_le hQ0 x hx]
  have hb : 2 * balancedB Q x ≤ 64 * Q⁻¹ := by
    linarith [balancedB_le hm1 hQ0 x]
  have e2 := balanced_Ec_nonneg hQ0 2
  have e3 := balanced_Ec_nonneg hQ0 3
  have e4 := balanced_Ec_nonneg hQ0 4
  have hc' := mul_le_mul_of_nonneg_right hc (by positivity :
    0 ≤ (1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 3) ^ 2 * (1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 4) ^ 3)
  have hb' := mul_le_mul_of_nonneg_right hb (by positivity :
    0 ≤ (1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 2) * (1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 3) ^ 2 *
      (1 + Ec (Real.sqrt Q)⁻¹ Q⁻¹ 4) ^ 2)
  exact (add_le_add hc' hb').trans_eq (by unfold Sc; ring)

theorem balanced_incident2_eq (hm1 : quadraticChar F (-1) = -1)
    {Q : ℝ} (hQ : 0 < Q) (x : CoreT F × PairT F) (π : ℕ → Fin 6 → ℕ) :
    collisionSignedIncident2 G6 D20Z π Q 6 (labels x) =
      (Lamc (Real.sqrt Q)⁻¹ Q⁻¹)⁻¹ * Uc (Real.sqrt Q)⁻¹ Q⁻¹ *
        (Fpoly (balancedA Q x) (balancedC Q x) * (1 + balancedB Q x) *
          (1 + balancedB Q x) - 1 - 2 * (balancedA Q x + balancedC Q x) -
            balancedB Q x - balancedB Q x) := by
  unfold collisionSignedIncident2
  simp only [Fintype.card_fin, balancedRho_eq hm1 hQ]
  change (collisionLint G6 Q 6)⁻¹ * ∑ k ∈ Icc 2 6,
    collisionUpsK G6 D20Z π Q 6 k *
      balancedPoly k (balancedA Q x) (balancedC Q x) (balancedB Q x) (balancedB Q x) = _
  have he : ∀ k ∈ Icc 2 6,
      collisionUpsK G6 D20Z π Q 6 k = Uc (Real.sqrt Q)⁻¹ Q⁻¹ :=
    fun k hk => balanced_UpsK π hQ (mem_Icc.mp hk).1
  rw [sum_congr rfl fun k hk => congrArg (fun u => u *
    balancedPoly k (balancedA Q x) (balancedC Q x) (balancedB Q x) (balancedB Q x)) (he k hk)]
  rw [← mul_sum, balancedPoly_sum, balanced_Lint hQ]
  ring

theorem balanced_incident2_le (hm1 : quadraticChar F (-1) = -1)
    {Q : ℝ} (hQ : 64 ≤ Q) (x : CoreT F × PairT F) (hx : Avoid x)
    (π : ℕ → Fin 6 → ℕ) :
    collisionSignedIncident2 G6 D20Z π Q 6 (labels x) ≤
      (Lamc (Real.sqrt Q)⁻¹ Q⁻¹)⁻¹ * Uc (Real.sqrt Q)⁻¹ Q⁻¹ * (Pc Q⁻¹ - 96 * Q⁻¹) := by
  have hQ0 : 0 < Q := by linarith
  rw [balanced_incident2_eq hm1 hQ0]
  exact mul_le_mul_of_nonneg_left
    (degree_two_le (balancedA_nonneg hm1 hQ0 x) (balancedC_nonneg hm1 hQ0 x)
      (balancedAC_le hQ0 x hx) (balancedB_nonneg hm1 hQ0 x) (balancedB_le hm1 hQ0 x)
      (balancedB_nonneg hm1 hQ0 x) (balancedB_le hm1 hQ0 x))
    (mul_nonneg (inv_nonneg.mpr (balanced_Lamc_pos hQ).le) (balanced_Uc_nonneg hQ0))

/-- The sum of the actual signed incident bounds is at most `D_bal`. -/
theorem balanced_incident_le (hm1 : quadraticChar F (-1) = -1)
    {Q : ℝ} (hQ : 64 ≤ Q) (x : CoreT F × PairT F) (hx : Avoid x)
    (π : ℕ → Fin 6 → ℕ) :
    collisionSignedIncident1 G6 D20Z balancedOrd Q 6 (labels x) +
      collisionSignedIncident2 G6 D20Z π Q 6 (labels x) ≤ Dbal (Real.sqrt Q)⁻¹ Q⁻¹ := by
  refine (add_le_add (balanced_incident1_le hm1 hQ x hx)
    (balanced_incident2_le hm1 hQ x hx π)).trans_eq ?_
  unfold Dbal
  ring

end Sarkozy.L20Cap
