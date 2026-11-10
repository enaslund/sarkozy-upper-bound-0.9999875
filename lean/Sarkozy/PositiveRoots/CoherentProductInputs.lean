module

public import Sarkozy.PositiveRoots.CoherentCoreStarNorm
public import Sarkozy.PositiveRoots.CoherentCoreCharacters
public import Sarkozy.Cuts.DiagonalProducts
public import Sarkozy.Cuts.DiagonalNorms

/-! Exact constant-diagonal image and the off-diagonal norm of normalized raw-star products. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD Sarkozy.Cuts
open Sarkozy.Recentering
open scoped symmDiff

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

noncomputable def normalizedStarProduct (S T : Finset U) (F : ZMod p × ZMod p → ℝ)
    (x : U → ZMod p) : ℝ := (p : ℝ) * starProduct S T (fun u v => F (u, v)) x

noncomputable def rawCorrelation (S T : Finset U) (x : U → ZMod p) : ℝ :=
  (fieldLaw p).expect (fun z => StarMatrix.psi S z x * StarMatrix.psi T z x)

omit [Fintype U] [DecidableEq U] in
theorem starMean_expect_psi (S : Finset U) (x : U → ZMod p) :
    (fieldLaw p).expect (fun z => StarMatrix.psi S z x) = starMean S x := by
  rw [fieldLaw, FiniteLaw.expect_uniform, ZMod.card, StarMatrix.sum_psi]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

omit [Fintype U] [DecidableEq U] in
theorem normalizedStarProduct_entangled (S T : Finset U) (x : U → ZMod p) :
    normalizedStarProduct S T (fun z => entangled z.1 z.2) x =
      ((p : ℝ) / Real.sqrt (p - 1)) * (rawCorrelation S T x - starMean S x * starMean T x) := by
  change (p : ℝ) * (fieldLaw p).expect (fun u => (fieldLaw p).expect
    (fun v => StarMatrix.psi S u x * StarMatrix.psi T v x * entangled u v)) = _
  rw [← FiniteLaw.expect_product (fieldLaw p) (fieldLaw p)
    (fun z => StarMatrix.psi S z.1 x * StarMatrix.psi T z.2 x * entangled z.1 z.2)]
  change (p : ℝ) * ((FiniteLaw.uniform (ZMod p)).product (FiniteLaw.uniform (ZMod p))).expect
    (fun z => StarMatrix.psi S z.1 x * StarMatrix.psi T z.2 x * entangled z.1 z.2) = _
  rw [entangled_tensor (fun u => StarMatrix.psi S u x) (fun v => StarMatrix.psi T v x),
    ZMod.card]
  change (p : ℝ) * ((rawCorrelation S T x -
    (fieldLaw p).expect (fun z => StarMatrix.psi S z x) *
      (fieldLaw p).expect (fun z => StarMatrix.psi T z x)) / _) = _
  rw [starMean_expect_psi, starMean_expect_psi]
  ring

theorem normalizedStarProduct_entangled_bound (S T : Finset U) (x : U → ZMod p)
    (hx : Set.InjOn x (S ∪ T)) {bD bS bT : ℝ}
    (hD : |starMean (S ∆ T) x| ≤ bD) (hS : |starMean S x| ≤ bS) (hT : |starMean T x| ≤ bT) :
    |normalizedStarProduct S T (fun z => entangled z.1 z.2) x| ≤
      ((p : ℝ) / Real.sqrt (p - 1)) *
        (bD + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ + bS * bT) := by
  have hS0 : 0 ≤ bS := (abs_nonneg _).trans hS
  have hfactor : 0 ≤ (p : ℝ) / Real.sqrt (p - 1) := by positivity
  rw [normalizedStarProduct_entangled, abs_mul, abs_of_nonneg hfactor]
  apply mul_le_mul_of_nonneg_left _ hfactor
  calc
    _ ≤ |rawCorrelation S T x| + |starMean S x * starMean T x| := abs_sub _ _
    _ ≤ (bD + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹) + bS * bT := by
      apply add_le_add
      · rw [rawCorrelation, fieldLaw, uniform_psi_pair]
        exact (abs_sum_starKer_mul_le S T x hx).trans (add_le_add hD le_rfl)
      · rw [abs_mul]
        exact mul_le_mul hS hT (abs_nonneg _) hS0

theorem rawCorrelation_self (S : Finset U) (x : U → ZMod p) (hx : Function.Injective x) :
    rawCorrelation S S x = 1 - (S.card : ℝ) * (p : ℝ)⁻¹ := by
  unfold rawCorrelation fieldLaw
  rw [uniform_psi_pair, sum_starKer_sq S x (fun k l hkl => hx.ne hkl)]
  ring

theorem normalizedStarProduct_equal_exception (S : Finset U) (x : U → ZMod p)
    (hx : Function.Injective x) :
    normalizedStarProduct S S (fun z => entangled z.1 z.2) x - (p : ℝ) / Real.sqrt (p - 1) =
      -((p : ℝ) / Real.sqrt (p - 1)) * ((S.card : ℝ) * (p : ℝ)⁻¹ + starMean S x ^ 2) := by
  rw [normalizedStarProduct_entangled, rawCorrelation_self S x hx]
  ring

theorem normalizedStarProduct_equal_remainder (S : Finset U) (x : U → ZMod p)
    (hx : Function.Injective x) {b : ℝ} (hb : |starMean S x| ≤ b) :
    |normalizedStarProduct S S (fun z => entangled z.1 z.2) x - (p : ℝ) / Real.sqrt (p - 1)| ≤
      ((p : ℝ) / Real.sqrt (p - 1)) * ((S.card : ℝ) * (p : ℝ)⁻¹ + b ^ 2) := by
  rw [normalizedStarProduct_equal_exception S x hx, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ (p : ℝ) / Real.sqrt (p - 1)),
    abs_of_nonneg (by positivity : 0 ≤ (S.card : ℝ) * (p : ℝ)⁻¹ + starMean S x ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2

theorem normalizedStarProduct_offdiag_sq {Ω : Type*} [Fintype Ω]
    (hDLK : Target.FourCycle) (hp2 : p ≠ 2) (ν : FiniteLaw Ω) (X : Ω → U → ZMod p)
    (hX : ∀ x, Function.Injective (X x)) {D : ℝ} (hD : 0 ≤ D)
    (hdens : ∀ f : (U → ZMod p) → ℝ, (∀ x, 0 ≤ f x) →
      ν.expect (fun x => f (X x)) ≤ D * (cube p U).expect f)
    (S T : Finset U) (hS : S.Nonempty) (hT : T.Nonempty) (hU : 2 ≤ (S ∪ T).card)
    (F : ZMod p × ZMod p → ℝ) (hF : ∀ z, F (z, z) = 0) :
    ν.expect (fun x => normalizedStarProduct S T F (X x) ^ 2) ≤
      ((if S = T then 4 else 1) * D) * ((fieldLaw p).product (fieldLaw p)).expect (fun z => F z ^ 2) := by
  have h := starProduct_law_sq hDLK hp2 ν X hX hD hdens S T hS hT hU (fun u v => F (u, v)) hF
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [normalizedStarProduct, mul_pow, FiniteLaw.expect_const_mul]
  refine (mul_le_mul_of_nonneg_left h (sq_nonneg (p : ℝ))).trans_eq ?_
  rw [FiniteLaw.expect_product]
  field_simp

end Sarkozy.PositiveRoots.CoherentFrame
