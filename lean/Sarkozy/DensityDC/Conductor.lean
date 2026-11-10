module

public import Sarkozy.DensityDC.Averaged
public import Sarkozy.Mixing.Fourier
public import Sarkozy.Functional.MomentBridge
public import Sarkozy.Structured.Representation

/-!
# The conductor bound for the telescoping terms of `lem:record:density-dc`

Step 1 of the proof of `lem:record:density-dc` (`paper/sections/08_scale_comparison.tex`)
bounds each telescoping term by `lem:record:prefix-conductor`. The bound uses that the
input at the changed slot, `g_v - g̃_v` (specialized at `z_v`), has no character of
conductor at most `H` (`lem:record:fibre-scale`(b)).

This file instantiates WP-S's `Sarkozy.Mixing.prefix_conductor_fourier` for the reference
law `μ_N = ⊗_b μ_b` (the coordinates of the group as atoms), and WP-FI's
`groupCoeff_squareStepModel_sq` for the paper's inputs and square-step models:

* `prodIntegral_eq_multilinear`: WP-S's `prodIntegral` is the multilinear average of
  `FiniteLaw.tensor`.
* `abs_multilinear_le_prefix_conductor`: `lem:record:prefix-conductor` in that form, with
  (R4) as `IsGammaMixing (m j) γ (μ_j) {v}` on the tail coordinates `T`.
* `groupCoeff_eq_zero_of_offE`: a function that does not depend on the coordinates of `E`
  has no character that is nonzero on `E`.
* `conj_squareStepModel`: the square-step model is real.
* `groupCoeff_input_sub_model_eq_zero`: `g(z,·) - g̃(z,·)` (real parts) has no character of
  conductor at most `H`, when `H ≤ Q'` (the paper's `H ≤ n^β`) and `H D_E ≤ Q`.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.DensityDC

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing

/-! ## Products of atom laws -/

section Product

variable {K : Type*} [Fintype K] [DecidableEq K] {Xk : K → Type*} [∀ j, Fintype (Xk j)]
  [∀ j, DecidableEq (Xk j)]

/-- WP-S's `prodIntegral ρ g = ∫ ∏_w g_w(z_w) d(⊗_j ρ_j)` is the multilinear average of the
product law `FiniteLaw.tensor ρ`. -/
theorem prodIntegral_eq_multilinear (ρ : ∀ j, FiniteLaw (Slot → Xk j))
    (g : Slot → (∀ j, Xk j) → ℝ) :
    prodIntegral ρ g = multilinearIntegral (signedIntegral (FiniteLaw.tensor ρ).weight) g := by
  unfold prodIntegral multilinearIntegral signedIntegral
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [tensor_weight]
  exact Fintype.sum_equiv (Equiv.piComm _) _ _ (fun z => rfl)

end Product

section Group

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- **`lem:record:prefix-conductor` for `μ_N = ⊗_b μ_b`** (WP-S's
`prefix_conductor_fourier`). The tail coordinates `T` are primes with (R4)
(`(γ, v)`-mixing), every one-slot marginal is uniform, and `C'` is divisible by the
conductor of every character of the prefix coordinates. If the input at `v` has no character
of conductor at most `H`, then `|Λ_{μ_N}(Y)| ≤ (C'/H)^γ ‖Y_v‖₂ ∏_{w≠v} ‖Y_w‖₁₄₂`. -/
theorem abs_multilinear_le_prefix_conductor (μb : ∀ j, FiniteLaw (Slot → ZMod (m j)))
    (hunif : ∀ j w, UniformSlot (μb j) w) (T : Finset J) (hprime : ∀ j ∈ T, (m j).Prime)
    {γ : ℝ} (hγ : 0 ≤ γ) (hmix : ∀ j ∈ T, ∀ v, IsGammaMixing (m j) γ (μb j) {v})
    {C' : ℕ} (hC' : 0 < C')
    (hdiv : ∀ a : ResidueSpace m, (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) ∣ C')
    {H : ℝ} (hH : 0 < H) (Y : Slot → ResidueSpace m → ℝ) (v : Slot)
    (hF : ∀ a, (conductor m a : ℝ) ≤ H → groupCoeff m (fun y => (Y v y : ℂ)) a = 0) :
    |multilinearIntegral (signedIntegral (FiniteLaw.tensor μb).weight) Y| ≤
      ((C' : ℝ) / H) ^ γ * (FiniteLaw.uniform (ResidueSpace m)).lpNorm 2 (Y v) *
        ∏ w : {w // w ≠ v}, (FiniteLaw.uniform (ResidueSpace m)).lpNorm 142 (Y w) := by
  have h := prefix_conductor_fourier m μb v (by rw [card_slot]; norm_num) hunif T hprime hγ
    (fun j hj => (isMixing_singleton_iff (μb j) v _).mp (hmix j hj v)) hC' hdiv hH Y hF
  rw [← prodIntegral_eq_multilinear]
  have h142 : ((2 * (Fintype.card Slot - 1) : ℕ) : ℝ) = 142 := by
    rw [card_slot]
    norm_num
  convert h using 4
  rw [card_slot]
  norm_num

/-- **Characters that are nonzero on `E`** vanish on a function that does not depend on the
coordinates of `E`. -/
theorem groupCoeff_eq_zero_of_offE (E : Finset J) (f : ResidueSpace m → ℂ)
    (hf : ∀ y y' : ResidueSpace m, (∀ k ∉ E, y k = y' k) → f y = f y') (a : ResidueSpace m)
    (ha : ∃ i ∈ E, a i ≠ 0) : groupCoeff m f a = 0 := by
  obtain ⟨i, hi, hai⟩ := ha
  set t : ResidueSpace m := Pi.single i 1 with ht
  have hft : ∀ y, f (y + t) = f y := by
    intro y
    apply hf
    intro k hk
    have hki : k ≠ i := fun h => hk (h ▸ hi)
    simp [ht, Pi.single_eq_of_ne hki]
  have hχt : prodChar m a t = ZMod.stdAddChar (a i) := by
    unfold prodChar
    rw [prod_eq_single i]
    · simp only [ht, Pi.single_eq_same, mul_one]
    · intro k _ hki
      simp only [ht, Pi.single_eq_of_ne hki, mul_zero, AddChar.map_zero_eq_one]
    · simp
  have hne : conj (prodChar m a t) ≠ 1 := by
    intro h
    have h1 : prodChar m a t = 1 := by
      have := congrArg conj h
      simpa using this
    rw [hχt, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := m i))] at h1
    exact hai (ZMod.injective_stdAddChar h1)
  have hshift : groupCoeff m f a = groupCoeff m f a * conj (prodChar m a t) := by
    unfold groupCoeff
    have h1 : (𝔼 y, f y * conj (prodChar m a y)) =
        𝔼 y, f (y + t) * conj (prodChar m a (y + t)) :=
      (Fintype.expect_equiv (Equiv.addRight t) (fun y => f (y + t) * conj (prodChar m a (y + t)))
        (fun y => f y * conj (prodChar m a y)) (fun y => rfl)).symm
    conv_lhs => rw [h1]
    rw [Finset.expect_mul]
    apply Finset.expect_congr rfl
    intro y _
    rw [hft, prodChar_add_right, map_mul]
    ring
  have h0 : groupCoeff m f a * (1 - conj (prodChar m a t)) = 0 := by
    rw [mul_sub, mul_one, ← hshift, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hne

/-- The square-step model is real. -/
theorem conj_squareStepModel (E : Finset J) (z : ResidueSpace m) {D0 : ℕ} (s : ZMod D0)
    (A I : Finset ℤ) (c : ℤ) (M R n : ℕ) (Q' : ℝ) (y : ResidueSpace m) :
    conj (squareStepModel m E z s A I c M R n Q' y) = squareStepModel m E z s A I c M R n Q' y := by
  unfold squareStepModel
  simp only [map_mul, map_div₀, map_sum, map_natCast]
  congr 1
  apply sum_congr rfl
  intro j _
  unfold stepLift
  exact conj_liftOn_of_real m (retainedOff m E Q') (fun a ha => neg_mem_retainedOff ha)
    (Icc 1 (n : ℤ)) (indicator _) (conj_indicator _) _

/-- The coefficients of a difference. -/
theorem groupCoeff_sub (f f' : ResidueSpace m → ℂ) (a : ResidueSpace m) :
    groupCoeff m (fun y => f y - f' y) a = groupCoeff m f a - groupCoeff m f' a := by
  unfold groupCoeff
  rw [← Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro y _
  ring

/-- **`lem:record:fibre-scale`(b) in the form used by `lem:record:density-dc`**: the
difference `g(z, ·) - g̃(z, ·)` of the specialized input and its square-step model (real
parts) has no character of conductor at most `H`, if `H ≤ Q'` and `H D_E ≤ Q`. -/
theorem groupCoeff_input_sub_model_eq_zero (hpair : Pairwise fun i j => (m i).Coprime (m j))
    (E : Finset J) (z : ResidueSpace m) {D0 : ℕ} (hD0 : 1 ≤ D0) (s : ZMod D0)
    (hcop0 : ∀ k, D0.Coprime (m k)) (A : Finset ℤ) (c : ℤ) {M : ℕ} (hM : 1 ≤ M) {K : ℕ}
    (hK : 1 ≤ K) {Q Q' H : ℝ} (hHQ' : H ≤ Q') (hHQ : H * (∏ j ∈ E, m j : ℕ) ≤ Q)
    (a : ResidueSpace m) (haH : (conductor m a : ℝ) ≤ H) :
    groupCoeff m (fun y => ((((input m Q (Icc (c + 1) (c + M)) D0 s A
        (coordinateFreeze m E z y)).re -
      (squareStepModel m E z s A (Icc (c + 1) (c + M)) c M (leastSquare (D0 * ∏ j ∈ E, m j))
        (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, m j))) Q' y).re : ℝ)) : ℂ)) a = 0 := by
  set R := leastSquare (D0 * ∏ j ∈ E, m j) with hR
  set n := K * stepScale K M R with hn
  have hreal : (fun y => ((((input m Q (Icc (c + 1) (c + M)) D0 s A
      (coordinateFreeze m E z y)).re -
      (squareStepModel m E z s A (Icc (c + 1) (c + M)) c M R n Q' y).re : ℝ)) : ℂ)) =
      fun y => input m Q (Icc (c + 1) (c + M)) D0 s A (coordinateFreeze m E z y) -
        squareStepModel m E z s A (Icc (c + 1) (c + M)) c M R n Q' y := by
    funext y
    push_cast
    rw [input_real, Complex.conj_eq_iff_re.mp (conj_squareStepModel m E z s A _ c M R n Q' y)]
  rw [hreal]
  by_cases haE : ∀ i ∈ E, a i = 0
  · rw [groupCoeff_sub, groupCoeff_squareStepModel_sq m hK hD0 hcop0 hpair A c hM hHQ' hHQ a
      haE haH, sub_self]
  · push Not at haE
    apply groupCoeff_eq_zero_of_offE m E _ _ a haE
    intro y y' hyy
    have h1 : coordinateFreeze m E z y = coordinateFreeze m E z y' := by
      funext k
      unfold coordinateFreeze
      by_cases hk : k ∈ E
      · rw [ite_eq_left hk, ite_eq_left hk]
      · rw [ite_eq_right hk, ite_eq_right hk, hyy k hk]
    have h2 : squareStepModel m E z s A (Icc (c + 1) (c + M)) c M R n Q' y =
        squareStepModel m E z s A (Icc (c + 1) (c + M)) c M R n Q' y' := by
      unfold squareStepModel
      congr 1
      apply sum_congr rfl
      intro j _
      apply stepLift_congr
      intro k hk
      rw [stepMap_apply, stepMap_apply, hyy k hk]
    rw [h1, h2]

end Group

end Sarkozy.DensityDC
