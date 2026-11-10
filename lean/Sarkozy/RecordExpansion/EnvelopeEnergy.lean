module

public import Sarkozy.RecordExpansion.SubsetExpansion

/-!
# Envelope energies (`lem:envelope-energy`)

`lem:envelope-energy` of the paper (`paper/sections/10_comparison_lemmas.tex`) bounds the
single-half random-inclusion energy of the envelopes `M_B = Ñ_B + Q_B`:

  `V ≤ (B e^{T_Q} ∏_{e ∈ 𝒮} (κ_e^{2θ/d} R_I) + o(1)) Y`.

Its proof has three steps:
1. fix the revealed data `𝒥` and the intervals;
2. expand `⊗_B (Ñ_B + Q_B)` over the sets `Z` of atoms carrying `Q_B`, and bound each term
   by (E1) under the bracket (`lem:bracket-energy`), with the slot prices of the index
   data, as `(B + o(1)) ∏_{B ∈ Z} ‖Q_B‖ q_B^{2a} Π_𝒥 Y`, where
   `∏_Z(1 + ‖Q_B‖ q_B^{2a}) ≤ e^{T_Q}`;
3. average over `𝒥`, with `E_𝒥 Π_𝒥 = ∏_e κ_e^{2θ/d} R_I` (`lem:hyb:moment`).

This file proves the expansion and summation of step 2 and the averaging of step 3, for
inputs that differ between the slots:

* `multilinear_add_eq_sum`: `Λ_{⊗(A+R)}((a_v)_v) = ∑_{X'} Λ_{⊗(R on X', A off X')}((a_v)_v)`;
* `abs_multilinear_add_le_exp`: per-term bounds `≤ K ∏_{B ∈ X'} u_B` give
  `|Λ_{⊗(A+R)}| ≤ K e^{U}`;
* `envelope_energy_le`: averaged over a law of `𝒥`, with per-term bounds
  `K(𝒥) ∏_{X'} u_B`, `V ≤ E_𝒥 K(𝒥) · e^{U}`. With `K(𝒥) = (B + z) Π_𝒥 Y` and
  `E_𝒥 Π_𝒥 = ∏_e κ_e^{2θ/d} R_I` this is `lem:envelope-energy`.

The per-term bounds (E1) and the moment identity are hypotheses. WP-FI's
`Sarkozy.Functional.conductorMoment_eq` (`Sarkozy/Functional/ConductorMoment.lean`)
computes the one-query conductor moment of `lem:hyb:moment`. The independence of the
queries, which turns the moment of the product into the product of the moments, is the
hypothesis `hmoment`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- The multilinear form of a product of two-term laws, expanded over subsets. -/
theorem multilinear_add_eq_sum (A R : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (a : V → (∀ b, X b) → ℝ) :
    multilinearIntegral (tensorLaw fun b => A b + R b) a =
      ∑ f : J → Bool, multilinearIntegral (tensorLaw fun b => if f b then R b else A b) a := by
  rw [tensorLaw_add_eq_sum]
  unfold multilinearIntegral
  exact LinearMap.sum_apply _ _ _

/-- **The summed bound for slot-dependent inputs**: per-term bounds `K ∏_{B ∈ X'} u_B`
give `|Λ_{⊗(A+R)}((a_v)_v)| ≤ K ∏_B (1 + u_B) ≤ K e^{∑ u}`. -/
theorem abs_multilinear_add_le_exp (A R : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (a : V → (∀ b, X b) → ℝ) (u : J → ℝ) (hu : ∀ b, 0 ≤ u b) {K : ℝ} (hK : 0 ≤ K)
    (hterm : ∀ f : J → Bool,
      |multilinearIntegral (tensorLaw fun b => if f b then R b else A b) a| ≤
        K * ∏ b, (if f b then u b else 1)) :
    |multilinearIntegral (tensorLaw fun b => A b + R b) a| ≤ K * Real.exp (∑ b, u b) := by
  rw [multilinear_add_eq_sum]
  have hprod : ∏ b, (1 + u b) = ∑ f : J → Bool, ∏ b, (if f b then u b else 1) := by
    rw [← Fintype.prod_sum (fun b (i : Bool) => if i then u b else 1)]
    apply Finset.prod_congr rfl
    intro b _
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    exact add_comm _ _
  calc |∑ f : J → Bool, multilinearIntegral (tensorLaw fun b => if f b then R b else A b) a|
      ≤ ∑ f : J → Bool, |multilinearIntegral (tensorLaw fun b => if f b then R b else A b) a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f : J → Bool, K * ∏ b, (if f b then u b else 1) := Finset.sum_le_sum fun f _ => hterm f
    _ = K * ∏ b, (1 + u b) := by rw [hprod, Finset.mul_sum]
    _ ≤ K * Real.exp (∑ b, u b) := mul_le_mul_of_nonneg_left (prod_one_add_le_exp u hu) hK

/-- **`lem:envelope-energy`, expansion and averaging**: for a law `P𝒥` of the revealed data,
slot inputs `a 𝒥`, and per-term bounds `K 𝒥 ∏_{B ∈ X'} u_B` at every `𝒥`,
`E_𝒥 Λ_{⊗(Ñ+Q)}((a_v^𝒥)_v) ≤ E_𝒥 K(𝒥) · e^{∑ u}`. -/
theorem envelope_energy_le {Ω : Type*} [Fintype Ω] (PJ : FiniteLaw Ω)
    (N Q : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (a : Ω → V → (∀ b, X b) → ℝ) (u : J → ℝ)
    (hu : ∀ b, 0 ≤ u b) (K : Ω → ℝ) (hK : ∀ 𝒥, 0 ≤ K 𝒥)
    (hterm : ∀ 𝒥 (f : J → Bool),
      |multilinearIntegral (tensorLaw fun b => if f b then Q b else N b) (a 𝒥)| ≤
        K 𝒥 * ∏ b, (if f b then u b else 1)) :
    PJ.expect (fun 𝒥 => multilinearIntegral (tensorLaw fun b => N b + Q b) (a 𝒥)) ≤
      PJ.expect K * Real.exp (∑ b, u b) := by
  calc PJ.expect (fun 𝒥 => multilinearIntegral (tensorLaw fun b => N b + Q b) (a 𝒥))
      ≤ PJ.expect (fun 𝒥 => K 𝒥 * Real.exp (∑ b, u b)) := by
        apply PJ.expect_mono
        intro 𝒥
        exact (le_abs_self _).trans (abs_multilinear_add_le_exp N Q (a 𝒥) u hu (hK 𝒥) (hterm 𝒥))
    _ = PJ.expect K * Real.exp (∑ b, u b) := PJ.expect_mul_const _ _

/-- **`lem:envelope-energy` with the paper's constants**: if the per-term bounds are
`(B + z) Π_𝒥 Y ∏_{B ∈ X'} u_B` (E1 under the bracket) and `E_𝒥 Π_𝒥 = Π̄`
(`lem:hyb:moment`, `Π̄ = ∏_e κ_e^{2θ/d} R_I`), then `V ≤ (B + z) e^{T_Q} Π̄ Y` for every
`T_Q ≥ ∑_B u_B`. -/
theorem envelope_energy_le_paper {Ω : Type*} [Fintype Ω] (PJ : FiniteLaw Ω)
    (N Q : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (a : Ω → V → (∀ b, X b) → ℝ) (u : J → ℝ)
    (hu : ∀ b, 0 ≤ u b) {Bz Y TQ Pbar : ℝ} (hBz : 0 ≤ Bz) (hY : 0 ≤ Y)
    (hTQ : ∑ b, u b ≤ TQ) (Pj : Ω → ℝ) (hPj : ∀ 𝒥, 0 ≤ Pj 𝒥)
    (hterm : ∀ 𝒥 (f : J → Bool),
      |multilinearIntegral (tensorLaw fun b => if f b then Q b else N b) (a 𝒥)| ≤
        Bz * Pj 𝒥 * Y * ∏ b, (if f b then u b else 1))
    (hmoment : PJ.expect Pj = Pbar) :
    PJ.expect (fun 𝒥 => multilinearIntegral (tensorLaw fun b => N b + Q b) (a 𝒥)) ≤
      Bz * Real.exp TQ * Pbar * Y := by
  have h := envelope_energy_le PJ N Q a u hu (fun 𝒥 => Bz * Pj 𝒥 * Y)
    (fun 𝒥 => mul_nonneg (mul_nonneg hBz (hPj 𝒥)) hY) hterm
  have hE : PJ.expect (fun 𝒥 => Bz * Pj 𝒥 * Y) = Bz * Pbar * Y := by
    have h1 : (fun 𝒥 => Bz * Pj 𝒥 * Y) = fun 𝒥 => Bz * (Pj 𝒥 * Y) := by
      funext 𝒥; ring
    rw [h1, PJ.expect_const_mul, PJ.expect_mul_const, hmoment]
    ring
  rw [hE] at h
  have hPbar : 0 ≤ Pbar := by
    rw [← hmoment]
    exact PJ.expect_nonneg hPj
  have hexp : Real.exp (∑ b, u b) ≤ Real.exp TQ := Real.exp_le_exp.mpr hTQ
  calc PJ.expect (fun 𝒥 => multilinearIntegral (tensorLaw fun b => N b + Q b) (a 𝒥))
      ≤ Bz * Pbar * Y * Real.exp (∑ b, u b) := h
    _ ≤ Bz * Pbar * Y * Real.exp TQ :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg (mul_nonneg hBz hPbar) hY)
    _ = Bz * Real.exp TQ * Pbar * Y := by ring

end Sarkozy.RecordExpansion
