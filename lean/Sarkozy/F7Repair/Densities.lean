module

public import Sarkozy.F7Repair.TwoLayer

@[expose] public section

/-!
# The one-way data from the density bounds of (F7) (proof of (F7), "Densities")

`paper/sections/26_upper_comparison.tex`, proof of (F7): "(F1) gives
`e^{-ℓ_U} ≤ dμ^old/dπ^new_j ≤ e^{ℓ_U}`, `dπ^new_j/dλ_H ≥ e^{-ℓ_new}` …; in the same way
`dπ^new/d(λ_H ⊗ λ_H) ≤ 2^{m_×} e^{2c⁺_H(∅) + c⁻_{G^new}(∅)}`, and dividing by the two marginal
densities gives `sup dπ^new/d(π^new_X ⊗ π^new_Y) ≤ K_∞²`", with
`K_∞ = (2^{m_×} exp(2c⁺_H(∅) + c⁻_{G^new}(∅) + 2ℓ_new))^{1/2}` and `U = e^{ℓ_U} − 1`.

* **`OneWayData.ofDensities`**: `OneWayData` from these density bounds (for any reference laws
  `lX`, `lY` of the halves), with `U = e^{ℓ_U} − 1` and `K_∞ = √M e^{ℓ_new}`; the correlation
  bound `ρ_new` (F2) and the gate `2F < 1` remain inputs, as in (F7);
* `mX_pairLaw`, `mY_pairLaw`: the marginal weights of a pair law are the laws of the halves;
* **`F7Record.ofDensities`**: an `F7Record` from the density statements of (F7) about `π^new`,
  `μ^old` and `λ_H`, the bound (F2) on `ρ_new`, the gate, and `ρ_old`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.Recentering Sarkozy.Structured Sarkozy.UpperComparison

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `|e^{±ℓ}`-bracketed ratio − 1| ≤ e^ℓ − 1`. -/
theorem abs_sub_le_of_exp_bounds {μ m ℓ : ℝ} (hm : 0 ≤ m) (h1 : Real.exp (-ℓ) * m ≤ μ)
    (h2 : μ ≤ Real.exp ℓ * m) : |μ - m| ≤ (Real.exp ℓ - 1) * m := by
  have e1 : 1 - Real.exp (-ℓ) ≤ Real.exp ℓ - 1 := by
    have a := Real.add_one_le_exp (-ℓ)
    have b := Real.add_one_le_exp ℓ
    linarith
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right e1 hm]
  · nlinarith

/-- **`OneWayData` from the density bounds of (F7)**: if `e^{-ℓ_U} ≤ dμ_X/dν_X, dμ_Y/dν_Y ≤ e^{ℓ_U}`,
`dν_X/dλ_X, dν_Y/dλ_Y ≥ e^{-ℓ_new}` and `dν/d(λ_X ⊗ λ_Y) ≤ M`, then the one-way data hold with
`U = e^{ℓ_U} − 1` and `K_∞ = √M e^{ℓ_new}`, given the correlation bound `ρ_new < 1` and the gate. -/
noncomputable def OneWayData.ofDensities (ν : FiniteLaw (X × Y)) (μX lX : FiniteLaw X)
    (μY lY : FiniteLaw Y) (ℓU ℓnew M ρ : ℝ) (hℓU : 0 ≤ ℓU) (hM : 0 ≤ M)
    (hUX : ∀ x, Real.exp (-ℓU) * mX ν x ≤ μX.weight x ∧ μX.weight x ≤ Real.exp ℓU * mX ν x)
    (hUY : ∀ y, Real.exp (-ℓU) * mY ν y ≤ μY.weight y ∧ μY.weight y ≤ Real.exp ℓU * mY ν y)
    (hnX : ∀ x, Real.exp (-ℓnew) * lX.weight x ≤ mX ν x)
    (hnY : ∀ y, Real.exp (-ℓnew) * lY.weight y ≤ mY ν y)
    (hJ : ∀ x y, ν.weight (x, y) ≤ M * lX.weight x * lY.weight y)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hcorr : CentredBound ν (margX ν) (margY ν) ρ)
    (hgate : 2 * ((Real.exp ℓU - 1) * (1 + Real.sqrt M * Real.exp ℓnew / (1 - ρ))) < 1) :
    OneWayData ν μX μY where
  U := Real.exp ℓU - 1
  ρ := ρ
  K := Real.sqrt M * Real.exp ℓnew
  U_nonneg := by linarith [Real.add_one_le_exp ℓU]
  ρ_nonneg := hρ0
  ρ_lt_one := hρ1
  K_nonneg := mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  twoF_lt := hgate
  dens_X x := abs_sub_le_of_exp_bounds (mX_nonneg ν x) (hUX x).1 (hUX x).2
  dens_Y y := abs_sub_le_of_exp_bounds (mY_nonneg ν y) (hUY y).1 (hUY y).2
  corr := hcorr
  sup x y := by
    have hE : 0 < Real.exp ℓnew := Real.exp_pos _
    have hx : lX.weight x ≤ Real.exp ℓnew * mX ν x := by
      have := mul_le_mul_of_nonneg_left (hnX x) hE.le
      rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
    have hy : lY.weight y ≤ Real.exp ℓnew * mY ν y := by
      have := mul_le_mul_of_nonneg_left (hnY y) hE.le
      rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
    have hK : (Real.sqrt M * Real.exp ℓnew) ^ 2 = M * Real.exp ℓnew ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hM]
    rw [hK]
    calc ν.weight (x, y) ≤ M * lX.weight x * lY.weight y := hJ x y
      _ ≤ M * (Real.exp ℓnew * mX ν x) * (Real.exp ℓnew * mY ν y) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hx hM) hy (lY.nonneg y)
          exact mul_nonneg hM (mul_nonneg hE.le (mX_nonneg ν x))
      _ = M * Real.exp ℓnew ^ 2 * mX ν x * mY ν y := by ring

variable {Ω : Type*} [Fintype Ω] [DecidableEq X] [DecidableEq Y]

/-- The first marginal weight of a pair law is the law of the first half. -/
theorem mX_pairLaw (lam : FiniteLaw Ω) (a : Ω → X) (b : Ω → Y) (x : X) :
    mX (pairLaw lam a b) x = (lam.map a).weight x := by
  have h1 := (pairLaw lam a b).expect_congr (f := fun p => if p.1 = x then (1 : ℝ) else 0)
    (g := fun p => if p.1 = x then 1 else 0) (fun _ => rfl)
  have e1 : (pairLaw lam a b).expect (fun p => if p.1 = x then (1 : ℝ) else 0) = mX (pairLaw lam a b) x := by
    rw [expect_fst (pairLaw lam a b) (fun x' => if x' = x then (1 : ℝ) else 0)]
    unfold FiniteLaw.expect
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
    rfl
  have e2 : (pairLaw lam a b).expect (fun p => if p.1 = x then (1 : ℝ) else 0) =
      (lam.map a).expect (fun x' => if x' = x then (1 : ℝ) else 0) := by
    rw [pairLaw_expect, FiniteLaw.expect_map]
    rfl
  have e3 : (lam.map a).expect (fun x' => if x' = x then (1 : ℝ) else 0) = (lam.map a).weight x := by
    unfold FiniteLaw.expect
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  clear h1
  rw [← e1, e2, e3]

/-- The second marginal weight of a pair law is the law of the second half. -/
theorem mY_pairLaw (lam : FiniteLaw Ω) (a : Ω → X) (b : Ω → Y) (y : Y) :
    mY (pairLaw lam a b) y = (lam.map b).weight y := by
  have e1 : (pairLaw lam a b).expect (fun p => if p.2 = y then (1 : ℝ) else 0) = mY (pairLaw lam a b) y := by
    rw [expect_snd (pairLaw lam a b) (fun y' => if y' = y then (1 : ℝ) else 0)]
    unfold FiniteLaw.expect
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
    rfl
  have e2 : (pairLaw lam a b).expect (fun p => if p.2 = y then (1 : ℝ) else 0) =
      (lam.map b).expect (fun y' => if y' = y then (1 : ℝ) else 0) := by
    rw [pairLaw_expect, FiniteLaw.expect_map]
    rfl
  have e3 : (lam.map b).expect (fun y' => if y' = y then (1 : ℝ) else 0) = (lam.map b).weight y := by
    unfold FiniteLaw.expect
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [← e1, e2, e3]

variable {O₀ O₁ Z : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
  [Fintype Z] [DecidableEq Z]

/-- **An `F7Record` from the statements of the proof of (F7)**: for `π^new` (`lamN`) with layers
where `λ_H` is, `e^{-ℓ_U} ≤ dμ^old/dπ^new_j ≤ e^{ℓ_U}` (`j = X, Y`), `dπ^new_j/dλ_H ≥ e^{-ℓ_new}`,
`dπ^new/d(λ_H ⊗ λ_H) ≤ M` (in (F7), `M = 2^{m_×} e^{2c⁺_H(∅) + c⁻_{G^new}(∅)}`), the bound (F2)
`ρ_new` on the centred correlation of `π^new`, the gate `2F < 1`, and `ρ_old` with its bound.
*All arguments are hypotheses* (the conclusions of (F1), (F2), (F6) at the prime). -/
noncomputable def F7Record.ofDensities {lamO : FiniteLaw (O₀ × O₁ × Fin 2 → Z)}
    {lamH : FiniteLaw (O₀ × O₁ → Z)} (lamN : FiniteLaw (O₀ × O₁ × Fin 2 → Z))
    (suppN : LayersSupported lamN lamH) (ℓU ℓnew M ρnew ρold : ℝ) (hℓU : 0 ≤ ℓU) (hM : 0 ≤ M)
    (hU0 : ∀ x, Real.exp (-ℓU) * (lamN.map lay0).weight x ≤ (oldHalf lamO).weight x ∧
      (oldHalf lamO).weight x ≤ Real.exp ℓU * (lamN.map lay0).weight x)
    (hU1 : ∀ x, Real.exp (-ℓU) * (lamN.map lay1).weight x ≤ (oldHalf lamO).weight x ∧
      (oldHalf lamO).weight x ≤ Real.exp ℓU * (lamN.map lay1).weight x)
    (hn0 : ∀ x, Real.exp (-ℓnew) * lamH.weight x ≤ (lamN.map lay0).weight x)
    (hn1 : ∀ x, Real.exp (-ℓnew) * lamH.weight x ≤ (lamN.map lay1).weight x)
    (hJ : ∀ x y, (pairLaw lamN lay0 lay1).weight (x, y) ≤ M * lamH.weight x * lamH.weight y)
    (hρ0 : 0 ≤ ρnew) (hρ1 : ρnew < 1)
    (hcorr : CentredBound (pairLaw lamN lay0 lay1) (margX (pairLaw lamN lay0 lay1))
      (margY (pairLaw lamN lay0 lay1)) ρnew)
    (hgate : 2 * ((Real.exp ℓU - 1) * (1 + Real.sqrt M * Real.exp ℓnew / (1 - ρnew))) < 1)
    (hρold : 0 ≤ ρold)
    (old_corr : ∀ h k, (oldHalf lamO).expect h = 0 → (oldHalf lamO).expect k = 0 →
      |lamO.expect (fun y => h (lay0 y) * k (lay1 y))| ≤
        ρold * nrm (oldHalf lamO) h * nrm (oldHalf lamO) k) :
    F7Record lamO lamH where
  lamN := lamN
  suppN := suppN
  D := OneWayData.ofDensities (pairLaw lamN lay0 lay1) (oldHalf lamO) lamH (oldHalf lamO) lamH
    ℓU ℓnew M ρnew hℓU hM
    (fun x => by rw [mX_pairLaw]; exact hU0 x) (fun y => by rw [mY_pairLaw]; exact hU1 y)
    (fun x => by rw [mX_pairLaw]; exact hn0 x) (fun y => by rw [mY_pairLaw]; exact hn1 y)
    hJ hρ0 hρ1 hcorr hgate
  ρold := ρold
  ρold_nonneg := hρold
  old_corr := old_corr

end Sarkozy.F7Repair
