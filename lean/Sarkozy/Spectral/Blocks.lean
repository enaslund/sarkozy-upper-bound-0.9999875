module

public import Sarkozy.Mixing.TensorSpectrum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `cor:spectral-criterion-blocks`: blocks of primes

From the two conclusions of `thm:spectral-criterion` used here,
`-g_𝔠 p^{-1/2} ≤ Op ≤ 1 + B⁺/p` at every prime `p` of a block `Blk`, the tensor product over
the block satisfies `⊗_{p∈Blk} Op ⪰ -d b^{-1/2}` with `d = g_𝔠 exp(B⁺ L/(P log P))`, where
`P ≤ b = min Blk` and `∑_{p∈Blk} log p ≤ L`.

* `sum_inv_le_of_sum_log_le`: `lem:spec:tensorcomp`(c), `∑_{p∈Blk} 1/p ≤ L/(P log P)`.
* `blocks_lower`: the corollary, for real symmetric matrices `A_p` (the operators `Op` on
  `L²(μ_p)`, written in an orthonormal basis, e.g. after conjugation by `diag(√μ_p)`) with the
  quadratic-form bounds `-(g/√p) ‖x‖² ≤ xᵀ A_p x ≤ (1 + B/p) ‖x‖²`. It is the tensor-spectrum
  lemma `Sarkozy.Mixing.tensor_spectrum_exp` (`lem:sector`(g), the content of
  `lem:spec:tensorcomp`(b)) together with (c).

For both prime classes, apply `blocks_lower` with `g ≥ max(g₁, g₃)` and the larger `B⁺`.
-/

@[expose] public section

open scoped Matrix

namespace Sarkozy.Spectral

/-- **`lem:spec:tensorcomp`(c)**: if every `p_j ≥ P > 1` and `∑_j log p_j ≤ L`, then
`∑_j 1/p_j ≤ L/(P log P)`. -/
theorem sum_inv_le_of_sum_log_le {K : Type*} [Fintype K] (p : K → ℝ) {P L : ℝ} (hP : 1 < P)
    (hpP : ∀ j, P ≤ p j) (hL : ∑ j, Real.log (p j) ≤ L) :
    ∑ j, 1 / p j ≤ L / (P * Real.log P) := by
  have hlogP : 0 < Real.log P := Real.log_pos hP
  have hPlog : 0 < P * Real.log P := mul_pos (by linarith) hlogP
  have hterm : ∀ j, 1 / p j ≤ Real.log (p j) / (P * Real.log P) := by
    intro j
    have hpj : 1 < p j := lt_of_lt_of_le hP (hpP j)
    have hlogp : Real.log P ≤ Real.log (p j) := Real.log_le_log (by linarith) (hpP j)
    have hlogp0 : 0 < Real.log (p j) := Real.log_pos hpj
    have hmul : P * Real.log P ≤ p j * Real.log (p j) :=
      mul_le_mul (hpP j) hlogp hlogP.le (by linarith)
    calc 1 / p j = Real.log (p j) / (p j * Real.log (p j)) := by
          field_simp
      _ ≤ Real.log (p j) / (P * Real.log P) :=
          div_le_div_of_nonneg_left hlogp0.le hPlog hmul
  calc ∑ j, 1 / p j ≤ ∑ j, Real.log (p j) / (P * Real.log P) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (∑ j, Real.log (p j)) / (P * Real.log P) := by rw [Finset.sum_div]
    _ ≤ L / (P * Real.log P) := div_le_div_of_nonneg_right hL hPlog.le

variable {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*} [∀ j, Fintype (Ω j)]
  [∀ j, DecidableEq (Ω j)]

/-- **`cor:spectral-criterion-blocks`.** Let `A_p` be real symmetric with
`-(g/√p) ‖x‖² ≤ xᵀ A_p x ≤ (1 + B/p) ‖x‖²` for every prime `p` of a block (indexed by `K`), with
`g/√p ≤ 1`, all `p ≥ b ≥ P > 1` and `∑_p log p ≤ L`. Then
`⊗_p A_p ⪰ -d b^{-1/2}` with `d = g exp(B L/(P log P))`. -/
theorem blocks_lower (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) (hA : ∀ j, (A j)ᵀ = A j) (p : K → ℝ)
    {g B L P b : ℝ} (hg0 : 0 ≤ g) (hB0 : 0 ≤ B) (hP : 1 < P) (hbP : P ≤ b)
    (hpb : ∀ j, b ≤ p j) (hL : ∑ j, Real.log (p j) ≤ L) (hgr : ∀ j, g / √(p j) ≤ 1)
    (hlow : ∀ j x, -(g / √(p j)) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A j *ᵥ x))
    (hup : ∀ j x, x ⬝ᵥ (A j *ᵥ x) ≤ (1 + B / p j) * (x ⬝ᵥ x)) (x : (∀ j, Ω j) → ℝ) :
    -(g * Real.exp (B * L / (P * Real.log P)) / √b) * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (Sarkozy.IndexSupport.piKron A *ᵥ x) := by
  have hb : 0 < b := by linarith
  have hpos : ∀ j, 0 < p j := fun j => lt_of_lt_of_le hb (hpb j)
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb
  have hcb : ∀ j, g / √(p j) ≤ 1 + B / p j := fun j =>
    (hgr j).trans (by linarith [div_nonneg hB0 (hpos j).le])
  have hm : ∀ j, g / √(p j) ≤ g / √b := fun j =>
    div_le_div_of_nonneg_left hg0 hsb (Real.sqrt_le_sqrt (hpb j))
  have h := Sarkozy.Mixing.tensor_spectrum_exp A hA (fun j => B / p j) (fun j => g / √(p j))
    (fun j => div_nonneg hB0 (hpos j).le) hcb hlow hup (div_nonneg hg0 hsb.le) hm x
  -- `∑_p B/p ≤ B L/(P log P)`
  have hsum : ∑ j, B / p j ≤ B * L / (P * Real.log P) := by
    have h1 := sum_inv_le_of_sum_log_le p hP (fun j => hbP.trans (hpb j)) hL
    calc ∑ j, B / p j = B * ∑ j, 1 / p j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ B * (L / (P * Real.log P)) := mul_le_mul_of_nonneg_left h1 hB0
      _ = B * L / (P * Real.log P) := by ring
  have hexp := Real.exp_le_exp.mpr hsum
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hcmp : g / √b * Real.exp (∑ j, B / p j) ≤ g * Real.exp (B * L / (P * Real.log P)) / √b := by
    rw [div_mul_eq_mul_div, mul_comm g]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hg0) hsb.le |>.trans_eq
      (by ring)
  have := mul_le_mul_of_nonneg_right hcmp hxx
  linarith

end Sarkozy.Spectral
