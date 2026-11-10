module

public import Sarkozy.CompSharp.FoldGen
public import Sarkozy.NormBoundsPaper4.Sanity

@[expose] public section

/-!
# Sanity checks for C38: optimality of `34` in the numerical step; a toy `FoldInputsC`

* **`compNumeric_ge`**: every `δ` with `CompNumeric δ` has `δ(s) > 34/s` (take `e = 0`,
  `Z = H²`, where `X₁ = T/H > 30/s` and `X₂ > 4/s`). So `34` is the best leading constant SD2's
  separable Paley + Schur argument gives with its channel constants (`T = (15√p + 8)p²` in
  `Vk_form`, and the `J_C` part).
* **`foldInputsC_crude`**: `FoldInputsC` holds for the paper's components at every middle block
  of the F1 data with crude piece constants (`s_F = (2 + t)∑p`, `a_F = (1 + t)∑p`, `ℓ = 0`) and
  `c_B = 34`, `R = 1000`: the structure is satisfiable at the paper's objects (FD's
  `foldPrime_crude` for `sym`, `skew`; `comp34_paper` for `comp`).
-/

open Finset

namespace Sarkozy.CompSharp

open Sarkozy.PrimeGram Sarkozy.SignedGram Sarkozy.SignedComponents
open Sarkozy.SignedDecomp
open Sarkozy.NormBoundsPaper4 (foldPrime_crude)
open Sarkozy.PartV (MiddleNonempty)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MainFinalF1 (bOf Blk)
open Sarkozy.PartVLaws (blockPrimes)

/-- **`34` is optimal for the numerical step**: if `CompNumeric δ` then `34/s < δ(s)` for every
`s ≥ 4096` (at `e = 0`, `Z = H²`). -/
theorem compNumeric_ge {δ : ℝ → ℝ} (hδ : CompNumeric δ) {s : ℝ} (hs : 4096 ≤ s) :
    34 / s < δ s := by
  set H := s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2 with hHdef
  set T := (15 * s + 8) * (s ^ 2) ^ 2 with hTdef
  have hs0 : 0 < s := by linarith
  have hS0 : 0 < s ^ 2 := by positivity
  have hs2 : 4096 ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by norm_num) hs 2
  have hp1 : 0 < s ^ 2 - 1 := by nlinarith
  have hp2 : 0 < s ^ 2 - 2 := by nlinarith
  have hH0 : 0 < H := by rw [hHdef]; positivity
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hZ : H ^ 2 - T * H ≤ H ^ 2 := by nlinarith
  have h := hδ s 0 (H ^ 2) hs le_rfl (by positivity) hZ
  have e1 : (0 ^ 2 * H + T) * (H / (1 - 0)) / H ^ 2 = T / H := by
    field_simp; ring
  rw [e1, ← hHdef] at h
  -- `T/H > 30/s`
  have h1 : 30 / s < T / H := by
    rw [div_lt_div_iff₀ hs0 hH0, hTdef, hHdef]
    have : 0 < 45 * s ^ 4 - 30 * s ^ 2 + 8 * s ^ 5 := by nlinarith [pow_pos hs0 4, pow_pos hs0 5]
    nlinarith [this]
  -- `X₂ > 4/s` at `e = 0`
  have h2 : 4 / s < 2 * (s ^ 2 / (s ^ 2 - 1) * ((s + 1) * (s ^ 2) ^ 2)) * (1 + 0) / H := by
    have hw : s ^ 2 / (s ^ 2 - 1) * (s ^ 2 - 1) = s ^ 2 := div_mul_cancel₀ _ hp1.ne'
    rw [div_lt_div_iff₀ hs0 hH0]
    refine lt_of_mul_lt_mul_right ?_ hp1.le
    have key : (s ^ 2 - 1) ^ 2 * (s ^ 2 - 2) < s ^ 5 * (s + 1) := by
      have e2 : s ^ 5 * (s + 1) - (s ^ 2 - 1) ^ 2 * (s ^ 2 - 2) =
          s ^ 5 + 4 * s ^ 4 - 5 * s ^ 2 + 2 := by ring
      have : 0 < s ^ 5 + 4 * s ^ 4 - 5 * s ^ 2 + 2 := by
        nlinarith [pow_pos hs0 5, pow_pos hs0 4, pow_pos hs0 3]
      linarith
    calc 4 * H * (s ^ 2 - 1) = s ^ 2 * ((s ^ 2 - 1) ^ 2 * (s ^ 2 - 2)) * 2 := by
          rw [hHdef]; ring
      _ < s ^ 2 * (s ^ 5 * (s + 1)) * 2 := by
          have := mul_lt_mul_of_pos_left key hS0
          linarith
      _ = (s ^ 2 / (s ^ 2 - 1) * (s ^ 2 - 1)) * (2 * ((s + 1) * (s ^ 2) ^ 2) * (1 + 0) * s) := by
          rw [hw]; ring
      _ = 2 * (s ^ 2 / (s ^ 2 - 1) * ((s + 1) * (s ^ 2) ^ 2)) * (1 + 0) * s * (s ^ 2 - 1) := by
          ring
  have e3 : 34 / s = 30 / s + 4 / s := by rw [← add_div]; norm_num
  rw [e3]
  linarith

/-- **A toy `FoldInputsC`** at the paper's components of every middle block of the F1 data, with
crude piece constants `s_F = (2 + t)∑p`, `a_F = (1 + t)∑p`, `ℓ = 0` and `c_B = 34`, `R = 1000`. -/
theorem foldInputsC_crude {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) :
    FoldInputsC (blockPrimes bOf b) hne (paperComponents Dc)
      ((2 + tPaper) * ∑ j, (blockPrimes bOf b j : ℝ))
      ((1 + tPaper) * ∑ j, (blockPrimes bOf b j : ℝ)) 0 34 1000 := by
  set pr := blockPrimes bOf b
  have ht := tPaper_nonneg
  have hrq : ∀ i, rP pr i ^ 2 = (pr i : ℝ)⁻¹ := fun i => by
    rw [rP, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hp : ∀ i, (0 : ℝ) < pr i := fun i => by
    have := (Fact.out : (pr i).Prime).pos
    exact_mod_cast this
  have hsum : ∀ i, (pr i : ℝ) ≤ ∑ j, (pr j : ℝ) := fun i =>
    single_le_sum (f := fun j => (pr j : ℝ)) (fun j _ => (hp j).le) (mem_univ i)
  have hge : ∀ i {c : ℝ}, 0 ≤ c → c ≤ c * (∑ j, (pr j : ℝ)) * rP pr i ^ 2 := fun i c hc => by
    rw [hrq, mul_assoc, ← div_eq_mul_inv]
    have : 1 ≤ (∑ j, (pr j : ℝ)) / pr i := by rw [le_div_iff₀ (hp i)]; linarith [hsum i]
    nlinarith
  refine FoldInputsC.ofPaper34 Dc (fun i => ?_) (fun i => ?_)
  · refine (foldPrime_crude _ ht (1 / 2) (1 / 2) 1 i).mono ?_
    have e : (1 + tPaper) * (|(1 : ℝ) / 2| + |(1 : ℝ) / 2|) + |(1 : ℝ)| = 2 + tPaper := by
      norm_num; ring
    rw [e]
    exact hge i (by positivity)
  · refine (foldPrime_crude _ ht (1 / 2) (-1 / 2) 0 i).mono ?_
    have e : (1 + tPaper) * (|(1 : ℝ) / 2| + |(-1 : ℝ) / 2|) + |(0 : ℝ)| = 1 + tPaper := by
      norm_num
    rw [e, zero_mul, zero_add]
    exact hge i (by positivity)

end Sarkozy.CompSharp
