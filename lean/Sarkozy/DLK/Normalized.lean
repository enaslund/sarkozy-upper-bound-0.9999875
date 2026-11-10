module

public import Sarkozy.DLK.Basic
public import Sarkozy.Spectral.GlueMatching

/-!
# `cor:dl:normalized` for `a = b = 2`, from `thm:dl:K`

`paper/sections/15_second_order.tex`, `cor:dl:normalized`, the case `a = b = 2`, with real
functions (the formalization is real-valued throughout). `K(x, y) = ∏_{a,b ≤ 2} χ(ς_{ab}(y_b - x_a))`
is `Extraction.twoCycleRectangle ς`, with signs `ς_{ab} = ±1`; `Target.FourCycle` is `thm:dl:K`.

* `rectangle_bilinear`: counting form, `|∑_{x,y ∈ 𝔽_p²} f(x) K(x, y) h(y)| ≤ 2p ‖f‖ ‖h‖` for `f`, `h`
  vanishing on the diagonal.
* `normalized_two`: **`eq:dl:normalized`** for `a = b = 2`, uniform probability on `𝔽_p²`:
  `|E_{x,y} f(x) K(x, y) h(y)| ≤ (2/p) ‖f‖₂ ‖h‖₂`.
* `normalized_two_density`: **`cor:dl:normalized`(b)** for `a = b = 2`: for measures `ν₁, ν₂` on
  `𝔽_p²` (weights `ν x ≥ 0`) vanishing on the diagonal, with densities at most `D₁, D₂` relative
  to uniform probability (`p² ν x ≤ D`),
  `|E_{x∼ν₁, y∼ν₂} f(x) K(x, y) h(y)| ≤ (2/p) √(D₁D₂) ‖f‖_{ν₁} ‖h‖_{ν₂}`. The proof does not use
  that `ν₁`, `ν₂` have mass one.

The general case `a, b ≥ 2` is in `DLK/NormalizedGeneral.lean`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DLK

open Sarkozy Sarkozy.Influence Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

/-- A function vanishing on the diagonal has the same sum over `𝔽_p²` and over the ordered pairs
of distinct elements. -/
theorem sum_offDiag_eq (F : ZMod p × ZMod p → ℝ) (hF : ∀ x : ZMod p × ZMod p, x.1 = x.2 → F x = 0) :
    ∑ x ∈ twoCycleOffDiag p, F x = ∑ x, F x :=
  sum_subset (subset_univ _) fun x _ hx => hF x (by
    by_contra h
    exact hx (mem_filter.mpr ⟨mem_univ _, h⟩))

/-- **`cor:dl:normalized`(a), `a = b = 2`, counting form**, from `thm:dl:K`: for `f`, `h` on `𝔽_p²`
vanishing on the diagonal, `|∑_{x,y} f(x) K(x, y) h(y)| ≤ 2p (∑ f²)^{1/2} (∑ h²)^{1/2}`. -/
theorem rectangle_bilinear (hDLK : Target.FourCycle) (hp2 : p ≠ 2) {ς : Fin 2 → Fin 2 → ZMod p}
    (hς : ∀ a b, ς a b = 1 ∨ ς a b = -1) (f h : ZMod p × ZMod p → ℝ)
    (hf : ∀ x : ZMod p × ZMod p, x.1 = x.2 → f x = 0)
    (hh : ∀ y : ZMod p × ZMod p, y.1 = y.2 → h y = 0) :
    |∑ x, ∑ y, f x * twoCycleRectangle ς x y * h y| ≤
      2 * (p : ℝ) * Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ y, h y ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hop := fourCycleBound hDLK hp2 ς hς
  rw [Real.sq_sqrt hp0.le] at hop
  have hb := Spectral.bilinear_of_opBound_on (twoCycleOffDiag p) (twoCycleOffDiag p) _
    (by positivity) hop f h
  have e1 : ∑ x, ∑ y, f x * twoCycleRectangle ς x y * h y =
      ∑ x ∈ twoCycleOffDiag p, ∑ y ∈ twoCycleOffDiag p, f x * twoCycleRectangle ς x y * h y := by
    rw [← sum_offDiag_eq _ fun x hx => by simp [hf x hx]]
    exact sum_congr rfl fun x _ => (sum_offDiag_eq _ fun y hy => by simp [hh y hy]).symm
  have e2 : ∑ x ∈ twoCycleOffDiag p, f x ^ 2 = ∑ x, f x ^ 2 :=
    sum_offDiag_eq _ fun x hx => by simp [hf x hx]
  have e3 : ∑ y ∈ twoCycleOffDiag p, h y ^ 2 = ∑ y, h y ^ 2 :=
    sum_offDiag_eq _ fun y hy => by simp [hh y hy]
  rw [e1, ← e2, ← e3]
  exact hb

/-- **`eq:dl:normalized`, `cor:dl:normalized`(a) for `a = b = 2`**, from `thm:dl:K`: for uniform
probability on `𝔽_p²` and `f`, `h` vanishing on the diagonal,
`|E_{x,y} f(x) K(x, y) h(y)| ≤ (2/p) ‖f‖₂ ‖h‖₂`. Equivalently, the operator with kernel `K`
relative to uniform probability, compressed to the functions vanishing on the diagonal, has norm
at most `2/p = 2r²`. -/
theorem normalized_two (hDLK : Target.FourCycle) (hp2 : p ≠ 2) {ς : Fin 2 → Fin 2 → ZMod p}
    (hς : ∀ a b, ς a b = 1 ∨ ς a b = -1) (f h : ZMod p × ZMod p → ℝ)
    (hf : ∀ x : ZMod p × ZMod p, x.1 = x.2 → f x = 0)
    (hh : ∀ y : ZMod p × ZMod p, y.1 = y.2 → h y = 0) :
    |(1 / (p : ℝ) ^ 4) * ∑ x, ∑ y, f x * twoCycleRectangle ς x y * h y| ≤
      (2 / p) * Real.sqrt ((1 / (p : ℝ) ^ 2) * ∑ x, f x ^ 2) *
        Real.sqrt ((1 / (p : ℝ) ^ 2) * ∑ y, h y ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hb := rectangle_bilinear hDLK hp2 hς f h hf hh
  have hs : ∀ S : ℝ, Real.sqrt ((1 / (p : ℝ) ^ 2) * S) = (1 / p) * Real.sqrt S := by
    intro S
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity), Real.sqrt_one,
      Real.sqrt_sq hp0.le]
  rw [hs, hs, abs_mul, abs_of_pos (by positivity)]
  calc 1 / (p : ℝ) ^ 4 * |∑ x, ∑ y, f x * twoCycleRectangle ς x y * h y|
      ≤ 1 / (p : ℝ) ^ 4 * (2 * (p : ℝ) * Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ y, h y ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 / p * (1 / p * Real.sqrt (∑ x, f x ^ 2)) * (1 / p * Real.sqrt (∑ y, h y ^ 2)) := by
        field_simp

/-- **`cor:dl:normalized`(b) for `a = b = 2`**, from `thm:dl:K`: let `ν₁, ν₂ ≥ 0` be weights on
`𝔽_p²` (measures) vanishing on the diagonal, with densities relative to uniform probability at
most `D₁, D₂` (`p² ν_i ≤ D_i`). Then for all `f`, `h`,
`|∑_{x,y} ν₁(x) f(x) K(x, y) ν₂(y) h(y)| ≤ (2/p) √(D₁ D₂) (∑ ν₁ f²)^{1/2} (∑ ν₂ h²)^{1/2}`,
i.e. `|E_{x∼ν₁, y∼ν₂} f K h| ≤ (2/p) √(D₁D₂) ‖f‖_{ν₁} ‖h‖_{ν₂}`. -/
theorem normalized_two_density (hDLK : Target.FourCycle) (hp2 : p ≠ 2)
    {ς : Fin 2 → Fin 2 → ZMod p} (hς : ∀ a b, ς a b = 1 ∨ ς a b = -1)
    (ν₁ ν₂ : ZMod p × ZMod p → ℝ) (hν₁ : ∀ x, 0 ≤ ν₁ x) (hν₂ : ∀ y, 0 ≤ ν₂ y)
    (hd₁ : ∀ x : ZMod p × ZMod p, x.1 = x.2 → ν₁ x = 0)
    (hd₂ : ∀ y : ZMod p × ZMod p, y.1 = y.2 → ν₂ y = 0) {D₁ D₂ : ℝ}
    (hD₁ : ∀ x, (p : ℝ) ^ 2 * ν₁ x ≤ D₁) (hD₂ : ∀ y, (p : ℝ) ^ 2 * ν₂ y ≤ D₂)
    (f h : ZMod p × ZMod p → ℝ) :
    |∑ x, ∑ y, ν₁ x * f x * twoCycleRectangle ς x y * (ν₂ y * h y)| ≤
      (2 / p) * Real.sqrt (D₁ * D₂) * Real.sqrt (∑ x, ν₁ x * f x ^ 2) *
        Real.sqrt (∑ y, ν₂ y * h y ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hb := rectangle_bilinear hDLK hp2 hς (fun x => ν₁ x * f x) (fun y => ν₂ y * h y)
    (fun x hx => by simp [hd₁ x hx]) (fun y hy => by simp [hd₂ y hy])
  have hsq : ∀ (ν : ZMod p × ZMod p → ℝ) (D : ℝ) (g : ZMod p × ZMod p → ℝ), (∀ x, 0 ≤ ν x) →
      (∀ x, (p : ℝ) ^ 2 * ν x ≤ D) →
      ∑ x, (ν x * g x) ^ 2 ≤ (D / (p : ℝ) ^ 2) * ∑ x, ν x * g x ^ 2 := by
    intro ν D g hν hD
    rw [mul_sum]
    refine sum_le_sum fun x _ => ?_
    have h1 : ν x ≤ D / (p : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith [hD x]
    have h2 : 0 ≤ ν x * g x ^ 2 := mul_nonneg (hν x) (sq_nonneg _)
    calc (ν x * g x) ^ 2 = ν x * (ν x * g x ^ 2) := by ring
      _ ≤ D / (p : ℝ) ^ 2 * (ν x * g x ^ 2) := mul_le_mul_of_nonneg_right h1 h2
  have hD₁0 : 0 ≤ D₁ := by
    have := hD₁ (0, 0); have := hν₁ (0, 0); nlinarith
  have hD₂0 : 0 ≤ D₂ := by
    have := hD₂ (0, 0); have := hν₂ (0, 0); nlinarith
  have s1 := Real.sqrt_le_sqrt (hsq ν₁ D₁ f hν₁ hD₁)
  have s2 := Real.sqrt_le_sqrt (hsq ν₂ D₂ h hν₂ hD₂)
  have e : ∀ (D S : ℝ), 0 ≤ D → 0 ≤ S →
      Real.sqrt (D / (p : ℝ) ^ 2 * S) = (1 / p) * Real.sqrt D * Real.sqrt S := by
    intro D S hD hS
    rw [Real.sqrt_mul (div_nonneg hD (by positivity)), Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hp0.le]
    ring
  rw [e D₁ _ hD₁0 (sum_nonneg fun x _ => mul_nonneg (hν₁ x) (sq_nonneg _))] at s1
  rw [e D₂ _ hD₂0 (sum_nonneg fun x _ => mul_nonneg (hν₂ x) (sq_nonneg _))] at s2
  have e2 : ∑ x, ∑ y, ν₁ x * f x * twoCycleRectangle ς x y * (ν₂ y * h y) =
      ∑ x, ∑ y, (ν₁ x * f x) * twoCycleRectangle ς x y * (ν₂ y * h y) := rfl
  rw [e2]
  refine hb.trans ?_
  rw [Real.sqrt_mul hD₁0]
  have hA : 0 ≤ Real.sqrt (∑ x, (ν₁ x * f x) ^ 2) := Real.sqrt_nonneg _
  have hB : 0 ≤ Real.sqrt (∑ y, (ν₂ y * h y) ^ 2) := Real.sqrt_nonneg _
  calc 2 * (p : ℝ) * Real.sqrt (∑ x, (ν₁ x * f x) ^ 2) * Real.sqrt (∑ y, (ν₂ y * h y) ^ 2)
      ≤ 2 * (p : ℝ) * ((1 / p) * Real.sqrt D₁ * Real.sqrt (∑ x, ν₁ x * f x ^ 2)) *
          ((1 / p) * Real.sqrt D₂ * Real.sqrt (∑ y, ν₂ y * h y ^ 2)) := by
        have h2p : 0 ≤ 2 * (p : ℝ) := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left s1 h2p) s2 hB (by positivity)
    _ = 2 / p * (Real.sqrt D₁ * Real.sqrt D₂) * Real.sqrt (∑ x, ν₁ x * f x ^ 2) *
          Real.sqrt (∑ y, ν₂ y * h y ^ 2) := by
        field_simp

end Sarkozy.DLK
