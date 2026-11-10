module

public import Sarkozy.JointRows.RowsA

/-!
# The preliminaries of `lem:joint-rows` for the chart objects

Source: `paper/sections/16_extraction.tex`, `lem:joint-rows`, "Then `C_F` and `C_E` annihilate
the constants on both sides, `C_E = C_E*`", and the proof's preliminaries.

For `ν = gμ` with `g = K_E𝟙/Z_E = K_E*𝟙/Z_E` on the support (the marginal of `π_E`):
* `relDensity_mass`: `T_F = K_F/(Z_F g ⊗ g)` has mass one relative to `ν ⊗ ν`; hence
  `C_F = T_F - u_L ⊗ u_R` annihilates the constants (`foldCov_chart_annihilates`, via
  `Blocks.foldCov_annihilates`);
* `relDensity_exactMarginals`: `T_E` has marginal densities one; hence `C_E = T_E - J` annihilates
  the constants (`matchCov_chart_annihilates`);
* `RowsA.matchCov_symm` (`RowsA.lean`): `C_E` is symmetric when `K_E` is.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace RowsA

variable {Ω : Type*} [Fintype Ω]

/-- `T = K/(Z g ⊗ g)` has mass one relative to `ν ⊗ ν`, `ν = gμ`. -/
theorem relDensity_mass (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (hν : ∀ x, ν.weight x = g x * μ.weight x)
    (hg : ∀ x, μ.weight x ≠ 0 → 0 < g x) (K : Ω → Ω → ℝ) (hZ : mass μ K ≠ 0) :
    kf ν (relDensity μ K g) (fun _ => 1) (fun _ => 1) = 1 := by
  have h : kf ν (relDensity μ K g) (fun _ => 1) (fun _ => 1) = mass μ K / mass μ K := by
    unfold mass
    rw [show kf μ K (fun _ => 1) (fun _ => 1) / kf μ K (fun _ => 1) (fun _ => 1) =
      ∑ x, ∑ y, μ.weight x * μ.weight y * (1 * K x y * 1) / mass μ K by
        unfold mass kf; rw [Finset.sum_div]; exact Finset.sum_congr rfl fun x _ => by
          rw [Finset.sum_div]]
    unfold kf
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases hx : μ.weight x = 0
    · rw [hν x, hx]; simp
    by_cases hy : μ.weight y = 0
    · rw [hν y, hy]; simp
    have hgx := (hg x hx).ne'
    have hgy := (hg y hy).ne'
    rw [hν, hν]
    unfold relDensity
    field_simp
  rw [h, div_self hZ]

/-- **`C_F` annihilates the constants** (relative to `ν`). -/
theorem foldCov_chart_annihilates (μ ν : FiniteLaw Ω) (g : Ω → ℝ)
    (hν : ∀ x, ν.weight x = g x * μ.weight x) (hg : ∀ x, μ.weight x ≠ 0 → 0 < g x)
    (K : Ω → Ω → ℝ) (hZ : mass μ K ≠ 0) :
    (∀ x, kone ν (foldCov ν (relDensity μ K g)) x = 0) ∧
      (∀ y, kone' ν (foldCov ν (relDensity μ K g)) y = 0) :=
  foldCov_annihilates ν _ (relDensity_mass μ ν g hν hg K hZ)

/-- `T_E` has marginal densities one relative to `ν` when `g` is the marginal density. -/
theorem relDensity_exactMarginals (μ ν : FiniteLaw Ω) (g : Ω → ℝ)
    (hν : ∀ x, ν.weight x = g x * μ.weight x) (hg : ∀ x, μ.weight x ≠ 0 → 0 < g x)
    (K : Ω → Ω → ℝ) (hg1 : ∀ x, μ.weight x ≠ 0 → g x = dens1 μ K x)
    (hg2 : ∀ x, μ.weight x ≠ 0 → g x = dens2 μ K x) :
    ExactMarginals ν (relDensity μ K g) := by
  have hsupp : ∀ x, ν.weight x ≠ 0 → μ.weight x ≠ 0 := fun x hx h => hx (by rw [hν, h, mul_zero])
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have hx' := hsupp x hx
    rw [kone_relDensity μ ν g hν hg K x hx', ← hg1 x hx', div_self (hg x hx').ne']
  · have hy' := hsupp y hy
    rw [kone'_relDensity μ ν g hν hg K y hy', ← hg2 y hy', div_self (hg y hy').ne']

/-- **`C_E` annihilates the constants** (relative to `ν`). -/
theorem matchCov_chart_annihilates (μ ν : FiniteLaw Ω) (g : Ω → ℝ)
    (hν : ∀ x, ν.weight x = g x * μ.weight x) (hg : ∀ x, μ.weight x ≠ 0 → 0 < g x)
    (K : Ω → Ω → ℝ) (hg1 : ∀ x, μ.weight x ≠ 0 → g x = dens1 μ K x)
    (hg2 : ∀ x, μ.weight x ≠ 0 → g x = dens2 μ K x) :
    Annihilates ν (matchCov (relDensity μ K g)) :=
  matchCov_annihilates ν _ (relDensity_exactMarginals μ ν g hν hg K hg1 hg2)

end RowsA

end Sarkozy.JointRows
