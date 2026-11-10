module

public import Sarkozy.F3Kernel.AnchorArithmetic
public import Sarkozy.F3Kernel.GraphWeights

/-!
# Real correctness of the production factor tables

Every entry of the stored LL20/LL22 tables bounds the required square root at `q = 2^60`,
with 36 excluded labels. The comparisons are exact rational kernel reductions.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem LL20_table_integrated : ∀ s : Fin 21,
    rationalFactor s 36 810 ≤ ((factorEntry LL20 LL20.FT s : ℚ) / 2 ^ 64) ^ 2 := by
  decide +kernel

theorem LL20_table_cover : ∀ s : Fin 21,
    rationalFactor s 72 134112 ≤ ((factorEntry LL20 (rhoTable LL20) s : ℚ) / 2 ^ 64) ^ 2 := by
  decide +kernel

theorem LL22_table_integrated : ∀ s : Fin 21,
    rationalFactor s 36 1528 ≤ ((factorEntry LL22 LL22.FT s : ℚ) / 2 ^ 64) ^ 2 := by
  decide +kernel

theorem LL22_table_cover : ∀ s : Fin 21,
    rationalFactor s 72 1117056 ≤ ((factorEntry LL22 (rhoTable LL22) s : ℚ) / 2 ^ 64) ^ 2 := by
  decide +kernel

theorem sqrt_le_rational_table {x : ℝ} {u : ℚ} {v : ℕ} (hx : x ≤ u)
    (hu : u ≤ ((v : ℚ) / 2 ^ 64) ^ 2) : Real.sqrt x ≤ value64 v := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨value64_nonneg v, hx.trans ?_⟩
  unfold value64
  have hu' : (u : ℝ) ≤ (((v : ℚ) / 2 ^ 64) ^ 2 : ℚ) := Rat.cast_le.mpr hu
  push_cast at hu'
  exact hu'

theorem LL20_gradedTableBounds :
    GradedTableBounds LL20 GraphData.graph20 GraphData.sign20 productionAnchor 36 where
  q_pos := productionAnchor_pos
  error_lt_one := gpEhat_anchor_lt_one _ GraphData.degree20_sup
  integrated s hs := by
    have hs' : s < 21 := by change s ≤ 20 at hs; omega
    exact sqrt_le_rational_table
      (grLeafFm_anchor_le _ _ GraphData.degree20_sup s 810 (GraphData.leafS_m20 s))
      (LL20_table_integrated ⟨s, hs'⟩)
  cover s hs := by
    have hs' : s < 21 := by change s ≤ 20 at hs; omega
    exact sqrt_le_rational_table
      (grLeafFrho_anchor_le _ _ GraphData.degree20_sup s 134112 (GraphData.leafS_rho20 s))
      (LL20_table_cover ⟨s, hs'⟩)

theorem LL22_gradedTableBounds :
    GradedTableBounds LL22 GraphData.graph22 GraphData.sign22 productionAnchor 36 where
  q_pos := productionAnchor_pos
  error_lt_one := gpEhat_anchor_lt_one _ GraphData.degree22_sup
  integrated s hs := by
    have hs' : s < 21 := by change s ≤ 20 at hs; omega
    exact sqrt_le_rational_table
      (grLeafFm_anchor_le _ _ GraphData.degree22_sup s 1528 (GraphData.leafS_m22 s))
      (LL22_table_integrated ⟨s, hs'⟩)
  cover s hs := by
    have hs' : s < 21 := by change s ≤ 20 at hs; omega
    exact sqrt_le_rational_table
      (grLeafFrho_anchor_le _ _ GraphData.degree22_sup s 1117056 (GraphData.leafS_rho22 s))
      (LL22_table_cover ⟨s, hs'⟩)

end Sarkozy.F3Kernel
