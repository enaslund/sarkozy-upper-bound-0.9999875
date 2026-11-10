module

public import Sarkozy.JointRows.NormConsequences

/-! Normalization and recentering from full and centred raw-kernel bounds. -/

@[expose] public section

namespace Sarkozy.JointRows

open Sarkozy.FiveType

variable {X : Type*} [Fintype X]

theorem chart_bound_of_norm (μ : FiniteLaw X) (K : X → X → ℝ) {s d : ℝ}
    (hs0 : 0 ≤ s) (hs : PerpBound μ K s) (hd : NormBound μ K d) (hd1 : d < 1) :
    FormBound μ (RowsA.chartKernel μ K) (s / (1 - d) + d ^ 2 / (1 - d) ^ 2) := by
  have hmass := normBound_mass hd
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hmass
  have hden : 0 < 1 - d := by linarith
  have hZ : 1 - d ≤ RowsA.mass μ K := by
    have hh := (abs_le.mp hmass).1
    linarith
  have hZ0 : 0 < RowsA.mass μ K := hden.trans_le hZ
  have hmL := RowsA.nrm_dens1_sub_one μ K hmass hd1 (normBound_cen_kone hd)
  have hmR := RowsA.nrm_dens2_sub_one μ K hmass hd1 (normBound_cen_kone' hd)
  intro f g
  have hnf := FiveType.nrm_nonneg μ f
  have hng := FiveType.nrm_nonneg μ g
  have hperp : |kf μ K (cen μ f) (cen μ g)| ≤ s * nrm μ f * nrm μ g := by
    apply (hs _ _ (expect_cen _ _) (expect_cen _ _)).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (RowsA.nrm_cen_le μ f) hs0)
      (RowsA.nrm_cen_le μ g) (FiveType.nrm_nonneg _ _) (mul_nonneg hs0 hnf)
  have hleft : |ip μ f (fun x => RowsA.dens1 μ K x - 1)| ≤ nrm μ f * (d / (1 - d)) :=
    (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_left hmL hnf)
  have hright : |ip μ (fun x => RowsA.dens2 μ K x - 1) g| ≤ (d / (1 - d)) * nrm μ g :=
    (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_right hmR hng)
  rw [RowsA.chart_centring μ K hZ0.ne']
  calc
    _ ≤ |kf μ K (cen μ f) (cen μ g) / RowsA.mass μ K| +
        |ip μ f (fun x => RowsA.dens1 μ K x - 1) *
          ip μ (fun x => RowsA.dens2 μ K x - 1) g| := abs_sub _ _
    _ ≤ (s * nrm μ f * nrm μ g) / (1 - d) +
        (nrm μ f * (d / (1 - d))) * ((d / (1 - d)) * nrm μ g) := by
      rw [abs_div, abs_of_pos hZ0, abs_mul]
      apply add_le_add
      · exact (div_le_div_of_nonneg_right hperp hZ0.le).trans
          (div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hs0 hnf) hng) hden hZ)
      · exact mul_le_mul hleft hright (abs_nonneg _)
          (mul_nonneg hnf (div_nonneg hd0 hden.le))
    _ = _ := by field_simp

end Sarkozy.JointRows
