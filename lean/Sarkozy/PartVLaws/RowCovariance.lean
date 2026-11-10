module

public import Sarkozy.PartVLaws.RowDensity
public import Sarkozy.JointRows.ChartVariance

/-! The ten row kernels satisfy the required correlation bound in their actual variances. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Sarkozy.Labellings Sarkozy.JointRows Sarkozy.FiveType Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

theorem row_correlation_scalar (c : RowCase) :
    ((c.cap : ℝ) - 1 / 100) * (1 + 1 / 2 ^ 200) ≤ c.cap - 1 / 2 ^ 90 := by
  have hcap : (c.cap : ℝ) ≤ 258 := by cases c <;> norm_num [cap]
  linarith

theorem row_covariance_bound (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b)
    (f g : (c.Index → ZMod p) → ℝ) :
    |kf (c.strictLaw hp hW b hb)
      (covKernel (c.strictLaw hp hW b hb) c.rowKernel) f g| ≤
      (((c.cap : ℝ) - 1 / 2 ^ 90) * (Real.sqrt p)⁻¹) *
        Real.sqrt (wvar (c.strictLaw hp hW b hb)
          (margL (c.strictLaw hp hW b hb) c.rowKernel) f) *
        Real.sqrt (wvar (c.strictLaw hp hW b hb)
          (margR (c.strictLaw hp hW b hb) c.rowKernel) g) := by
  have h := chart_variance_bound (c.strictLaw hp hW b hb) c.rowKernel
    (c.row_mass_pos hp hW h4 b hb).ne' (c.row_chart_bound hp hW h4 b hb)
    (by positivity : (0 : ℝ) < 1 + 1 / 2 ^ 200)
    (fun x hx => (c.row_density_lower hp hW h4 b hb x hx).1)
    (fun y hy => (c.row_density_lower hp hW h4 b hb y hy).2) f g
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hc := mul_le_mul_of_nonneg_right c.row_correlation_scalar
    (by positivity : (0 : ℝ) ≤ (Real.sqrt p)⁻¹)
  convert hc using 1
  ring

end Sarkozy.PartVLaws.FieldGraphs.RowCase
