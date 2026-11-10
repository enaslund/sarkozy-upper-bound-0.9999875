module

public import Sarkozy.PartVLaws.RowFullBound
public import Sarkozy.JointRows.ChartBound
public import Sarkozy.JointRows.PinnedChartScalars

/-! Normalized, recentered kernel bounds for all ten tail rows on their reference laws. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Sarkozy.Labellings Sarkozy.JointRows Sarkozy.FiveType Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

theorem fin_mass_error (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    |RowsA.mass (c.finLaw hp hW b hb) (Coll.rawKer c.finSigns) - 1| ≤
      2 ^ 44 * (Real.sqrt p)⁻¹ :=
  normBound_mass (c.fin_raw_full hp hW h4 b hb)

theorem fin_marginal_error (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    nrm (c.finLaw hp hW b hb)
        (cen (c.finLaw hp hW b hb) (kone (c.finLaw hp hW b hb) (Coll.rawKer c.finSigns))) ≤
      2 ^ 44 * (Real.sqrt p)⁻¹ ∧
    nrm (c.finLaw hp hW b hb)
        (cen (c.finLaw hp hW b hb) (kone' (c.finLaw hp hW b hb) (Coll.rawKer c.finSigns))) ≤
      2 ^ 44 * (Real.sqrt p)⁻¹ :=
  ⟨normBound_cen_kone (c.fin_raw_full hp hW h4 b hb),
    normBound_cen_kone' (c.fin_raw_full hp hW h4 b hb)⟩

theorem fin_chart_bound (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    FormBound (c.finLaw hp hW b hb)
      (RowsA.chartKernel (c.finLaw hp hW b hb) (Coll.rawKer c.finSigns))
      (((c.cap : ℝ) - 1 / 100) * (Real.sqrt p)⁻¹) := by
  have hcap : (3 : ℝ) ≤ c.cap ∧ (c.cap : ℝ) ≤ 258 := by cases c <;> norm_num [cap]
  have hs0 : 0 ≤ ((c.cap : ℝ) - 1 / 50) * (Real.sqrt p)⁻¹ :=
    mul_nonneg (by linarith [hcap.1]) (by positivity)
  have hd1 : (2 : ℝ) ^ 44 * (Real.sqrt p)⁻¹ < 1 :=
    (PinTail.deviation_small hp).trans_lt (by norm_num)
  have h := chart_bound_of_norm (c.finLaw hp hW b hb) (Coll.rawKer c.finSigns)
    hs0 (c.fin_raw_bound hp hW h4 b hb) (c.fin_raw_full hp hW h4 b hb) hd1
  exact Blocks.FormBound.mono h (PinTail.chart_tail_scalar hp hcap.1 hcap.2)

end Sarkozy.PartVLaws.FieldGraphs.RowCase
