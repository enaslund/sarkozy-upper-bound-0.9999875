module

public import Sarkozy.PartVLaws.RowKernel
public import Sarkozy.PartVLaws.TailSchur
public import Sarkozy.JointRows.MarginalRatio

/-! Both normalized row marginals have density at least 1 / (1 + 2^-200). -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows Sarkozy.FiveType Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

theorem row_kone_ratio (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) (x x' : c.Index → ZMod p)
    (hx : (c.strictLaw hp hW b hb).weight x ≠ 0)
    (hx' : (c.strictLaw hp hW b hb).weight x' ≠ 0) :
    kone (c.strictLaw hp hW b hb) c.rowKernel x ≤
      countRho p ^ 72 * kone (c.strictLaw hp hW b hb) c.rowKernel x' := by
  have hxs := c.strictLaw_support hp hW b hb hx
  have hxs' := c.strictLaw_support hp hW b hb hx'
  rw [c.row_kone_count hp hW b hb x hxs, c.row_kone_count hp hW b hb x' hxs']
  have h := mul_le_mul_of_nonneg_left
    (c.pinned_count_ratio hp hW b x x' hb hxs hxs' 0 (Or.inl rfl))
    (by positivity : 0 ≤ (2 : ℝ) ^ (Coll.pairSet c.finSigns).card *
      ((Coll.strictSet (c.allowed b)).card : ℝ)⁻¹)
  convert h using 1
  ring

theorem row_kone'_ratio (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) (y y' : c.Index → ZMod p)
    (hy : (c.strictLaw hp hW b hb).weight y ≠ 0)
    (hy' : (c.strictLaw hp hW b hb).weight y' ≠ 0) :
    kone' (c.strictLaw hp hW b hb) c.rowKernel y ≤
      countRho p ^ 72 * kone' (c.strictLaw hp hW b hb) c.rowKernel y' := by
  have hys := c.strictLaw_support hp hW b hb hy
  have hys' := c.strictLaw_support hp hW b hb hy'
  rw [c.row_kone'_count hp hW b hb y hys, c.row_kone'_count hp hW b hb y' hys']
  have h := mul_le_mul_of_nonneg_left
    (c.pinned_count_ratio hp hW b y y' hb hys hys' 2 (Or.inr rfl))
    (by positivity : 0 ≤ (2 : ℝ) ^ (Coll.pairSet c.finSigns).card *
      ((Coll.strictSet (c.allowed b)).card : ℝ)⁻¹)
  convert h using 1
  ring

theorem row_density_lower (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b) (x : c.Index → ZMod p)
    (hx : (c.strictLaw hp hW b hb).weight x ≠ 0) :
    (1 + (1 : ℝ) / 2 ^ 200)⁻¹ ≤ RowsA.dens1 (c.strictLaw hp hW b hb) c.rowKernel x ∧
    (1 + (1 : ℝ) / 2 ^ 200)⁻¹ ≤ RowsA.dens2 (c.strictLaw hp hW b hb) c.rowKernel x := by
  have hR : 0 < countRho p ^ 72 := lt_of_lt_of_le zero_lt_one
    (one_le_pow₀ (one_le_countRho p))
  have hinv : (1 + (1 : ℝ) / 2 ^ 200)⁻¹ ≤ (countRho p ^ 72)⁻¹ :=
    inv_anti₀ hR (countRho_pow_le p hp (by norm_num : 72 ≤ 288))
  exact ⟨hinv.trans (dens1_lower_of_ratio _ _ hR (c.row_mass_pos hp hW h4 b hb) x
      (fun x' hx' => c.row_kone_ratio hp hW b hb x' x hx' hx)),
    hinv.trans (dens2_lower_of_ratio _ _ hR (c.row_mass_pos hp hW h4 b hb) x
      (fun y hy => c.row_kone'_ratio hp hW b hb y x hy hx))⟩

end Sarkozy.PartVLaws.FieldGraphs.RowCase
