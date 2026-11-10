module

public import Sarkozy.PartVLaws.RowCompletionCounts
public import Sarkozy.JointRows.UniformIndicator
public import Sarkozy.JointRows.LawEquivChart

/-! The raw row kernel in the graph coordinates, including its exact marginal counts. -/

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows Sarkozy.FiveType Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

noncomputable def rowKernel (c : RowCase) (x y : c.Index → ZMod p) : ℝ :=
  Coll.rawKer c.finSigns (c.labelEquiv x) (c.labelEquiv y)

theorem rowKernel_indicator (c : RowCase) (x y : c.Index → ZMod p) :
    c.rowKernel x y = if Coll.Compatible c.finSigns (c.labelEquiv x) (c.labelEquiv y)
      then (2 : ℝ) ^ (Coll.pairSet c.finSigns).card else 0 :=
  Coll.rawKer_indicator c.finSigns c.finSigns_cases _ _

theorem rowKernel_nonneg (c : RowCase) (x y : c.Index → ZMod p) : 0 ≤ c.rowKernel x y := by
  rw [c.rowKernel_indicator]
  split_ifs <;> positivity

theorem strictLaw_weight (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) (x : c.Index → ZMod p) :
    (c.strictLaw hp hW b hb).weight x = if x ∈ Coll.strictSet (c.allowed b)
      then ((Coll.strictSet (c.allowed b)).card : ℝ)⁻¹ else 0 :=
  Coll.strict_product_weight (c.allowed b) (c.allowed_nonempty hp hW b hb)
    (c.prob_injective_pos hp hW b hb) x

theorem strictLaw_support (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) {x : c.Index → ZMod p}
    (hx : (c.strictLaw hp hW b hb).weight x ≠ 0) : x ∈ Coll.strictSet (c.allowed b) := by
  by_contra h
  exact hx (by rw [c.strictLaw_weight]; exact ite_eq_right h)

theorem row_kone_count (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) (x : c.Index → ZMod p)
    (hx : x ∈ Coll.strictSet (c.allowed b)) :
    kone (c.strictLaw hp hW b hb) c.rowKernel x =
      (2 : ℝ) ^ (Coll.pairSet c.finSigns).card *
        ((Coll.strictSet (c.allowed b)).card : ℝ)⁻¹ *
          extCount c.rowGraph (c.pinnedDomain 0) (c.pack b x x) := by
  change (c.strictLaw hp hW b hb).expect (fun y => c.rowKernel x y) = _
  simp_rw [c.rowKernel_indicator]
  rw [Coll.uniform_indicator_sum _ _ (c.strictLaw_weight hp hW b hb),
    c.low_completion_count b x hb hx]

theorem row_kone'_count (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) (y : c.Index → ZMod p)
    (hy : y ∈ Coll.strictSet (c.allowed b)) :
    kone' (c.strictLaw hp hW b hb) c.rowKernel y =
      (2 : ℝ) ^ (Coll.pairSet c.finSigns).card *
        ((Coll.strictSet (c.allowed b)).card : ℝ)⁻¹ *
          extCount c.rowGraph (c.pinnedDomain 2) (c.pack b y y) := by
  change (c.strictLaw hp hW b hb).expect (fun x => c.rowKernel x y) = _
  simp_rw [c.rowKernel_indicator]
  rw [Coll.uniform_indicator_sum _ _ (c.strictLaw_weight hp hW b hb),
    c.high_completion_count b y hb hy]

theorem row_mass_error (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    |RowsA.mass (c.strictLaw hp hW b hb) c.rowKernel - 1| ≤
      2 ^ 44 * (Real.sqrt p)⁻¹ := by
  unfold rowKernel
  simpa only [finLaw, lawEquiv_mass] using c.fin_mass_error hp hW h4 b hb

theorem row_mass_pos (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    0 < RowsA.mass (c.strictLaw hp hW b hb) c.rowKernel := by
  have h := (abs_le.mp (c.row_mass_error hp hW h4 b hb)).1
  have hd := PinTail.deviation_small hp
  linarith

theorem row_chart_bound (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    FormBound (c.strictLaw hp hW b hb)
      (RowsA.chartKernel (c.strictLaw hp hW b hb) c.rowKernel)
      (((c.cap : ℝ) - 1 / 100) * (Real.sqrt p)⁻¹) := by
  have h := formBound_of_lawEquiv _ _ _ (c.fin_chart_bound hp hW h4 b hb)
  unfold rowKernel
  simpa only [finLaw, lawEquiv_chart] using h

end Sarkozy.PartVLaws.FieldGraphs.RowCase
