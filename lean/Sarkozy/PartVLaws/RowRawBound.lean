module

public import Sarkozy.PartVLaws.RowFinLaw
public import Sarkozy.JointRows.StarEquiv
public import Sarkozy.JointRows.PinnedRemainder

/-! The full raw pinned kernel for each of the ten tail rows. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Sarkozy.Labellings Sarkozy.JointRows Sarkozy.JointRows.StarOps
  Sarkozy.FiveType Sarkozy.Extraction

noncomputable def finSigns (c : RowCase)
    (i j : Fin (Fintype.card c.Index)) : ℤ :=
  c.crossSign (c.indexEquiv.symm i) (c.indexEquiv.symm j)

theorem finSigns_cases (c : RowCase) (i j : Fin (Fintype.card c.Index)) :
    c.finSigns i j = 0 ∨ c.finSigns i j = 1 ∨ c.finSigns i j = -1 :=
  c.crossSign_cases _ _

variable {p : ℕ} [Fact p.Prime]

theorem fin_star_eq (c : RowCase) (x y : c.Index → ZMod p) :
    Coll.starKer c.finSigns (c.labelEquiv x) (c.labelEquiv y) =
      starKernel (c.coefficients (p := p)) (sets2 c.Index) x y := by
  rw [starKer_eq_characterStar, starKernel_equiv c.indexEquiv]
  simp only [characterSigns, finSigns, labelEquiv,
    Equiv.arrowCongr_apply, Function.comp_def, Equiv.refl_apply, Equiv.symm_apply_apply]
  rfl

theorem fin_star_bound (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    PerpBound (c.finLaw hp hW b hb) (Coll.starKer c.finSigns)
      (((c.cap : ℝ) - 3 / 100) * (Real.sqrt p)⁻¹) := by
  apply perpBound_lawEquiv
  simpa only [c.fin_star_eq] using c.strict_star_bound hp hW b hb

theorem fin_raw_bound (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    PerpBound (c.finLaw hp hW b hb) (Coll.rawKer c.finSigns)
      (((c.cap : ℝ) - 1 / 50) * (Real.sqrt p)⁻¹) := by
  have h := PinTail.raw_perp hp c.card_index hW h4 (c.fixedLabels b)
    (c.card_fixedLabels b) (c.pinData b) (c.pinData_cases b hb) (c.pinData_mem b)
    (c.pinData_count b hb) c.finSigns c.finSigns_cases (c.finLaw hp hW b hb)
    (c.finLaw_weight hp hW b hb) (c.fin_star_bound hp hW b hb)
  have he : (2 : ℝ) ^ 180 * (Real.sqrt p)⁻¹ ^ 2 ≤ (1 / 100) * (Real.sqrt p)⁻¹ := by
    have hr := mul_le_mul_of_nonneg_right (SpectralD.tail_rp_le hp)
      (by positivity : 0 ≤ (Real.sqrt p)⁻¹)
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ 2 ^ 180)
    nlinarith [inv_nonneg.mpr (Real.sqrt_nonneg p)]
  intro f g hf hg
  apply (h f g hf hg).trans
  have hcoef : ((c.cap : ℝ) - 3 / 100) * (Real.sqrt p)⁻¹ +
      2 ^ 180 * (Real.sqrt p)⁻¹ ^ 2 ≤ (c.cap - 1 / 50) * (Real.sqrt p)⁻¹ := by
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (FiveType.nrm_nonneg _ _))
    (FiveType.nrm_nonneg _ _)

end Sarkozy.PartVLaws.FieldGraphs.RowCase
