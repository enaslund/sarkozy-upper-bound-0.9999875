module

public import Sarkozy.PartVLaws.RowRawBound
public import Sarkozy.JointRows.StarFullTail
public import Sarkozy.JointRows.NormConsequences

/-! Full kernel bounds that supply the tail rows' normalizer and marginal errors. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Sarkozy.Labellings Sarkozy.JointRows Sarkozy.JointRows.StarOps
  Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

theorem coordinate_density_coarse (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (b : c.Index → ZMod p) (hb : Function.Injective b)
    (i : c.Index) (a : ZMod p) : (c.coordinateLaw hp hW b hb i).weight a ≤ 32 / p := by
  apply (c.coordinate_density hp hW b hb i a).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
  have h := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) c.pins_le)
    (by norm_num : (0 : ℝ) ≤ 1 + 1 / 100000)
  exact h.trans (by norm_num)

theorem coordinate_mean_full (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (b : c.Index → ZMod p) (hb : Function.Injective b)
    (i : c.Index) (t : ZMod p) (ht : t ∉ c.fixedLabels b) :
    |mchi (c.coordinateLaw hp hW b hb i) t| ≤ 1024 * (Real.sqrt p)⁻¹ :=
  PinCoordinate.mean_bound hp hW (c.roots b i) (c.roots_injective b hb i)
    (c.signs (p := p) i) (c.signs_pm i) (c.fixedLabels b) (c.roots_mem b i)
    ((c.card_pins i).trans c.pins_le) (c.card_fixedLabels b)
    (c.allowed_nonempty hp hW b hb i) t ht

theorem product_star_full (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    FormBound (blockLaw (c.coordinateLaw hp hW b hb))
      (starKernel (c.coefficients (p := p)) (sets2 c.Index))
      (2 ^ 42 * (Real.sqrt p)⁻¹) :=
  star_full_tail hp c.card_index (c.coordinateLaw hp hW b hb) (c.coefficients (p := p))
    c.abs_coefficients_le_one (c.coordinate_density_coarse hp hW b hb)
    (fun i j t ht => c.coordinate_mean_full hp hW b hb j t
      (c.charged_avoids hp hW b hb i t ht))

theorem strict_star_full (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    FormBound (c.strictLaw hp hW b hb)
      (starKernel (c.coefficients (p := p)) (sets2 c.Index))
      (2 ^ 43 * (Real.sqrt p)⁻¹) := by
  let lam := blockLaw (c.coordinateLaw hp hW b hb)
  let K := starKernel (p := p) (c.coefficients (p := p)) (sets2 c.Index)
  have hs := c.product_star_full hp hW b hb
  have hT : ∀ f g, |Cuts.kernelForm lam lam K f g| ≤
      2 ^ 42 * (Real.sqrt p)⁻¹ * nrm lam f * nrm lam g := by
    intro f g
    rw [← Restrict.kf_eq_kernelForm]
    exact hs f g
  have hP := c.prob_injective_pos hp hW b hb
  intro f g
  rw [Restrict.kf_eq_kernelForm]
  have h := Cuts.restriction_full lam lam (fun x => Function.Injective x)
    (fun x => Function.Injective x) hP hP K hT f g
  rw [Real.sqrt_mul_self hP.le] at h
  have hcoef : (2 ^ 42 * (Real.sqrt p)⁻¹) /
      Peyre.prob lam (fun x => Function.Injective x) ≤ 2 ^ 43 * (Real.sqrt p)⁻¹ := by
    rw [div_le_iff₀ hP]
    have hhalf : (1 / 2 : ℝ) ≤ Peyre.prob lam (fun x => Function.Injective x) :=
      le_trans (by norm_num) (c.prob_injective_lower hp hW b hb)
    have hh := mul_le_mul_of_nonneg_left hhalf
      (by positivity : (0 : ℝ) ≤ 2 ^ 43 * (Real.sqrt p)⁻¹)
    nlinarith
  apply h.trans
  change _ * nrm (c.strictLaw hp hW b hb) f * nrm (c.strictLaw hp hW b hb) g ≤ _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (FiveType.nrm_nonneg _ _)) (FiveType.nrm_nonneg _ _)

theorem fin_star_full (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    FormBound (c.finLaw hp hW b hb) (Coll.starKer c.finSigns)
      (2 ^ 43 * (Real.sqrt p)⁻¹) := by
  apply formBound_lawEquiv
  simpa only [c.fin_star_eq] using c.strict_star_full hp hW b hb

theorem fin_raw_full (c : RowCase) (hp : 2 ^ 512 ≤ p)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    NormBound (c.finLaw hp hW b hb) (Coll.rawKer c.finSigns)
      (2 ^ 44 * (Real.sqrt p)⁻¹) := by
  have hns := PinTail.nonstar_bound hp c.card_index hW h4 (c.fixedLabels b)
    (c.card_fixedLabels b) (c.pinData b) (c.pinData_cases b hb) (c.pinData_mem b)
    (c.pinData_count b hb) c.finSigns c.finSigns_cases (c.finLaw hp hW b hb)
    (c.finLaw_weight hp hW b hb)
  have hcoll := PinTail.collision_form hp c.card_index hW (c.fixedLabels b)
    (c.card_fixedLabels b) (c.pinData b) (c.pinData_cases b hb) (c.pinData_mem b)
    (c.pinData_count b hb) c.finSigns c.finSigns_cases (c.finLaw hp hW b hb)
    (c.finLaw_weight hp hW b hb)
  have h := normBound_of_parts (c.finLaw hp hW b hb) _ _ _ _
    (Coll.rawKer_expansion c.finSigns) (c.fin_star_full hp hW b hb) hns hcoll
  have hcoef : (2 : ℝ) ^ 43 * (Real.sqrt p)⁻¹ + 2 ^ 179 * (Real.sqrt p)⁻¹ ^ 2 +
      2 ^ 49 * (Real.sqrt p)⁻¹ ^ 2 ≤ 2 ^ 44 * (Real.sqrt p)⁻¹ := by
    have hr := mul_le_mul_of_nonneg_right (SpectralD.tail_rp_le hp)
      (by positivity : 0 ≤ (Real.sqrt p)⁻¹)
    have hh := mul_le_mul_of_nonneg_left hr
      (by positivity : (0 : ℝ) ≤ 2 ^ 179 + 2 ^ 49)
    nlinarith [inv_nonneg.mpr (Real.sqrt_nonneg p)]
  intro f g
  exact (h f g).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (FiveType.nrm_nonneg _ _)) (FiveType.nrm_nonneg _ _))

end Sarkozy.PartVLaws.FieldGraphs.RowCase
