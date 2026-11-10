module

public import Sarkozy.PartVLaws.RowPinnedLaws
public import Sarkozy.Cuts.RestrictionInj

/-! Restricting the ten row star estimates to injective allowed labellings. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Sarkozy.Labellings Sarkozy.JointRows Sarkozy.JointRows.StarOps
  Sarkozy.FiveType Sarkozy.FiveType.Blocks

variable {p : ℕ} [Fact p.Prime]

theorem prob_injective_lower (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    1 - (1 : ℝ) / 1000000 ≤ Peyre.prob (blockLaw (c.coordinateLaw hp hW b hb))
      (fun x => Function.Injective x) := by
  let κ : ℝ := 2 ^ c.pins * (1 + 1 / 100000)
  have hκ : κ ≤ 32 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) c.pins_le
    have hm := mul_le_mul_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 1 + 1 / 100000)
    exact hm.trans (by norm_num)
  have h := Cuts.prob_injective_ge (c.coordinateLaw hp hW b hb)
    (κ := κ) (fun i a => by
      simpa only [ZMod.card] using c.coordinate_density hp hW b hb i a)
  simp only [ZMod.card] at h
  change 1 - ((Fintype.card c.Index).choose 2 : ℝ) * (κ / p) ≤
    Peyre.prob (blockLaw (c.coordinateLaw hp hW b hb)) (fun x => Function.Injective x) at h
  have hn : ((Fintype.card c.Index).choose 2 : ℝ) ≤ 66 := by
    have hn := Nat.choose_le_choose 2 c.card_index
    exact_mod_cast hn
  have hnum := mul_le_mul hn hκ (by dsimp [κ]; positivity) (by norm_num : (0 : ℝ) ≤ 66)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hlarge : (2 : ℝ) ^ 32 ≤ p := by exact_mod_cast (show 2 ^ 32 ≤ p by omega)
  have herr : ((Fintype.card c.Index).choose 2 : ℝ) * (κ / p) ≤ 1 / 1000000 := by
    rw [← mul_div_assoc, div_le_iff₀ hp0]
    calc
      _ ≤ 66 * 32 := hnum
      _ ≤ _ := by norm_num only [pow_succ, pow_zero, mul_one] at hlarge; linarith
  linarith

theorem prob_injective_pos (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    0 < Peyre.prob (blockLaw (c.coordinateLaw hp hW b hb))
      (fun x => Function.Injective x) :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 - 1 / 1000000)
    (c.prob_injective_lower hp hW b hb)

noncomputable def strictLaw (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) : FiniteLaw (c.Index → ZMod p) :=
  Peyre.condLaw (blockLaw (c.coordinateLaw hp hW b hb)) (fun x => Function.Injective x)
    (c.prob_injective_pos hp hW b hb)

theorem strict_star_bound (c : RowCase) (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (b : c.Index → ZMod p) (hb : Function.Injective b) :
    PerpBound (c.strictLaw hp hW b hb)
      (starKernel (c.coefficients (p := p)) (sets2 c.Index))
      (((c.cap : ℝ) - 3 / 100) * (Real.sqrt p)⁻¹) := by
  let lam := blockLaw (c.coordinateLaw hp hW b hb)
  let K := starKernel (p := p) (c.coefficients (p := p)) (sets2 c.Index)
  have hcap : (3 : ℝ) ≤ c.cap ∧ (c.cap : ℝ) ≤ 258 := by cases c <;> norm_num [cap]
  have hT : ∀ f g, lam.expect f = 0 → lam.expect g = 0 →
      |Cuts.kernelForm lam lam K f g| ≤
        (((c.cap : ℝ) - 1 / 25) * (Real.sqrt p)⁻¹) * nrm lam f * nrm lam g := by
    intro f g hf hg
    rw [← Restrict.kf_eq_kernelForm, kf_eq_bform]
    exact c.product_star_bound hp hW b hb f g hf hg
  intro f g hf hg
  rw [Restrict.kf_eq_kernelForm]
  have h := Cuts.restriction_centred_I0 lam lam (fun x => Function.Injective x)
    (fun x => Function.Injective x) (c.prob_injective_pos hp hW b hb)
    (c.prob_injective_pos hp hW b hb) (by norm_num : (0 : ℝ) < 1 - 1 / 1000000)
    (c.prob_injective_lower hp hW b hb) (c.prob_injective_lower hp hW b hb) K
    (mul_nonneg (by linarith : (0 : ℝ) ≤ c.cap - 1 / 25) (by positivity)) hT f g hf hg
  apply h.trans
  change (((c.cap : ℝ) - 1 / 25) * (Real.sqrt p)⁻¹) / (1 - 1 / 1000000) *
    nrm (c.strictLaw hp hW b hb) f * nrm (c.strictLaw hp hW b hb) g ≤ _
  have hs : ((c.cap : ℝ) - 1 / 25) / (1 - 1 / 1000000) ≤ c.cap - 3 / 100 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 1000000)]
    linarith [hcap.2]
  have hmul := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt p)⁻¹)
      (FiveType.nrm_nonneg (c.strictLaw hp hW b hb) f))
      (FiveType.nrm_nonneg (c.strictLaw hp hW b hb) g))
  convert hmul using 1 <;> ring

end Sarkozy.PartVLaws.FieldGraphs.RowCase
