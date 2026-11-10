module

public import Sarkozy.JointRows.PinnedNonstarBound
public import Sarkozy.JointRows.PinnedCollisionScalars

/-! Complete nonstar and collision form bounds on strict pinned reference laws. -/

@[expose] public section

namespace Sarkozy.JointRows.PinTail

open Sarkozy.FiveType Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

variable {p n : ℕ} [Fact p.Prime]

theorem collision_form (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12) (hW : WeilBound (ZMod p))
    (M : Finset (ZMod p)) (hz : M.card ≤ 12) (pin : Fin n → ZMod p → ℤ)
    (hpin : ∀ j t, pin j t = 0 ∨ pin j t = 1 ∨ pin j t = -1)
    (hpinM : ∀ j t, pin j t ≠ 0 → t ∈ M) (hcount : ∀ j, pinCount pin j ≤ 4)
    (ς : Fin n → Fin n → ℤ) (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1)
    (μ : FiniteLaw (Fin n → ZMod p))
    (hμ : ∀ x, μ.weight x = if x ∈ pinLab M pin then
      (((pinLab M pin).card : ℝ))⁻¹ else 0) :
    FormBound μ (pinKer ς) (2 ^ 49 * (Real.sqrt p)⁻¹ ^ 2) := by
  have he : ePin (Fintype.card (ZMod p)) n M.card 4 < 1 := by
    rw [ZMod.card]
    exact (count_error hp hn hz).trans_lt (by norm_num)
  have hop := pinned_collision_opBound hW M pin hpin hpinM 4 hcount he ς hς
  simp only [ZMod.card] at hop
  exact Blocks.FormBound.mono
    (Coll.formBound_of_opBound μ (pinLab M pin) hμ _ (Real.sqrt_nonneg _) hop)
    (collision_bound hp hn hz ς)

theorem raw_perp (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (M : Finset (ZMod p)) (hz : M.card ≤ 12) (pin : Fin n → ZMod p → ℤ)
    (hpin : ∀ j t, pin j t = 0 ∨ pin j t = 1 ∨ pin j t = -1)
    (hpinM : ∀ j t, pin j t ≠ 0 → t ∈ M) (hcount : ∀ j, pinCount pin j ≤ 4)
    (ς : Fin n → Fin n → ℤ) (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1)
    (μ : FiniteLaw (Fin n → ZMod p))
    (hμ : ∀ x, μ.weight x = if x ∈ pinLab M pin then
      (((pinLab M pin).card : ℝ))⁻¹ else 0)
    {s : ℝ} (hstar : PerpBound μ (Coll.starKer ς) s) :
    PerpBound μ (Coll.rawKer ς) (s + 2 ^ 180 * (Real.sqrt p)⁻¹ ^ 2) := by
  have hns := nonstar_bound hp hn hW h4 M hz pin hpin hpinM hcount ς hς μ hμ
  have hcoll := collision_form hp hn hW M hz pin hpin hpinM hcount ς hς μ hμ
  intro f g hf hg
  have heq : kf μ (Coll.rawKer ς) f g = kf μ (Coll.starKer ς) f g +
      kf μ (Coll.nsKer ς) f g - kf μ (pinKer ς) f g := by
    simp only [kf, Coll.rawKer_expansion]
    simp only [mul_add, mul_sub, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    have hconst : (∑ x, ∑ y, μ.weight x * μ.weight y * (f x * 1 * g y)) = 0 := by
      calc
        _ = μ.expect f * μ.expect g := by
          unfold FiniteLaw.expect
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ = 0 := by rw [hf, zero_mul]
    rw [hconst, zero_add]
  rw [heq]
  have h1 := hstar f g hf hg
  have h2 := hns f g
  have h3 := hcoll f g
  have hnrm := mul_nonneg (FiveType.nrm_nonneg μ f) (FiveType.nrm_nonneg μ g)
  have hs : (2 : ℝ) ^ 179 + 2 ^ 49 ≤ 2 ^ 180 := by norm_num
  have hh := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (sq_nonneg ((Real.sqrt p)⁻¹)) hnrm)
  calc
    _ ≤ |kf μ (Coll.starKer ς) f g| + |kf μ (Coll.nsKer ς) f g| +
        |kf μ (pinKer ς) f g| := (abs_sub _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith

end Sarkozy.JointRows.PinTail
