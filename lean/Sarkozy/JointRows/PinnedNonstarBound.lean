module

public import Sarkozy.JointRows.PinnedNonstarTerm
public import Sarkozy.JointRows.CollNonstar
public import Sarkozy.JointRows.RowsC

/-! Summing singleton extraction over every nonstar subset in a pinned tail row. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.PinTail

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK Sarkozy.FiveType

variable {p n : ℕ} [Fact p.Prime]

theorem nonstar_bound (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (M : Finset (ZMod p)) (hz : M.card ≤ 12) (pin : Fin n → ZMod p → ℤ)
    (hpin : ∀ j t, pin j t = 0 ∨ pin j t = 1 ∨ pin j t = -1)
    (hpinM : ∀ j t, pin j t ≠ 0 → t ∈ M) (hcount : ∀ j, pinCount pin j ≤ 4)
    (ς : Fin n → Fin n → ℤ) (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1)
    (μ : FiniteLaw (Fin n → ZMod p))
    (hμ : ∀ x, μ.weight x = if x ∈ pinLab M pin then
      (((pinLab M pin).card : ℝ))⁻¹ else 0) :
    FormBound μ (Coll.nsKer ς) (2 ^ 179 * (Real.sqrt p)⁻¹ ^ 2) := by
  have hcard : (Coll.pairSet ς).card ≤ 144 := by
    have hc := card_le_univ (Coll.pairSet ς)
    simp only [Fintype.card_prod, Fintype.card_fin] at hc
    nlinarith
  have hc : ((nonstars (Coll.pairSet ς)).card : ℝ) ≤ 2 ^ 144 := by
    exact_mod_cast (calc
      (nonstars (Coll.pairSet ς)).card ≤ (Coll.pairSet ς).powerset.card := card_filter_le _ _
      _ = 2 ^ (Coll.pairSet ς).card := card_powerset _
      _ ≤ 2 ^ 144 := Nat.pow_le_pow_right (by omega) hcard)
  have hsum := formBound_sum (nonstars (Coll.pairSet ς))
    (K := fun S x y => ∏ e ∈ S, chiPair ς e x y)
    (e := fun _ => 2 ^ 35 * (Real.sqrt p)⁻¹ ^ 2) (fun S hS =>
      Coll.formBound_of_normalized μ (pinLab M pin) hμ _
        (nonstar_monomial hp hn hW h4 M hz pin hpin hpinM hcount ς hς S
          (mem_nonstars.mp hS).2 (fun e he =>
            (mem_filter.mp ((mem_nonstars.mp hS).1 he)).2)))
  apply Blocks.FormBound.mono hsum
  rw [sum_const, nsmul_eq_mul]
  calc
    _ ≤ 2 ^ 144 * (2 ^ 35 * (Real.sqrt p)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

omit [Fact p.Prime] in
theorem nonstar_tail_scalar (hp : 2 ^ 512 ≤ p) :
    (2 : ℝ) ^ 179 * (Real.sqrt p)⁻¹ ^ 2 ≤ 2⁻¹ ^ 77 * (Real.sqrt p)⁻¹ := by
  have hr := mul_le_mul_of_nonneg_right (SpectralD.tail_rp_le hp)
    (by positivity : 0 ≤ (Real.sqrt p)⁻¹)
  have hs := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ 2 ^ 179)
  nlinarith [inv_nonneg.mpr (Real.sqrt_nonneg p)]

end Sarkozy.JointRows.PinTail
