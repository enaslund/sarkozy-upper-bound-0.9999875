module

public import Sarkozy.PositiveRoots.CoherentCubeFrame
public import Sarkozy.SpectralC.FiniteFrame

/-! The fifteen core character products have frame price `1 + 42r + 56q`. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD
open scoped BigOperators symmDiff

def nonemptySets (U : Type*) [Fintype U] [DecidableEq U] : Finset (Finset U) :=
  univ.filter fun S => S.Nonempty

abbrev CoreSupport := nonemptySets (Fin 4)

theorem core_support_card : Fintype.card CoreSupport = 15 := by decide +kernel

variable {p : ℕ} [Fact p.Prime]

theorem uniform_psi_pair {U : Type*} [Fintype U] [DecidableEq U]
    (S T : Finset U) (x : U → ZMod p) :
    (FiniteLaw.uniform (ZMod p)).expect
      (fun z => StarMatrix.psi S z x * StarMatrix.psi T z x) =
        (p : ℝ) * ∑ z, starKer S x z * starKer T x z := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [FiniteLaw.expect_uniform, ZMod.card, sum_div, mul_sum]
  apply sum_congr rfl
  intro z _
  unfold starKer StarMatrix.psi
  field_simp

theorem core_character_diagonal (S : Finset (Fin 4)) (x : Fin 4 → ZMod p) :
    (FiniteLaw.uniform (ZMod p)).expect (fun z => StarMatrix.psi S z x ^ 2) ≤ 1 := by
  apply FiniteLaw.expect_le_const
  intro z
  exact (sq_le_one_iff_abs_le_one _).mpr (abs_prod_chiRe_le S x z)

theorem core_character_entry (hW : Labellings.WeilBound (ZMod p))
    (S T : Finset (Fin 4)) (hST : S ≠ T) (x : Fin 4 → ZMod p)
    (hx : Function.Injective x) :
    |(FiniteLaw.uniform (ZMod p)).expect
      (fun z => StarMatrix.psi S z x * StarMatrix.psi T z x)| ≤
        3 * rp p + 4 * (p : ℝ)⁻¹ := by
  rw [uniform_psi_pair]
  have h := abs_sum_starKer_mul_le S T x hx.injOn
  have hw := abs_starMean_le hW (symmDiff_nonempty.mpr hST) x hx.injOn
  have hd : ((S ∆ T).card : ℝ) ≤ 4 := by
    exact_mod_cast (card_le_univ (S ∆ T))
  have hc : ((S ∩ T).card : ℝ) ≤ 4 := by
    exact_mod_cast (card_le_univ (S ∩ T))
  have hr := rp_nonneg (p := p)
  have hq : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  nlinarith

theorem core_character_frame (hW : Labellings.WeilBound (ZMod p))
    (x : Fin 4 → ZMod p) (hx : Function.Injective x) (u : CoreSupport → ℝ) :
    (FiniteLaw.uniform (ZMod p)).expect
      (fun z => (∑ S : CoreSupport, u S * StarMatrix.psi S.val z x) ^ 2) ≤
        (1 + 42 * rp p + 56 * (p : ℝ)⁻¹) * ∑ S, u S ^ 2 := by
  have hM := finiteFrame_gram_bound (FiniteLaw.uniform (ZMod p))
    (fun (S : CoreSupport) z => StarMatrix.psi S.val z x)
    (by have := rp_nonneg (p := p); positivity : 0 ≤ 3 * rp p + 4 * (p : ℝ)⁻¹)
    (fun S => core_character_diagonal S.val x)
    (fun S T hST => core_character_entry hW S.val T.val
      (fun he => hST (Subtype.ext he)) x hx)
  have h := finiteFrame_synthesis (FiniteLaw.uniform (ZMod p))
    (fun (S : CoreSupport) z => StarMatrix.psi S.val z x) hM u
  rw [core_support_card] at h
  convert h using 1
  push_cast
  ring

end Sarkozy.PositiveRoots.CoherentFrame
