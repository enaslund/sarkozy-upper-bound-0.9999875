module

public import Sarkozy.PositiveRoots.CoherentCoreCharacters

/-! Mixed star means: a private Paley factor and the fifteen core characters. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD
open Sarkozy.JointRows.StarOps Sarkozy.FiveType.Blocks
open scoped BigOperators

abbrev PrivateSupport := nonemptySets (Fin 2)

variable {p : ℕ} [Fact p.Prime]

noncomputable def privateCube (p : ℕ) [Fact p.Prime] : FiniteLaw (Fin 2 → ZMod p) :=
  blockLaw (fun _ : Fin 2 => FiniteLaw.uniform (ZMod p))

noncomputable def mixedMean (A : CoreSupport) (B : PrivateSupport)
    (c : Fin 4 → ZMod p) (b : Fin 2 → ZMod p) : ℝ :=
  (FiniteLaw.uniform (ZMod p)).expect
    (fun z => StarMatrix.psi A.val z c * StarMatrix.psi B.val z b)

theorem mixedMean_synthesis (hp3 : p % 4 = 3) (c : Fin 4 → ZMod p)
    (u : CoreSupport × PrivateSupport → ℝ) (B : PrivateSupport) (b : Fin 2 → ZMod p) :
    wOp (fun _ : Fin 2 => FiniteLaw.uniform (ZMod p)) B.val
      (fun z => ∑ A : CoreSupport, u (A, B) * StarMatrix.psi A.val z c) b =
        ∑ A : CoreSupport, u (A, B) * mixedMean A B c b := by
  unfold wOp mixedMean
  simp_rw [uniform_phi hp3, sum_mul, expect_finset_sum, mul_assoc,
    FiniteLaw.expect_const_mul]
  rfl

/-- On each injective core, all 45 mixed means have this synthesis bound. -/
theorem mixedMean_fixed_frame (hW : Labellings.WeilBound (ZMod p)) (hp3 : p % 4 = 3)
    (c : Fin 4 → ZMod p) (hc : Function.Injective c)
    (u : CoreSupport × PrivateSupport → ℝ) :
    (privateCube p).expect (fun b =>
      (∑ B : PrivateSupport, ∑ A : CoreSupport, u (A, B) * mixedMean A B c b) ^ 2) ≤
        ((p : ℝ)⁻¹ * (1 + 42 * rp p + 56 * (p : ℝ)⁻¹)) *
          ∑ B : PrivateSupport, ∑ A : CoreSupport, u (A, B) ^ 2 := by
  have hdens (i : Fin 2) (a : ZMod p) :
      (FiniteLaw.uniform (ZMod p)).weight a ≤ (1 : ℝ) / p := by
    simp only [FiniteLaw.uniform, ZMod.card, one_div, le_refl]
  have h := rawStar_synthesis_subtype (by omega : p ≠ 2)
    (fun _ : Fin 2 => FiniteLaw.uniform (ZMod p)) hdens (nonemptySets (Fin 2))
    (fun _ hS => (mem_filter.mp hS).2)
    (fun B z => ∑ A : CoreSupport, u (A, B) * StarMatrix.psi A.val z c)
  simp only [mixedMean_synthesis hp3, FiveType.ip, ← pow_two, one_mul] at h
  calc
    _ ≤ (p : ℝ)⁻¹ * ∑ B : PrivateSupport,
        (FiniteLaw.uniform (ZMod p)).expect
          (fun z => (∑ A : CoreSupport, u (A, B) * StarMatrix.psi A.val z c) ^ 2) := h
    _ ≤ (p : ℝ)⁻¹ * ∑ B : PrivateSupport,
        (1 + 42 * rp p + 56 * (p : ℝ)⁻¹) * ∑ A : CoreSupport, u (A, B) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum fun B _ => core_character_frame hW c hc (fun A => u (A, B)))
        (by positivity)
    _ = _ := by rw [← mul_sum, mul_assoc]

end Sarkozy.PositiveRoots.CoherentFrame
