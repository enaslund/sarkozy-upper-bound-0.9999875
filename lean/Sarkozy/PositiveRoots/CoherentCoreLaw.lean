module

public import Sarkozy.PositiveRoots.CoherentDiagonalMaps

/-! The actual core law as an affine-invariant law on the full coordinate space. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))]

noncomputable def coreAmbientLaw : FiniteLaw (Fin 4 → ZMod p) :=
  (coreLaw (F := ZMod p)).map Subtype.val

theorem coreAmbient_expect (f : (Fin 4 → ZMod p) → ℝ) :
    (coreAmbientLaw (p := p)).expect f = coreLaw.expect (fun c : CoreT (ZMod p) => f c.val) :=
  FiniteLaw.expect_map coreLaw Subtype.val f

theorem coreAmbient_injective (x : Fin 4 → ZMod p) (k l : Fin 4)
    (hx : (coreAmbientLaw (p := p)).weight x ≠ 0) (hkl : k ≠ l) : x k ≠ x l := by
  intro he
  apply hx
  change (∑ c : CoreT (ZMod p), if c.val = x then coreLaw.weight c else 0) = 0
  apply sum_eq_zero
  intro c _
  have hn : c.val ≠ x := by
    intro hcx
    exact c.property.1.ne hkl (by simpa only [hcx] using he)
  rw [ite_eq_right hn]

theorem coreAmbient_affine (s c : ZMod p) (x : Fin 4 → ZMod p)
    (hs : s ≠ 0) (hsq : IsSquare s) :
    (coreAmbientLaw (p := p)).weight (affLab s c x) = (coreAmbientLaw (p := p)).weight x := by
  have hχ : quadraticChar (ZMod p) s = 1 := (quadraticChar_one_iff_isSquare hs).mpr hsq
  change (∑ C : CoreT (ZMod p), if C.val = affLab s c x then coreLaw.weight C else 0) =
    ∑ C : CoreT (ZMod p), if C.val = x then coreLaw.weight C else 0
  rw [← Equiv.sum_comp (affCoreEquiv hχ c)]
  apply sum_congr rfl
  intro C _
  have he : (affCoreEquiv hχ c C).val = affLab s c x ↔ C.val = x := by
    constructor
    · intro heq
      funext i
      exact mul_left_cancel₀ hs (add_right_cancel (congrFun heq i))
    · intro heq
      change affCore s c C.val = affLab s c x
      rw [heq]
      rfl
  rw [if_congr he rfl rfl]
  rfl

end Sarkozy.PositiveRoots.CoherentFrame
