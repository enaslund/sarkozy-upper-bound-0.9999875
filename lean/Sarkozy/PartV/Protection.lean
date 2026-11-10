module

public import Sarkozy.PartV.LayerCut

@[expose] public section

/-!
# The protection of the folds at `ι` (`lem:front12:reference`(iv))

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(iv), `eq:protection`. If the fold
components satisfy the layer caps of the type D, `Π_{F_s} ⪰_ι -k_D r Diag_ι(Π⁽¹⁾_{F_s})`, and the
weights satisfy `v_D ≥ 2 k_D w_D`, then
`2 w_D r Π_{F_s} + v_D r² Diag_ι(Π⁽¹⁾_{F_s}) ⪰_ι 0` (`middle_protection`), because
`2 w_D r Π + v_D r² D = 2 w_D r (Π + k_D r D) + (v_D - 2 k_D w_D) r² D` and `D` is positive at `ι`.
The paper states it for `s ∈ {1, 2}`; the argument holds for every fold. Parts (i)–(iii) do not
use it; the bracket of `lem:record:gram` does.
-/

namespace Sarkozy.PartV

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **`lem:front12:reference`(iv).** -/
theorem middle_protection (F : MiddleFieldLaws X) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (hcap : MiddleLayerCaps F I.k r) (hP : W.Protects I) (s : Fin 3) :
    reservedCut.Positive
      ((2 * W.w .D * r) • signedIntegral (midComponent F (true, ⟨.D, s⟩)).weight +
        (W.v .D * r ^ 2) • signedIntegral (midComponent F (false, ⟨.D, s⟩)).weight) := by
  set A := signedIntegral (midComponent F (true, ⟨.D, s⟩)).weight
  set B := signedIntegral (midComponent F (false, ⟨.D, s⟩)).weight
  have key : (2 * W.w .D * r) • A + (W.v .D * r ^ 2) • B =
      (2 * W.w .D * r) • (A - (-(I.k .D * r)) • B) +
        ((W.v .D - 2 * I.k .D * W.w .D) * r ^ 2) • B := by
    apply LinearMap.ext
    intro f
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
    ring
  rw [key]
  have hw : 0 ≤ 2 * W.w .D * r := mul_nonneg (mul_nonneg (by norm_num) (W.w_nonneg _)) hr
  have hv : 0 ≤ (W.v .D - 2 * I.k .D * W.w .D) * r ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hP) (sq_nonneg r)
  exact ((hcap .D s).smul hw).add ((middleDiag_reserved_positive F .D s).smul hv)

end Sarkozy.PartV
