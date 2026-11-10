module

public import Sarkozy.EnvelopeSteps.MaskLift
public import Sarkozy.Envelopes.MaskReduction

@[expose] public section

/-!
# The domination of Step 2 for the checked diagonal envelopes

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(c), `cert:envelopes`(b), and Step 2 of the
proof of `thm:envelopes`.

W2's `checked_table_envelope` turns the kernel checks of a diagonal envelope table (`tablePos`,
`maskCheck`; for the five witnesses F6E0, F5E1, F4E2, F3E3, F2E4 these are W2's `*_tablePos`,
`*_maskCheck`) into the feature-form bound `|∑⟪x_w, T_{wv} x_v⟫| ≤ ∑ d_v ‖x_v‖²` for every block
operator with the sector structure of the tensor of the stars. **`opLE_of_checked_table`** turns
that into the input `hdom` of `DegreeOps` (`±L_ω ⪯ D_ω` in `L²(m_ω)`), given the feature
representations of the forms of `L_ω` and `D_ω`. For these envelopes the joint spectral step
(move 1 of `lem:oct24:mask-schur`(a)) is not needed.
-/

open Finset

namespace Sarkozy.EnvelopeSteps

open Sarkozy.Envelopes

/-- **`±L_ω ⪯ D_ω` from a checked diagonal envelope table** (`cert:envelopes`(b) with
`lem:oct24:mask-schur`(c)). -/
theorem opLE_of_checked_table {O : Type*} [Fintype O] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {Tb : EnvTable} {n k : ℕ} (hT : tablePos Tb n k = true)
    (hC : maskCheck Tb n k = true) (Top : Feat n k → Feat n k → E →ₗ[ℝ] E)
    (hsec : ∀ v w, featMask w ≠ maskCompl (featMask v) → Top w v = 0)
    (hnorm : ∀ v w y, ‖Top w v y‖ ≤ (featAlpha v : ℝ) * (featAlpha w : ℝ) * ‖y‖)
    {m : O → ℝ} {Lop Dop : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (ι : Feat n k → (O → ℝ) →ₗ[ℝ] E)
    (hL : ∀ f, ip m f (Lop f) = ∑ v, ∑ w, inner ℝ (ι w f) (Top w v (ι v f)))
    (hD : ∀ f, ip m f (Dop f) = ∑ v, (featWeight Tb v : ℝ) * ‖ι v f‖ ^ 2)
    (hLs : ∀ f g, ip m f (Lop g) = ip m g (Lop f)) (hDs : ∀ f g, ip m f (Dop g) = ip m g (Dop f)) :
    OpLE m Lop Dop ∧ OpLE m (-Lop) Dop :=
  opLE_of_feature_form Top (fun v => (featWeight Tb v : ℝ)) ι
    (fun x => checked_table_envelope hT hC Top hsec hnorm x) hL hD hLs hDs

end Sarkozy.EnvelopeSteps
