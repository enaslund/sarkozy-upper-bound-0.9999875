module

public import Sarkozy.Envelopes.MaskReduction
public import Sarkozy.Envelopes.F6E0
public import Sarkozy.Envelopes.F5E1
public import Sarkozy.Envelopes.F4E2
public import Sarkozy.Envelopes.F3E3
public import Sarkozy.Envelopes.F2E4

@[expose] public section

/-!
# The five diagonal witnesses are envelopes (`cert:envelopes`(b), `thm:envelopes`(v))

`paper/sections/23_envelopes.tex`, `cert:envelopes`(b) and `thm:envelopes`(v)(b), (c): the diagonal
mask envelopes F6E0, F5E1, F4E2, F3E3 and F2E4 of the data file are envelopes in the sense of
`lem:oct24:mask-schur`(c). For each of them, the kernel checks (`*_tablePos`, `*_maskCheck`) and the
reduction `checked_table_envelope` give `-D ⪯ T ⪯ D` for every block operator `T` on the features
with the sector structure of the tensor of the stars `eq:signed-star` (blocks vanish unless the
masks are complementary, block norms at most `α(v) α(w)` with the arm magnitudes `1, t, 1 - t`
and `1`), `D` the diagonal of the envelope's weights.

What is not checked: the caps (the weighted-frame bounds, with the averages of
`lem:reflection-averaging`) and the coupling masses of these envelopes, which enter the class
costs.
-/

namespace Sarkozy.Envelopes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **F6E0 is an envelope** (`cert:envelopes`(b)): `-D ⪯ T ⪯ D` for the weights of F6E0 and every
block operator with the sector structure of the tensor of the stars of the class `(6, 0)`. -/
theorem F6E0_envelope (Top : Feat 6 0 → Feat 6 0 → E →ₗ[ℝ] E)
    (hsec : ∀ v w, featMask w ≠ maskCompl (featMask v) → Top w v = 0)
    (hnorm : ∀ v w y, ‖Top w v y‖ ≤ (featAlpha v : ℝ) * (featAlpha w : ℝ) * ‖y‖)
    (x : Feat 6 0 → E) :
    |∑ v, ∑ w, inner ℝ (x w) (Top w v (x v))| ≤
      ∑ v, (featWeight tableF6E0 v : ℝ) * ‖x v‖ ^ 2 :=
  checked_table_envelope F6E0_tablePos F6E0_maskCheck Top hsec hnorm x

/-- **F5E1 is an envelope** (`cert:envelopes`(b)): `-D ⪯ T ⪯ D` for the weights of F5E1 and every
block operator with the sector structure of the tensor of the stars of the class `(5, 1)`. -/
theorem F5E1_envelope (Top : Feat 5 1 → Feat 5 1 → E →ₗ[ℝ] E)
    (hsec : ∀ v w, featMask w ≠ maskCompl (featMask v) → Top w v = 0)
    (hnorm : ∀ v w y, ‖Top w v y‖ ≤ (featAlpha v : ℝ) * (featAlpha w : ℝ) * ‖y‖)
    (x : Feat 5 1 → E) :
    |∑ v, ∑ w, inner ℝ (x w) (Top w v (x v))| ≤
      ∑ v, (featWeight tableF5E1 v : ℝ) * ‖x v‖ ^ 2 :=
  checked_table_envelope F5E1_tablePos F5E1_maskCheck Top hsec hnorm x

/-- **F4E2 is an envelope** (`cert:envelopes`(b)): `-D ⪯ T ⪯ D` for the weights of F4E2 and every
block operator with the sector structure of the tensor of the stars of the class `(4, 2)`. -/
theorem F4E2_envelope (Top : Feat 4 2 → Feat 4 2 → E →ₗ[ℝ] E)
    (hsec : ∀ v w, featMask w ≠ maskCompl (featMask v) → Top w v = 0)
    (hnorm : ∀ v w y, ‖Top w v y‖ ≤ (featAlpha v : ℝ) * (featAlpha w : ℝ) * ‖y‖)
    (x : Feat 4 2 → E) :
    |∑ v, ∑ w, inner ℝ (x w) (Top w v (x v))| ≤
      ∑ v, (featWeight tableF4E2 v : ℝ) * ‖x v‖ ^ 2 :=
  checked_table_envelope F4E2_tablePos F4E2_maskCheck Top hsec hnorm x

/-- **F3E3 is an envelope** (`cert:envelopes`(b)): `-D ⪯ T ⪯ D` for the weights of F3E3 and every
block operator with the sector structure of the tensor of the stars of the class `(3, 3)`. -/
theorem F3E3_envelope (Top : Feat 3 3 → Feat 3 3 → E →ₗ[ℝ] E)
    (hsec : ∀ v w, featMask w ≠ maskCompl (featMask v) → Top w v = 0)
    (hnorm : ∀ v w y, ‖Top w v y‖ ≤ (featAlpha v : ℝ) * (featAlpha w : ℝ) * ‖y‖)
    (x : Feat 3 3 → E) :
    |∑ v, ∑ w, inner ℝ (x w) (Top w v (x v))| ≤
      ∑ v, (featWeight tableF3E3 v : ℝ) * ‖x v‖ ^ 2 :=
  checked_table_envelope F3E3_tablePos F3E3_maskCheck Top hsec hnorm x

/-- **F2E4 is an envelope** (`cert:envelopes`(b)): `-D ⪯ T ⪯ D` for the weights of F2E4 and every
block operator with the sector structure of the tensor of the stars of the class `(2, 4)`. -/
theorem F2E4_envelope (Top : Feat 2 4 → Feat 2 4 → E →ₗ[ℝ] E)
    (hsec : ∀ v w, featMask w ≠ maskCompl (featMask v) → Top w v = 0)
    (hnorm : ∀ v w y, ‖Top w v y‖ ≤ (featAlpha v : ℝ) * (featAlpha w : ℝ) * ‖y‖)
    (x : Feat 2 4 → E) :
    |∑ v, ∑ w, inner ℝ (x w) (Top w v (x v))| ≤
      ∑ v, (featWeight tableF2E4 v : ℝ) * ‖x v‖ ^ 2 :=
  checked_table_envelope F2E4_tablePos F2E4_maskCheck Top hsec hnorm x

end Sarkozy.Envelopes
