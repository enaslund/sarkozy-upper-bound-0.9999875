module

public import Sarkozy.IndexCert.EnvelopeTwo

@[expose] public section

/-!
# `lem:imp:padic-envelope` for the paper's index law (`PaperData.PaperIndexBound`)

`paper/sections/27_tail_index.tex`, `lem:imp:padic-envelope`, at the paper's data: the prime
powers `p^{128}` (`p ≡ 3 (mod 4)`, `p < Q₃`) and `2^{129}` of `M₀` (D1's `paperPr`, `paperH`),
the increments of V1's `squareIncrementLaw` with `m_ext = 64` (D1's `paperIncrement`), and the
tails `PartVLaws.oddTail p 64`, `PartVLaws.twoTail 64` (D1's `paperDepthTail`).

`paperIndexBound` proves D1's `PaperIndexBound`, the field `hIdx` of `MainAnchor.PaperData`
(the only open part of the index law). It is `odd_envelope` (`EnvelopeOdd.lean`) at the odd
primes and `two_envelope` (`EnvelopeTwo.lean`) at `2`. No hypothesis is used.
`paperIndexEnvelope_proved` is D1's depth envelope with this bound.
-/

namespace Sarkozy.IndexCert

open Finset Sarkozy.IndexSupport Sarkozy.CancellationSteps
open scoped Matrix BigOperators

/-- **`lem:imp:padic-envelope`, the transition bound, proved** (D1's
`Sarkozy.PaperData.PaperIndexBound`; the field `hIdx` of `MainAnchor.PaperData`): at every prime
of the paper's index law and every depth `l`, the transition of the square-increment law maps the
exact-depth space `ran Π_l` with norm at most the paper's tail `δ_l` (`PartVLaws.oddTail p 64`
at odd `p`, modulus `p^{128}`; `PartVLaws.twoTail 64` at `2`, modulus `2^{129}`). -/
theorem paperIndexBound : Sarkozy.PaperData.PaperIndexBound := by
  intro q l f hf
  have hl : (l : ℕ) ≤ paperH q := Nat.lt_succ_iff.mp l.isLt
  show _ ≤ Sarkozy.PaperData.paperDepthTail q l ^ 2 * _
  unfold Sarkozy.PaperData.paperDepthTail
  by_cases h2 : paperPr q = 2
  · rw [ite_eq_left h2]
    have hH : paperH q = 2 * 64 + 1 := by
      unfold paperH PartV.mExt
      simp only [paperPr] at h2
      simp [h2]
    exact two_envelope h2 (by norm_num) hH (Sarkozy.PaperData.paper_lowValuation_nonempty q) hl hf
  · rw [ite_eq_right h2]
    have hH : paperH q = 2 * 64 := by
      unfold paperH PartV.mExt
      simp only [paperPr] at h2
      simp [h2]
    exact odd_envelope (paperPr_prime q) h2 (by norm_num) hH
      (Sarkozy.PaperData.paper_lowValuation_nonempty q) hl hf

/-- D1's depth envelope of the paper's index law with the transition bound proved
(`lem:imp:padic-envelope`); its moment is `R_I = paperRI` (`cert:index-moment` bounds it). -/
noncomputable def paperIndexEnvelope_proved : Sarkozy.PaperData.PaperIndexEnvelope :=
  Sarkozy.PaperData.paperIndexEnvelope paperIndexBound

end Sarkozy.IndexCert
