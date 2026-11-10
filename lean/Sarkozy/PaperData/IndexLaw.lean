module

public import Sarkozy.PaperData.SquareIncrement
public import Sarkozy.CancellationSteps.Paper
public import Sarkozy.PartVLaws.PadicPrice
public import Sarkozy.Param.Params

@[expose] public section

/-!
# The paper's index law (`def:cp0`(d), `def:construction`(a), `def:hyb:coupled`)

`paper/sections/18_design.tex`, `def:construction`(a); `paper/sections/27_tail_index.tex`,
`lem:imp:padic-envelope`, `prop:imp:padic-price`.

`TheoremC.IndexLaw paperPr paperH Chamber` for the paper's six queries and the prime powers of
`M₀` (D1's `CancellationSteps.paperPr`, `paperH`). The fields are filled as follows.
* **Increments, proved.** `μ e q` is V1's `squareIncrementLaw` at `p^h` with valuation bound
  `m_ext = 64`, the same for every query (`paperIncrement`). It is a probability law, and its
  support consists of nonvanishing square coordinates (`squareIncrementLaw_nonvanishing`).
* **Depth envelope, open** (`PaperIndexEnvelope`).
  - The tails `t` and the transition-norm bound `hnorm` are `lem:imp:padic-envelope`: the depth
    tails bound the Gauss multipliers of the conditioned square increments. V2-A's
    `PartVLaws.PadicPrice` defines the tails (`oddTail`, `twoTail`) but not this bound.
  - The moment `R_I` is `lem:hyb:moment` with `cert:index-moment` for its value.
-/

namespace Sarkozy.PaperData

open Finset Sarkozy.CancellationSteps Sarkozy.TheoremC Sarkozy.IndexSupport
open scoped Matrix

theorem paperH_ge (q : PaperP) : 128 ≤ paperH q := by
  unfold paperH PartV.mExt
  split_ifs <;> norm_num

theorem paperH_two (q : PaperP) (h : paperPr q = 2) : 129 ≤ paperH q := by
  unfold paperH PartV.mExt
  simp only [paperPr] at h
  simp [h]

theorem paper_lowValuation_nonempty (q : PaperP) :
    (PartV.lowValuation (paperPr q) (paperH q) 64).Nonempty :=
  ⟨1, PartV.one_mem_lowValuation (paperPr_prime q).two_le (by have := paperH_ge q; omega)
    (by norm_num)⟩

/-- **The increment law at the index prime `q`** (`def:construction`(a)): the law of `x²`, `x`
uniform among the residues of `ℤ/p^hℤ` of valuation `< 64`. -/
noncomputable def paperIncrement (q : PaperP) : FiniteLaw (ZMod (paperPr q ^ paperH q)) :=
  PartV.squareIncrementLaw (paperPr q) (paperH q) 64 (paper_lowValuation_nonempty q)

/-- **The open part of the index law: its depth envelope.**
* `t`, `hnorm`: the depth tails and the bound of the transition on each exact-conductor space
  by the tails (`lem:imp:padic-envelope`). *Open* (analytic, Part V).
* `R_I`, `hR_I`: the conductor moment (`lem:hyb:moment`; its value is `cert:index-moment`,
  bounded by the ledger in `PaperObligations.hR`). -/
structure PaperIndexEnvelope where
  t : Chamber → ∀ q : PaperP, Tails (Chain.residues (paperPr q) (paperH q)).depth
  hnorm : ∀ e q (l : Fin ((Chain.residues (paperPr q) (paperH q)).depth + 1)) f,
    (Chain.residues (paperPr q) (paperH q)).diff l *ᵥ f = f →
    (convMatrix (paperIncrement q).weight *ᵥ f) ⬝ᵥ (convMatrix (paperIncrement q).weight *ᵥ f) ≤
      (t e q).tail l ^ 2 * (f ⬝ᵥ f)
  R_I : ℝ
  hR_I : 0 ≤ R_I

/-- **The paper's index law** from its depth envelope: the increments are `paperIncrement`, with
the nonvanishing square property proved. -/
noncomputable def paperIndexLaw (env : PaperIndexEnvelope) : IndexLaw paperPr paperH Chamber where
  μ _ q := (paperIncrement q).weight
  hμ _ q r := (paperIncrement q).nonneg r
  hμ1 _ q := (paperIncrement q).total
  hsq _ q _ hr :=
    squareIncrementLaw_nonvanishing (paperPr_prime q) (paperH_ge q) (paperH_two q) _ hr
  t := env.t
  hnorm := env.hnorm
  R_I := env.R_I
  hR_I := env.hR_I

/-! ## The paper's depth tails and moment -/

/-- **The paper's depth tails at the index prime `q`** (`lem:imp:padic-envelope`, V2-A's
`PartVLaws.twoTail 64` at `2` and `PartVLaws.oddTail q 64` at the odd primes). -/
noncomputable def paperDepthTail (q : PaperP) : ℕ → ℝ :=
  if paperPr q = 2 then PartVLaws.twoTail 64 else PartVLaws.oddTail (paperPr q) 64

theorem paperDepthTail_isDepthTail (q : PaperP) :
    Functional.IsDepthTail (paperH q) (paperDepthTail q) := by
  unfold paperDepthTail
  by_cases h2 : paperPr q = 2
  · simp only [h2, ↓reduceIte]
    have hH : paperH q = 129 := by
      unfold paperH PartV.mExt
      simp only [paperPr] at h2
      simp [h2]
    rw [hH]
    have h := PartVLaws.isDepthTail_twoTail (m := 64) (by norm_num)
    exact ⟨h.zero, fun j hj => h.anti j (by omega), h.nonneg_le 129 (by norm_num)⟩
  · simp only [h2, ↓reduceIte]
    have hH : paperH q = 2 * 64 := by
      unfold paperH PartV.mExt
      simp only [paperPr] at h2
      simp [h2]
    rw [hH]
    have h3 : 3 ≤ paperPr q := by
      have := (paperPr_prime q).two_le
      omega
    exact PartVLaws.isDepthTail_oddTail h3 (by norm_num)

/-- The paper's depth tails as `IndexSupport.Tails`. -/
noncomputable def paperTails (q : PaperP) : Tails (Chain.residues (paperPr q) (paperH q)).depth :=
  ⟨paperDepthTail q, (paperDepthTail_isDepthTail q).zero, (paperDepthTail_isDepthTail q).anti,
    (paperDepthTail_isDepthTail q).nonneg⟩

/-- **The paper's conductor moment** `R_I = M_pad(K)` at `a₀` (`prop:imp:padic-price`, V2-A's
`PartVLaws.Mpad`, with `m = 64`, `Q = Q₃`, `K = blockScale`). By `Mpad_eq_oneQueryMoment` it is
the exact one-query moment `E (K sq(D_J))^{a₀/36}` of the depths with these tails. Its numeric
bound is `cert:index-moment` (`PaperObligations.hR`). -/
noncomputable def paperRI : ℝ := PartVLaws.Mpad Param.Params.anchorDecay 64 PartV.Q3 blockScale

theorem paperRI_nonneg : 0 ≤ paperRI := by
  unfold paperRI
  rw [PartVLaws.Mpad_eq_oneQueryMoment (by unfold Param.Params.anchorDecay; norm_num)
    (by norm_num) _ (by unfold blockScale; norm_num)]
  unfold Functional.oneQueryMoment
  exact FiniteLaw.expect_nonneg _ fun J => Real.rpow_nonneg (by unfold blockScale; positivity) _

/-- **The remaining input of the index law** (`lem:imp:padic-envelope`, analytic): on each
exact-conductor space the transition of the increment law is bounded by the paper's depth tail.
*Open* (Part V). -/
def PaperIndexBound : Prop :=
  ∀ (q : PaperP) (l : Fin ((Chain.residues (paperPr q) (paperH q)).depth + 1)) f,
    (Chain.residues (paperPr q) (paperH q)).diff l *ᵥ f = f →
    (convMatrix (paperIncrement q).weight *ᵥ f) ⬝ᵥ (convMatrix (paperIncrement q).weight *ᵥ f) ≤
      (paperTails q).tail l ^ 2 * (f ⬝ᵥ f)

/-- The depth envelope with the paper's tails and moment, from `PaperIndexBound`. -/
noncomputable def paperIndexEnvelope (hb : PaperIndexBound) : PaperIndexEnvelope where
  t _ q := paperTails q
  hnorm _ q l f h := hb q l f h
  R_I := paperRI
  hR_I := paperRI_nonneg

end Sarkozy.PaperData
