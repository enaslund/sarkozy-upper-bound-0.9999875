module

public import Sarkozy.EnvelopesPaper.Matching

@[expose] public section

/-!
# (CP7) mean credit: from the envelopes to their cores

`paper/sections/09_comparison_theorem.tex`, `def:cp7`; `paper/sections/24_matching_mean.tex`,
`prop:record:mean-credit`, Step 1 (first half).

For the envelopes `M_s = core_s + extra` of `EnvelopeRefinement.toME`
(`core_s = Ñ + ∑_i k_{s,i} κK_i`, `extra` the norm envelopes of the non-replaced records), the
paper's Step 1 says `0 ⪯_ι core_s ⪯_ι M_s` at every atom (the bracket measure is positive,
`lem:record:gram`(ii); the added diagonals are positive and reserved diagonal; the difference is
positive), hence by the tensor monotonicity of `lem:record:block-gram`(d)
`⊗_𝔟 M_{s,𝔟} ⪰_ι ⊗_𝔟 core_{s,𝔟}` and, evaluated at `X̄`, `e_s ≥ Y_{⊗ core_s}`. This file proves
that step for any `GB`, `CL` and refinement:

* `energyMean_le_of_below`: `0 ⪯ C_𝔟 ⪯ M_𝔟` at every atom gives `Q_{⊗C}(X̄, X̄) ≤ Q_{⊗M}(X̄, X̄)`;
* `robustLower_mono`: a robust lower bound passes to a pointwise larger quantity;
* `MeanInputs F`: **the input** — a number `m` and the robust lower bound
  `½(Y_{⊗ coreL} + Y_{⊗ coreR}) ≥ (m - o(1)) Y`. It is the rest of `prop:record:mean-credit`:
  Step 1, second half (the comparison of `Ñ` with `Ñ₀` by (E1), the loss `R_err e^{T_K + T_QE}`),
  and Steps 2–3 (the positive expansion and the retained credits `m_F`, `m_Q`, the pool coupons);
* **`meanCreditOf`**: (CP7) for `F.toME a T hL hR`, with the mean credit `m` of the input.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopesPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.Comparison

/-! ## Monotonicity of the mean energy -/

section Mono

variable {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
  {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]

/-- **Tensor monotonicity of the mean energy** (`lem:record:block-gram`(d), evaluated at `X̄`;
Step 1 of `prop:record:mean-credit`): if `0 ⪯_ι C_𝔟 ⪯_ι M_𝔟` at every atom, then
`Q_{⊗C}(X̄, X̄) ≤ Q_{⊗M}(X̄, X̄)`. -/
theorem energyMean_le_of_below (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)
    (C M : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ) (hC : ∀ L b, reservedCut.Positive (C L b))
    (hM : ∀ L b, reservedCut.Below (C L b) (M L b)) (L : ℕ) (A : Finset ℤ) :
    energyMean F C L A ≤ energyMean F M L A := by
  have h := (RecordExpansion.below_tensorLaw reservedCut (C L) (M L) (hC L) (hM L)).nonneg
    (barHalf (F L A))
  have e : reservedCut.form (tensorLaw (M L) - tensorLaw (C L)) (barHalf (F L A))
      (barHalf (F L A)) = reservedCut.form (tensorLaw (M L)) (barHalf (F L A)) (barHalf (F L A)) -
        reservedCut.form (tensorLaw (C L)) (barHalf (F L A)) (barHalf (F L A)) := rfl
  rw [e] at h
  unfold energyMean
  linarith

end Mono

/-- **A robust lower bound passes to a larger quantity**: if `Ξ ≥ (c - o(1)) Y` robustly and
`Ξ ≤ Ξ'` everywhere, then `Ξ' ≥ (c - o(1)) Y` robustly (same argument, same remainders). -/
theorem robustLower_mono {a : ℝ} {Y Ξ Ξ' : ℕ → Finset ℤ → ℝ} {c : ℝ}
    (h : TheoremCParam.RobustLower a Y Ξ c) (hle : ∀ L A, Ξ L A ≤ Ξ' L A) :
    TheoremCParam.RobustLower a Y Ξ' c := by
  obtain ⟨ε, hε, c', hc', hA⟩ := h
  refine ⟨ε, hε, c', hc', ?_⟩
  unfold Param.AtCounterexamples at hA ⊢
  filter_upwards [hA] with L hL
  intro C hC hk A hAd hY
  exact (hL C hC hk A hAd hY).trans (hle L A)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R} {GB : GramBracket a m₀ blk p S₀ FS}
  {CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS}

namespace EnvelopeRefinement

variable (F : EnvelopeRefinement GB CL)

omit [∀ L, DecidableEq (J L)] in
/-- The left envelope of `toME` dominates its core: `coreL ⪯_ι M_L`. -/
theorem coreL_below_ML (T : ℝ) (hL : ∀ L, ∑ b, F.priceL L b ≤ T)
    (hR : ∀ L, ∑ b, F.priceR L b ≤ T) (L : ℕ) (b : BlockAtom Bk J L) :
    reservedCut.Below (F.coreL L b) ((F.toME a T hL hR).ML L b) := by
  rw [F.toME_ML]
  unfold ReflectionCut.Below
  rw [add_sub_cancel_left]
  exact F.extra_positive L b

omit [∀ L, DecidableEq (J L)] in
/-- The right envelope of `toME` dominates its core: `coreR ⪯_ι M_R`. -/
theorem coreR_below_MR (T : ℝ) (hL : ∀ L, ∑ b, F.priceL L b ≤ T)
    (hR : ∀ L, ∑ b, F.priceR L b ≤ T) (L : ℕ) (b : BlockAtom Bk J L) :
    reservedCut.Below (F.coreR L b) ((F.toME a T hL hR).MR L b) := by
  rw [F.toME_MR]
  unfold ReflectionCut.Below
  rw [add_sub_cancel_left]
  exact F.extra_positive L b

end EnvelopeRefinement

variable (a) in
/-- **The input of (CP7) for a refinement** (`prop:record:mean-credit`, all but the first half of
Step 1): a number `m` and the robust lower bound
`½(Q_{⊗ coreL}(X̄, X̄) + Q_{⊗ coreR}(X̄, X̄)) ≥ (m - o(1)) Y`, with `core_s = Ñ + ∑_i k_{s,i} κK_i`.
**Used as a hypothesis.** In the paper `m = 1 + m_F + m_Q - R_err e^{T_K + T_QE}`
(`eq:mean-credit`); the ledger's `m₁ = 1 + native_survivor - mean_error` is its evaluation
(`tab:four-routes-ledger`). -/
structure MeanInputs (F : EnvelopeRefinement GB CL) where
  m : ℝ
  bound : TheoremCParam.RobustLower a (energyFirst (R.law p) (blockLift m₀ blk p))
    (fun L A => (energyMean (blockLift m₀ blk p) F.coreL L A +
      energyMean (blockLift m₀ blk p) F.coreR L A) / 2) m

/-- **(CP7) for the envelopes of a refinement** (`def:cp7`, `prop:record:mean-credit`): Step 1
(`e_s ≥ Y_{⊗ core_s}`, `energyMean_le_of_below`) applied to the input `MeanInputs`. -/
noncomputable def meanCreditOf (F : EnvelopeRefinement GB CL) (T : ℝ)
    (hL : ∀ L, ∑ b, F.priceL L b ≤ T) (hR : ∀ L, ∑ b, F.priceR L b ≤ T)
    (MI : MeanInputs a F) : MeanCredit a m₀ blk p (F.toME a T hL hR) where
  m := MI.m
  bound := robustLower_mono MI.bound fun L A => by
    have h1 := energyMean_le_of_below (blockLift m₀ blk p) F.coreL (F.toME a T hL hR).ML
      F.coreL_positive (F.coreL_below_ML T hL hR) L A
    have h2 := energyMean_le_of_below (blockLift m₀ blk p) F.coreR (F.toME a T hL hR).MR
      F.coreR_positive (F.coreR_below_MR T hL hR) L A
    linarith

theorem meanCreditOf_m (F : EnvelopeRefinement GB CL) (T : ℝ)
    (hL : ∀ L, ∑ b, F.priceL L b ≤ T) (hR : ∀ L, ∑ b, F.priceR L b ≤ T)
    (MI : MeanInputs a F) : (meanCreditOf F T hL hR MI).m = MI.m := rfl

end Sarkozy.EnvelopesPaper
