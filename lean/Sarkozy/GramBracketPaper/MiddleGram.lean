module

public import Sarkozy.GramBracketPaper.Assembly
public import Sarkozy.FirstStagePaper.MiddleStage
public import Sarkozy.PartVRecords.Gram
public import Sarkozy.Misc.MatchingBlock

@[expose] public section

/-!
# The Gram bracket of a middle block (`lem:record:gram`, `def:cp3`)

`paper/sections/20c_middle_frame.tex`, `subsec:middle-gram`, `lem:record:gram`, and
`lem:record:middle-prices` (the price `U₀` of `Ñ₀ - μ`).

On a middle block, over A1's first-stage data `middleStage` (V3's frame `middleFrame` with the
least prime `bmin`), the (CP3) data are V3's: `Ñ₀ = μ + E_add + G + H` (divided by `P(r)`), written
as the six positive reserved-diagonal records `bracketRec` (`Nbr0_sub_mu_eq_sum`), and the bracket
`(Ñ λ; λ Ñ) ⪰_ι 0` of `lem:record:gram`(ii) (`gram_bracket`). The inputs of `gram_bracket` are
discharged as follows.

* **The disjoint-triple bound** `MatchingReservedBound` (`sec:frontier:empty-triple-negative`(c) on
  the block) is M2's `Misc.matchingReservedBound_block` at the natural number `⌈bmin⌉`,
  transported to the real `bmin` by monotonicity in the constant `3/(b - 3)`
  (`middleFrame_matchingReserved`):
  `Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0`, and `3/(bmin - 3) ≥ 3/(⌈bmin⌉ - 3)`.
* **The symmetry of `λ` at `ι`** is derived from `μ ⪰_ι 0` (`lam_symmetric_of_mu`): a measure that
  is positive at a cut is invariant under its reflection, so `μ̃ = P(r) μ` is symmetric at `ι`, and
  all records are reserved diagonal. This replaces the layer-swap hypothesis `hF` of V3's
  `gram_cp3`/`lam_symmetric` (proved by V1 only for the uniform and the individual-square roots); it
  covers the coherent root as well. `μ ⪰_ι 0` is (R2) of the reference at the family cut `ι`.
* The layer caps `hcap` (`lem:front12:reference`(ii)) and the third line `v_𝔱 ≥ k_𝔱 w_𝔱` (`hdom`,
  the last of the thirteen inequalities `MiddleWeights.Completes`) are fields of V2's block
  specification; `3 < bmin` holds for every block (`bmin ≥ 2²⁴`).
* **Two gates remain as hypotheses**: the protection inequality `v_D ≥ 2 k_D w_D`
  (`eq:protection`, `lem:front12:reference`(iv)), and `f₁ + h₁ ≥ 0` (the polarization coefficient
  of `G = (f₁ + h₁) r (G_e + G_o)`, `def:record:frame`(b)). Both are checks on the recorded weights
  and inputs of the piece.

`middleGram` is the `AtomGram` of the block; `middleGram_uprice` its price `u_𝔅` as an identity, and
`middleGram_uprice_le` the bound of `lem:record:middle-prices` (V3's `uprice_le`) when
`r² bmin = 1`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.GramBracketPaper

open Sarkozy.TheoremC Sarkozy.PartVRecords Sarkozy.PartV Sarkozy.Labellings Sarkozy.FiveType
  Sarkozy.RecordExpansion Sarkozy.FirstStagePaper

/-! ## `λ` is symmetric at `ι` when `μ` is positive at `ι` -/

/-- **`λ_𝔅` is symmetric at `ι`** (`lem:record:gram`(ii), "`λ` is symmetric at `ι`"), from
`μ_𝔅 ⪰_ι 0` ((R2) at the family cut `ι`): `μ̃ = P(r) μ` is invariant under the reflection of `ι`
(`Positive.reflection_invariant`), and the records `F_fold`, `E_fold`, `E_new`, `G` are reserved
diagonal (V3's `records_symmetric`). No layer-swap hypothesis on the root is needed. -/
theorem lam_symmetric_of_mu {X : Type} [Fintype X] [DecidableEq X] (D : FrameData X)
    (hμ : reservedCut.Positive D.mu) : IsSymmetricAt reservedCut D.lam := by
  have hmu : IsSymmetricAt reservedCut D.mu := AtomGram.isSymmetricAt_of_positive hμ
  have hmuT : D.muT = D.P • D.mu := by
    unfold FrameData.mu
    rw [smul_smul, mul_inv_cancel₀ D.P_pos.ne', one_smul]
  have sT : IsSymmetricAt reservedCut D.muT := by
    rw [hmuT]
    exact hmu.smul _
  obtain ⟨sF, sE, -, sG, -, sN⟩ := D.records_symmetric
  exact ((isSymmetricAt_sub (isSymmetricAt_sub sT sF) sE).add sN |>.add sG).smul _

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-! ## The disjoint-triple bound with a real `b` -/

/-- **`MatchingReservedBound` for the frame of a middle block with a real lower bound `bmin` of its
primes** (`sec:frontier:empty-triple-negative`(c) on the block, the hypothesis of
`lem:record:gram`(ii)): M2's `Misc.matchingReservedBound_block` at `⌈bmin⌉ ≤ min p`, and
`3/(bmin - 3) ≥ 3/(⌈bmin⌉ - 3)` with `Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0`. -/
theorem middleFrame_matchingReserved (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) {bmin : ℝ} (h : ClassThreeBlock pr) (hb7 : 7 ≤ bmin)
    (hbp : ∀ i, bmin ≤ (pr i : ℝ)) :
    (middleFrame pr hne root W I hr bmin h).MatchingReservedBound := by
  set n : ℕ := ⌈bmin⌉₊ with hn
  have hbn : bmin ≤ (n : ℝ) := Nat.le_ceil bmin
  have hn7 : 7 ≤ n := by
    have h7 : ((7 : ℕ) : ℝ) ≤ n := by
      push_cast
      linarith
    exact_mod_cast h7
  have hnp : ∀ i, n ≤ pr i := fun i => Nat.ceil_le.mpr (hbp i)
  have hM := Misc.matchingReservedBound_block pr (middleFrame pr hne root W I hr (n : ℝ) h) n hn7
    hnp hne.E2 hne.E1 rfl rfl rfl
  intro s
  have hs := hM s
  set D := middleFrame pr hne root W I hr bmin h with hD
  have hT : (middleFrame pr hne root W I hr (n : ℝ) h).two .S s = D.two .S s := rfl
  have hG : (middleFrame pr hne root W I hr (n : ℝ) h).diag .S s = D.diag .S s := rfl
  have hb' : (middleFrame pr hne root W I hr (n : ℝ) h).b = n := rfl
  rw [hT, hG, hb'] at hs
  have hDb : D.b = bmin := rfl
  have hc : 0 ≤ 3 / (D.b - 3) - 3 / ((n : ℝ) - 3) := by
    rw [hDb, sub_nonneg]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have e : D.two .S s + (3 / (D.b - 3)) • D.diag .S s =
      (D.two .S s + (3 / ((n : ℝ) - 3)) • D.diag .S s) +
        (3 / (D.b - 3) - 3 / ((n : ℝ) - 3)) • D.diag .S s := by
    apply LinearMap.ext
    intro f
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact hs.add ((D.diag_positive .S s).smul hc)

/-! ## The sign of the polarization coefficient, from the rows -/

omit [Fintype ι] [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
/-- **A bound `‖T - J‖ ≤ e` forces `e ≥ 0`** (`NormBound`, tested on `Φ = Ψ = 1`). -/
theorem normBound_nonneg {𝔛 : Type} [Fintype 𝔛] [DecidableEq 𝔛] {μ : FiniteLaw 𝔛}
    {T : 𝔛 → 𝔛 → ℝ} {e : ℝ} (hT : NormBound μ T e) : 0 ≤ e := by
  have h1 := hT (fun _ => 1) (fun _ => 1)
  have hn : nrm μ (fun _ => (1 : ℝ)) = 1 := by
    unfold nrm ip
    simp
  rw [hn, mul_one, mul_one] at h1
  exact le_trans (abs_nonneg _) h1

omit [Fintype ι] [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
/-- **The row constants are nonnegative multiples of `r`** (`lem:front12:reference`(i)): the rows
`‖T_F^b - J‖ ≤ f r`, `‖T_E^b - J‖ ≤ h r` at a middle value `b` with `ν(b) > 0` (one exists,
`ν` being a probability law) give `f r ≥ 0` and `h r ≥ 0`. -/
theorem rowBounds_nonneg {X : Type} [Fintype X] [DecidableEq X] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {D : Datum (Λ → X)} {f g r : ℝ} (hR : RowBounds D f g r) :
    0 ≤ f * r ∧ 0 ≤ g * r := by
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ) (f := D.nu.weight)
    (by rw [D.nu.total]; exact one_ne_zero)
  exact ⟨normBound_nonneg (hR b hb).1, normBound_nonneg (hR b hb).2⟩

/-- The inputs with `h₁` replaced by `-f₁`, so that `f₁ + h₁ = 0`; used only when `r = 0`, where the
merge records `G` carry the coefficient `(f₁ + h₁) r = 0` whatever `h₁` is. -/
def polarInputs (I : MiddleInputs) : MiddleInputs := { I with h₁ := -I.f₁ }

theorem polarInputs_sum (I : MiddleInputs) : 0 ≤ (polarInputs I).f₁ + (polarInputs I).h₁ := by
  simp only [polarInputs, add_neg_cancel, le_refl]

/-! ## The (CP3) data of a middle block -/

variable (hne : MiddleNonempty pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
  (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (bmin : ℝ) (h : ClassThreeBlock pr)

/-- **The polarization coefficient `(f₁ + h₁) r` is nonnegative**, from the one-layer rows
(`lem:front12:reference`(i), `j = 1`) of the block. -/
theorem polarCoef_nonneg
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r) :
    0 ≤ (I.f₁ + I.h₁) * r := by
  obtain ⟨hf, hh⟩ := rowBounds_nonneg hrows₁
  rw [add_mul]
  exact add_nonneg hf hh

/-- At `r = 0` the merge records vanish: `G = (f₁ + h₁) r (G_e + G_o) = 0`. -/
theorem middleFrame_Gpol_zero (hr0 : r = 0) : (middleFrame pr hne root W I hr bmin h).Gpol = 0 := by
  change ((I.f₁ + I.h₁) * r) • _ = (0 : SlotMeasure (BlockLabel pr))
  have hc : (I.f₁ + I.h₁) * r = 0 := by rw [hr0, mul_zero]
  rw [hc, zero_smul]

/-- At `r = 0`, `λ` does not depend on the row constants. -/
theorem middleFrame_lam_congr (hr0 : r = 0) (I' : MiddleInputs) :
    (middleFrame pr hne root W I hr bmin h).lam = (middleFrame pr hne root W I' hr bmin h).lam := by
  unfold FrameData.lam
  rw [middleFrame_Gpol_zero pr hne root W I hr bmin h hr0,
    middleFrame_Gpol_zero pr hne root W I' hr bmin h hr0]
  rfl

/-- At `r = 0`, `Ñ` does not depend on the row constants. -/
theorem middleFrame_Nbr_congr (hr0 : r = 0) (I' : MiddleInputs) :
    (middleFrame pr hne root W I hr bmin h).Nbr = (middleFrame pr hne root W I' hr bmin h).Nbr := by
  unfold FrameData.Nbr
  rw [middleFrame_lam_congr pr hne root W I hr bmin h hr0 I']
  rfl

/-- **`Ñ` is nonnegative** (`lem:record:gram`(ii), V3's `Nbr_nonneg`), with the sign of the
polarization coefficient `(f₁ + h₁) r ≥ 0` (for `r > 0` this is `f₁ + h₁ ≥ 0`; at `r = 0` the merge
records vanish). -/
theorem middle_Nbr_nonneg (hG0 : 0 ≤ (I.f₁ + I.h₁) * r) (hb : 3 < bmin) :
    IsNonneg (middleFrame pr hne root W I hr bmin h).Nbr := by
  rcases hr.eq_or_lt with hr0 | hrpos
  · rw [middleFrame_Nbr_congr pr hne root W I hr bmin h hr0.symm (polarInputs I)]
    exact (middleFrame pr hne root W (polarInputs I) hr bmin h).Nbr_nonneg (polarInputs_sum I) hb
  · exact (middleFrame pr hne root W I hr bmin h).Nbr_nonneg
      (show (0 : ℝ) ≤ I.f₁ + I.h₁ by nlinarith) hb

/-- **`(Ñ λ; λ Ñ) ⪰_ι 0`** (`lem:record:gram`(ii), V3's `gram_bracket`), with the sign of the
polarization coefficient `(f₁ + h₁) r ≥ 0` and the disjoint-triple bound of
`middleFrame_matchingReserved`. -/
theorem middle_gram_bracket (hG0 : 0 ≤ (I.f₁ + I.h₁) * r) (hb7 : 7 ≤ bmin)
    (hbp : ∀ i, bmin ≤ (pr i : ℝ))
    (hcap : MiddleLayerCaps (middleBlockFieldLaws pr hne root) I.k r)
    (hdom : ∀ t, I.k t * W.w t ≤ W.v t) (hP : W.Protects I) :
    reservedCut.Bracket (middleFrame pr hne root W I hr bmin h).Nbr
      (middleFrame pr hne root W I hr bmin h).lam (middleFrame pr hne root W I hr bmin h).Nbr := by
  have hb : (3 : ℝ) < bmin := by linarith
  rcases hr.eq_or_lt with hr0 | hrpos
  · rw [middleFrame_Nbr_congr pr hne root W I hr bmin h hr0.symm (polarInputs I),
      middleFrame_lam_congr pr hne root W I hr bmin h hr0.symm (polarInputs I)]
    exact (middleFrame pr hne root W (polarInputs I) hr bmin h).gram_bracket (polarInputs_sum I) hb
      hcap hdom hP (middleFrame_matchingReserved pr hne root W (polarInputs I) hr h hb7 hbp)
  · exact (middleFrame pr hne root W I hr bmin h).gram_bracket
      (show (0 : ℝ) ≤ I.f₁ + I.h₁ by nlinarith) hb hcap hdom hP
      (middleFrame_matchingReserved pr hne root W I hr h hb7 hbp)

/-- The six records of `Ñ₀ - μ` are positive records (V3's `isPositiveRecord_diag`; their
coefficients are nonnegative when `(f₁ + h₁) r ≥ 0` and `bmin > 3`). -/
theorem middle_bracketRec_positive (hG0 : 0 ≤ (I.f₁ + I.h₁) * r) (hb : 3 < bmin) (i : Fin 6) :
    IsPositiveRecord ((middleFrame pr hne root W I hr bmin h).bracketRec i) := by
  set D := middleFrame pr hne root W I hr bmin h
  have h1 := middleFrame_one_uniform pr hne root W I hr bmin h
  have hPi := inv_nonneg.mpr D.P_pos.le
  have hv := D.coef2_nonneg .D
  have hG : 0 ≤ (D.I.f₁ + D.I.h₁) * D.r * (D.W.v .D * D.r ^ 2) := mul_nonneg hG0 hv
  have hH := D.hCoef_nonneg hb
  fin_cases i
  · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hv)
  · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hv)
  · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hG)
  · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hG)
  · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hH)
  · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hH)

/-- The six records of `Ñ₀ - μ` are reserved diagonal. -/
theorem middle_bracketRec_diagonal (i : Fin 6) :
    TheoremC.IsDiagonalAt reservedCut ((middleFrame pr hne root W I hr bmin h).bracketRec i) := by
  fin_cases i <;> exact diagonal_smul ((middleFrame pr hne root W I hr bmin h).diag_diagonal _ _) _

variable (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
  {d : ℝ} (hd : 0 ≤ d) (hs : BlockSharp pr hne h d)

/-- The differences of the first stage of a middle block sum to the frame's `δ_E`. -/
theorem middleStage_delta :
    ∑ i, ((middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ' i -
        (middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ i) =
      (middleFrame pr hne root W I hr bmin h).deltaE :=
  ((middleFrame pr hne root W I hr bmin h).deltaE_eq_sum).symm

/-- **The (CP3) data of a middle block** (`def:cp3` at the atom, `lem:record:gram`): the six
records of `Ñ₀ - μ = (E_add + G + H)/P(r)`, `Ñ₀ = μ + ∑_i κu_i`, and the bracket
`(Ñ λ; λ Ñ) ⪰_ι 0` with `Ñ = Ñ₀ + δ_E = λ + (F_fold + H)/P(r)`, over A1's first stage `middleStage`.
Hypotheses: `μ ⪰_ι 0` ((R2) at `ι`); `7 ≤ bmin ≤` every prime of the block; the layer caps
(`lem:front12:reference`(ii)); `v_𝔱 ≥ k_𝔱 w_𝔱`; the protection `v_D ≥ 2 k_D w_D`
(`eq:protection`). The sign `(f₁ + h₁) r ≥ 0` of the polarization coefficient comes from the rows
`hrows₁` of the first stage (`polarCoef_nonneg`). -/
noncomputable def middleGram
    (hμ : reservedCut.Positive (signedIntegral (middleBlockReference pr hne root W hr).weight))
    (hb7 : 7 ≤ bmin) (hbp : ∀ i, bmin ≤ (pr i : ℝ))
    (hcap : MiddleLayerCaps (middleBlockFieldLaws pr hne root) I.k r)
    (hdom : ∀ t, I.k t * W.w t ≤ W.v t) (hP : W.Protects I) :
    AtomGram (middleStage pr hne root W I hr bmin h hrows₁ hd hs) where
  Iu := Fin 6
  κu := (middleFrame pr hne root W I hr bmin h).bracketRec
  κu_pos := middle_bracketRec_positive pr hne root W I hr bmin h
    (polarCoef_nonneg pr hne I hrows₁) (by linarith)
  κu_diag := middle_bracketRec_diagonal pr hne root W I hr bmin h
  N₀ := (middleFrame pr hne root W I hr bmin h).Nbr0
  N₀_sub := by
    rw [← middleFrame_mu pr hne root W I hr bmin h]
    exact (middleFrame pr hne root W I hr bmin h).Nbr0_sub_mu_eq_sum
  N₀_off hf := absurd hf.symm Bool.false_ne_true
  lam_sym := by
    rw [middleStage_lam]
    refine lam_symmetric_of_mu _ ?_
    rw [middleFrame_mu]
    exact hμ
  N_nonneg := by
    rw [middleStage_delta, ← FrameData.Nbr_eq_Nbr0_add_deltaE]
    exact middle_Nbr_nonneg pr hne root W I hr bmin h (polarCoef_nonneg pr hne I hrows₁)
      (by linarith)
  bracket := by
    rw [middleStage_lam, middleStage_delta, ← FrameData.Nbr_eq_Nbr0_add_deltaE]
    exact middle_gram_bracket pr hne root W I hr bmin h (polarCoef_nonneg pr hne I hrows₁) hb7 hbp
      hcap hdom hP

/-! ## The price `u_𝔅` (`lem:record:middle-prices`) -/

variable (hμ : reservedCut.Positive (signedIntegral (middleBlockReference pr hne root W hr).weight))
  (hb7 : 7 ≤ bmin) (hbp : ∀ i, bmin ≤ (pr i : ℝ))
  (hcap : MiddleLayerCaps (middleBlockFieldLaws pr hne root) I.k r)
  (hdom : ∀ t, I.k t * W.w t ≤ W.v t) (hP : W.Protects I)

/-- **The price `u_𝔅` of `Ñ₀ - μ`** (`lem:record:middle-prices`, `def:cp3`), as an identity:
`u_𝔅 = P(r)⁻¹ (2 v_D r² + 2 v_D (f₁ + h₁) r³ + 12 w_S r/(bmin - 3)) q_𝔅^{2a}`. -/
theorem middleGram_uprice (sel : ℝ) :
    (middleGram pr hne root W I hr bmin h hrows₁ hd hs hμ hb7 hbp hcap hdom hP).uprice sel =
      (midPoly W r)⁻¹ * (2 * W.v .D * r ^ 2 + 2 * W.v .D * (I.f₁ + I.h₁) * r ^ 3 +
        12 * W.w .S * r / (bmin - 3)) * sel := by
  set D := middleFrame pr hne root W I hr bmin h
  change ∑ i, mass (D.bracketRec i) * sel = _
  rw [D.uprice_eq]
  obtain ⟨-, -, mEa, mG, mH, -, -⟩ := D.records_mass
  have hm : mass (D.Nbr0 - D.mu) = D.P⁻¹ * (mass D.Eadd + mass D.Gpol + mass D.Hdiag) := by
    rw [D.Nbr0_sub_mu]
    rfl
  rw [hm, mEa, mG, mH]
  rfl

/-- **The price bound of `lem:record:middle-prices`** for `Ñ₀ - μ` (V3's `uprice_le`): when
`r² bmin = 1` and `3 < X ≤ bmin`, `u_𝔅 ≤ (2 v_D r² + (2 v_D (f₁ + h₁) + 12 w_S/(1 - 3/X)) r³)
q_𝔅^{2a}`. (`r > 0` here, so `f₁ + h₁ ≥ 0` by the rows.) -/
theorem middleGram_uprice_le (hrb : r ^ 2 * bmin = 1) {Xs : ℝ} (hX : 3 < Xs) (hXb : Xs ≤ bmin)
    {sel : ℝ} (hsel : 0 ≤ sel) :
    (middleGram pr hne root W I hr bmin h hrows₁ hd hs hμ hb7 hbp hcap hdom hP).uprice sel ≤
      (2 * W.v .D * r ^ 2 + (2 * W.v .D * (I.f₁ + I.h₁) + 12 * W.w .S / (1 - 3 / Xs)) * r ^ 3) *
        sel := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    norm_num at hrb
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hG0 := polarCoef_nonneg pr hne I hrows₁
  exact (middleFrame pr hne root W I hr bmin h).uprice_le
    (show (0 : ℝ) ≤ I.f₁ + I.h₁ by nlinarith) hrb hX hXb hsel

end Block

end Sarkozy.GramBracketPaper
