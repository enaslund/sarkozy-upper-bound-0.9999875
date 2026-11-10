module

public import Sarkozy.EnvelopeInputsBlock.EnvelopeCoupled
public import Sarkozy.TheoremCBlock.EnvelopeNonneg

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeInputsBlock

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame

variable {a : ℝ}

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut

section Final

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`EnvelopeBoundNonneg` from the per-term bounds with uniform nonnegative remainders**
(`lem:bracket-energy` for the selection envelopes, `def:robust`, `lem:record:record-expansion`(ii)):
`TheoremCParam.Structured.envelopeBoundNonneg_of_terms` with the remainder summation replaced by a
bound `∑_f r⁰_{ω,f} + ∑_σ r_{ω,σ} ≤ c₀ L^{-σ} α`, uniform in the selection
(`TheoremCParam.Structured.sum_selection_remainder_le`). The proof is P1's
`envelopeBound_of_terms_uniform`, with the extra hypotheses `r⁰ ≥ 0`, `r ≥ 0`. -/
theorem envelopeBoundNonneg_of_terms_uniform (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (ha : 0 ≤ a) (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {c₀ : ℝ}
    (hc₀ : 0 ≤ c₀)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (BlockAtom Bk J L → Bool) → ℝ)
    (r : ∀ L, Finset ℤ → Choice (D.CL.T L) → (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hr0 : ∀ L A ω f, 0 ≤ r0 L A ω f) (hr : ∀ L A ω σ, 0 ≤ r L A ω σ)
    (hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      (∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f) ∧
      (∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
        1 ≤ countVec (D.FS.tag L) σ j →
        |diagonalIntegral (tensorLaw (fun b => (σ b).elim
          (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
          (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))))
            (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ + r L A ω σ)))
    (hunif : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∑ f, r0 L A ω f +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          r L A ω σ ≤ remainder c₀ L A)) :
    D.EnvelopeBoundNonneg := by
  refine TheoremCBlock.Structured.envelopeBoundNonneg_of_terms D εE hε0 hεt
    (cE := Real.exp D.CL.S * Real.cosh D.CL.A * c₀)
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le) hc₀) r0 r hr0 hr hterms ?_
  filter_upwards [hunif] with L hL
  intro C hC hk A hA hY
  exact TheoremCBlock.Structured.sum_selection_remainder_le D ha L A _ hc₀ (hL C hC hk A hA hY)

omit [DecidableEq P] in
/-- The masses of the subset remainders are nonnegative: `m_𝔟 = 0` on the selected set, the mass
of the positive bracket records `∑_i κu_{𝔟,i}` (CP3) off it, and `1` where `f` does not choose
the records. -/
theorem subsetMass_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (f : BlockAtom Bk J L → Bool) (b : BlockAtom Bk J L) :
    0 ≤ (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1) := by
  have hmass : mass (∑ i, D.GB.κu L b i) = ∑ i, mass (D.GB.κu L b i) := by
    unfold mass
    rw [LinearMap.sum_apply]
  split_ifs
  · exact le_rfl
  · rw [hmass]
    exact sum_nonneg fun i _ =>
      TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1
  · exact zero_le_one

omit [DecidableEq P] in
/-- **`EnvelopeBoundNonneg` from the subset terms and the coupled per-term bounds**
(`lem:bracket-energy` with `lem:sharp-first` and `lem:density:coupled`; `def:robust`). The
hypotheses of `envelopeBound_of_coupledPieces` (I1's coupled reduction at a free exponent `a`),
together with `r⁰ ≥ 0` (`hs0`): the remainders of the subset terms are nonnegative, as the
paper's per-term remainders are absolute values. The selection remainders
`r_ω = ∑_f r⁰_{ω,f} + ∑_σ ∑_j ∑_f |c_f| r_{ω,σ,j,f}` are then nonnegative, which is the extra
field of `EnvelopeBoundNonneg` (P1's `TheoremCParam.Structured.envelopeBoundNonneg_of_terms`). -/
theorem envelopeBoundNonneg_of_coupledPieces (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {cE : ℝ} (hcE : 0 ≤ cE)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (BlockAtom Bk J L → Bool) → ℝ)
    (r : ∀ L, Finset ℤ → (ω : Choice (D.CL.T L)) → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
      (∀ b, CEPiece D L b) → ℝ)
    (hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f))
    (hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
      (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) →
      |diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A)| ≤
        (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) + r L A ω σ j f))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω *
          (∑ f, r0 L A ω f +
            ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f) ≤
          remainder cE L A))
    (hr0 : ∀ L A ω σ j f, 0 ≤ r L A ω σ j f) (hs0 : ∀ L A ω f, 0 ≤ r0 L A ω f) :
    D.EnvelopeBoundNonneg := by
  refine TheoremCBlock.Structured.envelopeBoundNonneg_of_terms D εE hε0 hεt hcE r0
    (fun L A ω σ => ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f) hs0
    (fun L A ω σ => sum_nonneg fun j _ => sum_nonneg fun f _ =>
      mul_nonneg (prod_nonneg fun b _ => abs_nonneg _) (hr0 L A ω σ j f)) ?_ hrem
  filter_upwards [envelopeBound_terms_of_coupled D εE hε0 r0 r hsub hcoup] with L hL
  intro C hC hk A hA hY ω hω
  obtain ⟨h1, h2⟩ := hL C hC hk A hA hY ω hω
  refine ⟨h1, fun σ hσ j hj => (h2 σ hσ j hj).trans ?_⟩
  have hsingle : ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f ≤
      ∑ j', ∑ f, (∏ b, |ecpieceCoef D L ω σ j' b (f b)|) * r L A ω σ j' f := by
    refine Finset.single_le_sum (f := fun j' => ∑ f, (∏ b, |ecpieceCoef D L ω σ j' b (f b)|) *
      r L A ω σ j' f) (fun j' _ => ?_) (Finset.mem_univ j)
    exact Finset.sum_nonneg fun f _ =>
      mul_nonneg (Finset.prod_nonneg fun b _ => abs_nonneg _) (hr0 L A ω σ j' f)
  linarith

omit [DecidableEq P] in
/-- **`EnvelopeBoundNonneg` from the subset terms and the coupled per-term bounds alone**
(`lem:bracket-energy`, `lem:sharp-first`, `lem:density:coupled`; `def:robust`): the hypotheses of
`envelopeBound_of_coupledPieces_uniform` (I1's coupled reduction with the remainder summation
proved, at a free exponent `a`), with the conclusion `EnvelopeBoundNonneg`. No extra hypothesis is
needed: the remainders `∏_f mass(∑κu) c₁ L^{-σ} α` and `(∏_𝔟 m_𝔟(f_𝔟)) c₁ L^{-σ} α` are
nonnegative (`subsetMass_nonneg`, `ecpieceM_nonneg`). This is the per-term form of the field
`hE1` of `MainAnchor.PaperObligations`. -/
theorem envelopeBoundNonneg_of_coupledPieces_uniform
    (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (ha : 0 ≤ a) (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {c₁ : ℝ}
        (hc₁ : 0 ≤ c₁)
    (hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
            remainder c₁ L A))
    (hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
      (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) →
      |diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A)| ≤
        (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) +
          (∏ b, ecpieceM D L b (f b)) * remainder c₁ L A)) :
    D.EnvelopeBoundNonneg := by
  have hrem0 : ∀ L A, 0 ≤ remainder c₁ L A := fun L A => by
    unfold remainder
    exact mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  set K := Real.exp D.GB.U₀ * (1 + (Fintype.card D.FS.Tag : ℝ) *
    Real.exp (∑ j, (D.FS.dT j + D.FS.vT j))) * c₁ with hK
  have hK0 : 0 ≤ K := by positivity
  refine envelopeBoundNonneg_of_terms_uniform D ha εE hε0 hεt hK0
    (fun L A ω f =>
      (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
        remainder c₁ L A)
    (fun L A ω σ => ∑ j, ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
      ((∏ b, ecpieceM D L b (f b)) * remainder c₁ L A))
    (fun L A ω f => mul_nonneg (prod_nonneg fun b _ => subsetMass_nonneg D L ω f b)
      (hrem0 L A))
    (fun L A ω σ => sum_nonneg fun j _ => sum_nonneg fun f _ =>
      mul_nonneg (prod_nonneg fun b _ => abs_nonneg _)
        (mul_nonneg (prod_nonneg fun b _ => ecpieceM_nonneg D L b (f b)) (hrem0 L A))) ?_ ?_
  · filter_upwards [envelopeBound_terms_of_coupled D εE hε0
      (fun L A ω f =>
        (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
          remainder c₁ L A)
      (fun L A _ _ _ f => (∏ b, ecpieceM D L b (f b)) * remainder c₁ L A) hsub hcoup]
      with L hL
    intro C hC hk A hA hY ω hω
    obtain ⟨h1, h2⟩ := hL C hC hk A hA hY ω hω
    refine ⟨h1, fun σ hσ j hj => (h2 σ hσ j hj).trans ?_⟩
    have hsingle : ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
        ((∏ b, ecpieceM D L b (f b)) * remainder c₁ L A) ≤
        ∑ j', ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j' b (f b)|) *
          ((∏ b, ecpieceM D L b (f b)) * remainder c₁ L A) := by
      refine Finset.single_le_sum (f := fun j' => ∑ f : (∀ b, CEPiece D L b),
        (∏ b, |ecpieceCoef D L ω σ j' b (f b)|) *
          ((∏ b, ecpieceM D L b (f b)) * remainder c₁ L A)) (fun j' _ => ?_)
        (Finset.mem_univ j)
      exact Finset.sum_nonneg fun f _ => mul_nonneg (Finset.prod_nonneg fun b _ => abs_nonneg _)
        (mul_nonneg (prod_nonneg fun b _ => ecpieceM_nonneg D L b (f b)) (hrem0 L A))
    linarith
  · refine Filter.Eventually.of_forall fun L => ?_
    intro C _ _ A _ _ ω _
    set rem := remainder c₁ L A
    have hr := hrem0 L A
    have hsub_rem := TheoremCBlock.Structured.sum_subset_remainder_le D ha L A ω hc₁
    have hterm : ∀ σ : (∀ b, Option (D.FS.Ib L b)), ∀ j,
        ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            ((∏ b, ecpieceM D L b (f b)) * rem) ≤
          maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.GB.U₀ * rem := by
      intro σ j
      have h1 : ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            ((∏ b, ecpieceM D L b (f b)) * rem) =
          (∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            ∏ b, ecpieceM D L b (f b)) * rem := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f _ => ?_
        ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (coupled_weighted_emass_le D ha L ω σ j) hr
    have hsum := sum_maxWeight_le (TheoremCBlock.Structured.dprice_nonneg D L)
        (TheoremCBlock.Structured.vprice_nonneg D L)
    have hexp := Real.exp_le_exp.mpr (TheoremCBlock.Structured.sum_prices_le_totals D L)
    have hstep1 := Finset.sum_le_sum (s := univ.filter
        (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none))
      fun σ _ => Finset.sum_le_sum (s := (univ : Finset D.FS.Tag)) fun j _ => hterm σ j
    have hstep2 : ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ _j : D.FS.Tag, maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.GB.U₀ * rem =
        (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
          ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    have hstep3 : (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          maxWeight (D.FS.dprice L) (D.FS.vprice L) σ ≤
        (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
          Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) :=
      mul_le_mul_of_nonneg_left (hsum.trans hexp) (by positivity)
    have hsharp := hstep1.trans (le_of_eq hstep2) |>.trans hstep3
    have hfin : remainder K L A = remainder (Real.exp D.GB.U₀ * c₁) L A +
        (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
          Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) := by
      unfold rem remainder
      rw [hK]
      ring
    rw [hfin]
    exact add_le_add hsub_rem hsharp

end Final

end Sarkozy.EnvelopeInputsBlock
