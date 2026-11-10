module

public import Sarkozy.EnvelopeInputsBlock.EnvelopeCoupledNonneg
public import Sarkozy.EnvelopeInputsBlock.EnvelopeUniform

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

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`EnvelopeBoundNonneg` from the subset terms and the folded per-term bounds**
(`lem:bracket-energy` with `lem:sharp-first` and `lem:record:folded-energy`; `def:robust`): the
hypotheses of `envelopeBound_of_foldedPieces` (I1's package 2 at a free exponent `a`), together
with `r⁰ ≥ 0` (`hs0`). The coefficients of the folded remainders are `choiceWeight = ∏ |c| d` with
`d ≥ 0` (`epieceD_nonneg`), so the selection remainders are nonnegative. -/
theorem envelopeBoundNonneg_of_foldedPieces (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (dec : ∀ L, DecFamily D L)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {cE : ℝ} (hcE : 0 ≤ cE)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (BlockAtom Bk J L → Bool) → ℝ)
    (rp rm : ∀ L, Finset ℤ → Choice (D.CL.T L) → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
      (∀ b, EPiece (dec L) b) → ℝ)
    (hr0 : ∀ L A ω σ j f, 0 ≤ rp L A ω σ j f ∧ 0 ≤ rm L A ω σ j f)
    (hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f))
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f,
      foldedPlus (D.FS.cut j) (epieceLp (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) + rp L A ω σ j f ∧
        foldedMinus (D.FS.cut j) (epieceLm (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) + rm L A ω σ j f))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω *
          (∑ f, r0 L A ω f +
            ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
                ((rp L A ω σ j f + rm L A ω σ j f) / 2)) ≤ remainder cE L A))
    (hs0 : ∀ L A ω f, 0 ≤ r0 L A ω f) :
    D.EnvelopeBoundNonneg :=
  TheoremCBlock.Structured.envelopeBoundNonneg_of_terms D εE hε0 hεt hcE r0
    (fun L A ω σ => ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
      ((rp L A ω σ j f + rm L A ω σ j f) / 2)) hs0
    (fun L A ω σ => sum_nonneg fun j _ => sum_nonneg fun f _ => mul_nonneg
      (by unfold choiceWeight; exact prod_nonneg fun b _ =>
        mul_nonneg (abs_nonneg _) (epieceD_nonneg (dec L) b (f b)))
      (div_nonneg (add_nonneg (hr0 L A ω σ j f).1 (hr0 L A ω σ j f).2) zero_le_two))
    (envelopeBound_terms_of_folded D dec εE hε0 r0 rp rm hr0 hsub hfold) hrem

omit [DecidableEq P] in
/-- **`EnvelopeBoundNonneg` from the subset terms and the folded per-term bounds alone**
(`lem:bracket-energy`, `lem:sharp-first`, `lem:record:folded-energy`; `def:robust`): the
hypotheses of `envelopeBound_of_foldedPieces_uniform` (I1's package 2 with the remainder
summation proved, at a free exponent `a`), with the conclusion `EnvelopeBoundNonneg` and no extra
hypothesis: the remainders are nonnegative (`subsetMass_nonneg`, `epieceD_nonneg`,
`epieceM_nonneg`). -/
theorem envelopeBoundNonneg_of_foldedPieces_uniform
    (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (ha : 0 ≤ a) (dec : ∀ L, DecFamily D L)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
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
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ j f,
      foldedPlus (D.FS.cut j) (epieceLp (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) +
            (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A ∧
        foldedMinus (D.FS.cut j) (epieceLm (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) +
            (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A)) :
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
    (fun L A ω σ => ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
      (((∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A +
        (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A) / 2))
    (fun L A ω f => mul_nonneg (prod_nonneg fun b _ => subsetMass_nonneg D L ω f b)
      (hrem0 L A))
    (fun L A ω σ => sum_nonneg fun j _ => sum_nonneg fun f _ => mul_nonneg
      (by unfold choiceWeight; exact prod_nonneg fun b _ =>
        mul_nonneg (abs_nonneg _) (epieceD_nonneg (dec L) b (f b)))
      (div_nonneg (add_nonneg
        (mul_nonneg (prod_nonneg fun b _ => epieceM_nonneg (dec L) b (f b)) (hrem0 L A))
        (mul_nonneg (prod_nonneg fun b _ => epieceM_nonneg (dec L) b (f b)) (hrem0 L A)))
        zero_le_two)) ?_ ?_
  · -- the two families of term bounds
    have hgen := (envelopeBound_terms_of_folded D dec εE hε0
      (fun L A ω f =>
        (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
          remainder c₁ L A)
      (fun L A ω _ _ f => (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A)
      (fun L A ω _ _ f => (∏ b, epieceM (dec L) b (f b)) * remainder c₁ L A)
      (fun L A ω σ j f => ⟨mul_nonneg (prod_nonneg fun b _ => epieceM_nonneg (dec L) b (f b))
        (hrem0 L A), mul_nonneg (prod_nonneg fun b _ => epieceM_nonneg (dec L) b (f b))
        (hrem0 L A)⟩) hsub (by
        filter_upwards [hfold] with L hL
        intro C hC hk A hA hY ω hω _ _ j _ f
        exact hL C hC hk A hA hY ω hω j f))
    exact hgen
  · refine Filter.Eventually.of_forall fun L => ?_
    intro C _ _ A _ _ ω _
    set rem := remainder c₁ L A
    have hr := hrem0 L A
    have hsub_rem := TheoremCBlock.Structured.sum_subset_remainder_le D ha L A ω hc₁
    have hterm : ∀ σ : (∀ b, Option (D.FS.Ib L b)), ∀ j,
        ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
          (((∏ b, epieceM (dec L) b (f b)) * rem + (∏ b, epieceM (dec L) b (f b)) * rem) / 2) ≤
          maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.GB.U₀ * rem := by
      intro σ j
      have h1 : ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
          (((∏ b, epieceM (dec L) b (f b)) * rem + (∏ b, epieceM (dec L) b (f b)) * rem) / 2) =
          (∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
            ∏ b, epieceM (dec L) b (f b)) * rem := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f _ => ?_
        ring
      rw [h1]
      exact (mul_le_mul_of_nonneg_right (weighted_emass_le D ha L (dec L) ω σ j) hr).trans
        (mul_le_mul_of_nonneg_right (tagWeight_selPrice_le D L ω σ j) hr)
    have hsum := sum_maxWeight_le (TheoremCBlock.Structured.dprice_nonneg D L)
        (TheoremCBlock.Structured.vprice_nonneg D L)
    have hexp := Real.exp_le_exp.mpr (TheoremCBlock.Structured.sum_prices_le_totals D L)
    have hsharp : ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
          (((∏ b, epieceM (dec L) b (f b)) * rem + (∏ b, epieceM (dec L) b (f b)) * rem) / 2) ≤
        (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
          Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) := by
      calc ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
              (((∏ b, epieceM (dec L) b (f b)) * rem +
                (∏ b, epieceM (dec L) b (f b)) * rem) / 2)
          ≤ ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              ∑ _j : D.FS.Tag, maxWeight (D.FS.dprice L) (D.FS.vprice L) σ *
                Real.exp D.GB.U₀ * rem :=
            Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun j _ => hterm σ j
        _ = (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
              ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
                maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
        _ ≤ (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
              Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) :=
            mul_le_mul_of_nonneg_left (hsum.trans hexp) (by positivity)
    calc ∑ f : BlockAtom Bk J L → Bool,
          (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
            rem +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
            (((∏ b, epieceM (dec L) b (f b)) * rem +
              (∏ b, epieceM (dec L) b (f b)) * rem) / 2)
        ≤ remainder (Real.exp D.GB.U₀ * c₁) L A + (Fintype.card D.FS.Tag : ℝ) *
            Real.exp D.GB.U₀ * rem * Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) :=
          add_le_add hsub_rem hsharp
      _ = remainder K L A := by
          unfold rem remainder
          rw [hK]
          ring

end Sarkozy.EnvelopeInputsBlock
