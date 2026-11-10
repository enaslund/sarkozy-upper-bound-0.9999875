module

public import Sarkozy.DensityFibre.FibreMoment
public import Sarkozy.DensityFibre.FoldedFields

@[expose] public section

/-!
# Sanity checks for `DensityFibre`

Non-vacuity of the new hypotheses, and their relation to the earlier ones.

* `fibre_moment_theta_one`: at `θ = 1` the convexity split costs nothing,
  `E Z ≤ K E α + E|Z − Z̃|` (the baseline fibre step).
* `fibreModel_hdc_of_actual`: with the actual fibre energies as models (`Z̃ = Z`), the dc input
  `hdc` of `FibreModelInputs` holds for every `η`, `c₁ ≥ 0`. The model input `hmod` then becomes
  B5's pointwise fibre bound. So `FibreModelInputs` is no stronger than B5's
  `coupledFibreMoment_of_fibres` route.
* `fibreModel_hmod_of_zero`: with the zero model, `hmod` holds. The two inputs are each
  satisfiable; their conjunction is the content (`prop:density:production`).
* `envHdiffL_hfold_satisfiable`: the per-choice folded hypothesis of `envHdiffL_of_folded` holds
  for any data, with `t = 1`, `M_± = 0`, `r_± = 𝔈_±` and the matching `rch`. It is consistent;
  its content is in the size of `rch`, i.e. in the summation fields `hm`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic Sarkozy.DensityUpgrade

/-- **At `θ = 1` the fibre step is exact**: `E Z ≤ K E α + E|Z − Z̃|` when `Z̃ ≤ K α`. -/
theorem fibre_moment_theta_one {Q : Type*} [Fintype Q] {Z Zt α : Q → ℝ} (hZ : ∀ q, 0 ≤ Z q)
    (hα : ∀ q, 0 ≤ α q) {K : ℝ} (hK : 0 ≤ K) (hmod : ∀ q, Zt q ≤ K * α q ^ (1 : ℝ)) :
    coupledMean (fun q => Z q ^ (1 / (1 : ℝ))) ^ (1 : ℝ) ≤
      K * coupledMean α ^ (1 : ℝ) + coupledMean (fun q => |Z q - Zt q|) := by
  have h := fibre_moment_le_of_model hZ hα hK le_rfl one_pos hmod
  simpa using h

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **The dc input holds for the actual fibres as models** (`Z̃ = Z`): the averaged difference is
`0`. -/
theorem fibreModel_hdc_of_actual (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (η : ℕ → ℝ) {c₁ : ℝ} (hc₁ : 0 ≤ c₁) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ f : (∀ b, CPiece D L b),
      (∏ b, cpieceW D L b (f b)) * ((1 + 1 / η L) ^ (densityExponent - 1) *
        coupledMean (fun q : SharpLabels D L f × SpecLabels D L f =>
          |fibreEnergy D L A f q.1 q.2 - fibreEnergy D L A f q.1 q.2|)) ≤
      (∏ b, cpieceM D L b (f b)) * remainder c₁ L A) := by
  refine Param.AtCounterexamples.of_forall _ fun L A f => ?_
  simp only [sub_self, abs_zero]
  have h0 : coupledMean (fun _ : SharpLabels D L f × SpecLabels D L f => (0 : ℝ)) = 0 := by
    unfold coupledMean
    simp
  rw [h0, mul_zero, mul_zero]
  refine mul_nonneg (Finset.prod_nonneg fun b _ => cpieceM_nonneg D L b _) ?_
  unfold remainder
  exact mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (density_nonneg _ _)

omit [DecidableEq P] in
/-- **The model input holds for the zero model.** -/
theorem fibreModel_hmod_of_zero (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (u : ℕ → ℝ) (hu : ∀ L, 0 ≤ u L) (price : ∀ L, (∀ b, CPiece D L b) → ℝ)
    (hprice0 : ∀ L f, 0 ≤ price L f) :
    AtCounterexamplesC (Params.ofDecay a) D.Y (fun C L A => ∀ (f : ∀ b, CPiece D L b) q,
      (0 : ℝ) ≤ (1 + u L) * C * (L : ℝ) ^ (-a) * price L f *
        termFibreDensity D L A f q ^ densityExponent) := by
  refine Eventually.of_forall fun L C hC _ A _ _ f q => ?_
  have hu1 : 0 ≤ 1 + u L := by linarith [hu L]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu1 (by linarith))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hprice0 L f))
    (Real.rpow_nonneg (termFibreDensity_nonneg D L A f q) _)

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The folded per-choice hypothesis is consistent**: for any data, `t = 1`, `M_± = 0`,
`r_± = 𝔈_±` satisfy it, with `rch` the mean of the two weighted folded sums. -/
theorem envHdiffL_hfold_satisfiable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (L : ℕ) (A : Finset ℤ) (dec : DecFamily D L) {M : ℝ} (hM : 0 ≤ M)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
    (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    ∃ (t Mp Mm : ℝ) (rp rm : (∀ b, HPiece D L b) → ℝ), 0 < t ∧ t * Mp + Mm / t ≤ 2 * M ∧
      (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
        foldedPlus (D.FS.cut j) (bpieceLp D L (TheoremCBlock.Structured.envIncL D L) dec j)
          (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
            ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
          (∏ b, bpieceG D L b (φ b)) * Mp + rp φ) ∧
      (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
        foldedMinus (D.FS.cut j) (bpieceLm D L (TheoremCBlock.Structured.envIncL D L) dec j)
          (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
            ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
          (∏ b, bpieceG D L b (φ b)) * Mm + rm φ) ∧
      (t * ∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rp φ +
        (∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rm φ) / t) / 2 ≤
        (∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ *
            foldedPlus (D.FS.cut j) (bpieceLp D L (TheoremCBlock.Structured.envIncL D L) dec j)
              (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
                (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ +
          ∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ *
            foldedMinus (D.FS.cut j) (bpieceLm D L (TheoremCBlock.Structured.envIncL D L) dec j)
              (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
                (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ) / 2 := by
  set a' : Slot → (∀ b, BlockLabel m₀ blk p L b) → ℝ := fun v x =>
    pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
      (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
      ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)
  refine ⟨1, 0, 0,
    fun φ => foldedPlus (D.FS.cut j)
      (bpieceLp D L (TheoremCBlock.Structured.envIncL D L) dec j) a' φ,
    fun φ => foldedMinus (D.FS.cut j)
      (bpieceLm D L (TheoremCBlock.Structured.envIncL D L) dec j) a' φ,
    one_pos, by simp [hM], fun φ _ => by simp, fun φ _ => by simp, ?_⟩
  rw [one_mul, div_one]
