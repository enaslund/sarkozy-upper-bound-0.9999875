module

public import Sarkozy.ThetaOne.Inputs

@[expose] public section

/-!
# Sanity checks for the baseline inputs of `SF` (`ϑ = 1`)

* **`hfold` is consistent on its own** (`hfold_satisfiable`): for any data, any sharp
  decompositions and any `ε`, the remainders `r_± := max(𝔈_±, 0) + |(∏ g)(1 + ε) Y|` are
  nonnegative and satisfy `hfold`. So, as DC2 found for the `hdiff` fields, the content of
  `SharpFirstBaseInputs` sits in the **summation `hrem`**, which shares `r_±`: an audit should
  check `hfold` and `hrem` together, with the paper's `r_±` (the remainders of
  `prop:record:density-structured` at the folded laws).
* **The pieces reproduce the term exactly**: `wpieceSum_eq` (in `SharpFirstWhole`).
* **The folded factors are those of admissible measures**: every non-`μ` factor of
  `wpieceLp`/`wpieceLm` is the diagonal law of a half marginal of a positive record, or the full
  folded law `κ(1) ∑_s π_s Diag(m_±(κ_s))` of a whole difference (`wpieceLp_positive`,
  `wpieceLm_positive`; DC2's `bpieceLp/Lm_positiveRecord` for the latter).
* At `ϑ = 1` the endgame's exponent is `densityExponent = 1` (`TheoremC.densityExponent_eq_one`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ThetaOne

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.Structured ReflectionCut

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`hfold` alone is satisfiable** for any data: take
`r_± := max(𝔈_±, 0) + |(∏ g)(1 + ε) Y|`. -/
theorem hfold_satisfiable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (dec : ∀ L, DecFamily D L) (ε : ℕ → ℝ) :
    ∃ rp rm : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
        (∀ b, WPiece D L b) → ℝ,
      (∀ L A σ j f, 0 ≤ rp L A σ j f ∧ 0 ≤ rm L A σ j f) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j → ∀ f,
      foldedPlus (D.FS.cut j) (wpieceLp (dec L) j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) + rp L A σ j f ∧
        foldedMinus (D.FS.cut j) (wpieceLm (dec L) j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) + rm L A σ j f) := by
  refine ⟨fun L A _ j f => max (foldedPlus (D.FS.cut j) (wpieceLp (dec L) j)
      (fun _ => blockLift m₀ blk p L A) f) 0 +
        |(∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A)|,
    fun L A _ j f => max (foldedMinus (D.FS.cut j) (wpieceLm (dec L) j)
      (fun _ => blockLift m₀ blk p L A) f) 0 +
        |(∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A)|, ?_, ?_⟩
  · intro L A σ j f
    exact ⟨add_nonneg (le_max_right _ _) (abs_nonneg _),
      add_nonneg (le_max_right _ _) (abs_nonneg _)⟩
  · refine Filter.Eventually.of_forall fun L => ?_
    intro C _ _ A _ _ σ _ j _ f
    set x := (∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A)
    have hx : 0 ≤ x + |x| := by
      have := neg_abs_le x
      linarith
    constructor
    · have := le_max_left (foldedPlus (D.FS.cut j) (wpieceLp (dec L) j)
        (fun _ => blockLift m₀ blk p L A) f) 0
      linarith
    · have := le_max_left (foldedMinus (D.FS.cut j) (wpieceLm (dec L) j)
        (fun _ => blockLift m₀ blk p L A) f) 0
      linarith

end Sarkozy.ThetaOne
