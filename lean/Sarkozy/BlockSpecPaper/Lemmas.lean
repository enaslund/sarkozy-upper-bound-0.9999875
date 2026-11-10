module

public import Sarkozy.BlockSpecPaper.Spec

@[expose] public section

/-!
# The analytic inputs in the paper's lemma form (`lem:front12:reference`, `lem:upper-reference-rp`)

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(i),(ii);
`paper/sections/25_upper_reference.tex`, `lem:upper-reference-rp`(ii);
`paper/sections/20_middle_reference.tex`, `def:record:exact-blocks`(c),(d);
`def:record:upper-bands`(b).

`PaperAnalyticInputs cell` (`Spec.lean`) asks for the analytic inequalities on each block of the
partition. The paper proves them in a form that does not refer to the partition: **for every block
of class-three primes of a piece (or band) whose logarithmic length is within the budget**, with
`r = b^{-1/2}` for its least prime `b`. This file states that form, one statement per piece or band,
and derives `PaperAnalyticInputs cell` from it and from the budget of the partition:

* `MiddleUniformLemma i` (31 pieces) and `MiddleIndividualLemma i u` (pieces `30`, `31`): for every
  finite family `pr : ι → ℕ` of distinct primes `p ≡ 3 (mod 4)` in `[X_i, X_{i+1})` with
  `∑ log p ≤ L = 570` and least prime `b`, and every proof of nonemptiness, the five inequalities
  `RowBounds` (`j = 2, 1`), `RootEnvelope` (L20, L10), `MiddleLayerCaps` at the ALLp caps of piece
  `i` and `r = b^{-1/2}` (`lem:front12:reference`(i),(ii)). *Hypotheses* (spectral).
* `UpperBandLemma k` (310 bands): the same for the bands, with the band budget `L_band` of the
  record and `ValidInputs` ((V1)–(V3), `lem:upper-reference-rp`(ii)). *Hypothesis* (spectral).
* `PaperBudget cell`: every block of a middle piece has `∑ log p ≤ 570`, every block of band `k` has
  `∑ log p ≤ L_band(k)`. This is a property of the within-site rule (`def:record:exact-blocks`(c),
  (d), `def:record:upper-bands`(b)); V1's `greedy_log_budget` and `cellBlock_log_budget` prove it
  for the greedy blocks and the cells, given the recorded bins and `n_j`. *Hypothesis*
  (combinatorial, on `cell`).
* **`paperAnalyticInputs_of_lemmas`**: these give `PaperAnalyticInputs cell`.

The lemma forms are weaker than "for every block of primes `≥ X_i`" (they also assume `p < Y_i`,
`p ≡ 3 (4)`, distinct primes and the budget), so they are implied by the paper's statements.
-/

open Finset

namespace Sarkozy.BlockSpecPaper

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.FirstStagePaper

/-- **`lem:front12:reference`(i),(ii) on piece `i` with the uniform root, at the ALLp caps.** For
every block of distinct class-three primes of the piece with `∑ log p ≤ 570` and least prime `b`:
the rows at `j = 2, 1`, the root envelopes of L20 and L10 and the layer caps, at `r = b^{-1/2}`.
*Hypothesis* (spectral). -/
def MiddleUniformLemma (i : Fin 33) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RowBounds (fieldDatum (middleBlock_datumHyp₂ pr hne)) (allpInputs i).f₂ (allpInputs i).h₂
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).f₁ (allpInputs i).h₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₂ pr hne)) (allpInputs i).d
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).d₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      MiddleLayerCaps (middleBlockFieldLaws pr hne (uniformRoot pr hne)) (allpInputs i).k
        ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- **`lem:front12:reference`(i),(ii) on piece `i` with the individual-square root of parameter `u`
(`def:positive-root`), at the ALLp caps.** As `MiddleUniformLemma`. *Hypothesis* (spectral). -/
def MiddleIndividualLemma (i : Fin 33) (u : ℚ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RowBounds (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) (allpInputs i).f₂
        (allpInputs i).h₂ ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).f₁ (allpInputs i).h₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) (allpInputs i).d
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).d₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      MiddleLayerCaps (middleBlockFieldLaws pr hne (individualBlockRoot pr u hne.L2))
        (allpInputs i).k ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- **`lem:upper-reference-rp`(ii) on band `k`** ((V1)–(V3) for the band's recorded inputs and
caps): for every block of distinct class-three primes of the band with `∑ log p ≤ L_band` (the
record's budget) and least prime `b`, `ValidInputs` at `r = b^{-1/2}`. *Hypothesis* (spectral). -/
def UpperBandLemma (k : Fin 310) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2) →
    (∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget) →
    (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne hW' hp', ValidInputs (upperBlockFieldLaws pr hne) (block_upperDatumHyp pr hW' hp' hne)
      ((b : ℝ) ^ (-(1 / 2 : ℝ))) (UpperRecords.bandOrd k) (UpperRecords.bandRes k)
      (UpperRecords.bandCap k)

variable (cell : ℕ → ℕ) in
/-- **The budget of the paper's partition** (`def:record:exact-blocks`(c),(d),
`def:record:upper-bands`(b)): a block of a middle piece has `∑ log p ≤ L = 570`, a block of band `k`
has `∑ log p ≤ L_band(k)`. *Hypothesis* on the within-site rule `cell` (combinatorial). -/
def PaperBudget : Prop :=
  ∀ b : PaperBlock cell,
    (∀ i, blockSite b = .inl i →
      ∑ j, Real.log (blockPrimes (paperBlockOf cell) b j) ≤ middleBudget) ∧
    (∀ k, blockSite b = .inr k →
      ∑ j, Real.log (blockPrimes (paperBlockOf cell) b j) ≤
        (UpperRecords.CompletionData.record k).budget)

variable {cell : ℕ → ℕ}

/-- The primes of a block are distinct. -/
theorem blockPrimes_injective (b : PaperBlock cell) :
    Function.Injective (blockPrimes (paperBlockOf cell) b) := by
  intro x y h
  have hx : blockPrimes (paperBlockOf cell) b x = x.1.1 := paperM0_cls3 (blockOf_of_coord x).1
  have hy : blockPrimes (paperBlockOf cell) b y = y.1.1 := paperM0_cls3 (blockOf_of_coord y).1
  rw [hx, hy] at h
  exact Subtype.ext (Subtype.ext h)

theorem blockPrimes_mem_piece {b : PaperBlock cell} {i : Fin 33} (hs : blockSite b = .inl i)
    (j : {j : PaperJ0 // paperAtomMap (paperBlockOf cell) j = .inr b}) :
    pieceStart i ≤ blockPrimes (paperBlockOf cell) b j ∧
      blockPrimes (paperBlockOf cell) b j < pieceStop i := by
  have h := mem_site j
  rw [hs] at h
  exact h

theorem blockPrimes_mem_band {b : PaperBlock cell} {k : Fin 310} (hs : blockSite b = .inr k)
    (j : {j : PaperJ0 // paperAtomMap (paperBlockOf cell) j = .inr b}) :
    (bandOf k).1 ≤ blockPrimes (paperBlockOf cell) b j ∧
      blockPrimes (paperBlockOf cell) b j < (bandOf k).2 := by
  have h := mem_site j
  rw [hs] at h
  exact h

/-- **The analytic inputs of the paper's blocks from the lemma forms and the budget.** -/
theorem paperAnalyticInputs_of_lemmas (hbud : PaperBudget cell)
    (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u) :
    PaperAnalyticInputs cell where
  upper b k hs := hU k _ (blockPrimes (paperBlockOf cell) b) (blockLeast b)
    (blockPrimes_injective b) (fun j => (blockPrimes_mod_ge b j).1) (blockPrimes_mem_band hs)
    ((hbud b).2 k hs) (blockLeast_le b) (blockLeast_mem b)
  uniform b i hs hu :=
    have h := hM i hu _ (blockPrimes (paperBlockOf cell) b) (blockLeast b)
      (blockPrimes_injective b) (fun j => (blockPrimes_mod_ge b j).1) (blockPrimes_mem_piece hs)
      ((hbud b).1 i hs) (blockLeast_le b) (blockLeast_mem b)
    { rows₂ := fun hne => (h hne).1
      rows₁ := fun hne => (h hne).2.1
      root₂ := fun hne => (h hne).2.2.1
      root₁ := fun hne => (h hne).2.2.2.1
      caps := fun hne => (h hne).2.2.2.2 }
  individual b i u hs hu :=
    have h := hI i u hu _ (blockPrimes (paperBlockOf cell) b) (blockLeast b)
      (blockPrimes_injective b) (fun j => (blockPrimes_mod_ge b j).1) (blockPrimes_mem_piece hs)
      ((hbud b).1 i hs) (blockLeast_le b) (blockLeast_mem b)
    { rows₂ := fun hne => (h hne).1
      rows₁ := fun hne => (h hne).2.1
      root₂ := fun hne => (h hne).2.2.1
      root₁ := fun hne => (h hne).2.2.2.1
      caps := fun hne => (h hne).2.2.2.2 }

end Sarkozy.BlockSpecPaper
