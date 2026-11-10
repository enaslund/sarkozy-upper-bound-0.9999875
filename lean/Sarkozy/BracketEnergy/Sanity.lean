module

public import Sarkozy.BracketEnergy.Bundles

@[expose] public section

/-!
# Sanity checks for the bracket inputs

* Off the first-stage atoms the bracket is the reference: `recLaw_off`, `delLaw_off`, `N_off`.
  So a term of the expansion that selects a record at an atom off the first stage vanishes
  (`term_energy_eq_zero_of_off`), and its first bound holds with remainder `0`
  (`first_bound_of_off`): the inputs `hfirst` are needed only for selections `g` inside the
  first-stage atoms, as in the paper (the sets `X'` of first-stage atoms outside `X`).
* If the first stage changes nothing outside `f` (`δ_E = 0` there), the difference input `hdiff`
  holds with remainder `0` (`diff_bound_of_delta_zero`): `Ñ = Ñ₀` outside `f`.
* `EnvelopeEnergyInputsCRT.ofExcess`, `FixedIntervalInputsCRT.ofExcess`: the remainders of B5's
  bundles are signed, so each bundle follows from (and implies) one averaged inequality: the
  average over the depth vectors and the indices of `∑_f (|E_f| − (B + z) Π Y ∏_f u)` is at most
  `c L^{-σ} α`. The bundles therefore assert a bound for the index-averaged energy, which is
  what the paper proves at fixed `𝒥` (`lem:envelope-energy`, proof: "Fix `𝒥` and the
  intervals"), not a bound at every residue index `ω`.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] in
/-- Off the first-stage atoms there are no reserved records: `Ñ₀ = μ`. -/
theorem recLaw_off (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) (hb : b ∉ D.FS.fs L) : recLaw D L b = 0 := by
  have h := N₀_eq D L b
  rw [D.GB.N₀_off L b hb] at h
  unfold muLaw at h
  have := congrArg (fun x => x - D.R.law p L b) h
  simp only [sub_self, add_sub_cancel_left] at this
  exact this.symm

omit [DecidableEq P] in
/-- Off the first-stage atoms there are no first-stage differences. -/
theorem delLaw_off (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) (hb : b ∉ D.FS.fs L) : delLaw D L b = 0 := by
  unfold delLaw
  have := D.FS.off L b hb
  exact Finset.sum_of_isEmpty _

omit [DecidableEq P] in
/-- Off the first-stage atoms the bracket is the reference. -/
theorem N_off (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) (hb : b ∉ D.FS.fs L) : D.GB.N L b = muLaw D L b := by
  rw [N_eq, recLaw_off D L b hb, delLaw_off D L b hb, add_zero, add_zero]

omit [DecidableEq P] in
/-- A term that selects a record off the first stage vanishes. -/
theorem term_energy_eq_zero_of_off (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (f g : BlockAtom Bk J L → Bool) (b : BlockAtom Bk J L) (hfb : f b = false)
    (hgb : g b = true) (hb : b ∉ D.FS.fs L) (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) :
    multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
      if f b then Qb b else if g b then recLaw D L b else muLaw D L b)) G = 0 := by
  rw [tensorLaw_eq_zero_of_factor _ b]
  · rfl
  · unfold crtLaws
    simp only [hfb, hgb, Bool.false_eq_true, ↓reduceIte, recLaw_off D L b hb]
    unfold pullLaw
    exact LinearMap.zero_comp _

omit [DecidableEq P] in
/-- **The first bound off the first stage**: for a selection `g` with a record off the first
stage, the first bound holds with remainder `0`. So `hfirst` matters only for `g` inside the
first-stage atoms. -/
theorem first_bound_of_off (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (f g : BlockAtom Bk J L → Bool) (b : BlockAtom Bk J L) (hfb : f b = false)
    (hgb : g b = true) (hb : b ∉ D.FS.fs L) (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ)
    {K z : ℝ} (hK : 0 ≤ K) (hz : 0 ≤ z) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
      if f b then Qb b else if g b then recLaw D L b else muLaw D L b)) G| ≤
      (1 + z) * K * ∏ b, (if g b then D.GB.uprice L b else 1) + 0 := by
  rw [term_energy_eq_zero_of_off D L h0 Qb f g b hfb hgb hb G, abs_zero, add_zero]
  exact mul_nonneg (mul_nonneg (by linarith) hK)
    (prod_nonneg fun b _ => by split_ifs; exacts [uprice_nonneg D L b, zero_le_one])

omit [DecidableEq P] in
/-- **The difference without first-stage changes**: if `δ_E = 0` at every atom outside `f`, then
`Ñ = Ñ₀` there and the difference input holds with remainder `0`. -/
theorem diff_bound_of_delta_zero (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (f : BlockAtom Bk J L → Bool) (hδ : ∀ b, f b = false → delLaw D L b = 0)
    (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) {K z : ℝ} (hK : 0 ≤ K) (hz : 0 ≤ z) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N L b)) G -
        multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N₀ L b)) G| ≤ (D.GB.Rerr + z) * K + 0 := by
  have heq : (fun b => if f b then Qb b else D.GB.N L b) =
      fun b => if f b then Qb b else D.GB.N₀ L b := by
    funext b
    cases hf : f b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [N_eq, N₀_eq, hδ b hf, add_zero]
    · rfl
  rw [heq, sub_self, abs_zero, add_zero]
  exact mul_nonneg (add_nonneg (Rerr_nonneg D) hz) hK

/-- **B5's `envC` from one averaged inequality** (the remainders are signed): with
`r_f = |E_f| − (B + z) Π Y ∏_f u`, the bundle holds as soon as the average of `∑_f r_f` over the
depth vectors and indices is at most `c L^{-σ} α`. Conversely every bundle gives that
inequality (`EnvelopeEnergyInputsCRT.excess_le`). -/
noncomputable def ofExcessEnv (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) (c : ℝ) (hc : 0 ≤ c)
    (hL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f : BlockAtom Bk J L → Bool,
            (|multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
                fun b => if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
              (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
                (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| -
              (D.B + z L) * conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
                D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1))))
        ≤ remainder c L A))
    (hR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f : BlockAtom Bk J L → Bool,
            (|multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
                fun b => if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N L b))
              (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
                (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| -
              (D.B + z L) * conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
                D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1))))
        ≤ remainder c L A)) :
    EnvelopeEnergyInputsCRT hcop D hpair where
  z := z
  hz0 := hz0
  hzt := hzt
  c := c
  hc := hc
  rL := fun L A Jq ω f =>
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
        fun b => if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
      (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
        (revealedInputCRT blk hcop D L A Jq)
        (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| -
      (D.B + z L) * conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
        D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)
  rR := fun L A Jq ω f =>
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
        fun b => if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N L b))
      (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
        (revealedInputCRT blk hcop D L A Jq)
        (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| -
      (D.B + z L) * conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
        D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)
  htermL := Eventually.of_forall fun _ _ _ _ _ _ _ _ _ _ => by linarith
  htermR := Eventually.of_forall fun _ _ _ _ _ _ _ _ _ _ => by linarith
  hremL := hL
  hremR := hR

/-- **Conversely**, every `envC` bundle gives the averaged inequality of `ofExcessEnv` (source
side; the target side is the same). -/
theorem EnvelopeEnergyInputsCRT.excess_le {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)}
    (I : EnvelopeEnergyInputsCRT hcop D hpair) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f : BlockAtom Bk J L → Bool,
            (|multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
                fun b => if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
              (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
                (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| -
              (D.B + I.z L) * conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
                D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1))))
        ≤ remainder I.c L A) := by
  filter_upwards [I.htermL, I.hremL] with L ht hr
  intro C hC hk A hA hY
  refine le_trans ?_ (hr C hC hk A hA hY)
  apply FiniteLaw.expect_mono
  intro Jq
  apply FiniteLaw.expect_mono
  intro ω
  apply sum_le_sum
  intro f _
  have := ht C hC hk A hA hY Jq ω f
  linarith

end Sarkozy.BracketEnergy
