module

public import Sarkozy.DensityFibre.FoldedChoice

@[expose] public section

/-!
# The four sharp-first differences by the baseline folded route

K2's fields `Sh.fixM.hdiffL/R` (26–27) and `Sh.envM.hdiffL/R` (30–31), by the paper's
**baseline** proof of `lem:sharp-first`: `lem:record:folded-energy` at the cut of the tag, then
`prop:record:density-structured` on the folded energies. Valid at `ϑ = 1`, and used neither by
`lem:density:coupled` nor by the mixed-moment gates.

Per choice `σ` and tag `j` the hypothesis `hfold` asks for:
* bounds `𝔈_±(φ) ≤ (∏ g) M_± + r_±(φ)` on the folded energies of the pieces. These are
  `prop:record:density-structured` for the folded laws (positive measures) with the folded
  revealed inputs, as B9's `data_block_energy_le_structured` gives them;
* prices with `t M₊ + M₋/t ≤ 2 (1 + ε_L) Λ K`. Here `Λ = Λ(L, A, 𝒥, ω) ≥ 0` is the local density
  factor of the revealed inputs at the index (B9's finding 1: it can exceed 1 at a fixed `ω`, and
  its mean over `ω` is at most 1, `env_localDensity_mean_le`);
* a per-choice remainder `rch(σ)` that dominates the AM–GM remainder.

The conclusion is the field with `r₂ = ∑_{σ ≠ ∅} rch(σ) + (R_err + z) K (Λ − 1)`. The second term
is signed and averages to at most `0` over `ω` when `E_ω Λ ≤ 1`. That average is the job of the
summation fields `hm`, which share `r₂`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame Sarkozy.RecordExpansion
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
/-- **`diff_bound_of_coupled` with a local factor**: per-choice bounds
`|E_σ| ≤ (1 + ε) Λ K wt_j(σ) + r_σ` (`Λ ≥ 0`) give
`|E_Ñ − E_{Ñ₀}| ≤ (R_err + z) K + (∑_σ r_σ + (R_err + z) K (Λ − 1))` for `z ≥ R_err ε`. -/
theorem diff_bound_of_coupled_loc (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f : BlockAtom Bk J L → Bool)
    (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) {K z ε Λ : ℝ} (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hΛ : 0 ≤ Λ) (hz : D.GB.Rerr * ε ≤ z) (r : (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      |multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G| ≤
        ((1 + ε) * (Λ * K)) * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if f b then 0 else D.GB.uprice L b) j σ + r σ) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N L b)) G -
        multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N₀ L b)) G| ≤
      (D.GB.Rerr + z) * K +
        (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ +
          (D.GB.Rerr + z) * K * (Λ - 1)) := by
  have hb := diff_bound_of_coupled_eps D L h0 Qb f G (mul_nonneg hΛ hK) hε hz r hterm
  have e : (D.GB.Rerr + z) * (Λ * K) = (D.GB.Rerr + z) * K + (D.GB.Rerr + z) * K * (Λ - 1) := by
    ring
  linarith

omit [DecidableEq P] in
/-- The left matching-envelope increments are nonnegative. -/
theorem envIncL_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) : IsNonneg (TheoremCBlock.Structured.envIncL D L b) := by
  intro F hF
  unfold TheoremCBlock.Structured.envIncL
  rw [LinearMap.sum_apply]
  exact Finset.sum_nonneg fun i _ => by
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (D.ME.cL_nonneg L b i) ((D.ME.κL_pos L b i).1 F hF)

omit [DecidableEq P] in
/-- The right matching-envelope increments are nonnegative. -/
theorem envIncR_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) : IsNonneg (TheoremCBlock.Structured.envIncR D L b) := by
  intro F hF
  unfold TheoremCBlock.Structured.envIncR
  rw [LinearMap.sum_apply]
  exact Finset.sum_nonneg fun i _ => by
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (D.ME.cR_nonneg L b i) ((D.ME.κR_pos L b i).1 F hF)

omit [DecidableEq P] in
/-- The wrapping increments are nonnegative (probability components, nonnegative weights). -/
theorem wrapInc_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) : IsNonneg (TheoremCBlock.Structured.wrapInc D L b) := by
  intro F hF
  unfold TheoremCBlock.Structured.wrapInc
  rw [LinearMap.sum_apply]
  exact Finset.sum_nonneg fun t _ => by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    exact add_nonneg (mul_nonneg (D.CL.πt_nonneg L b t _) ((D.CL.D_prob L b t _).1 F hF))
      (mul_nonneg (D.CL.πt_nonneg L b t _) ((D.CL.D_prob L b t _).1 F hF))

/-- **K2's field `Sh.envM.hdiffL` by the baseline folded route** (`lem:sharp-first` with
`lem:record:folded-energy`; the folded-energy bounds are `prop:record:density-structured` for the
folded laws, used as hypothesis `hfold`; local factor `Λ`). -/
theorem envHdiffL_of_folded (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (Λ : ℕ → Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → ℝ)
    (hΛ : ∀ L A Jq ω, 0 ≤ Λ L A Jq ω)
    (dec : ∀ L, DecFamily D L)
    (rch : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        ∃ (t Mp Mm : ℝ) (rp rm : (∀ b, HPiece D L b) → ℝ), 0 < t ∧
          t * Mp + Mm / t ≤ 2 * ((1 + ε L) * (Λ L A Jq ω * (conductorPrice pr h
              (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)))) ∧
          (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
            foldedPlus (D.FS.cut j) (bpieceLp D L (TheoremCBlock.Structured.envIncL D L) (dec L) j)
              (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, bpieceG D L b (φ b)) * Mp + rp φ) ∧
          (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
            foldedMinus (D.FS.cut j) (bpieceLm D L (TheoremCBlock.Structured.envIncL D L) (dec L) j)
              (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, bpieceG D L b (φ b)) * Mm + rm φ) ∧
          (t * ∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rp φ +
            (∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rm φ) / t) / 2 ≤
            rch L A Jq ω f σ)) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
            (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
          multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N₀ L b))
            (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) +
            (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              rch L A Jq ω f σ +
              (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) * (Λ L A
                Jq ω - 1))) := by
  filter_upwards [hfold] with L hL
  intro C hC hind A hA hY Jq ω f
  have hK : 0 ≤ (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) :=
    mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceL_nonneg D L b
        · exact zero_le_one)
  refine diff_bound_of_coupled_loc D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.envIncL D L) f _ hK (hε L) (hΛ _ _ _ _) (hz L) _ ?_
  intro σ hσ0 j hj
  obtain ⟨t, Mp, Mm, rp, rm, ht, hM, hp, hm, hr⟩ := hL C hC hind A hA hY Jq ω f σ hσ0 j hj
  have hM0 : 0 ≤ (1 + ε L) * (Λ L A Jq ω * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent
      a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1))) :=
    mul_nonneg (by linarith [hε L]) (mul_nonneg (hΛ _ _ _ _) hK)
  have hb := choice_bound_of_folded blk (dec L) (TheoremCBlock.Structured.envIncL D L)
    (prefix_pairwise (hpair L)) (envIncL_nonneg D L) f σ j _ ht hM0 hM rp rm hp hm
  linarith

/-- **K2's field `Sh.envM.hdiffR` by the baseline folded route** (`lem:sharp-first` with
`lem:record:folded-energy`; the folded-energy bounds are `prop:record:density-structured` for the
folded laws, used as hypothesis `hfold`; local factor `Λ`). -/
theorem envHdiffR_of_folded (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (Λ : ℕ → Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → ℝ)
    (hΛ : ∀ L A Jq ω, 0 ≤ Λ L A Jq ω)
    (dec : ∀ L, DecFamily D L)
    (rch : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        ∃ (t Mp Mm : ℝ) (rp rm : (∀ b, HPiece D L b) → ℝ), 0 < t ∧
          t * Mp + Mm / t ≤ 2 * ((1 + ε L) * (Λ L A Jq ω * (conductorPrice pr h
              (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)))) ∧
          (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
            foldedPlus (D.FS.cut j) (bpieceLp D L (TheoremCBlock.Structured.envIncR D L) (dec L) j)
              (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, bpieceG D L b (φ b)) * Mp + rp φ) ∧
          (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
            foldedMinus (D.FS.cut j) (bpieceLm D L (TheoremCBlock.Structured.envIncR D L) (dec L) j)
              (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, bpieceG D L b (φ b)) * Mm + rm φ) ∧
          (t * ∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rp φ +
            (∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rm φ) / t) / 2 ≤
            rch L A Jq ω f σ)) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N L b))
            (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
          multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N₀ L b))
            (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) +
            (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              rch L A Jq ω f σ +
              (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) * (Λ L A
                Jq ω - 1))) := by
  filter_upwards [hfold] with L hL
  intro C hC hind A hA hY Jq ω f
  have hK : 0 ≤ (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) :=
    mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceR_nonneg D L b
        · exact zero_le_one)
  refine diff_bound_of_coupled_loc D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.envIncR D L) f _ hK (hε L) (hΛ _ _ _ _) (hz L) _ ?_
  intro σ hσ0 j hj
  obtain ⟨t, Mp, Mm, rp, rm, ht, hM, hp, hm, hr⟩ := hL C hC hind A hA hY Jq ω f σ hσ0 j hj
  have hM0 : 0 ≤ (1 + ε L) * (Λ L A Jq ω * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent
      a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1))) :=
    mul_nonneg (by linarith [hε L]) (mul_nonneg (hΛ _ _ _ _) hK)
  have hb := choice_bound_of_folded blk (dec L) (TheoremCBlock.Structured.envIncR D L)
    (prefix_pairwise (hpair L)) (envIncR_nonneg D L) f σ j _ ht hM0 hM rp rm hp hm
  linarith

/-- **K2's field `Sh.fixM.hdiffL` by the baseline folded route** (`lem:sharp-first` with
`lem:record:folded-energy`; the folded-energy bounds are `prop:record:density-structured` for the
folded laws, used as hypothesis `hfold`; local factor `Λ`). -/
theorem fixHdiffL_of_folded (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (Λ : ℕ → Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → ℝ)
    (hΛ : ∀ L A S Jq ω, 0 ≤ Λ L A S Jq ω)
    (dec : ∀ L, DecFamily D L)
    (rch : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ S : Finset E, S ≠ ∅ → ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option
          (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        ∃ (t Mp Mm : ℝ) (rp rm : (∀ b, HPiece D L b) → ℝ), 0 < t ∧
          t * Mp + Mm / t ≤ 2 * ((1 + ε L) * (Λ L A S Jq ω * (fixedPrice pr h
              (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)))) ∧
          (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
            foldedPlus (D.FS.cut j) (bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
              (fun v x => pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S
                  0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, bpieceG D L b (φ b)) * Mp + rp φ) ∧
          (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
            foldedMinus (D.FS.cut j) (bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
              (fun v x => pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S
                  0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, bpieceG D L b (φ b)) * Mm + rm φ) ∧
          (t * ∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rp φ +
            (∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rm φ) / t) / 2 ≤
            rch L A S Jq ω f σ)) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
        multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
          D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
          (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            rch L A S Jq ω f σ +
              (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) * (Λ L A
                S Jq ω - 1))) := by
  filter_upwards [hfold] with L hL
  intro C hC hind A hA hY S hS Jq ω f
  have hK : 0 ≤ (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) :=
    mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one)
  refine diff_bound_of_coupled_loc D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.wrapInc D L) f _ hK (hε L) (hΛ _ _ _ _ _) (hz L) _ ?_
  intro σ hσ0 j hj
  obtain ⟨t, Mp, Mm, rp, rm, ht, hM, hp, hm, hr⟩ := hL C hC hind A hA hY S hS Jq ω f σ hσ0 j hj
  have hM0 : 0 ≤ (1 + ε L) * (Λ L A S Jq ω * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent
      a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))) :=
    mul_nonneg (by linarith [hε L]) (mul_nonneg (hΛ _ _ _ _ _) hK)
  have hb := choice_bound_of_folded blk (dec L) (TheoremCBlock.Structured.wrapInc D L)
    (prefix_pairwise (hpair L)) (wrapInc_nonneg D L) f σ j _ ht hM0 hM rp rm hp hm
  linarith

/-- **K2's field `Sh.fixM.hdiffR` by the baseline folded route** (`lem:sharp-first` with
`lem:record:folded-energy`; the folded-energy bounds are `prop:record:density-structured` for the
folded laws, used as hypothesis `hfold`; local factor `Λ`). -/
theorem fixHdiffR_of_folded (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (Λ : ℕ → Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → ℝ)
    (hΛ : ∀ L A S Jq ω, 0 ≤ Λ L A S Jq ω)
    (dec : ∀ L, DecFamily D L)
    (rch : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ S : Finset E, S ≠ ∅ → ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option
          (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        ∃ (t Mp Mm : ℝ) (rp rm : (∀ b, HPiece D L b) → ℝ), 0 < t ∧
          t * Mp + Mm / t ≤ 2 * ((1 + ε L) * (Λ L A S Jq ω * (fixedPrice pr h
              (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)))) ∧
          (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
            foldedPlus (D.FS.cut j) (bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
              (fun v x => pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S
                  1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, bpieceG D L b (φ b)) * Mp + rp φ) ∧
          (∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
            foldedMinus (D.FS.cut j) (bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
              (fun v x => pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S
                  1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, bpieceG D L b (φ b)) * Mm + rm φ) ∧
          (t * ∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rp φ +
            (∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ * rm φ) / t) / 2 ≤
            rch L A S Jq ω f σ)) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
        multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
          D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
          (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            rch L A S Jq ω f σ +
              (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) * (Λ L A
                S Jq ω - 1))) := by
  filter_upwards [hfold] with L hL
  intro C hC hind A hA hY S hS Jq ω f
  have hK : 0 ≤ (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) :=
    mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one)
  refine diff_bound_of_coupled_loc D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.wrapInc D L) f _ hK (hε L) (hΛ _ _ _ _ _) (hz L) _ ?_
  intro σ hσ0 j hj
  obtain ⟨t, Mp, Mm, rp, rm, ht, hM, hp, hm, hr⟩ := hL C hC hind A hA hY S hS Jq ω f σ hσ0 j hj
  have hM0 : 0 ≤ (1 + ε L) * (Λ L A S Jq ω * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent
      a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))) :=
    mul_nonneg (by linarith [hε L]) (mul_nonneg (hΛ _ _ _ _ _) hK)
  have hb := choice_bound_of_folded blk (dec L) (TheoremCBlock.Structured.wrapInc D L)
    (prefix_pairwise (hpair L)) (wrapInc_nonneg D L) f σ j _ ht hM0 hM rp rm hp hm
  linarith

/-! ## The average of the local-factor correction -/

/-- **The local-factor correction of `r₂` averages to at most `0`**: if `E_ω Λ ≤ 1` and the
prices `K_f` do not depend on `ω`, then
`E_ω ∑_f (rch(ω, f) + c K_f (Λ(ω) − 1)) ≤ E_ω ∑_f rch(ω, f)` for `c ≥ 0`. With `c = R_err + z_L`
this is how the remainder `r₂` of `*_of_folded` enters the summation fields `hm` (B9's
`EnvMeanBound`, `FixMeanBound`; DC1's hypothesis `hr2`): only `∑_σ rch` remains. -/
theorem expect_r2_le {Ω F : Type*} [Fintype Ω] [Fintype F] (μ : FiniteLaw Ω) (rch : Ω → F → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (K : F → ℝ) (hK : ∀ f, 0 ≤ K f) (Λ : Ω → ℝ) (hΛ : μ.expect Λ ≤ 1) :
    μ.expect (fun ω => ∑ f, (rch ω f + c * K f * (Λ ω - 1))) ≤
      μ.expect (fun ω => ∑ f, rch ω f) := by
  have e : ∀ ω, ∑ f, (rch ω f + c * K f * (Λ ω - 1)) =
      ∑ f, rch ω f + (c * ∑ f, K f) * (Λ ω - 1) := fun ω => by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [μ.expect_congr e, μ.expect_add, μ.expect_const_mul, μ.expect_sub, μ.expect_const]
  have hC : 0 ≤ c * ∑ f, K f := mul_nonneg hc (Finset.sum_nonneg fun f _ => hK f)
  have : (c * ∑ f, K f) * (μ.expect Λ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hC (by linarith)
  linarith

end Sarkozy.DensityFibre
