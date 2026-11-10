module

public import Sarkozy.ComparisonLawPaper.Main
public import Sarkozy.UpperComparison.Prices

@[expose] public section

/-!
# `hSA` by ranges: square-clique atoms, upper bands, middle blocks, tail

`def:closing-quantities`, `def:cp4`(b). The explicit form `SAExplicit` of `hSA` (`S + A ≤ S^{ledger}
+ A^{ledger}` for the assembled comparison law) is split here along the paper's ranges:

* `SAExplicit_of_ranges`: from bounds `H` on the square-clique prices
  (`lem:frontier:iidenergy`(iii), `H_iid`), `U` on the upper blocks, `M` on the middle blocks,
  and `T` on the tail bounds
  `S_tail + A_tail` (`lem:tail-prices`(iv)), with `H + U + M + T ≤ S^{ledger} + A^{ledger}`;
* **`upper_blocks_le_of_bands`**: the upper part `U` from W8's `prop:record:upper`(ii)
  (`UpperComparison.band_sum_le`): if every upper block of the band `β` has
  `s_𝔅 ≤ (∑_d c^s_{β,d} r_𝔅^d) q_𝔅^{2a}` and `a_𝔅 ≤ (∑_d c^a_{β,d} r_𝔅^d) q_𝔅^{2a}` (part (i),
  W8's `block_prices_le`/`paper_block_poly`) and the band charges bound `∑_𝔅 q_𝔅^{2a} r_𝔅^d`
  (`lem:record:block-charge`(i)), then `∑_{𝔅 upper} (s_𝔅 + a_𝔅) ≤ ∑_β ∑_d (c^s_{β,d} 𝒰^s_{β,d} +
  c^a_{β,d} 𝒰^a_{β,d})`;
* **`SAExplicit_of_bands`**: the combination, with the middle blocks bounded blockwise
  (`lem:middle-comparison-prices`: `s_𝔅 + a_𝔅 ≤ ((S₂r² + … + S₅r⁵) + (A₂r² + A₃r³ + A₄r⁴)) q^{2a}`,
  W6's `middle_comparison_prices`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainTarget Sarkozy.FirstStagePaper
open Sarkozy.PartVLaws (PaperBlockSpec TailInputsCorr paperAtomMap PaperAtom PrefixCoord)
open Sarkozy.UpperComparison (upperDegrees polyEval band_sum_le)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- The block of a specification is an upper block (`def:construction`(b)). -/
def specUpper {b : B} : PaperBlockSpec blockOf b → Bool
  | .upper _ => true
  | _ => false

variable (blockOf) in
/-- The selection factor `q_𝔅^{2a_T}` of a class-three block. -/
noncomputable abbrev blockSel (b : B) : ℝ := paperSelAt (paperAtomMap blockOf) targetDecay (.inr b)

variable {hW : Target.Weil} {spec : ∀ b, PaperBlockSpec blockOf b} {hC : TailInputsCorr PartV.P4}
  {In : FirstStageInputs blockOf}

/-- **`hSA` by ranges**: bounds `H` (square-clique atoms), `U` (upper blocks), `M` (middle blocks)
and `T` (tail bounds) with `H + U + M + T ≤ S^{ledger} + A^{ledger}` give `SAExplicit`. -/
theorem SAExplicit_of_ranges (Ci : ComparisonInputs blockOf hW spec hC In) {H U M T : ℝ}
    (hq : ∑ q, Ci.cliquePrice q ≤ H)
    (hu : ∑ b ∈ univ.filter (fun b => specUpper (spec b) = true), Ci.blockPrice b ≤ U)
    (hm : ∑ b ∈ univ.filter (fun b => ¬ specUpper (spec b) = true), Ci.blockPrice b ≤ M)
    (ht : Ci.St + Ci.At ≤ T) (hsum : H + U + M + T ≤ targetLedger.S + targetLedger.A) :
    SAExplicit Ci := by
  unfold SAExplicit
  have hsplit := sum_filter_add_sum_filter_not univ (fun b => specUpper (spec b) = true)
    Ci.blockPrice
  linarith

/-- The upper blocks of the band `β`. -/
noncomputable def upperBand {Bd : Type} [DecidableEq Bd] (spec : ∀ b, PaperBlockSpec blockOf b)
    (bandOf : B → Bd) (β : Bd) : Finset B :=
  (univ.filter fun b => specUpper (spec b) = true).filter fun b => bandOf b = β

/-- **The upper blocks, by bands** (`prop:record:upper`(ii), W8's `band_sum_le`): with per-block
bounds of (i) by polynomials with the band's coefficients `c^s_β`, `c^a_β ≥ 0` at `r_𝔅` and band
charges `𝒰^s_{β,d}`, `𝒰^a_{β,d}` bounding `∑_𝔅 q_𝔅^{2a} r_𝔅^d` over the upper blocks of the band,
`∑_{𝔅 upper} (s_𝔅 + a_𝔅) ≤ ∑_β ∑_d (c^s_{β,d} 𝒰^s_{β,d} + c^a_{β,d} 𝒰^a_{β,d})`. -/
theorem upper_blocks_le_of_bands (Ci : ComparisonInputs blockOf hW spec hC In) {Bd : Type}
    [DecidableEq Bd] (bandOf : B → Bd) (bands : Finset Bd)
    (hband : ∀ b, specUpper (spec b) = true → bandOf b ∈ bands) (rB : B → ℝ)
    (cS cA US UA : Bd → ℕ → ℝ)
    (hcS : ∀ β ∈ bands, ∀ d ∈ upperDegrees, 0 ≤ cS β d)
    (hcA : ∀ β ∈ bands, ∀ d ∈ upperDegrees, 0 ≤ cA β d)
    (hUS : ∀ β ∈ bands, ∀ d ∈ upperDegrees,
      ∑ b ∈ upperBand spec bandOf β, blockSel blockOf b * rB b ^ d ≤ US β d)
    (hUA : ∀ β ∈ bands, ∀ d ∈ upperDegrees,
      ∑ b ∈ upperBand spec bandOf β, blockSel blockOf b * rB b ^ d ≤ UA β d)
    (hs : ∀ b, specUpper (spec b) = true →
      (Ci.blockAtom b).sprice (blockSel blockOf b) ≤
        polyEval (cS (bandOf b)) (rB b) * blockSel blockOf b)
    (ha : ∀ b, specUpper (spec b) = true →
      (Ci.blockAtom b).aprice (blockSel blockOf b) ≤
        polyEval (cA (bandOf b)) (rB b) * blockSel blockOf b) :
    ∑ b ∈ univ.filter (fun b => specUpper (spec b) = true), Ci.blockPrice b ≤
      ∑ β ∈ bands, ∑ d ∈ upperDegrees, (cS β d * US β d + cA β d * UA β d) := by
  have hmaps : ∀ b ∈ univ.filter (fun b => specUpper (spec b) = true), bandOf b ∈ bands :=
    fun b hb => hband b (mem_filter.mp hb).2
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun β hβ => ?_
  have hmem : ∀ b ∈ upperBand spec bandOf β, specUpper (spec b) = true ∧ bandOf b = β := by
    intro b hb
    unfold upperBand at hb
    rw [mem_filter, mem_filter] at hb
    exact ⟨hb.1.2, hb.2⟩
  have h1 := band_sum_le (upperBand spec bandOf β) rB (blockSel blockOf)
    (fun b => (Ci.blockAtom b).sprice (blockSel blockOf b)) (cS β) (US β) (hcS β hβ) (hUS β hβ)
    (fun b hb => by
      have := hs b (hmem b hb).1
      rwa [(hmem b hb).2] at this)
  have h2 := band_sum_le (upperBand spec bandOf β) rB (blockSel blockOf)
    (fun b => (Ci.blockAtom b).aprice (blockSel blockOf b)) (cA β) (UA β) (hcA β hβ) (hUA β hβ)
    (fun b hb => by
      have := ha b (hmem b hb).1
      rwa [(hmem b hb).2] at this)
  rw [sum_add_distrib]
  change ∑ b ∈ upperBand spec bandOf β, ((Ci.blockAtom b).sprice (blockSel blockOf b) +
    (Ci.blockAtom b).aprice (blockSel blockOf b)) ≤ _
  rw [sum_add_distrib]
  exact add_le_add h1 h2

/-- **`hSA` from the paper's range bounds** (`def:closing-quantities`;
`lem:frontier:iidenergy`(iii), `prop:record:upper`(ii), `lem:middle-comparison-prices`,
`lem:tail-prices`(iv)): the square-clique prices at most `H`; the upper blocks bounded by bands as
in `upper_blocks_le_of_bands`; every middle
block `𝔅` with `s_𝔅 + a_𝔅 ≤ M_𝔅`; and
`H + ∑_β ∑_d (c^s 𝒰^s + c^a 𝒰^a) + ∑_{𝔅 middle} M_𝔅 + S_tail + A_tail ≤ S^{ledger} + A^{ledger}`. -/
theorem SAExplicit_of_bands (Ci : ComparisonInputs blockOf hW spec hC In) {H : ℝ}
    (hq : ∑ q, Ci.cliquePrice q ≤ H) {Bd : Type} [DecidableEq Bd] (bandOf : B → Bd)
    (bands : Finset Bd) (hband : ∀ b, specUpper (spec b) = true → bandOf b ∈ bands) (rB : B → ℝ)
    (cS cA US UA : Bd → ℕ → ℝ)
    (hcS : ∀ β ∈ bands, ∀ d ∈ upperDegrees, 0 ≤ cS β d)
    (hcA : ∀ β ∈ bands, ∀ d ∈ upperDegrees, 0 ≤ cA β d)
    (hUS : ∀ β ∈ bands, ∀ d ∈ upperDegrees,
      ∑ b ∈ upperBand spec bandOf β, blockSel blockOf b * rB b ^ d ≤ US β d)
    (hUA : ∀ β ∈ bands, ∀ d ∈ upperDegrees,
      ∑ b ∈ upperBand spec bandOf β, blockSel blockOf b * rB b ^ d ≤ UA β d)
    (hs : ∀ b, specUpper (spec b) = true →
      (Ci.blockAtom b).sprice (blockSel blockOf b) ≤
        polyEval (cS (bandOf b)) (rB b) * blockSel blockOf b)
    (ha : ∀ b, specUpper (spec b) = true →
      (Ci.blockAtom b).aprice (blockSel blockOf b) ≤
        polyEval (cA (bandOf b)) (rB b) * blockSel blockOf b)
    (Mb : B → ℝ) (hm : ∀ b, ¬ specUpper (spec b) = true → Ci.blockPrice b ≤ Mb b)
    (hsum : H + ∑ β ∈ bands, ∑ d ∈ upperDegrees, (cS β d * US β d + cA β d * UA β d) +
      ∑ b ∈ univ.filter (fun b => ¬ specUpper (spec b) = true), Mb b + (Ci.St + Ci.At) ≤
        targetLedger.S + targetLedger.A) :
    SAExplicit Ci :=
  SAExplicit_of_ranges Ci hq
    (upper_blocks_le_of_bands Ci bandOf bands hband rB cS cA US UA hcS hcA hUS hUA hs ha)
    (sum_le_sum fun b hb => hm b (mem_filter.mp hb).2) le_rfl hsum

end Sarkozy.ComparisonLawPaper
