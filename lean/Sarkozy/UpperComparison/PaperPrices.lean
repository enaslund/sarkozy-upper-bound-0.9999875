module

public import Sarkozy.UpperComparison.Ledger

@[expose] public section

/-!
# `prop:record:upper`(ii) and (iii) for the paper's record ledger

`paper/sections/26_upper_comparison.tex`, `prop:record:upper`(ii),(iii), with the coefficient
sequences of the paper's ledger (`Ledger.upperLedger` on V1's records).

* `paper_block_poly`: (i) in polynomial form: the block prices are at most
  `(∑_d c^s_d r^d) q^{2a}` and `(∑_d c^a_d r^d) q^{2a}`, with the coefficient sequences `coefS`,
  `coefA` of the ledger (`[r^d](Π^rep_s + Π^del)` and `[r^d]Π^rep_a`);
* `paper_block_price_const`: (iii), `s_𝔅 + a_𝔅 ≤ C_band b^{-3/2} q_𝔅^{2a}` with
  `C_band = ∑_{d=3}^{7} ([r^d]Π^rep_s + [r^d]Π^rep_a + [r^d]Π^del) X^{-(d-3)/2}`;
* `paper_upper_sym_totals`, `paper_upper_skew_totals`: (ii), the upper parts of `S` and `A` are
  at most `S_u(a)` and `A_u(a)` when every band carries its own weights and coefficients and every
  block of the band has the record coefficients of (i).

The record coefficients' bounds (the brackets of `Symmetry`, `OldRecords`, `Prices`), the block
charges (`lem:record:block-charge`(i), repriced by `charge_reprice`) and the tail sums
(`lem:tail-prices`(iv)) are hypotheses.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.PartV

section Block

variable (W : UpperWeights) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i)

/-- **`prop:record:upper`(i) in polynomial form** for the paper's ledger: the block prices are at
most the ledger polynomials `∑_d c_d r^d` times `q_𝔅^{2a}`. -/
theorem paper_block_poly {r sel : ℝ} (hr : 0 ≤ r) (hsel : 0 ≤ sel) (πs πa : UpIdx → ℝ)
    (hπs : ∀ ρ, πs ρ ≤ (upperLedger W Cs Ca hCs hCa).symCoef r ρ / upPoly W r)
    (hπa : ∀ ρ, πa ρ ≤ (upperLedger W Cs Ca hCs hCa).skewCoef r ρ / upPoly W r) :
    (∑ ρ, πs ρ) * sel ≤ polyEval (upperLedger W Cs Ca hCs hCa).coefS r * sel ∧
      (∑ ρ, πa ρ) * sel ≤ polyEval (upperLedger W Cs Ca hCs hCa).coefA r * sel := by
  have h := block_prices_le (upperLedger W Cs Ca hCs hCa) hr (one_le_upPoly W hr) hsel πs πa
    hπs hπa
  have hdeg := upperLedger_degreesInRange W Cs Ca hCs hCa
  rw [(upperLedger W Cs Ca hCs hCa).piRepS_add_piDel_eq hdeg r] at h
  rw [(upperLedger W Cs Ca hCs hCa).piRepA_eq_poly hdeg r] at h
  exact h

/-- **`prop:record:upper`(iii) for the paper's ledger**: with `r = b^{-1/2} ≤ r_X = X^{-1/2}`,
`s_𝔅 + a_𝔅 ≤ C_band r³ q_𝔅^{2a}`, `C_band = ∑_{d=3}^{7} (c^s_d + c^a_d) r_X^{d-3}`. -/
theorem paper_block_price_const {r rX sel : ℝ} (hr : 0 ≤ r) (hrX : r ≤ rX) (hsel : 0 ≤ sel)
    (πs πa : UpIdx → ℝ)
    (hπs : ∀ ρ, πs ρ ≤ (upperLedger W Cs Ca hCs hCa).symCoef r ρ / upPoly W r)
    (hπa : ∀ ρ, πa ρ ≤ (upperLedger W Cs Ca hCs hCa).skewCoef r ρ / upPoly W r) :
    (∑ ρ, πs ρ) * sel + (∑ ρ, πa ρ) * sel ≤
      (∑ d ∈ upperDegrees, ((upperLedger W Cs Ca hCs hCa).coefS d +
        (upperLedger W Cs Ca hCs hCa).coefA d) * rX ^ (d - 3)) * r ^ 3 * sel := by
  obtain ⟨hs, ha⟩ := paper_block_poly W Cs Ca hCs hCa hr hsel πs πa hπs hπa
  exact block_price_const _ _ (fun d _ => (upperLedger W Cs Ca hCs hCa).coefS_nonneg d)
    (fun d _ => (upperLedger W Cs Ca hCs hCa).coefA_nonneg d) hr hrX hsel hs ha

end Block

/-- **`prop:record:upper`(ii) for the paper's ledger, symmetric totals.** Each band `β` has its
weights `W β` and coefficients `C^s_β, C^a_β`, and charges `𝒰_{β,d}` bounding
`∑_𝔅 q_𝔅^{2a} r_𝔅^d` over its blocks; every block has record prices `π^s_{𝔅,ρ}` bounded as in (i)
at `r_𝔅`, with the factor `q_𝔅^{2a}`. With the tail bound `∑_{p ≥ P₄} s_p ≤ S_tail(a)`, the upper
part of `S` is at most `S_u(a) = ∑_β ∑_d c^s_{β,d} 𝒰_{β,d} + S_tail(a)`. -/
theorem paper_upper_sym_totals {Bd Blk P : Type*} (bands : Finset Bd) (blocks : Bd → Finset Blk)
    (tail : Finset P) (W : Bd → UpperWeights) (Cs Ca : Bd → UpIdx → ℝ)
    (hCs : ∀ β i, 0 ≤ Cs β i) (hCa : ∀ β i, 0 ≤ Ca β i) (band : Blk → Bd) (rB sel : Blk → ℝ)
    (πs : Blk → UpIdx → ℝ) (sp : P → ℝ) (U : Bd → ℕ → ℝ) (Stail : ℝ)
    (hband : ∀ β ∈ bands, ∀ B ∈ blocks β, band B = β)
    (hr : ∀ B, 0 ≤ rB B) (hsel : ∀ B, 0 ≤ sel B)
    (hU : ∀ β ∈ bands, ∀ d ∈ upperDegrees, ∑ B ∈ blocks β, sel B * rB B ^ d ≤ U β d)
    (hπs : ∀ B ρ, πs B ρ ≤ (upperLedger (W (band B)) (Cs (band B)) (Ca (band B)) (hCs _)
      (hCa _)).symCoef (rB B) ρ / upPoly (W (band B)) (rB B))
    (htail : ∑ p ∈ tail, sp p ≤ Stail) :
    ∑ β ∈ bands, ∑ B ∈ blocks β, (∑ ρ, πs B ρ) * sel B + ∑ p ∈ tail, sp p ≤
      upperTotal bands (fun β => (upperLedger (W β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS) U
        Stail := by
  refine upper_totals_le bands blocks tail rB sel (fun B => (∑ ρ, πs B ρ) * sel B) sp
    (fun β => (upperLedger (W β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS) U Stail
    (fun β _ d _ => (upperLedger (W β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS_nonneg d) hU ?_ htail
  intro β hβ B hB
  have h := (paper_block_poly (W (band B)) (Cs (band B)) (Ca (band B)) (hCs _) (hCa _) (hr B)
    (hsel B) (πs B) (fun _ => 0) (hπs B) (fun ρ => by
      rw [div_nonneg_iff]
      left
      exact ⟨(upperLedger _ _ _ (hCs _) (hCa _)).skewCoef_nonneg (hr B) ρ,
        (zero_le_one.trans (one_le_upPoly _ (hr B)))⟩)).1
  rw [hband β hβ B hB] at h
  exact h

/-- **`prop:record:upper`(ii) for the paper's ledger, skew totals**: the upper part of `A` is at
most `A_u(a) = ∑_β ∑_d c^a_{β,d} 𝒰_{β,d} + A_tail(a)`. -/
theorem paper_upper_skew_totals {Bd Blk P : Type*} (bands : Finset Bd) (blocks : Bd → Finset Blk)
    (tail : Finset P) (W : Bd → UpperWeights) (Cs Ca : Bd → UpIdx → ℝ)
    (hCs : ∀ β i, 0 ≤ Cs β i) (hCa : ∀ β i, 0 ≤ Ca β i) (band : Blk → Bd) (rB sel : Blk → ℝ)
    (πa : Blk → UpIdx → ℝ) (ap : P → ℝ) (U : Bd → ℕ → ℝ) (Atail : ℝ)
    (hband : ∀ β ∈ bands, ∀ B ∈ blocks β, band B = β)
    (hr : ∀ B, 0 ≤ rB B) (hsel : ∀ B, 0 ≤ sel B)
    (hU : ∀ β ∈ bands, ∀ d ∈ upperDegrees, ∑ B ∈ blocks β, sel B * rB B ^ d ≤ U β d)
    (hπa : ∀ B ρ, πa B ρ ≤ (upperLedger (W (band B)) (Cs (band B)) (Ca (band B)) (hCs _)
      (hCa _)).skewCoef (rB B) ρ / upPoly (W (band B)) (rB B))
    (htail : ∑ p ∈ tail, ap p ≤ Atail) :
    ∑ β ∈ bands, ∑ B ∈ blocks β, (∑ ρ, πa B ρ) * sel B + ∑ p ∈ tail, ap p ≤
      upperTotal bands (fun β => (upperLedger (W β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA) U
        Atail := by
  refine upper_totals_le bands blocks tail rB sel (fun B => (∑ ρ, πa B ρ) * sel B) ap
    (fun β => (upperLedger (W β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA) U Atail
    (fun β _ d _ => (upperLedger (W β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA_nonneg d) hU ?_ htail
  intro β hβ B hB
  have h := (paper_block_poly (W (band B)) (Cs (band B)) (Ca (band B)) (hCs _) (hCa _) (hr B)
    (hsel B) (fun _ => 0) (πa B) (fun ρ => by
      rw [div_nonneg_iff]
      left
      exact ⟨(upperLedger _ _ _ (hCs _) (hCa _)).symCoef_nonneg (hr B) ρ,
        (zero_le_one.trans (one_le_upPoly _ (hr B)))⟩) (hπa B)).2
  rw [hband β hβ B hB] at h
  exact h

end Sarkozy.UpperComparison
