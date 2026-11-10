module

public import Sarkozy.BlockRows.MiddleLaw

@[expose] public section

/-!
# Block rows, III″: the piece certificate of the middle rows

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(i) (row constants `f_j`, `h_j`
at the piece start, "Evaluation at the piece start").

* `pieceLen i = 570/log X`, `MiddleRowCert i` (**the piece certificate**, kind C + F): constants
  `ρ_{F,j}, ρ_{E,j}` with the gates `R_j(X)^n ρ_{F,j} + (2υ_j + υ_j²) X^{1/2} ≤ f_j`,
  `ρ_{E,j} ≤ h_j`, and `RowPrimeCert` at every class-three prime of the piece with the paper's
  ratios `R_j(p)`;
* **`middleBlockRows_of_cert`**: BA's `MiddleBlockRows i` from `MiddleRowCert i`, with the
  equality of the middle laws supplied by `primeMid_two`, `primeMid_one`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockRows

open Sarkozy Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.BlockSpecPaper
  Sarkozy.BlockInputs

/-! ## The piece certificate -/

/-- `n = L/log X`, the largest number of primes of a block of piece `i` (`L = 570`,
`lem:record:local-domain`(ii)). -/
noncomputable def pieceLen (i : Fin 33) : ℝ := (middleBudget : ℝ) / Real.log (pieceStart i)

/-- **The per-prime row certificate of the middle piece `i`** (`lem:front12:reference`(i) with
the row constants of the ALLp record). Constants `ρ_{F,j}, ρ_{E,j} ≥ 0` (`j = 2, 1`; the paper's
`ρ_{F,j}(X)/X^{-1/2}`, `ρ_{E,j}(X)/X^{-1/2}`) with the gates
`R_j(X)^n ρ_{F,j} + (2υ_j + υ_j²) X^{1/2} ≤ f_j`
and `ρ_{E,j} ≤ h_j` at the piece start `X` (`n = 570/log X`), and the per-prime rows
`RowPrimeCert` with the ratios `R₂(p)`, `R₁(p)` at every class-three prime of the piece (the
middle laws of `F` and `E` agree at every prime: proved, `primeMid_two`, `primeMid_one`).
*Hypothesis* (kind C + F: per-prime analytic statements with per-piece constants). -/
def MiddleRowCert (i : Fin 33) : Prop :=
  ∃ ρF₂ ρE₂ ρF₁ ρE₁ : ℝ, 0 ≤ ρF₂ ∧ 0 ≤ ρE₂ ∧ 0 ≤ ρF₁ ∧ 0 ≤ ρE₁ ∧
    RowGate (pieceStart i) (pieceLen i) (rowR₂ (pieceStart i)) ρF₂ ρE₂ (allpInputs i).f₂
      (allpInputs i).h₂ ∧
    RowGate (pieceStart i) (pieceLen i) (rowR₁ (pieceStart i)) ρF₁ ρE₁ (allpInputs i).f₁
      (allpInputs i).h₁ ∧
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
      (∀ hE hF, RowPrimeCert (Fin 2) p hE hF ρF₂ ρE₂ (rowR₂ p)) ∧
      (∀ hE hF, RowPrimeCert (Fin 1) p hE hF ρF₁ ρE₁ (rowR₁ p))

/-- **BA's middle rows from the per-prime row certificate** (`lem:front12:reference`(i)). -/
theorem middleBlockRows_of_cert {i : Fin 33} (hC : MiddleRowCert i) : MiddleBlockRows i := by
  obtain ⟨ρF₂, ρE₂, ρF₁, ρE₁, h0F₂, h0E₂, h0F₁, h0E₁, hg₂, hg₁, hp⟩ := hC
  intro ι _ _ pr _ b _ h3 hpc hbud hb hb' hne
  have hXQ : (Q3 : ℝ) ≤ (pieceStart i : ℝ) := by exact_mod_cast pieceStart_ge_Q3 i
  have hX19 : (19 : ℝ) ≤ (pieceStart i : ℝ) := le_trans (by norm_num [Q3]) hXQ
  have hX0 : (0 : ℝ) < (pieceStart i : ℝ) := by linarith
  have hXp : ∀ j, (pieceStart i : ℝ) ≤ (pr j : ℝ) := fun j => by exact_mod_cast (hpc j).1
  have hXb : (pieceStart i : ℝ) ≤ b := by
    obtain ⟨j, hj⟩ := hb'
    rw [← hj]
    exact hXp j
  have hlog := log_pieceStart_pos i
  have hcard : (Fintype.card ι : ℝ) ≤ pieceLen i := by
    unfold pieceLen
    rw [le_div_iff₀ hlog]
    calc (Fintype.card ι : ℝ) * Real.log (pieceStart i) = ∑ _j : ι, Real.log (pieceStart i) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ ∑ j, Real.log (pr j) := sum_le_sum fun j _ => Real.log_le_log hX0 (hXp j)
      _ ≤ middleBudget := hbud
  have hcert := fun j => hp (pr j) (h3 j) (hpc j).1 (hpc j).2
  have hr : ((b : ℝ) ^ (-(1 / 2 : ℝ))) = (√(b : ℝ))⁻¹ := BlockAdapter.rpow_neg_half_eq b
  rw [hr]
  refine ⟨fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · exact layerRows pr hne.E2 hne.F2
      (fun j ξ => primeMid_two (pr j) (h3 j) (hne.E2 j) (hne.F2 j) ξ) hX0 (rowR₂_mono hX19) hg₂
      h0F₂ h0E₂ (fun j => (hcert j).1 (hne.E2 j) (hne.F2 j)) hXb hb hcard ξ hξ
  · exact layerRows pr hne.E1 hne.F1
      (fun j ξ => primeMid_one (pr j) (hne.E1 j) (hne.F1 j) ξ) hX0 (rowR₁_mono hX19) hg₁ h0F₁ h0E₁
      (fun j => (hcert j).2 (hne.E1 j) (hne.F1 j)) hXb hb hcard ξ hξ

end Sarkozy.BlockRows
