module

public import Sarkozy.ClassBoundsPaper.Inputs
public import Sarkozy.ClassBoundsPaper.Savings

@[expose] public section

/-!
# `hΨ` for the paper's classes at `a_T` (`prop:closing-data`(d))

`paper/sections/28_closing.tex`, `prop:closing-data`(d) and `def:closing-quantities`(8)–(10).

For class inputs `CI : ClassInputs CL` whose degree classes are the paper's 49 degree vectors
(`paperN`), with `B' = targetLedger.B`, `PolynomialData CI` names the upper data of
`prop:closing-data`(d) at every scale:

* upper prices `π̂ ≥ π` and upper auxiliary prices `ŷ ≥ y`, with kind totals at least (full) and at
  most (raw-arm, leading, remainder) those of the closing (`paperAtot`, `paperAarm`, `paperAlead`,
  `paperArem`: `A_F`, `A_E/2`, `A_E/2` and the raw-arm, leading and remainder totals;
  `lem:record:record-expansion`(iii), the two matching records receiving equal shares) and the
  totals `Ŝ ≤ S`, `Â ≤ A` of the ledger (`prop:closing-data`(b));
* the completion polynomial `𝒟_sym` of the variance classes and the credits of `lem:class-credit`
  (the class costs `C_n ≤ paperC n` of `CI`), which together lower the polynomial by at least `D_var
  ≥ 0.010266762707` (`cor:variance:final`(iv), `hDvar`).

**`PolynomialData.hΨ`**: then, for any energy factor `B ≤ targetLedger.B` (the obligation `hB`), the
class sum of `hΨ` is at most `targetLedger.E` at every scale. The sixteen class savings enter
through the kernel-checked `paperSavings_ge`, and `D = 0.264439290659 + D_var` is
`targetLedger_D_eq`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.TheoremCBlock Sarkozy.TheoremC
  Sarkozy.Comparison Sarkozy.TargetLedger

/-- The saving is affine in the class cost: lowering `C_n` by `δ` raises it by `δ ∏ (A^arm_l)^{n_l}
/ n!` (the credits of `lem:class-credit` on the raw-arm monomials). -/
theorem savingOfTotals_cost {L : Type*} [Fintype L] (n : L → ℕ) (C C₀ B' : ℝ)
    (Atot Aarm Alead Arem : L → ℝ) :
    savingOfTotals n C B' Atot Aarm Alead Arem =
      savingOfTotals n C₀ B' Atot Aarm Alead Arem +
        (C₀ - C) * (∏ l, Aarm l ^ n l) / (degFact n : ℝ) := by
  unfold savingOfTotals
  ring

variable {a : ℝ} {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R} {CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS}

/-- **The upper data of the class polynomial at `a_T`** (`prop:closing-data`(d)). *Hypotheses*: the
per-scale upper prices with the closing's kind totals and the ledger's `S`, `A`
(`prop:closing-data`(b), `lem:record:record-expansion`(iii)), and the variance credit
(`cor:variance:final`(iv), `lem:class-credit`). -/
structure PolynomialData (CI : ClassInputs CL) where
  /-- `B'` is the ledger's `B` (`def:closing-quantities`(2)). -/
  hBp : CI.Bp = targetLedger.B
  /-- The replaced degree classes are the closing's (`cor:envelope-costs`, sixteen classes). -/
  hN : CI.N = paperN
  /-- The upper prices and the completion polynomial at every scale. -/
  U : ∀ L, CI.UpperData L
  /-- `Ŝ ≤ S` (`prop:closing-data`(b)). -/
  hS : ∀ L, ∑ b, symTotal (U L).πu b ≤ targetLedger.S
  /-- `Â ≤ A` (`prop:closing-data`(b)). -/
  hA : ∀ L, ∑ b, skewTotal (U L).πu b ≤ targetLedger.A
  /-- The kind totals (`def:closing-quantities`(3), (4); `lem:middle-comparison-prices`): the full
  totals of the upper prices are at least, and the raw-arm, leading and remainder totals of the
  upper auxiliary prices at most, the closing's (the saving is monotone, `savingOfTotals_mono`). -/
  hAtot : ∀ L l, paperAtot l ≤ kindTotal (CI.kind L) (priceVec (U L).πu) l
  hAarm : ∀ L l, kindTotal (CI.kind L) (U L).yarmu l ≤ paperAarm l
  hAlead : ∀ L l, kindTotal (CI.kind L) (U L).yleadu l ≤ paperAlead l
  hArem : ∀ L l, kindTotal (CI.kind L) (U L).yremu l ≤ paperArem l
  /-- **The variance credit** `D_var` (`cor:variance:final`(iv), `lem:class-credit`): `𝒟_sym` at the
  upper prices and the credits `(paperC n − C_n) ∏ (A^arm)^n / n!` on the raw-arm monomials lower
  the polynomial by at least `0.010266762707`. -/
  hDvar : ∀ L, (10266762707 / 1000000000000 : ℝ) ≤
    ∑ m ∈ (U L).supp, (U L).d m * mono (priceVec (U L).πu) m +
      ∑ n ∈ paperN, (paperC n - CI.C n) *
        (∏ l, kindTotal (CI.kind L) (U L).yarmu l ^ n l) / (degFact n : ℝ)

namespace PolynomialData

variable {CI : ClassInputs CL}

/-- **The complete polynomial at the upper prices is at most `𝓔`** (`prop:closing-data`(d),
conclusion: `Ψ(π̂, ŷ) ≤ B(e^S cosh A − 1) − (D − D_var) − D_var = 𝓔`). -/
theorem Psi_le_E (PD : PolynomialData CI) (L : ℕ) : (PD.U L).Psi ≤ targetLedger.E := by
  set U := PD.U L with hU
  have hπu : ∀ b t e, 0 ≤ U.πu b t e := fun b t e => (CI.π_nonneg L b t e).trans (U.le b t e)
  have hnn : ∀ (z : PriceVar (CL.T L) → ℝ), (∀ v, 0 ≤ z v) → ∀ l,
      0 ≤ kindTotal (CI.kind L) z l := fun z hz l => sum_nonneg fun v _ => hz v
  have harm0 := hnn U.yarmu fun v => (CI.yarm_nonneg L v).trans (U.arm_le v)
  have hlead0 := hnn U.yleadu fun v => (CI.ylead_nonneg L v).trans (U.lead_le v)
  have hrem0 := hnn U.yremu fun v => (CI.yrem_nonneg L v).trans (U.rem_le v)
  have hsav : ∑ n ∈ paperN, savingOfTotals n (paperC n) (bLed : ℝ) paperAtot paperAarm paperAlead
        paperArem +
      ∑ n ∈ paperN, (paperC n - CI.C n) *
        (∏ l, kindTotal (CI.kind L) U.yarmu l ^ n l) / (degFact n : ℝ) ≤
      ∑ n ∈ CI.N, replacementSaving (CI.kind L) n (CI.C n) CI.Bp (priceVec U.πu) U.yarmu
        U.yleadu U.yremu := by
    rw [PD.hN, ← sum_add_distrib]
    apply sum_le_sum
    intro n _
    rw [replacementSaving_eq_totals, PD.hBp, targetLedger_B_eq,
      savingOfTotals_cost n (CI.C n) (paperC n)]
    have hb0 : (0 : ℝ) ≤ (bLed : ℝ) := by
      have : (0 : ℚ) ≤ bLed := by norm_num [bLed]
      exact_mod_cast this
    have hm := savingOfTotals_mono n (paperC_nonneg n) hb0
      (fun l => (paperTotals_nonneg l).1) (PD.hAtot L) harm0 (PD.hAarm L) hlead0 (PD.hAlead L)
      hrem0 (PD.hArem L)
    linarith
  have hD := PD.hDvar L
  have h16 := paperSavings_ge
  have hX : targetLedger.D ≤ ∑ m ∈ U.supp, U.d m * mono (priceVec U.πu) m +
      ∑ n ∈ CI.N, replacementSaving (CI.kind L) n (CI.C n) CI.Bp (priceVec U.πu) U.yarmu
        U.yleadu U.yremu := by
    rw [targetLedger_D_eq]
    linarith
  have hS0 : 0 ≤ ∑ b, symTotal U.πu b := sum_nonneg fun b _ => sum_nonneg fun t _ => hπu b t _
  have hA0 : 0 ≤ ∑ b, skewTotal U.πu b := sum_skewTotal_nonneg hπu
  have h := completed_le_E targetLedger CI.Bp_nonneg (le_of_eq PD.hBp) hS0 (PD.hS L) hA0 (PD.hA L)
    hX
  unfold ClassInputs.UpperData.Psi
  linarith

/-- **`hΨ` at `a_T`** (`prop:closing-data`(d), `thm:comparison`): for the class bounds of the
construction (`ClassInputs.toClassBounds`) and any energy factor `B ≤ targetLedger.B` (the
obligation `hB`), the complete polynomial with class bounds is at most `targetLedger.E` at every
scale. -/
theorem hΨ (PD : PolynomialData CI) {B : ℝ} (hB : B ≤ targetLedger.B) (L : ℕ) :
    ∑ ω ∈ univ.filter (fun ω : Choice (CL.T L) => IsSelection ω),
      (if CI.toClassBounds.cls L ω = none then B * monomial (CL.π L) ω
        else CI.toClassBounds.phi L ω) ≤ targetLedger.E :=
  (CI.sum_le_upper (hB.trans (le_of_eq PD.hBp.symm)) (PD.U L)).trans (PD.Psi_le_E L)

end PolynomialData

end Sarkozy.ClassBoundsPaper
