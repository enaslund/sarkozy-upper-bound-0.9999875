module

public import Sarkozy.OpsVariance.Restoration
public import Sarkozy.OpsVariance.MatchFront

@[expose] public section

/-!
# `hres` from record laws: only (Res) and (E1) remain

`paper/sections/22_variance.tex`, `lem:var-gain`(b), `lem:record:restoration`,
`lem:record:paired-e-joint`(b).

`hres_of_restoration` takes the record laws `w` of a set `R` of choices on a common support `X`
through five pointwise inputs (`hw`, `hp`, `hn`, `ht`, `hcen`). **`hres_of_recordLaws`** replaces
them by the single input that `w ω b` is a record law (`RecordLawIs`) for the record selected by `ω`
at `b`; `recordLawIs_ofFold` and `matchRecord_CL` (MatchFront) supply it for the matching records
`E_s` of the middle blocks, with `κ_E = 3/(b − 3)`. What is left is the restoration
inequality `hRes` (C, `lem:record:restoration` / `lem:record:paired-e-joint`(b)) for those laws,
the (E1) bound `hE1` of the diagonal products, and the arithmetic `hY`, `hCX`, `hC`, `hz`.
-/

open Finset

namespace Sarkozy.OpsVariance

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.Variance

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

omit [DecidableEq P] in
/-- The selected record of a choice at a block of its support. -/
theorem exists_of_mem_support {L : ℕ} (ω : Choice (D.CL.T L)) {b : BlockAtom Bk J L}
    (hb : b ∈ Choice.support ω) : ∃ t e, ω b = some (t, e) := by
  unfold Choice.support at hb
  obtain ⟨⟨t, e⟩, h⟩ := Option.isSome_iff_exists.mp (mem_filter.mp hb).2
  exact ⟨t, e, h⟩

omit [DecidableEq P] in
/-- **A record law of the selected record gives the five pointwise inputs** of
`hres_of_restoration` at one block of the support. -/
theorem recordLaw_inputs {L : ℕ} (ω : Choice (D.CL.T L)) {b : BlockAtom Bk J L} {t : D.CL.T L b}
    {e : ChangeType} (hωb : ω b = some (t, e)) {w : (Slot → BlockLabel m₀ blk p L b) → ℝ} {κ : ℝ}
    (hw : RecordLawIs w (D.CL.D L b t) κ) :
    (∀ z, 0 ≤ w z) ∧ plusMarginal reservedCut w = envM D L ω b ∧
      minusMarginal reservedCut w = envM D L ω b ∧
      (∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ,
        reservedCut.form (signedIntegral w) G H = reservedCut.form (signedIntegral w) H G) ∧
      CentredNormLe reservedCut (signedIntegral w) (envM D L ω b) κ := by
  obtain ⟨h0, hp, hn, ht, hc⟩ := hw
  have henv : envM D L ω b = plusMarginal reservedCut w := by
    unfold envM
    rw [hωb]
    exact (hp e).symm
  rw [henv]
  exact ⟨h0, rfl, hn, ht, hc⟩

omit [DecidableEq P] in
/-- **`hres` from record laws** (`lem:var-gain`(b)): `hres_of_restoration` with the record-law
inputs `hw`, `hp`, `hn`, `ht`, `hcen` replaced by `hrec` (each `w ω b` is a record law of the record
that `ω` selects at `b`). The remaining inputs are (Res) `hRes` and (E1) `hE1`. -/
theorem hres_of_recordLaws {L : ℕ} {A : Finset ℤ} (R : Finset (Choice (D.CL.T L)))
    (hR : R.Nonempty) (X : Finset (BlockAtom Bk J L)) (hX : ∀ ω ∈ R, Choice.support ω = X)
    {γ₀ : ℝ} (hγ : ∀ ω ∈ R, monomial (D.CL.πt L) ω = γ₀)
    (w : Choice (D.CL.T L) → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (κj : Choice (D.CL.T L) → BlockAtom Bk J L → ℝ)
    (hrec : ∀ ω ∈ R, ∀ b ∈ X, ∀ t e, ω b = some (t, e) →
      RecordLawIs (w ω b) (D.CL.D L b t) (κj ω b))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ ω ∈ R, ∀ b ∈ X, κj ω b ≤ κ)
    {C l₀ z₁ z₂ z : ℝ} (rμ : Choice (D.CL.T L) → ℝ) (hrμ : ∀ ω ∈ R, 0 ≤ rμ ω)
    (hY : 0 ≤ D.Y L A) (hCX : 1 ≤ ∏ b ∈ X, selectionFactor a p D.S.selPre L b)
    (hC : ∏ b ∈ X, selectionFactor a p D.S.selPre L b ≤ C) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂)
    (hz : (z₁ + κ * z₂) / (1 - κ) ≤ z)
    (hRes : (l₀ - z₁) * D.Y L A * R.card ≤ ∑ ω ∈ R,
      diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X (w ω) (envM D L ω)))
        (blockLift m₀ blk p L A))
    (hE1 : ∀ ω ∈ R, diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) X X
        (envM D L ω))) (blockLift m₀ blk p L A) ≤
      (1 + z₂) * (∏ b ∈ X, selectionFactor a p D.S.selPre L b) * D.Y L A + rμ ω) :
    (gainBar l₀ C κ - z) * (∑ ω ∈ R, monomial (D.CL.π L) ω) * D.Y L A -
        γ₀ * (κ / (1 - κ)) * ∑ ω ∈ R, rμ ω ≤
      ∑ ω ∈ R, monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω) := by
  have key : ∀ ω ∈ R, ∀ b ∈ X, (∀ z, 0 ≤ w ω b z) ∧
      plusMarginal reservedCut (w ω b) = envM D L ω b ∧
      minusMarginal reservedCut (w ω b) = envM D L ω b ∧
      (∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ,
        reservedCut.form (signedIntegral (w ω b)) G H =
          reservedCut.form (signedIntegral (w ω b)) H G) ∧
      CentredNormLe reservedCut (signedIntegral (w ω b)) (envM D L ω b) (κj ω b) :=
    fun ω hω b hb => by
    obtain ⟨t, e, hωb⟩ := exists_of_mem_support ω (b := b) (by rw [hX ω hω]; exact hb)
    exact recordLaw_inputs ω hωb (hrec ω hω b hb t e hωb)
  exact hres_of_restoration R hR X hX hγ w (fun ω hω b hb => (key ω hω b hb).1)
    (fun ω hω b hb => (key ω hω b hb).2.1) (fun ω hω b hb => (key ω hω b hb).2.2.1)
    (fun ω hω b hb => (key ω hω b hb).2.2.2.1) κj (fun ω hω b hb => (key ω hω b hb).2.2.2.2)
    hκ0 hκ1 hκ rμ hrμ hY hCX hC hz₁ hz₂ hz hRes hE1

end Sarkozy.OpsVariance
