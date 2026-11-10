module

public import Sarkozy.OpsVariance.RestorationBridge
public import Sarkozy.Variance.MatchingBlocks

@[expose] public section

/-!
# (Res) for an aligned matching class: the reduction to (a), fold restoration and (E1)

`paper/sections/22_variance.tex`, `lem:record:paired-e-joint`(a), (b), `lem:record:restoration`,
`cor:var-classes`(ii).

An aligned matching class is a pair `R = {ω₀, ω₁}` of choices on a common support `X`, `ω_s`
selecting the matching record `E_s` at every block of `X`. Its (Res) input `hRes` of
`hres_of_restoration` / `hres_of_recordLaws` is `2 (l₀ − z₁) Y ≤ Y[E^X_0] + Y[E^X_1]`, with
`Y[E^X_s] = Y[⊗_X w(ω_s) ⊗ μ]` (`recFam` at `S = X`, `recFam_self`).

* **`hRes_aligned`**: (Res) for the pair from W1's `paired_e_joint_b_blocks`, with the energies
  at the comparison data: `YF j = Y[⊗_X Π_{F_j} ⊗ μ]` (laws `wF j`), `YA s = Y[⊗_X (Π_{E_s} +
  ε G_s) ⊗ μ]` (laws `wA s`). Its inputs are the polarization order in energy form `hord`
  (`lem:record:paired-e-joint`(a)), the fold restoration bounds `hF` (`lem:record:restoration`
  for `j = 1, 2`) and the merge bounds `hMg` ((E1)); the bound is at `l₀ − C ε − z ε C`.
* **`hres_aligned`**: `hres` for the pair, with the record-law inputs replaced by `RecordLawIs`
  (proved for `Π_{E_s}` at the paper's data in `MatchFront`) and (Res) by the inputs of
  `hRes_aligned`;
* **`hres_fold`**: `hres` for a fold class `{ω}`, with (Res) the restoration bound of the
  selected product (`lem:record:restoration`) and the record laws from `FoldFront`.
-/

open Finset

namespace Sarkozy.OpsVariance

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.Variance

/-- On `S = X`, the record family is the record laws on `X` and `O` outside. -/
theorem recFam_self {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {X : J → Type} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)] (c : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (w : ∀ j, (V → X j) → ℝ)
    (m : ∀ j, (c.Half → X j) → ℝ) :
    recFam c O Xs Xs w m = onBlocks Xs (fun j => signedIntegral (w j)) O := by
  funext j
  unfold recFam onBlocks
  by_cases hj : j ∈ Xs <;> simp [hj]

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

/-- The energy `Y[⊗_X w ⊗ μ]` of a product of laws on `X` with the background `μ` outside. -/
noncomputable def energyX (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (X : Finset (BlockAtom Bk J L))
    (w : ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ) : ℝ :=
  diagonalIntegral (tensorLaw (onBlocks X (fun b => signedIntegral (w b)) (D.R.law p L)))
    (blockLift m₀ blk p L A)

omit [DecidableEq P] in
/-- **(Res) for an aligned matching class** (`lem:record:paired-e-joint`(b) in the form `hRes`):
from the polarization order `hord` ((a)), the fold restorations `hF` (`lem:record:restoration`,
`j = 1, 2`) and the merge bounds `hMg` ((E1)), the pair `{ω₀, ω₁}` satisfies `hRes` at
`l₀ − C ε − z ε C`. -/
theorem hRes_aligned {L : ℕ} {A : Finset ℤ} (ω₀ ω₁ : Choice (D.CL.T L)) (h01 : ω₀ ≠ ω₁)
    (X : Finset (BlockAtom Bk J L))
    (w : Choice (D.CL.T L) → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (wF wA : Fin 2 → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    {CX C ε l₀ z₁ z : ℝ} (hY : 0 ≤ D.Y L A) (hCX : CX ≤ C) (hε : 0 ≤ ε) (hz : 0 ≤ z)
    (hord : energyX D L A X (wF 0) + energyX D L A X (wF 1) ≤
      energyX D L A X (wA 0) + energyX D L A X (wA 1))
    (hF : ∀ j, (l₀ - z₁) * D.Y L A ≤ energyX D L A X (wF j))
    (hMg0 : energyX D L A X (wA 0) - energyX D L A X (w ω₀) ≤ (1 + z) * ε * CX * D.Y L A)
    (hMg1 : energyX D L A X (wA 1) - energyX D L A X (w ω₁) ≤ (1 + z) * ε * CX * D.Y L A) :
    ((l₀ - C * ε - z * ε * C) - z₁) * D.Y L A * (({ω₀, ω₁} : Finset _).card : ℝ) ≤
      ∑ ω ∈ ({ω₀, ω₁} : Finset _),
        diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X (w ω) (envM D L ω)))
          (blockLift m₀ blk p L A) := by
  rw [card_pair h01, sum_pair h01, recFam_self, recFam_self]
  have hb := paired_e_joint_b_blocks hY hCX hε hz hord (hF 0) (hF 1) hMg0 hMg1
  change _ ≤ energyX D L A X (w ω₀) + energyX D L A X (w ω₁)
  push_cast
  linarith

omit [DecidableEq P] in
/-- **`hres` for an aligned matching class** (`cor:var-classes`(ii) through `lem:var-gain`(a)):
`hres_of_recordLaws` at `R = {ω₀, ω₁}` with (Res) from `hRes_aligned`. The inputs left are the
record laws `hrec` (proved for `Π_{E_s}` at the paper's data: `recordLawIs_ofFold`,
`matchRecord_CL`), the polarization order `hord`, the fold restorations `hF`, the merge bounds
`hMg`, (E1) `hE1` and the numbers. -/
theorem hres_aligned {L : ℕ} {A : Finset ℤ} (ω₀ ω₁ : Choice (D.CL.T L)) (h01 : ω₀ ≠ ω₁)
    (X : Finset (BlockAtom Bk J L)) (hX : ∀ ω ∈ ({ω₀, ω₁} : Finset _), Choice.support ω = X)
    {γ₀ : ℝ} (hγ : ∀ ω ∈ ({ω₀, ω₁} : Finset _), monomial (D.CL.πt L) ω = γ₀)
    (w : Choice (D.CL.T L) → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (κj : Choice (D.CL.T L) → BlockAtom Bk J L → ℝ)
    (hrec : ∀ ω ∈ ({ω₀, ω₁} : Finset _), ∀ b ∈ X, ∀ t e, ω b = some (t, e) →
      RecordLawIs (w ω b) (D.CL.D L b t) (κj ω b))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hκ : ∀ ω ∈ ({ω₀, ω₁} : Finset _), ∀ b ∈ X, κj ω b ≤ κ)
    (wF wA : Fin 2 → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    {C ε l₀ z₁ z₂ z zm : ℝ} (rμ : Choice (D.CL.T L) → ℝ)
    (hrμ : ∀ ω ∈ ({ω₀, ω₁} : Finset _), 0 ≤ rμ ω)
    (hY : 0 ≤ D.Y L A) (hCX : 1 ≤ ∏ b ∈ X, selectionFactor a p D.S.selPre L b)
    (hC : ∏ b ∈ X, selectionFactor a p D.S.selPre L b ≤ C) (hε : 0 ≤ ε) (hzm : 0 ≤ zm)
    (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hz : (z₁ + κ * z₂) / (1 - κ) ≤ z)
    (hord : energyX D L A X (wF 0) + energyX D L A X (wF 1) ≤
      energyX D L A X (wA 0) + energyX D L A X (wA 1))
    (hF : ∀ j, (l₀ - z₁) * D.Y L A ≤ energyX D L A X (wF j))
    (hMg0 : energyX D L A X (wA 0) - energyX D L A X (w ω₀) ≤
      (1 + zm) * ε * (∏ b ∈ X, selectionFactor a p D.S.selPre L b) * D.Y L A)
    (hMg1 : energyX D L A X (wA 1) - energyX D L A X (w ω₁) ≤
      (1 + zm) * ε * (∏ b ∈ X, selectionFactor a p D.S.selPre L b) * D.Y L A)
    (hE1 : ∀ ω ∈ ({ω₀, ω₁} : Finset _), diagonalIntegral (tensorLaw (diagFam reservedCut
        (D.R.law p L) X X (envM D L ω))) (blockLift m₀ blk p L A) ≤
      (1 + z₂) * (∏ b ∈ X, selectionFactor a p D.S.selPre L b) * D.Y L A + rμ ω) :
    (gainBar (l₀ - C * ε - zm * ε * C) C κ - z) *
        (∑ ω ∈ ({ω₀, ω₁} : Finset _), monomial (D.CL.π L) ω) * D.Y L A -
        γ₀ * (κ / (1 - κ)) * ∑ ω ∈ ({ω₀, ω₁} : Finset _), rμ ω ≤
      ∑ ω ∈ ({ω₀, ω₁} : Finset _), monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω) :=
  hres_of_recordLaws {ω₀, ω₁} (insert_nonempty _ _) X hX hγ w κj hrec hκ0 hκ1 hκ rμ hrμ hY hCX
    hC hz₁ hz₂ hz (hRes_aligned ω₀ ω₁ h01 X w wF wA hY hC hε hzm hord hF hMg0 hMg1) hE1

omit [DecidableEq P] in
/-- **`hres` for a fold class** (`cor:var-classes`(i) through `lem:var-gain`(a)):
`hres_of_recordLaws` at `R = {ω}`. The (Res) input is the restoration bound of the selected
product, `Y[⊗_X w(ω) ⊗ μ] ≥ (l₀ − z₁) Y` (`lem:record:restoration` for `Π_{F_j}`); the record
laws `hrec` are `foldRecord_CL` at the paper's data. -/
theorem hres_fold {L : ℕ} {A : Finset ℤ} (ω : Choice (D.CL.T L))
    (X : Finset (BlockAtom Bk J L)) (hX : Choice.support ω = X)
    (w : Choice (D.CL.T L) → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (κj : Choice (D.CL.T L) → BlockAtom Bk J L → ℝ)
    (hrec : ∀ b ∈ X, ∀ t e, ω b = some (t, e) → RecordLawIs (w ω b) (D.CL.D L b t) (κj ω b))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ b ∈ X, κj ω b ≤ κ)
    {C l₀ z₁ z₂ z : ℝ} (rμ : Choice (D.CL.T L) → ℝ) (hrμ : 0 ≤ rμ ω)
    (hY : 0 ≤ D.Y L A) (hCX : 1 ≤ ∏ b ∈ X, selectionFactor a p D.S.selPre L b)
    (hC : ∏ b ∈ X, selectionFactor a p D.S.selPre L b ≤ C) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂)
    (hz : (z₁ + κ * z₂) / (1 - κ) ≤ z)
    (hRes : (l₀ - z₁) * D.Y L A ≤ energyX D L A X (w ω))
    (hE1 : diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) X X (envM D L ω)))
        (blockLift m₀ blk p L A) ≤
      (1 + z₂) * (∏ b ∈ X, selectionFactor a p D.S.selPre L b) * D.Y L A + rμ ω) :
    (gainBar l₀ C κ - z) * monomial (D.CL.π L) ω * D.Y L A -
        monomial (D.CL.πt L) ω * (κ / (1 - κ)) * rμ ω ≤
      monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω) := by
  have h := hres_of_recordLaws {ω} (singleton_nonempty ω) X
    (fun ω' hω' => by rw [mem_singleton.mp hω']; exact hX)
    (γ₀ := monomial (D.CL.πt L) ω) (fun ω' hω' => by rw [mem_singleton.mp hω'])
    w κj (fun ω' hω' => by rw [mem_singleton.mp hω']; exact hrec) hκ0 hκ1
    (fun ω' hω' => by rw [mem_singleton.mp hω']; exact hκ) rμ
    (fun ω' hω' => by rw [mem_singleton.mp hω']; exact hrμ) hY hCX hC hz₁ hz₂ hz
    (by rw [card_singleton, sum_singleton, recFam_self]; push_cast; rw [mul_one]; exact hRes)
    (fun ω' hω' => by rw [mem_singleton.mp hω']; exact hE1)
  simpa only [sum_singleton] using h

end Sarkozy.OpsVariance
