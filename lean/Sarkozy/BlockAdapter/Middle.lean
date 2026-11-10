module

public import Sarkozy.BlockAdapter.Root
public import Sarkozy.BlockAdapter.GChecks
public import Sarkozy.BlockSpecPaper.Caps

@[expose] public section

/-!
# The middle root envelopes from per-prime cut caps (`lem:front12:reference`(ii))

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(ii), first two inequalities, at the
ALLp block caps (B1's `MiddleUniformCapLemma`, `MiddleIndividualCapLemma`, `Caps.lean`).

The ALLp records store the per-prime constants `(g, B)` (`clean_g`, `positive_B`, B1's
`AllpConsts.lean`) of the root cuts L20 and L10 on every piece. The paper's block caps come from
the per-prime bounds `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` of the cut operators at the primes `p ≥ X_i` of
the piece. This file states those per-prime bounds and derives B1's root fields from them:

* `RootCutCap Λ g B p`: the per-prime bounds of the cut operator of `ϑ₀` of `G_{L,Λ}` at the prime
  `p` (`recordData Λ`, `Root.lean`), for `Λ = Fin 2` (L20) and `Λ = Fin 1` (L10);
* `MiddleRootCaps Λ c i`: `RootCutCap` at the recorded constants `(allpG i c, allpB i c)` for every
  class-three prime of piece `i`. *Hypothesis* (the per-prime certificates; for L10
  `lem:layer12-caps`(b), for L20 the ALLp base cap of the uniform root, cf. `cert:l20-grid`);
* **`rootEnvelope₂_capVal`**, **`rootEnvelope₁_capVal`**: B1's root fields at the block-cap values
  `capVal i 0`, `capVal i 1`, for every block of the piece with `∑ log p ≤ 570`, from these
  certificates (block adapter `Root.lean` and W7's `cut_block_cap`; the side conditions
  `0 ≤ g`, `0 ≤ B` come from `allp_capCheck`, `g p^{-1/2} < 1` from `allpG_le_six`);
* `MiddleUniformRest i`, `MiddleIndividualRest i u`: B1's cap lemmas without the root fields that
  are now derived (rows and layer caps; for the individual root also its L20 envelope).
  *Hypotheses*; `middleUniformCapLemma_of_rest`, `middleIndividualCapLemma_of_rest`.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData

/-! ## The per-prime certificates -/

/-- **The per-prime cap of the root cut `ϑ₀` of `G_{L,Λ}`** at the prime `p`: the cut operator
`A_p = T_{K/Z}` on `L²(λ_p(G_F))` satisfies `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p`. -/
def RootCutCap (Λ : Type) [Fintype Λ] [DecidableEq Λ] (g B : ℝ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (hne : (injLabellings (ZMod p) (recordGraph Λ)).Nonempty)
    (v : EuclideanSpace ℝ ((recordData Λ).cut.Half → ZMod p)),
    -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (recordData Λ) hne v⟫_ℝ ∧
      ⟪v, Spectral.cutOp (recordData Λ) hne v⟫_ℝ ≤ (1 + B / p) * ‖v‖ ^ 2

/-- **The per-prime certificates of a root cut on piece `i`** at the recorded constants
`(g, B) = (allpG i c, allpB i c)`: `RootCutCap` at every class-three prime of the piece. Used with
`(Λ, c) = (Fin 2, 0)` (L20, the uniform root) and `(Fin 1, 1)` (L10). *Hypothesis* (per-prime
spectral certificate; `lem:front12:reference`(ii): `lem:layer12-caps`(b) for L10, the ALLp L20
cap of the uniform root, cf. `cert:l20-grid`). -/
def MiddleRootCaps (Λ : Type) [Fintype Λ] [DecidableEq Λ] (c : Fin 5) (i : Fin 33) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
    RootCutCap Λ (allpG i c) (allpB i c) p

/-! ## The side conditions -/

theorem rpow_neg_half_eq (b : ℕ) : (b : ℝ) ^ (-(1 / 2 : ℝ)) = (√(b : ℝ))⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]

theorem allpG_nonneg (i : Fin 33) (c : Fin 5) (hc : c ≠ 3) : (0 : ℝ) ≤ allpG i c := by
  exact_mod_cast (allp_capCheck i c hc).2.2.1

theorem allpB_nonneg (i : Fin 33) (c : Fin 5) (hc : c ≠ 3) : (0 : ℝ) ≤ allpB i c := by
  exact_mod_cast (allp_capCheck i c hc).2.2.2.1

theorem pieceStart_gt_36 (i : Fin 33) : (36 : ℝ) < pieceStart i := by
  have h := pieceStart_ge_Q3 i
  have h' : 36 < pieceStart i := by
    unfold Q3 at h
    omega
  exact_mod_cast h'

/-- `g p^{-1/2} < 1` at every prime of a piece (`g ≤ 6 < √p`). -/
theorem allpG_mul_lt_one (i : Fin 33) (c : Fin 5) {p : ℕ} (hp : pieceStart i ≤ p) :
    (allpG i c : ℝ) * (√(p : ℝ))⁻¹ < 1 := by
  have h6 : (allpG i c : ℝ) ≤ 6 := by exact_mod_cast allpG_le_six i c
  have hp' : (36 : ℝ) < p := lt_of_lt_of_le (pieceStart_gt_36 i) (by exact_mod_cast hp)
  have hs : (6 : ℝ) < √(p : ℝ) := by
    rw [show (6 : ℝ) = √36 by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hp'
  have hspos : 0 < √(p : ℝ) := by linarith
  rw [← div_eq_mul_inv, div_lt_one hspos]
  linarith

theorem middleBudget_real : ((middleBudget : ℕ) : ℝ) = 570 := by
  norm_num [middleBudget]

/-! ## The root fields at the block-cap values -/

section Fields

variable {i : Fin 33} {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime]
  (b : ℕ)

/-- **L20 at the block-cap value** (`lem:front12:reference`(ii), first inequality, uniform root):
for a block of class-three primes of piece `i` with `∑ log p ≤ 570` and least prime `b`,
`Π_L ⪰_{ϑ₀} -capVal(i, L20) b^{-1/2} Π_{F₀}`, from the per-prime certificates. -/
theorem rootEnvelope₂_capVal (h20 : MiddleRootCaps (Fin 2) 0 i) (h3 : ∀ j, pr j % 4 = 3)
    (hpc : ∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i)
    (hbud : ∑ j, Real.log (pr j) ≤ middleBudget) (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b)
    (hne : MiddleNonempty pr) :
    RootEnvelope (fieldDatum (middleBlock_datumHyp₂ pr hne)) (capVal i 0)
      ((b : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rw [rpow_neg_half_eq]
  obtain ⟨j₀, hj₀⟩ := hb'
  have hX : (1 : ℝ) < pieceStart i := lt_trans (by norm_num) (pieceStart_gt_36 i)
  have hXb : (pieceStart i : ℝ) ≤ b := by
    rw [← hj₀]
    exact_mod_cast (hpc j₀).1
  have hL : ∑ j, Real.log (pr j) ≤ 570 := middleBudget_real ▸ hbud
  unfold capVal
  exact rootEnvelope₂_of_cutCaps pr hne (allpG_nonneg i 0 (by decide))
    (allpB_nonneg i 0 (by decide)) hX hXb (fun j => by exact_mod_cast hb j) hL
    (fun j => allpG_mul_lt_one i 0 (hpc j).1)
    (fun j v => (h20 (pr j) (h3 j) (hpc j).1 (hpc j).2 (hne.L2 j) v).1)
    (fun j v => (h20 (pr j) (h3 j) (hpc j).1 (hpc j).2 (hne.L2 j) v).2)

/-- **L10 at the block-cap value** (`lem:front12:reference`(ii), second inequality). -/
theorem rootEnvelope₁_capVal (h10 : MiddleRootCaps (Fin 1) 1 i) (h3 : ∀ j, pr j % 4 = 3)
    (hpc : ∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i)
    (hbud : ∑ j, Real.log (pr j) ≤ middleBudget) (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b)
    (hne : MiddleNonempty pr) :
    RootEnvelope (fieldDatum (middleBlock_datumHyp₁ pr hne)) (capVal i 1)
      ((b : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rw [rpow_neg_half_eq]
  obtain ⟨j₀, hj₀⟩ := hb'
  have hX : (1 : ℝ) < pieceStart i := lt_trans (by norm_num) (pieceStart_gt_36 i)
  have hXb : (pieceStart i : ℝ) ≤ b := by
    rw [← hj₀]
    exact_mod_cast (hpc j₀).1
  have hL : ∑ j, Real.log (pr j) ≤ 570 := middleBudget_real ▸ hbud
  unfold capVal
  exact rootEnvelope₁_of_cutCaps pr hne (allpG_nonneg i 1 (by decide))
    (allpB_nonneg i 1 (by decide)) hX hXb (fun j => by exact_mod_cast hb j) hL
    (fun j => allpG_mul_lt_one i 1 (hpc j).1)
    (fun j v => (h10 (pr j) (h3 j) (hpc j).1 (hpc j).2 (hne.L1 j) v).1)
    (fun j v => (h10 (pr j) (h3 j) (hpc j).1 (hpc j).2 (hne.L1 j) v).2)

end Fields

/-! ## B1's cap lemmas from the per-prime root certificates -/

/-- **`lem:front12:reference`(i),(ii) on piece `i`, uniform root, without the root envelopes**: the
rows at `j = 2, 1` and the layer caps at the block-cap values `capK i`. *Hypothesis* (spectral). -/
def MiddleUniformRest (i : Fin 33) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RowBounds (fieldDatum (middleBlock_datumHyp₂ pr hne)) (allpInputs i).f₂ (allpInputs i).h₂
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).f₁ (allpInputs i).h₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      MiddleLayerCaps (middleBlockFieldLaws pr hne (uniformRoot pr hne)) (capK i)
        ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- **`lem:front12:reference`(i),(ii) on piece `i`, individual-square root `u`, without the L10
envelope**: the rows, the L20 envelope of the individual root (`def:positive-root`, a reweighted
law, not a graph law) and the layer caps. *Hypothesis* (spectral). -/
def MiddleIndividualRest (i : Fin 33) (u : ℚ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RowBounds (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) (allpInputs i).f₂
        (allpInputs i).h₂ ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).f₁ (allpInputs i).h₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) (capVal i 0)
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      MiddleLayerCaps (middleBlockFieldLaws pr hne (individualBlockRoot pr u hne.L2)) (capK i)
        ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- B1's `MiddleUniformCapLemma` from the rest and the per-prime root certificates L20, L10. -/
theorem middleUniformCapLemma_of_rest {i : Fin 33} (hR : MiddleUniformRest i)
    (h20 : MiddleRootCaps (Fin 2) 0 i) (h10 : MiddleRootCaps (Fin 1) 1 i) :
    MiddleUniformCapLemma i := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  obtain ⟨r2, r1, hk⟩ := hR ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨r2, r1, rootEnvelope₂_capVal pr b h20 h3 hpc hbud hb hb' hne,
    rootEnvelope₁_capVal pr b h10 h3 hpc hbud hb hb' hne, hk⟩

/-- B1's `MiddleIndividualCapLemma` from the rest and the per-prime root certificate L10. -/
theorem middleIndividualCapLemma_of_rest {i : Fin 33} {u : ℚ} (hR : MiddleIndividualRest i u)
    (h10 : MiddleRootCaps (Fin 1) 1 i) : MiddleIndividualCapLemma i u := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  obtain ⟨r2, r1, e2, hk⟩ := hR ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨r2, r1, e2, rootEnvelope₁_capVal pr b h10 h3 hpc hbud hb hb' hne, hk⟩

end Sarkozy.BlockAdapter
