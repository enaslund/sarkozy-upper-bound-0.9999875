module

public import Sarkozy.BlockAdapter.Layer
public import Sarkozy.BlockAdapter.Middle

@[expose] public section

/-!
# The middle layer caps from per-prime cut caps (`lem:front12:reference`(ii), third display)

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(ii), at the ALLp block caps
(B1's `capK`: `k_L ← L21`, `k_S = k_R = k_C ← E21` at `g e^{B·570/(X log X)}`, `k_D` recorded).

* `LayerCutCap O G₂ g B p`: the per-prime bounds `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` of the cut
  operator of the layer swap of `G₂` at `p` (`layerData`, `Layer.lean`);
* `MiddleL21Caps i`, `MiddleE21Caps i`: these at the recorded constants of piece `i` (cuts L21 of
  `G_{L,2}` and E21 of `G_{E,2}`) for every class-three prime of the piece. *Hypotheses*
  (per-prime certificates, `lem:layer12-caps`(b));
* `FoldLayerCaps pr hne k r`: the fold-type layer caps (`𝔱 = D`, cut F21) at the recorded cap
  `k_D`. This cap is not of block-cap form (B1: its `clean_g` exceeds it; it is the cap of the
  reference fold record of `lem:old-f-law`(e)), so it stays a block-level *hypothesis*;
* **`middleLayerCaps_uniform_of_cutCaps`**: `MiddleLayerCaps` of the uniform-root field laws at
  `capK i` from `MiddleL21Caps`, `MiddleE21Caps` and `FoldLayerCaps`;
* **`middleLayerCaps_individual_of_cutCaps`**: the same for the individual-square root, with the
  root-type cap (the L21 cap of the positive root, `cert:positive-root-caps`) as a hypothesis.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData

/-! ## The per-prime certificates of the layer cuts -/

/-- **The per-prime cap of the layer cut** of a swap-invariant two-layer graph `G₂` at the prime
`p`: the cut operator `A_p` on `L²(λ_p(G₁))` satisfies `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p`. -/
def LayerCutCap (O : Type) [Fintype O] [DecidableEq O] (G₂ : OrientedGraph (O × Fin 2))
    (hG : SwapInvariant O G₂) (g B : ℝ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (hne : (injLabellings (ZMod p) G₂).Nonempty)
    (v : EuclideanSpace ℝ ((layerData O G₂ hG).cut.Half → ZMod p)),
    -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (layerData O G₂ hG) hne v⟫_ℝ ∧
      ⟪v, Spectral.cutOp (layerData O G₂ hG) hne v⟫_ℝ ≤ (1 + B / p) * ‖v‖ ^ 2

/-- **The per-prime certificates of the cut L21 on piece `i`** (layer swap of `G_{L,2}`, uniform
root) at `(allpG i 2, allpB i 2)`. *Hypothesis* (`lem:layer12-caps`(b)). -/
def MiddleL21Caps (i : Fin 33) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
    LayerCutCap (ZMod 6) (recordGraph (Fin 2)) recordGraph_swap (allpG i 2) (allpB i 2) p

/-- **The per-prime certificates of the cut E21 on piece `i`** (layer swap of `G_{E,2}`) at
`(allpG i 4, allpB i 4)`. *Hypothesis* (`lem:layer12-caps`(b)). -/
def MiddleE21Caps (i : Fin 33) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
    LayerCutCap (Fin 3) (matchGraph (Fin 2)) matchGraph_swap (allpG i 4) (allpB i 4) p

/-! ## The layer caps at the block-cap values -/

section Fields

variable {i : Fin 33} {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime]
  (b : ℕ)

/-- **A layer cap at the block-cap value `capVal i c`**, from the per-prime certificates of the
layer cut of `G₂` at `(allpG i c, allpB i c)`, for a block of class-three primes of piece `i` with
`∑ log p ≤ 570` and least prime `b`. -/
theorem layerCap_capVal (O : Type) [Fintype O] [DecidableEq O] (G₂ : OrientedGraph (O × Fin 2))
    (hG : SwapInvariant O G₂) (G₁ : OrientedGraph (O × Fin 1)) (hres : LayerRestricts O G₂ G₁)
    (c : Fin 5) (hc : c ≠ 3)
    (hcert : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
      LayerCutCap O G₂ hG (allpG i c) (allpB i c) p)
    (h3 : ∀ j, pr j % 4 = 3) (hpc : ∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i)
    (hbud : ∑ j, Real.log (pr j) ≤ middleBudget) (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b)
    (hL : ∀ j, (injLabellings (ZMod (pr j)) G₂).Nonempty)
    (h₁ : ∀ j, (injLabellings (ZMod (pr j)) G₁).Nonempty) (φ : ZMod 6 → O) :
    reservedCut.Below
      (-(capVal i c * (b : ℝ) ^ (-(1 / 2 : ℝ))) •
        signedIntegral (emit (blockGraphLaw pr G₁ h₁) (midDiagEmission φ)).weight)
      (signedIntegral (emit (blockGraphLaw pr G₂ hL) (midEmission φ)).weight) := by
  rw [rpow_neg_half_eq]
  obtain ⟨j₀, hj₀⟩ := hb'
  have hX : (1 : ℝ) < pieceStart i := lt_trans (by norm_num) (pieceStart_gt_36 i)
  have hXb : (pieceStart i : ℝ) ≤ b := by
    rw [← hj₀]
    exact_mod_cast (hpc j₀).1
  have hLs : ∑ j, Real.log (pr j) ≤ 570 := middleBudget_real ▸ hbud
  unfold capVal
  exact layerCap_of_cutCaps O pr G₂ hG G₁ hres hL h₁ φ (allpG_nonneg i c hc) (allpB_nonneg i c hc)
    hX hXb (fun j => by exact_mod_cast hb j) hLs (fun j => allpG_mul_lt_one i c (hpc j).1)
    (fun j v => (hcert (pr j) (h3 j) (hpc j).1 (hpc j).2 (hL j) v).1)
    (fun j v => (hcert (pr j) (h3 j) (hpc j).1 (hpc j).2 (hL j) v).2)

/-- **The fold-type layer caps** (`𝔱 = D`, cut F21) of a middle block at the cap `k`:
`Π_{F_j} ⪰_ι -k r Diag_ι(Π⁽¹⁾_{F_j})` for the three folds. -/
def FoldLayerCaps (hne : MiddleNonempty pr) (k r : ℝ) : Prop :=
  ∀ j : Fin 3, reservedCut.Below
    (-(k * r) • signedIntegral (emit (blockGraphLaw pr (foldGraph (Fin 1)) hne.F1)
      (midDiagEmission (fold j))).weight)
    (signedIntegral (emit (blockGraphLaw pr (foldGraph (Fin 2)) hne.F2)
      (midEmission (fold j))).weight)

/-- The matching-, merge- and constant-type layer caps (`𝔱 = S, R, C`, cut E21) of a middle
block, which do not depend on the root. -/
theorem layerCaps_SRC (hE21 : MiddleE21Caps i) (h3 : ∀ j, pr j % 4 = 3)
    (hpc : ∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i)
    (hbud : ∑ j, Real.log (pr j) ≤ middleBudget) (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b)
    (hne : MiddleNonempty pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) :
    ∀ (t : PType) (φ : t.Pat), t = .S ∨ t = .R ∨ t = .C →
      reservedCut.Below
        (-(capK i t * (b : ℝ) ^ (-(1 / 2 : ℝ))) •
          signedIntegral (midComponent (middleBlockFieldLaws pr hne root) (false, ⟨t, φ⟩)).weight)
        (signedIntegral (midComponent (middleBlockFieldLaws pr hne root) (true, ⟨t, φ⟩)).weight)
  | .S, φ, _ => layerCap_capVal pr b (Fin 3) (matchGraph (Fin 2)) matchGraph_swap
      (matchGraph (Fin 1)) matchGraph_restricts 4 (by decide) hE21 h3 hpc hbud hb hb' hne.E2 hne.E1
      (matching φ)
  | .R, φ, _ => layerCap_capVal pr b (Fin 3) (matchGraph (Fin 2)) matchGraph_swap
      (matchGraph (Fin 1)) matchGraph_restricts 4 (by decide) hE21 h3 hpc hbud hb hb' hne.E2 hne.E1
      (fun u => (merge φ.1 φ.2 u).castSucc)
  | .C, _, _ => layerCap_capVal pr b (Fin 3) (matchGraph (Fin 2)) matchGraph_swap
      (matchGraph (Fin 1)) matchGraph_restricts 4 (by decide) hE21 h3 hpc hbud hb hb' hne.E2 hne.E1
      (fun _ => 0)

/-- **The layer caps of a uniform-root middle block at `capK i`** (`lem:front12:reference`(ii),
third display): L21 and E21 from the per-prime certificates, F21 (`k_D`) as `FoldLayerCaps`. -/
theorem middleLayerCaps_uniform_of_cutCaps (hL21 : MiddleL21Caps i) (hE21 : MiddleE21Caps i)
    (h3 : ∀ j, pr j % 4 = 3) (hpc : ∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i)
    (hbud : ∑ j, Real.log (pr j) ≤ middleBudget) (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b)
    (hne : MiddleNonempty pr)
    (hD : FoldLayerCaps pr hne ((allpInputs i).k .D) ((b : ℝ) ^ (-(1 / 2 : ℝ)))) :
    MiddleLayerCaps (middleBlockFieldLaws pr hne (uniformRoot pr hne)) (capK i)
      ((b : ℝ) ^ (-(1 / 2 : ℝ))) := by
  intro t φ
  cases t with
  | L =>
    exact layerCap_capVal pr b (ZMod 6) (recordGraph (Fin 2)) recordGraph_swap
      (recordGraph (Fin 1)) recordGraph_restricts 2 (by decide) hL21 h3 hpc hbud hb hb' hne.L2
      hne.L1 (fun u => u)
  | D => exact hD φ
  | S => exact layerCaps_SRC pr b hE21 h3 hpc hbud hb hb' hne _ .S φ (by simp)
  | R => exact layerCaps_SRC pr b hE21 h3 hpc hbud hb hb' hne _ .R φ (by simp)
  | C => exact layerCaps_SRC pr b hE21 h3 hpc hbud hb hb' hne _ .C φ (by simp)

/-- **The root-type layer cap of an individual-square-root block** (`𝔱 = L`, the L21 cap of the
positive root, `cert:positive-root-caps`): `Π_L ⪰_ι -k_L r Diag_ι(Π⁽¹⁾_L)`. -/
def IndividualRootLayerCap (u : ℚ) (hne : MiddleNonempty pr) (k r : ℝ) : Prop :=
  reservedCut.Below
    (-(k * r) • signedIntegral (midComponent (middleBlockFieldLaws pr hne
      (individualBlockRoot pr u hne.L2)) (false, ⟨.L, ()⟩)).weight)
    (signedIntegral (midComponent (middleBlockFieldLaws pr hne
      (individualBlockRoot pr u hne.L2)) (true, ⟨.L, ()⟩)).weight)

/-- **The layer caps of an individual-square-root middle block at `capK i`**: E21 from the
per-prime certificates; the root type and F21 as hypotheses. -/
theorem middleLayerCaps_individual_of_cutCaps {u : ℚ} (hE21 : MiddleE21Caps i)
    (h3 : ∀ j, pr j % 4 = 3) (hpc : ∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i)
    (hbud : ∑ j, Real.log (pr j) ≤ middleBudget) (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b)
    (hne : MiddleNonempty pr)
    (hLt : IndividualRootLayerCap pr u hne (capK i .L) ((b : ℝ) ^ (-(1 / 2 : ℝ))))
    (hD : FoldLayerCaps pr hne ((allpInputs i).k .D) ((b : ℝ) ^ (-(1 / 2 : ℝ)))) :
    MiddleLayerCaps (middleBlockFieldLaws pr hne (individualBlockRoot pr u hne.L2)) (capK i)
      ((b : ℝ) ^ (-(1 / 2 : ℝ))) := by
  intro t φ
  cases t with
  | L => exact hLt
  | D => exact hD φ
  | S => exact layerCaps_SRC pr b hE21 h3 hpc hbud hb hb' hne _ .S φ (by simp)
  | R => exact layerCaps_SRC pr b hE21 h3 hpc hbud hb hb' hne _ .R φ (by simp)
  | C => exact layerCaps_SRC pr b hE21 h3 hpc hbud hb hb' hne _ .C φ (by simp)

end Fields

end Sarkozy.BlockAdapter
