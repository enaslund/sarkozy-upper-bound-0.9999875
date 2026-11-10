module

public import Sarkozy.OpsSteps.Step3
public import Sarkozy.BracketEnergy.SharpDiff

@[expose] public section

/-!
# The per-coupling bound of Step 3 from the coupled sharp terms (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 3 ("`[D_ω]_ω = ∑_C c(C)[C]_ω` with
placed couplings, which are admissible probability measures") and proof of `lem:orbit-coupon`(i)
("Every `C_k` is an admissible probability measure. Its difference is bounded as in the proof of
`lem:bracket-energy`: `lem:sharp-first` with `F` the first-stage atoms outside `X`,
`ρ_𝔅 = Ñ_{0,𝔅}`, and the two tags"); `paper/sections/10_comparison_lemmas.tex`, `lem:bracket-energy`
(third bound), `lem:sharp-first`.

The input `herr` of `Step3.step3_orbit` is the bound
`|Y^Ñ[[C]] − Y^{Ñ₀}[[C]]| ≤ (R_err + z') C_X Y + r_C` at every placed coupling. A coupling of the
expansion is a tensor product `C = ⊗_𝔅 C_𝔅` of per-block couplings, so with product objects
`[C]_ω = ⊗_{𝔅 ∈ X} [C_𝔅]_{ω(𝔅)}` (B11's `place_tensor`). For such a tensor this file reduces
`herr` to the per-choice bounds of `lem:sharp-first` (the coupled pieces, `lem:density:coupled`),
the same form in which EC proved (E1) for the norm envelopes:

* `paperEN_tensor`, `paperEN0_tensor`: `Y^Ñ[⊗_{𝔅 ∈ S} Q_𝔅]` and `Y^{Ñ₀}[⊗_{𝔅 ∈ S} Q_𝔅]` are the
  energies of the full tensors with `Q` on `S` and `Ñ`, resp. `Ñ₀`, outside;
* **`coupling_diff_of_coupled`**: if every nonempty choice `σ` of record differences outside `S`
  and every tag `j` present in it have `|E_σ| ≤ K wt_j(σ) + r_σ` (B9's `sharpPiece` with `Q` on
  `S`), then `|Y^Ñ[⊗ Q] − Y^{Ñ₀}[⊗ Q]| ≤ (R_err + z) K + ∑_σ r_σ` (B9's `diff_bound_of_coupled`
  through the CRT coordinates, `multilinearIntegral_crt`);
* **`herr_of_coupled`**: the same for a placed tensor coupling `[⊗_𝔅 C_𝔅]_ω`, the form of `herr`;
* `rCan`, `hterm_rCan`, **`herr_canonical`**: with the canonical remainders (the excess of each
  coupled term over its main term, as EC's `rX`) the per-coupling bound holds outright; the content
  is the sum of these remainders over the couplings and the class selections.

With `K = (1 + ε) C_X Y` (the per-term main term of `lem:density:coupled`), the right side is
`(R_err + z') C_X Y + ∑_σ r_σ` with `z' = z + ε (R_err + z)`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.EnvelopeSteps Sarkozy.RecordExpansion Sarkozy.TheoremCBlock Sarkozy.BlockFrame
  Sarkozy.BracketEnergy Sarkozy.EnvelopeEnergiesPaper

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

omit [DecidableEq P] in
/-- `Y^Ñ[⊗_{𝔅 ∈ S} Q_𝔅]` is the energy of the full tensor with `Q` on `S` and `Ñ` outside. -/
theorem paperEN_tensor (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) :
    paperEN D L A S (tensorLaw fun b : {b // b ∈ S} => Qb b.1) =
      diagonalIntegral (tensorLaw fun b => if decide (b ∈ S) then Qb b else D.GB.N L b)
        (blockLift m₀ blk p L A) := by
  let L' : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b := fun b =>
    if decide (b ∈ S) then Qb b else D.GB.N L b
  have h1 : (fun b : {b // b ∈ S} => L' b.1) = fun b : {b // b ∈ S} => Qb b.1 := by
    funext b
    simp only [L', decide_eq_true b.2, ↓reduceIte]
  have h2 : (fun b : {b // b ∉ S} => L' b.1) = fun b : {b // b ∉ S} => D.GB.N L b.1 := by
    funext b
    simp only [L', decide_eq_false b.2, Bool.false_eq_true, ↓reduceIte]
  have key := jointEnergy_tensor S L' (blockLift m₀ blk p L A)
  rw [h1, h2] at key
  unfold paperEN
  rw [jointEnergyL_apply]
  change jointEnergy _ (NOut D L S) _ = _
  unfold NOut
  exact key

omit [DecidableEq P] in
/-- `Y^{Ñ₀}[⊗_{𝔅 ∈ S} Q_𝔅]` is the energy of the full tensor with `Q` on `S` and `Ñ₀` outside. -/
theorem paperEN0_tensor (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) :
    paperEN0 D L A S (tensorLaw fun b : {b // b ∈ S} => Qb b.1) =
      diagonalIntegral (tensorLaw fun b => if decide (b ∈ S) then Qb b else D.GB.N₀ L b)
        (blockLift m₀ blk p L A) := by
  let L' : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b := fun b =>
    if decide (b ∈ S) then Qb b else D.GB.N₀ L b
  have h1 : (fun b : {b // b ∈ S} => L' b.1) = fun b : {b // b ∈ S} => Qb b.1 := by
    funext b
    simp only [L', decide_eq_true b.2, ↓reduceIte]
  have h2 : (fun b : {b // b ∉ S} => L' b.1) = fun b : {b // b ∉ S} => D.GB.N₀ L b.1 := by
    funext b
    simp only [L', decide_eq_false b.2, Bool.false_eq_true, ↓reduceIte]
  have key := jointEnergy_tensor S L' (blockLift m₀ blk p L A)
  rw [h1, h2] at key
  unfold paperEN0
  rw [jointEnergyL_apply]
  change jointEnergy _ (N0Out D L S) _ = _
  unfold N0Out
  exact key

omit [DecidableEq P] in
/-- **The difference `Y^Ñ − Y^{Ñ₀}` at a tensor on `S` from the coupled sharp terms**
(`lem:bracket-energy`, third bound, through `lem:sharp-first`; B9's `diff_bound_of_coupled`). -/
theorem coupling_diff_of_coupled (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ)
    (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) {K z : ℝ} (hK : 0 ≤ K) (hz : 0 ≤ z)
    (r : (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      |diagonalIntegral (tensorLaw (sharpPiece D L Qb (fun b => decide (b ∈ S)) σ))
          (blockLift m₀ blk p L A)| ≤
        K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if decide (b ∈ S) then 0 else D.GB.uprice L b) j σ + r σ) :
    |paperEN D L A S (tensorLaw fun b : {b // b ∈ S} => Qb b.1) -
        paperEN0 D L A S (tensorLaw fun b : {b // b ∈ S} => Qb b.1)| ≤
      (D.GB.Rerr + z) * K +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ := by
  rw [paperEN_tensor, paperEN0_tensor]
  unfold diagonalIntegral
  rw [multilinearIntegral_crt blk h0 L, multilinearIntegral_crt blk h0 L]
  refine diff_bound_of_coupled blk D L h0 Qb (fun b => decide (b ∈ S))
    (fun v y => blockLift m₀ blk p L A (crtLabelEquiv blk h0 L y)) hK hz r ?_
  intro σ hσ j hj
  have h := hterm σ hσ j hj
  unfold diagonalIntegral at h
  rwa [multilinearIntegral_crt blk h0 L] at h

omit [DecidableEq P] in
/-- **The input `herr` of `step3_orbit` for a tensor coupling** (`lem:orbit-coupon`(i), "every `C_k`
is an admissible probability measure; its difference is bounded as in the proof of
`lem:bracket-energy`"): for product objects and a coupling `C` whose kernel is the product of
per-block kernels `C_𝔅`, the placed coupling is `⊗_𝔅 [C_𝔅]` (`place_tensor`), and the coupled
sharp terms with `Q_𝔅 = [C_𝔅]` on `S` give `|Y^Ñ[[C]] − Y^{Ñ₀}[[C]]| ≤ (R_err + z) K + ∑_σ r_σ`. -/
theorem herr_of_coupled (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ)
    (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) (O : {b // b ∈ S} → Type)
    [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)] (m : ∀ b, O b → ℝ)
    (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    (Cb : ∀ b, (O b → ℝ) →ₗ[ℝ] (O b → ℝ)) (Cop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hC : ∀ x y, kern (prodWeight m) Cop x y = ∏ b, kern (m b) (Cb b) (x b) (y b))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ : ∀ b : {b // b ∈ S}, Qb b.1 = place reservedCut (m b) (φ b) (Cb b))
    {K z : ℝ} (hK : 0 ≤ K) (hz : 0 ≤ z) (r : (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      |diagonalIntegral (tensorLaw (sharpPiece D L Qb (fun b => decide (b ∈ S)) σ))
          (blockLift m₀ blk p L A)| ≤
        K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if decide (b ∈ S) then 0 else D.GB.uprice L b) j σ + r σ) :
    |paperEN D L A S (place reservedCut (prodWeight m) (prodPlace reservedCut φ) Cop) -
        paperEN0 D L A S (place reservedCut (prodWeight m) (prodPlace reservedCut φ) Cop)| ≤
      (D.GB.Rerr + z) * K +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ := by
  have ht : place reservedCut (prodWeight m) (prodPlace reservedCut φ) Cop =
      tensorLaw fun b : {b // b ∈ S} => Qb b.1 := by
    rw [place_tensor reservedCut m φ Cb Cop hC]
    congr 1
    funext b
    exact (hQ b).symm
  rw [ht]
  exact coupling_diff_of_coupled D h0 L A S Qb hK hz r hterm

/-! ## Canonical remainders: the per-coupling bound holds outright -/

/-- **The canonical remainder of a coupled sharp term**: its excess over the main term
`K wt_j(σ)`, summed over the tags `j` present in `σ` (EC's `rX`, here for a tensor `Q` on `S`). -/
noncomputable def rCan (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (K : ℝ)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j, if 1 ≤ countVec (D.FS.tag L) σ j then
    max 0 (|diagonalIntegral (tensorLaw (sharpPiece D L Qb (fun b => decide (b ∈ S)) σ))
        (blockLift m₀ blk p L A)| -
      K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
        (fun b => if decide (b ∈ S) then 0 else D.GB.uprice L b) j σ)
  else 0

omit [DecidableEq P] in
theorem rCan_nonneg (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (K : ℝ) (σ : ∀ b, Option (D.FS.Ib L b)) :
    0 ≤ rCan D L A S Qb K σ :=
  sum_nonneg fun j _ => by split_ifs <;> simp

omit [DecidableEq P] in
/-- The per-choice bounds hold with the canonical remainders. -/
theorem hterm_rCan (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (K : ℝ) :
    ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      |diagonalIntegral (tensorLaw (sharpPiece D L Qb (fun b => decide (b ∈ S)) σ))
          (blockLift m₀ blk p L A)| ≤
        K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if decide (b ∈ S) then 0 else D.GB.uprice L b) j σ + rCan D L A S Qb K σ := by
  intro σ _ j hj
  set E := |diagonalIntegral (tensorLaw (sharpPiece D L Qb (fun b => decide (b ∈ S)) σ))
    (blockLift m₀ blk p L A)|
  set M := K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
    (fun b => if decide (b ∈ S) then 0 else D.GB.uprice L b) j σ
  have hj' : (if 1 ≤ countVec (D.FS.tag L) σ j then max 0 (E - M) else 0) ≤
      rCan D L A S Qb K σ := by
    unfold rCan
    exact single_le_sum (f := fun j => if 1 ≤ countVec (D.FS.tag L) σ j then
      max 0 (|diagonalIntegral (tensorLaw (sharpPiece D L Qb (fun b => decide (b ∈ S)) σ))
          (blockLift m₀ blk p L A)| -
        K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if decide (b ∈ S) then 0 else D.GB.uprice L b) j σ) else 0)
      (fun j _ => by split_ifs <;> simp) (mem_univ j)
  simp only [hj, ↓reduceIte] at hj'
  linarith [le_max_right 0 (E - M)]

omit [DecidableEq P] in
/-- **The per-coupling bound of Step 3 with canonical remainders** (no hypothesis on the terms):
`|Y^Ñ[[C]] − Y^{Ñ₀}[[C]]| ≤ (R_err + z) K + ∑_σ rCan_σ` for a placed tensor coupling. The content
of `lem:bracket-energy` at `[C]_ω` is then the **sum** of the canonical remainders over the
couplings and the selections of the classes (the analog of EC's `E1Rem`): it must be
`≤ c L^{-σ} α` with the weights `π̃_ω |c_ω(C)|` (field `hrr`, through `r₃ = ∑_C |c(C)| r_C`). -/
theorem herr_canonical (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ)
    (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) (O : {b // b ∈ S} → Type)
    [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)] (m : ∀ b, O b → ℝ)
    (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    (Cb : ∀ b, (O b → ℝ) →ₗ[ℝ] (O b → ℝ)) (Cop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hC : ∀ x y, kern (prodWeight m) Cop x y = ∏ b, kern (m b) (Cb b) (x b) (y b))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ : ∀ b : {b // b ∈ S}, Qb b.1 = place reservedCut (m b) (φ b) (Cb b))
    {K z : ℝ} (hK : 0 ≤ K) (hz : 0 ≤ z) :
    |paperEN D L A S (place reservedCut (prodWeight m) (prodPlace reservedCut φ) Cop) -
        paperEN0 D L A S (place reservedCut (prodWeight m) (prodPlace reservedCut φ) Cop)| ≤
      (D.GB.Rerr + z) * K +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          rCan D L A S Qb K σ :=
  herr_of_coupled D h0 L A S O m φ Cb Cop hC Qb hQ hK hz _ (hterm_rCan D L A S Qb K)

end Sarkozy.OpsSteps
