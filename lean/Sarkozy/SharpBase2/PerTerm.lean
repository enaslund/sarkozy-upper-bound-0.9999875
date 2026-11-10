module

public import Sarkozy.DensityFibre.FoldedFields

@[expose] public section

/-!
# The per-term geometric mean of `lem:sharp-first`

SH2 (7 November 2026). DC2's `choice_le_folded` folds a whole per-choice term at once:
`|E_σ| ≤ √(∑_φ w 𝔈₊(φ)) √(∑_φ w 𝔈₋(φ))`. Combined with per-piece bounds
`𝔈_±(φ) ≤ BG M_± + r_±(φ)`, any AM–GM of the two sums produces cross terms
`√(W M₊ R₋)` that mix the **main terms of the small pieces** with the **energies of the large
pieces** `q_E > N^τ`. The large pieces are summed only with the decay `N^{-τ/4}`
(`lem:record:density-lp`, Rankin), so these cross terms decay like `N^{-τ/8} = N^{-1/1608}`,
below the `L^{-1/825}` of the summation fields (and below the induction exponent).

The paper does not do this: in the proof of `lem:sharp-first` each expanded energy `T'` (one
choice of pieces `φ`) is bounded by **its own** geometric mean `√(𝔈₊(φ) 𝔈₋(φ))`, and only then
are the small pieces' main terms and the large pieces' energies summed separately. Here:

* `abs_tensor_sum_le_perterm`: `|E| ≤ ∑_φ w_φ √𝔈₊(φ) √𝔈₋(φ)` (the step before the
  Cauchy–Schwarz in G1/I1's `abs_tensor_sum_le_folded`);
* `choice_le_perterm`: the same for DC2's per-choice terms (`lem:record:folded-energy` per term);
* `sqrt_mul_add_le`: `√((x+a)(y+b)) ≤ √(xy) + √(xb) + √(ay) + √(ab)`;
* `pieceRem`: the per-piece remainder: at a small piece `√(BG M₊ G₋C) + √(G₊C BG M₋) +
  √(G₊C G₋C)` (main × chain remainder, chain²), at a large piece `√𝔈₊ √𝔈₋`;
* **`choice_bound_perterm`**: from the chain bounds `𝔈_±(φ) ≤ BG M_± + G_± C` at the small
  admissible pieces, `M₊M₋ = M₀²`, `M₀ ≤ M`: `|E_σ| ≤ M wt_j(σ) + ∑_φ w_φ pieceRem(φ)`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpBase2

open Sarkozy.EnvelopeInputs Sarkozy.Comparison Sarkozy.RecordExpansion ReflectionCut

section Tensor

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)]

/-- **The per-term folded bound** (`lem:record:folded-energy` applied to every expanded term):
`|E(⊗_b ∑_i c_{b,i} K_{b,i})| ≤ ∑_f w_f √𝔈₊(f) √𝔈₋(f)`, with nonnegative folded energies. -/
theorem abs_tensor_sum_le_perterm (c : ReflectionCut V) {I : J → Type*} [∀ j, Fintype (I j)]
    (coef d : ∀ j, I j → ℝ) (K Lp Lm : ∀ j, I j → ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hLp : ∀ j i, c.Positive (Lp j i)) (hLm : ∀ j i, c.Positive (Lm j i))
    (hbr : ∀ j i, c.Bracket (d j i • Lp j i) (K j i) (d j i • Lm j i))
    (a : V → (∀ j, X j) → ℝ) :
    (∀ f, 0 ≤ foldedPlus c Lp a f) ∧ (∀ f, 0 ≤ foldedMinus c Lm a f) ∧
      |multilinearIntegral (tensorLaw fun j => ∑ i, coef j i • K j i) a| ≤
        ∑ f, choiceWeight coef d f * Real.sqrt (foldedPlus c Lp a f) *
          Real.sqrt (foldedMinus c Lm a f) := by
  have hfold : ∀ f : ∀ j, I j, 0 ≤ foldedPlus c Lp a f ∧ 0 ≤ foldedMinus c Lm a f ∧
      |multilinearIntegral (tensorLaw fun j => K j (f j)) a| ≤ (∏ j, d j (f j)) *
        Real.sqrt (foldedPlus c Lp a f) * Real.sqrt (foldedMinus c Lm a f) := fun f =>
    folded_energy_tensor c (fun j => K j (f j)) (fun j => Lp j (f j)) (fun j => Lm j (f j))
      (fun j => d j (f j)) (fun j => hd j (f j)) (fun j => hLp j (f j)) (fun j => hLm j (f j))
      (fun j => hbr j (f j)) a
  refine ⟨fun f => (hfold f).1, fun f => (hfold f).2.1, ?_⟩
  have hexp : tensorLaw (fun j => ∑ i, coef j i • K j i) =
      ∑ f : (∀ j, I j), (∏ j, coef j (f j)) • tensorLaw (fun j => K j (f j)) := by
    rw [tensorLaw_sum (fun j i => coef j i • K j i)]
    refine Finset.sum_congr rfl fun f _ => ?_
    exact tensorLaw_smul (fun j => coef j (f j)) (fun j => K j (f j))
  have hsplit : multilinearIntegral (tensorLaw fun j => ∑ i, coef j i • K j i) a =
      ∑ f : (∀ j, I j), (∏ j, coef j (f j)) *
        multilinearIntegral (tensorLaw fun j => K j (f j)) a := by
    rw [hexp]
    unfold multilinearIntegral
    rw [LinearMap.sum_apply]
    rfl
  rw [hsplit]
  calc |∑ f : (∀ j, I j), (∏ j, coef j (f j)) *
        multilinearIntegral (tensorLaw fun j => K j (f j)) a|
      ≤ ∑ f : (∀ j, I j), |(∏ j, coef j (f j)) *
          multilinearIntegral (tensorLaw fun j => K j (f j)) a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f : (∀ j, I j), choiceWeight coef d f * Real.sqrt (foldedPlus c Lp a f) *
          Real.sqrt (foldedMinus c Lm a f) := by
        refine Finset.sum_le_sum fun f _ => ?_
        rw [abs_mul, Finset.abs_prod]
        have h1 := (hfold f).2.2
        have h0 : 0 ≤ ∏ j, |coef j (f j)| := Finset.prod_nonneg fun j _ => abs_nonneg _
        calc (∏ j, |coef j (f j)|) * |multilinearIntegral (tensorLaw fun j => K j (f j)) a|
            ≤ (∏ j, |coef j (f j)|) * ((∏ j, d j (f j)) *
                Real.sqrt (foldedPlus c Lp a f) * Real.sqrt (foldedMinus c Lm a f)) :=
              mul_le_mul_of_nonneg_left h1 h0
          _ = choiceWeight coef d f * Real.sqrt (foldedPlus c Lp a f) *
                Real.sqrt (foldedMinus c Lm a f) := by
              unfold choiceWeight
              rw [Finset.prod_mul_distrib]
              ring

end Tensor

/-- `√((x+a)(y+b)) ≤ √(xy) + √(xb) + √(ay) + √(ab)` for nonnegative `x, y, a, b`. -/
theorem sqrt_mul_add_le {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt ((x + a) * (y + b)) ≤
      Real.sqrt (x * y) + Real.sqrt (x * b) + Real.sqrt (a * y) + Real.sqrt (a * b) := by
  rw [Real.sqrt_le_left (by positivity)]
  have s1 := Real.sq_sqrt (mul_nonneg hx hy)
  have s2 := Real.sq_sqrt (mul_nonneg hx hb)
  have s3 := Real.sq_sqrt (mul_nonneg ha hy)
  have s4 := Real.sq_sqrt (mul_nonneg ha hb)
  have e1 : Real.sqrt (x * y) * Real.sqrt (a * b) = Real.sqrt (x * b) * Real.sqrt (a * y) := by
    rw [← Real.sqrt_mul (mul_nonneg hx hy), ← Real.sqrt_mul (mul_nonneg hx hb)]
    congr 1
    ring
  nlinarith [Real.sqrt_nonneg (x * y), Real.sqrt_nonneg (x * b), Real.sqrt_nonneg (a * y),
    Real.sqrt_nonneg (a * b),
    mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg (x * b)),
    mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg (a * y)),
    mul_nonneg (Real.sqrt_nonneg (x * b)) (Real.sqrt_nonneg (a * b)),
    mul_nonneg (Real.sqrt_nonneg (a * y)) (Real.sqrt_nonneg (a * b))]

open Classical in
/-- **The per-piece remainder of `lem:sharp-first`**: at a small piece (where the chain
`𝔈_± ≤ BG M_± + G_± C` applies) the cross terms `√(BG M₊ · G₋C) + √(G₊C · BG M₋) +
√(G₊C · G₋C)`; at a large piece the geometric mean `√𝔈₊ √𝔈₋` itself
(`lem:record:density-lp`). -/
noncomputable def pieceRem {Φ : Type} (small : Φ → Prop) (BG Gp Gm Fp Fm : Φ → ℝ)
    (Mp Mm Cr : ℝ) (φ : Φ) : ℝ :=
  if small φ then
    Real.sqrt (BG φ * Mp * (Gm φ * Cr)) + Real.sqrt (Gp φ * Cr * (BG φ * Mm)) +
      Real.sqrt (Gp φ * Cr * (Gm φ * Cr))
  else Real.sqrt (Fp φ) * Real.sqrt (Fm φ)

theorem pieceRem_nonneg {Φ : Type} (small : Φ → Prop) (BG Gp Gm Fp Fm : Φ → ℝ)
    (Mp Mm Cr : ℝ) (φ : Φ) : 0 ≤ pieceRem small BG Gp Gm Fp Fm Mp Mm Cr φ := by
  unfold pieceRem
  split_ifs
  · positivity
  · positivity

/-- **The per-term remainder of one choice and tag**: `∑_φ w_φ pieceRem(φ)` with the main prices
`M_± = K₀ P_±`. Arguments as DC3's `HfoldAlgebra.rchVal`. -/
noncomputable def rchPT {Φ : Type} [Fintype Φ] (small : Φ → Prop) (K₀ Pp Pm Cr : ℝ)
    (w BG Gp Gm Fp Fm : Φ → ℝ) : ℝ :=
  ∑ φ, w φ * pieceRem small BG Gp Gm Fp Fm (K₀ * Pp) (K₀ * Pm) Cr φ

theorem rchPT_nonneg {Φ : Type} [Fintype Φ] (small : Φ → Prop) (K₀ Pp Pm Cr : ℝ)
    (w BG Gp Gm Fp Fm : Φ → ℝ) (hw : ∀ φ, 0 ≤ w φ) :
    0 ≤ rchPT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm :=
  Finset.sum_nonneg fun φ _ => mul_nonneg (hw φ) (pieceRem_nonneg _ _ _ _ _ _ _ _ _ φ)

/-- **One piece**: `√𝔈₊ √𝔈₋ ≤ BG M₀ + pieceRem` (`M₊M₋ = M₀²`). -/
theorem sqrt_folded_le_piece {Φ : Type} (small : Φ → Prop) (BG Gp Gm Fp Fm : Φ → ℝ)
    {Mp Mm M0 Cr : ℝ} (hMp : 0 ≤ Mp) (hMm : 0 ≤ Mm) (hM0 : 0 ≤ M0) (hprod : Mp * Mm = M0 ^ 2)
    (hCr : 0 ≤ Cr) (φ : Φ) (hBG : 0 ≤ BG φ) (hGp : 0 ≤ Gp φ) (hGm : 0 ≤ Gm φ)
    (hFp : 0 ≤ Fp φ) (hFm : 0 ≤ Fm φ)
    (hp : small φ → Fp φ ≤ BG φ * Mp + Gp φ * Cr) (hm : small φ → Fm φ ≤ BG φ * Mm + Gm φ * Cr) :
    Real.sqrt (Fp φ) * Real.sqrt (Fm φ) ≤ BG φ * M0 + pieceRem small BG Gp Gm Fp Fm Mp Mm Cr φ := by
  unfold pieceRem
  split_ifs with hs
  · rw [← Real.sqrt_mul hFp]
    have hx : 0 ≤ BG φ * Mp := mul_nonneg hBG hMp
    have hy : 0 ≤ BG φ * Mm := mul_nonneg hBG hMm
    have ha : 0 ≤ Gp φ * Cr := mul_nonneg hGp hCr
    have hb : 0 ≤ Gm φ * Cr := mul_nonneg hGm hCr
    have h1 : Real.sqrt (Fp φ * Fm φ) ≤
        Real.sqrt ((BG φ * Mp + Gp φ * Cr) * (BG φ * Mm + Gm φ * Cr)) :=
      Real.sqrt_le_sqrt (mul_le_mul (hp hs) (hm hs) hFm (add_nonneg hx ha))
    have h2 := sqrt_mul_add_le hx hy ha hb
    have h3 : Real.sqrt (BG φ * Mp * (BG φ * Mm)) = BG φ * M0 := by
      rw [show BG φ * Mp * (BG φ * Mm) = (BG φ * M0) ^ 2 by rw [mul_pow, ← hprod]; ring]
      exact Real.sqrt_sq (mul_nonneg hBG hM0)
    linarith
  · have := mul_nonneg hBG hM0
    linarith

end Sarkozy.SharpBase2

namespace Sarkozy.SharpBase2

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.EnvelopeInputsBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic ReflectionCut
open Sarkozy.DensityFibre

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ} (dec : DecFamily D L)
  (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
variable (blk)

omit [DecidableEq P] in
/-- **The per-term folded bound of a per-choice term** (`lem:record:folded-energy` at `c_j`, per
expanded term, as in the paper's proof of `lem:sharp-first`):
`|E_σ| ≤ ∑_φ w_φ √𝔈₊(φ) √𝔈₋(φ)`, with nonnegative folded energies. -/
theorem choice_le_perterm (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (hQ0 : ∀ b, IsNonneg (Qb b)) (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) :
    (∀ φ, 0 ≤ foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
      (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) ∧
    (∀ φ, 0 ≤ foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
      (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) ∧
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G| ≤
      ∑ φ, choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ *
          Real.sqrt (foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
            (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) *
        Real.sqrt (foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
            (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) := by
  have hcrt := multilinearIntegral_crt blk h0 L (sharpPiece D L Qb f σ)
    (fun v x => G v ((crtLabelEquiv blk h0 L).symm x))
  simp only [Equiv.symm_apply_apply] at hcrt
  rw [← hcrt]
  have hlaw : sharpPiece D L Qb f σ = fun b => ∑ x, hpieceCoef D L f σ j b x • bpieceK D L Qb j b
      x :=
    funext fun b => (bpieceSum_eq D L Qb f σ j b).symm
  rw [hlaw]
  exact abs_tensor_sum_le_perterm (D.FS.cut j) (hpieceCoef D L f σ j) (bpieceD D L)
    (bpieceK D L Qb j) (bpieceLp D L Qb dec j) (bpieceLm D L Qb dec j) (bpieceD_nonneg D L)
    (bpieceLp_positive D L Qb dec hQ0 j) (bpieceLm_positive D L Qb dec hQ0 j)
    (bpiece_bracket D L Qb dec hQ0 j)
    (fun v x => G v ((crtLabelEquiv blk h0 L).symm x))

omit [DecidableEq P] in
/-- **The per-choice bound with per-term geometric means** (the paper's proof of
`lem:sharp-first`): if the folded energies of the small admissible pieces satisfy the chain bound
`𝔈_±(φ) ≤ (∏ g) M_± + G_±(φ) C` (`prop:record:density-structured`), with `M_± ≥ 0`,
`M₊M₋ = M₀²` and `0 ≤ M₀ ≤ M`, then `|E_σ| ≤ M wt_j(σ) + ∑_φ w_φ pieceRem(φ)`. -/
theorem choice_bound_perterm (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (hQ0 : ∀ b, IsNonneg (Qb b)) (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ)
    (small : (∀ b, HPiece D L b) → Prop)
    {K₀ Pp Pm M0 M Cr : ℝ} (hMp : 0 ≤ K₀ * Pp) (hMm : 0 ≤ K₀ * Pm) (hM0 : 0 ≤ M0)
    (hprod : (K₀ * Pp) * (K₀ * Pm) = M0 ^ 2)
    (hMM : M0 ≤ M) (hCr : 0 ≤ Cr) (Gp Gm : (∀ b, HPiece D L b) → ℝ) (hGp : ∀ φ, 0 ≤ Gp φ)
    (hGm : ∀ φ, 0 ≤ Gm φ)
    (hp : ∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) → small φ →
      foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
        (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ ≤
        (∏ b, bpieceG D L b (φ b)) * (K₀ * Pp) + Gp φ * Cr)
    (hm : ∀ φ, (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) → small φ →
      foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
        (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ ≤
        (∏ b, bpieceG D L b (φ b)) * (K₀ * Pm) + Gm φ * Cr) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G| ≤
      M * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if f b then 0 else D.GB.uprice L b) j σ +
        rchPT small K₀ Pp Pm Cr (choiceWeight (hpieceCoef D L f σ j) (bpieceD D L))
          (fun φ => ∏ b, bpieceG D L b (φ b)) Gp Gm
            (foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
              (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)))
            (foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
              (fun v x => G v ((crtLabelEquiv blk h0 L).symm x))) := by
  unfold rchPT
  obtain ⟨hp0, hm0, hfold⟩ := choice_le_perterm blk dec Qb h0 hQ0 f σ j G
  set w := choiceWeight (hpieceCoef D L f σ j) (bpieceD D L)
  have hw : ∀ φ, 0 ≤ w φ := fun φ =>
    Finset.prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (bpieceD_nonneg D L b (φ b))
  set T := ∑ φ : (∀ b, HPiece D L b), w φ * ∏ b, bpieceG D L b (φ b)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun φ _ =>
    mul_nonneg (hw φ) (Finset.prod_nonneg fun b _ => bpieceG_nonneg D L b (φ b))
  have hTw : T ≤ tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
      (fun b => if f b then 0 else D.GB.uprice L b) j σ := by
    have hprod' : ∏ b, ∑ x, |hpieceCoef D L f σ j b x| * bpieceD D L b x * bpieceG D L b x = T :=
      by
      rw [Fintype.prod_sum (fun b x => |hpieceCoef D L f σ j b x| * bpieceD D L b x *
        bpieceG D L b x)]
      refine Finset.sum_congr rfl fun φ _ => ?_
      simp only [w, choiceWeight]
      rw [← Finset.prod_mul_distrib]
    rw [← hprod']
    unfold tagWeight
    exact Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (bpieceD_nonneg D L b x)) (bpieceG_nonneg D L b x))
      fun b _ => sum_bpieceWeight_le D L f σ j b
  have hpt : ∀ φ, w φ * Real.sqrt (foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
        (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) *
      Real.sqrt (foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
        (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ) ≤
      w φ * ((∏ b, bpieceG D L b (φ b)) * M0) +
        w φ * pieceRem small (fun φ => ∏ b, bpieceG D L b (φ b)) Gp Gm
          (foldedPlus (D.FS.cut j) (bpieceLp D L Qb dec j)
            (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)))
          (foldedMinus (D.FS.cut j) (bpieceLm D L Qb dec j)
            (fun v x => G v ((crtLabelEquiv blk h0 L).symm x))) (K₀ * Pp) (K₀ * Pm) Cr φ := by
    intro φ
    by_cases hφ : ∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0
    · rw [mul_assoc, ← mul_add]
      exact mul_le_mul_of_nonneg_left (sqrt_folded_le_piece small
        (fun φ => ∏ b, bpieceG D L b (φ b)) Gp Gm _ _ hMp hMm hM0 hprod
        hCr φ (Finset.prod_nonneg fun b _ => bpieceG_nonneg D L b (φ b)) (hGp φ) (hGm φ) (hp0 φ)
        (hm0 φ) (hp φ hφ) (hm φ hφ)) (hw φ)
    · simp only [not_forall, not_not] at hφ
      obtain ⟨b₀, hb₀⟩ := hφ
      have : w φ = 0 := Finset.prod_eq_zero (Finset.mem_univ b₀) (by rw [hb₀, abs_zero, zero_mul])
      rw [this]
      simp
  have hsum := Finset.sum_le_sum fun φ (_ : φ ∈ Finset.univ) => hpt φ
  rw [Finset.sum_add_distrib] at hsum
  have hmain : ∑ φ, w φ * ((∏ b, bpieceG D L b (φ b)) * M0) = T * M0 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun φ _ => by ring
  rw [hmain] at hsum
  have hM : 0 ≤ M := hM0.trans hMM
  have h1 : T * M0 ≤ tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
      (fun b => if f b then 0 else D.GB.uprice L b) j σ * M :=
    mul_le_mul hTw hMM hM0 (hT0.trans hTw)
  linarith

end Sarkozy.SharpBase2
