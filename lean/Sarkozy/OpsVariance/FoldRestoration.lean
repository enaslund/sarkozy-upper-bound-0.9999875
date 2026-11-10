module

public import Sarkozy.OpsVariance.MergeE1
public import Sarkozy.Variance.RestorationBlocks
public import Sarkozy.Variance.RestorationVarianceBlocks

@[expose] public section

/-!
# `lem:record:restoration` at the comparison data: the reduction of `hF` / `hRes`

`paper/sections/22_variance.tex`, `lem:record:restoration` (steps (C), (B), the three branches),
`cor:var-classes`(i), `lem:record:paired-e-joint`(b).

The (Res) input of a fold class is `hRes : (l₀ − z₁) Y ≤ Y[⊗_X Π_{F_j} ⊗ μ]` (`energyX`), and the
inputs `hF` of an aligned matching class are the same for `j = 1, 2`. W1 proved the lemma on
abstract factors (`restoration_pointwise_blocks`, `restoration_variance_blocks`). Here it is
stated at the comparison data `D`, in the `energyX` form, with:

* the reference `Y = Y[⊗ μ]` (`energyFirst_eq_diagonalIntegral`) and the outside positivity at the
  fold chamber `c` (any cut of the family, `D.law_positive`) discharged;
* the fold records written as diagonal copies `Diag_c(λ_𝔅)` from their diagonality at `c`
  (`eq_diagonalLaw_of_isDiagonalAt`);
* (E1) for the nonroot part reduced to (E1) for the mixed products `⊗_S 𝓜̄ ⊗_{X∖S} Π^rt ⊗ μ`
  (`hE1M_of_E1`, through `energy_merge_le`).

Results:

* **`hRes_pointwise`**: the pointwise branch `Y[Π_X] ≥ (1 + h − (1 + z) h C_X)/M_X · Y`, from the
  root split `hmix`, the root half marginals `ν` at `c`, hypothesis (A) `ν ≤ M λ`, and (E1);
* **`hRes_variance`**: the bounded-variance branch `Y[Π_X] ≥ branchVar(l', C', χ_X) Y`, from the
  root split, the chi-square `χ_X`, the orbit decompositions and (E1) for the orbit diagonals.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
  Sarkozy.Variance

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

omit [DecidableEq P] in
/-- `Y = Y[⊗ μ]` as a diagonal integral. -/
theorem Y_eq_diag (L : ℕ) (A : Finset ℤ) :
    D.Y L A = diagonalIntegral (tensorLaw (D.R.law p L)) (blockLift m₀ blk p L A) :=
  TheoremC.energyFirst_eq_diagonalIntegral (fun L => D.R.law p L) (blockLift m₀ blk p) L A

omit [DecidableEq P] in
/-- **The energy of the selected records, as diagonal copies at `c`**: if every record law on `X`
is diagonal at `c`, `Y[⊗_X w ⊗ μ] = Y[⊗_X Diag_c(λ) ⊗ μ]`, `λ` the plus-half marginals. -/
theorem energyX_eq_diag (L : ℕ) (A : Finset ℤ) (c : ReflectionCut Slot)
    (X : Finset (BlockAtom Bk J L)) (wF : ∀ b, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (hd : ∀ b ∈ X, IsDiagonalAt c (signedIntegral (wF b))) :
    energyX D L A X wF = diagonalIntegral (tensorLaw (onBlocks X
      (fun b => c.diagonalLaw (Comparison.halfMarginalPlus c (signedIntegral (wF b))))
      (D.R.law p L))) (blockLift m₀ blk p L A) := by
  unfold energyX
  congr 2
  funext b
  unfold onBlocks
  by_cases hb : b ∈ X
  · simp only [hb, ↓reduceIte]
    exact eq_diagonalLaw_of_isDiagonalAt c (hd b hb)
  · simp only [hb, ↓reduceIte]

omit [DecidableEq P] in
/-- **(E1) for the nonroot part from (E1) for the mixed products**: with `𝓜_𝔅 = h_𝔅 𝓜̄_𝔅`, the
hypothesis `hE1M` of W1's restoration lemmas follows from
`Y[⊗_S 𝓜̄ ⊗_{X∖S} Π^rt ⊗ μ] ≤ (1 + z) C_X Y` for every nonempty `S ⊆ X`. -/
theorem hE1M_of_E1 (L : ℕ) (A : Finset ℤ) (X : Finset (BlockAtom Bk J L))
    (wR : ∀ b, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (Mr Mbar : ∀ b, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) (hh : BlockAtom Bk J L → ℝ)
    (hh0 : ∀ b, 0 ≤ hh b) (hMr : ∀ b ∈ X, Mr b = hh b • Mbar b) {CX z : ℝ}
    (hE1 : ∀ f : BlockAtom Bk J L → Bool, (∃ b, f b = true) → (∀ b, f b = true → b ∈ X) →
      diagonalIntegral (tensorLaw (fun b => if f b then Mbar b else
        onBlocks X (fun b => signedIntegral (wR b)) (D.R.law p L) b)) (blockLift m₀ blk p L A) ≤
        (1 + z) * CX * D.Y L A) :
    diagonalIntegral (tensorLaw (onBlocks X (fun b => signedIntegral (wR b) + Mr b) (D.R.law p L)))
        (blockLift m₀ blk p L A) -
      diagonalIntegral (tensorLaw (onBlocks X (fun b => signedIntegral (wR b)) (D.R.law p L)))
        (blockLift m₀ blk p L A) ≤
      (1 + z) * (∏ b ∈ X, (1 + hh b) - 1) * CX * D.Y L A := by
  have e : onBlocks X (fun b => signedIntegral (wR b) + Mr b) (D.R.law p L) =
      onBlocks X (fun b => signedIntegral (wR b) + hh b • Mbar b) (D.R.law p L) := by
    funext b
    unfold onBlocks
    by_cases hb : b ∈ X
    · simp only [hb, ↓reduceIte, hMr b hb]
    · simp only [hb, ↓reduceIte]
  rw [e]
  have hm := energy_merge_le (D.R.law p L) (fun b => signedIntegral (wR b)) Mbar X hh hh0
    (blockLift m₀ blk p L A) hE1
  calc _ ≤ (∏ b ∈ X, (1 + hh b) - 1) * ((1 + z) * CX * D.Y L A) := hm
    _ = (1 + z) * (∏ b ∈ X, (1 + hh b) - 1) * CX * D.Y L A := by ring

omit [DecidableEq P] in
/-- **`lem:record:restoration`, pointwise branch, at the comparison data** (the (Res) input
`hRes` / `hF` of a fold product): at a fold chamber `c` (a cut of the family), with the fold
records diagonal at `c` with half laws `λ`, the reference split `μ_𝔅 = (1 + h_𝔅)⁻¹(Π^rt_𝔅 + 𝓜_𝔅)`
on `X`, the root coupling `w_R ≥ 0` with both half marginals `ν` at `c`, hypothesis (A)
`ν ≤ M λ`, and (E1) for the nonroot part:
`(1 + h − (1 + z) h C_X) Y ≤ (∏_X M_𝔅) Y[⊗_X Π_{F} ⊗ μ]`, `h = ∏_X (1 + h_𝔅) − 1`. -/
theorem hRes_pointwise (L : ℕ) (A : Finset ℤ) (c : ReflectionCut Slot) (hc : IsFamilyCut c)
    (X : Finset (BlockAtom Bk J L)) (wF : ∀ b, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (hd : ∀ b ∈ X, IsDiagonalAt c (signedIntegral (wF b)))
    (wR : ∀ b, (Slot → BlockLabel m₀ blk p L b) → ℝ) (hwR : ∀ b ∈ X, ∀ z, 0 ≤ wR b z)
    (Mr : ∀ b, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) (hh : BlockAtom Bk J L → ℝ)
    (hh0 : ∀ b ∈ X, 0 ≤ hh b)
    (hmix : ∀ b ∈ X, D.R.law p L b = (1 + hh b)⁻¹ • (signedIntegral (wR b) + Mr b))
    {CX z : ℝ}
    (hE1M : diagonalIntegral (tensorLaw (onBlocks X (fun b => signedIntegral (wR b) + Mr b)
          (D.R.law p L))) (blockLift m₀ blk p L A) -
        diagonalIntegral (tensorLaw (onBlocks X (fun b => signedIntegral (wR b)) (D.R.law p L)))
          (blockLift m₀ blk p L A) ≤
      (1 + z) * (∏ b ∈ X, (1 + hh b) - 1) * CX * D.Y L A)
    (ν : ∀ b, (c.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hplus : ∀ b ∈ X, plusMarginal c (wR b) = ν b) (hminus : ∀ b ∈ X, minusMarginal c (wR b) = ν b)
    (M : BlockAtom Bk J L → ℝ)
    (hA : ∀ b ∈ X, ∀ x, ν b x ≤ M b * Comparison.halfMarginalPlus c (signedIntegral (wF b)) x) :
    (1 + (∏ b ∈ X, (1 + hh b) - 1) - (1 + z) * (∏ b ∈ X, (1 + hh b) - 1) * CX) * D.Y L A ≤
      (∏ b ∈ X, M b) * energyX D L A X wF := by
  rw [energyX_eq_diag L A c X wF hd]
  exact restoration_pointwise_blocks c (D.R.law p L) X (fun b _ => D.law_positive hc L b)
    (blockLift m₀ blk p L A) (Y_eq_diag L A).symm wR hwR Mr hh hh0 hmix hE1M ν
    (fun b => Comparison.halfMarginalPlus c (signedIntegral (wF b))) hplus hminus M hA

omit [DecidableEq P] in
/-- **`lem:record:restoration`, bounded-variance branch, at the comparison data**: with the root
split, the root half laws `ν` and the record half laws `λ` (probability laws, `ν ≪ λ`), the
product chi-square `χ_X ≥ ∏_X (1 + χ_𝔅) − 1`, the orbit decompositions `ν = ∑ ν(x) o_x`,
`λ = ∑ λ(x) o_x` (translation invariance) and (E1) for the orbit diagonals (`hE1o`, constant `C'`):
`branchVar(l', C', χ_X) Y ≤ Y[⊗_X Π_F ⊗ μ]`, `l' = 1 + h − (1 + z) h C_X`. -/
theorem hRes_variance (L : ℕ) (A : Finset ℤ) (c : ReflectionCut Slot) (hc : IsFamilyCut c)
    (X : Finset (BlockAtom Bk J L)) (wF : ∀ b, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (hd : ∀ b ∈ X, IsDiagonalAt c (signedIntegral (wF b))) (hY : 0 < D.Y L A)
    (wR : ∀ b, (Slot → BlockLabel m₀ blk p L b) → ℝ) (hwR : ∀ b ∈ X, ∀ z, 0 ≤ wR b z)
    (Mr : ∀ b, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) (hh : BlockAtom Bk J L → ℝ)
    (hh0 : ∀ b ∈ X, 0 ≤ hh b)
    (hmix : ∀ b ∈ X, D.R.law p L b = (1 + hh b)⁻¹ • (signedIntegral (wR b) + Mr b))
    {CX z : ℝ}
    (hE1M : diagonalIntegral (tensorLaw (onBlocks X (fun b => signedIntegral (wR b) + Mr b)
          (D.R.law p L))) (blockLift m₀ blk p L A) -
        diagonalIntegral (tensorLaw (onBlocks X (fun b => signedIntegral (wR b)) (D.R.law p L)))
          (blockLift m₀ blk p L A) ≤
      (1 + z) * (∏ b ∈ X, (1 + hh b) - 1) * CX * D.Y L A)
    (ν : ∀ b, (c.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hplus : ∀ b ∈ X, plusMarginal c (wR b) = ν b) (hminus : ∀ b ∈ X, minusMarginal c (wR b) = ν b)
    (hlam0 : ∀ b ∈ X, ∀ x, 0 ≤ Comparison.halfMarginalPlus c (signedIntegral (wF b)) x)
    (hν1 : ∀ b ∈ X, ∑ x, ν b x = 1)
    (hlam1 : ∀ b ∈ X, ∑ x, Comparison.halfMarginalPlus c (signedIntegral (wF b)) x = 1)
    (hac : ∀ b ∈ X, ∀ x, Comparison.halfMarginalPlus c (signedIntegral (wF b)) x = 0 → ν b x = 0)
    (χ : BlockAtom Bk J L → ℝ)
    (hχ : ∀ b ∈ X, ∑ x, (ν b x - Comparison.halfMarginalPlus c (signedIntegral (wF b)) x) ^ 2 /
      Comparison.halfMarginalPlus c (signedIntegral (wF b)) x ≤ χ b)
    {χX : ℝ} (hχX : ∏ b ∈ X, (1 + χ b) - 1 ≤ χX)
    (o : ∀ b, (c.Half → BlockLabel m₀ blk p L b) → (c.Half → BlockLabel m₀ blk p L b) → ℝ)
    (ho : ∀ b ∈ X, ∀ x y, 0 ≤ o b x y) (hνo : ∀ b ∈ X, ∀ y, ν b y = ∑ x, ν b x * o b x y)
    (hlamo : ∀ b ∈ X, ∀ y, Comparison.halfMarginalPlus c (signedIntegral (wF b)) y =
      ∑ x, Comparison.halfMarginalPlus c (signedIntegral (wF b)) x * o b x y)
    (i₀ : ∀ b, c.Half → BlockLabel m₀ blk p L b) {C' : ℝ}
    (hE1o : ∀ f : (∀ b, c.Half → BlockLabel m₀ blk p L b),
      diagonalIntegral (tensorLaw (onBlocks X (fun b => c.diagonalLaw (o b (f b))) (D.R.law p L)))
        (blockLift m₀ blk p L A) ≤ C' * D.Y L A)
    (hl' : 0 < 1 + (∏ b ∈ X, (1 + hh b) - 1) - (1 + z) * (∏ b ∈ X, (1 + hh b) - 1) * CX) :
    branchVar (1 + (∏ b ∈ X, (1 + hh b) - 1) - (1 + z) * (∏ b ∈ X, (1 + hh b) - 1) * CX) C' χX *
        D.Y L A ≤ energyX D L A X wF := by
  rw [energyX_eq_diag L A c X wF hd]
  exact restoration_variance_blocks c (D.R.law p L) X (fun b _ => D.law_positive hc L b)
    (blockLift m₀ blk p L A) (Y_eq_diag L A).symm hY wR hwR Mr hh hh0 hmix hE1M ν
    (fun b => Comparison.halfMarginalPlus c (signedIntegral (wF b))) hplus hminus hlam0 hν1 hlam1
    hac χ hχ hχX o ho hνo hlamo i₀ hE1o hl'

end Sarkozy.OpsVariance
