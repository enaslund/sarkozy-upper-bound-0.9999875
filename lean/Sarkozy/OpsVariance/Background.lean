module

public import Sarkozy.OpsVariance.Restoration

@[expose] public section

/-!
# `hres` for an aligned matching class from `prop:background-variance`(a) at the actual `Ñ₀`

`paper/sections/22_variance.tex`, `prop:background-variance`(a) (the displayed bound and "The class
cost"), `lem:pool-coupons`(a), `lem:distinct-choice`(a), `lem:record:paired-e-joint`(b),
`lem:record:paired-e-bridge`(b), `lem:record:gram`(i), `def:record:frame`(b).

W1's `background_variance_a_blocks` proves the displayed bound
`½ ∑_s Y[J_{X,s} ⊗ (μ + R)] ≥ (C_m b̃ − z_b) Y` for abstract outside laws `μ`, `R`. Here it is
applied at the paper's objects: `μ = D.R.law`, `R = Ñ₀ − μ = ∑_i κu_i` (`N₀_eq`), `F = blockLift`,
and the half marginals of the two aligned selections `ω₀, ω₁` on `X` are those of their norm
envelopes (`envM`). Then `μ + R = Ñ₀`, so the displayed bound is about B10's `Y[J_X ⊗ Ñ₀]`
(`varJ0`), and `hres_of_average` turns it into the field `hres` of `VarStepsAt` for the class
`{ω₀, ω₁}` (`hres_of_background`), with `b̃` the bracket
`[ℓ/C_m − (η + k)]_+/(1 − k) + ∑_r W_r [ℓ_r/C_m − C_r(η_r + k)]_+/(1 − k)` of the paper.

The inputs are W1's, at the actual laws: the aligned embeddings `e_s` on `X` and the matching
records `w_s` off `X`, their half marginals, symmetry and (Cen); the exterior order
`R_𝔅 ⪰ c_𝔅 Diag(m'_{s,𝔅})` (`lem:record:gram`(i)); the kept sets `Z` and the choice weights `W`
(`lem:distinct-choice`(a)); (E1) for the diagonals of `X` and `X ∪ Z` with `μ` outside; and
`lem:record:paired-e-joint`(b) for `X` and every `X ∪ Z` (the restoration). W1's (E1) hypotheses
have no additive remainders; at the paper's data (E1) carries the remainders of `E1Sub`
(`e1mu_front` for `X`).
-/

open Filter Finset Function
open scoped Topology BigOperators

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
/-- `Y[J_X ⊗ (μ + ∑ κu)] = Y[J_X ⊗ Ñ₀]`. -/
theorem varJ0_eq_muR (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ) :
    diagonalIntegral (tensorLaw fun b => if b ∈ Choice.support ω then indepLaw reservedCut (m b)
      else D.R.law p L b + ∑ i, D.GB.κu L b i) (blockLift m₀ blk p L A) = varJ0 D L A ω m := by
  unfold varJ0
  congr 2
  funext b
  split_ifs
  · rfl
  · exact (N₀_eq L b).symm

omit [DecidableEq P] in
/-- **The restoration field `hres` for an aligned matching class `{ω₀, ω₁}` from
`prop:background-variance`(a)** (W1's `background_variance_a_blocks` at `μ = D.R.law`,
`R = ∑_i κu_i`, `m_s = envM ω_s`; then `hres_of_average` with the common price `γ₀`). The gain is
the paper's bracket `b̃`; the error `z ≥ z_b` collects W1's error terms. -/
theorem hres_of_background {π : Type*} [DecidableEq π] {L : ℕ} {A : Finset ℤ}
    (ω₀ ω₁ : Choice (D.CL.T L)) (hne : ω₀ ≠ ω₁) (X : Finset (BlockAtom Bk J L))
    (hX₀ : Choice.support ω₀ = X) (hX₁ : Choice.support ω₁ = X) {γ₀ : ℝ}
    (hγ₀ : monomial (D.CL.πt L) ω₀ = γ₀) (hγ₁ : monomial (D.CL.πt L) ω₁ = γ₀)
    -- the selected aligned embeddings on `X`
    (e0 e1 : ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (hw0 : ∀ j ∈ X, ∀ z, 0 ≤ e0 j z) (hw1 : ∀ j ∈ X, ∀ z, 0 ≤ e1 j z)
    (hp0 : ∀ j ∈ X, plusMarginal reservedCut (e0 j) = envM D L ω₀ j)
    (hn0 : ∀ j ∈ X, minusMarginal reservedCut (e0 j) = envM D L ω₀ j)
    (hp1 : ∀ j ∈ X, plusMarginal reservedCut (e1 j) = envM D L ω₁ j)
    (hn1 : ∀ j ∈ X, minusMarginal reservedCut (e1 j) = envM D L ω₁ j)
    (ht0 : ∀ j ∈ X, ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L j) → ℝ,
      reservedCut.form (signedIntegral (e0 j)) G H = reservedCut.form (signedIntegral (e0 j)) H G)
    (ht1 : ∀ j ∈ X, ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L j) → ℝ,
      reservedCut.form (signedIntegral (e1 j)) G H = reservedCut.form (signedIntegral (e1 j)) H G)
    (κj : BlockAtom Bk J L → ℝ)
    (hcen0 : ∀ j ∈ X, CentredNormLe reservedCut (signedIntegral (e0 j)) (envM D L ω₀ j) (κj j))
    (hcen1 : ∀ j ∈ X, CentredNormLe reservedCut (signedIntegral (e1 j)) (envM D L ω₁ j) (κj j))
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hκ : ∀ j ∈ X, κj j ≤ k)
    -- the matching records of the other blocks
    (w0 w1 : ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (ms0 ms1 : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hv0 : ∀ j, j ∉ X → ∀ z, 0 ≤ w0 j z) (hv1 : ∀ j, j ∉ X → ∀ z, 0 ≤ w1 j z)
    (hq0 : ∀ j, j ∉ X → plusMarginal reservedCut (w0 j) = ms0 j)
    (hr0 : ∀ j, j ∉ X → minusMarginal reservedCut (w0 j) = ms0 j)
    (hq1 : ∀ j, j ∉ X → plusMarginal reservedCut (w1 j) = ms1 j)
    (hr1 : ∀ j, j ∉ X → minusMarginal reservedCut (w1 j) = ms1 j)
    (hu0 : ∀ j, j ∉ X → ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L j) → ℝ,
      reservedCut.form (signedIntegral (w0 j)) G H = reservedCut.form (signedIntegral (w0 j)) H G)
    (hu1 : ∀ j, j ∉ X → ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L j) → ℝ,
      reservedCut.form (signedIntegral (w1 j)) G H = reservedCut.form (signedIntegral (w1 j)) H G)
    -- the exterior (`lem:record:gram`(i), `def:record:frame`(b))
    (coef : BlockAtom Bk J L → ℝ) (hcoef : ∀ j, 0 ≤ coef j)
    (hR0 : ∀ j, j ∉ X → reservedCut.Positive
      ((∑ i, D.GB.κu L j i) - coef j • reservedCut.diagonalLaw (ms0 j)))
    (hR1 : ∀ j, j ∉ X → reservedCut.Positive
      ((∑ i, D.GB.κu L j i) - coef j • reservedCut.diagonalLaw (ms1 j)))
    -- the kept nonempty sets and their patterns (`lem:distinct-choice`(a))
    (Zs : Finset (BlockAtom Bk J L → Bool)) (hZs0 : ∀ g ∈ Zs, ∀ j ∈ X, g j = false)
    (hZsne : (fun _ => false) ∉ Zs) (pats : Finset π) (pat : (BlockAtom Bk J L → Bool) → π)
    (hpat : ∀ g ∈ Zs, pat g ∈ pats) (W : π → ℝ) (hW0 : ∀ r, 0 ≤ W r)
    (hW : ∀ r ∈ pats, W r ≤ ∑ g ∈ Zs.filter (fun g => pat g = r), setCoeff coef g)
    -- the numbers
    {CX Cm ℓ η e z₂ z : ℝ} (hY : 0 ≤ D.Y L A) (hCX1 : 1 ≤ CX)
    (hCX : ∏ b ∈ X, selectionFactor a p D.S.selPre L b = CX) (hCm : CX ≤ Cm) (hz₂ : 0 ≤ z₂)
    (he : 0 ≤ e) (ℓr Cr ηr er CXZ : π → ℝ) (hCr : ∀ r, 0 ≤ Cr r) (her : ∀ r, 0 ≤ er r)
    (hCXZ : ∀ r, CXZ r ≤ Cm * Cr r)
    -- (E1), `μ` outside, and `lem:record:paired-e-joint`(b) for `X` and every `X ∪ Z`
    (hDsel0 : diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) X X (envM D L ω₀)))
      (blockLift m₀ blk p L A) ≤ (1 + z₂) * CX * D.Y L A)
    (hDsel1 : diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) X X (envM D L ω₁)))
      (blockLift m₀ blk p L A) ≤ (1 + z₂) * CX * D.Y L A)
    (hbsel : (ℓ - Cm * 1 * η - e) * D.Y L A ≤
      (diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X e0 (envM D L ω₀)))
          (blockLift m₀ blk p L A) +
        diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X e1 (envM D L ω₁)))
          (blockLift m₀ blk p L A)) / 2)
    (hDZ0 : ∀ g ∈ Zs, diagonalIntegral (tensorLaw (diagFamZ reservedCut (D.R.law p L) X
        (indSet g) X (envM D L ω₀) ms0)) (blockLift m₀ blk p L A) ≤
      (1 + z₂) * CXZ (pat g) * D.Y L A)
    (hDZ1 : ∀ g ∈ Zs, diagonalIntegral (tensorLaw (diagFamZ reservedCut (D.R.law p L) X
        (indSet g) X (envM D L ω₁) ms1)) (blockLift m₀ blk p L A) ≤
      (1 + z₂) * CXZ (pat g) * D.Y L A)
    (hbZ : ∀ g ∈ Zs, (ℓr (pat g) - Cm * Cr (pat g) * ηr (pat g) - er (pat g)) * D.Y L A ≤
      (diagonalIntegral (tensorLaw (recFamZ reservedCut (D.R.law p L) X (indSet g) X e0
          (envM D L ω₀) w0)) (blockLift m₀ blk p L A) +
        diagonalIntegral (tensorLaw (recFamZ reservedCut (D.R.law p L) X (indSet g) X e1
          (envM D L ω₁) w1)) (blockLift m₀ blk p L A)) / 2)
    -- the error
    (hz : (e + k * z₂ * Cm * 1) / (1 - k) +
      ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k)) ≤ z) :
    ((max 0 (ℓ / Cm - 1 * (η + k)) / (1 - k) +
        ∑ r ∈ pats, W r * (max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k))) - z) *
      (∑ ω ∈ ({ω₀, ω₁} : Finset (Choice (D.CL.T L))), monomial (D.CL.πt L) ω * selProd D L ω) *
        D.Y L A - 0 ≤
      ∑ ω ∈ ({ω₀, ω₁} : Finset (Choice (D.CL.T L))),
        monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω) := by
  have hμ : ∀ j, j ∉ X → reservedCut.Positive (D.R.law p L j) := fun j _ =>
    D.law_positive reservedCut_isFamilyCut L j
  have hpCm : 0 < Cm := by linarith
  have hdisp := background_variance_a_blocks reservedCut (D.R.law p L)
    (fun b => ∑ i, D.GB.κu L b i) X hμ (blockLift m₀ blk p L A) e0 e1 (envM D L ω₀)
    (envM D L ω₁) hw0 hw1 hp0 hn0 hp1 hn1 ht0 ht1
    (fun j hj => by rw [sum_envM (by rw [hX₀]; exact hj)]; exact one_pos)
    (fun j hj => by rw [sum_envM (by rw [hX₁]; exact hj)]; exact one_pos)
    κj hcen0 hcen1 hk0 hk1 hκ w0 w1 ms0 ms1 hv0 hv1 hq0 hr0 hq1 hr1 hu0 hu1 coef hcoef hR0 hR1
    Zs hZs0 hZsne pats pat hpat W hW hY hCm hpCm hz₂ he ℓr Cr ηr er CXZ hCr her hCXZ hDsel0 hDsel1
    hbsel hDZ0 hDZ1 hbZ
  have e0' := varJ0_eq_muR (D := D) L A ω₀ (envM D L ω₀)
  have e1' := varJ0_eq_muR (D := D) L A ω₁ (envM D L ω₁)
  rw [hX₀] at e0'
  rw [hX₁] at e1'
  rw [e0', e1'] at hdisp
  -- the bracket `b̃ ≥ 0`
  set bt := max 0 (ℓ / Cm - 1 * (η + k)) / (1 - k) +
    ∑ r ∈ pats, W r * (max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k)) with hbt
  have h1k : 0 < 1 - k := by linarith
  have hbt0 : 0 ≤ bt := add_nonneg (div_nonneg (le_max_left _ _) h1k.le)
    (sum_nonneg fun r _ => mul_nonneg (hW0 r) (div_nonneg (le_max_left _ _) h1k.le))
  set zb := (e + k * z₂ * Cm * 1) / (1 - k) +
    ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k)) with hzb
  have hkz : 0 ≤ k * z₂ * Cm := mul_nonneg (mul_nonneg hk0 hz₂) hpCm.le
  have hzb0 : 0 ≤ zb := add_nonneg
    (div_nonneg (add_nonneg he (mul_nonneg hkz zero_le_one)) h1k.le)
    (sum_nonneg fun g _ => mul_nonneg (setCoeff_nonneg hcoef g)
      (div_nonneg (add_nonneg (her _) (mul_nonneg hkz (hCr _))) h1k.le))
  have hdisp' : (Cm * bt - zb) * D.Y L A * (({ω₀, ω₁} : Finset (Choice (D.CL.T L))).card) ≤
      ∑ ω ∈ ({ω₀, ω₁} : Finset (Choice (D.CL.T L))), varJ0 D L A ω (envM D L ω) := by
    rw [sum_pair hne, card_pair hne]
    have e : (Cm * bt - zb) * D.Y L A =
        (Cm * bt - (e + k * z₂ * Cm * 1) / (1 - k) -
          ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k))) *
            D.Y L A := by
      rw [hzb]
      ring
    push_cast
    nlinarith [hdisp, e]
  exact hres_of_average (γ₀ := γ₀) (C₀ := CX) ({ω₀, ω₁} : Finset (Choice (D.CL.T L)))
    (fun ω => monomial (D.CL.πt L) ω) (fun ω => selProd D L ω)
    (fun ω => varJ0 D L A ω (envM D L ω))
    (fun ω hω => by
      rcases mem_insert.mp hω with h | h
      · rw [h]; exact hγ₀
      · rw [mem_singleton.mp h]; exact hγ₁)
    (fun ω hω => by
      rcases mem_insert.mp hω with h | h
      · rw [h, selProd, hX₀]; exact hCX
      · rw [mem_singleton.mp h, selProd, hX₁]; exact hCX)
    (by rw [← hγ₀]; exact monomial_πt_nonneg L ω₀) hCX1 hCm hbt0 hzb0 hz hY hdisp'

omit [DecidableEq P] in
/-- **`hres_of_background` with the additive remainders of (E1)** (`def:robust`): at a least
counterexample (`Y > 0`), if the (E1) bounds for the diagonals of `X` and of every `X ∪ Z` carry
additive remainders at most `r`, the field `hres` holds with the remainder
`r₀ = γ₀ · 2 r · k C_m (1 + ∑_Z c_Z C_r)/(1 − k)`. (W1's bound at the error `z₂ + r/Y`.) -/
theorem hres_of_background_rem {π : Type*} [DecidableEq π] {L : ℕ} {A : Finset ℤ}
    (ω₀ ω₁ : Choice (D.CL.T L)) (hne : ω₀ ≠ ω₁) (X : Finset (BlockAtom Bk J L))
    (hX₀ : Choice.support ω₀ = X) (hX₁ : Choice.support ω₁ = X) {γ₀ : ℝ}
    (hγ₀ : monomial (D.CL.πt L) ω₀ = γ₀) (hγ₁ : monomial (D.CL.πt L) ω₁ = γ₀)
    -- the selected aligned embeddings on `X`
    (e0 e1 : ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (hw0 : ∀ j ∈ X, ∀ z, 0 ≤ e0 j z) (hw1 : ∀ j ∈ X, ∀ z, 0 ≤ e1 j z)
    (hp0 : ∀ j ∈ X, plusMarginal reservedCut (e0 j) = envM D L ω₀ j)
    (hn0 : ∀ j ∈ X, minusMarginal reservedCut (e0 j) = envM D L ω₀ j)
    (hp1 : ∀ j ∈ X, plusMarginal reservedCut (e1 j) = envM D L ω₁ j)
    (hn1 : ∀ j ∈ X, minusMarginal reservedCut (e1 j) = envM D L ω₁ j)
    (ht0 : ∀ j ∈ X, ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L j) → ℝ,
      reservedCut.form (signedIntegral (e0 j)) G H = reservedCut.form (signedIntegral (e0 j)) H G)
    (ht1 : ∀ j ∈ X, ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L j) → ℝ,
      reservedCut.form (signedIntegral (e1 j)) G H = reservedCut.form (signedIntegral (e1 j)) H G)
    (κj : BlockAtom Bk J L → ℝ)
    (hcen0 : ∀ j ∈ X, CentredNormLe reservedCut (signedIntegral (e0 j)) (envM D L ω₀ j) (κj j))
    (hcen1 : ∀ j ∈ X, CentredNormLe reservedCut (signedIntegral (e1 j)) (envM D L ω₁ j) (κj j))
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hκ : ∀ j ∈ X, κj j ≤ k)
    -- the matching records of the other blocks
    (w0 w1 : ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (ms0 ms1 : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hv0 : ∀ j, j ∉ X → ∀ z, 0 ≤ w0 j z) (hv1 : ∀ j, j ∉ X → ∀ z, 0 ≤ w1 j z)
    (hq0 : ∀ j, j ∉ X → plusMarginal reservedCut (w0 j) = ms0 j)
    (hr0 : ∀ j, j ∉ X → minusMarginal reservedCut (w0 j) = ms0 j)
    (hq1 : ∀ j, j ∉ X → plusMarginal reservedCut (w1 j) = ms1 j)
    (hr1 : ∀ j, j ∉ X → minusMarginal reservedCut (w1 j) = ms1 j)
    (hu0 : ∀ j, j ∉ X → ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L j) → ℝ,
      reservedCut.form (signedIntegral (w0 j)) G H = reservedCut.form (signedIntegral (w0 j)) H G)
    (hu1 : ∀ j, j ∉ X → ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L j) → ℝ,
      reservedCut.form (signedIntegral (w1 j)) G H = reservedCut.form (signedIntegral (w1 j)) H G)
    -- the exterior (`lem:record:gram`(i), `def:record:frame`(b))
    (coef : BlockAtom Bk J L → ℝ) (hcoef : ∀ j, 0 ≤ coef j)
    (hR0 : ∀ j, j ∉ X → reservedCut.Positive
      ((∑ i, D.GB.κu L j i) - coef j • reservedCut.diagonalLaw (ms0 j)))
    (hR1 : ∀ j, j ∉ X → reservedCut.Positive
      ((∑ i, D.GB.κu L j i) - coef j • reservedCut.diagonalLaw (ms1 j)))
    -- the kept nonempty sets and their patterns (`lem:distinct-choice`(a))
    (Zs : Finset (BlockAtom Bk J L → Bool)) (hZs0 : ∀ g ∈ Zs, ∀ j ∈ X, g j = false)
    (hZsne : (fun _ => false) ∉ Zs) (pats : Finset π) (pat : (BlockAtom Bk J L → Bool) → π)
    (hpat : ∀ g ∈ Zs, pat g ∈ pats) (W : π → ℝ) (hW0 : ∀ r, 0 ≤ W r)
    (hW : ∀ r ∈ pats, W r ≤ ∑ g ∈ Zs.filter (fun g => pat g = r), setCoeff coef g)
    -- the numbers
    {CX Cm ℓ η e z₂ z rt : ℝ} (hY : 0 < D.Y L A) (hrt : 0 ≤ rt) (hCX1 : 1 ≤ CX)
    (hCX : ∏ b ∈ X, selectionFactor a p D.S.selPre L b = CX) (hCm : CX ≤ Cm) (hz₂ : 0 ≤ z₂)
    (he : 0 ≤ e) (ℓr Cr ηr er CXZ : π → ℝ) (hCr : ∀ r, 0 ≤ Cr r) (her : ∀ r, 0 ≤ er r)
    (hCXZ : ∀ r, CXZ r ≤ Cm * Cr r) (hCXZ1 : ∀ r, 1 ≤ CXZ r)
    -- (E1), `μ` outside, and `lem:record:paired-e-joint`(b) for `X` and every `X ∪ Z`
    (hDsel0 : diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) X X (envM D L ω₀)))
      (blockLift m₀ blk p L A) ≤ (1 + z₂) * CX * D.Y L A + rt)
    (hDsel1 : diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) X X (envM D L ω₁)))
      (blockLift m₀ blk p L A) ≤ (1 + z₂) * CX * D.Y L A + rt)
    (hbsel : (ℓ - Cm * 1 * η - e) * D.Y L A ≤
      (diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X e0 (envM D L ω₀)))
          (blockLift m₀ blk p L A) +
        diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X e1 (envM D L ω₁)))
          (blockLift m₀ blk p L A)) / 2)
    (hDZ0 : ∀ g ∈ Zs, diagonalIntegral (tensorLaw (diagFamZ reservedCut (D.R.law p L) X
        (indSet g) X (envM D L ω₀) ms0)) (blockLift m₀ blk p L A) ≤
      (1 + z₂) * CXZ (pat g) * D.Y L A + rt)
    (hDZ1 : ∀ g ∈ Zs, diagonalIntegral (tensorLaw (diagFamZ reservedCut (D.R.law p L) X
        (indSet g) X (envM D L ω₁) ms1)) (blockLift m₀ blk p L A) ≤
      (1 + z₂) * CXZ (pat g) * D.Y L A + rt)
    (hbZ : ∀ g ∈ Zs, (ℓr (pat g) - Cm * Cr (pat g) * ηr (pat g) - er (pat g)) * D.Y L A ≤
      (diagonalIntegral (tensorLaw (recFamZ reservedCut (D.R.law p L) X (indSet g) X e0
          (envM D L ω₀) w0)) (blockLift m₀ blk p L A) +
        diagonalIntegral (tensorLaw (recFamZ reservedCut (D.R.law p L) X (indSet g) X e1
          (envM D L ω₁) w1)) (blockLift m₀ blk p L A)) / 2)
    -- the error
    (hz : (e + k * z₂ * Cm * 1) / (1 - k) +
      ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k)) ≤ z) :
    ((max 0 (ℓ / Cm - 1 * (η + k)) / (1 - k) +
        ∑ r ∈ pats, W r * (max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k))) - z) *
      (∑ ω ∈ ({ω₀, ω₁} : Finset (Choice (D.CL.T L))), monomial (D.CL.πt L) ω * selProd D L ω) *
        D.Y L A - γ₀ * (2 * rt * (k * Cm * (1 + ∑ g ∈ Zs, setCoeff coef g * Cr (pat g)) /
          (1 - k))) ≤
      ∑ ω ∈ ({ω₀, ω₁} : Finset (Choice (D.CL.T L))),
        monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω) := by
  have hμ : ∀ j, j ∉ X → reservedCut.Positive (D.R.law p L j) := fun j _ =>
    D.law_positive reservedCut_isFamilyCut L j
  have hpCm : 0 < Cm := by linarith
  set Y := D.Y L A with hYdef
  set δ := rt / Y with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hrt hY.le
  have hδY : δ * Y = rt := by rw [hδ]; field_simp
  -- (E1) at the error `z₂ + δ`
  have hup : ∀ {C₁ t : ℝ}, 1 ≤ C₁ → t ≤ (1 + z₂) * C₁ * Y + rt → t ≤ (1 + (z₂ + δ)) * C₁ * Y := by
    intro C₁ t hC₁ ht
    have : rt ≤ δ * C₁ * Y := by
      rw [← hδY]
      have := mul_le_mul_of_nonneg_left hC₁ hδ0
      nlinarith
    nlinarith
  have hdisp := background_variance_a_blocks reservedCut (D.R.law p L)
    (fun b => ∑ i, D.GB.κu L b i) X hμ (blockLift m₀ blk p L A) e0 e1 (envM D L ω₀)
    (envM D L ω₁) hw0 hw1 hp0 hn0 hp1 hn1 ht0 ht1
    (fun j hj => by rw [sum_envM (by rw [hX₀]; exact hj)]; exact one_pos)
    (fun j hj => by rw [sum_envM (by rw [hX₁]; exact hj)]; exact one_pos)
    κj hcen0 hcen1 hk0 hk1 hκ w0 w1 ms0 ms1 hv0 hv1 hq0 hr0 hq1 hr1 hu0 hu1 coef hcoef hR0 hR1
    Zs hZs0 hZsne pats pat hpat W hW hY.le hCm hpCm (add_nonneg hz₂ hδ0) he ℓr Cr ηr er CXZ hCr
    her hCXZ (hup hCX1 hDsel0) (hup hCX1 hDsel1) hbsel (fun g hg => hup (hCXZ1 _) (hDZ0 g hg))
    (fun g hg => hup (hCXZ1 _) (hDZ1 g hg)) hbZ
  have e0' := varJ0_eq_muR (D := D) L A ω₀ (envM D L ω₀)
  have e1' := varJ0_eq_muR (D := D) L A ω₁ (envM D L ω₁)
  rw [hX₀] at e0'
  rw [hX₁] at e1'
  rw [e0', e1'] at hdisp
  set bt := max 0 (ℓ / Cm - 1 * (η + k)) / (1 - k) +
    ∑ r ∈ pats, W r * (max 0 (ℓr r / Cm - Cr r * (ηr r + k)) / (1 - k)) with hbt
  have h1k : 0 < 1 - k := by linarith
  have hbt0 : 0 ≤ bt := add_nonneg (div_nonneg (le_max_left _ _) h1k.le)
    (sum_nonneg fun r _ => mul_nonneg (hW0 r) (div_nonneg (le_max_left _ _) h1k.le))
  set zb := (e + k * z₂ * Cm * 1) / (1 - k) +
    ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * z₂ * Cm * Cr (pat g)) / (1 - k)) with hzb
  have hkz : 0 ≤ k * z₂ * Cm := mul_nonneg (mul_nonneg hk0 hz₂) hpCm.le
  have hzb0 : 0 ≤ zb := add_nonneg
    (div_nonneg (add_nonneg he (mul_nonneg hkz zero_le_one)) h1k.le)
    (sum_nonneg fun g _ => mul_nonneg (setCoeff_nonneg hcoef g)
      (div_nonneg (add_nonneg (her _) (mul_nonneg hkz (hCr _))) h1k.le))
  -- the extra error is the remainder
  set κ' := k * Cm * (1 + ∑ g ∈ Zs, setCoeff coef g * Cr (pat g)) / (1 - k) with hκ'
  have hsplit : (e + k * (z₂ + δ) * Cm * 1) / (1 - k) + ∑ g ∈ Zs, setCoeff coef g *
      ((er (pat g) + k * (z₂ + δ) * Cm * Cr (pat g)) / (1 - k)) = zb + δ * κ' := by
    have hs : ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * (z₂ + δ) * Cm * Cr (pat g)) /
        (1 - k)) = ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * z₂ * Cm * Cr (pat g)) /
          (1 - k)) + δ * (k * Cm / (1 - k)) * ∑ g ∈ Zs, setCoeff coef g * Cr (pat g) := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun g _ => by field_simp; ring
    rw [hs, hzb, hκ']
    field_simp
    ring
  have hdisp2 : (Cm * bt - zb) * Y * (({ω₀, ω₁} : Finset (Choice (D.CL.T L))).card) -
      2 * rt * κ' ≤
      ∑ ω ∈ ({ω₀, ω₁} : Finset (Choice (D.CL.T L))), varJ0 D L A ω (envM D L ω) := by
    rw [sum_pair hne, card_pair hne]
    have e : (Cm * bt - (e + k * (z₂ + δ) * Cm * 1) / (1 - k) -
          ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * (z₂ + δ) * Cm * Cr (pat g)) /
            (1 - k))) * Y = (Cm * bt - zb) * Y - rt * κ' := by
      have : (Cm * bt - (e + k * (z₂ + δ) * Cm * 1) / (1 - k) -
          ∑ g ∈ Zs, setCoeff coef g * ((er (pat g) + k * (z₂ + δ) * Cm * Cr (pat g)) /
            (1 - k))) = Cm * bt - (zb + δ * κ') := by
        rw [← hsplit]
        ring
      rw [this, ← hδY]
      ring
    rw [e] at hdisp
    push_cast
    linarith
  -- `hres_of_average` with the remainder, through `JO + r/2`
  have hJO : ∀ ω ∈ ({ω₀, ω₁} : Finset (Choice (D.CL.T L))),
      monomial (D.CL.πt L) ω = γ₀ := fun ω hω => by
    rcases mem_insert.mp hω with h | h
    · rw [h]; exact hγ₀
    · rw [mem_singleton.mp h]; exact hγ₁
  have hres := hres_of_average (γ₀ := γ₀) (C₀ := CX) ({ω₀, ω₁} : Finset (Choice (D.CL.T L)))
    (fun ω => monomial (D.CL.πt L) ω) (fun ω => selProd D L ω)
    (fun ω => varJ0 D L A ω (envM D L ω) + rt * κ') hJO
    (fun ω hω => by
      rcases mem_insert.mp hω with h | h
      · rw [h, selProd, hX₀]; exact hCX
      · rw [mem_singleton.mp h, selProd, hX₁]; exact hCX)
    (by rw [← hγ₀]; exact monomial_πt_nonneg L ω₀) hCX1 hCm hbt0 hzb0 hz hY.le
    (by
      rw [sum_add_distrib, sum_const, card_pair hne]
      rw [card_pair hne] at hdisp2
      simp only [nsmul_eq_mul]
      push_cast at hdisp2 ⊢
      linarith)
  have hs2 : ∑ ω ∈ ({ω₀, ω₁} : Finset (Choice (D.CL.T L))),
      monomial (D.CL.πt L) ω * (varJ0 D L A ω (envM D L ω) + rt * κ') =
      ∑ ω ∈ ({ω₀, ω₁} : Finset (Choice (D.CL.T L))),
        monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω) + γ₀ * (2 * rt * κ') := by
    rw [sum_pair hne, sum_pair hne, hγ₀, hγ₁]
    ring
  rw [hs2] at hres
  rw [hκ'] at hres
  linarith

end Sarkozy.OpsVariance
