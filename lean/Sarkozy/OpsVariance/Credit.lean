module

public import Sarkozy.OpsVariance.Restoration
public import Sarkozy.OpsVariance.Comparison

@[expose] public section

/-!
# The class-cost step of a credit class from its record data

`paper/sections/22_variance.tex`, `lem:var-gain`(a),(b), `cor:var-classes`(i),(ii),
`prop:background-variance`(b); `paper/sections/10_comparison_lemmas.tex`,
`lem:record:variance-interface`, (E1), (E2), (P3), (P4), `lem:bracket-energy`.

**`varStepsAt_of_records`** assembles `varStepsAt_credit` (`Steps.lean`), `hres_of_restoration`
(`Restoration.lean`) and `hJN_of_coupled` (`Comparison.lean`): for a nonempty class `R` of
selections with common support `X` and common price `π̃_ω = γ₀` (the hypothesis of
`lem:var-gain`), B10's `VarStepsAt` holds with the gain `b̃ = l̄ = (l₀/C − κ)/(1 − κ)` (W1's
`gainBar`) and the class cost `B − [l̄ − R_*]_+`, from:

* `hz0`: the selected record changes annihilate the constants (`eq:record:zero-marginal`; R);
* `hEnv`: (E1) for the envelopes with `Ñ` outside (`lem:bracket-energy`; R, proved at the paper's
  data, `envelopeBoundNonneg_ec`);
* `hE1μ`: (E1) for the selected diagonals with `μ` outside (`lem:bracket-energy`, first display;
  R, proved at the paper's data, `e1mu_front`);
* `w`, `hw`, `hp`, `hn`, `ht`: the eligible record laws, with the half marginals of the norm
  envelopes (`def:record:eligible`, `def:cp4`(b); R);
* `hcen`: (Cen) `‖T − 𝒥‖ ≤ κ < 1` (`lem:record:old-f-marginal`(d),
  `lem:record:paired-e-bridge`(b); R);
* `hRes`: (Res) `∑_R Y[⊗_X Π ⊗ μ] ≥ (l₀ − z₁)|R| Y` (`lem:record:restoration`,
  `lem:record:paired-e-joint`(b); C);
* `hterm`: the coupled terms of `J_X` (`lem:sharp-first`, `lem:density:coupled`; C, as EC's
  `E1Coup` for the envelopes);
* `hρ`, `hrr`, `hWZ`, `K ≥ 3`: the residual and the remainder budget (evaluation).

`varStepsAt_of_records_canon` is the same with the coupled terms at their canonical remainders
(`hJN_canonical`): no `hterm`; their content is the budget `hrr`.

This covers the fold classes (`prop:background-variance`(b), `cor:var-classes`(i)) and the aligned
matching classes with the selected term only (`cor:var-classes`(ii)); the background terms of
`prop:background-variance`(a) would raise `b̃` further.
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
/-- **The class-cost step of a credit class from its record data** (`lem:var-gain`(a),(b) at the
paper's objects): see the module docstring for the inputs. The gain is `l̄ = gainBar l₀ C κ`, the
remainders `r_J(ω) = ∑_σ r_σ(ω)` and `r₀ = γ₀ κ/(1 − κ) ∑_R r_μ`. -/
theorem varStepsAt_of_records {L : ℕ} {A : Finset ℤ} (R : Finset (Choice (D.CL.T L)))
    (hR : R.Nonempty) (hsel : ∀ ω ∈ R, IsSelection ω) (X : Finset (BlockAtom Bk J L))
    (hX : ∀ ω ∈ R, Choice.support ω = X) {γ₀ : ℝ} (hγ : ∀ ω ∈ R, monomial (D.CL.πt L) ω = γ₀)
    (ρ rr rD rμ : Choice (D.CL.T L) → ℝ) {WZ z K : ℝ} (hY : 0 ≤ D.Y L A)
    -- `eq:record:zero-marginal`
    (hz0 : ∀ ω ∈ R, RecordsZeroMarginal D L ω)
    -- (E1), `Ñ` outside, for the envelopes
    (hEnv : ∀ ω ∈ R, envEnergy D L A ω ≤ (D.B + z) * selProd D L ω * D.Y L A + rD ω)
    -- (E1), `μ` outside, for the selected diagonals
    {z₂ : ℝ} (hz₂ : 0 ≤ z₂) (hrμ : ∀ ω ∈ R, 0 ≤ rμ ω)
    (hE1μ : ∀ ω ∈ R, diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) X X
        (envM D L ω))) (blockLift m₀ blk p L A) ≤
      (1 + z₂) * (∏ b ∈ X, selectionFactor a p D.S.selPre L b) * D.Y L A + rμ ω)
    -- the eligible record laws and (Cen)
    (w : Choice (D.CL.T L) → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (hw : ∀ ω ∈ R, ∀ b ∈ X, ∀ z, 0 ≤ w ω b z)
    (hp : ∀ ω ∈ R, ∀ b ∈ X, plusMarginal reservedCut (w ω b) = envM D L ω b)
    (hn : ∀ ω ∈ R, ∀ b ∈ X, minusMarginal reservedCut (w ω b) = envM D L ω b)
    (ht : ∀ ω ∈ R, ∀ b ∈ X, ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ,
      reservedCut.form (signedIntegral (w ω b)) G H = reservedCut.form (signedIntegral (w ω b)) H G)
    (κj : Choice (D.CL.T L) → BlockAtom Bk J L → ℝ)
    (hcen : ∀ ω ∈ R, ∀ b ∈ X,
      CentredNormLe reservedCut (signedIntegral (w ω b)) (envM D L ω b) (κj ω b))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ ω ∈ R, ∀ b ∈ X, κj ω b ≤ κ)
    -- (Res)
    {C l₀ z₁ : ℝ} (hCX : 1 ≤ ∏ b ∈ X, selectionFactor a p D.S.selPre L b)
    (hC : ∏ b ∈ X, selectionFactor a p D.S.selPre L b ≤ C) (hz₁ : 0 ≤ z₁)
    (hzR : (z₁ + κ * z₂) / (1 - κ) ≤ z)
    (hRes : (l₀ - z₁) * D.Y L A * R.card ≤ ∑ ω ∈ R,
      diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X (w ω) (envM D L ω)))
        (blockLift m₀ blk p L A))
    -- the coupled terms of `J_X`
    {ε : ℝ} (hε : 0 ≤ ε) (hzε : D.GB.Rerr * ε ≤ z)
    (rσ : Choice (D.CL.T L) → (∀ b, Option (D.FS.Ib L b)) → ℝ) (hrσ : ∀ ω σ, 0 ≤ rσ ω σ)
    (hterm : ∀ ω ∈ R, ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      |diagonalIntegral (tensorLaw (jPiece D L ω (envM D L ω) σ)) (blockLift m₀ blk p L A)| ≤
        (1 + ε) * selProd D L ω * D.Y L A *
          tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (outPrice D L ω) j σ + rσ ω σ)
    -- the evaluations
    (Rstar : ℝ) (hRs : D.GB.Rerr ≤ Rstar) (hWZ : 0 ≤ WZ)
    (hρ : ∀ ω ∈ R, (D.B - max 0 (gainBar l₀ C κ - Rstar)) * monomial (D.CL.π L) ω ≤ ρ ω)
    (hK : 3 ≤ K)
    (hrr : ∑ ω ∈ R, monomial (D.CL.πt L) ω * (rD ω + ∑ σ ∈ univ.filter
        (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), rσ ω σ) +
        γ₀ * (κ / (1 - κ)) * ∑ ω ∈ R, rμ ω ≤ ∑ ω ∈ R, rr ω) :
    Nonempty (VarStepsAt R (termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) ρ rr WZ
      (D.Y L A) z K) := by
  have h1κ : 0 < 1 - κ := by linarith
  have hγ₀ : 0 ≤ γ₀ := by
    obtain ⟨ω, hω⟩ := hR
    rw [← hγ ω hω]
    exact monomial_πt_nonneg L ω
  have hres := hres_of_restoration R hR X hX hγ w hw hp hn ht κj hcen hκ0 hκ1 hκ rμ hrμ hY hCX hC
    hz₁ hz₂ hzR hRes hE1μ
  exact varStepsAt_credit R hsel ρ rr rD
    (fun ω => ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rσ ω σ)
    (γ₀ * (κ / (1 - κ)) * ∑ ω ∈ R, rμ ω) Rstar (gainBar l₀ C κ)
    (mul_nonneg (mul_nonneg hγ₀ (div_nonneg hκ0 h1κ.le)) (sum_nonneg hrμ))
    (fun ω _ => sum_nonneg fun σ _ => hrσ ω σ) hRs hz0 hEnv
    (fun ω hω => hJN_of_coupled L A ω (envM D L ω) hε hzε hY (rσ ω) (hterm ω hω))
    hres hWZ hρ hK hrr

omit [DecidableEq P] in
/-- **`varStepsAt_of_records` at the canonical remainders of the coupled terms** (`hJN_canonical`):
no `hterm`; the remainders `r_J(ω) = ∑_{σ ≠ ∅} jExcess(ω, σ)` enter the budget `hrr`. -/
theorem varStepsAt_of_records_canon {L : ℕ} {A : Finset ℤ} (R : Finset (Choice (D.CL.T L)))
    (hR : R.Nonempty) (hsel : ∀ ω ∈ R, IsSelection ω) (X : Finset (BlockAtom Bk J L))
    (hX : ∀ ω ∈ R, Choice.support ω = X) {γ₀ : ℝ} (hγ : ∀ ω ∈ R, monomial (D.CL.πt L) ω = γ₀)
    (ρ rr rD rμ : Choice (D.CL.T L) → ℝ) {WZ z K : ℝ} (hY : 0 ≤ D.Y L A)
    -- `eq:record:zero-marginal`
    (hz0 : ∀ ω ∈ R, RecordsZeroMarginal D L ω)
    -- (E1), `Ñ` outside, for the envelopes
    (hEnv : ∀ ω ∈ R, envEnergy D L A ω ≤ (D.B + z) * selProd D L ω * D.Y L A + rD ω)
    -- (E1), `μ` outside, for the selected diagonals
    {z₂ : ℝ} (hz₂ : 0 ≤ z₂) (hrμ : ∀ ω ∈ R, 0 ≤ rμ ω)
    (hE1μ : ∀ ω ∈ R, diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) X X
        (envM D L ω))) (blockLift m₀ blk p L A) ≤
      (1 + z₂) * (∏ b ∈ X, selectionFactor a p D.S.selPre L b) * D.Y L A + rμ ω)
    -- the eligible record laws and (Cen)
    (w : Choice (D.CL.T L) → ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (hw : ∀ ω ∈ R, ∀ b ∈ X, ∀ z, 0 ≤ w ω b z)
    (hp : ∀ ω ∈ R, ∀ b ∈ X, plusMarginal reservedCut (w ω b) = envM D L ω b)
    (hn : ∀ ω ∈ R, ∀ b ∈ X, minusMarginal reservedCut (w ω b) = envM D L ω b)
    (ht : ∀ ω ∈ R, ∀ b ∈ X, ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ,
      reservedCut.form (signedIntegral (w ω b)) G H = reservedCut.form (signedIntegral (w ω b)) H G)
    (κj : Choice (D.CL.T L) → BlockAtom Bk J L → ℝ)
    (hcen : ∀ ω ∈ R, ∀ b ∈ X,
      CentredNormLe reservedCut (signedIntegral (w ω b)) (envM D L ω b) (κj ω b))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ ω ∈ R, ∀ b ∈ X, κj ω b ≤ κ)
    -- (Res)
    {C l₀ z₁ : ℝ} (hCX : 1 ≤ ∏ b ∈ X, selectionFactor a p D.S.selPre L b)
    (hC : ∏ b ∈ X, selectionFactor a p D.S.selPre L b ≤ C) (hz₁ : 0 ≤ z₁)
    (hzR : (z₁ + κ * z₂) / (1 - κ) ≤ z)
    (hRes : (l₀ - z₁) * D.Y L A * R.card ≤ ∑ ω ∈ R,
      diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X (w ω) (envM D L ω)))
        (blockLift m₀ blk p L A))
    -- the coupled terms of `J_X`, at their canonical remainders
    {ε : ℝ} (hε : 0 ≤ ε) (hzε : D.GB.Rerr * ε ≤ z)
    -- the evaluations
    (Rstar : ℝ) (hRs : D.GB.Rerr ≤ Rstar) (hWZ : 0 ≤ WZ)
    (hρ : ∀ ω ∈ R, (D.B - max 0 (gainBar l₀ C κ - Rstar)) * monomial (D.CL.π L) ω ≤ ρ ω)
    (hK : 3 ≤ K)
    (hrr : ∑ ω ∈ R, monomial (D.CL.πt L) ω * (rD ω + ∑ σ ∈ univ.filter
        (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          jExcess D L A ω (envM D L ω) ε σ) +
        γ₀ * (κ / (1 - κ)) * ∑ ω ∈ R, rμ ω ≤ ∑ ω ∈ R, rr ω) :
    Nonempty (VarStepsAt R (termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) ρ rr WZ
      (D.Y L A) z K) :=
  varStepsAt_of_records R hR hsel X hX hγ ρ rr rD rμ hY hz0 hEnv hz₂ hrμ hE1μ w hw hp hn ht κj hcen
    hκ0 hκ1 hκ hCX hC hz₁ hzR hRes hε hzε (fun ω => jExcess D L A ω (envM D L ω) ε)
    (fun ω σ => jExcess_nonneg L A ω (envM D L ω) ε σ)
    (fun ω _ σ _ j _ => hterm_jExcess L A ω (envM D L ω) ε σ j) Rstar hRs hWZ hρ hK hrr

end Sarkozy.OpsVariance
