module

public import Sarkozy.DensityChain2.Fields
public import Sarkozy.DensityFibre.All

@[expose] public section

/-!
# The folded energies of `lem:sharp-first` on the paper's tail: the chain inputs discharged

DC2's baseline route to the four `hdiff` fields (`DensityFibre.env/fixHdiffL/R_of_folded`) takes a
per-choice input `hfold`: bounds of the two folded energies `𝔈_±` of every piece by a main price
plus a remainder. DC2's `env_fold_le_chain` bounds one folded energy by
`prop:record:density-structured` at the folded slot data `envSlots ∘ fo`, from the chain's inputs
`hrest`, `hun`, `hdc`, the slot conditions and `hatom`. Here, on the paper's tail, for a set `Es` of
selected atoms with `D_{Es} ≠ 1` and positive-record laws:

* `hrest` is `envFoldHrest_paper` (restoration, `lem:record:fibre-scale`(c));
* `hdc` is DC1's `DCBlockProp` (`lem:record:density-dc`, signed form) at the folded slot data;
* every slot is changed (`D₀ D_{Es} ≠ 1`), so `hun` is vacuous;
* the slot conditions (`D₀ ∣ M₀`, coprime to the moduli, `M ∈ {N, L}`) hold at every slot of the
  folded data, as at the unfolded data;
* `Y(L, ∅) = 0` (DC1's `dataY_empty`).

**`env_fold_chain_paper`**, **`fix_fold_chain_paper`**: what remains of one folded energy's bound
is the modulus conditions on `D_{Es}` (`def:record:structured-energy`(a); `Factorization` and DC1's
`moduli_dichotomy` give them when `q_{Es} ≤ N^τ`, and `lem:record:density-lp` covers the other
case) and `hatom` (at `θ = 1`, DC2's `hatom_fold_one`). The price matching at the folded data
(`Price`, `PiecePrice`) and the assembly of `hfold` (`FoldedPieces`, `HfoldAlgebra`, `Hfold`)
follow.
-/

namespace Sarkozy.DensityChain2

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] [Fintype Bk] in
/-- The selected weight of positive-record laws has uniform selected marginals (condition (b)
of `def:record:structured-energy`). -/
theorem hsel_of_positive_laws {L : ℕ} (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Λ : ∀ b : BlockAtom Bk PaperJt L, ((Slot → BlockLabel m₀ blk paperTail L b) → ℝ) →ₗ[ℝ] ℝ)
    (Es : Finset (BlockAtom Bk PaperJt L)) (hΛ : ∀ b ∈ Es, IsPositiveRecord (Λ b)) :
    selectedMarginalsUniform (selectedWeight Es (crtLaws blk h0 L Λ)) := by
  unfold selectedWeight
  apply selectedMarginalsUniform_prod
    (fun b : {b // b ∈ Es} => lawDensity (crtLaws blk h0 L Λ b.1))
  intro b
  apply selectedMarginalsUniform_lawDensity
  unfold crtLaws
  exact isPositiveRecord_pullLaw _ (hΛ b.1 b.2)


/-- **One folded `envC` energy on the paper's tail** (`prop:record:density-structured` for a
folded energy, `lem:record:folded-energy`, `lem:sharp-first`): DC2's `env_fold_le_chain` with
`hrest` (restoration), `hdc` (`lem:record:density-dc` from DC1's `DCBlockProp`), `hun` (vacuous:
every slot is changed since `D_{Es} ≠ 1`) and the slot conditions discharged. Remaining: the
modulus conditions on `D_{Es}` and `hatom`. -/
theorem env_fold_chain_paper {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (Λ : ∀ b : BlockAtom Bk PaperJt L, ((Slot → BlockLabel m₀ blk paperTail L b) → ℝ) →ₗ[ℝ] ℝ)
    (Es : Finset (BlockAtom Bk PaperJt L)) (hE : ∀ b ∉ Es, Λ b = D.R.law paperTail L b)
    (hΛ : ∀ b ∈ Es, IsPositiveRecord (Λ b))
    (hne : ∏ j ∈ Es, crtModuli m₀ blk paperTail L j ≠ 1)
    {qE cE : ℕ} (hDE : ∏ b ∈ Es, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (u : E → reservedCut.Half) (fo : Slot → Slot)
    {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (hatom : ∀ b ∈ Es, ∀ hb : 0 < totalVariation (lawDensity (Λ b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L Λ))
        (fun v => pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω
          (fo v))| ≤
      (∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (Λ b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) Es
              (fun v => (envSlots hcop u L Jq ω (fo v)).1)
              (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop u L Jq ω (fo v)).1)
              (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1)
              (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.2.2)
              (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.1))
            (fun _ => True) a' θ (density (blockScale * L) A) * D.Y L A +
          dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hD0 : ∀ v, 1 ≤ (envSlots hcop u L Jq ω (fo v)).1 := by
    intro v
    rw [envSlots_fst hcop u L Jq ω (fo v)]
    unfold envD0
    split
    · exact Nat.pos_of_dvd_of_pos (revealedModulus_dvd _) hmpos
    · exact le_refl 1
  have hD0M : ∀ v, (envSlots hcop u L Jq ω (fo v)).1 ∣ M0 := by
    intro v
    rw [envSlots_fst hcop u L Jq ω (fo v)]
    unfold envD0
    split
    · exact dvd_trans (revealedModulus_dvd _) hMod
    · exact one_dvd _
  have hcop0 : ∀ v k, ((envSlots hcop u L Jq ω (fo v)).1).Coprime
      (crtModuli m₀ blk paperTail L k) := by
    intro v k
    rw [envSlots_fst hcop u L Jq ω (fo v)]
    unfold envD0
    split
    · exact Nat.Coprime.coprime_dvd_left (revealedModulus_dvd _) (hcopM_of_data D L k)
    · exact Nat.coprime_one_left _
  have hM : ∀ v, (envSlots hcop u L Jq ω (fo v)).2.2.1 = blockScale * L ∨
      (envSlots hcop u L Jq ω (fo v)).2.2.1 = L := by
    intro v
    rw [envSlots_len hcop u L Jq ω (fo v)]
    unfold envM
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hchg : ∀ v, (fun _ : Slot => True) v → ¬((envSlots hcop u L Jq ω (fo v)).1 *
      ∏ j ∈ Es, crtModuli m₀ blk paperTail L j = 1 ∧
      (envSlots hcop u L Jq ω (fo v)).2.2.1 = blockScale * L) :=
    fun v _ h1 => hne (Nat.dvd_one.mp ⟨_, by rw [mul_comm] at h1; exact h1.1.symm⟩)
  have h0 := prefix_pairwise (hpair L)
  have hdc := hdcb blk paperTail D.R (A := A) (hpair L) (D.S.p_prime L) (D.S.p_inj L) hL hsc hM0 Es
    hDE hqE
    hcE hcE0 hcQ hcopE hqN (FiniteLaw.uniform Unit) _
    (selectedMarginalsUniform_liftWeight_uniform Es _ (hsel_of_positive_laws h0 Λ Es hΛ))
    (fun v => (envSlots hcop u L Jq ω (fo v)).1) hD0 hD0M hcop0
    (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1) hM
    (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.2.2)
    (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.1)
    (fun _ => True)
    (fun _ => revealedModel (crtModuli m₀ blk paperTail L) Es A
      (fun v => (envSlots hcop u L Jq ω (fo v)).1)
      (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1)
      (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.2)
      (fun v => (envSlots hcop u L Jq ω (fo v)).2.1)
      (fun v => paperCutoff (blockScale * stepEll (crtModuli m₀ blk paperTail L) Es
        (envSlots hcop u L Jq ω (fo v)).1 (envSlots hcop u L Jq ω (fo v)).2.2.1)))
    (fun _ v x _ => by
      funext y
      simp only [revealedModel])
    (fun v hv => absurd trivial hv) hσ hS1
  rw [totalVariation_liftWeight] at hdc
  exact DensityFibre.env_fold_le_chain hcop D (hpair L) hcex hθ hθ2 ha hC0 hL
    (le_of_eq (dataY_empty D L)) hsc hM0 Λ Es hE hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ ω u fo hD0
    hD0M hcop0 hM (fun _ => True) hchg _ (fun v hv => absurd trivial hv)
    (fun v _ B hB => envFoldHrest_paper hcop D hpair u L Jq ω fo Es v B hB) hdc hatom

/-- **One folded `fixC` energy on the paper's tail** (`prop:record:density-structured` for a
folded energy, `lem:record:folded-energy`, `lem:sharp-first`): DC2's `fix_fold_le_chain` with
`hrest` (restoration), `hdc` (`lem:record:density-dc` from DC1's `DCBlockProp`), `hun` (vacuous:
every slot is changed since `D_{Es} ≠ 1`) and the slot conditions discharged. Remaining: the
modulus conditions on `D_{Es}` and `hatom`. -/
theorem fix_fold_chain_paper {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (Λ : ∀ b : BlockAtom Bk PaperJt L, ((Slot → BlockLabel m₀ blk paperTail L b) → ℝ) →ₗ[ℝ] ℝ)
    (Es : Finset (BlockAtom Bk PaperJt L)) (hE : ∀ b ∉ Es, Λ b = D.R.law paperTail L b)
    (hΛ : ∀ b ∈ Es, IsPositiveRecord (Λ b))
    (hne : ∏ j ∈ Es, crtModuli m₀ blk paperTail L j ≠ 1)
    {qE cE : ℕ} (hDE : ∏ b ∈ Es, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (u : E → reservedCut.Half) (fo : Slot → Slot)
    {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (hatom : ∀ b ∈ Es, ∀ hb : 0 < totalVariation (lawDensity (Λ b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L Λ))
        (fun v => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω
          (fo v))| ≤
      (∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (Λ b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) Es
              (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)
              (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.2)
              (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.1))
            (fun _ => True) a' θ (density (blockScale * L) A) * D.Y L A +
          dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hD0 : ∀ v, 1 ≤ (fixSlots hcop u L S t Jq ω (fo v)).1 := by
    intro v
    rw [fixSlots_fst hcop u L S t Jq ω (fo v)]
    unfold fixD0
    split
    · split_ifs
      · exact Nat.pos_of_dvd_of_pos (revealedModulus_dvd _) hmpos
      · exact le_refl 1
    · exact le_refl 1
  have hD0M : ∀ v, (fixSlots hcop u L S t Jq ω (fo v)).1 ∣ M0 := by
    intro v
    rw [fixSlots_fst hcop u L S t Jq ω (fo v)]
    unfold fixD0
    split
    · split_ifs
      · exact dvd_trans (revealedModulus_dvd _) hMod
      · exact one_dvd _
    · exact one_dvd _
  have hcop0 : ∀ v k, ((fixSlots hcop u L S t Jq ω (fo v)).1).Coprime
      (crtModuli m₀ blk paperTail L k) := by
    intro v k
    rw [fixSlots_fst hcop u L S t Jq ω (fo v)]
    unfold fixD0
    split
    · split_ifs
      · exact Nat.Coprime.coprime_dvd_left (revealedModulus_dvd _) (hcopM_of_data D L k)
      · exact Nat.coprime_one_left _
    · exact Nat.coprime_one_left _
  have hM : ∀ v, (fixSlots hcop u L S t Jq ω (fo v)).2.2.1 = blockScale * L ∨
      (fixSlots hcop u L S t Jq ω (fo v)).2.2.1 = L := by
    intro v
    rw [fixSlots_len hcop u L S t Jq ω (fo v)]
    unfold fixM
    split
    · split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact Or.inl rfl
  have hchg : ∀ v, (fun _ : Slot => True) v → ¬((fixSlots hcop u L S t Jq ω (fo v)).1 *
      ∏ j ∈ Es, crtModuli m₀ blk paperTail L j = 1 ∧
      (fixSlots hcop u L S t Jq ω (fo v)).2.2.1 = blockScale * L) :=
    fun v _ h1 => hne (Nat.dvd_one.mp ⟨_, by rw [mul_comm] at h1; exact h1.1.symm⟩)
  have h0 := prefix_pairwise (hpair L)
  have hdc := hdcb blk paperTail D.R (A := A) (hpair L) (D.S.p_prime L) (D.S.p_inj L) hL hsc hM0 Es
    hDE hqE
    hcE hcE0 hcQ hcopE hqN (FiniteLaw.uniform Unit) _
    (selectedMarginalsUniform_liftWeight_uniform Es _ (hsel_of_positive_laws h0 Λ Es hΛ))
    (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1) hD0 hD0M hcop0
    (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1) hM
    (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.2)
    (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.1)
    (fun _ => True)
    (fun _ => revealedModel (crtModuli m₀ blk paperTail L) Es A
      (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
      (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)
      (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.2)
      (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.1)
      (fun v => paperCutoff (blockScale * stepEll (crtModuli m₀ blk paperTail L) Es
        (fixSlots hcop u L S t Jq ω (fo v)).1 (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)))
    (fun _ v x _ => by
      funext y
      simp only [revealedModel])
    (fun v hv => absurd trivial hv) hσ hS1
  rw [totalVariation_liftWeight] at hdc
  exact DensityFibre.fix_fold_le_chain hcop D (hpair L) hcex hθ hθ2 ha hC0 hL
    (le_of_eq (dataY_empty D L)) hsc hM0 Λ Es hE hDE hqE hcE hcE0 hcQ hcopE hqN S t Jq ω u fo hD0
    hD0M hcop0 hM (fun _ => True) hchg _ (fun v hv => absurd trivial hv)
    (fun v _ B hB => fixFoldHrest_paper hcop D hpair u L S t Jq ω fo Es v B hB) hdc hatom

omit [DecidableEq P] in
/-- **The modulus conditions of any set of block atoms on the paper's tail**
(`def:record:structured-energy`(a) against `lem:record:density-lp`): with the parity condition,
either `D_{Es} = q_{Es} c_{Es}` with `q_{Es}` squarefree, `c_{Es}` a nonzero square coprime to it,
`c_{Es} ≤ Q_cl` and `q_{Es} ≤ T`, or `T < q_{Es}` (DC1's `moduli_dichotomy` with `atomQ`,
`atomC`). These are the modulus inputs of `env/fix_fold_chain_paper` and of DC1's chain. -/
theorem moduli_paper (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hpar : ParityCondition D.S.ep) {Qcl : ℕ} (hQcl : cliqueConstant m₀ D.S.ep ≤ Qcl) (L : ℕ)
    (T : ℝ) (Es : Finset (BlockAtom Bk PaperJt L)) :
    (∃ qE cE : ℕ, ∏ b ∈ Es, crtModuli m₀ blk paperTail L b = qE * cE ∧ Squarefree qE ∧
      IsSquare cE ∧ cE ≠ 0 ∧ cE ≤ Qcl ∧ qE.Coprime cE ∧ (qE : ℝ) ≤ T) ∨
      T < ∏ b, ((if b ∈ Es then atomQ blk paperTail D.S.pp D.S.ep L b else 1 : ℕ) : ℝ) := by
  have h0 := prefix_pairwise (hpair 0)
  exact moduli_dichotomy (crtModuli m₀ blk paperTail L) (atomQ blk paperTail D.S.pp D.S.ep L)
    (atomC m₀ blk D.S.ep L) (crtModuli_eq_atomQ_mul_atomC D.S.m₀_eq L)
    (squarefree_atomQ D.S.m₀_eq D.S.pp_prime D.S.ep_pos h0 D.S.p_prime L)
    (isSquare_atomC D.S.m₀_eq hpar L) (atomC_ne_zero D.S.ep L)
    (coprime_atomQ_atomC D.S.m₀_eq D.S.ep_pos h0 L) (crtModuli_pairwise blk (hpair L))
    ((prod_atomC_eq D.S.ep L).trans_le hQcl) T Es

omit [DecidableEq P] in
/-- `D_{Es} ≠ 1` for a nonempty set of atoms when every block is nonempty. -/
theorem prod_crtModuli_ne_one (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hne : ∀ β, ∃ i, blk i = β) {L : ℕ} {Es : Finset (BlockAtom Bk PaperJt L)}
    (hEs : Es.Nonempty) : ∏ b ∈ Es, crtModuli m₀ blk paperTail L b ≠ 1 :=
  prod_ne_one_of_nonempty _ (two_le_crtModuli D.S.m₀_eq D.S.pp_prime D.S.ep_pos hne
    D.S.p_prime L) hEs

/-- **One plus folded energy of DC2's baseline pieces on the paper's tail**
(`lem:record:folded-energy`, `prop:record:density-structured` for a folded energy,
`lem:sharp-first`): for a piece `φ` of DC2's choice expansion at the tag `j` with selected atoms
`hTermAtoms φ` (the non-`μ` pieces), the plus folded energy of `envC` that DC2's `hfold` bounds
satisfies the chain bound. The folded laws are positive records off `μ` (DC2's
`bpieceLp_positiveRecord`) and equal `μ` at the `μ`-pieces, and `env_fold_chain_paper` applies at
the fold map `φ₊` of the cut `c_j` (`foldedPlus_eq_crt`). Remaining: the modulus conditions and
`hatom` for the folded laws. -/
theorem env_foldPlus_piece_paper {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag)
    (φ : ∀ b, DensityFibre.HPiece D L b)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L Qb dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |EnvelopeInputs.foldedPlus (D.FS.cut j) (DensityFibre.bpieceLp D L Qb dec j)
        (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| ≤
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L Qb dec j b.1 (φ b.1)) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) (DensityFibre.hTermAtoms D L φ)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1)
              (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.2.2)
              (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.1))
            (fun _ => True) a' θ (density (blockScale * L) A) * D.Y L A +
          dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  rw [DensityFibre.foldedPlus_eq_crt blk (prefix_pairwise (hpair L)) (D.FS.cut j)
    (DensityFibre.bpieceLp D L Qb dec j)
    (fun v => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
      (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v) φ]
  have hE : ∀ b ∉ DensityFibre.hTermAtoms D L φ,
      DensityFibre.bpieceLp D L Qb dec j b (φ b) = D.R.law paperTail L b := by
    intro b hb
    unfold DensityFibre.hTermAtoms at hb
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_false] at hb
    revert hb
    rcases φ b with (_ | k) | (⟨i, _ | t⟩ | _) <;> intro hb <;>
      simp_all [DensityFibre.hpieceIsMu, DensityFibre.bpieceLp]
  have hΛ : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      IsPositiveRecord (DensityFibre.bpieceLp D L Qb dec j b (φ b)) := by
    intro b hb
    exact DensityFibre.bpieceLp_positiveRecord D L Qb dec hQ j b (φ b) (mem_filter.mp hb).2
  exact env_fold_chain_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (fun b => DensityFibre.bpieceLp D L Qb dec j b (φ b)) (DensityFibre.hTermAtoms D L φ) hE hΛ
    hne hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ ω D.index.u (D.FS.cut j).foldPlus hσ hS1 hatom

/-- **One minus folded energy of DC2's baseline pieces on the paper's tail**
(`lem:record:folded-energy`, `prop:record:density-structured` for a folded energy,
`lem:sharp-first`): for a piece `φ` of DC2's choice expansion at the tag `j` with selected atoms
`hTermAtoms φ` (the non-`μ` pieces), the minus folded energy of `envC` that DC2's `hfold` bounds
satisfies the chain bound. The folded laws are positive records off `μ` (DC2's
`bpieceLm_positiveRecord`) and equal `μ` at the `μ`-pieces, and `env_fold_chain_paper` applies at
the fold map `φ₋` of the cut `c_j` (`foldedMinus_eq_crt`). Remaining: the modulus conditions and
`hatom` for the folded laws. -/
theorem env_foldMinus_piece_paper {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag)
    (φ : ∀ b, DensityFibre.HPiece D L b)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L Qb dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |EnvelopeInputs.foldedMinus (D.FS.cut j) (DensityFibre.bpieceLm D L Qb dec j)
        (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| ≤
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L Qb dec j b.1 (φ b.1)) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) (DensityFibre.hTermAtoms D L φ)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1)
              (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.2.2)
              (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.1))
            (fun _ => True) a' θ (density (blockScale * L) A) * D.Y L A +
          dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  rw [DensityFibre.foldedMinus_eq_crt blk (prefix_pairwise (hpair L)) (D.FS.cut j)
    (DensityFibre.bpieceLm D L Qb dec j)
    (fun v => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
      (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v) φ]
  have hE : ∀ b ∉ DensityFibre.hTermAtoms D L φ,
      DensityFibre.bpieceLm D L Qb dec j b (φ b) = D.R.law paperTail L b := by
    intro b hb
    unfold DensityFibre.hTermAtoms at hb
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_false] at hb
    revert hb
    rcases φ b with (_ | k) | (⟨i, _ | t⟩ | _) <;> intro hb <;>
      simp_all [DensityFibre.hpieceIsMu, DensityFibre.bpieceLm]
  have hΛ : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      IsPositiveRecord (DensityFibre.bpieceLm D L Qb dec j b (φ b)) := by
    intro b hb
    exact DensityFibre.bpieceLm_positiveRecord D L Qb dec hQ j b (φ b) (mem_filter.mp hb).2
  exact env_fold_chain_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (fun b => DensityFibre.bpieceLm D L Qb dec j b (φ b)) (DensityFibre.hTermAtoms D L φ) hE hΛ
    hne hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ ω D.index.u (D.FS.cut j).foldMinus hσ hS1 hatom

/-- **One plus folded energy of DC2's baseline pieces on the paper's tail**
(`lem:record:folded-energy`, `prop:record:density-structured` for a folded energy,
`lem:sharp-first`): for a piece `φ` of DC2's choice expansion at the tag `j` with selected atoms
`hTermAtoms φ` (the non-`μ` pieces), the plus folded energy of `fixC` that DC2's `hfold` bounds
satisfies the chain bound. The folded laws are positive records off `μ` (DC2's
`bpieceLp_positiveRecord`) and equal `μ` at the `μ`-pieces, and `fix_fold_chain_paper` applies at
the fold map `φ₊` of the cut `c_j` (`foldedPlus_eq_crt`). Remaining: the modulus conditions and
`hatom` for the folded laws. -/
theorem fix_foldPlus_piece_paper {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag)
    (φ : ∀ b, DensityFibre.HPiece D L b)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (u : E → reservedCut.Half) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L Qb dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |EnvelopeInputs.foldedPlus (D.FS.cut j) (DensityFibre.bpieceLp D L Qb dec j)
        (fun v x => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| ≤
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L Qb dec j b.1 (φ b.1)) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) (DensityFibre.hTermAtoms D L φ)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.2.1)
              (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.2.2)
              (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.1))
            (fun _ => True) a' θ (density (blockScale * L) A) * D.Y L A +
          dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  rw [DensityFibre.foldedPlus_eq_crt blk (prefix_pairwise (hpair L)) (D.FS.cut j)
    (DensityFibre.bpieceLp D L Qb dec j)
    (fun v => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v) φ]
  have hE : ∀ b ∉ DensityFibre.hTermAtoms D L φ,
      DensityFibre.bpieceLp D L Qb dec j b (φ b) = D.R.law paperTail L b := by
    intro b hb
    unfold DensityFibre.hTermAtoms at hb
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_false] at hb
    revert hb
    rcases φ b with (_ | k) | (⟨i, _ | t⟩ | _) <;> intro hb <;>
      simp_all [DensityFibre.hpieceIsMu, DensityFibre.bpieceLp]
  have hΛ : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      IsPositiveRecord (DensityFibre.bpieceLp D L Qb dec j b (φ b)) := by
    intro b hb
    exact DensityFibre.bpieceLp_positiveRecord D L Qb dec hQ j b (φ b) (mem_filter.mp hb).2
  exact fix_fold_chain_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (fun b => DensityFibre.bpieceLp D L Qb dec j b (φ b)) (DensityFibre.hTermAtoms D L φ) hE hΛ
    hne hDE hqE hcE hcE0 hcQ hcopE hqN S t Jq ω u (D.FS.cut j).foldPlus hσ hS1 hatom

/-- **One minus folded energy of DC2's baseline pieces on the paper's tail**
(`lem:record:folded-energy`, `prop:record:density-structured` for a folded energy,
`lem:sharp-first`): for a piece `φ` of DC2's choice expansion at the tag `j` with selected atoms
`hTermAtoms φ` (the non-`μ` pieces), the minus folded energy of `fixC` that DC2's `hfold` bounds
satisfies the chain bound. The folded laws are positive records off `μ` (DC2's
`bpieceLm_positiveRecord`) and equal `μ` at the `μ`-pieces, and `fix_fold_chain_paper` applies at
the fold map `φ₋` of the cut `c_j` (`foldedMinus_eq_crt`). Remaining: the modulus conditions and
`hatom` for the folded laws. -/
theorem fix_foldMinus_piece_paper {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag)
    (φ : ∀ b, DensityFibre.HPiece D L b)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (u : E → reservedCut.Half) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L Qb dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |EnvelopeInputs.foldedMinus (D.FS.cut j) (DensityFibre.bpieceLm D L Qb dec j)
        (fun v x => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| ≤
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L Qb dec j b.1 (φ b.1)) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) (DensityFibre.hTermAtoms D L φ)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.2.1)
              (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.2.2)
              (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.1))
            (fun _ => True) a' θ (density (blockScale * L) A) * D.Y L A +
          dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  rw [DensityFibre.foldedMinus_eq_crt blk (prefix_pairwise (hpair L)) (D.FS.cut j)
    (DensityFibre.bpieceLm D L Qb dec j)
    (fun v => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v) φ]
  have hE : ∀ b ∉ DensityFibre.hTermAtoms D L φ,
      DensityFibre.bpieceLm D L Qb dec j b (φ b) = D.R.law paperTail L b := by
    intro b hb
    unfold DensityFibre.hTermAtoms at hb
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_false] at hb
    revert hb
    rcases φ b with (_ | k) | (⟨i, _ | t⟩ | _) <;> intro hb <;>
      simp_all [DensityFibre.hpieceIsMu, DensityFibre.bpieceLm]
  have hΛ : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      IsPositiveRecord (DensityFibre.bpieceLm D L Qb dec j b (φ b)) := by
    intro b hb
    exact DensityFibre.bpieceLm_positiveRecord D L Qb dec hQ j b (φ b) (mem_filter.mp hb).2
  exact fix_fold_chain_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (fun b => DensityFibre.bpieceLm D L Qb dec j b (φ b)) (DensityFibre.hTermAtoms D L φ) hE hΛ
    hne hDE hqE hcE hcE0 hcQ hcopE hqN S t Jq ω u (D.FS.cut j).foldMinus hσ hS1 hatom

/-- **One plus folded energy of DC2's baseline pieces on the paper's tail**
(`lem:record:folded-energy`, `prop:record:density-structured` for a folded energy,
`lem:sharp-first`): for a piece `φ` of DC2's choice expansion at the tag `j` with selected atoms
`hTermAtoms φ` (the non-`μ` pieces), the plus folded energy of `envC` (right increments,
`D.index.w`) that DC2's `hfold` bounds
satisfies the chain bound. The folded laws are positive records off `μ` (DC2's
`bpieceLp_positiveRecord`) and equal `μ` at the `μ`-pieces, and `env_fold_chain_paper` applies at
the fold map `φ₊` of the cut `c_j` (`foldedPlus_eq_crt`). Remaining: the modulus conditions and
`hatom` for the folded laws. -/
theorem envR_foldPlus_piece_paper {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag)
    (φ : ∀ b, DensityFibre.HPiece D L b)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L Qb dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |EnvelopeInputs.foldedPlus (D.FS.cut j) (DensityFibre.bpieceLp D L Qb dec j)
        (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| ≤
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L Qb dec j b.1 (φ b.1)) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) (DensityFibre.hTermAtoms D L φ)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1)
              (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.2.2)
              (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.1))
            (fun _ => True) a' θ (density (blockScale * L) A) * D.Y L A +
          dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  rw [DensityFibre.foldedPlus_eq_crt blk (prefix_pairwise (hpair L)) (D.FS.cut j)
    (DensityFibre.bpieceLp D L Qb dec j)
    (fun v => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
      (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v) φ]
  have hE : ∀ b ∉ DensityFibre.hTermAtoms D L φ,
      DensityFibre.bpieceLp D L Qb dec j b (φ b) = D.R.law paperTail L b := by
    intro b hb
    unfold DensityFibre.hTermAtoms at hb
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_false] at hb
    revert hb
    rcases φ b with (_ | k) | (⟨i, _ | t⟩ | _) <;> intro hb <;>
      simp_all [DensityFibre.hpieceIsMu, DensityFibre.bpieceLp]
  have hΛ : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      IsPositiveRecord (DensityFibre.bpieceLp D L Qb dec j b (φ b)) := by
    intro b hb
    exact DensityFibre.bpieceLp_positiveRecord D L Qb dec hQ j b (φ b) (mem_filter.mp hb).2
  exact env_fold_chain_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (fun b => DensityFibre.bpieceLp D L Qb dec j b (φ b)) (DensityFibre.hTermAtoms D L φ) hE hΛ
    hne hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ ω D.index.w (D.FS.cut j).foldPlus hσ hS1 hatom

/-- **One minus folded energy of DC2's baseline pieces on the paper's tail**
(`lem:record:folded-energy`, `prop:record:density-structured` for a folded energy,
`lem:sharp-first`): for a piece `φ` of DC2's choice expansion at the tag `j` with selected atoms
`hTermAtoms φ` (the non-`μ` pieces), the minus folded energy of `envC` (right increments,
`D.index.w`) that DC2's `hfold` bounds
satisfies the chain bound. The folded laws are positive records off `μ` (DC2's
`bpieceLm_positiveRecord`) and equal `μ` at the `μ`-pieces, and `env_fold_chain_paper` applies at
the fold map `φ₋` of the cut `c_j` (`foldedMinus_eq_crt`). Remaining: the modulus conditions and
`hatom` for the folded laws. -/
theorem envR_foldMinus_piece_paper {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag)
    (φ : ∀ b, DensityFibre.HPiece D L b)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L Qb dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |EnvelopeInputs.foldedMinus (D.FS.cut j) (DensityFibre.bpieceLm D L Qb dec j)
        (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| ≤
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L Qb dec j b.1 (φ b.1)) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) (DensityFibre.hTermAtoms D L φ)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1)
              (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.2.2)
              (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.1))
            (fun _ => True) a' θ (density (blockScale * L) A) * D.Y L A +
          dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  rw [DensityFibre.foldedMinus_eq_crt blk (prefix_pairwise (hpair L)) (D.FS.cut j)
    (DensityFibre.bpieceLm D L Qb dec j)
    (fun v => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
      (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v) φ]
  have hE : ∀ b ∉ DensityFibre.hTermAtoms D L φ,
      DensityFibre.bpieceLm D L Qb dec j b (φ b) = D.R.law paperTail L b := by
    intro b hb
    unfold DensityFibre.hTermAtoms at hb
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_false] at hb
    revert hb
    rcases φ b with (_ | k) | (⟨i, _ | t⟩ | _) <;> intro hb <;>
      simp_all [DensityFibre.hpieceIsMu, DensityFibre.bpieceLm]
  have hΛ : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      IsPositiveRecord (DensityFibre.bpieceLm D L Qb dec j b (φ b)) := by
    intro b hb
    exact DensityFibre.bpieceLm_positiveRecord D L Qb dec hQ j b (φ b) (mem_filter.mp hb).2
  exact env_fold_chain_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (fun b => DensityFibre.bpieceLm D L Qb dec j b (φ b)) (DensityFibre.hTermAtoms D L φ) hE hΛ
    hne hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ ω D.index.w (D.FS.cut j).foldMinus hσ hS1 hatom

end Sarkozy.DensityChain2
