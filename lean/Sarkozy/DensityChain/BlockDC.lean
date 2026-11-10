module

public import Sarkozy.DensityChain.DensityDC
public import Sarkozy.EnvelopeEnergiesPaper.BlockReference
public import Sarkozy.TheoremCBlock.Data
public import Mathlib.NumberTheory.Primorial

@[expose] public section

/-!
# `lem:record:density-dc` on the paper's block coordinates

The block atoms `BlockAtom Bk J L = Bk ⊕ J L` in B5's cyclic coordinates have moduli
`crtModuli m₀ blk p L = Sum.elim (blockModulus m₀ blk) (p L)`, which is *by definition*
`joinModuli (blockModulus m₀ blk) (p L)`. So `density_dc_groups` and `density_dc_fibrewise`
(`DensityChain.DensityDC`) apply with `J₀ := Bk`. This file supplies, from K0's reference
`TheoremCBlock.Reference` (the data's `D.R`), every hypothesis of `lem:record:density-dc` that
concerns the reference law `μ = crtRef`:

* (R3): `crtRef_squareAffineInvariant` (B5), restated as `block_hR3`;
* the tail coordinates `T = {p_j ≥ P₅}` (`tailAtoms`), prime (`tailAtoms_prime`) and
  `γ`-mixing at every slot by (R4) (`tailAtoms_mixing`, from `Reference.mixing`);
* the prefix conductor `C' = Q_pre := (∏_β D_β) · primorial(P₅)` (`prefixConductor`): the order
  of every character of the coordinates outside `T` (the blocks and the tail primes below `P₅`)
  divides it (`prefixConductor_dvd`), and it does not depend on `L`.

In the paper (proof of `lem:record:density-dc`, Step 1), `μ_𝒮` is the product of the atom laws
below `P₅` (conductor dividing `Q_pre`) and of the tail laws `μ_p`, `p ≥ P₅`, which satisfy (R4).
`prefixConductor` is that `Q_pre`, with the tail primes below `P₅` bounded by `primorial(P₅)`.

**`density_dc_block`** and **`density_dc_block_fibrewise`** are `lem:record:density-dc` on the
block coordinates with these inputs discharged: what is left is the paper's own per-energy data
(distinct prime tail moduli, the scale conditions, the modulus conditions on `D_E`, uniform
one-slot marginals of `|ρ|`, (S1)).
-/

namespace Sarkozy.DensityChain

open Finset Function
open scoped BigOperators
open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing
  Sarkozy.DensityDC Sarkozy.EnvelopeEnergiesPaper Sarkozy.BlockFrame

/-- The block coordinates are joined coordinates with the block moduli as prefix. -/
theorem crtModuli_eq_joinModuli {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ}
    {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk) {J : ℕ → Type}
    (p : ∀ L, J L → ℕ) (L : ℕ) :
    crtModuli m₀ blk p L = joinModuli (blockModulus m₀ blk) (p L) := rfl

/-- The tail coordinates of (R4): the tail primes `p_j ≥ P₅`. -/
def tailAtoms {Bk : Type} {J : ℕ → Type} [∀ L, Fintype (J L)] (p : ∀ L, J L → ℕ) (P5 L : ℕ) :
    Finset (BlockAtom Bk J L) :=
  ((univ : Finset (J L)).filter fun j => P5 ≤ p L j).map ⟨Sum.inr, Sum.inr_injective⟩

theorem mem_tailAtoms {Bk : Type} {J : ℕ → Type} [∀ L, Fintype (J L)] (p : ∀ L, J L → ℕ)
    {P5 L : ℕ} (b : BlockAtom Bk J L) :
    b ∈ tailAtoms (Bk := Bk) p P5 L ↔ ∃ j, b = Sum.inr j ∧ P5 ≤ p L j := by
  unfold tailAtoms
  simp only [mem_map, mem_filter, mem_univ, true_and, Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, rfl, hj⟩
  · rintro ⟨j, rfl, hj⟩
    exact ⟨j, hj, rfl⟩

theorem inl_not_mem_tailAtoms {Bk : Type} {J : ℕ → Type} [∀ L, Fintype (J L)] (p : ∀ L, J L → ℕ)
    {P5 L : ℕ} (β : Bk) :
    (Sum.inl β : BlockAtom Bk J L) ∉ tailAtoms p P5 L := by
  rw [mem_tailAtoms]
  rintro ⟨j, hj, _⟩
  exact Sum.inl_ne_inr hj

theorem inr_mem_tailAtoms_iff {Bk : Type} {J : ℕ → Type} [∀ L, Fintype (J L)] (p : ∀ L, J L → ℕ)
    {P5 L : ℕ} (j : J L) :
    (Sum.inr j : BlockAtom Bk J L) ∈ tailAtoms p P5 L ↔ P5 ≤ p L j := by
  rw [mem_tailAtoms]
  constructor
  · rintro ⟨j', hj', hle⟩
    rw [Sum.inr_injective hj']
    exact hle
  · intro h
    exact ⟨j, rfl, h⟩

/-- The tail coordinates have prime moduli. -/
theorem tailAtoms_prime {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ}
    {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk) {J : ℕ → Type}
    [∀ L, Fintype (J L)] (p : ∀ L, J L → ℕ) {P5 L : ℕ} (hp : ∀ j, (p L j).Prime) :
    ∀ b ∈ tailAtoms (Bk := Bk) p P5 L, (crtModuli m₀ blk p L b).Prime := by
  intro b hb
  obtain ⟨j, rfl, _⟩ := (mem_tailAtoms p b).mp hb
  exact hp j

/-- **(R4) at the tail coordinates** (`Reference.mixing`): the reference read on the cyclic
coordinates is `γ`-mixing at every slot at the tail primes `p ≥ P₅`. -/
theorem tailAtoms_mixing {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ}
    [∀ i, NeZero (m₀ i)] {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
    [∀ L j, NeZero (p L j)] (R : TheoremCBlock.Reference m₀ blk) {L : ℕ}
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (hp : ∀ j, (p L j).Prime) :
    ∀ b ∈ tailAtoms (Bk := Bk) p R.P5 L, ∀ v,
      IsGammaMixing (crtModuli m₀ blk p L b) Sarkozy.AnalyticStage.γ
        (crtRef blk p h0 R.μ₀ R.μp L b) {v} := by
  intro b hb v
  obtain ⟨j, rfl, hj⟩ := (mem_tailAtoms p b).mp hb
  exact R.mixing (p L j) (hp j) hj v

/-- The prefix conductor `Q_pre = (∏_β D_β) · primorial(P₅)`. -/
def prefixConductor {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ}
    {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk) (P5 : ℕ) : ℕ :=
  (∏ β, blockModulus m₀ blk β) * primorial P5

theorem prefixConductor_pos {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ}
    [∀ i, NeZero (m₀ i)] {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
    (P5 : ℕ) :
    0 < prefixConductor (m₀ := m₀) blk P5 := by
  unfold prefixConductor
  apply Nat.mul_pos
  · exact prod_pos fun β _ => Nat.pos_of_ne_zero (NeZero.ne _)
  · exact primorial_pos P5


/-- The order of a residue divides its modulus. -/
theorem addOrderOf_dvd_modulus (n : ℕ) [NeZero n] (x : ZMod n) : addOrderOf x ∣ n := by
  have h := addOrderOf_dvd_card (x := x)
  rwa [ZMod.card] at h

/-- **The prefix conductor bound** of `lem:record:prefix-conductor` with `C' = Q_pre`: for every
residue `a`, the orders of its coordinates outside the tail coordinates of (R4) multiply to a
divisor of `prefixConductor P₅`. Needs distinct prime tail moduli. -/
theorem prefixConductor_dvd {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ}
    [∀ i, NeZero (m₀ i)] {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
    [∀ L j, NeZero (p L j)] {P5 L : ℕ} (hp : ∀ j, (p L j).Prime) (hinj : Injective (p L))
    (a : ResidueSpace (crtModuli m₀ blk p L)) :
    (∏ b ∈ univ.filter (· ∉ tailAtoms p P5 L), addOrderOf (a b)) ∣
      prefixConductor (m₀ := m₀) blk P5 := by
  have h1 : (∏ b ∈ univ.filter (· ∉ tailAtoms p P5 L), addOrderOf (a b)) ∣
      ∏ b ∈ univ.filter (· ∉ tailAtoms p P5 L), crtModuli m₀ blk p L b :=
    prod_dvd_prod_of_dvd _ _ fun b _ => addOrderOf_dvd_modulus _ (a b)
  refine h1.trans ?_
  have hsplit : ∏ b ∈ univ.filter (· ∉ tailAtoms p P5 L), crtModuli m₀ blk p L b =
      (∏ β, blockModulus m₀ blk β) * ∏ j ∈ univ.filter (fun j => p L j < P5), p L j := by
    rw [prod_filter, Fintype.prod_sum_type, prod_filter]
    congr 1
    · apply prod_congr rfl
      intro β _
      simp only [inl_not_mem_tailAtoms p β, not_false_eq_true, ite_true]
      rfl
    · apply prod_congr rfl
      intro j _
      by_cases hj : P5 ≤ p L j
      · have h2 : ¬ p L j < P5 := not_lt.mpr hj
        simp only [(inr_mem_tailAtoms_iff p j).mpr hj, not_true_eq_false, ite_false, h2]
      · have h2 : p L j < P5 := lt_of_not_ge hj
        have h3 : (Sum.inr j : BlockAtom Bk J L) ∉ tailAtoms p P5 L :=
          fun h => hj ((inr_mem_tailAtoms_iff p j).mp h)
        simp only [h3, not_false_eq_true, ite_true, h2]
        rfl
  rw [hsplit]
  unfold prefixConductor
  apply mul_dvd_mul (dvd_refl _)
  have himg : ∏ j ∈ univ.filter (fun j => p L j < P5), p L j =
      ∏ q ∈ (univ.filter (fun j => p L j < P5)).image (p L), q :=
    (prod_image (f := fun q => q) fun x _ y _ h => hinj h).symm
  rw [himg]
  unfold primorial
  apply prod_dvd_prod_of_subset
  intro q hq
  simp only [mem_image, mem_filter, mem_univ, true_and] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  simp only [mem_filter, mem_range]
  exact ⟨by omega, hp j⟩

/-- The property of the moment constants `C₁, C₇₁` in `density_dc_block` (named so that the
same constants can be shared by several consequences). -/
def DCBlockProp (ε C1 C71 : ℝ) : Prop :=
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
      {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
      {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
      [∀ L j, NeZero (p L j)] {Ω : Type} [Fintype Ω]
      (R : TheoremCBlock.Reference m₀ blk) {L : ℕ}
      (_hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)),
      (∀ j, (p L j).Prime) → Injective (p L) →
      ∀ {A : Finset ℤ} (_hL : 2 ≤ L)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (E : Finset (BlockAtom Bk J L)) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, crtModuli m₀ blk p L j = qE * cE) (_hqE : Squarefree qE)
      (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace (crtModuli m₀ blk p L)) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (crtModuli m₀ blk p L k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (gt : Ω → Slot → ResidueSpace (crtModuli m₀ blk p L) →
        ResidueSpace (crtModuli m₀ blk p L) → ℝ)
      (_hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
        (squareStepModel (crtModuli m₀ blk p L) E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v))
          (c ω v) (M v) (stepR (crtModuli m₀ blk p L) E (D0 v))
          (blockScale * stepEll (crtModuli m₀ blk p L) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) E (D0 v) (M v))) y).re)
      (_hgu : ∀ v, ¬changed v → ∀ ω x,
        gt ω v x = paperInputs (crtModuli m₀ blk p L) E (paperCutoff (blockScale * L)) A D0 M
          c s ω v x)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ),
      |structuredEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise _hpair) R.μ₀ R.μp L)) P
          ρ (paperInputs (crtModuli m₀ blk p L) E (paperCutoff (blockScale * L)) A D0 M c s) -
        structuredEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise _hpair) R.μ₀ R.μp L))
          P ρ gt| ≤
        dcConstant (prefixConductor (m₀ := m₀) blk R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A

/-- **`lem:record:density-dc` on the paper's block coordinates** (signed form, any index law).
For every `ε > 0` there are moment constants `C₁, C₇₁ > 0` such that: for K0's reference `R`,
distinct prime tail moduli, a scale satisfying `lem:scale-conditions`, a selected set `E` with
the modulus conditions of `def:record:structured-energy`, a weight `ρ` whose variation has
uniform one-slot marginals, and inputs `g^{I_v, D_{0,v}, s_v}`, the square-step models `g̃` at the
changed slots satisfy
`|𝔈 − 𝔈̃| ≤ C_dc ‖ρ‖ L^{-σ} α` with `C_dc = dcConstant Q_pre γ M₀ |X₀| C₁ C₇₁`,
`Q_pre = prefixConductor P₅`, `|X₀| = ∏_β D_β`. (R3), (R4) and the conductor bound are
discharged from `R`. -/
theorem density_dc_block (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
      {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
      {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
      [∀ L j, NeZero (p L j)] {Ω : Type} [Fintype Ω]
      (R : TheoremCBlock.Reference m₀ blk) {L : ℕ}
      (_hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)),
      (∀ j, (p L j).Prime) → Injective (p L) →
      ∀ {A : Finset ℤ} (_hL : 2 ≤ L)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (E : Finset (BlockAtom Bk J L)) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, crtModuli m₀ blk p L j = qE * cE) (_hqE : Squarefree qE)
      (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace (crtModuli m₀ blk p L)) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (crtModuli m₀ blk p L k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (gt : Ω → Slot → ResidueSpace (crtModuli m₀ blk p L) →
        ResidueSpace (crtModuli m₀ blk p L) → ℝ)
      (_hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
        (squareStepModel (crtModuli m₀ blk p L) E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v))
          (c ω v) (M v) (stepR (crtModuli m₀ blk p L) E (D0 v))
          (blockScale * stepEll (crtModuli m₀ blk p L) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) E (D0 v) (M v))) y).re)
      (_hgu : ∀ v, ¬changed v → ∀ ω x,
        gt ω v x = paperInputs (crtModuli m₀ blk p L) E (paperCutoff (blockScale * L)) A D0 M
          c s ω v x)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ),
      |structuredEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise _hpair) R.μ₀ R.μp L)) P
          ρ (paperInputs (crtModuli m₀ blk p L) E (paperCutoff (blockScale * L)) A D0 M c s) -
        structuredEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise _hpair) R.μ₀ R.μp L))
          P ρ gt| ≤
        dcConstant (prefixConductor (m₀ := m₀) blk R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_dc_groups ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ _ _ m₀ _ Bk _ _ blk J _ _ p _ Ω _ R L hpair hp hinj A hL M0 Qcl Qpre N0 N0' hsc hM0
    E qE cE hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed _ gt
    hgt hgu σ hσ hS1
  have hγ : (0 : ℝ) ≤ Sarkozy.AnalyticStage.γ := by
    unfold Sarkozy.AnalyticStage.γ; norm_num
  exact h (blockModulus m₀ blk) (p L) hp hinj (crtModuli_pairwise blk hpair) hL hsc hM0
    (crtRef blk p (prefix_pairwise hpair) R.μ₀ R.μp L)
    (crtRef_squareAffineInvariant blk p (prefix_pairwise hpair) R.μ₀ R.μp L R.inv₀ R.invp)
    (tailAtoms p R.P5 L) (tailAtoms_prime blk p hp) hγ
    (tailAtoms_mixing blk p R (prefix_pairwise hpair) hp)
    (prefixConductor_pos blk R.P5) (prefixConductor_dvd blk p hp hinj) E hDE hqE hcE hcE0 hcQ
    hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed gt hgt hgu hσ hS1

/-- `density_dc_block` with its property named. -/
theorem density_dc_block' (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧ DCBlockProp ε C1 C71 :=
  density_dc_block ε hε

/-- **`lem:record:density-dc` on the block coordinates, fibrewise, at a point index** (the first
display of the lemma, the absolute value inside the `z`-sum; `density_dc_fibrewise` with the
reference inputs discharged from `R` as in `density_dc_block`):
`∑_z |ρ(z)| |Λ_μ((g_v(z_v, ·))_v) − Λ_μ((g̃_v(z_v, ·))_v)| ≤ C_dc ‖ρ‖ L^{-σ} α`, for every `σ ≥ 0`
with `ε/20 − γ/40 ≤ −σ`. -/
theorem density_dc_block_fibrewise (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
      {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
      {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
      [∀ L j, NeZero (p L j)]
      (R : TheoremCBlock.Reference m₀ blk) {L : ℕ}
      (_hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)),
      (∀ j, (p L j).Prime) → Injective (p L) →
      ∀ {A : Finset ℤ} (_hL : 2 ≤ L)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (E : Finset (BlockAtom Bk J L)) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, crtModuli m₀ blk p L j = qE * cE) (_hqE : Squarefree qE)
      (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (ρ : (Slot → ResidueSpace (crtModuli m₀ blk p L)) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (crtModuli m₀ blk p L k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Slot → ℤ) (s : ∀ v : Slot, ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (gt : Slot → ResidueSpace (crtModuli m₀ blk p L) → ResidueSpace (crtModuli m₀ blk p L) → ℝ)
      (_hgt : ∀ v x, changed v → gt v x = fun y =>
        (squareStepModel (crtModuli m₀ blk p L) E x (s v) A (Icc (c v + 1) (c v + M v))
          (c v) (M v) (stepR (crtModuli m₀ blk p L) E (D0 v))
          (blockScale * stepEll (crtModuli m₀ blk p L) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) E (D0 v) (M v))) y).re)
      (_hgu : ∀ v, ¬changed v → ∀ x,
        gt v x = paperInputs (crtModuli m₀ blk p L) E (paperCutoff (blockScale * L)) A D0 M
          (fun _ : Unit => c) (fun _ : Unit => s) () v x)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ),
      ∑ z, |ρ z| *
        |multilinearIntegral (signedIntegral
            (FiniteLaw.tensor (crtRef blk p (prefix_pairwise _hpair) R.μ₀ R.μp L)).weight)
            (fun v => paperInputs (crtModuli m₀ blk p L) E (paperCutoff (blockScale * L)) A D0 M
              (fun _ : Unit => c) (fun _ : Unit => s) () v (z v)) -
          multilinearIntegral (signedIntegral
            (FiniteLaw.tensor (crtRef blk p (prefix_pairwise _hpair) R.μ₀ R.μp L)).weight)
            (fun v => gt v (z v))| ≤
        dcConstant (prefixConductor (m₀ := m₀) blk R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_dc_fibrewise ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ _ _ m₀ _ Bk _ _ blk J _ _ p _ R L hpair hp hinj A hL M0 Qcl Qpre N0 N0' hsc hM0
    E qE cE hDE hqE hcE hcE0 hcQ hcopE hqN ρ hunif D0 hD0 hD0M hcop0 M hM c s changed _ gt
    hgt hgu σ hσ hS1
  have hγ : (0 : ℝ) ≤ Sarkozy.AnalyticStage.γ := by
    unfold Sarkozy.AnalyticStage.γ; norm_num
  exact h (blockModulus m₀ blk) (p L) hp hinj (crtModuli_pairwise blk hpair) hL hsc hM0
    (crtRef blk p (prefix_pairwise hpair) R.μ₀ R.μp L)
    (crtRef_squareAffineInvariant blk p (prefix_pairwise hpair) R.μ₀ R.μp L R.inv₀ R.invp)
    (tailAtoms p R.P5 L) (tailAtoms_prime blk p hp) hγ
    (tailAtoms_mixing blk p R (prefix_pairwise hpair) hp)
    (prefixConductor_pos blk R.P5) (prefixConductor_dvd blk p hp hinj) E hDE hqE hcE hcE0 hcQ
    hcopE hqN ρ hunif D0 hD0 hD0M hcop0 M hM c s changed gt hgt hgu hσ hS1

end Sarkozy.DensityChain
