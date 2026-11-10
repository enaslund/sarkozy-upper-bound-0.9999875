module

public import Sarkozy.DensityChain.LargeTerms
public import Sarkozy.DensityChain.MuTerm

@[expose] public section

/-!
# `Y ≤ C_ε Q^ε α`: the reference energy is at most the density, up to `N^ε`

SUM (7 November 2026). The cross terms of `lem:sharp-first` need an *upper* bound of the
reference energy `Y = Y(L, A)` by the density. The paper does not state one: its proof of
`lem:sharp-first` absorbs the chain remainders into `(1 + o(1)) Y` with the *lower* bound
`Y > C₀ L^{-a} α^θ` at a counterexample. The upper bound used here is the first step of the proof
of `lem:record:density-lp`, applied to the reference law:

* Hölder in `L^{72}` with uniform one-slot marginals (DC1's `abs_signed_energy_le_lpNorm`,
  through `expect_abs_signed_energy_le_moment` over a one-point index law), the reference laws
  being positive records (`isPositiveRecord_muLaw`, (R3));
* the `72`-th moment of `F_A` (`lem:record:lift-moments`(c), DC1's `input_moment_le_density`
  with `r = 36`): `‖F_A‖_{72}^{72} ≤ M₀^{72} |X₀|^{72} C_ε Q^ε K α`.

**`dataY_le_lp ε`**: `Y(L, A) ≤ M₀^{72} |X₀|^{72} C_ε Q^ε K α` under the scale conditions.
-/

namespace Sarkozy.SharpSums

open Finset Function
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.DensityDC Sarkozy.DensityChain

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **The reference energy is at most the density, up to `Q^ε`** (`lem:record:density-lp`, first
step, at the reference law; `lem:record:lift-moments`(c)): under the scale conditions,
`Y(L, A) ≤ M₀^{72} |X₀|^{72} C_ε Q^ε K α`, `Q = Q(KL)`. -/
theorem dataY_le_lp (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (_hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    {L : ℕ} {A : Finset ℤ} {M0 Qcl Qpre N0 N0' : ℕ}
    (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L) (_hL : 1 ≤ L) (_hM0 : 1 ≤ M0)
    (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L)),
    D.Y L A ≤
      (M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
        paperCutoff (blockScale * L) ^ ε * ((blockScale : ℝ) * density (blockScale * L) A)) := by
  obtain ⟨C, hC, hc⟩ := input_moment_le_density 36 (by norm_num) ε hε
  refine ⟨C, hC, ?_⟩
  intro D hpair L A M0 Qcl Qpre N0 N0' hsc hL hM0 hp hinj
  set Λ' := crtLaws blk (prefix_pairwise (hpair L)) L
    (BracketEnergy.termLaw D L (muLaw D L) (fun _ => false) (fun _ => false)) with hΛ'
  set ρ : (Slot → ResidueSpace (crtModuli m₀ blk p L)) → ℝ := lawDensity (tensorLaw Λ') with hρ
  set Q := paperCutoff (blockScale * L) with hQ
  set F : Unit → Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ :=
    fun _ _ => unchangedInput (crtModuli m₀ blk p L) Q A L with hF
  -- the reference energy as a signed sum
  have hlaw : D.R.law p L =
      BracketEnergy.termLaw D L (muLaw D L) (fun _ => false) (fun _ => false) := by
    funext b
    simp [BracketEnergy.termLaw, muLaw]
  have hY : D.Y L A = ∑ z, ρ z * ∏ v, F () v (z v) := by
    unfold TheoremCBlock.ComparisonData.Y
    rw [energyFirst_eq_diagonalIntegral]
    unfold diagonalIntegral
    rw [multilinearIntegral_crt blk (prefix_pairwise (hpair L)) L]
    simp_rw [blockLift_crtLabel blk L (hpair L) A]
    rw [hlaw]
    unfold multilinearIntegral
    rw [apply_eq_sum_lawDensity']
  -- the weight is a product of positive-record densities
  have hρprod : ρ = fun z => ∏ b, lawDensity (Λ' b) (fun v => z v b) := by
    funext z
    rw [hρ, Sarkozy.DensityDC.lawDensity_tensorLaw]
  have hpos : ∀ b, IsPositiveRecord (Λ' b) := fun b =>
    isPositiveRecord_pullLaw _ (isPositiveRecord_termLaw D L hp (muLaw D L)
      (fun b => isPositiveRecord_muLaw D L hp b) (fun _ => false) (fun _ => false) b)
  have hunif : selectedMarginalsUniform ρ := by
    rw [hρprod]
    exact selectedMarginalsUniform_prod (fun b => lawDensity (Λ' b))
      fun b => selectedMarginalsUniform_lawDensity (hpos b)
  have htv : totalVariation ρ = 1 := by
    rw [hρprod, totalVariation_prod]
    refine (prod_congr rfl fun b _ => ?_).trans prod_const_one
    rw [show (1 : ℝ) = termWeight D L (muLaw D L) b false false by simp [termWeight]]
    rw [← totalVariation_termLaw D L hp (muLaw D L) (fun _ => false) (fun _ => false) b]
    unfold totalVariation
    rw [hΛ']
    exact sum_abs_lawDensity_pullLaw _ _
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hQ1 : 1 ≤ Q := one_le_paperCutoff hKL
  -- the moments of `F_A`
  have hB : ∀ v, (FiniteLaw.uniform Unit).expect (fun ω =>
        (FiniteLaw.uniform (ResidueSpace (crtModuli m₀ blk p L))).moment 72 (F ω v)) ≤
      (M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
        Q ^ ε * ((blockScale : ℝ) * density (blockScale * L) A)) := by
    intro v
    apply FiniteLaw.expect_le_const
    intro ω
    have hFw : F ω v = paperForm (crtModuli m₀ blk p L) Q A (wholeDatum L) :=
      unchangedInput_eq_paperForm _ Q A L
    rw [hFw]
    have hLM : L ≤ (wholeDatum L).2.2.1 := Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    have hcut := cutoff_conditions_of_scale hsc hKL hLM
    have hD0le : (wholeDatum L).1 ≤ M0 := hM0
    have key := hc (blockModulus m₀ blk) (p L) hp hinj Q hQ1 (wholeDatum L).2.2.2
      hL hLM hcut.1 hcut.2 hD0le (wholeDatum L).2.1 A
    simp only [show (2 * 36 : ℕ) = 72 from rfl, Nat.cast_ofNat] at key
    exact key
  have h := expect_abs_signed_energy_le_moment (FiniteLaw.uniform Unit) ρ hunif F hB
  rw [htv, one_mul] at h
  have e : (FiniteLaw.uniform Unit).expect (fun ω => |∑ z, ρ z * ∏ v, F ω v (z v)|) =
      |∑ z, ρ z * ∏ v, F () v (z v)| :=
    FiniteLaw.expect_const (FiniteLaw.uniform Unit) _
  rw [e] at h
  rw [hY]
  exact (le_abs_self _).trans h

end Sarkozy.SharpSums
