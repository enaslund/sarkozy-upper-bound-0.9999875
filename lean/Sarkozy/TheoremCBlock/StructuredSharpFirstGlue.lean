module

public import Sarkozy.Structured.SharpFirstGlue
public import Sarkozy.TheoremCBlock.StructuredTheoremCGlue

@[expose] public section




open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.TheoremCBlock.Structured

open Sarkozy.TheoremC Sarkozy.Structured
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame

variable {a : ℝ}

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion

section Reduction

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- The variation prices `p_𝔟` of the first stage are nonnegative. -/
theorem pvar_nonneg (D : ComparisonData a m₀ blk p pr h E) (L : ℕ) (b : BlockAtom Bk J L) :
    0 ≤ D.FS.pvar L b := by
  unfold FirstStage.pvar
  exact sum_nonneg fun i _ => mul_nonneg (mul_nonneg (abs_nonneg _)
    (ComparisonData.mass_nonneg_of_nonneg (D.FS.κa_pos L b i).1)) (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
/-- **`SharpFirstTerms` from the folded-energy bounds** (`lem:sharp-first` with
`lem:record:folded-energy` and `prop:record:density-structured`). Suppose that at every least
counterexample, for every nonempty choice `σ` of differences and every tag `j` present:
* the folded factorization `|Y_σ| ≤ W_j(σ) √(F⁺_{σ,j}) √(F⁻_{σ,j})` holds, with
  `F^± ≥ 0` (`lem:record:folded-energy`);
* the folded energies are bounded, `F^± ≤ (1 + ε_L) Y R(σ) + r_σ`, with `r_σ ≥ 0`
  (`prop:record:density-structured`, the `_theta` layers at `ϑ`);
* the remainders add up: `∑_σ W*(σ) r_σ ≤ c L^{-1/825} α`.

Then `SharpFirstTerms` holds, with remainders `W*(σ) r_σ`. -/
theorem sharpFirstTerms_of_folded (D : ComparisonData a m₀ blk p pr h E)
    (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L) (hεt : Tendsto ε atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (Fp Fm : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → ℝ)
    (rf : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ σ : (∀ b, Option
        (D.FS.Ib L b)),
      σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      0 ≤ Fp L A σ j ∧ 0 ≤ Fm L A σ j ∧ 0 ≤ rf L A σ ∧
      |diagonalIntegral (tensorLaw (fun b => (σ b).elim (D.FS.ρ L b)
          (fun i => D.FS.κ' L b i - D.FS.κ L b i))) (blockLift m₀ blk p L A)| ≤
        sharpVarWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) j σ *
          Real.sqrt (Fp L A σ j) * Real.sqrt (Fm L A σ j) ∧
      Fp L A σ j ≤ (1 + ε L) * D.Y L A * restWeight (D.FS.pvar L) σ + rf L A σ ∧
      Fm L A σ j ≤ (1 + ε L) * D.Y L A * restWeight (D.FS.pvar L) σ + rf L A σ))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * rf L A σ ≤ remainder c L A)) :
    D.SharpFirstTerms := by
  refine ⟨ε, hε0, hεt, c, hc,
    fun L A σ => maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * rf L A σ, ?_, hrem⟩
  filter_upwards [hfold] with L hL
  intro C hC hk A hA hY σ hσ j hj
  obtain ⟨hFp0, hFm0, hr0, hY1, hFp, hFm⟩ := hL C hC hk A hA hY σ hσ j hj
  have hY0 : 0 ≤ D.Y L A := by
    have : 0 ≤ C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
        density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent :=
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)
    linarith
  have hW0 := sharpVarWeight_nonneg (D.FS.tag L) (dprice_nonneg D L) (vprice_nonneg D L) j σ
  have hWm := sharpVarWeight_le_maxWeight (D.FS.tag L) (dprice_nonneg D L) (vprice_nonneg D L)
    j σ
  have hgm := sqrt_mul_sqrt_le_add_div_two hFp0 hFm0
  rw [tagWeight_eq_mul]
  set W := sharpVarWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) j σ with hWdef
  set R := restWeight (D.FS.pvar L) σ with hRdef
  set Wm := maxWeight (D.FS.dprice L) (D.FS.vprice L) σ with hWmdef
  have h1 : W * (Real.sqrt (Fp L A σ j) * Real.sqrt (Fm L A σ j)) ≤
      W * ((Fp L A σ j + Fm L A σ j) / 2) := mul_le_mul_of_nonneg_left hgm hW0
  have h2 : W * ((Fp L A σ j + Fm L A σ j) / 2) ≤ W * ((1 + ε L) * D.Y L A * R + rf L A σ) := by
    apply mul_le_mul_of_nonneg_left _ hW0
    linarith
  have h3 : W * rf L A σ ≤ Wm * rf L A σ := mul_le_mul_of_nonneg_right hWm hr0
  calc |diagonalIntegral (tensorLaw (fun b => (σ b).elim (D.FS.ρ L b)
          (fun i => D.FS.κ' L b i - D.FS.κ L b i))) (blockLift m₀ blk p L A)|
      ≤ W * Real.sqrt (Fp L A σ j) * Real.sqrt (Fm L A σ j) := hY1
    _ = W * (Real.sqrt (Fp L A σ j) * Real.sqrt (Fm L A σ j)) := by ring
    _ ≤ W * ((1 + ε L) * D.Y L A * R + rf L A σ) := h1.trans h2
    _ = (1 + ε L) * D.Y L A * (W * R) + W * rf L A σ := by ring
    _ ≤ (1 + ε L) * D.Y L A * (W * R) + Wm * rf L A σ := by linarith

omit [DecidableEq P] in
/-- The variation prices of the chosen differences add up to the tag totals:
`∑_𝔟 ∑_i (d_{𝔟,i} + v_{𝔟,i}) ≤ ∑_j (d_j + v_j)`. -/
theorem sum_prices_le_totals (D : ComparisonData a m₀ blk p pr h E) (L : ℕ) :
    ∑ b, ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i) ≤ ∑ j, (D.FS.dT j + D.FS.vT j) := by
  have hre : ∀ (w : ∀ b, D.FS.Ib L b → ℝ), ∑ b, ∑ i, w b i =
      ∑ j, ∑ b, ∑ i, (if D.FS.tag L b i = j then w b i else 0) := by
    intro w
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq, ite_eq_left (mem_univ _)]
  have hsplit : ∑ b, ∑ i, (D.FS.dprice L b i + D.FS.vprice L b i) =
      ∑ b, ∑ i, D.FS.dprice L b i + ∑ b, ∑ i, D.FS.vprice L b i := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun b _ => sum_add_distrib
  rw [hsplit, hre (D.FS.dprice L), hre (D.FS.vprice L), sum_add_distrib]
  exact add_le_add (sum_le_sum fun j _ => D.FS.dT_total L j)
    (sum_le_sum fun j _ => D.FS.vT_total L j)

end Reduction

section UniformReduction

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`SharpFirstTerms` from the folded-energy bounds with uniform remainders**: as
`sharpFirstTerms_of_folded`, with the remainder summation replaced by `r_σ ≤ c₀ L^{-1/825} α`
uniformly in `σ`. The constant is `e^{∑_j (d_j + v_j)} c₀`. -/
theorem sharpFirstTerms_of_folded_uniform (D : ComparisonData a m₀ blk p pr h E)
    (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L) (hεt : Tendsto ε atTop (𝓝 0)) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (Fp Fm : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → ℝ)
    (rf : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ σ : (∀ b, Option
        (D.FS.Ib L b)),
      σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      0 ≤ Fp L A σ j ∧ 0 ≤ Fm L A σ j ∧ 0 ≤ rf L A σ ∧
      |diagonalIntegral (tensorLaw (fun b => (σ b).elim (D.FS.ρ L b)
          (fun i => D.FS.κ' L b i - D.FS.κ L b i))) (blockLift m₀ blk p L A)| ≤
        sharpVarWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) j σ *
          Real.sqrt (Fp L A σ j) * Real.sqrt (Fm L A σ j) ∧
      Fp L A σ j ≤ (1 + ε L) * D.Y L A * restWeight (D.FS.pvar L) σ + rf L A σ ∧
      Fm L A σ j ≤ (1 + ε L) * D.Y L A * restWeight (D.FS.pvar L) σ + rf L A σ))
    (hunif : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ σ : (∀ b, Option
        (D.FS.Ib L b)),
      rf L A σ ≤ remainder c₀ L A)) :
    D.SharpFirstTerms := by
  refine sharpFirstTerms_of_folded D ε hε0 hεt
    (c := Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) * c₀)
    (mul_nonneg (Real.exp_pos _).le hc₀) Fp Fm rf hfold ?_
  filter_upwards [hunif] with L hL
  intro C hC hk A hA hY
  have hr := hL C hC hk A hA hY
  have hrem0 : 0 ≤ remainder c₀ L A := by
    unfold remainder
    exact mul_nonneg (mul_nonneg hc₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  have hnn : ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      0 ≤ maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
    intro σ
    unfold maxWeight
    refine prod_nonneg fun b _ => ?_
    rcases σ b with _ | i
    · exact zero_le_one
    · exact add_nonneg (dprice_nonneg D L b i) (vprice_nonneg D L b i)
  have hsum := sum_maxWeight_le (dprice_nonneg D L) (vprice_nonneg D L)
  have hexp := Real.exp_le_exp.mpr (sum_prices_le_totals D L)
  calc ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * rf L A σ ≤
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * remainder c₀ L A :=
        sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hr σ) (hnn σ)
    _ = (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        maxWeight (D.FS.dprice L) (D.FS.vprice L) σ) * remainder c₀ L A := by rw [sum_mul]
    _ ≤ Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) * remainder c₀ L A :=
        mul_le_mul_of_nonneg_right (hsum.trans hexp) hrem0
    _ = remainder (Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) * c₀) L A := by
        unfold remainder
        ring

end UniformReduction

end Sarkozy.TheoremCBlock.Structured
