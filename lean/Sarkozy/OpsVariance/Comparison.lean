module

public import Sarkozy.OpsVariance.Steps
public import Sarkozy.BracketEnergy.Bracket

@[expose] public section

/-!
# The comparison `hJN` of `Ñ` with `Ñ₀` at `J_X`, through `lem:sharp-first`

`paper/sections/10_comparison_lemmas.tex`, `lem:record:variance-interface`(ii)
(`Y^Ñ[J_X] ≥ Y^{Ñ₀}[J_X] − (R_err + o(1)) C_X Y`), (E1) (last bound,
`|Y^Ñ[κ] − Y^{Ñ₀}[κ]| ≤ (R_err + o(1)) ‖κ‖ C_X Y`), `lem:bracket-energy` and its proof ("The
difference is `lem:sharp-first` with `F` the first-stage atoms outside `X`, `ρ_𝔟 = Ñ_{0,𝔟}` …: it
is at most `(e^{U₀} 𝔗(d, v) + o(1)) ‖κ‖ Π_X Y = (R_err + o(1)) ‖κ‖ Π_X Y`").

The input `hJN` of `varStepsAt_credit` compares `Y[J_X ⊗ Ñ]` with `Y[J_X ⊗ Ñ₀]`, where outside `X`
`Ñ_𝔟 = Ñ_{0,𝔟} + ∑_i (κ'_i − κ_i)` (`def:cp3`). Here it is reduced, by WP-R's
`abs_energy_sub_le_sharpFirst` (`lem:sharp-first`) and the tag-series bound of B9's
`diff_bound_of_coupled` (`e^{∑ u} 𝔗(d, v) ≤ e^{U₀} 𝔗(d_T, v_T) = R_err`), to the **per-choice
coupled bounds** of the choices `σ` of first-stage differences outside `X`:

`|Y[J_X ⊗ (⊗_{σ} (κ'_i − κ_i)) ⊗ Ñ₀]| ≤ K wt_j(σ) + r_σ` for every nonempty `σ` and tag `j ∈ σ`,

the same kind of term as EC's coupled envelope pieces (`E1Coup`), with `J_X` in place of the
envelope `⊗_X D` (`lem:sharp-first`, `lem:density:coupled`). With `K = (1 + ε) C_X Y`:

* **`abs_varJ_sub_varJ0_le`**: `|Y[J_X ⊗ Ñ] − Y[J_X ⊗ Ñ₀]| ≤ (R_err + z) K + ∑_σ r_σ`;
* **`hJN_of_coupled`**: the field `hJN` with `z ≥ R_err ε` and `r_J = ∑_σ r_σ`;
* **`hJN_canonical`**: the field `hJN` **proved** at the canonical remainders `jExcess` (the excess
  of each coupled term over its main term, as EC's `rX`); its content moves to the remainder budget
  `∑_ω π̃_ω ∑_σ jExcess(ω, σ) ≤ c L^{-σ} α` of the field `hrr`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- **The law of a choice `σ` of first-stage differences** in the comparison of `Y[J_X ⊗ Ñ]` with
`Y[J_X ⊗ Ñ₀]`: `J(m_𝔟)` on `X`; outside `X`, the difference `κ'_i − κ_i` where `σ` picks `i` and
`Ñ_{0,𝔟}` elsewhere (B9's `sharpPiece` with `Q = J(m)`). -/
noncomputable def jPiece (L : ℕ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (σ : ∀ b, Option (D.FS.Ib L b)) (b : BlockAtom Bk J L) : AtomMeasure m₀ blk p L b :=
  (σ b).elim (if b ∈ Choice.support ω then indepLaw reservedCut (m b) else D.GB.N₀ L b)
    (fun i => if b ∈ Choice.support ω then 0 else D.FS.κ' L b i - D.FS.κ L b i)

/-- The variation prices of the outside atoms: `u_𝔟` off `X`, `0` on `X`. -/
noncomputable def outPrice (L : ℕ) (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) : ℝ :=
  if b ∈ Choice.support ω then 0 else D.GB.uprice L b

variable {D}

omit [DecidableEq P] in
/-- **`|Y[J_X ⊗ Ñ] − Y[J_X ⊗ Ñ₀]| ≤ (R_err + z) K + ∑_σ r_σ`** from the per-choice coupled bounds
(`lem:sharp-first`; the proof of `lem:bracket-energy`; for the field `hJN` of `VarStepsAt`). -/
theorem abs_varJ_sub_varJ0_le (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    {K z : ℝ} (hK : 0 ≤ K) (hz : 0 ≤ z) (r : (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      |diagonalIntegral (tensorLaw (jPiece D L ω m σ)) (blockLift m₀ blk p L A)| ≤
        K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (outPrice D L ω) j σ + r σ) :
    |varJ D L A ω m - varJ0 D L A ω m| ≤ (D.GB.Rerr + z) * K +
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ := by
  set Aw : ∀ b : BlockAtom Bk J L, AtomMeasure m₀ blk p L b := fun b =>
    if b ∈ Choice.support ω then indepLaw reservedCut (m b) else D.GB.N₀ L b with hAw
  set Dd : ∀ b : BlockAtom Bk J L, D.FS.Ib L b → AtomMeasure m₀ blk p L b := fun b i =>
    if b ∈ Choice.support ω then 0 else D.FS.κ' L b i - D.FS.κ L b i with hDd
  have hN : (fun b => if b ∈ Choice.support ω then indepLaw reservedCut (m b) else D.GB.N L b) =
      fun b => Aw b + ∑ i, Dd b i := by
    funext b
    simp only [hAw, hDd]
    by_cases hb : b ∈ Choice.support ω
    · simp only [hb, ↓reduceIte, sum_const_zero, add_zero]
    · simp only [hb, ↓reduceIte]
      rfl
  have hσ : ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      jPiece D L ω m σ = fun b => (σ b).elim (Aw b) (Dd b) := by
    intro σ
    funext b
    rfl
  have hp : ∀ b, 0 ≤ outPrice D L ω b := by
    intro b
    unfold outPrice
    split_ifs
    · exact le_refl 0
    · exact BracketEnergy.uprice_nonneg D L b
  have hmain := abs_energy_sub_le_sharpFirst Aw Dd (blockLift m₀ blk p L A) (D.FS.tag L)
    (fun b i => D.dprice_nonneg L b i) (fun b i => D.vprice_nonneg L b i) hp hK r
    (fun σ hσ0 j hj => by rw [← hσ σ]; exact hterm σ hσ0 j hj)
  have e1 : varJ D L A ω m = diagonalIntegral (tensorLaw fun b => Aw b + ∑ i, Dd b i)
      (blockLift m₀ blk p L A) := by
    unfold varJ
    rw [hN]
  have e2 : varJ0 D L A ω m = diagonalIntegral (tensorLaw Aw) (blockLift m₀ blk p L A) := rfl
  rw [e1, e2]
  -- the constant: `e^{∑ u} 𝔗(d, v) ≤ e^{U₀} 𝔗(d_T, v_T) = R_err`
  have hP : ∑ b, outPrice D L ω b ≤ D.GB.U₀ := by
    refine le_trans (sum_le_sum fun b _ => ?_) (BracketEnergy.sum_uprice_le D L)
    unfold outPrice
    split_ifs
    · exact BracketEnergy.uprice_nonneg D L b
    · exact le_refl _
  have hd0 : ∀ j, 0 ≤ tagTotal (D.FS.tag L) (D.FS.dprice L) j := fun j =>
    sum_nonneg fun b _ => sum_nonneg fun i _ => by
      split_ifs
      · exact D.dprice_nonneg L b i
      · exact le_refl 0
  have hv0 : ∀ j, 0 ≤ tagTotal (D.FS.tag L) (D.FS.vprice L) j := fun j =>
    sum_nonneg fun b _ => sum_nonneg fun i _ => by
      split_ifs
      · exact D.vprice_nonneg L b i
      · exact le_refl 0
  have hser := tagSeries_mono hd0 hv0 (fun j => D.FS.dT_total L j) (fun j => D.FS.vT_total L j)
  have hser0 := tagSeries_nonneg hd0 hv0
  have hexp := Real.exp_le_exp.mpr hP
  have hR : Real.exp (∑ b, outPrice D L ω b) *
      tagSeries (tagTotal (D.FS.tag L) (D.FS.dprice L)) (tagTotal (D.FS.tag L) (D.FS.vprice L)) ≤
      D.GB.Rerr := by
    unfold TheoremCBlock.GramBracket.Rerr
    exact mul_le_mul hexp hser hser0 (Real.exp_pos _).le
  have hzK : 0 ≤ z * K := mul_nonneg hz hK
  have hRK := mul_le_mul_of_nonneg_left hR hK
  calc _ ≤ _ := hmain
    _ ≤ (D.GB.Rerr + z) * K +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ := by
      nlinarith

omit [DecidableEq P] in
/-- **The field `hJN` of `varStepsAt_credit` from the per-choice coupled bounds** at the scale
`K = (1 + ε) C_X Y`: `Y[J_X ⊗ Ñ] ≥ Y[J_X ⊗ Ñ₀] − (R_err + z) C_X Y − ∑_σ r_σ` for every
`z ≥ R_err ε`. -/
theorem hJN_of_coupled (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    {ε z : ℝ} (hε : 0 ≤ ε) (hzε : D.GB.Rerr * ε ≤ z) (hY : 0 ≤ D.Y L A)
    (r : (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      |diagonalIntegral (tensorLaw (jPiece D L ω m σ)) (blockLift m₀ blk p L A)| ≤
        (1 + ε) * selProd D L ω * D.Y L A *
          tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (outPrice D L ω) j σ + r σ) :
    varJ0 D L A ω m - (D.GB.Rerr + z) * selProd D L ω * D.Y L A -
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ ≤
      varJ D L A ω m := by
  have hCY : 0 ≤ selProd D L ω * D.Y L A := mul_nonneg (selProd_nonneg L ω) hY
  have hK : 0 ≤ (1 + ε) * selProd D L ω * D.Y L A := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hCY
    linarith [mul_assoc (1 + ε) (selProd D L ω) (D.Y L A)]
  have h := abs_varJ_sub_varJ0_le L A ω m hK (le_refl 0) r hterm
  have hR0 : 0 ≤ D.GB.Rerr := BracketEnergy.Rerr_nonneg D
  have hb : (D.GB.Rerr + 0) * ((1 + ε) * selProd D L ω * D.Y L A) ≤
      (D.GB.Rerr + z) * selProd D L ω * D.Y L A := by
    have e : (D.GB.Rerr + 0) * ((1 + ε) * selProd D L ω * D.Y L A) =
        (D.GB.Rerr + D.GB.Rerr * ε) * (selProd D L ω * D.Y L A) := by ring
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hCY
  have := neg_abs_le (varJ D L A ω m - varJ0 D L A ω m)
  linarith

variable (D) in
/-- **The canonical remainder of the coupled terms of `J_X`** (EC's exactness device): for a choice
`σ`, the sum over the tags `j` of the excess `(|E_σ| − (1 + ε) C_X Y wt_j(σ))⁺`. With it the
per-choice coupled bounds hold outright (`hterm_jExcess`), and their content is the budget
`∑_ω π̃_ω ∑_σ jExcess(ω, σ) ≤ c L^{-σ} α` in the field `hrr`. -/
noncomputable def jExcess (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ) (ε : ℝ)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j, max 0 (|diagonalIntegral (tensorLaw (jPiece D L ω m σ)) (blockLift m₀ blk p L A)| -
    (1 + ε) * selProd D L ω * D.Y L A *
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (outPrice D L ω) j σ)

omit [DecidableEq P] in
theorem jExcess_nonneg (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ) (ε : ℝ)
    (σ : ∀ b, Option (D.FS.Ib L b)) : 0 ≤ jExcess D L A ω m ε σ :=
  sum_nonneg fun _ _ => le_max_left _ _

omit [DecidableEq P] in
/-- **The coupled bounds of `J_X` hold at the canonical remainders** (the hypothesis `hterm` of
`hJN_of_coupled` with `r = jExcess`). -/
theorem hterm_jExcess (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ) (ε : ℝ)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    |diagonalIntegral (tensorLaw (jPiece D L ω m σ)) (blockLift m₀ blk p L A)| ≤
      (1 + ε) * selProd D L ω * D.Y L A *
        tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (outPrice D L ω) j σ +
      jExcess D L A ω m ε σ := by
  have h1 := le_max_right 0 (|diagonalIntegral (tensorLaw (jPiece D L ω m σ))
    (blockLift m₀ blk p L A)| - (1 + ε) * selProd D L ω * D.Y L A *
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (outPrice D L ω) j σ)
  have h2 : max 0 (|diagonalIntegral (tensorLaw (jPiece D L ω m σ))
      (blockLift m₀ blk p L A)| - (1 + ε) * selProd D L ω * D.Y L A *
        tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (outPrice D L ω) j σ) ≤
      jExcess D L A ω m ε σ :=
    single_le_sum (f := fun j => max 0 (|diagonalIntegral (tensorLaw (jPiece D L ω m σ))
      (blockLift m₀ blk p L A)| - (1 + ε) * selProd D L ω * D.Y L A *
        tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (outPrice D L ω) j σ))
      (fun _ _ => le_max_left _ _) (mem_univ j)
  linarith

omit [DecidableEq P] in
/-- **The field `hJN` of `VarStepsAt`, proved at the canonical remainders**: for every `ε ≥ 0` and
`z ≥ R_err ε`, `Y[J_X ⊗ Ñ] ≥ Y[J_X ⊗ Ñ₀] − (R_err + z) C_X Y − r_J` with
`r_J = ∑_{σ ≠ ∅} jExcess(ω, σ)`. The analytic content of `lem:record:variance-interface`(ii) at
`J_X` is then the budget of these remainders. -/
theorem hJN_canonical (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    {ε z : ℝ} (hε : 0 ≤ ε) (hzε : D.GB.Rerr * ε ≤ z) (hY : 0 ≤ D.Y L A) :
    varJ0 D L A ω m - (D.GB.Rerr + z) * selProd D L ω * D.Y L A -
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          jExcess D L A ω m ε σ ≤ varJ D L A ω m :=
  hJN_of_coupled L A ω m hε hzε hY (jExcess D L A ω m ε)
    (fun σ _ j _ => hterm_jExcess L A ω m ε σ j)

end Sarkozy.OpsVariance
