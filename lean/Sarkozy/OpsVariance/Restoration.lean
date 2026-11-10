module

public import Sarkozy.OpsVariance.Steps
public import Sarkozy.Variance.GainFlat
public import Sarkozy.Variance.BackgroundBlocks

@[expose] public section

/-!
# The restoration bound `hres` from `lem:var-gain`(a) at the paper's objects

`paper/sections/22_variance.tex`, `lem:var-gain`(a) and its proof, `cor:var-classes`(i),(ii),
`prop:background-variance`(b) ("The exterior contains no fold diagonal"), `lem:record:restoration`;
`paper/sections/10_comparison_lemmas.tex`, (E1), (E2), (P3), (P4).

The field `hres` of `VarStepsAt` at the paper's objects (`varStepsAt_credit`) is
`∑_R π̃_ω Y[J_X ⊗ Ñ₀] ≥ (b̃ − z)(∑_R π_ω) Y − r₀`. Here it is derived, for a class of selections
with a common support `X` and common prices `π̃_ω = γ₀` (the hypothesis of `lem:var-gain`), from:

* the eligible record laws `Π_{ω,𝔅}` on the blocks of `X` (nonnegative weights `w ω 𝔅`, symmetric at
  `ι`), whose half marginals at `ι` are the half marginals `envM` of the norm envelopes of `ω`
  (`def:cp4`(b): "diagonal copies of actual half marginals of `t`, in the applications");
* (Cen): `‖T_{ω,𝔅} − 𝒥‖ ≤ κ_{ω,𝔅} ≤ κ < 1` (`lem:record:old-f-marginal`(d) for the folds,
  `lem:record:paired-e-bridge`(b) for the matchings);
* (Res): `∑_R Y[⊗_X Π_ω ⊗ μ] ≥ (l₀ − z₁) |R| Y` (`lem:record:restoration`, or
  `lem:record:paired-e-joint`(b) with `l₀ − C ε_X` for the aligned matchings);
* (E1) with `μ` outside for the selected diagonals, **with remainders** `r_μ(ω)`:
  `Y[Diag_X(envM ω) ⊗ μ] ≤ (1 + z₂) C_X Y + r_μ(ω)` (EC's `E1Sub` at `f = ∅`, `FrontCredit.lean`).

The proof is that of `lem:var-gain`(a) (W1's `var_gain_a_blocks`, here with additive remainders, as
`def:robust` requires): (P3) with (P4) for each `ω` (W1's `energy_le_product_records`), the
average, and (E2) to pass from `μ` to `Ñ₀ = μ + (Ñ₀ − μ)` outside `X` (`varJmu_le_varJ0`; the
exterior `Ñ₀ − μ = ∑_i κu_i` is a positive reserved-diagonal measure). The gain is
`l̄ = (l₀/C − κ)/(1 − κ)` (W1's `gainBar`), the error `z ≥ (z₁ + κ z₂)/(1 − κ)`, and the remainder
`r₀ = γ₀ κ/(1 − κ) ∑_R r_μ(ω)`.

This is the class-cost credit of `prop:background-variance`(b) (fold classes) and of
`cor:var-classes`(ii) (aligned matching classes, the selected term only). The background terms of
`prop:background-variance`(a) (the extra `∑_r W(m, r; c_E) p_E(m, r)`) are not included: W1's
`background_variance_a_blocks` has them, without remainders.
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

theorem reservedCut_isFamilyCut : IsFamilyCut reservedCut := Or.inr (Or.inr rfl)

/-- A nonnegative measure carried by the reflection-fixed labellings of `c` is positive at `c`. -/
theorem positive_of_diagonal {X : Type} [Fintype X] [DecidableEq X] (c : ReflectionCut Slot)
    {κ : SlotMeasure X} (h0 : IsNonneg κ) (hd : IsDiagonalAt c κ) : c.Positive κ := by
  rw [eq_diagonalLaw_of_isDiagonalAt c hd]
  exact c.diagonalLaw_positive fun x => h0 _ fun _ => by split_ifs <;> norm_num

omit [DecidableEq P] in
/-- `Ñ₀ − μ = ∑_i κu_i ⪰_ι 0` (`def:cp3`: positive reserved-diagonal records). -/
theorem positive_sum_κu (L : ℕ) (b : BlockAtom Bk J L) :
    reservedCut.Positive (∑ i, D.GB.κu L b i) := by
  classical
  have h : ∀ s : Finset (D.GB.Iu L b), reservedCut.Positive (∑ i ∈ s, D.GB.κu L b i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [sum_empty]
      refine ⟨fun F G => ?_, fun F => ?_⟩
      · simp [ReflectionCut.form]
      · simp [ReflectionCut.form]
    | insert i s hi ih =>
      rw [sum_insert hi]
      exact (positive_of_diagonal reservedCut (D.GB.κu_pos L b i).1 (D.GB.κu_diag L b i)).add ih
  exact h univ

omit [DecidableEq P] in
/-- `Ñ₀ = μ + ∑_i κu_i` (`def:cp3`). -/
theorem N₀_eq (L : ℕ) (b : BlockAtom Bk J L) :
    D.GB.N₀ L b = D.R.law p L b + ∑ i, D.GB.κu L b i := by
  rw [← D.GB.N₀_sub L b]
  abel

omit [DecidableEq P] in
/-- `Ñ₀ ⪰_ι 0`. -/
theorem N₀_positive (L : ℕ) (b : BlockAtom Bk J L) : reservedCut.Positive (D.GB.N₀ L b) := by
  rw [N₀_eq]
  exact (D.law_positive reservedCut_isFamilyCut L b).add (positive_sum_κu L b)

omit [DecidableEq P] in
/-- **(E2)**: `Y[J_X ⊗ Ñ₀] ≥ 0`. -/
theorem varJ0_nonneg (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hm : ∀ b ∈ Choice.support ω, ∀ x, 0 ≤ m b x) : 0 ≤ varJ0 D L A ω m := by
  unfold varJ0
  apply energy_nonneg_of_positive reservedCut
  intro b
  by_cases hb : b ∈ Choice.support ω
  · simp only [hb, ↓reduceIte]
    exact positive_indepLaw reservedCut (hm b hb)
  · simp only [hb, ↓reduceIte]
    exact N₀_positive L b

omit [DecidableEq P] in
/-- **(E2), `μ` to `Ñ₀` outside `X`**: `Y[J_X ⊗ μ] ≤ Y[J_X ⊗ Ñ₀]`, since `Ñ₀ − μ ⪰_ι 0` and
`J_X ⪰_ι 0` (the exterior expansion with no kept set, W1's `exterior_expansion_ge_blocks`). Here
`Y[J_X ⊗ μ]` is W1's `recFam … X ∅` energy with `μ` outside. -/
theorem varJmu_le_varJ0 (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (w : ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hm : ∀ b ∈ Choice.support ω, ∀ x, 0 ≤ m b x) :
    diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) (Choice.support ω) ∅ w m))
        (blockLift m₀ blk p L A) ≤ varJ0 D L A ω m := by
  classical
  have h := exterior_expansion_ge_blocks reservedCut (D.R.law p L) (fun b => ∑ i, D.GB.κu L b i)
    (Choice.support ω) m (fun _ _ => 0) hm (fun _ _ _ => le_refl 0)
    (fun b _ => D.law_positive reservedCut_isFamilyCut L b) (fun _ => 0) (fun _ => le_refl 0)
    (fun b _ => by
      have e : (∑ i, D.GB.κu L b i) - (0 : ℝ) • reservedCut.diagonalLaw (fun _ => 0) =
          ∑ i, D.GB.κu L b i := by
        rw [zero_smul, sub_zero]
      rw [e]
      exact positive_sum_κu L b)
    {fun _ => false} (fun g hg _ _ => by rw [mem_singleton.mp hg]) (blockLift m₀ blk p L A)
  rw [sum_singleton] at h
  have e1 : setCoeff (fun _ : BlockAtom Bk J L => (0 : ℝ)) (fun _ => false) = 1 := by
    simp [setCoeff]
  have e2 : diagFamZ reservedCut (D.R.law p L) (Choice.support ω) (indSet fun _ => false) ∅ m
      (fun _ _ => 0) = recFam reservedCut (D.R.law p L) (Choice.support ω) ∅ w m := by
    funext b
    simp [diagFamZ, recFam, indSet_false]
  rw [e1, one_mul, e2] at h
  unfold varJ0
  convert h using 3
  funext b
  split_ifs
  · rfl
  · exact N₀_eq L b

omit [DecidableEq P] in
/-- The half marginal of a norm envelope has total mass one. -/
theorem sum_envM {L : ℕ} {ω : Choice (D.CL.T L)} {b : BlockAtom Bk J L}
    (hb : b ∈ Choice.support ω) : ∑ x, envM D L ω b x = 1 := by
  rcases hω : ω b with _ | ⟨t, e⟩
  · exact absurd (by simpa [Choice.support] using hb) (by simp [hω])
  · unfold envM
    rw [hω]
    simp only [Option.elim_some]
    unfold halfMarginalPlus
    rw [← map_sum]
    have h1 : (∑ x : reservedCut.Half → BlockLabel m₀ blk p L b,
        fun z : Slot → BlockLabel m₀ blk p L b =>
          if (fun v : reservedCut.Half => z v.1) = x then (1 : ℝ) else 0) = fun _ => 1 := by
      funext z
      rw [Finset.sum_apply]
      simp
    rw [h1]
    exact (D.CL.D_prob L b t e).2

omit [DecidableEq P] in
/-- **The field `hres` of `VarStepsAt` from `lem:var-gain`(a) at the paper's objects, with
remainders.** For a nonempty class
`R` of selections with common support `X` and common price `π̃_ω = γ₀`, eligible record laws
`w ω 𝔅` on `X` with half marginals `envM ω 𝔅`, symmetric, of centred norm `≤ κ < 1` (Cen), the
restoration bound (Res) with `μ` outside, and (E1) with `μ` outside for the selected diagonals with
remainders `r_μ`, the restoration field holds with `b̃ = l̄ = (l₀/C − κ)/(1 − κ)`, any
`z ≥ (z₁ + κ z₂)/(1 − κ)` and `r₀ = γ₀ κ/(1 − κ) ∑_R r_μ`. -/
theorem hres_of_restoration {L : ℕ} {A : Finset ℤ} (R : Finset (Choice (D.CL.T L)))
    (hR : R.Nonempty) (X : Finset (BlockAtom Bk J L)) (hX : ∀ ω ∈ R, Choice.support ω = X)
    {γ₀ : ℝ} (hγ : ∀ ω ∈ R, monomial (D.CL.πt L) ω = γ₀)
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
    {C l₀ z₁ z₂ z : ℝ} (rμ : Choice (D.CL.T L) → ℝ) (hrμ : ∀ ω ∈ R, 0 ≤ rμ ω)
    (hY : 0 ≤ D.Y L A) (hCX : 1 ≤ ∏ b ∈ X, selectionFactor a p D.S.selPre L b)
    (hC : ∏ b ∈ X, selectionFactor a p D.S.selPre L b ≤ C) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂)
    (hz : (z₁ + κ * z₂) / (1 - κ) ≤ z)
    (hRes : (l₀ - z₁) * D.Y L A * R.card ≤ ∑ ω ∈ R,
      diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X (w ω) (envM D L ω)))
        (blockLift m₀ blk p L A))
    (hE1 : ∀ ω ∈ R, diagonalIntegral (tensorLaw (diagFam reservedCut (D.R.law p L) X X
        (envM D L ω))) (blockLift m₀ blk p L A) ≤
      (1 + z₂) * (∏ b ∈ X, selectionFactor a p D.S.selPre L b) * D.Y L A + rμ ω) :
    (gainBar l₀ C κ - z) * (∑ ω ∈ R, monomial (D.CL.π L) ω) * D.Y L A -
        γ₀ * (κ / (1 - κ)) * ∑ ω ∈ R, rμ ω ≤
      ∑ ω ∈ R, monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω) := by
  set CX := ∏ b ∈ X, selectionFactor a p D.S.selPre L b with hCXdef
  set Y := D.Y L A
  set F := blockLift m₀ blk p L A
  have h1κ : 0 < 1 - κ := by linarith
  have hCpos : 0 < C := by linarith
  have hγ₀ : 0 ≤ γ₀ := by
    obtain ⟨ω, hω⟩ := hR
    rw [← hγ ω hω]
    exact monomial_πt_nonneg L ω
  have hn' : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have hμ : ∀ b, b ∉ X → reservedCut.Positive (D.R.law p L b) := fun b _ =>
    D.law_positive reservedCut_isFamilyCut L b
  -- the products `J` with `μ` outside, and their comparison with `Ñ₀`
  set Jμ : Choice (D.CL.T L) → ℝ := fun ω =>
    diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X ∅ (w ω) (envM D L ω))) F
    with hJμ
  have hJO : ∀ ω ∈ R, Jμ ω ≤ varJ0 D L A ω (envM D L ω) := by
    intro ω hω
    have h := varJmu_le_varJ0 (D := D) L A ω (w ω) (envM D L ω)
      (fun b _ x => envM_nonneg L ω b x)
    rw [hX ω hω] at h
    exact h
  have hJO0 : ∀ ω, 0 ≤ varJ0 D L A ω (envM D L ω) := fun ω =>
    varJ0_nonneg L A ω (envM D L ω) fun b _ x => envM_nonneg L ω b x
  -- (P3) with (P4) for each selection
  have hP : ∀ ω ∈ R, diagonalIntegral (tensorLaw (recFam reservedCut (D.R.law p L) X X (w ω)
      (envM D L ω))) F ≤ (1 - κ) * Jμ ω + κ * ((1 + z₂) * CX * Y + rμ ω) := by
    intro ω hω
    have hmpos : ∀ b ∈ X, 0 < ∑ x, envM D L ω b x := fun b hb => by
      rw [sum_envM (by rw [hX ω hω]; exact hb)]
      exact one_pos
    have h3 := energy_le_product_records reservedCut (D.R.law p L) X hμ F (w ω) (envM D L ω)
      (hw ω hω) (hp ω hω) (hn ω hω) (ht ω hω) hmpos (κj ω) (hcen ω hω) (hκ ω hω)
    have h4 := hE1 ω hω
    have := mul_le_mul_of_nonneg_left h4 hκ0
    linarith
  have hsum := sum_le_sum hP
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
  -- the price sums
  have hπsum : ∑ ω ∈ R, monomial (D.CL.π L) ω = R.card * (γ₀ * CX) := by
    rw [sum_congr rfl fun ω hω => by rw [monomial_π_eq, hγ ω hω, selProd, hX ω hω],
      sum_const, nsmul_eq_mul]
  have hJsum : γ₀ * ∑ ω ∈ R, Jμ ω ≤
      ∑ ω ∈ R, monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω) := by
    rw [mul_sum]
    exact sum_le_sum fun ω hω => by
      rw [hγ ω hω]
      exact mul_le_mul_of_nonneg_left (hJO ω hω) hγ₀
  have hJO0s : 0 ≤ ∑ ω ∈ R, monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω) :=
    sum_nonneg fun ω _ => mul_nonneg (monomial_πt_nonneg L ω) (hJO0 ω)
  have hrsum : 0 ≤ ∑ ω ∈ R, rμ ω := sum_nonneg hrμ
  rw [hπsum]
  -- the scalar step of `lem:var-gain`(a)
  have hz0 : 0 ≤ z := le_trans (div_nonneg (by nlinarith) h1κ.le) hz
  unfold gainBar
  by_cases hl : 0 ≤ l₀
  · -- `(1 − κ) ∑ Jμ ≥ (l₀ − z₁) |R| Y − κ (1 + z₂) C_X Y |R| − κ ∑ r_μ`
    have hlow : (1 - κ) * ∑ ω ∈ R, Jμ ω ≥
        (l₀ - z₁) * Y * R.card - R.card * (κ * ((1 + z₂) * CX * Y)) - κ * ∑ ω ∈ R, rμ ω := by
      have : κ * ∑ ω ∈ R, ((1 + z₂) * CX * Y + rμ ω) =
          R.card * (κ * ((1 + z₂) * CX * Y)) + κ * ∑ ω ∈ R, rμ ω := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
        ring
      linarith
    -- `((l₀/C − κ)/(1 − κ) − z) C_X ≤ ((l₀ − z₁) − κ (1 + z₂) C_X)/(1 − κ)`
    have hA : l₀ / C * CX ≤ l₀ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hCpos]
      nlinarith
    have hB : z₁ ≤ z₁ * CX := by nlinarith
    have hzC : (z₁ + κ * z₂) * CX ≤ z * (1 - κ) * CX := by
      have := (div_le_iff₀ h1κ).mp hz
      have hCX0 : 0 ≤ CX := by linarith
      nlinarith
    have key : ((l₀ / C - κ) / (1 - κ) - z) * CX * (1 - κ) ≤
        (l₀ - z₁) - κ * ((1 + z₂) * CX) := by
      have e : ((l₀ / C - κ) / (1 - κ) - z) * CX * (1 - κ) =
          (l₀ / C * CX - κ * CX) - z * (1 - κ) * CX := by
        field_simp
      rw [e]
      nlinarith
    have key2 : ((l₀ / C - κ) / (1 - κ) - z) * (R.card * (γ₀ * CX)) * Y * (1 - κ) ≤
        γ₀ * ((l₀ - z₁) * Y * R.card - R.card * (κ * ((1 + z₂) * CX * Y))) := by
      have := mul_le_mul_of_nonneg_right key (mul_nonneg (mul_nonneg hn'.le hγ₀) hY)
      nlinarith
    have hfin : ((l₀ / C - κ) / (1 - κ) - z) * (R.card * (γ₀ * CX)) * Y * (1 - κ) -
        γ₀ * (κ / (1 - κ)) * (∑ ω ∈ R, rμ ω) * (1 - κ) ≤
        γ₀ * ((1 - κ) * ∑ ω ∈ R, Jμ ω) := by
      have e : γ₀ * (κ / (1 - κ)) * (∑ ω ∈ R, rμ ω) * (1 - κ) = γ₀ * κ * ∑ ω ∈ R, rμ ω := by
        field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left hlow hγ₀
      nlinarith
    have hfin' : ((l₀ / C - κ) / (1 - κ) - z) * (R.card * (γ₀ * CX)) * Y -
        γ₀ * (κ / (1 - κ)) * (∑ ω ∈ R, rμ ω) ≤ γ₀ * ∑ ω ∈ R, Jμ ω := by
      have e : γ₀ * ((1 - κ) * ∑ ω ∈ R, Jμ ω) = (γ₀ * ∑ ω ∈ R, Jμ ω) * (1 - κ) := by ring
      rw [e] at hfin
      have e2 : ((l₀ / C - κ) / (1 - κ) - z) * (R.card * (γ₀ * CX)) * Y * (1 - κ) -
          γ₀ * (κ / (1 - κ)) * (∑ ω ∈ R, rμ ω) * (1 - κ) =
          (((l₀ / C - κ) / (1 - κ) - z) * (R.card * (γ₀ * CX)) * Y -
            γ₀ * (κ / (1 - κ)) * (∑ ω ∈ R, rμ ω)) * (1 - κ) := by ring
      rw [e2] at hfin
      exact le_of_mul_le_mul_right hfin h1κ
    linarith
  · -- `l̄ < 0`: the left side is nonpositive and `Y[J_X ⊗ Ñ₀] ≥ 0`
    push Not at hl
    have hlb : (l₀ / C - κ) / (1 - κ) - z ≤ 0 := by
      have h5 : l₀ / C < 0 := div_neg_of_neg_of_pos hl hCpos
      have h6 : (l₀ / C - κ) / (1 - κ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h1κ.le
      linarith
    have hCX0 : 0 ≤ CX := by linarith
    have h7 : ((l₀ / C - κ) / (1 - κ) - z) * (R.card * (γ₀ * CX)) * Y ≤ 0 := by
      have : 0 ≤ R.card * (γ₀ * CX) * Y := mul_nonneg (mul_nonneg hn'.le (mul_nonneg hγ₀ hCX0)) hY
      nlinarith
    have h8 : 0 ≤ γ₀ * (κ / (1 - κ)) * ∑ ω ∈ R, rμ ω :=
      mul_nonneg (mul_nonneg hγ₀ (div_nonneg hκ0 h1κ.le)) hrsum
    linarith

end Sarkozy.OpsVariance
