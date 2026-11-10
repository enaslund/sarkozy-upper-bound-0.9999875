module

public import Sarkozy.Structured.TheoremCGlue
public import Sarkozy.TheoremCParam.Main

@[expose] public section



open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.TheoremCParam.Structured

open Sarkozy.TheoremC Sarkozy.Structured
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice

/-! ## Least counterexamples -/

/-- `AtCounterexamples` from a statement at the least counterexamples of
`IsLeastCounterexample` (exponents `a = decay`, `θ = densityExponent`). -/
theorem atCounterexamples_of_isLeast (Y : ℕ → Finset ℤ → ℝ) (P : ℕ → Finset ℤ → Prop)
    (h : ∀ᶠ L : ℕ in atTop, ∀ C : ℝ, 1 ≤ C → ∀ A : Finset ℤ,
      IsLeastCounterexample Y a densityExponent C L A → P L A) :
    Param.AtCounterexamples (Params.ofDecay a) Y P := by
  exact (Param.atCounterexamples_ofDecay_iff a Y P).mpr h

/-! ## Constants -/

/-- **The selection factor is the square-step price**: for a set `S` of tail atoms whose
primes have squarefree product `D_E`, `C_S = ∏_{j∈S} p_j^{2a}` (WP-FI's `selectionFactor`)
equals `sq(D_E)^a = R_E^a`, the main price of `prop:record:density-structured` for unchanged
inputs (`mainPrice_unchanged_inputs`). -/
theorem selectionFactor_prod_tail {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    (p : ∀ L, J L → ℕ) (selPre : ℝ) (L : ℕ) (S : Finset (J L))
    (hsq : Squarefree (∏ j ∈ S, p L j)) :
    ∏ j ∈ S, selectionFactor a p selPre L (some j) =
      ((Sarkozy.Functional.leastSquare (∏ j ∈ S, p L j) : ℕ) : ℝ) ^ a := by
  rw [Sarkozy.Functional.leastSquare_of_squarefree hsq]
  simp only [selectionFactor]
  rw [Real.finsetProd_rpow _ _ (fun j _ => Nat.cast_nonneg _)]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (prod_nonneg fun j _ => Nat.cast_nonneg _)]
  norm_num

/-! ## The bracket bound with remainders in the subset terms -/

/-! ## `EnvelopeBound` from the per-term bounds -/

section Envelope

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- The bracket of (CP3) in the form of the bracket expansion:
`Ñ_𝔟 = (μ_𝔟 + ∑_i κu_{𝔟,i}) + ∑_i (κ'_{𝔟,i} - κ_{𝔟,i})`. -/
theorem bracket_N_eq (D : ComparisonData a m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) :
    D.GB.N L b = (D.R.law p L b + ∑ i, D.GB.κu L b i) +
      ∑ i, (D.FS.κ' L b i - D.FS.κ L b i) := by
  unfold GramBracket.N
  rw [← D.GB.N₀_sub L b]
  abel

omit [DecidableEq P] in
/-- The record prices `u_𝔟` of (CP3) are nonnegative. -/
theorem uprice_nonneg (D : ComparisonData a m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) :
    0 ≤ D.GB.uprice L b := by
  unfold GramBracket.uprice
  exact sum_nonneg fun i _ =>
    mul_nonneg (ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1)
      (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
theorem dprice_nonneg (D : ComparisonData a m₀ p pr h E) (L : ℕ) (b : PaperAtom J L)
    (i : D.FS.Ib L b) : 0 ≤ D.FS.dprice L b i := by
  unfold FirstStage.dprice sharpPrice
  exact mul_nonneg (mul_nonneg (ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
    (D.FS.dconst_nonneg L b i)) (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
theorem vprice_nonneg (D : ComparisonData a m₀ p pr h E) (L : ℕ) (b : PaperAtom J L)
    (i : D.FS.Ib L b) : 0 ≤ D.FS.vprice L b i := by
  unfold FirstStage.vprice
  exact mul_nonneg (add_nonneg (ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
    (ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)) (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
/-- The tag totals of the first stage are nonnegative. -/
theorem dT_nonneg (D : ComparisonData a m₀ p pr h E) (j : D.FS.Tag) : 0 ≤ D.FS.dT j := by
  refine le_trans ?_ (D.FS.dT_total 0 j)
  exact sum_nonneg fun b _ => sum_nonneg fun i _ => by
    split_ifs
    · exact dprice_nonneg D 0 b i
    · exact le_rfl

omit [DecidableEq P] in
theorem vT_nonneg (D : ComparisonData a m₀ p pr h E) (j : D.FS.Tag) : 0 ≤ D.FS.vT j := by
  refine le_trans ?_ (D.FS.vT_total 0 j)
  exact sum_nonneg fun b _ => sum_nonneg fun i _ => by
    split_ifs
    · exact vprice_nonneg D 0 b i
    · exact le_rfl

omit [DecidableEq P] in
/-- `B = e^{U₀}(1 + 𝔗(d, v)) ≥ 0`. -/
theorem B_nonneg (D : ComparisonData a m₀ p pr h E) : 0 ≤ D.B := by
  unfold ComparisonData.B GramBracket.B GramBracket.Rerr
  have := tagSeries_nonneg (dT_nonneg D) (vT_nonneg D)
  positivity

omit [DecidableEq P] in
/-- **The bracket factor**: the envelope energy of a selection is at most `K B` plus the
remainders, given the two families of per-term bounds with the factor `K`. -/
theorem envelope_energy_le_B (D : ComparisonData a m₀ p pr h E) (L : ℕ) (A : Finset ℤ)
    (ω : Choice (D.CL.T L)) {K : ℝ} (hK : 0 ≤ K) (r0 : (PaperAtom J L → Bool) → ℝ)
    (r : (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterm0 : ∀ f : PaperAtom J L → Bool,
      |diagonalIntegral (tensorLaw fun b => if f b then
          (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
        else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (atomLift m₀ p L A)| ≤
        K * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) + r0 f)
    (hterm : ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j →
      |diagonalIntegral (tensorLaw (fun b => (σ b).elim
        (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
          (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
        (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))))
          (atomLift m₀ p L A)| ≤
        K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ + r σ) :
    diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (atomLift m₀ p L A) ≤
      K * D.B + (∑ f, r0 f +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ) := by
  have hbr := envelope_energy_le_of_bracket_rem (D.GB.N L) (D.R.law p L)
    (fun b => ∑ i, D.GB.κu L b i) (fun b i => D.FS.κ' L b i - D.FS.κ L b i)
    (bracket_N_eq D L) (D.CL.D L) ω (atomLift m₀ p L A) (D.GB.uprice L) (uprice_nonneg D L)
    hK hK r0 hterm0 (D.FS.tag L) (dprice_nonneg D L) (vprice_nonneg D L) r hterm
  -- `∑_{b ∉ X} u_𝔟 ≤ U₀`
  have hU : (∑ b, if (ω b).isSome then 0 else D.GB.uprice L b) ≤ D.GB.U₀ := by
    refine le_trans ?_ (D.GB.U₀_total L)
    refine sum_le_sum fun b _ => ?_
    split_ifs
    · exact uprice_nonneg D L b
    · exact le_rfl
  have hexp := Real.exp_le_exp.mpr hU
  -- `𝔗(d, v) ≤ 𝔗(d_j, v_j)`
  have htag : tagSeries (tagTotal (D.FS.tag L) (D.FS.dprice L))
      (tagTotal (D.FS.tag L) (D.FS.vprice L)) ≤ tagSeries D.FS.dT D.FS.vT := by
    apply tagSeries_mono
    · intro j
      exact sum_nonneg fun b _ => sum_nonneg fun i _ => by
        split_ifs
        · exact dprice_nonneg D L b i
        · exact le_rfl
    · intro j
      exact sum_nonneg fun b _ => sum_nonneg fun i _ => by
        split_ifs
        · exact vprice_nonneg D L b i
        · exact le_rfl
    · exact fun j => D.FS.dT_total L j
    · exact fun j => D.FS.vT_total L j
  have htag0 : 0 ≤ tagSeries (tagTotal (D.FS.tag L) (D.FS.dprice L))
      (tagTotal (D.FS.tag L) (D.FS.vprice L)) := by
    apply tagSeries_nonneg
    · intro j
      exact sum_nonneg fun b _ => sum_nonneg fun i _ => by
        split_ifs
        · exact dprice_nonneg D L b i
        · exact le_rfl
    · intro j
      exact sum_nonneg fun b _ => sum_nonneg fun i _ => by
        split_ifs
        · exact vprice_nonneg D L b i
        · exact le_rfl
  have hB : D.B = Real.exp D.GB.U₀ + Real.exp D.GB.U₀ * tagSeries D.FS.dT D.FS.vT := rfl
  refine hbr.trans ?_
  rw [hB]
  have e1 : K * Real.exp (∑ b, if (ω b).isSome then 0 else D.GB.uprice L b) ≤
      K * Real.exp D.GB.U₀ := mul_le_mul_of_nonneg_left hexp hK
  have e2 : K * Real.exp (∑ b, if (ω b).isSome then 0 else D.GB.uprice L b) *
      tagSeries (tagTotal (D.FS.tag L) (D.FS.dprice L)) (tagTotal (D.FS.tag L) (D.FS.vprice L)) ≤
      K * Real.exp D.GB.U₀ * tagSeries D.FS.dT D.FS.vT :=
    mul_le_mul e1 htag htag0 (mul_nonneg hK (Real.exp_pos _).le)
  nlinarith

omit [DecidableEq P] in
/-- **`EnvelopeBound` from the per-term bounds with outside law `μ`** (`lem:bracket-energy`,
the algebraic part). Suppose that at every least counterexample, for every selection `ω`
with selected set `X`:
* (`hterms`, first part) the subset terms satisfy
  `|Y[(⊗_X D) ⊗ (⊗_{f-atoms} ∑κu) ⊗ μ_{rest}]| ≤ (1 + ε_L) C_X Y ∏_{f-atoms} u_𝔟 + r⁰_f`;
* (`hterms`, second part) the sharp-first terms with a chosen difference of tag `j`
  satisfy `|Y_σ| ≤ (1 + ε_L) C_X Y wt_j(σ) + r_σ`;
* (`hrem`) the remainders `r_ω = ∑_f r⁰_f + ∑_σ r_σ` add up, with the weights `π̃_ω`, to a
  density-linear remainder.

Then `EnvelopeBound` holds with relative error `ε_L B`. The factor `B = e^{U₀}(1 + 𝔗(d, v))`
comes from `∑_{𝔟 ∉ X} u_𝔟 ≤ U₀` and `𝔗(d, v) ≤ 𝔗(d_j, v_j)` (`envelope_energy_le_B`). -/
theorem envelopeBound_of_terms (D : ComparisonData a m₀ p pr h E)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {cE : ℝ} (hcE : 0 ≤ cE)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (PaperAtom J L → Bool) → ℝ)
    (r : ∀ L, Finset ℤ → Choice (D.CL.T L) → (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      (∀ f : PaperAtom J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (atomLift m₀ p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f) ∧
      (∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
        1 ≤ countVec (D.FS.tag L) σ j →
        |diagonalIntegral (tensorLaw (fun b => (σ b).elim
          (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
          (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))))
            (atomLift m₀ p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
            D.Y L A) * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ + r L A ω σ)))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω *
          (∑ f, r0 L A ω f +
            ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              r L A ω σ) ≤ remainder cE L A)) :
    D.EnvelopeBound := by
  refine ⟨fun L => εE L * D.B, fun L => mul_nonneg (hε0 L) (B_nonneg D), ?_, cE, hcE,
    fun L A ω => ∑ f, r0 L A ω f +
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        r L A ω σ, ?_, hrem⟩
  · simpa using hεt.mul_const D.B
  · filter_upwards [hterms] with L hL
    intro C hC hk A hA hY ω hω
    obtain ⟨h0, h1⟩ := hL C hC hk A hA hY ω hω
    have hY0 : 0 ≤ D.Y L A := by
      have : 0 ≤ C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
        density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent :=
        mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (density_nonneg _ _) _)
      linarith
    have hCX : 0 ≤ ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b :=
      prod_nonneg fun b _ => D.selectionFactor_nonneg L b
    have hK : 0 ≤ (1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
        D.Y L A := mul_nonneg (mul_nonneg (by linarith [hε0 L]) hCX) hY0
    refine (envelope_energy_le_B D L A ω hK (r0 L A ω) (r L A ω) h0 h1).trans (le_of_eq ?_)
    ring

omit [DecidableEq P] in
/-- **The per-selection bound for the subset remainders** (gap 6 of the report): if the
subset term with the records at the unselected atoms of `f` has the remainder
`∏_{𝔟∈f} mass(∑_i κu_{𝔟,i}) · c₁ L^{-1/825} α`, which is the form of the remainder of
`prop:record:density-structured` (`‖ρ‖ C_dc L^{-σ} α` with `‖ρ‖` the product of the masses),
then `∑_f r⁰_f ≤ e^{U₀} c₁ L^{-1/825} α`. The masses are at most the prices `u_𝔟`
(`selectionFactor ≥ 1`), and `∑_𝔟 u_𝔟 ≤ U₀`. -/
theorem sum_subset_remainder_le (D : ComparisonData a m₀ p pr h E) (ha : 0 ≤ a) (L : ℕ)
    (A : Finset ℤ)
    (ω : Choice (D.CL.T L)) {c₁ : ℝ} (hc₁ : 0 ≤ c₁) :
    ∑ f : PaperAtom J L → Bool,
        (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
          remainder c₁ L A ≤
      remainder (Real.exp D.GB.U₀ * c₁) L A := by
  set m : PaperAtom J L → ℝ := fun b => if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)
    with hm
  have hsel1 : ∀ b, 1 ≤ selectionFactor a p D.S.selPre L b := by
    intro b
    cases b with
    | none => exact D.S.one_le_selPre
    | some j =>
      exact Real.one_le_rpow (by exact_mod_cast (D.S.p_prime L j).one_lt.le)
        (by linarith)
  have hmass : ∀ b, mass (∑ i, D.GB.κu L b i) = ∑ i, mass (D.GB.κu L b i) := by
    intro b
    unfold mass
    rw [LinearMap.sum_apply]
  have hm0 : ∀ b, 0 ≤ m b := by
    intro b
    simp only [hm]
    split_ifs
    · exact le_rfl
    · rw [hmass]
      exact sum_nonneg fun i _ => ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1
  have hmu : ∀ b, m b ≤ D.GB.uprice L b := by
    intro b
    simp only [hm]
    split_ifs
    · exact uprice_nonneg D L b
    · rw [hmass]
      unfold GramBracket.uprice
      refine sum_le_sum fun i _ => ?_
      have h0 := ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1
      nlinarith [hsel1 b]
  have hsum : ∑ b, m b ≤ D.GB.U₀ :=
    (sum_le_sum fun b _ => hmu b).trans (D.GB.U₀_total L)
  have hprod : ∏ b, (1 + m b) = ∑ f : PaperAtom J L → Bool, ∏ b, (if f b then m b else 1) := by
    rw [← Fintype.prod_sum (fun b (i : Bool) => if i then m b else 1)]
    apply Finset.prod_congr rfl
    intro b _
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    exact add_comm _ _
  have hrem0 : 0 ≤ remainder c₁ L A := by
    unfold remainder
    exact mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  have hexp : ∏ b, (1 + m b) ≤ Real.exp D.GB.U₀ :=
    (prod_one_add_le_exp m hm0).trans (Real.exp_le_exp.mpr hsum)
  calc ∑ f : PaperAtom J L → Bool,
        (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
          remainder c₁ L A =
      (∑ f : PaperAtom J L → Bool, ∏ b, (if f b then m b else 1)) * remainder c₁ L A := by
        rw [sum_mul]
    _ = (∏ b, (1 + m b)) * remainder c₁ L A := by rw [hprod]
    _ ≤ Real.exp D.GB.U₀ * remainder c₁ L A := mul_le_mul_of_nonneg_right hexp hrem0
    _ = remainder (Real.exp D.GB.U₀ * c₁) L A := by
        unfold remainder
        ring

omit [DecidableEq P] in
/-- **The remainder summation for uniform remainders** (`lem:record:record-expansion`(ii)
with the prices `π̃`): if every selection's remainder is at most `c₀ L^{-1/825} α`, then the
sum weighted by `π̃_ω` is at most `e^S cosh A · c₀ L^{-1/825} α`. Here `π̃ ≤ π̃ q^{2a}`
(`selectionFactor ≥ 1`), so the totals `S`, `A` of (CP4) bound those of `π̃`. -/
theorem sum_selection_remainder_le (D : ComparisonData a m₀ p pr h E) (ha : 0 ≤ a) (L : ℕ)
    (A : Finset ℤ)
    (rE : Choice (D.CL.T L) → ℝ) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hr : ∀ ω, IsSelection ω → rE ω ≤ remainder c₀ L A) :
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * rE ω ≤
      remainder (Real.exp D.CL.S * Real.cosh D.CL.A * c₀) L A := by
  have hπ : ∀ b t e, 0 ≤ D.CL.πt L b t e := D.CL.πt_nonneg L
  have hrem0 : 0 ≤ remainder c₀ L A := by
    unfold remainder
    exact mul_nonneg (mul_nonneg hc₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  have hsel1 : ∀ b, 1 ≤ selectionFactor a p D.S.selPre L b := by
    intro b
    cases b with
    | none => exact D.S.one_le_selPre
    | some j =>
      exact Real.one_le_rpow (by exact_mod_cast (D.S.p_prime L j).one_lt.le)
        (by linarith)
  have hsym : ∑ b, symTotal (D.CL.πt L) b ≤ D.CL.S := by
    refine le_trans (sum_le_sum fun b _ => sum_le_sum fun t _ => ?_) (D.CL.S_total L)
    have := hπ b t .sym
    nlinarith [hsel1 b]
  have hskew0 : 0 ≤ ∑ b, skewTotal (D.CL.πt L) b :=
    sum_nonneg fun b _ => sum_nonneg fun t _ => hπ b t .skew
  have hskew : ∑ b, skewTotal (D.CL.πt L) b ≤ D.CL.A := by
    refine le_trans (sum_le_sum fun b _ => sum_le_sum fun t _ => ?_) (D.CL.A_total L)
    have := hπ b t .skew
    nlinarith [hsel1 b]
  have hmono := sum_monomial_selections_le hπ
  have hexp : Real.exp (∑ b, symTotal (D.CL.πt L) b) * Real.cosh (∑ b, skewTotal (D.CL.πt L) b)
      ≤ Real.exp D.CL.S * Real.cosh D.CL.A := by
    apply mul_le_mul (Real.exp_le_exp.mpr hsym) _ (Real.cosh_pos _).le (Real.exp_pos _).le
    rw [Real.cosh_le_cosh, abs_of_nonneg hskew0, abs_of_nonneg (hskew0.trans hskew)]
    exact hskew
  calc ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * rE ω ≤
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * remainder c₀ L A := by
        refine sum_le_sum fun ω hω => ?_
        exact mul_le_mul_of_nonneg_left (hr ω (mem_filter.mp hω).2) (monomial_nonneg hπ ω)
    _ = (∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω) * remainder c₀ L A := by rw [sum_mul]
    _ ≤ (Real.exp D.CL.S * Real.cosh D.CL.A) * remainder c₀ L A := by
        apply mul_le_mul_of_nonneg_right _ hrem0
        linarith
    _ = remainder (Real.exp D.CL.S * Real.cosh D.CL.A * c₀) L A := by
        unfold remainder
        ring

omit [DecidableEq P] in
/-- **`EnvelopeBound` from the per-term bounds with uniform remainders**:
`envelopeBound_of_terms` with the remainder summation replaced by a bound
`∑_f r⁰_{ω,f} + ∑_σ r_{ω,σ} ≤ c₀ L^{-1/825} α`, uniform in the selection
(`sum_selection_remainder_le`). -/
theorem envelopeBound_of_terms_uniform (D : ComparisonData a m₀ p pr h E) (ha : 0 ≤ a)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (PaperAtom J L → Bool) → ℝ)
    (r : ∀ L, Finset ℤ → Choice (D.CL.T L) → (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      (∀ f : PaperAtom J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (atomLift m₀ p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f) ∧
      (∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
        1 ≤ countVec (D.FS.tag L) σ j →
        |diagonalIntegral (tensorLaw (fun b => (σ b).elim
          (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
          (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))))
            (atomLift m₀ p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
            D.Y L A) * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ + r L A ω σ)))
    (hunif : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∑ f, r0 L A ω f +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          r L A ω σ ≤ remainder c₀ L A)) :
    D.EnvelopeBound := by
  refine envelopeBound_of_terms D εE hε0 hεt
    (cE := Real.exp D.CL.S * Real.cosh D.CL.A * c₀)
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le) hc₀) r0 r hterms ?_
  filter_upwards [hunif] with L hL
  intro C hC hk A hA hY
  exact sum_selection_remainder_le D ha L A _ hc₀ (hL C hC hk A hA hY)

end Envelope

end Sarkozy.TheoremCParam.Structured
