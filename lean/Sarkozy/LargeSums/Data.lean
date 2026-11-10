module

public import Sarkozy.LargeSums.Pieces

@[expose] public section

/-!
# The large pieces of the data: `q_E > N^τ` and the `q^{1/4}`-weighted summability

LP (8 November 2026). The two inputs of Rankin's trick (`lem:record:density-lp`) that come from
the comparison data:

* **`large_of_not_small`** (`def:record:structured-energy`(a)): a piece that is not small has
  `N^τ < ∏_𝔟 qf_𝔟(φ_𝔟)`, with `q_𝔟` the product of the primes of `𝔟` with `e_p = 1`. This is
  DC1's `moduli_dichotomy` at DC2's factorization `D_𝔟 = q_𝔟 c_𝔟` (`crtModuli_eq_atomQ_mul_atomC`,
  `squarefree_atomQ`, `isSquare_atomC` from the parity condition, `∏_𝔟 c_𝔟 = Q_cl⁰`);
* **`prod_atomPr_le_exp`** (`def:cp8`(c), the summability, as the paper uses it after
  `lem:record:density-lp`: "`Π_H` is then finite by the summability (c) of `def:cp8`"):
  `∏_𝔟 (1 + q_𝔟^{1/4} Pr_𝔟) ≤ exp(D.SM.bound)` for every increment `Q` whose masses are at most
  the comparison prices `s_𝔟 + a_𝔟 + T_{L,𝔟} + T_{R,𝔟}`. The masses are bounded by the prices
  because every selection factor is at least `1`; `q_𝔟 = oneWeight` (`oneWeight_eq_atomQ`).
-/

namespace Sarkozy.LargeSums

open Finset Function
open scoped BigOperators
open Sarkozy.TheoremC Sarkozy.Structured Sarkozy.DensityChain Sarkozy.DensityFibre
  Sarkozy.EnvelopeInputs Sarkozy.EnvelopeInputsBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
  Sarkozy.EnvelopeEnergiesPaper Sarkozy.DensityChain2 Sarkozy.Comparison Sarkozy.Functional
  Sarkozy.CancellationSteps Sarkozy.BracketEnergy

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Summability

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- `q_𝔟` as a real number. -/
noncomputable def atomQR (b : BlockAtom Bk J L) : ℝ := (atomQ blk p D.S.pp D.S.ep L b : ℝ)

omit [DecidableEq P] in
theorem atomQR_nonneg (b : BlockAtom Bk J L) : 0 ≤ atomQR D L b := Nat.cast_nonneg _

omit [DecidableEq P] [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk]
  [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
/-- **`q_𝔟` is the weight of `def:cp8`(c)** (`oneWeight`). -/
theorem oneWeight_eq_atomQ (pp ep : J₀ → ℕ) (b : BlockAtom Bk J L) :
    TheoremCBlock.oneWeight blk p pp ep L b = (atomQ blk p pp ep L b : ℝ) := by
  cases b with
  | inl β =>
    change ∏ i ∈ univ.filter (fun i : BlockIdx blk β => ep i.1 = 1), (pp i.1 : ℝ) =
      ((∏ i ∈ univ.filter (fun i : BlockIdx blk β => ep i.1 = 1), pp i.1 : ℕ) : ℝ)
    rw [Nat.cast_prod]
  | inr j => rfl

/-- The comparison prices of an atom that bound the mass of an increment:
`s_𝔟 + a_𝔟 + T_{L,𝔟} + T_{R,𝔟}` (the last four terms of `def:cp8`(c)). -/
noncomputable def incPrice (b : BlockAtom Bk J L) : ℝ :=
  symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b +
    TheoremCBlock.Structured.envPriceL D L b + TheoremCBlock.Structured.envPriceR D L b

omit [DecidableEq P] in
/-- **The masses of the records at an atom are at most the prices of `def:cp8`(c)**: with
`sel_𝔟 ≥ 1`, `Pr_𝔟 ≤ p_𝔟 + ∑ v + ∑ d + u + (s + a + T_L + T_R)`, when
`‖Q_𝔟‖ ≤ s + a + T_L + T_R`. -/
theorem atomPr_le (ha : 0 ≤ a) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (b : BlockAtom Bk J L) (hQ : mass (Qb b) ≤ incPrice D L b) :
    atomPr D L Qb b ≤ D.FS.pvar L b + ∑ i, D.FS.vprice L b i + ∑ i, D.FS.dprice L b i +
      D.GB.uprice L b + symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b +
      ∑ i, D.ME.cL L b i * mass (D.ME.κL L b i) * TheoremCBlock.selectionFactor a p D.S.selPre L b +
      ∑ i, D.ME.cR L b i * mass (D.ME.κR L b i) *
        TheoremCBlock.selectionFactor a p D.S.selPre L b := by
  have hs := D.one_le_selectionFactor ha L b
  set s := TheoremCBlock.selectionFactor a p D.S.selPre L b with hsdef
  have hm : ∀ {X : Type} [Fintype X] {κ : SlotMeasure X}, IsNonneg κ → mass κ ≤ mass κ * s :=
    fun hκ => le_mul_of_one_le_right
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg hκ) hs
  have hu : ∑ k, mass (D.GB.κu L b k) ≤ D.GB.uprice L b :=
    sum_le_sum fun k _ => hm (D.GB.κu_pos L b k).1
  have hdv : ∑ i, (D.FS.dconst L b i * mass (D.FS.κ L b i) +
      (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i))) ≤
      ∑ i, D.FS.vprice L b i + ∑ i, D.FS.dprice L b i := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    have h1 : D.FS.dconst L b i * mass (D.FS.κ L b i) ≤ D.FS.dprice L b i := by
      unfold TheoremCBlock.FirstStage.dprice sharpPrice
      have := mul_le_mul_of_nonneg_left (hm (D.FS.κ_pos L b i).1) (D.FS.dconst_nonneg L b i)
      nlinarith
    have h2 : mass (D.FS.κ' L b i) + mass (D.FS.κ L b i) ≤ D.FS.vprice L b i := by
      unfold TheoremCBlock.FirstStage.vprice
      have := hm (D.FS.κ_pos L b i).1
      have := hm (D.FS.κ'_pos L b i).1
      nlinarith
    linarith
  have hp0 := D.pvar_nonneg L b
  have hQ' : mass (Qb b) ≤ symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b +
      (∑ i, D.ME.cL L b i * mass (D.ME.κL L b i) * s +
        ∑ i, D.ME.cR L b i * mass (D.ME.κR L b i) * s) := by
    refine hQ.trans (le_of_eq ?_)
    unfold incPrice TheoremCBlock.Structured.envPriceL TheoremCBlock.Structured.envPriceR
    ring
  unfold atomPr
  linarith

omit [DecidableEq P] in
/-- **`Π_H ≤ exp(D.SM.bound)`** (`def:cp8`(c), the summability): for an increment `Q` whose
masses are at most `s + a + T_L + T_R`. -/
theorem prod_atomPr_le_exp (ha : 0 ≤ a) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hQ0 : ∀ b, 0 ≤ mass (Qb b)) (hQ : ∀ b, mass (Qb b) ≤ incPrice D L b) :
    ∏ b, (1 + atomQR D L b ^ ((1 : ℝ) / 4) * atomPr D L Qb b) ≤ Real.exp D.SM.bound := by
  have hPr0 : ∀ b, 0 ≤ atomPr D L Qb b := by
    intro b
    unfold atomPr
    refine add_nonneg (add_nonneg (sum_nonneg fun k _ =>
      TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1) (hQ0 b))
      (sum_nonneg fun i _ => add_nonneg (mul_nonneg (D.FS.dconst_nonneg L b i)
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1))
        (add_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
          (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)))
  have hq4 : ∀ b, 0 ≤ atomQR D L b ^ ((1 : ℝ) / 4) := fun b =>
    Real.rpow_nonneg (atomQR_nonneg D L b) _
  refine (prod_one_add_le_exp _ _ fun b _ => mul_nonneg (hq4 b) (hPr0 b)).trans ?_
  refine Real.exp_le_exp.mpr ((sum_le_sum fun b _ => ?_).trans (D.SM.summable L))
  rw [oneWeight_eq_atomQ]
  exact mul_le_mul_of_nonneg_left (atomPr_le D L ha Qb b (hQ b)) (hq4 b)

omit [DecidableEq P] in
/-- The mass of a positive record is the sum of the absolute values of its density. -/
theorem mass_eq_sum_abs {X : Type} [Fintype X] [DecidableEq X] {κ : SlotMeasure X}
    (hκ : IsPositiveRecord κ) : mass κ = ∑ z, |lawDensity κ z| :=
  (totalVariation_lawDensity_of_positive hκ).symm

omit [DecidableEq P] in
/-- The wrapping increments satisfy the price condition (`wrapInc_price_le` at `s = 1`). -/
theorem mass_wrapInc_le (ha : 0 ≤ a) (b : BlockAtom Bk J L) :
    mass (TheoremCBlock.Structured.wrapInc D L b) ≤ incPrice D L b := by
  have h1 := wrapInc_price_le D L b zero_le_one (D.one_le_selectionFactor ha L b)
  rw [mul_one, ← mass_eq_sum_abs (isPositiveRecord_wrapInc D L b)] at h1
  have h2 : TheoremCBlock.Structured.wrapPrice D L b =
      symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b := by
    unfold TheoremCBlock.Structured.wrapPrice symTotal skewTotal
    rw [sum_add_distrib]
  have h3 := TheoremCBlock.Structured.envPriceL_nonneg D L b
  have h4 := TheoremCBlock.Structured.envPriceR_nonneg D L b
  unfold incPrice
  linarith

omit [DecidableEq P] in
/-- The left envelope increments satisfy the price condition (`envIncL_price_le` at `s = 1`). -/
theorem mass_envIncL_le (ha : 0 ≤ a) (b : BlockAtom Bk J L) :
    mass (TheoremCBlock.Structured.envIncL D L b) ≤ incPrice D L b := by
  have h1 := envIncL_price_le D L b zero_le_one (D.one_le_selectionFactor ha L b)
  rw [mul_one, ← mass_eq_sum_abs (isPositiveRecord_envIncL D L b)] at h1
  have h2 : 0 ≤ symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b := by
    have := TheoremCBlock.Structured.wrapPrice_nonneg D L b
    unfold TheoremCBlock.Structured.wrapPrice at this
    unfold symTotal skewTotal
    rw [← sum_add_distrib]
    exact this
  have h4 := TheoremCBlock.Structured.envPriceR_nonneg D L b
  unfold incPrice
  linarith

omit [DecidableEq P] in
/-- The right envelope increments satisfy the price condition (`envIncR_price_le` at `s = 1`). -/
theorem mass_envIncR_le (ha : 0 ≤ a) (b : BlockAtom Bk J L) :
    mass (TheoremCBlock.Structured.envIncR D L b) ≤ incPrice D L b := by
  have h1 := envIncR_price_le D L b zero_le_one (D.one_le_selectionFactor ha L b)
  rw [mul_one, ← mass_eq_sum_abs (isPositiveRecord_envIncR D L b)] at h1
  have h2 : 0 ≤ symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b := by
    have := TheoremCBlock.Structured.wrapPrice_nonneg D L b
    unfold TheoremCBlock.Structured.wrapPrice at this
    unfold symTotal skewTotal
    rw [← sum_add_distrib]
    exact this
  have h3 := TheoremCBlock.Structured.envPriceL_nonneg D L b
  unfold incPrice
  linarith

end Summability

section Moduli

omit [DecidableEq P] in
/-- **A piece that is not small is large** (`def:record:structured-energy`(a); DC1's
`moduli_dichotomy`, DC2's factorization): `N^τ < ∏_𝔟 qf_𝔟(φ_𝔟)`, `N = KL`. -/
theorem large_of_not_small (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hpar : ParityCondition D.S.ep) (L : ℕ) (φ : ∀ b, HPiece D L b)
    (hφ : ¬ smallPiece m₀ blk D L φ) :
    ((blockScale * L : ℕ) : ℝ) ^ stageTau < ∏ b, qf D L (atomQR D L) b (φ b) := by
  have h0 := prefix_pairwise (hpair L)
  rcases moduli_dichotomy (crtModuli m₀ blk paperTail L) (atomQ blk paperTail D.S.pp D.S.ep L)
      (atomC m₀ blk D.S.ep L) (crtModuli_eq_atomQ_mul_atomC D.S.m₀_eq L)
      (squarefree_atomQ D.S.m₀_eq D.S.pp_prime D.S.ep_pos h0 D.S.p_prime L)
      (isSquare_atomC D.S.m₀_eq hpar L) (atomC_ne_zero D.S.ep L)
      (coprime_atomQ_atomC D.S.m₀_eq D.S.ep_pos h0 L) (crtModuli_pairwise blk (hpair L))
      (le_of_eq (prod_atomC_eq D.S.ep L)) (((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (hTermAtoms D L φ) with hs | hl
  · exact absurd hs hφ
  · refine hl.trans_le (le_of_eq (prod_congr rfl fun b _ => ?_))
    unfold qf atomQR hTermAtoms
    cases hb : hpieceIsMu D L b (φ b) <;> simp [hb]

end Moduli

end Sarkozy.LargeSums
