module

public import Sarkozy.PaperFrame.Reference
public import Sarkozy.RecordExpansion.Bound

@[expose] public section

/-!
# The record comparison and the joint closing hypothesis (Theorem C)

This module proves, for the concrete energies of `Sarkozy.Comparison.ConcreteFrame` over a
generic atom frame (atoms `Atom L`, alphabets `Xb L b`, lift `F`, reference family `μ`,
reference energy `Y = energyFirst μ F`), the two estimates of `thm:record:criterion`
(`paper/sections/11_comparison_proof.tex`) that concern the comparison law, and their
combination into the hypothesis of `cor:joint-closing`:

* `comparison_estimate` — hypothesis (i) of `thm:record:criterion`,
  `|Y_ν - Y_λ| ≤ (𝓔 + o(1)) Y`, from `lem:record:record-expansion` (i) and (ii) without the
  classes of (CP5) (`Sarkozy.RecordExpansion.abs_energy_sub_le_of_terms`,
  `abs_term_le_envelope`): the expansion of `ν - λ` over the selections of (CP4)(c), the
  vanishing of the terms with an odd number of skew types, the brackets of (CP3) and
  (CP4)(b), and the selection monomials summed into `e^S cosh A - 1`. Here
  `𝓔 ≥ B(e^S cosh A - 1)` is the class-free complete polynomial at the totals `S`, `A`
  (which bound the scale-`L` totals at every scale, `def:price`(c));
* `joint_of_comparison_mean` — the hypothesis of `cor:joint-closing` from (i) and the
  mean-credit bound (CP7) ((ii) of `thm:record:criterion`), with the joint constant
  `jointConstantC k 𝓔 m = (1 - 2^{-k}) 𝓔 + (1 - m)/2^k`, for which the closing number of
  `cor:joint-closing` is the paper's `Θ` of `thm:comparison` (`jointTheta_jointConstantC`);
* `joint_estimate` — the two combined.

**Robust errors.** As everywhere in `Sarkozy.Comparison.Criterion`, a robust bound
`Ξ ≤ (c + o(1)) Y` is recorded as `Ξ ≤ (c + ε(L)) Y + c' L^{-σ} α` at every least
normalized counterexample of every large scale, uniformly in the induction constant
(`AtCounterexamples`, `remainder`).

**What remains a hypothesis.** `hE1` in `comparison_estimate` is the energy estimate (E1)
of `lem:energy-toolkit` for the envelope laws `(⊗_{b ∈ X} D^{ε_b}_{b,t_b}) ⊗ Ñ_{-X}` of the
selections, i.e. `lem:bracket-energy` with `κ = ⊗_{b ∈ X} D^{ε_b}_{b,t_b}`, together with
the large-union remainders (`lem:record:density-lp`) carried by `rE`. WP-R's
`Sarkozy.Structured.abs_envelope_energy_le` (outside law `μ`) and
`Sarkozy.RecordExpansion.envelope_energy_le_of_bracket` (outside law `Ñ`) reduce it to
`prop:record:density-structured` and to the folded-energy bounds of the sharp-first terms;
that reduction is not connected here.
-/

open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.TheoremC

open Sarkozy.Comparison Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-! ## The joint constant -/

/-- The joint comparison-and-mean constant `𝓗 = (1 - 2^{-k}) 𝓔 + (1 - m)/2^k` of
`cor:joint-closing`, for a comparison bound `𝓔` (hypothesis (i) of `thm:record:criterion`)
and a mean credit `m` ((CP7), hypothesis (ii)). -/
noncomputable def jointConstantC (k : ℕ) (𝓔 m : ℝ) : ℝ :=
  (1 - ((2 : ℝ) ^ k)⁻¹) * 𝓔 + (1 - m) / 2 ^ k

/-- With the joint constant `jointConstantC`, the closing number of `cor:joint-closing` is the
paper's `Θ = (1 - 2^{-k})(L₀ + 𝓔) + J + W + (1 - m)/2^k` of `thm:comparison`. -/
theorem jointTheta_jointConstantC (k : ℕ) (L₀ J W 𝓔 m : ℝ) :
    jointTheta k L₀ J W (jointConstantC k 𝓔 m) =
      (1 - ((2 : ℝ) ^ k)⁻¹) * (L₀ + 𝓔) + J + W + (1 - m) / 2 ^ k := by
  unfold jointTheta jointConstantC
  ring

theorem two_pow_mul_jointConstantC (k : ℕ) (𝓔 m : ℝ) :
    (2 : ℝ) ^ k * jointConstantC k 𝓔 m - 1 = ((2 : ℝ) ^ k - 1) * 𝓔 - m := by
  have h : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold jointConstantC
  field_simp
  ring

/-! ## Elementary facts about counterexamples and remainders -/

/-- The reference energy is positive at a least normalized counterexample. -/
theorem counterexample_pos {Y : ℕ → Finset ℤ → ℝ} {C : ℝ} (hC : 1 ≤ C) {L : ℕ}
    {A : Finset ℤ}
    (h : C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A) :
    0 < Y L A := by
  have h0 : 0 ≤ C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)
  linarith

theorem remainder_add (c₁ c₂ : ℝ) (L : ℕ) (A : Finset ℤ) :
    remainder (c₁ + c₂) L A = remainder c₁ L A + remainder c₂ L A := by
  unfold remainder
  ring

theorem remainder_mul (a c : ℝ) (L : ℕ) (A : Finset ℤ) :
    remainder (a * c) L A = a * remainder c L A := by
  unfold remainder
  ring

theorem remainder_nonneg {c : ℝ} (hc : 0 ≤ c) (L : ℕ) (A : Finset ℤ) :
    0 ≤ remainder c L A := by
  unfold remainder
  exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (density_nonneg _ _)

/-- `e^s cosh a ≤ e^S cosh A` for `s ≤ S` and `0 ≤ a ≤ A`: the class-free complete polynomial
is nondecreasing in the totals (`rem:cp:monotone`). -/
theorem exp_mul_cosh_le_of_le {s S a A : ℝ} (hs : s ≤ S) (ha0 : 0 ≤ a) (ha : a ≤ A) :
    Real.exp s * Real.cosh a ≤ Real.exp S * Real.cosh A := by
  have hcosh : Real.cosh a ≤ Real.cosh A :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg ha0, abs_of_nonneg (ha0.trans ha)]; exact ha)
  exact mul_le_mul (Real.exp_le_exp.mpr hs) hcosh (Real.cosh_pos a).le (Real.exp_pos S).le

/-- The relative error of `joint_estimate` tends to zero with those of its inputs. -/
theorem tendsto_joint_error {εE ε₂ : ℕ → ℝ} (hεE : Tendsto εE atTop (𝓝 0))
    (hε₂ : Tendsto ε₂ atTop (𝓝 0)) (k : ℕ) (X : ℝ) :
    Tendsto (fun L => ((2 : ℝ) ^ k - 1) * (εE L * X) + ε₂ L) atTop (𝓝 0) := by
  have h := ((hεE.mul_const X).const_mul ((2 : ℝ) ^ k - 1)).add hε₂
  simpa using h

variable {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
  {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]

/-! ## The joint hypothesis from (i) and (ii) -/

/-- **The hypothesis of `cor:joint-closing` from (i) and (ii) of `thm:record:criterion`.**
If `|Y_ν - Y_λ| ≤ (𝓔 + ε₁) Y + r₁` (i) and `½(e_L + e_R) ≥ (m - ε₂) Y - r₂` ((CP7), (ii)) at
every least normalized counterexample, then for every number `k` of queries
`(2^k - 1)(Y_λ - Y_ν) - ½(e_L + e_R) ≤ (2^k 𝓗 - 1 + o(1)) Y + r` with
`𝓗 = jointConstantC k 𝓔 m`. -/
theorem joint_of_comparison_mean (μ lam ν ML MR : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ) {𝓔 m c₁ c₂ : ℝ} {ε₁ ε₂ : ℕ → ℝ}
    (hcomp : AtCounterexamples (energyFirst μ F) fun L A =>
      |energyComparison ν F L A - energyFirst lam F L A| ≤
        (𝓔 + ε₁ L) * energyFirst μ F L A + remainder c₁ L A)
    (hmean : AtCounterexamples (energyFirst μ F) fun L A =>
      (m - ε₂ L) * energyFirst μ F L A - remainder c₂ L A ≤
        (energyMean F ML L A + energyMean F MR L A) / 2) (k : ℕ) :
    AtCounterexamples (energyFirst μ F) fun L A =>
      (2 ^ k - 1) * (energyFirst lam F L A - energyComparison ν F L A) -
          (energyMean F ML L A + energyMean F MR L A) / 2 ≤
        (2 ^ k * jointConstantC k 𝓔 m - 1 + ((2 ^ k - 1) * ε₁ L + ε₂ L)) *
            energyFirst μ F L A + remainder ((2 ^ k - 1) * c₁ + c₂) L A := by
  filter_upwards [hcomp, hmean] with L h1 h2
  intro C hC hind A hA hc
  have e1 := h1 C hC hind A hA hc
  have e2 := h2 C hC hind A hA hc
  have hk : (0 : ℝ) ≤ 2 ^ k - 1 := by
    have := one_le_pow₀ (n := k) (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  have hdiff : energyFirst lam F L A - energyComparison ν F L A ≤
      (𝓔 + ε₁ L) * energyFirst μ F L A + remainder c₁ L A := by
    have := neg_abs_le (energyComparison ν F L A - energyFirst lam F L A)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hk
  rw [two_pow_mul_jointConstantC, remainder_add, remainder_mul]
  nlinarith [hmul, e2]

/-! ## Hypothesis (i): the record comparison -/

section Comparison

variable {T : ∀ L, Atom L → Type} [∀ L b, Fintype (T L b)] [∀ L b, DecidableEq (T L b)]

/-- **Hypothesis (i) of `thm:record:criterion`: `|Y_ν - Y_λ| ≤ (𝓔 + o(1)) Y`**
(`lem:record:record-expansion` (i) and (ii) without the classes of (CP5), at the reserved
cut). At every scale `L`:

* (CP4)(b): `ν_b = λ_b + ∑_t (ζ^s_{b,t} + ζ^a_{b,t})`, `ζ^s` symmetric and `ζ^a` skew at
  `ι`, with the brackets `(π̃ D  ζ; ζ*  π̃ D) ⪰_ι 0`, `π̃ ≥ 0`;
* (CP3): `λ_b` symmetric at `ι` and `(Ñ_b λ_b; λ_b Ñ_b) ⪰_ι 0`;
* the prices `π^ε_{b,t} = π̃^ε_{b,t} q_b` (`q_b ≥ 0` the selection factors) have totals at
  most `S` (symmetric) and `Askew` (skew; the paper's `A`, renamed since `A` names the set),
  and `𝓔 ≥ B(e^S cosh A - 1)`;
* `hE1`: (E1) of `lem:energy-toolkit` for the envelopes of the selections
  (`lem:bracket-energy`), robustly: `Y_{(⊗_{b∈X} D) ⊗ Ñ_{-X}} ≤ (B + ε) C_X Y + r_ω`,
  `C_X = ∏_{b ∈ X} q_b`, with `ε ≥ 0` and remainders `r_ω` whose sum weighted by the
  monomials `∏_{b ∈ X} π̃^{ε_b}_{b,t_b}` is a density-linear remainder `hrE` (the
  large-union terms of `lem:record:density-lp`).

Then `|Y_ν - Y_λ| ≤ (𝓔 + ε (e^S cosh A - 1)) Y + c L^{-σ} α`. -/
theorem comparison_estimate (μ lam Nt ν : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)
    (ζ D : ∀ L b, T L b → ChangeType → ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (hν : ∀ L b, ν L b = lam L b + ∑ t, (ζ L b t .sym + ζ L b t .skew))
    (hlam : ∀ L b, IsSymmetricAt reservedCut (lam L b))
    (hs : ∀ L b t, IsSymmetricAt reservedCut (ζ L b t .sym))
    (ha : ∀ L b t, IsSkewAt reservedCut (ζ L b t .skew))
    (πt : ∀ L b, T L b → ChangeType → ℝ) (hπt : ∀ L b t e, 0 ≤ πt L b t e)
    (hN : ∀ L b, reservedCut.Bracket (Nt L b) (lam L b) (Nt L b))
    (hζ : ∀ L b t e, reservedCut.Bracket (πt L b t e • D L b t e) (ζ L b t e)
      (πt L b t e • D L b t e))
    (q : ∀ L, Atom L → ℝ) (hq : ∀ L b, 0 ≤ q L b) {S Askew Bf 𝓔 cE : ℝ}
    (hS : ∀ L, ∑ b, symTotal (fun b t e => πt L b t e * q L b) b ≤ S)
    (hA : ∀ L, ∑ b, skewTotal (fun b t e => πt L b t e * q L b) b ≤ Askew)
    (hBf : 0 ≤ Bf) (h𝓔 : Bf * (Real.exp S * Real.cosh Askew - 1) ≤ 𝓔)
    (εE : ℕ → ℝ) (hεE0 : ∀ L, 0 ≤ εE L) (rE : ∀ L, Finset ℤ → Choice (T L) → ℝ)
    (hE1 : AtCounterexamples (energyFirst μ F) fun L A => ∀ ω : Choice (T L), IsSelection ω →
      diagonalIntegral (envelopeLaw (Nt L) (D L) ω) (F L A) ≤
        (Bf + εE L) * (∏ b ∈ Choice.support ω, q L b) * energyFirst μ F L A + rE L A ω)
    (hrE : AtCounterexamples (energyFirst μ F) fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (T L) => IsSelection ω),
        monomial (πt L) ω * rE L A ω ≤ remainder cE L A) :
    AtCounterexamples (energyFirst μ F) fun L A =>
      |energyComparison ν F L A - energyFirst lam F L A| ≤
        (𝓔 + εE L * (Real.exp S * Real.cosh Askew - 1)) * energyFirst μ F L A +
          remainder cE L A := by
  filter_upwards [hE1, hrE] with L h1 h2
  intro C hC hind A' hA' hc
  have hE := h1 C hC hind A' hA' hc
  have hr := h2 C hC hind A' hA' hc
  have hY : 0 < energyFirst μ F L A' := counterexample_pos hC hc
  have hBz : 0 ≤ Bf + εE L := add_nonneg hBf (hεE0 L)
  have hterm : ∀ ω : Choice (T L), IsSelection ω →
      |term (lam L) (ζ L) (F L A') ω| ≤
        (Bf + εE L) * monomial (fun b t e => πt L b t e * q L b) ω * energyFirst μ F L A' +
          monomial (πt L) ω * rE L A' ω := by
    intro ω hω
    have h1' := abs_term_le_envelope (c := reservedCut) (hN L) (hζ L) (F L A') ω
    have hm : 0 ≤ monomial (πt L) ω := monomial_nonneg (hπt L) ω
    have h2' := mul_le_mul_of_nonneg_left (hE ω hω) hm
    rw [monomial_mul_selectionFactor]
    calc |term (lam L) (ζ L) (F L A') ω|
        ≤ monomial (πt L) ω * diagonalIntegral (envelopeLaw (Nt L) (D L) ω) (F L A') := h1'
      _ ≤ monomial (πt L) ω * ((Bf + εE L) * (∏ b ∈ Choice.support ω, q L b) *
            energyFirst μ F L A' + rE L A' ω) := h2'
      _ = (Bf + εE L) * (monomial (πt L) ω * ∏ b ∈ Choice.support ω, q L b) *
            energyFirst μ F L A' + monomial (πt L) ω * rE L A' ω := by ring
  have hmain := abs_energy_sub_le_of_terms reservedCut (hν L) (hlam L) (hs L) (ha L) (F L A')
    (fun b t e => mul_nonneg (hπt L b t e) (hq L b)) hY.le hBz
    (fun ω => monomial (πt L) ω * rE L A' ω) hterm
  have hS0 : 0 ≤ ∑ b, skewTotal (fun b t e => πt L b t e * q L b) b :=
    sum_nonneg fun b _ => sum_nonneg fun t _ => mul_nonneg (hπt L b t _) (hq L b)
  have hmono := exp_mul_cosh_le_of_le (hS L) hS0 (hA L)
  have hnueq : energyComparison ν F L A' = diagonalIntegral (tensorLaw (ν L)) (F L A') :=
    Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
  have hlameq : energyFirst lam F L A' = diagonalIntegral (tensorLaw (lam L)) (F L A') :=
    Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
  have step1 : (Bf + εE L) * (Real.exp (∑ b, symTotal (fun b t e => πt L b t e * q L b) b) *
        Real.cosh (∑ b, skewTotal (fun b t e => πt L b t e * q L b) b) - 1) *
          energyFirst μ F L A' ≤
      (Bf + εE L) * (Real.exp S * Real.cosh Askew - 1) * energyFirst μ F L A' := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    apply mul_le_mul_of_nonneg_left _ hBz
    linarith
  have step2 : (Bf + εE L) * (Real.exp S * Real.cosh Askew - 1) * energyFirst μ F L A' ≤
      (𝓔 + εE L * (Real.exp S * Real.cosh Askew - 1)) * energyFirst μ F L A' := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    linarith
  rw [hnueq, hlameq]
  linarith [hmain, step1, step2, hr]

/-- **The hypothesis of `cor:joint-closing`** from the record comparison
(`comparison_estimate`, hypothesis (i) of `thm:record:criterion`) and the mean credit of
(CP7) (hypothesis (ii)): `joint_of_comparison_mean` with `ε₁ = ε (e^S cosh A - 1)` and the
remainder constant `c₁ = cE`. The only analytic hypotheses are `hE1`/`hrE` (see
`comparison_estimate`) and the robust (CP7) bound `hmean`. -/
theorem joint_estimate (μ lam Nt ν ML MR : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)
    (ζ D : ∀ L b, T L b → ChangeType → ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (hν : ∀ L b, ν L b = lam L b + ∑ t, (ζ L b t .sym + ζ L b t .skew))
    (hlam : ∀ L b, IsSymmetricAt reservedCut (lam L b))
    (hs : ∀ L b t, IsSymmetricAt reservedCut (ζ L b t .sym))
    (ha : ∀ L b t, IsSkewAt reservedCut (ζ L b t .skew))
    (πt : ∀ L b, T L b → ChangeType → ℝ) (hπt : ∀ L b t e, 0 ≤ πt L b t e)
    (hN : ∀ L b, reservedCut.Bracket (Nt L b) (lam L b) (Nt L b))
    (hζ : ∀ L b t e, reservedCut.Bracket (πt L b t e • D L b t e) (ζ L b t e)
      (πt L b t e • D L b t e))
    (q : ∀ L, Atom L → ℝ) (hq : ∀ L b, 0 ≤ q L b) {S Askew Bf 𝓔 cE : ℝ}
    (hS : ∀ L, ∑ b, symTotal (fun b t e => πt L b t e * q L b) b ≤ S)
    (hA : ∀ L, ∑ b, skewTotal (fun b t e => πt L b t e * q L b) b ≤ Askew)
    (hBf : 0 ≤ Bf) (h𝓔 : Bf * (Real.exp S * Real.cosh Askew - 1) ≤ 𝓔)
    (εE : ℕ → ℝ) (hεE0 : ∀ L, 0 ≤ εE L) (rE : ∀ L, Finset ℤ → Choice (T L) → ℝ)
    (hE1 : AtCounterexamples (energyFirst μ F) fun L A => ∀ ω : Choice (T L), IsSelection ω →
      diagonalIntegral (envelopeLaw (Nt L) (D L) ω) (F L A) ≤
        (Bf + εE L) * (∏ b ∈ Choice.support ω, q L b) * energyFirst μ F L A + rE L A ω)
    (hrE : AtCounterexamples (energyFirst μ F) fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (T L) => IsSelection ω),
        monomial (πt L) ω * rE L A ω ≤ remainder cE L A)
    {m c₂ : ℝ} {ε₂ : ℕ → ℝ}
    (hmean : AtCounterexamples (energyFirst μ F) fun L A =>
      (m - ε₂ L) * energyFirst μ F L A - remainder c₂ L A ≤
        (energyMean F ML L A + energyMean F MR L A) / 2) (k : ℕ) :
    AtCounterexamples (energyFirst μ F) fun L A =>
      (2 ^ k - 1) * (energyFirst lam F L A - energyComparison ν F L A) -
          (energyMean F ML L A + energyMean F MR L A) / 2 ≤
        (2 ^ k * jointConstantC k 𝓔 m - 1 +
            ((2 ^ k - 1) * (εE L * (Real.exp S * Real.cosh Askew - 1)) + ε₂ L)) *
          energyFirst μ F L A + remainder ((2 ^ k - 1) * cE + c₂) L A :=
  joint_of_comparison_mean μ lam ν ML MR F
    (ε₁ := fun L => εE L * (Real.exp S * Real.cosh Askew - 1))
    (comparison_estimate μ lam Nt ν F ζ D hν hlam hs ha πt hπt hN hζ q hq hS hA hBf h𝓔 εE
      hεE0 rE hE1 hrE) hmean k

end Comparison

end Sarkozy.TheoremC
