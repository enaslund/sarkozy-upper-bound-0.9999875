module

public import Sarkozy.DensityDC.Moments

/-!
# The cited moment bounds of `lem:record:density-dc`

The proof of `lem:record:density-dc` cites two moment bounds:
* `lem:record:lift-moments`(c) for the inputs `g^{I,D₀,s}`,
  `E ‖g‖_{2r}^{2r} ≤ C_{r,ε} N^ε M₀^{2r} α_I`;
* `lem:record:fibre-scale`(e) for the square-step models,
  `E ‖g̃(z,·)‖_{2r}^{2r} ≤ C_{r,ε} N^ε λ^{2r-1} α_f`.

This file derives both, on the paper's groups (a prime-power prefix `X₀` and a prime
tail, `joinModuli m₀ p`), from WP-FI's `Sarkozy.Functional.moment_stepLift_le` and
`moment_squareStepModel_paperCutoff` (`Sarkozy/Functional/MomentBridge.lean`). Those in
turn rest on `Sarkozy.FourierArithmetic.uniform_prefixed_indicator_moment`.

* `liftOn_Icc_shift`: a lift over `c + [M]` is a translate of a lift over `[M]`.
* `input_eq_stepLift`: `g^{I,D₀,s}(y) = D₀ · h(y - ι(c))`, where `h` is the lift on
  `[M]` of the indicator of the shifted residue class (`stepLift` with `E = ∅`).
* `moment_input_le`: `‖Re g^{I,D₀,s}‖_{2r}^{2r} ≤ D₀^{2r} |X₀|^{2r} C Q^ε |B|/M`, with
  `B = {x ∈ A ∩ I : x ≡ s (D₀)}` shifted to `[M]`.
* `moment_model_le`: `‖Re g̃(z,·)‖_{2r}^{2r} ≤ |X₀|^{2r} C (n^β)^ε λ^{2r-1} α_f(z)`.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.DensityDC

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic

section Shift

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

omit [DecidableEq J] in
/-- A lift over `c + [M]` is the translate by `ι(c)` of the lift over `[M]` of the shifted
function. -/
theorem liftOn_Icc_shift (T : Finset (ResidueSpace m)) (c : ℤ) (M : ℕ) (f : ℤ → ℂ)
    (y : ResidueSpace m) :
    liftOn m T (Icc (c + 1) (c + M)) f y =
      liftOn m T (Icc 1 (M : ℤ)) (fun x => f (x + c)) (y - integerResidue m c) := by
  unfold liftOn intervalCoeff
  apply sum_congr rfl
  intro a _
  have hI : Icc (c + 1) (c + (M : ℤ)) = (Icc 1 (M : ℤ)).map (addRightEmbedding c) := by
    rw [Finset.map_add_right_Icc, add_comm c 1, add_comm c (M : ℤ)]
  have hcard : (Icc (c + 1) (c + (M : ℤ))).card = (Icc 1 (M : ℤ)).card := by
    rw [hI, card_map]
  rw [hcard, hI, sum_map]
  simp only [addRightEmbedding_apply, map_add, prodChar_add_right, map_mul,
    prodChar_sub_right]
  rw [mul_assoc, mul_assoc]
  congr 1
  rw [Finset.sum_mul, Finset.sum_mul]
  apply sum_congr rfl
  intro x _
  have hn := norm_prodChar m a (integerResidue m c)
  have hcc : conj (prodChar m a (integerResidue m c)) * prodChar m a (integerResidue m c) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  calc f (x + c) * (conj (prodChar m a (integerResidue m x)) *
        conj (prodChar m a (integerResidue m c))) * prodChar m a y
      = f (x + c) * conj (prodChar m a (integerResidue m x)) *
          (prodChar m a y * conj (prodChar m a (integerResidue m c))) := by ring

/-- `retainedOff` with no selected coordinates is the set of all labels of conductor at most
`Q`. -/
theorem retainedOff_empty (Q : ℝ) : retainedOff m ∅ Q = retained m Q := by
  ext a
  simp [retainedOff, retained]

/-- **The input as a translated piece**: `g^{I,D₀,s}(y) = D₀ · h(y - ι(c))` with
`h = 𝓛_{[M],Q} 1_B`, `B = {x ∈ [M] : x + c ∈ A, x + c ≡ s (D₀)}`. -/
theorem input_eq_stepLift (Q : ℝ) (c : ℤ) (M : ℕ) {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ)
    (y : ResidueSpace m) :
    input m Q (Icc (c + 1) (c + M)) D0 s A y =
      (D0 : ℂ) * stepLift m ∅ Q ((Icc 1 (M : ℤ)).filter fun x =>
        ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A) M (y - integerResidue m c) := by
  unfold input Sarkozy.Functional.lift
  rw [liftOn_Icc_shift]
  unfold stepLift
  rw [retainedOff_empty]
  unfold liftOn
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro a _
  unfold intervalCoeff
  rw [← mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro x hx
  simp only [inputFun, indicator]
  by_cases h : ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A
  · rw [ite_eq_left h, ite_eq_left (mem_filter.mpr ⟨hx, h⟩)]
    ring
  · have hnot : x ∉ (Icc 1 (M : ℤ)).filter
        (fun x => ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A) := by
      intro hm
      exact h (mem_filter.mp hm).2
    rw [ite_eq_right h, ite_eq_right hnot]
    ring

/-- Moments under the uniform law are translation invariant. -/
theorem moment_translate (r : ℝ) (F : ResidueSpace m → ℝ) (t : ResidueSpace m) :
    (FiniteLaw.uniform (ResidueSpace m)).moment r (fun y => F (y - t)) =
      (FiniteLaw.uniform (ResidueSpace m)).moment r F := by
  unfold FiniteLaw.moment
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight t) _ _ (fun y => rfl)

end Shift

/-! ## The moment bounds on the paper's groups -/

section Moments

/-- `|Re w|^{2r} ≤ ‖w‖^{2r}` in the form of the moments. -/
theorem moment_re_le_norm {X : Type*} [Fintype X] [Nonempty X] (r : ℕ) (G : X → ℂ) :
    (FiniteLaw.uniform X).moment ((2 * r : ℕ) : ℝ) (fun x => (G x).re) ≤
      𝔼 x, ‖G x‖ ^ (2 * r) := by
  unfold FiniteLaw.moment
  rw [uniform_expect_eq_expect]
  apply Finset.expect_le_expect
  intro x _
  rw [Real.rpow_natCast]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (G x)) _

/-- **`lem:record:lift-moments`(c) for the inputs** on the paper's groups: for every `r ≥ 1`
and `ε > 0` there is `C` with
`‖Re g^{I,D₀,s}‖_{2r}^{2r} ≤ D₀^{2r} |X₀|^{2r} C Q^ε |B|/M` for `I = c + [M]`, where
`B = {x ∈ [M] : x + c ∈ A, x + c ≡ s (D₀)}` and the cutoff `Q` satisfies `1 ≤ Q`,
`2⌊Q⌋ ≤ M + 1`, `⌊Q⌋^5 ≤ M + 1`. -/
theorem moment_input_le (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)],
      (∀ j, (p j).Prime) → Function.Injective p →
      ∀ (Q : ℝ), 1 ≤ Q → ∀ (c : ℤ) (M : ℕ), 0 < M → 2 * ⌊Q⌋₊ ≤ M + 1 → ⌊Q⌋₊ ^ 5 ≤ M + 1 →
      ∀ {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ),
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ p))).moment ((2 * r : ℕ) : ℝ)
          (fun x => (input (joinModuli m₀ p) Q (Icc (c + 1) (c + M)) D0 s A x).re) ≤
        (D0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C * Q ^ ε *
          ((((Icc 1 (M : ℤ)).filter fun x =>
            ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A).card : ℝ) / M)) := by
  obtain ⟨C, hC, hc⟩ := moment_stepLift_le r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ hp hinj Q hQ c M hM hs1 hs2 D0 s A
  set B := (Icc 1 (M : ℤ)).filter fun x => ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A with hB
  set t := integerResidue (joinModuli m₀ p) c
  have hstep := hc m₀ p hp hinj ∅ Q hQ M hM hs1 hs2 B (filter_subset _ _)
  have hpt : ∀ x, |(input (joinModuli m₀ p) Q (Icc (c + 1) (c + M)) D0 s A x).re| ^ (2 * r) ≤
      (D0 : ℝ) ^ (2 * r) * ‖stepLift (joinModuli m₀ p) ∅ Q B M (x - t)‖ ^ (2 * r) := by
    intro x
    rw [input_eq_stepLift, ← mul_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    calc |((D0 : ℂ) * stepLift (joinModuli m₀ p) ∅ Q B M (x - t)).re|
        ≤ ‖(D0 : ℂ) * stepLift (joinModuli m₀ p) ∅ Q B M (x - t)‖ := Complex.abs_re_le_norm _
      _ = (D0 : ℝ) * ‖stepLift (joinModuli m₀ p) ∅ Q B M (x - t)‖ := by
          rw [norm_mul, Complex.norm_natCast]
  have htr : (𝔼 x, ‖stepLift (joinModuli m₀ p) ∅ Q B M (x - t)‖ ^ (2 * r)) =
      𝔼 x, ‖stepLift (joinModuli m₀ p) ∅ Q B M x‖ ^ (2 * r) :=
    Fintype.expect_equiv (Equiv.subRight t) _ _ (fun x => rfl)
  unfold FiniteLaw.moment
  rw [uniform_expect_eq_expect]
  calc (𝔼 x, |(input (joinModuli m₀ p) Q (Icc (c + 1) (c + M)) D0 s A x).re| ^
        ((2 * r : ℕ) : ℝ))
      = 𝔼 x, |(input (joinModuli m₀ p) Q (Icc (c + 1) (c + M)) D0 s A x).re| ^ (2 * r) := by
        simp_rw [Real.rpow_natCast]
    _ ≤ 𝔼 x, (D0 : ℝ) ^ (2 * r) * ‖stepLift (joinModuli m₀ p) ∅ Q B M (x - t)‖ ^ (2 * r) :=
        Finset.expect_le_expect fun x _ => hpt x
    _ = (D0 : ℝ) ^ (2 * r) * 𝔼 x, ‖stepLift (joinModuli m₀ p) ∅ Q B M (x - t)‖ ^ (2 * r) := by
        rw [Finset.mul_expect]
    _ ≤ (D0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C * Q ^ ε *
          ((B.card : ℝ) / M)) := by
        rw [htr]
        exact mul_le_mul_of_nonneg_left hstep (by positivity)

/-- **`lem:record:fibre-scale`(e) in moment form** on the paper's groups, with the paper's
cutoff `Q' = n^{1/20}`: `‖Re g̃(z,·)‖_{2r}^{2r} ≤ |X₀|^{2r} C (n^β)^ε λ^{2r-1} α_f(z)`. -/
theorem moment_model_le (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)],
      (∀ j, (p j).Prime) → Function.Injective p →
      (Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j)) →
      ∀ (E : Finset (J₀ ⊕ J)) (z : ResidueSpace (joinModuli m₀ p)) {D0 : ℕ}, 1 ≤ D0 →
      ∀ (s : ZMod D0), (∀ k, D0.Coprime (joinModuli m₀ p k)) →
      ∀ {K : ℕ}, 1 ≤ K → ∀ (A : Finset ℤ) (c : ℤ) {M : ℕ}, 1 ≤ M →
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ p))).moment ((2 * r : ℕ) : ℝ)
          (fun y => (squareStepModel (joinModuli m₀ p) E z s A (Icc (c + 1) (c + M)) c M
            (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))
            (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j)))
            (paperCutoff (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))))
            y).re) ≤
        ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
            paperCutoff (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))) ^ ε) *
          (((leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j) *
              (K * stepScale K M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))) : ℕ) : ℝ) /
            M) ^ (2 * r - 1) *
          fibreDensity (joinModuli m₀ p) E z s A c M := by
  obtain ⟨C, hC, hc⟩ := moment_squareStepModel_paperCutoff r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ hp hinj hpair E z D0 hD0 s hcop0 K hK A c M hM
  exact (moment_re_le_norm r _).trans (hc m₀ p hp hinj hpair E z hD0 s hcop0 hK A c hM)

end Moments

end Sarkozy.DensityDC
