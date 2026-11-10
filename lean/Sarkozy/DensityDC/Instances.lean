module

public import Sarkozy.DensityDC.LiftMoments

/-!
# The moment hypotheses of `density_dc_lift_moments` on the paper's groups

`density_dc_lift_moments` takes four moment hypotheses:
* `hlift2`, `hlift142`: the inputs on the whole group;
* `hmod2`, `hmod142`: the square-step models per sample.

On the paper's groups (`joinModuli m₀ p`: a prime-power prefix `X₀` and a prime tail),
`moment_input_le` and `moment_model_le` prove them, uniformly in the index:

* `input_moment_le_density`: `‖Re g^{I_v,D_{0,v},s_v}‖_{2r}^{2r} ≤ M₀^{2r} |X₀|^{2r} C Q^ε K α`
  (`lem:record:lift-moments`(c), with `α_I ≤ K α` for `|I| ≥ L`, as in the paper).
* `model_moment_le_fibre`: `‖Re g̃(z,·)‖_{2r}^{2r} ≤ |X₀|^{2r} C (n^β)^ε 2^{2r-1} α_f(z)`
  (`lem:record:fibre-scale`(e), with `λ ≤ 2`).
* `paperMeanDensity_le`: `ᾱ_v ≤ M₀ K α`.

The conditions on the cutoffs and on `λ` are those that `lem:scale-conditions` provides.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.DensityDC

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic

/-- The shifted residue class has at most `|A|` elements. -/
theorem card_shift_filter_le (A : Finset ℤ) (c : ℤ) (M : ℕ) {D0 : ℕ} (s : ZMod D0) :
    ((Icc 1 (M : ℤ)).filter fun x => ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A).card ≤ A.card := by
  apply card_le_card_of_injOn (fun x => x + c)
  · intro x hx
    exact (mem_filter.mp hx).2.2
  · intro x _ y _ h
    simpa using h

/-- `|A|/M ≤ K α` for `M ≥ L`, `α = |A|/(KL)`. -/
theorem card_div_le_density (A : Finset ℤ) {M L : ℕ} (hL : 1 ≤ L) (hML : L ≤ M) {x : ℝ}
    (hx : x ≤ A.card) :
    x / M ≤ (blockScale : ℝ) * density (blockScale * L) A := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hM' : (L : ℝ) ≤ M := by exact_mod_cast hML
  have hK : (0 : ℝ) < blockScale := by norm_num [blockScale]
  calc x / M ≤ (A.card : ℝ) / M := div_le_div_of_nonneg_right hx (lt_of_lt_of_le hL' hM').le
    _ ≤ (A.card : ℝ) / L := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hL' hM'
    _ = (blockScale : ℝ) * density (blockScale * L) A := by
        unfold density
        push_cast
        field_simp

/-- `|B|/M ≤ K α` for `M ≥ L`, `α = |A|/(KL)`. -/
theorem shift_density_le (A : Finset ℤ) (c : ℤ) {M L : ℕ} (hL : 1 ≤ L) (hML : L ≤ M)
    {D0 : ℕ} (s : ZMod D0) :
    (((Icc 1 (M : ℤ)).filter fun x => ((x + c : ℤ) : ZMod D0) = s ∧ x + c ∈ A).card : ℝ) / M ≤
      (blockScale : ℝ) * density (blockScale * L) A :=
  card_div_le_density A hL hML (by exact_mod_cast card_shift_filter_le A c M s)

/-- **`hlift` on the paper's groups**: for the constant `C` of `moment_input_le`, every
input satisfies `‖Re g^{I,D₀,s}‖_{2r}^{2r} ≤ M₀^{2r} |X₀|^{2r} C Q^ε K α` when `D₀ ∣ M₀`,
`|I| = M ≥ L` and the cutoff conditions hold. -/
theorem input_moment_le_density (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)],
      (∀ j, (p j).Prime) → Function.Injective p →
      ∀ (Q : ℝ), 1 ≤ Q → ∀ (c : ℤ) {M L M0 : ℕ}, 1 ≤ L → L ≤ M → 2 * ⌊Q⌋₊ ≤ M + 1 →
      ⌊Q⌋₊ ^ 5 ≤ M + 1 → ∀ {D0 : ℕ}, D0 ≤ M0 → ∀ (s : ZMod D0) (A : Finset ℤ),
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ p))).moment ((2 * r : ℕ) : ℝ)
          (fun x => (input (joinModuli m₀ p) Q (Icc (c + 1) (c + M)) D0 s A x).re) ≤
        (M0 : ℝ) ^ (2 * r) * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C * Q ^ ε *
          ((blockScale : ℝ) * density (blockScale * L) A)) := by
  obtain ⟨C, hC, hc⟩ := moment_input_le r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ hp hinj Q hQ c M L M0 hL hLM hs1 hs2 D0 hD0 s A
  refine (hc m₀ p hp hinj Q hQ c M (by omega) hs1 hs2 s A).trans ?_
  have hQe : 0 ≤ Q ^ ε := Real.rpow_nonneg (zero_le_one.trans hQ) _
  have hX : 0 ≤ (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C * Q ^ ε := by positivity
  apply mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hD0) _) _ _
    (by positivity)
  · exact mul_le_mul_of_nonneg_left (shift_density_le A c hL hLM s) hX
  · exact mul_nonneg hX (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- **`hmod` on the paper's groups**: for the constant `C` of `moment_model_le`, every
square-step model satisfies `‖Re g̃(z,·)‖_{2r}^{2r} ≤ |X₀|^{2r} C (n^β)^ε 2^{2r-1} α_f(z)`
when `λ ≤ 2` (`lem:scale-conditions`). -/
theorem model_moment_le_fibre (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)],
      (∀ j, (p j).Prime) → Function.Injective p →
      (Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j)) →
      ∀ (E : Finset (J₀ ⊕ J)) (z : ResidueSpace (joinModuli m₀ p)) {D0 : ℕ}, 1 ≤ D0 →
      ∀ (s : ZMod D0), (∀ k, D0.Coprime (joinModuli m₀ p k)) →
      ∀ (A : Finset ℤ) (c : ℤ) {M : ℕ}, 1 ≤ M →
      (((leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j) *
          (blockScale * stepScale blockScale M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))) :
            ℕ) : ℝ) / M) ≤ 2 →
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ p))).moment ((2 * r : ℕ) : ℝ)
          (fun y => (squareStepModel (joinModuli m₀ p) E z s A (Icc (c + 1) (c + M)) c M
            (stepR (joinModuli m₀ p) E D0)
            (blockScale * stepEll (joinModuli m₀ p) E D0 M)
            (paperCutoff (blockScale * stepEll (joinModuli m₀ p) E D0 M)) y).re) ≤
        ((Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
            paperCutoff (blockScale * stepEll (joinModuli m₀ p) E D0 M) ^ ε * 2 ^ (2 * r - 1)) *
          fibreDensity (joinModuli m₀ p) E z s A c M := by
  obtain ⟨C, hC, hc⟩ := moment_model_le r hr ε hε
  refine ⟨C, hC, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ hp hinj hpair E z D0 hD0 s hcop0 A c M hM hlam
  have h := hc m₀ p hp hinj hpair E z hD0 s hcop0 (K := blockScale) (by norm_num [blockScale])
    A c hM
  refine h.trans ?_
  have hlam0 : 0 ≤ (((leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j) *
      (blockScale * stepScale blockScale M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))) :
        ℕ) : ℝ) / M) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpow := pow_le_pow_left₀ hlam0 hlam (2 * r - 1)
  have hfd : 0 ≤ fibreDensity (joinModuli m₀ p) E z s A c M := by
    unfold fibreDensity
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hX : 0 ≤ (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
      paperCutoff (blockScale * stepEll (joinModuli m₀ p) E D0 M) ^ ε := by
    have : 0 ≤ paperCutoff (blockScale * stepEll (joinModuli m₀ p) E D0 M) ^ ε :=
      Real.rpow_nonneg (by unfold paperCutoff; exact Real.rpow_nonneg (Nat.cast_nonneg _) _) _
    positivity
  calc (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
          paperCutoff (blockScale * stepEll (joinModuli m₀ p) E D0 M) ^ ε *
        (((leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j) *
          (blockScale * stepScale blockScale M (leastSquare (D0 * ∏ j ∈ E, joinModuli m₀ p j))) :
            ℕ) : ℝ) / M) ^ (2 * r - 1) * fibreDensity (joinModuli m₀ p) E z s A c M
      ≤ (Fintype.card (ResidueSpace m₀) : ℝ) ^ (2 * r) * C *
          paperCutoff (blockScale * stepEll (joinModuli m₀ p) E D0 M) ^ ε * 2 ^ (2 * r - 1) *
          fibreDensity (joinModuli m₀ p) E z s A c M := by
        apply mul_le_mul_of_nonneg_right _ hfd
        exact mul_le_mul_of_nonneg_left hpow hX
    _ = _ := by ring

/-- `ᾱ_v ≤ M₀ K α` for `D_{0,v} ≤ M₀` and `|I_v| ≥ L`. -/
theorem paperMeanDensity_le {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (A : Finset ℤ)
    (D0 M : Slot → ℕ) (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v)) (v : Slot)
    {L M0 : ℕ} (hL : 1 ≤ L) (hLM : L ≤ M v) (hD0 : D0 v ≤ M0) :
    paperMeanDensity P A D0 M c s v ≤
      (M0 : ℝ) * ((blockScale : ℝ) * density (blockScale * L) A) := by
  unfold paperMeanDensity
  apply P.expect_le_const
  intro ω
  have hcard : (((A ∩ Icc (c ω v + 1) (c ω v + M v)).filter fun x : ℤ =>
      (x : ZMod (D0 v)) = s ω v).card : ℝ) ≤ A.card := by
    exact_mod_cast (card_filter_le _ _).trans (card_le_card inter_subset_left)
  have hD : (D0 v : ℝ) ≤ M0 := by exact_mod_cast hD0
  have h1 : (D0 v : ℝ) * (((A ∩ Icc (c ω v + 1) (c ω v + M v)).filter fun x : ℤ =>
      (x : ZMod (D0 v)) = s ω v).card : ℝ) ≤ M0 * A.card :=
    mul_le_mul hD hcard (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h2 := card_div_le_density A hL hLM (x := (D0 v : ℝ) *
    (((A ∩ Icc (c ω v + 1) (c ω v + M v)).filter fun x : ℤ =>
      (x : ZMod (D0 v)) = s ω v).card : ℝ) / M0) (by
        rcases (Nat.cast_nonneg M0 : (0 : ℝ) ≤ M0).lt_or_eq with hM0 | hM0
        · rw [div_le_iff₀ hM0]
          linarith
        · rw [← hM0, div_zero]
          exact Nat.cast_nonneg _)
  rcases (Nat.cast_nonneg M0 : (0 : ℝ) ≤ M0).lt_or_eq with hM0 | hM0
  · calc (D0 v : ℝ) / M v * (((A ∩ Icc (c ω v + 1) (c ω v + M v)).filter fun x : ℤ =>
          (x : ZMod (D0 v)) = s ω v).card : ℝ)
        = (M0 : ℝ) * ((D0 v : ℝ) * (((A ∩ Icc (c ω v + 1) (c ω v + M v)).filter fun x : ℤ =>
            (x : ZMod (D0 v)) = s ω v).card : ℝ) / M0 / M v) := by
          field_simp
      _ ≤ (M0 : ℝ) * ((blockScale : ℝ) * density (blockScale * L) A) :=
          mul_le_mul_of_nonneg_left h2 hM0.le
  · have hDz : (D0 v : ℝ) = 0 := le_antisymm (hM0 ▸ hD) (Nat.cast_nonneg _)
    rw [hDz, ← hM0]
    simp

end Sarkozy.DensityDC
