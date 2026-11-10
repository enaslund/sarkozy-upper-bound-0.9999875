module

public import Sarkozy.Comparison.FoldedEnergy

/-!
# Folded energies of tensor products of finite combinations (`lem:record:folded-energy`)

`paper/sections/08_scale_comparison.tex`, `lem:record:folded-energy` (a), (c), (d), (d′), as used
in the proof of `lem:sharp-first` (`paper/sections/10_comparison_lemmas.tex`): every atom carries
a finite real combination `∑_i c_i K_i` of *pieces*, each with a bracket
`(d_i L_i, K_i; K_iᵀ, d_i R_i) ⪰ 0` at one cut `c`, with `L_i, R_i` reflection positive. Three
kinds of pieces occur:

* a component `K_s` of a sharp difference (`HasSharpBound`): the bracket with the diagonal laws
  of the half marginals of `κ_s` and the sharp constant (`Comparison.sharp_iff_bracket`);
* a nonnegative measure (a positive part of a difference of another tag, or a positive record of
  `ρ − μ`): the bracket with the diagonal laws of its own half marginals and constant one
  (`bracket_of_nonneg`, from `Comparison.sharp_one_of_nonneg`; "positive couplings are
  contractions between their marginal spaces, and no positivity of these factors at `c_j` is
  used");
* a reflection positive law (the outside `μ_𝔟`): the bracket `(K, K, K)` (`bracket_of_positive`).

`abs_tensor_sum_le_folded`: expand the product over the atoms into choices `f` of one piece at
every atom (`RecordExpansion.tensorLaw_sum`), fold every choice (`Comparison.folded_energy_tensor`)
and recombine by Cauchy–Schwarz:
`|∫ ⊗_b (∑_i c_{b,i} K_{b,i}) a| ≤ √𝔈₊ √𝔈₋`, `𝔈_± = ∑_f w_f 𝔈_±(f)`,
`w_f = ∏_b |c_{b,f_b}| d_{b,f_b}`, with `𝔈_±(f) ≥ 0` the folded energies of the choice `f`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Comparison Sarkozy.RecordExpansion ReflectionCut

variable {V : Type*} [Fintype V] [DecidableEq V]

section Pieces

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A nonnegative measure is bracketed by the diagonal laws of its own half marginals, with
constant one (`lem:record:folded-energy` (d)). -/
theorem bracket_of_nonneg (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hK : ∀ f : (V → X) → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ K f) :
    c.Bracket ((1 : ℝ) • c.diagonalLaw (halfMarginalPlus c K)) K
      ((1 : ℝ) • c.diagonalLaw (halfMarginalMinus c K)) :=
  (sharp_iff_bracket c K (fun x => hK _ fun z => by split_ifs <;> norm_num)
    (fun x => hK _ fun z => by split_ifs <;> norm_num) zero_le_one).mp
    (sharp_one_of_nonneg c K hK)

omit [Fintype X] [DecidableEq X] in
/-- A reflection positive law is bracketed by itself, with constant one. -/
theorem bracket_of_positive (c : ReflectionCut V) {K : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hK : c.Positive K) : c.Bracket ((1 : ℝ) • K) K ((1 : ℝ) • K) := by
  rw [one_smul]
  exact hK.bracket_self

omit [Fintype X] in
theorem halfMarginalPlus_nonneg (c : ReflectionCut V) {K : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hK : ∀ f : (V → X) → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ K f) (x : c.Half → X) :
    0 ≤ halfMarginalPlus c K x :=
  hK _ fun z => by split_ifs <;> norm_num

omit [Fintype X] in
theorem halfMarginalMinus_nonneg (c : ReflectionCut V) {K : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hK : ∀ f : (V → X) → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ K f) (x : c.Half → X) :
    0 ≤ halfMarginalMinus c K x :=
  hK _ fun z => by split_ifs <;> norm_num

end Pieces

section Tensor

variable {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)]

/-- Weighted Cauchy–Schwarz: `∑ w √x √y ≤ √(∑ w x) √(∑ w y)` for `w, x, y ≥ 0`. -/
theorem sum_mul_sqrt_mul_sqrt_le {ι : Type*} [Fintype ι] (w x y : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    ∑ i, w i * Real.sqrt (x i) * Real.sqrt (y i) ≤
      Real.sqrt (∑ i, w i * x i) * Real.sqrt (∑ i, w i * y i) := by
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => mul_nonneg (hw i) (hx i))
    (fun i => mul_nonneg (hw i) (hy i))
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.sqrt_mul (hw i), Real.sqrt_mul (hw i)]
  have : Real.sqrt (w i) * Real.sqrt (w i) = w i := Real.mul_self_sqrt (hw i)
  calc w i * Real.sqrt (x i) * Real.sqrt (y i)
      = (Real.sqrt (w i) * Real.sqrt (w i)) * Real.sqrt (x i) * Real.sqrt (y i) := by rw [this]
    _ = Real.sqrt (w i) * Real.sqrt (x i) * (Real.sqrt (w i) * Real.sqrt (y i)) := by ring

/-- The weight `w_f = ∏_b |c_{b,f_b}| d_{b,f_b}` of a choice of pieces. -/
noncomputable def choiceWeight {I : J → Type*} (coef d : ∀ j, I j → ℝ) (f : ∀ j, I j) : ℝ :=
  ∏ j, |coef j (f j)| * d j (f j)

/-- The folded energy `𝔈₊(f) = ∫ (a ∘ φ₊) d(⊗_b L_{b,f_b})` of a choice. -/
noncomputable def foldedPlus (c : ReflectionCut V) {I : J → Type*}
    (Lp : ∀ j, I j → ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (a : V → (∀ j, X j) → ℝ) (f : ∀ j, I j) : ℝ :=
  multilinearIntegral (tensorLaw fun j => Lp j (f j)) (a ∘ c.foldPlus)

/-- The folded energy `𝔈₋(f) = ∫ (a ∘ φ₋) d(⊗_b R_{b,f_b})` of a choice. -/
noncomputable def foldedMinus (c : ReflectionCut V) {I : J → Type*}
    (Lm : ∀ j, I j → ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (a : V → (∀ j, X j) → ℝ) (f : ∀ j, I j) : ℝ :=
  multilinearIntegral (tensorLaw fun j => Lm j (f j)) (a ∘ c.foldMinus)

/-- **Folded factorization of a product of finite combinations** (`lem:record:folded-energy`
(a), (c), (d), (d′), the step of `lem:sharp-first` that folds every expanded term). If every
piece `K_{b,i}` has a bracket `(d L, K; Kᵀ, d R) ⪰ 0` at `c` with `L, R` reflection positive and
`d ≥ 0`, then the energy of `⊗_b ∑_i c_{b,i} K_{b,i}` is at most `√𝔈₊ √𝔈₋`, where
`𝔈_± = ∑_f w_f 𝔈_±(f)` are the weighted folded energies of the choices `f`, which are
nonnegative. -/
theorem abs_tensor_sum_le_folded (c : ReflectionCut V) {I : J → Type*} [∀ j, Fintype (I j)]
    (coef d : ∀ j, I j → ℝ) (K Lp Lm : ∀ j, I j → ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hLp : ∀ j i, c.Positive (Lp j i)) (hLm : ∀ j i, c.Positive (Lm j i))
    (hbr : ∀ j i, c.Bracket (d j i • Lp j i) (K j i) (d j i • Lm j i))
    (a : V → (∀ j, X j) → ℝ) :
    (∀ f, 0 ≤ foldedPlus c Lp a f) ∧ (∀ f, 0 ≤ foldedMinus c Lm a f) ∧
      |multilinearIntegral (tensorLaw fun j => ∑ i, coef j i • K j i) a| ≤
        Real.sqrt (∑ f, choiceWeight coef d f * foldedPlus c Lp a f) *
          Real.sqrt (∑ f, choiceWeight coef d f * foldedMinus c Lm a f) := by
  have hfold : ∀ f : ∀ j, I j, 0 ≤ foldedPlus c Lp a f ∧ 0 ≤ foldedMinus c Lm a f ∧
      |multilinearIntegral (tensorLaw fun j => K j (f j)) a| ≤ (∏ j, d j (f j)) *
        Real.sqrt (foldedPlus c Lp a f) * Real.sqrt (foldedMinus c Lm a f) := fun f =>
    folded_energy_tensor c (fun j => K j (f j)) (fun j => Lp j (f j)) (fun j => Lm j (f j))
      (fun j => d j (f j)) (fun j => hd j (f j)) (fun j => hLp j (f j)) (fun j => hLm j (f j))
      (fun j => hbr j (f j)) a
  refine ⟨fun f => (hfold f).1, fun f => (hfold f).2.1, ?_⟩
  have hexp : tensorLaw (fun j => ∑ i, coef j i • K j i) =
      ∑ f : (∀ j, I j), (∏ j, coef j (f j)) • tensorLaw (fun j => K j (f j)) := by
    rw [tensorLaw_sum (fun j i => coef j i • K j i)]
    refine Finset.sum_congr rfl fun f _ => ?_
    exact tensorLaw_smul (fun j => coef j (f j)) (fun j => K j (f j))
  have hsplit : multilinearIntegral (tensorLaw fun j => ∑ i, coef j i • K j i) a =
      ∑ f : (∀ j, I j), (∏ j, coef j (f j)) *
        multilinearIntegral (tensorLaw fun j => K j (f j)) a := by
    rw [hexp]
    unfold multilinearIntegral
    rw [LinearMap.sum_apply]
    rfl
  have hw : ∀ f, 0 ≤ choiceWeight coef d f := fun f =>
    Finset.prod_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hd j (f j))
  rw [hsplit]
  calc |∑ f : (∀ j, I j), (∏ j, coef j (f j)) *
        multilinearIntegral (tensorLaw fun j => K j (f j)) a|
      ≤ ∑ f : (∀ j, I j), |(∏ j, coef j (f j)) *
          multilinearIntegral (tensorLaw fun j => K j (f j)) a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f : (∀ j, I j), choiceWeight coef d f * Real.sqrt (foldedPlus c Lp a f) *
          Real.sqrt (foldedMinus c Lm a f) := by
        refine Finset.sum_le_sum fun f _ => ?_
        rw [abs_mul, Finset.abs_prod]
        have h1 := (hfold f).2.2
        have h0 : 0 ≤ ∏ j, |coef j (f j)| := Finset.prod_nonneg fun j _ => abs_nonneg _
        calc (∏ j, |coef j (f j)|) * |multilinearIntegral (tensorLaw fun j => K j (f j)) a|
            ≤ (∏ j, |coef j (f j)|) * ((∏ j, d j (f j)) *
                Real.sqrt (foldedPlus c Lp a f) * Real.sqrt (foldedMinus c Lm a f)) :=
              mul_le_mul_of_nonneg_left h1 h0
          _ = choiceWeight coef d f * Real.sqrt (foldedPlus c Lp a f) *
                Real.sqrt (foldedMinus c Lm a f) := by
              unfold choiceWeight
              rw [Finset.prod_mul_distrib]
              ring
    _ ≤ Real.sqrt (∑ f, choiceWeight coef d f * foldedPlus c Lp a f) *
          Real.sqrt (∑ f, choiceWeight coef d f * foldedMinus c Lm a f) :=
        sum_mul_sqrt_mul_sqrt_le _ _ _ hw (fun f => (hfold f).1) (fun f => (hfold f).2.1)

end Tensor

end Sarkozy.EnvelopeInputs
