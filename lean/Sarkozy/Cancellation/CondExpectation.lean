module

public import Sarkozy.Cancellation.PairDecomposition
public import Sarkozy.Cancellation.SquareShift

@[expose] public section

/-!
# `E_U φ_x` as the strict-square pair average on `X_{𝒮'}`

Step 3 of `lem:record:density-can` begins: "`E_U φ_x` averages both pair variables over the
tail primes outside `U`. Fix also the pair labels `y` at `U`…". This file proves that reading
for WP-S's conditional expectation `condProjOn A U` (`Sarkozy.Mixing.PairSupport`), which is what
`step1_pair_decomposition` produces:

* `condProjOn_mulVec_apply`: `(E_U φ)(a)` is the uniform average of `φ` over the coordinates
  outside `U`, those of `U` kept;
* `expect_pairAlphabet`: with `A j = Ω_{p_j}` (the type `PairAlphabet`), the uniform average over
  vectors of pairs is the average over `pairSet` (pairs of vectors) used in
  `Sarkozy.Cancellation.SquareShift`.

New material for this paper.
-/

namespace Sarkozy.Cancellation

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Finset
open scoped Matrix
open Sarkozy.Mixing Sarkozy.IndexSupport

section CondProj

variable {K : Type*} [Fintype K] [DecidableEq K] {A : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)]

/-- Replace the coordinates outside `U` of `a` by `c`. -/
def mergeFree (U : K → Bool) (a : ∀ j, A j) (c : ∀ j : {j // U j = false}, A j) : ∀ j, A j :=
  fun j => if h : U j = false then c ⟨j, h⟩ else a j

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] in
lemma mergeFree_free (U : K → Bool) (a : ∀ j, A j) (c : ∀ j : {j // U j = false}, A j)
    (k : {j // U j = false}) : mergeFree U a c k.1 = c k := by
  simp [mergeFree, k.2]

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] in
lemma mergeFree_fixed (U : K → Bool) (a : ∀ j, A j) (c : ∀ j : {j // U j = false}, A j)
    {j : K} (hj : U j = true) : mergeFree U a c j = a j := by
  simp [mergeFree, hj]

/-- **`E_U` as an average** (Step 3 of `lem:record:density-can`): `(E_U φ)(a)` is the uniform
average of `φ` over the coordinates outside `U`, with those of `U` kept. -/
theorem condProjOn_mulVec_apply (U : K → Bool) (φ : (∀ j, A j) → ℝ) (a : ∀ j, A j) :
    (condProjOn A U *ᵥ φ) a =
      (∏ j : {j // U j = false}, (Fintype.card (A j) : ℝ))⁻¹ *
        ∑ c : (∀ j : {j // U j = false}, A j), φ (mergeFree U a c) := by
  classical
  simp only [condProjOn, Matrix.mulVec, dotProduct, piKron_apply]
  have hterm : ∀ b : ∀ j, A j,
      (∏ j, (if U j then (1 : Matrix (A j) (A j) ℝ) else meanMatrix (A j)) (a j) (b j)) =
        if (∀ j ∈ univ.filter (fun j => U j = true), a j = b j) then
          (∏ j : {j // U j = false}, (Fintype.card (A j) : ℝ))⁻¹ else 0 := by
    intro b
    have h1 : ∀ j, (if U j then (1 : Matrix (A j) (A j) ℝ) else meanMatrix (A j)) (a j) (b j) =
        if U j = true then (if a j = b j then (1 : ℝ) else 0) else (Fintype.card (A j) : ℝ)⁻¹ := by
      intro j
      split_ifs with hU <;> simp [Matrix.one_apply, meanMatrix_apply, *]
    simp_rw [h1]
    rw [prod_ite, prod_boole]
    have h2 : ∏ j ∈ univ.filter (fun j => ¬ U j = true), (Fintype.card (A j) : ℝ)⁻¹ =
        (∏ j : {j // U j = false}, (Fintype.card (A j) : ℝ))⁻¹ := by
      rw [prod_inv_distrib]
      congr 1
      exact prod_subtype _ (fun j => by simp) (fun j => (Fintype.card (A j) : ℝ))
    rw [h2]
    split_ifs <;> simp
  simp_rw [hterm, ite_mul, zero_mul]
  rw [← sum_filter, ← mul_sum]
  congr 1
  symm
  apply sum_bij (fun c _ => mergeFree U a c)
  · intro c _
    rw [mem_filter]
    refine ⟨mem_univ _, fun j hj => ?_⟩
    rw [mem_filter] at hj
    rw [mergeFree_fixed U a c hj.2]
  · intro c₁ _ c₂ _ h
    funext k
    have := congrFun h k.1
    rwa [mergeFree_free, mergeFree_free] at this
  · intro b hb
    rw [mem_filter] at hb
    refine ⟨fun k => b k.1, mem_univ _, ?_⟩
    funext j
    by_cases hj : U j = false
    · simp [mergeFree, hj]
    · have hj' : U j = true := by simpa using hj
      rw [mergeFree_fixed U a _ hj']
      exact hb.2 j (by simp [hj'])
  · intro c _
    rfl

end CondProj

section PairAlphabet

open Sarkozy.FourierArithmetic

variable {K : Type*} [Fintype K] [DecidableEq K] (p : K → ℕ) [∀ j, NeZero (p j)]

/-- The strict-square pair alphabet `Ω_p = {(x, y) : y − x a nonzero square}` at `j`, the pair
alphabet `A j` of WP-S's `pair_support_decay` in `lem:record:density-can`. -/
abbrev PairAlphabet (j : K) := {xy : ZMod (p j) × ZMod (p j) // xy.2 - xy.1 ∈ sqSet p j}

instance pairAlphabet_nonempty [∀ j, Fact (p j).Prime] (j : K) : Nonempty (PairAlphabet p j) :=
  ⟨⟨(0, 1), by simpa using one_mem_sqSet p j⟩⟩

/-- The pair of vectors `(x, y)` of a vector of pairs. -/
def pairsToVectors (c : ∀ j, PairAlphabet p j) : ResidueSpace p × ResidueSpace p :=
  (fun j => (c j).1.1, fun j => (c j).1.2)

/-- Vectors of pairs in `∏_j Ω_{p_j}` are the pairs of vectors in `pairSet`. -/
theorem sum_pairAlphabet (F : ResidueSpace p × ResidueSpace p → ℂ) :
    ∑ c : (∀ j, PairAlphabet p j), F (pairsToVectors p c) = ∑ xy ∈ pairSet p, F xy := by
  apply sum_bij (fun c _ => pairsToVectors p c)
  · intro c _
    rw [pairSet, mem_filter]
    exact ⟨mem_univ _, fun j => (c j).2⟩
  · intro c₁ _ c₂ _ h
    funext j
    apply Subtype.ext
    have h1 := congrFun (congrArg Prod.fst h) j
    have h2 := congrFun (congrArg Prod.snd h) j
    exact Prod.ext h1 h2
  · intro xy hxy
    rw [pairSet, mem_filter] at hxy
    exact ⟨fun j => ⟨(xy.1 j, xy.2 j), hxy.2 j⟩, mem_univ _, rfl⟩
  · intro c _
    rfl

theorem card_pairAlphabet : Fintype.card (∀ j, PairAlphabet p j) = (pairSet p).card := by
  have h := sum_pairAlphabet p (fun _ => (1 : ℂ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- The uniform average over `∏_j Ω_{p_j}` of `F₁(x) F₂(y)` is the pair average `∫ F₁ ⊗ F₂ dπ`. -/
theorem uniform_expect_pairAlphabet [∀ j, Fact (p j).Prime] (F₁ F₂ : ResidueSpace p → ℝ) :
    (((FiniteLaw.uniform (∀ j, PairAlphabet p j)).expect
        (fun c => F₁ (pairsToVectors p c).1 * F₂ (pairsToVectors p c).2) : ℝ) : ℂ) =
      pairAvg p (fun x => (F₁ x : ℂ)) (fun y => (F₂ y : ℂ)) := by
  rw [FiniteLaw.expect_uniform, pairAvg]
  push_cast
  rw [sum_pairAlphabet p (fun xy => (F₁ xy.1 : ℂ) * (F₂ xy.2 : ℂ)), card_pairAlphabet,
    div_eq_inv_mul]

end PairAlphabet

/-! ## `E_U φ_x` is the pair average on `X_{𝒮'}` -/

section Identification

open Sarkozy.FourierArithmetic

variable {K : Type*} [Fintype K] [DecidableEq K] (q : K → ℕ) [∀ j, NeZero (q j)]

/-- **`E_U φ_x(y)` as the strict-square pair average** (Step 3 of `lem:record:density-can`): for
the pair factor `φ(a) = F₁(x(a)) F₂(y(a))` on `∏_j Ω_{q_j}` and a support `U`,
`(E_U φ)(a) = ∫ g₁ ⊗ g₂ dπ`, `π` uniform on `∏_{j ∉ U} Ω_{q_j}`, with `g_i` the function `F_i` with
the coordinates of `U` frozen at the labels of `a`. -/
theorem condProjOn_eq_pairAvg (U : K → Bool) (F₁ F₂ : ResidueSpace q → ℝ)
    (a : ∀ j, PairAlphabet q j) :
    (((condProjOn (PairAlphabet q) U *ᵥ
        (fun b => F₁ (pairsToVectors q b).1 * F₂ (pairsToVectors q b).2)) a : ℝ) : ℂ) =
      pairAvg (fun k : {j // U j = false} => q k.1)
        (fun x' => (F₁ (mergeFree U (pairsToVectors q a).1 x') : ℂ))
        (fun y' => (F₂ (mergeFree U (pairsToVectors q a).2 y') : ℂ)) := by
  rw [condProjOn_mulVec_apply]
  have hcard : (∏ j : {j // U j = false}, (Fintype.card (PairAlphabet q j.1) : ℝ)) =
      (pairSet (fun k : {j // U j = false} => q k.1)).card := by
    rw [← card_pairAlphabet (fun k : {j // U j = false} => q k.1)]
    rw [Fintype.card_pi]
    push_cast
    rfl
  rw [hcard, pairAvg]
  push_cast
  rw [← sum_pairAlphabet (fun k : {j // U j = false} => q k.1)
    (fun xy => (F₁ (mergeFree U (pairsToVectors q a).1 xy.1) : ℂ) *
      (F₂ (mergeFree U (pairsToVectors q a).2 xy.2) : ℂ))]
  congr 1
  apply sum_congr rfl
  intro c _
  congr 2
  · congr 1
    funext j
    by_cases h : U j = false <;> simp [mergeFree, pairsToVectors, h]
  · congr 1
    funext j
    by_cases h : U j = false <;> simp [mergeFree, pairsToVectors, h]

/-- **Step 1's `∫‖E_U φ_x‖₂²` in the form of Step 3**: integrated over the prefix labels `x ∼ μ`
and the pair labels `a ∼ Unif(∏_j Ω_{q_j})`, it is the weighted mean of
`|∫ g₁ ⊗ g₂ dπ|²` over `ω = (x, a)`, `g_i` the factor `F_i(x, ·)` with the coordinates of `U`
frozen at `a`. -/
theorem expect_condProjOn_sq_eq [∀ j, Fact (q j).Prime] {X : Type*} [Fintype X] (μ : FiniteLaw X)
    (U : K → Bool) (F₁ F₂ : X → ResidueSpace q → ℝ) :
    (μ.expect fun x => (FiniteLaw.uniform (∀ j, PairAlphabet q j)).expect
        (fun a => (condProjOn (PairAlphabet q) U *ᵥ
          (fun b => F₁ x (pairsToVectors q b).1 * F₂ x (pairsToVectors q b).2)) a ^ 2)) =
      ∑ ω : X × (∀ j, PairAlphabet q j),
        (μ.weight ω.1 * (Fintype.card (∀ j, PairAlphabet q j) : ℝ)⁻¹) *
          ‖pairAvg (fun k : {j // U j = false} => q k.1)
            (fun x' => (F₁ ω.1 (mergeFree U (pairsToVectors q ω.2).1 x') : ℂ))
            (fun y' => (F₂ ω.1 (mergeFree U (pairsToVectors q ω.2).2 y') : ℂ))‖ ^ 2 := by
  have hpt : ∀ (x : X) (a : ∀ j, PairAlphabet q j),
      (condProjOn (PairAlphabet q) U *ᵥ
          (fun b => F₁ x (pairsToVectors q b).1 * F₂ x (pairsToVectors q b).2)) a ^ 2 =
        ‖pairAvg (fun k : {j // U j = false} => q k.1)
            (fun x' => (F₁ x (mergeFree U (pairsToVectors q a).1 x') : ℂ))
            (fun y' => (F₂ x (mergeFree U (pairsToVectors q a).2 y') : ℂ))‖ ^ 2 := by
    intro x a
    rw [← condProjOn_eq_pairAvg q U (F₁ x) (F₂ x) a, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hpt]
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  simp only [FiniteLaw.uniform]
  ring

end Identification

end Sarkozy.Cancellation
