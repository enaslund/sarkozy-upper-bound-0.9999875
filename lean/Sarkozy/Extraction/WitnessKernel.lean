module

public import Sarkozy.Influence.SquareShift

/-!
# Witness kernels with acyclic digraphs (`lem:matching:kernel`(a))

`paper/sections/16_extraction.tex`. For a set `𝒦 ⊆ {1, …, k}²` containing the diagonal and
signs `ς_{il} = ±1`, the operator with kernel `∏_{(i,l)∈𝒦} χ(ς_{il}(y_l - x_i))` on `L²(𝔽_p^k)`
(uniform probability) has norm at most `r^k = p^{-k/2}` when the digraph of the off-diagonal
pairs is acyclic. In counting-measure (`ℓ²`) normalization the kernel matrix has norm at most
`p^{k/2}`.

The formal statement uses the digraph in topologically sorted form (every acyclic digraph has
one, after relabelling the coordinates, which does not change norms): each vertex `l` has a set
of *parents* `i < l`, and the kernel is
`∏_l χ(ς_{ll}(y_l - x_l)) ∏_{i ∈ parents l} χ(ς_{il}(y_l - x_i))` (`sortedWitnessKernel`).
`sortedWitnessKernel_opBound` is the bound `‖·‖_{ℓ²} ≤ √p^k`, proved as in the paper by peeling
off coordinate `0`, a source: the operator factors as a Gauss operator in that coordinate, a
multiplication by a function of modulus one, and the kernel of the remaining digraph.

Auxiliary operator bounds: `opBound_tensor_left`, `opBound_tensor_right` (an operator tensored
with the identity keeps its bound), `opBound_diag` (multiplications by functions of modulus at
most one), `OpBound.equiv` (relabelling).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy.Influence

section Operators

variable {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]

/-- An operator acting in the first coordinate, tensored with the identity. -/
theorem opBound_tensor_left [DecidableEq W] {A : U → V → ℝ} {Λ : ℝ}
    (h : OpBound univ univ A Λ) :
    OpBound univ univ (fun (x : U × W) (y : V × W) => A x.1 y.1 * (if x.2 = y.2 then 1 else 0))
      Λ := by
  intro g
  have hrow : ∀ x : U × W, ∑ y : V × W, A x.1 y.1 * (if x.2 = y.2 then 1 else 0) * g y =
      ∑ v : V, A x.1 v * g (v, x.2) := by
    intro x
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun v _ => ?_
    rw [sum_eq_single x.2]
    · simp
    · intro w _ hw; simp [Ne.symm hw]
    · intro h'; exact absurd (mem_univ _) h'
  simp_rw [hrow]
  calc ∑ x : U × W, (∑ v : V, A x.1 v * g (v, x.2)) ^ 2
      = ∑ w : W, ∑ u : U, (∑ v : V, A u v * g (v, w)) ^ 2 := by
        rw [Fintype.sum_prod_type, sum_comm]
    _ ≤ ∑ w : W, Λ ^ 2 * ∑ v : V, g (v, w) ^ 2 :=
        sum_le_sum fun w _ => h (fun v => g (v, w))
    _ = Λ ^ 2 * ∑ y : V × W, g y ^ 2 := by
        rw [← mul_sum, Fintype.sum_prod_type, sum_comm]

/-- An operator acting in the second coordinate, tensored with the identity. -/
theorem opBound_tensor_right [DecidableEq W] {A : U → V → ℝ} {Λ : ℝ}
    (h : OpBound univ univ A Λ) :
    OpBound univ univ (fun (x : W × U) (y : W × V) => (if x.1 = y.1 then 1 else 0) * A x.2 y.2)
      Λ := by
  intro g
  have hrow : ∀ x : W × U, ∑ y : W × V, (if x.1 = y.1 then 1 else 0) * A x.2 y.2 * g y =
      ∑ v : V, A x.2 v * g (x.1, v) := by
    intro x
    rw [Fintype.sum_prod_type, sum_eq_single x.1]
    · simp
    · intro w _ hw; simp [Ne.symm hw]
    · intro h'; exact absurd (mem_univ _) h'
  simp_rw [hrow]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, mul_sum]
  exact sum_le_sum fun w _ => h (fun v => g (w, v))

/-- A multiplication by a function of modulus at most one. -/
theorem opBound_diag [DecidableEq U] (m : U → ℝ) (hm : ∀ u, |m u| ≤ 1) :
    OpBound univ univ (fun x y : U => if x = y then m x else 0) 1 := by
  intro g
  have hrow : ∀ x : U, ∑ y : U, (if x = y then m x else 0) * g y = m x * g x := by
    intro x
    rw [sum_eq_single x]
    · simp
    · intro y _ hy; simp [Ne.symm hy]
    · intro h'; exact absurd (mem_univ _) h'
  simp_rw [hrow]
  rw [one_pow, one_mul]
  refine sum_le_sum fun x _ => ?_
  have h1 : (m x) ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hm x)
  rw [mul_pow]
  nlinarith [sq_nonneg (g x)]

/-- Relabelling the rows and columns does not change an operator bound. -/
theorem OpBound.equiv {U' V' : Type*} [Fintype U'] [Fintype V'] {A : U → V → ℝ} {Λ : ℝ}
    (h : OpBound univ univ A Λ) (e : U' ≃ U) (e' : V' ≃ V) :
    OpBound univ univ (fun x y => A (e x) (e' y)) Λ := by
  intro g
  have h1 := h (fun v => g (e'.symm v))
  have hinner : ∀ u : U, ∑ y : V', A u (e' y) * g y = ∑ v : V, A u v * g (e'.symm v) := by
    intro u
    exact Fintype.sum_equiv e' (fun y => A u (e' y) * g y) (fun v => A u v * g (e'.symm v))
      (fun y => by simp)
  have hrows : ∑ x : U', (∑ y : V', A (e x) (e' y) * g y) ^ 2 =
      ∑ u : U, (∑ v : V, A u v * g (e'.symm v)) ^ 2 :=
    Fintype.sum_equiv e (fun x => (∑ y : V', A (e x) (e' y) * g y) ^ 2)
      (fun u => (∑ v : V, A u v * g (e'.symm v)) ^ 2) (fun x => by rw [hinner])
  have hcols : ∑ y : V', g y ^ 2 = ∑ v : V, g (e'.symm v) ^ 2 :=
    Fintype.sum_equiv e' _ _ fun y => by simp
  rw [hrows, hcols]
  exact h1

/-- Bounds pass to pointwise equal kernels. -/
theorem OpBound.congr' {A B : U → V → ℝ} {Λ Λ' : ℝ} (h : OpBound univ univ A Λ)
    (hAB : ∀ x y, A x y = B x y) (hΛ : Λ = Λ') : OpBound univ univ B Λ' := by
  have : A = B := funext fun x => funext fun y => hAB x y
  rw [← this, ← hΛ]; exact h

end Operators

/-! ## The sorted witness kernel -/

variable {p : ℕ} [Fact p.Prime]

/-- Topologically sorted witness data on `k` vertices: parents `i < l` and signs. -/
structure SortedWitness (k : ℕ) where
  parents : Fin k → Finset (Fin k)
  lt : ∀ l, ∀ i ∈ parents l, i < l
  sign : Fin k → Fin k → ZMod p
  sign_pm : ∀ i l, sign i l = 1 ∨ sign i l = -1

/-- The kernel `∏_l χ(ς_{ll}(y_l - x_l)) ∏_{i ∈ parents l} χ(ς_{il}(y_l - x_i))`. -/
noncomputable def sortedWitnessKernel {k : ℕ} (D : SortedWitness (p := p) k)
    (x y : Fin k → ZMod p) : ℝ :=
  ∏ l, (chiR (D.sign l l * (y l - x l)) * ∏ i ∈ D.parents l, chiR (D.sign i l * (y l - x i)))

/-- Removing vertex `0`: the parents of the remaining vertices, shifted down. -/
noncomputable def SortedWitness.tail {k : ℕ} (D : SortedWitness (p := p) (k + 1)) : SortedWitness (p := p) k where
  parents l := (D.parents l.succ).preimage Fin.succ (Fin.succ_injective _).injOn
  lt l i hi := by
    rw [mem_preimage] at hi
    exact Fin.succ_lt_succ_iff.mp (D.lt _ _ hi)
  sign i l := D.sign i.succ l.succ
  sign_pm i l := D.sign_pm _ _

theorem chiR_sign_mul_abs_le (a t : ZMod p) : |chiR (a * t)| ≤ 1 := by
  unfold chiR
  rcases eq_or_ne (a * t) 0 with h | h
  · rw [h, quadraticChar_zero]; simp
  · rcases quadraticChar_dichotomy h with h' | h' <;> rw [h'] <;> simp

/-- The factorization of the kernel at vertex `0`. -/
theorem sortedWitnessKernel_succ {k : ℕ} (D : SortedWitness (p := p) (k + 1))
    (x₀ y₀ : ZMod p) (x y : Fin k → ZMod p) :
    sortedWitnessKernel D (Fin.cons x₀ x) (Fin.cons y₀ y) =
      chiR (D.sign 0 0 * (y₀ - x₀)) *
        ((∏ l : Fin k, if (0 : Fin (k + 1)) ∈ D.parents l.succ then
            chiR (D.sign 0 l.succ * (y l - x₀)) else 1) *
          sortedWitnessKernel D.tail x y) := by
  unfold sortedWitnessKernel
  rw [Fin.prod_univ_succ]
  have hp0 : D.parents 0 = ∅ := by
    ext i; simp only [Finset.notMem_empty, iff_false]; intro hi
    exact absurd (D.lt 0 i hi) (Fin.not_lt_zero i)
  simp only [Fin.cons_zero, Fin.cons_succ, hp0, prod_empty, mul_one]
  congr 1
  rw [← prod_mul_distrib]
  -- split the parents of `l.succ` into `0` and the shifted parents of the tail
  have hsplit : ∀ l : Fin k, ∏ i ∈ D.parents l.succ,
      chiR (D.sign i l.succ * (y l - (Fin.cons x₀ x : Fin (k + 1) → ZMod p) i)) =
      (if (0 : Fin (k + 1)) ∈ D.parents l.succ then chiR (D.sign 0 l.succ * (y l - x₀)) else 1) *
        ∏ i ∈ D.tail.parents l, chiR (D.tail.sign i l * (y l - x i)) := by
    intro l
    have hdecomp : D.parents l.succ = (D.parents l.succ).filter (fun i => i = 0) ∪
        ((D.tail.parents l).map (Fin.succEmb k)) := by
      ext i
      simp only [mem_union, mem_filter, mem_map, Fin.coe_succEmb, SortedWitness.tail, mem_preimage]
      constructor
      · intro hi
        rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
        · exact Or.inl ⟨hi, h0⟩
        · exact Or.inr ⟨j, hi, rfl⟩
      · rintro (⟨hi, _⟩ | ⟨j, hj, rfl⟩)
        · exact hi
        · exact hj
    have hdisj : Disjoint ((D.parents l.succ).filter (fun i => i = 0))
        ((D.tail.parents l).map (Fin.succEmb k)) := by
      rw [disjoint_left]
      intro i hi hi'
      rw [mem_filter] at hi
      obtain ⟨j, _, rfl⟩ := mem_map.mp hi'
      exact Fin.succ_ne_zero j hi.2
    have hzero : ∏ i ∈ (D.parents l.succ).filter (fun i => i = 0),
        chiR (D.sign i l.succ * (y l - (Fin.cons x₀ x : Fin (k + 1) → ZMod p) i)) =
        if (0 : Fin (k + 1)) ∈ D.parents l.succ then chiR (D.sign 0 l.succ * (y l - x₀)) else 1 := by
      by_cases h0 : (0 : Fin (k + 1)) ∈ D.parents l.succ
      · have hf : (D.parents l.succ).filter (fun i => i = 0) = {0} := by
          ext i; simp only [mem_filter, mem_singleton]
          constructor
          · rintro ⟨_, h⟩; exact h
          · rintro rfl; exact ⟨h0, rfl⟩
        rw [hf, prod_singleton]
        simp only [h0, ↓reduceIte, Fin.cons_zero]
      · have hf : (D.parents l.succ).filter (fun i => i = 0) = ∅ := by
          ext i; simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
          rintro hi rfl; exact h0 hi
        rw [hf, prod_empty]
        simp only [h0, ↓reduceIte]
    have hrest : ∏ i ∈ (D.tail.parents l).map (Fin.succEmb k),
        chiR (D.sign i l.succ * (y l - (Fin.cons x₀ x : Fin (k + 1) → ZMod p) i)) =
        ∏ i ∈ D.tail.parents l, chiR (D.tail.sign i l * (y l - x i)) := by
      rw [prod_map]
      refine prod_congr rfl fun j _ => ?_
      simp only [Fin.coe_succEmb, Fin.cons_succ, SortedWitness.tail]
    have hsplit' := prod_union hdisj (f := fun i =>
      chiR (D.sign i l.succ * (y l - (Fin.cons x₀ x : Fin (k + 1) → ZMod p) i)))
    rw [← hdecomp] at hsplit'
    rw [hsplit', hzero, hrest]
  refine prod_congr rfl fun l _ => ?_
  rw [hsplit l]
  simp only [SortedWitness.tail]
  ring

/-- The composite of the three factors, evaluated. -/
theorem composite_eval {k : ℕ} (D : SortedWitness (p := p) (k + 1))
    (x y : ZMod p × (Fin k → ZMod p)) :
    ∑ l : ZMod p × (Fin k → ZMod p),
      (∑ m : ZMod p × (Fin k → ZMod p), (if x.1 = m.1 then 1 else 0) *
          sortedWitnessKernel D.tail x.2 m.2 *
          (if m = l then (∏ j : Fin k, if (0 : Fin (k + 1)) ∈ D.parents j.succ then
            chiR (D.sign 0 j.succ * (m.2 j - m.1)) else 1) else 0)) *
        (chiR (D.sign 0 0 * (y.1 - l.1)) * (if l.2 = y.2 then 1 else 0)) =
      sortedWitnessKernel D (Fin.cons x.1 x.2) (Fin.cons y.1 y.2) := by
  rw [sortedWitnessKernel_succ]
  have hinner : ∀ l : ZMod p × (Fin k → ZMod p),
      (∑ m : ZMod p × (Fin k → ZMod p), (if x.1 = m.1 then 1 else 0) *
          sortedWitnessKernel D.tail x.2 m.2 *
          (if m = l then (∏ j : Fin k, if (0 : Fin (k + 1)) ∈ D.parents j.succ then
            chiR (D.sign 0 j.succ * (m.2 j - m.1)) else 1) else 0)) =
      (if x.1 = l.1 then 1 else 0) * sortedWitnessKernel D.tail x.2 l.2 *
        (∏ j : Fin k, if (0 : Fin (k + 1)) ∈ D.parents j.succ then
            chiR (D.sign 0 j.succ * (l.2 j - l.1)) else 1) := by
    intro l
    rw [sum_eq_single l]
    · simp only [↓reduceIte]
    · intro m _ hm; simp only [hm, ↓reduceIte, mul_zero]
    · intro h'; exact absurd (mem_univ _) h'
  simp_rw [hinner]
  rw [sum_eq_single (x.1, y.2)]
  · simp only [↓reduceIte, mul_one, one_mul]
    ring
  · intro l _ hl
    by_cases h1 : x.1 = l.1
    · have h2 : l.2 ≠ y.2 := fun h2 => hl (Prod.ext h1.symm h2)
      simp only [h2, ↓reduceIte, mul_zero]
    · simp only [h1, ↓reduceIte, zero_mul]
  · intro h'; exact absurd (mem_univ _) h'

/-- **`lem:matching:kernel`(a)**: the sorted witness kernel on `k` vertices has `ℓ²` operator
norm at most `√p^k`; in the uniform normalization, `‖T_𝒦‖ ≤ r^k`. -/
theorem sortedWitnessKernel_opBound (hp2 : p ≠ 2) :
    ∀ {k : ℕ} (D : SortedWitness (p := p) k),
      OpBound univ univ (sortedWitnessKernel D) (Real.sqrt p ^ k)
  | 0, D => by
      intro g
      have hone : ∀ x y : Fin 0 → ZMod p, sortedWitnessKernel D x y = 1 := fun x y => by
        simp [sortedWitnessKernel]
      simp_rw [hone, one_mul, pow_zero, one_pow, one_mul]
      have huniq : ∀ z : Fin 0 → ZMod p, z = Fin.elim0 := fun z => funext fun i => i.elim0
      rw [Fintype.sum_eq_single (Fin.elim0 : Fin 0 → ZMod p) (fun z hz => absurd (huniq z) hz),
        Fintype.sum_eq_single (Fin.elim0 : Fin 0 → ZMod p) (fun z hz => absurd (huniq z) hz),
        Fintype.sum_eq_single (Fin.elim0 : Fin 0 → ZMod p) (fun z hz => absurd (huniq z) hz)]
  | k + 1, D => by
      have hG : OpBound univ univ
          (fun (x : ZMod p × (Fin k → ZMod p)) (y : ZMod p × (Fin k → ZMod p)) =>
            chiR (D.sign 0 0 * (y.1 - x.1)) * (if x.2 = y.2 then 1 else 0)) (Real.sqrt p) := by
        have hpal := (opBound_paley (p := p) hp2).smul (chiR (D.sign 0 0))
        have habs : |chiR (D.sign 0 0)| = 1 := by
          rcases chiR_sign (D.sign_pm 0 0) with h | h <;> rw [h] <;> simp
        rw [habs, one_mul] at hpal
        have hpal' : OpBound univ univ (fun x y : ZMod p => chiR (D.sign 0 0 * (y - x)))
            (Real.sqrt p) :=
          OpBound.congr' (A := fun x y : ZMod p => chiR (D.sign 0 0) * chiR (y - x)) hpal
            (fun x y => by rw [chiR_mul]) rfl
        exact opBound_tensor_left (U := ZMod p) (V := ZMod p) (W := Fin k → ZMod p)
          (A := fun x y : ZMod p => chiR (D.sign 0 0 * (y - x))) hpal'
      have hM : OpBound univ univ (fun (x y : ZMod p × (Fin k → ZMod p)) => if x = y then
          (∏ l : Fin k, if (0 : Fin (k + 1)) ∈ D.parents l.succ then
            chiR (D.sign 0 l.succ * (x.2 l - x.1)) else 1) else 0) 1 := by
        apply opBound_diag
        intro u
        rw [abs_prod]
        refine prod_le_one₀ (fun l _ => abs_nonneg _) fun l _ => ?_
        split_ifs
        · exact chiR_sign_mul_abs_le _ _
        · simp
      have hT : OpBound univ univ (fun (x y : ZMod p × (Fin k → ZMod p)) =>
          (if x.1 = y.1 then 1 else 0) * sortedWitnessKernel D.tail x.2 y.2)
          (Real.sqrt p ^ k) :=
        opBound_tensor_right (sortedWitnessKernel_opBound hp2 D.tail)
      have hcomp := OpBound.equiv ((hT.comp hM).comp hG)
        (Fin.consEquiv (fun _ : Fin (k + 1) => ZMod p)).symm
        (Fin.consEquiv (fun _ : Fin (k + 1) => ZMod p)).symm
      refine OpBound.congr' hcomp (fun x y => ?_) (by rw [mul_one, pow_succ])
      have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
      have hy : y = Fin.cons (y 0) (Fin.tail y) := (Fin.cons_self_tail y).symm
      have := composite_eval D (x 0, Fin.tail x) (y 0, Fin.tail y)
      rw [← hx, ← hy] at this
      exact this

end Sarkozy.Extraction
