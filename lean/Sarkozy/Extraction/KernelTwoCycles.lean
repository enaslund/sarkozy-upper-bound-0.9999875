module

public import Sarkozy.Extraction.KernelAcyclic
public import Sarkozy.Extraction.KernelMultipliers

/-!
# Witness kernels with two-vertex components (`lem:matching:kernel`(b))

`paper/sections/16_extraction.tex`, `lem:matching:kernel`(b). Let `𝒦 ⊆ {1, …, k}²` contain the
diagonal, let `ς_{il} = ±1`, and let `T_𝒦` have the kernel `∏_{(i,l) ∈ 𝒦} χ(ς_{il}(y_l - x_i))`
(`witnessKernel`, `KernelAcyclic.lean`). If every strongly connected component of the digraph
`D_𝒦` has at most two vertices, `β` of them two, and `P_in`, `P_out` are the multiplications by
the indicators of sets of tuples `y`, resp. `x`, with `y_i ≠ y_l`, resp. `x_i ≠ x_l`, for every
two-vertex component `{i, l}`, then `‖P_out T_𝒦 P_in‖ ≤ 2^β r^k`.

**The four-cycle bound is a hypothesis here.** The case `a = b = 2` of `cor:dl:normalized`(a)
(`paper/sections/15_second_order.tex`) enters as `FourCycleBound p`. Since 1 November 2026 it is
derived from `Target.FourCycle` (`thm:dl:K`) in `Sarkozy/DLK/` (`DLK.fourCycleBound`, and the
`_of_fourCycle` versions of the theorems below). Its statement:
for all signs `ς_{ab} = ±1`, the complete rectangle kernel `∏_{a,b ≤ 2} χ(ς_{ab}(y_b - x_a))` on
`𝔽_p² × 𝔽_p²`, compressed to the pairs with distinct coordinates on both sides, has `ℓ²` norm at
most `2 √p² = 2p`, i.e. norm at most `2/p = 2r²` for uniform probability.

Normalization: `OpBound R C A Λ` bounds the block `R × C` of the kernel matrix `A` in `ℓ²`
(counting measure), i.e. the compression `P_out A P_in` with `R`, `C` the supports of `P_out`,
`P_in`. The paper's bound `2^β r^k` for uniform probability is `2^β √p^k` here.

* `blockWitnessKernel_opBound`: the **sorted-block form**. A `BlockWitness` assigns to every
  coordinate a block `blk i ∈ ℕ` (the blocks, the fibres of `blk`, are listed in increasing
  order); every block has at most two vertices, every pair of `𝒦` goes from a block to the same
  or a later block, and every block carries all pairs inside it (for a two-vertex block the
  complete rectangle, both connectors present). `β` is the number of two-vertex blocks
  (`BlockWitness.numTwo`). The proof follows the paper: step `t` replaces the coordinates `y` of
  block `t` by `x`, through the block operator `B_t` (`BlockWitness.step`) and the multiplier
  `M_t` of the pairs from block `t` to later blocks (`BlockWitness.mult`); the kernel identity
  is `BlockWitness.tail_succ_mul`, and `BlockWitness.tail_opBound` multiplies the bounds, by
  induction over the blocks. The intermediate sums run over the tuples injective on the
  two-vertex blocks (`BlockWitness.tail_eq_sum`): this is the insertion of `Q_in`, `Q_out`
  around each two-vertex block, and `‖Q_out B_t Q_in‖ ≤ 2 √p²` is the four-cycle bound tensored
  with the identity (`twoCycle_pair_opBound`). A one-vertex block is a Gauss operator in its
  coordinate (`twoCycle_single_opBound`, norm `√p`). `witnessKernel_rectangle_opBound`: the
  complete rectangle on two coordinates (`rem:extraction-kernels`), one block, `β = 1`.
* `witnessKernel_opBound_twoCycles`: the **general form**, with the strongly connected
  components defined by mutual reachability (`twoCycleMutual`: `Relation.ReflTransGen` of the
  arcs both ways; `twoCycleComponent`, `twoCycleCount`). The components are ordered along the
  condensation of `D_𝒦` (`twoCycleBlk`: by the number of vertices from which a component is
  reachable, ties broken by its least vertex), which gives a `BlockWitness` with the same pairs
  (`twoCycleBlockWitness`); strong connectivity of a two-vertex component gives both arcs
  (`twoCycle_mem_of_mutual`). Since blocks are given by a block function rather than by
  positions, no renumbering of the coordinates is needed.
  `witnessKernel_opBound_twoCycles_injective`: `P_in`, `P_out` the injective tuples.

As in `KernelAcyclic.lean`, `ς` is a function on all pairs; the general form assumes `ς = ±1`
only on `𝒦`, the sorted-block form on all pairs. Both assume `p ≠ 2`.

Auxiliary: `twoCycle_opBound_congr` (kernels agreeing on the block), `twoCycle_opBound_compress`,
`twoCycle_opBound_of_compress` (a block bound is a bound of the compression `P_R A P_C`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy.Influence

/-! ## Compressions -/

section Compress

/-- Bounds pass to kernels that agree on the block `R × C`. -/
theorem twoCycle_opBound_congr {U V : Type*} {R : Finset U} {C : Finset V} {A B : U → V → ℝ}
    {Λ Λ' : ℝ} (h : OpBound R C A Λ) (hAB : ∀ x ∈ R, ∀ y ∈ C, A x y = B x y) (hΛ : Λ = Λ') :
    OpBound R C B Λ' := by
  intro g
  have e : ∀ x ∈ R, ∑ y ∈ C, B x y * g y = ∑ y ∈ C, A x y * g y := fun x hx =>
    sum_congr rfl fun y hy => by rw [hAB x hx y hy]
  rw [sum_congr rfl fun x hx => by rw [e x hx], ← hΛ]
  exact h g

variable {U V : Type*} [Fintype U] [Fintype V]

/-- A block bound is a bound of the compression `P_R A P_C` on all functions. -/
theorem twoCycle_opBound_compress [DecidableEq U] [DecidableEq V] {R : Finset U}
    {C : Finset V} {A : U → V → ℝ} {Λ : ℝ} (h : OpBound R C A Λ) :
    OpBound univ univ
      (fun x y => (if x ∈ R then 1 else 0) * A x y * (if y ∈ C then 1 else 0)) Λ := by
  intro g
  have e1 : ∀ x, ∑ y, (if x ∈ R then 1 else 0) * A x y * (if y ∈ C then 1 else 0) * g y =
      if x ∈ R then ∑ y ∈ C, A x y * g y else 0 := by
    intro x
    rw [← sum_subset (subset_univ C) (fun y _ hy => by simp [hy])]
    split_ifs with hx
    · exact sum_congr rfl fun y hy => by simp
    · simp
  simp_rw [e1]
  have e2 : ∑ x, (if x ∈ R then ∑ y ∈ C, A x y * g y else 0) ^ 2 =
      ∑ x ∈ R, (∑ y ∈ C, A x y * g y) ^ 2 := by
    rw [← sum_subset (subset_univ R) (fun x _ hx => by simp [hx])]
    exact sum_congr rfl fun x hx => by simp [hx]
  rw [e2]
  refine (h g).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg Λ))
  exact sum_le_sum_of_subset_of_nonneg (subset_univ C) fun y _ _ => sq_nonneg _

/-- Conversely, a bound of the compression `P_R A P_C` is a block bound. -/
theorem twoCycle_opBound_of_compress [DecidableEq U] [DecidableEq V] {R : Finset U}
    {C : Finset V} {A : U → V → ℝ} {Λ : ℝ}
    (h : OpBound univ univ
      (fun x y => (if x ∈ R then 1 else 0) * A x y * (if y ∈ C then 1 else 0)) Λ) :
    OpBound R C A Λ := by
  intro g
  have h1 := h (fun y => if y ∈ C then g y else 0)
  have e1 : ∀ x, ∑ y, (if x ∈ R then 1 else 0) * A x y * (if y ∈ C then 1 else 0) *
      (if y ∈ C then g y else 0) = if x ∈ R then ∑ y ∈ C, A x y * g y else 0 := by
    intro x
    rw [← sum_subset (subset_univ C) (fun y _ hy => by simp [hy])]
    split_ifs with hx
    · exact sum_congr rfl fun y hy => by simp
    · simp
  simp_rw [e1] at h1
  have e2 : ∑ x, (if x ∈ R then ∑ y ∈ C, A x y * g y else 0) ^ 2 =
      ∑ x ∈ R, (∑ y ∈ C, A x y * g y) ^ 2 := by
    rw [← sum_subset (subset_univ R) (fun x _ hx => by simp [hx])]
    exact sum_congr rfl fun x hx => by simp [hx]
  have e3 : ∑ y, (if y ∈ C then g y else 0) ^ 2 = ∑ y ∈ C, g y ^ 2 := by
    rw [← sum_subset (subset_univ C) (fun y _ hy => by simp [hy])]
    exact sum_congr rfl fun y hy => by simp [hy]
  rw [e2, e3] at h1
  exact h1

end Compress

/-! ## The four-cycle bound, as a hypothesis -/

variable {p : ℕ} [Fact p.Prime]

/-- The ordered pairs of distinct elements of `𝔽_p`. -/
def twoCycleOffDiag (p : ℕ) [Fact p.Prime] : Finset (ZMod p × ZMod p) :=
  univ.filter (fun z => z.1 ≠ z.2)

/-- The complete rectangle kernel `K(x, y) = ∏_{a, b ≤ 2} χ(ς_{ab}(y_b - x_a))`,
`x, y ∈ 𝔽_p²`. -/
noncomputable def twoCycleRectangle (ς : Fin 2 → Fin 2 → ZMod p) (x y : ZMod p × ZMod p) : ℝ :=
  ∏ a : Fin 2, ∏ b : Fin 2, chiR (ς a b * (![y.1, y.2] b - ![x.1, x.2] a))

/-- **`cor:dl:normalized`(a) for `a = b = 2`, taken as a hypothesis** (it is not formalized
here; `paper/sections/15_second_order.tex`). For all signs `ς_{ab} = ±1`, the complete rectangle
kernel `K(x, y) = ∏_{a, b ≤ 2} χ(ς_{ab}(y_b - x_a))` on `𝔽_p² × 𝔽_p²` (`twoCycleRectangle`),
compressed to the functions that vanish on the diagonal on both sides (rows and columns in
`twoCycleOffDiag`), has `ℓ²` (counting measure) operator norm at most `2 √p² = 2p`.

Normalization: for uniform probability on `𝔽_p²` the operator `f ↦ 𝔼_y K(·, y) f(y)` is `p⁻²`
times the kernel matrix, and both `L²` norms are `p⁻¹` times the `ℓ²` norms, so this is the
paper's bound `2/p = 2r²`; it is the bound `‖M_aff‖ ≤ 2p` of `thm:dl:K`. -/
def FourCycleBound (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ ς : Fin 2 → Fin 2 → ZMod p, (∀ a b, ς a b = 1 ∨ ς a b = -1) →
    OpBound (twoCycleOffDiag p) (twoCycleOffDiag p) (twoCycleRectangle ς) (2 * Real.sqrt p ^ 2)

/-! ## The block operators -/

/-- A one-vertex block: the Gauss operator in coordinate `i`, tensored with the identity in the
other coordinates, has `ℓ²` norm at most `√p`. -/
theorem twoCycle_single_opBound (hp2 : p ≠ 2) {k : ℕ} (i : Fin k) {ς : ZMod p}
    (hς : ς = 1 ∨ ς = -1) :
    OpBound univ univ (fun x y : Fin k → ZMod p =>
      (if ∀ j, j ≠ i → x j = y j then 1 else 0) * chiR (ς * (y i - x i))) (Real.sqrt p) := by
  have hT := Sarkozy.Extraction.opBound_tensor_left (U := ZMod p) (V := ZMod p)
    (W := {j // j ≠ i} → ZMod p) (A := fun a b : ZMod p => chiR (ς * (b - a)))
    (opBound_gauss hp2 hς)
  have hE := Sarkozy.Extraction.OpBound.equiv (U := ZMod p × ({j // j ≠ i} → ZMod p))
    (V := ZMod p × ({j // j ≠ i} → ZMod p)) (U' := Fin k → ZMod p) (V' := Fin k → ZMod p) hT
    (Equiv.funSplitAt i (ZMod p)) (Equiv.funSplitAt i (ZMod p))
  refine Sarkozy.Extraction.OpBound.congr' hE (fun x y => ?_) rfl
  simp only [Equiv.funSplitAt_apply]
  have hiff : ((fun j : {j // j ≠ i} => x j) = fun j : {j // j ≠ i} => y j) ↔
      ∀ j, j ≠ i → x j = y j := by
    rw [funext_iff]
    exact ⟨fun h j hj => h ⟨j, hj⟩, fun h j => h j j.2⟩
  rw [if_congr hiff rfl rfl, mul_comm]

/-- Splitting off the coordinates `i ≠ l`: `x ↦ ((x i, x l), x|_{j ≠ i, l})`. -/
def twoCycleSplit {k : ℕ} {i l : Fin k} (hil : i ≠ l) :
    (Fin k → ZMod p) ≃
      (ZMod p × ZMod p) × ({j' : {j // j ≠ i} // j' ≠ ⟨l, hil.symm⟩} → ZMod p) :=
  ((Equiv.funSplitAt i (ZMod p)).trans
    ((Equiv.refl (ZMod p)).prodCongr (Equiv.funSplitAt ⟨l, hil.symm⟩ (ZMod p)))).trans
    (Equiv.prodAssoc _ _ _).symm

omit [Fact p.Prime] in
theorem twoCycleSplit_apply {k : ℕ} {i l : Fin k} (hil : i ≠ l) (x : Fin k → ZMod p) :
    twoCycleSplit hil x = ((x i, x l), fun j' => x j'.1.1) := rfl

/-- A two-vertex block `{i, l}` carrying the complete rectangle: compressed to the tuples with
`x_i ≠ x_l` on both sides, the operator has `ℓ²` norm at most `2 √p²` (given the four-cycle
bound). -/
theorem twoCycle_pair_opBound (h4 : FourCycleBound p) {k : ℕ} {i l : Fin k} (hil : i ≠ l)
    (ς : Fin k → Fin k → ZMod p) (hς : ∀ a b, ς a b = 1 ∨ ς a b = -1) :
    OpBound (univ.filter (fun z : Fin k → ZMod p => z i ≠ z l))
      (univ.filter (fun z : Fin k → ZMod p => z i ≠ z l))
      (fun x y => (if ∀ j, j ≠ i → j ≠ l → x j = y j then 1 else 0) *
        (chiR (ς i i * (y i - x i)) * chiR (ς i l * (y l - x i)) *
          (chiR (ς l i * (y i - x l)) * chiR (ς l l * (y l - x l)))))
      (2 * Real.sqrt p ^ 2) := by
  have hK := twoCycle_opBound_compress
    (h4 (fun a b => ς (![i, l] a) (![i, l] b)) (fun a b => hς _ _))
  have hT := Sarkozy.Extraction.opBound_tensor_left (U := ZMod p × ZMod p)
    (V := ZMod p × ZMod p) (W := {j' : {j // j ≠ i} // j' ≠ ⟨l, hil.symm⟩} → ZMod p) hK
  have hE := Sarkozy.Extraction.OpBound.equiv
    (U := (ZMod p × ZMod p) × ({j' : {j // j ≠ i} // j' ≠ ⟨l, hil.symm⟩} → ZMod p))
    (V := (ZMod p × ZMod p) × ({j' : {j // j ≠ i} // j' ≠ ⟨l, hil.symm⟩} → ZMod p))
    (U' := Fin k → ZMod p) (V' := Fin k → ZMod p) hT (twoCycleSplit hil) (twoCycleSplit hil)
  refine twoCycle_opBound_of_compress (Sarkozy.Extraction.OpBound.congr' hE (fun x y => ?_) rfl)
  simp only [twoCycleSplit_apply]
  have hiff : ((fun j' : {j' : {j // j ≠ i} // j' ≠ ⟨l, hil.symm⟩} => x j'.1.1) =
      fun j' : {j' : {j // j ≠ i} // j' ≠ ⟨l, hil.symm⟩} => y j'.1.1) ↔
      ∀ j, j ≠ i → j ≠ l → x j = y j := by
    rw [funext_iff]
    refine ⟨fun h j hj hj' => h ⟨⟨j, hj⟩, fun h' => hj' (congrArg Subtype.val h')⟩,
      fun h j' => h j'.1.1 j'.1.2 fun h' => j'.2 (Subtype.ext h')⟩
  simp only [hiff, twoCycleOffDiag, twoCycleRectangle, mem_filter, mem_univ, true_and,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ## Sorted blocks -/

/-- Sorted block data for `lem:matching:kernel`(b): a set `𝒦 = pairs` of pairs of coordinates,
signs `±1`, and a block `blk i ∈ ℕ` for every coordinate (the blocks are the fibres of `blk`,
listed in increasing order). Every block has at most two vertices, every pair goes from a block
to the same or a later block, and every block carries all pairs inside it (the diagonal pair of
a one-vertex block, the complete rectangle of a two-vertex block). -/
structure BlockWitness (k : ℕ) where
  /-- The set `𝒦` of pairs `(i, l)`. -/
  pairs : Finset (Fin k × Fin k)
  /-- The block of each coordinate. -/
  blk : Fin k → ℕ
  /-- The signs `ς_{il}`. -/
  sign : Fin k → Fin k → ZMod p
  sign_pm : ∀ i l, sign i l = 1 ∨ sign i l = -1
  card_le : ∀ b, (univ.filter (fun i => blk i = b)).card ≤ 2
  forward : ∀ e ∈ pairs, blk e.1 ≤ blk e.2
  complete : ∀ i l, blk i = blk l → (i, l) ∈ pairs

namespace BlockWitness

variable {k : ℕ} (D : BlockWitness (p := p) k)

/-- The number `β` of two-vertex blocks. -/
def numTwo : ℕ :=
  ((univ.image D.blk).filter (fun b => (univ.filter (fun i => D.blk i = b)).card = 2)).card

/-- The tuples `x` with `x_i ≠ x_l` for every two-vertex block `{i, l}`. -/
def inj : Finset (Fin k → ZMod p) :=
  univ.filter (fun x => ∀ i l, i ≠ l → D.blk i = D.blk l → x i ≠ x l)

/-- The kernel of the blocks `≥ t`, tensored with the identity in the coordinates of the blocks
`< t`. -/
noncomputable def tail (t : ℕ) (x y : Fin k → ZMod p) : ℝ :=
  (if ∀ j, D.blk j < t → x j = y j then 1 else 0) *
    ∏ e ∈ D.pairs, if t ≤ D.blk e.1 then chiR (D.sign e.1 e.2 * (y e.2 - x e.1)) else 1

/-- The block operator `B_t` (the kernel of block `t`, tensored with the identity). -/
noncomputable def step (t : ℕ) (x y : Fin k → ZMod p) : ℝ :=
  (if ∀ j, D.blk j ≠ t → x j = y j then 1 else 0) *
    ∏ e ∈ D.pairs, if D.blk e.1 = t ∧ D.blk e.2 = t then
      chiR (D.sign e.1 e.2 * (y e.2 - x e.1)) else 1

/-- The multiplier `M_t`: the pairs from block `t` to later blocks. -/
noncomputable def mult (t : ℕ) (z : Fin k → ZMod p) : ℝ :=
  ∏ e ∈ D.pairs, if D.blk e.1 = t ∧ t < D.blk e.2 then
    chiR (D.sign e.1 e.2 * (z e.2 - z e.1)) else 1

/-- The number of coordinates in the blocks `≥ t`. -/
def levelCard (t : ℕ) : ℕ := (univ.filter (fun i => t ≤ D.blk i)).card

/-- The number of two-vertex blocks `≥ t`. -/
def levelTwo (t : ℕ) : ℕ :=
  ((univ.image D.blk).filter
    (fun b => t ≤ b ∧ (univ.filter (fun i => D.blk i = b)).card = 2)).card

/-- The pairs inside block `t` are the pairs of its vertices. -/
theorem prod_block (t : ℕ) (f : Fin k × Fin k → ℝ) :
    ∏ e ∈ D.pairs, (if D.blk e.1 = t ∧ D.blk e.2 = t then f e else 1) =
      ∏ e ∈ (univ.filter (fun i => D.blk i = t)) ×ˢ (univ.filter (fun i => D.blk i = t)),
        f e := by
  rw [← prod_filter]
  congr 1
  ext e
  simp only [mem_filter, mem_product, mem_univ, true_and]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨D.complete _ _ (h1.trans h2.symm), h1, h2⟩

/-- The block operator `B_t` has `ℓ²` norm at most `1`, `√p` or `2 √p²` on the tuples injective
on the two-vertex blocks, according as block `t` has `0`, `1` or `2` vertices. -/
theorem step_opBound (hp2 : p ≠ 2) (h4 : FourCycleBound p) (t : ℕ) :
    OpBound D.inj D.inj (D.step t)
      (2 ^ (if (univ.filter (fun i => D.blk i = t)).card = 2 then 1 else 0) *
        Real.sqrt p ^ (univ.filter (fun i => D.blk i = t)).card) := by
  have hc := D.card_le t
  rcases (show (univ.filter (fun i => D.blk i = t)).card = 0 ∨
      (univ.filter (fun i => D.blk i = t)).card = 1 ∨
      (univ.filter (fun i => D.blk i = t)).card = 2 by omega) with h0 | h1 | h2
  · -- an empty block: the identity
    have hF : univ.filter (fun i => D.blk i = t) = ∅ := card_eq_zero.mp h0
    have hnone : ∀ j, D.blk j ≠ t := fun j hj => by
      have hj' : j ∈ univ.filter (fun i => D.blk i = t) := mem_filter.mpr ⟨mem_univ _, hj⟩
      rw [hF] at hj'
      exact absurd hj' (notMem_empty _)
    have hId := (Sarkozy.Extraction.opBound_diag (fun _ : Fin k → ZMod p => (1 : ℝ))
      (fun _ => by simp)).subset (subset_univ D.inj) (subset_univ D.inj)
    refine twoCycle_opBound_congr hId (fun x _ y _ => ?_) (by rw [h0]; simp)
    unfold step
    rw [prod_block, hF, empty_product, prod_empty, mul_one]
    have hiff : (∀ j, D.blk j ≠ t → x j = y j) ↔ x = y :=
      ⟨fun h => funext fun j => h j (hnone j), fun h j _ => by rw [h]⟩
    simp only [hiff]
  · -- a one-vertex block: a Gauss operator
    obtain ⟨i, hi⟩ := card_eq_one.mp h1
    have hblk : ∀ j, D.blk j = t ↔ j = i := fun j => by
      simpa using congrArg (fun s => j ∈ s) hi
    have hG := (twoCycle_single_opBound hp2 i (D.sign_pm i i)).subset (subset_univ D.inj)
      (subset_univ D.inj)
    refine twoCycle_opBound_congr hG (fun x _ y _ => ?_) (by rw [h1]; simp)
    unfold step
    rw [prod_block, hi, singleton_product_singleton, prod_singleton]
    have hiff : (∀ j, D.blk j ≠ t → x j = y j) ↔ ∀ j, j ≠ i → x j = y j :=
      ⟨fun h j hj => h j fun h' => hj ((hblk j).mp h'),
        fun h j hj => h j fun h' => hj ((hblk j).mpr h')⟩
    simp only [hiff]
  · -- a two-vertex block: the four-cycle bound
    obtain ⟨i, l, hil, hF⟩ := card_eq_two.mp h2
    have hblk : ∀ j, D.blk j = t ↔ j = i ∨ j = l := fun j => by
      simpa using congrArg (fun s => j ∈ s) hF
    have hsub : D.inj ⊆ univ.filter (fun z : Fin k → ZMod p => z i ≠ z l) := by
      intro x hx
      rw [inj, mem_filter] at hx
      exact mem_filter.mpr ⟨mem_univ _, hx.2 i l hil
        (((hblk i).mpr (Or.inl rfl)).trans ((hblk l).mpr (Or.inr rfl)).symm)⟩
    have hP := (twoCycle_pair_opBound h4 hil D.sign D.sign_pm).subset hsub hsub
    refine twoCycle_opBound_congr hP (fun x _ y _ => ?_) (by rw [h2]; simp)
    unfold step
    rw [prod_block, hF, prod_product, prod_pair hil, prod_pair hil, prod_pair hil]
    have hiff : (∀ j, D.blk j ≠ t → x j = y j) ↔ ∀ j, j ≠ i → j ≠ l → x j = y j :=
      ⟨fun h j hj hj' => h j fun h' => ((hblk j).mp h').elim hj hj',
        fun h j hj => h j (fun h' => hj ((hblk j).mpr (Or.inl h')))
          (fun h' => hj ((hblk j).mpr (Or.inr h')))⟩
    simp only [hiff]

/-! ### The factorization `T = M_n B_n ⋯ M_1 B_1`, one block at a time -/

/-- Removing block `t` from the blocks `≥ t`: the number of coordinates. -/
theorem levelCard_succ (t : ℕ) :
    D.levelCard t = D.levelCard (t + 1) + (univ.filter (fun i => D.blk i = t)).card := by
  unfold levelCard
  rw [card_filter, card_filter, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

/-- Removing block `t` from the blocks `≥ t`: the number of two-vertex blocks. -/
theorem levelTwo_succ (t : ℕ) :
    D.levelTwo t = D.levelTwo (t + 1) +
      (if (univ.filter (fun i => D.blk i = t)).card = 2 then 1 else 0) := by
  unfold levelTwo
  rw [card_filter, card_filter]
  have e : ∀ b ∈ univ.image D.blk,
      (if t ≤ b ∧ (univ.filter (fun i => D.blk i = b)).card = 2 then 1 else 0) =
      (if t + 1 ≤ b ∧ (univ.filter (fun i => D.blk i = b)).card = 2 then 1 else 0) +
        (if t = b then (if (univ.filter (fun i => D.blk i = b)).card = 2 then 1 else 0)
          else 0) := by
    intro b _
    split_ifs <;> omega
  rw [sum_congr rfl e, sum_add_distrib, sum_ite_eq]
  by_cases h2 : (univ.filter (fun i => D.blk i = t)).card = 2
  · have ht : t ∈ univ.image D.blk := by
      obtain ⟨i, hi⟩ : (univ.filter (fun i => D.blk i = t)).Nonempty := by
        rw [← card_pos, h2]
        norm_num
      exact mem_image.mpr ⟨i, mem_univ _, (mem_filter.mp hi).2⟩
    rw [ite_eq_left ht]
  · simp [h2]

/-- One factor of the kernel identity, for a pair `e ∈ 𝒦`: at the intermediate point
`z = (x on block t, y elsewhere)`. -/
theorem tail_factor (t : ℕ) (x y : Fin k → ZMod p) (e : Fin k × Fin k) (he : e ∈ D.pairs) :
    (if t + 1 ≤ D.blk e.1 then
        chiR (D.sign e.1 e.2 * ((if D.blk e.2 = t then x e.2 else y e.2) - x e.1)) else 1) *
      (if D.blk e.1 = t ∧ t < D.blk e.2 then chiR (D.sign e.1 e.2 *
        ((if D.blk e.2 = t then x e.2 else y e.2) - (if D.blk e.1 = t then x e.1 else y e.1)))
        else 1) *
      (if D.blk e.1 = t ∧ D.blk e.2 = t then
        chiR (D.sign e.1 e.2 * (y e.2 - (if D.blk e.1 = t then x e.1 else y e.1))) else 1) =
      if t ≤ D.blk e.1 then chiR (D.sign e.1 e.2 * (y e.2 - x e.1)) else 1 := by
  have hf := D.forward e he
  rcases lt_trichotomy (D.blk e.1) t with h1 | h1 | h1
  · have a1 : ¬ t + 1 ≤ D.blk e.1 := by omega
    have a2 : ¬ (D.blk e.1 = t ∧ t < D.blk e.2) := by omega
    have a3 : ¬ (D.blk e.1 = t ∧ D.blk e.2 = t) := by omega
    have a4 : ¬ t ≤ D.blk e.1 := by omega
    rw [ite_eq_right a1, ite_eq_right a2, ite_eq_right a3, ite_eq_right a4]
    ring
  · by_cases h2 : D.blk e.2 = t
    · have a1 : ¬ t + 1 ≤ D.blk e.1 := by omega
      have a2 : ¬ (D.blk e.1 = t ∧ t < D.blk e.2) := by omega
      have a4 : t ≤ D.blk e.1 := by omega
      rw [ite_eq_right a1, ite_eq_right a2, ite_eq_left ⟨h1, h2⟩, ite_eq_left a4, ite_eq_left h1]
      ring
    · have a1 : ¬ t + 1 ≤ D.blk e.1 := by omega
      have a2 : D.blk e.1 = t ∧ t < D.blk e.2 := ⟨h1, by omega⟩
      have a3 : ¬ (D.blk e.1 = t ∧ D.blk e.2 = t) := fun h => h2 h.2
      have a4 : t ≤ D.blk e.1 := by omega
      rw [ite_eq_right a1, ite_eq_left a2, ite_eq_right a3, ite_eq_left a4, ite_eq_right h2,
        ite_eq_left h1]
      ring
  · have h2 : D.blk e.2 ≠ t := by omega
    have a1 : t + 1 ≤ D.blk e.1 := by omega
    have a2 : ¬ (D.blk e.1 = t ∧ t < D.blk e.2) := by omega
    have a3 : ¬ (D.blk e.1 = t ∧ D.blk e.2 = t) := by omega
    have a4 : t ≤ D.blk e.1 := by omega
    rw [ite_eq_left a1, ite_eq_right a2, ite_eq_right a3, ite_eq_left a4, ite_eq_right h2]
    ring

/-- The kernel identity at the intermediate point `z = (x on block t, y elsewhere)`: the pairs
of `𝒦` are used exactly once, inside block `t` in `B_t`, from block `t` to later blocks in
`M_t`, and between later blocks in the kernel of the blocks `> t`. -/
theorem tail_succ_mul (t : ℕ) (x y : Fin k → ZMod p) :
    D.tail (t + 1) x (fun j => if D.blk j = t then x j else y j) *
      D.mult t (fun j => if D.blk j = t then x j else y j) *
        D.step t (fun j => if D.blk j = t then x j else y j) y = D.tail t x y := by
  have i1 : (∀ j, D.blk j < t + 1 → x j = if D.blk j = t then x j else y j) ↔
      (∀ j, D.blk j < t → x j = y j) := by
    constructor
    · intro h j hj
      have h' := h j (by omega)
      rwa [ite_eq_right (show D.blk j ≠ t by omega)] at h'
    · intro h j hj
      by_cases hjt : D.blk j = t
      · rw [ite_eq_left hjt]
      · rw [ite_eq_right hjt]
        exact h j (by omega)
  have i2 : ∀ j, D.blk j ≠ t → (if D.blk j = t then x j else y j) = y j := fun j hj =>
    ite_eq_right hj
  have hprod := prod_congr rfl fun e he => D.tail_factor t x y e he
  rw [prod_mul_distrib, prod_mul_distrib] at hprod
  simp only [tail, mult, step]
  rw [ite_eq_left i2, ← hprod]
  simp only [i1]
  ring

/-- Away from the intermediate point the composite kernel vanishes. -/
theorem tail_succ_mul_eq_zero (t : ℕ) (x y z : Fin k → ZMod p)
    (hz : z ≠ fun j => if D.blk j = t then x j else y j) :
    D.tail (t + 1) x z * D.mult t z * D.step t z y = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
  have hj : z j ≠ if D.blk j = t then x j else y j := hj
  by_cases hb : D.blk j = t
  · rw [ite_eq_left hb] at hj
    have h' : ¬ ∀ j, D.blk j < t + 1 → x j = z j := fun h => hj (h j (by omega)).symm
    simp only [tail, ite_eq_right h', zero_mul]
  · rw [ite_eq_right hb] at hj
    have h' : ¬ ∀ j, D.blk j ≠ t → z j = y j := fun h => hj (h j hb)
    simp only [step, ite_eq_right h', zero_mul, mul_zero]

/-- The kernel identity `P_out T_{≥ t} P_in = P_out T_{> t} M_t B_t P_in` on the tuples
injective on the two-vertex blocks; the intermediate sums run over such tuples (the insertion of
`Q_in`, `Q_out` around the blocks). -/
theorem tail_eq_sum (t : ℕ) {x y : Fin k → ZMod p} (hx : x ∈ D.inj) (hy : y ∈ D.inj) :
    ∑ z ∈ D.inj, (∑ w ∈ D.inj, D.tail (t + 1) x w * (if w = z then D.mult t w else 0)) *
      D.step t z y = D.tail t x y := by
  have hzs : (fun j => if D.blk j = t then x j else y j) ∈ D.inj := by
    rw [inj, mem_filter] at hx hy ⊢
    refine ⟨mem_univ _, fun i l hil hb => ?_⟩
    dsimp only
    by_cases hi : D.blk i = t
    · have hl : D.blk l = t := hb ▸ hi
      rw [ite_eq_left hi, ite_eq_left hl]
      exact hx.2 i l hil hb
    · have hl : D.blk l ≠ t := fun h => hi (hb.trans h)
      rw [ite_eq_right hi, ite_eq_right hl]
      exact hy.2 i l hil hb
  have hinner : ∀ z ∈ D.inj, ∑ w ∈ D.inj, D.tail (t + 1) x w *
      (if w = z then D.mult t w else 0) = D.tail (t + 1) x z * D.mult t z := by
    intro z hz
    rw [sum_eq_single_of_mem z hz]
    · simp
    · intro w _ hw
      simp [hw]
  rw [sum_congr rfl fun z hz => by rw [hinner z hz], sum_eq_single_of_mem _ hzs]
  · exact D.tail_succ_mul t x y
  · intro z _ hz
    exact D.tail_succ_mul_eq_zero t x y z hz

/-- The multiplier `M_t` has modulus at most one. -/
theorem abs_mult_le (t : ℕ) (z : Fin k → ZMod p) : |D.mult t z| ≤ 1 := by
  unfold mult
  rw [abs_prod]
  refine prod_le_one₀ (fun e _ => abs_nonneg _) fun e _ => ?_
  split_ifs
  · exact chiR_sign_mul_abs_le _ _
  · simp

/-- The bound for the blocks `≥ t`, by downward induction on `t`. -/
theorem tail_opBound (hp2 : p ≠ 2) (h4 : FourCycleBound p) (d : ℕ) :
    ∀ t, (∀ i, D.blk i < t + d) →
      OpBound D.inj D.inj (D.tail t) (2 ^ D.levelTwo t * Real.sqrt p ^ D.levelCard t) := by
  induction d with
  | zero =>
    intro t h
    have hId := (Sarkozy.Extraction.opBound_diag (fun _ : Fin k → ZMod p => (1 : ℝ))
      (fun _ => by simp)).subset (subset_univ D.inj) (subset_univ D.inj)
    have hc : D.levelCard t = 0 := by
      unfold levelCard
      rw [card_eq_zero, filter_eq_empty_iff]
      intro i _
      have := h i
      omega
    have h2 : D.levelTwo t = 0 := by
      unfold levelTwo
      rw [card_eq_zero, filter_eq_empty_iff]
      intro b hb
      obtain ⟨i, _, rfl⟩ := mem_image.mp hb
      have := h i
      omega
    refine twoCycle_opBound_congr hId (fun x _ y _ => ?_) (by rw [hc, h2]; simp)
    have hiff : (∀ j, D.blk j < t → x j = y j) ↔ x = y :=
      ⟨fun h' => funext fun j => h' j (by have := h j; omega), fun h' j _ => by rw [h']⟩
    have hprod : ∏ e ∈ D.pairs,
        (if t ≤ D.blk e.1 then chiR (D.sign e.1 e.2 * (y e.2 - x e.1)) else 1) = 1 :=
      prod_eq_one fun e _ => ite_eq_right (by have := h e.1; omega)
    simp only [tail, hiff, hprod, mul_one]
  | succ d ih =>
    intro t h
    have ih' := ih (t + 1) (fun i => by have := h i; omega)
    have hM := (Sarkozy.Extraction.opBound_diag (D.mult t) (D.abs_mult_le t)).subset
      (subset_univ D.inj) (subset_univ D.inj)
    have hcomp := (ih'.comp hM).comp (D.step_opBound hp2 h4 t)
    refine twoCycle_opBound_congr hcomp (fun x hx y hy => D.tail_eq_sum t hx hy) ?_
    rw [D.levelTwo_succ t, D.levelCard_succ t, pow_add, pow_add]
    ring

/-- **`lem:matching:kernel`(b), sorted-block form, on the tuples injective on the two-vertex
blocks.** -/
theorem opBound_inj (hp2 : p ≠ 2) (h4 : FourCycleBound p) :
    OpBound D.inj D.inj (witnessKernel D.pairs D.sign) (2 ^ D.numTwo * Real.sqrt p ^ k) := by
  have h := D.tail_opBound hp2 h4 (univ.sup D.blk + 1) 0
    (fun i => by have := le_sup (f := D.blk) (mem_univ i); omega)
  have hc : D.levelCard 0 = k := by
    unfold levelCard
    rw [filter_true_of_mem (fun i _ => Nat.zero_le _), card_univ, Fintype.card_fin]
  have h2 : D.levelTwo 0 = D.numTwo := by
    unfold levelTwo numTwo
    congr 1
  refine twoCycle_opBound_congr h (fun x _ y _ => ?_) (by rw [hc, h2])
  simp [tail, witnessKernel]

end BlockWitness

/-- **`lem:matching:kernel`(b), sorted-block form.** Let the coordinates be grouped into blocks
of at most two vertices, listed in increasing order (`BlockWitness`): every pair of `𝒦` goes
from a block to the same or a later block, and every two-vertex block carries the complete
rectangle. Let `β` be the number of two-vertex blocks, and let `R`, `C` be sets of tuples `x`
with `x_i ≠ x_l` for every two-vertex block `{i, l}` (the supports of `P_out`, `P_in`). Given
the four-cycle bound (`cor:dl:normalized`(a), a hypothesis), the block `R × C` of the witness
kernel has `ℓ²` operator norm at most `2^β √p^k`; in the uniform normalization,
`‖P_out T_𝒦 P_in‖ ≤ 2^β r^k`. -/
theorem blockWitnessKernel_opBound (hp2 : p ≠ 2) (h4 : FourCycleBound p) {k : ℕ}
    (D : BlockWitness (p := p) k) {R C : Finset (Fin k → ZMod p)}
    (hR : ∀ x ∈ R, ∀ i l, i ≠ l → D.blk i = D.blk l → x i ≠ x l)
    (hC : ∀ y ∈ C, ∀ i l, i ≠ l → D.blk i = D.blk l → y i ≠ y l) :
    OpBound R C (witnessKernel D.pairs D.sign) (2 ^ D.numTwo * Real.sqrt p ^ k) :=
  (D.opBound_inj hp2 h4).subset (fun x hx => mem_filter.mpr ⟨mem_univ _, hR x hx⟩)
    (fun y hy => mem_filter.mpr ⟨mem_univ _, hC y hy⟩)

/-- **The complete rectangle** (`rem:extraction-kernels`), the case `k = 2`, `𝒦` all four pairs,
of the sorted-block form (one two-vertex block, `β = 1`): on the pairs with distinct coordinates
the kernel `∏_{a,b ≤ 2} χ(ς_{ab}(y_b - x_a))` has `ℓ²` norm at most `2 √p²`, i.e. `2r²` for
uniform probability, given the four-cycle bound (`cor:dl:normalized`(a), a hypothesis). -/
theorem witnessKernel_rectangle_opBound (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    {ς : Fin 2 → Fin 2 → ZMod p} (hς : ∀ a b, ς a b = 1 ∨ ς a b = -1) :
    OpBound (univ.filter (fun x : Fin 2 → ZMod p => x 0 ≠ x 1))
      (univ.filter (fun x : Fin 2 → ZMod p => x 0 ≠ x 1)) (witnessKernel univ ς)
      (2 * Real.sqrt p ^ 2) := by
  let D : BlockWitness (p := p) 2 :=
    { pairs := univ
      blk := fun _ => 0
      sign := ς
      sign_pm := hς
      card_le := fun b => (card_filter_le _ _).trans (by simp)
      forward := fun _ _ => le_rfl
      complete := fun _ _ _ => mem_univ _ }
  have hinj : ∀ x ∈ univ.filter (fun x : Fin 2 → ZMod p => x 0 ≠ x 1),
      ∀ i l, i ≠ l → D.blk i = D.blk l → x i ≠ x l := by
    intro x hx i l hil _
    have hx' := (mem_filter.mp hx).2
    fin_cases i <;> fin_cases l
    · exact absurd rfl hil
    · exact hx'
    · exact Ne.symm hx'
    · exact absurd rfl hil
  have h := blockWitnessKernel_opBound hp2 h4 D hinj hinj
  have hβ : D.numTwo = 1 := by
    simp only [BlockWitness.numTwo, D]
    rw [image_const univ_nonempty, filter_singleton]
    simp
  rw [hβ, pow_one] at h
  exact h

/-! ## Strongly connected components with at most two vertices -/

section Components

variable {k : ℕ}

/-- Mutual reachability in `D_𝒦`: `i` and `l` lie in the same strongly connected component. -/
def twoCycleMutual (𝒦 : Finset (Fin k × Fin k)) (i l : Fin k) : Prop :=
  Relation.ReflTransGen (WitnessArc 𝒦) i l ∧ Relation.ReflTransGen (WitnessArc 𝒦) l i

open Classical in
/-- The strongly connected component of `i` in `D_𝒦`. -/
noncomputable def twoCycleComponent (𝒦 : Finset (Fin k × Fin k)) (i : Fin k) : Finset (Fin k) :=
  univ.filter (fun l => twoCycleMutual 𝒦 i l)

/-- The number `β` of two-vertex strongly connected components of `D_𝒦`. -/
noncomputable def twoCycleCount (𝒦 : Finset (Fin k × Fin k)) : ℕ :=
  ((univ.image (twoCycleComponent 𝒦)).filter (fun C => C.card = 2)).card

variable {𝒦 : Finset (Fin k × Fin k)}

theorem twoCycleMutual_refl (i : Fin k) : twoCycleMutual 𝒦 i i :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem twoCycleMutual.symm {i l : Fin k} (h : twoCycleMutual 𝒦 i l) : twoCycleMutual 𝒦 l i :=
  ⟨h.2, h.1⟩

theorem twoCycleMutual.trans {i l m : Fin k} (h : twoCycleMutual 𝒦 i l)
    (h' : twoCycleMutual 𝒦 l m) : twoCycleMutual 𝒦 i m :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

theorem mem_twoCycleComponent {i l : Fin k} :
    l ∈ twoCycleComponent 𝒦 i ↔ twoCycleMutual 𝒦 i l := by
  simp [twoCycleComponent]

theorem twoCycleComponent_eq {i l : Fin k} (h : twoCycleMutual 𝒦 i l) :
    twoCycleComponent 𝒦 i = twoCycleComponent 𝒦 l := by
  ext m
  rw [mem_twoCycleComponent, mem_twoCycleComponent]
  exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

open Classical in
/-- The number of vertices from which `i` is reachable. -/
noncomputable def twoCycleAnc (𝒦 : Finset (Fin k × Fin k)) (i : Fin k) : ℕ :=
  (univ.filter (fun a => Relation.ReflTransGen (WitnessArc 𝒦) a i)).card

/-- The least vertex of the component of `i`. -/
noncomputable def twoCycleRep (𝒦 : Finset (Fin k × Fin k)) (i : Fin k) : Fin k :=
  (twoCycleComponent 𝒦 i).min' ⟨i, mem_twoCycleComponent.mpr (twoCycleMutual_refl i)⟩

/-- A block assignment along the condensation of `D_𝒦`: the components, ordered by the number
of vertices from which they are reachable, ties broken by the least vertex. -/
noncomputable def twoCycleBlk (𝒦 : Finset (Fin k × Fin k)) (i : Fin k) : ℕ :=
  twoCycleAnc 𝒦 i * (k + 1) + (twoCycleRep 𝒦 i : ℕ)

theorem twoCycleAnc_eq {i l : Fin k} (h : twoCycleMutual 𝒦 i l) :
    twoCycleAnc 𝒦 i = twoCycleAnc 𝒦 l := by
  unfold twoCycleAnc
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩

theorem twoCycleRep_eq {i l : Fin k} (h : twoCycleMutual 𝒦 i l) :
    twoCycleRep 𝒦 i = twoCycleRep 𝒦 l := by
  unfold twoCycleRep
  congr 1
  exact twoCycleComponent_eq h

theorem twoCycleMutual_of_rep_eq {i l : Fin k} (h : twoCycleRep 𝒦 i = twoCycleRep 𝒦 l) :
    twoCycleMutual 𝒦 i l := by
  have hi := mem_twoCycleComponent.mp (min'_mem (twoCycleComponent 𝒦 i)
    ⟨i, mem_twoCycleComponent.mpr (twoCycleMutual_refl i)⟩)
  have hl := mem_twoCycleComponent.mp (min'_mem (twoCycleComponent 𝒦 l)
    ⟨l, mem_twoCycleComponent.mpr (twoCycleMutual_refl l)⟩)
  have h' : twoCycleMutual 𝒦 i (twoCycleRep 𝒦 l) := by
    rw [← h]
    exact hi
  exact h'.trans hl.symm

theorem twoCycleAnc_lt {i l : Fin k} (h : WitnessArc 𝒦 i l) (hn : ¬ twoCycleMutual 𝒦 i l) :
    twoCycleAnc 𝒦 i < twoCycleAnc 𝒦 l := by
  classical
  have hnot : ¬ Relation.ReflTransGen (WitnessArc 𝒦) l i := fun h' =>
    hn ⟨Relation.ReflTransGen.single h, h'⟩
  unfold twoCycleAnc
  refine card_lt_card ?_
  rw [ssubset_iff_of_subset]
  · refine ⟨l, ?_, by simpa using hnot⟩
    rw [mem_filter]
    exact ⟨mem_univ _, Relation.ReflTransGen.refl⟩
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact ha.tail h

theorem twoCycleRep_lt (i : Fin k) : (twoCycleRep 𝒦 i : ℕ) < k + 1 := by
  have := (twoCycleRep 𝒦 i).isLt
  omega

theorem twoCycleBlk_eq_iff {i l : Fin k} :
    twoCycleBlk 𝒦 i = twoCycleBlk 𝒦 l ↔ twoCycleMutual 𝒦 i l := by
  constructor
  · intro h
    unfold twoCycleBlk at h
    have hi := twoCycleRep_lt (𝒦 := 𝒦) i
    have hl := twoCycleRep_lt (𝒦 := 𝒦) l
    rcases lt_trichotomy (twoCycleAnc 𝒦 i) (twoCycleAnc 𝒦 l) with h' | h' | h'
    · have := Nat.mul_le_mul_right (k + 1) (Nat.succ_le_of_lt h')
      rw [Nat.succ_mul] at this
      omega
    · rw [h'] at h
      exact twoCycleMutual_of_rep_eq (Fin.ext (by omega))
    · have := Nat.mul_le_mul_right (k + 1) (Nat.succ_le_of_lt h')
      rw [Nat.succ_mul] at this
      omega
  · intro h
    unfold twoCycleBlk
    rw [twoCycleAnc_eq h, twoCycleRep_eq h]

theorem twoCycleBlk_le {i l : Fin k} (h : (i, l) ∈ 𝒦) : twoCycleBlk 𝒦 i ≤ twoCycleBlk 𝒦 l := by
  by_cases hil : i = l
  · rw [hil]
  by_cases hm : twoCycleMutual 𝒦 i l
  · exact (twoCycleBlk_eq_iff.mpr hm).le
  have hlt := twoCycleAnc_lt ⟨h, hil⟩ hm
  have := Nat.mul_le_mul_right (k + 1) (Nat.succ_le_of_lt hlt)
  rw [Nat.succ_mul] at this
  have hi := twoCycleRep_lt (𝒦 := 𝒦) i
  unfold twoCycleBlk
  omega

theorem twoCycle_fiber_eq (i : Fin k) :
    univ.filter (fun l => twoCycleBlk 𝒦 l = twoCycleBlk 𝒦 i) = twoCycleComponent 𝒦 i := by
  ext l
  rw [mem_filter, mem_twoCycleComponent, twoCycleBlk_eq_iff]
  exact ⟨fun h => h.2.symm, fun h => ⟨mem_univ _, h.symm⟩⟩

/-- Strong connectivity gives both arcs: in a component with at most two vertices, two distinct
mutually reachable vertices are joined by an arc. -/
theorem twoCycle_mem_of_mutual (hcard : ∀ i, (twoCycleComponent 𝒦 i).card ≤ 2) {i l : Fin k}
    (hil : i ≠ l) (h : twoCycleMutual 𝒦 i l) : (i, l) ∈ 𝒦 := by
  rcases Relation.ReflTransGen.cases_head h.1 with h' | ⟨m, him, hml⟩
  · exact absurd h' hil
  have hmi : twoCycleMutual 𝒦 i m := ⟨Relation.ReflTransGen.single him, hml.trans h.2⟩
  by_cases hml' : m = l
  · rw [← hml']
    exact him.1
  exfalso
  have hsub : ({i, l, m} : Finset (Fin k)) ⊆ twoCycleComponent 𝒦 i := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_twoCycleComponent]
    rcases hx with rfl | rfl | rfl
    · exact twoCycleMutual_refl _
    · exact h
    · exact hmi
  have h3 : ({i, l, m} : Finset (Fin k)).card = 3 :=
    card_eq_three.mpr ⟨i, l, m, hil, him.2, Ne.symm hml', rfl⟩
  have := card_le_card hsub
  have := hcard i
  omega

/-- The sorted-block data of `𝒦` along the condensation of `D_𝒦`. -/
noncomputable def twoCycleBlockWitness (𝒦 : Finset (Fin k × Fin k))
    (ς : Fin k → Fin k → ZMod p) (h𝒦 : ∀ i, (i, i) ∈ 𝒦)
    (hcard : ∀ i, (twoCycleComponent 𝒦 i).card ≤ 2) : BlockWitness (p := p) k where
  pairs := 𝒦
  blk := twoCycleBlk 𝒦
  sign i l := if (i, l) ∈ 𝒦 ∧ (ς i l = 1 ∨ ς i l = -1) then ς i l else 1
  sign_pm i l := by
    by_cases h : (i, l) ∈ 𝒦 ∧ (ς i l = 1 ∨ ς i l = -1)
    · rw [ite_eq_left h]
      exact h.2
    · rw [ite_eq_right h]
      exact Or.inl rfl
  card_le b := by
    by_cases hb : ∃ i, twoCycleBlk 𝒦 i = b
    · obtain ⟨i, rfl⟩ := hb
      rw [twoCycle_fiber_eq]
      exact hcard i
    · have hempty : univ.filter (fun l => twoCycleBlk 𝒦 l = b) = ∅ := by
        rw [filter_eq_empty_iff]
        exact fun l _ hl => hb ⟨l, hl⟩
      rw [hempty, card_empty]
      omega
  forward e he := twoCycleBlk_le he
  complete i l h := by
    by_cases hil : i = l
    · rw [hil]
      exact h𝒦 l
    · exact twoCycle_mem_of_mutual hcard hil (twoCycleBlk_eq_iff.mp h)

theorem twoCycleBlockWitness_numTwo (ς : Fin k → Fin k → ZMod p) (h𝒦 : ∀ i, (i, i) ∈ 𝒦)
    (hcard : ∀ i, (twoCycleComponent 𝒦 i).card ≤ 2) :
    (twoCycleBlockWitness (p := p) 𝒦 ς h𝒦 hcard).numTwo = twoCycleCount 𝒦 := by
  have hcomp : twoCycleComponent 𝒦 =
      (fun b => univ.filter (fun l => twoCycleBlk 𝒦 l = b)) ∘ twoCycleBlk 𝒦 := by
    funext i
    exact (twoCycle_fiber_eq i).symm
  have e1 : univ.image (twoCycleComponent 𝒦) = (univ.image (twoCycleBlk 𝒦)).image
      (fun b => univ.filter (fun l => twoCycleBlk 𝒦 l = b)) := by
    rw [hcomp, image_image]
  unfold twoCycleCount
  rw [e1, filter_image, card_image_of_injOn]
  · rfl
  · intro b hb b' _ hbb'
    rw [mem_coe, mem_filter] at hb
    obtain ⟨i, _, rfl⟩ := mem_image.mp hb.1
    have hi : i ∈ univ.filter (fun l => twoCycleBlk 𝒦 l = b') := by
      have : i ∈ univ.filter (fun l => twoCycleBlk 𝒦 l = twoCycleBlk 𝒦 i) :=
        mem_filter.mpr ⟨mem_univ _, rfl⟩
      simpa only [hbb'] using this
    exact (mem_filter.mp hi).2

/-- **`lem:matching:kernel`(b).** Let `𝒦 ⊆ {1, …, k}²` contain the diagonal, let `ς = ±1` on
`𝒦`, and suppose that every strongly connected component of `D_𝒦` has at most two vertices
(`twoCycleComponent`, mutual reachability), `β` of them two (`twoCycleCount`). Let `R`, `C` be
sets of tuples `x` with `x_i ≠ x_l` whenever `i ≠ l` lie in the same component (the supports of
`P_out`, `P_in`; for instance the injective tuples). Given the four-cycle bound
(`cor:dl:normalized`(a), a hypothesis), the block `R × C` of the witness kernel has `ℓ²` operator
norm at most `2^β √p^k`; in the uniform normalization, `‖P_out T_𝒦 P_in‖ ≤ 2^β r^k`.

The proof orders the components along the condensation of `D_𝒦` (`twoCycleBlockWitness`) and
applies the sorted-block form `blockWitnessKernel_opBound`. -/
theorem witnessKernel_opBound_twoCycles (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    {ς : Fin k → Fin k → ZMod p} (h𝒦 : ∀ i, (i, i) ∈ 𝒦)
    (hς : ∀ e ∈ 𝒦, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1)
    (hcard : ∀ i, (twoCycleComponent 𝒦 i).card ≤ 2) {R C : Finset (Fin k → ZMod p)}
    (hR : ∀ x ∈ R, ∀ i l, i ≠ l → twoCycleMutual 𝒦 i l → x i ≠ x l)
    (hC : ∀ y ∈ C, ∀ i l, i ≠ l → twoCycleMutual 𝒦 i l → y i ≠ y l) :
    OpBound R C (witnessKernel 𝒦 ς) (2 ^ twoCycleCount 𝒦 * Real.sqrt p ^ k) := by
  have h := blockWitnessKernel_opBound hp2 h4 (twoCycleBlockWitness (p := p) 𝒦 ς h𝒦 hcard)
    (R := R) (C := C) (fun x hx i l hil hb => hR x hx i l hil (twoCycleBlk_eq_iff.mp hb))
    (fun y hy i l hil hb => hC y hy i l hil (twoCycleBlk_eq_iff.mp hb))
  rw [twoCycleBlockWitness_numTwo] at h
  have hker : witnessKernel (twoCycleBlockWitness (p := p) 𝒦 ς h𝒦 hcard).pairs
      (twoCycleBlockWitness (p := p) 𝒦 ς h𝒦 hcard).sign = witnessKernel 𝒦 ς :=
    witnessKernel_congr_sign fun e he => by
      show (if (e.1, e.2) ∈ 𝒦 ∧ (ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1) then ς e.1 e.2 else 1) = _
      rw [ite_eq_left ⟨he, hς e he⟩]
  rw [hker] at h
  exact h

/-- **`lem:matching:kernel`(b) for the injective tuples**: `P_in = P_out` the multiplication by
the indicator of the injective tuples. Given the four-cycle bound (`cor:dl:normalized`(a), a
hypothesis), `‖P_out T_𝒦 P_in‖_{ℓ²} ≤ 2^β √p^k`, i.e. `≤ 2^β r^k` for uniform probability. -/
theorem witnessKernel_opBound_twoCycles_injective (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    {ς : Fin k → Fin k → ZMod p} (h𝒦 : ∀ i, (i, i) ∈ 𝒦)
    (hς : ∀ e ∈ 𝒦, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1)
    (hcard : ∀ i, (twoCycleComponent 𝒦 i).card ≤ 2) :
    OpBound (univ.filter (fun x : Fin k → ZMod p => Function.Injective x))
      (univ.filter (fun x : Fin k → ZMod p => Function.Injective x))
      (witnessKernel 𝒦 ς) (2 ^ twoCycleCount 𝒦 * Real.sqrt p ^ k) :=
  witnessKernel_opBound_twoCycles hp2 h4 h𝒦 hς hcard
    (fun _ hx _ _ hil _ h => hil ((mem_filter.mp hx).2 h))
    (fun _ hy _ _ hil _ h => hil ((mem_filter.mp hy).2 h))

end Components

end Sarkozy.Extraction
