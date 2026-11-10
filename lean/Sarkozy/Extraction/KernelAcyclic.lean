module

public import Sarkozy.Extraction.WitnessKernel

@[expose] public section

/-!
# Witness kernels on general acyclic digraphs (`lem:matching:kernel`(a), (c))

`paper/sections/16_extraction.tex`, `lem:matching:kernel`. Let `𝒦 ⊆ {1, …, k}²` contain the
diagonal pairs and let `ς_{il} = ±1`. The operator `T_𝒦` has the kernel
`∏_{(i,l) ∈ 𝒦} χ(ς_{il}(y_l - x_i))` (`witnessKernel`). The digraph `D_𝒦` has an arc `i → l`
for every `(i, l) ∈ 𝒦` with `i ≠ l` (`WitnessArc`); it is acyclic when no vertex reaches itself
along a nonempty chain of arcs (`IsAcyclicWitness`).

* Part (a), `witnessKernel_opBound`: if `D_𝒦` is acyclic, the kernel matrix has `ℓ²` (counting
  measure) operator norm at most `√p^k`. This is `‖T_𝒦‖ ≤ r^k`, `r = p^{-1/2}`, in the paper's
  uniform-probability normalization. The proof relabels the coordinates along a topological
  order of `D_𝒦` (`exists_equiv_lt_of_acyclic`, a linear extension built from the numbers of
  ancestors). After the relabelling the kernel is the sorted kernel of `WitnessKernel.lean`
  (`sortedOfTopological_kernel`: the product over `𝒦` splits into the diagonal and the arcs),
  and `sortedWitnessKernel_opBound` applies; relabelling rows and columns does not change
  operator norms.
* Part (c), `isAcyclicWitness_iff`: `D_𝒦` is acyclic iff the identity is the only permutation
  `π` with `(i, π i) ∈ 𝒦` for all `i`, i.e. iff the diagonal is the only perfect matching in `𝒦`.
  A permutation `π ≠ 1` inside `𝒦` gives the closed walk `i → π i → π² i → ⋯ → i` along a
  non-trivial cycle of `π`. Conversely, from a directed cycle one picks for every vertex on a
  cycle a successor that is again on a cycle; this map permutes its periodic points, which gives
  a permutation inside `𝒦` moving a vertex.

Parts (b) (strongly connected components with two vertices; it needs `cor:dl:normalized`) and
(d) (inserted multipliers) are not in this file.

The paper has signs `ς_{il}` only for `(i, l) ∈ 𝒦`; here `ς` is a function on all pairs, and
its values outside `𝒦` do not enter the kernel (`witnessKernel_congr_sign`).
`witnessKernel_opBound` assumes `ς = ±1` on all pairs; `witnessKernel_opBound_of_mem` assumes it
only on `𝒦`, as in the paper. Both hold for every `k`, including `k = 0`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy.Influence

/-! ## The digraph `D_𝒦` -/

section Digraph

variable {k : ℕ}

/-- The arcs of `D_𝒦`: `i → l` for `(i, l) ∈ 𝒦` with `i ≠ l`. -/
def WitnessArc (𝒦 : Finset (Fin k × Fin k)) (i l : Fin k) : Prop := (i, l) ∈ 𝒦 ∧ i ≠ l

instance (𝒦 : Finset (Fin k × Fin k)) : DecidableRel (WitnessArc 𝒦) := fun i l =>
  inferInstanceAs (Decidable ((i, l) ∈ 𝒦 ∧ i ≠ l))

/-- `D_𝒦` has no directed cycle: no vertex reaches itself along a nonempty chain of arcs. -/
def IsAcyclicWitness (𝒦 : Finset (Fin k × Fin k)) : Prop :=
  ∀ i, ¬ Relation.TransGen (WitnessArc 𝒦) i i

/-- A topological relabelling: a relation on `Fin k` without cycles has a linear extension,
i.e. an equivalence `σ` of `Fin k` with `σ i < σ l` whenever `r i l`. -/
theorem exists_equiv_lt_of_acyclic {r : Fin k → Fin k → Prop}
    (hr : ∀ i, ¬ Relation.TransGen r i i) :
    ∃ σ : Fin k ≃ Fin k, ∀ i l, r i l → σ i < σ l := by
  classical
  -- the number of strict ancestors increases along arcs
  let anc : Fin k → ℕ := fun j => (univ.filter (fun a => Relation.TransGen r a j)).card
  have hanc : ∀ i l, r i l → anc i < anc l := by
    intro i l hil
    refine card_lt_card ?_
    rw [ssubset_iff_of_subset]
    · refine ⟨i, ?_, ?_⟩
      · simpa using Relation.TransGen.single hil
      · simpa using hr i
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact ha.tail hil
  -- an injective key that increases along arcs
  let key : Fin k → ℕ := fun j => k * anc j + j
  have hkey : ∀ i l, anc i < anc l → key i < key l := by
    intro i l h
    have h1 : k * (anc i + 1) ≤ k * anc l := Nat.mul_le_mul_left k h
    have h2 : (i : ℕ) < k := i.isLt
    rw [mul_add, mul_one] at h1
    show k * anc i + i < k * anc l + l
    omega
  have hkey_inj : Function.Injective key := by
    intro i l h
    rcases lt_trichotomy (anc i) (anc l) with h' | h' | h'
    · exact absurd h (hkey i l h').ne
    · have h'' : k * anc i + (i : ℕ) = k * anc l + (l : ℕ) := h
      rw [h'] at h''
      exact Fin.ext (by omega)
    · exact absurd h (hkey l i h').ne'
  -- the rank of the key
  let rk : Fin k → ℕ := fun j => (univ.filter (fun a => key a < key j)).card
  have hrk : ∀ i l, key i < key l → rk i < rk l := by
    intro i l h
    refine card_lt_card ?_
    rw [ssubset_iff_of_subset]
    · exact ⟨i, by simpa using h, by simp⟩
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact ha.trans h
  have hrk_lt : ∀ j, rk j < k := by
    intro j
    calc rk j < (univ : Finset (Fin k)).card := by
          refine card_lt_card ?_
          rw [ssubset_iff_of_subset (subset_univ _)]
          exact ⟨j, mem_univ _, by simp⟩
      _ = k := by simp
  let σ' : Fin k → Fin k := fun j => ⟨rk j, hrk_lt j⟩
  have hσ' : ∀ i l, key i < key l → σ' i < σ' l := fun i l h => by
    show rk i < rk l
    exact hrk i l h
  have hσ'_inj : Function.Injective σ' := by
    intro i l h
    by_contra hne
    rcases lt_or_gt_of_ne (hkey_inj.ne hne) with h' | h'
    · exact (hσ' i l h').ne h
    · exact (hσ' l i h').ne' h
  exact ⟨Equiv.ofBijective σ' (Finite.injective_iff_bijective.mp hσ'_inj),
    fun i l hil => hσ' i l (hkey i l (hanc i l hil))⟩

/-- **`lem:matching:kernel`(c)**: if `𝒦` contains the diagonal, `D_𝒦` is acyclic iff the
identity is the only permutation `π` with `(i, π i) ∈ 𝒦` for all `i` (the diagonal is the only
perfect matching contained in `𝒦`). -/
theorem isAcyclicWitness_iff {𝒦 : Finset (Fin k × Fin k)} (h𝒦 : ∀ i, (i, i) ∈ 𝒦) :
    IsAcyclicWitness 𝒦 ↔ ∀ π : Equiv.Perm (Fin k), (∀ i, (i, π i) ∈ 𝒦) → π = 1 := by
  constructor
  · -- a permutation `π ≠ 1` inside `𝒦` gives a closed walk along a cycle of `π`
    intro hac π hπ
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, π i ≠ i := by
      by_contra h
      exact hne (Equiv.ext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
    have harc : ∀ m : ℕ, WitnessArc 𝒦 ((π ^ m) i) ((π ^ (m + 1)) i) := by
      intro m
      have e1 : (π ^ (m + 1)) i = π ((π ^ m) i) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      have e2 : (π ^ (m + 1)) i = (π ^ m) (π i) := by
        rw [pow_succ, Equiv.Perm.mul_apply]
      refine ⟨by rw [e1]; exact hπ _, fun h => hi ?_⟩
      rw [e2] at h
      exact ((π ^ m).injective h).symm
    have hpath : ∀ m : ℕ, Relation.TransGen (WitnessArc 𝒦) i ((π ^ (m + 1)) i) := by
      intro m
      induction m with
      | zero =>
        have h0 := harc 0
        rw [pow_zero, Equiv.Perm.one_apply] at h0
        exact Relation.TransGen.single h0
      | succ m ih => exact ih.tail (harc (m + 1))
    have hcyc := hpath (orderOf π - 1)
    rw [Nat.sub_add_cancel (orderOf_pos π), pow_orderOf_eq_one, Equiv.Perm.one_apply] at hcyc
    exact hac i hcyc
  · -- a directed cycle gives a permutation inside `𝒦` that moves a vertex
    intro hperm i₀ hi₀
    classical
    have hsucc : ∀ j, Relation.TransGen (WitnessArc 𝒦) j j →
        ∃ j', WitnessArc 𝒦 j j' ∧ Relation.TransGen (WitnessArc 𝒦) j' j' := by
      intro j hj
      obtain ⟨j', hjj', hj'j⟩ := Relation.TransGen.head'_iff.mp hj
      exact ⟨j', hjj', Relation.TransGen.tail' hj'j hjj'⟩
    -- a successor map: on the vertices of cycles it follows an arc to a vertex of a cycle
    let s : Fin k → Fin k := fun j =>
      if hj : Relation.TransGen (WitnessArc 𝒦) j j then Classical.choose (hsucc j hj) else j
    have hs_arc : ∀ j, Relation.TransGen (WitnessArc 𝒦) j j → WitnessArc 𝒦 j (s j) := by
      intro j hj
      simp only [s, hj, ↓reduceDIte]
      exact (Classical.choose_spec (hsucc j hj)).1
    have hs_cyc : ∀ j, Relation.TransGen (WitnessArc 𝒦) j j →
        Relation.TransGen (WitnessArc 𝒦) (s j) (s j) := by
      intro j hj
      simp only [s, hj, ↓reduceDIte]
      exact (Classical.choose_spec (hsucc j hj)).2
    have hs_fix : ∀ j, ¬ Relation.TransGen (WitnessArc 𝒦) j j → s j = j := by
      intro j hj
      simp only [s, hj, ↓reduceDIte]
    have hiter : ∀ n : ℕ, Relation.TransGen (WitnessArc 𝒦) (s^[n] i₀) (s^[n] i₀) := by
      intro n
      induction n with
      | zero => exact hi₀
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hs_cyc _ ih
    -- some iterate of `i₀` is a periodic point of `s`
    obtain ⟨a, b, hab, heq⟩ : ∃ a b : ℕ, a < b ∧ s^[a] i₀ = s^[b] i₀ := by
      obtain ⟨a, b, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => s^[n] i₀)
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨a, b, h, heq⟩
      · exact ⟨b, a, h, heq.symm⟩
    have hper : Function.IsPeriodicPt s (b - a) (s^[a] i₀) := by
      show s^[b - a] (s^[a] i₀) = s^[a] i₀
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le, ← heq]
    have hmem : s^[a] i₀ ∈ Function.periodicPts s :=
      Function.mk_mem_periodicPts (Nat.sub_pos_of_lt hab) hper
    -- `s` permutes its periodic points
    let π : Equiv.Perm (Fin k) :=
      Equiv.Perm.ofSubtype ((Function.bijOn_periodicPts s).equiv s)
    have hπ_mem : ∀ j, j ∈ Function.periodicPts s → π j = s j := by
      intro j hj
      rw [Equiv.Perm.ofSubtype_apply_of_mem _ hj]
      rfl
    have hπ_not : ∀ j, j ∉ Function.periodicPts s → π j = j := fun j hj =>
      Equiv.Perm.ofSubtype_apply_of_not_mem _ hj
    have h1 : π = 1 := by
      refine hperm π fun j => ?_
      by_cases hj : j ∈ Function.periodicPts s
      · rw [hπ_mem j hj]
        by_cases hc : Relation.TransGen (WitnessArc 𝒦) j j
        · exact (hs_arc j hc).1
        · rw [hs_fix j hc]
          exact h𝒦 j
      · rw [hπ_not j hj]
        exact h𝒦 j
    have h2 : π (s^[a] i₀) ≠ s^[a] i₀ := by
      rw [hπ_mem _ hmem]
      exact (hs_arc _ (hiter a)).2.symm
    exact h2 (by rw [h1]; rfl)

end Digraph

/-! ## The kernel `T_𝒦` -/

section Kernel

variable {p : ℕ} [Fact p.Prime] {k : ℕ}

/-- The kernel of `T_𝒦`: `∏_{(i,l) ∈ 𝒦} χ(ς_{il}(y_l - x_i))`. -/
noncomputable def witnessKernel (𝒦 : Finset (Fin k × Fin k)) (ς : Fin k → Fin k → ZMod p)
    (x y : Fin k → ZMod p) : ℝ :=
  ∏ e ∈ 𝒦, chiR (ς e.1 e.2 * (y e.2 - x e.1))

/-- The product over `𝒦`, grouped by the second index: the diagonal factor and the arcs into
`l`. -/
theorem witnessKernel_eq_prod_arcs {𝒦 : Finset (Fin k × Fin k)} (h𝒦 : ∀ i, (i, i) ∈ 𝒦)
    (ς : Fin k → Fin k → ZMod p) (x y : Fin k → ZMod p) :
    witnessKernel 𝒦 ς x y = ∏ l, (chiR (ς l l * (y l - x l)) *
      ∏ i ∈ univ.filter (fun i => WitnessArc 𝒦 i l), chiR (ς i l * (y l - x i))) := by
  unfold witnessKernel
  rw [prod_finset_product_right 𝒦 univ (fun l => univ.filter (fun i => (i, l) ∈ 𝒦))
    (fun e => by simp)]
  refine prod_congr rfl fun l _ => ?_
  have hsplit : univ.filter (fun i => (i, l) ∈ 𝒦) =
      insert l (univ.filter (fun i => WitnessArc 𝒦 i l)) := by
    ext i
    rw [mem_insert, mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    constructor
    · intro hi
      by_cases h : i = l
      · exact Or.inl h
      · exact Or.inr ⟨hi, h⟩
    · rintro (rfl | ⟨hi, _⟩)
      · exact h𝒦 i
      · exact hi
  have hnot : l ∉ univ.filter (fun i => WitnessArc 𝒦 i l) := by
    rw [mem_filter]
    exact fun h => h.2.2 rfl
  rw [hsplit, prod_insert hnot]

/-- The sorted witness of `𝒦` along a topological relabelling `σ` of `D_𝒦`: the parents of
`l` are the images of the tails of the arcs into `σ⁻¹ l`. -/
def sortedOfTopological {𝒦 : Finset (Fin k × Fin k)} (ς : Fin k → Fin k → ZMod p)
    (hς : ∀ i l, ς i l = 1 ∨ ς i l = -1) (σ : Fin k ≃ Fin k)
    (hσ : ∀ i l, WitnessArc 𝒦 i l → σ i < σ l) : SortedWitness (p := p) k where
  parents l := (univ.filter (fun j => WitnessArc 𝒦 j (σ.symm l))).map σ.toEmbedding
  lt l i hi := by
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
    rw [mem_filter] at hj
    simpa using hσ _ _ hj.2
  sign i l := ς (σ.symm i) (σ.symm l)
  sign_pm _ _ := hς _ _

/-- After the relabelling `σ`, the witness kernel is the sorted witness kernel. -/
theorem sortedOfTopological_kernel {𝒦 : Finset (Fin k × Fin k)} (h𝒦 : ∀ i, (i, i) ∈ 𝒦)
    (ς : Fin k → Fin k → ZMod p) (hς : ∀ i l, ς i l = 1 ∨ ς i l = -1) (σ : Fin k ≃ Fin k)
    (hσ : ∀ i l, WitnessArc 𝒦 i l → σ i < σ l) (x y : Fin k → ZMod p) :
    sortedWitnessKernel (sortedOfTopological ς hς σ hσ) (x ∘ σ.symm) (y ∘ σ.symm) =
      witnessKernel 𝒦 ς x y := by
  rw [witnessKernel_eq_prod_arcs h𝒦]
  unfold sortedWitnessKernel
  simp only [sortedOfTopological, prod_map, Function.comp_apply, Equiv.coe_toEmbedding,
    Equiv.symm_apply_apply]
  exact Equiv.prod_comp σ.symm (fun m => chiR (ς m m * (y m - x m)) *
    ∏ i ∈ univ.filter (fun i => WitnessArc 𝒦 i m), chiR (ς i m * (y m - x i)))

/-- **`lem:matching:kernel`(a)**: if `𝒦` contains the diagonal, the signs are `±1` and `D_𝒦`
is acyclic, the witness kernel has `ℓ²` operator norm at most `√p^k`; in the uniform
normalization, `‖T_𝒦‖ ≤ r^k`. -/
theorem witnessKernel_opBound (hp2 : p ≠ 2) {𝒦 : Finset (Fin k × Fin k)}
    {ς : Fin k → Fin k → ZMod p} (h𝒦 : ∀ i, (i, i) ∈ 𝒦) (hς : ∀ i l, ς i l = 1 ∨ ς i l = -1)
    (hac : IsAcyclicWitness 𝒦) :
    OpBound univ univ (witnessKernel 𝒦 ς) (Real.sqrt p ^ k) := by
  obtain ⟨σ, hσ⟩ := exists_equiv_lt_of_acyclic (r := WitnessArc 𝒦) hac
  have hD := sortedWitnessKernel_opBound hp2 (sortedOfTopological ς hς σ hσ)
  let e : (Fin k → ZMod p) ≃ (Fin k → ZMod p) :=
    { toFun := fun x => x ∘ σ.symm
      invFun := fun x => x ∘ σ
      left_inv := fun x => by funext i; simp
      right_inv := fun x => by funext i; simp }
  exact Sarkozy.Extraction.OpBound.congr'
    (Sarkozy.Extraction.OpBound.equiv (U := Fin k → ZMod p) (V := Fin k → ZMod p)
      (U' := Fin k → ZMod p) (V' := Fin k → ZMod p) hD e e)
    (fun x y => sortedOfTopological_kernel h𝒦 ς hς σ hσ x y) rfl

/-- The witness kernel depends only on the signs at the pairs of `𝒦`. -/
theorem witnessKernel_congr_sign {𝒦 : Finset (Fin k × Fin k)} {ς ς' : Fin k → Fin k → ZMod p}
    (h : ∀ e ∈ 𝒦, ς e.1 e.2 = ς' e.1 e.2) : witnessKernel 𝒦 ς = witnessKernel 𝒦 ς' := by
  funext x y
  exact prod_congr rfl fun e he => by rw [h e he]

/-- **`lem:matching:kernel`(a)** with the signs `±1` required only on `𝒦`, as in the paper. -/
theorem witnessKernel_opBound_of_mem (hp2 : p ≠ 2) {𝒦 : Finset (Fin k × Fin k)}
    {ς : Fin k → Fin k → ZMod p} (h𝒦 : ∀ i, (i, i) ∈ 𝒦)
    (hς : ∀ e ∈ 𝒦, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1) (hac : IsAcyclicWitness 𝒦) :
    OpBound univ univ (witnessKernel 𝒦 ς) (Real.sqrt p ^ k) := by
  let ς' : Fin k → Fin k → ZMod p := fun i l => if (i, l) ∈ 𝒦 then ς i l else 1
  have h' : witnessKernel 𝒦 ς' = witnessKernel 𝒦 ς :=
    witnessKernel_congr_sign fun e he => by simp [ς', he]
  rw [← h']
  refine witnessKernel_opBound hp2 h𝒦 (fun i l => ?_) hac
  by_cases hil : (i, l) ∈ 𝒦
  · simpa [ς', hil] using hς (i, l) hil
  · simp [ς', hil]

end Kernel

end Sarkozy.Extraction
