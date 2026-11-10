module

public import Sarkozy.TraceMixing.Pair

/-!
# Counting admissible pairs (`lem:trace-mixing`(c), the counts)

`paper/sections/12_labellings.tex`, proof of `lem:trace-mixing`(c), "Counts", over any finite
field `F`. Fix a labelling `z` whose restriction to `W' = W ∖ {u, v}` (`restSet`) is feasible,
for an edge `(u, v)`. `pairAdm G z u v` is the set `Φ` of admissible pairs `(x, x')` (the
labelling `z` with `z_u = x`, `z_v = x'` lies in `Inj(G)`), and `diffCount G z u v y` is
`c_y = #{x : (x, x + y) ∈ Φ}`.

* `card_pairAdm_eq_sum`: `|Φ| = ∑_{y ∈ Q} c_y`.
* `diffCount_le_u`, `diffCount_le_v`: `c_y` is at most the number of admissible labels of one
  endpoint given `z|_{W'}`.
* `card_pairAdm_ge`: `|Φ| ≥ ∑_{x ∈ Φ_u} |Φ_v(x)|`, labelling `u` first and then `v`.
* `diffCount_eq_admissible`: for `χ(y) = 1` and generic `y` (`B_u ∩ (B_v - y) = ∅`), the set of
  such `x` is a set `Φ` of `lem:extension`, with the `t = d'_u + d'_v` roots `B_u ∪ (B_v - y)`
  and the excluded set `𝓛 ∪ (𝓛 - y)`; `diffCount_bounds` applies `extension_bounds`.
* `card_nongeneric_le`: at most `d'_u d'_v` values of `y` are not generic.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W]

section Feasibility

omit [Fintype W] [DecidableEq W] in
theorem feasible_congr' (G : OrientedGraph W) {A : Finset W} {x x' : W → F}
    (h : ∀ a ∈ A, x a = x' a) (hx : Feasible F G A x) : Feasible F G A x' := by
  refine ⟨fun a ha b hb hab => hx.1 a ha b hb (by rw [h a ha, h b hb]; exact hab),
    fun e he h1 h2 => ?_⟩
  rw [← h _ h1, ← h _ h2]
  exact hx.2 e he h1 h2

omit [Fintype W] [DecidableEq W] in
theorem feasible_mono (G : OrientedGraph W) {A B : Finset W} {x : W → F} (hAB : A ⊆ B)
    (hx : Feasible F G B x) : Feasible F G A x :=
  ⟨fun a ha b hb hab => hx.1 a (hAB ha) b (hAB hb) hab,
    fun e he h1 h2 => hx.2 e he (hAB h1) (hAB h2)⟩

theorem vertexAdmissible_congr (G : OrientedGraph W) {A : Finset W} {x x' : W → F}
    (h : ∀ a ∈ A, x a = x' a) (v : W) :
    vertexAdmissible G A x v = vertexAdmissible G A x' v := by
  have himg : A.image x = A.image x' := Finset.image_congr (fun a ha => h a ha)
  unfold vertexAdmissible
  ext c
  simp only [mem_filter, mem_univ, true_and, himg]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun u hu he => by rw [← h u hu]; exact h2 u hu he,
      fun u hu he => by rw [← h u hu]; exact h3 u hu he⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun u hu he => by rw [h u hu]; exact h2 u hu he,
      fun u hu he => by rw [h u hu]; exact h3 u hu he⟩

/-- The converse of `feasible_insert`: the label of the new vertex is admissible. -/
theorem mem_vertexAdmissible_of_feasible (G : OrientedGraph W) {A : Finset W} {y : W → F}
    {v : W} (hy : Feasible F G (insert v A) y) (hv : v ∉ A) :
    y v ∈ vertexAdmissible G A y v := by
  unfold vertexAdmissible
  simp only [mem_filter, mem_univ, true_and, mem_image, not_exists, not_and]
  refine ⟨fun a ha hya => ?_, fun u hu he => ?_, fun u hu he => ?_⟩
  · have := hy.1 a (mem_insert_of_mem ha) v (mem_insert_self v A) hya
    exact hv (this ▸ ha)
  · exact hy.2 (u, v) he (mem_insert_of_mem hu) (mem_insert_self v A)
  · exact hy.2 (v, u) he (mem_insert_self v A) (mem_insert_of_mem hu)

end Feasibility

/-- `W' = W ∖ {u, v}`. -/
def restSet (u v : W) : Finset W := univ \ {u, v}

theorem mem_restSet' {u v w : W} : w ∈ restSet u v ↔ w ≠ u ∧ w ≠ v := by
  unfold restSet
  simp

theorem u_notMem_restSet (u v : W) : u ∉ restSet u v := by simp [restSet]

theorem v_notMem_restSet (u v : W) : v ∉ restSet u v := by simp [restSet]

theorem insert_insert_restSet (u v : W) : insert v (insert u (restSet u v)) = univ := by
  ext w
  simp only [mem_insert, mem_univ, iff_true]
  by_cases hv : w = v
  · exact Or.inl hv
  · by_cases hu : w = u
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr (mem_restSet'.mpr ⟨hu, hv⟩))

theorem card_restSet {u v : W} (huv : u ≠ v) : (restSet u v).card = Fintype.card W - 2 := by
  unfold restSet
  rw [card_sdiff_of_subset (subset_univ _), card_univ, card_pair huv]

variable (G : OrientedGraph W)

/-- The labelling `z` with `z_u = x` and `z_v = x'`. -/
def pairExt (z : W → F) (u v : W) (x x' : F) : W → F :=
  Function.update (Function.update z u x) v x'

/-- `Φ`: the admissible pairs `(x, x')`. -/
noncomputable def pairAdm (z : W → F) (u v : W) : Finset (F × F) := by
  classical exact univ.filter fun ω => Feasible F G univ (pairExt z u v ω.1 ω.2)

/-- `c_y = #{x : (x, x + y) ∈ Φ}`. -/
noncomputable def diffCount (z : W → F) (u v : W) (y : F) : ℕ :=
  (univ.filter fun x => (x, x + y) ∈ pairAdm G z u v).card

omit [Field F] [Fintype F] [DecidableEq F] [Fintype W] in
theorem pairExt_u {z : W → F} {u v : W} (huv : u ≠ v) (x x' : F) : pairExt z u v x x' u = x := by
  unfold pairExt
  rw [Function.update_of_ne huv, Function.update_self]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype W] in
theorem pairExt_v {z : W → F} {u v : W} (x x' : F) : pairExt z u v x x' v = x' := by
  unfold pairExt
  rw [Function.update_self]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem pairExt_rest {z : W → F} {u v : W} (x x' : F) {w : W} (hw : w ∈ restSet u v) :
    pairExt z u v x x' w = z w := by
  rw [mem_restSet'] at hw
  unfold pairExt
  rw [Function.update_of_ne hw.2, Function.update_of_ne hw.1]

theorem mem_pairAdm {z : W → F} {u v : W} {ω : F × F} :
    ω ∈ pairAdm G z u v ↔ Feasible F G univ (pairExt z u v ω.1 ω.2) := by
  unfold pairAdm
  simp

/-- Admissible pairs are strict-square pairs. -/
theorem quadraticChar_of_mem_pairAdm {z : W → F} {u v : W} (huv : (u, v) ∈ G.E) {ω : F × F}
    (hω : ω ∈ pairAdm G z u v) : quadraticChar F (ω.2 - ω.1) = 1 := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  have hf := (mem_pairAdm G).mp hω
  have := hf.2 (u, v) huv (mem_univ _) (mem_univ _)
  rwa [pairExt_u huv', pairExt_v] at this

/-- **`|Φ| = ∑_{y ∈ Q} c_y`.** -/
theorem card_pairAdm_eq_sum {z : W → F} {u v : W} (huv : (u, v) ∈ G.E) :
    ((pairAdm G z u v).card : ℝ) =
      ∑ y ∈ univ.filter (fun y => quadraticChar F y = 1), (diffCount G z u v y : ℝ) := by
  have h1 : ((pairAdm G z u v).card : ℝ) = ∑ ω, (if ω ∈ pairAdm G z u v then 1 else 0) := by
    rw [Finset.sum_boole]
    congr 2
    ext ω
    simp
  have h2 : ∑ ω : F × F, (if ω ∈ pairAdm G z u v then (1 : ℝ) else 0) =
      ∑ x, ∑ y, (if (x, x + y) ∈ pairAdm G z u v then (1 : ℝ) else 0) := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro x _
    exact (Equiv.sum_comp (Equiv.addLeft x)
      (fun x' => if (x, x') ∈ pairAdm G z u v then (1 : ℝ) else 0)).symm
  rw [h1, h2, Finset.sum_comm, Finset.sum_filter]
  apply sum_congr rfl
  intro y _
  unfold diffCount
  rw [Finset.sum_boole]
  split_ifs with hy
  · rfl
  · have : (univ.filter fun x => (x, x + y) ∈ pairAdm G z u v) = ∅ := by
      rw [filter_eq_empty_iff]
      intro x _ hx
      apply hy
      have := quadraticChar_of_mem_pairAdm G huv hx
      rwa [add_sub_cancel_left] at this
    rw [this, card_empty, Nat.cast_zero]

/-- `c_y` is at most the number of admissible labels of `u` given `z|_{W'}`. -/
theorem diffCount_le_u {z : W → F} {u v : W} (huv : (u, v) ∈ G.E) (y : F) :
    diffCount G z u v y ≤ (vertexAdmissible G (restSet u v) z u).card := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  apply card_le_card
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx
  have hf := (mem_pairAdm G).mp hx
  have hfu : Feasible F G (insert u (restSet u v)) (pairExt z u v x (x + y)) :=
    feasible_mono G (subset_univ _) hf
  have hmem := mem_vertexAdmissible_of_feasible G hfu (u_notMem_restSet u v)
  rw [pairExt_u huv', vertexAdmissible_congr G (fun a ha => pairExt_rest x (x + y) ha)] at hmem
  exact hmem

/-- `c_y` is at most the number of admissible labels of `v` given `z|_{W'}`. -/
theorem diffCount_le_v {z : W → F} {u v : W} (y : F) :
    diffCount G z u v y ≤ (vertexAdmissible G (restSet u v) z v).card := by
  unfold diffCount
  rw [← card_image_of_injective _ (add_left_injective y)]
  apply card_le_card
  intro x' hx'
  simp only [mem_image, mem_filter, mem_univ, true_and] at hx'
  obtain ⟨x, hx, rfl⟩ := hx'
  have hf := (mem_pairAdm G).mp hx
  have hfv : Feasible F G (insert v (restSet u v)) (pairExt z u v x (x + y)) :=
    feasible_mono G (subset_univ _) hf
  have hmem := mem_vertexAdmissible_of_feasible G hfv (v_notMem_restSet u v)
  rw [pairExt_v, vertexAdmissible_congr G (fun a ha => pairExt_rest x (x + y) ha)] at hmem
  exact hmem

/-- **The sequential count**: labelling `u` first and then `v`,
`|Φ| ≥ ∑_{x ∈ Φ_u} |Φ_v(x)|`. -/
theorem card_pairAdm_ge {z : W → F} {u v : W} (huv : (u, v) ∈ G.E)
    (hA : Feasible F G (restSet u v) z) :
    ∑ x ∈ vertexAdmissible G (restSet u v) z u,
        (vertexAdmissible G (insert u (restSet u v)) (Function.update z u x) v).card ≤
      (pairAdm G z u v).card := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  rw [card_eq_sum_card_fiberwise (f := fun ω : F × F => ω.1) (t := univ)
    (fun _ _ => mem_univ _)]
  calc ∑ x ∈ vertexAdmissible G (restSet u v) z u,
        (vertexAdmissible G (insert u (restSet u v)) (Function.update z u x) v).card
      ≤ ∑ x ∈ vertexAdmissible G (restSet u v) z u,
          ((pairAdm G z u v).filter fun ω => ω.1 = x).card := by
        apply Finset.sum_le_sum
        intro x hx
        have hfeas1 := feasible_insert hA (u_notMem_restSet u v) hx
        rw [← card_image_of_injective _ (Prod.mk_right_injective x)]
        apply card_le_card
        intro ω hω
        simp only [mem_image] at hω
        obtain ⟨x', hx', rfl⟩ := hω
        have hvA : v ∉ insert u (restSet u v) := by
          simp only [mem_insert, not_or]
          exact ⟨Ne.symm huv', v_notMem_restSet u v⟩
        have hfeas2 := feasible_insert hfeas1 hvA hx'
        rw [insert_insert_restSet] at hfeas2
        simp only [mem_filter, and_true]
        exact (mem_pairAdm G).mpr hfeas2
    _ ≤ ∑ x, ((pairAdm G z u v).filter fun ω => ω.1 = x).card :=
        Finset.sum_le_sum_of_subset (subset_univ _)

theorem nbrCount_insert_u {u v : W} (huv : (u, v) ∈ G.E) :
    nbrCount G (insert u (restSet u v)) v = nbrCount G (restSet u v) v + 1 := by
  unfold nbrCount
  rw [Finset.filter_insert, ite_eq_left (Or.inl huv)]
  rw [card_insert_of_notMem]
  simp only [mem_filter, not_and]
  intro h
  exact absurd h (u_notMem_restSet u v)

/-! ## Generic differences -/

/-- The neighbours of `w` in `W'`. -/
noncomputable def restNbrs (u v w : W) : Finset W :=
  (restSet u v).filter fun a => (a, w) ∈ G.E ∨ (w, a) ∈ G.E

omit [Fintype F] [DecidableEq F] in
theorem card_restNbrs (u v w : W) : (restNbrs G u v w).card = nbrCount G (restSet u v) w := by
  unfold restNbrs nbrCount
  rfl

/-- `y` is generic if `B_u ∩ (B_v - y) = ∅`. -/
def IsGeneric (z : W → F) (u v : W) (y : F) : Prop :=
  ∀ a ∈ restNbrs G u v u, ∀ b ∈ restNbrs G u v v, z a ≠ z b - y

/-- The sign of the condition at a root: `1` for an edge into the new vertex, `χ(-1)` for an
edge out of it. -/
noncomputable def edgeSign (w a : W) : ℤ :=
  if (a, w) ∈ G.E then 1 else quadraticChar F (-1)

omit [Fintype W] in
theorem edgeSign_pm (w a : W) : edgeSign (F := F) G w a = 1 ∨ edgeSign (F := F) G w a = -1 := by
  unfold edgeSign
  split_ifs
  · exact Or.inl rfl
  · exact quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)

omit [Fintype W] in
/-- The edge conditions between a new label `c` and a labelled vertex `a` as one sign
condition. -/
theorem edge_cond_iff (z : W → F) (w a : W) (c : F) (hc : c - z a ≠ 0) :
    (((a, w) ∈ G.E → quadraticChar F (c - z a) = 1) ∧
        ((w, a) ∈ G.E → quadraticChar F (z a - c) = 1)) ↔
      ((a, w) ∈ G.E ∨ (w, a) ∈ G.E → quadraticChar F (c - z a) = edgeSign (F := F) G w a) := by
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  have hneg : quadraticChar F (z a - c) = quadraticChar F (-1) * quadraticChar F (c - z a) := by
    rw [← map_mul]
    congr 1
    ring
  have hpm := quadraticChar_dichotomy hc
  unfold edgeSign
  constructor
  · rintro ⟨h1, h2⟩ hor
    split_ifs with he
    · exact h1 he
    · have hwa : (w, a) ∈ G.E := hor.resolve_left he
      have := h2 hwa
      rw [hneg] at this
      have hsq : quadraticChar F (-1) * quadraticChar F (-1) = 1 := by
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
      calc quadraticChar F (c - z a)
          = (quadraticChar F (-1) * quadraticChar F (-1)) * quadraticChar F (c - z a) := by
            rw [hsq, one_mul]
        _ = quadraticChar F (-1) * (quadraticChar F (-1) * quadraticChar F (c - z a)) := by ring
        _ = quadraticChar F (-1) := by rw [this, mul_one]
  · intro h
    refine ⟨fun he => ?_, fun he => ?_⟩
    · have := h (Or.inl he)
      rwa [ite_eq_left he] at this
    · have hnot : (a, w) ∉ G.E := G.oriented w a he
      have := h (Or.inr he)
      rw [ite_eq_right hnot] at this
      rw [hneg, this]
      rcases hm1 with h' | h' <;> rw [h'] <;> norm_num

/-- The roots `B_u ∪ (B_v - y)`. -/
def pairRoots (z : W → F) (u v : W) (y : F) :
    {a // a ∈ restNbrs G u v u} ⊕ {b // b ∈ restNbrs G u v v} → F :=
  Sum.elim (fun a => z a.1) (fun b => z b.1 - y)

/-- The signs at the roots. -/
noncomputable def pairSigns (u v : W) :
    {a // a ∈ restNbrs G u v u} ⊕ {b // b ∈ restNbrs G u v v} → ℤ :=
  Sum.elim (fun a => edgeSign (F := F) G u a.1) (fun b => edgeSign (F := F) G v b.1)

/-- The excluded set `𝓛 ∪ (𝓛 - y)`. -/
noncomputable def pairExcl (z : W → F) (u v : W) (y : F) : Finset F :=
  (restSet u v).image z ∪ ((restSet u v).image z).image (fun c => c - y)

omit [Fintype F] in
theorem card_pairExcl_le (z : W → F) {u v : W} (huv : u ≠ v) (y : F) :
    (pairExcl z u v y).card ≤ 2 * (Fintype.card W - 2) := by
  unfold pairExcl
  calc _ ≤ ((restSet u v).image z).card + (((restSet u v).image z).image (fun c => c - y)).card :=
        card_union_le _ _
    _ ≤ (restSet u v).card + (restSet u v).card :=
        add_le_add card_image_le (card_image_le.trans card_image_le)
    _ = 2 * (Fintype.card W - 2) := by rw [card_restSet huv]; ring

theorem pairRoots_injective (z : W → F) {u v : W} (hA : Feasible F G (restSet u v) z) {y : F}
    (hgen : IsGeneric G z u v y) : Function.Injective (pairRoots G z u v y) := by
  have hmem (w : W) (a : W) (ha : a ∈ restNbrs G u v w) : a ∈ restSet u v :=
    (mem_filter.mp ha).1
  intro i j hij
  rcases i with ⟨a, ha⟩ | ⟨b, hb⟩ <;> rcases j with ⟨a', ha'⟩ | ⟨b', hb'⟩
  · simp only [pairRoots, Sum.elim_inl] at hij
    have := hA.1 a (hmem u a ha) a' (hmem u a' ha') hij
    subst this
    rfl
  · simp only [pairRoots, Sum.elim_inl, Sum.elim_inr] at hij
    exact absurd hij (hgen a ha b' hb')
  · simp only [pairRoots, Sum.elim_inl, Sum.elim_inr] at hij
    exact absurd hij.symm (hgen a' ha' b hb)
  · simp only [pairRoots, Sum.elim_inr, sub_left_inj] at hij
    have := hA.1 b (hmem v b hb) b' (hmem v b' hb') hij
    subst this
    rfl

omit [Fintype F] in
theorem pairRoots_mem (z : W → F) (u v : W) (y : F) (i) :
    pairRoots G z u v y i ∈ pairExcl z u v y := by
  unfold pairExcl
  rcases i with ⟨a, ha⟩ | ⟨b, hb⟩
  · simp only [pairRoots, Sum.elim_inl, mem_union, mem_image]
    exact Or.inl ⟨a, (mem_filter.mp ha).1, rfl⟩
  · simp only [pairRoots, Sum.elim_inr, mem_union, mem_image]
    exact Or.inr ⟨z b, ⟨b, (mem_filter.mp hb).1, rfl⟩, rfl⟩

/-- **A generic difference is a set of `lem:extension`.** -/
theorem diffCount_eq_admissible {z : W → F} {u v : W} (huv : (u, v) ∈ G.E)
    (hA : Feasible F G (restSet u v) z) {y : F} (hy : quadraticChar F y = 1) :
    (univ.filter fun x => (x, x + y) ∈ pairAdm G z u v) =
      admissible (pairRoots G z u v y) (pairSigns (F := F) G u v) (pairExcl z u v y) := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  have hvu : (v, u) ∉ G.E := G.oriented u v huv
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at hy
    exact zero_ne_one hy
  set A := restSet u v
  have hvA : v ∉ insert u A := by
    simp only [mem_insert, not_or]
    exact ⟨Ne.symm huv', v_notMem_restSet u v⟩
  ext x
  simp only [mem_filter, mem_univ, true_and]
  rw [mem_pairAdm]
  constructor
  · -- an admissible pair gives the conditions of `lem:extension`
    intro hf
    have hfu : Feasible F G (insert u A) (pairExt z u v x (x + y)) :=
      feasible_mono G (subset_univ _) hf
    have hmu := mem_vertexAdmissible_of_feasible G hfu (u_notMem_restSet u v)
    rw [pairExt_u huv', vertexAdmissible_congr G (fun a ha => pairExt_rest x (x + y) ha)] at hmu
    have hfv : Feasible F G (insert v A) (pairExt z u v x (x + y)) :=
      feasible_mono G (subset_univ _) hf
    have hmv := mem_vertexAdmissible_of_feasible G hfv (v_notMem_restSet u v)
    rw [pairExt_v, vertexAdmissible_congr G (fun a ha => pairExt_rest x (x + y) ha)] at hmv
    unfold vertexAdmissible at hmu hmv
    simp only [mem_filter, mem_univ, true_and, mem_image, not_exists, not_and] at hmu hmv
    obtain ⟨hu1, hu2, hu3⟩ := hmu
    obtain ⟨hv1, hv2, hv3⟩ := hmv
    unfold admissible pairExcl
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, not_or, not_exists,
      not_and, forall_exists_index, and_imp]
    refine ⟨⟨fun a ha hza => hu1 a ha hza, fun c a ha hza hc => ?_⟩, fun i => ?_⟩
    · subst hza
      apply hv1 a ha
      rw [← hc]
      ring
    · rcases i with ⟨a, ha⟩ | ⟨b, hb⟩
      · simp only [pairRoots, pairSigns, Sum.elim_inl]
        have haA := (mem_filter.mp ha).1
        have hadj := (mem_filter.mp ha).2
        have hne : x - z a ≠ 0 := sub_ne_zero.mpr (fun h => hu1 a haA h.symm)
        exact (edge_cond_iff G z u a x hne).mp ⟨hu2 a haA, hu3 a haA⟩ hadj
      · simp only [pairRoots, pairSigns, Sum.elim_inr]
        have hbA := (mem_filter.mp hb).1
        have hadj := (mem_filter.mp hb).2
        have hne : x + y - z b ≠ 0 := sub_ne_zero.mpr (fun h => hv1 b hbA h.symm)
        have := (edge_cond_iff G z v b (x + y) hne).mp ⟨hv2 b hbA, hv3 b hbA⟩ hadj
        rw [show x - (z b - y) = x + y - z b by ring]
        exact this
  · -- the conditions of `lem:extension` give an admissible pair
    intro hx
    unfold admissible pairExcl at hx
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, not_or, not_exists,
      not_and, forall_exists_index, and_imp] at hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    have hxu : x ∈ vertexAdmissible G A z u := by
      unfold vertexAdmissible
      simp only [mem_filter, mem_univ, true_and, mem_image, not_exists, not_and]
      refine ⟨fun a ha hza => hx1 a ha hza, fun a ha he => ?_, fun a ha he => ?_⟩
      · have hmem : a ∈ restNbrs G u v u := mem_filter.mpr ⟨ha, Or.inl he⟩
        have hne : x - z a ≠ 0 := sub_ne_zero.mpr (fun h => hx1 a ha h.symm)
        have := hx3 (Sum.inl ⟨a, hmem⟩)
        simp only [pairRoots, pairSigns, Sum.elim_inl] at this
        exact ((edge_cond_iff G z u a x hne).mpr (fun _ => this)).1 he
      · have hmem : a ∈ restNbrs G u v u := mem_filter.mpr ⟨ha, Or.inr he⟩
        have hne : x - z a ≠ 0 := sub_ne_zero.mpr (fun h => hx1 a ha h.symm)
        have := hx3 (Sum.inl ⟨a, hmem⟩)
        simp only [pairRoots, pairSigns, Sum.elim_inl] at this
        exact ((edge_cond_iff G z u a x hne).mpr (fun _ => this)).2 he
    have hfeas1 := feasible_insert hA (u_notMem_restSet u v) hxu
    have hxv : x + y ∈ vertexAdmissible G (insert u A) (Function.update z u x) v := by
      unfold vertexAdmissible
      simp only [mem_filter, mem_univ, true_and, mem_image, not_exists, not_and]
      have hupd (a : W) (ha : a ∈ A) : Function.update z u x a = z a :=
        Function.update_of_ne (fun h => u_notMem_restSet u v (by
          have ha' : a ∈ restSet u v := ha
          rw [h] at ha'
          exact ha')) _ _
      refine ⟨fun a ha hza => ?_, fun a ha he => ?_, fun a ha he => ?_⟩
      · rcases mem_insert.mp ha with rfl | ha'
        · rw [Function.update_self] at hza
          exact hy0 (by linear_combination (-1 : F) * hza)
        · rw [hupd a ha'] at hza
          exact hx2 (z a) a ha' rfl (by rw [hza]; ring)
      · rcases mem_insert.mp ha with rfl | ha'
        · rw [Function.update_self, add_sub_cancel_left]
          exact hy
        · rw [hupd a ha']
          have hmem : a ∈ restNbrs G u v v := mem_filter.mpr ⟨ha', Or.inl he⟩
          have hne : x + y - z a ≠ 0 := sub_ne_zero.mpr (fun h =>
            hx2 (z a) a ha' rfl (by rw [← h]; ring))
          have := hx3 (Sum.inr ⟨a, hmem⟩)
          simp only [pairRoots, pairSigns, Sum.elim_inr] at this
          rw [show x - (z a - y) = x + y - z a by ring] at this
          exact ((edge_cond_iff G z v a (x + y) hne).mpr (fun _ => this)).1 he
      · rcases mem_insert.mp ha with rfl | ha'
        · exact absurd he hvu
        · rw [hupd a ha']
          have hmem : a ∈ restNbrs G u v v := mem_filter.mpr ⟨ha', Or.inr he⟩
          have hne : x + y - z a ≠ 0 := sub_ne_zero.mpr (fun h =>
            hx2 (z a) a ha' rfl (by rw [← h]; ring))
          have := hx3 (Sum.inr ⟨a, hmem⟩)
          simp only [pairRoots, pairSigns, Sum.elim_inr] at this
          rw [show x - (z a - y) = x + y - z a by ring] at this
          exact ((edge_cond_iff G z v a (x + y) hne).mpr (fun _ => this)).2 he
    have hfeas2 := feasible_insert hfeas1 hvA hxv
    rw [insert_insert_restSet] at hfeas2
    exact hfeas2

/-- **The generic counts** (`lem:extension`(b), (c)): for `χ(y) = 1` and generic `y`,
`q - 𝔈_t - 2^t (2n - 4) ≤ 2^t c_y ≤ q + 𝔈_t`, `t = d'_u + d'_v`. -/
theorem diffCount_bounds (hW : WeilBound F) {z : W → F} {u v : W} (huv : (u, v) ∈ G.E)
    (hA : Feasible F G (restSet u v) z) {y : F} (hy : quadraticChar F y = 1)
    (hgen : IsGeneric G z u v y) :
    (2 : ℝ) ^ (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v) *
        diffCount G z u v y ≤
      Fintype.card F + softError (Fintype.card F)
        (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v) ∧
    (Fintype.card F : ℝ) - softError (Fintype.card F)
        (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v) -
        2 ^ (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v) *
          ((2 * (Fintype.card W - 2) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v) *
        diffCount G z u v y := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  have hcard : Fintype.card ({a // a ∈ restNbrs G u v u} ⊕ {b // b ∈ restNbrs G u v v}) =
      nbrCount G (restSet u v) u + nbrCount G (restSet u v) v := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, card_restNbrs, card_restNbrs]
  have hb := extension_bounds hW (pairRoots G z u v y) (pairRoots_injective G z hA hgen)
    (pairSigns (F := F) G u v)
    (fun i => by rcases i with ⟨a, _⟩ | ⟨b, _⟩ <;> exact edgeSign_pm G _ _)
    (pairExcl z u v y) (pairRoots_mem G z u v y)
  rw [hcard, ← diffCount_eq_admissible G huv hA hy] at hb
  unfold diffCount
  have hX : ((pairExcl z u v y).card : ℝ) ≤ ((2 * (Fintype.card W - 2) : ℕ) : ℝ) := by
    exact_mod_cast card_pairExcl_le z huv' y
  have hpow : (0 : ℝ) ≤ 2 ^ (nbrCount G (restSet u v) u + nbrCount G (restSet u v) v) := by
    positivity
  refine ⟨hb.1, ?_⟩
  have := mul_le_mul_of_nonneg_left hX hpow
  unfold softError
  linarith [hb.2]

open Classical in
/-- **At most `d'_u d'_v` values of `y` are not generic.** -/
theorem card_nongeneric_le (z : W → F) (u v : W) :
    (univ.filter fun y => ¬ IsGeneric G z u v y).card ≤
      nbrCount G (restSet u v) u * nbrCount G (restSet u v) v := by
  have hsub : (univ.filter fun y => ¬ IsGeneric G z u v y) ⊆
      ((restNbrs G u v u) ×ˢ (restNbrs G u v v)).image (fun ab => z ab.2 - z ab.1) := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and, IsGeneric, not_forall, not_not] at hy
    obtain ⟨a, ha, b, hb, h⟩ := hy
    simp only [mem_image, mem_product]
    exact ⟨(a, b), ⟨ha, hb⟩, by rw [h]; ring⟩
  calc _ ≤ (((restNbrs G u v u) ×ˢ (restNbrs G u v v)).image (fun ab => z ab.2 - z ab.1)).card :=
        card_le_card hsub
    _ ≤ ((restNbrs G u v u) ×ˢ (restNbrs G u v v)).card := card_image_le
    _ = _ := by rw [card_product, card_restNbrs, card_restNbrs]

end Sarkozy.TraceMixing
