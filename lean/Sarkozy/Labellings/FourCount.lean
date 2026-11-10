module

public import Sarkozy.Labellings.GraphLaw

/-!
# Four-count comparison (`lem:four-count`)

`paper/sections/12_labellings.tex`. Two oriented graphs `G` on `W` and `G'` on `W'` share a vertex
set, given by injections `e : C → W` and `e' : C → W'`. On it, disjoint sets `M, S` with
`G[M ∪ S] = G'[M ∪ S]` (`hind`). The conditional laws of `z_S` given `z_M = x_M` under the uniform
laws on `Inj_p(G)` and `Inj_p(G')` are `C_G^{M∪S}(x_M, ·)/C_G^M(x_M)` and its `G'` analogue, with
`C_H^A(x)` = `extCount H A x`. So their density is
`ϱ = C_G^{M∪S} C_{G'}^M / (C_G^M C_{G'}^{M∪S})`. That formula is part (a)
(`graphLaw_prob`, `four_count_density`). The product over the primes of a block, part (c), is not
formalized.

* `upperProd_eq`, `lowerProd_eq`: the products of `lem:graphs:sequential` split as the main term
  `main_H(A) = q^{|W_H| - |A|} 2^{-(|E(H)| - |E(H[A])|)}` (`mainCount`) times the error products
  `∏(1 + e⁺)` (`upperErr`) and `∏ max(0, 1 - e⁻)` (`lowerErr`). The main term does not depend on
  the ordering (`sumNbr_add_edgeCount`).
* `mainCount_cancel`: the four main terms of `ϱ` cancel when `G[M ∪ S] = G'[M ∪ S]`.
* `four_count`: **`lem:four-count`(b)** in exponentiated form,
  `ϱ · lo_G(M) lo_{G'}(M∪S) ≤ up_G(M∪S) up_{G'}(M)` and
  `ϱ⁻¹ · lo_G(M∪S) lo_{G'}(M) ≤ up_G(M) up_{G'}(M∪S)`, written without division. Here `up` and
  `lo` are the error products, i.e. `e^{up_H(A)}` and `e^{-lo_H(A)}` in the paper's logarithmic
  notation.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The number of edges of `G` inside `A`. -/
def edgeCount (G : OrientedGraph W) (A : Finset W) : ℕ :=
  (G.E.filter fun e => e.1 ∈ A ∧ e.2 ∈ A).card

omit [Fintype W] in
theorem edgeCount_insert (G : OrientedGraph W) {A : Finset W} {v : W} (hv : v ∉ A) :
    edgeCount G (insert v A) = edgeCount G A + nbrCount G A v := by
  classical
  unfold edgeCount nbrCount
  have hsplit : G.E.filter (fun e => e.1 ∈ insert v A ∧ e.2 ∈ insert v A) =
      G.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ A) ∪
        G.E.filter (fun e => (e.1 = v ∧ e.2 ∈ A) ∨ (e.2 = v ∧ e.1 ∈ A)) := by
    ext e
    simp only [mem_filter, mem_union, mem_insert]
    constructor
    · rintro ⟨he, h1, h2⟩
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · have hev : e = (v, v) := Prod.ext h1 h2
        rw [hev] at he
        exact absurd he (G.loopless v)
      · exact Or.inr ⟨he, Or.inl ⟨h1, h2⟩⟩
      · exact Or.inr ⟨he, Or.inr ⟨h2, h1⟩⟩
      · exact Or.inl ⟨he, h1, h2⟩
    · rintro (⟨he, h1, h2⟩ | ⟨he, ⟨h1, h2⟩ | ⟨h2, h1⟩⟩)
      · exact ⟨he, Or.inr h1, Or.inr h2⟩
      · exact ⟨he, Or.inl h1, Or.inr h2⟩
      · exact ⟨he, Or.inr h1, Or.inl h2⟩
  have hdisj : Disjoint (G.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ A))
      (G.E.filter (fun e => (e.1 = v ∧ e.2 ∈ A) ∨ (e.2 = v ∧ e.1 ∈ A))) := by
    rw [disjoint_filter]
    rintro e _ ⟨h1, h2⟩ (⟨h, _⟩ | ⟨h, _⟩)
    · exact hv (h ▸ h1)
    · exact hv (h ▸ h2)
  rw [hsplit, card_union_of_disjoint hdisj]
  congr 1
  -- the edges at `v` correspond to the neighbours of `v` in `A`
  refine card_bij (fun e _ => if e.1 = v then e.2 else e.1) ?_ ?_ ?_
  · intro e he
    simp only [mem_filter] at he ⊢
    obtain ⟨he, h⟩ := he
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, ↓reduceIte]
      refine ⟨h2, Or.inr ?_⟩
      rw [← h1]; exact he
    · have hne : e.1 ≠ v := fun h => hv (h ▸ h2)
      simp only [hne, ↓reduceIte]
      refine ⟨h2, Or.inl ?_⟩
      rw [← h1]; exact he
  · intro e₁ he₁ e₂ he₂ h
    simp only [mem_filter] at he₁ he₂
    obtain ⟨he₁, h₁⟩ := he₁
    obtain ⟨he₂, h₂⟩ := he₂
    rcases h₁ with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases h₂ with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · simp only [a1, a2, ↓reduceIte] at h
      exact Prod.ext (a1.trans a2.symm) h
    · have hne : e₂.1 ≠ v := fun h => hv (h ▸ b2)
      simp only [a1, hne, ↓reduceIte] at h
      -- `e₁ = (v, u)` and `e₂ = (u, v)`: both orientations, impossible
      have h1 : (v, e₁.2) ∈ G.E := by rw [← a1]; exact he₁
      have h2 : (e₁.2, v) ∈ G.E := by rw [h, ← a2]; exact he₂
      exact absurd h2 (G.oriented _ _ h1)
    · have hne : e₁.1 ≠ v := fun h => hv (h ▸ b1)
      simp only [a2, hne, ↓reduceIte] at h
      have h1 : (e₁.1, v) ∈ G.E := by rw [← a1]; exact he₁
      have h2 : (v, e₁.1) ∈ G.E := by rw [h, ← a2]; exact he₂
      exact absurd h2 (G.oriented _ _ h1)
    · have hne1 : e₁.1 ≠ v := fun h => hv (h ▸ b1)
      have hne2 : e₂.1 ≠ v := fun h => hv (h ▸ b2)
      simp only [hne1, hne2, ↓reduceIte] at h
      exact Prod.ext h (a1.trans a2.symm)
  · intro u hu
    simp only [mem_filter] at hu
    obtain ⟨huA, h⟩ := hu
    have huv : u ≠ v := fun h => hv (h ▸ huA)
    rcases h with h | h
    · refine ⟨(u, v), mem_filter.mpr ⟨h, Or.inr ⟨rfl, huA⟩⟩, ?_⟩
      simp [huv]
    · refine ⟨(v, u), mem_filter.mpr ⟨h, Or.inl ⟨rfl, huA⟩⟩, ?_⟩
      simp

/-- The total number of earlier neighbours along an ordering. -/
noncomputable def sumNbr (G : OrientedGraph W) : Finset W → List W → ℕ
  | _, [] => 0
  | A, v :: l => nbrCount G A v + sumNbr G (insert v A) l

/-- Along an ordering `l` of `W ∖ A`, the earlier neighbours count the edges not inside `A`. -/
theorem sumNbr_add_edgeCount (G : OrientedGraph W) :
    ∀ (l : List W) (A : Finset W), l.Nodup → (∀ w, w ∈ A ∨ w ∈ l) → (∀ w ∈ l, w ∉ A) →
      sumNbr G A l + edgeCount G A = edgeCount G univ
  | [], A, _, hcov, _ => by
      have hA : A = univ := eq_univ_of_forall fun w => (hcov w).resolve_right (by simp)
      subst hA
      simp [sumNbr]
  | v :: l, A, hnd, hcov, hdisj => by
      have hv : v ∉ A := hdisj v (List.mem_cons_self ..)
      have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
      have hvl : v ∉ l := (List.nodup_cons.mp hnd).1
      have hcov' : ∀ w, w ∈ insert v A ∨ w ∈ l := fun w => by
        rcases hcov w with h | h
        · exact Or.inl (mem_insert_of_mem h)
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inl (mem_insert_self _ _)
          · exact Or.inr h'
      have hdisj' : ∀ w ∈ l, w ∉ insert v A := fun w hw hwA => by
        rcases mem_insert.mp hwA with rfl | h
        · exact hvl hw
        · exact hdisj w (List.mem_cons_of_mem _ hw) h
      have ih := sumNbr_add_edgeCount G l (insert v A) hnd' hcov' hdisj'
      rw [edgeCount_insert G hv] at ih
      simp only [sumNbr]
      omega

/-- The main term `main_H(A) = q^{|W| - |A|} 2^{-(|E(H)| - |E(H[A])|)}`. -/
noncomputable def mainCount (G : OrientedGraph W) (q : ℝ) (A : Finset W) : ℝ :=
  q ^ (Fintype.card W - A.card) / 2 ^ (edgeCount G univ - edgeCount G A)

omit [Fintype W] in
theorem edgeCount_mono (G : OrientedGraph W) {A B : Finset W} (hAB : A ⊆ B) :
    edgeCount G A ≤ edgeCount G B :=
  card_le_card fun y hy => by
    simp only [mem_filter] at hy ⊢
    exact ⟨hy.1, hAB hy.2.1, hAB hy.2.2⟩

theorem mainCount_nonneg (G : OrientedGraph W) {q : ℝ} (hq : 0 ≤ q) (A : Finset W) :
    0 ≤ mainCount G q A := by
  unfold mainCount; positivity

/-- The upper error product `∏_i (1 + 𝔈_{t_i}/q)`. -/
noncomputable def upperErr (G : OrientedGraph W) (q : ℝ) : Finset W → List W → ℝ
  | _, [] => 1
  | A, v :: l => (1 + softError q (nbrCount G A v) / q) * upperErr G q (insert v A) l

/-- The lower error product `∏_i max(0, 1 - (𝔈_{t_i} + 2^{t_i} n)/q)`. -/
noncomputable def lowerErr (G : OrientedGraph W) (q : ℝ) (n : ℕ) : Finset W → List W → ℝ
  | _, [] => 1
  | A, v :: l => max 0 (1 - (softError q (nbrCount G A v) + 2 ^ nbrCount G A v * n) / q) *
      lowerErr G q n (insert v A) l

omit [Fintype W] in
theorem upperProd_eq_aux (G : OrientedGraph W) {q : ℝ} (hq : 0 < q) :
    ∀ (l : List W) (A : Finset W),
      upperProd G q A l = q ^ l.length / 2 ^ sumNbr G A l * upperErr G q A l
  | [], A => by simp [upperProd, upperErr, sumNbr]
  | v :: l, A => by
      simp only [upperProd, upperErr, sumNbr, List.length_cons]
      rw [upperProd_eq_aux G hq l (insert v A)]
      unfold stepUpper
      rw [pow_succ, pow_add]
      field_simp

omit [Fintype W] in
theorem lowerProd_eq_aux (G : OrientedGraph W) {q : ℝ} (hq : 0 < q) (n : ℕ) :
    ∀ (l : List W) (A : Finset W),
      lowerProd G q n A l = q ^ l.length / 2 ^ sumNbr G A l * lowerErr G q n A l
  | [], A => by simp [lowerProd, lowerErr, sumNbr]
  | v :: l, A => by
      simp only [lowerProd, lowerErr, sumNbr, List.length_cons]
      rw [lowerProd_eq_aux G hq n l (insert v A)]
      unfold stepLower
      have h2 : (0 : ℝ) < 2 ^ nbrCount G A v := by positivity
      have hc : (0 : ℝ) < q / 2 ^ nbrCount G A v := div_pos hq h2
      have hstep : max 0 ((q - softError q (nbrCount G A v) - 2 ^ nbrCount G A v * n) /
          2 ^ nbrCount G A v) = q / 2 ^ nbrCount G A v *
            max 0 (1 - (softError q (nbrCount G A v) + 2 ^ nbrCount G A v * n) / q) := by
        rw [mul_max_of_nonneg _ _ hc.le, mul_zero]
        congr 1
        field_simp
        ring
      rw [hstep, pow_succ, pow_add]
      field_simp

theorem length_of_ordering {l : List W} {A : Finset W} (hnd : l.Nodup)
    (hcov : ∀ w, w ∈ A ∨ w ∈ l) (hdisj : ∀ w ∈ l, w ∉ A) :
    l.length = Fintype.card W - A.card := by
  have h : l.toFinset = univ \ A := by
    ext w
    simp only [List.mem_toFinset, mem_sdiff, mem_univ, true_and]
    exact ⟨fun hw => hdisj w hw, fun hw => (hcov w).resolve_left hw⟩
  rw [← List.toFinset_card_of_nodup hnd, h, card_sdiff_of_subset (subset_univ A), card_univ]

/-- `lem:graphs:sequential`'s upper product is the main term times the error product. -/
theorem upperProd_eq (G : OrientedGraph W) {q : ℝ} (hq : 0 < q) {l : List W} {A : Finset W}
    (hnd : l.Nodup) (hcov : ∀ w, w ∈ A ∨ w ∈ l) (hdisj : ∀ w ∈ l, w ∉ A) :
    upperProd G q A l = mainCount G q A * upperErr G q A l := by
  rw [upperProd_eq_aux G hq, mainCount, length_of_ordering hnd hcov hdisj]
  have := sumNbr_add_edgeCount G l A hnd hcov hdisj
  rw [show sumNbr G A l = edgeCount G univ - edgeCount G A by omega]

/-- `lem:graphs:sequential`'s lower product is the main term times the error product. -/
theorem lowerProd_eq (G : OrientedGraph W) {q : ℝ} (hq : 0 < q) (n : ℕ) {l : List W}
    {A : Finset W} (hnd : l.Nodup) (hcov : ∀ w, w ∈ A ∨ w ∈ l) (hdisj : ∀ w ∈ l, w ∉ A) :
    lowerProd G q n A l = mainCount G q A * lowerErr G q n A l := by
  rw [lowerProd_eq_aux G hq, mainCount, length_of_ordering hnd hcov hdisj]
  have := sumNbr_add_edgeCount G l A hnd hcov hdisj
  rw [show sumNbr G A l = edgeCount G univ - edgeCount G A by omega]

omit [Fintype W] in
theorem upperErr_nonneg (G : OrientedGraph W) {q : ℝ} (hq : 0 < q) :
    ∀ (l : List W) (A : Finset W), 0 ≤ upperErr G q A l
  | [], _ => by simp [upperErr]
  | v :: l, A => by
      simp only [upperErr]
      exact mul_nonneg (by have := softError_nonneg q (nbrCount G A v); positivity)
        (upperErr_nonneg G hq l _)

omit [Fintype W] in
theorem lowerErr_nonneg (G : OrientedGraph W) (q : ℝ) (n : ℕ) :
    ∀ (l : List W) (A : Finset W), 0 ≤ lowerErr G q n A l
  | [], _ => by simp [lowerErr]
  | v :: l, A => by
      simp only [lowerErr]
      exact mul_nonneg (le_max_left _ _) (lowerErr_nonneg G q n l _)

/-! ## Two graphs with the same induced graph -/

variable {W' C : Type*} [Fintype W'] [DecidableEq W'] [DecidableEq C]

omit [Fintype W] [DecidableEq C] in
/-- The edges of `G` inside `e(A)`, counted on `A`. -/
theorem edgeCount_image (G : OrientedGraph W) {e : C → W} (he : Function.Injective e)
    (A : Finset C) :
    edgeCount G (A.image e) = ((A ×ˢ A).filter fun ab => (e ab.1, e ab.2) ∈ G.E).card := by
  unfold edgeCount
  have h : G.E.filter (fun x => x.1 ∈ A.image e ∧ x.2 ∈ A.image e) =
      ((A ×ˢ A).filter fun ab => (e ab.1, e ab.2) ∈ G.E).image (fun ab => (e ab.1, e ab.2)) := by
    ext ⟨u, v⟩
    simp only [mem_filter, mem_image, mem_product, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨huv, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
      exact ⟨a, b, ⟨⟨ha, hb⟩, huv⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl, rfl⟩
      exact ⟨hab, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
  rw [h, card_image_of_injective]
  intro ⟨a, b⟩ ⟨a', b'⟩ hab
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext (he hab.1) (he hab.2)

omit [Fintype W] [Fintype W'] [DecidableEq C] in
/-- Equal induced graphs on `M ∪ S` have equal edge counts on every subset. -/
theorem edgeCount_transport (G : OrientedGraph W) (G' : OrientedGraph W') {e : C → W}
    {e' : C → W'} (he : Function.Injective e) (he' : Function.Injective e') {B A : Finset C}
    (hind : ∀ a ∈ B, ∀ b ∈ B, (e a, e b) ∈ G.E ↔ (e' a, e' b) ∈ G'.E) (hA : A ⊆ B) :
    edgeCount G (A.image e) = edgeCount G' (A.image e') := by
  rw [edgeCount_image G he, edgeCount_image G' he']
  congr 1
  exact filter_congr fun ab hab => by
    rw [mem_product] at hab
    exact hind _ (hA hab.1) _ (hA hab.2)

/-- **The main terms cancel** (`lem:four-count`(b)): if `G[M ∪ S] = G'[M ∪ S]`, then
`main_G(M ∪ S) main_{G'}(M) = main_G(M) main_{G'}(M ∪ S)`. -/
theorem mainCount_cancel (G : OrientedGraph W) (G' : OrientedGraph W') {e : C → W}
    {e' : C → W'} (he : Function.Injective e) (he' : Function.Injective e') (M S : Finset C)
    (hind : ∀ a ∈ M ∪ S, ∀ b ∈ M ∪ S, (e a, e b) ∈ G.E ↔ (e' a, e' b) ∈ G'.E) (q : ℝ) :
    mainCount G q ((M ∪ S).image e) * mainCount G' q (M.image e') =
      mainCount G q (M.image e) * mainCount G' q ((M ∪ S).image e') := by
  have hEMS := edgeCount_transport G G' he he' hind (subset_refl (M ∪ S))
  have hEM := edgeCount_transport G G' he he' hind (subset_union_left (s₂ := S))
  -- the counts of vertices
  have hcMS : ((M ∪ S).image e).card = (M ∪ S).card := card_image_of_injective _ he
  have hcMS' : ((M ∪ S).image e').card = (M ∪ S).card := card_image_of_injective _ he'
  have hcM : (M.image e).card = M.card := card_image_of_injective _ he
  have hcM' : (M.image e').card = M.card := card_image_of_injective _ he'
  have hle : M.card ≤ (M ∪ S).card := card_le_card subset_union_left
  have hW : (M ∪ S).card ≤ Fintype.card W := by
    rw [← hcMS]; exact card_le_univ _
  have hW' : (M ∪ S).card ≤ Fintype.card W' := by
    rw [← hcMS']; exact card_le_univ _
  -- the edge counts are monotone
  have h1 := edgeCount_mono G (image_subset_image (f := e) (subset_union_left (s₁ := M) (s₂ := S)))
  have h2 := edgeCount_mono G (subset_univ ((M ∪ S).image e))
  have h3 := edgeCount_mono G'
    (image_subset_image (f := e') (subset_union_left (s₁ := M) (s₂ := S)))
  have h4 := edgeCount_mono G' (subset_univ ((M ∪ S).image e'))
  unfold mainCount
  rw [hcMS, hcMS', hcM, hcM', div_mul_div_comm, div_mul_div_comm, ← pow_add, ← pow_add,
    ← pow_add, ← pow_add]
  congr 2
  · omega
  · omega

omit [Fintype W] [DecidableEq W] in
theorem Feasible.mono {G : OrientedGraph W} {A B : Finset W} {x : W → F}
    (hx : Feasible F G B x) (hAB : A ⊆ B) : Feasible F G A x :=
  ⟨fun a ha b hb h => hx.1 a (hAB ha) b (hAB hb) h,
    fun e he h1 h2 => hx.2 e he (hAB h1) (hAB h2)⟩

/-- **`lem:four-count`(b)**, in exponentiated form: with
`ϱ = C_G^{M∪S} C_{G'}^M / (C_G^M C_{G'}^{M∪S})` and the error products of the four orderings,
`ϱ · lo_G(M) lo_{G'}(M∪S) ≤ up_G(M∪S) up_{G'}(M)` and
`ϱ⁻¹ · lo_G(M∪S) lo_{G'}(M) ≤ up_G(M) up_{G'}(M∪S)`. The main terms cancel. -/
theorem four_count (hW : WeilBound F) (G : OrientedGraph W) (G' : OrientedGraph W')
    {e : C → W} {e' : C → W'} (he : Function.Injective e) (he' : Function.Injective e')
    (M S : Finset C)
    (hind : ∀ a ∈ M ∪ S, ∀ b ∈ M ∪ S, (e a, e b) ∈ G.E ↔ (e' a, e' b) ∈ G'.E)
    {n : ℕ} (hn : Fintype.card W ≤ n) (hn' : Fintype.card W' ≤ n)
    (l₁ l₂ : List W) (l₃ l₄ : List W')
    (h₁ : l₁.Nodup ∧ (∀ w, w ∈ M.image e ∨ w ∈ l₁) ∧ ∀ w ∈ l₁, w ∉ M.image e)
    (h₂ : l₂.Nodup ∧ (∀ w, w ∈ (M ∪ S).image e ∨ w ∈ l₂) ∧ ∀ w ∈ l₂, w ∉ (M ∪ S).image e)
    (h₃ : l₃.Nodup ∧ (∀ w, w ∈ M.image e' ∨ w ∈ l₃) ∧ ∀ w ∈ l₃, w ∉ M.image e')
    (h₄ : l₄.Nodup ∧ (∀ w, w ∈ (M ∪ S).image e' ∨ w ∈ l₄) ∧ ∀ w ∈ l₄, w ∉ (M ∪ S).image e')
    (x : W → F) (x' : W' → F)
    (hx : Feasible F G ((M ∪ S).image e) x) (hx' : Feasible F G' ((M ∪ S).image e') x') :
    let q : ℝ := Fintype.card F
    let CGMS : ℝ := extCount G ((M ∪ S).image e) x
    let CGM : ℝ := extCount G (M.image e) x
    let CG'MS : ℝ := extCount G' ((M ∪ S).image e') x'
    let CG'M : ℝ := extCount G' (M.image e') x'
    CGMS * CG'M * (lowerErr G q n (M.image e) l₁ * lowerErr G' q n ((M ∪ S).image e') l₄) ≤
        CGM * CG'MS * (upperErr G q ((M ∪ S).image e) l₂ * upperErr G' q (M.image e') l₃) ∧
      CGM * CG'MS * (lowerErr G q n ((M ∪ S).image e) l₂ * lowerErr G' q n (M.image e') l₃) ≤
        CGMS * CG'M * (upperErr G q (M.image e) l₁ * upperErr G' q ((M ∪ S).image e') l₄) := by
  intro q CGMS CGM CG'MS CG'M
  have hq : (0 : ℝ) < q := by simp only [q]; exact_mod_cast Fintype.card_pos
  have hxM : Feasible F G (M.image e) x := hx.mono (image_subset_image subset_union_left)
  have hxM' : Feasible F G' (M.image e') x' := hx'.mono (image_subset_image subset_union_left)
  obtain ⟨b₁l, b₁u⟩ := extCount_bounds hW G hn l₁ (M.image e) x h₁.1 h₁.2.1 h₁.2.2 hxM
  obtain ⟨b₂l, b₂u⟩ := extCount_bounds hW G hn l₂ ((M ∪ S).image e) x h₂.1 h₂.2.1 h₂.2.2 hx
  obtain ⟨b₃l, b₃u⟩ := extCount_bounds hW G' hn' l₃ (M.image e') x' h₃.1 h₃.2.1 h₃.2.2 hxM'
  obtain ⟨b₄l, b₄u⟩ := extCount_bounds hW G' hn' l₄ ((M ∪ S).image e') x' h₄.1 h₄.2.1 h₄.2.2 hx'
  rw [lowerProd_eq G hq n h₁.1 h₁.2.1 h₁.2.2] at b₁l
  rw [upperProd_eq G hq h₁.1 h₁.2.1 h₁.2.2] at b₁u
  rw [lowerProd_eq G hq n h₂.1 h₂.2.1 h₂.2.2] at b₂l
  rw [upperProd_eq G hq h₂.1 h₂.2.1 h₂.2.2] at b₂u
  rw [lowerProd_eq G' hq n h₃.1 h₃.2.1 h₃.2.2] at b₃l
  rw [upperProd_eq G' hq h₃.1 h₃.2.1 h₃.2.2] at b₃u
  rw [lowerProd_eq G' hq n h₄.1 h₄.2.1 h₄.2.2] at b₄l
  rw [upperProd_eq G' hq h₄.1 h₄.2.1 h₄.2.2] at b₄u
  have hcancel := mainCount_cancel G G' he he' M S hind q
  set mGMS := mainCount G q ((M ∪ S).image e)
  set mGM := mainCount G q (M.image e)
  set mG'MS := mainCount G' q ((M ∪ S).image e')
  set mG'M := mainCount G' q (M.image e')
  have u₁ := upperErr_nonneg G hq l₁ (M.image e)
  have u₂ := upperErr_nonneg G hq l₂ ((M ∪ S).image e)
  have u₃ := upperErr_nonneg G' hq l₃ (M.image e')
  have u₄ := upperErr_nonneg G' hq l₄ ((M ∪ S).image e')
  have w₁ := lowerErr_nonneg G q n l₁ (M.image e)
  have w₂ := lowerErr_nonneg G q n l₂ ((M ∪ S).image e)
  have w₃ := lowerErr_nonneg G' q n l₃ (M.image e')
  have w₄ := lowerErr_nonneg G' q n l₄ ((M ∪ S).image e')
  have c₁ : (0 : ℝ) ≤ CGM := Nat.cast_nonneg _
  have c₂ : (0 : ℝ) ≤ CGMS := Nat.cast_nonneg _
  have c₃ : (0 : ℝ) ≤ CG'M := Nat.cast_nonneg _
  have c₄ : (0 : ℝ) ≤ CG'MS := Nat.cast_nonneg _
  have m₁ := mainCount_nonneg G hq.le (M.image e)
  have m₂ := mainCount_nonneg G hq.le ((M ∪ S).image e)
  have m₃ := mainCount_nonneg G' hq.le (M.image e')
  have m₄ := mainCount_nonneg G' hq.le ((M ∪ S).image e')
  constructor
  · -- `C_G^{M∪S} C_{G'}^M lo lo ≤ (m u)(m u) lo lo = (m lo)(m lo) u u ≤ C_G^M C_{G'}^{M∪S} u u`
    calc CGMS * CG'M * (lowerErr G q n (M.image e) l₁ * lowerErr G' q n ((M ∪ S).image e') l₄)
        ≤ (mGMS * upperErr G q ((M ∪ S).image e) l₂) * (mG'M * upperErr G' q (M.image e') l₃) *
            (lowerErr G q n (M.image e) l₁ * lowerErr G' q n ((M ∪ S).image e') l₄) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg w₁ w₄)
          exact mul_le_mul b₂u b₃u c₃ (mul_nonneg m₂ u₂)
      _ = (mGM * lowerErr G q n (M.image e) l₁) * (mG'MS * lowerErr G' q n ((M ∪ S).image e') l₄) *
            (upperErr G q ((M ∪ S).image e) l₂ * upperErr G' q (M.image e') l₃) := by
          have : mGMS * mG'M = mGM * mG'MS := hcancel
          linear_combination (upperErr G q ((M ∪ S).image e) l₂ * upperErr G' q (M.image e') l₃ *
            lowerErr G q n (M.image e) l₁ * lowerErr G' q n ((M ∪ S).image e') l₄) * this
      _ ≤ CGM * CG'MS * (upperErr G q ((M ∪ S).image e) l₂ * upperErr G' q (M.image e') l₃) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg u₂ u₃)
          exact mul_le_mul b₁l b₄l (mul_nonneg m₄ w₄) c₁
  · calc CGM * CG'MS * (lowerErr G q n ((M ∪ S).image e) l₂ * lowerErr G' q n (M.image e') l₃)
        ≤ (mGM * upperErr G q (M.image e) l₁) * (mG'MS * upperErr G' q ((M ∪ S).image e') l₄) *
            (lowerErr G q n ((M ∪ S).image e) l₂ * lowerErr G' q n (M.image e') l₃) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg w₂ w₃)
          exact mul_le_mul b₁u b₄u c₄ (mul_nonneg m₁ u₁)
      _ = (mGMS * lowerErr G q n ((M ∪ S).image e) l₂) * (mG'M * lowerErr G' q n (M.image e') l₃) *
            (upperErr G q (M.image e) l₁ * upperErr G' q ((M ∪ S).image e') l₄) := by
          have : mGMS * mG'M = mGM * mG'MS := hcancel
          linear_combination (-(upperErr G q (M.image e) l₁ * upperErr G' q ((M ∪ S).image e') l₄ *
            lowerErr G q n ((M ∪ S).image e) l₂ * lowerErr G' q n (M.image e') l₃)) * this
      _ ≤ CGMS * CG'M * (upperErr G q (M.image e) l₁ * upperErr G' q ((M ∪ S).image e') l₄) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg u₁ u₄)
          exact mul_le_mul b₂l b₃l (mul_nonneg m₃ w₃) c₂

/-! ## Part (a): the density of the conditional laws -/

omit [DecidableEq C] [Fintype W'] [DecidableEq W'] in
/-- Under `λ_p(G)`, `λ(z_A = x_A) = C_G^A(x)/|Inj_p(G)|`. -/
theorem graphLaw_prob (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty)
    (A : Finset W) (x : W → F) :
    ∑ y ∈ univ.filter (fun y : W → F => ∀ a ∈ A, y a = x a), (graphLaw G hne).weight y =
      (extCount G A x : ℝ) / (injLabellings F G).card := by
  classical
  have hset : (univ.filter (fun y : W → F => ∀ a ∈ A, y a = x a)).filter
      (fun y => y ∈ injLabellings F G) =
      (injLabellings F G).filter (fun y => ∀ a ∈ A, y a = x a) := by
    ext y
    simp only [mem_filter, mem_univ, true_and]
    tauto
  have hsum : ∑ y ∈ univ.filter (fun y : W → F => ∀ a ∈ A, y a = x a), (graphLaw G hne).weight y =
      ∑ y ∈ (univ.filter (fun y : W → F => ∀ a ∈ A, y a = x a)).filter
        (fun y => y ∈ injLabellings F G), 1 / ((injLabellings F G).card : ℝ) := by
    rw [sum_filter (p := fun y => y ∈ injLabellings F G)]
    rfl
  rw [hsum, hset, sum_const, nsmul_eq_mul, mul_one_div]
  unfold extCount
  congr 2

/-- **`lem:four-count`(a)**: given `z_M = x_M`, the conditional law of `z_S` under `λ_p(G)` has
density `ϱ = C_G^{M∪S} C_{G'}^M / (C_G^M C_{G'}^{M∪S})` with respect to that under `λ_p(G')`,
at every `x_S` where the latter is positive. -/
theorem four_count_density (G : OrientedGraph W) (G' : OrientedGraph W')
    (hne : (injLabellings F G).Nonempty) (hne' : (injLabellings F G').Nonempty)
    (AM AMS : Finset W) (AM' AMS' : Finset W') (x : W → F) (x' : W' → F)
    (hM : 0 < extCount G AM x) (hM' : 0 < extCount G' AM' x')
    (hMS' : 0 < extCount G' AMS' x') :
    let P : Finset W → ℝ := fun A =>
      ∑ y ∈ univ.filter (fun y : W → F => ∀ a ∈ A, y a = x a), (graphLaw G hne).weight y
    let P' : Finset W' → ℝ := fun A =>
      ∑ y ∈ univ.filter (fun y : W' → F => ∀ a ∈ A, y a = x' a), (graphLaw G' hne').weight y
    (P AMS / P AM) / (P' AMS' / P' AM') =
      ((extCount G AMS x : ℝ) * extCount G' AM' x') /
        ((extCount G AM x : ℝ) * extCount G' AMS' x') := by
  intro P P'
  simp only [P, P', graphLaw_prob]
  have h1 : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have h2 : (0 : ℝ) < (injLabellings F G').card := by exact_mod_cast card_pos.mpr hne'
  have h3 : (0 : ℝ) < extCount G AM x := by exact_mod_cast hM
  have h4 : (0 : ℝ) < extCount G' AM' x' := by exact_mod_cast hM'
  have h5 : (0 : ℝ) < extCount G' AMS' x' := by exact_mod_cast hMS'
  field_simp

end Sarkozy.Labellings
