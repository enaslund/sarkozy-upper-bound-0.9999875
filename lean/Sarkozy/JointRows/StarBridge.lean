module

public import Sarkozy.JointRows.StarRowsA
public import Sarkozy.JointRows.CollRowsFull

/-!
# The two star kernels agree: `Coll.starKer ς = StarOps.starKernel ς 𝒮_{≥2}`

Sources: `paper/sections/16_extraction.tex`, `prop:conditional-star` ("the star part consists of
the single pairs, the row stars ... and the column stars ... (`|T|, |S| ≥ 2`)"; "for a pinned row
at `p ≡ 3 (mod 4)`, `D_{ij} = ς_{ij}` for `(i, j) ∈ E_×` ... and `D_{ij} = 0` off `E_×`");
`paper/sections/14_spectral.tex`, `lem:spec:expansion`.

Fork C1-P's `Coll.starKer ς = ∑_{S ⊆ E_× star} ∏_{e∈S} χ_e` sums over the star subsets of the pair
set (`Extraction.IsStar`); `StarOps.starKernel D 𝒮` sums the single pairs, the row stars
`∏_{j∈T} D_{ij} χ(y_j - x_i)` and the column stars `∏_{i∈S} D_{ij} χ(y_j - x_i)` over `S, T ∈ 𝒮`.
* `rowStar_filter_eq`, `colStar_filter_eq`: the row (column) stars with at least two pairs are the
  sets `{i} × T` (`S × {j}`) with `|T| ≥ 2`, each exactly once;
* `star_indicator`: a star is a singleton, or a row star with `≥ 2` pairs, or a column star with
  `≥ 2` pairs, and exactly one of these;
* **`starKer_eq_starKernel`**: `starKer ς = starKernel ς 𝒮_{≥2}` at `p ≡ 3 (mod 4)`, where
  `𝒮_{≥2}` is the family of all sets with at least two elements (`sets2`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Sarkozy.JointRows.PaleyGauss

section Combinatorics

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- All sets with at least two elements. -/
def sets2 (β : Type*) [Fintype β] : Finset (Finset β) :=
  Finset.univ.filter fun T => 2 ≤ T.card

omit [DecidableEq α] [DecidableEq β] in
theorem mem_sets2 {T : Finset β} : T ∈ sets2 β ↔ 2 ≤ T.card := by
  simp [sets2]

/-- `{i} × T`. -/
def rowMap (q : α × Finset β) : Finset (α × β) := q.2.image fun j => (q.1, j)

/-- `S × {j}`. -/
def colMap (q : β × Finset α) : Finset (α × β) := q.2.image fun i => (i, q.1)

omit [Fintype α] [Fintype β] in
theorem card_rowMap (q : α × Finset β) : (rowMap q).card = q.2.card :=
  Finset.card_image_of_injective _ fun _ _ h => (Prod.mk.inj h).2

omit [Fintype α] [Fintype β] in
theorem card_colMap (q : β × Finset α) : (colMap q).card = q.2.card :=
  Finset.card_image_of_injective _ fun _ _ h => (Prod.mk.inj h).1

omit [Fintype α] [Fintype β] in
/-- A row star and a column star at once has one pair. -/
theorem card_eq_one_of_row_col {S : Finset (α × β)} (hr : Extraction.IsRowStar S)
    (hc : Extraction.IsColStar S) : S.card = 1 := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hr
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
  have hsub : S ⊆ {(i, j)} := fun e he => by
    have h1 : e.1 ∈ S.image Prod.fst := Finset.mem_image_of_mem _ he
    have h2 : e.2 ∈ S.image Prod.snd := Finset.mem_image_of_mem _ he
    rw [hi, Finset.mem_singleton] at h1
    rw [hj, Finset.mem_singleton] at h2
    rw [Finset.mem_singleton, Prod.ext_iff]
    exact ⟨h1, h2⟩
  have hne : S.Nonempty := by
    rw [← Finset.image_nonempty (f := Prod.fst), hi]; exact Finset.singleton_nonempty i
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  have := hne.card_pos
  omega

omit [Fintype α] [Fintype β] in
theorem row_col_of_card_one {S : Finset (α × β)} (h : S.card = 1) :
    Extraction.IsRowStar S ∧ Extraction.IsColStar S := by
  obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp h
  exact ⟨by simp [Extraction.IsRowStar], by simp [Extraction.IsColStar]⟩

omit [Fintype α] [Fintype β] [DecidableEq β] in
theorem card_pos_of_rowStar {S : Finset (α × β)} (h : Extraction.IsRowStar S) : 0 < S.card := by
  unfold Extraction.IsRowStar at h
  have h0 : 0 < (S.image Prod.fst).card := by omega
  exact Finset.card_pos.mpr (Finset.image_nonempty.mp (Finset.card_pos.mp h0))

/-- **The row stars with at least two pairs** are the sets `{i} × T`, `|T| ≥ 2`. -/
theorem rowStar_filter_eq :
    Finset.univ.filter (fun S : Finset (α × β) => Extraction.IsRowStar S ∧ 2 ≤ S.card) =
      (Finset.univ ×ˢ sets2 β).image rowMap := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_product,
    mem_sets2, Prod.exists]
  constructor
  · rintro ⟨hr, h2⟩
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hr
    have hfst : ∀ e ∈ S, e.1 = i := fun e he => by
      have h1 : e.1 ∈ S.image Prod.fst := Finset.mem_image_of_mem _ he
      rwa [hi, Finset.mem_singleton] at h1
    have hS : rowMap (i, S.image Prod.snd) = S := by
      ext e
      simp only [rowMap, Finset.mem_image]
      constructor
      · rintro ⟨j, ⟨e', he', rfl⟩, rfl⟩
        rw [← hfst e' he']
        exact he'
      · intro he
        exact ⟨e.2, ⟨e, he, rfl⟩, by rw [← hfst e he]⟩
    refine ⟨i, S.image Prod.snd, ?_, hS⟩
    rw [← card_rowMap (i, S.image Prod.snd), hS]
    exact h2
  · rintro ⟨i, T, hT, rfl⟩
    refine ⟨?_, by rw [card_rowMap]; exact hT⟩
    unfold Extraction.IsRowStar
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    have : (rowMap (i, T)).image Prod.fst = {i} := by
      ext a
      simp only [rowMap, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨_, ⟨j, _, rfl⟩, rfl⟩; rfl
      · rintro rfl
        obtain ⟨j, hj⟩ := hne
        exact ⟨(a, j), ⟨j, hj, rfl⟩, rfl⟩
    rw [this, Finset.card_singleton]

/-- **The column stars with at least two pairs** are the sets `S × {j}`, `|S| ≥ 2`. -/
theorem colStar_filter_eq :
    Finset.univ.filter (fun S : Finset (α × β) => Extraction.IsColStar S ∧ 2 ≤ S.card) =
      (Finset.univ ×ˢ sets2 α).image colMap := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_product,
    mem_sets2, Prod.exists]
  constructor
  · rintro ⟨hc, h2⟩
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
    have hsnd : ∀ e ∈ S, e.2 = j := fun e he => by
      have h1 : e.2 ∈ S.image Prod.snd := Finset.mem_image_of_mem _ he
      rwa [hj, Finset.mem_singleton] at h1
    have hS : colMap (j, S.image Prod.fst) = S := by
      ext e
      simp only [colMap, Finset.mem_image]
      constructor
      · rintro ⟨i, ⟨e', he', rfl⟩, rfl⟩
        rw [← hsnd e' he']
        exact he'
      · intro he
        exact ⟨e.1, ⟨e, he, rfl⟩, by rw [← hsnd e he]⟩
    refine ⟨j, S.image Prod.fst, ?_, hS⟩
    rw [← card_colMap (j, S.image Prod.fst), hS]
    exact h2
  · rintro ⟨j, T, hT, rfl⟩
    refine ⟨?_, by rw [card_colMap]; exact hT⟩
    unfold Extraction.IsColStar
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    have : (colMap (j, T)).image Prod.snd = {j} := by
      ext a
      simp only [colMap, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨_, ⟨i, _, rfl⟩, rfl⟩; rfl
      · rintro rfl
        obtain ⟨i, hi⟩ := hne
        exact ⟨(i, a), ⟨i, hi, rfl⟩, rfl⟩
    rw [this, Finset.card_singleton]

theorem rowMap_injOn : Set.InjOn (rowMap (α := α) (β := β))
    ((Finset.univ ×ˢ sets2 β : Finset (α × Finset β)) : Set (α × Finset β)) := by
  rintro ⟨i, T⟩ hq ⟨i', T'⟩ _ h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_sets2, Finset.mem_univ,
    true_and] at hq
  obtain ⟨j, hj⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : (i, j) ∈ rowMap (i', T') := by
    rw [← h]; exact Finset.mem_image_of_mem _ hj
  simp only [rowMap, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨_, _, hii, _⟩ := hmem
  subst hii
  have : T = T' := Finset.image_injective (fun _ _ h' => (Prod.mk.inj h').2) h
  rw [this]

theorem colMap_injOn : Set.InjOn (colMap (α := α) (β := β))
    ((Finset.univ ×ˢ sets2 α : Finset (β × Finset α)) : Set (β × Finset α)) := by
  rintro ⟨j, T⟩ hq ⟨j', T'⟩ _ h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_sets2, Finset.mem_univ,
    true_and] at hq
  obtain ⟨i, hi⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : (i, j) ∈ colMap (j', T') := by
    rw [← h]; exact Finset.mem_image_of_mem _ hi
  simp only [colMap, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨_, _, _, hjj⟩ := hmem
  subst hjj
  have : T = T' := Finset.image_injective (fun _ _ h' => (Prod.mk.inj h').1) h
  rw [this]

omit [Fintype α] [Fintype β] in
/-- **A star is exactly one of**: a singleton, a row star with `≥ 2` pairs, a column star with
`≥ 2` pairs. -/
theorem star_indicator (S : Finset (α × β)) (c : ℝ) :
    (if Extraction.IsStar S then c else 0) =
      (if S.card = 1 then c else 0) + (if Extraction.IsRowStar S ∧ 2 ≤ S.card then c else 0) +
        (if Extraction.IsColStar S ∧ 2 ≤ S.card then c else 0) := by
  unfold Extraction.IsStar
  by_cases h1 : S.card = 1
  · have := row_col_of_card_one h1
    simp only [this, true_or, ↓reduceIte, h1]
    norm_num
  · by_cases hr : Extraction.IsRowStar S
    · have hnc : ¬ Extraction.IsColStar S := fun hc => h1 (card_eq_one_of_row_col hr hc)
      have h2 : 2 ≤ S.card := by have := card_pos_of_rowStar hr; omega
      simp only [hr, true_or, ↓reduceIte, h1, h2, and_self, hnc, false_and]
      ring
    · by_cases hc : Extraction.IsColStar S
      · have h2 : 2 ≤ S.card := by
          have : 0 < S.card := by
            unfold Extraction.IsColStar at hc
            have h0 : 0 < (S.image Prod.snd).card := by omega
            exact Finset.card_pos.mpr (Finset.image_nonempty.mp (Finset.card_pos.mp h0))
          omega
        simp only [hr, hc, or_true, ↓reduceIte, h1, h2, and_self, false_and]
        ring
      · simp only [hr, hc, or_self, ↓reduceIte, h1, false_and]
        ring

end Combinatorics

variable {p : ℕ} [Fact p.Prime] {nv : ℕ}

/-- **The two star kernels agree** (`prop:conditional-star`, `lem:spec:expansion`): at
`p ≡ 3 (mod 4)`, `Coll.starKer ς = starKernel (ς : ℝ) 𝒮_{≥2}`. -/
theorem starKer_eq_starKernel (hp : p % 4 = 3) (ς : Fin nv → Fin nv → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (x y : Fin nv → ZMod p) :
    Coll.starKer ς x y = starKernel (fun i j => (ς i j : ℝ)) (sets2 (Fin nv)) x y := by
  set c : Fin nv × Fin nv → ℝ := fun e => (ς e.1 e.2 : ℝ) * chiR p (y e.2 - x e.1) with hc
  -- the star subsets of `E_×`, with `χ_e = c e`
  have hA : Coll.starKer ς x y = ∑ S ∈ Coll.starSets ς, ∏ e ∈ S, c e := by
    unfold Coll.starKer
    exact Finset.sum_congr rfl fun S _ => Finset.prod_congr rfl fun e _ =>
      Coll.chiPair_eq hp ς (hς e.1 e.2) x y
  -- extend to all star sets: a set leaving `E_×` has a factor `c e = 0`
  have hB : ∑ S ∈ Coll.starSets ς, ∏ e ∈ S, c e =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => Extraction.IsStar S),
        ∏ e ∈ S, c e := by
    apply Finset.sum_subset
    · intro S hS
      simp only [Coll.starSets, Finset.mem_filter, Finset.mem_powerset] at hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hS.2
    · intro S hS hS'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      simp only [Coll.starSets, Finset.mem_filter, Finset.mem_powerset, not_and] at hS'
      have hsub : ¬ S ⊆ Coll.pairSet ς := fun h => hS' h hS
      obtain ⟨e, he, he'⟩ := Finset.not_subset.mp hsub
      apply Finset.prod_eq_zero he
      simp only [Coll.pairSet, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at he'
      simp only [hc, he', Int.cast_zero, zero_mul]
  -- split the stars
  have hC : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => Extraction.IsStar S),
      ∏ e ∈ S, c e =
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => S.card = 1), ∏ e ∈ S, c e) +
      (∑ S ∈ Finset.univ.filter
        (fun S : Finset (Fin nv × Fin nv) => Extraction.IsRowStar S ∧ 2 ≤ S.card), ∏ e ∈ S, c e) +
      ∑ S ∈ Finset.univ.filter
        (fun S : Finset (Fin nv × Fin nv) => Extraction.IsColStar S ∧ 2 ≤ S.card),
          ∏ e ∈ S, c e := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun S _ => star_indicator S _
  -- the three classes
  have h1 : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => S.card = 1),
      ∏ e ∈ S, c e = ∑ i, ∑ j, (ς i j : ℝ) * chiR p (y j - x i) := by
    rw [show Finset.univ.filter (fun S : Finset (Fin nv × Fin nv) => S.card = 1) =
        Finset.powersetCard 1 Finset.univ by
      rw [Finset.powersetCard_eq_filter, Finset.powerset_univ], Finset.powersetCard_one,
      Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, Finset.prod_singleton]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have h2 : ∑ S ∈ Finset.univ.filter
      (fun S : Finset (Fin nv × Fin nv) => Extraction.IsRowStar S ∧ 2 ≤ S.card), ∏ e ∈ S, c e =
      ∑ i, ∑ T ∈ sets2 (Fin nv), ∏ j ∈ T, ((ς i j : ℝ) * chiR p (y j - x i)) := by
    rw [rowStar_filter_eq, Finset.sum_image rowMap_injOn, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun T _ => ?_
    unfold rowMap
    rw [Finset.prod_image fun j _ j' _ h => (Prod.mk.inj h).2]
  have h3 : ∑ S ∈ Finset.univ.filter
      (fun S : Finset (Fin nv × Fin nv) => Extraction.IsColStar S ∧ 2 ≤ S.card), ∏ e ∈ S, c e =
      ∑ j, ∑ S ∈ sets2 (Fin nv), ∏ i ∈ S, ((ς i j : ℝ) * chiR p (y j - x i)) := by
    rw [colStar_filter_eq, Finset.sum_image colMap_injOn, Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun S _ => ?_
    unfold colMap
    rw [Finset.prod_image fun i _ i' _ h => (Prod.mk.inj h).1]
  rw [hA, hB, hC, h1, h2, h3]
  rfl

end Sarkozy.JointRows.StarOps
