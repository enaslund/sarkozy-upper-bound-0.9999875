module

public import Sarkozy.L20Cap.PrimeCapsX1
public import Sarkozy.L20Cap.Stars
public import Sarkozy.L20Cap.Collisions

/-!
# The full nonstar kernel in X1's form (`cor:extraction-compressed`, the input `N_ns`)

`paper/sections/20_middle_reference.tex`, proof of `prop:l20-completion`: `T_ns`, the nonstar
part of the soft kernel `∏_{i,j}(1 + (D₂₀)_ijχ(x'_j - x_i))`, is bounded by `N_ns` from
`cor:extraction-compressed` (X1's `cor:soft-kernels`(a) form). Here the kernel `nonstar` of
`Stars` is identified with X1's soft nonstar class sum over the `16` pairs of `supp D₂₀`.

* `sum_nonstars_eq` (any finite `X`, `Z`, any `E ⊆ X × Z`, any weights): the nonstar sum
  `∑_{S ⊆ E nonstar} ∏_S w = ∏_E(1 + w) - 1 - ∑_i(∏_{row i}(1 + w) - 1)
  - ∑_j(∏_{col j}(1 + w) - 1) + ∑_E w`;
* **`nonstar_eq_X1`**: `nonstar x x' = ∑_{S ∈ nonstars Ex16} ∏_{e∈S} χ_e(x, x')` at the labels;
* **`hns_of_X1`**: a bound of X1's form on `λ_p(G6)` gives the hypothesis `hns` of the caps;
* **`l20_prime_caps_X1ns`**: `l20_prime_caps_X1` with `hns` in X1's form;
* **`hXns_of_compressed`**: that form from X1's `sk_soft_extraction_compressed_buckets_two_g`
  (`cor:extraction-compressed`), given the compressed class data of the `16`-pair kernel.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.Labellings Sarkozy.Extraction
  Sarkozy.ExtractionK

section General

variable {X Z : Type*} [DecidableEq X] [DecidableEq Z] [Fintype X] [Fintype Z]

omit [DecidableEq Z] [Fintype X] [Fintype Z] in
theorem image_fst_eq_singleton {S : Finset (X × Z)} {i : X} :
    S.image Prod.fst = {i} ↔ S.Nonempty ∧ ∀ e ∈ S, e.1 = i := by
  rw [eq_singleton_iff_unique_mem]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨e, he, rfl⟩ := mem_image.mp h1
    exact ⟨⟨e, he⟩, fun e' he' => h2 _ (mem_image_of_mem _ he')⟩
  · rintro ⟨⟨e, he⟩, h⟩
    refine ⟨mem_image.mpr ⟨e, he, h e he⟩, fun a ha => ?_⟩
    obtain ⟨e', he', rfl⟩ := mem_image.mp ha
    exact h e' he'

omit [DecidableEq X] [Fintype X] [Fintype Z] in
theorem image_snd_eq_singleton {S : Finset (X × Z)} {j : Z} :
    S.image Prod.snd = {j} ↔ S.Nonempty ∧ ∀ e ∈ S, e.2 = j := by
  rw [eq_singleton_iff_unique_mem]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨e, he, rfl⟩ := mem_image.mp h1
    exact ⟨⟨e, he⟩, fun e' he' => h2 _ (mem_image_of_mem _ he')⟩
  · rintro ⟨⟨e, he⟩, h⟩
    refine ⟨mem_image.mpr ⟨e, he, h e he⟩, fun a ha => ?_⟩
    obtain ⟨e', he', rfl⟩ := mem_image.mp ha
    exact h e' he'

omit [DecidableEq Z] [Fintype Z] in
theorem rowStar_indicator (S : Finset (X × Z)) :
    (if IsRowStar S then (1 : ℝ) else 0) =
      ∑ i, if S.image Prod.fst = {i} then (1 : ℝ) else 0 := by
  by_cases h : IsRowStar S
  · obtain ⟨a, ha⟩ := card_eq_one.mp h
    simp only [h, ↓reduceIte, ha, singleton_inj]
    simp
  · simp only [h, ↓reduceIte]
    symm
    refine sum_eq_zero fun i _ => ?_
    have : S.image Prod.fst ≠ {i} := by
      intro h'
      apply h
      show (S.image Prod.fst).card = 1
      rw [h', card_singleton]
    simp only [this, ↓reduceIte]

omit [DecidableEq X] [Fintype X] in
theorem colStar_indicator (S : Finset (X × Z)) :
    (if IsColStar S then (1 : ℝ) else 0) =
      ∑ j, if S.image Prod.snd = {j} then (1 : ℝ) else 0 := by
  by_cases h : IsColStar S
  · obtain ⟨a, ha⟩ := card_eq_one.mp h
    simp only [h, ↓reduceIte, ha, singleton_inj]
    simp
  · simp only [h, ↓reduceIte]
    symm
    refine sum_eq_zero fun j _ => ?_
    have : S.image Prod.snd ≠ {j} := by
      intro h'
      apply h
      show (S.image Prod.snd).card = 1
      rw [h', card_singleton]
    simp only [this, ↓reduceIte]

/-- The row-star part of the subset sum. -/
theorem sum_rowStars (E : Finset (X × Z)) (w : X × Z → ℝ) :
    ∑ S ∈ E.powerset, (if IsRowStar S then (1 : ℝ) else 0) * ∏ e ∈ S, w e =
      ∑ i, ((∏ e ∈ E.filter (fun e => e.1 = i), (1 + w e)) - 1) := by
  simp_rw [rowStar_indicator, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  simp_rw [boole_mul]
  rw [← sum_filter]
  have hset : E.powerset.filter (fun S => S.image Prod.fst = {i}) =
      (E.filter (fun e => e.1 = i)).powerset.erase ∅ := by
    ext S
    simp only [mem_filter, mem_powerset, mem_erase, image_fst_eq_singleton, ne_eq,
      ← nonempty_iff_ne_empty]
    constructor
    · rintro ⟨hS, hne, h⟩
      exact ⟨hne, fun e he => mem_filter.mpr ⟨hS he, h e he⟩⟩
    · rintro ⟨hne, h⟩
      exact ⟨fun e he => (mem_filter.mp (h he)).1, hne, fun e he => (mem_filter.mp (h he)).2⟩
  rw [hset, prod_one_add, ← sum_erase_add _ _ (empty_mem_powerset _), prod_empty,
    add_sub_cancel_right]

/-- The column-star part of the subset sum. -/
theorem sum_colStars (E : Finset (X × Z)) (w : X × Z → ℝ) :
    ∑ S ∈ E.powerset, (if IsColStar S then (1 : ℝ) else 0) * ∏ e ∈ S, w e =
      ∑ j, ((∏ e ∈ E.filter (fun e => e.2 = j), (1 + w e)) - 1) := by
  simp_rw [colStar_indicator, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  simp_rw [boole_mul]
  rw [← sum_filter]
  have hset : E.powerset.filter (fun S => S.image Prod.snd = {j}) =
      (E.filter (fun e => e.2 = j)).powerset.erase ∅ := by
    ext S
    simp only [mem_filter, mem_powerset, mem_erase, image_snd_eq_singleton, ne_eq,
      ← nonempty_iff_ne_empty]
    constructor
    · rintro ⟨hS, hne, h⟩
      exact ⟨hne, fun e he => mem_filter.mpr ⟨hS he, h e he⟩⟩
    · rintro ⟨hne, h⟩
      exact ⟨fun e he => (mem_filter.mp (h he)).1, hne, fun e he => (mem_filter.mp (h he)).2⟩
  rw [hset, prod_one_add, ← sum_erase_add _ _ (empty_mem_powerset _), prod_empty,
    add_sub_cancel_right]

omit [DecidableEq X] [DecidableEq Z] [Fintype X] [Fintype Z] in
/-- The singletons of the subset sum. -/
theorem sum_singletons (E : Finset (X × Z)) (w : X × Z → ℝ) :
    ∑ S ∈ E.powerset, (if S.card = 1 then (1 : ℝ) else 0) * ∏ e ∈ S, w e = ∑ e ∈ E, w e := by
  simp_rw [boole_mul]
  rw [← sum_filter]
  have hset : E.powerset.filter (fun S => S.card = 1) = E.powersetCard 1 := by
    ext S
    simp [mem_powersetCard, mem_filter, mem_powerset]
  rw [hset, powersetCard_one, sum_map]
  simp

omit [Fintype X] [Fintype Z] in
theorem card_one_iff_row_col (S : Finset (X × Z)) :
    S.card = 1 ↔ IsRowStar S ∧ IsColStar S := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := card_eq_one.mp h
    simp [IsRowStar, IsColStar]
  · rintro ⟨hr, hc⟩
    obtain ⟨i, hi⟩ := card_eq_one.mp hr
    obtain ⟨j, hj⟩ := card_eq_one.mp hc
    obtain ⟨hne, hi'⟩ := image_fst_eq_singleton.mp hi
    obtain ⟨-, hj'⟩ := image_snd_eq_singleton.mp hj
    have : S = {(i, j)} := by
      refine eq_singleton_iff_unique_mem.mpr ⟨?_, fun e he => Prod.ext (hi' e he) (hj' e he)⟩
      obtain ⟨e, he⟩ := hne
      have : e = (i, j) := Prod.ext (hi' e he) (hj' e he)
      rw [← this]
      exact he
    rw [this, card_singleton]

omit [Fintype X] [Fintype Z] in
/-- The indicator of "empty or a star". -/
theorem emptyOrStar_indicator (S : Finset (X × Z)) :
    (if S = ∅ ∨ IsStar S then (1 : ℝ) else 0) =
      (if S = ∅ then 1 else 0) + (if IsRowStar S then 1 else 0) + (if IsColStar S then 1 else 0) -
        (if S.card = 1 then 1 else 0) := by
  have hc := card_one_iff_row_col S
  by_cases h0 : S = ∅
  · subst h0
    simp [IsRowStar, IsColStar]
  · unfold IsStar
    by_cases hr : IsRowStar S <;> by_cases hcs : IsColStar S <;> simp [h0, hr, hcs, hc]

/-- **The nonstar part of a subset sum**: for any `E ⊆ X × Z` and weights `w`,
`∑_{S ⊆ E nonstar} ∏_S w = ∏_E(1 + w) - 1 - ∑_i(∏_{row i}(1 + w) - 1)
- ∑_j(∏_{col j}(1 + w) - 1) + ∑_E w`. -/
theorem sum_nonstars_eq (E : Finset (X × Z)) (w : X × Z → ℝ) :
    ∑ S ∈ nonstars E, ∏ e ∈ S, w e =
      (∏ e ∈ E, (1 + w e)) - 1 - ∑ i, ((∏ e ∈ E.filter (fun e => e.1 = i), (1 + w e)) - 1) -
        ∑ j, ((∏ e ∈ E.filter (fun e => e.2 = j), (1 + w e)) - 1) + ∑ e ∈ E, w e := by
  have hns : ∑ S ∈ nonstars E, ∏ e ∈ S, w e = ∑ S ∈ E.powerset,
      (1 - if S = ∅ ∨ IsStar S then (1 : ℝ) else 0) * ∏ e ∈ S, w e := by
    unfold nonstars
    rw [sum_filter]
    refine sum_congr rfl fun S _ => ?_
    by_cases h : S = ∅ ∨ IsStar S
    · have : ¬ IsNonstar S := fun hn => isNonstar_iff_not.mp hn h
      simp [h, this]
    · have : IsNonstar S := isNonstar_iff_not.mpr h
      simp [h, this]
  have h0 : ∑ S ∈ E.powerset, (if S = ∅ then (1 : ℝ) else 0) * ∏ e ∈ S, w e = 1 := by
    simp_rw [boole_mul]
    rw [sum_ite_eq' E.powerset ∅ (fun S => ∏ e ∈ S, w e)]
    simp
  rw [hns]
  simp_rw [emptyOrStar_indicator, sub_mul, add_mul]
  rw [sum_sub_distrib, sum_sub_distrib, sum_add_distrib, sum_add_distrib, h0, sum_rowStars,
    sum_colStars, sum_singletons]
  simp only [one_mul]
  rw [← prod_one_add]
  ring

end General

section Six

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The sixteen pairs** of `supp D₂₀`. -/
def Ex16 : Finset (Fin 6 × Fin 6) := univ.filter fun e => D20Z e.1 e.2 ≠ 0

theorem card_Ex16 : Ex16.card = 16 := by decide

/-- **X1's soft nonstar class sum of the full kernel** at two labellings (`Dsk = 1`). -/
noncomputable def Kns (z z' : Fin 6 → F) : ℝ :=
  ∑ S ∈ nonstars Ex16, ∏ e ∈ S, ((1 : ℝ) * chiPair D20Z e z z')

/-- The weights `w_e = (D₂₀)_eχ(z'_j - z_i)`. -/
noncomputable def wD (z z' : Fin 6 → F) (e : Fin 6 × Fin 6) : ℝ :=
  (D20Z e.1 e.2 : ℝ) * chi (z' e.2 - z e.1)

/-- `χ_e(z, z') = (D₂₀)_eχ(z'_j - z_i)` on `supp D₂₀`. -/
theorem chiPair_supp (hm1 : quadraticChar F (-1) = -1) {e : Fin 6 × Fin 6}
    (he : D20Z e.1 e.2 ≠ 0) (z z' : Fin 6 → F) :
    chiPair D20Z e z z' = (D20Z e.1 e.2 : ℝ) * chi (z' e.2 - z e.1) := by
  have hpm : D20Z e.1 e.2 = 1 ∨ D20Z e.1 e.2 = -1 := by
    revert he; revert e; decide
  unfold chiPair
  rcases hpm with h | h
  · rw [h]; simp [chi]
  · rw [h]
    have e1 : ((-1 : ℤ) : F) * (z' e.2 - z e.1) = -(z' e.2 - z e.1) := by push_cast; ring
    rw [e1]
    have := chi_neg hm1 (z' e.2 - z e.1)
    simp only [chi] at this
    rw [this]
    simp [chi]

/-- `Kns` is the nonstar sum of the weights `wD` over all `36` pairs. -/
theorem Kns_eq (hm1 : quadraticChar F (-1) = -1) (z z' : Fin 6 → F) :
    Kns z z' = ∑ S ∈ nonstars (univ : Finset (Fin 6 × Fin 6)), ∏ e ∈ S, wD z z' e := by
  unfold Kns
  have hA : ∀ S ∈ nonstars Ex16, ∏ e ∈ S, ((1 : ℝ) * chiPair D20Z e z z') =
      ∏ e ∈ S, wD z z' e := by
    intro S hS
    have hsub : S ⊆ Ex16 := mem_powerset.mp (mem_filter.mp hS).1
    refine prod_congr rfl fun e he => ?_
    rw [one_mul, chiPair_supp hm1 (mem_filter.mp (hsub he)).2]
    rfl
  rw [sum_congr rfl hA]
  refine sum_subset ?_ ?_
  · intro S hS
    simp only [nonstars, mem_filter, mem_powerset] at hS ⊢
    exact ⟨subset_univ _, hS.2⟩
  · intro S hS hS'
    have hn : ¬ S ⊆ Ex16 := by
      intro hsub
      apply hS'
      simp only [nonstars, mem_filter, mem_powerset] at hS ⊢
      exact ⟨hsub, hS.2⟩
    obtain ⟨e, he, he'⟩ := not_subset.mp hn
    refine prod_eq_zero he ?_
    have h0 : D20Z e.1 e.2 = 0 := by
      simp only [Ex16, mem_filter, mem_univ, true_and, not_not] at he'
      exact he'
    simp [wD, h0]

theorem filter_fst_univ (i : Fin 6) :
    (univ : Finset (Fin 6 × Fin 6)).filter (fun e => e.1 = i) = {i} ×ˢ univ := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, and_true]

theorem filter_snd_univ (j : Fin 6) :
    (univ : Finset (Fin 6 × Fin 6)).filter (fun e => e.2 = j) = univ ×ˢ {j} := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]

theorem small_supports :
    (univ : Finset (Finset (Fin 6))).filter (fun S => ¬ 2 ≤ S.card) =
      insert ∅ (univ.map ⟨singleton, singleton_injective⟩) := by
  decide

/-- `∑_{|S| ≥ 2} ∏_S f = ∏(1 + f) - 1 - ∑ f`. -/
theorem sum_supports6 (f : Fin 6 → ℝ) :
    ∑ S ∈ supports6, ∏ j ∈ S, f j = (∏ j, (1 + f j)) - 1 - ∑ j, f j := by
  rw [prod_one_add, powerset_univ]
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Finset (Fin 6)))
    (fun S => 2 ≤ S.card) (fun S => ∏ j ∈ S, f j)
  rw [small_supports, sum_insert (by decide), sum_map, prod_empty] at hsplit
  simp only [Function.Embedding.coeFn_mk, prod_singleton] at hsplit
  unfold supports6
  linarith

/-- **The nonstar part `T_ns` of the soft kernel is X1's nonstar class sum over `supp D₂₀`.** -/
theorem nonstar_eq_X1 (hm1 : quadraticChar F (-1) = -1) [Nonempty (CoreT F)]
    [Nonempty (PairT F)] (x x' : CoreT F × PairT F) :
    nonstar x x' = Kns (labels x) (labels x') := by
  rw [Kns_eq hm1, sum_nonstars_eq]
  set z := labels x with hz
  set z' := labels x' with hz'
  set a : Fin 6 → Fin 6 → ℝ := fun i j => (D20Z i j : ℝ) * chi (z' j - z i) with ha
  have hcD : ∀ i j, crossD i j = (D20Z i j : ℝ) := fun i j => by rw [crossD_eq_D20]; rfl
  have hK : Ksoft x x' = ∏ i, ∏ j, (1 + a i j) := by
    rw [Ksoft_eq_softKernel hm1]
    unfold softKernel
    simp only [hcD, ha]
    rfl
  have h2 : ∀ i, ∑ S ∈ supports6, (∏ j ∈ S, crossD i j) * ∏ j ∈ S, chi (z' j - z i) =
      (∏ j, (1 + a i j)) - 1 - ∑ j, a i j := by
    intro i
    rw [← sum_supports6]
    refine sum_congr rfl fun S _ => ?_
    rw [← prod_mul_distrib]
    simp only [hcD, ha]
  have h3 : ∑ S ∈ supports6, ∑ j, (∏ i ∈ S, crossD i j) * ∏ i ∈ S, chi (z' j - z i) =
      ∑ j, ((∏ i, (1 + a i j)) - 1 - ∑ i, a i j) := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_supports6 (fun i => a i j)]
    refine sum_congr rfl fun S _ => ?_
    rw [← prod_mul_distrib]
    simp only [hcD, ha]
  have hstar : starPart6 z z' = ∑ i, ∑ j, a i j + ∑ i, ((∏ j, (1 + a i j)) - 1 - ∑ j, a i j) +
      ∑ j, ((∏ i, (1 + a i j)) - 1 - ∑ i, a i j) := by
    unfold starPart6
    rw [sum_congr rfl fun i _ => h2 i, h3]
    simp only [hcD, ha]
  have hrow : ∀ i, ∏ e ∈ (univ : Finset (Fin 6 × Fin 6)).filter (fun e => e.1 = i),
      (1 + wD z z' e) = ∏ j, (1 + a i j) := by
    intro i
    rw [filter_fst_univ, prod_product, prod_singleton]
    rfl
  have hcol : ∀ j, ∏ e ∈ (univ : Finset (Fin 6 × Fin 6)).filter (fun e => e.2 = j),
      (1 + wD z z' e) = ∏ i, (1 + a i j) := by
    intro j
    rw [filter_snd_univ, prod_product]
    simp only [prod_singleton]
    rfl
  have hall : ∏ e ∈ (univ : Finset (Fin 6 × Fin 6)), (1 + wD z z' e) = ∏ i, ∏ j, (1 + a i j) := by
    rw [← Fintype.prod_prod_type']
    rfl
  have hsum : ∑ e ∈ (univ : Finset (Fin 6 × Fin 6)), wD z z' e = ∑ i, ∑ j, a i j := by
    rw [← Fintype.sum_prod_type']
    rfl
  have hc : ∑ j, ∑ i, a i j = ∑ i, ∑ j, a i j := sum_comm
  unfold nonstar
  rw [hK, hstar]
  simp only [hrow, hcol, hall, hsum, sum_sub_distrib]
  rw [hc]
  ring

end Six

section Transport

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

/-- **`hns` from X1's form** (`prop:l20-completion`, the input `N_ns`): a bound
`|⟨φ, K_{ns}h⟩_{λ_p(G6)}| ≤ N_ns‖φ‖‖h‖` for X1's soft nonstar class sum over `supp D₂₀`
(the conclusion of `sk_soft_extraction_compressed_*` or `sk_soft_extraction_leaf_partition_g`
with `Ex = Ex16`, `Dsk = 1`) gives `|⟨f, T_{ns}f⟩_{μ_p}| ≤ N_ns‖f‖²`. -/
theorem hns_of_X1 (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    (hne : (injLabellings F G6).Nonempty) {Nns : ℝ}
    (hX1 : ∀ φ h : (Fin 6 → F) → ℝ,
      |(graphLaw G6 hne).expect (fun z => φ z * (graphLaw G6 hne).expect (fun z' =>
          Kns z z' * h z'))| ≤
        Nns * Real.sqrt ((graphLaw G6 hne).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 hne).expect (fun z => h z ^ 2)))
    (f : CoreT F × PairT F → ℝ) :
    |kernelForm (halfLaw h6) (halfLaw h6) nonstar f f| ≤ Nns * nrm (halfLaw h6) f ^ 2 := by
  set φ : (Fin 6 → F) → ℝ := fun z => if hz : z ∈ injLabellings F G6 then f (toHalf z hz) else 0
    with hφ
  have hφl : ∀ x, Avoid x → φ (labels x) = f x := by
    intro x hx
    have hm := (labels_mem x).mpr hx
    simp only [hφ, hm, ↓reduceDIte, toHalf_labels]
  have hX := hX1 φ φ
  have hform : (graphLaw G6 hne).expect (fun z => φ z * (graphLaw G6 hne).expect (fun z' =>
      Kns z z' * φ z')) = kernelForm (halfLaw h6) (halfLaw h6) nonstar f f := by
    rw [kernelForm_apply, graphLaw_eq_halfLaw h6 hne]
    refine halfLaw_expect_congr h6 fun x hx => ?_
    rw [hφl x hx, graphLaw_eq_halfLaw h6 hne]
    congr 1
    refine halfLaw_expect_congr h6 fun x' hx' => ?_
    rw [nonstar_eq_X1 hm1 x x', hφl x' hx']
  have hnφ : Real.sqrt ((graphLaw G6 hne).expect (fun z => φ z ^ 2)) = nrm (halfLaw h6) f := by
    rw [graphLaw_eq_halfLaw h6 hne]
    unfold nrm ip
    congr 1
    refine halfLaw_expect_congr h6 fun x hx => ?_
    rw [hφl x hx, sq]
  rw [hform, hnφ] at hX
  rw [sq, ← mul_assoc]
  exact hX

end Transport

section Prime

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]

/-- **The caps of L20 over `𝔽_p` with `N_A` and `N_ns` both in X1's form**: `l20_prime_caps_X1`
with `hns` replaced by X1's form of the nonstar bound on `λ_p(G6)` (`hns_of_X1`). -/
theorem l20_prime_caps_X1ns (hm1 : quadraticChar (ZMod p) (-1) = -1) (hW : WeilBound (ZMod p))
    (h4 : FourCycleBound p) (h6 : 6 ≤ Fintype.card (ZMod p)) {m NA xg D mstar Nns χp : ℝ}
    (𝔓 : Finset (Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6)))
    (h𝔓 : IsExactPartition Ex8 𝔓 (nonstars Ex8))
    (rec : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → LeafRecordData (Fin 6))
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex8 c) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (hS1 : leafEhat G6 Q 6 < 1)
    (hNAle : ∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G6 D20Z Q 6 Ex8 c (rec c) ≤ NA)
    (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card (ZMod p) : ℝ)⁻¹ -
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) ^ 2)
    (hxg : xG (ZMod p) m NA ≤ xg)
    (hgate : cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) xg ≤ sP (ZMod p) m)
    (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hNns0 : 0 ≤ Nns)
    (hXns : ∀ φ h : (Fin 6 → ZMod p) → ℝ,
      |(graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z *
          (graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z' => Kns z z' * h z'))| ≤
        Nns * Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => h z ^ 2)))
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + D + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) xg /
      prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
        (1 - (Nns + D + mstar)) < 1)
    (hH1 : (Nns + D) / (1 - (Nns + D + mstar)) < 1) (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    -((sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) xg /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
          (1 - (Nns + D + mstar))) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - (Nns + D + mstar)))) * nrm (halfLaw h6) f ^ 2 := by
  exact l20_prime_caps_X1 hm1 hW h4 h6 𝔓 h𝔓 rec hrec hQ hQp hS1 hNAle hm hm0 hΔ hxg hgate hD0
    hD hNns0 (hns_of_X1 hm1 h6 (injLabellings_G6_nonempty h6) hXns) hstar hεZ hχ0 hchi hC1 hH1 f

end Prime

section Compressed

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]

/-- **`N_ns` from `cor:extraction-compressed`** (X1's `cor:soft-kernels`(a) form,
`sk_soft_extraction_compressed_buckets_two_g`): for an exact partition of the nonstars of
`supp D₂₀` into compressed classes with two-pair witnesses, covers and buckets, any `N_ns` at
least X1's bucket sum satisfies the hypothesis `hXns` of `l20_prime_caps_X1ns`. The class data
are hypotheses. -/
theorem hXns_of_compressed (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (h6 : 6 ≤ Fintype.card (ZMod p)) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G6 i) (Fintype.card (ZMod p)) 6 ≤ ehat)
    (hehat1 : ehat < 1) {Δ : ℕ} (hΔ : ∀ i, cmpDeg G6 D20Z i ≤ Δ)
    (𝔓 : Finset (Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6)))
    (h𝔓 : IsExactPartition Ex16 𝔓 (nonstars Ex16))
    (wit : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → Fin 2 → Fin 6 × Fin 6)
    (cx cz : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → Finset (Fin 6))
    (bucket : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex16 c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex16 c.1 c.2 (wit c) (cx c) (cz c))
    (hbucket : ∀ c ∈ 𝔓, cmpOc G6 (Ex16 \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c)
      (cz c) ≤ (bucket c : ℝ) * 2 ^ 𝔮)
    {Nns : ℝ}
    (hNsle : (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
        cmpLambda0 G6 D20Z (Fintype.card (ZMod p)) 6 ehat 2 *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          (2 : ℝ) ^ twoCycleCount (witnessIdx c.1 (wit c)) *
            Real.sqrt (2 ^ cmpEx G6 (Ex16 \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
              (cx c) (cz c))) * Real.exp (cmpGamma (Fintype.card (ZMod p)) 6 Δ * (b * 2 ^ 𝔮)))
        ≤ Nns) :
    ∀ φ h : (Fin 6 → ZMod p) → ℝ,
      |(graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z *
          (graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z' => Kns z z' * h z'))| ≤
        Nns * Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => h z ^ 2)) := by
  intro φ h
  have hp6 : 6 ≤ p := by rwa [ZMod.card] at h6
  have hp2 : p ≠ 2 := by omega
  have hς : ∀ j k, D20Z j k = 0 ∨ D20Z j k = 1 ∨ D20Z j k = -1 := by decide
  have hEx : ∀ e ∈ Ex16, D20Z e.1 e.2 ≠ 0 := fun e he => (mem_filter.mp he).2
  have hn : Fintype.card (Fin 6) ≤ 6 := by simp
  have hb := sk_soft_extraction_compressed_buckets_two_g hp2 h4 hW G6 D20Z hς D20Z_antisymm
    (injLabellings_G6_nonempty h6) hn hehat hehat1 hΔ Ex16 hEx 𝔓 h𝔓 wit cx cz bucket 𝔮 hwit hcov
    hbucket (fun _ => 1) (fun _ => by simp) φ h
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNsle (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

end Compressed

end Sarkozy.L20Cap
