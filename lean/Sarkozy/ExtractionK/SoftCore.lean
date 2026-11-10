module

public import Sarkozy.ExtractionK.Grouped

@[expose] public section

/-!
# Soft cross factors (`cor:soft-kernels`(a)) for `lem:matching:extractionk`

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(a): for coefficients `D_e ∈ [-1, 1]` the
soft class operator `T^D_𝒞 = ∑_{S ∈ 𝒞} D_S T_S`, `D_S = ∏_{e ∈ S} D_e`, satisfies the bound of
`lem:matching:extractionk` of the Boolean class (`grouped_extraction`).

* `sk_soft_extraction`: the bound, for all `D_e ∈ [-1, 1]` when `χ(-1) = -1` at the free pairs
  with `D_e < 0` (`p ≡ 3 (mod 4)`); `sk_soft_extraction_nonneg`: the bound when `D_e ≥ 0` on the
  free pairs, for every field. `sk_soft_sum_le`: the sum form (as `grouped_extraction_sum_le`).

## Proof

`∑_{S ∈ 𝒞} D_S χ_S = ∏_{e ∈ P} D_e χ_e ∏_{e ∈ F} (1 + D_e χ_e)` (`sk_sum_cls_eq`, `skSoftKer`).
The present factors give the constant `∏_{e ∈ P} D_e` of modulus at most one. A free factor is
`1 + D_e χ_e = (1 - |D_e|) + |D_e| (1 + χ'_e)` with `χ'_e = χ_e` if `D_e ≥ 0` and
`χ'_e = -χ_e = χ(-ς_e ⋯)` if `D_e < 0` (`sk_flip_identity`, which needs `χ(-1) = -1` at a flipped
pair; the flipped signs are `skFlip`). Expanding the product (`sk_softKer_expand`), the soft
kernel is `∏_P D_e · ∑_{T ⊆ F} w_T K_{P,T}` with convex weights `w_T` (`skW`, `skW_sum`) and the
Boolean kernels `K_{P,T}` of the sub-classes `𝒞(P, A ∪ (F \ T))` for the flipped signs. Each is
bounded by `lem:matching:extractionk` (`sk_grouped_sum_le`, the theorem with a symmetric support
of `ς` in place of antisymmetry, since the flipped signs are not antisymmetric; the transposed
side uses `ςᵀ_{jk} = -ς_{kj}`, `sk_other_side_le`). The vertex factors depend on the signs only
through their support (`sk_recordFactor_congr`), and the bound is nondecreasing in the free set
(`sk_recordFactor_mono`, `sk_recordExp_mono`, `sk_bound_mono`: `2^{|H|} 2^{-[b ∈ H]}` is
nondecreasing in `H`), so every `K_{P,T}` has at most the bound of `𝒞`.

## Not covered

The paper's proof works with the soft factors directly: the one-label sums of products of soft
factors are bounded through `lem:extraction-merged-count`, which holds for any signs. This file
instead reduces to Boolean kernels, which needs a sign `ν` with `χ(ν) = -1` among the integers
`±1` to flip a free pair with `D_e < 0`; so negative free coefficients are covered only when
`χ(-1) = -1`. For `χ(-1) = 1` (`p ≡ 1 (mod 4)`) and `D_e < 0` on a free pair, the one-vertex
bounds would have to be restated with general nonzero signs (or with soft factors).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SkSupport

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The transposed signs `ςᵀ_{jk} = -ς_{kj}` (the signs of the transposed class, Step 8). -/
def skT (ς : U → U → ℤ) : U → U → ℤ := fun j k => -ς k j

omit [Fintype U] [DecidableEq U] in
theorem skT_ne_zero_iff (ς : U → U → ℤ) (hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0) (j k : U) :
    skT ς j k ≠ 0 ↔ ς j k ≠ 0 := by
  unfold skT
  rw [neg_ne_zero]
  exact (hsym k j)

omit [Fintype U] [DecidableEq U] in
theorem skT_values (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (j k : U) :
    skT ς j k = 0 ∨ skT ς j k = 1 ∨ skT ς j k = -1 := by
  unfold skT
  rcases hς k j with h | h | h <;> simp [h]

omit [DecidableEq U] in
theorem sk_rowsN_congr {ς ς' : U → U → ℤ} (h : ∀ j k, ς j k ≠ 0 ↔ ς' j k ≠ 0) :
    rowsN ς = rowsN ς' := by
  funext k
  unfold rowsN
  exact filter_congr fun j _ => h j k

theorem sk_rowsCU_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ j k, ς j k ≠ 0 ↔ ς' j k ≠ 0) : rowsCU G ς = rowsCU G ς' := by
  funext j i
  unfold rowsCU
  rw [sk_rowsN_congr h]

theorem sk_rowsMg_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ j k, ς j k ≠ 0 ↔ ς' j k ≠ 0) : rowsMg G ς = rowsMg G ς' := by
  funext j i
  unfold rowsMg
  rw [sk_rowsN_congr h]

theorem sk_intNum_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ j k, ς j k ≠ 0 ↔ ς' j k ≠ 0) (q : ℝ) (n : ℕ) (ord : U → ℕ) (Fr : Finset (U × U))
    (Cz : Finset U) : intNum G ς q n ord Fr Cz = intNum G ς' q n ord Fr Cz := by
  funext u
  unfold intNum intExp
  rw [sk_rowsCU_congr G h]

theorem sk_intF_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ j k, ς j k ≠ 0 ↔ ς' j k ≠ 0) (q : ℝ) (n : ℕ) (ord : U → ℕ) (Fr : Finset (U × U))
    (Cz : Finset U) : intF G ς q n ord Fr Cz = intF G ς' q n ord Fr Cz := by
  funext u
  unfold intF
  rw [sk_intNum_congr G h]

theorem sk_coverRowF_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ j k, ς j k ≠ 0 ↔ ς' j k ≠ 0) (q : ℝ) (n : ℕ) (C : Finset U) (ord : U → ℕ)
    (H : Finset (U × U)) : coverRowF G ς q n C ord H = coverRowF G ς' q n C ord H := by
  funext b
  unfold coverRowF coverRowExp
  rw [sk_rowsCU_congr G h, sk_rowsMg_congr G h]

theorem sk_recordFactor_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ j k, ς j k ≠ 0 ↔ ς' j k ≠ 0) (q : ℝ) (n : ℕ) (Fr : Finset (U × U))
    (V W Cx Cz : Finset U) (ordX ordZ : U → ℕ) :
    recordFactor G ς q n Fr V W Cx Cz ordX ordZ = recordFactor G ς' q n Fr V W Cx Cz ordX ordZ := by
  unfold recordFactor
  rw [sk_intF_congr G h, sk_intF_congr G h, sk_coverRowF_congr G h, sk_coverRowF_congr G h]

end SkSupport

section SkQ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Field F] [DecidableEq F] in
theorem sk_intNumQ_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ j k, ς j k ≠ 0 ↔ ς' j k ≠ 0) (n : ℕ) (ord : U → ℕ) (Fr : Finset (U × U))
    (Cz : Finset U) : intNumQ F G ς n ord Fr Cz = intNumQ F G ς' n ord Fr Cz := by
  funext u
  unfold intNumQ
  rw [sk_intNum_congr G h]

omit [Field F] [DecidableEq F] in
theorem sk_coverNumQ_congr (G : OrientedGraph U) {ς ς' : U → U → ℤ}
    (h : ∀ j k, ς j k ≠ 0 ↔ ς' j k ≠ 0) (n : ℕ) (C : Finset U) (ord : U → ℕ)
    (H : Finset (U × U)) : coverNumQ F G ς n C ord H = coverNumQ F G ς' n C ord H := by
  funext b
  unfold coverNumQ coverRowExp
  rw [sk_rowsCU_congr G h, sk_rowsMg_congr G h]

omit [Fintype U] [DecidableEq U] in
theorem sk_chiPair_skT_swap (ς : U → U → ℤ) (e : U × U) (x x' : U → F) :
    chiPair (skT ς) e.swap x' x = chiPair ς e x x' := by
  unfold chiPair skT
  simp only [Prod.fst_swap, Prod.snd_swap, Int.cast_neg]
  congr 2
  ring

omit [Fintype U] in
theorem sk_groupKer_swap (ς : U → U → ℤ) (P Fr : Finset (U × U)) (p : U × U → Prop)
    [DecidablePred p] (x x' : U → F) :
    groupKer (skT ς) (P.image Prod.swap) (Fr.image Prod.swap) p x' x =
      groupKer ς P Fr (fun e => p e.swap) x x' := by
  unfold groupKer
  rw [filter_image, filter_image, prod_image (fun a _ b _ h => Prod.swap_injective h),
    prod_image (fun a _ b _ h => Prod.swap_injective h)]
  simp only [sk_chiPair_skT_swap]

theorem sk_betaF_eq_alphaF (G : OrientedGraph U) (ς : U → U → ℤ) (P Fr : Finset (U × U))
    (W Cx Cz : Finset U) (h : (U → F) → ℝ) (c c' w : U → F) :
    betaF G ς P Fr W Cx Cz h c c' w =
      alphaF G (skT ς) (P.image Prod.swap) (Fr.image Prod.swap) W Cz Cx h c' c w := by
  unfold alphaF betaF
  refine sum_congr rfl fun x' _ => ?_
  rw [sk_groupKer_swap ς, mul_comm]
  congr 1
  unfold groupKer
  congr 2
  · exact filter_congr fun e _ => and_comm
  · exact filter_congr fun e _ => and_comm

omit [Fintype U] in
theorem sk_gam_swap (ς : U → U → ℤ) (P Fr : Finset (U × U)) (Cx Cz : Finset U) (c c' : U → F) :
    groupKer (skT ς) (P.image Prod.swap) (Fr.image Prod.swap) (predGam Cz Cx) c' c =
      groupKer ς P Fr (predGam Cx Cz) c c' := by
  rw [sk_groupKer_swap ς]
  unfold groupKer
  congr 2
  · exact filter_congr fun e _ => and_comm
  · exact filter_congr fun e _ => and_comm

/-- **Step 8 without antisymmetry**: the other side, with the factors computed from the transposed
signs `ςᵀ` (equal to those of `ς` when the support is symmetric). -/
theorem sk_other_side_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (W Cx Cz : Finset U) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hFr2 : ∀ e ∈ Fr, e.2 ∉ Cz → e.1 ∈ Cx)
    (ordX ordZ : U → ℕ) (hordX : Set.InjOn ordX Cx) (hordZ : Function.Injective ordZ)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    (h : (U → F) → ℝ) :
    ∑ c ∈ (injLabellings F G).image (restr Cx), ∑ c' ∈ (injLabellings F G).image (restr Cz),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ w ∈ injTuples F W, betaF G ς P Fr W Cx Cz h c c' w ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.2 ∈ W)).card *
        (∏ u ∈ univ \ (W ∪ Cz), intNumQ F G (skT ς) n ordZ (Fr.image Prod.swap) Cx u) *
        (∏ b ∈ Cx, coverNumQ F G (skT ς) n Cx ordX
          ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b) *
        ∑ x ∈ injLabellings F G, h x ^ 2 := by
  have hT := one_side_le hW G (skT ς) (skT_values ς hς) n (P.image Prod.swap)
    (Fr.image Prod.swap)
    (fun e he => by
      obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
      simp only [skT, Prod.fst_swap, Prod.snd_swap, neg_ne_zero]
      exact hFrς e₀ he₀)
    W Cz Cx hWC
    (fun e he h1 => by
      obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
      exact hFr2 e₀ he₀ h1)
    ordZ ordX hordZ hordX hsegZ h
  rw [card_filter_swap] at hT
  refine le_trans (le_of_eq ?_) hT
  rw [sum_comm]
  refine sum_congr rfl fun c' _ => sum_congr rfl fun c _ => ?_
  rw [sk_gam_swap ς]
  congr 1
  exact sum_congr rfl fun w _ => by rw [sk_betaF_eq_alphaF G ς]

/-- `grouped_extraction_count` with a symmetric support of `ς` in place of antisymmetry. -/
theorem sk_grouped_count (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0)
    (n : ℕ) (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (V W Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W) Λ)
    (f h : (U → F) → ℝ) :
    |∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * classKer ς P Fr x x' * h x'| ≤
      Λ * Real.sqrt (2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
          (∏ u ∈ univ \ (V ∪ Cx), intNumQ F G ς n ordX Fr Cz u) *
          (∏ b ∈ Cz, coverNumQ F G ς n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
          ∑ x ∈ injLabellings F G, f x ^ 2) *
        Real.sqrt (2 ^ (Fr.filter (fun e => e.2 ∈ W)).card *
          (∏ u ∈ univ \ (W ∪ Cz), intNumQ F G ς n ordZ (Fr.image Prod.swap) Cx u) *
          (∏ b ∈ Cx, coverNumQ F G ς n Cx ordX
            ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b) *
          ∑ x ∈ injLabellings F G, h x ^ 2) := by
  refine (bilinear_le G ς P Fr V W Cx Cz hVC hWC hP hFr hΛ hker f h).trans ?_
  have h1 := one_side_le hW G ς hς n P Fr hFrς V Cx Cz hVC
    (fun e he h1 => (hFr e he).resolve_left h1) ordX ordZ hordX hordZ.injOn hsegX f
  have h2 := sk_other_side_le hW G ς hς n P Fr hFrς W Cx Cz hWC
    (fun e he h2 => (hFr e he).resolve_right h2) ordX ordZ hordX.injOn hordZ hsegZ h
  have hsupp : ∀ j k, skT ς j k ≠ 0 ↔ ς j k ≠ 0 := skT_ne_zero_iff ς hsym
  rw [sk_intNumQ_congr G hsupp, sk_coverNumQ_congr G hsupp] at h2
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hΛ)
    (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) (mul_nonneg hΛ (Real.sqrt_nonneg _))

/-- `grouped_extraction_sum_le` with a symmetric support of `ς` in place of antisymmetry. -/
theorem sk_grouped_sum_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0) {n : ℕ}
    (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ}
    (V W Cx Cz : Finset U) (hVk : V.card = k) (hWk : W.card = k)
    (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * classKer ς P Fr x x' * h x') /
        ((injLabellings F G).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, ordT G ordX v + ∑ v ∈ W, ordT G ordZ v) *
          ((∏ u ∈ univ \ (V ∪ Cx), intF G ς (Fintype.card F) n ordX Fr Cz u) *
            (∏ b ∈ Cz, coverRowF G ς (Fintype.card F) n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
            (∏ u ∈ univ \ (W ∪ Cz), intF G ς (Fintype.card F) n ordZ (Fr.image Prod.swap) Cx u) *
            ∏ b ∈ Cx, coverRowF G ς (Fintype.card F) n Cx ordX
              ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b)) /
        (1 - ehat) ^ k *
        Real.sqrt ((∑ x ∈ injLabellings F G, f x ^ 2) / (injLabellings F G).card) *
        Real.sqrt ((∑ x ∈ injLabellings F G, h x ^ 2) / (injLabellings F G).card) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  set I := injLabellings F G
  set N : ℝ := (I.card : ℝ)
  set Ux := univ \ (V ∪ Cx)
  set Uz := univ \ (W ∪ Cz)
  set H := Fr.filter (fun e => e.2 ∈ Cz)
  set HT := (Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set fW := (Fr.filter (fun e => e.2 ∈ W)).card
  set tV := ∑ v ∈ V, ordT G ordX v
  set tW := ∑ v ∈ W, ordT G ordZ v
  set ℓX := stepLow G q n ordX
  set ℓZ := stepLow G q n ordZ
  have he1 : ∀ ord v, coarseError (ordT G ord v) q n < 1 := fun ord v =>
    lt_of_le_of_lt (coarseError_ordT_le G hehat ord v) hehat1
  have hℓpos : ∀ ord v, 0 < stepLow G q n ord v := fun ord v => by
    unfold stepLow
    have := he1 ord v
    exact mul_pos (mul_pos hq0 (by positivity)) (by linarith)
  -- the counting bound
  have hΛ : 0 ≤ cker * Real.sqrt q ^ k := mul_nonneg hcker (by positivity)
  have hQ := sk_grouped_count hW G ς hς hsym n P Fr hFrς V W Cx Cz hVC hWC hP hFr ordX
    ordZ hordX hordZ hsegX hsegZ hΛ hker f h
  -- the lower counts
  have hLX : ∏ v, ℓX v ≤ N := by
    have := card_injLabellings_ge hW G hn ordX hordX (fun v => (he1 ordX v).le)
    refine le_trans (le_of_eq ?_) this
    refine prod_congr rfl fun v _ => ?_
    simp only [ℓX, stepLow, div_eq_mul_inv, inv_pow, hq]
  have hLZ : ∏ v, ℓZ v ≤ N := by
    have := card_injLabellings_ge hW G hn ordZ hordZ (fun v => (he1 ordZ v).le)
    refine le_trans (le_of_eq ?_) this
    refine prod_congr rfl fun v _ => ?_
    simp only [ℓZ, stepLow, div_eq_mul_inv, inv_pow, hq]
  have hLX0 : 0 < ∏ v, ℓX v := prod_pos fun v _ => hℓpos ordX v
  have hLZ0 : 0 < ∏ v, ℓZ v := prod_pos fun v _ => hℓpos ordZ v
  have hN0 : 0 < N := lt_of_lt_of_le hLX0 hLX
  -- the factor identities
  set PUx := ∏ u ∈ Ux, intF G ς q n ordX Fr Cz u
  set PCz := ∏ b ∈ Cz, coverRowF G ς q n Cz ordZ H b
  set PUz := ∏ u ∈ Uz, intF G ς q n ordZ (Fr.image Prod.swap) Cx u
  set PCx := ∏ b ∈ Cx, coverRowF G ς q n Cx ordX HT b
  have hMUx : ∏ u ∈ Ux, intNumQ F G ς n ordX Fr Cz u = PUx * ∏ u ∈ Ux, ℓX u := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun u _ => intNumQ_eq G ς n ordX Fr Cz u (he1 ordX u)
  have hMUz : ∏ u ∈ Uz, intNumQ F G ς n ordZ (Fr.image Prod.swap) Cx u =
      PUz * ∏ u ∈ Uz, ℓZ u := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun u _ => intNumQ_eq G ς n ordZ _ Cx u (he1 ordZ u)
  have hMCz : ∏ b ∈ Cz, coverNumQ F G ς n Cz ordZ H b = PCz * ∏ b ∈ Cz, ℓZ b := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => coverNumQ_eq G ς n Cz ordZ H hZ0 hb (he1 ordZ b)
  have hMCx : ∏ b ∈ Cx, coverNumQ F G ς n Cx ordX HT b = PCx * ∏ b ∈ Cx, ℓX b := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => coverNumQ_eq G ς n Cx ordX HT hX0 hb (he1 ordX b)
  rw [hMUx, hMCz, hMUz, hMCx] at hQ
  set A := (2 : ℝ) ^ fV * (PUx * ∏ u ∈ Ux, ℓX u) * (PCz * ∏ b ∈ Cz, ℓZ b)
  set B := (2 : ℝ) ^ fW * (PUz * ∏ u ∈ Uz, ℓZ u) * (PCx * ∏ b ∈ Cx, ℓX b)
  have hPF0 : ∀ ord Fr' Cz' u, 0 ≤ intF G ς q n ord Fr' Cz' u := by
    intro ord Fr' Cz' u
    have h1 := intNumQ_nonneg (F := F) G ς n ord Fr' Cz' u
    rw [intNumQ_eq G ς n ord Fr' Cz' u (he1 ord u)] at h1
    exact nonneg_of_mul_nonneg_left h1 (hℓpos ord u)
  have hcF0 : ∀ (C : Finset U) (ord : U → ℕ) (H' : Finset (U × U)),
      (∀ a ∈ C, ∀ b, b ∉ C → ord a < ord b) → ∀ b ∈ C, 0 ≤ coverRowF G ς q n C ord H' b := by
    intro C ord H' hseg b hb
    have h1 := coverNumQ_nonneg (F := F) G ς n C ord H' b
    rw [coverNumQ_eq G ς n C ord H' hseg hb (he1 ord b)] at h1
    exact nonneg_of_mul_nonneg_left h1 (hℓpos ord b)
  have hPUx0 : 0 ≤ PUx := prod_nonneg fun u _ => hPF0 _ _ _ u
  have hPUz0 : 0 ≤ PUz := prod_nonneg fun u _ => hPF0 _ _ _ u
  have hPCz0 : 0 ≤ PCz := prod_nonneg fun b hb => hcF0 Cz ordZ H hZ0 b hb
  have hPCx0 : 0 ≤ PCx := prod_nonneg fun b hb => hcF0 Cx ordX HT hX0 b hb
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUx0 (prod_nonneg fun u _ => (hℓpos ordX u).le)))
    (mul_nonneg hPCz0 (prod_nonneg fun u _ => (hℓpos ordZ u).le))
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUz0 (prod_nonneg fun u _ => (hℓpos ordZ u).le)))
    (mul_nonneg hPCx0 (prod_nonneg fun u _ => (hℓpos ordX u).le))
  have hnorm := normalize_le hN0 hLX0 hLZ0 hLX hLZ hA0 hB0
    (sum_nonneg fun x _ => sq_nonneg (f x)) (sum_nonneg fun x _ => sq_nonneg (h x)) hΛ hQ
  refine hnorm.trans ?_
  -- the witness factors
  set DV := ∏ v ∈ V, ℓX v
  set DW := ∏ v ∈ W, ℓZ v
  have hDV : q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k ≤ DV := by
    have : ∏ v ∈ V, (q * (2 : ℝ)⁻¹ ^ ordT G ordX v * (1 - ehat)) ≤ DV := by
      refine prod_le_prod₀ (fun v _ => ?_) (fun v _ => ?_)
      · exact mul_nonneg (mul_nonneg hq0.le (by positivity)) (by linarith)
      · simp only [ℓX, stepLow]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hq0.le (by positivity))
        linarith [coarseError_ordT_le G hehat ordX v]
    refine le_trans (le_of_eq ?_) this
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hVk, prod_pow_eq_pow_sum]
  have hDW : q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k ≤ DW := by
    have : ∏ v ∈ W, (q * (2 : ℝ)⁻¹ ^ ordT G ordZ v * (1 - ehat)) ≤ DW := by
      refine prod_le_prod₀ (fun v _ => ?_) (fun v _ => ?_)
      · exact mul_nonneg (mul_nonneg hq0.le (by positivity)) (by linarith)
      · simp only [ℓZ, stepLow]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hq0.le (by positivity))
        linarith [coarseError_ordT_le G hehat ordZ v]
    refine le_trans (le_of_eq ?_) this
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hWk, prod_pow_eq_pow_sum]
  have h1e : 0 < 1 - ehat := by linarith
  have hdV0 : 0 < q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k := by positivity
  have hdW0 : 0 < q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k := by positivity
  -- `A B = 2^{f_V + f_W} ∏ F · L_X L_Z / (D_V D_W)`
  set PF := PUx * PCz * PUz * PCx
  have hPF0 : 0 ≤ PF := mul_nonneg (mul_nonneg (mul_nonneg hPUx0 hPCz0) hPUz0) hPCx0
  have hsplitX : ∏ v, ℓX v = (∏ v ∈ Ux, ℓX v) * DV * ∏ v ∈ Cx, ℓX v :=
    prod_univ_three V Cx hVC ℓX
  have hsplitZ : ∏ v, ℓZ v = (∏ v ∈ Uz, ℓZ v) * DW * ∏ v ∈ Cz, ℓZ v :=
    prod_univ_three W Cz hWC ℓZ
  have hAB : A * B / ((∏ v, ℓX v) * ∏ v, ℓZ v) = 2 ^ fV * 2 ^ fW * PF / (DV * DW) := by
    rw [hsplitX, hsplitZ]
    have h1 : (0 : ℝ) < ∏ v ∈ Ux, ℓX v := prod_pos fun v _ => hℓpos ordX v
    have h2 : (0 : ℝ) < ∏ v ∈ Cx, ℓX v := prod_pos fun v _ => hℓpos ordX v
    have h3 : (0 : ℝ) < ∏ v ∈ Uz, ℓZ v := prod_pos fun v _ => hℓpos ordZ v
    have h4 : (0 : ℝ) < ∏ v ∈ Cz, ℓZ v := prod_pos fun v _ => hℓpos ordZ v
    have h5 : (0 : ℝ) < DV := prod_pos fun v _ => hℓpos ordX v
    have h6 : (0 : ℝ) < DW := prod_pos fun v _ => hℓpos ordZ v
    simp only [A, B, PF]
    field_simp
  rw [hAB]
  have hbound : 2 ^ fV * 2 ^ fW * PF / (DV * DW) ≤
      2 ^ fV * 2 ^ fW * PF / ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
        (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hdV0 hdW0)
      (mul_le_mul hDV hDW hdW0.le (lt_of_lt_of_le hdV0 hDV).le)
  have hinv : ((Real.sqrt q)⁻¹ ^ k) ^ 2 = (q ^ k)⁻¹ := by
    rw [inv_pow, inv_pow, sqrt_pow_sq hq0.le]
  have hsq : (cker * Real.sqrt q ^ k) ^ 2 *
      (2 ^ fV * 2 ^ fW * PF / ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
        (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k))) =
      (cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k) ^ 2 * (2 ^ (fV + fW + tV + tW) * PF) := by
    have e1 : (cker * Real.sqrt q ^ k) ^ 2 = cker ^ 2 * q ^ k := by
      rw [mul_pow, sqrt_pow_sq hq0.le]
    have e2 : (cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k) ^ 2 =
        cker ^ 2 * (q ^ k)⁻¹ / ((1 - ehat) ^ k) ^ 2 := by
      rw [div_pow, mul_pow, hinv]
    rw [e1, e2]
    simp only [pow_add, inv_pow]
    have hq' : (q ^ k) ≠ 0 := by positivity
    have he' : (1 - ehat) ^ k ≠ 0 := by positivity
    field_simp
  have hc' : 0 ≤ cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k := by positivity
  have hkey : cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF / (DV * DW)) ≤
      cker * (Real.sqrt q)⁻¹ ^ k * Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) / (1 - ehat) ^ k := by
    calc cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF / (DV * DW))
        ≤ cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF /
            ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
              (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k))) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbound) hΛ
      _ = Real.sqrt ((cker * Real.sqrt q ^ k) ^ 2 * (2 ^ fV * 2 ^ fW * PF /
            ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
              (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k)))) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛ]
      _ = Real.sqrt ((cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k) ^ 2 *
            (2 ^ (fV + fW + tV + tW) * PF)) := by rw [hsq]
      _ = cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k *
            Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc']
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)


end SkQ


section SkMono

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] in
/-- `2^{|H|} 2^{-[b ∈ H]}` is nondecreasing in `H`. -/
theorem sk_two_pow_ite_mono {H H' : Finset U} (hHH : H ⊆ H') (b : U) :
    (2 : ℝ) ^ H.card * (if b ∈ H then (2 : ℝ)⁻¹ else 1) ≤
      2 ^ H'.card * (if b ∈ H' then (2 : ℝ)⁻¹ else 1) := by
  by_cases hb : b ∈ H
  · have hb' : b ∈ H' := hHH hb
    simp only [hb, hb', ↓reduceIte]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (card_le_card hHH))
      (by norm_num)
  · by_cases hb' : b ∈ H'
    · simp only [hb, hb', ↓reduceIte, mul_one]
      have hlt : H.card < H'.card := card_lt_card ⟨hHH, fun h => hb (h hb')⟩
      have : (2 : ℝ) ^ (H.card + 1) ≤ 2 ^ H'.card := pow_le_pow_right₀ (by norm_num) hlt
      rw [pow_succ] at this
      linarith
    · simp only [hb, hb', ↓reduceIte, mul_one]
      exact pow_le_pow_right₀ (by norm_num) (card_le_card hHH)

theorem sk_intH_mono {Fr Fr' : Finset (U × U)} (h : Fr ⊆ Fr') (u : U) :
    intH Fr u ⊆ intH Fr' u := by
  intro b hb
  simp only [intH, mem_filter, mem_univ, true_and] at hb ⊢
  exact h hb

theorem sk_coverRowH_mono {H H' : Finset (U × U)} (h : H ⊆ H') (b : U) :
    coverRowH H b ⊆ coverRowH H' b := by
  intro a ha
  simp only [coverRowH, mem_filter, mem_univ, true_and] at ha ⊢
  exact h ha

/-- The numerator of `F_u` is nondecreasing in the free pairs. -/
theorem sk_intNum_mono (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (n : ℕ) (ord : U → ℕ)
    {Fr Fr' : Finset (U × U)} (hFr : Fr ⊆ Fr') (Cz : Finset U) (u : U) :
    intNum G ς q n ord Fr Cz u ≤ intNum G ς q n ord Fr' Cz u := by
  unfold intNum
  have hS : intS G ord Fr u ≤ intS G ord Fr' u := by
    unfold intS
    exact Nat.add_le_add_left (card_le_card (sk_intH_mono hFr u)) _
  have he := coarseError_mono (q := q) (Nat.cast_nonneg n) hS
  have hsum : (2 : ℝ) ^ intS G ord Fr u * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b ≤
      (2 : ℝ) ^ intS G ord Fr' u * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr' u b := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun b _ => ?_
    rw [intExp_two_zpow, intExp_two_zpow]
    unfold intS
    rw [pow_add, pow_add]
    have hm : (2 : ℝ) ^ (intH Fr u).card * (if b ∈ intH Fr u then (2 : ℝ)⁻¹ else 1) ≤
        2 ^ (intH Fr' u).card * (if b ∈ intH Fr' u then (2 : ℝ)⁻¹ else 1) :=
      sk_two_pow_ite_mono (sk_intH_mono hFr u) b
    have h0 : (0 : ℝ) ≤ 2 ^ ordT G ord u * 2 ^ rowsCU G ς u b := by positivity
    calc (2 : ℝ) ^ ordT G ord u * 2 ^ (intH Fr u).card *
          (2 ^ rowsCU G ς u b * if b ∈ intH Fr u then (2 : ℝ)⁻¹ else 1)
        = (2 ^ ordT G ord u * 2 ^ rowsCU G ς u b) *
            ((2 : ℝ) ^ (intH Fr u).card * if b ∈ intH Fr u then (2 : ℝ)⁻¹ else 1) := by ring
      _ ≤ (2 ^ ordT G ord u * 2 ^ rowsCU G ς u b) *
            ((2 : ℝ) ^ (intH Fr' u).card * if b ∈ intH Fr' u then (2 : ℝ)⁻¹ else 1) :=
          mul_le_mul_of_nonneg_left hm h0
      _ = _ := by ring
  have hr : (0 : ℝ) ≤ (Real.sqrt q)⁻¹ ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hsum hr
  nlinarith [this, he]

/-- The numerator of `F_b` is nondecreasing in the free pairs `H` at `b`. -/
theorem sk_coverNum_mono (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (n : ℕ) (C : Finset U)
    (ord : U → ℕ) {H H' : Finset (U × U)} (hH : H ⊆ H') (b : U) :
    1 + coarseError (coverRowS G C ord H b) q (2 * n) +
        (Real.sqrt q)⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b ≤
      1 + coarseError (coverRowS G C ord H' b) q (2 * n) +
        (Real.sqrt q)⁻¹ ^ 2 * 2 ^ coverRowS G C ord H' b *
          ∑ j, (2 : ℝ) ^ coverRowExp G ς H' j b := by
  have hS : coverRowS G C ord H b ≤ coverRowS G C ord H' b := by
    unfold coverRowS
    exact Nat.add_le_add_left (card_le_card (sk_coverRowH_mono hH b)) _
  have he := coarseError_mono (q := q) (by positivity : (0 : ℝ) ≤ 2 * n) hS
  have hsum : (2 : ℝ) ^ coverRowS G C ord H b * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b ≤
      (2 : ℝ) ^ coverRowS G C ord H' b * ∑ j, (2 : ℝ) ^ coverRowExp G ς H' j b := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun j _ => ?_
    rw [coverRow_two_zpow_exp, coverRow_two_zpow_exp]
    unfold coverRowS
    rw [pow_add (2 : ℝ) (coverRowT G C ord b), pow_add (2 : ℝ) (coverRowT G C ord b)]
    have hm : (2 : ℝ) ^ (coverRowH H b).card * (if j ∈ coverRowH H b then (2 : ℝ)⁻¹ else 1) ≤
        2 ^ (coverRowH H' b).card * (if j ∈ coverRowH H' b then (2 : ℝ)⁻¹ else 1) :=
      sk_two_pow_ite_mono (sk_coverRowH_mono hH b) j
    have h0 : (0 : ℝ) ≤ 2 ^ coverRowT G C ord b * 2 ^ (rowsMg G ς j b + rowsCU G ς j b) := by
      positivity
    calc (2 : ℝ) ^ coverRowT G C ord b * 2 ^ (coverRowH H b).card *
          (2 ^ (rowsMg G ς j b + rowsCU G ς j b) * if j ∈ coverRowH H b then (2 : ℝ)⁻¹ else 1)
        = (2 ^ coverRowT G C ord b * 2 ^ (rowsMg G ς j b + rowsCU G ς j b)) *
            ((2 : ℝ) ^ (coverRowH H b).card * if j ∈ coverRowH H b then (2 : ℝ)⁻¹ else 1) := by
          ring
      _ ≤ (2 ^ coverRowT G C ord b * 2 ^ (rowsMg G ς j b + rowsCU G ς j b)) *
            ((2 : ℝ) ^ (coverRowH H' b).card * if j ∈ coverRowH H' b then (2 : ℝ)⁻¹ else 1) :=
          mul_le_mul_of_nonneg_left hm h0
      _ = _ := by ring
  have hr : (0 : ℝ) ≤ (Real.sqrt q)⁻¹ ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hsum hr
  nlinarith [this, he]

theorem sk_intNum_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (n : ℕ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (Cz : Finset U) (u : U) : 0 ≤ intNum G ς q n ord Fr Cz u := by
  unfold intNum
  have he := coarseError_nonneg (q := q) (Nat.cast_nonneg n) (intS G ord Fr u)
  have : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * 2 ^ intS G ord Fr u * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b :=
    mul_nonneg (by positivity) (sum_nonneg fun b _ => by positivity)
  linarith

theorem sk_coverNum_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (n : ℕ) (C : Finset U)
    (ord : U → ℕ) (H : Finset (U × U)) (b : U) :
    0 ≤ 1 + coarseError (coverRowS G C ord H b) q (2 * n) +
        (Real.sqrt q)⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b := by
  have he := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n) (coverRowS G C ord H b)
  have : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
      ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b :=
    mul_nonneg (by positivity) (sum_nonneg fun b _ => by positivity)
  linarith

/-- The vertex factors are nonnegative and nondecreasing in the free pairs, so `∏_v F_v`
(`recordFactor`) is nondecreasing in the free set (all count errors below one). -/
theorem sk_recordFactor_mono (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ}
    (he : ∀ i, coarseError (rowsDeg0 G i) q n < 1) {Fr Fr' : Finset (U × U)} (hFr : Fr ⊆ Fr')
    (V W Cx Cz : Finset U) (ordX ordZ : U → ℕ) :
    recordFactor G ς q n Fr V W Cx Cz ordX ordZ ≤ recordFactor G ς q n Fr' V W Cx Cz ordX ordZ := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : ∀ ord u, 0 < 1 - coarseError (ordT G ord u) q n := fun ord u => by
    have := (coarseError_mono hn0 (ordT_le_deg G ord u)).trans_lt (he u)
    linarith
  have hdenC : ∀ (C : Finset U) ord b, 0 < 1 - coarseError (coverRowT G C ord b) q n := by
    intro C ord b
    have := (coarseError_mono hn0 (coverRow_nbrCount_le G (coverRowEarlier C ord b) b)).trans_lt
      (he b)
    unfold coverRowT
    linarith
  have hIF : ∀ ord (A B : Finset (U × U)), A ⊆ B → ∀ (Cz' : Finset U) (S : Finset U),
      ∏ u ∈ S, intF G ς q n ord A Cz' u ≤ ∏ u ∈ S, intF G ς q n ord B Cz' u := by
    intro ord A B hAB Cz' S
    refine prod_le_prod₀ (fun u _ => div_nonneg (sk_intNum_nonneg G ς n ord A Cz' u)
      (hden ord u).le) (fun u _ => ?_)
    exact div_le_div_of_nonneg_right (sk_intNum_mono G ς n ord hAB Cz' u) (hden ord u).le
  have hCF : ∀ (C : Finset U) ord (A B : Finset (U × U)), A ⊆ B →
      ∏ b ∈ C, coverRowF G ς q n C ord A b ≤ ∏ b ∈ C, coverRowF G ς q n C ord B b := by
    intro C ord A B hAB
    refine prod_le_prod₀ (fun b _ => div_nonneg (sk_coverNum_nonneg G ς n C ord A b)
      (hdenC C ord b).le) (fun b _ => ?_)
    exact div_le_div_of_nonneg_right (sk_coverNum_mono G ς n C ord hAB b) (hdenC C ord b).le
  have hnn1 : ∀ ord (A : Finset (U × U)) (Cz' S : Finset U), 0 ≤ ∏ u ∈ S, intF G ς q n ord A Cz' u :=
    fun ord A Cz' S => prod_nonneg fun u _ =>
      div_nonneg (sk_intNum_nonneg G ς n ord A Cz' u) (hden ord u).le
  have hnn2 : ∀ (C : Finset U) ord (A : Finset (U × U)),
      0 ≤ ∏ b ∈ C, coverRowF G ς q n C ord A b :=
    fun C ord A => prod_nonneg fun b _ =>
      div_nonneg (sk_coverNum_nonneg G ς n C ord A b) (hdenC C ord b).le
  have hsw : Fr.image Prod.swap ⊆ Fr'.image Prod.swap := image_subset_image hFr
  unfold recordFactor
  refine mul_le_mul (mul_le_mul (mul_le_mul (hIF ordX Fr Fr' hFr Cz _)
    (hCF Cz ordZ _ _ (filter_subset_filter _ hFr)) (hnn2 _ _ _) (hnn1 _ _ _ _))
    (hIF ordZ _ _ hsw Cx _) (hnn1 _ _ _ _) (mul_nonneg (hnn1 _ _ _ _) (hnn2 _ _ _)))
    (hCF Cx ordX _ _ (filter_subset_filter _ hsw)) (hnn2 _ _ _)
    (mul_nonneg (mul_nonneg (hnn1 _ _ _ _) (hnn2 _ _ _)) (hnn1 _ _ _ _))

theorem sk_recordExp_mono (G : OrientedGraph U) {Fr Fr' : Finset (U × U)} (hFr : Fr ⊆ Fr')
    (V W : Finset U) (ordX ordZ : U → ℕ) :
    recordExp G Fr V W ordX ordZ ≤ recordExp G Fr' V W ordX ordZ := by
  unfold recordExp
  have h1 := card_le_card (filter_subset_filter (fun e : U × U => e.1 ∈ V) hFr)
  have h2 := card_le_card (filter_subset_filter (fun e : U × U => e.2 ∈ W) hFr)
  omega

end SkMono

section SkSoft

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] in
/-- **Step 1 with coefficients**: for any `g`, `∑_{S ∈ 𝒞(P, A)} ∏_{e ∈ S} g_e =
∏_{e ∈ P} g_e ∏_{e ∈ F} (1 + g_e)`. -/
theorem sk_sum_cls_eq (Ex P A : Finset (U × U)) (hP : P ⊆ Ex) (hPA : Disjoint P A)
    (g : U × U → ℝ) :
    ∑ S ∈ cls Ex P A, ∏ e ∈ S, g e = (∏ e ∈ P, g e) * ∏ e ∈ Ex \ (P ∪ A), (1 + g e) := by
  rw [prod_one_add, mul_sum]
  symm
  refine sum_nbij' (fun T => P ∪ T) (fun S => S \ P) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [mem_powerset] at hT
    rw [mem_cls]
    refine ⟨subset_union_left, fun e he => ?_⟩
    rcases mem_union.mp he with he | he
    · exact mem_sdiff.mpr ⟨hP he, disjoint_left.mp hPA he⟩
    · have := hT he
      simp only [mem_sdiff, mem_union, not_or] at this
      exact mem_sdiff.mpr ⟨this.1, this.2.2⟩
  · intro S hS
    rw [mem_cls] at hS
    rw [mem_powerset]
    intro e he
    simp only [mem_sdiff] at he
    have := hS.2 he.1
    simp only [mem_sdiff] at this
    simp only [mem_sdiff, mem_union, not_or]
    exact ⟨this.1, he.2, this.2⟩
  · intro T hT
    rw [mem_powerset] at hT
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, hn⟩
      · exact absurd h hn
      · exact h
    · intro h
      refine ⟨Or.inr h, fun hP' => ?_⟩
      have := hT h
      simp only [mem_sdiff, mem_union, not_or] at this
      exact this.2.1 hP'
  · intro S hS
    rw [mem_cls] at hS
    exact union_sdiff_of_subset hS.1
  · intro T hT
    simp only [mem_powerset] at hT
    have hdisj : Disjoint P T := by
      rw [disjoint_left]
      intro e heP heT
      have := hT heT
      simp only [mem_sdiff, mem_union, not_or] at this
      exact this.2.1 heP
    rw [prod_union hdisj]

/-- The soft class kernel `∑_{S ∈ 𝒞} D_S χ_S = ∏_{e ∈ P} D_e χ_e ∏_{e ∈ F} (1 + D_e χ_e)`
(`cor:soft-kernels`). -/
noncomputable def skSoftKer (ς : U → U → ℤ) (D : U × U → ℝ) (P Fr : Finset (U × U))
    (x x' : U → F) : ℝ :=
  (∏ e ∈ P, (D e * chiPair ς e x x')) * ∏ e ∈ Fr, (1 + D e * chiPair ς e x x')

/-- The signs flipped at the free pairs with a negative coefficient. -/
noncomputable def skFlip (ς : U → U → ℤ) (D : U × U → ℝ) (Fr : Finset (U × U)) : U → U → ℤ :=
  fun j k => if (j, k) ∈ Fr ∧ D (j, k) < 0 then -ς j k else ς j k

/-- The convex weights `w_T = ∏_{e ∈ T} |D_e| ∏_{e ∈ F \ T} (1 - |D_e|)`. -/
noncomputable def skW (D : U × U → ℝ) (Fr T : Finset (U × U)) : ℝ :=
  (∏ e ∈ T, |D e|) * ∏ e ∈ Fr \ T, (1 - |D e|)

omit [Fintype U] in
theorem skW_nonneg {D : U × U → ℝ} {Fr : Finset (U × U)} (hD : ∀ e ∈ Fr, |D e| ≤ 1)
    (T : Finset (U × U)) : 0 ≤ skW D Fr T :=
  mul_nonneg (prod_nonneg fun e _ => abs_nonneg _)
    (prod_nonneg fun e he => by linarith [hD e (mem_sdiff.mp he).1])

omit [Fintype U] in
theorem skW_sum (D : U × U → ℝ) (Fr : Finset (U × U)) : ∑ T ∈ Fr.powerset, skW D Fr T = 1 := by
  have h := prod_add (fun e => |D e|) (fun e => 1 - |D e|) Fr
  simp only [add_sub_cancel, prod_const_one] at h
  unfold skW
  rw [← h]

omit [Fintype U] in
theorem skFlip_ne_zero_iff (ς : U → U → ℤ) (D : U × U → ℝ) (Fr : Finset (U × U)) (j k : U) :
    skFlip ς D Fr j k ≠ 0 ↔ ς j k ≠ 0 := by
  unfold skFlip
  split_ifs <;> simp

omit [Fintype U] in
theorem skFlip_values (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (D : U × U → ℝ) (Fr : Finset (U × U)) (j k : U) :
    skFlip ς D Fr j k = 0 ∨ skFlip ς D Fr j k = 1 ∨ skFlip ς D Fr j k = -1 := by
  unfold skFlip
  split_ifs
  · rcases hς j k with h | h | h <;> simp [h]
  · exact hς j k

omit [Fintype U] in
theorem skFlip_of_not_mem (ς : U → U → ℤ) (D : U × U → ℝ) {Fr : Finset (U × U)} {e : U × U}
    (he : e ∉ Fr) (x x' : U → F) : chiPair (skFlip ς D Fr) e x x' = chiPair ς e x x' := by
  unfold chiPair skFlip
  simp only [Prod.mk.eta, he, false_and, ↓reduceIte]

omit [Fintype U] in
/-- `1 + D χ = (1 - |D|) + |D| (1 + χ')`, `χ'` with the sign flipped when `D < 0` (this needs
`χ(-1) = -1` at a flipped pair). -/
theorem sk_flip_identity (ς : U → U → ℤ) (D : U × U → ℝ) {Fr : Finset (U × U)} {e : U × U}
    (he : e ∈ Fr) (hneg : D e < 0 → quadraticChar F (-1) = -1) (x x' : U → F) :
    1 + D e * chiPair ς e x x' =
      |D e| * (1 + chiPair (skFlip ς D Fr) e x x') + (1 - |D e|) := by
  by_cases hD : D e < 0
  · have hm := hneg hD
    have hflip : chiPair (skFlip ς D Fr) e x x' = -chiPair ς e x x' := by
      unfold chiPair skFlip
      simp only [Prod.mk.eta, he, hD, and_self, ↓reduceIte, Int.cast_neg]
      have : (-(ς e.1 e.2 : F)) * (x' e.2 - x e.1) = (-1) * ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) := by
        ring
      rw [this, map_mul, hm]
      push_cast
      ring
    rw [hflip, abs_of_neg hD]
    ring
  · push Not at hD
    have hflip : chiPair (skFlip ς D Fr) e x x' = chiPair ς e x x' := by
      unfold chiPair skFlip
      have : ¬ (D e < 0) := not_lt.mpr hD
      simp only [Prod.mk.eta, this, and_false, ↓reduceIte]
    rw [hflip, abs_of_nonneg hD]
    ring

omit [Fintype U] in
/-- **The convex decomposition of the soft class kernel**:
`K^D_𝒞 = (∏_{e ∈ P} D_e) ∑_{T ⊆ F} w_T K^{ς'}_{𝒞(P, A ∪ (F \ T))}`, the signs `ς'` flipped at the
free pairs with negative coefficient. -/
theorem sk_softKer_expand (ς : U → U → ℤ) (D : U × U → ℝ) (P Fr : Finset (U × U))
    (hPFr : Disjoint P Fr) (hneg : ∀ e ∈ Fr, D e < 0 → quadraticChar F (-1) = -1)
    (x x' : U → F) :
    skSoftKer ς D P Fr x x' = (∏ e ∈ P, D e) *
      ∑ T ∈ Fr.powerset, skW D Fr T * classKer (skFlip ς D Fr) P T x x' := by
  unfold skSoftKer classKer skW
  rw [prod_mul_distrib]
  have hP : ∏ e ∈ P, chiPair ς e x x' = ∏ e ∈ P, chiPair (skFlip ς D Fr) e x x' :=
    prod_congr rfl fun e he => (skFlip_of_not_mem ς D (disjoint_left.mp hPFr he) x x').symm
  have hF : ∏ e ∈ Fr, (1 + D e * chiPair ς e x x') =
      ∏ e ∈ Fr, (|D e| * (1 + chiPair (skFlip ς D Fr) e x x') + (1 - |D e|)) :=
    prod_congr rfl fun e he => sk_flip_identity ς D he (hneg e he) x x'
  rw [hP, hF, prod_add, mul_assoc]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun T _ => ?_
  rw [prod_mul_distrib]
  ring

omit [Fintype U] in
theorem sk_rectKer_flip (ς : U → U → ℤ) (D : U × U → ℝ) (P Fr : Finset (U × U))
    (hPFr : Disjoint P Fr) (V W : Finset U) :
    rectKer (skFlip ς D Fr) P V W = (rectKer ς P V W : (U → F) → (U → F) → ℝ) := by
  funext v w
  unfold rectKer
  exact prod_congr rfl fun e he =>
    skFlip_of_not_mem ς D (disjoint_left.mp hPFr (mem_filter.mp he).1) v w

theorem sk_recordFactor_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ}
    (he : ∀ i, coarseError (rowsDeg0 G i) q n < 1) (Fr : Finset (U × U))
    (V W Cx Cz : Finset U) (ordX ordZ : U → ℕ) :
    0 ≤ recordFactor G ς q n Fr V W Cx Cz ordX ordZ := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : ∀ ord u, 0 ≤ 1 - coarseError (ordT G ord u) q n := fun ord u => by
    have := (coarseError_mono hn0 (ordT_le_deg G ord u)).trans_lt (he u)
    linarith
  have hdenC : ∀ (C : Finset U) ord b, 0 ≤ 1 - coarseError (coverRowT G C ord b) q n := by
    intro C ord b
    have := (coarseError_mono hn0 (coverRow_nbrCount_le G (coverRowEarlier C ord b) b)).trans_lt
      (he b)
    unfold coverRowT
    linarith
  unfold recordFactor intF coverRowF
  refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
  · exact prod_nonneg fun u _ => div_nonneg (sk_intNum_nonneg G ς n _ _ _ u) (hden _ u)
  · exact prod_nonneg fun b _ => div_nonneg (sk_coverNum_nonneg G ς n _ _ _ b) (hdenC _ _ b)
  · exact prod_nonneg fun u _ => div_nonneg (sk_intNum_nonneg G ς n _ _ _ u) (hden _ u)
  · exact prod_nonneg fun b _ => div_nonneg (sk_coverNum_nonneg G ς n _ _ _ b) (hdenC _ _ b)

/-- The bilinear sum of the soft kernel is the weighted sum of the Boolean sub-class sums. -/
theorem sk_soft_sum_eq (G : OrientedGraph U) (ς : U → U → ℤ) (D : U × U → ℝ)
    (P Fr : Finset (U × U)) (hPFr : Disjoint P Fr)
    (hneg : ∀ e ∈ Fr, D e < 0 → quadraticChar F (-1) = -1) (f h : (U → F) → ℝ) :
    ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * skSoftKer ς D P Fr x x' * h x' =
      (∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset, skW D Fr T *
        ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
          f x * classKer (skFlip ς D Fr) P T x x' * h x' := by
  simp only [sk_softKer_expand ς D P Fr hPFr hneg]
  calc ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
        f x * ((∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset,
          skW D Fr T * classKer (skFlip ς D Fr) P T x x') * h x'
      = ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, ∑ T ∈ Fr.powerset,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlip ς D Fr) P T x x' * h x')) := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
        rw [mul_sum, mul_sum, sum_mul]
        exact sum_congr rfl fun T _ => by ring
    _ = ∑ x ∈ injLabellings F G, ∑ T ∈ Fr.powerset, ∑ x' ∈ injLabellings F G,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlip ς D Fr) P T x x' * h x')) :=
        sum_congr rfl fun x _ => sum_comm
    _ = ∑ T ∈ Fr.powerset, ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlip ς D Fr) P T x x' * h x')) := sum_comm
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun T _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum, mul_sum]

end SkSoft

section SkMain

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `sk_grouped_sum_le` with the bound written with `recordExp` and `recordFactor`. -/
theorem sk_grouped_sum_le' (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0) {n : ℕ}
    (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ}
    (V W Cx Cz : Finset U) (hVk : V.card = k) (hWk : W.card = k)
    (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * classKer ς P Fr x x' * h x') /
        ((injLabellings F G).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G Fr V W ordX ordZ *
          recordFactor G ς (Fintype.card F) n Fr V W Cx Cz ordX ordZ) / (1 - ehat) ^ k *
        Real.sqrt ((∑ x ∈ injLabellings F G, f x ^ 2) / (injLabellings F G).card) *
        Real.sqrt ((∑ x ∈ injLabellings F G, h x ^ 2) / (injLabellings F G).card) :=
  sk_grouped_sum_le hW G ς hς hsym hn hehat hehat1 P Fr hFrς V W Cx Cz hVk hWk hVC hWC hP hFr
    ordX ordZ hordX hordZ hX0 hZ0 hsegX hsegZ hcker hker f h

/-- The bound of `lem:matching:extractionk` is nondecreasing in the free set. -/
theorem sk_bound_mono (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} {n : ℕ}
    (he : ∀ i, coarseError (rowsDeg0 G i) q n < 1) {T Fr : Finset (U × U)} (hT : T ⊆ Fr)
    (V W Cx Cz : Finset U) (ordX ordZ : U → ℕ) :
    Real.sqrt (2 ^ recordExp G T V W ordX ordZ * recordFactor G ς q n T V W Cx Cz ordX ordZ) ≤
      Real.sqrt (2 ^ recordExp G Fr V W ordX ordZ *
        recordFactor G ς q n Fr V W Cx Cz ordX ordZ) := by
  refine Real.sqrt_le_sqrt (mul_le_mul ?_ (sk_recordFactor_mono G ς he hT V W Cx Cz ordX ordZ)
    (sk_recordFactor_nonneg G ς he T V W Cx Cz ordX ordZ) (by positivity))
  exact pow_le_pow_right₀ (by norm_num) (sk_recordExp_mono G hT V W ordX ordZ)

/-- **`cor:soft-kernels`(a), sum form.** The soft class kernel `K^D_𝒞 = ∑_{S ∈ 𝒞} D_S χ_S`
(`skSoftKer`), `|D_e| ≤ 1`, satisfies the bound of `lem:matching:extractionk` for the Boolean
class (the right side of `grouped_extraction_sum_le`), provided `χ(-1) = -1` whenever a free pair
has a negative coefficient (`hneg`; no condition when `D ≥ 0` on the free pairs). -/
theorem sk_soft_sum_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0) {n : ℕ}
    (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (P Fr : Finset (U × U)) (hPFr : Disjoint P Fr) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ}
    (V W Cx Cz : Finset U) (hVk : V.card = k) (hWk : W.card = k)
    (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (D : U × U → ℝ) (hDP : ∀ e ∈ P, |D e| ≤ 1) (hDF : ∀ e ∈ Fr, |D e| ≤ 1)
    (hneg : ∀ e ∈ Fr, D e < 0 → quadraticChar F (-1) = -1)
    (f h : (U → F) → ℝ) :
    |(∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * skSoftKer ς D P Fr x x' * h x') /
        ((injLabellings F G).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G Fr V W ordX ordZ *
          recordFactor G ς (Fintype.card F) n Fr V W Cx Cz ordX ordZ) / (1 - ehat) ^ k *
        Real.sqrt ((∑ x ∈ injLabellings F G, f x ^ 2) / (injLabellings F G).card) *
        Real.sqrt ((∑ x ∈ injLabellings F G, h x ^ 2) / (injLabellings F G).card) := by
  rw [sk_soft_sum_eq G ς D P Fr hPFr hneg f h]
  have hsupp : ∀ j k, skFlip ς D Fr j k ≠ 0 ↔ ς j k ≠ 0 := skFlip_ne_zero_iff ς D Fr
  have hsym' : ∀ j k, skFlip ς D Fr j k ≠ 0 ↔ skFlip ς D Fr k j ≠ 0 := fun j k => by
    rw [hsupp, hsupp]
    exact hsym j k
  have hker' : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W)
      (rectKer (skFlip ς D Fr) P V W) (cker * Real.sqrt (Fintype.card F) ^ k) := by
    rw [sk_rectKer_flip ς D P Fr hPFr V W]
    exact hker
  have he : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n < 1 := fun i =>
    lt_of_le_of_lt (hehat i) hehat1
  have h1e : 0 < 1 - ehat := by linarith
  have hc : |∏ e ∈ P, D e| ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one₀ (fun e _ => abs_nonneg _) (fun e he => hDP e he)
  have hw0 : ∀ T ∈ Fr.powerset, 0 ≤ skW D Fr T := fun T _ => skW_nonneg hDF T
  -- the bound for each sub-class, at most the bound for the class
  have hT : ∀ T ∈ Fr.powerset,
      |(∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
          f x * classKer (skFlip ς D Fr) P T x x' * h x') / ((injLabellings F G).card : ℝ) ^ 2| ≤
        cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          Real.sqrt (2 ^ recordExp G Fr V W ordX ordZ *
            recordFactor G ς (Fintype.card F) n Fr V W Cx Cz ordX ordZ) / (1 - ehat) ^ k *
          Real.sqrt ((∑ x ∈ injLabellings F G, f x ^ 2) / (injLabellings F G).card) *
          Real.sqrt ((∑ x ∈ injLabellings F G, h x ^ 2) / (injLabellings F G).card) := by
    intro T hT
    rw [mem_powerset] at hT
    have hb := sk_grouped_sum_le' hW G (skFlip ς D Fr) (skFlip_values ς hς D Fr) hsym' hn hehat
      hehat1 P T (fun e he => (hsupp e.1 e.2).mpr (hFrς e (hT he))) V W Cx Cz hVk hWk hVC hWC
      hP (fun e he => hFr e (hT he)) ordX ordZ hordX hordZ hX0 hZ0 hsegX hsegZ hcker hker' f h
    rw [sk_recordFactor_congr G hsupp] at hb
    refine hb.trans ?_
    have hm := sk_bound_mono G ς he hT V W Cx Cz ordX ordZ
    have hX : 0 ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k := by positivity
    gcongr
  calc |((∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset, skW D Fr T *
          (∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
            f x * classKer (skFlip ς D Fr) P T x x' * h x')) / ((injLabellings F G).card : ℝ) ^ 2|
      = |∏ e ∈ P, D e| * |∑ T ∈ Fr.powerset, skW D Fr T *
          ((∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
            f x * classKer (skFlip ς D Fr) P T x x' * h x') /
              ((injLabellings F G).card : ℝ) ^ 2)| := by
        rw [mul_div_assoc, abs_mul, sum_div]
        congr 2
        exact sum_congr rfl fun T _ => by ring
    _ ≤ 1 * ∑ T ∈ Fr.powerset, skW D Fr T *
          |(∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
            f x * classKer (skFlip ς D Fr) P T x x' * h x') /
              ((injLabellings F G).card : ℝ) ^ 2| := by
        refine mul_le_mul hc ?_ (abs_nonneg _) zero_le_one
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact sum_congr rfl fun T hT => by rw [abs_mul, abs_of_nonneg (hw0 T hT)]
    _ ≤ 1 * ∑ T ∈ Fr.powerset, skW D Fr T *
          (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
            Real.sqrt (2 ^ recordExp G Fr V W ordX ordZ *
              recordFactor G ς (Fintype.card F) n Fr V W Cx Cz ordX ordZ) / (1 - ehat) ^ k *
            Real.sqrt ((∑ x ∈ injLabellings F G, f x ^ 2) / (injLabellings F G).card) *
            Real.sqrt ((∑ x ∈ injLabellings F G, h x ^ 2) / (injLabellings F G).card)) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun T hT' => ?_) zero_le_one
        exact mul_le_mul_of_nonneg_left (hT T hT') (hw0 T hT')
    _ = _ := by rw [← sum_mul, skW_sum, one_mul, one_mul]

end SkMain

section SkPaper

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The soft class form: `∑_{S ∈ 𝒞} D_S ⟨f, T_S h⟩_μ = |𝓘⁺|^{-2} ∑_{x,x'} f(x) K^D_𝒞(x,x') h(x')`. -/
theorem sk_softForm_eq (G : OrientedGraph U) (hne : (injLabellings F G).Nonempty)
    (ς : U → U → ℤ) (D : U × U → ℝ) (Ex P A : Finset (U × U)) (hP : P ⊆ Ex)
    (hPA : Disjoint P A) (f h : (U → F) → ℝ) :
    (graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x x')) * h x')) =
      (∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
        f x * skSoftKer ς D P (Ex \ (P ∪ A)) x x' * h x') /
          ((injLabellings F G).card : ℝ) ^ 2 := by
  have hN : ((injLabellings F G).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
  have hK : ∀ x x' : U → F, ∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x x') =
      skSoftKer ς D P (Ex \ (P ∪ A)) x x' := fun x x' =>
    sk_sum_cls_eq Ex P A hP hPA (fun e => D e * chiPair ς e x x')
  rw [coverRow_expect_graphLaw]
  simp_rw [coverRow_expect_graphLaw, hK]
  rw [pow_two, ← div_div]
  congr 1
  rw [eq_div_iff hN, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  have e : f x * ((∑ x' ∈ injLabellings F G, skSoftKer ς D P (Ex \ (P ∪ A)) x x' * h x') /
      ((injLabellings F G).card : ℝ)) * ((injLabellings F G).card : ℝ) =
      f x * ∑ x' ∈ injLabellings F G, skSoftKer ς D P (Ex \ (P ∪ A)) x x' * h x' := by
    field_simp
  rw [e, mul_sum]
  exact sum_congr rfl fun x' _ => by ring

/-- **`cor:soft-kernels`(a) for `lem:matching:extractionk`.** Let `D_e ∈ [-1, 1]`. Under the
hypotheses of `grouped_extraction`, the soft class operator `T^D_𝒞 = ∑_{S ∈ 𝒞} D_S T_S`
(`D_S = ∏_{e ∈ S} D_e`) satisfies the same bound,
`|∑_{S ∈ 𝒞} D_S ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex(𝒞)/2} (∏_v F_v)^{1/2} (1 - ê)^{-k} ‖f‖_μ ‖h‖_μ`,
provided `χ(-1) = -1` (`p ≡ 3 (mod 4)`) whenever a free pair has a negative coefficient (`hneg`;
there is no condition when `D ≥ 0` on the free pairs, see `sk_soft_extraction_nonneg`). The
present factors `D_e χ_e` only contribute the constant `∏_{e ∈ P} D_e` of modulus at most one;
a free factor is `1 + D_e χ_e = (1 - |D_e|) + |D_e| (1 ± χ_e)`, a convex combination over the
sub-classes `𝒞(P, A ∪ (F \ T))` of Boolean kernels (with the sign of `ς_e` flipped where
`D_e < 0`, `1 - χ_e = 1 + χ(-ς_e ⋯)`), whose bounds are at most the bound of `𝒞`
(`sk_bound_mono`). -/
theorem sk_soft_extraction (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w)) (rectKer ς P (witV w) (witW w))
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1)
    (hneg : ∀ e ∈ Ex \ (P ∪ A), D e < 0 → quadraticChar F (-1) = -1)
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x x')) * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
        (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨hP, -, hPA⟩ := hcls
  rw [sk_softForm_eq G hne ς D Ex P A hP hPA, coverRow_expect_graphLaw, coverRow_expect_graphLaw]
  set Fr := Ex \ (P ∪ A) with hFr
  have hrect : ∀ e : U × U, e.1 ∈ witV w ∧ e.2 ∈ witW w ↔
      (∃ i, (w i).1 = e.1) ∧ ∃ l, (w l).2 = e.2 := by
    intro e
    simp [witV, witW]
  have hFrEx : ∀ e ∈ Fr, e ∈ Ex := fun e he => (mem_sdiff.mp he).1
  have hP' : ∀ e ∈ P, (e.1 ∈ witV w ∧ e.2 ∈ witW w) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    by_cases hr : e.1 ∈ witV w ∧ e.2 ∈ witW w
    · exact Or.inl hr
    · exact Or.inr (hcov.cover e (mem_union_left _ he) (by rwa [← hrect]))
  have hFr' : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (hFrEx e he) hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hVC : ∀ u ∈ witV w, u ∉ Cx := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.fst_not_mem i
  have hWC : ∀ u ∈ witW w, u ∉ Cz := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.snd_not_mem i
  have hVk : (witV w).card = k := by
    unfold witV
    rw [card_image_of_injective _ hw.injective_fst, card_univ, Fintype.card_fin]
  have hWk : (witW w).card = k := by
    unfold witW
    rw [card_image_of_injective _ hw.injective_snd, card_univ, Fintype.card_fin]
  have hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0 := fun j k => by
    rw [hanti j k, neg_ne_zero]
  have hPFr : Disjoint P Fr := by
    rw [disjoint_left]
    intro e heP heF
    exact (mem_sdiff.mp heF).2 (mem_union_left _ heP)
  exact sk_soft_sum_le hW G ς hς hsym hn hehat hehat1 P Fr hPFr
    (fun e he => hEx e (hFrEx e he)) (witV w) (witW w) Cx Cz hVk hWk hVC hWC hP' hFr' ordX ordZ
    hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker D (fun e _ => hD e) (fun e _ => hD e) hneg f h


/-- **`cor:soft-kernels`(a), coefficients nonnegative on the free pairs** (any field, no condition
on `χ(-1)`): the bound of `grouped_extraction` for `T^D_𝒞` with `D_e ∈ [-1, 1]` on the present
pairs and `D_e ∈ [0, 1]` on the free pairs. -/
theorem sk_soft_extraction_nonneg (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w)) (rectKer ς P (witV w) (witW w))
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1)
    (hD0 : ∀ e ∈ Ex \ (P ∪ A), 0 ≤ D e)
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x x')) * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
        (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨hP, -, hPA⟩ := hcls
  rw [sk_softForm_eq G hne ς D Ex P A hP hPA, coverRow_expect_graphLaw, coverRow_expect_graphLaw]
  set Fr := Ex \ (P ∪ A) with hFr
  have hrect : ∀ e : U × U, e.1 ∈ witV w ∧ e.2 ∈ witW w ↔
      (∃ i, (w i).1 = e.1) ∧ ∃ l, (w l).2 = e.2 := by
    intro e
    simp [witV, witW]
  have hFrEx : ∀ e ∈ Fr, e ∈ Ex := fun e he => (mem_sdiff.mp he).1
  have hP' : ∀ e ∈ P, (e.1 ∈ witV w ∧ e.2 ∈ witW w) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    by_cases hr : e.1 ∈ witV w ∧ e.2 ∈ witW w
    · exact Or.inl hr
    · exact Or.inr (hcov.cover e (mem_union_left _ he) (by rwa [← hrect]))
  have hFr' : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (hFrEx e he) hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hVC : ∀ u ∈ witV w, u ∉ Cx := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.fst_not_mem i
  have hWC : ∀ u ∈ witW w, u ∉ Cz := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.snd_not_mem i
  have hVk : (witV w).card = k := by
    unfold witV
    rw [card_image_of_injective _ hw.injective_fst, card_univ, Fintype.card_fin]
  have hWk : (witW w).card = k := by
    unfold witW
    rw [card_image_of_injective _ hw.injective_snd, card_univ, Fintype.card_fin]
  have hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0 := fun j k => by
    rw [hanti j k, neg_ne_zero]
  have hPFr : Disjoint P Fr := by
    rw [disjoint_left]
    intro e heP heF
    exact (mem_sdiff.mp heF).2 (mem_union_left _ heP)
  exact sk_soft_sum_le hW G ς hς hsym hn hehat hehat1 P Fr hPFr
    (fun e he => hEx e (hFrEx e he)) (witV w) (witW w) Cx Cz hVk hWk hVC hWC hP' hFr' ordX ordZ
    hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker D (fun e _ => hD e) (fun e _ => hD e)
    (fun e he hlt => absurd (hD0 e he) (not_le.mpr hlt)) f h


end SkPaper

end Sarkozy.ExtractionK
