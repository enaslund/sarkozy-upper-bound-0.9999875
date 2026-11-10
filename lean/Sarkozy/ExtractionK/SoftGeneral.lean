module

public import Sarkozy.ExtractionK.SoftCore

@[expose] public section

/-!
# Soft cross factors with negative coefficients (`cor:soft-kernels`(a), all `D_e ∈ [-1, 1]`)

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(a), without the restriction of
`SoftCore.lean` (`χ(-1) = -1` at the free pairs with `D_e < 0`). A free factor with `D_e < 0` is
`1 + D_e χ_e = (1 - |D_e|) + |D_e| (1 - χ_e)` and `1 - χ(ς_e t) = 1 + χ(ν ς_e t)` for a non-square
`ν`; the flipped signs `ν ς_e` (`skFlipN`) are nonzero in `F` but no longer in `{0, ±1}`. So the
Boolean chain of `lem:matching:extractionk` is re-proved for cross signs that are only nonzero in
`F` on their support (hypothesis `ς_{jk} ≠ 0 → (ς_{jk} : F) ≠ 0` in place of `ς ∈ {0, ±1}`); the
proofs are those of `Extraction/CoverRows.lean` (`coverRows_oneVertex`), `PartialLabellings.lean`,
`IntegratedVertex.lean`, `OneSide.lean` and `SoftCore.lean`, where the sign hypothesis is used only
to get `χ(ς_{ab}) = ±1` for the signs of `lem:extraction-merged-count`:

* `sk_coverRows_oneVertex_g` (`eq:extraction:onevertex`), `sk_partLab_coverRows_le_g` (Steps 2–5
  of `lem:extraction-rows`), `sk_integrated_oneVertex_g`, `sk_integrated_extSum_le_g`
  (`eq:extraction:mbound`), `sk_alpha_sq_le_g`, `sk_one_side_le_g`, `sk_other_side_le_g`,
  `sk_grouped_count_g`, `sk_grouped_sum_le_g` (`lem:matching:extractionk`, general nonzero signs
  with a symmetric support);
* `skFlipN`, `sk_flipN_identity`, `sk_softKer_expandN`, `sk_soft_sum_eqN`: the convex decomposition
  with the signs multiplied by `ν`;
* `sk_soft_sum_le_g` and **`sk_soft_extraction_g`**: `cor:soft-kernels`(a) for
  `lem:matching:extractionk` for all `D_e ∈ [-1, 1]`, given an integer `ν` with `χ(ν) = -1`;
  `sk_exists_nonsquare_int`: such a `ν` exists for `𝔽_p`, `p` odd.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SkGen

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype F] [DecidableEq F] [Fintype U] [DecidableEq U] in
theorem skT_castF (ς : U → U → ℤ) (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (j k : U) :
    skT ς j k ≠ 0 → ((skT ς j k : ℤ) : F) ≠ 0 := by
  unfold skT
  intro h
  rw [neg_ne_zero] at h
  push_cast
  exact neg_ne_zero.mpr (hς k j h)

/-- **`eq:extraction:onevertex`** (Step 4 of `lem:extraction-rows`). Fix `b` and labels `x'` of
the vertices of `C` earlier than `b` (feasible there), and let `Adm_b = Φ_b(x')` be the labels
distinct from the earlier ones satisfying the `t_b` constraints of `G⁺` with the earlier
neighbours of `b`. Then
`∑_{y ∈ Adm_b} ω̂_b(y) 2^{-μ_b} ≤ q 2^{-t_b}(1 + e_{s_b}(q, 2n) + r² 2^{s_b}
∑_{j ∈ U⁺} 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]})`. The labels `y ∉ x(U⁺)` are counted by
`lem:extraction-merged-count` (`merged_count_le_fintype'`), with the `μ_b` merges; the labels
`y = x_j` by `coverRow_omegaHat_at_le`. `WeilBound F` is Weil's theorem (literature input). -/
theorem sk_coverRows_oneVertex_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (C : Finset U) (ord : U → ℕ)
    (H : Finset (U × U)) (hHς : ∀ e ∈ H, ς e.1 e.2 ≠ 0) (x : U → F) (hx : Function.Injective x)
    (n : ℕ) (b : U) (x' : U → F) (hx' : Feasible F G (coverRowEarlier C ord b) x') :
    ∑ y ∈ vertexAdmissible G (coverRowEarlier C ord b) x' b,
        coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ coverRowMerges G C ord H x x' b)⁻¹ ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
        (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n) +
          (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
            ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) := by
  set A := coverRowEarlier C ord b with hA
  set Hb := coverRowH H b with hHb
  set μ := coverRowMerges G C ord H x x' b with hμ
  set X : Finset F := univ.image x with hX
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hμinv0 : (0 : ℝ) ≤ ((2 : ℝ) ^ μ)⁻¹ := by positivity
  have hμinv1 : ((2 : ℝ) ^ μ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [← sum_filter_add_sum_filter_not (vertexAdmissible G A x' b) (fun y => y ∈ X)]
  -- the labels `x_j`
  have hii : ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∈ X),
      coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹ ≤
        ∑ j, 2 ^ Hb.card * (2 : ℝ) ^ coverRowExp G ς H j b := by
    calc ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∈ X),
          coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹
        ≤ ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∈ X),
            coverRowOmegaHat G ς H x b y :=
          sum_le_sum fun y _ => mul_le_of_le_one_right (coverRow_omegaHat_nonneg G ς H x b y)
            hμinv1
      _ ≤ ∑ y ∈ X, coverRowOmegaHat G ς H x b y :=
          sum_le_sum_of_subset_of_nonneg (fun y hy => (mem_filter.mp hy).2)
            (fun y _ _ => coverRow_omegaHat_nonneg G ς H x b y)
      _ = ∑ j, coverRowOmegaHat G ς H x b (x j) := sum_image fun j _ k _ h => hx h
      _ ≤ _ := sum_le_sum fun j _ => coverRow_omegaHat_at_le G ς H x hx b j
  -- the other labels: `lem:extraction-merged-count`
  set NA := A.filter (fun u => (u, b) ∈ G.E ∨ (b, u) ∈ G.E) with hNA
  let β : NA → F := fun u => x' u
  have hβ : Function.Injective β := fun u w h =>
    Subtype.ext (hx'.1 u (mem_filter.mp u.2).1 w (mem_filter.mp w.2).1 h)
  let γ : Hb → F := fun a => x a
  have hγ : Function.Injective γ := fun a a' h => Subtype.ext (hx h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : NA → ℤ := fun u => if (u.1, b) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ u, s u = 1 ∨ s u = -1 := fun u => by
    simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact hm1
  let s' : Hb → ℤ := fun a => quadraticChar F (ς a.1 b : F)
  have hs' : ∀ a, s' a = 1 ∨ s' a = -1 := fun a => by
    have ha : ς a.1 b ≠ 0 := hHς (a.1, b) (by simpa [hHb, coverRowH] using a.2)
    exact quadraticChar_dichotomy (hς a.1 b ha)
  set 𝒳 : Finset F := A.image x' ∪ X with h𝒳
  have hβX : ∀ u, β u ∈ 𝒳 := fun u =>
    mem_union_left _ (mem_image_of_mem x' (mem_filter.mp u.2).1)
  have hγX : ∀ a, γ a ∈ 𝒳 := fun a => mem_union_right _ (mem_image_of_mem x (mem_univ _))
  have hmc := merged_count_le_fintype' hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX
    (n' := 2 * (n : ℝ)) (by positivity)
  have hset : (vertexAdmissible G A x' b).filter (fun y => y ∉ X) =
      univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i) := by
    ext c
    simp only [vertexAdmissible, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨hc, hin, hout⟩, hcX⟩
      refine ⟨⟨hc, hcX⟩, fun u => ?_⟩
      have hu := (mem_filter.mp u.2).2
      simp only [s, β]
      split_ifs with h
      · exact hin u (mem_filter.mp u.2).1 h
      · have hvu : (b, u.1) ∈ G.E := hu.resolve_left h
        have h1 := hout u (mem_filter.mp u.2).1 hvu
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul] at h1
        rcases hm1 with h' | h' <;> rw [h'] at h1 ⊢ <;> linarith
    · rintro ⟨⟨hc, hcX⟩, hall⟩
      refine ⟨⟨hc, fun u hu he => ?_, fun u hu he => ?_⟩, hcX⟩
      · have hmem : u ∈ NA := mem_filter.mpr ⟨hu, Or.inl he⟩
        have := hall ⟨u, hmem⟩
        simpa [s, β, he] using this
      · have hmem : u ∈ NA := mem_filter.mpr ⟨hu, Or.inr he⟩
        have hnot : (u, b) ∉ G.E := G.oriented b u he
        have h1 := hall ⟨u, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hsummand : ∀ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
      coverRowOmegaHat G ς H x b y = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l)) := by
    intro y hy
    have hyX : y ∉ X := fun h => (mem_filter.mp hy).2.1 (mem_union_right _ h)
    have hne : ∀ i, y ≠ x i := fun i h => hyX (h ▸ mem_image_of_mem x (mem_univ i))
    unfold coverRowOmegaHat coverRowOmega coverRowMgAt
    simp only [hne, ↓reduceIte, sum_const_zero, pow_zero, mul_one]
    rw [← prod_coe_sort Hb]
    refine prod_congr rfl fun a _ => ?_
    simp only [s', γ, map_mul, Int.cast_mul]
  have hcardι : Fintype.card NA = coverRowT G C ord b := by
    rw [Fintype.card_coe]
    rfl
  have hcardκ : Fintype.card Hb = Hb.card := Fintype.card_coe _
  have hmerge : mergedCount β γ = μ := by
    unfold mergedCount
    calc (univ.filter fun il : NA × Hb => β il.1 = γ il.2).card
        = ∑ il : NA × Hb, if β il.1 = γ il.2 then 1 else 0 := card_filter _ _
      _ = ∑ u : NA, ∑ a : Hb, if β u = γ a then 1 else 0 := Fintype.sum_prod_type _
      _ = ∑ u : NA, ∑ a ∈ Hb, if x' u = x a then 1 else 0 :=
          sum_congr rfl fun u _ => sum_coe_sort Hb (fun a => if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, ∑ a ∈ Hb, if x' u = x a then 1 else 0 :=
          sum_coe_sort NA (fun u => ∑ a ∈ Hb, if x' u = x a then 1 else 0)
      _ = μ := rfl
  have hS : coverRowS G C ord H b = coverRowT G C ord b + Hb.card := rfl
  have hi : ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∉ X),
      coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹ ≤
        Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
          (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n)) := by
    rw [← sum_mul, hset, sum_congr rfl hsummand]
    rw [hcardι, hcardκ, hmerge, ← hS] at hmc
    calc (∑ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
          ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l))) * ((2 : ℝ) ^ μ)⁻¹
        ≤ (Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b * 2 ^ μ *
            (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n))) *
            ((2 : ℝ) ^ μ)⁻¹ := mul_le_mul_of_nonneg_right hmc hμinv0
      _ = _ := by field_simp
  have hid : (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
      ((Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
        ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) =
      ∑ j, 2 ^ Hb.card * (2 : ℝ) ^ coverRowExp G ς H j b := by
    rw [coverRow_r_sq hq0, ← mul_sum, hS, pow_add]
    have h2 : (2 : ℝ)⁻¹ ^ coverRowT G C ord b * 2 ^ coverRowT G C ord b = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
    calc (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
          ((Fintype.card F : ℝ)⁻¹ * (2 ^ coverRowT G C ord b * 2 ^ Hb.card) *
            ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b)
        = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹) *
            ((2 : ℝ)⁻¹ ^ coverRowT G C ord b * 2 ^ coverRowT G C ord b) *
            (2 ^ Hb.card * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hq0.ne', h2, one_mul, one_mul]
  calc ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∈ X),
        coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹ +
      ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∉ X),
        coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹
      ≤ ∑ j, 2 ^ Hb.card * (2 : ℝ) ^ coverRowExp G ς H j b +
          Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
            (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n)) :=
        add_le_add hii hi
    _ = _ := by rw [← hid]; ring

/-- **Steps 2–5 of `lem:extraction-rows`, summed over the labellings of `C`** (the form used in
Step 7 of `lem:matching:extractionk`, without the marginal comparison of Step 1). Let `C ⊆ U⁺` be
ordered by `ord` (injective on `C`), `x` injective and `H ⊆ {(a, b) ∈ E_× : b ∈ C}`. Then
`∑_{c' ∈ Inj(G⁺[C])} ∏_{(a,b) ∈ H} (1 + χ(ς_{ab}(c'_b - x_a))) 2^{κ_C(x, c')} ≤
∏_{b ∈ C} q 2^{-t_b} (1 + e_{s_b}(q, 2n) + r² 2^{s_b} ∑_{j ∈ U⁺} 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]})`
for every `n`; the factor of `b` is the numerator of `F_b(H)` times `q 2^{-t_b}`. Proof: Step 3
(`coverRow_integrand_le`), Step 4 (`sk_coverRows_oneVertex_g`, `eq:extraction:onevertex`) and Step 5
(`partLab_seq_upper`). `WeilBound F` is Weil's theorem (literature input). -/
theorem sk_partLab_coverRows_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (n : ℕ)
    (C : Finset U) (ord : U → ℕ) (hord : Set.InjOn ord C) (x : U → F)
    (hx : Function.Injective x) (H : Finset (U × U)) (hH : ∀ e ∈ H, e.2 ∈ C ∧ ς e.1 e.2 ≠ 0) :
    ∑ c' ∈ partLab F G C, coverRowIntegrand G ς C H x c' ≤
      ∏ b ∈ C, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
        (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n) +
          (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
            ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b)) := by
  set M : U → ℝ := fun b => (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
    (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n) +
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
        ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) with hM
  have hMnn : ∀ b, 0 ≤ M b := fun b => by
    have he := coarseError_nonneg (q := (Fintype.card F : ℝ))
      (by positivity : (0 : ℝ) ≤ 2 * n) (coverRowS G C ord H b)
    exact mul_nonneg (by positivity) (add_nonneg (add_nonneg zero_le_one he) (by positivity))
  have hmerges_loc : ∀ b, ∀ y y' : U → F, (∀ a ∈ coverRowEarlier C ord b, y a = y' a) →
      coverRowMerges G C ord H x y b = coverRowMerges G C ord H x y' b := by
    intro b y y' h
    unfold coverRowMerges
    refine sum_congr rfl fun b' hb' => ?_
    rw [h b' (mem_filter.mp hb').1]
  have hphi_loc : ∀ b ∈ C, ∀ y y' : U → F, (∀ a ∈ C, ord a ≤ ord b → y a = y' a) →
      coverRowPhi G ς C ord H x b y = coverRowPhi G ς C ord H x b y' := by
    intro b hb y y' hyy
    unfold coverRowPhi
    rw [hyy b hb le_rfl, hmerges_loc b y y' (fun a ha =>
      hyy a (mem_filter.mp ha).1 (mem_filter.mp ha).2.le)]
  have hphi_step : ∀ b ∈ C, ∀ x' : U → F, Feasible F G (coverRowEarlier C ord b) x' →
      ∑ c ∈ vertexAdmissible G (coverRowEarlier C ord b) x' b,
        coverRowPhi G ς C ord H x b (Function.update x' b c) ≤ M b := by
    intro b _ x' hx'
    have hupd : ∀ c, coverRowPhi G ς C ord H x b (Function.update x' b c) =
        coverRowOmegaHat G ς H x b c * ((2 : ℝ) ^ coverRowMerges G C ord H x x' b)⁻¹ := by
      intro c
      unfold coverRowPhi
      rw [Function.update_self, hmerges_loc b _ x' (fun a ha => by
        have hab : a ≠ b := by
          rintro rfl
          exact lt_irrefl _ (mem_filter.mp ha).2
        exact Function.update_of_ne hab _ _)]
    rw [sum_congr rfl fun c _ => hupd c]
    exact sk_coverRows_oneVertex_g hW G ς hς C ord H (fun e he => (hH e he).2) x hx n b x' hx'
  calc ∑ c' ∈ partLab F G C, coverRowIntegrand G ς C H x c'
      ≤ ∑ c' ∈ partLab F G C, ∏ b ∈ C, coverRowPhi G ς C ord H x b c' :=
        sum_le_sum fun c' _ => coverRow_integrand_le G ς C ord H hH x c'
    _ ≤ ∏ b ∈ C, M b :=
        partLab_seq_upper G C ord hord (coverRowPhi G ς C ord H x) M
          (fun b y => coverRow_phi_nonneg G ς C ord H x b y) hMnn hphi_loc hphi_step

/-- **The one-vertex bound of Step 6.** Let `u ∈ U_x` and let `y` be feasible on the vertices
earlier than `u`. Summing `ŵ_u(z) 2^{-κ_u(y)}` over the admissible labels `z` of `u` gives at most
`q 2^{-t_u}(1 + e_{s_u}(q, n) + r² 2^{s_u} ∑_{b ∈ C_z} 2^{c^U(u,b) - [b ∈ H_u]})`. The generic
labels `z ∉ c'(C_z)` are counted by `lem:extraction-merged-count` (`merged_count_le_fintype'`,
with the `κ_u` merged roots), the special labels `z = c'_b` by `intWHat_special_le`.
`WeilBound F` is Weil's theorem (literature input). -/
theorem sk_integrated_oneVertex_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (n : ℕ)
    (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (Ux Cz : Finset U) (hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz) (ord : U → ℕ)
    (c' : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b)
    (u : U) (hu : u ∈ Ux) (y : U → F) (hy : Feasible F G (coverRowEarlier univ ord u) y) :
    ∑ z ∈ vertexAdmissible G (coverRowEarlier univ ord u) y u,
        intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ intMerges G ord Fr c' y u)⁻¹ ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u *
        intNum G ς (Fintype.card F) n ord Fr Cz u := by
  set A := coverRowEarlier univ ord u with hA
  set μ := intMerges G ord Fr c' y u with hμ
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hμinv0 : (0 : ℝ) ≤ ((2 : ℝ) ^ μ)⁻¹ := by positivity
  have hμinv1 : ((2 : ℝ) ^ μ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hHbFr : ∀ b ∈ intH Fr u, (u, b) ∈ Fr := fun b hb => by simpa [intH] using hb
  rw [← sum_filter_add_sum_filter_not (vertexAdmissible G A y u) (fun z => z ∈ Cz.image c')]
  -- the special labels `c'_b`, `b ∈ C_z`
  have hii : ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
      intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹ ≤
        ∑ b ∈ Cz, 2 ^ (intH Fr u).card * (2 : ℝ) ^ intExp G ς Fr u b := by
    calc ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
          intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹
        ≤ ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
            intWHat G ς Fr Cz c' u z :=
          sum_le_sum fun z _ => mul_le_of_le_one_right (intWHat_nonneg G ς Fr Cz c' u z) hμinv1
      _ ≤ ∑ z ∈ Cz.image c', intWHat G ς Fr Cz c' u z :=
          sum_le_sum_of_subset_of_nonneg (fun z hz => (mem_filter.mp hz).2)
            (fun z _ _ => intWHat_nonneg G ς Fr Cz c' u z)
      _ = ∑ b ∈ Cz, intWHat G ς Fr Cz c' u (c' b) :=
          sum_image fun a ha b hb h => hc' a ha b hb h
      _ ≤ _ := sum_le_sum fun b hb => intWHat_special_le G ς Fr Cz c' hc' u b hb
  -- the other labels: `lem:extraction-merged-count`
  set NA := A.filter (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E) with hNA
  set Hb := intH Fr u with hHb
  let β : NA → F := fun i => y i
  have hβ : Function.Injective β := fun i j h =>
    Subtype.ext (hy.1 i (mem_filter.mp i.2).1 j (mem_filter.mp j.2).1 h)
  let γ : Hb → F := fun b => c' b
  have hγ : Function.Injective γ := fun a b h =>
    Subtype.ext (hc' a (hH (u, a) (hHbFr a a.2) hu) b (hH (u, b) (hHbFr b b.2) hu) h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : NA → ℤ := fun i => if (i.1, u) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
    simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact hm1
  let s' : Hb → ℤ := fun b => quadraticChar F (-(ς u b.1 : F))
  have hs' : ∀ b, s' b = 1 ∨ s' b = -1 := fun b => by
    have hb : ς u b.1 ≠ 0 := hFr (u, b.1) (hHbFr b.1 b.2)
    have hne : -(ς u b.1 : F) ≠ 0 := neg_ne_zero.mpr (hς u b.1 hb)
    exact quadraticChar_dichotomy hne
  set 𝒳 : Finset F := A.image y ∪ Cz.image c' with h𝒳
  have hβX : ∀ i, β i ∈ 𝒳 := fun i =>
    mem_union_left _ (mem_image_of_mem y (mem_filter.mp i.2).1)
  have hγX : ∀ b, γ b ∈ 𝒳 := fun b =>
    mem_union_right _ (mem_image_of_mem c' (hH (u, b.1) (hHbFr b.1 b.2) hu))
  have hmc := merged_count_le_fintype' hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX
    (n' := (n : ℝ)) (by positivity)
  have hset : (vertexAdmissible G A y u).filter (fun z => z ∉ Cz.image c') =
      univ.filter (fun z => z ∉ 𝒳 ∧ ∀ i, quadraticChar F (z - β i) = s i) := by
    ext c
    simp only [vertexAdmissible, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨hc, hin, hout⟩, hcX⟩
      refine ⟨⟨hc, hcX⟩, fun i => ?_⟩
      have hi := (mem_filter.mp i.2).2
      simp only [s, β]
      split_ifs with h
      · exact hin i (mem_filter.mp i.2).1 h
      · have hvu : (u, i.1) ∈ G.E := hi.resolve_left h
        have h1 := hout i (mem_filter.mp i.2).1 hvu
        have : y i - c = -1 * (c - y i) := by ring
        rw [this, map_mul] at h1
        rcases hm1 with h' | h' <;> rw [h'] at h1 ⊢ <;> linarith
    · rintro ⟨⟨hc, hcX⟩, hall⟩
      refine ⟨⟨hc, fun i hi he => ?_, fun i hi he => ?_⟩, hcX⟩
      · have hmem : i ∈ NA := mem_filter.mpr ⟨hi, Or.inl he⟩
        have := hall ⟨i, hmem⟩
        simpa [s, β, he] using this
      · have hmem : i ∈ NA := mem_filter.mpr ⟨hi, Or.inr he⟩
        have hnot : (i, u) ∉ G.E := G.oriented u i he
        have h1 := hall ⟨i, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : y i - c = -1 * (c - y i) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hsummand : ∀ z ∈ univ.filter (fun z => z ∉ 𝒳 ∧ ∀ i, quadraticChar F (z - β i) = s i),
      intWHat G ς Fr Cz c' u z = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (z - γ l)) := by
    intro z hz
    have hzX : z ∉ Cz.image c' := fun h => (mem_filter.mp hz).2.1 (mem_union_right _ h)
    have hne : ∀ b ∈ Cz, z ≠ c' b := fun b hb h => hzX (mem_image.mpr ⟨b, hb, h.symm⟩)
    unfold intWHat
    rw [sum_eq_zero fun b hb => by simp only [hne b hb, ↓reduceIte], pow_zero, mul_one]
    unfold intW
    rw [← prod_coe_sort Hb]
    refine prod_congr rfl fun b _ => ?_
    have : (ς u b.1 : F) * (c' b.1 - z) = (-(ς u b.1 : F)) * (z - c' b.1) := by ring
    simp only [s', γ, this, map_mul, Int.cast_mul]
  have hcardι : Fintype.card NA = ordT G ord u := by
    rw [Fintype.card_coe]
    rfl
  have hcardκ : Fintype.card Hb = Hb.card := Fintype.card_coe _
  have hmerge : mergedCount β γ = μ := by
    unfold mergedCount
    calc (univ.filter fun il : NA × Hb => β il.1 = γ il.2).card
        = ∑ il : NA × Hb, if β il.1 = γ il.2 then 1 else 0 := card_filter _ _
      _ = ∑ i : NA, ∑ b : Hb, if β i = γ b then 1 else 0 := Fintype.sum_prod_type _
      _ = ∑ i : NA, ∑ b ∈ Hb, if y i = c' b then 1 else 0 :=
          sum_congr rfl fun i _ => sum_coe_sort Hb (fun b => if y i = c' b then 1 else 0)
      _ = ∑ i ∈ NA, ∑ b ∈ Hb, if y i = c' b then 1 else 0 :=
          sum_coe_sort NA (fun i => ∑ b ∈ Hb, if y i = c' b then 1 else 0)
      _ = μ := rfl
  have hS : intS G ord Fr u = ordT G ord u + Hb.card := rfl
  have hi : ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∉ Cz.image c'),
      intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹ ≤
        Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u *
          (1 + coarseError (intS G ord Fr u) (Fintype.card F) n) := by
    rw [← sum_mul, hset, sum_congr rfl hsummand]
    rw [hcardι, hcardκ, hmerge, ← hS] at hmc
    calc (∑ z ∈ univ.filter (fun z => z ∉ 𝒳 ∧ ∀ i, quadraticChar F (z - β i) = s i),
          ∏ l, ((1 : ℝ) + s' l * quadraticChar F (z - γ l))) * ((2 : ℝ) ^ μ)⁻¹
        ≤ (Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u * 2 ^ μ *
            (1 + coarseError (intS G ord Fr u) (Fintype.card F) n)) *
            ((2 : ℝ) ^ μ)⁻¹ := mul_le_mul_of_nonneg_right hmc hμinv0
      _ = _ := by field_simp
  have hid : (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
      ((Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ intS G ord Fr u *
        ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b) =
      ∑ b ∈ Cz, 2 ^ Hb.card * (2 : ℝ) ^ intExp G ς Fr u b := by
    rw [coverRow_r_sq hq0, ← mul_sum, hS, pow_add]
    have h2 : (2 : ℝ)⁻¹ ^ ordT G ord u * 2 ^ ordT G ord u = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
    calc (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
          ((Fintype.card F : ℝ)⁻¹ * (2 ^ ordT G ord u * 2 ^ Hb.card) *
            ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b)
        = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹) *
            ((2 : ℝ)⁻¹ ^ ordT G ord u * 2 ^ ordT G ord u) *
            (2 ^ Hb.card * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hq0.ne', h2, one_mul, one_mul]
  have hnum : intNum G ς (Fintype.card F) n ord Fr Cz u =
      1 + coarseError (intS G ord Fr u) (Fintype.card F) n +
        (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ intS G ord Fr u *
          ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b := rfl
  rw [hnum]
  calc ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
        intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹ +
      ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∉ Cz.image c'),
        intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹
      ≤ ∑ b ∈ Cz, 2 ^ Hb.card * (2 : ℝ) ^ intExp G ς Fr u b +
          Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u *
            (1 + coarseError (intS G ord Fr u) (Fintype.card F) n) :=
        add_le_add hii hi
    _ = _ := by rw [← hid]; ring

/-- **`eq:extraction:mbound`** (Step 6 of `lem:matching:extractionk`), in summed form. Let the
labels `x₀` of `V ∪ C_x = X \ U_x` be feasible, the labels `c'` of `C_z` injective on `C_z`, and
`H_u ⊆ C_z` for `u ∈ U_x`. Label `U_x` along `ord` (after all other vertices). Then the sum over
the completions `x ∈ 𝓘⁺` of `x₀` of `Θ⁺_U(x, c') = ∏_{(u,b) ∈ Fr, u ∈ U_x} (1 + χ_{ub}(x, c'))` is
at most `2^{κ^f} ∏_{u ∈ U_x} q 2^{-t_u}(1 + e_{s_u}(q, n) + r² 2^{s_u}
∑_{b ∈ C_z} 2^{c^U(u,b) - [b ∈ H_u]})`. `WeilBound F` is Weil's theorem (literature input). -/
theorem sk_integrated_extSum_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (n : ℕ)
    (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (Ux Cz : Finset U) (hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz)
    (ord : U → ℕ) (hord : Function.Injective ord)
    (hseg : ∀ a, a ∉ Ux → ∀ b ∈ Ux, ord a < ord b)
    (c' : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b)
    (x₀ : U → F) (hx₀ : Feasible F G (univ \ Ux) x₀) :
    coverRowExtSum G (univ \ Ux) x₀
        (fun x => ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c')) ≤
      2 ^ kappaFixed G Fr Ux x₀ c' *
        ∏ u ∈ Ux, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
          intNum G ς (Fintype.card F) n ord Fr Cz u) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  set M : U → ℝ := fun b => if b ∈ Ux then (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord b *
      intNum G ς (Fintype.card F) n ord Fr Cz b else Fintype.card F with hM
  have hnum0 : ∀ b, 0 ≤ intNum G ς (Fintype.card F) n ord Fr Cz b := fun b => by
    unfold intNum
    have he := coarseError_nonneg (q := (Fintype.card F : ℝ)) (Nat.cast_nonneg n)
      (intS G ord Fr b)
    have hs : 0 ≤ ∑ b' ∈ Cz, (2 : ℝ) ^ intExp G ς Fr b b' :=
      sum_nonneg fun _ _ => by positivity
    exact add_nonneg (add_nonneg zero_le_one he) (mul_nonneg (by positivity) hs)
  have hM0 : ∀ b, 0 ≤ M b := fun b => by
    simp only [hM]
    split_ifs
    · exact mul_nonneg (by positivity) (hnum0 b)
    · exact hq0.le
  have hloc : ∀ b ∈ (univ : Finset U), ∀ y y' : U → F,
      (∀ a ∈ (univ : Finset U), ord a ≤ ord b → y a = y' a) →
        intPhi G ς ord Fr Ux Cz c' b y = intPhi G ς ord Fr Ux Cz c' b y' := by
    intro b _ y y' hyy
    unfold intPhi
    split_ifs
    · have hm : intMerges G ord Fr c' y b = intMerges G ord Fr c' y' b := by
        unfold intMerges
        refine sum_congr rfl fun i hi => ?_
        have hi' : ord i < ord b := by
          simpa [coverRowEarlier] using (mem_filter.mp hi).1
        rw [hyy i (mem_univ i) hi'.le]
      rw [hyy b (mem_univ b) le_rfl, hm]
    · rfl
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord b) x' →
        ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord b) x' b,
          intPhi G ς ord Fr Ux Cz c' b (Function.update x' b c) ≤ M b := by
    intro b _ x' hx'
    by_cases hb : b ∈ Ux
    · have hupd : ∀ c, intPhi G ς ord Fr Ux Cz c' b (Function.update x' b c) =
          intWHat G ς Fr Cz c' b c * ((2 : ℝ) ^ intMerges G ord Fr c' x' b)⁻¹ := by
        intro c
        have hm : intMerges G ord Fr c' (Function.update x' b c) b =
            intMerges G ord Fr c' x' b := by
          unfold intMerges
          refine sum_congr rfl fun i hi => ?_
          have hib : i ≠ b := by
            rintro rfl
            have : ord i < ord i := by simpa [coverRowEarlier] using (mem_filter.mp hi).1
            exact lt_irrefl _ this
          rw [Function.update_of_ne hib]
        simp only [intPhi, hb, ↓reduceIte, Function.update_self, hm]
      rw [sum_congr rfl fun c _ => hupd c]
      simp only [hM, hb, ↓reduceIte]
      exact sk_integrated_oneVertex_g hW G ς hς n Fr hFr Ux Cz hH ord c' hc' b hb x' hx'
    · simp only [intPhi, hM, hb, ↓reduceIte, sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast card_le_univ _
  have hK : ∀ y : U → F, Feasible F G univ y → (extCount G univ y : ℝ) ≤ 1 := fun y hy => by
    rw [extCount_univ G hy, Nat.cast_one]
  have hseq := coverRow_seq_upper G (C := univ) (ord := ord) (fun a _ b _ h => hord h)
    (intPhi G ς ord Fr Ux Cz c') M 1 (fun b y => intPhi_nonneg G ς ord Fr Ux Cz c' b y) hM0
    zero_le_one hloc hstep hK Ux.card Ux rfl (subset_univ _)
    (fun b hb b' _ hb' => hseg b' hb' b hb) x₀ hx₀
  have hMprod : ∏ b ∈ Ux, M b = ∏ u ∈ Ux, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
      intNum G ς (Fintype.card F) n ord Fr Cz u) :=
    prod_congr rfl fun b hb => by simp only [hM, hb, ↓reduceIte]
  have hpt : ∀ y ∈ (injLabellings F G).filter (fun y => ∀ a ∈ univ \ Ux, y a = x₀ a),
      ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e y c') ≤
        2 ^ kappaFixed G Fr Ux x₀ c' * ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y := by
    intro y hy
    rw [prod_free_eq_prod_intW]
    refine intW_prod_le G ς ord Fr hFr Ux Cz hH hseg x₀ c' y fun i hi => ?_
    exact (mem_filter.mp hy).2 i (mem_sdiff.mpr ⟨mem_univ i, hi⟩)
  calc coverRowExtSum G (univ \ Ux) x₀
        (fun x => ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c'))
      ≤ ∑ y ∈ (injLabellings F G).filter (fun y => ∀ a ∈ univ \ Ux, y a = x₀ a),
          2 ^ kappaFixed G Fr Ux x₀ c' * ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y := by
        unfold coverRowExtSum
        exact sum_le_sum hpt
    _ = 2 ^ kappaFixed G Fr Ux x₀ c' * coverRowExtSum G (univ \ Ux) x₀
          (fun y => ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y) := by
        unfold coverRowExtSum
        rw [mul_sum]
    _ ≤ 2 ^ kappaFixed G Fr Ux x₀ c' * (1 * ∏ b ∈ Ux, M b) :=
        mul_le_mul_of_nonneg_left hseq (by positivity)
    _ = _ := by rw [one_mul, hMprod]

/-- **Steps 5–6 for one fibre** (`eq:extraction:mbound` with Cauchy–Schwarz):
`𝖺_{c,c'}(v)² ≤ 2^{f_V} ∏_{u ∈ U_x} q 2^{-t_u} num_u · ∑_{x : x_{C_x} = c, x_V = v}
f(x)² Θ₁⁺(x, c') 2^{κ_{C_z}(x, c')}`. -/
theorem sk_alpha_sq_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (n : ℕ)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (V Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz)
    (ordX : U → ℕ) (hordX : Function.Injective ordX)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (f : (U → F) → ℝ) (c c' v : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b) :
    alphaF G ς P Fr V Cx Cz f c c' v ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
        (∏ u ∈ univ \ (V ∪ Cx), intNumQ F G ς n ordX Fr Cz u) *
        ∑ x ∈ fib G Cx V c v, f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' *
          2 ^ coverRowKappa G ς Cz x c' := by
  set Ux := univ \ (V ∪ Cx) with hUx
  set MU := ∏ u ∈ Ux, intNumQ F G ς n ordX Fr Cz u
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set g : (U → F) → ℝ := fun x => groupPos ς Fr (predOne Cx Cz) x c' with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => groupPos_nonneg ς Fr _ x c'
  have hMU0 : 0 ≤ MU := prod_nonneg fun u _ => intNumQ_nonneg G ς n ordX Fr Cz u
  by_cases hne : (fib G Cx V c v).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hne
    unfold alphaF
    rw [hne, sum_empty, sum_empty]
    simp
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨hx₀I, hx₀c, hx₀v⟩ := mem_fib.mp hx₀
  have hfib : fib G Cx V c v = (injLabellings F G).filter
      (fun y => ∀ a ∈ univ \ Ux, y a = x₀ a) := by
    rw [← hx₀c, ← hx₀v]
    exact fib_eq_extensions G V Cx x₀
  have hx₀f : Feasible F G (univ \ Ux) x₀ := by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx₀I
    exact ⟨fun a _ b _ h => hx₀I.1 a (mem_univ _) b (mem_univ _) h,
      fun e he _ _ => hx₀I.2 e he (mem_univ _) (mem_univ _)⟩
  have hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz := fun e he h1 => hFr1 e he (by
    have := (mem_sdiff.mp h1).2
    simp only [mem_union, not_or] at this
    exact this.2)
  -- Step 6: the integrated vertices
  have hm := sk_integrated_extSum_le_g (n := n) hW G ς hς Fr hFrς Ux Cz hH ordX hordX hsegX c' hc'
    x₀ hx₀f
  unfold coverRowExtSum at hm
  rw [← hfib] at hm
  -- `∑ Θ₁⁺ ≤ 2^{f_V} 2^{κ^f} M_U`
  have hsumg : ∑ x ∈ fib G Cx V c v, g x ≤ 2 ^ fV * (2 ^ kappaFixed G Fr Ux x₀ c' * MU) := by
    calc ∑ x ∈ fib G Cx V c v, g x
        ≤ ∑ x ∈ fib G Cx V c v, 2 ^ fV *
            ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c') := by
          refine sum_le_sum fun x _ => ?_
          simp only [hg]
          rw [groupPos_one_split ς Fr V Cx Cz hVC hFr1 x c']
          exact mul_le_mul_of_nonneg_right (prod_free_le_two_pow ς _ x c')
            (prod_nonneg fun e _ => one_add_chiPair_nonneg ς e x c')
      _ = 2 ^ fV * ∑ x ∈ fib G Cx V c v,
            ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c') := by rw [mul_sum]
      _ ≤ 2 ^ fV * (2 ^ kappaFixed G Fr Ux x₀ c' * MU) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
  -- Cauchy–Schwarz
  have hα : |alphaF G ς P Fr V Cx Cz f c c' v| ≤ ∑ x ∈ fib G Cx V c v, g x * |f x| := by
    unfold alphaF
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_groupKer_le ς P Fr _ x c') (abs_nonneg _)
  have hcs := weighted_cs (fib G Cx V c v) g f (fun x _ => hg0 x)
  have hκ : ∀ x ∈ fib G Cx V c v, kappaFixed G Fr Ux x₀ c' ≤ coverRowKappa G ς Cz x c' := by
    intro x hx
    rw [hfib, mem_filter] at hx
    rw [← kappaFixed_congr G Fr Ux (x := x) (y := x₀) (fun i hi => hx.2 i (by
      simp only [mem_sdiff, mem_univ, true_and]; exact hi)) c']
    exact kappaFixed_le_coverRowKappa G ς Fr hFrς Ux Cz hH x c'
  have hsum2 : (2 : ℝ) ^ kappaFixed G Fr Ux x₀ c' * ∑ x ∈ fib G Cx V c v, g x * f x ^ 2 ≤
      ∑ x ∈ fib G Cx V c v, f x ^ 2 * g x * 2 ^ coverRowKappa G ς Cz x c' := by
    rw [mul_sum]
    refine sum_le_sum fun x hx => ?_
    have h2 : (2 : ℝ) ^ kappaFixed G Fr Ux x₀ c' ≤ 2 ^ coverRowKappa G ς Cz x c' :=
      pow_le_pow_right₀ (by norm_num) (hκ x hx)
    have h0 : 0 ≤ g x * f x ^ 2 := mul_nonneg (hg0 x) (sq_nonneg _)
    calc (2 : ℝ) ^ kappaFixed G Fr Ux x₀ c' * (g x * f x ^ 2)
        ≤ 2 ^ coverRowKappa G ς Cz x c' * (g x * f x ^ 2) := mul_le_mul_of_nonneg_right h2 h0
      _ = _ := by ring
  have hS0 : 0 ≤ ∑ x ∈ fib G Cx V c v, g x * f x ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (hg0 x) (sq_nonneg _)
  calc alphaF G ς P Fr V Cx Cz f c c' v ^ 2
      = |alphaF G ς P Fr V Cx Cz f c c' v| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ x ∈ fib G Cx V c v, g x * |f x|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hα 2
    _ ≤ (∑ x ∈ fib G Cx V c v, g x) * ∑ x ∈ fib G Cx V c v, g x * f x ^ 2 := hcs
    _ ≤ (2 ^ fV * (2 ^ kappaFixed G Fr Ux x₀ c' * MU)) *
          ∑ x ∈ fib G Cx V c v, g x * f x ^ 2 := mul_le_mul_of_nonneg_right hsumg hS0
    _ = 2 ^ fV * MU * ((2 : ℝ) ^ kappaFixed G Fr Ux x₀ c' *
          ∑ x ∈ fib G Cx V c v, g x * f x ^ 2) := by ring
    _ ≤ 2 ^ fV * MU * ∑ x ∈ fib G Cx V c v, f x ^ 2 * g x * 2 ^ coverRowKappa G ς Cz x c' :=
        mul_le_mul_of_nonneg_left hsum2 (mul_nonneg (by positivity) hMU0)

/-- **One side of `lem:matching:extractionk` (Steps 5–7)**, counting form:
`∑_{c, c'} |Γ(c, c')| ‖𝖺_{c,c'}‖² ≤ 2^{f_V} ∏_{u ∈ U_x} q 2^{-t_u} num_u
∏_{b ∈ C_z} q 2^{-t_b} num_b ∑_{x ∈ 𝓘⁺} f(x)²`, where `num_u`, `num_b` are the numerators of the
vertex factors `F_u` (`u ∈ U_x`) and `F_b` (`b ∈ C_z`, with `H_b` all free pairs at `b`). The
cover labels `c'` are summed over the labellings of `C_z` without completions (Steps 2–5 of
`lem:extraction-rows`, `sk_partLab_coverRows_le_g`). -/
theorem sk_one_side_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (n : ℕ)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (V Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Set.InjOn ordZ Cz)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (f : (U → F) → ℝ) :
    ∑ c ∈ (injLabellings F G).image (restr Cx), ∑ c' ∈ (injLabellings F G).image (restr Cz),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
        (∏ u ∈ univ \ (V ∪ Cx), intNumQ F G ς n ordX Fr Cz u) *
        (∏ b ∈ Cz, coverNumQ F G ς n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
        ∑ x ∈ injLabellings F G, f x ^ 2 := by
  set I := injLabellings F G
  set Ix := I.image (restr Cx)
  set Iz := I.image (restr Cz)
  set H := Fr.filter (fun e => e.2 ∈ Cz) with hHdef
  set K := 2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
    (∏ u ∈ univ \ (V ∪ Cx), intNumQ F G ς n ordX Fr Cz u) with hK
  set MC := ∏ b ∈ Cz, coverNumQ F G ς n Cz ordZ H b
  have hK0 : 0 ≤ K := mul_nonneg (by positivity)
    (prod_nonneg fun u _ => intNumQ_nonneg G ς n ordX Fr Cz u)
  set Prow : (U → F) → (U → F) → ℝ := fun x c' => coverRowIntegrand G ς Cz H x c' with hProw
  have hProw0 : ∀ x c', 0 ≤ Prow x c' := fun x c' => coverRowIntegrand_nonneg G ς Cz H x c'
  -- the cover labels are injective on `C_z`
  have hinjz : ∀ c' ∈ Iz, ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b := by
    intro c' hc' a ha b hb hab
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
    simp only [I, injLabellings, mem_filter, mem_univ, true_and] at hy
    rw [restr_apply_of_mem ha, restr_apply_of_mem hb] at hab
    exact hy.1 a (mem_univ _) b (mem_univ _) hab
  -- Steps 5–6 for each `(c, c')`, summed over `v`
  have hstep : ∀ c ∈ Ix, ∀ c' ∈ Iz,
      |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2 ≤
        K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' := by
    intro c _ c' hc'
    have hv : ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2 ≤
        K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 *
          groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c' := by
      calc ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2
          ≤ ∑ v ∈ injTuples F V, K * ∑ x ∈ fib G Cx V c v, f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c' :=
            sum_le_sum fun v _ => sk_alpha_sq_le_g hW G ς hς n P Fr hFrς V Cx Cz hVC hFr1 ordX
              hordX hsegX f c c' v (hinjz c' hc')
        _ = K * ∑ v ∈ injTuples F V, ∑ x ∈ fib G Cx V c v, f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c' := by
            rw [mul_sum]
        _ = _ := by
            congr 1
            rw [← sum_fiberwise_of_maps_to (s := I.filter (fun x => restr Cx x = c))
              (g := restr V) (t := injTuples F V)
              (fun x hx => restr_mem_injTuples G V (mem_filter.mp hx).1)]
            refine sum_congr rfl fun v _ => ?_
            unfold fib
            rw [filter_filter]
    have hΓ : ∀ x ∈ I.filter (fun x => restr Cx x = c),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') ≤
          f x ^ 2 * Prow x c' := by
      intro x hx
      have hxc := (mem_filter.mp hx).2
      have hg : groupPos ς Fr (predGam Cx Cz) c c' = groupPos ς Fr (predGam Cx Cz) x c' :=
        groupPos_congr ς Fr _ fun e he => ⟨(restr_eq_iff hxc he.1).symm, rfl⟩
      have h1 := abs_groupKer_le ς P Fr (predGam Cx Cz) c c'
      rw [hg] at h1
      have h0 : 0 ≤ f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' *
          2 ^ coverRowKappa G ς Cz x c' :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (groupPos_nonneg ς Fr _ x c')) (by positivity)
      calc |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c')
          ≤ groupPos ς Fr (predGam Cx Cz) x c' *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') :=
            mul_le_mul_of_nonneg_right h1 h0
        _ = f x ^ 2 * (groupPos ς Fr (predOne Cx Cz) x c' *
              groupPos ς Fr (predGam Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') := by ring
        _ = f x ^ 2 * Prow x c' := by rw [groupPos_one_mul_gam]
    calc |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2
        ≤ |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') :=
          mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ = K * ∑ x ∈ I.filter (fun x => restr Cx x = c),
            |groupKer ς P Fr (predGam Cx Cz) c c'| * (f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') := by
          rw [mul_sum, mul_sum, mul_sum]
          exact sum_congr rfl fun x _ => by ring
      _ ≤ K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' :=
          mul_le_mul_of_nonneg_left (sum_le_sum hΓ) hK0
  -- Step 7: the cover rows
  have hrow : ∀ x ∈ I, ∑ c' ∈ Iz, Prow x c' ≤ MC := by
    intro x hx
    have hxinj : Function.Injective x := by
      simp only [I, injLabellings, mem_filter, mem_univ, true_and] at hx
      exact fun a b h => hx.1 a (mem_univ _) b (mem_univ _) h
    calc ∑ c' ∈ Iz, Prow x c' ≤ ∑ c' ∈ partLab F G Cz, Prow x c' := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun c' _ _ => hProw0 x c'
          intro c' hc'
          obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
          exact restr_mem_partLab G Cz hy
      _ ≤ MC := sk_partLab_coverRows_le_g hW G ς hς n Cz ordZ hordZ x hxinj H
          (fun e he => ⟨(mem_filter.mp he).2, hFrς e (mem_filter.mp he).1⟩)
  calc ∑ c ∈ Ix, ∑ c' ∈ Iz, |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2
      ≤ ∑ c ∈ Ix, ∑ c' ∈ Iz, K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' :=
        sum_le_sum fun c hc => sum_le_sum fun c' hc' => hstep c hc c' hc'
    _ = K * ∑ c' ∈ Iz, ∑ c ∈ Ix, ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun c' _ => ?_
        rw [mul_sum]
    _ = K * ∑ c' ∈ Iz, ∑ x ∈ I, f x ^ 2 * Prow x c' := by
        congr 1
        refine sum_congr rfl fun c' _ => ?_
        exact sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem _ hx) _
    _ = K * ∑ x ∈ I, f x ^ 2 * ∑ c' ∈ Iz, Prow x c' := by
        rw [sum_comm]
        congr 1
        exact sum_congr rfl fun x _ => by rw [mul_sum]
    _ ≤ K * ∑ x ∈ I, f x ^ 2 * MC :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun x hx =>
          mul_le_mul_of_nonneg_left (hrow x hx) (sq_nonneg _)) hK0
    _ = _ := by
        rw [← sum_mul]
        ring

/-- **Step 8 without antisymmetry**: the other side, with the factors computed from the transposed
signs `ςᵀ` (equal to those of `ς` when the support is symmetric). -/
theorem sk_other_side_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (n : ℕ)
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
  have hT := sk_one_side_le_g hW G (skT ς) (skT_castF ς hς) n (P.image Prod.swap)
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
theorem sk_grouped_count_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0)
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
  have h1 := sk_one_side_le_g hW G ς hς n P Fr hFrς V Cx Cz hVC
    (fun e he h1 => (hFr e he).resolve_left h1) ordX ordZ hordX hordZ.injOn hsegX f
  have h2 := sk_other_side_le_g hW G ς hς n P Fr hFrς W Cx Cz hWC
    (fun e he h2 => (hFr e he).resolve_right h2) ordX ordZ hordX.injOn hordZ hsegZ h
  have hsupp : ∀ j k, skT ς j k ≠ 0 ↔ ς j k ≠ 0 := skT_ne_zero_iff ς hsym
  rw [sk_intNumQ_congr G hsupp, sk_coverNumQ_congr G hsupp] at h2
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hΛ)
    (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) (mul_nonneg hΛ (Real.sqrt_nonneg _))

/-- `grouped_extraction_sum_le` with a symmetric support of `ς` in place of antisymmetry. -/
theorem sk_grouped_sum_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0) {n : ℕ}
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
  have hQ := sk_grouped_count_g hW G ς hς hsym n P Fr hFrς V W Cx Cz hVC hWC hP hFr ordX
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


/-- The signs multiplied by `ν` (with `χ(ν) = -1`) at the free pairs with a negative
coefficient. -/
noncomputable def skFlipN (ς : U → U → ℤ) (D : U × U → ℝ) (Fr : Finset (U × U)) (ν : ℤ) :
    U → U → ℤ :=
  fun j k => if (j, k) ∈ Fr ∧ D (j, k) < 0 then ν * ς j k else ς j k

omit [Fintype U] in
theorem skFlipN_ne_zero_iff (ς : U → U → ℤ) (D : U × U → ℝ) (Fr : Finset (U × U)) {ν : ℤ}
    (hν : quadraticChar F (ν : F) = -1) (j k : U) :
    skFlipN ς D Fr ν j k ≠ 0 ↔ ς j k ≠ 0 := by
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν
  unfold skFlipN
  split_ifs
  · exact ⟨fun h h' => h (by rw [h', mul_zero]), fun h => mul_ne_zero hν0 h⟩
  · exact Iff.rfl

omit [Fintype U] in
theorem skFlipN_castF (ς : U → U → ℤ) (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0)
    (D : U × U → ℝ) (Fr : Finset (U × U)) {ν : ℤ} (hν : quadraticChar F (ν : F) = -1)
    (j k : U) : skFlipN ς D Fr ν j k ≠ 0 → ((skFlipN ς D Fr ν j k : ℤ) : F) ≠ 0 := by
  have hνF : (ν : F) ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at hν
    norm_num at hν
  intro h
  have hj : ς j k ≠ 0 := (skFlipN_ne_zero_iff ς D Fr hν j k).mp h
  unfold skFlipN
  split_ifs
  · push_cast
    exact mul_ne_zero hνF (hς j k hj)
  · exact hς j k hj

omit [Fintype U] in
theorem skFlipN_of_not_mem (ς : U → U → ℤ) (D : U × U → ℝ) {Fr : Finset (U × U)} (ν : ℤ)
    {e : U × U} (he : e ∉ Fr) (x x' : U → F) :
    chiPair (skFlipN ς D Fr ν) e x x' = chiPair ς e x x' := by
  unfold chiPair skFlipN
  simp only [Prod.mk.eta, he, false_and, ↓reduceIte]

omit [Fintype U] in
/-- `1 + D χ = (1 - |D|) + |D| (1 + χ')`, `χ'` with the sign multiplied by a non-square `ν` when
`D < 0` (`χ(ν ς t) = -χ(ς t)`). -/
theorem sk_flipN_identity (ς : U → U → ℤ) (D : U × U → ℝ) {Fr : Finset (U × U)} {e : U × U}
    (he : e ∈ Fr) {ν : ℤ} (hν : quadraticChar F (ν : F) = -1) (x x' : U → F) :
    1 + D e * chiPair ς e x x' =
      |D e| * (1 + chiPair (skFlipN ς D Fr ν) e x x') + (1 - |D e|) := by
  by_cases hD : D e < 0
  · have hflip : chiPair (skFlipN ς D Fr ν) e x x' = -chiPair ς e x x' := by
      unfold chiPair skFlipN
      simp only [Prod.mk.eta, he, hD, and_self, ↓reduceIte]
      push_cast
      rw [mul_assoc, map_mul, hν]
      push_cast
      ring
    rw [hflip, abs_of_neg hD]
    ring
  · push Not at hD
    have hflip : chiPair (skFlipN ς D Fr ν) e x x' = chiPair ς e x x' := by
      unfold chiPair skFlipN
      have : ¬ (D e < 0) := not_lt.mpr hD
      simp only [Prod.mk.eta, this, and_false, ↓reduceIte]
    rw [hflip, abs_of_nonneg hD]
    ring

omit [Fintype U] in
/-- **The convex decomposition of the soft class kernel**:
`K^D_𝒞 = (∏_{e ∈ P} D_e) ∑_{T ⊆ F} w_T K^{ς'}_{𝒞(P, A ∪ (F \ T))}`, the signs `ς'` flipped at the
free pairs with negative coefficient. -/
theorem sk_softKer_expandN (ς : U → U → ℤ) (D : U × U → ℝ) (P Fr : Finset (U × U))
    (hPFr : Disjoint P Fr) {ν : ℤ} (hν : quadraticChar F (ν : F) = -1)
    (x x' : U → F) :
    skSoftKer ς D P Fr x x' = (∏ e ∈ P, D e) *
      ∑ T ∈ Fr.powerset, skW D Fr T * classKer (skFlipN ς D Fr ν) P T x x' := by
  unfold skSoftKer classKer skW
  rw [prod_mul_distrib]
  have hP : ∏ e ∈ P, chiPair ς e x x' = ∏ e ∈ P, chiPair (skFlipN ς D Fr ν) e x x' :=
    prod_congr rfl fun e he => (skFlipN_of_not_mem ς D ν (disjoint_left.mp hPFr he) x x').symm
  have hF : ∏ e ∈ Fr, (1 + D e * chiPair ς e x x') =
      ∏ e ∈ Fr, (|D e| * (1 + chiPair (skFlipN ς D Fr ν) e x x') + (1 - |D e|)) :=
    prod_congr rfl fun e he => sk_flipN_identity ς D he hν x x'
  rw [hP, hF, prod_add, mul_assoc]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun T _ => ?_
  rw [prod_mul_distrib]
  ring

omit [Fintype U] in
theorem sk_rectKer_flipN (ς : U → U → ℤ) (D : U × U → ℝ) (P Fr : Finset (U × U))
    (hPFr : Disjoint P Fr) (ν : ℤ) (V W : Finset U) :
    rectKer (skFlipN ς D Fr ν) P V W = (rectKer ς P V W : (U → F) → (U → F) → ℝ) := by
  funext v w
  unfold rectKer
  exact prod_congr rfl fun e he =>
    skFlipN_of_not_mem ς D ν (disjoint_left.mp hPFr (mem_filter.mp he).1) v w

/-- The bilinear sum of the soft kernel is the weighted sum of the Boolean sub-class sums. -/
theorem sk_soft_sum_eqN (G : OrientedGraph U) (ς : U → U → ℤ) (D : U × U → ℝ)
    (P Fr : Finset (U × U)) (hPFr : Disjoint P Fr)
    {ν : ℤ} (hν : quadraticChar F (ν : F) = -1) (f h : (U → F) → ℝ) :
    ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * skSoftKer ς D P Fr x x' * h x' =
      (∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset, skW D Fr T *
        ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
          f x * classKer (skFlipN ς D Fr ν) P T x x' * h x' := by
  simp only [sk_softKer_expandN ς D P Fr hPFr hν]
  calc ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
        f x * ((∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset,
          skW D Fr T * classKer (skFlipN ς D Fr ν) P T x x') * h x'
      = ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, ∑ T ∈ Fr.powerset,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlipN ς D Fr ν) P T x x' * h x')) := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
        rw [mul_sum, mul_sum, sum_mul]
        exact sum_congr rfl fun T _ => by ring
    _ = ∑ x ∈ injLabellings F G, ∑ T ∈ Fr.powerset, ∑ x' ∈ injLabellings F G,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlipN ς D Fr ν) P T x x' * h x')) :=
        sum_congr rfl fun x _ => sum_comm
    _ = ∑ T ∈ Fr.powerset, ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlipN ς D Fr ν) P T x x' * h x')) := sum_comm
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun T _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum, mul_sum]

/-- `sk_grouped_sum_le_g` (general nonzero signs) with the bound written with `recordExp` and `recordFactor`. -/
theorem sk_grouped_sum_le_g' (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0) {n : ℕ}
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
  sk_grouped_sum_le_g hW G ς hς hsym hn hehat hehat1 P Fr hFrς V W Cx Cz hVk hWk hVC hWC hP hFr
    ordX ordZ hordX hordZ hX0 hZ0 hsegX hsegZ hcker hker f h

/-- **`cor:soft-kernels`(a), sum form, all coefficients `D_e ∈ [-1, 1]`**, given an integer
`ν` with `χ(ν) = -1` (a non-square of `F`): the soft class kernel satisfies the bound of
`lem:matching:extractionk` for the Boolean class (signs of the free pairs with `D_e < 0` are
multiplied by `ν`). -/
theorem sk_soft_sum_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (hsym : ∀ j k, ς j k ≠ 0 ↔ ς k j ≠ 0) {n : ℕ}
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
    (ν : ℤ) (hν : quadraticChar F (ν : F) = -1)
    (f h : (U → F) → ℝ) :
    |(∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * skSoftKer ς D P Fr x x' * h x') /
        ((injLabellings F G).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G Fr V W ordX ordZ *
          recordFactor G ς (Fintype.card F) n Fr V W Cx Cz ordX ordZ) / (1 - ehat) ^ k *
        Real.sqrt ((∑ x ∈ injLabellings F G, f x ^ 2) / (injLabellings F G).card) *
        Real.sqrt ((∑ x ∈ injLabellings F G, h x ^ 2) / (injLabellings F G).card) := by
  rw [sk_soft_sum_eqN G ς D P Fr hPFr hν f h]
  have hsupp : ∀ j k, skFlipN ς D Fr ν j k ≠ 0 ↔ ς j k ≠ 0 := skFlipN_ne_zero_iff ς D Fr hν
  have hsym' : ∀ j k, skFlipN ς D Fr ν j k ≠ 0 ↔ skFlipN ς D Fr ν k j ≠ 0 := fun j k => by
    rw [hsupp, hsupp]
    exact hsym j k
  have hker' : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W)
      (rectKer (skFlipN ς D Fr ν) P V W) (cker * Real.sqrt (Fintype.card F) ^ k) := by
    rw [sk_rectKer_flipN ς D P Fr hPFr ν V W]
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
          f x * classKer (skFlipN ς D Fr ν) P T x x' * h x') / ((injLabellings F G).card : ℝ) ^ 2| ≤
        cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          Real.sqrt (2 ^ recordExp G Fr V W ordX ordZ *
            recordFactor G ς (Fintype.card F) n Fr V W Cx Cz ordX ordZ) / (1 - ehat) ^ k *
          Real.sqrt ((∑ x ∈ injLabellings F G, f x ^ 2) / (injLabellings F G).card) *
          Real.sqrt ((∑ x ∈ injLabellings F G, h x ^ 2) / (injLabellings F G).card) := by
    intro T hT
    rw [mem_powerset] at hT
    have hb := sk_grouped_sum_le_g' hW G (skFlipN ς D Fr ν) (skFlipN_castF ς hς D Fr hν) hsym' hn hehat
      hehat1 P T (fun e he => (hsupp e.1 e.2).mpr (hFrς e (hT he))) V W Cx Cz hVk hWk hVC hWC
      hP (fun e he => hFr e (hT he)) ordX ordZ hordX hordZ hX0 hZ0 hsegX hsegZ hcker hker' f h
    rw [sk_recordFactor_congr G hsupp] at hb
    refine hb.trans ?_
    have hm := sk_bound_mono G ς he hT V W Cx Cz ordX ordZ
    have hX : 0 ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k := by positivity
    gcongr
  calc |((∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset, skW D Fr T *
          (∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
            f x * classKer (skFlipN ς D Fr ν) P T x x' * h x')) / ((injLabellings F G).card : ℝ) ^ 2|
      = |∏ e ∈ P, D e| * |∑ T ∈ Fr.powerset, skW D Fr T *
          ((∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
            f x * classKer (skFlipN ς D Fr ν) P T x x' * h x') /
              ((injLabellings F G).card : ℝ) ^ 2)| := by
        rw [mul_div_assoc, abs_mul, sum_div]
        congr 2
        exact sum_congr rfl fun T _ => by ring
    _ ≤ 1 * ∑ T ∈ Fr.powerset, skW D Fr T *
          |(∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
            f x * classKer (skFlipN ς D Fr ν) P T x x' * h x') /
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

/-- **`cor:soft-kernels`(a) for `lem:matching:extractionk`, all coefficients.** Let `D_e ∈ [-1, 1]`
and let `ν` be an integer with `χ(ν) = -1` (a non-square; for `𝔽_p` it exists,
`sk_exists_nonsquare_int`). Under the hypotheses of `grouped_extraction`, the soft class operator
`T^D_𝒞 = ∑_{S ∈ 𝒞} D_S T_S` satisfies the bound of `grouped_extraction`. -/
theorem sk_soft_extraction_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
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
    (ν : ℤ) (hν : quadraticChar F (ν : F) = -1)
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
  have hςF : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0 := fun j k hjk => by
    rcases hς j k with h0 | h1 | h1
    · exact absurd h0 hjk
    · rw [h1]; simp
    · rw [h1]; simp
  exact sk_soft_sum_le_g hW G ς hςF hsym hn hehat hehat1 P Fr hPFr
    (fun e he => hEx e (hFrEx e he)) (witV w) (witW w) Cx Cz hVk hWk hVC hWC hP' hFr' ordX ordZ
    hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker D (fun e _ => hD e) (fun e _ => hD e) ν hν f h


/-- For an odd prime `p` some integer is a non-square modulo `p`. -/
theorem sk_exists_nonsquare_int {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ ν : ℤ, quadraticChar (ZMod p) ((ν : ℤ) : ZMod p) = -1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hF
  refine ⟨(a.val : ℤ), ?_⟩
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  exact quadraticChar_neg_one_iff_not_isSquare.mpr ha

end SkGen

end Sarkozy.ExtractionK
