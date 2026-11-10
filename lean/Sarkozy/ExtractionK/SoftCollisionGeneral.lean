module

public import Sarkozy.ExtractionK.SoftCollision3
public import Sarkozy.ExtractionK.SoftGeneral

@[expose] public section

/-!
# Soft coincidences, all coefficients (`cor:soft-kernels`(b), `lem:oct24-collision`)

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(b) without the restriction of
`SoftCollision*.lean` (`χ(-1) = -1` at the pairs with `D_e < 0`): such a pair is flipped by an
integer non-square `ν` (`skCollSgnN`), so the row sums of `lem:oct24-collision` are re-proved for
cross signs that are only nonzero in `F` on their support: `sk_collision_oneStep_g`,
`sk_collision_stratum_le_g`, `sk_collision_stratum_ratio_g`, `sk_collision_rowSum_le_g`,
`sk_collision_oneStep_gen_g`, `sk_collision_stratumI_le_g`, `sk_collision_stratumI_ratio_g`,
`sk_collision_rowSum2_le_g` (the proofs of `Extraction/CollisionBound.lean` and
`Extraction/CollisionStrata.lean`, where the sign hypothesis only gives `χ(ς_{jk}) = ±1`).

* `sk_soft_collision_opBound_g` (`D_1`), `sk_soft_collision_opBound2_g` (`D_{≥2}`),
  `sk_soft_collision_opBound_sum_g`, `sk_soft_collision_opBound_natural_g` (`D_nat`),
  `sk_soft_collision_opBound_ord_g`, `sk_soft_collision_opBound_tailForm_g`: the bounds of
  `lem:oct24-collision` for `T^D_coll` and its parts, every `|D_e| ≤ 1`, given `ν` with `χ(ν) = -1`;
* over `𝔽_p`, `p` odd, with no condition: `sk_soft_collision_opBound_zmod`,
  `sk_soft_collision_opBound2_zmod`, `sk_soft_collision_opBound_natural_zmod`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SkCollG

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **The one-step sum at a non-coincident vertex** (proof of `lem:oct24-collision`(a)). Let
`x'` be feasible on the labelled set `A`, with one coincident vertex `i ∈ A`, `x'_i = x_j`, all
other labels of `A` outside `x(U⁺)`. For a new vertex `ℓ` with `t` labelled neighbours, the sum of
`w_ℓ` over its admissible labels outside `x(U⁺)` is at most
`q 2^{-t} 2^{μ} (1 + e_{t + r_ℓ - μ}(q, n'))`, `μ = [ℓ ∼ i and j ∈ N(ℓ)]`, by
`lem:extraction-merged-count`: the only merged root is `x'_i = x_j`. -/
theorem sk_collision_oneStep_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (x : U → F) (hx : Function.Injective x)
    (A : Finset U) (ℓ : U) (x' : U → F) (hx' : Feasible F G A x') (i j : U) (hiA : i ∈ A)
    (hxi : x' i = x j) (hother : ∀ u ∈ A, u ≠ i → x' u ∉ univ.image x) {n' : ℝ}
    (hn' : 0 ≤ n') :
    ∑ c ∈ (vertexAdmissible G A x' ℓ).filter (fun c => c ∉ univ.image x),
        collisionW ς x ℓ c ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ nbrCount G A ℓ *
        2 ^ (if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0) *
        (1 + coarseError (nbrCount G A ℓ + collisionR ς ℓ -
          (if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0)) (Fintype.card F) n') := by
  set X : Finset F := univ.image x with hX
  set NA := A.filter (fun u => (u, ℓ) ∈ G.E ∨ (ℓ, u) ∈ G.E) with hNA
  set Nl := rowsN ς ℓ with hNl
  let β : NA → F := fun u => x' u
  have hβ : Function.Injective β := fun u w h =>
    Subtype.ext (hx'.1 u (mem_filter.mp u.2).1 w (mem_filter.mp w.2).1 h)
  let γ : Nl → F := fun a => x a
  have hγ : Function.Injective γ := fun a a' h => Subtype.ext (hx h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : NA → ℤ := fun u => if (u.1, ℓ) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ u, s u = 1 ∨ s u = -1 := fun u => by
    simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact hm1
  let s' : Nl → ℤ := fun a => quadraticChar F (ς a.1 ℓ : F)
  have hs' : ∀ a, s' a = 1 ∨ s' a = -1 := fun a => by
    have ha : ς a.1 ℓ ≠ 0 := by simpa [hNl, rowsN] using a.2
    exact quadraticChar_dichotomy (hς a.1 ℓ ha)
  set 𝒳 : Finset F := A.image x' ∪ X with h𝒳
  have hβX : ∀ u, β u ∈ 𝒳 := fun u =>
    mem_union_left _ (mem_image_of_mem x' (mem_filter.mp u.2).1)
  have hγX : ∀ a, γ a ∈ 𝒳 := fun a => mem_union_right _ (mem_image_of_mem x (mem_univ _))
  have hmc := merged_count_le_fintype hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX hn'
  have hset : (vertexAdmissible G A x' ℓ).filter (fun y => y ∉ X) =
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
      · have hvu : (ℓ, u.1) ∈ G.E := hu.resolve_left h
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
        have hnot : (u, ℓ) ∉ G.E := G.oriented ℓ u he
        have h1 := hall ⟨u, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hsummand : ∀ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
      collisionW ς x ℓ y = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l)) := by
    intro y _
    unfold collisionW
    rw [← prod_coe_sort Nl]
    refine prod_congr rfl fun a _ => ?_
    simp only [s', γ, map_mul, Int.cast_mul]
  have hcardι : Fintype.card NA = nbrCount G A ℓ := by
    rw [Fintype.card_coe]
    rfl
  have hcardκ : Fintype.card Nl = collisionR ς ℓ := Fintype.card_coe _
  have hmerge : mergedCount β γ = if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0 := by
    unfold mergedCount
    calc (univ.filter fun il : NA × Nl => β il.1 = γ il.2).card
        = ∑ il : NA × Nl, if β il.1 = γ il.2 then 1 else 0 := card_filter _ _
      _ = ∑ u : NA, ∑ a : Nl, if β u = γ a then 1 else 0 := Fintype.sum_prod_type _
      _ = ∑ u : NA, ∑ a ∈ Nl, if x' u = x a then 1 else 0 :=
          sum_congr rfl fun u _ => sum_coe_sort Nl (fun a => if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, ∑ a ∈ Nl, if x' u = x a then 1 else 0 :=
          sum_coe_sort NA (fun u => ∑ a ∈ Nl, if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, if u = i then (if j ∈ Nl then 1 else 0) else 0 := by
          refine sum_congr rfl fun u hu => ?_
          by_cases hui : u = i
          · subst hui
            simp only [hxi, hx.eq_iff, ↓reduceIte]
            rw [sum_ite_eq]
          · simp only [hui, ↓reduceIte]
            refine sum_eq_zero fun a _ => ?_
            have hno := hother u (mem_filter.mp hu).1 hui
            have : x' u ≠ x a := fun h => hno (h ▸ mem_image_of_mem x (mem_univ a))
            simp only [this, ↓reduceIte]
      _ = if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0 := by
          rw [sum_ite_eq']
          have hiff : i ∈ NA ↔ i ∈ rowsAdj G ℓ := by
            simp only [hNA, rowsAdj, mem_filter, mem_univ, true_and, hiA]
          by_cases h1 : i ∈ rowsAdj G ℓ <;> by_cases h2 : j ∈ rowsN ς ℓ <;>
            simp [h1, h2, hiff, hNl]
  rw [hset, sum_congr rfl hsummand]
  rw [hcardι, hcardκ, hmerge] at hmc
  exact hmc

/-- **The stratum `(i, j)`** (proof of `lem:oct24-collision`(a)): labelling `i` first and the
other vertices in the order `ord i j`,
`∑_{x' ∈ 𝓘⁺, x'_i = x_j, x'_ℓ ∉ x(U⁺) (ℓ ≠ i)} K_coll(x, x') ≤ w_i(x_j) ∏_{ℓ ≠ i} M_ℓ`. -/
theorem sk_collision_stratum_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : Function.Injective x) (n : ℕ) (i j : U) :
    ∑ y ∈ injLabellings F G,
        (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) ≤
      collisionW ς x i (x j) * ∏ ℓ ∈ univ.erase i, collisionM G ς ord (Fintype.card F) n i j ℓ := by
  set X : Finset F := univ.image x with hX
  set ord' := collisionOrd ord i j with hord'
  have hinj := collisionOrd_injOn ord hord i j univ
  have hq0 : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  -- locality of the weights
  have hloc : ∀ b ∈ (univ : Finset U), ∀ y y' : U → F,
      (∀ a ∈ (univ : Finset U), ord' a ≤ ord' b → y a = y' a) →
        collisionPhi ς ord x i j b y = collisionPhi ς ord x i j b y' := by
    intro b _ y y' h
    have e1 : y i = y' i := h i (mem_univ _) (by simp [hord', collisionOrd])
    have e2 : ∀ u ∈ coverRowEarlier univ ord' b, y u = y' u :=
      fun u hu => h u (mem_univ _) (mem_filter.mp hu).2.le
    have e3 : y b = y' b := h b (mem_univ _) le_rfl
    unfold collisionPhi
    refine if_congr ?_ (by rw [e3]) rfl
    rw [e1, e3]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun u hu hui => (e2 u hu) ▸ h3 u hu hui, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun u hu hui => (e2 u hu).symm ▸ h3 u hu hui, h4⟩
  -- the one-step bounds
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord' b) x' →
        ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord' b) x' b,
          collisionPhi ς ord x i j b (Function.update x' b c) ≤
            collisionM G ς ord (Fintype.card F) n i j b := by
    intro b _ x' hx'
    by_cases hbi : b = i
    · subst hbi
      simp [collisionPhi, collisionM]
    have hupd : ∀ c, collisionPhi ς ord x i j b (Function.update x' b c) =
        if (x' i = x j ∧ ∀ u ∈ coverRowEarlier univ ord' b, u ≠ i → x' u ∉ X) ∧ c ∉ X then
          collisionW ς x b c else 0 := by
      intro c
      unfold collisionPhi
      have hui : Function.update x' b c i = x' i := Function.update_of_ne (Ne.symm hbi) _ _
      have hu : ∀ u ∈ coverRowEarlier univ ord' b, Function.update x' b c u = x' u := by
        intro u hu
        have hub : u ≠ b := by
          rintro rfl
          exact lt_irrefl _ (mem_filter.mp hu).2
        exact Function.update_of_ne hub _ _
      refine if_congr ?_ (by rw [Function.update_self]) rfl
      rw [hui, Function.update_self]
      constructor
      · rintro ⟨_, h2, h3, h4⟩
        exact ⟨⟨h2, fun u huE hui' => (hu u huE) ▸ h3 u huE hui'⟩, h4⟩
      · rintro ⟨⟨h2, h3⟩, h4⟩
        exact ⟨hbi, h2, fun u huE hui' => (hu u huE).symm ▸ h3 u huE hui', h4⟩
    rw [sum_congr rfl fun c _ => hupd c]
    by_cases hcond : x' i = x j ∧ ∀ u ∈ coverRowEarlier univ ord' b, u ≠ i → x' u ∉ X
    · have hc' : ∀ c, (if (x' i = x j ∧ ∀ u ∈ coverRowEarlier univ ord' b, u ≠ i → x' u ∉ X) ∧
          c ∉ X then collisionW ς x b c else 0) = if c ∉ X then collisionW ς x b c else 0 := by
        intro c
        by_cases hcX : c ∈ X
        · rw [ite_eq_right (fun h => h.2 hcX), ite_eq_right (fun h => h hcX)]
        · rw [ite_eq_left ⟨hcond, hcX⟩, ite_eq_left hcX]
      rw [sum_congr rfl fun c _ => hc' c, ← sum_filter]
      have hiA : i ∈ coverRowEarlier univ ord' b := (collision_mem_earlier ord hbi i).mpr (Or.inl rfl)
      have h := sk_collision_oneStep_g hW G ς hς x hx (coverRowEarlier univ ord' b) b x' hx' i j hiA
        hcond.1 hcond.2 (n' := 2 * (n : ℝ)) (by positivity)
      rw [collision_t_eq G ς ord hbi] at h
      unfold collisionM
      rw [ite_eq_right hbi]
      exact h
    · simp only [hcond, false_and, ↓reduceIte, sum_const_zero]
      exact collisionM_nonneg G ς ord hq0 n i j b
  have hK : ∀ y : U → F, Feasible F G univ y → (extCount G univ y : ℝ) ≤ 1 := by
    intro y hy
    rw [extCount_univ G hy, Nat.cast_one]
  have hseg : ∀ b ∈ univ.erase i, ∀ b' ∈ (univ : Finset U), b' ∉ univ.erase i →
      ord' b' < ord' b := by
    intro b hb b' _ hb'
    have hb'i : b' = i := by
      by_contra h
      exact hb' (mem_erase.mpr ⟨h, mem_univ _⟩)
    have hbi : b ≠ i := (mem_erase.mp hb).1
    simp [hord', collisionOrd, hb'i, hbi]
  set y0 : U → F := fun _ => x j with hy0
  have hfe : Feasible F G (univ \ univ.erase i) y0 := by
    rw [sdiff_erase_self (mem_univ i)]
    refine ⟨fun a ha b hb _ => by rw [mem_singleton.mp ha, mem_singleton.mp hb], ?_⟩
    intro e he h1 h2
    have h1' := mem_singleton.mp h1
    have h2' := mem_singleton.mp h2
    have : e = (i, i) := Prod.ext h1' h2'
    exact absurd (this ▸ he) (G.loopless i)
  have hseq := coverRow_seq_upper G hinj (collisionPhi ς ord x i j)
    (collisionM G ς ord (Fintype.card F) n i j) 1
    (fun b y => by unfold collisionPhi; split_ifs
                   · exact collisionW_nonneg ς x b _
                   · exact le_rfl)
    (fun b => collisionM_nonneg G ς ord hq0 n i j b) zero_le_one hloc hstep hK
    (univ.erase i).card (univ.erase i) rfl (subset_univ _) hseg y0 hfe
  rw [one_mul, sdiff_erase_self (mem_univ i)] at hseq
  unfold coverRowExtSum at hseq
  rw [sum_filter] at hseq
  calc ∑ y ∈ injLabellings F G,
        (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ X then collisionKernel ς x y else 0)
      ≤ ∑ y ∈ injLabellings F G, collisionW ς x i (x j) *
          (if ∀ a ∈ ({i} : Finset U), y a = y0 a then
            ∏ ℓ ∈ univ.erase i, collisionPhi ς ord x i j ℓ y else 0) := by
        refine sum_le_sum fun y _ => ?_
        split_ifs with h1 h2
        · rw [collisionKernel_eq_prod, ← mul_prod_erase univ _ (mem_univ i), h1.1]
          refine mul_le_mul_of_nonneg_left (le_of_eq (prod_congr rfl fun ℓ hℓ => ?_))
            (collisionW_nonneg ς x i _)
          have hℓi : ℓ ≠ i := (mem_erase.mp hℓ).1
          unfold collisionPhi
          rw [ite_eq_left ⟨hℓi, h1.1, fun u _ hui => h1.2 u hui, h1.2 ℓ hℓi⟩]
        · exact absurd (fun a ha => by rw [mem_singleton.mp ha]; exact h1.1) h2
        · exact mul_nonneg (collisionW_nonneg ς x i _) (prod_nonneg fun ℓ _ => by
            unfold collisionPhi; split_ifs
            · exact collisionW_nonneg ς x ℓ _
            · exact le_rfl)
        · simp
    _ = collisionW ς x i (x j) * ∑ y ∈ injLabellings F G,
          (if ∀ a ∈ ({i} : Finset U), y a = y0 a then
            ∏ ℓ ∈ univ.erase i, collisionPhi ς ord x i j ℓ y else 0) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hseq (collisionW_nonneg ς x i _)

/-- **One stratum, normalized**: the sum of `K_coll(x, ·)` over the stratum `(i, j)` is at most
`(q L_int)⁻¹ a_{ij} ∏_{ℓ ≠ i} (1 + e_{t^{ij}_ℓ}(q, 2n)) · |𝓘⁺|`. -/
theorem sk_collision_stratum_ratio_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : Function.Injective x) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (i j : U) :
    ∑ y ∈ injLabellings F G,
        (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) ≤
      ((Fintype.card F : ℝ) * collisionLint G (Fintype.card F) n)⁻¹ *
        (collisionA G ς i j * ∏ ℓ ∈ univ.erase i,
          (1 + coarseError (collisionT G ς ord i j ℓ) (Fintype.card F) (2 * n))) *
        (injLabellings F G).card := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr Fintype.card_pos
  have hq0 : (0 : ℝ) < q := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set t' : U → ℕ := fun v => nbrCount G (coverRowEarlier univ (collisionOrd ord i j) v) v with ht'
  set μ : U → ℕ := fun ℓ => if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0 with hμ
  set eT : U → ℝ := fun ℓ => coarseError (collisionT G ς ord i j ℓ) q (2 * n) with heT
  set ℓf : U → ℝ := fun v => q / 2 ^ t' v * (1 - coarseError (t' v) q n) with hℓf
  have het : ∀ v, coarseError (t' v) q n ≤ coarseError (rowsDeg0 G v) q n :=
    fun v => coarseError_mono hn0 (coverRow_nbrCount_le G _ v)
  have het1 : ∀ v, 0 < 1 - coarseError (t' v) q n := fun v => by linarith [het v, hS1 v]
  have heT0 : ∀ ℓ, 0 ≤ eT ℓ := fun ℓ =>
    coarseError_nonneg (by positivity : (0 : ℝ) ≤ 2 * n) _
  have hstr := sk_collision_stratum_le_g hW G ς hς ord hord x hx n i j
  have hlow := collision_card_lower hW G ord hord hn hS1 i j
  -- `M_ℓ = c_ℓ ℓ_ℓ` with `c_ℓ = 2^{μ_ℓ}(1 + e_{t^{ij}_ℓ})/(1 - e_{t'_ℓ})`
  have hM : ∀ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ =
      (2 ^ μ ℓ * (1 + eT ℓ) / (1 - coarseError (t' ℓ) q n)) * ℓf ℓ := by
    intro ℓ hℓ
    have hℓi : ℓ ≠ i := (mem_erase.mp hℓ).1
    unfold collisionM
    rw [ite_eq_right hℓi]
    have h1 : 1 - coarseError (nbrCount G (coverRowEarlier univ (collisionOrd ord i j) ℓ) ℓ) q n
        ≠ 0 := (het1 ℓ).ne'
    simp only [hℓf, heT, hμ, ht', inv_pow]
    field_simp
  have hprodM : ∏ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ =
      (2 ^ rowsMg G ς j i * ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)) /
        (∏ ℓ ∈ univ.erase i, (1 - coarseError (t' ℓ) q n)) * ∏ ℓ ∈ univ.erase i, ℓf ℓ := by
    rw [prod_congr rfl hM, prod_mul_distrib, prod_div_distrib, prod_mul_distrib,
      prod_pow_eq_pow_sum, collision_sum_merges G ς i j]
  have hti : t' i = 0 := by
    simp only [ht', collision_earlier_self, nbrCount, filter_empty, card_empty]
  have hℓi : ℓf i = q * (1 - coarseError 0 q n) := by
    simp only [hℓf, hti, pow_zero, div_one]
  have hprodℓ : ∏ v, ℓf v = q * (1 - coarseError 0 q n) * ∏ ℓ ∈ univ.erase i, ℓf ℓ := by
    rw [← mul_prod_erase univ ℓf (mem_univ i), hℓi]
  -- `L_int ≤ (1 - e_0) ∏_{ℓ ≠ i} (1 - e_{t'_ℓ})`
  have hLle : collisionLint G q n ≤
      (1 - coarseError 0 q n) * ∏ ℓ ∈ univ.erase i, (1 - coarseError (t' ℓ) q n) := by
    unfold collisionLint
    rw [← mul_prod_erase univ _ (mem_univ i)]
    refine mul_le_mul ?_ ?_ (prod_nonneg fun v _ => by linarith [hS1 v]) ?_
    · linarith [coarseError_mono (q := q) hn0 (Nat.zero_le (rowsDeg0 G i))]
    · exact prod_le_prod₀ (fun v _ => by linarith [hS1 v]) (fun v _ => by linarith [het v])
    · linarith [coarseError_mono (q := q) hn0 (Nat.zero_le (rowsDeg0 G i)), hS1 i]
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hQpos : 0 < ∏ ℓ ∈ univ.erase i, (1 - coarseError (t' ℓ) q n) :=
    prod_pos fun v _ => het1 v
  have hP0 : 0 ≤ ∏ ℓ ∈ univ.erase i, (1 + eT ℓ) := prod_nonneg fun ℓ _ => by linarith [heT0 ℓ]
  have hℓ'0 : 0 ≤ ∏ ℓ ∈ univ.erase i, ℓf ℓ :=
    prod_nonneg fun v _ => mul_nonneg (by positivity) (het1 v).le
  have hw := collisionW_at_le ς x i j
  have hw0 := collisionW_nonneg ς x i (x j)
  have ha : collisionA G ς i j = 2 ^ (collisionR ς i - if j ∈ rowsN ς i then 1 else 0) *
      2 ^ rowsMg G ς j i := by
    unfold collisionA
    rw [pow_add]
  have he00 : 0 < 1 - coarseError 0 q n := by
    linarith [coarseError_mono (q := q) hn0 (Nat.zero_le (rowsDeg0 G i)), hS1 i]
  -- the key inequality: `w_i(x_j) ∏ M ≤ (q L)⁻¹ a ∏(1 + e) ∏ ℓ`
  have hkey : collisionW ς x i (x j) * ∏ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ ≤
      (q * collisionLint G q n)⁻¹ * (collisionA G ς i j * ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)) *
        ∏ v, ℓf v := by
    rw [hprodM, hprodℓ]
    set P := ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)
    set Q := ∏ ℓ ∈ univ.erase i, (1 - coarseError (t' ℓ) q n)
    set ℓ' := ∏ ℓ ∈ univ.erase i, ℓf ℓ
    set L := collisionLint G q n
    set w := collisionW ς x i (x j)
    set A := collisionA G ς i j
    -- `w 2^{mg} L ≤ A (1 - e_0) Q`
    have h1 : w * 2 ^ rowsMg G ς j i * L ≤ A * ((1 - coarseError 0 q n) * Q) := by
      have hA' : w * 2 ^ rowsMg G ς j i ≤ A := by
        rw [ha]
        exact mul_le_mul_of_nonneg_right hw (by positivity)
      have hA0 : 0 ≤ A := by unfold A collisionA; positivity
      calc w * 2 ^ rowsMg G ς j i * L ≤ A * L := mul_le_mul_of_nonneg_right hA' hLpos.le
        _ ≤ A * ((1 - coarseError 0 q n) * Q) := mul_le_mul_of_nonneg_left hLle hA0
    have hlhs : w * ((2 ^ rowsMg G ς j i * P) / Q * ℓ') =
        (w * 2 ^ rowsMg G ς j i * L) * (P * ℓ' / (L * Q)) := by
      field_simp
    have hrhs : (q * L)⁻¹ * (A * P) * (q * (1 - coarseError 0 q n) * ℓ') =
        (A * ((1 - coarseError 0 q n) * Q)) * (P * ℓ' / (L * Q)) := by
      field_simp
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right h1 (div_nonneg (mul_nonneg hP0 hℓ'0)
      (mul_pos hLpos hQpos).le)
  have hcoef : 0 ≤ (q * collisionLint G q n)⁻¹ *
      (collisionA G ς i j * ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)) := by
    refine mul_nonneg (inv_nonneg.mpr (mul_pos hq0 hLpos).le) (mul_nonneg ?_ hP0)
    unfold collisionA
    positivity
  calc _ ≤ collisionW ς x i (x j) * ∏ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ := hstr
    _ ≤ _ := hkey
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hcoef

/-- **`lem:oct24-collision`(a), row sums**: for every injective `x` (e.g. `x ∈ 𝓘⁺`),
`E_{x' ∼ μ}[K_coll,1(x, x')] ≤ D_1`. -/
theorem sk_collision_rowSum_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : Function.Injective x) :
    (graphLaw G hne).expect (collisionKernel1 ς x) ≤ collisionD1 G ς ord (Fintype.card F) n := by
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  rw [div_le_iff₀ hN]
  calc ∑ y ∈ injLabellings F G, collisionKernel1 ς x y
      ≤ ∑ y ∈ injLabellings F G, ∑ i, ∑ j,
          (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) := by
        refine sum_le_sum fun y hy => collisionKernel1_le_sum ς x y fun a b h => ?_
        simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
        exact hy.1 a (mem_univ _) b (mem_univ _) h
    _ = ∑ i, ∑ j, ∑ y ∈ injLabellings F G,
          (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    _ ≤ ∑ i, ∑ j, ((Fintype.card F : ℝ) * collisionLint G (Fintype.card F) n)⁻¹ *
          (collisionA G ς i j * ∏ ℓ ∈ univ.erase i,
            (1 + coarseError (collisionT G ς ord i j ℓ) (Fintype.card F) (2 * n))) *
          (injLabellings F G).card :=
        sum_le_sum fun i _ => sum_le_sum fun j _ =>
          sk_collision_stratum_ratio_g hW G ς hς ord hord x hx hn hS1 i j
    _ = collisionD1 G ς ord (Fintype.card F) n * (injLabellings F G).card := by
        unfold collisionD1
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum, sum_mul]

/-- **The one-step sum with several coincident vertices**: `x'` feasible on `A`, the vertices
`u ∈ A ∩ I` coincident (`x'_u = x_{ψ(u)}`), the others outside `x(U⁺)`. For a new vertex `ℓ`, the
sum of `w_ℓ` over its admissible labels outside `x(U⁺)` is at most
`q 2^{-t} 2^{μ} (1 + e_{t + r_ℓ - μ}(q, n'))`, with `μ` the number of labelled coincident
neighbours `u` of `ℓ` with `ψ(u) ∈ N(ℓ)` (`lem:extraction-merged-count`). -/
theorem sk_collision_oneStep_gen_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (x : U → F) (hx : Function.Injective x)
    (A : Finset U) (ℓ : U) (x' : U → F) (hx' : Feasible F G A x') (I : Finset U) (ψ : U → U)
    (hcoinc : ∀ u ∈ A, u ∈ I → x' u = x (ψ u)) (hother : ∀ u ∈ A, u ∉ I → x' u ∉ univ.image x)
    {n' : ℝ} (hn' : 0 ≤ n') :
    ∑ c ∈ (vertexAdmissible G A x' ℓ).filter (fun c => c ∉ univ.image x),
        collisionW ς x ℓ c ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ nbrCount G A ℓ *
        2 ^ ((A.filter fun u => (u, ℓ) ∈ G.E ∨ (ℓ, u) ∈ G.E).filter
          fun u => u ∈ I ∧ ψ u ∈ rowsN ς ℓ).card *
        (1 + coarseError (nbrCount G A ℓ + collisionR ς ℓ -
          ((A.filter fun u => (u, ℓ) ∈ G.E ∨ (ℓ, u) ∈ G.E).filter
            fun u => u ∈ I ∧ ψ u ∈ rowsN ς ℓ).card) (Fintype.card F) n') := by
  set X : Finset F := univ.image x with hX
  set NA := A.filter (fun u => (u, ℓ) ∈ G.E ∨ (ℓ, u) ∈ G.E) with hNA
  set Nl := rowsN ς ℓ with hNl
  let β : NA → F := fun u => x' u
  have hβ : Function.Injective β := fun u w h =>
    Subtype.ext (hx'.1 u (mem_filter.mp u.2).1 w (mem_filter.mp w.2).1 h)
  let γ : Nl → F := fun a => x a
  have hγ : Function.Injective γ := fun a a' h => Subtype.ext (hx h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : NA → ℤ := fun u => if (u.1, ℓ) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ u, s u = 1 ∨ s u = -1 := fun u => by
    simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact hm1
  let s' : Nl → ℤ := fun a => quadraticChar F (ς a.1 ℓ : F)
  have hs' : ∀ a, s' a = 1 ∨ s' a = -1 := fun a => by
    have ha : ς a.1 ℓ ≠ 0 := by simpa [hNl, rowsN] using a.2
    exact quadraticChar_dichotomy (hς a.1 ℓ ha)
  set 𝒳 : Finset F := A.image x' ∪ X with h𝒳
  have hβX : ∀ u, β u ∈ 𝒳 := fun u =>
    mem_union_left _ (mem_image_of_mem x' (mem_filter.mp u.2).1)
  have hγX : ∀ a, γ a ∈ 𝒳 := fun a => mem_union_right _ (mem_image_of_mem x (mem_univ _))
  have hmc := merged_count_le_fintype hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX hn'
  have hset : (vertexAdmissible G A x' ℓ).filter (fun y => y ∉ X) =
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
      · have hvu : (ℓ, u.1) ∈ G.E := hu.resolve_left h
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
        have hnot : (u, ℓ) ∉ G.E := G.oriented ℓ u he
        have h1 := hall ⟨u, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hsummand : ∀ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
      collisionW ς x ℓ y = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l)) := by
    intro y _
    unfold collisionW
    rw [← prod_coe_sort Nl]
    refine prod_congr rfl fun a _ => ?_
    simp only [s', γ, map_mul, Int.cast_mul]
  have hcardι : Fintype.card NA = nbrCount G A ℓ := by
    rw [Fintype.card_coe]
    rfl
  have hcardκ : Fintype.card Nl = collisionR ς ℓ := Fintype.card_coe _
  have hmerge : mergedCount β γ = (NA.filter fun u => u ∈ I ∧ ψ u ∈ rowsN ς ℓ).card := by
    unfold mergedCount
    rw [card_filter (fun u => u ∈ I ∧ ψ u ∈ rowsN ς ℓ) NA]
    calc (univ.filter fun il : NA × Nl => β il.1 = γ il.2).card
        = ∑ il : NA × Nl, if β il.1 = γ il.2 then 1 else 0 := card_filter _ _
      _ = ∑ u : NA, ∑ a : Nl, if β u = γ a then 1 else 0 := Fintype.sum_prod_type _
      _ = ∑ u : NA, ∑ a ∈ Nl, if x' u = x a then 1 else 0 :=
          sum_congr rfl fun u _ => sum_coe_sort Nl (fun a => if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, ∑ a ∈ Nl, if x' u = x a then 1 else 0 :=
          sum_coe_sort NA (fun u => ∑ a ∈ Nl, if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, if u ∈ I ∧ ψ u ∈ rowsN ς ℓ then 1 else 0 := by
          refine sum_congr rfl fun u hu => ?_
          have huA := (mem_filter.mp hu).1
          by_cases huI : u ∈ I
          · rw [hcoinc u huA huI]
            simp only [hx.eq_iff]
            rw [sum_ite_eq]
            by_cases hψ : ψ u ∈ rowsN ς ℓ <;> simp [hψ, huI, hNl]
          · simp only [huI, false_and, ↓reduceIte]
            refine sum_eq_zero fun a _ => ?_
            have hno := hother u huA huI
            have : x' u ≠ x a := fun h => hno (h ▸ mem_image_of_mem x (mem_univ a))
            simp only [this, ↓reduceIte]
  rw [hset, sum_congr rfl hsummand]
  rw [hcardι, hcardκ, hmerge] at hmc
  exact hmc

/-- **The stratum `(I, ψ)`, `|I| ≤ k`** (proof of `lem:oct24-collision`(b)): labelling `I` first
and the other vertices in the order `p = π_k`,
`∑_{x' ∈ 𝓘⁺ in the stratum} K_coll(x, x') ≤ ∏_v M_v`. -/
theorem sk_collision_stratumI_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (p : U → ℕ) (hp : Function.Injective p)
    (x : U → F) (hx : Function.Injective x) (n : ℕ) (I : Finset U) (ψ : U → U) {k : ℕ}
    (hk : I.card ≤ k) :
    ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
      ∏ v, collisionMI G ς p I ψ (Fintype.card F) n k v := by
  set X : Finset F := univ.image x with hX
  set ord' := collisionOrdI p I with hord'
  have hinj := collisionOrdI_injOn p hp I univ
  have hq0 : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  have hloc : ∀ b ∈ (univ : Finset U), ∀ y y' : U → F,
      (∀ a ∈ (univ : Finset U), ord' a ≤ ord' b → y a = y' a) →
        collisionPhiI ς p x I ψ b y = collisionPhiI ς p x I ψ b y' := by
    intro b _ y y' h
    have e3 : y b = y' b := h b (mem_univ _) le_rfl
    unfold collisionPhiI
    by_cases hbI : b ∈ I
    · simp only [hbI, ↓reduceIte, e3]
    · have e1 : ∀ l ∈ I, y l = y' l := fun l hl => h l (mem_univ _)
        (mem_filter.mp (collision_I_sub_earlier p I hbI hl)).2.le
      have e2 : ∀ u ∈ coverRowEarlier univ ord' b, y u = y' u :=
        fun u hu => h u (mem_univ _) (mem_filter.mp hu).2.le
      simp only [hbI, ↓reduceIte]
      refine if_congr ?_ (by rw [e3]) rfl
      rw [e3]
      constructor
      · rintro ⟨h1, h2, h4⟩
        exact ⟨fun l hl => (e1 l hl) ▸ h1 l hl, fun u hu huI => (e2 u hu) ▸ h2 u hu huI, h4⟩
      · rintro ⟨h1, h2, h4⟩
        exact ⟨fun l hl => (e1 l hl).symm ▸ h1 l hl,
          fun u hu huI => (e2 u hu).symm ▸ h2 u hu huI, h4⟩
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord' b) x' →
        ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord' b) x' b,
          collisionPhiI ς p x I ψ b (Function.update x' b c) ≤
            collisionMI G ς p I ψ (Fintype.card F) n k b := by
    intro b _ x' hx'
    by_cases hbI : b ∈ I
    · have hupd : ∀ c, collisionPhiI ς p x I ψ b (Function.update x' b c) =
          if c = x (ψ b) then collisionW ς x b c else 0 := by
        intro c
        unfold collisionPhiI
        simp only [hbI, ↓reduceIte, Function.update_self]
      rw [sum_congr rfl fun c _ => hupd c]
      have hle : ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord' b) x' b,
          (if c = x (ψ b) then collisionW ς x b c else 0) ≤ collisionW ς x b (x (ψ b)) := by
        rw [sum_ite_eq']
        split_ifs
        · exact le_rfl
        · exact collisionW_nonneg ς x b _
      unfold collisionMI
      rw [ite_eq_left hbI]
      exact hle.trans (collisionW_at_le ς x b (ψ b))
    · have hu : ∀ c, ∀ u ∈ coverRowEarlier univ ord' b, Function.update x' b c u = x' u := by
        intro c u hu
        have hub : u ≠ b := by
          rintro rfl
          exact lt_irrefl _ (mem_filter.mp hu).2
        exact Function.update_of_ne hub _ _
      have hl : ∀ c, ∀ l ∈ I, Function.update x' b c l = x' l := by
        intro c l hlI
        have hlb : l ≠ b := by
          rintro rfl
          exact hbI hlI
        exact Function.update_of_ne hlb _ _
      have hupd : ∀ c, collisionPhiI ς p x I ψ b (Function.update x' b c) =
          if ((∀ l ∈ I, x' l = x (ψ l)) ∧ ∀ u ∈ coverRowEarlier univ ord' b, u ∉ I →
            x' u ∉ X) ∧ c ∉ X then collisionW ς x b c else 0 := by
        intro c
        unfold collisionPhiI
        simp only [hbI, ↓reduceIte]
        refine if_congr ?_ (by rw [Function.update_self]) rfl
        rw [Function.update_self]
        constructor
        · rintro ⟨h1, h2, h4⟩
          exact ⟨⟨fun l hlI => (hl c l hlI) ▸ h1 l hlI,
            fun u huE huI => (hu c u huE) ▸ h2 u huE huI⟩, h4⟩
        · rintro ⟨⟨h1, h2⟩, h4⟩
          exact ⟨fun l hlI => (hl c l hlI).symm ▸ h1 l hlI,
            fun u huE huI => (hu c u huE).symm ▸ h2 u huE huI, h4⟩
      rw [sum_congr rfl fun c _ => hupd c]
      by_cases hcond : (∀ l ∈ I, x' l = x (ψ l)) ∧
          ∀ u ∈ coverRowEarlier univ ord' b, u ∉ I → x' u ∉ X
      · have hc' : ∀ c, (if ((∀ l ∈ I, x' l = x (ψ l)) ∧ ∀ u ∈ coverRowEarlier univ ord' b,
            u ∉ I → x' u ∉ X) ∧ c ∉ X then collisionW ς x b c else 0) =
              if c ∉ X then collisionW ς x b c else 0 := by
          intro c
          by_cases hcX : c ∈ X
          · rw [ite_eq_right (fun h => h.2 hcX), ite_eq_right (fun h => h hcX)]
          · rw [ite_eq_left ⟨hcond, hcX⟩, ite_eq_left hcX]
        rw [sum_congr rfl fun c _ => hc' c, ← sum_filter]
        have h := sk_collision_oneStep_gen_g hW G ς hς x hx (coverRowEarlier univ ord' b) b x' hx' I ψ
          (fun u _ huI => hcond.1 u huI) hcond.2 (n' := 2 * (n : ℝ)) (by positivity)
        refine h.trans ?_
        unfold collisionMI
        rw [ite_eq_right hbI]
        -- the number of distinct roots is at most `t^{(k)}_b`
        have ht0 : nbrCount G (coverRowEarlier univ ord' b) b ≤
            min (rowsDeg0 G b) (collisionB G p b + k) := by
          refine le_min (coverRow_nbrCount_le G _ b) ?_
          unfold nbrCount collisionB
          calc ((coverRowEarlier univ ord' b).filter
                fun u => (u, b) ∈ G.E ∨ (b, u) ∈ G.E).card
              ≤ (I ∪ (rowsAdj G b ∩ univ.filter fun u => p u < p b)).card := by
                refine card_le_card fun u hu => ?_
                have hu1 := (mem_filter.mp hu).1
                have hu2 := (mem_filter.mp hu).2
                rcases mem_union.mp (collision_earlierI_sub p I b hu1) with h | h
                · exact mem_union_left _ h
                · refine mem_union_right _ (mem_inter.mpr ⟨?_, h⟩)
                  simp only [rowsAdj, mem_filter, mem_univ, true_and]
                  exact hu2
            _ ≤ I.card + (rowsAdj G b ∩ univ.filter fun u => p u < p b).card := card_union_le _ _
            _ ≤ (rowsAdj G b ∩ univ.filter fun u => p u < p b).card + k := by omega
        have hroots : nbrCount G (coverRowEarlier univ ord' b) b + collisionR ς b -
            collisionMuI G ς p I ψ b ≤
              min (collisionR ς b + rowsDeg0 G b) (collisionR ς b + collisionB G p b + k) := by
          have := le_min_iff.mp ht0
          refine le_min ?_ ?_ <;> omega
        have hmono := coarseError_mono (q := (Fintype.card F : ℝ))
          (by positivity : (0 : ℝ) ≤ 2 * n) hroots
        have hpos : (0 : ℝ) ≤ Fintype.card F * (2 : ℝ)⁻¹ ^
            nbrCount G (coverRowEarlier univ ord' b) b * 2 ^ collisionMuI G ς p I ψ b := by
          positivity
        unfold collisionMuI at hmono hpos ⊢
        exact mul_le_mul_of_nonneg_left (by linarith) hpos
      · simp only [hcond, false_and, ↓reduceIte, sum_const_zero]
        exact collisionMI_nonneg G ς p I ψ hq0 n k b
  have hK : ∀ y : U → F, Feasible F G univ y → (extCount G univ y : ℝ) ≤ 1 := by
    intro y hy
    rw [extCount_univ G hy, Nat.cast_one]
  have hfe : Feasible F G (univ \ univ) (fun _ => (0 : F)) := by
    rw [Finset.sdiff_self]
    exact ⟨by simp, by simp⟩
  have hseq := coverRow_seq_upper G hinj (collisionPhiI ς p x I ψ)
    (collisionMI G ς p I ψ (Fintype.card F) n k) 1
    (fun b y => collisionPhiI_nonneg ς p x I ψ b y)
    (fun b => collisionMI_nonneg G ς p I ψ hq0 n k b) zero_le_one hloc hstep hK
    (univ : Finset U).card univ rfl subset_rfl (fun _ _ b' _ hb' => absurd (mem_univ b') hb')
    (fun _ => (0 : F)) hfe
  rw [one_mul, Finset.sdiff_self, coverRowExtSum_empty] at hseq
  refine le_trans (sum_le_sum fun y _ => ?_) hseq
  split_ifs with h1
  · rw [collisionKernel_eq_prod]
    refine le_of_eq (prod_congr rfl fun v _ => ?_)
    unfold collisionPhiI
    by_cases hvI : v ∈ I
    · rw [ite_eq_left hvI, ite_eq_left (h1.1 v hvI)]
    · rw [ite_eq_right hvI, ite_eq_left ⟨h1.1, fun u _ huI => h1.2 u huI, h1.2 v hvI⟩]
  · exact prod_nonneg fun v _ => collisionPhiI_nonneg ς p x I ψ v y

/-- **One stratum `(I, ψ)`, normalized** (proof of `lem:oct24-collision`(b)): with `k = |I|`
and the order `π_k`, the stratum sum of `K_coll(x, ·)` is at most
`L_int⁻¹ Υ_k q^{-k} 2^{kΔ⁺/2} ∏_{l ∈ I} a_{l, ψ(l)} · |𝓘⁺|`. -/
theorem sk_collision_stratumI_ratio_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) (x : U → F) (hx : Function.Injective x) {n : ℕ}
    (hn : Fintype.card U ≤ n) (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1)
    (I : Finset U) (ψ : U → U) :
    ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
      (collisionLint G (Fintype.card F) n)⁻¹ * collisionUpsK G ς π (Fintype.card F) n I.card *
        ((Fintype.card F : ℝ)⁻¹ ^ I.card * Real.sqrt 2 ^ (I.card * collisionDeltaPlus G) *
          ∏ l ∈ I, collisionA G ς l (ψ l)) * (injLabellings F G).card := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr Fintype.card_pos
  have hq0 : (0 : ℝ) < q := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set k := I.card with hk
  set p := π k with hp
  set o := collisionOrdI p I with ho
  set t' : U → ℕ := fun v => nbrCount G (coverRowEarlier univ o v) v with ht'
  set eK : U → ℝ := fun v => coarseError (collisionTk G ς π k v) q (2 * n) with heK
  have het : ∀ v, coarseError (t' v) q n ≤ coarseError (rowsDeg0 G v) q n :=
    fun v => coarseError_mono hn0 (coverRow_nbrCount_le G _ v)
  have het1 : ∀ v, 0 < 1 - coarseError (t' v) q n := fun v => by linarith [het v, hS1 v]
  have heK0 : ∀ v, 0 ≤ eK v := fun v => coarseError_nonneg (by positivity : (0 : ℝ) ≤ 2 * n) _
  have hstr := sk_collision_stratumI_le_g hW G ς hς p (hπ k) x hx n I ψ (le_refl k)
  have hlow := collision_card_lower_gen hW G o (collisionOrdI_injOn p (hπ k) I univ) hn hS1
  set ℓf : U → ℝ := fun v => q / 2 ^ t' v * (1 - coarseError (t' v) q n) with hℓf
  set num : U → ℝ := fun v => if v ∈ I then
      2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0) * 2 ^ t' v * q⁻¹
    else 2 ^ collisionMuI G ς p I ψ v * (1 + eK v) with hnum
  -- `M_v = (num_v / (1 - e_{t'_v})) ℓ_v`
  have hM : ∀ v, collisionMI G ς p I ψ q n k v = num v / (1 - coarseError (t' v) q n) * ℓf v := by
    intro v
    have h1 := (het1 v).ne'
    unfold collisionMI
    by_cases hv : v ∈ I
    · rw [ite_eq_left hv]
      simp only [hnum, hℓf, hv, ↓reduceIte]
      field_simp
    · rw [ite_eq_right hv]
      simp only [hnum, hℓf, hv, ↓reduceIte, heK, collisionTk, inv_pow]
      field_simp
      simp only [ht', hp, ho]
      ring
  have hprodM : ∏ v, collisionMI G ς p I ψ q n k v =
      (∏ v, num v) / (∏ v, (1 - coarseError (t' v) q n)) * ∏ v, ℓf v := by
    rw [prod_congr rfl fun v _ => hM v, prod_mul_distrib, prod_div_distrib]
  have hLle : collisionLint G q n ≤ ∏ v, (1 - coarseError (t' v) q n) :=
    prod_le_prod₀ (fun v _ => by linarith [hS1 v]) (fun v _ => by linarith [het v])
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hfilt : univ.filter (fun v => v ∈ I) = I := by
    ext v
    simp
  -- the numerator
  have hnum_le : ∏ v, num v ≤ collisionUpsK G ς π q n k *
      (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G) * ∏ l ∈ I, collisionA G ς l (ψ l)) := by
    have hsplit : ∏ v, num v = (∏ v ∈ I, (2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0) *
        2 ^ t' v * q⁻¹)) * ∏ v ∈ univ.filter (fun v => v ∉ I),
          (2 ^ collisionMuI G ς p I ψ v * (1 + eK v)) := by
      simp only [hnum]
      rw [prod_ite, hfilt]
    have hI : ∏ v ∈ I, (2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0) * 2 ^ t' v * q⁻¹) =
        (∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
          (2 : ℝ) ^ (∑ v ∈ I, t' v) * q⁻¹ ^ k := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, ← prod_pow_eq_pow_sum]
    have hJ : ∏ v ∈ univ.filter (fun v => v ∉ I), (2 ^ collisionMuI G ς p I ψ v * (1 + eK v)) =
        (2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) *
          ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum]
    -- the pieces
    have hP1 : (2 : ℝ) ^ (∑ v ∈ I, t' v) ≤ Real.sqrt 2 ^ (k * collisionDeltaPlus G) := by
      have hh : 2 * ∑ v ∈ I, t' v ≤ k * collisionDeltaPlus G := collision_handshake G p I
      have h2 : (2 : ℝ) ^ (∑ v ∈ I, t' v) = Real.sqrt 2 ^ (2 * ∑ v ∈ I, t' v) := by
        rw [pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [h2]
      exact pow_le_pow_right₀ (Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)) hh
    have hP2 : (2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) ≤
        ∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l := by
      rw [prod_pow_eq_pow_sum]
      exact pow_le_pow_right₀ (by norm_num) (collision_sum_muI_le G ς p I ψ)
    have hP3 : ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) ≤ collisionUpsK G ς π q n k := by
      unfold collisionUpsK
      rw [← prod_filter_mul_prod_filter_not univ (fun v => v ∈ I)]
      refine le_mul_of_one_le_left (prod_nonneg fun v _ => by linarith [heK0 v]) ?_
      exact one_le_prod₀ fun v _ => by linarith [heK0 v]
    have hP4 : ∏ l ∈ I, collisionA G ς l (ψ l) =
        (∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
          ∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun l _ => ?_
      unfold collisionA
      rw [pow_add]
    have hA0 : 0 ≤ ∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0) := by
      positivity
    have hU0 : 0 ≤ ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) :=
      prod_nonneg fun v _ => by linarith [heK0 v]
    have hq0' : 0 ≤ q⁻¹ ^ k := by positivity
    calc ∏ v, num v
        = ((∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
            (2 : ℝ) ^ (∑ v ∈ I, t' v) * q⁻¹ ^ k) *
          ((2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) *
            ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v)) := by
          rw [hsplit, hI, hJ]
      _ ≤ ((∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
            Real.sqrt 2 ^ (k * collisionDeltaPlus G) * q⁻¹ ^ k) *
          ((∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l) * collisionUpsK G ς π q n k) := by
          refine mul_le_mul ?_ ?_ (mul_nonneg (by positivity) hU0) (by positivity)
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP1 hA0) hq0'
          · exact mul_le_mul hP2 hP3 hU0 (by positivity)
      _ = _ := by rw [hP4]; ring
  have hnum0 : 0 ≤ ∏ v, num v := prod_nonneg fun v _ => by
    by_cases hv : v ∈ I
    · simp only [hnum, hv, ↓reduceIte]
      positivity
    · simp only [hnum, hv, ↓reduceIte]
      exact mul_nonneg (by positivity) (by linarith [heK0 v])
  have hQpos : 0 < ∏ v, (1 - coarseError (t' v) q n) := prod_pos fun v _ => het1 v
  have hℓ0 : 0 ≤ ∏ v, ℓf v := prod_nonneg fun v _ => mul_nonneg (by positivity) (het1 v).le
  have hC0 : 0 ≤ (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
      (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G) * ∏ l ∈ I, collisionA G ς l (ψ l)) := by
    have hU : 0 ≤ collisionUpsK G ς π q n k :=
      prod_nonneg fun v _ => by linarith [heK0 v]
    have hA : 0 ≤ ∏ l ∈ I, collisionA G ς l (ψ l) :=
      prod_nonneg fun l _ => by unfold collisionA; positivity
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hLpos.le) hU) (by positivity)
  calc _ ≤ ∏ v, collisionMI G ς p I ψ q n k v := hstr
    _ = (∏ v, num v) / (∏ v, (1 - coarseError (t' v) q n)) * ∏ v, ℓf v := hprodM
    _ ≤ (∏ v, num v) / collisionLint G q n * ∏ v, ℓf v := by
        refine mul_le_mul_of_nonneg_right ?_ hℓ0
        exact div_le_div_of_nonneg_left hnum0 hLpos hLle
    _ ≤ (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
          (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G) * ∏ l ∈ I, collisionA G ς l (ψ l)) *
          ∏ v, ℓf v := by
        refine mul_le_mul_of_nonneg_right ?_ hℓ0
        rw [div_eq_inv_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left hnum_le (inv_nonneg.mpr hLpos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hC0

/-- **`lem:oct24-collision`(b), row sums**: for every injective `x`,
`E_{x' ∼ μ}[K_coll,≥2(x, x')] ≤ D_{≥2}`. -/
theorem sk_collision_rowSum2_le_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) (x : U → F) (hx : Function.Injective x) :
    (graphLaw G hne).expect (collisionKernel2 ς x) ≤ collisionD2 G ς π (Fintype.card F) n := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set N : ℝ := ((injLabellings F G).card : ℝ) with hNdef
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < N := by
    rw [hNdef]
    exact_mod_cast card_pos.mpr hne
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  rw [div_le_iff₀ hN]
  set c : ℕ → ℝ := fun k => (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
    (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G)) with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by
    have hU : 0 ≤ collisionUpsK G ς π q n k := prod_nonneg fun v _ => by
      have := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n)
        (collisionTk G ς π k v)
      linarith
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hLpos.le) hU) (by positivity)
  calc ∑ y ∈ injLabellings F G, collisionKernel2 ς x y
      ≤ ∑ y ∈ injLabellings F G, ∑ k ∈ Icc 2 (Fintype.card U),
          ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        refine sum_le_sum fun y hy => collisionKernel2_le_sum ς x y fun a b h => ?_
        simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
        exact hy.1 a (mem_univ _) b (mem_univ _) h
    _ = ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          ∑ y ∈ injLabellings F G,
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun I _ => ?_
        rw [sum_comm]
    _ ≤ ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          c k * (∏ l ∈ I, collisionA G ς l (collisionExt I ψ l)) * N := by
        refine sum_le_sum fun k _ => sum_le_sum fun I hI => sum_le_sum fun ψ _ => ?_
        have hIk : I.card = k := (mem_powersetCard.mp hI).2
        have h := sk_collision_stratumI_ratio_g hW G ς hς π hπ x hx hn hS1 I (collisionExt I ψ)
        rw [hIk] at h
        refine h.trans (le_of_eq ?_)
        simp only [hc]
        ring
    _ = ∑ k ∈ Icc 2 (Fintype.card U), c k * N * (∑ I ∈ (univ : Finset U).powersetCard k,
          ∑ ψ : (I → U), ∏ l ∈ I, collisionA G ς l (collisionExt I ψ l)) := by
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun I _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun ψ _ => ?_
        ring
    _ ≤ ∑ k ∈ Icc 2 (Fintype.card U), c k * N *
          ((∑ i, ∑ j, collisionA G ς i j) ^ k / (k.factorial : ℝ)) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (collision_sum_strata G ς k)
          (mul_nonneg (hc0 k) hN.le)
    _ = collisionD2 G ς π q n * N := by
        unfold collisionD2 collisionXi
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        simp only [hc]
        rw [mul_pow, mul_pow, ← pow_mul, mul_comm (collisionDeltaPlus G) k]
        ring

/-- The signs restricted to `T` and multiplied by `ν` at the pairs with a negative coefficient. -/
noncomputable def skCollSgnN (ς : U → U → ℤ) (D : U × U → ℝ) (T : Finset (U × U)) (ν : ℤ) :
    U → U → ℤ :=
  fun j k => if (j, k) ∈ T then (if D (j, k) < 0 then ν * ς j k else ς j k) else 0

theorem sk_collCross_sgnN (ς : U → U → ℤ) (D : U × U → ℝ) {T : Finset (U × U)}
    (hT : T ⊆ collisionCross ς) {ν : ℤ} (hν0 : ν ≠ 0) :
    collisionCross (skCollSgnN ς D T ν) = T := by
  ext e
  unfold collisionCross skCollSgnN
  simp only [mem_filter, mem_univ, true_and, Prod.mk.eta]
  constructor
  · intro h
    by_contra he
    simp [he] at h
  · intro he
    have hς : ς e.1 e.2 ≠ 0 := by
      have := hT he
      unfold collisionCross at this
      simpa using this
    simp only [he, ↓reduceIte]
    split_ifs
    · exact mul_ne_zero hν0 hς
    · exact hς

omit [Fintype F] [DecidableEq F] [Fintype U] in
theorem sk_collSgnN_castF {ς : U → U → ℤ} (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0)
    (D : U × U → ℝ) (T : Finset (U × U)) {ν : ℤ} (hνF : ((ν : ℤ) : F) ≠ 0) (j k : U) :
    skCollSgnN ς D T ν j k ≠ 0 → ((skCollSgnN ς D T ν j k : ℤ) : F) ≠ 0 := by
  unfold skCollSgnN
  split_ifs
  · intro h
    have : ς j k ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    push_cast
    exact mul_ne_zero hνF (hς j k this)
  · exact hς j k
  · intro h
    exact absurd rfl h

theorem sk_rowsN_collSgnN_subset (ς : U → U → ℤ) (D : U × U → ℝ) (T : Finset (U × U)) (ν : ℤ)
    (i : U) : rowsN (skCollSgnN ς D T ν) i ⊆ rowsN ς i := by
  intro j hj
  unfold rowsN skCollSgnN at *
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  intro h0
  apply hj
  split_ifs <;> simp [h0]

omit [Fintype U] in
theorem sk_coll_flipN_identity (ς : U → U → ℤ) (D : U × U → ℝ) {T : Finset (U × U)}
    {e : U × U} (he : e ∈ T) {ν : ℤ} (hν : quadraticChar F ((ν : ℤ) : F) = -1) (x x' : U → F) :
    1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) =
      |D e| * (1 + (quadraticChar F ((skCollSgnN ς D T ν e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) +
        (1 - |D e|) := by
  by_cases hD : D e < 0
  · have hflip : (quadraticChar F ((skCollSgnN ς D T ν e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) =
        -(quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) := by
      unfold skCollSgnN
      simp only [Prod.mk.eta, he, hD, ↓reduceIte]
      push_cast
      rw [mul_assoc, map_mul, hν]
      push_cast
      ring
    rw [hflip, abs_of_neg hD]
    ring
  · push Not at hD
    have hflip : (quadraticChar F ((skCollSgnN ς D T ν e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) =
        (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ) := by
      unfold skCollSgnN
      have : ¬ (D e < 0) := not_lt.mpr hD
      simp only [Prod.mk.eta, he, this, ↓reduceIte]
    rw [hflip, abs_of_nonneg hD]
    ring

/-- **The convex decomposition** of the soft collision kernel. -/
theorem sk_collKer1_expandN (ς : U → U → ℤ) (D : U × U → ℝ)
    {ν : ℤ} (hν : quadraticChar F ((ν : ℤ) : F) = -1) (x x' : U → F) :
    skCollKer1 ς D x x' = ∑ T ∈ (collisionCross ς).powerset,
      skW D (collisionCross ς) T * collisionKernel1 (skCollSgnN ς D T ν) x x' := by
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν
  unfold skCollKer1 collisionKernel1
  split_ifs with h
  · have hF : ∏ e ∈ collisionCross ς,
        (1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) =
        ∏ e ∈ collisionCross ς, (|D e| * (1 + (quadraticChar F
          ((skCollSgnN ς D (collisionCross ς) ν e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) +
            (1 - |D e|)) :=
      prod_congr rfl fun e he => sk_coll_flipN_identity ς D he hν x x'
    rw [hF, prod_add]
    refine sum_congr rfl fun T hT => ?_
    rw [mem_powerset] at hT
    unfold collisionKernel skW
    rw [sk_collCross_sgnN ς D hT hν0, prod_mul_distrib]
    have hTe : ∏ e ∈ T, (1 + (quadraticChar F
        ((skCollSgnN ς D (collisionCross ς) ν e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) =
        ∏ e ∈ T, (1 + (quadraticChar F ((skCollSgnN ς D T ν e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) := by
      refine prod_congr rfl fun e he => ?_
      unfold skCollSgnN
      simp only [Prod.mk.eta, he, hT he, ↓reduceIte]
    rw [hTe]
    ring
  · simp

/-- **The convex decomposition** of the soft collision kernel. -/
theorem sk_collKer2_expandN (ς : U → U → ℤ) (D : U × U → ℝ)
    {ν : ℤ} (hν : quadraticChar F ((ν : ℤ) : F) = -1) (x x' : U → F) :
    skCollKer2 ς D x x' = ∑ T ∈ (collisionCross ς).powerset,
      skW D (collisionCross ς) T * collisionKernel2 (skCollSgnN ς D T ν) x x' := by
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν
  unfold skCollKer2 collisionKernel2
  split_ifs with h
  · have hF : ∏ e ∈ collisionCross ς,
        (1 + D e * (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) =
        ∏ e ∈ collisionCross ς, (|D e| * (1 + (quadraticChar F
          ((skCollSgnN ς D (collisionCross ς) ν e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) +
            (1 - |D e|)) :=
      prod_congr rfl fun e he => sk_coll_flipN_identity ς D he hν x x'
    rw [hF, prod_add]
    refine sum_congr rfl fun T hT => ?_
    rw [mem_powerset] at hT
    unfold collisionKernel skW
    rw [sk_collCross_sgnN ς D hT hν0, prod_mul_distrib]
    have hTe : ∏ e ∈ T, (1 + (quadraticChar F
        ((skCollSgnN ς D (collisionCross ς) ν e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) =
        ∏ e ∈ T, (1 + (quadraticChar F ((skCollSgnN ς D T ν e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)) := by
      refine prod_congr rfl fun e he => ?_
      unfold skCollSgnN
      simp only [Prod.mk.eta, he, hT he, ↓reduceIte]
    rw [hTe]
    ring
  · simp

/-- Row sums of the soft collision kernel (`lem:oct24-collision`(a)): `E_{x'} K^D_1(x, x') ≤ D_1`. -/
theorem sk_coll_rowSum_le_gN (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) {ν : ℤ} (hν : quadraticChar F ((ν : ℤ) : F) = -1)
    (x : U → F) (hx : Function.Injective x) :
    ∑ x' ∈ injLabellings F G, skCollKer1 ς D x x' / (injLabellings F G).card ≤
      collisionD1 G ς ord (Fintype.card F) n := by
  have hνF : ((ν : ℤ) : F) ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at hν
    norm_num at hν
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hw0 : ∀ T ∈ (collisionCross ς).powerset, 0 ≤ skW D (collisionCross ς) T :=
    fun T _ => skW_nonneg (fun e _ => hD e) T
  have hT : ∀ T ∈ (collisionCross ς).powerset,
      ∑ x' ∈ injLabellings F G, collisionKernel1 (skCollSgnN ς D T ν) x x' /
        (injLabellings F G).card ≤ collisionD1 G ς ord (Fintype.card F) n := by
    intro T _
    have h := sk_collision_rowSum_le_g hW G (skCollSgnN ς D T ν) (sk_collSgnN_castF hς D T hνF) hne hn hS1 ord
      hord x hx
    rw [coverRow_expect_graphLaw] at h
    rw [← sum_div]
    exact h.trans (sk_collisionD1_mono G (sk_rowsN_collSgnN_subset ς D T ν) ord hq hS1)
  simp only [sk_collKer1_expandN ς D hν x]
  calc ∑ x' ∈ injLabellings F G, (∑ T ∈ (collisionCross ς).powerset,
        skW D (collisionCross ς) T * collisionKernel1 (skCollSgnN ς D T ν) x x') /
          (injLabellings F G).card
      = ∑ T ∈ (collisionCross ς).powerset, skW D (collisionCross ς) T *
          ∑ x' ∈ injLabellings F G, collisionKernel1 (skCollSgnN ς D T ν) x x' /
            (injLabellings F G).card := by
        simp only [sum_div, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun T _ => sum_congr rfl fun x' _ => by ring
    _ ≤ ∑ T ∈ (collisionCross ς).powerset, skW D (collisionCross ς) T *
          collisionD1 G ς ord (Fintype.card F) n :=
        sum_le_sum fun T hT' => mul_le_mul_of_nonneg_left (hT T hT') (hw0 T hT')
    _ = _ := by rw [← sum_mul, skW_sum, one_mul]

/-- Row sums of the soft collision kernel with at least two common labels: `≤ D_{≥2}`. -/
theorem sk_coll_rowSum2_le_gN (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) {ν : ℤ} (hν : quadraticChar F ((ν : ℤ) : F) = -1)
    (x : U → F) (hx : Function.Injective x) :
    ∑ x' ∈ injLabellings F G, skCollKer2 ς D x x' / (injLabellings F G).card ≤
      collisionD2 G ς π (Fintype.card F) n := by
  have hνF : ((ν : ℤ) : F) ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at hν
    norm_num at hν
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hw0 : ∀ T ∈ (collisionCross ς).powerset, 0 ≤ skW D (collisionCross ς) T :=
    fun T _ => skW_nonneg (fun e _ => hD e) T
  have hT : ∀ T ∈ (collisionCross ς).powerset,
      ∑ x' ∈ injLabellings F G, collisionKernel2 (skCollSgnN ς D T ν) x x' /
        (injLabellings F G).card ≤ collisionD2 G ς π (Fintype.card F) n := by
    intro T _
    have h := sk_collision_rowSum2_le_g hW G (skCollSgnN ς D T ν) (sk_collSgnN_castF hς D T hνF) hne hn hS1 π
      hπ x hx
    rw [coverRow_expect_graphLaw] at h
    rw [← sum_div]
    exact h.trans (sk_collisionD2_mono G (sk_rowsN_collSgnN_subset ς D T ν) π hq hS1)
  simp only [sk_collKer2_expandN ς D hν x]
  calc ∑ x' ∈ injLabellings F G, (∑ T ∈ (collisionCross ς).powerset,
        skW D (collisionCross ς) T * collisionKernel2 (skCollSgnN ς D T ν) x x') /
          (injLabellings F G).card
      = ∑ T ∈ (collisionCross ς).powerset, skW D (collisionCross ς) T *
          ∑ x' ∈ injLabellings F G, collisionKernel2 (skCollSgnN ς D T ν) x x' /
            (injLabellings F G).card := by
        simp only [sum_div, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun T _ => sum_congr rfl fun x' _ => by ring
    _ ≤ ∑ T ∈ (collisionCross ς).powerset, skW D (collisionCross ς) T *
          collisionD2 G ς π (Fintype.card F) n :=
        sum_le_sum fun T hT' => mul_le_mul_of_nonneg_left (hT T hT') (hw0 T hT')
    _ = _ := by rw [← sum_mul, skW_sum, one_mul]

/-- **`cor:soft-kernels`(b), all coefficients**: `sk_soft_collision_opBound` for every `|D_e| ≤ 1`, given an integer
`ν` with `χ(ν) = -1`. -/
theorem sk_soft_collision_opBound_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (ν : ℤ) (hν : quadraticChar F ((ν : ℤ) : F) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKer1 ς D x x' / (injLabellings F G).card)
      (collisionD1 G ς ord (Fintype.card F) n) := by
  have hςF : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0 := fun j k h0 => by
    rcases hς j k with h | h | h
    · exact absurd h h0
    · rw [h]; simp
    · rw [h]; simp
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hinj : ∀ x ∈ injLabellings F G, Function.Injective x := fun x hx a b h => by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      skCollKer1 ς D x x' / (injLabellings F G).card ≤ collisionD1 G ς ord (Fintype.card F) n :=
    fun x hx => sk_coll_rowSum_le_gN hW G ς hςF hne hn hS1 ord hord D hD hν x (hinj x hx)
  have hsupp : ∀ i, rowsN (skT ς) i = rowsN ς i := by
    intro i
    unfold rowsN skT
    exact filter_congr fun j _ => by rw [hanti i j]
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      skCollKer1 ς D x x' / (injLabellings F G).card ≤ collisionD1 G ς ord (Fintype.card F) n := by
    intro x' hx'
    have h := sk_coll_rowSum_le_gN hW G (skT ς) (skT_castF ς hςF) hne hn hS1 ord hord
      (fun e => D e.swap) (fun e => hD e.swap) hν x' (hinj x' hx')
    rw [sk_collisionD1_congr G hsupp] at h
    calc ∑ x ∈ injLabellings F G, skCollKer1 ς D x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, skCollKer1 (skT ς) (fun e => D e.swap) x' x /
            (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [sk_collKer1_swap]
      _ ≤ _ := h
  obtain ⟨x0, hx0⟩ := hne
  have hD1 : 0 ≤ collisionD1 G ς ord (Fintype.card F) n :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (sk_collKer1_nonneg ς D hD x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (sk_collKer1_nonneg ς D hD x x') hN.le) hD1 hD1 hrow hcol
  rwa [Real.sqrt_mul_self hD1] at h

/-- **`cor:soft-kernels`(b), all coefficients**: `sk_soft_collision_opBound2` for every `|D_e| ≤ 1`, given an integer
`ν` with `χ(ν) = -1`. -/
theorem sk_soft_collision_opBound2_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (ν : ℤ) (hν : quadraticChar F ((ν : ℤ) : F) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKer2 ς D x x' / (injLabellings F G).card)
      (collisionD2 G ς π (Fintype.card F) n) := by
  have hςF : ∀ j k, ς j k ≠ 0 → ((ς j k : ℤ) : F) ≠ 0 := fun j k h0 => by
    rcases hς j k with h | h | h
    · exact absurd h h0
    · rw [h]; simp
    · rw [h]; simp
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hinj : ∀ x ∈ injLabellings F G, Function.Injective x := fun x hx a b h => by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      skCollKer2 ς D x x' / (injLabellings F G).card ≤ collisionD2 G ς π (Fintype.card F) n :=
    fun x hx => sk_coll_rowSum2_le_gN hW G ς hςF hne hn hS1 π hπ D hD hν x (hinj x hx)
  have hsupp : ∀ i, rowsN (skT ς) i = rowsN ς i := by
    intro i
    unfold rowsN skT
    exact filter_congr fun j _ => by rw [hanti i j]
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      skCollKer2 ς D x x' / (injLabellings F G).card ≤ collisionD2 G ς π (Fintype.card F) n := by
    intro x' hx'
    have h := sk_coll_rowSum2_le_gN hW G (skT ς) (skT_castF ς hςF) hne hn hS1 π hπ
      (fun e => D e.swap) (fun e => hD e.swap) hν x' (hinj x' hx')
    rw [sk_collisionD2_congr G hsupp] at h
    calc ∑ x ∈ injLabellings F G, skCollKer2 ς D x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, skCollKer2 (skT ς) (fun e => D e.swap) x' x /
            (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [sk_collKer2_swap]
      _ ≤ _ := h
  obtain ⟨x0, hx0⟩ := hne
  have hD1 : 0 ≤ collisionD2 G ς π (Fintype.card F) n :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (sk_collKer2_nonneg ς D hD x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (sk_collKer2_nonneg ς D hD x x') hN.le) hD1 hD1 hrow hcol
  rwa [Real.sqrt_mul_self hD1] at h

/-- **`cor:soft-kernels`(b), all coefficients**: `sk_soft_collision_opBound_sum` for every `|D_e| ≤ 1`, given `ν` with
`χ(ν) = -1`. -/
theorem sk_soft_collision_opBound_sum_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (ν : ℤ) (hν : quadraticChar F ((ν : ℤ) : F) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKerColl ς D x x' / (injLabellings F G).card)
      (collisionD1 G ς ord (Fintype.card F) n + collisionD2 G ς π (Fintype.card F) n) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := sk_soft_collision_opBound_g hW G ς hς hanti hne hn hS1 ord hord D hD ν hν
  have h2 := sk_soft_collision_opBound2_g hW G ς hς hanti hne hn hS1 π hπ D hD ν hν
  have hsum := Sarkozy.Influence.OpBound.add h1 h2 (collisionD1_nonneg G ς ord hq0 hS1)
    (collisionD2_nonneg G ς π hq0 hS1)
  have heq : (fun (x x' : U → F) => skCollKerColl ς D x x' / (injLabellings F G).card) =
      (fun (x x' : U → F) => skCollKer1 ς D x x' / (injLabellings F G).card +
        skCollKer2 ς D x x' / (injLabellings F G).card) := by
    funext x x'
    rw [sk_collKerColl_eq, add_div]
  rw [heq]
  exact hsum

/-- **`cor:soft-kernels`(b), all coefficients**: `sk_soft_collision_opBound_natural` for every `|D_e| ≤ 1`, given `ν` with
`χ(ν) = -1`. -/
theorem sk_soft_collision_opBound_natural_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (ν : ℤ) (hν : quadraticChar F ((ν : ℤ) : F) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKerColl ς D x x' / (injLabellings F G).card)
      (collisionDnat G ς (Fintype.card F) n) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := sk_soft_collision_opBound_g hW G ς hς hanti hne hn hS1 ord hord D hD ν hν
  have h2 := sk_soft_collision_opBound2_g hW G ς hς hanti hne hn hS1 π hπ D hD ν hν
  have hD1 := collisionD1_nonneg G ς ord hq0 hS1
  have hD2 := collisionD2_nonneg G ς π hq0 hS1
  have hsum := Sarkozy.Influence.OpBound.add h1 h2 hD1 hD2
  have heq : (fun (x x' : U → F) => skCollKerColl ς D x x' / (injLabellings F G).card) =
      (fun (x x' : U → F) => skCollKer1 ς D x x' / (injLabellings F G).card +
        skCollKer2 ς D x x' / (injLabellings F G).card) := by
    funext x x'
    rw [sk_collKerColl_eq, add_div]
  rw [heq]
  refine hsum.mono (add_nonneg hD1 hD2) ?_
  have hc1 := collisionD1_le G ς ord hq0 hS1
  have hc2 := collisionD2_le G ς π hq0 hS1
  have hL : 0 < collisionLint G (Fintype.card F) n := prod_pos fun v _ => by linarith [hS1 v]
  unfold collisionDnat
  have hrw : collisionUps G ς (Fintype.card F) n * ((Fintype.card F : ℝ) *
      collisionLint G (Fintype.card F) n)⁻¹ * ∑ i, ∑ j, collisionA G ς i j =
      collisionUps G ς (Fintype.card F) n / collisionLint G (Fintype.card F) n *
        ((Fintype.card F : ℝ)⁻¹ * ∑ i, ∑ j, collisionA G ς i j) := by
    field_simp
  rw [hrw] at hc1
  nlinarith [hc1, hc2]

/-- **`cor:soft-kernels`(b), all coefficients**: `sk_soft_collision_opBound_ord` for every `|D_e| ≤ 1`, given `ν` with
`χ(ν) = -1`. -/
theorem sk_soft_collision_opBound_ord_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (ν : ℤ) (hν : quadraticChar F ((ν : ℤ) : F) = -1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKerColl ς D x x' / (injLabellings F G).card)
      (collisionDord G ς ord (Fintype.card F) n) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine (sk_soft_collision_opBound_sum_g hW G ς hς hanti hne hn hS1 ord hord π hπ D hD ν hν).mono
    (add_nonneg (collisionD1_nonneg G ς ord hq0 hS1) (collisionD2_nonneg G ς π hq0 hS1)) ?_
  unfold collisionDord
  linarith [collisionD2_le G ς π hq0 hS1]

/-- **`cor:soft-kernels`(b), all coefficients**: `sk_soft_collision_opBound_tailForm` for every `|D_e| ≤ 1`, given `ν` with
`χ(ν) = -1`. -/
theorem sk_soft_collision_opBound_tailForm_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) (ν : ℤ) (hν : quadraticChar F ((ν : ℤ) : F) = -1) {k₀ : ℕ} (h2 : 2 ≤ k₀)
    (hk₀ : collisionDeltaPlus G ≤ k₀) (hΞ : collisionXi G ς (Fintype.card F) < k₀ + 1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => skCollKerColl ς D x x' / (injLabellings F G).card)
      (collisionD1 G ς ord (Fintype.card F) n +
        ((collisionLint G (Fintype.card F) n)⁻¹ * ∑ k ∈ Ico 2 k₀,
          collisionUpsK G ς π (Fintype.card F) n k *
            (collisionXi G ς (Fintype.card F) ^ k / (k.factorial : ℝ)) +
        collisionUps G ς (Fintype.card F) n / collisionLint G (Fintype.card F) n *
          (collisionXi G ς (Fintype.card F) ^ k₀ / (k₀.factorial : ℝ)) *
            (1 - collisionXi G ς (Fintype.card F) / (k₀ + 1))⁻¹)) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine (sk_soft_collision_opBound_sum_g hW G ς hς hanti hne hn hS1 ord hord π hπ D hD ν hν).mono
    (add_nonneg (collisionD1_nonneg G ς ord hq0 hS1) (collisionD2_nonneg G ς π hq0 hS1)) ?_
  linarith [collisionD2_le_tail G ς π hq0 hS1 h2 hk₀ hΞ]

end SkCollG

section SkCollZMod

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`cor:soft-kernels`(b) over `𝔽_p`, `p` odd, all coefficients `|D_e| ≤ 1`**: the natural
bound `D_nat` of `lem:oct24-collision`(d) (`eq:collision-natural`) for the soft collision
operator `T^D_coll`, with no condition on the coefficients. -/
theorem sk_soft_collision_opBound_natural_zmod (hp2 : p ≠ 2) (hW : WeilBound (ZMod p))
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card (ZMod p)) n < 1)
    (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) :
    Sarkozy.Influence.OpBound (injLabellings (ZMod p) G) (injLabellings (ZMod p) G)
      (fun x x' => skCollKerColl ς D x x' / (injLabellings (ZMod p) G).card)
      (collisionDnat G ς (Fintype.card (ZMod p)) n) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  exact sk_soft_collision_opBound_natural_g hW G ς hς hanti hne hn hS1 ord hord π hπ D hD ν hν

/-- **`cor:soft-kernels`(b) over `𝔽_p`, all coefficients**: `‖T^D_coll,1‖ ≤ D_1`. -/
theorem sk_soft_collision_opBound_zmod (hp2 : p ≠ 2) (hW : WeilBound (ZMod p))
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card (ZMod p)) n < 1)
    (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) :
    Sarkozy.Influence.OpBound (injLabellings (ZMod p) G) (injLabellings (ZMod p) G)
      (fun x x' => skCollKer1 ς D x x' / (injLabellings (ZMod p) G).card)
      (collisionD1 G ς ord (Fintype.card (ZMod p)) n) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  exact sk_soft_collision_opBound_g hW G ς hς hanti hne hn hS1 ord hord D hD ν hν

/-- **`cor:soft-kernels`(b) over `𝔽_p`, all coefficients**: `‖T^D_coll,≥2‖ ≤ D_{≥2}`. -/
theorem sk_soft_collision_opBound2_zmod (hp2 : p ≠ 2) (hW : WeilBound (ZMod p))
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card (ZMod p)) n < 1)
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1) :
    Sarkozy.Influence.OpBound (injLabellings (ZMod p) G) (injLabellings (ZMod p) G)
      (fun x x' => skCollKer2 ς D x x' / (injLabellings (ZMod p) G).card)
      (collisionD2 G ς π (Fintype.card (ZMod p)) n) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  exact sk_soft_collision_opBound2_g hW G ς hς hanti hne hn hS1 π hπ D hD ν hν

end SkCollZMod

end Sarkozy.ExtractionK
