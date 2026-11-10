module

public import Sarkozy.SpectralD.CxBridge

@[expose] public section

/-!
# The nonstar kernel is the sum over the nonstar sets

`paper/sections/14_spectral.tex`, `subsec:spec:perp`: `K_ns = ∑_{S ⊆ E_× nonstar} χ_S`. With WP-A's
star kernel `K_star` (column stars `J ⊆ N(k)`, `J ≠ ∅`, and row stars `K ⊆ N(j)`, `|K| ≥ 2`) and
`Extraction`'s stars (`IsStar`, `filter_rowStar_eq`, `filter_colStar_eq`):
`∑_{S = ∅ or a star} χ_S = 1 + K_star` (`starPart_eq`), hence
`nsKer = ∏_e (1 + χ_e) − 1 − K_star = ∑_{S ∈ nonstars E_×} χ_S` (`nsKer_eq`), the kernel of X1's
`extraction_compressed_buckets`.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.Extraction
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

lemma mem_crossPairs_iff_row (j k : D.cut.Half) : (j, k) ∈ D.crossPairs ↔ k ∈ D.Nset j := by
  simp only [Cuts.SpecData.crossPairs, Cuts.SpecData.Nset, mem_filter, mem_univ, true_and]
  rw [D.sgn_antisymm j k, neg_ne_zero]

lemma mem_crossPairs_iff_col (j k : D.cut.Half) : (j, k) ∈ D.crossPairs ↔ j ∈ D.Nset k := by
  simp only [Cuts.SpecData.crossPairs, Cuts.SpecData.Nset, mem_filter, mem_univ, true_and]

/-- Row stars: WP-A's enumeration agrees with `Extraction`'s. -/
lemma row_sum_eq (x x' : D.cut.Half → ZMod p) (j : D.cut.Half) :
    ∑ K ∈ (D.Nset j).powerset.filter (fun K => 2 ≤ K.card), Spectral.rowChar D j K x x' =
      ∑ U ∈ (D.crossPairs.filter fun e => e.1 = j).powerset.filter (fun U => 2 ≤ U.card),
        ∏ e ∈ U, ExtractionK.chiPair D.sgn e x x' := by
  classical
  refine sum_nbij' (fun K => K.image (fun k => (j, k))) (fun U => U.image Prod.snd)
    ?_ ?_ ?_ ?_ ?_
  · intro K hK
    simp only [mem_filter, mem_powerset] at hK ⊢
    refine ⟨fun e he => ?_, ?_⟩
    · rw [mem_image] at he
      obtain ⟨k, hk, rfl⟩ := he
      exact mem_filter.mpr ⟨(mem_crossPairs_iff_row D j k).mpr (hK.1 hk), rfl⟩
    · rw [card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
      exact hK.2
  · intro U hU
    simp only [mem_filter, mem_powerset] at hU ⊢
    refine ⟨fun k hk => ?_, ?_⟩
    · rw [mem_image] at hk
      obtain ⟨e, he, rfl⟩ := hk
      have h1 := mem_filter.mp (hU.1 he)
      have he' : e = (j, e.2) := Prod.ext h1.2 rfl
      have h2 := h1.1
      rw [he'] at h2
      exact (mem_crossPairs_iff_row D j e.2).mp h2
    · rw [card_image_of_injOn]
      · exact hU.2
      · intro a ha b hb h
        have ha' := (mem_filter.mp (hU.1 ha)).2
        have hb' := (mem_filter.mp (hU.1 hb)).2
        exact Prod.ext (ha'.trans hb'.symm) h
  · intro K _
    rw [image_image]
    exact image_id'
  · intro U hU
    simp only [mem_filter, mem_powerset] at hU
    rw [image_image]
    conv_rhs => rw [← image_id (s := U)]
    refine image_congr fun e he => ?_
    have h1 := (mem_filter.mp (hU.1 he)).2
    exact Prod.ext h1.symm rfl
  · intro K _
    rw [prod_image (fun a _ b _ h => (Prod.mk.inj h).2)]
    rfl

/-- Column stars with at least two edges: WP-A's enumeration agrees with `Extraction`'s. -/
lemma col_sum_eq (x x' : D.cut.Half → ZMod p) (k : D.cut.Half) :
    ∑ J ∈ (D.Nset k).powerset.filter (fun J => 2 ≤ J.card), Spectral.colChar D k J x x' =
      ∑ U ∈ (D.crossPairs.filter fun e => e.2 = k).powerset.filter (fun U => 2 ≤ U.card),
        ∏ e ∈ U, ExtractionK.chiPair D.sgn e x x' := by
  classical
  refine sum_nbij' (fun J => J.image (fun j => (j, k))) (fun U => U.image Prod.fst)
    ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    simp only [mem_filter, mem_powerset] at hJ ⊢
    refine ⟨fun e he => ?_, ?_⟩
    · rw [mem_image] at he
      obtain ⟨j, hj, rfl⟩ := he
      exact mem_filter.mpr ⟨(mem_crossPairs_iff_col D j k).mpr (hJ.1 hj), rfl⟩
    · rw [card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
      exact hJ.2
  · intro U hU
    simp only [mem_filter, mem_powerset] at hU ⊢
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [mem_image] at hj
      obtain ⟨e, he, rfl⟩ := hj
      have h1 := mem_filter.mp (hU.1 he)
      have he' : e = (e.1, k) := Prod.ext rfl h1.2
      have h2 := h1.1
      rw [he'] at h2
      exact (mem_crossPairs_iff_col D e.1 k).mp h2
    · rw [card_image_of_injOn]
      · exact hU.2
      · intro a ha b hb h
        have ha' := (mem_filter.mp (hU.1 ha)).2
        have hb' := (mem_filter.mp (hU.1 hb)).2
        exact Prod.ext h (ha'.trans hb'.symm)
  · intro J _
    rw [image_image]
    exact image_id'
  · intro U hU
    simp only [mem_filter, mem_powerset] at hU
    rw [image_image]
    conv_rhs => rw [← image_id (s := U)]
    refine image_congr fun e he => ?_
    have h1 := (mem_filter.mp (hU.1 he)).2
    exact Prod.ext rfl h1.symm
  · intro J _
    rw [prod_image (fun a _ b _ h => (Prod.mk.inj h).1)]
    rfl

/-- WP-A's column stars: the single edges and the stars with at least two edges. -/
lemma col_single (x x' : D.cut.Half → ZMod p) (k : D.cut.Half) :
    ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.Nonempty), Spectral.colChar D k J x x' =
      ∑ j ∈ D.Nset k, ExtractionK.chiPair D.sgn (j, k) x x' +
        ∑ J ∈ (D.Nset k).powerset.filter (fun J => 2 ≤ J.card), Spectral.colChar D k J x x' := by
  classical
  rw [← sum_filter_add_sum_filter_not _ (fun J => 2 ≤ J.card),
    add_comm (∑ j ∈ D.Nset k, ExtractionK.chiPair D.sgn (j, k) x x')]
  congr 1
  · rw [filter_filter]
    refine sum_congr (filter_congr fun J _ => ⟨fun h => h.2, fun h =>
      ⟨card_pos.mp (by omega), h⟩⟩) fun J _ => rfl
  · have hset : ((D.Nset k).powerset.filter (fun J => J.Nonempty)).filter
        (fun J => ¬ 2 ≤ J.card) = (D.Nset k).image singleton := by
      ext J
      simp only [mem_filter, mem_powerset, mem_image, not_le]
      constructor
      · rintro ⟨⟨hJ, hne⟩, h2⟩
        have h1 : J.card = 1 := by have := hne.card_pos; omega
        obtain ⟨j, rfl⟩ := card_eq_one.mp h1
        exact ⟨j, hJ (mem_singleton_self j), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨singleton_subset_iff.mpr hj, singleton_nonempty j⟩, by simp⟩
    rw [hset, sum_image (fun a _ b _ h => singleton_injective h)]
    refine sum_congr rfl fun j _ => ?_
    unfold Spectral.colChar
    rw [prod_singleton]
    rfl

lemma sum_cross_eq (g : D.cut.Half × D.cut.Half → ℝ) :
    ∑ k, ∑ j ∈ D.Nset k, g (j, k) = ∑ e ∈ D.crossPairs, g e := by
  classical
  simp only [Cuts.SpecData.Nset, Cuts.SpecData.crossPairs, sum_filter]
  rw [Fintype.sum_prod_type]
  exact sum_comm

/-- **The empty set and the stars**: `∑_{S = ∅ or a star} χ_S = 1 + K_star`. -/
theorem starPart_eq (x x' : D.cut.Half → ZMod p) :
    ∑ S ∈ D.crossPairs.powerset.filter (fun S => S = ∅ ∨ IsStar S),
        ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x' = 1 + Spectral.starKer D x x' := by
  classical
  set E := D.crossPairs with hE
  set χ : D.cut.Half × D.cut.Half → ℝ := fun e => ExtractionK.chiPair D.sgn e x x' with hχ
  have hsplit : (E.powerset.filter fun S => S = ∅ ∨ IsStar S) =
      (E.powerset.filter fun S => #S < 2) ∪
        ((E.powerset.filter fun S => 2 ≤ #S ∧ IsRowStar S) ∪
          (E.powerset.filter fun S => 2 ≤ #S ∧ IsColStar S)) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_union]
    constructor
    · rintro ⟨hS, h⟩
      by_cases h2 : #S < 2
      · exact Or.inl ⟨hS, h2⟩
      · rcases h with h0 | hr | hc
        · subst h0; simp at h2
        · exact Or.inr (Or.inl ⟨hS, by omega, hr⟩)
        · exact Or.inr (Or.inr ⟨hS, by omega, hc⟩)
    · rintro (⟨hS, h2⟩ | ⟨hS, -, hr⟩ | ⟨hS, -, hc⟩)
      · refine ⟨hS, ?_⟩
        have : #S = 0 ∨ #S = 1 := by omega
        rcases this with h | h
        · exact Or.inl (card_eq_zero.1 h)
        · exact Or.inr (isStar_of_card_eq_one h)
      · exact ⟨hS, Or.inr (Or.inl hr)⟩
      · exact ⟨hS, Or.inr (Or.inr hc)⟩
  have hd1 : Disjoint (E.powerset.filter fun S => 2 ≤ #S ∧ IsRowStar S)
      (E.powerset.filter fun S => 2 ≤ #S ∧ IsColStar S) := by
    rw [disjoint_filter]
    rintro S - ⟨h2, hr⟩ ⟨-, hc⟩
    obtain ⟨-, j, hj⟩ := isRowStar_iff.1 hr
    obtain ⟨-, k, hk⟩ := isColStar_iff.1 hc
    have : #S ≤ 1 := card_le_one.2 fun a ha b hb =>
      Prod.ext (by rw [hj a ha, hj b hb]) (by rw [hk a ha, hk b hb])
    omega
  have hd2 : Disjoint (E.powerset.filter fun S => #S < 2)
      ((E.powerset.filter fun S => 2 ≤ #S ∧ IsRowStar S) ∪
        (E.powerset.filter fun S => 2 ≤ #S ∧ IsColStar S)) := by
    rw [disjoint_union_right]
    constructor
    · rw [disjoint_filter]
      rintro S - h ⟨h2, -⟩
      omega
    · rw [disjoint_filter]
      rintro S - h ⟨h2, -⟩
      omega
  have hsmall : ∑ S ∈ E.powerset.filter (fun S => #S < 2), ∏ e ∈ S, χ e =
      1 + ∑ e ∈ E, χ e := by
    have hset : E.powerset.filter (fun S => #S < 2) = insert ∅ (E.image singleton) := by
      ext S
      simp only [mem_filter, mem_powerset, mem_insert, mem_image]
      constructor
      · rintro ⟨hS, h2⟩
        have : #S = 0 ∨ #S = 1 := by omega
        rcases this with h | h
        · exact Or.inl (card_eq_zero.1 h)
        · obtain ⟨e, rfl⟩ := card_eq_one.mp h
          exact Or.inr ⟨e, hS (mem_singleton_self e), rfl⟩
      · rintro (rfl | ⟨e, he, rfl⟩)
        · exact ⟨empty_subset _, by simp⟩
        · exact ⟨singleton_subset_iff.mpr he, by simp⟩
    have hnot : (∅ : Finset (D.cut.Half × D.cut.Half)) ∉ E.image singleton := by
      simp only [mem_image, not_exists, not_and]
      exact fun e _ h => singleton_ne_empty e h
    rw [hset, sum_insert hnot, sum_image (fun a _ b _ h => singleton_injective h), prod_empty]
    simp only [prod_singleton]
  have hrowd : ((univ : Finset D.cut.Half) : Set D.cut.Half).PairwiseDisjoint
      (fun j => (E.filter fun e => e.1 = j).powerset.filter fun U => 2 ≤ #U) := by
    intro j _ j' _ hjj'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro U hU hU'
    simp only [mem_filter, mem_powerset] at hU hU'
    obtain ⟨e, he⟩ := card_pos.1 (by omega : 0 < #U)
    exact hjj' ((mem_filter.1 (hU.1 he)).2.symm.trans (mem_filter.1 (hU'.1 he)).2)
  have hcold : ((univ : Finset D.cut.Half) : Set D.cut.Half).PairwiseDisjoint
      (fun k => (E.filter fun e => e.2 = k).powerset.filter fun U => 2 ≤ #U) := by
    intro k _ k' _ hkk'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro U hU hU'
    simp only [mem_filter, mem_powerset] at hU hU'
    obtain ⟨e, he⟩ := card_pos.1 (by omega : 0 < #U)
    exact hkk' ((mem_filter.1 (hU.1 he)).2.symm.trans (mem_filter.1 (hU'.1 he)).2)
  rw [hsplit, sum_union hd2, sum_union hd1, filter_rowStar_eq, filter_colStar_eq,
    sum_biUnion hrowd, sum_biUnion hcold, hsmall]
  unfold Spectral.starKer
  rw [sum_congr rfl fun k _ => col_single D x x' k, sum_add_distrib,
    sum_cross_eq D (fun e => ExtractionK.chiPair D.sgn e x x'),
    sum_congr rfl fun j _ => row_sum_eq D x x' j, sum_congr rfl fun k _ => col_sum_eq D x x' k]
  ring

/-- **`K_ns = ∑_{S ∈ nonstars E_×} χ_S`**, the kernel of X1's `extraction_compressed_buckets`. -/
theorem nsKer_eq (x x' : D.cut.Half → ZMod p) :
    nsKer D x x' = ∑ S ∈ nonstars D.crossPairs, ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x' := by
  classical
  have h1 : prodKer D x x' =
      ∑ S ∈ D.crossPairs.powerset, ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x' := by
    unfold prodKer
    rw [prod_one_add]
    rfl
  have h2 := sum_filter_add_sum_filter_not D.crossPairs.powerset (fun S => S = ∅ ∨ IsStar S)
    (fun S => ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x')
  have h3 : D.crossPairs.powerset.filter (fun S => ¬ (S = ∅ ∨ IsStar S)) =
      nonstars D.crossPairs := by
    ext S
    simp only [nonstars, mem_filter, isNonstar_iff_not]
  rw [h3, starPart_eq] at h2
  unfold nsKer
  rw [h1, ← h2]
  ring

section Final

open Sarkozy.SpectralC
open scoped InnerProductSpace

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at `p ≡ 3 (mod 4)`**, with the
expansion inputs in the form of X1's and `Extraction`'s theorems: the bilinear nonstar bound of
`ExtractionK.extraction_compressed_buckets` (`hnsX`, `N_ns`) and the collision matrix bounds of
`Extraction.collision_opBound`, `collision_opBound2` (`hcoll1`, `hcoll2`, `D_col = D_1 + D_{≥2}`).
Otherwise as `spectral_criterion_cut_exp`. -/
theorem spectral_criterion_cut_X1 [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- the character expansion: X1's nonstar bound, `Extraction`'s collision bounds
    {εZ Nns Dcol D1 D2 : ℝ} (hεZ : εZ < 1) (hNns0 : 0 ≤ Nns) (hD10 : 0 ≤ D1) (hD20 : 0 ≤ D2)
    (hnsX : ∀ f g : (D.cut.Half → ZMod p) → ℝ,
      |(D.halfLaw hne).expect (fun x => f x * (D.halfLaw hne).expect (fun x' =>
        (∑ S ∈ Extraction.nonstars D.crossPairs, ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x') *
          g x'))| ≤
        Nns * Real.sqrt ((D.halfLaw hne).expect (fun x => f x ^ 2)) *
          Real.sqrt ((D.halfLaw hne).expect (fun x => g x ^ 2)))
    (hcoll1 : Sarkozy.Influence.OpBound (Labellings.injLabellings (ZMod p) D.halfGraph)
      (Labellings.injLabellings (ZMod p) D.halfGraph)
      (fun x x' => Extraction.collisionKernel1 D.sgn x x' /
        (Labellings.injLabellings (ZMod p) D.halfGraph).card) D1)
    (hcoll2 : Sarkozy.Influence.OpBound (Labellings.injLabellings (ZMod p) D.halfGraph)
      (Labellings.injLabellings (ZMod p) D.halfGraph)
      (fun x x' => Extraction.collisionKernel2 D.sgn x x' /
        (Labellings.injLabellings (ZMod p) D.halfGraph).card) D2)
    (hDcol : D1 + D2 ≤ Dcol)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p hp2) D.halfGraph (D.half_nonempty hne)
        (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) + Nns + Dcol ≤
        εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mXcut p D k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p D k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn))⁻¹)
        lamH εH θ ρ ΓE lamH 1
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
    (hεVb : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hsp : 0 < sp) (hsm : 0 < sm)
    (htp : ∀ ξ : ZMod p, (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) D) ξ) x).re)
        (qXcx Adj D.Nset (sgnZ (p := p) D) ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ : ZMod p, ¬ (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) D) ξ) x).re)
        (qXcx Adj D.Nset (sgnZ (p := p) D) ξ) cbar sm ηQbar ηBbar)
    (hgp : (cbar + sp) / (1 - εVbar) ≤ g) (hgm : (cbar + sm) / (1 - εVbar) ≤ g)
    (f : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    -(g * rp p) * ‖f‖ ^ 2 ≤ ⟪f, Spectral.cutOp D hne f⟫_ℝ := by
  have hns : ∀ x, ‖nsOp D hne x‖ ≤ Nns * ‖x‖ := by
    intro v
    have hk : nsKer (p := p) D = fun x x' => ∑ S ∈ Extraction.nonstars D.crossPairs,
        ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x' := by
      funext x x'
      exact nsKer_eq D x x'
    unfold nsOp
    rw [hk]
    exact kernelOp_norm_le_of_bilinear (D.halfLaw hne) _ hNns0 hnsX v
  have hcoll : ∀ x, ‖collOp D hne x‖ ≤ Dcol * ‖x‖ := by
    intro v
    have hk : collKer (p := p) D = fun x x' => Extraction.collisionKernel1 D.sgn x x' +
        Extraction.collisionKernel2 D.sgn x x' := by
      funext x x'
      rw [collKer_eq, Extraction.collisionKernelColl_eq]
    unfold collOp
    rw [hk, kernelOp_add_ker]
    have h1 := kernelOp_norm_le_of_opBound D.halfGraph (D.half_nonempty hne) _ hD10 hcoll1 v
    have h2 := kernelOp_norm_le_of_opBound D.halfGraph (D.half_nonempty hne) _ hD20 hcoll2 v
    calc ‖Spectral.kernelOp (D.halfLaw hne) (fun x x' => Extraction.collisionKernel1 D.sgn x x') v +
          Spectral.kernelOp (D.halfLaw hne) (fun x x' => Extraction.collisionKernel2 D.sgn x x') v‖
        ≤ ‖Spectral.kernelOp (D.halfLaw hne) (fun x x' => Extraction.collisionKernel1 D.sgn x x') v‖ +
          ‖Spectral.kernelOp (D.halfLaw hne) (fun x x' => Extraction.collisionKernel2 D.sgn x x') v‖ :=
          norm_add_le _ _
      _ ≤ D1 * ‖v‖ + D2 * ‖v‖ := add_le_add h1 h2
      _ = (D1 + D2) * ‖v‖ := by ring
      _ ≤ Dcol * ‖v‖ := mul_le_mul_of_nonneg_right hDcol (norm_nonneg v)
  exact spectral_criterion_cut_exp D hW hMR Adj hp2 hp3 hn hne hdeg hS1 l hnd hcov hdisj hεZ hns
    hcoll hεZc hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hΛD hηQ0 hDE hrowS hηQc hrowV hεVc hεV hcbar0
    hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Final

end Sarkozy.SpectralD.Cx
