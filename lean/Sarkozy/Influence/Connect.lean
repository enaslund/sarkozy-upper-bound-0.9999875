module

public import Sarkozy.Influence.PinPairBound

/-!
# Pinned influence, IX: connectivity of pinned state spaces (`lem:mid:connect`)

For a feasible pinning `(S', s')`, any two completions in `Ω_{S',s'}` are joined by a sequence
of completions in which consecutive elements differ in exactly one free coordinate
(`connect`). The count errors are the second inequality of `eq:mid:standing`
(`t ≤ Δ + 1` roots, at most `2n` excluded values, `w^{conn} < 1`), with `Δ` bounding the
degrees of the free vertices.

The proof differs from the paper's two-phase argument. It is an induction on the number of
free vertices. If `x ≠ y`, pick a free vertex `i` with `x_i ≠ y_i`. `place` moves `x`,
inside `Ω_{S',s'}`, to a completion with label `y_i` at `i`:
1. move the vertex currently carrying `y_i`, if any, to a fresh label;
2. move each free neighbour of `i` to a fresh label compatible with `y_i` at `i`;
3. move `i` to `y_i`.
Both the result and `y` are then completions of the pinning `(S' ∪ {i}, (s', y_i))`. Each
move exists by `exists_move`: a vertex of degree at most `Δ` with one extra root has
`p 2^{-t}(1 - w^{conn}) > 0` admissible labels.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy Sarkozy.Peyre

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ} [NeZero p]

/-- One step of `lem:mid:connect`: two injective strict-square labellings that differ in
exactly one coordinate outside `S'`. -/
def ConnStep (G : OrientedGraph U) (S' : Finset U) (a b : U → ZMod p) : Prop :=
  a ∈ injLabellings G p ∧ b ∈ injLabellings G p ∧
    ∃ v ∉ S', a v ≠ b v ∧ ∀ u, u ≠ v → a u = b u

theorem reach_update (G : OrientedGraph U) (S' : Finset U) {a : U → ZMod p} {v : U}
    {c : ZMod p} (ha : a ∈ injLabellings G p) (hb : Function.update a v c ∈ injLabellings G p)
    (hv : v ∉ S') : Relation.ReflTransGen (ConnStep G S') a (Function.update a v c) := by
  by_cases hc : c = a v
  · rw [hc, Function.update_eq_self]
  · refine Relation.ReflTransGen.single ⟨ha, hb, v, hv, ?_, fun u hu => ?_⟩
    · rw [Function.update_self]
      exact Ne.symm hc
    · rw [Function.update_of_ne hu]

/-- **A move exists.** For a vertex `v` of degree at most `Δ` and an extra root `c₀` (with
sign `σ`) not carried by a neighbour of `v`, the second inequality of `eq:mid:standing`
gives a label `c` that is unused and different from `c₀`, satisfies `σ(c - c₀) ∈ Q_p`, and
keeps `update a v c` an injective strict-square labelling. -/
theorem exists_move (G : OrientedGraph U) {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn)
    {a : U → ZMod p} (ha : a ∈ injLabellings G p) {v : U} (hvdeg : G.deg v ≤ Δ)
    (c₀ σ : ZMod p) (hσ : σ = 1 ∨ σ = -1) (hc₀ : ∀ u, G.Adj v u → a u ≠ c₀) :
    ∃ c, (∀ u, a u ≠ c) ∧ c ≠ c₀ ∧ IsNzSq (σ * (c - c₀)) ∧
      Function.update a v c ∈ injLabellings G p := by
  classical
  obtain ⟨hainj, hasq⟩ := mem_injLabellings.mp ha
  set Nv := (Finset.univ : Finset U).filter (fun u => G.Adj v u) with hNv
  set eN : Fin Nv.card ≃ Nv := Nv.equivFin.symm with heN
  set sgu : U → ZMod p := fun u => if G.edge u v then 1 else -1 with hsgu
  set E' : Finset (ZMod p) := insert c₀ ((Finset.univ : Finset U).image a) with hE'
  set roots : Fin (Nv.card + 1) → ZMod p := Fin.cons c₀ (fun m => a (eN m)) with hroots
  set sg : Fin (Nv.card + 1) → ZMod p := Fin.cons σ (fun m => sgu (eN m)) with hsg
  have hNadj : ∀ u ∈ Nv, G.Adj v u := fun u hu => (Finset.mem_filter.mp hu).2
  have hroots_inj : Function.Injective roots := by
    rw [hroots, Fin.cons_injective_iff]
    refine ⟨fun ⟨m, hm⟩ => hc₀ _ (hNadj _ (eN m).2) hm, fun m m' hmm => ?_⟩
    exact eN.injective (Subtype.ext (hainj hmm))
  have hsg1 : ∀ m, sg m = 1 ∨ sg m = -1 := by
    intro m
    refine Fin.cases ?_ (fun m => ?_) m
    · simp only [hsg, Fin.cons_zero]
      exact hσ
    · simp only [hsg, Fin.cons_succ, hsgu]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hrootsE : ∀ m, roots m ∈ E' := by
    intro m
    refine Fin.cases ?_ (fun m => ?_) m
    · simp only [hroots, Fin.cons_zero]
      exact Finset.mem_insert_self _ _
    · simp only [hroots, Fin.cons_succ]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem a (Finset.mem_univ _))
  have hdeg : Nv.card + 1 ≤ Δ + 1 := by
    have : Nv.card = G.deg v := rfl
    omega
  have hcardE : E'.card ≤ 2 * Fintype.card U := by
    have h1 : E'.card ≤ ((Finset.univ : Finset U).image a).card + 1 := Finset.card_insert_le _ _
    have h2 : ((Finset.univ : Finset U).image a).card ≤ Fintype.card U := by
      exact Finset.card_image_le.trans (le_of_eq Finset.card_univ)
    have h3 : 1 ≤ Fintype.card U := by
      have hv : v ∈ (Finset.univ : Finset U) := Finset.mem_univ v
      exact Finset.card_pos.mpr ⟨v, hv⟩
    omega
  have hb := hconn (Nv.card + 1) roots sg E' hroots_inj hsg1 hrootsE hdeg hcardE
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hpos : 0 < standingCount roots sg E' := by
    by_contra h0
    have h00 : standingCount roots sg E' = 0 := by omega
    rw [h00] at hb
    simp only [Nat.cast_zero, mul_zero, zero_div] at hb
    linarith
  unfold standingCount at hpos
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hcE, hcon⟩ := hc
  rw [Fin.forall_fin_succ] at hcon
  obtain ⟨h0, hs⟩ := hcon
  simp only [hroots, hsg, Fin.cons_zero, Fin.cons_succ] at h0 hs
  have hcfresh : ∀ u, a u ≠ c := fun u hau => hcE (by
    rw [hE', ← hau]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem a (Finset.mem_univ _)))
  have hcc₀ : c ≠ c₀ := fun h => hcE (by rw [hE', h]; exact Finset.mem_insert_self _ _)
  refine ⟨c, hcfresh, hcc₀, h0, ?_⟩
  rw [mem_injLabellings]
  constructor
  · intro u₁ u₂ h12
    by_cases h1 : u₁ = v
    · by_cases h2 : u₂ = v
      · rw [h1, h2]
      · subst h1
        rw [Function.update_self, Function.update_of_ne h2] at h12
        exact absurd h12.symm (hcfresh u₂)
    · by_cases h2 : u₂ = v
      · subst h2
        rw [Function.update_self, Function.update_of_ne h1] at h12
        exact absurd h12 (hcfresh u₁)
      · rw [Function.update_of_ne h1, Function.update_of_ne h2] at h12
        exact hainj h12
  · intro u₁ u₂ he
    by_cases h1 : u₁ = v
    · subst h1
      have h2 : u₂ ≠ u₁ := fun h => G.irrefl u₁ (h ▸ he)
      rw [Function.update_self, Function.update_of_ne h2]
      have hadj : G.Adj u₁ u₂ := Or.inl he
      have hm := hs (eN.symm ⟨u₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩⟩)
      simp only [Equiv.apply_symm_apply] at hm
      have hne : ¬ G.edge u₂ u₁ := G.asymm u₁ u₂ he
      simp only [hsgu, hne, ite_false] at hm
      have e : (-1 : ZMod p) * (c - a u₂) = a u₂ - c := by ring
      rwa [e] at hm
    · by_cases h2 : u₂ = v
      · subst h2
        rw [Function.update_self, Function.update_of_ne h1]
        have hadj : G.Adj u₂ u₁ := Or.inr he
        have hm := hs (eN.symm ⟨u₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩⟩)
        simp only [Equiv.apply_symm_apply] at hm
        simp only [hsgu, he, ite_true, one_mul] at hm
        exact hm
      · rw [Function.update_of_ne h1, Function.update_of_ne h2]
        exact hasq u₁ u₂ he

/-- Compatibility of the label `c` at a neighbour `j` of `i` with the label `c₀` at `i`. -/
def Compat (G : OrientedGraph U) (i j : U) (c c₀ : ZMod p) : Prop :=
  (G.edge i j → IsNzSq (c - c₀)) ∧ (G.edge j i → IsNzSq (c₀ - c))

/-- **Placing one vertex.** From a completion `x` of `(S', s')` one reaches, by single free
moves, a completion with label `c₀` at the free vertex `i`. This needs `c₀` to differ from
the pinned labels and to be compatible with the pinned neighbours of `i`. -/
theorem place (G : OrientedGraph U) {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) (S' : Finset U)
    (s' : U → ZMod p) (hΔ : ∀ v, v ∉ S' → G.deg v ≤ Δ) {x : U → ZMod p}
    (hx : x ∈ injLabellings G p) (hxS : pinEvent S' s' x) {i : U} (hi : i ∉ S')
    {c₀ : ZMod p} (hcpin : ∀ v ∈ S', s' v ≠ c₀)
    (hcedge : ∀ v ∈ S', (G.edge i v → IsNzSq (s' v - c₀)) ∧ (G.edge v i → IsNzSq (c₀ - s' v))) :
    ∃ x', x' ∈ injLabellings G p ∧ pinEvent S' s' x' ∧ x' i = c₀ ∧
      Relation.ReflTransGen (ConnStep G S') x x' := by
  classical
  by_cases hxi : x i = c₀
  · exact ⟨x, hx, hxS, hxi, Relation.ReflTransGen.refl⟩
  -- Step A: nobody carries `c₀`
  have hA : ∃ xA, xA ∈ injLabellings G p ∧ pinEvent S' s' xA ∧ xA i = x i ∧
      (∀ u, xA u ≠ c₀) ∧ Relation.ReflTransGen (ConnStep G S') x xA := by
    by_cases hk : ∃ k, x k = c₀
    · obtain ⟨k, hk⟩ := hk
      have hki : k ≠ i := fun h => hxi (h ▸ hk)
      have hkS : k ∉ S' := fun h => hcpin k h (by rw [← hxS k h]; exact hk)
      have hxinj := (mem_injLabellings.mp hx).1
      have hc₀ : ∀ u, G.Adj k u → x u ≠ c₀ := by
        intro u hadj hu
        have : u = k := hxinj (hu.trans hk.symm)
        exact G.not_adj_self k (this ▸ hadj)
      obtain ⟨c, hcfresh, hcc₀, -, hcinj⟩ :=
        exists_move G hw hconn hx (hΔ k hkS) c₀ 1 (Or.inl rfl) hc₀
      refine ⟨Function.update x k c, hcinj, fun v hv => ?_, ?_, fun u => ?_,
        reach_update G S' hx hcinj hkS⟩
      · have hvk : v ≠ k := fun h => hkS (h ▸ hv)
        rw [Function.update_of_ne hvk]
        exact hxS v hv
      · rw [Function.update_of_ne (Ne.symm hki)]
      · by_cases huk : u = k
        · rw [huk, Function.update_self]
          exact hcc₀
        · rw [Function.update_of_ne huk]
          intro hu
          exact huk (hxinj (hu.trans hk.symm))
    · push Not at hk
      exact ⟨x, hx, hxS, rfl, hk, Relation.ReflTransGen.refl⟩
  obtain ⟨xA, hxA, hxAS, hxAi, hxAc, hreachA⟩ := hA
  -- Step B: the free neighbours of `i` become compatible with `c₀`
  set J := (Finset.univ : Finset U).filter (fun j => G.Adj i j ∧ j ∉ S') with hJ
  have hB : ∀ J₀ ⊆ J, ∃ xB, xB ∈ injLabellings G p ∧ pinEvent S' s' xB ∧ xB i = x i ∧
      (∀ u, xB u ≠ c₀) ∧ (∀ j ∈ J₀, Compat G i j (xB j) c₀) ∧
      Relation.ReflTransGen (ConnStep G S') xA xB := by
    intro J₀
    induction J₀ using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨xA, hxA, hxAS, hxAi, hxAc, fun j hj => absurd hj (Finset.notMem_empty j),
        Relation.ReflTransGen.refl⟩
    | insert j J₀ hjJ₀ ih =>
      intro hsub
      obtain ⟨xB, hxB, hxBS, hxBi, hxBc, hcomp, hreach⟩ :=
        ih ((Finset.subset_insert j J₀).trans hsub)
      have hjJ : j ∈ J := hsub (Finset.mem_insert_self j J₀)
      obtain ⟨hadj, hjS⟩ := (Finset.mem_filter.mp hjJ).2
      have hji : j ≠ i := fun h => G.not_adj_self i (h ▸ hadj)
      set σ : ZMod p := if G.edge i j then 1 else -1 with hσ
      have hσ1 : σ = 1 ∨ σ = -1 := by
        simp only [hσ]
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
      obtain ⟨c, hcfresh, hcc₀, hcσ, hcinj⟩ :=
        exists_move G hw hconn hxB (hΔ j hjS) c₀ σ hσ1 (fun u _ => hxBc u)
      refine ⟨Function.update xB j c, hcinj, fun v hv => ?_, ?_, fun u => ?_, fun j' hj' => ?_,
        hreach.trans (reach_update G S' hxB hcinj hjS)⟩
      · have hvj : v ≠ j := fun h => hjS (h ▸ hv)
        rw [Function.update_of_ne hvj]
        exact hxBS v hv
      · rw [Function.update_of_ne (Ne.symm hji)]
        exact hxBi
      · by_cases huj : u = j
        · rw [huj, Function.update_self]
          exact hcc₀
        · rw [Function.update_of_ne huj]
          exact hxBc u
      · rcases Finset.mem_insert.mp hj' with rfl | hj'
        · rw [Function.update_self]
          constructor
          · intro he
            simp only [hσ, he, ite_true, one_mul] at hcσ
            exact hcσ
          · intro he
            have hne : ¬ G.edge i j' := G.asymm j' i he
            simp only [hσ, hne, ite_false] at hcσ
            have e : (-1 : ZMod p) * (c - c₀) = c₀ - c := by ring
            rwa [e] at hcσ
        · have hj'j : j' ≠ j := fun h => hjJ₀ (h ▸ hj')
          rw [Function.update_of_ne hj'j]
          exact hcomp j' hj'
  obtain ⟨xB, hxB, hxBS, hxBi, hxBc, hcomp, hreachB⟩ := hB J le_rfl
  -- Step C: move `i` to `c₀`
  obtain ⟨hBinj, hBsq⟩ := mem_injLabellings.mp hxB
  have hCinj : Function.update xB i c₀ ∈ injLabellings G p := by
    rw [mem_injLabellings]
    constructor
    · intro u₁ u₂ h12
      by_cases h1 : u₁ = i
      · by_cases h2 : u₂ = i
        · rw [h1, h2]
        · subst h1
          rw [Function.update_self, Function.update_of_ne h2] at h12
          exact absurd h12.symm (hxBc u₂)
      · by_cases h2 : u₂ = i
        · subst h2
          rw [Function.update_self, Function.update_of_ne h1] at h12
          exact absurd h12 (hxBc u₁)
        · rw [Function.update_of_ne h1, Function.update_of_ne h2] at h12
          exact hBinj h12
    · intro u₁ u₂ he
      by_cases h1 : u₁ = i
      · subst h1
        have h2 : u₂ ≠ u₁ := fun h => G.irrefl u₁ (h ▸ he)
        rw [Function.update_self, Function.update_of_ne h2]
        by_cases hS : u₂ ∈ S'
        · rw [hxBS u₂ hS]
          exact (hcedge u₂ hS).1 he
        · have hJ2 : u₂ ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl he, hS⟩
          exact (hcomp u₂ hJ2).1 he
      · by_cases h2 : u₂ = i
        · subst h2
          rw [Function.update_self, Function.update_of_ne h1]
          by_cases hS : u₁ ∈ S'
          · rw [hxBS u₁ hS]
            exact (hcedge u₁ hS).2 he
          · have hJ1 : u₁ ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr he, hS⟩
            exact (hcomp u₁ hJ1).2 he
        · rw [Function.update_of_ne h1, Function.update_of_ne h2]
          exact hBsq u₁ u₂ he
  refine ⟨Function.update xB i c₀, hCinj, fun v hv => ?_, Function.update_self _ _ _,
    hreachA.trans (hreachB.trans (reach_update G S' hxB hCinj hi))⟩
  have hvi : v ≠ i := fun h => hi (h ▸ hv)
  rw [Function.update_of_ne hvi]
  exact hxBS v hv

theorem connStep_mono {G : OrientedGraph U} {S S' : Finset U} (h : S ⊆ S')
    {a b : U → ZMod p} (hab : ConnStep G S' a b) : ConnStep G S a b := by
  obtain ⟨ha, hb, v, hv, hne, heq⟩ := hab
  exact ⟨ha, hb, v, fun hvS => hv (h hvS), hne, heq⟩

/-- `lem:mid:connect`, by induction on the number of free vertices. -/
theorem connect_aux (G : OrientedGraph U) {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) :
    ∀ (n : ℕ) (S' : Finset U) (s' : U → ZMod p),
      ((Finset.univ : Finset U).filter (fun v => v ∉ S')).card = n →
      (∀ v, v ∉ S' → G.deg v ≤ Δ) →
      ∀ x y, x ∈ injLabellings G p → pinEvent S' s' x → y ∈ injLabellings G p →
        pinEvent S' s' y → Relation.ReflTransGen (ConnStep G S') x y := by
  classical
  intro n
  induction n with
  | zero =>
    intro S' s' hcard _ x y _ hxS _ hyS
    have hall : ∀ v, v ∈ S' := by
      intro v
      by_contra hv
      have : v ∈ (Finset.univ : Finset U).filter (fun v => v ∉ S') :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      rw [Finset.card_eq_zero.mp hcard] at this
      exact Finset.notMem_empty v this
    have hxy : x = y := funext fun v => (hxS v (hall v)).trans (hyS v (hall v)).symm
    rw [hxy]
  | succ n ih =>
    intro S' s' hcard hΔ x y hx hxS hy hyS
    by_cases hxy : x = y
    · rw [hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    have hiS : i ∉ S' := fun h => hi ((hxS i h).trans (hyS i h).symm)
    obtain ⟨hyinj, hysq⟩ := mem_injLabellings.mp hy
    have hcpin : ∀ v ∈ S', s' v ≠ y i := by
      intro v hv h
      have hvi : v ≠ i := fun e => hiS (e ▸ hv)
      exact hvi (hyinj ((hyS v hv).trans h))
    have hcedge : ∀ v ∈ S', (G.edge i v → IsNzSq (s' v - y i)) ∧
        (G.edge v i → IsNzSq (y i - s' v)) := by
      intro v hv
      rw [← hyS v hv]
      exact ⟨hysq i v, hysq v i⟩
    obtain ⟨x', hx', hx'S, hx'i, hreach⟩ :=
      place G hw hconn S' s' hΔ hx hxS hiS hcpin hcedge
    set S'' := insert i S' with hS''
    set s'' : U → ZMod p := Function.update s' i (y i) with hs''
    have hpin : ∀ z : U → ZMod p, pinEvent S' s' z → z i = y i → pinEvent S'' s'' z := by
      intro z hz hzi v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · rw [hs'', Function.update_self]
        exact hzi
      · have hvi : v ≠ i := fun e => hiS (e ▸ hv)
        rw [hs'', Function.update_of_ne hvi]
        exact hz v hv
    have hcard' : ((Finset.univ : Finset U).filter (fun v => v ∉ S'')).card = n := by
      have e : (Finset.univ : Finset U).filter (fun v => v ∉ S'') =
          ((Finset.univ : Finset U).filter (fun v => v ∉ S')).erase i := by
        ext v
        simp only [hS'', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          not_or, Finset.mem_erase]
      have hmem : i ∈ (Finset.univ : Finset U).filter (fun v => v ∉ S') :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩
      rw [e, Finset.card_erase_of_mem hmem, hcard]
      omega
    have hΔ' : ∀ v, v ∉ S'' → G.deg v ≤ Δ := fun v hv =>
      hΔ v (fun h => hv (Finset.mem_insert_of_mem h))
    have hrest := ih S'' s'' hcard' hΔ' x' y hx' (hpin x' hx'S hx'i) hy (hpin y hyS rfl)
    exact hreach.trans (Relation.ReflTransGen.mono
      (fun a b hab => connStep_mono (Finset.subset_insert i S') hab) x' y hrest)

/-- **`lem:mid:connect`.** Let `w^{conn} < 1` satisfy the second inequality of
`eq:mid:standing` with degree bound `Δ`, and let every free vertex of the pinning `(S', s')`
have degree at most `Δ`. Then any two completions `x, y ∈ Ω_{S',s'}` are joined by a sequence
of completions in which consecutive elements differ in exactly one free coordinate. -/
theorem connect (G : OrientedGraph U) {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) (S' : Finset U)
    (s' : U → ZMod p) (hΔ : ∀ v, v ∉ S' → G.deg v ≤ Δ) {x y : U → ZMod p}
    (hx : x ∈ injLabellings G p) (hxS : pinEvent S' s' x) (hy : y ∈ injLabellings G p)
    (hyS : pinEvent S' s' y) : Relation.ReflTransGen (ConnStep G S') x y :=
  connect_aux G hw hconn _ S' s' rfl hΔ x y hx hxS hy hyS

/-- `lem:mid:connect` in the setting of `def:mid:influence`. Take count errors for `(G, F)`,
`F = U \ S`, and a pinning `(S', s')` extending `(S, s)`. Then completions of `(S', s')` are
connected by single free moves. -/
theorem connect_of_countErrors (G : OrientedGraph U) (S : Finset U) {w wconn : ℝ}
    (hce : CountErrors G p (free S) w wconn) (S' : Finset U) (s' : U → ZMod p)
    (hSS' : S ⊆ S') {x y : U → ZMod p} (hx : x ∈ injLabellings G p) (hxS : pinEvent S' s' x)
    (hy : y ∈ injLabellings G p) (hyS : pinEvent S' s' y) :
    Relation.ReflTransGen (ConnStep G S') x y := by
  refine connect G hce.wconn_lt_one hce.conn S' s' (fun v hv => ?_) hx hxS hy hyS
  have hvF : v ∈ free S := by
    simp only [free, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun h => hv (hSS' h)
  exact Finset.le_sup (f := G.deg) hvF

/-- **`lem:mid:subspaces` (i), the part without angles.** Let `f` be unchanged by every
single move in `A` between completions of `(S', s')`; that is, `f ∈ V_i` for all `i ∈ A`.
Then `f` is a function of `y_{U \ A}` on the completions, i.e. `f ∈` the functions of
`y_{F' \ A}`. (The second labelling `ω'` is automatically a completion, since it agrees with
`ω` outside `A ⊆ F'`.) The proof is by connectivity (`connect`) of the completions of the finer
pinning of `U \ A`. -/
theorem subspaces_funOf (G : OrientedGraph U) {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) (S' : Finset U)
    (s' : U → ZMod p) (hΔ : ∀ v, v ∉ S' → G.deg v ≤ Δ) (A : Finset U)
    (hA : ∀ v ∈ A, v ∉ S') (f : (U → ZMod p) → ℝ)
    (hf : ∀ i ∈ A, ∀ ω ω', ω ∈ injLabellings G p → pinEvent S' s' ω →
      ω' ∈ injLabellings G p → pinEvent S' s' ω' → (∀ u, u ≠ i → ω u = ω' u) → f ω = f ω')
    {ω ω' : U → ZMod p} (hω : ω ∈ injLabellings G p) (hωS : pinEvent S' s' ω)
    (hω' : ω' ∈ injLabellings G p) (hagree : ∀ u, u ∉ A → ω u = ω' u) :
    f ω = f ω' := by
  classical
  set S'' : Finset U := (Finset.univ : Finset U).filter (fun u => u ∉ A) with hS''
  have hmem : ∀ u, u ∈ S'' ↔ u ∉ A := fun u => by simp [hS'']
  have hΔ'' : ∀ v, v ∉ S'' → G.deg v ≤ Δ := fun v hv => by
    have hvA : v ∈ A := by
      by_contra h
      exact hv ((hmem v).mpr h)
    exact hΔ v (hA v hvA)
  have hpinω : pinEvent S'' ω ω := fun u _ => rfl
  have hpinω' : pinEvent S'' ω ω' := fun u hu => (hagree u ((hmem u).mp hu)).symm
  have hchain := connect G hw hconn S'' ω hΔ'' hω hpinω hω' hpinω'
  -- along the chain, every state agrees with `ω` outside `A` and has the same value of `f`
  have key : ∀ b, Relation.ReflTransGen (ConnStep G S'') ω b →
      pinEvent S'' ω b ∧ f b = f ω := by
    intro b hb
    induction hb with
    | refl => exact ⟨hpinω, rfl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hb, hc, v, hvS, -, hbc'⟩ := hbc
      obtain ⟨hpin, hfb⟩ := ih
      have hvA : v ∈ A := by
        by_contra h
        exact hvS ((hmem v).mpr h)
      have hpinc : pinEvent S'' ω c := by
        intro u hu
        have huv : u ≠ v := fun h => (hmem u).mp hu (h ▸ hvA)
        rw [← hbc' u huv]
        exact hpin u hu
      have hpS' : ∀ z : U → ZMod p, pinEvent S'' ω z → pinEvent S' s' z := by
        intro z hz u hu
        have huA : u ∉ A := fun h => hA u h hu
        rw [hz u ((hmem u).mpr huA)]
        exact hωS u hu
      refine ⟨hpinc, ?_⟩
      rw [← hfb]
      exact (hf v hvA b c hb (hpS' b hpin) hc (hpS' c hpinc) hbc').symm
  exact ((key ω' hchain).2).symm

/-- **`lem:mid:subspaces` (iii), the intersection part.** For disjoint `β, β'`, a function on
the completions of `(S', s')` that is both a function of `y_β` and a function of `y_{β'}` is
constant on the completions. So `V_{F' \ β'} ∩ V_{F' \ β}` consists of the constants, which
is what identifies the Friedrichs cosine of these subspaces with the maximal correlation. -/
theorem funOf_disjoint_const (G : OrientedGraph U) {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) (S' : Finset U)
    (s' : U → ZMod p) (hΔ : ∀ v, v ∉ S' → G.deg v ≤ Δ) {β β' : Finset U}
    (hdisj : Disjoint β β') (f : (U → ZMod p) → ℝ)
    (hfβ : ∀ ω ω', ω ∈ injLabellings G p → pinEvent S' s' ω → ω' ∈ injLabellings G p →
      pinEvent S' s' ω' → (∀ v ∈ β, ω v = ω' v) → f ω = f ω')
    (hfβ' : ∀ ω ω', ω ∈ injLabellings G p → pinEvent S' s' ω → ω' ∈ injLabellings G p →
      pinEvent S' s' ω' → (∀ v ∈ β', ω v = ω' v) → f ω = f ω')
    {ω ω' : U → ZMod p} (hω : ω ∈ injLabellings G p) (hωS : pinEvent S' s' ω)
    (hω' : ω' ∈ injLabellings G p) (hω'S : pinEvent S' s' ω') : f ω = f ω' := by
  classical
  refine subspaces_funOf G hw hconn S' s' hΔ ((Finset.univ : Finset U).filter (· ∉ S'))
    (fun v hv => (Finset.mem_filter.mp hv).2) f ?_ hω hωS hω' ?_
  · intro i _ a b ha haS hb hbS hab
    by_cases hiβ : i ∈ β
    · have hiβ' : i ∉ β' := Finset.disjoint_left.mp hdisj hiβ
      exact hfβ' a b ha haS hb hbS (fun v hv => hab v (fun h => hiβ' (h ▸ hv)))
    · exact hfβ a b ha haS hb hbS (fun v hv => hab v (fun h => hiβ (h ▸ hv)))
  · intro u hu
    have huS : u ∈ S' := by
      by_contra h
      exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [hωS u huS, hω'S u huS]

end Sarkozy.Influence
