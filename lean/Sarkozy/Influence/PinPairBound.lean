module

public import Sarkozy.Influence.PinPair
public import Sarkozy.Influence.Pinned

/-!
# Pinned influence, VII: `lem:mid:pinpair`

The bound `ρ(y_i; y_j | y_{U \ {i,j}} = z) ≤ ε_ij` (`pinpair`) for distinct free vertices `i`,
`j` and a feasible value `z`. The ingredients are:

* `mem_inj_compl2`: the allowed pairs are those with `x ∈ S_i`, `x' ∈ S_j`, `x ≠ x'` and the
  square constraint on the edge `ij`, if any (`pinSet`).
* `row_count_ge`: every row has at least `p 2^{-d_j} (1 - w)` allowed pairs. This uses the
  first count-error inequality of `eq:mid:standing`, with the roots
  `z(N_j) ∪ {x}` (or `z(N_j)` for a non-edge) and the excluded set `z(U \ {i,j}) ∪ {x}`.
* The operator norm of `K - kJ` on `S_i × S_j`. For an edge it is a block of the matrix
  `(A_p(±(x'-x)) - 1/2)`, whose norm is at most `(√p+1)/2` by `lem:square-shift` (a). That
  bound is taken as the explicit hypothesis `SquareShiftBound p`, since it is not proved
  in the project. For a non-edge, `K - J` is minus a partial identity, of norm at most `1`.
* `maxCorr_kernelLaw_le` (the linear-algebra core) and the arithmetic of `eq:mid:epsij`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy Sarkozy.Peyre

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ} [NeZero p]

open Classical in
/-- `A_p(t) = 1_{Q_p}(t)` as a real number. -/
noncomputable def sqInd (t : ZMod p) : ℝ := if IsNzSq t then 1 else 0

/-- `lem:square-shift` (a), matrix form, as an explicit hypothesis: for `σ = ±1` the
`𝔽_p × 𝔽_p` matrix `(A_p(σ(x' - x)) - 1/2)_{x,x'}` has norm at most `(√p + 1)/2`. -/
def SquareShiftBound (p : ℕ) [NeZero p] : Prop :=
  ∀ σ : ZMod p, (σ = 1 ∨ σ = -1) →
    OpBound (Finset.univ : Finset (ZMod p)) Finset.univ
      (fun x x' => sqInd (σ * (x' - x)) - 1 / 2) ((√(p : ℝ) + 1) / 2)

open Classical in
/-- `S_i`: the labels of `i` outside `z(U \ {i,j})` that satisfy the constraints between `i`
and the pinned vertices. -/
noncomputable def pinSet (G : OrientedGraph U) (i j : U) (z : U → ZMod p) :
    Finset (ZMod p) :=
  Finset.univ.filter (fun x => (∀ v ∈ offPair i j, z v ≠ x) ∧
    ∀ v ∈ offPair i j, (G.edge i v → IsNzSq (z v - x)) ∧ (G.edge v i → IsNzSq (x - z v)))

theorem offPair_comm (i j : U) : offPair i j = offPair j i := by
  unfold offPair
  rw [Finset.pair_comm]

omit [Fintype U] [NeZero p] in
theorem compl2_comm {i j : U} (hij : i ≠ j) (z : U → ZMod p) (x x' : ZMod p) :
    compl2 i j z x x' = compl2 j i z x' x := by
  funext v
  unfold compl2
  by_cases hvi : v = i
  · subst hvi
    simp [hij]
  · by_cases hvj : v = j
    · subst hvj
      simp [hvi]
    · simp [hvi, hvj]

theorem pinKernel_comm (G : OrientedGraph U) {i j : U} (hij : i ≠ j) (z : U → ZMod p)
    (x x' : ZMod p) : pinKernel G i j z x x' = pinKernel G j i z x' x := by
  unfold pinKernel
  rw [compl2_comm hij]

theorem mem_injLabellings {G : OrientedGraph U} {ω : U → ZMod p} :
    ω ∈ injLabellings G p ↔ Function.Injective ω ∧ IsStrictSquare G ω := by
  classical
  simp [injLabellings]

omit [NeZero p] in
/-- The value of a completion at any vertex. -/
theorem compl2_cases {i j : U} (z : U → ZMod p) (x x' : ZMod p) (v : U) :
    (v = i ∧ compl2 i j z x x' v = x) ∨ (v ≠ i ∧ v = j ∧ compl2 i j z x x' v = x') ∨
      (v ∈ offPair i j ∧ compl2 i j z x x' v = z v) := by
  by_cases hvi : v = i
  · subst hvi
    exact Or.inl ⟨rfl, compl2_left _ _ z x x'⟩
  · by_cases hvj : v = j
    · subst hvj
      exact Or.inr (Or.inl ⟨hvi, rfl, compl2_right (Ne.symm (Ne.symm hvi)) z x x' ▸ by
        simp [compl2, hvi]⟩)
    · exact Or.inr (Or.inr ⟨mem_offPair.mpr ⟨hvi, hvj⟩, compl2_off z x x' hvi hvj⟩)

/-- The allowed pairs (`lem:mid:pinpair`, first paragraph). Here `z` is injective and
strict-square on `U \ {i,j}`. -/
theorem mem_inj_compl2 (G : OrientedGraph U) {i j : U} (hij : i ≠ j) (z : U → ZMod p)
    (hzinj : ∀ v ∈ offPair i j, ∀ v' ∈ offPair i j, z v = z v' → v = v')
    (hzsq : ∀ v ∈ offPair i j, ∀ v' ∈ offPair i j, G.edge v v' → IsNzSq (z v' - z v))
    (x x' : ZMod p) :
    compl2 i j z x x' ∈ injLabellings G p ↔
      x ∈ pinSet G i j z ∧ x' ∈ pinSet G j i z ∧ x ≠ x' ∧
        (G.edge i j → IsNzSq (x' - x)) ∧ (G.edge j i → IsNzSq (x - x')) := by
  classical
  have hci : compl2 i j z x x' i = x := compl2_left _ _ z x x'
  have hcj : compl2 i j z x x' j = x' := compl2_right hij z x x'
  have hco : ∀ v ∈ offPair i j, compl2 i j z x x' v = z v := fun v hv =>
    compl2_off z x x' (mem_offPair.mp hv).1 (mem_offPair.mp hv).2
  rw [mem_injLabellings]
  simp only [pinSet, Finset.mem_filter, Finset.mem_univ, true_and, ← offPair_comm i j]
  constructor
  · rintro ⟨hinj, hsq⟩
    refine ⟨⟨fun v hv hzv => ?_, fun v hv => ⟨fun he => ?_, fun he => ?_⟩⟩,
      ⟨fun v hv hzv => ?_, fun v hv => ⟨fun he => ?_, fun he => ?_⟩⟩, fun hxx => ?_,
      fun he => ?_, fun he => ?_⟩
    · have : v = i := hinj (by rw [hco v hv, hci, hzv])
      exact (mem_offPair.mp hv).1 this
    · have := hsq i v he
      rwa [hco v hv, hci] at this
    · have := hsq v i he
      rwa [hco v hv, hci] at this
    · have : v = j := hinj (by rw [hco v hv, hcj, hzv])
      exact (mem_offPair.mp hv).2 this
    · have := hsq j v he
      rwa [hco v hv, hcj] at this
    · have := hsq v j he
      rwa [hco v hv, hcj] at this
    · exact hij (hinj (by rw [hci, hcj, hxx]))
    · have := hsq i j he
      rwa [hci, hcj] at this
    · have := hsq j i he
      rwa [hci, hcj] at this
  · rintro ⟨⟨hxz, hxc⟩, ⟨hx'z, hx'c⟩, hxx, hij', hji'⟩
    refine ⟨fun v₁ v₂ h12 => ?_, fun u v he => ?_⟩
    · rcases compl2_cases (j := j) z x x' v₁ with ⟨h1, e1⟩ | ⟨_, h1, e1⟩ | ⟨h1, e1⟩ <;>
      rcases compl2_cases (j := j) z x x' v₂ with ⟨h2, e2⟩ | ⟨_, h2, e2⟩ | ⟨h2, e2⟩
      · rw [h1, h2]
      · rw [e1, e2] at h12; exact absurd h12 hxx
      · rw [e1, e2] at h12; exact absurd h12.symm (hxz v₂ h2)
      · rw [e1, e2] at h12; exact absurd h12.symm hxx
      · rw [h1, h2]
      · rw [e1, e2] at h12; exact absurd h12.symm (hx'z v₂ h2)
      · rw [e1, e2] at h12; exact absurd h12 (hxz v₁ h1)
      · rw [e1, e2] at h12; exact absurd h12 (hx'z v₁ h1)
      · rw [e1, e2] at h12; exact hzinj v₁ h1 v₂ h2 h12
    · rcases compl2_cases (j := j) z x x' u with ⟨h1, e1⟩ | ⟨_, h1, e1⟩ | ⟨h1, e1⟩ <;>
      rcases compl2_cases (j := j) z x x' v with ⟨h2, e2⟩ | ⟨_, h2, e2⟩ | ⟨h2, e2⟩ <;>
      rw [e1, e2]
      · subst h1; subst h2; exact absurd he (G.irrefl _)
      · subst h1; subst h2; exact hij' he
      · subst h1; exact (hxc v h2).1 he
      · subst h1; subst h2; exact hji' he
      · subst h1; subst h2; exact absurd he (G.irrefl _)
      · subst h1; exact (hx'c v h2).1 he
      · subst h2; exact (hxc u h1).2 he
      · subst h2; exact (hx'c u h1).2 he
      · exact hzsq u h1 v h2 he

/-- Feasibility of `z` makes it injective and strict-square on `U \ {i,j}`. -/
theorem feasible_props (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty) {i j : U}
    (z : U → ZMod p) (h : 0 < prob (graphLaw G p hInj) (pinEvent (offPair i j) z)) :
    (∀ v ∈ offPair i j, ∀ v' ∈ offPair i j, z v = z v' → v = v') ∧
      (∀ v ∈ offPair i j, ∀ v' ∈ offPair i j, G.edge v v' → IsNzSq (z v' - z v)) := by
  classical
  obtain ⟨ω₀, hω₀, hw⟩ := exists_of_prob_pos h
  have hmem : ω₀ ∈ injLabellings G p := by
    by_contra hn
    apply hw
    simp only [graphLaw, hn, ite_false]
  obtain ⟨hinj, hsq⟩ := mem_injLabellings.mp hmem
  refine ⟨fun v hv v' hv' hzz => hinj (by rw [hω₀ v hv, hω₀ v' hv', hzz]),
    fun v hv v' hv' he => ?_⟩
  have := hsq v v' he
  rwa [hω₀ v hv, hω₀ v' hv'] at this

/-- A row sum of the pinned kernel dominates any count of `eq:mid:standing` whose admissible
labels are allowed. -/
theorem standingCount_le_row (G : OrientedGraph U) {i j : U} (hij : i ≠ j) (z : U → ZMod p)
    (hzinj : ∀ v ∈ offPair i j, ∀ v' ∈ offPair i j, z v = z v' → v = v')
    (hzsq : ∀ v ∈ offPair i j, ∀ v' ∈ offPair i j, G.edge v v' → IsNzSq (z v' - z v))
    {x : ZMod p} (hx : x ∈ pinSet G i j z) {t : ℕ} (a sg : Fin t → ZMod p)
    (E' : Finset (ZMod p)) (hxE : x ∈ E')
    (hP : ∀ x', x' ∉ E' → (∀ m, IsNzSq (sg m * (x' - a m))) →
      x' ∈ pinSet G j i z ∧ (G.edge i j → IsNzSq (x' - x)) ∧ (G.edge j i → IsNzSq (x - x'))) :
    (standingCount a sg E' : ℝ) ≤ ∑ x', pinKernel G i j z x x' := by
  classical
  have e : ∑ x', pinKernel G i j z x x' =
      (((Finset.univ : Finset (ZMod p)).filter
        (fun x' => compl2 i j z x x' ∈ injLabellings G p)).card : ℝ) := by
    simp only [pinKernel]
    rw [Finset.sum_boole]
  rw [e]
  unfold standingCount
  exact_mod_cast Finset.card_le_card (fun x' hx' => by
    rw [Finset.mem_filter] at hx' ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨hx'E, hcon⟩ := hx'.2
    obtain ⟨h1, h2, h3⟩ := hP x' hx'E hcon
    exact (mem_inj_compl2 G hij z hzinj hzsq x x').mpr
      ⟨hx, h1, fun hxx => hx'E (hxx ▸ hxE), h2, h3⟩)

/-- Each row of the pinned kernel has at least `p 2^{-d_j} (1 - w)` allowed entries, by the
first inequality of `eq:mid:standing` (`lem:mid:pinpair`). -/
theorem row_count_ge (G : OrientedGraph U) {i j : U} (hij : i ≠ j) (z : U → ZMod p)
    (hzinj : ∀ v ∈ offPair i j, ∀ v' ∈ offPair i j, z v = z v' → v = v')
    (hzsq : ∀ v ∈ offPair i j, ∀ v' ∈ offPair i j, G.edge v v' → IsNzSq (z v' - z v))
    {T : ℕ} (hT : G.deg j ≤ T) {w : ℝ} (hw1 : w ≤ 1)
    (hw : StandingBound p T (Fintype.card U) w) {x : ZMod p} (hx : x ∈ pinSet G i j z) :
    (1 - w) * p / 2 ^ G.deg j ≤ ∑ x', pinKernel G i j z x x' := by
  classical
  set Nj := (offPair i j).filter (fun v => G.Adj j v) with hNj
  set eN : Fin Nj.card ≃ Nj := Nj.equivFin.symm with heN
  set sgv : U → ZMod p := fun v => if G.edge v j then 1 else -1 with hsgv
  set E' : Finset (ZMod p) := insert x ((offPair i j).image z) with hE'
  have hxE : x ∈ E' := Finset.mem_insert_self _ _
  have hxz : ∀ v ∈ offPair i j, z v ≠ x := by
    have := (Finset.mem_filter.mp hx).2
    exact this.1
  have hNT : ∀ v ∈ Nj, v ∈ offPair i j := fun v hv => (Finset.mem_filter.mp hv).1
  have hNadj : ∀ v ∈ Nj, G.Adj j v := fun v hv => (Finset.mem_filter.mp hv).2
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  -- the card bound `|E'| ≤ n`
  have hcardE : E'.card ≤ Fintype.card U := by
    have h1 : E'.card ≤ ((offPair i j).image z).card + 1 := Finset.card_insert_le _ _
    have h2 : ((offPair i j).image z).card ≤ (offPair i j).card := Finset.card_image_le
    have h3 : (offPair i j).card + 1 ≤ Fintype.card U := by
      have hi : i ∉ offPair i j := fun h => (mem_offPair.mp h).1 rfl
      rw [← Finset.card_insert_of_notMem hi]
      exact Finset.card_le_univ _
    omega
  -- the pinned-neighbour constraints give `x' ∈ S_j`
  have hSj : ∀ x', x' ∉ E' → (∀ m : Fin Nj.card, IsNzSq (sgv (eN m) * (x' - z (eN m)))) →
      x' ∈ pinSet G j i z := by
    intro x' hx'E hcon
    simp only [pinSet, Finset.mem_filter, Finset.mem_univ, true_and, ← offPair_comm i j]
    have hzE : ∀ v ∈ offPair i j, z v ∈ E' := fun v hv =>
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem z hv)
    refine ⟨fun v hv hzv => hx'E (hzv ▸ hzE v hv), fun v hv => ?_⟩
    by_cases hadj : G.Adj j v
    · have hvN : v ∈ Nj := Finset.mem_filter.mpr ⟨hv, hadj⟩
      have hm := hcon (eN.symm ⟨v, hvN⟩)
      simp only [Equiv.apply_symm_apply] at hm
      constructor
      · intro he
        have hne : ¬ G.edge v j := G.asymm j v he
        simp only [hsgv, hne, ite_false] at hm
        have e : (-1 : ZMod p) * (x' - z v) = z v - x' := by ring
        rwa [e] at hm
      · intro he
        simp only [hsgv, he, ite_true, one_mul] at hm
        exact hm
    · exact ⟨fun he => absurd (Or.inl he) hadj, fun he => absurd (Or.inr he) hadj⟩
  have hsgv1 : ∀ v, sgv v = 1 ∨ sgv v = -1 := by
    intro v
    simp only [hsgv]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hinjN : Function.Injective (fun m : Fin Nj.card => z (eN m)) := by
    intro m m' hmm
    have h1 : ((eN m : U)) = eN m' := hzinj _ (hNT _ (eN m).2) _ (hNT _ (eN m').2) hmm
    exact eN.injective (Subtype.ext h1)
  have hNdeg : Nj.card ≤ G.deg j := by
    unfold OrientedGraph.deg
    exact Finset.card_le_card (fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNadj v hv⟩)
  -- the count with `t` roots gives the bound `(1 - w) p / 2^t`
  have key : ∀ (t : ℕ) (a sg : Fin t → ZMod p), t ≤ G.deg j → Function.Injective a →
      (∀ m, sg m = 1 ∨ sg m = -1) → (∀ m, a m ∈ E') →
      (∀ x', x' ∉ E' → (∀ m, IsNzSq (sg m * (x' - a m))) →
        x' ∈ pinSet G j i z ∧ (G.edge i j → IsNzSq (x' - x)) ∧ (G.edge j i → IsNzSq (x - x'))) →
      (1 - w) * p / 2 ^ G.deg j ≤ ∑ x', pinKernel G i j z x x' := by
    intro t a sg ht ha hsg haE hP
    have hb := hw t a sg E' ha hsg haE (ht.trans hT) hcardE
    have hle := standingCount_le_row G hij z hzinj hzsq hx a sg E' hxE hP
    have h2t : (0 : ℝ) < 2 ^ t := by positivity
    have h1 : (1 - w) * p / 2 ^ t ≤ standingCount a sg E' := by
      rw [div_le_iff₀ h2t]
      rw [le_div_iff₀ hp] at hb
      linarith
    have h2 : (1 - w) * p / 2 ^ G.deg j ≤ (1 - w) * p / 2 ^ t := by
      have hw1' : 0 ≤ (1 - w) * p := mul_nonneg (by linarith) hp.le
      exact div_le_div_of_nonneg_left hw1' h2t (pow_le_pow_right₀ (by norm_num) ht)
    linarith
  have hzE : ∀ v ∈ offPair i j, z v ∈ E' := fun v hv =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem z hv)
  by_cases hadj : G.Adj i j
  · -- the roots are `x` and the labels of the pinned neighbours of `j`
    have hadj' : G.Adj j i := G.adj_symm hadj
    have hiN : i ∉ Nj := fun h => (mem_offPair.mp (hNT i h)).1 rfl
    have ht : Nj.card + 1 ≤ G.deg j := by
      rw [← Finset.card_insert_of_notMem hiN]
      unfold OrientedGraph.deg
      refine Finset.card_le_card (fun v hv => ?_)
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj'⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNadj v hv⟩
    refine key (Nj.card + 1) (Fin.cons x (fun m => z (eN m)))
      (Fin.cons (if G.edge i j then 1 else -1) (fun m => sgv (eN m))) ht ?_ ?_ ?_ ?_
    · rw [Fin.cons_injective_iff]
      exact ⟨fun ⟨m, hm⟩ => hxz _ (hNT _ (eN m).2) hm, hinjN⟩
    · intro m
      refine Fin.cases ?_ (fun m => ?_) m
      · simp only [Fin.cons_zero]
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
      · simp only [Fin.cons_succ]
        exact hsgv1 _
    · intro m
      refine Fin.cases ?_ (fun m => ?_) m
      · simp only [Fin.cons_zero]
        exact hxE
      · simp only [Fin.cons_succ]
        exact hzE _ (hNT _ (eN m).2)
    · intro x' hx'E hcon
      rw [Fin.forall_fin_succ] at hcon
      obtain ⟨h0, hs⟩ := hcon
      simp only [Fin.cons_zero, Fin.cons_succ] at h0 hs
      refine ⟨hSj x' hx'E hs, fun he => ?_, fun he => ?_⟩
      · simp only [he, ite_true, one_mul] at h0
        exact h0
      · have hne : ¬ G.edge i j := G.asymm j i he
        simp only [hne, ite_false] at h0
        have e : (-1 : ZMod p) * (x' - x) = x - x' := by ring
        rwa [e] at h0
  · -- the roots are the labels of the pinned neighbours of `j`
    refine key Nj.card (fun m => z (eN m)) (fun m => sgv (eN m)) hNdeg hinjN
      (fun m => hsgv1 _) (fun m => hzE _ (hNT _ (eN m).2)) ?_
    intro x' hx'E hcon
    exact ⟨hSj x' hx'E hcon, fun he => absurd (Or.inl he) hadj,
      fun he => absurd (Or.inr he) hadj⟩

/-- The arithmetic of `eq:mid:epsij` for an edge: with `A = (1-w) p 2^{-d_j}`,
`B = (1-w) p 2^{-d_i}` and `L = (√p+1)/2`,
`L/√(AB) = 2^{(d_i+d_j-2)/2} (r + r²)/(1-w) ≤ ε_ij`. -/
theorem pinpair_arith_edge {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) {q : ℝ} (hq : 0 < q)
    {di dj : ℕ} (hd : 2 ≤ di + dj) :
    ((√q + 1) / 2) / √(((1 - w) * q / 2 ^ dj) * ((1 - w) * q / 2 ^ di)) ≤
      Hw w * √2 ^ (di + dj - 2) * (1 / √q + (1 / √q) ^ 2) := by
  have hc : 0 < 1 - w := by linarith
  have hs : 0 < √q := Real.sqrt_pos.mpr hq
  have hs2 : √q ^ 2 = q := Real.sq_sqrt hq.le
  have h2 : (0 : ℝ) < √2 := by positivity
  set m := di + dj - 2 with hm
  have hmd : di + dj = m + 2 := by omega
  have hpow : ∀ n : ℕ, (√2 ^ n) ^ 2 = 2 ^ n := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hAB : ((1 - w) * q / 2 ^ dj) * ((1 - w) * q / 2 ^ di) =
      ((1 - w) * q / √2 ^ (di + dj)) ^ 2 := by
    rw [div_pow, hpow, pow_add]
    field_simp
  rw [hAB, Real.sqrt_sq (by positivity), hmd, pow_add, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold Hw
  have hm0 : 0 < √2 ^ m := by positivity
  rw [div_le_iff₀ (by positivity)]
  have e : (1 / √q + (1 / √q) ^ 2) = (√q + 1) / q := by
    field_simp
    rw [hs2]
  rw [e]
  have key : (1 - w) ≤ 1 + w := by linarith
  have hq' : q ≠ 0 := hq.ne'
  field_simp
  nlinarith [mul_pos hm0 hs, mul_pos hm0 hc, mul_pos (mul_pos hm0 hc) hs, sq_nonneg (1 - w),
    mul_pos (mul_pos hm0 (mul_pos hc hc)) (add_pos hs one_pos)]

/-- The arithmetic of `eq:mid:epsij` for a non-edge: `1/√(AB) = 2^{(d_i+d_j)/2} r²/(1-w)
≤ ε_ij`. -/
theorem pinpair_arith_nonedge {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) {q : ℝ} (hq : 0 < q)
    (di dj : ℕ) :
    1 / √(((1 - w) * q / 2 ^ dj) * ((1 - w) * q / 2 ^ di)) ≤
      Hw w * √2 ^ (di + dj) * (1 / √q) ^ 2 := by
  have hc : 0 < 1 - w := by linarith
  have hs2 : √q ^ 2 = q := Real.sq_sqrt hq.le
  have hpow : ∀ n : ℕ, (√2 ^ n) ^ 2 = 2 ^ n := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hAB : ((1 - w) * q / 2 ^ dj) * ((1 - w) * q / 2 ^ di) =
      ((1 - w) * q / √2 ^ (di + dj)) ^ 2 := by
    rw [div_pow, hpow, pow_add]
    field_simp
  rw [hAB, Real.sqrt_sq (by positivity)]
  unfold Hw
  have hm0 : 0 < √2 ^ (di + dj) := by positivity
  rw [one_div_div, div_pow, one_pow, hs2]
  rw [div_le_iff₀ (by positivity)]
  have key : (1 - w) ≤ 1 + w := by linarith
  field_simp
  nlinarith [mul_pos hm0 hc, mul_pos (mul_pos hm0 hc) hq]

omit [NeZero p] in
/-- The non-edge block `K - J = -(partial identity)` has norm at most `1`. -/
theorem opBound_neg_diag (Si Sj : Finset (ZMod p)) :
    OpBound Si Sj (fun x x' => -(if x = x' then (1 : ℝ) else 0)) 1 := by
  classical
  intro u
  have e : ∀ x, ∑ x' ∈ Sj, -(if x = x' then (1 : ℝ) else 0) * u x' =
      -(if x ∈ Sj then u x else 0) := by
    intro x
    simp only [neg_mul, ite_mul, one_mul, zero_mul, Finset.sum_neg_distrib]
    rw [Finset.sum_ite_eq Sj x]
  simp_rw [e]
  rw [one_pow, one_mul]
  calc ∑ x ∈ Si, (-(if x ∈ Sj then u x else 0)) ^ 2 = ∑ x ∈ Si.filter (· ∈ Sj), u x ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        split_ifs <;> simp
    _ ≤ ∑ x ∈ Sj, u x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).2)
          (fun _ _ _ => sq_nonneg _)

/-- **`lem:mid:pinpair`.** Let `F` contain the distinct vertices `i, j`, and let `w < 1`
satisfy the first inequality of `eq:mid:standing` with `Δ_F = maxDeg G F` and `n = |U|`.
Assume `lem:square-shift` (a) in the form `SquareShiftBound p`. Then, for every feasible
value `z` of `y_{U \ {i,j}}`, `ρ(y_i; y_j | y_{U \ {i,j}} = z) ≤ ε_ij`. The paper's
hypothesis that `z` extends the pinning `(S, s)` is not needed. -/
theorem pinpair (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)
    (hsq : SquareShiftBound p) (F : Finset U) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hw : StandingBound p (maxDeg G F) (Fintype.card U) w) {i j : U} (hi : i ∈ F)
    (hj : j ∈ F) (hij : i ≠ j) (z : U → ZMod p)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent (offPair i j) z)) :
    maxCorr (condLaw (graphLaw G p hInj) (pinEvent (offPair i j) z) h)
      (fun ω => ω i) (fun ω => ω j) ≤ influence G p w i j := by
  classical
  obtain ⟨hzinj, hzsq⟩ := feasible_props G hInj z h
  have hzinj' : ∀ v ∈ offPair j i, ∀ v' ∈ offPair j i, z v = z v' → v = v' := by
    rw [← offPair_comm]; exact hzinj
  have hzsq' : ∀ v ∈ offPair j i, ∀ v' ∈ offPair j i, G.edge v v' → IsNzSq (z v' - z v) := by
    rw [← offPair_comm]; exact hzsq
  have hdi : G.deg i ≤ maxDeg G F := Finset.le_sup (f := G.deg) hi
  have hdj : G.deg j ≤ maxDeg G F := Finset.le_sup (f := G.deg) hj
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  rw [maxCorr_pin_eq G hInj hij z h]
  set K := pinKernel G i j z with hK
  set Si := pinSet G i j z with hSi
  set Sj := pinSet G j i z with hSj
  set A := (1 - w) * p / 2 ^ G.deg j with hA
  set B := (1 - w) * p / 2 ^ G.deg i with hB
  have hApos : 0 < A := div_pos (mul_pos (by linarith) hp) (by positivity)
  have hBpos : 0 < B := div_pos (mul_pos (by linarith) hp) (by positivity)
  have hmem := mem_inj_compl2 G hij z hzinj hzsq
  have hsupp : ∀ x x', K x x' ≠ 0 → x ∈ Si ∧ x' ∈ Sj := by
    intro x x' hK0
    have hin : compl2 i j z x x' ∈ injLabellings G p := by
      by_contra hn
      exact hK0 (by simp only [hK, pinKernel, hn, ite_false])
    obtain ⟨h1, h2, -⟩ := (hmem x x').mp hin
    exact ⟨h1, h2⟩
  have hrow_full : ∀ x, ∑ x' ∈ Sj, K x x' = ∑ x', K x x' := by
    intro x
    refine Finset.sum_subset (Finset.subset_univ _) (fun x' _ hx' => ?_)
    by_contra hK0
    exact hx' (hsupp x x' hK0).2
  have hcol_full : ∀ x', ∑ x ∈ Si, K x x' = ∑ x, K x x' := by
    intro x'
    refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
    by_contra hK0
    exact hx (hsupp x x' hK0).1
  have ha : ∀ x ∈ Si, A ≤ ∑ x' ∈ Sj, K x x' := by
    intro x hx
    rw [hrow_full]
    exact row_count_ge G hij z hzinj hzsq hdj hw1.le hw hx
  have hb : ∀ x' ∈ Sj, B ≤ ∑ x ∈ Si, K x x' := by
    intro x' hx'
    rw [hcol_full]
    have := row_count_ge G (Ne.symm hij) z hzinj' hzsq' hdi hw1.le hw hx'
    simp only [hK]
    rw [Finset.sum_congr rfl (fun x _ => pinKernel_comm G hij z x x')]
    exact this
  have hgoal_rp : rp p = 1 / √(p : ℝ) := rfl
  by_cases hadj : G.Adj i j
  · -- an edge: `K - 1/2` is a block of the square-shift matrix
    set σ : ZMod p := if G.edge i j then 1 else -1 with hσ
    have hσ1 : σ = 1 ∨ σ = -1 := by
      simp only [hσ]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hblock : ∀ x ∈ Si, ∀ x' ∈ Sj, sqInd (σ * (x' - x)) - 1 / 2 = K x x' - 1 / 2 := by
      intro x hx x' hx'
      congr 1
      have hiff : compl2 i j z x x' ∈ injLabellings G p ↔ IsNzSq (σ * (x' - x)) := by
        rw [hmem x x']
        by_cases he : G.edge i j
        · have hne : ¬ G.edge j i := G.asymm i j he
          simp only [hσ, he, ite_true, one_mul, hne, IsEmpty.forall_iff, and_true, true_implies]
          constructor
          · rintro ⟨-, -, -, h1⟩
            exact h1
          · intro h1
            refine ⟨hx, hx', fun hxx => h1.1 (by rw [hxx, sub_self]), h1⟩
        · have hji : G.edge j i := hadj.resolve_left he
          simp only [hσ, he, ite_false, IsEmpty.forall_iff, true_and, hji, true_implies]
          have e : (-1 : ZMod p) * (x' - x) = x - x' := by ring
          rw [e]
          constructor
          · rintro ⟨-, -, -, h1⟩
            exact h1
          · intro h1
            refine ⟨hx, hx', fun hxx => h1.1 (by rw [hxx, sub_self]), h1⟩
      simp only [hK, pinKernel, sqInd]
      by_cases hin : compl2 i j z x x' ∈ injLabellings G p
      · rw [ite_eq_left hin, ite_eq_left (hiff.mp hin)]
      · rw [ite_eq_right hin, ite_eq_right (fun h => hin (hiff.mpr h))]
    have hop : OpBound Si Sj (fun x x' => K x x' - 1 / 2) ((√(p : ℝ) + 1) / 2) :=
      ((hsq σ hσ1).subset (Finset.subset_univ _) (Finset.subset_univ _)).congr hblock
    have hmc := maxCorr_kernelLaw_le K (pinKernel_nonneg G i j z)
      (pinKernel_mass_pos G hInj hij z h) Si Sj hsupp hApos hBpos (by positivity) ha hb hop
    refine hmc.trans ?_
    have hdeg : 2 ≤ G.deg i + G.deg j := by
      have h1 : 1 ≤ G.deg i := by
        unfold OrientedGraph.deg
        exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩⟩
      have h2 : 1 ≤ G.deg j := by
        unfold OrientedGraph.deg
        exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          G.adj_symm hadj⟩⟩
      omega
    have harith := pinpair_arith_edge hw0 hw1 hp hdeg
    rw [mul_comm A B] at harith ⊢
    simp only [influence, hij, ite_false, hadj, ite_true, hgoal_rp]
    rw [mul_comm B A]
    simpa only [hA, hB, mul_comm] using harith
  · -- a non-edge: `K - 1` is minus a partial identity
    have hblock : ∀ x ∈ Si, ∀ x' ∈ Sj, -(if x = x' then (1 : ℝ) else 0) = K x x' - 1 := by
      intro x hx x' hx'
      have hiff : compl2 i j z x x' ∈ injLabellings G p ↔ x ≠ x' := by
        rw [hmem x x']
        have hne1 : ¬ G.edge i j := fun he => hadj (Or.inl he)
        have hne2 : ¬ G.edge j i := fun he => hadj (Or.inr he)
        simp only [hne1, hne2, IsEmpty.forall_iff, and_true]
        exact ⟨fun h => h.2.2, fun h => ⟨hx, hx', h⟩⟩
      simp only [hK, pinKernel]
      by_cases hxx : x = x'
      · rw [ite_eq_left hxx, ite_eq_right (fun h => (hiff.mp h) hxx)]
        ring
      · rw [ite_eq_right hxx, ite_eq_left (hiff.mpr hxx)]
        ring
    have hop : OpBound Si Sj (fun x x' => K x x' - 1) 1 :=
      (opBound_neg_diag Si Sj).congr hblock
    have hmc := maxCorr_kernelLaw_le K (pinKernel_nonneg G i j z)
      (pinKernel_mass_pos G hInj hij z h) Si Sj hsupp hApos hBpos zero_le_one ha hb hop
    refine hmc.trans ?_
    have harith := pinpair_arith_nonedge hw0 hw1 hp (G.deg i) (G.deg j)
    simp only [influence, hij, ite_false, hadj, hgoal_rp]
    simpa only [hA, hB, mul_comm] using harith

end Sarkozy.Influence
