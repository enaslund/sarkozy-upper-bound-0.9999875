module

public import Sarkozy.RecordExpansion.TagSeries
public import Sarkozy.RecordExpansion.SubsetExpansion
public import Sarkozy.RecordExpansion.FirstStage

/-!
# The summation in the tagged sharp-first expansion

`lem:sharp-first` of the paper (Section 10) expands
`⊗_{B ∈ F} (ρ_B + ∑_i δ_{B,i}) - ⊗_{B ∈ F} ρ_B` over the nonempty choices `σ` of at
most one difference `δ_{B,σ(B)}` at every atom, groups the terms into categories by
their count vector `k` (`k_j` = number of chosen differences of tag `j`), bounds every
term analytically at the cut of each tag present, and sums the bounds into the tag
series `𝔗(d, v)`. This file formalizes the expansion and the summation, with the
per-term analytic bound as a hypothesis.

* `tensorLaw_add_sum_eq_sum_optChoices`: the expansion over choices
  `σ : ∀ B, Option (I B)`.
* `abs_energy_sub_le_sharpFirst`: the energy form,
  `|Y_{⊗(ρ + ∑ δ)} - Y_{⊗ρ}| ≤ K e^P 𝔗(d, v) + ∑_σ r_σ` (`lem:sharp-first`).
* `first_stage_lower_bound`: with Step 1 (`first_stage_step_one`), the first
  comparison `Y_λ ≥ Y_μ - K e^P 𝔗(d, v) - ∑_σ r_σ` (`lem:record:first-stage`;
  in the paper `K = (1 + o(1)) Y` and `L_0 = e^P 𝔗(d, v)`).
* `abs_energy_le_bracket`: the combination of `lem:bracket-energy`,
  `|𝔈_Ñ[κ]| ≤ K e^{U_0} + K' e^{U_0} 𝔗(d, v) + ∑_σ r_σ`, i.e. `(B + o(1)) ‖κ‖ Π_X Y` with
  `B = e^{U_0} + R_err`, `R_err = e^{U_0} 𝔗(d, v)`, from the expansion
  `Ñ_0 = μ + (Ñ_0 - μ)` and the sharp-first expansion `Ñ = Ñ_0 + δ_E`.
* `abs_sum_le_tagSeries`: if every nonempty choice satisfies, for every tag `j`
  present in it, `|term σ| ≤ K · wt_j(σ) + r_σ` with
  `wt_j(σ) = ∏_{B ∈ S_j} d_{B,σ(B)} ∏_{B ∈ S ∖ S_j} v_{B,σ(B)} ∏_{B ∉ S} (1 + p_B)`
  (`tagWeight`), then `|∑_{σ ≠ ∅} term σ| ≤ K e^P 𝔗(d, v) + ∑_σ r_σ`, where `d_j`,
  `v_j` are the tag totals and `P = ∑_B p_B`.

The per-term hypothesis is what the paper's proof derives for each term `σ`
and each tag `j` with `k_j ≥ 1` from the folded-energy bounds at the cut `c_j`
(after expanding the positive parts and `ρ_B = μ_B + ∑_h c_h ρ_h`). Here `K`
stands for `(1 + o(1)) ‖κ‖ Π_X Y`, and `r_σ` for the remainders. As in the
paper, the minimum over the tags is taken after a whole category has been
summed. The sum over the terms of a category with fixed tag counts is bounded
by "dropping the distinctness" (`sum_category_le`, through the multinomial
theorem over kinds).
-/

@[expose] public section

open Finset
open scoped BigOperators Nat

namespace Sarkozy.RecordExpansion

section Expansion

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {I : J → Type*} [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]

omit [∀ b, DecidableEq (I b)] in
/-- `⊗_B (A_B + ∑_i D_{B,i}) = ∑_σ ⊗_B (D_{B,σ(B)} if `σ(B) = some i`, `A_B` otherwise)`. -/
theorem tensorLaw_add_sum_eq_sum_optChoices (A : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (D : ∀ b, I b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (fun b => A b + ∑ i, D b i) =
      ∑ σ : (∀ b, Option (I b)), tensorLaw (fun b => (σ b).elim (A b) (D b)) := by
  have h : (fun b => A b + ∑ i, D b i) =
      fun b => ∑ o : Option (I b), o.elim (A b) (D b) := by
    funext b
    rw [Fintype.sum_option]
    rfl
  rw [h, tensorLaw_sum]

/-- The expansion of the difference over the nonempty choices. -/
theorem tensorLaw_add_sum_sub_eq (A : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (D : ∀ b, I b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (fun b => A b + ∑ i, D b i) - tensorLaw A =
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none),
        tensorLaw (fun b => (σ b).elim (A b) (D b)) := by
  rw [tensorLaw_add_sum_eq_sum_optChoices,
    ← Finset.add_sum_erase univ _ (mem_univ (fun _ => none)), Finset.filter_ne']
  have h0 : tensorLaw (fun b => ((fun _ => none : ∀ b, Option (I b)) b).elim (A b) (D b)) =
      tensorLaw A := rfl
  rw [h0, add_sub_cancel_left]

end Expansion

section Summation

variable {J : Type*} [Fintype J] [DecidableEq J] {I : J → Type*} [∀ b, Fintype (I b)]
  [∀ b, DecidableEq (I b)] {Tag : Type*} [Fintype Tag] [DecidableEq Tag]

/-- The count vector of a choice: the number of chosen differences of each tag. -/
def countVec (tag : ∀ b, I b → Tag) (σ : ∀ b, Option (I b)) (j : Tag) : ℕ :=
  (univ.filter fun b => (σ b).map (tag b) = some j).card

/-- The weight `wt_j(σ)` of a choice for the tag `j`: the sharp price of the chosen
differences of tag `j`, the variation price of the other chosen differences, and
`1 + p_B` at the atoms without a chosen difference. -/
noncomputable def tagWeight (tag : ∀ b, I b → Tag) (d v : ∀ b, I b → ℝ) (p : J → ℝ)
    (j : Tag) (σ : ∀ b, Option (I b)) : ℝ :=
  ∏ b, (σ b).elim (1 + p b) (fun i => if tag b i = j then d b i else v b i)

/-- The tag totals `d_j = ∑_{tag(B,i) = j} d_{B,i}`. -/
noncomputable def tagTotal (tag : ∀ b, I b → Tag) (d : ∀ b, I b → ℝ) (j : Tag) : ℝ :=
  ∑ b, ∑ i, if tag b i = j then d b i else 0

/-- The monomial of a choice on the variables `(B, i)`. -/
def optMono (σ : ∀ b, Option (I b)) : (Σ b, I b) → ℕ := fun x => if σ x.1 = some x.2 then 1 else 0

omit [Fintype J] [DecidableEq J] [∀ b, Fintype (I b)] in
theorem optMono_injective : Function.Injective (optMono (I := I)) := by
  intro σ σ' h
  funext b
  have key : ∀ i : I b, σ b = some i ↔ σ' b = some i := by
    intro i
    have h1 := congrFun h ⟨b, i⟩
    simp only [optMono] at h1
    by_cases hi : σ b = some i <;> by_cases hi' : σ' b = some i <;> simp_all
  rcases hb : σ b with _ | i
  · rcases hb' : σ' b with _ | i'
    · rfl
    · have h2 := (key i').mpr hb'
      rw [hb] at h2
      exact absurd h2 (by simp)
  · exact ((key i).mp hb).symm

omit [DecidableEq J] in
theorem prod_optMono (z : (Σ b, I b) → ℝ) (σ : ∀ b, Option (I b)) :
    ∏ x, z x ^ optMono σ x = ∏ b, (σ b).elim 1 (fun i => z ⟨b, i⟩) := by
  rw [Fintype.prod_sigma]
  apply prod_congr rfl
  intro b _
  change (∏ i : I b, z ⟨b, i⟩ ^ (if σ b = some i then 1 else 0)) = (σ b).elim 1 _
  rcases σ b with _ | i₀
  · simp
  · have he : ∀ i : I b, z ⟨b, i⟩ ^ (if some i₀ = some i then 1 else 0) =
        if i₀ = i then z ⟨b, i⟩ else 1 := by
      intro i
      by_cases hi : i₀ = i
      · subst hi
        simp
      · have hi' : some i₀ ≠ some i := fun h => hi (Option.some.inj h)
        simp [hi, hi']
    rw [Finset.prod_congr rfl (fun i _ => he i), Fintype.prod_ite_eq]
    rfl

omit [DecidableEq J] in
theorem prod_factorial_optMono (σ : ∀ b, Option (I b)) :
    ∏ x, ((optMono σ x)! : ℝ) = 1 := by
  apply prod_eq_one
  intro x _
  unfold optMono
  split_ifs <;> simp

theorem optMono_mem_kindMonos (tag : ∀ b, I b → Tag) (σ : ∀ b, Option (I b)) :
    optMono σ ∈ kindMonos (fun x : (Σ b, I b) => some (tag x.1 x.2)) (countVec tag σ) := by
  rw [mem_kindMonos]
  refine ⟨fun x hx => absurd hx (by simp), ?_⟩
  intro j
  unfold countVec optMono kindSet
  rw [card_eq_sum_ones, sum_filter, sum_filter, Fintype.sum_sigma]
  apply sum_congr rfl
  intro b _
  have key : ∀ o : Option (I b),
      (∑ y : I b, if some (tag b y) = some j then (if o = some y then (1 : ℕ) else 0) else 0) =
        if o.map (tag b) = some j then 1 else 0 := by
    intro o
    rcases o with _ | i₀
    · simp
    · rw [Finset.sum_eq_single i₀]
      · simp
      · intro i _ hi
        have hi' : (some i₀ : Option (I b)) ≠ some i := fun h' => hi (Option.some.inj h').symm
        simp [hi']
      · intro h'
        exact absurd (mem_univ _) h'
  exact key (σ b)

/-- **Dropping the distinctness**: the sum of the weights of the choices with count
vector `k`, for the tag `j`, is at most `e^P · tagTerm d v k j`. -/
theorem sum_category_le (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ} {p : J → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (hp : ∀ b, 0 ≤ p b)
    (k : Tag → ℕ) (j : Tag) :
    ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => countVec tag σ = k),
        tagWeight tag d v p j σ ≤
      Real.exp (∑ b, p b) * tagTerm (tagTotal tag d) (tagTotal tag v) k j := by
  set kind : (Σ b, I b) → Option Tag := fun x => some (tag x.1 x.2) with hkind
  set z : (Σ b, I b) → ℝ := fun x => if tag x.1 x.2 = j then d x.1 x.2 else v x.1 x.2
    with hzdef
  have hz : ∀ x, 0 ≤ z x := by
    intro x
    simp only [hzdef]
    split_ifs
    · exact hd _ _
    · exact hv _ _
  set cat := univ.filter (fun σ : (∀ b, Option (I b)) => countVec tag σ = k) with hcat
  -- the weight is at most `∏ (1 + p_B)` times the monomial
  have hwt : ∀ σ, tagWeight tag d v p j σ ≤ (∏ b, (1 + p b)) * ∏ x, z x ^ optMono σ x := by
    intro σ
    rw [prod_optMono, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro b _
      rcases σ b with _ | i
      · exact add_nonneg zero_le_one (hp b)
      · exact hz ⟨b, i⟩
    · intro b _
      rcases σ b with _ | i
      · simp
      · change z ⟨b, i⟩ ≤ (1 + p b) * z ⟨b, i⟩
        nlinarith [hz ⟨b, i⟩, hp b]
  have hinj : Set.InjOn optMono (cat : Set (∀ b, Option (I b))) :=
    fun a _ b _ h => optMono_injective h
  have hmono : ∑ σ ∈ cat, ∏ x, z x ^ optMono σ x ≤
      ∑ m ∈ kindMonos kind k, ∏ x, z x ^ m x / ((m x)! : ℝ) := by
    rw [← sum_image (f := fun m : (Σ b, I b) → ℕ => ∏ x, z x ^ m x) hinj]
    have h1 : ∑ m ∈ cat.image optMono, ∏ x, z x ^ m x =
        ∑ m ∈ cat.image optMono, ∏ x, z x ^ m x / ((m x)! : ℝ) := by
      apply sum_congr rfl
      intro m hm
      obtain ⟨σ, _, rfl⟩ := mem_image.mp hm
      rw [Finset.prod_div_distrib, prod_factorial_optMono, div_one]
    rw [h1]
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hm
      have hk : countVec tag σ = k := (mem_filter.mp hσ).2
      rw [← hk]
      exact optMono_mem_kindMonos tag σ
    · intro m _ _
      exact prod_nonneg fun x _ => div_nonneg (pow_nonneg (hz x) _) (by positivity)
  have hmult := prod_kind_pow_div kind k z
  have htot : ∀ j', ∑ x ∈ kindSet kind j', z x =
      if j' = j then tagTotal tag d j' else tagTotal tag v j' := by
    intro j'
    unfold kindSet tagTotal
    rw [sum_filter, Fintype.sum_sigma]
    split_ifs with hj'
    · subst hj'
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro i _
      simp only [hzdef, hkind, Option.some.injEq]
      split_ifs <;> simp_all
    · apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro i _
      simp only [hzdef, hkind, Option.some.injEq]
      split_ifs <;> simp_all
  simp_rw [htot] at hmult
  have hterm : tagTerm (tagTotal tag d) (tagTotal tag v) k j =
      ∑ m ∈ kindMonos kind k, ∏ x, z x ^ m x / ((m x)! : ℝ) := by
    rw [← hmult, Finset.prod_div_distrib]
    unfold tagTerm
    congr 1
  rw [hterm]
  calc ∑ σ ∈ cat, tagWeight tag d v p j σ
      ≤ ∑ σ ∈ cat, (∏ b, (1 + p b)) * ∏ x, z x ^ optMono σ x := sum_le_sum fun σ _ => hwt σ
    _ = (∏ b, (1 + p b)) * ∑ σ ∈ cat, ∏ x, z x ^ optMono σ x := by rw [mul_sum]
    _ ≤ (∏ b, (1 + p b)) * ∑ m ∈ kindMonos kind k, ∏ x, z x ^ m x / ((m x)! : ℝ) :=
        mul_le_mul_of_nonneg_left hmono (prod_nonneg fun b _ => by linarith [hp b])
    _ ≤ Real.exp (∑ b, p b) * ∑ m ∈ kindMonos kind k, ∏ x, z x ^ m x / ((m x)! : ℝ) := by
        apply mul_le_mul_of_nonneg_right (prod_one_add_le_exp p hp)
        exact sum_nonneg fun m _ => prod_nonneg fun x _ =>
          div_nonneg (pow_nonneg (hz x) _) (by positivity)

omit [DecidableEq J] [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [Fintype Tag] in
theorem countVec_eq_zero_iff (tag : ∀ b, I b → Tag) (σ : ∀ b, Option (I b)) :
    countVec tag σ = 0 ↔ σ = fun _ => none := by
  constructor
  · intro h
    funext b
    rcases hb : σ b with _ | i
    · rfl
    · exfalso
      have h1 := congrFun h (tag b i)
      unfold countVec at h1
      rw [Pi.zero_apply, card_eq_zero, filter_eq_empty_iff] at h1
      exact h1 (mem_univ b) (by rw [hb]; rfl)
  · rintro rfl
    funext j
    simp [countVec]

/-- **The summation of `lem:sharp-first`.** If every nonempty choice `σ` satisfies,
for every tag `j` present in it, `|term σ| ≤ K · wt_j(σ) + r_σ`, and `K ≥ 0`, then
`|∑_{σ ≠ ∅} term σ| ≤ K e^P 𝔗(d, v) + ∑_{σ ≠ ∅} r_σ`, with the tag totals `d_j`, `v_j`
and `P = ∑_B p_B`. -/
theorem abs_sum_le_tagSeries (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ} {p : J → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (hp : ∀ b, 0 ≤ p b) {K : ℝ}
    (hK : 0 ≤ K) (term r : (∀ b, Option (I b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec tag σ j →
      |term σ| ≤ K * tagWeight tag d v p j σ + r σ) :
    |∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none), term σ| ≤
      K * Real.exp (∑ b, p b) * tagSeries (tagTotal tag d) (tagTotal tag v) +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none), r σ := by
  set ne := univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none) with hne
  set Kset := ne.image (countVec tag) with hKset
  have hd' : ∀ j, 0 ≤ tagTotal tag d j :=
    fun j => sum_nonneg fun b _ => sum_nonneg fun i _ => by split_ifs <;> simp [hd b i]
  have hv' : ∀ j, 0 ≤ tagTotal tag v j :=
    fun j => sum_nonneg fun b _ => sum_nonneg fun i _ => by split_ifs <;> simp [hv b i]
  -- the bound for one category
  have hcat : ∀ k ∈ Kset,
      ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k), |term σ| ≤
        K * Real.exp (∑ b, p b) * tagMin (tagTotal tag d) (tagTotal tag v) k +
          ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k), r σ := by
    intro k hk
    obtain ⟨σ₀, hσ₀, hσk⟩ := mem_image.mp hk
    have hk0 : k ≠ 0 := by
      rw [← hσk]
      intro h
      exact (mem_filter.mp hσ₀).2 ((countVec_eq_zero_iff tag σ₀).mp h)
    have hnemp : (tagsOf k).Nonempty := by
      by_contra hemp
      apply hk0
      funext j
      by_contra hj
      simp only [Pi.zero_apply] at hj
      exact hemp ⟨j, by simp [tagsOf]; omega⟩
    obtain ⟨j, hj, hjmin⟩ := Finset.exists_mem_eq_inf' hnemp (tagTerm (tagTotal tag d) (tagTotal tag v) k)
    have hjk : 1 ≤ k j := by simpa [tagsOf] using hj
    have hmin : tagMin (tagTotal tag d) (tagTotal tag v) k =
        tagTerm (tagTotal tag d) (tagTotal tag v) k j := by
      unfold tagMin
      rw [dite_eq_left hnemp, hjmin]
    rw [hmin]
    have h1 : ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k), |term σ| ≤
        ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k), (K * tagWeight tag d v p j σ + r σ) := by
      apply sum_le_sum
      intro σ hσ
      rw [mem_filter] at hσ
      apply hterm σ (mem_filter.mp hσ.1).2 j
      rw [hσ.2]
      exact hjk
    have h2 : ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k), tagWeight tag d v p j σ ≤
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => countVec tag σ = k),
          tagWeight tag d v p j σ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro σ hσ
        rw [mem_filter] at hσ ⊢
        exact ⟨mem_univ _, hσ.2⟩
      · intro σ _ _
        apply prod_nonneg
        intro b _
        rcases σ b with _ | i
        · exact add_nonneg zero_le_one (hp b)
        · change 0 ≤ if tag b i = j then d b i else v b i
          split_ifs
          · exact hd b i
          · exact hv b i
    have h3 := sum_category_le tag hd hv hp k j
    rw [sum_add_distrib, ← mul_sum] at h1
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hK
    linarith
  -- sum over the categories
  have hfib : ∑ σ ∈ ne, |term σ| =
      ∑ k ∈ Kset, ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k), |term σ| :=
    (Finset.sum_fiberwise_of_maps_to (fun σ hσ => mem_image_of_mem _ hσ) _).symm
  have hfibr : ∑ σ ∈ ne, r σ =
      ∑ k ∈ Kset, ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k), r σ :=
    (Finset.sum_fiberwise_of_maps_to (fun σ hσ => mem_image_of_mem _ hσ) _).symm
  have hseries := sum_tagMin_le_tagSeries hd' hv' Kset
  have hEP : 0 ≤ K * Real.exp (∑ b, p b) := mul_nonneg hK (Real.exp_pos _).le
  calc |∑ σ ∈ ne, term σ| ≤ ∑ σ ∈ ne, |term σ| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Kset, ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k), |term σ| := hfib
    _ ≤ ∑ k ∈ Kset, (K * Real.exp (∑ b, p b) * tagMin (tagTotal tag d) (tagTotal tag v) k +
          ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k), r σ) := sum_le_sum hcat
    _ = K * Real.exp (∑ b, p b) * ∑ k ∈ Kset, tagMin (tagTotal tag d) (tagTotal tag v) k +
          ∑ σ ∈ ne, r σ := by
        rw [sum_add_distrib, ← mul_sum, hfibr]
    _ ≤ K * Real.exp (∑ b, p b) * tagSeries (tagTotal tag d) (tagTotal tag v) +
          ∑ σ ∈ ne, r σ := by
        have := mul_le_mul_of_nonneg_left hseries hEP
        linarith

end Summation

/-! ### Energy form and the first comparison -/

section Energy

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {I : J → Type*} [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
  {Tag : Type*} [Fintype Tag] [DecidableEq Tag]

/-- **`lem:sharp-first`, energy form.** Let `A_B` be the laws without differences and
`D_{B,i}` the tagged differences. If the energy of every nonempty choice satisfies,
for every tag `j` present, `|Y_σ| ≤ K · wt_j(σ) + r_σ`, then
`|Y_{⊗(A + ∑ D)} - Y_{⊗A}| ≤ K e^P 𝔗(d, v) + ∑_σ r_σ`. -/
theorem abs_energy_sub_le_sharpFirst (A : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (D : ∀ b, I b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ)
    (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ} {p : J → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (hp : ∀ b, 0 ≤ p b) {K : ℝ}
    (hK : 0 ≤ K) (r : (∀ b, Option (I b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec tag σ j →
      |diagonalIntegral (tensorLaw (fun b => (σ b).elim (A b) (D b))) F| ≤
        K * tagWeight tag d v p j σ + r σ) :
    |diagonalIntegral (tensorLaw (fun b => A b + ∑ i, D b i)) F -
        diagonalIntegral (tensorLaw A) F| ≤
      K * Real.exp (∑ b, p b) * tagSeries (tagTotal tag d) (tagTotal tag v) +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none), r σ := by
  rw [← diagonalIntegral_sub, tensorLaw_add_sum_sub_eq, diagonalIntegral_sum]
  exact abs_sum_le_tagSeries tag hd hv hp hK _ r hterm

/-- **`lem:record:first-stage`**, assembled from Step 1 and Step 2. Let `μ_B ⪰_ϑ 0`,
`ρ_B ⪰_ϑ μ_B` at every atom (Step 1, (CP2)(a)), and `λ_B = ρ_B + ∑_i δ_{B,i}` with tagged
differences whose terms satisfy the per-term bounds of `lem:sharp-first`
(Step 2, (CP2)(b)). Then `Y_λ ≥ Y_μ - K e^P 𝔗(d, v) - ∑_σ r_σ`. -/
theorem first_stage_lower_bound (ϑ : ReflectionCut V) (μ ρ : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (hμ : ∀ b, ϑ.Positive (μ b)) (hρ : ∀ b, ϑ.Below (μ b) (ρ b))
    (δ : ∀ b, I b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ)
    (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ} {p : J → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (hp : ∀ b, 0 ≤ p b) {K : ℝ}
    (hK : 0 ≤ K) (r : (∀ b, Option (I b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec tag σ j →
      |diagonalIntegral (tensorLaw (fun b => (σ b).elim (ρ b) (δ b))) F| ≤
        K * tagWeight tag d v p j σ + r σ) :
    diagonalIntegral (tensorLaw μ) F - K * Real.exp (∑ b, p b) *
        tagSeries (tagTotal tag d) (tagTotal tag v) -
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none), r σ ≤
    diagonalIntegral (tensorLaw (fun b => ρ b + ∑ i, δ b i)) F := by
  have h1 := energy_le_of_below ϑ μ ρ hμ hρ F
  have h2 := abs_energy_sub_le_sharpFirst ρ δ F tag hd hv hp hK r hterm
  have h3 := neg_abs_le (diagonalIntegral (tensorLaw (fun b => ρ b + ∑ i, δ b i)) F -
    diagonalIntegral (tensorLaw ρ) F)
  linarith

/-- **`lem:bracket-energy`, combination**: write `Ñ_{0,B} = μ_B + R_B` (`R_B` the positive
records of price `u_B`, zero off the first-stage atoms and on the selected block) and
`Ñ_B = Ñ_{0,B} + ∑_i δ_{B,i}`. If the energies of the subset expansion of `⊗ Ñ_0` satisfy
`|Y_{X'}| ≤ K ∏_{B ∈ X'} u_B` and those of the sharp-first expansion of `⊗ Ñ` around
`⊗ Ñ_0` satisfy the per-term bounds with `p = u`, then
`|Y_{⊗Ñ}| ≤ K e^{U_0} + K' e^{U_0} 𝔗(d, v) + ∑_σ r_σ`, `U_0 = ∑_B u_B`. -/
theorem abs_energy_le_bracket (μ R : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (δ : ∀ b, I b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ)
    (u : J → ℝ) (hu : ∀ b, 0 ≤ u b) {K K' : ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hterm0 : ∀ f : J → Bool,
      |diagonalIntegral (tensorLaw fun b => if f b then R b else μ b) F| ≤
        K * ∏ b, (if f b then u b else 1))
    (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (r : (∀ b, Option (I b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec tag σ j →
      |diagonalIntegral (tensorLaw (fun b => (σ b).elim (μ b + R b) (δ b))) F| ≤
        K' * tagWeight tag d v u j σ + r σ) :
    |diagonalIntegral (tensorLaw (fun b => (μ b + R b) + ∑ i, δ b i)) F| ≤
      K * Real.exp (∑ b, u b) +
        K' * Real.exp (∑ b, u b) * tagSeries (tagTotal tag d) (tagTotal tag v) +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none), r σ := by
  have h0 := abs_energy_add_le_exp μ R F u hu hK hterm0
  have h1 := abs_energy_sub_le_sharpFirst (fun b => μ b + R b) δ F tag hd hv hu hK' r hterm
  have h2 := abs_sub_abs_le_abs_sub
    (diagonalIntegral (tensorLaw (fun b => (μ b + R b) + ∑ i, δ b i)) F)
    (diagonalIntegral (tensorLaw (fun b => μ b + R b)) F)
  linarith

end Energy

end Sarkozy.RecordExpansion
