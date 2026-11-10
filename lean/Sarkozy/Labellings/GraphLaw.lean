module

public import Sarkozy.Labellings.Sequential
public import Sarkozy.ProbabilityConstructions

/-!
# Graph laws have bounded joint density (`def:graphs:labeling`, `lem:graphs:sequential`)

The graph law `λ_p(G)` is the uniform probability on `Inj_p(G)` (`graphLaw`). From the
sequential counts (`extCount_bounds`):

* `card_fibre_le`: for every set `S` of vertices and every labelling `x` of `S`, at most
  `upperProd(S, l)` elements of `Inj_p(G)` restrict to `x`, for any ordering `l` of `W \ S`;
  `lowerProd_le_card_inj`: `|Inj_p(G)| ≥ lowerProd(∅, l')`.
* `graphLaw_density` is the joint density bound used by the interpolation lemma (`hdens` of
  `Sarkozy.mixedLpBound_of_density_and_centeredL2`):
  `|E_λ ∏_{v∈S} g_v(z_v)| ≤ D_S ∏_{v∈S} E_unif |g_v|`, `D_S = q^{|S|} upperProd(S, l)/|Inj_p(G)|`.
* `tendsto_upperProd`, `tendsto_lowerProd`: as `q → ∞`, `upperProd(A, l)/q^{|l|}` and
  `lowerProd(A, l)/q^{|l|}` tend to `∏_i 2^{-t_i}` (`powProd`). `eventually_density_le`: the
  density constant `q^{|S|} upperProd(S, l) / lowerProd(∅, l')` is eventually at most its
  limit plus one, uniformly over the fields with `q` elements. This is the "bounded joint
  density relative to independent uniform labels" of the proof of `lem:density:global-moment`,
  conditional on Weil's bound.
-/

@[expose] public section

open scoped BigOperators
open Finset Filter Topology

namespace Sarkozy.Labellings

variable {W : Type*} [Fintype W] [DecidableEq W]

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The graph law `λ_p(G)`, the uniform probability on `Inj_p(G)` (assumed nonempty). -/
noncomputable def graphLaw (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) :
    FiniteLaw (W → F) where
  weight z := if z ∈ injLabellings F G then 1 / ((injLabellings F G).card : ℝ) else 0
  nonneg z := by split_ifs <;> positivity
  total := by
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    have : ((injLabellings F G).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
    field_simp

/-- The extension of a labelling of `S` by `0` (only its values on `S` matter). -/
noncomputable def extendLabel (S : Finset W) (x : S → F) : W → F :=
  fun v => if h : v ∈ S then x ⟨v, h⟩ else 0

/-- **Fibre counts.** At most `upperProd(S, l)` elements of `Inj_p(G)` restrict to a given
labelling of `S`, for any ordering `l` of `W \ S`. -/
theorem card_fibre_le (hW : WeilBound F) (G : OrientedGraph W) {n : ℕ}
    (hn : Fintype.card W ≤ n) (S : Finset W) (l : List W) (hnd : l.Nodup)
    (hcov : ∀ w, w ∈ S ∨ w ∈ l) (hdisj : ∀ w ∈ l, w ∉ S) (x : S → F) :
    (((injLabellings F G).filter fun y => (fun v : S => y v) = x).card : ℝ) ≤
      upperProd G (Fintype.card F) S l := by
  classical
  set x' := extendLabel S x
  have hfib : ((injLabellings F G).filter fun y => (fun v : S => y v) = x) =
      ((injLabellings F G).filter fun y => ∀ a ∈ S, y a = x' a) := by
    ext y
    simp only [mem_filter, x', extendLabel, funext_iff, Subtype.forall]
    constructor
    · rintro ⟨hy, h⟩; exact ⟨hy, fun a ha => by simp only [ha, ↓reduceDIte]; exact h a ha⟩
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun a ha => by have := h a ha; simpa only [ha, ↓reduceDIte] using this⟩
  rw [hfib]
  by_cases hfeas : Feasible F G S x'
  · have := (extCount_bounds hW G hn l S x' hnd hcov hdisj hfeas).2
    unfold extCount at this
    convert this
  · have hempty : ((injLabellings F G).filter fun y => ∀ a ∈ S, y a = x' a) = ∅ := by
      rw [filter_eq_empty_iff]
      intro y hy hagree
      apply hfeas
      simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
      refine ⟨fun a ha b hb hab => ?_, fun e he h1 h2 => ?_⟩
      · rw [← hagree a ha, ← hagree b hb] at hab
        exact hy.1 a (mem_univ _) b (mem_univ _) hab
      · rw [← hagree _ h1, ← hagree _ h2]
        exact hy.2 e he (mem_univ _) (mem_univ _)
    rw [hempty, card_empty, Nat.cast_zero]
    exact upperProd_nonneg G (Nat.cast_nonneg _) l S

/-- `|Inj_p(G)| ≥ lowerProd(∅, l)` for every ordering `l` of `W`. -/
theorem lowerProd_le_card_inj (hW : WeilBound F) (G : OrientedGraph W) {n : ℕ}
    (hn : Fintype.card W ≤ n) (l : List W) (hnd : l.Nodup) (hcov : ∀ w, w ∈ l) :
    lowerProd G (Fintype.card F) n ∅ l ≤ (injLabellings F G).card := by
  classical
  have hfeas : Feasible F G ∅ (fun _ => (0 : F)) := ⟨by simp, by simp⟩
  have h := (extCount_bounds hW G hn l ∅ (fun _ => (0 : F)) hnd (fun w => Or.inr (hcov w))
    (by simp) hfeas).1
  have he : extCount G ∅ (fun _ => (0 : F)) = (injLabellings F G).card := by
    unfold extCount
    congr 1
    exact filter_true_of_mem fun _ _ => by simp
  rwa [he] at h

/-- **Joint density of a graph law.** For every set `S` of vertices and every input family `g`,
`|E_λ ∏_{v∈S} g_v(z_v)| ≤ q^{|S|} upperProd(S, l)/|Inj_p(G)| · ∏_{v∈S} E_unif |g_v|`. -/
theorem graphLaw_density [Nonempty F] (hW : WeilBound F) (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card W ≤ n) (S : Finset W)
    (l : List W) (hnd : l.Nodup) (hcov : ∀ w, w ∈ S ∨ w ∈ l) (hdisj : ∀ w ∈ l, w ∉ S)
    (g : W → F → ℝ) :
    |(graphLaw G hne).expect (fun z => ∏ v ∈ S, g v (z v))| ≤
      (Fintype.card F : ℝ) ^ S.card * upperProd G (Fintype.card F) S l /
          (injLabellings F G).card *
        ∏ v ∈ S, (FiniteLaw.uniform F).expect (fun c => |g v c|) := by
  classical
  set I := injLabellings F G
  set U := upperProd G (Fintype.card F) S l
  have hIpos : (0 : ℝ) < I.card := by exact_mod_cast card_pos.mpr hne
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  -- the expectation of the absolute product as a sum over `Inj`
  have h1 : |(graphLaw G hne).expect (fun z => ∏ v ∈ S, g v (z v))| ≤
      (1 / (I.card : ℝ)) * ∑ y ∈ I, ∏ v ∈ S, |g v (y v)| := by
    refine ((graphLaw G hne).abs_expect_le _).trans (le_of_eq ?_)
    unfold FiniteLaw.expect graphLaw
    simp only [abs_prod, ite_mul, zero_mul]
    rw [sum_ite_mem, univ_inter, mul_sum]
  -- grouping by the restriction to `S`, and the fibre bound
  have h2 : ∑ y ∈ I, ∏ v ∈ S, |g v (y v)| ≤ U * ∑ x : S → F, ∏ v : S, |g v (x v)| := by
    rw [← sum_fiberwise_of_maps_to (g := fun y : W → F => fun v : S => y v) (t := univ)
      (fun _ _ => mem_univ _), mul_sum]
    refine sum_le_sum fun x _ => ?_
    have hconst : ∀ y ∈ I.filter (fun y => (fun v : S => y v) = x),
        ∏ v ∈ S, |g v (y v)| = ∏ v : S, |g v (x v)| := by
      intro y hy
      have hyx := (mem_filter.mp hy).2
      rw [← prod_coe_sort S]
      exact prod_congr rfl fun v _ => by rw [← hyx]
    rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_fibre_le hW G hn S l hnd hcov hdisj x)
      (prod_nonneg fun v _ => abs_nonneg _)
  -- the sum over labellings of `S` factorizes
  have h3 : ∑ x : S → F, ∏ v : S, |g v (x v)| =
      (Fintype.card F : ℝ) ^ S.card * ∏ v ∈ S, (FiniteLaw.uniform F).expect (fun c => |g v c|) := by
    rw [← Fintype.prod_sum (fun (v : S) (c : F) => |g v c|),
      prod_coe_sort S (fun v => ∑ c, |g v c|)]
    simp only [FiniteLaw.expect_uniform]
    rw [show (Fintype.card F : ℝ) ^ S.card = ∏ _v ∈ S, (Fintype.card F : ℝ) from
      (prod_const _).symm, ← prod_mul_distrib]
    refine prod_congr rfl fun v _ => ?_
    field_simp
  have hU : 0 ≤ U := upperProd_nonneg G (Nat.cast_nonneg _) l S
  calc |(graphLaw G hne).expect (fun z => ∏ v ∈ S, g v (z v))|
      ≤ (1 / (I.card : ℝ)) * (U * ∑ x : S → F, ∏ v : S, |g v (x v)|) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by rw [h3]; field_simp

end Field

/-! ## Limits as `q → ∞` -/

/-- The limit `∏_i 2^{-t_i}` of the products along an ordering. -/
noncomputable def powProd (G : OrientedGraph W) : Finset W → List W → ℝ
  | _, [] => 1
  | A, v :: l => (2 ^ nbrCount G A v)⁻¹ * powProd G (insert v A) l

omit [Fintype W] in
theorem powProd_pos (G : OrientedGraph W) : ∀ (l : List W) (A : Finset W), 0 < powProd G A l
  | [], _ => by simp [powProd]
  | v :: l, A => by simp only [powProd]; exact mul_pos (by positivity) (powProd_pos G l _)

theorem tendsto_softError_div (t : ℕ) :
    Tendsto (fun q : ℝ => softError q t / q) atTop (𝓝 0) := by
  have hs : Tendsto (fun q : ℝ => (Real.sqrt q)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hi : Tendsto (fun q : ℝ => q⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlim := (hs.const_mul (gradedA t)).add (hi.const_mul (gradedB t))
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
  unfold softError
  rw [add_div, mul_div_assoc, Real.sqrt_div_self', div_eq_mul_inv (gradedB t) q, one_div]

omit [Fintype W] in
/-- `upperProd(A, l)/q^{|l|} → ∏_i 2^{-t_i}` as `q → ∞`. -/
theorem tendsto_upperProd (G : OrientedGraph W) : ∀ (l : List W) (A : Finset W),
    Tendsto (fun q : ℝ => upperProd G q A l / q ^ l.length) atTop (𝓝 (powProd G A l))
  | [], A => by simp [upperProd, powProd]
  | v :: l, A => by
      have hrec := tendsto_upperProd G l (insert v A)
      have hstep : Tendsto (fun q : ℝ => stepUpper q (nbrCount G A v) / q) atTop
          (𝓝 (2 ^ nbrCount G A v)⁻¹) := by
        have h := ((tendsto_const_nhds (x := (1 : ℝ))).add
          (tendsto_softError_div (nbrCount G A v))).div_const (2 ^ nbrCount G A v)
        rw [add_zero, one_div] at h
        refine h.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
        unfold stepUpper
        field_simp
      have := hstep.mul hrec
      simp only [powProd]
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
      simp only [upperProd, List.length_cons, pow_succ]
      field_simp

omit [Fintype W] in
/-- `lowerProd(A, l)/q^{|l|} → ∏_i 2^{-t_i}` as `q → ∞`. -/
theorem tendsto_lowerProd (G : OrientedGraph W) (n : ℕ) : ∀ (l : List W) (A : Finset W),
    Tendsto (fun q : ℝ => lowerProd G q n A l / q ^ l.length) atTop (𝓝 (powProd G A l))
  | [], A => by simp [lowerProd, powProd]
  | v :: l, A => by
      have hrec := tendsto_lowerProd G n l (insert v A)
      set t := nbrCount G A v
      have hinner : Tendsto (fun q : ℝ => ((q - softError q t - 2 ^ t * n) / 2 ^ t) / q) atTop
          (𝓝 (2 ^ t)⁻¹) := by
        have hc : Tendsto (fun q : ℝ => (2 ^ t * (n : ℝ)) * q⁻¹) atTop (𝓝 0) := by
          simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2 ^ t * (n : ℝ))
        have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_softError_div t)).sub
          hc).div_const (2 ^ t)
        rw [sub_zero, sub_zero, one_div] at h
        refine h.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
        field_simp
      have hpos : ∀ᶠ q : ℝ in atTop, 0 ≤ (q - softError q t - 2 ^ t * n) / 2 ^ t := by
        have hev := hinner.eventually (lt_mem_nhds (by positivity : (0 : ℝ) < (2 ^ t)⁻¹))
        filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with q hq hq0
        have : 0 < ((q - softError q t - 2 ^ t * n) / 2 ^ t) / q := hq
        have h2 := (div_pos_iff_of_pos_right hq0).mp this
        exact h2.le
      have hstep : Tendsto (fun q : ℝ => stepLower q n t / q) atTop (𝓝 (2 ^ t)⁻¹) := by
        refine hinner.congr' ?_
        filter_upwards [hpos] with q hq
        unfold stepLower
        rw [max_eq_right hq]
      have := hstep.mul hrec
      simp only [powProd]
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
      simp only [lowerProd, List.length_cons, pow_succ]
      field_simp
      exact mul_comm _ _

omit [Fintype W] in
/-- **The density constant is eventually bounded.** For orderings `l` of `W \ S` and `l'` of
`W`, the constant `q^{|S|} upperProd(S, l) / lowerProd(∅, l')` is eventually positive-denominator
and at most `powProd(S, l)/powProd(∅, l') + 1`. -/
theorem eventually_density_le (G : OrientedGraph W) (n : ℕ) (S : Finset W) (l l' : List W)
    (hlen : S.card + l.length = l'.length) :
    ∀ᶠ q : ℝ in atTop, 0 < lowerProd G q n ∅ l' ∧
      q ^ S.card * upperProd G q S l / lowerProd G q n ∅ l' ≤
        powProd G S l / powProd G ∅ l' + 1 := by
  have hU := tendsto_upperProd G l S
  have hL := tendsto_lowerProd G n l' ∅
  have hL0 := powProd_pos G l' ∅
  have hratio := hU.div hL hL0.ne'
  have hev := hratio.eventually (gt_mem_nhds (lt_add_one (powProd G S l / powProd G ∅ l')))
  have hLpos := hL.eventually (lt_mem_nhds hL0)
  filter_upwards [hev, hLpos, eventually_gt_atTop (0 : ℝ)] with q hq hLq hq0
  have hlow : 0 < lowerProd G q n ∅ l' := by
    have := (div_pos_iff_of_pos_right (pow_pos hq0 l'.length)).mp hLq
    exact this
  refine ⟨hlow, le_of_lt ?_⟩
  have heq : q ^ S.card * upperProd G q S l / lowerProd G q n ∅ l' =
      (upperProd G q S l / q ^ l.length) / (lowerProd G q n ∅ l' / q ^ l'.length) := by
    rw [← hlen, pow_add]
    field_simp
  rw [heq]
  exact hq

/-- **Uniform joint density of graph laws** (the density input of `lem:density:global-moment`,
conditional on Weil's bound). For every oriented graph `G` there are `D` and `q₀` such that for
every finite field `F` with `q ≥ q₀` elements satisfying `WeilBound F`, the graph law exists
(`Inj_q(G) ≠ ∅`) and every marginal has density at most `D` with respect to independent uniform
labels: `|E_λ ∏_{v∈S} g_v(z_v)| ≤ D ∏_{v∈S} E_unif |g_v|` for all `S` and `g`. -/
theorem graphLaw_uniform_density (G : OrientedGraph W) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ q₀ : ℝ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
      WeilBound F → q₀ ≤ Fintype.card F →
        ∃ hne : (injLabellings F G).Nonempty, ∀ (S : Finset W) (g : W → F → ℝ),
          |(graphLaw G hne).expect (fun z => ∏ v ∈ S, g v (z v))| ≤
            D * ∏ v ∈ S, (FiniteLaw.uniform F).expect (fun c => |g v c|) := by
  classical
  set n := Fintype.card W
  set l' := (univ : Finset W).toList
  have hl'nd : l'.Nodup := nodup_toList _
  have hl'cov : ∀ w, w ∈ l' := fun w => mem_toList.mpr (mem_univ w)
  -- one bound for each of the finitely many sets `S`
  have hS : ∀ S : Finset W, ∀ᶠ q : ℝ in atTop, 0 < lowerProd G q n ∅ l' ∧
      q ^ S.card * upperProd G q S (univ \ S).toList / lowerProd G q n ∅ l' ≤
        powProd G S (univ \ S).toList / powProd G ∅ l' + 1 := fun S =>
    eventually_density_le G n S _ l' (by
      rw [length_toList, length_toList, card_univ_sdiff, card_univ]
      exact Nat.add_sub_cancel' (card_le_univ S))
  have hall : ∀ᶠ q : ℝ in atTop, ∀ S : Finset W, 0 < lowerProd G q n ∅ l' ∧
      q ^ S.card * upperProd G q S (univ \ S).toList / lowerProd G q n ∅ l' ≤
        powProd G S (univ \ S).toList / powProd G ∅ l' + 1 :=
    eventually_all.mpr hS
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.mp hall
  set D := ∑ S : Finset W, (powProd G S (univ \ S).toList / powProd G ∅ l' + 1)
  have hterm : ∀ S : Finset W, 0 ≤ powProd G S (univ \ S).toList / powProd G ∅ l' + 1 :=
    fun S => by
      have := div_pos (powProd_pos G (univ \ S).toList S) (powProd_pos G l' ∅)
      linarith
  have hD : ∀ S : Finset W, powProd G S (univ \ S).toList / powProd G ∅ l' + 1 ≤ D :=
    fun S => single_le_sum (fun S _ => hterm S) (mem_univ S)
  refine ⟨D, sum_nonneg fun S _ => hterm S, max q₀ 1, ?_⟩
  intro F _ _ _ hW hq
  have hqq := hq₀ (Fintype.card F) (le_of_max_le_left hq)
  have hlow := (hqq ∅).1
  have hinj := lowerProd_le_card_inj hW G (le_refl n) l' hl'nd hl'cov
  have hIpos : (0 : ℝ) < (injLabellings F G).card := lt_of_lt_of_le hlow hinj
  have hne : (injLabellings F G).Nonempty := card_pos.mp (by exact_mod_cast hIpos)
  have : Nonempty F := ⟨0⟩
  refine ⟨hne, fun S g => ?_⟩
  have hdisj : ∀ w ∈ (univ \ S).toList, w ∉ S := fun w hw =>
    (mem_sdiff.mp (mem_toList.mp hw)).2
  have hcov : ∀ w, w ∈ S ∨ w ∈ (univ \ S).toList := fun w => by
    by_cases h : w ∈ S
    · exact Or.inl h
    · exact Or.inr (mem_toList.mpr (mem_sdiff.mpr ⟨mem_univ w, h⟩))
  have hdens := graphLaw_density hW G hne (le_refl n) S (univ \ S).toList (nodup_toList _)
    hcov hdisj g
  have hE : 0 ≤ ∏ v ∈ S, (FiniteLaw.uniform F).expect (fun c => |g v c|) :=
    prod_nonneg fun v _ => (FiniteLaw.uniform F).expect_nonneg fun c => abs_nonneg _
  have hU := upperProd_nonneg G (Nat.cast_nonneg (Fintype.card F)) (univ \ S).toList S
  have hconst : (Fintype.card F : ℝ) ^ S.card * upperProd G (Fintype.card F) S (univ \ S).toList /
      (injLabellings F G).card ≤ D := by
    calc (Fintype.card F : ℝ) ^ S.card * upperProd G (Fintype.card F) S (univ \ S).toList /
          (injLabellings F G).card
        ≤ (Fintype.card F : ℝ) ^ S.card * upperProd G (Fintype.card F) S (univ \ S).toList /
          lowerProd G (Fintype.card F) n ∅ l' :=
          div_le_div_of_nonneg_left (by positivity) hlow hinj
      _ ≤ _ := (hqq S).2
      _ ≤ D := hD S
  exact hdens.trans (mul_le_mul_of_nonneg_right hconst hE)

end Sarkozy.Labellings
