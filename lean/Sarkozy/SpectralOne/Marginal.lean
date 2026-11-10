module

public import Sarkozy.SpectralD.CouplingInputs
public import Sarkozy.SpectralC.PaleyOne
public import Sarkozy.Labellings.Sequential

@[expose] public section

/-!
# The law of `x_J` and the isolated-vertex average (`lem:spec2:paley-one`, realization)

`paper/sections/14_spectral.tex`, `subsec:advance:parity`, proof of `lem:spec2:paley-one`:
"Let `j ∈ J` be isolated in `G⁺[J]`, and let `u_cons` be the uniform law on `Inj_p(G⁺[J])`. …
the law `ν_J` of `x_J` under `ν` is `w u_cons/E_{u_cons} w` with `max w/min w ≤ R` … Since
`w/E w ∈ [1/R, R]` and `|S_J| ≤ r`, `|t_J − E_{u_cons} S_J| ≤ (R − 1) r`. Under `u_cons`, given
`x_{J∖{j}}` the label `x_j` is uniform on the `p − |J| + 1` values not used, because `j` has no
edge in `G⁺[J]` … so `|E_{u_cons} S_J| ≤ |J|/(p − |J| + 1)`."

WP-K's `SpectralC.PaleyOne` proves the two estimates in abstract form (`density_transfer`,
`isolated_vertex_avg`). This file realizes them for the actual `t_J = E_ν S_J` of
`SpectralD.PaleyB.tJ`, for any weight `ν` on the labellings `U → 𝔽_p` and any oriented graph `G`:

* the labellings of `J` are the labellings vanishing off `J` (`cfgs J`), `x ↦ x|_J` is `restr J`,
  the law of `x_J` under `ν` is `margJ ν J`, and `t_J = ∑_y margJ ν J y · S_J(y)`
  (`tJ_eq_marg`);
* `u_cons` is `refLaw G J`, the uniform law on `Inj_p(G[J])` (`feasCfgs G J`);
* for `J = {j} ∪ J'` with `j` isolated in `G[J]` (`feasible_insert_iff`), the labellings of `J`
  are the pairs `(x_{J'}, x_j)` (`sum_cfgs_insert`), `|Inj_p(G[J])| = |Inj_p(G[J'])|(p − |J'|)`
  (`card_feasCfgs_insert`) and `|∑_{Inj_p(G[J])} S_J| ≤ |Inj_p(G[J'])|(|J'| + 1)`
  (`norm_sum_feasCfgs_SJ_le`, from `isolated_vertex_avg`);
* **`norm_tJ_le_isolated`**: if the law of `x_J` under `ν` has density in `[1/R, R]` with respect
  to `u_cons`, then `|t_J| ≤ (R − 1) r + (|J'| + 1)/(p − |J'|)`.

No property of the prime class is used here; at `p ≡ 3 (mod 4)` all `t_J` vanish anyway
(`PaleyB.tJ_eq_zero_of_three`).

New material for this paper.
-/

namespace Sarkozy.SpectralOne

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC Sarkozy.Labellings
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-! ## Labellings of a subset -/

/-- Feasibility is decidable (finite quantifiers). A local instance of this file only. -/
@[instance_reducible] def feasibleDec (G : OrientedGraph U) (A : Finset U) :
    DecidablePred (Feasible (ZMod p) G A) := fun x => by
  unfold Feasible; infer_instance

attribute [local instance] feasibleDec

/-- The labellings of `J`, as the labellings of `U` vanishing off `J`. -/
noncomputable def cfgs (J : Finset U) : Finset (U → ZMod p) :=
  univ.filter (fun y => ∀ k, k ∉ J → y k = 0)

/-- `x|_J`, extended by `0`. -/
def restr (J : Finset U) (x : U → ZMod p) : U → ZMod p := fun k => if k ∈ J then x k else 0

lemma mem_cfgs {J : Finset U} {y : U → ZMod p} : y ∈ cfgs J ↔ ∀ k, k ∉ J → y k = 0 := by
  simp [cfgs]

lemma restr_mem_cfgs (J : Finset U) (x : U → ZMod p) : restr J x ∈ cfgs J :=
  mem_cfgs.mpr fun k hk => by simp [restr, hk]

omit [Fintype U] in
lemma restr_apply_of_mem {J : Finset U} {k : U} (hk : k ∈ J) (x : U → ZMod p) :
    restr J x k = x k := by
  simp [restr, hk]

lemma restr_eq_iff {J : Finset U} {x y : U → ZMod p} (hy : y ∈ cfgs J) :
    restr J x = y ↔ ∀ k ∈ J, x k = y k := by
  constructor
  · rintro rfl k hk
    rw [restr_apply_of_mem hk]
  · intro h
    funext k
    by_cases hk : k ∈ J
    · rw [restr_apply_of_mem hk, h k hk]
    · simp only [restr, hk, ↓reduceIte]
      exact (mem_cfgs.mp hy k hk).symm

omit [Fintype U] in
lemma gJ_restr (J : Finset U) (x : U → ZMod p) : gJ J (restr J x) = gJ J x := by
  funext a
  unfold gJ
  exact prod_congr rfl fun k hk => by rw [restr_apply_of_mem hk]

omit [Fintype U] in
lemma SJ_restr (J : Finset U) (x : U → ZMod p) : SJ J (restr J x) = SJ J x := by
  unfold SJ
  rw [gJ_restr]

/-- The law of `x_J` under `ν`: `margJ ν J y = ν{x : x|_J = y}`. -/
noncomputable def margJ (ν : (U → ZMod p) → ℝ) (J : Finset U) (y : U → ZMod p) : ℝ :=
  ∑ x ∈ univ.filter (fun x => restr J x = y), ν x

/-- `t_J = E_ν S_J = ∑_y ν_J(y) S_J(y)`: `S_J` depends only on `x_J`. -/
theorem tJ_eq_marg (ν : (U → ZMod p) → ℝ) (J : Finset U) :
    SpectralD.PaleyB.tJ ν J = ∑ y, (margJ ν J y : ℂ) * SJ J y := by
  unfold SpectralD.PaleyB.tJ margJ
  have h1 : ∑ x, (ν x : ℂ) * SJ J x = ∑ x, (ν x : ℂ) * SJ J (restr J x) :=
    sum_congr rfl fun x _ => by rw [SJ_restr]
  rw [h1, ← sum_fiberwise_of_maps_to (g := restr J) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun y _ => ?_
  push_cast
  rw [sum_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [(mem_filter.mp hx).2]

/-! ## Feasibility with an isolated vertex -/

omit [Fintype U] [DecidableEq U] in
lemma feasible_congr {G : OrientedGraph U} {A : Finset U} {x y : U → ZMod p}
    (h : ∀ k ∈ A, x k = y k) : Feasible (ZMod p) G A x ↔ Feasible (ZMod p) G A y := by
  unfold Feasible
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha b hb hab => h1 a ha b hb (by rw [h a ha, h b hb]; exact hab),
      fun e he he1 he2 => ?_⟩
    rw [← h e.1 he1, ← h e.2 he2]
    exact h2 e he he1 he2
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha b hb hab => h1 a ha b hb (by rw [← h a ha, ← h b hb]; exact hab),
      fun e he he1 he2 => ?_⟩
    rw [h e.1 he1, h e.2 he2]
    exact h2 e he he1 he2

omit [Fintype U] in
/-- **`j` isolated in `G[{j} ∪ J]`**: a labelling is feasible on `{j} ∪ J` iff it is feasible on
`J` and `x_j` is not one of the labels of `J`. -/
lemma feasible_insert_iff {G : OrientedGraph U} {J : Finset U} {j : U} (hj : j ∉ J)
    (hiso : ∀ i ∈ J, (i, j) ∉ G.E ∧ (j, i) ∉ G.E) (x : U → ZMod p) :
    Feasible (ZMod p) G (insert j J) x ↔ Feasible (ZMod p) G J x ∧ x j ∉ J.image x := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun a ha b hb hab => h1 a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab,
      fun e he he1 he2 => h2 e he (mem_insert_of_mem he1) (mem_insert_of_mem he2)⟩, ?_⟩
    intro hmem
    obtain ⟨k, hk, hkx⟩ := mem_image.mp hmem
    have := h1 k (mem_insert_of_mem hk) j (mem_insert_self j J) hkx
    exact hj (this ▸ hk)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun a ha b hb hab => ?_, fun e he he1 he2 => ?_⟩
    · rcases mem_insert.mp ha with rfl | ha'
      · rcases mem_insert.mp hb with rfl | hb'
        · rfl
        · exact absurd (mem_image.mpr ⟨b, hb', hab.symm⟩) h3
      · rcases mem_insert.mp hb with rfl | hb'
        · exact absurd (mem_image.mpr ⟨a, ha', hab⟩) h3
        · exact h1 a ha' b hb' hab
    · rcases mem_insert.mp he1 with h | he1'
      · rcases mem_insert.mp he2 with h' | he2'
        · have hej : e = (j, j) := Prod.ext h h'
          rw [hej] at he
          exact absurd he (G.loopless j)
        · exact absurd (show (j, e.2) ∈ G.E by rw [← h]; exact he) (hiso e.2 he2').2
      · rcases mem_insert.mp he2 with h' | he2'
        · exact absurd (show (e.1, j) ∈ G.E by rw [← h']; exact he) (hiso e.1 he1').1
        · exact h2 e he he1' he2'

/-! ## Labellings of `{j} ∪ J` as pairs -/

/-- The labellings of `{j} ∪ J` are the pairs `(x_J, x_j)`. -/
lemma sum_cfgs_insert {M : Type*} [AddCommMonoid M] {J : Finset U} {j : U} (hj : j ∉ J)
    (ψ : (U → ZMod p) → M) :
    ∑ y ∈ cfgs (insert j J), ψ y = ∑ y ∈ cfgs J, ∑ t, ψ (Function.update y j t) := by
  rw [← sum_product' (s := cfgs J) (t := (univ : Finset (ZMod p)))
    (f := fun y t => ψ (Function.update y j t))]
  refine sum_nbij' (fun y => (Function.update y j 0, y j))
    (fun z => Function.update z.1 j z.2) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [mem_product]
    refine ⟨mem_cfgs.mpr fun k hk => ?_, mem_univ _⟩
    show Function.update y j 0 k = 0
    by_cases hkj : k = j
    · subst hkj; exact Function.update_self ..
    · rw [Function.update_of_ne hkj]
      exact mem_cfgs.mp hy k (by simp [hkj, hk])
  · intro z hz
    rw [mem_product] at hz
    refine mem_cfgs.mpr fun k hk => ?_
    have hkj : k ≠ j := fun h => hk (h ▸ mem_insert_self j J)
    rw [Function.update_of_ne hkj]
    exact mem_cfgs.mp hz.1 k fun h => hk (mem_insert_of_mem h)
  · intro y _
    simp
  · intro z hz
    rw [mem_product] at hz
    have hz0 : z.1 j = 0 := mem_cfgs.mp hz.1 j hj
    ext k
    · simp only [Function.update_idem]
      by_cases hkj : k = j
      · subst hkj; rw [Function.update_self, hz0]
      · rw [Function.update_of_ne hkj]
    · simp
  · intro y _
    simp

/-- `Inj_p(G[J])`: the labellings of `J` that are feasible on `J`. -/
noncomputable def feasCfgs (G : OrientedGraph U) (J : Finset U) : Finset (U → ZMod p) :=
  (cfgs J).filter (Feasible (ZMod p) G J)

/-- `u_cons`: the uniform law on `Inj_p(G[J])`. -/
noncomputable def refLaw (G : OrientedGraph U) (J : Finset U) (y : U → ZMod p) : ℝ :=
  if y ∈ feasCfgs (p := p) G J then ((feasCfgs (p := p) G J).card : ℝ)⁻¹ else 0

lemma refLaw_nonneg (G : OrientedGraph U) (J : Finset U) (y : U → ZMod p) :
    0 ≤ refLaw G J y := by
  unfold refLaw; split_ifs <;> positivity

lemma sum_refLaw (G : OrientedGraph U) (J : Finset U)
    (hF : (feasCfgs (p := p) G J).Nonempty) : ∑ y, refLaw (p := p) G J y = 1 := by
  unfold refLaw
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  have : ((feasCfgs (p := p) G J).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hF).ne'
  field_simp

omit [Fintype U] in
/-- The fibre of a feasible labelling of `J` over the new label `x_j`. -/
lemma feasible_update_iff {G : OrientedGraph U} {J : Finset U} {j : U} (hj : j ∉ J)
    (hiso : ∀ i ∈ J, (i, j) ∉ G.E ∧ (j, i) ∉ G.E) (y : U → ZMod p) (t : ZMod p) :
    Feasible (ZMod p) G (insert j J) (Function.update y j t) ↔
      Feasible (ZMod p) G J y ∧ t ∉ J.image y := by
  have hag : ∀ k ∈ J, Function.update y j t k = y k := fun k hk =>
    Function.update_of_ne (by rintro rfl; exact hj hk) _ _
  have himg : J.image (Function.update y j t) = J.image y := image_congr fun k hk => hag k hk
  rw [feasible_insert_iff hj hiso, feasible_congr hag, himg, Function.update_self]

omit [Fintype U] [DecidableEq U] in
lemma card_image_of_feasible {G : OrientedGraph U} {J : Finset U} {y : U → ZMod p}
    (hy : Feasible (ZMod p) G J y) : (J.image y).card = J.card :=
  card_image_of_injOn fun a ha b hb h => hy.1 a ha b hb h

/-- **The isolated vertex is uniform**: `|Inj_p(G[{j} ∪ J])| = |Inj_p(G[J])| (p − |J|)`. -/
theorem card_feasCfgs_insert {G : OrientedGraph U} {J : Finset U} {j : U} (hj : j ∉ J)
    (hiso : ∀ i ∈ J, (i, j) ∉ G.E ∧ (j, i) ∉ G.E) :
    (feasCfgs (p := p) G (insert j J)).card = (feasCfgs (p := p) G J).card * (p - J.card) := by
  have h1 : (feasCfgs (p := p) G (insert j J)).card =
      ∑ y ∈ cfgs (p := p) (insert j J), if Feasible (ZMod p) G (insert j J) y then 1 else 0 := by
    rw [feasCfgs, card_eq_sum_ones, sum_filter]
  rw [h1, sum_cfgs_insert hj]
  have h2 : ∀ y ∈ cfgs (p := p) J, (∑ t : ZMod p,
      if Feasible (ZMod p) G (insert j J) (Function.update y j t) then 1 else 0) =
      if Feasible (ZMod p) G J y then p - J.card else 0 := by
    intro y _
    simp_rw [feasible_update_iff hj hiso]
    by_cases hy : Feasible (ZMod p) G J y
    · simp only [hy, true_and, ↓reduceIte]
      rw [← card_filter, show univ.filter (fun t => t ∉ J.image y) = univ \ J.image y by
        ext t; simp, card_univ_sdiff, ZMod.card, card_image_of_feasible hy]
    · simp [hy]
  rw [sum_congr rfl h2, ← sum_filter, sum_const, smul_eq_mul]
  rfl

/-- **The isolated-vertex sum** (`isolated_vertex_avg`): if `j` is isolated in `G[{j} ∪ J]`,
`|∑_{Inj_p(G[{j} ∪ J])} S_{{j} ∪ J}| ≤ |Inj_p(G[J])| (|J| + 1)`. -/
theorem norm_sum_feasCfgs_SJ_le (hp2 : p ≠ 2) {G : OrientedGraph U} {J : Finset U} {j : U}
    (hj : j ∉ J) (hiso : ∀ i ∈ J, (i, j) ∉ G.E ∧ (j, i) ∉ G.E) :
    ‖∑ y ∈ feasCfgs (p := p) G (insert j J), SJ (insert j J) y‖ ≤
      ((feasCfgs (p := p) G J).card : ℝ) * ((J.card : ℝ) + 1) := by
  have h1 : ∑ y ∈ feasCfgs (p := p) G (insert j J), SJ (insert j J) y =
      ∑ y ∈ cfgs (p := p) J, ∑ t, (if Feasible (ZMod p) G (insert j J) (Function.update y j t)
        then SJ (insert j J) (Function.update y j t) else 0) := by
    rw [feasCfgs, sum_filter, sum_cfgs_insert hj]
  have hJe : (insert j J).erase j = J := erase_insert hj
  have h2 : ∀ y ∈ cfgs (p := p) J, (∑ t, (if Feasible (ZMod p) G (insert j J)
      (Function.update y j t) then SJ (insert j J) (Function.update y j t) else 0)) =
      if Feasible (ZMod p) G J y then ∑ t ∈ univ \ J.image y, isoS (gJ J y) t else 0 := by
    intro y _
    simp_rw [feasible_update_iff hj hiso]
    by_cases hy : Feasible (ZMod p) G J y
    · simp only [hy, true_and, ↓reduceIte]
      rw [← sum_filter, show univ.filter (fun t => t ∉ J.image y) = univ \ J.image y by
        ext t; simp]
      refine sum_congr rfl fun t _ => ?_
      unfold SJ isoS
      rw [SpectralD.PaleyB.gJ_update_of_mem (mem_insert_self j J), hJe]
    · simp [hy]
  rw [h1, sum_congr rfl h2, ← sum_filter]
  have h3 : ∀ y ∈ (cfgs (p := p) J).filter (Feasible (ZMod p) G J),
      ‖∑ t ∈ univ \ J.image y, isoS (gJ J y) t‖ ≤ (J.card : ℝ) + 1 := by
    intro y hy
    have hyF := (mem_filter.mp hy).2
    have h := isolated_vertex_avg hp2 (gJ J y) (fun a => norm_gJ_le J y a) (J.image y)
    simp_rw [← isoS_eq] at h
    rwa [card_image_of_feasible hyF] at h
  refine (norm_sum_le _ _).trans ((sum_le_sum h3).trans (le_of_eq ?_))
  rw [sum_const, nsmul_eq_mul]
  rfl

/-! ## The isolated-vertex bound for `t_J` -/

/-- **`lem:spec2:paley-one`, realized for `t_J`.** Let `j ∉ J` be isolated in `G[{j} ∪ J]`, and
let the law `ν_{J⁺}` of `x_{J⁺}` under `ν` (`J⁺ = {j} ∪ J`) satisfy
`R⁻¹ u_cons ≤ ν_{J⁺} ≤ R u_cons`, `u_cons` the uniform law on `Inj_p(G[J⁺])` (assumed
nonempty). Then `|t_{J⁺}| ≤ (R − 1) r + (|J| + 1)/(p − |J|)`. -/
theorem norm_tJ_le_isolated (hp2 : p ≠ 2) (G : OrientedGraph U) (ν : (U → ZMod p) → ℝ)
    {J : Finset U} {j : U} (hj : j ∉ J) (hiso : ∀ i ∈ J, (i, j) ∉ G.E ∧ (j, i) ∉ G.E)
    (hF : (feasCfgs (p := p) G (insert j J)).Nonempty) {R : ℝ} (hR : 1 ≤ R)
    (hdens : ∀ y, R⁻¹ * refLaw G (insert j J) y ≤ margJ ν (insert j J) y ∧
      margJ ν (insert j J) y ≤ R * refLaw G (insert j J) y) :
    ‖SpectralD.PaleyB.tJ ν (insert j J)‖ ≤
      (R - 1) * rp p + ((J.card : ℝ) + 1) / ((p : ℝ) - J.card) := by
  have hcard := card_feasCfgs_insert (p := p) hj hiso
  have hpos : 0 < (feasCfgs (p := p) G (insert j J)).card := card_pos.mpr hF
  have hJp : J.card < p := by
    rw [hcard] at hpos
    have := Nat.pos_of_mul_pos_left hpos
    omega
  have hF' : 0 < (feasCfgs (p := p) G J).card := by
    rw [hcard] at hpos
    exact Nat.pos_of_mul_pos_right hpos
  have hpm : (0 : ℝ) < (p : ℝ) - J.card := by
    have : (J.card : ℝ) < p := by exact_mod_cast hJp
    linarith
  -- the comparison with `u_cons`
  have htr := density_transfer (refLaw G (insert j J)) (margJ ν (insert j J))
    (SJ (insert j J)) hR (refLaw_nonneg G _) (sum_refLaw G _ hF) hdens
    (fun y => norm_SJ_le hp2 _ y)
  rw [← tJ_eq_marg] at htr
  -- the uniform completion
  have hu : ‖∑ y, (refLaw (p := p) G (insert j J) y : ℂ) * SJ (insert j J) y‖ ≤
      ((J.card : ℝ) + 1) / ((p : ℝ) - J.card) := by
    have h1 : ∑ y, (refLaw (p := p) G (insert j J) y : ℂ) * SJ (insert j J) y =
        (((feasCfgs (p := p) G (insert j J)).card : ℝ)⁻¹ : ℂ) *
          ∑ y ∈ feasCfgs (p := p) G (insert j J), SJ (insert j J) y := by
      have hpt : ∀ y, (refLaw (p := p) G (insert j J) y : ℂ) * SJ (insert j J) y =
          if y ∈ feasCfgs (p := p) G (insert j J) then
            (((feasCfgs (p := p) G (insert j J)).card : ℝ)⁻¹ : ℂ) * SJ (insert j J) y
          else 0 := by
        intro y
        unfold refLaw
        split_ifs <;> simp
      simp_rw [hpt]
      rw [sum_ite_mem, univ_inter, mul_sum]
    rw [h1]
    simp only [norm_mul, norm_inv, Complex.ofReal_natCast, Complex.norm_natCast]
    have h2 := norm_sum_feasCfgs_SJ_le (p := p) hp2 hj hiso (G := G)
    have hc : ((feasCfgs (p := p) G (insert j J)).card : ℝ) =
        ((feasCfgs (p := p) G J).card : ℝ) * ((p : ℝ) - J.card) := by
      rw [hcard]; push_cast [Nat.cast_sub hJp.le]; ring
    rw [hc]
    have hF'r : (0 : ℝ) < (feasCfgs (p := p) G J).card := by exact_mod_cast hF'
    calc (((feasCfgs (p := p) G J).card : ℝ) * ((p : ℝ) - J.card))⁻¹ *
          ‖∑ y ∈ feasCfgs (p := p) G (insert j J), SJ (insert j J) y‖
        ≤ (((feasCfgs (p := p) G J).card : ℝ) * ((p : ℝ) - J.card))⁻¹ *
          (((feasCfgs (p := p) G J).card : ℝ) * ((J.card : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((J.card : ℝ) + 1) / ((p : ℝ) - J.card) := by
          field_simp
  calc ‖SpectralD.PaleyB.tJ ν (insert j J)‖
      ≤ ‖SpectralD.PaleyB.tJ ν (insert j J) -
          ∑ y, (refLaw (p := p) G (insert j J) y : ℂ) * SJ (insert j J) y‖ +
        ‖∑ y, (refLaw (p := p) G (insert j J) y : ℂ) * SJ (insert j J) y‖ := by
        have := norm_add_le (SpectralD.PaleyB.tJ ν (insert j J) -
          ∑ y, (refLaw (p := p) G (insert j J) y : ℂ) * SJ (insert j J) y)
          (∑ y, (refLaw (p := p) G (insert j J) y : ℂ) * SJ (insert j J) y)
        rwa [sub_add_cancel] at this
    _ ≤ (R - 1) * rp p + ((J.card : ℝ) + 1) / ((p : ℝ) - J.card) := add_le_add htr hu

end Sarkozy.SpectralOne
