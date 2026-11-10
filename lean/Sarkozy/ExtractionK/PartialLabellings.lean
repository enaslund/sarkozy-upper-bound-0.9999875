module

public import Sarkozy.ExtractionK.Defs

@[expose] public section

/-!
# Sums over the labellings of a vertex set (Steps 2–5 of `lem:extraction-rows`)

`paper/sections/16_extraction.tex`, `lem:extraction-rows` and Step 7 of the proof of
`lem:matching:extractionk`: there the cover rows are applied after
`eq:extraction:cross-density` has replaced the cover marginal by the uniform law on
`Inj_p(G⁺[C_z])`, and "only Steps 2–5 of that row lemma are then needed; its separate marginal
comparison is omitted". This file states those steps as a bound for a sum over the labellings of
`C` alone, with no completion to the other vertices.

A labelling of `S ⊆ U⁺` is an element of `partLab F G S` (`Defs.lean`): a function `U → F` that is
zero outside `S`, injective on `S` and satisfies the strict-square conditions of the edges inside
`S`, i.e. an element of `Inj_p(G⁺[S])` extended by `0`.

* `restr_mem_partLab`, `restr_mem_injTuples`: the restriction of an element of `Inj_p(G⁺)` to `S`
  is a labelling of `S`, and an injective tuple on `S`.
* `sum_partLab_insert`: labelling one more vertex `v ∉ S`,
  `∑_{c ∈ Inj(G[S ∪ v])} g(c) = ∑_{c ∈ Inj(G[S])} ∑_{z ∈ Φ_v(c)} g(c[v ↦ z])`.
* `partLab_seq_upper`: the sequential upper bound (Step 5 of `lem:extraction-rows`): if the
  weights `φ_b` (`b ∈ S`) read only the labels of `b` and of the vertices of `S` earlier than `b`,
  and the one-step sums are at most `M_b`, then `∑_{c ∈ Inj(G[S])} ∏_{b ∈ S} φ_b(c) ≤ ∏_b M_b`.
* `partLab_coverRows_le`: Steps 2–5 of `lem:extraction-rows` in this form: for an ordered `C`,
  an injective `x` and `H ⊆ {(a, b) ∈ E_× : b ∈ C}`,
  `∑_{c' ∈ Inj(G[C])} Π(c') ≤ ∏_{b ∈ C} q 2^{-t_b} (1 + e_{s_b}(q, 2n) + r² 2^{s_b}
  ∑_{j ∈ U⁺} 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]})`, `Π` the integrand of the lemma
  (`coverRowIntegrand`). Dividing by the lower count `|Inj(G[C])| ≥ ∏_b q 2^{-t_b}(1 - e_{t_b})`
  of Step 2 gives `E_{λ_C} Π ≤ ∏_b F_b(H)`; the formal proof of `lem:matching:extractionk` keeps
  the sum and divides only once, by `|Inj_p(G⁺)|`.
* `card_injLabellings_ge`: the lower count of `lem:graphs:sequential`(a) along an order of all of
  `U⁺`: `|Inj_p(G⁺)| ≥ ∏_v q 2^{-t_v}(1 - e_{t_v}(q, n))`, `t_v` the number of earlier
  neighbours, when every `e_{t_v}(q, n) ≤ 1` (so that every factor is nonnegative).

The only literature input is `WeilBound F` (Weil's theorem, `thm:weil`(a)), through
`coverRows_oneVertex` (`eq:extraction:onevertex`) and `card_vertexAdmissible` (`lem:extension`).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-! ## Labellings of a vertex set -/

theorem mem_partLab {G : OrientedGraph U} {S : Finset U} {c : U → F} :
    c ∈ partLab F G S ↔ (∀ u, u ∉ S → c u = 0) ∧ Feasible F G S c := by
  unfold partLab
  simp only [mem_filter, mem_univ, true_and]

theorem mem_injTuples {V : Finset U} {v : U → F} :
    v ∈ injTuples F V ↔ (∀ u, u ∉ V → v u = 0) ∧ ∀ a ∈ V, ∀ b ∈ V, v a = v b → a = b := by
  unfold injTuples
  simp only [mem_filter, mem_univ, true_and]

/-- The restriction of `y ∈ Inj_p(G⁺)` to `S` is a labelling of `S`. -/
theorem restr_mem_partLab (G : OrientedGraph U) (S : Finset U) {y : U → F}
    (hy : y ∈ injLabellings F G) : restr S y ∈ partLab F G S := by
  simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
  rw [mem_partLab]
  refine ⟨fun u hu => by simp [restr, hu], fun a ha b hb hab => ?_, fun e he h1 h2 => ?_⟩
  · simp only [restr, ha, hb, ↓reduceIte] at hab
    exact hy.1 a (mem_univ _) b (mem_univ _) hab
  · simp only [restr, h1, h2, ↓reduceIte]
    exact hy.2 e he (mem_univ _) (mem_univ _)

/-- The restriction of `y ∈ Inj_p(G⁺)` to `V` is an injective tuple on `V`. -/
theorem restr_mem_injTuples (G : OrientedGraph U) (V : Finset U) {y : U → F}
    (hy : y ∈ injLabellings F G) : restr V y ∈ injTuples F V := by
  simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
  rw [mem_injTuples]
  refine ⟨fun u hu => by simp [restr, hu], fun a ha b hb hab => ?_⟩
  simp only [restr, ha, hb, ↓reduceIte] at hab
  exact hy.1 a (mem_univ _) b (mem_univ _) hab

/-- **Labelling one more vertex**: for `v ∉ S`,
`∑_{c ∈ Inj(G[S ∪ {v}])} g(c) = ∑_{c ∈ Inj(G[S])} ∑_{z ∈ Φ_v(c)} g(c[v ↦ z])`, `Φ_v(c)` the
admissible labels of `v` given the labels `c` of `S` (`vertexAdmissible`). -/
theorem sum_partLab_insert (G : OrientedGraph U) {S : Finset U} {v : U} (hv : v ∉ S)
    (g : (U → F) → ℝ) :
    ∑ c ∈ partLab F G (insert v S), g c =
      ∑ c ∈ partLab F G S, ∑ z ∈ vertexAdmissible G S c v, g (Function.update c v z) := by
  have hmaps : ∀ c ∈ partLab F G (insert v S), Function.update c v 0 ∈ partLab F G S := by
    intro c hc
    rw [mem_partLab] at hc ⊢
    obtain ⟨hz, hf⟩ := hc
    refine ⟨fun u hu => ?_, ⟨fun a ha b hb hab => ?_, fun e he h1 h2 => ?_⟩⟩
    · by_cases huv : u = v
      · subst huv
        simp
      · rw [Function.update_of_ne huv]
        exact hz u (by simp [huv, hu])
    · have hav : a ≠ v := fun h => hv (h ▸ ha)
      have hbv : b ≠ v := fun h => hv (h ▸ hb)
      rw [Function.update_of_ne hav, Function.update_of_ne hbv] at hab
      exact hf.1 a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
    · have h1v : e.1 ≠ v := fun h => hv (h ▸ h1)
      have h2v : e.2 ≠ v := fun h => hv (h ▸ h2)
      rw [Function.update_of_ne h1v, Function.update_of_ne h2v]
      exact hf.2 e he (mem_insert_of_mem h1) (mem_insert_of_mem h2)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun c hc => ?_
  have hcv : c v = 0 := (mem_partLab.mp hc).1 v hv
  have hfib : (partLab F G (insert v S)).filter (fun c'' => Function.update c'' v 0 = c) =
      (vertexAdmissible G S c v).image (fun z => Function.update c v z) := by
    ext c''
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hc'', heq⟩
      have hcu : ∀ u ∈ S, c u = c'' u := fun u hu => by
        rw [← heq, Function.update_of_ne (fun h : u = v => hv (h ▸ hu))]
      obtain ⟨-, hf''⟩ := mem_partLab.mp hc''
      refine ⟨c'' v, ?_, ?_⟩
      · simp only [vertexAdmissible, mem_filter, mem_univ, true_and, mem_image, not_exists,
          not_and]
        refine ⟨fun a ha hca => ?_, fun u hu he => ?_, fun u hu he => ?_⟩
        · rw [hcu a ha] at hca
          have := hf''.1 a (mem_insert_of_mem ha) v (mem_insert_self v S) hca
          exact hv (this ▸ ha)
        · rw [hcu u hu]
          exact hf''.2 (u, v) he (mem_insert_of_mem hu) (mem_insert_self v S)
        · rw [hcu u hu]
          exact hf''.2 (v, u) he (mem_insert_self v S) (mem_insert_of_mem hu)
      · rw [← heq]
        funext u
        by_cases huv : u = v
        · subst huv
          simp
        · simp [Function.update_of_ne huv]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [mem_partLab]
        obtain ⟨hz0, hf⟩ := mem_partLab.mp hc
        refine ⟨fun u hu => ?_, feasible_insert hf hv hz⟩
        have huv : u ≠ v := fun h => hu (h ▸ mem_insert_self v S)
        rw [Function.update_of_ne huv]
        exact hz0 u (fun h => hu (mem_insert_of_mem h))
      · funext u
        by_cases huv : u = v
        · subst huv
          simp [hcv]
        · simp [Function.update_of_ne huv]
  rw [hfib, sum_image]
  intro z _ z' _ h
  simpa using congrFun h v

/-! ## The sequential upper bound -/

/-- **Sequential upper bound over the labellings of `S`** (Step 5 of `lem:extraction-rows`). Let
`S` be ordered by `ord` (injective on `S`), and let the weights `φ_b ≥ 0` (`b ∈ S`) read only the
labels of `b` and of the vertices of `S` earlier than `b`. If for every `b ∈ S` and every labelling
`c` feasible on the vertices of `S` earlier than `b`, `∑_{z ∈ Φ_b(c)} φ_b(c[b ↦ z]) ≤ M_b`, then
`∑_{c ∈ Inj(G[S])} ∏_{b ∈ S} φ_b(c) ≤ ∏_{b ∈ S} M_b`. -/
theorem partLab_seq_upper (G : OrientedGraph U) (S : Finset U) (ord : U → ℕ)
    (hord : Set.InjOn ord S) (φ : U → (U → F) → ℝ) (M : U → ℝ)
    (hφ0 : ∀ b y, 0 ≤ φ b y) (hM0 : ∀ b, 0 ≤ M b)
    (hloc : ∀ b ∈ S, ∀ y y' : U → F, (∀ a ∈ S, ord a ≤ ord b → y a = y' a) → φ b y = φ b y')
    (hstep : ∀ b ∈ S, ∀ c : U → F, Feasible F G (coverRowEarlier S ord b) c →
      ∑ z ∈ vertexAdmissible G (coverRowEarlier S ord b) c b, φ b (Function.update c b z) ≤
        M b) :
    ∑ c ∈ partLab F G S, ∏ b ∈ S, φ b c ≤ ∏ b ∈ S, M b := by
  suffices key : ∀ (m : ℕ) (S : Finset U), S.card = m → Set.InjOn ord S →
      (∀ b ∈ S, ∀ y y' : U → F, (∀ a ∈ S, ord a ≤ ord b → y a = y' a) → φ b y = φ b y') →
      (∀ b ∈ S, ∀ c : U → F, Feasible F G (coverRowEarlier S ord b) c →
        ∑ z ∈ vertexAdmissible G (coverRowEarlier S ord b) c b, φ b (Function.update c b z) ≤
          M b) →
      ∑ c ∈ partLab F G S, ∏ b ∈ S, φ b c ≤ ∏ b ∈ S, M b from key _ S rfl hord hloc hstep
  intro m
  induction m with
  | zero =>
    intro S hS _ _ _
    rw [card_eq_zero] at hS
    subst hS
    simp only [prod_empty, sum_const, nsmul_eq_mul, mul_one]
    have hcard : (partLab F G (∅ : Finset U)).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      funext u
      rw [(mem_partLab.mp ha).1 u (notMem_empty u), (mem_partLab.mp hb).1 u (notMem_empty u)]
    exact_mod_cast hcard
  | succ m ih =>
    intro S hS hord hloc hstep
    have hSne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨bm, hbm, hmax⟩ := S.exists_max_image ord hSne
    have hbmS' : bm ∉ S.erase bm := notMem_erase bm S
    have hins : insert bm (S.erase bm) = S := insert_erase hbm
    have hlt : ∀ b ∈ S.erase bm, ord b < ord bm := by
      intro b hb
      have hb' := mem_erase.mp hb
      have hle := hmax b hb'.2
      have hne : ord b ≠ ord bm := fun heq => hb'.1 (hord hb'.2 hbm heq)
      omega
    have hearl : coverRowEarlier S ord bm = S.erase bm := by
      ext a
      simp only [coverRowEarlier, mem_filter, mem_erase]
      constructor
      · rintro ⟨haS, hlt'⟩
        refine ⟨fun h => ?_, haS⟩
        subst h
        exact lt_irrefl _ hlt'
      · rintro ⟨hne, haS⟩
        exact ⟨haS, hlt a (mem_erase.mpr ⟨hne, haS⟩)⟩
    have hearl' : ∀ b ∈ S.erase bm,
        coverRowEarlier (S.erase bm) ord b = coverRowEarlier S ord b := by
      intro b hb
      ext a
      simp only [coverRowEarlier, mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨_, haS⟩, h⟩
        exact ⟨haS, h⟩
      · rintro ⟨haS, h⟩
        refine ⟨⟨fun hab => ?_, haS⟩, h⟩
        subst hab
        exact absurd (hlt b hb) (not_lt.mpr h.le)
    have hloc' : ∀ b ∈ S.erase bm, ∀ y y' : U → F,
        (∀ a ∈ S.erase bm, ord a ≤ ord b → y a = y' a) → φ b y = φ b y' := by
      intro b hb y y' hyy
      apply hloc b (mem_of_mem_erase hb) y y'
      intro a ha hab
      have hne : a ≠ bm := fun h => by
        subst h
        exact absurd (hlt b hb) (not_lt.mpr hab)
      exact hyy a (mem_erase.mpr ⟨hne, ha⟩) hab
    have hstep' : ∀ b ∈ S.erase bm, ∀ c : U → F,
        Feasible F G (coverRowEarlier (S.erase bm) ord b) c →
        ∑ z ∈ vertexAdmissible G (coverRowEarlier (S.erase bm) ord b) c b,
          φ b (Function.update c b z) ≤ M b := by
      intro b hb c hc
      rw [hearl' b hb] at hc ⊢
      exact hstep b (mem_of_mem_erase hb) c hc
    have hih := ih (S.erase bm) (by rw [card_erase_of_mem hbm]; omega)
      (hord.mono (erase_subset bm S)) hloc' hstep'
    calc ∑ c ∈ partLab F G S, ∏ b ∈ S, φ b c
        = ∑ c ∈ partLab F G (S.erase bm), ∑ z ∈ vertexAdmissible G (S.erase bm) c bm,
            ∏ b ∈ S, φ b (Function.update c bm z) := by
          have h := sum_partLab_insert G hbmS' (fun c => ∏ b ∈ S, φ b c)
          rw [hins] at h
          exact h
      _ = ∑ c ∈ partLab F G (S.erase bm), (∏ b ∈ S.erase bm, φ b c) *
            ∑ z ∈ vertexAdmissible G (S.erase bm) c bm, φ bm (Function.update c bm z) := by
          refine sum_congr rfl fun c _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun z _ => ?_
          rw [← mul_prod_erase S _ hbm, mul_comm]
          congr 1
          refine prod_congr rfl fun b hb => ?_
          apply hloc b (mem_of_mem_erase hb)
          intro a _ hab
          have hne : a ≠ bm := fun h => by
            subst h
            exact absurd (hlt b hb) (not_lt.mpr hab)
          exact Function.update_of_ne hne _ _
      _ ≤ ∑ c ∈ partLab F G (S.erase bm), (∏ b ∈ S.erase bm, φ b c) * M bm := by
          refine sum_le_sum fun c hc => ?_
          refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun b _ => hφ0 b c)
          have hf : Feasible F G (coverRowEarlier S ord bm) c := by
            rw [hearl]
            exact (mem_partLab.mp hc).2
          have h := hstep bm hbm c hf
          rw [hearl] at h
          exact h
      _ = (∑ c ∈ partLab F G (S.erase bm), ∏ b ∈ S.erase bm, φ b c) * M bm := by
          rw [sum_mul]
      _ ≤ (∏ b ∈ S.erase bm, M b) * M bm := mul_le_mul_of_nonneg_right hih (hM0 bm)
      _ = ∏ b ∈ S, M b := by rw [← mul_prod_erase S M hbm, mul_comm]

/-! ## Cover rows over the labellings of `C` (Steps 2–5 of `lem:extraction-rows`) -/

/-- **Steps 2–5 of `lem:extraction-rows`, summed over the labellings of `C`** (the form used in
Step 7 of `lem:matching:extractionk`, without the marginal comparison of Step 1). Let `C ⊆ U⁺` be
ordered by `ord` (injective on `C`), `x` injective and `H ⊆ {(a, b) ∈ E_× : b ∈ C}`. Then
`∑_{c' ∈ Inj(G⁺[C])} ∏_{(a,b) ∈ H} (1 + χ(ς_{ab}(c'_b - x_a))) 2^{κ_C(x, c')} ≤
∏_{b ∈ C} q 2^{-t_b} (1 + e_{s_b}(q, 2n) + r² 2^{s_b} ∑_{j ∈ U⁺} 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]})`
for every `n`; the factor of `b` is the numerator of `F_b(H)` times `q 2^{-t_b}`. Proof: Step 3
(`coverRow_integrand_le`), Step 4 (`coverRows_oneVertex`, `eq:extraction:onevertex`) and Step 5
(`partLab_seq_upper`). `WeilBound F` is Weil's theorem (literature input). -/
theorem partLab_coverRows_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ)
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
    exact coverRows_oneVertex hW G ς hς C ord H (fun e he => (hH e he).2) x hx n b x' hx'
  calc ∑ c' ∈ partLab F G C, coverRowIntegrand G ς C H x c'
      ≤ ∑ c' ∈ partLab F G C, ∏ b ∈ C, coverRowPhi G ς C ord H x b c' :=
        sum_le_sum fun c' _ => coverRow_integrand_le G ς C ord H hH x c'
    _ ≤ ∏ b ∈ C, M b :=
        partLab_seq_upper G C ord hord (coverRowPhi G ς C ord H x) M
          (fun b y => coverRow_phi_nonneg G ς C ord H x b y) hMnn hphi_loc hphi_step

/-! ## The lower count of `Inj_p(G⁺)` -/

/-- **The lower count of `lem:graphs:sequential`(a) along an order of all vertices**: labelling
`U⁺` in the order `ord` (injective), `|Inj_p(G⁺)| ≥ ∏_v q 2^{-t_v} (1 - e_{t_v}(q, n))`, `t_v` the
number of `G⁺`-neighbours of `v` earlier in the order (`ordT`), for `n ≥ |U⁺|`. The hypothesis
`e_{t_v}(q, n) ≤ 1` makes every factor nonnegative (under (S1), `e_t(p, n) < 1` for `t ≤ Δ`).
`WeilBound F` is Weil's theorem (literature input, through `card_vertexAdmissible`). -/
theorem card_injLabellings_ge (hW : WeilBound F) (G : OrientedGraph U) {n : ℕ}
    (hn : Fintype.card U ≤ n) (ord : U → ℕ) (hord : Function.Injective ord)
    (he : ∀ v, coarseError (ordT G ord v) (Fintype.card F) n ≤ 1) :
    ∏ v, ((Fintype.card F : ℝ) / 2 ^ ordT G ord v *
      (1 - coarseError (ordT G ord v) (Fintype.card F) n)) ≤ (injLabellings F G).card := by
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  set ℓ : U → ℝ := fun v => (Fintype.card F : ℝ) / 2 ^ ordT G ord v *
    (1 - coarseError (ordT G ord v) (Fintype.card F) n) with hℓ
  have hℓ0 : ∀ v, 0 ≤ ℓ v := fun v => mul_nonneg (by positivity) (by linarith [he v])
  have hℓstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord b) x' →
      ℓ b ≤ (vertexAdmissible G (coverRowEarlier univ ord b) x' b).card := by
    intro b _ x' hx'
    obtain ⟨-, hlo⟩ := card_vertexAdmissible hW G hx' b
    have hsoft := coverRow_softError_le hq1 n (nbrCount G (coverRowEarlier univ ord b) b)
    have hA : ((coverRowEarlier univ ord b).card : ℝ) ≤ n := by
      have := (card_le_univ (coverRowEarlier univ ord b)).trans hn
      exact_mod_cast this
    have hpos : (0 : ℝ) < 2 ^ nbrCount G (coverRowEarlier univ ord b) b := by positivity
    have h2A := mul_le_mul_of_nonneg_left hA hpos.le
    simp only [hℓ, ordT, coverRowT]
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith
  have hfe : Feasible F G (univ \ univ) (fun _ : U => (0 : F)) := by
    rw [Finset.sdiff_self]
    exact ⟨by simp, by simp⟩
  have hseg : ∀ b ∈ (univ : Finset U), ∀ b' ∈ (univ : Finset U), b' ∉ univ → ord b' < ord b :=
    fun _ _ _ _ hb' => absurd (mem_univ _) hb'
  have h := coverRow_seq_lower G (C := univ) (ord := ord) (fun a _ b _ hab => hord hab) ℓ 1
    hℓ0 zero_le_one hℓstep (fun y hy => by rw [extCount_univ G hy]; norm_num) _ univ rfl
    subset_rfl hseg _ hfe
  rw [Finset.sdiff_self, one_mul] at h
  have hext : extCount G ∅ (fun _ : U => (0 : F)) = (injLabellings F G).card := by
    unfold extCount
    congr 1
    exact filter_true_of_mem fun _ _ => by simp
  rw [hext] at h
  exact h

end Sarkozy.ExtractionK
