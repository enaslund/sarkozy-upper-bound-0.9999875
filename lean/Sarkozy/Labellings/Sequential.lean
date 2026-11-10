module

public import Sarkozy.Labellings.Extension

/-!
# Sequential counts of strict-square labellings (`def:graphs:labeling`, `lem:graphs:sequential`)

`paper/sections/12_labellings.tex`. An oriented graph `G` on a finite vertex set `W` (no loops,
at most one edge on each unordered pair) and a finite field `F` of odd characteristic with
`q` elements. A *strict-square labelling* `z : W → F` has `χ(z_v - z_u) = 1` on every edge
`(u, v)`; `injLabellings G` is `Inj_p(G)`. A labelling `x` is *feasible on* `A` if it is
injective on `A` and satisfies the edge conditions inside `A` (an element of `Inj_p(G[A])`).

* `extCount_insert`: labelling one more vertex, `C_A(x) = ∑_{c ∈ Φ_v(x)} C_{A ∪ {v}}(x[v ↦ c])`,
  where `Φ_v(x)` is the set of admissible labels of `v`; `feasible_insert`.
* `card_vertexAdmissible`: `Φ_v(x)` is a set `Φ` of `lem:extension` with the labels of the
  `t` neighbours of `v` in `A` as roots (signs from the orientation) and `x(A)` excluded, so
  `q - 𝔈_t - 2^t |A| ≤ 2^t |Φ_v(x)| ≤ q + 𝔈_t`, `𝔈_t = a_t √q + b_t` (from `WeilBound`).
* `extCount_bounds` is `lem:graphs:sequential`(a): along an ordering `l` of `W \ A`, the
  number of completions of a feasible `x` lies between the products of the one-step bounds
  `max(0, (q - 𝔈_t - 2^t n)/2^t)` and `(q + 𝔈_t)/2^t`, with `t` the number of earlier
  neighbours (`n ≥ |W|`). These are `p 2^{-t}(1 - e^-_t(n))` and `p 2^{-t}(1 + e^+_t)` of the
  graded pair. In particular every feasible labelling extends when the lower product is
  positive.
* `extCount_ratio` is the density statement of (b): completion counts of two feasible
  labellings of `A` differ by at most the factor `upper / lower`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- An oriented graph (`def:graphs:labeling`): a loopless edge set with at most one edge on each
unordered pair. -/
structure OrientedGraph (W : Type*) where
  E : Finset (W × W)
  loopless : ∀ u, (u, u) ∉ E
  oriented : ∀ u v, (u, v) ∈ E → (v, u) ∉ E

variable (F) in
/-- `x` is injective on `A` and satisfies the strict-square conditions of the edges inside `A`. -/
def Feasible (G : OrientedGraph W) (A : Finset W) (x : W → F) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, x a = x b → a = b) ∧
    ∀ e ∈ G.E, e.1 ∈ A → e.2 ∈ A → quadraticChar F (x e.2 - x e.1) = 1

variable (F) in
/-- `Inj_p(G)`: the injective strict-square labellings. -/
noncomputable def injLabellings (G : OrientedGraph W) : Finset (W → F) := by
  classical exact univ.filter fun y => Feasible F G univ y

/-- `C_A(x)`: the number of `y ∈ Inj_p(G)` that agree with `x` on `A`. -/
noncomputable def extCount (G : OrientedGraph W) (A : Finset W) (x : W → F) : ℕ := by
  classical exact ((injLabellings F G).filter fun y => ∀ a ∈ A, y a = x a).card

/-- The admissible labels of a new vertex `v` given the labels `x` on `A`. -/
noncomputable def vertexAdmissible (G : OrientedGraph W) (A : Finset W) (x : W → F) (v : W) :
    Finset F := by
  classical exact univ.filter fun c => c ∉ A.image x ∧
    (∀ u ∈ A, (u, v) ∈ G.E → quadraticChar F (c - x u) = 1) ∧
    (∀ u ∈ A, (v, u) ∈ G.E → quadraticChar F (x u - c) = 1)

/-- The number of neighbours of `v` in `A`. -/
noncomputable def nbrCount (G : OrientedGraph W) (A : Finset W) (v : W) : ℕ := by
  classical exact (A.filter fun u => (u, v) ∈ G.E ∨ (v, u) ∈ G.E).card

theorem feasible_insert {G : OrientedGraph W} {A : Finset W} {x : W → F} {v : W} {c : F}
    (hx : Feasible F G A x) (hv : v ∉ A) (hc : c ∈ vertexAdmissible G A x v) :
    Feasible F G (insert v A) (Function.update x v c) := by
  classical
  simp only [vertexAdmissible, mem_filter, mem_univ, true_and, mem_image, not_exists,
    not_and] at hc
  obtain ⟨hcx, hin, hout⟩ := hc
  have hupd : ∀ a ∈ A, Function.update x v c a = x a := fun a ha =>
    Function.update_of_ne (fun (h : a = v) => hv (h ▸ ha)) _ _
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    rcases mem_insert.mp ha with rfl | ha' <;> rcases mem_insert.mp hb with rfl | hb'
    · rfl
    · rw [Function.update_self, hupd b hb'] at hab
      exact absurd hab.symm (hcx b hb')
    · rw [Function.update_self, hupd a ha'] at hab
      exact absurd hab (hcx a ha')
    · rw [hupd a ha', hupd b hb'] at hab
      exact hx.1 a ha' b hb' hab
  · intro e he h1 h2
    rcases mem_insert.mp h1 with h1v | h1A <;> rcases mem_insert.mp h2 with h2v | h2A
    · have hev : e = (v, v) := Prod.ext h1v h2v
      rw [hev] at he
      exact absurd he (G.loopless v)
    · rw [h1v, Function.update_self, hupd _ h2A]
      exact hout e.2 h2A (by rw [← h1v]; exact he)
    · rw [h2v, Function.update_self, hupd _ h1A]
      exact hin e.1 h1A (by rw [← h2v]; exact he)
    · rw [hupd _ h1A, hupd _ h2A]
      exact hx.2 e he h1A h2A

/-- **One more vertex**: `C_A(x) = ∑_{c ∈ Φ_v(x)} C_{A ∪ {v}}(x[v ↦ c])` for `v ∉ A`. -/
theorem extCount_insert (G : OrientedGraph W) {A : Finset W} (x : W → F) {v : W} (hv : v ∉ A) :
    extCount G A x = ∑ c ∈ vertexAdmissible G A x v,
      extCount G (insert v A) (Function.update x v c) := by
  classical
  unfold extCount
  rw [card_eq_sum_card_fiberwise (f := fun y => y v) (t := univ) (fun _ _ => mem_univ _)]
  have hfib : ∀ c : F, ((injLabellings F G).filter fun y => ∀ a ∈ A, y a = x a).filter
      (fun y => y v = c) = (injLabellings F G).filter
        (fun y => ∀ a ∈ insert v A, y a = Function.update x v c a) := by
    intro c
    ext y
    simp only [mem_filter, mem_insert, forall_eq_or_imp, Function.update_self]
    constructor
    · rintro ⟨⟨hy, hA⟩, hyv⟩
      refine ⟨hy, hyv, fun a ha => ?_⟩
      rw [Function.update_of_ne (fun (h : a = v) => hv (h ▸ ha))]
      exact hA a ha
    · rintro ⟨hy, hyv, hA⟩
      refine ⟨⟨hy, fun a ha => ?_⟩, hyv⟩
      rw [hA a ha, Function.update_of_ne (fun (h : a = v) => hv (h ▸ ha))]
  simp_rw [hfib]
  symm
  apply sum_subset (subset_univ _)
  intro c _ hc
  rw [card_eq_zero, filter_eq_empty_iff]
  intro y hy hagree
  apply hc
  simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
  have hyv : y v = c := by simpa using hagree v (mem_insert_self v A)
  have hyA : ∀ a ∈ A, y a = x a := fun a ha => by
    rw [hagree a (mem_insert_of_mem ha), Function.update_of_ne (fun (h : a = v) => hv (h ▸ ha))]
  simp only [vertexAdmissible, mem_filter, mem_univ, true_and, mem_image, not_exists, not_and]
  refine ⟨fun a ha hxa => ?_, fun u hu he => ?_, fun u hu he => ?_⟩
  · have : y a = y v := by rw [hyA a ha, hxa, hyv]
    exact hv (hy.1 a (mem_univ _) v (mem_univ _) this ▸ ha)
  · have := hy.2 (u, v) he (mem_univ _) (mem_univ _)
    simpa [hyv, hyA u hu] using this
  · have := hy.2 (v, u) he (mem_univ _) (mem_univ _)
    simpa [hyv, hyA u hu] using this

theorem extCount_univ (G : OrientedGraph W) {x : W → F} (hx : Feasible F G univ x) :
    extCount G univ x = 1 := by
  classical
  unfold extCount
  rw [card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  simp only [injLabellings, mem_filter, mem_univ, true_and, forall_const, mem_singleton]
  constructor
  · rintro ⟨_, h⟩; exact funext h
  · rintro rfl; exact ⟨hx, fun _ => rfl⟩

/-! ## The one-step count -/

/-- The bound `𝔈_t = a_t √q + b_t` of the soft count. -/
noncomputable def softError (q : ℝ) (t : ℕ) : ℝ := gradedA t * Real.sqrt q + gradedB t

theorem gradedA_nonneg (t : ℕ) : 0 ≤ gradedA t := by
  unfold gradedA
  split_ifs with h0
  · exact le_rfl
  · rcases Nat.lt_or_ge t 3 with ht | ht
    · interval_cases t
      · exact absurd rfl h0
      · norm_num
      · norm_num
    · have : (0 : ℝ) ≤ (t : ℝ) - 3 := by
        have : (3 : ℝ) ≤ t := by exact_mod_cast ht
        linarith
      positivity

theorem gradedB_nonneg (t : ℕ) : 0 ≤ gradedB t := by
  unfold gradedB
  split_ifs with h0
  · exact le_rfl
  · have : (1 : ℝ) ≤ 2 ^ (t - 1) := one_le_pow₀ (by norm_num)
    linarith

theorem softError_nonneg (q : ℝ) (t : ℕ) : 0 ≤ softError q t :=
  add_nonneg (mul_nonneg (gradedA_nonneg t) (Real.sqrt_nonneg _)) (gradedB_nonneg t)

/-- **The one-step count** (`lem:extension` applied to a new vertex). -/
theorem card_vertexAdmissible (hW : WeilBound F) (G : OrientedGraph W) {A : Finset W}
    {x : W → F} (hx : Feasible F G A x) (v : W) :
    (2 : ℝ) ^ nbrCount G A v * (vertexAdmissible G A x v).card ≤
        Fintype.card F + softError (Fintype.card F) (nbrCount G A v) ∧
      (Fintype.card F : ℝ) - softError (Fintype.card F) (nbrCount G A v) -
          2 ^ nbrCount G A v * A.card ≤
        2 ^ nbrCount G A v * (vertexAdmissible G A x v).card := by
  classical
  set N := A.filter fun u => (u, v) ∈ G.E ∨ (v, u) ∈ G.E with hN
  have hNcard : nbrCount G A v = Fintype.card N := by
    simp only [nbrCount, hN, Fintype.card_coe]
  have hNA : ∀ u ∈ N, u ∈ A := fun u hu => (mem_filter.mp hu).1
  let β : N → F := fun u => x u
  have hβ : Function.Injective β := fun u w h => Subtype.ext (hx.1 u (hNA u u.2) w (hNA w w.2) h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : N → ℤ := fun u => if (u.1, v) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ u, s u = 1 ∨ s u = -1 := fun u => by
    simp only [s]; split_ifs
    · exact Or.inl rfl
    · exact hm1
  have hroots : ∀ u, β u ∈ A.image x := fun u => mem_image_of_mem x (hNA u u.2)
  have heq : vertexAdmissible G A x v = admissible β s (A.image x) := by
    ext c
    simp only [vertexAdmissible, admissible, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hc, hin, hout⟩
      refine ⟨hc, fun u => ?_⟩
      have hu := (mem_filter.mp u.2).2
      simp only [s, β]
      split_ifs with h
      · exact hin u (hNA u u.2) h
      · have hvu : (v, u.1) ∈ G.E := hu.resolve_left h
        have h1 := hout u (hNA u u.2) hvu
        have : x u - c = -1 * (c - x u) := by ring
        rw [this, map_mul] at h1
        rcases hm1 with h' | h' <;> rw [h'] at h1 ⊢ <;> linarith
    · rintro ⟨hc, hall⟩
      refine ⟨hc, fun u hu he => ?_, fun u hu he => ?_⟩
      · have hmem : u ∈ N := mem_filter.mpr ⟨hu, Or.inl he⟩
        have := hall ⟨u, hmem⟩
        simpa [s, β, he] using this
      · have hmem : u ∈ N := mem_filter.mpr ⟨hu, Or.inr he⟩
        have hnot : (u, v) ∉ G.E := G.oriented v u he
        have h1 := hall ⟨u, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : x u - c = -1 * (c - x u) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hb := extension_bounds hW β hβ s hs (A.image x) hroots
  rw [← heq, ← hNcard] at hb
  have hcardX : ((A.image x).card : ℝ) ≤ A.card := by exact_mod_cast card_image_le
  have hpow : (0 : ℝ) ≤ 2 ^ nbrCount G A v := by positivity
  refine ⟨hb.1, ?_⟩
  have := mul_le_mul_of_nonneg_left hcardX hpow
  unfold softError
  linarith [hb.2]

/-! ## Products along an ordering -/

/-- The one-step upper bound `(q + 𝔈_t) / 2^t = q 2^{-t}(1 + e^+_t)`. -/
noncomputable def stepUpper (q : ℝ) (t : ℕ) : ℝ := (q + softError q t) / 2 ^ t

/-- The one-step lower bound `max(0, (q - 𝔈_t - 2^t n) / 2^t) = max(0, q 2^{-t}(1 - e^-_t(n)))`. -/
noncomputable def stepLower (q : ℝ) (n t : ℕ) : ℝ := max 0 ((q - softError q t - 2 ^ t * n) / 2 ^ t)

/-- The upper product `∏_i (q + 𝔈_{t_i}) / 2^{t_i}` along an ordering. -/
noncomputable def upperProd (G : OrientedGraph W) (q : ℝ) : Finset W → List W → ℝ
  | _, [] => 1
  | A, v :: l => stepUpper q (nbrCount G A v) * upperProd G q (insert v A) l

/-- The lower product along an ordering. -/
noncomputable def lowerProd (G : OrientedGraph W) (q : ℝ) (n : ℕ) : Finset W → List W → ℝ
  | _, [] => 1
  | A, v :: l => stepLower q n (nbrCount G A v) * lowerProd G q n (insert v A) l

omit [Fintype W] in
theorem upperProd_nonneg (G : OrientedGraph W) {q : ℝ} (hq : 0 ≤ q) :
    ∀ (l : List W) (A : Finset W), 0 ≤ upperProd G q A l
  | [], _ => by simp [upperProd]
  | v :: l, A => by
      simp only [upperProd]
      exact mul_nonneg (div_nonneg (add_nonneg hq (softError_nonneg _ _)) (by positivity))
        (upperProd_nonneg G hq l _)

omit [Fintype W] in
theorem lowerProd_nonneg (G : OrientedGraph W) (q : ℝ) (n : ℕ) :
    ∀ (l : List W) (A : Finset W), 0 ≤ lowerProd G q n A l
  | [], _ => by simp [lowerProd]
  | v :: l, A => by
      simp only [lowerProd]
      exact mul_nonneg (le_max_left _ _) (lowerProd_nonneg G q n l _)

/-- **`lem:graphs:sequential`(a).** Let `l` be an ordering of `W \ A` (no repetitions) and
`n ≥ |W|`. For every labelling `x` feasible on `A`, the number of its completions in
`Inj_p(G)` lies between the lower and the upper products along `l`. -/
theorem extCount_bounds (hW : WeilBound F) (G : OrientedGraph W) {n : ℕ}
    (hn : Fintype.card W ≤ n) :
    ∀ (l : List W) (A : Finset W) (x : W → F), l.Nodup → (∀ w, w ∈ A ∨ w ∈ l) →
      (∀ w ∈ l, w ∉ A) → Feasible F G A x →
      lowerProd G (Fintype.card F) n A l ≤ extCount G A x ∧
        (extCount G A x : ℝ) ≤ upperProd G (Fintype.card F) A l
  | [], A, x, _, hcov, _, hx => by
      have hA : A = univ := eq_univ_of_forall fun w => (hcov w).resolve_right (by simp)
      subst hA
      rw [extCount_univ G hx]
      simp [lowerProd, upperProd]
  | v :: l, A, x, hnd, hcov, hdisj, hx => by
      have hv : v ∉ A := hdisj v (List.mem_cons_self ..)
      have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
      have hvl : v ∉ l := (List.nodup_cons.mp hnd).1
      have hcov' : ∀ w, w ∈ insert v A ∨ w ∈ l := fun w => by
        rcases hcov w with h | h
        · exact Or.inl (mem_insert_of_mem h)
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inl (mem_insert_self _ _)
          · exact Or.inr h'
      have hdisj' : ∀ w ∈ l, w ∉ insert v A := fun w hw hmem => by
        rcases mem_insert.mp hmem with rfl | h
        · exact hvl hw
        · exact hdisj w (List.mem_cons_of_mem _ hw) h
      have hIH : ∀ c ∈ vertexAdmissible G A x v,
          lowerProd G (Fintype.card F) n (insert v A) l ≤
              extCount G (insert v A) (Function.update x v c) ∧
            (extCount G (insert v A) (Function.update x v c) : ℝ) ≤
              upperProd G (Fintype.card F) (insert v A) l := fun c hc =>
        extCount_bounds hW G hn l (insert v A) _ hnd' hcov' hdisj' (feasible_insert hx hv hc)
      have hrec := extCount_insert G x hv
      have hrecR : (extCount G A x : ℝ) = ∑ c ∈ vertexAdmissible G A x v,
          (extCount G (insert v A) (Function.update x v c) : ℝ) := by exact_mod_cast hrec
      set t := nbrCount G A v
      set Φ := vertexAdmissible G A x v
      obtain ⟨hup, hlo⟩ := card_vertexAdmissible hW G hx v
      have hpos : (0 : ℝ) < 2 ^ t := by positivity
      have hAn : (A.card : ℝ) ≤ n := by
        have : A.card ≤ n := (card_le_univ A).trans hn
        exact_mod_cast this
      simp only [lowerProd, upperProd]
      constructor
      · -- lower bound
        have hsum : (Φ.card : ℝ) * lowerProd G (Fintype.card F) n (insert v A) l ≤
            (extCount G A x : ℝ) := by
          rw [hrecR, ← nsmul_eq_mul, ← sum_const]
          exact sum_le_sum fun c hc => (hIH c hc).1
        have hstep : stepLower (Fintype.card F) n t ≤ Φ.card := by
          unfold stepLower
          refine max_le (by positivity) ?_
          rw [div_le_iff₀ hpos]
          have := mul_le_mul_of_nonneg_left hAn hpos.le
          nlinarith [hlo]
        exact (mul_le_mul_of_nonneg_right hstep (lowerProd_nonneg G _ n l _)).trans hsum
      · -- upper bound
        have hsum : (extCount G A x : ℝ) ≤
            (Φ.card : ℝ) * upperProd G (Fintype.card F) (insert v A) l := by
          rw [hrecR, ← nsmul_eq_mul, ← sum_const]
          exact sum_le_sum fun c hc => (hIH c hc).2
        have hstep : (Φ.card : ℝ) ≤ stepUpper (Fintype.card F) t := by
          unfold stepUpper
          rw [le_div_iff₀ hpos]
          linarith [hup]
        exact hsum.trans (mul_le_mul_of_nonneg_right hstep
          (upperProd_nonneg G (Nat.cast_nonneg _) l _))

/-- **`lem:graphs:sequential`(b), density form.** Completion counts of two feasible labellings
of `A` are within the factor `upper / lower` of each other: the marginal of `λ_p(G)` on `A`
has density in `[lower/upper, upper/lower]` relative to the uniform law on the feasible
labellings of `A`. -/
theorem extCount_ratio (hW : WeilBound F) (G : OrientedGraph W) {n : ℕ}
    (hn : Fintype.card W ≤ n) (l : List W) (A : Finset W) (hnd : l.Nodup)
    (hcov : ∀ w, w ∈ A ∨ w ∈ l) (hdisj : ∀ w ∈ l, w ∉ A) {x x' : W → F}
    (hx : Feasible F G A x) (hx' : Feasible F G A x') :
    lowerProd G (Fintype.card F) n A l * extCount G A x ≤
      upperProd G (Fintype.card F) A l * extCount G A x' := by
  obtain ⟨h1, h2⟩ := extCount_bounds hW G hn l A x hnd hcov hdisj hx
  obtain ⟨h1', h2'⟩ := extCount_bounds hW G hn l A x' hnd hcov hdisj hx'
  have hL := lowerProd_nonneg G (Fintype.card F) n l A
  have hU := upperProd_nonneg G (Nat.cast_nonneg (Fintype.card F)) l A
  calc lowerProd G (Fintype.card F) n A l * extCount G A x
      ≤ lowerProd G (Fintype.card F) n A l * upperProd G (Fintype.card F) A l :=
        mul_le_mul_of_nonneg_left h2 hL
    _ = upperProd G (Fintype.card F) A l * lowerProd G (Fintype.card F) n A l := mul_comm _ _
    _ ≤ upperProd G (Fintype.card F) A l * extCount G A x' := mul_le_mul_of_nonneg_left h1' hU

end Sarkozy.Labellings
