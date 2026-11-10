module

public import Sarkozy.ExtractionK.PartialLabellings

@[expose] public section

/-!
# Grouped extraction, I: grouping, fibres and the kernel step (`lem:matching:extractionk`)

`paper/sections/16_extraction.tex`, `lem:matching:extractionk`, Steps 1–4, in the counting form
used throughout `ExtractionK/` (sums over `𝓘⁺ = Inj_p(G⁺)`; the expectations over `μ = λ_p(G⁺)`
are these sums divided by `|𝓘⁺|`).

* `sum_cls_eq_classKer` (Step 1): `∑_{S ∈ 𝒞(P, A)} χ_S = ∏_{e ∈ P} χ_e ∏_{e ∈ F} (1 + χ_e)`.
* `classKer_eq_groups` (Step 1, the groups): under (VC_k) and (W_k) the class kernel is
  `𝖶(x_V, x'_W) Θ₁ Θ₂ Γ`, with `Θ₁` over the pairs `a ∉ C_x, b ∈ C_z` (`𝒢₁`), `Θ₂` over
  `a ∈ C_x, b ∉ C_z` (`𝒢₂`), `Γ` over `a ∈ C_x, b ∈ C_z` (`𝒢_Γ`) (`groupKer`, `groupPos` for the
  products of `1 + χ_e` over the free pairs); each reads only the coordinates of its group
  (`groupKer_congr`, `rectKer_congr`).
* `bilinear_decomp` (Step 2, in counting form): grouping the sum over `(x, x')` by the cover
  labels `(c, c')` and the witness labels `(v, w)`,
  `∑ f K_𝒞 h = ∑_{c,c'} Γ(c,c') ∑_{v,w} 𝖺_{c,c'}(v) 𝖶(v,w) 𝖻_{c,c'}(w)` (`alphaF`, `betaF`;
  the paper's `𝖺`, `𝖻` are these sums divided by the fibre sizes).
* `bilinear_le` (Steps 3–4): the kernel hypothesis bounds each `(c, c')` term by
  `Λ ‖𝖺_{c,c'}‖ ‖𝖻_{c,c'}‖`, and Cauchy–Schwarz with the weights `|Γ|` gives
  `|∑ f K_𝒞 h| ≤ Λ (∑ |Γ| ‖𝖺‖²)^{1/2} (∑ |Γ| ‖𝖻‖²)^{1/2}`.

In counting form no density (`D_V`, `eq:extraction:cross-density`) is needed: the kernel is
applied to the fibre sums themselves, and the completions are counted once, in the final
normalization (`Grouped.lean`). This is why the bound of `grouped_extraction` does not carry the
paper's factor `(R̃_{U_x} R̃_{U_z})^{1/2}` (see the report).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-! ## Part A -/

section PartA

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
theorem chiPair_abs_le (ς : U → U → ℤ) (e : U × U) (x x' : U → F) : |chiPair ς e x x'| ≤ 1 := by
  unfold chiPair
  rcases eq_or_ne ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) 0 with h | h
  · rw [h]; simp
  · rcases quadraticChar_dichotomy h with h' | h' <;> rw [h'] <;> norm_num

omit [Fintype U] [DecidableEq U] in
theorem one_add_chiPair_nonneg (ς : U → U → ℤ) (e : U × U) (x x' : U → F) :
    0 ≤ 1 + chiPair ς e x x' := by
  have := chiPair_abs_le ς e x x'
  have := neg_abs_le (chiPair ς e x x')
  linarith

omit [Fintype U] [DecidableEq U] in
theorem one_add_chiPair_le_two (ς : U → U → ℤ) (e : U × U) (x x' : U → F) :
    1 + chiPair ς e x x' ≤ 2 := by
  have := chiPair_abs_le ς e x x'
  have := le_abs_self (chiPair ς e x x')
  linarith

omit [Fintype U] [DecidableEq U] in
theorem chiPair_congr (ς : U → U → ℤ) (e : U × U) {x x' y y' : U → F} (h1 : x e.1 = y e.1)
    (h2 : x' e.2 = y' e.2) : chiPair ς e x x' = chiPair ς e y y' := by
  unfold chiPair
  rw [h1, h2]

omit [Fintype U] [DecidableEq U] in
/-- Antisymmetry `ς_{kj} = -ς_{jk}` (`lem:spec:elementary`) gives
`χ_{(b,a)}(x', x) = χ_{(a,b)}(x, x')`. -/
theorem chiPair_swap (ς : U → U → ℤ) (hanti : ∀ j k, ς k j = -ς j k) (e : U × U)
    (x x' : U → F) : chiPair ς e.swap x' x = chiPair ς e x x' := by
  unfold chiPair
  simp only [Prod.fst_swap, Prod.snd_swap, hanti e.1 e.2, Int.cast_neg]
  congr 2
  ring

omit [Fintype F] [DecidableEq F] [Fintype U] in
theorem restr_apply_of_mem {S : Finset U} {u : U} (hu : u ∈ S) (x : U → F) :
    restr S x u = x u := by
  simp [restr, hu]

omit [Fintype U] in
/-- **Step 1 of `lem:matching:extractionk` (grouping)**: the sets of `𝒞(P, A)` are the sets
`P ∪ S'` with `S' ⊆ F`, so `∑_{S ∈ 𝒞} χ_S = ∏_{e ∈ P} χ_e ∏_{e ∈ F} (1 + χ_e)`. -/
theorem sum_cls_eq_classKer (ς : U → U → ℤ) (Ex P A : Finset (U × U)) (hP : P ⊆ Ex)
    (hPA : Disjoint P A) (x x' : U → F) :
    ∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x' = classKer ς P (Ex \ (P ∪ A)) x x' := by
  unfold classKer
  rw [prod_one_add, mul_sum]
  symm
  refine sum_nbij' (fun T => P ∪ T) (fun S => S \ P) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [mem_powerset] at hT
    rw [mem_cls]
    refine ⟨subset_union_left, fun e he => ?_⟩
    rcases mem_union.mp he with he | he
    · exact mem_sdiff.mpr ⟨hP he, disjoint_left.mp hPA he⟩
    · have := hT he
      simp only [mem_sdiff, mem_union, not_or] at this
      exact mem_sdiff.mpr ⟨this.1, this.2.2⟩
  · intro S hS
    rw [mem_cls] at hS
    rw [mem_powerset]
    intro e he
    simp only [mem_sdiff] at he
    have := hS.2 he.1
    simp only [mem_sdiff] at this
    simp only [mem_sdiff, mem_union, not_or]
    exact ⟨this.1, he.2, this.2⟩
  · intro T hT
    rw [mem_powerset] at hT
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h | h, hn⟩
      · exact absurd h hn
      · exact h
    · intro h
      refine ⟨Or.inr h, fun hP' => ?_⟩
      have := hT h
      simp only [mem_sdiff, mem_union, not_or] at this
      exact this.2.1 hP'
  · intro S hS
    rw [mem_cls] at hS
    exact union_sdiff_of_subset hS.1
  · intro T hT
    simp only [mem_powerset] at hT
    have hdisj : Disjoint P T := by
      rw [disjoint_left]
      intro e heP heT
      have := hT heT
      simp only [mem_sdiff, mem_union, not_or] at this
      exact this.2.1 heP
    rw [prod_union hdisj]

end PartA

/-! ## Part B: the groups of pairs -/

section PartB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The product of `ψ_e` (`χ_e` for `e ∈ P`, `1 + χ_e` for `e ∈ Fr`) over the pairs satisfying
`p`. -/
noncomputable def groupKer (ς : U → U → ℤ) (P Fr : Finset (U × U)) (p : U × U → Prop)
    [DecidablePred p] (x x' : U → F) : ℝ :=
  (∏ e ∈ P.filter p, chiPair ς e x x') * ∏ e ∈ Fr.filter p, (1 + chiPair ς e x x')

/-- The product of `1 + χ_e` over the free pairs satisfying `p`. -/
noncomputable def groupPos (ς : U → U → ℤ) (Fr : Finset (U × U)) (p : U × U → Prop)
    [DecidablePred p] (x x' : U → F) : ℝ :=
  ∏ e ∈ Fr.filter p, (1 + chiPair ς e x x')

omit [Fintype U] [DecidableEq U] in
theorem groupPos_nonneg (ς : U → U → ℤ) (Fr : Finset (U × U)) (p : U × U → Prop)
    [DecidablePred p] (x x' : U → F) : 0 ≤ groupPos ς Fr p x x' :=
  prod_nonneg fun e _ => one_add_chiPair_nonneg ς e x x'

omit [Fintype U] [DecidableEq U] in
theorem abs_groupKer_le (ς : U → U → ℤ) (P Fr : Finset (U × U)) (p : U × U → Prop)
    [DecidablePred p] (x x' : U → F) : |groupKer ς P Fr p x x'| ≤ groupPos ς Fr p x x' := by
  unfold groupKer groupPos
  rw [abs_mul, abs_prod, abs_of_nonneg (prod_nonneg fun e _ => one_add_chiPair_nonneg ς e x x')]
  have h1 : ∏ e ∈ P.filter p, |chiPair ς e x x'| ≤ 1 :=
    prod_le_one₀ (fun e _ => abs_nonneg _) (fun e _ => chiPair_abs_le ς e x x')
  exact mul_le_of_le_one_left (prod_nonneg fun e _ => one_add_chiPair_nonneg ς e x x') h1

omit [Fintype U] [DecidableEq U] in
theorem groupKer_congr (ς : U → U → ℤ) (P Fr : Finset (U × U)) (p : U × U → Prop)
    [DecidablePred p] {x x' y y' : U → F}
    (h : ∀ e, p e → x e.1 = y e.1 ∧ x' e.2 = y' e.2) :
    groupKer ς P Fr p x x' = groupKer ς P Fr p y y' := by
  unfold groupKer
  congr 1
  · exact prod_congr rfl fun e he =>
      chiPair_congr ς e (h e (mem_filter.mp he).2).1 (h e (mem_filter.mp he).2).2
  · exact prod_congr rfl fun e he => by
      rw [chiPair_congr ς e (h e (mem_filter.mp he).2).1 (h e (mem_filter.mp he).2).2]

omit [Fintype U] [DecidableEq U] in
theorem groupPos_congr (ς : U → U → ℤ) (Fr : Finset (U × U)) (p : U × U → Prop)
    [DecidablePred p] {x x' y y' : U → F}
    (h : ∀ e, p e → x e.1 = y e.1 ∧ x' e.2 = y' e.2) :
    groupPos ς Fr p x x' = groupPos ς Fr p y y' := by
  unfold groupPos
  exact prod_congr rfl fun e he => by
    rw [chiPair_congr ς e (h e (mem_filter.mp he).2).1 (h e (mem_filter.mp he).2).2]

omit [Fintype U] in
/-- A set of pairs each with `a ∈ C_x` or `b ∈ C_z` splits into the three groups
`𝒢₁ : a ∉ C_x, b ∈ C_z`, `𝒢₂ : a ∈ C_x, b ∉ C_z`, `𝒢_Γ : a ∈ C_x, b ∈ C_z`. -/
theorem prod_three_groups (S : Finset (U × U)) (Cx Cz : Finset U)
    (hS : ∀ e ∈ S, e.1 ∈ Cx ∨ e.2 ∈ Cz) (g : U × U → ℝ) :
    ∏ e ∈ S, g e = (∏ e ∈ S.filter (fun e => e.1 ∉ Cx ∧ e.2 ∈ Cz), g e) *
      (∏ e ∈ S.filter (fun e => e.1 ∈ Cx ∧ e.2 ∉ Cz), g e) *
        ∏ e ∈ S.filter (fun e => e.1 ∈ Cx ∧ e.2 ∈ Cz), g e := by
  rw [← prod_filter_mul_prod_filter_not S (fun e => e.1 ∈ Cx),
    ← prod_filter_mul_prod_filter_not (S.filter fun e => e.1 ∈ Cx) (fun e => e.2 ∈ Cz),
    filter_filter, filter_filter]
  have h1 : S.filter (fun e => ¬ e.1 ∈ Cx) = S.filter (fun e => e.1 ∉ Cx ∧ e.2 ∈ Cz) := by
    refine filter_congr fun e he => ?_
    constructor
    · intro h; exact ⟨h, (hS e he).resolve_left h⟩
    · exact fun h => h.1
  rw [h1]
  have h2 : S.filter (fun e => e.1 ∈ Cx ∧ ¬ e.2 ∈ Cz) =
      S.filter (fun e => e.1 ∈ Cx ∧ e.2 ∉ Cz) := rfl
  rw [h2]
  ring

omit [Fintype U] in
/-- **The grouping of Step 1**: with the cover condition (VC_k) (`hP`, `hFr`: every present
pair outside `V × W` and every free pair has `a ∈ C_x` or `b ∈ C_z`; no free pair lies in
`V × W` by (W_k)) and `V ∩ C_x = W ∩ C_z = ∅`, the class kernel is
`𝖶(x_V, x'_W) Θ₁ Θ₂ Γ`. -/
theorem classKer_eq_groups (ς : U → U → ℤ) (P Fr : Finset (U × U)) (V W Cx Cz : Finset U)
    (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) (x x' : U → F) :
    classKer ς P Fr x x' = rectKer ς P V W x x' *
      groupKer ς P Fr (fun e => e.1 ∉ Cx ∧ e.2 ∈ Cz) x x' *
      groupKer ς P Fr (fun e => e.1 ∈ Cx ∧ e.2 ∉ Cz) x x' *
      groupKer ς P Fr (fun e => e.1 ∈ Cx ∧ e.2 ∈ Cz) x x' := by
  unfold classKer rectKer groupKer
  rw [← prod_filter_mul_prod_filter_not P (fun e => e.1 ∈ V ∧ e.2 ∈ W)]
  have hP' : ∀ e ∈ P.filter (fun e => ¬ (e.1 ∈ V ∧ e.2 ∈ W)), e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    rw [mem_filter] at he
    exact (hP e he.1).resolve_left he.2
  rw [prod_three_groups _ Cx Cz hP', prod_three_groups Fr Cx Cz hFr, filter_filter,
    filter_filter, filter_filter]
  have e1 : P.filter (fun e => ¬ (e.1 ∈ V ∧ e.2 ∈ W) ∧ (e.1 ∉ Cx ∧ e.2 ∈ Cz)) =
      P.filter (fun e => e.1 ∉ Cx ∧ e.2 ∈ Cz) :=
    filter_congr fun e _ => ⟨fun h => h.2, fun h => ⟨fun h' => hWC e.2 h'.2 h.2, h⟩⟩
  have e2 : P.filter (fun e => ¬ (e.1 ∈ V ∧ e.2 ∈ W) ∧ (e.1 ∈ Cx ∧ e.2 ∉ Cz)) =
      P.filter (fun e => e.1 ∈ Cx ∧ e.2 ∉ Cz) :=
    filter_congr fun e _ => ⟨fun h => h.2, fun h => ⟨fun h' => hVC e.1 h'.1 h.1, h⟩⟩
  have e3 : P.filter (fun e => ¬ (e.1 ∈ V ∧ e.2 ∈ W) ∧ (e.1 ∈ Cx ∧ e.2 ∈ Cz)) =
      P.filter (fun e => e.1 ∈ Cx ∧ e.2 ∈ Cz) :=
    filter_congr fun e _ => ⟨fun h => h.2, fun h => ⟨fun h' => hVC e.1 h'.1 h.1, h⟩⟩
  rw [e1, e2, e3]
  ring

omit [Fintype U] in
theorem rectKer_congr (ς : U → U → ℤ) (P : Finset (U × U)) (V W : Finset U) {x x' y y' : U → F}
    (h1 : ∀ u ∈ V, x u = y u) (h2 : ∀ u ∈ W, x' u = y' u) :
    rectKer ς P V W x x' = rectKer ς P V W y y' := by
  unfold rectKer
  exact prod_congr rfl fun e he =>
    chiPair_congr ς e (h1 e.1 (mem_filter.mp he).2.1) (h2 e.2 (mem_filter.mp he).2.2)

end PartB

/-! ## Part C: fibres over the cover labels and the witness labels -/

section PartC

theorem sum_fiber_two {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α)
    (g₁ : α → β) (g₂ : α → γ) (T₁ : Finset β) (T₂ : Finset γ) (h₁ : ∀ a ∈ s, g₁ a ∈ T₁)
    (h₂ : ∀ a ∈ s, g₂ a ∈ T₂) (φ : α → ℝ) :
    ∑ a ∈ s, φ a = ∑ c ∈ T₁, ∑ v ∈ T₂, ∑ a ∈ s.filter (fun a => g₁ a = c ∧ g₂ a = v), φ a := by
  rw [← sum_fiberwise_of_maps_to h₁]
  refine sum_congr rfl fun c _ => ?_
  rw [← sum_fiberwise_of_maps_to (s := s.filter (fun a => g₁ a = c)) (g := g₂)
    (fun a ha => h₂ a (mem_filter.mp ha).1)]
  refine sum_congr rfl fun v _ => ?_
  rw [filter_filter]

end PartC

/-! ## Part D: the kernel bound and the Cauchy–Schwarz inequalities -/

section PartD

open Sarkozy.Influence

/-- The bilinear form of a matrix with an operator bound. -/
theorem opBound_bilinear {ι κ : Type*} {R : Finset ι} {C : Finset κ} {A : ι → κ → ℝ} {Λ : ℝ}
    (h : OpBound R C A Λ) (hΛ : 0 ≤ Λ) (a : ι → ℝ) (b : κ → ℝ) :
    |∑ i ∈ R, ∑ j ∈ C, a i * A i j * b j| ≤
      Λ * Real.sqrt (∑ i ∈ R, a i ^ 2) * Real.sqrt (∑ j ∈ C, b j ^ 2) := by
  have heq : ∑ i ∈ R, ∑ j ∈ C, a i * A i j * b j = ∑ i ∈ R, a i * ∑ j ∈ C, A i j * b j := by
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [heq]
  have hcs : |∑ i ∈ R, a i * ∑ j ∈ C, A i j * b j| ≤
      Real.sqrt (∑ i ∈ R, a i ^ 2) * Real.sqrt (∑ i ∈ R, (∑ j ∈ C, A i j * b j) ^ 2) := by
    calc |∑ i ∈ R, a i * ∑ j ∈ C, A i j * b j|
        ≤ ∑ i ∈ R, |a i| * |∑ j ∈ C, A i j * b j| := by
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ Real.sqrt (∑ i ∈ R, |a i| ^ 2) *
            Real.sqrt (∑ i ∈ R, |∑ j ∈ C, A i j * b j| ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = _ := by simp only [sq_abs]
  have hop := h.vnorm_le hΛ b
  unfold vnorm at hop
  calc |∑ i ∈ R, a i * ∑ j ∈ C, A i j * b j|
      ≤ Real.sqrt (∑ i ∈ R, a i ^ 2) * Real.sqrt (∑ i ∈ R, (∑ j ∈ C, A i j * b j) ^ 2) := hcs
    _ ≤ Real.sqrt (∑ i ∈ R, a i ^ 2) * (Λ * Real.sqrt (∑ j ∈ C, b j ^ 2)) :=
        mul_le_mul_of_nonneg_left hop (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Cauchy–Schwarz over a double sum with nonnegative weights `g`. -/
theorem double_sum_cs {β γ : Type*} (s : Finset β) (t : Finset γ) (g a b : β → γ → ℝ)
    (hg : ∀ c c', 0 ≤ g c c') :
    ∑ c ∈ s, ∑ c' ∈ t, g c c' * (|a c c'| * |b c c'|) ≤
      Real.sqrt (∑ c ∈ s, ∑ c' ∈ t, g c c' * a c c' ^ 2) *
        Real.sqrt (∑ c ∈ s, ∑ c' ∈ t, g c c' * b c c' ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (s ×ˢ t)
    (fun cc => Real.sqrt (g cc.1 cc.2) * |a cc.1 cc.2|)
    (fun cc => Real.sqrt (g cc.1 cc.2) * |b cc.1 cc.2|)
  simp only [mul_pow, Real.sq_sqrt (hg _ _), sq_abs] at h
  rw [sum_product, sum_product, sum_product] at h
  refine le_trans (le_of_eq ?_) h
  refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => ?_
  have := Real.mul_self_sqrt (hg c c')
  calc g c c' * (|a c c'| * |b c c'|)
      = (Real.sqrt (g c c') * Real.sqrt (g c c')) * (|a c c'| * |b c c'|) := by rw [this]
    _ = _ := by ring

end PartD

/-! ## Part C₂: the decomposition of the bilinear form -/

section PartC2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The fibre `{x ∈ 𝓘⁺ : x_{C} = c, x_V = v}`. -/
noncomputable def fib (G : OrientedGraph U) (C V : Finset U) (c v : U → F) : Finset (U → F) :=
  (injLabellings F G).filter (fun x => restr C x = c ∧ restr V x = v)

/-- `Θ₁`: the pairs `(a, b)` with `a ∉ C_x`, `b ∈ C_z`. -/
abbrev predOne (Cx Cz : Finset U) : U × U → Prop := fun e => e.1 ∉ Cx ∧ e.2 ∈ Cz

/-- `Θ₂`: the pairs `(a, b)` with `a ∈ C_x`, `b ∉ C_z`. -/
abbrev predTwo (Cx Cz : Finset U) : U × U → Prop := fun e => e.1 ∈ Cx ∧ e.2 ∉ Cz

/-- `Γ`: the pairs `(a, b)` with `a ∈ C_x`, `b ∈ C_z`. -/
abbrev predGam (Cx Cz : Finset U) : U × U → Prop := fun e => e.1 ∈ Cx ∧ e.2 ∈ Cz

/-- `𝖺(v) = ∑_{x : x_{C_x} = c, x_V = v} f(x) Θ₁(x, c')` (Step 2, in counting form). -/
noncomputable def alphaF (G : OrientedGraph U) (ς : U → U → ℤ) (P Fr : Finset (U × U))
    (V Cx Cz : Finset U) (f : (U → F) → ℝ) (c c' v : U → F) : ℝ :=
  ∑ x ∈ fib G Cx V c v, f x * groupKer ς P Fr (predOne Cx Cz) x c'

/-- `𝖻(w) = ∑_{x' : x'_{C_z} = c', x'_W = w} Θ₂(c, x') h(x')`. -/
noncomputable def betaF (G : OrientedGraph U) (ς : U → U → ℤ) (P Fr : Finset (U × U))
    (W Cx Cz : Finset U) (h : (U → F) → ℝ) (c c' w : U → F) : ℝ :=
  ∑ x' ∈ fib G Cz W c' w, groupKer ς P Fr (predTwo Cx Cz) c x' * h x'

omit [Fintype F] [DecidableEq F] [Fintype U] in
theorem restr_eq_iff {S : Finset U} {x c : U → F} (h : restr S x = c) {u : U} (hu : u ∈ S) :
    x u = c u := by
  rw [← h, restr_apply_of_mem hu]

theorem mem_fib {G : OrientedGraph U} {C V : Finset U} {c v x : U → F} :
    x ∈ fib G C V c v ↔ x ∈ injLabellings F G ∧ restr C x = c ∧ restr V x = v := by
  unfold fib
  rw [mem_filter]

/-- **Steps 1–2 of `lem:matching:extractionk`, counting form**: the bilinear form
`∑_{x, x' ∈ 𝓘⁺} f(x) K_𝒞(x, x') h(x')` is
`∑_{c, c'} Γ(c, c') ∑_{v, w} 𝖺_{c,c'}(v) 𝖶(v, w) 𝖻_{c,c'}(w)`, the sums over the labels `c` of
`C_x`, `c'` of `C_z` occurring in `𝓘⁺`, and over the injective tuples `v` on `V`, `w` on `W`. -/
theorem bilinear_decomp (G : OrientedGraph U) (ς : U → U → ℤ) (P Fr : Finset (U × U))
    (V W Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) (f h : (U → F) → ℝ) :
    ∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * classKer ς P Fr x x' * h x' =
      ∑ c ∈ (injLabellings F G).image (restr Cx), ∑ c' ∈ (injLabellings F G).image (restr Cz),
        groupKer ς P Fr (predGam Cx Cz) c c' *
          ∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
            alphaF G ς P Fr V Cx Cz f c c' v * rectKer ς P V W v w *
              betaF G ς P Fr W Cx Cz h c c' w := by
  set I := injLabellings F G
  set Ix := I.image (restr Cx)
  set Iz := I.image (restr Cz)
  set T : (U → F) → (U → F) → ℝ := fun x x' => f x * classKer ς P Fr x x' * h x' with hT
  have hx1 : ∀ x ∈ I, restr Cx x ∈ Ix := fun x hx => mem_image_of_mem _ hx
  have hx2 : ∀ x ∈ I, restr V x ∈ injTuples F V := fun x hx => restr_mem_injTuples G V hx
  have hz1 : ∀ x ∈ I, restr Cz x ∈ Iz := fun x hx => mem_image_of_mem _ hx
  have hz2 : ∀ x ∈ I, restr W x ∈ injTuples F W := fun x hx => restr_mem_injTuples G W hx
  -- the summand on the fibres
  have hfib : ∀ c c' v w x x', x ∈ fib G Cx V c v → x' ∈ fib G Cz W c' w →
      T x x' = groupKer ς P Fr (predGam Cx Cz) c c' *
        ((f x * groupKer ς P Fr (predOne Cx Cz) x c') * rectKer ς P V W v w *
          (groupKer ς P Fr (predTwo Cx Cz) c x' * h x')) := by
    intro c c' v w x x' hx hx'
    obtain ⟨-, hxc, hxv⟩ := mem_fib.mp hx
    obtain ⟨-, hxc', hxw⟩ := mem_fib.mp hx'
    simp only [hT]
    rw [classKer_eq_groups ς P Fr V W Cx Cz hVC hWC hP hFr x x']
    have e1 : rectKer ς P V W x x' = rectKer ς P V W v w :=
      rectKer_congr ς P V W (fun u hu => restr_eq_iff hxv hu) (fun u hu => restr_eq_iff hxw hu)
    have e2 : groupKer ς P Fr (predOne Cx Cz) x x' = groupKer ς P Fr (predOne Cx Cz) x c' :=
      groupKer_congr ς P Fr _ fun e he => ⟨rfl, restr_eq_iff hxc' he.2⟩
    have e3 : groupKer ς P Fr (predTwo Cx Cz) x x' = groupKer ς P Fr (predTwo Cx Cz) c x' :=
      groupKer_congr ς P Fr _ fun e he => ⟨restr_eq_iff hxc he.1, rfl⟩
    have e4 : groupKer ς P Fr (predGam Cx Cz) x x' = groupKer ς P Fr (predGam Cx Cz) c c' :=
      groupKer_congr ς P Fr _ fun e he => ⟨restr_eq_iff hxc he.1, restr_eq_iff hxc' he.2⟩
    rw [e1, e2, e3, e4]
    ring
  -- the right side, expanded
  have hR : ∑ c ∈ Ix, ∑ c' ∈ Iz, groupKer ς P Fr (predGam Cx Cz) c c' *
        ∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
          alphaF G ς P Fr V Cx Cz f c c' v * rectKer ς P V W v w *
            betaF G ς P Fr W Cx Cz h c c' w =
      ∑ c ∈ Ix, ∑ c' ∈ Iz, ∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
        ∑ x ∈ fib G Cx V c v, ∑ x' ∈ fib G Cz W c' w, T x x' := by
    refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun w _ => ?_
    unfold alphaF betaF
    rw [sum_mul, sum_mul, mul_sum]
    refine sum_congr rfl fun x hx => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun x' hx' => ?_
    rw [hfib c c' v w x x' hx hx']
  rw [hR]
  -- the left side, decomposed into fibres
  have hL : ∑ x ∈ I, ∑ x' ∈ I, T x x' =
      ∑ c ∈ Ix, ∑ v ∈ injTuples F V, ∑ x ∈ fib G Cx V c v,
        ∑ c' ∈ Iz, ∑ w ∈ injTuples F W, ∑ x' ∈ fib G Cz W c' w, T x x' := by
    rw [sum_fiber_two I (restr Cx) (restr V) Ix (injTuples F V) hx1 hx2]
    refine sum_congr rfl fun c _ => sum_congr rfl fun v _ => sum_congr rfl fun x _ => ?_
    exact sum_fiber_two I (restr Cz) (restr W) Iz (injTuples F W) hz1 hz2 _
  have hL' : ∑ x ∈ I, ∑ x' ∈ I, f x * classKer ς P Fr x x' * h x' =
      ∑ x ∈ I, ∑ x' ∈ I, T x x' := rfl
  rw [hL', hL]
  refine sum_congr rfl fun c _ => ?_
  calc ∑ v ∈ injTuples F V, ∑ x ∈ fib G Cx V c v,
        ∑ c' ∈ Iz, ∑ w ∈ injTuples F W, ∑ x' ∈ fib G Cz W c' w, T x x'
      = ∑ v ∈ injTuples F V, ∑ c' ∈ Iz, ∑ x ∈ fib G Cx V c v,
          ∑ w ∈ injTuples F W, ∑ x' ∈ fib G Cz W c' w, T x x' :=
        sum_congr rfl fun v _ => sum_comm
    _ = ∑ c' ∈ Iz, ∑ v ∈ injTuples F V, ∑ x ∈ fib G Cx V c v,
          ∑ w ∈ injTuples F W, ∑ x' ∈ fib G Cz W c' w, T x x' := sum_comm
    _ = _ := sum_congr rfl fun c' _ => sum_congr rfl fun v _ => sum_comm

open Sarkozy.Influence in
/-- **Steps 3–4 of `lem:matching:extractionk`, counting form**: with the kernel hypothesis
`‖𝖶‖ ≤ Λ` on injective tuples (`ℓ²` counting normalization; `Λ = c_ker √q^k` is the paper's
`c_ker r^k` for uniform probability) and Cauchy–Schwarz over `(c, c')` with the weights `|Γ|`,
`|∑ f K_𝒞 h| ≤ Λ (∑_{c,c'} |Γ| ‖𝖺_{c,c'}‖²)^{1/2} (∑_{c,c'} |Γ| ‖𝖻_{c,c'}‖²)^{1/2}`; the first
inequality of the proof is the counting form of `eq:extraction:step4`. -/
theorem bilinear_le (G : OrientedGraph U) (ς : U → U → ℤ) (P Fr : Finset (U × U))
    (V W Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hker : OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W) Λ)
    (f h : (U → F) → ℝ) :
    |∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * classKer ς P Fr x x' * h x'| ≤
      Λ * Real.sqrt (∑ c ∈ (injLabellings F G).image (restr Cx),
          ∑ c' ∈ (injLabellings F G).image (restr Cz),
            |groupKer ς P Fr (predGam Cx Cz) c c'| *
              ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2) *
        Real.sqrt (∑ c ∈ (injLabellings F G).image (restr Cx),
          ∑ c' ∈ (injLabellings F G).image (restr Cz),
            |groupKer ς P Fr (predGam Cx Cz) c c'| *
              ∑ w ∈ injTuples F W, betaF G ς P Fr W Cx Cz h c c' w ^ 2) := by
  rw [bilinear_decomp G ς P Fr V W Cx Cz hVC hWC hP hFr f h]
  set Ix := (injLabellings F G).image (restr Cx)
  set Iz := (injLabellings F G).image (restr Cz)
  set Γ := fun (c c' : U → F) => groupKer ς P Fr (predGam Cx Cz) c c'
  set na := fun (c c' : U → F) => Real.sqrt (∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2)
  set nb := fun (c c' : U → F) => Real.sqrt (∑ w ∈ injTuples F W, betaF G ς P Fr W Cx Cz h c c' w ^ 2)
  have hB : ∀ c c', |∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
      alphaF G ς P Fr V Cx Cz f c c' v * rectKer ς P V W v w *
        betaF G ς P Fr W Cx Cz h c c' w| ≤ Λ * (|na c c'| * |nb c c'|) := by
    intro c c'
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _), ← mul_assoc]
    exact opBound_bilinear hker hΛ _ _
  have hsq : ∀ c c', na c c' ^ 2 = ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2 :=
    fun c c' => Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hsq' : ∀ c c', nb c c' ^ 2 = ∑ w ∈ injTuples F W, betaF G ς P Fr W Cx Cz h c c' w ^ 2 :=
    fun c c' => Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  calc |∑ c ∈ Ix, ∑ c' ∈ Iz, Γ c c' * ∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
          alphaF G ς P Fr V Cx Cz f c c' v * rectKer ς P V W v w *
            betaF G ς P Fr W Cx Cz h c c' w|
      ≤ ∑ c ∈ Ix, ∑ c' ∈ Iz, |Γ c c'| * (Λ * (|na c c'| * |nb c c'|)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ => ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c' _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hB c c') (abs_nonneg _)
    _ = Λ * ∑ c ∈ Ix, ∑ c' ∈ Iz, |Γ c c'| * (|na c c'| * |nb c c'|) := by
        rw [mul_sum]
        refine sum_congr rfl fun c _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun c' _ => by ring
    _ ≤ Λ * (Real.sqrt (∑ c ∈ Ix, ∑ c' ∈ Iz, |Γ c c'| * na c c' ^ 2) *
          Real.sqrt (∑ c ∈ Ix, ∑ c' ∈ Iz, |Γ c c'| * nb c c' ^ 2)) :=
        mul_le_mul_of_nonneg_left (double_sum_cs Ix Iz (fun c c' => |Γ c c'|) na nb
          (fun _ _ => abs_nonneg _)) hΛ
    _ = _ := by
        simp only [hsq, hsq']
        ring

end PartC2


end Sarkozy.ExtractionK
