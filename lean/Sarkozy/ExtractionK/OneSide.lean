module

public import Sarkozy.ExtractionK.Decomposition
public import Sarkozy.ExtractionK.IntegratedVertex

@[expose] public section

/-!
# Grouped extraction, II: one side and the transposed side (`lem:matching:extractionk`)

`paper/sections/16_extraction.tex`, `lem:matching:extractionk`, Steps 5–8, counting form.

* `alpha_sq_le` (Steps 5–6): Cauchy–Schwarz in the integrated variables and the integrated
  vertex bound `eq:extraction:mbound` (`integrated_extSum_le`), with
  `κ^f ≤ κ_{C_z}(x, c')` (`kappaFixed_le_coverRowKappa`):
  `𝖺_{c,c'}(v)² ≤ 2^{f_V} ∏_{u ∈ U_x} q 2^{-t_u} num_u ∑_{fibre} f² Θ₁⁺ 2^{κ_{C_z}}`.
* `one_side_le` (Step 7): summing over `v`, `c` and `c'`, with `Θ₁⁺ Γ⁺ 2^{κ_{C_z}}` the integrand of
  the cover rows, summed over the labellings of `C_z` by `partLab_coverRows_le` (Steps 2–5 of
  `lem:extraction-rows`, without its marginal comparison, as in the paper):
  `∑_{c,c'} |Γ| ‖𝖺_{c,c'}‖² ≤ 2^{f_V} M_{U_x} M_{C_z} ∑ f²`.
* `other_side_le` (Step 8): the same for `𝖻`, by applying `one_side_le` to the transposed class
  `𝒞(Pᵀ, Aᵀ)` (`betaF_eq_alphaF_swap`, `gam_swap`, `groupKer_swap`; this uses the antisymmetry
  `ς_{kj} = -ς_{jk}` of `lem:spec:elementary`).

`intNumQ`, `coverNumQ` are `q 2^{-t_v}` times the numerators of the vertex factors `F_u`
(`u ∈ U_x`) and `F_b` (`b ∈ C_z`) of `def:extraction:records`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-! ## Part E: one side (Steps 5–7) -/

section PartE

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

variable (F) in
/-- `q 2^{-t_u}` times the numerator of `F_u` (integrated vertex `u ∈ U_x`, Step 6). -/
noncomputable def intNumQ (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (Cz : Finset U) (u : U) : ℝ :=
  (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u * intNum G ς (Fintype.card F) n ord Fr Cz u

variable (F) in
/-- `q 2^{-t_b}` times the numerator of `F_b` (cover vertex `b ∈ C`, Step 7,
`eq:extraction:onevertex`). -/
noncomputable def coverNumQ (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (C : Finset U)
    (ord : U → ℕ) (H : Finset (U × U)) (b : U) : ℝ :=
  (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
    (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n) +
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
        ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b)

omit [DecidableEq F] in
theorem intNumQ_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (Cz : Finset U) (u : U) : 0 ≤ intNumQ F G ς n ord Fr Cz u := by
  unfold intNumQ intNum
  have he := coarseError_nonneg (q := (Fintype.card F : ℝ)) (Nat.cast_nonneg n)
    (intS G ord Fr u)
  have : 0 ≤ (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ intS G ord Fr u *
      ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b :=
    mul_nonneg (by positivity) (sum_nonneg fun b _ => by positivity)
  exact mul_nonneg (by positivity) (by linarith)

omit [DecidableEq F] in
theorem coverNumQ_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (n : ℕ) (C : Finset U)
    (ord : U → ℕ) (H : Finset (U × U)) (b : U) : 0 ≤ coverNumQ F G ς n C ord H b := by
  unfold coverNumQ
  have he := coarseError_nonneg (q := (Fintype.card F : ℝ)) (by positivity : (0 : ℝ) ≤ 2 * n)
    (coverRowS G C ord H b)
  have : 0 ≤ (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
      ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b :=
    mul_nonneg (by positivity) (sum_nonneg fun b _ => by positivity)
  exact mul_nonneg (by positivity) (by linarith)

/-- Weighted Cauchy–Schwarz: `(∑ g |a|)² ≤ (∑ g)(∑ g a²)` for `g ≥ 0`. -/
theorem weighted_cs {ι : Type*} (s : Finset ι) (g a : ι → ℝ) (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, g i * |a i|) ^ 2 ≤ (∑ i ∈ s, g i) * ∑ i ∈ s, g i * a i ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (g i))
    (fun i => Real.sqrt (g i) * |a i|)
  have e1 : ∀ i ∈ s, Real.sqrt (g i) * (Real.sqrt (g i) * |a i|) = g i * |a i| := by
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hg i hi)]
  have e2 : ∀ i ∈ s, Real.sqrt (g i) ^ 2 = g i := fun i hi => Real.sq_sqrt (hg i hi)
  have e3 : ∀ i ∈ s, (Real.sqrt (g i) * |a i|) ^ 2 = g i * a i ^ 2 := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hg i hi), sq_abs]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at h
  exact h

omit [Fintype F] [DecidableEq F] [Fintype U] in
theorem restr_eq_restr_iff {S : Finset U} {x y : U → F} :
    restr S x = restr S y ↔ ∀ a ∈ S, x a = y a := by
  constructor
  · intro h a ha
    have := congrFun h a
    simpa [restr, ha] using this
  · intro h
    funext a
    by_cases ha : a ∈ S
    · simp [restr, ha, h a ha]
    · simp [restr, ha]

/-- The fibre of `(x₀_{C_x}, x₀_V)` is the set of `x ∈ 𝓘⁺` agreeing with `x₀` on `V ∪ C_x`. -/
theorem fib_eq_extensions (G : OrientedGraph U) (V Cx : Finset U) (x₀ : U → F) :
    fib G Cx V (restr Cx x₀) (restr V x₀) =
      (injLabellings F G).filter (fun y => ∀ a ∈ univ \ (univ \ (V ∪ Cx)), y a = x₀ a) := by
  unfold fib
  refine filter_congr fun y _ => ?_
  rw [restr_eq_restr_iff, restr_eq_restr_iff]
  simp only [mem_sdiff, mem_univ, true_and, not_not, mem_union]
  constructor
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact h2 a ha
    · exact h1 a ha
  · intro h
    exact ⟨fun a ha => h a (Or.inr ha), fun a ha => h a (Or.inl ha)⟩

/-- `Θ₁⁺ = Θ_V⁺ Θ_U⁺`: the free pairs of `𝒢₁` are those with `x`-endpoint in `V` or in `U_x`. -/
theorem groupPos_one_split (ς : U → U → ℤ) (Fr : Finset (U × U)) (V Cx Cz : Finset U)
    (hVC : ∀ u ∈ V, u ∉ Cx) (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz) (x c' : U → F) :
    groupPos ς Fr (predOne Cx Cz) x c' =
      (∏ e ∈ Fr.filter (fun e => e.1 ∈ V), (1 + chiPair ς e x c')) *
        ∏ e ∈ Fr.filter (fun e => e.1 ∈ univ \ (V ∪ Cx)), (1 + chiPair ς e x c') := by
  unfold groupPos
  rw [← prod_filter_mul_prod_filter_not (Fr.filter (predOne Cx Cz)) (fun e => e.1 ∈ V),
    filter_filter, filter_filter]
  congr 1
  · congr 1
    refine filter_congr fun e he => ?_
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨hVC e.1 h, hFr1 e he (hVC e.1 h)⟩, h⟩
  · congr 1
    refine filter_congr fun e he => ?_
    simp only [predOne, mem_sdiff, mem_univ, true_and, mem_union, not_or]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h3, h1⟩
    · rintro ⟨h3, h1⟩
      exact ⟨⟨h1, hFr1 e he h1⟩, h3⟩

omit [Fintype U] [DecidableEq U] in
theorem prod_free_le_two_pow (ς : U → U → ℤ) (S : Finset (U × U)) (x c' : U → F) :
    ∏ e ∈ S, (1 + chiPair ς e x c') ≤ 2 ^ S.card := by
  calc ∏ e ∈ S, (1 + chiPair ς e x c') ≤ ∏ _e ∈ S, (2 : ℝ) :=
        prod_le_prod₀ (fun e _ => one_add_chiPair_nonneg ς e x c')
          (fun e _ => one_add_chiPair_le_two ς e x c')
    _ = 2 ^ S.card := prod_const 2

/-- `Θ₁⁺ Γ⁺ = ∏_{(a,b) ∈ F, b ∈ C_z} (1 + χ_{ab})`, so `Θ₁⁺ Γ⁺ 2^{κ_{C_z}}` is the integrand of
the cover rows. -/
theorem groupPos_one_mul_gam (G : OrientedGraph U) (ς : U → U → ℤ) (Fr : Finset (U × U))
    (Cx Cz : Finset U) (x c' : U → F) :
    groupPos ς Fr (predOne Cx Cz) x c' * groupPos ς Fr (predGam Cx Cz) x c' *
        2 ^ coverRowKappa G ς Cz x c' =
      coverRowIntegrand G ς Cz (Fr.filter (fun e => e.2 ∈ Cz)) x c' := by
  unfold coverRowIntegrand groupPos
  congr 1
  rw [← prod_filter_mul_prod_filter_not (Fr.filter (fun e => e.2 ∈ Cz)) (fun e => e.1 ∈ Cx),
    filter_filter, filter_filter, mul_comm]
  congr 1
  · refine prod_congr (filter_congr fun e _ => ?_) fun e _ => rfl
    exact and_comm
  · refine prod_congr (filter_congr fun e _ => ?_) fun e _ => rfl
    exact and_comm

/-- **Steps 5–6 for one fibre** (`eq:extraction:mbound` with Cauchy–Schwarz):
`𝖺_{c,c'}(v)² ≤ 2^{f_V} ∏_{u ∈ U_x} q 2^{-t_u} num_u · ∑_{x : x_{C_x} = c, x_V = v}
f(x)² Θ₁⁺(x, c') 2^{κ_{C_z}(x, c')}`. -/
theorem alpha_sq_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (V Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz)
    (ordX : U → ℕ) (hordX : Function.Injective ordX)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (f : (U → F) → ℝ) (c c' v : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b) :
    alphaF G ς P Fr V Cx Cz f c c' v ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
        (∏ u ∈ univ \ (V ∪ Cx), intNumQ F G ς n ordX Fr Cz u) *
        ∑ x ∈ fib G Cx V c v, f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' *
          2 ^ coverRowKappa G ς Cz x c' := by
  set Ux := univ \ (V ∪ Cx) with hUx
  set MU := ∏ u ∈ Ux, intNumQ F G ς n ordX Fr Cz u
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set g : (U → F) → ℝ := fun x => groupPos ς Fr (predOne Cx Cz) x c' with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => groupPos_nonneg ς Fr _ x c'
  have hMU0 : 0 ≤ MU := prod_nonneg fun u _ => intNumQ_nonneg G ς n ordX Fr Cz u
  by_cases hne : (fib G Cx V c v).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hne
    unfold alphaF
    rw [hne, sum_empty, sum_empty]
    simp
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨hx₀I, hx₀c, hx₀v⟩ := mem_fib.mp hx₀
  have hfib : fib G Cx V c v = (injLabellings F G).filter
      (fun y => ∀ a ∈ univ \ Ux, y a = x₀ a) := by
    rw [← hx₀c, ← hx₀v]
    exact fib_eq_extensions G V Cx x₀
  have hx₀f : Feasible F G (univ \ Ux) x₀ := by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx₀I
    exact ⟨fun a _ b _ h => hx₀I.1 a (mem_univ _) b (mem_univ _) h,
      fun e he _ _ => hx₀I.2 e he (mem_univ _) (mem_univ _)⟩
  have hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz := fun e he h1 => hFr1 e he (by
    have := (mem_sdiff.mp h1).2
    simp only [mem_union, not_or] at this
    exact this.2)
  -- Step 6: the integrated vertices
  have hm := integrated_extSum_le (n := n) hW G ς hς Fr hFrς Ux Cz hH ordX hordX hsegX c' hc'
    x₀ hx₀f
  unfold coverRowExtSum at hm
  rw [← hfib] at hm
  -- `∑ Θ₁⁺ ≤ 2^{f_V} 2^{κ^f} M_U`
  have hsumg : ∑ x ∈ fib G Cx V c v, g x ≤ 2 ^ fV * (2 ^ kappaFixed G Fr Ux x₀ c' * MU) := by
    calc ∑ x ∈ fib G Cx V c v, g x
        ≤ ∑ x ∈ fib G Cx V c v, 2 ^ fV *
            ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c') := by
          refine sum_le_sum fun x _ => ?_
          simp only [hg]
          rw [groupPos_one_split ς Fr V Cx Cz hVC hFr1 x c']
          exact mul_le_mul_of_nonneg_right (prod_free_le_two_pow ς _ x c')
            (prod_nonneg fun e _ => one_add_chiPair_nonneg ς e x c')
      _ = 2 ^ fV * ∑ x ∈ fib G Cx V c v,
            ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c') := by rw [mul_sum]
      _ ≤ 2 ^ fV * (2 ^ kappaFixed G Fr Ux x₀ c' * MU) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
  -- Cauchy–Schwarz
  have hα : |alphaF G ς P Fr V Cx Cz f c c' v| ≤ ∑ x ∈ fib G Cx V c v, g x * |f x| := by
    unfold alphaF
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_groupKer_le ς P Fr _ x c') (abs_nonneg _)
  have hcs := weighted_cs (fib G Cx V c v) g f (fun x _ => hg0 x)
  have hκ : ∀ x ∈ fib G Cx V c v, kappaFixed G Fr Ux x₀ c' ≤ coverRowKappa G ς Cz x c' := by
    intro x hx
    rw [hfib, mem_filter] at hx
    rw [← kappaFixed_congr G Fr Ux (x := x) (y := x₀) (fun i hi => hx.2 i (by
      simp only [mem_sdiff, mem_univ, true_and]; exact hi)) c']
    exact kappaFixed_le_coverRowKappa G ς Fr hFrς Ux Cz hH x c'
  have hsum2 : (2 : ℝ) ^ kappaFixed G Fr Ux x₀ c' * ∑ x ∈ fib G Cx V c v, g x * f x ^ 2 ≤
      ∑ x ∈ fib G Cx V c v, f x ^ 2 * g x * 2 ^ coverRowKappa G ς Cz x c' := by
    rw [mul_sum]
    refine sum_le_sum fun x hx => ?_
    have h2 : (2 : ℝ) ^ kappaFixed G Fr Ux x₀ c' ≤ 2 ^ coverRowKappa G ς Cz x c' :=
      pow_le_pow_right₀ (by norm_num) (hκ x hx)
    have h0 : 0 ≤ g x * f x ^ 2 := mul_nonneg (hg0 x) (sq_nonneg _)
    calc (2 : ℝ) ^ kappaFixed G Fr Ux x₀ c' * (g x * f x ^ 2)
        ≤ 2 ^ coverRowKappa G ς Cz x c' * (g x * f x ^ 2) := mul_le_mul_of_nonneg_right h2 h0
      _ = _ := by ring
  have hS0 : 0 ≤ ∑ x ∈ fib G Cx V c v, g x * f x ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (hg0 x) (sq_nonneg _)
  calc alphaF G ς P Fr V Cx Cz f c c' v ^ 2
      = |alphaF G ς P Fr V Cx Cz f c c' v| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ x ∈ fib G Cx V c v, g x * |f x|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hα 2
    _ ≤ (∑ x ∈ fib G Cx V c v, g x) * ∑ x ∈ fib G Cx V c v, g x * f x ^ 2 := hcs
    _ ≤ (2 ^ fV * (2 ^ kappaFixed G Fr Ux x₀ c' * MU)) *
          ∑ x ∈ fib G Cx V c v, g x * f x ^ 2 := mul_le_mul_of_nonneg_right hsumg hS0
    _ = 2 ^ fV * MU * ((2 : ℝ) ^ kappaFixed G Fr Ux x₀ c' *
          ∑ x ∈ fib G Cx V c v, g x * f x ^ 2) := by ring
    _ ≤ 2 ^ fV * MU * ∑ x ∈ fib G Cx V c v, f x ^ 2 * g x * 2 ^ coverRowKappa G ς Cz x c' :=
        mul_le_mul_of_nonneg_left hsum2 (mul_nonneg (by positivity) hMU0)

/-- **One side of `lem:matching:extractionk` (Steps 5–7)**, counting form:
`∑_{c, c'} |Γ(c, c')| ‖𝖺_{c,c'}‖² ≤ 2^{f_V} ∏_{u ∈ U_x} q 2^{-t_u} num_u
∏_{b ∈ C_z} q 2^{-t_b} num_b ∑_{x ∈ 𝓘⁺} f(x)²`, where `num_u`, `num_b` are the numerators of the
vertex factors `F_u` (`u ∈ U_x`) and `F_b` (`b ∈ C_z`, with `H_b` all free pairs at `b`). The
cover labels `c'` are summed over the labellings of `C_z` without completions (Steps 2–5 of
`lem:extraction-rows`, `partLab_coverRows_le`). -/
theorem one_side_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (V Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Set.InjOn ordZ Cz)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (f : (U → F) → ℝ) :
    ∑ c ∈ (injLabellings F G).image (restr Cx), ∑ c' ∈ (injLabellings F G).image (restr Cz),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
        (∏ u ∈ univ \ (V ∪ Cx), intNumQ F G ς n ordX Fr Cz u) *
        (∏ b ∈ Cz, coverNumQ F G ς n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
        ∑ x ∈ injLabellings F G, f x ^ 2 := by
  set I := injLabellings F G
  set Ix := I.image (restr Cx)
  set Iz := I.image (restr Cz)
  set H := Fr.filter (fun e => e.2 ∈ Cz) with hHdef
  set K := 2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
    (∏ u ∈ univ \ (V ∪ Cx), intNumQ F G ς n ordX Fr Cz u) with hK
  set MC := ∏ b ∈ Cz, coverNumQ F G ς n Cz ordZ H b
  have hK0 : 0 ≤ K := mul_nonneg (by positivity)
    (prod_nonneg fun u _ => intNumQ_nonneg G ς n ordX Fr Cz u)
  set Prow : (U → F) → (U → F) → ℝ := fun x c' => coverRowIntegrand G ς Cz H x c' with hProw
  have hProw0 : ∀ x c', 0 ≤ Prow x c' := fun x c' => coverRowIntegrand_nonneg G ς Cz H x c'
  -- the cover labels are injective on `C_z`
  have hinjz : ∀ c' ∈ Iz, ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b := by
    intro c' hc' a ha b hb hab
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
    simp only [I, injLabellings, mem_filter, mem_univ, true_and] at hy
    rw [restr_apply_of_mem ha, restr_apply_of_mem hb] at hab
    exact hy.1 a (mem_univ _) b (mem_univ _) hab
  -- Steps 5–6 for each `(c, c')`, summed over `v`
  have hstep : ∀ c ∈ Ix, ∀ c' ∈ Iz,
      |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2 ≤
        K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' := by
    intro c _ c' hc'
    have hv : ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2 ≤
        K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 *
          groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c' := by
      calc ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2
          ≤ ∑ v ∈ injTuples F V, K * ∑ x ∈ fib G Cx V c v, f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c' :=
            sum_le_sum fun v _ => alpha_sq_le hW G ς hς n P Fr hFrς V Cx Cz hVC hFr1 ordX
              hordX hsegX f c c' v (hinjz c' hc')
        _ = K * ∑ v ∈ injTuples F V, ∑ x ∈ fib G Cx V c v, f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c' := by
            rw [mul_sum]
        _ = _ := by
            congr 1
            rw [← sum_fiberwise_of_maps_to (s := I.filter (fun x => restr Cx x = c))
              (g := restr V) (t := injTuples F V)
              (fun x hx => restr_mem_injTuples G V (mem_filter.mp hx).1)]
            refine sum_congr rfl fun v _ => ?_
            unfold fib
            rw [filter_filter]
    have hΓ : ∀ x ∈ I.filter (fun x => restr Cx x = c),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') ≤
          f x ^ 2 * Prow x c' := by
      intro x hx
      have hxc := (mem_filter.mp hx).2
      have hg : groupPos ς Fr (predGam Cx Cz) c c' = groupPos ς Fr (predGam Cx Cz) x c' :=
        groupPos_congr ς Fr _ fun e he => ⟨(restr_eq_iff hxc he.1).symm, rfl⟩
      have h1 := abs_groupKer_le ς P Fr (predGam Cx Cz) c c'
      rw [hg] at h1
      have h0 : 0 ≤ f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' *
          2 ^ coverRowKappa G ς Cz x c' :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (groupPos_nonneg ς Fr _ x c')) (by positivity)
      calc |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c')
          ≤ groupPos ς Fr (predGam Cx Cz) x c' *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') :=
            mul_le_mul_of_nonneg_right h1 h0
        _ = f x ^ 2 * (groupPos ς Fr (predOne Cx Cz) x c' *
              groupPos ς Fr (predGam Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') := by ring
        _ = f x ^ 2 * Prow x c' := by rw [groupPos_one_mul_gam]
    calc |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2
        ≤ |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') :=
          mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ = K * ∑ x ∈ I.filter (fun x => restr Cx x = c),
            |groupKer ς P Fr (predGam Cx Cz) c c'| * (f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' * 2 ^ coverRowKappa G ς Cz x c') := by
          rw [mul_sum, mul_sum, mul_sum]
          exact sum_congr rfl fun x _ => by ring
      _ ≤ K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' :=
          mul_le_mul_of_nonneg_left (sum_le_sum hΓ) hK0
  -- Step 7: the cover rows
  have hrow : ∀ x ∈ I, ∑ c' ∈ Iz, Prow x c' ≤ MC := by
    intro x hx
    have hxinj : Function.Injective x := by
      simp only [I, injLabellings, mem_filter, mem_univ, true_and] at hx
      exact fun a b h => hx.1 a (mem_univ _) b (mem_univ _) h
    calc ∑ c' ∈ Iz, Prow x c' ≤ ∑ c' ∈ partLab F G Cz, Prow x c' := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun c' _ _ => hProw0 x c'
          intro c' hc'
          obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
          exact restr_mem_partLab G Cz hy
      _ ≤ MC := partLab_coverRows_le hW G ς hς n Cz ordZ hordZ x hxinj H
          (fun e he => ⟨(mem_filter.mp he).2, hFrς e (mem_filter.mp he).1⟩)
  calc ∑ c ∈ Ix, ∑ c' ∈ Iz, |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, alphaF G ς P Fr V Cx Cz f c c' v ^ 2
      ≤ ∑ c ∈ Ix, ∑ c' ∈ Iz, K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' :=
        sum_le_sum fun c hc => sum_le_sum fun c' hc' => hstep c hc c' hc'
    _ = K * ∑ c' ∈ Iz, ∑ c ∈ Ix, ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun c' _ => ?_
        rw [mul_sum]
    _ = K * ∑ c' ∈ Iz, ∑ x ∈ I, f x ^ 2 * Prow x c' := by
        congr 1
        refine sum_congr rfl fun c' _ => ?_
        exact sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem _ hx) _
    _ = K * ∑ x ∈ I, f x ^ 2 * ∑ c' ∈ Iz, Prow x c' := by
        rw [sum_comm]
        congr 1
        exact sum_congr rfl fun x _ => by rw [mul_sum]
    _ ≤ K * ∑ x ∈ I, f x ^ 2 * MC :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun x hx =>
          mul_le_mul_of_nonneg_left (hrow x hx) (sq_nonneg _)) hK0
    _ = _ := by
        rw [← sum_mul]
        ring

end PartE

/-! ## Part F: the transposed class (Step 8) -/

section PartF

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] in
/-- Exchanging the two labellings: `∏_{e ∈ Pᵀ, p(e)} ψ_e(x', x) = ∏_{e ∈ P, p(eᵀ)} ψ_e(x, x')`
(`χ_{(b,a)}(x', x) = χ_{(a,b)}(x, x')` by `ς_{ba} = -ς_{ab}`, `lem:spec:elementary`). -/
theorem groupKer_swap (ς : U → U → ℤ) (hanti : ∀ j k, ς k j = -ς j k) (P Fr : Finset (U × U))
    (p : U × U → Prop) [DecidablePred p] (x x' : U → F) :
    groupKer ς (P.image Prod.swap) (Fr.image Prod.swap) p x' x =
      groupKer ς P Fr (fun e => p e.swap) x x' := by
  unfold groupKer
  rw [filter_image, filter_image, prod_image (fun a _ b _ h => Prod.swap_injective h),
    prod_image (fun a _ b _ h => Prod.swap_injective h)]
  simp only [chiPair_swap ς hanti]

omit [Fintype U] in
theorem card_filter_swap (Fr : Finset (U × U)) (W : Finset U) :
    ((Fr.image Prod.swap).filter (fun e => e.1 ∈ W)).card = (Fr.filter (fun e => e.2 ∈ W)).card := by
  rw [filter_image, card_image_of_injective _ Prod.swap_injective]
  rfl

/-- **Step 8**: the right factor `𝖻` of the class is the left factor `𝖺` of the transposed class
`𝒞(Pᵀ, Aᵀ)` (with `h` in place of `f`, the cover and the witness sets exchanged). -/
theorem betaF_eq_alphaF_swap (G : OrientedGraph U) (ς : U → U → ℤ)
    (hanti : ∀ j k, ς k j = -ς j k) (P Fr : Finset (U × U)) (W Cx Cz : Finset U)
    (h : (U → F) → ℝ) (c c' w : U → F) :
    betaF G ς P Fr W Cx Cz h c c' w =
      alphaF G ς (P.image Prod.swap) (Fr.image Prod.swap) W Cz Cx h c' c w := by
  unfold alphaF betaF
  refine sum_congr rfl fun x' _ => ?_
  rw [groupKer_swap ς hanti, mul_comm]
  congr 1
  unfold groupKer
  congr 2
  · exact filter_congr fun e _ => and_comm
  · exact filter_congr fun e _ => and_comm

omit [Fintype U] in
theorem gam_swap (ς : U → U → ℤ) (hanti : ∀ j k, ς k j = -ς j k) (P Fr : Finset (U × U))
    (Cx Cz : Finset U) (c c' : U → F) :
    groupKer ς (P.image Prod.swap) (Fr.image Prod.swap) (predGam Cz Cx) c' c =
      groupKer ς P Fr (predGam Cx Cz) c c' := by
  rw [groupKer_swap ς hanti]
  unfold groupKer
  congr 2
  · exact filter_congr fun e _ => and_comm
  · exact filter_congr fun e _ => and_comm

/-- **The other side (Step 8)**: `∑_{c, c'} |Γ| ‖𝖻_{c,c'}‖² ≤ 2^{f_W} ∏_{u ∈ U_z} q 2^{-t_u} num_u
∏_{a ∈ C_x} q 2^{-t_a} num_a ∑_{x' ∈ 𝓘⁺} h(x')²`, the factors being those of the transposed
record (`def:extraction:records` for `U_z` and `C_x`). -/
theorem other_side_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k) (n : ℕ)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (W Cx Cz : Finset U) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hFr2 : ∀ e ∈ Fr, e.2 ∉ Cz → e.1 ∈ Cx)
    (ordX ordZ : U → ℕ) (hordX : Set.InjOn ordX Cx) (hordZ : Function.Injective ordZ)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    (h : (U → F) → ℝ) :
    ∑ c ∈ (injLabellings F G).image (restr Cx), ∑ c' ∈ (injLabellings F G).image (restr Cz),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ w ∈ injTuples F W, betaF G ς P Fr W Cx Cz h c c' w ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.2 ∈ W)).card *
        (∏ u ∈ univ \ (W ∪ Cz), intNumQ F G ς n ordZ (Fr.image Prod.swap) Cx u) *
        (∏ b ∈ Cx, coverNumQ F G ς n Cx ordX
          ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b) *
        ∑ x ∈ injLabellings F G, h x ^ 2 := by
  have hT := one_side_le hW G ς hς n (P.image Prod.swap) (Fr.image Prod.swap)
    (fun e he => by
      obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
      simp only [Prod.fst_swap, Prod.snd_swap, hanti e₀.1 e₀.2, neg_ne_zero]
      exact hFrς e₀ he₀)
    W Cz Cx hWC
    (fun e he h1 => by
      obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
      exact hFr2 e₀ he₀ h1)
    ordZ ordX hordZ hordX hsegZ h
  rw [card_filter_swap] at hT
  refine le_trans (le_of_eq ?_) hT
  rw [sum_comm]
  refine sum_congr rfl fun c' _ => sum_congr rfl fun c _ => ?_
  rw [gam_swap ς hanti]
  congr 1
  exact sum_congr rfl fun w _ => by rw [betaF_eq_alphaF_swap G ς hanti]

end PartF


end Sarkozy.ExtractionK
