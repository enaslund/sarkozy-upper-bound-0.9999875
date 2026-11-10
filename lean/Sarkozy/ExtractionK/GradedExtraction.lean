module

public import Sarkozy.ExtractionK.GradedCounts

@[expose] public section

/-!
# Graded errors, II: `lem:matching:extractionk` for an error function

`paper/sections/16_extraction.tex`, `lem:matching:extractionk`, with the paragraph *Graded errors*
of `subsec:extraction:partition`: the theorem for an abstract error function `e` (`GrErr`,
`GradedCounts.lean`) and its graded instance.

* `gr_alpha_sq_le`, `gr_one_side_le`, `gr_other_side_le` (Steps 5–8), `gr_grouped_extraction_count`
  (counting form), `gr_grouped_extraction_sum_le` (normalized), `gr_grouped_extraction` (the class
  form, `grRecordFactor` the product of the vertex factors with `e`): the statements of
  `OneSide.lean` and `Grouped.lean` with `e` in place of `e_t(q, n')` (same proofs; the
  error-free steps — grouping, fibres, kernel step, Cauchy–Schwarz, transposition — are reused).
* **`gr_grouped_extraction_graded`**: `lem:matching:extractionk` with the graded error pair,
  `e^-_t(n') = (𝔈_t + 2^t n')/q` (`grGraded`), in the vertex factors and in `ê`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section GrOneSide

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

variable (F) in
/-- `q 2^{-t_u}` times the numerator of `F_u` (integrated vertex `u ∈ U_x`, Step 6), error
function `e`. -/
noncomputable def grIntNumQ (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (n : ℕ)
    (ord : U → ℕ)
    (Fr : Finset (U × U)) (Cz : Finset U) (u : U) : ℝ :=
  (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u * grIntNum G ς e (Fintype.card F) n ord Fr Cz u

variable (F) in
/-- `q 2^{-t_b}` times the numerator of `F_b` (cover vertex `b ∈ C`, Step 7,
`eq:extraction:onevertex`), error function `e`. -/
noncomputable def grCoverNumQ (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (n : ℕ)
    (C : Finset U)
    (ord : U → ℕ) (H : Finset (U × U)) (b : U) : ℝ :=
  (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
    (1 + e (coverRowS G C ord H b) (2 * n) +
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
        ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b)

omit [DecidableEq F] in
theorem gr_intNumQ_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (n : ℕ)
    (he : GrErr (Fintype.card F) n e) (ord : U → ℕ) (Fr : Finset (U × U)) (Cz : Finset U)
    (u : U) : 0 ≤ grIntNumQ F G ς e n ord Fr Cz u := by
  unfold grIntNumQ grIntNum
  have he0 := he.nonneg (intS G ord Fr u) n (Nat.cast_nonneg n)
  have : 0 ≤ (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ intS G ord Fr u *
      ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b :=
    mul_nonneg (by positivity) (sum_nonneg fun b _ => by positivity)
  exact mul_nonneg (by positivity) (by linarith)

omit [DecidableEq F] in
theorem gr_coverNumQ_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (n : ℕ)
    (he : GrErr (Fintype.card F) n e) (C : Finset U) (ord : U → ℕ) (H : Finset (U × U)) (b : U) :
    0 ≤ grCoverNumQ F G ς e n C ord H b := by
  unfold grCoverNumQ
  have he0 := he.nonneg (coverRowS G C ord H b) (2 * n) (by positivity)
  have : 0 ≤ (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
      ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b :=
    mul_nonneg (by positivity) (sum_nonneg fun b _ => by positivity)
  exact mul_nonneg (by positivity) (by linarith)


/-- **Steps 5–6 for one fibre** (`eq:extraction:mbound` with Cauchy–Schwarz):
`𝖺_{c,c'}(v)² ≤ 2^{f_V} ∏_{u ∈ U_x} q 2^{-t_u} num_u · ∑_{x : x_{C_x} = c, x_V = v}
f(x)² Θ₁⁺(x, c') 2^{κ_{C_z}(x, c')}`. -/
theorem gr_alpha_sq_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ) (e : ℕ → ℝ → ℝ)
    (he : GrErr (Fintype.card F) n e)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (V Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz)
    (ordX : U → ℕ) (hordX : Function.Injective ordX)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (f : (U → F) → ℝ) (c c' v : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b) :
    alphaF G ς P Fr V Cx Cz f c c' v ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
        (∏ u ∈ univ \ (V ∪ Cx), grIntNumQ F G ς e n ordX Fr Cz u) *
        ∑ x ∈ fib G Cx V c v, f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' *
          2 ^ coverRowKappa G ς Cz x c' := by
  set Ux := univ \ (V ∪ Cx) with hUx
  set MU := ∏ u ∈ Ux, grIntNumQ F G ς e n ordX Fr Cz u
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set g : (U → F) → ℝ := fun x => groupPos ς Fr (predOne Cx Cz) x c' with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => groupPos_nonneg ς Fr _ x c'
  have hMU0 : 0 ≤ MU := prod_nonneg fun u _ => gr_intNumQ_nonneg G ς e n he ordX Fr Cz u
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
  have hm := gr_integrated_extSum_le hW G ς hς n e he Fr hFrς Ux Cz hH ordX hordX hsegX c' hc'
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
theorem gr_one_side_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ) (e : ℕ → ℝ → ℝ)
    (he : GrErr (Fintype.card F) n e)
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
        (∏ u ∈ univ \ (V ∪ Cx), grIntNumQ F G ς e n ordX Fr Cz u) *
        (∏ b ∈ Cz, grCoverNumQ F G ς e n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
        ∑ x ∈ injLabellings F G, f x ^ 2 := by
  set I := injLabellings F G
  set Ix := I.image (restr Cx)
  set Iz := I.image (restr Cz)
  set H := Fr.filter (fun e => e.2 ∈ Cz) with hHdef
  set K := 2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
    (∏ u ∈ univ \ (V ∪ Cx), grIntNumQ F G ς e n ordX Fr Cz u) with hK
  set MC := ∏ b ∈ Cz, grCoverNumQ F G ς e n Cz ordZ H b
  have hK0 : 0 ≤ K := mul_nonneg (by positivity)
    (prod_nonneg fun u _ => gr_intNumQ_nonneg G ς e n he ordX Fr Cz u)
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
            sum_le_sum fun v _ => gr_alpha_sq_le hW G ς hς n e he P Fr hFrς V Cx Cz hVC hFr1 ordX
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
      _ ≤ MC := gr_partLab_coverRows_le hW G ς hς n e he Cz ordZ hordZ x hxinj H
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


/-- **The other side (Step 8)**: `∑_{c, c'} |Γ| ‖𝖻_{c,c'}‖² ≤ 2^{f_W} ∏_{u ∈ U_z} q 2^{-t_u} num_u
∏_{a ∈ C_x} q 2^{-t_a} num_a ∑_{x' ∈ 𝓘⁺} h(x')²`, the factors being those of the transposed
record (`def:extraction:records` for `U_z` and `C_x`). -/
theorem gr_other_side_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k) (n : ℕ)
    (e : ℕ → ℝ → ℝ) (he : GrErr (Fintype.card F) n e)
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
        (∏ u ∈ univ \ (W ∪ Cz), grIntNumQ F G ς e n ordZ (Fr.image Prod.swap) Cx u) *
        (∏ b ∈ Cx, grCoverNumQ F G ς e n Cx ordX
          ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b) *
        ∑ x ∈ injLabellings F G, h x ^ 2 := by
  have hT := gr_one_side_le hW G ς hς n e he (P.image Prod.swap) (Fr.image Prod.swap)
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


end GrOneSide

section GrGrouped

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **Steps 1–8, counting form**, for an error function `e` (*Graded errors*):
`|∑_{x, x' ∈ 𝓘⁺} f(x) K_𝒞(x, x') h(x')| ≤ Λ (2^{f_V} M_{U_x} M_{C_z} ∑ f²)^{1/2}
(2^{f_W} M_{U_z} M_{C_x} ∑ h²)^{1/2}`, where `M_Y` is the product over `Y` of `q 2^{-t_v}` times
the numerator of the vertex factor `F_v`. -/
theorem gr_grouped_extraction_count (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k) (n : ℕ)
    (e : ℕ → ℝ → ℝ) (he : GrErr (Fintype.card F) n e)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (V W Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W) Λ)
    (f h : (U → F) → ℝ) :
    |∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * classKer ς P Fr x x' * h x'| ≤
      Λ * Real.sqrt (2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
          (∏ u ∈ univ \ (V ∪ Cx), grIntNumQ F G ς e n ordX Fr Cz u) *
          (∏ b ∈ Cz, grCoverNumQ F G ς e n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
          ∑ x ∈ injLabellings F G, f x ^ 2) *
        Real.sqrt (2 ^ (Fr.filter (fun e => e.2 ∈ W)).card *
          (∏ u ∈ univ \ (W ∪ Cz), grIntNumQ F G ς e n ordZ (Fr.image Prod.swap) Cx u) *
          (∏ b ∈ Cx, grCoverNumQ F G ς e n Cx ordX
            ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b) *
          ∑ x ∈ injLabellings F G, h x ^ 2) := by
  refine (bilinear_le G ς P Fr V W Cx Cz hVC hWC hP hFr hΛ hker f h).trans ?_
  have h1 := gr_one_side_le hW G ς hς n e he P Fr hFrς V Cx Cz hVC
    (fun e he h1 => (hFr e he).resolve_left h1) ordX ordZ hordX hordZ.injOn hsegX f
  have h2 := gr_other_side_le hW G ς hς hanti n e he P Fr hFrς W Cx Cz hWC
    (fun e he h2 => (hFr e he).resolve_right h2) ordX ordZ hordX.injOn hordZ hsegZ h
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hΛ)
    (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) (mul_nonneg hΛ (Real.sqrt_nonneg _))


/-- The one-step lower count `ℓ_v = q 2^{-t_v} (1 - e_{t_v}(n))` of `lem:graphs:sequential`
along the order `ord`, for an error function `e`. -/
noncomputable def grStepLow (G : OrientedGraph U) (e : ℕ → ℝ → ℝ) (q : ℝ) (n : ℕ) (ord : U → ℕ)
    (v : U) : ℝ :=
  q * (2 : ℝ)⁻¹ ^ ordT G ord v * (1 - e (ordT G ord v) n)

theorem gr_err_ordT_le (G : OrientedGraph U) {e : ℕ → ℝ → ℝ} {q : ℝ} {n : ℕ} {ehat : ℝ}
    (he : GrErr q n e) (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (ord : U → ℕ) (v : U) :
    e (ordT G ord v) n ≤ ehat :=
  (he.mono n (Nat.cast_nonneg n) _ _ (ordT_le_deg G ord v)).trans (hehat v)

omit [DecidableEq F] in
/-- `F_u · ℓ_u = q 2^{-t_u} num_u` for an integrated vertex (error function `e`). -/
theorem gr_intNumQ_eq (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (n : ℕ)
    (ord : U → ℕ) (Fr : Finset (U × U)) (Cz : Finset U) (u : U) (he : e (ordT G ord u) n < 1) :
    grIntNumQ F G ς e n ord Fr Cz u =
      grIntF G ς e (Fintype.card F) n ord Fr Cz u * grStepLow G e (Fintype.card F) n ord u := by
  unfold grIntNumQ grIntF grStepLow
  have h1 : 1 - e (ordT G ord u) n ≠ 0 := by linarith
  field_simp

omit [DecidableEq F] in
/-- `F_b · ℓ_b = q 2^{-t_b} num_b` for a cover vertex (error function `e`). -/
theorem gr_coverNumQ_eq (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (n : ℕ)
    (C : Finset U) (ord : U → ℕ) (H : Finset (U × U)) (hseg : ∀ a ∈ C, ∀ b, b ∉ C → ord a < ord b)
    {b : U} (hb : b ∈ C) (he : e (ordT G ord b) n < 1) :
    grCoverNumQ F G ς e n C ord H b =
      grCoverF G ς e (Fintype.card F) n C ord H b * grStepLow G e (Fintype.card F) n ord b := by
  unfold grCoverNumQ grCoverF grStepLow
  rw [coverRowT_eq_ordT G C ord hseg hb]
  have h1 : 1 - e (ordT G ord b) n ≠ 0 := by linarith
  field_simp

/-- **`lem:matching:extractionk` (grouped extraction), sum form, for an error function `e`**
(*Graded errors*; `def:graphs:error-pair`). For a class with present
pairs `P`, free pairs `Fr`, witness sets `V`, `W` (`|V| = |W| = k`), a cover `(C_x, C_z)`
(`hP`, `hFr`: (VC_k), with no free pair in `V × W` by (W_k)) and orders of the two copies in
which `C_x` (`C_z`) comes first and `U_x` (`U_z`) last, if the rectangle kernel `𝖶` has norm at
most `c_ker √q^k` on injective tuples (`ℓ²` counting normalization; `c_ker r^k` for uniform
probability), then
`|E_{x,x' ∼ μ} f(x) K_𝒞(x, x') h(x')| ≤ c_ker r^k (2^{ex} ∏_v F_v)^{1/2} (1 - ê)^{-k} ‖f‖_μ ‖h‖_μ`,
`ex = t_V + t_W + f_V + f_W`, the product over the `2(n - k)` non-witness vertices
`U_x ⊔ C_z ⊔ U_z ⊔ C_x`. This is the paper's bound without the factor
`(R̃_{U_x} R̃_{U_z})^{1/2} ≥ 1` (`grouped_extraction_sum_le_paper` adds it). Here `E_μ` is
written as `|𝓘⁺|⁻¹ ∑_{𝓘⁺}`; `ê ≥ e_{d⁰_i}(q, n)` for all `i`, `ê < 1` (from (S1)). -/
theorem gr_grouped_extraction_sum_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k) {n : ℕ}
    (hn : Fintype.card U ≤ n) (e : ℕ → ℝ → ℝ) (he : GrErr (Fintype.card F) n e) {ehat : ℝ}
    (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1)
    (P Fr : Finset (U × U)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ}
    (V W Cx Cz : Finset U) (hVk : V.card = k) (hWk : W.card = k)
    (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hsegX : ∀ a, a ∉ univ \ (V ∪ Cx) → ∀ b ∈ univ \ (V ∪ Cx), ordX a < ordX b)
    (hsegZ : ∀ a, a ∉ univ \ (W ∪ Cz) → ∀ b ∈ univ \ (W ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(∑ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G, f x * classKer ς P Fr x x' * h x') /
        ((injLabellings F G).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, ordT G ordX v + ∑ v ∈ W, ordT G ordZ v) *
          ((∏ u ∈ univ \ (V ∪ Cx), grIntF G ς e (Fintype.card F) n ordX Fr Cz u) *
            (∏ b ∈ Cz, grCoverF G ς e (Fintype.card F) n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
            (∏ u ∈ univ \ (W ∪ Cz), grIntF G ς e (Fintype.card F) n ordZ (Fr.image Prod.swap) Cx u) *
            ∏ b ∈ Cx, grCoverF G ς e (Fintype.card F) n Cx ordX
              ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b)) /
        (1 - ehat) ^ k *
        Real.sqrt ((∑ x ∈ injLabellings F G, f x ^ 2) / (injLabellings F G).card) *
        Real.sqrt ((∑ x ∈ injLabellings F G, h x ^ 2) / (injLabellings F G).card) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  set I := injLabellings F G
  set N : ℝ := (I.card : ℝ)
  set Ux := univ \ (V ∪ Cx)
  set Uz := univ \ (W ∪ Cz)
  set H := Fr.filter (fun e => e.2 ∈ Cz)
  set HT := (Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set fW := (Fr.filter (fun e => e.2 ∈ W)).card
  set tV := ∑ v ∈ V, ordT G ordX v
  set tW := ∑ v ∈ W, ordT G ordZ v
  set ℓX := grStepLow G e q n ordX
  set ℓZ := grStepLow G e q n ordZ
  have he1 : ∀ ord v, e (ordT G ord v) n < 1 := fun ord v =>
    lt_of_le_of_lt (gr_err_ordT_le G he hehat ord v) hehat1
  have hℓpos : ∀ ord v, 0 < grStepLow G e q n ord v := fun ord v => by
    unfold grStepLow
    have := he1 ord v
    exact mul_pos (mul_pos hq0 (by positivity)) (by linarith)
  -- the counting bound
  have hΛ : 0 ≤ cker * Real.sqrt q ^ k := mul_nonneg hcker (by positivity)
  have hQ := gr_grouped_extraction_count hW G ς hς hanti n e he P Fr hFrς V W Cx Cz hVC hWC hP hFr ordX
    ordZ hordX hordZ hsegX hsegZ hΛ hker f h
  -- the lower counts
  have hLX : ∏ v, ℓX v ≤ N := by
    have := gr_card_injLabellings_ge hW G hn ordX hordX e he (fun v => (he1 ordX v).le)
    refine le_trans (le_of_eq ?_) this
    refine prod_congr rfl fun v _ => ?_
    simp only [ℓX, grStepLow, div_eq_mul_inv, inv_pow, hq]
  have hLZ : ∏ v, ℓZ v ≤ N := by
    have := gr_card_injLabellings_ge hW G hn ordZ hordZ e he (fun v => (he1 ordZ v).le)
    refine le_trans (le_of_eq ?_) this
    refine prod_congr rfl fun v _ => ?_
    simp only [ℓZ, grStepLow, div_eq_mul_inv, inv_pow, hq]
  have hLX0 : 0 < ∏ v, ℓX v := prod_pos fun v _ => hℓpos ordX v
  have hLZ0 : 0 < ∏ v, ℓZ v := prod_pos fun v _ => hℓpos ordZ v
  have hN0 : 0 < N := lt_of_lt_of_le hLX0 hLX
  -- the factor identities
  set PUx := ∏ u ∈ Ux, grIntF G ς e q n ordX Fr Cz u
  set PCz := ∏ b ∈ Cz, grCoverF G ς e q n Cz ordZ H b
  set PUz := ∏ u ∈ Uz, grIntF G ς e q n ordZ (Fr.image Prod.swap) Cx u
  set PCx := ∏ b ∈ Cx, grCoverF G ς e q n Cx ordX HT b
  have hMUx : ∏ u ∈ Ux, grIntNumQ F G ς e n ordX Fr Cz u = PUx * ∏ u ∈ Ux, ℓX u := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun u _ => gr_intNumQ_eq G ς e n ordX Fr Cz u (he1 ordX u)
  have hMUz : ∏ u ∈ Uz, grIntNumQ F G ς e n ordZ (Fr.image Prod.swap) Cx u =
      PUz * ∏ u ∈ Uz, ℓZ u := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun u _ => gr_intNumQ_eq G ς e n ordZ _ Cx u (he1 ordZ u)
  have hMCz : ∏ b ∈ Cz, grCoverNumQ F G ς e n Cz ordZ H b = PCz * ∏ b ∈ Cz, ℓZ b := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => gr_coverNumQ_eq G ς e n Cz ordZ H hZ0 hb (he1 ordZ b)
  have hMCx : ∏ b ∈ Cx, grCoverNumQ F G ς e n Cx ordX HT b = PCx * ∏ b ∈ Cx, ℓX b := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => gr_coverNumQ_eq G ς e n Cx ordX HT hX0 hb (he1 ordX b)
  rw [hMUx, hMCz, hMUz, hMCx] at hQ
  set A := (2 : ℝ) ^ fV * (PUx * ∏ u ∈ Ux, ℓX u) * (PCz * ∏ b ∈ Cz, ℓZ b)
  set B := (2 : ℝ) ^ fW * (PUz * ∏ u ∈ Uz, ℓZ u) * (PCx * ∏ b ∈ Cx, ℓX b)
  have hPF0 : ∀ ord Fr' Cz' u, 0 ≤ grIntF G ς e q n ord Fr' Cz' u := by
    intro ord Fr' Cz' u
    have h1 := gr_intNumQ_nonneg (F := F) G ς e n he ord Fr' Cz' u
    rw [gr_intNumQ_eq G ς e n ord Fr' Cz' u (he1 ord u)] at h1
    exact nonneg_of_mul_nonneg_left h1 (hℓpos ord u)
  have hcF0 : ∀ (C : Finset U) (ord : U → ℕ) (H' : Finset (U × U)),
      (∀ a ∈ C, ∀ b, b ∉ C → ord a < ord b) → ∀ b ∈ C, 0 ≤ grCoverF G ς e q n C ord H' b := by
    intro C ord H' hseg b hb
    have h1 := gr_coverNumQ_nonneg (F := F) G ς e n he C ord H' b
    rw [gr_coverNumQ_eq G ς e n C ord H' hseg hb (he1 ord b)] at h1
    exact nonneg_of_mul_nonneg_left h1 (hℓpos ord b)
  have hPUx0 : 0 ≤ PUx := prod_nonneg fun u _ => hPF0 _ _ _ u
  have hPUz0 : 0 ≤ PUz := prod_nonneg fun u _ => hPF0 _ _ _ u
  have hPCz0 : 0 ≤ PCz := prod_nonneg fun b hb => hcF0 Cz ordZ H hZ0 b hb
  have hPCx0 : 0 ≤ PCx := prod_nonneg fun b hb => hcF0 Cx ordX HT hX0 b hb
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUx0 (prod_nonneg fun u _ => (hℓpos ordX u).le)))
    (mul_nonneg hPCz0 (prod_nonneg fun u _ => (hℓpos ordZ u).le))
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUz0 (prod_nonneg fun u _ => (hℓpos ordZ u).le)))
    (mul_nonneg hPCx0 (prod_nonneg fun u _ => (hℓpos ordX u).le))
  have hnorm := normalize_le hN0 hLX0 hLZ0 hLX hLZ hA0 hB0
    (sum_nonneg fun x _ => sq_nonneg (f x)) (sum_nonneg fun x _ => sq_nonneg (h x)) hΛ hQ
  refine hnorm.trans ?_
  -- the witness factors
  set DV := ∏ v ∈ V, ℓX v
  set DW := ∏ v ∈ W, ℓZ v
  have hDV : q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k ≤ DV := by
    have : ∏ v ∈ V, (q * (2 : ℝ)⁻¹ ^ ordT G ordX v * (1 - ehat)) ≤ DV := by
      refine prod_le_prod₀ (fun v _ => ?_) (fun v _ => ?_)
      · exact mul_nonneg (mul_nonneg hq0.le (by positivity)) (by linarith)
      · simp only [ℓX, grStepLow]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hq0.le (by positivity))
        linarith [gr_err_ordT_le G he hehat ordX v]
    refine le_trans (le_of_eq ?_) this
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hVk, prod_pow_eq_pow_sum]
  have hDW : q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k ≤ DW := by
    have : ∏ v ∈ W, (q * (2 : ℝ)⁻¹ ^ ordT G ordZ v * (1 - ehat)) ≤ DW := by
      refine prod_le_prod₀ (fun v _ => ?_) (fun v _ => ?_)
      · exact mul_nonneg (mul_nonneg hq0.le (by positivity)) (by linarith)
      · simp only [ℓZ, grStepLow]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hq0.le (by positivity))
        linarith [gr_err_ordT_le G he hehat ordZ v]
    refine le_trans (le_of_eq ?_) this
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hWk, prod_pow_eq_pow_sum]
  have h1e : 0 < 1 - ehat := by linarith
  have hdV0 : 0 < q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k := by positivity
  have hdW0 : 0 < q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k := by positivity
  -- `A B = 2^{f_V + f_W} ∏ F · L_X L_Z / (D_V D_W)`
  set PF := PUx * PCz * PUz * PCx
  have hPF0 : 0 ≤ PF := mul_nonneg (mul_nonneg (mul_nonneg hPUx0 hPCz0) hPUz0) hPCx0
  have hsplitX : ∏ v, ℓX v = (∏ v ∈ Ux, ℓX v) * DV * ∏ v ∈ Cx, ℓX v :=
    prod_univ_three V Cx hVC ℓX
  have hsplitZ : ∏ v, ℓZ v = (∏ v ∈ Uz, ℓZ v) * DW * ∏ v ∈ Cz, ℓZ v :=
    prod_univ_three W Cz hWC ℓZ
  have hAB : A * B / ((∏ v, ℓX v) * ∏ v, ℓZ v) = 2 ^ fV * 2 ^ fW * PF / (DV * DW) := by
    rw [hsplitX, hsplitZ]
    have h1 : (0 : ℝ) < ∏ v ∈ Ux, ℓX v := prod_pos fun v _ => hℓpos ordX v
    have h2 : (0 : ℝ) < ∏ v ∈ Cx, ℓX v := prod_pos fun v _ => hℓpos ordX v
    have h3 : (0 : ℝ) < ∏ v ∈ Uz, ℓZ v := prod_pos fun v _ => hℓpos ordZ v
    have h4 : (0 : ℝ) < ∏ v ∈ Cz, ℓZ v := prod_pos fun v _ => hℓpos ordZ v
    have h5 : (0 : ℝ) < DV := prod_pos fun v _ => hℓpos ordX v
    have h6 : (0 : ℝ) < DW := prod_pos fun v _ => hℓpos ordZ v
    simp only [A, B, PF]
    field_simp
  rw [hAB]
  have hbound : 2 ^ fV * 2 ^ fW * PF / (DV * DW) ≤
      2 ^ fV * 2 ^ fW * PF / ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
        (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hdV0 hdW0)
      (mul_le_mul hDV hDW hdW0.le (lt_of_lt_of_le hdV0 hDV).le)
  have hinv : ((Real.sqrt q)⁻¹ ^ k) ^ 2 = (q ^ k)⁻¹ := by
    rw [inv_pow, inv_pow, sqrt_pow_sq hq0.le]
  have hsq : (cker * Real.sqrt q ^ k) ^ 2 *
      (2 ^ fV * 2 ^ fW * PF / ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
        (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k))) =
      (cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k) ^ 2 * (2 ^ (fV + fW + tV + tW) * PF) := by
    have e1 : (cker * Real.sqrt q ^ k) ^ 2 = cker ^ 2 * q ^ k := by
      rw [mul_pow, sqrt_pow_sq hq0.le]
    have e2 : (cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k) ^ 2 =
        cker ^ 2 * (q ^ k)⁻¹ / ((1 - ehat) ^ k) ^ 2 := by
      rw [div_pow, mul_pow, hinv]
    rw [e1, e2]
    simp only [pow_add, inv_pow]
    have hq' : (q ^ k) ≠ 0 := by positivity
    have he' : (1 - ehat) ^ k ≠ 0 := by positivity
    field_simp
  have hc' : 0 ≤ cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k := by positivity
  have hkey : cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF / (DV * DW)) ≤
      cker * (Real.sqrt q)⁻¹ ^ k * Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) / (1 - ehat) ^ k := by
    calc cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF / (DV * DW))
        ≤ cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF /
            ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
              (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k))) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbound) hΛ
      _ = Real.sqrt ((cker * Real.sqrt q ^ k) ^ 2 * (2 ^ fV * 2 ^ fW * PF /
            ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - ehat) ^ k) *
              (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - ehat) ^ k)))) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛ]
      _ = Real.sqrt ((cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k) ^ 2 *
            (2 ^ (fV + fW + tV + tW) * PF)) := by rw [hsq]
      _ = cker * (Real.sqrt q)⁻¹ ^ k / (1 - ehat) ^ k *
            Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc']
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)


/-- The product `∏_v F_v` of the `2(n - k)` vertex factors of a record, error function `e`
(`def:extraction:records`): `F_u` over `U_x` and `U_z`, `F_b` over `C_z` and `C_x`. The factors of
`U_z` and `C_x` are those of the transposed record (Step 8), i.e. with `H_u = {a : (a, u) ∈ F}`
and `H_a = {b : (a, b) ∈ F}`. -/
noncomputable def grRecordFactor (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (q : ℝ)
    (n : ℕ)
    (Fr : Finset (U × U)) (V W Cx Cz : Finset U) (ordX ordZ : U → ℕ) : ℝ :=
  (∏ u ∈ univ \ (V ∪ Cx), grIntF G ς e q n ordX Fr Cz u) *
    (∏ b ∈ Cz, grCoverF G ς e q n Cz ordZ (Fr.filter (fun e => e.2 ∈ Cz)) b) *
    (∏ u ∈ univ \ (W ∪ Cz), grIntF G ς e q n ordZ (Fr.image Prod.swap) Cx u) *
    ∏ b ∈ Cx, grCoverF G ς e q n Cx ordX ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) b


/-- **`lem:matching:extractionk` (Grouped extraction with a witness of size `k`), for an error
function `e`** (the paragraph *Graded errors*; `GrErr`, `def:graphs:error-pair`). Assume
`e(d⁰_i, n) ≤ ê < 1` for every vertex (from (S1) at `p`; `n ≥ |U⁺|`). Let `𝒞 = 𝒞(P, A)` be a
class of the cross pairs `E_× ⊇ Ex` with a record: a witness `w` of size `k` (`IsWitness`,
(W_k)), a cover `(C_x, C_z)` (`IsCover`, (VC_k)), and orders `ordX`, `ordZ` of the two copies
in which the cover comes first and the integrated set `U_x` (`U_z`) last (any order of `V`, `W`
in between). Suppose the kernel `𝖶` of the present rectangle pairs, compressed to injective
tuples, has `ℓ²` norm at most `c_ker √q^k` (`c_ker r^k` for uniform probability; by
`lem:matching:kernel`, `c_ker = 2^{β(𝒞)}`, see `KernelBridge.lean`). Then for all `f, h`
`|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex(𝒞)/2} (∏_v F_v)^{1/2} (1 - ê)^{-k} ‖f‖_μ ‖h‖_μ`.
This is the paper's bound without its factor `(R̃_{U_x} R̃_{U_z})^{1/2} ≥ 1`
(`grouped_extraction_paper` states it with that factor). The antisymmetry `ς_{kj} = -ς_{jk}`
(`lem:spec:elementary`) is used in Step 8 only. Literature input: `WeilBound F`. -/
theorem gr_grouped_extraction (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) (e : ℕ → ℝ → ℝ)
    (he : GrErr (Fintype.card F) n e) {ehat : ℝ}
    (hehat : ∀ i, e (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w)) (rectKer ς P (witV w) (witW w))
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          grRecordFactor G ς e (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
        (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨hP, -, hPA⟩ := hcls
  rw [classForm_eq G hne ς Ex P A hP hPA, coverRow_expect_graphLaw, coverRow_expect_graphLaw]
  set Fr := Ex \ (P ∪ A) with hFr
  have hrect : ∀ e : U × U, e.1 ∈ witV w ∧ e.2 ∈ witW w ↔
      (∃ i, (w i).1 = e.1) ∧ ∃ l, (w l).2 = e.2 := by
    intro e
    simp [witV, witW]
  have hFrEx : ∀ e ∈ Fr, e ∈ Ex := fun e he => (mem_sdiff.mp he).1
  have hP' : ∀ e ∈ P, (e.1 ∈ witV w ∧ e.2 ∈ witW w) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    by_cases hr : e.1 ∈ witV w ∧ e.2 ∈ witW w
    · exact Or.inl hr
    · exact Or.inr (hcov.cover e (mem_union_left _ he) (by rwa [← hrect]))
  have hFr' : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (hFrEx e he) hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hVC : ∀ u ∈ witV w, u ∉ Cx := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.fst_not_mem i
  have hWC : ∀ u ∈ witW w, u ∉ Cz := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.snd_not_mem i
  have hVk : (witV w).card = k := by
    unfold witV
    rw [card_image_of_injective _ hw.injective_fst, card_univ, Fintype.card_fin]
  have hWk : (witW w).card = k := by
    unfold witW
    rw [card_image_of_injective _ hw.injective_snd, card_univ, Fintype.card_fin]
  exact gr_grouped_extraction_sum_le hW G ς hς hanti hn e he hehat hehat1 P Fr
    (fun e he => hEx e (hFrEx e he)) (witV w) (witW w) Cx Cz hVk hWk hVC hWC hP' hFr' ordX ordZ
    hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker f h


end GrGrouped


section GrGradedMain

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`lem:matching:extractionk` with the graded error pair** (the paragraph *Graded errors* of
`subsec:extraction:partition`; `def:graphs:error-pair`, `eq:graphs:graded`): the bound of
`grouped_extraction` with every count error `e_t(p, n')` replaced by the graded error
`e^-_t(n') = (𝔈_t + 2^t n')/q` (`grGraded`) — in the vertex factors `F_u`, `F_b`
(`grRecordFactor`) and in `ê ≥ e^-_{d⁰_i}(n)`. Literature input: `WeilBound F`. -/
theorem gr_grouped_extraction_graded (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, grGraded (Fintype.card F) (rowsDeg0 G i) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w)) (rectKer ς P (witV w) (witW w))
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          grRecordFactor G ς (grGraded (Fintype.card F)) (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
        (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := gr_grouped_extraction hW G ς hς hanti hne hn (grGraded (Fintype.card F))
    (grErr_graded (by exact_mod_cast Fintype.card_pos) n) hehat hehat1 Ex P A hEx hcls w hw Cx Cz
    hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker f h

end GrGradedMain

end Sarkozy.ExtractionK
