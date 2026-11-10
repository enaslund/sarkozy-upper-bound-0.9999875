module

public import Sarkozy.ExtractionK.Grouped
public import Sarkozy.ExtractionK.PinnedCollision

@[expose] public section

/-!
# Pinned compressed classes, I: the class bound (`prop:pinned-extraction`)

`paper/sections/16_extraction.tex`, `subsec:push:pinnedremainder` and `prop:pinned-extraction`
("We follow the proof of `lem:matching:extractionk` … only the counts change"), in the counting
form of `Grouped.lean`. The setting is that of `PinnedCollision.lean`: `n` coordinates, the fixed
labels `𝓜` (`z = |𝓜|`), pins `pin j β ∈ {0, ±1}` with roots in `𝓜` (`ϖ_j = pinCount pin j ≤ ϖ`),
the pinned law `μ` uniform on `𝓘_pin = pinLab M pin` on both rows, cross signs
`ς ∈ {0, ±1}` with `E_× = {ς ≠ 0}` not necessarily symmetric, `e^pin_d = ePin q n z d`.

* `pe_bilinear_decomp`, `pe_bilinear_le`: Steps 1–4 for any finite set of injective labellings
  (copies of `bilinear_decomp`, `bilinear_le` with `peFib`, `peAlpha`, `peBeta`).
* `pe_one_le`: one pinned coordinate. A label meets its pins (roots in `𝓜`) and cross roots that
  avoid `𝓜`, so no root merges (and there are no internal edges): the values outside the set `𝒮`
  of special values are counted by `lem:extraction-merged-count`, the special values have weight
  at most `2^h`. `pe_sum_prod_le`: dropping injectivity.
* `pe_integrated_le` (Step 6) and `pe_coverRows_le` (Step 7): the integrated vertices and the cover
  rows cost `peNum = q 2^{-ϖ_v}(1 + e_{ϖ_v+h_v}(q, 2n + z)) + n 2^{h_v}` each (at most `n` special
  values: the labels of the other row).
* `pe_one_side_le`, `pe_other_side_le` (Step 8 for the transposed class, signs `pinSwap ς`, the
  support `{(j, i)}`; no symmetry is used), `pe_class_count`.
* `pe_class_sum_le`: the class bound
  `|E_{x,y∼μ} f(x) K_𝒞(x, y) h(y)| ≤ c_ker r^k (2^{f_V + f_W + ϖ_V + ϖ_W} ∏_v F^pin_v)^{1/2}
  (1 - e^pin_ϖ)^{-k} ‖f‖_μ ‖h‖_μ` (`peFactor`, `peF`), from the lower count
  `|𝓘_pin| ≥ ∏_j q 2^{-ϖ_j}(1 - e^pin_ϖ)` (`card_pinLab_ge`) on each side.

## Deviations from the paper

* The counting route needs no density bound `D_V` and no completion ratio `R_pin` (as for
  `grouped_extraction`); the witness labels contribute `2^{ϖ_v}` each through the lower count.
* The upper bounds drop injectivity (sums over the products of the allowed sets).
* A general finite field `F` with `WeilBound F` (Weil's theorem, `thm:weil`(a)).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-! ## The decomposition for a finite set of injective labellings -/

section PeDecomp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

theorem pe_restr_mem_injTuples (V : Finset U) {y : U → F} (hy : Function.Injective y) :
    restr V y ∈ injTuples F V := by
  rw [mem_injTuples]
  refine ⟨fun u hu => ?_, fun a ha b hb h => ?_⟩
  · simp [restr, hu]
  · rw [restr_apply_of_mem ha, restr_apply_of_mem hb] at h
    exact hy h

/-- The fibre `{x ∈ I : x_C = c, x_V = v}` of a finite set `I` of labellings. -/
noncomputable def peFib (I : Finset (U → F)) (C V : Finset U) (c v : U → F) : Finset (U → F) :=
  I.filter (fun x => restr C x = c ∧ restr V x = v)

/-- `𝖺(v)` for the labellings `I` (`alphaF` with `I` in place of `Inj_p(G⁺)`). -/
noncomputable def peAlpha (I : Finset (U → F)) (ς : U → U → ℤ) (P Fr : Finset (U × U))
    (V Cx Cz : Finset U) (f : (U → F) → ℝ) (c c' v : U → F) : ℝ :=
  ∑ x ∈ peFib I Cx V c v, f x * groupKer ς P Fr (predOne Cx Cz) x c'

/-- `𝖻(w)` for the labellings `I`. -/
noncomputable def peBeta (I : Finset (U → F)) (ς : U → U → ℤ) (P Fr : Finset (U × U))
    (W Cx Cz : Finset U) (h : (U → F) → ℝ) (c c' w : U → F) : ℝ :=
  ∑ x' ∈ peFib I Cz W c' w, groupKer ς P Fr (predTwo Cx Cz) c x' * h x'

omit [Fintype F] in
theorem mem_peFib {I : Finset (U → F)} {C V : Finset U} {c v x : U → F} :
    x ∈ peFib I C V c v ↔ x ∈ I ∧ restr C x = c ∧ restr V x = v := by
  unfold peFib
  rw [mem_filter]

/-- `bilinear_decomp` for a finite set `I` of injective labellings (Steps 1–2 of
`lem:matching:extractionk`, used for the pinned law of `prop:pinned-extraction`). -/
theorem pe_bilinear_decomp (I : Finset (U → F)) (hI : ∀ x ∈ I, Function.Injective x)
    (ς : U → U → ℤ) (P Fr : Finset (U × U))
    (V W Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) (f h : (U → F) → ℝ) :
    ∑ x ∈ I, ∑ x' ∈ I, f x * classKer ς P Fr x x' * h x' =
      ∑ c ∈ I.image (restr Cx), ∑ c' ∈ I.image (restr Cz),
        groupKer ς P Fr (predGam Cx Cz) c c' *
          ∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
            peAlpha I ς P Fr V Cx Cz f c c' v * rectKer ς P V W v w *
              peBeta I ς P Fr W Cx Cz h c c' w := by
  set Ix := I.image (restr Cx)
  set Iz := I.image (restr Cz)
  set T : (U → F) → (U → F) → ℝ := fun x x' => f x * classKer ς P Fr x x' * h x' with hT
  have hx1 : ∀ x ∈ I, restr Cx x ∈ Ix := fun x hx => mem_image_of_mem _ hx
  have hx2 : ∀ x ∈ I, restr V x ∈ injTuples F V := fun x hx => pe_restr_mem_injTuples V (hI x hx)
  have hz1 : ∀ x ∈ I, restr Cz x ∈ Iz := fun x hx => mem_image_of_mem _ hx
  have hz2 : ∀ x ∈ I, restr W x ∈ injTuples F W := fun x hx => pe_restr_mem_injTuples W (hI x hx)
  have hfib : ∀ c c' v w x x', x ∈ peFib I Cx V c v → x' ∈ peFib I Cz W c' w →
      T x x' = groupKer ς P Fr (predGam Cx Cz) c c' *
        ((f x * groupKer ς P Fr (predOne Cx Cz) x c') * rectKer ς P V W v w *
          (groupKer ς P Fr (predTwo Cx Cz) c x' * h x')) := by
    intro c c' v w x x' hx hx'
    obtain ⟨-, hxc, hxv⟩ := mem_peFib.mp hx
    obtain ⟨-, hxc', hxw⟩ := mem_peFib.mp hx'
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
  have hR : ∑ c ∈ Ix, ∑ c' ∈ Iz, groupKer ς P Fr (predGam Cx Cz) c c' *
        ∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
          peAlpha I ς P Fr V Cx Cz f c c' v * rectKer ς P V W v w *
            peBeta I ς P Fr W Cx Cz h c c' w =
      ∑ c ∈ Ix, ∑ c' ∈ Iz, ∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
        ∑ x ∈ peFib I Cx V c v, ∑ x' ∈ peFib I Cz W c' w, T x x' := by
    refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun w _ => ?_
    unfold peAlpha peBeta
    rw [sum_mul, sum_mul, mul_sum]
    refine sum_congr rfl fun x hx => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun x' hx' => ?_
    rw [hfib c c' v w x x' hx hx']
  rw [hR]
  have hL : ∑ x ∈ I, ∑ x' ∈ I, T x x' =
      ∑ c ∈ Ix, ∑ v ∈ injTuples F V, ∑ x ∈ peFib I Cx V c v,
        ∑ c' ∈ Iz, ∑ w ∈ injTuples F W, ∑ x' ∈ peFib I Cz W c' w, T x x' := by
    rw [sum_fiber_two I (restr Cx) (restr V) Ix (injTuples F V) hx1 hx2]
    refine sum_congr rfl fun c _ => sum_congr rfl fun v _ => sum_congr rfl fun x _ => ?_
    exact sum_fiber_two I (restr Cz) (restr W) Iz (injTuples F W) hz1 hz2 _
  have hL' : ∑ x ∈ I, ∑ x' ∈ I, f x * classKer ς P Fr x x' * h x' =
      ∑ x ∈ I, ∑ x' ∈ I, T x x' := rfl
  rw [hL', hL]
  refine sum_congr rfl fun c _ => ?_
  calc ∑ v ∈ injTuples F V, ∑ x ∈ peFib I Cx V c v,
        ∑ c' ∈ Iz, ∑ w ∈ injTuples F W, ∑ x' ∈ peFib I Cz W c' w, T x x'
      = ∑ v ∈ injTuples F V, ∑ c' ∈ Iz, ∑ x ∈ peFib I Cx V c v,
          ∑ w ∈ injTuples F W, ∑ x' ∈ peFib I Cz W c' w, T x x' :=
        sum_congr rfl fun v _ => sum_comm
    _ = ∑ c' ∈ Iz, ∑ v ∈ injTuples F V, ∑ x ∈ peFib I Cx V c v,
          ∑ w ∈ injTuples F W, ∑ x' ∈ peFib I Cz W c' w, T x x' := sum_comm
    _ = _ := sum_congr rfl fun c' _ => sum_congr rfl fun v _ => sum_comm

/-- `bilinear_le` for a finite set `I` of injective labellings (Steps 3–4). -/
theorem pe_bilinear_le (I : Finset (U → F)) (hI : ∀ x ∈ I, Function.Injective x)
    (ς : U → U → ℤ) (P Fr : Finset (U × U))
    (V W Cx Cz : Finset U) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W) Λ)
    (f h : (U → F) → ℝ) :
    |∑ x ∈ I, ∑ x' ∈ I, f x * classKer ς P Fr x x' * h x'| ≤
      Λ * Real.sqrt (∑ c ∈ I.image (restr Cx), ∑ c' ∈ I.image (restr Cz),
            |groupKer ς P Fr (predGam Cx Cz) c c'| *
              ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2) *
        Real.sqrt (∑ c ∈ I.image (restr Cx), ∑ c' ∈ I.image (restr Cz),
            |groupKer ς P Fr (predGam Cx Cz) c c'| *
              ∑ w ∈ injTuples F W, peBeta I ς P Fr W Cx Cz h c c' w ^ 2) := by
  rw [pe_bilinear_decomp I hI ς P Fr V W Cx Cz hVC hWC hP hFr f h]
  set Ix := I.image (restr Cx)
  set Iz := I.image (restr Cz)
  set Γ := fun (c c' : U → F) => groupKer ς P Fr (predGam Cx Cz) c c'
  set na := fun (c c' : U → F) =>
    Real.sqrt (∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2)
  set nb := fun (c c' : U → F) =>
    Real.sqrt (∑ w ∈ injTuples F W, peBeta I ς P Fr W Cx Cz h c c' w ^ 2)
  have hB : ∀ c c', |∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
      peAlpha I ς P Fr V Cx Cz f c c' v * rectKer ς P V W v w *
        peBeta I ς P Fr W Cx Cz h c c' w| ≤ Λ * (|na c c'| * |nb c c'|) := by
    intro c c'
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _), ← mul_assoc]
    exact opBound_bilinear hker hΛ _ _
  have hsq : ∀ c c', na c c' ^ 2 = ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2 :=
    fun c c' => Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hsq' : ∀ c c', nb c c' ^ 2 = ∑ w ∈ injTuples F W, peBeta I ς P Fr W Cx Cz h c c' w ^ 2 :=
    fun c c' => Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  calc |∑ c ∈ Ix, ∑ c' ∈ Iz, Γ c c' * ∑ v ∈ injTuples F V, ∑ w ∈ injTuples F W,
          peAlpha I ς P Fr V Cx Cz f c c' v * rectKer ς P V W v w *
            peBeta I ς P Fr W Cx Cz h c c' w|
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

end PeDecomp

/-! ## One coordinate of a pinned row -/

section PeOne

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem pe_factor_bounds (s' : ℤ) (hs' : s' = 1 ∨ s' = -1) (a : F) :
    0 ≤ (1 : ℝ) + s' * quadraticChar F a ∧ (1 : ℝ) + s' * quadraticChar F a ≤ 2 := by
  have hχ : quadraticChar F a = 0 ∨ quadraticChar F a = 1 ∨ quadraticChar F a = -1 := by
    rcases eq_or_ne a 0 with h | h
    · left; simp [h]
    · right; exact quadraticChar_dichotomy h
  rcases hs' with rfl | rfl <;> rcases hχ with h | h | h <;> rw [h] <;> norm_num

/-- **One pinned coordinate** (Steps 6–7 of `prop:pinned-extraction`): a label `t` of
coordinate `j` meets its pins (roots in `𝓜`) and cross roots `γ_l` (which avoid `𝓜`, so no
root merges); the values outside `𝒮 ⊇ {γ_l}` are counted by `lem:extraction-merged-count`, the
values in `𝒮` have weight at most `2^h`:
`∑_{t allowed} ∏_l (1 + s'_l χ(t - γ_l)) ≤ q 2^{-ϖ_j}(1 + e_{ϖ_j + h}(q, 2n + z)) + |𝒮| 2^h`. -/
theorem pe_one_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (j : Fin n)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (γ : κ → F) (hγ : Function.Injective γ)
    (hγM : ∀ l, γ l ∉ M) (s' : κ → ℤ) (hs' : ∀ l, s' l = 1 ∨ s' l = -1)
    (𝒮 : Finset F) (h𝒮 : ∀ l, γ l ∈ 𝒮) :
    ∑ t ∈ pinAllowed M pin j, ∏ l, ((1 : ℝ) + s' l * quadraticChar F (t - γ l)) ≤
      (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin j *
        (1 + coarseError (pinCount pin j + Fintype.card κ) (Fintype.card F) (2 * n + M.card)) +
      𝒮.card * 2 ^ Fintype.card κ := by
  rw [← sum_filter_add_sum_filter_not (pinAllowed M pin j) (fun t => t ∈ 𝒮), add_comm]
  refine add_le_add ?_ ?_
  · -- the values outside `𝒮`
    set ι := ↥(pinRoots pin j)
    let β : ι → F := fun b => b.1
    have hβ : Function.Injective β := fun a b h => Subtype.ext h
    have hpm : ∀ b : ι, pin j b.1 = 1 ∨ pin j b.1 = -1 := by
      intro b
      have hb : pin j b.1 ≠ 0 := (mem_filter.mp b.2).2
      rcases hpin j b.1 with h | h | h
      · exact absurd h hb
      · exact Or.inl h
      · exact Or.inr h
    let s : ι → ℤ := fun b => quadraticChar F (pin j b.1 : F)
    have hs : ∀ b, s b = 1 ∨ s b = -1 := fun b => pin_char_pm (hpm b)
    set 𝒳 : Finset F := M ∪ 𝒮 with h𝒳
    have hβX : ∀ b, β b ∈ 𝒳 := fun b => mem_union_left _ (hpinM j b.1 (mem_filter.mp b.2).2)
    have hγX : ∀ l, γ l ∈ 𝒳 := fun l => mem_union_right _ (h𝒮 l)
    have hmc := merged_count_le_fintype hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX
      (n' := 2 * (n : ℝ) + M.card) (by positivity)
    have hm0 : mergedCount β γ = 0 := by
      unfold mergedCount
      rw [card_eq_zero, filter_eq_empty_iff]
      intro il _ h
      have h1 : β il.1 ∈ M := hpinM j il.1.1 (mem_filter.mp il.1.2).2
      exact hγM il.2 (h ▸ h1)
    have hcι : Fintype.card ι = pinCount pin j := Fintype.card_coe _
    rw [hm0, hcι, Nat.sub_zero, pow_zero, mul_one] at hmc
    have hset : (pinAllowed M pin j).filter (fun t => t ∉ 𝒮) =
        univ.filter (fun y => y ∉ 𝒳 ∧ ∀ b, quadraticChar F (y - β b) = s b) := by
      ext t
      simp only [pinAllowed, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
      constructor
      · rintro ⟨⟨htM, hpins⟩, htS⟩
        refine ⟨⟨htM, htS⟩, fun b => ?_⟩
        exact (pin_cond_iff (hpm b) _).mp (hpins b.1 (mem_filter.mp b.2).2)
      · rintro ⟨⟨htM, htS⟩, hall⟩
        refine ⟨⟨htM, fun b hb => ?_⟩, htS⟩
        have hbm : b ∈ pinRoots pin j := mem_filter.mpr ⟨mem_univ _, hb⟩
        exact (pin_cond_iff (hpm ⟨b, hbm⟩) _).mpr (hall ⟨b, hbm⟩)
    rw [hset]
    exact hmc
  · -- the values in `𝒮`
    calc ∑ t ∈ (pinAllowed M pin j).filter (fun t => t ∈ 𝒮),
          ∏ l, ((1 : ℝ) + s' l * quadraticChar F (t - γ l))
        ≤ ∑ _t ∈ 𝒮, (2 : ℝ) ^ Fintype.card κ := by
          refine sum_le_sum_of_subset_of_nonneg (fun t ht => (mem_filter.mp ht).2)
            (fun t _ _ => prod_nonneg fun l _ => (pe_factor_bounds _ (hs' l) _).1) |>.trans ?_
          refine sum_le_sum fun t _ => ?_
          calc ∏ l, ((1 : ℝ) + s' l * quadraticChar F (t - γ l)) ≤ ∏ _l : κ, (2 : ℝ) :=
                prod_le_prod₀ (fun l _ => (pe_factor_bounds _ (hs' l) _).1)
                  (fun l _ => (pe_factor_bounds _ (hs' l) _).2)
            _ = 2 ^ Fintype.card κ := by rw [prod_const, card_univ]
      _ = 𝒮.card * 2 ^ Fintype.card κ := by rw [sum_const, nsmul_eq_mul]

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Dropping injectivity: a sum over a set of labellings with coordinates in `T i` of a product
of nonnegative coordinate weights is at most the product of the coordinate sums. -/
theorem pe_sum_prod_le {n : ℕ} (Φ : Finset (Fin n → F)) (T : Fin n → Finset F)
    (hΦ : ∀ x ∈ Φ, ∀ i, x i ∈ T i) (g : Fin n → F → ℝ) (hg : ∀ i t, 0 ≤ g i t) :
    ∑ x ∈ Φ, ∏ i, g i (x i) ≤ ∏ i, ∑ t ∈ T i, g i t := by
  rw [prod_univ_sum]
  refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ =>
    prod_nonneg fun i _ => hg i _
  rw [Fintype.mem_piFinset]
  exact hΦ x hx

end PeOne

/-! ## One side of a pinned class (Steps 5–7) -/

section PeSide

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `q 2^{-ϖ_j}(1 + e_{ϖ_j + h}(q, 2n + z)) + n 2^h`: `q 2^{-ϖ_j}` times the numerator of the
pinned vertex factor of a vertex with `ϖ_j` pins and `h` free pairs (`prop:pinned-extraction`,
Steps 6–7; at most `n` special values). -/
noncomputable def peNum (q : ℝ) (n z ϖj h : ℕ) : ℝ :=
  q * (2 : ℝ)⁻¹ ^ ϖj * (1 + coarseError (ϖj + h) q (2 * n + z)) + n * 2 ^ h

/-- The free partners `{a : (a, b) ∈ Fr}` of a column vertex `b`. -/
def peColH {n : ℕ} (Fr : Finset (Fin n × Fin n)) (b : Fin n) : Finset (Fin n) :=
  univ.filter fun a => (a, b) ∈ Fr

/-- The free factors of a column vertex `b` with label `t`:
`∏_{a : (a,b) ∈ Fr} (1 + χ(ς_{ab}(t - x_a)))`. -/
noncomputable def peCovW {n : ℕ} (ς : Fin n → Fin n → ℤ) (Fr : Finset (Fin n × Fin n))
    (x : Fin n → F) (b : Fin n) (t : F) : ℝ :=
  ∏ a ∈ peColH Fr b, (1 + (quadraticChar F ((ς a b : F) * (t - x a)) : ℝ))

theorem peNum_nonneg (q : ℝ) (n z ϖj h : ℕ) (hq : 0 ≤ q) : 0 ≤ peNum q n z ϖj h := by
  unfold peNum
  have := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n + z) (ϖj + h)
  have h1 : 0 ≤ 1 + coarseError (ϖj + h) q (2 * n + z) := by linarith
  positivity

theorem pe_prod_col {n : ℕ} (ς : Fin n → Fin n → ℤ) (Fr : Finset (Fin n × Fin n))
    (Cz : Finset (Fin n)) (x c' : Fin n → F) :
    ∏ e ∈ Fr.filter (fun e => e.2 ∈ Cz), (1 + chiPair ς e x c') =
      ∏ b ∈ Cz, peCovW ς Fr x b (c' b) := by
  unfold peCovW chiPair
  refine prod_finset_product_right' (Fr.filter fun e => e.2 ∈ Cz) Cz (peColH Fr)
    (f := fun a b => 1 + (quadraticChar F ((ς a b : F) * (c' b - x a)) : ℝ)) ?_
  intro e
  simp only [mem_filter, peColH, mem_univ, true_and, Prod.mk.eta]
  exact and_comm

/-- **Step 6 (pinned)**: the sum over the completions of `(x₀_{C_x}, x₀_V)` of the free
product of the integrated vertices is at most `∏_{u ∈ U_x} peNum` (no merges: the pins have their
roots in `𝓜`, which the cross roots avoid). -/
theorem pe_integrated_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V Cx Cz : Finset (Fin n))
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz) (x₀ : Fin n → F) (y : Fin n → F)
    (hy : y ∈ pinLab M pin) :
    ∑ x ∈ peFib (pinLab M pin) Cx V (restr Cx x₀) (restr V x₀),
        ∏ e ∈ Fr.filter (fun e => e.1 ∈ univ \ (V ∪ Cx)), (1 + chiPair ς e x (restr Cz y)) ≤
      ∏ u ∈ univ \ (V ∪ Cx),
        peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card := by
  set Ux := univ \ (V ∪ Cx) with hUx
  obtain ⟨hyinj, hyM, -⟩ := mem_pinLab_iff.mp hy
  set c' := restr Cz y
  set g : Fin n → F → ℝ := fun i t => if i ∈ Ux then intW ς Fr c' i t else 1 with hg
  have hint : ∀ x : Fin n → F,
      ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c') = ∏ i, g i (x i) := by
    intro x
    rw [prod_free_eq_prod_intW]
    simp only [hg]
    rw [prod_ite_mem_eq]
  rw [sum_congr rfl fun x _ => hint x]
  have hg0 : ∀ i t, 0 ≤ g i t := by
    intro i t
    simp only [hg]
    split_ifs
    · exact prod_nonneg fun _ _ => (pin_one_add_chi _).1
    · exact zero_le_one
  refine (pe_sum_prod_le _ (fun i => if i ∈ Ux then pinAllowed M pin i else {x₀ i}) ?_ g hg0).trans
    ?_
  · intro x hx i
    obtain ⟨hxI, hxc, hxv⟩ := mem_peFib.mp hx
    split_ifs with hi
    · exact (mem_pinLab.mp hxI).2 i
    · rw [mem_singleton]
      have hi' : i ∈ V ∪ Cx := by
        by_contra h
        exact hi (mem_sdiff.mpr ⟨mem_univ _, h⟩)
      rcases mem_union.mp hi' with hiV | hiC
      · have := congrFun hxv i
        simpa [restr, hiV] using this
      · have := congrFun hxc i
        simpa [restr, hiC] using this
  · have hsplit : ∏ i, ∑ t ∈ (if i ∈ Ux then pinAllowed M pin i else {x₀ i}), g i t =
        ∏ i, (if i ∈ Ux then ∑ t ∈ pinAllowed M pin i, intW ς Fr c' i t else 1) := by
      refine prod_congr rfl fun i _ => ?_
      split_ifs with hi
      · exact sum_congr rfl fun t _ => by simp only [hg, hi, ↓reduceIte]
      · simp only [hg, hi, ↓reduceIte, sum_singleton]
    rw [hsplit, prod_ite_mem_eq]
    refine prod_le_prod₀ (fun u _ => sum_nonneg fun t _ => prod_nonneg fun _ _ =>
      (pin_one_add_chi _).1) fun u hu => ?_
    -- one integrated vertex
    have hHC : ∀ b ∈ intH Fr u, b ∈ Cz := by
      intro b hb
      have hub : (u, b) ∈ Fr := by simpa [intH] using hb
      refine hFr1 (u, b) hub ?_
      have := (mem_sdiff.mp hu).2
      simp only [mem_union, not_or] at this
      exact this.2
    set κ := ↥(intH Fr u)
    let γ : κ → F := fun b => c' b.1
    have hγ : Function.Injective γ := by
      intro a b hab
      simp only [γ, c', restr_apply_of_mem (hHC a.1 a.2), restr_apply_of_mem (hHC b.1 b.2)] at hab
      exact Subtype.ext (hyinj hab)
    have hγM : ∀ l, γ l ∉ M := by
      intro l
      simp only [γ, c', restr_apply_of_mem (hHC l.1 l.2)]
      exact hyM l.1
    have hpm : ∀ b : κ, ς u b.1 = 1 ∨ ς u b.1 = -1 := by
      intro b
      have hb : ς u b.1 ≠ 0 := hFrς (u, b.1) (by simpa [intH] using b.2)
      rcases hς u b.1 with h | h | h
      · exact absurd h hb
      · exact Or.inl h
      · exact Or.inr h
    let s' : κ → ℤ := fun b => quadraticChar F (-(ς u b.1 : F))
    have hs' : ∀ b, s' b = 1 ∨ s' b = -1 := by
      intro b
      have : (-(ς u b.1 : F)) = ((-ς u b.1 : ℤ) : F) := by push_cast; ring
      simp only [s', this]
      exact pin_char_pm (by rcases hpm b with h | h <;> simp [h])
    have heq : ∀ t, intW ς Fr c' u t = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (t - γ l)) := by
      intro t
      unfold intW
      rw [← prod_coe_sort (intH Fr u)]
      refine prod_congr rfl fun b _ => ?_
      simp only [s', γ]
      have : (ς u b.1 : F) * (c' b.1 - t) = -(ς u b.1 : F) * (t - c' b.1) := by ring
      rw [this, map_mul, Int.cast_mul]
    rw [sum_congr rfl fun t _ => heq t]
    have h1 := pe_one_le hW M pin hpin hpinM u γ hγ hγM s' hs' (Cz.image c')
      (fun l => mem_image_of_mem c' (hHC l.1 l.2))
    have hcard : ((Cz.image c').card : ℝ) ≤ n := by
      have : (Cz.image c').card ≤ n :=
        card_image_le.trans ((card_le_univ Cz).trans (by simp))
      exact_mod_cast this
    have hκ : Fintype.card κ = (intH Fr u).card := Fintype.card_coe _
    rw [hκ] at h1
    unfold peNum
    have : ((Cz.image c').card : ℝ) * 2 ^ (intH Fr u).card ≤ (n : ℝ) * 2 ^ (intH Fr u).card :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    linarith

/-- **Step 7 (pinned cover rows)**: for `x ∈ 𝓘_pin`, the sum over the labels `c'` of `C_z`
occurring in `𝓘_pin` of the free product of the pairs at `C_z` is at most `∏_{b ∈ C_z} peNum`. -/
theorem pe_coverRows_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (Cz : Finset (Fin n)) (x : Fin n → F)
    (hx : x ∈ pinLab M pin) :
    ∑ c' ∈ (pinLab M pin).image (restr Cz),
        ∏ e ∈ Fr.filter (fun e => e.2 ∈ Cz), (1 + chiPair ς e x c') ≤
      ∏ b ∈ Cz, peNum (Fintype.card F) n M.card (pinCount pin b) (peColH Fr b).card := by
  obtain ⟨hxinj, hxM, -⟩ := mem_pinLab_iff.mp hx
  set g : Fin n → F → ℝ := fun i t => if i ∈ Cz then peCovW ς Fr x i t else 1 with hg
  have hint : ∀ c' : Fin n → F,
      ∏ e ∈ Fr.filter (fun e => e.2 ∈ Cz), (1 + chiPair ς e x c') = ∏ i, g i (c' i) := by
    intro c'
    rw [pe_prod_col]
    simp only [hg]
    rw [prod_ite_mem_eq]
  rw [sum_congr rfl fun c' _ => hint c']
  have hg0 : ∀ i t, 0 ≤ g i t := by
    intro i t
    simp only [hg]
    split_ifs
    · exact prod_nonneg fun _ _ => (pin_one_add_chi _).1
    · exact zero_le_one
  refine (pe_sum_prod_le _ (fun i => if i ∈ Cz then pinAllowed M pin i else {0}) ?_ g hg0).trans ?_
  · intro c' hc' i
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
    split_ifs with hi
    · rw [restr_apply_of_mem hi]
      exact (mem_pinLab.mp hy).2 i
    · simp [restr, hi]
  · have hsplit : ∏ i, ∑ t ∈ (if i ∈ Cz then pinAllowed M pin i else {0}), g i t =
        ∏ i, (if i ∈ Cz then ∑ t ∈ pinAllowed M pin i, peCovW ς Fr x i t else 1) := by
      refine prod_congr rfl fun i _ => ?_
      split_ifs with hi
      · exact sum_congr rfl fun t _ => by simp only [hg, hi, ↓reduceIte]
      · simp only [hg, hi, ↓reduceIte, sum_singleton]
    rw [hsplit, prod_ite_mem_eq]
    refine prod_le_prod₀ (fun b _ => sum_nonneg fun t _ => prod_nonneg fun _ _ =>
      (pin_one_add_chi _).1) fun b _ => ?_
    set κ := ↥(peColH Fr b)
    let γ : κ → F := fun a => x a.1
    have hγ : Function.Injective γ := fun a a' h => Subtype.ext (hxinj h)
    have hγM : ∀ l, γ l ∉ M := fun l => hxM l.1
    have hpm : ∀ a : κ, ς a.1 b = 1 ∨ ς a.1 b = -1 := by
      intro a
      have ha : ς a.1 b ≠ 0 := hFrς (a.1, b) (by simpa [peColH] using a.2)
      rcases hς a.1 b with h | h | h
      · exact absurd h ha
      · exact Or.inl h
      · exact Or.inr h
    let s' : κ → ℤ := fun a => quadraticChar F (ς a.1 b : F)
    have hs' : ∀ a, s' a = 1 ∨ s' a = -1 := fun a => pin_char_pm (hpm a)
    have heq : ∀ t, peCovW ς Fr x b t = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (t - γ l)) := by
      intro t
      unfold peCovW
      rw [← prod_coe_sort (peColH Fr b)]
      refine prod_congr rfl fun a _ => ?_
      simp only [s', γ, map_mul, Int.cast_mul]
    rw [sum_congr rfl fun t _ => heq t]
    have h1 := pe_one_le hW M pin hpin hpinM b γ hγ hγM s' hs' (univ.image x)
      (fun l => mem_image_of_mem x (mem_univ _))
    have hcard : ((univ.image x).card : ℝ) ≤ n := by
      have : (univ.image x).card ≤ n := card_image_le.trans (by simp)
      exact_mod_cast this
    have hκ : Fintype.card κ = (peColH Fr b).card := Fintype.card_coe _
    rw [hκ] at h1
    unfold peNum
    have : ((univ.image x).card : ℝ) * 2 ^ (peColH Fr b).card ≤
        (n : ℝ) * 2 ^ (peColH Fr b).card :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    linarith

end PeSide

/-! ## One side: assembly -/

section PeOneSide

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem pe_groupPos_one_mul_gam {n : ℕ} (ς : Fin n → Fin n → ℤ) (Fr : Finset (Fin n × Fin n))
    (Cx Cz : Finset (Fin n)) (x c' : Fin n → F) :
    groupPos ς Fr (predOne Cx Cz) x c' * groupPos ς Fr (predGam Cx Cz) x c' =
      ∏ e ∈ Fr.filter (fun e => e.2 ∈ Cz), (1 + chiPair ς e x c') := by
  unfold groupPos
  rw [← prod_filter_mul_prod_filter_not (Fr.filter (fun e => e.2 ∈ Cz)) (fun e => e.1 ∈ Cx),
    filter_filter, filter_filter, mul_comm]
  congr 1
  · refine prod_congr (filter_congr fun e _ => ?_) fun e _ => rfl
    exact and_comm
  · refine prod_congr (filter_congr fun e _ => ?_) fun e _ => rfl
    exact and_comm

/-- **Steps 5–6 (pinned) for one fibre**:
`𝖺_{c,c'}(v)² ≤ 2^{f_V} ∏_{u ∈ U_x} peNum · ∑_{fibre} f(x)² Θ₁⁺(x, c')`. -/
theorem pe_alpha_sq_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V Cx Cz : Finset (Fin n)) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz) (f : (Fin n → F) → ℝ) (c c' v : Fin n → F)
    (hc' : c' ∈ (pinLab M pin).image (restr Cz)) :
    peAlpha (pinLab M pin) ς P Fr V Cx Cz f c c' v ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
        (∏ u ∈ univ \ (V ∪ Cx),
          peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card) *
        ∑ x ∈ peFib (pinLab M pin) Cx V c v, f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' := by
  set I := pinLab M pin
  set Ux := univ \ (V ∪ Cx) with hUx
  set MU := ∏ u ∈ Ux, peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set g : (Fin n → F) → ℝ := fun x => groupPos ς Fr (predOne Cx Cz) x c' with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => groupPos_nonneg ς Fr _ x c'
  have hMU0 : 0 ≤ MU := prod_nonneg fun u _ => peNum_nonneg _ _ _ _ _ (Nat.cast_nonneg _)
  by_cases hne : (peFib I Cx V c v).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hne
    unfold peAlpha
    rw [hne, sum_empty, sum_empty]
    simp
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨-, hx₀c, hx₀v⟩ := mem_peFib.mp hx₀
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
  have hfib : peFib I Cx V c v = peFib I Cx V (restr Cx x₀) (restr V x₀) := by
    rw [hx₀c, hx₀v]
  have hm := pe_integrated_le hW M pin hpin hpinM ς hς Fr hFrς V Cx Cz hFr1 x₀ y hy
  rw [← hfib] at hm
  have hsumg : ∑ x ∈ peFib I Cx V c v, g x ≤ 2 ^ fV * MU := by
    calc ∑ x ∈ peFib I Cx V c v, g x
        ≤ ∑ x ∈ peFib I Cx V c v, 2 ^ fV *
            ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x (restr Cz y)) := by
          refine sum_le_sum fun x _ => ?_
          simp only [hg]
          rw [groupPos_one_split ς Fr V Cx Cz hVC hFr1 x (restr Cz y)]
          exact mul_le_mul_of_nonneg_right (prod_free_le_two_pow ς _ x (restr Cz y))
            (prod_nonneg fun e _ => one_add_chiPair_nonneg ς e x (restr Cz y))
      _ = 2 ^ fV * ∑ x ∈ peFib I Cx V c v,
            ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x (restr Cz y)) := by
          rw [mul_sum]
      _ ≤ 2 ^ fV * MU := mul_le_mul_of_nonneg_left hm (by positivity)
  have hα : |peAlpha I ς P Fr V Cx Cz f c (restr Cz y) v| ≤
      ∑ x ∈ peFib I Cx V c v, g x * |f x| := by
    unfold peAlpha
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_groupKer_le ς P Fr _ x _) (abs_nonneg _)
  have hcs := weighted_cs (peFib I Cx V c v) g f (fun x _ => hg0 x)
  have hS0 : 0 ≤ ∑ x ∈ peFib I Cx V c v, g x * f x ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (hg0 x) (sq_nonneg _)
  calc peAlpha I ς P Fr V Cx Cz f c (restr Cz y) v ^ 2
      = |peAlpha I ς P Fr V Cx Cz f c (restr Cz y) v| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ x ∈ peFib I Cx V c v, g x * |f x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hα 2
    _ ≤ (∑ x ∈ peFib I Cx V c v, g x) * ∑ x ∈ peFib I Cx V c v, g x * f x ^ 2 := hcs
    _ ≤ (2 ^ fV * MU) * ∑ x ∈ peFib I Cx V c v, g x * f x ^ 2 :=
        mul_le_mul_of_nonneg_right hsumg hS0
    _ = _ := by
        rw [mul_sum, mul_sum]
        exact sum_congr rfl fun x _ => by simp only [hg]; ring

/-- **One side of `prop:pinned-extraction` (Steps 5–7)**, counting form:
`∑_{c,c'} |Γ| ‖𝖺_{c,c'}‖² ≤ 2^{f_V} ∏_{u ∈ U_x} peNum ∏_{b ∈ C_z} peNum ∑_{x ∈ 𝓘_pin} f(x)²`. -/
theorem pe_one_side_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V Cx Cz : Finset (Fin n)) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz) (f : (Fin n → F) → ℝ) :
    ∑ c ∈ (pinLab M pin).image (restr Cx), ∑ c' ∈ (pinLab M pin).image (restr Cz),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, peAlpha (pinLab M pin) ς P Fr V Cx Cz f c c' v ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
        (∏ u ∈ univ \ (V ∪ Cx),
          peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card) *
        (∏ b ∈ Cz, peNum (Fintype.card F) n M.card (pinCount pin b) (peColH Fr b).card) *
        ∑ x ∈ pinLab M pin, f x ^ 2 := by
  set I := pinLab M pin
  set Ix := I.image (restr Cx)
  set Iz := I.image (restr Cz)
  set K := 2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
    (∏ u ∈ univ \ (V ∪ Cx), peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card)
    with hK
  set MC := ∏ b ∈ Cz, peNum (Fintype.card F) n M.card (pinCount pin b) (peColH Fr b).card
  have hK0 : 0 ≤ K := mul_nonneg (by positivity)
    (prod_nonneg fun u _ => peNum_nonneg _ _ _ _ _ (Nat.cast_nonneg _))
  set Prow : (Fin n → F) → (Fin n → F) → ℝ := fun x c' =>
    ∏ e ∈ Fr.filter (fun e => e.2 ∈ Cz), (1 + chiPair ς e x c') with hProw
  have hProw0 : ∀ x c', 0 ≤ Prow x c' := fun x c' =>
    prod_nonneg fun e _ => one_add_chiPair_nonneg ς e x c'
  have hI : ∀ x ∈ I, Function.Injective x := fun x hx => (mem_pinLab_iff.mp hx).1
  have hstep : ∀ c ∈ Ix, ∀ c' ∈ Iz,
      |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2 ≤
        K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' := by
    intro c _ c' hc'
    have hv : ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2 ≤
        K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 *
          groupPos ς Fr (predOne Cx Cz) x c' := by
      calc ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2
          ≤ ∑ v ∈ injTuples F V, K * ∑ x ∈ peFib I Cx V c v, f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' :=
            sum_le_sum fun v _ => pe_alpha_sq_le hW M pin hpin hpinM ς hς P Fr hFrς V Cx Cz hVC
              hFr1 f c c' v hc'
        _ = K * ∑ v ∈ injTuples F V, ∑ x ∈ peFib I Cx V c v, f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' := by rw [mul_sum]
        _ = _ := by
            congr 1
            rw [← sum_fiberwise_of_maps_to (s := I.filter (fun x => restr Cx x = c))
              (g := restr V) (t := injTuples F V)
              (fun x hx => pe_restr_mem_injTuples V (hI x (mem_filter.mp hx).1))]
            refine sum_congr rfl fun v _ => ?_
            unfold peFib
            rw [filter_filter]
    have hΓ : ∀ x ∈ I.filter (fun x => restr Cx x = c),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c') ≤ f x ^ 2 * Prow x c' := by
      intro x hx
      have hxc := (mem_filter.mp hx).2
      have hg : groupPos ς Fr (predGam Cx Cz) c c' = groupPos ς Fr (predGam Cx Cz) x c' :=
        groupPos_congr ς Fr _ fun e he => ⟨(restr_eq_iff hxc he.1).symm, rfl⟩
      have h1 := abs_groupKer_le ς P Fr (predGam Cx Cz) c c'
      rw [hg] at h1
      have h0 : 0 ≤ f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' :=
        mul_nonneg (sq_nonneg _) (groupPos_nonneg ς Fr _ x c')
      calc |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c')
          ≤ groupPos ς Fr (predGam Cx Cz) x c' *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c') := mul_le_mul_of_nonneg_right h1 h0
        _ = f x ^ 2 * (groupPos ς Fr (predOne Cx Cz) x c' *
              groupPos ς Fr (predGam Cx Cz) x c') := by ring
        _ = f x ^ 2 * Prow x c' := by rw [pe_groupPos_one_mul_gam]
    calc |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2
        ≤ |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c') :=
          mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ = K * ∑ x ∈ I.filter (fun x => restr Cx x = c),
            |groupKer ς P Fr (predGam Cx Cz) c c'| * (f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c') := by
          rw [mul_sum, mul_sum, mul_sum]
          exact sum_congr rfl fun x _ => by ring
      _ ≤ K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' :=
          mul_le_mul_of_nonneg_left (sum_le_sum hΓ) hK0
  have hrow : ∀ x ∈ I, ∑ c' ∈ Iz, Prow x c' ≤ MC := fun x hx =>
    pe_coverRows_le hW M pin hpin hpinM ς hς Fr hFrς Cz x hx
  calc ∑ c ∈ Ix, ∑ c' ∈ Iz, |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2
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

end PeOneSide

/-! ## The transposed class (Step 8, no symmetry) and the class bound -/

section PeClass

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem pe_chiPair_swap {n : ℕ} (ς : Fin n → Fin n → ℤ) (e : Fin n × Fin n) (x x' : Fin n → F) :
    chiPair (pinSwap ς) e.swap x' x = chiPair ς e x x' := by
  unfold chiPair pinSwap
  simp only [Prod.fst_swap, Prod.snd_swap, Int.cast_neg]
  congr 2
  ring

theorem pe_groupKer_swap {n : ℕ} (ς : Fin n → Fin n → ℤ) (P Fr : Finset (Fin n × Fin n))
    (p : Fin n × Fin n → Prop) [DecidablePred p] (x x' : Fin n → F) :
    groupKer (pinSwap ς) (P.image Prod.swap) (Fr.image Prod.swap) p x' x =
      groupKer ς P Fr (fun e => p e.swap) x x' := by
  unfold groupKer
  rw [filter_image, filter_image, prod_image (fun a _ b _ h => Prod.swap_injective h),
    prod_image (fun a _ b _ h => Prod.swap_injective h)]
  simp only [pe_chiPair_swap]

theorem pe_beta_eq_alpha_swap {n : ℕ} (I : Finset (Fin n → F)) (ς : Fin n → Fin n → ℤ)
    (P Fr : Finset (Fin n × Fin n)) (W Cx Cz : Finset (Fin n)) (h : (Fin n → F) → ℝ)
    (c c' w : Fin n → F) :
    peBeta I ς P Fr W Cx Cz h c c' w =
      peAlpha I (pinSwap ς) (P.image Prod.swap) (Fr.image Prod.swap) W Cz Cx h c' c w := by
  unfold peAlpha peBeta
  refine sum_congr rfl fun x' _ => ?_
  rw [pe_groupKer_swap, mul_comm]
  congr 1
  unfold groupKer
  congr 2
  · exact filter_congr fun e _ => and_comm
  · exact filter_congr fun e _ => and_comm

theorem pe_gam_swap {n : ℕ} (ς : Fin n → Fin n → ℤ) (P Fr : Finset (Fin n × Fin n))
    (Cx Cz : Finset (Fin n)) (c c' : Fin n → F) :
    groupKer (pinSwap ς) (P.image Prod.swap) (Fr.image Prod.swap) (predGam Cz Cx) c' c =
      groupKer ς P Fr (predGam Cx Cz) c c' := by
  rw [pe_groupKer_swap]
  unfold groupKer
  congr 2
  · exact filter_congr fun e _ => and_comm
  · exact filter_congr fun e _ => and_comm

theorem pe_intH_swap {n : ℕ} (Fr : Finset (Fin n × Fin n)) (u : Fin n) :
    intH (Fr.image Prod.swap) u = peColH Fr u := by
  unfold intH peColH
  refine filter_congr fun a _ => ?_
  simp only [mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨b, c, h, rfl, rfl⟩
    exact h
  · intro h
    exact ⟨a, u, h, rfl, rfl⟩

theorem pe_colH_swap {n : ℕ} (Fr : Finset (Fin n × Fin n)) (b : Fin n) :
    peColH (Fr.image Prod.swap) b = intH Fr b := by
  unfold intH peColH
  refine filter_congr fun a _ => ?_
  simp only [mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨c, d, h, rfl, rfl⟩
    exact h
  · intro h
    exact ⟨b, a, h, rfl, rfl⟩

/-- **The other side (Step 8)**: the transposed class `𝒞(Pᵀ, Aᵀ)` for the support
`{(j, i) : (i, j) ∈ E_×}` with the signs `-ς_{ji}` (`pinSwap`), the same pinned law on both rows;
no symmetry of `E_×` is used. Its counts are the column counts on `U_z` and the row counts on
`C_x`. -/
theorem pe_other_side_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (W Cx Cz : Finset (Fin n)) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hFr2 : ∀ e ∈ Fr, e.2 ∉ Cz → e.1 ∈ Cx) (h : (Fin n → F) → ℝ) :
    ∑ c ∈ (pinLab M pin).image (restr Cx), ∑ c' ∈ (pinLab M pin).image (restr Cz),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ w ∈ injTuples F W, peBeta (pinLab M pin) ς P Fr W Cx Cz h c c' w ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.2 ∈ W)).card *
        (∏ u ∈ univ \ (W ∪ Cz),
          peNum (Fintype.card F) n M.card (pinCount pin u) (peColH Fr u).card) *
        (∏ b ∈ Cx, peNum (Fintype.card F) n M.card (pinCount pin b) (intH Fr b).card) *
        ∑ x ∈ pinLab M pin, h x ^ 2 := by
  have hT := pe_one_side_le hW M pin hpin hpinM (pinSwap ς) (pinSwap_signs hς)
    (P.image Prod.swap) (Fr.image Prod.swap)
    (fun e he => by
      obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
      simp only [pinSwap, Prod.fst_swap, Prod.snd_swap, neg_ne_zero]
      exact hFrς e₀ he₀)
    W Cz Cx hWC
    (fun e he h1 => by
      obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
      exact hFr2 e₀ he₀ h1) h
  rw [card_filter_swap] at hT
  simp only [pe_intH_swap, pe_colH_swap] at hT
  refine le_trans (le_of_eq ?_) hT
  rw [sum_comm]
  refine sum_congr rfl fun c' _ => sum_congr rfl fun c _ => ?_
  rw [pe_gam_swap]
  congr 1
  exact sum_congr rfl fun w _ => by rw [pe_beta_eq_alpha_swap]

/-- **`prop:pinned-extraction`, counting form of the class bound**:
`|∑_{x, y ∈ 𝓘_pin} f(x) K_𝒞(x, y) h(y)| ≤ Λ (2^{f_V} M_{U_x} M_{C_z} ∑ f²)^{1/2}
(2^{f_W} M_{U_z} M_{C_x} ∑ h²)^{1/2}` with `M_S = ∏_{v ∈ S} peNum`. -/
theorem pe_class_count (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V W Cx Cz : Finset (Fin n)) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hWC : ∀ u ∈ W, u ∉ Cz) (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W) Λ)
    (f h : (Fin n → F) → ℝ) :
    |∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * classKer ς P Fr x x' * h x'| ≤
      Λ * Real.sqrt (2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
          (∏ u ∈ univ \ (V ∪ Cx),
            peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card) *
          (∏ b ∈ Cz, peNum (Fintype.card F) n M.card (pinCount pin b) (peColH Fr b).card) *
          ∑ x ∈ pinLab M pin, f x ^ 2) *
        Real.sqrt (2 ^ (Fr.filter (fun e => e.2 ∈ W)).card *
          (∏ u ∈ univ \ (W ∪ Cz),
            peNum (Fintype.card F) n M.card (pinCount pin u) (peColH Fr u).card) *
          (∏ b ∈ Cx, peNum (Fintype.card F) n M.card (pinCount pin b) (intH Fr b).card) *
          ∑ x ∈ pinLab M pin, h x ^ 2) := by
  refine (pe_bilinear_le (pinLab M pin) (fun x hx => (mem_pinLab_iff.mp hx).1) ς P Fr V W Cx Cz
    hVC hWC hP hFr hΛ hker f h).trans ?_
  have h1 := pe_one_side_le hW M pin hpin hpinM ς hς P Fr hFrς V Cx Cz hVC
    (fun e he h1 => (hFr e he).resolve_left h1) f
  have h2 := pe_other_side_le hW M pin hpin hpinM ς hς P Fr hFrς W Cx Cz hWC
    (fun e he h2 => (hFr e he).resolve_right h2) h
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hΛ)
    (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) (mul_nonneg hΛ (Real.sqrt_nonneg _))

end PeClass

/-! ## The class bound in the normalization of `L²(μ)` -/

section PeNorm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The one-step lower count `q 2^{-ϖ_j}(1 - e^pin_ϖ)` of a pinned coordinate. -/
noncomputable def peLow (q : ℝ) (n z ϖ ϖj : ℕ) : ℝ := q * (2 : ℝ)⁻¹ ^ ϖj * (1 - ePin q n z ϖ)

/-- The pinned vertex factor `F^pin_v` of a vertex with `ϖ_v` pins and `h_v` free pairs:
`peNum / peLow = (1 + e_{ϖ_v+h_v}(q, 2n+z) + r² n 2^{ϖ_v+h_v})/(1 - e^pin_ϖ)`, at most the paper's
`(1 + e^pin_{ϖ_v+h_v} + r² n 2^{ϖ_v+h_v})/(1 - e^pin_ϖ)` (`peF_le`). -/
noncomputable def peF (q : ℝ) (n z ϖ ϖj h : ℕ) : ℝ := peNum q n z ϖj h / peLow q n z ϖ ϖj

/-- The product of the pinned vertex factors over the `2(n - k)` non-witness vertices of a record
(`U_x`, `C_z` with the row and column counts of the class; `U_z`, `C_x` with those of the transposed
class). -/
noncomputable def peFactor (q : ℝ) (n z ϖ : ℕ) (pin : Fin n → F → ℤ) (Fr : Finset (Fin n × Fin n))
    (V W Cx Cz : Finset (Fin n)) : ℝ :=
  (∏ u ∈ univ \ (V ∪ Cx), peF q n z ϖ (pinCount pin u) (intH Fr u).card) *
    (∏ b ∈ Cz, peF q n z ϖ (pinCount pin b) (peColH Fr b).card) *
    (∏ u ∈ univ \ (W ∪ Cz), peF q n z ϖ (pinCount pin u) (peColH Fr u).card) *
    ∏ b ∈ Cx, peF q n z ϖ (pinCount pin b) (intH Fr b).card

theorem peLow_pos {q : ℝ} (hq : 0 < q) {n z ϖ : ℕ} (he : ePin q n z ϖ < 1) (ϖj : ℕ) :
    0 < peLow q n z ϖ ϖj := by
  unfold peLow
  exact mul_pos (mul_pos hq (by positivity)) (by linarith)

theorem peNum_eq {q : ℝ} (hq : 0 < q) {n z ϖ : ℕ} (he : ePin q n z ϖ < 1) (ϖj h : ℕ) :
    peNum q n z ϖj h = peF q n z ϖ ϖj h * peLow q n z ϖ ϖj := by
  unfold peF
  rw [div_mul_cancel₀ _ (peLow_pos hq he ϖj).ne']

theorem peF_nonneg {q : ℝ} (hq : 0 < q) {n z ϖ : ℕ} (he : ePin q n z ϖ < 1) (ϖj h : ℕ) :
    0 ≤ peF q n z ϖ ϖj h :=
  div_nonneg (peNum_nonneg q n z ϖj h hq.le) (peLow_pos hq he ϖj).le

/-- **`prop:pinned-extraction`, the class bound** (Steps 1–8, any witness size `k`): with the
pinned law `μ` uniform on `𝓘_pin`, `e^pin_ϖ < 1`, a class with a witness (`|V| = |W| = k`) and a
cover, and the kernel hypothesis `‖𝖶‖ ≤ c_ker r^k` on injective tuples,
`|E_{x,y∼μ} f(x) K_𝒞(x,y) h(y)| ≤ c_ker r^k (2^{f_V + f_W + ϖ_V + ϖ_W} ∏_v F^pin_v)^{1/2}
(1 - e^pin_ϖ)^{-k} ‖f‖_μ ‖h‖_μ`, `ϖ_V`, `ϖ_W` the numbers of pins of the witness vertices (each
witness label contributes the factor `2^{ϖ_v}` of its pins). Written with `E_μ = |𝓘_pin|⁻¹ ∑`.
The counting route needs no completion ratio `R_pin`. -/
theorem pe_class_sum_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ} (V W Cx Cz : Finset (Fin n)) (hVk : V.card = k)
    (hWk : W.card = k) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * classKer ς P Fr x x' * h x') /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin Fr V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  set z := M.card
  set I := pinLab M pin
  set N : ℝ := (I.card : ℝ)
  set Ux := univ \ (V ∪ Cx)
  set Uz := univ \ (W ∪ Cz)
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set fW := (Fr.filter (fun e => e.2 ∈ W)).card
  set tV := ∑ v ∈ V, pinCount pin v
  set tW := ∑ v ∈ W, pinCount pin v
  set e := ePin q n z ϖ
  set ℓ : Fin n → ℝ := fun j => peLow q n z ϖ (pinCount pin j) with hℓ
  have hℓpos : ∀ j, 0 < ℓ j := fun j => peLow_pos hq0 he _
  have hΛ : 0 ≤ cker * Real.sqrt q ^ k := mul_nonneg hcker (by positivity)
  have hQ := pe_class_count hW M pin hpin hpinM ς hς P Fr hFrς V W Cx Cz hVC hWC hP hFr hΛ hker
    f h
  -- the lower count
  have hL : ∏ j, ℓ j ≤ N := by
    have := card_pinLab_ge hW M pin hpin hpinM ϖ hϖ he
    exact this
  have hL0 : 0 < ∏ j, ℓ j := prod_pos fun j _ => hℓpos j
  have hN0 : 0 < N := lt_of_lt_of_le hL0 hL
  -- the factor identities
  set PUx := ∏ u ∈ Ux, peF q n z ϖ (pinCount pin u) (intH Fr u).card
  set PCz := ∏ b ∈ Cz, peF q n z ϖ (pinCount pin b) (peColH Fr b).card
  set PUz := ∏ u ∈ Uz, peF q n z ϖ (pinCount pin u) (peColH Fr u).card
  set PCx := ∏ b ∈ Cx, peF q n z ϖ (pinCount pin b) (intH Fr b).card
  have hfac : ∀ (S : Finset (Fin n)) (hh : Fin n → ℕ),
      ∏ u ∈ S, peNum q n z (pinCount pin u) (hh u) =
        (∏ u ∈ S, peF q n z ϖ (pinCount pin u) (hh u)) * ∏ u ∈ S, ℓ u := by
    intro S hh
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun u _ => peNum_eq hq0 he _ _
  rw [hfac Ux (fun u => (intH Fr u).card), hfac Cz (fun b => (peColH Fr b).card),
    hfac Uz (fun u => (peColH Fr u).card), hfac Cx (fun b => (intH Fr b).card)] at hQ
  set A := (2 : ℝ) ^ fV * (PUx * ∏ u ∈ Ux, ℓ u) * (PCz * ∏ b ∈ Cz, ℓ b)
  set B := (2 : ℝ) ^ fW * (PUz * ∏ u ∈ Uz, ℓ u) * (PCx * ∏ b ∈ Cx, ℓ b)
  have hPUx0 : 0 ≤ PUx := prod_nonneg fun u _ => peF_nonneg hq0 he _ _
  have hPUz0 : 0 ≤ PUz := prod_nonneg fun u _ => peF_nonneg hq0 he _ _
  have hPCz0 : 0 ≤ PCz := prod_nonneg fun b _ => peF_nonneg hq0 he _ _
  have hPCx0 : 0 ≤ PCx := prod_nonneg fun b _ => peF_nonneg hq0 he _ _
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUx0 (prod_nonneg fun u _ => (hℓpos u).le)))
    (mul_nonneg hPCz0 (prod_nonneg fun u _ => (hℓpos u).le))
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUz0 (prod_nonneg fun u _ => (hℓpos u).le)))
    (mul_nonneg hPCx0 (prod_nonneg fun u _ => (hℓpos u).le))
  have hnorm := normalize_le hN0 hL0 hL0 hL hL hA0 hB0
    (sum_nonneg fun x _ => sq_nonneg (f x)) (sum_nonneg fun x _ => sq_nonneg (h x)) hΛ hQ
  refine hnorm.trans ?_
  -- the witness factors
  set DV := ∏ v ∈ V, ℓ v
  set DW := ∏ v ∈ W, ℓ v
  have hDV : DV = q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k := by
    simp only [DV, hℓ, peLow]
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hVk, prod_pow_eq_pow_sum]
  have hDW : DW = q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k := by
    simp only [DW, hℓ, peLow]
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hWk, prod_pow_eq_pow_sum]
  have h1e : 0 < 1 - e := by linarith
  set PF := PUx * PCz * PUz * PCx
  have hsplitX : ∏ v, ℓ v = (∏ v ∈ Ux, ℓ v) * DV * ∏ v ∈ Cx, ℓ v :=
    prod_univ_three V Cx hVC ℓ
  have hsplitZ : ∏ v, ℓ v = (∏ v ∈ Uz, ℓ v) * DW * ∏ v ∈ Cz, ℓ v :=
    prod_univ_three W Cz hWC ℓ
  have hAB : A * B / ((∏ v, ℓ v) * ∏ v, ℓ v) = 2 ^ fV * 2 ^ fW * PF / (DV * DW) := by
    have h1 : (0 : ℝ) < ∏ v ∈ Ux, ℓ v := prod_pos fun v _ => hℓpos v
    have h2 : (0 : ℝ) < ∏ v ∈ Cx, ℓ v := prod_pos fun v _ => hℓpos v
    have h3 : (0 : ℝ) < ∏ v ∈ Uz, ℓ v := prod_pos fun v _ => hℓpos v
    have h4 : (0 : ℝ) < ∏ v ∈ Cz, ℓ v := prod_pos fun v _ => hℓpos v
    have h5 : (0 : ℝ) < DV := prod_pos fun v _ => hℓpos v
    have h6 : (0 : ℝ) < DW := prod_pos fun v _ => hℓpos v
    rw [show ((∏ v, ℓ v) * ∏ v, ℓ v) = ((∏ v ∈ Ux, ℓ v) * DV * ∏ v ∈ Cx, ℓ v) *
        ((∏ v ∈ Uz, ℓ v) * DW * ∏ v ∈ Cz, ℓ v) by rw [← hsplitX, ← hsplitZ]]
    simp only [A, B, PF]
    field_simp
  rw [hAB, hDV, hDW]
  have hinv : ((Real.sqrt q)⁻¹ ^ k) ^ 2 = (q ^ k)⁻¹ := by
    rw [inv_pow, inv_pow, sqrt_pow_sq hq0.le]
  have hsq : (cker * Real.sqrt q ^ k) ^ 2 *
      (2 ^ fV * 2 ^ fW * PF / ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k) *
        (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k))) =
      (cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k) ^ 2 * (2 ^ (fV + fW + tV + tW) * PF) := by
    have e1 : (cker * Real.sqrt q ^ k) ^ 2 = cker ^ 2 * q ^ k := by
      rw [mul_pow, sqrt_pow_sq hq0.le]
    have e2 : (cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k) ^ 2 =
        cker ^ 2 * (q ^ k)⁻¹ / ((1 - e) ^ k) ^ 2 := by
      rw [div_pow, mul_pow, hinv]
    rw [e1, e2]
    simp only [pow_add, inv_pow]
    have hq' : (q ^ k) ≠ 0 := by positivity
    have he' : (1 - e) ^ k ≠ 0 := by positivity
    field_simp
  have hc' : 0 ≤ cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k := by positivity
  have hPF0 : 0 ≤ PF := mul_nonneg (mul_nonneg (mul_nonneg hPUx0 hPCz0) hPUz0) hPCx0
  have hkey : cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF /
        ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k) * (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k))) =
      cker * (Real.sqrt q)⁻¹ ^ k * Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) / (1 - e) ^ k := by
    calc cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF /
          ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k) * (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k)))
        = Real.sqrt ((cker * Real.sqrt q ^ k) ^ 2 * (2 ^ fV * 2 ^ fW * PF /
            ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k) *
              (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k)))) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛ]
      _ = Real.sqrt ((cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k) ^ 2 *
            (2 ^ (fV + fW + tV + tW) * PF)) := by rw [hsq]
      _ = cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k *
            Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc']
      _ = _ := by ring
  rw [hkey]
  unfold peFactor
  exact le_rfl

end PeNorm

end Sarkozy.ExtractionK
