module

public import Sarkozy.PartVRecords.MergeRecords
public import Sarkozy.PartVRecords.OneStageMarginals

@[expose] public section

/-!
# The half marginals of the mirror-edge replacement (`lem:merge-repair`, first sentence)

`paper/sections/21_middle_records.tex`, `lem:merge-repair`: "The replacements of
`def:merge-records` are positive probability laws with both actual half marginals equal to `m_p`".
For the first-coordinate law this is `firstLaw_half0`, `firstLaw_half1`
(`Sarkozy.PartVRecords.MergeRecords`). Here: **the mirror-edge law** (uniform on the injective
four-label tuples `(x₀, x₁, y₀, y₁)` with `x₁ → y₀` and `x₀ → y₁`) **has both half marginals
`m_p`**, the uniform law on the ordered distinct pairs (`mirrorLaw_half0`, `mirrorLaw_half1`), for
`p ≡ 3 (mod 4)`.

The count (the paper's "Fix `x₀ ≠ x₁` …"): for `a ≠ b`, the number of `(y₀, y₁)` completing
`(x₀, x₁) = (a, b)` is `(m - [a → b])(m - [b → a]) - k = (p - 3)(p - 2)/4`, `m = (p - 1)/2`,
`k = (p - 3)/4` the number of common out-neighbours, since exactly one of `a → b`, `b → a` holds
(`mirror_count_layer0`); and symmetrically for `(y₀, y₁) = (c, d)` with in-neighbours
(`mirror_count_layer1`).
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- Quadruples and four-label configurations. -/
def quadEquiv : F × F × F × F ≃ (Fin 2 × Fin 2 → F) where
  toFun := quadConfig
  invFun z := (z (0, 0), z (1, 0), z (0, 1), z (1, 1))
  left_inv t := by
    obtain ⟨a, b, c, d⟩ := t
    simp [quadConfig]
  right_inv z := by
    funext o
    obtain ⟨a, l⟩ := o
    fin_cases a <;> fin_cases l <;> simp [quadConfig]

/-- The mirror condition on `(x₀, x₁, y₀, y₁)`: distinct labels with `x₁ → y₀` and `x₀ → y₁`. -/
abbrev MirrorCond (t : F × F × F × F) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2 ∧
    χ (t.2.2.1 - t.2.1) = 1 ∧ χ (t.2.2.2 - t.1) = 1

theorem quadConfig_injective_iff (t : F × F × F × F) (h1 : χ (t.2.2.1 - t.2.1) = 1)
    (h2 : χ (t.2.2.2 - t.1) = 1) :
    Function.Injective (quadConfig t) ↔
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2 := by
  obtain ⟨a, b, c, d⟩ := t
  have hbc : b ≠ c := (ne_of_chi_eq h1 (Or.inl rfl)).symm
  have had : a ≠ d := (ne_of_chi_eq h2 (Or.inl rfl)).symm
  clear h1 h2
  constructor
  · intro h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · have := @h (0, 0) (1, 0) (by simpa [quadConfig] using e)
      simp at this
    · have := @h (0, 0) (0, 1) (by simpa [quadConfig] using e)
      simp at this
    · have := @h (1, 0) (1, 1) (by simpa [quadConfig] using e)
      simp at this
    · have := @h (0, 1) (1, 1) (by simpa [quadConfig] using e)
      simp at this
  · rintro ⟨h1, h2, h3, h4⟩ ⟨o, l⟩ ⟨o', l'⟩ e
    fin_cases o <;> fin_cases l <;> fin_cases o' <;> fin_cases l' <;>
      simp_all [quadConfig, eq_comm]

/-- Membership in `Inj_p(mirrorGraph)` is the mirror condition. -/
theorem mem_inj_mirror_iff (t : F × F × F × F) :
    quadConfig t ∈ injLabellings F mirrorGraph ↔ MirrorCond t := by
  rw [mem_injLabellings_iff_feasible]
  have he1 : quadConfig t (0, 1) - quadConfig t (1, 0) = t.2.2.1 - t.2.1 := by simp [quadConfig]
  have he2 : quadConfig t (1, 1) - quadConfig t (0, 0) = t.2.2.2 - t.1 := by simp [quadConfig]
  constructor
  · rintro ⟨hinj, hedge⟩
    have h1 := hedge ((1, 0), (0, 1)) (by simp [mirrorGraph]) (mem_univ _) (mem_univ _)
    have h2 := hedge ((0, 0), (1, 1)) (by simp [mirrorGraph]) (mem_univ _) (mem_univ _)
    simp only at h1 h2
    rw [he1] at h1
    rw [he2] at h2
    have hi : Function.Injective (quadConfig t) := fun x y hxy =>
      hinj x (mem_univ _) y (mem_univ _) hxy
    obtain ⟨d1, d2, d3, d4⟩ := (quadConfig_injective_iff t h1 h2).mp hi
    exact ⟨d1, d2, d3, d4, h1, h2⟩
  · rintro ⟨d1, d2, d3, d4, h1, h2⟩
    have hi := (quadConfig_injective_iff t h1 h2).mpr ⟨d1, d2, d3, d4⟩
    refine ⟨fun x _ y _ hxy => hi hxy, fun e he _ _ => ?_⟩
    simp only [mirrorGraph, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · rw [he1]
      exact h1
    · rw [he2]
      exact h2

/-- **The mirror-edge law at one prime**, as a sum over quadruples. -/
theorem mirrorLaw_expect (hne : (injLabellings F mirrorGraph).Nonempty)
    (H : (Fin 2 × Fin 2 → F) → ℝ) :
    (mirrorLaw hne).expect H =
      (∑ t : F × F × F × F, if MirrorCond t then H (quadConfig t) else 0) /
        (∑ t : F × F × F × F, if MirrorCond t then (1 : ℝ) else 0) := by
  have hcard : ((injLabellings F mirrorGraph).card : ℝ) =
      ∑ t : F × F × F × F, if MirrorCond t then (1 : ℝ) else 0 := by
    have h1 : ((injLabellings F mirrorGraph).card : ℝ) =
        ∑ z : Fin 2 × Fin 2 → F, if z ∈ injLabellings F mirrorGraph then (1 : ℝ) else 0 := by
      rw [sum_boole]
      congr 2
      ext z
      simp
    rw [h1]
    refine (Fintype.sum_equiv quadEquiv _ _ fun t => ?_).symm
    change _ = (if quadConfig t ∈ injLabellings F mirrorGraph then (1 : ℝ) else 0)
    by_cases hd : MirrorCond t
    · rw [ite_eq_left hd, ite_eq_left ((mem_inj_mirror_iff t).mpr hd)]
    · rw [ite_eq_right hd, ite_eq_right (fun h' => hd ((mem_inj_mirror_iff t).mp h'))]
  have hexp : (mirrorLaw hne).expect H =
      ∑ t : F × F × F × F, (mirrorLaw hne).weight (quadConfig t) * H (quadConfig t) := by
    unfold FiniteLaw.expect
    exact (Fintype.sum_equiv quadEquiv _ (fun z => (mirrorLaw hne).weight z * H z)
      fun _ => rfl).symm
  rw [hexp, ← hcard, sum_div]
  refine sum_congr rfl fun t _ => ?_
  change (if quadConfig t ∈ injLabellings F mirrorGraph then
    1 / ((injLabellings F mirrorGraph).card : ℝ) else 0) * H (quadConfig t) = _
  by_cases hd : MirrorCond t
  · rw [ite_eq_left ((mem_inj_mirror_iff t).mpr hd), ite_eq_left hd]
    ring
  · rw [ite_eq_right (fun h' => hd ((mem_inj_mirror_iff t).mp h')), ite_eq_right hd]
    ring

/-! ## The counts -/

/-- `∑_y [a → y] = (q - 1)/2`. -/
theorem sum_arrow (hF : ringChar F ≠ 2) (a : F) :
    ∑ y : F, (if χ (y - a) = 1 then (1 : ℝ) else 0) = ((Fintype.card F : ℝ) - 1) / 2 :=
  sum_out_indicator hF a

/-- `∑_y [a → y][b → y] = (q - 3)/4` for `a ≠ b`. -/
theorem sum_common_arrow (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a b : F}
    (hab : a ≠ b) :
    ∑ y : F, (if χ (y - a) = 1 ∧ χ (y - b) = 1 then (1 : ℝ) else 0) =
      ((Fintype.card F : ℝ) - 3) / 4 := by
  rw [sum_boole]
  have h := card_common_out hF h3 hab
  have : (4 : ℝ) * ((univ.filter fun c => χ (c - a) = 1 ∧ χ (c - b) = 1).card : ℝ) =
      (Fintype.card F : ℝ) - 3 := by exact_mod_cast h
  linarith

/-- The tournament: for `a ≠ b`, `[a → b] + [b → a] = 1`. -/
theorem arrow_add_arrow (h3 : Fintype.card F % 4 = 3) {a b : F} (hab : a ≠ b) :
    (if χ (b - a) = 1 then (1 : ℝ) else 0) + (if χ (a - b) = 1 then 1 else 0) = 1 := by
  have := paley_tournament h3 hab
  by_cases h : χ (b - a) = 1
  · rw [ite_eq_left h, ite_eq_right (this.mp h)]
    norm_num
  · have h' : χ (a - b) = 1 := by
      by_contra h''
      exact h (this.mpr h'')
    rw [ite_eq_right h, ite_eq_left h']
    norm_num

/-- **The layer-`0` count**: for `a ≠ b` the number of `(y₀, y₁)` completing `(x₀, x₁) = (a, b)`
is `(q - 3)(q - 2)/4`. -/
theorem mirror_count_layer0 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a b : F}
    (hab : a ≠ b) :
    ∑ y₀ : F, ∑ y₁ : F, (if MirrorCond (a, b, y₀, y₁) then (1 : ℝ) else 0) =
      ((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2) / 4 := by
  set m : ℝ := ((Fintype.card F : ℝ) - 1) / 2 with hm
  -- the inner sum
  have hinner : ∀ y₀ : F, ∑ y₁ : F, (if MirrorCond (a, b, y₀, y₁) then (1 : ℝ) else 0) =
      (if y₀ ≠ a ∧ χ (y₀ - b) = 1 then 1 else 0) *
        (m - (if χ (b - a) = 1 then 1 else 0) - (if χ (y₀ - a) = 1 then 1 else 0)) := by
    intro y₀
    by_cases hy : y₀ ≠ a ∧ χ (y₀ - b) = 1
    · rw [ite_eq_left hy, one_mul]
      have hyb : y₀ ≠ b := ne_of_chi_eq hy.2 (Or.inl rfl)
      have hpt : ∀ y₁ : F, (if MirrorCond (a, b, y₀, y₁) then (1 : ℝ) else 0) =
          (if χ (y₁ - a) = 1 then 1 else 0) - (if y₁ = b ∧ χ (b - a) = 1 then 1 else 0) -
            (if y₁ = y₀ ∧ χ (y₀ - a) = 1 then 1 else 0) := by
        intro y₁
        by_cases ha : χ (y₁ - a) = 1
        · by_cases h1 : y₁ = b
          · have hM : ¬ MirrorCond (a, b, y₀, y₁) := fun h => h.2.2.1 h1.symm
            have hB : y₁ = b ∧ χ (b - a) = 1 := ⟨h1, by rw [← h1]; exact ha⟩
            have hC : ¬ (y₁ = y₀ ∧ χ (y₀ - a) = 1) := fun h => hyb (h.1.symm.trans h1)
            rw [ite_eq_right hM, ite_eq_left ha, ite_eq_left hB, ite_eq_right hC]
            norm_num
          · by_cases h2 : y₁ = y₀
            · have hM : ¬ MirrorCond (a, b, y₀, y₁) := fun h => h.2.2.2.1 h2.symm
              have hB : ¬ (y₁ = b ∧ χ (b - a) = 1) := fun h => h1 h.1
              have hC : y₁ = y₀ ∧ χ (y₀ - a) = 1 := ⟨h2, by rw [← h2]; exact ha⟩
              rw [ite_eq_right hM, ite_eq_left ha, ite_eq_right hB, ite_eq_left hC]
              norm_num
            · have hM : MirrorCond (a, b, y₀, y₁) :=
                ⟨hab, Ne.symm hy.1, fun e => h1 e.symm, fun e => h2 e.symm, hy.2, ha⟩
              have hB : ¬ (y₁ = b ∧ χ (b - a) = 1) := fun h => h1 h.1
              have hC : ¬ (y₁ = y₀ ∧ χ (y₀ - a) = 1) := fun h => h2 h.1
              rw [ite_eq_left hM, ite_eq_left ha, ite_eq_right hB, ite_eq_right hC]
              norm_num
        · have hM : ¬ MirrorCond (a, b, y₀, y₁) := fun h => ha h.2.2.2.2.2
          have hB : ¬ (y₁ = b ∧ χ (b - a) = 1) := fun h => ha (by rw [h.1]; exact h.2)
          have hC : ¬ (y₁ = y₀ ∧ χ (y₀ - a) = 1) := fun h => ha (by rw [h.1]; exact h.2)
          rw [ite_eq_right hM, ite_eq_right ha, ite_eq_right hB, ite_eq_right hC]
          norm_num
      simp only [hpt, sum_sub_distrib]
      rw [sum_arrow hF a]
      have e1 : ∑ y₁ : F, (if y₁ = b ∧ χ (b - a) = 1 then (1 : ℝ) else 0) =
          if χ (b - a) = 1 then 1 else 0 := by
        by_cases h : χ (b - a) = 1
        · rw [ite_eq_left h]
          simp only [h, and_true, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
        · rw [ite_eq_right h]
          simp only [h, and_false, ↓reduceIte, sum_const_zero]
      have e2 : ∑ y₁ : F, (if y₁ = y₀ ∧ χ (y₀ - a) = 1 then (1 : ℝ) else 0) =
          if χ (y₀ - a) = 1 then 1 else 0 := by
        by_cases h : χ (y₀ - a) = 1
        · rw [ite_eq_left h]
          simp only [h, and_true, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
        · rw [ite_eq_right h]
          simp only [h, and_false, ↓reduceIte, sum_const_zero]
      rw [e1, e2]
    · rw [ite_eq_right hy, zero_mul]
      refine sum_eq_zero fun y₁ _ => ?_
      have hM : ¬ MirrorCond (a, b, y₀, y₁) := fun h => hy ⟨Ne.symm h.2.1, h.2.2.2.2.1⟩
      rw [ite_eq_right hM]
  simp only [hinner]
  -- split the outer sum
  have hsplit : ∀ y₀ : F, (if y₀ ≠ a ∧ χ (y₀ - b) = 1 then (1 : ℝ) else 0) *
      (m - (if χ (b - a) = 1 then 1 else 0) - (if χ (y₀ - a) = 1 then 1 else 0)) =
      (m - (if χ (b - a) = 1 then 1 else 0)) *
          ((if χ (y₀ - b) = 1 then 1 else 0) - (if y₀ = a ∧ χ (a - b) = 1 then 1 else 0)) -
        (if χ (y₀ - b) = 1 ∧ χ (y₀ - a) = 1 then 1 else 0) := by
    intro y₀
    by_cases hya : y₀ = a
    · have h0 : ¬ χ (y₀ - a) = 1 := by rw [hya, sub_self, quadraticChar_zero]; decide
      have hL : ¬ (y₀ ≠ a ∧ χ (y₀ - b) = 1) := fun h => h.1 hya
      have hR : ¬ (χ (y₀ - b) = 1 ∧ χ (y₀ - a) = 1) := fun h => h0 h.2
      rw [ite_eq_right hL, ite_eq_right hR]
      by_cases hb : χ (y₀ - b) = 1
      · have hab' : y₀ = a ∧ χ (a - b) = 1 := ⟨hya, by rw [← hya]; exact hb⟩
        rw [ite_eq_left hb, ite_eq_left hab']
        ring
      · have hab' : ¬ (y₀ = a ∧ χ (a - b) = 1) := fun h => hb (by rw [hya]; exact h.2)
        rw [ite_eq_right hb, ite_eq_right hab']
        ring
    · have hn : ¬ (y₀ = a ∧ χ (a - b) = 1) := fun h => hya h.1
      rw [ite_eq_right hn]
      by_cases hb : χ (y₀ - b) = 1
      · have hL : y₀ ≠ a ∧ χ (y₀ - b) = 1 := ⟨hya, hb⟩
        rw [ite_eq_left hL, ite_eq_left hb]
        by_cases ha : χ (y₀ - a) = 1
        · rw [ite_eq_left ha, ite_eq_left (show χ (y₀ - b) = 1 ∧ χ (y₀ - a) = 1 from ⟨hb, ha⟩)]
          ring
        · rw [ite_eq_right ha, ite_eq_right (show ¬ (χ (y₀ - b) = 1 ∧ χ (y₀ - a) = 1) from
            fun h => ha h.2)]
          ring
      · have hL : ¬ (y₀ ≠ a ∧ χ (y₀ - b) = 1) := fun h => hb h.2
        rw [ite_eq_right hL, ite_eq_right hb, ite_eq_right (show ¬ (χ (y₀ - b) = 1 ∧
          χ (y₀ - a) = 1) from fun h => hb h.1)]
        ring
  simp only [hsplit, sum_sub_distrib, ← mul_sum]
  rw [sum_arrow hF b, sum_common_arrow hF h3 (Ne.symm hab)]
  have e3 : ∑ y₀ : F, (if y₀ = a ∧ χ (a - b) = 1 then (1 : ℝ) else 0) =
      if χ (a - b) = 1 then 1 else 0 := by
    by_cases h : χ (a - b) = 1
    · rw [ite_eq_left h]
      simp only [h, and_true, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
    · rw [ite_eq_right h]
      simp only [h, and_false, ↓reduceIte, sum_const_zero]
  rw [e3]
  have ht := arrow_add_arrow h3 hab
  have hprod : (if χ (b - a) = 1 then (1 : ℝ) else 0) * (if χ (a - b) = 1 then 1 else 0) = 0 := by
    have := paley_tournament h3 hab
    by_cases h : χ (b - a) = 1
    · rw [ite_eq_right (this.mp h), mul_zero]
    · rw [ite_eq_right h, zero_mul]
  rw [hm]
  linear_combination (-(((Fintype.card F : ℝ) - 1) / 2)) * ht + hprod

/-- The count of `(y₀, y₁)` for every `(x₀, x₁) = (a, b)`: zero on the diagonal. -/
theorem mirror_count_layer0' (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a b : F) :
    ∑ y₀ : F, ∑ y₁ : F, (if MirrorCond (a, b, y₀, y₁) then (1 : ℝ) else 0) =
      if a = b then 0 else ((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2) / 4 := by
  by_cases hab : a = b
  · rw [ite_eq_left hab]
    refine sum_eq_zero fun y₀ _ => sum_eq_zero fun y₁ _ => ?_
    exact ite_eq_right (fun h => h.1 hab)
  · rw [ite_eq_right hab]
    exact mirror_count_layer0 hF h3 hab

/-- **The layer swap with negation preserves the mirror condition**:
`(x₀, x₁, y₀, y₁) ↦ (-y₀, -y₁, -x₀, -x₁)` (the two mirror edges are exchanged). -/
theorem mirrorCond_neg_swap (x₀ x₁ y₀ y₁ : F) :
    MirrorCond (x₀, x₁, y₀, y₁) ↔ MirrorCond (-y₀, -y₁, -x₀, -x₁) := by
  have e1 : -x₀ - -y₁ = y₁ - x₀ := by ring
  have e2 : -x₁ - -y₀ = y₀ - x₁ := by ring
  simp only [MirrorCond, e1, e2, ne_eq, neg_inj]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h4, fun e => h2 e.symm, fun e => h3 e.symm, h1, h6, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h4, fun e => h2 e.symm, fun e => h3 e.symm, h1, h6, h5⟩

/-- **The layer-`1` count**: for `c ≠ d` the number of `(x₀, x₁)` completing `(y₀, y₁) = (c, d)` is
`(q - 3)(q - 2)/4`. -/
theorem mirror_count_layer1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c d : F) :
    ∑ x₀ : F, ∑ x₁ : F, (if MirrorCond (x₀, x₁, c, d) then (1 : ℝ) else 0) =
      if c = d then 0 else ((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2) / 4 := by
  have hswap : ∀ x₀ x₁ : F, (if MirrorCond (x₀, x₁, c, d) then (1 : ℝ) else 0) =
      (if MirrorCond (-c, -d, -x₀, -x₁) then 1 else 0) := by
    intro x₀ x₁
    by_cases h : MirrorCond (x₀, x₁, c, d)
    · rw [ite_eq_left h, ite_eq_left ((mirrorCond_neg_swap x₀ x₁ c d).mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((mirrorCond_neg_swap x₀ x₁ c d).mpr h'))]
  simp only [hswap]
  have hre : ∑ x₀ : F, ∑ x₁ : F, (if MirrorCond (-c, -d, -x₀, -x₁) then (1 : ℝ) else 0) =
      ∑ y₀ : F, ∑ y₁ : F, (if MirrorCond (-c, -d, y₀, y₁) then (1 : ℝ) else 0) := by
    refine Fintype.sum_equiv (Equiv.neg F) _ _ fun x₀ => ?_
    exact Fintype.sum_equiv (Equiv.neg F) _ _ fun x₁ => rfl
  rw [hre, mirror_count_layer0' hF h3]
  have : (-c = -d) ↔ (c = d) := neg_inj
  by_cases hcd : c = d
  · rw [ite_eq_left (this.mpr hcd), ite_eq_left hcd]
  · rw [ite_eq_right (fun h => hcd (this.mp h)), ite_eq_right hcd]

/-- **The mirror-edge replacement has layer-`0` half marginal `m_q`**: `P(x₀ = a, x₁ = b) =
[a ≠ b]/(q(q - 1))` (`lem:merge-repair`). -/
theorem mirrorLaw_half0 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h7 : 7 ≤ Fintype.card F) (hne : (injLabellings F mirrorGraph).Nonempty) (g : F → F → ℝ) :
    (mirrorLaw hne).expect (fun z => g (z (0, 0)) (z (1, 0))) =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ *
        ∑ a, ∑ b, if a = b then 0 else g a b := by
  set K : ℝ := ((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2) / 4 with hK
  have hq : (7 : ℝ) ≤ Fintype.card F := by exact_mod_cast h7
  have hK0 : K ≠ 0 := by rw [hK]; nlinarith
  rw [mirrorLaw_expect]
  simp only [(quadConfig_apply _).1, (quadConfig_apply _).2.1]
  have hnum : ∑ t : F × F × F × F, (if MirrorCond t then g t.1 t.2.1 else 0) =
      K * ∑ a, ∑ b, if a = b then 0 else g a b := by
    simp only [Fintype.sum_prod_type]
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    have e : ∑ y₀ : F, ∑ y₁ : F, (if MirrorCond (a, b, y₀, y₁) then g a b else 0) =
        g a b * ∑ y₀ : F, ∑ y₁ : F, (if MirrorCond (a, b, y₀, y₁) then (1 : ℝ) else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun y₀ _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun y₁ _ => ?_
      split_ifs <;> ring
    rw [e, mirror_count_layer0' hF h3]
    split_ifs <;> ring
  have hden : ∑ t : F × F × F × F, (if MirrorCond t then (1 : ℝ) else 0) =
      K * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1)) := by
    have := hnum
    have h1 := hnum
    have hg : ∑ t : F × F × F × F, (if MirrorCond t then (1 : ℝ) else 0) =
        K * ∑ a : F, ∑ b : F, (if a = b then (0 : ℝ) else 1) := by
      simp only [Fintype.sum_prod_type]
      rw [mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun b _ => ?_
      rw [mirror_count_layer0' hF h3]
      split_ifs <;> ring
    rw [hg]
    congr 1
    simp only [sum_ite_eq_zero_one, sum_const, card_univ, nsmul_eq_mul]
  rw [hnum, hden]
  have hq0 : (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) ≠ 0 := by
    apply mul_ne_zero <;> linarith
  field_simp

/-- **The mirror-edge replacement has layer-`1` half marginal `m_q`**: `P(y₀ = c, y₁ = d) =
[c ≠ d]/(q(q - 1))` (`lem:merge-repair`). -/
theorem mirrorLaw_half1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h7 : 7 ≤ Fintype.card F) (hne : (injLabellings F mirrorGraph).Nonempty) (g : F → F → ℝ) :
    (mirrorLaw hne).expect (fun z => g (z (0, 1)) (z (1, 1))) =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ *
        ∑ c, ∑ d, if c = d then 0 else g c d := by
  -- the layer swap with negation exchanges the two half marginals
  have hsym : (mirrorLaw hne).expect (fun z => g (z (0, 1)) (z (1, 1))) =
      (mirrorLaw hne).expect (fun z => g (-(z (0, 0))) (-(z (1, 0)))) := by
    rw [mirrorLaw_expect, mirrorLaw_expect]
    congr 1
    let σ : F × F × F × F ≃ F × F × F × F :=
      ⟨fun t => (-t.2.2.1, -t.2.2.2, -t.1, -t.2.1), fun t => (-t.2.2.1, -t.2.2.2, -t.1, -t.2.1),
        fun t => by simp, fun t => by simp⟩
    refine Fintype.sum_equiv σ _ _ fun t => ?_
    obtain ⟨x₀, x₁, y₀, y₁⟩ := t
    change (if MirrorCond (x₀, x₁, y₀, y₁) then g (quadConfig (x₀, x₁, y₀, y₁) (0, 1))
        (quadConfig (x₀, x₁, y₀, y₁) (1, 1)) else 0) =
      (if MirrorCond (-y₀, -y₁, -x₀, -x₁) then g (-(quadConfig (-y₀, -y₁, -x₀, -x₁) (0, 0)))
        (-(quadConfig (-y₀, -y₁, -x₀, -x₁) (1, 0))) else 0)
    simp only [(quadConfig_apply _).1, (quadConfig_apply _).2.1, (quadConfig_apply _).2.2.1,
      (quadConfig_apply _).2.2.2, neg_neg]
    by_cases h : MirrorCond (x₀, x₁, y₀, y₁)
    · rw [ite_eq_left h, ite_eq_left ((mirrorCond_neg_swap x₀ x₁ y₀ y₁).mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((mirrorCond_neg_swap x₀ x₁ y₀ y₁).mpr h'))]
  rw [hsym, mirrorLaw_half0 hF h3 h7 hne (fun a b => g (-a) (-b))]
  congr 1
  refine Fintype.sum_equiv (Equiv.neg F) _ _ fun a => ?_
  refine Fintype.sum_equiv (Equiv.neg F) _ _ fun b => ?_
  change (if a = b then (0 : ℝ) else g (-a) (-b)) = (if -a = -b then 0 else g (-a) (-b))
  by_cases hab : a = b
  · rw [ite_eq_left hab, ite_eq_left (by rw [hab])]
  · rw [ite_eq_right hab, ite_eq_right (fun h => hab (neg_inj.mp h))]

end Sarkozy.PartVRecords
