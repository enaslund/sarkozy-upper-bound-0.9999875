module

public import Sarkozy.PartVRecords.MergeMarginals

@[expose] public section

/-!
# The queried pairs of the merge replacements (`lem:merge-repair`, first sentence)

`paper/sections/21_middle_records.tex`, `lem:merge-repair`: the replacements "have uniform queried
pairs on the ordered strict-square pairs". At one prime `p ≡ 3 (mod 4)`, `p ≥ 7`:
* the first-coordinate law: the designated pair `(x₀, y₀)` has weight `[x₀ → y₀] · 2/(p(p - 1))`
  (`firstLaw_queried`);
* the mirror-edge law: the designated pair `(x₁, y₀)` (of `G₀₀`, `G₁₀`) has weight
  `[x₁ → y₀] · 2/(p(p - 1))` (`mirrorLaw_queried10`), from the count
  `#{(x₀, y₁)} = (p - 2)(p - 3)/2` for `u → v` (`mirror_count_queried`); the pair `(x₀, y₁)` (of
  `G₀₁`, `G₁₁`) follows by the layer swap with negation (`mirrorLaw_queried01`).
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- `∑_x [x → u] = (q - 1)/2` for `q ≡ 3 (mod 4)`. -/
theorem sum_in_arrow (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (u : F) :
    ∑ x : F, (if χ (u - x) = 1 then (1 : ℝ) else 0) = ((Fintype.card F : ℝ) - 1) / 2 := by
  rw [sum_boole]
  have h := card_in hF h3 u
  have : (2 : ℝ) * ((univ.filter fun b => χ (u - b) = 1).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    exact_mod_cast h
  linarith

/-- **The count for the designated pair `(x₁, y₀) = (u, v)` of the mirror law**: for `u → v`,
`#{(x₀, y₁)} = (q - 2)(q - 3)/2`. -/
theorem mirror_count_queried (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {u v : F}
    (huv : χ (v - u) = 1) :
    ∑ x₀ : F, ∑ y₁ : F, (if MirrorCond (x₀, u, v, y₁) then (1 : ℝ) else 0) =
      ((Fintype.card F : ℝ) - 2) * ((Fintype.card F : ℝ) - 3) / 2 := by
  set m : ℝ := ((Fintype.card F : ℝ) - 1) / 2 with hm
  have hne : u ≠ v := (ne_of_chi_eq huv (Or.inl rfl)).symm
  have hvu : ¬ χ (u - v) = 1 := (paley_tournament h3 hne).mp huv
  -- the inner sum over `y₁`
  have hinner : ∀ x₀ : F, ∑ y₁ : F, (if MirrorCond (x₀, u, v, y₁) then (1 : ℝ) else 0) =
      (if x₀ ≠ u ∧ x₀ ≠ v then 1 else 0) *
        (m - (if χ (u - x₀) = 1 then 1 else 0) - (if χ (v - x₀) = 1 then 1 else 0)) := by
    intro x₀
    by_cases hx : x₀ ≠ u ∧ x₀ ≠ v
    · rw [ite_eq_left hx, one_mul]
      have hpt : ∀ y₁ : F, (if MirrorCond (x₀, u, v, y₁) then (1 : ℝ) else 0) =
          (if χ (y₁ - x₀) = 1 then 1 else 0) - (if y₁ = u ∧ χ (u - x₀) = 1 then 1 else 0) -
            (if y₁ = v ∧ χ (v - x₀) = 1 then 1 else 0) := by
        intro y₁
        by_cases ha : χ (y₁ - x₀) = 1
        · by_cases h1 : y₁ = u
          · have hM : ¬ MirrorCond (x₀, u, v, y₁) := fun h => h.2.2.1 h1.symm
            have hB : y₁ = u ∧ χ (u - x₀) = 1 := ⟨h1, by rw [← h1]; exact ha⟩
            have hC : ¬ (y₁ = v ∧ χ (v - x₀) = 1) := fun h => hne (h1.symm.trans h.1)
            rw [ite_eq_right hM, ite_eq_left ha, ite_eq_left hB, ite_eq_right hC]
            norm_num
          · by_cases h2 : y₁ = v
            · have hM : ¬ MirrorCond (x₀, u, v, y₁) := fun h => h.2.2.2.1 h2.symm
              have hB : ¬ (y₁ = u ∧ χ (u - x₀) = 1) := fun h => h1 h.1
              have hC : y₁ = v ∧ χ (v - x₀) = 1 := ⟨h2, by rw [← h2]; exact ha⟩
              rw [ite_eq_right hM, ite_eq_left ha, ite_eq_right hB, ite_eq_left hC]
              norm_num
            · have hM : MirrorCond (x₀, u, v, y₁) :=
                ⟨hx.1, hx.2, fun e => h1 e.symm, fun e => h2 e.symm, huv, ha⟩
              have hB : ¬ (y₁ = u ∧ χ (u - x₀) = 1) := fun h => h1 h.1
              have hC : ¬ (y₁ = v ∧ χ (v - x₀) = 1) := fun h => h2 h.1
              rw [ite_eq_left hM, ite_eq_left ha, ite_eq_right hB, ite_eq_right hC]
              norm_num
        · have hM : ¬ MirrorCond (x₀, u, v, y₁) := fun h => ha h.2.2.2.2.2
          have hB : ¬ (y₁ = u ∧ χ (u - x₀) = 1) := fun h => ha (by rw [h.1]; exact h.2)
          have hC : ¬ (y₁ = v ∧ χ (v - x₀) = 1) := fun h => ha (by rw [h.1]; exact h.2)
          rw [ite_eq_right hM, ite_eq_right ha, ite_eq_right hB, ite_eq_right hC]
          norm_num
      simp only [hpt, sum_sub_distrib]
      rw [sum_arrow hF x₀]
      have e1 : ∑ y₁ : F, (if y₁ = u ∧ χ (u - x₀) = 1 then (1 : ℝ) else 0) =
          if χ (u - x₀) = 1 then 1 else 0 := by
        by_cases h : χ (u - x₀) = 1
        · rw [ite_eq_left h]
          simp only [h, and_true, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
        · rw [ite_eq_right h]
          simp only [h, and_false, ↓reduceIte, sum_const_zero]
      have e2 : ∑ y₁ : F, (if y₁ = v ∧ χ (v - x₀) = 1 then (1 : ℝ) else 0) =
          if χ (v - x₀) = 1 then 1 else 0 := by
        by_cases h : χ (v - x₀) = 1
        · rw [ite_eq_left h]
          simp only [h, and_true, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
        · rw [ite_eq_right h]
          simp only [h, and_false, ↓reduceIte, sum_const_zero]
      rw [e1, e2]
    · rw [ite_eq_right hx, zero_mul]
      refine sum_eq_zero fun y₁ _ => ?_
      have hM : ¬ MirrorCond (x₀, u, v, y₁) := fun h => hx ⟨h.1, h.2.1⟩
      rw [ite_eq_right hM]
  simp only [hinner]
  -- the outer sum over `x₀`
  have hsplit : ∀ x₀ : F, (if x₀ ≠ u ∧ x₀ ≠ v then (1 : ℝ) else 0) *
      (m - (if χ (u - x₀) = 1 then 1 else 0) - (if χ (v - x₀) = 1 then 1 else 0)) =
      m * (1 - (if x₀ = u then 1 else 0) - (if x₀ = v then 1 else 0)) -
        ((if χ (u - x₀) = 1 then 1 else 0) - (if x₀ = v ∧ χ (u - v) = 1 then 1 else 0)) -
        ((if χ (v - x₀) = 1 then 1 else 0) - (if x₀ = u ∧ χ (v - u) = 1 then 1 else 0)) := by
    intro x₀
    have h0u : ¬ χ (u - u) = 1 := by rw [sub_self, quadraticChar_zero]; decide
    have h0v : ¬ χ (v - v) = 1 := by rw [sub_self, quadraticChar_zero]; decide
    by_cases hxu : x₀ = u
    · have hL : ¬ (x₀ ≠ u ∧ x₀ ≠ v) := fun h => h.1 hxu
      have hxv : ¬ x₀ = v := fun h => hne (hxu.symm.trans h)
      rw [ite_eq_right hL, ite_eq_left hxu, ite_eq_right hxv,
        ite_eq_right (show ¬ (x₀ = v ∧ χ (u - v) = 1) from fun h => hxv h.1),
        ite_eq_left (show x₀ = u ∧ χ (v - u) = 1 from ⟨hxu, huv⟩)]
      rw [hxu, ite_eq_right h0u, ite_eq_left huv]
      ring
    · by_cases hxv : x₀ = v
      · have hL : ¬ (x₀ ≠ u ∧ x₀ ≠ v) := fun h => h.2 hxv
        rw [ite_eq_right hL, ite_eq_right hxu, ite_eq_left hxv,
          ite_eq_right (show ¬ (x₀ = v ∧ χ (u - v) = 1) from fun h => hvu h.2),
          ite_eq_right (show ¬ (x₀ = u ∧ χ (v - u) = 1) from fun h => hxu h.1)]
        rw [hxv, ite_eq_right hvu, ite_eq_right h0v]
        ring
      · have hL : x₀ ≠ u ∧ x₀ ≠ v := ⟨hxu, hxv⟩
        rw [ite_eq_left hL, ite_eq_right hxu, ite_eq_right hxv,
          ite_eq_right (show ¬ (x₀ = v ∧ χ (u - v) = 1) from fun h => hxv h.1),
          ite_eq_right (show ¬ (x₀ = u ∧ χ (v - u) = 1) from fun h => hxu h.1)]
        ring
  simp only [hsplit, sum_sub_distrib, ← mul_sum]
  rw [sum_in_arrow hF h3 u, sum_in_arrow hF h3 v]
  have e3 : ∑ x₀ : F, (if x₀ = v ∧ χ (u - v) = 1 then (1 : ℝ) else 0) = 0 := by
    refine sum_eq_zero fun x₀ _ => ite_eq_right fun h => hvu h.2
  have e4 : ∑ x₀ : F, (if x₀ = u ∧ χ (v - u) = 1 then (1 : ℝ) else 0) = 1 := by
    simp only [huv, and_true, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
  rw [e3, e4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Finset.sum_ite_eq', mem_univ,
    ↓reduceIte]
  rw [hm]
  ring

theorem mirror_count_queried' (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (u v : F) :
    ∑ x₀ : F, ∑ y₁ : F, (if MirrorCond (x₀, u, v, y₁) then (1 : ℝ) else 0) =
      if χ (v - u) = 1 then ((Fintype.card F : ℝ) - 2) * ((Fintype.card F : ℝ) - 3) / 2
      else 0 := by
  by_cases huv : χ (v - u) = 1
  · rw [ite_eq_left huv]
    exact mirror_count_queried hF h3 huv
  · rw [ite_eq_right huv]
    refine sum_eq_zero fun x₀ _ => sum_eq_zero fun y₁ _ => ?_
    exact ite_eq_right fun h => huv h.2.2.2.2.1

/-- The total count of the mirror law: `q(q - 1)(q - 3)(q - 2)/4`. -/
theorem mirror_count_total (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) :
    ∑ t : F × F × F × F, (if MirrorCond t then (1 : ℝ) else 0) =
      (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) *
        (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2) / 4) := by
  simp only [Fintype.sum_prod_type]
  have h : ∀ a b : F, ∑ y₀ : F, ∑ y₁ : F, (if MirrorCond (a, b, y₀, y₁) then (1 : ℝ) else 0) =
      (if a = b then (0 : ℝ) else 1) *
        (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2) / 4) := by
    intro a b
    rw [mirror_count_layer0' hF h3]
    split_ifs <;> ring
  simp only [h, ← sum_mul, sum_ite_eq_zero_one, sum_const, card_univ, nsmul_eq_mul]

/-- **The designated pair `(x₁, y₀)` of the mirror law is uniform on the strict-square pairs**
(the replacements of `G₀₀`, `G₁₀`; `lem:merge-repair`). -/
theorem mirrorLaw_queried10 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h7 : 7 ≤ Fintype.card F) (hne : (injLabellings F mirrorGraph).Nonempty) (g : F → F → ℝ) :
    (mirrorLaw hne).expect (fun z => g (z (1, 0)) (z (0, 1))) =
      ∑ u, ∑ v, if χ (v - u) = 1 then
        2 / ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1)) * g u v else 0 := by
  have hq : (7 : ℝ) ≤ Fintype.card F := by exact_mod_cast h7
  rw [mirrorLaw_expect, mirror_count_total hF h3]
  simp only [(quadConfig_apply _).2.1, (quadConfig_apply _).2.2.1]
  have hreord : ∑ t : F × F × F × F, (if MirrorCond t then g t.2.1 t.2.2.1 else 0) =
      ∑ u : F, ∑ v : F, ∑ x₀ : F, ∑ y₁ : F,
        (if MirrorCond (x₀, u, v, y₁) then g u v else 0) := by
    simp only [Fintype.sum_prod_type]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_comm]
  rw [hreord, sum_div]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun v _ => ?_
  have e : ∑ x₀ : F, ∑ y₁ : F, (if MirrorCond (x₀, u, v, y₁) then g u v else 0) =
      g u v * ∑ x₀ : F, ∑ y₁ : F, (if MirrorCond (x₀, u, v, y₁) then (1 : ℝ) else 0) := by
    rw [mul_sum]
    refine sum_congr rfl fun x₀ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun y₁ _ => ?_
    split_ifs <;> ring
  rw [e, mirror_count_queried' hF h3]
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hq2 : (Fintype.card F : ℝ) - 2 ≠ 0 := by linarith
  have hq3 : (Fintype.card F : ℝ) - 3 ≠ 0 := by linarith
  split_ifs
  · field_simp
    ring
  · simp

/-- **The designated pair `(x₀, y₁)` of the mirror law is uniform on the strict-square pairs**
(the replacements of `G₀₁`, `G₁₁`), by the layer swap with negation. -/
theorem mirrorLaw_queried01 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h7 : 7 ≤ Fintype.card F) (hne : (injLabellings F mirrorGraph).Nonempty) (g : F → F → ℝ) :
    (mirrorLaw hne).expect (fun z => g (z (0, 0)) (z (1, 1))) =
      ∑ u, ∑ v, if χ (v - u) = 1 then
        2 / ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1)) * g u v else 0 := by
  have hsym : (mirrorLaw hne).expect (fun z => g (z (0, 0)) (z (1, 1))) =
      (mirrorLaw hne).expect (fun z => g (-(z (0, 1))) (-(z (1, 0)))) := by
    rw [mirrorLaw_expect, mirrorLaw_expect]
    congr 1
    let σ : F × F × F × F ≃ F × F × F × F :=
      ⟨fun t => (-t.2.2.1, -t.2.2.2, -t.1, -t.2.1), fun t => (-t.2.2.1, -t.2.2.2, -t.1, -t.2.1),
        fun t => by simp, fun t => by simp⟩
    refine Fintype.sum_equiv σ _ _ fun t => ?_
    obtain ⟨x₀, x₁, y₀, y₁⟩ := t
    change (if MirrorCond (x₀, x₁, y₀, y₁) then g (quadConfig (x₀, x₁, y₀, y₁) (0, 0))
        (quadConfig (x₀, x₁, y₀, y₁) (1, 1)) else 0) =
      (if MirrorCond (-y₀, -y₁, -x₀, -x₁) then g (-(quadConfig (-y₀, -y₁, -x₀, -x₁) (0, 1)))
        (-(quadConfig (-y₀, -y₁, -x₀, -x₁) (1, 0))) else 0)
    simp only [(quadConfig_apply _).1, (quadConfig_apply _).2.1, (quadConfig_apply _).2.2.1,
      (quadConfig_apply _).2.2.2, neg_neg]
    by_cases h : MirrorCond (x₀, x₁, y₀, y₁)
    · rw [ite_eq_left h, ite_eq_left ((mirrorCond_neg_swap x₀ x₁ y₀ y₁).mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((mirrorCond_neg_swap x₀ x₁ y₀ y₁).mpr h'))]
  have h10 := mirrorLaw_queried10 hF h3 h7 hne (fun a b => g (-b) (-a))
  rw [hsym, h10]
  -- reindex `(u, v) ↦ (-v, -u)`
  rw [sum_comm]
  refine Fintype.sum_equiv (Equiv.neg F) _ _ fun v => ?_
  refine Fintype.sum_equiv (Equiv.neg F) _ _ fun u => ?_
  change (if χ (v - u) = 1 then 2 / ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1)) *
      g (-v) (-u) else 0) =
    (if χ (-u - -v) = 1 then 2 / ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1)) *
      g (-v) (-u) else 0)
  rw [show -u - -v = v - u by ring]

/-- **The designated pair `(x₀, y₀)` of the first-coordinate law is uniform on the strict-square
pairs** (the replacements of `G₀₂`, `G₁₂`; `lem:merge-repair`). -/
theorem firstLaw_queried (hF : ringChar F ≠ 2) (g : F → F → ℝ) :
    (firstLaw F hF).expect (fun z => g (z (0, 0)) (z (0, 1))) =
      ∑ u, ∑ v, if χ (v - u) = 1 then
        2 / ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1)) * g u v else 0 := by
  have hq := card_gt_one_real (F := F)
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  rw [expect_firstLaw]
  simp only [(quadConfig_apply _).1, (quadConfig_apply _).2.2.1, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  have e : ∀ x₁ y₁ : F, firstWeight (u, x₁, v, y₁) * g u v =
      (2 / (1 - 1 / (Fintype.card F : ℝ)) *
        ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ ^ 2 *
          (if χ (v - u) = 1 then 1 else 0) * g u v) *
        ((if u = x₁ then 0 else 1) * (if v = y₁ then 0 else 1)) := by
    intro x₁ y₁
    rw [firstWeight_split]
    ring
  simp only [e]
  set C := 2 / (1 - 1 / (Fintype.card F : ℝ)) *
    ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ ^ 2 *
      (if χ (v - u) = 1 then 1 else 0) * g u v with hC
  have hfac : ∑ x₁ : F, ∑ y₁ : F, C * ((if u = x₁ then (0 : ℝ) else 1) *
      (if v = y₁ then (0 : ℝ) else 1)) =
      C * ((∑ x₁ : F, (if u = x₁ then (0 : ℝ) else 1)) *
        (∑ y₁ : F, (if v = y₁ then (0 : ℝ) else 1))) := by
    rw [Finset.sum_mul_sum, mul_sum]
    refine sum_congr rfl fun x₁ _ => ?_
    rw [mul_sum]
  rw [hfac, sum_ite_eq_zero_one u, sum_ite_eq_zero_one v, hC]
  have h1q : 1 - 1 / (Fintype.card F : ℝ) = ((Fintype.card F : ℝ) - 1) / Fintype.card F := by
    field_simp
  rw [h1q]
  split_ifs
  · field_simp
  · simp

end Sarkozy.PartVRecords
