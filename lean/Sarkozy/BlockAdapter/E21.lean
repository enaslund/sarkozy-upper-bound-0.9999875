module

public import Sarkozy.BlockAdapter.KernelBounds
public import Sarkozy.BlockAdapter.MiddleLayer

@[expose] public section

/-!
# The per-prime cap of the cut E21, proved (`lem:layer12-caps`(b) for E21)

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(ii) (the cap `k_E` of the layer
cut E21); `lem:layer12-geometry`(c).

The `E` graph `G_{E,2}` has no edges, so at the layer swap the half law `μ` is the uniform law on
the injective triples `x : {0,1,2} → 𝔽_p` and the cut kernel is the disjointness indicator
`K(x, x') = 1{x(U⁺) ∩ x'(U⁺) = ∅}` (no cross pairs). Two elementary facts give the per-prime
bounds of the cut operator `A = T_{K/Z}`:

* **upper bound `A ⪯ 1`** (Schur test, `kernel_quad_upper`): the row mean
  `R(x) = E_{x'} K(x, x')` is the same at every injective `x`, because `μ` and `K` are invariant
  under the permutations of `𝔽_p`, which act transitively on injective triples
  (`exists_perm_comp_eq`); so `R = Z` on the support;
* **lower bound `A ⪰ -9/(pZ)`** (collision bound, `kernel_quad_lower`): `1 - K` is at most the
  number of coincidences `x_c = x'_d`, whose row and column means are `9/p` because every vertex
  marginal of `μ` is uniform (`graphLaw_vertex_uniform`); and `Z ≥ 1 - 9/p`.

With the rational gate `allp_e21Check`, **`middleE21Caps_proved`** proves V1–B6's per-prime
certificate `MiddleE21Caps i` on all 33 pieces at the recorded constants `(allpG i 4, allpB i 4)`:
`-g p^{-1/2} ⪯ A_p ⪯ 1 ≤ 1 + B/p`. No hypothesis remains for E21.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.Cuts Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData

/-! ## Permutations act transitively on injective maps -/

/-- Any two injective maps into a finite type differ by a permutation of the target. -/
theorem exists_perm_comp_eq {α β : Type*} [Fintype β] [DecidableEq β] {x y : α → β}
    (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ σ : Equiv.Perm β, ⇑σ ∘ x = y := by
  classical
  let e : {c // c ∈ Set.range x} ≃ {c // c ∈ Set.range y} :=
    (Equiv.ofInjective x hx).symm.trans (Equiv.ofInjective y hy)
  refine ⟨e.extendSubtype, funext fun a => ?_⟩
  rw [Function.comp_apply, Equiv.extendSubtype_apply_of_mem e (x a) ⟨a, rfl⟩]
  have h : (Equiv.ofInjective x hx).symm ⟨x a, ⟨a, rfl⟩⟩ = a := Equiv.ofInjective_symm_apply hx a
  simp only [e, Equiv.trans_apply, h, Equiv.ofInjective_apply]

/-- Postcomposition with a permutation. -/
def postcomp {α β : Type*} (σ : Equiv.Perm β) : (α → β) ≃ (α → β) where
  toFun y := σ ∘ y
  invFun y := σ.symm ∘ y
  left_inv y := by
    funext a
    simp
  right_inv y := by
    funext a
    simp

/-! ## The cut E21 at one prime -/

section E21

variable {p : ℕ} [Fact p.Prime]

theorem matchLayer_crossPairs : matchLayer.crossPairs = ∅ := by
  ext q
  simp [SpecData.crossPairs, SpecData.sgn, layerData, matchGraph]

/-- The cut kernel of E21 is the disjointness indicator. -/
theorem matchLayer_cutK (x x' : matchLayer.cut.Half → ZMod p) :
    matchLayer.cutK x x' = if Disjoint (univ.image x) (univ.image x') then 1 else 0 := by
  rw [SpecData.cutK_eq_prod, matchLayer_crossPairs, Finset.prod_empty, mul_one]

/-- The half labellings of E21 are the injective maps. -/
theorem matchHalf_mem_iff (x : matchLayer.cut.Half → ZMod p) :
    x ∈ injLabellings (ZMod p) matchLayer.halfGraph ↔ Function.Injective x := by
  rw [mem_injLabellings_iff_feasible]
  simp [Feasible, SpecData.halfGraph, layerData, matchGraph, Function.Injective]

variable (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)

theorem matchHalf_weight_comp (σ : Equiv.Perm (ZMod p)) (x : matchLayer.cut.Half → ZMod p) :
    (matchLayer.halfLaw hne).weight (⇑σ ∘ x) = (matchLayer.halfLaw hne).weight x := by
  simp only [SpecData.halfLaw, graphLaw, matchHalf_mem_iff, σ.injective.of_comp_iff]

theorem matchHalf_injective_of_weight {x : matchLayer.cut.Half → ZMod p}
    (hx : (matchLayer.halfLaw hne).weight x ≠ 0) : Function.Injective x := by
  rw [← matchHalf_mem_iff]
  by_contra h
  apply hx
  simp only [SpecData.halfLaw, graphLaw, h, ↓reduceIte]

theorem matchLayer_cutK_comp (σ : Equiv.Perm (ZMod p)) (x x' : matchLayer.cut.Half → ZMod p) :
    matchLayer.cutK (⇑σ ∘ x) (⇑σ ∘ x') = matchLayer.cutK x x' := by
  rw [matchLayer_cutK, matchLayer_cutK, ← Finset.image_image, ← Finset.image_image]
  simp only [Finset.disjoint_image σ.injective]

/-- The row mean `R(x) = E_{x'} K(x, x')` of E21. -/
noncomputable def matchRow (x : matchLayer.cut.Half → ZMod p) : ℝ :=
  ∑ y, (matchLayer.halfLaw hne).weight y * matchLayer.cutK x y

theorem matchRow_comp (σ : Equiv.Perm (ZMod p)) (x : matchLayer.cut.Half → ZMod p) :
    matchRow hne (⇑σ ∘ x) = matchRow hne x := by
  unfold matchRow
  refine (Fintype.sum_equiv (postcomp σ) _ _ fun y => ?_).symm
  change _ = (matchLayer.halfLaw hne).weight (⇑σ ∘ y) * matchLayer.cutK (⇑σ ∘ x) (⇑σ ∘ y)
  rw [matchHalf_weight_comp, matchLayer_cutK_comp]

/-- **The row mean of E21 is `Z` on the support** (transitivity of the permutations). -/
theorem matchRow_eq_cutZ (x : matchLayer.cut.Half → ZMod p)
    (hx : (matchLayer.halfLaw hne).weight x ≠ 0) : matchRow hne x = matchLayer.cutZ hne := by
  have hxi := matchHalf_injective_of_weight hne hx
  have hconst : ∀ y, (matchLayer.halfLaw hne).weight y ≠ 0 → matchRow hne y = matchRow hne x := by
    intro y hy
    obtain ⟨σ, hσ⟩ := exists_perm_comp_eq hxi (matchHalf_injective_of_weight hne hy)
    rw [← hσ, matchRow_comp]
  have hZ : matchLayer.cutZ hne =
      ∑ y, (matchLayer.halfLaw hne).weight y * matchRow hne y := by
    unfold SpecData.cutZ
    rw [FiniteLaw.expect_product]
    rfl
  rw [hZ]
  calc matchRow hne x = ∑ y, (matchLayer.halfLaw hne).weight y * matchRow hne x := by
        rw [← Finset.sum_mul, (matchLayer.halfLaw hne).total, one_mul]
    _ = ∑ y, (matchLayer.halfLaw hne).weight y * matchRow hne y :=
        Finset.sum_congr rfl fun y _ => by
          by_cases hy : (matchLayer.halfLaw hne).weight y = 0
          · rw [hy, zero_mul, zero_mul]
          · rw [hconst y hy]

/-- **Every vertex marginal of the E21 half law is uniform**: `P(x'_d = c) = 1/p`. -/
theorem matchHalf_vertex (d : matchLayer.cut.Half) (c : ZMod p) :
    ∑ y, (matchLayer.halfLaw hne).weight y * (if y d = c then (1 : ℝ) else 0) = 1 / p := by
  have h := graphLaw_vertex_uniform matchLayer.halfGraph (matchLayer.half_nonempty hne) d
    (fun z => if z = c then (1 : ℝ) else 0)
  change (matchLayer.halfLaw hne).expect (fun y => if y d = c then (1 : ℝ) else 0) = _
  rw [show matchLayer.halfLaw hne =
    graphLaw matchLayer.halfGraph (matchLayer.half_nonempty hne) from rfl, h,
    FiniteLaw.expect_uniform]
  simp [ZMod.card]

/-- The number of coincidences `x_c = x'_d`. -/
noncomputable def coll (x y : matchLayer.cut.Half → ZMod p) : ℝ :=
  ∑ c, ∑ d, if x c = y d then (1 : ℝ) else 0

theorem card_matchHalf : Fintype.card matchLayer.cut.Half = 3 := by
  rw [Fintype.card_congr (layerHalfEquiv (Fin 3) (matchGraph (Fin 2)) matchGraph_swap)]
  simp

theorem one_sub_cutK_le_coll (x y : matchLayer.cut.Half → ZMod p) :
    1 - matchLayer.cutK x y ≤ coll x y := by
  rw [matchLayer_cutK]
  have hnn : ∀ c d, (0 : ℝ) ≤ if x c = y d then (1 : ℝ) else 0 := fun c d => by
    split_ifs <;> norm_num
  by_cases h : Disjoint (univ.image x) (univ.image y)
  · simp only [h, ↓reduceIte, sub_self]
    exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => hnn c d
  · simp only [h, ↓reduceIte, sub_zero]
    obtain ⟨a, ha, hb⟩ := Finset.not_disjoint_iff.mp h
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hb
    have h1 : (if x c = y d then (1 : ℝ) else 0) = 1 := by simp [hd]
    calc (1 : ℝ) = if x c = y d then (1 : ℝ) else 0 := h1.symm
      _ ≤ ∑ d', if x c = y d' then (1 : ℝ) else 0 :=
          Finset.single_le_sum (fun d' _ => hnn c d') (Finset.mem_univ d)
      _ ≤ coll x y :=
          Finset.single_le_sum (f := fun c' => ∑ d', if x c' = y d' then (1 : ℝ) else 0)
            (fun c' _ => Finset.sum_nonneg fun d' _ => hnn c' d') (Finset.mem_univ c)

theorem coll_row (x : matchLayer.cut.Half → ZMod p) :
    ∑ y, (matchLayer.halfLaw hne).weight y * coll x y = 9 / p := by
  unfold coll
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ c d, ∑ y, (matchLayer.halfLaw hne).weight y * (if x c = y d then (1 : ℝ) else 0) =
      1 / p := by
    intro c d
    rw [← matchHalf_vertex hne d (x c)]
    exact Finset.sum_congr rfl fun y _ => by simp only [eq_comm]
  rw [Finset.sum_congr rfl fun c _ => (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun d _ => h c d))]
  simp only [Finset.sum_const, Finset.card_univ, card_matchHalf, nsmul_eq_mul]
  ring

theorem coll_col (y : matchLayer.cut.Half → ZMod p) :
    ∑ x, (matchLayer.halfLaw hne).weight x * coll x y = 9 / p := by
  unfold coll
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ c d, ∑ x, (matchLayer.halfLaw hne).weight x * (if x c = y d then (1 : ℝ) else 0) =
      1 / p := fun c d => matchHalf_vertex hne c (y d)
  rw [Finset.sum_congr rfl fun c _ => (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun d _ => h c d))]
  simp only [Finset.sum_const, Finset.card_univ, card_matchHalf, nsmul_eq_mul]
  ring

theorem matchLayer_cutK_le_one (x y : matchLayer.cut.Half → ZMod p) :
    matchLayer.cutK x y ≤ 1 := by
  rw [matchLayer_cutK]
  split_ifs <;> norm_num

/-- `Z ≥ 1 - 9/p` for E21. -/
theorem matchLayer_cutZ_ge : 1 - 9 / (p : ℝ) ≤ matchLayer.cutZ hne := by
  have hZ : matchLayer.cutZ hne =
      ∑ x, (matchLayer.halfLaw hne).weight x * matchRow hne x := by
    unfold SpecData.cutZ
    rw [FiniteLaw.expect_product]
    rfl
  have hR : ∀ x, 1 - 9 / (p : ℝ) ≤ matchRow hne x := by
    intro x
    have h1 : ∑ y, (matchLayer.halfLaw hne).weight y * (1 - coll x y) ≤ matchRow hne x :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
        (by linarith [one_sub_cutK_le_coll x y]) ((matchLayer.halfLaw hne).nonneg y)
    have h2 : ∑ y, (matchLayer.halfLaw hne).weight y * (1 - coll x y) = 1 - 9 / p := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, (matchLayer.halfLaw hne).total,
        coll_row hne x]
    linarith
  rw [hZ]
  calc 1 - 9 / (p : ℝ) = ∑ x, (matchLayer.halfLaw hne).weight x * (1 - 9 / (p : ℝ)) := by
        rw [← Finset.sum_mul, (matchLayer.halfLaw hne).total, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hR x) ((matchLayer.halfLaw hne).nonneg x)

end E21

/-! ## The per-prime certificate -/

/-- **The per-prime cap of E21**: if `9/(p - 9) ≤ g p^{-1/2}`, `p > 9` and `B ≥ 0`, then
`-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p`. -/
theorem e21_layerCutCap {p : ℕ} [Fact p.Prime] {g B : ℝ} (hB : 0 ≤ B) (hp : 9 < (p : ℝ))
    (hg : 9 / ((p : ℝ) - 9) ≤ g * (√(p : ℝ))⁻¹) :
    LayerCutCap (Fin 3) (matchGraph (Fin 2)) matchGraph_swap g B p := by
  intro hne v
  have hZpos := matchLayer.cutZ_pos hne
  have hZge := matchLayer_cutZ_ge hne
  have hp0 : (0 : ℝ) < p := by linarith
  have hv := sq_nonneg ‖v‖
  constructor
  · have h := kernel_quad_lower (matchLayer.halfLaw hne) matchLayer.cutK coll
      matchLayer_cutK_le_one one_sub_cutK_le_coll hZpos (fun x => (coll_row hne x).le)
      (fun y => (coll_col hne y).le) v
    have hc : 9 / (p : ℝ) / matchLayer.cutZ hne ≤ g * (√(p : ℝ))⁻¹ := by
      have hZ' : ((p : ℝ) - 9) / p ≤ matchLayer.cutZ hne := by
        have : ((p : ℝ) - 9) / p = 1 - 9 / p := by field_simp
        rw [this]
        exact hZge
      have hpos : 0 < ((p : ℝ) - 9) / p := div_pos (by linarith) hp0
      calc 9 / (p : ℝ) / matchLayer.cutZ hne ≤ 9 / (p : ℝ) / (((p : ℝ) - 9) / p) :=
            div_le_div_of_nonneg_left (by positivity) hpos hZ'
        _ = 9 / ((p : ℝ) - 9) := by
            field_simp
        _ ≤ _ := hg
    calc -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ -(9 / (p : ℝ) / matchLayer.cutZ hne) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hv
      _ ≤ _ := h
  · have h := kernel_quad_upper (matchLayer.halfLaw hne) matchLayer.cutK
      (fun x y => matchLayer.cutK_nonneg x y) (fun x y => matchLayer.cutK_symm y x) hZpos
      (fun x hx => (matchRow_eq_cutZ hne x hx).le) v
    have hBp : 0 ≤ B / p := div_nonneg hB hp0.le
    calc _ ≤ ‖v‖ ^ 2 := h
      _ ≤ (1 + B / p) * ‖v‖ ^ 2 := by nlinarith

/-- The rational gate gives `9/(p - 9) ≤ g p^{-1/2}`. -/
theorem e21_gate {g s₀ p : ℝ} (hg : 0 ≤ g) (hs₀ : 0 < s₀) (hchk : 9 + 9 * g / s₀ ≤ g * s₀)
    (hp : s₀ ^ 2 ≤ p) (hp9 : 9 < p) : 9 / (p - 9) ≤ g * (√p)⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hs : s₀ ≤ √p := Real.le_sqrt_of_sq_le hp
  have hsp : 0 < √p := lt_of_lt_of_le hs₀ hs
  have hsq : √p ^ 2 = p := Real.sq_sqrt hp0.le
  have h1 : 9 * g / √p ≤ 9 * g / s₀ :=
    div_le_div_of_nonneg_left (by positivity) hs₀ hs
  have h2 : 9 * √p + 9 * g ≤ g * p := by
    have e : 9 * √p + 9 * g = √p * (9 + 9 * g / √p) := by
      field_simp
    rw [e]
    calc √p * (9 + 9 * g / √p) ≤ √p * (9 + 9 * g / s₀) :=
          mul_le_mul_of_nonneg_left (by linarith) hsp.le
      _ ≤ √p * (g * s₀) := mul_le_mul_of_nonneg_left hchk hsp.le
      _ ≤ √p * (g * √p) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs hg) hsp.le
      _ = g * p := by linear_combination g * hsq
  rw [div_le_iff₀ (by linarith), ← div_eq_mul_inv]
  rw [div_mul_eq_mul_div, le_div_iff₀ hsp]
  nlinarith

/-- **`MiddleE21Caps` holds on every piece** (`lem:layer12-caps`(b) for E21, at the recorded
constants): no hypothesis remains for the cut E21. -/
theorem middleE21Caps_proved (i : Fin 33) : MiddleE21Caps i := by
  intro p _ _ hp _
  obtain ⟨hk, -, hg, hB, -, -⟩ := allp_capCheck i 4 (by decide)
  have hchk := allp_e21Check i
  set k := allpLog2 i
  have hs₀ : (0 : ℝ) < 2 ^ (k / 2) := by positivity
  have hsq : ((2 : ℝ) ^ (k / 2)) ^ 2 ≤ p := by
    have h1 : (2 : ℕ) ^ (k / 2 * 2) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self k 2)
    have h2 : (2 : ℕ) ^ (k / 2 * 2) ≤ p := (h1.trans hk).trans hp
    rw [← pow_mul]
    exact_mod_cast h2
  have hp9 : (9 : ℝ) < p := by
    have := pieceStart_gt_36 i
    have hp' : ((pieceStart i : ℕ) : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  apply e21_layerCutCap (by exact_mod_cast hB) hp9
  refine e21_gate (by exact_mod_cast hg) hs₀ ?_ hsq hp9
  have h := (Rat.cast_le (K := ℝ)).mpr hchk
  push_cast at h
  exact h

end Sarkozy.BlockAdapter
