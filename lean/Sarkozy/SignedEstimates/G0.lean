module

public import Sarkozy.SignedEstimates.Sums

@[expose] public section

/-!
# The density `g₀` of the half marginal of the reference fold record (`lem:old-f-law`(a)) (E1)

`paper/sections/21_middle_records.tex`, `lem:old-f-law`(a).

At one prime `p ≡ 3 (4)`, `p ≥ 19`, with `k_p = (p - 3)/4`:

* `mem_inj_iff`: a pair of halves is a labelling of `G_{F,2}` iff both are in `H_F`, the six
  labels are distinct, `x₀ → y₂` and `y₀ → x₂`;
* `N0 x`: the fibre count `N₀(x)`; **`N0_eq`**: `N₀(x) = (p-5)(k_p-1)((p-3)/2 - e₀₁ - e₁₂)` on
  `H_F`, written as `(p-5)(p-7)(p - 5 - χ(x₁ - x₀) - χ(x₂ - x₁))/8` (`2e = 1 + χ`);
* `m0_weight_eq`, `card_inj_eq`: `m₀(x) = N₀(x)/|Inj|`, `|Inj| = ∑_x N₀(x)`;
  **`card_inj_val`**: `|Inj| = (p-5)(p-7) p(p-1)(p-3)(p-4)/16`;
* **`g0_eq`**: `g₀ = (p-2)(p - 5 - χ(x₁ - x₀) - χ(x₂ - x₁))/((p-3)(p-4))` on `H_F` (the paper's
  `(p-2)(p-3-2e₀₁-2e₁₂)/((p-3)(p-4))`);
* **`g0_bound`**: `|g₀ - 1| ≤ η_F = 2(p-1)/((p-3)(p-4)) ≤ e₀ = 2q/((1-3q)(1-4q))` on `H_F`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedEstimates

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-! ## Labellings of the fold graph as pairs of halves -/

/-- **A pair of halves is a labelling of `G_{F,2}`** iff both halves are in `H_F`, the six labels
are distinct, `x₀ → y₂` and `y₀ → x₂`. -/
theorem mem_inj_iff (x y : Fin 3 → F) :
    toY (x, y) ∈ injLabellings F (foldGraph (Fin 2)) ↔
      HF x ∧ HF y ∧ (∀ i j, x i ≠ y j) ∧ χ (y 2 - x 0) = 1 ∧ χ (x 2 - y 0) = 1 := by
  rw [mem_injLabellings_iff_feasible]
  have hv0 : ∀ o, toY (x, y) (o, 0) = x o := fun o => by simp [toY]
  have hv1 : ∀ o, toY (x, y) (o, 1) = y o := fun o => by simp [toY]
  have hE : ∀ o o' : Fin 3, ∀ ℓ ℓ' : Fin 2, ((o, ℓ), (o', ℓ')) ∈ (foldGraph (Fin 2)).E ↔
      o = 0 ∧ o' = 2 := fun o o' ℓ ℓ' => mem_foldGraph (Fin 2) _
  constructor
  · rintro ⟨hinj, hedge⟩
    have e : ∀ ℓ ℓ' : Fin 2, χ (toY (x, y) (2, ℓ') - toY (x, y) (0, ℓ)) = 1 := fun ℓ ℓ' =>
      hedge ((0, ℓ), (2, ℓ')) ((hE _ _ _ _).mpr ⟨rfl, rfl⟩) (mem_univ _) (mem_univ _)
    refine ⟨⟨fun o o' h => ?_, ?_⟩, ⟨fun o o' h => ?_, ?_⟩, fun i j h => ?_, ?_, ?_⟩
    · have := hinj (o, 0) (mem_univ _) (o', 0) (mem_univ _) (by rw [hv0, hv0]; exact h)
      exact (Prod.mk.inj this).1
    · have := e 0 0; rwa [hv0, hv0] at this
    · have := hinj (o, 1) (mem_univ _) (o', 1) (mem_univ _) (by rw [hv1, hv1]; exact h)
      exact (Prod.mk.inj this).1
    · have := e 1 1; rwa [hv1, hv1] at this
    · have := hinj (i, 0) (mem_univ _) (j, 1) (mem_univ _) (by rw [hv0, hv1]; exact h)
      exact absurd (Prod.mk.inj this).2 (by decide)
    · have := e 0 1; rwa [hv0, hv1] at this
    · have := e 1 0; rwa [hv0, hv1] at this
  · rintro ⟨hx, hy, hxy, h1, h2⟩
    refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
    · obtain ⟨o, ℓ⟩ := a
      obtain ⟨o', ℓ'⟩ := b
      fin_cases ℓ <;> fin_cases ℓ'
      · simp only [Fin.zero_eta, Fin.isValue, hv0] at hab
        rw [hx.1 hab]
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, hv0, hv1] at hab
        exact absurd hab (hxy o o')
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, hv0, hv1] at hab
        exact absurd hab.symm (hxy o' o)
      · simp only [Fin.isValue, Fin.mk_one, hv1] at hab
        rw [hy.1 hab]
    · obtain ⟨⟨o, ℓ⟩, ⟨o', ℓ'⟩⟩ := e
      obtain ⟨rfl, rfl⟩ := (hE _ _ _ _).mp he
      fin_cases ℓ <;> fin_cases ℓ'
      · simp only [Fin.zero_eta, Fin.isValue, hv0]; exact hx.2
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, hv0, hv1]; exact h1
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, hv0, hv1]; exact h2
      · simp only [Fin.isValue, Fin.mk_one, hv1]; exact hy.2

/-! ## The fibre count `N₀` -/

/-- The fibre count `N₀(x) = #{y : (x, y) ∈ Inj_p(G_{F,2})}` (`lem:old-f-law`(a)). -/
noncomputable def N0 (x : Fin 3 → F) : ℝ :=
  ∑ y, (if toY (x, y) ∈ injLabellings F (foldGraph (Fin 2)) then (1 : ℝ) else 0)

omit [Field F] in
/-- The labels other than five distinct ones. -/
theorem sum_excl5 {p₁ p₂ p₃ p₄ p₅ : F} (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h14 : p₁ ≠ p₄)
    (h15 : p₁ ≠ p₅) (h23 : p₂ ≠ p₃) (h24 : p₂ ≠ p₄) (h25 : p₂ ≠ p₅) (h34 : p₃ ≠ p₄)
    (h35 : p₃ ≠ p₅) (h45 : p₄ ≠ p₅) :
    ∑ w, (if w ≠ p₁ ∧ w ≠ p₂ ∧ w ≠ p₃ ∧ w ≠ p₄ ∧ w ≠ p₅ then (1 : ℝ) else 0) =
      (Fintype.card F : ℝ) - 5 := by
  have e : ∀ w, (if w ≠ p₁ ∧ w ≠ p₂ ∧ w ≠ p₃ ∧ w ≠ p₄ ∧ w ≠ p₅ then (1 : ℝ) else 0) =
      1 - (if p₁ = w then 1 else 0) - (if p₂ = w then 1 else 0) - (if p₃ = w then 1 else 0) -
        (if p₄ = w then 1 else 0) - (if p₅ = w then 1 else 0) := by
    intro w
    by_cases e1 : w = p₁
    · rw [e1]; simp [Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15]
    by_cases e2 : w = p₂
    · rw [e2]; simp [h12, Ne.symm h23, Ne.symm h24, Ne.symm h25]
    by_cases e3 : w = p₃
    · rw [e3]; simp [h13, h23, Ne.symm h34, Ne.symm h35]
    by_cases e4 : w = p₄
    · rw [e4]; simp [h14, h24, h34, Ne.symm h45]
    by_cases e5 : w = p₅
    · rw [e5]; simp [h15, h25, h35, h45]
    simp [e1, e2, e3, e4, e5, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5]
  simp only [e, sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte, sum_const, card_univ,
    nsmul_eq_mul, mul_one]
  ring

omit [Field F] in
/-- A filter count with two points removed. -/
theorem sum_excl_two (P : F → Prop) [DecidablePred P] {b d : F} (hbd : b ≠ d) :
    ∑ z, (if P z ∧ z ≠ b ∧ z ≠ d then (1 : ℝ) else 0) =
      ((univ.filter P).card : ℝ) - (if P b then 1 else 0) - (if P d then 1 else 0) := by
  have e : ∀ z, (if P z ∧ z ≠ b ∧ z ≠ d then (1 : ℝ) else 0) =
      (if P z then 1 else 0) - (if b = z then (if P b then 1 else 0) else 0) -
        (if d = z then (if P d then 1 else 0) else 0) := by
    intro z
    by_cases e1 : z = b
    · rw [e1]; by_cases hp : P b <;> simp [hp, Ne.symm hbd]
    by_cases e2 : z = d
    · rw [e2]; by_cases hp : P d <;> simp [hp, hbd]
    simp [e1, e2, Ne.symm e1, Ne.symm e2]
  simp only [e, sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← Finset.sum_boole]

omit [Field F] in
/-- A filter count with one point removed. -/
theorem sum_excl_one (P : F → Prop) [DecidablePred P] (b : F) :
    ∑ z, (if P z ∧ z ≠ b then (1 : ℝ) else 0) =
      ((univ.filter P).card : ℝ) - (if P b then 1 else 0) := by
  have e : ∀ z, (if P z ∧ z ≠ b then (1 : ℝ) else 0) =
      (if P z then 1 else 0) - (if b = z then (if P b then 1 else 0) else 0) := by
    intro z
    by_cases e1 : z = b
    · rw [e1]; by_cases hp : P b <;> simp [hp]
    simp [e1, Ne.symm e1]
  simp only [e, sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← Finset.sum_boole]

theorem card_common_outR (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a a' : F}
    (haa : a ≠ a') :
    ((univ.filter fun c => χ (c - a) = 1 ∧ χ (c - a') = 1).card : ℝ) =
      ((Fintype.card F : ℝ) - 3) / 4 := by
  have h := card_common_out hR h3 haa
  have h' : ((4 * ((univ.filter fun c => χ (c - a) = 1 ∧ χ (c - a') = 1).card : ℤ) : ℤ) : ℝ) =
      (((Fintype.card F : ℤ) - 3 : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  linarith

theorem card_common_inR (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a a' : F}
    (haa : a ≠ a') :
    ((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℝ) =
      ((Fintype.card F : ℝ) - 3) / 4 := by
  have h := card_common_in hR h3 haa
  have h' : ((4 * ((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) : ℤ) : ℝ) =
      (((Fintype.card F : ℤ) - 3 : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  linarith

theorem card_inR (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a : F) :
    ((univ.filter fun c => χ (a - c) = 1).card : ℝ) = ((Fintype.card F : ℝ) - 1) / 2 := by
  have h := card_in hR h3 a
  have h' : ((2 * ((univ.filter fun c => χ (a - c) = 1).card : ℤ) : ℤ) : ℝ) =
      (((Fintype.card F : ℤ) - 1 : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  linarith

theorem ind_chi (h : F) : (if χ h = 1 then (1 : ℝ) else 0) = (1 + χ h) / 2 - (if h = 0 then 1 / 2
    else 0) := by
  by_cases h0 : h = 0
  · subst h0; simp
  · rcases quadraticChar_dichotomy h0 with e | e <;> simp [e, h0]

/-- The explicit condition for `(x, ![c, w, z]) ∈ Inj_p(G_{F,2})` at a half `x ∈ H_F`. -/
def Ecnd (x : Fin 3 → F) (c w z : F) : Prop :=
  χ (z - c) = 1 ∧ w ≠ c ∧ w ≠ z ∧ x 0 ≠ c ∧ x 1 ≠ c ∧ x 2 ≠ c ∧ x 0 ≠ w ∧ x 1 ≠ w ∧ x 2 ≠ w ∧
    x 0 ≠ z ∧ x 1 ≠ z ∧ x 2 ≠ z ∧ χ (z - x 0) = 1 ∧ χ (x 2 - c) = 1

instance (x : Fin 3 → F) (c w z : F) : Decidable (Ecnd x c w z) := by
  unfold Ecnd; infer_instance

theorem mem_inj_tri {x : Fin 3 → F} (hx : HF x) (c w z : F) :
    toY (x, ![c, w, z]) ∈ injLabellings F (foldGraph (Fin 2)) ↔ Ecnd x c w z := by
  rw [mem_inj_iff, HF_tri]
  unfold Ecnd
  constructor
  · rintro ⟨-, ⟨h1, h2, h3⟩, hd, h4, h5⟩
    exact ⟨h1, h2, h3, hd 0 0, hd 1 0, hd 2 0, hd 0 1, hd 1 1, hd 2 1, hd 0 2, hd 1 2, hd 2 2,
      h4, h5⟩
  · rintro ⟨h1, h2, h3, d00, d10, d20, d01, d11, d21, d02, d12, d22, h4, h5⟩
    refine ⟨hx, ⟨h1, h2, h3⟩, fun i j => ?_, h4, h5⟩
    fin_cases i <;> fin_cases j <;> assumption

theorem N0_tri {x : Fin 3 → F} (hx : HF x) :
    N0 x = ∑ c, ∑ z, ∑ w, (if Ecnd x c w z then (1 : ℝ) else 0) := by
  unfold N0
  rw [← Equiv.sum_comp tri, Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun z _ => sum_congr rfl fun w _ => ?_
  change (if toY (x, ![c, w, z]) ∈ injLabellings F (foldGraph (Fin 2)) then (1 : ℝ) else 0) = _
  by_cases h : Ecnd x c w z
  · simp only [(mem_inj_tri hx c w z).mpr h, h, ↓reduceIte]
  · have h' : toY (x, ![c, w, z]) ∉ injLabellings F (foldGraph (Fin 2)) :=
      fun hm => h ((mem_inj_tri hx c w z).mp hm)
    simp only [h', h, ↓reduceIte]

/-- The condition after summing `y₁ = w`. -/
def Ecnd2 (x : Fin 3 → F) (c z : F) : Prop :=
  χ (z - c) = 1 ∧ x 0 ≠ c ∧ x 1 ≠ c ∧ x 2 ≠ c ∧ x 0 ≠ z ∧ x 1 ≠ z ∧ x 2 ≠ z ∧
    χ (z - x 0) = 1 ∧ χ (x 2 - c) = 1

instance (x : Fin 3 → F) (c z : F) : Decidable (Ecnd2 x c z) := by
  unfold Ecnd2; infer_instance

theorem N0_w {x : Fin 3 → F} (hx : HF x) (c z : F) :
    ∑ w, (if Ecnd x c w z then (1 : ℝ) else 0) =
      if Ecnd2 x c z then (Fintype.card F : ℝ) - 5 else 0 := by
  obtain ⟨h01, h02, h12⟩ := HF_ne hx
  by_cases h : Ecnd2 x c z
  · obtain ⟨hzc, h0c, h1c, h2c, h0z, h1z, h2z, hz0, h2c'⟩ := h
    have hcz : c ≠ z := (ne_of_chi_one hzc).symm
    have e : ∀ w, (if Ecnd x c w z then (1 : ℝ) else 0) =
        if w ≠ c ∧ w ≠ z ∧ w ≠ x 0 ∧ w ≠ x 1 ∧ w ≠ x 2 then 1 else 0 := by
      intro w
      unfold Ecnd
      by_cases hw : w ≠ c ∧ w ≠ z ∧ w ≠ x 0 ∧ w ≠ x 1 ∧ w ≠ x 2
      · obtain ⟨w1, w2, w3, w4, w5⟩ := hw
        simp only [hzc, w1, w2, h0c, h1c, h2c, Ne.symm w3, Ne.symm w4, Ne.symm w5, h0z, h1z,
          h2z, hz0, h2c', w3, w4, w5, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      · have : ¬ (χ (z - c) = 1 ∧ w ≠ c ∧ w ≠ z ∧ x 0 ≠ c ∧ x 1 ≠ c ∧ x 2 ≠ c ∧ x 0 ≠ w ∧
            x 1 ≠ w ∧ x 2 ≠ w ∧ x 0 ≠ z ∧ x 1 ≠ z ∧ x 2 ≠ z ∧ χ (z - x 0) = 1 ∧
            χ (x 2 - c) = 1) := fun hh =>
          hw ⟨hh.2.1, hh.2.2.1, fun e => hh.2.2.2.2.2.2.1 e.symm,
            fun e => hh.2.2.2.2.2.2.2.1 e.symm, fun e => hh.2.2.2.2.2.2.2.2.1 e.symm⟩
        simp only [this, hw, ↓reduceIte]
    rw [sum_congr rfl fun w _ => e w, sum_excl5 hcz (Ne.symm h0c) (Ne.symm h1c) (Ne.symm h2c)
      (Ne.symm h0z) (Ne.symm h1z) (Ne.symm h2z) h01 h02 h12]
    have : Ecnd2 x c z := ⟨hzc, h0c, h1c, h2c, h0z, h1z, h2z, hz0, h2c'⟩
    simp only [this, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    refine sum_eq_zero fun w _ => ?_
    have : ¬ Ecnd x c w z := fun hh => h ⟨hh.1, hh.2.2.2.1, hh.2.2.2.2.1, hh.2.2.2.2.2.1,
      hh.2.2.2.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2.2.2.2.2.1,
      hh.2.2.2.2.2.2.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
    simp only [this, ↓reduceIte]

/-- The condition on `y₀ = c` after summing `y₂`. -/
def Ecnd3 (x : Fin 3 → F) (c : F) : Prop := x 0 ≠ c ∧ x 1 ≠ c ∧ χ (x 2 - c) = 1

instance (x : Fin 3 → F) (c : F) : Decidable (Ecnd3 x c) := by
  unfold Ecnd3; infer_instance

theorem N0_z (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {x : Fin 3 → F} (hx : HF x)
    (c : F) :
    ∑ z, (if Ecnd2 x c z then (Fintype.card F : ℝ) - 5 else 0) =
      if Ecnd3 x c then ((Fintype.card F : ℝ) - 5) * (((Fintype.card F : ℝ) - 3) / 4 - 1 -
        (if χ (x 1 - c) = 1 ∧ χ (x 1 - x 0) = 1 then 1 else 0)) else 0 := by
  obtain ⟨h01, h02, h12⟩ := HF_ne hx
  by_cases h : Ecnd3 x c
  · obtain ⟨h0c, h1c, h2c⟩ := h
    have e : ∀ z, (if Ecnd2 x c z then (Fintype.card F : ℝ) - 5 else 0) =
        ((Fintype.card F : ℝ) - 5) *
          (if (χ (z - c) = 1 ∧ χ (z - x 0) = 1) ∧ z ≠ x 1 ∧ z ≠ x 2 then 1 else 0) := by
      intro z
      unfold Ecnd2
      by_cases hz : (χ (z - c) = 1 ∧ χ (z - x 0) = 1) ∧ z ≠ x 1 ∧ z ≠ x 2
      · obtain ⟨⟨hzc, hz0⟩, hz1, hz2⟩ := hz
        have h0z : x 0 ≠ z := (ne_of_chi_one hz0).symm
        simp only [hzc, hz0, h0c, h1c, ne_of_chi_one h2c, h0z, Ne.symm hz1, Ne.symm hz2, h2c,
          hz1, hz2, ne_eq, not_false_eq_true, and_self, ↓reduceIte, mul_one]
      · have : ¬ (χ (z - c) = 1 ∧ x 0 ≠ c ∧ x 1 ≠ c ∧ x 2 ≠ c ∧ x 0 ≠ z ∧ x 1 ≠ z ∧ x 2 ≠ z ∧
            χ (z - x 0) = 1 ∧ χ (x 2 - c) = 1) := fun hh =>
          hz ⟨⟨hh.1, hh.2.2.2.2.2.2.2.1⟩, fun e => hh.2.2.2.2.2.1 e.symm,
            fun e => hh.2.2.2.2.2.2.1 e.symm⟩
        simp only [this, hz, ↓reduceIte, mul_zero]
    rw [sum_congr rfl fun z _ => e z, ← mul_sum, sum_excl_two _ h12,
      card_common_outR hR h3 (Ne.symm h0c)]
    have hP2 : χ (x 2 - c) = 1 ∧ χ (x 2 - x 0) = 1 := ⟨h2c, hx.2⟩
    have : Ecnd3 x c := ⟨h0c, h1c, h2c⟩
    simp only [hP2, this, and_self, ↓reduceIte]
    ring
  · simp only [h, ↓reduceIte]
    refine sum_eq_zero fun z _ => ?_
    have : ¬ Ecnd2 x c z := fun hh => h ⟨hh.2.1, hh.2.2.1, hh.2.2.2.2.2.2.2.2⟩
    simp only [this, ↓reduceIte]

/-- **The fibre count** (`lem:old-f-law`(a)):
`N₀(x) = (p-5)(p-7)(p - 5 - χ(x₁ - x₀) - χ(x₂ - x₁))/8`
on `H_F`, i.e. `(p-5)(k_p-1)((p-3)/2 - e₀₁ - e₁₂)`. -/
theorem N0_eq (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {x : Fin 3 → F} (hx : HF x) :
    N0 x = ((Fintype.card F : ℝ) - 5) * ((Fintype.card F : ℝ) - 7) *
      ((Fintype.card F : ℝ) - 5 - χ (x 1 - x 0) - χ (x 2 - x 1)) / 8 := by
  obtain ⟨h01, h02, h12⟩ := HF_ne hx
  rw [N0_tri hx]
  simp only [N0_w hx, N0_z hR h3 hx]
  set n : ℝ := (Fintype.card F : ℝ) with hn
  have e : ∀ c, (if Ecnd3 x c then (n - 5) * ((n - 3) / 4 - 1 -
      (if χ (x 1 - c) = 1 ∧ χ (x 1 - x 0) = 1 then 1 else 0)) else 0) =
      ((n - 5) * ((n - 3) / 4 - 1)) * (if χ (x 2 - c) = 1 ∧ c ≠ x 0 ∧ c ≠ x 1 then 1 else 0) -
        (n - 5) * (if χ (x 1 - x 0) = 1 then
          (if (χ (x 2 - c) = 1 ∧ χ (x 1 - c) = 1) ∧ c ≠ x 0 then 1 else 0) else 0) := by
    intro c
    unfold Ecnd3
    by_cases hc : x 0 ≠ c ∧ x 1 ≠ c ∧ χ (x 2 - c) = 1
    · obtain ⟨h0c, h1c, h2c⟩ := hc
      simp only [h0c, h1c, h2c, Ne.symm h0c, Ne.symm h1c, ne_eq, not_false_eq_true, and_self,
        true_and, ↓reduceIte, mul_one]
      by_cases h10 : χ (x 1 - x 0) = 1 <;> by_cases h1c' : χ (x 1 - c) = 1 <;>
        simp [h10, h1c', -quadraticChar_apply]
      ring
    · have hc' : ¬ (χ (x 2 - c) = 1 ∧ c ≠ x 0 ∧ c ≠ x 1) := fun hh =>
        hc ⟨Ne.symm hh.2.1, Ne.symm hh.2.2, hh.1⟩
      have hc'' : ¬ ((χ (x 2 - c) = 1 ∧ χ (x 1 - c) = 1) ∧ c ≠ x 0) := fun hh => by
        refine hc ⟨Ne.symm hh.2, ?_, hh.1.1⟩
        exact (ne_of_chi_one hh.1.2)
      simp only [hc, hc', hc'', ↓reduceIte, mul_zero, sub_zero, ite_self]
  rw [sum_congr rfl fun c _ => e c, sum_sub_distrib, ← mul_sum, ← mul_sum,
    sum_excl_two _ h01]
  have hin := card_inR hR h3 (x 2)
  by_cases h10 : χ (x 1 - x 0) = 1
  · simp only [h10, ↓reduceIte]
    rw [sum_excl_one, card_common_inR hR h3 (Ne.symm h12), hin]
    have hP : χ (x 2 - x 0) = 1 ∧ χ (x 1 - x 0) = 1 := ⟨hx.2, h10⟩
    simp only [hx.2, hP, and_self, ↓reduceIte, Int.cast_one]
    rw [← hn]
    by_cases h21 : χ (x 2 - x 1) = 1
    · simp only [h21, ↓reduceIte, Int.cast_one]
      ring
    · have hχ' : (χ (x 2 - x 1) : ℝ) = -1 := by
        rcases chiR_ne_cases (sub_ne_zero.mpr (Ne.symm h12)) with e | e
        · exact absurd (by exact_mod_cast e) h21
        · exact e
      simp only [h21, ↓reduceIte, hχ']
      ring
  · have hχ : (χ (x 1 - x 0) : ℝ) = -1 := by
      rcases chiR_ne_cases (sub_ne_zero.mpr (Ne.symm h01)) with e | e
      · exact absurd (by exact_mod_cast e) h10
      · exact e
    simp only [h10, ↓reduceIte, sum_const_zero, mul_zero, sub_zero, hin, hx.2, hχ]
    rw [← hn]
    by_cases h21 : χ (x 2 - x 1) = 1
    · simp only [h21, ↓reduceIte, Int.cast_one]
      ring
    · have hχ' : (χ (x 2 - x 1) : ℝ) = -1 := by
        rcases chiR_ne_cases (sub_ne_zero.mpr (Ne.symm h12)) with e | e
        · exact absurd (by exact_mod_cast e) h21
        · exact e
      simp only [h21, ↓reduceIte, hχ']
      ring

/-! ## The half marginal `m₀` and its density `g₀` -/

theorem N0_off {x : Fin 3 → F} (hx : ¬ HF x) : N0 x = 0 := by
  unfold N0
  refine sum_eq_zero fun y _ => ?_
  have : toY (x, y) ∉ injLabellings F (foldGraph (Fin 2)) := fun h =>
    hx ((mem_inj_iff x y).mp h).1
  simp only [this, ↓reduceIte]

section Law

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

/-- `m₀(x) = N₀(x)/|Inj_p(G_{F,2})|`. -/
theorem m0_weight_eq (x : Fin 3 → F) :
    (m0 hF).weight x = N0 x / ((injLabellings F (foldGraph (Fin 2))).card : ℝ) := by
  change (∑ Y, if lay Y 0 = x then (K0 hF).weight Y else 0) = _
  rw [← Equiv.sum_comp pairEquiv, Fintype.sum_prod_type, sum_eq_single x]
  · change (∑ y, if lay (toY (x, y)) 0 = x then (K0 hF).weight (toY (x, y)) else 0) = _
    simp only [lay_toY_zero, ↓reduceIte]
    unfold N0
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    change (if toY (x, y) ∈ injLabellings F (foldGraph (Fin 2)) then
      1 / ((injLabellings F (foldGraph (Fin 2))).card : ℝ) else 0) = _
    split_ifs <;> simp
  · intro x' _ hx'
    refine sum_eq_zero fun y _ => ?_
    change (if lay (toY (x', y)) 0 = x then (K0 hF).weight (toY (x', y)) else 0) = 0
    simp only [lay_toY_zero, hx', ↓reduceIte]
  · intro h; exact absurd (mem_univ x) h

end Law

/-- `|Inj_p(G_{F,2})| = ∑_x N₀(x)`. -/
theorem card_inj_eq :
    ((injLabellings F (foldGraph (Fin 2))).card : ℝ) = ∑ x : Fin 3 → F, N0 x := by
  have e : ((injLabellings F (foldGraph (Fin 2))).card : ℝ) =
      ∑ Y, (if Y ∈ injLabellings F (foldGraph (Fin 2)) then (1 : ℝ) else 0) := by
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one]
  rw [e, ← Equiv.sum_comp pairEquiv, Fintype.sum_prod_type]
  rfl

theorem sumR_chi_left (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a : F) :
    ∑ w, (χ (a - w) : ℝ) = 0 := by
  simp only [chiR_swap h3 a, sum_neg_distrib, sumR_chi hR, neg_zero]

/-- **`|Inj_p(G_{F,2})| = (p-5)(p-7) p(p-1)(p-3)(p-4)/16`** (`lem:old-f-law`(a): the mean
`N̄₀ = (p-3)(p-4)(p-5)(p-7)/(8(p-2))`). -/
theorem card_inj_val (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) :
    ((injLabellings F (foldGraph (Fin 2))).card : ℝ) =
      ((Fintype.card F : ℝ) - 5) * ((Fintype.card F : ℝ) - 7) * ((Fintype.card F : ℝ) *
        ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 4)) /
        16 := by
  set n : ℝ := (Fintype.card F : ℝ) with hn
  rw [card_inj_eq]
  have e : ∀ x : Fin 3 → F, N0 x = if HF x then (n - 5) * (n - 7) / 8 *
      (n - 5 - χ (x 1 - x 0) - χ (x 2 - x 1)) else 0 := by
    intro x
    by_cases hx : HF x
    · simp only [hx, ↓reduceIte, N0_eq hR h3 hx]; ring
    · simp only [hx, ↓reduceIte, N0_off hx]
  simp only [e]
  rw [sumHF]
  have hz : ∀ c z, χ (z - c) = 1 → ∑ w, (if w ≠ c ∧ w ≠ z then (n - 5) * (n - 7) / 8 *
      (n - 5 - χ (![c, w, z] 1 - ![c, w, z] 0) - χ (![c, w, z] 2 - ![c, w, z] 1)) else 0) =
      (n - 5) * (n - 7) / 8 * ((n - 3) * (n - 4)) := by
    intro c z hzc
    have e2 : ∀ w, (n - 5) * (n - 7) / 8 *
        (n - 5 - χ (![c, w, z] 1 - ![c, w, z] 0) - χ (![c, w, z] 2 - ![c, w, z] 1)) =
        (n - 5) * (n - 7) / 8 * (n - 5 - χ (w - c) - χ (z - w)) := fun w => rfl
    simp only [e2]
    rw [sum_excl2 (ne_of_chi_one hzc).symm]
    have hzc' : (χ (z - c) : ℝ) = 1 := by rw [hzc]; simp
    simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, sumR_chi hR,
      sumR_chi_left hR h3, sub_self, quadraticChar_zero, Int.cast_zero, hzc']
    rw [← hn]
    ring
  have hc : ∀ c, ∑ z, (if χ (z - c) = 1 then ∑ w, (if w ≠ c ∧ w ≠ z then (n - 5) * (n - 7) / 8 *
      (n - 5 - χ (![c, w, z] 1 - ![c, w, z] 0) - χ (![c, w, z] 2 - ![c, w, z] 1)) else 0)
      else 0) = (n - 5) * (n - 7) / 8 * ((n - 3) * (n - 4)) * ((n - 1) / 2) := by
    intro c
    rw [sum_ite_congr (hz c), sum_out]
    simp only [sum_const, card_univ, nsmul_eq_mul, ← sum_mul, sumR_chi hR, zero_mul]
    rw [← hn]
    ring
  simp only [hc, sum_const, card_univ, nsmul_eq_mul]
  rw [← hn]
  ring

/-- The paper's `e₀ = 2q/((1-3q)(1-4q))` at `q = 1/p`, written `2p/((p-3)(p-4))`. -/
noncomputable def e0 (n : ℝ) : ℝ := 2 * n / ((n - 3) * (n - 4))

theorem e0_eq_paper {n : ℝ} (hn : 5 ≤ n) :
    e0 n = 2 * (1 / n) / ((1 - 3 * (1 / n)) * (1 - 4 * (1 / n))) := by
  unfold e0
  have h0 : n ≠ 0 := by intro h; rw [h] at hn; norm_num at hn
  have h3 : n - 3 ≠ 0 := by intro h; linarith
  have h4 : n - 4 ≠ 0 := by intro h; linarith
  field_simp

/-- **The density `g₀`** (`lem:old-f-law`(a)):
`g₀ = (p-2)(p - 5 - χ(x₁ - x₀) - χ(x₂ - x₁))/((p-3)(p-4))` on `H_F`, the paper's
`(p-2)(p-3-2e₀₁-2e₁₂)/((p-3)(p-4))`. -/
theorem g0_eq (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)
    (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) {x : Fin 3 → F} (hx : HF x) :
    g0 hF x = ((Fintype.card F : ℝ) - 2) *
      ((Fintype.card F : ℝ) - 5 - χ (x 1 - x 0) - χ (x 2 - x 1)) /
      (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 4)) := by
  unfold g0
  rw [m0_weight_eq, card_inj_val hR h3, N0_eq hR h3 hx, Hcard_eq hR]
  have h19' : (19 : ℝ) ≤ Fintype.card F := by exact_mod_cast h19
  set n : ℝ := (Fintype.card F : ℝ)
  have : n ≠ 0 := by intro h; linarith
  have : n - 1 ≠ 0 := by intro h; linarith
  have : n - 3 ≠ 0 := by intro h; linarith
  have : n - 4 ≠ 0 := by intro h; linarith
  have : n - 5 ≠ 0 := by intro h; linarith
  have : n - 7 ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- **`|g₀ - 1| ≤ η_F ≤ e₀` on `H_F`** (`lem:old-f-law`(a):
`‖g₀ - 1‖_∞ = η_F = 2(p-1)/((p-3)(p-4)) ≤ e₀`). -/
theorem g0_bound (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)
    (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) {x : Fin 3 → F} (hx : HF x) :
    |g0 hF x - 1| ≤ e0 (Fintype.card F) := by
  obtain ⟨h01, -, h12⟩ := HF_ne hx
  rw [g0_eq hR h3 h19 hF hx]
  have h19' : (19 : ℝ) ≤ Fintype.card F := by exact_mod_cast h19
  have hA := chiR_ne_cases (sub_ne_zero.mpr (Ne.symm h01))
  have hB := chiR_ne_cases (sub_ne_zero.mpr (Ne.symm h12))
  unfold e0
  set n : ℝ := (Fintype.card F : ℝ)
  have hD : 0 < (n - 3) * (n - 4) := by
    have : 0 < n - 3 := by linarith
    have : 0 < n - 4 := by linarith
    positivity
  rw [div_sub_one hD.ne', abs_div, abs_of_pos hD, div_le_div_iff_of_pos_right hD, abs_le]
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB] <;> constructor <;> nlinarith

end Sarkozy.SignedEstimates
