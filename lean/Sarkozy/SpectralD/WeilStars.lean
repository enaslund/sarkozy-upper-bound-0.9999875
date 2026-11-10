module

public import Sarkozy.SpectralC.All
public import Sarkozy.Spectral.Stars
public import Sarkozy.Labellings.TargetBridge

@[expose] public section

/-!
# Star means and products of stars (`lem:general-star`, the Weil inputs)

`paper/sections/14_spectral.tex`, `subsec:spec:actual-stars`. For labels `x` injective on a set
`R` of coordinates, the star mean `w_R(x) = E_z ψ_R(z, x)` (WP-K's `SpectralC.starMean`) is the
star trace `p⁻¹ ∑_t χ(∏_{a ∈ x(R)} (t − a))` of the root set `x(R)` (WP-A's
`Spectral.starTrace`; `starMean_eq_starTrace`). Hence:

* `starMean_singleton`: `w_R = 0` for `|R| = 1`;
* `starMean_pair`: `w_R = −q` for `|R| = 2` (the two-root identity `eq:two-root`);
* `abs_starMean_le`: `|w_R| ≤ (|R| − 1) r` for nonempty `R` (`thm:weil`, the hypothesis
  `Labellings.WeilBound`, obtained from `Target.Weil` by `Labellings.weilBound_of_target`).

The product of two stars (`sum_starKer_mul`, the first display of the proof of
`lem:general-star`(c)): for `x` injective on `S ∪ T`,
`E_z ψ_S ψ_T = w_{S△T}(x) − q ∑_{j ∈ S∩T} ψ_{S△T}(x_j, x)`, so
`|E_z ψ_S ψ_T| ≤ |w_{S△T}| + |S∩T| q` (`abs_sum_starKer_mul_le`).

The constant `a_d` of `lem:general-star`(c) is `aConst`: `a_1 = 0`, `a_2 = q`,
`a_d = (d − 1) r` for `d ≥ 3`; `abs_starMean_le_aConst` gives `|w_R| ≤ a_{|R|}`.

New material for this paper.
-/

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped BigOperators symmDiff

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] in
/-- `ψ_R(a, x) = χ(∏_{b ∈ x(R)} (a − b))` for `x` injective on `R`. -/
lemma prod_chiRe_eq (R : Finset U) (x : U → ZMod p) (hx : Set.InjOn x R) (a : ZMod p) :
    ∏ j ∈ R, chiRe (a - x j) = (quadraticChar (ZMod p) (∏ b ∈ R.image x, (a - b)) : ℝ) := by
  rw [← Sarkozy.Spectral.prod_char_eq R x hx a]
  unfold chiRe
  push_cast
  rfl

omit [Fintype U] in
/-- **The star mean is the star trace of the root set**: `w_R(x) = starTrace (x(R))`. -/
theorem starMean_eq_starTrace (R : Finset U) (x : U → ZMod p) (hx : Set.InjOn x R) :
    starMean R x = Sarkozy.Spectral.starTrace (R.image x) := by
  unfold starMean starKer Sarkozy.Spectral.starTrace
  rw [ZMod.card, ← mul_sum, one_div]
  congr 1
  exact sum_congr rfl fun a _ => prod_chiRe_eq R x hx a

omit [Fintype U] [DecidableEq U] in
/-- `|ψ_R(a, x)| ≤ 1`. -/
lemma abs_prod_chiRe_le (R : Finset U) (x : U → ZMod p) (a : ZMod p) :
    |∏ j ∈ R, chiRe (a - x j)| ≤ 1 := by
  rw [abs_prod]
  exact prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => abs_chiRe_le _)

/-- `r = p^{-1/2}` in WP-A's form. -/
lemma one_div_sqrt_card : (1 / √(Fintype.card (ZMod p) : ℝ)) = rp p := by
  rw [ZMod.card, rp, one_div]

omit [Fintype U] in
/-- **`thm:weil` for star means**: `|w_R(x)| ≤ (|R| − 1) r` for nonempty `R` and `x` injective on
`R`. -/
theorem abs_starMean_le (hW : Labellings.WeilBound (ZMod p)) {R : Finset U} (hR : R.Nonempty)
    (x : U → ZMod p) (hx : Set.InjOn x R) :
    |starMean R x| ≤ ((R.card : ℝ) - 1) * rp p := by
  rw [starMean_eq_starTrace R x hx]
  have h := Sarkozy.Spectral.abs_starTrace_le hW (hR.image x)
  rw [card_image_of_injOn hx, one_div_sqrt_card] at h
  exact h

omit [Fintype U] in
/-- The same from `Target.Weil`. -/
theorem abs_starMean_le_of_target (hW : Target.Weil) (hp2 : p ≠ 2) {R : Finset U}
    (hR : R.Nonempty) (x : U → ZMod p) (hx : Set.InjOn x R) :
    |starMean R x| ≤ ((R.card : ℝ) - 1) * rp p :=
  abs_starMean_le (Labellings.weilBound_of_target hW p hp2) hR x hx

omit [Fintype U] in
/-- `w_R = 0` for `|R| = 1`. -/
theorem starMean_singleton (hp2 : p ≠ 2) (j : U) (x : U → ZMod p) : starMean {j} x = 0 := by
  rw [starMean_eq_starTrace {j} x (by simp), image_singleton]
  exact Sarkozy.Spectral.starTrace_singleton (by rwa [ZMod.ringChar_zmod_n]) _

omit [Fintype U] in
/-- `w_R = −q` for `|R| = 2` (the two-root identity). -/
theorem starMean_pair (hp2 : p ≠ 2) {i j : U} (x : U → ZMod p) (hij : x i ≠ x j) :
    starMean {i, j} x = -(p : ℝ)⁻¹ := by
  have hne : i ≠ j := fun h => hij (by rw [h])
  have hinj : Set.InjOn x ({i, j} : Finset U) := by
    intro a ha b hb hab
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact absurd hab hij
    · exact absurd hab.symm hij
    · rfl
  rw [starMean_eq_starTrace _ x hinj, image_insert, image_singleton,
    Sarkozy.Spectral.starTrace_pair (by rwa [ZMod.ringChar_zmod_n]) hij, ZMod.card, one_div]

omit [Fintype U] in
lemma exists_pair_of_card_two {R : Finset U} (h : R.card = 2) : ∃ i j, i ≠ j ∧ R = {i, j} := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h
  exact ⟨i, j, hij, rfl⟩

/-- The constant `a_d` of `lem:general-star`(c): `a_0 = a_1 = 0`, `a_2 = q`, `a_d = (d − 1) r`
for `d ≥ 3`. -/
noncomputable def aConst (p : ℕ) (d : ℕ) : ℝ :=
  if d ≤ 1 then 0 else if d = 2 then (p : ℝ)⁻¹ else ((d : ℝ) - 1) * rp p

omit [Fintype U] in
/-- `|w_R| ≤ a_{|R|}` for nonempty `R`, `x` injective on `R` (`|R| = 1`: `w = 0`; `|R| = 2`:
`w = −q`; `|R| ≥ 3`: Weil). -/
theorem abs_starMean_le_aConst (hp2 : p ≠ 2) (hW : Labellings.WeilBound (ZMod p))
    {R : Finset U} (hR : R.Nonempty) (x : U → ZMod p) (hx : Set.InjOn x R) :
    |starMean R x| ≤ aConst p R.card := by
  unfold aConst
  have h1 : 1 ≤ R.card := hR.card_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  by_cases hc1 : R.card ≤ 1
  · simp only [hc1, ↓reduceIte]
    obtain ⟨j, rfl⟩ := card_eq_one.mp (le_antisymm hc1 h1)
    rw [starMean_singleton hp2 j x, abs_zero]
  · simp only [hc1, ↓reduceIte]
    by_cases hc2 : R.card = 2
    · simp only [hc2, ↓reduceIte]
      obtain ⟨i, j, hij, rfl⟩ := exists_pair_of_card_two hc2
      have hxij : x i ≠ x j := fun h => hij (hx (by simp) (by simp) h)
      rw [starMean_pair hp2 x hxij, abs_neg, abs_of_pos (inv_pos.mpr hp0)]
    · simp only [hc2, ↓reduceIte]
      exact abs_starMean_le hW hR x hx

/-! ## Products of two stars -/

omit [Fintype U] in
/-- `ψ_S ψ_T = ψ_{S△T} · ψ_{S∩T}²`. -/
lemma prod_mul_prod_eq (S T : Finset U) (f : U → ℝ) :
    (∏ j ∈ S, f j) * ∏ j ∈ T, f j = (∏ j ∈ S ∆ T, f j) * (∏ j ∈ S ∩ T, f j) ^ 2 := by
  rw [← prod_union_inter, sq, ← mul_assoc]
  congr 1
  have hU : S ∪ T = (S ∆ T) ∪ (S ∩ T) := by
    ext a; simp only [mem_union, mem_symmDiff, mem_inter]; tauto
  have hD : Disjoint (S ∆ T) (S ∩ T) := by
    rw [disjoint_left]; intro a ha hb
    simp only [mem_symmDiff, mem_inter] at ha hb; tauto
  rw [hU, prod_union hD]

/-- **The product of two stars** (proof of `lem:general-star`(c)): for `x` injective on `S ∪ T`,
`p ∑_a (p⁻¹ψ_S)(p⁻¹ψ_T) = w_{S△T}(x) − q ∑_{j ∈ S∩T} ψ_{S△T}(x_j, x)`. -/
theorem sum_starKer_mul (S T : Finset U) (x : U → ZMod p) (hx : Set.InjOn x (S ∪ T)) :
    (p : ℝ) * ∑ a, starKer S x a * starKer T x a =
      starMean (S ∆ T) x - (p : ℝ)⁻¹ * ∑ j ∈ S ∩ T, ∏ i ∈ S ∆ T, chiRe (x j - x i) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hinj : Set.InjOn x (S ∩ T : Finset U) :=
    hx.mono (by intro a ha; simp only [coe_inter, Set.mem_inter_iff] at ha
                simp only [Set.mem_union]; exact Or.inl ha.1)
  have h1 : ∀ a, starKer S x a * starKer T x a = (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ *
      ((∏ j ∈ S ∆ T, chiRe (a - x j)) * (1 - if a ∈ (S ∩ T).image x then 1 else 0))) := by
    intro a
    unfold starKer
    have e := prod_mul_prod_eq S T (fun j => chiRe (a - x j))
    rw [prod_chiRe_sq] at e
    rw [show ((p : ℝ)⁻¹ * ∏ j ∈ S, chiRe (a - x j)) * ((p : ℝ)⁻¹ * ∏ j ∈ T, chiRe (a - x j)) =
      (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * ((∏ j ∈ S, chiRe (a - x j)) * ∏ j ∈ T, chiRe (a - x j))) by ring,
      e]
    split_ifs <;> ring
  rw [sum_congr rfl fun a _ => h1 a, ← mul_sum, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  have e2 : ∀ a, (p : ℝ)⁻¹ * ((∏ j ∈ S ∆ T, chiRe (a - x j)) *
      (1 - if a ∈ (S ∩ T).image x then 1 else 0)) = (p : ℝ)⁻¹ * ∏ j ∈ S ∆ T, chiRe (a - x j) -
      (if a ∈ (S ∩ T).image x then (p : ℝ)⁻¹ * ∏ j ∈ S ∆ T, chiRe (a - x j) else 0) := by
    intro a; split_ifs <;> ring
  rw [sum_congr rfl fun a _ => e2 a, sum_sub_distrib]
  congr 1
  rw [← sum_filter, ← mul_sum]
  congr 1
  have hf : univ.filter (fun a => a ∈ (S ∩ T).image x) = (S ∩ T).image x := by
    ext a; simp
  rw [hf, sum_image (fun a ha b hb h => hinj ha hb h)]

/-- `|E_z ψ_S ψ_T| ≤ |w_{S△T}| + |S∩T| q` for `x` injective on `S ∪ T`. -/
theorem abs_sum_starKer_mul_le (S T : Finset U) (x : U → ZMod p) (hx : Set.InjOn x (S ∪ T)) :
    |(p : ℝ) * ∑ a, starKer S x a * starKer T x a| ≤
      |starMean (S ∆ T) x| + ((S ∩ T).card : ℝ) * (p : ℝ)⁻¹ := by
  rw [sum_starKer_mul S T x hx]
  refine (abs_sub _ _).trans (add_le_add (le_refl _) ?_)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [abs_mul, abs_of_pos (inv_pos.mpr hp0), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ S ∩ T, |∏ i ∈ S ∆ T, chiRe (x j - x i)| ≤ ∑ _j ∈ S ∩ T, (1 : ℝ) :=
        sum_le_sum fun j _ => abs_prod_chiRe_le _ x _
    _ = ((S ∩ T).card : ℝ) := by rw [sum_const, nsmul_one]

end Sarkozy.SpectralD
