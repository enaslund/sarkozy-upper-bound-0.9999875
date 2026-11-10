module

public import Sarkozy.DensityChain.Summation
public import Sarkozy.Structured.MainTerm
public import Sarkozy.Moments.Mixed
public import Sarkozy.Moments.Normalization

@[expose] public section

/-!
# `lem:record:density-lp`: large products with a density factor

`lem:record:density-lp` (`paper/sections/08_scale_comparison.tex`): for the selected sets `E`
with `q_E > N^τ`, measures `κ'_E` with `κ'_E(1) ≤ c ∏_{𝔟 ∈ E} η_𝔟` whose one-slot marginals are
multiples of the uniform law, and inputs `G^E_v` (possibly averaged over indices),
`∑_{q_E > N^τ} |∫ ∏_v G^E_v dκ'_E| ≤ c C_ε Π_H N^{-τ/4+ε} α`. The proof has three steps, all
formalized here in the paper's form:

* **Hölder in `L^{72}(κ')` with uniform marginals** (`abs_signed_energy_le_lpNorm`):
  `|∫ ∏_v G_v dκ'| ≤ κ'(1) ∏_v ‖G_v‖_{L^{72}(G_N)}` for a signed weight whose variation has
  uniform one-slot marginals (`hasUniformMarginals_variationLaw`,
  `mixedLpBound_of_uniform_marginals`);
* **Hölder over the index law** (`expect_abs_signed_energy_le_moment`):
  `E_ω |∫ ∏_v G^ω_v dκ'| ≤ κ'(1) ∏_v (E_ω ‖G^ω_v‖_{72}^{72})^{1/72}`, so that a bound
  `E_ω ‖G^ω_v‖_{72}^{72} ≤ B` at every slot (`lem:record:lift-moments`(c) with moments of order
  `72`, `B = C_ε N^ε M₀^{72} K α`) gives `κ'(1) B` (the density exponents add to `72/72 = 1`);
* **Rankin's trick** (`DensityChain.sum_choice_large_le`).

**`density_lp`** combines them for the terms `(f, g)` of a bracket expansion: if each large term
is such an energy with `κ'(1) ≤ ∏_𝔟 G(𝔟, f 𝔟, g 𝔟)` and `T < ∏_{f ∪ g} w`, then the sum over the
large terms is at most `B · T^{-1/4} ∏_𝔟 ∑_{x,y} G w^{[x∨y]/4}` (the paper's `Π_H` with
`η_𝔟 = G` and `q_𝔟 = w_𝔟`).
-/

namespace Sarkozy.DensityChain

open Finset
open scoped BigOperators
open Sarkozy.Structured

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- Condition (b) of `def:record:structured-energy` makes the normalized variation a law with
uniform one-slot marginals. -/
theorem hasUniformMarginals_variationLaw (ρ : (Slot → X) → ℝ) (hρ : 0 < totalVariation ρ)
    (hunif : selectedMarginalsUniform ρ) : HasUniformMarginals (variationLaw ρ hρ) := by
  intro v f
  rw [FiniteLaw.expect_uniform]
  unfold FiniteLaw.expect
  change ∑ z, |ρ z| / totalVariation ρ * f (z v) = _
  rw [← Finset.sum_fiberwise univ (fun z : Slot → X => z v)]
  have hinner : ∀ x : X, ∑ z ∈ univ.filter (fun z : Slot → X => z v = x),
      |ρ z| / totalVariation ρ * f (z v) = f x / (Fintype.card X : ℝ) := by
    intro x
    have h1 : ∑ z ∈ univ.filter (fun z : Slot → X => z v = x),
        |ρ z| / totalVariation ρ * f (z v) =
        (∑ z ∈ univ.filter (fun z : Slot → X => z v = x), |ρ z|) / totalVariation ρ * f x := by
      rw [sum_div, sum_mul]
      apply sum_congr rfl
      intro z hz
      rw [(mem_filter.mp hz).2]
    rw [h1, hunif v x]
    field_simp
  simp_rw [hinner]
  rw [sum_div]

/-- **Hölder in `L^{72}` for a signed weight with uniform variation marginals** (first step of
`lem:record:density-lp`): `|∑_z ρ(z) ∏_v a_v(z_v)| ≤ ‖ρ‖ ∏_v ‖a_v‖_{L^{72}(X)}`. -/
theorem abs_signed_energy_le_lpNorm (ρ : (Slot → X) → ℝ) (hunif : selectedMarginalsUniform ρ)
    (a : Slot → X → ℝ) :
    |∑ z, ρ z * ∏ v, a v (z v)| ≤
      totalVariation ρ * ∏ v, (FiniteLaw.uniform X).lpNorm 72 (a v) := by
  rcases (totalVariation_nonneg ρ).lt_or_eq with hρ | hρ0
  · have hm := mixedLpBound_of_uniform_marginals (variationLaw ρ hρ)
      (hasUniformMarginals_variationLaw ρ hρ hunif)
    rw [card_slot] at hm
    have h1 := hm (fun v x => |a v x|)
    simp only [FiniteLaw.lpNorm_abs, one_mul, Nat.cast_ofNat] at h1
    have h2 : |∑ z, ρ z * ∏ v, a v (z v)| ≤ ∑ z, |ρ z| * ∏ v, |a v (z v)| := by
      refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      apply sum_congr rfl
      intro z _
      rw [abs_mul, Finset.abs_prod]
    have h3 : ∑ z, |ρ z| * ∏ v, |a v (z v)| =
        totalVariation ρ * (variationLaw ρ hρ).expect (fun z => ∏ v, |a v (z v)|) := by
      unfold FiniteLaw.expect
      rw [mul_sum]
      apply sum_congr rfl
      intro z _
      change |ρ z| * _ = totalVariation ρ * (|ρ z| / totalVariation ρ * _)
      field_simp
    have h4 : 0 ≤ (variationLaw ρ hρ).expect (fun z => ∏ v, |a v (z v)|) :=
      FiniteLaw.expect_nonneg _ fun z => prod_nonneg fun v _ => abs_nonneg _
    rw [h3] at h2
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hρ.le)
    exact (le_abs_self _).trans h1
  · have hz : ∀ z, ρ z = 0 := by
      intro z
      have h := (sum_eq_zero_iff_of_nonneg (fun z _ => abs_nonneg (ρ z))).mp hρ0.symm z
        (mem_univ z)
      exact abs_eq_zero.mp h
    simp [hz, ← hρ0]

/-- **Hölder over the index law** (second step of `lem:record:density-lp`): if the averaged
`72`-th moments of the inputs are at most `B` at every slot, then
`E_ω |∑_z ρ(z) ∏_v a^ω_v(z_v)| ≤ ‖ρ‖ B`. -/
theorem expect_abs_signed_energy_le_moment {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (ρ : (Slot → X) → ℝ) (hunif : selectedMarginalsUniform ρ) (a : Ω → Slot → X → ℝ) {B : ℝ}
    (hB : ∀ v, P.expect (fun ω => (FiniteLaw.uniform X).moment 72 (a ω v)) ≤ B) :
    P.expect (fun ω => |∑ z, ρ z * ∏ v, a ω v (z v)|) ≤ totalVariation ρ * B := by
  have hpt := fun ω => abs_signed_energy_le_lpNorm ρ hunif (a ω)
  refine (P.expect_mono hpt).trans ?_
  rw [FiniteLaw.expect_const_mul]
  apply mul_le_mul_of_nonneg_left _ (totalVariation_nonneg ρ)
  have hH := P.abs_expect_prod_le_lpNorm (fun _ : Slot => (72 : ℝ)) (fun _ => by norm_num)
    (by rw [sum_const, card_univ, card_slot]; norm_num)
    (fun v ω => (FiniteLaw.uniform X).lpNorm 72 (a ω v))
  refine (le_abs_self _).trans (hH.trans ?_)
  have hB0 : 0 ≤ B := by
    obtain ⟨v⟩ : Nonempty Slot := ⟨(0, 0, 0)⟩
    exact (P.expect_nonneg fun ω => (FiniteLaw.uniform X).moment_nonneg _ _).trans (hB v)
  have hslot : ∀ v, P.lpNorm 72 (fun ω => (FiniteLaw.uniform X).lpNorm 72 (a ω v)) ≤
      B ^ ((1 : ℝ) / 72) := by
    intro v
    have hm : P.moment 72 (fun ω => (FiniteLaw.uniform X).lpNorm 72 (a ω v)) =
        P.expect (fun ω => (FiniteLaw.uniform X).moment 72 (a ω v)) := by
      change P.expect (fun ω => |(FiniteLaw.uniform X).lpNorm 72 (a ω v)| ^ (72 : ℝ)) = _
      apply FiniteLaw.expect_congr
      intro ω
      rw [abs_of_nonneg (FiniteLaw.lpNorm_nonneg _ _ _),
        FiniteLaw.lpNorm_rpow _ (by norm_num)]
    change (P.moment 72 (fun ω => (FiniteLaw.uniform X).lpNorm 72 (a ω v))) ^ ((1 : ℝ) / 72) ≤ _
    rw [hm]
    exact Real.rpow_le_rpow (P.expect_nonneg fun ω => (FiniteLaw.uniform X).moment_nonneg _ _)
      (hB v) (by norm_num)
  calc ∏ v, P.lpNorm 72 (fun ω => (FiniteLaw.uniform X).lpNorm 72 (a ω v))
      ≤ ∏ _v : Slot, B ^ ((1 : ℝ) / 72) :=
        prod_le_prod₀ (fun v _ => FiniteLaw.lpNorm_nonneg _ _ _) fun v _ => hslot v
    _ = B := by
        rw [prod_const, card_univ, card_slot, ← Real.rpow_natCast, ← Real.rpow_mul hB0]
        norm_num

/-- **`lem:record:density-lp`** for the terms of a bracket expansion. If every term `(f, g)` of a
subfamily `S` (the large unions) is an index-averaged energy `E_ω |∑_z ρ ∏_v a^ω_v|` whose weight
has uniform variation marginals and mass `‖ρ_{f,g}‖ ≤ ∏_𝔟 G(𝔟, f 𝔟, g 𝔟)`, whose inputs have
averaged `72`-th moments at most `B`, and whose selected product exceeds `T`, then the sum over
`S` is at most `B · T^{-1/4} ∏_𝔟 ∑_{x,y} G(𝔟, x, y) w_𝔟^{[x∨y]/4}`. -/
theorem density_lp {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Fintype Ω]
    (P : FiniteLaw Ω) (G : ι → Bool → Bool → ℝ) (hG : ∀ b x y, 0 ≤ G b x y) (w : ι → ℝ)
    (hw : ∀ b, 0 ≤ w b) {T B : ℝ} (hT : 0 < T) (hB0 : 0 ≤ B)
    (S : (ι → Bool) → Finset (ι → Bool)) (ρ : (ι → Bool) → (ι → Bool) → (Slot → X) → ℝ)
    (a : (ι → Bool) → (ι → Bool) → Ω → Slot → X → ℝ)
    (hunif : ∀ f, ∀ g ∈ S f, selectedMarginalsUniform (ρ f g))
    (hmass : ∀ f, ∀ g ∈ S f, totalVariation (ρ f g) ≤ ∏ b, G b (f b) (g b))
    (hB : ∀ f, ∀ g ∈ S f, ∀ v,
      P.expect (fun ω => (FiniteLaw.uniform X).moment 72 (a f g ω v)) ≤ B)
    (hlarge : ∀ f, ∀ g ∈ S f, T < ∏ b, (if (f b || g b) = true then w b else 1)) :
    ∑ f, ∑ g ∈ S f, P.expect (fun ω => |∑ z, ρ f g z * ∏ v, a f g ω v (z v)|) ≤
      B * (T ^ (-((1 : ℝ) / 4)) *
        ∏ b, ∑ x, ∑ y, G b x y * (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1)) := by
  have hterm : ∀ f, ∀ g ∈ S f,
      P.expect (fun ω => |∑ z, ρ f g z * ∏ v, a f g ω v (z v)|) ≤
        B * ∏ b, G b (f b) (g b) := by
    intro f g hg
    refine (expect_abs_signed_energy_le_moment P (ρ f g) (hunif f g hg) (a f g) (hB f g hg)).trans
      ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hmass f g hg) hB0
  calc ∑ f, ∑ g ∈ S f, P.expect (fun ω => |∑ z, ρ f g z * ∏ v, a f g ω v (z v)|)
      ≤ ∑ f, ∑ g ∈ S f, B * ∏ b, G b (f b) (g b) :=
        sum_le_sum fun f _ => sum_le_sum fun g hg => hterm f g hg
    _ = B * ∑ f, ∑ g ∈ S f, ∏ b, G b (f b) (g b) := by
        rw [mul_sum]
        exact sum_congr rfl fun f _ => by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_choice_large_le G hG w hw hT S hlarge) hB0

end Sarkozy.DensityChain
