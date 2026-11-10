module

public import Sarkozy.Interpolation.SquarePairEndpoints
public import Sarkozy.DensityUpgrade.StrongF

/-!
# The interpolated pair bounds of `lem:density:strong-F`

`paper/sections/31_density_induction_upgrade.tex`, proof of `lem:density:strong-F`. Two named
hypotheses of WP-P's `DensityUpgrade.StrongF` are interpolated centred bounds:

* `hνcent` of `strongF_two_layer_distinct`: "The uniform ordered-distinct pair has centered
  bilinear `L¹` norm at most one and `L²` norm `1/(p−1)`. Interpolation gives centered `L^{9/8}`
  norm `(p−1)^{-2/9}`." Proved here as `distinctPair_interp` (`distinctPair_L1`,
  `distinctPair_L2`, then `centred_interp` at `t = 2/9`);
* `hεcent` of `strongF_one_layer`: "For a strict Paley edge in class three, centered
  interpolation at `4/3` gives bilinear norm `(p+1)^{3/4}/(p−1) ≤ 2p^{-1/4}`." Proved here as
  `class_interp_four_thirds` for both class laws and every odd prime `p ≥ 4`, from `class_L1`,
  `class_L2` at `t = 1/2`. We use the `L²` bound `1/(√p − 1)` of `class_L2` (valid for all odd
  `p`), not the sharper tournament value `√(p+1)/(p−1)` behind the paper's `(p+1)^{3/4}/(p−1)`;
  the resulting `((p+1)/(p−1))^{1/2} (√p − 1)^{-1/2}` is still at most `2p^{-1/4}`
  (`paley_four_thirds_numeric`), which is the bound the Lean chain uses.

Consequences, with the interpolation hypotheses discharged:
* `strongF_two_layer_distinct_proved`: `strongF_two_layer_distinct` without `hνcent`;
* `strongF_one_layer_class`: `strongF_one_layer` for the class law on `𝔽_p`, without
  `hεcent`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Interpolation

section Centred

variable {X : Type*} [Fintype X] [Nonempty X]

/-- `∑_a (f(a) − E f)² ≤ ∑ f²`. -/
theorem sum_centred_sq_le' (f : X → ℝ) :
    ∑ a, (f a - (∑ b, f b) / Fintype.card X) ^ 2 ≤ ∑ a, f a ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have h : ∑ a, (f a - (∑ b, f b) / Fintype.card X) ^ 2 =
      ∑ a, f a ^ 2 - (∑ b, f b) ^ 2 / Fintype.card X := by
    have hexp : ∀ a, (f a - (∑ b, f b) / Fintype.card X) ^ 2 = f a ^ 2 -
        2 * ((∑ b, f b) / Fintype.card X) * f a + ((∑ b, f b) / Fintype.card X) ^ 2 :=
      fun a => by ring
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  rw [h]
  have : 0 ≤ (∑ b, f b) ^ 2 / Fintype.card X := by positivity
  linarith

/-- **Covariance bound**: `|∑_a (f(a) − E f) g(a)| ≤ (∑ f²)^{1/2} (∑ g²)^{1/2}`. -/
theorem abs_cov_le (f g : X → ℝ) :
    |∑ a, (f a - (∑ b, f b) / Fintype.card X) * g a| ≤
      Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ a, g a ^ 2) := by
  have hA : 0 ≤ ∑ a, f a ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← Real.sqrt_mul hA]
  apply Real.abs_le_sqrt
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun a => f a - (∑ b, f b) / Fintype.card X) g
  have hG : 0 ≤ ∑ a, g a ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact hcs.trans (mul_le_mul_of_nonneg_right (sum_centred_sq_le' f) hG)

end Centred

section Distinct

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The centred form of the uniform ordered-distinct pair:
`B(f,g) = −∑_a (f(a) − E f) g(a) / (n(n−1))`, `n = |X|`. -/
theorem distinctPair_centredForm (hX : 2 ≤ Fintype.card X) (f g : X → ℝ) :
    centredForm (DensityUpgrade.distinctPair X) f g =
      -(∑ a, (f a - (∑ b, f b) / Fintype.card X) * g a) /
        ((Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1)) := by
  have hN : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
  have hN0 : (Fintype.card X : ℝ) ≠ 0 := by linarith
  have hN1 : (Fintype.card X : ℝ) - 1 ≠ 0 := by linarith
  have e := DensityUpgrade.sum_distinctPair (X := X) (fun a b => f a * g b)
  have hfg : ∑ a : X, ∑ b : X, (if a = b then 0 else f a * g b) =
      (∑ a, f a) * (∑ b, g b) - ∑ a, f a * g a := by
    have h1 : ∀ a : X, ∑ b : X, (if a = b then 0 else f a * g b) =
        f a * ∑ b, g b - f a * g a := by
      intro a
      have : ∑ b : X, (if a = b then 0 else f a * g b) =
          ∑ b : X, (f a * g b - if a = b then f a * g b else 0) :=
        Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, ← Finset.mul_sum]
      simp
    simp only [h1, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hX' : ∑ a, (f a - (∑ b, f b) / Fintype.card X) * g a =
      ∑ a, f a * g a - (∑ b, f b) / Fintype.card X * ∑ a, g a := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold centredForm
  rw [e, hfg, hX']
  field_simp
  ring

/-- **The `L²` endpoint of the distinct pair** (all `f, g`): `|B(f,g)| ≤ ‖f‖₂ ‖g‖₂/(n − 1)`. -/
theorem distinctPair_L2 (hX : 2 ≤ Fintype.card X) (f g : X → ℝ) :
    |centredForm (DensityUpgrade.distinctPair X) f g| ≤
      ((Fintype.card X : ℝ) - 1)⁻¹ * DensityUpgrade.conditioningNorm 2 f *
        DensityUpgrade.conditioningNorm 2 g := by
  have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hcov := abs_cov_le f g
  rw [distinctPair_centredForm hX, conditioningNorm_two, conditioningNorm_two]
  set N : ℝ := (Fintype.card X : ℝ) with hN_def
  have hN : (2 : ℝ) ≤ N := by rw [hN_def]; exact_mod_cast hX
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  set A := ∑ a, f a ^ 2 with hA_def
  set G := ∑ a, g a ^ 2 with hG_def
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.sqrt_div' _ hN0.le, Real.sqrt_div' _ hN0.le, abs_div, abs_neg,
    abs_of_pos (mul_pos hN0 hN1)]
  set s := Real.sqrt N with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.2 hN0
  have hs2 : s ^ 2 = N := Real.sq_sqrt hN0.le
  rw [div_le_iff₀ (mul_pos hN0 hN1)]
  refine hcov.trans (le_of_eq ?_)
  have hs1 : s ^ 2 - 1 ≠ 0 := by rw [hs2]; exact hN1.ne'
  rw [← hs2]
  field_simp

/-- The distinct-pair weight at a pair. -/
theorem distinctPair_pair (a b : X) :
    DensityUpgrade.distinctPair X ![a, b] =
      if a = b then 0 else ((Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1))⁻¹ := by
  simp [DensityUpgrade.distinctPair]

/-- **The `L¹` endpoint of the distinct pair**: `|B(f,g)| ≤ ‖f‖₁ ‖g‖₁` (`n ≥ 2`). -/
theorem distinctPair_L1 (hX : 2 ≤ Fintype.card X) (f g : X → ℝ) :
    |centredForm (DensityUpgrade.distinctPair X) f g| ≤
      1 * DensityUpgrade.conditioningNorm 1 f * DensityUpgrade.conditioningNorm 1 g := by
  have hN : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
  have hN0 : (0 : ℝ) < Fintype.card X := by linarith
  have hN1 : (1 : ℝ) ≤ (Fintype.card X : ℝ) - 1 := by linarith
  rw [centredForm_eq_rbil]
  refine L1_uniform_of_kernel_le _ (fun a b => ?_) f g
  simp only [centredKernel]
  rw [distinctPair_pair]
  split_ifs
  · rw [zero_sub, abs_neg, abs_of_nonneg (by positivity), one_mul]
  · have heq : ((Fintype.card X : ℝ) * ((Fintype.card X : ℝ) - 1))⁻¹ -
        (Fintype.card X : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹ =
        (Fintype.card X : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹ * ((Fintype.card X : ℝ) - 1)⁻¹ := by
      have h1 : (Fintype.card X : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    have hN1' : (0 : ℝ) < (Fintype.card X : ℝ) - 1 := by linarith
    rw [heq, one_mul, abs_of_nonneg (by positivity)]
    have hinv : ((Fintype.card X : ℝ) - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    calc (Fintype.card X : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹ * ((Fintype.card X : ℝ) - 1)⁻¹
        ≤ (Fintype.card X : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (Fintype.card X : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹ := mul_one _

/-- **`lem:density:strong-F`, the interpolated distinct-pair bound** (`hνcent` of
`DensityUpgrade.strongF_two_layer_distinct`, with `p = |X|`): for mean-zero `f, g`,
`|E f(x₀) g(x₁)| ≤ (n − 1)^{-2/9} ‖f‖_{9/8} ‖g‖_{9/8}`. -/
theorem distinctPair_interp (hX : 2 ≤ Fintype.card X) :
    ∀ f g : X → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, DensityUpgrade.distinctPair X x * (f (x 0) * g (x 1))| ≤
        ((Fintype.card X : ℝ) - 1) ^ (-(2 / 9 : ℝ)) * DensityUpgrade.conditioningNorm (9 / 8) f *
          DensityUpgrade.conditioningNorm (9 / 8) g := by
  intro f g hf _
  have hN : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
  have hN1 : (0 : ℝ) < (Fintype.card X : ℝ) - 1 := by linarith
  have key := centred_interp (DensityUpgrade.distinctPair X) (L := 1)
    (ρ := ((Fintype.card X : ℝ) - 1)⁻¹) (t := 2 / 9) (r := 9 / 8) zero_le_one
    (inv_nonneg.mpr hN1.le) (by norm_num) (by norm_num) (by norm_num) (distinctPair_L1 hX)
    (distinctPair_L2 hX) f g
  rwa [centredForm_of_mean_zero _ g hf, Real.one_rpow, one_mul, Real.inv_rpow hN1.le,
    ← Real.rpow_neg hN1.le] at key

/-- **`lem:density:strong-F`, two-layer fold, with the distinct-pair interpolation proved**:
`DensityUpgrade.strongF_two_layer_distinct` without its hypothesis `hνcent`, for any real
parameter `2^18 ≤ p ≤ |X|`. Only part of `lem:density:strong-F`: the other construction-specific
inputs (`κ` and its pair marginals, the fold decomposition `hmix`, `hρu`) remain hypotheses. -/
theorem strongF_two_layer_distinct_proved [Nonempty X] (hX : 2 ≤ Fintype.card X) {p : ℝ}
    (hp : 2 ^ 18 ≤ p) (hpX : p ≤ Fintype.card X)
    (κ : (Fin 4 → X) → ℝ) (hκ : ∀ x, 0 ≤ κ x)
    (h01 : ∀ h : (Fin 2 → X) → ℝ,
      ∑ x, κ x * h ![x 0, x 1] = ∑ y, DensityUpgrade.distinctPair X y * h y)
    (h23 : ∀ h : (Fin 2 → X) → ℝ,
      ∑ x, κ x * h ![x 2, x 3] = ∑ y, DensityUpgrade.distinctPair X y * h y)
    (π ρ : (Fin (4 + 2) → X) → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 8 / p)
    (hmix : ∀ x, κ (fun i => x (Fin.castAdd 2 i)) *
      DensityUpgrade.distinctPair X (fun j => x (Fin.natAdd 4 j)) = (1 - η) * π x + η * ρ x)
    (hρu : DensityUpgrade.conditioningUniformCoords ρ) :
    DensityUpgrade.conditioningUnitMixed π (5 / 2) := by
  have hp1 : (0 : ℝ) < p - 1 := by
    have : (1 : ℝ) < 2 ^ 18 := by norm_num
    linarith
  have hmono : ((Fintype.card X : ℝ) - 1) ^ (-(2 / 9 : ℝ)) ≤ (p - 1) ^ (-(2 / 9 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hp1 (by linarith) (by norm_num)
  refine DensityUpgrade.strongF_two_layer_distinct hX hp (fun f g hf hg => ?_) κ hκ h01 h23 π ρ
    hπ hπ1 hρ hρ1 hη0 hη hmix hρu
  refine (distinctPair_interp hX f g hf hg).trans ?_
  have h1 := DensityUpgrade.conditioningNorm_nonneg (9 / 8) f
  have h2 := DensityUpgrade.conditioningNorm_nonneg (9 / 8) g
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono h1) h2

end Distinct

/-- `((p+1)/(p−1))^{1/2} (1/(√p − 1))^{1/2} ≤ 2 p^{-1/4}` for `p ≥ 4`. -/
theorem paley_four_thirds_numeric {p : ℝ} (hp : 4 ≤ p) :
    ((p + 1) / (p - 1)) ^ (1 - 1 / 2 : ℝ) * (1 / (Real.sqrt p - 1)) ^ (1 / 2 : ℝ) ≤
      2 * p ^ (-(1 / 4 : ℝ)) := by
  have hp0 : 0 < p := by linarith
  set s := Real.sqrt p with hs_def
  have hs2 : s ^ 2 = p := Real.sq_sqrt hp0.le
  have hs : 2 ≤ s := by
    rw [hs_def, show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hp
  have hL0 : 0 ≤ (p + 1) / (p - 1) := div_nonneg (by linarith) (by linarith)
  have hρ0 : 0 ≤ 1 / (s - 1) := one_div_nonneg.mpr (by linarith)
  have hprod : (p + 1) / (p - 1) * (1 / (s - 1)) ≤ 4 / s := by
    rw [← hs2, div_mul_div_comm, mul_one,
      div_le_div_iff₀ (mul_pos (by nlinarith) (by linarith)) (by linarith)]
    have hu : 0 ≤ s - 2 := by linarith
    nlinarith [mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu]
  have e1 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [e1, ← Real.mul_rpow hL0 hρ0]
  calc ((p + 1) / (p - 1) * (1 / (s - 1))) ^ (1 / 2 : ℝ) ≤ (4 / s) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (mul_nonneg hL0 hρ0) hprod (by norm_num)
    _ = 2 * p ^ (-(1 / 4 : ℝ)) := by
        have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.mpr (by linarith)), h4,
          hs_def, Real.sqrt_eq_rpow, ← Real.rpow_neg hp0.le, ← Real.rpow_mul hp0.le]
        norm_num

section ClassLaw

open Sarkozy.InvariantPair

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [hp : Fact p.Prime]

/-- **`lem:density:strong-F`, the interpolated Paley-edge bound** (`hεcent` of
`DensityUpgrade.strongF_one_layer`): for either class law on `𝔽_p`, `p ≥ 4`, and mean-zero
`f, g`, `|E f(x₀) g(x₁)| ≤ 2 p^{-1/4} ‖f‖_{4/3} ‖g‖_{4/3}`. -/
theorem class_interp_four_thirds (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1)
    (hp4 : (4 : ℝ) ≤ p) :
    ∀ f g : ZMod p → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight x *
          (f (x 0) * g (x 1))| ≤
        2 * (p : ℝ) ^ (-(1 / 4 : ℝ)) * DensityUpgrade.conditioningNorm (4 / 3) f *
          DensityUpgrade.conditioningNorm (4 / 3) g := by
  intro f g hf _
  have hp1 : (1 : ℝ) < p := by linarith
  have hsq : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hp1
  have key := centred_interp _ (t := 1 / 2) (r := 4 / 3)
    (div_nonneg (by linarith) (by linarith) : (0 : ℝ) ≤ ((p : ℝ) + 1) / ((p : ℝ) - 1))
    (one_div_nonneg.mpr (by linarith) : (0 : ℝ) ≤ 1 / (Real.sqrt p - 1))
    (by norm_num) (by norm_num) (by norm_num) (class_L1 hp2 hc) (class_L2 hp2 hc) f g
  rw [centredForm_of_mean_zero _ g hf] at key
  refine key.trans ?_
  have h1 := DensityUpgrade.conditioningNorm_nonneg (4 / 3) f
  have h2 := DensityUpgrade.conditioningNorm_nonneg (4 / 3) g
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (paley_four_thirds_numeric hp4) h1) h2

/-- **`lem:density:strong-F`, one-layer fold, with the Paley-edge interpolation proved**:
`DensityUpgrade.strongF_one_layer` for the class law `ε` on `𝔽_p` (`c = 1`: strict Paley edges),
without its hypotheses `hε`, `hεu`, `hεcent`. Only part of `lem:density:strong-F`: the fold
decomposition `hmix` and `hρu` remain hypotheses. -/
theorem strongF_one_layer_class (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1)
    (hp24 : (2 : ℝ) ^ 24 ≤ p)
    (π ρ : (Fin (2 + 1) → ZMod p) → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 2 / p)
    (hmix : ∀ x, (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight
        (fun i => x (Fin.castAdd 1 i)) * (Fintype.card (Fin 1 → ZMod p) : ℝ)⁻¹ =
      (1 - η) * π x + η * ρ x)
    (hρu : DensityUpgrade.conditioningUniformCoords ρ) :
    DensityUpgrade.conditioningUnitMixed π (7 / 5) :=
  DensityUpgrade.strongF_one_layer _ (fun x => (uniformOn _ _).nonneg x)
    (EdgeGate.classSet_uniformCoords hp2 hc) hp24
    (class_interp_four_thirds hp2 hc (by have : (4 : ℝ) ≤ 2 ^ 24 := by norm_num
                                         linarith))
    π ρ hπ hπ1 hρ hρ1 hη0 hη hmix hρu

end ClassLaw

end Sarkozy.Interpolation
