module

public import Sarkozy.PartVRecords.OneStageDelta

@[expose] public section

/-!
# The symmetric part of the record difference at one prime (`lem:record:one-stage-folded-e`(c))

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(c): **the symmetric part of
`Δ = 𝒦₊ - 𝒦₀` has norm exactly `1/(p - 2)` on the mean-zero functions of `V_c`, attained at the
sector contrast `𝐡_c`** (`p ≥ 11`). The norm of the symmetric part is the largest value of
`|⟨f, Δ f⟩|/‖f‖²`, since `⟨f, Sym Δ f⟩ = ⟨f, Δ f⟩` (`symForm_eq`).

The paper's proof, formalized here:
* `𝐂_c` is skew (`sum_mul_Cop_self`), so `⟨g, 𝐂 g⟩ = 0`;
* on `𝒵_c`, `⟨g, Δ g⟩ = -‖g‖²/((p - 3)(p - 2)) - 4 ⟨g₊, 𝐂 g₋⟩/((p - 3)(p + 1))` (`form_Dop_Z`) and
  `|⟨g₊, 𝐂 g₋⟩| ≤ √p ‖g₊‖ ‖g₋‖ ≤ √p ‖g‖²/2` (`abs_cross_le`), so
  `|⟨g, Δ g⟩| ≤ (1/((p - 3)(p - 2)) + 2√p/((p - 3)(p + 1))) ‖g‖² ≤ ‖g‖²/(p - 2)` for `p ≥ 11`
  (`sym_coef_le`, the paper's `4q + 2r(1 - 2q)/(1 + q) ≤ 1`);
* for `f = t 𝐡_c + g`, `⟨f, Δ f⟩ = t² ‖𝐡_c‖²/(p - 2) + ⟨g, Δ g⟩` (`form_Dop_split`), hence
  `|⟨f, Δ f⟩| ≤ ‖f‖²/(p - 2)` (`abs_form_Dop_le`), with equality at `𝐡_c`
  (`form_Dop_sector`).
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- The quadratic form of the symmetric part equals that of the operator. -/
theorem symForm_eq (c : F) (f : F → ℝ) :
    (∑ a, f a * Dop c f a + ∑ a, Dop c f a * f a) / 2 = ∑ a, f a * Dop c f a := by
  have : ∑ a, Dop c f a * f a = ∑ a, f a * Dop c f a := sum_congr rfl fun a _ => mul_comm _ _
  rw [this]
  ring

/-- **The Paley matrix is skew** for `q ≡ 3 (mod 4)`: `⟨g, 𝐂 g⟩ = 0`. -/
theorem sum_mul_Cop_self (h3 : Fintype.card F % 4 = 3) (g : F → ℝ) :
    ∑ a, g a * Cop g a = 0 := by
  unfold Cop
  have hS : ∑ a, g a * ∑ a', ((χ (a' - a) : ℤ) : ℝ) * g a' =
      ∑ a, ∑ a', g a * ((χ (a' - a) : ℤ) : ℝ) * g a' := by
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun a' _ => by ring
  have hswap : ∑ a, ∑ a', g a * ((χ (a' - a) : ℤ) : ℝ) * g a' =
      -∑ a, ∑ a', g a * ((χ (a' - a) : ℤ) : ℝ) * g a' := by
    conv_lhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun a' _ => ?_
    have : ((χ (a - a') : ℤ) : ℝ) = -((χ (a' - a) : ℤ) : ℝ) := by
      exact_mod_cast chi_swap h3 a a'
    rw [this]
    ring
  rw [hS]
  linarith

/-- The part of `g` on `V_c^+`. -/
noncomputable def gPlus (c : F) (g : F → ℝ) (a : F) : ℝ := if χ (a - c) = 1 then g a else 0

theorem sum_sq_split (c : F) {g : F → ℝ} (hg : g c = 0) :
    ∑ a, g a ^ 2 = ∑ a, gPlus c g a ^ 2 + ∑ a, gMinus c g a ^ 2 := by
  have := sum_split_sectors (c := c) (fun a => g a ^ 2) (by simp only [hg, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
  rw [this]
  unfold gPlus gMinus
  congr 1 <;> refine sum_congr rfl fun a _ => ?_ <;> split_ifs <;> simp

/-- **`|⟨g₊, 𝐂 g₋⟩| ≤ √q (‖g₊‖² + ‖g₋‖²)/2`.** -/
theorem abs_cross_le (hF : ringChar F ≠ 2) (c : F) (g : F → ℝ) :
    |∑ a, gPlus c g a * Cop (gMinus c g) a| ≤
      Real.sqrt (Fintype.card F : ℝ) * (∑ a, gPlus c g a ^ 2 + ∑ a, gMinus c g a ^ 2) / 2 := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set X := ∑ a, gPlus c g a * Cop (gMinus c g) a with hX
  set P := ∑ a, gPlus c g a ^ 2 with hP
  set M := ∑ a, gMinus c g a ^ 2 with hM
  have hP0 : 0 ≤ P := sum_nonneg fun a _ => sq_nonneg _
  have hM0 : 0 ≤ M := sum_nonneg fun a _ => sq_nonneg _
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (gPlus c g) (Cop (gMinus c g))
  have hC := sum_Cop_sq hF (gMinus c g)
  have hCle : ∑ a, Cop (gMinus c g) a ^ 2 ≤ q * M := by
    rw [hC]
    nlinarith [sq_nonneg (∑ a, gMinus c g a)]
  have hX2 : X ^ 2 ≤ P * (q * M) := hcs.trans (mul_le_mul_of_nonneg_left hCle hP0)
  have hY : 0 ≤ Real.sqrt q * (P + M) / 2 := by positivity
  have hX2' : X ^ 2 ≤ (Real.sqrt q * (P + M) / 2) ^ 2 := by
    have : (Real.sqrt q * (P + M) / 2) ^ 2 = q * ((P + M) / 2) ^ 2 := by
      rw [div_pow, mul_pow, hsq]
      ring
    rw [this]
    nlinarith [sq_nonneg (P - M)]
  rw [abs_le]
  constructor <;> nlinarith [hX2', hY]

/-- **The quadratic form of `Δ` on `𝒵_c`**:
`⟨g, Δ g⟩ = -‖g‖²/((q - 3)(q - 2)) - 4 ⟨g₊, 𝐂 g₋⟩/((q - 3)(q + 1))`. -/
theorem form_Dop_Z (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c : F) {g : F → ℝ}
    (hg : g c = 0) (hp : Sp c g = 0) (hm : Sm c g = 0) :
    ∑ a, g a * Dop c g a =
      -(∑ a, g a ^ 2) / (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2)) -
        4 / (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) + 1)) *
          ∑ a, gPlus c g a * Cop (gMinus c g) a := by
  have hpt : ∀ a, g a * Dop c g a =
      g a * Cop g a / ((Fintype.card F : ℝ) - 3) -
        g a ^ 2 / (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2)) -
        4 / (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) + 1)) *
          (gPlus c g a * Cop (gMinus c g) a) := by
    intro a
    by_cases ha : a = c
    · subst ha
      simp only [hg, zero_mul, zero_div, zero_pow two_ne_zero, gPlus, ite_self,
        mul_zero, sub_self]
    · rw [Dop_apply_Z hk c hg hp hm ha]
      unfold gPlus
      split_ifs <;> ring
  simp only [hpt, sum_sub_distrib, ← mul_sum, ← sum_div]
  have hskew := sum_mul_Cop_self h3 g
  rw [hskew]
  ring

/-- **`1/((q - 3)(q - 2)) + 2√q/((q - 3)(q + 1)) ≤ 1/(q - 2)` for `q ≥ 11`** (the paper's
`4q + 2r(1 - 2q)/(1 + q) ≤ 1`). -/
theorem sym_coef_le {q : ℝ} (hq : 11 ≤ q) :
    1 / ((q - 3) * (q - 2)) + 2 * Real.sqrt q / ((q - 3) * (q + 1)) ≤ 1 / (q - 2) := by
  have hq3 : 0 < q - 3 := by linarith
  have hq2 : 0 < q - 2 := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have hs : Real.sqrt q ≤ q / 3 := by
    rw [show q / 3 = Real.sqrt ((q / 3) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hB : 2 * Real.sqrt q / ((q - 3) * (q + 1)) ≤ 2 * (q / 3) / ((q - 3) * (q + 1)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hpoly : 0 ≤ q ^ 2 - 5 * q - 12 := by nlinarith
  have hmain : 1 / ((q - 3) * (q - 2)) + 2 * (q / 3) / ((q - 3) * (q + 1)) ≤ 1 / (q - 2) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hq2]
    nlinarith [mul_nonneg (mul_nonneg hq2.le hq3.le) hpoly]
  linarith

/-- **`|⟨g, Δ g⟩| ≤ ‖g‖²/(q - 2)` on `𝒵_c`** (`q ≥ 11`). -/
theorem abs_form_Dop_Z_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (h11 : 11 ≤ Fintype.card F) (c : F) {g : F → ℝ} (hg : g c = 0) (hp : Sp c g = 0)
    (hm : Sm c g = 0) :
    |∑ a, g a * Dop c g a| ≤ (∑ a, g a ^ 2) / ((Fintype.card F : ℝ) - 2) := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq : (11 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast h11
  have hq3 : 0 < q - 3 := by linarith
  have hq2 : 0 < q - 2 := by linarith
  have hq1 : 0 < q + 1 := by linarith
  rw [form_Dop_Z h3 hk c hg hp hm]
  have hcross := abs_cross_le hF c g
  rw [← sum_sq_split c hg] at hcross
  set G := ∑ a, g a ^ 2 with hG
  have hG0 : 0 ≤ G := sum_nonneg fun a _ => sq_nonneg _
  set X := ∑ a, gPlus c g a * Cop (gMinus c g) a with hX
  have hcoef := sym_coef_le hq
  have h4 : 0 ≤ 4 / ((q - 3) * (q + 1)) := by positivity
  calc |-G / ((q - 3) * (q - 2)) - 4 / ((q - 3) * (q + 1)) * X|
      ≤ |-G / ((q - 3) * (q - 2))| + |4 / ((q - 3) * (q + 1)) * X| := abs_sub _ _
    _ = G / ((q - 3) * (q - 2)) + 4 / ((q - 3) * (q + 1)) * |X| := by
        rw [abs_mul, abs_of_nonneg h4, abs_div, abs_neg, abs_of_nonneg hG0,
          abs_of_pos (by positivity : (0 : ℝ) < (q - 3) * (q - 2))]
    _ ≤ G / ((q - 3) * (q - 2)) + 4 / ((q - 3) * (q + 1)) * (Real.sqrt q * G / 2) := by
        gcongr
    _ = (1 / ((q - 3) * (q - 2)) + 2 * Real.sqrt q / ((q - 3) * (q + 1))) * G := by ring
    _ ≤ 1 / (q - 2) * G := mul_le_mul_of_nonneg_right hcoef hG0
    _ = G / (q - 2) := by ring

/-- **The quadratic form of `Δ` splits**: for `f = t 𝐡_c + g`, `g ∈ 𝒵_c`,
`⟨f, Δ f⟩ = t² ‖𝐡_c‖²/(q - 2) + ⟨g, Δ g⟩`. -/
theorem form_Dop_split (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c : F) (t : ℝ) {g : F → ℝ} (hg : g c = 0) (hp : Sp c g = 0) (hm : Sm c g = 0) :
    ∑ a, (t * sectorContrast c a + g a) * Dop c (fun x => t * sectorContrast c x + g x) a =
      t ^ 2 * ((Fintype.card F : ℝ) - 1) / ((Fintype.card F : ℝ) - 2) +
        ∑ a, g a * Dop c g a := by
  have h1 : ∑ a, sectorContrast c a * Dop c g a = 0 := by
    rw [sum_sector_mul, Sp_Dop hF h3 hk c hg hp hm, Sm_Dop hF h3 hk c hg hp hm, sub_zero]
  have h2 : ∑ a, sectorContrast c a * g a = 0 := by
    rw [sum_sector_mul, hp, hm, sub_zero]
  have e : ∀ a, (t * sectorContrast c a + g a) * Dop c (fun x => t * sectorContrast c x + g x) a =
      t ^ 2 / ((Fintype.card F : ℝ) - 2) * (sectorContrast c a * sectorContrast c a) +
        t * (sectorContrast c a * Dop c g a) +
        t / ((Fintype.card F : ℝ) - 2) * (sectorContrast c a * g a) + g a * Dop c g a := by
    intro a
    rw [Dop_lin, Dop_sector hF h3 hk]
    ring
  simp only [e, sum_add_distrib, ← mul_sum, h1, h2, mul_zero, add_zero]
  have hss : ∑ a, sectorContrast c a * sectorContrast c a = (Fintype.card F : ℝ) - 1 := by
    rw [← sum_sector_sq hF h3 c]
    exact sum_congr rfl fun a _ => (sq _).symm
  rw [hss]
  ring

/-- **The symmetric part of `Δ` has norm at most `1/(q - 2)`**: `|⟨f, Δ f⟩| ≤ ‖f‖²/(q - 2)` for
every mean-zero function `f` on `V_c` (`q ≥ 11`). -/
theorem abs_form_Dop_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (h11 : 11 ≤ Fintype.card F) (c : F) {f : F → ℝ} (hf : f c = 0) (h0 : ∑ a, f a = 0) :
    |∑ a, f a * Dop c f a| ≤ (∑ a, f a ^ 2) / ((Fintype.card F : ℝ) - 2) := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq : (11 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast h11
  have hq2 : 0 < q - 2 := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set m : ℝ := (q - 1) / 2 with hmdef
  have hm0 : m ≠ 0 := by rw [hmdef]; linarith
  set t : ℝ := Sp c f / m with htdef
  set g : F → ℝ := fun a => f a - t * sectorContrast c a with hgdef
  have hfg : f = fun a => t * sectorContrast c a + g a := by
    funext a
    simp only [hgdef]
    ring
  have hgc : g c = 0 := by simp only [hgdef, hf, sectorContrast_c, mul_zero, sub_zero]
  have hSpf_Smf : Sp c f + Sm c f = 0 := by rw [← sum_eq_Sp_add_Sm c hf, h0]
  have hgp : Sp c g = 0 := by
    have : Sp c g = Sp c f - t * Sp c (sectorContrast c) := by
      rw [show g = fun a => f a - (fun x => t * sectorContrast c x) a from rfl, Sp_sub]
      unfold Sp
      rw [mul_sum]
      congr 1
      exact sum_congr rfl fun a _ => by split_ifs <;> ring
    rw [this, Sp_sector hF c, htdef]
    field_simp
    ring
  have hgm : Sm c g = 0 := by
    have : Sm c g = Sm c f - t * Sm c (sectorContrast c) := by
      rw [show g = fun a => f a - (fun x => t * sectorContrast c x) a from rfl, Sm_sub]
      unfold Sm
      rw [mul_sum]
      congr 1
      exact sum_congr rfl fun a _ => by split_ifs <;> ring
    rw [this, Sm_sector hF h3 c, htdef]
    have hSm : Sm c f = -Sp c f := by linarith
    rw [hSm]
    field_simp
    ring
  have hform : ∑ a, f a * Dop c f a = t ^ 2 * (q - 1) / (q - 2) + ∑ a, g a * Dop c g a := by
    rw [hfg]
    exact form_Dop_split hF h3 hk c t hgc hgp hgm
  have hnorm : ∑ a, f a ^ 2 = t ^ 2 * (q - 1) + ∑ a, g a ^ 2 := by
    rw [hfg]
    exact norm_sq_split hF h3 c t hgp hgm
  have hZ := abs_form_Dop_Z_le hF h3 hk h11 c hgc hgp hgm
  rw [hform, hnorm]
  have ht : 0 ≤ t ^ 2 * (q - 1) / (q - 2) := by positivity
  calc |t ^ 2 * (q - 1) / (q - 2) + ∑ a, g a * Dop c g a|
      ≤ |t ^ 2 * (q - 1) / (q - 2)| + |∑ a, g a * Dop c g a| := abs_add_le _ _
    _ ≤ t ^ 2 * (q - 1) / (q - 2) + (∑ a, g a ^ 2) / (q - 2) := by
        rw [abs_of_nonneg ht]
        linarith [hZ]
    _ = (t ^ 2 * (q - 1) + ∑ a, g a ^ 2) / (q - 2) := by ring

/-- **The bound is attained at the sector contrast**: `⟨𝐡_c, Δ 𝐡_c⟩ = ‖𝐡_c‖²/(q - 2)`. -/
theorem form_Dop_sector (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c : F) :
    ∑ a, sectorContrast c a * Dop c (sectorContrast c) a =
      (∑ a, sectorContrast c a ^ 2) / ((Fintype.card F : ℝ) - 2) := by
  rw [sum_div]
  refine sum_congr rfl fun a _ => ?_
  rw [Dop_sector hF h3 hk]
  ring

end Sarkozy.PartVRecords
