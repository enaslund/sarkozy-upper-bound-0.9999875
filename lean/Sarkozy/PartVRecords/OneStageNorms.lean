module

public import Sarkozy.PartVRecords.OneStage
public import Sarkozy.TraceMixing.PaleyTriple

@[expose] public section

/-!
# The operators of the one-stage replacement at one prime (`lem:record:one-stage-folded-e`(c))

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(c). On the functions on
`V_c = F ∖ {c}` (here: functions `f : F → ℝ` with `f c = 0`; the norms are the `ℓ²` norms, which
are those of `L²` of the uniform law of `V_c` up to the common factor `1/(q - 1)`):

* `𝒦₊ f(a) = ∑_{a'} 𝒦₊^{(c)}(a, a') f(a')` (`Kop`) and its adjoint (`KopT`);
* `𝒦₀ = (J - I)/(q - 2)` on `V_c`, the conditional coupling of the record being replaced (`K0op`);
* the sector contrast `𝐡_c = 𝟙_{V_c^+} - 𝟙_{V_c^-}` (`sectorContrast`).

**Proved:**
* both couplings fix the constants of `V_c` (`Kop_one`, `KopT_one`, `K0op_one`) and preserve the
  mean-zero functions (`sum_Kop`, `sum_KopT`; `K0op_meanZero`: `𝒦₀ f = -f/(q - 2)` there, so
  `‖𝒦₀‖ = 1/(q - 2)` on them);
* `𝒦₊ 𝐡_c = 𝒦₊^* 𝐡_c = 0` (`Kop_sector`, `KopT_sector`; the sector balance of (b)), `𝐡_c` has mean
  zero (`sum_sectorContrast`), hence `Δ 𝐡_c = Δ^* 𝐡_c = 𝐡_c/(q - 2)` for `Δ = 𝒦₊ - 𝒦₀`
  (`Delta_sector`, `DeltaT_sector`): **the symmetric part of `Δ` attains `1/(q - 2)` at the sector
  contrast**;
* **`‖𝒦₊‖ ≤ κ^{fold} = (√q + 3)/(q - 3)` on the mean-zero functions** (`Kop_norm_sq_le`), by the
  paper's argument: `M_c = (J - I + 𝐂_c)/2` with `‖𝐂_c‖ ≤ √q` (WP-S's `norm_paleyOp`), and the
  Schur test `‖M_c^{+-}‖ ≤ k + 1`.

**Not proved here:** the upper bound `‖Sym Δ‖ ≤ 1/(q - 2)` and `‖Δ‖ ≤ k_new(q) r` (the
decomposition into `𝐡_c` and the sector-centred space `𝒵_c`), and part (d).
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- `𝒦₊ f (a) = ∑_{a'} 𝒦₊^{(c)}(a, a') f(a')`. -/
noncomputable def Kop (c : F) (f : F → ℝ) (a : F) : ℝ := ∑ a', Kplus c a a' * f a'

/-- The adjoint `𝒦₊^* f (a') = ∑_a 𝒦₊^{(c)}(a, a') f(a)`. -/
noncomputable def KopT (c : F) (f : F → ℝ) (a' : F) : ℝ := ∑ a, Kplus c a a' * f a

/-- `𝒦₀ = (J - I)/(q - 2)` on `V_c`: the average over the other labels of `V_c`. -/
noncomputable def K0op (c : F) (f : F → ℝ) (a : F) : ℝ :=
  if a = c then 0 else (∑ a', if a' = c ∨ a' = a then 0 else f a') / ((Fintype.card F : ℝ) - 2)

/-- The indicator of `V_c`. -/
noncomputable def oneV (c : F) (a : F) : ℝ := if a = c then 0 else 1

/-- **The sector contrast** `𝐡_c = 𝟙_{V_c^+} - 𝟙_{V_c^-}`. -/
noncomputable def sectorContrast (c : F) (a : F) : ℝ :=
  (if χ (a - c) = 1 then 1 else 0) - (if χ (a - c) = -1 then 1 else 0)

/-! ## Constants and mean-zero functions -/

/-- `𝒦₊ 𝟙_{V_c} = 𝟙_{V_c}`. -/
theorem Kop_one (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c a : F) :
    Kop c (oneV c) a = oneV c a := by
  unfold Kop oneV
  have : ∀ a', Kplus c a a' * (if a' = c then 0 else 1) = Kplus c a a' := by
    intro a'
    by_cases h : a' = c
    · subst h
      simp [Kplus_right_eq]
    · simp [h]
  simp only [this, Kplus_row_sum' hF h3 hk]

/-- `𝒦₊^* 𝟙_{V_c} = 𝟙_{V_c}`. -/
theorem KopT_one (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c a' : F) :
    KopT c (oneV c) a' = oneV c a' := by
  unfold KopT oneV
  have : ∀ a, Kplus c a a' * (if a = c then 0 else 1) = Kplus c a a' := by
    intro a
    by_cases h : a = c
    · subst h
      simp [Kplus_left_eq]
    · simp [h]
  simp only [this, Kplus_col_sum' hF h3 hk]

/-- `𝒦₊` preserves sums of functions on `V_c` (column sums one); in particular mean-zero
functions go to mean-zero functions. -/
theorem sum_Kop (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c : F)
    {f : F → ℝ} (hf : f c = 0) : ∑ a, Kop c f a = ∑ a, f a := by
  unfold Kop
  rw [sum_comm]
  refine sum_congr rfl fun a' _ => ?_
  rw [← sum_mul, Kplus_col_sum' hF h3 hk]
  by_cases h : a' = c
  · subst h
    simp [hf]
  · simp [h]

theorem sum_KopT (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c : F)
    {f : F → ℝ} (hf : f c = 0) : ∑ a', KopT c f a' = ∑ a, f a := by
  unfold KopT
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_mul, Kplus_row_sum' hF h3 hk]
  by_cases h : a = c
  · subst h
    simp [hf]
  · simp [h]

omit [Field F] [DecidableEq F] in
theorem card_three_le (h3 : Fintype.card F % 4 = 3) : (3 : ℝ) ≤ Fintype.card F := by
  have : 3 ≤ Fintype.card F := by omega
  exact_mod_cast this

omit [Field F] in
/-- **`𝒦₀ f = -f/(q - 2)` on the mean-zero functions of `V_c`**, so `‖𝒦₀‖ = 1/(q - 2)` there. -/
theorem K0op_meanZero (c : F) {f : F → ℝ} (hf : f c = 0) (h0 : ∑ a, f a = 0) {a : F}
    (ha : a ≠ c) : K0op c f a = -f a / ((Fintype.card F : ℝ) - 2) := by
  unfold K0op
  rw [ite_eq_right ha]
  congr 1
  have : ∀ a', (if a' = c ∨ a' = a then 0 else f a') = f a' - (if a' = a then f a else 0) := by
    intro a'
    by_cases h1 : a' = c
    · subst h1
      simp [hf, Ne.symm ha]
    · by_cases h2 : a' = a
      · subst h2
        simp
      · simp [h1, h2]
  simp only [this, sum_sub_distrib, h0, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
  ring

omit [Field F] in
/-- `𝒦₀ 𝟙_{V_c} = 𝟙_{V_c}`. -/
theorem K0op_one (h3 : Fintype.card F % 4 = 3) (c a : F) (ha : a ≠ c) : K0op c (oneV c) a = 1 := by
  unfold K0op oneV
  rw [ite_eq_right ha]
  have hq := card_three_le h3 (F := F)
  have hcount : ∑ a' : F, (if a' = c ∨ a' = a then (0 : ℝ) else if a' = c then 0 else 1) =
      (Fintype.card F : ℝ) - 2 := by
    have : ∀ a' : F, (if a' = c ∨ a' = a then (0 : ℝ) else if a' = c then 0 else 1) =
        1 - (if a' = c then 1 else 0) - (if a' = a then 1 else 0) := by
      intro a'
      by_cases h1 : a' = c
      · subst h1
        simp [Ne.symm ha]
      · by_cases h2 : a' = a
        · subst h2
          simp [h1]
        · simp [h1, h2]
    simp only [this, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
      Finset.sum_ite_eq', mem_univ, ↓reduceIte]
    ring
  rw [hcount, div_self]
  linarith

/-! ## The sector contrast -/

theorem sectorContrast_c (c : F) : sectorContrast c c = 0 := by
  simp [sectorContrast]

/-- `𝒦₊ 𝐡_c = 0`: from each `a`, the coupling puts mass `1/2` on each sector. -/
theorem Kop_sector (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c a : F) :
    Kop c (sectorContrast c) a = 0 := by
  by_cases ha : a = c
  · subst ha
    unfold Kop
    simp [Kplus_left_eq]
  · unfold Kop sectorContrast
    have e : ∀ a', Kplus c a a' * ((if χ (a' - c) = 1 then (1 : ℝ) else 0) -
        (if χ (a' - c) = -1 then 1 else 0)) = (if χ (a' - c) = 1 then Kplus c a a' else 0) -
        (if χ (a' - c) = -1 then Kplus c a a' else 0) := by
      intro a'
      split_ifs <;> ring
    simp only [e, sum_sub_distrib, Kplus_row_sector hF h3 hk ha (Or.inl rfl),
      Kplus_row_sector hF h3 hk ha (Or.inr rfl), sub_self]

/-- `𝒦₊^* 𝐡_c = 0`: every column receives `1/2` from each sector. -/
theorem KopT_sector (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c a' : F) : KopT c (sectorContrast c) a' = 0 := by
  by_cases ha : a' = c
  · subst ha
    unfold KopT
    simp [Kplus_right_eq]
  · unfold KopT sectorContrast
    have e : ∀ a, Kplus c a a' * ((if χ (a - c) = 1 then (1 : ℝ) else 0) -
        (if χ (a - c) = -1 then 1 else 0)) = (if χ (a - c) = 1 then Kplus c a a' else 0) -
        (if χ (a - c) = -1 then Kplus c a a' else 0) := by
      intro a
      split_ifs <;> ring
    simp only [e, sum_sub_distrib, Kplus_col_sector hF h3 hk ha (Or.inl rfl),
      Kplus_col_sector hF h3 hk ha (Or.inr rfl), sub_self]

/-- **`𝐡_c` has mean zero**: the two sectors have `(q - 1)/2` elements each. -/
theorem sum_sectorContrast (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c : F) :
    ∑ a, sectorContrast c a = 0 := by
  unfold sectorContrast
  rw [sum_sub_distrib, sum_boole, sum_boole]
  have h1 := card_out hF c
  have h2 := card_in hF h3 c
  have hfilt : (univ.filter fun b => χ (c - b) = 1) = univ.filter fun b => χ (b - c) = -1 := by
    ext b
    simp only [mem_filter, mem_univ, true_and, chi_swap h3 c b]
    constructor <;> intro h <;> linarith
  rw [hfilt] at h2
  have : ((univ.filter fun b => χ (b - c) = 1).card : ℤ) =
      ((univ.filter fun b => χ (b - c) = -1).card : ℤ) := by linarith
  have : ((univ.filter fun b => χ (b - c) = 1).card : ℝ) =
      ((univ.filter fun b => χ (b - c) = -1).card : ℝ) := by exact_mod_cast this
  rw [this, sub_self]

/-- **`Δ 𝐡_c = 𝐡_c/(q - 2)`** on `V_c`, `Δ = 𝒦₊ - 𝒦₀`. -/
theorem Delta_sector (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c a : F) (ha : a ≠ c) :
    Kop c (sectorContrast c) a - K0op c (sectorContrast c) a =
      sectorContrast c a / ((Fintype.card F : ℝ) - 2) := by
  rw [Kop_sector hF h3 hk, K0op_meanZero c (sectorContrast_c c) (sum_sectorContrast hF h3 c) ha]
  ring

/-- **`Δ^* 𝐡_c = 𝐡_c/(q - 2)`** on `V_c` (`𝒦₀` is symmetric). -/
theorem DeltaT_sector (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c a : F) (ha : a ≠ c) :
    KopT c (sectorContrast c) a - K0op c (sectorContrast c) a =
      sectorContrast c a / ((Fintype.card F : ℝ) - 2) := by
  rw [KopT_sector hF h3 hk, K0op_meanZero c (sectorContrast_c c) (sum_sectorContrast hF h3 c) ha]
  ring

/-! ## `‖𝒦₊‖ ≤ (√q + 3)/(q - 3)` on the mean-zero functions -/

/-- The Paley matrix `(𝐂 f)(a) = ∑_{a'} χ(a' - a) f(a')`. -/
noncomputable def Cop (f : F → ℝ) (a : F) : ℝ := ∑ a', (χ (a' - a) : ℝ) * f a'

/-- **`‖𝐂 f‖² = q ‖f‖² - (∑ f)²`** (`lem:square-shift`(c), from WP-S's `norm_paleyOp`). -/
theorem sum_Cop_sq (hF : ringChar F ≠ 2) (f : F → ℝ) :
    ∑ a, Cop f a ^ 2 = (Fintype.card F : ℝ) * ∑ a, f a ^ 2 - (∑ a, f a) ^ 2 := by
  have h := norm_paleyOp hF f
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hP : ∀ s, paleyOp f s = (Fintype.card F : ℝ)⁻¹ * Cop f s := fun s => rfl
  simp only [hP, mul_pow] at h
  rw [← mul_sum] at h
  field_simp at h
  linarith

omit [Field F] [DecidableEq F] in
/-- Minkowski: `∑ (u + v)² ≤ (A + B)²` when `∑ u² ≤ A²`, `∑ v² ≤ B²`, `A, B ≥ 0`. -/
theorem sum_sq_add_le {u v : F → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∑ a, u a ^ 2 ≤ A ^ 2) (hv : ∑ a, v a ^ 2 ≤ B ^ 2) :
    ∑ a, (u a + v a) ^ 2 ≤ (A + B) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ u v
  have hu0 : 0 ≤ ∑ a, u a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
  have hv0 : 0 ≤ ∑ a, v a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
  have huv : (∑ a, u a * v a) ^ 2 ≤ (A * B) ^ 2 := by
    calc (∑ a, u a * v a) ^ 2 ≤ (∑ a, u a ^ 2) * ∑ a, v a ^ 2 := hcs
      _ ≤ A ^ 2 * B ^ 2 := mul_le_mul hu hv hv0 (sq_nonneg _)
      _ = (A * B) ^ 2 := by ring
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have huv' : ∑ a, u a * v a ≤ A * B := by nlinarith [sq_nonneg (∑ a, u a * v a + A * B)]
  have hexp : ∑ a, (u a + v a) ^ 2 = ∑ a, u a ^ 2 + 2 * ∑ a, u a * v a + ∑ a, v a ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by ring
  rw [hexp]
  nlinarith

/-- The relation part: for `a ∈ V_c` and `f` on `V_c` with mean zero,
`∑_{a'} M_c(a, a') f(a') = (-f(a) + (𝐂 f)(a))/2`. -/
theorem Mrel_apply (c : F) {f : F → ℝ} (hf : f c = 0) (h0 : ∑ a, f a = 0) {a : F} (ha : a ≠ c) :
    ∑ a', Mrel c a a' * f a' = (-f a + Cop f a) / 2 := by
  have hpt : ∀ a', Mrel c a a' * f a' =
      ((((χ (a' - a) : ℤ) : ℝ) ^ 2 + ((χ (a' - a) : ℤ) : ℝ)) / 2) * f a' := by
    intro a'
    rw [← two_mul_indicator_real]
    unfold Mrel
    by_cases h1 : a' = c
    · subst h1
      simp [hf]
    · by_cases h2 : χ (a' - a) = 1
      · simp only [ha, h1, h2, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        ring
      · simp only [h2, and_false, ↓reduceIte]
        ring
  simp only [hpt]
  have hsq : ∀ a', (((χ (a' - a) : ℤ) : ℝ) ^ 2) = 1 - (if a' = a then 1 else 0) := by
    intro a'
    have := chi_sq_eq (F := F) (a' - a)
    by_cases h : a' = a
    · subst h
      simp
    · have hne : a' - a ≠ 0 := sub_ne_zero.mpr h
      rw [ite_eq_right hne] at this
      rw [ite_eq_right h]
      exact_mod_cast this
  unfold Cop
  simp only [hsq]
  have e : ∀ a', ((1 - (if a' = a then (1 : ℝ) else 0) + ((χ (a' - a) : ℤ) : ℝ)) / 2) * f a' =
      (f a' - (if a' = a then f a else 0) + ((χ (a' - a) : ℤ) : ℝ) * f a') / 2 := by
    intro a'
    split_ifs with h
    · subst h
      ring
    · ring
  simp only [e]
  rw [← sum_div, sum_add_distrib, sum_sub_distrib, h0, Finset.sum_ite_eq', ite_eq_left (mem_univ _)]
  ring

/-- Schur test for the block `M_c^{+-}`: `‖M_c^{+-} f‖² ≤ (k + 1)² ‖f‖²`. -/
theorem Mpm_schur (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c : F) (f : F → ℝ) :
    ∑ a, (∑ a', Mpm c a a' * f a') ^ 2 ≤ (kP F + 1) ^ 2 * ∑ a, f a ^ 2 := by
  have hk1 : 0 ≤ kP F + 1 := by
    have := card_three_le h3 (F := F)
    unfold kP
    linarith
  have hM01 : ∀ a a', Mpm c a a' ^ 2 = Mpm c a a' := by
    intro a a'
    unfold Mpm
    split_ifs <;> norm_num
  have hM0 : ∀ a a', 0 ≤ Mpm c a a' := by
    intro a a'
    unfold Mpm
    split_ifs <;> norm_num
  -- row and column sums at most `k + 1`
  have hrow : ∀ a, ∑ a', Mpm c a a' ≤ kP F + 1 := by
    intro a
    unfold Mpm
    by_cases ha : χ (a - c) = 1
    · have hac : a ≠ c := ne_of_chi_eq ha (Or.inl rfl)
      have hc := card_real_of_four (rowCount hF h3 hac (σ' := -1) (Or.inr rfl))
      have e : ∀ a' : F, (if χ (a - c) = 1 ∧ χ (a' - c) = -1 ∧ χ (a' - a) = 1 then (1 : ℝ)
          else 0) = if χ (a' - a) = 1 ∧ χ (a' - c) = -1 then 1 else 0 := by
        intro a'
        simp only [ha, true_and]
        by_cases h1 : χ (a' - c) = -1 <;> by_cases h2 : χ (a' - a) = 1 <;>
          simp only [h1, h2, and_self, and_true, and_false, ↓reduceIte]
      simp only [e]
      rw [sum_boole, hc]
      simp only [ha, and_self, ↓reduceIte]
      unfold kP
      push_cast
      linarith
    · have e : ∀ a' : F, (if χ (a - c) = 1 ∧ χ (a' - c) = -1 ∧ χ (a' - a) = 1 then (1 : ℝ)
          else 0) = 0 := fun a' => by simp only [ha, false_and, ↓reduceIte]
      simp only [e, sum_const_zero]
      exact hk1
  have hcol : ∀ a', ∑ a, Mpm c a a' ≤ kP F + 1 := by
    intro a'
    unfold Mpm
    by_cases ha : χ (a' - c) = -1
    · have hac : a' ≠ c := ne_of_chi_eq ha (Or.inr rfl)
      have hc := card_real_of_four (colCount hF h3 hac (σ := 1) (Or.inl rfl))
      have e : ∀ a : F, (if χ (a - c) = 1 ∧ χ (a' - c) = -1 ∧ χ (a' - a) = 1 then (1 : ℝ)
          else 0) = if χ (a' - a) = 1 ∧ χ (a - c) = 1 then 1 else 0 := by
        intro a
        simp only [ha, true_and]
        by_cases h1 : χ (a - c) = 1 <;> by_cases h2 : χ (a' - a) = 1 <;>
          simp only [h1, h2, and_self, and_true, and_false, ↓reduceIte]
      simp only [e]
      rw [sum_boole, hc]
      simp only [ha, and_self, ↓reduceIte]
      unfold kP
      push_cast
      linarith
    · have e : ∀ a : F, (if χ (a - c) = 1 ∧ χ (a' - c) = -1 ∧ χ (a' - a) = 1 then (1 : ℝ)
          else 0) = 0 := fun a => by simp only [ha, false_and, and_false, ↓reduceIte]
      simp only [e, sum_const_zero]
      exact hk1
  -- Cauchy–Schwarz row by row
  have hCS : ∀ a, (∑ a', Mpm c a a' * f a') ^ 2 ≤
      (kP F + 1) * ∑ a', Mpm c a a' * f a' ^ 2 := by
    intro a
    have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun a' => Mpm c a a')
      (fun a' => Mpm c a a' * f a')
    have e1 : ∑ a', Mpm c a a' * (Mpm c a a' * f a') = ∑ a', Mpm c a a' * f a' := by
      refine sum_congr rfl fun a' _ => ?_
      rw [← mul_assoc, ← sq, hM01]
    have e2 : ∑ a', Mpm c a a' ^ 2 = ∑ a', Mpm c a a' := by simp only [hM01]
    have e3 : ∑ a', (Mpm c a a' * f a') ^ 2 = ∑ a', Mpm c a a' * f a' ^ 2 := by
      refine sum_congr rfl fun a' _ => ?_
      rw [mul_pow, hM01]
    rw [e1, e2, e3] at h
    have hnn : 0 ≤ ∑ a', Mpm c a a' * f a' ^ 2 :=
      sum_nonneg fun a' _ => mul_nonneg (hM0 a a') (sq_nonneg _)
    exact h.trans (mul_le_mul_of_nonneg_right (hrow a) hnn)
  calc ∑ a, (∑ a', Mpm c a a' * f a') ^ 2
      ≤ ∑ a, (kP F + 1) * ∑ a', Mpm c a a' * f a' ^ 2 := sum_le_sum fun a _ => hCS a
    _ = (kP F + 1) * ∑ a', f a' ^ 2 * ∑ a, Mpm c a a' := by
        rw [← mul_sum, sum_comm]
        congr 1
        refine sum_congr rfl fun a' _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun a _ => by ring
    _ ≤ (kP F + 1) * ∑ a', f a' ^ 2 * (kP F + 1) := by
        apply mul_le_mul_of_nonneg_left _ hk1
        exact sum_le_sum fun a' _ => mul_le_mul_of_nonneg_left (hcol a') (sq_nonneg _)
    _ = (kP F + 1) ^ 2 * ∑ a, f a ^ 2 := by
        rw [← sum_mul]
        ring

/-- **`lem:record:one-stage-folded-e`(c): `‖𝒦₊ f‖ ≤ κ^{fold} ‖f‖`, `κ^{fold} = (√q + 3)/(q - 3)`,
on the mean-zero functions of `V_c`.** -/
theorem Kop_norm_sq_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c : F) {f : F → ℝ} (hf : f c = 0) (h0 : ∑ a, f a = 0) :
    ∑ a, Kop c f a ^ 2 ≤
      ((Real.sqrt (Fintype.card F : ℝ) + 3) / ((Fintype.card F : ℝ) - 3)) ^ 2 * ∑ a, f a ^ 2 := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set N : ℝ := Real.sqrt (∑ a, f a ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hNsq : N ^ 2 = ∑ a, f a ^ 2 := Real.sq_sqrt (sum_nonneg fun a _ => sq_nonneg _)
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  have hkq : q = 4 * kP F + 3 := by
    rw [hq]
    unfold kP
    ring
  -- `u = M_c f`, `v = M_c^{+-} f`
  set u : F → ℝ := fun a => ∑ a', Mrel c a a' * f a' with hu
  set v : F → ℝ := fun a => ∑ a', Mpm c a a' * f a' with hv
  have hKuv : ∀ a, Kop c f a = (1 / (2 * kP F)) * u a + (-(1 / (2 * kP F * (kP F + 1)))) * v a := by
    intro a
    unfold Kop Kplus
    simp only [hu, hv, mul_sum]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun a' _ => by ring
  -- `‖u‖ ≤ (1 + √q)/2 ‖f‖`
  have hu_bound : ∑ a, u a ^ 2 ≤ ((1 + Real.sqrt q) / 2 * N) ^ 2 := by
    have hpt : ∀ a, u a ^ 2 ≤ ((-f a + Cop f a) / 2) ^ 2 := by
      intro a
      by_cases ha : a = c
      · subst ha
        have : u a = 0 := by
          simp only [hu]
          exact sum_eq_zero fun a' _ => by simp [Mrel]
        rw [this, zero_pow two_ne_zero]
        exact sq_nonneg _
      · rw [show u a = (-f a + Cop f a) / 2 from Mrel_apply c hf h0 ha]
    have h1 : ∑ a, ((-f a / 2) + Cop f a / 2) ^ 2 ≤ (N / 2 + Real.sqrt q * N / 2) ^ 2 := by
      apply sum_sq_add_le (by positivity) (by positivity)
      · have : ∑ a, (-f a / 2) ^ 2 = N ^ 2 / 4 := by
          rw [hNsq, sum_div]
          exact sum_congr rfl fun a _ => by ring
        rw [this]
        nlinarith
      · have h := sum_Cop_sq hF f
        rw [h0] at h
        have : ∑ a, (Cop f a / 2) ^ 2 = (q * ∑ a, f a ^ 2 - 0 ^ 2) / 4 := by
          rw [← h, sum_div]
          exact sum_congr rfl fun a _ => by ring
        rw [this, ← hNsq]
        have : (Real.sqrt q * N / 2) ^ 2 = q * N ^ 2 / 4 := by
          rw [div_pow, mul_pow, hsq]
          norm_num
        rw [this]
        nlinarith
    calc ∑ a, u a ^ 2 ≤ ∑ a, ((-f a + Cop f a) / 2) ^ 2 := sum_le_sum fun a _ => hpt a
      _ = ∑ a, ((-f a / 2) + Cop f a / 2) ^ 2 := sum_congr rfl fun a _ => by ring
      _ ≤ (N / 2 + Real.sqrt q * N / 2) ^ 2 := h1
      _ = ((1 + Real.sqrt q) / 2 * N) ^ 2 := by ring
  -- `‖v‖ ≤ (k + 1) ‖f‖`
  have hk1 : 0 < kP F + 1 := by linarith
  have hv_bound : ∑ a, v a ^ 2 ≤ ((kP F + 1) * N) ^ 2 := by
    have := Mpm_schur hF h3 c f
    rw [mul_pow, hNsq]
    exact this
  -- combine
  have hα : 0 ≤ 1 / (2 * kP F) := by positivity
  have hβ : 0 ≤ 1 / (2 * kP F * (kP F + 1)) := by positivity
  have hcomb : ∑ a, ((1 / (2 * kP F)) * u a + (-(1 / (2 * kP F * (kP F + 1)))) * v a) ^ 2 ≤
      ((1 / (2 * kP F)) * ((1 + Real.sqrt q) / 2 * N) +
        (1 / (2 * kP F * (kP F + 1))) * ((kP F + 1) * N)) ^ 2 := by
    apply sum_sq_add_le (mul_nonneg hα (by positivity)) (mul_nonneg hβ (by positivity))
    · have : ∑ a, ((1 / (2 * kP F)) * u a) ^ 2 = (1 / (2 * kP F)) ^ 2 * ∑ a, u a ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun a _ => by ring
      rw [this, mul_pow]
      exact mul_le_mul_of_nonneg_left hu_bound (sq_nonneg _)
    · have : ∑ a, ((-(1 / (2 * kP F * (kP F + 1)))) * v a) ^ 2 =
          (1 / (2 * kP F * (kP F + 1))) ^ 2 * ∑ a, v a ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun a _ => by ring
      rw [this, mul_pow]
      exact mul_le_mul_of_nonneg_left hv_bound (sq_nonneg _)
  have hval : (1 / (2 * kP F)) * ((1 + Real.sqrt q) / 2 * N) +
      (1 / (2 * kP F * (kP F + 1))) * ((kP F + 1) * N) =
      (Real.sqrt q + 3) / (q - 3) * N := by
    rw [hkq]
    field_simp
    ring
  simp only [hKuv]
  rw [hval] at hcomb
  rw [mul_pow, hNsq] at hcomb
  exact hcomb

end Sarkozy.PartVRecords
