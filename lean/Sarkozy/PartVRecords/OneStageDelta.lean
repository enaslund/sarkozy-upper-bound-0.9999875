module

public import Sarkozy.PartVRecords.OneStageNorms

@[expose] public section

/-!
# The record difference of the one-stage replacement at one prime:
`‖Δ‖ ≤ k_new(p) r` (`lem:record:one-stage-folded-e`(c))

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(c), last display. With
`Δ = 𝒦₊ - 𝒦₀` on the mean-zero functions of `V_c` (`Dop`), the paper's proof:

* the mean-zero functions are the orthogonal sum of the multiples of the sector contrast `𝐡_c`
  and the sector-centred space `𝒵_c` (functions with zero sum on each sector) — here
  `f = t 𝐡_c + g` with `t = S₊(f)/m`, `m = (q - 1)/2` (`decomp_*`);
* `Δ 𝐡_c = 𝐡_c/(q - 2)` (`Delta_sector`) and `Δ` maps `𝒵_c` into `𝒵_c` (`Sp_Dop`, `Sm_Dop`), so
  `‖Δ f‖² = t² ‖𝐡_c‖²/(q - 2)² + ‖Δ g‖²` (`Dop_norm_sq_split`);
* on `𝒵_c`, `M_c^{+-}` is half the `(V_c^+, V_c^-)` block of the Paley matrix `𝐂_c`
  (`Mpm_apply_Z`), so `Δ g = 𝐂 g/(q - 3) - g/((q - 3)(q - 2)) - 4 [V_c^+] 𝐂 g₋/((q - 3)(q + 1))`
  (`Dop_apply_Z`) and `‖Δ g‖ ≤ κ_Δ ‖g‖` with
  `κ_Δ = √q/(q - 3) + 1/((q - 3)(q - 2)) + 4√q/((q - 3)(q + 1))` (`Dop_Z_norm_sq_le`);
* `κ_Δ ≥ 1/(q - 2)`, so **`‖Δ f‖ ≤ κ_Δ ‖f‖` for every mean-zero `f`** (`Dop_norm_sq_le`);
* `κ_Δ = k_new(p) r` with `k_new(p) = (1 + 5q')/((1 - 3q')(1 + q')) + q'r/((1 - 3q')(1 - 2q'))`,
  `q' = 1/p`, `r = p^{-1/2}` (`kappaDelta_eq_knew`).

The upper bound `‖Sym Δ‖ ≤ 1/(p - 2)` on `𝒵_c` and part (d) (the block) are not formalized.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- `Δ f = 𝒦₊ f - 𝒦₀ f`. -/
noncomputable def Dop (c : F) (f : F → ℝ) (a : F) : ℝ := Kop c f a - K0op c f a

/-- The sum over the sector `V_c^+`. -/
noncomputable def Sp (c : F) (f : F → ℝ) : ℝ := ∑ a, if χ (a - c) = 1 then f a else 0

/-- The sum over the sector `V_c^-`. -/
noncomputable def Sm (c : F) (f : F → ℝ) : ℝ := ∑ a, if χ (a - c) = -1 then f a else 0

/-- The constant `κ_Δ = √q/(q - 3) + 1/((q - 3)(q - 2)) + 4√q/((q - 3)(q + 1))`. -/
noncomputable def kappaDelta (q : ℝ) : ℝ :=
  Real.sqrt q / (q - 3) + 1 / ((q - 3) * (q - 2)) + 4 * Real.sqrt q / ((q - 3) * (q + 1))

/-- The paper's `k_new` as a function of `q' = 1/p` and `r = p^{-1/2}`. -/
noncomputable def knew (q' r : ℝ) : ℝ :=
  (1 + 5 * q') / ((1 - 3 * q') * (1 + q')) + q' * r / ((1 - 3 * q') * (1 - 2 * q'))

/-- **`κ_Δ = k_new(p) r`**, `r = p^{-1/2}`, `q' = 1/p`. -/
theorem kappaDelta_eq_knew {p : ℝ} (hp : 3 < p) :
    kappaDelta p = knew (1 / p) (1 / Real.sqrt p) * (1 / Real.sqrt p) := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have h3 : p - 3 ≠ 0 := by linarith
  have h2 : p - 2 ≠ 0 := by linarith
  have h1 : p + 1 ≠ 0 := by linarith
  unfold kappaDelta knew
  have e1 : 1 - 3 * (1 / p) = (p - 3) / p := by field_simp
  have e2 : 1 + 1 / p = (p + 1) / p := by field_simp
  have e3 : 1 - 2 * (1 / p) = (p - 2) / p := by field_simp
  rw [e1, e2, e3]
  field_simp
  rw [hs2]
  ring

/-! ## Sector sums -/

theorem sum_eq_Sp_add_Sm (c : F) {f : F → ℝ} (hf : f c = 0) : ∑ a, f a = Sp c f + Sm c f :=
  sum_split_sectors f hf

theorem Sp_sub (c : F) (u v : F → ℝ) : Sp c (fun a => u a - v a) = Sp c u - Sp c v := by
  unfold Sp
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun a _ => by split_ifs <;> ring

theorem Sm_sub (c : F) (u v : F → ℝ) : Sm c (fun a => u a - v a) = Sm c u - Sm c v := by
  unfold Sm
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun a _ => by split_ifs <;> ring

theorem card_sector_plus (hF : ringChar F ≠ 2) (c : F) :
    ((univ.filter fun a => χ (a - c) = 1).card : ℝ) = ((Fintype.card F : ℝ) - 1) / 2 := by
  have h := card_out hF c
  have : (2 : ℝ) * ((univ.filter fun b => χ (b - c) = 1).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    exact_mod_cast h
  linarith

theorem card_sector_minus (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c : F) :
    ((univ.filter fun a => χ (a - c) = -1).card : ℝ) = ((Fintype.card F : ℝ) - 1) / 2 := by
  have h := card_in hF h3 c
  have hfilt : (univ.filter fun b => χ (c - b) = 1) = univ.filter fun b => χ (b - c) = -1 := by
    ext b
    simp only [mem_filter, mem_univ, true_and, chi_swap h3 c b]
    constructor <;> intro h' <;> linarith
  rw [hfilt] at h
  have : (2 : ℝ) * ((univ.filter fun b => χ (b - c) = -1).card : ℝ) =
      (Fintype.card F : ℝ) - 1 := by exact_mod_cast h
  linarith

theorem Sp_sector (hF : ringChar F ≠ 2) (c : F) :
    Sp c (sectorContrast c) = ((Fintype.card F : ℝ) - 1) / 2 := by
  unfold Sp sectorContrast
  have : ∀ a : F, (if χ (a - c) = 1 then (if χ (a - c) = 1 then (1 : ℝ) else 0) -
      (if χ (a - c) = -1 then 1 else 0) else 0) = if χ (a - c) = 1 then 1 else 0 := by
    intro a
    by_cases h : χ (a - c) = 1
    · have h1 : (1 : ℤ) ≠ -1 := by decide
      simp only [h, h1, ↓reduceIte, sub_zero]
    · simp only [h, ↓reduceIte]
  simp only [this]
  rw [sum_boole, card_sector_plus hF c]

theorem Sm_sector (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c : F) :
    Sm c (sectorContrast c) = -(((Fintype.card F : ℝ) - 1) / 2) := by
  unfold Sm sectorContrast
  have : ∀ a : F, (if χ (a - c) = -1 then (if χ (a - c) = 1 then (1 : ℝ) else 0) -
      (if χ (a - c) = -1 then 1 else 0) else 0) = -(if χ (a - c) = -1 then 1 else 0) := by
    intro a
    by_cases h : χ (a - c) = -1
    · have h1 : (-1 : ℤ) ≠ 1 := by decide
      simp only [h, h1, ↓reduceIte, zero_sub]
    · simp only [h, ↓reduceIte, neg_zero]
  simp only [this, sum_neg_distrib]
  rw [sum_boole, card_sector_minus hF h3 c]

/-- The inner product with the sector contrast is the difference of the sector sums. -/
theorem sum_sector_mul (c : F) (u : F → ℝ) :
    ∑ a, sectorContrast c a * u a = Sp c u - Sm c u := by
  unfold Sp Sm sectorContrast
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun a _ => by split_ifs <;> ring

theorem sum_sector_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c : F) :
    ∑ a, sectorContrast c a ^ 2 = (Fintype.card F : ℝ) - 1 := by
  have : ∀ a, sectorContrast c a ^ 2 = sectorContrast c a * sectorContrast c a := fun a => sq _
  simp only [this, sum_sector_mul, Sp_sector hF, Sm_sector hF h3]
  ring

/-- `S₊(𝒦₊ g) = (1/2) ∑ g` (column sector sums `1/2`). -/
theorem Sp_Kop (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c : F)
    {g : F → ℝ} (hg : g c = 0) : Sp c (Kop c g) = (1 / 2) * ∑ a, g a := by
  unfold Sp Kop
  have e : ∀ a : F, (if χ (a - c) = 1 then ∑ a', Kplus c a a' * g a' else 0) =
      ∑ a', (if χ (a - c) = 1 then Kplus c a a' else 0) * g a' := by
    intro a
    split_ifs <;> simp
  simp only [e]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun a' _ => ?_
  rw [← sum_mul]
  by_cases ha' : a' = c
  · subst ha'
    simp [hg]
  · rw [Kplus_col_sector hF h3 hk ha' (Or.inl rfl)]

theorem Sm_Kop (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c : F)
    {g : F → ℝ} (hg : g c = 0) : Sm c (Kop c g) = (1 / 2) * ∑ a, g a := by
  unfold Sm Kop
  have e : ∀ a : F, (if χ (a - c) = -1 then ∑ a', Kplus c a a' * g a' else 0) =
      ∑ a', (if χ (a - c) = -1 then Kplus c a a' else 0) * g a' := by
    intro a
    split_ifs <;> simp
  simp only [e]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun a' _ => ?_
  rw [← sum_mul]
  by_cases ha' : a' = c
  · subst ha'
    simp [hg]
  · rw [Kplus_col_sector hF h3 hk ha' (Or.inr rfl)]

/-- On the mean-zero functions, the sector sums of `𝒦₀ g = -g/(q - 2)`. -/
theorem Sp_K0op (c : F) {g : F → ℝ} (hg : g c = 0) (h0 : ∑ a, g a = 0) :
    Sp c (K0op c g) = -Sp c g / ((Fintype.card F : ℝ) - 2) := by
  unfold Sp
  rw [neg_div, sum_div, ← sum_neg_distrib]
  refine sum_congr rfl fun a _ => ?_
  by_cases h : χ (a - c) = 1
  · have ha : a ≠ c := ne_of_chi_eq h (Or.inl rfl)
    simp only [h, ↓reduceIte]
    rw [K0op_meanZero c hg h0 ha]
    ring
  · simp only [h, ↓reduceIte, neg_zero, zero_div]

theorem Sm_K0op (c : F) {g : F → ℝ} (hg : g c = 0) (h0 : ∑ a, g a = 0) :
    Sm c (K0op c g) = -Sm c g / ((Fintype.card F : ℝ) - 2) := by
  unfold Sm
  rw [neg_div, sum_div, ← sum_neg_distrib]
  refine sum_congr rfl fun a _ => ?_
  by_cases h : χ (a - c) = -1
  · have ha : a ≠ c := ne_of_chi_eq h (Or.inr rfl)
    simp only [h, ↓reduceIte]
    rw [K0op_meanZero c hg h0 ha]
    ring
  · simp only [h, ↓reduceIte, neg_zero, zero_div]

/-- **`Δ` maps `𝒵_c` into `𝒵_c`** (sector sums). -/
theorem Sp_Dop (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c : F)
    {g : F → ℝ} (hg : g c = 0) (hp : Sp c g = 0) (hm : Sm c g = 0) : Sp c (Dop c g) = 0 := by
  have h0 : ∑ a, g a = 0 := by rw [sum_eq_Sp_add_Sm c hg, hp, hm, add_zero]
  unfold Dop
  rw [Sp_sub, Sp_Kop hF h3 hk c hg, Sp_K0op c hg h0, h0, hp]
  ring

theorem Sm_Dop (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c : F)
    {g : F → ℝ} (hg : g c = 0) (hp : Sp c g = 0) (hm : Sm c g = 0) : Sm c (Dop c g) = 0 := by
  have h0 : ∑ a, g a = 0 := by rw [sum_eq_Sp_add_Sm c hg, hp, hm, add_zero]
  unfold Dop
  rw [Sm_sub, Sm_Kop hF h3 hk c hg, Sm_K0op c hg h0, h0, hm]
  ring

/-! ## Linearity and the decomposition -/

theorem Kop_lin (c : F) (t : ℝ) (h g : F → ℝ) (a : F) :
    Kop c (fun x => t * h x + g x) a = t * Kop c h a + Kop c g a := by
  unfold Kop
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun a' _ => by ring

omit [Field F] in
theorem K0op_lin (c : F) (t : ℝ) (h g : F → ℝ) (a : F) :
    K0op c (fun x => t * h x + g x) a = t * K0op c h a + K0op c g a := by
  unfold K0op
  by_cases ha : a = c
  · simp only [ha, ↓reduceIte, mul_zero, add_zero]
  · simp only [ha, ↓reduceIte]
    have : ∀ a' : F, (if a' = c ∨ a' = a then (0 : ℝ) else t * h a' + g a') =
        t * (if a' = c ∨ a' = a then 0 else h a') + (if a' = c ∨ a' = a then 0 else g a') := by
      intro a'
      split_ifs <;> ring
    simp only [this, sum_add_distrib, ← mul_sum]
    ring

theorem Dop_lin (c : F) (t : ℝ) (h g : F → ℝ) (a : F) :
    Dop c (fun x => t * h x + g x) a = t * Dop c h a + Dop c g a := by
  unfold Dop
  rw [Kop_lin, K0op_lin]
  ring

theorem Kop_c (c : F) (f : F → ℝ) : Kop c f c = 0 := by
  unfold Kop
  exact sum_eq_zero fun a' _ => by rw [Kplus_left_eq, zero_mul]

omit [Field F] in
theorem K0op_c (c : F) (f : F → ℝ) : K0op c f c = 0 := by
  unfold K0op
  simp

theorem Dop_c (c : F) (f : F → ℝ) : Dop c f c = 0 := by
  unfold Dop
  rw [Kop_c, K0op_c, sub_zero]

/-- `Δ 𝐡_c = 𝐡_c/(q - 2)` everywhere (both sides vanish at `c`). -/
theorem Dop_sector (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F) (c a : F) :
    Dop c (sectorContrast c) a = sectorContrast c a / ((Fintype.card F : ℝ) - 2) := by
  by_cases ha : a = c
  · subst ha
    rw [Dop_c, sectorContrast_c, zero_div]
  · exact Delta_sector hF h3 hk c a ha

/-- **`‖Δ f‖² = t² ‖𝐡_c‖²/(q - 2)² + ‖Δ g‖²`** for `f = t 𝐡_c + g`, `g ∈ 𝒵_c`. -/
theorem Dop_norm_sq_split (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c : F) (t : ℝ) {g : F → ℝ} (hg : g c = 0) (hp : Sp c g = 0) (hm : Sm c g = 0) :
    ∑ a, Dop c (fun x => t * sectorContrast c x + g x) a ^ 2 =
      (t / ((Fintype.card F : ℝ) - 2)) ^ 2 * ((Fintype.card F : ℝ) - 1) +
        ∑ a, Dop c g a ^ 2 := by
  have hcross : ∑ a, sectorContrast c a * Dop c g a = 0 := by
    rw [sum_sector_mul, Sp_Dop hF h3 hk c hg hp hm, Sm_Dop hF h3 hk c hg hp hm, sub_zero]
  have e : ∀ a, Dop c (fun x => t * sectorContrast c x + g x) a ^ 2 =
      (t / ((Fintype.card F : ℝ) - 2)) ^ 2 * sectorContrast c a ^ 2 +
        2 * t / ((Fintype.card F : ℝ) - 2) * (sectorContrast c a * Dop c g a) + Dop c g a ^ 2 := by
    intro a
    rw [Dop_lin, Dop_sector hF h3 hk]
    ring
  simp only [e, sum_add_distrib, ← mul_sum, hcross, mul_zero, add_zero, sum_sector_sq hF h3]

/-- **`‖f‖² = t² ‖𝐡_c‖² + ‖g‖²`** for `f = t 𝐡_c + g`, `g ∈ 𝒵_c`. -/
theorem norm_sq_split (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (c : F) (t : ℝ)
    {g : F → ℝ} (hp : Sp c g = 0) (hm : Sm c g = 0) :
    ∑ a, (t * sectorContrast c a + g a) ^ 2 =
      t ^ 2 * ((Fintype.card F : ℝ) - 1) + ∑ a, g a ^ 2 := by
  have hcross : ∑ a, sectorContrast c a * g a = 0 := by
    rw [sum_sector_mul, hp, hm, sub_zero]
  have e : ∀ a, (t * sectorContrast c a + g a) ^ 2 =
      t ^ 2 * sectorContrast c a ^ 2 + 2 * t * (sectorContrast c a * g a) + g a ^ 2 := by
    intro a
    ring
  simp only [e, sum_add_distrib, ← mul_sum, hcross, mul_zero, add_zero, sum_sector_sq hF h3]

/-! ## `Δ` on the sector-centred space -/

/-- The part of `g` on `V_c^-`. -/
noncomputable def gMinus (c : F) (g : F → ℝ) (a : F) : ℝ := if χ (a - c) = -1 then g a else 0

/-- **On `𝒵_c`, `M_c^{+-}` is half the `(V_c^+, V_c^-)` block of the Paley matrix**:
`∑_{a'} M_c^{+-}(a, a') g(a') = [a ∈ V_c^+] (𝐂 g₋)(a)/2`. -/
theorem Mpm_apply_Z (c : F) {g : F → ℝ} (hm : Sm c g = 0) (a : F) :
    ∑ a', Mpm c a a' * g a' = if χ (a - c) = 1 then Cop (gMinus c g) a / 2 else 0 := by
  by_cases ha : χ (a - c) = 1
  · simp only [ha, ↓reduceIte]
    have hpt : ∀ a', Mpm c a a' * g a' =
        ((((χ (a' - a) : ℤ) : ℝ) ^ 2 + ((χ (a' - a) : ℤ) : ℝ)) / 2) * gMinus c g a' := by
      intro a'
      rw [← two_mul_indicator_real]
      unfold Mpm gMinus
      by_cases h1 : χ (a' - c) = -1
      · by_cases h2 : χ (a' - a) = 1
        · simp only [ha, h1, h2, and_self, ↓reduceIte]
          ring
        · simp only [h2, and_false, ↓reduceIte, h1]
          ring
      · simp only [h1, false_and, and_false, ↓reduceIte, mul_zero, zero_mul]
    simp only [hpt]
    have hsq : ∀ a', (((χ (a' - a) : ℤ) : ℝ) ^ 2) * gMinus c g a' = gMinus c g a' := by
      intro a'
      unfold gMinus
      by_cases h1 : χ (a' - c) = -1
      · have hne : a' ≠ a := by
          rintro rfl
          rw [ha] at h1
          exact absurd h1 (by decide)
        have := chi_sq_eq (F := F) (a' - a)
        rw [ite_eq_right (sub_ne_zero.mpr hne)] at this
        have h' : (((χ (a' - a) : ℤ) : ℝ) ^ 2) = 1 := by exact_mod_cast this
        simp only [h1, ↓reduceIte, h', one_mul]
      · simp only [h1, ↓reduceIte, mul_zero]
    have e : ∀ a', ((((χ (a' - a) : ℤ) : ℝ) ^ 2 + ((χ (a' - a) : ℤ) : ℝ)) / 2) * gMinus c g a' =
        (gMinus c g a' + ((χ (a' - a) : ℤ) : ℝ) * gMinus c g a') / 2 := by
      intro a'
      calc ((((χ (a' - a) : ℤ) : ℝ) ^ 2 + ((χ (a' - a) : ℤ) : ℝ)) / 2) * gMinus c g a'
          = ((((χ (a' - a) : ℤ) : ℝ) ^ 2 * gMinus c g a') +
              ((χ (a' - a) : ℤ) : ℝ) * gMinus c g a') / 2 := by ring
        _ = _ := by rw [hsq a']
    simp only [e]
    rw [← sum_div, sum_add_distrib]
    have hSm : ∑ a', gMinus c g a' = 0 := hm
    rw [hSm, zero_add]
    rfl
  · simp only [ha, ↓reduceIte]
    exact sum_eq_zero fun a' _ => by simp only [Mpm, ha, false_and, ↓reduceIte, zero_mul]

/-- **`Δ g = 𝐂 g/(q - 3) - g/((q - 3)(q - 2)) - 4 [V_c^+] 𝐂 g₋/((q - 3)(q + 1))`** on `V_c`, for
`g ∈ 𝒵_c`. -/
theorem Dop_apply_Z (hk : 0 < kP F) (c : F) {g : F → ℝ} (hg : g c = 0) (hp : Sp c g = 0)
    (hm : Sm c g = 0) {a : F} (ha : a ≠ c) :
    Dop c g a = Cop g a / ((Fintype.card F : ℝ) - 3) -
      g a / (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2)) -
      4 / (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) + 1)) *
        (if χ (a - c) = 1 then Cop (gMinus c g) a else 0) := by
  have h0 : ∑ a, g a = 0 := by rw [sum_eq_Sp_add_Sm c hg, hp, hm, add_zero]
  have hq : (Fintype.card F : ℝ) = 4 * kP F + 3 := by
    unfold kP
    ring
  have hK : Kop c g a = (∑ a', Mrel c a a' * g a') / (2 * kP F) -
      (∑ a', Mpm c a a' * g a') / (2 * kP F * (kP F + 1)) := by
    unfold Kop Kplus
    rw [sum_div, sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun a' _ => by ring
  unfold Dop
  rw [hK, Mrel_apply c hg h0 ha, Mpm_apply_Z c hm a, K0op_meanZero c hg h0 ha]
  have hq3 : (Fintype.card F : ℝ) - 3 ≠ 0 := by rw [hq]; linarith
  have hq2 : (Fintype.card F : ℝ) - 2 ≠ 0 := by rw [hq]; linarith
  have hq1 : (Fintype.card F : ℝ) + 1 ≠ 0 := by rw [hq]; linarith
  have e3 : 2 * kP F * (kP F + 1) =
      ((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) + 1) / 8 := by
    unfold kP
    ring
  have e2 : 2 * kP F = ((Fintype.card F : ℝ) - 3) / 2 := by
    unfold kP
    ring
  rw [e3, e2]
  split_ifs
  · field_simp
    ring
  · field_simp
    ring

/-- **`‖Δ g‖ ≤ κ_Δ ‖g‖` on `𝒵_c`.** -/
theorem Dop_Z_norm_sq_le (hF : ringChar F ≠ 2) (hk : 0 < kP F) (c : F) {g : F → ℝ}
    (hg : g c = 0) (hp : Sp c g = 0) (hm : Sm c g = 0) :
    ∑ a, Dop c g a ^ 2 ≤ kappaDelta (Fintype.card F : ℝ) ^ 2 * ∑ a, g a ^ 2 := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have h0 : ∑ a, g a = 0 := by rw [sum_eq_Sp_add_Sm c hg, hp, hm, add_zero]
  have hkq : q = 4 * kP F + 3 := by
    rw [hqdef]
    unfold kP
    ring
  have hq3 : 0 < q - 3 := by linarith
  have hq2 : 0 < q - 2 := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have hq0 : 0 ≤ q := by linarith
  set N : ℝ := Real.sqrt (∑ a, g a ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hNsq : N ^ 2 = ∑ a, g a ^ 2 := Real.sq_sqrt (sum_nonneg fun a _ => sq_nonneg _)
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  set u : F → ℝ := fun a => Cop g a / (q - 3) with hu
  set v : F → ℝ := fun a => -(g a / ((q - 3) * (q - 2))) with hv
  set w : F → ℝ := fun a => -(4 / ((q - 3) * (q + 1)) *
    (if χ (a - c) = 1 then Cop (gMinus c g) a else 0)) with hw
  have hpt : ∀ a, Dop c g a ^ 2 ≤ (u a + v a + w a) ^ 2 := by
    intro a
    by_cases ha : a = c
    · subst ha
      rw [Dop_c, zero_pow two_ne_zero]
      exact sq_nonneg _
    · rw [Dop_apply_Z hk c hg hp hm ha]
      simp only [hu, hv, hw]
      apply le_of_eq
      ring
  have hu2 : ∑ a, u a ^ 2 ≤ (Real.sqrt q / (q - 3) * N) ^ 2 := by
    have h := sum_Cop_sq hF g
    rw [h0] at h
    have : ∑ a, u a ^ 2 = (∑ a, Cop g a ^ 2) / (q - 3) ^ 2 := by
      simp only [hu, div_pow]
      rw [sum_div]
    rw [this, h, mul_pow, div_pow, hsq, hNsq]
    apply le_of_eq
    ring
  have hv2 : ∑ a, v a ^ 2 ≤ (1 / ((q - 3) * (q - 2)) * N) ^ 2 := by
    have : ∑ a, v a ^ 2 = (∑ a, g a ^ 2) / ((q - 3) * (q - 2)) ^ 2 := by
      simp only [hv, neg_sq, div_pow]
      rw [sum_div]
    rw [this]
    apply le_of_eq
    rw [← hNsq]
    have hne : (q - 3) * (q - 2) ≠ 0 := by positivity
    field_simp
  have hw2 : ∑ a, w a ^ 2 ≤ (4 * Real.sqrt q / ((q - 3) * (q + 1)) * N) ^ 2 := by
    have hgm : ∑ a, gMinus c g a ^ 2 ≤ ∑ a, g a ^ 2 := by
      refine sum_le_sum fun a _ => ?_
      unfold gMinus
      split_ifs
      · exact le_rfl
      · rw [zero_pow two_ne_zero]
        exact sq_nonneg _
    have hC := sum_Cop_sq hF (gMinus c g)
    have hCle : ∑ a, Cop (gMinus c g) a ^ 2 ≤ q * ∑ a, g a ^ 2 := by
      rw [hC]
      nlinarith [sq_nonneg (∑ a, gMinus c g a)]
    have hpt' : ∀ a, w a ^ 2 ≤ (4 / ((q - 3) * (q + 1))) ^ 2 * Cop (gMinus c g) a ^ 2 := by
      intro a
      simp only [hw, neg_sq, mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      split_ifs
      · exact le_rfl
      · rw [zero_pow two_ne_zero]
        exact sq_nonneg _
    calc ∑ a, w a ^ 2 ≤ ∑ a, (4 / ((q - 3) * (q + 1))) ^ 2 * Cop (gMinus c g) a ^ 2 :=
          sum_le_sum fun a _ => hpt' a
      _ = (4 / ((q - 3) * (q + 1))) ^ 2 * ∑ a, Cop (gMinus c g) a ^ 2 := by rw [mul_sum]
      _ ≤ (4 / ((q - 3) * (q + 1))) ^ 2 * (q * ∑ a, g a ^ 2) :=
          mul_le_mul_of_nonneg_left hCle (sq_nonneg _)
      _ = (4 * Real.sqrt q / ((q - 3) * (q + 1)) * N) ^ 2 := by
          rw [← hNsq]
          simp only [div_pow, mul_pow, hsq]
          ring
  have hA : 0 ≤ Real.sqrt q / (q - 3) * N := by positivity
  have hB : 0 ≤ 1 / ((q - 3) * (q - 2)) * N := by positivity
  have hC' : 0 ≤ 4 * Real.sqrt q / ((q - 3) * (q + 1)) * N := by positivity
  have huv := sum_sq_add_le hA hB hu2 hv2
  have huvw := sum_sq_add_le (add_nonneg hA hB) hC' huv hw2
  calc ∑ a, Dop c g a ^ 2 ≤ ∑ a, (u a + v a + w a) ^ 2 := sum_le_sum fun a _ => hpt a
    _ ≤ (Real.sqrt q / (q - 3) * N + 1 / ((q - 3) * (q - 2)) * N +
          4 * Real.sqrt q / ((q - 3) * (q + 1)) * N) ^ 2 := huvw
    _ = kappaDelta q ^ 2 * ∑ a, g a ^ 2 := by
        rw [← hNsq]
        unfold kappaDelta
        ring

/-- `κ_Δ ≥ 1/(q - 2)` for `q ≥ 7`. -/
theorem kappaDelta_ge {q : ℝ} (hq : 7 ≤ q) : 1 / (q - 2) ≤ kappaDelta q := by
  have hq3 : 0 < q - 3 := by linarith
  have hq2 : 0 < q - 2 := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have hs : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  unfold kappaDelta
  have h1 : 1 / (q - 2) ≤ Real.sqrt q / (q - 3) := by
    rw [div_le_div_iff₀ hq2 hq3]
    nlinarith
  have h2 : 0 ≤ 1 / ((q - 3) * (q - 2)) := by positivity
  have h3 : 0 ≤ 4 * Real.sqrt q / ((q - 3) * (q + 1)) := by positivity
  linarith

/-- **`lem:record:one-stage-folded-e`(c): `‖Δ f‖ ≤ k_new(p) r ‖f‖` on the mean-zero functions of
`V_c`**, with `κ_Δ = k_new(p) r` (`kappaDelta_eq_knew`). -/
theorem Dop_norm_sq_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c : F) {f : F → ℝ} (hf : f c = 0) (h0 : ∑ a, f a = 0) :
    ∑ a, Dop c f a ^ 2 ≤ kappaDelta (Fintype.card F : ℝ) ^ 2 * ∑ a, f a ^ 2 := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hkq : q = 4 * kP F + 3 := by
    rw [hqdef]
    unfold kP
    ring
  have hq7 : 7 ≤ q := by
    have h3' : 3 < Fintype.card F := by
      have : (3 : ℝ) < Fintype.card F := by
        unfold kP at hk
        linarith
      exact_mod_cast this
    have : 7 ≤ Fintype.card F := by omega
    rw [hqdef]
    exact_mod_cast this
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
  have hsplit := Dop_norm_sq_split hF h3 hk c t hgc hgp hgm
  have hnorm := norm_sq_split hF h3 c t hgp hgm
  have hZ := Dop_Z_norm_sq_le hF hk c hgc hgp hgm
  have hκ := kappaDelta_ge hq7
  have hκ2 : (1 / (q - 2)) ^ 2 ≤ kappaDelta q ^ 2 := by
    have : 0 ≤ 1 / (q - 2) := by positivity
    exact pow_le_pow_left₀ this hκ 2
  have hfg' : ∑ a, f a ^ 2 = t ^ 2 * (q - 1) + ∑ a, g a ^ 2 := by
    rw [hfg]
    exact hnorm
  have hlhs : ∑ a, Dop c f a ^ 2 = (t / (q - 2)) ^ 2 * (q - 1) + ∑ a, Dop c g a ^ 2 := by
    rw [hfg]
    exact hsplit
  rw [hlhs, hfg']
  have ht : 0 ≤ t ^ 2 * (q - 1) := mul_nonneg (sq_nonneg _) hq1.le
  have h1 : (t / (q - 2)) ^ 2 * (q - 1) ≤ kappaDelta q ^ 2 * (t ^ 2 * (q - 1)) := by
    have e : (t / (q - 2)) ^ 2 * (q - 1) = (1 / (q - 2)) ^ 2 * (t ^ 2 * (q - 1)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hκ2 ht
  nlinarith [h1, hZ]

end Sarkozy.PartVRecords
