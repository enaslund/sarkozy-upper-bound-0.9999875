module

public import Sarkozy.SignedDecomp.Comp
public import Sarkozy.CompSharp.Numeric

@[expose] public section

/-!
# The centred norm of a repaired fold component at `34 r + 1000 q` (C38)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), Step 1 ("every centred component
`Π_⊥ T[P_{uv,p}] Π_⊥` has norm at most `c_+ r`").

SD2's separable Paley + Schur argument (`Sarkozy.SignedDecomp.comp_form`, `comp_centred`), with
its numerical step abstracted (`CompNumeric`):
* **`comp_form_of`**, **`comp_centred_of`**: the form bound and the centred norm at any `δ(√p)`
  with `CompNumeric δ`;
* **`comp_centred34`**: centred norm `≤ 34 r + 1000 q`;
* **`comp_centred35`**, **`comp_centred38`**: `≤ 35 r`, `≤ 38 r`.

Here `r = p^{-1/2}`, `q = 1/p`, `p ≥ 2²⁴`, for B8's repaired component with **any** repair
constant `M ≥ 0` satisfying the defect bound.
-/

open Finset Matrix

namespace Sarkozy.CompSharp

open Sarkozy.SignedComponents Sarkozy.PrimeGram Sarkozy.Labellings Sarkozy.SignedDecomp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "qF" => (Fintype.card F : ℝ)

section Prime

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)
  (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)

include hR h3 h19 in
/-- **The form of a repaired component on the `m₀`-centred functions, at any constant the
numerical step gives** (`prop:signed-bounds`(c), Step 1): if `CompNumeric δ`, then
`|⟨g, T_P f⟩_{m₀}| ≤ δ(√p) ‖g‖_{m₀} ‖f‖_{m₀}` at `p ≥ 2²⁴`, for any repair constant `M ≥ 0` with
the defect bound. This is SD2's `comp_form` (proof copied verbatim) with its last step, SD2's
`comp_numeric` at `80`, replaced by the hypothesis `CompNumeric δ`. -/
theorem comp_form_of {δ : ℝ → ℝ} (hδ : CompNumeric δ) (hp : (2 : ℝ) ^ 24 ≤ qF) (c : Fin 3)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : (repairInput hR h3 h19 hF ht0 ht1 c).DefectBound M)
    (g f : (Fin 3 → F) → ℝ) (hg : (m0 hF).weight ⬝ᵥ g = 0) (hf : (m0 hF).weight ⬝ᵥ f = 0) :
    |∑ x, ∑ y, g x * (repairInput hR h3 h19 hF ht0 ht1 c).repair M (x, y) * f y| ≤
      δ (√qF) * (√(mip (m0 hF).weight g g) * √(mip (m0 hF).weight f f)) := by
  set R := repairInput hR h3 h19 hF ht0 ht1 c with hRdef
  set m := (m0 hF).weight with hmdef
  set H := Hcard (F := F) with hHdef
  set e := Sarkozy.SignedEstimates.e0 qF with hedef
  set s := √qF with hsdef
  have hq0 : 0 < qF := lt_of_lt_of_le (by positivity) hp
  have hs2 : s ^ 2 = qF := Real.sq_sqrt hq0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hq0
  have hs : 4096 ≤ s := by
    have : √((2 : ℝ) ^ 24) = 4096 := by
      rw [show (2 : ℝ) ^ 24 = 4096 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← this]; exact Real.sqrt_le_sqrt hp
  have hH : H = s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2 := by
    rw [hs2]; exact Sarkozy.SignedEstimates.Hcard_eq hR
  have hH0 : 0 < H := Hcard_pos hR h19
  have he0 : 0 ≤ e := e0_nonneg h19
  have he1 : e < 1 := e0_lt_one h19
  have he3 : e ≤ 3 / s ^ 2 := by
    rw [hs2, hedef, Sarkozy.SignedEstimates.e0]
    have h4 : 0 < qF - 4 := by linarith
    have h3' : 0 < qF - 3 := by linarith
    rw [div_le_div_iff₀ (by positivity) hq0]
    nlinarith
  -- the indicator of `H_F`
  set I : (Fin 3 → F) → ℝ := hfI with hIdef
  have hI : ∀ x, I x = 0 ∨ I x = 1 := by
    intro x; simp only [I, hfI]; split_ifs <;> simp
  have hIsum : ∑ x, I x = H := by
    simp only [I, hfI, hHdef, Hcard, Hset]
    rw [sum_boole]
  have hoff : ∀ x, I x = 0 → m x = 0 := by
    intro x h
    apply m_zero_off
    intro hx
    simp [I, hfI, hx] at h
  have hon : ∀ x, I x = 1 → |m x * H - 1| ≤ e := by
    intro x h
    have hx : HF x := by
      by_contra hx
      simp [I, hfI, hx] at h
    exact Sarkozy.SignedEstimates.g0_bound hR h3 h19 hF hx
  have hm0 : ∀ x, 0 ≤ m x := (m0 hF).nonneg
  have hgc : ∑ x, m x * g x = 0 := hg
  have hfc : ∑ x, m x * f x = 0 := hf
  set Ng := √(mip m g g)
  set Nf := √(mip m f f)
  have hmipg : 0 ≤ mip m g g := sum_nonneg fun x _ => by
    rw [mul_assoc]; exact mul_nonneg (hm0 x) (mul_self_nonneg _)
  have hmipf : 0 ≤ mip m f f := sum_nonneg fun x _ => by
    rw [mul_assoc]; exact mul_nonneg (hm0 x) (mul_self_nonneg _)
  -- the parameters `u, v`
  set u : ℝ := (compU c : ℝ)
  set v : ℝ := (compV c : ℝ)
  have hu : |u| ≤ 1 := by rcases compU_cases c with h | h <;> simp [u, h]
  have hv : |v| ≤ 1 := by rcases compV_cases c with h | h <;> simp [v, h]
  have hW : ∀ x y, R.W (x, y) = I x * Vk t u v x y * I y := by
    intro x y
    change Ukernel t u v (x, y) = _
    rw [Ukernel_eq]
    simp only [I, hfI]
    by_cases hx : HF x <;> by_cases hy : HF y <;> simp [hx, hy]
  -- `T`
  set T := (15 * s + 8) * qF ^ 2
  have hT0 : 0 ≤ T := by positivity
  -- the mass `Z`
  have hZ : H ^ 2 - T * H ≤ R.Z := by
    have hV := Vk_form hR h3 ht0 ht1 hu hv I I
    have e1 : R.Z = ∑ x, ∑ y, I x * Vk t u v x y * I y := by
      change ∑ p, R.W p = _
      rw [Fintype.sum_prod_type]
      exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => hW x y
    have hII : nrm I * nrm I = H := by
      rw [← Real.sqrt_mul (sum_nonneg fun x _ => sq_nonneg _), Real.sqrt_mul_self
        (sum_nonneg fun x _ => sq_nonneg _)]
      rw [← hIsum]
      exact sum_congr rfl fun x _ => by rcases hI x with h | h <;> rw [h] <;> norm_num
    rw [hIsum, hII] at hV
    rw [e1]
    have := (abs_le.mp hV).1
    nlinarith
  have hZ0 : 0 < R.Z := R.W_pos
  -- the `W/Z` part
  set gt : (Fin 3 → F) → ℝ := fun x => I x * g x
  set ft : (Fin 3 → F) → ℝ := fun y => I y * f y
  have hWpart : |∑ x, ∑ y, g x * (R.W (x, y) / R.Z) * f y| ≤
      (e ^ 2 * H + T) * (H / (1 - e)) / R.Z * (Ng * Nf) := by
    have e1 : ∑ x, ∑ y, g x * (R.W (x, y) / R.Z) * f y =
        (∑ x, ∑ y, gt x * Vk t u v x y * ft y) / R.Z := by
      rw [sum_div]
      refine sum_congr rfl fun x _ => ?_
      rw [sum_div]
      refine sum_congr rfl fun y _ => ?_
      rw [hW]; simp only [gt, ft]; ring
    have hV := Vk_form hR h3 ht0 ht1 hu hv gt ft
    have hcg := sum_ind_centred I m hI hIsum hoff hon he0 g hgc
    have hcf := sum_ind_centred I m hI hIsum hoff hon he0 f hfc
    have hng : nrm gt ≤ √(H / (1 - e)) * Ng :=
      sqrt_mul_le_of (div_nonneg hH0.le (by linarith))
        (sum_ind_sq_le I m hI hm0 hH0 he1 hon g)
    have hnf : nrm ft ≤ √(H / (1 - e)) * Nf :=
      sqrt_mul_le_of (div_nonneg hH0.le (by linarith))
        (sum_ind_sq_le I m hI hm0 hH0 he1 hon f)
    have hgt0 : 0 ≤ nrm gt := Real.sqrt_nonneg _
    have hft0 : 0 ≤ nrm ft := Real.sqrt_nonneg _
    have hsum : |∑ x, ∑ y, gt x * Vk t u v x y * ft y| ≤ (e ^ 2 * H + T) * (nrm gt * nrm ft) := by
      have h1 : |(∑ x, gt x) * ∑ y, ft y| ≤ e ^ 2 * H * (nrm gt * nrm ft) := by
        rw [abs_mul]
        have := mul_le_mul hcg hcf (abs_nonneg _) (by positivity)
        have hHs : √H * √H = H := Real.mul_self_sqrt hH0.le
        calc |∑ x, gt x| * |∑ y, ft y| ≤ e * √H * nrm gt * (e * √H * nrm ft) := this
          _ = e ^ 2 * (√H * √H) * (nrm gt * nrm ft) := by ring
          _ = _ := by rw [hHs]
      have := abs_sub_abs_le_abs_sub (∑ x, ∑ y, gt x * Vk t u v x y * ft y)
        ((∑ x, gt x) * ∑ y, ft y)
      have h2 := hV
      have e2 : (e ^ 2 * H + T) * (nrm gt * nrm ft) =
          e ^ 2 * H * (nrm gt * nrm ft) + T * (nrm gt * nrm ft) := by ring
      rw [e2]
      linarith
    have hHe : √(H / (1 - e)) * √(H / (1 - e)) = H / (1 - e) :=
      Real.mul_self_sqrt (div_nonneg hH0.le (by linarith))
    rw [e1, abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
    have hprod : nrm gt * nrm ft ≤ H / (1 - e) * (Ng * Nf) := by
      have := mul_le_mul hng hnf hft0 (by positivity)
      calc nrm gt * nrm ft ≤ √(H / (1 - e)) * Ng * (√(H / (1 - e)) * Nf) := this
        _ = (√(H / (1 - e)) * √(H / (1 - e))) * (Ng * Nf) := by ring
        _ = _ := by rw [hHe]
    have hc0 : 0 ≤ e ^ 2 * H + T := by positivity
    calc |∑ x, ∑ y, gt x * Vk t u v x y * ft y| ≤ (e ^ 2 * H + T) * (nrm gt * nrm ft) := hsum
      _ ≤ (e ^ 2 * H + T) * (H / (1 - e) * (Ng * Nf)) := mul_le_mul_of_nonneg_left hprod hc0
      _ = (e ^ 2 * H + T) * (H / (1 - e)) / R.Z * (Ng * Nf) * R.Z := by
          field_simp
  -- the `J` part
  set k := qF / (qF - 1) * ((√qF + 1) * qF ^ 2) with hkdef
  have hq1 : (0 : ℝ) < qF - 1 := by linarith
  have hk0 : 0 ≤ k := by positivity
  set gm : (Fin 3 → F) → ℝ := fun x => g x * m x
  set fm : (Fin 3 → F) → ℝ := fun y => f y * m y
  have hHe' : 0 ≤ (1 + e) / H := by positivity
  have hngm : nrm gm ≤ √((1 + e) / H) * Ng :=
    sqrt_mul_le_of hHe' (sum_mul_sq_le I m hI hm0 hH0 hoff hon he0 g)
  have hnfm : nrm fm ≤ √((1 + e) / H) * Nf :=
    sqrt_mul_le_of hHe' (sum_mul_sq_le I m hI hm0 hH0 hoff hon he0 f)
  have hα : ∀ x, m x ≠ 0 → |R.α x| ≤ M := fun x hx =>
    (hM x (lt_of_le_of_ne (hm0 x) (Ne.symm hx))).1
  have hβ : ∀ y, m y ≠ 0 → |R.β y| ≤ M := fun y hy =>
    (hM y (lt_of_le_of_ne (hm0 y) (Ne.symm hy))).2
  set G1 : (Fin 3 → F) → ℝ := fun x => g x * m x * (R.α x + 2 * M)
  set F2 : (Fin 3 → F) → ℝ := fun y => f y * m y * R.β y
  have hJsplit : ∑ x, ∑ y, g x * (R.J (x, y) * (R.α x + R.β y + 2 * M) * R.m.weight x *
      R.m.weight y) * f y = ∑ x, ∑ y, G1 x * Jker (x, y) * fm y +
        ∑ x, ∑ y, gm x * Jker (x, y) * F2 y := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    change g x * (Jker (x, y) * (R.α x + R.β y + 2 * M) * m x * m y) * f y = _
    simp only [G1, fm, gm, F2]
    ring
  have hJ1 := Jker_form hR h3 G1 fm
  have hJ2 := Jker_form hR h3 gm F2
  have hsf : ∑ y, fm y = 0 := by rw [← hfc]; exact sum_congr rfl fun y _ => by simp only [fm]; ring
  have hsg : ∑ x, gm x = 0 := by rw [← hgc]; exact sum_congr rfl fun x _ => by simp only [gm]; ring
  rw [hsf, mul_zero, mul_zero, sub_zero] at hJ1
  rw [hsg, zero_mul, mul_zero, sub_zero] at hJ2
  have hG1 : nrm G1 ≤ 3 * M * nrm gm := by
    have : ∑ x, G1 x ^ 2 ≤ (3 * M) ^ 2 * ∑ x, gm x ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun x _ => ?_
      simp only [G1, gm]
      by_cases hx : m x = 0
      · rw [hx]; simp
      · have h := abs_le.mp (hα x hx)
        have hb : (R.α x + 2 * M) ^ 2 ≤ (3 * M) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        calc (g x * m x * (R.α x + 2 * M)) ^ 2 = (g x * m x) ^ 2 * (R.α x + 2 * M) ^ 2 := by ring
          _ ≤ (g x * m x) ^ 2 * (3 * M) ^ 2 := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
          _ = (3 * M) ^ 2 * (g x * m x) ^ 2 := by ring
    calc nrm G1 ≤ √((3 * M) ^ 2) * nrm gm := sqrt_mul_le_of (sq_nonneg _) this
      _ = 3 * M * nrm gm := by rw [Real.sqrt_sq (by positivity)]
  have hF2 : nrm F2 ≤ M * nrm fm := by
    have : ∑ y, F2 y ^ 2 ≤ M ^ 2 * ∑ y, fm y ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun y _ => ?_
      simp only [F2, fm]
      by_cases hy : m y = 0
      · rw [hy]; simp
      · have hb : R.β y ^ 2 ≤ M ^ 2 := by
          have h := hβ y hy
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
        calc (f y * m y * R.β y) ^ 2 = (f y * m y) ^ 2 * R.β y ^ 2 := by ring
          _ ≤ (f y * m y) ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
          _ = M ^ 2 * (f y * m y) ^ 2 := by ring
    calc nrm F2 ≤ √(M ^ 2) * nrm fm := sqrt_mul_le_of (sq_nonneg _) this
      _ = M * nrm fm := by rw [Real.sqrt_sq hM0]
  have hgm0 : 0 ≤ nrm gm := Real.sqrt_nonneg _
  have hfm0 : 0 ≤ nrm fm := Real.sqrt_nonneg _
  have hHe2 : √((1 + e) / H) * √((1 + e) / H) = (1 + e) / H := Real.mul_self_sqrt hHe'
  have hpm : nrm gm * nrm fm ≤ (1 + e) / H * (Ng * Nf) := by
    have := mul_le_mul hngm hnfm hfm0 (by positivity)
    calc nrm gm * nrm fm ≤ √((1 + e) / H) * Ng * (√((1 + e) / H) * Nf) := this
      _ = (√((1 + e) / H) * √((1 + e) / H)) * (Ng * Nf) := by ring
      _ = _ := by rw [hHe2]
  have hJpart : |∑ x, ∑ y, g x * (R.J (x, y) * (R.α x + R.β y + 2 * M) * R.m.weight x *
      R.m.weight y) * f y| ≤ 4 * M * (k * ((1 + e) / H)) * (Ng * Nf) := by
    rw [hJsplit]
    refine (abs_add_le _ _).trans ?_
    have h1 : k * (nrm G1 * nrm fm) ≤ k * (3 * M * nrm gm * nrm fm) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hG1 hfm0) hk0
    have h2 : k * (nrm gm * nrm F2) ≤ k * (nrm gm * (M * nrm fm)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF2 hgm0) hk0
    have h3' : k * (4 * M * (nrm gm * nrm fm)) ≤ k * (4 * M * ((1 + e) / H * (Ng * Nf))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpm (by positivity)) hk0
    calc |∑ x, ∑ y, G1 x * Jker (x, y) * fm y| + |∑ x, ∑ y, gm x * Jker (x, y) * F2 y|
        ≤ k * (nrm G1 * nrm fm) + k * (nrm gm * nrm F2) := add_le_add hJ1 hJ2
      _ ≤ k * (3 * M * nrm gm * nrm fm) + k * (nrm gm * (M * nrm fm)) := add_le_add h1 h2
      _ = k * (4 * M * (nrm gm * nrm fm)) := by ring
      _ ≤ k * (4 * M * ((1 + e) / H * (Ng * Nf))) := h3'
      _ = _ := by ring
  -- assembly
  have hrep : ∑ x, ∑ y, g x * R.repair M (x, y) * f y =
      (∑ x, ∑ y, g x * (R.W (x, y) / R.Z) * f y + ∑ x, ∑ y, g x * (R.J (x, y) *
        (R.α x + R.β y + 2 * M) * R.m.weight x * R.m.weight y) * f y) / (1 + 2 * M) := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun y _ => ?_
    unfold RepairInput.repair
    ring
  have hM1 : 0 < 1 + 2 * M := by linarith
  have hN0 : 0 ≤ Ng * Nf := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hX2 : 0 ≤ k * ((1 + e) / H) := by positivity
  have htot : |∑ x, ∑ y, g x * R.repair M (x, y) * f y| ≤
      ((e ^ 2 * H + T) * (H / (1 - e)) / R.Z + 2 * (k * ((1 + e) / H))) * (Ng * Nf) := by
    rw [hrep, abs_div, abs_of_pos hM1, div_le_iff₀ hM1]
    refine (abs_add_le _ _).trans ?_
    have hX1 : 0 ≤ (e ^ 2 * H + T) * (H / (1 - e)) / R.Z := by
      have : 0 < 1 - e := by linarith
      positivity
    have hA := hWpart
    have hB := hJpart
    set X1 := (e ^ 2 * H + T) * (H / (1 - e)) / R.Z
    set X2 := k * ((1 + e) / H)
    have p1 : 0 ≤ 2 * M * (X1 * (Ng * Nf)) :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (mul_nonneg hX1 hN0)
    have p2 : 0 ≤ 2 * X2 * (Ng * Nf) := mul_nonneg (mul_nonneg (by norm_num) hX2) hN0
    calc |∑ x, ∑ y, g x * (R.W (x, y) / R.Z) * f y| + |∑ x, ∑ y, g x * (R.J (x, y) *
          (R.α x + R.β y + 2 * M) * R.m.weight x * R.m.weight y) * f y|
        ≤ X1 * (Ng * Nf) + 4 * M * X2 * (Ng * Nf) := add_le_add hA hB
      _ ≤ (X1 + 2 * X2) * (Ng * Nf) * (1 + 2 * M) := by
          have e3 : (X1 + 2 * X2) * (Ng * Nf) * (1 + 2 * M) = X1 * (Ng * Nf) +
              4 * M * X2 * (Ng * Nf) + (2 * M * (X1 * (Ng * Nf)) + 2 * X2 * (Ng * Nf)) := by ring
          rw [e3]
          linarith
  -- the numbers
  have hZs : (s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2) ^ 2 -
      (15 * s + 8) * (s ^ 2) ^ 2 * (s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2) ≤ R.Z := by
    rw [← hH, hs2]; exact hZ
  have hnum := hδ s e R.Z hs he0 he3 hZs
  rw [← hH, hs2] at hnum
  refine htot.trans (mul_le_mul_of_nonneg_right ?_ hN0)
  have ek : 2 * (k * ((1 + e) / H)) = 2 * (qF / (qF - 1) * ((s + 1) * qF ^ 2)) * (1 + e) / H := by
    simp only [hkdef]; ring
  rw [ek]
  exact hnum

include hR h3 h19 in
/-- **`prop:signed-bounds`(c), Step 1, at any constant of the numerical step**: at a prime
`p ≥ 2²⁴` the repaired component `P_{uv}` (any repair constant `M ≥ 0` with the defect bound) has
centred norm at most `δ(√p)` on `L²(m₀)`, if `CompNumeric δ`. -/
theorem comp_centred_of {δ : ℝ → ℝ} (hδ : CompNumeric δ) (hp : (2 : ℝ) ^ 24 ≤ qF) (c : Fin 3)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : (repairInput hR h3 h19 hF ht0 ht1 c).DefectBound M) :
    Sarkozy.SignedGram.CentredNorm (m0 hF).weight
      (fun a b => (repairInput hR h3 h19 hF ht0 ht1 c).repair M (a, b)) (δ (√qF)) := by
  set R := repairInput hR h3 h19 hF ht0 ht1 c
  refine centredNorm_of_form (m0 hF).nonneg (fun a b => R.repair_nonneg hM0 hM (a, b))
    (fun a => R.repair_row hM0 (fun x => repair_Jβ x) a)
    (fun b => R.repair_col hM0 (fun y => repair_Jα y) b) fun g f hg hf => ?_
  exact comp_form_of hR h3 h19 hF ht0 ht1 hδ hp c hM0 hM g f hg hf

include hR h3 h19 in
/-- **`prop:signed-bounds`(c), Step 1, with leading constant `34`**: at a prime `p ≥ 2²⁴` the
repaired component `P_{uv}` (any repair constant `M ≥ 0` with the defect bound) has centred norm
at most `34 r + 1000 q` on `L²(m₀)`, `r = p^{-1/2}`, `q = 1/p`. The paper's sharper `c_+ < 1.74`
(frame argument) is not formalized here. -/
theorem comp_centred34 (hp : (2 : ℝ) ^ 24 ≤ qF) (c : Fin 3) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : (repairInput hR h3 h19 hF ht0 ht1 c).DefectBound M) :
    Sarkozy.SignedGram.CentredNorm (m0 hF).weight
      (fun a b => (repairInput hR h3 h19 hF ht0 ht1 c).repair M (a, b))
      (34 * (√qF)⁻¹ + 1000 * qF⁻¹) := by
  have h := comp_centred_of hR h3 h19 hF ht0 ht1 compNumeric_34 hp c hM0 hM
  have hq : (0 : ℝ) ≤ qF := Nat.cast_nonneg _
  have e : 34 / √qF + 1000 / √qF ^ 2 = 34 * (√qF)⁻¹ + 1000 * qF⁻¹ := by
    rw [Real.sq_sqrt hq, div_eq_mul_inv, div_eq_mul_inv]
  rw [← e]
  exact h

include hR h3 h19 in
/-- **`prop:signed-bounds`(c), Step 1, with the constant `38`** (SD2's computed constant): the
centred norm of `P_{uv}` is at most `38 r` at `p ≥ 2²⁴`. -/
theorem comp_centred38 (hp : (2 : ℝ) ^ 24 ≤ qF) (c : Fin 3) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : (repairInput hR h3 h19 hF ht0 ht1 c).DefectBound M) :
    Sarkozy.SignedGram.CentredNorm (m0 hF).weight
      (fun a b => (repairInput hR h3 h19 hF ht0 ht1 c).repair M (a, b)) (38 * (√qF)⁻¹) := by
  have h := comp_centred_of hR h3 h19 hF ht0 ht1 compNumeric_38 hp c hM0 hM
  rwa [div_eq_mul_inv] at h

include hR h3 h19 in
/-- **`prop:signed-bounds`(c), Step 1, with the constant `35`**: the centred norm of `P_{uv}` is
at most `35 r` at `p ≥ 2²⁴`. -/
theorem comp_centred35 (hp : (2 : ℝ) ^ 24 ≤ qF) (c : Fin 3) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : (repairInput hR h3 h19 hF ht0 ht1 c).DefectBound M) :
    Sarkozy.SignedGram.CentredNorm (m0 hF).weight
      (fun a b => (repairInput hR h3 h19 hF ht0 ht1 c).repair M (a, b)) (35 * (√qF)⁻¹) := by
  have h := comp_centred_of hR h3 h19 hF ht0 ht1 compNumeric_35 hp c hM0 hM
  rwa [div_eq_mul_inv] at h

end Prime

end Sarkozy.CompSharp
