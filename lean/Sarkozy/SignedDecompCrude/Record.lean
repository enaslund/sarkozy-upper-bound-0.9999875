module

public import Sarkozy.SignedDecompCrude.Reduce
public import Sarkozy.SignedDecomp.Comp

@[expose] public section

/-!
# (K): the normalizations and completions of the three components (ND)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), Step 1 ("Dividing by `z_{uv}`
... and the completion of `lem:signed-components`(d) ... together `E_c q`") and Step 2 ("By
(T1)–(T3) and Step 1 for the normalizations and completions of the three components, weighted by
`∑|c_{uv}| = 1 + t`").

For B8's repaired component `P = (W/Z + J_C(α ⊕ β + 2M) m₀ ⊗ m₀)/(1 + 2M)` with
`W = 1_{H_F} ⊗ 1_{H_F} V_{uv}`, `S = ∑ g̃ V f̃` (`g̃ = 1_{H_F} g`):
`⟨g, T_P f⟩ - E_{ν⊗ν}[g V f] = S (1/(Z(1 + 2M)) - 1/|H_F|²) + J/(1 + 2M)`.

* **`comp_diff`**: if `|z_{uv} - 1| ≤ η` (`z_{uv} = Z/|H_F|²`, B8's `zMean`, the estimate
  `SignedEstimates.z`) and `|α|, |β| ≤ M`, then on `m₀`-centred `g, f`
  `|⟨g, T_P f⟩ - E_{ν⊗ν}[g V f]| ≤ (δ X₁ + 4 M X₂) ‖g‖ ‖f‖`, with
  `δ = (η + 2M(1 + η))/(1 - η)`, `X₁ = (e₀²|H_F| + T)/(|H_F|(1 - e₀))`, `T = (15√p + 8)p²`
  (SD2's `Vk_form`), and `X₂ = p/(p - 1)(√p + 1)p²(1 + e₀)/|H_F|` (SD2's `Jker_form`).
  These are the pieces of SD2's `comp_form`; `X₁ ≈ 30 r`, `X₂ ≈ 2 r`, `δ ≈ η + 2M`.
* **`recordForm_of`**: for the signed record `N = ∑_c α_c P_c`, (K) `RecordForm N t κ` with
  `κ q = (1 + t)(δ X₁ + 4 M X₂)`.
-/

open Finset Matrix

namespace Sarkozy.SignedDecompCrude

open Sarkozy.SignedComponents Sarkozy.PrimeGram Sarkozy.Labellings Sarkozy.SignedDecomp
open Sarkozy.MiddleComparison (signedCoef)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

section Prime

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)
  (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)

/-- `X₁ = (e²H + T)/(H(1 - e))`, `T = (15√p + 8)p²`. -/
noncomputable def X1C (p e H : ℝ) : ℝ := (e ^ 2 * H + (15 * √p + 8) * p ^ 2) / (H * (1 - e))

/-- `X₂ = p/(p - 1)(√p + 1)p²(1 + e)/H`. -/
noncomputable def X2C (p e H : ℝ) : ℝ := p / (p - 1) * ((√p + 1) * p ^ 2) * ((1 + e) / H)

/-- `δ = (η + 2M(1 + η))/(1 - η)`. -/
noncomputable def deltaC (η M : ℝ) : ℝ := (η + 2 * M * (1 + η)) / (1 - η)

/-- `|1/(ζ(1 + 2M)) - 1| ≤ δ` for `|ζ - 1| ≤ η < 1`, `M ≥ 0`. -/
theorem fac_bound {ζ η M : ℝ} (hM0 : 0 ≤ M) (hη1 : η < 1) (hζ : |ζ - 1| ≤ η) :
    |(1 - ζ * (1 + 2 * M)) / (ζ * (1 + 2 * M))| ≤ deltaC η M := by
  unfold deltaC
  obtain ⟨hz1, hz2⟩ := abs_le.mp hζ
  have hζ0 : 0 < ζ := by linarith
  have hM1 : 0 < 1 + 2 * M := by linarith
  have hd : 0 < ζ * (1 + 2 * M) := mul_pos hζ0 hM1
  rw [abs_div, abs_of_pos hd]
  have hp1 : 2 * M * ζ ≤ 2 * M * (1 + η) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hp2 : 0 ≤ 2 * M * ζ := by positivity
  have hnum : |1 - ζ * (1 + 2 * M)| ≤ η + 2 * M * (1 + η) := by
    rw [abs_le]; constructor <;> linarith
  have hden : 1 - η ≤ ζ * (1 + 2 * M) := by linarith
  have h1η : 0 < 1 - η := by linarith
  have hη0 : 0 ≤ η := le_trans (abs_nonneg _) hζ
  calc |1 - ζ * (1 + 2 * M)| / (ζ * (1 + 2 * M)) ≤ (η + 2 * M * (1 + η)) / (ζ * (1 + 2 * M)) :=
        div_le_div_of_nonneg_right hnum hd.le
    _ ≤ (η + 2 * M * (1 + η)) / (1 - η) :=
        div_le_div_of_nonneg_left (by positivity) h1η hden

include hR h3 h19 in
/-- **One component: normalization and completion** (see the module docstring). -/
theorem comp_diff (c : Fin 3) {M η : ℝ} (hM0 : 0 ≤ M)
    (hM : (repairInput hR h3 h19 hF ht0 ht1 c).DefectBound M) (hη1 : η < 1)
    (hz : |zMean (F := F) t (compU c) (compV c) - 1| ≤ η)
    (g f : (Fin 3 → F) → ℝ) (hg : (m0 hF).weight ⬝ᵥ g = 0) (hf : (m0 hF).weight ⬝ᵥ f = 0) :
    |∑ x, ∑ y, g x * (repairInput hR h3 h19 hF ht0 ht1 c).repair M (x, y) * f y -
        E2 (Vk t (compU c : ℝ) (compV c : ℝ)) g f| ≤
      (deltaC η M * X1C qF (Sarkozy.SignedEstimates.e0 qF) (Hcard (F := F)) +
        4 * M * X2C qF (Sarkozy.SignedEstimates.e0 qF) (Hcard (F := F))) *
        (√(mip (m0 hF).weight g g) * √(mip (m0 hF).weight f f)) := by
  set R := repairInput hR h3 h19 hF ht0 ht1 c with hRdef
  set m := (m0 hF).weight with hmdef
  set H := Hcard (F := F) with hHdef
  set e := Sarkozy.SignedEstimates.e0 qF with hedef
  have h19' : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have hq0 : 0 < qF := by linarith
  have hH0 : 0 < H := Hcard_pos hR h19
  have he0 : 0 ≤ e := e0_nonneg h19
  have he1 : e < 1 := e0_lt_one h19
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
  have hN0 : 0 ≤ Ng * Nf := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
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
  set T := (15 * √qF + 8) * qF ^ 2 with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hZ0 : 0 < R.Z := R.W_pos
  -- `S`
  set gt : (Fin 3 → F) → ℝ := fun x => I x * g x
  set ft : (Fin 3 → F) → ℝ := fun y => I y * f y
  set S := ∑ x, ∑ y, gt x * Vk t u v x y * ft y with hSdef
  have hS : |S| ≤ (e ^ 2 * H + T) * (H / (1 - e)) * (Ng * Nf) := by
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
    have hsum : |S| ≤ (e ^ 2 * H + T) * (nrm gt * nrm ft) := by
      have h1 : |(∑ x, gt x) * ∑ y, ft y| ≤ e ^ 2 * H * (nrm gt * nrm ft) := by
        rw [abs_mul]
        have := mul_le_mul hcg hcf (abs_nonneg _) (by positivity)
        have hHs : √H * √H = H := Real.mul_self_sqrt hH0.le
        calc |∑ x, gt x| * |∑ y, ft y| ≤ e * √H * nrm gt * (e * √H * nrm ft) := this
          _ = e ^ 2 * (√H * √H) * (nrm gt * nrm ft) := by ring
          _ = _ := by rw [hHs]
      have := abs_sub_abs_le_abs_sub S ((∑ x, gt x) * ∑ y, ft y)
      have h2 := hV
      have e2 : (e ^ 2 * H + T) * (nrm gt * nrm ft) =
          e ^ 2 * H * (nrm gt * nrm ft) + T * (nrm gt * nrm ft) := by ring
      rw [e2]
      linarith
    have hHe : √(H / (1 - e)) * √(H / (1 - e)) = H / (1 - e) :=
      Real.mul_self_sqrt (div_nonneg hH0.le (by linarith))
    have hprod : nrm gt * nrm ft ≤ H / (1 - e) * (Ng * Nf) := by
      have := mul_le_mul hng hnf hft0 (by positivity)
      calc nrm gt * nrm ft ≤ √(H / (1 - e)) * Ng * (√(H / (1 - e)) * Nf) := this
        _ = (√(H / (1 - e)) * √(H / (1 - e))) * (Ng * Nf) := by ring
        _ = _ := by rw [hHe]
    have hc0 : 0 ≤ e ^ 2 * H + T := by positivity
    calc |S| ≤ (e ^ 2 * H + T) * (nrm gt * nrm ft) := hsum
      _ ≤ (e ^ 2 * H + T) * (H / (1 - e) * (Ng * Nf)) := mul_le_mul_of_nonneg_left hprod hc0
      _ = _ := by ring
  have hWS : ∑ x, ∑ y, g x * (R.W (x, y) / R.Z) * f y = S / R.Z := by
    rw [hSdef, sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    rw [hW]; simp only [gt, ft]; ring
  have hE2 : E2 (Vk t u v) g f = S / H ^ 2 := by
    unfold E2
    rw [hSdef, sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    simp only [gt, ft, I]
    ring
  -- the `J` part (as in SD2's `comp_form`)
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
  set J := ∑ x, ∑ y, g x * (R.J (x, y) * (R.α x + R.β y + 2 * M) * R.m.weight x *
      R.m.weight y) * f y with hJdef
  have hJpart : |J| ≤ 4 * M * (k * ((1 + e) / H)) * (Ng * Nf) := by
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
  have hrep : ∑ x, ∑ y, g x * R.repair M (x, y) * f y = (S / R.Z + J) / (1 + 2 * M) := by
    rw [← hWS, hJdef, ← sum_add_distrib, sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun y _ => ?_
    unfold RepairInput.repair
    ring
  have hM1 : 0 < 1 + 2 * M := by linarith
  -- the normalization: `ζ = Z/H²`
  have hzeta : zMean (F := F) t (compU c) (compV c) = R.Z / H ^ 2 := rfl
  set ζ := R.Z / H ^ 2 with hζdef
  rw [hzeta] at hz
  have hζ := abs_le.mp hz
  have hζ0 : 0 < ζ := by linarith
  have hH2 : 0 < H ^ 2 := by positivity
  have hZeq : R.Z = ζ * H ^ 2 := by rw [hζdef]; field_simp
  have hdiff : (S / R.Z + J) / (1 + 2 * M) - S / H ^ 2 =
      S / H ^ 2 * ((1 - ζ * (1 + 2 * M)) / (ζ * (1 + 2 * M))) + J / (1 + 2 * M) := by
    rw [hZeq]
    field_simp
    ring
  have hfac := fac_bound hM0 hη1 hz
  have hSH : |S / H ^ 2| ≤ X1C qF e H * (Ng * Nf) := by
    rw [abs_div, abs_of_pos hH2, div_le_iff₀ hH2]
    unfold X1C
    have h1e : 0 < 1 - e := by linarith
    calc |S| ≤ (e ^ 2 * H + T) * (H / (1 - e)) * (Ng * Nf) := hS
      _ = (e ^ 2 * H + (15 * √qF + 8) * qF ^ 2) / (H * (1 - e)) * (Ng * Nf) * H ^ 2 := by
          rw [hTdef]; field_simp
  have hJM : |J / (1 + 2 * M)| ≤ 4 * M * X2C qF e H * (Ng * Nf) := by
    rw [abs_div, abs_of_pos hM1, div_le_iff₀ hM1]
    unfold X2C
    have hX : 0 ≤ 4 * M * (qF / (qF - 1) * ((√qF + 1) * qF ^ 2) * ((1 + e) / H)) * (Ng * Nf) := by
      positivity
    have := hJpart
    rw [hkdef] at this
    exact this.trans (le_mul_of_one_le_right hX (by linarith))
  rw [hrep, hE2, hdiff]
  have h1e' : 0 < 1 - e := by linarith
  have hX1 : 0 ≤ X1C qF e H := by unfold X1C; positivity
  calc |S / H ^ 2 * ((1 - ζ * (1 + 2 * M)) / (ζ * (1 + 2 * M))) + J / (1 + 2 * M)|
      ≤ |S / H ^ 2| * |(1 - ζ * (1 + 2 * M)) / (ζ * (1 + 2 * M))| + |J / (1 + 2 * M)| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ X1C qF e H * (Ng * Nf) * deltaC η M + 4 * M * X2C qF e H * (Ng * Nf) :=
        add_le_add (mul_le_mul hSH hfac (abs_nonneg _) (mul_nonneg hX1 hN0)) hJM
    _ = _ := by ring

theorem deltaC_mono {η M M' : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (h : M ≤ M') :
    deltaC η M ≤ deltaC η M' := by
  unfold deltaC
  have h1η : 0 < 1 - η := by linarith
  apply div_le_div_of_nonneg_right _ h1η.le
  have : 2 * M * (1 + η) ≤ 2 * M' * (1 + η) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

omit [Field F] [DecidableEq F] in
theorem sum3_swap {γ : Type} [Fintype γ] (f : (Fin 3 → F) → (Fin 3 → F) → γ → ℝ) :
    ∑ x, ∑ y, ∑ c, f x y c = ∑ c, ∑ x, ∑ y, f x y c := by
  calc ∑ x, ∑ y, ∑ c, f x y c = ∑ x, ∑ c, ∑ y, f x y c := sum_congr rfl fun x _ => sum_comm
    _ = ∑ c, ∑ x, ∑ y, f x y c := sum_comm

include hR h3 h19 in
/-- **(K) for the signed record**: with the three components `P_c` at repair constants `M_c ≤ M̄`
satisfying the defect bound, and `|z_c - 1| ≤ η`, the signed record `N = ∑_c α_c P_c` satisfies
`RecordForm N t κ` with `κ q = (1 + t)(δ(η, M̄) X₁ + 4 M̄ X₂)`. -/
theorem recordForm_of (M : Fin 3 → ℝ) (hM0 : ∀ c, 0 ≤ M c)
    (hM : ∀ c, (repairInput hR h3 h19 hF ht0 ht1 c).DefectBound (M c)) {η Mb : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hz : ∀ c, |zMean (F := F) t (compU c) (compV c) - 1| ≤ η)
    (hMb : ∀ c, M c ≤ Mb) {N : Matrix (Fin 3 → F) (Fin 3 → F) ℝ}
    (hN : ∀ a b, N a b =
      ∑ c, signedCoef t c * (repairInput hR h3 h19 hF ht0 ht1 c).repair (M c) (a, b)) :
    RecordForm hF N t ((1 + t) *
      (deltaC η Mb * X1C qF (Sarkozy.SignedEstimates.e0 qF) (Hcard (F := F)) +
      4 * Mb * X2C qF (Sarkozy.SignedEstimates.e0 qF) (Hcard (F := F))) * qF) := by
  intro f g hf hg
  set e := Sarkozy.SignedEstimates.e0 qF with hedef
  set H := Hcard (F := F) with hHdef
  set A : Fin 3 → ℝ := fun c => ∑ x, ∑ y,
    f x * (repairInput hR h3 h19 hF ht0 ht1 c).repair (M c) (x, y) * g y with hAdef
  set E : Fin 3 → ℝ := fun c => E2 (Vk t (compU c : ℝ) (compV c : ℝ)) f g with hEdef
  have h19' : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have hq0 : 0 < qF := by linarith
  have hH0 : 0 < H := Hcard_pos hR h19
  have he0 : 0 ≤ e := e0_nonneg h19
  have he1 : e < 1 := e0_lt_one h19
  have hdot : f ⬝ᵥ (N *ᵥ g) = ∑ c, signedCoef t c * A c := by
    calc f ⬝ᵥ (N *ᵥ g) = ∑ x, ∑ y, ∑ c, signedCoef t c *
          (f x * (repairInput hR h3 h19 hF ht0 ht1 c).repair (M c) (x, y) * g y) := by
          simp only [dotProduct, mulVec, hN]
          refine sum_congr rfl fun x _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun y _ => ?_
          rw [sum_mul, mul_sum]
          exact sum_congr rfl fun c _ => by ring
      _ = ∑ c, ∑ x, ∑ y, signedCoef t c *
          (f x * (repairInput hR h3 h19 hF ht0 ht1 c).repair (M c) (x, y) * g y) := sum3_swap _
      _ = ∑ c, signedCoef t c * A c := by
          refine sum_congr rfl fun c _ => ?_
          simp only [hAdef, mul_sum]
  have hE : E2 (signedV t) f g = ∑ c, signedCoef t c * E c := by
    calc E2 (signedV t) f g = ∑ x, ∑ y, ∑ c, signedCoef t c * (hfI x * hfI y * f x * g y *
          Vk t (compU c : ℝ) (compV c : ℝ) x y / H ^ 2) := by
          unfold E2 signedV
          refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
          rw [mul_sum, sum_div]
          exact sum_congr rfl fun c _ => by ring
      _ = ∑ c, ∑ x, ∑ y, signedCoef t c * (hfI x * hfI y * f x * g y *
          Vk t (compU c : ℝ) (compV c : ℝ) x y / H ^ 2) := sum3_swap _
      _ = ∑ c, signedCoef t c * E c := by
          refine sum_congr rfl fun c _ => ?_
          simp only [hEdef, E2, mul_sum, hHdef]
  set NN := √(mip (m0 hF).weight f f) * √(mip (m0 hF).weight g g) with hNN
  have hNN0 : 0 ≤ NN := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hX1 : 0 ≤ X1C qF e H := by
    unfold X1C; have : 0 < 1 - e := by linarith
    positivity
  have hX2 : 0 ≤ X2C qF e H := by
    unfold X2C; have : 0 < qF - 1 := by linarith
    positivity
  set B := (deltaC η Mb * X1C qF e H + 4 * Mb * X2C qF e H) * NN with hBdef
  have hD : ∀ c, |A c - E c| ≤ B := by
    intro c
    have h := comp_diff hR h3 h19 hF ht0 ht1 c (hM0 c) (hM c) hη1 (hz c) f g hf hg
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hNN0)
    have h1 := deltaC_mono hη0 hη1 (hMb c)
    have h2 : 4 * M c * X2C qF e H ≤ 4 * Mb * X2C qF e H :=
      mul_le_mul_of_nonneg_right (by linarith [hMb c]) hX2
    have h3' := mul_le_mul_of_nonneg_right h1 hX1
    linarith
  rw [hdot, hE, ← sum_sub_distrib]
  have e3 : ∑ c, (signedCoef t c * A c - signedCoef t c * E c) =
      ∑ c, signedCoef t c * (A c - E c) := sum_congr rfl fun c _ => by ring
  rw [e3]
  have hq : (1 + t) * (deltaC η Mb * X1C qF e H + 4 * Mb * X2C qF e H) * qF * qF⁻¹ * NN =
      (1 + t) * B := by
    rw [hBdef]; field_simp
  rw [hq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hc : ∀ c, |signedCoef t c * (A c - E c)| ≤ |signedCoef t c| * B := fun c => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD c) (abs_nonneg _)
  refine (sum_le_sum fun c _ => hc c).trans (le_of_eq ?_)
  simp only [Fin.sum_univ_three, signedCoef, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, abs_one, abs_neg,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ t / 2)]
  ring

end Prime

end Sarkozy.SignedDecompCrude
