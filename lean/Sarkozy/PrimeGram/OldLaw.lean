module

public import Sarkozy.PrimeGram.Kernel

@[expose] public section

/-!
# `lem:old-f-law`(f) from `lem:old-f-law`(b)(ii) and `lem:record:conditional-collision`(d) (PG)

`paper/sections/21_middle_records.tex`, `lem:old-f-law`(a),(b),(f) and the proof of (e),(f)
("Transport", "The remainder").

At one prime, with `m = m₀` (B8's `m0`), `ν = ν_F` (uniform on `H_F`), `g₀ = dm₀/dν`, the coupling
`C₀(x, y) = K₀(toY(x, y))` of `T_old`, `q = 1/p`, `r = p^{-1/2}`, `e₀ = 2q/((1-3q)(1-4q))`:

* **`K0_eq`** (`lem:old-f-law`): `K₀ = 1_{H_F}(x) 1_{H_F}(y) Ψ₀(x, y) / (4 |Inj|)` with
  `Ψ₀ = I_×(1 + 𝖠)(1 + 𝖡)`; **`dot_C0`**: `⟨f, T_old g⟩_{m₀} = z₀⁻¹ E_{ν⊗ν}[f Ψ₀ g]`,
  `z₀ = 4|Inj|/|H_F|²`; **`z0_bounds`**: `h₀ = 1 - 14q ≤ z₀ ≤ 1` (`lem:old-f-law`(a)).
* **`Psi0_split`** (`lem:old-f-law`(b)): `Ψ₀ = 1 + 𝖫 + 𝖠𝖡 - 𝖢_rem`.
* The transport rules of the proof: the constant kernel (T3, `c_g`), the leading kernel through
  `oForm_eq_kernel` and the bilinearity of `O₀` (T2, `D_g`), the kernel `𝖠𝖡` (T1).
* **`oldDecomp_of_inputs`**: with the two named inputs
  - `ABBound` (`lem:old-f-law`(b)(ii)): `‖𝖠𝖡‖ ≤ 2q/(1 - q)` on `L²(ν_F)`;
  - `CollisionBound c_col` (`lem:record:conditional-collision`(d), last claim): on the
    `m₀`-centred functions the operator of `𝖢_rem` on `L²(m₀)` has norm at most `c_col q`;
  `OldDecomp m₀ C₀ e_o` holds with the paper's
  `e_o = r_o + n_o`, `r_o = 2/(Z(1 - e₀)) + c_col + c_g/q + (D_g/q) Γ r`,
  `n_o = (14/h₀)(Γ + r_o r) r` (`eq:signed-constants`), `Γ = gammaW ≤ Γ_A`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents
  Sarkozy.SignedEstimates Sarkozy.MiddleRecords

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-! ## Kernels on pairs of halves -/

/-- The channel `𝖠 = χ(y₂ - x₀)` (`eq:middle:channels`). -/
noncomputable def chA (x y : Fin 3 → F) : ℝ := (χ (y 2 - x 0) : ℝ)

/-- The channel `𝖡 = χ(x₂ - y₀)`. -/
noncomputable def chB (x y : Fin 3 → F) : ℝ := (χ (x 2 - y 0) : ℝ)

/-- `I_×`: the two halves have no common label. -/
def Icr (x y : Fin 3 → F) : ℝ := if ∀ i j, x i ≠ y j then 1 else 0

/-- The indicator of `H_F`. -/
def hfI (x : Fin 3 → F) : ℝ := if HF x then 1 else 0

/-- `Ψ₀ = I_×(1 + 𝖠)(1 + 𝖡)` (`lem:old-f-law`). -/
noncomputable def Psi0 (x y : Fin 3 → F) : ℝ := Icr x y * (1 + chA x y) * (1 + chB x y)

/-- `𝖢_rem = (1 - I_×)(1 + 𝖠)(1 + 𝖡)` (`lem:old-f-law`(b)). -/
noncomputable def Crem (x y : Fin 3 → F) : ℝ := (1 - Icr x y) * ((1 + chA x y) * (1 + chB x y))

/-- `E_{ν_F ⊗ ν_F}[f(x) K(x, y) g(y)]`: the bilinear form of the operator of a kernel `K` (the
paper's convention: the operator of `K` on `L²(m)` has this form for every `m = g ν_F`). -/
noncomputable def E2 (K : (Fin 3 → F) → (Fin 3 → F) → ℝ) (f g : (Fin 3 → F) → ℝ) : ℝ :=
  ∑ x, ∑ y, hfI x * hfI y * f x * g y * K x y / Hcard (F := F) ^ 2

/-- `E_{ν_F} f`. -/
noncomputable def Enu (f : (Fin 3 → F) → ℝ) : ℝ := ∑ x, hfI x * f x / Hcard (F := F)

/-- **`lem:old-f-law`(b)(ii)** (hypothesis): `‖𝖠𝖡‖ ≤ 2q/(1 - q)` on `L²(ν_F)`. -/
def ABBound : Prop :=
  ∀ f g : (Fin 3 → F) → ℝ, |E2 (fun x y => chA x y * chB x y) f g| ≤
    2 * qF⁻¹ / (1 - qF⁻¹) * (√(Enu (fun x => f x ^ 2)) * √(Enu (fun x => g x ^ 2)))

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

/-- **`lem:record:conditional-collision`(d), the last claim** (hypothesis): on the `m₀`-centred
functions of `L²(m₀)` the operator of `𝖢_rem` has norm at most `c_col q`. -/
def CollisionBound (ccol : ℝ) : Prop :=
  ∀ f g : (Fin 3 → F) → ℝ, (m0 hF).weight ⬝ᵥ f = 0 → (m0 hF).weight ⬝ᵥ g = 0 →
    |E2 Crem f g| ≤ ccol * qF⁻¹ * (√(mip (m0 hF).weight f f) * √(mip (m0 hF).weight g g))

/-- The coupling matrix of `T_old` (SGA's `oldP` at one prime). -/
noncomputable def C0 : Matrix (Fin 3 → F) (Fin 3 → F) ℝ := fun a b => (K0 hF).weight (toY (a, b))

/-- `|Inj_p(G_{F,2})|`. -/
noncomputable def Icard : ℝ := ((injLabellings F (foldGraph (Fin 2))).card : ℝ)

/-- **`K₀` as a kernel** (`lem:old-f-law`): `K₀(x, y) = 1_{H_F}(x) 1_{H_F}(y) Ψ₀(x, y)/(4|Inj|)`. -/
theorem K0_eq (x y : Fin 3 → F) :
    (K0 hF).weight (toY (x, y)) = hfI x * hfI y * Psi0 x y / (4 * Icard (F := F)) := by
  change (if toY (x, y) ∈ injLabellings F (foldGraph (Fin 2)) then
    1 / ((injLabellings F (foldGraph (Fin 2))).card : ℝ) else 0) = _
  unfold Icard
  by_cases hm : toY (x, y) ∈ injLabellings F (foldGraph (Fin 2))
  · obtain ⟨hx, hy, hd, hA, hB⟩ := (mem_inj_iff x y).mp hm
    have hc : ((injLabellings F (foldGraph (Fin 2))).card : ℝ) ≠ 0 := by
      exact_mod_cast (card_pos.mpr hF).ne'
    have hA' : (χ (y 2 - x 0) : ℝ) = 1 := by exact_mod_cast hA
    have hB' : (χ (x 2 - y 0) : ℝ) = 1 := by exact_mod_cast hB
    have hI : Icr x y = 1 := by
      unfold Icr
      split_ifs
      rfl
    simp only [hm, ↓reduceIte, hfI, hx, hy, Psi0, hI, chA, chB, hA', hB']
    field_simp
    norm_num
  · simp only [hm, ↓reduceIte]
    have : hfI x * hfI y * Psi0 x y = 0 := by
      unfold hfI Psi0 chA chB
      by_cases hx : HF x
      swap
      · simp [hx]
      by_cases hy : HF y
      swap
      · simp [hy]
      by_cases hd : ∀ i j, x i ≠ y j
      swap
      · have hI : Icr x y = 0 := by
          unfold Icr
          split_ifs
          rfl
        rw [hI]
        ring
      have hI : Icr x y = 1 := by
        unfold Icr
        split_ifs
        rfl
      have hn : ¬ (χ (y 2 - x 0) = 1 ∧ χ (x 2 - y 0) = 1) := fun h =>
        hm ((mem_inj_iff x y).mpr ⟨hx, hy, hd, h.1, h.2⟩)
      simp only [hx, hy, ↓reduceIte, one_mul, hI]
      rcases chiR_ne_cases (sub_ne_zero.mpr (hd 0 2).symm) with ha | ha
      · rcases chiR_ne_cases (sub_ne_zero.mpr (hd 2 0)) with hb | hb
        · exact absurd ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩ hn
        · rw [hb]; ring
      · rw [ha]; ring
    rw [this, zero_div]

theorem Hcard_pos (hR : ringChar F ≠ 2) (h19 : 19 ≤ Fintype.card F) : 0 < Hcard (F := F) := by
  rw [Hcard_eq hR]
  have h : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have h1 : (0 : ℝ) < qF - 1 := by linarith
  have h2 : (0 : ℝ) < qF - 2 := by linarith
  have h0 : (0 : ℝ) < qF := by linarith
  positivity

/-- `z₀ = 4|Inj|/|H_F|²`. -/
noncomputable def z0 : ℝ := 4 * Icard (F := F) / Hcard (F := F) ^ 2

/-- **`⟨f, T_old g⟩_{m₀} = z₀⁻¹ E_{ν⊗ν}[f Ψ₀ g]`**. -/
theorem dot_C0 (hR : ringChar F ≠ 2) (h19 : 19 ≤ Fintype.card F) (f g : (Fin 3 → F) → ℝ) :
    f ⬝ᵥ (C0 hF *ᵥ g) = (z0 (F := F))⁻¹ * E2 Psi0 f g := by
  have hH := (Hcard_pos (F := F) hR h19).ne'
  have hc : Icard (F := F) ≠ 0 := by
    unfold Icard; exact_mod_cast (card_pos.mpr hF).ne'
  unfold z0 E2
  simp only [dotProduct, mulVec, C0, K0_eq hF, mul_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  field_simp

/-- **`Ψ₀ = 1 + 𝖫 + 𝖠𝖡 - 𝖢_rem`** (`lem:old-f-law`(b)), `𝖫 = 𝖠 + 𝖡`. -/
theorem Psi0_split (x y : Fin 3 → F) :
    Psi0 x y = 1 + (chA x y + chB x y) + chA x y * chB x y - Crem x y := by
  unfold Psi0 Crem
  ring

theorem E2_split (f g : (Fin 3 → F) → ℝ) :
    E2 Psi0 f g = Enu f * Enu g + E2 (fun x y => chA x y + chB x y) f g +
      E2 (fun x y => chA x y * chB x y) f g - E2 Crem f g := by
  have e1 : E2 (fun _ _ => (1 : ℝ)) f g = Enu f * Enu g := by
    unfold E2 Enu
    rw [sum_mul]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    ring
  rw [← e1]
  unfold E2
  simp only [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [Psi0_split]
  ring

/-! ## The density `g₀` -/

/-- `f/g₀` on `H_F`, `0` elsewhere. -/
noncomputable def divG (f : (Fin 3 → F) → ℝ) : (Fin 3 → F) → ℝ :=
  fun x => if HF x then f x / g0 hF x else 0

omit [Field F] [DecidableEq F] in
theorem e0_lt_one (h19 : 19 ≤ Fintype.card F) : e0 qF < 1 := by
  unfold e0
  have h : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  rw [div_lt_one (by nlinarith)]
  nlinarith

omit [Field F] [DecidableEq F] in
theorem e0_nonneg (h19 : 19 ≤ Fintype.card F) : 0 ≤ e0 qF := by
  unfold e0
  have h : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have h3' : (0 : ℝ) < qF - 3 := by linarith
  have h4' : (0 : ℝ) < qF - 4 := by linarith
  positivity

theorem m_zero_off {x : Fin 3 → F} (hx : ¬ HF x) : (m0 hF).weight x = 0 := by
  by_contra h
  exact hx (m0_support hF h)

section Density

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)

include hR h3 h19 in
theorem g0_ge {x : Fin 3 → F} (hx : HF x) : 1 - e0 qF ≤ g0 hF x := by
  have := g0_bound hR h3 h19 hF hx
  rw [abs_le] at this
  linarith

include hR h3 h19 in
theorem mw_divG (f : (Fin 3 → F) → ℝ) (x : Fin 3 → F) :
    (m0 hF).weight x * divG hF f x = hfI x * f x / Hcard (F := F) := by
  have hH := (Hcard_pos (F := F) hR h19).ne'
  unfold divG hfI
  by_cases hx : HF x
  · simp only [hx, ↓reduceIte]
    have hg : 0 < g0 hF x := lt_of_lt_of_le (by linarith [e0_lt_one h19]) (g0_ge hF hR h3 h19 hx)
    have e : (m0 hF).weight x = g0 hF x / Hcard (F := F) := by
      unfold g0; field_simp
    rw [e]
    field_simp
  · simp only [hx, ↓reduceIte, mul_zero, zero_mul, zero_div]

include hR h3 h19 in
/-- **`E_{ν⊗ν}[f K g] = ⟨f/g₀, K (g/g₀)⟩_{m₀ ⊗ m₀}`**. -/
theorem E2_eq_m (K : (Fin 3 → F) → (Fin 3 → F) → ℝ) (f g : (Fin 3 → F) → ℝ) :
    E2 K f g = ∑ x, ∑ y, (m0 hF).weight x * (m0 hF).weight y * divG hF f x * divG hF g y *
      K x y := by
  unfold E2
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  have e : (m0 hF).weight x * (m0 hF).weight y * divG hF f x * divG hF g y * K x y =
      ((m0 hF).weight x * divG hF f x) * ((m0 hF).weight y * divG hF g y) * K x y := by ring
  rw [e, mw_divG hF hR h3 h19, mw_divG hF hR h3 h19]
  ring

include hR h3 h19 in
/-- `‖f/g₀ - f‖_{m₀} ≤ (e₀/(1 - e₀)) ‖f‖_{m₀}`. -/
theorem norm_divG_sub (f : (Fin 3 → F) → ℝ) :
    mip (m0 hF).weight (fun x => divG hF f x - f x) (fun x => divG hF f x - f x) ≤
      (e0 qF / (1 - e0 qF)) ^ 2 * mip (m0 hF).weight f f := by
  have he := e0_lt_one h19
  have he0 := e0_nonneg h19
  unfold mip
  rw [mul_sum]
  refine sum_le_sum fun x _ => ?_
  have hm := (m0 hF).nonneg x
  by_cases hx : HF x
  · have hg := g0_ge hF hR h3 h19 hx
    have hb := g0_bound hR h3 h19 hF hx
    have hgp : 0 < g0 hF x := by linarith
    simp only [divG, hx, ↓reduceIte]
    have e : f x / g0 hF x - f x = f x * ((1 - g0 hF x) / g0 hF x) := by field_simp
    rw [e]
    have hk : |(1 - g0 hF x) / g0 hF x| ≤ e0 qF / (1 - e0 qF) := by
      rw [abs_div, abs_of_pos hgp, abs_sub_comm]
      exact div_le_div₀ he0 hb (by linarith) hg
    have hk2 : ((1 - g0 hF x) / g0 hF x) ^ 2 ≤ (e0 qF / (1 - e0 qF)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hk 2
    nlinarith [mul_le_mul_of_nonneg_left hk2 (mul_nonneg hm (sq_nonneg (f x)))]
  · rw [m_zero_off hF hx]
    simp

include hR h3 h19 in
/-- `‖f/g₀‖_{m₀} ≤ ‖f‖_{m₀}/(1 - e₀)`. -/
theorem norm_divG (f : (Fin 3 → F) → ℝ) :
    mip (m0 hF).weight (divG hF f) (divG hF f) ≤
      (1 / (1 - e0 qF)) ^ 2 * mip (m0 hF).weight f f := by
  have he := e0_lt_one h19
  unfold mip
  rw [mul_sum]
  refine sum_le_sum fun x _ => ?_
  have hm := (m0 hF).nonneg x
  by_cases hx : HF x
  · have hg := g0_ge hF hR h3 h19 hx
    have hgp : 0 < g0 hF x := by linarith
    simp only [divG, hx, ↓reduceIte]
    have hk : 1 / g0 hF x ≤ 1 / (1 - e0 qF) := one_div_le_one_div_of_le (by linarith) hg
    have hk0 : 0 ≤ 1 / g0 hF x := by positivity
    have hk2 : (1 / g0 hF x) ^ 2 ≤ (1 / (1 - e0 qF)) ^ 2 := pow_le_pow_left₀ hk0 hk 2
    have e : (m0 hF).weight x * (f x / g0 hF x) * (f x / g0 hF x) =
        (m0 hF).weight x * f x ^ 2 * (1 / g0 hF x) ^ 2 := by field_simp
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hk2 (mul_nonneg hm (sq_nonneg (f x)))]
  · rw [m_zero_off hF hx]
    simp

include hR h3 h19 in
/-- **(T3)**: for `m₀`-centred `f`, `|E_ν f| ≤ (e₀/(1 - e₀)) ‖f‖_{m₀}`. -/
theorem Enu_centred (f : (Fin 3 → F) → ℝ) (hf : (m0 hF).weight ⬝ᵥ f = 0) :
    |Enu f| ≤ e0 qF / (1 - e0 qF) * √(mip (m0 hF).weight f f) := by
  have hm : ∀ x, 0 ≤ (m0 hF).weight x := (m0 hF).nonneg
  have e : Enu f = mip (m0 hF).weight (fun x => divG hF f x - f x) (fun _ => 1) := by
    unfold Enu mip
    have hf' : ∑ x, (m0 hF).weight x * f x = 0 := hf
    have : ∑ x, (m0 hF).weight x * (divG hF f x - f x) * 1 =
        ∑ x, (m0 hF).weight x * divG hF f x - ∑ x, (m0 hF).weight x * f x := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun x _ => by ring
    rw [this, hf', sub_zero]
    exact sum_congr rfl fun x _ => (mw_divG hF hR h3 h19 f x).symm
  have h1 : mip (m0 hF).weight (fun _ => (1 : ℝ)) (fun _ => 1) = 1 := by
    unfold mip; simp [(m0 hF).total]
  have hcs := mip_sq_le hm (fun x => divG hF f x - f x) (fun _ => 1)
  rw [h1, mul_one, ← e] at hcs
  have h2 := norm_divG_sub hF hR h3 h19 f
  have he := e0_lt_one h19
  have he0 := e0_nonneg h19
  have hk : 0 ≤ e0 qF / (1 - e0 qF) := div_nonneg he0 (by linarith)
  have hff := mip_self_nonneg hm f
  calc |Enu f| ≤ √(mip (m0 hF).weight (fun x => divG hF f x - f x)
        (fun x => divG hF f x - f x)) := Real.abs_le_sqrt hcs
    _ ≤ √((e0 qF / (1 - e0 qF)) ^ 2 * mip (m0 hF).weight f f) := Real.sqrt_le_sqrt h2
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk]

include hR h3 h19 in
/-- **(T1)**: `E_ν[f²] ≤ ‖f‖²_{m₀}/(1 - e₀)`. -/
theorem Enu_sq (f : (Fin 3 → F) → ℝ) :
    Enu (fun x => f x ^ 2) ≤ mip (m0 hF).weight f f / (1 - e0 qF) := by
  have he := e0_lt_one h19
  have hH := Hcard_pos (F := F) hR h19
  unfold Enu mip
  rw [sum_div]
  refine sum_le_sum fun x _ => ?_
  by_cases hx : HF x
  · have hg := g0_ge hF hR h3 h19 hx
    have e : (m0 hF).weight x = g0 hF x / Hcard (F := F) := by
      unfold g0; field_simp
    simp only [hfI, hx, ↓reduceIte, one_mul]
    rw [e, le_div_iff₀ (by linarith)]
    have hf2 := sq_nonneg (f x)
    have : f x ^ 2 / Hcard (F := F) * (1 - e0 qF) ≤ g0 hF x / Hcard (F := F) * f x * f x := by
      rw [div_mul_eq_mul_div, mul_assoc, mul_comm (g0 hF x / Hcard (F := F)), ← sq]
      rw [show f x ^ 2 * (g0 hF x / Hcard (F := F)) = f x ^ 2 * g0 hF x / Hcard (F := F) by ring]
      apply div_le_div_of_nonneg_right _ hH.le
      exact mul_le_mul_of_nonneg_left hg hf2
    exact this
  · simp only [hfI, hx, ↓reduceIte, zero_mul, zero_div]
    rw [m_zero_off hF hx]
    simp

end Density

end Sarkozy.PrimeGram
