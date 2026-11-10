module

public import Sarkozy.OpsFeature.Label3
public import Sarkozy.PrimeGram.Gram

@[expose] public section

/-!
# The leading star at a prime is the lift of `𝖥(Φ̂_p)` (`eq:signed-star`, `hLb` at one prime)

`paper/sections/23_envelopes.tex`, after `eq:signed-star`: "The lift of `𝖥(Φ̂_p)` by `Ξ_p` is
`r_p⁻¹` times the leading signed star `L°_{t,p} = A°_t V₀^* − V₀(A°_t)^*` of
`eq:signed-leading`, `A°_t = r_p(V₁Φ̂_p + t V₂Φ̂_p) + (1 − t)A₃°`", with
`Ξ_p = (V₀, V₁, V₂, A₃°/r_p, 0)`.

**PG's leading form against the paper's `A°_t`.** PG (`PrimeGram.Gram.lForm`, `Lm`) has
`L^m_t = A_{a_t} V₀^{*m} − V₀ A_{a_t}^{*m}` with `a_t = (t, 1, 1 − t)` (`Envelopes.aT`) on the arms
`(A₁, A₂, A₃) = (V₂P, V₁P, A₃)` (`PrimeGram.arm`), `P = r Φ̂`. So
`A_{a_t} = t V₂P + V₁P + (1 − t)A₃ = r(V₁Φ̂ + tV₂Φ̂) + (1 − t)A₃`: the paper's `A°_t` exactly,
except that PG's third arm is the unprojected `A₃` and the paper's is `A₃°` (OPS-L's finding 5).

Here the third arm is a parameter `Y` (`lFormY m t Y`, with `lFormY m t A₃ = lForm m t`,
`lFormY_A3`), so the identity covers both:

* **`lFormY_eq_starForm`**: `lFormY m t Y f g = r · ∑_{a,b} ⟨ξ_a f, 𝖥(Φ̂)_{ab} ξ_b g⟩_{H₀}` with
  `ξ = (V₀^{*m}, V₁^{*m}, V₂^{*m}, r⁻¹ Y^{*m})` (`xiF`), the adjoints of `Ξ = (V₀, V₁, V₂, Y/r)`
  restricted to `H₀`, and `𝖥(Φ̂)` the paper's star at a general `t` (`foldStarT`;
  `foldStarT tlaw = foldStar`). That is, `⟨f, L^m_t g⟩_m = r ⟨f, Ξ 𝖥(Φ̂) Ξ^* g⟩_m`.

* **`kern_lead_prime`**: an operator with `⟨f, L g⟩_m = c · lFormY(f, g)` has the kernel
  `c r p⁻¹ Ξ 𝖥(Φ̂) Ξᵀ` (`starForm_delta`, `XiM`); **`kern_block_lead`**: at a fold block, for
  prime forms placed on the singleton sectors by linear maps `C_j` (OPS-L's `singForm`), the
  kernel is the star form `∑_j c_j (C_jΞ_j) 𝖥(Φ̂_j) (C_jΞ_j)ᵀ`; `kern_block_lead_starSum`: the
  same in the shape of `starKer` (`hLb`), `Ξ_j = p_j^{-1/2} C_j XiM_j`, `c_j = c r_j`;
* `lFormY_sub`: the projected and the unprojected third arm differ by `(1 − t)` times the
  `(Y − Y')` terms only; `adj_expand`, `lFormY_expand`: linearity.

The ingredients: `adj_paley` (`(V_i P)^{*m} = −P V_i^{*m}`, from `χ(−1) = −1`) and the skewness of
`Φ̂` in `H₀` (`uip_phiApp_skew`). With `Y = A₃°` this is the paper's sentence; with `Y = A₃` it is
the star form of PG's (and OPS-L's) unprojected leading star.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.TraceMixing Sarkozy.Envelopes Sarkozy.PrimeGram

section Prime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-- The coordinate lift `V_i h = h(x_i)`. -/
def Vc (i : Fin 3) (h : F → ℝ) : (Fin 3 → F) → ℝ := fun x => h (x i)

/-- `Φ̂` applied to a function. -/
noncomputable def phiApp (w : F → ℝ) : F → ℝ := fun z => ∑ z', phiHat z z' * w z'

/-- `P = r Φ̂`. -/
theorem paleyOp_eq_phiApp (w : F → ℝ) (z : F) :
    paleyOp w z = (Real.sqrt qF)⁻¹ * phiApp w z := by
  have hq : 0 < qF := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt qF * Real.sqrt qF = qF := Real.mul_self_sqrt hq.le
  have hs0 : Real.sqrt qF ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  unfold paleyOp phiApp phiHat
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  calc qF⁻¹ * ((χ (t - z) : ℝ) * w t)
      = (χ (t - z) : ℝ) * w t / (Real.sqrt qF * Real.sqrt qF) := by
        rw [hs]; field_simp
    _ = (Real.sqrt qF)⁻¹ * ((χ (t - z) : ℝ) / Real.sqrt qF * w t) := by
        field_simp

/-- **`Φ̂` is skew in `H₀`**: `⟨Φ̂ k, w⟩ = −⟨k, Φ̂ w⟩`. -/
theorem uip_phiApp_skew (h3 : Fintype.card F % 4 = 3) (k w : F → ℝ) :
    uip (phiApp k) w = -uip k (phiApp w) := by
  have key : ∑ z, (∑ z', phiHat z z' * k z') * w z =
      -∑ z', k z' * ∑ z, phiHat z' z * w z := by
    simp only [sum_mul, mul_sum, ← sum_neg_distrib]
    rw [sum_comm]
    refine sum_congr rfl fun z' _ => sum_congr rfl fun z _ => ?_
    rw [phiHat_antisymm h3 z z']
    ring
  unfold uip phiApp
  rw [key]
  ring

/-- **`(V_i P)^{*m} = −P V_i^{*m}`**, as `−r Φ̂ V_i^{*m}`. -/
theorem adj_paley (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (m : (Fin 3 → F) → ℝ) (i : Fin 3) (f : (Fin 3 → F) → ℝ) :
    adj m (fun h x => paleyOp h (x i)) f =
      fun s => -((Real.sqrt qF)⁻¹ * phiApp (adj m (Vc i) f) s) := by
  have hq : 0 < qF := by exact_mod_cast Fintype.card_pos
  have hq0 : qF ≠ 0 := hq.ne'
  -- the left side: `G(s) = ∑_x m(x) χ(s − x_i) f(x)`, already centred
  have hL : ∀ s, qF * mip m (fun x => paleyOp (PrimeGram.delta s) (x i)) f =
      ∑ x, m x * (χ (s - x i) : ℝ) * f x := by
    intro s
    unfold mip paleyOp PrimeGram.delta
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
    field_simp
  have hG0 : ∑ s, ∑ x, m x * (χ (s - x i) : ℝ) * f x = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun x _ => ?_
    have := sum_chi_shift hF (x i)
    have hR : ∑ s, (χ (s - x i) : ℝ) = 0 := by exact_mod_cast this
    simp only [mul_assoc, ← mul_sum, ← sum_mul, hR, zero_mul, mul_zero]
  -- the right side
  have hK : ∀ u, qF * mip m (Vc i (PrimeGram.delta u)) f =
      qF * ∑ x, (if x i = u then m x * f x else 0) := by
    intro u
    unfold mip Vc PrimeGram.delta
    congr 1
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  funext s
  unfold adj
  simp only [hL, hK]
  unfold cen phiApp phiHat
  rw [hG0, mul_zero, sub_zero]
  -- `∑_{z'} χ(z' − s)/√p (K z' − mean K) = (1/√p) ∑_{z'} χ(z' − s) K z'`
  have hc : ∑ z', (χ (z' - s) : ℝ) = 0 := by exact_mod_cast sum_chi_shift hF s
  have e1 : ∑ z', (χ (z' - s) : ℝ) / Real.sqrt qF *
      (qF * ∑ x, (if x i = z' then m x * f x else 0) -
        qF⁻¹ * ∑ s', qF * ∑ x, (if x i = s' then m x * f x else 0)) =
      ∑ z', (χ (z' - s) : ℝ) / Real.sqrt qF * (qF * ∑ x, (if x i = z' then m x * f x else 0)) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [sub_eq_self, ← sum_mul, ← sum_div, hc, zero_div, zero_mul]
  rw [e1]
  -- collapse `∑_{z'} χ(z' − s) ∑_x [x_i = z'] m f = ∑_x χ(x_i − s) m f`
  have e2 : ∑ z', (χ (z' - s) : ℝ) / Real.sqrt qF *
      (qF * ∑ x, (if x i = z' then m x * f x else 0)) =
      qF / Real.sqrt qF * ∑ x, (χ (x i - s) : ℝ) * (m x * f x) := by
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    simp only [mul_ite, mul_zero]
    rw [sum_ite_eq]
    simp only [mem_univ, ↓reduceIte]
    ring
  rw [e2]
  have hs : Real.sqrt qF * Real.sqrt qF = qF := Real.mul_self_sqrt hq.le
  have hs0 : Real.sqrt qF ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have e3 : (Real.sqrt qF)⁻¹ * (qF / Real.sqrt qF) = 1 := by
    rw [inv_mul_eq_div, div_div, hs, div_self hq0]
  rw [← mul_assoc, e3, one_mul, ← sum_neg_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [chi_swap h3 (x i) s]
  push_cast
  ring

/-- The paper's fold star `𝖥(Φ̂)` at a general `t` (`foldStarT tlaw = foldStar`). -/
noncomputable def foldStarT (t : ℝ) : Matrix (Fin 4 × F) (Fin 4 × F) ℝ := fun x x' =>
  if x.1 = 0 ∧ x'.1 = 1 then phiHat x.2 x'.2
  else if x.1 = 1 ∧ x'.1 = 0 then phiHat x.2 x'.2
  else if x.1 = 0 ∧ x'.1 = 2 then t * phiHat x.2 x'.2
  else if x.1 = 2 ∧ x'.1 = 0 then t * phiHat x.2 x'.2
  else if x.1 = 0 ∧ x'.1 = 3 then (t - 1) * (if x.2 = x'.2 then 1 else 0)
  else if x.1 = 3 ∧ x'.1 = 0 then (1 - t) * (if x.2 = x'.2 then 1 else 0)
  else 0

theorem foldStarT_tlaw : foldStarT (F := F) tlaw = foldStar := rfl

/-- The row `(𝖥(Φ̂)_{ab} w)(z) = ∑_{z'} 𝖥(Φ̂)((a, z), (b, z')) w(z')`. -/
noncomputable def rowT (t : ℝ) (a b : Fin 4) (w : F → ℝ) : F → ℝ :=
  fun z => ∑ z', foldStarT t (a, z) (b, z') * w z'

theorem rowT_eq (t : ℝ) (a b : Fin 4) (w : F → ℝ) :
    rowT t a b w = fun z =>
      if a = 0 ∧ b = 1 then phiApp w z
      else if a = 1 ∧ b = 0 then phiApp w z
      else if a = 0 ∧ b = 2 then t * phiApp w z
      else if a = 2 ∧ b = 0 then t * phiApp w z
      else if a = 0 ∧ b = 3 then (t - 1) * w z
      else if a = 3 ∧ b = 0 then (1 - t) * w z
      else 0 := by
  funext z
  unfold rowT foldStarT phiApp
  simp only
  split_ifs <;> simp [mul_sum, mul_assoc]

/-- The coordinate adjoints and the scaled third arm:
`ξ = (V₀^{*m}, V₁^{*m}, V₂^{*m}, r⁻¹ Y^{*m})`. -/
noncomputable def xiF (m : (Fin 3 → F) → ℝ) (Y : (F → ℝ) → (Fin 3 → F) → ℝ) :
    Fin 4 → ((Fin 3 → F) → ℝ) → F → ℝ :=
  ![adj m (Vc 0), adj m (Vc 1), adj m (Vc 2), fun f z => Real.sqrt qF * adj m Y f z]

/-- The form of the lift of `𝖥(Φ̂)` by `Ξ`: `∑_{a,b} ⟨ξ_a f, 𝖥(Φ̂)_{ab} ξ_b g⟩_{H₀}`. -/
noncomputable def starForm (m : (Fin 3 → F) → ℝ) (t : ℝ) (Y : (F → ℝ) → (Fin 3 → F) → ℝ)
    (f g : (Fin 3 → F) → ℝ) : ℝ :=
  ∑ a, ∑ b, uip (xiF m Y a f) (rowT t a b (xiF m Y b g))

/-- PG's arms with a general third arm `Y`. -/
noncomputable def armY (Y : (F → ℝ) → (Fin 3 → F) → ℝ) : Fin 3 → (F → ℝ) → (Fin 3 → F) → ℝ :=
  ![A1, A2, Y]

/-- PG's leading form `lForm` with a general third arm `Y`. -/
noncomputable def lFormY (m : (Fin 3 → F) → ℝ) (t : ℝ) (Y : (F → ℝ) → (Fin 3 → F) → ℝ)
    (f g : (Fin 3 → F) → ℝ) : ℝ :=
  ∑ i, aT t i * uip (adj m (armY Y i) f) (Wa m g) -
    ∑ i, aT t i * uip (Wa m f) (adj m (armY Y i) g)

theorem lFormY_A3 (m : (Fin 3 → F) → ℝ) (t : ℝ) (f g : (Fin 3 → F) → ℝ) :
    lFormY m t A3 f g = lForm m t f g := rfl

omit [Field F] [DecidableEq F] in
theorem uip_mul_left (c : ℝ) (h w : F → ℝ) : uip (fun s => c * h s) w = c * uip h w := by
  unfold uip
  rw [mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun s _ => by ring

omit [Field F] [DecidableEq F] in
theorem uip_mul_right (c : ℝ) (h w : F → ℝ) : uip h (fun s => c * w s) = c * uip h w := by
  unfold uip
  rw [mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun s _ => by ring

omit [Field F] [DecidableEq F] in
theorem uip_neg_left (h w : F → ℝ) : uip (fun s => -h s) w = -uip h w := by
  unfold uip
  rw [← mul_neg, ← sum_neg_distrib]
  exact congrArg _ (sum_congr rfl fun s _ => by ring)

omit [Field F] [DecidableEq F] in
theorem uip_neg_right (h w : F → ℝ) : uip h (fun s => -w s) = -uip h w := by
  unfold uip
  rw [← mul_neg, ← sum_neg_distrib]
  exact congrArg _ (sum_congr rfl fun s _ => by ring)

omit [Field F] [DecidableEq F] in
theorem uip_zero_right (h : F → ℝ) : uip h (fun _ => 0) = 0 := by
  simp [uip]

/-- **The leading star at a prime is `r` times the lift of `𝖥(Φ̂)`** (`eq:signed-star`): PG's
leading form with the third arm `Y` is `r ∑_{a,b} ⟨ξ_a f, 𝖥(Φ̂)_{ab} ξ_b g⟩`,
`ξ = (V₀^{*m}, V₁^{*m}, V₂^{*m}, r⁻¹Y^{*m})`. -/
theorem lFormY_eq_starForm (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (m : (Fin 3 → F) → ℝ) (t : ℝ) (Y : (F → ℝ) → (Fin 3 → F) → ℝ) (f g : (Fin 3 → F) → ℝ) :
    lFormY m t Y f g = (Real.sqrt qF)⁻¹ * starForm m t Y f g := by
  have hq : 0 < qF := by exact_mod_cast Fintype.card_pos
  have hs0 : Real.sqrt qF ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hr : (Real.sqrt qF)⁻¹ * Real.sqrt qF = 1 := inv_mul_cancel₀ hs0
  have hA1 : ∀ f, adj m A1 f = fun s => -((Real.sqrt qF)⁻¹ * phiApp (adj m (Vc 2) f) s) :=
    fun f => adj_paley hF h3 m 2 f
  have hA2 : ∀ f, adj m A2 f = fun s => -((Real.sqrt qF)⁻¹ * phiApp (adj m (Vc 1) f) s) :=
    fun f => adj_paley hF h3 m 1 f
  have hW : ∀ g, Wa m g = adj m (Vc 0) g := fun g => rfl
  have hx0 : xiF m Y 0 = adj m (Vc 0) := rfl
  have hx1 : xiF m Y 1 = adj m (Vc 1) := rfl
  have hx2 : xiF m Y 2 = adj m (Vc 2) := rfl
  have hx3 : ∀ f, xiF m Y 3 f = fun z => Real.sqrt qF * adj m Y f z := fun f => rfl
  have ha0 : armY Y 0 = A1 := rfl
  have ha1 : armY Y 1 = A2 := rfl
  have ha2 : armY Y 2 = Y := rfl
  have hsk := uip_phiApp_skew h3
  unfold lFormY starForm
  simp only [Fin.sum_univ_three, Fin.sum_univ_four, ha0, ha1, ha2, hA1, hA2, hW, hx0, hx1, hx2,
    hx3, rowT_eq, aT, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, and_true, and_false,
    Fin.reduceEq, ↓reduceIte, uip_mul_left, uip_mul_right, uip_neg_left,
    uip_neg_right, uip_zero_right]
  rw [hsk (adj m (Vc 2) f), hsk (adj m (Vc 1) f)]
  linear_combination ((1 - t) * (uip (adj m (Vc 0) f) (adj m Y g) -
    uip (adj m Y f) (adj m (Vc 0) g))) * hr

/-- The sector map `Ξ` as a matrix: `Ξ(x, (a, z)) = (ξ_a δ_x)(z)`. -/
noncomputable def XiM (m : (Fin 3 → F) → ℝ) (Y : (F → ℝ) → (Fin 3 → F) → ℝ) :
    Matrix (Fin 3 → F) (Fin 4 × F) ℝ := fun x az => xiF m Y az.1 (EnvelopeSteps.delta x) az.2

/-- **The star form at point masses is the lifted matrix**:
`∑_{a,b} ⟨ξ_a δ_x, 𝖥(Φ̂)_{ab} ξ_b δ_y⟩_{H₀} = p⁻¹ (Ξ 𝖥(Φ̂) Ξᵀ)(x, y)`. -/
theorem starForm_delta (m : (Fin 3 → F) → ℝ) (t : ℝ) (Y : (F → ℝ) → (Fin 3 → F) → ℝ)
    (x y : Fin 3 → F) :
    starForm m t Y (EnvelopeSteps.delta x) (EnvelopeSteps.delta y) =
      qF⁻¹ * (XiM m Y * foldStarT (F := F) t * (XiM m Y)ᵀ) x y := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, transpose_apply, XiM, Fintype.sum_prod_type]
  unfold starForm uip rowT
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [← mul_sum, sum_comm]
  congr 1
  refine sum_congr rfl fun z _ => ?_
  rw [mul_sum]

/-- **The kernel of a leading operator at a prime** (`hLb` at one prime): if `⟨f, L g⟩_m =
c · lFormY m t Y f g` (OPS-L's `opOfForm`, `ip_opOfForm`, with `c = w⁻¹`), then
`kern_m L = c r p⁻¹ · Ξ 𝖥(Φ̂) Ξᵀ` with `Ξ = XiM m Y`, the lift of `𝖥(Φ̂)` by
`(V₀, V₁, V₂, Y/r)` (`eq:signed-star` with `Y = A₃°`; with `Y = A₃` PG's unprojected star). -/
theorem kern_lead_prime (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (m : (Fin 3 → F) → ℝ) (t : ℝ) (Y : (F → ℝ) → (Fin 3 → F) → ℝ) (c : ℝ)
    (L : ((Fin 3 → F) → ℝ) →ₗ[ℝ] ((Fin 3 → F) → ℝ))
    (hL : ∀ f g, EnvelopeSteps.ip m f (L g) = c * lFormY m t Y f g) (x y : Fin 3 → F) :
    EnvelopeSteps.kern m L x y =
      c * (Real.sqrt qF)⁻¹ * qF⁻¹ * (XiM m Y * foldStarT (F := F) t * (XiM m Y)ᵀ) x y := by
  have hk : EnvelopeSteps.kern m L x y =
      EnvelopeSteps.ip m (EnvelopeSteps.delta x) (L (EnvelopeSteps.delta y)) := by
    simp only [EnvelopeSteps.kern, EnvelopeSteps.ip, EnvelopeSteps.delta, ite_mul, one_mul,
      zero_mul, mul_ite,
      mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [hk, hL, lFormY_eq_starForm hF h3, starForm_delta]
  ring

/-- **The projected and the unprojected third arm** (OPS-L's finding 5): the leading forms differ
only in the arm `3`, by `(1 − t)(⟨(Y − Y')^* f, V₀^* g⟩ − ⟨V₀^* f, (Y − Y')^* g⟩)`; with
`Y = A₃`, `Y' = A₃°`, `Y − Y' = Π_{𝓗₁+𝓗₂}A₃` (`lem:actual-features`(c), `‖Π A₃‖ ≤ J_F q r`). -/
theorem lFormY_sub (m : (Fin 3 → F) → ℝ) (t : ℝ) (Y Y' : (F → ℝ) → (Fin 3 → F) → ℝ)
    (f g : (Fin 3 → F) → ℝ) :
    lFormY m t Y f g - lFormY m t Y' f g =
      (1 - t) * (uip (adj m Y f) (Wa m g) - uip (adj m Y' f) (Wa m g) -
        (uip (Wa m f) (adj m Y g) - uip (Wa m f) (adj m Y' g))) := by
  unfold lFormY
  simp only [Fin.sum_univ_three, aT, armY, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

omit [Field F] in
/-- `S^{*m}` is linear: `S^{*m} f = ∑_x f(x) S^{*m} δ_x`. -/
theorem adj_expand (m : (Fin 3 → F) → ℝ) (S : (F → ℝ) → (Fin 3 → F) → ℝ)
    (f : (Fin 3 → F) → ℝ) :
    adj m S f = fun z => ∑ x, f x * adj m S (EnvelopeSteps.delta x) z := by
  have hmip : ∀ (h : (Fin 3 → F) → ℝ) (x : Fin 3 → F),
      mip m h (EnvelopeSteps.delta x) = m x * h x := by
    intro h x
    simp only [mip, EnvelopeSteps.delta, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      ↓reduceIte]
  funext z
  simp only [adj, cen, hmip]
  unfold mip
  simp only [mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  · exact sum_congr rfl fun x _ => by ring
  · rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun s _ => by ring

omit [Field F] [DecidableEq F] in
theorem uip_expand {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → ℝ) (g : κ → ℝ)
    (a : ι → F → ℝ) (b : κ → F → ℝ) :
    uip (fun z => ∑ x, f x * a x z) (fun z => ∑ y, g y * b y z) =
      ∑ x, ∑ y, f x * g y * uip (a x) (b y) := by
  unfold uip
  simp only [sum_mul, mul_sum]
  rw [sum_congr rfl fun z _ => sum_comm, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun z _ => by ring

/-- **`lFormY` is bilinear**: `lFormY(f, g) = ∑_{x,y} f(x) g(y) lFormY(δ_x, δ_y)`. -/
theorem lFormY_expand (m : (Fin 3 → F) → ℝ) (t : ℝ) (Y : (F → ℝ) → (Fin 3 → F) → ℝ)
    (f g : (Fin 3 → F) → ℝ) :
    lFormY m t Y f g = ∑ x, ∑ y, f x * g y *
      lFormY m t Y (EnvelopeSteps.delta x) (EnvelopeSteps.delta y) := by
  have hW : ∀ h, Wa m h = adj m V0 h := fun h => rfl
  unfold lFormY
  simp only [hW]
  simp only [adj_expand m _ f, adj_expand m _ g, uip_expand, mul_sum, ← sum_sub_distrib]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun i _ => by ring

end Prime

/-! ## A fold block: the prime stars placed on the singleton sectors -/

section Block

variable {K : Type*} [Fintype K] {Fp : K → Type} [∀ j, Field (Fp j)] [∀ j, Fintype (Fp j)]
  [∀ j, DecidableEq (Fp j)] {O : Type*} [Fintype O] [DecidableEq O]

/-- **The kernel of the leading star of a fold block** (`prop:signed-bounds`(b): `L_{t,𝔅}` is
`L°_{t,p}` on the singleton sector `{p}`; OPS-L's `singForm` with `comp1`): if the block form is
`c ∑_j lFormY_j(comp_j f, comp_j g)` with linear placements `comp_j f = ∑_x f(x) C_j(x, ·)`, its
kernel is the star form `∑_j c_j Ξ̂_j 𝖥(Φ̂_j) Ξ̂_jᵀ` with `Ξ̂_j = C_j Ξ_j` (`Ξ_j = XiM`) and
`c_j = c r_j p_j⁻¹`: the per-block hypothesis `hLb` of `hdom_of_units` at a fold block, with
`Y_j = A₃°` for the paper's star (`Y_j = A₃` for PG's unprojected one). -/
theorem kern_block_lead (hF : ∀ j, ringChar (Fp j) ≠ 2)
    (h3 : ∀ j, Fintype.card (Fp j) % 4 = 3) (mP : ∀ j, (Fin 3 → Fp j) → ℝ)
    (Y : ∀ j, (Fp j → ℝ) → (Fin 3 → Fp j) → ℝ) (C : ∀ j, Matrix O (Fin 3 → Fp j) ℝ)
    (comp : ∀ j, (O → ℝ) → (Fin 3 → Fp j) → ℝ)
    (hcomp : ∀ j f a, comp j f a = ∑ x, f x * C j x a) (c : ℝ) (m : O → ℝ)
    (L : (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hL : ∀ f g, EnvelopeSteps.ip m f (L g) =
      c * ∑ j, lFormY (mP j) tlaw (Y j) (comp j f) (comp j g)) (x y : O) :
    EnvelopeSteps.kern m L x y = ∑ j, (c * (Real.sqrt (Fintype.card (Fp j)))⁻¹ *
      (Fintype.card (Fp j) : ℝ)⁻¹) * ((C j * XiM (mP j) (Y j)) * foldStar (F := Fp j) *
        (C j * XiM (mP j) (Y j))ᵀ) x y := by
  have hk : EnvelopeSteps.kern m L x y =
      EnvelopeSteps.ip m (EnvelopeSteps.delta x) (L (EnvelopeSteps.delta y)) := by
    simp only [EnvelopeSteps.kern, EnvelopeSteps.ip, EnvelopeSteps.delta, ite_mul, one_mul,
      zero_mul, mul_ite, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  have hc : ∀ j (z : O) a, comp j (EnvelopeSteps.delta z) a = C j z a := by
    intro j z a
    rw [hcomp]
    simp only [EnvelopeSteps.delta, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
      ↓reduceIte]
  rw [hk, hL, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [lFormY_expand]
  simp only [hc, lFormY_eq_starForm (hF j) (h3 j), starForm_delta, foldStarT_tlaw]
  set M := XiM (mP j) (Y j) * foldStar (F := Fp j) * (XiM (mP j) (Y j))ᵀ with hM
  have key : ∑ a, ∑ b, C j x a * C j y b * ((Real.sqrt (Fintype.card (Fp j)))⁻¹ *
      ((Fintype.card (Fp j) : ℝ)⁻¹ * M a b)) =
      (Real.sqrt (Fintype.card (Fp j)))⁻¹ * (Fintype.card (Fp j) : ℝ)⁻¹ *
        (C j * M * (C j)ᵀ) x y := by
    simp only [Matrix.mul_apply, transpose_apply, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring
  have e : C j * M * (C j)ᵀ = (C j * XiM (mP j) (Y j)) * foldStar (F := Fp j) *
      (C j * XiM (mP j) (Y j))ᵀ := by
    rw [hM, transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [key, e]
  ring

/-- **`kern_block_lead` in the shape of `starKer`** (`hLb` at a fold block): with the sector maps
`Ξ_j = p_j^{-1/2} C_j XiM_j` (whose label-`a` columns are the lifts of the orthonormal basis
`√p (δ_z − 1/p)` of `H₀`) and the coefficients `c_j = c r_j`, the kernel is
`∑_j c_j Ξ_j 𝖥(Φ̂_j) Ξ_jᵀ`. -/
theorem kern_block_lead_starSum (hF : ∀ j, ringChar (Fp j) ≠ 2)
    (h3 : ∀ j, Fintype.card (Fp j) % 4 = 3) (mP : ∀ j, (Fin 3 → Fp j) → ℝ)
    (Y : ∀ j, (Fp j → ℝ) → (Fin 3 → Fp j) → ℝ) (C : ∀ j, Matrix O (Fin 3 → Fp j) ℝ)
    (comp : ∀ j, (O → ℝ) → (Fin 3 → Fp j) → ℝ)
    (hcomp : ∀ j f a, comp j f a = ∑ x, f x * C j x a) (c : ℝ) (m : O → ℝ)
    (L : (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hL : ∀ f g, EnvelopeSteps.ip m f (L g) =
      c * ∑ j, lFormY (mP j) tlaw (Y j) (comp j f) (comp j g)) (x y : O) :
    EnvelopeSteps.kern m L x y = (∑ j, (c * (Real.sqrt (Fintype.card (Fp j)))⁻¹) •
      (((Real.sqrt (Fintype.card (Fp j)))⁻¹ • (C j * XiM (mP j) (Y j))) * foldStar (F := Fp j) *
        ((Real.sqrt (Fintype.card (Fp j)))⁻¹ • (C j * XiM (mP j) (Y j)))ᴴ)) x y := by
  rw [kern_block_lead hF h3 mP Y C comp hcomp c m L hL x y]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    conjTranspose_eq_transpose_of_trivial, transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
  refine sum_congr rfl fun j _ => ?_
  have hq : (0 : ℝ) < Fintype.card (Fp j) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card (Fp j)))⁻¹ * (Real.sqrt (Fintype.card (Fp j)))⁻¹ =
      (Fintype.card (Fp j) : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hq.le]
  rw [← hs]
  ring

/-- **The block form is bilinear**: `∑_j lFormY_j(comp_j φ, comp_j ψ) =
∑_{x,y} φ(x) ψ(y) ∑_j lFormY_j(comp_j δ_x, comp_j δ_y)` for linear placements `comp_j`. -/
theorem blockForm_expand (mP : ∀ j, (Fin 3 → Fp j) → ℝ) (t : ℝ)
    (Y : ∀ j, (Fp j → ℝ) → (Fin 3 → Fp j) → ℝ) (C : ∀ j, Matrix O (Fin 3 → Fp j) ℝ)
    (comp : ∀ j, (O → ℝ) → (Fin 3 → Fp j) → ℝ)
    (hcomp : ∀ j f a, comp j f a = ∑ x, f x * C j x a) (φ ψ : O → ℝ) :
    ∑ j, lFormY (mP j) t (Y j) (comp j φ) (comp j ψ) =
      ∑ x, ∑ y, φ x * ψ y * ∑ j, lFormY (mP j) t (Y j) (comp j (EnvelopeSteps.delta x))
        (comp j (EnvelopeSteps.delta y)) := by
  have hc : ∀ j (z : O) a, comp j (EnvelopeSteps.delta z) a = C j z a := by
    intro j z a
    rw [hcomp]
    simp only [EnvelopeSteps.delta, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
      ↓reduceIte]
  have per : ∀ j, lFormY (mP j) t (Y j) (comp j φ) (comp j ψ) =
      ∑ x, ∑ y, φ x * ψ y * lFormY (mP j) t (Y j) (comp j (EnvelopeSteps.delta x))
        (comp j (EnvelopeSteps.delta y)) := by
    intro j
    set Lab : (Fin 3 → Fp j) → (Fin 3 → Fp j) → ℝ := fun a b =>
      lFormY (mP j) t (Y j) (EnvelopeSteps.delta a) (EnvelopeSteps.delta b) with hLab
    have e1 : ∀ x y, lFormY (mP j) t (Y j) (comp j (EnvelopeSteps.delta x))
        (comp j (EnvelopeSteps.delta y)) = ∑ a, ∑ b, C j x a * C j y b * Lab a b := by
      intro x y
      rw [lFormY_expand]
      simp only [hc, hLab]
    rw [lFormY_expand]
    simp only [e1, hcomp, mul_sum, sum_mul]
    set G : (Fin 3 → Fp j) → (Fin 3 → Fp j) → O → O → ℝ := fun a b x y =>
      φ x * ψ y * (C j x a * C j y b * Lab a b) with hG
    calc ∑ a, ∑ b, ∑ y, ∑ x, φ x * C j x a * (ψ y * C j y b) * Lab a b
        = ∑ a, ∑ b, ∑ y, ∑ x, G a b x y :=
          sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun y _ =>
            sum_congr rfl fun x _ => by rw [hG]; ring
      _ = ∑ a, ∑ b, ∑ x, ∑ y, G a b x y :=
          sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_comm
      _ = ∑ a, ∑ x, ∑ b, ∑ y, G a b x y := sum_congr rfl fun a _ => sum_comm
      _ = ∑ x, ∑ a, ∑ b, ∑ y, G a b x y := sum_comm
      _ = ∑ x, ∑ a, ∑ y, ∑ b, G a b x y :=
          sum_congr rfl fun x _ => sum_congr rfl fun a _ => sum_comm
      _ = ∑ x, ∑ y, ∑ a, ∑ b, G a b x y := sum_congr rfl fun x _ => sum_comm
  simp only [per, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]

end Block

end Sarkozy.OpsFeature
