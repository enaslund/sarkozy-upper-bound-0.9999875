module

public import Sarkozy.MiddleRecords.ActualFeaturesA3
public import Sarkozy.TraceMixing.PaleyGram

/-!
# The leading kernels of the mirror pairing as feature stars (`lem:mirror`(c), (d))

`paper/sections/21_middle_records.tex`, `lem:mirror`(c), (d): on `L²(ν_F)`,
`L_p = A_⋆ V₀^* - V₀ A_⋆^*` and `L_{t,p} = A_t V₀^* - V₀ A_t^*`, with
`A_t = A₂ + t A₁ + (1 - t) A₃` (`A_⋆ = A₀`), `A₁ h = (P h)(x₂)`, `A₂ h = (P h)(x₁)` and `A₃` the
pair feature (`Sarkozy.MiddleRecords.A3op`).

* `Lt_eq_feat`: `L_{t,p} = K_t - K_t^⊤` as kernels, with `K_t = 𝖢 - t𝖡 + (1 - t)(𝖡𝖢 - q)`
  (`featKer`), and `Lt_zero`: `L_{0,p} = L_p`.
* `featKer_op`: `K_t` is the kernel of `A_t V₀^*` relative to `ν_F`: for every function `f` on
  halves, `E_{y ∼ ν_F} K_t(x, y) f(y) = (A_t V₀^* f)(x)`, where `V₀^* f = E[f | x₀ = ·]` (WP-S's
  `condExp0`), since `K_t(x, ·)` depends on `y` only through the uniform coordinate `y₀`.
* `Lt_form`: hence the bilinear form of `L_{t,p}` on `L²(ν_F)` is
  `⟨f, L_{t,p} g⟩ = ⟨f, A_t V₀^* g⟩ - ⟨A_t V₀^* f, g⟩`, i.e. `L_{t,p} = A_t V₀^* - V₀ A_t^*`.

`ν_F` is the uniform law on `H_F` (WP-S's `hfSum`, `fibre0`, of size `p · D`, `D = fibreSize F`).
With `TwoFeature` and the Gram data of `lem:paley-triple`(e) (in WP-S's
`Sarkozy.TraceMixing.PaleyFeatures*`, weak form), this is the remaining identification for the
norm of `lem:mirror`(c) (`Sarkozy.MiddleRecords.mirror_c`); the transport of those Gram data into
a `TwoFeature` bundle is not done.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-! ## The kernel identity -/

/-- **The kernel of `A_t V₀^*`**: `K_t = 𝖢 - t𝖡 + (1 - t)(𝖡𝖢 - q)`. -/
noncomputable def featKer (t : ℝ) : Ker F :=
  chanKer fun _ b c _ => c - t * b + (1 - t) * (b * c - qF⁻¹)

/-- **`lem:mirror`(c), (d): `L_{t,p} = K_t - K_t^⊤`.** -/
theorem Lt_eq_feat (h3 : Fintype.card F % 4 = 3) (t : ℝ) :
    (Lt t : Ker F) = featKer t - kerT (featKer t) := by
  rw [featKer, kerT_chanKer h3, Lt_eq']
  funext x y
  simp only [chanKer, Pi.sub_apply]
  ring

/-- `L_{0,p} = L_p`, the star part of `lem:mirror`(b). -/
theorem Lt_zero : (Lt 0 : Ker F) = Lp := by
  funext x y
  simp only [Lt, Lp, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The half `(x₀, x₁, x₂)`. -/
def half3 (x₀ x₁ x₂ : F) : Half F := ![x₀, x₁, x₂]

/-- `K_t(x, y) = χ(y₀ - x₁) - t χ(x₂ - y₀) + (1 - t)(χ(x₂ - y₀) χ(y₀ - x₁) - q)`: it depends on `y`
only through `y₀`. -/
theorem featKer_apply (t : ℝ) (x₀ x₁ x₂ y₀ y₁ y₂ : F) :
    featKer t (half3 x₀ x₁ x₂) (half3 y₀ y₁ y₂) =
      (χ (y₀ - x₁) : ℝ) - t * (χ (x₂ - y₀) : ℝ) +
        (1 - t) * ((χ (x₂ - y₀) : ℝ) * (χ (y₀ - x₁) : ℝ) - qF⁻¹) := by
  simp only [featKer, chanKer, chB, chC, half3]
  rfl

/-! ## `K_t` is the kernel of `A_t V₀^*` -/

/-- **The feature `A_t = A₂ + t A₁ + (1 - t) A₃`** on functions of one label. -/
noncomputable def Atop (t : ℝ) (h : F → ℝ) (x₁ x₂ : F) : ℝ :=
  paleyOp h x₁ + t * paleyOp h x₂ + (1 - t) * A3op h x₁ x₂

/-- **`K_t` is the kernel of `A_t V₀^*`**: `E_{y ∼ ν_F} K_t(x, y) f(y) = (A_t V₀^* f)(x)`. -/
theorem featKer_op (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (t : ℝ)
    (f : F → F → F → ℝ) (x₀ x₁ x₂ : F) :
    (qF * fibreSize F)⁻¹ *
        hfSum (fun y₀ y₁ y₂ => featKer t (half3 x₀ x₁ x₂) (half3 y₀ y₁ y₂) * f y₀ y₁ y₂) =
      Atop t (condExp0 f) x₁ x₂ := by
  simp only [featKer_apply]
  rw [hfSum_mul_x0 hF (fun s => (χ (s - x₁) : ℝ) - t * (χ (x₂ - s) : ℝ) +
    (1 - t) * ((χ (x₂ - s) : ℝ) * (χ (s - x₁) : ℝ) - qF⁻¹)) f]
  have hD := (fibreSize_pos hF).ne'
  have h0 : qF ≠ 0 := by
    have := Fintype.card_pos (α := F)
    positivity
  set h := condExp0 f with hh
  have e : ∀ s, ((χ (s - x₁) : ℝ) - t * (χ (x₂ - s) : ℝ) +
      (1 - t) * ((χ (x₂ - s) : ℝ) * (χ (s - x₁) : ℝ) - qF⁻¹)) * h s =
      (χ (s - x₁) : ℝ) * h s + t * ((χ (s - x₂) : ℝ) * h s) +
        (1 - t) * (-((χ (s - x₁) : ℝ) * (χ (s - x₂) : ℝ) * h s) - qF⁻¹ * h s) := by
    intro s
    rw [chi_swap h3 x₂ s]
    push_cast
    ring
  simp only [e, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_neg_distrib]
  unfold Atop A3op paleyOp
  field_simp

/-! ## The bilinear form -/

/-- The sum over `H_F × H_F`. -/
noncomputable def hfSum2 (G : F → F → F → F → F → F → ℝ) : ℝ :=
  hfSum fun x₀ x₁ x₂ => hfSum fun y₀ y₁ y₂ => G x₀ x₁ x₂ y₀ y₁ y₂

theorem hfSum_eq_prod (G : F → F → F → ℝ) :
    hfSum G = ∑ x : F × F × F, if fibre0 x.1 x.2.1 x.2.2 then G x.1 x.2.1 x.2.2 else 0 := by
  unfold hfSum
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type]

/-- **Fubini on `H_F × H_F`.** -/
theorem hfSum2_comm (G : F → F → F → F → F → F → ℝ) :
    hfSum2 G = hfSum2 (fun y₀ y₁ y₂ x₀ x₁ x₂ => G x₀ x₁ x₂ y₀ y₁ y₂) := by
  unfold hfSum2
  have key : ∀ (c : Prop) [Decidable c] (f : F × F × F → ℝ),
      (if c then ∑ y, f y else 0) = ∑ y, (if c then f y else 0) := by
    intro c _ f
    by_cases h : c
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, sum_const_zero]
  simp only [hfSum_eq_prod, key]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
  by_cases h1 : fibre0 x.1 x.2.1 x.2.2
  · by_cases h2 : fibre0 y.1 y.2.1 y.2.2
    · simp only [h1, h2, ↓reduceIte]
    · simp only [h1, h2, ↓reduceIte]
  · by_cases h2 : fibre0 y.1 y.2.1 y.2.2
    · simp only [h1, h2, ↓reduceIte]
    · simp only [h1, h2, ↓reduceIte]

/-- **`lem:mirror`(c), (d) on `L²(ν_F)`: `L_{t,p} = A_t V₀^* - V₀ A_t^*`**, as bilinear forms:
`E_{x,y ∼ ν_F} f(x) L_{t,p}(x, y) g(y) = ⟨f, A_t V₀^* g⟩ - ⟨A_t V₀^* f, g⟩`. -/
theorem Lt_form (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (t : ℝ)
    (f g : F → F → F → ℝ) :
    (qF * fibreSize F)⁻¹ ^ 2 * hfSum2 (fun x₀ x₁ x₂ y₀ y₁ y₂ =>
        f x₀ x₁ x₂ * Lt t (half3 x₀ x₁ x₂) (half3 y₀ y₁ y₂) * g y₀ y₁ y₂) =
      (qF * fibreSize F)⁻¹ * hfSum (fun x₀ x₁ x₂ => f x₀ x₁ x₂ * Atop t (condExp0 g) x₁ x₂) -
        (qF * fibreSize F)⁻¹ * hfSum (fun y₀ y₁ y₂ => g y₀ y₁ y₂ * Atop t (condExp0 f) y₁ y₂) := by
  set c := (qF * fibreSize F)⁻¹ with hc
  -- split `L_t = K_t - K_t^⊤`
  have hsplit : ∀ x₀ x₁ x₂ y₀ y₁ y₂ : F, f x₀ x₁ x₂ * Lt t (half3 x₀ x₁ x₂) (half3 y₀ y₁ y₂) *
      g y₀ y₁ y₂ =
      f x₀ x₁ x₂ * (featKer t (half3 x₀ x₁ x₂) (half3 y₀ y₁ y₂) * g y₀ y₁ y₂) -
        g y₀ y₁ y₂ * (featKer t (half3 y₀ y₁ y₂) (half3 x₀ x₁ x₂) * f x₀ x₁ x₂) := by
    intro x₀ x₁ x₂ y₀ y₁ y₂
    rw [Lt_eq_feat h3]
    simp only [Pi.sub_apply, kerT_apply]
    ring
  -- linearity of `hfSum`
  have hlin_sub : ∀ G G' : F → F → F → ℝ,
      hfSum (fun a b c => G a b c - G' a b c) = hfSum G - hfSum G' := by
    intro G G'
    unfold hfSum
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  have hlin_mul : ∀ (k : ℝ) (G : F → F → F → ℝ),
      hfSum (fun a b c => k * G a b c) = k * hfSum G := by
    intro k G
    unfold hfSum
    rw [mul_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  unfold hfSum2
  simp only [hsplit, hlin_sub, hlin_mul]
  -- the second term, by Fubini
  have hfub : hfSum (fun x₀ x₁ x₂ => hfSum (fun y₀ y₁ y₂ =>
      g y₀ y₁ y₂ * (featKer t (half3 y₀ y₁ y₂) (half3 x₀ x₁ x₂) * f x₀ x₁ x₂))) =
      hfSum (fun y₀ y₁ y₂ => g y₀ y₁ y₂ *
        hfSum (fun x₀ x₁ x₂ => featKer t (half3 y₀ y₁ y₂) (half3 x₀ x₁ x₂) * f x₀ x₁ x₂)) := by
    have := hfSum2_comm (fun x₀ x₁ x₂ y₀ y₁ y₂ =>
      g y₀ y₁ y₂ * (featKer t (half3 y₀ y₁ y₂) (half3 x₀ x₁ x₂) * f x₀ x₁ x₂))
    unfold hfSum2 at this
    rw [this]
    congr 1
    funext y₀ y₁ y₂
    rw [hlin_mul]
  rw [hfub]
  have hK1 : ∀ x₀ x₁ x₂ : F, hfSum (fun y₀ y₁ y₂ =>
      featKer t (half3 x₀ x₁ x₂) (half3 y₀ y₁ y₂) * g y₀ y₁ y₂) =
      c⁻¹ * Atop t (condExp0 g) x₁ x₂ := by
    intro x₀ x₁ x₂
    rw [← featKer_op hF h3 t g x₀ x₁ x₂, hc]
    have hD := (fibreSize_pos hF).ne'
    have h0 : qF ≠ 0 := by
      have := Fintype.card_pos (α := F)
      positivity
    field_simp
  have hK2 : ∀ y₀ y₁ y₂ : F, hfSum (fun x₀ x₁ x₂ =>
      featKer t (half3 y₀ y₁ y₂) (half3 x₀ x₁ x₂) * f x₀ x₁ x₂) =
      c⁻¹ * Atop t (condExp0 f) y₁ y₂ := by
    intro y₀ y₁ y₂
    rw [← featKer_op hF h3 t f y₀ y₁ y₂, hc]
    have hD := (fibreSize_pos hF).ne'
    have h0 : qF ≠ 0 := by
      have := Fintype.card_pos (α := F)
      positivity
    field_simp
  simp only [hK1, hK2]
  have hc0 : c ≠ 0 := by
    rw [hc]
    have hD := (fibreSize_pos hF).ne'
    have h0 : qF ≠ 0 := by
      have := Fintype.card_pos (α := F)
      positivity
    exact inv_ne_zero (mul_ne_zero h0 hD)
  have e1 : hfSum (fun x₀ x₁ x₂ => f x₀ x₁ x₂ * (c⁻¹ * Atop t (condExp0 g) x₁ x₂)) =
      c⁻¹ * hfSum (fun x₀ x₁ x₂ => f x₀ x₁ x₂ * Atop t (condExp0 g) x₁ x₂) := by
    rw [← hlin_mul]
    congr 1
    funext a b d
    ring
  have e2 : hfSum (fun y₀ y₁ y₂ => g y₀ y₁ y₂ * (c⁻¹ * Atop t (condExp0 f) y₁ y₂)) =
      c⁻¹ * hfSum (fun y₀ y₁ y₂ => g y₀ y₁ y₂ * Atop t (condExp0 f) y₁ y₂) := by
    rw [← hlin_mul]
    congr 1
    funext a b d
    ring
  rw [e1, e2]
  field_simp

end Sarkozy.MiddleRecords
