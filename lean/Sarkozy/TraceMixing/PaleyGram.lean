module

public import Sarkozy.TraceMixing.PaleyTriple

/-!
# Directed triples: the conditional operators and the Gram bound (`lem:paley-triple`(d))

`paper/sections/12_labellings.tex`, `lem:paley-triple`(d), over a finite field `F` with `q`
elements (`qF`), `q ≡ 3 (mod 4)`. Sums over
`H_F = {(x₀, x₁, x₂) : x₁ ∉ {x₀, x₂}, x₀ → x₂}` are `hfSum`, so `E_{ν_F} = hfSum/|H_F|` with
`|H_F| = q D` and `D = (q - 1)(q - 2)/2` (`fibreSize`, `hfSum_one`); the norm on `L²(F)` is
`‖h‖² = q⁻¹ ∑ h²`, and `H_0` is the space of functions with `∑ h = 0`.

* The coordinates are uniform (each `V_i` is an isometry): `hfSum_x0`, `hfSum_x1`, `hfSum_x2`.
* `count_shift`, `hfSum_shift`: each pair occurs as `(x₁, x₂)` exactly as often as `(x₀, x₁)`;
  hence `V_1^* V_2 = V_0^* V_1` and `V_2^* V_1 = V_1^* V_0`.
* The operators on `H_0`, in weak form `∑_{H_F} g(x_i) h(x_j) = D ∑_s g(s) (V_i^* V_j h)(s)`:
  `hfSum_x0_x2` (`V_0^* V_2 = (qP - I)/(q - 1)`, `opE2`; the paper's `(P - qI)/(1 - q)` with
  `q = 1/p`), `hfSum_x0_x1` and `hfSum_x1_x2` (`V_0^* V_1 = V_1^* V_2 = -((q - 2)I + qP)/((q - 1)(q - 2))`,
  `opE1`), `hfSum_x2_x0` (`V_2^* V_0 = -(qP + I)/(q - 1)`), `hfSum_x1_x0` and `hfSum_x2_x1`
  (`V_1^* V_0 = V_2^* V_1 = (-(q - 2)I + qP)/((q - 1)(q - 2))`).
* The exact norms on `H_0`: `sum_opE2_sq` (`‖V_0^* V_2 h‖ = ϱ ‖h‖`) and `sum_opE1_sq`
  (`‖V_0^* V_1 h‖ = ϱ₁ ‖h‖`), with `ϱ = √(q + 1)/(q - 1)` (`paleyRho`) and
  `ϱ₁ = √((q - 2)² + q)/((q - 1)(q - 2))` (`paleyRho1`), the paper's
  `(q/(1 - q))√(1 + q/(1 - 2q)²)` at `q = 1/p`.
* `paleyRho1_le`: `ϱ₁ ≤ ϱ' = (1 + ϱ)/(q - 2)` (`paleyRho'`); `paleyRho'_le`: `ϱ' ≤ ϱ` for `q ≥ 5`.
* `gram_bound`: for `h₁, h₂ ∈ H_0` and any `h₀`,
  `∑_{H_F} (h₀(x₀) + h₁(x₁) + h₂(x₂))² ≤ Γ D (∑ h₀² + ∑ h₁² + ∑ h₂²)`, `Γ = 1 + ϱ + ϱ'`
  (`paleyGamma`), that is `E_{ν_F}(V_0 h₀ + V_1 h₁ + V_2 h₂)² ≤ Γ (‖h₀‖² + ‖h₁‖² + ‖h₂‖²)`:
  the Gram operator `(V_i^* V_j)` has norm at most `Γ` on `H_0³`.

The functions are real-valued; the operators have real kernels, so the statements for complex
functions follow by taking real and imaginary parts.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer. -/
local notation "χ" => quadraticChar F

/-- `q = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

omit [DecidableEq F] in
/-- A field of odd characteristic has at least three elements. -/
theorem three_le_card_of_char_ne_two (hF : ringChar F ≠ 2) : (3 : ℝ) ≤ qF := by
  have h2 : 2 < Fintype.card F := by
    have h1 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have hodd := FiniteField.odd_card_of_char_ne_two hF
    rcases h1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hodd
      exact absurd hodd (by decide)
  exact_mod_cast h2

variable (F) in
/-- The fibre size `D = (q - 1)(q - 2)/2` of each coordinate of `H_F`. -/
noncomputable def fibreSize : ℝ := (qF - 1) * (qF - 2) / 2

omit [DecidableEq F] in
theorem fibreSize_pos (hF : ringChar F ≠ 2) : 0 < fibreSize F := by
  have := three_le_card_of_char_ne_two hF
  unfold fibreSize
  apply div_pos _ two_pos
  nlinarith

/-- The sum over `H_F`. -/
noncomputable def hfSum (G : F → F → F → ℝ) : ℝ :=
  ∑ s, ∑ a, ∑ b, if fibre0 s a b then G s a b else 0

theorem fibre_card (hF : ringChar F ≠ 2) (s : F) :
    ∑ a, ∑ b, (if fibre0 s a b then (1 : ℝ) else 0) = fibreSize F := by
  have := card_fibre0 hF s
  unfold fibreSize
  linarith

theorem fibreSum_eq (hF : ringChar F ≠ 2) (G : F → F → F → ℝ) (s : F) :
    ∑ a, ∑ b, (if fibre0 s a b then G s a b else 0) = fibreSize F * condExp0 G s := by
  have hD := (fibreSize_pos hF).ne'
  unfold condExp0
  rw [fibre_card hF s]
  field_simp

/-- `∑_{H_F} g(x₀) G(x) = D ∑_s g(s) E[G | x₀ = s]`. -/
theorem hfSum_mul_x0 (hF : ringChar F ≠ 2) (g : F → ℝ) (G : F → F → F → ℝ) :
    hfSum (fun s a b => g s * G s a b) = fibreSize F * ∑ s, g s * condExp0 G s := by
  unfold hfSum
  rw [Finset.mul_sum]
  refine sum_congr rfl fun s _ => ?_
  have e : ∑ a, ∑ b, (if fibre0 s a b then g s * G s a b else 0) =
      g s * ∑ a, ∑ b, (if fibre0 s a b then G s a b else 0) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [e, fibreSum_eq hF G s]
  ring

/-- **The coordinate `x₀` is uniform.** -/
theorem hfSum_x0 (hF : ringChar F ≠ 2) (g : F → ℝ) :
    hfSum (fun s _ _ => g s) = fibreSize F * ∑ s, g s := by
  have h := hfSum_mul_x0 hF g (fun _ _ _ => 1)
  simp only [mul_one] at h
  rw [h]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  have hD := (fibreSize_pos hF).ne'
  unfold condExp0
  rw [fibre_card hF s, div_self hD, mul_one]

/-- **Each pair `(u, v)` occurs as `(x₁, x₂)` exactly as often as `(x₀, x₁)`**: both counts
are `[u ≠ v] ((q - 1)/2 - [u → v])`. -/
theorem count_shift (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (u v : F) :
    (∑ s, if fibre0 s u v then (1 : ℝ) else 0) = ∑ b, if fibre0 u v b then (1 : ℝ) else 0 := by
  by_cases huv : u = v
  · rw [huv]
    simp [fibre0]
  have e1 (s : F) : (if fibre0 s u v then (1 : ℝ) else 0) =
      (if χ (v - s) = 1 then 1 else 0) - (if s = u then (if χ (v - u) = 1 then 1 else 0) else 0) := by
    unfold fibre0
    by_cases hs : s = u
    · rw [hs]
      simp
    · simp [hs, huv]
  have e2 (b : F) : (if fibre0 u v b then (1 : ℝ) else 0) =
      (if χ (b - u) = 1 then 1 else 0) - (if b = v then (if χ (v - u) = 1 then 1 else 0) else 0) := by
    unfold fibre0
    by_cases hb : b = v
    · rw [hb]
      simp
    · simp [hb, huv, Ne.symm hb]
  simp only [e1, e2, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, ite_true]
  congr 1
  rw [Finset.sum_boole, Finset.sum_boole]
  have h1 := (card_in hF h3 v).trans (card_out hF u).symm
  have h2 : ((univ.filter fun s => χ (v - s) = 1).card : ℤ) =
      ((univ.filter fun b => χ (b - u) = 1).card : ℤ) := by linarith
  exact_mod_cast h2

/-- **`∑_{H_F} g(x₁) h(x₂) = ∑_{H_F} g(x₀) h(x₁)`.** -/
theorem hfSum_shift (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ) :
    hfSum (fun _ a b => g a * h b) = hfSum (fun s a _ => g s * h a) := by
  unfold hfSum
  have hL : ∑ s, ∑ a, ∑ b, (if fibre0 s a b then g a * h b else 0) =
      ∑ a, ∑ b, g a * h b * ∑ s, (if fibre0 s a b then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun s _ => ?_
    split_ifs <;> ring
  have hR : ∑ s, ∑ a, ∑ b, (if fibre0 s a b then g s * h a else 0) =
      ∑ s, ∑ a, g s * h a * ∑ b, (if fibre0 s a b then (1 : ℝ) else 0) := by
    refine sum_congr rfl fun s _ => sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [hL, hR]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  rw [count_shift hF h3 u v]

/-- **The coordinate `x₁` is uniform.** -/
theorem hfSum_x1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g : F → ℝ) :
    hfSum (fun _ a _ => g a) = fibreSize F * ∑ s, g s := by
  have h := hfSum_shift hF h3 g (fun _ => 1)
  simp only [mul_one] at h
  rw [h, hfSum_x0 hF]

/-- **The coordinate `x₂` is uniform.** -/
theorem hfSum_x2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g : F → ℝ) :
    hfSum (fun _ _ b => g b) = fibreSize F * ∑ s, g s := by
  have h := hfSum_shift hF h3 (fun _ => 1) g
  simp only [one_mul] at h
  rw [h, hfSum_x1 hF h3]

/-- `|H_F| = q D`. -/
theorem hfSum_one (hF : ringChar F ≠ 2) :
    hfSum (F := F) (fun _ _ _ => (1 : ℝ)) = qF * fibreSize F := by
  rw [hfSum_x0 hF (fun _ => 1)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-- `V_0^* V_2` on `H_0`: `(q P - I)/(q - 1)`. -/
noncomputable def opE2 (h : F → ℝ) (s : F) : ℝ := (qF * paleyOp h s - h s) / (qF - 1)

/-- `V_0^* V_1 = V_1^* V_2` on `H_0`: `-((q - 2) I + q P)/((q - 1)(q - 2))`. -/
noncomputable def opE1 (h : F → ℝ) (s : F) : ℝ :=
  -((qF - 2) * h s + qF * paleyOp h s) / ((qF - 1) * (qF - 2))

/-- The closed form of `V_0^* V_1 = -(I + V_0^* V_2)/(q - 2)` on `H_0`. -/
theorem condExp0_x1_eq (hF : ringChar F ≠ 2) (h : F → ℝ) (hh : ∑ x, h x = 0) (s : F) :
    condExp0 (fun _ a _ => h a) s = opE1 h s := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  rw [condExp0_x1 hF h hh s, condExp0_x2 hF h hh s, opE1]
  field_simp
  ring

/-- **`V_0^* V_2 = (qP - I)/(q - 1)` on `H_0`**, weak form. -/
theorem hfSum_x0_x2 (hF : ringChar F ≠ 2) (g h : F → ℝ) (hh : ∑ s, h s = 0) :
    hfSum (fun s _ b => g s * h b) = fibreSize F * ∑ s, g s * opE2 h s := by
  rw [hfSum_mul_x0 hF g (fun _ _ b => h b)]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [condExp0_x2 hF h hh s, opE2]

/-- **`V_0^* V_1 = -((q - 2)I + qP)/((q - 1)(q - 2))` on `H_0`**, weak form. -/
theorem hfSum_x0_x1 (hF : ringChar F ≠ 2) (g h : F → ℝ) (hh : ∑ s, h s = 0) :
    hfSum (fun s a _ => g s * h a) = fibreSize F * ∑ s, g s * opE1 h s := by
  rw [hfSum_mul_x0 hF g (fun _ a _ => h a)]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [condExp0_x1_eq hF h hh s]

/-- **`V_1^* V_2 = V_0^* V_1` on `H_0`**, weak form. -/
theorem hfSum_x1_x2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    hfSum (fun _ a b => g a * h b) = fibreSize F * ∑ s, g s * opE1 h s := by
  rw [hfSum_shift hF h3 g h, hfSum_x0_x1 hF g h hh]

/-- **`V_2^* V_0 = -(qP + I)/(q - 1)` on `H_0`**, weak form. -/
theorem hfSum_x2_x0 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hg : ∑ s, g s = 0) :
    hfSum (fun s _ b => h s * g b) =
      fibreSize F * ∑ b, g b * (-(qF * paleyOp h b + h b) / (qF - 1)) := by
  rw [hfSum_x0_x2 hF h g hg]
  congr 1
  unfold opE2
  have hadj := paleyOp_adjoint h3 g h
  have hc : ∑ s, h s * g s = ∑ s, g s * h s := sum_congr rfl fun s _ => mul_comm _ _
  have e1 : ∑ s, h s * ((qF * paleyOp g s - g s) / (qF - 1)) =
      (qF * ∑ s, paleyOp g s * h s - ∑ s, h s * g s) / (qF - 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact sum_congr rfl fun s _ => by ring
  have e2 : ∑ b, g b * (-(qF * paleyOp h b + h b) / (qF - 1)) =
      (-(qF * ∑ b, g b * paleyOp h b) - ∑ b, g b * h b) / (qF - 1) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact sum_congr rfl fun s _ => by ring
  rw [e1, e2, hadj, hc]
  ring

/-- **`V_1^* V_0 = (-(q - 2)I + qP)/((q - 1)(q - 2))` on `H_0`**, weak form. -/
theorem hfSum_x1_x0 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hg : ∑ s, g s = 0) :
    hfSum (fun s a _ => h s * g a) =
      fibreSize F * ∑ a, g a * ((-((qF - 2) * h a) + qF * paleyOp h a) / ((qF - 1) * (qF - 2))) := by
  rw [hfSum_x0_x1 hF h g hg]
  congr 1
  unfold opE1
  have hadj := paleyOp_adjoint h3 g h
  have hc : ∑ s, h s * g s = ∑ s, g s * h s := sum_congr rfl fun s _ => mul_comm _ _
  have e1 : ∑ s, h s * (-((qF - 2) * g s + qF * paleyOp g s) / ((qF - 1) * (qF - 2))) =
      (-((qF - 2) * ∑ s, h s * g s) - qF * ∑ s, paleyOp g s * h s) / ((qF - 1) * (qF - 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_div]
    exact sum_congr rfl fun s _ => by ring
  have e2 : ∑ a, g a * ((-((qF - 2) * h a) + qF * paleyOp h a) / ((qF - 1) * (qF - 2))) =
      (-((qF - 2) * ∑ a, g a * h a) + qF * ∑ a, g a * paleyOp h a) / ((qF - 1) * (qF - 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      Finset.sum_div]
    exact sum_congr rfl fun s _ => by ring
  rw [e1, e2, hadj, hc]
  ring

/-- **`V_2^* V_1 = V_1^* V_0` on `H_0`**, weak form. -/
theorem hfSum_x2_x1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ)
    (hg : ∑ s, g s = 0) :
    hfSum (fun _ a b => h a * g b) =
      fibreSize F * ∑ a, g a * ((-((qF - 2) * h a) + qF * paleyOp h a) / ((qF - 1) * (qF - 2))) := by
  rw [hfSum_shift hF h3 h g, hfSum_x1_x0 hF h3 g h hg]

/-- `∑ (P h)² = q⁻¹ ∑ h²` on `H_0`. -/
theorem sum_paleyOp_sq (hF : ringChar F ≠ 2) (h : F → ℝ) (hh : ∑ s, h s = 0) :
    ∑ s, paleyOp h s ^ 2 = qF⁻¹ * ∑ s, h s ^ 2 := by
  have h1 := norm_paleyOp hF h
  have e : (qF⁻¹ * ∑ s, h s) ^ 2 = 0 := by
    rw [hh, mul_zero]
    ring
  rw [e, sub_zero] at h1
  exact mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)) h1

/-- `∑ (P h) h = 0` (`P^* = -P`). -/
theorem sum_paleyOp_mul_self (h3 : Fintype.card F % 4 = 3) (h : F → ℝ) :
    ∑ s, paleyOp h s * h s = 0 := by
  have h1 := paleyOp_adjoint h3 h h
  have e : ∑ s, h s * paleyOp h s = ∑ s, paleyOp h s * h s :=
    sum_congr rfl fun s _ => mul_comm _ _
  linarith

/-- **`‖V_0^* V_2 h‖² = ϱ² ‖h‖²` on `H_0`**, `ϱ² = (q + 1)/(q - 1)²`. -/
theorem sum_opE2_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    ∑ s, opE2 h s ^ 2 = (qF + 1) / (qF - 1) ^ 2 * ∑ s, h s ^ 2 := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hP2 := sum_paleyOp_sq hF h hh
  have hPh := sum_paleyOp_mul_self h3 h
  have e (s : F) : opE2 h s ^ 2 =
      (qF ^ 2 * paleyOp h s ^ 2 - 2 * qF * (paleyOp h s * h s) + h s ^ 2) / (qF - 1) ^ 2 := by
    unfold opE2
    rw [div_pow]
    ring
  simp only [e]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hP2, hPh]
  field_simp
  ring

/-- **`‖V_0^* V_1 h‖² = ϱ₁² ‖h‖²` on `H_0`**, `ϱ₁² = ((q - 2)² + q)/((q - 1)(q - 2))²`. -/
theorem sum_opE1_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    ∑ s, opE1 h s ^ 2 = ((qF - 2) ^ 2 + qF) / ((qF - 1) * (qF - 2)) ^ 2 * ∑ s, h s ^ 2 := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq0 : qF ≠ 0 := by linarith
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  have hP2 := sum_paleyOp_sq hF h hh
  have hPh := sum_paleyOp_mul_self h3 h
  have e (s : F) : opE1 h s ^ 2 =
      ((qF - 2) ^ 2 * h s ^ 2 + 2 * (qF - 2) * qF * (paleyOp h s * h s) +
        qF ^ 2 * paleyOp h s ^ 2) / ((qF - 1) * (qF - 2)) ^ 2 := by
    unfold opE1
    rw [div_pow]
    ring
  simp only [e]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, hP2, hPh]
  field_simp
  ring

variable (F) in
/-- `ϱ = √(q + 1)/(q - 1)`, the norm of `V_0^* V_2` on `H_0`. -/
noncomputable def paleyRho : ℝ := Real.sqrt (qF + 1) / (qF - 1)

variable (F) in
/-- `ϱ₁ = √((q - 2)² + q)/((q - 1)(q - 2))`, the norm of `V_0^* V_1 = V_1^* V_2` on `H_0`. -/
noncomputable def paleyRho1 : ℝ := Real.sqrt ((qF - 2) ^ 2 + qF) / ((qF - 1) * (qF - 2))

variable (F) in
/-- `ϱ' = (1 + ϱ)/(q - 2)`, the paper's `q(1 + ϱ)/(1 - 2q)` at `q = 1/p`. -/
noncomputable def paleyRho' : ℝ := (1 + paleyRho F) / (qF - 2)

variable (F) in
/-- `Γ = 1 + ϱ + ϱ'`. -/
noncomputable def paleyGamma : ℝ := 1 + paleyRho F + paleyRho' F

omit [DecidableEq F] in
theorem paleyRho_pos (hF : ringChar F ≠ 2) : 0 < paleyRho F := by
  have hq3 := three_le_card_of_char_ne_two hF
  unfold paleyRho
  exact div_pos (Real.sqrt_pos.mpr (by linarith)) (by linarith)

omit [DecidableEq F] in
theorem paleyRho1_pos (hF : ringChar F ≠ 2) : 0 < paleyRho1 F := by
  have hq3 := three_le_card_of_char_ne_two hF
  unfold paleyRho1
  exact div_pos (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (qF - 2)]))
    (mul_pos (by linarith) (by linarith))

omit [DecidableEq F] in
theorem paleyRho_sq : paleyRho F ^ 2 = (qF + 1) / (qF - 1) ^ 2 := by
  unfold paleyRho
  rw [div_pow, Real.sq_sqrt (by positivity)]

omit [DecidableEq F] in
theorem paleyRho1_sq : paleyRho1 F ^ 2 = ((qF - 2) ^ 2 + qF) / ((qF - 1) * (qF - 2)) ^ 2 := by
  unfold paleyRho1
  rw [div_pow, Real.sq_sqrt (by positivity)]

omit [DecidableEq F] in
/-- **`ϱ₁ ≤ ϱ'`.** -/
theorem paleyRho1_le (hF : ringChar F ≠ 2) : paleyRho1 F ≤ paleyRho' F := by
  have hq3 := three_le_card_of_char_ne_two hF
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hρ := (paleyRho_pos hF).le
  have hs : Real.sqrt ((qF - 2) ^ 2 + qF) ≤ qF - 1 := by
    have := Real.sqrt_le_sqrt (show (qF - 2) ^ 2 + qF ≤ (qF - 1) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  unfold paleyRho1 paleyRho'
  calc Real.sqrt ((qF - 2) ^ 2 + qF) / ((qF - 1) * (qF - 2))
      ≤ (qF - 1) / ((qF - 1) * (qF - 2)) :=
        div_le_div_of_nonneg_right hs (mul_nonneg (by linarith) (by linarith))
    _ = 1 / (qF - 2) := by rw [div_mul_eq_div_div, div_self hq1]
    _ ≤ (1 + paleyRho F) / (qF - 2) := div_le_div_of_nonneg_right (by linarith) (by linarith)

omit [Field F] [DecidableEq F] in
/-- **`ϱ' ≤ ϱ` for `q ≥ 5`** (the paper's `p ≥ 7`). -/
theorem paleyRho'_le (h5 : (5 : ℝ) ≤ qF) : paleyRho' F ≤ paleyRho F := by
  have hq1 : qF - 1 ≠ 0 := by linarith
  have hq2 : qF - 2 ≠ 0 := by linarith
  have hr : 2 ≤ Real.sqrt (qF + 1) := by
    have := Real.sqrt_le_sqrt (show (2 : ℝ) ^ 2 ≤ qF + 1 by nlinarith)
    rwa [Real.sqrt_sq (by norm_num)] at this
  unfold paleyRho' paleyRho
  set r := Real.sqrt (qF + 1)
  have e : r / (qF - 1) - (1 + r / (qF - 1)) / (qF - 2) =
      ((qF - 3) * r - (qF - 1)) / ((qF - 1) * (qF - 2)) := by
    field_simp
    ring
  have hnum : 0 ≤ ((qF - 3) * r - (qF - 1)) / ((qF - 1) * (qF - 2)) := by
    apply div_nonneg
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ qF - 3) (by linarith : (0 : ℝ) ≤ r - 2)]
    · exact mul_nonneg (by linarith) (by linarith)
  linarith

omit [Field F] [DecidableEq F] in
/-- `2 ∑ u v ≤ c (∑ u² + B)` when `∑ v² = c² B`, `c > 0`. -/
theorem two_sum_mul_le (u v : F → ℝ) {c B : ℝ} (hc : 0 < c) (hv : ∑ s, v s ^ 2 = c ^ 2 * B) :
    2 * ∑ s, u s * v s ≤ c * (∑ s, u s ^ 2 + B) := by
  have hpt (s : F) : c * (2 * (u s * v s)) ≤ c ^ 2 * u s ^ 2 + v s ^ 2 := by
    nlinarith [sq_nonneg (c * u s - v s)]
  have hsum : ∑ s, c * (2 * (u s * v s)) ≤ ∑ s, (c ^ 2 * u s ^ 2 + v s ^ 2) :=
    Finset.sum_le_sum fun s _ => hpt s
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hv] at hsum
  refine le_of_mul_le_mul_left ?_ hc
  linarith

/-- **The Gram bound** (`lem:paley-triple`(d)): for `h₁, h₂ ∈ H_0` and any `h₀`,
`∑_{H_F} (h₀(x₀) + h₁(x₁) + h₂(x₂))² ≤ Γ D (∑ h₀² + ∑ h₁² + ∑ h₂²)`, i.e.
`E_{ν_F}(V_0 h₀ + V_1 h₁ + V_2 h₂)² ≤ Γ (‖h₀‖² + ‖h₁‖² + ‖h₂‖²)` with `Γ = 1 + ϱ + ϱ'`. -/
theorem gram_bound (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h5 : 5 ≤ Fintype.card F)
    (h₀ h₁ h₂ : F → ℝ) (hh₁ : ∑ s, h₁ s = 0) (hh₂ : ∑ s, h₂ s = 0) :
    hfSum (fun s a b => (h₀ s + h₁ a + h₂ b) ^ 2) ≤
      paleyGamma F * (fibreSize F * (∑ s, h₀ s ^ 2 + ∑ s, h₁ s ^ 2 + ∑ s, h₂ s ^ 2)) := by
  have hq5 : (5 : ℝ) ≤ qF := by exact_mod_cast h5
  have hD := fibreSize_pos hF
  have hexp : hfSum (fun s a b => (h₀ s + h₁ a + h₂ b) ^ 2) =
      hfSum (fun s _ _ => h₀ s ^ 2) + hfSum (fun _ a _ => h₁ a ^ 2) +
        hfSum (fun _ _ b => h₂ b ^ 2) + 2 * hfSum (fun s a _ => h₀ s * h₁ a) +
        2 * hfSum (fun s _ b => h₀ s * h₂ b) + 2 * hfSum (fun _ a b => h₁ a * h₂ b) := by
    unfold hfSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun s _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [hexp, hfSum_x0_x1 hF h₀ h₁ hh₁, hfSum_x0_x2 hF h₀ h₂ hh₂, hfSum_x1_x2 hF h3 h₁ h₂ hh₂]
  simp only [hfSum_x0 hF, hfSum_x1 hF h3, hfSum_x2 hF h3]
  have hρ := paleyRho_pos hF
  have hρ₁ := paleyRho1_pos hF
  have c01 := two_sum_mul_le (B := ∑ s, h₁ s ^ 2) h₀ (opE1 h₁) hρ₁
    (by rw [sum_opE1_sq hF h3 h₁ hh₁, paleyRho1_sq])
  have c02 := two_sum_mul_le (B := ∑ s, h₂ s ^ 2) h₀ (opE2 h₂) hρ
    (by rw [sum_opE2_sq hF h3 h₂ hh₂, paleyRho_sq])
  have c12 := two_sum_mul_le (B := ∑ s, h₂ s ^ 2) h₁ (opE1 h₂) hρ₁
    (by rw [sum_opE1_sq hF h3 h₂ hh₂, paleyRho1_sq])
  have k1 := paleyRho1_le hF
  have k2 := paleyRho'_le hq5
  have hS0 : 0 ≤ ∑ s, h₀ s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have hS1 : 0 ≤ ∑ s, h₁ s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have hS2 : 0 ≤ ∑ s, h₂ s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have key : ∑ s, h₀ s ^ 2 + ∑ s, h₁ s ^ 2 + ∑ s, h₂ s ^ 2 + 2 * ∑ s, h₀ s * opE1 h₁ s +
      2 * ∑ s, h₀ s * opE2 h₂ s + 2 * ∑ s, h₁ s * opE1 h₂ s ≤
      paleyGamma F * (∑ s, h₀ s ^ 2 + ∑ s, h₁ s ^ 2 + ∑ s, h₂ s ^ 2) := by
    unfold paleyGamma
    nlinarith [mul_le_mul_of_nonneg_right k1 hS0, mul_le_mul_of_nonneg_right k1 hS1,
      mul_le_mul_of_nonneg_right k1 hS2, mul_le_mul_of_nonneg_right (k1.trans k2) hS1]
  have := mul_le_mul_of_nonneg_left key hD.le
  linarith

end Sarkozy.TraceMixing
