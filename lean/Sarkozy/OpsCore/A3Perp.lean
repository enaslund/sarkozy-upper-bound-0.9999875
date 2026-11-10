module

public import Sarkozy.OpsCore.A3Chart

@[expose] public section

/-!
# The projected arm `A₃°` at a prime, explicitly (OPS-L)

`paper/sections/21_middle_records.tex`, `lem:actual-features`(c), (e); `eq:signed-star`. The chart
of OPS-F uses `A₃° = A₃ - Π_{𝓗₁+𝓗₂} A₃` (its fourth coordinate lies in `𝒦₁₂`). Here the projection
is computed in closed form, so that `A3Chart.lead_chart_change` holds unconditionally.

On `H₀` every operator in sight is in the algebra of `I` and the Paley operator `P`, with
`P^* = -P` and `P² = -q I` (`paleyOp_paleyOp`). The normal equations of the projection are
`u + T v = V^*_{1,m} A₃ h` and `T^* u + v = V^*_{2,m} A₃ h`, with
`T = V^*_{1,m} V₂ = -(I + μpP)/(p - 1)`. Their solution is `u = α h + β P h`,
`v = α h - β P h`, where `α = (μ² - 1)/(p(p - 2 - μ²))` and `β = μ(p - 3)/(p(p - 2 - μ²))`
(`alphaA`, `betaA`).

* `eq_w1`, `eq_w2`: the two normal equations, pointwise;
* **`A3_perp`**: `A₃ h - (u(x₁) + v(x₂))` is orthogonal in `L²(m₀)` to every `u'(x₁) + v'(x₂)`
  (`v'` of mean zero), i.e. `A₃° h := A₃ h - G h` lies in `𝒦₁₂` (pair functions orthogonal to
  `𝓗₁ + 𝓗₂` and the constants);
* `GA` (the projection as a kernel map on half triples, `GA_kernel`);
* **`lead_chart_change_proj`**: `|⟨f, L^m_t g⟩ - ⟨f, L°_t g⟩| ≤ |1 - t| J_F q r
  (‖V₀^{*m} g‖ ‖f‖ + ‖V₀^{*m} f‖ ‖g‖)` at `m = m₀`, with `L°_t` the leading form whose third arm is
  `A₃°` — no hypotheses beyond `p ≡ 3 (mod 4)`, `p ≥ 7`.
-/

open Finset

namespace Sarkozy.OpsCore

open Sarkozy.MiddleRecords Sarkozy.TraceMixing Sarkozy.PrimeGram Sarkozy.Envelopes

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-! ### The Paley algebra on `H₀` -/

theorem paleyOp_lin (c₁ c₂ : ℝ) (f g : F → ℝ) (a : F) :
    paleyOp (fun b => c₁ * f b + c₂ * g b) a = c₁ * paleyOp f a + c₂ * paleyOp g a := by
  unfold paleyOp
  simp only [mul_add, sum_add_distrib, mul_sum]
  congr 1 <;> exact sum_congr rfl fun t _ => by ring

theorem sum_paleyOp_eq_zero (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ) :
    ∑ s, paleyOp h s = 0 := by
  have e := paleyOp_adjoint h3 h (fun _ => 1)
  simp only [mul_one, paleyOp_const hF, mul_zero, sum_const_zero, neg_zero] at e
  exact e

/-- **`P² = -q I` on `H₀`**. -/
theorem paleyOp_paleyOp (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (s : F) : paleyOp (paleyOp h) s = -(qF⁻¹ * h s) := by
  have key : ∀ u, ∑ t, (χ (t - s) : ℝ) * (χ (u - t) : ℝ) = 1 - (if s = u then qF else 0) := by
    intro u
    have e : ∀ t, (χ (t - s) : ℝ) * (χ (u - t) : ℝ) = -((χ (t - s) : ℝ) * (χ (t - u) : ℝ)) := by
      intro t
      have hs : (χ (u - t) : ℝ) = -(χ (t - u) : ℝ) := by exact_mod_cast chi_swap h3 u t
      rw [hs]; ring
    simp only [e, sum_neg_distrib]
    have hc := sum_chi_mul_chi hF s u
    by_cases hsu : s = u
    · simp only [hsu, ↓reduceIte] at hc ⊢
      have : (∑ t, (χ (t - u) : ℝ) * (χ (t - u) : ℝ)) = qF - 1 := by exact_mod_cast hc
      rw [this]; ring
    · simp only [hsu, ↓reduceIte] at hc ⊢
      have : (∑ t, (χ (t - s) : ℝ) * (χ (t - u) : ℝ)) = -1 := by exact_mod_cast hc
      rw [this]; ring
  have h0 : qF ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e1 : paleyOp (paleyOp h) s =
      qF⁻¹ * qF⁻¹ * ∑ u, h u * ∑ t, (χ (t - s) : ℝ) * (χ (u - t) : ℝ) := by
    unfold paleyOp
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => sum_congr rfl fun t _ => by ring
  rw [e1]
  simp only [key, mul_sub, mul_one, sum_sub_distrib, hh, mul_ite, mul_zero, sum_ite_eq,
    mem_univ, ↓reduceIte]
  field_simp
  ring

/-! ### The projection -/

/-- `α = (μ² - 1)/(p(p - 2 - μ²))`. -/
noncomputable def alphaA : ℝ := (muF (F := F) ^ 2 - 1) / (qF * (qF - 2 - muF (F := F) ^ 2))

/-- `β = μ(p - 3)/(p(p - 2 - μ²))`. -/
noncomputable def betaA : ℝ := muF (F := F) * (qF - 3) / (qF * (qF - 2 - muF (F := F) ^ 2))

/-- The `𝓗₁` part of the projection: `u = α h + β P h`. -/
noncomputable def uA (h : F → ℝ) (a : F) : ℝ := alphaA (F := F) * h a + betaA (F := F) * paleyOp h a

/-- The `𝓗₂` part of the projection: `v = α h - β P h`. -/
noncomputable def vA (h : F → ℝ) (b : F) : ℝ := alphaA (F := F) * h b - betaA (F := F) * paleyOp h b

omit [Field F] [DecidableEq F] in
theorem den_pos (h7 : 7 ≤ qF) : 0 < qF - 2 - muF (F := F) ^ 2 := by
  have h4 : 3 ≤ qF - 4 := by linarith
  have hμ0 : 0 ≤ muF (F := F) := by unfold muF; positivity
  have hμ : muF (F := F) ≤ 2 / 3 := by
    unfold muF; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  nlinarith

theorem sum_vA (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) : ∑ b, vA h b = 0 := by
  unfold vA
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hh, sum_paleyOp_eq_zero hF h3]
  ring

theorem paleyOp_vA (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (a : F) :
    paleyOp (vA h) a = alphaA (F := F) * paleyOp h a + betaA (F := F) * (qF⁻¹ * h a) := by
  have e : vA h = fun b => alphaA (F := F) * h b + (-betaA (F := F)) * paleyOp h b := by
    funext b; unfold vA; ring
  rw [e, paleyOp_lin, paleyOp_paleyOp hF h3 h hh]
  ring

theorem paleyOp_uA (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (a : F) :
    paleyOp (uA h) a = alphaA (F := F) * paleyOp h a - betaA (F := F) * (qF⁻¹ * h a) := by
  have e : uA h = fun b => alphaA (F := F) * h b + betaA (F := F) * paleyOp h b := rfl
  rw [e, paleyOp_lin, paleyOp_paleyOp hF h3 h hh]
  ring

/-- **The first normal equation**: `V^*_{1,m} A₃ h = u + T v` pointwise. -/
theorem eq_w1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (a : F) : w1 h a = uA h a + condOp m12 (vA h) a := by
  rw [V1m_V2 hF h3 h7 (vA h) (sum_vA hF h3 h hh), paleyOp_vA hF h3 h hh]
  have hd := den_pos (F := F) h7
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  unfold w1 uA vA alphaA betaA
  field_simp
  ring

/-- **The second normal equation**: `V^*_{2,m} A₃ h = v + T^* u` pointwise, with
`T^* u = -(u - μpPu)/(p - 1)`. -/
theorem eq_w2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (b : F) :
    w2 h b = vA h b + -(uA h b - muF (F := F) * qF * paleyOp (uA h) b) / (qF - 1) := by
  rw [paleyOp_uA hF h3 h hh]
  have hd := den_pos (F := F) h7
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  unfold w2 uA vA alphaA betaA
  field_simp
  ring

/-- `⟨u(x₁), v'(x₂)⟩ = ⟨T^* u, v'⟩` (`v'` of mean zero; `P^* = -P`). -/
theorem sum_mul_condOp (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (u v' : F → ℝ) (hv' : ∑ b, v' b = 0) :
    ∑ a, u a * condOp m12 v' a =
      ∑ b, v' b * (-(u b - muF (F := F) * qF * paleyOp u b) / (qF - 1)) := by
  simp only [V1m_V2 hF h3 h7 v' hv']
  have hadj := paleyOp_adjoint h3 u v'
  have e1 : ∑ a, u a * (-(v' a + muF (F := F) * qF * paleyOp v' a) / (qF - 1)) =
      -(∑ a, u a * v' a + muF (F := F) * qF * ∑ a, u a * paleyOp v' a) / (qF - 1) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_neg_distrib, sum_div]
    exact sum_congr rfl fun a _ => by ring
  have e2 : ∑ b, v' b * (-(u b - muF (F := F) * qF * paleyOp u b) / (qF - 1)) =
      -(∑ b, u b * v' b - muF (F := F) * qF * ∑ b, paleyOp u b * v' b) / (qF - 1) := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_neg_distrib, sum_div]
    exact sum_congr rfl fun b _ => by ring
  rw [e1, e2, hadj]
  ring

/-- **`A₃° h = A₃ h - (u(x₁) + v(x₂))` is orthogonal to `𝓗₁ + 𝓗₂` and the constants**: for
`h ∈ H₀`, every `u'` and every mean-zero `v'`, `⟨A₃ h - G h, u'(x₁) + v'(x₂)⟩_{m₀} = 0`. -/
theorem A3_perp (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (u' v' : F → ℝ) (hv' : ∑ b, v' b = 0) :
    ip12 (fun a b => A3op h a b - (uA h a + vA h b)) (fun a b => u' a + v' b) = 0 := by
  set u := uA h
  set v := vA h
  -- expand the inner product into the four pair sums
  have hsplit : ip12 (fun a b => A3op h a b - (u a + v b)) (fun a b => u' a + v' b) =
      (ip12 (A3op h) (fun a _ => u' a) + ip12 (A3op h) (fun _ b => v' b)) -
        (∑ a, ∑ b, m12 a b * u a * u' a + ∑ a, ∑ b, m12 a b * v b * u' a +
          ∑ a, ∑ b, m12 a b * u a * v' b + ∑ a, ∑ b, m12 a b * v b * v' b) := by
    unfold ip12
    simp only [← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have hq : ∀ a, ∑ b, m12 a b = qF⁻¹ := fun a => by rw [sum_m12_right hF h3 h7 a, one_div]
  have hq' : ∀ b, ∑ a, m12 a b = qF⁻¹ := fun b => by rw [sum_m12_left hF h3 h7 b, one_div]
  have s1 : ∑ a, ∑ b, m12 a b * u a * u' a = qF⁻¹ * ∑ a, u a * u' a := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [← hq a, sum_mul]
    exact sum_congr rfl fun b _ => by ring
  have s4 : ∑ a, ∑ b, m12 a b * v b * v' b = qF⁻¹ * ∑ b, v b * v' b := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [← hq' b, sum_mul]
    exact sum_congr rfl fun a _ => by ring
  have h0 : qF ≠ 0 := by intro h; linarith
  have s2 : ∑ a, ∑ b, m12 a b * v b * u' a = qF⁻¹ * ∑ a, u' a * condOp m12 v a := by
    unfold condOp
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    field_simp
  have s3 : ∑ a, ∑ b, m12 a b * u a * v' b = qF⁻¹ * ∑ a, u a * condOp m12 v' a := by
    unfold condOp
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    field_simp
  rw [hsplit, ip12_A3_left hF h3 h7 h u' hh, ip12_A3_right hF h3 h7 h v' hh, s1, s2, s3, s4,
    sum_mul_condOp hF h3 h7 u v' hv']
  have e1 : ∀ a, w1 h a = u a + condOp m12 v a := eq_w1 hF h3 h7 h hh
  have e2 : ∀ b, w2 h b = v b + -(u b - muF (F := F) * qF * paleyOp u b) / (qF - 1) :=
    eq_w2 hF h3 h7 h hh
  simp only [e1, e2]
  have r1 : ∑ a, u' a * (u a + condOp m12 v a) =
      ∑ a, u a * u' a + ∑ a, u' a * condOp m12 v a := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => by ring
  have r2 : ∑ b, v' b * (v b + -(u b - muF (F := F) * qF * paleyOp u b) / (qF - 1)) =
      ∑ b, v b * v' b + ∑ b, v' b * (-(u b - muF (F := F) * qF * paleyOp u b) / (qF - 1)) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun b _ => by ring
  rw [r1, r2]
  ring

/-- **The projection as a kernel map on half triples**: `G h (x) = u_h(x₁) + v_h(x₂)`. -/
noncomputable def GA (h : F → ℝ) (x : Fin 3 → F) : ℝ := uA h (x 1) + vA h (x 2)

theorem GA_kernel : IsKernel (GA (F := F)) := by
  intro h x
  have d1 : ∀ a, ∑ s, h s * delta s a = h a := by
    intro a
    simp only [delta, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
  have k1 := paleyOp_kernel h (x 1)
  have k2 := paleyOp_kernel h (x 2)
  unfold GA uA vA
  have e : ∀ s, h s * (alphaA (F := F) * delta s (x 1) + betaA (F := F) * paleyOp (delta s) (x 1) +
      (alphaA (F := F) * delta s (x 2) - betaA (F := F) * paleyOp (delta s) (x 2))) =
      alphaA (F := F) * (h s * delta s (x 1)) + betaA (F := F) * (h s * paleyOp (delta s) (x 1)) +
        alphaA (F := F) * (h s * delta s (x 2)) -
          betaA (F := F) * (h s * paleyOp (delta s) (x 2)) := fun s => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, d1, ← k1, ← k2]
  ring

/-- **`L^m_t` against `L°_t` at a prime, unconditionally**: with `A₃° = A₃ - GA` (in `𝒦₁₂` by
`A3_perp`), `|⟨f, L^m_t g⟩ - ⟨f, L°_t g⟩| ≤ |1 - t| J_F q r (‖V₀^{*m} g‖ ‖f‖ + ‖V₀^{*m} f‖ ‖g‖)`
in `L²(m₀)`. -/
theorem lead_chart_change_proj (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (t : ℝ) (f g : (Fin 3 → F) → ℝ) :
    |lForm m0W t f g - lFormC m0W t GA f g| ≤
      |1 - t| * jFqr (F := F) (Real.sqrt (rho01Sq (F := F))) *
        (Real.sqrt (uip (Wa m0W g) (Wa m0W g)) * Real.sqrt (mip m0W f f) +
          Real.sqrt (uip (Wa m0W f) (Wa m0W f)) * Real.sqrt (mip m0W g g)) :=
  lead_chart_change hF h3 h7 t GA_kernel uA vA (fun _ _ => rfl)
    (fun h hh => sum_vA hF h3 h hh)
    (fun h hh => A3_perp hF h3 h7 h hh (uA h) (vA h) (sum_vA hF h3 h hh)) f g

end Sarkozy.OpsCore
