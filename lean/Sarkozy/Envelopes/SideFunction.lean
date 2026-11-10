module

public import Sarkozy.Envelopes.DirectGram

@[expose] public section

/-!
# The side function (`def:side-function`)

`paper/sections/24_matching_mean.tex`, `def:side-function`: the arithmetic definition of the
auxiliary sides `d^aux_L(X)`, `d^aux_R(X)`, transcribed as functions of `(q, r)` (and of the
number `n_X` of primes, a parameter here), with the paper's fixed parameters.

**Checked.**
* `sideBars`: the stated `(b̄, d̄, f̄) = (.6426372, .5181074, .1607446)` are exactly
  `∑ β w_{βδ}`, `∑ δ w_{βδ}`, `∑ βδ w_{βδ}` of the weights `(5803723, 2409463, 1786814, 0)/10⁷`;
* `sAux_bounds`: at `τ = 31/32`, `u = (-b̄, 1, b̄)`, `v = (-1, -d̄, -d̄)`,
  `2.0778741 < s(τ) < 2.0778742`, `2.0129405 < sτ < 2.0129406` and `2.1449023 < s/τ < 2.1449024`,
  as stated after the definition (`s(31/32) = 2.0778741…`, `sτ = 2.0129405…`, `s/τ = 2.1449023…`).

The evaluation conventions of the definition (the nondecreasing `(q, r)` form, `r_X = 1/⌊√X⌋`,
`n_X = ⌊L_loc/log₋ X⌋`) and the 33 values and gates of `cert:record:matching` are not formalized.
-/

namespace Sarkozy.Envelopes

/-! ### The fixed parameters -/

/-- `(w_{++}, w_{+-}, w_{-+}, w_{--}) = (5803723, 2409463, 1786814, 0)/10⁷`. -/
def wPP : ℚ := 5803723 / 10 ^ 7
/-- `w_{+-}`. -/
def wPM : ℚ := 2409463 / 10 ^ 7
/-- `w_{-+}`. -/
def wMP : ℚ := 1786814 / 10 ^ 7
/-- `w_{--}`. -/
def wMM : ℚ := 0

/-- `b̄ = .6426372`. -/
def bBar : ℚ := 6426372 / 10 ^ 7
/-- `d̄ = .5181074`. -/
def dBar : ℚ := 5181074 / 10 ^ 7
/-- `f̄ = .1607446`. -/
def fBar : ℚ := 1607446 / 10 ^ 7

/-- **The bars are the stated sums**: `b̄ = ∑ β w_{βδ}`, `d̄ = ∑ δ w_{βδ}`,
`f̄ = ∑ βδ w_{βδ}`, and the weights sum to `1`. -/
theorem sideBars :
    bBar = wPP + wPM - wMP - wMM ∧ dBar = wPP - wPM + wMP - wMM ∧
      fBar = wPP - wPM - wMP + wMM ∧ wPP + wPM + wMP + wMM = 1 := by
  simp only [bBar, dBar, fBar, wPP, wPM, wMP, wMM]
  norm_num

/-- `τ = 31/32`. -/
noncomputable def tauSide : ℝ := 31 / 32

/-- `u = (-b̄, 1, b̄)`. -/
noncomputable def uSide : Fin 3 → ℝ := ![-(bBar : ℝ), 1, bBar]

/-- `v = (-1, -d̄, -d̄)`. -/
noncomputable def vSide : Fin 3 → ℝ := ![-1, -(dBar : ℝ), -(dBar : ℝ)]

/-- `s(τ) = s(τ; u, v)` of `lem:record:direct-gram`. -/
noncomputable def sAux : ℝ := sSide tauSide uSide vSide

/-! ### The coefficients, as functions of `(q, r)` -/

section Coefficients

variable (q r : ℝ)

/-- `Z = (1-q)(1-2q)`. -/
noncomputable def sfZ : ℝ := (1 - q) * (1 - 2 * q)
/-- `h₀ = 1 - 14q`. -/
noncomputable def sfh0 : ℝ := 1 - 14 * q
/-- `e₀ = 2q/((1-3q)(1-4q))`. -/
noncomputable def sfe0 : ℝ := 2 * q / ((1 - 3 * q) * (1 - 4 * q))
/-- `γ = (1 + q(1+2r)/(1-2q))^{1/2}`. -/
noncomputable def sfGamma : ℝ := Real.sqrt (1 + q * (1 + 2 * r) / (1 - 2 * q))
/-- `c_lead = γ(‖u‖₂ + ‖v‖₂)`. -/
noncomputable def sfClead : ℝ := sfGamma q r * (Real.sqrt (nsq uSide) + Real.sqrt (nsq vSide))
/-- `F_frame`. -/
noncomputable def sfFframe : ℝ :=
  (2 + |(bBar : ℝ) + 1|) / (1 - q) + |1 - (dBar : ℝ)| * q / ((1 - q) * (1 - 2 * q)) +
    2 * |(bBar : ℝ) - dBar| * q ^ 2 / ((1 - q) * (1 - 2 * q)) +
    |2 - (bBar : ℝ) + dBar| * r / (1 - q)
/-- `ζ_{++}`, `ζ_{+-}`, `ζ_{-+}`, `ζ_{--}`. -/
noncomputable def sfZetaPP : ℝ := 6 * q ^ 2 / ((1 - 4 * q) * (1 - 5 * q))
/-- `ζ_{+-}`. -/
noncomputable def sfZetaPM : ℝ := 4 * q / ((1 - 4 * q) * (1 - 5 * q))
/-- `ζ_{-+}`. -/
noncomputable def sfZetaMP : ℝ := 4 * q / ((1 - 4 * q) * (1 - 5 * q) * (1 - 7 * q))
/-- `ζ_{--}`. -/
noncomputable def sfZetaMM : ℝ := 8 * q / ((1 - 4 * q) * (1 - 5 * q) * (1 - 7 * q))
/-- `C_old = 19/(Z h₀)`. -/
noncomputable def sfCold : ℝ := 19 / (sfZ q * sfh0 q)
/-- `C_ns = 2|b̄| + 1 + 2|d̄| + 4|f̄|`. -/
noncomputable def sfCns : ℝ := 2 * |(bBar : ℝ)| + 1 + 2 * |(dBar : ℝ)| + 4 * |(fBar : ℝ)|
/-- `n_* = (1 + 8r + (18/Z + 144)q)/h₀`. -/
noncomputable def sfNstar : ℝ := (1 + 8 * r + (18 / sfZ q + 144) * q) / sfh0 q
/-- `C_z = (n_*/q) ∑ w_{βδ} ζ_{βδ}`. -/
noncomputable def sfCz : ℝ :=
  sfNstar q r / q * ((wPP : ℝ) * sfZetaPP q + wPM * sfZetaPM q + wMP * sfZetaMP q +
    wMM * sfZetaMM q)
/-- `C_new = (2C_ns/Z + 144 + |b̄ - d̄|)/h₀ + C_z`. -/
noncomputable def sfCnew : ℝ :=
  (2 * sfCns / sfZ q + 144 + |(bBar : ℝ) - dBar|) / sfh0 q + sfCz q r
/-- `k_raw = r c_lead/h₀ + q C_new`. -/
noncomputable def sfKraw : ℝ := r * sfClead q r / sfh0 q + q * sfCnew q r
/-- `η₁ = (4w_{++} + 6w_{+-} + 4w_{-+} + 8w_{--}) q/h₀`. -/
noncomputable def sfEta1 : ℝ :=
  (4 * (wPP : ℝ) + 6 * wPM + 4 * wMP + 8 * wMM) * q / sfh0 q
/-- `ρ₁ = (k_raw + η₁²)/(1 - η₁)`. -/
noncomputable def sfRho1 : ℝ := (sfKraw q r + sfEta1 q ^ 2) / (1 - sfEta1 q)
/-- `η_* = (e₀ + η₁)/(1 - η₁)`. -/
noncomputable def sfEtaStar : ℝ := (sfe0 q + sfEta1 q) / (1 - sfEta1 q)
/-- `φ₂ = η_*/(1 - ρ₁)`. -/
noncomputable def sfPhi2 : ℝ := sfEtaStar q / (1 - sfRho1 q r)
/-- `K_∞ = 4/(h₀^{1/2}(1 - η₁))`. -/
noncomputable def sfKinf : ℝ := 4 / (Real.sqrt (sfh0 q) * (1 - sfEta1 q))
/-- `φ_∞ = η_* + K_∞ φ₂`. -/
noncomputable def sfPhiInf : ℝ := sfEtaStar q + sfKinf q * sfPhi2 q r
/-- `C_rep = (2φ_∞/q)(k_raw + 14q/h₀)`. -/
noncomputable def sfCrep : ℝ := 2 * sfPhiInf q r / q * (sfKraw q r + 14 * q / sfh0 q)
/-- `C' = C_new + C_rep`. -/
noncomputable def sfCprime : ℝ := sfCnew q r + sfCrep q r
/-- `c_com = r F_frame/h₀ + r(C_old + C' + 2e₀²/q)`. -/
noncomputable def sfCcom : ℝ :=
  r * sfFframe q r / sfh0 q + r * (sfCold q + sfCprime q r + 2 * sfe0 q ^ 2 / q)
/-- `d^m_L = (γ s(τ) τ/h₀ + c_com)/(1 - e₀)`. -/
noncomputable def sfDmL : ℝ :=
  (sfGamma q r * sAux * tauSide / sfh0 q + sfCcom q r) / (1 - sfe0 q)
/-- `d^m_R = (γ s(τ) τ⁻¹/h₀ + c_com)/(1 - e₀)`. -/
noncomputable def sfDmR : ℝ :=
  (sfGamma q r * sAux * tauSide⁻¹ / sfh0 q + sfCcom q r) / (1 - sfe0 q)
/-- `k₀ = (2γ/h₀ + r(C_old + 14/h₀ + 2e₀/q + e₀²/q))/(1 - e₀)`. -/
noncomputable def sfK0 : ℝ :=
  (2 * sfGamma q r / sfh0 q +
    r * (sfCold q + 14 / sfh0 q + 2 * sfe0 q / q + sfe0 q ^ 2 / q)) / (1 - sfe0 q)
/-- `k₁ = (c_lead/h₀ + r(C' + 14/h₀ + 2e₀/q + e₀²/q))/(1 - e₀)`. -/
noncomputable def sfK1 : ℝ :=
  (sfClead q r / sfh0 q +
    r * (sfCprime q r + 14 / sfh0 q + 2 * sfe0 q / q + sfe0 q ^ 2 / q)) / (1 - sfe0 q)
/-- `k̄ = max(k₀, k₁)`. -/
noncomputable def sfKbar : ℝ := max (sfK0 q r) (sfK1 q r)

/-- **The auxiliary sides** `d^aux_s = e^{n e₀} max(d^m_s, 2k̄² r)` (`def:side-function`), with
`n = n_X` the number of primes of a block of the piece, at `(q, r) = (q_X, r_X)`. -/
noncomputable def dAuxL (n : ℕ) : ℝ :=
  Real.exp (n * sfe0 q) * max (sfDmL q r) (2 * sfKbar q r ^ 2 * r)

/-- The auxiliary side `d^aux_R`. -/
noncomputable def dAuxR (n : ℕ) : ℝ :=
  Real.exp (n * sfe0 q) * max (sfDmR q r) (2 * sfKbar q r ^ 2 * r)

end Coefficients

/-! ### The value of `s(31/32)` -/

/-- `s(τ)² = λ_max` at `τ = 31/32`, `u = (-b̄, 1, b̄)`, `v = (-1, -d̄, -d̄)`. -/
theorem sAux_sq : sSq tauSide uSide vSide =
    lamMax ((32 / 31) ^ 2 + (1 + 2 * (dBar : ℝ) ^ 2)) ((31 / 32) ^ 2 + (1 + 2 * (bBar : ℝ) ^ 2))
      ((bBar : ℝ) * (32 / 31) + 31 / 32) := by
  simp only [sSq, tauSide, nsq, uSide, vSide, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  congr 1 <;> ring

/-- **The auxiliary point** (after `def:side-function`): `s(31/32) = 2.0778741…`,
`s τ = 2.0129405…`, `s/τ = 2.1449023…`. -/
theorem sAux_bounds :
    (2.0778741 : ℝ) < sAux ∧ sAux < 2.0778742 ∧
      (2.0129405 : ℝ) < sAux * tauSide ∧ sAux * tauSide < 2.0129406 ∧
      (2.1449023 : ℝ) < sAux / tauSide ∧ sAux / tauSide < 2.1449024 := by
  -- the radicand of `λ_max`
  have hb : (bBar : ℝ) = 6426372 / 10 ^ 7 := by simp [bBar]
  have hd : (dBar : ℝ) = 5181074 / 10 ^ 7 := by simp [dBar]
  set R : ℝ := (((32 / 31) ^ 2 + (1 + 2 * (dBar : ℝ) ^ 2) -
      ((31 / 32) ^ 2 + (1 + 2 * (bBar : ℝ) ^ 2))) / 2) ^ 2 + ((bBar : ℝ) * (32 / 31) + 31 / 32) ^ 2
    with hR
  have hRlo : (1.634126519 : ℝ) ^ 2 < R := by rw [hR, hb, hd]; norm_num
  have hRhi : R < (1.634126520 : ℝ) ^ 2 := by rw [hR, hb, hd]; norm_num
  have hsq_lo : (1.634126519 : ℝ) < Real.sqrt R := by
    rw [Real.lt_sqrt (by norm_num)]; exact hRlo
  have hsq_hi : Real.sqrt R < 1.634126520 := by
    rw [Real.sqrt_lt' (by norm_num)]; exact hRhi
  have hS : sSq tauSide uSide vSide =
      ((32 / 31) ^ 2 + (1 + 2 * (dBar : ℝ) ^ 2) +
        ((31 / 32) ^ 2 + (1 + 2 * (bBar : ℝ) ^ 2))) / 2 + Real.sqrt R := by
    rw [sAux_sq, lamMax]
  have hP : ((32 / 31) ^ 2 + (1 + 2 * (dBar : ℝ) ^ 2) +
      ((31 / 32) ^ 2 + (1 + 2 * (bBar : ℝ) ^ 2))) / 2 =
      ((32 / 31) ^ 2 + (1 + 2 * (5181074 / 10 ^ 7) ^ 2) +
        ((31 / 32) ^ 2 + (1 + 2 * (6426372 / 10 ^ 7) ^ 2))) / 2 := by rw [hb, hd]
  have hlo : (2.07787415 : ℝ) ^ 2 < sSq tauSide uSide vSide := by
    rw [hS, hP]; norm_num at hsq_lo ⊢; linarith
  have hhi : sSq tauSide uSide vSide < (2.07787416 : ℝ) ^ 2 := by
    rw [hS, hP]; norm_num at hsq_hi ⊢; linarith
  have h1 : (2.07787415 : ℝ) < sAux := by
    unfold sAux sSide; rw [Real.lt_sqrt (by norm_num)]; exact hlo
  have h2 : sAux < 2.07787416 := by
    unfold sAux sSide; rw [Real.sqrt_lt' (by norm_num)]; exact hhi
  have ht : tauSide = 31 / 32 := rfl
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [ht]; nlinarith
  · rw [ht]; nlinarith
  · rw [ht, lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [ht, div_lt_iff₀ (by norm_num)]; nlinarith

end Sarkozy.Envelopes
