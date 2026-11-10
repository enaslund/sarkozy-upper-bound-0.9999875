module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The side function (`def:side-function`)

`paper/sections/24_matching_mean.tex`, paragraph "Auxiliary sides and the certified price",
`def:side-function`, with the norm `s(t; u, v)` of `lem:record:direct-gram`.

The definition is a chain of numbers. As the paper prescribes, every coefficient is a function of
the **independent variables** `(q, r)` (`q = 1/p`, `r = p^{-1/2}` at a prime; at a piece start `X`
they are evaluated at `q_X = 1/X`, `r_X = 1/⌊√X⌋`), written exactly as displayed. Nothing is
proved about these numbers here beyond the consistency of the fixed constants: the sums
`b̄ = ∑ β w_{βδ}`, `d̄ = ∑ δ w_{βδ}`, `f̄ = ∑ βδ w_{βδ}` of the four weights reproduce the tabulated
`(b₀, d₀, f₀)` exactly (`side_consts_consistent`), and the weights sum to one
(`side_weights_total`). The 33 values and their gates (`tab:data:sides`, `cert:record:matching`)
are not entered.

* `sNorm t u v = s(t; u, v) = ‖Υ_t(u, v)‖`, through the largest eigenvalue of the `2 × 2` Gram
  matrix of `lem:record:direct-gram` (`lamMax2`: `(A + C)/2 + √(((A - C)/2)² + B²)`). A hand
  evaluation of `sNorm (31/32) sideU sideV` gives `A ≈ 2.602427`, `B ≈ 1.632117`, `C ≈ 2.764440`,
  `λ_max ≈ 4.317559` and `s ≈ 2.077874`, the paper's `s(31/32) = 2.0778741…` (a check of the
  transcription, not a Lean proof).
* `sideConsts`: `(w_{++}, w_{+-}, w_{-+}, w_{--})`, `(b̄, d̄, f̄)`, `t = 31/32`.
* The coefficients `γ, c_lead, F_frame, ζ_{βδ}, C_old, C_ns, n_*, C_z, C_new, k_raw, η₁, ρ₁, η_*,
  φ₂, K_∞, φ_∞, C_rep, C'` and `c_com, d^m_L, d^m_R, k₀, k₁, k̄` (namespace `SideCoeffs`).
* The auxiliary sides `d^aux_s(X) = e^{n_X e₀(X)} max(d^m_s(X), 2 k̄(X)² r_X)` (`dAux`), with the
  integer `n_X = ⌊L_loc/log₋X⌋` as a parameter (`log₋ X` is the certified lower value of `log X`
  used by the certificate; it is not modelled here).
-/

namespace Sarkozy.PartVRecords

/-- The largest eigenvalue of the symmetric matrix `(A B; B C)`. -/
noncomputable def lamMax2 (A B C : ℝ) : ℝ := (A + C) / 2 + Real.sqrt (((A - C) / 2) ^ 2 + B ^ 2)

/-- The squared Euclidean norm of a vector of `ℝ³`. -/
def sq3 (u : Fin 3 → ℝ) : ℝ := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2

/-- **`s(t; u, v) = ‖Υ_t(u, v)‖`** (`lem:record:direct-gram`): `s² = λ_max` of
`(t⁻² + ‖v‖², -u₁/t - t v₁; -u₁/t - t v₁, t² + ‖u‖²)`, `u₁, v₁` the first coordinates. -/
noncomputable def sNorm (t : ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (lamMax2 (t⁻¹ ^ 2 + sq3 v) (-(u 0) / t - t * v 0) (t ^ 2 + sq3 u))

/-- The fixed constants of `def:side-function`. -/
structure SideConsts where
  wpp : ℚ
  wpm : ℚ
  wmp : ℚ
  wmm : ℚ
  bbar : ℚ
  dbar : ℚ
  fbar : ℚ
  tside : ℚ

/-- `(w_{++}, w_{+-}, w_{-+}, w_{--}) = (5803723, 2409463, 1786814, 0)/10⁷`,
`(b̄, d̄, f̄) = (.6426372, .5181074, .1607446)`, `t = 31/32`. -/
def sideConsts : SideConsts where
  wpp := 5803723 / 10 ^ 7
  wpm := 2409463 / 10 ^ 7
  wmp := 1786814 / 10 ^ 7
  wmm := 0
  bbar := 6426372 / 10 ^ 7
  dbar := 5181074 / 10 ^ 7
  fbar := 1607446 / 10 ^ 7
  tside := 31 / 32

/-- **The tabulated `(b̄, d̄, f̄)` are the sums `∑ β w_{βδ}`, `∑ δ w_{βδ}`, `∑ βδ w_{βδ}`.** -/
theorem side_consts_consistent :
    sideConsts.bbar = sideConsts.wpp + sideConsts.wpm - sideConsts.wmp - sideConsts.wmm ∧
      sideConsts.dbar = sideConsts.wpp - sideConsts.wpm + sideConsts.wmp - sideConsts.wmm ∧
      sideConsts.fbar = sideConsts.wpp - sideConsts.wpm - sideConsts.wmp + sideConsts.wmm := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [sideConsts]

/-- The four weights sum to one (a probability mixture of the four sign patterns). -/
theorem side_weights_total :
    sideConsts.wpp + sideConsts.wpm + sideConsts.wmp + sideConsts.wmm = 1 := by
  norm_num [sideConsts]

/-- `u = (-b̄, 1, b̄)`. -/
noncomputable def sideU : Fin 3 → ℝ := ![-(sideConsts.bbar : ℝ), 1, (sideConsts.bbar : ℝ)]

/-- `v = (-1, -d̄, -d̄)`. -/
noncomputable def sideV : Fin 3 → ℝ := ![-1, -(sideConsts.dbar : ℝ), -(sideConsts.dbar : ℝ)]

/-! ## The coefficients of `def:side-function`, as functions of the independent variables
`(q, r)`, exactly as displayed -/

namespace SideCoeffs

variable (q r : ℝ)

noncomputable def b : ℝ := (sideConsts.bbar : ℝ)
noncomputable def d : ℝ := (sideConsts.dbar : ℝ)
noncomputable def f : ℝ := (sideConsts.fbar : ℝ)
noncomputable def t : ℝ := (sideConsts.tside : ℝ)
noncomputable def Z : ℝ := (1 - q) * (1 - 2 * q)
noncomputable def h0 : ℝ := 1 - 14 * q
noncomputable def e0 : ℝ := 2 * q / ((1 - 3 * q) * (1 - 4 * q))
noncomputable def s : ℝ := sNorm t sideU sideV
noncomputable def γ : ℝ := (1 + q * (1 + 2 * r) / (1 - 2 * q)) ^ (1 / 2 : ℝ)
noncomputable def clead : ℝ := γ q r * (Real.sqrt (sq3 sideU) + Real.sqrt (sq3 sideV))
noncomputable def Fframe : ℝ :=
  (2 + |b + 1|) / (1 - q) + |1 - d| * q / ((1 - q) * (1 - 2 * q)) +
    2 * |b - d| * q ^ 2 / ((1 - q) * (1 - 2 * q)) + |2 - b + d| * r / (1 - q)
noncomputable def ζpp : ℝ := 6 * q ^ 2 / ((1 - 4 * q) * (1 - 5 * q))
noncomputable def ζpm : ℝ := 4 * q / ((1 - 4 * q) * (1 - 5 * q))
noncomputable def ζmp : ℝ := 4 * q / ((1 - 4 * q) * (1 - 5 * q) * (1 - 7 * q))
noncomputable def ζmm : ℝ := 8 * q / ((1 - 4 * q) * (1 - 5 * q) * (1 - 7 * q))
noncomputable def Cold : ℝ := 19 / (Z q * h0 q)
noncomputable def Cns : ℝ := 2 * |b| + 1 + 2 * |d| + 4 * |f|
noncomputable def nstar : ℝ := (1 + 8 * r + (18 / Z q + 144) * q) / h0 q
noncomputable def Cz : ℝ :=
  nstar q r / q * ((sideConsts.wpp : ℝ) * ζpp q + (sideConsts.wpm : ℝ) * ζpm q +
    (sideConsts.wmp : ℝ) * ζmp q + (sideConsts.wmm : ℝ) * ζmm q)
noncomputable def Cnew : ℝ := (2 * Cns / Z q + 144 + |b - d|) / h0 q + Cz q r
noncomputable def kraw : ℝ := r * clead q r / h0 q + q * Cnew q r
noncomputable def η1 : ℝ :=
  (4 * (sideConsts.wpp : ℝ) + 6 * (sideConsts.wpm : ℝ) + 4 * (sideConsts.wmp : ℝ) +
    8 * (sideConsts.wmm : ℝ)) * q / h0 q
noncomputable def ρ1 : ℝ := (kraw q r + η1 q ^ 2) / (1 - η1 q)
noncomputable def ηstar : ℝ := (e0 q + η1 q) / (1 - η1 q)
noncomputable def φ2 : ℝ := ηstar q / (1 - ρ1 q r)
noncomputable def Kinf : ℝ := 4 / (h0 q ^ (1 / 2 : ℝ) * (1 - η1 q))
noncomputable def φinf : ℝ := ηstar q + Kinf q * φ2 q r
noncomputable def Crep : ℝ := 2 * φinf q r / q * (kraw q r + 14 * q / h0 q)
noncomputable def Cprime : ℝ := Cnew q r + Crep q r
noncomputable def ccom : ℝ :=
  r * Fframe q r / h0 q + r * (Cold q + Cprime q r + 2 * e0 q ^ 2 / q)
noncomputable def dmL : ℝ := (γ q r * s * t / h0 q + ccom q r) / (1 - e0 q)
noncomputable def dmR : ℝ := (γ q r * s * t⁻¹ / h0 q + ccom q r) / (1 - e0 q)
noncomputable def k0 : ℝ :=
  (2 * γ q r / h0 q + r * (Cold q + 14 / h0 q + 2 * e0 q / q + e0 q ^ 2 / q)) / (1 - e0 q)
noncomputable def k1 : ℝ :=
  (clead q r / h0 q + r * (Cprime q r + 14 / h0 q + 2 * e0 q / q + e0 q ^ 2 / q)) / (1 - e0 q)
noncomputable def kbar : ℝ := max (k0 q r) (k1 q r)

end SideCoeffs

/-- **The auxiliary sides** `d^aux_s(X) = e^{n_X e₀(X)} max(d^m_s(X), 2 k̄(X)² r_X)`,
`s ∈ {L, R}` (`sideL = true` for `L`), at `(q_X, r_X)` and the integer `n_X`. -/
noncomputable def dAux (sideL : Bool) (qX rX : ℝ) (nX : ℕ) : ℝ :=
  Real.exp (nX * SideCoeffs.e0 qX) *
    max (if sideL then SideCoeffs.dmL qX rX else SideCoeffs.dmR qX rX)
      (2 * SideCoeffs.kbar qX rX ^ 2 * rX)

/-- The evaluation point of a piece starting at `X`: `q_X = 1/X`, `r_X = 1/⌊√X⌋`. -/
noncomputable def sidePoint (X : ℕ) : ℝ × ℝ := (1 / (X : ℝ), 1 / (Nat.sqrt X : ℝ))

end Sarkozy.PartVRecords
