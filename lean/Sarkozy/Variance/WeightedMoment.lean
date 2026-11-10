module

public import Sarkozy.Target
public import Sarkozy.Labellings.Extension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The second moment of the neighbourhood count (`lem:record:weighted-moment`)

`paper/sections/22_variance.tex`, `lem:record:weighted-moment`, at one prime `p ≡ 3 (mod 4)` with
`q = 1/p`, `r = p^{-1/2}`, and the graph moments `M_G = E ∏_{uv ∈ G, u<v} χ(ξ_v - ξ_u)` of the
graphs `G₅`, `G₁₂`, `G₁₀`.

**What is proved, and what is a hypothesis.**
* (a) `weightedMoment_a`: from the identity `eq:record:weighted-identity` (a **hypothesis**: it is
  the finite symbolic computation `cert:record:weighted-identity` over `400` terms, not formalized)
  and `|M_{G₅}|, |M_{G₁₂}| ≤ q`, `|M_{G₁₀}| ≤ qr`, the bound
  `E[P_adm 𝒲²]/p² ≤ 10q + 24qr + 4q² + 14q³`. The bounds `|M_{G₅}|, |M_{G₁₂}| ≤ q` (the kernel
  bound of `lem:matching:kernel`) are **hypotheses** there.
* (a) at the actual moments, **`weightedMoment_a_final`**: the only hypothesis is the certificate
  identity. `|M_{G₅}| ≤ q - q²` (`weightedMoment_mG5_abs_le`) and `|M_{G₁₂}| ≤ q`
  (`weightedMoment_mG12_abs_le`) are proved for every odd prime by a route different from the
  paper's (which uses the kernel bound of `lem:matching:kernel`): the modular evaluation with
  `∑_λ T_λ² ≤ p²`, then the inversion identity. This route needs no H3.
* (a), the bound `|M_{G₁₀}| ≤ qr`, **proved in full** over `ZMod p` for every odd prime
  (`weightedMoment_mG10_bound`), by the paper's argument: translation and dilation give
  `M_{G₁₀} = (p-1)/p⁵ ∑_{β,γ} χ(γ)χ(β-1)χ(γ-β) T_β T_γ` (`weightedMoment_sG10_eq`); the Gram
  identity `∑_γ (∑_β χ(γ-β) ψ_β)² = p ∑ψ² - (∑ψ)²` (from `eq:two-root`,
  `Labellings.two_root`) gives `‖H‖ ≤ √p` and `‖T‖ ≤ p` (`weightedMoment_k10_sq_le`).
* (b), the modular evaluation, **proved in full** over `ZMod p` (`weightedMoment_mG5_eq`):
  `M_{G₅} = (p-1)/p⁴ · ∑_λ χ(λ) T_λ²` with `T_λ = ∑_y χ(y(y-1)(y-λ))` (the project's
  `Target.legendreSum`), for every prime `p`. With H3 (`Target.AhlgrenOno`, `thm:ahlgren-ono`)
  this gives `-(1-q)(2qr+q²) ≤ M_{G₅} ≤ (1-q)(2qr-q²)` for every odd prime
  (`weightedMoment_mG5_bounds`; the scalar step is `weightedMoment_modular_bounds`).
* (b), the inversion identity `M_{G₁₂} = (1-5q)M_{G₅} + q²(1-q)(1-2q)`, **proved in full** over
  `ZMod p` for every odd prime (`weightedMoment_mG12_inversion`), by the paper's argument: the
  translation `ξ₀ = 0`; on `ξ₁ ≠ 0` the inversion `ξ_v = 1/η_v` turns the summand into a copy of
  `G₅` on nonzero labels (`weightedMoment_g12_inv`), and inclusion–exclusion over the vanishing
  labels (`weightedMoment_ie_pointwise`, the slices `weightedMoment_slice_b` … `_slice_ef`) gives
  `(p⁵ - 5p⁴)M_{G₅} + 2(p-1)`; on `ξ₁ = 0` the sum is `∑_{a,b ≠ 0} c(a,b)² = (p-1)(p²-2p-2)`
  (`weightedMoment_r_eq`). The sign `χ(-1)⁸ = 1` makes `p ≡ 3 (mod 4)` unnecessary here.
* (b), the consequences: the displayed identity
  `E/p² = (5+3q)M_{G₅} + 24M_{G₁₀} + 5q - 3q² + 11q³ - 13q⁴` (`weightedMoment_b_identity`) and the
  bound `E/p² ≤ 5q + 34qr + 11q³` (`weightedMoment_b_bound`, needing only `0 ≤ q ≤ 4`, `r ≥ 0`).
  At the actual moments: **`weightedMoment_b_final`**, whose only hypotheses are H3 and the
  certificate identity `eq:record:weighted-identity` (`cert:record:weighted-identity`).
* `lem:l20-star-mean`, the scalar consequence (`l20_starMean_bound`, `l20_normalizer`): the star
  means of the four centres have modulus at most `m_⋆`, and `|Z₀ - 1| ≤ ε_Z`, `Z₀ ≥ 1 - ε_Z > 0`,
  `R_Z = (1-ε_Z)⁻¹ ≥ Z₀⁻¹`. The identities `eq:l20-star-identities` (the `1200`-term computation
  of `cert:l20-star-mean`) are **hypotheses**.

The moments are normalized sums: `M_{G₅} = p⁻⁵ ∑_{ξ ∈ 𝔽_p⁵} ∏_{uv ∈ G₅} χ(ξ_v - ξ_u)` (`mG5`) and
`M_{G₁₀} = p⁻⁶ ∑_{ξ ∈ 𝔽_p⁶} ∏_{uv ∈ G₁₀} χ(ξ_v - ξ_u)` (`mG10`), `M_{G₁₂}` likewise (`mG12`),
with the edges oriented `u < v`. The three character-sum results hold for every odd prime;
`p ≡ 3 (mod 4)` is not used by them.
-/

namespace Sarkozy.Variance

namespace WeightedMoment

open Finset
open scoped BigOperators

/-! ### (a) and (b): the scalar consequences -/

/-- **`lem:record:weighted-moment`(a), the last assertion.** If
`E[P_adm 𝒲²]/p² = (4+8q)M₅ + M₁₂ + 24M₁₀ + 5q - 4q² + 14q³ - 15q⁴` (`eq:record:weighted-identity`,
**hypothesis**: `cert:record:weighted-identity`) and `|M₅|, |M₁₂| ≤ q`, `|M₁₀| ≤ qr`
(**hypotheses**), then `E[P_adm 𝒲²]/p² ≤ 10q + 24qr + 4q² + 14q³`. -/
theorem weightedMoment_a {q r M5 M12 M10 E : ℝ}
    (hid : E = (4 + 8 * q) * M5 + M12 + 24 * M10 + 5 * q - 4 * q ^ 2 + 14 * q ^ 3 - 15 * q ^ 4)
    (h5 : |M5| ≤ q) (h12 : |M12| ≤ q) (h10 : |M10| ≤ q * r) :
    E ≤ 10 * q + 24 * q * r + 4 * q ^ 2 + 14 * q ^ 3 := by
  have hq : 0 ≤ q := (abs_nonneg _).trans h5
  have a5 := (abs_le.mp h5).2
  have a12 := (abs_le.mp h12).2
  have a10 := (abs_le.mp h10).2
  have hm : (4 + 8 * q) * M5 ≤ (4 + 8 * q) * q := mul_le_mul_of_nonneg_left a5 (by positivity)
  nlinarith [pow_nonneg hq 4]

/-- **`lem:record:weighted-moment`(b), the bounds of `eq:record:modular-moment`** in scalar form:
if `M₅ = (p-1)/p⁴ · S` and `|S + p| ≤ 2 p √p` with `p ≥ 1`, then with `q = 1/p`, `r = p^{-1/2}`,
`-(1-q)(2qr+q²) ≤ M₅ ≤ (1-q)(2qr-q²)`. -/
theorem weightedMoment_modular_bounds {p q r S M5 : ℝ} (hp : 1 ≤ p) (hq : q = 1 / p)
    (hr : r * Real.sqrt p = 1) (hM5 : M5 = (p - 1) / p ^ 4 * S)
    (hS : |S + p| ≤ 2 * p * Real.sqrt p) :
    -((1 - q) * (2 * q * r + q ^ 2)) ≤ M5 ∧ M5 ≤ (1 - q) * (2 * q * r - q ^ 2) := by
  set s := Real.sqrt p with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hps : p = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hr' : r = 1 / s := by field_simp; linarith
  have hS' := abs_le.mp hS
  have hc : 0 ≤ (p - 1) / p ^ 4 := div_nonneg (by linarith) (by positivity)
  have e1 : (1 - q) * (2 * q * r - q ^ 2) = (p - 1) / p ^ 4 * (2 * p * s - p) := by
    rw [hq, hr', hps]
    field_simp
  have e2 : -((1 - q) * (2 * q * r + q ^ 2)) = (p - 1) / p ^ 4 * (-2 * p * s - p) := by
    rw [hq, hr', hps]
    field_simp
    ring
  rw [e1, e2, hM5]
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith) hc
  · exact mul_le_mul_of_nonneg_left (by linarith) hc

/-- **`lem:record:weighted-moment`(b), the displayed identity**: substituting the inversion
identity `M₁₂ = (1-5q)M₅ + q²(1-q)(1-2q)` (**hypothesis**) in `eq:record:weighted-identity`
(**hypothesis**) gives `E/p² = (5+3q)M₅ + 24M₁₀ + 5q - 3q² + 11q³ - 13q⁴`. -/
theorem weightedMoment_b_identity {q M5 M12 M10 E : ℝ}
    (hid : E = (4 + 8 * q) * M5 + M12 + 24 * M10 + 5 * q - 4 * q ^ 2 + 14 * q ^ 3 - 15 * q ^ 4)
    (hinv : M12 = (1 - 5 * q) * M5 + q ^ 2 * (1 - q) * (1 - 2 * q)) :
    E = (5 + 3 * q) * M5 + 24 * M10 + 5 * q - 3 * q ^ 2 + 11 * q ^ 3 - 13 * q ^ 4 := by
  rw [hid, hinv]
  ring

/-- **`lem:record:weighted-moment`(b), the final bound**: with the displayed identity of (b),
`M₅ ≤ (1-q)(2qr - q²)` and `|M₁₀| ≤ qr`, `E/p² ≤ 5q + 34qr + 11q³`; the gap is
`8q² - 2q³ + 10q⁴ + 4q²r + 6q³r ≥ 0`, which needs only `0 ≤ q ≤ 4` and `r ≥ 0`. -/
theorem weightedMoment_b_bound {q r M5 M10 E : ℝ} (hq : 0 ≤ q) (hq4 : q ≤ 4) (hr : 0 ≤ r)
    (hid : E = (5 + 3 * q) * M5 + 24 * M10 + 5 * q - 3 * q ^ 2 + 11 * q ^ 3 - 13 * q ^ 4)
    (h5 : M5 ≤ (1 - q) * (2 * q * r - q ^ 2)) (h10 : |M10| ≤ q * r) :
    E ≤ 5 * q + 34 * q * r + 11 * q ^ 3 := by
  have a10 := (abs_le.mp h10).2
  have hm : (5 + 3 * q) * M5 ≤ (5 + 3 * q) * ((1 - q) * (2 * q * r - q ^ 2)) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have hgap : 0 ≤ 8 * q ^ 2 - 2 * q ^ 3 + 10 * q ^ 4 + 4 * q ^ 2 * r + 6 * q ^ 3 * r := by
    have : 0 ≤ 2 * q ^ 2 * (4 - q) := by
      have := sq_nonneg q
      nlinarith
    have h1 : 0 ≤ q ^ 4 := pow_nonneg hq 4
    have h2 : 0 ≤ q ^ 2 * r := mul_nonneg (sq_nonneg q) hr
    have h3 : 0 ≤ q ^ 3 * r := mul_nonneg (pow_nonneg hq 3) hr
    nlinarith
  have hexp : (5 + 3 * q) * ((1 - q) * (2 * q * r - q ^ 2)) + 24 * (q * r) + 5 * q - 3 * q ^ 2 +
      11 * q ^ 3 - 13 * q ^ 4 = 5 * q + 34 * q * r + 11 * q ^ 3 -
        (8 * q ^ 2 - 2 * q ^ 3 + 10 * q ^ 4 + 4 * q ^ 2 * r + 6 * q ^ 3 * r) := by ring
  nlinarith

/-! ### `lem:l20-star-mean`: the scalar consequence -/

/-- **`lem:l20-star-mean`, the star means.** If at each of the four centres of the second kind
the star mean is `±(M₅ + 8q² - 33q³ + 25q⁴)/Z₄` (the three-leaf stars cancel and the four-leaf
star has this mean, by `eq:l20-star-identities`, **hypotheses**: `cert:l20-star-mean`), and
`|M₅| ≤ (1-q)(q² + 2qr)` (`eq:record:modular-moment`), then the four centres give at most
`m_⋆ = 4{(1-q)(q²+2qr) + 8q² + 33q³ + 25q⁴}/Z₄` in modulus. -/
theorem l20_starMean_bound {q r M5 Z4 : ℝ} (hq : 0 ≤ q) (hZ : 0 < Z4)
    (h5 : |M5| ≤ (1 - q) * (q ^ 2 + 2 * q * r)) (σ : Fin 4 → ℝ) (hσ : ∀ i, |σ i| = 1) :
    |∑ i, σ i * ((M5 + 8 * q ^ 2 - 33 * q ^ 3 + 25 * q ^ 4) / Z4)| ≤
      4 * ((1 - q) * (q ^ 2 + 2 * q * r) + 8 * q ^ 2 + 33 * q ^ 3 + 25 * q ^ 4) / Z4 := by
  have hone : |(M5 + 8 * q ^ 2 - 33 * q ^ 3 + 25 * q ^ 4) / Z4| ≤
      ((1 - q) * (q ^ 2 + 2 * q * r) + 8 * q ^ 2 + 33 * q ^ 3 + 25 * q ^ 4) / Z4 := by
    rw [abs_div, abs_of_pos hZ]
    apply div_le_div_of_nonneg_right _ hZ.le
    calc |M5 + 8 * q ^ 2 - 33 * q ^ 3 + 25 * q ^ 4|
        ≤ |M5| + |8 * q ^ 2| + |33 * q ^ 3| + |25 * q ^ 4| := by
          have := abs_add_le (M5 + 8 * q ^ 2 - 33 * q ^ 3) (25 * q ^ 4)
          have := abs_sub (M5 + 8 * q ^ 2) (33 * q ^ 3)
          have := abs_add_le M5 (8 * q ^ 2)
          linarith
      _ = |M5| + 8 * q ^ 2 + 33 * q ^ 3 + 25 * q ^ 4 := by
          rw [abs_of_nonneg (show (0 : ℝ) ≤ 8 * q ^ 2 by positivity),
            abs_of_nonneg (show (0 : ℝ) ≤ 33 * q ^ 3 by positivity),
            abs_of_nonneg (show (0 : ℝ) ≤ 25 * q ^ 4 by positivity)]
      _ ≤ _ := by linarith
  calc |∑ i, σ i * ((M5 + 8 * q ^ 2 - 33 * q ^ 3 + 25 * q ^ 4) / Z4)|
      ≤ ∑ i, |σ i * ((M5 + 8 * q ^ 2 - 33 * q ^ 3 + 25 * q ^ 4) / Z4)| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ _i : Fin 4, |(M5 + 8 * q ^ 2 - 33 * q ^ 3 + 25 * q ^ 4) / Z4| := by
        apply sum_congr rfl
        intro i _
        rw [abs_mul, hσ i, one_mul]
    _ ≤ ∑ _i : Fin 4, ((1 - q) * (q ^ 2 + 2 * q * r) + 8 * q ^ 2 + 33 * q ^ 3 + 25 * q ^ 4) / Z4 :=
        sum_le_sum fun i _ => hone
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **`lem:l20-star-mean`, the normalizer.** If `Z₀ = 1 + t_ns + t_⋆ - t_coll` (the empty set
of edges, the nonstar sets, the star sets and the collision correction) with `|t_ns| ≤ N_ns`,
`|t_⋆| ≤ m_⋆`, `|t_coll| ≤ D_col` and `ε_Z = N_ns + D_col + m_⋆ < 1`, then `|Z₀ - 1| ≤ ε_Z`,
`Z₀ ≥ 1 - ε_Z > 0`, and `R_Z = (1 - ε_Z)⁻¹ ≥ Z₀⁻¹`. -/
theorem l20_normalizer {Z0 tns tstar tcoll Nns mstar Dcol : ℝ}
    (hZ : Z0 = 1 + tns + tstar - tcoll) (hns : |tns| ≤ Nns) (hstar : |tstar| ≤ mstar)
    (hcoll : |tcoll| ≤ Dcol) (hε : Nns + Dcol + mstar < 1) :
    |Z0 - 1| ≤ Nns + Dcol + mstar ∧ 1 - (Nns + Dcol + mstar) ≤ Z0 ∧ 0 < Z0 ∧
      Z0⁻¹ ≤ (1 - (Nns + Dcol + mstar))⁻¹ := by
  have a := abs_le.mp hns
  have b := abs_le.mp hstar
  have c := abs_le.mp hcoll
  have h1 : |Z0 - 1| ≤ Nns + Dcol + mstar := by
    rw [hZ, abs_le]
    constructor <;> linarith
  have h2 : 1 - (Nns + Dcol + mstar) ≤ Z0 := by
    rw [hZ]
    linarith
  have h3 : 0 < 1 - (Nns + Dcol + mstar) := by linarith
  exact ⟨h1, h2, lt_of_lt_of_le h3 h2, inv_anti₀ h3 h2⟩

/-! ### (b): the modular evaluation over `ZMod p` -/

section Modular

variable (p : ℕ) [Fact p.Prime]

/-- The summand of `p⁵ M_{G₅}` after the translation `ξ₀ = 0` (labels `ξ₁, …, ξ₄ = b, c, d, e`). -/
def g5 (b c d e : ZMod p) : ℤ :=
  quadraticChar (ZMod p) b * quadraticChar (ZMod p) c * quadraticChar (ZMod p) d *
    quadraticChar (ZMod p) e * quadraticChar (ZMod p) (d - b) *
    quadraticChar (ZMod p) (e - b) * quadraticChar (ZMod p) (d - c) *
    quadraticChar (ZMod p) (e - c)

/-- `p⁵ M_{G₅} = ∑_{ξ ∈ 𝔽_p⁵} ∏_{uv ∈ G₅, u<v} χ(ξ_v - ξ_u)`, with `ξ₀, …, ξ₄ = a, b, c, d, e` and
the eight edges `01, 02, 03, 04, 13, 14, 23, 24` of `G₅` (the complete tripartite graph with parts
`{0}`, `{1,2}`, `{3,4}`). -/
def sG5 : ℤ :=
  ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p, ∑ e : ZMod p,
    quadraticChar (ZMod p) (b - a) * quadraticChar (ZMod p) (c - a) *
      quadraticChar (ZMod p) (d - a) * quadraticChar (ZMod p) (e - a) *
      quadraticChar (ZMod p) (d - b) * quadraticChar (ZMod p) (e - b) *
      quadraticChar (ZMod p) (d - c) * quadraticChar (ZMod p) (e - c)

theorem weightedMoment_sum_comp_sub (f : ZMod p → ℤ) (a : ZMod p) : ∑ x, f (x - a) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

theorem weightedMoment_sum_comp_mul (f : ZMod p → ℤ) {b : ZMod p} (hb : b ≠ 0) :
    ∑ x, f (b * x) = ∑ x, f x :=
  Fintype.sum_bijective (b * ·) (mulLeft_bijective₀ b hb) _ _ (fun _ => rfl)

/-- The translation `ξ₀ = 0`: the inner sum does not depend on `ξ₀`. -/
theorem weightedMoment_sG5_translate : sG5 p = (p : ℤ) * ∑ b, ∑ c, ∑ d, ∑ e, g5 p b c d e := by
  have hpt : ∀ a b c d e : ZMod p,
      quadraticChar (ZMod p) (b - a) * quadraticChar (ZMod p) (c - a) *
        quadraticChar (ZMod p) (d - a) * quadraticChar (ZMod p) (e - a) *
        quadraticChar (ZMod p) (d - b) * quadraticChar (ZMod p) (e - b) *
        quadraticChar (ZMod p) (d - c) * quadraticChar (ZMod p) (e - c) =
      g5 p (b - a) (c - a) (d - a) (e - a) := by
    intro a b c d e
    simp only [g5, sub_sub_sub_cancel_right]
  have hshift : ∀ a : ZMod p, (∑ b, ∑ c, ∑ d, ∑ e, g5 p (b - a) (c - a) (d - a) (e - a)) =
      ∑ b, ∑ c, ∑ d, ∑ e, g5 p b c d e := by
    intro a
    have h1 : ∀ b c d, ∑ e, g5 p b c d (e - a) = ∑ e, g5 p b c d e :=
      fun b c d => weightedMoment_sum_comp_sub p (g5 p b c d) a
    have h2 : ∀ b c, ∑ d, ∑ e, g5 p b c (d - a) e = ∑ d, ∑ e, g5 p b c d e :=
      fun b c => weightedMoment_sum_comp_sub p (fun d => ∑ e, g5 p b c d e) a
    have h3 : ∀ b, ∑ c, ∑ d, ∑ e, g5 p b (c - a) d e = ∑ c, ∑ d, ∑ e, g5 p b c d e :=
      fun b => weightedMoment_sum_comp_sub p (fun c => ∑ d, ∑ e, g5 p b c d e) a
    have h4 : ∑ b, ∑ c, ∑ d, ∑ e, g5 p (b - a) c d e = ∑ b, ∑ c, ∑ d, ∑ e, g5 p b c d e :=
      weightedMoment_sum_comp_sub p (fun b => ∑ c, ∑ d, ∑ e, g5 p b c d e) a
    simp only [h1, h2, h3, h4]
  unfold sG5
  simp only [hpt, hshift]
  rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]

/-- The reduced sum `H = ∑_{c,d,e} χ(c)χ(d)χ(e)χ(d-1)χ(e-1)χ(d-c)χ(e-c)`. -/
def h5 : ℤ := ∑ c : ZMod p, ∑ d : ZMod p, ∑ e : ZMod p,
  quadraticChar (ZMod p) c * quadraticChar (ZMod p) d * quadraticChar (ZMod p) e *
    quadraticChar (ZMod p) (d - 1) * quadraticChar (ZMod p) (e - 1) *
    quadraticChar (ZMod p) (d - c) * quadraticChar (ZMod p) (e - c)

/-- The dilation `ξ_v = c η_v`: for `ξ₁ = c ≠ 0` every edge factor acquires `χ(c)`, and
`χ(c)⁸ = 1`; for `ξ₁ = 0` the factor `χ(ξ₁)` vanishes. -/
theorem weightedMoment_inner_eq (b : ZMod p) :
    ∑ c, ∑ d, ∑ e, g5 p b c d e = if b = 0 then 0 else h5 p := by
  by_cases hb : b = 0
  · subst hb
    simp [g5]
  · simp only [hb, ↓reduceIte]
    have hscale : ∀ c d e : ZMod p, g5 p b (b * c) (b * d) (b * e) =
        quadraticChar (ZMod p) c * quadraticChar (ZMod p) d * quadraticChar (ZMod p) e *
        quadraticChar (ZMod p) (d - 1) * quadraticChar (ZMod p) (e - 1) *
        quadraticChar (ZMod p) (d - c) * quadraticChar (ZMod p) (e - c) := by
      intro c d e
      have e1 : b * d - b = b * (d - 1) := by ring
      have e2 : b * e - b = b * (e - 1) := by ring
      have e3 : b * d - b * c = b * (d - c) := by ring
      have e4 : b * e - b * c = b * (e - c) := by ring
      have hsq : quadraticChar (ZMod p) b ^ 2 = 1 := quadraticChar_sq_one hb
      simp only [g5, e1, e2, e3, e4, map_mul]
      linear_combination
        (quadraticChar (ZMod p) c * quadraticChar (ZMod p) d * quadraticChar (ZMod p) e *
          quadraticChar (ZMod p) (d - 1) * quadraticChar (ZMod p) (e - 1) *
          quadraticChar (ZMod p) (d - c) * quadraticChar (ZMod p) (e - c)) *
          (quadraticChar (ZMod p) b ^ 6 + quadraticChar (ZMod p) b ^ 4 +
            quadraticChar (ZMod p) b ^ 2 + 1) * hsq
    have h1 : ∀ c d, ∑ e, g5 p b c d e = ∑ e, g5 p b c d (b * e) :=
      fun c d => (weightedMoment_sum_comp_mul p (g5 p b c d) hb).symm
    have h2 : ∀ c, ∑ d, ∑ e, g5 p b c d (b * e) = ∑ d, ∑ e, g5 p b c (b * d) (b * e) :=
      fun c => (weightedMoment_sum_comp_mul p (fun d => ∑ e, g5 p b c d (b * e)) hb).symm
    have h3 : ∑ c, ∑ d, ∑ e, g5 p b c (b * d) (b * e) =
        ∑ c, ∑ d, ∑ e, g5 p b (b * c) (b * d) (b * e) :=
      (weightedMoment_sum_comp_mul p (fun c => ∑ d, ∑ e, g5 p b c (b * d) (b * e)) hb).symm
    simp only [h1, h2]
    rw [h3]
    simp only [hscale]
    rfl

/-- The sums over `η₃` and `η₄` are both `T_λ`, `λ = η₂`. -/
theorem weightedMoment_h5_eq :
    h5 p = ∑ t : ZMod p, quadraticChar (ZMod p) t * Target.legendreSum p t ^ 2 := by
  unfold h5 Target.legendreSum
  apply sum_congr rfl
  intro c _
  simp only [map_mul]
  rw [sq, sum_mul_sum, mul_sum]
  apply sum_congr rfl
  intro d _
  rw [mul_sum]
  apply sum_congr rfl
  intro e _
  ring

/-- `p⁵ M_{G₅} = p (p - 1) ∑_λ χ(λ) T_λ²`. -/
theorem weightedMoment_sG5_eq : sG5 p = (p : ℤ) * ((p : ℤ) - 1) *
    ∑ t : ZMod p, quadraticChar (ZMod p) t * Target.legendreSum p t ^ 2 := by
  rw [weightedMoment_sG5_translate]
  simp only [weightedMoment_inner_eq]
  have hif : ∀ b : ZMod p,
      (if b = 0 then (0 : ℤ) else h5 p) = h5 p - if b = 0 then h5 p else 0 := by
    intro b
    split_ifs <;> ring
  simp only [hif]
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  simp only [sum_ite_eq', mem_univ, ↓reduceIte]
  rw [weightedMoment_h5_eq]
  ring

/-- `M_{G₅} = p⁻⁵ ∑_{ξ ∈ 𝔽_p⁵} ∏_{uv ∈ G₅} χ(ξ_v - ξ_u)`. -/
noncomputable def mG5 : ℝ := (sG5 p : ℝ) / (p : ℝ) ^ 5

/-- **`lem:record:weighted-moment`(b), the modular evaluation `eq:record:modular-moment`**:
`M_{G₅} = (p-1)/p⁴ · ∑_λ χ(λ) T_λ²`, for every prime `p`. -/
theorem weightedMoment_mG5_eq : mG5 p = ((p : ℝ) - 1) / (p : ℝ) ^ 4 *
    ((∑ t : ZMod p, quadraticChar (ZMod p) t * Target.legendreSum p t ^ 2 : ℤ) : ℝ) := by
  unfold mG5
  rw [weightedMoment_sG5_eq]
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  push_cast
  field_simp

/-- **`lem:record:weighted-moment`(b), the bounds of `eq:record:modular-moment`**, from H3
(`Target.AhlgrenOno`, `thm:ahlgren-ono`): for every odd prime `p`, with `q = 1/p` and
`r = p^{-1/2}`, `-(1-q)(2qr+q²) ≤ M_{G₅} ≤ (1-q)(2qr-q²)`. -/
theorem weightedMoment_mG5_bounds (hAO : Target.AhlgrenOno) (hp2 : p ≠ 2) {q r : ℝ}
    (hq : q = 1 / (p : ℝ)) (hr : r * Real.sqrt p = 1) :
    -((1 - q) * (2 * q * r + q ^ 2)) ≤ mG5 p ∧ mG5 p ≤ (1 - q) * (2 * q * r - q ^ 2) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have h32 : (p : ℝ) ^ ((3 : ℝ) / 2) = (p : ℝ) * Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hp0,
      Real.rpow_one]
  have hS := hAO p hp2
  rw [h32] at hS
  exact weightedMoment_modular_bounds hp1 hq hr (weightedMoment_mG5_eq p) (by linarith [hS])

end Modular

/-! ### (a): the bound for `M_{G₁₀}` over `ZMod p` -/

section G10

variable (p : ℕ) [Fact p.Prime]

/-- `p⁶ M_{G₁₀}`: edges `01, 03, 04, 05, 12, 14, 15, 23, 25, 34`, labels `a, b, c, d, e, f`. -/
def sG10 : ℤ :=
  ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p, ∑ e : ZMod p, ∑ f : ZMod p,
    quadraticChar (ZMod p) (b - a) * quadraticChar (ZMod p) (d - a) *
      quadraticChar (ZMod p) (e - a) * quadraticChar (ZMod p) (f - a) *
      quadraticChar (ZMod p) (c - b) * quadraticChar (ZMod p) (e - b) *
      quadraticChar (ZMod p) (f - b) * quadraticChar (ZMod p) (d - c) *
      quadraticChar (ZMod p) (f - c) * quadraticChar (ZMod p) (e - d)

/-- The summand of `p⁶ M_{G₁₀}` after the translation `ξ₀ = 0`. -/
def g10 (b c d e f : ZMod p) : ℤ :=
  quadraticChar (ZMod p) b * quadraticChar (ZMod p) d * quadraticChar (ZMod p) e *
    quadraticChar (ZMod p) f * quadraticChar (ZMod p) (c - b) * quadraticChar (ZMod p) (e - b) *
    quadraticChar (ZMod p) (f - b) * quadraticChar (ZMod p) (d - c) *
    quadraticChar (ZMod p) (f - c) * quadraticChar (ZMod p) (e - d)

/-- The translation `ξ₀ = 0`. -/
theorem weightedMoment_sG10_translate :
    sG10 p = (p : ℤ) * ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g10 p b c d e f := by
  have hpt : ∀ a b c d e f : ZMod p,
      quadraticChar (ZMod p) (b - a) * quadraticChar (ZMod p) (d - a) *
        quadraticChar (ZMod p) (e - a) * quadraticChar (ZMod p) (f - a) *
        quadraticChar (ZMod p) (c - b) * quadraticChar (ZMod p) (e - b) *
        quadraticChar (ZMod p) (f - b) * quadraticChar (ZMod p) (d - c) *
        quadraticChar (ZMod p) (f - c) * quadraticChar (ZMod p) (e - d) =
      g10 p (b - a) (c - a) (d - a) (e - a) (f - a) := by
    intro a b c d e f
    simp only [g10, sub_sub_sub_cancel_right]
  have hshift : ∀ a : ZMod p,
      (∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g10 p (b - a) (c - a) (d - a) (e - a) (f - a)) =
        ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g10 p b c d e f := by
    intro a
    have h1 : ∀ b c d e, ∑ f, g10 p b c d e (f - a) = ∑ f, g10 p b c d e f :=
      fun b c d e => weightedMoment_sum_comp_sub p (g10 p b c d e) a
    have h2 : ∀ b c d, ∑ e, ∑ f, g10 p b c d (e - a) f = ∑ e, ∑ f, g10 p b c d e f :=
      fun b c d => weightedMoment_sum_comp_sub p (fun e => ∑ f, g10 p b c d e f) a
    have h3 : ∀ b c, ∑ d, ∑ e, ∑ f, g10 p b c (d - a) e f = ∑ d, ∑ e, ∑ f, g10 p b c d e f :=
      fun b c => weightedMoment_sum_comp_sub p (fun d => ∑ e, ∑ f, g10 p b c d e f) a
    have h4 : ∀ b, ∑ c, ∑ d, ∑ e, ∑ f, g10 p b (c - a) d e f =
        ∑ c, ∑ d, ∑ e, ∑ f, g10 p b c d e f :=
      fun b => weightedMoment_sum_comp_sub p (fun c => ∑ d, ∑ e, ∑ f, g10 p b c d e f) a
    have h5 : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g10 p (b - a) c d e f =
        ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g10 p b c d e f :=
      weightedMoment_sum_comp_sub p (fun b => ∑ c, ∑ d, ∑ e, ∑ f, g10 p b c d e f) a
    simp only [h1, h2, h3, h4, h5]
  unfold sG10
  simp only [hpt, hshift]
  rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]

/-- The reduced double sum `∑_{β,γ} χ(γ)χ(β-1)χ(γ-β) T_β T_γ`, here with `c = β`, `d = γ`. -/
noncomputable def k10 : ℤ := ∑ c : ZMod p, ∑ d : ZMod p,
  quadraticChar (ZMod p) d * quadraticChar (ZMod p) (c - 1) * quadraticChar (ZMod p) (d - c) *
    Target.legendreSum p d * Target.legendreSum p c

/-- The dilation `ξ_v = c η_v` (`v ≥ 2`) for `ξ₁ = c ≠ 0`: the ten edge factors acquire
`χ(c)¹⁰ = 1`, and the sums over `η₄`, `η₅` give `T_γ`, `T_β`. -/
theorem weightedMoment_inner10 (b : ZMod p) :
    ∑ c, ∑ d, ∑ e, ∑ f, g10 p b c d e f = if b = 0 then 0 else k10 p := by
  by_cases hb : b = 0
  · subst hb
    simp [g10]
  · simp only [hb, ↓reduceIte]
    have hscale : ∀ c d e f : ZMod p, g10 p b (b * c) (b * d) (b * e) (b * f) =
        (quadraticChar (ZMod p) d * quadraticChar (ZMod p) (c - 1) *
          quadraticChar (ZMod p) (d - c)) *
        (quadraticChar (ZMod p) e * quadraticChar (ZMod p) (e - 1) *
          quadraticChar (ZMod p) (e - d)) *
        (quadraticChar (ZMod p) f * quadraticChar (ZMod p) (f - 1) *
          quadraticChar (ZMod p) (f - c)) := by
      intro c d e f
      have e1 : b * c - b = b * (c - 1) := by ring
      have e2 : b * e - b = b * (e - 1) := by ring
      have e3 : b * f - b = b * (f - 1) := by ring
      have e4 : b * d - b * c = b * (d - c) := by ring
      have e5 : b * f - b * c = b * (f - c) := by ring
      have e6 : b * e - b * d = b * (e - d) := by ring
      have hsq : quadraticChar (ZMod p) b ^ 2 = 1 := quadraticChar_sq_one hb
      simp only [g10, e1, e2, e3, e4, e5, e6, map_mul]
      linear_combination
        (quadraticChar (ZMod p) d * quadraticChar (ZMod p) (c - 1) *
          quadraticChar (ZMod p) (d - c) *
          (quadraticChar (ZMod p) e * quadraticChar (ZMod p) (e - 1) *
            quadraticChar (ZMod p) (e - d)) *
          (quadraticChar (ZMod p) f * quadraticChar (ZMod p) (f - 1) *
            quadraticChar (ZMod p) (f - c))) *
          (quadraticChar (ZMod p) b ^ 8 + quadraticChar (ZMod p) b ^ 6 +
            quadraticChar (ZMod p) b ^ 4 + quadraticChar (ZMod p) b ^ 2 + 1) * hsq
    have h1 : ∀ c d e, ∑ f, g10 p b c d e f = ∑ f, g10 p b c d e (b * f) :=
      fun c d e => (weightedMoment_sum_comp_mul p (g10 p b c d e) hb).symm
    have h2 : ∀ c d, ∑ e, ∑ f, g10 p b c d e (b * f) = ∑ e, ∑ f, g10 p b c d (b * e) (b * f) :=
      fun c d => (weightedMoment_sum_comp_mul p (fun e => ∑ f, g10 p b c d e (b * f)) hb).symm
    have h3 : ∀ c, ∑ d, ∑ e, ∑ f, g10 p b c d (b * e) (b * f) =
        ∑ d, ∑ e, ∑ f, g10 p b c (b * d) (b * e) (b * f) :=
      fun c =>
        (weightedMoment_sum_comp_mul p (fun d => ∑ e, ∑ f, g10 p b c d (b * e) (b * f)) hb).symm
    have h4 : ∑ c, ∑ d, ∑ e, ∑ f, g10 p b c (b * d) (b * e) (b * f) =
        ∑ c, ∑ d, ∑ e, ∑ f, g10 p b (b * c) (b * d) (b * e) (b * f) :=
      (weightedMoment_sum_comp_mul p
        (fun c => ∑ d, ∑ e, ∑ f, g10 p b c (b * d) (b * e) (b * f)) hb).symm
    simp only [h1, h2, h3]
    rw [h4]
    simp only [hscale]
    unfold k10 Target.legendreSum
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro d _
    simp only [map_mul]
    simp only [mul_sum, sum_mul]
    exact sum_comm

/-- `p⁶ M_{G₁₀} = p (p - 1) ∑_{β,γ} χ(γ)χ(β-1)χ(γ-β) T_β T_γ`. -/
theorem weightedMoment_sG10_eq : sG10 p = (p : ℤ) * ((p : ℤ) - 1) * k10 p := by
  rw [weightedMoment_sG10_translate]
  simp only [weightedMoment_inner10]
  have hif : ∀ b : ZMod p, (if b = 0 then (0 : ℤ) else k10 p) =
      k10 p - if b = 0 then k10 p else 0 := by
    intro b
    split_ifs <;> ring
  simp only [hif]
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  simp only [sum_ite_eq', mem_univ, ↓reduceIte]
  ring

theorem weightedMoment_chi_sq_le_one (x : ZMod p) : quadraticChar (ZMod p) x ^ 2 ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [quadraticChar_sq_one hx]

/-- `∑_γ χ(γ-β)χ(γ-β') = p[β = β'] - 1` (`eq:two-root` for `β ≠ β'`). -/
theorem weightedMoment_gram_chi (hp2 : p ≠ 2) (β β' : ZMod p) :
    ∑ γ : ZMod p, quadraticChar (ZMod p) (γ - β) * quadraticChar (ZMod p) (γ - β') =
      if β = β' then (p : ℤ) - 1 else -1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  split_ifs with h
  · subst h
    have hγ : ∀ γ : ZMod p, quadraticChar (ZMod p) (γ - β) * quadraticChar (ZMod p) (γ - β) =
        1 - if γ = β then 1 else 0 := by
      intro γ
      split_ifs with hγ
      · subst hγ
        simp
      · rw [← sq, quadraticChar_sq_one (sub_ne_zero.mpr hγ)]
        ring
    simp only [hγ]
    rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]
    ring
  · have h2 := Labellings.two_root hF h
    unfold Labellings.rootSum at h2
    simp only [prod_pair h, map_mul] at h2
    exact h2

/-- The Gram identity: a kernel with `∑_γ K(γ,β)K(γ,β') = p[β = β'] - 1` satisfies
`∑_γ (∑_β K(γ,β) ψ_β)² = p ∑ ψ² - (∑ ψ)²`. -/
theorem weightedMoment_gram_sum (K : ZMod p → ZMod p → ℤ)
    (hK : ∀ β β', ∑ γ, K γ β * K γ β' = if β = β' then (p : ℤ) - 1 else -1)
    (ψ : ZMod p → ℤ) :
    ∑ γ, (∑ β, K γ β * ψ β) ^ 2 = (p : ℤ) * ∑ β, ψ β ^ 2 - (∑ β, ψ β) ^ 2 := by
  have e1 : ∀ γ, (∑ β, K γ β * ψ β) ^ 2 = ∑ β, ∑ β', ψ β * ψ β' * (K γ β * K γ β') := by
    intro γ
    rw [sq, sum_mul_sum]
    apply sum_congr rfl
    intro β _
    apply sum_congr rfl
    intro β' _
    ring
  simp only [e1]
  rw [sum_comm]
  have e2 : ∀ β, ∑ γ, ∑ β', ψ β * ψ β' * (K γ β * K γ β') =
      ∑ β', ψ β * ψ β' * (if β = β' then (p : ℤ) - 1 else -1) := by
    intro β
    rw [sum_comm]
    apply sum_congr rfl
    intro β' _
    rw [← mul_sum, hK]
  simp only [e2]
  have e3 : ∀ β β' : ZMod p, ψ β * ψ β' * (if β = β' then (p : ℤ) - 1 else -1) =
      (p : ℤ) * (if β = β' then ψ β * ψ β' else 0) - ψ β * ψ β' := by
    intro β β'
    split_ifs <;> ring
  simp only [e3, sum_sub_distrib, ← mul_sum, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [sq (∑ β, ψ β), sum_mul_sum]
  simp only [sq, mul_sum]

/-- The matrix bound of the proof: with `H_{γβ} = χ(γ-β)` (`HᵀH = pI - J`, so `‖H‖ ≤ √p`),
`T = -Hv`, `‖v‖² ≤ p`, so `‖T‖ ≤ p`; the double sum is `ψ'ᵀ H ψ` with `‖ψ‖, ‖ψ'‖ ≤ ‖T‖`, hence at
most `p^{5/2}` in modulus: `(∑_{β,γ} …)² ≤ p⁵`. -/
theorem weightedMoment_k10_sq_le (hp2 : p ≠ 2) : k10 p ^ 2 ≤ (p : ℤ) ^ 5 := by
  set T : ZMod p → ℤ := fun x => Target.legendreSum p x with hT
  set ψ : ZMod p → ℤ := fun c => quadraticChar (ZMod p) (c - 1) * T c with hψ
  set ψ' : ZMod p → ℤ := fun d => quadraticChar (ZMod p) d * T d with hψ'
  set hvec : ZMod p → ℤ := fun d => ∑ c, quadraticChar (ZMod p) (d - c) * ψ c with hhvec
  have hk : k10 p = ∑ d, ψ' d * hvec d := by
    unfold k10
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    simp only [hψ', hhvec, hψ, hT, mul_sum]
    apply sum_congr rfl
    intro c _
    ring
  have hCS := sum_mul_sq_le_sq_mul_sq univ ψ' hvec
  have hgram := weightedMoment_gram_sum p (fun γ β => quadraticChar (ZMod p) (γ - β))
    (weightedMoment_gram_chi p hp2) ψ
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hh : ∑ d, hvec d ^ 2 ≤ (p : ℤ) * ∑ c, ψ c ^ 2 := by
    have : ∑ d, hvec d ^ 2 = (p : ℤ) * ∑ β, ψ β ^ 2 - (∑ β, ψ β) ^ 2 := hgram
    nlinarith [sq_nonneg (∑ β, ψ β)]
  -- `∑ T² ≤ p²`
  have hTsq : ∑ x, T x ^ 2 ≤ (p : ℤ) ^ 2 := by
    set v : ZMod p → ℤ := fun y => quadraticChar (ZMod p) y * quadraticChar (ZMod p) (y - 1)
      with hv
    have hTv : ∀ x, T x = ∑ y, quadraticChar (ZMod p) (y - x) * v y := by
      intro x
      simp only [hT, hv, Target.legendreSum, map_mul]
      apply sum_congr rfl
      intro y _
      ring
    have hK' : ∀ y y' : ZMod p,
        ∑ x, quadraticChar (ZMod p) (y - x) * quadraticChar (ZMod p) (y' - x) =
        if y = y' then (p : ℤ) - 1 else -1 := by
      intro y y'
      rw [← weightedMoment_gram_chi p hp2 y y']
      apply sum_congr rfl
      intro x _
      rw [← map_mul, ← map_mul]
      congr 1
      ring
    have hg2 := weightedMoment_gram_sum p (fun x y => quadraticChar (ZMod p) (y - x)) hK' v
    have hvsq : ∑ y, v y ^ 2 ≤ (p : ℤ) := by
      have : ∀ y, v y ^ 2 ≤ 1 := by
        intro y
        simp only [hv, mul_pow]
        have h1 := weightedMoment_chi_sq_le_one p y
        have h2 := weightedMoment_chi_sq_le_one p (y - 1)
        have h3 : 0 ≤ quadraticChar (ZMod p) y ^ 2 := sq_nonneg _
        nlinarith
      calc ∑ y, v y ^ 2 ≤ ∑ _y : ZMod p, (1 : ℤ) := sum_le_sum fun y _ => this y
        _ = p := by rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    simp only [hTv]
    have : ∑ x, (∑ y, quadraticChar (ZMod p) (y - x) * v y) ^ 2 =
        (p : ℤ) * ∑ y, v y ^ 2 - (∑ y, v y) ^ 2 := hg2
    rw [this]
    nlinarith [sq_nonneg (∑ y, v y)]
  have hψsq : ∑ c, ψ c ^ 2 ≤ ∑ x, T x ^ 2 := by
    apply sum_le_sum
    intro c _
    simp only [hψ, mul_pow]
    have h1 := weightedMoment_chi_sq_le_one p (c - 1)
    nlinarith [sq_nonneg (T c)]
  have hψ'sq : ∑ d, ψ' d ^ 2 ≤ ∑ x, T x ^ 2 := by
    apply sum_le_sum
    intro d _
    simp only [hψ', mul_pow]
    have h1 := weightedMoment_chi_sq_le_one p d
    nlinarith [sq_nonneg (T d)]
  rw [hk]
  have hA : 0 ≤ ∑ d, ψ' d ^ 2 := sum_nonneg fun d _ => sq_nonneg _
  have hB : 0 ≤ ∑ c, ψ c ^ 2 := sum_nonneg fun c _ => sq_nonneg _
  calc (∑ d, ψ' d * hvec d) ^ 2 ≤ (∑ d, ψ' d ^ 2) * ∑ d, hvec d ^ 2 := hCS
    _ ≤ (∑ d, ψ' d ^ 2) * ((p : ℤ) * ∑ c, ψ c ^ 2) := mul_le_mul_of_nonneg_left hh hA
    _ ≤ (p : ℤ) ^ 2 * ((p : ℤ) * (p : ℤ) ^ 2) := by
        apply mul_le_mul (hψ'sq.trans hTsq) _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (hψsq.trans hTsq) hp0
    _ = (p : ℤ) ^ 5 := by ring

/-- `M_{G₁₀} = p⁻⁶ ∑_{ξ ∈ 𝔽_p⁶} ∏_{uv ∈ G₁₀} χ(ξ_v - ξ_u)`. -/
noncomputable def mG10 : ℝ := (sG10 p : ℝ) / (p : ℝ) ^ 6

/-- **`lem:record:weighted-moment`(a), the bound `|M_{G₁₀}| ≤ qr`**, proved in full for every odd
prime `p` (`q = 1/p`, `r = p^{-1/2}`): `|M_{G₁₀}| ≤ (p-1)p^{-5/2} ≤ p^{-3/2}`. -/
theorem weightedMoment_mG10_bound (hp2 : p ≠ 2) {q r : ℝ} (hq : q = 1 / (p : ℝ))
    (hr : r * Real.sqrt p = 1) :
    |mG10 p| ≤ q * r := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hk : ((k10 p : ℤ) : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 := by exact_mod_cast weightedMoment_k10_sq_le p hp2
  have hM : mG10 p = ((p : ℝ) - 1) * (k10 p : ℝ) / (p : ℝ) ^ 5 := by
    unfold mG10
    rw [weightedMoment_sG10_eq]
    push_cast
    field_simp
  have hr2 : r ^ 2 = 1 / (p : ℝ) := by
    have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
    field_simp
    nlinarith [hr]
  have hr0 : 0 ≤ r := by
    by_contra h
    push Not at h
    have : r * Real.sqrt p < 0 := mul_neg_of_neg_of_pos h (Real.sqrt_pos.mpr hp0)
    linarith
  have hqr : 0 ≤ q * r := mul_nonneg (by rw [hq]; positivity) hr0
  apply abs_le_of_sq_le_sq _ hqr
  rw [hM, mul_pow, hq, hr2, div_pow, mul_pow]
  have h1 : ((p : ℝ) - 1) ^ 2 ≤ (p : ℝ) ^ 2 := by nlinarith
  have h2 : 0 ≤ ((p : ℝ) - 1) ^ 2 := sq_nonneg _
  rw [div_le_iff₀ (by positivity)]
  calc ((p : ℝ) - 1) ^ 2 * (k10 p : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 * (p : ℝ) ^ 5 :=
        mul_le_mul h1 hk (sq_nonneg _) (by positivity)
    _ = (1 / (p : ℝ)) ^ 2 * (1 / (p : ℝ)) * ((p : ℝ) ^ 5) ^ 2 := by
        field_simp


/-- **`lem:record:weighted-moment`(b), the final bound, at the actual graph moments.** For an odd
prime `p`, H3 (`Target.AhlgrenOno`), the identity `eq:record:weighted-identity` for
`E = E[P_adm 𝒲²]/p²` (**hypothesis**, `cert:record:weighted-identity`) and the inversion identity
for `M_{G₁₂}` (**hypothesis**) give `E ≤ 5q + 34qr + 11q³`. The moments `M_{G₅}` (`mG5`) and
`M_{G₁₀}` (`mG10`) are the actual character sums; their bounds are proved here. -/
theorem weightedMoment_b_of_H3 (hAO : Target.AhlgrenOno) (hp2 : p ≠ 2) {q r M12 E : ℝ}
    (hq : q = 1 / (p : ℝ)) (hr : r * Real.sqrt p = 1)
    (hid : E = (4 + 8 * q) * mG5 p + M12 + 24 * mG10 p + 5 * q - 4 * q ^ 2 + 14 * q ^ 3 -
      15 * q ^ 4)
    (hinv : M12 = (1 - 5 * q) * mG5 p + q ^ 2 * (1 - q) * (1 - 2 * q)) :
    E ≤ 5 * q + 34 * q * r + 11 * q ^ 3 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 4 := by
    rw [hq, div_le_iff₀ (by linarith)]
    linarith
  have hr0 : 0 ≤ r := by
    by_contra h
    push Not at h
    have : r * Real.sqrt p < 0 := mul_neg_of_neg_of_pos h (Real.sqrt_pos.mpr (by linarith))
    linarith
  exact weightedMoment_b_bound hq0 hq1 hr0 (weightedMoment_b_identity hid hinv)
    (weightedMoment_mG5_bounds p hAO hp2 hq hr).2 (weightedMoment_mG10_bound p hp2 hq hr)

end G10

/-! ### (b): the inversion identity for `M_{G₁₂}` over `ZMod p` -/

section G12

variable (p : ℕ) [Fact p.Prime]

/-- `p⁶ M_{G₁₂}`: edges `02, 03, 04, 05, 12, 13, 14, 15, 24, 25, 34, 35`. -/
def sG12 : ℤ :=
  ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p, ∑ e : ZMod p, ∑ f : ZMod p,
    quadraticChar (ZMod p) (c - a) * quadraticChar (ZMod p) (d - a) *
      quadraticChar (ZMod p) (e - a) * quadraticChar (ZMod p) (f - a) *
      quadraticChar (ZMod p) (c - b) * quadraticChar (ZMod p) (d - b) *
      quadraticChar (ZMod p) (e - b) * quadraticChar (ZMod p) (f - b) *
      quadraticChar (ZMod p) (e - c) * quadraticChar (ZMod p) (f - c) *
      quadraticChar (ZMod p) (e - d) * quadraticChar (ZMod p) (f - d)

/-- The summand of `p⁶ M_{G₁₂}` after the translation `ξ₀ = 0`. -/
def g12 (b c d e f : ZMod p) : ℤ :=
  quadraticChar (ZMod p) c * quadraticChar (ZMod p) d *
    quadraticChar (ZMod p) e * quadraticChar (ZMod p) f *
    quadraticChar (ZMod p) (c - b) * quadraticChar (ZMod p) (d - b) *
    quadraticChar (ZMod p) (e - b) * quadraticChar (ZMod p) (f - b) *
    quadraticChar (ZMod p) (e - c) * quadraticChar (ZMod p) (f - c) *
    quadraticChar (ZMod p) (e - d) * quadraticChar (ZMod p) (f - d)

/-- The copy of `G₅` on `b, …, f` (centre `b`, parts `{c,d}`, `{e,f}`). -/
def copy5 (b c d e f : ZMod p) : ℤ :=
  quadraticChar (ZMod p) (c - b) * quadraticChar (ZMod p) (d - b) *
    quadraticChar (ZMod p) (e - b) * quadraticChar (ZMod p) (f - b) *
    quadraticChar (ZMod p) (e - c) * quadraticChar (ZMod p) (f - c) *
    quadraticChar (ZMod p) (e - d) * quadraticChar (ZMod p) (f - d)

/-- The translation `ξ₀ = 0`. -/
theorem weightedMoment_sG12_translate :
    sG12 p = (p : ℤ) * ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g12 p b c d e f := by
  have hpt : ∀ a b c d e f : ZMod p,
      quadraticChar (ZMod p) (c - a) * quadraticChar (ZMod p) (d - a) *
        quadraticChar (ZMod p) (e - a) * quadraticChar (ZMod p) (f - a) *
        quadraticChar (ZMod p) (c - b) * quadraticChar (ZMod p) (d - b) *
        quadraticChar (ZMod p) (e - b) * quadraticChar (ZMod p) (f - b) *
        quadraticChar (ZMod p) (e - c) * quadraticChar (ZMod p) (f - c) *
        quadraticChar (ZMod p) (e - d) * quadraticChar (ZMod p) (f - d) =
      g12 p (b - a) (c - a) (d - a) (e - a) (f - a) := by
    intro a b c d e f
    simp only [g12, sub_sub_sub_cancel_right]
  have hshift : ∀ a : ZMod p,
      (∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g12 p (b - a) (c - a) (d - a) (e - a) (f - a)) =
        ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g12 p b c d e f := by
    intro a
    have h1 : ∀ b c d e, ∑ f, g12 p b c d e (f - a) = ∑ f, g12 p b c d e f :=
      fun b c d e => weightedMoment_sum_comp_sub p (g12 p b c d e) a
    have h2 : ∀ b c d, ∑ e, ∑ f, g12 p b c d (e - a) f = ∑ e, ∑ f, g12 p b c d e f :=
      fun b c d => weightedMoment_sum_comp_sub p (fun e => ∑ f, g12 p b c d e f) a
    have h3 : ∀ b c, ∑ d, ∑ e, ∑ f, g12 p b c (d - a) e f = ∑ d, ∑ e, ∑ f, g12 p b c d e f :=
      fun b c => weightedMoment_sum_comp_sub p (fun d => ∑ e, ∑ f, g12 p b c d e f) a
    have h4 : ∀ b, ∑ c, ∑ d, ∑ e, ∑ f, g12 p b (c - a) d e f =
        ∑ c, ∑ d, ∑ e, ∑ f, g12 p b c d e f :=
      fun b => weightedMoment_sum_comp_sub p (fun c => ∑ d, ∑ e, ∑ f, g12 p b c d e f) a
    have h5 : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g12 p (b - a) c d e f =
        ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g12 p b c d e f :=
      weightedMoment_sum_comp_sub p (fun b => ∑ c, ∑ d, ∑ e, ∑ f, g12 p b c d e f) a
    simp only [h1, h2, h3, h4, h5]
  unfold sG12
  simp only [hpt, hshift]
  rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]

theorem weightedMoment_chi_inv {x : ZMod p} (hx : x ≠ 0) :
    quadraticChar (ZMod p) x⁻¹ = quadraticChar (ZMod p) x := by
  have h1 : quadraticChar (ZMod p) x⁻¹ * quadraticChar (ZMod p) x = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  have h2 := quadraticChar_sq_one hx
  linear_combination (-(quadraticChar (ZMod p) x⁻¹)) * h2 + quadraticChar (ZMod p) x * h1

theorem weightedMoment_inv_sub_inv' {x y : ZMod p} (hx : x ≠ 0) (hy : y ≠ 0) :
    y⁻¹ - x⁻¹ = (-1) * (y - x) * (x⁻¹ * y⁻¹) := by
  field_simp
  ring

/-- The inversion `ξ_v = 1/η_v`: pointwise form. -/
theorem weightedMoment_g12_inv (b c d e f : ZMod p) :
    (if b⁻¹ = 0 then 0 else g12 p b⁻¹ c⁻¹ d⁻¹ e⁻¹ f⁻¹) =
      quadraticChar (ZMod p) b ^ 2 * quadraticChar (ZMod p) c ^ 2 *
        quadraticChar (ZMod p) d ^ 2 * quadraticChar (ZMod p) e ^ 2 *
        quadraticChar (ZMod p) f ^ 2 * copy5 p b c d e f := by
  by_cases hb : b = 0
  · subst hb
    simp
  by_cases hc : c = 0
  · subst hc
    simp [g12]
  by_cases hd : d = 0
  · subst hd
    simp [g12]
  by_cases he : e = 0
  · subst he
    simp [g12]
  by_cases hf : f = 0
  · subst hf
    simp [g12]
  have hb' : b⁻¹ ≠ 0 := inv_ne_zero hb
  simp only [hb', ↓reduceIte]
  simp only [g12, copy5, weightedMoment_inv_sub_inv' p hb hc,
    weightedMoment_inv_sub_inv' p hb hd, weightedMoment_inv_sub_inv' p hb he,
    weightedMoment_inv_sub_inv' p hb hf, weightedMoment_inv_sub_inv' p hc he,
    weightedMoment_inv_sub_inv' p hc hf, weightedMoment_inv_sub_inv' p hd he,
    weightedMoment_inv_sub_inv' p hd hf, map_mul, weightedMoment_chi_inv p hb,
    weightedMoment_chi_inv p hc, weightedMoment_chi_inv p hd, weightedMoment_chi_inv p he,
    weightedMoment_chi_inv p hf]
  have hm : quadraticChar (ZMod p) (-1) ^ 2 = 1 :=
    quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  have h2b := quadraticChar_sq_one hb
  have h2c := quadraticChar_sq_one hc
  have h2d := quadraticChar_sq_one hd
  have h2e := quadraticChar_sq_one he
  have h2f := quadraticChar_sq_one hf
  set m := quadraticChar (ZMod p) (-1)
  set xb := quadraticChar (ZMod p) b
  set xc := quadraticChar (ZMod p) c
  set xd := quadraticChar (ZMod p) d
  set xe := quadraticChar (ZMod p) e
  set xf := quadraticChar (ZMod p) f
  linear_combination (quadraticChar (ZMod p) (c - b) * quadraticChar (ZMod p) (d - b) *
      quadraticChar (ZMod p) (e - b) * quadraticChar (ZMod p) (f - b) *
      quadraticChar (ZMod p) (e - c) * quadraticChar (ZMod p) (f - c) *
      quadraticChar (ZMod p) (e - d) * quadraticChar (ZMod p) (f - d)) *
    ((m ^ 6 + m ^ 4 + m ^ 2 + 1) * (xb ^ 2 * xc ^ 2 * xd ^ 2 * xe ^ 2 * xf ^ 2) ^ 2 * hm +
      (xb ^ 2 * xc ^ 2 * xd ^ 2 * xe ^ 2 * xf ^ 2) *
        (xc ^ 2 * xd ^ 2 * xe ^ 2 * xf ^ 2 * h2b + xd ^ 2 * xe ^ 2 * xf ^ 2 * h2c +
          xe ^ 2 * xf ^ 2 * h2d + xf ^ 2 * h2e + h2f))

/-! #### Small facts about `χ` -/

theorem weightedMoment_chi_sq_if (x : ZMod p) :
    quadraticChar (ZMod p) x ^ 2 = if x = 0 then 0 else 1 := by
  split_ifs with hx
  · subst hx
    simp
  · exact quadraticChar_sq_one hx

theorem weightedMoment_chi_vals (x : ZMod p) :
    quadraticChar (ZMod p) x = 0 ∨ quadraticChar (ZMod p) x = 1 ∨
      quadraticChar (ZMod p) x = -1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rcases quadraticChar_dichotomy hx with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem weightedMoment_chi_pow3 (x : ZMod p) :
    quadraticChar (ZMod p) x ^ 3 = quadraticChar (ZMod p) x := by
  rcases weightedMoment_chi_vals p x with h | h | h <;> rw [h] <;> norm_num

theorem weightedMoment_chi_pow4 (x : ZMod p) :
    quadraticChar (ZMod p) x ^ 4 = quadraticChar (ZMod p) x ^ 2 := by
  rcases weightedMoment_chi_vals p x with h | h | h <;> rw [h] <;> norm_num

theorem weightedMoment_sum_chi_sq :
    ∑ x : ZMod p, quadraticChar (ZMod p) x ^ 2 = (p : ℤ) - 1 := by
  have h : ∀ x : ZMod p, quadraticChar (ZMod p) x ^ 2 = 1 - if x = 0 then 1 else 0 := by
    intro x
    rw [weightedMoment_chi_sq_if]
    split_ifs <;> ring
  simp only [h, sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one,
    sum_ite_eq', mem_univ, ↓reduceIte]

theorem weightedMoment_sum_chi (hp2 : p ≠ 2) : ∑ x : ZMod p, quadraticChar (ZMod p) x = 0 :=
  quadraticChar_sum_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)

theorem weightedMoment_sum_chi_shift (hp2 : p ≠ 2) (b : ZMod p) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x - b) = 0 := by
  rw [weightedMoment_sum_comp_sub p (fun x => quadraticChar (ZMod p) x) b]
  exact weightedMoment_sum_chi p hp2

theorem weightedMoment_sum_chi_sq_mul (hp2 : p ≠ 2) (b : ZMod p) :
    ∑ x : ZMod p, quadraticChar (ZMod p) x ^ 2 * quadraticChar (ZMod p) (x - b) =
      -quadraticChar (ZMod p) (0 - b) := by
  have h : ∀ x : ZMod p, quadraticChar (ZMod p) x ^ 2 * quadraticChar (ZMod p) (x - b) =
      quadraticChar (ZMod p) (x - b) - if x = 0 then quadraticChar (ZMod p) (x - b) else 0 := by
    intro x
    rw [weightedMoment_chi_sq_if]
    split_ifs <;> ring
  simp only [h, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte,
    weightedMoment_sum_chi_shift p hp2]
  ring

theorem weightedMoment_sum_comp_neg (g : ZMod p → ℤ) : ∑ x : ZMod p, g (0 - x) = ∑ x, g x :=
  Fintype.sum_equiv (Equiv.subLeft 0) _ _ (fun _ => rfl)

theorem weightedMoment_sum_comp_inv (g : ZMod p → ℤ) : ∑ x : ZMod p, g x⁻¹ = ∑ x, g x :=
  Fintype.sum_bijective (·⁻¹) inv_involutive.bijective _ _ (fun _ => rfl)

theorem weightedMoment_sum_rot3 (F : ZMod p → ZMod p → ZMod p → ℤ) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ x, ∑ y, F x y z := by
  calc ∑ x, ∑ y, ∑ z, F x y z = ∑ x, ∑ z, ∑ y, F x y z := sum_congr rfl fun x _ => sum_comm
    _ = ∑ z, ∑ x, ∑ y, F x y z := sum_comm

theorem weightedMoment_sum_inv5 (F : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℤ) :
    ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F b⁻¹ c⁻¹ d⁻¹ e⁻¹ f⁻¹ =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F b c d e f := by
  have h1 : ∀ b c d e, ∑ f, F b c d e f⁻¹ = ∑ f, F b c d e f :=
    fun b c d e => weightedMoment_sum_comp_inv p (F b c d e)
  have h2 : ∀ b c d, ∑ e, ∑ f, F b c d e⁻¹ f = ∑ e, ∑ f, F b c d e f :=
    fun b c d => weightedMoment_sum_comp_inv p (fun e => ∑ f, F b c d e f)
  have h3 : ∀ b c, ∑ d, ∑ e, ∑ f, F b c d⁻¹ e f = ∑ d, ∑ e, ∑ f, F b c d e f :=
    fun b c => weightedMoment_sum_comp_inv p (fun d => ∑ e, ∑ f, F b c d e f)
  have h4 : ∀ b, ∑ c, ∑ d, ∑ e, ∑ f, F b c⁻¹ d e f = ∑ c, ∑ d, ∑ e, ∑ f, F b c d e f :=
    fun b => weightedMoment_sum_comp_inv p (fun c => ∑ d, ∑ e, ∑ f, F b c d e f)
  have h5 : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F b⁻¹ c d e f = ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F b c d e f :=
    weightedMoment_sum_comp_inv p (fun b => ∑ c, ∑ d, ∑ e, ∑ f, F b c d e f)
  simp only [h1, h2, h3, h4, h5]

theorem weightedMoment_shift3 (G : ZMod p → ZMod p → ZMod p → ℤ) (b : ZMod p) :
    ∑ x, ∑ y, ∑ z, G (x - b) (y - b) (z - b) = ∑ x, ∑ y, ∑ z, G x y z := by
  have h1 : ∀ x y, ∑ z, G x y (z - b) = ∑ z, G x y z :=
    fun x y => weightedMoment_sum_comp_sub p (G x y) b
  have h2 : ∀ x, ∑ y, ∑ z, G x (y - b) z = ∑ y, ∑ z, G x y z :=
    fun x => weightedMoment_sum_comp_sub p (fun y => ∑ z, G x y z) b
  have h3 : ∑ x, ∑ y, ∑ z, G (x - b) y z = ∑ x, ∑ y, ∑ z, G x y z :=
    weightedMoment_sum_comp_sub p (fun x => ∑ y, ∑ z, G x y z) b
  simp only [h1, h2, h3]

/-! #### Symmetries of `G₅` -/

theorem weightedMoment_g5_swap12 (x₁ x₂ x₃ x₄ : ZMod p) :
    g5 p x₁ x₂ x₃ x₄ = g5 p x₂ x₁ x₃ x₄ := by
  unfold g5
  ring

theorem weightedMoment_g5_swapPairs (x₁ x₂ x₃ x₄ : ZMod p) :
    g5 p x₁ x₂ x₃ x₄ = g5 p x₃ x₄ x₁ x₂ := by
  have e1 : x₁ - x₃ = (-1) * (x₃ - x₁) := by ring
  have e2 : x₂ - x₃ = (-1) * (x₃ - x₂) := by ring
  have e3 : x₁ - x₄ = (-1) * (x₄ - x₁) := by ring
  have e4 : x₂ - x₄ = (-1) * (x₄ - x₂) := by ring
  have hm : quadraticChar (ZMod p) (-1) ^ 2 = 1 :=
    quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  unfold g5
  rw [e1, e2, e3, e4]
  simp only [map_mul]
  linear_combination (-(quadraticChar (ZMod p) x₁ * quadraticChar (ZMod p) x₂ *
      quadraticChar (ZMod p) x₃ * quadraticChar (ZMod p) x₄ *
      quadraticChar (ZMod p) (x₃ - x₁) * quadraticChar (ZMod p) (x₄ - x₁) *
      quadraticChar (ZMod p) (x₃ - x₂) * quadraticChar (ZMod p) (x₄ - x₂)) *
    (quadraticChar (ZMod p) (-1) ^ 2 + 1)) * hm

/-- `S₄ = p⁴ M_{G₅}`. -/
def s4 : ℤ := ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p, ∑ e : ZMod p, g5 p b c d e

theorem weightedMoment_slice_core :
    ∑ b : ZMod p, ∑ x : ZMod p, ∑ y : ZMod p, ∑ z : ZMod p,
      g5 p (0 - b) (x - b) (y - b) (z - b) = s4 p := by
  have h : ∀ b : ZMod p, ∑ x, ∑ y, ∑ z, g5 p (0 - b) (x - b) (y - b) (z - b) =
      ∑ x, ∑ y, ∑ z, g5 p (0 - b) x y z :=
    fun b => weightedMoment_shift3 p (fun x y z => g5 p (0 - b) x y z) b
  rw [sum_congr rfl fun b _ => h b]
  exact weightedMoment_sum_comp_neg p (fun b => ∑ x, ∑ y, ∑ z, g5 p b x y z)

/-! #### The slices of the inclusion–exclusion -/

theorem weightedMoment_slice_b : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    (if b = 0 then copy5 p b c d e f else 0) = s4 p := by
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  unfold s4
  simp only [copy5, g5, sub_zero]

theorem weightedMoment_slice_c : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    (if c = 0 then copy5 p b c d e f else 0) = s4 p := by
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [← weightedMoment_slice_core p]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro f _
  simp only [copy5, g5, sub_sub_sub_cancel_right]

theorem weightedMoment_slice_d : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    (if d = 0 then copy5 p b c d e f else 0) = s4 p := by
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [← weightedMoment_slice_core p]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro f _
  rw [weightedMoment_g5_swap12]
  simp only [copy5, g5, sub_sub_sub_cancel_right]

theorem weightedMoment_slice_e : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    (if e = 0 then copy5 p b c d e f else 0) = s4 p := by
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [← weightedMoment_slice_core p]
  apply sum_congr rfl
  intro b _
  rw [weightedMoment_sum_rot3 p (fun c d f => copy5 p b c d 0 f)]
  apply sum_congr rfl
  intro f _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro d _
  rw [weightedMoment_g5_swapPairs]
  simp only [copy5, g5, sub_sub_sub_cancel_right]

theorem weightedMoment_slice_f : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    (if f = 0 then copy5 p b c d e f else 0) = s4 p := by
  simp only [sum_ite_eq', mem_univ, ↓reduceIte]
  rw [← weightedMoment_slice_core p]
  apply sum_congr rfl
  intro b _
  rw [weightedMoment_sum_rot3 p (fun c d e => copy5 p b c d e 0)]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro d _
  rw [weightedMoment_g5_swapPairs]
  simp only [copy5, g5, sub_sub_sub_cancel_right]
  ring

theorem weightedMoment_chi_neg_sq (x : ZMod p) :
    quadraticChar (ZMod p) (0 - x) ^ 2 = quadraticChar (ZMod p) x ^ 2 := by
  rw [zero_sub, show -x = (-1) * x by ring, map_mul, mul_pow,
    quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero), one_mul]

theorem weightedMoment_sum_sum_prod (A : ℤ) (B C : ZMod p → ℤ) :
    ∑ e, ∑ f, A * B e * C f = A * (∑ e, B e) * (∑ f, C f) := by
  rw [mul_assoc, sum_mul_sum, mul_sum]
  apply sum_congr rfl
  intro e _
  rw [mul_sum]
  apply sum_congr rfl
  intro f _
  ring

theorem weightedMoment_sum_chi_pow4_neg :
    ∑ b : ZMod p, quadraticChar (ZMod p) (0 - b) ^ 4 = (p : ℤ) - 1 := by
  rw [weightedMoment_sum_comp_neg p (fun b => quadraticChar (ZMod p) b ^ 4)]
  simp only [weightedMoment_chi_pow4]
  exact weightedMoment_sum_chi_sq p

theorem weightedMoment_slice_cd (hp2 : p ≠ 2) : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    (if c = 0 ∧ d = 0 then copy5 p b c d e f else 0) = (p : ℤ) - 1 := by
  simp only [ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  have h : ∀ b e f : ZMod p, copy5 p b 0 0 e f = quadraticChar (ZMod p) (0 - b) ^ 2 *
      (quadraticChar (ZMod p) e ^ 2 * quadraticChar (ZMod p) (e - b)) *
      (quadraticChar (ZMod p) f ^ 2 * quadraticChar (ZMod p) (f - b)) := by
    intro b e f
    simp only [copy5, sub_zero]
    ring
  simp only [h, weightedMoment_sum_sum_prod, weightedMoment_sum_chi_sq_mul p hp2]
  rw [← weightedMoment_sum_chi_pow4_neg p]
  apply sum_congr rfl
  intro b _
  ring

theorem weightedMoment_slice_ef (hp2 : p ≠ 2) : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    (if e = 0 ∧ f = 0 then copy5 p b c d e f else 0) = (p : ℤ) - 1 := by
  simp only [ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  have h : ∀ b c d : ZMod p, copy5 p b c d 0 0 = quadraticChar (ZMod p) (0 - b) ^ 2 *
      (quadraticChar (ZMod p) c ^ 2 * quadraticChar (ZMod p) (c - b)) *
      (quadraticChar (ZMod p) d ^ 2 * quadraticChar (ZMod p) (d - b)) := by
    intro b c d
    have hc := weightedMoment_chi_neg_sq p c
    have hd := weightedMoment_chi_neg_sq p d
    simp only [copy5]
    linear_combination (quadraticChar (ZMod p) (0 - b) ^ 2 * quadraticChar (ZMod p) (c - b) *
      quadraticChar (ZMod p) (d - b)) * (quadraticChar (ZMod p) (0 - d) ^ 2 * hc +
        quadraticChar (ZMod p) c ^ 2 * hd)
  simp only [h, weightedMoment_sum_sum_prod, weightedMoment_sum_chi_sq_mul p hp2]
  rw [← weightedMoment_sum_chi_pow4_neg p]
  apply sum_congr rfl
  intro b _
  ring

/-- The inclusion–exclusion over the vanishing labels, pointwise: `χ(v)² = 1 - [v = 0]`, and a
product of indicators of two adjacent labels kills the `G₅` product. -/
theorem weightedMoment_ie_pointwise (b c d e f : ZMod p) :
    quadraticChar (ZMod p) b ^ 2 * quadraticChar (ZMod p) c ^ 2 *
        quadraticChar (ZMod p) d ^ 2 * quadraticChar (ZMod p) e ^ 2 *
        quadraticChar (ZMod p) f ^ 2 * copy5 p b c d e f =
      copy5 p b c d e f - (if b = 0 then copy5 p b c d e f else 0) -
        (if c = 0 then copy5 p b c d e f else 0) - (if d = 0 then copy5 p b c d e f else 0) -
        (if e = 0 then copy5 p b c d e f else 0) - (if f = 0 then copy5 p b c d e f else 0) +
        (if c = 0 ∧ d = 0 then copy5 p b c d e f else 0) +
        (if e = 0 ∧ f = 0 then copy5 p b c d e f else 0) := by
  simp only [weightedMoment_chi_sq_if]
  rcases eq_or_ne b 0 with hb | hb <;> rcases eq_or_ne c 0 with hc | hc <;>
    rcases eq_or_ne d 0 with hd | hd <;> rcases eq_or_ne e 0 with he | he <;>
    rcases eq_or_ne f 0 with hf | hf <;> simp [hb, hc, hd, he, hf, copy5]

theorem weightedMoment_sum_rot3' (F : ZMod p → ZMod p → ZMod p → ℤ) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ y, ∑ z, ∑ x, F x y z := by
  calc ∑ x, ∑ y, ∑ z, F x y z = ∑ y, ∑ x, ∑ z, F x y z := sum_comm
    _ = ∑ y, ∑ z, ∑ x, F x y z := sum_congr rfl fun y _ => sum_comm

/-- `∑_c χ(c)² χ(e-c) χ(f-c) = p[e = f] - 1 - χ(e)χ(f)`. -/
theorem weightedMoment_sum_c_eq (hp2 : p ≠ 2) (e f : ZMod p) :
    ∑ c : ZMod p, quadraticChar (ZMod p) c ^ 2 * quadraticChar (ZMod p) (e - c) *
        quadraticChar (ZMod p) (f - c) =
      (if e = f then (p : ℤ) - 1 else -1) -
        quadraticChar (ZMod p) e * quadraticChar (ZMod p) f := by
  have h : ∀ c : ZMod p, quadraticChar (ZMod p) c ^ 2 * quadraticChar (ZMod p) (e - c) *
      quadraticChar (ZMod p) (f - c) =
      quadraticChar (ZMod p) (c - e) * quadraticChar (ZMod p) (c - f) -
        if c = 0 then quadraticChar (ZMod p) (e - c) * quadraticChar (ZMod p) (f - c) else 0 := by
    intro c
    have hcomm : quadraticChar (ZMod p) (e - c) * quadraticChar (ZMod p) (f - c) =
        quadraticChar (ZMod p) (c - e) * quadraticChar (ZMod p) (c - f) := by
      rw [← map_mul, ← map_mul]
      congr 1
      ring
    rw [weightedMoment_chi_sq_if]
    split_ifs <;> linear_combination hcomm
  simp only [h, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, sub_zero,
    weightedMoment_gram_chi p hp2 e f]

/-- The pointwise evaluation of the summand of the part `ξ₁ = 0`. -/
theorem weightedMoment_r_pointwise (e f : ZMod p) :
    quadraticChar (ZMod p) e ^ 2 * quadraticChar (ZMod p) f ^ 2 *
        ((if e = f then (p : ℤ) - 1 else -1) -
          quadraticChar (ZMod p) e * quadraticChar (ZMod p) f) ^ 2 =
      2 * (quadraticChar (ZMod p) e ^ 2 * quadraticChar (ZMod p) f ^ 2) +
        2 * (quadraticChar (ZMod p) e * quadraticChar (ZMod p) f) +
        (if e = f then quadraticChar (ZMod p) e ^ 2 * ((p : ℤ) ^ 2 - 4 * p) else 0) := by
  by_cases hef : e = f
  · subst hef
    simp only [↓reduceIte]
    rcases weightedMoment_chi_vals p e with h | h | h <;> rw [h] <;> ring
  · simp only [hef, ↓reduceIte, add_zero]
    rcases weightedMoment_chi_vals p e with h | h | h <;>
      rcases weightedMoment_chi_vals p f with h' | h' | h' <;>
      rw [h, h'] <;> ring

/-- **The part `ξ₁ = 0`**: `∑_{a,b ≠ 0} c(a,b)² = (p-1)(p² - 2p - 2)`. -/
theorem weightedMoment_r_eq (hp2 : p ≠ 2) :
    ∑ c, ∑ d, ∑ e, ∑ f, g12 p 0 c d e f = ((p : ℤ) - 1) * ((p : ℤ) ^ 2 - 2 * p - 2) := by
  have hpt : ∀ c d e f : ZMod p, g12 p 0 c d e f =
      (quadraticChar (ZMod p) e ^ 2 * quadraticChar (ZMod p) f ^ 2) *
        (quadraticChar (ZMod p) c ^ 2 * quadraticChar (ZMod p) (e - c) *
          quadraticChar (ZMod p) (f - c)) *
        (quadraticChar (ZMod p) d ^ 2 * quadraticChar (ZMod p) (e - d) *
          quadraticChar (ZMod p) (f - d)) := by
    intro c d e f
    simp only [g12, sub_zero]
    ring
  simp only [hpt]
  have hre : ∀ c : ZMod p, (∑ d, ∑ e, ∑ f,
      (quadraticChar (ZMod p) e ^ 2 * quadraticChar (ZMod p) f ^ 2) *
        (quadraticChar (ZMod p) c ^ 2 * quadraticChar (ZMod p) (e - c) *
          quadraticChar (ZMod p) (f - c)) *
        (quadraticChar (ZMod p) d ^ 2 * quadraticChar (ZMod p) (e - d) *
          quadraticChar (ZMod p) (f - d))) =
      ∑ e, ∑ f, ∑ d, (quadraticChar (ZMod p) e ^ 2 * quadraticChar (ZMod p) f ^ 2) *
        (quadraticChar (ZMod p) c ^ 2 * quadraticChar (ZMod p) (e - c) *
          quadraticChar (ZMod p) (f - c)) *
        (quadraticChar (ZMod p) d ^ 2 * quadraticChar (ZMod p) (e - d) *
          quadraticChar (ZMod p) (f - d)) := fun c => weightedMoment_sum_rot3' p _
  rw [sum_congr rfl fun c _ => hre c, weightedMoment_sum_rot3' p]
  have hcd : ∀ e f : ZMod p, (∑ c, ∑ d,
      (quadraticChar (ZMod p) e ^ 2 * quadraticChar (ZMod p) f ^ 2) *
        (quadraticChar (ZMod p) c ^ 2 * quadraticChar (ZMod p) (e - c) *
          quadraticChar (ZMod p) (f - c)) *
        (quadraticChar (ZMod p) d ^ 2 * quadraticChar (ZMod p) (e - d) *
          quadraticChar (ZMod p) (f - d))) =
      quadraticChar (ZMod p) e ^ 2 * quadraticChar (ZMod p) f ^ 2 *
        ((if e = f then (p : ℤ) - 1 else -1) -
          quadraticChar (ZMod p) e * quadraticChar (ZMod p) f) ^ 2 := by
    intro e f
    rw [weightedMoment_sum_sum_prod, weightedMoment_sum_c_eq p hp2 e f]
    ring
  simp only [hcd]
  simp only [weightedMoment_r_pointwise, sum_add_distrib]
  have A1 : ∑ e : ZMod p, ∑ f : ZMod p,
      2 * (quadraticChar (ZMod p) e ^ 2 * quadraticChar (ZMod p) f ^ 2) =
        2 * (((p : ℤ) - 1) * ((p : ℤ) - 1)) := by
    rw [← weightedMoment_sum_chi_sq p, sum_mul_sum, mul_sum]
    apply sum_congr rfl
    intro e _
    rw [mul_sum]
  have A2 : ∑ e : ZMod p, ∑ f : ZMod p,
      2 * (quadraticChar (ZMod p) e * quadraticChar (ZMod p) f) = 0 := by
    have : (0 : ℤ) = 2 * ((∑ e : ZMod p, quadraticChar (ZMod p) e) *
        ∑ f : ZMod p, quadraticChar (ZMod p) f) := by
      rw [weightedMoment_sum_chi p hp2]
      ring
    rw [this, sum_mul_sum, mul_sum]
    apply sum_congr rfl
    intro e _
    rw [mul_sum]
  have A3 : ∑ e : ZMod p, ∑ f : ZMod p,
      (if e = f then quadraticChar (ZMod p) e ^ 2 * ((p : ℤ) ^ 2 - 4 * p) else 0) =
        ((p : ℤ) - 1) * ((p : ℤ) ^ 2 - 4 * p) := by
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    rw [← sum_mul, weightedMoment_sum_chi_sq p]
  rw [A1, A2, A3]
  ring

/-- **The assembly**: `∑_{ξ₁,…,ξ₅} Φ = (p⁵ - 5p⁴) M_{G₅} + (p-1)(p² - 2p)` at `ξ₀ = 0`, i.e.
`(p - 5) S₄ + (p - 1)(p² - 2p)` with `S₄ = p⁴ M_{G₅}`. -/
theorem weightedMoment_sum_g12 (hp2 : p ≠ 2) : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g12 p b c d e f =
    ((p : ℤ) - 5) * s4 p + ((p : ℤ) - 1) * ((p : ℤ) ^ 2 - 2 * p) := by
  have h1 : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g12 p b c d e f =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ((if b = 0 then g12 p b c d e f else 0) +
        (if b = 0 then 0 else g12 p b c d e f)) := by
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro f _
    split_ifs <;> simp
  rw [h1]
  simp only [sum_add_distrib]
  have hR : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, (if b = 0 then g12 p b c d e f else 0) =
      ((p : ℤ) - 1) * ((p : ℤ) ^ 2 - 2 * p - 2) := by
    simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ↓reduceIte]
    exact weightedMoment_r_eq p hp2
  have hall : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, copy5 p b c d e f = (p : ℤ) * s4 p := by
    have : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, copy5 p b c d e f = sG5 p := rfl
    rw [this, weightedMoment_sG5_translate]
    rfl
  have hQ : ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, (if b = 0 then 0 else g12 p b c d e f) =
      (p : ℤ) * s4 p - 5 * s4 p + 2 * ((p : ℤ) - 1) := by
    have hinv := weightedMoment_sum_inv5 p (fun b c d e f => if b = 0 then 0 else g12 p b c d e f)
    rw [← hinv]
    simp only [weightedMoment_g12_inv, weightedMoment_ie_pointwise, sum_add_distrib,
      sum_sub_distrib]
    rw [weightedMoment_slice_b, weightedMoment_slice_c, weightedMoment_slice_d,
      weightedMoment_slice_e, weightedMoment_slice_f, weightedMoment_slice_cd p hp2,
      weightedMoment_slice_ef p hp2, hall]
    ring
  rw [hR, hQ]
  ring

/-- `M_{G₁₂} = p⁻⁶ ∑_{ξ ∈ 𝔽_p⁶} ∏_{uv ∈ G₁₂} χ(ξ_v - ξ_u)`. -/
noncomputable def mG12 : ℝ := (sG12 p : ℝ) / (p : ℝ) ^ 6

/-- **`lem:record:weighted-moment`(b), the inversion identity**, proved in full for every odd
prime: `M_{G₁₂} = (1 - 5q) M_{G₅} + q²(1-q)(1-2q)`, `q = 1/p`. -/
theorem weightedMoment_mG12_inversion (hp2 : p ≠ 2) {q : ℝ} (hq : q = 1 / (p : ℝ)) :
    mG12 p = (1 - 5 * q) * mG5 p + q ^ 2 * (1 - q) * (1 - 2 * q) := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  unfold mG12 mG5
  rw [weightedMoment_sG12_translate, weightedMoment_sum_g12 p hp2, weightedMoment_sG5_translate, hq]
  have hs : (∑ b, ∑ c, ∑ d, ∑ e, g5 p b c d e) = s4 p := rfl
  rw [hs]
  push_cast
  field_simp


/-- **`lem:record:weighted-moment`(b), the final bound, at the actual graph moments, with the
inversion identity proved.** For an odd prime `p`, H3 (`Target.AhlgrenOno`) and the identity
`eq:record:weighted-identity` for `E = E[P_adm 𝒲²]/p²` at the actual moments `M_{G₅}`, `M_{G₁₂}`,
`M_{G₁₀}` (the only remaining **hypothesis**: `cert:record:weighted-identity`) give
`E ≤ 5q + 34qr + 11q³`, and `E` equals the displayed identity of (b). -/
theorem weightedMoment_b_final (hAO : Target.AhlgrenOno) (hp2 : p ≠ 2) {q r E : ℝ}
    (hq : q = 1 / (p : ℝ)) (hr : r * Real.sqrt p = 1)
    (hid : E = (4 + 8 * q) * mG5 p + mG12 p + 24 * mG10 p + 5 * q - 4 * q ^ 2 +
      14 * q ^ 3 - 15 * q ^ 4) :
    E = (5 + 3 * q) * mG5 p + 24 * mG10 p + 5 * q - 3 * q ^ 2 + 11 * q ^ 3 - 13 * q ^ 4 ∧
      E ≤ 5 * q + 34 * q * r + 11 * q ^ 3 :=
  ⟨weightedMoment_b_identity hid (weightedMoment_mG12_inversion p hp2 hq),
    weightedMoment_b_of_H3 p hAO hp2 hq hr hid (weightedMoment_mG12_inversion p hp2 hq)⟩


/-! ### (a): the bounds `|M_{G₅}|, |M_{G₁₂}| ≤ q` without H3 -/

/-- `∑_λ T_λ² ≤ p²` (`T = -Hv` with `‖v‖² ≤ p` and the Gram identity; from the proof of the
bound for `M_{G₁₀}`). -/
theorem weightedMoment_sum_T_sq_le (hp2 : p ≠ 2) :
    ∑ x : ZMod p, Target.legendreSum p x ^ 2 ≤ (p : ℤ) ^ 2 := by
  set v : ZMod p → ℤ := fun y => quadraticChar (ZMod p) y * quadraticChar (ZMod p) (y - 1)
    with hv
  have hTv : ∀ x, Target.legendreSum p x = ∑ y, quadraticChar (ZMod p) (y - x) * v y := by
    intro x
    simp only [hv, Target.legendreSum, map_mul]
    apply sum_congr rfl
    intro y _
    ring
  have hK' : ∀ y y' : ZMod p,
      ∑ x, quadraticChar (ZMod p) (y - x) * quadraticChar (ZMod p) (y' - x) =
      if y = y' then (p : ℤ) - 1 else -1 := by
    intro y y'
    rw [← weightedMoment_gram_chi p hp2 y y']
    apply sum_congr rfl
    intro x _
    rw [← map_mul, ← map_mul]
    congr 1
    ring
  have hg2 := weightedMoment_gram_sum p (fun x y => quadraticChar (ZMod p) (y - x)) hK' v
  have hvsq : ∑ y, v y ^ 2 ≤ (p : ℤ) := by
    have : ∀ y, v y ^ 2 ≤ 1 := by
      intro y
      simp only [hv, mul_pow]
      have h1 := weightedMoment_chi_sq_le_one p y
      have h2 := weightedMoment_chi_sq_le_one p (y - 1)
      have h3 : 0 ≤ quadraticChar (ZMod p) y ^ 2 := sq_nonneg _
      nlinarith
    calc ∑ y, v y ^ 2 ≤ ∑ _y : ZMod p, (1 : ℤ) := sum_le_sum fun y _ => this y
      _ = p := by rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  simp only [hTv]
  have : ∑ x, (∑ y, quadraticChar (ZMod p) (y - x) * v y) ^ 2 =
      (p : ℤ) * ∑ y, v y ^ 2 - (∑ y, v y) ^ 2 := hg2
  rw [this]
  nlinarith [sq_nonneg (∑ y, v y)]

/-- **`lem:record:weighted-moment`(a), `|M_{G₅}| ≤ q`**, unconditionally, for every odd prime, by
a route different from the paper's kernel bound: by the modular evaluation,
`|M_{G₅}| ≤ (p-1)/p⁴ · ∑_λ T_λ² ≤ (p-1)/p² = q - q²`. -/
theorem weightedMoment_mG5_abs_le (hp2 : p ≠ 2) {q : ℝ} (hq : q = 1 / (p : ℝ)) :
    |mG5 p| ≤ q - q ^ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hS : |∑ t : ZMod p, quadraticChar (ZMod p) t * Target.legendreSum p t ^ 2| ≤
      (p : ℤ) ^ 2 := by
    calc |∑ t : ZMod p, quadraticChar (ZMod p) t * Target.legendreSum p t ^ 2|
        ≤ ∑ t : ZMod p, |quadraticChar (ZMod p) t * Target.legendreSum p t ^ 2| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ t : ZMod p, Target.legendreSum p t ^ 2 := by
          apply sum_le_sum
          intro t _
          rw [abs_mul, abs_of_nonneg (sq_nonneg (Target.legendreSum p t))]
          have : |quadraticChar (ZMod p) t| ≤ 1 := by
            rcases weightedMoment_chi_vals p t with h | h | h <;> rw [h] <;> norm_num
          exact mul_le_of_le_one_left (sq_nonneg _) this
      _ ≤ (p : ℤ) ^ 2 := weightedMoment_sum_T_sq_le p hp2
  have hS' : |((∑ t : ZMod p, quadraticChar (ZMod p) t * Target.legendreSum p t ^ 2 : ℤ) : ℝ)| ≤
      (p : ℝ) ^ 2 := by
    rw [← Int.cast_abs]
    exact_mod_cast hS
  rw [weightedMoment_mG5_eq, abs_mul, abs_of_nonneg (div_nonneg (by linarith) (by positivity))]
  calc ((p : ℝ) - 1) / (p : ℝ) ^ 4 *
        |((∑ t : ZMod p, quadraticChar (ZMod p) t * Target.legendreSum p t ^ 2 : ℤ) : ℝ)|
      ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 4 * (p : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hS' (div_nonneg (by linarith) (by positivity))
    _ = q - q ^ 2 := by
        rw [hq]
        field_simp

/-- **`lem:record:weighted-moment`(a), `|M_{G₁₂}| ≤ q`**, unconditionally, for every odd prime:
from the inversion identity and `|M_{G₅}| ≤ q - q²`. -/
theorem weightedMoment_mG12_abs_le (hp2 : p ≠ 2) {q : ℝ} (hq : q = 1 / (p : ℝ)) :
    |mG12 p| ≤ q := by
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq3 : q ≤ 1 / 3 := by
    rw [hq]
    exact one_div_le_one_div_of_le (by norm_num) hp3
  have hm := abs_le.mp (weightedMoment_mG5_abs_le p hp2 hq)
  rw [weightedMoment_mG12_inversion p hp2 hq, abs_le]
  have hpos : 0 ≤ q ^ 2 * (1 - q) * (1 - 2 * q) := by
    have : 0 ≤ 1 - q := by linarith
    have : 0 ≤ 1 - 2 * q := by linarith
    positivity
  have hsmall : q ^ 2 * (1 - q) * (1 - 2 * q) ≤ q ^ 2 := by
    have h1 : (1 - q) * (1 - 2 * q) ≤ 1 := by nlinarith
    nlinarith
  rcases le_or_gt q (1 / 5) with h5 | h5
  · have hc : 0 ≤ 1 - 5 * q := by linarith
    have u := mul_le_mul_of_nonneg_left hm.2 hc
    have l := mul_le_mul_of_nonneg_left hm.1 hc
    constructor <;> nlinarith
  · have hc : 0 ≤ 5 * q - 1 := by linarith
    have u := mul_le_mul_of_nonneg_left hm.2 hc
    have l := mul_le_mul_of_nonneg_left hm.1 hc
    constructor <;> nlinarith

/-- **`lem:record:weighted-moment`(a), in full at the actual moments**: for an odd prime, the
identity `eq:record:weighted-identity` (the only **hypothesis**, `cert:record:weighted-identity`)
gives `E[P_adm 𝒲²]/p² ≤ 10q + 24qr + 4q² + 14q³`; the three moment bounds are proved here
(without H3). -/
theorem weightedMoment_a_final (hp2 : p ≠ 2) {q r E : ℝ} (hq : q = 1 / (p : ℝ))
    (hr : r * Real.sqrt p = 1)
    (hid : E = (4 + 8 * q) * mG5 p + mG12 p + 24 * mG10 p + 5 * q - 4 * q ^ 2 +
      14 * q ^ 3 - 15 * q ^ 4) :
    E ≤ 10 * q + 24 * q * r + 4 * q ^ 2 + 14 * q ^ 3 := by
  have h5 : |mG5 p| ≤ q := (weightedMoment_mG5_abs_le p hp2 hq).trans (by nlinarith)
  exact weightedMoment_a hid h5 (weightedMoment_mG12_abs_le p hp2 hq)
    (weightedMoment_mG10_bound p hp2 hq hr)

end G12

end WeightedMoment

end Sarkozy.Variance
