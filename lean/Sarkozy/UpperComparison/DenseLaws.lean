module

public import Sarkozy.UpperComparison.ForestRecords
public import Sarkozy.PartVRecords.DenseComparison

@[expose] public section

/-!
# Replacements keeping the old cross edges (`prop:dense-comparison`)

`paper/sections/26_upper_comparison.tex`, paragraph "Dense laws", `prop:dense-comparison`,
parts (a), (b), (c), for a softening `K₁ = K_{D₁}` of an LE or EL record of degree two
(`def:dense-comparison`, formalized by V3 in `Sarkozy/PartVRecords/DenseComparison.lean`).

**Framework.** As in `Sarkozy/UpperComparison/ForestRecords.lean`: `ν = μ = λ_H` is a `FiniteLaw X`,
kernels are relative to `ν ⊗ ν`, operators are bilinear forms (`kform`), and the old actual half
marginal is `m₀ = g₀μ = (1 + u₀)μ`.

**Inputs taken as hypotheses** (the paper's citations; not formalized here):
* `cor:soft-kernels` and `cor:star-matrix`: on centred functions the raw kernel `H_{D_h}` has the
  form `Lead_h + Rem_h`, where `Lead_h = r 𝓕 M_h(Φ̂) 𝓕^*` is its doubly centred complete star part,
  with `‖Lead_h‖ ≤ Γ k_h r`, `‖Sym(Lead₁ - Lead₀)‖ ≤ Γ k_s r`, `‖Skew(Lead₁ - Lead₀)‖ ≤ Γ k_a r`,
  and `‖Rem_h‖ ≤ ℛ_h` (the nonstar and collision parts);
* the two-root identity and `thm:weil`: `|Z_{D_h} - 1| ≤ ε_h < 1/2`;
* `lem:wt:stars` (paragraph "Marginals"): `‖g_{1,L} - 1‖, ‖g_{1,R} - 1‖ ≤ u₁`;
* `lem:tr:repair`(g): multipliers `f`, `g` with `‖f‖_∞, ‖g‖_∞ ≤ F_N` such that `K₁'` has both half
  marginals `m₀`; and the old law `K₀` has both half marginals `m₀`, `m₀ ≥ e^{-ℓ₀}μ`.

**Proved.**
* The constants of the proposition: `denseEps`, `denseC`, `denseU`, `denseKinf`, `denseRhoI`,
  `denseEI`, `denseFN`, `denseE`, `denseD`, `denseC0`; the gates of (c), `DenseBlockGates`.
* **`dense_comparison_a`**: part (a) from the output of `lem:tr:repair`(g): `K₁'` is a nonnegative
  probability coupling of `m₀` with itself, supported where `K₁ > 0`; with
  **`dense_accepts_required`**: for `K₁ = K_{D₁}` the softening of `def:dense-comparison`, every
  required query holds on the support (V3's `Hdense_support_req`).
* `dense_centred_kernel`: `‖K_c‖ ≤ C₁` for the normalized new kernel.
* **`dense_comparison_b`**: part (b), the symmetric and skew parts of the change `K₁' - K₀` have
  norms at most `d_s` and `d_a` relative to `m₀`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperComparison

open Sarkozy.Recentering Sarkozy.Structured

variable {X : Type*} [Fintype X]

/-! ## The constants of `prop:dense-comparison` -/

/-- `ε_h = T_{2,h} q + T_{>,h} r + ℛ_h`. -/
noncomputable def denseEps (T2 Tgt q r R : ℝ) : ℝ := T2 * q + Tgt * r + R

/-- `C_h = (Γ k_h r + ℛ_h)/z_h`. -/
noncomputable def denseC (Γ k r R z : ℝ) : ℝ := (Γ * k * r + R) / z

/-- `u_h = (W_h + ℛ_h)/z_h`. -/
noncomputable def denseU (W R z : ℝ) : ℝ := (W + R) / z

/-- `K_∞ = (2^{m_×} e^{2ℓ₁}/z₁)^{1/2}`. -/
noncomputable def denseKinf (mx : ℕ) (ℓ1 z1 : ℝ) : ℝ := Real.sqrt (2 ^ mx * Real.exp (2 * ℓ1) / z1)

/-- `ρ_I = e^{ℓ₁}(ℛ₁/z₁ + u₁²)`. -/
noncomputable def denseRhoI (ℓ1 R1 z1 u1 : ℝ) : ℝ := Real.exp ℓ1 * (R1 / z1 + u1 ^ 2)

/-- `e_I = (1 + ρ_I) e^{ℓ₁/2}(u₀ + u₁)`. -/
noncomputable def denseEI (ρI ℓ1 u0 u1 : ℝ) : ℝ := (1 + ρI) * Real.exp (ℓ1 / 2) * (u0 + u1)

/-- `F_N = 2NU + K_∞ ρ_I^{2N-1} e_I/(1 - ρ_I²)`. -/
noncomputable def denseFN (N : ℕ) (U Kinf ρI eI : ℝ) : ℝ :=
  2 * N * U + Kinf * ρI ^ (2 * N - 1) * eI / (1 - ρI ^ 2)

/-- `E = ∑_h (ℛ_h + ε_h (Γ k_h r + ℛ_h)/z_h)` of `prop:dense-comparison`(b). -/
noncomputable def denseE (Γ k0 k1 r R0 R1 ε0 ε1 z0 z1 : ℝ) : ℝ :=
  (R0 + ε0 * (Γ * k0 * r + R0) / z0) + (R1 + ε1 * (Γ * k1 * r + R1) / z1)

/-- `d_s = e^{ℓ₀}(Γ k_s r + E + 2F_N(C₁ + u₁))` (and `d_a` with `k_a`). -/
noncomputable def denseD (ℓ0 Γ k r E FN C1 u1 : ℝ) : ℝ :=
  Real.exp ℓ0 * (Γ * k * r + E + 2 * FN * (C1 + u1))

/-- `c₀ = e^{ℓ₀}(C₀ + u₀²)`, the bound for the actual centred norm of the old law. -/
noncomputable def denseC0 (ℓ0 C0 u0 : ℝ) : ℝ := Real.exp ℓ0 * (C0 + u0 ^ 2)

/-- **`prop:dense-comparison`(c), the block gates**: with `c₁ = c₀ + d_s + d_a`,
`max(c₀, c₁) < 1/2` and `c₀² + c₁² < min(k_s, k_a) r`. A numerical condition, checked by the
certificates at the endpoints and used in `lem:record:domain`(ii). -/
def DenseBlockGates (c0 ds da ks ka r : ℝ) : Prop :=
  max c0 (c0 + ds + da) < 1 / 2 ∧ c0 ^ 2 + (c0 + ds + da) ^ 2 < min ks ka * r

/-! ## Part (a) -/

/-- **`prop:dense-comparison`(a)**, given the output of `lem:tr:repair`(g) (hypotheses: the
multipliers `f`, `g` with `‖f‖_∞, ‖g‖_∞ ≤ F_N`, `2F_N < 1`, and the two marginal equations of the
repaired kernel, `m₀ = (1 + u₀)μ` with `E_μ u₀ = 0`), and `K₁ ≥ 0`: the repaired kernel
`K₁' = (1 + f(x) + g(y))K₁` is nonnegative, has mass one and both half marginals `m₀`, and is
supported where `K₁ ≠ 0`. -/
theorem dense_comparison_a (ν : FiniteLaw X) (K₁ K₁' : X × X → ℝ) (hK₁ : ∀ p, 0 ≤ K₁ p)
    {FN : ℝ} (hFN : 2 * FN < 1) (f g : X → ℝ) (hf : ∀ x, |f x| ≤ FN) (hg : ∀ y, |g y| ≤ FN)
    (hK' : ∀ p, K₁' p = (1 + f p.1 + g p.2) * K₁ p) (u0 : X → ℝ) (hu00 : ν.expect u0 = 0)
    (hm1 : ∀ x, ν.expect (fun y => K₁' (x, y)) = 1 + u0 x)
    (hm2 : ∀ y, ν.expect (fun x => K₁' (x, y)) = 1 + u0 y) :
    (∀ p, 0 ≤ K₁' p) ∧ ν.expect (fun x => ν.expect (fun y => K₁' (x, y))) = 1 ∧
      (∀ x, ν.expect (fun y => K₁' (x, y)) = 1 + u0 x) ∧
      (∀ y, ν.expect (fun x => K₁' (x, y)) = 1 + u0 y) ∧
      ∀ p, K₁' p ≠ 0 → K₁ p ≠ 0 := by
  have hpos : ∀ p : X × X, 0 < 1 + f p.1 + g p.2 := by
    intro p
    have h1 := abs_le.mp (hf p.1)
    have h2 := abs_le.mp (hg p.2)
    linarith
  refine ⟨fun p => by rw [hK']; exact mul_nonneg (hpos p).le (hK₁ p), ?_, hm1, hm2, ?_⟩
  · rw [ν.expect_congr hm1, ν.expect_add, ν.expect_const, hu00, add_zero]
  · intro p hp h0
    exact hp (by rw [hK', h0, mul_zero])

section Acceptance

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq] {n : ℕ}

/-- **Acceptance** (`prop:dense-comparison`(a), "it accepts the required queries"): for the
softening `D₁ = soften D₀ req β β̃` of `def:dense-comparison` and `K₁ = K_{D₁}` (V3's `Kdense`),
every pair `(x, y)` in the support of the repaired kernel `K₁' = (1 + f(x) + g(y))K₁` satisfies
every required query: `χ(y_j - x_i) = 1` for `(i, j)` required. -/
theorem dense_accepts_required (μ : FiniteLaw (Fin n → Fq)) (D₀ : Fin n → Fin n → ℝ)
    (req : Finset (Fin n × Fin n)) (β βt : ℝ) (f g : (Fin n → Fq) → ℝ)
    {x y : Fin n → Fq}
    (hxy : (1 + f x + g y) * PartVRecords.Kdense μ (PartVRecords.soften D₀ req β βt) x y ≠ 0)
    {i j : Fin n} (hij : (i, j) ∈ req) : quadraticChar Fq (y j - x i) = 1 := by
  have hK : PartVRecords.Kdense μ (PartVRecords.soften D₀ req β βt) x y ≠ 0 := by
    intro h; exact hxy (by rw [h, mul_zero])
  have hH : PartVRecords.Hdense (PartVRecords.soften D₀ req β βt) x y ≠ 0 := by
    intro h; apply hK; unfold PartVRecords.Kdense; rw [h, zero_div]
  exact PartVRecords.Hdense_support_req D₀ req β βt hH hij

end Acceptance

/-! ## Part (b) -/

/-- **The centred new kernel**: `K₁ = H₁/Z₁` with `kform H₁ = Lead₁ + Rem₁` on centred functions,
`‖Lead₁‖ ≤ Γ k₁ r`, `‖Rem₁‖ ≤ ℛ₁` and `Z₁ ≥ z₁ > 0` has `‖K_c‖ ≤ C₁ = (Γ k₁ r + ℛ₁)/z₁`
(proof of `prop:dense-comparison`, "Normalizing each kernel by its own `Z_{D_h}`"). -/
theorem dense_centred_kernel (ν : FiniteLaw X) (H₁ K₁ : X × X → ℝ) (Z₁ : ℝ)
    (hK₁ : ∀ p, K₁ p = H₁ p / Z₁) (Lead₁ Rem₁ : (X → ℝ) → (X → ℝ) → ℝ)
    (hdec : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → kform ν ν H₁ φ ψ = Lead₁ φ ψ + Rem₁ φ ψ)
    {Γ k₁ r R₁ z₁ : ℝ} (hz : 0 < z₁) (hZ : z₁ ≤ Z₁)
    (hL : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Lead₁ φ ψ| ≤ Γ * k₁ * r * nrm ν φ * nrm ν ψ)
    (hR : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Rem₁ φ ψ| ≤ R₁ * nrm ν φ * nrm ν ψ)
    (φ ψ : X → ℝ) (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    |kform ν ν (centeredKernel ν K₁) φ ψ| ≤ denseC Γ k₁ r R₁ z₁ * nrm ν φ * nrm ν ψ := by
  rw [← kform_eq_centeredKernel ν K₁ φ ψ hφ hψ, kform_normalized ν H₁ K₁ Z₁ hK₁,
    hdec φ ψ hφ hψ]
  have hZpos : 0 < Z₁ := hz.trans_le hZ
  have hsum : |Lead₁ φ ψ + Rem₁ φ ψ| ≤ (Γ * k₁ * r + R₁) * nrm ν φ * nrm ν ψ := by
    have := abs_add_le (Lead₁ φ ψ) (Rem₁ φ ψ)
    have h1 := hL φ ψ hφ hψ
    have h2 := hR φ ψ hφ hψ
    linarith
  have hnn : 0 ≤ (Γ * k₁ * r + R₁) * nrm ν φ * nrm ν ψ := (abs_nonneg _).trans hsum
  rw [abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
  unfold denseC
  calc |Lead₁ φ ψ + Rem₁ φ ψ| ≤ (Γ * k₁ * r + R₁) * nrm ν φ * nrm ν ψ := hsum
    _ = (Γ * k₁ * r + R₁) / z₁ * nrm ν φ * nrm ν ψ * z₁ := by field_simp
    _ ≤ (Γ * k₁ * r + R₁) / z₁ * nrm ν φ * nrm ν ψ * Z₁ := by
        apply mul_le_mul_of_nonneg_left hZ
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
        exact div_nonneg hnn hz.le

/-- **`prop:dense-comparison`(b)**. Inputs (hypotheses, see the module docstring):
the raw kernels `H_h = H_{D_h}` with `Z_h = ∫H_h`, `K_h = H_h/Z_h`, `|Z_h - 1| ≤ ε_h < 1/2`; on
centred functions `kform H_h = Lead_h + Rem_h` with `‖Lead_h‖ ≤ Γ k_h r` (`k₁ = k₀ + k_s + k_a` in
the paper), `‖Sym(Lead₁ - Lead₀)‖ ≤ Γ k_s r`, `‖Skew(Lead₁ - Lead₀)‖ ≤ Γ k_a r`, `‖Rem_h‖ ≤ ℛ_h`;
the raw marginal defects of `K₁` at most `u₁`; the repair `K₁' = (1 + f + g)K₁` with
`‖f‖_∞, ‖g‖_∞ ≤ F_N` and both half marginals `m₀ = (1 + u₀)μ`, which are also those of `K₀`;
`m₀ ≥ e^{-ℓ₀}μ`. Conclusion: relative to `m₀`, the change `K₁' - K₀` has symmetric part of norm at
most `d_s` and skew part of norm at most `d_a` (`z_h = 1 - ε_h`). The proof is the two-normalizer
estimate (`two_normalizer_sym`, giving `Γ k_s r + E` and `Γ k_a r + E`) followed by
`lem:record:centered-correction`(c) with `K = K₁`, `O = K₀`, `c = C₁`, `e = u₁`, `F = F_N`. -/
theorem dense_comparison_b (ν : FiniteLaw X) (H₀ H₁ K₀ K₁ K₁' : X × X → ℝ) (Z₀ Z₁ : ℝ)
    (hZ₁def : Z₁ = ν.expect (fun x => ν.expect (fun y => H₁ (x, y))))
    (hK₀ : ∀ p, K₀ p = H₀ p / Z₀) (hK₁ : ∀ p, K₁ p = H₁ p / Z₁)
    (Lead₀ Lead₁ Rem₀ Rem₁ : (X → ℝ) → (X → ℝ) → ℝ)
    (hdec₀ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → kform ν ν H₀ φ ψ = Lead₀ φ ψ + Rem₀ φ ψ)
    (hdec₁ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → kform ν ν H₁ φ ψ = Lead₁ φ ψ + Rem₁ φ ψ)
    {Γ k₀ k₁ ks ka r R₀ R₁ ε₀ ε₁ u₁ FN ℓ₀ : ℝ}
    (hk₀ : 0 ≤ Γ * k₀ * r) (hk₁ : 0 ≤ Γ * k₁ * r) (hks : 0 ≤ Γ * ks * r) (hka : 0 ≤ Γ * ka * r)
    (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁)
    (hL₀ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Lead₀ φ ψ| ≤ Γ * k₀ * r * nrm ν φ * nrm ν ψ)
    (hL₁ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Lead₁ φ ψ| ≤ Γ * k₁ * r * nrm ν φ * nrm ν ψ)
    (hLs : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |((Lead₁ φ ψ - Lead₀ φ ψ) + (Lead₁ ψ φ - Lead₀ ψ φ)) / 2| ≤
        Γ * ks * r * nrm ν φ * nrm ν ψ)
    (hLa : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |((Lead₁ φ ψ - Lead₀ φ ψ) - (Lead₁ ψ φ - Lead₀ ψ φ)) / 2| ≤
        Γ * ka * r * nrm ν φ * nrm ν ψ)
    (hRm₀ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Rem₀ φ ψ| ≤ R₀ * nrm ν φ * nrm ν ψ)
    (hRm₁ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Rem₁ φ ψ| ≤ R₁ * nrm ν φ * nrm ν ψ)
    (hZ₀ : |Z₀ - 1| ≤ ε₀) (hZ₁ : |Z₁ - 1| ≤ ε₁) (hε₀ : ε₀ < 1 / 2) (hε₁ : ε₁ < 1 / 2)
    (hδL : nrm ν (deltaL ν K₁) ≤ u₁) (hδR : nrm ν (deltaR ν K₁) ≤ u₁)
    (hFN : 0 ≤ FN) (f g : X → ℝ) (hf : ∀ x, |f x| ≤ FN) (hg : ∀ y, |g y| ≤ FN)
    (hK' : ∀ p, K₁' p = (1 + f p.1 + g p.2) * K₁ p) (u0 : X → ℝ)
    (hm1 : ∀ x, ν.expect (fun y => K₁' (x, y)) = 1 + u0 x)
    (hm2 : ∀ y, ν.expect (fun x => K₁' (x, y)) = 1 + u0 y)
    (hO1 : ∀ x, ν.expect (fun y => K₀ (x, y)) = 1 + u0 x)
    (hO2 : ∀ y, ν.expect (fun x => K₀ (x, y)) = 1 + u0 y)
    (hu : ∀ x, Real.exp (-ℓ₀) ≤ 1 + u0 x) (φ ψ : X → ℝ) :
    |((centredForm ν u0 K₁' φ ψ - centredForm ν u0 K₀ φ ψ) +
        (centredForm ν u0 K₁' ψ φ - centredForm ν u0 K₀ ψ φ)) / 2| ≤
      denseD ℓ₀ Γ ks r (denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) FN
          (denseC Γ k₁ r R₁ (1 - ε₁)) u₁ * mnrm ν u0 φ * mnrm ν u0 ψ ∧
    |((centredForm ν u0 K₁' φ ψ - centredForm ν u0 K₀ φ ψ) -
        (centredForm ν u0 K₁' ψ φ - centredForm ν u0 K₀ ψ φ)) / 2| ≤
      denseD ℓ₀ Γ ka r (denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) FN
          (denseC Γ k₁ r R₁ (1 - ε₁)) u₁ * mnrm ν u0 φ * mnrm ν u0 ψ := by
  have hε₀1 : ε₀ < 1 := by linarith
  have hε₁1 : ε₁ < 1 := by linarith
  have hε₀0 : 0 ≤ ε₀ := (abs_nonneg _).trans hZ₀
  have hε₁0 : 0 ≤ ε₁ := (abs_nonneg _).trans hZ₁
  have hz₁ : 0 < 1 - ε₁ := by linarith
  have hz₀ : 0 < 1 - ε₀ := by linarith
  have hZ₁lo : 1 - ε₁ ≤ Z₁ := by have := abs_le.mp hZ₁; linarith
  have hZ₁pos : 0 < Z₁ := hz₁.trans_le hZ₁lo
  have hmass : ν.expect (fun x => ν.expect (fun y => K₁ (x, y))) = 1 :=
    raw_kernel_mass ν H₁ K₁ Z₁ hZ₁def hZ₁pos.ne' hK₁
  have hKc := dense_centred_kernel ν H₁ K₁ Z₁ hK₁ Lead₁ Rem₁ hdec₁ hz₁ hZ₁lo hL₁ hRm₁
  have hc : 0 ≤ denseC Γ k₁ r R₁ (1 - ε₁) := div_nonneg (add_nonneg hk₁ hR₁) hz₁.le
  -- the forms of `K_h` on centred functions
  have hf₁ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      kform ν ν K₁ φ ψ = (Lead₁ φ ψ + Rem₁ φ ψ) / Z₁ := by
    intro φ ψ hφ hψ; rw [kform_normalized ν H₁ K₁ Z₁ hK₁, hdec₁ φ ψ hφ hψ]
  have hf₀ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      kform ν ν K₀ φ ψ = (Lead₀ φ ψ + Rem₀ φ ψ) / Z₀ := by
    intro φ ψ hφ hψ; rw [kform_normalized ν H₀ K₀ Z₀ hK₀, hdec₀ φ ψ hφ hψ]
  have hU₁ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |Lead₁ φ ψ + Rem₁ φ ψ| ≤ (Γ * k₁ * r + R₁) * nrm ν φ * nrm ν ψ := by
    intro φ ψ hφ hψ
    have := abs_add_le (Lead₁ φ ψ) (Rem₁ φ ψ)
    have h1 := hL₁ φ ψ hφ hψ
    have h2 := hRm₁ φ ψ hφ hψ
    linarith
  have hU₀ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |Lead₀ φ ψ + Rem₀ φ ψ| ≤ (Γ * k₀ * r + R₀) * nrm ν φ * nrm ν ψ := by
    intro φ ψ hφ hψ
    have := abs_add_le (Lead₀ φ ψ) (Rem₀ φ ψ)
    have h1 := hL₀ φ ψ hφ hψ
    have h2 := hRm₀ φ ψ hφ hψ
    linarith
  -- the two-normalizer estimate, for both parts
  have hpart : ∀ (τ k : ℝ), |τ| ≤ 1 →
      (∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
        |((Lead₁ φ ψ - Lead₀ φ ψ) + τ * (Lead₁ ψ φ - Lead₀ ψ φ)) / 2| ≤
          Γ * k * r * nrm ν φ * nrm ν ψ) →
      ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
        |(kform ν ν (fun p => K₁ p - K₀ p) φ ψ + τ * kform ν ν (fun p => K₁ p - K₀ p) ψ φ) / 2| ≤
          (Γ * k * r + denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) * nrm ν φ * nrm ν ψ := by
    intro τ k hτ hLk φ ψ hφ hψ
    rw [kform_sub, kform_sub, hf₁ φ ψ hφ hψ, hf₁ ψ φ hψ hφ, hf₀ φ ψ hφ hψ, hf₀ ψ φ hψ hφ]
    have key := two_normalizer_sym (n := nrm ν φ * nrm ν ψ) hτ rfl rfl rfl rfl
      (bound_assoc hLk φ ψ hφ hψ)
      (bound_assoc hRm₁ φ ψ hφ hψ) (bound_swap hRm₁ φ ψ hφ hψ)
      (bound_assoc hRm₀ φ ψ hφ hψ) (bound_swap hRm₀ φ ψ hφ hψ)
      (bound_assoc hU₁ φ ψ hφ hψ) (bound_swap hU₁ φ ψ hφ hψ)
      (bound_assoc hU₀ φ ψ hφ hψ) (bound_swap hU₀ φ ψ hφ hψ) hZ₁ hZ₀ hε₁1 hε₀1
    have e : (Γ * k * r + denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) * nrm ν φ * nrm ν ψ =
        (Γ * k * r + R₁ + R₀ + ε₁ * (Γ * k₁ * r + R₁) / (1 - ε₁) +
          ε₀ * (Γ * k₀ * r + R₀) / (1 - ε₀)) * (nrm ν φ * nrm ν ψ) := by
      unfold denseE; ring
    rw [e]
    exact key
  have hKOs : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν (fun p => K₁ p - K₀ p) φ ψ + kform ν ν (fun p => K₁ p - K₀ p) ψ φ) / 2| ≤
        (Γ * ks * r + denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) * nrm ν φ * nrm ν ψ := by
    intro φ ψ hφ hψ
    have := hpart 1 ks (by norm_num) (fun φ ψ hφ hψ => by rw [one_mul]; exact hLs φ ψ hφ hψ)
      φ ψ hφ hψ
    rwa [one_mul] at this
  have hKOa : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν (fun p => K₁ p - K₀ p) φ ψ - kform ν ν (fun p => K₁ p - K₀ p) ψ φ) / 2| ≤
        (Γ * ka * r + denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) * nrm ν φ * nrm ν ψ := by
    intro φ ψ hφ hψ
    have := hpart (-1) ka (by norm_num)
      (fun φ ψ hφ hψ => by rw [neg_one_mul, ← sub_eq_add_neg]; exact hLa φ ψ hφ hψ) φ ψ hφ hψ
    rwa [neg_one_mul, ← sub_eq_add_neg] at this
  have hE : 0 ≤ denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁) := by
    unfold denseE
    have a : 0 ≤ ε₀ * (Γ * k₀ * r + R₀) / (1 - ε₀) :=
      div_nonneg (mul_nonneg hε₀0 (add_nonneg hk₀ hR₀)) hz₀.le
    have b : 0 ≤ ε₁ * (Γ * k₁ * r + R₁) / (1 - ε₁) :=
      div_nonneg (mul_nonneg hε₁0 (add_nonneg hk₁ hR₁)) hz₁.le
    linarith
  have hT := centered_transport_difference ν K₁ K₁' K₀ hmass hc hFN (add_nonneg hks hE)
    (add_nonneg hka hE) hKc hδL hδR f g hf hg hK' u0 hm1 hm2 hO1 hO2 hu hKOs hKOa φ ψ
  unfold denseD
  exact ⟨hT.2.1, hT.2.2⟩

end Sarkozy.UpperComparison
