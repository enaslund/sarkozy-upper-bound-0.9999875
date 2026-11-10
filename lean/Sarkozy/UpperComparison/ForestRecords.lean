module

public import Sarkozy.Structured.CenteredTransport

@[expose] public section

/-!
# Degree-two FF, FE and EF records (`prop:forest-records`)

`paper/sections/26_upper_comparison.tex`, subsection "Replacements keeping the old cross edges",
`prop:forest-records`, parts (a), (b), (c). The statements are the *closure* of the proposition:
the step from the inputs the proof cites to the three norms (a), the symmetric bound of the
common-frame comparison (b) and the block gates (c).

**Framework.** As in `Sarkozy/Structured/CenteredTransport.lean`: `ν = λ_H` is a `FiniteLaw X`
(the common half law), kernels are functions `X × X → ℝ` relative to `ν ⊗ ν`, operators are their
bilinear forms `kform`, a norm bound on `L²_0(ν)` is a bound on centred functions, and the centred
operator of a law with half marginals `m = (1 + u₀)ν` is `centredForm ν u₀` on `L²(m)` (`mnrm`).
The symmetric and skew parts of a form `B` are `(B(φ,ψ) ± B(ψ,φ))/2`.

**Inputs taken as hypotheses** (the paper's citations; not formalized here):
* Steps 1–6 of the proof of `lem:upper-stars`: the decomposition
  `K₀ = (1 - q ∑ D_S)(1 ⊗ 1) + 𝒮^c + (ℛ_* - K_col)` of the unnormalized density, with `𝒮^c`
  annihilating the constants and mapping into `L²_0`, the remainder bounds `ℛ` for the form of
  `ℛ_* - K_col` and of its two centred marginal images, and `Z₀ ≥ Z_-` (`hZ`);
* `cor:star-matrix` and `lem:upper-stars`(c): the full, symmetric and skew parts of `𝒮^c` have
  norms at most `Γ_F k_f r + E_proj`, `Γ_F k_s r + E_proj`, `Γ_F k_a r + E_proj` (`hSf`, `hSs`,
  `hSa`), and, for (b), the symmetric part of `𝒮^c_new - 𝒮^c_old` in one synthesis is at most
  `Γ_F k_Δ r + E_new + E_old`;
* (F7) (`it:record:upper-F7`): the one-way repair `K' = (1 + f(x) + g(y))K` with
  `‖f‖_∞, ‖g‖_∞ ≤ F`, both half marginals `μ^old = (1 + u₀)λ_H`, `1 + u₀ ≥ e^{-ℓ_old}`,
  `‖u₀‖² ≤ B_top q`, and the full bound `ρ'`; the old record is symmetric with centred norm at most
  `ρ_old` relative to `μ^old`.

**Proved.**
* `raw_kernel_mass`, `raw_kernel_form`, `raw_kernel_full`, `raw_kernel_sym`, `raw_kernel_deltaL`,
  `raw_kernel_deltaR`, collected in **`forest_raw_kernel`**: the paragraph "The raw kernel" of the
  proof. Dividing by `Z₀ ≥ Z_-`, `K = K₀/Z₀ = 1⊗1 + δ_L⊗1 + 1⊗δ_R + K_c` with `‖K_c‖ ≤ c`,
  `‖Sym K_c‖ ≤ s`, `‖Skew K_c‖ ≤ a` and `‖δ_L‖, ‖δ_R‖ ≤ e`.
* **`forest_records_a`**: part (a), the three norms `c_new`, `s_new`, `a_new` of the centred
  operator of the repair and the bounds `ρ_old + s_new`, `a_new` for the symmetric and skew parts of
  the change (via `lem:record:centered-correction`(b), `Structured.centered_transport_norms`).
* `inv_sub_one_abs_le`, `two_normalizer_sym` (two kernels, each normalized by its own `Z`, compared
  without assuming the normalizers equal) and **`forest_records_b`**: part (b), the bound `d_sym`
  (via `lem:record:centered-correction`(c), `Structured.centered_transport_difference`).
* `ForestBlockGates`, `ForestBlockGatesFE`: part (c), the block gates, as propositions; they are
  numerical conditions checked by the certificates and used in `lem:record:domain`(ii).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperComparison

open Sarkozy.Recentering Sarkozy.Structured

variable {X : Type*} [Fintype X]

/-! ## General facts about forms -/

/-- `‖c f‖ = |c| ‖f‖`. -/
theorem nrm_const_mul (ν : FiniteLaw X) (c : ℝ) (f : X → ℝ) :
    nrm ν (fun x => c * f x) = |c| * nrm ν f := by
  unfold nrm ip
  have e : ν.expect (fun x => c * f x * (c * f x)) = c ^ 2 * ν.expect (fun x => f x * f x) := by
    rw [← ν.expect_const_mul]; exact ν.expect_congr fun x => by ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The form of a constant kernel vanishes on centred functions. -/
theorem kform_const_centred (ν : FiniteLaw X) (z : ℝ) (φ ψ : X → ℝ) (hψ : ν.expect ψ = 0) :
    kform ν ν (fun _ => z) φ ψ = 0 := by
  unfold kform
  have h : ∀ x, ν.expect (fun y => φ x * ψ y * z) = 0 := by
    intro x
    rw [show (fun y => φ x * ψ y * z) = fun y => (φ x * z) * ψ y from funext fun y => by ring,
      ν.expect_const_mul, hψ, mul_zero]
  exact (ν.expect_congr h).trans (ν.expect_const 0)

/-- A full bound in both orders bounds the symmetric (`σ = 1`) and skew (`σ = -1`) parts. -/
theorem abs_half_add_le {a b C : ℝ} {σ : ℝ} (hσ : |σ| ≤ 1) (ha : |a| ≤ C) (hb : |b| ≤ C) :
    |(a + σ * b) / 2| ≤ C := by
  rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have h1 := abs_add_le a (σ * b)
  have h2 : |σ * b| ≤ C := by
    rw [abs_mul]
    calc |σ| * |b| ≤ 1 * C := mul_le_mul hσ hb (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  linarith

/-- `|Z⁻¹ - 1| ≤ ε/(1 - ε)` when `|Z - 1| ≤ ε < 1`: each normalizer is paid separately. -/
theorem inv_sub_one_abs_le {Z ε : ℝ} (hZ : |Z - 1| ≤ ε) (hε : ε < 1) :
    |Z⁻¹ - 1| ≤ ε / (1 - ε) := by
  have hZ' := abs_le.mp hZ
  have h1ε : 0 < 1 - ε := by linarith
  have hZpos : 0 < Z := by linarith
  have e : Z⁻¹ - 1 = (1 - Z) / Z := by field_simp
  rw [e, abs_div, abs_of_pos hZpos, div_le_div_iff₀ hZpos h1ε]
  have h1 : |1 - Z| ≤ ε := by rw [abs_sub_comm]; exact hZ
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hZ
  have h2 : |1 - Z| * (1 - ε) ≤ ε * (1 - ε) := mul_le_mul_of_nonneg_right h1 h1ε.le
  have h3 : ε * (1 - ε) ≤ ε * Z := mul_le_mul_of_nonneg_left (by linarith) hε0
  linarith

/-! ## The raw kernel (proof of `prop:forest-records`, paragraph "The raw kernel") -/

section RawKernel

variable (ν : FiniteLaw X) (K₀ Sc Rem K : X × X → ℝ) (z Z₀ : ℝ)

/-- The kernel `K = K₀/Z₀` has mass one when `Z₀ = ∫ K₀ d(ν⊗ν) ≠ 0`. -/
theorem raw_kernel_mass (hZ₀ : Z₀ = ν.expect (fun x => ν.expect (fun y => K₀ (x, y))))
    (hZne : Z₀ ≠ 0) (hK : ∀ p, K p = K₀ p / Z₀) :
    ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1 := by
  have h : ∀ x, ν.expect (fun y => K (x, y)) = ν.expect (fun y => K₀ (x, y)) * Z₀⁻¹ := by
    intro x
    rw [← ν.expect_mul_const]
    exact ν.expect_congr fun y => by rw [hK, div_eq_mul_inv]
  rw [ν.expect_congr h, ν.expect_mul_const, ← hZ₀, mul_inv_cancel₀ hZne]

/-- On centred functions the form of `K = K₀/Z₀` is `Z₀⁻¹ (𝒮^c + ℛ)`: the constant part of
`K₀ = z + 𝒮^c + ℛ` does not see centred functions. -/
theorem raw_kernel_form (hdec : ∀ p, K₀ p = z + Sc p + Rem p) (hK : ∀ p, K p = K₀ p / Z₀)
    (φ ψ : X → ℝ) (hψ : ν.expect ψ = 0) :
    kform ν ν K φ ψ = Z₀⁻¹ * (kform ν ν Sc φ ψ + kform ν ν Rem φ ψ) := by
  have e1 : ∀ p, K p = Z₀⁻¹ * K₀ p := fun p => by rw [hK, div_eq_mul_inv, mul_comm]
  have e2 : ∀ p, K₀ p = (fun _ : X × X => z) p + Sc p + Rem p := fun p => hdec p
  rw [kform_congr ν ν e1, kform_const_mul, kform_congr ν ν e2, kform_add, kform_add,
    kform_const_centred ν z φ ψ hψ, zero_add]

variable {ν K₀ Sc Rem K z Z₀}

/-- **The full bound of `K_c`**: `‖K_c‖ ≤ (σ + ℛ)/Z_-` on `L²_0(ν)`. -/
theorem raw_kernel_full (hdec : ∀ p, K₀ p = z + Sc p + Rem p) (hK : ∀ p, K p = K₀ p / Z₀)
    {σ R Zm : ℝ} (hZm : 0 < Zm) (hZ : Zm ≤ Z₀)
    (hS : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |kform ν ν Sc φ ψ| ≤ σ * nrm ν φ * nrm ν ψ)
    (hR : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |kform ν ν Rem φ ψ| ≤ R * nrm ν φ * nrm ν ψ)
    (φ ψ : X → ℝ) (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    |kform ν ν (centeredKernel ν K) φ ψ| ≤ (σ + R) / Zm * nrm ν φ * nrm ν ψ := by
  rw [← kform_eq_centeredKernel ν K φ ψ hφ hψ, raw_kernel_form ν K₀ Sc Rem K z Z₀ hdec hK φ ψ hψ]
  have hZpos : 0 < Z₀ := hZm.trans_le hZ
  have h1 := hS φ ψ hφ hψ
  have h2 := hR φ ψ hφ hψ
  have hsum : |kform ν ν Sc φ ψ + kform ν ν Rem φ ψ| ≤ (σ + R) * nrm ν φ * nrm ν ψ := by
    have := abs_add_le (kform ν ν Sc φ ψ) (kform ν ν Rem φ ψ)
    linarith
  have hnn : 0 ≤ (σ + R) * nrm ν φ * nrm ν ψ := (abs_nonneg _).trans hsum
  rw [abs_mul, abs_of_pos (inv_pos.mpr hZpos)]
  calc Z₀⁻¹ * |kform ν ν Sc φ ψ + kform ν ν Rem φ ψ| ≤ Z₀⁻¹ * ((σ + R) * nrm ν φ * nrm ν ψ) :=
        mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hZpos).le
    _ ≤ Zm⁻¹ * ((σ + R) * nrm ν φ * nrm ν ψ) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hZm hZ) hnn
    _ = (σ + R) / Zm * nrm ν φ * nrm ν ψ := by ring

/-- **The symmetric (`τ = 1`) and skew (`τ = -1`) bounds of `K_c`**: `(σ_τ + ℛ)/Z_-`. -/
theorem raw_kernel_sym (hdec : ∀ p, K₀ p = z + Sc p + Rem p) (hK : ∀ p, K p = K₀ p / Z₀)
    {σ R Zm τ : ℝ} (hτ : |τ| ≤ 1) (hZm : 0 < Zm) (hZ : Zm ≤ Z₀)
    (hS : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν Sc φ ψ + τ * kform ν ν Sc ψ φ) / 2| ≤ σ * nrm ν φ * nrm ν ψ)
    (hR : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |kform ν ν Rem φ ψ| ≤ R * nrm ν φ * nrm ν ψ)
    (φ ψ : X → ℝ) (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    |(kform ν ν (centeredKernel ν K) φ ψ + τ * kform ν ν (centeredKernel ν K) ψ φ) / 2| ≤
      (σ + R) / Zm * nrm ν φ * nrm ν ψ := by
  rw [← kform_eq_centeredKernel ν K φ ψ hφ hψ, ← kform_eq_centeredKernel ν K ψ φ hψ hφ,
    raw_kernel_form ν K₀ Sc Rem K z Z₀ hdec hK φ ψ hψ,
    raw_kernel_form ν K₀ Sc Rem K z Z₀ hdec hK ψ φ hφ]
  have hZpos : 0 < Z₀ := hZm.trans_le hZ
  have e : (Z₀⁻¹ * (kform ν ν Sc φ ψ + kform ν ν Rem φ ψ) +
      τ * (Z₀⁻¹ * (kform ν ν Sc ψ φ + kform ν ν Rem ψ φ))) / 2 =
      Z₀⁻¹ * ((kform ν ν Sc φ ψ + τ * kform ν ν Sc ψ φ) / 2 +
        (kform ν ν Rem φ ψ + τ * kform ν ν Rem ψ φ) / 2) := by ring
  rw [e]
  have h1 := hS φ ψ hφ hψ
  have h2 : |(kform ν ν Rem φ ψ + τ * kform ν ν Rem ψ φ) / 2| ≤ R * nrm ν φ * nrm ν ψ := by
    refine abs_half_add_le hτ (hR φ ψ hφ hψ) ?_
    have := hR ψ φ hψ hφ
    linarith [show R * nrm ν ψ * nrm ν φ = R * nrm ν φ * nrm ν ψ by ring]
  have hsum : |(kform ν ν Sc φ ψ + τ * kform ν ν Sc ψ φ) / 2 +
      (kform ν ν Rem φ ψ + τ * kform ν ν Rem ψ φ) / 2| ≤ (σ + R) * nrm ν φ * nrm ν ψ := by
    have := abs_add_le ((kform ν ν Sc φ ψ + τ * kform ν ν Sc ψ φ) / 2)
      ((kform ν ν Rem φ ψ + τ * kform ν ν Rem ψ φ) / 2)
    linarith
  have hnn : 0 ≤ (σ + R) * nrm ν φ * nrm ν ψ := (abs_nonneg _).trans hsum
  rw [abs_mul, abs_of_pos (inv_pos.mpr hZpos)]
  calc Z₀⁻¹ * |(kform ν ν Sc φ ψ + τ * kform ν ν Sc ψ φ) / 2 +
        (kform ν ν Rem φ ψ + τ * kform ν ν Rem ψ φ) / 2| ≤
        Z₀⁻¹ * ((σ + R) * nrm ν φ * nrm ν ψ) :=
        mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hZpos).le
    _ ≤ Zm⁻¹ * ((σ + R) * nrm ν φ * nrm ν ψ) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hZm hZ) hnn
    _ = (σ + R) / Zm * nrm ν φ * nrm ν ψ := by ring

/-- **The left marginal defect**: `δ_L = Z₀⁻¹ Q(ℛ 1)`, so `‖δ_L‖ ≤ ℛ/Z_-`. -/
theorem raw_kernel_deltaL (hdec : ∀ p, K₀ p = z + Sc p + Rem p) (hK : ∀ p, K p = K₀ p / Z₀)
    (hZ₀ : Z₀ = ν.expect (fun x => ν.expect (fun y => K₀ (x, y))))
    (hScRow : ∀ x, ν.expect (fun y => Sc (x, y)) = 0) {R Zm : ℝ} (hR : 0 ≤ R) (hZm : 0 < Zm)
    (hZ : Zm ≤ Z₀) (hRL : nrm ν (center ν (fun x => ν.expect (fun y => Rem (x, y)))) ≤ R) :
    nrm ν (deltaL ν K) ≤ R / Zm := by
  have hZpos : 0 < Z₀ := hZm.trans_le hZ
  set ρL : X → ℝ := fun x => ν.expect (fun y => Rem (x, y)) with hρL
  have hrow : ∀ x, ν.expect (fun y => K₀ (x, y)) = z + ρL x := by
    intro x
    have e : (fun y => K₀ (x, y)) = fun y => (z + Sc (x, y)) + Rem (x, y) :=
      funext fun y => hdec (x, y)
    rw [e, ν.expect_add, ν.expect_add, ν.expect_const, hScRow x, add_zero]
  have hZ₀' : Z₀ = z + ν.expect ρL := by
    rw [hZ₀, ν.expect_congr hrow, ν.expect_add, ν.expect_const]
  have hδ : deltaL ν K = fun x => Z₀⁻¹ * center ν ρL x := by
    funext x
    unfold deltaL center
    have e : ν.expect (fun y => K (x, y)) = ν.expect (fun y => K₀ (x, y)) * Z₀⁻¹ := by
      rw [← ν.expect_mul_const]
      exact ν.expect_congr fun y => by rw [hK, div_eq_mul_inv]
    rw [e, hrow]
    have hZne : Z₀ ≠ 0 := hZpos.ne'
    field_simp
    rw [hZ₀']
    ring
  rw [hδ, nrm_const_mul, abs_of_pos (inv_pos.mpr hZpos)]
  calc Z₀⁻¹ * nrm ν (center ν ρL) ≤ Z₀⁻¹ * R := mul_le_mul_of_nonneg_left hRL (inv_pos.mpr hZpos).le
    _ ≤ Zm⁻¹ * R := mul_le_mul_of_nonneg_right (inv_anti₀ hZm hZ) hR
    _ = R / Zm := by ring

/-- **The right marginal defect**: `δ_R = Z₀⁻¹ Q(ℛ^* 1)`, so `‖δ_R‖ ≤ ℛ/Z_-`. -/
theorem raw_kernel_deltaR (hdec : ∀ p, K₀ p = z + Sc p + Rem p) (hK : ∀ p, K p = K₀ p / Z₀)
    (hZ₀ : Z₀ = ν.expect (fun x => ν.expect (fun y => K₀ (x, y))))
    (hScCol : ∀ y, ν.expect (fun x => Sc (x, y)) = 0) {R Zm : ℝ} (hR : 0 ≤ R) (hZm : 0 < Zm)
    (hZ : Zm ≤ Z₀) (hRR : nrm ν (center ν (fun y => ν.expect (fun x => Rem (x, y)))) ≤ R) :
    nrm ν (deltaR ν K) ≤ R / Zm := by
  have hZpos : 0 < Z₀ := hZm.trans_le hZ
  set ρR : X → ℝ := fun y => ν.expect (fun x => Rem (x, y)) with hρR
  have hcol : ∀ y, ν.expect (fun x => K₀ (x, y)) = z + ρR y := by
    intro y
    have e : (fun x => K₀ (x, y)) = fun x => (z + Sc (x, y)) + Rem (x, y) :=
      funext fun x => hdec (x, y)
    rw [e, ν.expect_add, ν.expect_add, ν.expect_const, hScCol y, add_zero]
  have hZ₀' : Z₀ = z + ν.expect ρR := by
    rw [hZ₀, expect_swap ν (fun x y => K₀ (x, y)), ν.expect_congr hcol, ν.expect_add,
      ν.expect_const]
  have hδ : deltaR ν K = fun y => Z₀⁻¹ * center ν ρR y := by
    funext y
    unfold deltaR center
    have e : ν.expect (fun x => K (x, y)) = ν.expect (fun x => K₀ (x, y)) * Z₀⁻¹ := by
      rw [← ν.expect_mul_const]
      exact ν.expect_congr fun x => by rw [hK, div_eq_mul_inv]
    rw [e, hcol]
    have hZne : Z₀ ≠ 0 := hZpos.ne'
    field_simp
    rw [hZ₀']
    ring
  rw [hδ, nrm_const_mul, abs_of_pos (inv_pos.mpr hZpos)]
  calc Z₀⁻¹ * nrm ν (center ν ρR) ≤ Z₀⁻¹ * R := mul_le_mul_of_nonneg_left hRR (inv_pos.mpr hZpos).le
    _ ≤ Zm⁻¹ * R := mul_le_mul_of_nonneg_right (inv_anti₀ hZm hZ) hR
    _ = R / Zm := by ring

end RawKernel

/-! ## The constants of `prop:forest-records` -/

/-- `c = (Γ_F k_f r + E_proj + ℛ)/Z_-` of `prop:forest-records`; with `k_s`, `k_a` in place of
`k_f` it is `s`, `a`. -/
noncomputable def forestCoef (ΓF k r Eproj R Zm : ℝ) : ℝ := (ΓF * k * r + Eproj + R) / Zm

/-- `c_new = min{ρ', e^{ℓ_old}(c + 2F(c + e) + B_top q)}` of `prop:forest-records`(a). -/
noncomputable def forestCNew (ρ' ℓold c e F Btop q : ℝ) : ℝ :=
  min ρ' (Real.exp ℓold * (c + 2 * F * (c + e) + Btop * q))

/-- `s_new = e^{ℓ_old}(s + 2F(c + e) + B_top q)` of `prop:forest-records`(a). -/
noncomputable def forestSNew (ℓold s c e F Btop q : ℝ) : ℝ :=
  Real.exp ℓold * (s + 2 * F * (c + e) + Btop * q)

/-- `a_new = e^{ℓ_old}(a + 2F(c + e))` of `prop:forest-records`(a). -/
noncomputable def forestANew (ℓold a c e F : ℝ) : ℝ := Real.exp ℓold * (a + 2 * F * (c + e))

/-- **The raw kernel of `prop:forest-records`** (its proof, paragraph "The raw kernel"), from the
inputs of Steps 1–6 of `lem:upper-stars` and of `cor:star-matrix`/`lem:upper-stars`(c), all taken
as hypotheses: `K₀ = z + 𝒮^c + ℛ` with `𝒮^c` of zero row and column means, the three bounds
`Γ_F k_• r + E_proj` for `𝒮^c`, the bound `ℛ` for the remainder and its two centred marginal images,
and `Z₀ = ∫K₀ ≥ Z_- > 0`. Conclusion: `K = K₀/Z₀` has mass one,
`K = 1⊗1 + δ_L⊗1 + 1⊗δ_R + K_c` with `‖K_c‖ ≤ c`, `‖Sym K_c‖ ≤ s`, `‖Skew K_c‖ ≤ a`, and
`‖δ_L‖, ‖δ_R‖ ≤ e = ℛ/Z_-`. -/
theorem forest_raw_kernel (ν : FiniteLaw X) (K₀ Sc Rem K : X × X → ℝ) (z Z₀ : ℝ)
    (hdec : ∀ p, K₀ p = z + Sc p + Rem p)
    (hZ₀ : Z₀ = ν.expect (fun x => ν.expect (fun y => K₀ (x, y))))
    (hK : ∀ p, K p = K₀ p / Z₀)
    (hScRow : ∀ x, ν.expect (fun y => Sc (x, y)) = 0)
    (hScCol : ∀ y, ν.expect (fun x => Sc (x, y)) = 0)
    {ΓF kf ks ka r Eproj R Zm : ℝ} (hR : 0 ≤ R) (hZm : 0 < Zm) (hZ : Zm ≤ Z₀)
    (hSf : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν Sc φ ψ| ≤ (ΓF * kf * r + Eproj) * nrm ν φ * nrm ν ψ)
    (hSs : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν Sc φ ψ + kform ν ν Sc ψ φ) / 2| ≤ (ΓF * ks * r + Eproj) * nrm ν φ * nrm ν ψ)
    (hSa : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν Sc φ ψ - kform ν ν Sc ψ φ) / 2| ≤ (ΓF * ka * r + Eproj) * nrm ν φ * nrm ν ψ)
    (hRf : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν Rem φ ψ| ≤ R * nrm ν φ * nrm ν ψ)
    (hRL : nrm ν (center ν (fun x => ν.expect (fun y => Rem (x, y)))) ≤ R)
    (hRR : nrm ν (center ν (fun y => ν.expect (fun x => Rem (x, y)))) ≤ R) :
    ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1 ∧
      (∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
        |kform ν ν (centeredKernel ν K) φ ψ| ≤
          forestCoef ΓF kf r Eproj R Zm * nrm ν φ * nrm ν ψ) ∧
      (∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
        |(kform ν ν (centeredKernel ν K) φ ψ + kform ν ν (centeredKernel ν K) ψ φ) / 2| ≤
          forestCoef ΓF ks r Eproj R Zm * nrm ν φ * nrm ν ψ) ∧
      (∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
        |(kform ν ν (centeredKernel ν K) φ ψ - kform ν ν (centeredKernel ν K) ψ φ) / 2| ≤
          forestCoef ΓF ka r Eproj R Zm * nrm ν φ * nrm ν ψ) ∧
      nrm ν (deltaL ν K) ≤ R / Zm ∧ nrm ν (deltaR ν K) ≤ R / Zm := by
  have hZpos : 0 < Z₀ := hZm.trans_le hZ
  refine ⟨raw_kernel_mass ν K₀ K Z₀ hZ₀ hZpos.ne' hK, ?_, ?_, ?_,
    raw_kernel_deltaL hdec hK hZ₀ hScRow hR hZm hZ hRL,
    raw_kernel_deltaR hdec hK hZ₀ hScCol hR hZm hZ hRR⟩
  · intro φ ψ hφ hψ
    have := raw_kernel_full hdec hK hZm hZ hSf hRf φ ψ hφ hψ
    unfold forestCoef
    exact this
  · intro φ ψ hφ hψ
    have hS' : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
        |(kform ν ν Sc φ ψ + 1 * kform ν ν Sc ψ φ) / 2| ≤
          (ΓF * ks * r + Eproj) * nrm ν φ * nrm ν ψ := by
      intro φ ψ hφ hψ; rw [one_mul]; exact hSs φ ψ hφ hψ
    have := raw_kernel_sym hdec hK (by norm_num : |(1 : ℝ)| ≤ 1) hZm hZ hS' hRf φ ψ hφ hψ
    rw [one_mul] at this
    unfold forestCoef
    exact this
  · intro φ ψ hφ hψ
    have hS' : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
        |(kform ν ν Sc φ ψ + (-1) * kform ν ν Sc ψ φ) / 2| ≤
          (ΓF * ka * r + Eproj) * nrm ν φ * nrm ν ψ := by
      intro φ ψ hφ hψ; rw [neg_one_mul, ← sub_eq_add_neg]; exact hSa φ ψ hφ hψ
    have := raw_kernel_sym hdec hK (by norm_num : |(-1 : ℝ)| ≤ 1) hZm hZ hS' hRf φ ψ hφ hψ
    rw [neg_one_mul, ← sub_eq_add_neg] at this
    unfold forestCoef
    exact this

/-- The centred operator of a symmetric kernel is symmetric. -/
theorem centredForm_symm (ν : FiniteLaw X) (u0 : X → ℝ) {O : X × X → ℝ}
    (hOsym : ∀ x y, O (x, y) = O (y, x)) (φ ψ : X → ℝ) :
    centredForm ν u0 O ψ φ = centredForm ν u0 O φ ψ := by
  unfold centredForm
  rw [← kform_transpose ν O φ ψ, kform_congr ν ν (fun p => (hOsym p.2 p.1)), mul_comm]

/-- **`prop:forest-records`(a)**, in the frame of the raw kernel. Inputs (hypotheses): those of
`forest_raw_kernel` (Steps 1–6 of `lem:upper-stars`, `cor:star-matrix`, `lem:upper-stars`(c));
the one-way repair `K' = (1 + f(x) + g(y))K` of (F7) with `|f|, |g| ≤ F`, both half marginals
`μ^old = (1 + u₀)λ_H`, `1 + u₀ ≥ e^{-ℓ_old}`, `‖u₀‖² ≤ B_top q` (proof of (F7)) and its full
bound `ρ'` (F7); the old record `O`, symmetric under the layer interchange, with centred norm at
most `ρ_old` relative to `μ^old`.

Conclusion: relative to `μ^old` on both halves, the centred operator of the repair has full,
symmetric and skew norms at most `c_new`, `s_new`, `a_new`, and the change `K' - O` has symmetric
part of norm at most `ρ_old + s_new` and skew part of norm at most `a_new` (the skew part of the
symmetric old record vanishes, `rem:cp:charging`(iii)). The proof is
`lem:record:centered-correction`(b) with `b₀ = B_top q` (`Structured.centered_transport_norms`). -/
theorem forest_records_a (ν : FiniteLaw X) (K₀ Sc Rem K K' O : X × X → ℝ) (z Z₀ : ℝ)
    (hdec : ∀ p, K₀ p = z + Sc p + Rem p)
    (hZ₀ : Z₀ = ν.expect (fun x => ν.expect (fun y => K₀ (x, y))))
    (hK : ∀ p, K p = K₀ p / Z₀)
    (hScRow : ∀ x, ν.expect (fun y => Sc (x, y)) = 0)
    (hScCol : ∀ y, ν.expect (fun x => Sc (x, y)) = 0)
    {ΓF kf ks ka r Eproj R Zm : ℝ}
    (hσf : 0 ≤ ΓF * kf * r + Eproj) (hσs : 0 ≤ ΓF * ks * r + Eproj)
    (hσa : 0 ≤ ΓF * ka * r + Eproj) (hR : 0 ≤ R) (hZm : 0 < Zm) (hZ : Zm ≤ Z₀)
    (hSf : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν Sc φ ψ| ≤ (ΓF * kf * r + Eproj) * nrm ν φ * nrm ν ψ)
    (hSs : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν Sc φ ψ + kform ν ν Sc ψ φ) / 2| ≤ (ΓF * ks * r + Eproj) * nrm ν φ * nrm ν ψ)
    (hSa : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν Sc φ ψ - kform ν ν Sc ψ φ) / 2| ≤ (ΓF * ka * r + Eproj) * nrm ν φ * nrm ν ψ)
    (hRf : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν Rem φ ψ| ≤ R * nrm ν φ * nrm ν ψ)
    (hRL : nrm ν (center ν (fun x => ν.expect (fun y => Rem (x, y)))) ≤ R)
    (hRR : nrm ν (center ν (fun y => ν.expect (fun x => Rem (x, y)))) ≤ R)
    {F ℓold Btop q ρ' ρold : ℝ} (hF : 0 ≤ F) (f g : X → ℝ) (hf : ∀ x, |f x| ≤ F)
    (hg : ∀ y, |g y| ≤ F) (hK' : ∀ p, K' p = (1 + f p.1 + g p.2) * K p)
    (u0 : X → ℝ) (hu00 : ν.expect u0 = 0)
    (hm1 : ∀ x, ν.expect (fun y => K' (x, y)) = 1 + u0 x)
    (hm2 : ∀ y, ν.expect (fun x => K' (x, y)) = 1 + u0 y)
    (hu : ∀ x, Real.exp (-ℓold) ≤ 1 + u0 x) (hb : nrm ν u0 ^ 2 ≤ Btop * q)
    (hρ' : ∀ φ ψ, |centredForm ν u0 K' φ ψ| ≤ ρ' * mnrm ν u0 φ * mnrm ν u0 ψ)
    (hOsym : ∀ x y, O (x, y) = O (y, x))
    (hOρ : ∀ φ ψ, |centredForm ν u0 O φ ψ| ≤ ρold * mnrm ν u0 φ * mnrm ν u0 ψ)
    (φ ψ : X → ℝ) :
    |centredForm ν u0 K' φ ψ| ≤
        forestCNew ρ' ℓold (forestCoef ΓF kf r Eproj R Zm) (R / Zm) F Btop q *
          mnrm ν u0 φ * mnrm ν u0 ψ ∧
      |(centredForm ν u0 K' φ ψ + centredForm ν u0 K' ψ φ) / 2| ≤
        forestSNew ℓold (forestCoef ΓF ks r Eproj R Zm) (forestCoef ΓF kf r Eproj R Zm) (R / Zm)
          F Btop q * mnrm ν u0 φ * mnrm ν u0 ψ ∧
      |(centredForm ν u0 K' φ ψ - centredForm ν u0 K' ψ φ) / 2| ≤
        forestANew ℓold (forestCoef ΓF ka r Eproj R Zm) (forestCoef ΓF kf r Eproj R Zm) (R / Zm)
          F * mnrm ν u0 φ * mnrm ν u0 ψ ∧
      |((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) +
          (centredForm ν u0 K' ψ φ - centredForm ν u0 O ψ φ)) / 2| ≤
        (ρold + forestSNew ℓold (forestCoef ΓF ks r Eproj R Zm) (forestCoef ΓF kf r Eproj R Zm)
          (R / Zm) F Btop q) * mnrm ν u0 φ * mnrm ν u0 ψ ∧
      |((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) -
          (centredForm ν u0 K' ψ φ - centredForm ν u0 O ψ φ)) / 2| ≤
        forestANew ℓold (forestCoef ΓF ka r Eproj R Zm) (forestCoef ΓF kf r Eproj R Zm) (R / Zm)
          F * mnrm ν u0 φ * mnrm ν u0 ψ := by
  obtain ⟨hmass, hKc, hKs, hKa, hδL, hδR⟩ := forest_raw_kernel ν K₀ Sc Rem K z Z₀ hdec hZ₀ hK
    hScRow hScCol hR hZm hZ hSf hSs hSa hRf hRL hRR
  have hc : 0 ≤ forestCoef ΓF kf r Eproj R Zm := div_nonneg (add_nonneg hσf hR) hZm.le
  have hs : 0 ≤ forestCoef ΓF ks r Eproj R Zm := div_nonneg (add_nonneg hσs hR) hZm.le
  have ha : 0 ≤ forestCoef ΓF ka r Eproj R Zm := div_nonneg (add_nonneg hσa hR) hZm.le
  have hn := centered_transport_norms ν K K' hmass hc hs ha hF hKc hKs hKa hδL hδR f g hf hg hK'
    u0 hu00 hm1 hm2 hu hb
  obtain ⟨h1, h2, h3⟩ := hn φ ψ
  have hmn : 0 ≤ mnrm ν u0 φ * mnrm ν u0 ψ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hO := centredForm_symm ν u0 hOsym φ ψ
  have hOb := hOρ φ ψ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold forestCNew
    rw [mul_assoc, min_mul_of_nonneg _ _ hmn]
    refine le_min ?_ ?_
    · rw [← mul_assoc]; exact hρ' φ ψ
    · rw [← mul_assoc]; exact h1
  · unfold forestSNew; exact h2
  · unfold forestANew; exact h3
  · rw [hO]
    have e : ((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) +
        (centredForm ν u0 K' ψ φ - centredForm ν u0 O φ ψ)) / 2 =
        (centredForm ν u0 K' φ ψ + centredForm ν u0 K' ψ φ) / 2 - centredForm ν u0 O φ ψ := by
      ring
    rw [e]
    have := abs_sub (((centredForm ν u0 K' φ ψ + centredForm ν u0 K' ψ φ) / 2))
      (centredForm ν u0 O φ ψ)
    unfold forestSNew
    nlinarith
  · rw [hO]
    have e : ((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) -
        (centredForm ν u0 K' ψ φ - centredForm ν u0 O φ ψ)) / 2 =
        (centredForm ν u0 K' φ ψ - centredForm ν u0 K' ψ φ) / 2 := by ring
    rw [e]
    unfold forestANew; exact h3

/-! ## Two kernels with their own normalizers (`prop:forest-records`(b), `prop:dense-comparison`) -/

/-- A bound on centred functions, regrouped: `|B φ ψ| ≤ C (‖φ‖‖ψ‖)`. -/
theorem bound_assoc {ν : FiniteLaw X} {B : (X → ℝ) → (X → ℝ) → ℝ} {C : ℝ}
    (h : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |B φ ψ| ≤ C * nrm ν φ * nrm ν ψ)
    (φ ψ : X → ℝ) (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    |B φ ψ| ≤ C * (nrm ν φ * nrm ν ψ) := by
  rw [← mul_assoc]; exact h φ ψ hφ hψ

/-- A bound on centred functions at the transposed pair: `|B ψ φ| ≤ C (‖φ‖‖ψ‖)`. -/
theorem bound_swap {ν : FiniteLaw X} {B : (X → ℝ) → (X → ℝ) → ℝ} {C : ℝ}
    (h : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |B φ ψ| ≤ C * nrm ν φ * nrm ν ψ)
    (φ ψ : X → ℝ) (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    |B ψ φ| ≤ C * (nrm ν φ * nrm ν ψ) := by
  have := h ψ φ hψ hφ
  rw [mul_assoc, mul_comm (nrm ν ψ)] at this
  exact this

/-- **Two normalizers, paid separately**, at one pair of test functions: if
`A_h = L_h + M_h` (`h = 1` new, `h = 0` old, primes for the transposed pair), the leading parts
differ in their symmetric (`τ = 1`) or skew (`τ = -1`) part by at most `S`, the remainders are at
most `ℛ_h`, the whole forms at most `U_h`, and `|Z_h - 1| ≤ ε_h < 1`, then the part of
`A₁/Z₁ - A₀/Z₀` is at most `S + ℛ₁ + ℛ₀ + ∑_h ε_h U_h/(1 - ε_h)`. No equality of the two
normalizers is assumed. -/
theorem two_normalizer_sym {A₁ A₁' A₀ A₀' L₁ L₁' L₀ L₀' M₁ M₁' M₀ M₀' Z₁ Z₀ ε₁ ε₀ τ S R₁ R₀ U₁ U₀
    n : ℝ} (hτ : |τ| ≤ 1)
    (hA₁ : A₁ = L₁ + M₁) (hA₁' : A₁' = L₁' + M₁') (hA₀ : A₀ = L₀ + M₀) (hA₀' : A₀' = L₀' + M₀')
    (hL : |((L₁ - L₀) + τ * (L₁' - L₀')) / 2| ≤ S * n)
    (hM₁ : |M₁| ≤ R₁ * n) (hM₁' : |M₁'| ≤ R₁ * n) (hM₀ : |M₀| ≤ R₀ * n) (hM₀' : |M₀'| ≤ R₀ * n)
    (hU₁ : |A₁| ≤ U₁ * n) (hU₁' : |A₁'| ≤ U₁ * n) (hU₀ : |A₀| ≤ U₀ * n) (hU₀' : |A₀'| ≤ U₀ * n)
    (hZ₁ : |Z₁ - 1| ≤ ε₁) (hZ₀ : |Z₀ - 1| ≤ ε₀) (hε₁ : ε₁ < 1) (hε₀ : ε₀ < 1) :
    |((A₁ / Z₁ - A₀ / Z₀) + τ * (A₁' / Z₁ - A₀' / Z₀)) / 2| ≤
      (S + R₁ + R₀ + ε₁ * U₁ / (1 - ε₁) + ε₀ * U₀ / (1 - ε₀)) * n := by
  have ht₁ := inv_sub_one_abs_le hZ₁ hε₁
  have ht₀ := inv_sub_one_abs_le hZ₀ hε₀
  have hε₁0 : 0 ≤ ε₁ := (abs_nonneg _).trans hZ₁
  have hε₀0 : 0 ≤ ε₀ := (abs_nonneg _).trans hZ₀
  have hq₁ : 0 ≤ ε₁ / (1 - ε₁) := div_nonneg hε₁0 (by linarith)
  have hq₀ : 0 ≤ ε₀ / (1 - ε₀) := div_nonneg hε₀0 (by linarith)
  have e : ((A₁ / Z₁ - A₀ / Z₀) + τ * (A₁' / Z₁ - A₀' / Z₀)) / 2 =
      ((L₁ - L₀) + τ * (L₁' - L₀')) / 2 + (M₁ + τ * M₁') / 2 - (M₀ + τ * M₀') / 2 +
        (Z₁⁻¹ - 1) * ((A₁ + τ * A₁') / 2) - (Z₀⁻¹ - 1) * ((A₀ + τ * A₀') / 2) := by
    rw [hA₁, hA₁', hA₀, hA₀']; simp only [div_eq_mul_inv]; ring
  rw [e]
  have b1 := abs_half_add_le hτ hM₁ hM₁'
  have b0 := abs_half_add_le hτ hM₀ hM₀'
  have c1 := abs_half_add_le hτ hU₁ hU₁'
  have c0 := abs_half_add_le hτ hU₀ hU₀'
  have d1 : |(Z₁⁻¹ - 1) * ((A₁ + τ * A₁') / 2)| ≤ ε₁ / (1 - ε₁) * (U₁ * n) := by
    rw [abs_mul]; exact mul_le_mul ht₁ c1 (abs_nonneg _) hq₁
  have d0 : |(Z₀⁻¹ - 1) * ((A₀ + τ * A₀') / 2)| ≤ ε₀ / (1 - ε₀) * (U₀ * n) := by
    rw [abs_mul]; exact mul_le_mul ht₀ c0 (abs_nonneg _) hq₀
  have t1 := abs_add_le (((L₁ - L₀) + τ * (L₁' - L₀')) / 2 + (M₁ + τ * M₁') / 2 -
      (M₀ + τ * M₀') / 2 + (Z₁⁻¹ - 1) * ((A₁ + τ * A₁') / 2))
    (-((Z₀⁻¹ - 1) * ((A₀ + τ * A₀') / 2)))
  have t2 := abs_add_le (((L₁ - L₀) + τ * (L₁' - L₀')) / 2 + (M₁ + τ * M₁') / 2 -
      (M₀ + τ * M₀') / 2) ((Z₁⁻¹ - 1) * ((A₁ + τ * A₁') / 2))
  have t3 := abs_sub (((L₁ - L₀) + τ * (L₁' - L₀')) / 2 + (M₁ + τ * M₁') / 2) ((M₀ + τ * M₀') / 2)
  have t4 := abs_add_le (((L₁ - L₀) + τ * (L₁' - L₀')) / 2) ((M₁ + τ * M₁') / 2)
  rw [abs_neg] at t1
  have e2 : ((L₁ - L₀) + τ * (L₁' - L₀')) / 2 + (M₁ + τ * M₁') / 2 - (M₀ + τ * M₀') / 2 +
      (Z₁⁻¹ - 1) * ((A₁ + τ * A₁') / 2) - (Z₀⁻¹ - 1) * ((A₀ + τ * A₀') / 2) =
      ((L₁ - L₀) + τ * (L₁' - L₀')) / 2 + (M₁ + τ * M₁') / 2 - (M₀ + τ * M₀') / 2 +
      (Z₁⁻¹ - 1) * ((A₁ + τ * A₁') / 2) + -((Z₀⁻¹ - 1) * ((A₀ + τ * A₀') / 2)) := by ring
  rw [e2]
  have e3 : (S + R₁ + R₀ + ε₁ * U₁ / (1 - ε₁) + ε₀ * U₀ / (1 - ε₀)) * n =
      S * n + R₁ * n + R₀ * n + ε₁ / (1 - ε₁) * (U₁ * n) + ε₀ / (1 - ε₀) * (U₀ * n) := by ring
  rw [e3]
  linarith

/-- On centred functions the form of `O = O₀/Z` is `(L + M)/Z` when that of `O₀` is `L + M`. -/
theorem kform_normalized (ν : FiniteLaw X) (O₀ O : X × X → ℝ) (Z : ℝ) (hO : ∀ p, O p = O₀ p / Z)
    (φ ψ : X → ℝ) : kform ν ν O φ ψ = kform ν ν O₀ φ ψ / Z := by
  have e : ∀ p, O p = Z⁻¹ * O₀ p := fun p => by rw [hO, div_eq_mul_inv, mul_comm]
  rw [kform_congr ν ν e, kform_const_mul, inv_mul_eq_div]

/-- `U_h = Γ_F k_h r + E_h + ℛ_h` of `prop:forest-records`(b). -/
noncomputable def forestU (ΓF k r E R : ℝ) : ℝ := ΓF * k * r + E + R

/-- `d_raw = Γ_F k_Δ r + ∑_h (E_h + ℛ_h + ε_h U_h/(1 - ε_h))` of `prop:forest-records`(b). -/
noncomputable def forestDRaw (ΓF kΔ r Enew Eold Rnew Rold εnew εold Unew Uold : ℝ) : ℝ :=
  ΓF * kΔ * r + (Enew + Rnew + εnew * Unew / (1 - εnew)) +
    (Eold + Rold + εold * Uold / (1 - εold))

/-- `d_sym = e^{ℓ_old}(d_raw + 2F(c + e))` of `prop:forest-records`(b). -/
noncomputable def forestDSym (ℓold draw c e F : ℝ) : ℝ := Real.exp ℓold * (draw + 2 * F * (c + e))

/-- **`prop:forest-records`(b)** (FE and EF records), in the frame of the raw kernel. Inputs
(hypotheses): those of `forest_raw_kernel` for the new law (with the frame constant `Γ_F` of (a),
giving `c` and `e`); the old density `O = O₀/Z_old`, whose unnormalized form on centred functions
is `L_old + M_old` (Steps 1–6 of `lem:upper-stars` for the old cross graph), with
`|M_old| ≤ ℛ_old`; in the common synthesis over the leaf pairs of both graphs (frame constant
`Γ'_F`, `cor:star-matrix` and `lem:upper-stars`(c)): `‖𝒮^c_new‖ ≤ Γ'_F k_new r + E_new`,
`‖𝒮^c_old‖ ≤ Γ'_F k_old r + E_old` and `‖Sym(𝒮^c_new - 𝒮^c_old)‖ ≤ Γ'_F k_Δ r + E_new + E_old`;
normalizers with `|Z_h - 1| ≤ ε_h < 1/2` (Step 6); the repair as in (a); and `O` with the same
half marginals `μ^old`. Conclusion: the symmetric part of the change `K' - O` has norm at most
`d_sym` relative to `μ^old` (via `lem:record:centered-correction`(c),
`Structured.centered_transport_difference`): the rank-one terms of the actual centring cancel. -/
theorem forest_records_b (ν : FiniteLaw X) (K₀ Sc Rem K K' O₀ O : X × X → ℝ) (z Z₀ Zo : ℝ)
    (hdec : ∀ p, K₀ p = z + Sc p + Rem p)
    (hZ₀ : Z₀ = ν.expect (fun x => ν.expect (fun y => K₀ (x, y))))
    (hK : ∀ p, K p = K₀ p / Z₀)
    (hScRow : ∀ x, ν.expect (fun y => Sc (x, y)) = 0)
    (hScCol : ∀ y, ν.expect (fun x => Sc (x, y)) = 0)
    {ΓF kf r Eproj R Zm : ℝ} (hσf : 0 ≤ ΓF * kf * r + Eproj) (hR : 0 ≤ R) (hZm : 0 < Zm)
    (hZ : Zm ≤ Z₀)
    (hSf : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν Sc φ ψ| ≤ (ΓF * kf * r + Eproj) * nrm ν φ * nrm ν ψ)
    (hRf : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν Rem φ ψ| ≤ R * nrm ν φ * nrm ν ψ)
    (hRL : nrm ν (center ν (fun x => ν.expect (fun y => Rem (x, y)))) ≤ R)
    (hRR : nrm ν (center ν (fun y => ν.expect (fun x => Rem (x, y)))) ≤ R)
    (hO : ∀ p, O p = O₀ p / Zo) (Lo Mo : (X → ℝ) → (X → ℝ) → ℝ)
    (hOdec : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → kform ν ν O₀ φ ψ = Lo φ ψ + Mo φ ψ)
    {ΓF' knew kold kΔ Enew Eold Rold εnew εold : ℝ} (hkΔ : 0 ≤ ΓF' * kΔ * r)
    (hknew : 0 ≤ ΓF' * knew * r) (hkold : 0 ≤ ΓF' * kold * r) (hEnew : 0 ≤ Enew)
    (hEold : 0 ≤ Eold) (hRold : 0 ≤ Rold)
    (hMo : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Mo φ ψ| ≤ Rold * nrm ν φ * nrm ν ψ)
    (hLn : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν Sc φ ψ| ≤ (ΓF' * knew * r + Enew) * nrm ν φ * nrm ν ψ)
    (hLo : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |Lo φ ψ| ≤ (ΓF' * kold * r + Eold) * nrm ν φ * nrm ν ψ)
    (hLΔ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |((kform ν ν Sc φ ψ - Lo φ ψ) + (kform ν ν Sc ψ φ - Lo ψ φ)) / 2| ≤
        (ΓF' * kΔ * r + Enew + Eold) * nrm ν φ * nrm ν ψ)
    (hZn : |Z₀ - 1| ≤ εnew) (hZo : |Zo - 1| ≤ εold) (hεn : εnew < 1 / 2) (hεo : εold < 1 / 2)
    {F ℓold : ℝ} (hF : 0 ≤ F) (f g : X → ℝ) (hf : ∀ x, |f x| ≤ F)
    (hg : ∀ y, |g y| ≤ F) (hK' : ∀ p, K' p = (1 + f p.1 + g p.2) * K p) (u0 : X → ℝ)
    (hm1 : ∀ x, ν.expect (fun y => K' (x, y)) = 1 + u0 x)
    (hm2 : ∀ y, ν.expect (fun x => K' (x, y)) = 1 + u0 y)
    (hO1 : ∀ x, ν.expect (fun y => O (x, y)) = 1 + u0 x)
    (hO2 : ∀ y, ν.expect (fun x => O (x, y)) = 1 + u0 y)
    (hu : ∀ x, Real.exp (-ℓold) ≤ 1 + u0 x) (φ ψ : X → ℝ) :
    |((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) +
        (centredForm ν u0 K' ψ φ - centredForm ν u0 O ψ φ)) / 2| ≤
      forestDSym ℓold (forestDRaw ΓF' kΔ r Enew Eold R Rold εnew εold
          (forestU ΓF' knew r Enew R) (forestU ΓF' kold r Eold Rold))
        (forestCoef ΓF kf r Eproj R Zm) (R / Zm) F * mnrm ν u0 φ * mnrm ν u0 ψ := by
  have hZpos : 0 < Z₀ := hZm.trans_le hZ
  have hmass := raw_kernel_mass ν K₀ K Z₀ hZ₀ hZpos.ne' hK
  have hKc : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν (centeredKernel ν K) φ ψ| ≤ forestCoef ΓF kf r Eproj R Zm * nrm ν φ * nrm ν ψ := by
    intro φ ψ hφ hψ
    have := raw_kernel_full hdec hK hZm hZ hSf hRf φ ψ hφ hψ
    unfold forestCoef
    exact this
  have hδL := raw_kernel_deltaL hdec hK hZ₀ hScRow hR hZm hZ hRL
  have hδR := raw_kernel_deltaR hdec hK hZ₀ hScCol hR hZm hZ hRR
  have hc : 0 ≤ forestCoef ΓF kf r Eproj R Zm := div_nonneg (add_nonneg hσf hR) hZm.le
  -- the forms of `K` and `O` on centred functions
  have hKform : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      kform ν ν K φ ψ = (kform ν ν Sc φ ψ + kform ν ν Rem φ ψ) / Z₀ := by
    intro φ ψ _ hψ
    rw [raw_kernel_form ν K₀ Sc Rem K z Z₀ hdec hK φ ψ hψ, inv_mul_eq_div]
  have hOform : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      kform ν ν O φ ψ = (Lo φ ψ + Mo φ ψ) / Zo := by
    intro φ ψ hφ hψ
    rw [kform_normalized ν O₀ O Zo hO, hOdec φ ψ hφ hψ]
  -- the full bounds `U_h`
  have hUn : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν Sc φ ψ + kform ν ν Rem φ ψ| ≤ forestU ΓF' knew r Enew R * nrm ν φ * nrm ν ψ := by
    intro φ ψ hφ hψ
    have := abs_add_le (kform ν ν Sc φ ψ) (kform ν ν Rem φ ψ)
    have h1 := hLn φ ψ hφ hψ
    have h2 := hRf φ ψ hφ hψ
    unfold forestU
    linarith
  have hUo : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |Lo φ ψ + Mo φ ψ| ≤ forestU ΓF' kold r Eold Rold * nrm ν φ * nrm ν ψ := by
    intro φ ψ hφ hψ
    have := abs_add_le (Lo φ ψ) (Mo φ ψ)
    have h1 := hLo φ ψ hφ hψ
    have h2 := hMo φ ψ hφ hψ
    unfold forestU
    linarith
  have hεn1 : εnew < 1 := by linarith
  have hεo1 : εold < 1 := by linarith
  -- the symmetric part of `Q(K - O)Q`
  have hKOs : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν (fun p => K p - O p) φ ψ + kform ν ν (fun p => K p - O p) ψ φ) / 2| ≤
        forestDRaw ΓF' kΔ r Enew Eold R Rold εnew εold (forestU ΓF' knew r Enew R)
          (forestU ΓF' kold r Eold Rold) * nrm ν φ * nrm ν ψ := by
    intro φ ψ hφ hψ
    rw [kform_sub, kform_sub, hKform φ ψ hφ hψ, hKform ψ φ hψ hφ, hOform φ ψ hφ hψ,
      hOform ψ φ hψ hφ]
    have key := two_normalizer_sym (τ := 1) (n := nrm ν φ * nrm ν ψ) (by norm_num) rfl rfl rfl rfl
      (by rw [one_mul, ← mul_assoc]; exact hLΔ φ ψ hφ hψ)
      (bound_assoc hRf φ ψ hφ hψ) (bound_swap hRf φ ψ hφ hψ)
      (bound_assoc hMo φ ψ hφ hψ) (bound_swap hMo φ ψ hφ hψ)
      (bound_assoc hUn φ ψ hφ hψ) (bound_swap hUn φ ψ hφ hψ)
      (bound_assoc hUo φ ψ hφ hψ) (bound_swap hUo φ ψ hφ hψ) hZn hZo hεn1 hεo1
    rw [one_mul] at key
    have e : forestDRaw ΓF' kΔ r Enew Eold R Rold εnew εold (forestU ΓF' knew r Enew R)
        (forestU ΓF' kold r Eold Rold) * nrm ν φ * nrm ν ψ =
        (ΓF' * kΔ * r + Enew + Eold + R + Rold +
          εnew * forestU ΓF' knew r Enew R / (1 - εnew) +
          εold * forestU ΓF' kold r Eold Rold / (1 - εold)) * (nrm ν φ * nrm ν ψ) := by
      unfold forestDRaw; ring
    rw [e]
    exact key
  -- a crude bound for the skew part (only needed to call the transport lemma)
  have hKOa : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν (fun p => K p - O p) φ ψ - kform ν ν (fun p => K p - O p) ψ φ) / 2| ≤
        ((ΓF' * knew * r + Enew) + (ΓF' * kold * r + Eold) + R + Rold +
          εnew * forestU ΓF' knew r Enew R / (1 - εnew) +
          εold * forestU ΓF' kold r Eold Rold / (1 - εold)) * nrm ν φ * nrm ν ψ := by
    intro φ ψ hφ hψ
    rw [kform_sub, kform_sub, hKform φ ψ hφ hψ, hKform ψ φ hψ hφ, hOform φ ψ hφ hψ,
      hOform ψ φ hψ hφ]
    have hLd : |((kform ν ν Sc φ ψ - Lo φ ψ) + (-1) * (kform ν ν Sc ψ φ - Lo ψ φ)) / 2| ≤
        ((ΓF' * knew * r + Enew) + (ΓF' * kold * r + Eold)) * (nrm ν φ * nrm ν ψ) := by
      have a1 := bound_assoc hLn φ ψ hφ hψ
      have a2 := bound_swap hLn φ ψ hφ hψ
      have a3 := bound_assoc hLo φ ψ hφ hψ
      have a4 := bound_swap hLo φ ψ hφ hψ
      rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have e1 : (kform ν ν Sc φ ψ - Lo φ ψ) + (-1) * (kform ν ν Sc ψ φ - Lo ψ φ) =
          kform ν ν Sc φ ψ - Lo φ ψ - kform ν ν Sc ψ φ + Lo ψ φ := by ring
      rw [e1]
      have t1 := abs_add_le (kform ν ν Sc φ ψ - Lo φ ψ - kform ν ν Sc ψ φ) (Lo ψ φ)
      have t2 := abs_sub (kform ν ν Sc φ ψ - Lo φ ψ) (kform ν ν Sc ψ φ)
      have t3 := abs_sub (kform ν ν Sc φ ψ) (Lo φ ψ)
      nlinarith
    have key := two_normalizer_sym (τ := -1) (n := nrm ν φ * nrm ν ψ) (by norm_num) rfl rfl rfl
      rfl hLd
      (bound_assoc hRf φ ψ hφ hψ) (bound_swap hRf φ ψ hφ hψ)
      (bound_assoc hMo φ ψ hφ hψ) (bound_swap hMo φ ψ hφ hψ)
      (bound_assoc hUn φ ψ hφ hψ) (bound_swap hUn φ ψ hφ hψ)
      (bound_assoc hUo φ ψ hφ hψ) (bound_swap hUo φ ψ hφ hψ) hZn hZo hεn1 hεo1
    have e : ((kform ν ν Sc φ ψ + kform ν ν Rem φ ψ) / Z₀ - (Lo φ ψ + Mo φ ψ) / Zo -
        ((kform ν ν Sc ψ φ + kform ν ν Rem ψ φ) / Z₀ - (Lo ψ φ + Mo ψ φ) / Zo)) / 2 =
        (((kform ν ν Sc φ ψ + kform ν ν Rem φ ψ) / Z₀ - (Lo φ ψ + Mo φ ψ) / Zo) +
          (-1) * ((kform ν ν Sc ψ φ + kform ν ν Rem ψ φ) / Z₀ - (Lo ψ φ + Mo ψ φ) / Zo)) / 2 := by
      ring
    rw [e, mul_assoc]
    exact key
  -- nonnegativity of the two constants handed to the transport lemma
  have hεn0 : 0 ≤ εnew := (abs_nonneg _).trans hZn
  have hεo0 : 0 ≤ εold := (abs_nonneg _).trans hZo
  have hUn0 : 0 ≤ forestU ΓF' knew r Enew R := by
    unfold forestU; linarith
  have hUo0 : 0 ≤ forestU ΓF' kold r Eold Rold := by
    unfold forestU; linarith
  have hqn : 0 ≤ εnew * forestU ΓF' knew r Enew R / (1 - εnew) :=
    div_nonneg (mul_nonneg hεn0 hUn0) (by linarith)
  have hqo : 0 ≤ εold * forestU ΓF' kold r Eold Rold / (1 - εold) :=
    div_nonneg (mul_nonneg hεo0 hUo0) (by linarith)
  have hsO : 0 ≤ forestDRaw ΓF' kΔ r Enew Eold R Rold εnew εold (forestU ΓF' knew r Enew R)
      (forestU ΓF' kold r Eold Rold) := by
    unfold forestDRaw; linarith
  have haO : 0 ≤ (ΓF' * knew * r + Enew) + (ΓF' * kold * r + Eold) + R + Rold +
      εnew * forestU ΓF' knew r Enew R / (1 - εnew) +
      εold * forestU ΓF' kold r Eold Rold / (1 - εold) := by
    linarith
  have hT := centered_transport_difference ν K K' O hmass hc hF hsO haO hKc hδL hδR f g hf hg hK'
    u0 hm1 hm2 hO1 hO2 hu hKOs hKOa φ ψ
  unfold forestDSym
  exact hT.2.1

/-! ## Part (c): the block gates -/

/-- **`prop:forest-records`(c), the block gates**: `c_new < 1/2` and
`c_new² < min(s_new, a_new)`. A numerical condition on the formulas of (a), not a consequence of
the analytic argument: it is checked by the certificates at `2^48` and `2^49` and used in
`lem:record:domain`(ii). -/
def ForestBlockGates (cNew sNew aNew : ℝ) : Prop := cNew < 1 / 2 ∧ cNew ^ 2 < min sNew aNew

/-- **`prop:forest-records`(c)** for FE and EF records, the further gate
`ρ_old² + c_new² < d_sym`. -/
def ForestBlockGatesFE (ρold cNew dsym : ℝ) : Prop := ρold ^ 2 + cNew ^ 2 < dsym

end Sarkozy.UpperComparison
