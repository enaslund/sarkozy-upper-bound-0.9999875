module

public import Sarkozy.FiveType.FoldDataRemark
public import Sarkozy.FiveType.JointBlocks
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Joint fold and matching rows, part (a) (`lem:joint-rows`(a))

Source: `paper/sections/16_extraction.tex`, `lem:joint-rows`(a) and its proof ("The actual
chart", "Centring and normalization", "Restriction", "Pure stars").

**Setting** (finite, in the quadratic-form conventions of `FiveType/Datum.lean`). The rows have
the law `μ` on a finite set `Ω`. The raw kernels `K_E`, `K_F` are relative to `μ ⊗ μ`, with
`Z_• = ⟨𝟙, K_•𝟙⟩_μ` (`mass`) and marginal densities `g₁ = K𝟙/Z`, `g₂ = K*𝟙/Z` (`dens1`, `dens2`).
The marginal `ν = gμ` of `π_E` has `g = K_E𝟙/Z_E ≥ e^{-ℓ_E}`. Relative to `ν ⊗ ν` the densities of
`π_•` are `T_•(x, y) = K_•(x, y)/(Z_• g(x) g(y))` (`relDensity`), and
`C_F = T_F - u_L ⊗ u_R = foldCov ν T_F`, `C_E = T_E - J = matchCov T_E` (the objects of
`FiveType/JointBlocks.lean`). The joint block `(C_E C_F; C_F* C_E) ⪰ -𝔨 I` on `L²(ν) ⊕ L²(ν)` is
`JointBlockLower ν C_E C_F 𝔨`.

**Proved** (the lemma's own steps):
* *the actual chart* (`kf_foldCov_chart`, `kf_matchCov_chart`):
  `⟨f, C_F h⟩_ν = ⟨f, (K_F/Z_F - g_L ⊗ g_R) h⟩_μ`, `⟨f, C_E h⟩_ν = ⟨f, (K_E/Z_E - g ⊗ g) h⟩_μ`,
  and `‖f‖²_μ ≤ e^{ℓ_E} ‖f‖²_ν` (`nrm_sq_le_of_density`);
* *centring* (`chart_centring`): `K/Z - g₁ ⊗ g₂ = P₀KP₀/Z - (g₁ - 𝟙) ⊗ (g₂ - 𝟙)`, and the rank-one
  term has norm at most `m²/(1 - ε)²` (`nrm_dens1_sub_one`);
* *normalization* (`row_error_bound`): with the expansion `K = 𝟙 ⊗ 𝟙 + K^{st} + T_{ns} - T_{coll}`
  on the support, `K/Z - g₁ ⊗ g₂` differs from `P₀K^{st}P₀` by at most
  `𝔠 = (εS⋆ + N)/(1 - ε) + m²/(1 - ε)²` in norm (`cconst`);
* in `RowsAChain.lean`: *restriction* (`𝕋 ⪰ -c'I` gives `𝕂^{st} ⪰ -(c'/I₀)I`) and the chain
  `joint_rows_chain` (`𝕋 ⪰ -c'I` gives the joint block `⪰ -e^{ℓ_E}(c'/I₀ + 𝔠_F + 𝔠_E) I`);
  *pure stars* (`pure_star_bound`: `𝕋 = κ₀r 𝒲𝕄𝒲* + 𝕋_mean` with a contraction `𝒲`,
  `‖𝕋_mean‖ ≤ κ₀r(e_F + e_E)` and `𝕄 ⪰ -𝗄I` give `𝕋 ⪰ -κ₀r(𝗄 + e_F + e_E)I`); and
  **`joint_rows_a`**, the conclusion of (a), `𝔨_p = e^{ℓ_E}[κ₀r(𝗄 + e_F + e_E)/I₀ + 𝔠_F + 𝔠_E]`;
* in `RowsAGate.lean`: `eq:joint-gate` gives `𝕄 ⪰ -𝗄I` on both sectors (`joint_rows_a_gate`);
* the preliminaries: `C_E` is symmetric when `K_E` is (`matchCov_symm`); `A_{D_E} = B_{D_E}` when
  `D_Eᵀ = -D_E` (`starA_eq_starB`); `C_F`, `C_E` annihilate the constants
  (`RowsAPrelim.lean`).

**Hypotheses (cited, with labels):**
* `lem:spec:expansion` with the collision part of `prop:pinned-collision`: the expansion
  `K_• = 𝟙 ⊗ 𝟙 + K^{st}_• + T^•_{ns} - T^•_{coll}` on the support of `μ` (`hexpE`, `hexpF`), with
  the
  norm bounds `S⋆_• ≥ ‖P₀K^{st}_•P₀‖`, `‖T^•_{ns}‖ ≤ n`, `‖T^•_{coll}‖ ≤ n'`, `n + n' ≤ N_•`,
  `|Z_• - 1| ≤ ε_• < 1`, `m_• ≥ ‖P₀K_•𝟙‖, ‖P₀K_•*𝟙‖` (the lemma's own hypotheses);
* `lem:restriction`(a): the form of `𝕂^{st}` at centred `(Φ, Ψ)` is `⟨ιF, 𝕋 ιF⟩/P`, with `ι` an
  isometry and `P = λ(𝓘_pin) ≥ I₀` (`hrestr`); `𝕋` is the joint block of the star operators,
  here a quadratic form `qT` on a real inner product space `E`;
* `prop:conditional-star`(b),(c): the decomposition of `𝕋` (`hTdec`, `hV`, `hmean`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace RowsA

variable {Ω : Type*} [Fintype Ω]

/-- `Z = ⟨𝟙, K𝟙⟩_μ`. -/
noncomputable def mass (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) : ℝ := kf μ K (fun _ => 1) (fun _ => 1)

/-- `g₁ = K𝟙/Z`, the density of the first marginal of `Kμ⊗μ/Z` relative to `μ`. -/
noncomputable def dens1 (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) (x : Ω) : ℝ := kone μ K x / mass μ K

/-- `g₂ = K*𝟙/Z`. -/
noncomputable def dens2 (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) (y : Ω) : ℝ := kone' μ K y / mass μ K

/-- The density `K(x, y)/(Z g(x) g(y))` of `Kμ⊗μ/Z` relative to `ν ⊗ ν`, `ν = gμ`. -/
noncomputable def relDensity (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) (g : Ω → ℝ) (x y : Ω) : ℝ :=
  K x y / (mass μ K * g x * g y)

/-- The kernel `K/Z - g₁ ⊗ g₂` relative to `μ ⊗ μ`. -/
noncomputable def chartKernel (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) (x y : Ω) : ℝ :=
  K x y / mass μ K - dens1 μ K x * dens2 μ K y

/-- The error constant `𝔠 = (εS⋆ + N)/(1 - ε) + m²/(1 - ε)²`. -/
noncomputable def cconst (ε S N m : ℝ) : ℝ := (ε * S + N) / (1 - ε) + m ^ 2 / (1 - ε) ^ 2

/-! ## Preliminaries -/

/-- `C_E = T_E - J` is symmetric when the raw kernel is. -/
theorem matchCov_symm (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) (g : Ω → ℝ) (hK : ∀ x y, K x y = K y x)
    (x y : Ω) : matchCov (relDensity μ K g) x y = matchCov (relDensity μ K g) y x := by
  simp only [matchCov, relDensity, hK x y]
  ring_nf

/-- `A_{D_E} = B_{D_E}` when `D_Eᵀ = -D_E`: `(-1)^{|S|} ∏_{j∈S} D(i, j) = ∏_{j∈S} D(j, i)`. -/
theorem starA_eq_starB {n : Type*} (D : n → n → ℝ) (hD : ∀ i j, D j i = -D i j) (i : n)
    (S : Finset n) : (-1 : ℝ) ^ S.card * ∏ j ∈ S, D i j = ∏ j ∈ S, D j i := by
  rw [Finset.prod_congr rfl (fun j _ => hD i j), Finset.prod_neg]

/-! ## The actual chart -/

theorem kone_relDensity (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (hν : ∀ x, ν.weight x = g x * μ.weight x)
    (hg : ∀ x, μ.weight x ≠ 0 → 0 < g x) (K : Ω → Ω → ℝ) (x : Ω) (hx : μ.weight x ≠ 0) :
    kone ν (relDensity μ K g) x = dens1 μ K x / g x := by
  have hgx := (hg x hx).ne'
  unfold dens1 relDensity
  rw [div_div, show kone μ K x = ∑ y, μ.weight y * K x y from rfl, Finset.sum_div]
  unfold kone
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hν]
  by_cases hy : μ.weight y = 0
  · rw [hy]; simp
  · have hgy := (hg y hy).ne'
    field_simp

theorem kone'_relDensity (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (hν : ∀ x, ν.weight x = g x * μ.weight x)
    (hg : ∀ x, μ.weight x ≠ 0 → 0 < g x) (K : Ω → Ω → ℝ) (y : Ω) (hy : μ.weight y ≠ 0) :
    kone' ν (relDensity μ K g) y = dens2 μ K y / g y := by
  have hgy := (hg y hy).ne'
  unfold dens2 relDensity
  rw [div_div, show kone' μ K y = ∑ x, μ.weight x * K x y from rfl, Finset.sum_div]
  unfold kone'
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hν]
  by_cases hx : μ.weight x = 0
  · rw [hx]; simp
  · have hgx := (hg x hx).ne'
    field_simp

/-- **The actual chart, fold row**: `⟨f, C_F h⟩_ν = ⟨f, (K_F/Z_F - g_L ⊗ g_R) h⟩_μ`. -/
theorem kf_foldCov_chart (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (hν : ∀ x, ν.weight x = g x * μ.weight x)
    (hg : ∀ x, μ.weight x ≠ 0 → 0 < g x) (K : Ω → Ω → ℝ) (f h : Ω → ℝ) :
    kf ν (foldCov ν (relDensity μ K g)) f h = kf μ (chartKernel μ K) f h := by
  unfold kf
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : μ.weight x = 0
  · rw [hν, hx]; simp
  by_cases hy : μ.weight y = 0
  · rw [hν y, hy]; simp
  have hgx := (hg x hx).ne'
  have hgy := (hg y hy).ne'
  simp only [foldCov, chartKernel]
  rw [kone_relDensity μ ν g hν hg K x hx, kone'_relDensity μ ν g hν hg K y hy, hν, hν]
  unfold relDensity
  field_simp

/-- **The actual chart, matching row**: `⟨f, C_E h⟩_ν = ⟨f, (K_E/Z_E - g ⊗ g) h⟩_μ` when `g` is
the marginal density, `g = K_E𝟙/Z_E = K_E*𝟙/Z_E` on the support. -/
theorem kf_matchCov_chart (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (hν : ∀ x, ν.weight x = g x * μ.weight x)
    (hg : ∀ x, μ.weight x ≠ 0 → 0 < g x) (K : Ω → Ω → ℝ)
    (hg1 : ∀ x, μ.weight x ≠ 0 → g x = dens1 μ K x) (hg2 : ∀ x, μ.weight x ≠ 0 → g x = dens2 μ K x)
    (f h : Ω → ℝ) :
    kf ν (matchCov (relDensity μ K g)) f h = kf μ (chartKernel μ K) f h := by
  unfold kf
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : μ.weight x = 0
  · rw [hν, hx]; simp
  by_cases hy : μ.weight y = 0
  · rw [hν y, hy]; simp
  have hgx := (hg x hx).ne'
  have hgy := (hg y hy).ne'
  simp only [matchCov, chartKernel]
  rw [← hg1 x hx, ← hg2 y hy, hν, hν]
  unfold relDensity
  field_simp

/-- **`‖f‖²_μ ≤ e^{ℓ} ‖f‖²_ν`** when `ν = gμ` with `g ≥ e^{-ℓ}` on the support. -/
theorem nrm_sq_le_of_density (μ ν : FiniteLaw Ω) (g : Ω → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * μ.weight x) (hg : ∀ x, μ.weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (f : Ω → ℝ) : nrm μ f ^ 2 ≤ Real.exp ℓ * nrm ν f ^ 2 := by
  rw [← ip_self_eq, ← ip_self_eq]
  unfold ip FiniteLaw.expect
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [hν]
  by_cases hx : μ.weight x = 0
  · rw [hx]; simp
  have h1 : 1 ≤ Real.exp ℓ * g x := by
    have := mul_le_mul_of_nonneg_left (hg x hx) (Real.exp_pos ℓ).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
  have h2 : 0 ≤ μ.weight x * (f x * f x) := mul_nonneg (μ.nonneg x) (mul_self_nonneg _)
  nlinarith

/-! ## Centring and normalization -/

/-- **The centring identity**, in form: `⟨f, (K/Z - g₁ ⊗ g₂) h⟩ = ⟨f, P₀KP₀ h⟩/Z
- ⟨f, g₁ - 𝟙⟩⟨g₂ - 𝟙, h⟩`. -/
theorem chart_centring (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) (hZ : mass μ K ≠ 0) (f h : Ω → ℝ) :
    kf μ (chartKernel μ K) f h = kf μ K (cen μ f) (cen μ h) / mass μ K -
      ip μ f (fun x => dens1 μ K x - 1) * ip μ (fun y => dens2 μ K y - 1) h := by
  have hlin : kf μ (chartKernel μ K) f h =
      kf μ K f h / mass μ K - ip μ f (dens1 μ K) * ip μ (dens2 μ K) h := by
    simp only [kf, chartKernel, ip, FiniteLaw.expect, Finset.sum_div, Finset.sum_mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have hcen : kf μ K (cen μ f) (cen μ h) = μ.expect f * μ.expect h * mass μ K -
      μ.expect f * kf μ K (fun _ => 1) h - μ.expect h * kf μ K f (fun _ => 1) + kf μ K f h := by
    have e1 : cen μ f = fun x => -μ.expect f + f x := funext fun x => by unfold cen; ring
    have e2 : cen μ h = fun y => -μ.expect h + h y := funext fun y => by unfold cen; ring
    rw [e1, e2, kf_add_const]
    unfold mass
    ring
  have h1 : kf μ K (fun _ => 1) h = mass μ K * ip μ (dens2 μ K) h := by
    rw [kf_one_left]
    unfold ip dens2 FiniteLaw.expect
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    field_simp
  have h2 : kf μ K f (fun _ => 1) = mass μ K * ip μ f (dens1 μ K) := by
    rw [kf_one_right]
    unfold ip dens1 FiniteLaw.expect
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    field_simp
  have h3 : ip μ f (fun x => dens1 μ K x - 1) = ip μ f (dens1 μ K) - μ.expect f := by
    unfold ip
    rw [← FiniteLaw.expect_sub]
    exact μ.expect_congr fun x => by ring
  have h4 : ip μ (fun y => dens2 μ K y - 1) h = ip μ (dens2 μ K) h - μ.expect h := by
    unfold ip
    rw [← FiniteLaw.expect_sub]
    exact μ.expect_congr fun y => by ring
  rw [hlin, hcen, h1, h2, h3, h4]
  field_simp
  ring

/-- `g₁ - 𝟙 = P₀K𝟙/Z`, so `‖g₁ - 𝟙‖ ≤ m/(1 - ε)`. -/
theorem nrm_dens1_sub_one (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) {ε m : ℝ}
    (hε : |mass μ K - 1| ≤ ε) (hε1 : ε < 1) (hm : nrm μ (cen μ (kone μ K)) ≤ m) :
    nrm μ (fun x => dens1 μ K x - 1) ≤ m / (1 - ε) := by
  have hZ : 1 - ε ≤ mass μ K := by
    have := neg_abs_le (mass μ K - 1); linarith
  have hZ0 : 0 < mass μ K := by linarith
  have hZne : kf μ K (fun _ => 1) (fun _ => 1) ≠ 0 := hZ0.ne'
  have he : (fun x => dens1 μ K x - 1) = fun x => (mass μ K)⁻¹ * cen μ (kone μ K) x := by
    funext x
    unfold dens1 cen
    rw [← kf_one_one]
    unfold mass
    field_simp
  rw [he, nrm_smul, abs_of_pos (inv_pos.mpr hZ0)]
  rw [inv_mul_eq_div]
  have hm0 : 0 ≤ m := le_trans (FiveType.nrm_nonneg _ _) hm
  calc nrm μ (cen μ (kone μ K)) / mass μ K ≤ m / mass μ K :=
        div_le_div_of_nonneg_right hm hZ0.le
    _ ≤ m / (1 - ε) := div_le_div_of_nonneg_left hm0 (by linarith) hZ

theorem nrm_dens2_sub_one (μ : FiniteLaw Ω) (K : Ω → Ω → ℝ) {ε m : ℝ}
    (hε : |mass μ K - 1| ≤ ε) (hε1 : ε < 1) (hm : nrm μ (cen μ (kone' μ K)) ≤ m) :
    nrm μ (fun x => dens2 μ K x - 1) ≤ m / (1 - ε) := by
  have hZ : 1 - ε ≤ mass μ K := by
    have := neg_abs_le (mass μ K - 1); linarith
  have hZ0 : 0 < mass μ K := by linarith
  have hZne : kf μ K (fun _ => 1) (fun _ => 1) ≠ 0 := hZ0.ne'
  have he : (fun x => dens2 μ K x - 1) = fun x => (mass μ K)⁻¹ * cen μ (kone' μ K) x := by
    funext x
    unfold dens2 cen
    rw [← kf_one_one']
    unfold mass
    field_simp
  rw [he, nrm_smul, abs_of_pos (inv_pos.mpr hZ0)]
  rw [inv_mul_eq_div]
  have hm0 : 0 ≤ m := le_trans (FiveType.nrm_nonneg _ _) hm
  calc nrm μ (cen μ (kone' μ K)) / mass μ K ≤ m / mass μ K :=
        div_le_div_of_nonneg_right hm hZ0.le
    _ ≤ m / (1 - ε) := div_le_div_of_nonneg_left hm0 (by linarith) hZ

/-- A form bound is nonnegative. -/
theorem FormBound.nonneg' {μ : FiniteLaw Ω} {A : Ω → Ω → ℝ} {e : ℝ} (h : FormBound μ A e) :
    0 ≤ e := by
  have h11 := h (fun _ => 1) (fun _ => 1)
  have hn : nrm μ (fun _ => (1 : ℝ)) = 1 := by
    unfold nrm ip
    simp only [mul_one, FiniteLaw.expect_const, Real.sqrt_one]
  rw [hn, mul_one, mul_one] at h11
  exact le_trans (abs_nonneg _) h11

/-- The centred part has the smaller norm. -/
theorem nrm_cen_le (μ : FiniteLaw Ω) (f : Ω → ℝ) : nrm μ (cen μ f) ≤ nrm μ f := by
  unfold nrm
  apply Real.sqrt_le_sqrt
  have := ip_self_split μ f
  nlinarith [sq_nonneg (μ.expect f)]

/-- **Normalization**: with `K = 𝟙 ⊗ 𝟙 + K^{st} + T_{ns} - T_{coll}` on the support of `μ`,
`|⟨f, (K/Z - g₁ ⊗ g₂) h⟩ - ⟨f, P₀K^{st}P₀ h⟩| ≤ 𝔠 ‖f‖ ‖h‖`,
`𝔠 = (εS⋆ + N)/(1 - ε) + m²/(1 - ε)²`. -/
theorem row_error_bound (μ : FiniteLaw Ω) (K Kst Tns Tcoll : Ω → Ω → ℝ)
    (hexp : ∀ x y, μ.weight x ≠ 0 → μ.weight y ≠ 0 → K x y = 1 + Kst x y + Tns x y - Tcoll x y)
    {ε S N n1 n2 m : ℝ} (hε : |mass μ K - 1| ≤ ε) (hε1 : ε < 1) (hS0 : 0 ≤ S)
    (hSt : PerpBound μ Kst S) (hns : FormBound μ Tns n1) (hcoll : FormBound μ Tcoll n2)
    (hN : n1 + n2 ≤ N) (hm1 : nrm μ (cen μ (kone μ K)) ≤ m)
    (hm2 : nrm μ (cen μ (kone' μ K)) ≤ m) (f h : Ω → ℝ) :
    |kf μ (chartKernel μ K) f h - kf μ Kst (cen μ f) (cen μ h)| ≤
      cconst ε S N m * nrm μ f * nrm μ h := by
  have hZ : 1 - ε ≤ mass μ K := by
    have := neg_abs_le (mass μ K - 1); linarith
  have hZ0 : 0 < mass μ K := by linarith
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hε
  have hn1 := FormBound.nonneg' hns
  have hn2 := FormBound.nonneg' hcoll
  have hm0 : 0 ≤ m := le_trans (FiveType.nrm_nonneg _ _) hm1
  set a := nrm μ f
  set b := nrm μ h
  have ha : 0 ≤ a := FiveType.nrm_nonneg _ _
  have hb : 0 ≤ b := FiveType.nrm_nonneg _ _
  have hca := nrm_cen_le μ f
  have hcb := nrm_cen_le μ h
  -- the expansion on centred functions
  have hK : kf μ K (cen μ f) (cen μ h) = kf μ Kst (cen μ f) (cen μ h) +
      kf μ Tns (cen μ f) (cen μ h) - kf μ Tcoll (cen μ f) (cen μ h) := by
    have h1 : kf μ (fun _ _ => (1 : ℝ)) (cen μ f) (cen μ h) = 0 := by
      have : kf μ (fun _ _ => (1 : ℝ)) (cen μ f) (cen μ h) =
          μ.expect (cen μ f) * μ.expect (cen μ h) := by
        simp only [kf, FiniteLaw.expect, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        ring
      rw [this, expect_cen, zero_mul]
    have h2 : kf μ K (cen μ f) (cen μ h) = kf μ (fun _ _ => (1 : ℝ)) (cen μ f) (cen μ h) +
        kf μ Kst (cen μ f) (cen μ h) + kf μ Tns (cen μ f) (cen μ h) -
        kf μ Tcoll (cen μ f) (cen μ h) := by
      simp only [kf, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      by_cases hx : μ.weight x = 0
      · rw [hx]; ring
      by_cases hy : μ.weight y = 0
      · rw [hy]; ring
      rw [hexp x y hx hy]
      ring
    rw [h2, h1, zero_add]
  -- the three error terms
  set kst := kf μ Kst (cen μ f) (cen μ h)
  have bst : |kst| ≤ S * a * b := by
    have := hSt (cen μ f) (cen μ h) (expect_cen μ f) (expect_cen μ h)
    calc |kst| ≤ S * nrm μ (cen μ f) * nrm μ (cen μ h) := this
      _ ≤ S * a * b := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hca hcb (FiveType.nrm_nonneg _ _) ha) hS0
  have bns : |kf μ Tns (cen μ f) (cen μ h)| ≤ n1 * a * b := by
    calc _ ≤ n1 * nrm μ (cen μ f) * nrm μ (cen μ h) := hns _ _
      _ ≤ n1 * a * b := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hca hcb (FiveType.nrm_nonneg _ _) ha) hn1
  have bcoll : |kf μ Tcoll (cen μ f) (cen μ h)| ≤ n2 * a * b := by
    calc _ ≤ n2 * nrm μ (cen μ f) * nrm μ (cen μ h) := hcoll _ _
      _ ≤ n2 * a * b := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hca hcb (FiveType.nrm_nonneg _ _) ha) hn2
  have brank : |ip μ f (fun x => dens1 μ K x - 1) * ip μ (fun y => dens2 μ K y - 1) h| ≤
      m ^ 2 / (1 - ε) ^ 2 * a * b := by
    rw [abs_mul]
    have r1 : |ip μ f (fun x => dens1 μ K x - 1)| ≤ a * (m / (1 - ε)) :=
      (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_left (nrm_dens1_sub_one μ K hε hε1 hm1) ha)
    have r2 : |ip μ (fun y => dens2 μ K y - 1) h| ≤ (m / (1 - ε)) * b :=
      (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_right (nrm_dens2_sub_one μ K hε hε1 hm2) hb)
    calc _ ≤ (a * (m / (1 - ε))) * ((m / (1 - ε)) * b) :=
          mul_le_mul r1 r2 (abs_nonneg _) (mul_nonneg ha (div_nonneg hm0 (by linarith)))
      _ = (m / (1 - ε)) ^ 2 * a * b := by ring
      _ = m ^ 2 / (1 - ε) ^ 2 * a * b := by rw [div_pow]
  -- assemble
  have hZinv : |1 / mass μ K - 1| ≤ ε / (1 - ε) := by
    rw [show 1 / mass μ K - 1 = (1 - mass μ K) / mass μ K by field_simp, abs_div,
      abs_of_pos hZ0, abs_sub_comm]
    exact div_le_div₀ hε0 hε (by linarith) hZ
  have hZinv' : 1 / mass μ K ≤ 1 / (1 - ε) := one_div_le_one_div_of_le (by linarith) hZ
  rw [chart_centring μ K hZ0.ne', hK]
  have key : kf μ Kst (cen μ f) (cen μ h) / mass μ K + kf μ Tns (cen μ f) (cen μ h) / mass μ K -
      kf μ Tcoll (cen μ f) (cen μ h) / mass μ K -
      ip μ f (fun x => dens1 μ K x - 1) * ip μ (fun y => dens2 μ K y - 1) h - kst =
      (1 / mass μ K - 1) * kst + (1 / mass μ K) * (kf μ Tns (cen μ f) (cen μ h) -
        kf μ Tcoll (cen μ f) (cen μ h)) -
      ip μ f (fun x => dens1 μ K x - 1) * ip μ (fun y => dens2 μ K y - 1) h := by
    ring
  rw [show (kst + kf μ Tns (cen μ f) (cen μ h) - kf μ Tcoll (cen μ f) (cen μ h)) / mass μ K -
      ip μ f (fun x => dens1 μ K x - 1) * ip μ (fun y => dens2 μ K y - 1) h - kst =
      kf μ Kst (cen μ f) (cen μ h) / mass μ K + kf μ Tns (cen μ f) (cen μ h) / mass μ K -
      kf μ Tcoll (cen μ f) (cen μ h) / mass μ K -
      ip μ f (fun x => dens1 μ K x - 1) * ip μ (fun y => dens2 μ K y - 1) h - kst by ring, key]
  have t1 : |(1 / mass μ K - 1) * kst| ≤ ε / (1 - ε) * (S * a * b) := by
    rw [abs_mul]
    exact mul_le_mul hZinv bst (abs_nonneg _) (div_nonneg hε0 (by linarith))
  have t2 : |(1 / mass μ K) * (kf μ Tns (cen μ f) (cen μ h) - kf μ Tcoll (cen μ f) (cen μ h))| ≤
      1 / (1 - ε) * ((n1 + n2) * a * b) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / mass μ K)]
    have : |kf μ Tns (cen μ f) (cen μ h) - kf μ Tcoll (cen μ f) (cen μ h)| ≤ (n1 + n2) * a * b := by
      calc _ ≤ |kf μ Tns (cen μ f) (cen μ h)| + |kf μ Tcoll (cen μ f) (cen μ h)| := abs_sub _ _
        _ ≤ n1 * a * b + n2 * a * b := add_le_add bns bcoll
        _ = (n1 + n2) * a * b := by ring
    exact mul_le_mul hZinv' this (abs_nonneg _) (by positivity)
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have t3 : 1 / (1 - ε) * ((n1 + n2) * a * b) ≤ 1 / (1 - ε) * (N * a * b) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_right hN hab
    nlinarith
  calc _ ≤ |(1 / mass μ K - 1) * kst| + |(1 / mass μ K) * (kf μ Tns (cen μ f) (cen μ h) -
        kf μ Tcoll (cen μ f) (cen μ h))| +
        |ip μ f (fun x => dens1 μ K x - 1) * ip μ (fun y => dens2 μ K y - 1) h| := by
          have := abs_sub ((1 / mass μ K - 1) * kst + (1 / mass μ K) *
            (kf μ Tns (cen μ f) (cen μ h) - kf μ Tcoll (cen μ f) (cen μ h)))
            (ip μ f (fun x => dens1 μ K x - 1) * ip μ (fun y => dens2 μ K y - 1) h)
          have := abs_add_le ((1 / mass μ K - 1) * kst) ((1 / mass μ K) *
            (kf μ Tns (cen μ f) (cen μ h) - kf μ Tcoll (cen μ f) (cen μ h)))
          linarith
    _ ≤ ε / (1 - ε) * (S * a * b) + 1 / (1 - ε) * (N * a * b) + m ^ 2 / (1 - ε) ^ 2 * a * b := by
          linarith
    _ = cconst ε S N m * a * b := by
          unfold cconst
          field_simp

end RowsA

end Sarkozy.JointRows
