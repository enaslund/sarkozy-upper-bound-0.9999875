module

public import Sarkozy.PositiveRoots.Normalization
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# The linear root trace (`lem:root-linear`, `eq:root-score-feature`)

`paper/sections/20b_positive_roots.tex`, `eq:root-score-feature` and `lem:root-linear`.

* **`eq:root-score-feature`** (`pairScore_feature`): for distinct pairs `y, y'` the score is
  `H(y, y') = r E_z 𝒰_y(z)𝒰_{y'}(z) + qr` with the normalized pair feature
  `𝒰_y(z) = (ψ_y(z) + q)/r` (`pairFeature`), which is mean zero in `z` (`pairFeature_mean`):
  this is `H₀ = r𝒰_a𝒰_c^* + qr`, `H₁ = r𝒰_b𝒰_b^* + qr`, `H₂ = r𝒰_c𝒰_a^* + qr` as kernels, the
  constant `qr` being `q²/r`.
* **The average of the class prices** (`lin_price_average`): if for each score the centred form
  of `K_soft∘H_j` is `r L_j(f) + qr K(f) + ∑_{k} C_{j,k}(f)` over the six classes
  (rank/rank, rank/star, star/star, rank/remainder, star/remainder, remainder/remainder) with
  `|C_{j,k}(f)| ≤ ε_k^{type(j)}‖f‖²` (core prices for `j = 0, 2`, private prices for `j = 1`;
  the classes `00, 02, 22` have one price) and `‖K_soft‖ ≤ 𝔯₂²`, then the centred form of
  `K_soft∘H̄` is `(r/3)∑_j L_j(f)` up to
  `ε_lin = ε₀₀ + (2ε₀₁,c + ε₀₁,b)/3 + (2ε₁₁,c + ε₁₁,b)/3 + ε₀₂ + (2ε₁₂,c + ε₁₂,b)/3 + ε₂₂ + qr𝔯₂²`
  (`epsLin`), "a core value counted twice and the private value once".
* **The leading term** (`lead_bound`): `|(r/3)(⟨𝒰_a,f⟩⟨𝒰_c,g⟩ + ⟨𝒰_c,f⟩⟨𝒰_a,g⟩ + ⟨𝒰_b,f⟩⟨𝒰_b,g⟩)|
  ≤ r‖f‖‖g‖` when `‖𝒰‖ ≤ 1`; with the two constant-to-feature ranks (each of norm `≤ 𝔩₀r`) and the
  remainder this gives `‖P₀(K_soft∘H̄)‖ ≤ r(1 + 2𝔩₀) + ε_lin` (`full_norm_bound`), and, one
  orientation surviving on `1`, `‖P₀(K_soft∘H̄)1‖ ≤ 𝔩₀r + ε_lin` (`one_bound`).
* `rank_rank_price`: the rank/rank class price `ε₀₀ = r(2δ_𝔯 + δ_𝔯²)` (the perturbation
  algebra; the bound `‖P₀((𝔯 − 1)𝒰)‖ ≤ δ_𝔯` from `lem:spec:affpair`(d) is its hypothesis);
* `ell0_limit`: `𝔩₀ → (2√2 + 2)/3`: at `q = 0`, `A_𝔯 = 𝔯₂ = 1`,
  `(2√30 r h_𝐳 A_𝔯 + 2 r h_𝐞 𝔯₂)/3 = (2√30/√15 + 2)/3 = (2√2 + 2)/3`.

Not formalized: the six class prices themselves (the product maps `𝒰_S × 𝒰_{A₀}`, `R_S`, `R_𝐳`,
`R_𝐰`, `R_𝐯`, `R_𝐞`, the entangled swap); they are the hypotheses `hC` of `lin_price_average`
(see the SYNTH-CHECK comment after the lemma in the paper: the class factorizations were
re-derived in the verification pass, and are kept as the hook for an independent referee).
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy.L20Cap

/-! ## `eq:root-score-feature` -/

section Feature

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The normalized pair feature** `𝒰_y(z) = (ψ_y(z) + q)/r`, `q = 1/n`, `r = n^{-1/2}`. -/
noncomputable def pairFeature (y : F × F) (z : F) : ℝ :=
  (psiP y z + 1 / (Fintype.card F : ℝ)) * Real.sqrt (Fintype.card F)

/-- `∑_z ψ_y(z) = −1` for a distinct pair (`E_zψ_y = −q`). -/
theorem sum_psiP_z (hF : ringChar F ≠ 2) {y : F × F} (hy : y.1 ≠ y.2) : ∑ z, psiP y z = -1 := by
  unfold psiP
  rw [sum_chi_mul_chi hF y.1 y.2]
  simp [hy]

/-- **The pair feature is mean zero**: `∑_z 𝒰_y(z) = 0`. -/
theorem pairFeature_mean (hF : ringChar F ≠ 2) {y : F × F} (hy : y.1 ≠ y.2) :
    ∑ z, pairFeature y z = 0 := by
  have hn : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  unfold pairFeature
  rw [← Finset.sum_mul, sum_add_distrib, sum_psiP_z hF hy]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- **`eq:root-score-feature`**: `H(y, y') = r E_z 𝒰_y(z)𝒰_{y'}(z) + qr` for distinct pairs. -/
theorem pairScore_feature (hF : ringChar F ≠ 2) {y y' : F × F} (hy : y.1 ≠ y.2)
    (hy' : y'.1 ≠ y'.2) :
    pairScore y y' = 1 / Real.sqrt (Fintype.card F) *
        ((1 / (Fintype.card F : ℝ)) * ∑ z, pairFeature y z * pairFeature y' z) +
      1 / (Fintype.card F : ℝ) * (1 / Real.sqrt (Fintype.card F)) := by
  set n : ℝ := (Fintype.card F : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn.le
  have e : ∑ z, pairFeature y z * pairFeature y' z =
      n * (∑ z, psiP y z * psiP y' z) + (∑ z, psiP y z) + (∑ z, psiP y' z) + 1 := by
    unfold pairFeature
    rw [← hn_def]
    have : ∀ z, (psiP y z + 1 / n) * Real.sqrt n * ((psiP y' z + 1 / n) * Real.sqrt n) =
        n * (psiP y z * psiP y' z) + psiP y z + psiP y' z + 1 / n := by
      intro z
      have : (psiP y z + 1 / n) * Real.sqrt n * ((psiP y' z + 1 / n) * Real.sqrt n) =
          (psiP y z + 1 / n) * (psiP y' z + 1 / n) * (Real.sqrt n * Real.sqrt n) := by ring
      rw [this, hss]
      field_simp
      ring
    rw [sum_congr rfl fun z _ => this z, sum_add_distrib, sum_add_distrib, sum_add_distrib,
      ← Finset.mul_sum]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [← hn_def]
    field_simp
  rw [e, sum_psiP_z hF hy, sum_psiP_z hF hy']
  unfold pairScore
  rw [← hn_def]
  field_simp
  ring

end Feature

/-! ## The average of the class prices -/

/-- **`ε_lin`** of `lem:root-linear` (a core value counted twice, the private value once). -/
noncomputable def epsLin (e00 e01c e01b e11c e11b e02 e12c e12b e22 q r r2 : ℝ) : ℝ :=
  e00 + (2 * e01c + e01b) / 3 + (2 * e11c + e11b) / 3 + e02 + (2 * e12c + e12b) / 3 + e22 +
    q * r * r2 ^ 2

/-- **`lem:root-linear`, the first assertion** (the averaging): let `B_j`, `j = 0, 1, 2`, be the
centred forms of `K_soft∘H_j` at a centred `f` with `‖f‖² = N`, and suppose
`B_j = r L_j + qr K + ∑_k C_{j,k}` with `|K| ≤ 𝔯₂²N` and class bounds `|C_{j,k}| ≤ ε N` by the core
prices for `j = 0, 2` and the private prices for `j = 1`. Then
`|(B₀ + B₁ + B₂)/3 − (r/3)(L₀ + L₁ + L₂)| ≤ ε_lin N`. -/
theorem lin_price_average {r q r2 N K e00 e01c e01b e11c e11b e02 e12c e12b e22 : ℝ}
    (hr : 0 ≤ r) (hq : 0 ≤ q)
    (B L : Fin 3 → ℝ) (C : Fin 3 → Fin 6 → ℝ) (hK : |K| ≤ r2 ^ 2 * N)
    (hB : ∀ j, B j = r * L j + q * r * K + ∑ k, C j k)
    (hcore : ∀ j, j ≠ 1 → |C j 0| ≤ e00 * N ∧ |C j 1| ≤ e01c * N ∧ |C j 2| ≤ e11c * N ∧
      |C j 3| ≤ e02 * N ∧ |C j 4| ≤ e12c * N ∧ |C j 5| ≤ e22 * N)
    (hpriv : |C 1 0| ≤ e00 * N ∧ |C 1 1| ≤ e01b * N ∧ |C 1 2| ≤ e11b * N ∧
      |C 1 3| ≤ e02 * N ∧ |C 1 4| ≤ e12b * N ∧ |C 1 5| ≤ e22 * N) :
    |(B 0 + B 1 + B 2) / 3 - r / 3 * (L 0 + L 1 + L 2)| ≤
      epsLin e00 e01c e01b e11c e11b e02 e12c e12b e22 q r r2 * N := by
  have hqr : 0 ≤ q * r := mul_nonneg hq hr
  have e : (B 0 + B 1 + B 2) / 3 - r / 3 * (L 0 + L 1 + L 2) =
      q * r * K + ((C 0 0 + C 1 0 + C 2 0) / 3 + (C 0 1 + C 1 1 + C 2 1) / 3 +
        (C 0 2 + C 1 2 + C 2 2) / 3 + (C 0 3 + C 1 3 + C 2 3) / 3 +
        (C 0 4 + C 1 4 + C 2 4) / 3 + (C 0 5 + C 1 5 + C 2 5) / 3) := by
    rw [hB 0, hB 1, hB 2]
    simp only [Fin.sum_univ_six]
    ring
  rw [e]
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hcore 0 (by decide)
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := hcore 2 (by decide)
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hpriv
  have hK' : |q * r * K| ≤ q * r * (r2 ^ 2 * N) := by
    rw [abs_mul, abs_of_nonneg hqr]
    exact mul_le_mul_of_nonneg_left hK hqr
  unfold epsLin
  have t : ∀ a b c : ℝ, |(a + b + c) / 3| ≤ (|a| + |b| + |c|) / 3 := by
    intro a b c
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans
      (add_le_add (abs_add_le _ _) le_rfl)) (by norm_num)
  have t0 := t (C 0 0) (C 1 0) (C 2 0)
  have t1 := t (C 0 1) (C 1 1) (C 2 1)
  have t2 := t (C 0 2) (C 1 2) (C 2 2)
  have t3 := t (C 0 3) (C 1 3) (C 2 3)
  have t4 := t (C 0 4) (C 1 4) (C 2 4)
  have t5 := t (C 0 5) (C 1 5) (C 2 5)
  have tri : ∀ a b c d e f g : ℝ, |a + (b + c + d + e + f + g)| ≤
      |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    intro a b c d e f g
    calc |a + (b + c + d + e + f + g)| ≤ |a| + |b + c + d + e + f + g| := abs_add_le _ _
      _ ≤ |a| + (|b + c + d + e + f| + |g|) := add_le_add le_rfl (abs_add_le _ _)
      _ ≤ |a| + ((|b + c + d + e| + |f|) + |g|) :=
          add_le_add le_rfl (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |a| + (((|b + c + d| + |e|) + |f|) + |g|) :=
          add_le_add le_rfl (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl)
      _ ≤ |a| + ((((|b + c| + |d|) + |e|) + |f|) + |g|) :=
          add_le_add le_rfl (add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl)
            le_rfl)
      _ ≤ |a| + (((((|b| + |c|) + |d|) + |e|) + |f|) + |g|) :=
          add_le_add le_rfl (add_le_add (add_le_add (add_le_add (add_le_add (abs_add_le _ _)
            le_rfl) le_rfl) le_rfl) le_rfl)
      _ = _ := by ring
  have := tri (q * r * K) ((C 0 0 + C 1 0 + C 2 0) / 3) ((C 0 1 + C 1 1 + C 2 1) / 3)
    ((C 0 2 + C 1 2 + C 2 2) / 3) ((C 0 3 + C 1 3 + C 2 3) / 3) ((C 0 4 + C 1 4 + C 2 4) / 3)
    ((C 0 5 + C 1 5 + C 2 5) / 3)
  nlinarith

/-! ## The norms -/

/-- **The leading pair term has norm at most `r`**: if `|⟨𝒰,f⟩| ≤ ‖f‖` for the three normalized
pair features, then
`|(r/3)(⟨𝒰_a,f⟩⟨𝒰_c,g⟩ + ⟨𝒰_c,f⟩⟨𝒰_a,g⟩ + ⟨𝒰_b,f⟩⟨𝒰_b,g⟩)| ≤ r‖f‖‖g‖`. -/
theorem lead_bound {r af cf bf ag cg bg nf ng : ℝ} (hr : 0 ≤ r)
    (haf : |af| ≤ nf) (hcf : |cf| ≤ nf) (hbf : |bf| ≤ nf)
    (hag : |ag| ≤ ng) (hcg : |cg| ≤ ng) (hbg : |bg| ≤ ng) :
    |r / 3 * (af * cg + cf * ag + bf * bg)| ≤ r * nf * ng := by
  have hnf : 0 ≤ nf := le_trans (abs_nonneg _) haf
  have hng : 0 ≤ ng := le_trans (abs_nonneg _) hag
  have p1 : |af * cg| ≤ nf * ng := by rw [abs_mul]; exact mul_le_mul haf hcg (abs_nonneg _) hnf
  have p2 : |cf * ag| ≤ nf * ng := by rw [abs_mul]; exact mul_le_mul hcf hag (abs_nonneg _) hnf
  have p3 : |bf * bg| ≤ nf * ng := by rw [abs_mul]; exact mul_le_mul hbf hbg (abs_nonneg _) hnf
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ r / 3)]
  have : |af * cg + cf * ag + bf * bg| ≤ 3 * (nf * ng) := by
    calc _ ≤ |af * cg + cf * ag| + |bf * bg| := abs_add_le _ _
      _ ≤ |af * cg| + |cf * ag| + |bf * bg| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  calc r / 3 * |af * cg + cf * ag + bf * bg| ≤ r / 3 * (3 * (nf * ng)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = r * nf * ng := by ring

/-- **`‖P₀(K_soft∘H̄)‖ ≤ r(1 + 2𝔩₀) + ε_lin`**: the leading term (norm `≤ r`), the two
constant-to-feature ranks (each `≤ 𝔩₀r`) and the remainder (`≤ ε_lin`). -/
theorem full_norm_bound {lead rk1 rk2 rem r l0 εlin M : ℝ} (hlead : |lead| ≤ r * M)
    (h1 : |rk1| ≤ l0 * r * M) (h2 : |rk2| ≤ l0 * r * M) (hrem : |rem| ≤ εlin * M) :
    |lead + rk1 + rk2 + rem| ≤ (r * (1 + 2 * l0) + εlin) * M := by
  have := abs_add_le (lead + rk1 + rk2) rem
  have := abs_add_le (lead + rk1) rk2
  have := abs_add_le lead rk1
  nlinarith

/-- **`‖P₀(K_soft∘H̄)1‖ ≤ 𝔩₀r + ε_lin`**: on `1` the leading term vanishes (the features are mean
zero), one rank orientation is killed, and the other is `≤ 𝔩₀r`. -/
theorem one_bound {rk1 rem r l0 εlin : ℝ} (h1 : |rk1| ≤ l0 * r) (hrem : |rem| ≤ εlin) :
    |0 + rk1 + 0 + rem| ≤ l0 * r + εlin := by
  simp only [zero_add, add_zero]
  exact (abs_add_le _ _).trans (add_le_add h1 hrem)

/-- **`𝔩₀ → (2√2 + 2)/3`** (`lem:root-linear`): `rh_𝐳 = 1/√(15(1 − q))`, `rh_𝐞 = 1/√(1 − q)`; at
`q = 0`, `A_𝔯 = 𝔯₂ = 1` the value `(2√30 rh_𝐳 A_𝔯 + 2 rh_𝐞 𝔯₂)/3` is `(2√2 + 2)/3`. -/
theorem ell0_limit :
    (2 * Real.sqrt 30 * (1 / Real.sqrt (15 * (1 - 0))) * 1 + 2 * (1 / Real.sqrt (1 - 0)) * 1) / 3 =
      (2 * Real.sqrt 2 + 2) / 3 := by
  have h15 : 0 < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  have e : Real.sqrt 30 = Real.sqrt 2 * Real.sqrt 15 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  simp only [sub_zero, mul_one, Real.sqrt_one, div_one]
  rw [e]
  field_simp

/-! ## The rank/rank class price -/

/-- **The rank/rank class price `ε₀₀ = r(2δ_𝔯 + δ_𝔯²)`** (proof of `lem:root-linear`, "Rank/rank"):
the class is `r(𝔯𝒰_a)(𝔯𝒰_c)^*`, and after centring `P₀(𝔯𝒰) = 𝒰 + 𝒟` with `‖𝒟‖ ≤ δ_𝔯`. In the
form `⟨f, XY^*g⟩ = ⟨X^*f, Y^*g⟩`, with `a = 𝒰_a^*f`, `d = 𝒟_a^*f`, `c = 𝒰_c^*g`, `e = 𝒟_c^*g`
(`‖𝒰‖ ≤ 1`, `‖𝒟‖ ≤ δ`): `|⟨a + d, c + e⟩ − ⟨a, c⟩| ≤ (2δ + δ²)‖f‖‖g‖`. -/
theorem rank_rank_price {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {a d c e : E}
    {δ nf ng : ℝ} (hδ : 0 ≤ δ) (ha : ‖a‖ ≤ nf) (hd : ‖d‖ ≤ δ * nf) (hc : ‖c‖ ≤ ng)
    (he : ‖e‖ ≤ δ * ng) :
    |inner ℝ (a + d) (c + e) - inner ℝ a c| ≤ (2 * δ + δ ^ 2) * nf * ng := by
  have hnf : 0 ≤ nf := (norm_nonneg a).trans ha
  have hng : 0 ≤ ng := (norm_nonneg c).trans hc
  have e1 : inner ℝ (a + d) (c + e) - inner ℝ a c = inner ℝ a e + inner ℝ d c + inner ℝ d e := by
    simp only [inner_add_left, inner_add_right]
    ring
  rw [e1]
  have t1 : |inner ℝ a e| ≤ nf * (δ * ng) :=
    (abs_real_inner_le_norm a e).trans (mul_le_mul ha he (norm_nonneg _) hnf)
  have t2 : |inner ℝ d c| ≤ (δ * nf) * ng :=
    (abs_real_inner_le_norm d c).trans (mul_le_mul hd hc (norm_nonneg _) (by positivity))
  have t3 : |inner ℝ d e| ≤ (δ * nf) * (δ * ng) :=
    (abs_real_inner_le_norm d e).trans (mul_le_mul hd he (norm_nonneg _) (by positivity))
  have tri : |inner ℝ a e + inner ℝ d c + inner ℝ d e| ≤
      |inner ℝ a e| + |inner ℝ d c| + |inner ℝ d e| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  nlinarith

end Sarkozy.PositiveRoots
