module

public import Sarkozy.PositiveRoots.RootCubic
public import Sarkozy.Cuts.Tilt
public import Sarkozy.Cuts.Envelope

@[expose] public section

/-!
# The chamber cut of a positive root (`prop:root-chamber`)

`paper/sections/20b_positive_roots.tex`, `prop:root-chamber` and its proof. The setting is the
form framework of `Sarkozy.Cuts`: `(X, ν)` is the fixed uniform actual half chart `L²(μ_p)`,
`K₀ ≥ 0` the raw kernel of the uniform root (`K₀ = K^μ_soft − T_coll`), `T₀ = K₀/Z₀` its cut
operator, `η₀, η₁, η₂` the three scores as functions of a pair of halves, permuted by the
transposition (`lem:positive-root-properties`(c)), `H̄ = η̄` their mean (`etaBar`) and
`V = (1/3)∑ η_j²` (`sqMean`). The feature synthesis enters through its adjoint
`F^* : L²(μ_p) → ℂ^{U⊔𝒮}` (`Fadj`), with the frame cap `|F^*f|² ≤ Γ₂₀‖f‖²`
(`lem:l20-star-matrix`(b)), and the star matrices `M = softM D20`, `M_λ = Mlam λ` of
`lem:root-pair-matrix` (`PairMatrix`).

* `individual_weight_eq`: `w_u = (1/3)∑_j(1 + uη_j)² = 1 + 2uH̄ + u²V` (`def:positive-root`,
  "Thus").
* `tilt_centred_form` (**the tilt**, proof of `prop:root-chamber`): from the base-kernel
  decomposition `P₀K₀P₀ = r𝓕M𝓕^* + P₀𝔯_μ𝔯_μ^*P₀ + 𝓡₀`, `‖𝓡₀‖ ≤ ε₀` (hypothesis `hbase`), the
  linear price `P₀(K₀∘H̄)P₀ = (r/3)𝓕P𝓕^* + 𝓡_lin`, `‖𝓡_lin‖ ≤ ε^raw_lin` (`hlin`,
  `lem:root-normalization`(a)) and the square price `‖K₀∘V − K₀‖ ≤ ε^raw_sq` (`hsq`, the same),
  `P₀(K₀∘w_u)P₀ = s r𝓕M_λ𝓕^* + sP₀𝔯_μ𝔯_μ^*P₀ + 𝓡_u`, `‖𝓡_u‖ ≤ ε_u = sε₀ + 2uε^raw_lin + u²ε^raw_sq`,
  with `s = 1 + u²` and `λ = 2u/s`.
* `tilt_centred_bounds`: with `M_λ ⪰ −gI` (`g ≥ g(λ)`) and `‖M_λ‖ ≤ √30 + λ/3`:
  `P₀(K₀∘w_u)P₀ ⪰ −(sgrΓ₂₀ + ε_u)` and `‖P₀(K₀∘w_u)P₀‖ ≤ s(√30 + λ/3)rΓ₂₀ + ε_u + s d²_𝔯/h'_p`.
* **`root_chamber`** (`prop:root-chamber`, the caps at a prime): with the inputs of
  `lem:tilt-marginals` (`Cuts.tilt_marginals`) — `(c_V, δ₀, e, ℓ, h, c, b) =
  (1, (χ⁺_p)^{1/2}, ε_sq, 𝔩, h₀, c_cond, 2 + r)` — the tilted cut operator
  `T_u = (K₀∘w_u)/⟨1,(K₀∘w_u)1⟩` (`Cuts.tiltKernel` of `T₀`) satisfies
  `−(g_ch + d_u²/(1 + g_ch)) I ⪯ T_u ⪯ (1 + d_u²/(1 − c_ch)) I`, `‖T_u1 − 1‖ ≤ d_u` and the
  range ratio `R_p(1 + u(2 + r))²/(1 − uc_cond)²`, with the paper's
  `z₋ = s − 2uh₀ − u²ε_sq`, `z_raw = (1 − ε_Z)z₋`, `g_ch = (sgrΓ₂₀ + ε_u)/z_raw`,
  `c_ch = (s(√30 + λ/3)rΓ₂₀ + ε_u + s d²_𝔯/h'_p)/z_raw`, `d_u = (s√χ⁺_p + 2u𝔩 + u²ε_sq)/z₋`,
  `ε_sq = ε^raw_sq/(1 − ε_Z)`. The constant block uses `prop:matching:positive`(a), (a′)
  (`Cuts.envelope_lower`, `Cuts.envelope_upper`).
* `root_chamber_endpoint`: the same bounds in the endpoint normalization
  `−g^u_{20} r ⪯ T_u ⪯ 1 + c^{+,u}_{20} q`, `g^u_{20} = (g_ch + d_u²/(1+g_ch))/r`,
  `c^{+,u}_{20} = d_u²/(q(1 − c_ch))`.
* `negCoef_mono`, `posCoef_mono`: the monotonicity used in "Uniformity": `G + D²r/(1 + Gr)` is
  nondecreasing in `G`, `D`, `r ≥ 0` on `Dr < 1`, and `D²/(1 − C)` in `D ≥ 0`, `C < 1` (so values
  at an endpoint bound every larger prime once `G, D, C` are majorized there).

**Hypotheses, by label.** `hbase`: the base kernel of the proof (`prop:l20-rectangular`(a),(b),
`prop:l20-rank4`, `prop:l20-collisions`(a), `lem:restriction`; its constant `ε₀` is the paper's
formula, not re-derived here). `hlin`, `hsq`, `hl`: `lem:root-normalization`(a). `hh`:
`lem:root-normalization`(b). `hc`: `lem:root-normalization`(c). `hb`:
`lem:positive-root-properties`(a) (`|H_j| ≤ 2 + r` on the support, `thm:weil`(b)). `hδ`, `hR`:
`lem:record:root-marginal`(ii), (i) with `eq:record:root-count`. `hF`: `lem:l20-star-matrix`(b).
`hZ`: `prop:l20-completion`. `hg`: `g ≥ g(λ)` (`lem:root-pair-matrix`, `RootCubic`). The
constants `ε₀, ε^raw_lin, ε^raw_sq, d²_𝔯/h'_p` are nonnegative by their formulas; this is assumed
(`hε0`, `hεlin`, `hεsq`, `hdr2`). The
identification of the abstract `T₀` with the L20 cut operator of `λ_p(G_{L,2})`
(`lem:spec:cutkernel`(f)) is not formalized here (see W3's `Caps.cutT`). The block caps
(`lem:spec:tensorcomp`(b)) are W3's `Caps.block_cap` applied to these per-prime bounds and are not
repeated.
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.SpectralC Sarkozy.L20Cap
open Sarkozy.SpectralD.StarMatrix

variable {X : Type*} [Fintype X]

/-- The mean of the squares of the scores, `V = (1/3)∑_j η_j²` (`def:positive-root`). -/
noncomputable def sqMean (η : Fin 3 → X → X → ℝ) : X → X → ℝ :=
  fun x y => (1 / 3) * ∑ j, η j x y ^ 2

omit [Fintype X] in
/-- **`w_u = 1 + 2uH̄ + u²V`** (`def:positive-root`, "Thus"): the individual-square weight is
`(1/3)∑_j(1 + uη_j)²`. -/
theorem individual_weight_eq (η : Fin 3 → X → X → ℝ) (u : ℝ) (x y : X) :
    (1 / 3) * ∑ j, (1 + u * η j x y) ^ 2 = 1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y := by
  unfold etaBar sqMean
  simp only [Fin.sum_univ_three]
  ring

/-- The kernel form is linear in the kernel (three terms). -/
theorem kernelForm_lin3 (ν : FiniteLaw X) (K L N : X → X → ℝ) (a b c : ℝ) (f g : X → ℝ) :
    kernelForm ν ν (fun x y => a * K x y + b * L x y + c * N x y) f g =
      a * kernelForm ν ν K f g + b * kernelForm ν ν L f g + c * kernelForm ν ν N f g := by
  simp only [kernelForm, LinearMap.mk₂_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

/-- The kernel form of a scalar multiple. -/
theorem kernelForm_smul (ν : FiniteLaw X) (K : X → X → ℝ) (a : ℝ) (f g : X → ℝ) :
    kernelForm ν ν (fun x y => a * K x y) f g = a * kernelForm ν ν K f g := by
  simp only [kernelForm, LinearMap.mk₂_apply, Finset.mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

/-- For centred `f`, `⟨f, φ⟩ = ⟨f, P₀φ⟩`. -/
theorem ip_center_right (ν : FiniteLaw X) {f : X → ℝ} (hf : ν.expect f = 0) (φ : X → ℝ) :
    Recentering.ip ν f (center ν φ) = Recentering.ip ν f φ := by
  unfold Recentering.ip center
  have : (fun x => f x * (φ x - ν.expect φ)) = fun x => f x * φ x - ν.expect φ * f x := by
    funext x; ring
  rw [this, ν.expect_sub, ν.expect_const_mul, hf]
  ring

/-! ## The tilt -/

/-- **The tilt** (proof of `prop:root-chamber`): on centred `f`,
`K₀∘w_u(f,f) = s r Re⟨𝓕^*f, M_λ𝓕^*f⟩ + s⟨f,𝔯_μ⟩² + 𝓡_u(f,f)`, `|𝓡_u(f,f)| ≤ ε_u‖f‖²`,
`s = 1 + u²`, `λ = 2u/s`, `ε_u = sε₀ + 2uε^raw_lin + u²ε^raw_sq`. -/
theorem tilt_centred_form (ν : FiniteLaw X) (K0 : X → X → ℝ) (η : Fin 3 → X → X → ℝ)
    (Fadj : (X → ℝ) → Idx → ℂ) (rμ : X → ℝ) {u r ε0 εlin εsq : ℝ} (hu : 0 ≤ u)
    (hbase : ∀ f, ν.expect f = 0 →
      |kernelForm ν ν K0 f f -
          (r * (bform (softM D20) (Fadj f) (Fadj f)).re + Recentering.ip ν f rμ ^ 2)| ≤
        ε0 * nrm ν f ^ 2)
    (hlin : ∀ f, ν.expect f = 0 →
      |kernelForm ν ν (fun x y => K0 x y * etaBar η x y) f f -
        r / 3 * (bform pairC (Fadj f) (Fadj f)).re| ≤ εlin * nrm ν f ^ 2)
    (hsq : ∀ f g, |kernelForm ν ν (fun x y => K0 x y * sqMean η x y - K0 x y) f g| ≤
      εsq * nrm ν f * nrm ν g)
    (f : X → ℝ) (hf : ν.expect f = 0) :
    |kernelForm ν ν (fun x y => K0 x y * (1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y)) f f -
        ((1 + u ^ 2) * r * (bform (Mlam (2 * u / (1 + u ^ 2))) (Fadj f) (Fadj f)).re +
          (1 + u ^ 2) * Recentering.ip ν f rμ ^ 2)| ≤
      ((1 + u ^ 2) * ε0 + 2 * u * εlin + u ^ 2 * εsq) * nrm ν f ^ 2 := by
  set s := 1 + u ^ 2 with hs
  have hs0 : 0 < s := by positivity
  -- the form of the tilted kernel
  have hK : kernelForm ν ν (fun x y => K0 x y * (1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y))
      f f = s * kernelForm ν ν K0 f f +
        2 * u * kernelForm ν ν (fun x y => K0 x y * etaBar η x y) f f +
        u ^ 2 * kernelForm ν ν (fun x y => K0 x y * sqMean η x y - K0 x y) f f := by
    have e : (fun x y => K0 x y * (1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y)) =
        fun x y => s * K0 x y + 2 * u * (K0 x y * etaBar η x y) +
          u ^ 2 * (K0 x y * sqMean η x y - K0 x y) := by
      funext x y
      ring
    rw [e, kernelForm_lin3]
  -- the form of `M_λ`
  have hM : (bform (Mlam (2 * u / s)) (Fadj f) (Fadj f)).re =
      (bform (softM D20) (Fadj f) (Fadj f)).re +
        2 * u / s / 3 * (bform pairC (Fadj f) (Fadj f)).re := by
    rw [bform_Mlam, Complex.add_re, Complex.re_ofReal_mul]
  rw [hK, hM]
  have e1 := hbase f hf
  have e2 := hlin f hf
  have e3 := hsq f f
  rw [mul_assoc, ← sq] at e3
  set A := kernelForm ν ν K0 f f
  set B := kernelForm ν ν (fun x y => K0 x y * etaBar η x y) f f
  set C := kernelForm ν ν (fun x y => K0 x y * sqMean η x y - K0 x y) f f
  set m := (bform (softM D20) (Fadj f) (Fadj f)).re
  set pc := (bform pairC (Fadj f) (Fadj f)).re
  have key : s * A + 2 * u * B + u ^ 2 * C -
      (s * r * (m + 2 * u / s / 3 * pc) + s * Recentering.ip ν f rμ ^ 2) =
      s * (A - (r * m + Recentering.ip ν f rμ ^ 2)) + 2 * u * (B - r / 3 * pc) + u ^ 2 * C := by
    field_simp
    ring
  rw [key]
  have t1 := abs_add_le (s * (A - (r * m + Recentering.ip ν f rμ ^ 2)) + 2 * u * (B - r / 3 * pc))
    (u ^ 2 * C)
  have t2 := abs_add_le (s * (A - (r * m + Recentering.ip ν f rμ ^ 2))) (2 * u * (B - r / 3 * pc))
  rw [abs_mul, abs_of_pos hs0] at t2
  rw [abs_mul (2 * u), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * u)] at t2
  rw [abs_mul, abs_of_nonneg (sq_nonneg u)] at t1
  have f1 := mul_le_mul_of_nonneg_left e1 hs0.le
  have f2 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 2 * u)
  have f3 := mul_le_mul_of_nonneg_left e3 (sq_nonneg u)
  nlinarith

/-- **The centred bounds of the tilted raw kernel**: with the frame cap `|𝓕^*f|² ≤ Γ₂₀‖f‖²`,
`‖P₀𝔯_μ‖² ≤ d²_𝔯/h'_p` (`dr2`), `M_λ ⪰ −gI` (`g ≥ g(λ)`) and `‖M_λ‖ ≤ √30 + λ/3`, on centred `f`:
`−(sgrΓ₂₀ + ε_u)‖f‖² ≤ K₀∘w_u(f,f)` and `|K₀∘w_u(f,f)| ≤ (s(√30 + λ/3)rΓ₂₀ + ε_u + s·dr2)‖f‖²`. -/
theorem tilt_centred_bounds (ν : FiniteLaw X) (K0 : X → X → ℝ) (η : Fin 3 → X → X → ℝ)
    (Fadj : (X → ℝ) → Idx → ℂ) (rμ : X → ℝ) {u r ε0 εlin εsq Γ g dr2 : ℝ} (hu : 0 ≤ u)
    (hr : 0 ≤ r)
    (hF : ∀ f, ∑ k, ‖Fadj f k‖ ^ 2 ≤ Γ * nrm ν f ^ 2)
    (hrμ : nrm ν (center ν rμ) ^ 2 ≤ dr2)
    (hg : gRoot (2 * u / (1 + u ^ 2)) ≤ g)
    (hbase : ∀ f, ν.expect f = 0 →
      |kernelForm ν ν K0 f f -
          (r * (bform (softM D20) (Fadj f) (Fadj f)).re + Recentering.ip ν f rμ ^ 2)| ≤
        ε0 * nrm ν f ^ 2)
    (hlin : ∀ f, ν.expect f = 0 →
      |kernelForm ν ν (fun x y => K0 x y * etaBar η x y) f f -
        r / 3 * (bform pairC (Fadj f) (Fadj f)).re| ≤ εlin * nrm ν f ^ 2)
    (hsq : ∀ f g, |kernelForm ν ν (fun x y => K0 x y * sqMean η x y - K0 x y) f g| ≤
      εsq * nrm ν f * nrm ν g)
    (f : X → ℝ) (hf : ν.expect f = 0) :
    -((1 + u ^ 2) * g * r * Γ + ((1 + u ^ 2) * ε0 + 2 * u * εlin + u ^ 2 * εsq)) * nrm ν f ^ 2 ≤
        kernelForm ν ν (fun x y => K0 x y * (1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y)) f f ∧
      |kernelForm ν ν (fun x y => K0 x y * (1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y)) f f| ≤
        ((1 + u ^ 2) * (Real.sqrt 30 + 2 * u / (1 + u ^ 2) / 3) * r * Γ +
          ((1 + u ^ 2) * ε0 + 2 * u * εlin + u ^ 2 * εsq) + (1 + u ^ 2) * dr2) * nrm ν f ^ 2 := by
  have hD := tilt_centred_form ν K0 η Fadj rμ hu hbase hlin hsq f hf
  set lam := 2 * u / (1 + u ^ 2) with hlam
  set s := 1 + u ^ 2 with hs
  have hs0 : 0 < s := by positivity
  set N := ∑ k, ‖Fadj f k‖ ^ 2 with hN
  have hN0 : 0 ≤ N := sum_nonneg fun k _ => sq_nonneg _
  have hNf := hF f
  have hlam0 : 0 ≤ lam := strength_nonneg hu
  -- the matrix: lower bound and norm
  have hlow := Mlam_lower_of_le hlam0 (strength_sq_le hu) hg (Fadj f)
  have hnorm : |(bform (Mlam lam) (Fadj f) (Fadj f)).re| ≤ (Real.sqrt 30 + lam / 3) * N := by
    have h1 := normLe_Mlam hlam0 (Fadj f) (Fadj f)
    have h2 := Complex.abs_re_le_norm (bform (Mlam lam) (Fadj f) (Fadj f))
    have hv : vnorm (Fadj f) * vnorm (Fadj f) = N := by
      unfold vnorm
      rw [Real.mul_self_sqrt hN0]
    calc _ ≤ _ := h2
      _ ≤ _ := h1
      _ = (Real.sqrt 30 + lam / 3) * (vnorm (Fadj f) * vnorm (Fadj f)) := by ring
      _ = _ := by rw [hv]
  -- the rank term
  have hρ0 : 0 ≤ Recentering.ip ν f rμ ^ 2 := sq_nonneg _
  have hρ : Recentering.ip ν f rμ ^ 2 ≤ dr2 * nrm ν f ^ 2 := by
    rw [← ip_center_right ν hf]
    have h1 := abs_ip_le ν f (center ν rμ)
    have h2 : Recentering.ip ν f (center ν rμ) ^ 2 ≤ (nrm ν f * nrm ν (center ν rμ)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : (nrm ν f * nrm ν (center ν rμ)) ^ 2 ≤ nrm ν f ^ 2 * dr2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hrμ (sq_nonneg _)
    linarith
  have hgN : -g * N ≥ -g * (Γ * nrm ν f ^ 2) := by
    have hg0 : 0 ≤ g := (gRoot_pos hlam0).le.trans hg
    nlinarith
  have hsr : 0 ≤ s * r := mul_nonneg hs0.le hr
  set εu := s * ε0 + 2 * u * εlin + u ^ 2 * εsq
  set Kf := kernelForm ν ν
    (fun x y => K0 x y * (1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y)) f f
  set mf := (bform (Mlam lam) (Fadj f) (Fadj f)).re
  have hab := abs_le.mp hD
  constructor
  · -- lower
    have h1 : s * r * mf ≥ s * r * (-g * (Γ * nrm ν f ^ 2)) :=
      mul_le_mul_of_nonneg_left (le_trans hgN.le hlow) hsr
    have h2 : 0 ≤ s * Recentering.ip ν f rμ ^ 2 := mul_nonneg hs0.le hρ0
    nlinarith
  · -- absolute value
    have h1 : |s * r * mf| ≤ s * r * ((Real.sqrt 30 + lam / 3) * (Γ * nrm ν f ^ 2)) := by
      rw [abs_mul, abs_of_nonneg hsr]
      refine mul_le_mul_of_nonneg_left (hnorm.trans ?_) hsr
      have : 0 ≤ Real.sqrt 30 + lam / 3 := by positivity
      exact mul_le_mul_of_nonneg_left hNf this
    have h2 : s * Recentering.ip ν f rμ ^ 2 ≤ s * (dr2 * nrm ν f ^ 2) :=
      mul_le_mul_of_nonneg_left hρ hs0.le
    have h3 : 0 ≤ s * Recentering.ip ν f rμ ^ 2 := mul_nonneg hs0.le hρ0
    have h1' := abs_le.mp h1
    rw [abs_le]
    constructor <;> nlinarith

/-! ## The caps at a prime -/

/-- The mass of a scalar multiple of a kernel. -/
theorem kmass_smul (ν : FiniteLaw X) (K : X → X → ℝ) (a : ℝ) :
    kmass ν (fun x y => a * K x y) = a * kmass ν K := by
  rw [kmass_eq_kernelForm, kmass_eq_kernelForm, kernelForm_smul]

/-! ### The constants of `prop:root-chamber` -/

/-- `ε_u = sε₀ + 2uε^raw_lin + u²ε^raw_sq`, `s = 1 + u²`. -/
def epsU (u ε0 εlin εsq : ℝ) : ℝ := (1 + u ^ 2) * ε0 + 2 * u * εlin + u ^ 2 * εsq

/-- `z₋ = s − 2uh₀ − u²ε_sq`. -/
def zMinus (u h0 esq : ℝ) : ℝ := 1 + u ^ 2 - 2 * u * h0 - u ^ 2 * esq

/-- `g_ch = (s g r Γ₂₀ + ε_u)/z_raw`. -/
noncomputable def gCh (u g r Γ eu zraw : ℝ) : ℝ := ((1 + u ^ 2) * g * r * Γ + eu) / zraw

/-- `c_ch = (s(√30 + λ/3) r Γ₂₀ + ε_u + s d²_𝔯/h'_p)/z_raw`, `λ = 2u/s`. -/
noncomputable def cCh (u r Γ eu dr2 zraw : ℝ) : ℝ :=
  ((1 + u ^ 2) * (Real.sqrt 30 + 2 * u / (1 + u ^ 2) / 3) * r * Γ + eu + (1 + u ^ 2) * dr2) / zraw

/-- `d_u = (s√χ⁺_p + 2u𝔩 + u²ε_sq)/z₋` (with `δ = √χ⁺_p`). -/
noncomputable def dU (u δ l esq zm : ℝ) : ℝ := ((1 + u ^ 2) * δ + 2 * u * l + u ^ 2 * esq) / zm

/-- **`prop:root-chamber`, the caps at a prime.** Let `K₀ ≥ 0` be symmetric with
`Z₀ = ⟨1, K₀1⟩ ≥ 1 − ε_Z > 0`, `T₀ = K₀/Z₀`, and let the scores `η_j` be permuted by the
transposition. Under the hypotheses listed in the module docstring (each the bound of the paper
named there), the tilted cut operator `T_u = Cuts.tiltKernel ν T₀ η V u`
(`= (K₀∘w_u)/⟨1,(K₀∘w_u)1⟩`, `V = sqMean η`) satisfies, if `z₋ > 0`, `u c_cond < 1` and
`c_ch < 1` (with `ε_sq = ε^raw_sq/(1 − ε_Z)`, `z_raw = (1 − ε_Z)z₋`):
* `−(g_ch + d_u²/(1 + g_ch))‖f‖² ≤ ⟨f, T_u f⟩ ≤ (1 + d_u²/(1 − c_ch))‖f‖²` for all `f`;
* `‖T_u1 − 1‖ ≤ d_u`;
* `T_u1(x) ≤ R(1 + ub)²/(1 − uc_cond)² T_u1(x')` (the range ratio; `b = 2 + r` in the paper);
* `P₀T_uP₀ ⪰ −g_ch` and `‖P₀T_uP₀‖ ≤ c_ch` (the intermediate claims of the proof). -/
theorem root_chamber (ν : FiniteLaw X) (K0 : X → X → ℝ) (hK0 : ∀ x y, 0 ≤ K0 x y)
    (hK0s : ∀ x y, K0 y x = K0 x y) (η : Fin 3 → X → X → ℝ) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ j x y, η j y x = η (σ j) x y) (Fadj : (X → ℝ) → Idx → ℂ) (rμ : X → ℝ)
    {u r εZ ε0 εlin εsq Γ g dr2 δ l h0 cc b R : ℝ} (hu : 0 ≤ u) (hr : 0 ≤ r) (hΓ : 0 ≤ Γ)
    (hε0 : 0 ≤ ε0) (hεlin : 0 ≤ εlin) (hεsq : 0 ≤ εsq) (hdr2 : 0 ≤ dr2)
    (hεZ : εZ < 1) (hZ : 1 - εZ ≤ kmass ν K0)
    (hF : ∀ f, ∑ k, ‖Fadj f k‖ ^ 2 ≤ Γ * nrm ν f ^ 2)
    (hrμ : nrm ν (center ν rμ) ^ 2 ≤ dr2)
    (hg : gRoot (2 * u / (1 + u ^ 2)) ≤ g)
    (hbase : ∀ f, ν.expect f = 0 →
      |kernelForm ν ν K0 f f -
          (r * (bform (softM D20) (Fadj f) (Fadj f)).re + Recentering.ip ν f rμ ^ 2)| ≤
        ε0 * nrm ν f ^ 2)
    (hlin : ∀ f, ν.expect f = 0 →
      |kernelForm ν ν (fun x y => K0 x y * etaBar η x y) f f -
        r / 3 * (bform pairC (Fadj f) (Fadj f)).re| ≤ εlin * nrm ν f ^ 2)
    (hsq : ∀ f g, |kernelForm ν ν (fun x y => K0 x y * sqMean η x y - K0 x y) f g| ≤
      εsq * nrm ν f * nrm ν g)
    (hδ : nrm ν (fun x => rowFun ν (fun x y => K0 x y / kmass ν K0) x - 1) ≤ δ)
    (hR : ∀ x x', rowFun ν (fun x y => K0 x y / kmass ν K0) x ≤
      R * rowFun ν (fun x y => K0 x y / kmass ν K0) x')
    (hl : nrm ν (center ν (rowFun ν (fun x y => K0 x y / kmass ν K0 * etaBar η x y))) ≤ l)
    (hh : |kmass ν (fun x y => K0 x y / kmass ν K0 * etaBar η x y)| ≤ h0)
    (hc : ∀ x, |rowFun ν (fun x y => K0 x y / kmass ν K0 * etaBar η x y) x| ≤
      cc * rowFun ν (fun x y => K0 x y / kmass ν K0) x)
    (hb : ∀ j x y, 0 < K0 x y → |η j x y| ≤ b)
    (huc : u * cc < 1)
    (hz : 0 < zMinus u h0 (εsq / (1 - εZ)))
    (hcch : cCh u r Γ (epsU u ε0 εlin εsq) dr2 ((1 - εZ) * zMinus u h0 (εsq / (1 - εZ))) < 1) :
    (∀ f, -(gCh u g r Γ (epsU u ε0 εlin εsq) ((1 - εZ) * zMinus u h0 (εsq / (1 - εZ))) +
          dU u δ l (εsq / (1 - εZ)) (zMinus u h0 (εsq / (1 - εZ))) ^ 2 /
            (1 + gCh u g r Γ (epsU u ε0 εlin εsq) ((1 - εZ) * zMinus u h0 (εsq / (1 - εZ))))) *
          nrm ν f ^ 2 ≤
        kernelForm ν ν (tiltKernel ν (fun x y => K0 x y / kmass ν K0) η (sqMean η) u) f f) ∧
    (∀ f, kernelForm ν ν (tiltKernel ν (fun x y => K0 x y / kmass ν K0) η (sqMean η) u) f f ≤
        (1 + dU u δ l (εsq / (1 - εZ)) (zMinus u h0 (εsq / (1 - εZ))) ^ 2 /
          (1 - cCh u r Γ (epsU u ε0 εlin εsq) dr2 ((1 - εZ) * zMinus u h0 (εsq / (1 - εZ))))) *
          nrm ν f ^ 2) ∧
    nrm ν (fun x => rowFun ν (tiltKernel ν (fun x y => K0 x y / kmass ν K0) η (sqMean η) u) x - 1)
      ≤ dU u δ l (εsq / (1 - εZ)) (zMinus u h0 (εsq / (1 - εZ))) ∧
    (∀ x x', rowFun ν (tiltKernel ν (fun x y => K0 x y / kmass ν K0) η (sqMean η) u) x ≤
      R * ((1 + u * b) ^ 2 / (1 - u * cc) ^ 2) *
        rowFun ν (tiltKernel ν (fun x y => K0 x y / kmass ν K0) η (sqMean η) u) x') ∧
    (∀ f, ν.expect f = 0 →
      -gCh u g r Γ (epsU u ε0 εlin εsq) ((1 - εZ) * zMinus u h0 (εsq / (1 - εZ))) * nrm ν f ^ 2 ≤
        kernelForm ν ν (tiltKernel ν (fun x y => K0 x y / kmass ν K0) η (sqMean η) u) f f ∧
      |kernelForm ν ν (tiltKernel ν (fun x y => K0 x y / kmass ν K0) η (sqMean η) u) f f| ≤
        cCh u r Γ (epsU u ε0 εlin εsq) dr2 ((1 - εZ) * zMinus u h0 (εsq / (1 - εZ))) *
          nrm ν f ^ 2) := by
  set Z0 := kmass ν K0 with hZ0
  have hZpos : 0 < Z0 := lt_of_lt_of_le (by linarith) hZ
  have h1εZ : 0 < 1 - εZ := by linarith
  set T0 : X → X → ℝ := fun x y => K0 x y / Z0 with hT0
  set T := tiltKernel ν T0 η (sqMean η) u with hTdef
  set esq := εsq / (1 - εZ) with hesq
  set zm := zMinus u h0 esq with hzmdef
  set zraw := (1 - εZ) * zm with hzrawdef
  set εu := epsU u ε0 εlin εsq with hεudef
  set gch := gCh u g r Γ εu zraw with hgchdef
  set cch := cCh u r Γ εu dr2 zraw with hcchdef
  set du := dU u δ l esq zm with hdudef
  -- `T₀` has mass one
  have hT0m : kmass ν T0 = 1 := by
    have : T0 = fun x y => Z0⁻¹ * K0 x y := by funext x y; rw [hT0]; ring
    rw [this, kmass_smul, ← hZ0, inv_mul_cancel₀ hZpos.ne']
  have hT00 : ∀ x y, 0 ≤ T0 x y := fun x y => div_nonneg (hK0 x y) hZpos.le
  have hT0s : ∀ x y, T0 y x = T0 x y := fun x y => by rw [hT0]; simp only [hK0s]
  -- the square price for `T₀`
  have he : ∀ f g, |kernelForm ν ν (fun x y => T0 x y * sqMean η x y - 1 * T0 x y) f g| ≤
      esq * nrm ν f * nrm ν g := by
    intro f g
    have e : (fun x y => T0 x y * sqMean η x y - 1 * T0 x y) =
        fun x y => Z0⁻¹ * (K0 x y * sqMean η x y - K0 x y) := by
      funext x y; rw [hT0]; field_simp
    rw [e, kernelForm_smul, abs_mul, abs_of_pos (inv_pos.mpr hZpos)]
    have h1 := hsq f g
    have hn : 0 ≤ nrm ν f * nrm ν g := mul_nonneg (nrm_nonneg ν f) (nrm_nonneg ν g)
    have h2 : Z0⁻¹ ≤ (1 - εZ)⁻¹ := inv_anti₀ h1εZ hZ
    calc Z0⁻¹ * |kernelForm ν ν (fun x y => K0 x y * sqMean η x y - K0 x y) f g|
        ≤ Z0⁻¹ * (εsq * nrm ν f * nrm ν g) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hZpos.le)
      _ ≤ (1 - εZ)⁻¹ * (εsq * nrm ν f * nrm ν g) :=
          mul_le_mul_of_nonneg_right h2 (by rw [mul_assoc]; exact mul_nonneg hεsq hn)
      _ = esq * nrm ν f * nrm ν g := by rw [hesq]; ring
  have hbT : ∀ j x y, 0 < T0 x y → |η j x y| ≤ b := by
    intro j x y hxy
    refine hb j x y ?_
    rw [hT0] at hxy
    exact (div_pos_iff_of_pos_right hZpos).mp hxy
  have hV : IsTiltV η (sqMean η) := Or.inl rfl
  have hesq0 : 0 ≤ esq := div_nonneg hεsq h1εZ.le
  have hz' : 0 < 1 + 1 * u ^ 2 - 2 * u * h0 - u ^ 2 * esq := by
    have : zm = 1 + 1 * u ^ 2 - 2 * u * h0 - u ^ 2 * esq := by rw [hzmdef, zMinus]; ring
    rw [← this]; exact hz
  -- `lem:tilt-marginals`
  obtain ⟨hTn, hTs, hTm, hZz, hTd, hTr⟩ := tilt_marginals ν T0 hT00 hT0s hT0m hR hδ η σ hσ
    (sqMean η) hV (cV := 1) (e := esq) (by norm_num) hesq0 he hl hh hc hbT hu huc hz'
  have hzmeq : 1 + 1 * u ^ 2 - 2 * u * h0 - u ^ 2 * esq = zm := by rw [hzmdef, zMinus]; ring
  rw [hzmeq] at hZz hTd
  have hTd' : nrm ν (fun x => rowFun ν T x - 1) ≤ du := by
    have e : du = ((1 + 1 * u ^ 2) * δ + 2 * u * l + u ^ 2 * esq) / zm := by
      rw [hdudef, dU]; ring
    rw [e]; exact hTd
  -- the raw mass
  set Mt := kmass ν (tiltNum T0 η (sqMean η) u) with hMt
  have hzm : 0 < zm := hz
  have hMtpos : 0 < Mt := lt_of_lt_of_le hzm hZz
  have hzraw : 0 < zraw := mul_pos h1εZ hzm
  have hDz : zraw ≤ Z0 * Mt := mul_le_mul hZ hZz hzm.le hZpos.le
  have hDpos : 0 < Z0 * Mt := mul_pos hZpos hMtpos
  -- the form of `T` is the raw form divided by `Z₀ M_t`
  have hTform : ∀ f g, kernelForm ν ν T f g =
      (Z0 * Mt)⁻¹ * kernelForm ν ν
        (fun x y => K0 x y * (1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y)) f g := by
    intro f g
    have e : T = fun x y => (Z0 * Mt)⁻¹ *
        (K0 x y * (1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y)) := by
      funext x y
      change tiltNum T0 η (sqMean η) u x y / Mt = _
      rw [tiltNum_eq, hT0]
      field_simp
    rw [e, kernelForm_smul]
  have hg0 : 0 ≤ g := (gRoot_pos (strength_nonneg hu)).le.trans hg
  have hεu0 : 0 ≤ εu := by rw [hεudef, epsU]; positivity
  have hA0 : 0 ≤ (1 + u ^ 2) * g * r * Γ + εu := by positivity
  have hgch0 : 0 ≤ gch := div_nonneg hA0 hzraw.le
  have hB0 : 0 ≤ (1 + u ^ 2) * (Real.sqrt 30 + 2 * u / (1 + u ^ 2) / 3) * r * Γ + εu +
      (1 + u ^ 2) * dr2 := by positivity
  -- centred bounds for `T`
  have hcent : ∀ f, ν.expect f = 0 → -gch * nrm ν f ^ 2 ≤ kernelForm ν ν T f f ∧
      |kernelForm ν ν T f f| ≤ cch * nrm ν f ^ 2 := by
    intro f hf
    obtain ⟨hlo, hab⟩ := tilt_centred_bounds ν K0 η Fadj rμ hu hr hF hrμ hg hbase hlin hsq f hf
    rw [hTform]
    have hinv0 : 0 ≤ (Z0 * Mt)⁻¹ := inv_nonneg.mpr hDpos.le
    have hinv : (Z0 * Mt)⁻¹ ≤ zraw⁻¹ := inv_anti₀ hzraw hDz
    have hn0 := sq_nonneg (nrm ν f)
    set Kf := kernelForm ν ν
      (fun x y => K0 x y * (1 + 2 * u * etaBar η x y + u ^ 2 * sqMean η x y)) f f
    constructor
    · have h1 := mul_le_mul_of_nonneg_left hlo hinv0
      have h2 : (Z0 * Mt)⁻¹ * (((1 + u ^ 2) * g * r * Γ + εu) * nrm ν f ^ 2) ≤
          zraw⁻¹ * (((1 + u ^ 2) * g * r * Γ + εu) * nrm ν f ^ 2) :=
        mul_le_mul_of_nonneg_right hinv (mul_nonneg hA0 hn0)
      have e : gch * nrm ν f ^ 2 = zraw⁻¹ * (((1 + u ^ 2) * g * r * Γ + εu) * nrm ν f ^ 2) := by
        rw [hgchdef, gCh]; ring
      have e2 : (Z0 * Mt)⁻¹ * (-((1 + u ^ 2) * g * r * Γ + epsU u ε0 εlin εsq) * nrm ν f ^ 2) =
          -((Z0 * Mt)⁻¹ * (((1 + u ^ 2) * g * r * Γ + εu) * nrm ν f ^ 2)) := by
        rw [hεudef]; ring
      rw [epsU] at e2
      linarith
    · rw [abs_mul, abs_of_nonneg hinv0]
      have h1 := mul_le_mul_of_nonneg_left hab hinv0
      have h2 := mul_le_mul_of_nonneg_right hinv (mul_nonneg hB0 hn0)
      have e : cch * nrm ν f ^ 2 = zraw⁻¹ * (((1 + u ^ 2) *
          (Real.sqrt 30 + 2 * u / (1 + u ^ 2) / 3) * r * Γ + εu + (1 + u ^ 2) * dr2) *
            nrm ν f ^ 2) := by
        rw [hcchdef, cCh]; ring
      rw [hεudef, epsU] at e h2
      rw [e]
      linarith
  -- the form of `T`
  have hsym : ∀ f g, kernelForm ν ν T f g = kernelForm ν ν T g f :=
    fun f g => kernelForm_symm ν T hTs f g
  have h11 : kernelForm ν ν T (fun _ => 1) (fun _ => 1) = 1 := by
    rw [← kmass_eq_kernelForm]; exact hTm
  have hrow : ∀ f, ν.expect f = 0 → |kernelForm ν ν T f (fun _ => 1)| ≤ du * nrm ν f := by
    intro f hf
    rw [kernelForm_one_right]
    have e : Recentering.ip ν f (fun x => ν.expect (fun y => T x y)) =
        Recentering.ip ν f (fun x => rowFun ν T x - 1) := by
      unfold Recentering.ip rowFun
      have : (fun x => f x * (ν.expect (fun y => T x y) - 1)) =
          fun x => f x * ν.expect (fun y => T x y) - f x := by funext x; ring
      rw [this, ν.expect_sub, hf, sub_zero]
    rw [e]
    calc _ ≤ nrm ν f * nrm ν (fun x => rowFun ν T x - 1) := abs_ip_le ν f _
      _ ≤ nrm ν f * du := mul_le_mul_of_nonneg_left hTd' (nrm_nonneg ν f)
      _ = du * nrm ν f := by ring
  refine ⟨fun f => ?_, fun f => ?_, hTd', hTr, hcent⟩
  · exact envelope_lower ν (kernelForm ν ν T) hsym h11 hgch0 hrow (fun f hf => (hcent f hf).1) f
  · exact envelope_upper ν (kernelForm ν ν T) hsym h11 hcch hrow
      (fun f hf => le_trans (le_abs_self _) (hcent f hf).2) f

/-! ## The endpoint normalization and the uniformity -/

/-- **The endpoint normalization** (`prop:root-chamber`): with `g^u_{20} = (g_ch + d²/(1 + g_ch))/r`
and `c^{+,u}_{20} = d²/(q(1 − c_ch))`, the caps of `root_chamber` read
`−g^u_{20} r ⪯ T_u ⪯ 1 + c^{+,u}_{20} q`. -/
theorem root_chamber_endpoint {G D C r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hC : C < 1) :
    -((G + D ^ 2 / (1 + G)) / r) * r = -(G + D ^ 2 / (1 + G)) ∧
      1 + D ^ 2 / (q * (1 - C)) * q = 1 + D ^ 2 / (1 - C) := by
  have h1 : 1 - C ≠ 0 := by linarith
  constructor
  · field_simp
  · field_simp

/-- **The uniformity of the negative coefficient** (`prop:root-chamber`, "Uniformity";
`lem:majorant`(ii)): `G + D²r/(1 + Gr)` is nondecreasing in `G`, `D` and `r` on `D'r' < 1`; so once
`G = g_ch/r` and `D = d_u/r` are majorized at the endpoint, the negative coefficient is. -/
theorem negCoef_mono {G G' D D' r r' : ℝ} (hG : 0 ≤ G) (hGG : G ≤ G') (hD : 0 ≤ D) (hDD : D ≤ D')
    (hr : 0 ≤ r) (hrr : r ≤ r') (hgate : D' * r' < 1) :
    G + D ^ 2 * r / (1 + G * r) ≤ G' + D' ^ 2 * r' / (1 + G' * r') := by
  have hG' : 0 ≤ G' := hG.trans hGG
  have hr' : 0 ≤ r' := hr.trans hrr
  have ha : 1 ≤ 1 + G * r := by nlinarith [mul_nonneg hG hr]
  have hb : 1 ≤ 1 + G' * r := by nlinarith [mul_nonneg hG' hr]
  have hc : 1 ≤ 1 + G' * r' := by nlinarith [mul_nonneg hG' hr']
  have hDr : D * r ≤ D' * r' := mul_le_mul hDD hrr hr (hD.trans hDD)
  have hDr1 : (D * r) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ D * r := mul_nonneg hD hr
    nlinarith
  -- step 1: in `G`
  have s1 : G + D ^ 2 * r / (1 + G * r) ≤ G' + D ^ 2 * r / (1 + G' * r) := by
    have e : D ^ 2 * r / (1 + G * r) - D ^ 2 * r / (1 + G' * r) =
        (G' - G) * ((D * r) ^ 2 / ((1 + G * r) * (1 + G' * r))) := by
      field_simp
      ring
    have hfrac : (D * r) ^ 2 / ((1 + G * r) * (1 + G' * r)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    have : (G' - G) * ((D * r) ^ 2 / ((1 + G * r) * (1 + G' * r))) ≤ G' - G := by
      have := mul_le_mul_of_nonneg_left hfrac (sub_nonneg.mpr hGG)
      linarith
    linarith
  -- step 2: in `D`
  have s2 : D ^ 2 * r / (1 + G' * r) ≤ D' ^ 2 * r / (1 + G' * r) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD hDD 2) hr
  -- step 3: in `r`
  have s3 : D' ^ 2 * r / (1 + G' * r) ≤ D' ^ 2 * r' / (1 + G' * r') := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have : r * (1 + G' * r') ≤ r' * (1 + G' * r) := by nlinarith
    have hD2 : 0 ≤ D' ^ 2 := sq_nonneg D'
    nlinarith
  linarith

/-- **The uniformity of the positive coefficient**: `D²/(1 − C)` is nondecreasing in `D ≥ 0` and in
`C < 1`. -/
theorem posCoef_mono {D D' C C' : ℝ} (hD : 0 ≤ D) (hDD : D ≤ D') (hCC : C ≤ C') (hC' : C' < 1) :
    D ^ 2 / (1 - C) ≤ D' ^ 2 / (1 - C') := by
  have h1 : 0 < 1 - C' := by linarith
  calc D ^ 2 / (1 - C) ≤ D' ^ 2 / (1 - C) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hD hDD 2) (by linarith)
    _ ≤ D' ^ 2 / (1 - C') := div_le_div_of_nonneg_left (sq_nonneg _) h1 (by linarith)

end Sarkozy.PositiveRoots
