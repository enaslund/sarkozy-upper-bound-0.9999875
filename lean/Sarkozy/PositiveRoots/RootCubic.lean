module

public import Sarkozy.PositiveRoots.PairMatrix
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# The leading coefficient `g(λ)` of a tilt (`eq:root-cubic`, `lem:root-pair-matrix`)

`paper/sections/20b_positive_roots.tex`, `lem:root-pair-matrix`, step (5) of the proof, and
`rem:positive-root-family`. For `λ ≥ 0` let `f_λ(g) = 3g³ + λg² − 90g − 26λ` (`rootCubic`).

* `rootCubic_neg`: `f_λ(g) < 0` for `0 < g ≤ √26` (strictly below `√26` or `λ > 0`; at
  `g = √26` the value is `−12√26`);
* `rootCubic_strictMonoOn`: `f_λ` is strictly increasing on `[√26, ∞)`;
* `exists_root`, `gRoot`, `gRoot_spec`: the root `g(λ)` exists, by the intermediate value
  theorem on `[√26, √30]` (`f_λ(√26) = −12√26 < 0 ≤ 4λ = f_λ(√30)`), and
  `g(λ) ∈ (√26, √30]`;
* `gRoot_unique`: it is the only positive root;
* `cubic_nonneg_iff`: for `g > 0`, `f_λ(g) ≥ 0 ⟺ g ≥ g(λ)` (the form in which a rational upper
  bound for `g(λ)` is certified);
* `gRoot_zero`: `g(0) = √30`; `gRoot_antitone`, `gRoot_strictAnti`: `g` decreases in `λ`;
* `Mlam_lower_gRoot`, `Mlam_least`: **the least eigenvalue of `M_λ` is `−g(λ)`** for
  `0 ≤ λ ≤ 3√26`: `M_λ ⪰ −g(λ)I`, attained;
* `strength_le_one`: the strength `λ = 2u/(1 + u²)` of a tilt is at most `1`, so the lemma applies
  (`prop:root-chamber`: "applicable since `λ ≤ 1`");
* **rational enclosures** (`gRoot_selected`): `g(λ_u)` at the six selected individual-square
  parameters `u = 711/4096, 1021/4096, 1455/4096, 833/1024, 3851/4096, 4049/4096` of
  `def:positive-root` lies in an explicit rational interval of width `10⁻⁹`, and the values
  `5.466411, 5.456962, 5.456161` (individual squares, `λ = 1/2, 24/25, 1`) and `5.443543`
  (square of the average, `λ = 4080/2467`) of `rem:positive-root-family` are correct to the
  stated digits (`gRoot_family`). These are exact rational sign checks of `f_λ`.
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy.SpectralC Sarkozy.L20Cap

/-- **The cubic of `eq:root-cubic`**: `f_λ(g) = 3g³ + λg² − 90g − 26λ`. -/
def rootCubic (lam g : ℝ) : ℝ := 3 * g ^ 3 + lam * g ^ 2 - 90 * g - 26 * lam

theorem sqrt26_sq : Real.sqrt 26 ^ 2 = 26 := Real.sq_sqrt (by norm_num)

theorem sqrt30_sq : Real.sqrt 30 ^ 2 = 30 := Real.sq_sqrt (by norm_num)

theorem sqrt26_pos : 0 < Real.sqrt 26 := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt26_lt_sqrt30 : Real.sqrt 26 < Real.sqrt 30 :=
  Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `f_λ(√26) = −12√26`. -/
theorem rootCubic_sqrt26 (lam : ℝ) : rootCubic lam (Real.sqrt 26) = -12 * Real.sqrt 26 := by
  unfold rootCubic
  have h3 : Real.sqrt 26 ^ 3 = 26 * Real.sqrt 26 := by
    rw [pow_succ, sqrt26_sq]
  rw [h3, sqrt26_sq]
  ring

/-- `f_λ(√30) = 4λ`. -/
theorem rootCubic_sqrt30 (lam : ℝ) : rootCubic lam (Real.sqrt 30) = 4 * lam := by
  unfold rootCubic
  have h3 : Real.sqrt 30 ^ 3 = 30 * Real.sqrt 30 := by
    rw [pow_succ, sqrt30_sq]
  rw [h3, sqrt30_sq]
  ring

/-- A positive `g` with `f_λ(g) ≥ 0` has `g ≥ √26`. -/
theorem sqrt26_le_of_nonneg {lam g : ℝ} (hlam : 0 ≤ lam) (hg : 0 < g)
    (hf : 0 ≤ rootCubic lam g) : Real.sqrt 26 ≤ g := by
  have h := sq_ge_26 hlam hg hf
  rw [← Real.sqrt_sq hg.le]
  exact Real.sqrt_le_sqrt h

/-- **`f_λ` is strictly increasing on `[√26, ∞)`**:
`f(g₂) − f(g₁) = (g₂ − g₁)(3(g₂² + g₁g₂ + g₁²) + λ(g₁ + g₂) − 90)` and `9 · 26 > 90`. -/
theorem rootCubic_strictMonoOn {lam : ℝ} (hlam : 0 ≤ lam) :
    StrictMonoOn (rootCubic lam) (Set.Ici (Real.sqrt 26)) := by
  intro g₁ h₁ g₂ h₂ h12
  simp only [Set.mem_Ici] at h₁ h₂
  have s1 : 26 ≤ g₁ ^ 2 := by
    have := pow_le_pow_left₀ sqrt26_pos.le h₁ 2
    rwa [sqrt26_sq] at this
  have s2 : 26 ≤ g₂ ^ 2 := by
    have := pow_le_pow_left₀ sqrt26_pos.le h₂ 2
    rwa [sqrt26_sq] at this
  have hp1 : 0 < g₁ := lt_of_lt_of_le sqrt26_pos h₁
  have hp2 : 0 < g₂ := lt_of_lt_of_le sqrt26_pos h₂
  have key : rootCubic lam g₂ - rootCubic lam g₁ =
      (g₂ - g₁) * (3 * (g₂ ^ 2 + g₁ * g₂ + g₁ ^ 2) + lam * (g₁ + g₂) - 90) := by
    unfold rootCubic; ring
  have hfac : 0 < 3 * (g₂ ^ 2 + g₁ * g₂ + g₁ ^ 2) + lam * (g₁ + g₂) - 90 := by
    have : 0 ≤ lam * (g₁ + g₂) := mul_nonneg hlam (by linarith)
    nlinarith [mul_pos hp1 hp2]
  have : 0 < rootCubic lam g₂ - rootCubic lam g₁ := by
    rw [key]; exact mul_pos (by linarith) hfac
  linarith

theorem rootCubic_continuous (lam : ℝ) : Continuous (rootCubic lam) := by
  unfold rootCubic
  fun_prop

/-- **The root exists in `(√26, √30]`** (intermediate value theorem). -/
theorem exists_root {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ g, Real.sqrt 26 < g ∧ g ≤ Real.sqrt 30 ∧ rootCubic lam g = 0 := by
  have hab : Real.sqrt 26 ≤ Real.sqrt 30 := sqrt26_lt_sqrt30.le
  have h0 : (0 : ℝ) ∈ Set.Icc (rootCubic lam (Real.sqrt 26)) (rootCubic lam (Real.sqrt 30)) := by
    rw [rootCubic_sqrt26, rootCubic_sqrt30]
    constructor
    · nlinarith [sqrt26_pos]
    · linarith
  obtain ⟨g, ⟨hg1, hg2⟩, hgf⟩ :=
    intermediate_value_Icc hab (rootCubic_continuous lam).continuousOn h0
  refine ⟨g, lt_of_le_of_ne hg1 ?_, hg2, hgf⟩
  intro h
  rw [← h, rootCubic_sqrt26] at hgf
  nlinarith [sqrt26_pos]

/-- **The leading coefficient `g(λ)`** of a tilt: the positive root of `eq:root-cubic`
(defined as `0` for `λ < 0`, where it is not used). -/
noncomputable def gRoot (lam : ℝ) : ℝ :=
  if h : 0 ≤ lam then Classical.choose (exists_root h) else 0

theorem gRoot_spec {lam : ℝ} (hlam : 0 ≤ lam) :
    Real.sqrt 26 < gRoot lam ∧ gRoot lam ≤ Real.sqrt 30 ∧ rootCubic lam (gRoot lam) = 0 := by
  unfold gRoot
  simp only [hlam, ↓reduceDIte]
  exact Classical.choose_spec (exists_root hlam)

theorem gRoot_pos {lam : ℝ} (hlam : 0 ≤ lam) : 0 < gRoot lam :=
  lt_trans sqrt26_pos (gRoot_spec hlam).1

/-- **`g(λ)` is the only positive root** of `eq:root-cubic`. -/
theorem gRoot_unique {lam g : ℝ} (hlam : 0 ≤ lam) (hg : 0 < g) (h : rootCubic lam g = 0) :
    g = gRoot lam := by
  have h1 : Real.sqrt 26 ≤ g := sqrt26_le_of_nonneg hlam hg h.symm.le
  have h2 : Real.sqrt 26 ≤ gRoot lam := (gRoot_spec hlam).1.le
  exact (rootCubic_strictMonoOn hlam).injOn h1 h2 (h.trans (gRoot_spec hlam).2.2.symm)

/-- **For `g > 0`: `f_λ(g) ≥ 0 ⟺ g ≥ g(λ)`.** A rational `g` with `f_λ(g) ≥ 0` is a certified
upper bound for `g(λ)`. -/
theorem cubic_nonneg_iff {lam g : ℝ} (hlam : 0 ≤ lam) (hg : 0 < g) :
    0 ≤ rootCubic lam g ↔ gRoot lam ≤ g := by
  have hm := rootCubic_strictMonoOn hlam
  have h2 : Real.sqrt 26 ≤ gRoot lam := (gRoot_spec hlam).1.le
  have h0 := (gRoot_spec hlam).2.2
  constructor
  · intro hf
    have h1 := sqrt26_le_of_nonneg hlam hg hf
    by_contra hlt
    push Not at hlt
    have := hm h1 h2 hlt
    linarith
  · intro hle
    have h1 : Real.sqrt 26 ≤ g := h2.trans hle
    rcases hle.lt_or_eq with hlt | heq
    · have := hm h2 h1 hlt
      linarith
    · rw [← heq, h0]

/-- For `g > 0`: `f_λ(g) < 0 ⟺ g < g(λ)` (a certified lower bound). -/
theorem cubic_neg_iff {lam g : ℝ} (hlam : 0 ≤ lam) (hg : 0 < g) :
    rootCubic lam g < 0 ↔ g < gRoot lam := by
  rw [← not_le, cubic_nonneg_iff hlam hg, not_le]

/-- **`g(0) = √30`** (the uniform root). -/
theorem gRoot_zero : gRoot 0 = Real.sqrt 30 := by
  symm
  refine gRoot_unique le_rfl (Real.sqrt_pos.mpr (by norm_num)) ?_
  rw [rootCubic_sqrt30]
  ring

/-- **`g` decreases in `λ`**: at the root `∂_λ f = g² − 26 > 0`. -/
theorem gRoot_antitone {lam lam' : ℝ} (hlam : 0 ≤ lam) (hle : lam ≤ lam') :
    gRoot lam' ≤ gRoot lam := by
  have hlam' : 0 ≤ lam' := hlam.trans hle
  obtain ⟨hs, -, h0⟩ := gRoot_spec hlam
  have hsq : 26 < gRoot lam ^ 2 := by
    have := pow_lt_pow_left₀ hs sqrt26_pos.le (by norm_num : (2 : ℕ) ≠ 0)
    rwa [sqrt26_sq] at this
  rw [← cubic_nonneg_iff hlam' (gRoot_pos hlam)]
  have : rootCubic lam' (gRoot lam) = rootCubic lam (gRoot lam) +
      (lam' - lam) * (gRoot lam ^ 2 - 26) := by unfold rootCubic; ring
  rw [this, h0]
  have := mul_nonneg (sub_nonneg.mpr hle) (by linarith : (0 : ℝ) ≤ gRoot lam ^ 2 - 26)
  linarith

/-- `g` is strictly decreasing in `λ ≥ 0`. -/
theorem gRoot_strictAnti {lam lam' : ℝ} (hlam : 0 ≤ lam) (hlt : lam < lam') :
    gRoot lam' < gRoot lam := by
  have hlam' : 0 ≤ lam' := hlam.trans hlt.le
  obtain ⟨hs, -, h0⟩ := gRoot_spec hlam
  have hsq : 26 < gRoot lam ^ 2 := by
    have := pow_lt_pow_left₀ hs sqrt26_pos.le (by norm_num : (2 : ℕ) ≠ 0)
    rwa [sqrt26_sq] at this
  have hpos : 0 < rootCubic lam' (gRoot lam) := by
    have : rootCubic lam' (gRoot lam) = rootCubic lam (gRoot lam) +
        (lam' - lam) * (gRoot lam ^ 2 - 26) := by unfold rootCubic; ring
    rw [this, h0]
    have := mul_pos (sub_pos.mpr hlt) (by linarith : (0 : ℝ) < gRoot lam ^ 2 - 26)
    linarith
  rcases (gRoot_antitone hlam hlt.le).lt_or_eq with h | h
  · exact h
  · exfalso
    have := (gRoot_spec hlam').2.2
    rw [h] at this
    linarith

/-! ## The least eigenvalue of `M_λ` -/

/-- **`M_λ ⪰ −g(λ) I`** for `0 ≤ λ ≤ 3√26` (`lem:root-pair-matrix`). -/
theorem Mlam_lower_gRoot {lam : ℝ} (hlam : 0 ≤ lam) (hlam2 : lam ^ 2 ≤ 234) (x : Idx → ℂ) :
    -gRoot lam * ∑ k, ‖x k‖ ^ 2 ≤ (bform (Mlam lam) x x).re :=
  Mlam_lower hlam hlam2 (gRoot_pos hlam) (gRoot_spec hlam).2.2.symm.le x

/-- **`lem:root-pair-matrix`, the least eigenvalue**: for `0 ≤ λ ≤ 3√26`, `−g(λ)` is the minimum
of the Rayleigh quotient of `M_λ`: `M_λ ⪰ −g(λ)I`, with equality at a nonzero vector. -/
theorem Mlam_least {lam : ℝ} (hlam : 0 ≤ lam) (hlam2 : lam ^ 2 ≤ 234) :
    (∀ x : Idx → ℂ, -gRoot lam * ∑ k, ‖x k‖ ^ 2 ≤ (bform (Mlam lam) x x).re) ∧
    ∃ x : Idx → ℂ, ∑ k, ‖x k‖ ^ 2 ≠ 0 ∧ (bform (Mlam lam) x x).re = -gRoot lam * ∑ k, ‖x k‖ ^ 2 :=
  ⟨Mlam_lower_gRoot hlam hlam2, ⟨_, Mlam_attains hlam (gRoot_pos hlam) (gRoot_spec hlam).2.2⟩⟩

/-- **A rational upper bound for `g(λ)` gives the matrix cap** `M_λ ⪰ −g I`. -/
theorem Mlam_lower_of_le {lam g : ℝ} (hlam : 0 ≤ lam) (hlam2 : lam ^ 2 ≤ 234)
    (hg : gRoot lam ≤ g) (x : Idx → ℂ) :
    -g * ∑ k, ‖x k‖ ^ 2 ≤ (bform (Mlam lam) x x).re := by
  have h := Mlam_lower_gRoot hlam hlam2 x
  have h0 : 0 ≤ ∑ k, ‖x k‖ ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  nlinarith

/-- **The strength of a tilt is at most one**: `λ = 2u/(1 + u²) ≤ 1` (`def:positive-root`). -/
theorem strength_le_one (u : ℝ) : 2 * u / (1 + u ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (u - 1)]

theorem strength_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ 2 * u / (1 + u ^ 2) := by positivity

theorem strength_sq_le {u : ℝ} (hu : 0 ≤ u) : (2 * u / (1 + u ^ 2)) ^ 2 ≤ 234 := by
  have h1 := strength_le_one u
  have h0 := strength_nonneg hu
  nlinarith

/-- **`M_{λ_u} ⪰ −g(λ_u) I` for every tilt** `u ≥ 0`, `λ_u = 2u/(1+u²)`. -/
theorem Mlam_lower_tilt {u : ℝ} (hu : 0 ≤ u) (x : Idx → ℂ) :
    -gRoot (2 * u / (1 + u ^ 2)) * ∑ k, ‖x k‖ ^ 2 ≤
      (bform (Mlam (2 * u / (1 + u ^ 2))) x x).re :=
  Mlam_lower_gRoot (strength_nonneg hu) (strength_sq_le hu) x

/-! ## Rational enclosures -/

/-- An enclosure `lo < g(λ) ≤ hi` from two exact sign checks. -/
theorem gRoot_mem_of_signs {lam lo hi : ℝ} (hlam : 0 ≤ lam) (hlo : 0 < lo)
    (hflo : rootCubic lam lo < 0) (hfhi : 0 ≤ rootCubic lam hi) (hhi : 0 < hi) :
    lo < gRoot lam ∧ gRoot lam ≤ hi :=
  ⟨(cubic_neg_iff hlam hlo).mp hflo, (cubic_nonneg_iff hlam hhi).mp hfhi⟩

/-- The six selected strengths `λ_u = 2u/(1 + u²)` (`def:positive-root`), exactly. -/
theorem selected_strengths :
    (2 * (711 / 4096 : ℝ) / (1 + (711 / 4096) ^ 2) = 5824512 / 17282737) ∧
    (2 * (1021 / 4096 : ℝ) / (1 + (1021 / 4096) ^ 2) = 8364032 / 17819657) ∧
    (2 * (1455 / 4096 : ℝ) / (1 + (1455 / 4096) ^ 2) = 11919360 / 18894241) ∧
    (2 * (833 / 1024 : ℝ) / (1 + (833 / 1024) ^ 2) = 1705984 / 1742465) ∧
    (2 * (3851 / 4096 : ℝ) / (1 + (3851 / 4096) ^ 2) = 31547392 / 31607417) ∧
    (2 * (4049 / 4096 : ℝ) / (1 + (4049 / 4096) ^ 2) = 33169408 / 33171617) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **The leading coefficients at the six selected parameters** (`def:positive-root`,
`rem:positive-root-family`: `g(λ)` is the `p → ∞` limit of the chamber coefficient
`g^u_{20}`): enclosures of width `10⁻⁹`,
`g(λ_u) ∈ (5.469872303, 5.469872304]`, `(5.467057002, 5.467057003]`,
`(5.463676084, 5.463676085]`, `(5.456579855, 5.456579856]`, `(5.456199367, 5.456199368]`,
`(5.456162783, 5.456162784]`. Each table value `g` of L20 in `cert:positive-root-caps` exceeds the
corresponding limit (`cert_l20_above_limit`). -/
theorem gRoot_selected :
    (5469872303 / 10 ^ 9 < gRoot (5824512 / 17282737) ∧
      gRoot (5824512 / 17282737) ≤ 5469872304 / 10 ^ 9) ∧
    (5467057002 / 10 ^ 9 < gRoot (8364032 / 17819657) ∧
      gRoot (8364032 / 17819657) ≤ 5467057003 / 10 ^ 9) ∧
    (5463676084 / 10 ^ 9 < gRoot (11919360 / 18894241) ∧
      gRoot (11919360 / 18894241) ≤ 5463676085 / 10 ^ 9) ∧
    (5456579855 / 10 ^ 9 < gRoot (1705984 / 1742465) ∧
      gRoot (1705984 / 1742465) ≤ 5456579856 / 10 ^ 9) ∧
    (5456199367 / 10 ^ 9 < gRoot (31547392 / 31607417) ∧
      gRoot (31547392 / 31607417) ≤ 5456199368 / 10 ^ 9) ∧
    (5456162783 / 10 ^ 9 < gRoot (33169408 / 33171617) ∧
      gRoot (33169408 / 33171617) ≤ 5456162784 / 10 ^ 9) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact gRoot_mem_of_signs (by norm_num) (by norm_num) (by unfold rootCubic; norm_num)
      (by unfold rootCubic; norm_num) (by norm_num)

/-- **The values of `rem:positive-root-family`** to the printed digits: `g(1/2) ≈ 5.466411`,
`g(24/25) ≈ 5.456962`, `g(1) ≈ 5.456161` (individual squares) and, for the square of the average
(strength `6u/(3 + u²)`, `u = 51/40`), `g(4080/2467) ≈ 5.443543`. -/
theorem gRoot_family :
    (5466411 / 10 ^ 6 < gRoot (1 / 2) ∧ gRoot (1 / 2) ≤ 5466412 / 10 ^ 6) ∧
    (5456961 / 10 ^ 6 < gRoot (24 / 25) ∧ gRoot (24 / 25) ≤ 5456962 / 10 ^ 6) ∧
    (5456161 / 10 ^ 6 < gRoot 1 ∧ gRoot 1 ≤ 5456162 / 10 ^ 6) ∧
    (5443543 / 10 ^ 6 < gRoot (4080 / 2467) ∧ gRoot (4080 / 2467) ≤ 5443544 / 10 ^ 6) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact gRoot_mem_of_signs (by norm_num) (by norm_num) (by unfold rootCubic; norm_num)
      (by unfold rootCubic; norm_num) (by norm_num)

/-- The strengths of `rem:positive-root-family`: `u = 3/4` gives `λ = 24/25`, and the square of the
average at `u = 51/40` has strength `6u/(3 + u²) = 4080/2467`. -/
theorem family_strengths :
    2 * (3 / 4 : ℝ) / (1 + (3 / 4) ^ 2) = 24 / 25 ∧
    6 * (51 / 40 : ℝ) / (3 + (51 / 40) ^ 2) = 4080 / 2467 := by
  constructor <;> norm_num

/-- **`cert:positive-root-caps`, a consistency check of the L20 column**: at each of the six
individual-square starts `2³⁰, 2³¹, 2³², 2³⁴, 2³⁶, 2⁴⁰`, the certified chamber coefficient `g` of
the table exceeds the leading coefficient `g(λ_u)`, its `p → ∞` limit
(`rem:positive-root-family`). This checks the table against the matrix lemma; it does not
re-derive the finite caps, whose inputs (`imp:local:collision-gap`, `imp:env:finite-gap-chamber`,
`imp:env:physical-interpolation`) are not formalized here. -/
theorem cert_l20_above_limit :
    gRoot (5824512 / 17282737) < 5476619678296 / 10 ^ 12 ∧
    gRoot (8364032 / 17819657) < 5474335244881 / 10 ^ 12 ∧
    gRoot (11919360 / 18894241) < 5471257426364 / 10 ^ 12 ∧
    gRoot (1705984 / 1742465) < 5464133834236 / 10 ^ 12 ∧
    gRoot (31547392 / 31607417) < 5460775686025 / 10 ^ 12 ∧
    gRoot (33169408 / 33171617) < 5457521105807 / 10 ^ 12 := by
  obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩, ⟨-, h4⟩, ⟨-, h5⟩, ⟨-, h6⟩⟩ := gRoot_selected
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt h1 (by norm_num)
  · exact lt_of_le_of_lt h2 (by norm_num)
  · exact lt_of_le_of_lt h3 (by norm_num)
  · exact lt_of_le_of_lt h4 (by norm_num)
  · exact lt_of_le_of_lt h5 (by norm_num)
  · exact lt_of_le_of_lt h6 (by norm_num)

end Sarkozy.PositiveRoots
