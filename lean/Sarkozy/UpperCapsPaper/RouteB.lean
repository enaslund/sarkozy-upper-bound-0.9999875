module

public import Sarkozy.UpperCapsPaper.RouteA

/-!
# Anchor certificates from Route B: the LL20 root caps below `2⁵²`

`paper/sections/25_upper_reference.tex`: `lem:record:monotone-endpoint` (general form),
`thm:record:direct-star`, `lem:record:frame-inputs`, `lem:record:direct-star-inputs`,
`cert:record:direct-star`, `cert:upper-root-caps`; `lem:logconvex-coefficients`,
`cor:extraction-leaf`(b) (the nonstar coefficients of the 19-anchor tables).

* `RouteBPrime …`: **the per-prime Route B data** of LL20 at `p` (W7's `RouteBData`: the
  decomposition (b) of `thm:record:direct-star` and (H1) with the frame numbers of
  `lem:record:frame-inputs`), with frame numbers at most the anchor's, and with the inputs (H3)
  bounded by fixed functions of `r = p^{-1/2}`. *Analytic*.
* `RouteBPackage p₀ g B`: the data of one band's anchor (`p₀ = X_k`). The nonstar input is the
  polynomial `N_ns/r = C₂ + C₃ r + C₄ r²` (`lem:record:direct-star-inputs`(iii), the coefficients
  `C_k` of the tables at the 19 anchors, interpolated log-convexly to `X_k`); its admissibility is
  **proved** (`nonstarPoly_admissible`). The other normalized inputs `M_⋆/r`, `z_⋆/r²`, `D_col/r`,
  `ε_soft/r` are admissible functions (*analytic*: `rem:pivot-order`, `lem:oct24-collision`(e),
  `lem:record:monotone-endpoint`, proof). The anchor's frame witness `(s_⋆, g_⋆)`, the matrices
  `D`, `𝐑` and the Schur tests (`cert:record:direct-star`), and the numbers at `r₀`, are *finite*.
* **`RouteBPackage.anchor`** (proved): at every class-three prime `p ≥ p₀`, LL20 satisfies
  `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p`. The monotonicity in `p` is W7's `endpoint_numbers` (`ε_Z`,
  `g_root`, `ε_ϱ/r` at `p` are at most their values at `p₀`); the per-prime step is W7's
  `rootcut_prime` (`thm:record:direct-star` with the Schur test of the anchor, `schur_test_mono`).
* **`rootAnchorsB_of_packages`** (proved): `RootAnchorsB` from one package per band below `2⁵²`.
-/

@[expose] public section

open scoped InnerProductSpace Matrix ComplexOrder

namespace Sarkozy.UpperCapsPaper

open Sarkozy Sarkozy.Spectral Sarkozy.UpperReference Sarkozy.Majorant Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws.FieldGraphs Sarkozy.BlockAdapter

/-- **The nonstar polynomial** `N_ns/r = C₂ + C₃ r + C₄ r²` on the box
(`lem:record:direct-star-inputs`(iii) with the coefficients `C_k(Q)` of
`cor:extraction-leaf`(b)). -/
def nonstarPoly {p₀ : ℝ} (C₂ C₃ C₄ : ℝ) (x : Box p₀) : ℝ := C₂ + C₃ * x.1 + C₄ * x.1 ^ 2

/-- **The nonstar polynomial is admissible** (`lem:majorant`(i)): a polynomial in `r` with
nonnegative coefficients. -/
theorem nonstarPoly_admissible {p₀ C₂ C₃ C₄ : ℝ} (h₂ : 0 ≤ C₂) (h₃ : 0 ≤ C₃) (h₄ : 0 ≤ C₄) :
    Majorant.Admissible (nonstarPoly (p₀ := p₀) C₂ C₃ C₄) := by
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · have r0 : 0 ≤ x.1 := x.2.1.le
    have r1 : x.1 ≤ y.1 := hxy
    have a1 := mul_le_mul_of_nonneg_left r1 h₃
    have a2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r0 r1 2) h₄
    unfold nonstarPoly
    linarith
  · have r0 : 0 ≤ x.1 := x.2.1.le
    unfold nonstarPoly
    positivity

/-- **The per-prime Route B data of LL20 at `p`** (W7's `RouteBData`: `thm:record:direct-star`(b),
(H1) with the frame numbers of `lem:record:frame-inputs`; `lem:record:direct-star-inputs`): for
every nonempty labelling set, Route B data with frame numbers at most `(ε_V⁰, ε_×⁰, ε_𝐁⁰)` and with
`ε_soft = r·ns`, `M_⋆ = r·m`, `z_⋆ = r²·z`, `N_ns = r·N`, `D_col = r·D`, `r = p^{-1/2}`.
*Hypothesis* (analytic). -/
def RouteBPrime {n : Type} [Fintype n] (Dm R : Matrix n n ℂ) (p : ℕ) [Fact p.Prime]
    (εV₀ εx₀ εB₀ Λ ns m z N D : ℝ) : Prop :=
  ∀ hne : (Labellings.injLabellings (ZMod p) SpectralD.Root.LL20.G).Nonempty,
    ∃ (Ξ : Type) (_ : Fintype Ξ) (_ : DecidableEq Ξ) (εV εx εB : ℝ),
      RouteBData SpectralD.Root.LL20 hne Ξ n Dm R εV εx εB Λ (√(p : ℝ))⁻¹
        ((√(p : ℝ))⁻¹ * ns) ((√(p : ℝ))⁻¹ * m) ((√(p : ℝ))⁻¹ ^ 2 * z)
        ((√(p : ℝ))⁻¹ * N) ((√(p : ℝ))⁻¹ * D) ∧
      0 ≤ εV ∧ 0 ≤ εx ∧ 0 < εB ∧ εV ≤ εV₀ ∧ εx ≤ εx₀ ∧ εB ≤ εB₀

/-- **One Route B anchor certificate of LL20**, as data (`lem:record:monotone-endpoint`, general
form, at `p₀ = X_k`; `cert:upper-root-caps`). -/
structure RouteBPackage (p₀ g B : ℝ) where
  hp₀ : 0 < p₀
  /-- The index type of the frame and the two fixed matrices `D = ε_G Δ^E` and `𝐑`
  (`lem:record:frame-inputs`, class three). -/
  n : Type
  [fin : Fintype n]
  [dec : DecidableEq n]
  Dm : Matrix n n ℂ
  R : Matrix n n ℂ
  /-- The anchor's frame numbers, `Λ`, and the frame witness `(s_⋆, g_⋆)`. -/
  εV₀ : ℝ
  εx₀ : ℝ
  εB₀ : ℝ
  Λ : ℝ
  s : ℝ
  gs : ℝ
  /-- The nonstar coefficients `C₂, C₃, C₄` at `X_k` (the 19-anchor tables, interpolated). -/
  C₂ : ℝ
  C₃ : ℝ
  C₄ : ℝ
  /-- The normalized inputs `M_⋆/r`, `z_⋆/r²`, `D_col/r`, `ε_soft/r` on the box. -/
  nM : Box p₀ → ℝ
  nz : Box p₀ → ℝ
  nD : Box p₀ → ℝ
  nsoft : Box p₀ → ℝ
  /-- *Finite*: the coefficients are nonnegative. -/
  hC₂ : 0 ≤ C₂
  hC₃ : 0 ≤ C₃
  hC₄ : 0 ≤ C₄
  /-- *Analytic, uniform in the prime*: admissibility (`rem:pivot-order`, `lem:oct24-collision`(e),
  `soft_admissible`). -/
  admM : Majorant.Admissible nM
  admz : Majorant.Admissible nz
  admD : Majorant.Admissible nD
  admsoft : Majorant.Admissible nsoft
  /-- *Analytic, uniform in the prime*: the Route B data at every class-three prime `p ≥ p₀`,
  with the inputs at `r = p^{-1/2}`. -/
  inputs : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → p₀ ≤ p →
    ∀ hr : 0 < (√(p : ℝ))⁻¹ ∧ (√(p : ℝ))⁻¹ ≤ 1 / √p₀,
      @RouteBPrime n fin Dm R p _ εV₀ εx₀ εB₀ Λ (nsoft ⟨_, hr⟩) (nM ⟨_, hr⟩) (nz ⟨_, hr⟩)
        (nonstarPoly C₂ C₃ C₄ ⟨_, hr⟩) (nD ⟨_, hr⟩)
  /-- *Finite, at the anchor*: `𝐑 ⪰ 0`, the signs, and the two Schur tests
  `eq:record:schur` with `g_⋆` (`cert:record:direct-star`(b)). -/
  hRpsd : R.PosSemidef
  hΛ0 : 0 ≤ Λ
  hs0 : 0 < s
  hgs : 0 < gs
  htestp : (Dm + ((gs / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / gs : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef
  htestm : (-Dm + ((gs / (1 + εV₀ + s) : ℝ) : ℂ) • (1 : Matrix n n ℂ) - ((1 / gs : ℝ) : ℂ) •
      (R + ((εB₀ + 2 * Λ * εx₀ + Λ ^ 2 * εV₀ + (εx₀ + Λ * εV₀) ^ 2 / s : ℝ) : ℂ) •
        (1 : Matrix n n ℂ))).PosSemidef
  /-- *Finite, at the anchor*: `ε_Z < 1`, `g_root ≤ g`, `g r₀ < 1` and
  `B ≥ B_top(p₀) = (ε_ϱ/r)²/(1 - g_root r₀)` at `r₀ = p₀^{-1/2}` (`lem:record:monotone-endpoint`,
  `cert:upper-root-caps`). -/
  hZ1 : epsZ (fun x : Box p₀ => x.1) nz (nonstarPoly C₂ C₃ C₄) nD (topBox hp₀) < 1
  hgle : gRoot gs (fun x : Box p₀ => x.1) nM nz (nonstarPoly C₂ C₃ C₄) nD nsoft (topBox hp₀) ≤ g
  hgr : g * (1 / √p₀) < 1
  hB : bTop gs (fun x : Box p₀ => x.1) nM nz (nonstarPoly C₂ C₃ C₄) nD nsoft (topBox hp₀) ≤ B

attribute [instance] RouteBPackage.fin RouteBPackage.dec

namespace RouteBPackage

/-- **The LL20 anchor certificate from a Route B package** (`lem:record:monotone-endpoint`): at
every class-three prime `p ≥ p₀`, `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` for the LL20 chamber cut. -/
theorem anchor {p₀ g B : ℝ} (P : RouteBPackage p₀ g B) :
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → p₀ ≤ p → ChamberCutCap .L (ZMod 2) g B p := by
  intro p _ h3 hp hne v
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le P.hp₀ hp
  have hrpos : 0 < (√(p : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hp0)
  have hrle : (√(p : ℝ))⁻¹ ≤ 1 / √p₀ := by
    rw [one_div]
    exact inv_anti₀ (Real.sqrt_pos.mpr P.hp₀) (Real.sqrt_le_sqrt hp)
  have hr : 0 < (√(p : ℝ))⁻¹ ∧ (√(p : ℝ))⁻¹ ≤ 1 / √p₀ := ⟨hrpos, hrle⟩
  set x : Box p₀ := ⟨(√(p : ℝ))⁻¹, hr⟩ with hx
  have htop : ∀ y : Box p₀, y ≤ topBox P.hp₀ := fun y => y.2.2
  obtain ⟨-, hZx, hgx, hex, -, -⟩ := endpoint_numbers P.gs P.hgs.le (fun x : Box p₀ => x.1)
    P.nM P.nz (nonstarPoly P.C₂ P.C₃ P.C₄) P.nD P.nsoft (admissible_coord p₀) P.admM P.admz
    (nonstarPoly_admissible P.hC₂ P.hC₃ P.hC₄) P.admD P.admsoft (topBox P.hp₀) htop P.hZ1
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right P.hgle (topBox P.hp₀).2.1.le) P.hgr) x
  obtain ⟨Ξ, _, _, εV, εx, εB, hdata, hεV, hεx, hεB, hV, hX, hBB⟩ := P.inputs p h3 hp hr hne
  have hεZ : 2 * ((√(p : ℝ))⁻¹ ^ 2 * P.nz x) + (√(p : ℝ))⁻¹ * nonstarPoly P.C₂ P.C₃ P.C₄ x +
      (√(p : ℝ))⁻¹ * P.nD x < 1 := hZx
  set G := gRoot P.gs (fun x : Box p₀ => x.1) P.nM P.nz (nonstarPoly P.C₂ P.C₃ P.C₄) P.nD P.nsoft
    (topBox P.hp₀) with hG
  have hgR := (gRoot_eq P.gs (fun x : Box p₀ => x.1) P.nM P.nz (nonstarPoly P.C₂ P.C₃ P.C₄) P.nD
    P.nsoft x hrpos).symm.le.trans hgx
  have heR := (eRho_eq (fun x : Box p₀ => x.1) P.nM P.nz (nonstarPoly P.C₂ P.C₃ P.C₄) P.nD x
    hrpos).symm.le.trans hex
  have hr₀ : (0 : ℝ) ≤ (√p₀)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hgr₀ : G * (√p₀)⁻¹ < 1 := by
    have : g * (√p₀)⁻¹ < 1 := by rw [← one_div]; exact P.hgr
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right P.hgle hr₀) this
  obtain ⟨hl, hu⟩ := rootcut_prime SpectralD.Root.LL20 hne P.Dm P.R hdata P.hRpsd hεV hεx hεB
    P.hΛ0 P.hs0 P.hgs hrpos hV hX hBB P.htestp P.htestm hεZ hgR heR (hrle.trans_eq (one_div _))
    hgr₀
  have hv : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  constructor
  · have h : -(G * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
        ⟪v, Spectral.cutOp (chamberData .L (ZMod 2)) hne v⟫_ℝ := hl v
    have : -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ -(G * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_right P.hgle hrpos.le)) hv
    exact this.trans h
  · have h := hu v
    have hsq : ((√(p : ℝ))⁻¹) ^ 2 = 1 / (p : ℝ) := by
      rw [inv_pow, Real.sq_sqrt hp0.le, one_div]
    have hB' : eRho (fun x : Box p₀ => x.1) P.nM P.nz (nonstarPoly P.C₂ P.C₃ P.C₄) P.nD
        (topBox P.hp₀) ^ 2 / (1 - G * (√p₀)⁻¹) ≤ B := by
      have hb := P.hB
      unfold bTop at hb
      rw [← one_div]
      exact hb
    have hle : 1 + eRho (fun x : Box p₀ => x.1) P.nM P.nz (nonstarPoly P.C₂ P.C₃ P.C₄) P.nD
        (topBox P.hp₀) ^ 2 / (1 - G * (√p₀)⁻¹) * ((√(p : ℝ))⁻¹) ^ 2 ≤ 1 + B / p := by
      rw [hsq, mul_one_div]
      exact add_le_add_right (div_le_div_of_nonneg_right hB' hp0.le) 1
    exact h.trans (mul_le_mul_of_nonneg_right hle hv)

end RouteBPackage

/-- **`RootAnchorsB` (the LL20 caps below `2⁵²`) from one Route B package per band.** -/
theorem rootAnchorsB_of_packages
    (P : ∀ k : Fin 310, k.val < 301 → RouteBPackage (capRow k .LL20).anchor (capRow k .LL20).g
      (capRow k .LL20).B) : RootAnchorsB := fun k hk p _ h3 hp => (P k hk).anchor p h3 hp

end Sarkozy.UpperCapsPaper
