module

public import Sarkozy.UpperCapsPaper.Tables
public import Sarkozy.UpperReference.RootCaps

/-!
# Anchor certificates from Route A: the completed root from `2⁵²` and the nonroot caps

`paper/sections/25_upper_reference.tex`: `lem:upper-completed-root` (LL20 and LL22 from `2⁵²`,
`cert:upper-completed-root`); `subsec:upper-nonroot` with (F6) and `lem:record:domain`(i) (the five
nonroot chamber cuts, `cert:upper-band-inputs`(a)); `thm:spectral-criterion`,
`cor:spec2:coupling`, `prop:spec2:mucentre`, `lem:spectral-monotone`, `lem:majorant`.

Both kinds of anchor are Route A (`thm:spectral-criterion`) certificates at an evaluation point
`p₀`: the inputs are admissible functions of `r ∈ (0, p₀^{-1/2}]`, the tests are made once at
`r₀ = p₀^{-1/2}`, and the conclusions then hold at every prime `p ≥ p₀` of the tested class.

* `RouteAPrime f Λ Aplus X p …`: **the per-prime Route A inputs** of the chamber cut of `G_{Lf}`
  at `p` (W1/WP-A's `Spectral.RouteAInputs` for the complex cut operator `Cx.cutOpC` on
  `L²(λ(G⁺))`, at every nonempty labelling set). *Analytic*.
* `RouteAPackage f Λ p₀ g B`: the data of one anchor. Its fields are marked:
  - *analytic, uniform in the prime*: the admissibility of the input functions
    (`lem:spectral-monotone`(a)–(d), `lem:oct24-collision`(e), `rem:pivot-order`) and the per-prime
    inputs at every class-three prime `p ≥ p₀`;
  - *finite, at the anchor*: the numbers at `r₀` (`ε_Z < 1`, `c_⊥ ≤ c̄_⊥`, `η_Q ≤ η̄_Q`,
    `η_B ≤ η̄_B`, `ε_V ≤ ε̄_V < 1`), the two matrix tests `eq:spectral-test` (PSD), `g ≥ g_±`,
    `g' r₀ < 1` and `B ≥ p₀ ε_ϱ(r₀)²/(1 - g' r₀)` (for any `g₁ ≤ g, g'` with `g₁ ≥ g_±`; the paper
    takes `g₁ = g' = g`).
* **`RouteAPackage.anchor`** (proved): the package gives `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` for the
  real chamber cut operator at every class-three prime `p ≥ p₀`. This is the monotonicity in `p`
  (W7's `upper_completed_root_prime`, through WP-A's `spectral_criterion_uniform`) and the passage
  from the complex realization to B6's real operator (W7's `real_bounds_of_complex`).
* **`rootAnchorsA_of_packages`**, **`nonrootAnchors_of_packages`** (proved): `RootAnchorsA` (the 9
  bands from `2⁵²`) and `NonrootAnchors` (the 10 nonroot anchors) from one package per anchor.

What stays open in a package: the per-prime inputs (the paper's `prop:spec2:mucentre`,
`cor:spec2:coupling` with the refined coupling inputs `Γ^loc_E` (`lem:push:localvariance`, which
uses H4 through `thm:dl:H2`) and `ε^loc_H`; `cor:extraction-compressed` or the coefficient tables
for `N_ns`), their admissibility, and the anchor numbers and matrices (the grids
`upper_*_grid.json`, `class3_*caps.json`, replayed by `replay_upper_psd.py`,
`review_class3_nonroot.py`).
-/

@[expose] public section

open scoped InnerProductSpace Matrix ComplexOrder

namespace Sarkozy.UpperCapsPaper

open Sarkozy Sarkozy.Spectral Sarkozy.UpperReference Sarkozy.Majorant Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws.FieldGraphs Sarkozy.BlockAdapter

variable (f : FieldTy) (Λ : Type) [Fintype Λ] [DecidableEq Λ]

/-- **The per-prime Route A inputs of the chamber cut of `G_{Lf}` at `p`**
(`thm:spectral-criterion` with `prop:spec2:mucentre`, `cor:spec2:coupling`): for every nonempty
labelling set, WP-A's `RouteAInputs` for the complex cut operator, with the degree-one forms of the
fixed matrices `±A₊` (by Fourier sign) and `X`, at `r = p^{-1/2}`. *Hypothesis* (analytic). -/
def RouteAPrime {n : Type} [Fintype n] (Aplus X : Matrix n n ℂ) (p : ℕ) [Fact p.Prime]
    (ηQ ηB εV ερ aperp : ℝ) : Prop :=
  ∀ hne : (Labellings.injLabellings (ZMod p) (chamberData f Λ).G).Nonempty,
    ∃ (V Sp Sm : Submodule ℂ (EuclideanSpace ℂ ((chamberData f Λ).cut.Half → ZMod p)))
      (Ξ : Type) (_ : Fintype Ξ) (sgn : Ξ → Prop) (_ : DecidablePred sgn)
      (coef : EuclideanSpace ℂ ((chamberData f Λ).cut.Half → ZMod p) → Ξ → n → ℂ),
      RouteAInputs (SpectralD.Cx.cutOpC (chamberData f Λ) hne)
        (SpectralD.Cx.cutOneC (chamberData f Λ) hne) V Sp Sm sgn coef
        (fun ξ x => RCLike.re (star x ⬝ᵥ ((if sgn ξ then Aplus else -Aplus) *ᵥ x)))
        (fun _ x => RCLike.re (star x ⬝ᵥ (X *ᵥ x))) (1 / √(p : ℝ)) ηQ ηB εV ερ aperp

/-- The top `r₀ = p₀^{-1/2}` of the box. -/
noncomputable def topBox {p₀ : ℝ} (hp₀ : 0 < p₀) : Box p₀ :=
  ⟨1 / √p₀, by positivity, le_rfl⟩

/-- **One Route A anchor certificate**, as data (`lem:upper-completed-root` for LL20 from `2⁵²`;
(F6) of `lem:record:domain` for the nonroot cuts). -/
structure RouteAPackage (p₀ g B : ℝ) where
  /-- The anchor is positive. -/
  hp₀ : 0 < p₀
  /-- The index type of the degree-one coordinates and the two fixed matrices of the tests. -/
  n : Type
  [fin : Fintype n]
  [dec : DecidableEq n]
  Aplus : Matrix n n ℂ
  X : Matrix n n ℂ
  /-- The standard star constants `P_st = c_P r²`, `W_st = c_W r`. -/
  cP : ℝ
  cW : ℝ
  hcP : 0 ≤ cP
  hcW : 0 ≤ cW
  /-- The normalized inputs `N_ns/r`, `D_ord/r`, `D_nat/r`, `M_⋆/r`, `z_⋆/r²` (both classes) and the
  coupling numbers `η_Q`, `η_B`, `ε_V`, as functions on the box. -/
  nN : Box p₀ → ℝ
  nDord : Box p₀ → ℝ
  nDnat : Box p₀ → ℝ
  nM₁ : Box p₀ → ℝ
  nM₃ : Box p₀ → ℝ
  nz₁ : Box p₀ → ℝ
  nz₃ : Box p₀ → ℝ
  ηQf : Box p₀ → ℝ
  ηBf : Box p₀ → ℝ
  εVf : Box p₀ → ℝ
  /-- *Analytic, uniform in the prime*: admissibility (`lem:spectral-monotone`(a)–(d),
  `lem:oct24-collision`(e), `rem:pivot-order`, `lem:majorant`). -/
  admN : Majorant.Admissible nN
  admDord : Majorant.Admissible nDord
  admDnat : Majorant.Admissible nDnat
  admM₁ : Majorant.Admissible nM₁
  admM₃ : Majorant.Admissible nM₃
  admz₁ : Majorant.Admissible nz₁
  admz₃ : Majorant.Admissible nz₃
  admηQ : Majorant.Admissible ηQf
  admηB : Majorant.Admissible ηBf
  admεV : Majorant.Admissible εVf
  /-- *Analytic, uniform in the prime*: the Route A inputs at every class-three prime `p ≥ p₀`,
  formed with the input functions at `r = p^{-1/2}` (`lem:upper-completed-root`(i),(ii)). -/
  inputs : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → p₀ ≤ p →
    ∀ hr : 0 < 1 / √(p : ℝ) ∧ 1 / √(p : ℝ) ≤ 1 / √p₀,
      @RouteAPrime f Λ _ _ n fin Aplus X p _ (ηQf ⟨1 / √(p : ℝ), hr⟩) (ηBf ⟨1 / √(p : ℝ), hr⟩)
        (εVf ⟨1 / √(p : ℝ), hr⟩)
        (1 / √(p : ℝ) * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ ⟨1 / √(p : ℝ), hr⟩)
        (1 / √(p : ℝ) * (1 / (1 - completedEpsZ cP cW nN nDord nDnat nz₁ nz₃
          ⟨1 / √(p : ℝ), hr⟩) * (nN ⟨1 / √(p : ℝ), hr⟩ +
            min (nDord ⟨1 / √(p : ℝ), hr⟩) (nDnat ⟨1 / √(p : ℝ), hr⟩))))
  /-- *Finite, at the anchor*: the bars and the test parameters. -/
  cbar : ℝ
  ηQbar : ℝ
  ηBbar : ℝ
  εVbar : ℝ
  τp : ℝ
  τm : ℝ
  g₁ : ℝ
  g' : ℝ
  hZ1 : completedEpsZ cP cW nN nDord nDnat nz₁ nz₃ (topBox hp₀) < 1
  hcbar0 : 0 ≤ cbar
  hc0 : completedCperp cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ (topBox hp₀) ≤ cbar
  hηQ0 : ηQf (topBox hp₀) ≤ ηQbar
  hηB0 : ηBf (topBox hp₀) ≤ ηBbar
  hεV0 : εVf (topBox hp₀) ≤ εVbar
  hεVbar0 : 0 ≤ εVbar
  hεV1 : εVbar < 1
  hτp : 0 < τp
  hτm : 0 < τm
  /-- *Finite*: the two matrix tests `eq:spectral-test` (both Fourier signs). -/
  htestp : (Aplus - ((τp⁻¹ : ℝ) : ℂ) • X +
    ((cbar + τp - ηQbar - ηBbar / τp : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef
  htestm : (-Aplus - ((τm⁻¹ : ℝ) : ℂ) • X +
    ((cbar + τm - ηQbar - ηBbar / τm : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef
  /-- *Finite*: the recorded `g`, `g'` and `B`. -/
  hgp : (cbar + τp) / (1 - εVbar) ≤ g₁
  hgm : (cbar + τm) / (1 - εVbar) ≤ g₁
  hg₁ : g₁ ≤ g
  hgg' : g₁ ≤ g'
  hg'r : g' * (1 / √p₀) < 1
  hB : p₀ * (1 / √p₀ * completedRhoR cP cW nN nDord nDnat nM₁ nM₃ nz₁ nz₃ (topBox hp₀)) ^ 2 /
    (1 - g' * (1 / √p₀)) ≤ B

attribute [instance] RouteAPackage.fin RouteAPackage.dec

namespace RouteAPackage

variable {f Λ}

/-- **The anchor certificate from a Route A package** (`lem:upper-completed-root`; (F6) with
`lem:record:domain`(i)): at every class-three prime `p ≥ p₀`, the real chamber cut operator
satisfies `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p`. The monotonicity in `p` is W7's
`upper_completed_root_prime`; the passage to the real operator is `real_bounds_of_complex`. -/
theorem anchor {p₀ g B : ℝ} (P : RouteAPackage f Λ p₀ g B) :
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → p₀ ≤ p → ChamberCutCap f Λ g B p := by
  intro p _ h3 hp hne v
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le P.hp₀ hp
  have hr : 0 < 1 / √(p : ℝ) ∧ 1 / √(p : ℝ) ≤ 1 / √p₀ :=
    ⟨by positivity, one_div_le_one_div_of_le (Real.sqrt_pos.mpr P.hp₀) (Real.sqrt_le_sqrt hp)⟩
  obtain ⟨V, Sp, Sm, Ξ, _, sgn, _, coef, hin⟩ := P.inputs p h3 hp hr hne
  obtain ⟨hlow, -, -, hup⟩ := upper_completed_root_prime P.Aplus P.X P.hp₀ hp P.hcP P.hcW
    P.nN P.nDord P.nDnat P.nM₁ P.nM₃ P.nz₁ P.nz₃ P.admN P.admDord P.admDnat P.admM₁ P.admM₃
    P.admz₁ P.admz₃ P.ηQf P.ηBf P.εVf P.admηQ P.admηB P.admεV hr (topBox P.hp₀) rfl P.hZ1 hin
    P.hcbar0 P.hc0 P.hηQ0 P.hηB0 P.hεV0 P.hεVbar0 P.hεV1 P.hτp P.hτm P.htestp P.htestm P.hgp
    P.hgm P.hgg' P.hg'r
  obtain ⟨hl, hu⟩ := real_bounds_of_complex (chamberData f Λ) hne hlow hup
  have hpinv : 1 / √(p : ℝ) = (√(p : ℝ))⁻¹ := one_div _
  constructor
  · have h : -(P.g₁ * (1 / √(p : ℝ))) * ‖v‖ ^ 2 ≤
        ⟪v, Spectral.cutOp (chamberData f Λ) hne v⟫_ℝ := hl v
    rw [hpinv] at h
    have hr0 : (0 : ℝ) ≤ (√(p : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have : -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ -(P.g₁ * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_right P.hg₁ hr0))
        (sq_nonneg _)
    exact this.trans h
  · have h := hu v
    have hv : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    have hle : 1 + p₀ * (1 / √p₀ * completedRhoR P.cP P.cW P.nN P.nDord P.nDnat P.nM₁ P.nM₃
        P.nz₁ P.nz₃ (topBox P.hp₀)) ^ 2 / (1 - P.g' * (1 / √p₀)) / p ≤ 1 + B / p :=
      add_le_add_right (div_le_div_of_nonneg_right P.hB hp0.le) 1
    exact h.trans (mul_le_mul_of_nonneg_right hle hv)

end RouteAPackage

/-! ## The six cuts as chamber data -/

/-- The layer set of the cut: `ℤ/2` (two layers) or `Unit` (one layer). -/
def Cap.Lam : Cap → Type
  | .LL20 | .FL21 | .EL21 => ZMod 2
  | .LL10 | .FL11 | .EL11 => Unit

instance Cap.instFintypeLam : (c : Cap) → Fintype c.Lam
  | .LL20 | .FL21 | .EL21 => inferInstanceAs (Fintype (ZMod 2))
  | .LL10 | .FL11 | .EL11 => inferInstanceAs (Fintype Unit)

instance Cap.instDecEqLam : (c : Cap) → DecidableEq c.Lam
  | .LL20 | .FL21 | .EL21 => inferInstanceAs (DecidableEq (ZMod 2))
  | .LL10 | .FL11 | .EL11 => inferInstanceAs (DecidableEq Unit)

/-- `CapPrime` is B6's `ChamberCutCap` at the cut's field type and layer set. -/
theorem capPrime_iff (c : Cap) (g B : ℝ) (p : ℕ) [Fact p.Prime] :
    CapPrime c g B p ↔ ChamberCutCap c.field c.Lam g B p := by
  cases c <;> exact Iff.rfl

/-- An anchor certificate from a Route A package. -/
theorem anchorCap_of_package {c : Cap} {p₀ g B : ℝ} (P : RouteAPackage c.field c.Lam p₀ g B) :
    AnchorCap c p₀ g B := fun p _ h3 hp => (capPrime_iff c g B p).mpr (P.anchor p h3 hp)

/-- **`RootAnchorsA` (the completed root from `2⁵²`) from one Route A package per band.** -/
theorem rootAnchorsA_of_packages
    (P : ∀ k : Fin 310, 301 ≤ k.val → RouteAPackage .L (ZMod 2) (capRow k .LL20).anchor
      (capRow k .LL20).g (capRow k .LL20).B) : RootAnchorsA := fun k hk =>
  anchorCap_of_package (c := .LL20) (P k hk)

/-- **`NonrootAnchors` from one Route A package per nonroot cut and anchor** (`2⁴⁷`, `2⁴⁸`). -/
theorem nonrootAnchors_of_packages
    (P47 : ∀ c : Cap, c ≠ .LL20 → RouteAPackage c.field c.Lam (nonroot47 c).anchor
      (nonroot47 c).g (nonroot47 c).B)
    (P48 : ∀ c : Cap, c ≠ .LL20 → RouteAPackage c.field c.Lam (nonroot48 c).anchor
      (nonroot48 c).g (nonroot48 c).B) : NonrootAnchors := fun c hc =>
  ⟨anchorCap_of_package (P47 c hc), anchorCap_of_package (P48 c hc)⟩

end Sarkozy.UpperCapsPaper
