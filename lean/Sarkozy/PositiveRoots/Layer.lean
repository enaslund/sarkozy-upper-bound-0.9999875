module

public import Sarkozy.PositiveRoots.LayerConstants
public import Sarkozy.Cuts.Envelope
public import Sarkozy.Cuts.Restriction
public import Sarkozy.Cuts.Tilt
public import Sarkozy.PartV.PositiveRoot

/-!
# The layer cut of a positive root, II: the assembly (`prop:root-layer`, `lem:native-pair-linear`)

`paper/sections/20b_positive_roots.tex`, subsection `subsec:positive-root-layer`: the proof of
`prop:root-layer` from its intermediate bounds, the mass step, and the arithmetic of
`lem:native-pair-linear`. Constants: `Sarkozy.PositiveRoots.Layer` (`LayerConstants`).

**The setting.** `lam` is the soft half law `ν_△ = μ_△ ⊗ μ_△` (one uniform directed cyclic
triangle for each component of `G_{L,1}`), on a finite type `X`; `I` is the event that the six
labels are distinct, of probability `h ≥ h_- = 1 - 9q`; `ν = lam(· | I)` is the fixed uniform
induced layer half `λ_p(G_{L,1})`. A kernel `N` on `X × X` is the numerator of the cut operator
of the tilted root at `ι`, i.e. the raw kernel of the uniform root multiplied by `w_u`; by
`lem:spec:cutkernel`(f) the cut operator is `T^ι_u = N / ⟨1, N1⟩_ν` (`cutOp`). This
identification is the modelling step; it is not proved here.

**Proved** (`root_layer_caps`): from the intermediate bounds of the proof of `prop:root-layer`,
taken as hypotheses (each named after its paragraph),
* `N = B + E₁ + E₂ + E_nn - E_sc - E_cr` ("Soft expansion" and "Coincidences"): the base term
  `B = (1 ⊗ 1) ∘ Υ` is positive semidefinite on `L²(ν)` (`hB`); the two one-component terms have
  norm `≤ 𝔫m_u` (`hE₁`, `hE₂`, from (L1), (L2)); the `63²` monomials of `N_Φ ⊗ N_Φ` have norm
  `≤ C_{nn,u}q` (`hEnn`, from (L3)); the deleted selected-label coincidences `≤ C_{sc,u}q`
  (`hEsc`) and the other cross coincidences `≤ C_{cr,u}q` (`hEcr`, (L4)), all on `L²(ν_△)`;
* "Centred norm": `‖P₀BP₀‖ ≤ 2ur + γc₀q` on `L²(ν)` (`hBc`);
* "Row": `‖P₀N1‖ ≤ q(C_u + C_{in,u} + 910γ + 2(1 + γ)𝔟/h_-)/h_-` on `L²(ν)` (`hrow`);
* "Mass": `⟨1, N1⟩_ν ≥ z^ι_u Z_-` (`hmass`; from `raw_mass_ge` and `tilt_mass_ge_zI`);

the conclusions of `prop:root-layer` with the paper's constants:
`-g^ι_u r I ⪯ T^ι_u ⪯ (1 + c^{+,ι}_u q)I`, `‖P₀T^ι_u1‖ ≤ qA^ι_u`, `‖P₀T^ι_uP₀‖ ≤ c^ι_u`, and
`T^ι_u` symmetric of mass one. The restriction to `ν` (cost `h_-^{-1}`) is `lem:restriction`(b)
(`Cuts.restriction_full`); the upper bound is `prop:matching:positive`(a)
(`Cuts.envelope_upper`). At `p ≥ 2³⁰` the gates `Z_- > 0`, `h_- > 0` are proved
(`root_layer_caps_of_ge`); the gates `z^ι_u > 0` and `c^ι_u < 1` stay hypotheses, as in the paper.

* **The mass step** (`tilt_mass_ge`, `tilt_mass_ge_zI`), with V1's `PartV.individualWeight` and
  `PartV.rootScore`: from `|E_{Γ_{p,0}} H_j| ≤ h_0` and
  `E_{Γ_{p,0}} H_j² ≥ 1 - 4q - 36qB_H² - 2q/(1 - q)` (`lem:root-normalization`(b), hypotheses),
  `E_{Γ_{p,0}} w_u ≥ z^ι_u` for every law `Γ_{p,0}` (in particular `λ_p(G_{L,2})`).
* **`lem:native-pair-linear`, the arithmetic** (`native_pair_sum`, `native_pair_linear`): the
  eight classes of `K ∘ 𝖧 - 𝖧` with the prices of the proof (one-sided terms `r‖S‖`, `r‖R‖`; the
  `144` terms of `S ⊗ S` at `16q`; the mixed terms `r^{-1}‖S‖‖R‖`, `r^{-1}‖R‖²`) sum to exactly
  `C_pair q` (with `q = r²`), and the restriction to the actual half costs `(1 - 9q)^{-1}`
  (`native_pair_linear_restrict`). The class prices themselves are hypotheses.

**Not proved here** (hypotheses): every analytic bound listed above ((L1)–(L4), the class
prices of `lem:native-pair-linear`, the centred base, the row, the coincidence row and column
bounds, `lem:root-normalization`(b)), and the identification of `cutOp` with the cut operator.

**Non-vacuity** (`root_layer_caps_nonvacuous`): the hypotheses of `root_layer_caps` hold together
for a one-point space with `N = B` constant, at `q = 2⁻³⁰`, `r = 2⁻¹⁵`, `u = 0`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.PositiveRoots

namespace Layer

open Sarkozy Sarkozy.Cuts Sarkozy.Recentering Sarkozy.Peyre

variable {X : Type*} [Fintype X]

/-! ## Linearity of the kernel form in the kernel -/

theorem kernelForm_add_kernel (ν μ : FiniteLaw X) (K₁ K₂ : X → X → ℝ) (f g : X → ℝ) :
    kernelForm ν μ (fun x y => K₁ x y + K₂ x y) f g =
      kernelForm ν μ K₁ f g + kernelForm ν μ K₂ f g := by
  simp only [kernelForm, LinearMap.mk₂_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

theorem kernelForm_div_const (ν μ : FiniteLaw X) (K : X → X → ℝ) (D : ℝ) (f g : X → ℝ) :
    kernelForm ν μ (fun x y => K x y / D) f g = kernelForm ν μ K f g / D := by
  simp only [kernelForm, LinearMap.mk₂_apply, Finset.sum_div]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

/-- The form of `E₁ + E₂ + E_nn - E_sc - E_cr`. -/
theorem kernelForm_five (ν μ : FiniteLaw X) (E₁ E₂ E₃ E₄ E₅ : X → X → ℝ) (f g : X → ℝ) :
    kernelForm ν μ (fun x y => E₁ x y + E₂ x y + E₃ x y - E₄ x y - E₅ x y) f g =
      kernelForm ν μ E₁ f g + kernelForm ν μ E₂ f g + kernelForm ν μ E₃ f g -
        kernelForm ν μ E₄ f g - kernelForm ν μ E₅ f g := by
  simp only [kernelForm, LinearMap.mk₂_apply, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

/-! ## The cut operator of the tilted root -/

/-- The normalized kernel `T = N/⟨1, N1⟩_ν`: by `lem:spec:cutkernel`(f), the cut operator
`T^ι_u = (T^ι_0 ∘ w_u)/E_{Γ_{p,0}} w_u` of `Γ_{p,u}` at `ι`, for `N` the raw kernel of the uniform
root times `w_u`. -/
noncomputable def cutOp (ν : FiniteLaw X) (N : X → X → ℝ) : X → X → ℝ :=
  fun x y => N x y / kmass ν N

/-! ## `prop:root-layer`: the assembly -/

/-- **`prop:root-layer`, the assembly** (paragraphs "Soft expansion", "Coincidences", "Mass",
"Lower bound", "Centred norm", "Row", "Upper bound" of the proof). The analytic bounds of the
proof are hypotheses, named after their paragraphs (see the module docstring); the conclusion is
the statement of `prop:root-layer` for `T^ι_u = cutOp ν N`:
`-g^ι_u r I ⪯ T^ι_u ⪯ (1 + c^{+,ι}_u q) I`, `‖P₀ T^ι_u 1‖ ≤ q A^ι_u`, `‖P₀ T^ι_u P₀‖ ≤ c^ι_u`,
`T^ι_u` symmetric of mass one. The gates: `z^ι_u > 0`, `c^ι_u < 1` (as in the paper) and
`Z_- > 0`, `h_- > 0` (proved for `p ≥ 2³⁰` in `root_layer_caps_of_ge`). -/
theorem root_layer_caps (lam : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lam I)
    (ν : FiniteLaw X) (hν : ν = condLaw lam I hP) {u q r : ℝ} (hu : 0 ≤ u) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hr : 0 < r) (hhm : 0 < hm q) (hPh : hm q ≤ prob lam I) (hZm : 0 < Zm q r)
    (hz : 0 < zI u q r) (hc : cI u q r < 1)
    (N B E₁ E₂ Enn Esc Ecr : X → X → ℝ)
    (hNdec : ∀ x y, N x y = B x y + (E₁ x y + E₂ x y + Enn x y - Esc x y - Ecr x y))
    (hNsymm : ∀ x y, N y x = N x y)
    (hB : ∀ f, 0 ≤ kernelForm ν ν B f f)
    (hBc : ∀ f g, ν.expect f = 0 → ν.expect g = 0 →
      |kernelForm ν ν B f g| ≤ (2 * u * r + u ^ 2 * c0 q * q) * nrm ν f * nrm ν g)
    (hE₁ : ∀ f g, |kernelForm lam lam E₁ f g| ≤ nF q r * mU u r * nrm lam f * nrm lam g)
    (hE₂ : ∀ f g, |kernelForm lam lam E₂ f g| ≤ nF q r * mU u r * nrm lam f * nrm lam g)
    (hEnn : ∀ f g, |kernelForm lam lam Enn f g| ≤ Cnn u r * q * nrm lam f * nrm lam g)
    (hEsc : ∀ f g, |kernelForm lam lam Esc f g| ≤ Csc u q r * q * nrm lam f * nrm lam g)
    (hEcr : ∀ f g, |kernelForm lam lam Ecr f g| ≤ Ccr u q r * q * nrm lam f * nrm lam g)
    (hrow : ∀ f, ν.expect f = 0 → |kernelForm ν ν N f (fun _ => 1)| ≤
      q * ((CU u q r + Cin u q r + 910 * u ^ 2 + 2 * (1 + u ^ 2) * bF q r / hm q) / hm q) *
        nrm ν f)
    (hmass : zI u q r * Zm q r ≤ kmass ν N) :
    kmass ν (cutOp ν N) = 1 ∧ (∀ x y, cutOp ν N y x = cutOp ν N x y) ∧
    (∀ f, -(gI u q r * r) * nrm ν f ^ 2 ≤ kernelForm ν ν (cutOp ν N) f f) ∧
    (∀ f, kernelForm ν ν (cutOp ν N) f f ≤ (1 + cPlusI u q r * q) * nrm ν f ^ 2) ∧
    (∀ f, ν.expect f = 0 → |kernelForm ν ν (cutOp ν N) f (fun _ => 1)| ≤ q * AI u q r * nrm ν f) ∧
    (∀ f g, ν.expect f = 0 → ν.expect g = 0 →
      |kernelForm ν ν (cutOp ν N) f g| ≤ cI u q r * nrm ν f * nrm ν g) := by
  set D := kmass ν N with hD
  have hzZ : 0 < zI u q r * Zm q r := mul_pos hz hZm
  have hD0 : 0 < D := lt_of_lt_of_le hzZ hmass
  have hT : ∀ f g, kernelForm ν ν (cutOp ν N) f g = kernelForm ν ν N f g / D := fun f g =>
    kernelForm_div_const ν ν N D f g
  -- the error kernel and its soft bound
  set E : X → X → ℝ := fun x y => E₁ x y + E₂ x y + Enn x y - Esc x y - Ecr x y with hE
  set ε := 2 * nF q r * mU u r + CU u q r * q with hε
  have hNBE : ∀ f g, kernelForm ν ν N f g = kernelForm ν ν B f g + kernelForm ν ν E f g := by
    intro f g
    have : N = fun x y => B x y + E x y := by
      funext x y
      rw [hNdec]
    rw [this, kernelForm_add_kernel]
  have hn1 : nrm lam (fun _ => 1) = 1 := nrm_one lam
  have p1 : 0 ≤ nF q r * mU u r := by
    have := hE₁ (fun _ => 1) (fun _ => 1)
    rw [hn1, mul_one, mul_one] at this
    exact le_trans (abs_nonneg _) this
  have hε0 : 0 ≤ ε := by
    have := CU_nonneg hu hq0 hq1 hr.le
    rw [hε]
    have : 0 ≤ CU u q r * q := mul_nonneg this hq0
    linarith
  have hEsoft : ∀ f g, |kernelForm lam lam E f g| ≤ ε * nrm lam f * nrm lam g := by
    intro f g
    rw [hE, kernelForm_five, sub_eq_add_neg, sub_eq_add_neg]
    have a1 := hE₁ f g
    have a2 := hE₂ f g
    have a3 := hEnn f g
    have a4 := hEsc f g
    have a5 := hEcr f g
    have t := abs_add_le (kernelForm lam lam E₁ f g + kernelForm lam lam E₂ f g +
      kernelForm lam lam Enn f g + -kernelForm lam lam Esc f g) (-kernelForm lam lam Ecr f g)
    have t2 := abs_add_le (kernelForm lam lam E₁ f g + kernelForm lam lam E₂ f g +
      kernelForm lam lam Enn f g) (-kernelForm lam lam Esc f g)
    have t3 := abs_add_le (kernelForm lam lam E₁ f g + kernelForm lam lam E₂ f g)
      (kernelForm lam lam Enn f g)
    have t4 := abs_add_le (kernelForm lam lam E₁ f g) (kernelForm lam lam E₂ f g)
    rw [abs_neg] at t t2
    have e : ε * nrm lam f * nrm lam g = nF q r * mU u r * nrm lam f * nrm lam g +
        nF q r * mU u r * nrm lam f * nrm lam g + Cnn u r * q * nrm lam f * nrm lam g +
        Csc u q r * q * nrm lam f * nrm lam g + Ccr u q r * q * nrm lam f * nrm lam g := by
      rw [hε]
      unfold CU
      ring
    rw [e]
    linarith
  -- the restriction to `ν`
  have hEν : ∀ f g, |kernelForm ν ν E f g| ≤ ε / hm q * nrm ν f * nrm ν g := by
    intro f g
    have h := restriction_full lam lam I I hP hP E hEsoft f g
    rw [Real.sqrt_mul_self hP.le, ← hν] at h
    have hle : ε / prob lam I ≤ ε / hm q := div_le_div_of_nonneg_left hε0 hhm hPh
    have hf0 := nrm_nonneg ν f
    have hg0 := nrm_nonneg ν g
    calc _ ≤ ε / prob lam I * nrm ν f * nrm ν g := h
      _ ≤ ε / hm q * nrm ν f * nrm ν g := by gcongr
  -- the mass and the symmetry
  have hmass1 : kmass ν (cutOp ν N) = 1 := by
    rw [kmass_eq_kernelForm, hT, ← kmass_eq_kernelForm, ← hD, div_self hD0.ne']
  have hsymm : ∀ x y, cutOp ν N y x = cutOp ν N x y := by
    intro x y
    unfold cutOp
    rw [hNsymm]
  -- the centred bound
  have hcen : ∀ f g, ν.expect f = 0 → ν.expect g = 0 →
      |kernelForm ν ν (cutOp ν N) f g| ≤ cI u q r * nrm ν f * nrm ν g := by
    intro f g hf hg
    rw [hT, abs_div, abs_of_pos hD0, hNBE]
    have a1 := hBc f g hf hg
    have a2 := hEν f g
    have hf0 := nrm_nonneg ν f
    have hg0 := nrm_nonneg ν g
    have hc00 := c0_nonneg hq0 hq1
    have hco : 0 ≤ (2 * u * r + u ^ 2 * c0 q * q + ε / hm q) := by
      have : 0 ≤ ε / hm q := div_nonneg hε0 hhm.le
      have : 0 ≤ u ^ 2 * c0 q * q := by positivity
      have : 0 ≤ 2 * u * r := by positivity
      linarith
    have hnum : |kernelForm ν ν B f g + kernelForm ν ν E f g| ≤
        (2 * u * r + u ^ 2 * c0 q * q + ε / hm q) * nrm ν f * nrm ν g := by
      have := abs_add_le (kernelForm ν ν B f g) (kernelForm ν ν E f g)
      have e : (2 * u * r + u ^ 2 * c0 q * q + ε / hm q) * nrm ν f * nrm ν g =
          (2 * u * r + u ^ 2 * c0 q * q) * nrm ν f * nrm ν g + ε / hm q * nrm ν f * nrm ν g := by
        ring
      linarith
    have hX0 : 0 ≤ (2 * u * r + u ^ 2 * c0 q * q + ε / hm q) * nrm ν f * nrm ν g := by positivity
    calc |kernelForm ν ν B f g + kernelForm ν ν E f g| / D
        ≤ (2 * u * r + u ^ 2 * c0 q * q + ε / hm q) * nrm ν f * nrm ν g / D := by gcongr
      _ ≤ (2 * u * r + u ^ 2 * c0 q * q + ε / hm q) * nrm ν f * nrm ν g /
            (zI u q r * Zm q r) := div_le_div_of_nonneg_left hX0 hzZ hmass
      _ = cI u q r * nrm ν f * nrm ν g := by
          unfold cI
          rw [← hε]
          field_simp
  -- the row
  have hrowT : ∀ f, ν.expect f = 0 →
      |kernelForm ν ν (cutOp ν N) f (fun _ => 1)| ≤ q * AI u q r * nrm ν f := by
    intro f hf
    rw [hT, abs_div, abs_of_pos hD0]
    have a1 := hrow f hf
    have hf0 := nrm_nonneg ν f
    have hb6 := bF_ge_six hq0 hq1 hr.le
    have hco : 0 ≤ q * ((CU u q r + Cin u q r + 910 * u ^ 2 + 2 * (1 + u ^ 2) * bF q r / hm q) /
        hm q) := by
      have := CU_nonneg hu hq0 hq1 hr.le
      have := Cin_nonneg hu hq0 hr.le
      have : 0 ≤ 2 * (1 + u ^ 2) * bF q r / hm q := div_nonneg (by positivity) hhm.le
      have : 0 ≤ CU u q r + Cin u q r + 910 * u ^ 2 + 2 * (1 + u ^ 2) * bF q r / hm q := by
        positivity
      positivity
    have hX0 : 0 ≤ q * ((CU u q r + Cin u q r + 910 * u ^ 2 + 2 * (1 + u ^ 2) * bF q r / hm q) /
        hm q) * nrm ν f := mul_nonneg hco hf0
    calc |kernelForm ν ν N f (fun _ => 1)| / D
        ≤ q * ((CU u q r + Cin u q r + 910 * u ^ 2 + 2 * (1 + u ^ 2) * bF q r / hm q) / hm q) *
            nrm ν f / D := by gcongr
      _ ≤ q * ((CU u q r + Cin u q r + 910 * u ^ 2 + 2 * (1 + u ^ 2) * bF q r / hm q) / hm q) *
            nrm ν f / (zI u q r * Zm q r) := div_le_div_of_nonneg_left hX0 hzZ hmass
      _ = q * AI u q r * nrm ν f := by
          unfold AI
          field_simp
  -- the lower bound
  have hlow : ∀ f, -(gI u q r * r) * nrm ν f ^ 2 ≤ kernelForm ν ν (cutOp ν N) f f := by
    intro f
    rw [hT, hNBE]
    have a1 := hB f
    have a2 := hEν f f
    have a3 := neg_abs_le (kernelForm ν ν E f f)
    have hf0 := nrm_nonneg ν f
    set X0 := ε / hm q * nrm ν f ^ 2 with hX0
    have hX00 : 0 ≤ X0 := by
      have : 0 ≤ ε / hm q := div_nonneg hε0 hhm.le
      positivity
    have hnum : -X0 ≤ kernelForm ν ν B f f + kernelForm ν ν E f f := by
      have e : ε / hm q * nrm ν f * nrm ν f = X0 := by rw [hX0]; ring
      linarith
    have h1 : -X0 / D ≤ (kernelForm ν ν B f f + kernelForm ν ν E f f) / D :=
      div_le_div_of_nonneg_right hnum hD0.le
    have h2 : X0 / D ≤ X0 / (zI u q r * Zm q r) := div_le_div_of_nonneg_left hX00 hzZ hmass
    have e2 : -(gI u q r * r) * nrm ν f ^ 2 = -(X0 / (zI u q r * Zm q r)) := by
      rw [hX0]
      unfold gI
      rw [← hε]
      field_simp
    rw [e2]
    have e3 : -X0 / D = -(X0 / D) := by ring
    linarith
  -- the upper bound, by `prop:matching:positive`(a)
  have hup : ∀ f, kernelForm ν ν (cutOp ν N) f f ≤ (1 + cPlusI u q r * q) * nrm ν f ^ 2 := by
    intro f
    have h11 : kernelForm ν ν (cutOp ν N) (fun _ => 1) (fun _ => 1) = 1 := by
      rw [← kmass_eq_kernelForm]
      exact hmass1
    have h := envelope_upper ν (kernelForm ν ν (cutOp ν N))
      (fun f g => kernelForm_symm ν (cutOp ν N) hsymm f g) h11 hc
      (fun f hf => hrowT f hf)
      (fun f hf => by
        have := hcen f f hf hf
        have e : cI u q r * nrm ν f * nrm ν f = cI u q r * nrm ν f ^ 2 := by ring
        rw [e] at this
        exact le_trans (le_abs_self _) this) f
    have e : 1 + (q * AI u q r) ^ 2 / (1 - cI u q r) = 1 + cPlusI u q r * q := by
      unfold cPlusI
      ring
    rw [e] at h
    exact h
  exact ⟨hmass1, hsymm, hlow, hup, hrowT, hcen⟩

/-- **`prop:root-layer` at `p ≥ 2³⁰`**: `root_layer_caps` with `q = 1/p`, `r = p^{-1/2}`, where the
gates `Z_- > 0` and `h_- > 0` are proved (`Zm_pos`, `hm_pos`); the gates `z^ι_u > 0` and
`c^ι_u < 1` remain (as in the paper's statement). -/
theorem root_layer_caps_of_ge (lam : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lam I)
    (ν : FiniteLaw X) (hν : ν = condLaw lam I hP) {u p : ℝ} (hu : 0 ≤ u) (hp : 2 ^ 30 ≤ p)
    (hPh : hm (1 / p) ≤ prob lam I)
    (hz : 0 < zI u (1 / p) (1 / Real.sqrt p)) (hc : cI u (1 / p) (1 / Real.sqrt p) < 1)
    (N B E₁ E₂ Enn Esc Ecr : X → X → ℝ)
    (hNdec : ∀ x y, N x y = B x y + (E₁ x y + E₂ x y + Enn x y - Esc x y - Ecr x y))
    (hNsymm : ∀ x y, N y x = N x y)
    (hB : ∀ f, 0 ≤ kernelForm ν ν B f f)
    (hBc : ∀ f g, ν.expect f = 0 → ν.expect g = 0 →
      |kernelForm ν ν B f g| ≤ (2 * u * (1 / Real.sqrt p) + u ^ 2 * c0 (1 / p) * (1 / p)) *
        nrm ν f * nrm ν g)
    (hE₁ : ∀ f g, |kernelForm lam lam E₁ f g| ≤
      nF (1 / p) (1 / Real.sqrt p) * mU u (1 / Real.sqrt p) * nrm lam f * nrm lam g)
    (hE₂ : ∀ f g, |kernelForm lam lam E₂ f g| ≤
      nF (1 / p) (1 / Real.sqrt p) * mU u (1 / Real.sqrt p) * nrm lam f * nrm lam g)
    (hEnn : ∀ f g, |kernelForm lam lam Enn f g| ≤
      Cnn u (1 / Real.sqrt p) * (1 / p) * nrm lam f * nrm lam g)
    (hEsc : ∀ f g, |kernelForm lam lam Esc f g| ≤
      Csc u (1 / p) (1 / Real.sqrt p) * (1 / p) * nrm lam f * nrm lam g)
    (hEcr : ∀ f g, |kernelForm lam lam Ecr f g| ≤
      Ccr u (1 / p) (1 / Real.sqrt p) * (1 / p) * nrm lam f * nrm lam g)
    (hrow : ∀ f, ν.expect f = 0 → |kernelForm ν ν N f (fun _ => 1)| ≤
      1 / p * ((CU u (1 / p) (1 / Real.sqrt p) + Cin u (1 / p) (1 / Real.sqrt p) + 910 * u ^ 2 +
        2 * (1 + u ^ 2) * bF (1 / p) (1 / Real.sqrt p) / hm (1 / p)) / hm (1 / p)) * nrm ν f)
    (hmass : zI u (1 / p) (1 / Real.sqrt p) * Zm (1 / p) (1 / Real.sqrt p) ≤ kmass ν N) :
    kmass ν (cutOp ν N) = 1 ∧ (∀ x y, cutOp ν N y x = cutOp ν N x y) ∧
    (∀ f, -(gI u (1 / p) (1 / Real.sqrt p) * (1 / Real.sqrt p)) * nrm ν f ^ 2 ≤
      kernelForm ν ν (cutOp ν N) f f) ∧
    (∀ f, kernelForm ν ν (cutOp ν N) f f ≤
      (1 + cPlusI u (1 / p) (1 / Real.sqrt p) * (1 / p)) * nrm ν f ^ 2) ∧
    (∀ f, ν.expect f = 0 → |kernelForm ν ν (cutOp ν N) f (fun _ => 1)| ≤
      1 / p * AI u (1 / p) (1 / Real.sqrt p) * nrm ν f) ∧
    (∀ f g, ν.expect f = 0 → ν.expect g = 0 →
      |kernelForm ν ν (cutOp ν N) f g| ≤ cI u (1 / p) (1 / Real.sqrt p) * nrm ν f * nrm ν g) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := qr_of_ge hp
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hr : 0 < 1 / Real.sqrt p := by
    have := Real.sqrt_pos.mpr hp0
    positivity
  exact root_layer_caps lam I hP ν hν hu h1 (lt_of_le_of_lt h2 (by norm_num)) hr (hm_pos h2) hPh
    (Zm_pos h1 h2 h3 h4) hz hc N B E₁ E₂ Enn Esc Ecr hNdec hNsymm hB hBc hE₁ hE₂ hEnn hEsc hEcr
    hrow hmass

/-- **`prop:root-layer` at `p ≥ 2³⁰` and `0 ≤ u ≤ 1`, with every gate proved**: the gates
`z^ι_u > 0` and `c^ι_u < 1` follow from `zI_pos` and `cI_lt_one` (all six individual-square
parameters of `def:positive-root` lie in `[0, 1]`). -/
theorem root_layer_caps_of_ge_le_one (lam : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lam I)
    (ν : FiniteLaw X) (hν : ν = condLaw lam I hP) {u p : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hp : 2 ^ 30 ≤ p) (hPh : hm (1 / p) ≤ prob lam I)
    (N B E₁ E₂ Enn Esc Ecr : X → X → ℝ)
    (hNdec : ∀ x y, N x y = B x y + (E₁ x y + E₂ x y + Enn x y - Esc x y - Ecr x y))
    (hNsymm : ∀ x y, N y x = N x y)
    (hB : ∀ f, 0 ≤ kernelForm ν ν B f f)
    (hBc : ∀ f g, ν.expect f = 0 → ν.expect g = 0 →
      |kernelForm ν ν B f g| ≤ (2 * u * (1 / Real.sqrt p) + u ^ 2 * c0 (1 / p) * (1 / p)) *
        nrm ν f * nrm ν g)
    (hE₁ : ∀ f g, |kernelForm lam lam E₁ f g| ≤
      nF (1 / p) (1 / Real.sqrt p) * mU u (1 / Real.sqrt p) * nrm lam f * nrm lam g)
    (hE₂ : ∀ f g, |kernelForm lam lam E₂ f g| ≤
      nF (1 / p) (1 / Real.sqrt p) * mU u (1 / Real.sqrt p) * nrm lam f * nrm lam g)
    (hEnn : ∀ f g, |kernelForm lam lam Enn f g| ≤
      Cnn u (1 / Real.sqrt p) * (1 / p) * nrm lam f * nrm lam g)
    (hEsc : ∀ f g, |kernelForm lam lam Esc f g| ≤
      Csc u (1 / p) (1 / Real.sqrt p) * (1 / p) * nrm lam f * nrm lam g)
    (hEcr : ∀ f g, |kernelForm lam lam Ecr f g| ≤
      Ccr u (1 / p) (1 / Real.sqrt p) * (1 / p) * nrm lam f * nrm lam g)
    (hrow : ∀ f, ν.expect f = 0 → |kernelForm ν ν N f (fun _ => 1)| ≤
      1 / p * ((CU u (1 / p) (1 / Real.sqrt p) + Cin u (1 / p) (1 / Real.sqrt p) + 910 * u ^ 2 +
        2 * (1 + u ^ 2) * bF (1 / p) (1 / Real.sqrt p) / hm (1 / p)) / hm (1 / p)) * nrm ν f)
    (hmass : zI u (1 / p) (1 / Real.sqrt p) * Zm (1 / p) (1 / Real.sqrt p) ≤ kmass ν N) :
    kmass ν (cutOp ν N) = 1 ∧ (∀ x y, cutOp ν N y x = cutOp ν N x y) ∧
    (∀ f, -(gI u (1 / p) (1 / Real.sqrt p) * (1 / Real.sqrt p)) * nrm ν f ^ 2 ≤
      kernelForm ν ν (cutOp ν N) f f) ∧
    (∀ f, kernelForm ν ν (cutOp ν N) f f ≤
      (1 + cPlusI u (1 / p) (1 / Real.sqrt p) * (1 / p)) * nrm ν f ^ 2) ∧
    (∀ f, ν.expect f = 0 → |kernelForm ν ν (cutOp ν N) f (fun _ => 1)| ≤
      1 / p * AI u (1 / p) (1 / Real.sqrt p) * nrm ν f) ∧
    (∀ f g, ν.expect f = 0 → ν.expect g = 0 →
      |kernelForm ν ν (cutOp ν N) f g| ≤ cI u (1 / p) (1 / Real.sqrt p) * nrm ν f * nrm ν g) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := qr_of_ge hp
  exact root_layer_caps_of_ge lam I hP ν hν hu hp hPh (zI_pos hu1 h1 h2 h3 h4)
    (cI_lt_one hu hu1 h1 h2 h3 h4) N B E₁ E₂ Enn Esc Ecr hNdec hNsymm hB hBc hE₁ hE₂ hEnn hEsc
    hEcr hrow hmass

/-- **`prop:root-layer`, "The bounds at an endpoint hold for all larger primes with the same
`u`"**: at a prime with `r = p^{-1/2}`, `q = r²`, and an endpoint with `r' = P^{-1/2}`,
`0 < r ≤ r' ≤ 2⁻¹⁵` (i.e. `p ≥ P ≥ 2³⁰`), the conclusions of `root_layer_caps` hold with the
constants `g^ι_u`, `c^{+,ι}_u`, `A^ι_u`, `c^ι_u` evaluated at the endpoint; the gates are needed
only at the endpoint (`gI_uniform`, `cI_uniform`, `AI_uniform`, `cPlusI_uniform`). -/
theorem root_layer_caps_uniform (lam : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lam I)
    (ν : FiniteLaw X) (hν : ν = condLaw lam I hP) {u r r' : ℝ} (hu : 0 ≤ u) (hr : 0 < r)
    (hrr : r ≤ r') (hr' : r' ≤ 1 / 2 ^ 15) (hPh : hm (r ^ 2) ≤ prob lam I)
    (hz' : 0 < zI u (r' ^ 2) r') (hc' : cI u (r' ^ 2) r' < 1)
    (N B E₁ E₂ Enn Esc Ecr : X → X → ℝ)
    (hNdec : ∀ x y, N x y = B x y + (E₁ x y + E₂ x y + Enn x y - Esc x y - Ecr x y))
    (hNsymm : ∀ x y, N y x = N x y)
    (hB : ∀ f, 0 ≤ kernelForm ν ν B f f)
    (hBc : ∀ f g, ν.expect f = 0 → ν.expect g = 0 →
      |kernelForm ν ν B f g| ≤ (2 * u * r + u ^ 2 * c0 (r ^ 2) * r ^ 2) * nrm ν f * nrm ν g)
    (hE₁ : ∀ f g, |kernelForm lam lam E₁ f g| ≤ nF (r ^ 2) r * mU u r * nrm lam f * nrm lam g)
    (hE₂ : ∀ f g, |kernelForm lam lam E₂ f g| ≤ nF (r ^ 2) r * mU u r * nrm lam f * nrm lam g)
    (hEnn : ∀ f g, |kernelForm lam lam Enn f g| ≤ Cnn u r * r ^ 2 * nrm lam f * nrm lam g)
    (hEsc : ∀ f g, |kernelForm lam lam Esc f g| ≤ Csc u (r ^ 2) r * r ^ 2 * nrm lam f * nrm lam g)
    (hEcr : ∀ f g, |kernelForm lam lam Ecr f g| ≤ Ccr u (r ^ 2) r * r ^ 2 * nrm lam f * nrm lam g)
    (hrow : ∀ f, ν.expect f = 0 → |kernelForm ν ν N f (fun _ => 1)| ≤
      r ^ 2 * ((CU u (r ^ 2) r + Cin u (r ^ 2) r + 910 * u ^ 2 +
        2 * (1 + u ^ 2) * bF (r ^ 2) r / hm (r ^ 2)) / hm (r ^ 2)) * nrm ν f)
    (hmass : zI u (r ^ 2) r * Zm (r ^ 2) r ≤ kmass ν N) :
    kmass ν (cutOp ν N) = 1 ∧ (∀ x y, cutOp ν N y x = cutOp ν N x y) ∧
    (∀ f, -(gI u (r' ^ 2) r' * r) * nrm ν f ^ 2 ≤ kernelForm ν ν (cutOp ν N) f f) ∧
    (∀ f, kernelForm ν ν (cutOp ν N) f f ≤ (1 + cPlusI u (r' ^ 2) r' * r ^ 2) * nrm ν f ^ 2) ∧
    (∀ f, ν.expect f = 0 →
      |kernelForm ν ν (cutOp ν N) f (fun _ => 1)| ≤ r ^ 2 * AI u (r' ^ 2) r' * nrm ν f) ∧
    (∀ f g, ν.expect f = 0 → ν.expect g = 0 →
      |kernelForm ν ν (cutOp ν N) f g| ≤ cI u (r' ^ 2) r' * nrm ν f * nrm ν g) := by
  have hq := sq_le_of_le hr.le (le_trans hrr hr')
  have hq1 : r ^ 2 < 1 := lt_of_le_of_lt hq (by norm_num)
  obtain ⟨-, hzle, -, -, -, -⟩ := denoms_anti hu hr.le hrr hr' hz'
  have hz : 0 < zI u (r ^ 2) r := lt_of_lt_of_le hz' hzle
  have hcu := cI_uniform hu hr hrr hr' hz'
  have hc : cI u (r ^ 2) r < 1 := lt_of_le_of_lt hcu hc'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := root_layer_caps lam I hP ν hν hu (sq_nonneg r) hq1 hr
    (hm_pos hq) hPh (Zm_pos (sq_nonneg r) hq hr.le (le_trans hrr hr')) hz hc N B E₁ E₂ Enn Esc Ecr
    hNdec hNsymm hB hBc hE₁ hE₂ hEnn hEsc hEcr hrow hmass
  have hg := gI_uniform hu hr hrr hr' hz'
  have hA := AI_uniform hu hr hrr hr' hz'
  have hcp := cPlusI_uniform hu hr hrr hr' hz' hc'
  refine ⟨h1, h2, fun f => ?_, fun f => ?_, fun f hf => ?_, fun f g hf hg' => ?_⟩
  · have := h3 f
    have h0 : 0 ≤ nrm ν f ^ 2 := sq_nonneg _
    have : gI u (r ^ 2) r * r * nrm ν f ^ 2 ≤ gI u (r' ^ 2) r' * r * nrm ν f ^ 2 := by
      gcongr
    linarith
  · have := h4 f
    have h0 : 0 ≤ nrm ν f ^ 2 := sq_nonneg _
    have : (1 + cPlusI u (r ^ 2) r * r ^ 2) * nrm ν f ^ 2 ≤
        (1 + cPlusI u (r' ^ 2) r' * r ^ 2) * nrm ν f ^ 2 := by gcongr
    linarith
  · have := h5 f hf
    have h0 := nrm_nonneg ν f
    have : r ^ 2 * AI u (r ^ 2) r * nrm ν f ≤ r ^ 2 * AI u (r' ^ 2) r' * nrm ν f := by gcongr
    linarith
  · have := h6 f g hf hg'
    have h0 := nrm_nonneg ν f
    have h0' := nrm_nonneg ν g
    have : cI u (r ^ 2) r * nrm ν f * nrm ν g ≤ cI u (r' ^ 2) r' * nrm ν f * nrm ν g := by gcongr
    linarith

/-! ## Non-vacuity -/

/-- The uniform law on `Bool`. -/
noncomputable def boolLaw : FiniteLaw Bool where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  total := by
    rw [Fintype.sum_bool]
    norm_num

theorem prob_true_boolLaw : prob boolLaw (fun _ => True) = 1 := by
  unfold prob
  have : ind (fun _ : Bool => True) = fun _ => 1 := funext fun _ => ind_of_pos trivial
  rw [this, FiniteLaw.expect_const]

theorem kernelForm_const_one (ν : FiniteLaw X) (f g : X → ℝ) :
    kernelForm ν ν (fun _ _ => (1 : ℝ)) f g = ν.expect f * ν.expect g := by
  rw [kernelForm_apply]
  have : ∀ x, f x * ν.expect (fun y => 1 * g y) = f x * ν.expect g := by
    intro x
    congr 1
    exact ν.expect_congr (fun y => one_mul (g y))
  rw [ν.expect_congr this, FiniteLaw.expect_mul_const]

theorem kernelForm_zero_kernel (ν : FiniteLaw X) (f g : X → ℝ) :
    kernelForm ν ν (fun _ _ => (0 : ℝ)) f g = 0 := by
  simp only [kernelForm, LinearMap.mk₂_apply, mul_zero, zero_mul, Finset.sum_const_zero]

/-- **Non-vacuity of `root_layer_caps`** (rule 9): all its hypotheses hold together for the
uniform law on `Bool` (`I` the sure event, so `ν = lam`), the constant kernel `N = B = 1`, zero
error kernels, `u = 0`, `q = 2⁻³⁰`, `r = 2⁻¹⁵`; the gates come from `zI_pos`, `cI_lt_one`,
`Zm_pos`, `hm_pos`. The conclusion recorded is the mass identity `⟨1, T1⟩ = 1`. -/
theorem root_layer_caps_nonvacuous :
    kmass (condLaw boolLaw (fun _ => True) (by rw [prob_true_boolLaw]; norm_num))
      (cutOp (condLaw boolLaw (fun _ => True) (by rw [prob_true_boolLaw]; norm_num))
        (fun _ _ => 1)) = 1 := by
  have hP : 0 < prob boolLaw (fun _ => True) := by rw [prob_true_boolLaw]; norm_num
  set ν := condLaw boolLaw (fun _ => True) hP with hν
  have hq0 : (0 : ℝ) ≤ 1 / 2 ^ 30 := by norm_num
  have hq : (1 : ℝ) / 2 ^ 30 ≤ 1 / 2 ^ 30 := le_rfl
  have hr0 : (0 : ℝ) ≤ 1 / 2 ^ 15 := by norm_num
  have hr : (1 : ℝ) / 2 ^ 15 ≤ 1 / 2 ^ 15 := le_rfl
  have hq1 : (1 : ℝ) / 2 ^ 30 < 1 := by norm_num
  have hnF := nF_nonneg hq0 hq1 hr0
  have hmU : 0 ≤ mU 0 (1 / 2 ^ 15) := by unfold mU; norm_num
  have hFU := FU_nonneg (le_refl (0 : ℝ)) hr0
  have hCU := CU_nonneg (le_refl (0 : ℝ)) hq0 hq1 hr0
  have hCin := Cin_nonneg (le_refl (0 : ℝ)) hq0 hr0
  have hM := MPhi_nonneg hq0 hq1
  have hd := dMu_nonneg hq0 hq1
  have hb6 := bF_ge_six hq0 hq1 hr0
  have hhm := hm_pos hq
  have zero_bd : ∀ (c : ℝ), 0 ≤ c → ∀ (μ : FiniteLaw Bool) (f g : Bool → ℝ),
      |kernelForm μ μ (fun _ _ => (0 : ℝ)) f g| ≤ c * nrm μ f * nrm μ g := by
    intro c hc μ f g
    rw [kernelForm_zero_kernel, abs_zero]
    have := nrm_nonneg μ f
    have := nrm_nonneg μ g
    positivity
  have h := root_layer_caps boolLaw (fun _ => True) hP ν hν (u := 0) (q := 1 / 2 ^ 30)
    (r := 1 / 2 ^ 15) le_rfl hq0 hq1 (by norm_num) hhm
    (by rw [prob_true_boolLaw]; unfold hm; norm_num) (Zm_pos hq0 hq hr0 hr)
    (zI_pos (by norm_num) hq0 hq hr0 hr) (cI_lt_one le_rfl (by norm_num) hq0 hq hr0 hr)
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ => by norm_num) (fun _ _ => rfl)
    (fun f => by rw [kernelForm_const_one]; exact mul_self_nonneg _)
    (fun f g hf _ => by
      rw [kernelForm_const_one, hf, zero_mul, abs_zero]
      have := nrm_nonneg ν f
      have := nrm_nonneg ν g
      have : 0 ≤ c0 (1 / 2 ^ 30) := c0_nonneg hq0 hq1
      positivity)
    (fun f g => zero_bd _ (mul_nonneg hnF hmU) boolLaw f g)
    (fun f g => zero_bd _ (mul_nonneg hnF hmU) boolLaw f g)
    (fun f g => zero_bd _ (by unfold Cnn; positivity) boolLaw f g)
    (fun f g => zero_bd _ (by unfold Csc; positivity) boolLaw f g)
    (fun f g => zero_bd _ (by unfold Ccr; positivity) boolLaw f g)
    (fun f hf => by
      rw [kernelForm_const_one, hf, zero_mul, abs_zero]
      have := nrm_nonneg ν f
      have : 0 ≤ 2 * (1 + (0 : ℝ) ^ 2) * bF (1 / 2 ^ 30) (1 / 2 ^ 15) / hm (1 / 2 ^ 30) :=
        div_nonneg (by positivity) hhm.le
      positivity)
    (by
      rw [kmass_eq_kernelForm, kernelForm_const_one, FiniteLaw.expect_const, one_mul]
      have hz := zI_ge (u := 0) (by norm_num) hq0 hq hr0 hr
      have hzle : zI 0 (1 / 2 ^ 30) (1 / 2 ^ 15) ≤ 1 := by
        have := h0_le hq0 hq hr0 hr
        unfold zI
        have : 0 ≤ h0 (1 / 2 ^ 30) (1 / 2 ^ 15) := by unfold h0; norm_num
        nlinarith
      have hZle : Zm (1 / 2 ^ 30) (1 / 2 ^ 15) ≤ 1 := by
        have hb := bF_lt hq0 hq hr
        unfold Zm
        have hbq0 : 0 ≤ bF (1 / 2 ^ 30) (1 / 2 ^ 15) * (1 / 2 ^ 30) := by positivity
        have hbq1 : bF (1 / 2 ^ 30) (1 / 2 ^ 15) * (1 / 2 ^ 30) ≤ 1 := by
          have : bF (1 / 2 ^ 30) (1 / 2 ^ 15) * (1 / 2 ^ 30) ≤ 140004 / 1000 * (1 / 2 ^ 30) :=
            mul_le_mul_of_nonneg_right hb.le (by norm_num)
          linarith [show (140004 / 1000 : ℝ) * (1 / 2 ^ 30) ≤ 1 by norm_num]
        have : 0 ≤ (1 / 2 ^ 30 : ℝ) * (18 * MPhi (1 / 2 ^ 30) ^ 2 + 384 * MPhi (1 / 2 ^ 30) +
            72 * dMu (1 / 2 ^ 30) ^ 2 * (1 + 1 / 2 ^ 30) ^ 5) := by positivity
        nlinarith
      have hz0 : 0 ≤ zI 0 (1 / 2 ^ 30) (1 / 2 ^ 15) := le_trans (by norm_num) hz
      have hZ0 := (Zm_pos hq0 hq hr0 hr).le
      calc zI 0 (1 / 2 ^ 30) (1 / 2 ^ 15) * Zm (1 / 2 ^ 30) (1 / 2 ^ 15) ≤ 1 * 1 :=
            mul_le_mul hzle hZle hZ0 (by norm_num)
        _ = 1 := by norm_num)
  exact h.1

/-! ## The mass step -/

section Mass

variable {Ω : Type*} [Fintype Ω]

theorem expect_one_add_sq (Γ : FiniteLaw Ω) (u : ℝ) (H : Ω → ℝ) :
    Γ.expect (fun x => (1 + u * H x) ^ 2) =
      1 + 2 * u * Γ.expect H + u ^ 2 * Γ.expect (fun x => H x ^ 2) := by
  have e : (fun x => (1 + u * H x) ^ 2) =
      fun x => (fun _ => (1 : ℝ)) x +
        ((fun y => (2 * u) * H y) x + (fun y => u ^ 2 * H y ^ 2) x) := by
    funext x
    ring
  rw [e, FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_const,
    FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul]
  ring

/-- **The mass step of `prop:root-layer`**, abstractly: for three scores with `|E H_j| ≤ h` and
`E H_j² ≥ s` and `u ≥ 0`, `E[(1/3) ∑_j (1 + uH_j)²] ≥ 1 - 2uh + u²s`. -/
theorem tilt_mass_ge_abstract (Γ : FiniteLaw Ω) (H : Fin 3 → Ω → ℝ) {u h s : ℝ} (hu : 0 ≤ u)
    (hh : ∀ j, |Γ.expect (H j)| ≤ h) (hs : ∀ j, s ≤ Γ.expect (fun x => H j x ^ 2)) :
    1 - 2 * u * h + u ^ 2 * s ≤ Γ.expect (fun x => (1 / 3) * ∑ j, (1 + u * H j x) ^ 2) := by
  have e : Γ.expect (fun x => (1 / 3) * ∑ j, (1 + u * H j x) ^ 2) =
      (1 / 3) * ∑ j, Γ.expect (fun x => (1 + u * H j x) ^ 2) := by
    rw [FiniteLaw.expect_const_mul]
    congr 1
    unfold FiniteLaw.expect
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  rw [e]
  have hj : ∀ j, 1 - 2 * u * h + u ^ 2 * s ≤ Γ.expect (fun x => (1 + u * H j x) ^ 2) := by
    intro j
    rw [expect_one_add_sq]
    have a1 := hh j
    have a2 := hs j
    have a3 := neg_abs_le (Γ.expect (H j))
    have t1 : -(2 * u * h) ≤ 2 * u * Γ.expect (H j) := by
      have := mul_le_mul_of_nonneg_left (show -h ≤ Γ.expect (H j) by linarith)
        (by linarith : (0 : ℝ) ≤ 2 * u)
      linarith
    have t2 : u ^ 2 * s ≤ u ^ 2 * Γ.expect (fun x => H j x ^ 2) :=
      mul_le_mul_of_nonneg_left a2 (sq_nonneg u)
    linarith
  rw [Fin.sum_univ_three]
  have := hj 0
  have := hj 1
  have := hj 2
  linarith

/-- **The mass step of `prop:root-layer`** ("Mass"), for the individual-square weight
`w_u = (1/3) ∑_j (1 + u H_j)²` of V1 (`PartV.individualWeight`) and any law `Γ` on the twelve-label
labellings (in the paper `Γ = Γ_{p,0} = λ_p(G_{L,2})`): if `|E_Γ H_j| ≤ h_0` and
`E_Γ H_j² ≥ 1 - 4q - 36qB_H² - 2q/(1 - q)` (`lem:root-normalization`(b), hypotheses), then
`E_Γ w_u ≥ z^ι_u`. -/
theorem tilt_mass_ge_zI {p : ℕ} [Fact p.Prime] (Γ : FiniteLaw (ZMod 6 × Fin 2 → ZMod p)) (u : ℚ)
    (hu : 0 ≤ u) {q r : ℝ}
    (hh : ∀ j, |Γ.expect (PartV.rootScore p j)| ≤ h0 q r)
    (hs : ∀ j, 1 - 4 * q - 36 * q * BH r ^ 2 - 2 * q / (1 - q) ≤
      Γ.expect (fun x => PartV.rootScore p j x ^ 2)) :
    zI (u : ℝ) q r ≤ Γ.expect (PartV.individualWeight p u) := by
  have h := tilt_mass_ge_abstract Γ (fun j => PartV.rootScore p j) (u := (u : ℝ))
    (by exact_mod_cast hu) hh hs
  have e : zI (u : ℝ) q r = 1 - 2 * (u : ℝ) * h0 q r +
      (u : ℝ) ^ 2 * (1 - 4 * q - 36 * q * BH r ^ 2 - 2 * q / (1 - q)) := by
    unfold zI
    ring
  rw [e]
  exact h

/-- **The mass step, the raw mass** ("Mass"): if the raw mass factors as `Z₀ · W` (the raw mass
`Z₀ ≥ Z_-` of the uniform root, (L4), times the tilt mass `W = E_{Γ_{p,0}} w_u ≥ z^ι_u`), then
`⟨1, N1⟩ ≥ z^ι_u Z_-`. -/
theorem raw_mass_ge {D Z₀ W z Z : ℝ} (hD : D = Z₀ * W) (hZ : Z ≤ Z₀) (hW : z ≤ W) (hz : 0 ≤ z)
    (hZ0 : 0 ≤ Z) : z * Z ≤ D := by
  rw [hD]
  calc z * Z ≤ W * Z₀ := mul_le_mul hW hZ hZ0 (le_trans hz hW)
    _ = Z₀ * W := by ring

end Mass

/-! ## `lem:native-pair-linear`: the arithmetic -/

/-- **`lem:native-pair-linear`, the sum of the prices**: with `q = r²`, `‖S‖ ≤ s = κ(1 + 5r)r + 6q`
and `‖R‖ ≤ eq`, the one-sided terms `2r s + 2r eq`, the `144` terms of `S ⊗ S` at `16q`, and the
mixed terms `r^{-1}(2s · eq + (eq)²)` sum to exactly `C_pair q`. -/
theorem native_pair_sum {r e : ℝ} (hr : r ≠ 0) :
    2 * (r * (kappa * (1 + 5 * r) * r + 6 * r ^ 2)) + 2 * (r * (e * r ^ 2)) + 144 * (16 * r ^ 2) +
      (2 * ((kappa * (1 + 5 * r) * r + 6 * r ^ 2) * (e * r ^ 2)) + (e * r ^ 2) ^ 2) / r =
    (2304 + 2 * kappa * (1 + 5 * r) * (1 + e) + r * (12 + 14 * e + e ^ 2)) * r ^ 2 := by
  field_simp
  ring

/-- **`lem:native-pair-linear`** (the assembly). On a finite law `lam` (the two independent cyclic
triangles), let the form of `K ∘ 𝖧 - 𝖧` (`K = Φ ⊗ Φ`) split into the eight classes of the proof:
`S ⊗ J`, `J ⊗ S`, `R ⊗ J`, `J ⊗ R` (`one`: each of norm `≤ r` times `‖S‖ ≤ s` or `‖R‖ ≤ eq`, the
sandwich `(A ⊗ J) ∘ 𝖧 = r^{-1}V(A ⊗ I)V^*` with `‖V‖ ≤ r`), the `144` terms of `S ⊗ S` (`ss`, at
`16q` each), and `S ⊗ R`, `R ⊗ S`, `R ⊗ R` (`mixed`, Schur multiplier norm `≤ r^{-1}`). These
class prices are hypotheses. Then `‖K ∘ 𝖧 - 𝖧‖ ≤ C_pair q`, with `q = r²`, `e = 𝔟 - 6`. -/
theorem native_pair_linear (lam : FiniteLaw X) {q r : ℝ} (hr : 0 < r) (hq : q = r ^ 2)
    (L : X → X → ℝ) (oS₁ oS₂ oR₁ oR₂ ss mSR mRS mRR : X → X → ℝ)
    (hL : ∀ f g, kernelForm lam lam L f g =
      kernelForm lam lam oS₁ f g + kernelForm lam lam oS₂ f g + kernelForm lam lam oR₁ f g +
        kernelForm lam lam oR₂ f g + kernelForm lam lam ss f g + kernelForm lam lam mSR f g +
        kernelForm lam lam mRS f g + kernelForm lam lam mRR f g)
    (hoS₁ : ∀ f g, |kernelForm lam lam oS₁ f g| ≤
      r * (kappa * (1 + 5 * r) * r + 6 * q) * nrm lam f * nrm lam g)
    (hoS₂ : ∀ f g, |kernelForm lam lam oS₂ f g| ≤
      r * (kappa * (1 + 5 * r) * r + 6 * q) * nrm lam f * nrm lam g)
    (hoR₁ : ∀ f g, |kernelForm lam lam oR₁ f g| ≤ r * (eF q r * q) * nrm lam f * nrm lam g)
    (hoR₂ : ∀ f g, |kernelForm lam lam oR₂ f g| ≤ r * (eF q r * q) * nrm lam f * nrm lam g)
    (hss : ∀ f g, |kernelForm lam lam ss f g| ≤ 144 * (16 * q) * nrm lam f * nrm lam g)
    (hmSR : ∀ f g, |kernelForm lam lam mSR f g| ≤
      (kappa * (1 + 5 * r) * r + 6 * q) * (eF q r * q) / r * nrm lam f * nrm lam g)
    (hmRS : ∀ f g, |kernelForm lam lam mRS f g| ≤
      (kappa * (1 + 5 * r) * r + 6 * q) * (eF q r * q) / r * nrm lam f * nrm lam g)
    (hmRR : ∀ f g, |kernelForm lam lam mRR f g| ≤ (eF q r * q) ^ 2 / r * nrm lam f * nrm lam g)
    (f g : X → ℝ) :
    |kernelForm lam lam L f g| ≤ Cpair q r * q * nrm lam f * nrm lam g := by
  rw [hL]
  have a1 := hoS₁ f g
  have a2 := hoS₂ f g
  have a3 := hoR₁ f g
  have a4 := hoR₂ f g
  have a5 := hss f g
  have a6 := hmSR f g
  have a7 := hmRS f g
  have a8 := hmRR f g
  have hsum : Cpair q r * q * nrm lam f * nrm lam g =
      r * (kappa * (1 + 5 * r) * r + 6 * q) * nrm lam f * nrm lam g +
      r * (kappa * (1 + 5 * r) * r + 6 * q) * nrm lam f * nrm lam g +
      r * (eF q r * q) * nrm lam f * nrm lam g + r * (eF q r * q) * nrm lam f * nrm lam g +
      144 * (16 * q) * nrm lam f * nrm lam g +
      (kappa * (1 + 5 * r) * r + 6 * q) * (eF q r * q) / r * nrm lam f * nrm lam g +
      (kappa * (1 + 5 * r) * r + 6 * q) * (eF q r * q) / r * nrm lam f * nrm lam g +
      (eF q r * q) ^ 2 / r * nrm lam f * nrm lam g := by
    subst hq
    have key := native_pair_sum (e := eF (r ^ 2) r) hr.ne'
    have e2 : Cpair (r ^ 2) r * r ^ 2 =
        2 * (r * (kappa * (1 + 5 * r) * r + 6 * r ^ 2)) + 2 * (r * (eF (r ^ 2) r * r ^ 2)) +
          144 * (16 * r ^ 2) + (2 * ((kappa * (1 + 5 * r) * r + 6 * r ^ 2) *
            (eF (r ^ 2) r * r ^ 2)) + (eF (r ^ 2) r * r ^ 2) ^ 2) / r := by
      rw [key]
      unfold Cpair
      ring
    rw [e2]
    ring
  rw [hsum]
  calc _ ≤ |kernelForm lam lam oS₁ f g| + |kernelForm lam lam oS₂ f g| +
        |kernelForm lam lam oR₁ f g| + |kernelForm lam lam oR₂ f g| +
        |kernelForm lam lam ss f g| + |kernelForm lam lam mSR f g| +
        |kernelForm lam lam mRS f g| + |kernelForm lam lam mRR f g| := by
        refine le_trans (abs_add_le _ _) ?_
        refine add_le_add (le_trans (abs_add_le _ _) ?_) le_rfl
        refine add_le_add (le_trans (abs_add_le _ _) ?_) le_rfl
        refine add_le_add (le_trans (abs_add_le _ _) ?_) le_rfl
        refine add_le_add (le_trans (abs_add_le _ _) ?_) le_rfl
        refine add_le_add (le_trans (abs_add_le _ _) ?_) le_rfl
        exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith

/-- **`lem:native-pair-linear`, the restriction**: on the actual six-distinct half
`ν = lam(· | I)`, with `P(I) ≥ 1 - 9q > 0`, a soft bound `‖L‖ ≤ C` becomes `‖L_ν‖ ≤ C/(1 - 9q)`
(`lem:restriction`(b)). -/
theorem native_pair_linear_restrict (lam : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lam I)
    {q C : ℝ} (hC : 0 ≤ C) (hh : 0 < 1 - 9 * q) (hPh : 1 - 9 * q ≤ prob lam I) (L : X → X → ℝ)
    (hL : ∀ f g, |kernelForm lam lam L f g| ≤ C * nrm lam f * nrm lam g) (f g : X → ℝ) :
    |kernelForm (condLaw lam I hP) (condLaw lam I hP) L f g| ≤
      C / (1 - 9 * q) * nrm (condLaw lam I hP) f * nrm (condLaw lam I hP) g := by
  have h := restriction_full lam lam I I hP hP L hL f g
  rw [Real.sqrt_mul_self hP.le] at h
  have hle : C / prob lam I ≤ C / (1 - 9 * q) := div_le_div_of_nonneg_left hC hh hPh
  have hf0 := nrm_nonneg (condLaw lam I hP) f
  have hg0 := nrm_nonneg (condLaw lam I hP) g
  calc _ ≤ C / prob lam I * nrm (condLaw lam I hP) f * nrm (condLaw lam I hP) g := h
    _ ≤ _ := by gcongr

end Layer

end Sarkozy.PositiveRoots
