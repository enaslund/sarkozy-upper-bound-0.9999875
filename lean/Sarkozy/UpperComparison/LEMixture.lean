module

public import Sarkozy.UpperComparison.DenseLaws

@[expose] public section

/-!
# Replacing an LE record by a positive mixture of four dense laws (`prop:le-mixture`)

`paper/sections/26_upper_comparison.tex`, paragraph "The LE mixture", `prop:le-mixture`.

**Framework.** As in `Sarkozy/UpperComparison/ForestRecords.lean`: `ν = μ = λ_H` is a `FiniteLaw X`,
kernels are relative to `ν ⊗ ν`, operators are bilinear forms, and the old actual half marginal is
`m₀ = (1 + u₀)μ`. The components are indexed by any finite type `ι` (the paper: `j = 0, …, 3`), with
weights `w_j ≥ 0`, `∑ w_j = 1` (the paper's vectors I and II).

**Inputs taken as hypotheses.**
* `prop:dense-comparison`(a) for each component: the repaired components `K_j'` are nonnegative
  couplings of `m₀` with itself (both half marginals `m₀`); acceptance and invariance of each
  component, as predicates on its support (`dense_accepts_required` gives the acceptance of a
  softening).
* The proof of `prop:dense-comparison`(b) for each component, in one synthesis over the union of all
  supports: on centred functions the centred change of component `j` is `Lead_j + Rem_j`, with
  `Lead_j = r 𝓕 M_j(Φ̂) 𝓕^*` and `‖Rem_j‖ ≤ E_j` (`le_component_change` proves this decomposition
  from the inputs of `dense_comparison_b`, with the paper's `E_j`).
* `cor:star-matrix` for the mixed matrix `M = ∑_j w_j M_j`: `‖Sym M(i)‖ ≤ k_s`, `‖Skew M(i)‖ ≤ k_a`,
  that is, `‖Sym ∑_j w_j Lead_j‖ ≤ Γ k_s r` and `‖Skew ∑_j w_j Lead_j‖ ≤ Γ k_a r`.

**Proved.**
* **`le_mixture_law`**: `K = ∑_j w_j K_j'` is a nonnegative probability coupling of `m₀` with
  itself; `le_mixture_accepts` and `le_mixture_invariant`: it accepts, and is invariant, when every
  component is (a convex combination of such couplings is one).
* **`le_mixture_change`**: relative to `m₀`, the change `K - K₀` has symmetric and skew parts of
  norms at most `d_s = e^{ℓ₀}(Γ k_s r + E)` and `d_a = e^{ℓ₀}(Γ k_a r + E)`, `E = ∑_j w_j E_j`. The
  rank-one terms of the actual centring cancel because every component has the marginals `m₀`, and
  the transport to `L²(m₀)` costs `e^{ℓ₀}` (`Structured.kform_transport`).
* **`le_component_change`**: the decomposition of one component's change with
  `E_j = ∑_h (ℛ_{j,h} + ε_{j,h} C_{j,h}) + 2F_j(C_{j,1} + u_j)` (`leCompE`, `leCompE_nonneg`).
* **`le_mixture_of_components`**: the two combined, so that the proposition takes, for each
  component, the inputs of `prop:dense-comparison`, and `cor:star-matrix` for the mixed matrix.
* `leMixtureC0`, and the block gates are `DenseBlockGates` with `c₀ = ∑_j w_j c_{0,j}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperComparison

open Sarkozy.Recentering Sarkozy.Structured

variable {X : Type*} [Fintype X] {ι : Type*} [Fintype ι]

/-- `E_ν ∑_j w_j F_j = ∑_j w_j E_ν F_j`. -/
theorem expect_wsum (ν : FiniteLaw X) (w : ι → ℝ) (F : ι → X → ℝ) :
    ν.expect (fun x => ∑ j, w j * F j x) = ∑ j, w j * ν.expect (F j) := by
  unfold FiniteLaw.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => by ring

/-- The form of a weighted sum of kernels. -/
theorem kform_wsum (ν : FiniteLaw X) (w : ι → ℝ) (Y : ι → X × X → ℝ) (φ ψ : X → ℝ) :
    kform ν ν (fun p => ∑ j, w j * Y j p) φ ψ = ∑ j, w j * kform ν ν (Y j) φ ψ := by
  unfold kform
  have h : ∀ x, ν.expect (fun y => φ x * ψ y * ∑ j, w j * Y j (x, y)) =
      ∑ j, w j * ν.expect (fun y => φ x * ψ y * Y j (x, y)) := by
    intro x
    rw [← expect_wsum ν w (fun j y => φ x * ψ y * Y j (x, y))]
    exact ν.expect_congr fun y => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [ν.expect_congr h, expect_wsum ν w (fun j x => ν.expect (fun y => φ x * ψ y * Y j (x, y)))]

/-- The mixture `K = ∑_j w_j K_j'` (`prop:le-mixture`). -/
noncomputable def mixKernel (w : ι → ℝ) (K' : ι → X × X → ℝ) : X × X → ℝ :=
  fun p => ∑ j, w j * K' j p

/-- **`prop:le-mixture`, the law**: a convex combination of nonnegative couplings of `m₀` with
itself is one; it is supported in the union of the supports of the components with positive
weight. -/
theorem le_mixture_law (ν : FiniteLaw X) (w : ι → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (K' : ι → X × X → ℝ) (hK'0 : ∀ j p, 0 ≤ K' j p) (u0 : X → ℝ) (hu00 : ν.expect u0 = 0)
    (hm1 : ∀ j x, ν.expect (fun y => K' j (x, y)) = 1 + u0 x)
    (hm2 : ∀ j y, ν.expect (fun x => K' j (x, y)) = 1 + u0 y) :
    (∀ p, 0 ≤ mixKernel w K' p) ∧
      ν.expect (fun x => ν.expect (fun y => mixKernel w K' (x, y))) = 1 ∧
      (∀ x, ν.expect (fun y => mixKernel w K' (x, y)) = 1 + u0 x) ∧
      (∀ y, ν.expect (fun x => mixKernel w K' (x, y)) = 1 + u0 y) ∧
      ∀ p, mixKernel w K' p ≠ 0 → ∃ j, w j ≠ 0 ∧ K' j p ≠ 0 := by
  have hrow : ∀ x, ν.expect (fun y => mixKernel w K' (x, y)) = 1 + u0 x := by
    intro x
    unfold mixKernel
    rw [expect_wsum ν w (fun j y => K' j (x, y))]
    simp only [hm1]
    rw [← Finset.sum_mul, hw1, one_mul]
  have hcol : ∀ y, ν.expect (fun x => mixKernel w K' (x, y)) = 1 + u0 y := by
    intro y
    unfold mixKernel
    rw [expect_wsum ν w (fun j x => K' j (x, y))]
    simp only [hm2]
    rw [← Finset.sum_mul, hw1, one_mul]
  refine ⟨fun p => Finset.sum_nonneg fun j _ => mul_nonneg (hw0 j) (hK'0 j p), ?_, hrow, hcol, ?_⟩
  · rw [ν.expect_congr hrow, ν.expect_add, ν.expect_const, hu00, add_zero]
  · intro p hp
    by_contra hne
    push Not at hne
    apply hp
    unfold mixKernel
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hw : w j = 0
    · rw [hw, zero_mul]
    · rw [hne j hw, mul_zero]

omit [Fintype X] in
/-- **Acceptance of the mixture**: if every component is supported where a predicate holds (for the
LE components: the six queries `𝓔₆`), so is the mixture. -/
theorem le_mixture_accepts (w : ι → ℝ) (K' : ι → X × X → ℝ) (Acc : X × X → Prop)
    (hacc : ∀ j p, K' j p ≠ 0 → Acc p) (p : X × X) (hp : mixKernel w K' p ≠ 0) : Acc p := by
  by_contra hA
  apply hp
  unfold mixKernel
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases h : K' j p = 0
  · rw [h, mul_zero]
  · exact absurd (hacc j p h) hA

omit [Fintype X] in
/-- **Invariance of the mixture**: a mixture of kernels invariant under a map is invariant. -/
theorem le_mixture_invariant (w : ι → ℝ) (K' : ι → X × X → ℝ) (σ : X × X → X × X)
    (hσ : ∀ j p, K' j (σ p) = K' j p) (p : X × X) : mixKernel w K' (σ p) = mixKernel w K' p := by
  unfold mixKernel
  exact Finset.sum_congr rfl fun j _ => by rw [hσ]

/-- The difference of two centred forms is the form of the difference of the kernels (the
rank-one terms of the centring cancel for laws with the same half marginals). -/
theorem centredForm_sub (ν : FiniteLaw X) (u0 : X → ℝ) (K O : X × X → ℝ) (φ ψ : X → ℝ) :
    centredForm ν u0 K φ ψ - centredForm ν u0 O φ ψ = kform ν ν (fun p => K p - O p) φ ψ := by
  unfold centredForm
  rw [kform_sub]
  ring

/-- **Transport of a part** (`τ = 1` symmetric, `τ = -1` skew): a kernel with rows and columns of
`ν`-mean zero whose part is at most `C` on `L²_0(ν)` has that part at most `e^ℓ C` on `L²(m)`. -/
theorem transport_part (ν : FiniteLaw X) (u0 : X → ℝ) {ℓ C τ : ℝ} (hC : 0 ≤ C)
    (hu : ∀ x, Real.exp (-ℓ) ≤ 1 + u0 x) (Y : X × X → ℝ)
    (hrow : ∀ x, ν.expect (fun y => Y (x, y)) = 0) (hcol : ∀ y, ν.expect (fun x => Y (x, y)) = 0)
    (hY : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |(kform ν ν Y φ ψ + τ * kform ν ν Y ψ φ) / 2| ≤ C * nrm ν φ * nrm ν ψ) (φ ψ : X → ℝ) :
    |(kform ν ν Y φ ψ + τ * kform ν ν Y ψ φ) / 2| ≤
      Real.exp ℓ * C * mnrm ν u0 φ * mnrm ν u0 ψ := by
  have hs := sym_rows ν Y τ hrow hcol
  rw [← kform_sym]
  refine kform_transport ν u0 hC hu _ hs.1 hs.2 ?_ φ ψ
  intro φ ψ hφ hψ
  rw [kform_sym]
  exact hY φ ψ hφ hψ

/-- **`prop:le-mixture`, the change**. Inputs (hypotheses, see the module docstring): the weights,
the repaired components `K_j'` and the old law `K₀`, all with both half marginals `m₀ = (1 + u₀)μ`,
`m₀ ≥ e^{-ℓ₀}μ`; on centred functions `kform(K_j' - K₀) = Lead_j + Rem_j` with `‖Rem_j‖ ≤ E_j`; and
the mixed leading part `∑_j w_j Lead_j` with symmetric and skew parts at most `Γ k_s r` and
`Γ k_a r` (`cor:star-matrix` for `M = ∑_j w_j M_j`). Conclusion: relative to `m₀`, the symmetric and
skew parts of the change `K - K₀`, `K = ∑_j w_j K_j'`, have norms at most
`d_s = e^{ℓ₀}(Γ k_s r + E)` and `d_a = e^{ℓ₀}(Γ k_a r + E)`, `E = ∑_j w_j E_j`. -/
theorem le_mixture_change (ν : FiniteLaw X) (w : ι → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (K' : ι → X × X → ℝ) (K₀ : X × X → ℝ) (u0 : X → ℝ)
    (hm1 : ∀ j x, ν.expect (fun y => K' j (x, y)) = 1 + u0 x)
    (hm2 : ∀ j y, ν.expect (fun x => K' j (x, y)) = 1 + u0 y)
    (hO1 : ∀ x, ν.expect (fun y => K₀ (x, y)) = 1 + u0 x)
    (hO2 : ∀ y, ν.expect (fun x => K₀ (x, y)) = 1 + u0 y)
    (Lead Rem : ι → (X → ℝ) → (X → ℝ) → ℝ)
    (hdec : ∀ j φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      kform ν ν (fun p => K' j p - K₀ p) φ ψ = Lead j φ ψ + Rem j φ ψ)
    (E : ι → ℝ) (hRem : ∀ j φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |Rem j φ ψ| ≤ E j * nrm ν φ * nrm ν ψ)
    {Γ ks ka r ℓ₀ : ℝ} (hks : 0 ≤ Γ * ks * r) (hka : 0 ≤ Γ * ka * r) (hE : ∀ j, 0 ≤ E j)
    (hLs : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |∑ j, w j * ((Lead j φ ψ + Lead j ψ φ) / 2)| ≤ Γ * ks * r * nrm ν φ * nrm ν ψ)
    (hLa : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |∑ j, w j * ((Lead j φ ψ - Lead j ψ φ) / 2)| ≤ Γ * ka * r * nrm ν φ * nrm ν ψ)
    (hu : ∀ x, Real.exp (-ℓ₀) ≤ 1 + u0 x) (φ ψ : X → ℝ) :
    |((centredForm ν u0 (mixKernel w K') φ ψ - centredForm ν u0 K₀ φ ψ) +
        (centredForm ν u0 (mixKernel w K') ψ φ - centredForm ν u0 K₀ ψ φ)) / 2| ≤
      Real.exp ℓ₀ * (Γ * ks * r + ∑ j, w j * E j) * mnrm ν u0 φ * mnrm ν u0 ψ ∧
    |((centredForm ν u0 (mixKernel w K') φ ψ - centredForm ν u0 K₀ φ ψ) -
        (centredForm ν u0 (mixKernel w K') ψ φ - centredForm ν u0 K₀ ψ φ)) / 2| ≤
      Real.exp ℓ₀ * (Γ * ka * r + ∑ j, w j * E j) * mnrm ν u0 φ * mnrm ν u0 ψ := by
  -- the mixture has the marginals `m₀`, so the difference has rows and columns of mean zero
  have hrowK : ∀ x, ν.expect (fun y => mixKernel w K' (x, y)) = 1 + u0 x := by
    intro x
    unfold mixKernel
    rw [expect_wsum ν w (fun j y => K' j (x, y))]
    simp only [hm1]
    rw [← Finset.sum_mul, hw1, one_mul]
  have hcolK : ∀ y, ν.expect (fun x => mixKernel w K' (x, y)) = 1 + u0 y := by
    intro y
    unfold mixKernel
    rw [expect_wsum ν w (fun j x => K' j (x, y))]
    simp only [hm2]
    rw [← Finset.sum_mul, hw1, one_mul]
  have hrow : ∀ x, ν.expect (fun y => mixKernel w K' (x, y) - K₀ (x, y)) = 0 := by
    intro x; rw [ν.expect_sub, hrowK, hO1, sub_self]
  have hcol : ∀ y, ν.expect (fun x => mixKernel w K' (x, y) - K₀ (x, y)) = 0 := by
    intro y; rw [ν.expect_sub, hcolK, hO2, sub_self]
  -- the form of the difference on centred functions
  have hYsum : ∀ p, mixKernel w K' p - K₀ p = ∑ j, w j * (K' j p - K₀ p) := by
    intro p
    unfold mixKernel
    have e : ∑ j, w j * (K' j p - K₀ p) = ∑ j, w j * K' j p - (∑ j, w j) * K₀ p := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, hw1, one_mul]
  have hform : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      kform ν ν (fun p => mixKernel w K' p - K₀ p) φ ψ = ∑ j, w j * (Lead j φ ψ + Rem j φ ψ) := by
    intro φ ψ hφ hψ
    rw [kform_congr ν ν hYsum, kform_wsum ν w (fun j p => K' j p - K₀ p)]
    exact Finset.sum_congr rfl fun j _ => by rw [hdec j φ ψ hφ hψ]
  -- the bound of a part on centred functions
  have hpart : ∀ (τ k : ℝ), |τ| ≤ 1 →
      (∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
        |∑ j, w j * ((Lead j φ ψ + τ * Lead j ψ φ) / 2)| ≤ Γ * k * r * nrm ν φ * nrm ν ψ) →
      ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
        |(kform ν ν (fun p => mixKernel w K' p - K₀ p) φ ψ +
            τ * kform ν ν (fun p => mixKernel w K' p - K₀ p) ψ φ) / 2| ≤
          (Γ * k * r + ∑ j, w j * E j) * nrm ν φ * nrm ν ψ := by
    intro τ k hτ hLk φ ψ hφ hψ
    rw [hform φ ψ hφ hψ, hform ψ φ hψ hφ]
    have e : (∑ j, w j * (Lead j φ ψ + Rem j φ ψ) + τ * ∑ j, w j * (Lead j ψ φ + Rem j ψ φ)) / 2 =
        ∑ j, w j * ((Lead j φ ψ + τ * Lead j ψ φ) / 2) +
          ∑ j, w j * ((Rem j φ ψ + τ * Rem j ψ φ) / 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have h1 := hLk φ ψ hφ hψ
    have h2 : |∑ j, w j * ((Rem j φ ψ + τ * Rem j ψ φ) / 2)| ≤
        (∑ j, w j * E j) * nrm ν φ * nrm ν ψ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_of_nonneg (hw0 j)]
      have hj : |(Rem j φ ψ + τ * Rem j ψ φ) / 2| ≤ E j * (nrm ν φ * nrm ν ψ) :=
        abs_half_add_le hτ (bound_assoc (hRem j) φ ψ hφ hψ) (bound_swap (hRem j) φ ψ hφ hψ)
      calc w j * |(Rem j φ ψ + τ * Rem j ψ φ) / 2| ≤ w j * (E j * (nrm ν φ * nrm ν ψ)) :=
            mul_le_mul_of_nonneg_left hj (hw0 j)
        _ = w j * E j * nrm ν φ * nrm ν ψ := by ring
    have := abs_add_le (∑ j, w j * ((Lead j φ ψ + τ * Lead j ψ φ) / 2))
      (∑ j, w j * ((Rem j φ ψ + τ * Rem j ψ φ) / 2))
    have e2 : (Γ * k * r + ∑ j, w j * E j) * nrm ν φ * nrm ν ψ =
        Γ * k * r * nrm ν φ * nrm ν ψ + (∑ j, w j * E j) * nrm ν φ * nrm ν ψ := by ring
    rw [e2]
    linarith
  have hEsum : 0 ≤ ∑ j, w j * E j := Finset.sum_nonneg fun j _ => mul_nonneg (hw0 j) (hE j)
  have hs := transport_part ν u0 (τ := 1) (add_nonneg hks hEsum) hu _ hrow hcol
    (hpart 1 ks (by norm_num) (fun φ ψ hφ hψ => by
      simp only [one_mul]; exact hLs φ ψ hφ hψ)) φ ψ
  have ha := transport_part ν u0 (τ := -1) (add_nonneg hka hEsum) hu _ hrow hcol
    (hpart (-1) ka (by norm_num) (fun φ ψ hφ hψ => by
      simp only [neg_one_mul, ← sub_eq_add_neg]; exact hLa φ ψ hφ hψ)) φ ψ
  rw [centredForm_sub, centredForm_sub]
  rw [one_mul] at hs
  rw [neg_one_mul, ← sub_eq_add_neg] at ha
  exact ⟨hs, ha⟩

/-- `c₀ = ∑_j w_j c_{0,j}` of `prop:le-mixture`, a convex combination of valid bounds for the old
centred norm; the block gates of the mixture are `DenseBlockGates c₀ d_s d_a k_s k_a r`. -/
noncomputable def leMixtureC0 (w c0 : ι → ℝ) : ℝ := ∑ j, w j * c0 j

/-- `E_j = ∑_h (ℛ_{j,h} + ε_{j,h} C_{j,h}) + 2F_j(C_{j,1} + u_j)` of `prop:le-mixture`, with
`C_{j,h} = (Γ k_{j,h} r + ℛ_{j,h})/(1 - ε_{j,h})`. -/
noncomputable def leCompE (Γ k0 k1 r R0 R1 ε0 ε1 F u : ℝ) : ℝ :=
  (R0 + ε0 * denseC Γ k0 r R0 (1 - ε0)) + (R1 + ε1 * denseC Γ k1 r R1 (1 - ε1)) +
    2 * F * (denseC Γ k1 r R1 (1 - ε1) + u)

/-- **The change of one repaired component** (proof of `prop:le-mixture`, "the proof of
`prop:dense-comparison`(b) writes the centred change of component `j` relative to `μ` as
`r 𝓕 M_j(Φ̂) 𝓕^*` plus a remainder of norm at most `E_j`"). Inputs (hypotheses) as in
`dense_comparison_b`, for the component (`h = 1`, raw kernel `H₁`, its own normalizer and repair
`K₁' = (1 + f + g)K₁`) and the old law (`h = 0`). Conclusion: on centred functions
`kform(K₁' - K₀) = (Lead₁ - Lead₀) + Rem` with `‖Rem‖ ≤ E_j`; here `Lead₁ - Lead₀` is the form of
`r 𝓕 M_j 𝓕^*`, `M_j` the star matrix of the component minus that of `K₀`. -/
theorem le_component_change (ν : FiniteLaw X) (H₀ H₁ K₀ K₁ K₁' : X × X → ℝ) (Z₀ Z₁ : ℝ)
    (hZ₁def : Z₁ = ν.expect (fun x => ν.expect (fun y => H₁ (x, y))))
    (hK₀ : ∀ p, K₀ p = H₀ p / Z₀) (hK₁ : ∀ p, K₁ p = H₁ p / Z₁)
    (Lead₀ Lead₁ Rem₀ Rem₁ : (X → ℝ) → (X → ℝ) → ℝ)
    (hdec₀ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → kform ν ν H₀ φ ψ = Lead₀ φ ψ + Rem₀ φ ψ)
    (hdec₁ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → kform ν ν H₁ φ ψ = Lead₁ φ ψ + Rem₁ φ ψ)
    {Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ u F : ℝ} (hk₁ : 0 ≤ Γ * k₁ * r) (hR₁ : 0 ≤ R₁)
    (hL₀ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Lead₀ φ ψ| ≤ Γ * k₀ * r * nrm ν φ * nrm ν ψ)
    (hL₁ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Lead₁ φ ψ| ≤ Γ * k₁ * r * nrm ν φ * nrm ν ψ)
    (hRm₀ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Rem₀ φ ψ| ≤ R₀ * nrm ν φ * nrm ν ψ)
    (hRm₁ : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Rem₁ φ ψ| ≤ R₁ * nrm ν φ * nrm ν ψ)
    (hZ₀ : |Z₀ - 1| ≤ ε₀) (hZ₁ : |Z₁ - 1| ≤ ε₁) (hε₀ : ε₀ < 1) (hε₁ : ε₁ < 1)
    (hδL : nrm ν (deltaL ν K₁) ≤ u) (hδR : nrm ν (deltaR ν K₁) ≤ u)
    (hF : 0 ≤ F) (f g : X → ℝ) (hf : ∀ x, |f x| ≤ F) (hg : ∀ y, |g y| ≤ F)
    (hK' : ∀ p, K₁' p = (1 + f p.1 + g p.2) * K₁ p)
    (φ ψ : X → ℝ) (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    |kform ν ν (fun p => K₁' p - K₀ p) φ ψ - (Lead₁ φ ψ - Lead₀ φ ψ)| ≤
      leCompE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ F u * nrm ν φ * nrm ν ψ := by
  have hε₀0 : 0 ≤ ε₀ := (abs_nonneg _).trans hZ₀
  have hε₁0 : 0 ≤ ε₁ := (abs_nonneg _).trans hZ₁
  have hz₁ : 0 < 1 - ε₁ := by linarith
  have hz₀ : 0 < 1 - ε₀ := by linarith
  have hZ₁lo : 1 - ε₁ ≤ Z₁ := by have := abs_le.mp hZ₁; linarith
  have hZ₁pos : 0 < Z₁ := hz₁.trans_le hZ₁lo
  have hmass := raw_kernel_mass ν H₁ K₁ Z₁ hZ₁def hZ₁pos.ne' hK₁
  have hKc := dense_centred_kernel ν H₁ K₁ Z₁ hK₁ Lead₁ Rem₁ hdec₁ hz₁ hZ₁lo hL₁ hRm₁
  have hc : 0 ≤ denseC Γ k₁ r R₁ (1 - ε₁) := div_nonneg (add_nonneg hk₁ hR₁) hz₁.le
  have hD := centered_correction_norm ν K₁ hmass hc hF hKc hδL hδR f g hf hg φ ψ hφ hψ
  have e1 : ∀ p, K₁' p - K₀ p = (K₁ p - K₀ p) + (f p.1 + g p.2) * K₁ p := by
    intro p; rw [hK']; ring
  rw [kform_congr ν ν e1, kform_add, kform_sub, kform_normalized ν H₁ K₁ Z₁ hK₁,
    kform_normalized ν H₀ K₀ Z₀ hK₀, hdec₁ φ ψ hφ hψ, hdec₀ φ ψ hφ hψ]
  set D := kform ν ν (fun p => (f p.1 + g p.2) * K₁ p) φ ψ
  set n := nrm ν φ * nrm ν ψ with hn
  have e2 : (Lead₁ φ ψ + Rem₁ φ ψ) / Z₁ - (Lead₀ φ ψ + Rem₀ φ ψ) / Z₀ + D -
      (Lead₁ φ ψ - Lead₀ φ ψ) =
      (Rem₁ φ ψ - Rem₀ φ ψ) + (Z₁⁻¹ - 1) * (Lead₁ φ ψ + Rem₁ φ ψ) -
        (Z₀⁻¹ - 1) * (Lead₀ φ ψ + Rem₀ φ ψ) + D := by
    simp only [div_eq_mul_inv]; ring
  rw [e2]
  have hA₁ : |Lead₁ φ ψ + Rem₁ φ ψ| ≤ (Γ * k₁ * r + R₁) * n := by
    have := abs_add_le (Lead₁ φ ψ) (Rem₁ φ ψ)
    have a := bound_assoc hL₁ φ ψ hφ hψ
    have b := bound_assoc hRm₁ φ ψ hφ hψ
    rw [mul_assoc] at a ⊢
    nlinarith
  have hA₀ : |Lead₀ φ ψ + Rem₀ φ ψ| ≤ (Γ * k₀ * r + R₀) * n := by
    have := abs_add_le (Lead₀ φ ψ) (Rem₀ φ ψ)
    have a := bound_assoc hL₀ φ ψ hφ hψ
    have b := bound_assoc hRm₀ φ ψ hφ hψ
    rw [mul_assoc] at a ⊢
    nlinarith
  have ht₁ := inv_sub_one_abs_le hZ₁ hε₁
  have ht₀ := inv_sub_one_abs_le hZ₀ hε₀
  have hq₁ : 0 ≤ ε₁ / (1 - ε₁) := div_nonneg hε₁0 hz₁.le
  have hq₀ : 0 ≤ ε₀ / (1 - ε₀) := div_nonneg hε₀0 hz₀.le
  have d1 : |(Z₁⁻¹ - 1) * (Lead₁ φ ψ + Rem₁ φ ψ)| ≤ ε₁ / (1 - ε₁) * ((Γ * k₁ * r + R₁) * n) := by
    rw [abs_mul]; exact mul_le_mul ht₁ hA₁ (abs_nonneg _) hq₁
  have d0 : |(Z₀⁻¹ - 1) * (Lead₀ φ ψ + Rem₀ φ ψ)| ≤ ε₀ / (1 - ε₀) * ((Γ * k₀ * r + R₀) * n) := by
    rw [abs_mul]; exact mul_le_mul ht₀ hA₀ (abs_nonneg _) hq₀
  have m1 := bound_assoc hRm₁ φ ψ hφ hψ
  have m0 := bound_assoc hRm₀ φ ψ hφ hψ
  have hD' : |D| ≤ 2 * F * (denseC Γ k₁ r R₁ (1 - ε₁) + u) * n := by
    rw [hn, ← mul_assoc]; exact hD
  have t1 := abs_add_le ((Rem₁ φ ψ - Rem₀ φ ψ) + (Z₁⁻¹ - 1) * (Lead₁ φ ψ + Rem₁ φ ψ) -
    (Z₀⁻¹ - 1) * (Lead₀ φ ψ + Rem₀ φ ψ)) D
  have t2 := abs_sub ((Rem₁ φ ψ - Rem₀ φ ψ) + (Z₁⁻¹ - 1) * (Lead₁ φ ψ + Rem₁ φ ψ))
    ((Z₀⁻¹ - 1) * (Lead₀ φ ψ + Rem₀ φ ψ))
  have t3 := abs_add_le (Rem₁ φ ψ - Rem₀ φ ψ) ((Z₁⁻¹ - 1) * (Lead₁ φ ψ + Rem₁ φ ψ))
  have t4 := abs_sub (Rem₁ φ ψ) (Rem₀ φ ψ)
  have e3 : leCompE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ F u * nrm ν φ * nrm ν ψ =
      R₀ * n + ε₀ / (1 - ε₀) * ((Γ * k₀ * r + R₀) * n) +
        (R₁ * n + ε₁ / (1 - ε₁) * ((Γ * k₁ * r + R₁) * n)) +
        2 * F * (denseC Γ k₁ r R₁ (1 - ε₁) + u) * n := by
    rw [hn]; unfold leCompE denseC; ring
  rw [e3]
  linarith

/-- `E_j ≥ 0`. -/
theorem leCompE_nonneg {Γ k0 k1 r R0 R1 ε0 ε1 F u : ℝ} (hk0 : 0 ≤ Γ * k0 * r)
    (hk1 : 0 ≤ Γ * k1 * r) (hR0 : 0 ≤ R0) (hR1 : 0 ≤ R1) (hε0 : 0 ≤ ε0) (hε1 : 0 ≤ ε1)
    (hε0' : ε0 < 1) (hε1' : ε1 < 1) (hF : 0 ≤ F) (hu : 0 ≤ u) :
    0 ≤ leCompE Γ k0 k1 r R0 R1 ε0 ε1 F u := by
  unfold leCompE denseC
  have a : 0 ≤ (Γ * k0 * r + R0) / (1 - ε0) := div_nonneg (add_nonneg hk0 hR0) (by linarith)
  have b : 0 ≤ (Γ * k1 * r + R1) / (1 - ε1) := div_nonneg (add_nonneg hk1 hR1) (by linarith)
  have c : 0 ≤ ε0 * ((Γ * k0 * r + R0) / (1 - ε0)) := mul_nonneg hε0 a
  have d : 0 ≤ ε1 * ((Γ * k1 * r + R1) / (1 - ε1)) := mul_nonneg hε1 b
  have e : 0 ≤ 2 * F * ((Γ * k1 * r + R1) / (1 - ε1) + u) :=
    mul_nonneg (mul_nonneg (by norm_num) hF) (add_nonneg b hu)
  linarith

/-- **`prop:le-mixture` from the component inputs.** For each component `j` the inputs of
`prop:dense-comparison` (hypotheses, as in `le_component_change`: its raw kernel `H_j` with its own
normalizer, the decompositions of `H_j` and of the old raw kernel `H₀` in the synthesis of the
component, the remainder, normalizer and marginal bounds, and the repair `K_j' = (1 + f_j + g_j)K_j`
with both half marginals `m₀`, the half marginals of `K₀`), and `cor:star-matrix` for the mixed
matrix `M = ∑_j w_j M_j` (`‖Sym M(i)‖ ≤ k_s`, `‖Skew M(i)‖ ≤ k_a`). Conclusion: the change of the
mixture `K = ∑_j w_j K_j'` from the old law has symmetric and skew parts of norms at most
`d_s = e^{ℓ₀}(Γ k_s r + E)` and `d_a = e^{ℓ₀}(Γ k_a r + E)` relative to `m₀`, with
`E = ∑_j w_j E_j` and the paper's `E_j` (`leCompE`). -/
theorem le_mixture_of_components (ν : FiniteLaw X) (w : ι → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (H₀ K₀ : X × X → ℝ) (Z₀ : ℝ) (hK₀ : ∀ p, K₀ p = H₀ p / Z₀)
    (H K K' : ι → X × X → ℝ) (Z : ι → ℝ)
    (hZdef : ∀ j, Z j = ν.expect (fun x => ν.expect (fun y => H j (x, y))))
    (hK : ∀ j p, K j p = H j p / Z j)
    (Lead₀ Rem₀ Lead₁ Rem₁ : ι → (X → ℝ) → (X → ℝ) → ℝ)
    (hdec₀ : ∀ j φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      kform ν ν H₀ φ ψ = Lead₀ j φ ψ + Rem₀ j φ ψ)
    (hdec₁ : ∀ j φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      kform ν ν (H j) φ ψ = Lead₁ j φ ψ + Rem₁ j φ ψ)
    {Γ r ks ka ℓ₀ : ℝ} (k₀ k₁ R₀ R₁ ε₀ ε₁ u F : ι → ℝ)
    (hk₀ : ∀ j, 0 ≤ Γ * k₀ j * r) (hk₁ : ∀ j, 0 ≤ Γ * k₁ j * r) (hR₀ : ∀ j, 0 ≤ R₀ j)
    (hR₁ : ∀ j, 0 ≤ R₁ j)
    (hL₀ : ∀ j φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |Lead₀ j φ ψ| ≤ Γ * k₀ j * r * nrm ν φ * nrm ν ψ)
    (hL₁ : ∀ j φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |Lead₁ j φ ψ| ≤ Γ * k₁ j * r * nrm ν φ * nrm ν ψ)
    (hRm₀ : ∀ j φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Rem₀ j φ ψ| ≤ R₀ j * nrm ν φ * nrm ν ψ)
    (hRm₁ : ∀ j φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 → |Rem₁ j φ ψ| ≤ R₁ j * nrm ν φ * nrm ν ψ)
    (hZ₀ : ∀ j, |Z₀ - 1| ≤ ε₀ j) (hZ : ∀ j, |Z j - 1| ≤ ε₁ j) (hε₀ : ∀ j, ε₀ j < 1)
    (hε₁ : ∀ j, ε₁ j < 1)
    (hδL : ∀ j, nrm ν (deltaL ν (K j)) ≤ u j) (hδR : ∀ j, nrm ν (deltaR ν (K j)) ≤ u j)
    (hF : ∀ j, 0 ≤ F j) (f g : ι → X → ℝ) (hf : ∀ j x, |f j x| ≤ F j)
    (hg : ∀ j y, |g j y| ≤ F j) (hK' : ∀ j p, K' j p = (1 + f j p.1 + g j p.2) * K j p)
    (u0 : X → ℝ)
    (hm1 : ∀ j x, ν.expect (fun y => K' j (x, y)) = 1 + u0 x)
    (hm2 : ∀ j y, ν.expect (fun x => K' j (x, y)) = 1 + u0 y)
    (hO1 : ∀ x, ν.expect (fun y => K₀ (x, y)) = 1 + u0 x)
    (hO2 : ∀ y, ν.expect (fun x => K₀ (x, y)) = 1 + u0 y)
    (hks : 0 ≤ Γ * ks * r) (hka : 0 ≤ Γ * ka * r)
    (hLs : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |∑ j, w j * (((Lead₁ j φ ψ - Lead₀ j φ ψ) + (Lead₁ j ψ φ - Lead₀ j ψ φ)) / 2)| ≤
        Γ * ks * r * nrm ν φ * nrm ν ψ)
    (hLa : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |∑ j, w j * (((Lead₁ j φ ψ - Lead₀ j φ ψ) - (Lead₁ j ψ φ - Lead₀ j ψ φ)) / 2)| ≤
        Γ * ka * r * nrm ν φ * nrm ν ψ)
    (hu : ∀ x, Real.exp (-ℓ₀) ≤ 1 + u0 x) (φ ψ : X → ℝ) :
    |((centredForm ν u0 (mixKernel w K') φ ψ - centredForm ν u0 K₀ φ ψ) +
        (centredForm ν u0 (mixKernel w K') ψ φ - centredForm ν u0 K₀ ψ φ)) / 2| ≤
      Real.exp ℓ₀ * (Γ * ks * r + ∑ j, w j *
          leCompE Γ (k₀ j) (k₁ j) r (R₀ j) (R₁ j) (ε₀ j) (ε₁ j) (F j) (u j)) *
        mnrm ν u0 φ * mnrm ν u0 ψ ∧
    |((centredForm ν u0 (mixKernel w K') φ ψ - centredForm ν u0 K₀ φ ψ) -
        (centredForm ν u0 (mixKernel w K') ψ φ - centredForm ν u0 K₀ ψ φ)) / 2| ≤
      Real.exp ℓ₀ * (Γ * ka * r + ∑ j, w j *
          leCompE Γ (k₀ j) (k₁ j) r (R₀ j) (R₁ j) (ε₀ j) (ε₁ j) (F j) (u j)) *
        mnrm ν u0 φ * mnrm ν u0 ψ := by
  refine le_mixture_change ν w hw0 hw1 K' K₀ u0 hm1 hm2 hO1 hO2
    (fun j φ ψ => Lead₁ j φ ψ - Lead₀ j φ ψ)
    (fun j φ ψ => kform ν ν (fun p => K' j p - K₀ p) φ ψ - (Lead₁ j φ ψ - Lead₀ j φ ψ))
    (fun _ _ _ _ _ => by ring)
    (fun j => leCompE Γ (k₀ j) (k₁ j) r (R₀ j) (R₁ j) (ε₀ j) (ε₁ j) (F j) (u j))
    (fun j φ ψ hφ hψ => le_component_change ν H₀ (H j) K₀ (K j) (K' j) Z₀ (Z j) (hZdef j) hK₀
      (hK j) (Lead₀ j) (Lead₁ j) (Rem₀ j) (Rem₁ j) (hdec₀ j) (hdec₁ j) (hk₁ j) (hR₁ j) (hL₀ j)
      (hL₁ j) (hRm₀ j) (hRm₁ j) (hZ₀ j) (hZ j) (hε₀ j) (hε₁ j) (hδL j) (hδR j) (hF j) (f j) (g j)
      (hf j) (hg j) (hK' j) φ ψ hφ hψ)
    hks hka (fun j => leCompE_nonneg (hk₀ j) (hk₁ j) (hR₀ j) (hR₁ j)
      ((abs_nonneg _).trans (hZ₀ j)) ((abs_nonneg _).trans (hZ j)) (hε₀ j) (hε₁ j) (hF j)
      ((Real.sqrt_nonneg _).trans (hδL j))) hLs hLa hu φ ψ

end Sarkozy.UpperComparison
