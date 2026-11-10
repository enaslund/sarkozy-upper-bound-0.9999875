module

public import Sarkozy.UpperRepair.OldKernel
public import Sarkozy.UpperComparison.DenseLaws
public import Sarkozy.UpperComparison.LEMixture

@[expose] public section

/-!
# The 2 dense EL laws and the 6 LE mixtures from W8's propositions (`prop:dense-comparison`,
`prop:le-mixture`)

`paper/sections/26_upper_comparison.tex`, "Replacements keeping the old cross edges". W8 proved the
closure of `prop:dense-comparison` (`dense_comparison_a`, `dense_comparison_b`) and of
`prop:le-mixture` (`le_mixture_law`, `le_mixture_change`) from their cited inputs, in kernel form.
Here they are instantiated at the record `(t, φ)` of an upper block, with `ν := λ_H` (`recHalf`),
`u₀ := recU` and the old kernel `K₀ := recK` (`OldKernel.lean`: W8's `hO1`, `hO2` and the
identification of its centred forms are proved), and give a `KernelInput`, hence a `ReplRecord`:

* **`KernelInput.ofDense`**: the dense EL law `K₁' = (1 + f(x) + g(y))K₁` with
  `C^s = d_s`, `C^a = d_a` (`denseD`, `prop:dense-comparison`(b));
* **`KernelInput.ofMixture`**: the LE mixture `∑_j w_j K_j'` with
  `C^s = e^{ℓ₀}(Γ k_s r + ∑_j w_j E_j)`, `C^a = e^{ℓ₀}(Γ k_a r + ∑_j w_j E_j)` (`prop:le-mixture`).

*Hypotheses*: W8's (the cited inputs of the two propositions at the block: `cor:soft-kernels`,
`cor:star-matrix`, `lem:wt:stars`, `lem:tr:repair`(g), the two-root identity), the acceptance of
the new kernels on their support (for `K₁ = K_{D₁}` W8's `dense_accepts_required`, in the
coordinates of V3's dense kernels), and `ℓ₀ ≥ 0` with `e^{-ℓ₀} ≤ 1 + u₀`. The marginals of the
old kernel and its kernel identification are proved.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.Structured Sarkozy.Recentering

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]
  {hne : UpperNonempty pr} {t : PType × PType} {φ : t.1.Pat × t.2.Pat}

namespace KernelInput

/-- **The dense EL law of a record as a `KernelInput`** (`prop:dense-comparison`(a),(b), W8's
`dense_comparison_a`, `dense_comparison_b` at `ν = λ_H`, `u₀ = recU`, `K₀ = recK`). -/
noncomputable def ofDense
    (H₀ H₁ K₁ K₁' : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) ×
      (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) (Z₀ Z₁ : ℝ)
    (hK₁0 : ∀ p, 0 ≤ K₁ p)
    (hZ₁def : Z₁ = (recHalf pr hne t).expect (fun x => (recHalf pr hne t).expect
      (fun y => H₁ (x, y))))
    (hK₀ : ∀ p, recK pr hne t p = H₀ p / Z₀) (hK₁ : ∀ p, K₁ p = H₁ p / Z₁)
    (Lead₀ Lead₁ Rem₀ Rem₁ : ((t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) →
      ((t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) → ℝ)
    (hdec₀ : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      kform (recHalf pr hne t) (recHalf pr hne t) H₀ φ' ψ' = Lead₀ φ' ψ' + Rem₀ φ' ψ')
    (hdec₁ : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      kform (recHalf pr hne t) (recHalf pr hne t) H₁ φ' ψ' = Lead₁ φ' ψ' + Rem₁ φ' ψ')
    {Γ k₀ k₁ ks ka r R₀ R₁ ε₀ ε₁ u₁ FN ℓ₀ : ℝ}
    (hk₀ : 0 ≤ Γ * k₀ * r) (hk₁ : 0 ≤ Γ * k₁ * r) (hks : 0 ≤ Γ * ks * r) (hka : 0 ≤ Γ * ka * r)
    (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁)
    (hL₀ : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      |Lead₀ φ' ψ'| ≤ Γ * k₀ * r * nrm (recHalf pr hne t) φ' * nrm (recHalf pr hne t) ψ')
    (hL₁ : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      |Lead₁ φ' ψ'| ≤ Γ * k₁ * r * nrm (recHalf pr hne t) φ' * nrm (recHalf pr hne t) ψ')
    (hLs : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      |((Lead₁ φ' ψ' - Lead₀ φ' ψ') + (Lead₁ ψ' φ' - Lead₀ ψ' φ')) / 2| ≤
        Γ * ks * r * nrm (recHalf pr hne t) φ' * nrm (recHalf pr hne t) ψ')
    (hLa : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      |((Lead₁ φ' ψ' - Lead₀ φ' ψ') - (Lead₁ ψ' φ' - Lead₀ ψ' φ')) / 2| ≤
        Γ * ka * r * nrm (recHalf pr hne t) φ' * nrm (recHalf pr hne t) ψ')
    (hRm₀ : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      |Rem₀ φ' ψ'| ≤ R₀ * nrm (recHalf pr hne t) φ' * nrm (recHalf pr hne t) ψ')
    (hRm₁ : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      |Rem₁ φ' ψ'| ≤ R₁ * nrm (recHalf pr hne t) φ' * nrm (recHalf pr hne t) ψ')
    (hZ₀ : |Z₀ - 1| ≤ ε₀) (hZ₁ : |Z₁ - 1| ≤ ε₁) (hε₀ : ε₀ < 1 / 2) (hε₁ : ε₁ < 1 / 2)
    (hδL : nrm (recHalf pr hne t) (deltaL (recHalf pr hne t) K₁) ≤ u₁)
    (hδR : nrm (recHalf pr hne t) (deltaR (recHalf pr hne t) K₁) ≤ u₁)
    (hFN : 0 ≤ FN) (hFN2 : 2 * FN < 1) (f g : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ)
    (hf : ∀ x, |f x| ≤ FN) (hg : ∀ y, |g y| ≤ FN) (hK' : ∀ p, K₁' p = (1 + f p.1 + g p.2) * K₁ p)
    (hm1 : ∀ x, (recHalf pr hne t).expect (fun y => K₁' (x, y)) = 1 + recU pr hne t x)
    (hm2 : ∀ y, (recHalf pr hne t).expect (fun x => K₁' (x, y)) = 1 + recU pr hne t y)
    (hu : ∀ x, Real.exp (-ℓ₀) ≤ 1 + recU pr hne t x)
    (hacc : ∀ x x', (recHalf pr hne t).weight x ≠ 0 → (recHalf pr hne t).weight x' ≠ 0 →
      K₁ (x, x') ≠ 0 → ∀ (j : Chamber) (i : ι),
      quadraticChar (ZMod (pr i)) (x' (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j)) i -
        x (t.1.pat φ.1 0, t.2.pat φ.2 j) i) = 1)
    (hCs : 0 ≤ denseD ℓ₀ Γ ks r (denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) FN
      (denseC Γ k₁ r R₁ (1 - ε₁)) u₁)
    (hCa : 0 ≤ denseD ℓ₀ Γ ka r (denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) FN
      (denseC Γ k₁ r R₁ (1 - ε₁)) u₁) :
    KernelInput pr hne t φ where
  K := K₁'
  K_nonneg := (dense_comparison_a (recHalf pr hne t) K₁ K₁' hK₁0 hFN2 f g hf hg hK'
    (recU pr hne t) (by
      have h := recU_mean pr hne t
      rw [FiniteLaw.expect_add, FiniteLaw.expect_const] at h
      linarith) hm1 hm2).1
  row x _ := hm1 x
  col y _ := hm2 y
  accepts x x' hx hx' hK j i := by
    have hsupp := (dense_comparison_a (recHalf pr hne t) K₁ K₁' hK₁0 hFN2 f g hf hg hK'
      (recU pr hne t) (by
        have h := recU_mean pr hne t
        rw [FiniteLaw.expect_add, FiniteLaw.expect_const] at h
        linarith) hm1 hm2).2.2.2.2 (x, x') hK
    exact hacc x x' hx hx' hsupp j i
  Cs := denseD ℓ₀ Γ ks r (denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) FN
    (denseC Γ k₁ r R₁ (1 - ε₁)) u₁
  Ca := denseD ℓ₀ Γ ka r (denseE Γ k₀ k₁ r R₀ R₁ ε₀ ε₁ (1 - ε₀) (1 - ε₁)) FN
    (denseC Γ k₁ r R₁ (1 - ε₁)) u₁
  Cs_nonneg := hCs
  Ca_nonneg := hCa
  sym φ' ψ' := by
    have h := (dense_comparison_b (recHalf pr hne t) H₀ H₁ (recK pr hne t) K₁ K₁' Z₀ Z₁ hZ₁def
      hK₀ hK₁ Lead₀ Lead₁ Rem₀ Rem₁ hdec₀ hdec₁ hk₀ hk₁ hks hka hR₀ hR₁ hL₀ hL₁ hLs hLa hRm₀ hRm₁
      hZ₀ hZ₁ hε₀ hε₁ hδL hδR hFN f g hf hg hK' (recU pr hne t) hm1 hm2 (recK_row pr hne t)
      (recK_col pr hne t) hu φ' ψ').1
    rwa [recK_centredForm, recK_centredForm] at h
  skew φ' ψ' := by
    have h := (dense_comparison_b (recHalf pr hne t) H₀ H₁ (recK pr hne t) K₁ K₁' Z₀ Z₁ hZ₁def
      hK₀ hK₁ Lead₀ Lead₁ Rem₀ Rem₁ hdec₀ hdec₁ hk₀ hk₁ hks hka hR₀ hR₁ hL₀ hL₁ hLs hLa hRm₀ hRm₁
      hZ₀ hZ₁ hε₀ hε₁ hδL hδR hFN f g hf hg hK' (recU pr hne t) hm1 hm2 (recK_row pr hne t)
      (recK_col pr hne t) hu φ' ψ').2
    rwa [recK_centredForm, recK_centredForm] at h

/-- **The LE mixture of a record as a `KernelInput`** (`prop:le-mixture`, W8's `le_mixture_law`,
`le_mixture_change` at `ν = λ_H`, `u₀ = recU`, `K₀ = recK`). -/
noncomputable def ofMixture {J : Type} [Fintype J] (w : J → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1)
    (K' : J → (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) ×
      (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) (hK'0 : ∀ j p, 0 ≤ K' j p)
    (hm1 : ∀ j x, (recHalf pr hne t).expect (fun y => K' j (x, y)) = 1 + recU pr hne t x)
    (hm2 : ∀ j y, (recHalf pr hne t).expect (fun x => K' j (x, y)) = 1 + recU pr hne t y)
    (Lead Rem : J → ((t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) →
      ((t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) → ℝ)
    (hdec : ∀ j φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      kform (recHalf pr hne t) (recHalf pr hne t) (fun p => K' j p - recK pr hne t p) φ' ψ' =
        Lead j φ' ψ' + Rem j φ' ψ')
    (E : J → ℝ) (hRem : ∀ j φ' ψ', (recHalf pr hne t).expect φ' = 0 →
      (recHalf pr hne t).expect ψ' = 0 →
      |Rem j φ' ψ'| ≤ E j * nrm (recHalf pr hne t) φ' * nrm (recHalf pr hne t) ψ')
    {Γ ks ka r ℓ₀ : ℝ} (hks : 0 ≤ Γ * ks * r) (hka : 0 ≤ Γ * ka * r) (hE : ∀ j, 0 ≤ E j)
    (hLs : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      |∑ j, w j * ((Lead j φ' ψ' + Lead j ψ' φ') / 2)| ≤
        Γ * ks * r * nrm (recHalf pr hne t) φ' * nrm (recHalf pr hne t) ψ')
    (hLa : ∀ φ' ψ', (recHalf pr hne t).expect φ' = 0 → (recHalf pr hne t).expect ψ' = 0 →
      |∑ j, w j * ((Lead j φ' ψ' - Lead j ψ' φ') / 2)| ≤
        Γ * ka * r * nrm (recHalf pr hne t) φ' * nrm (recHalf pr hne t) ψ')
    (hu : ∀ x, Real.exp (-ℓ₀) ≤ 1 + recU pr hne t x)
    (hacc : ∀ j x x', (recHalf pr hne t).weight x ≠ 0 → (recHalf pr hne t).weight x' ≠ 0 →
      w j ≠ 0 → K' j (x, x') ≠ 0 → ∀ (c : Chamber) (i : ι),
      quadraticChar (ZMod (pr i)) (x' (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation c)) i -
        x (t.1.pat φ.1 0, t.2.pat φ.2 c) i) = 1) :
    KernelInput pr hne t φ where
  K := mixKernel w K'
  K_nonneg := (le_mixture_law (recHalf pr hne t) w hw0 hw1 K' hK'0 (recU pr hne t) (by
      have h := recU_mean pr hne t
      rw [FiniteLaw.expect_add, FiniteLaw.expect_const] at h
      linarith) hm1 hm2).1
  row x _ := (le_mixture_law (recHalf pr hne t) w hw0 hw1 K' hK'0 (recU pr hne t) (by
      have h := recU_mean pr hne t
      rw [FiniteLaw.expect_add, FiniteLaw.expect_const] at h
      linarith) hm1 hm2).2.2.1 x
  col y _ := (le_mixture_law (recHalf pr hne t) w hw0 hw1 K' hK'0 (recU pr hne t) (by
      have h := recU_mean pr hne t
      rw [FiniteLaw.expect_add, FiniteLaw.expect_const] at h
      linarith) hm1 hm2).2.2.2.1 y
  accepts x x' hx hx' hK c i := by
    obtain ⟨j, hwj, hKj⟩ := (le_mixture_law (recHalf pr hne t) w hw0 hw1 K' hK'0
      (recU pr hne t) (by
        have h := recU_mean pr hne t
        rw [FiniteLaw.expect_add, FiniteLaw.expect_const] at h
        linarith) hm1 hm2).2.2.2.2 (x, x') hK
    exact hacc j x x' hx hx' hwj hKj c i
  Cs := Real.exp ℓ₀ * (Γ * ks * r + ∑ j, w j * E j)
  Ca := Real.exp ℓ₀ * (Γ * ka * r + ∑ j, w j * E j)
  Cs_nonneg := mul_nonneg (Real.exp_pos _).le
    (add_nonneg hks (Finset.sum_nonneg fun j _ => mul_nonneg (hw0 j) (hE j)))
  Ca_nonneg := mul_nonneg (Real.exp_pos _).le
    (add_nonneg hka (Finset.sum_nonneg fun j _ => mul_nonneg (hw0 j) (hE j)))
  sym φ' ψ' := by
    have h := (le_mixture_change (recHalf pr hne t) w hw0 hw1 K' (recK pr hne t) (recU pr hne t)
      hm1 hm2 (recK_row pr hne t) (recK_col pr hne t) Lead Rem hdec E hRem hks hka hE hLs hLa hu
      φ' ψ').1
    rwa [recK_centredForm, recK_centredForm] at h
  skew φ' ψ' := by
    have h := (le_mixture_change (recHalf pr hne t) w hw0 hw1 K' (recK pr hne t) (recU pr hne t)
      hm1 hm2 (recK_row pr hne t) (recK_col pr hne t) Lead Rem hdec E hRem hks hka hE hLs hLa hu
      φ' ψ').2
    rwa [recK_centredForm, recK_centredForm] at h

end KernelInput

end Sarkozy.UpperRepair
