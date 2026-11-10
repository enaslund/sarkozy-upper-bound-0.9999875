module

public import Sarkozy.UpperRepair.Replacement

@[expose] public section

/-!
# Replacing laws from kernels: the dense EL laws and the LE mixtures (`prop:dense-comparison`,
`prop:le-mixture`)

`paper/sections/26_upper_comparison.tex`, "Replacements keeping the old cross edges": the two dense
EL records (`RL`) are replaced by the repaired softening `K₁'` of `prop:dense-comparison`, and the
six LE records (`LR`) by the positive mixture `∑_j w_j K_j'` of `prop:le-mixture`. W8 states both
propositions for **kernels** `K : X × X → ℝ` relative to `ν ⊗ ν`, `ν = λ_H`
(`UpperComparison/DenseLaws.lean`, `LEMixture.lean`): (a) `K'` is a nonnegative coupling of
`m₀ = (1 + u₀)ν` with itself, accepting the required queries on its support; (b) the symmetric and
skew parts of `𝒞_{K'} − 𝒞_{K₀}` relative to `m₀` are at most `d_s`, `d_a`. Here such a kernel is
turned into a two-layer block law, so that it is a `ReplRecord`:

* `half_density_lin`: the layer-`0` law of a two-layer law is `(1 + u₀)ν` (the linear form of W8's
  `half_density_eq`);
* `kerPair`, **`kerLaw ν K`**: the two-layer law whose pair of layers has the law `K(ν ⊗ ν)`
  (`glue` puts the two halves on the two layers); `kerLaw_pair`: its pair forms are `kform ν ν K`;
  `kerLaw_weight_ne_zero`: its support;
* `oldKernel_row`: on the support of `ν`, the rows of the old kernel `K₀ = pairDensity π^old λ_H`
  are `1 + u₀` (W8's hypothesis `hO1`; the columns, `hO2`, follow in the same way by the layer
  symmetry). W8 states `hO1`, `hO2` for all `x`; off the support of `ν` they fail for this `K₀`
  (its rows vanish there), which is harmless since `kform` gives those points weight zero, but
  W8's propositions must then be applied to `K₀` modified off the support (see the report);
* `KernelInput pr hne t φ`: a kernel with W8's outputs (a) and (b) (marginals on the support of
  `ν`, acceptance, the bounds `d_s`, `d_a` in W8's form); **`KernelInput.toRepl`**: its
  `ReplRecord`.

So W8's `dense_comparison_a`/`_b` and `le_mixture_law`/`le_mixture_change` (with `ν := λ_H`,
`u₀ := recU`, `K₀ := pairDensity π^old λ_H`) produce exactly the fields of `KernelInput`. Their own
hypotheses (the inputs of `cor:soft-kernels`, `cor:star-matrix`, `lem:wt:stars`,
`lem:tr:repair`(g) at the block) stay open.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.Structured

section Generic

variable {O₀ O₁ Z : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
  [Fintype Z] [DecidableEq Z]

/-- **The layer-`0` law of a two-layer law is `(1 + u₀)ν`** (linear form of `half_density_eq`). -/
theorem half_density_lin (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (ν : FiniteLaw (O₀ × O₁ → Z))
    (hs : LayersSupported lam ν) (g : (O₀ × O₁ → Z) → ℝ) :
    lam.expect (fun y => g (layerOf y 0)) =
      ν.expect (fun x => (1 + halfDensity lam ν x) * g x) := by
  have hterm : ∀ x : O₀ × O₁ → Z, ν.weight x * ((1 + halfDensity lam ν x) * g x) =
      (∑ y, if layerOf y 0 = x then lam.weight y else 0) * g x := by
    intro x
    unfold halfDensity
    split_ifs with h
    · have hz : (∑ y, if layerOf y 0 = x then lam.weight y else 0) = 0 := by
        refine Finset.sum_eq_zero fun y _ => ?_
        split_ifs with hy
        · by_contra hw
          have := (hs y hw).1
          rw [hy] at this
          exact this h
        · rfl
      rw [h, hz]
      ring
    · field_simp
      ring
  unfold FiniteLaw.expect
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  rw [sum_marginal_mul (fun y => layerOf y 0) lam.weight g]

/-- Two functions that agree on the support of a law have the same expectation. -/
theorem expect_congr_supp {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω) {f g : Ω → ℝ}
    (h : ∀ ω, ν.weight ω ≠ 0 → f ω = g ω) : ν.expect f = ν.expect g := by
  unfold FiniteLaw.expect
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ν.weight ω = 0
  · rw [hω, zero_mul, zero_mul]
  · rw [h ω hω]

/-- The double expectation can be taken in either order. -/
theorem expect_comm {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω) (F : Ω → Ω → ℝ) :
    ν.expect (fun x => ν.expect (fun y => F x y)) =
      ν.expect (fun y => ν.expect (fun x => F x y)) := by
  unfold FiniteLaw.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The two-layer labelling with halves `p.1` (layer `0`) and `p.2` (layer `1`). -/
def glue (p : (O₀ × O₁ → Z) × (O₀ × O₁ → Z)) : O₀ × O₁ × Fin 2 → Z :=
  fun v => if v.2.2 = 0 then p.1 (v.1, v.2.1) else p.2 (v.1, v.2.1)

omit [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁] [Fintype Z] [DecidableEq Z] in
theorem layerOf_glue0 (p : (O₀ × O₁ → Z) × (O₀ × O₁ → Z)) : layerOf (glue p) 0 = p.1 := by
  funext o
  simp [glue, layerOf]

omit [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁] [Fintype Z] [DecidableEq Z] in
theorem layerOf_glue1 (p : (O₀ × O₁ → Z) × (O₀ × O₁ → Z)) : layerOf (glue p) 1 = p.2 := by
  funext o
  simp [glue, layerOf]

/-- The law `K(ν ⊗ ν)` on pairs of halves. -/
noncomputable def kerPair (ν : FiniteLaw (O₀ × O₁ → Z)) (K : (O₀ × O₁ → Z) × (O₀ × O₁ → Z) → ℝ)
    (hK : ∀ p, 0 ≤ K p) (htot : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) :
    FiniteLaw ((O₀ × O₁ → Z) × (O₀ × O₁ → Z)) where
  weight p := ν.weight p.1 * ν.weight p.2 * K p
  nonneg p := mul_nonneg (mul_nonneg (ν.nonneg _) (ν.nonneg _)) (hK p)
  total := by
    rw [Fintype.sum_prod_type, ← htot]
    unfold FiniteLaw.expect
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring

omit [DecidableEq Z] in
theorem kerPair_expect (ν : FiniteLaw (O₀ × O₁ → Z)) (K : (O₀ × O₁ → Z) × (O₀ × O₁ → Z) → ℝ)
    (hK : ∀ p, 0 ≤ K p) (htot : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1)
    (F : (O₀ × O₁ → Z) × (O₀ × O₁ → Z) → ℝ) :
    (kerPair ν K hK htot).expect F =
      ν.expect (fun x => ν.expect (fun y => K (x, y) * F (x, y))) := by
  unfold FiniteLaw.expect kerPair
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **The two-layer law of a kernel**: its two layers have the joint law `K(ν ⊗ ν)`. -/
noncomputable def kerLaw (ν : FiniteLaw (O₀ × O₁ → Z)) (K : (O₀ × O₁ → Z) × (O₀ × O₁ → Z) → ℝ)
    (hK : ∀ p, 0 ≤ K p) (htot : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) :
    FiniteLaw (O₀ × O₁ × Fin 2 → Z) :=
  (kerPair ν K hK htot).map glue

theorem kerLaw_expect (ν : FiniteLaw (O₀ × O₁ → Z)) (K : (O₀ × O₁ → Z) × (O₀ × O₁ → Z) → ℝ)
    (hK : ∀ p, 0 ≤ K p) (htot : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1)
    (F : (O₀ × O₁ × Fin 2 → Z) → ℝ) :
    (kerLaw ν K hK htot).expect F =
      ν.expect (fun x => ν.expect (fun y => K (x, y) * F (glue (x, y)))) := by
  unfold kerLaw
  rw [FiniteLaw.expect_map, kerPair_expect]
  rfl

/-- **The pair forms of the kernel law are those of `K`.** -/
theorem kerLaw_pair (ν : FiniteLaw (O₀ × O₁ → Z)) (K : (O₀ × O₁ → Z) × (O₀ × O₁ → Z) → ℝ)
    (hK : ∀ p, 0 ≤ K p) (htot : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1)
    (φ ψ : (O₀ × O₁ → Z) → ℝ) :
    (kerLaw ν K hK htot).expect (fun y => φ (layerOf y 0) * ψ (layerOf y 1)) = kform ν ν K φ ψ := by
  rw [kerLaw_expect]
  unfold kform
  refine ν.expect_congr fun x => ν.expect_congr fun y => ?_
  rw [layerOf_glue0, layerOf_glue1]
  ring

/-- **The support of the kernel law**: both halves are charged by `ν`, and `K ≠ 0` there. -/
theorem kerLaw_weight_ne_zero (ν : FiniteLaw (O₀ × O₁ → Z))
    (K : (O₀ × O₁ → Z) × (O₀ × O₁ → Z) → ℝ) (hK : ∀ p, 0 ≤ K p)
    (htot : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) {y : O₀ × O₁ × Fin 2 → Z}
    (hy : (kerLaw ν K hK htot).weight y ≠ 0) :
    ν.weight (layerOf y 0) ≠ 0 ∧ ν.weight (layerOf y 1) ≠ 0 ∧
      K (layerOf y 0, layerOf y 1) ≠ 0 := by
  change (∑ p, if glue p = y then (kerPair ν K hK htot).weight p else 0) ≠ 0 at hy
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  have hg : glue p = y := by
    by_contra hne
    simp only [hne, ↓reduceIte] at hp
    exact hp rfl
  simp only [hg, ↓reduceIte] at hp
  change ν.weight p.1 * ν.weight p.2 * K p ≠ 0 at hp
  subst hg
  rw [layerOf_glue0, layerOf_glue1]
  exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hp), right_ne_zero_of_mul
    (left_ne_zero_of_mul hp), right_ne_zero_of_mul hp⟩

theorem kerLaw_supported (ν : FiniteLaw (O₀ × O₁ → Z)) (K : (O₀ × O₁ → Z) × (O₀ × O₁ → Z) → ℝ)
    (hK : ∀ p, 0 ≤ K p) (htot : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) :
    LayersSupported (kerLaw ν K hK htot) ν := fun _ hy =>
  ⟨(kerLaw_weight_ne_zero ν K hK htot hy).1, (kerLaw_weight_ne_zero ν K hK htot hy).2.1⟩

/-- **The rows of the old kernel** `K₀ = pairDensity lam ν` are `1 + u₀` on the support of `ν`. -/
theorem oldKernel_row (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (ν : FiniteLaw (O₀ × O₁ → Z))
    (hs : LayersSupported lam ν) (x : O₀ × O₁ → Z) (hx : ν.weight x ≠ 0) :
    ν.expect (fun y => pairDensity lam ν (x, y)) = 1 + halfDensity lam ν x := by
  set δ : (O₀ × O₁ → Z) → ℝ := fun z => if z = x then 1 else 0 with hδ
  have h1 := pair_density_eq lam ν hs δ (fun _ => 1)
  have h2 := half_density_lin lam ν hs δ
  have e1 : lam.expect (fun y => δ (layerOf y 0) * (fun _ => (1 : ℝ)) (layerOf y 1)) =
      lam.expect (fun y => δ (layerOf y 0)) := lam.expect_congr fun _ => mul_one _
  rw [e1, h2] at h1
  have e2 : ν.expect (fun z => (1 + halfDensity lam ν z) * δ z) =
      ν.weight x * (1 + halfDensity lam ν x) := by
    unfold FiniteLaw.expect
    rw [Finset.sum_eq_single x]
    · simp [hδ]
    · intro z _ hz
      simp [hδ, hz]
    · simp
  have e3 : kform ν ν (pairDensity lam ν) δ (fun _ => 1) =
      ν.weight x * ν.expect (fun y => pairDensity lam ν (x, y)) := by
    unfold kform
    unfold FiniteLaw.expect
    rw [Finset.sum_eq_single x]
    · simp [hδ]
    · intro z _ hz
      simp [hδ, hz]
    · simp
  rw [e2, e3] at h1
  exact (mul_left_cancel₀ hx h1).symm

end Generic

/-! ## The kernel inputs of a changed record -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- `E_{λ_H} u₀ = 0`: the old half marginal `(1 + u₀)λ_H` is a probability law. -/
theorem recU_mean (hne : UpperNonempty pr) (t : PType × PType) :
    (recHalf pr hne t).expect (fun x => 1 + recU pr hne t x) = 1 := by
  have h := half_density_lin (recOld pr hne t) (recHalf pr hne t)
    (upper_layersSupported pr hne _ _) (fun _ => 1)
  simp only [mul_one, FiniteLaw.expect_const] at h
  exact h.symm

/-- **The kernel inputs of a changed record** (`prop:dense-comparison`(a),(b), `prop:le-mixture`):
a nonnegative kernel `K` relative to `ν ⊗ ν` (`ν = λ_H`) with both marginals `1 + u₀` on the support
of `ν`, accepting the six projected queries on its support, and the bounds `C^s`, `C^a` on the
symmetric and skew parts of `𝒞_K − 𝒞_{K₀}` relative to `m₀ = (1 + u₀)ν`, `K₀ = pairDensity π^old ν`,
in the form of W8's `dense_comparison_b` and `le_mixture_change`. *Hypotheses*: these are the
conclusions of the two propositions (W8 proves them from their cited inputs). -/
structure KernelInput (hne : UpperNonempty pr) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) where
  /-- The kernel `K₁'` (dense law) or `∑_j w_j K_j'` (LE mixture). -/
  K : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) ×
    (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ
  K_nonneg : ∀ p, 0 ≤ K p
  /-- The rows of `K` are `1 + u₀` on the support of `ν`. -/
  row : ∀ x, (recHalf pr hne t).weight x ≠ 0 →
    (recHalf pr hne t).expect (fun y => K (x, y)) = 1 + recU pr hne t x
  /-- The columns of `K` are `1 + u₀` on the support of `ν`. -/
  col : ∀ y, (recHalf pr hne t).weight y ≠ 0 →
    (recHalf pr hne t).expect (fun x => K (x, y)) = 1 + recU pr hne t y
  /-- `K` accepts the six projected queries (layer `0` to layer `1`) at every prime, on the
  support of `K(ν ⊗ ν)`. -/
  accepts : ∀ x x', (recHalf pr hne t).weight x ≠ 0 → (recHalf pr hne t).weight x' ≠ 0 →
    K (x, x') ≠ 0 → ∀ (j : Chamber) (i : ι),
    quadraticChar (ZMod (pr i))
      (x' (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j)) i -
        x (t.1.pat φ.1 0, t.2.pat φ.2 j) i) = 1
  Cs : ℝ
  Ca : ℝ
  Cs_nonneg : 0 ≤ Cs
  Ca_nonneg : 0 ≤ Ca
  /-- `prop:dense-comparison`(b) / `prop:le-mixture`: the symmetric part, at most `d_s`. -/
  sym : ∀ φ' ψ', |((centredForm (recHalf pr hne t) (recU pr hne t) K φ' ψ' -
      centredForm (recHalf pr hne t) (recU pr hne t)
        (pairDensity (recOld pr hne t) (recHalf pr hne t)) φ' ψ') +
      (centredForm (recHalf pr hne t) (recU pr hne t) K ψ' φ' -
      centredForm (recHalf pr hne t) (recU pr hne t)
        (pairDensity (recOld pr hne t) (recHalf pr hne t)) ψ' φ')) / 2| ≤
    Cs * mnrm (recHalf pr hne t) (recU pr hne t) φ' * mnrm (recHalf pr hne t) (recU pr hne t) ψ'
  /-- The skew part, at most `d_a`. -/
  skew : ∀ φ' ψ', |((centredForm (recHalf pr hne t) (recU pr hne t) K φ' ψ' -
      centredForm (recHalf pr hne t) (recU pr hne t)
        (pairDensity (recOld pr hne t) (recHalf pr hne t)) φ' ψ') -
      (centredForm (recHalf pr hne t) (recU pr hne t) K ψ' φ' -
      centredForm (recHalf pr hne t) (recU pr hne t)
        (pairDensity (recOld pr hne t) (recHalf pr hne t)) ψ' φ')) / 2| ≤
    Ca * mnrm (recHalf pr hne t) (recU pr hne t) φ' * mnrm (recHalf pr hne t) (recU pr hne t) ψ'

namespace KernelInput

variable {pr} {hne : UpperNonempty pr} {t : PType × PType} {φ : t.1.Pat × t.2.Pat}

theorem total (I : KernelInput pr hne t φ) :
    (recHalf pr hne t).expect (fun x => (recHalf pr hne t).expect (fun y => I.K (x, y))) = 1 := by
  rw [expect_congr_supp _ I.row]
  exact recU_mean pr hne t

/-- The two-layer law of the kernel. -/
noncomputable def lam (I : KernelInput pr hne t φ) :
    FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr) :=
  kerLaw (recHalf pr hne t) I.K I.K_nonneg I.total

theorem lam_half0 (I : KernelInput pr hne t φ)
    (g : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) :
    I.lam.expect (fun y => g (layerOf y 0)) =
      (recOld pr hne t).expect (fun y => g (layerOf y 0)) := by
  rw [half_density_lin _ _ (upper_layersSupported pr hne _ _), lam, kerLaw_expect]
  refine expect_congr_supp _ fun x hx => ?_
  simp only [layerOf_glue0]
  rw [← I.row x hx, mul_comm, ← FiniteLaw.expect_const_mul]
  exact (recHalf pr hne t).expect_congr fun y => by ring

theorem lam_half1 (I : KernelInput pr hne t φ)
    (g : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) :
    I.lam.expect (fun y => g (layerOf y 1)) =
      (recOld pr hne t).expect (fun y => g (layerOf y 0)) := by
  rw [half_density_lin _ _ (upper_layersSupported pr hne _ _), lam, kerLaw_expect]
  simp only [layerOf_glue1]
  rw [expect_comm]
  refine expect_congr_supp _ fun y hy => ?_
  rw [← I.col y hy, mul_comm, ← FiniteLaw.expect_const_mul]
  exact (recHalf pr hne t).expect_congr fun x => by ring

theorem cf_lam (I : KernelInput pr hne t φ)
    (φ' ψ' : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) :
    centredForm (recHalf pr hne t) (recU pr hne t) (pairDensity I.lam (recHalf pr hne t)) φ' ψ' =
      centredForm (recHalf pr hne t) (recU pr hne t) I.K φ' ψ' := by
  unfold centredForm
  rw [← pair_density_eq I.lam (recHalf pr hne t) (kerLaw_supported _ _ _ _) φ' ψ', lam,
    kerLaw_pair]

/-- **The replacing law of a dense or mixed record**: the two-layer law of the kernel. -/
noncomputable def toRepl (I : KernelInput pr hne t φ) : ReplRecord pr hne t φ where
  lamN := I.lam
  supp := kerLaw_supported _ _ _ _
  half0 := I.lam_half0
  half1 := I.lam_half1
  accepts y hy j i := by
    have hw := kerLaw_weight_ne_zero _ _ _ _ hy
    have h := I.accepts _ _ hw.1 hw.2.1 hw.2.2 j i
    have h1 : recEm t φ (queryTarget j) = (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j), 1) := by
      change (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j), layerFin 1) = _
      rw [layerFin_one]
    have h2 : recEm t φ (querySource j) = (t.1.pat φ.1 0, t.2.pat φ.2 j, 0) := by
      change (t.1.pat φ.1 0, t.2.pat φ.2 j, layerFin 0) = _
      rw [layerFin_zero]
    rw [h1, h2]
    exact h
  Cs := I.Cs
  Ca := I.Ca
  Cs_nonneg := I.Cs_nonneg
  Ca_nonneg := I.Ca_nonneg
  sym φ' ψ' := by
    unfold recChangeForm
    rw [I.cf_lam, I.cf_lam]
    exact I.sym φ' ψ'
  skew φ' ψ' := by
    unfold recChangeForm
    rw [I.cf_lam, I.cf_lam]
    exact I.skew φ' ψ'

end KernelInput

end Sarkozy.UpperRepair
