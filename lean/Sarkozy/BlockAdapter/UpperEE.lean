module

public import Sarkozy.BlockAdapter.Edgeless
public import Sarkozy.BlockAdapter.UpperLayer
public import Sarkozy.BlockAdapter.EEChecks
public import Sarkozy.PartVLaws.RecordedUpper

@[expose] public section

/-!
# The upper `E × E` layer caps, proved (`lem:upper-reference-rp`(ii), (V3))

`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`(d), (V3), at the recorded caps.

The upper graph `G_{EE,2}` has no edges (`typeE.fwd = false`), so the per-prime cut of its layer
swap is the disjointness cut of `|U⁺| = 9` labels, bounded by `Edgeless.lean`:
`-81/(p - 81) ⪯ A_p ⪯ 1`. With the rational gate `ee_gate` (all 310 bands) and the block adapter
`upLayerCap_of_cutCaps` (with `B = 0`, so no inflation), **`upperLayerCaps_EE`** proves the layer
caps (V3) of the nine `E × E` type pairs `(t₀, t₁)`, `t₀, t₁ ∈ {S, R, C}`, on every block of every
band, at the recorded caps `bandCap k t₀ t₁`.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts Sarkozy.UpperRecords

theorem fieldGraph_EE_empty (Λ : Type) [Fintype Λ] : (fieldGraph .E .E Λ).E = ∅ := by
  ext e
  rw [fieldGraph, mem_twoLayerGraph]
  simp [twoLayerEdge, FType.rel, typeE]

theorem ee_swap : UpSwapInvariant FType.E.Obj FType.E.Obj (fieldGraph .E .E (Fin 2)) := by
  intro u w
  simp [fieldGraph_EE_empty]

theorem ee_restricts : UpLayerRestricts FType.E.Obj FType.E.Obj (fieldGraph .E .E (Fin 2))
    (fieldGraph .E .E (Fin 1)) := by
  intro a a' b b'
  simp [fieldGraph_EE_empty]

/-- The spectral data of the layer cut of `G_{EE,2}`. -/
noncomputable abbrev eeLayer : SpecData (FType.E.Obj × FType.E.Obj × Fin 2) :=
  upLayerData FType.E.Obj FType.E.Obj (fieldGraph .E .E (Fin 2)) ee_swap

theorem card_eeHalf : (Fintype.card eeLayer.cut.Half : ℝ) ^ 2 = 81 := by
  rw [Fintype.card_congr (upHalfEquiv FType.E.Obj FType.E.Obj (fieldGraph .E .E (Fin 2)) ee_swap)]
  have h : Fintype.card (FType.E.Obj × FType.E.Obj × Fin 1) = 9 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
  rw [h]
  norm_num

/-- **The `E × E` layer cap on a block of band `k`** at the recorded cap of `(t₀, t₁)`, for any
patterns `φ₀, φ₁`. -/
theorem eeLayerCap (k : Fin 310) {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    [∀ j, Fact (pr j).Prime] (b : ℕ) (hband : ∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2)
    (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b) (hne : UpperNonempty pr) (t₀ t₁ : PType)
    (hok : EEOK (CompletionData.record k) t₀ t₁) (φ₀ φ₁ : ZMod 6 → FType.E.Obj) :
    reservedCut.Below
      (-(bandCap k t₀ t₁ * (b : ℝ) ^ (-(1 / 2 : ℝ))) •
        signedIntegral (emit (blockGraphLaw pr (fieldGraph .E .E (Fin 1)) (hne.one .E .E))
          (upDiagEmission φ₀ φ₁)).weight)
      (signedIntegral (emit (blockGraphLaw pr (fieldGraph .E .E (Fin 2)) (hne.two .E .E))
        (upEmission φ₀ φ₁)).weight) := by
  have hstart : (CompletionData.record k).start = (bandOf k).1 :=
    congrArg Prod.fst (CompletionData.record_endpoints k)
  have h6561 : 6561 ≤ (CompletionData.record k).start := (ee_gate k).1
  set g : ℝ := bandCap k t₀ t₁ with hgdef
  set X : ℝ := ((CompletionData.record k).start : ℝ) with hXdef
  have hg0 : 0 < g := bandCap_pos k t₀ t₁
  have hgq : g = ((CompletionData.record k).cap t₀ t₁ : ℝ) := rfl
  have hg1 : g ≤ 1 := by
    rw [hgq]
    exact_mod_cast hok.1
  have hgX : (81 + g) ^ 2 ≤ g ^ 2 * X := by
    have h := (Rat.cast_le (K := ℝ)).mpr hok.2
    push_cast at h
    rw [hgq, hXdef]
    nlinarith [h]
  have hX81 : (81 : ℝ) ^ 2 ≤ X := by
    rw [hXdef]
    have : ((6561 : ℕ) : ℝ) ≤ ((CompletionData.record k).start : ℝ) := by exact_mod_cast h6561
    norm_num at this ⊢
    linarith
  have hXp : ∀ j, X ≤ pr j := fun j => by
    rw [hXdef, hstart]
    exact_mod_cast (hband j).1
  have hX1 : (1 : ℝ) < X := by nlinarith
  have hXb : X ≤ b := by
    obtain ⟨j₀, hj₀⟩ := hb'
    rw [← hj₀]
    exact hXp j₀
  have hgate : ∀ j, (81 : ℝ) < pr j ∧ 81 / ((pr j : ℝ) - 81) ≤ g * (√(pr j : ℝ))⁻¹ := fun j =>
    edgeless_gate hg0 hg1 (by norm_num) hX81 hgX (hXp j)
  have hcap : ∀ j v, -(g * (√(pr j : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
        ⟪v, Spectral.cutOp eeLayer (hne.two .E .E j) v⟫_ℝ ∧
      ⟪v, Spectral.cutOp eeLayer (hne.two .E .E j) v⟫_ℝ ≤ (1 + 0 / pr j) * ‖v‖ ^ 2 := by
    intro j v
    refine edgeless_cutCap eeLayer (fieldGraph_EE_empty (Fin 2)) le_rfl ?_ ?_ (hne.two .E .E j) v
    · rw [card_eeHalf]
      exact (hgate j).1
    · rw [card_eeHalf]
      exact (hgate j).2
  have hgp : ∀ j, g * (√(pr j : ℝ))⁻¹ < 1 := by
    intro j
    have hs : (1 : ℝ) < √(pr j : ℝ) := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [hXp j])
    have hspos : 0 < √(pr j : ℝ) := by linarith
    rw [← div_eq_mul_inv, div_lt_one hspos]
    linarith
  have h := upLayerCap_of_cutCaps FType.E.Obj FType.E.Obj pr (fieldGraph .E .E (Fin 2)) ee_swap
    (fieldGraph .E .E (Fin 1)) ee_restricts (hne.two .E .E) (hne.one .E .E) φ₀ φ₁ hg0.le le_rfl
    hX1 hXb (fun j => by exact_mod_cast hb j) le_rfl hgp (fun j v => (hcap j v).1)
    (fun j v => (hcap j v).2)
  rw [zero_mul, zero_div, Real.exp_zero, mul_one] at h
  rw [rpow_neg_half_eq]
  exact h

/-- The nine `E × E` type pairs. -/
def IsEE (t : PType × PType) : Prop :=
  (t.1 = .S ∨ t.1 = .R ∨ t.1 = .C) ∧ (t.2 = .S ∨ t.2 = .R ∨ t.2 = .C)

theorem eeOK_of_gate (k : Fin 310) (t : PType × PType) (ht : IsEE t) :
    EEOK (CompletionData.record k) t.1 t.2 := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ee_gate k
  rcases t with ⟨t₀, t₁⟩
  rcases ht with ⟨h0 | h0 | h0, h1' | h1' | h1'⟩ <;> simp only at h0 h1' <;> subst h0 h1' <;>
    assumption

/-- **The upper layer caps (V3) of the nine `E × E` type pairs**, on every block of band `k`, at
the recorded caps: no hypothesis. -/
theorem upperLayerCaps_EE (k : Fin 310) {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    [∀ j, Fact (pr j).Prime] (b : ℕ) (hband : ∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2)
    (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b) (hne : UpperNonempty pr)
    (t : PType × PType) (φ : t.1.Pat × t.2.Pat) (ht : IsEE t) :
    reservedCut.Below
      (-(bandCap k t.1 t.2 * (b : ℝ) ^ (-(1 / 2 : ℝ))) •
        signedIntegral (upComponent (upperBlockFieldLaws pr hne) (false, ⟨t, φ⟩)).weight)
      (signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight) := by
  have hok := eeOK_of_gate k t ht
  rcases t with ⟨t₀, t₁⟩
  rcases ht with ⟨h0 | h0 | h0, h1 | h1 | h1⟩ <;> simp only at h0 h1 <;> subst h0 h1 <;>
    exact eeLayerCap k pr b hband hb hb' hne _ _ hok _ _

end Sarkozy.BlockAdapter
