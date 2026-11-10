module

public import Sarkozy.PartV.UpperReference
public import Sarkozy.PartV.MiddleReference
public import Sarkozy.TheoremC.Defs

@[expose] public section

/-!
# Positivity of the reference laws at the reserved cut `ι` (fold pairing)

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(iii), paragraph "The reserved
cut"; `paper/sections/17_completion_repair.tex`, `lem:five-type`(e) (fold pairing, the step used
there); `paper/sections/25_upper_reference.tex`, `def:record:upper-bands`(d),
`eq:independent-fold-domination`.

**The step.** If every two-layer component is bounded below at `ι` by `-k_𝔱 r` times the diagonal
copy of its one-layer component, `Π_{𝔱,φ} ⪰_ι -k_𝔱 r Diag_ι(Π⁽¹⁾_{𝔱,φ})` (the third display of
`lem:front12:reference`(ii); for the upper law the layer caps of the band), and the one-layer
weights dominate, `v_𝔱 ≥ k_𝔱 w_𝔱` (the third line of the thirteen inequalities;
`eq:independent-fold-domination`), then
`w_𝔱 r^d Π + v_𝔱 r^{d+1} D = w_𝔱 r^d (Π + k_𝔱 r D) + (v_𝔱 - k_𝔱 w_𝔱) r^{d+1} D ⪰_ι 0`,
because a diagonal copy is positive at `ι`. Summing over the components gives `μ̃ ⪰_ι 0`.

Proved here, with the caps as hypotheses (`MiddleLayerCaps`, `UpperLayerCaps`):
* `middleTilde_reserved_positive`, `middleReference_reserved_positive`;
* `upperTilde_reserved_positive`, `upperReference_reserved_positive`;
* `middleReference_familyPositive`: the middle law is reflection positive at every cut of the
  family `𝔉` (`TheoremC.FamilyReflectionPositive`, (R2)) as soon as it is positive at the chamber
  cuts of the first coordinate; the second-coordinate cuts are proved
  (`middleReference_secondCut_positive`) and `ι` comes from the caps. The first-coordinate cuts
  are the five-type criterion `lem:five-type`(b) with the rows (i) and the root envelopes (ii) of
  `lem:front12:reference`; they are supplied in `Sarkozy.PartV.ChamberCut`.

The caps themselves (the spectral bounds of the twelve-label and two-layer cuts) are the large
spectral inputs of Part V and remain hypotheses.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## The middle law -/

/-- **The layer caps of the middle components** (`lem:front12:reference`(ii), third display):
`Π_φ ⪰_ι -k_𝔱 r Diag_ι(Π⁽¹⁾_φ)` for every two-layer component of type `𝔱`, the root included. -/
def MiddleLayerCaps (F : MiddleFieldLaws X) (k : PType → ℝ) (r : ℝ) : Prop :=
  ∀ (t : PType) (φ : t.Pat),
    reservedCut.Below (-(k t * r) • signedIntegral (midComponent F (false, ⟨t, φ⟩)).weight)
      (signedIntegral (midComponent F (true, ⟨t, φ⟩)).weight)

/-- **Fold pairing at `ι` for the middle law**: under the layer caps and `v_𝔱 ≥ k_𝔱 w_𝔱`,
`μ̃_𝔅 ⪰_ι 0` (`lem:front12:reference`(iii), "The reserved cut"). -/
theorem middleTilde_reserved_positive (F : MiddleFieldLaws X) (W : MiddleWeights)
    (k : PType → ℝ) {r : ℝ} (hr : 0 ≤ r) (hcap : MiddleLayerCaps F k r)
    (hdom : ∀ t, k t * W.w t ≤ W.v t) : reservedCut.Positive (middleTilde F W r) := by
  unfold middleTilde tildeMeasure
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← sum_add_distrib]
  refine ReflectionCut.Positive.sum _ fun s _ => ?_
  rcases s with ⟨t, φ⟩
  set A := signedIntegral (midComponent F (true, ⟨t, φ⟩)).weight
  set B := signedIntegral (midComponent F (false, ⟨t, φ⟩)).weight
  have key : midCoeff W r (true, ⟨t, φ⟩) • A + midCoeff W r (false, ⟨t, φ⟩) • B =
      (W.w t * r ^ t.deg) • (A - (-(k t * r)) • B) +
        ((W.v t - k t * W.w t) * r ^ (t.deg + 1)) • B := by
    apply LinearMap.ext
    intro f
    simp only [midCoeff, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      smul_eq_mul, pow_succ]
    ring
  rw [key]
  refine ((hcap t φ).smul (mul_nonneg (W.w_nonneg t) (pow_nonneg hr _))).add
    ((middleDiag_reserved_positive F t φ).smul
      (mul_nonneg (sub_nonneg.mpr (hdom t)) (pow_nonneg hr _)))

/-- **The normalized middle law is positive at `ι`** under the layer caps and `v_𝔱 ≥ k_𝔱 w_𝔱`. -/
theorem middleReference_reserved_positive (F : MiddleFieldLaws X) (W : MiddleWeights)
    (k : PType → ℝ) {r : ℝ} (hr : 0 ≤ r) (hcap : MiddleLayerCaps F k r)
    (hdom : ∀ t, k t * W.w t ≤ W.v t) :
    reservedCut.Positive (signedIntegral (middleReference F W hr).weight) := by
  rw [middleReference_eq]
  exact (middleTilde_reserved_positive F W k hr hcap hdom).smul
    (inv_nonneg.mpr (le_trans zero_le_one (one_le_midPoly W hr)))

/-- **(R2) for the middle law, reduced to the first-coordinate chamber cuts**: positivity at every
cut of the family `𝔉` follows from positivity at the chamber cuts of the first coordinate
(`lem:five-type`(b), see `ChamberCut`), the layer caps at `ι` and `v_𝔱 ≥ k_𝔱 w_𝔱`; the
second-coordinate cuts hold for every middle law. -/
theorem middleReference_familyPositive (F : MiddleFieldLaws X) (W : MiddleWeights)
    (k : PType → ℝ) {r : ℝ} (hr : 0 ≤ r) (hcap : MiddleLayerCaps F k r)
    (hdom : ∀ t, k t * W.w t ≤ W.v t)
    (hfirst : ∀ a, (firstChamberCut a).Positive (signedIntegral (middleReference F W hr).weight)) :
    TheoremC.FamilyReflectionPositive (signedIntegral (middleReference F W hr).weight) := by
  intro c hc
  rcases hc with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact hfirst a
  · exact middleReference_secondCut_positive F W hr a
  · exact middleReference_reserved_positive F W k hr hcap hdom

/-! ## The upper law -/

/-- **The layer caps of the upper components**: `Π_{𝔱,φ} ⪰_ι -k_𝔱 r Diag_ι(Π⁽¹⁾_{𝔱,φ})` for every
state `𝔱` and pattern pair `φ` (the reserved caps `k_𝔱` of `def:record:upper-bands`(c)). -/
def UpperLayerCaps (F : UpperFieldLaws X) (k : PType → PType → ℝ) (r : ℝ) : Prop :=
  ∀ (t : PType × PType) (φ : t.1.Pat × t.2.Pat),
    reservedCut.Below (-(k t.1 t.2 * r) • signedIntegral (upComponent F (false, ⟨t, φ⟩)).weight)
      (signedIntegral (upComponent F (true, ⟨t, φ⟩)).weight)

/-- **Fold pairing at `ι` for the upper law**: under the layer caps and the domination
`v_𝔱 ≥ k_𝔱 w_𝔱` (`eq:independent-fold-domination`), `μ̃_𝔅 ⪰_ι 0`. -/
theorem upperTilde_reserved_positive (F : UpperFieldLaws X) (W : UpperWeights)
    (k : PType → PType → ℝ) {r : ℝ} (hr : 0 ≤ r) (hcap : UpperLayerCaps F k r)
    (hdom : ∀ t₀ t₁, k t₀ t₁ * W.w t₀ t₁ ≤ W.v t₀ t₁) :
    reservedCut.Positive (upperTilde F W r) := by
  unfold upperTilde tildeMeasure
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← sum_add_distrib]
  refine ReflectionCut.Positive.sum _ fun s _ => ?_
  rcases s with ⟨t, φ⟩
  set A := signedIntegral (upComponent F (true, ⟨t, φ⟩)).weight
  set B := signedIntegral (upComponent F (false, ⟨t, φ⟩)).weight
  have key : upCoeff W r (true, ⟨t, φ⟩) • A + upCoeff W r (false, ⟨t, φ⟩) • B =
      (W.w t.1 t.2 * r ^ (t.1.deg + t.2.deg)) • (A - (-(k t.1 t.2 * r)) • B) +
        ((W.v t.1 t.2 - k t.1 t.2 * W.w t.1 t.2) * r ^ (t.1.deg + t.2.deg + 1)) • B := by
    apply LinearMap.ext
    intro f
    simp only [upCoeff, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      smul_eq_mul, pow_succ]
    ring
  rw [key]
  refine ((hcap t φ).smul (mul_nonneg (W.w_nonneg _ _) (pow_nonneg hr _))).add
    ((upperDiag_reserved_positive F t φ).smul
      (mul_nonneg (sub_nonneg.mpr (hdom _ _)) (pow_nonneg hr _)))

theorem upperReference_reserved_positive (F : UpperFieldLaws X) (W : UpperWeights)
    (k : PType → PType → ℝ) {r : ℝ} (hr : 0 ≤ r) (hcap : UpperLayerCaps F k r)
    (hdom : ∀ t₀ t₁, k t₀ t₁ * W.w t₀ t₁ ≤ W.v t₀ t₁) :
    reservedCut.Positive (signedIntegral (upperReference F W hr).weight) := by
  rw [upperReference_eq]
  exact (upperTilde_reserved_positive F W k hr hcap hdom).smul
    (inv_nonneg.mpr (le_trans zero_le_one (one_le_upPoly W hr)))

/-- **The tail datum's domination, as used here**: `v_𝔱 ≥ k_𝔱 w_𝔱` with the caps of the tail datum
(from `tailDatum_gates`), so the tail law is positive at `ι` as soon as its layer caps hold. -/
theorem tailWeights_dom (t₀ t₁ : PType) :
    ((tailFieldCap t₀.field t₁.field : ℚ) : ℝ) * tailWeights.w t₀ t₁ ≤ tailWeights.v t₀ t₁ := by
  have h := tailDatum_gates.2.2 t₀ t₁
  change ((tailFieldCap t₀.field t₁.field : ℚ) : ℝ) * ((tailW t₀ t₁ : ℚ) : ℝ) ≤
    ((tailV t₀ t₁ : ℚ) : ℝ)
  exact_mod_cast h

/-- **The tail law is positive at `ι`** when its two-layer components satisfy the layer caps
`k_𝔱 = k_{𝔣(𝔱)}` of the tail datum (`lem:tail-law`(ii), the reserved cut, with the caps as a
hypothesis). -/
theorem tailLaw_reserved_positive (p : ℕ) [Fact p.Prime] (hne : TailNonempty p)
    (hcap : UpperLayerCaps (tailFieldLaws p hne)
      (fun t₀ t₁ => ((tailFieldCap t₀.field t₁.field : ℚ) : ℝ)) (tailR p)) :
    reservedCut.Positive (signedIntegral (tailLaw p hne).weight) :=
  upperReference_reserved_positive _ _ _ (tailR_nonneg p) hcap tailWeights_dom

end Sarkozy.PartV
