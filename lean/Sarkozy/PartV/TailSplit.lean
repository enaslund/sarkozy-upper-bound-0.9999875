module

public import Sarkozy.PartV.TailCoefficients
public import Sarkozy.PartV.Acceptance

@[expose] public section

/-!
# The root and the remainder of the tail law (`lem:tail-law`(iii))

`paper/sections/27_tail_index.tex`, `lem:tail-law`(iii), as used in `lem:record:tail-mixing`:
`μ̃_p = π_{LL,2} + ρ̃_p` with `ρ̃_p ≥ 0` of mass `h_p = P_μ(r) - 1 ≤ C₁ p^{-1/2}`
(`upperTilde_root_split` for every upper law; `tailTilde_split` for the tail law at `p ≥ P₄`).
With `tailRoot_accepts` (the root accepts `𝓔₆`) this is the two-component mixture
`μ_p = ϖ π_{LL,2} + (1 - ϖ) ρ̃_p / h_p`, `ϖ = 1/(1 + h_p)`, of the proof of
`lem:record:tail-mixing`.
-/

namespace Sarkozy.PartV

open Finset

/-- The root index `(LL, (id, id))` of the two-layer upper components. -/
def rootIdx : UpIdx := (true, ⟨(.L, .L), ((), ())⟩)

/-- **`lem:tail-law`(iii), the decomposition**: `μ̃_p = π_{LL,2} + ρ̃_p` with `ρ̃_p ≥ 0` the sum of
all the other weighted components, of mass `h_p = P_μ(r) - 1`. -/
theorem upperTilde_root_split {X : Type*} [Fintype X] [DecidableEq X] (F : UpperFieldLaws X)
    (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) :
    upperTilde F W r = signedIntegral (upComponent F rootIdx).weight +
        ∑ i ∈ univ.erase rootIdx, upCoeff W r i • signedIntegral (upComponent F i).weight ∧
      (∀ f : (Slot → X) → ℝ, (∀ z, 0 ≤ f z) →
        0 ≤ (∑ i ∈ univ.erase rootIdx, upCoeff W r i • signedIntegral (upComponent F i).weight) f) ∧
      (∑ i ∈ univ.erase rootIdx, upCoeff W r i • signedIntegral (upComponent F i).weight)
        (fun _ => 1) = upPoly W r - 1 := by
  have hroot : upCoeff W r rootIdx = 1 := by
    simp [rootIdx, upCoeff, PType.deg, W.w_LL]
  have hsplit : upperTilde F W r =
      upCoeff W r rootIdx • signedIntegral (upComponent F rootIdx).weight +
        ∑ i ∈ univ.erase rootIdx, upCoeff W r i • signedIntegral (upComponent F i).weight := by
    unfold upperTilde tildeMeasure
    rw [← add_sum_erase _ _ (mem_univ rootIdx)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit, hroot, one_smul]
  · intro f hf
    rw [LinearMap.sum_apply]
    refine sum_nonneg fun i _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (upCoeff_nonneg W hr i) ((upComponent F i).expect_nonneg hf)
  · have hmass := (upperTilde_mass F W hr).1
    rw [hsplit, LinearMap.add_apply, hroot, one_smul] at hmass
    have h1 : signedIntegral (upComponent F rootIdx).weight (fun _ => 1) = 1 :=
      (upComponent F rootIdx).expect_const 1
    rw [h1] at hmass
    linarith

/-- **`lem:tail-law`(iii) for the tail law at `p ≥ P₄`**: `μ̃_p = π_{LL,2} + ρ̃_p`, `ρ̃_p ≥ 0` of
mass `h_p` with `0 ≤ h_p ≤ C₁ p^{-1/2}`; the root `π_{LL,2}` accepts `𝓔₆` (`tailRoot_accepts`). -/
theorem tailTilde_split (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (hp : P4 ≤ p) :
    let ρ := ∑ i ∈ univ.erase rootIdx,
      upCoeff tailWeights (tailR p) i • signedIntegral (upComponent (tailFieldLaws p hne) i).weight
    upperTilde (tailFieldLaws p hne) tailWeights (tailR p) =
        signedIntegral (upComponent (tailFieldLaws p hne) rootIdx).weight + ρ ∧
      (∀ f : (Slot → ZMod p) → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ ρ f) ∧
      ρ (fun _ => 1) = upPoly tailWeights (tailR p) - 1 ∧
      0 ≤ ρ (fun _ => 1) ∧ ρ (fun _ => 1) ≤ (tailC 1 : ℝ) * tailR p := by
  intro ρ
  obtain ⟨h1, h2, h3⟩ := upperTilde_root_split (tailFieldLaws p hne) tailWeights (tailR_nonneg p)
  obtain ⟨h4, h5⟩ := tail_nonroot_mass p hp
  exact ⟨h1, h2, h3, h3 ▸ h4, h3 ▸ h5⟩

end Sarkozy.PartV
