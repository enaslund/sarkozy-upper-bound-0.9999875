module

public import Sarkozy.DensityMoments.CoupledSlots
public import Sarkozy.DensityMoments.Unconditional
public import Sarkozy.DensityMoments.MiddleCatalog72
public import Sarkozy.DensityMoments.PacketsBridge

/-!
# The moment inputs of `lem:density:coupled` from M1's unconditional moments

`paper/sections/31_density_induction_upgrade.tex`, `lem:density:coupled`: the folded laws `λ_±`
of a sharp law and the positive spectator `κ` need unit mixed `L^{d/θ}` (`d = 72`). M1's
`DensityMoments.coupled_spectator_estimate_sharpDecomp` states these hypotheses with
`coupledUnitMixedV (72/θ)` on weights; M1's moment theorems are stated with `MixedLpBound` on
finite laws at fixed exponents. This file connects the two:

* `coupledLpNorm_eq_lpNorm`, `coupledUnitMixedV_iff_mixedLpBound`,
  `coupledUnitMixedV_of_mixedLpBound`: the two definitions of the unit mixed norm agree;
* `le_72_div_of_le_densityExponent`, `mixedLpBound_72_div`: a unit mixed `L^p` bound with
  `p ϑ ≤ 72` gives unit mixed `L^{72/θ}` for every `0 < θ ≤ ϑ = densityExponent`
  (`MixedLpBound.mono_exponent`);
* the instances, all with no named inputs beyond the range of the prime:
  - `cliqueIidLaw_moment_72`, `tensor_cliqueIidLaw_moment_72`, `cliqueCopyLaw_moment_72`: the
    prefix factors (`thm:density:iid-prefix`(b), exponent `1200/17`);
  - `catalog72_root_72`, `catalog72_folded_root_72` and the other rows (`…_fold_two_72`,
    `…_fold_one_72`, `…_matching_two_72`, `…_matching_one_72`, `…_merge_two_72`,
    `…_merge_one_72`, `…_const_two_72`): `lem:density:middle-catalog` on the 72 slots (exponents
    `69` and `66`);
  - `middle_packet_12`: the packet gate `lem:density:joint-block-gate` on its twelve effective
    slots, at `12/θ` for `θ ≤ θ_*` (`middle_packet_unit_mixed_proved`);
  - `middle_packet_72`: the same packet emitted to the 72 slots, each label read by at most six
    slots, at `72/θ`. It uses `mixedLpBound_emit` (emission multiplies the exponent by the
    multiplicity; Hölder in each fibre, `lpNorm_prod_le_prod`).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.DensityUpgrade Sarkozy.DensityMoments Sarkozy.PartV

/-! ## The two unit mixed norms -/

/-- M1's `coupledLpNorm` is the uniform `L^r` norm. -/
theorem coupledLpNorm_eq_lpNorm {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) (f : X → ℝ) :
    coupledLpNorm r f = (FiniteLaw.uniform X).lpNorm r f := by
  unfold coupledLpNorm coupledMean FiniteLaw.lpNorm FiniteLaw.moment
  rw [FiniteLaw.expect_uniform]

/-- **The two unit mixed norms agree** for the weights of a finite law. -/
theorem coupledUnitMixedV_iff_mixedLpBound {V X : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Nonempty X] (μ : FiniteLaw (V → X)) (r : ℝ) :
    coupledUnitMixedV r (fun x => μ.weight x) ↔ MixedLpBound μ r 1 := by
  unfold coupledUnitMixedV MixedLpBound
  simp only [one_mul, coupledLpNorm_eq_lpNorm]
  rfl

/-- A unit mixed bound of a finite law gives M1's hypothesis for any weight equal to its
weights (for instance the normalized folded laws `foldedLawPlus c π κs`). -/
theorem coupledUnitMixedV_of_mixedLpBound {V X : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Nonempty X] (μ : FiniteLaw (V → X)) {π : (V → X) → ℝ}
    (hπ : ∀ x, π x = μ.weight x) {r : ℝ} (h : MixedLpBound μ r 1) : coupledUnitMixedV r π := by
  have he : π = fun x => μ.weight x := funext hπ
  rw [he]
  exact (coupledUnitMixedV_iff_mixedLpBound μ r).mpr h

/-! ## From a fixed exponent to `72/θ` -/

/-- `p ≤ 72/θ` whenever `p ϑ ≤ 72` and `0 < θ ≤ ϑ`. -/
theorem le_72_div_of_le_densityExponent {p θ : ℝ} (hp0 : 0 ≤ p) (hp : p * densityExponent ≤ 72)
    (hθ : 0 < θ) (hθe : θ ≤ densityExponent) : p ≤ 72 / θ := by
  rw [le_div_iff₀ hθ]
  calc p * θ ≤ p * densityExponent := mul_le_mul_of_nonneg_left hθe hp0
    _ ≤ 72 := hp

/-- **A unit mixed `L^p` bound with `p ϑ ≤ 72` gives unit mixed `L^{72/θ}`** for every
`0 < θ ≤ ϑ`. -/
theorem mixedLpBound_72_div {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]
    {μ : FiniteLaw (V → X)} {p θ : ℝ} (h : MixedLpBound μ p 1) (hp0 : 0 < p)
    (hp : p * densityExponent ≤ 72) (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound μ (72 / θ) 1 :=
  h.mono_exponent zero_le_one hp0 (le_72_div_of_le_densityExponent hp0.le hp hθ hθe)

theorem exponent_1200_17 : (1200 / 17 : ℝ) * densityExponent ≤ 72 := by
  norm_num [densityExponent]

theorem exponent_69 : (69 : ℝ) * densityExponent ≤ 72 := by
  norm_num [densityExponent]

theorem exponent_66 : (66 : ℝ) * densityExponent ≤ 72 := by
  norm_num [densityExponent]

/-! ## The prefix factors (`thm:density:iid-prefix`(b)) -/

section Prefix

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ)

/-- **The clique-iid prefix law at `72/θ`**, unconditional. -/
theorem cliqueIidLaw_moment_72 (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512) {θ : ℝ}
    (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (cliqueIidLaw p ℓ) (72 / θ) 1 :=
  mixedLpBound_72_div (cliqueIidLaw_moment_proved p ℓ hp2 h16 h512) (by norm_num)
    exponent_1200_17 hθ hθe

/-- **The copies of clique draws at `72/θ`**, unconditional. -/
theorem cliqueCopyLaw_moment_72 (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512)
    {T : Type*} [Fintype T] [DecidableEq T] (σ : Slot → T)
    (hσ : ∀ t, (univ.filter (fun v => σ v = t)).card ≤ 2) {θ : ℝ} (hθ : 0 < θ)
    (hθe : θ ≤ densityExponent) :
    MixedLpBound (DensityMoments.cliqueCopyLaw p ℓ σ) (72 / θ) 1 :=
  mixedLpBound_72_div (cliqueCopyLaw_moment_proved p ℓ hp2 h16 h512 σ hσ) (by norm_num)
    exponent_1200_17 hθ hθe

end Prefix

/-- **The tensor product of clique-iid prefix laws at `72/θ`**, unconditional. -/
theorem tensor_cliqueIidLaw_moment_72 {J : Type*} [Fintype J] [DecidableEq J] (P : J → ℕ)
    [∀ j, Fact (P j).Prime] (L : J → ℕ) (hp2 : ∀ j, P j ≠ 2) (h16 : ∀ j, 2 ^ 16 ≤ P j)
    (h512 : ∀ j, P j < 2 ^ 512) {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (FiniteLaw.tensor (fun j => cliqueIidLaw (P j) (L j))) (72 / θ) 1 :=
  mixedLpBound_72_div (tensor_cliqueIidLaw_moment_proved P L hp2 h16 h512) (by norm_num)
    exponent_1200_17 hθ hθe

/-! ## The middle catalog on the 72 slots (`lem:density:middle-catalog`) -/

section Catalog

variable {p : ℕ} [Fact p.Prime]

/-- **The two-layer root at `72/θ`** (`catalog72_root`, exponent `69`). -/
theorem catalog72_root_72 (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p)
    (lam : FiniteLaw (ZMod 6 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : ZMod 6 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (emit lam (midEmission (fun u : ZMod 6 => u))) (72 / θ) 1 :=
  mixedLpBound_72_div (catalog72_root hp2 hp64 lam hdist hinv hunif) (by norm_num) exponent_69
    hθ hθe

/-- **The folded root at `72/θ`** (`catalog72_folded_root`, exponent `66`). -/
theorem catalog72_folded_root_72 (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p)
    (lam : FiniteLaw (ZMod 6 × Fin 1 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : ZMod 6 × Fin 1) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (emit lam (midDiagEmission (fun u : ZMod 6 => u))) (72 / θ) 1 :=
  mixedLpBound_72_div (catalog72_folded_root hp2 hp64 lam hdist hinv hunif) (by norm_num)
    exponent_66 hθ hθe

/-- `catalog72_fold_two` at `72/θ` (exponent `66`). -/
theorem catalog72_fold_two_72
    (hp2 : p ≠ 2)
    (hp64 : (64 : ℝ) ≤ p)
    (jf : Fin 3)
    (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (emit lam (midEmission (Labellings.fold jf))) (72 / θ) 1 :=
  mixedLpBound_72_div (catalog72_fold_two hp2 hp64 jf lam hdist hinv hunif)
    (by norm_num) exponent_66 hθ hθe

/-- `catalog72_fold_one` at `72/θ` (exponent `66`). -/
theorem catalog72_fold_one_72
    (hp2 : p ≠ 2)
    (hp64 : (64 : ℝ) ≤ p)
    (jf : Fin 3)
    (lam : FiniteLaw (Fin 3 × Fin 1 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 1) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (emit lam (midDiagEmission (Labellings.fold jf))) (72 / θ) 1 :=
  mixedLpBound_72_div (catalog72_fold_one hp2 hp64 jf lam hdist hinv hunif)
    (by norm_num) exponent_66 hθ hθe

/-- `catalog72_matching_two` at `72/θ` (exponent `66`). -/
theorem catalog72_matching_two_72
    (hp2 : p ≠ 2)
    (hp64 : (64 : ℝ) ≤ p)
    (sm : Fin 2)
    (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (emit lam (midEmission (Labellings.matching sm))) (72 / θ) 1 :=
  mixedLpBound_72_div (catalog72_matching_two hp2 hp64 sm lam hdist hinv hunif)
    (by norm_num) exponent_66 hθ hθe

/-- `catalog72_matching_one` at `72/θ` (exponent `66`). -/
theorem catalog72_matching_one_72
    (hp2 : p ≠ 2)
    (hp64 : (64 : ℝ) ≤ p)
    (sm : Fin 2)
    (lam : FiniteLaw (Fin 3 × Fin 1 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 1) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (emit lam (midDiagEmission (Labellings.matching sm))) (72 / θ) 1 :=
  mixedLpBound_72_div (catalog72_matching_one hp2 hp64 sm lam hdist hinv hunif)
    (by norm_num) exponent_66 hθ hθe

/-- `catalog72_merge_two` at `72/θ` (exponent `66`). -/
theorem catalog72_merge_two_72
    (hp2 : p ≠ 2)
    (hp64 : (64 : ℝ) ≤ p)
    (sk : Fin 2 × Fin 3)
    (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (emit lam (midEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc)))
      (72 / θ) 1 :=
  mixedLpBound_72_div (catalog72_merge_two hp2 hp64 sk lam hdist hinv hunif)
    (by norm_num) exponent_66 hθ hθe

/-- `catalog72_merge_one` at `72/θ` (exponent `66`). -/
theorem catalog72_merge_one_72
    (hp2 : p ≠ 2)
    (hp64 : (64 : ℝ) ≤ p)
    (sk : Fin 2 × Fin 3)
    (lam : FiniteLaw (Fin 3 × Fin 1 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 1) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound
      (emit lam (midDiagEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc)))
      (72 / θ) 1 :=
  mixedLpBound_72_div (catalog72_merge_one hp2 hp64 sk lam hdist hinv hunif)
    (by norm_num) exponent_66 hθ hθe

/-- `catalog72_const_two` at `72/θ` (exponent `66`). -/
theorem catalog72_const_two_72
    (hp2 : p ≠ 2)
    (hp64 : (64 : ℝ) ≤ p)
    (c : Fin 2)
    (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ densityExponent) :
    MixedLpBound (emit lam (midEmission (fun _ : ZMod 6 => (0 : Fin 3)))) (72 / θ) 1 :=
  mixedLpBound_72_div (catalog72_const_two hp2 hp64 c lam hdist hinv hunif)
    (by norm_num) exponent_66 hθ hθe

end Catalog

/-! ## The packet gate on its twelve effective slots (`lem:density:joint-block-gate`) -/

/-- **A certified packet at `12/θ`** for `0 < θ ≤ θ_*`, on the twelve effective slots of one
prime coordinate (`middle_packet_unit_mixed_proved`, with `R_* = 12/θ_*`). -/
theorem middle_packet_12 {row : GateRow} (hrow : row ∈ gateRows) {b : ℝ}
    (hb : (row.beta : ℝ) ≤ b) {X : Type*} [Fintype X] [Nonempty X] (hQ : 2 ≤ Fintype.card X)
    (hL : Real.log (Fintype.card X) ≤ row.L) {good bad packet : FiniteLaw (Fin 12 → X)}
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ht : t ≤ (packetPiece row.piece).sym (1 / Real.sqrt b) ∨
      t ≤ (packetPiece row.piece).skew (1 / Real.sqrt b))
    (hgood : blockGateUnitMixed good 11) (hbad : HasUniformMarginals bad)
    (hpacket : ∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ blockGateTheta) :
    MixedLpBound packet (12 / θ) 1 := by
  have h := middle_packet_unit_mixed_proved hrow hb hQ hL ht0 ht1 ht hgood hbad hpacket
  have hT : (0 : ℝ) < blockGateTheta := by norm_num [blockGateTheta]
  refine h.2.mono_exponent zero_le_one (by unfold blockGateR; positivity) ?_
  unfold blockGateR
  exact div_le_div_of_nonneg_left (by norm_num) hθ hθe

/-! ## Emission: every label read by at most `t` slots -/

section Emission

/-- **Hölder for a product** under a finite law: `‖∏_k h_k‖_r ≤ ∏_k ‖h_k‖_{r |K|}`. -/
theorem lpNorm_prod_le_prod {Ω K : Type*} [Fintype Ω] [Fintype K] [Nonempty K]
    (μ : FiniteLaw Ω) {r : ℝ} (hr : 0 < r) (h : K → Ω → ℝ) :
    μ.lpNorm r (fun x => ∏ k, h k x) ≤ ∏ k, μ.lpNorm (r * Fintype.card K) (h k) := by
  set n : ℝ := (Fintype.card K : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  have hrn : 0 < r * n := mul_pos hr hn
  have hP : 0 ≤ ∏ k, μ.lpNorm (r * n) (h k) := Finset.prod_nonneg fun k _ => μ.lpNorm_nonneg _ _
  -- the moment of the product
  have hpoint : ∀ x, |∏ k, h k x| ^ r = ∏ k, |h k x| ^ r := fun x => by
    rw [Finset.abs_prod]
    exact (Real.finsetProd_rpow Finset.univ (fun k => |h k x|) (fun k _ => abs_nonneg _) r).symm
  have hnorm : ∀ k, μ.lpNorm n (fun x => |h k x| ^ r) = μ.lpNorm (r * n) (h k) ^ r := by
    intro k
    unfold FiniteLaw.lpNorm FiniteLaw.moment
    have he : ∀ x, |(|h k x| ^ r)| ^ n = |h k x| ^ (r * n) := fun x => by
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_mul (abs_nonneg _)]
    simp only [he]
    rw [← Real.rpow_mul (μ.expect_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _)]
    congr 1
    field_simp
  have hmom : μ.moment r (fun x => ∏ k, h k x) ≤ (∏ k, μ.lpNorm (r * n) (h k)) ^ r := by
    unfold FiniteLaw.moment
    simp only [hpoint]
    have hH := μ.abs_expect_prod_le_lpNorm (fun _ : K => n) (fun _ => hn)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn_def]; field_simp)
      (fun k x => |h k x| ^ r)
    simp only [hnorm] at hH
    rw [← Real.finsetProd_rpow Finset.univ _ (fun k _ => μ.lpNorm_nonneg _ _) r]
    exact (le_abs_self _).trans hH
  unfold FiniteLaw.lpNorm at hP ⊢
  calc μ.moment r (fun x => ∏ k, h k x) ^ (1 / r)
      ≤ ((∏ k, μ.moment (r * n) (h k) ^ (1 / (r * n))) ^ r) ^ (1 / r) :=
        Real.rpow_le_rpow (μ.moment_nonneg _ _) hmom (by positivity)
    _ = ∏ k, μ.moment (r * n) (h k) ^ (1 / (r * n)) := by
        rw [← Real.rpow_mul hP, mul_one_div_cancel hr.ne', Real.rpow_one]

/-- Hölder for a product over a nonempty finset: `‖∏_{k ∈ s} h_k‖_r ≤ ∏_{k ∈ s} ‖h_k‖_{r |s|}`. -/
theorem lpNorm_finset_prod_le {Ω K : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (s : Finset K)
    (hs : s.Nonempty) {r : ℝ} (hr : 0 < r) (h : K → Ω → ℝ) :
    μ.lpNorm r (fun x => ∏ k ∈ s, h k x) ≤ ∏ k ∈ s, μ.lpNorm (r * s.card) (h k) := by
  have : Nonempty {k // k ∈ s} := hs.coe_sort
  have h1 := lpNorm_prod_le_prod μ hr (fun k : {k // k ∈ s} => h k.1)
  rw [Fintype.card_coe] at h1
  have e1 : ∀ x, ∏ k ∈ s, h k x = ∏ k : {k // k ∈ s}, h k.1 x := fun x =>
    Finset.prod_subtype s (fun _ => Iff.rfl) (fun k => h k x)
  have e2 : ∏ k ∈ s, μ.lpNorm (r * s.card) (h k) =
      ∏ k : {k // k ∈ s}, μ.lpNorm (r * s.card) (h k.1) :=
    Finset.prod_subtype s (fun _ => Iff.rfl) _
  simp only [e1, e2]
  exact h1

/-- **Emission preserves unit mixed bounds, with the exponent multiplied by the multiplicity**:
if every label is read by at most `t` slots, unit mixed `L^r` of `μ` gives unit mixed `L^{t r}`
of the emitted law. -/
theorem mixedLpBound_emit {I V X : Type*} [Fintype I] [DecidableEq I] [Fintype V]
    [DecidableEq V] [Fintype X] [DecidableEq X] [Nonempty X] (μ : FiniteLaw (I → X))
    (π : V → I) {r : ℝ} (hr : 0 < r) {t : ℕ}
    (ht : ∀ i, (Finset.univ.filter (fun v => π v = i)).card ≤ t) (h : MixedLpBound μ r 1) :
    MixedLpBound (μ.map (fun y v => y (π v))) (t * r) 1 := by
  intro f
  have hfib : ∀ y : I → X, ∏ v, f v (y (π v)) =
      ∏ i, ∏ v ∈ Finset.univ.filter (fun v => π v = i), f v (y i) := by
    intro y
    rw [← Finset.prod_fiberwise Finset.univ π (fun v => f v (y (π v)))]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v hv => ?_
    rw [(Finset.mem_filter.mp hv).2]
  have hgi : ∀ i, (FiniteLaw.uniform X).lpNorm r
      (fun x => ∏ v ∈ Finset.univ.filter (fun v => π v = i), f v x) ≤
      ∏ v ∈ Finset.univ.filter (fun v => π v = i), (FiniteLaw.uniform X).lpNorm (t * r) (f v) := by
    intro i
    rcases (Finset.univ.filter (fun v => π v = i)).eq_empty_or_nonempty with hs | hs
    · rw [hs]
      simp only [Finset.prod_empty]
      unfold FiniteLaw.lpNorm FiniteLaw.moment
      simp
    · refine (lpNorm_finset_prod_le _ _ hs hr _).trans
        (Finset.prod_le_prod₀ (fun v _ => FiniteLaw.lpNorm_nonneg _ _ _) fun v _ => ?_)
      have hc0 : (0 : ℝ) < (Finset.univ.filter (fun v => π v = i)).card := by
        exact_mod_cast hs.card_pos
      have hct : ((Finset.univ.filter (fun v => π v = i)).card : ℝ) ≤ t := by
        exact_mod_cast ht i
      exact (FiniteLaw.uniform X).lpNorm_mono (mul_pos hr hc0) (by nlinarith) _
  rw [FiniteLaw.expect_map]
  have hm := h (fun i x => ∏ v ∈ Finset.univ.filter (fun v => π v = i), f v x)
  rw [one_mul] at hm
  rw [one_mul]
  calc |μ.expect ((fun z => ∏ v, f v (z v)) ∘ fun y v => y (π v))|
      = |μ.expect (fun y => ∏ i, ∏ v ∈ Finset.univ.filter (fun v => π v = i), f v (y i))| := by
        congr 2
        funext y
        exact hfib y
    _ ≤ ∏ i, (FiniteLaw.uniform X).lpNorm r
          (fun x => ∏ v ∈ Finset.univ.filter (fun v => π v = i), f v x) := hm
    _ ≤ ∏ i, ∏ v ∈ Finset.univ.filter (fun v => π v = i),
          (FiniteLaw.uniform X).lpNorm (t * r) (f v) :=
        Finset.prod_le_prod₀ (fun i _ => FiniteLaw.lpNorm_nonneg _ _ _) fun i _ => hgi i
    _ = ∏ v, (FiniteLaw.uniform X).lpNorm (t * r) (f v) :=
        Finset.prod_fiberwise Finset.univ π (fun v => (FiniteLaw.uniform X).lpNorm (t * r) (f v))

/-- **A certified packet at `72/θ` on the 72 slots**, when each of its twelve labels is read by at
most six slots (the middle emissions read every label six times): `middle_packet_12` with
`mixedLpBound_emit`, `6 · 12/θ = 72/θ`. -/
theorem middle_packet_72 {row : GateRow} (hrow : row ∈ gateRows) {b : ℝ}
    (hb : (row.beta : ℝ) ≤ b) {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (hQ : 2 ≤ Fintype.card X)
    (hL : Real.log (Fintype.card X) ≤ row.L) {good bad packet : FiniteLaw (Fin 12 → X)}
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ht : t ≤ (packetPiece row.piece).sym (1 / Real.sqrt b) ∨
      t ≤ (packetPiece row.piece).skew (1 / Real.sqrt b))
    (hgood : blockGateUnitMixed good 11) (hbad : HasUniformMarginals bad)
    (hpacket : ∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z)
    (π : Slot → Fin 12) (hπ : ∀ i, (Finset.univ.filter (fun v => π v = i)).card ≤ 6)
    {θ : ℝ} (hθ : 0 < θ) (hθe : θ ≤ blockGateTheta) :
    MixedLpBound (packet.map (fun y v => y (π v))) (72 / θ) 1 := by
  have h := mixedLpBound_emit packet π (by positivity) hπ
    (middle_packet_12 hrow hb hQ hL ht0 ht1 ht hgood hbad hpacket hθ hθe)
  have he : ((6 : ℕ) : ℝ) * (12 / θ) = 72 / θ := by
    push_cast
    ring
  rw [he] at h
  exact h

end Emission

end Sarkozy.EnvelopeInputs
