module

public import Sarkozy.DensityMoments.MiddleCatalogTable

/-!
# The table of `lem:density:middle-catalog` on the 72 slots (`PartV` emissions)

`paper/sections/31_density_induction_upgrade.tex`, `lem:density:middle-catalog`. The middle
components of `PartV` (`Sarkozy/PartV/Components.lean`) are laws `PartV.emit lam π` on the 72
slots, with the middle emission `midEmission φ` (slot `(u₀, u₁, ℓ)` reads `(φ(u₀), ℓ)`) or its
one-layer diagonal copy `midDiagEmission φ`; every label of the twelve-slot law is read by six
slots (`u₁` is forgotten). With `emit_mixed_of_two_labels` and the multiplicities checked by
`decide`, the twelve-slot exponents `11` and `23/2` become `66 = 6 · 11` and `69 = 6 · (23/2)`:
the same density endpoints `12/11` and `24/23`.
-/

@[expose] public section

namespace Sarkozy.DensityMoments

open Sarkozy.DensityUpgrade Sarkozy.PartV

variable {p : ℕ} [hp : Fact p.Prime]

/-- **the two-layer root (twelve labels, six slots each on the 72 slots)** on the 72 slots: unit mixed `L^{69}`. -/
theorem catalog72_root (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (lam : FiniteLaw (ZMod 6 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : ZMod 6 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (emit lam (midEmission (fun u : ZMod 6 => u))) 69 1 := by
  have hc : 6 ≤ (Finset.univ.filter (fun v => midEmission (fun u : ZMod 6 => u) v = (0, 0))).card ∧
      6 ≤ (Finset.univ.filter (fun v => midEmission (fun u : ZMod 6 => u) v = (1, 0))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (midEmission (fun u : ZMod 6 => u))
    (i := (0, 0)) (j := (1, 0)) (by decide) (t := 6) (by norm_num) hc.1 hc.2 hdist hinv hunif
  rw [card_slot] at h
  norm_num at h
  exact h

/-- **the folded root (one-layer copy, six labels)** on the 72 slots: unit mixed `L^{66}`. -/
theorem catalog72_folded_root (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (lam : FiniteLaw (ZMod 6 × Fin 1 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : ZMod 6 × Fin 1) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (emit lam (midDiagEmission (fun u : ZMod 6 => u))) 66 1 := by
  have hc : 12 ≤ (Finset.univ.filter (fun v => midDiagEmission (fun u : ZMod 6 => u) v = (0, 0))).card ∧
      12 ≤ (Finset.univ.filter (fun v => midDiagEmission (fun u : ZMod 6 => u) v = (1, 0))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (midDiagEmission (fun u : ZMod 6 => u))
    (i := (0, 0)) (j := (1, 0)) (by decide) (t := 12) (by norm_num) hc.1 hc.2 hdist hinv hunif
  rw [card_slot] at h
  norm_num at h
  exact h

/-- **`F₂` (two-layer fold `F_j`)** on the 72 slots: unit mixed `L^{66}`. -/
theorem catalog72_fold_two (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (jf : Fin 3) (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (emit lam (midEmission (Labellings.fold jf))) 66 1 := by
  have hc : ∀ jf : Fin 3, 12 ≤ (Finset.univ.filter (fun v => midEmission (Labellings.fold jf) v = (0, 0))).card ∧
      12 ≤ (Finset.univ.filter (fun v => midEmission (Labellings.fold jf) v = (0, 1))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (midEmission (Labellings.fold jf))
    (i := (0, 0)) (j := (0, 1)) (by decide) (t := 12) (by norm_num) (hc jf).1 (hc jf).2 hdist hinv hunif
  rw [card_slot] at h
  norm_num at h
  exact h

/-- **folded `F₁` (one-layer fold `F_j`)** on the 72 slots: unit mixed `L^{66}`. -/
theorem catalog72_fold_one (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (jf : Fin 3) (lam : FiniteLaw (Fin 3 × Fin 1 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 1) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (emit lam (midDiagEmission (Labellings.fold jf))) 66 1 := by
  have hc : ∀ jf : Fin 3, 12 ≤ (Finset.univ.filter (fun v => midDiagEmission (Labellings.fold jf) v = (0, 0))).card ∧
      12 ≤ (Finset.univ.filter (fun v => midDiagEmission (Labellings.fold jf) v = (1, 0))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (midDiagEmission (Labellings.fold jf))
    (i := (0, 0)) (j := (1, 0)) (by decide) (t := 12) (by norm_num) (hc jf).1 (hc jf).2 hdist hinv hunif
  rw [card_slot] at h
  norm_num at h
  exact h

/-- **`E₂` (two-layer matching `E_s`)** on the 72 slots: unit mixed `L^{66}`. -/
theorem catalog72_matching_two (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (sm : Fin 2) (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (emit lam (midEmission (Labellings.matching sm))) 66 1 := by
  have hc : ∀ sm : Fin 2, 12 ≤ (Finset.univ.filter (fun v => midEmission (Labellings.matching sm) v = (0, 0))).card ∧
      12 ≤ (Finset.univ.filter (fun v => midEmission (Labellings.matching sm) v = (0, 1))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (midEmission (Labellings.matching sm))
    (i := (0, 0)) (j := (0, 1)) (by decide) (t := 12) (by norm_num) (hc sm).1 (hc sm).2 hdist hinv hunif
  rw [card_slot] at h
  norm_num at h
  exact h

/-- **folded `E₁` (one-layer matching `E_s`)** on the 72 slots: unit mixed `L^{66}`. -/
theorem catalog72_matching_one (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (sm : Fin 2) (lam : FiniteLaw (Fin 3 × Fin 1 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 1) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (emit lam (midDiagEmission (Labellings.matching sm))) 66 1 := by
  have hc : ∀ sm : Fin 2, 12 ≤ (Finset.univ.filter (fun v => midDiagEmission (Labellings.matching sm) v = (0, 0))).card ∧
      12 ≤ (Finset.univ.filter (fun v => midDiagEmission (Labellings.matching sm) v = (1, 0))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (midDiagEmission (Labellings.matching sm))
    (i := (0, 0)) (j := (1, 0)) (by decide) (t := 12) (by norm_num) (hc sm).1 (hc sm).2 hdist hinv hunif
  rw [card_slot] at h
  norm_num at h
  exact h

/-- **`G₂` (two-layer merge `G_{sk}`)** on the 72 slots: unit mixed `L^{66}`. -/
theorem catalog72_merge_two (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (sk : Fin 2 × Fin 3) (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (emit lam (midEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc))) 66 1 := by
  have hc : ∀ sk : Fin 2 × Fin 3, 12 ≤ (Finset.univ.filter (fun v => midEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc) v = (0, 0))).card ∧
      12 ≤ (Finset.univ.filter (fun v => midEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc) v = (0, 1))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (midEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc))
    (i := (0, 0)) (j := (0, 1)) (by decide) (t := 12) (by norm_num) (hc sk).1 (hc sk).2 hdist hinv hunif
  rw [card_slot] at h
  norm_num at h
  exact h

/-- **folded `G₁` (one-layer merge `G_{sk}`)** on the 72 slots: unit mixed `L^{66}`. -/
theorem catalog72_merge_one (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (sk : Fin 2 × Fin 3) (lam : FiniteLaw (Fin 3 × Fin 1 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 1) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (emit lam (midDiagEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc))) 66 1 := by
  have hc : ∀ sk : Fin 2 × Fin 3, 12 ≤ (Finset.univ.filter (fun v => midDiagEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc) v = (0, 0))).card ∧
      12 ≤ (Finset.univ.filter (fun v => midDiagEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc) v = (1, 0))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (midDiagEmission (fun u => (Labellings.merge sk.1 sk.2 u).castSucc))
    (i := (0, 0)) (j := (1, 0)) (by decide) (t := 12) (by norm_num) (hc sk).1 (hc sk).2 hdist hinv hunif
  rw [card_slot] at h
  norm_num at h
  exact h

/-- **`C₂` (two-layer constant)** on the 72 slots: unit mixed `L^{66}`. -/
theorem catalog72_const_two (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) (c : Fin 2) (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (emit lam (midEmission (fun _ : ZMod 6 => (0 : Fin 3)))) 66 1 := by
  have hc : ∀ c : Fin 2, 12 ≤ (Finset.univ.filter (fun v => midEmission (fun _ : ZMod 6 => (0 : Fin 3)) v = (0, 0))).card ∧
      12 ≤ (Finset.univ.filter (fun v => midEmission (fun _ : ZMod 6 => (0 : Fin 3)) v = (0, 1))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (midEmission (fun _ : ZMod 6 => (0 : Fin 3)))
    (i := (0, 0)) (j := (0, 1)) (by decide) (t := 12) (by norm_num) (hc c).1 (hc c).2 hdist hinv hunif
  rw [card_slot] at h
  norm_num at h
  exact h

end Sarkozy.DensityMoments
