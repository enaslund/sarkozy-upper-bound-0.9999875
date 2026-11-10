module

public import Sarkozy.Interpolation.InvariantPairProved
public import Sarkozy.PartV.Components
public import Sarkozy.DensityMoments.LawAlgebra

/-!
# The table of `lem:density:middle-catalog`

`paper/sections/31_density_induction_upgrade.tex`, `lem:density:middle-catalog` and its table
of physical multiplicities. WP-P proved the chain (`DensityUpgrade.MiddleCatalog`), and I1
discharged its `L^{3/2}` inputs (`Interpolation.middleCatalog_component_proved`, …). This file
does the case analysis of the table.

* `mixedLpBound_reindex`: mixed bounds are invariant under a relabelling of the slots.
* `emit_mixed_of_two_labels`: **the general step.** A law of labels `y : I → ZMod p` emitted to
  any finite slot set `V` by `π : V → I` (slot `v` reads `y (π v)`) has unit mixed
  `L^{|V| - t/2}` if two labels `i ≠ j` are each read by at least `t ≥ 1` slots, their actual
  pair law is distinct and square-affine invariant, all labels are uniform, and `p ≥ 64`
  (`lem:density:repeated-pair` with `q = 3/2`, `lem:density:invariant-pair`).
* The twelve slots `(u₀, ℓ)` of one prime coordinate (`TwelveSlot`), with the two-layer emission
  `(u₀, ℓ) ↦ (φ(u₀), ℓ)` (`twoLayer12`) and the one-layer emission `(u₀, ℓ) ↦ φ(u₀)` copied onto
  the reserved diagonal (`oneLayer12`), for the pattern maps `PartV.PType.pat` of
  `def:patterns`.
* **The rows of the table**, each with its exponent:

  | component | visible labels | chosen multiplicities | Lean | exponent |
  |---|---|---|---|---|
  | two-layer root | 12 | 1, 1 | `catalog_root` | `23/2` |
  | folded root | 6 | 2, 2 | `catalog_folded_root` | `11` |
  | `F₂` | 6 | 2, 2 | `catalog_fold_two` | `11` |
  | `E₂` | 6 | 2, 2 | `catalog_matching_two` | `11` |
  | folded `F₁` | 3 | 4, 4 | `catalog_fold_one` | `11` |
  | folded `E₁` | 3 | 4, 4 | `catalog_matching_one` | `11` |
  | `G₂` | 4 | 4, 4 | `catalog_merge_two` | `11` |
  | folded `G₁` | 2 | 8, 4 | `catalog_merge_one` | `11` |
  | `C₂` | 2 | 6, 6 | `catalog_const_two` | `11` |

  The multiplicities are checked by `decide` from the pattern tables. The one-layer constant
  (one label, twelve slots) is excluded, as in the paper.
* `catalog_matching_law`, `catalog_matching_fold`: the additional first-stage matching law
  (three labels, multiplicities `4, 4, 4`) and its private sharp fold (`8, 4`) are instances of
  `emit_mixed_of_two_labels` with `t = 2`; so is every positive coupling for which two distinct
  labels of one half occur twice each (`catalog_two_occurrences`).

Inputs, as in the paper's proof: the actual pair law of the two chosen visible labels is
distinct and square-affine invariant, and every visible label is uniform (`hdist`, `hinv`,
`hunif`). They are properties of the actual label laws of the construction.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open Sarkozy.InvariantPair Sarkozy.DensityUpgrade Sarkozy.PartV

/-- **Mixed bounds are invariant under a relabelling of the slots.** -/
theorem mixedLpBound_reindex {V W X : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] [Fintype X] [DecidableEq X] [Nonempty X] (e : W ≃ V)
    {μ : FiniteLaw (V → X)} {R C : ℝ} (h : MixedLpBound (μ.map (fun z w => z (e w))) R C) :
    MixedLpBound μ R C := by
  intro f
  have hf := h (fun w => f (e w))
  rw [FiniteLaw.expect_map] at hf
  have h1 : ∀ z : V → X, ∏ w, f (e w) (z (e w)) = ∏ v, f v (z v) :=
    fun z => Fintype.prod_equiv e _ _ (fun _ => rfl)
  have h2 : ∏ w, (FiniteLaw.uniform X).lpNorm R (f (e w)) =
      ∏ v, (FiniteLaw.uniform X).lpNorm R (f v) := Fintype.prod_equiv e _ _ (fun _ => rfl)
  simp only [Function.comp_def, h1, h2] at hf
  exact hf

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The general step of the table.** Slot `v` reads label `π v`. If two labels `i ≠ j` are each
read by at least `t ≥ 1` slots, their actual pair law is distinct and square-affine invariant,
and every label is uniform, the emitted law has unit mixed `L^{|V| - t/2}` (`p ≥ 64`). -/
theorem emit_mixed_of_two_labels (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) {V I : Type*} [Fintype V]
    [DecidableEq V] [Fintype I] [DecidableEq I] (lam : FiniteLaw (I → ZMod p)) (π : V → I)
    {i j : I} (hij : i ≠ j) {t : ℕ} (ht : 0 < t)
    (hti : t ≤ (univ.filter (fun v => π v = i)).card)
    (htj : t ≤ (univ.filter (fun v => π v = j)).card)
    (hdist : ∀ w, w 0 = w 1 → (pairLaw lam (fun y => y i) (fun y => y j)).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y i) (fun y => y j)).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y i) (fun y => y j)).weight w)
    (hunif : ∀ (l : I) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (π v))) ((Fintype.card V : ℝ) - t / 2) 1 := by
  classical
  -- two families of `t` slots reading `i` and `j`
  have hci : Fintype.card (Fin t) ≤ Fintype.card {v // π v = i} := by
    rw [Fintype.card_fin, Fintype.card_subtype]
    exact hti
  have hcj : Fintype.card (Fin t) ≤ Fintype.card {v // π v = j} := by
    rw [Fintype.card_fin, Fintype.card_subtype]
    exact htj
  obtain ⟨ea⟩ := Function.Embedding.nonempty_of_card_le hci
  obtain ⟨eb⟩ := Function.Embedding.nonempty_of_card_le hcj
  set a : Fin t → V := fun k => (ea k).1 with hadef
  set b : Fin t → V := fun k => (eb k).1 with hbdef
  have ha : ∀ k, π (a k) = i := fun k => (ea k).2
  have hb : ∀ k, π (b k) = j := fun k => (eb k).2
  have hainj : Function.Injective a := fun k l h => ea.injective (Subtype.ext h)
  have hbinj : Function.Injective b := fun k l h => eb.injective (Subtype.ext h)
  have hab : ∀ k l, a k ≠ b l := fun k l h => hij (by rw [← ha k, ← hb l, h])
  set S : Finset V := univ.image a ∪ univ.image b with hS
  -- the slot bijection `(Fin t ⊕ Fin t) ⊕ {v ∉ S} ≃ V`
  set g : (Fin t ⊕ Fin t) ⊕ {v // v ∉ S} → V := Sum.elim (Sum.elim a b) Subtype.val with hg
  have hginj : Function.Injective g := by
    rintro ((k | k) | ⟨w, hw⟩) ((l | l) | ⟨w', hw'⟩) h <;> simp only [hg, Sum.elim_inl,
      Sum.elim_inr] at h
    · rw [hainj h]
    · exact absurd h (hab k l)
    · exact absurd h.symm (fun h' => hw' (h' ▸ mem_union_left _ (mem_image_of_mem a (mem_univ k))))
    · exact absurd h.symm (hab l k)
    · rw [hbinj h]
    · exact absurd h.symm (fun h' => hw' (h' ▸ mem_union_right _ (mem_image_of_mem b (mem_univ k))))
    · exact absurd h (fun h' => hw (h' ▸ mem_union_left _ (mem_image_of_mem a (mem_univ l))))
    · exact absurd h (fun h' => hw (h' ▸ mem_union_right _ (mem_image_of_mem b (mem_univ l))))
    · exact congrArg Sum.inr (Subtype.ext h)
  have hgsurj : Function.Surjective g := by
    intro v
    by_cases hv : v ∈ S
    · rcases mem_union.mp hv with h | h
      · obtain ⟨k, _, rfl⟩ := mem_image.mp h
        exact ⟨Sum.inl (Sum.inl k), rfl⟩
      · obtain ⟨k, _, rfl⟩ := mem_image.mp h
        exact ⟨Sum.inl (Sum.inr k), rfl⟩
    · exact ⟨Sum.inr ⟨v, hv⟩, rfl⟩
  set e := Equiv.ofBijective g ⟨hginj, hgsurj⟩ with he
  -- the pair moment
  have hpair := Interpolation.invariant_pair_three_halves hp2 hp64 (pairLaw lam (fun y => y i) (fun y => y j))
    hdist hinv
  have hNe : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  have hrep := mixedLpBound_repeated_pair (I := Fin t) (K := {v // v ∉ S}) lam
    (fun y => y i) (fun y => y j) (fun k y => y (π k.1)) (by norm_num : (0 : ℝ) < 3 / 2)
    (pairLpBound_of_mixedLpBound lam _ _ hpair) (fun k f => hunif (π k.1) f)
  -- the cardinality of the remaining slots
  have hScard : S.card = 2 * t := by
    rw [hS, card_union_of_disjoint, card_image_of_injective _ hainj,
      card_image_of_injective _ hbinj, card_univ, Fintype.card_fin]
    · ring
    · rw [disjoint_left]
      intro v hva hvb
      obtain ⟨k, _, rfl⟩ := mem_image.mp hva
      obtain ⟨l, _, hl⟩ := mem_image.mp hvb
      exact hab k l hl.symm
  have hK : Fintype.card {v // v ∉ S} = Fintype.card V - 2 * t := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hScard]
  have hle : 2 * t ≤ Fintype.card V := by
    rw [← hScard]
    exact card_le_univ S
  have hR : ((Fintype.card (Fin t) : ℕ) : ℝ) * (3 / 2) +
      ((Fintype.card {v // v ∉ S} : ℕ) : ℝ) = (Fintype.card V : ℝ) - t / 2 := by
    rw [Fintype.card_fin, hK, Nat.cast_sub hle]
    push_cast
    ring
  rw [hR] at hrep
  apply mixedLpBound_reindex e
  have hlaw : (lam.map (fun y v => y (π v))).map (fun z w => z (e w)) =
      lam.map (repeatedConfiguration (I := Fin t) (fun y => y i) (fun y => y j)
        (fun k y => y (π k.1))) := by
    rw [map_map_law]
    congr 1
    funext y w
    rcases w with (k | k) | w
    · show y (π (a k)) = y i
      rw [ha k]
    · show y (π (b k)) = y j
      rw [hb k]
    · rfl
  rw [hlaw]
  exact hrep

/-! ## The twelve slots of one prime coordinate -/

/-- The twelve slots `(u₀, ℓ)` of one prime coordinate. -/
abbrev TwelveSlot := ZMod 6 × Fin 2

/-- The two-layer emission: slot `(u₀, ℓ)` reads the label `(φ(u₀), ℓ)`. -/
def twoLayer12 {O : Type*} (φ : ZMod 6 → O) (v : TwelveSlot) : O × Fin 2 := (φ v.1, v.2)

/-- The one-layer emission copied onto the reserved diagonal: slot `(u₀, ℓ)` reads `φ(u₀)`. -/
def oneLayer12 {O : Type*} (φ : ZMod 6 → O) (v : TwelveSlot) : O := φ v.1

theorem card_twelveSlot : Fintype.card TwelveSlot = 12 := rfl

/-- The pattern maps of the rows are those of `def:patterns` (`PartV.PType.pat`). -/
theorem rows_are_patterns :
    (∀ u : ZMod 6, PType.pat .L () u = u) ∧ (∀ j u, PType.pat .D j u = Labellings.fold j u) ∧
    (∀ s u, PType.pat .S s u = Labellings.matching s u) ∧
    (∀ sk u, PType.pat .R sk u = (Labellings.merge sk.1 sk.2 u).castSucc) ∧
    (∀ c u, PType.pat .C c u = (0 : Fin 3)) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

section Rows

variable (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p)

include hp2 hp64

/-- **The two-layer root** (`φ = id`, twelve labels, one slot each): unit mixed `L^{23/2}`. -/
theorem catalog_root (lam : FiniteLaw (ZMod 6 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (1, 0))).weight w)
    (hunif : ∀ (l : ZMod 6 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (twoLayer12 (fun u : ZMod 6 => u) v))) (23 / 2) 1 := by
  have h := emit_mixed_of_two_labels hp2 hp64 lam (twoLayer12 (fun u : ZMod 6 => u))
    (i := (0, 0)) (j := (1, 0)) (by decide) (t := 1) one_pos (by decide) (by decide)
    hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **The folded root** (one layer, six labels, two slots each): unit mixed `L^{11}`. -/
theorem catalog_folded_root (lam : FiniteLaw (ZMod 6 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 → (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y 0) (fun y => y 1)).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w)
    (hunif : ∀ (l : ZMod 6) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (oneLayer12 (fun u : ZMod 6 => u) v))) 11 1 := by
  have h := emit_mixed_of_two_labels hp2 hp64 lam (oneLayer12 (fun u : ZMod 6 => u))
    (i := 0) (j := 1) (by decide) (t := 2) two_pos (by decide) (by decide) hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **`F₂`** (two-layer fold `F_j`, six labels, two slots each): unit mixed `L^{11}`. -/
theorem catalog_fold_two (jf : Fin 3) (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (twoLayer12 (Labellings.fold jf) v))) 11 1 := by
  have hc : ∀ jf : Fin 3, 2 ≤ (univ.filter (fun v => twoLayer12 (Labellings.fold jf) v = (0, 0))).card ∧
      2 ≤ (univ.filter (fun v => twoLayer12 (Labellings.fold jf) v = (0, 1))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (twoLayer12 (Labellings.fold jf))
    (i := (0, 0)) (j := (0, 1)) (by decide) (t := 2) two_pos (hc jf).1 (hc jf).2 hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **Folded `F₁`** (one-layer fold `F_j`, three labels, four slots each): unit mixed `L^{11}`. -/
theorem catalog_fold_one (jf : Fin 3) (lam : FiniteLaw (Fin 3 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 → (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y 0) (fun y => y 1)).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w)
    (hunif : ∀ (l : Fin 3) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (oneLayer12 (Labellings.fold jf) v))) 11 1 := by
  have hc : ∀ jf : Fin 3, 4 ≤ (univ.filter (fun v => oneLayer12 (Labellings.fold jf) v = 0)).card ∧
      4 ≤ (univ.filter (fun v => oneLayer12 (Labellings.fold jf) v = 1)).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (oneLayer12 (Labellings.fold jf))
    (i := 0) (j := 1) (by decide) (t := 2) two_pos (le_trans (by norm_num) (hc jf).1)
    (le_trans (by norm_num) (hc jf).2) hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **`E₂`** (two-layer matching `E_s`, six labels, two slots each): unit mixed `L^{11}`. -/
theorem catalog_matching_two (sm : Fin 2) (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (twoLayer12 (Labellings.matching sm) v))) 11 1 := by
  have hc : ∀ sm : Fin 2, 2 ≤ (univ.filter (fun v => twoLayer12 (Labellings.matching sm) v = (0, 0))).card ∧
      2 ≤ (univ.filter (fun v => twoLayer12 (Labellings.matching sm) v = (0, 1))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (twoLayer12 (Labellings.matching sm))
    (i := (0, 0)) (j := (0, 1)) (by decide) (t := 2) two_pos (hc sm).1 (hc sm).2 hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **Folded `E₁`** (one-layer matching `E_s`, three labels, four slots each): unit mixed
`L^{11}`. -/
theorem catalog_matching_one (sm : Fin 2) (lam : FiniteLaw (Fin 3 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 → (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y 0) (fun y => y 1)).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w)
    (hunif : ∀ (l : Fin 3) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (oneLayer12 (Labellings.matching sm) v))) 11 1 := by
  have hc : ∀ sm : Fin 2, 4 ≤ (univ.filter (fun v => oneLayer12 (Labellings.matching sm) v = 0)).card ∧
      4 ≤ (univ.filter (fun v => oneLayer12 (Labellings.matching sm) v = 1)).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (oneLayer12 (Labellings.matching sm))
    (i := 0) (j := 1) (by decide) (t := 2) two_pos (le_trans (by norm_num) (hc sm).1)
    (le_trans (by norm_num) (hc sm).2) hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **`G₂`** (two-layer merge `G_{sk}`: the object `0` has four preimages): the labels `(0, 0)`
and `(0, 1)`, four slots each; unit mixed `L^{11}`. -/
theorem catalog_merge_two (sk : Fin 2 × Fin 3) (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (twoLayer12 ((fun u => (Labellings.merge sk.1 sk.2 u).castSucc)) v))) 11 1 := by
  have hc : ∀ sk : Fin 2 × Fin 3,
      4 ≤ (univ.filter (fun v => twoLayer12 ((fun u => (Labellings.merge sk.1 sk.2 u).castSucc)) v = (0, 0))).card ∧
      4 ≤ (univ.filter (fun v => twoLayer12 ((fun u => (Labellings.merge sk.1 sk.2 u).castSucc)) v = (0, 1))).card := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (twoLayer12 ((fun u => (Labellings.merge sk.1 sk.2 u).castSucc)))
    (i := (0, 0)) (j := (0, 1)) (by decide) (t := 2) two_pos (le_trans (by norm_num) (hc sk).1)
    (le_trans (by norm_num) (hc sk).2) hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **Folded `G₁`** (one-layer merge: objects `0, 1` with eight and four slots): unit mixed
`L^{11}`. -/
theorem catalog_merge_one (sk : Fin 2 × Fin 3) (lam : FiniteLaw (Fin 3 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 → (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y 0) (fun y => y 1)).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w)
    (hunif : ∀ (l : Fin 3) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (oneLayer12 ((fun u => (Labellings.merge sk.1 sk.2 u).castSucc)) v))) 11 1 := by
  have hc : ∀ sk : Fin 2 × Fin 3,
      (univ.filter (fun v => oneLayer12 ((fun u => (Labellings.merge sk.1 sk.2 u).castSucc)) v = 0)).card = 8 ∧
      (univ.filter (fun v => oneLayer12 ((fun u => (Labellings.merge sk.1 sk.2 u).castSucc)) v = 1)).card = 4 := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (oneLayer12 ((fun u => (Labellings.merge sk.1 sk.2 u).castSucc)))
    (i := 0) (j := 1) (by decide) (t := 2) two_pos (by rw [(hc sk).1]; norm_num)
    (by rw [(hc sk).2]; norm_num) hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **`C₂`** (two-layer constant: two labels, six slots each): unit mixed `L^{11}`. -/
theorem catalog_const_two (c : Fin 2) (lam : FiniteLaw (Fin 3 × Fin 2 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 →
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y (0, 0)) (fun y => y (0, 1))).weight w)
    (hunif : ∀ (l : Fin 3 × Fin 2) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (twoLayer12 ((fun _ : ZMod 6 => (0 : Fin 3))) v))) 11 1 := by
  have hc : ∀ c : Fin 2,
      (univ.filter (fun v => twoLayer12 ((fun _ : ZMod 6 => (0 : Fin 3))) v = (0, 0))).card = 6 ∧
      (univ.filter (fun v => twoLayer12 ((fun _ : ZMod 6 => (0 : Fin 3))) v = (0, 1))).card = 6 := by decide
  have h := emit_mixed_of_two_labels hp2 hp64 lam (twoLayer12 ((fun _ : ZMod 6 => (0 : Fin 3))))
    (i := (0, 0)) (j := (0, 1)) (by decide) (t := 2) two_pos (by rw [(hc c).1]; norm_num)
    (by rw [(hc c).2]; norm_num) hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **Any twelve-slot law in which two distinct labels occur twice each** (the matching law
`(a, b, c)` with multiplicities `4, 4, 4`, its private sharp fold with `8, 4`, the polarization
and merge destinations, and every positive coupling whose half contains two distinct labels
with two occurrences each): unit mixed `L^{11}`. -/
theorem catalog_two_occurrences {I : Type*} [Fintype I] [DecidableEq I]
    (lam : FiniteLaw (I → ZMod p)) (π : TwelveSlot → I) {i j : I} (hij : i ≠ j)
    (hti : 2 ≤ (univ.filter (fun v => π v = i)).card)
    (htj : 2 ≤ (univ.filter (fun v => π v = j)).card)
    (hdist : ∀ w, w 0 = w 1 → (pairLaw lam (fun y => y i) (fun y => y j)).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y i) (fun y => y j)).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y i) (fun y => y j)).weight w)
    (hunif : ∀ (l : I) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (π v))) 11 1 := by
  have h := emit_mixed_of_two_labels hp2 hp64 lam π hij (t := 2) two_pos hti htj hdist hinv hunif
  rw [card_twelveSlot] at h
  norm_num at h
  exact h

/-- **The additional first-stage matching law**: three labels `a, b, c`, four slots each (here
the slot `(u₀, ℓ)` reads `⌊u₀/2⌋ = E₁(u₀)`), unit mixed `L^{11}`. -/
def matchingLawEmission (v : TwelveSlot) : Fin 3 := Labellings.matching 1 v.1

theorem catalog_matching_law (lam : FiniteLaw (Fin 3 → ZMod p))
    (hdist : ∀ w, w 0 = w 1 → (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw lam (fun y => y 0) (fun y => y 1)).weight (fun k => s * w k + u) =
        (pairLaw lam (fun y => y 0) (fun y => y 1)).weight w)
    (hunif : ∀ (l : Fin 3) (f : ZMod p → ℝ),
      lam.expect (fun y => f (y l)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (lam.map (fun y v => y (matchingLawEmission v))) 11 1 :=
  catalog_two_occurrences hp2 hp64 lam matchingLawEmission (i := 0) (j := 1) (by decide)
    (by decide) (by decide) hdist hinv hunif

end Rows

/-- The exponents of the table: density endpoints `12/11` and `24/23` exceed `θ_*`. -/
theorem catalog_density_endpoints :
    (1014587 / 1000000 : ℝ) < 12 / 11 ∧ (1014587 / 1000000 : ℝ) < 12 / (23 / 2) := by
  norm_num

end Sarkozy.DensityMoments
