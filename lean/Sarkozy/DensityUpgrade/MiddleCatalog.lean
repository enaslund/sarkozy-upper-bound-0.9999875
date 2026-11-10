module

public import Sarkozy.Moments.RepeatedPair
public import Sarkozy.Moments.InvariantPair
public import Sarkozy.Moments.Product

/-!
# The nonconstant middle catalog (`lem:density:middle-catalog`)

`paper/sections/31_density_induction_upgrade.tex`, Lemma "The nonconstant middle catalog"
(`lem:density:middle-catalog`). The proof chooses, in every component, two distinct visible
labels `x, y`. Their actual pair law is square-affine invariant, so
`lem:density:invariant-pair` gives it unit mixed `L^{3/2}`. Then `lem:density:repeated-pair`
gives the bound on the twelve slots of one prime coordinate:
* with two occurrences of each label (`t = 2`): `R = 12 - (2 - 3/2) 2 = 11`;
* for the two-layer root, with one occurrence each (`t = 1`): `R = 23/2`.

* `pairLpBound_of_mixedLpBound`: the pair hypothesis of the repeated-pair lemma from a unit
  mixed bound of the actual pair law.
* `middleCatalog_component`: a twelve-slot law in which two distinct labels with a
  square-affine-invariant pair law occupy two slots each, and the other eight slots have
  uniform marginals, has unit mixed `L^{11}`.
* `middleCatalog_root`: the same with one slot each and ten other slots: unit mixed `L^{23/2}`.
* `middleCatalog_root_density`: `24/23 > θ_* = 1.014587`.
* `middleCatalog_tensor`: the bound tensors over prime coordinates.
* `upperDiagonal_L70`: the same with four slots each on `72` slots: unit mixed `L^{70}`
  (`lem:density:packets`, upper selected diagonals).

Construction-specific inputs, as named hypotheses:
* the identification of each component of the paper's table with such a configuration
  (`def:record:frame`, "the physical multiplicities");
* the square-affine invariance of the actual pair law (`hinv`) and the distinctness of the
  labels (`hdist`);
* the uniform marginals of the remaining slots (`hz`);
* the unit mixed `L^{3/2}` norm of the uniform strict square and nonsquare pair laws (`hsq`,
  `hnsq`), which `lem:density:edge-moment` supplies (not formalized; its gate at `p ≥ 64` is
  `Sarkozy.InvariantPair.edge_gate_two`).

Not formalized here: the case analysis of the table.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityUpgrade

open Sarkozy Sarkozy.InvariantPair

/-- The actual joint law of two labels `x, y` under `μ`, on `Fin 2 → X`. -/
noncomputable def pairLaw {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    (μ : FiniteLaw Ω) (x y : Ω → X) : FiniteLaw (Fin 2 → X) :=
  μ.map (fun ω => ![x ω, y ω])

/-- A unit mixed `L^q` bound of the actual pair law is the pair hypothesis of
`lem:density:repeated-pair`. -/
theorem pairLpBound_of_mixedLpBound {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    [Nonempty X] (μ : FiniteLaw Ω) (x y : Ω → X) {q : ℝ}
    (h : MixedLpBound (pairLaw μ x y) q 1) : PairLpBound μ x y q := by
  intro f g
  have h1 := h ![f, g]
  rw [pairLaw, FiniteLaw.expect_map] at h1
  simpa [Function.comp_def, Fin.prod_univ_two] using h1

variable {p : ℕ} [Fact p.Prime]

/-- **`lem:density:middle-catalog`, a nonroot component.** Let `x, y` be two distinct visible
labels of a law on one prime coordinate, each occupying two of the twelve slots, with an actual
pair law that is square-affine invariant. If the other eight slots have uniform marginals and
the two uniform pair laws have unit mixed `L^{3/2}` (`lem:density:edge-moment`), the law of the
twelve slots has unit mixed `L^{11}`. -/
theorem middleCatalog_component (hp2 : p ≠ 2) {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (x y : Ω → ZMod p) (z : Fin 8 → Ω → ZMod p)
    (hdist : ∀ w, w 0 = w 1 → (pairLaw μ x y).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw μ x y).weight (fun k => s * w k + u) = (pairLaw μ x y).weight w)
    (hsq : MixedLpBound (uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl)))
      (3 / 2) 1)
    (hnsq : MixedLpBound (uniformOn (classSet (p := p) (-1))
      (classSet_nonempty hp2 (Or.inr rfl))) (3 / 2) 1)
    (hz : ∀ k f, μ.expect (fun ω => f (z k ω)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (μ.map (repeatedConfiguration (I := Fin 2) x y z)) 11 1 := by
  have hpair := invariant_pair_mixedLpBound hp2 (pairLaw μ x y) hdist hinv hsq hnsq
  have h := mixedLpBound_repeated_pair (I := Fin 2) μ x y z (by norm_num : (0 : ℝ) < 3 / 2)
    (pairLpBound_of_mixedLpBound μ x y hpair) hz
  have e : ((Fintype.card (Fin 2) : ℕ) : ℝ) * (3 / 2) + ((Fintype.card (Fin 8) : ℕ) : ℝ) = 11 := by
    simp only [Fintype.card_fin]
    norm_num
  rw [e] at h
  exact h

/-- **`lem:density:middle-catalog`, the two-layer root.** Two distinct labels of the root, one
slot each, with a square-affine-invariant actual pair law (including every positive tilt), and
ten other slots with uniform marginals: unit mixed `L^{23/2}`. -/
theorem middleCatalog_root (hp2 : p ≠ 2) {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (x y : Ω → ZMod p) (z : Fin 10 → Ω → ZMod p)
    (hdist : ∀ w, w 0 = w 1 → (pairLaw μ x y).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw μ x y).weight (fun k => s * w k + u) = (pairLaw μ x y).weight w)
    (hsq : MixedLpBound (uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl)))
      (3 / 2) 1)
    (hnsq : MixedLpBound (uniformOn (classSet (p := p) (-1))
      (classSet_nonempty hp2 (Or.inr rfl))) (3 / 2) 1)
    (hz : ∀ k f, μ.expect (fun ω => f (z k ω)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (μ.map (repeatedConfiguration (I := Fin 1) x y z)) (23 / 2) 1 := by
  have hpair := invariant_pair_mixedLpBound hp2 (pairLaw μ x y) hdist hinv hsq hnsq
  have h := mixedLpBound_repeated_pair (I := Fin 1) μ x y z (by norm_num : (0 : ℝ) < 3 / 2)
    (pairLpBound_of_mixedLpBound μ x y hpair) hz
  have e : ((Fintype.card (Fin 1) : ℕ) : ℝ) * (3 / 2) + ((Fintype.card (Fin 10) : ℕ) : ℝ) =
      23 / 2 := by
    simp only [Fintype.card_fin]
    norm_num
  rw [e] at h
  exact h

/-- The root bound gives density `12/(23/2) = 24/23 > θ_* = 1.014587`. -/
theorem middleCatalog_root_density : (12 : ℝ) / (23 / 2) = 24 / 23 ∧
    (1014587 / 1000000 : ℝ) < 24 / 23 := by
  norm_num

/-- **`lem:density:packets`, upper selected diagonals** (and `lem:density:repeated-pair`, "a pair
repeated four times gives unit mixed `L^{70}` on `72` slots"): two distinct labels with a
square-affine-invariant actual pair law, four slots each, and `64` other slots with uniform
marginals give unit mixed `L^{70}`. -/
theorem upperDiagonal_L70 (hp2 : p ≠ 2) {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (x y : Ω → ZMod p) (z : Fin 64 → Ω → ZMod p)
    (hdist : ∀ w, w 0 = w 1 → (pairLaw μ x y).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw μ x y).weight (fun k => s * w k + u) = (pairLaw μ x y).weight w)
    (hsq : MixedLpBound (uniformOn (classSet (p := p) 1) (classSet_nonempty hp2 (Or.inl rfl)))
      (3 / 2) 1)
    (hnsq : MixedLpBound (uniformOn (classSet (p := p) (-1))
      (classSet_nonempty hp2 (Or.inr rfl))) (3 / 2) 1)
    (hz : ∀ k f, μ.expect (fun ω => f (z k ω)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (μ.map (repeatedConfiguration (I := Fin 4) x y z)) 70 1 := by
  have hpair := invariant_pair_mixedLpBound hp2 (pairLaw μ x y) hdist hinv hsq hnsq
  have h := mixedLpBound_repeated_pair (I := Fin 4) μ x y z (by norm_num : (0 : ℝ) < 3 / 2)
    (pairLpBound_of_mixedLpBound μ x y hpair) hz
  have e : ((Fintype.card (Fin 4) : ℕ) : ℝ) * (3 / 2) + ((Fintype.card (Fin 64) : ℕ) : ℝ) =
      70 := by
    simp only [Fintype.card_fin]
    norm_num
  rw [e] at h
  exact h

/-- **`lem:density:middle-catalog`, tensorization over prime coordinates.** The unit mixed
bound tensors: if the laws at two prime coordinates have unit mixed `L^R`, so does their
product on the paired labels (`Sarkozy.MixedLpBound.slotProduct`). Iterating gives the block
statement and the products of selected blocks. -/
theorem middleCatalog_tensor {V X Y : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y] {μ : FiniteLaw (V → X)}
    {ν : FiniteLaw (V → Y)} {R : ℝ} (hR : R ≠ 0) (hμ : MixedLpBound μ R 1)
    (hν : MixedLpBound ν R 1) : MixedLpBound (μ.slotProduct ν) R 1 := by
  have h := hμ.slotProduct hν zero_le_one hR
  rwa [one_mul] at h

end Sarkozy.DensityUpgrade
