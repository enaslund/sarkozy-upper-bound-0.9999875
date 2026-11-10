module

public import Sarkozy.ExtractionK.Grouped
public import Sarkozy.ExtractionK.KernelBridge

@[expose] public section

/-!
# Non-vacuity of the hypotheses of `grouped_extraction` (`lem:matching:extractionk`)

A concrete instance of every hypothesis of `grouped_extraction` except the literature input
`WeilBound (ZMod 5)` (Weil's theorem, `thm:weil`(a)), which stays a hypothesis.

* `F = 𝔽₅`, `U⁺ = Fin 2`, `G⁺` the empty oriented graph, cross signs `ς₀₁ = 1`, `ς₁₀ = -1`
  (antisymmetric, `lem:spec:elementary`), `E_× = {(0,1), (1,0)}`.
* The class `𝒞(P, A)` with `P = {(0,1)}`, `A = ∅`, so `F = {(1,0)}` is free.
* The witness of size `k = 1`, `w₀ = (0,1)` (`V = {0}`, `W = {1}`), and the cover `C_x = {1}`,
  `C_z = ∅` (the free pair `(1,0)` has its `x`-endpoint in `C_x`), so `U_x = ∅`, `U_z = {0}`.
* The orders `ordX = ordZ` with `1` before `0` (the cover first, the integrated set last).
* `n = 2 = |U⁺|`, `ê = e_0(5, 2) = 2/5 < 1`.
* `c_ker = 1`, from `IsWitness.rectKer_opBound_acyclic` (`lem:matching:kernel`(a)): the witness
  digraph on one vertex has no arc.

`sanity_grouped_extraction` is the conclusion of `grouped_extraction` for this instance, for all
`f`, `h`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

local instance sanityFactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The empty oriented graph on `Fin 2`. -/
def sanityG : OrientedGraph (Fin 2) where
  E := ∅
  loopless _ := notMem_empty _
  oriented _ _ h := absurd h (notMem_empty _)

/-- The cross signs `ς₀₁ = 1`, `ς₁₀ = -1`, `ς_{ii} = 0`. -/
def sanitySgn : Fin 2 → Fin 2 → ℤ := ![![0, 1], ![-1, 0]]

/-- The cross pairs `E_× = {(0,1), (1,0)}`. -/
def sanityEx : Finset (Fin 2 × Fin 2) := {(0, 1), (1, 0)}

/-- The present pairs `P = {(0,1)}`. -/
def sanityP : Finset (Fin 2 × Fin 2) := {(0, 1)}

/-- The witness of size one, `w₀ = (0,1)`. -/
def sanityW : Fin 1 → Fin 2 × Fin 2 := fun _ => (0, 1)

/-- The order of both copies: `1` before `0`. -/
def sanityOrd : Fin 2 → ℕ := fun i => if i = 1 then 0 else 1

theorem sanity_hne : (injLabellings (ZMod 5) sanityG).Nonempty := by
  refine ⟨![0, 1], ?_⟩
  unfold injLabellings
  simp only [mem_filter, mem_univ, true_and, Feasible]
  refine ⟨fun a _ b _ hab => ?_, fun e he => absurd he (notMem_empty _)⟩
  fin_cases a <;> fin_cases b <;> simp_all

theorem sanity_deg (i : Fin 2) : rowsDeg0 sanityG i = 0 := by
  simp [rowsDeg0, rowsAdj, sanityG]

theorem sanity_ehat1 : coarseError 0 (Fintype.card (ZMod 5)) 2 < 1 := by
  rw [ZMod.card]
  unfold coarseError coarseH
  have h5 : (Real.sqrt ((5 : ℕ) : ℝ))⁻¹ ^ 2 = 1 / 5 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [h5]
  norm_num

theorem sanity_witness : IsWitness sanityEx sanityP ∅ sanityW where
  mem _ := by simp [sanityW, sanityP]
  injective_fst := fun a b _ => Subsingleton.elim a b
  injective_snd := fun a b _ => Subsingleton.elim a b
  decided := by decide

theorem sanity_cover : IsCover sanityEx sanityP ∅ sanityW {1} ∅ where
  fst_not_mem := by decide
  snd_not_mem := by decide
  cover := by decide

theorem sanity_acyclic : IsAcyclicWitness (witnessIdx sanityP sanityW) := by
  intro i h
  cases h with
  | single h => exact h.2 rfl
  | tail _ h => exact h.2 (Subsingleton.elim _ _)

theorem sanity_ker : Sarkozy.Influence.OpBound (injTuples (ZMod 5) (witV sanityW))
    (injTuples (ZMod 5) (witW sanityW))
    (rectKer sanitySgn sanityP (witV sanityW) (witW sanityW))
    (1 * Real.sqrt (Fintype.card (ZMod 5)) ^ 1) := by
  have h := IsWitness.rectKer_opBound_acyclic (p := 5) sanity_witness (by norm_num) sanitySgn
    (by decide) sanity_acyclic
  rw [ZMod.card, one_mul]
  exact h

/-- **Non-vacuity of `lem:matching:extractionk`** (`grouped_extraction`): for the instance of the
module docstring, every hypothesis except Weil's theorem is discharged, and the conclusion holds
for all `f`, `h`. -/
theorem sanity_grouped_extraction (hW : WeilBound (ZMod 5)) (f h : (Fin 2 → ZMod 5) → ℝ) :
    |(graphLaw sanityG sanity_hne).expect (fun x => f x * (graphLaw sanityG sanity_hne).expect
        (fun x' => (∑ S ∈ cls sanityEx sanityP ∅, ∏ e ∈ S, chiPair sanitySgn e x x') * h x'))| ≤
      1 * (Real.sqrt (Fintype.card (ZMod 5)))⁻¹ ^ 1 *
        Real.sqrt (2 ^ recordExp sanityG (sanityEx \ (sanityP ∪ ∅)) (witV sanityW)
            (witW sanityW) sanityOrd sanityOrd *
          recordFactor sanityG sanitySgn (Fintype.card (ZMod 5)) 2 (sanityEx \ (sanityP ∪ ∅))
            (witV sanityW) (witW sanityW) {1} ∅ sanityOrd sanityOrd) /
        (1 - coarseError 0 (Fintype.card (ZMod 5)) 2) ^ 1 *
        Real.sqrt ((graphLaw sanityG sanity_hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw sanityG sanity_hne).expect (fun x => h x ^ 2)) :=
  grouped_extraction hW sanityG sanitySgn (by decide) (by decide) sanity_hne (n := 2)
    (by simp) (ehat := coarseError 0 (Fintype.card (ZMod 5)) 2)
    (fun i => by rw [sanity_deg, Nat.cast_ofNat]) sanity_ehat1 sanityEx sanityP ∅ (by decide)
    ⟨by decide, by decide, by decide⟩ sanityW sanity_witness {1} ∅ sanity_cover sanityOrd
    sanityOrd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    zero_le_one sanity_ker f h

end Sarkozy.ExtractionK
