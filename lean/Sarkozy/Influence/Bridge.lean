module

public import Sarkozy.Influence.Defs
public import Sarkozy.Labellings.GraphLaw



@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A `Labellings` oriented graph, read as an `Influence` oriented graph. -/
def ofLabellings (G' : Labellings.OrientedGraph U) : OrientedGraph U where
  edge u v := (u, v) ∈ G'.E
  irrefl u := G'.loopless u
  asymm u v h := G'.oriented u v h

variable {p : ℕ} [Fact p.Prime]

/-- `d ∈ Q_p ⟺ χ(d) = 1`. -/
theorem isNzSq_iff_quadraticChar (d : ZMod p) : IsNzSq d ↔ quadraticChar (ZMod p) d = 1 := by
  unfold IsNzSq
  by_cases hd : d = 0
  · subst hd
    simp
  · rw [quadraticChar_one_iff_isSquare hd]
    exact ⟨fun h => h.2, fun h => ⟨hd, h⟩⟩

theorem mem_injLabellings_iff {G : OrientedGraph U} {z : U → ZMod p} :
    z ∈ injLabellings G p ↔ Function.Injective z ∧ IsStrictSquare G z := by
  classical
  simp [injLabellings]

theorem mem_labellings_injLabellings_iff {G' : Labellings.OrientedGraph U} {z : U → ZMod p} :
    z ∈ Labellings.injLabellings (ZMod p) G' ↔ Labellings.Feasible (ZMod p) G' Finset.univ z := by
  classical
  unfold Labellings.injLabellings
  simp

theorem injLabellings_ofLabellings (G' : Labellings.OrientedGraph U) :
    injLabellings (ofLabellings G') p = Labellings.injLabellings (ZMod p) G' := by
  ext z
  rw [mem_injLabellings_iff, mem_labellings_injLabellings_iff]
  unfold Labellings.Feasible IsStrictSquare
  constructor
  · rintro ⟨hinj, hsq⟩
    exact ⟨fun a _ b _ hab => hinj hab,
      fun e he _ _ => (isNzSq_iff_quadraticChar _).mp (hsq e.1 e.2 he)⟩
  · rintro ⟨hinj, hsq⟩
    exact ⟨fun a b hab => hinj a (Finset.mem_univ _) b (Finset.mem_univ _) hab,
      fun u v he => (isNzSq_iff_quadraticChar _).mpr
        (hsq (u, v) he (Finset.mem_univ _) (Finset.mem_univ _))⟩

/-- The two graph laws coincide. -/
theorem graphLaw_ofLabellings (G' : Labellings.OrientedGraph U)
    (h : (injLabellings (ofLabellings G') p).Nonempty)
    (h' : (Labellings.injLabellings (ZMod p) G').Nonempty) :
    graphLaw (ofLabellings G') p h = Labellings.graphLaw G' h' := by
  classical
  apply Sarkozy.Peyre.law_ext
  intro z
  simp only [graphLaw, Labellings.graphLaw, injLabellings_ofLabellings G']

end Sarkozy.Influence
