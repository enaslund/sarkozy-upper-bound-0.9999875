module

public import Sarkozy.PartV.NonVacuity
public import Sarkozy.PaperFrame.StepInvariance

@[expose] public section

/-!
# Query acceptance of the roots, and positivity of the aligned components at `ϑ₀`

`paper/sections/27_tail_index.tex`, `lem:tail-law`(iii) (acceptance part);
`paper/sections/18_design.tex`, `subsec:front6:construction`; `paper/sections/20c_middle_frame.tex`
(the root and the aligned fold accept the six queries); `paper/sections/17_completion_repair.tex`,
`lem:five-type`(a) (the components that are diagonal at `ϑ₀`).

Proved:
* every query pair `(0, j, 0) → (2, rot j, 1)` of `𝓔₆` is an edge of the root `G_{LL,2}`
  (`query_edge_bool`) and, read through the middle emission, of the twelve-label root
  `G_{L,2}` (`query_edge_recordGraph`);
* **the tail root accepts `𝓔₆`** (`tailRoot_accepts`, `lem:tail-law`(iii)): on the support of the
  root component `π_{LL,2}` of the tail law, every query difference `z_{v_e} - z_{u_e}` is a
  nonzero square;
* **the middle root accepts `𝓔₆`** at a single prime, for the uniform root and for the
  individual-square positive root, which has the same support (`middleRoot_accepts`,
  `individualRoot_accepts`);
* the aligned fold `Π_{F₀}`, the diagonal merges `Π_{G_e}`, `Π_{G_o}` and the constants of the
  middle reference are diagonal at the first chamber cut `ϑ₀`, hence positive there
  (`middle_aligned_positive`; the identities `Q_{Π_{F₀}}(g) = E g²`, `Q_{Π_{G_e}} = E_b‖U_b‖²`,
  `Q_{Π_{C_k}} = E_b z_b²` of `lem:five-type`(a) are the cut forms of such laws);
* the tail law satisfies the invariance field `invp` of `TheoremC.Reference` in its unit form
  (`tailLaw_invp`).
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-! ## The query edges -/

/-- **The query pair `(0, j, 0) → (2, rot j, 1)` is an edge of `G_{LL,2}`** (as the Boolean edge
relation of `twoLayerGraph`). -/
theorem query_edge_bool (j : ZMod 6) :
    twoLayerEdge (Λ := Fin 2) typeL typeL ((0 : ZMod 6), j, (0 : Fin 2))
      ((2 : ZMod 6), rot j, (1 : Fin 2)) = true := by
  revert j
  unfold twoLayerEdge typeL
  decide

theorem rot_eq_chamberRotation (j : ZMod 6) : rot j = chamberRotation j := by
  revert j
  decide

/-- **Through the middle emission every query of `𝓔₆` reads the pair `((0, 0), (2, 1))`, an edge of
the twelve-label root `G_{L,2}`** (`subsec:front6:construction`). -/
theorem query_edge_recordGraph :
    (((0 : ZMod 6), (0 : Fin 2)), ((2 : ZMod 6), (1 : Fin 2))) ∈ (recordGraph (Fin 2)).E := by
  rw [mem_recordGraph]
  decide

/-! ## Supports -/

/-- A labelling charged by a graph law is an injective strict-square labelling. -/
theorem graphLaw_support {W : Type*} [Fintype W] [DecidableEq W] {F : Type*} [Field F]
    [Fintype F] [DecidableEq F] (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty)
    {y : W → F} (hy : (graphLaw G hne).weight y ≠ 0) : Feasible F G univ y := by
  rw [← mem_injLabellings_iff_feasible]
  by_contra hn
  apply hy
  change (if y ∈ injLabellings F G then 1 / ((injLabellings F G).card : ℝ) else 0) = 0
  simp only [hn, ↓reduceIte]

/-- A labelling charged by an emitted law is the image of a labelling charged by the field law. -/
theorem emit_support {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (lam : FiniteLaw (I → X)) (π : Slot → I) {z : Slot → X} (hz : (emit lam π).weight z ≠ 0) :
    ∃ y, lam.weight y ≠ 0 ∧ y ∘ π = z := by
  unfold emit FiniteLaw.map at hz
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  split_ifs at hy with hyz
  · exact ⟨y, hy, hyz⟩
  · exact absurd rfl hy

/-! ## The tail root -/

theorem layerFin_one : layerFin 1 = 1 := by decide

theorem layerFin_zero : layerFin 0 = 0 := by decide

/-- The root component `π_{LL,2}` of the tail law (identity patterns in both coordinates), with
the root graph `G_{LL,2} = rootGraph`. -/
noncomputable def tailRootComponent (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) :
    FiniteLaw (Slot → ZMod p) :=
  emit (graphLaw rootGraph (hne.two .L .L)) (upEmission (fun u : ZMod 6 => u) (fun u => u))

/-- It is the component of the state `LL` of `upComponent`. -/
theorem tailRootComponent_eq (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) :
    tailRootComponent p hne = upComponent (tailFieldLaws p hne) (true, ⟨(.L, .L), ((), ())⟩) :=
  rfl

/-- **`lem:tail-law`(iii), acceptance**: on the support of the root component of the tail law
every query of `𝓔₆` has a nonzero square difference `z_{v_e} - z_{u_e}`. -/
theorem tailRoot_accepts (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) {z : Slot → ZMod p}
    (hz : (tailRootComponent p hne).weight z ≠ 0) (j : Chamber) :
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  have hfeas := graphLaw_support rootGraph (hne.two .L .L) hy
  have h1 : upEmission (fun u : ZMod 6 => u) (fun u => u) (queryTarget j) =
      ((2 : ZMod 6), rot j, (1 : Fin 2)) := by
    change ((2 : ZMod 6), chamberRotation j, layerFin 1) = _
    rw [layerFin_one, rot_eq_chamberRotation]
  have h2 : upEmission (fun u : ZMod 6 => u) (fun u => u) (querySource j) =
      ((0 : ZMod 6), j, (0 : Fin 2)) := by
    change ((0 : ZMod 6), j, layerFin 0) = _
    rw [layerFin_zero]
  obtain ⟨-, hedge⟩ := hfeas
  simp only [rootGraph, mem_twoLayerGraph, mem_univ, forall_const] at hedge
  rw [Function.comp_apply, Function.comp_apply, h1, h2]
  exact hedge (((0 : ZMod 6), j, (0 : Fin 2)), ((2 : ZMod 6), rot j, (1 : Fin 2)))
    (query_edge_bool j)

/-! ## The middle root at one prime -/

theorem midEmission_queryTarget (j : Chamber) :
    midEmission (fun u : ZMod 6 => u) (queryTarget j) = ((2 : ZMod 6), (1 : Fin 2)) := by
  change ((2 : ZMod 6), layerFin 1) = _
  rw [layerFin_one]

theorem midEmission_querySource (j : Chamber) :
    midEmission (fun u : ZMod 6 => u) (querySource j) = ((0 : ZMod 6), (0 : Fin 2)) := by
  change ((0 : ZMod 6), layerFin 0) = _
  rw [layerFin_zero]

section MiddleRoot

variable (p : ℕ) [Fact p.Prime]

/-- **The uniform middle root accepts `𝓔₆`** (at one prime): on the support of the image of
`λ_p(G_{L,2})` under the middle emission, every query difference is a nonzero square. -/
theorem middleRoot_accepts (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty)
    {z : Slot → ZMod p}
    (hz : (emit (graphLaw (recordGraph (Fin 2)) hne)
      (midEmission (fun u : ZMod 6 => u))).weight z ≠ 0)
    (j : Chamber) : quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  have hfeas := graphLaw_support (recordGraph (Fin 2)) hne hy
  have he := hfeas.2 _ query_edge_recordGraph (mem_univ _) (mem_univ _)
  rw [Function.comp_apply, Function.comp_apply, midEmission_queryTarget, midEmission_querySource]
  exact he

/-- **The individual-square positive root accepts `𝓔₆`** (it has the support of the uniform root,
`lem:positive-root-properties`(a)). -/
theorem individualRoot_accepts (u : ℚ)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) {z : Slot → ZMod p}
    (hz : (emit (individualRoot p u hne) (midEmission (fun u : ZMod 6 => u))).weight z ≠ 0)
    (j : Chamber) : quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  have hy' := (individualRoot_support p u hne y).mp hy
  have hfeas := graphLaw_support (recordGraph (Fin 2)) hne hy'
  have he := hfeas.2 _ query_edge_recordGraph (mem_univ _) (mem_univ _)
  rw [Function.comp_apply, Function.comp_apply, midEmission_queryTarget, midEmission_querySource]
  exact he

end MiddleRoot

/-! ## Components diagonal at `ϑ₀` -/

/-- The patterns fixed by the reflection `u ↦ 5 - u` of `ϑ₀`: the aligned fold `F₀`, the merges
`G_e = G_{00}` and `G_o = G_{11}`, and the constants (`lem:record:fold-identification`(e)). -/
def FixedAtTheta0 : (t : PType) → t.Pat → Prop
  | .L, _ => False
  | .D, j => j = 0
  | .S, _ => False
  | .R, sk => sk = (0, 0) ∨ sk = (1, 1)
  | .C, _ => True

theorem pat_fixed_theta0 : ∀ (t : PType) (φ : t.Pat), FixedAtTheta0 t φ →
    ∀ u : ZMod 6, t.pat φ (-1 - u) = t.pat φ u
  | .L, _, h, _ => h.elim
  | .D, j, h, u => by
      change j = 0 at h
      subst h
      revert u
      decide
  | .S, _, h, _ => h.elim
  | .R, sk, h, u => by
      change sk = (0, 0) ∨ sk = (1, 1) at h
      rcases h with h | h <;> subst h <;> revert u <;> decide
  | .C, _, _, _ => rfl

/-- **The middle components of the patterns fixed by `ϑ₀` are positive at `ϑ₀`** (both the
two-layer components and the one-layer diagonal copies): every configuration is fixed by the
reflection (`lem:commoncut`). -/
theorem middle_aligned_positive {X : Type*} [Fintype X] [DecidableEq X] (F : MiddleFieldLaws X)
    (b : Bool) (t : PType) (φ : t.Pat) (h : FixedAtTheta0 t φ) :
    (firstChamberCut 0).Positive (signedIntegral (midComponent F (b, ⟨t, φ⟩)).weight) := by
  cases b
  · refine emit_positive _ _ _ fun v => ?_
    change (t.pat φ (2 * 0 - 1 - v.1), (0 : Fin 1)) = (t.pat φ v.1, 0)
    rw [show (2 * 0 - 1 - v.1 : ZMod 6) = -1 - v.1 by ring, pat_fixed_theta0 t φ h]
  · refine emit_positive _ _ _ fun v => ?_
    change (t.pat φ (2 * 0 - 1 - v.1), layerFin v.2.2) = (t.pat φ v.1, layerFin v.2.2)
    rw [show (2 * 0 - 1 - v.1 : ZMod 6) = -1 - v.1 by ring, pat_fixed_theta0 t φ h]

/-! ## The invariance field of `TheoremC.Reference` -/

/-- **`Reference.invp` for the tail law**: invariance under `z_v ↦ a z_v + b` for a unit `a` that is
a square (`(R3)` of `hyp:record:reference` at a tail atom). -/
theorem tailLaw_invp (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (a : (ZMod p)ˣ) (b : ZMod p)
    (ha : IsSquare (a : ZMod p)) (F : (Slot → ZMod p) → ℝ) :
    (tailLaw p hne).expect (fun z => F (fun v => PaperFrame.affineEquiv a b (z v))) =
      (tailLaw p hne).expect F := by
  have hχ : quadraticChar (ZMod p) (a : ZMod p) = 1 :=
    (quadraticChar_one_iff_isSquare a.ne_zero).mpr ha
  exact tailLaw_affine p hne hχ b F

end Sarkozy.PartV
