module

public import Sarkozy.Cuts.CutTransport
public import Sarkozy.Cuts.CutBlock
public import Sarkozy.Cuts.RowProducts
public import Sarkozy.Cuts.RestrictionInj

/-!
# Cuts, X′: transport over blocks and on label subspaces (`lem:cut-transport`)

`13_cuts_correlations.tex`, `lem:cut-transport`, the last two clauses.

* `transportFun_funOf`, `transportFun_funOf_surj`: `Φ` maps the functions of the labels of
  `A ⊆ U⁺` onto the functions of the labels of `φ(A)`. So the compressions of `A` and `A'` to
  corresponding subspaces correspond under the unitary `Φ` (`transport_cutForm`).
* `transport_block`: over a block of primes, `⊗_p Φ` intertwines the block cut operators.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Labellings

namespace SpecData

variable {U U' : Type*} [Fintype U] [DecidableEq U] [Fintype U'] [DecidableEq U']
  {D : SpecData U} {D' : SpecData U'} {φ : U ≃ U'}

/-- `F` depends only on the labels of `A ⊆ U⁺`. -/
def FunOfLabels {F : Type*} {V : Type*} (A : Set V) (Fn : (V → F) → ℝ) : Prop :=
  ∀ x x' : V → F, (∀ a ∈ A, x a = x' a) → Fn x = Fn x'

theorem transportFun_funOf {F : Type*} (hφ : D.Transport D' φ) {A : Set D.cut.Half}
    {Fn : (D.cut.Half → F) → ℝ} (hF : FunOfLabels A Fn) :
    FunOfLabels (halfEquiv hφ '' A) (transportFun hφ Fn) := by
  intro ξ ξ' h
  apply hF
  intro a ha
  exact h _ ⟨a, ha, rfl⟩

/-- Every function of the labels of `φ(A)` is `Φ F` for a function `F` of the labels of `A`. -/
theorem transportFun_funOf_surj {F : Type*} (hφ : D.Transport D' φ) {A : Set D.cut.Half}
    {G : (D'.cut.Half → F) → ℝ} (hG : FunOfLabels (halfEquiv hφ '' A) G) :
    ∃ Fn : (D.cut.Half → F) → ℝ, FunOfLabels A Fn ∧ transportFun hφ Fn = G := by
  refine ⟨fun x => G (fun k' => x ((halfEquiv hφ).symm k')), fun x x' h => ?_, ?_⟩
  · apply hG
    rintro _ ⟨a, ha, rfl⟩
    simp only [Equiv.symm_apply_apply]
    exact h a ha
  · funext ξ
    simp only [transportFun, Equiv.apply_symm_apply]

/-- **`lem:cut-transport`, blocks.** `⊗_p Φ` intertwines the block cut operators:
`⟨(⊗Φ) F, A'_B (⊗Φ) H⟩ = ⟨F, A_B H⟩`. -/
theorem transport_block (hφ : D.Transport D' φ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (hne : ∀ i, (injLabellings (F i) D.G).Nonempty) (Fn Hn : (∀ i, D.cut.Half → F i) → ℝ) :
    kernelForm (FiniteLaw.pi (fun i => D'.halfLaw (nonempty_transport hφ (hne i))))
        (FiniteLaw.pi (fun i => D'.halfLaw (nonempty_transport hφ (hne i))))
        (fun ξ ξ' => ∏ i, D'.cutK (ξ i) (ξ' i) / D'.cutZ (nonempty_transport hφ (hne i)))
        (fun ξ => Fn (fun i k => ξ i (halfEquiv hφ k)))
        (fun ξ => Hn (fun i k => ξ i (halfEquiv hφ k))) =
      kernelForm (FiniteLaw.pi (fun i => D.halfLaw (hne i)))
        (FiniteLaw.pi (fun i => D.halfLaw (hne i)))
        (fun ξ ξ' => ∏ i, D.cutK (ξ i) (ξ' i) / D.cutZ (hne i)) Fn Hn := by
  rw [← D'.block_cut_form (fun i => nonempty_transport hφ (hne i)), ← D.block_cut_form hne]
  -- the product of the graph laws is carried along by `y ↦ y ∘ φ⁻¹`
  have hone : ∀ i (a : U' → F i), (graphLaw D.G (hne i)).expect
      (fun y => if (fun u' => y (φ.symm u')) = a then (1 : ℝ) else 0) =
      (graphLaw D'.G (nonempty_transport hφ (hne i))).weight a * 1 := by
    intro i a
    rw [mul_one, ← expect_indicator_eq]
    exact (graphLaw_iso D.G D'.G φ hφ.edges (hne i) (nonempty_transport hφ (hne i))
      (fun z => if z = a then (1 : ℝ) else 0)).symm
  have h := pi_single_law (fun i => graphLaw D.G (hne i))
    (fun i => graphLaw D'.G (nonempty_transport hφ (hne i)))
    (fun _ y => fun u' => y (φ.symm u')) (fun _ _ => 1) hone
    (fun y' => Fn (fun i k => D'.halfL (y' i) (halfEquiv hφ k)) *
      Hn (fun i k => D'.halfR (y' i) (halfEquiv hφ k)))
  simp only [Finset.prod_const_one, one_mul] at h
  rw [← h]
  refine (FiniteLaw.pi (fun i => graphLaw D.G (hne i))).expect_congr (fun y => ?_)
  congr 2
  · funext i k
    rw [halfL_transport hφ]
    simp only [Equiv.symm_apply_apply]
  · funext i k
    rw [halfR_transport hφ]
    simp only [Equiv.symm_apply_apply]

end SpecData

end Sarkozy.Cuts
