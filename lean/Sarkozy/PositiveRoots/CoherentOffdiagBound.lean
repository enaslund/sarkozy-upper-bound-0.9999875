module

public import Sarkozy.PositiveRoots.CoherentOffdiagCost
public import Sarkozy.PartV.CoherentDiagonalBound
public import Sarkozy.PositiveRoots.Chamber

/-! The complete off-diagonal coherent covariance operator, including constants. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.PartV.CoherentDictionary
open scoped BigOperators

theorem kernelForm_list {Ω I : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    (L : List I) (K : I → Ω → Ω → ℝ) (f g : Ω → ℝ) :
    kernelForm ν ν (fun x y => (L.map fun i => K i x y).sum) f g =
      (L.map fun i => kernelForm ν ν (K i) f g).sum := by
  induction L with
  | nil => simp [kernelForm]
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have he : kernelForm ν ν (fun x y => K a x y + (L.map fun i => K i x y).sum) f g =
        kernelForm ν ν (K a) f g + kernelForm ν ν (fun x y => (L.map fun i => K i x y).sum) f g := by
      simp only [kernelForm, LinearMap.mk₂_apply, mul_add, add_mul, sum_add_distrib]
    rw [he, ih]

variable {p : ℕ} [Fact p.Prime]

noncomputable def coherentOffdiagKernel (x y : CoreT (ZMod p) × PairT (ZMod p)) : ℝ :=
  ((dictionary39.product dictionary39).map fun st =>
    ((st.1.2 * st.2.2 : ℚ) : ℝ) * chamberPairOffdiag st.1.1 st.2.1 x y).sum

theorem coherentOffdiag_form [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (A : CoreT (ZMod p) → PairT (ZMod p) → ℝ)
    (F G : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => A x.1 y.2 * A y.1 x.2 * coherentOffdiagKernel x y) F G =
      ((dictionary39.product dictionary39).map fun st => ((st.1.2 * st.2.2 : ℚ) : ℝ) *
        kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
          (fun x y => A x.1 y.2 * A y.1 x.2 * chamberPairOffdiag st.1.1 st.2.1 x y) F G).sum := by
  have he : (fun (x y : CoreT (ZMod p) × PairT (ZMod p)) =>
      A x.1 y.2 * A y.1 x.2 * coherentOffdiagKernel x y) =
      (fun x y => ((dictionary39.product dictionary39).map fun st =>
        ((st.1.2 * st.2.2 : ℚ) : ℝ) *
          (A x.1 y.2 * A y.1 x.2 * chamberPairOffdiag st.1.1 st.2.1 x y)).sum) := by
    funext x y
    unfold coherentOffdiagKernel
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro st _
    ring
  rw [he, kernelForm_list]
  simp_rw [kernelForm_smul]

theorem coherent_offdiag_bound (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (A : CoreT (ZMod p) → PairT (ZMod p) → ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ c, pairLaw.expect (fun b => A c b ^ 2) ≤ R)
    (hcol : ∀ b, coreLaw.expect (fun c => A c b ^ 2) ≤ R)
    (F G : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => A x.1 y.2 * A y.1 x.2 * coherentOffdiagKernel x y) F G| ≤
      R * coherentOffdiagPrice p *
        nrm (coreLaw.product pairLaw) F * nrm (coreLaw.product pairLaw) G := by
  rw [coherentOffdiag_form]
  calc
    _ ≤ ((dictionary39.product dictionary39).map fun st =>
        |((st.1.2 * st.2.2 : ℚ) : ℝ)| *
          |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
            (fun x y => A x.1 y.2 * A y.1 x.2 * chamberPairOffdiag st.1.1 st.2.1 x y) F G|).sum := by
      simpa only [abs_mul] using abs_map_sum (dictionary39.product dictionary39)
        (fun st => ((st.1.2 * st.2.2 : ℚ) : ℝ) *
          kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
            (fun x y => A x.1 y.2 * A y.1 x.2 * chamberPairOffdiag st.1.1 st.2.1 x y) F G)
    _ ≤ ((dictionary39.product dictionary39).map fun st =>
        (R * nrm (coreLaw.product pairLaw) F * nrm (coreLaw.product pairLaw) G) *
          (|((st.1.2 * st.2.2 : ℚ) : ℝ)| * offdiagPairPrice p st.1.1 st.2.1)).sum := by
      apply List.sum_le_sum
      intro st hst
      obtain ⟨hs, ht⟩ := List.mem_product.mp hst
      have h := mul_le_mul_of_nonneg_left
        (chamberPairOffdiag_bound hDLK hp3 hp7 A hR hrow hcol st.1 st.2 hs ht F G)
        (abs_nonneg (((st.1.2 * st.2.2 : ℚ) : ℝ)))
      convert h using 1
      ring
    _ = _ := by
      rw [List.sum_map_mul_left, offdiag_price_sum]
      ring

end Sarkozy.PositiveRoots.CoherentFrame
