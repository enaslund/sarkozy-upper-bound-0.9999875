module

public import Sarkozy.PositiveRoots.CoherentOffdiagTrace

/-! Each physical score-support pair has its proved core or private covariance price. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC.TwoLabel Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.PartV.CoherentDictionary
open scoped BigOperators

noncomputable def offdiagPairPrice (p : ℕ) (S T : Support) : ℝ :=
  if (covarianceCase S T).1 then
    (privatePairCost S T : ℝ) * ((p : ℝ) / (p - 1)) * (p : ℝ)⁻¹
  else (corePairCost S T : ℝ) / 16 * coreCubeDensity p * (p : ℝ)⁻¹

variable {p : ℕ} [Fact p.Prime]

theorem chamberPairOffdiag_bound (hDLK : Target.FourCycle) (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (A : CoreT (ZMod p) → PairT (ZMod p) → ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ c, pairLaw.expect (fun b => A c b ^ 2) ≤ R)
    (hcol : ∀ b, coreLaw.expect (fun c => A c b ^ 2) ≤ R)
    (sc tc : Support × ℚ) (hsc : sc ∈ dictionary39) (htc : tc ∈ dictionary39)
    (F G : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => A x.1 y.2 * A y.1 x.2 * chamberPairOffdiag sc.1 tc.1 x y) F G| ≤
      R * offdiagPairPrice p sc.1 tc.1 *
        nrm (coreLaw.product pairLaw) F * nrm (coreLaw.product pairLaw) G := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpne := hp0.ne'
  have hcases := covariance_chart_cases sc hsc tc htc
  by_cases hc : (covarianceCase sc.1 tc.1).1 = true
  · rw [ite_eq_left hc] at hcases
    obtain ⟨⟨hS, hT, hST⟩, ⟨hU, hV, hUV⟩⟩ := hcases
    let ψ := fun (c : CoreT (ZMod p)) z =>
      rawPairFeature (coreSupport true sc.1) (coreSupport true tc.1) c.val z
    let ψ' := fun (c : CoreT (ZMod p)) z =>
      rawPairFeature (coreSupport false sc.1) (coreSupport false tc.1) c.val z
    have hb := private_rectangle_bound hDLK (by omega : p ≠ 2) (fun b c => A c b)
      _ _ _ _ hS hT hU hV hST hUV ψ ψ'
      (fun c z => rawPairFeature_abs _ _ c.val z) (fun c z => rawPairFeature_abs _ _ c.val z)
      hR hcol (fun x => F (x.2, x.1)) (fun x => G (x.2, x.1))
    rw [nrm_prodComm, nrm_prodComm] at hb
    have he : kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
        (fun x y => A x.1 y.2 * A y.1 x.2 * chamberPairOffdiag sc.1 tc.1 x y) F G =
        (p : ℝ) * kernelForm (pairLaw.product coreLaw) (pairLaw.product coreLaw)
          (fun x y => A y.2 x.1 * A x.2 y.1 *
            ip ((fieldLaw p).product (fieldLaw p))
              (fun z => offdiagFeature (privateSupport true sc.1) (privateSupport true tc.1)
                ![x.1.val.1, x.1.val.2] z * ψ x.2 z)
              (fun z => offdiagFeature (privateSupport false sc.1) (privateSupport false tc.1)
                ![y.1.val.1, y.1.val.2] z * ψ' y.2 z))
            (fun x => F (x.2, x.1)) (fun x => G (x.2, x.1)) := by
      rw [kernelForm_prodComm]
      simp only [chamberPairOffdiag_private, kernelForm, LinearMap.mk₂_apply, mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      dsimp [ψ, ψ']
      ring
    rw [he, abs_mul, abs_of_pos hp0]
    refine (mul_le_mul_of_nonneg_left hb hp0.le).trans_eq ?_
    rw [offdiagPairPrice, ite_eq_left hc, privatePairCost_real]
    field_simp
  · rw [ite_eq_right hc] at hcases
    obtain ⟨⟨hS, hT, hST⟩, ⟨hU, hV, hUV⟩⟩ := hcases
    let ψ := fun (b : PairT (ZMod p)) z =>
      rawPairFeature (privateSupport true sc.1) (privateSupport true tc.1) ![b.val.1, b.val.2] z
    let ψ' := fun (b : PairT (ZMod p)) z =>
      rawPairFeature (privateSupport false sc.1) (privateSupport false tc.1) ![b.val.1, b.val.2] z
    have hb := core_rectangle_bound hDLK hp3 hp7 A _ _ _ _ hS hT hU hV hST hUV ψ ψ'
      (fun b z => rawPairFeature_abs _ _ ![b.val.1, b.val.2] z)
      (fun b z => rawPairFeature_abs _ _ ![b.val.1, b.val.2] z) hR hrow F G
    have he : kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
        (fun x y => A x.1 y.2 * A y.1 x.2 * chamberPairOffdiag sc.1 tc.1 x y) F G =
        (p : ℝ) * kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
          (fun x y => A x.1 y.2 * A y.1 x.2 *
            ip ((fieldLaw p).product (fieldLaw p))
              (fun z => offdiagFeature (coreSupport true sc.1) (coreSupport true tc.1) x.1.val z * ψ x.2 z)
              (fun z => offdiagFeature (coreSupport false sc.1) (coreSupport false tc.1) y.1.val z * ψ' y.2 z)) F G := by
      simp only [chamberPairOffdiag_core, kernelForm, LinearMap.mk₂_apply, mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      dsimp [ψ, ψ']
      ring
    rw [he, abs_mul, abs_of_pos hp0]
    refine (mul_le_mul_of_nonneg_left hb hp0.le).trans_eq ?_
    rw [offdiagPairPrice, ite_eq_right hc, corePairCost_real]
    field_simp

end Sarkozy.PositiveRoots.CoherentFrame
