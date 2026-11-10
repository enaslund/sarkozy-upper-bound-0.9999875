module

public import Sarkozy.Variance.WeightedIdentity
public import Sarkozy.PositiveRoots.RootMass
public import Sarkozy.L20Cap.CoreCount

/-! Transfer the verified weighted moment to the actual admissible core law. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.Variance Sarkozy.Variance.WeightedMoment
open Sarkozy.Variance.WeightedIdentityCertificate

variable {p : ℕ} [Fact p.Prime]

theorem core_sum_admissible (f : ZMod p → ZMod p → ZMod p → ZMod p → ℝ) :
    (∑ C : CoreT (ZMod p), f (C.val 0) (C.val 1) (C.val 2) (C.val 3)) =
      ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p,
        if IsAdm p a b c d then f a b c d else 0 := by
  rw [← sum_subtype (univ.filter (fun x : Fin 4 → ZMod p => Adm x)) (by simp)
    (fun x => f (x 0) (x 1) (x 2) (x 3))]
  rw [sum_filter]
  calc
    _ = ∑ y : ZMod p × ZMod p × ZMod p × ZMod p,
        if IsAdm p y.1 y.2.1 y.2.2.1 y.2.2.2 then f y.1 y.2.1 y.2.2.1 y.2.2.2 else 0 := by
      apply Fintype.sum_equiv fourEquiv
      intro x
      change (if Adm x then f (x 0) (x 1) (x 2) (x 3) else 0) =
        if IsAdm p (x 0) (x 1) (x 2) (x 3) then f (x 0) (x 1) (x 2) (x 3) else 0
      simp only [adm_iff_isAdm]
    _ = _ := by simp only [Fintype.sum_prod_type]

variable [Nonempty (CoreT (ZMod p))]

theorem core_expect_admissible (f : ZMod p → ZMod p → ZMod p → ZMod p → ℝ) :
    coreLaw.expect (fun C : CoreT (ZMod p) => f (C.val 0) (C.val 1) (C.val 2) (C.val 3)) =
      (∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p,
        if IsAdm p a b c d then f a b c d else 0) / (nAdm p : ℝ) := by
  rw [coreLaw, FiniteLaw.expect_uniform, core_sum_admissible]
  have hc : (Fintype.card (CoreT (ZMod p)) : ℝ) = (nAdm p : ℝ) := by
    exact_mod_cast (card_coreT_eq_nAdm (p := p))
  rw [hc]

theorem core_softW_second_moment (hp3 : p % 4 = 3) (hp7 : 7 < p)
    (hAO : Target.AhlgrenOno) {r : ℝ} (hr : r * Real.sqrt p = 1) :
    coreLaw.expect (fun C : CoreT (ZMod p) =>
      ((RootMarginal.softW (C.val 0) (C.val 1) (C.val 2) (C.val 3) : ℝ) / p) ^ 2) ≤
      (5 * (1 / (p : ℝ)) + 34 * (1 / (p : ℝ)) * r + 11 * (1 / (p : ℝ)) ^ 3) /
        RootMarginal.Z4 (1 / (p : ℝ)) := by
  rw [core_expect_admissible (fun a b c d => ((RootMarginal.softW a b c d : ℝ) / p) ^ 2)]
  exact weightedMoment_hmom_verified p hp3 hp7 hAO hr

omit [Nonempty (CoreT (ZMod p))] in
theorem higher_softIntegrand (x : Fin 4 → ZMod p) (z : ZMod p) :
    (∑ S ∈ higher.filter (fun S : Finset (Fin 4) => ¬ S.card = 2), sig S * psi S z x) =
      softIntegrand (ZMod p) (x 0) (x 1) (x 2) (x 3) z := by
  have hf : higher.filter (fun S : Finset (Fin 4) => ¬ S.card = 2) =
      {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}} := by decide +kernel
  rw [hf]
  have h0 : ({0, 1, 2} : Finset (Fin 4)) ∉
      ({{0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}} : Finset (Finset (Fin 4))) := by decide +kernel
  have h1 : ({0, 1, 3} : Finset (Fin 4)) ∉
      ({{0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}} : Finset (Finset (Fin 4))) := by decide +kernel
  have h2 : ({0, 2, 3} : Finset (Fin 4)) ∉
      ({{1, 2, 3}, {0, 1, 2, 3}} : Finset (Finset (Fin 4))) := by decide +kernel
  have h3 : ({1, 2, 3} : Finset (Fin 4)) ∉
      ({{0, 1, 2, 3}} : Finset (Finset (Fin 4))) := by decide +kernel
  rw [sum_insert h0, sum_insert h1, sum_insert h2, sum_insert h3, sum_singleton]
  norm_num [sig, psi, sgn, softIntegrand]
  ring

omit [Nonempty (CoreT (ZMod p))] in
theorem Kbar_softW (hp2 : p ≠ 2) (C : CoreT (ZMod p)) :
    Kbar C.val - 1 = 2 / (p : ℝ) +
      (RootMarginal.softW (C.val 0) (C.val 1) (C.val 2) (C.val 3) : ℝ) / p := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  rw [Kbar_expansion hF C.property.1, ZMod.card]
  simp_rw [higher_softIntegrand]
  rw [softIntegrand_sum]

end Sarkozy.PositiveRoots.CoherentFrame
