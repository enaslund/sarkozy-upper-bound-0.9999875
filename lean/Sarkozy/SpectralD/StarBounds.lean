module

public import Sarkozy.SecondOrder.StarUniform
public import Sarkozy.SpectralD.CollisionNumerics
public import Sarkozy.SpectralD.RootCriterion

/-!
# Uniform star bounds for the root graphs

The pinned error is bounded by the coarse count error. For both root
halves, its value is at most 1/10000 at primes at least 2^64. This supplies
the remaining gate in the uniform star mean and variance estimates.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.SecondOrder

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

theorem graphCountError_le_coarse (G : OrientedGraph U) (i : U) :
    graphCountError (p := p) G i ≤
      coarseError (graphNbrs G i).card p (Fintype.card U) := by
  let t := (graphNbrs G i).card
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hsoft := Cuts.SpecData.softError_le hp1 t
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  rw [div_le_iff₀ h2] at hsoft
  have hs : (p : ℝ) * (Real.sqrt p)⁻¹ = Real.sqrt p := by
    rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hs0.ne', Real.mul_self_sqrt hp0.le]
  have hE : coarseError t p (Fintype.card U) * p =
      2 ^ t * (coarseH t * Real.sqrt p + Fintype.card U) := by
    unfold coarseError
    rw [inv_pow, Real.sq_sqrt hp0.le]
    calc _ = 2 ^ t * (coarseH t * ((p : ℝ) * (Real.sqrt p)⁻¹) +
          Fintype.card U * ((p : ℝ) * (p : ℝ)⁻¹)) := by ring
      _ = _ := by rw [hs, mul_inv_cancel₀ hp0.ne', mul_one]
  unfold graphCountError
  change (_ : ℝ) / p ≤ coarseError t p (Fintype.card U)
  rw [div_le_iff₀ hp0, hE]
  change softError p t + 2 ^ t * ((Fintype.card U : ℝ) - 1) ≤ _
  have hsoft' : softError p t ≤ coarseH t * Real.sqrt p * 2 ^ t := by
    simpa only [coarseH, one_div] using hsoft
  nlinarith

theorem graphCountError_root_bound (G : OrientedGraph U) (hn : Fintype.card U = 36)
    (hd : ∀ i, (graphNbrs G i).card ≤ 10) (hp : 2 ^ 64 ≤ p) (i : U) :
    graphCountError (p := p) G i ≤ 1 / 10000 := by
  have h := graphCountError_le_coarse (p := p) G i
  rw [hn] at h
  exact h.trans ((coarseError_mono (by norm_num) (hd i)).trans
    (collision_error10 (by exact_mod_cast hp)))

theorem LL20_starMstar (hW : WeilBound (ZMod p)) (hp : 2 ^ 64 ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL20.halfGraph).Nonempty)
    (he : ∀ i, graphCountError (p := p) Root.LL20.halfGraph i < 1) :
    Spectral.starMstar (graphPinned hW Root.LL20.halfGraph hne he) Root.LL20.Nset
      (Spectral.starCoef (p := p) Root.LL20) ≤ 2 ^ 84 * (1 / Real.sqrt p) := by
  have hd : ∀ i, (graphNbrs Root.LL20.halfGraph i).card ≤ 10 := fun i => by
    rw [← nbrCount_erase_self]; exact Root.LL20_d0_le i
  exact starMstar_uniform _ _ _ (Spectral.starCoef_abs_le _)
    Root.LL20_card_half Root.LL20_card_half hd (fun i =>
      (graphCountError_root_bound _ Root.LL20_card_half hd hp i).trans (by norm_num))

theorem LL22_starMstar (hW : WeilBound (ZMod p)) (hp : 2 ^ 64 ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL22.halfGraph).Nonempty)
    (he : ∀ i, graphCountError (p := p) Root.LL22.halfGraph i < 1) :
    Spectral.starMstar (graphPinned hW Root.LL22.halfGraph hne he) Root.LL22.Nset
      (Spectral.starCoef (p := p) Root.LL22) ≤ 2 ^ 84 * (1 / Real.sqrt p) := by
  have hd : ∀ i, (graphNbrs Root.LL22.halfGraph i).card ≤ 10 := fun i => by
    rw [← nbrCount_erase_self]; exact Root.LL22_d0_le i
  exact starMstar_uniform _ _ _ (Spectral.starCoef_abs_le _)
    Root.LL22_card_half Root.LL22_card_half hd (fun i =>
      (graphCountError_root_bound _ Root.LL22_card_half hd hp i).trans (by norm_num))

theorem LL20_starZstar (hW : WeilBound (ZMod p)) (hp : 2 ^ 64 ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL20.halfGraph).Nonempty)
    (he : ∀ i, graphCountError (p := p) Root.LL20.halfGraph i < 1) :
    Spectral.starZstar (graphPinned hW Root.LL20.halfGraph hne he) Root.LL20.Nset
      (Spectral.starCoef (p := p) Root.LL20) ≤ 2 ^ 88 * (1 / Real.sqrt p) ^ 2 := by
  have hd : ∀ i, (graphNbrs Root.LL20.halfGraph i).card ≤ 10 := fun i => by
    rw [← nbrCount_erase_self]; exact Root.LL20_d0_le i
  exact starZstar_uniform _ _ _ (Spectral.starCoef_abs_le _)
    Root.LL20_card_half Root.LL20_card_half hd (fun i =>
      (graphCountError_root_bound _ Root.LL20_card_half hd hp i).trans (by norm_num))

theorem LL22_starZstar (hW : WeilBound (ZMod p)) (hp : 2 ^ 64 ≤ p)
    (hne : (injLabellings (ZMod p) Root.LL22.halfGraph).Nonempty)
    (he : ∀ i, graphCountError (p := p) Root.LL22.halfGraph i < 1) :
    Spectral.starZstar (graphPinned hW Root.LL22.halfGraph hne he) Root.LL22.Nset
      (Spectral.starCoef (p := p) Root.LL22) ≤ 2 ^ 88 * (1 / Real.sqrt p) ^ 2 := by
  have hd : ∀ i, (graphNbrs Root.LL22.halfGraph i).card ≤ 10 := fun i => by
    rw [← nbrCount_erase_self]; exact Root.LL22_d0_le i
  exact starZstar_uniform _ _ _ (Spectral.starCoef_abs_le _)
    Root.LL22_card_half Root.LL22_card_half hd (fun i =>
      (graphCountError_root_bound _ Root.LL22_card_half hd hp i).trans (by norm_num))

end Sarkozy.SpectralD
