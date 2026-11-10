module

public import Sarkozy.SpectralD.RootTailErrors
public import Sarkozy.SpectralD.TailAnalyticInputs
public import Sarkozy.SpectralD.FiniteRowTest
public import Sarkozy.SpectralD.RootCriterionExp

/-!
# The two root spectral bounds at class-three tail primes

For p ≥ 2^512 and p = 3 mod 4, the LL20 and LL22 operators have lower
bounds -113/sqrt(p) and -45/sqrt(p), respectively. All numerical and
analytic inputs of the spectral criterion are supplied here. The named
Weil, moving-root, and four-cycle literature inputs remain hypotheses.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Sarkozy.Labellings Sarkozy.Extraction Sarkozy.SpectralC Sarkozy.SpectralD.Cx
open scoped InnerProductSpace

variable {p : ℕ} [Fact p.Prime]

theorem LL20_tail_three (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hp3 : p % 4 = 3)
    (hne : (injLabellings (ZMod p) LL20.G).Nonempty)
    (v : EuclideanSpace ℝ (LL20.cut.Half → ZMod p)) :
    -(113 * rp p) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp LL20 hne v⟫_ℝ := by
  have hp52 : 2 ^ 52 ≤ p := by omega
  let Adj : LL20.cut.Half → LL20.cut.Half → Prop := fun _ _ => False
  let : DecidableRel Adj := fun _ _ => inferInstanceAs (Decidable False)
  have he := (errors_of_S1 LL20 card_slot.le LL20_hdeg (coarseErr_root_lt_nat hp52)).2.2.1
  have hb := LL20_tail_expansion_bounds
    (weilBound_of_target hW p (ne_two_of_ge hp52)) h4 hp hne he
  have ha := tail_analytic_inputs LL20 hp card_slot.le LL20_card_half
    LL20_hdeg LL20_d0_le LL20_r_le
  exact LL20_criterion_exp hW hMR Adj hp52 hp3 hne
    (εZ := 1 / 100) (Nns := 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹)
    (Dcol := 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹)
    (ΓE := 1 / 100000000) (εH := 1 / 1000) (ρβ := 1 / 2000) (ρX := 1 / 2000)
    (θ := 64) (ηQ := 1 / 1000) (εV := 1 / 100000) (ρs := 2⁻¹ ^ 40) (ρv := 36)
    (cbar := 1 / 4) (ηQbar := 1) (ηBbar := 1) (εVbar := 1 / 100) (sp := 110) (sm := 110)
    (by norm_num) hb.1 hb.2.1 hb.2.2.1 ha.coupling ha.beta ha.cross
    (by norm_num) (by norm_num) (by norm_num) ha.theta
    (by norm_num) ha.smallX
    (by simpa only [LL20_card_half, Nat.cast_ofNat, rp] using tail_etaQ hp (d := 12) le_rfl)
    ha.smallV
    (by simpa only [LL20_card_half, Nat.cast_ofNat, rp] using tail_epsilonV hp)
    (by norm_num) (by norm_num) hb.2.2.2 (by norm_num)
    (etaB_tail hp hp3 ha.density (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun ξ _ => LL20_tail_finiteTest hp3 Adj ξ) (fun ξ _ => LL20_tail_finiteTest hp3 Adj ξ)
    LL20_tail_finite_cap LL20_tail_finite_cap v

theorem LL22_tail_three (hW : Target.Weil) (hMR : Target.MovingRoot) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hp3 : p % 4 = 3)
    (hne : (injLabellings (ZMod p) LL22.G).Nonempty)
    (v : EuclideanSpace ℝ (LL22.cut.Half → ZMod p)) :
    -(45 * rp p) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp LL22 hne v⟫_ℝ := by
  have hp52 : 2 ^ 52 ≤ p := by omega
  let Adj : LL22.cut.Half → LL22.cut.Half → Prop := fun _ _ => False
  let : DecidableRel Adj := fun _ _ => inferInstanceAs (Decidable False)
  have he := (errors_of_S1 LL22 card_slot.le LL22_hdeg (coarseErr_root_lt_nat hp52)).2.2.1
  have hb := LL22_tail_expansion_bounds
    (weilBound_of_target hW p (ne_two_of_ge hp52)) h4 hp hne he
  have ha := tail_analytic_inputs LL22 hp card_slot.le LL22_card_half LL22_hdeg LL22_d0_le
    (fun k => (LL22_r_le k).trans (by norm_num))
  exact LL22_criterion_exp hW hMR Adj hp52 hp3 hne
    (εZ := 1 / 100) (Nns := 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹)
    (Dcol := 2⁻¹ ^ 200 * (Real.sqrt p)⁻¹)
    (ΓE := 1 / 100000000) (εH := 1 / 1000) (ρβ := 1 / 2000) (ρX := 1 / 2000)
    (θ := 64) (ηQ := 1 / 1000) (εV := 1 / 100000) (ρs := 2⁻¹ ^ 40) (ρv := 36)
    (cbar := 1 / 4) (ηQbar := 1) (ηBbar := 1) (εVbar := 1 / 100) (sp := 44) (sm := 44)
    (by norm_num) hb.1 hb.2.1 hb.2.2.1 ha.coupling ha.beta ha.cross
    (by norm_num) (by norm_num) (by norm_num) ha.theta
    (by norm_num) ha.smallX
    (by simpa only [LL22_card_half, Nat.cast_ofNat, rp] using tail_etaQ hp (d := 10) (by norm_num))
    ha.smallV
    (by simpa only [LL22_card_half, Nat.cast_ofNat, rp] using tail_epsilonV hp)
    (by norm_num) (by norm_num) hb.2.2.2 (by norm_num)
    (etaB_tail hp hp3 ha.density (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun ξ _ => LL22_tail_finiteTest hp3 Adj ξ) (fun ξ _ => LL22_tail_finiteTest hp3 Adj ξ)
    LL22_tail_finite_cap LL22_tail_finite_cap v

end Sarkozy.SpectralD.Root
