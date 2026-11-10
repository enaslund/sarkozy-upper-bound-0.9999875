module

public import Sarkozy.TailCorrelations.TwoLayer
public import Sarkozy.F7Repair.Hybrid

@[expose] public section

/-!
# The tail correlation bounds `TailCorr` from Weil's bound (K2's field 10, outright)

`26_upper_comparison.tex`, (F7) at a tail prime `q ≥ P₄ = 2⁵¹²` (`lem:tail-prices`): the two
correlation inputs of a changed two-layer record are

* `ρ_new`: the bound `it:record:upper-F2` for `G^new` between its two layers;
* `ρ_old`: "the smaller of the bound `it:record:upper-F2` for `G` between its layers and
  `e^{ℓ_old}(gr + B_top r²)`" (the second from (F6) and `lem:recentering`(b)).

Both are taken here from the first alternative, (F2), which the paper allows. (F2) is
`prop:middle-negative`(b) / `cor:influence-schur`, formalized from Weil's bound
(`InfluenceGlue.middle_negative_b_weil`), and evaluated with crude uniform constants in
`Layer.lean`: `ρ ≤ 2⁸¹ r`. The (F6) route is not needed.

* **`rhoHat = 2⁸¹`**, the normalized constant of both bounds;
* **`newCorr`**, **`oldCorr`**: the two correlation bounds, for **every** two-layer record
  (`t, φ`) at every tail prime, not only the 28 changed records of degree two;
* **`tailCorr`**: F7Repair's `TailCorr` with `ρ̂_new = ρ̂_old = 2⁸¹`, from `Target.Weil` alone;
* **`tailCorr2`**: F7Repair's `TailCorr2` (the 28 degree-two records), from `Target.Weil` alone;
* **`tailRp`**: **K2's field 10 (`Cmp.Rp`) outright**: the (F7) one-way repair of every changed
  record at every tail prime, from `Target.Weil` alone (`F7Repair.corrRepairs`);
* **`tailRp_C_le`**: its constants, `C^ε_ρ ≤ tailConst(2⁸¹, 2⁸¹) · r ≤ 2⁸³ r`;
* **`tailRpHybrid`**, `tailRpHybrid_C_le`: the same through `F7Repair.hybridRepairs` (degree three
  with `C = 3`);
* **`tailRp_sum_π_le`**: `∑_{changed} π^ε_ρ ≤ ∑_{changed} c_ρ · tailConst(2⁸¹, 2⁸¹) · r`, the input
  to regenerate the tail ledger.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailCorrelations

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison Sarkozy.Recentering Sarkozy.TailPrices
  Sarkozy.F7Repair Sarkozy.Peyre
open Sarkozy.ComparisonLawPaper (tailNe)

/-- **The normalized correlation constant** `ρ̂ = 2⁸¹` (crude; `Layer.lean`). -/
noncomputable def rhoHat : ℝ := 2 ^ 81

/-- `q^{-1/2}` in the two conventions. -/
theorem tailR_eq_rp (q : ℕ) : tailR q = Influence.rp q := by
  unfold tailR Influence.rp
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg _), inv_eq_one_div]

variable {q : ℕ} [Fact q.Prime]

/-- (F2) between the layers of any two-layer field graph `Γ` at a tail prime:
`ρ(y_X; y_Y) ≤ 2⁸¹ q^{-1/2}` under `λ_q(Γ)`. -/
theorem layer_corrLe (hW : Target.Weil) (h4 : P4 ≤ q) {f₀ f₁ : FType}
    (Γ : OrientedGraph (f₀.Obj × f₁.Obj × Fin 2))
    (hN : (injLabellings (ZMod q) Γ).Nonempty) :
    CorrLe (graphLaw Γ hN) lay0 lay1 (rhoHat * tailR q) := by
  apply corrLe_of_maxCorr_le
  rw [tailR_eq_rp]
  exact layer_maxCorr_le (ne_two_of_P4 q h4) (weilBound_of_target hW q (ne_two_of_P4 q h4))
    (two_pow_512_le_of_P4 q h4) Γ (card_two_le _ _) hN

/-- **`ρ_new` of a tail record** ((F2) for `G^new` between its two layers), relative to the
marginals of `π^new`: `ρ_new ≤ 2⁸¹ q^{-1/2}`. -/
theorem newCorr (hW : Target.Weil) (h4 : P4 ≤ q) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    CentredBound (pairLaw (crudeLam hW h4 t φ) lay0 lay1)
      (margX (pairLaw (crudeLam hW h4 t φ) lay0 lay1))
      (margY (pairLaw (crudeLam hW h4 t φ) lay0 lay1)) (rhoHat * tailR q) :=
  centredBound_of_corrLe _ _ _ (layer_corrLe hW h4 _ (recN hW h4 t φ))

/-- **`ρ_old` of a tail record** ((F2) for `G = G_{φ₀φ₁,2}` between its layers), relative to
`μ^old` on both halves: `ρ_old ≤ 2⁸¹ q^{-1/2}`. -/
theorem oldCorr (hW : Target.Weil) (h4 : P4 ≤ q) (hne : TailNonempty q) (t : PType × PType) :
    ∀ h k, (oldHalf (tailOld q hne t)).expect h = 0 → (oldHalf (tailOld q hne t)).expect k = 0 →
      |(tailOld q hne t).expect (fun y => h (lay0 y) * k (lay1 y))| ≤
        rhoHat * tailR q * nrm (oldHalf (tailOld q hne t)) h *
          nrm (oldHalf (tailOld q hne t)) k :=
  oldCorr_of_corrLe _ (tailOld_symm hne t)
    (layer_corrLe hW h4 (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _))

omit [Fact q.Prime] in
theorem rhoHat_r_nonneg : 0 ≤ rhoHat * tailR q :=
  mul_nonneg (by unfold rhoHat; positivity) (tailR_nonneg q)

omit [Fact q.Prime] in
theorem rhoHat_r_le_half (h4 : P4 ≤ q) : rhoHat * tailR q ≤ 1 / 2 := by
  have h := tailR_le h4
  unfold rhoHat
  calc (2 : ℝ) ^ 81 * tailR q ≤ 2 ^ 81 * (1 / 2 ^ 256) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 1 / 2 := by norm_num

/-- **`TailCorr` of every two-layer record at every tail prime, from Weil's bound**, with
`ρ̂_new = ρ̂_old = 2⁸¹` ((F2) for `G^new` and for `G`, `it:record:upper-F2`; F7Repair's
hypothesis structure, discharged). -/
noncomputable def tailCorr (hW : Target.Weil) (h4 : P4 ≤ q) (hne : TailNonempty q)
    (t : PType × PType) (φ : t.1.Pat × t.2.Pat) : TailCorr hW h4 hne t φ rhoHat rhoHat where
  ρ := rhoHat * tailR q
  ρ_nonneg := rhoHat_r_nonneg
  ρ_half := rhoHat_r_le_half h4
  ρ_le := le_rfl
  corr := newCorr hW h4 t φ
  ρold := rhoHat * tailR q
  ρold_nonneg := rhoHat_r_nonneg
  ρold_le := le_rfl
  old_corr := oldCorr hW h4 hne t

/-- **`TailCorr2` (the 28 degree-two changed records) from Weil's bound.** -/
noncomputable def tailCorr2 (hW : Target.Weil) : TailCorr2 hW (fun _ => rhoHat) (fun _ => rhoHat) :=
  fun _ _ h4 t φ _ _ => tailCorr hW h4 (tailNe hW h4) t φ

/-- **K2's field 10 (`Cmp.Rp`), outright from `Target.Weil`**: the (F7) one-way repair of every
changed record at every tail prime (`lem:tail-prices`(i),(ii), `lem:tr:repair`, (F7), with
`ρ_new`, `ρ_old` from (F2)). -/
noncomputable def tailRp (hW : Target.Weil) :
    ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (tailNe hW h4) :=
  corrRepairs hW (fun _ => rhoHat) (fun _ => rhoHat)
    (fun _ _ h4 t φ _ => tailCorr hW h4 (tailNe hW h4) t φ)

/-- `tailConst(2⁸¹, 2⁸¹) = (2 + 2⁻¹⁰) 2⁸¹ + 2⁻⁵⁰ ≤ 2⁸³`. -/
theorem tailConst_rhoHat : tailConst rhoHat rhoHat = (2 + 1 / 2 ^ 10) * 2 ^ 81 + 1 / 2 ^ 50 := by
  unfold tailConst rhoHat
  ring

theorem tailConst_rhoHat_le : tailConst rhoHat rhoHat ≤ 2 ^ 83 := by
  rw [tailConst_rhoHat]
  norm_num

/-- **The constants of `tailRp`**: `C^ε_ρ ≤ tailConst(2⁸¹, 2⁸¹) · q^{-1/2}` for every changed
record and both change types. -/
theorem tailRp_C_le (hW : Target.Weil) (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (h : upperFate (true, ⟨t, φ⟩) = .changed) (e : ChangeType) :
    (tailRp hW q h4 t φ h).C e ≤ tailConst rhoHat rhoHat * tailR q :=
  corrRepairs_C_le hW _ _ _ q h4 t φ h e

theorem tailRp_C_le' (hW : Target.Weil) (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (h : upperFate (true, ⟨t, φ⟩) = .changed) (e : ChangeType) :
    (tailRp hW q h4 t φ h).C e ≤ 2 ^ 83 * tailR q :=
  (tailRp_C_le hW q h4 t φ h e).trans
    (mul_le_mul_of_nonneg_right tailConst_rhoHat_le (tailR_nonneg q))

/-- **The tail repair prices of `tailRp`**: `∑_{changed} π^ε_ρ ≤ ∑_{changed} c_ρ ·
tailConst(2⁸¹, 2⁸¹) · q^{-1/2}`. -/
theorem tailRp_sum_π_le (hW : Target.Weil) (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q)
    (e : ChangeType) :
    ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), (tailRp hW q h4).π ρ e ≤
      ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed),
        upCoeff tailWeights (tailR q) ρ * tailConst rhoHat rhoHat * tailR q :=
  (tailRp hW q h4).sum_π_le (fun _ => tailConst rhoHat rhoHat) e
    (fun t φ h => tailRp_C_le hW q h4 t φ h e)

/-- **K2's field 10 through `hybridRepairs`**: (F7) for the 28 degree-two records with the
correlation bounds of `tailCorr2`, the replacement `λ_q(G^new)` with `C = 3` for the others. -/
noncomputable def tailRpHybrid (hW : Target.Weil) :
    ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (tailNe hW h4) :=
  hybridRepairs hW (fun _ => rhoHat) (fun _ => rhoHat) (tailCorr2 hW)

theorem tailRpHybrid_C_le (hW : Target.Weil) (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q)
    (t : PType × PType) (φ : t.1.Pat × t.2.Pat) (h : upperFate (true, ⟨t, φ⟩) = .changed)
    (e : ChangeType) :
    (tailRpHybrid hW q h4 t φ h).C e ≤
      hybridBound (fun _ => rhoHat) (fun _ => rhoHat) (tailR q) (true, ⟨t, φ⟩) :=
  hybrid_C_le hW _ _ (tailCorr2 hW) q h4 t φ h e

end Sarkozy.TailCorrelations
