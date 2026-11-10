module

public import Sarkozy.F7Repair.TailFine

@[expose] public section

/-!
# The (F7) repair at the tail from H1 and two correlation bounds (K2's field 10)

`paper/sections/26_upper_comparison.tex`, (F7), at a tail prime `q ≥ P₄` (`lem:tail-prices`):

* `fineU q = R_q^{144} − 1 ≤ 2⁹⁹/√q` (`fineU_le`);
* **`tailOneWay`**: the `OneWayData` of `π^new = λ_q(G^new)` with targets `μ^old`, with
  `U = fineU q`, `K_∞ = 2¹⁴⁴` and the gate `2F < 1` proved from H1; the only input is the centred
  correlation bound `ρ_new ≤ 1/2` of `π^new` (*hypothesis*, (F2));
* **`TailCorr`**: the two correlation bounds of a changed record at the prime, `ρ_new` for
  `π^new` and `ρ_old` for the old record, with normalized constants `ρ̂_new`, `ρ̂_old`:
  `ρ_new ≤ ρ̂_new r`, `ρ_old ≤ ρ̂_old r` (*hypotheses*, (F2) and (F6)/`lem:recentering`(b));
* **`TailCorr.toRepair`**: the (F7) one-way repair as T2's `TailRepair`;
* **`TailCorr.C_le`**: its constant is at most `tailConst ρ̂_new ρ̂_old · r` with
  `tailConst ρ̂_new ρ̂_old = ρ̂_old + (1 + 2⁻¹⁰)ρ̂_new + 2⁻⁵⁰`;
* **`corrRepairs`**, **`corrRepairs_C_le`**: K2's field 10 from the correlation bounds at every
  tail prime, and the per-record constants (field 11 in the form "explicit constant times `r`").
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison Sarkozy.Recentering Sarkozy.Structured
  Sarkozy.TailPrices

/-- `U_q = R_q^{144} − 1`. -/
noncomputable def fineU (q : ℝ) : ℝ := fineR q ^ 144 - 1

theorem fineU_nonneg (q : ℝ) : 0 ≤ fineU q := by
  unfold fineU
  have := one_le_pow₀ (n := 144) (fineR_ge_one q)
  linarith

theorem fineU_le {q : ℝ} (hq : 2 ^ 512 ≤ q) : fineU q ≤ 2 ^ 99 / Real.sqrt q := by
  unfold fineU
  linarith [fineR_pow_le hq]

/-- `fineU q ≤ 2⁻¹⁵⁷` at `q ≥ 2⁵¹²`. -/
theorem fineU_le' {q : ℝ} (hq : 2 ^ 512 ≤ q) : fineU q ≤ 2 ^ 99 / 2 ^ 256 :=
  (fineU_le hq).trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (sqrt_ge_of_large hq))

/-- Two-sided density bounds give `|μ − m| ≤ (R − 1) m`. -/
theorem abs_sub_le_of_two_sided {μ m R : ℝ} (h1 : μ ≤ R * m) (h2 : m ≤ R * μ) (hR : 1 ≤ R)
    (hm : 0 ≤ m) : |μ - m| ≤ (R - 1) * m := by
  rw [abs_le]
  constructor
  · have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    have key : 0 ≤ R * ((R - 1) * m - (m - μ)) := by
      nlinarith [mul_nonneg hm (sq_nonneg (R - 1))]
    have := (mul_nonneg_iff_of_pos_left hR0).mp key
    linarith
  · nlinarith

theorem map_weight_eq_expect {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (lam : FiniteLaw Ω) (a : Ω → Ξ) (z : Ξ) :
    (lam.map a).weight z = lam.expect (fun ω => if a ω = z then 1 else 0) := by
  change (∑ ω, if a ω = z then lam.weight ω else 0) = ∑ ω, lam.weight ω * _
  exact sum_congr rfl fun ω _ => by split_ifs <;> simp

variable {q : ℕ} [Fact q.Prime]

/-- The two layers of the old tail record have the same law (weights). -/
theorem tailOld_layer_weight (hne : TailNonempty q) (t : PType × PType)
    (y : t.1.field.Obj × t.2.field.Obj → ZMod q) :
    ((tailOld q hne t).map lay1).weight y = (oldHalf (tailOld q hne t)).weight y := by
  unfold oldHalf
  rw [map_weight_eq_expect, map_weight_eq_expect]
  exact tailOld_symm hne t (fun x => if x = y then 1 else 0)

/-- The layer-`k` densities of `λ_q(G^new)` against the old record, both directions. -/
theorem tail_dens (hW : Target.Weil) (h4 : P4 ≤ q) (hne : TailNonempty q) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (k : Fin 2) (x : t.1.field.Obj × t.2.field.Obj → ZMod q) :
    |((tailOld q hne t).map (fun y => layerOf y k)).weight x -
        ((crudeLam hW h4 t φ).map (fun y => layerOf y k)).weight x| ≤
      fineU (Fintype.card (ZMod q)) * ((crudeLam hW h4 t φ).map (fun y => layerOf y k)).weight x := by
  have hWeil := weilBound_of_target hW q (ne_two_of_P4 q h4)
  have h1 := layer_density_fine hWeil (fieldGraph t.1.field t.2.field (Fin 2))
    (newGraph t.1.field t.2.field (recQ t φ)) (hne.two _ _) (recN hW h4 t φ) k
    (fun x => (feasible_layerSet_iff _ _ _ k x).symm) (card_zmod_large h4) (card_two_le _ _) x
  have h2 := layer_density_fine hWeil (newGraph t.1.field t.2.field (recQ t φ))
    (fieldGraph t.1.field t.2.field (Fin 2)) (recN hW h4 t φ) (hne.two _ _) k
    (fun x => feasible_layerSet_iff _ _ _ k x) (card_zmod_large h4) (card_two_le _ _) x
  have hR : 1 ≤ fineR (Fintype.card (ZMod q)) ^ 144 := one_le_pow₀ (fineR_ge_one _)
  have h := abs_sub_le_of_two_sided h1 h2 hR ((FiniteLaw.nonneg _) x)
  unfold fineU
  exact h

/-- **The one-way data of a tail record from H1 and `ρ_new ≤ 1/2`** ((F7), "Densities", with
`U = fineU q`, `K_∞ = 2¹⁴⁴`). -/
noncomputable def tailOneWay (hW : Target.Weil) (h4 : P4 ≤ q) (hne : TailNonempty q)
    (t : PType × PType) (φ : t.1.Pat × t.2.Pat) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2)
    (hcorr : CentredBound (pairLaw (crudeLam hW h4 t φ) lay0 lay1)
      (margX (pairLaw (crudeLam hW h4 t φ) lay0 lay1))
      (margY (pairLaw (crudeLam hW h4 t φ) lay0 lay1)) ρ) :
    OneWayData (pairLaw (crudeLam hW h4 t φ) lay0 lay1) (oldHalf (tailOld q hne t))
      (oldHalf (tailOld q hne t)) where
  U := fineU (Fintype.card (ZMod q))
  ρ := ρ
  K := 2 ^ 144
  U_nonneg := fineU_nonneg _
  ρ_nonneg := hρ0
  ρ_lt_one := by linarith
  K_nonneg := by positivity
  twoF_lt := by
    have hU := fineU_le' (card_zmod_large h4)
    have hU0 := fineU_nonneg ((Fintype.card (ZMod q) : ℕ) : ℝ)
    have hd : (1 / 2 : ℝ) ≤ 1 - ρ := by linarith
    have hK : (2 : ℝ) ^ 144 / (1 - ρ) ≤ 2 ^ 145 := by
      rw [div_le_iff₀ (by linarith)]
      have e := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 ^ 145)
      have e2 : (2 : ℝ) ^ 145 * (1 / 2) = 2 ^ 144 := by norm_num
      linarith only [e, e2]
    have hK0 : (0 : ℝ) ≤ 2 ^ 144 / (1 - ρ) := div_nonneg (by positivity) (by linarith)
    calc 2 * (fineU (Fintype.card (ZMod q)) * (1 + 2 ^ 144 / (1 - ρ)))
        ≤ 2 * (2 ^ 99 / 2 ^ 256 * (1 + 2 ^ 145)) := by gcongr
      _ < 1 := by norm_num
  dens_X x := by
    rw [mX_pairLaw]
    exact tail_dens hW h4 hne t φ 0 x
  dens_Y y := by
    rw [mY_pairLaw, ← tailOld_layer_weight hne t y]
    exact tail_dens hW h4 hne t φ 1 y
  corr := hcorr
  sup x y := tail_sup hW h4 t φ x y

/-- **The two correlation bounds of a changed tail record at one prime** ((F2) for `π^new`, (F6)
with `lem:recentering`(b) for the old record), with normalized constants `ρ̂_new`, `ρ̂_old`:
`ρ_new ≤ min(ρ̂_new r, 1/2)` and `ρ_old ≤ ρ̂_old r`. *Hypotheses*. -/
structure TailCorr (hW : Target.Weil) (h4 : P4 ≤ q) (hne : TailNonempty q) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (ρh ρoh : ℝ) where
  /-- `ρ_new`. -/
  ρ : ℝ
  ρ_nonneg : 0 ≤ ρ
  ρ_half : ρ ≤ 1 / 2
  ρ_le : ρ ≤ ρh * tailR q
  /-- The centred correlation of `π^new` between its halves is at most `ρ_new`. -/
  corr : CentredBound (pairLaw (crudeLam hW h4 t φ) lay0 lay1)
    (margX (pairLaw (crudeLam hW h4 t φ) lay0 lay1))
    (margY (pairLaw (crudeLam hW h4 t φ) lay0 lay1)) ρ
  /-- `ρ_old`. -/
  ρold : ℝ
  ρold_nonneg : 0 ≤ ρold
  ρold_le : ρold ≤ ρoh * tailR q
  /-- `ρ(π^old) ≤ ρ_old` relative to `μ^old`. -/
  old_corr : ∀ h k, (oldHalf (tailOld q hne t)).expect h = 0 →
    (oldHalf (tailOld q hne t)).expect k = 0 →
    |(tailOld q hne t).expect (fun y => h (lay0 y) * k (lay1 y))| ≤
      ρold * nrm (oldHalf (tailOld q hne t)) h * nrm (oldHalf (tailOld q hne t)) k

/-- **The explicit tail constant** `ρ̂_old + (1 + 2⁻¹⁰)ρ̂_new + 2⁻⁵⁰`. -/
noncomputable def tailConst (ρh ρoh : ℝ) : ℝ := ρoh + (1 + 1 / 2 ^ 10) * ρh + 1 / 2 ^ 50

namespace TailCorr

variable {hW : Target.Weil} {h4 : P4 ≤ q} {hne : TailNonempty q} {t : PType × PType}
  {φ : t.1.Pat × t.2.Pat} {ρh ρoh : ℝ} (T : TailCorr hW h4 hne t φ ρh ρoh)

/-- The (F7) inputs of the record. -/
noncomputable def toGraph : TailF7Graph hne t φ where
  Q := recQ t φ
  hQ := recQ_mem t φ
  hN := recN hW h4 t φ
  D := tailOneWay hW h4 hne t φ T.ρ T.ρ_nonneg T.ρ_half T.corr
  ρold := T.ρold
  ρold_nonneg := T.ρold_nonneg
  old_corr := T.old_corr

/-- **The (F7) one-way repair of the record**, as T2's `TailRepair`. -/
noncomputable def toRepair : TailRepair q hne t φ := T.toGraph.toTailF7.toRepair

/-- **The repair constant is at most `tailConst ρ̂_new ρ̂_old · r`.** -/
theorem C_le (e : ChangeType) : T.toRepair.C e ≤ tailConst ρh ρoh * tailR q := by
  rw [toRepair, TailF7.toRepair_C]
  have hr := tailR_le h4
  have hr0 := tailR_nonneg q
  set r := tailR q
  set D := tailOneWay hW h4 hne t φ T.ρ T.ρ_nonneg T.ρ_half T.corr
  change T.ρold + D.ρ' ≤ _
  have hU : D.U ≤ 2 ^ 99 * r := by
    have h1 := fineU_le (card_zmod_large h4)
    change fineU _ ≤ _
    refine h1.trans (le_of_eq ?_)
    rw [ZMod.card]
    unfold r tailR
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  have hU0 := D.U_nonneg
  have hF := D.twoF_lt'
  have hF0 := D.F_nonneg
  have hUs : D.U ≤ 2 ^ 99 / 2 ^ 256 := by
    refine hU.trans ?_
    have := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ 2 ^ 99)
    calc 2 ^ 99 * r ≤ 2 ^ 99 * (1 / 2 ^ 256) := this
      _ = 2 ^ 99 / 2 ^ 256 := by ring
  have hρ : D.ρ ≤ ρh * r := T.ρ_le
  have hρ0 : 0 ≤ D.ρ := T.ρ_nonneg
  have hd : (1 / 2 : ℝ) ≤ 1 - D.U := by
    have : (2 : ℝ) ^ 99 / 2 ^ 256 ≤ 1 / 2 := by norm_num
    linarith only [this, hUs]
  have hρh : 0 ≤ ρh * r := hρ0.trans hρ
  have hd' : (1 / 2 : ℝ) ≤ 1 - D.ρ := by
    have : D.ρ ≤ 1 / 2 := T.ρ_half
    linarith only [this]
  have hK : D.K / (1 - D.ρ) ≤ 2 ^ 145 := by
    change (2 : ℝ) ^ 144 / (1 - D.ρ) ≤ 2 ^ 145
    rw [div_le_iff₀ (by linarith only [hd'])]
    have e := mul_le_mul_of_nonneg_left hd' (by positivity : (0 : ℝ) ≤ 2 ^ 145)
    have e2 : (2 : ℝ) ^ 145 * (1 / 2) = 2 ^ 144 := by norm_num
    linarith only [e, e2]
  have hFle : D.F ≤ 2 ^ 99 / 2 ^ 256 * (1 + 2 ^ 145) := by
    unfold OneWayData.F
    have hK0 : 0 ≤ D.K / (1 - D.ρ) := div_nonneg D.K_nonneg (by linarith only [hd'])
    exact mul_le_mul hUs (by linarith only [hK]) (by linarith only [hK0]) (by positivity)
  have e2 : (1 + 2 * D.F) ≤ (1 + 1 / 2 ^ 10) * (1 - D.U) := by
    have : 1 + 2 * (2 ^ 99 / 2 ^ 256 * (1 + 2 ^ 145) : ℝ) ≤
        (1 + 1 / 2 ^ 10) * (1 - 2 ^ 99 / 2 ^ 256) := by norm_num
    have e3 : (1 + 1 / 2 ^ 10 : ℝ) * (1 - 2 ^ 99 / 2 ^ 256) ≤ (1 + 1 / 2 ^ 10) * (1 - D.U) :=
      mul_le_mul_of_nonneg_left (by linarith only [hUs]) (by norm_num)
    linarith only [this, hFle, e3]
  have h1 : D.ρ * (1 + 2 * D.F) ≤ (1 + 1 / 2 ^ 10) * (ρh * r) * (1 - D.U) := by
    calc D.ρ * (1 + 2 * D.F) ≤ ρh * r * (1 + 2 * D.F) :=
          mul_le_mul_of_nonneg_right hρ (by linarith only [hF0])
      _ ≤ ρh * r * ((1 + 1 / 2 ^ 10) * (1 - D.U)) := mul_le_mul_of_nonneg_left e2 hρh
      _ = (1 + 1 / 2 ^ 10) * (ρh * r) * (1 - D.U) := by ring
  have h2 : D.U ^ 2 ≤ 1 / 2 ^ 50 * r * (1 - D.U) := by
    have e1 : D.U ^ 2 ≤ (2 ^ 99 * r) * (2 ^ 99 / 2 ^ 256) := by
      rw [sq]; exact mul_le_mul hU hUs hU0 (mul_nonneg (by positivity) hr0)
    have e2' : (2 ^ 99 * r) * (2 ^ 99 / 2 ^ 256 : ℝ) ≤ 1 / 2 ^ 50 * r * (1 / 2) := by
      rw [show (2 ^ 99 * r) * (2 ^ 99 / 2 ^ 256 : ℝ) = r * (2 ^ 99 * (2 ^ 99 / 2 ^ 256)) by ring,
        show (1 / 2 ^ 50 * r * (1 / 2) : ℝ) = r * (1 / 2 ^ 50 * (1 / 2)) by ring]
      exact mul_le_mul_of_nonneg_left (by norm_num) hr0
    have e3 : 1 / 2 ^ 50 * r * (1 / 2) ≤ 1 / 2 ^ 50 * r * (1 - D.U) :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num) hr0)
    linarith only [e1, e2', e3]
  have hnum : D.ρ * (1 + 2 * D.F) + D.U ^ 2 ≤
      ((1 + 1 / 2 ^ 10) * (ρh * r) + 1 / 2 ^ 50 * r) * (1 - D.U) := by
    have e : ((1 + 1 / 2 ^ 10) * (ρh * r) + 1 / 2 ^ 50 * r) * (1 - D.U) =
        (1 + 1 / 2 ^ 10) * (ρh * r) * (1 - D.U) + 1 / 2 ^ 50 * r * (1 - D.U) := by ring
    rw [e]
    linarith only [h1, h2]
  have hρ' : D.ρ' ≤ (1 + 1 / 2 ^ 10) * (ρh * r) + 1 / 2 ^ 50 * r := by
    unfold OneWayData.ρ'
    rw [div_le_iff₀ (by linarith only [hd])]
    exact hnum
  have hold := T.ρold_le
  unfold tailConst
  calc T.ρold + D.ρ' ≤ ρoh * r + ((1 + 1 / 2 ^ 10) * (ρh * r) + 1 / 2 ^ 50 * r) :=
        add_le_add hold hρ'
    _ = (ρoh + (1 + 1 / 2 ^ 10) * ρh + 1 / 2 ^ 50) * r := by ring

end TailCorr

/-- **K2's field 10 from the correlation bounds**: at every tail prime, the (F7) one-way repair of
every changed record. *Hypothesis*: the correlation bounds `TailCorr` of every changed record at
every tail prime, with normalized constants `ρ̂_new ρ`, `ρ̂_old ρ`. -/
noncomputable def corrRepairs (hW : Target.Weil) (ρh ρoh : UpIdx → ℝ)
    (Tc : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (_ : upperFate (true, ⟨t, φ⟩) = .changed),
      TailCorr hW h4 (ComparisonLawPaper.tailNe hW h4) t φ (ρh (true, ⟨t, φ⟩))
        (ρoh (true, ⟨t, φ⟩))) :
    ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (ComparisonLawPaper.tailNe hW h4) :=
  fun q _ h4 t φ h => (Tc q h4 t φ h).toRepair

/-- **The constants of `corrRepairs`** (field 11 in the form "explicit constant times `r`"):
`C^ε_ρ ≤ (ρ̂_old ρ + 2ρ̂_new ρ + 1) q^{-1/2}`. -/
theorem corrRepairs_C_le (hW : Target.Weil) (ρh ρoh : UpIdx → ℝ)
    (Tc : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (_ : upperFate (true, ⟨t, φ⟩) = .changed),
      TailCorr hW h4 (ComparisonLawPaper.tailNe hW h4) t φ (ρh (true, ⟨t, φ⟩))
        (ρoh (true, ⟨t, φ⟩)))
    (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (h : upperFate (true, ⟨t, φ⟩) = .changed) (e : ChangeType) :
    (corrRepairs hW ρh ρoh Tc q h4 t φ h).C e ≤
      tailConst (ρh (true, ⟨t, φ⟩)) (ρoh (true, ⟨t, φ⟩)) * tailR q :=
  (Tc q h4 t φ h).C_le e

end Sarkozy.F7Repair
