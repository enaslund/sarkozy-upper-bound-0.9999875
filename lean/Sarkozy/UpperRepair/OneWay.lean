module

public import Sarkozy.UpperRepair.Replacement
public import Sarkozy.F7Repair.Upper

@[expose] public section

/-!
# The one-way repairs of an upper block as replacing laws ((F7), `prop:record:upper`(i))

`paper/sections/26_upper_comparison.tex`, `prop:record:upper`(i), "Records repaired", and (F7)
(`it:record:upper-F7`): the `84` changed records that are neither LE (`LR`) nor dense EL (`RL`) are
replaced by their one-way repairs `π^rep = (1 + f(x) + g(y))π^new`, whose change has symmetric part
at most `C^s = ρ_old + ρ'` and skew part at most `C^a = ρ'` (the old record is symmetric, so the
skew part of the change is that of `𝒞_{π^rep}`).

FR's `F7Record` (`Sarkozy/F7Repair/TwoLayer.lean`) at W8's block laws gives the repaired law and its
change bound `C = ρ_old + ρ'` for both parts (`F7Record.upper_bracket`). Here:

* `recOld_pair_symm`: the pair form of the old record is symmetric in its two layers (the layer
  swap is an automorphism of `G_{φ₀φ₁,2}` at every prime);
* **`f7_skew_le`**: the skew part of `𝒞_{π^rep} − 𝒞_{π^old}` relative to `μ^old` is at most
  `ρ'`, not only `ρ_old + ρ'`. This is the paper's `C^a = ρ'/r`, which the skew ledger
  (`PaperLedgers`, `skew_ledger`) needs;
* `OneWayInput pr hne t φ`: an `F7Record` of the record together with the acceptance of `𝓔₆` on
  the support of `π^new` (for `π^new = λ_𝔅(G^new)` this is `newBlock_accepts` in
  `NewGraphBlock.lean`);
* **`OneWayInput.toRepl`**: the `ReplRecord` of the record, `C^s = ρ_old + ρ'`, `C^a = ρ'`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.Structured Sarkozy.Recentering Sarkozy.F7Repair

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The pair form of an old upper record is symmetric in its layers.** -/
theorem recOld_pair_symm (hne : UpperNonempty pr) (t : PType × PType)
    (φ' ψ' : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) :
    (recOld pr hne t).expect (fun y => φ' (layerOf y 0) * ψ' (layerOf y 1)) =
      (recOld pr hne t).expect (fun y => ψ' (layerOf y 0) * φ' (layerOf y 1)) := by
  have h := blockGraphLaw_expect_auto pr (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _)
    (upLayerSwap _ _) (upLayerSwap_automorphism _ _)
    (fun y => ψ' (layerOf y 0) * φ' (layerOf y 1))
  have e0 : ∀ z : t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr,
      layerOf (z ∘ upLayerSwap t.1.field.Obj t.2.field.Obj) 0 = layerOf z 1 := by
    intro z
    funext o
    simp only [layerOf, Function.comp_apply, upLayerSwap, Equiv.prodCongr_apply,
      Equiv.coe_refl, Prod.map, id_eq, Equiv.swap_apply_left]
  have e1 : ∀ z : t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr,
      layerOf (z ∘ upLayerSwap t.1.field.Obj t.2.field.Obj) 1 = layerOf z 0 := by
    intro z
    funext o
    simp only [layerOf, Function.comp_apply, upLayerSwap, Equiv.prodCongr_apply,
      Equiv.coe_refl, Prod.map, id_eq, Equiv.swap_apply_right]
  simp only [e0, e1] at h
  exact ((recOld pr hne t).expect_congr fun y => mul_comm _ _).trans h

/-- **The skew part of a one-way repair's change is at most `ρ'`** ((F7): `C^a = ρ'/r`). The old
record is symmetric, so the skew part of `𝒞_{π^rep} − 𝒞_{π^old}` is that of `𝒞_{π^rep}`; the
repair has both half marginals `μ^old` and centred norm at most `ρ'` relative to `μ^old`, so the
difference of `π^rep` and its layer swap is at most `2ρ'` (`coupling_change`). -/
theorem f7_skew_le (hne : UpperNonempty pr) (t : PType × PType)
    (R : F7Record (recOld pr hne t) (recHalf pr hne t))
    (φ' ψ' : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) :
    |(recChangeForm pr hne t R.lam φ' ψ' - recChangeForm pr hne t R.lam ψ' φ') / 2| ≤
      R.D.ρ' * mnrm (recHalf pr hne t) (recU pr hne t) φ' *
        mnrm (recHalf pr hne t) (recU pr hne t) ψ' := by
  have hsO := upper_layersSupported pr hne t.1.field t.2.field
  have hN : ∀ a b : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ,
      kform (recHalf pr hne t) (recHalf pr hne t) (pairDensity R.lam (recHalf pr hne t)) a b =
        R.lam.expect (fun y => a (layerOf y 0) * b (layerOf y 1)) :=
    fun a b => (pair_density_eq R.lam (recHalf pr hne t) R.supp a b).symm
  have hO : ∀ a b : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ,
      kform (recHalf pr hne t) (recHalf pr hne t) (pairDensity (recOld pr hne t)
        (recHalf pr hne t)) a b =
        (recOld pr hne t).expect (fun y => a (layerOf y 0) * b (layerOf y 1)) :=
    fun a b => (pair_density_eq (recOld pr hne t) (recHalf pr hne t) hsO a b).symm
  have hdiff : recChangeForm pr hne t R.lam φ' ψ' - recChangeForm pr hne t R.lam ψ' φ' =
      R.lam.expect (fun y => φ' (layerOf y 0) * ψ' (layerOf y 1)) -
        R.lam.expect (fun y => φ' (layerOf y 1) * ψ' (layerOf y 0)) := by
    unfold recChangeForm centredForm
    rw [hN, hN, hO, hO, recOld_pair_symm pr hne t φ' ψ']
    have hc : R.lam.expect (fun y => ψ' (layerOf y 0) * φ' (layerOf y 1)) =
        R.lam.expect (fun y => φ' (layerOf y 1) * ψ' (layerOf y 0)) :=
      R.lam.expect_congr fun y => mul_comm _ _
    rw [hc]
    ring
  have hQs : ∀ h k : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ,
      (oldHalf (recOld pr hne t)).expect h = 0 → (oldHalf (recOld pr hne t)).expect k = 0 →
      |R.lam.expect (fun y => h (lay1 y) * k (lay0 y))| ≤
        R.D.ρ' * nrm (oldHalf (recOld pr hne t)) h * nrm (oldHalf (recOld pr hne t)) k := by
    intro h k hh hk
    have hc := R.centred k h hk hh
    have e : R.lam.expect (fun y => h (lay1 y) * k (lay0 y)) =
        R.lam.expect (fun y => k (lay0 y) * h (lay1 y)) :=
      R.lam.expect_congr fun y => mul_comm _ _
    rw [e]
    linarith [show R.D.ρ' * nrm (oldHalf (recOld pr hne t)) k * nrm (oldHalf (recOld pr hne t)) h =
      R.D.ρ' * nrm (oldHalf (recOld pr hne t)) h * nrm (oldHalf (recOld pr hne t)) k by ring]
  have hcc := coupling_change R.lam R.lam lay0 lay1 lay1 lay0 R.half0 R.half1 R.half1 R.half0
    R.D.ρ'_nonneg R.D.ρ'_nonneg R.centred hQs φ' ψ'
  rw [hdiff, F7Repair.F7Record.mnrm_eq hsO, F7Repair.F7Record.mnrm_eq hsO, abs_div, abs_two,
    div_le_iff₀ (by norm_num)]
  have e2 : (R.D.ρ' + R.D.ρ') * nrm (oldHalf (recOld pr hne t)) φ' *
      nrm (oldHalf (recOld pr hne t)) ψ' =
      R.D.ρ' * nrm (oldHalf (recOld pr hne t)) φ' * nrm (oldHalf (recOld pr hne t)) ψ' * 2 := by
    ring
  rw [← e2]
  exact hcc

/-- The symmetric part of a one-way repair's change is at most `C = ρ_old + ρ'` (FR's
`change_bound`). -/
theorem f7_sym_le (hne : UpperNonempty pr) (t : PType × PType)
    (R : F7Record (recOld pr hne t) (recHalf pr hne t))
    (φ' ψ' : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) :
    |(recChangeForm pr hne t R.lam φ' ψ' + recChangeForm pr hne t R.lam ψ' φ') / 2| ≤
      R.C * mnrm (recHalf pr hne t) (recU pr hne t) φ' *
        mnrm (recHalf pr hne t) (recU pr hne t) ψ' := by
  have hB : ∀ a b, |recChangeForm pr hne t R.lam a b| ≤
      R.C * mnrm (recHalf pr hne t) (recU pr hne t) a *
        mnrm (recHalf pr hne t) (recU pr hne t) b := fun a b => by
    unfold recChangeForm
    exact R.change_bound (upper_layersSupported pr hne _ _) (recOld_symm pr hne t) a b
  exact (TailPrices.half_bounds (hB φ' ψ') (hB ψ' φ')).1

/-- **The (F7) inputs of a one-way repaired upper record** (`it:record:upper-F7`): FR's
`F7Record` at the block laws, and the acceptance of `𝓔₆` on the support of `π^new` at every prime
of the block. *Hypotheses*: the analytic inputs of (F7) at the block (`U`, `ρ_new`, `K_∞`, the gate,
`ρ_old`), which the paper evaluates at the band start (`lem:record:domain`). -/
structure OneWayInput (hne : UpperNonempty pr) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) where
  /-- The (F7) record: `π^new`, the one-way data, `ρ_old`. -/
  R : F7Record (recOld pr hne t) (recHalf pr hne t)
  /-- `π^new` accepts `𝓔₆` at every prime of the block. -/
  accepts : ∀ y, R.lamN.weight y ≠ 0 → ∀ (j : Chamber) (i : ι),
    quadraticChar (ZMod (pr i))
      (y (recEm t φ (queryTarget j)) i - y (recEm t φ (querySource j)) i) = 1

namespace OneWayInput

variable {pr} {hne : UpperNonempty pr} {t : PType × PType} {φ : t.1.Pat × t.2.Pat}

/-- **The replacing law of a one-way repaired record** (`prop:record:upper`(i), "Records
repaired"): `π^rep`, with `C^s = ρ_old + ρ'` and `C^a = ρ'`. -/
noncomputable def toRepl (I : OneWayInput pr hne t φ) : ReplRecord pr hne t φ where
  lamN := I.R.lam
  supp := I.R.supp
  half0 g := (I.R.half0 g).trans (oldHalf_expect _ g)
  half1 g := (I.R.half1 g).trans (oldHalf_expect _ g)
  accepts y hy j i := I.accepts y (I.R.support hy) j i
  Cs := I.R.C
  Ca := I.R.D.ρ'
  Cs_nonneg := I.R.C_nonneg
  Ca_nonneg := I.R.D.ρ'_nonneg
  sym := f7_sym_le pr hne t I.R
  skew := f7_skew_le pr hne t I.R

theorem toRepl_Cs (I : OneWayInput pr hne t φ) : I.toRepl.Cs = I.R.ρold + I.R.D.ρ' := rfl

theorem toRepl_Ca (I : OneWayInput pr hne t φ) : I.toRepl.Ca = I.R.D.ρ' := rfl

end OneWayInput

end Sarkozy.UpperRepair
