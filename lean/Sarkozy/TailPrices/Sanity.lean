module

public import Sarkozy.TailPrices.RepairMain

@[expose] public section




open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.PartV Sarkozy.PartVRecords

variable {p : ℕ} [Fact p.Prime]

/-- **Non-vacuity of `TailRestData`**: `ρ_p = h_p π_{LL,2}`, of mass `h_p`. -/
noncomputable def TailRestData.rootOnly (hne : TailNonempty p) : TailRestData p hne where
  h' := tailH p
  ρt z := tailH p * (tailRootComponent p hne).weight z
  ρt_nonneg z := mul_nonneg (tailH_pos p).le ((tailRootComponent p hne).nonneg z)
  ρt_mass := by rw [← mul_sum, (tailRootComponent p hne).total, mul_one]
  h'_pos := tailH_pos p
  h'_le := le_rfl
  ρt_inv α β hα z := by
    change tailH p * _ = tailH p * _
    rw [root_invariant hne α β hα z]
  ρt_acc z hz j := root_accepts hne j z (fun h0 => hz (by rw [h0, mul_zero]))

/-- The law of `rootOnly` is the root. -/
theorem rootOnly_law (hne : TailNonempty p) (z : Slot → ZMod p) :
    (TailRestData.rootOnly hne).law.weight z = (tailRootComponent p hne).weight z := by
  change ((tailRootComponent p hne).weight z + tailH p * (tailRootComponent p hne).weight z) /
    (1 + tailH p) = _
  have := tailH_pos p
  field_simp

/-- `Π^{rep}(r) ≥ 0` and `Π^{del}(r) ≥ 0` for `r ≥ 0`. -/
theorem price_fields_nonvacuous {r : ℝ} (hr : 0 ≤ r) : 0 ≤ piRep r ∧ 0 ≤ piRep r + piDel r := by
  have h1 : 0 ≤ piRep r := by
    unfold piRep cRep3 cRep4
    positivity
  have h2 : 0 ≤ piDel r := by
    unfold piDel cDel3 cDel4 cDel5 cDel6 cDel7
    positivity
  exact ⟨h1, add_nonneg h1 h2⟩

theorem tailSt_pos : 0 < tailSt ∧ 0 < tailAt := by
  unfold tailSt tailAt kS kA
  constructor <;> positivity

/-- The root law accepts `𝓔₆` (a candidate `new ρ` for the field `new_accepts`). -/
theorem root_new_accepts (hne : TailNonempty p) (z : Slot → ZMod p)
    (hz : (tailRootComponent p hne).weight z ≠ 0) (j : Chamber) :
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 :=
  root_accepts hne j z hz

/-- The root law is square-affine invariant (a candidate `new ρ` for the field `new_inv`). -/
theorem root_new_inv (hne : TailNonempty p) : AffineInvariant p (tailRootComponent p hne).weight :=
  root_invariant hne

/-- Changed records exist (W8's count: 92). -/
theorem changed_exist : ∃ ρ : UpIdx, UpperComparison.upperFate ρ = .changed :=
  UpperComparison.exists_changed

theorem delW_3_lt : delW 3 < 81606792 / 25 := by
  rw [delW_3]
  norm_num

/-- The old law of a two-layer record satisfies the support, invariance and norm-bound fields of
`TailRepair` with constants zero. -/
theorem old_repair_fields (hne : TailNonempty p) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    UpperComparison.LayersSupported (tailOld p hne t) (tailHalf p hne t.1.field t.2.field) ∧
      AffineInvariant p (emit (tailOld p hne t) (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight ∧
      ∀ φ' ψ', |(tailChangeForm p hne t (tailOld p hne t) φ' ψ' +
        tailChangeForm p hne t (tailOld p hne t) ψ' φ') / 2| ≤
          0 * Structured.mnrm (tailHalf p hne t.1.field t.2.field) (tailU p hne t) φ' *
            Structured.mnrm (tailHalf p hne t.1.field t.2.field) (tailU p hne t) ψ' := by
  refine ⟨tail_layersSupported p hne _ _, tail_component_invariant p hne (true, ⟨t, φ⟩),
    fun φ' ψ' => ?_⟩
  unfold tailChangeForm
  simp

end Sarkozy.TailPrices
