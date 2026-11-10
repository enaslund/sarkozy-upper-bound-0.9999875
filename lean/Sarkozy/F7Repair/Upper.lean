module

public import Sarkozy.F7Repair.TwoLayer
public import Sarkozy.ComparisonLawPaper.Upper
public import Sarkozy.UpperComparison.Symmetry
public import Sarkozy.TailPrices.RepairBound

@[expose] public section

/-!
# The one-way repairs at the upper blocks (`prop:record:upper`(i), (F7); K2's field 9, partly)

`paper/sections/26_upper_comparison.tex`, `prop:record:upper`(i), "Records repaired": the `84`
one-way repairs of a band. The generic `F7Record` (`TwoLayer.lean`) is instantiated at the block
laws of W8 (`recOld`, `recHalf`, labels in `BlockLabel pr`):

* `recOld_symm`: the two layers of the old block record have one law (the layer swap is an
  automorphism of `G_{φ₀φ₁,2}` at every prime);
* **`F7Record.upper_bracket`**: for an `F7Record` of the upper record `(t, φ)`, the bracket at `ι`
  of the symmetric and of the skew part of `Π_rep − Π_{𝔱,φ}` with constant `C = ρ_old + ρ'` and
  the envelope of the old record (W8's `oldRecord_sym_bracket`, `oldRecord_skew_bracket`). This is
  the `bracket` field of B2's `UpperAtomInputs` for a one-way repaired record, up to the factor
  `P_μ(r)⁻¹ c_ρ` (`bracket_smul`, as in T2's `TailRepairs.toRecords`).

Not done here: the `6` LE mixtures and the `2` dense EL laws of a band (`prop:le-mixture`,
`prop:dense-comparison`), the acceptance and uniform marginals of the emitted block repairs
(`new_accepts`, `new_uniform`), and the analytic inputs of the `F7Record`s at the band primes.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison Sarkozy.Recentering Sarkozy.Structured
open Sarkozy.ComparisonLawPaper (upperEnv)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The two layers of an old upper record have one law.** -/
theorem recOld_symm (hne : UpperNonempty pr) (t : PType × PType)
    (φ' : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) :
    (recOld pr hne t).expect (fun y => φ' (lay1 y)) =
      (recOld pr hne t).expect (fun y => φ' (lay0 y)) := by
  have h := blockGraphLaw_expect_auto pr (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _)
    (upLayerSwap _ _) (upLayerSwap_automorphism _ _) (fun y => φ' (lay0 y))
  have e : ∀ z : t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr,
      lay0 (z ∘ upLayerSwap t.1.field.Obj t.2.field.Obj) = lay1 z := by
    intro z
    funext o
    simp only [lay0, lay1, layerOf, Function.comp_apply, upLayerSwap, Equiv.prodCongr_apply,
      Equiv.coe_refl, Prod.map, id_eq, Equiv.swap_apply_left]
  simp only [e] at h
  exact h

/-- **The bracket of a one-way repaired upper record** (`prop:record:upper`(i), "Records repaired";
(F7), `lem:tr:repair`(f)): for an `F7Record` of the upper record `(t, φ)`, both parts of
`Π_rep − Π_{𝔱,φ}` at `ι` lie in the bracket of `C · Diag(m_+(Π_{𝔱,φ}))`, `C = ρ_old + ρ'`. -/
theorem F7Record.upper_bracket (hne : UpperNonempty pr) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (R : F7Record (recOld pr hne t) (recHalf pr hne t))
    (e : ChangeType) :
    reservedCut.Bracket (R.C • upperEnv pr hne (true, ⟨t, φ⟩))
      (changePart e (signedIntegral (emit R.lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight -
        signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight))
      (R.C • upperEnv pr hne (true, ⟨t, φ⟩)) := by
  have hB : ∀ φ' ψ', |recChangeForm pr hne t R.lam φ' ψ'| ≤
      R.C * mnrm (recHalf pr hne t) (recU pr hne t) φ' *
        mnrm (recHalf pr hne t) (recU pr hne t) ψ' := fun φ' ψ' => by
    unfold recChangeForm
    exact R.change_bound (upper_layersSupported pr hne _ _) (recOld_symm pr hne t) φ' ψ'
  cases e
  · exact oldRecord_sym_bracket pr hne t φ R.lam R.supp R.C_nonneg fun φ' ψ' =>
      (TailPrices.half_bounds (hB φ' ψ') (hB ψ' φ')).1
  · exact oldRecord_skew_bracket pr hne t φ R.lam R.supp R.C_nonneg fun φ' ψ' =>
      (TailPrices.half_bounds (hB φ' ψ') (hB ψ' φ')).2

end Sarkozy.F7Repair
