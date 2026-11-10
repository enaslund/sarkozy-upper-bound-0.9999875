module

public import Sarkozy.NumericalFields.Main

@[expose] public section

/-!
# Sanity checks of E2's reductions

* `KappaNonneg` is satisfiable (`kappaNonneg_zero`, `kappaNonneg_one`); with it the signs of
  `K_d(i)` hold on all 33 pieces (`midK_signs_one`).
* The new structures add no hypothesis to K2's, except the sign condition `hκ` on the data `κ`:
  `MainFinalObligationsE2.ofMF2` maps K2's obligations (with `hκ`) to E2's, and
  `MainFinalObligationsE2.toMF2` maps back (`Main.lean`). The round trips keep the refinement
  `MR` and the data of `hSA` other than the band charges (`roundtrip_MR`, `roundtrip_κ`,
  `roundtrip_U`).
-/

namespace Sarkozy.NumericalFields

open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.PaperNumbers (paperCell)

/-- The zero constants satisfy the side condition. -/
theorem kappaNonneg_zero : KappaNonneg ⟨0, 0, 0, 0, 0⟩ :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- The unit constants satisfy the side condition. -/
theorem kappaNonneg_one : KappaNonneg ⟨1, 1, 1, 1, 1⟩ :=
  ⟨zero_le_one, zero_le_one, zero_le_one, zero_le_one, zero_le_one⟩

/-- The signs at the unit constants (a toy instance of `midK_signs`). -/
theorem midK_signs_one :
    ∀ i, 0 ≤ midK2 (fun _ => ⟨1, 1, 1, 1, 1⟩) i ∧ 0 ≤ midK3 (fun _ => ⟨1, 1, 1, 1, 1⟩) i ∧
      0 ≤ midK4 i ∧ 0 ≤ midK5 i :=
  midK_signs _ fun _ => kappaNonneg_one

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- The round trip through K2's obligations keeps the middle refinement. -/
theorem roundtrip_MR (O : MainFinalObligations2 hW hMR hFour)
    (hκ : ∀ i, KappaNonneg (O.SA.κ i)) :
    ((MainFinalObligationsE2.ofMF2 O hκ).toMF2).Dv.Env.MR = O.Dv.Env.MR := rfl

/-- The round trip keeps the constants `κ`. -/
theorem roundtrip_κ (O : MainFinalObligations2 hW hMR hFour)
    (hκ : ∀ i, KappaNonneg (O.SA.κ i)) :
    ((MainFinalObligationsE2.ofMF2 O hκ).toMF2).SA.κ = O.SA.κ := rfl

/-- The round trip replaces the band charges by `min(US, UA)` for both prices. -/
theorem roundtrip_U (O : MainFinalObligations2 hW hMR hFour)
    (hκ : ∀ i, KappaNonneg (O.SA.κ i)) (β : Fin 310) (d : ℕ) :
    ((MainFinalObligationsE2.ofMF2 O hκ).toMF2).SA.US β d = min (O.SA.US β d) (O.SA.UA β d) ∧
      ((MainFinalObligationsE2.ofMF2 O hκ).toMF2).SA.UA β d =
        min (O.SA.US β d) (O.SA.UA β d) := ⟨rfl, rfl⟩

end Sarkozy.NumericalFields
