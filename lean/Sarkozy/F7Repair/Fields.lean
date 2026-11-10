module

public import Sarkozy.F7Repair.Cap
public import Sarkozy.MainFinalF1.K3
public import Sarkozy.F7Repair.TailOneWay

@[expose] public section

/-!
# K2's fields 10 and 11 from the (F7) inputs (`lem:tail-prices`, `cert:tail-caps`)

Constructors into the exact field types of `MainFinalF1.ComparisonParts3` (and of K2's
`ComparisonParts2`, which has the same `Rp` and `hcap`):

* `TailF7Family`: the (F7) inputs of every changed record at every tail prime (`TailF7s`);
* **`TailF7Table`**: the finite numerical input of `cert:tail-caps`: normalized majorants
  `n ρ` of the (F7) inputs, an evaluation radius `r₀ ≥ 2⁻²⁵⁶`, the two gates, and the
  comparison of the normalized coefficients with the paper's caps `tailCap`;
* **`paperRp`**: field 10 (`Rp`);
* **`paperRp_hcap`**: field 11 (`hcap`), from the table and the per-prime scaling of the inputs;
* **`ComparisonParts3.ofF7`**: `ComparisonParts3` with `Rp`, `hcap` from the (F7) inputs; only
  `blkU` (field 9) is passed through.
* **`ComparisonParts3.ofCorr`**: the same with the density part of (F7) proved from H1
  (`TailOneWay.lean`): the inputs are the two correlation bounds `TailCorr` of every changed record
  at every tail prime, with normalized constants `ρ̂_new ρ`, `ρ̂_old ρ`, and the finite comparison
  `tailConst (ρ̂_new ρ) (ρ̂_old ρ) ≤ tailCap ρ` with the paper's caps.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.TailPrices Sarkozy.BlockSpecPaper Sarkozy.MainFinalF1
open Sarkozy.ComparisonLawPaper (tailNe)
open Sarkozy.AnalyticCells (f1Cell)

/-- **The (F7) inputs at every tail prime**: for every prime `q` with nonempty tail laws, the
(F7) inputs of every changed record (`TailF7s`). *Hypotheses* (analytic, per prime). -/
abbrev TailF7Family : Type := ∀ (q : ℕ) [Fact q.Prime] (hne : TailNonempty q), TailF7s hne

/-- **The normalized (F7) table** (`cert:tail-caps`). *Hypotheses* (a finite numerical table): the
normalized majorants `n ρ` of the (F7) inputs of the changed records, an evaluation radius
`r₀ ≥ 2⁻²⁵⁶`, the gates `Û r₀ < 1`, `ρ̂ r₀ < 1`, and `C_ϱ(r₀) ≤ tailCap ρ` for the 92 changed
records. -/
structure TailF7Table where
  /-- The normalized majorants. -/
  n : UpIdx → F7Norm
  /-- The evaluation radius. -/
  r₀ : ℝ
  hr₀ : (1 / 2 ^ 256 : ℝ) ≤ r₀
  gU : ∀ ρ, (n ρ).U * r₀ < 1
  gρ : ∀ ρ, (n ρ).ρ * r₀ < 1
  /-- The normalized coefficients at `r₀` are at most the paper's caps. -/
  num : ∀ ρ, upperFate ρ = .changed → (n ρ).coeff r₀ ≤ tailCap ρ

/-- **Field 10 (`Cmp.Rp`) from the (F7) inputs**: the one-way repair of every changed record at
every tail prime (`lem:tail-prices`(i),(ii), `lem:tr:repair`(a)–(d),(f), (F7)). -/
noncomputable def paperRp (hW : Target.Weil) (F : TailF7Family) :
    ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (tailNe hW h4) :=
  fun q _ h4 => (F q (tailNe hW h4)).toRepairs

/-- **Field 11 (`Cmp.hcap`) from the (F7) inputs** (`cert:tail-caps`, `lem:record:domain`(iii)):
from the normalized table and the per-prime bounds of the (F7) inputs by its majorants. -/
theorem paperRp_hcap (hW : Target.Weil) (F : TailF7Family) (T : TailF7Table)
    (hs : ∀ (q : ℕ) [Fact q.Prime] (hne : TailNonempty q), P4 ≤ q → ∀ t φ
      (h : upperFate (true, ⟨t, φ⟩) = .changed),
      (F q hne t φ h).data.Scaled (T.n (true, ⟨t, φ⟩)) (tailR q)) :
    ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (h : upperFate (true, ⟨t, φ⟩) = .changed)
      (e : ChangeType), (paperRp hW F q h4 t φ h).C e ≤ tailCap (true, ⟨t, φ⟩) * tailR q :=
  fun q _ h4 t φ h e =>
    TailF7s.hcap_of_scaled F tailCap T.n T.hr₀ T.gU T.gρ T.num hs q (tailNe hW h4) h4 t φ h e

/-- **`ComparisonParts3` with fields 10 and 11 from the (F7) inputs**; field 9 (`blkU`) is passed
through. -/
noncomputable def ComparisonParts3.ofF7 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs f1Cell}
    (blkU : ∀ b : Blk, MainFinalF1.UpperSpec hW (MainFinalF1.specF hW A b)) (F : TailF7Family)
    (T : TailF7Table)
    (hs : ∀ (q : ℕ) [Fact q.Prime] (hne : TailNonempty q), P4 ≤ q → ∀ t φ
      (h : upperFate (true, ⟨t, φ⟩) = .changed),
      (F q hne t φ h).data.Scaled (T.n (true, ⟨t, φ⟩)) (tailR q)) :
    MainFinalF1.ComparisonParts3 hW hMR hFour A where
  blkU := blkU
  Rp := paperRp hW F
  hcap := paperRp_hcap hW F T hs

/-- **`ComparisonParts3` from the correlation bounds**: field 10 is `corrRepairs` (the (F7) one-way
repairs, density part proved from H1), field 11 follows from `corrRepairs_C_le` and the finite
comparison `hnum` of the explicit constants `tailConst` with the paper's caps. *Hypotheses*: `blkU`
(field 9), the correlation bounds `Tc`, and `hnum`. -/
noncomputable def ComparisonParts3.ofCorr {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs f1Cell}
    (blkU : ∀ b : Blk, MainFinalF1.UpperSpec hW (MainFinalF1.specF hW A b)) (ρh ρoh : UpIdx → ℝ)
    (Tc : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (_ : upperFate (true, ⟨t, φ⟩) = .changed),
      TailCorr hW h4 (tailNe hW h4) t φ (ρh (true, ⟨t, φ⟩)) (ρoh (true, ⟨t, φ⟩)))
    (hnum : ∀ ρ, upperFate ρ = .changed → tailConst (ρh ρ) (ρoh ρ) ≤ tailCap ρ) :
    MainFinalF1.ComparisonParts3 hW hMR hFour A where
  blkU := blkU
  Rp := corrRepairs hW ρh ρoh Tc
  hcap q _ h4 t φ h e := (corrRepairs_C_le hW ρh ρoh Tc q h4 t φ h e).trans
    (mul_le_mul_of_nonneg_right (hnum _ h) (tailR_nonneg q))

end Sarkozy.F7Repair
