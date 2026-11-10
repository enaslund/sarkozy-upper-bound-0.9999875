module

public import Sarkozy.MiddlePrimeInputs.StepLower

/-!
# Concrete deletion orders for the middle cuts

`paper/sections/14_spectral.tex`, `eq:spec:Rcut`, `prop:spec2:mucentre`(c2): the bounds `R_cut`,
`R₊` and the pivot densities of the chain are products along a deletion order `v_1, …, v_n` of the
half, through `t_i` (`tdeg`) and `t⁰_i` (`t0deg`). B6's spectral data carry the order
`Fintype.equivFin`, which the kernel cannot evaluate. The cut law and the cut operator do not
depend on the order, so the chain may be run with any order (`withOrder`, and the parameter `o` of
`routeALower_midRplus`, `routeAUpper_midRplus`).

* `ordMid c`: the order of the half by the code `u = 0, 1, …` (computable);
* **`tdeg_ordMid`**, **`t0deg_ordMid`**, **`mcross_mid`**: by `decide`,
  `t = (2, 2, 1)`, `t⁰ = (1, 0, 0)`, `m_× = 4` for L10, and `t = (4, 4, 3, 3, 2, 2)`,
  `t⁰ = (2, 2, 1, 1, 0, 0)`, `m_× = 12` for L21. These are the evaluator's deletion histograms
  (`layer12.cut`, `hist`), as multisets.
* `prod_tdeg_ordMid`, `prod_t0deg_ordMid`, **`rcut_ordMid`**: the products of the chain along this
  order as products over these lists (`R_cut`, and the numerator and denominator of `R₊`).
-/

@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.MiddleCertificates MiddleCertificates.MidCut

theorem chamber_half : ∀ u : Fin 3, (((u : ℕ) : ZMod 6)) ∈ (Sarkozy.chamberCut 0).half := by
  decide

/-- The half element of code `u`. -/
noncomputable def halfAt10 (i : Fin MidCut.l10.data.cut.half.card) : MidCut.l10.data.cut.Half :=
  ⟨((i.val : ZMod 6), 0),
    (BlockAdapter.mem_recordHalf (Fin 1) ((i.val : ZMod 6), 0)).mpr (chamber_half ⟨i.val, i.isLt⟩)⟩

noncomputable def halfAt21 (i : Fin MidCut.l21.data.cut.half.card) : MidCut.l21.data.cut.Half :=
  ⟨((i.val : ZMod 6), 0), (BlockAdapter.mem_layerHalf (ZMod 6) ((i.val : ZMod 6), (0 : Fin 2))).mpr rfl⟩

theorem halfAt10_bij : Function.Bijective halfAt10 := by
  unfold halfAt10
  decide

theorem halfAt21_bij : Function.Bijective halfAt21 := by
  unfold halfAt21
  decide

/-- The deletion order by the code. -/
noncomputable def ordMid : (c : MidCut) → Fin c.data.cut.half.card ≃ c.data.cut.Half
  | .l10 => Equiv.ofBijective halfAt10 halfAt10_bij
  | .l21 => Equiv.ofBijective halfAt21 halfAt21_bij

/-- The deletion degrees along `ordMid`. -/
def tList : MidCut → List ℕ
  | .l10 => [2, 2, 1]
  | .l21 => [4, 4, 3, 3, 2, 2]

def t0List : MidCut → List ℕ
  | .l10 => [1, 0, 0]
  | .l21 => [2, 2, 1, 1, 0, 0]

/-- **`t_i` along `ordMid`**. -/
theorem tdeg_ordMid (c : MidCut) :
    ∀ i, (withOrder c (ordMid c)).tdeg i = (tList c).getD i.val 0 := by
  cases c
  all_goals
    unfold Cuts.SpecData.tdeg withOrder ordMid tList
    decide

/-- **`t⁰_i` along `ordMid`**. -/
theorem t0deg_ordMid (c : MidCut) :
    ∀ i, (withOrder c (ordMid c)).t0deg i = (t0List c).getD i.val 0 := by
  cases c
  all_goals
    unfold Cuts.SpecData.t0deg withOrder ordMid t0List
    decide

/-- `m_× = |E_×|`: `4` (L10), `12` (L21). -/
def mcrossVal : MidCut → ℕ
  | .l10 => 4
  | .l21 => 12

theorem mcross_mid (c : MidCut) (o : Fin c.data.cut.half.card ≃ c.data.cut.Half) :
    (withOrder c o).mcross = mcrossVal c := by
  change c.data.mcross = mcrossVal c
  cases c <;> decide

/-- The size of the half: `half.card = |U⁺|`. -/
theorem half_card (c : MidCut) : c.data.cut.half.card = (tList c).length := by
  cases c <;> rfl

/-- A product along the order by the code, as a product over the list of degrees. -/
theorem prod_tdeg_ordMid (c : MidCut) {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i, f ((withOrder c (ordMid c)).tdeg i) = ((tList c).map f).prod := by
  simp only [tdeg_ordMid]
  rw [Fin.prod_univ_eq_prod_range (fun k => f ((tList c).getD k 0)), half_card]
  cases c <;> simp [tList, Finset.prod_range_succ] <;> ac_rfl

theorem prod_t0deg_ordMid (c : MidCut) {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i, f ((withOrder c (ordMid c)).t0deg i) = ((t0List c).map f).prod := by
  simp only [t0deg_ordMid]
  rw [Fin.prod_univ_eq_prod_range (fun k => f ((t0List c).getD k 0)), half_card]
  cases c <;> simp [tList, t0List, Finset.prod_range_succ] <;> ac_rfl

/-- **`R_cut` along the order by the code** (`eq:spec:Rcut`), explicitly:
`∏_{t ∈ (2,2,1)}` (L10) or `∏_{t ∈ (4,4,3,3,2,2)}` (L21) of `(1 + e_t)/(1 - e_t)`. -/
theorem rcut_ordMid (c : MidCut) (e : ℕ → ℝ) :
    (withOrder c (ordMid c)).Rcut e = ((tList c).map (fun t => (1 + e t) / (1 - e t))).prod :=
  prod_tdeg_ordMid c (fun t => (1 + e t) / (1 - e t))

end Sarkozy.MiddlePrimeInputs
