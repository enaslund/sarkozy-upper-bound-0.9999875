module

public import Sarkozy.BlockAdapter.UpperMain

@[expose] public section

/-!
# The coordinate exchange of the upper block laws (`lem:upper-reference-rp`(ii))

`paper/sections/25_upper_reference.tex`, `subsec:upper-reference-rp`; `lem:upper-geometry`.

The two-layer graph `G_{φ₀φ₁}` is carried to `G_{φ₁φ₀}` by the exchange of the two coordinates
(`coordSwap_edges`: the edge rule `c₀.rel ∧ c₁.rel ∧ (c₀.fwd ∨ c₁.fwd)` is symmetric). Hence the
upper block laws satisfy `λ_{φ₁φ₀} = λ_{φ₀φ₁} ∘ swap` (`lam2_upperBlock_swap`), the coordinate-`1`
row laws at `φ'` are the coordinate-`0` row laws at `φ'` (`rows1_map_lam2`), and the two row data
coincide: **`rowD1_eq_rowD0`**. Since `ValidInputs` uses the same inputs `(d, f, h, M)` of the
field type for both coordinates, the coordinate-`1` fields `root21`, `root11`, `rows21`, `rows11`
follow from the coordinate-`0` ones.

* `UpperBandRows k`: the fields `rows20`, `rows10` and `caps` of `ValidInputs` on band `k` (3 of
  9). *Hypothesis* (spectral; `lem:upper-reference-rp`(ii), (V2), (V3));
* `upperBandRest_of_rows`: B6's `UpperBandRest k` from `UpperBandRows k` and `UpperRootCaps k`;
* `main_target_paper_joint_B6_swap`: the main statement with this reduction (`Final.lean`
  reduces further: `main_target_paper_joint_B6`).
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.PartVLaws.FieldGraphs Sarkozy.BlockSpecPaper

/-- The exchange of the two coordinates. -/
def coordSwap (f0 f1 : FieldTy) (Λ : Type) : f1.Obj × f0.Obj × Λ ≃ f0.Obj × f1.Obj × Λ where
  toFun w := (w.2.1, w.1, w.2.2)
  invFun w := (w.2.1, w.1, w.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The coordinate exchange carries `G_{φ₁φ₀}` to `G_{φ₀φ₁}`.** -/
theorem coordSwap_edges (f0 f1 : FieldTy) (Λ : Type) [Fintype Λ] (u w : f1.Obj × f0.Obj × Λ) :
    (u, w) ∈ (graph f1 f0 Λ).E ↔
      (coordSwap f0 f1 Λ u, coordSwap f0 f1 Λ w) ∈ (graph f0 f1 Λ).E := by
  rw [mem_graph, mem_graph]
  simp only [twoLayerEdge, coordSwap, Equiv.coe_fn_mk, Bool.and_eq_true, Bool.or_eq_true]
  tauto

theorem datumOfGam_congr {𝔛 : Type} [Fintype 𝔛] [DecidableEq 𝔛]
    {A A' B B' : FiniteLaw (Fin 3 → 𝔛)} {C C' : FiniteLaw (ZMod 6 → 𝔛)} (hA : A = A')
    (hB : B = B') (hC : C = C')
    (h1 : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), A.weight (ω ∘ σ) = A.weight ω)
    (h2 : GamSupported A B) (h3 : ∀ (k : Fin 6) (Ψ : ZMod 6 → 𝔛), C.weight (Ψ ∘ g6 k) = C.weight Ψ)
    (h1' : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), A'.weight (ω ∘ σ) = A'.weight ω)
    (h2' : GamSupported A' B')
    (h3' : ∀ (k : Fin 6) (Ψ : ZMod 6 → 𝔛), C'.weight (Ψ ∘ g6 k) = C'.weight Ψ) :
    datumOfGam A B C h1 h2 h3 = datumOfGam A' B' C' h1' h2' h3' := by
  subst hA hB hC
  rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hne : UpperNonempty pr)

theorem lam2_upperBlock_swap (f0 f1 : FieldTy) :
    lam2 (upperBlockFieldLaws pr hne) f1 f0 =
      (lam2 (upperBlockFieldLaws pr hne) f0 f1).map (fun y => y ∘ coordSwap f0 f1 (ZMod 2)) := by
  rw [lam2_upperBlock, lam2_upperBlock]
  exact (blockGraphLaw_map_iso pr _ _ (coordSwap f0 f1 (ZMod 2))
    (coordSwap_edges f0 f1 (ZMod 2)) _ _).symm

theorem lam1_upperBlock_swap (f0 f1 : FieldTy) :
    lam1 (upperBlockFieldLaws pr hne) f1 f0 =
      (lam1 (upperBlockFieldLaws pr hne) f0 f1).map (fun y => y ∘ coordSwap f0 f1 Unit) := by
  rw [lam1_upperBlock, lam1_upperBlock]
  exact (blockGraphLaw_map_iso pr _ _ (coordSwap f0 f1 Unit) (coordSwap_edges f0 f1 Unit) _ _).symm

/-- The coordinate-`1` row laws at `φ'` are the coordinate-`0` row laws at `φ'` (two layers). -/
theorem rows1_map_lam2 (f' t : FieldTy) :
    (lam2 (upperBlockFieldLaws pr hne) f' t).map rows1 =
      (lam2 (upperBlockFieldLaws pr hne) t f').map rows0 := by
  rw [lam2_upperBlock_swap pr hne t f', map_map']
  rfl

/-- The same for one layer. -/
theorem rows1_map_lam1 (f' t : FieldTy) :
    (lam1 (upperBlockFieldLaws pr hne) f' t).map rows1 =
      (lam1 (upperBlockFieldLaws pr hne) t f').map rows0 := by
  rw [lam1_upperBlock_swap pr hne t f', map_map']
  rfl

/-- **The coordinate-`1` row datum is the coordinate-`0` row datum** (two layers). -/
theorem rowD1_eq_rowD0_two (f' : FieldTy) (h1 : RowHyp1 (lam2 (upperBlockFieldLaws pr hne)) f')
    (h0 : RowHyp0 (lam2 (upperBlockFieldLaws pr hne)) f') :
    rowD1 (lam2 (upperBlockFieldLaws pr hne)) f' h1 =
      rowD0 (lam2 (upperBlockFieldLaws pr hne)) f' h0 := by
  unfold rowD1 rowD0
  exact datumOfGam_congr (rows1_map_lam2 pr hne f' .E) (rows1_map_lam2 pr hne f' .F)
    (rows1_map_lam2 pr hne f' .L) _ _ _ _ _ _

/-- The same for one layer. -/
theorem rowD1_eq_rowD0_one (f' : FieldTy) (h1 : RowHyp1 (lam1 (upperBlockFieldLaws pr hne)) f')
    (h0 : RowHyp0 (lam1 (upperBlockFieldLaws pr hne)) f') :
    rowD1 (lam1 (upperBlockFieldLaws pr hne)) f' h1 =
      rowD0 (lam1 (upperBlockFieldLaws pr hne)) f' h0 := by
  unfold rowD1 rowD0
  exact datumOfGam_congr (rows1_map_lam1 pr hne f' .E) (rows1_map_lam1 pr hne f' .F)
    (rows1_map_lam1 pr hne f' .L) _ _ _ _ _ _

/-- **`lem:upper-reference-rp`(ii) on band `k`, the coordinate-`0` rows and the layer caps**: the
fields `rows20`, `rows10`, `caps` of `ValidInputs`. *Hypothesis* (spectral). 3 fields. -/
def UpperBandRows (k : Fin 310) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, (bandOf k).1 ≤ pr j ∧ pr j < (bandOf k).2) →
    (∑ j, Real.log (pr j) ≤ (UpperRecords.CompletionData.record k).budget) →
    (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ (hne : UpperNonempty pr) (hW' : ∀ i, WeilBound (ZMod (pr i)))
      (hp' : ∀ i, (2 : ℝ) ^ 20 ≤ pr i),
      (∀ f', ValidRows (rowD0 (lam2 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).two0 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandOrd k f').f (UpperRecords.bandOrd k f').h
          (UpperRecords.bandOrd k f').M) ∧
      (∀ f', ValidRows (rowD0 (lam1 (upperBlockFieldLaws pr hne)) f'
        ((block_upperDatumHyp pr hW' hp' hne).one0 f')) ((b : ℝ) ^ (-(1 / 2 : ℝ)))
          (UpperRecords.bandRes k f').f (UpperRecords.bandRes k f').h
          (UpperRecords.bandRes k f').M) ∧
      UpperLayerCaps (upperBlockFieldLaws pr hne) (UpperRecords.bandCap k)
        ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- **B6's `UpperBandRest k` from the coordinate-`0` rows, the caps and the root certificates**
(coordinate exchange). -/
theorem upperBandRest_of_rows {k : Fin 310} (hR : UpperBandRows k) (hC : UpperRootCaps k) :
    UpperBandRest k := by
  intro ι _ _ pr _ b hinj h3 hband hbud hb hb' hne hW' hp'
  obtain ⟨w20, w10, caps⟩ := hR ι pr b hinj h3 hband hbud hb hb' hne hW' hp'
  set H := block_upperDatumHyp pr hW' hp' hne
  refine ⟨fun f' => ?_, fun f' => ?_, w20, fun f' => ?_, w10, fun f' => ?_, caps⟩
  · rw [rowD1_eq_rowD0_two pr hne f' (H.two1 f') (H.two0 f')]
    exact upper_root20_of_cert pr b f' (hC f').1 h3 hband hbud hb hb' hne _
  · rw [rowD1_eq_rowD0_one pr hne f' (H.one1 f') (H.one0 f')]
    exact upper_root10_of_cert pr b f' (hC f').2 h3 hband hbud hb hb' hne _
  · rw [rowD1_eq_rowD0_two pr hne f' (H.two1 f') (H.two0 f')]
    exact w20 f'
  · rw [rowD1_eq_rowD0_one pr hne f' (H.one1 f') (H.one0 f')]
    exact w10 f'

/-- **The main statement at `ε = a_T/71`, joint form, with the block adapter and the coordinate
exchange** (`thm:main` at `ε = a_T/71`, `cor:joint-closing`, `def:construction`(b) in the ALLp
configuration, `lem:front12:reference`(i),(ii), `lem:upper-reference-rp`(ii)).

Remaining, besides the literature hypotheses:
* the data `cell` and `PaperBudget cell` (combinatorial);
* upper bands (310): `hUR` (`UpperBandRows`: `rows20`, `rows10`, `caps`, 3 of the 9 fields of
  `ValidInputs`) and `hUC` (`UpperRootCaps`: per-prime certificates of the chamber cuts with
  per-band constants, `cert:upper-root-caps`);
* middle pieces: `hMB`, `hIB` (block level: the rows; F21 at `k_D`; on `2³⁶`, `2⁴⁰` the L20
  envelope and L21 cap of the individual root) and the per-prime certificates `h20` (L20, 31
  uniform pieces), `h10` (L10, 33 pieces), `h21` (L21, 31 uniform pieces); E21 is proved;
* B1's 11 joint obligations `O`. -/
theorem main_target_paper_joint_B6_swap (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR) (cell : ℕ → ℕ)
    (hbud : PaperBudget cell) (hUR : ∀ k, UpperBandRows k) (hUC : ∀ k, UpperRootCaps k)
    (hMB : ∀ i, allpIndividual i = none → MiddleUniformBlockInputs i)
    (hIB : ∀ i u, allpIndividual i = some u → MiddleIndividualBlockInputs i u)
    (h20 : ∀ i, allpIndividual i = none → MiddleRootCaps (Fin 2) 0 i)
    (h10 : ∀ i, MiddleRootCaps (Fin 1) 1 i)
    (h21 : ∀ i, allpIndividual i = none → MiddleL21Caps i)
    (O : B1JointFinalObligations cell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_B6 hbud
        (fun k => upperBandLemma_of_rest (upperBandRest_of_rows (hUR k) (hUC k)) (hUC k)) hMB hIB
        h20 h10 h21 middleE21Caps_proved)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_B1 hWeil hMovingRoot hFourCycle hThetaSmallRR cell _ O

end Sarkozy.BlockAdapter
