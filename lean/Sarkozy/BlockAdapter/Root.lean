module

public import Sarkozy.PartV.ChamberCut
public import Sarkozy.PartVLaws.ChamberSpectral
public import Sarkozy.Cuts.CutBlock
public import Sarkozy.Cuts.CutTransport
public import Sarkozy.UpperReference.BlockCaps

@[expose] public section

/-!
# The block adapter for the middle root cuts L20 and L10 (`lem:front12:reference`(ii))

`paper/sections/20c_middle_frame.tex`, proof of `lem:front12:reference`(ii), first two
inequalities; `lem:layer12-geometry`(b); `lem:spec:cutkernel`(e); `lem:spec:tensorcomp`(b),(c),
`lem:majorant`(c) (W7's `cut_block_cap`).

The proof of (ii) reads: the plus half of `ϑ₀` carries the objects `0, 1, 2`, the half graph of
the root `G_{L,j}` at `ϑ₀` is `G_{F,j}` (`lem:layer12-geometry`(b)), the configurations of
`Π_{F₀}` are fixed by `ϑ₀`, so the cut form of `Π_{F₀}` at a half function `Φ` is `E_{λ_F} Φ²`;
for the uniform root the cut form of `Π_L` is `⟨Φ, A_𝔅 Φ⟩` for the block cut operator `A_𝔅` on
`L²(λ_F)`; the per-prime caps and the tensor step give the inequality. Formalized here:

* `recordData Λ`: the spectral data (`def:spec:data`) of the chamber cut `ϑ₀` of the record graph
  `G_L` on `ℤ/6ℤ × Λ` (the L20 cut for `Λ = Fin 2`, the L10 cut for `Λ = Fin 1`);
* `recordHalfEquiv_edges`: its half graph is `G_F` (`lem:layer12-geometry`(b), here for every `Λ`),
  hence `recordHalfLaw_weight`: the half law is the fold graph law;
* `pi_expect_equiv`: products of laws transported factorwise;
* **`blockRootForm`**: for a block of primes, the cut form at `ϑ₀` of the root
  `objLaw (λ_𝔅(G_L))` equals the kernel form of the tensor of the per-prime cut operators
  (`kernelForm (⊗ μ_p) (⊗ μ_p) (∏ K_p/Z_p)`), on the row functions (`blockRows`);
* **`blockFoldForm`**: the cut form at `ϑ₀` of `Π_{F₀}` of `objLaw (λ_𝔅(G_F))` is `E_{⊗ μ_p} Φ²`;
* **`rootEnvelope_of_cutCaps`**: `RootEnvelope D (g e^{BL/(X log X)}) b^{-1/2}` for any five-type
  datum whose root and fold laws are these block laws, from the per-prime bounds
  `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` (W7's `cut_block_cap`);
* `rootEnvelope₂_of_cutCaps`, `rootEnvelope₁_of_cutCaps`: the instances at V1's middle data
  (`middleBlock_datumHyp₂`, `middleBlock_datumHyp₁`).
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts

/-! ## Products of laws transported factorwise -/

/-- A precomposition bijection `y ↦ y ∘ e`. -/
def precomp {α β : Type*} (e : α ≃ β) (X : Type*) : (β → X) ≃ (α → X) where
  toFun y := y ∘ e
  invFun x := x ∘ e.symm
  left_inv y := by
    funext b
    simp
  right_inv x := by
    funext a
    simp

/-- **Products of laws transported factorwise**: if `T_i` carries `ν_i` to `μ_i` (weights), then
`E_{⊗ μ} G = E_{⊗ ν}[G ∘ (T_i)_i]`. -/
theorem pi_expect_equiv {I : Type*} [Fintype I] [DecidableEq I] {A B : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] (μ : ∀ i, FiniteLaw (A i))
    (ν : ∀ i, FiniteLaw (B i)) (T : ∀ i, B i ≃ A i)
    (hw : ∀ i b, (μ i).weight (T i b) = (ν i).weight b) (G : (∀ i, A i) → ℝ) :
    (FiniteLaw.pi μ).expect G = (FiniteLaw.pi ν).expect (fun b => G (fun i => T i (b i))) := by
  unfold FiniteLaw.expect
  refine (Fintype.sum_equiv (Equiv.piCongrRight T) _ _ fun b => ?_).symm
  change (∏ i, (ν i).weight (b i)) * _ = (∏ i, (μ i).weight (T i (b i))) * _
  simp only [hw]
  rfl

/-- A weight identity from an expectation identity along a bijection. -/
theorem weight_of_expect_equiv {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (μ : FiniteLaw A) (ν : FiniteLaw B) (T : B ≃ A)
    (h : ∀ Ψ : A → ℝ, μ.expect Ψ = ν.expect (fun y => Ψ (T y))) (y : B) :
    μ.weight (T y) = ν.weight y := by
  rw [weight_eq_expect, h, weight_eq_expect]
  refine ν.expect_congr fun y' => ?_
  simp only [T.apply_eq_iff_eq]

/-! ## The spectral data of the root cuts -/

section Data

variable (Λ : Type) [Fintype Λ] [DecidableEq Λ]

theorem record_flip_iff (u w : ZMod 6) :
    w = rot u ↔ (chamberCut 0).flip w = rot ((chamberCut 0).flip u) := by
  revert u w
  decide

/-- **The spectral data of the chamber cut `ϑ₀` of the record graph** `G_L` on `ℤ/6ℤ × Λ`
(`def:spec:data`): the cut L20 for `Λ = Fin 2`, L10 for `Λ = Fin 1`. The reflection `u ↦ 5 - u`
is an automorphism of `G_L` (`lem:record:fold-identification`(a)). -/
noncomputable def recordData : SpecData (ZMod 6 × Λ) where
  G := recordGraph Λ
  cut := (chamberCut 0).prodLeft Λ
  aut a b := by
    rw [mem_recordGraph, mem_recordGraph]
    exact record_flip_iff a.1 b.1
  order := by
    classical
    simpa only [Fintype.card_coe] using
      (Fintype.equivFin ((chamberCut 0).prodLeft Λ).Half).symm

theorem mem_recordHalf (v : ZMod 6 × Λ) :
    v ∈ (recordData Λ).cut.half ↔ v.1 ∈ (chamberCut 0).half := by
  change v ∈ (chamberCut 0).half ×ˢ Finset.univ ↔ _
  simp only [Finset.mem_product, Finset.mem_univ, and_true]

/-- The plus half of `ϑ₀` is `{0, 1, 2} × Λ`, the vertex set of `G_F`. -/
def recordHalfEquiv : (recordData Λ).cut.Half ≃ Fin 3 × Λ where
  toFun v := (fold 0 v.1.1, v.1.2)
  invFun v := ⟨((v.1.val : ZMod 6), v.2),
    (mem_recordHalf Λ _).mpr (PartVLaws.FieldGraphs.cast_mem_chamberHalf v.1)⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext (PartVLaws.FieldGraphs.fold0_cast_of_half v.1.1
      ((mem_recordHalf Λ _).mp v.2)) rfl
  right_inv v := by
    refine Prod.ext ?_ rfl
    simpa using fold_half 0 v.1

theorem record_half_edge (u w : ZMod 6) (hu : u ∈ (chamberCut 0).half)
    (hw : w ∈ (chamberCut 0).half) : w = rot u ↔ fold 0 u = 0 ∧ fold 0 w = 2 := by
  revert u w
  decide

/-- **`lem:layer12-geometry`(b)**: the half graph of `G_L` at `ϑ₀` is `G_F`, for every layer set. -/
theorem recordHalfEquiv_edges (a b : (recordData Λ).cut.Half) :
    (a, b) ∈ (recordData Λ).halfGraph.E ↔
      (recordHalfEquiv Λ a, recordHalfEquiv Λ b) ∈ (foldGraph Λ).E := by
  rw [SpecData.mem_halfGraph]
  change (a.1, b.1) ∈ (recordGraph Λ).E ↔ _
  rw [mem_recordGraph, mem_foldGraph]
  exact record_half_edge a.1.1 b.1.1 ((mem_recordHalf Λ _).mp a.2) ((mem_recordHalf Λ _).mp b.2)

section Laws

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  (hneL : (injLabellings F (recordGraph Λ)).Nonempty)
  (hneF : (injLabellings F (foldGraph Λ)).Nonempty)

/-- The half law of `ϑ₀` is the fold graph law. -/
theorem recordHalfLaw_expect (Ψ : ((recordData Λ).cut.Half → F) → ℝ) :
    ((recordData Λ).halfLaw hneL).expect Ψ =
      (graphLaw (foldGraph Λ) hneF).expect (fun y => Ψ (y ∘ recordHalfEquiv Λ)) := by
  let e := recordHalfEquiv Λ
  have hedge : ∀ a b, (a, b) ∈ (foldGraph Λ).E ↔
      (e.symm a, e.symm b) ∈ (recordData Λ).halfGraph.E := by
    intro a b
    rw [recordHalfEquiv_edges, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Cuts.graphLaw_iso _ _ e.symm hedge hneF ((recordData Λ).half_nonempty hneL) Ψ

theorem recordHalfLaw_weight (y : Fin 3 × Λ → F) :
    ((recordData Λ).halfLaw hneL).weight (precomp (recordHalfEquiv Λ) F y) =
      (graphLaw (foldGraph Λ) hneF).weight y :=
  weight_of_expect_equiv _ _ (precomp (recordHalfEquiv Λ) F)
    (recordHalfLaw_expect Λ hneL hneF) y

end Laws

end Data

/-! ## The block forms -/

section Block

variable (Λ : Type) [Fintype Λ] [DecidableEq Λ]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The rows of a block half configuration: `ξ ↦ (u, ℓ) ↦ (ξ_p(u, ℓ))_p`. -/
def blockRows (ξ : ∀ i, (recordData Λ).cut.Half → ZMod (pr i)) :
    (chamberCut 0).Half → Λ → BlockLabel pr :=
  fun u l i => ξ i ⟨(u.1, l), (mem_recordHalf Λ _).mpr u.2⟩

/-- The per-prime half laws `μ_p = λ_p(G_F)` of the block, as a product. -/
noncomputable abbrev halfPi (hL : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph Λ)).Nonempty) :
    FiniteLaw (∀ i, (recordData Λ).cut.Half → ZMod (pr i)) :=
  FiniteLaw.pi fun i => (recordData Λ).halfLaw (hL i)

/-- The kernel `∏_p K_p/Z_p` of the tensor of the per-prime cut operators. -/
noncomputable abbrev blockKernel
    (hL : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph Λ)).Nonempty)
    (x y : ∀ i, (recordData Λ).cut.Half → ZMod (pr i)) : ℝ :=
  ∏ i, (recordData Λ).cutK (x i) (y i) / (recordData Λ).cutZ (hL i)

/-- **The cut form of the uniform root at `ϑ₀` is the tensor of the per-prime cut operators**
(proof of `lem:front12:reference`(ii); `lem:spec:cutkernel`(e)): for the block law
`λ_𝔅(G_L) = ⊗_p λ_p(G_L)` read as a law of objects,
`(ϑ₀-form of Π_L)(φ, ψ) = ⟨φ ∘ rows, (⊗_p A_p)(ψ ∘ rows)⟩_{⊗ μ_p}`. -/
theorem blockRootForm (hL : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph Λ)).Nonempty)
    (φ ψ : ((chamberCut 0).Half → Λ → BlockLabel pr) → ℝ) :
    (chamberCut 0).form (lawL (objLaw (blockGraphLaw pr (recordGraph Λ) hL))) φ ψ =
      kernelForm (halfPi Λ pr hL) (halfPi Λ pr hL) (blockKernel Λ pr hL)
        (φ ∘ blockRows Λ pr) (ψ ∘ blockRows Λ pr) := by
  rw [← SpecData.block_cut_form (recordData Λ) hL]
  change (objLaw (blockGraphLaw pr (recordGraph Λ) hL)).expect _ = _
  rw [expect_objLaw]
  unfold blockGraphLaw
  rw [expect_tensor_eq_sum]
  rfl

/-- **The cut form of `Π_{F₀}` at `ϑ₀` is the `L²(⊗ μ_p)` norm** (proof of
`lem:front12:reference`(ii)): the configurations of `Π_{F₀}` are fixed by `ϑ₀`
(`F₀(5 - u) = F₀(u)`), and the fold graph law is the half law of `ϑ₀`. -/
theorem blockFoldForm (hL : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph Λ)).Nonempty)
    (hF : ∀ i, (injLabellings (ZMod (pr i)) (foldGraph Λ)).Nonempty)
    (φ : ((chamberCut 0).Half → Λ → BlockLabel pr) → ℝ) :
    (chamberCut 0).form (lawL (patternLaw (fold 0) (objLaw (blockGraphLaw pr (foldGraph Λ) hF))))
        φ φ =
      (halfPi Λ pr hL).expect (fun ξ => (φ ∘ blockRows Λ pr) ξ * (φ ∘ blockRows Λ pr) ξ) := by
  rw [pi_expect_equiv (fun i => (recordData Λ).halfLaw (hL i))
    (fun i => graphLaw (foldGraph Λ) (hF i)) (fun i => precomp (recordHalfEquiv Λ) _)
    (fun i y => recordHalfLaw_weight Λ (hL i) (hF i) y)]
  change (patternLaw (fold 0) (objLaw (blockGraphLaw pr (foldGraph Λ) hF))).expect _ = _
  rw [patternLaw, FiniteLaw.expect_map, expect_objLaw]
  unfold blockGraphLaw
  rw [expect_tensor_eq_sum]
  unfold FiniteLaw.expect
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  simp only [Function.comp_apply, PartVLaws.FieldGraphs.fold0_flip]
  rfl

/-- **The root envelope from per-prime cut caps** (`lem:front12:reference`(ii), first two
inequalities, with `lem:spec:tensorcomp`(b),(c) and `lem:majorant`(c)): for a five-type datum whose
root is `objLaw (λ_𝔅(G_L))` and whose fold law is `objLaw (λ_𝔅(G_F))`, on a block of primes
`p_i ≥ b ≥ X > 1` with `∑ log p_i ≤ L`, if every per-prime cut operator of `ϑ₀` satisfies
`-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` (and `g p^{-1/2} < 1`), then `Π_L ⪰_{ϑ₀} -d r Π_{F₀}` with
`d = g e^{BL/(X log X)}` and `r = b^{-1/2}`. -/
theorem rootEnvelope_of_cutCaps (D : Datum (Λ → BlockLabel pr))
    (hL : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph Λ)).Nonempty)
    (hF : ∀ i, (injLabellings (ZMod (pr i)) (foldGraph Λ)).Nonempty)
    (hpiL : D.piL = objLaw (blockGraphLaw pr (recordGraph Λ) hL))
    (hpiF : D.piF = objLaw (blockGraphLaw pr (foldGraph Λ) hF))
    {g B X L b : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ pr i) (hLs : ∑ i, Real.log (pr i) ≤ L)
    (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(pr i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (recordData Λ) (hL i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp (recordData Λ) (hL i) v⟫_ℝ ≤ (1 + B / pr i) * ‖v‖ ^ 2) :
    RootEnvelope D (g * Real.exp (B * L / (X * Real.log X))) (√b)⁻¹ := by
  have hcompL : D.compL = lawL (objLaw (blockGraphLaw pr (recordGraph Λ) hL)) := by
    unfold Datum.compL
    rw [hpiL]
  have hcompF : D.compF 0 =
      lawL (patternLaw (fold 0) (objLaw (blockGraphLaw pr (foldGraph Λ) hF))) := by
    unfold Datum.compF
    rw [hpiF]
  constructor
  · intro φ ψ
    change (chamberCut 0).form D.compL φ ψ -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) * (chamberCut 0).form (D.compF 0) φ ψ =
      (chamberCut 0).form D.compL ψ φ -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) * (chamberCut 0).form (D.compF 0) ψ φ
    rw [form_symm_of_flip_inv (chamberCut 0) (flip_inv_of_inv6 D.compL_inv6) φ ψ,
      D.compF0_positive.symmetric φ ψ]
  · intro φ
    change 0 ≤ (chamberCut 0).form D.compL φ φ -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) * (chamberCut 0).form (D.compF 0) φ φ
    rw [hcompL, hcompF, blockRootForm Λ pr hL φ φ, blockFoldForm Λ pr hL hF φ]
    have h := UpperReference.cut_block_cap (recordData Λ) pr hL hg hB hX hXb hbp hLs hgp hlow hup
      (φ ∘ blockRows Λ pr)
    have hn : Recentering.nrm (halfPi Λ pr hL) (φ ∘ blockRows Λ pr) ^ 2 =
        (halfPi Λ pr hL).expect (fun ξ => (φ ∘ blockRows Λ pr) ξ * (φ ∘ blockRows Λ pr) ξ) := by
      unfold Recentering.nrm Recentering.ip
      exact Real.sq_sqrt ((halfPi Λ pr hL).expect_nonneg fun ξ => mul_self_nonneg _)
    rw [hn] at h
    change _ ≤ kernelForm (halfPi Λ pr hL) (halfPi Λ pr hL) (blockKernel Λ pr hL) _ _ at h
    linarith

end Block

/-! ## The middle data -/

section Middle

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **L20 at a middle block** (`lem:front12:reference`(ii), first inequality, uniform root). -/
theorem rootEnvelope₂_of_cutCaps (hne : MiddleNonempty pr) {g B X L b : ℝ} (hg : 0 ≤ g)
    (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ pr i)
    (hLs : ∑ i, Real.log (pr i) ≤ L) (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(pr i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (recordData (Fin 2)) (hne.L2 i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp (recordData (Fin 2)) (hne.L2 i) v⟫_ℝ ≤
      (1 + B / pr i) * ‖v‖ ^ 2) :
    RootEnvelope (fieldDatum (middleBlock_datumHyp₂ pr hne))
      (g * Real.exp (B * L / (X * Real.log X))) (√b)⁻¹ :=
  rootEnvelope_of_cutCaps (Fin 2) pr _ hne.L2 hne.F2 rfl rfl hg hB hX hXb hbp hLs hgp hlow hup

/-- **L10 at a middle block** (`lem:front12:reference`(ii), second inequality; the one-layer root
is uniform on every piece). -/
theorem rootEnvelope₁_of_cutCaps (hne : MiddleNonempty pr) {g B X L b : ℝ} (hg : 0 ≤ g)
    (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ pr i)
    (hLs : ∑ i, Real.log (pr i) ≤ L) (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(pr i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (recordData (Fin 1)) (hne.L1 i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp (recordData (Fin 1)) (hne.L1 i) v⟫_ℝ ≤
      (1 + B / pr i) * ‖v‖ ^ 2) :
    RootEnvelope (fieldDatum (middleBlock_datumHyp₁ pr hne))
      (g * Real.exp (B * L / (X * Real.log X))) (√b)⁻¹ :=
  rootEnvelope_of_cutCaps (Fin 1) pr _ hne.L1 hne.F1 rfl rfl hg hB hX hXb hbp hLs hgp hlow hup

end Middle

end Sarkozy.BlockAdapter
