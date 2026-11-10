module

public import Sarkozy.IndexSupport.SignedIndex

/-!
# Product half-functions: factorization of means and conditional expectations

This file proves the construction-independent part of `cor:index-support-frame`(ii) and
of the identity `I_{κ,∅} = Y_κ` after `eq:record:expansion`: the queries have pairwise
distinct source slots and independent indices, so the half-function
`X_ω(x) = ∏_e φ_e(ω_e)(x_{u_e}) · ∏_{v ∉ {u_e}} F(x_v)` is a product of functions of the
independent `ω_e` at distinct slots, with `F` at the remaining slots; expectations and
conditional expectations therefore factorize over the queries.

* `piKron_mulVec_prod`: `(⊗_e A_e)(∏_e f_e) = ∏_e (A_e f_e)`.
* `act_productHalf`: a tensor product operator acts on a product half-function slot by slot
  (for the revealed projection: `X^𝒥_ω` carries the conditional expectation of the slot
  function of query `e` at `u_e` and `F` at the other slots).
* `vmean_productHalf_of_mean`: if every slot function averages to `F`
  (`E_{b,s} g^{I_b, M_0, s} = F_A` of `lem:twointerval`) and the slots `u_e` are distinct,
  then `E_ω X_ω = X̄`, the half-function carrying `F` at every slot.
* `cut_signed_index_bounds_of_product`: `cor:index-support-frame`(iii) and
  `eq:cp:mean-step` for product half-functions `X` (slots `u_e`) and `Y` (slots `ι v_e`)
  whose slot functions average to `F`.

The identification of the actual slot functions and their conditional expectations
(`g^{I,D,s}` and `lem:twointerval`) depends on the construction and is not formalized here.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

section Factor

variable {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*} [∀ e, Fintype (Ω e)]

/-- A tensor product of operators acts factorwise on product functions. -/
theorem piKron_mulVec_prod (A : ∀ e, Matrix (Ω e) (Ω e) ℝ) (f : ∀ e, Ω e → ℝ) :
    piKron A *ᵥ (fun ω => ∏ e, f e (ω e)) = fun ω => ∏ e, (A e *ᵥ f e) (ω e) := by
  funext ω
  simp only [Matrix.mulVec, dotProduct, piKron_apply]
  rw [Fintype.prod_sum (fun e y => A e (ω e) y * f e y)]
  apply sum_congr rfl
  intro η _
  rw [prod_mul_distrib]

variable {W L : Type*} [Fintype W] [DecidableEq W]

/-- A product half-function: query `e` carries `φ_e(ω_e)` at its slot `u_e`, and every
other slot carries `F`. -/
def productHalf (u : E → W) (φ : ∀ e, Ω e → L → ℝ) (F : L → ℝ) :
    (∀ e, Ω e) → (W → L) → ℝ :=
  fun ω x => (∏ e, φ e (ω e) (x (u e))) * ∏ v ∈ univ \ univ.image u, F (x v)

/-- A tensor product operator acts on a product half-function slot by slot. -/
theorem act_productHalf (A : ∀ e, Matrix (Ω e) (Ω e) ℝ) (u : E → W)
    (φ : ∀ e, Ω e → L → ℝ) (F : L → ℝ) :
    act (piKron A) (productHalf u φ F) =
      productHalf u (fun e ωe y => (A e *ᵥ (fun η => φ e η y)) ωe) F := by
  funext ω x
  have h := congrFun (piKron_mulVec_prod A (fun e η => φ e η (x (u e)))) ω
  simp only [Matrix.mulVec, dotProduct] at h
  simp only [act, productHalf, Matrix.mulVec, dotProduct]
  rw [← h, Finset.sum_mul]
  apply sum_congr rfl
  intro η _
  ring

theorem vmean_eq_act_mean [∀ e, Nonempty (Ω e)] {ι : Type*} (Z : (∀ e, Ω e) → ι → ℝ)
    (ω : ∀ e, Ω e) : vmean Z = act (piKron (fun e => meanMatrix (Ω e))) Z ω := by
  rw [piKron_meanMatrix, act_meanMatrix]

/-- The mean of a product half-function is the product half-function of the means. -/
theorem vmean_productHalf [∀ e, Nonempty (Ω e)] (u : E → W) (φ : ∀ e, Ω e → L → ℝ)
    (F : L → ℝ) :
    vmean (productHalf u φ F) = fun x =>
      (∏ e, (FiniteLaw.uniform (Ω e)).expect (fun η => φ e η (x (u e)))) *
        ∏ v ∈ univ \ univ.image u, F (x v) := by
  obtain ⟨ω⟩ := (inferInstance : Nonempty (∀ e, Ω e))
  rw [vmean_eq_act_mean _ ω, act_productHalf]
  funext x
  simp only [productHalf, meanMatrix_mulVec, FiniteLaw.expect_uniform, div_eq_inv_mul]

/-- If every slot function averages to `F` and the slots are distinct, the mean of the
product half-function is the half-function `X̄` carrying `F` at every slot. -/
theorem vmean_productHalf_of_mean [∀ e, Nonempty (Ω e)] {u : E → W} (hu : Function.Injective u)
    {φ : ∀ e, Ω e → L → ℝ} {F : L → ℝ}
    (hφ : ∀ e y, (FiniteLaw.uniform (Ω e)).expect (fun η => φ e η y) = F y) :
    vmean (productHalf u φ F) = fun x => ∏ v, F (x v) := by
  rw [vmean_productHalf]
  funext x
  simp only [hφ]
  have himg : ∏ v ∈ univ.image u, F (x v) = ∏ e, F (x (u e)) :=
    prod_image (fun a _ b _ hab => hu hab)
  rw [← himg, mul_comm, prod_sdiff (subset_univ _)]

end Factor

section Cut

variable {E : Type*} [Fintype E] [DecidableEq E] {Kq : E → Type*} [∀ e, Fintype (Kq e)]
  [∀ e, DecidableEq (Kq e)] {Ωc : ∀ e, Kq e → Type*} [∀ e j, Fintype (Ωc e j)]
  [∀ e j, DecidableEq (Ωc e j)] [∀ e j, Nonempty (Ωc e j)]
  {V : Type*} [Fintype V] [DecidableEq V]
  {𝔅 : Type*} [Fintype 𝔅] [DecidableEq 𝔅] {Xb : 𝔅 → Type*} [∀ b, Fintype (Xb b)]
  [∀ b, DecidableEq (Xb b)]

/-- **`cor:index-support-frame`(ii)+(iii) and `eq:cp:mean-step`** for product half-functions.
`X` carries the slot function `φ_e(ω_e)` at the source slot `u_e`, `Y` carries `ψ_e(ω_e)`
at the reflected target slot `ι v_e`, both carry `F` elsewhere; the slots of each family are
distinct and every slot function averages to `F` over its uniform index. Then, with
`X̄ = ∏_v F(x_v)`, all conclusions of `cut_signed_index_bounds` hold. -/
theorem cut_signed_index_bounds_of_product (C : ∀ e j, Chain (Ωc e j))
    (t : ∀ e j, Tails (C e j).depth) (Tc : ∀ e j, Matrix (Ωc e j) (Ωc e j) ℝ)
    (hT : ∀ e j (l : Fin ((C e j).depth + 1)),
      RangeBound ((C e j).diff l) (Tc e j) ((t e j).tail l))
    (hT0 : ∀ e j, Tc e j * (C e j).cond 0 = (C e j).cond 0)
    (c : ReflectionCut V) (ML ν MR : ∀ b, ((V → Xb b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ b, c.Bracket (ML b) (ν b) (MR b))
    {u w : E → c.Half} (hu : Function.Injective u) (hw : Function.Injective w)
    (φ ψ : ∀ e, (∀ j, Ωc e j) → (∀ b, Xb b) → ℝ) (F : (∀ b, Xb b) → ℝ)
    (hφ : ∀ e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => φ e η y) = F y)
    (hψ : ∀ e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => ψ e η y) = F y) :
    let X := productHalf u φ F
    let Y := productHalf w ψ F
    let Xbar : (c.Half → ∀ b, Xb b) → ℝ := fun x => ∏ v, F (x v)
    let unif := FiniteLaw.uniform (∀ e, ∀ j, Ωc e j)
    let Jν := unif.expect (fun ω => c.form (tensorLaw ν) (X ω) (act (signedIndexOp Tc) Y ω))
    let Yν := c.form (tensorLaw ν) Xbar Xbar
    let eL := c.form (tensorLaw ML) Xbar Xbar
    let eR := c.form (tensorLaw MR) Xbar Xbar
    let VL := (queryLaw C t).expect (fun J => unif.expect (fun ω =>
      c.form (tensorLaw ML) (queryReveal C J X ω) (queryReveal C J X ω)))
    let VR := (queryLaw C t).expect (fun J => unif.expect (fun ω =>
      c.form (tensorLaw MR) (queryReveal C J Y ω) (queryReveal C J Y ω)))
    eL ≤ VL ∧ 0 ≤ eL ∧ eR ≤ VR ∧ 0 ≤ eR ∧
      |Jν - Yν| ≤ (1 / 2) * ((VL - eL) + (VR - eR)) ∧
      |Jν| ≤ Real.sqrt VL * Real.sqrt VR ∧
      Jν ≤ Yν + (1 / 2) * ((VL - eL) + (VR - eR)) := by
  intro X Y Xbar
  exact cut_signed_index_bounds C t Tc hT hT0 c ML ν MR hbr X Y Xbar
    (vmean_productHalf_of_mean hu hφ) (vmean_productHalf_of_mean hw hψ)

end Cut

section Expansion

variable {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*}

/-- The expansion of the signed index operator (`eq:record:expansion`):
`⊗_e (2P_e - T_e) = ∑_𝒮 (-1)^{|𝒮|} 2^{k-|𝒮|} ⊗_{e ∈ 𝒮} T_e ⊗_{e ∉ 𝒮} P_e`. -/
theorem piKron_two_sub_expansion (P T : ∀ e, Matrix (Ω e) (Ω e) ℝ) :
    piKron (fun e => (2 : ℝ) • P e - T e) =
      ∑ S : Finset E, ((-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card)) •
        piKron (fun e => if e ∈ S then T e else P e) := by
  ext x y
  simp only [piKron_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  rw [show (∏ e, (2 * P e (x e) (y e) - T e (x e) (y e))) =
      ∏ e, (-(T e (x e) (y e)) + 2 * P e (x e) (y e)) from
    prod_congr rfl (fun e _ => by ring), Fintype.prod_add]
  apply sum_congr rfl
  intro S _
  have hsplit : (∏ e, (if e ∈ S then T e else P e) (x e) (y e)) =
      (∏ e ∈ S, T e (x e) (y e)) * ∏ e ∈ Sᶜ, P e (x e) (y e) := by
    rw [← Finset.prod_mul_prod_compl S]
    congr 1
    · exact prod_congr rfl (fun e he => by rw [ite_eq_left he])
    · exact prod_congr rfl (fun e he => by rw [ite_eq_right (Finset.mem_compl.mp he)])
  rw [hsplit, Finset.prod_neg, prod_mul_distrib, prod_const, Finset.card_compl]
  ring

end Expansion

end Sarkozy.IndexSupport
