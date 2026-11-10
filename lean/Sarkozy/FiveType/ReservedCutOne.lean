module

public import Sarkozy.FiveType.ReservedCut

/-!
# The reserved cut in one coordinate (`lem:five-type`(e), one coordinate)

Source: `lem:five-type`(e), `paper/sections/17_completion_repair.tex`; the case "components of
one coordinate (objects carrying one label per layer)".

The two-layer components are those of a five-type datum `D2` on `𝔛 = X^{\{0,1\}}`. The one-layer
components are those of a datum `D1` on `X`. Their configurations `ℤ/6ℤ → 𝔛` are read on the
slots `ℤ/6ℤ × {0, 1}` through `unc`, `unc(Ψ)_{(u,ℓ)} = Ψ_u(ℓ)`, since the layer swap `ι` acts
inside the labels. On these slots:
* `ι` is `resCut (ZMod 6)` (`layerCut` in the layer coordinate);
* the chamber cut `ϑ_i` is `chamberCut2 i`;
* `Diag_ι` is the pushforward along `diag1`, `diag1(z')_{(u,ℓ)} = z'_u`.

* `piT_eq_sum`: `π_t = ∑_{φ ∈ P_t} Π_φ` (`dcomp`), for every datum.
* `fold_pairing_one`: the paired measure
  `μ̃ = ∑_t w_t r^{deg t} π_{t,2} + r ∑_t v_t r^{deg t} Diag_ι(π_{t,1})` satisfies `μ̃ ⪰_ι 0`,
  when every two-layer component satisfies `Π ⪰_ι -k_t r Diag_ι(Π^{(1)})` (with the one-layer
  component of the same pattern) and `v_t ≥ k_t w_t ≥ 0`.
* **`reserved_rp_one`**: if moreover the two-layer measure `D2.Q (w r^{deg})` and the one-layer
  measure `D1.Q (v r^{deg})` are reflection positive at every chamber cut (the conclusions of
  (b), (c) or (f)), then `μ̃` is reflection positive at every chamber cut and at `ι`.
* `reserved_rp_one_of_laws`: the same conclusion from the bounds of the five laws of the data,
  through `patternLaw_below` and `below_mono_coeff`.
* `diag1_below`: `Diag_ι` preserves the order `⪰_ϑ` at the chamber cuts.
* `patternLaw_below`: the field-law bound passes to pattern laws. If
  `λ ⪰_ι -c Diag_ι(λ^{(1)})` for a law `λ` on `𝔛^O` and its one-layer law `λ^{(1)}`, then
  `Π_φ(λ) ⪰_ι -c Diag_ι(Π_φ(λ^{(1)}))` for every pattern `φ : ℤ/6ℤ → O`; this is the map
  `ω ↦ ω ∘ φ` of the paper. In the applications `Γ` and `ν` are images of `π_E` under such
  maps. So the merges and the constants inherit the bound of the matching law.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings ReflectionCut TwoCoord Reserved

namespace ReservedOne

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Uncurrying: a configuration of two-layer labels, read on the slots `O × {0, 1}`. -/
def unc {O : Type*} (Ψ : O → ZMod 2 → X) : O × ZMod 2 → X := fun p => Ψ p.1 p.2

/-- The diagonal embedding `z_{(u,ℓ)} = z'_u` of one-layer configurations. -/
def diag1 {O : Type*} (z' : O → X) : O × ZMod 2 → X := fun p => z' p.1

/-- The layer swap `ι` on `O × {0, 1}`. -/
def resCut (O : Type*) [Fintype O] [DecidableEq O] : ReflectionCut (O × ZMod 2) :=
  layerCut.prodRight O

/-- The chamber cut `ϑ_i` on the slots `ℤ/6ℤ × {0, 1}`. -/
def chamberCut2 (i : ZMod 6) : ReflectionCut (ZMod 6 × ZMod 2) :=
  (chamberCut i).prodLeft (ZMod 2)

section Components

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- The components `Π_φ`, `φ ∈ P_t`, of a five-type datum. -/
noncomputable def dcomp (D : Datum 𝔛) : (t : Ty) → PatIdx t → ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ
  | .L, _ => D.compL
  | .D, j => D.compF (j : Fin 3)
  | .S, s => D.compE (s : Fin 2)
  | .R, sk => D.compG (sk : Fin 2 × Fin 3).1 (sk : Fin 2 × Fin 3).2
  | .C, _ => D.compC

/-- **`π_t = ∑_{φ ∈ P_t} Π_φ`.** -/
theorem piT_eq_sum (D : Datum 𝔛) (t : Ty) : D.piT t = ∑ φ : PatIdx t, dcomp D t φ := by
  cases t with
  | L => exact (Fintype.sum_unique (ι := Unit) (fun φ => dcomp D .L φ)).symm
  | D => rfl
  | S => rfl
  | R =>
    refine Eq.trans ?_ (Fintype.sum_prod_type (fun sk : Fin 2 × Fin 3 => dcomp D .R sk)).symm
    rfl
  | C => rfl

theorem dcomp_nonneg (D : Datum 𝔛) (t : Ty) (φ : PatIdx t) {f : (ZMod 6 → 𝔛) → ℝ}
    (hf : ∀ z, 0 ≤ f z) : 0 ≤ dcomp D t φ f := by
  cases t with
  | L => exact FiniteLaw.expect_nonneg _ hf
  | D => exact FiniteLaw.expect_nonneg _ hf
  | S => exact FiniteLaw.expect_nonneg _ hf
  | R => exact FiniteLaw.expect_nonneg _ hf
  | C => exact FiniteLaw.expect_nonneg _ hf

end Components

variable (D2 : Datum (ZMod 2 → X)) (D1 : Datum X)

/-- The paired measure of (e) in one coordinate, on the slots `ℤ/6ℤ × {0, 1}`:
`μ̃ = ∑_t w_t r^{deg t} π_{t,2} + r ∑_t v_t r^{deg t} Diag_ι(π_{t,1})`. -/
noncomputable def pairedMeasure1 (w v : Ty → ℝ) (r : ℝ) :
    ((ZMod 6 × ZMod 2 → X) → ℝ) →ₗ[ℝ] ℝ :=
  pushFunctional (D2.Q (fun t => w t * r ^ t.deg)) unc +
    r • pushFunctional (D1.Q (fun t => v t * r ^ t.deg)) diag1

/-- `μ̃` as a sum of pairs, one for each two-layer component. -/
theorem pairedMeasure1_eq (w v : Ty → ℝ) (r : ℝ) :
    pairedMeasure1 D2 D1 w v r =
      ∑ t, ∑ φ : PatIdx t,
        ((w t * r ^ t.deg) • pushFunctional (dcomp D2 t φ) unc +
          (v t * r ^ (t.deg + 1)) • pushFunctional (dcomp D1 t φ) diag1) := by
  refine LinearMap.ext fun f => ?_
  simp only [pairedMeasure1, Datum.Q, piT_eq_sum, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul, push_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun φ _ => ?_
  rw [pow_succ]
  ring

omit [Fintype X] [DecidableEq X] in
/-- The diagonal copy is fixed samplewise by `ι`. -/
theorem diag1_fixed {O : Type*} [Fintype O] [DecidableEq O] (z' : O → X) :
    diag1 z' ∘ (resCut O).flip = diag1 z' :=
  rfl

/-- **`lem:five-type`(e), the reserved cut, one coordinate.** If every two-layer component
satisfies `Π_φ ⪰_ι -k_t r Diag_ι(Π^{(1)}_φ)` and `v_t ≥ k_t w_t`, `w_t ≥ 0`, `r ≥ 0`, then
`μ̃ ⪰_ι 0`. -/
theorem fold_pairing_one (w v k : Ty → ℝ) {r : ℝ} (hr : 0 ≤ r) (hw : ∀ t, 0 ≤ w t)
    (hvk : ∀ t, k t * w t ≤ v t)
    (hcomp : ∀ t (φ : PatIdx t), (resCut (ZMod 6)).Below
      (-(k t * r) • pushFunctional (dcomp D1 t φ) diag1) (pushFunctional (dcomp D2 t φ) unc)) :
    (resCut (ZMod 6)).Positive (pairedMeasure1 D2 D1 w v r) := by
  rw [pairedMeasure1_eq]
  refine Positive.sum _ fun t _ => Positive.sum _ fun φ _ => ?_
  refine pair_term_positive (resCut (ZMod 6)) diag1 diag1_fixed
    (fun f hf => dcomp_nonneg D1 t φ hf) (hcomp t φ)
    (mul_nonneg (hw t) (pow_nonneg hr _)) ?_
  have h := mul_le_mul_of_nonneg_right (hvk t) (pow_nonneg hr (t.deg + 1))
  calc k t * r * (w t * r ^ t.deg) = k t * w t * r ^ (t.deg + 1) := by rw [pow_succ]; ring
    _ ≤ v t * r ^ (t.deg + 1) := h

omit [Fintype X] [DecidableEq X] in
/-- Uncurrying is half-local for `ϑ_i` and `ϑ_i × {0,1}`. -/
theorem positive_unc (i : ZMod 6) {L : ((ZMod 6 → ZMod 2 → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : (chamberCut i).Positive L) : (chamberCut2 i).Positive (pushFunctional L unc) :=
  positive_push_halfLocal (chamberCut2 i) h unc
    (fun x w => x ⟨w.1.1, (Finset.mem_product.mp w.2).1⟩ w.1.2) (fun _ => rfl) (fun _ => rfl)

omit [Fintype X] [DecidableEq X] in
/-- **`Diag_ι` preserves reflection positivity at the chamber cuts**: the diagonal embedding is
half-local for `ϑ_i` on the one-layer and the two-layer slots. -/
theorem positive_diag1 (i : ZMod 6) {L : ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : (chamberCut i).Positive L) : (chamberCut2 i).Positive (pushFunctional L diag1) :=
  positive_push_halfLocal (chamberCut2 i) h diag1
    (fun x w => x ⟨w.1.1, (Finset.mem_product.mp w.2).1⟩) (fun _ => rfl) (fun _ => rfl)

/-- **`lem:five-type`(e), conclusion, one coordinate.** If the two-layer five-type measure with
the weights `w_t r^{deg t}` and the one-layer one with the weights `v_t r^{deg t}` are
reflection positive at every chamber cut (by (b), (c) or (f), root envelopes included), and the
component bounds and `v_t ≥ k_t w_t ≥ 0` hold, then `μ̃` is reflection positive at every chamber
cut and at `ι`. -/
theorem reserved_rp_one (w v k : Ty → ℝ) {r : ℝ} (hr : 0 ≤ r) (hw : ∀ t, 0 ≤ w t)
    (hvk : ∀ t, k t * w t ≤ v t)
    (hcomp : ∀ t (φ : PatIdx t), (resCut (ZMod 6)).Below
      (-(k t * r) • pushFunctional (dcomp D1 t φ) diag1) (pushFunctional (dcomp D2 t φ) unc))
    (h2 : RPAll (D2.Q (fun t => w t * r ^ t.deg))) (h1 : RPAll (D1.Q (fun t => v t * r ^ t.deg))) :
    (∀ i, (chamberCut2 i).Positive (pairedMeasure1 D2 D1 w v r)) ∧
      (resCut (ZMod 6)).Positive (pairedMeasure1 D2 D1 w v r) :=
  ⟨fun i => (positive_unc i (h2 i)).add ((positive_diag1 i (h1 i)).smul hr),
    fold_pairing_one D2 D1 w v k hr hw hvk hcomp⟩

/-- **Pattern laws inherit the field-law bound at `ι`** (`lem:five-type`(e), last claims, one
coordinate). If a law `λ` on `𝔛^O` (two-layer labels) and its one-layer law `λ^{(1)}` on `X^O`
satisfy `λ ⪰_ι -c Diag_ι(λ^{(1)})`, then `Π_φ(λ) ⪰_ι -c Diag_ι(Π_φ(λ^{(1)}))` for every pattern
`φ`. -/
theorem patternLaw_below {O : Type*} [Fintype O] [DecidableEq O] (φ : ZMod 6 → O)
    (lam2 : FiniteLaw (O → ZMod 2 → X)) (lam1 : FiniteLaw (O → X)) {c : ℝ}
    (h : (resCut O).Below (-c • pushFunctional (lawL lam1) diag1)
      (pushFunctional (lawL lam2) unc)) :
    (resCut (ZMod 6)).Below (-c • pushFunctional (lawL (patternLaw φ lam1)) diag1)
      (pushFunctional (lawL (patternLaw φ lam2)) unc) := by
  have hπ : CutMap (resCut (ZMod 6)) (resCut O) (fun p : ZMod 6 × ZMod 2 => (φ p.1, p.2)) := by
    constructor
    · intro p hp
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (Finset.mem_product.mp hp).2⟩
    · intro p
      rfl
  have h' := below_pullback (resCut O) (resCut (ZMod 6)) _ hπ φ diag1 diag1 (fun _ => rfl) h
  have e2 : pushFunctional (lawL (patternLaw φ lam2)) unc =
      ReflectionCut.pullback (pushFunctional (lawL lam2) unc)
        (fun p : ZMod 6 × ZMod 2 => (φ p.1, p.2)) := by
    refine LinearMap.ext fun f => ?_
    change (patternLaw φ lam2).expect (f ∘ unc) = lam2.expect (fun ω => f (unc ω ∘ _))
    rw [patternLaw, FiniteLaw.expect_map]
    rfl
  have e1 : pushFunctional (lawL (patternLaw φ lam1)) diag1 =
      pushFunctional (ReflectionCut.pullback (lawL lam1) φ) diag1 := by
    refine LinearMap.ext fun f => ?_
    change (patternLaw φ lam1).expect (f ∘ diag1) = lam1.expect (fun ω => f (diag1 (ω ∘ φ)))
    rw [patternLaw, FiniteLaw.expect_map]
    rfl
  rw [e2, e1]
  exact h'

omit [Fintype X] [DecidableEq X] in
/-- **`Diag_ι` preserves the order `⪰_ϑ` at the chamber cuts**, one coordinate. -/
theorem diag1_below (i : ZMod 6) {L M : ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : (chamberCut i).Below L M) :
    (chamberCut2 i).Below (pushFunctional L diag1) (pushFunctional M diag1) :=
  diag_below_halfLocal (chamberCut i) (chamberCut2 i) diag1
    (fun x w => x ⟨w.1.1, (Finset.mem_product.mp w.2).1⟩) (fun _ => rfl) (fun _ => rfl) h

/-- **`lem:five-type`(e) from the bounds of the laws of the data**, one coordinate. Suppose the
five laws of the two-layer datum `D2` and of the one-layer datum `D1` satisfy
`λ ⪰_ι -κ r Diag_ι(λ^{(1)})`, with the coefficients `κ_L` (root `π_L`), `κ_F` (fold law `π_F`),
`κ_E` (matching law `π_E`), `κ_G` (merge law `Γ`) and `κ_C` (middle law `ν`), and that the
type coefficients dominate them. Then every component satisfies the hypothesis of
`fold_pairing_one`, and the conclusions of `reserved_rp_one` hold under its chamber
hypotheses. In the applications `Γ` and `ν` are images of `π_E`, so `κ_G = κ_C = κ_E` is
available by `patternLaw_below`. -/
theorem reserved_rp_one_of_laws (w v k : Ty → ℝ) (κL κF κE κG κC : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hw : ∀ t, 0 ≤ w t) (hvk : ∀ t, k t * w t ≤ v t)
    (hkL : κL ≤ k .L) (hkD : κF ≤ k .D) (hkS : κE ≤ k .S) (hkR : κG ≤ k .R) (hkC : κC ≤ k .C)
    (hL : (resCut (ZMod 6)).Below (-(κL * r) • pushFunctional (lawL D1.piL) diag1)
      (pushFunctional (lawL D2.piL) unc))
    (hF : (resCut (Fin 3)).Below (-(κF * r) • pushFunctional (lawL D1.piF) diag1)
      (pushFunctional (lawL D2.piF) unc))
    (hE : (resCut (Fin 3)).Below (-(κE * r) • pushFunctional (lawL D1.piE) diag1)
      (pushFunctional (lawL D2.piE) unc))
    (hG : (resCut (Fin 2)).Below (-(κG * r) • pushFunctional (lawL D1.Gam) diag1)
      (pushFunctional (lawL D2.Gam) unc))
    (hC : (resCut (Fin 1)).Below (-(κC * r) • pushFunctional (lawL D1.nu1) diag1)
      (pushFunctional (lawL D2.nu1) unc))
    (h2 : RPAll (D2.Q (fun t => w t * r ^ t.deg))) (h1 : RPAll (D1.Q (fun t => v t * r ^ t.deg))) :
    (∀ i, (chamberCut2 i).Positive (pairedMeasure1 D2 D1 w v r)) ∧
      (resCut (ZMod 6)).Positive (pairedMeasure1 D2 D1 w v r) := by
  refine reserved_rp_one D2 D1 w v k hr hw hvk (fun t φ => ?_) h2 h1
  have hpos : (resCut (ZMod 6)).Positive (pushFunctional (dcomp D1 t φ) diag1) :=
    diag_positive_of_fixed _ diag1 diag1_fixed fun f hf => dcomp_nonneg D1 t φ hf
  cases t with
  | L => exact below_mono_coeff _ hpos (mul_le_mul_of_nonneg_right hkL hr) hL
  | D =>
    exact below_mono_coeff _ hpos (mul_le_mul_of_nonneg_right hkD hr)
      (patternLaw_below (fold (φ : Fin 3)) D2.piF D1.piF hF)
  | S =>
    exact below_mono_coeff _ hpos (mul_le_mul_of_nonneg_right hkS hr)
      (patternLaw_below (matching (φ : Fin 2)) D2.piE D1.piE hE)
  | R =>
    exact below_mono_coeff _ hpos (mul_le_mul_of_nonneg_right hkR hr)
      (patternLaw_below (merge (φ : Fin 2 × Fin 3).1 (φ : Fin 2 × Fin 3).2) D2.Gam D1.Gam hG)
  | C =>
    exact below_mono_coeff _ hpos (mul_le_mul_of_nonneg_right hkC hr)
      (patternLaw_below Datum.constPat D2.nu1 D1.nu1 hC)

end ReservedOne

end Sarkozy.FiveType
