module

public import Sarkozy.PartVLaws.SchurRows
public import Sarkozy.PartVLaws.UpperGraphs

@[expose] public section

/-!
# The matching kernel of a row datum has exact marginals

`paper/sections/17_completion_repair.tex`, the remark after `def:five-type-datum`: "`T^b_E`, the
density of the conditional law of the objects `0, 2` given `ω₁ = b`, is a coupling of `ν^b` with
itself, `T_E^b 𝟙 = (T_E^b)^* 𝟙 = 𝟙`."

This is the hypothesis "exact marginals" of `lem:five-type`(c) and (f), and of the Schur and joint
branches of (V2). It is not spectral: it holds for every datum built by `datumOfGam` from an
exchangeable matching law (`datumOfGam_exactE`), in particular for every row datum of the upper and
tail laws (`rowD0_exactE`, `rowD1_exactE`). So in (V2) only the norm bound of `T_E^b - J` and the
fold or joint data of `T_F^b` remain inputs:
* `validRows_schur_rowD0`, `validRows_schur_rowD1`: the Schur branch of `ValidRows` for a row
  datum, from the fold data and the `E` norm bound alone. (The field `exactE` of `SchurRowData`
  is likewise always supplied by `rowD0_exactE`, `rowD1_exactE`.)
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- The configurations with objects `0, 1` equal to `x, b` are the `![x, b, y]`. -/
theorem gamOf_weight_eq_sum (piE : FiniteLaw (Fin 3 → 𝔛)) (x b : 𝔛) :
    (gamOf piE).weight ![x, b] = ∑ y, piE.weight ![x, b, y] := by
  rw [gamOf, map_weight_eq]
  have hfilt : (univ.filter fun ω : Fin 3 → 𝔛 => (fun i : Fin 2 => ω i.castSucc) = ![x, b]) =
      univ.image fun y => ![x, b, y] := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      have h0 : ω 0 = x := by
        have := congrFun h 0
        simpa using this
      have h1 : ω 1 = b := by
        have := congrFun h 1
        simpa using this
      refine ⟨ω 2, ?_⟩
      funext i
      fin_cases i
      · simp [h0]
      · simp [h1]
      · rfl
    · rintro ⟨y, rfl⟩
      funext i
      fin_cases i <;> rfl
  rw [hfilt, sum_image]
  intro y _ y' _ h
  have := congrFun h 2
  simpa using this

omit [DecidableEq 𝔛] in
/-- `π_E(x, b, y) = π_E(y, b, x)` for an exchangeable `π_E`. -/
theorem piE_swap02 (piE : FiniteLaw (Fin 3 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    (x b y : 𝔛) : piE.weight ![x, b, y] = piE.weight ![y, b, x] := by
  rw [← hexch (Equiv.swap 0 2) ![y, b, x]]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- One term of the row sum of the matching kernel. -/
theorem term_eq (piE : FiniteLaw (Fin 3 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    {b x : 𝔛} (hb : (nuOf piE).weight b ≠ 0) (hx : (nubOf piE b).weight x ≠ 0) (y : 𝔛) :
    (nubOf piE b).weight y * kernelOf piE piE b x y =
      piE.weight ![x, b, y] / ((nuOf piE).weight b * (nubOf piE b).weight x) := by
  unfold kernelOf
  split_ifs with hden
  · have hy : (nubOf piE b).weight y = 0 := by
      rcases mul_eq_zero.mp hden with h | h
      · exact absurd h (mul_ne_zero hb hx)
      · exact h
    have hπ : piE.weight ![x, b, y] = 0 := by
      rw [piE_swap02 piE hexch]
      have hle := piE_le_gam piE ![y, b, x]
      have hg := gamOf_weight piE ![y, b]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hle hg
      rw [hg, hy, mul_zero] at hle
      exact le_antisymm hle (piE.nonneg _)
    rw [hy, hπ, zero_mul, zero_div]
  · have hy : (nubOf piE b).weight y ≠ 0 := right_ne_zero_of_mul hden
    field_simp

/-- **The matching kernel of `datumOfGam` has exact marginals** at every `b ∈ supp ν`:
`T_E^b 𝟙 = (T_E^b)^* 𝟙 = 𝟙` on the support of `ν^b`. -/
theorem kernelOf_exactE (piE : FiniteLaw (Fin 3 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    {b : 𝔛} (hb : (nuOf piE).weight b ≠ 0) :
    ExactMarginals (nubOf piE b) (kernelOf piE piE b) := by
  have hden : ∀ x, (nubOf piE b).weight x ≠ 0 →
      (nuOf piE).weight b * (nubOf piE b).weight x ≠ 0 := fun x hx => mul_ne_zero hb hx
  have hgam : ∀ x, (gamOf piE).weight ![x, b] =
      (nuOf piE).weight b * (nubOf piE b).weight x := by
    intro x
    have := gamOf_weight piE ![x, b]
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] using this
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · unfold kone
    rw [Finset.sum_congr rfl fun y _ => term_eq piE hexch hb hx y, ← Finset.sum_div,
      ← gamOf_weight_eq_sum, hgam, div_self (hden x hx)]
  · unfold kone'
    have hsymm : ∀ x, (nubOf piE b).weight x * kernelOf piE piE b x y =
        (nubOf piE b).weight x * kernelOf piE piE b y x := by
      intro x
      unfold kernelOf
      have hw : piE.weight ![x, b, y] = piE.weight ![y, b, x] := piE_swap02 piE hexch x b y
      have hc : (nuOf piE).weight b * (nubOf piE b).weight x * (nubOf piE b).weight y =
          (nuOf piE).weight b * (nubOf piE b).weight y * (nubOf piE b).weight x := by ring
      rw [hc, hw]
    rw [Finset.sum_congr rfl fun x _ => hsymm x,
      Finset.sum_congr rfl fun x _ => term_eq piE hexch hb hy x, ← Finset.sum_div,
      ← gamOf_weight_eq_sum, hgam, div_self (hden y hy)]

/-- **`datumOfGam` has exact matching marginals.** -/
theorem datumOfGam_exactE (piE piF : FiniteLaw (Fin 3 → 𝔛)) (piL : FiniteLaw (ZMod 6 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    (hsupp : GamSupported piE piF)
    (hL : ∀ (k : Fin 6) (Ψ : ZMod 6 → 𝔛), piL.weight (Ψ ∘ g6 k) = piL.weight Ψ) (b : 𝔛)
    (hb : (datumOfGam piE piF piL hexch hsupp hL).nu.weight b ≠ 0) :
    ExactMarginals ((datumOfGam piE piF piL hexch hsupp hL).nub b)
      ((datumOfGam piE piF piL hexch hsupp hL).TE b) :=
  kernelOf_exactE piE hexch hb

section Rows

variable {X : Type} [Fintype X] [DecidableEq X] {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-- **Every row datum of the coordinate `0` has exact matching marginals.** -/
theorem rowD0_exactE (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp0 lam f') (b : f'.Obj × Λ → X)
    (hb : (rowD0 lam f' h).nu.weight b ≠ 0) :
    ExactMarginals ((rowD0 lam f' h).nub b) ((rowD0 lam f' h).TE b) :=
  datumOfGam_exactE _ _ _ h.exch h.supp h.root b hb

/-- **Every row datum of the coordinate `1` has exact matching marginals.** -/
theorem rowD1_exactE (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp1 lam f') (b : f'.Obj × Λ → X)
    (hb : (rowD1 lam f' h).nu.weight b ≠ 0) :
    ExactMarginals ((rowD1 lam f' h).nub b) ((rowD1 lam f' h).TE b) :=
  datumOfGam_exactE _ _ _ h.exch h.supp h.root b hb

/-- **The Schur branch of (V2) for a row datum of the coordinate `0`**, from the fold data of
`T_F^b` and the bound `‖T_E^b - J‖ ≤ h r` only (the exact marginals are proved). -/
theorem validRows_schur_rowD0 (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h0 : RowHyp0 lam f') {r f h M H β qperp tY : ℝ} (hq : 0 ≤ qperp)
    (htY : 0 < tY) (htH : tY ≤ H⁻¹) (hHM : H + tY ≤ M) (hf : (qperp + β ^ 2 / tY) / r ≤ f)
    (hb : ∀ b, (rowD0 lam f' h0).nu.weight b ≠ 0 →
      NormBound ((rowD0 lam f' h0).nub b) ((rowD0 lam f' h0).TE b) (h * r) ∧
        FoldData ((rowD0 lam f' h0).nub b) ((rowD0 lam f' h0).TF b) H β qperp) :
    ValidRows (rowD0 lam f' h0) r f h M :=
  Or.inr (Or.inl ⟨H, β, qperp, tY, hq, htY, htH, hHM, hf, fun b hb' =>
    ⟨rowD0_exactE lam f' h0 b hb', (hb b hb').1, (hb b hb').2⟩⟩)

/-- **The Schur branch of (V2) for a row datum of the coordinate `1`.** -/
theorem validRows_schur_rowD1 (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h1 : RowHyp1 lam f') {r f h M H β qperp tY : ℝ} (hq : 0 ≤ qperp)
    (htY : 0 < tY) (htH : tY ≤ H⁻¹) (hHM : H + tY ≤ M) (hf : (qperp + β ^ 2 / tY) / r ≤ f)
    (hb : ∀ b, (rowD1 lam f' h1).nu.weight b ≠ 0 →
      NormBound ((rowD1 lam f' h1).nub b) ((rowD1 lam f' h1).TE b) (h * r) ∧
        FoldData ((rowD1 lam f' h1).nub b) ((rowD1 lam f' h1).TF b) H β qperp) :
    ValidRows (rowD1 lam f' h1) r f h M :=
  Or.inr (Or.inl ⟨H, β, qperp, tY, hq, htY, htH, hHM, hf, fun b hb' =>
    ⟨rowD1_exactE lam f' h1 b hb', (hb b hb').1, (hb b hb').2⟩⟩)

/-- **V1's middle data have exact matching marginals** too (`fieldDatum`, built by `datumOf` from
an exchangeable matching law). -/
theorem fieldDatum_exactE {lamE lamF : FiniteLaw (Fin 3 × Λ → X)}
    {lamL : FiniteLaw (ZMod 6 × Λ → X)} (h : DatumHyp lamE lamF lamL) (b : Λ → X)
    (hb : (fieldDatum h).nu.weight b ≠ 0) :
    ExactMarginals ((fieldDatum h).nub b) ((fieldDatum h).TE b) :=
  kernelOf_exactE _ h.exch hb

end Rows

end Sarkozy.PartVLaws
