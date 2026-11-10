module

public import Sarkozy.BlockRows.Eval
public import Sarkozy.BlockInputs.Middle

@[expose] public section

/-!
# Block rows, III: the middle rows `lem:front12:reference`(i) from per-prime certificates

`paper/sections/20c_middle_frame.tex`, paragraph "Rows" of `subsec:middle-reference-law` and
`lem:front12:reference`(i) with its proof ("One prime", "The block", "Evaluation at the piece
start"); `paper/sections/21_middle_records.tex`, `lem:record:class-three`(ii),(iii).

BA's `MiddleBlockRows i` (block level, kind C) asks, on every block of piece `i`, at every middle
value `ξ ∈ supp ν`, for `‖T_F^ξ - J‖ ≤ f_j r` and `‖T_E^ξ - J‖ ≤ h_j r`
(`j = 2, 1`, `r = b^{-1/2}`).
Here it is **proved** from per-prime statements, as the paper proves it:

* `objSplit`, `block_isProd3`: the block laws of three objects are products over the primes of
  the one-prime laws `primeLaw p G` (`λ_p(G)` as a law of objects);
* `RowPrimeCert Λ p … ρF ρE R` (**the per-prime input**, "One prime"): at the prime `p` and
  every `ξ`, the conditional maximal correlations of the outer objects given `y₁ = ξ` are at most
  `ρF p^{-1/2}` (under `F`, relative to its actual marginals) and `ρE p^{-1/2}` (under `E`)
  (`cor:influence-schur`, the bounds `ρ_{F,j}(p)`, `ρ_{E,j}(p)`); and the actual outer marginals
  under `F` have densities in `[R⁻¹, R]` relative to `ν^ξ` (`lem:record:class-three`(iii)). The
  third per-prime fact of the paper, that the middle object has the same law under `F` and `E`,
  is a hypothesis `hmid` here and is proved in `MiddleLaw.lean`;
* **`blockRows_of_primeCerts`** ("The block"): the block rows from the per-prime certificates,
  through `rows_of_product` (`lem:row-comparison`(a),(c), Peyre);
* `RowGate` and **`layerRows`** ("Evaluation at the piece start", `block_eval`): one layer set of
  the block rows at the recorded constants. The piece certificate is in `MiddleCert.lean`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockRows

open Sarkozy Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.Cuts Sarkozy.Peyre
  Sarkozy.BlockSpecPaper Sarkozy.BlockInputs

/-! ## The block laws as products over the primes -/

section Split

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The coordinates of an object of a block: `x ↦ (x_{·,p})_p`. -/
def objSplit (Λ : Type) : (Λ → BlockLabel pr) ≃ ∀ i, Λ → ZMod (pr i) where
  toFun x i l := x l i
  invFun z l i := z i l
  left_inv _ := rfl
  right_inv _ := rfl

/-- The one-prime law `λ_p(G)` of three objects, as a law of objects. -/
noncomputable abbrev primeLaw {Λ : Type} [Fintype Λ] [DecidableEq Λ] (p : ℕ) [Fact p.Prime]
    (G : OrientedGraph (Fin 3 × Λ)) (hne : (injLabellings (ZMod p) G).Nonempty) :
    FiniteLaw (Fin 3 → Λ → ZMod p) :=
  objLaw (graphLaw G hne)

/-- **The block law of three objects is the product of the one-prime laws.** -/
theorem block_isProd3 {Λ : Type} [Fintype Λ] [DecidableEq Λ] (G : OrientedGraph (Fin 3 × Λ))
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) :
    IsProd3 (objSplit pr Λ) (objLaw (blockGraphLaw pr G hne))
      (fun i => primeLaw (pr i) G (hne i)) := by
  intro ω
  rw [objLaw_weight]
  unfold blockGraphLaw
  rw [tensor_weight]
  refine prod_congr rfl fun i _ => ?_
  rw [objLaw_weight]
  rfl

end Split

/-! ## The per-prime rows -/

/-- **The per-prime rows of `lem:front12:reference`(i)** ("One prime") for the layer set `Λ` at the
prime `p`, with correlation constants `ρF`, `ρE` and density ratio `R`. *Hypothesis* (per prime):
* `corrE`: at every `ξ ∈ supp ν`, the maximal correlation of the outer objects given `y₁ = ξ`
  under the `E` law is at most `ρE p^{-1/2}` (`cor:influence-schur`, `ρ_{E,j}(p)`);
* `corrF`: the same under the `F` law, relative to its actual marginals, at most `ρF p^{-1/2}`
  (`ρ_{F,j}(p)`);
* `densF`: the actual outer marginals given `y₁ = ξ` under the `F` law have densities in
  `[R⁻¹, R]` relative to `ν^ξ` (`lem:record:class-three`(iii)). -/
structure RowPrimeCert (Λ : Type) [Fintype Λ] [DecidableEq Λ] (p : ℕ) [Fact p.Prime]
    (hE : (injLabellings (ZMod p) (matchGraph Λ)).Nonempty)
    (hF : (injLabellings (ZMod p) (foldGraph Λ)).Nonempty) (ρF ρE R : ℝ) : Prop where
  corrE : ∀ ξ, (nuOf (primeLaw p (matchGraph Λ) hE)).weight ξ ≠ 0 →
    maxCorr (condLaw (primeLaw p (matchGraph Λ) hE) ξ) Prod.fst Prod.snd ≤ ρE * (√(p : ℝ))⁻¹
  corrF : ∀ ξ, (nuOf (primeLaw p (matchGraph Λ) hE)).weight ξ ≠ 0 →
    maxCorr (condLaw (primeLaw p (foldGraph Λ) hF) ξ) Prod.fst Prod.snd ≤ ρF * (√(p : ℝ))⁻¹
  densF : ∀ ξ, (nuOf (primeLaw p (matchGraph Λ) hE)).weight ξ ≠ 0 →
    ∃ rL rR : (Λ → ZMod p) → ℝ,
      HasMarginalDensities (nubOf (primeLaw p (matchGraph Λ) hE) ξ)
        (condLaw (primeLaw p (foldGraph Λ) hF) ξ) rL rR ∧
      ∀ x, (R⁻¹ ≤ rL x ∧ rL x ≤ R) ∧ (R⁻¹ ≤ rR x ∧ rR x ≤ R)

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The block rows from the per-prime rows** ("The block"): at every `ξ ∈ supp ν`,
`‖T_F^ξ - J‖ ≤ (∏_p R_p) ρF b^{-1/2} + 2υ + υ²` (`υ = chiAllow R`) and
`‖T_E^ξ - J‖ ≤ ρE b^{-1/2}`, for every `b` at most every prime of the block, given that the middle
laws of `F` and `E` agree at every prime (`hmid`, `MiddleLaw.lean`). -/
theorem blockRows_of_primeCerts {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (hE : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph Λ)).Nonempty)
    (hF : ∀ i, (injLabellings (ZMod (pr i)) (foldGraph Λ)).Nonempty)
    (hmidp : ∀ i ξ, (nuOf (primeLaw (pr i) (foldGraph Λ) (hF i))).weight ξ =
      (nuOf (primeLaw (pr i) (matchGraph Λ) (hE i))).weight ξ)
    {ρF ρE : ℝ} (hρF : 0 ≤ ρF) (hρE : 0 ≤ ρE) (R : ι → ℝ) (hR1 : ∀ i, 1 ≤ R i)
    (hc : ∀ i, RowPrimeCert Λ (pr i) (hE i) (hF i) ρF ρE (R i)) {b : ℕ} (hb0 : 0 < b)
    (hb : ∀ i, b ≤ pr i) (ξ : Λ → BlockLabel pr)
    (hξ : (nuOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE))).weight ξ ≠ 0) :
    NormBound (nubOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE)) ξ)
        (kernelOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE))
          (objLaw (blockGraphLaw pr (foldGraph Λ) hF)) ξ)
        ((∏ i, R i) * (ρF * (√(b : ℝ))⁻¹) + 2 * chiAllow R + chiAllow R ^ 2) ∧
      NormBound (nubOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE)) ξ)
        (kernelOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE))
          (objLaw (blockGraphLaw pr (matchGraph Λ) hE)) ξ) (ρE * (√(b : ℝ))⁻¹) := by
  have hPE := block_isProd3 pr (matchGraph Λ) hE
  have hPF := block_isProd3 pr (foldGraph Λ) hF
  have hexch := objLaw_match_exch pr hE
  have hS : PartVLaws.GamSupported (objLaw (blockGraphLaw pr (matchGraph Λ) hE))
      (objLaw (blockGraphLaw pr (foldGraph Λ) hF)) :=
    PartVLaws.gamSupported_of_support _ _ (hexch (Equiv.swap 0 2)) (objLaw_fold_supp pr hF hE)
  have hξi := nu_prod_ne_zero hPE hξ
  have hmid : (nuOf (objLaw (blockGraphLaw pr (foldGraph Λ) hF))).weight ξ =
      (nuOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE))).weight ξ := by
    rw [nu_prod hPF, nu_prod hPE]
    exact prod_congr rfl fun i _ => hmidp i _
  have hξF : (nuOf (objLaw (blockGraphLaw pr (foldGraph Λ) hF))).weight ξ ≠ 0 := by
    rw [hmid]
    exact hξ
  have hsb : ∀ i, (√(pr i : ℝ))⁻¹ ≤ (√(b : ℝ))⁻¹ := fun i =>
    inv_anti₀ (Real.sqrt_pos.mpr (by exact_mod_cast hb0))
      (Real.sqrt_le_sqrt (by exact_mod_cast hb i))
  have hsb0 : 0 ≤ (√(b : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  constructor
  · choose rL rR hr hbd using fun i => (hc i).densF _ (hξi i)
    refine normBound_of_condLaw _ _ hS hξ hmid fun Φ Ψ => ?_
    exact rows_of_product (objSplit pr Λ) _ _
      (fun i => nubOf (primeLaw (pr i) (matchGraph Λ) (hE i)) (objSplit pr Λ ξ i))
      (fun i => condLaw (primeLaw (pr i) (foldGraph Λ) (hF i)) (objSplit pr Λ ξ i))
      (nub_prod hPE hξ) (condLaw_prod hPF hξF) rL rR hr R hR1 (fun i y => (hbd i y).1)
      (fun i y => (hbd i y).2) (mul_nonneg hρF hsb0)
      (fun i => ((hc i).corrF _ (hξi i)).trans (mul_le_mul_of_nonneg_left (hsb i) hρF)) Φ Ψ
  · refine normBound_of_condLaw _ _ (PartVLaws.gamSupported_self _ (hexch (Equiv.swap 0 2))) hξ
      rfl fun Φ Ψ => ?_
    have hρC : maxCorr (condLaw (objLaw (blockGraphLaw pr (matchGraph Λ) hE)) ξ) Prod.fst
        Prod.snd ≤ ρE * (√(b : ℝ))⁻¹ :=
      maxCorr_split_le (objSplit pr Λ) _
        (fun i => condLaw (primeLaw (pr i) (matchGraph Λ) (hE i)) (objSplit pr Λ ξ i))
        (condLaw_prod hPE hξ) (mul_nonneg hρE hsb0)
        fun i => ((hc i).corrE _ (hξi i)).trans (mul_le_mul_of_nonneg_left (hsb i) hρE)
    exact exact_rows _ _ (condLaw_exact _ hexch hξ) hρC (mul_nonneg hρE hsb0) Φ Ψ

/-- **The row gate at the piece start** (`lem:front12:reference`, the row constants):
`R(X)^n ρF + (2υ + υ²) X^{1/2} ≤ f` and `ρE ≤ h`, `υ = (e^{n(R(X)-1)²} - 1)^{1/2}`. -/
def RowGate (X n RX ρF ρE f h : ℝ) : Prop :=
  RX ^ n * ρF + (2 * upsAllow n RX + upsAllow n RX ^ 2) * √X ≤ f ∧ ρE ≤ h

/-- **One layer set of the block rows at the recorded constants** ("The block" and "Evaluation at
the piece start"): if the ratio `R` has the majorant properties on `[X, ∞)`, the gate holds at `X`,
and every prime of the block, at least `b ≥ X` and at most `n` in number, has the per-prime rows
with the ratio `R(p)`, then `‖T_F^ξ - J‖ ≤ f b^{-1/2}` and `‖T_E^ξ - J‖ ≤ h b^{-1/2}`. -/
theorem layerRows {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (hE : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph Λ)).Nonempty)
    (hF : ∀ i, (injLabellings (ZMod (pr i)) (foldGraph Λ)).Nonempty)
    (hmidp : ∀ i ξ, (nuOf (primeLaw (pr i) (foldGraph Λ) (hF i))).weight ξ =
      (nuOf (primeLaw (pr i) (matchGraph Λ) (hE i))).weight ξ)
    {Rf : ℝ → ℝ} {X n ρF ρE f h : ℝ} (hX : 0 < X) (hmono : RatioMono Rf X)
    (hgate : RowGate X n (Rf X) ρF ρE f h) (hρF : 0 ≤ ρF) (hρE : 0 ≤ ρE)
    (hc : ∀ i, RowPrimeCert Λ (pr i) (hE i) (hF i) ρF ρE (Rf (pr i))) {b : ℕ}
    (hXb : X ≤ b) (hb : ∀ i, b ≤ pr i) (hcard : (Fintype.card ι : ℝ) ≤ n)
    (ξ : Λ → BlockLabel pr)
    (hξ : (nuOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE))).weight ξ ≠ 0) :
    NormBound (nubOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE)) ξ)
        (kernelOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE))
          (objLaw (blockGraphLaw pr (foldGraph Λ) hF)) ξ) (f * (√(b : ℝ))⁻¹) ∧
      NormBound (nubOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE)) ξ)
        (kernelOf (objLaw (blockGraphLaw pr (matchGraph Λ) hE))
          (objLaw (blockGraphLaw pr (matchGraph Λ) hE)) ξ) (h * (√(b : ℝ))⁻¹) := by
  have hb0 : 0 < b := by
    have : (0 : ℝ) < b := lt_of_lt_of_le hX hXb
    exact_mod_cast this
  have hXp : ∀ i, X ≤ (pr i : ℝ) := fun i => hXb.trans (by exact_mod_cast hb i)
  have hR1 : ∀ i, 1 ≤ Rf (pr i) := fun i => (hmono _ (hXp i)).1
  obtain ⟨hF', hE'⟩ := blockRows_of_primeCerts pr hE hF hmidp hρF hρE (fun i => Rf (pr i)) hR1 hc
    hb0 hb ξ hξ
  have hsb0 : 0 ≤ (√(b : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hchi : ∀ i, (Rf (pr i) - 1) ^ 2 * b ≤ (Rf X - 1) ^ 2 * X := fun i =>
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hb i) (sq_nonneg _)).trans
      ((hmono.sq hX.le (hXp i)))
  have hev := block_eval (fun i => Rf (pr i)) hX hXb hcard (hmono X le_rfl).1 hR1
    (fun i => (hmono _ (hXp i)).2.1) hchi hρF
  refine ⟨normBound_le hF' (hev.trans (mul_le_mul_of_nonneg_right hgate.1 hsb0)),
    normBound_le hE' (mul_le_mul_of_nonneg_right hgate.2 hsb0)⟩

end Block

end Sarkozy.BlockRows
