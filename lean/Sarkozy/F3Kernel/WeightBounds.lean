module

public import Sarkozy.F3Kernel.ConcreteNonstarBound

/-!
# Finite upper bounds for the special-value sums

The production tables use the maximum complete row sum. Nonnegativity of the subtracted
minimum-weight sum proves that this coarser bound also bounds the paper's refined factors.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem leafSigma_nonneg {U : Type*} [Fintype U] [DecidableEq U]
    (sgn : U → U → ℤ) (w : U → U → ℝ) (hw : ∀ i j, 0 ≤ w i j) (i : U) (h : ℕ) :
    0 ≤ leafSigma sgn w i h := by
  unfold leafSigma
  split_ifs with hn
  · exact le_inf' hn _ (fun H _ => sum_nonneg fun j _ => hw i j)
  · exact le_rfl

theorem leafS_le_row_bound {U : Type*} [Fintype U] [DecidableEq U]
    (H : OrientedGraph U) (sgn : U → U → ℤ) (w : U → U → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ∑ j, w i j ≤ B) (s : ℕ) :
    leafS H sgn w s ≤ B := by
  unfold leafS
  split_ifs with hn
  · apply sup'_le
    intro i _
    exact (sub_le_self _ (div_nonneg (leafSigma_nonneg sgn w hw i _) (by norm_num))).trans
      (hb i)
  · exact hB

def finiteCU (a b : Fin 36 → Fin 36 → Bool) (i j : Fin 36) : ℕ :=
  #(univ.filter (fun v => a i v = true ∧ b v j = true))

def finiteMg (a b : Fin 36 → Fin 36 → Bool) (j i : Fin 36) : ℕ :=
  #(univ.filter (fun v => a i v = true ∧ b j v = true))

def finiteM (a b : Fin 36 → Fin 36 → Bool) (i j : Fin 36) : ℕ := 2 ^ finiteCU a b i j

def finiteRho (a b : Fin 36 → Fin 36 → Bool) (i j : Fin 36) : ℕ :=
  2 ^ (finiteMg a b j i + finiteCU a b j i)

theorem finiteCU_eq (H : OrientedGraph (Fin 36)) (sgn : Fin 36 → Fin 36 → ℤ)
    {a b : Fin 36 → Fin 36 → Bool} (ha : ∀ i j, a i j = true ↔ graphAdj H i j)
    (hb : ∀ i j, b i j = true ↔ sgn i j ≠ 0) (i j : Fin 36) :
    finiteCU a b i j = rowsCU H sgn i j := by
  simp only [finiteCU, rowsCU, rowsAdj, rowsN, filter_filter, mem_filter, mem_univ, true_and,
    ha, hb, graphAdj, or_comm]

theorem finiteMg_eq (H : OrientedGraph (Fin 36)) (sgn : Fin 36 → Fin 36 → ℤ)
    {a b : Fin 36 → Fin 36 → Bool} (ha : ∀ i j, a i j = true ↔ graphAdj H i j)
    (hb : ∀ i j, b i j = true ↔ sgn i j ≠ 0) (i j : Fin 36) :
    finiteMg a b i j = rowsMg H sgn i j := by
  simp only [finiteMg, rowsMg, rowsAdj, rowsN, filter_filter, mem_filter, mem_univ, true_and,
    ha, hb, graphAdj, or_comm]

theorem finiteM_cast (H : OrientedGraph (Fin 36)) (sgn : Fin 36 → Fin 36 → ℤ)
    {a b : Fin 36 → Fin 36 → Bool} (ha : ∀ i j, a i j = true ↔ graphAdj H i j)
    (hb : ∀ i j, b i j = true ↔ sgn i j ≠ 0) (i j : Fin 36) :
    (finiteM a b i j : ℝ) = weightM H sgn i j := by
  simp only [finiteM, Nat.cast_pow, Nat.cast_ofNat, finiteCU_eq H sgn ha hb, weightM]

theorem finiteRho_cast (H : OrientedGraph (Fin 36)) (sgn : Fin 36 → Fin 36 → ℤ)
    {a b : Fin 36 → Fin 36 → Bool} (ha : ∀ i j, a i j = true ↔ graphAdj H i j)
    (hb : ∀ i j, b i j = true ↔ sgn i j ≠ 0) (i j : Fin 36) :
    (finiteRho a b i j : ℝ) = weightRho H sgn i j := by
  simp only [finiteRho, Nat.cast_pow, Nat.cast_ofNat, finiteCU_eq H sgn ha hb,
    finiteMg_eq H sgn ha hb, weightRho]

theorem leafS_m_le_finite (H : OrientedGraph (Fin 36)) (sgn : Fin 36 → Fin 36 → ℤ)
    {a b : Fin 36 → Fin 36 → Bool} (ha : ∀ i j, a i j = true ↔ graphAdj H i j)
    (hb : ∀ i j, b i j = true ↔ sgn i j ≠ 0) {B : ℕ}
    (hB : ∀ i, ∑ j, finiteM a b i j ≤ B) (s : ℕ) :
    leafS H sgn (weightM H sgn) s ≤ B := by
  apply leafS_le_row_bound H sgn _ (weightM_nonneg H sgn) (Nat.cast_nonneg B)
  intro i
  have hi : ((∑ j, finiteM a b i j : ℕ) : ℝ) ≤ B := by exact_mod_cast hB i
  simpa only [Nat.cast_sum, finiteM_cast H sgn ha hb] using hi

theorem leafS_rho_le_finite (H : OrientedGraph (Fin 36)) (sgn : Fin 36 → Fin 36 → ℤ)
    {a b : Fin 36 → Fin 36 → Bool} (ha : ∀ i j, a i j = true ↔ graphAdj H i j)
    (hb : ∀ i j, b i j = true ↔ sgn i j ≠ 0) {B : ℕ}
    (hB : ∀ i, ∑ j, finiteRho a b i j ≤ B) (s : ℕ) :
    leafS H sgn (weightRho H sgn) s ≤ B := by
  apply leafS_le_row_bound H sgn _ (weightRho_nonneg H sgn) (Nat.cast_nonneg B)
  intro i
  have hi : ((∑ j, finiteRho a b i j : ℕ) : ℝ) ≤ B := by exact_mod_cast hB i
  simpa only [Nat.cast_sum, finiteRho_cast H sgn ha hb] using hi

end Sarkozy.F3Kernel
