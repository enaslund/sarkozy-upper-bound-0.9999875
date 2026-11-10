module

public import Sarkozy.ExtractionK.Grouped

@[expose] public section

/-!
# Grouped extraction for spectral data (`lem:matching:extractionk`, `def:spec:data`)

`paper/sections/16_extraction.tex`, `lem:matching:extractionk` in the paper's setting: spectral
data `D` (`def:spec:data`, `Cuts.SpecData`), the half graph `G⁺ = D.halfGraph` on `U⁺`, the
cross signs `ς = D.sgn` (antisymmetric by `lem:spec:elementary`, `sgn_antisymm`), `n = |U⁺|`,
(S1) at `p` (`D.S1` with `e_t = e_t(p, 2n)`), and `ê = e_{Δ⁺}(p, n)`, the classes being classes of
the cross pairs `E_× = D.crossPairs`.

* `grouped_extraction_specData`: the bound of `grouped_extraction` in this setting.
* `ratioTilde_le_rowsR`: `R̃_U ≤ R_full` for an integrated set `U` (insertion degrees are at most
  the full degrees), so `(R̃_{U_x} R̃_{U_z})^{1/2} ≤ R_full`, the remark at the end of the paper's
  proof (the coarser factor `R_full²` used by the certificates is therefore also valid).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section Ratio

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `R̃_S ≤ R_full = ∏_{i ∈ U⁺} (1 + e_{d⁰_i})/(1 - e_{d⁰_i})`: each insertion degree is at most
the full degree, and every factor is at least one. -/
theorem ratioTilde_le_rowsR (G : OrientedGraph U) {q : ℝ} {n : ℕ} (ord : U → ℕ) (S : Finset U)
    (he : ∀ i, coarseError (rowsDeg0 G i) q n < 1) :
    ratioTilde G q n ord S ≤ rowsR G q n univ := by
  unfold ratioTilde rowsR
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfac1 : ∀ i, 1 ≤ (1 + coarseError (rowsDeg0 G i) q n) /
      (1 - coarseError (rowsDeg0 G i) q n) := by
    intro i
    have h0 := coarseError_nonneg (q := q) hn0 (rowsDeg0 G i)
    have h1 := he i
    rw [one_le_div (by linarith)]
    linarith
  calc ∏ u ∈ S, (1 + coarseError (ordT G ord u) q n) / (1 - coarseError (ordT G ord u) q n)
      ≤ ∏ u ∈ S, (1 + coarseError (rowsDeg0 G u) q n) / (1 - coarseError (rowsDeg0 G u) q n) := by
        refine prod_le_prod₀ (fun u _ => ?_) (fun u _ => ?_)
        · have h0 := coarseError_nonneg (q := q) hn0 (ordT G ord u)
          have h1 : coarseError (ordT G ord u) q n ≤ coarseError (rowsDeg0 G u) q n :=
            coarseError_mono hn0 (ordT_le_deg G ord u)
          have h2 := he u
          exact div_nonneg (by linarith) (by linarith)
        · have h0 := coarseError_nonneg (q := q) hn0 (ordT G ord u)
          have h1 : coarseError (ordT G ord u) q n ≤ coarseError (rowsDeg0 G u) q n :=
            coarseError_mono hn0 (ordT_le_deg G ord u)
          have h2 := he u
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith
    _ ≤ ∏ u, (1 + coarseError (rowsDeg0 G u) q n) / (1 - coarseError (rowsDeg0 G u) q n) :=
        prod_le_prod_of_subset_of_one_le₀ (subset_univ S)
          (fun i _ => le_trans zero_le_one (hfac1 i)) fun i _ _ => hfac1 i

end Ratio

section Spec

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:matching:extractionk` for spectral data.** Let `D` be spectral data
(`def:spec:data`) with (S1) at `p` (`D.S1`, `e_t = e_t(p, 2n)`), `𝒞(P, A)` a class of the cross
pairs `E_×` with a record (witness `w` of size `k`, cover `(C_x, C_z)`, orders with the cover
first and the integrated set last), and suppose the rectangle kernel `𝖶` has norm at most
`c_ker r^k` on injective tuples. Then, with `ê = e_{Δ⁺}(p, n)`,
`|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex(𝒞)/2} (∏_v F_v)^{1/2} (1 - ê)^{-k} ‖f‖_μ ‖h‖_μ`
for `μ = λ_p(G⁺)`. Literature input: `WeilBound F` (`thm:weil`(a)). -/
theorem grouped_extraction_specData (hW : WeilBound F) (D : Cuts.SpecData V)
    (hne : (injLabellings F D.halfGraph).Nonempty)
    (hS1 : D.S1 (fun t => coarseError t (Fintype.card F) (2 * D.n)) (Fintype.card F))
    (P A : Finset (D.cut.Half × D.cut.Half)) (hcls : IsClassDatum D.crossPairs (P, A))
    {k : ℕ} (w : Fin k → D.cut.Half × D.cut.Half) (hw : IsWitness D.crossPairs P A w)
    (Cx Cz : Finset D.cut.Half) (hcov : IsCover D.crossPairs P A w Cx Cz)
    (ordX ordZ : D.cut.Half → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w))
      (rectKer D.sgn P (witV w) (witW w)) (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (D.cut.Half → F) → ℝ) :
    |(graphLaw D.halfGraph hne).expect (fun x => f x * (graphLaw D.halfGraph hne).expect
        (fun x' => (∑ S ∈ cls D.crossPairs P A, ∏ e ∈ S, chiPair D.sgn e x x') * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp D.halfGraph (D.crossPairs \ (P ∪ A)) (witV w) (witW w) ordX
            ordZ *
          recordFactor D.halfGraph D.sgn (Fintype.card F) D.n (D.crossPairs \ (P ∪ A)) (witV w)
            (witW w) Cx Cz ordX ordZ) /
        (1 - coarseError D.DeltaPlus (Fintype.card F) D.n) ^ k *
        Real.sqrt ((graphLaw D.halfGraph hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw D.halfGraph hne).expect (fun x => h x ^ 2)) := by
  have hn0 : (0 : ℝ) ≤ D.n := Nat.cast_nonneg _
  have hdeg : ∀ i, rowsDeg0 D.halfGraph i ≤ D.DeltaPlus := fun i => by
    rw [coverRow_rowsDeg0_halfGraph]
    exact Finset.le_sup (f := D.deg0) (mem_univ i)
  have hDP : D.DeltaPlus ≤ D.Delta :=
    Finset.sup_le fun i _ => (Nat.le_add_right _ _).trans (Finset.le_sup (f := D.dk) (mem_univ i))
  have hehat1 : coarseError D.DeltaPlus (Fintype.card F) D.n < 1 :=
    calc coarseError D.DeltaPlus (Fintype.card F) D.n
        ≤ coarseError D.Delta (Fintype.card F) D.n := coarseError_mono hn0 hDP
      _ ≤ coarseError D.Delta (Fintype.card F) (2 * D.n) :=
          coverRow_coarseError_mono_n _ (by linarith)
      _ < 1 := hS1.1
  refine grouped_extraction hW D.halfGraph D.sgn ?_ D.sgn_antisymm hne
    (le_of_eq (Fintype.card_coe _)) (fun i => coarseError_mono hn0 (hdeg i)) hehat1
    D.crossPairs P A (fun e he => (mem_filter.mp he).2) hcls w hw Cx Cz hcov ordX ordZ hordX
    hordZ hX0 hZ0 hX1 hZ1 hcker hker f h
  intro j k
  unfold Cuts.SpecData.sgn
  split_ifs <;> simp

end Spec

end Sarkozy.ExtractionK
