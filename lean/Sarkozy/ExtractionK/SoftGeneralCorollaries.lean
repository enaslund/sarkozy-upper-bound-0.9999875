module

public import Sarkozy.ExtractionK.SoftGeneral
public import Sarkozy.ExtractionK.Leaf
public import Sarkozy.ExtractionK.Compressed

@[expose] public section

/-!
# Soft cross factors, all coefficients: the corollaries (`cor:soft-kernels`(a))

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(a) for every `D_e ∈ [-1, 1]` (`Dsk`), from
`sk_soft_extraction_g` (`SoftGeneral.lean`): the corollaries of `Leaf.lean` and `Compressed.lean`
restated for the soft class operators and the soft nonstar part, with the same proofs.

* `lem:matching:extractionk` over `𝔽_p` with no condition: `sk_soft_extraction_zmod`;
* `cor:extraction-leaf`(a): `sk_soft_extraction_leaf_g` (given an integer `ν` with `χ(ν) = -1`),
  `sk_soft_extraction_leaf_twoCycles_g`, `sk_soft_extraction_leaf_acyclic_g` (over `𝔽_p`, `p` odd;
  `ν` from `sk_exists_nonsquare_int`, so no condition on `D` beyond `|D_e| ≤ 1`);
* `cor:extraction-leaf`(b): `sk_soft_extraction_leaf_partition_g`,
  `sk_soft_extraction_leaf_partition_grouped_g`;
* `cor:extraction-compressed`: `sk_soft_extraction_compressed_class_g`,
  `sk_soft_extraction_compressed_buckets_g` (given `ν`), `sk_soft_extraction_compressed_class_two_g`,
  `sk_soft_extraction_compressed_buckets_two_g` (over `𝔽_p`).

The four-cycle bound (`cor:dl:normalized`(a)) is the hypothesis `FourCycleBound p` where
`c_ker = 2^β` is used, as in `Leaf.lean` and `Compressed.lean`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SkGCorF0

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence (OpBound)

/-- **`cor:soft-kernels`(a) for `cor:extraction-leaf`(a), all coefficients `D_e ∈ [-1, 1]`**
(given a non-square integer `ν`). -/
theorem sk_soft_extraction_leaf_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w))
      (rectKer ς P (witV w) (witW w)) (cker * Real.sqrt (Fintype.card F) ^ k))
    (Dsk : U × U → ℝ) (hDsk : ∀ e, |Dsk e| ≤ 1)
    (ν : ℤ) (hν : quadraticChar F (ν : F) = -1)
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          leafProd G ς (Fintype.card F) n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G (Fintype.card F) n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine (sk_soft_extraction_g hW G ς hς hanti hne hn hehat hehat1 Ex P A hEx hcls w hw Cx Cz hcov
    ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker Dsk hDsk ν hν f h).trans ?_
  -- the cover condition for the free pairs
  have hFr' : ∀ e ∈ Ex \ (P ∪ A), e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (mem_sdiff.mp he).1 hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hPF := recordFactor_le_leafProd G ς hanti hehat hehat1 (Ex \ (P ∪ A))
    (fun e he => hEx e (mem_sdiff.mp he).1) (witV w) (witW w) Cx Cz
    (fun e he h1 => (hFr' e he).resolve_left h1) (fun e he h2 => (hFr' e he).resolve_right h2)
    ordX ordZ
  have hR : 1 ≤ rowsR G (Fintype.card F) n univ ^ 2 := by
    have := rowsR_univ_ge_one G (q := (Fintype.card F : ℝ)) (n := n)
      (fun i => lt_of_le_of_lt (hehat i) hehat1)
    nlinarith
  have h1e : 0 < 1 - ehat := by linarith
  have hsq : Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
        recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) ≤
      Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
        leafProd G ς (Fintype.card F) n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G (Fintype.card F) n univ ^ 2 := by
    refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hPF (by positivity))).trans ?_
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _) hR
  set X := cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k / (1 - ehat) ^ k *
    Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
    Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) with hX
  have hX0 : 0 ≤ X := by positivity
  calc cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
        (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))
      = X * Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) := by
        rw [hX]
        ring
    _ ≤ X * (Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          leafProd G ς (Fintype.card F) n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
          rowsR G (Fintype.card F) n univ ^ 2) := mul_le_mul_of_nonneg_left hsq hX0
    _ = _ := by
        rw [hX]
        ring

end SkGCorF0

section SkGCorP1

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence (OpBound)

/-- **`cor:soft-kernels`(a) for `cor:extraction-leaf`(a) over `𝔽_p`, `c_ker = 2^β`, all
coefficients `D_e ∈ [-1, 1]`.** -/
theorem sk_soft_extraction_leaf_twoCycles_g (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p)
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) p n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w)
    (hcard : ∀ i, (twoCycleComponent (witnessIdx P w) i).card ≤ 2)
    (Cx Cz : Finset U) (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ)
    (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    (Dsk : U × U → ℝ) (hDsk : ∀ e, |Dsk e| ≤ 1)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      (Real.sqrt p)⁻¹ ^ k *
        Real.sqrt (2 ^ (recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ +
            2 * twoCycleCount (witnessIdx P w)) *
          leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G p n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  have hςP := sign_pm_of_ne_zero hς (fun e he => hEx e (hcls.1 he))
  have hk := IsWitness.rectKer_opBound_twoCycles hw hp2 h4 ς hςP hcard
  have hker : Sarkozy.Influence.OpBound (injTuples (ZMod p) (witV w))
      (injTuples (ZMod p) (witW w)) (rectKer ς P (witV w) (witW w))
      (2 ^ twoCycleCount (witnessIdx P w) * Real.sqrt (Fintype.card (ZMod p)) ^ k) := by
    rw [ZMod.card]
    exact hk
  have hehat' : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat := by
    rw [ZMod.card]
    exact hehat
  have hL := sk_soft_extraction_leaf_g hW G ς hς hanti hne hn hehat' hehat1 Ex P A hEx hcls w hw Cx Cz
    hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 (by positivity) hker Dsk hDsk ν hν f h
  rw [ZMod.card] at hL
  refine hL.trans (le_of_eq ?_)
  have e : (2 : ℝ) ^ (recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ +
        2 * twoCycleCount (witnessIdx P w)) *
        leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ =
      ((2 : ℝ) ^ twoCycleCount (witnessIdx P w)) ^ 2 *
        (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) := by
    rw [pow_add, pow_mul']
    ring
  rw [e, Real.sqrt_mul (sq_nonneg ((2 : ℝ) ^ twoCycleCount (witnessIdx P w))),
    Real.sqrt_sq (by positivity)]
  ring

/-- **`cor:soft-kernels`(a) for `cor:extraction-leaf`(a) over `𝔽_p`, acyclic, all coefficients.** -/
theorem sk_soft_extraction_leaf_acyclic_g (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) p n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w)
    (hac : IsAcyclicWitness (witnessIdx P w))
    (Cx Cz : Finset U) (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ)
    (hordX : Function.Injective ordX) (hordZ : Function.Injective ordZ)
    (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    (Dsk : U × U → ℝ) (hDsk : ∀ e, |Dsk e| ≤ 1)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      (Real.sqrt p)⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          leafProd G ς p n ehat (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) *
        rowsR G p n univ ^ 2 / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  have hςP := sign_pm_of_ne_zero hς (fun e he => hEx e (hcls.1 he))
  have hk := IsWitness.rectKer_opBound_acyclic hw hp2 ς hςP hac
  have hker : Sarkozy.Influence.OpBound (injTuples (ZMod p) (witV w))
      (injTuples (ZMod p) (witW w)) (rectKer ς P (witV w) (witW w))
      (1 * Real.sqrt (Fintype.card (ZMod p)) ^ k) := by
    rw [ZMod.card, one_mul]
    exact hk
  have hehat' : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat := by
    rw [ZMod.card]
    exact hehat
  have hL := sk_soft_extraction_leaf_g hW G ς hς hanti hne hn hehat' hehat1 Ex P A hEx hcls w hw Cx Cz
    hcov ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 zero_le_one hker Dsk hDsk ν hν f h
  rw [ZMod.card, one_mul] at hL
  exact hL

/-- **`cor:soft-kernels`(a) for `cor:extraction-leaf`(b), all coefficients `D_e ∈ [-1, 1]`**: the
soft nonstar part `∑_{S nonstar} D_S T_S` over `𝔽_p`. -/
theorem sk_soft_extraction_leaf_partition_g (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (Ex : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (hS1 : leafEhat G Q n < 1) (Dsk : U × U → ℝ) (hDsk : ∀ e, |Dsk e| ≤ 1)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      (∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G ς Q n Ex c (rec c)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  set μ := graphLaw G hne
  -- the nonstar sum over the partition
  have hsplit : ∀ x x' : U → ZMod p, ∑ S ∈ nonstars Ex, ∏ e ∈ S, (Dsk e * chiPair ς e x x') =
      ∑ c ∈ 𝔓, ∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (Dsk e * chiPair ς e x x') := by
    intro x x'
    rw [← h𝔓.2.2, sum_biUnion h𝔓.2.1]
  have hlin : μ.expect (fun x => f x * μ.expect (fun x' =>
      (∑ S ∈ nonstars Ex, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x')) =
      ∑ c ∈ 𝔓, μ.expect (fun x => f x * μ.expect (fun x' =>
        (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x')) := by
    simp_rw [hsplit, sum_mul]
    rw [← leaf_expect_finset_sum]
    refine μ.expect_congr fun x => ?_
    rw [leaf_expect_finset_sum, mul_sum]
  rw [hlin]
  have hpQ : (0 : ℝ) < p := lt_of_lt_of_le hQ hQp
  have hp1 : leafEhat G p n < 1 := lt_of_le_of_lt (leafEhat_anti G hQ hQp) hS1
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [sum_mul, sum_mul]
  refine sum_le_sum fun c hc => ?_
  have hv := hrec c hc
  have hcls : IsClassDatum Ex (c.1, c.2) := h𝔓.1 c hc
  have hb := sk_soft_extraction_leaf_twoCycles_g hW hp2 h4 G ς hς hanti hne hn
    (coarseError_le_leafEhat G p n) hp1 Ex c.1 c.2 hEx hcls (rec c).w hv.witness hv.twoCycles
    (rec c).Cx (rec c).Cz hv.cover (rec c).ordX (rec c).ordZ hv.injX hv.injZ hv.segX0 hv.segZ0
    hv.segX1 hv.segZ1 Dsk hDsk f h
  refine hb.trans ?_
  have hco := leafCoef_anti G ς hQ hQp hS1 Ex c (rec c)
  unfold leafCoef at hco
  have hX : 0 ≤ (Real.sqrt p)⁻¹ ^ (rec c).k * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
      Real.sqrt (μ.expect (fun x => h x ^ 2)) := by positivity
  calc (Real.sqrt p)⁻¹ ^ (rec c).k *
        Real.sqrt (2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).ordX (rec c).ordZ + 2 * twoCycleCount (witnessIdx c.1 (rec c).w)) *
          leafProd G ς p n (leafEhat G p n) (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).Cx (rec c).Cz (rec c).ordX (rec c).ordZ) *
        rowsR G p n univ ^ 2 / (1 - leafEhat G p n) ^ (rec c).k *
        Real.sqrt (μ.expect (fun x => f x ^ 2)) * Real.sqrt (μ.expect (fun x => h x ^ 2))
      = ((Real.sqrt p)⁻¹ ^ (rec c).k * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
          Real.sqrt (μ.expect (fun x => h x ^ 2))) *
        (Real.sqrt (2 ^ (recordExp G (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).ordX (rec c).ordZ + 2 * twoCycleCount (witnessIdx c.1 (rec c).w)) *
          leafProd G ς p n (leafEhat G p n) (Ex \ (c.1 ∪ c.2)) (witV (rec c).w) (witW (rec c).w)
            (rec c).Cx (rec c).Cz (rec c).ordX (rec c).ordZ) *
        rowsR G p n univ ^ 2 / (1 - leafEhat G p n) ^ (rec c).k) := by ring
    _ ≤ ((Real.sqrt p)⁻¹ ^ (rec c).k * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
          Real.sqrt (μ.expect (fun x => h x ^ 2))) * leafCoef G ς Q n Ex c (rec c) :=
        mul_le_mul_of_nonneg_left hco hX
    _ = _ := by ring

/-- **`cor:soft-kernels`(a) for `cor:extraction-leaf`(b), grouped, all coefficients.** -/
theorem sk_soft_extraction_leaf_partition_grouped_g (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (Ex : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (rec : Finset (U × U) × Finset (U × U) → LeafRecordData U)
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex c) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (hS1 : leafEhat G Q n < 1) (Dsk : U × U → ℝ) (hDsk : ∀ e, |Dsk e| ≤ 1)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      (∑ k ∈ 𝔓.image (fun c => (rec c).k),
          (∑ c ∈ 𝔓.filter (fun c => (rec c).k = k), leafCoef G ς Q n Ex c (rec c)) *
            (Real.sqrt p)⁻¹ ^ k) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine (sk_soft_extraction_leaf_partition_g hW hp2 h4 G ς hς hanti hne hn Ex hEx 𝔓 h𝔓 rec hrec hQ hQp
    hS1 Dsk hDsk f h).trans (le_of_eq ?_)
  congr 2
  rw [← sum_fiberwise_of_maps_to (g := fun c => (rec c).k) (t := 𝔓.image (fun c => (rec c).k))
    (fun c hc => mem_image_of_mem _ hc)]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun c hc => ?_
  rw [(mem_filter.mp hc).2]
  ring

end SkGCorP1

section SkGCorF2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence (OpBound)

/-- **`cor:soft-kernels`(a) for `cor:extraction-compressed`, the class bound, all coefficients**
(given a non-square integer `ν`). -/
theorem sk_soft_extraction_compressed_class_g (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : OpBound (injTuples F (witV w)) (injTuples F (witW w))
      (rectKer ς P (witV w) (witW w)) (cker * Real.sqrt (Fintype.card F) ^ k))
    (Dsk : U × U → ℝ) (hDsk : ∀ e, |Dsk e| ≤ 1)
    (ν : ℤ) (hν : quadraticChar F (ν : F) = -1)
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        cmpLambda0 G ς (Fintype.card F) n ehat k *
        Real.exp (cmpGamma (Fintype.card F) n Δ *
          cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  have hsym : ∀ a b, ς a b ≠ 0 ↔ ς b a ≠ 0 := fun a b => by
    rw [hanti a b, neg_ne_zero]
  have hVC : ∀ u ∈ witV w, u ∉ Cx := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.fst_not_mem i
  have hWC : ∀ u ∈ witW w, u ∉ Cz := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.snd_not_mem i
  obtain ⟨ordX, hiX, hX0, hX1, hX2, hXs⟩ :=
    cmp_exists_order G (witV w) Cx hVC (cmpHx (Ex \ (P ∪ A)))
  obtain ⟨ordZ, hiZ, hZ0, hZ1, hZ2, hZs⟩ :=
    cmp_exists_order G (witW w) Cz hWC (cmpHz (Ex \ (P ∪ A)))
  have hmain := sk_soft_extraction_g hW G ς hς hanti hne hn hehat hehat1 Ex P A hEx hcls w hw Cx Cz
    hcov ordX ordZ hiX hiZ hX0 hZ0 hX1 hZ1 hcker hker Dsk hDsk ν hν f h
  have hex : recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ =
      cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz := by
    unfold recordExp cmpEx
    rw [cmp_sum_ordT G (witV w) Cx ordX hiX hVC (fun a ha v hv => hX0 a ha v (hVC v hv)) hX2,
      cmp_sum_ordT G (witW w) Cz ordZ hiZ hWC (fun a ha v hv => hZ0 a ha v (hWC v hv)) hZ2]
  rw [hex] at hmain
  have he : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n < 1 := fun i =>
    lt_of_le_of_lt (hehat i) hehat1
  have hRF := cmp_recordFactor_le G ς hsym hΔ he (Ex \ (P ∪ A))
    (fun e he' => hEx e (mem_sdiff.mp he').1) (witV w) (witW w) Cx Cz ordX ordZ hXs hZs
  refine hmain.trans ?_
  set X := Real.exp (cmpGamma (Fintype.card F) n Δ *
      cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz +
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * cmpJsp G ς) /
    ∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n) with hXdef
  have hD : 0 < ∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n) :=
    prod_pos fun i _ => by linarith [he i]
  have hXnn : 0 ≤ X := div_nonneg (Real.exp_pos _).le hD.le
  have hsq : Real.sqrt (recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w)
      Cx Cz ordX ordZ) ≤ X := by
    rw [← Real.sqrt_sq hXnn]
    exact Real.sqrt_le_sqrt hRF
  have h1e : 0 < 1 - ehat := by linarith
  have hR : 1 ≤ rowsR G (Fintype.card F) n univ ^ 2 :=
    one_le_pow₀ (cmp_rowsR_ge_one G he)
  have hXL : X / (1 - ehat) ^ k ≤ cmpLambda0 G ς (Fintype.card F) n ehat k *
      Real.exp (cmpGamma (Fintype.card F) n Δ * cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) := by
    unfold cmpLambda0
    rw [hXdef, Real.exp_add, div_div]
    have hpos : 0 < (1 - ehat) ^ k * ∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n) :=
      mul_pos (pow_pos h1e k) hD
    rw [div_mul_eq_mul_div, mul_comm (∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n))]
    apply div_le_div_of_nonneg_right _ hpos.le
    have e1 := Real.exp_pos (cmpGamma (Fintype.card F) n Δ *
      cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz)
    have e2 := Real.exp_pos ((Real.sqrt (Fintype.card F))⁻¹ ^ 2 * cmpJsp G ς)
    nlinarith [mul_pos e1 e2]
  have hcr : 0 ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k := mul_nonneg hcker (by positivity)
  have hE : 0 ≤ Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
      Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by positivity
  rw [Real.sqrt_mul (by positivity)]
  calc cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        (Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
          Real.sqrt (recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w)
            Cx Cz ordX ordZ)) / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))
      = cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
          (Real.sqrt (recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w)
            Cx Cz ordX ordZ) / (1 - ehat) ^ k) *
          (Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
            Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))) := by ring
    _ ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
          (X / (1 - ehat) ^ k) *
          (Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
            Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))) := by
        gcongr
    _ ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
          (cmpLambda0 G ς (Fintype.card F) n ehat k *
            Real.exp (cmpGamma (Fintype.card F) n Δ *
              cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz)) *
          (Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
            Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))) := by
        gcongr
    _ = _ := by ring

/-- **`cor:soft-kernels`(a) for `cor:extraction-compressed`, the buckets, all coefficients.** -/
theorem sk_soft_extraction_compressed_buckets_g (hW : WeilBound F) (G : OrientedGraph U)
    (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hanti : ∀ j k, ς k j = -ς j k) (hne : (injLabellings F G).Nonempty) {n : ℕ}
    (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ) (Ex : Finset (U × U))
    (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex)) {k : ℕ}
    (wit : Finset (U × U) × Finset (U × U) → Fin k → U × U)
    (cx cz : Finset (U × U) × Finset (U × U) → Finset U)
    (ck : Finset (U × U) × Finset (U × U) → ℝ)
    (bucket : Finset (U × U) × Finset (U × U) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hck : ∀ c ∈ 𝔓, 0 ≤ ck c)
    (hker : ∀ c ∈ 𝔓, OpBound (injTuples F (witV (wit c))) (injTuples F (witW (wit c)))
      (rectKer ς c.1 (witV (wit c)) (witW (wit c))) (ck c * Real.sqrt (Fintype.card F) ^ k))
    (hbucket : ∀ c ∈ 𝔓, cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (Dsk : U × U → ℝ) (hDsk : ∀ e, |Dsk e| ≤ 1)
    (ν : ℤ) (hν : quadraticChar F (ν : F) = -1)
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      (Real.sqrt (Fintype.card F))⁻¹ ^ k * cmpLambda0 G ς (Fintype.card F) n ehat k *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
            (cx c) (cz c))) * Real.exp (cmpGamma (Fintype.card F) n Δ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨hdat, hdisj, hunion⟩ := h𝔓
  set μ := graphLaw G hne
  set r := (Real.sqrt (Fintype.card F))⁻¹
  set L := cmpLambda0 G ς (Fintype.card F) n ehat k
  set γ := cmpGamma (Fintype.card F) n Δ
  set Nf := Real.sqrt (μ.expect (fun x => f x ^ 2))
  set Nh := Real.sqrt (μ.expect (fun x => h x ^ 2))
  set exc := fun c : Finset (U × U) × Finset (U × U) =>
    Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c))
  -- the nonstar sum splits over the classes
  have hsplit : ∀ x x' : U → F, (∑ S ∈ nonstars Ex, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) =
      ∑ c ∈ 𝔓, ∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (Dsk e * chiPair ς e x x') := by
    intro x x'
    rw [← hunion, sum_biUnion hdisj]
  have hform : μ.expect (fun x => f x * μ.expect (fun x' =>
      (∑ S ∈ nonstars Ex, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x')) =
      ∑ c ∈ 𝔓, μ.expect (fun x => f x * μ.expect (fun x' =>
        (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x')) := by
    rw [← cmp_expect_sum]
    refine μ.expect_congr fun x => ?_
    rw [← mul_sum, ← cmp_expect_sum]
    congr 1
    refine μ.expect_congr fun x' => ?_
    rw [hsplit, sum_mul]
  rw [hform]
  -- the class bounds
  have hclass : ∀ c ∈ 𝔓, |μ.expect (fun x => f x * μ.expect (fun x' =>
      (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      r ^ k * L * (ck c * exc c * Real.exp (γ * (bucket c * 2 ^ 𝔮))) * Nf * Nh := by
    intro c hc
    have hb := sk_soft_extraction_compressed_class_g hW G ς hς hanti hne hn hehat hehat1 hΔ Ex c.1 c.2 hEx
      (hdat c hc) (wit c) (hwit c hc) (cx c) (cz c) (hcov c hc) (hck c hc) (hker c hc) Dsk hDsk ν hν f h
    refine hb.trans ?_
    have hγ : 0 ≤ γ := cmpGamma_nonneg _ n Δ
    have hexp : Real.exp (γ * cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c)
        (cz c)) ≤ Real.exp (γ * (bucket c * 2 ^ 𝔮)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbucket c hc) hγ)
    have hL : 0 ≤ L := by
      have he : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n < 1 := fun i =>
        lt_of_le_of_lt (hehat i) hehat1
      have hD : 0 < ∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n) :=
        prod_pos fun i _ => by linarith [he i]
      have h1e : 0 < 1 - ehat := by linarith
      simp only [L, cmpLambda0]
      positivity
    have h0 : 0 ≤ ck c * r ^ k * exc c * L := by
      have := hck c hc
      positivity
    have hN : 0 ≤ Nf * Nh := by positivity
    calc ck c * r ^ k * exc c * L *
          Real.exp (γ * cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c)) *
          Nf * Nh
        = (ck c * r ^ k * exc c * L) *
          Real.exp (γ * cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c)) *
          (Nf * Nh) := by ring
      _ ≤ (ck c * r ^ k * exc c * L) * Real.exp (γ * (bucket c * 2 ^ 𝔮)) * (Nf * Nh) := by
          gcongr
      _ = _ := by ring
  calc |∑ c ∈ 𝔓, μ.expect (fun x => f x * μ.expect (fun x' =>
        (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))|
      ≤ ∑ c ∈ 𝔓, r ^ k * L * (ck c * exc c * Real.exp (γ * (bucket c * 2 ^ 𝔮))) * Nf * Nh :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hclass)
    _ = r ^ k * L * (∑ c ∈ 𝔓, ck c * exc c * Real.exp (γ * (bucket c * 2 ^ 𝔮))) * Nf * Nh := by
        rw [mul_sum, sum_mul, sum_mul]
    _ = r ^ k * L * (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * exc c) * Real.exp (γ * (b * 2 ^ 𝔮))) * Nf * Nh := by
        congr 3
        rw [← sum_fiberwise_of_maps_to (fun c hc => mem_image_of_mem bucket hc)]
        refine sum_congr rfl fun b _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun c hc => ?_
        rw [(mem_filter.mp hc).2]

end SkGCorF2

section SkGCorP3

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence (OpBound)

/-- **`cor:soft-kernels`(a) for `cor:extraction-compressed` over `𝔽_p`, size two, all
coefficients.** -/
theorem sk_soft_extraction_compressed_class_two_g (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    (hW : WeilBound (ZMod p)) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat)
    (hehat1 : ehat < 1) {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    (w : Fin 2 → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (Dsk : U × U → ℝ) (hDsk : ∀ e, |Dsk e| ≤ 1)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      2 ^ twoCycleCount (witnessIdx P w) * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
        Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        cmpLambda0 G ς (Fintype.card (ZMod p)) n ehat 2 *
        Real.exp (cmpGamma (Fintype.card (ZMod p)) n Δ *
          cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  have hςP : ∀ e ∈ P, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1 :=
    sign_pm_of_ne_zero hς fun e he => hEx e (hcls.1 he)
  have hker := Sarkozy.ExtractionK.IsWitness.rectKer_opBound_twoCycles hw hp2 h4 ς hςP
    (cmp_component_card_le_two (witnessIdx P w))
  have hker' : OpBound (injTuples (ZMod p) (witV w)) (injTuples (ZMod p) (witW w))
      (rectKer ς P (witV w) (witW w))
      (2 ^ twoCycleCount (witnessIdx P w) * Real.sqrt (Fintype.card (ZMod p)) ^ 2) := by
    rw [ZMod.card]
    exact hker
  exact sk_soft_extraction_compressed_class_g hW G ς hς hanti hne hn hehat hehat1 hΔ Ex P A hEx hcls w hw
    Cx Cz hcov (by positivity) hker' Dsk hDsk ν hν f h

/-- **`cor:soft-kernels`(a) for `cor:extraction-compressed`, the buckets over `𝔽_p`, all
coefficients.** -/
theorem sk_soft_extraction_compressed_buckets_two_g (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    (hW : WeilBound (ZMod p)) (G : OrientedGraph U)
    (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hanti : ∀ j k, ς k j = -ς j k) (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ}
    (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat)
    (hehat1 : ehat < 1) {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ) (Ex : Finset (U × U))
    (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (wit : Finset (U × U) × Finset (U × U) → Fin 2 → U × U)
    (cx cz : Finset (U × U) × Finset (U × U) → Finset U)
    (bucket : Finset (U × U) × Finset (U × U) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hbucket : ∀ c ∈ 𝔓, cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (Dsk : U × U → ℝ) (hDsk : ∀ e, |Dsk e| ≤ 1)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, (Dsk e * chiPair ς e x x')) * h x'))| ≤
      (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
        cmpLambda0 G ς (Fintype.card (ZMod p)) n ehat 2 *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          (2 : ℝ) ^ twoCycleCount (witnessIdx c.1 (wit c)) *
            Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
              (cx c) (cz c))) * Real.exp (cmpGamma (Fintype.card (ZMod p)) n Δ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  refine sk_soft_extraction_compressed_buckets_g hW G ς hς hanti hne hn hehat hehat1 hΔ Ex hEx 𝔓 h𝔓 wit cx
    cz (fun c => (2 : ℝ) ^ twoCycleCount (witnessIdx c.1 (wit c))) bucket 𝔮 hwit hcov
    (fun c _ => by positivity) (fun c hc => ?_) hbucket Dsk hDsk ν hν f h
  have hςP : ∀ e ∈ c.1, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1 :=
    sign_pm_of_ne_zero hς fun e he => hEx e (h𝔓.1 c hc |>.1 he)
  have hker := Sarkozy.ExtractionK.IsWitness.rectKer_opBound_twoCycles (hwit c hc) hp2 h4 ς hςP
    (cmp_component_card_le_two (witnessIdx c.1 (wit c)))
  rw [ZMod.card]
  exact hker

end SkGCorP3

section SkGZMod

variable {p : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`cor:soft-kernels`(a) for `lem:matching:extractionk` over `𝔽_p`, `p` odd, all coefficients
`|D_e| ≤ 1`**: the bound of `grouped_extraction` for `T^D_𝒞 = ∑_{S ∈ 𝒞} D_S T_S`, with no further
condition (the non-square `ν` from `sk_exists_nonsquare_int`). -/
theorem sk_soft_extraction_zmod (hp2 : p ≠ 2) (hW : WeilBound (ZMod p)) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat) (hehat1 : ehat < 1)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (ordX ordZ : U → ℕ) (hordX : Function.Injective ordX)
    (hordZ : Function.Injective ordZ) (hX0 : ∀ a ∈ Cx, ∀ b, b ∉ Cx → ordX a < ordX b)
    (hZ0 : ∀ a ∈ Cz, ∀ b, b ∉ Cz → ordZ a < ordZ b)
    (hX1 : ∀ a, a ∉ univ \ (witV w ∪ Cx) → ∀ b ∈ univ \ (witV w ∪ Cx), ordX a < ordX b)
    (hZ1 : ∀ a, a ∉ univ \ (witW w ∪ Cz) → ∀ b ∈ univ \ (witW w ∪ Cz), ordZ a < ordZ b)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples (ZMod p) (witV w)) (injTuples (ZMod p) (witW w)) (rectKer ς P (witV w) (witW w))
      (cker * Real.sqrt (Fintype.card (ZMod p)) ^ k))
    (D : U × U → ℝ) (hD : ∀ e, |D e| ≤ 1)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x x')) * h x'))| ≤
      cker * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ k *
        Real.sqrt (2 ^ recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ *
          recordFactor G ς (Fintype.card (ZMod p)) n (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz ordX ordZ) /
        (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  exact sk_soft_extraction_g hW G ς hς hanti hne hn hehat hehat1 Ex P A hEx hcls w hw Cx Cz hcov
    ordX ordZ hordX hordZ hX0 hZ0 hX1 hZ1 hcker hker D hD ν hν f h

end SkGZMod

end Sarkozy.ExtractionK
