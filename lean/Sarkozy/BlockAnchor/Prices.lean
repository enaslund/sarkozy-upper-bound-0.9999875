module

public import Sarkozy.BlockFrame.Atoms
public import Sarkozy.CancellationSteps.Paper
public import Sarkozy.Param.Params
public import Sarkozy.Functional.SquareStep

@[expose] public section

/-!
# The selection factors of the paper's prefix atoms (`def:price`)

`paper/sections/09_comparison_theorem.tex`, `def:price`: the selection factor of an atom `𝔟` is
`q_𝔟^{2a}`, `q_𝔟 = ∏_{p ∈ 𝔟} p`, read as `p^{e_p a}` for a prefix atom `{p}` with `e_p` even.

* `coordSel a pp ep i`: the factor of one fixed coordinate `ℤ/p^{e}ℤ` (`p^{2a}` if `e = 1`,
  `p^{e a}` otherwise); `blockSel a pp ep blk β`: the factor of the block `β` of a block
  assignment `blk`, the product over its coordinates. For the paper's atoms (the square-clique
  primes `{p}` with `e_p = 2𝔪`, the middle and upper blocks of class-three primes with `e_p = 1`)
  this is exactly `def:price`.
* `one_le_blockSel`: every factor is `≥ 1` (for `a ≥ 0`), the hypothesis `one_le_selPre` of the
  standing data of `Sarkozy.TheoremCBlock`.
* `blockSel_eq_rpow`, **`blockSel_le_exp`**: a block of primes with `e_p = 1` has factor
  `q_𝔟^{2a} = e^{2a log q_𝔟} ≤ e^{2aL}` when `log q_𝔟 ≤ L` (`lem:record:local-domain`(ii),
  `lem:record:repricing`): it is controlled by the block's own logarithmic length.
* **`prod_blockSel`**: the factors of the blocks multiply to the factor of the merged prefix
  (`blockSel_unit`, the one-block partition of `Sarkozy.PaperFrame`).
* `prod_blockSel_eq_leastSquare`: for blocks of primes with `e_p = 1` and squarefree product `D`,
  the product of the block factors is the square-step price `sq(D)^a` of
  `prop:record:density-structured` (WP-R's gap 2).
* **`six_billion_le_paperMergedSel`**: for the paper's prefix at `a₀` the merged factor is at least
  `6·10⁹` (already the atom `{5}` contributes `5^{2𝔪 a₀} ≥ 5^{14}`). This is the obstruction found
  by D1: in the merged frame every first-stage record at the prefix is charged at least this
  factor.
-/

open Finset

namespace Sarkozy.BlockAnchor

open Sarkozy.BlockFrame

section General

variable {J₀ : Type} [Fintype J₀] {Bk : Type} [Fintype Bk] [DecidableEq Bk]

/-- The selection factor of one fixed coordinate `ℤ/p^{e}ℤ` (`def:price`): `p^{2a}` if `e = 1`,
and `p^{e a}` otherwise (the paper's reading of `q_𝔟^{2a}` for a prefix atom `{p}` with `e_p`
even). -/
noncomputable def coordSel (a : ℝ) (pp ep : J₀ → ℕ) (i : J₀) : ℝ :=
  if ep i = 1 then (pp i : ℝ) ^ (2 * a) else (pp i : ℝ) ^ ((ep i : ℝ) * a)

/-- **The selection factor `q_𝔟^{2a}` of the block `β`** (`def:price`): the product of the
factors of its coordinates. -/
noncomputable def blockSel (a : ℝ) (pp ep : J₀ → ℕ) (blk : J₀ → Bk) (β : Bk) : ℝ :=
  ∏ i : BlockIdx blk β, coordSel a pp ep i.1

omit [Fintype J₀] in
theorem one_le_coordSel {a : ℝ} (ha : 0 ≤ a) {pp ep : J₀ → ℕ} (hpp : ∀ i, 1 ≤ pp i) (i : J₀) :
    1 ≤ coordSel a pp ep i := by
  have h1 : (1 : ℝ) ≤ pp i := by exact_mod_cast hpp i
  unfold coordSel
  split_ifs
  · exact Real.one_le_rpow h1 (by positivity)
  · exact Real.one_le_rpow h1 (by positivity)

omit [Fintype Bk] in
/-- Every block factor is at least `1` (`a ≥ 0`). -/
theorem one_le_blockSel {a : ℝ} (ha : 0 ≤ a) {pp ep : J₀ → ℕ} (hpp : ∀ i, 1 ≤ pp i)
    (blk : J₀ → Bk) (β : Bk) : 1 ≤ blockSel a pp ep blk β :=
  Finset.one_le_prod₀ fun i _ => one_le_coordSel ha hpp i.1

/-- **The block factors multiply to the merged factor**: `∏_β q_β^{2a} = ∏_i (factor of i)`. -/
theorem prod_blockSel (a : ℝ) (pp ep : J₀ → ℕ) (blk : J₀ → Bk) :
    ∏ β, blockSel a pp ep blk β = ∏ i, coordSel a pp ep i :=
  Fintype.prod_fiberwise blk (coordSel a pp ep)

omit [Fintype Bk] [DecidableEq Bk] in
/-- The merged prefix atom of `Sarkozy.PaperFrame` is the one-block partition: its factor is the
product of the factors of all the fixed coordinates. -/
theorem blockSel_unit (a : ℝ) (pp ep : J₀ → ℕ) :
    blockSel a pp ep (fun _ : J₀ => ()) () = ∏ i, coordSel a pp ep i := by
  rw [← prod_blockSel a pp ep (fun _ : J₀ => ())]
  exact (Fintype.prod_unique _).symm

/-- A block factor is at most the merged factor. -/
theorem blockSel_le_prod {a : ℝ} (ha : 0 ≤ a) {pp ep : J₀ → ℕ} (hpp : ∀ i, 1 ≤ pp i)
    (blk : J₀ → Bk) (β : Bk) : blockSel a pp ep blk β ≤ ∏ i, coordSel a pp ep i := by
  rw [← prod_blockSel a pp ep blk, ← Finset.mul_prod_erase univ _ (mem_univ β)]
  have h1 : 1 ≤ ∏ x ∈ univ.erase β, blockSel a pp ep blk x :=
    Finset.one_le_prod₀ fun x _ => one_le_blockSel ha hpp blk x
  have h0 : 0 ≤ blockSel a pp ep blk β := le_trans zero_le_one (one_le_blockSel ha hpp blk β)
  nlinarith

omit [Fintype Bk] in
/-- A block of primes with `e_p = 1`: its factor is `q_𝔟^{2a}`, `q_𝔟 = ∏_{p ∈ 𝔟} p`. -/
theorem blockSel_eq_rpow (a : ℝ) (pp ep : J₀ → ℕ) (blk : J₀ → Bk) (β : Bk)
    (h1 : ∀ i : BlockIdx blk β, ep i.1 = 1) :
    blockSel a pp ep blk β = (∏ i : BlockIdx blk β, (pp i.1 : ℝ)) ^ (2 * a) := by
  unfold blockSel coordSel
  rw [← Real.finsetProd_rpow _ _ (fun i _ => Nat.cast_nonneg _)]
  exact prod_congr rfl fun i _ => by simp only [h1 i, ↓reduceIte]

omit [Fintype Bk] in
/-- **A block's factor is controlled by its logarithmic length** (`lem:record:local-domain`(ii),
`lem:record:repricing`): for a block of primes with `e_p = 1` and `log q_𝔟 ≤ L`,
`q_𝔟^{2a} ≤ e^{2aL}`. -/
theorem blockSel_le_exp {a : ℝ} (ha : 0 ≤ a) {pp ep : J₀ → ℕ} (hpp : ∀ i, 1 ≤ pp i)
    (blk : J₀ → Bk) (β : Bk) (h1 : ∀ i : BlockIdx blk β, ep i.1 = 1) {Lb : ℝ}
    (hL : ∑ i : BlockIdx blk β, Real.log (pp i.1) ≤ Lb) :
    blockSel a pp ep blk β ≤ Real.exp (2 * a * Lb) := by
  have hpos : ∀ i : BlockIdx blk β, (0 : ℝ) < pp i.1 := fun i => by
    have := hpp i.1
    exact_mod_cast (show 0 < pp i.1 by omega)
  have heq : blockSel a pp ep blk β = Real.exp (∑ i : BlockIdx blk β, Real.log (pp i.1) *
      (2 * a)) := by
    unfold blockSel coordSel
    rw [Real.exp_sum]
    exact prod_congr rfl fun i _ => by
      simp only [h1 i, ↓reduceIte]
      rw [Real.rpow_def_of_pos (hpos i)]
  rw [heq, ← Finset.sum_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

omit [Fintype Bk] in
/-- **The block factors are the square-step price** (`prop:record:density-structured`; WP-R's
gap 2, "`selPre` against `sq(D)^a`"): for a set `S` of blocks of primes with `e_p = 1` whose
primes have squarefree product `D`, `∏_{β∈S} q_β^{2a} = sq(D)^a` with `sq(D) = D²` the least
square multiple. The tail analogue is `TheoremCBlock.Structured.selectionFactor_prod_tail`. -/
theorem prod_blockSel_eq_leastSquare (a : ℝ) (pp ep : J₀ → ℕ) (blk : J₀ → Bk) (S : Finset Bk)
    (h1 : ∀ β ∈ S, ∀ i : BlockIdx blk β, ep i.1 = 1)
    (hsq : Squarefree (∏ β ∈ S, ∏ i : BlockIdx blk β, pp i.1)) :
    ∏ β ∈ S, blockSel a pp ep blk β =
      ((Sarkozy.Functional.leastSquare (∏ β ∈ S, ∏ i : BlockIdx blk β, pp i.1) : ℕ) : ℝ) ^ a := by
  rw [Sarkozy.Functional.leastSquare_of_squarefree hsq,
    Finset.prod_congr rfl fun β hβ => blockSel_eq_rpow a pp ep blk β (h1 β hβ),
    Real.finsetProd_rpow _ _ (fun β _ => prod_nonneg fun i _ => Nat.cast_nonneg _)]
  push_cast
  rw [← Real.rpow_natCast,
    ← Real.rpow_mul (prod_nonneg fun β _ => prod_nonneg fun i _ => Nat.cast_nonneg _)]
  norm_num

end General

/-! ## The paper's prefix -/

section Paper

open CancellationSteps

theorem one_le_paperPP (i : PaperJ0) : 1 ≤ paperPP i := (paperJ0_prime i).one_lt.le

/-- **The paper's selection factors of the prefix blocks at `a₀`** (`def:price`), for a block
assignment `blk` of the fixed primes `𝒫₁ ∪ 𝒫₃`: `p^{2𝔪 a₀}` for a square-clique atom `{p}`,
`q_𝔟^{2a₀}` for a block of class-three primes. Irreducible, so that elaboration never unfolds the
product over the `2^{512}`-range of fixed primes (`paperSel_eq` unfolds it). -/
@[irreducible] noncomputable def paperSel {Bk : Type} [DecidableEq Bk] (blk : PaperJ0 → Bk)
    (β : Bk) :
    ℝ :=
  blockSel Param.Params.anchorDecay paperPP paperEP blk β

theorem paperSel_eq {Bk : Type} [DecidableEq Bk] (blk : PaperJ0 → Bk) (β : Bk) :
    paperSel blk β = blockSel Param.Params.anchorDecay paperPP paperEP blk β := by
  unfold paperSel
  rfl

theorem anchorDecay_nonneg : 0 ≤ Param.Params.anchorDecay := by
  norm_num [Param.Params.anchorDecay]

theorem one_le_paperSel {Bk : Type} [DecidableEq Bk] (blk : PaperJ0 → Bk) (β : Bk) :
    1 ≤ paperSel blk β := by
  rw [paperSel_eq]
  exact one_le_blockSel anchorDecay_nonneg one_le_paperPP blk β

/-- The factor of the merged prefix of `Sarkozy.PaperFrame` at `a₀`, by `def:price`: the product
of the factors of all the fixed coordinates. -/
noncomputable def paperMergedSel : ℝ :=
    ∏ i : PaperJ0, coordSel Param.Params.anchorDecay paperPP paperEP i

theorem five_lt_P4 : 5 < PartV.P4 := by
  decide +kernel

theorem five_mem_paperFixedPrimes : 5 ∈ paperFixedPrimes := by
  rw [mem_paperFixedPrimes]
  left
  show Nat.Prime 5 ∧ 5 % 4 = 1 ∧ 5 < PartV.P4
  exact ⟨by norm_num, by norm_num, five_lt_P4⟩

/-- The square-clique atom `{5}`. -/
def paperFive : PaperJ0 := ⟨5, five_mem_paperFixedPrimes⟩

theorem coordSel_paperFive :
    coordSel Param.Params.anchorDecay paperPP paperEP paperFive =
      (5 : ℝ) ^ ((PartV.prefixExponent : ℝ) * Param.Params.anchorDecay) := by
  have hep : paperEP paperFive = PartV.prefixExponent := rfl
  have hne : paperEP paperFive ≠ 1 := by
    rw [hep]
    unfold PartV.prefixExponent PartV.digitPairs
    norm_num
  unfold coordSel
  simp only [hne, ↓reduceIte]
  rw [hep]
  rfl

/-- **The merged prefix factor at `a₀` is at least `6·10⁹`**: the atom `{5}` alone contributes
`5^{2𝔪 a₀} ≥ 5^{14}` (`2𝔪 a₀ = 16384 a₀ ≈ 14.58`). -/
theorem six_billion_le_paperMergedSel : (6000000000 : ℝ) ≤ paperMergedSel := by
  have hfive : (6000000000 : ℝ) ≤ coordSel Param.Params.anchorDecay paperPP paperEP paperFive := by
    rw [coordSel_paperFive]
    have hexp : ((14 : ℕ) : ℝ) ≤ (PartV.prefixExponent : ℝ) * Param.Params.anchorDecay := by
      unfold PartV.prefixExponent PartV.digitPairs Param.Params.anchorDecay
      norm_num
    calc (6000000000 : ℝ) ≤ (5 : ℝ) ^ (14 : ℕ) := by norm_num
      _ = (5 : ℝ) ^ ((14 : ℕ) : ℝ) := (Real.rpow_natCast 5 14).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hle : coordSel Param.Params.anchorDecay paperPP paperEP paperFive ≤ paperMergedSel := by
    unfold paperMergedSel
    rw [← Finset.mul_prod_erase univ _ (mem_univ paperFive)]
    have h1 : 1 ≤ ∏ x ∈ univ.erase paperFive, coordSel Param.Params.anchorDecay paperPP paperEP x :=
      Finset.one_le_prod₀ fun x _ => one_le_coordSel anchorDecay_nonneg one_le_paperPP x
    have h0 := one_le_coordSel anchorDecay_nonneg one_le_paperPP (ep := paperEP) paperFive
    nlinarith
  linarith

end Paper

end Sarkozy.BlockAnchor
