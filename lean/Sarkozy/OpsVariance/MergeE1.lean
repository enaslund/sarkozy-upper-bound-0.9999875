module

public import Sarkozy.OpsVariance.HresFront

@[expose] public section

/-!
# The merge bounds `hMg` from (E1) for the mixed products

`paper/sections/22_variance.tex`, proof of `lem:record:paired-e-joint`(b) ("(E1) bounds the merge
part by `(1 + o(1)) ε_X C_X Y`"); `paper/sections/10_comparison_lemmas.tex`, (E1).

The merged law of an aligned matching class is `⊗_X (Π_{E_s} + ε_𝔅 G_s) ⊗ μ`. Expanding the
tensor product over the subsets `S ⊆ X`, the merge part is
`∑_{S ≠ ∅} (∏_S ε_𝔅) Y[⊗_S G_s ⊗_{X∖S} Π_{E_s} ⊗ μ]`, and `∑_{S ≠ ∅} ∏_S ε_𝔅 = ∏_X (1 + ε_𝔅) − 1`.
So the merge bound `hMg` of `hRes_aligned` follows from (E1) for the mixed products
`⊗_S G ⊗ Π_E ⊗ μ` (positive laws with uniform one-slot marginals in the paper):

* **`energy_merge_le`** (generic): `Y[⊗_X (E + ε G) ⊗ O] − Y[⊗_X E ⊗ O] ≤ (∏_X (1 + ε) − 1) B` if
  every mixed product (a nonempty set of `G` factors inside `X`) has energy `≤ B`;
* `signedIntegral_add_smul`, **`hMg_of_E1`**: the same for `energyX` at the comparison data, in
  the form of `hMg` (`B = (1 + z) C_X Y`, `ε_X ≥ ∏_X (1 + ε_𝔅) − 1`), for merged record laws
  `w_E + ε_𝔅 w_G`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.RecordExpansion Sarkozy.Variance

section Generic

variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

omit [Fintype J] [DecidableEq J] [DecidableEq V] [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] in
theorem diagonalIntegral_sum' {ι : Type} (s : Finset ι)
    (L : ι → ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ) (g : (∀ j, X j) → ℝ) :
    diagonalIntegral (∑ i ∈ s, L i) g = ∑ i ∈ s, diagonalIntegral (L i) g := by
  unfold diagonalIntegral multilinearIntegral
  exact LinearMap.sum_apply s L _

/-- **The merge part of a product, by the subset expansion.** -/
theorem energy_merge_le (O E G : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (ε : J → ℝ)
    (hε : ∀ j, 0 ≤ ε j) (F : (∀ j, X j) → ℝ) {B : ℝ}
    (hB : ∀ f : J → Bool, (∃ j, f j = true) → (∀ j, f j = true → j ∈ Xs) →
      diagonalIntegral (tensorLaw (fun j => if f j then G j else onBlocks Xs E O j)) F ≤ B) :
    diagonalIntegral (tensorLaw (onBlocks Xs (fun j => E j + ε j • G j) O)) F -
        diagonalIntegral (tensorLaw (onBlocks Xs E O)) F ≤
      (∏ j ∈ Xs, (1 + ε j) - 1) * B := by
  set ε' : J → ℝ := fun j => if j ∈ Xs then ε j else 0 with hε'
  have hε'0 : ∀ j, 0 ≤ ε' j := fun j => by
    simp only [hε']
    split_ifs
    · exact hε j
    · exact le_rfl
  set A := onBlocks Xs E O with hA
  have h1 : onBlocks Xs (fun j => E j + ε j • G j) O = fun j => A j + ε' j • G j := by
    funext j
    by_cases hj : j ∈ Xs <;> simp [onBlocks, hA, hε', hj]
  set c : (J → Bool) → ℝ := fun f => ∏ j, (if f j then ε' j else 1) with hc
  set Yf : (J → Bool) → ℝ := fun f =>
    diagonalIntegral (tensorLaw (fun j => if f j then G j else A j)) F with hYf
  have h2 : ∀ f : J → Bool, tensorLaw (fun j => if f j then ε' j • G j else A j) =
      c f • tensorLaw (fun j => if f j then G j else A j) := by
    intro f
    rw [hc, ← tensorLaw_smul]
    congr 1
    funext j
    by_cases hf : f j <;> simp [hf]
  have hexp : diagonalIntegral (tensorLaw (onBlocks Xs (fun j => E j + ε j • G j) O)) F =
      ∑ f : J → Bool, c f * Yf f := by
    rw [h1, tensorLaw_add_eq_sum, diagonalIntegral_sum']
    refine sum_congr rfl fun f _ => ?_
    rw [h2 f]
    rfl
  have hc0 : ∀ f, 0 ≤ c f := fun f => prod_nonneg fun j _ => by
    split_ifs
    · exact hε'0 j
    · exact zero_le_one
  set f₀ : J → Bool := fun _ => false
  have hcf₀ : c f₀ = 1 := by simp [hc, f₀]
  have hYf₀ : Yf f₀ = diagonalIntegral (tensorLaw A) F := by simp [hYf, f₀]
  have hsplit : ∑ f : J → Bool, c f * Yf f = Yf f₀ + ∑ f ∈ univ.erase f₀, c f * Yf f := by
    rw [← add_sum_erase _ _ (mem_univ f₀), hcf₀, one_mul]
  have hterm : ∀ f ∈ univ.erase f₀, c f * Yf f ≤ c f * B := by
    intro f hf
    have hne : ∃ j, f j = true := by
      by_contra hcon
      push Not at hcon
      apply (mem_erase.mp hf).1
      funext j
      simpa [f₀] using hcon j
    by_cases hin : ∀ j, f j = true → j ∈ Xs
    · exact mul_le_mul_of_nonneg_left (hB f hne hin) (hc0 f)
    · push Not at hin
      obtain ⟨j, hfj, hj⟩ := hin
      have : c f = 0 := by
        apply prod_eq_zero (mem_univ j)
        simp [hfj, hε', hj]
      rw [this, zero_mul, zero_mul]
  have hsumc : ∑ f : J → Bool, c f = ∏ j ∈ Xs, (1 + ε j) := by
    have e : ∑ f : J → Bool, c f = ∏ j, (1 + ε' j) := by
      rw [hc]
      have := (Fintype.prod_sum (fun (j : J) (b : Bool) => if b then ε' j else (1 : ℝ))).symm
      rw [this]
      refine prod_congr rfl fun j _ => ?_
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.false_eq_true]
      ring
    rw [e, ← prod_subset (subset_univ Xs)]
    · exact prod_congr rfl fun j hj => by simp [hε', hj]
    · intro j _ hj
      simp [hε', hj]
  have hsumc' : ∑ f ∈ univ.erase f₀, c f = ∏ j ∈ Xs, (1 + ε j) - 1 := by
    rw [← hsumc, ← add_sum_erase _ _ (mem_univ f₀), hcf₀]
    ring
  rw [hexp, hsplit, hYf₀, add_sub_cancel_left, ← hsumc', sum_mul]
  exact sum_le_sum hterm

end Generic

section Data

open Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.TheoremC

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

theorem signedIntegral_add_smul {Ω : Type} [Fintype Ω] (w₁ w₂ : Ω → ℝ) (c : ℝ) :
    signedIntegral (fun z => w₁ z + c * w₂ z) = signedIntegral w₁ + c • signedIntegral w₂ := by
  apply LinearMap.ext
  intro f
  simp only [signedIntegral, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, mul_sum]
  congr 1
  exact sum_congr rfl fun z _ => by ring

omit [DecidableEq P] in
/-- **The merge bound `hMg` from (E1) for the mixed products** (proof of
`lem:record:paired-e-joint`(b)): if every product with `G` on a nonempty `S ⊆ X`, `E` on `X ∖ S`
and `μ` outside has energy `≤ (1 + z) C_X Y`, then the merged product exceeds `⊗_X E ⊗ μ` by at most
`(1 + z) ε_X C_X Y`, `ε_X ≥ ∏_X (1 + ε_𝔅) − 1`. -/
theorem hMg_of_E1 {L : ℕ} {A : Finset ℤ} (X : Finset (BlockAtom Bk J L))
    (wE wG : ∀ b : BlockAtom Bk J L, (Slot → BlockLabel m₀ blk p L b) → ℝ)
    (ε : BlockAtom Bk J L → ℝ) (hε : ∀ b, 0 ≤ ε b) {CX z εX : ℝ}
    (hB0 : 0 ≤ (1 + z) * CX * D.Y L A) (hεX : ∏ b ∈ X, (1 + ε b) - 1 ≤ εX)
    (hE1 : ∀ f : BlockAtom Bk J L → Bool, (∃ b, f b = true) → (∀ b, f b = true → b ∈ X) →
      diagonalIntegral (tensorLaw (fun b => if f b then signedIntegral (wG b) else
        onBlocks X (fun b => signedIntegral (wE b)) (D.R.law p L) b)) (blockLift m₀ blk p L A) ≤
        (1 + z) * CX * D.Y L A) :
    energyX D L A X (fun b x => wE b x + ε b * wG b x) - energyX D L A X wE ≤
      (1 + z) * εX * CX * D.Y L A := by
  unfold energyX
  have e : (fun b => signedIntegral (fun x => wE b x + ε b * wG b x)) =
      fun b => signedIntegral (wE b) + ε b • signedIntegral (wG b) :=
    funext fun b => signedIntegral_add_smul (wE b) (wG b) (ε b)
  rw [e]
  have hm := energy_merge_le (D.R.law p L) (fun b => signedIntegral (wE b))
    (fun b => signedIntegral (wG b)) X ε hε (blockLift m₀ blk p L A) hE1
  calc _ ≤ (∏ b ∈ X, (1 + ε b) - 1) * ((1 + z) * CX * D.Y L A) := hm
    _ ≤ εX * ((1 + z) * CX * D.Y L A) := mul_le_mul_of_nonneg_right hεX hB0
    _ = (1 + z) * εX * CX * D.Y L A := by ring

end Data

end Sarkozy.OpsVariance
