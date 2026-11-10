module

public import Sarkozy.SignedGram.Paper

@[expose] public section

/-!
# Non-vacuity of the new hypotheses (SGA)

The hypotheses left by this package are `PrimeGram` and `MultiBound` at the shift
`σ = r_b · paperSide i / H_𝔅` (`SectorInputs`), about the paper's own records (`oldP`, `compP` at
E1's `paperComponents`). Here:

* `coupling_bound`: for a nonnegative coupling `C` with both marginals `μ`,
  `2 |⟨f, C g⟩| ≤ ‖f‖²_μ + ‖g‖²_μ` (a Markov operator has norm at most one);
* `piKron_coupling`: a Kronecker product of nonnegative couplings is a nonnegative coupling of the
  product weights;
* **`sectorInputs_large`**, **`primeInputs_large`**: for **every** fold components `C` of a
  middle block (in particular the paper's), `SectorInputs pr hne C σ` and `PrimeInputs pr hne C σ`
  hold as soon as `σ ≥ 2 + t` (`t = 127/500`); `centredNorm_one` (a Markov operator is a
  contraction).

So the two hypotheses are satisfiable on the paper's very objects, and they are monotone in `σ`;
their content is that they hold already at the small shift `σ ≈ 2.4 r_b` of the paper, which is
`prop:signed-sides`(i) (the prime Gram from `prop:signed-bounds`(c), `lem:old-f-law`(f) and
`lem:record:direct-gram`; the sector bound from `prop:signed-bounds`(d)). Through
`opGram_of_sectors`, `signedSideGrams_of_opGram` and the density bound, `sectorInputs_large` also
exhibits instances of `OpGram` and of MRG's `SignedSideGrams` at the paper's records (with large
sides).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.SignedGram

open Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.MiddleComparison Sarkozy.MiddleRefinement
open Sarkozy.PartVRecords
open Sarkozy.IndexSupport Sarkozy.Mixing
open Sarkozy.MainFinal2 (tPaper)

section Coupling

variable {B : Type} [Fintype B] [DecidableEq B]

/-- **A nonnegative coupling with both marginals `μ` has form bounded by the norms**:
`2 |f ⬝ (C g)| ≤ f ⬝ (diag μ f) + g ⬝ (diag μ g)`. -/
theorem coupling_bound {μ : B → ℝ} {C : Matrix B B ℝ} (hC : ∀ a b, 0 ≤ C a b)
    (hrow : ∀ a, ∑ b, C a b = μ a) (hcol : ∀ b, ∑ a, C a b = μ b) (f g : B → ℝ) :
    2 * |f ⬝ᵥ (C *ᵥ g)| ≤ f ⬝ᵥ (Matrix.diagonal μ *ᵥ f) + g ⬝ᵥ (Matrix.diagonal μ *ᵥ g) := by
  have h1 : f ⬝ᵥ (C *ᵥ g) = ∑ a, ∑ b, C a b * (f a * g b) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have h2 : f ⬝ᵥ (Matrix.diagonal μ *ᵥ f) + g ⬝ᵥ (Matrix.diagonal μ *ᵥ g) =
      ∑ a, ∑ b, C a b * (f a * f a + g b * g b) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, mul_add, Finset.sum_add_distrib]
    congr 1
    · refine sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_mul, hrow]
      ring
    · rw [Finset.sum_comm]
      refine sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_mul, hcol]
      ring
  rw [h1, h2]
  calc 2 * |∑ a, ∑ b, C a b * (f a * g b)| ≤ 2 * ∑ a, ∑ b, |C a b * (f a * g b)| :=
        mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)) (by norm_num)
    _ = ∑ a, ∑ b, 2 * |C a b * (f a * g b)| := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ a, ∑ b, C a b * (f a * f a + g b * g b) := by
        refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_of_nonneg (hC a b), abs_mul]
        have := two_mul_le_add_sq |f a| |g b|
        rw [sq_abs, sq_abs] at this
        have hC' := hC a b
        nlinarith [mul_le_mul_of_nonneg_left this hC']

omit [DecidableEq B] in
/-- **A Markov operator is a contraction** (`CentredNorm` with `δ = 1`), for a nonnegative coupling
with both marginals `μ ≥ 0`. -/
theorem centredNorm_one {μ : B → ℝ} {C : Matrix B B ℝ} (hC : ∀ a b, 0 ≤ C a b)
    (hμ : ∀ a, 0 ≤ μ a) (hrow : ∀ a, ∑ b, C a b = μ a) (hcol : ∀ b, ∑ a, C a b = μ b) :
    CentredNorm μ C 1 := by
  intro f _
  have hT : ∀ b a, 0 ≤ condM C μ b a := by
    intro b a
    unfold condM
    split_ifs
    · exact hμ a
    · exact div_nonneg (hC b a) (hμ b)
  have hb : ∀ b, μ b * (condM C μ *ᵥ f) b ^ 2 ≤ μ b * ∑ a, condM C μ b a * f a ^ 2 := by
    intro b
    by_cases h0 : μ b = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (hμ b)
      have hs : ∑ a, condM C μ b a = 1 := by
        simp only [condM, h0, ↓reduceIte]
        rw [← Finset.sum_div, hrow b, div_self h0]
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset B)
        (r := fun a => condM C μ b a * f a) (f := fun a => condM C μ b a)
        (g := fun a => condM C μ b a * f a ^ 2) (fun a _ => hT b a)
        (fun a _ => mul_nonneg (hT b a) (sq_nonneg _)) (fun a _ => le_of_eq (by ring))
      rw [hs, one_mul] at hcs
      simpa [Matrix.mulVec, dotProduct] using hcs
  refine (sum_le_sum fun b _ => hb b).trans (le_of_eq ?_)
  simp only [Finset.mul_sum, one_pow, one_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  simp only [← mul_assoc, mul_condM hC hrow]
  rw [← Finset.sum_mul, hcol]

end Coupling

section Matrices

variable {K : Type} [Fintype K] [DecidableEq K] {A : K → Type} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)] {m : ∀ j, A j → ℝ}

omit [∀ j, DecidableEq (A j)] in
/-- **A Kronecker product of couplings is a coupling of the product weights.** -/
theorem piKron_coupling {C : ∀ j, Matrix (A j) (A j) ℝ} (hC : IsCoupling m C) :
    (∀ x, ∑ y, piKron C x y = prodW m x) ∧ ∀ y, ∑ x, piKron C x y = prodW m y := by
  constructor
  · intro x
    simp only [piKron_apply, prodW]
    rw [← Fintype.prod_sum]
    exact prod_congr rfl fun j _ => hC.row j (x j)
  · intro y
    simp only [piKron_apply, prodW]
    rw [← Fintype.prod_sum (fun j a => C j a (y j))]
    exact prod_congr rfl fun j _ => hC.col j (y j)

omit [DecidableEq K] [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] in
theorem piKron_nonneg {C : ∀ j, Matrix (A j) (A j) ℝ} (hC : ∀ j a b, 0 ≤ C j a b) (x y) :
    0 ≤ piKron C x y :=
  prod_nonneg fun j _ => hC j _ _

/-- The form of a signed combination of couplings: `2 |⟨f, ∑ α_c C_c g⟩| ≤ ∑|α_c| (‖f‖² + ‖g‖²)`. -/
theorem comb_bound {B : Type} [Fintype B] [DecidableEq B] {μ : B → ℝ}
    {P : Fin 3 → Matrix B B ℝ} (hP : ∀ c a b, 0 ≤ P c a b) (hrow : ∀ c a, ∑ b, P c a b = μ a)
    (hcol : ∀ c b, ∑ a, P c a b = μ b) (α : Fin 3 → ℝ) (f g : B → ℝ) :
    2 * |f ⬝ᵥ ((∑ c, α c • P c) *ᵥ g)| ≤
      (∑ c, |α c|) * (f ⬝ᵥ (Matrix.diagonal μ *ᵥ f) + g ⬝ᵥ (Matrix.diagonal μ *ᵥ g)) := by
  rw [Matrix.sum_mulVec, dotProduct_sum, Finset.sum_mul]
  calc 2 * |∑ c, f ⬝ᵥ ((α c • P c) *ᵥ g)| ≤ 2 * ∑ c, |f ⬝ᵥ ((α c • P c) *ᵥ g)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by norm_num)
    _ = ∑ c, |α c| * (2 * |f ⬝ᵥ (P c *ᵥ g)|) := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun c _ => ?_
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, abs_mul]
        ring
    _ ≤ _ := sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left (coupling_bound (hP c) (hrow c) (hcol c) f g) (abs_nonneg _)

omit [Fintype K] [DecidableEq K] in
/-- **The prime Gram holds at large shifts** for any nonnegative couplings with marginals `m`. -/
theorem primeGram_large {C₀ : ∀ j, Matrix (A j) (A j) ℝ} {P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ}
    (hC₀ : IsCoupling m C₀) (hP : ∀ c, IsCoupling m (P c)) (hC₀n : ∀ j a b, 0 ≤ C₀ j a b)
    (hPn : ∀ c j a b, 0 ≤ P c j a b) (α : Fin 3 → ℝ) {σ : ℝ} (hσ : 1 + ∑ c, |α c| ≤ σ)
    (hm : ∀ j a, 0 ≤ m j a) (i : K) : PrimeGram m C₀ P α σ σ i := by
  intro f g
  have hN := comb_bound (fun c => hPn c i) (fun c => (hP c).row i) (fun c => (hP c).col i) α f g
  have dF : 0 ≤ f ⬝ᵥ (Matrix.diagonal (m i) *ᵥ f) := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact sum_nonneg fun a _ => by nlinarith [hm i a, mul_self_nonneg (f a)]
  have dG : 0 ≤ g ⬝ᵥ (Matrix.diagonal (m i) *ᵥ g) := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact sum_nonneg fun a _ => by nlinarith [hm i a, mul_self_nonneg (g a)]
  have h1 := neg_abs_le (f ⬝ᵥ (C₀ i *ᵥ f))
  have h2 := neg_abs_le (g ⬝ᵥ (C₀ i *ᵥ g))
  have h3 := neg_abs_le (f ⬝ᵥ ((∑ c, α c • P c i) *ᵥ g))
  have hf := coupling_bound (hC₀n i) (hC₀.row i) (hC₀.col i) f f
  have hg := coupling_bound (hC₀n i) (hC₀.row i) (hC₀.col i) g g
  have hS : 0 ≤ ∑ c, |α c| := sum_nonneg fun c _ => abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hσ dF, mul_le_mul_of_nonneg_right hσ dG]

/-- **The sector bound holds at large shifts** (`a = 1`, `n = ∑|α_c|`). -/
theorem multiBound_large {C₀ : ∀ j, Matrix (A j) (A j) ℝ} {P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ}
    (hC₀ : IsCoupling m C₀) (hP : ∀ c, IsCoupling m (P c)) (hC₀n : ∀ j a b, 0 ≤ C₀ j a b)
    (hPn : ∀ c j a b, 0 ≤ P c j a b) (α : Fin 3 → ℝ) {σ : ℝ} (hσ : 1 + ∑ c, |α c| ≤ σ)
    (l : K → Bool) : MultiBound m (piKron C₀) (∑ c, α c • piKron (P c)) σ l := by
  refine ⟨1, ∑ c, |α c|, zero_le_one, sum_nonneg fun c _ => abs_nonneg _, hσ, fun φ ψ => ⟨?_, ?_⟩⟩
  · have h := coupling_bound (piKron_nonneg hC₀n) (piKron_coupling hC₀).1 (piKron_coupling hC₀).2
      (SP m l *ᵥ φ) (SP m l *ᵥ φ)
    linarith
  · exact comb_bound (fun c => piKron_nonneg (hPn c)) (fun c => (piKron_coupling (hP c)).1)
      (fun c => (piKron_coupling (hP c)).2) α _ _

end Matrices

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]
  (hne : MiddleNonempty pr)

/-- **Non-vacuity of `SectorInputs` on the paper's objects**: for every fold components `C`
(in particular E1's `paperComponents`), the prime Grams and the sector bounds hold at every shift
`σ ≥ 2 + t`, `t = 127/500`. -/
theorem sectorInputs_large (C : FoldComponents pr hne) {σ : ℝ} (hσ : 2 + tPaper ≤ σ) :
    SectorInputs pr hne C σ := by
  have ht : 0 ≤ tPaper := MainFinal2.tPaper_nonneg
  have hs : 1 + ∑ c, |signedCoef tPaper c| ≤ σ := by
    rw [sum_abs_signedCoef ht]
    linarith
  have hC₀n : ∀ j a b, 0 ≤ oldP hne j a b := fun j a b => (K0 (hne.F2 j)).nonneg _
  have hPn : ∀ c j a b, 0 ≤ compP hne C c j a b := fun c j a b => ((C j).law 0 c).nonneg _
  exact ⟨fun i f g _ _ => primeGram_large (oldP_coupling hne) (compP_coupling hne C) hC₀n hPn _ hs
      (mP_nonneg hne) i f g,
    fun l _ => multiBound_large (oldP_coupling hne) (compP_coupling hne C) hC₀n hPn _ hs l⟩

/-- **Non-vacuity of `PrimeInputs` on the paper's objects**: for every fold components `C`, the
centred prime Grams and the prime centred norms (`ρ₀ = ρ₁ = 1`) hold at every `σ ≥ 2 + t`. -/
theorem primeInputs_large (C : FoldComponents pr hne) {σ : ℝ} (hσ : 2 + tPaper ≤ σ) :
    PrimeInputs pr hne C σ := by
  have hS := sectorInputs_large hne C hσ
  have hC₀n : ∀ j a b, 0 ≤ oldP hne j a b := fun j a b => (K0 (hne.F2 j)).nonneg _
  have hPn : ∀ c j a b, 0 ≤ compP hne C c j a b := fun c j a b => ((C j).law 0 c).nonneg _
  refine ⟨hS.1, 1, 1, zero_le_one, le_rfl, zero_le_one, le_rfl, fun j => ?_, fun c j => ?_, ?_⟩
  · exact centredNorm_one (hC₀n j) (mP_nonneg hne j) ((oldP_coupling hne).row j)
      ((oldP_coupling hne).col j)
  · exact centredNorm_one (hPn c j) (mP_nonneg hne j) ((compP_coupling hne C c).row j)
      ((compP_coupling hne C c).col j)
  · linarith

/-- **The whole chain at the paper's records, with large sides**: for reflected fold components
(for instance E1's `paperComponents`), at any frame of the middle block, MRG's
`SignedSideGrams` holds at the sides `d` as soon as `2 + t ≤ r d / H_𝔅`
(`sectorInputs_large`, `opGram_of_sectors`, `densityLe_block`, `signedSideGrams_of_opGram`). -/
theorem signedSideGrams_large (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (h : ClassThreeBlock pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
    (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (b : ℝ)
    (C : FoldComponents pr hne) (hC : Reflected C) {d : ℝ}
    (hd : 2 + tPaper ≤ r * d / Hblock pr) :
    SignedSideGrams (PartVRecords.middleFrame pr hne root W I hr b h)
      (ofFold pr h hne root W I hr b C tPaper MainFinal2.tPaper_nonneg
        MainFinal2.tPaper_le_one).toReplacements d d := by
  have hH := Hblock_pos pr h19
  have hσ : 0 ≤ r * d / Hblock pr := le_trans (by norm_num [MainFinal2.tPaper]) hd
  have hs : 1 + ∑ c, |signedCoef tPaper c| ≤ r * d / Hblock pr := by
    rw [sum_abs_signedCoef MainFinal2.tPaper_nonneg]
    linarith
  have hG := opGram_of_sectors hne C tPaper hσ
    (fun i => primeGram_large (oldP_coupling hne) (compP_coupling hne C)
      (fun j a b => (K0 (hne.F2 j)).nonneg _) (fun c j a b => ((C j).law 0 c).nonneg _) _ hs
      (mP_nonneg hne) i)
    (sectorInputs_large hne C hd).2
  have hHd : Hblock pr * (r * d / Hblock pr) ≤ r * d := by rw [mul_div_cancel₀ _ hH.ne']
  exact signedSideGrams_of_opGram h root W I hr b C hC MainFinal2.tPaper_nonneg
    MainFinal2.tPaper_le_one hσ hσ (densityLe_block pr hne h3 h19) hHd hHd hG

end Block

end Sarkozy.SignedGram
