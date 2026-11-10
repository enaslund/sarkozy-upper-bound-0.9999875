module

public import Sarkozy.BracketEnergy.Bracket

@[expose] public section

/-!
# The difference `Ñ − Ñ₀` through `lem:sharp-first`

The input `hdiff` of the bracket bundles is `|E_{f ? Q : Ñ} − E_{f ? Q : Ñ₀}| ≤ (R_err + z) K + r₂`.
The paper: "The difference is `lem:sharp-first` with `F` the first-stage atoms outside `X`,
`ρ_𝔟 = Ñ_{0,𝔟}` (variation price `u_𝔟`) and the tagged record differences of (CP2)(b): it is at
most `(e^{U₀} 𝔗(d, v) + o(1)) ‖κ‖ Π_X Y = (R_err + o(1)) ‖κ‖ Π_X Y`, the tag totals over the
first-stage atoms outside `X` being at most those of (CP2) and `𝔗` being nondecreasing."

* `abs_multilinear_sub_le_sharpFirst`: WP-R's `abs_energy_sub_le_sharpFirst` for a multilinear
  energy (any slot inputs, so the revealed inputs are allowed);
* `sharpPiece`: the law of a choice `σ` (a difference `κ'_i − κ_i` at the atoms where `σ` picks
  one, `f ? Q : Ñ₀` elsewhere; no difference at the atoms of `f`);
* **`diff_bound_of_coupled`** (`lem:sharp-first`): `hdiff` from the per-choice bounds
  `|E_σ| ≤ K wt_j(σ) + r_σ` for every nonempty choice and every tag `j` present in it, with the
  sharp prices `d_{𝔟,i}`, the variation prices `v_{𝔟,i}` and `p_𝔟 = u'_𝔟` off `f`. These are
  the per-term coupled sharp bounds (`lem:density:coupled`).
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.RecordExpansion

section Generic

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {I : J → Type*} [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
  {Tag : Type*} [Fintype Tag] [DecidableEq Tag]

/-- **`lem:sharp-first` for a multilinear energy**: if every nonempty choice satisfies, for every
tag `j` present in it, `|E_σ| ≤ K wt_j(σ) + r_σ`, then
`|E_{⊗(A + ∑ D)} − E_{⊗A}| ≤ K e^P 𝔗(d, v) + ∑_σ r_σ`. -/
theorem abs_multilinear_sub_le_sharpFirst (A : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (D : ∀ b, I b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (G : V → (∀ b, X b) → ℝ)
    (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ} {p : J → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (hp : ∀ b, 0 ≤ p b) {K : ℝ}
    (hK : 0 ≤ K) (r : (∀ b, Option (I b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec tag σ j →
      |multilinearIntegral (tensorLaw (fun b => (σ b).elim (A b) (D b))) G| ≤
        K * tagWeight tag d v p j σ + r σ) :
    |multilinearIntegral (tensorLaw (fun b => A b + ∑ i, D b i)) G -
        multilinearIntegral (tensorLaw A) G| ≤
      K * Real.exp (∑ b, p b) * tagSeries (tagTotal tag d) (tagTotal tag v) +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none), r σ := by
  have hsub : multilinearIntegral (tensorLaw (fun b => A b + ∑ i, D b i)) G -
      multilinearIntegral (tensorLaw A) G =
      multilinearIntegral (tensorLaw (fun b => A b + ∑ i, D b i) - tensorLaw A) G := by
    unfold multilinearIntegral
    rw [LinearMap.sub_apply]
  rw [hsub, tensorLaw_add_sum_sub_eq, multilinearIntegral_sum]
  exact abs_sum_le_tagSeries tag hd hv hp hK _ r hterm

end Generic

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.BlockFrame Sarkozy.TheoremCBlock
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.PaperFrame

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The law of a choice `σ` of `lem:sharp-first` for the selected bracket: the difference
`κ'_i − κ_i` where `σ` picks `i` (none at the atoms of `f`), and `f ? Q : Ñ₀` elsewhere. -/
noncomputable def sharpPiece (D : ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, AtomMeasure m₀ blk p L b) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (b : BlockAtom Bk J L) : AtomMeasure m₀ blk p L b :=
  (σ b).elim (if f b then Qb b else D.GB.N₀ L b)
    (fun i => if f b then 0 else D.FS.κ' L b i - D.FS.κ L b i)

section CRT

variable (blk)

omit [DecidableEq P] in
/-- **`hdiff` from the coupled sharp terms** (`lem:sharp-first` for the selected bracket, with any
slot inputs): if every nonempty choice `σ` and every tag `j` present in it satisfy
`|E_σ| ≤ K wt_j(σ) + r_σ` (sharp prices `d`, variation prices `v`, and `p_𝔟 = u'_𝔟` off `f`), then
`|E_{f ? Q : Ñ} − E_{f ? Q : Ñ₀}| ≤ (R_err + z) K + ∑_σ r_σ` for every `z ≥ 0`. -/
theorem diff_bound_of_coupled (D : ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (Qb : ∀ b, AtomMeasure m₀ blk p L b)
    (f : BlockAtom Bk J L → Bool) (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ)
    {K z : ℝ} (hK : 0 ≤ K) (hz : 0 ≤ z) (r : (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      |multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G| ≤
        K * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if f b then 0 else D.GB.uprice L b) j σ + r σ) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N L b)) G -
        multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N₀ L b)) G| ≤
      (D.GB.Rerr + z) * K +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ := by
  set A : ∀ b, ((Slot → ZMod (crtModuli m₀ blk p L b)) → ℝ) →ₗ[ℝ] ℝ :=
    crtLaws blk h0 L fun b => if f b then Qb b else D.GB.N₀ L b
  set Dd : ∀ b, D.FS.Ib L b → ((Slot → ZMod (crtModuli m₀ blk p L b)) → ℝ) →ₗ[ℝ] ℝ :=
    fun b i => pullLaw (crtAtomEquiv blk h0 L b)
      (if f b then 0 else D.FS.κ' L b i - D.FS.κ L b i)
  have hN : crtLaws blk h0 L (fun b => if f b then Qb b else D.GB.N L b) =
      fun b => A b + ∑ i, Dd b i := by
    funext b
    unfold A Dd crtLaws
    apply LinearMap.ext
    intro F
    cases hf : f b
    · simp only [hf, Bool.false_eq_true, ↓reduceIte, pullLaw_apply, LinearMap.add_apply,
        LinearMap.sum_apply, GramBracket.N]
    · simp only [hf, ↓reduceIte, pullLaw_apply, LinearMap.add_apply, LinearMap.sum_apply,
        LinearMap.zero_apply, sum_const_zero, add_zero]
  have hσ : ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      crtLaws blk h0 L (sharpPiece D L Qb f σ) = fun b => (σ b).elim (A b) (Dd b) := by
    intro σ
    funext b
    unfold sharpPiece A Dd crtLaws
    rcases hb : σ b with _ | i
    · simp only [hb, Option.elim]
    · simp only [hb, Option.elim]
  have hp : ∀ b, 0 ≤ (fun b => if f b then 0 else D.GB.uprice L b) b := by
    intro b
    show 0 ≤ if f b then 0 else D.GB.uprice L b
    split_ifs
    · exact le_refl 0
    · exact uprice_nonneg D L b
  have hmain := abs_multilinear_sub_le_sharpFirst A Dd G (D.FS.tag L)
    (fun b i => D.dprice_nonneg L b i) (fun b i => D.vprice_nonneg L b i) hp hK r
    (fun σ hσ0 j hj => by rw [← hσ σ]; exact hterm σ hσ0 j hj)
  rw [← hN] at hmain
  -- the constant: `e^P 𝔗(d, v) ≤ e^{U₀} 𝔗(d_T, v_T) = R_err`
  have hP : ∑ b, (fun b => if f b then 0 else D.GB.uprice L b) b ≤ D.GB.U₀ := by
    refine le_trans (sum_le_sum fun b _ => ?_) (sum_uprice_le D L)
    show (if f b then 0 else D.GB.uprice L b) ≤ D.GB.uprice L b
    split_ifs
    · exact uprice_nonneg D L b
    · exact le_refl _
  have hdT : ∀ j, tagTotal (D.FS.tag L) (D.FS.dprice L) j ≤ D.FS.dT j :=
    fun j => D.FS.dT_total L j
  have hvT : ∀ j, tagTotal (D.FS.tag L) (D.FS.vprice L) j ≤ D.FS.vT j :=
    fun j => D.FS.vT_total L j
  have hd0 : ∀ j, 0 ≤ tagTotal (D.FS.tag L) (D.FS.dprice L) j := fun j =>
    sum_nonneg fun b _ => sum_nonneg fun i _ => by
      split_ifs
      · exact D.dprice_nonneg L b i
      · exact le_refl 0
  have hv0 : ∀ j, 0 ≤ tagTotal (D.FS.tag L) (D.FS.vprice L) j := fun j =>
    sum_nonneg fun b _ => sum_nonneg fun i _ => by
      split_ifs
      · exact D.vprice_nonneg L b i
      · exact le_refl 0
  have hser := tagSeries_mono hd0 hv0 hdT hvT
  have hser0 := tagSeries_nonneg hd0 hv0
  have hexp := Real.exp_le_exp.mpr hP
  have hR : Real.exp (∑ b, (fun b => if f b then 0 else D.GB.uprice L b) b) *
      tagSeries (tagTotal (D.FS.tag L) (D.FS.dprice L)) (tagTotal (D.FS.tag L) (D.FS.vprice L)) ≤
      D.GB.Rerr := by
    unfold GramBracket.Rerr
    exact mul_le_mul hexp hser hser0 (Real.exp_pos _).le
  have hzK : 0 ≤ z * K := mul_nonneg hz hK
  have hRK := mul_le_mul_of_nonneg_left hR hK
  calc _ ≤ _ := hmain
    _ ≤ (D.GB.Rerr + z) * K +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ := by
      nlinarith

end CRT

end Sarkozy.BracketEnergy
