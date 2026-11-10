module

public import Sarkozy.OpsSteps.FineSum
public import Sarkozy.OpsSteps.Background

@[expose] public section

/-!
# The finer (E1) grouped by the outside set `Z`: the input `hfine` of `heval_of_finer` (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, "(iii) and (i)".

Step 4 prices the background energies `Y^{O_Z}[Diag_ω]` per set `Z` of outside atoms carrying the
generic tag `G` (`Step4.paperEO`). With `Ñ^inv_𝔟 = μ_𝔟 + ∑_{¬isG} κu` and `G_𝔟 = ∑_{isG} κu`:

* `tensorLaw_sum_finset`: a tensor of finite sums is the sum over the choices in the product set;
* `Tset`, **`paperEO_eq_fine`**: `Y^{O_Z}[Diag_ω] = ∑_{g ∈ T(Z)} 𝔈_{ω,g}` (the finer terms whose `G`
  atoms are `Z`), given the identification of the diagonals with the norm envelopes;
* **`sum_fineMain_eq`**: their main terms add up to
  `(1 + ε) C_X Y ∏_{𝔟 ∈ Z} w_𝔟 ∏_{𝔟 ∉ Z ∪ S} (1 + v_𝔟)`,
  `w`, `v` the prices of `G` and of `E_add + H`;
* **`hfine_of_fine`**: hence the input `hfine` of `Background.heval_of_finer`, with
  `r_{ω,Z} = ∑_{g ∈ T(Z)} fX_{ω,g}`; `sum_rZ_le`: `∑_Z r_{ω,Z} ≤ ∑_g fX_{ω,g}`, which
  `FineSum.fX_summable` sums.
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.E1Closure Sarkozy.EnvelopeSteps
open Sarkozy.Param (Params)
open Sarkozy.SharpFirst (sfEps sfEps_nonneg)

section Generic

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- **A tensor of finite sums is the sum over the product set of the choices.** -/
theorem tensorLaw_sum_finset {I : J → Type*} [∀ j, DecidableEq (I j)] (T : ∀ j, Finset (I j))
    (Lk : ∀ j, I j → ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (fun j => ∑ i ∈ T j, Lk j i) =
      ∑ f ∈ Fintype.piFinset T, tensorLaw (fun j => Lk j (f j)) := by
  apply LinearMap.ext
  intro F
  rw [LinearMap.sum_apply]
  simp only [tensorLaw_apply, lawDensity_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_mul, Finset.prod_univ_sum]

end Generic

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ)
  (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)

/-- The invariant background `μ + ∑_{¬isG} κu` and the generic tag `∑_{isG} κu` of an atom. -/
noncomputable def NinvOf (b : BlockAtom Bk PaperJt L) :
    TheoremCBlock.AtomMeasure m₀ blk paperTail L b :=
  D.R.law paperTail L b + ∑ i ∈ univ.filter (fun i => isG b i = false), D.GB.κu L b i

/-- The generic tag `G = ∑_{isG} κu` of an atom. -/
noncomputable def GOf (b : BlockAtom Bk PaperJt L) :
    TheoremCBlock.AtomMeasure m₀ blk paperTail L b :=
  ∑ i ∈ univ.filter (fun i => isG b i = true), D.GB.κu L b i

omit [DecidableEq P] in
/-- `Ñ₀ = Ñ^inv + G` for this split. -/
theorem N₀_eq_split (b : BlockAtom Bk PaperJt L) :
    D.GB.N₀ L b = NinvOf D L isG b + GOf D L isG b := by
  unfold NinvOf GOf
  have e1 := sum_filter_add_sum_filter_not univ (fun i => isG b i = true) (fun i => D.GB.κu L b i)
  simp only [Bool.not_eq_true] at e1
  rw [add_assoc, add_comm (∑ i ∈ univ.filter (fun i => isG b i = false), D.GB.κu L b i), e1]
  have := D.GB.N₀_sub L b
  rw [← this]
  abel

/-- The choices of the finer terms whose generic atoms are `Z` (`f`): `none` on `S`, `G` on `Z`,
`μ` or `E_add + H` elsewhere. -/
def Tset (S : Finset (BlockAtom Bk PaperJt L)) (f : {b // b ∉ S} → Bool)
    (b : BlockAtom Bk PaperJt L) : Finset (Option Bool) :=
  if hb : b ∈ S then {none} else if f ⟨b, hb⟩ then {some true} else {none, some false}

omit [DecidableEq P] in
/-- **The background energy at `Z` is the sum of the finer terms with generic atoms `Z`.** -/
theorem paperEO_eq_fine (A : Finset ℤ) (ω : Choice (D.CL.T L)) (S : Finset (BlockAtom Bk PaperJt L))
    (hS : Choice.support ω = S) (O : {b // b ∈ S} → Type) [∀ b, Fintype (O b)]
    [∀ b, DecidableEq (O b)] (m : ∀ b, O b → ℝ)
    (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk paperTail L b.1))
    (hD : ∀ b (hb : b ∈ S), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (m ⟨b, hb⟩) (φ ⟨b, hb⟩)) = D.CL.D L b t e)
    (f : {b // b ∉ S} → Bool) :
    paperEO L A S (NinvOf D L isG) (GOf D L isG) f
        (reservedCut.diagonalLaw (push (prodWeight m) (prodPlace reservedCut φ))) =
      ∑ g ∈ Fintype.piFinset (Tset L S f), fineInt D L isG A ω g := by
  rw [← place_id, place_tensor reservedCut m φ (fun _ => LinearMap.id) LinearMap.id
    (kern_id_prod m)]
  simp only [place_id]
  let L' : ∀ b : BlockAtom Bk PaperJt L, TheoremCBlock.AtomMeasure m₀ blk paperTail L b := fun b =>
    if hb : b ∈ S then reservedCut.diagonalLaw (push (m ⟨b, hb⟩) (φ ⟨b, hb⟩))
    else if f ⟨b, hb⟩ then GOf D L isG b else NinvOf D L isG b
  have h1 : (fun b : {b // b ∈ S} => L' b.1) =
      fun b : {b // b ∈ S} => reservedCut.diagonalLaw (push (m b) (φ b)) := by
    funext b
    simp only [L', b.2, ↓reduceDIte]
  have h2 : (fun b : {b // b ∉ S} => L' b.1) =
      fun b : {b // b ∉ S} => if f b then GOf D L isG b.1 else NinvOf D L isG b.1 := by
    funext b
    simp only [L', b.2, ↓reduceDIte]
  have key := jointEnergy_tensor S L' (blockLift m₀ blk paperTail L A)
  rw [h1, h2] at key
  unfold paperEO
  rw [jointEnergyL_apply]
  change jointEnergy _ (OZ L S (NinvOf D L isG) (GOf D L isG) f) _ = _
  unfold OZ
  rw [key]
  have hL' : L' = fun b => ∑ y ∈ Tset L S f b, fineLaw D L isG b (ω b) y := by
    funext b
    unfold Tset
    by_cases hb : b ∈ S
    · simp only [L', hb, ↓reduceDIte, sum_singleton]
      have hb' : b ∈ Choice.support ω := hS ▸ hb
      rcases hω : ω b with _ | ⟨t, e⟩
      · exact absurd (by simpa [Choice.support] using hb') (by simp [hω])
      · rw [hD b hb t e hω]
        rfl
    · have hb' : b ∉ Choice.support ω := hS ▸ hb
      have hω : ω b = none := eq_none_of_not_mem_support D hb'
      simp only [L', hb, ↓reduceDIte]
      by_cases hf : f ⟨b, hb⟩
      · simp only [hf, ↓reduceIte, sum_singleton, fineLaw, hω, Option.isSome_none,
          Bool.false_eq_true]
        rfl
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        rw [sum_pair (by simp)]
        simp only [fineLaw, hω, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        rfl
  rw [hL', tensorLaw_sum_finset, diagonalIntegral_sum]
  rfl

omit [DecidableEq P] in
/-- **The main terms of the finer terms with generic atoms `Z`.** -/
theorem sum_fineMain_eq (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (S : Finset (BlockAtom Bk PaperJt L)) (hS : Choice.support ω = S) (f : {b // b ∉ S} → Bool) :
    ∑ g ∈ Fintype.piFinset (Tset L S f), fineMain D L isG εE A ω g =
      ((1 + εE L) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          D.Y L A) *
        ∏ b : {b // b ∉ S}, (if f b then finePr D L isG b.1 none (some true)
          else 1 + finePr D L isG b.1 none (some false)) := by
  unfold fineMain
  rw [← mul_sum, ← Finset.prod_univ_sum]
  congr 1
  have hsplit := (prod_filter_mul_prod_filter_not univ (fun b => b ∈ S)
    (fun b => ∑ y ∈ Tset L S f b, finePr D L isG b (ω b) y)).symm
  rw [hsplit]
  have hin : ∏ b ∈ univ.filter (fun b => b ∈ S), ∑ y ∈ Tset L S f b,
      finePr D L isG b (ω b) y = 1 := by
    refine prod_eq_one fun b hb => ?_
    have hbS : b ∈ S := (mem_filter.mp hb).2
    simp only [Tset, hbS, ↓reduceDIte, sum_singleton]
    rfl
  rw [hin, one_mul]
  rw [Finset.prod_subtype (univ.filter (fun b => b ∉ S)) (p := fun b => b ∉ S)
    (fun b => by simp) (fun b => ∑ y ∈ Tset L S f b, finePr D L isG b (ω b) y)]
  refine prod_congr rfl fun b _ => ?_
  have hb' : b.1 ∉ Choice.support ω := hS ▸ b.2
  have hω : ω b.1 = none := eq_none_of_not_mem_support D hb'
  simp only [Tset, b.2, ↓reduceDIte, hω]
  by_cases hf : f b
  · simp only [hf, ↓reduceIte, sum_singleton]
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rw [sum_pair (by simp)]
    rfl

omit [DecidableEq P] in
/-- **The finer (E1) per outside set `Z`** (the input `hfine` of `heval_of_finer`):
`Y^{O_Z}[Diag_ω] ≤ (1 + ε) C_X Y ∏_{Z} w ∏_{Zᶜ} (1 + v) + ∑_{g ∈ T(Z)} fX_{ω,g}`. -/
theorem hfine_of_fine (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (S : Finset (BlockAtom Bk PaperJt L)) (hS : Choice.support ω = S) (O : {b // b ∈ S} → Type)
    [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)] (m : ∀ b, O b → ℝ)
    (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk paperTail L b.1))
    (hD : ∀ b (hb : b ∈ S), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (m ⟨b, hb⟩) (φ ⟨b, hb⟩)) = D.CL.D L b t e)
    (f : {b // b ∉ S} → Bool) :
    paperEO L A S (NinvOf D L isG) (GOf D L isG) f
        (reservedCut.diagonalLaw (push (prodWeight m) (prodPlace reservedCut φ))) ≤
      (1 + εE L) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          D.Y L A *
        ∏ b : {b // b ∉ S}, (if f b then finePr D L isG b.1 none (some true)
          else 1 + finePr D L isG b.1 none (some false)) +
        ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG εE A ω g := by
  rw [paperEO_eq_fine D L isG A ω S hS O m φ hD f, ← sum_fineMain_eq D L isG εE A ω S hS f,
    ← sum_add_distrib]
  refine sum_le_sum fun g _ => ?_
  unfold fX
  linarith [le_abs_self (fineInt D L isG A ω g),
    le_max_right 0 (|fineInt D L isG A ω g| - fineMain D L isG εE A ω g)]

omit [DecidableEq P] in
/-- **The remainders grouped by `Z` are at most the remainders of all finer terms** (the sets `T(Z)`
are disjoint). -/
theorem sum_rZ_le (εE : ℕ → ℝ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (S : Finset (BlockAtom Bk PaperJt L)) :
    ∑ f : {b // b ∉ S} → Bool, ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG εE A ω g ≤
      ∑ g : BlockAtom Bk PaperJt L → Option Bool, fX D L isG εE A ω g := by
  rw [← sum_biUnion]
  · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun g _ _ => le_max_left _ _
  · intro f₁ _ f₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro g hg₁ hg₂
    apply hne
    funext b
    have h1 := (Fintype.mem_piFinset.mp hg₁) b.1
    have h2 := (Fintype.mem_piFinset.mp hg₂) b.1
    simp only [Tset, b.2, ↓reduceDIte] at h1 h2
    cases hf1 : f₁ b <;> cases hf2 : f₂ b
    · rfl
    · simp only [hf1, hf2, Bool.false_eq_true, ↓reduceIte, mem_insert, mem_singleton] at h1 h2
      rcases h1 with h1 | h1 <;> rw [h1] at h2 <;> simp at h2
    · simp only [hf1, hf2, Bool.false_eq_true, ↓reduceIte, mem_insert, mem_singleton] at h1 h2
      rcases h2 with h2 | h2 <;> rw [h2] at h1 <;> simp at h1
    · rfl

end Sarkozy.OpsSteps
