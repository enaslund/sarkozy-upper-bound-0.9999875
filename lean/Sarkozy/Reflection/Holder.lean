module

public import Sarkozy.Reflection.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Signed Hölder from a sorting sequence

This is the finite maximizer proof of `thm:holder` in Section 5. The
normalization-and-limit step adapts OpenAI's `holder_of_finite_maximum` in
`MarkedTuples.lean`; the sorting argument applies to the paper's arbitrary
reflection coordinates, not the upstream permutation-word slot set.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter

namespace Sarkozy

variable {V X : Type*} [Fintype V] [DecidableEq V]

def foldSequence : List (ReflectionCut V) → V → V
  | [] => id
  | c :: cs => c.foldPlus ∘ foldSequence cs

def IsSorting (cs : List (ReflectionCut V)) (v₀ : V) : Prop :=
  ∀ v, foldSequence cs v = v₀

omit [Fintype V] [DecidableEq V] in
/-- Both folds of an absolute maximizer remain maximizers. -/
theorem maximum_preserved_by_fold {F : (V → V) → ℝ} {r f g : V → V}
    (hmax : ∀ s, |F s| ≤ |F r|)
    (hcs : |F r| ^ 2 ≤ F (r ∘ f) * F (r ∘ g))
    (hf : 0 ≤ F (r ∘ f)) : ∀ s, |F s| ≤ |F (r ∘ f)| := by
  have hg : F (r ∘ g) ≤ |F r| := (le_abs_self _).trans (hmax _)
  have hmul := mul_le_mul_of_nonneg_left hg hf
  have hbound : |F r| ≤ F (r ∘ f) := by
    by_cases hz : |F r| = 0
    · simpa only [hz] using hf
    have hp : 0 < |F r| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
    have hm : |F r| * |F r| ≤ F (r ∘ f) * |F r| := by
      simpa only [pow_two] using hcs.trans hmul
    nlinarith
  intro s
  exact (hmax s).trans (hbound.trans (le_abs_self _))

theorem maximum_preserved_by_sorting
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → X → ℝ)
    (cs : List (ReflectionCut V)) (hp : ∀ c ∈ cs, c.Positive L)
    {r : V → V}
    (hmax : ∀ s : V → V,
      |multilinearIntegral L (a ∘ s)| ≤ |multilinearIntegral L (a ∘ r)|) :
    ∀ s : V → V, |multilinearIntegral L (a ∘ s)| ≤
      |multilinearIntegral L (a ∘ (r ∘ foldSequence cs))| := by
  induction cs generalizing r with
  | nil => simpa only [foldSequence, Function.comp_id] using hmax
  | cons c cs ih =>
    have hc := hp c (by simp)
    have hnext := maximum_preserved_by_fold
      (F := fun s => multilinearIntegral L (a ∘ s)) hmax
      (hc.folding (a ∘ r)) (hc.foldPlus_nonneg (a ∘ r))
    have htail := ih (fun d hd => hp d (by simp [hd])) hnext
    simpa only [foldSequence, Function.comp_assoc] using htail

theorem diagonal_maximum_of_sorting [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ f, 0 ≤ diagonalIntegral L f)
    (cs : List (ReflectionCut V)) (hp : ∀ c ∈ cs, c.Positive L)
    {v₀ : V} (hs : IsSorting cs v₀) (a : V → X → ℝ) :
    ∃ i : V, |multilinearIntegral L a| ≤ diagonalIntegral L (a i) := by
  classical
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image (Finset.univ : Finset (V → V))
    (fun s => |multilinearIntegral L (a ∘ s)|) Finset.univ_nonempty
  have hmax := maximum_preserved_by_sorting L a cs hp (fun s => hr s (Finset.mem_univ _))
  refine ⟨r v₀, ?_⟩
  have hconstant : a ∘ (r ∘ foldSequence cs) = fun _ => a (r v₀) := by
    funext v
    simp only [Function.comp_apply, hs v]
  have h := hmax id
  rw [hconstant, Function.comp_id] at h
  change |multilinearIntegral L a| ≤ |diagonalIntegral L (a (r v₀))| at h
  rw [abs_of_nonneg (hdiag (a (r v₀)))] at h
  exact h

omit [DecidableEq V] in
theorem multilinearIntegral_div (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (a : V → X → ℝ) (c : V → ℝ) :
    multilinearIntegral L (fun v x => a v x / c v) =
      multilinearIntegral L a / ∏ v, c v := by
  unfold multilinearIntegral
  simp_rw [Finset.prod_div_distrib]
  have he : (fun z : V → X => (∏ v, a v (z v)) / ∏ v, c v) =
      (∏ v, c v)⁻¹ • (fun z => ∏ v, a v (z v)) := by
    funext z
    simp [div_eq_mul_inv, mul_comm]
  rw [he, map_smul, smul_eq_mul]
  ring

omit [DecidableEq V] in
theorem diagonalIntegral_div (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (g : X → ℝ) (c : ℝ) :
    diagonalIntegral L (fun x => g x / c) =
      diagonalIntegral L g / c ^ Fintype.card V := by
  unfold diagonalIntegral
  simpa only [Finset.prod_const, Finset.card_univ] using
    multilinearIntegral_div L (fun _ => g) (fun _ => c)

omit [DecidableEq V] in
/-- The epsilon regularization handles vanishing diagonal energies. -/
theorem holder_of_finite_maximum [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g)
    (hmax : ∀ a : V → X → ℝ, ∃ i : V,
      |multilinearIntegral L a| ≤ diagonalIntegral L (a i))
    (a : V → X → ℝ) :
    |multilinearIntegral L a| ≤
      ∏ v, diagonalIntegral L (a v) ^ ((1 : ℝ) / (Fintype.card V : ℝ)) := by
  classical
  let d : ℝ := Fintype.card V
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  have hε (ε : ℝ) (hε : 0 < ε) :
      |multilinearIntegral L a| ≤ ∏ v, (diagonalIntegral L (a v) + ε) ^ ((1 : ℝ) / d) := by
    let c (v : V) : ℝ := (diagonalIntegral L (a v) + ε) ^ ((1 : ℝ) / d)
    have hc (v : V) : 0 < c v := Real.rpow_pos_of_pos (by linarith [hdiag (a v)]) _
    have hcp (v : V) : c v ^ Fintype.card V = diagonalIntegral L (a v) + ε := by
      dsimp [c]
      rw [← Real.rpow_mul_natCast (le_of_lt (by linarith [hdiag (a v)] :
        0 < diagonalIntegral L (a v) + ε))]
      change (diagonalIntegral L (a v) + ε) ^ ((1 / d) * d) = _
      rw [one_div_mul_cancel hd.ne', Real.rpow_one]
    obtain ⟨i, hi⟩ := hmax (fun v x => a v x / c v)
    rw [multilinearIntegral_div, diagonalIntegral_div, hcp] at hi
    have hle : diagonalIntegral L (a i) / (diagonalIntegral L (a i) + ε) ≤ 1 := by
      apply (div_le_one (by linarith [hdiag (a i)])).mpr
      linarith
    have hprod : 0 < ∏ v, c v := Finset.prod_pos (fun v _ => hc v)
    rw [abs_div, abs_of_pos hprod] at hi
    exact (div_le_one hprod).mp (hi.trans hle)
  have hc : Continuous (fun ε : ℝ =>
      ∏ v, (diagonalIntegral L (a v) + ε) ^ ((1 : ℝ) / d)) := by
    apply continuous_finsetProd
    intro v _
    exact (Real.continuous_rpow_const (div_nonneg zero_le_one hd.le)).comp
      (continuous_const.add continuous_id)
  have ht := hc.continuousAt.tendsto.mono_left
    (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  have hevent : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      |multilinearIntegral L a| ≤ ∏ v, (diagonalIntegral L (a v) + ε) ^ ((1 : ℝ) / d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hεpos
    exact hε ε hεpos
  simpa only [add_zero] using ge_of_tendsto ht hevent

/-- Signed Hölder for any reflection-positive law with a sorting sequence. -/
theorem signed_holder_of_sorting [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ f, 0 ≤ diagonalIntegral L f)
    (cs : List (ReflectionCut V)) (hp : ∀ c ∈ cs, c.Positive L)
    {v₀ : V} (hs : IsSorting cs v₀) (a : V → X → ℝ) :
    |multilinearIntegral L a| ≤
      ∏ v, diagonalIntegral L (a v) ^ ((1 : ℝ) / (Fintype.card V : ℝ)) :=
  holder_of_finite_maximum L hdiag (diagonal_maximum_of_sorting L hdiag cs hp hs) a

/-- A normalized law with equal one-slot marginals controls their mean. -/
theorem mean_le_diagonal_root [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (mean : (X → ℝ) → ℝ)
    (hL : L (fun _ => 1) = 1)
    (hmarginal : ∀ v f, L (fun z => f (z v)) = mean f)
    (hholder : ∀ a : V → X → ℝ,
      |multilinearIntegral L a| ≤
        ∏ v, diagonalIntegral L (a v) ^ ((1 : ℝ) / (Fintype.card V : ℝ)))
    (f : X → ℝ) :
    |mean f| ≤ diagonalIntegral L f ^ ((1 : ℝ) / (Fintype.card V : ℝ)) := by
  classical
  let v : V := Classical.choice inferInstance
  have h := hholder (fun w => if w = v then f else fun _ => 1)
  have he : multilinearIntegral L (fun w => if w = v then f else fun _ => 1) = mean f := by
    unfold multilinearIntegral
    simp only [ite_apply]
    rw [show (fun z : V → X => ∏ w, if w = v then f (z w) else (1 : ℝ)) =
      (fun z => f (z v)) by funext z; simp]
    exact hmarginal v f
  have hone : diagonalIntegral L (fun _ => 1) = 1 := by
    simp [diagonalIntegral, multilinearIntegral, hL]
  rw [he] at h
  simpa only [apply_ite, hone, ite_pow, Real.one_rpow, Finset.prod_ite_eq',
    Finset.mem_univ, ite_eq_left] using h

/-- The unrooted lower bound needed for the density argument. -/
theorem mean_pow_le_diagonal [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (mean : (X → ℝ) → ℝ)
    (hL : L (fun _ => 1) = 1)
    (hmarginal : ∀ v f, L (fun z => f (z v)) = mean f)
    (hholder : ∀ a : V → X → ℝ,
      |multilinearIntegral L a| ≤
        ∏ v, diagonalIntegral L (a v) ^ ((1 : ℝ) / (Fintype.card V : ℝ)))
    (f : X → ℝ) (hdiag : 0 ≤ diagonalIntegral L f) :
    |mean f| ^ Fintype.card V ≤ diagonalIntegral L f := by
  have hroot := mean_le_diagonal_root L mean hL hmarginal hholder f
  have hpow := pow_le_pow_left₀ (abs_nonneg _) hroot (Fintype.card V)
  rw [← Real.rpow_mul_natCast hdiag] at hpow
  have hd : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rwa [one_div_mul_cancel hd, Real.rpow_one] at hpow

end Sarkozy
