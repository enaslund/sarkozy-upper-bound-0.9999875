module

public import Sarkozy.DensityUpgrade.Coupled

/-!
# `lem:density:coupled` with a mixture over shared labels

`paper/sections/31_density_induction_upgrade.tex`, `lem:density:coupled`: "let `λ₊, λ₋` be its
two full actual folded laws, including integration of shared labels". WP-FI's
`DensityUpgrade.coupled_spectator_estimate_cut` treats one shared label: the selected law `K` is
`Comparison.Sharp` relative to half marginals `m₊, m₋`, and the folded laws are the diagonal
laws `Diag(m±)`. With several shared labels (`def:price`(b), `TheoremC.HasSharpBound`), the
selected law is a mixture `K = ∑_s π_s K_s` over the values `s` of the shared labels, each `K_s`
sharp relative to its own half marginals `m±_s` with the same constant `δ`, and the full folded
laws are the mixtures `λ± = ∑_s π_s Diag(m±_s)`.

* `coupled_folded_energy_of_sharp`: for one value `s`, the two folded energies are nonnegative and
  bound `K_s` (WP-FI's `coupledSharpBracket_of_sharp`, with the nonnegativity kept).
* `coupledSharpBracket_mixture`: the bracket passes to mixtures, by Cauchy–Schwarz over `s`
  (`|∑ π_s A_s| ≤ δ ∑ π_s √E₊(s) √E₋(s) ≤ δ √(∑ π_s E₊(s)) √(∑ π_s E₋(s))`).
* `coupled_spectator_estimate_mixture`: **`lem:density:coupled` for a mixture over shared
  labels**: with `λ±` the mixtures of the diagonal laws, the outside signed Hölder inequality and
  unit mixed `L^{d/θ}` of `λ₊, λ₋, κ`, the conclusion of the lemma holds.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityMoments

open Sarkozy.DensityUpgrade Sarkozy.ReflectionCut

variable {d : ℕ} {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]

/-- **The folded energies of one sharp law**: nonnegative, and they bound the coupled integral. -/
theorem coupled_folded_energy_of_sharp (c : ReflectionCut (Fin d))
    (K : ((Fin d → X) → ℝ) →ₗ[ℝ] ℝ) (O : ((Fin d → W) → ℝ) →ₗ[ℝ] ℝ)
    {mp mm : (c.Half → X) → ℝ} (hmp : ∀ x, 0 ≤ mp x) (hmm : ∀ x, 0 ≤ mm x) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsharp : Comparison.Sharp c K mp mm δ) (hO : c.Positive O)
    (g : Fin d → X → W → ℝ) :
    0 ≤ ∑ x, lawDensity (c.diagonalLaw mp) x *
        multilinearIntegral O (fun u => g (c.foldPlus u) (x u)) ∧
      0 ≤ ∑ x, lawDensity (c.diagonalLaw mm) x *
        multilinearIntegral O (fun u => g (c.foldMinus u) (x u)) ∧
      |∑ x, lawDensity K x * multilinearIntegral O (fun v => g v (x v))| ≤
        δ * Real.sqrt (∑ x, lawDensity (c.diagonalLaw mp) x *
          multilinearIntegral O (fun u => g (c.foldPlus u) (x u))) *
        Real.sqrt (∑ x, lawDensity (c.diagonalLaw mm) x *
          multilinearIntegral O (fun u => g (c.foldMinus u) (x u))) := by
  have hE : ∀ j ∈ ({true} : Finset Bool), j = true := fun j hj => Finset.mem_singleton.mp hj
  have h3 := Comparison.folded_energy c {true} (coupledPair (W := W) K O)
    (coupledHalf (W := W) c mp) (coupledHalf (W := W) c mm) (fun _ => δ) (fun _ _ => hδ)
    (fun j hj x => by obtain rfl := hE j hj; exact hmp x)
    (fun j hj x => by obtain rfl := hE j hj; exact hmm x)
    (fun j hj => by obtain rfl := hE j hj; exact hsharp)
    (fun j hj => by
      cases j
      · exact hO
      · exact absurd (Finset.mem_singleton_self _) hj)
    (fun v p => g v (p true) (p false))
  rw [Finset.prod_singleton] at h3
  have eT : multilinearIntegral (tensorLaw (coupledPair (W := W) K O))
      (fun v p => g v (p true) (p false)) =
      ∑ x, lawDensity K x * multilinearIntegral O (fun v => g v (x v)) :=
    coupled_two_atom _ g
  have eP : multilinearIntegral (tensorLaw fun j => if j ∈ ({true} : Finset Bool) then
      c.diagonalLaw (coupledHalf (W := W) c mp j) else coupledPair (W := W) K O j)
      (fun u p => g (c.foldPlus u) (p true) (p false)) =
      ∑ x, lawDensity (c.diagonalLaw mp) x *
        multilinearIntegral O (fun u => g (c.foldPlus u) (x u)) := by
    refine (coupled_two_atom _ (fun u => g (c.foldPlus u))).trans ?_
    rw [ite_eq_left (Finset.mem_singleton_self true), ite_eq_right (by simp)]
    rfl
  have eM : multilinearIntegral (tensorLaw fun j => if j ∈ ({true} : Finset Bool) then
      c.diagonalLaw (coupledHalf (W := W) c mm j) else coupledPair (W := W) K O j)
      (fun u p => g (c.foldMinus u) (p true) (p false)) =
      ∑ x, lawDensity (c.diagonalLaw mm) x *
        multilinearIntegral O (fun u => g (c.foldMinus u) (x u)) := by
    refine (coupled_two_atom _ (fun u => g (c.foldMinus u))).trans ?_
    rw [ite_eq_left (Finset.mem_singleton_self true), ite_eq_right (by simp)]
    rfl
  obtain ⟨hp, hm, hb⟩ := h3
  refine ⟨?_, ?_, ?_⟩
  · have := hp
    simp only [Function.comp_def] at this
    rw [← eP]
    exact this
  · have := hm
    simp only [Function.comp_def] at this
    rw [← eM]
    exact this
  · rw [← eT, ← eP, ← eM]
    simpa only [Function.comp_def] using hb

omit [DecidableEq X] [Fintype W] [DecidableEq W] in
/-- **The bracket passes to mixtures over the shared labels** (Cauchy–Schwarz over `s`). -/
theorem coupledSharpBracket_mixture {S : Type*} [Fintype S] {Λ : (Fin d → W → ℝ) → ℝ}
    {fp fm : Fin d → Fin d} {δ : ℝ} (hδ : 0 ≤ δ) (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (K lp lm : S → (Fin d → X) → ℝ)
    (hEp : ∀ s (g : Fin d → X → W → ℝ), 0 ≤ ∑ x, lp s x * Λ (fun u => g (fp u) (x u)))
    (hEm : ∀ s (g : Fin d → X → W → ℝ), 0 ≤ ∑ x, lm s x * Λ (fun u => g (fm u) (x u)))
    (hK : ∀ s, coupledSharpBracket Λ (K s) (lp s) (lm s) fp fm δ) :
    coupledSharpBracket Λ (fun x => ∑ s, π s * K s x) (fun x => ∑ s, π s * lp s x)
      (fun x => ∑ s, π s * lm s x) fp fm δ := by
  intro g
  set Ep : S → ℝ := fun s => ∑ x, lp s x * Λ (fun u => g (fp u) (x u)) with hEpdef
  set Em : S → ℝ := fun s => ∑ x, lm s x * Λ (fun u => g (fm u) (x u)) with hEmdef
  have hswap : ∀ (F : S → (Fin d → X) → ℝ) (G : (Fin d → X) → ℝ),
      ∑ x, (∑ s, π s * F s x) * G x = ∑ s, π s * ∑ x, F s x * G x := by
    intro F G
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hswap, hswap lp, hswap lm]
  calc |∑ s, π s * ∑ x, K s x * Λ (fun v => g v (x v))|
      ≤ ∑ s, π s * |∑ x, K s x * Λ (fun v => g v (x v))| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (hπ s)]
    _ ≤ ∑ s, π s * (δ * Real.sqrt (Ep s) * Real.sqrt (Em s)) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hK s g) (hπ s)
    _ = δ * ∑ s, Real.sqrt (π s * Ep s) * Real.sqrt (π s * Em s) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Real.sqrt_mul (hπ s), Real.sqrt_mul (hπ s)]
        have hss : Real.sqrt (π s) * Real.sqrt (π s) = π s := Real.mul_self_sqrt (hπ s)
        calc π s * (δ * Real.sqrt (Ep s) * Real.sqrt (Em s))
            = δ * ((Real.sqrt (π s) * Real.sqrt (π s)) * Real.sqrt (Ep s) *
                Real.sqrt (Em s)) := by rw [hss]; ring
          _ = _ := by ring
    _ ≤ δ * (Real.sqrt (∑ s, π s * Ep s) * Real.sqrt (∑ s, π s * Em s)) := by
        apply mul_le_mul_of_nonneg_left _ hδ
        exact Real.sum_sqrt_mul_sqrt_le _ (fun s => mul_nonneg (hπ s) (hEp s g))
          (fun s => mul_nonneg (hπ s) (hEm s g))
    _ = δ * Real.sqrt (∑ s, π s * Ep s) * Real.sqrt (∑ s, π s * Em s) := by ring

/-- **`lem:density:coupled` with a mixture over shared labels.** The selected law is
`K = ∑_s π_s K_s` with every `K_s` `Sharp` at the cut `c` with constant `δ` relative to its half
marginals `m±_s`; the full actual folded laws are `λ± = ∑_s π_s Diag(m±_s)`; `O` is reflection
positive at `c` and satisfies the outside signed Hölder inequality; `λ₊, λ₋, κ` have unit mixed
`L^{d/θ}`. Then the conclusion of `lem:density:coupled` holds. -/
theorem coupled_spectator_estimate_mixture {Y : Type*} [Fintype Y] {S : Type*} [Fintype S]
    (c : ReflectionCut (Fin d)) (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (K : S → ((Fin d → X) → ℝ) →ₗ[ℝ] ℝ) (O : ((Fin d → W) → ℝ) →ₗ[ℝ] ℝ)
    {κ : (Fin d → Y) → ℝ} {mp mm : S → (c.Half → X) → ℝ} (hmp : ∀ s x, 0 ≤ mp s x)
    (hmm : ∀ s x, 0 ≤ mm s x) {δ θ : ℝ} (hδ : 0 ≤ δ) (hθ : θ ≠ 0)
    (hsharp : ∀ s, Comparison.Sharp c (K s) (mp s) (mm s) δ) (hO : c.Positive O)
    (hhol : coupledOutsideHolder (multilinearIntegral O)) (hκ : ∀ z, 0 ≤ κ z)
    (hmp' : coupledUnitMixed ((d : ℝ) / θ)
      (fun x => ∑ s, π s * lawDensity (c.diagonalLaw (mp s)) x))
    (hmm' : coupledUnitMixed ((d : ℝ) / θ)
      (fun x => ∑ s, π s * lawDensity (c.diagonalLaw (mm s)) x))
    (hmκ : coupledUnitMixed ((d : ℝ) / θ) κ)
    {h : Fin d → X → Y → W → ℝ} {a : Fin d → X → Y → ℝ} {b : Fin d → ℝ}
    (ha : ∀ v x y, 0 ≤ a v x y) (hb : ∀ v, 0 ≤ b v)
    (hZ : ∀ v x y, coupledEnergy (multilinearIntegral O) (h v x y) ^ (1 / (d : ℝ)) ≤
      b v * a v x y ^ (θ / d)) :
    |∑ x, ∑ z, (∑ s, π s * lawDensity (K s) x) * κ z *
        multilinearIntegral O (fun v => h v (x v) (z v))| ≤
      δ * (∏ v, b v) * ∏ v, coupledMean (fun p : X × Y => a v p.1 p.2) ^ (θ / d) := by
  have hbr := coupledSharpBracket_mixture hδ π hπ (fun s => lawDensity (K s))
    (fun s => lawDensity (c.diagonalLaw (mp s))) (fun s => lawDensity (c.diagonalLaw (mm s)))
    (fun s g => (coupled_folded_energy_of_sharp c (K s) O (hmp s) (hmm s) hδ (hsharp s) hO g).1)
    (fun s g => (coupled_folded_energy_of_sharp c (K s) O (hmp s) (hmm s) hδ (hsharp s) hO g).2.1)
    (fun s g => (coupled_folded_energy_of_sharp c (K s) O (hmp s) (hmm s) hδ (hsharp s) hO g).2.2)
  exact coupled_spectator_estimate hδ hθ (coupledCopying_cut c) hbr hhol
    (fun x => Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (coupled_diagonalLaw_nonneg c (hmp s) x))
    (fun x => Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (coupled_diagonalLaw_nonneg c (hmm s) x))
    hκ hmp' hmm' hmκ ha hb hZ

end Sarkozy.DensityMoments
