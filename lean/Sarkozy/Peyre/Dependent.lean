module

public import Sarkozy.Peyre.Main

/-!
# Peyre's tensorization in finite form, XI: variables with different value sets

`thm:peyre-finite` (first statement) for a family `X v : Ω → α v` whose value types depend
on the index (`peyre_finite_dep`).  It is deduced from `peyre_finite` by embedding every
`α v` into the sigma type `Σ v, α v`; maximal correlations depend only on level sets
(`maxCorr_congr`), and the embedding `Sigma.mk v` is injective.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

open Sarkozy

variable {Ω : Type*} [Fintype Ω]

/-- **`thm:peyre-finite`, first statement, for value types depending on the index.** -/
theorem peyre_finite_dep (μ : FiniteLaw Ω) {ι : Type*} {α : ι → Type*}
    (X : (v : ι) → Ω → α v) (A B : Finset ι) (hAB : Disjoint A B) (ε : ι → ι → ℝ)
    (hε : ∀ i ∈ A, ∀ j ∈ B, 0 ≤ ε i j) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hop : ∀ x : B → ℝ, ∑ i : A, (∑ j : B, ε i j * x j) ^ 2 ≤ Λ ^ 2 * ∑ j : B, x j ^ 2)
    (hyp : ∀ i ∈ A, ∀ j ∈ B, ∀ S : Finset ι, (∀ v ∈ S, v ∈ A ∨ v ∈ B) → i ∉ S → j ∉ S →
      ∀ s : (v : ι) → α v,
      ∀ h : 0 < prob μ (fun ω => ∀ v ∈ S, X v ω = s v),
        maxCorr (condLaw μ (fun ω => ∀ v ∈ S, X v ω = s v) h) (X i) (X j) ≤ ε i j) :
    maxCorr μ (fun ω (v : A) => X v ω) (fun ω (v : B) => X v ω) ≤ min 1 Λ := by
  set X' : ι → Ω → (Σ v, α v) := fun v ω => ⟨v, X v ω⟩ with hX'
  have hinj : ∀ v ω ω', X' v ω = X' v ω' ↔ X v ω = X v ω' := fun v ω ω' =>
    ⟨fun h => sigma_mk_injective h, fun h => by simp only [hX', h]⟩
  have hmain := peyre_finite μ X' A B hAB ε hε hΛ hop (by
    intro i hi j hj S hS hiS hjS s' h
    obtain ⟨ω₀, hω₀, -⟩ := exists_of_prob_pos h
    have hs' : ∀ v ∈ S, X' v ω₀ = s' v := hω₀
    have hev : (fun ω => ∀ v ∈ S, X' v ω = s' v) = (fun ω => ∀ v ∈ S, X v ω = X v ω₀) := by
      funext ω
      apply propext
      constructor
      · intro hω v hv
        exact (hinj v ω ω₀).mp ((hω v hv).trans (hs' v hv).symm)
      · intro hω v hv
        exact ((hinj v ω ω₀).mpr (hω v hv)).trans (hs' v hv)
    have h' : 0 < prob μ (fun ω => ∀ v ∈ S, X v ω = X v ω₀) := hev ▸ h
    rw [cond_congr μ hev h h']
    have hc : maxCorr (condLaw μ (fun ω => ∀ v ∈ S, X v ω = X v ω₀) h') (X' i) (X' j) =
        maxCorr (condLaw μ (fun ω => ∀ v ∈ S, X v ω = X v ω₀) h') (X i) (X j) :=
      maxCorr_congr _ (fun ω ω' => hinj i ω ω') (fun ω ω' => hinj j ω ω')
    rw [hc]
    exact hyp i hi j hj S hS hiS hjS (fun v => X v ω₀) h')
  have hc : maxCorr μ (fun ω (v : A) => X' v ω) (fun ω (v : B) => X' v ω) =
      maxCorr μ (fun ω (v : A) => X v ω) (fun ω (v : B) => X v ω) := by
    apply maxCorr_congr
    · intro ω ω'
      simp only [funext_iff]
      exact forall_congr' (fun v => hinj v ω ω')
    · intro ω ω'
      simp only [funext_iff]
      exact forall_congr' (fun v => hinj v ω ω')
  rw [← hc]
  exact hmain

end Sarkozy.Peyre
