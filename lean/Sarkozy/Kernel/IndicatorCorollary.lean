module

public import Sarkozy.Kernel.Admissible
public import Sarkozy.Definitions

@[expose] public section

/-!
# The kernel estimate for a square-difference-free set

How square-difference-freeness enters (Section 7, paragraph after `cor:kernel20`): for a
square-difference-free `A ⊆ [1,N]` (the project's `Admissible N A`, with the OpenAI convention
`IsSquareDifferenceFree`), two intervals `I₁ = [u₁, v₁]`, `I₂ = [u₂, v₂]` with `v₁ < u₂`, and
two residue classes `a, b mod D` whose difference is a nonvanishing square class, the indicator
functions `F = 1_{A ∩ I₁ ∩ (a + Dℤ)}` and `J = 1_{A ∩ I₂ ∩ (b + Dℤ)}` satisfy all hypotheses of
`prop:record:kernel20`, so
`|D ∑_{ξ ∈ Ξ_{H,D}} g(ξ) F̂(-ξ) Ĵ(ξ)| ≤ C N^(-β/6) (|A₁| |A₂|)^(1/2) / N`
with `A₁ = A ∩ I₁ ∩ (a + Dℤ)`, `A₂ = A ∩ I₂ ∩ (b + Dℤ)`. This is the form used by the
accepted-pair cancellation `lem:record:density-can` (not formalized here).

New material for this paper.
-/

namespace Sarkozy

namespace Kernel

open Finset

/-- The indicator function of a finite set of integers, as a finitely supported function. -/
noncomputable def setIndicator (S : Finset ℤ) : ℤ →₀ ℂ := Finsupp.indicator S (fun _ _ => (1 : ℂ))

lemma setIndicator_apply (S : Finset ℤ) (x : ℤ) :
    setIndicator S x = if x ∈ S then 1 else 0 := by
  classical
  unfold setIndicator
  rw [Finsupp.indicator_apply]
  split_ifs <;> rfl

lemma setIndicator_support (S : Finset ℤ) : (setIndicator S).support = S := by
  classical
  ext x
  rw [Finsupp.mem_support_iff, setIndicator_apply]
  split_ifs with h <;> simp [h]

lemma l2norm_setIndicator (S : Finset ℤ) : l2norm (setIndicator S) = Real.sqrt S.card := by
  unfold l2norm
  rw [setIndicator_support]
  congr 1
  have : ∀ x ∈ S, ‖setIndicator S x‖ ^ 2 = 1 := by
    intro x hx
    rw [setIndicator_apply, ite_eq_left hx]
    simp
  rw [Finset.sum_congr rfl this]
  simp

/-- The part of `A` in the interval `[u, v]` and the residue class `c mod D`. -/
noncomputable def classPart (A : Finset ℤ) (u v c : ℤ) (D : ℕ) : Finset ℤ :=
  A.filter (fun x => u ≤ x ∧ x ≤ v ∧ x ≡ c [ZMOD (D : ℤ)])

/-- **The kernel estimate for a square-difference-free set** (`prop:record:kernel20`(iii), hence
(i) and (ii), applied to the indicators of `A ∩ I₁ ∩ (a + Dℤ)` and `A ∩ I₂ ∩ (b + Dℤ)`), for every
admissible triple. -/
theorem prop_kernel20_squareDifferenceFree (β κ η : ℝ) (hadm : KernelAdmissible β κ η)
    (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ (β / 2) ≤ H → H ≤ CH * (N : ℝ) ^ (β / 2) →
      ∀ D : ℕ, (D : ℝ) ≤ CD * (N : ℝ) ^ κ →
      ∀ a b : ℤ, IsNonvanishingSquareClass D (b - a) →
      ∀ A : Finset ℤ, Admissible N A →
      ∀ u₁ v₁ u₂ v₂ : ℤ, v₁ < u₂ →
        ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D,
            unitQuadraticAverage ξ *
              kernelTransform N (setIndicator (classPart A u₁ v₁ a D)) (-(ξ : ℝ)) *
              kernelTransform N (setIndicator (classPart A u₂ v₂ b D)) (ξ : ℝ)‖ ≤
          C * (N : ℝ) ^ (-(β / 6)) *
            Real.sqrt ((classPart A u₁ v₁ a D).card * (classPart A u₂ v₂ b D).card) / N := by
  obtain ⟨C, hC, N₀, hmain⟩ := prop_kernel20 β κ η hadm CD CH hCD hCH
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN H hH1 hH2 D hD a b hab A hA u₁ v₁ u₂ v₂ huv
  obtain ⟨hAN, hsdf⟩ := hA
  have hmem : ∀ (u v c x : ℤ), x ∈ classPart A u v c D →
      x ∈ A ∧ u ≤ x ∧ x ≤ v ∧ x ≡ c [ZMOD (D : ℤ)] := by
    intro u v c x hx
    unfold classPart at hx
    rw [mem_filter] at hx
    exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩
  have hbound := (hmain N hN H hH1 hH2).2.2 D hD a b hab
    (setIndicator (classPart A u₁ v₁ a D)) (setIndicator (classPart A u₂ v₂ b D))
    (by
      intro x hx
      rw [setIndicator_support] at hx
      obtain ⟨hxA, _, _, hxc⟩ := hmem u₁ v₁ a x hx
      have := mem_Icc.mp (hAN hxA)
      exact ⟨this.1, this.2, hxc⟩)
    (by
      intro y hy
      rw [setIndicator_support] at hy
      obtain ⟨hyA, _, _, hyc⟩ := hmem u₂ v₂ b y hy
      have := mem_Icc.mp (hAN hyA)
      exact ⟨this.1, this.2, hyc⟩)
    (by
      intro x hx y hy
      rw [setIndicator_support] at hx hy
      obtain ⟨_, _, hxv, _⟩ := hmem u₁ v₁ a x hx
      obtain ⟨_, hyu, _, _⟩ := hmem u₂ v₂ b y hy
      omega)
    (by
      intro x hx y hy m hm
      rw [setIndicator_support] at hx hy
      obtain ⟨hxA, _, _, _⟩ := hmem u₁ v₁ a x hx
      obtain ⟨hyA, _, _, _⟩ := hmem u₂ v₂ b y hy
      exact hsdf y hyA x hxA m hm)
  rw [l2norm_setIndicator, l2norm_setIndicator] at hbound
  rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  calc _ ≤ _ := hbound
    _ = _ := by ring

end Kernel

end Sarkozy
