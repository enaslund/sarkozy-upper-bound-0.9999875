module

public import Sarkozy.Kernel.KernelEstimate

@[expose] public section

/-!
# The kernel estimate for bounded functions on intervals

The last sentence of the paper's `prop:record:kernel20`: if `|F|, |J| ≤ 1` and `F, J` are
supported in intervals `I₁, I₂`, the right-hand side of `eq:record:K20` is at most
`C N^(-β/6) N⁻¹ ((|I₁|/D + 1)(|I₂|/D + 1))^(1/2)`. Here `I = [u, v] ∩ ℤ` and `|I|` is
its length `v - u` (the bound with the number `v - u + 1` of its integers follows).
The key count is `#{x ∈ [u,v] : x ≡ a (mod D)} ≤ (v - u)/D + 1`.

New material for this paper.
-/

namespace Sarkozy

namespace Kernel

open Finset

lemma card_Icc_filter_modEq_le (D : ℕ) (hD : 0 < D) (a u v : ℤ) (huv : u ≤ v) :
    ((({x ∈ Icc u v | x ≡ a [ZMOD (D : ℤ)]} : Finset ℤ)).card : ℝ) ≤
      ((v - u : ℤ) : ℝ) / D + 1 := by
  have hIcc : Icc u v = Ioc (u - 1) v := by
    ext x; simp only [mem_Icc, mem_Ioc]; omega
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have hc := Int.Ioc_filter_modEq_card (u - 1) v hDz a
  have hDq : (0 : ℚ) < ((D : ℤ) : ℚ) := by exact_mod_cast hD
  have key : ∀ A B : ℚ, A - B = ((v - u + 1 : ℤ) : ℚ) / ((D : ℤ) : ℚ) →
      (D : ℤ) * ((⌊A⌋ - ⌊B⌋) - 1) ≤ v - u := by
    intro A B hAB
    have h1 := Int.floor_le A
    have h2 := Int.lt_floor_add_one B
    have h3 : (((⌊A⌋ - ⌊B⌋ - 1 : ℤ)) : ℚ) < ((v - u + 1 : ℤ) : ℚ) / ((D : ℤ) : ℚ) := by
      rw [← hAB]
      push_cast
      linarith
    have h4 : ((D : ℤ) : ℚ) * (((⌊A⌋ - ⌊B⌋ - 1 : ℤ)) : ℚ) < ((v - u + 1 : ℤ) : ℚ) := by
      have := (lt_div_iff₀ hDq).mp h3
      linarith
    have h5 : (D : ℤ) * (⌊A⌋ - ⌊B⌋ - 1) < v - u + 1 := by exact_mod_cast h4
    omega
  have hAB : ((v : ℚ) - a) / ((D : ℤ) : ℚ) - (((u - 1 : ℤ) : ℚ) - a) / ((D : ℤ) : ℚ) =
      ((v - u + 1 : ℤ) : ℚ) / ((D : ℤ) : ℚ) := by
    push_cast
    field_simp
    ring
  have h2 := key _ _ hAB
  set n : ℤ := ⌊((v : ℚ) - a) / ((D : ℤ) : ℚ)⌋ - ⌊(((u - 1 : ℤ) : ℚ) - a) / ((D : ℤ) : ℚ)⌋ with hn
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h5 : ((max n 0 : ℤ) : ℝ) ≤ ((v - u : ℤ) : ℝ) / D + 1 := by
    rcases le_total n 0 with hn0 | hn0
    · rw [max_eq_right hn0, Int.cast_zero]
      have : (0 : ℝ) ≤ ((v - u : ℤ) : ℝ) / D :=
        div_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ v - u by omega)) hDr.le
      linarith
    · rw [max_eq_left hn0]
      have h7 : (((D : ℤ) * (n - 1) : ℤ) : ℝ) ≤ ((v - u : ℤ) : ℝ) := Int.cast_le.mpr h2
      have h6 : ((n : ℝ) - 1) ≤ ((v - u : ℤ) : ℝ) / D := by
        rw [le_div_iff₀ hDr]
        push_cast at h7 ⊢
        linarith
      linarith
  have hcard : ((({x ∈ Icc u v | x ≡ a [ZMOD (D : ℤ)]} : Finset ℤ)).card : ℝ) =
      ((max n 0 : ℤ) : ℝ) := by
    rw [hIcc]
    have h8 := congrArg (fun z : ℤ => (z : ℝ)) hc
    simp only [Int.cast_natCast] at h8
    rw [h8]
  rw [hcard]
  exact h5

lemma sqrt_mul_le' (A B : ℝ) : Real.sqrt A * Real.sqrt B ≤ Real.sqrt (A * B) := by
  by_cases hA : 0 ≤ A
  · by_cases hB : 0 ≤ B
    · rw [Real.sqrt_mul hA]
    · rw [Real.sqrt_eq_zero'.mpr (le_of_lt (not_le.mp hB)), mul_zero]
      exact Real.sqrt_nonneg _
  · rw [Real.sqrt_eq_zero'.mpr (le_of_lt (not_le.mp hA)), zero_mul]
    exact Real.sqrt_nonneg _

lemma l2norm_le_of_interval (F : ℤ →₀ ℂ) (D : ℕ) (hD : 0 < D) (a u v : ℤ)
    (hF1 : ∀ x, ‖F x‖ ≤ 1) (hFs : ∀ x ∈ F.support, u ≤ x ∧ x ≤ v ∧ x ≡ a [ZMOD (D : ℤ)]) :
    l2norm F ≤ Real.sqrt (((v - u : ℤ) : ℝ) / D + 1) := by
  have hsub : F.support ⊆ ({x ∈ Icc u v | x ≡ a [ZMOD (D : ℤ)]} : Finset ℤ) := by
    intro x hx
    have h := hFs x hx
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  unfold l2norm
  by_cases huv : u ≤ v
  · apply Real.sqrt_le_sqrt
    calc ∑ n ∈ F.support, ‖F n‖ ^ 2 ≤ ∑ _n ∈ F.support, (1 : ℝ) := by
          apply sum_le_sum
          intro n _
          have := hF1 n
          have h0 := norm_nonneg (F n)
          nlinarith
      _ = (F.support.card : ℝ) := by simp
      _ ≤ (({x ∈ Icc u v | x ≡ a [ZMOD (D : ℤ)]} : Finset ℤ).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ _ := card_Icc_filter_modEq_le D hD a u v huv
  · have hempty : ({x ∈ Icc u v | x ≡ a [ZMOD (D : ℤ)]} : Finset ℤ) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x hx
      simp only [mem_Icc] at hx
      omega
    have hsupp : F.support = ∅ := Finset.subset_empty.mp (hempty ▸ hsub)
    rw [hsupp, sum_empty, Real.sqrt_zero]
    exact Real.sqrt_nonneg _

/-- **The kernel estimate for bounded functions on intervals** (the last sentence of
`prop:record:kernel20`, at the triple of `cor:kernel20`, in the generality of part (iii); parts
(i) and (ii) are special cases by `isNonvanishing_of_strict` and
`dividedSquareClass_nonvanishing`): if moreover `|F|, |J| ≤ 1` and `F, J` are supported in
`[u₁, v₁]`, `[u₂, v₂]`, then
`|D ∑_{ξ ∈ Ξ_{H,D}} g(ξ) F̂(-ξ) Ĵ(ξ)| ≤ C N^(-1/120) N⁻¹ ((|I₁|/D + 1)(|I₂|/D + 1))^(1/2)`
with `|I_k| = v_k - u_k`. -/
theorem prop_kernel20_twentieth_intervals (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 40) ≤ H → H ≤ CH * (N : ℝ) ^ ((1 : ℝ) / 40) →
      ∀ D : ℕ, (D : ℝ) ≤ CD * (N : ℝ) ^ ((1 : ℝ) / 20) →
      ∀ a b : ℤ, IsNonvanishingSquareClass D (b - a) →
      ∀ (u₁ v₁ u₂ v₂ : ℤ) (F J : ℤ →₀ ℂ),
        (∀ x, ‖F x‖ ≤ 1) → (∀ y, ‖J y‖ ≤ 1) →
        (∀ x ∈ F.support, 1 ≤ x ∧ x ≤ N ∧ x ≡ a [ZMOD (D : ℤ)] ∧ u₁ ≤ x ∧ x ≤ v₁) →
        (∀ y ∈ J.support, 1 ≤ y ∧ y ≤ N ∧ y ≡ b [ZMOD (D : ℤ)] ∧ u₂ ≤ y ∧ y ≤ v₂) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, x < y) →
        (∀ x ∈ F.support, ∀ y ∈ J.support, ∀ m : ℕ, 1 ≤ m → y - x ≠ (m : ℤ) ^ 2) →
        ‖(D : ℂ) * ∑ ξ ∈ frequencySet H D,
            unitQuadraticAverage ξ * kernelTransform N F (-(ξ : ℝ)) *
              kernelTransform N J (ξ : ℝ)‖ ≤
          C * (N : ℝ) ^ (-(1 : ℝ) / 120) * (N : ℝ)⁻¹ *
            Real.sqrt ((((v₁ - u₁ : ℤ) : ℝ) / D + 1) * (((v₂ - u₂ : ℤ) : ℝ) / D + 1)) := by
  obtain ⟨C, hC, N₀, hmain⟩ := prop_kernel20_twentieth CD CH hCD hCH
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN H hH1 hH2 D hD a b hab u₁ v₁ u₂ v₂ F J hF1 hJ1 hF hJ hord hsq
  have hD0 : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · exfalso
      have := hab.1
      rw [h] at this
      simp at this
    · exact h
  have hbound := (hmain N hN H hH1 hH2).2.2 D hD a b hab F J
    (fun x hx => ⟨(hF x hx).1, (hF x hx).2.1, (hF x hx).2.2.1⟩)
    (fun y hy => ⟨(hJ y hy).1, (hJ y hy).2.1, (hJ y hy).2.2.1⟩) hord hsq
  have hlF := l2norm_le_of_interval F D hD0 a u₁ v₁ hF1
    (fun x hx => ⟨(hF x hx).2.2.2.1, (hF x hx).2.2.2.2, (hF x hx).2.2.1⟩)
  have hlJ := l2norm_le_of_interval J D hD0 b u₂ v₂ hJ1
    (fun y hy => ⟨(hJ y hy).2.2.2.1, (hJ y hy).2.2.2.2, (hJ y hy).2.2.1⟩)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hC0 : 0 ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 120) := mul_nonneg hC.le (Real.rpow_nonneg hN0 _)
  have hprod : l2norm F * l2norm J ≤
      Real.sqrt ((((v₁ - u₁ : ℤ) : ℝ) / D + 1) * (((v₂ - u₂ : ℤ) : ℝ) / D + 1)) := by
    have hJn : 0 ≤ l2norm J := Real.sqrt_nonneg _
    calc l2norm F * l2norm J ≤ Real.sqrt (((v₁ - u₁ : ℤ) : ℝ) / D + 1) *
          Real.sqrt (((v₂ - u₂ : ℤ) : ℝ) / D + 1) :=
          mul_le_mul hlF hlJ hJn (Real.sqrt_nonneg _)
      _ ≤ _ := sqrt_mul_le' _ _
  calc _ ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 120) * (l2norm F * l2norm J) / N := hbound
    _ ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 120) *
          Real.sqrt ((((v₁ - u₁ : ℤ) : ℝ) / D + 1) * (((v₂ - u₂ : ℤ) : ℝ) / D + 1)) / N := by
        gcongr
    _ = _ := by ring

end Kernel

end Sarkozy
