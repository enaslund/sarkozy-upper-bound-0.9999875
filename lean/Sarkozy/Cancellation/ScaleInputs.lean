module

public import Sarkozy.Kernel.All
public import Sarkozy.Functional.ScaleConditions

@[expose] public section

/-!
# Scale inputs of Step 3 of `lem:record:density-can`

* `fibreModulus_le_of_scaleConditions`: by `lem:scale-conditions`(vi) (WP-FI's
  `Sarkozy.Functional.ScaleConditionsAt.cond_vi_min`, `M₀ Q_pre T₀ ≤ min(N^{1/20}, 𝔏)`), the
  fibre modulus `D = M₀ D_pre q_U` with `D_pre ≤ Q_pre` and `q_U ≤ T₀` satisfies
  `D ≤ N^{1/20}` and `D ≤ 𝔏`;
* `card_classPart_le`, `fibreDensity_le_two`: "since `D ≤ 𝔏`,
  `α_{f,i} ≤ (D/𝔏)(𝔏/D + 1) ≤ 2`" (Step 3), for an interval of at most `𝔏` integers;
* `sum_card_classPart_above`, `expect_fibreDensity_eq`, `expect_fibreDensity_le`: "the class
  `𝔞₁` is uniform among the `D_pre q_U` classes modulo `D` above `s`, and
  `E α_{f,1} = M₀ #{n ∈ A ∩ I_b : n ≡ s (M₀)}/𝔏 ≤ M₀ K α`" (Step 3).

New material for this paper.
-/

namespace Sarkozy.Cancellation

open Finset

/-- `#{n ∈ A ∩ [u, v] : n ≡ c (D)} ≤ (v − u + 1)/D + 1`. -/
lemma card_classPart_le (A : Finset ℤ) {u v : ℤ} (huv : u ≤ v) (c : ℤ) {D : ℕ} (hD : 0 < D) :
    ((Kernel.classPart A u v c D).card : ℝ) ≤ ((v - u + 1 : ℤ) : ℝ) / D + 1 := by
  have hsub : Kernel.classPart A u v c D ⊆
      (Ioc (u - 1) v).filter (fun x => x ≡ c [ZMOD (D : ℤ)]) := by
    intro x hx
    unfold Kernel.classPart at hx
    rw [mem_filter] at hx ⊢
    obtain ⟨_, h1, h2, h3⟩ := hx
    exact ⟨mem_Ioc.mpr ⟨by omega, h2⟩, h3⟩
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have hcard := Int.Ioc_filter_modEq_card (u - 1) v hDz c
  have hDq : (0 : ℚ) < ((D : ℤ) : ℚ) := by exact_mod_cast hD
  set x : ℚ := ((v - c : ℤ) : ℚ) / ((D : ℤ) : ℚ) with hx
  set y : ℚ := ((u - 1 - c : ℤ) : ℚ) / ((D : ℤ) : ℚ) with hy
  have hfl : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℚ) < x - y + 1 := by
    have h1 := Int.floor_le x
    have h2 := Int.sub_one_lt_floor y
    push_cast
    linarith
  have hxy : x - y + 1 = ((v - u + 1 : ℤ) : ℚ) / ((D : ℤ) : ℚ) + 1 := by
    rw [hx, hy]
    field_simp
    push_cast
    ring
  have hnn : (0 : ℚ) ≤ x - y + 1 := by
    rw [hxy]
    have : (0 : ℚ) ≤ ((v - u + 1 : ℤ) : ℚ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ v - u + 1)
    positivity
  have hmax : ((max (⌊x⌋ - ⌊y⌋) 0 : ℤ) : ℚ) ≤ x - y + 1 := by
    rcases le_total (⌊x⌋ - ⌊y⌋) 0 with h | h
    · rw [max_eq_right h]; push_cast; exact hnn
    · rw [max_eq_left h]; exact hfl.le
  have hc1 : ((Kernel.classPart A u v c D).card : ℤ) ≤ max (⌊x⌋ - ⌊y⌋) 0 := by
    have h := card_le_card hsub
    have h' : (((Ioc (u - 1) v).filter (fun x => x ≡ c [ZMOD (D : ℤ)])).card : ℤ) =
        max (⌊x⌋ - ⌊y⌋) 0 := by
      rw [hcard, hx, hy]
      push_cast
      ring_nf
    rw [← h']
    exact_mod_cast h
  have hq : ((Kernel.classPart A u v c D).card : ℚ) ≤
      ((v - u + 1 : ℤ) : ℚ) / ((D : ℤ) : ℚ) + 1 := by
    rw [← hxy]
    calc ((Kernel.classPart A u v c D).card : ℚ) = (((Kernel.classPart A u v c D).card : ℤ) : ℚ) := by
          push_cast; rfl
      _ ≤ ((max (⌊x⌋ - ⌊y⌋) 0 : ℤ) : ℚ) := by exact_mod_cast hc1
      _ ≤ x - y + 1 := hmax
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hr ⊢
  exact hr

/-- **The fibre densities are at most `2`** (Step 3 of `lem:record:density-can`): for an
interval `[u, v]` of at most `𝔏` integers and `0 < D ≤ 𝔏`,
`α_f = (D/𝔏) #{n ∈ A ∩ [u, v] : n ≡ c (D)} ≤ 2`. -/
theorem fibreDensity_le_two (A : Finset ℤ) {u v : ℤ} (huv : u ≤ v) (c : ℤ) {D : ℕ} (hD : 0 < D)
    {L : ℝ} (hlen : ((v - u + 1 : ℤ) : ℝ) ≤ L) (hDL : (D : ℝ) ≤ L) :
    (D : ℝ) / L * (Kernel.classPart A u v c D).card ≤ 2 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hL : 0 < L := lt_of_lt_of_le hDr hDL
  have h := card_classPart_le A huv c hD
  calc (D : ℝ) / L * (Kernel.classPart A u v c D).card
      ≤ (D : ℝ) / L * (((v - u + 1 : ℤ) : ℝ) / D + 1) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((v - u + 1 : ℤ) : ℝ) / L + (D : ℝ) / L := by field_simp
    _ ≤ 1 + 1 := by
        apply add_le_add
        · rw [div_le_one hL]; exact hlen
        · rw [div_le_one hL]; exact hDL
    _ = 2 := by norm_num

/-- **The fibre modulus under the scale conditions** (`lem:scale-conditions`(vi), used in Step 3
of `lem:record:density-can`): `D = M₀ D_pre q_U ≤ min(N^{1/20}, 𝔏)` when `D_pre ≤ Q_pre` and
`q_U ≤ T₀ = N^{t_an}`, `N = K 𝔏`. -/
theorem fibreModulus_le_of_scaleConditions {K M0 Qcl Qpre N0 N0' L : ℕ}
    (h : Sarkozy.Functional.ScaleConditionsAt K M0 Qcl Qpre N0 N0' L) {Dpre : ℕ}
    (hDpre : Dpre ≤ Qpre) {qU : ℝ} (hqU0 : 0 ≤ qU)
    (hqU : qU ≤ ((K * L : ℕ) : ℝ) ^ Sarkozy.Functional.stageTan) :
    (M0 : ℝ) * Dpre * qU ≤ ((K * L : ℕ) : ℝ) ^ ((1 : ℝ) / 20) ∧ (M0 : ℝ) * Dpre * qU ≤ L := by
  have hmin := h.cond_vi_min
  have hle : (M0 : ℝ) * Dpre * qU ≤
      (M0 : ℝ) * Qpre * ((K * L : ℕ) : ℝ) ^ Sarkozy.Functional.stageTan := by
    have h1 : (Dpre : ℝ) ≤ Qpre := by exact_mod_cast hDpre
    have h2 : (0 : ℝ) ≤ M0 := by positivity
    calc (M0 : ℝ) * Dpre * qU ≤ (M0 : ℝ) * Qpre * qU :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) hqU0
      _ ≤ _ := mul_le_mul_of_nonneg_left hqU (by positivity)
  exact ⟨hle.trans (hmin.trans (min_le_left _ _)), hle.trans (hmin.trans (min_le_right _ _))⟩

/-! ## The average fibre density -/

lemma classPart_periodic (A : Finset ℤ) (u v c : ℤ) (D : ℕ) :
    Kernel.classPart A u v (c + D) D = Kernel.classPart A u v c D := by
  unfold Kernel.classPart
  congr 1
  funext x
  have h : (c + D : ℤ) ≡ c [ZMOD (D : ℤ)] := by
    rw [Int.modEq_iff_dvd]; simp
  apply propext
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3.trans h⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3.trans h.symm⟩

/-- **The classes modulo `D` above `s` partition the class `s` modulo `M₀`** (`M₀ ∣ D`):
`∑_{c mod D, c ≡ s (M₀)} #(A ∩ [u,v] ∩ (c + Dℤ)) = #(A ∩ [u,v] ∩ (s + M₀ℤ))`. -/
theorem sum_card_classPart_above (A : Finset ℤ) (u v : ℤ) {D M₀ : ℕ} (hD : 0 < D)
    (hM₀D : M₀ ∣ D) (s : ℤ) :
    ∑ c ∈ (range D).filter (fun c : ℕ => (c : ℤ) ≡ s [ZMOD (M₀ : ℤ)]),
        (Kernel.classPart A u v c D).card =
      (Kernel.classPart A u v s M₀).card := by
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have hdvd : (M₀ : ℤ) ∣ (D : ℤ) := by exact_mod_cast hM₀D
  set T := (range D).filter (fun c : ℕ => (c : ℤ) ≡ s [ZMOD (M₀ : ℤ)]) with hT
  set f : ℤ → ℕ := fun x => (x % (D : ℤ)).toNat with hf
  have hmaps : ∀ x ∈ Kernel.classPart A u v s M₀, f x ∈ T := by
    intro x hx
    have hx' := (mem_filter.mp hx).2.2.2
    have hmod0 : 0 ≤ x % (D : ℤ) := Int.emod_nonneg x hDz.ne'
    have hlt : x % (D : ℤ) < D := Int.emod_lt_of_pos x hDz
    rw [hT, mem_filter, mem_range]
    refine ⟨by simp only [hf]; omega, ?_⟩
    simp only [hf]
    rw [Int.toNat_of_nonneg hmod0]
    exact ((Int.mod_modEq x D).of_dvd hdvd).trans hx'
  have hfib : ∀ c ∈ T, (Kernel.classPart A u v s M₀).filter (fun x => f x = c) =
      Kernel.classPart A u v c D := by
    intro c hc
    rw [hT, mem_filter, mem_range] at hc
    ext x
    have hmod0 : 0 ≤ x % (D : ℤ) := Int.emod_nonneg x hDz.ne'
    have hxD : x ≡ x % (D : ℤ) [ZMOD (D : ℤ)] := (Int.mod_modEq x D).symm
    rw [mem_filter]
    unfold Kernel.classPart
    rw [mem_filter, mem_filter]
    constructor
    · intro h
      obtain ⟨⟨hA, h1, h2, _⟩, hx⟩ := h
      refine ⟨hA, h1, h2, ?_⟩
      have h5 : x % (D : ℤ) = (c : ℤ) := by
        have h6 : ((x % (D : ℤ)).toNat : ℤ) = (c : ℤ) := by exact_mod_cast hx
        rwa [Int.toNat_of_nonneg hmod0] at h6
      rw [← h5]
      exact hxD
    · intro h
      obtain ⟨hA, h1, h2, h3⟩ := h
      have hc' : x % (D : ℤ) = (c : ℤ) := by
        have h4 : x % (D : ℤ) = (c : ℤ) % (D : ℤ) := h3
        rw [h4, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hc.1)]
      refine ⟨⟨hA, h1, h2, (h3.of_dvd hdvd).trans hc.2⟩, ?_⟩
      simp only [hf, hc', Int.toNat_natCast]
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_congr rfl
  intro c hc
  rw [hfib c hc]

/-- **The average fibre density** (Step 3 of `lem:record:density-can`): if the class `𝔞(ω)` is
uniform among the classes modulo `D` above `s` modulo `M₀` (for `D`-periodic test functions), then
`E α_f = (M₀/𝔏) #{n ∈ A ∩ [u,v] : n ≡ s (M₀)}`. -/
theorem expect_fibreDensity_eq {Ω : Type*} (S : Finset Ω) (w : Ω → ℝ) (𝔞 : Ω → ℤ)
    (A : Finset ℤ) (u v : ℤ) {D M₀ : ℕ} (hD : 0 < D) (hM₀D : M₀ ∣ D) (s : ℤ) (L : ℝ)
    (hunif : ∀ f : ℤ → ℝ, (∀ c, f (c + D) = f c) →
      ∑ ω ∈ S, w ω * f (𝔞 ω) = (M₀ : ℝ) / D *
        ∑ c ∈ (range D).filter (fun c : ℕ => (c : ℤ) ≡ s [ZMOD (M₀ : ℤ)]), f c) :
    ∑ ω ∈ S, w ω * ((D : ℝ) / L * (Kernel.classPart A u v (𝔞 ω) D).card) =
      (M₀ : ℝ) / L * (Kernel.classPart A u v s M₀).card := by
  rw [hunif (fun c => (D : ℝ) / L * (Kernel.classPart A u v c D).card)
    (fun c => by simp only [classPart_periodic])]
  rw [← mul_sum, ← Nat.cast_sum, sum_card_classPart_above A u v hD hM₀D s]
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp

/-- `E α_{f,1} ≤ M₀ K α`, `α = |A|/N`, `N/𝔏 ≤ K`. -/
theorem expect_fibreDensity_le {Ω : Type*} (S : Finset Ω) (w : Ω → ℝ) (𝔞 : Ω → ℤ)
    (A : Finset ℤ) (u v : ℤ) {D M₀ N : ℕ} (hD : 0 < D) (hM₀D : M₀ ∣ D) (s : ℤ) {L Kc : ℝ}
    (hL : 0 < L) (hN : 0 < N) (hKc : (N : ℝ) / L ≤ Kc)
    (hunif : ∀ f : ℤ → ℝ, (∀ c, f (c + D) = f c) →
      ∑ ω ∈ S, w ω * f (𝔞 ω) = (M₀ : ℝ) / D *
        ∑ c ∈ (range D).filter (fun c : ℕ => (c : ℤ) ≡ s [ZMOD (M₀ : ℤ)]), f c) :
    ∑ ω ∈ S, w ω * ((D : ℝ) / L * (Kernel.classPart A u v (𝔞 ω) D).card) ≤
      M₀ * Kc * ((A.card : ℝ) / N) := by
  rw [expect_fibreDensity_eq S w 𝔞 A u v hD hM₀D s L hunif]
  have hsub : ((Kernel.classPart A u v s M₀).card : ℝ) ≤ A.card := by
    exact_mod_cast card_le_card (filter_subset _ _)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : (0 : ℝ) ≤ M₀ := by positivity
  calc (M₀ : ℝ) / L * (Kernel.classPart A u v s M₀).card ≤ (M₀ : ℝ) / L * A.card :=
        mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = M₀ * ((N : ℝ) / L) * ((A.card : ℝ) / N) := by field_simp
    _ ≤ M₀ * Kc * ((A.card : ℝ) / N) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKc hM) (by positivity)

end Sarkozy.Cancellation
