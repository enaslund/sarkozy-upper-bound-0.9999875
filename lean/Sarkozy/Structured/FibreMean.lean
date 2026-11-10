module

public import Sarkozy.Structured.PaperSlot

/-!
# The mean of the fibre density

The step `E α_{f,v} = ᾱ_v` of `prop:record:density-structured`, which the paper takes
"as in Step 2 of `lem:record:density-dc`": under `|ρ|/‖ρ‖` every label `z_v` is uniform
on `X_E` (condition (b) of `def:record:structured-energy`) and independent of `ω`, and
the class `𝔞(z_v)` is uniform among the classes modulo `D` compatible with `s_v`.

* `expect_variationLaw_slot`: if the one-slot marginals of `|ρ|` are uniform, the
  expectation of a function of `z_v` under `|ρ|/‖ρ‖` is its uniform average.
* `sum_card_filter_inFibre`: summing the fibre count over all labels `z` gives
  `#{x ∈ S : x ≡ s (mod D₀)} · ∏_{j ∉ E} m_j`.
* `uniform_fibreDensity`: the uniform average of the fibre density
  `α_f(z) = (D/|I|) #{x ∈ A ∩ I : x ≡ 𝔞(z) (mod D)}` is
  `(D₀/|I|) #{x ∈ A ∩ I : x ≡ s (mod D₀)}`, the integrand of `ᾱ_v`.

Here the selected labels `z_v` are elements of the whole group `ResidueSpace m`; only
their coordinates in `E` enter `α_f`. Uniformity of the one-slot marginals on the whole
group is then a condition on the representative of `ρ` on full labels. A measure `ρ_E`
on `X_E^V` corresponds to `ρ_E ⊗ Unif(X_𝒮)^V`, with the same energy and total
variation, and uniform marginals transfer. This is proved in
`Sarkozy/Structured/Representation.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Functional Sarkozy.FourierArithmetic

/-- Under uniform one-slot marginals of `|ρ|`, the expectation of a function of the label
at one slot is its uniform average. -/
theorem expect_variationLaw_slot {XE : Type*} [Fintype XE] [DecidableEq XE] [Nonempty XE]
    (ρ : (Slot → XE) → ℝ) (hρ : 0 < totalVariation ρ) (hunif : selectedMarginalsUniform ρ)
    (v : Slot) (f : XE → ℝ) :
    (variationLaw ρ hρ).expect (fun z => f (z v)) = (FiniteLaw.uniform XE).expect f := by
  rw [expect_variationLaw, FiniteLaw.expect_uniform]
  have h1 : ∑ z, |ρ z| * f (z v) = ∑ x, f x * ∑ z ∈ univ.filter (fun z : Slot → XE => z v = x),
      |ρ z| := by
    rw [← Finset.sum_fiberwise univ (fun z : Slot → XE => z v) (fun z => |ρ z| * f (z v))]
    apply sum_congr rfl
    intro x _
    rw [mul_sum]
    apply sum_congr rfl
    intro z hz
    rw [(mem_filter.mp hz).2]
    ring
  rw [h1]
  simp_rw [hunif v]
  have hc : (Fintype.card XE : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hρ' : totalVariation ρ ≠ 0 := hρ.ne'
  rw [← sum_mul]
  field_simp

section Count

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The number of labels with prescribed coordinates on `E` is `∏_{j ∉ E} m_j`. -/
theorem card_freeze (E : Finset J) (t : ResidueSpace m) :
    (∑ x : ResidueSpace m, if ∀ j ∈ E, x j = t j then (1 : ℕ) else 0) =
      ∏ j, if j ∈ E then 1 else m j := by
  have h : ∀ x : ResidueSpace m, (if ∀ j ∈ E, x j = t j then (1 : ℕ) else 0) =
      ∏ j, (if j ∈ E then (if x j = t j then 1 else 0) else 1) := by
    intro x
    by_cases hx : ∀ j ∈ E, x j = t j
    · rw [ite_eq_left hx]
      symm
      apply prod_eq_one
      intro j _
      split_ifs with h1 h2
      · rfl
      · exact absurd (hx j h1) h2
      · rfl
    · rw [ite_eq_right hx]
      push Not at hx
      obtain ⟨j, hj, hne⟩ := hx
      symm
      apply prod_eq_zero (mem_univ j)
      rw [ite_eq_left hj, ite_eq_right hne]
  simp_rw [h]
  rw [← Fintype.prod_sum (fun j (a : ZMod (m j)) => if j ∈ E then (if a = t j then 1 else 0) else 1)]
  apply prod_congr rfl
  intro j _
  split_ifs with hj
  · rw [Fintype.sum_ite_eq']
  · simp [ZMod.card]

/-- **The fibre count summed over the labels**:
`∑_z #{x ∈ S : x ∈ fibre(z)} = #{x ∈ S : x ≡ s (D₀)} · ∏_{j ∉ E} m_j`. -/
theorem sum_card_filter_inFibre (E : Finset J) {D0 : ℕ} (s : ZMod D0) (S : Finset ℤ) :
    (∑ z : ResidueSpace m, ((S.filter (InFibre m E z s)).card : ℝ)) =
      ((S.filter fun x : ℤ => (x : ZMod D0) = s).card : ℝ) * ∏ j, if j ∈ E then (1 : ℝ) else m j := by
  have h1 : ∀ z : ResidueSpace m, ((S.filter (InFibre m E z s)).card : ℝ) =
      ∑ x ∈ S, if (x : ZMod D0) = s ∧ ∀ j ∈ E, (x : ZMod (m j)) = z j then (1 : ℝ) else 0 := by
    intro z
    rw [card_filter]
    push_cast
    apply sum_congr rfl
    intro x _
    unfold InFibre
    rfl
  simp_rw [h1]
  rw [sum_comm, card_filter]
  push_cast
  rw [sum_mul]
  apply sum_congr rfl
  intro x _
  by_cases hs : (x : ZMod D0) = s
  · rw [ite_eq_left hs, one_mul]
    have h2 : ∀ z : ResidueSpace m, (if (x : ZMod D0) = s ∧ ∀ j ∈ E, (x : ZMod (m j)) = z j
        then (1 : ℝ) else 0) = ((if ∀ j ∈ E, z j = (fun k => (x : ZMod (m k))) j then 1 else 0 : ℕ) : ℝ) := by
      intro z
      by_cases hz : ∀ j ∈ E, z j = (x : ZMod (m j))
      · rw [ite_eq_left ⟨hs, fun j hj => (hz j hj).symm⟩, ite_eq_left hz]
        simp
      · rw [ite_eq_right (fun h => hz fun j hj => (h.2 j hj).symm), ite_eq_right hz]
        simp
    simp_rw [h2]
    rw [← Nat.cast_sum, card_freeze m E (fun k => (x : ZMod (m k)))]
    push_cast
    rfl
  · rw [ite_eq_right hs, zero_mul]
    apply sum_eq_zero
    intro z _
    rw [ite_eq_right (fun h => hs h.1)]

/-- **The uniform average of the fibre density** is
`(D₀/|I|) #{x ∈ A ∩ I : x ≡ s (mod D₀)}`. -/
theorem uniform_fibreDensity (E : Finset J) {D0 : ℕ} (s : ZMod D0) (A : Finset ℤ) (c : ℤ)
    (M : ℕ) :
    (FiniteLaw.uniform (ResidueSpace m)).expect (fun z => fibreDensity m E z s A c M) =
      (D0 : ℝ) / M *
        ((A ∩ Icc (c + 1) (c + M)).filter fun x : ℤ => (x : ZMod D0) = s).card := by
  rw [FiniteLaw.expect_uniform]
  unfold fibreDensity
  rw [← mul_sum, sum_card_filter_inFibre]
  have hcard : (Fintype.card (ResidueSpace m) : ℝ) = ∏ j, (m j : ℝ) := by
    rw [Fintype.card_pi]
    push_cast
    simp [ZMod.card]
  have hsplit : (∏ j, (m j : ℝ)) = (∏ j ∈ E, (m j : ℝ)) * ∏ j, if j ∈ E then (1 : ℝ) else m j := by
    have hE' : ∏ j ∈ E, (m j : ℝ) = ∏ j, (if j ∈ E then (m j : ℝ) else 1) := by
      rw [prod_ite_mem, univ_inter]
    rw [hE', ← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    split_ifs with hj
    · ring
    · ring
  have hE : (∏ j ∈ E, (m j : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast NeZero.ne (m j)
  have hrest : (∏ j, if j ∈ E then (1 : ℝ) else m j) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j _
    split_ifs
    · exact one_ne_zero
    · exact_mod_cast NeZero.ne (m j)
  rw [hcard, hsplit]
  push_cast
  field_simp

end Count

end Sarkozy.Structured
