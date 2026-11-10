module

public import Sarkozy.Construction.CliqueArithmetic

/-!
# Coincidence masses of the square-clique law (`lem:frontier:iidlocal` (iv), (v))

`paper/sections/19_prefix.tex`. Under a chamber pullback of independent labels, two slots in
distinct first chambers carry equal labels with probability `∑_ω w_ω ∑_x ν_ω(x)²`
(`chamberIidLaw_coincidence`). For the square-clique law the labels are uniform on a set of
`2^ℓ` elements, so this probability is exactly `2^{-ℓ}` (`cliqueLaw_coincidence`); by the
union bound a family of query pairs with `n` distinct first-coordinate pairs has exception mass
at most `n 2^{-ℓ}` (`cliqueLaw_exception_le`). For the six queries of `𝓔₆`, whose
first-coordinate pairs are all `(0, 2)`, the exception mass is exactly `2^{-ℓ}`
(`cliqueLaw_coincidence` with `u₀ = 0`, `v₀ = 2`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy

variable {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]

/-- **Coincidence probability of a chamber pullback**: for slots in distinct first chambers. -/
theorem chamberIidLaw_coincidence (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) {u v : Slot}
    (huv : firstChamber u ≠ firstChamber v) :
    (chamberIidLaw w ν).expect (fun z => if z u = z v then 1 else 0) =
      ∑ ω, w.weight ω * ∑ x, (ν ω).weight x ^ 2 := by
  rw [expect_chamberIidLaw]
  refine sum_congr rfl fun ω _ => ?_
  congr 1
  set j := firstChamber u
  set j' := firstChamber v
  -- split the indicator over the common value
  have hsplit : ∀ y : Chamber → X, (∏ i, (ν ω).weight (y i)) *
      (if (y ∘ firstChamber) u = (y ∘ firstChamber) v then (1 : ℝ) else 0) =
      ∑ x : X, ∏ i, ((ν ω).weight (y i) *
        (if i = j ∨ i = j' then (if y i = x then 1 else 0) else 1)) := by
    intro y
    simp only [Function.comp_apply]
    rw [sum_congr rfl fun x _ => prod_mul_distrib, ← mul_sum]
    congr 1
    -- `∑_x ∏_i [i ∈ {j, j'} → y_i = x] = [y_j = y_{j'}]`
    have hprod : ∀ x : X, (∏ i, (if i = j ∨ i = j' then (if y i = x then (1 : ℝ) else 0) else 1)) =
        (if y j = x then 1 else 0) * (if y j' = x then 1 else 0) := by
      intro x
      rw [← prod_filter_mul_prod_filter_not univ (fun i => i = j ∨ i = j')]
      have hf : univ.filter (fun i => i = j ∨ i = j') = {j, j'} := by
        ext i; simp
      rw [hf, prod_pair huv]
      have hrest : ∏ i ∈ univ.filter (fun i => ¬ (i = j ∨ i = j')),
          (if i = j ∨ i = j' then (if y i = x then (1 : ℝ) else 0) else 1) = 1 :=
        prod_eq_one fun i hi => by
          have h := (mem_filter.mp hi).2
          simp only [h, ↓reduceIte]
      rw [hrest, mul_one]
      simp
    simp_rw [hprod]
    by_cases hyy : y j = y j'
    · rw [ite_eq_left hyy, sum_eq_single (y j)]
      · simp [hyy]
      · intro x _ hx; simp [Ne.symm hx]
      · intro h; exact absurd (mem_univ _) h
    · rw [ite_eq_right hyy]
      refine (sum_eq_zero fun x _ => ?_).symm
      by_cases h1 : y j = x
      · have h2 : y j' ≠ x := fun h2 => hyy (h1.trans h2.symm)
        simp [h1, h2]
      · simp [h1]
  simp_rw [hsplit]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← Fintype.prod_sum (fun (i : Chamber) (a : X) => (ν ω).weight a *
    (if i = j ∨ i = j' then (if a = x then 1 else 0) else 1))]
  rw [← prod_filter_mul_prod_filter_not univ (fun i => i = j ∨ i = j')]
  have hf : univ.filter (fun i => i = j ∨ i = j') = {j, j'} := by ext i; simp
  rw [hf, prod_pair huv]
  have hrest : ∏ i ∈ univ.filter (fun i => ¬ (i = j ∨ i = j')), ∑ a : X, (ν ω).weight a *
      (if i = j ∨ i = j' then (if a = x then (1 : ℝ) else 0) else 1) = 1 :=
    prod_eq_one fun i hi => by
      have h := (mem_filter.mp hi).2
      simp only [h, ↓reduceIte, mul_one]
      exact (ν ω).total
  rw [hrest, mul_one]
  simp only [true_or, or_true, ↓reduceIte, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ]
  ring

variable {R D : Type*} [CommRing R] [Fintype R] [DecidableEq R] [Fintype D]

omit [CommRing R] in
theorem sum_sq_uniformOn (A : Finset R) (hA : A.Nonempty) :
    ∑ x, (uniformOn A hA).weight x ^ 2 = 1 / A.card := by
  unfold uniformOn
  simp only [ite_pow, zero_pow two_ne_zero]
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  have : (A.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hA).ne'
  field_simp

section Clique

variable {p : ℕ} [Fact p.Prime] (ℓ : ℕ)

/-- **`lem:frontier:iidlocal`(v), one pair**: under the square-clique law (with `p ≡ 1 (mod 4)`),
two slots in distinct first chambers carry equal labels with probability exactly `2^{-ℓ}`. -/
theorem cliqueLaw_coincidence (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3) {u v : Slot}
    (huv : firstChamber u ≠ firstChamber v) :
    (cliqueLaw p ℓ).expect (fun z => if z u = z v then 1 else 0) = 1 / 2 ^ ℓ := by
  have hS : Nonempty (unitSquares p ℓ) :=
    ⟨⟨(unitSquares_nonempty p ℓ).choose, (unitSquares_nonempty p ℓ).choose_spec⟩⟩
  unfold cliqueLaw affineChamberLaw
  rw [chamberIidLaw_coincidence _ _ huv]
  have hlabel : ∀ q : AffineData (R := ZMod (p ^ (2 * ℓ))) (CliqueData p ℓ) (unitSquares p ℓ),
      ∑ x, (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ) q).weight x ^ 2 =
        1 / 2 ^ ℓ := by
    intro q
    unfold affineLabelLaw
    rw [sum_sq_uniformOn]
    have hinj : Function.Injective fun y : ZMod (p ^ (2 * ℓ)) => (q.2.1 : ZMod _) * y + q.2.2 := by
      intro y y' h
      have hu := unitSquares_isUnit p ℓ q.2.1 q.2.1.2
      have : (q.2.1 : ZMod (p ^ (2 * ℓ))) * y = q.2.1 * y' := by simpa using h
      exact hu.mul_left_cancel this
    rw [card_image_of_injective _ hinj, clique_card ℓ hp2 hp4]
    push_cast
    ring
  simp_rw [hlabel]
  rw [← sum_mul, FiniteLaw.total, one_mul]

/-- **`lem:frontier:iidlocal`(iv), union bound**: for query pairs `(u_k, v_k)` in distinct first
chambers, the exception (some pair coincides) has mass at most `n 2^{-ℓ}`. -/
theorem cliqueLaw_exception_le (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3) {n : ℕ} (u v : Fin n → Slot)
    (huv : ∀ k, firstChamber (u k) ≠ firstChamber (v k)) :
    (cliqueLaw p ℓ).expect (fun z => if ∃ k, z (u k) = z (v k) then 1 else 0) ≤ n / 2 ^ ℓ := by
  have hle : ∀ z : Slot → ZMod (p ^ (2 * ℓ)),
      (if ∃ k, z (u k) = z (v k) then (1 : ℝ) else 0) ≤
        ∑ k, (if z (u k) = z (v k) then 1 else 0) := by
    intro z
    split_ifs with h
    · obtain ⟨k, hk⟩ := h
      calc (1 : ℝ) = if z (u k) = z (v k) then 1 else 0 := by rw [ite_eq_left hk]
        _ ≤ ∑ k', (if z (u k') = z (v k') then 1 else 0) :=
            single_le_sum (f := fun k' => if z (u k') = z (v k') then (1 : ℝ) else 0)
              (fun k' _ => by split_ifs <;> norm_num) (mem_univ k)
    · exact sum_nonneg fun k _ => by split_ifs <;> norm_num
  calc (cliqueLaw p ℓ).expect (fun z => if ∃ k, z (u k) = z (v k) then 1 else 0)
      ≤ (cliqueLaw p ℓ).expect (fun z => ∑ k, (if z (u k) = z (v k) then (1 : ℝ) else 0)) :=
        (cliqueLaw p ℓ).expect_mono hle
    _ = ∑ k, (cliqueLaw p ℓ).expect (fun z => if z (u k) = z (v k) then (1 : ℝ) else 0) := by
        unfold FiniteLaw.expect
        rw [sum_comm]
        exact sum_congr rfl fun z _ => by rw [mul_sum]
    _ = ∑ _k : Fin n, (1 : ℝ) / 2 ^ ℓ :=
        sum_congr rfl fun k _ => cliqueLaw_coincidence ℓ hp2 hp4 (huv k)
    _ = n / 2 ^ ℓ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Clique

end Sarkozy
