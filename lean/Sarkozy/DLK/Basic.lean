module

public import Sarkozy.TargetDLK
public import Sarkozy.Extraction.KernelTwoCycles

/-!
# The four-cycle bound from `thm:dl:K` (`cor:dl:normalized`(a), `a = b = 2`)

`paper/sections/15_second_order.tex`. The hypothesis `Target.FourCycle` (`thm:dl:K`, H6, in
`Sarkozy/TargetDLK.lean`) is the eigenvalue bound `|vᵀ M v| ≤ 2p vᵀ v` for the four-cycle matrix
`M` on the ordered pairs of distinct points of `ℙ¹(𝔽_p)`. This file derives from it the form
the formalization uses, `Extraction.FourCycleBound p` (`cor:dl:normalized`(a) with `a = b = 2`,
in `ℓ²` normalization), which was a hypothesis of WP-FI's `lem:matching:kernel`(b)
(`Extraction/KernelTwoCycles.lean`) and of WP-A's matching bound (`Spectral/GlueMatching.lean`).

* `fourCycleMatrix_symm`: `M` is symmetric (`lem:dl:invariance`(a), symmetry part).
* `fourCycleMatrix_some`: for finite points `M(x, z) = χ((z₁ - x₁)(z₁ - x₂)(z₂ - x₁)(z₂ - x₂))`.
* `principal_opBound`: the "in particular" clause of `thm:dl:K`, every principal submatrix of `M`
  has norm at most `2p`.
* `fourCycleAffine_of_fourCycle`: the "in particular" clause of `thm:dl:K` for the principal
  submatrix `M_aff` on the ordered pairs of distinct elements of `𝔽_p`, as a quadratic form
  (`FourCycleAffine`).
* `opBound_of_quadForm`: polarization; for a symmetric matrix, `|vᵀ A v| ≤ c vᵀ v` for all `v`
  gives `‖A v‖ ≤ c ‖v‖` (`OpBound`).
* `fourCycleBound_of_affine`, `fourCycleBound`: the signs `ς_{ab} = ±1` multiply the kernel by
  `∏ χ(ς_{ab}) = ±1` (the first line of the proof of `cor:dl:normalized`), so
  `FourCycleBound p` follows for every odd prime `p`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DLK

open Sarkozy Sarkozy.Target Sarkozy.Influence

variable {p : ℕ} [Fact p.Prime]

/-! ## The matrix `M` -/

/-- `M(x, z) = M(z, x)` (`lem:dl:invariance`(a): `M` is real symmetric). -/
theorem fourCycleMatrix_symm (x z : Option (ZMod p) × Option (ZMod p)) :
    fourCycleMatrix p x z = fourCycleMatrix p z x := by
  unfold fourCycleMatrix wedge
  congr 1
  ring

/-- For finite points, `M(x, z) = χ((z₁ - x₁)(z₁ - x₂)(z₂ - x₁)(z₂ - x₂))`. -/
theorem fourCycleMatrix_some (a b c d : ZMod p) :
    fourCycleMatrix p (some a, some b) (some c, some d) =
      quadraticChar (ZMod p) ((c - a) * (c - b) * ((d - a) * (d - b))) := by
  unfold fourCycleMatrix wedge projRep
  simp only [mul_one, one_mul]

/-! ## The affine principal submatrix -/

/-- The kernel of the affine principal submatrix `M_aff`:
`K(x, z) = χ((z₁ - x₁)(z₁ - x₂)(z₂ - x₁)(z₂ - x₂))` for `x, z ∈ 𝔽_p²`. -/
noncomputable def affineKernel (x z : ZMod p × ZMod p) : ℝ :=
  chiR ((z.1 - x.1) * (z.1 - x.2) * ((z.2 - x.1) * (z.2 - x.2)))

theorem affineKernel_symm (x z : ZMod p × ZMod p) : affineKernel x z = affineKernel z x := by
  unfold affineKernel
  congr 1
  ring

/-- **The "in particular" clause of `thm:dl:K` for `M_aff`**, as a quadratic form: for every
real `v` on `𝔽_p²`, `|∑_{x, z} v(x) K(x, z) v(z)| ≤ 2p ∑_x v(x)²`, the sums over the ordered
pairs of distinct elements of `𝔽_p` (`Extraction.twoCycleOffDiag`). -/
def FourCycleAffine (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ v : ZMod p × ZMod p → ℝ,
    |∑ x ∈ Extraction.twoCycleOffDiag p, ∑ z ∈ Extraction.twoCycleOffDiag p,
        v x * affineKernel x z * v z| ≤
      2 * (p : ℝ) * ∑ x ∈ Extraction.twoCycleOffDiag p, v x ^ 2

/-- The extension of a function on `𝔽_p²` by zero to `ℙ¹ × ℙ¹`. -/
def extendZero (v : ZMod p × ZMod p → ℝ) : Option (ZMod p) × Option (ZMod p) → ℝ
  | (some a, some b) => v (a, b)
  | _ => 0

omit [Fact p.Prime] in
@[simp] theorem extendZero_some (v : ZMod p × ZMod p → ℝ) (a b : ZMod p) :
    extendZero v (some a, some b) = v (a, b) := rfl

/-- A sum over `𝒳` of a function vanishing at the pairs with a point at infinity is the sum over
the ordered pairs of distinct finite points. -/
theorem sum_distinctPairs_of_finite (F : Option (ZMod p) × Option (ZMod p) → ℝ)
    (hF : ∀ x : Option (ZMod p) × Option (ZMod p), x.1 = none ∨ x.2 = none → F x = 0) :
    ∑ x ∈ distinctPairs p, F x =
      ∑ y ∈ Extraction.twoCycleOffDiag p, F (some y.1, some y.2) := by
  unfold distinctPairs Extraction.twoCycleOffDiag
  rw [sum_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_option]
  have h0 : ∀ o : Option (ZMod p), F (none, o) = 0 := fun o => hF _ (Or.inl rfl)
  have h1 : ∀ a : ZMod p, F (some a, none) = 0 := fun a => hF _ (Or.inr rfl)
  simp only [h0, ite_self, sum_const_zero, zero_add, Fintype.sum_option, h1, ne_eq,
    Option.some.injEq]

/-- **`thm:dl:K` ⟹ its "in particular" clause for `M_aff`** (`FourCycleAffine`): restrict the
quadratic form of `M` to the vectors vanishing at the pairs with a point at infinity. -/
theorem fourCycleAffine_of_fourCycle (h : Target.FourCycle) (hp2 : p ≠ 2) :
    FourCycleAffine p := by
  intro v
  have hv := h p hp2 (extendZero v)
  have hzero : ∀ x : Option (ZMod p) × Option (ZMod p), x.1 = none ∨ x.2 = none →
      extendZero v x = 0 := by
    rintro ⟨x1, x2⟩ hx
    rcases hx with hx | hx <;> simp only at hx <;> subst hx
    · rfl
    · cases x1 <;> rfl
  have hinner : ∀ x : Option (ZMod p) × Option (ZMod p),
      ∑ z ∈ distinctPairs p, extendZero v x * (fourCycleMatrix p x z : ℝ) * extendZero v z =
        ∑ w ∈ Extraction.twoCycleOffDiag p,
          extendZero v x * (fourCycleMatrix p x (some w.1, some w.2) : ℝ) * v w := by
    intro x
    rw [sum_distinctPairs_of_finite _ fun z hz => by rw [hzero z hz, mul_zero]]
    rfl
  simp_rw [hinner] at hv
  rw [sum_distinctPairs_of_finite _ fun x hx => by simp only [hzero x hx, zero_mul, sum_const_zero],
    sum_distinctPairs_of_finite _ fun x hx => by rw [hzero x hx]; ring] at hv
  simp only [extendZero_some, Prod.mk.eta] at hv
  convert hv using 4 with y _ w _
  · show v y * affineKernel y w * v w =
      v y * (fourCycleMatrix p (some y.1, some y.2) (some w.1, some w.2) : ℝ) * v w
    rw [fourCycleMatrix_some]
    rfl

/-! ## Polarization -/

/-- **Polarization.** If `A` is symmetric on `S` and `|∑_{x, z ∈ S} v(x) A(x, z) v(z)| ≤ c ∑ v²`
for every `v`, with `c > 0`, then the block `S × S` of `A` has `ℓ²` operator norm at most `c`.
(For `w = A v`: `4c ‖w‖² = Q(w + cv) - Q(w - cv) ≤ c (‖w + cv‖² + ‖w - cv‖²) = 2c ‖w‖² + 2c³ ‖v‖²`.) -/
theorem opBound_of_quadForm {U : Type*} (S : Finset U) (A : U → U → ℝ)
    (hsym : ∀ x ∈ S, ∀ z ∈ S, A x z = A z x) {c : ℝ} (hc : 0 < c)
    (hQ : ∀ v : U → ℝ, |∑ x ∈ S, ∑ z ∈ S, v x * A x z * v z| ≤ c * ∑ x ∈ S, v x ^ 2) :
    OpBound S S A c := by
  intro v
  set w : U → ℝ := fun x => ∑ z ∈ S, A x z * v z with hw
  set u₁ : U → ℝ := fun x => w x + c * v x
  set u₂ : U → ℝ := fun x => w x - c * v x
  have hB : ∑ x ∈ S, ∑ z ∈ S, w x * A x z * v z = ∑ x ∈ S, w x ^ 2 := by
    refine sum_congr rfl fun x _ => ?_
    rw [sq, hw]
    simp only [mul_sum]
    exact sum_congr rfl fun z _ => by ring
  have hB' : ∑ x ∈ S, ∑ z ∈ S, v x * A x z * w z = ∑ x ∈ S, ∑ z ∈ S, w x * A x z * v z := by
    rw [sum_comm]
    exact sum_congr rfl fun x hx => sum_congr rfl fun z hz => by rw [hsym z hz x hx]; ring
  have hdiff : ∑ x ∈ S, ∑ z ∈ S, u₁ x * A x z * u₁ z - ∑ x ∈ S, ∑ z ∈ S, u₂ x * A x z * u₂ z =
      4 * c * ∑ x ∈ S, w x ^ 2 := by
    have e : ∀ x z, u₁ x * A x z * u₁ z - u₂ x * A x z * u₂ z =
        2 * c * (w x * A x z * v z) + 2 * c * (v x * A x z * w z) := fun x z => by
      simp only [u₁, u₂]; ring
    rw [← sum_sub_distrib]
    simp_rw [← sum_sub_distrib, e, sum_add_distrib, ← mul_sum]
    rw [hB', hB]
    ring
  have hnorm : ∑ x ∈ S, u₁ x ^ 2 + ∑ x ∈ S, u₂ x ^ 2 =
      2 * ∑ x ∈ S, w x ^ 2 + 2 * c ^ 2 * ∑ x ∈ S, v x ^ 2 := by
    rw [← sum_add_distrib, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by simp only [u₁, u₂]; ring
  have h1 := (le_abs_self _).trans (hQ u₁)
  have h2 := (neg_abs_le _).trans' (neg_le_neg (hQ u₂))
  have hmain : 2 * c * ∑ x ∈ S, w x ^ 2 ≤ 2 * c * (c ^ 2 * ∑ x ∈ S, v x ^ 2) := by
    nlinarith
  have := le_of_mul_le_mul_left hmain (by positivity)
  simpa only [hw] using this

/-- **The "in particular" clause of `thm:dl:K`**: every principal submatrix of `M` (rows and
columns in a set `S ⊆ 𝒳`) has `ℓ²` operator norm at most `2p`. -/
theorem principal_opBound (h : Target.FourCycle) (hp2 : p ≠ 2)
    {S : Finset (Option (ZMod p) × Option (ZMod p))} (hS : S ⊆ distinctPairs p) :
    OpBound S S (fun x z => (fourCycleMatrix p x z : ℝ)) (2 * (p : ℝ)) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine opBound_of_quadForm S _ (fun x _ z _ => by rw [fourCycleMatrix_symm]) (by positivity)
    fun v => ?_
  set V : Option (ZMod p) × Option (ZMod p) → ℝ := fun x => if x ∈ S then v x else 0 with hV
  have hv := h p hp2 V
  have e1 : ∀ x, ∑ z ∈ distinctPairs p, V x * (fourCycleMatrix p x z : ℝ) * V z =
      ∑ z ∈ S, V x * (fourCycleMatrix p x z : ℝ) * V z := fun x =>
    (sum_subset hS fun z _ hz => by simp [hV, hz]).symm
  simp_rw [e1] at hv
  rw [← sum_subset hS fun x _ hx => by simp [hV, hx],
    ← sum_subset hS fun x _ hx => by simp [hV, hx]] at hv
  have e2 : ∑ x ∈ S, ∑ z ∈ S, V x * (fourCycleMatrix p x z : ℝ) * V z =
      ∑ x ∈ S, ∑ z ∈ S, v x * (fourCycleMatrix p x z : ℝ) * v z :=
    sum_congr rfl fun x hx => sum_congr rfl fun z hz => by simp [hV, hx, hz]
  have e3 : ∑ x ∈ S, V x ^ 2 = ∑ x ∈ S, v x ^ 2 :=
    sum_congr rfl fun x hx => by simp [hV, hx]
  rw [e2, e3] at hv
  exact hv

/-! ## The four-cycle bound with signs -/

/-- The signs multiply the rectangle kernel by `∏_{a,b} χ(ς_{ab})`:
`∏_{a,b ≤ 2} χ(ς_{ab}(y_b - x_a)) = (∏_{a,b} χ(ς_{ab})) K(x, y)`. -/
theorem twoCycleRectangle_eq (ς : Fin 2 → Fin 2 → ZMod p) (x y : ZMod p × ZMod p) :
    Extraction.twoCycleRectangle ς x y = (∏ a : Fin 2, ∏ b : Fin 2, chiR (ς a b)) *
      affineKernel x y := by
  unfold Extraction.twoCycleRectangle affineKernel
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, chiR_mul]
  ring

theorem sign_prod_sq {ς : Fin 2 → Fin 2 → ZMod p} (hς : ∀ a b, ς a b = 1 ∨ ς a b = -1) :
    (∏ a : Fin 2, ∏ b : Fin 2, chiR (ς a b)) ^ 2 = 1 := by
  rw [← prod_pow]
  refine prod_eq_one fun a _ => ?_
  rw [← prod_pow]
  refine prod_eq_one fun b _ => ?_
  rcases chiR_sign (hς a b) with h | h <;> rw [h] <;> norm_num

/-- **`cor:dl:normalized`(a) for `a = b = 2`, `ℓ²` form** (`Extraction.FourCycleBound p`), from
the affine clause of `thm:dl:K`: for all signs `ς_{ab} = ±1`, the rectangle kernel compressed to
the pairs of distinct elements has norm at most `2 √p² = 2p` (`2/p = 2r²` for uniform
probability). -/
theorem fourCycleBound_of_affine (h : FourCycleAffine p) : Extraction.FourCycleBound p := by
  intro ς hς
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [Real.sq_sqrt hp0.le]
  set ε := ∏ a : Fin 2, ∏ b : Fin 2, chiR (ς a b) with hε
  have hε1 : |ε| = 1 := by
    have h2 := sign_prod_sq hς
    rw [← hε] at h2
    have : |ε| ^ 2 = 1 := by rw [sq_abs, h2]
    nlinarith [abs_nonneg ε]
  refine opBound_of_quadForm _ _ (fun x _ z _ => ?_) (by positivity) (fun v => ?_)
  · rw [twoCycleRectangle_eq, twoCycleRectangle_eq, affineKernel_symm]
  · have e : ∑ x ∈ Extraction.twoCycleOffDiag p, ∑ z ∈ Extraction.twoCycleOffDiag p,
        v x * Extraction.twoCycleRectangle ς x z * v z =
        ε * ∑ x ∈ Extraction.twoCycleOffDiag p, ∑ z ∈ Extraction.twoCycleOffDiag p,
          v x * affineKernel x z * v z := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun z _ => by rw [twoCycleRectangle_eq]; ring
    rw [e, abs_mul, hε1, one_mul]
    exact h v

/-- **`Extraction.FourCycleBound p` from `thm:dl:K`** (`Target.FourCycle`), for every odd prime
`p`: the case `a = b = 2` of `cor:dl:normalized`(a), in `ℓ²` normalization. -/
theorem fourCycleBound (h : Target.FourCycle) (hp2 : p ≠ 2) : Extraction.FourCycleBound p :=
  fourCycleBound_of_affine (fourCycleAffine_of_fourCycle h hp2)

/-- `Extraction.FourCycleBound p` for every odd prime `p`, from `thm:dl:K`. -/
theorem fourCycleBound_forall (h : Target.FourCycle) :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → Extraction.FourCycleBound p :=
  fun _ _ hp2 => fourCycleBound h hp2

end Sarkozy.DLK
