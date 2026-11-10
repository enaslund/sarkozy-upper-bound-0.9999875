module

public import Sarkozy.TraceMixing.DisjointTriple
public import Sarkozy.TraceMixing.DisjointTripleBound

/-!
# `-3/(n - 3) I ⪯ T` on ordered triples (`sec:frontier:empty-triple-negative`(b))

`paper/sections/12_labellings.tex`, lemma `sec:frontier:empty-triple-negative`(b), for the
operator `T` (`tripleOp`) on the ordered triples `𝒯` of distinct elements of `F`, `n = |F| ≥ 6`:

* `tripleForm_eq`: `∑_{x,y ∈ 𝒯, x ∩ y = ∅} f(x) f(y) = ⟨K F̃, F̃⟩`, where `F̃(S)` is the sum of `f`
  over the six orderings of the `3`-set `S` (`liftTriple`);
* `liftTriple_sq_le`: `∑_S F̃(S)² ≤ 6 ∑_x f(x)²` (Cauchy–Schwarz over the orderings);
* `tripleOp_ge`: **`⟨T f, f⟩ ≥ -3/(n - 3) ⟨f, f⟩`**, from `disjForm_ge`
  (`Sarkozy.TraceMixing.DisjointTripleBound`, which replaces the paper's harmonic decomposition
  by an elementary Cauchy–Schwarz argument). With `tripleOp_le` this is `-3/(n-3) I ⪯ T ⪯ I`.
* `tripleOp_abs_le`: **`‖T - J‖ ≤ 3/(n - 3)`** (`n ≥ 7`): `|⟨T f, f⟩| ≤ 3/(n-3) ⟨f, f⟩` for
  `f` of mean zero, from `disjForm_le_of_mean_zero`.
* `tripleOp_eq_disjOp` (part (a)): `T f(x) = 6⁻¹ T̄ F̃(x)`, so `T` factors through the unordered
  triple.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- The `3`-subsets of `F`. -/
local notation "P3" =>
  Finset.filter (fun S : Finset F => Finset.card S = 3) (Finset.univ : Finset (Finset F))

/-- The underlying set of an ordered triple. -/
def tripleSet (x : Fin 3 → F) : Finset F := univ.image x

theorem tripleSet_mem {x : Fin 3 → F} (hx : Function.Injective x) : tripleSet x ∈ P3 := by
  simp [tripleSet, card_image_of_injective _ hx]

omit [Fintype F] in
theorem disj_iff_disjoint (x y : Fin 3 → F) :
    (∀ i j, x i ≠ y j) ↔ Disjoint (tripleSet x) (tripleSet y) := by
  unfold tripleSet
  rw [disjoint_left]
  constructor
  · intro h a ha hb
    obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    obtain ⟨j, _, hj⟩ := mem_image.mp hb
    exact h i j hj.symm
  · intro h i j hij
    apply h (mem_image_of_mem x (mem_univ i))
    rw [hij]
    exact mem_image_of_mem y (mem_univ j)

/-- `F̃(S) = ∑_{x ∈ 𝒯, x = S as a set} f(x)`. -/
noncomputable def liftTriple (f : (Fin 3 → F) → ℝ) (S : Finset F) : ℝ :=
  ∑ x, if Function.Injective x ∧ tripleSet x = S then f x else 0

omit [Fintype F] [DecidableEq F] in
theorem sum_comm4 {β γ : Type*} (A B : Finset β) (C D : Finset γ) (f : β → β → γ → γ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d
      = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, f a b c d :=
        sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, f a b c d :=
        sum_congr rfl fun a _ => sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, f a b c d := Finset.sum_comm
    _ = ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d :=
        sum_congr rfl fun c _ => Finset.sum_comm

/-- **The form of `T` is the disjointness form of the lift.** -/
theorem tripleForm_eq (f : (Fin 3 → F) → ℝ) :
    ∑ x, ∑ y, (if Function.Injective x ∧ DisjTriple x y then f x * f y else 0) =
      disjForm (liftTriple f) := by
  unfold disjForm liftTriple
  simp only [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  rw [sum_comm4]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases hx : Function.Injective x
  · by_cases hy : Function.Injective y
    · have e2 (S S' : Finset F) : (if Disjoint S S' then (1 : ℝ) else 0) *
          ((if Function.Injective x ∧ tripleSet x = S then f x else 0) *
            (if Function.Injective y ∧ tripleSet y = S' then f y else 0)) =
          if tripleSet y = S' then
            (if tripleSet x = S then (if Disjoint S S' then f x * f y else 0) else 0) else 0 := by
        by_cases h1 : tripleSet x = S <;> by_cases h2 : tripleSet y = S' <;>
          by_cases h3 : Disjoint S S' <;> simp [hx, hy, h1, h2, h3]
      simp only [e2]
      simp only [Finset.sum_ite_eq, tripleSet_mem hx, tripleSet_mem hy, ite_true]
      have hiff : DisjTriple x y ↔ Disjoint (tripleSet x) (tripleSet y) := by
        unfold DisjTriple
        rw [← disj_iff_disjoint]
        exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
      by_cases hd : Disjoint (tripleSet x) (tripleSet y)
      · rw [ite_eq_left hd, ite_eq_left (⟨hx, hiff.mpr hd⟩ : Function.Injective x ∧ DisjTriple x y)]
      · rw [ite_eq_right hd,
          ite_eq_right (fun h : Function.Injective x ∧ DisjTriple x y => hd (hiff.mp h.2))]
    · rw [ite_eq_right (fun h : Function.Injective x ∧ DisjTriple x y => hy h.2.1)]
      symm
      refine Finset.sum_eq_zero fun S _ => Finset.sum_eq_zero fun S' _ => ?_
      rw [ite_eq_right (fun h : Function.Injective y ∧ tripleSet y = S' => hy h.1)]
      ring
  · rw [ite_eq_right (fun h : Function.Injective x ∧ DisjTriple x y => hx h.1)]
    symm
    refine Finset.sum_eq_zero fun S _ => Finset.sum_eq_zero fun S' _ => ?_
    rw [ite_eq_right (fun h : Function.Injective x ∧ tripleSet x = S => hx h.1)]
    ring

/-- A `3`-set has at most `6` orderings. -/
theorem card_orderings_le (S : Finset F) (hS : S.card = 3) :
    (univ.filter fun x : Fin 3 → F => Function.Injective x ∧ tripleSet x = S).card ≤ 6 := by
  rw [← Fintype.card_subtype]
  have hmem (x : {x : Fin 3 → F // Function.Injective x ∧ tripleSet x = S}) (i : Fin 3) :
      x.1 i ∈ S := by
    have h := x.2.2
    have hi : x.1 i ∈ tripleSet x.1 := mem_image_of_mem _ (mem_univ i)
    rwa [h] at hi
  let φ : {x : Fin 3 → F // Function.Injective x ∧ tripleSet x = S} → (Fin 3 ↪ S) :=
    fun x => ⟨fun i => ⟨x.1 i, hmem x i⟩, fun _ _ h => x.2.1 (congrArg Subtype.val h)⟩
  have hφ : Function.Injective φ := by
    intro x x' h
    apply Subtype.ext
    funext i
    have := congrArg (fun e : Fin 3 ↪ S => (e i).1) h
    exact this
  have := Fintype.card_le_of_injective φ hφ
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe, hS] at this
  simpa [Nat.descFactorial] using this

/-- **`∑_S F̃(S)² ≤ 6 ∑_x f(x)²`.** -/
theorem liftTriple_sq_le (f : (Fin 3 → F) → ℝ) :
    ∑ S ∈ P3, liftTriple f S ^ 2 ≤ 6 * ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by
  have hpt (S : Finset F) (hS : S ∈ P3) : liftTriple f S ^ 2 ≤
      6 * ∑ x, (if Function.Injective x ∧ tripleSet x = S then f x ^ 2 else 0) := by
    unfold liftTriple
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ
      (fun x => if Function.Injective x ∧ tripleSet x = S then (1 : ℝ) else 0)
      (fun x => if Function.Injective x ∧ tripleSet x = S then f x else 0)
    have e1 : ∑ x, (if Function.Injective x ∧ tripleSet x = S then (1 : ℝ) else 0) *
        (if Function.Injective x ∧ tripleSet x = S then f x else 0) =
        ∑ x, if Function.Injective x ∧ tripleSet x = S then f x else 0 :=
      sum_congr rfl fun x _ => by split_ifs <;> ring
    have e2 : ∑ x, (if Function.Injective x ∧ tripleSet x = S then (1 : ℝ) else 0) ^ 2 =
        ((univ.filter fun x : Fin 3 → F => Function.Injective x ∧ tripleSet x = S).card : ℝ) := by
      rw [← Finset.sum_boole]
      exact sum_congr rfl fun x _ => by split_ifs <;> ring
    have e3 : ∑ x, (if Function.Injective x ∧ tripleSet x = S then f x else 0) ^ 2 =
        ∑ x, (if Function.Injective x ∧ tripleSet x = S then f x ^ 2 else 0) :=
      sum_congr rfl fun x _ => by split_ifs <;> ring
    rw [e1, e2, e3] at hcs
    have hc : ((univ.filter fun x : Fin 3 → F => Function.Injective x ∧ tripleSet x = S).card : ℝ)
        ≤ 6 := by exact_mod_cast card_orderings_le S (mem_filter.mp hS).2
    have h0 : 0 ≤ ∑ x, (if Function.Injective x ∧ tripleSet x = S then f x ^ 2 else 0) :=
      Finset.sum_nonneg fun x _ => by split_ifs <;> positivity
    exact hcs.trans (mul_le_mul_of_nonneg_right hc h0)
  calc ∑ S ∈ P3, liftTriple f S ^ 2
      ≤ ∑ S ∈ P3, 6 * ∑ x, (if Function.Injective x ∧ tripleSet x = S then f x ^ 2 else 0) :=
        Finset.sum_le_sum hpt
    _ = 6 * ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine sum_congr rfl fun x _ => ?_
        by_cases hx : Function.Injective x
        · rw [ite_eq_left hx]
          have e : ∀ S, (if Function.Injective x ∧ tripleSet x = S then f x ^ 2 else 0) =
              if tripleSet x = S then f x ^ 2 else 0 := fun S => by simp [hx]
          simp only [e]
          rw [Finset.sum_ite_eq, ite_eq_left (tripleSet_mem hx)]
        · rw [ite_eq_right hx]
          exact Finset.sum_eq_zero fun S _ => ite_eq_right (fun h => hx h.1)

/-- **`⟨T f, f⟩ ≥ -3/(n - 3) ⟨f, f⟩`** on `L²(𝒯)` (`n ≥ 6`): with `tripleOp_le`,
`-3/(n-3) I ⪯ T ⪯ I`. -/
theorem tripleOp_ge (hn : 6 ≤ Fintype.card F) (f : (Fin 3 → F) → ℝ) :
    -(3 / ((Fintype.card F : ℝ) - 3)) * ∑ x, (if Function.Injective x then f x ^ 2 else 0) ≤
      ∑ x, (if Function.Injective x then f x * tripleOp f x else 0) := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = k + 6 := ⟨Fintype.card F - 6, by omega⟩
  have hc : ((Fintype.card F - 3).descFactorial 3 : ℝ) = ((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) := by
    have hk3 : Fintype.card F - 3 = k + 3 := by omega
    rw [hk3]
    have hd : (k + 3).descFactorial 3 = (k + 3) * (k + 2) * (k + 1) := by
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
      have e1 : k + 3 - 2 = k + 1 := by omega
      have e2 : k + 3 - 1 = k + 2 := by omega
      rw [e1, e2, Nat.sub_zero]
      ring
    rw [hd]
    push_cast
    ring
  have hform : ∑ x, (if Function.Injective x then f x * tripleOp f x else 0) =
      ((Fintype.card F - 3).descFactorial 3 : ℝ)⁻¹ * disjForm (liftTriple f) := by
    rw [← tripleForm_eq, Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    unfold tripleOp
    by_cases hx : Function.Injective x
    · rw [ite_eq_left hx, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun y _ => ?_
      by_cases hy : DisjTriple x y
      · rw [ite_eq_left hy, ite_eq_left (⟨hx, hy⟩ : Function.Injective x ∧ DisjTriple x y)]
        ring
      · rw [ite_eq_right hy,
          ite_eq_right (fun h : Function.Injective x ∧ DisjTriple x y => hy h.2)]
        ring
    · rw [ite_eq_right hx]
      have : ∑ y, (if Function.Injective x ∧ DisjTriple x y then f x * f y else 0) = 0 :=
        Finset.sum_eq_zero fun y _ => ite_eq_right (fun h => hx h.1)
      rw [this, mul_zero]
  rw [hform, hc]
  have hbound := disjForm_ge hn (liftTriple f)
  have hlift := liftTriple_sq_le f
  have hcast : (Fintype.card F : ℝ) = (k : ℝ) + 6 := by rw [hk]; push_cast; ring
  rw [hcast] at hbound ⊢
  have e1 : (k : ℝ) + 6 - 3 = (k : ℝ) + 3 := by ring
  have e2 : (k : ℝ) + 6 - 4 = (k : ℝ) + 2 := by ring
  have e3 : (k : ℝ) + 6 - 5 = (k : ℝ) + 1 := by ring
  rw [e1]
  rw [e2, e3] at hbound
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 < ((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) := by positivity
  have hC : 0 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 := by positivity
  set Q := ∑ x, (if Function.Injective x then f x ^ 2 else 0)
  set L := ∑ S ∈ P3, liftTriple f S ^ 2
  have h1 : -(((k : ℝ) + 2) * ((k : ℝ) + 1) / 2) * (6 * Q) ≤ disjForm (liftTriple f) := by
    have := mul_le_mul_of_nonneg_left hlift hC
    linarith
  have hk3' : (k : ℝ) + 3 ≠ 0 := by positivity
  calc -(3 / ((k : ℝ) + 3)) * Q
      = (((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1))⁻¹ *
          (-(((k : ℝ) + 2) * ((k : ℝ) + 1) / 2) * (6 * Q)) := by
        field_simp
        ring
    _ ≤ (((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1))⁻¹ * disjForm (liftTriple f) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)

/-- `⟨T f, f⟩ = ((n-3)(n-4)(n-5))⁻¹ ⟨K F̃, F̃⟩`. -/
theorem tripleOp_form (f : (Fin 3 → F) → ℝ) :
    ∑ x, (if Function.Injective x then f x * tripleOp f x else 0) =
      ((Fintype.card F - 3).descFactorial 3 : ℝ)⁻¹ * disjForm (liftTriple f) := by
  rw [← tripleForm_eq, Finset.mul_sum]
  refine sum_congr rfl fun x _ => ?_
  unfold tripleOp
  by_cases hx : Function.Injective x
  · rw [ite_eq_left hx, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases hy : DisjTriple x y
    · rw [ite_eq_left hy, ite_eq_left (⟨hx, hy⟩ : Function.Injective x ∧ DisjTriple x y)]
      ring
    · rw [ite_eq_right hy,
        ite_eq_right (fun h : Function.Injective x ∧ DisjTriple x y => hy h.2)]
      ring
  · rw [ite_eq_right hx]
    have : ∑ y, (if Function.Injective x ∧ DisjTriple x y then f x * f y else 0) = 0 :=
      Finset.sum_eq_zero fun y _ => ite_eq_right (fun h => hx h.1)
    rw [this, mul_zero]

/-- `∑_S F̃(S) = ∑_{x ∈ 𝒯} f(x)`. -/
theorem liftTriple_sum (f : (Fin 3 → F) → ℝ) :
    ∑ S ∈ P3, liftTriple f S = ∑ x, (if Function.Injective x then f x else 0) := by
  unfold liftTriple
  rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : Function.Injective x
  · rw [ite_eq_left hx]
    have e : ∀ S, (if Function.Injective x ∧ tripleSet x = S then f x else 0) =
        if tripleSet x = S then f x else 0 := fun S => by simp [hx]
    simp only [e]
    rw [Finset.sum_ite_eq, ite_eq_left (tripleSet_mem hx)]
  · rw [ite_eq_right hx]
    exact Finset.sum_eq_zero fun S _ => ite_eq_right (fun h => hx h.1)

/-- **`‖T - J‖ ≤ 3/(n - 3)`** on `L²(𝒯)` (`n ≥ 7`): for `f` with `ν`-mean zero,
`|⟨T f, f⟩| ≤ 3/(n-3) ⟨f, f⟩`. -/
theorem tripleOp_abs_le (hn : 7 ≤ Fintype.card F) (f : (Fin 3 → F) → ℝ)
    (hf : ∑ x, (if Function.Injective x then f x else 0) = 0) :
    |∑ x, (if Function.Injective x then f x * tripleOp f x else 0)| ≤
      3 / ((Fintype.card F : ℝ) - 3) * ∑ x, (if Function.Injective x then f x ^ 2 else 0) := by
  have hlo := tripleOp_ge (by omega) f
  rw [abs_le]
  refine ⟨by linarith, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = k + 6 := ⟨Fintype.card F - 6, by omega⟩
  have hc : ((Fintype.card F - 3).descFactorial 3 : ℝ) =
      ((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) := by
    have hk3 : Fintype.card F - 3 = k + 3 := by omega
    rw [hk3]
    have hd : (k + 3).descFactorial 3 = (k + 3) * (k + 2) * (k + 1) := by
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
      have e1 : k + 3 - 2 = k + 1 := by omega
      have e2 : k + 3 - 1 = k + 2 := by omega
      rw [e1, e2, Nat.sub_zero]
      ring
    rw [hd]
    push_cast
    ring
  rw [tripleOp_form, hc]
  have hmean : ∑ S ∈ P3, liftTriple f S = 0 := by rw [liftTriple_sum, hf]
  have hbound := disjForm_le_of_mean_zero hn (liftTriple f) hmean
  have hlift := liftTriple_sq_le f
  have hcast : (Fintype.card F : ℝ) = (k : ℝ) + 6 := by rw [hk]; push_cast; ring
  rw [hcast] at hbound ⊢
  have e1 : (k : ℝ) + 6 - 3 = (k : ℝ) + 3 := by ring
  have e2 : (k : ℝ) + 6 - 4 = (k : ℝ) + 2 := by ring
  have e3 : (k : ℝ) + 6 - 5 = (k : ℝ) + 1 := by ring
  rw [e1]
  rw [e2, e3] at hbound
  have hpos : 0 < ((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1) := by positivity
  have hC : 0 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 := by positivity
  set Q := ∑ x, (if Function.Injective x then f x ^ 2 else 0)
  have h1 : disjForm (liftTriple f) ≤ ((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 * (6 * Q) := by
    have := mul_le_mul_of_nonneg_left hlift hC
    linarith
  have hk3' : (k : ℝ) + 3 ≠ 0 := by positivity
  calc (((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1))⁻¹ * disjForm (liftTriple f)
      ≤ (((k : ℝ) + 3) * ((k : ℝ) + 2) * ((k : ℝ) + 1))⁻¹ *
          (((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 * (6 * Q)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
    _ = 3 / ((k : ℝ) + 3) * Q := by
        field_simp
        ring

/-- **`T` factors through the unordered triple** (`sec:frontier:empty-triple-negative`(a)):
`T f(x) = 6⁻¹ T̄ F̃(x)`, where `F̃` sums `f` over the orderings (`liftTriple`) and `x` is read as
a set. In particular `T f` depends only on `F̃` and on the set of `x`. -/
theorem tripleOp_eq_disjOp (f : (Fin 3 → F) → ℝ) (x : Fin 3 → F) :
    tripleOp f x = 6⁻¹ * disjOp (liftTriple f) (tripleSet x) := by
  have hsum : ∑ y, (if DisjTriple x y then f y else 0) =
      ∑ S' ∈ P3, (if Disjoint (tripleSet x) S' then liftTriple f S' else 0) := by
    unfold liftTriple
    have e (S' : Finset F) : (if Disjoint (tripleSet x) S' then
        ∑ y, (if Function.Injective y ∧ tripleSet y = S' then f y else 0) else 0) =
        ∑ y, (if tripleSet y = S' then
          (if Function.Injective y ∧ Disjoint (tripleSet x) S' then f y else 0) else 0) := by
      split_ifs with hd
      · exact sum_congr rfl fun y _ => by
          by_cases h1 : tripleSet y = S' <;> by_cases h2 : Function.Injective y <;>
            simp [h1, h2, hd]
      · symm
        exact Finset.sum_eq_zero fun y _ => by
          by_cases h1 : tripleSet y = S' <;> simp [h1, hd]
    simp only [e]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun y _ => ?_
    by_cases hy : Function.Injective y
    · rw [Finset.sum_ite_eq, ite_eq_left (tripleSet_mem hy)]
      have hiff : DisjTriple x y ↔
          (Function.Injective y ∧ Disjoint (tripleSet x) (tripleSet y)) := by
        unfold DisjTriple
        rw [disj_iff_disjoint]
      by_cases h : DisjTriple x y
      · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]
    · rw [ite_eq_right (fun h : DisjTriple x y => hy h.1)]
      symm
      exact Finset.sum_eq_zero fun S' _ => by
        by_cases h1 : tripleSet y = S' <;> simp [h1, hy]
  unfold tripleOp disjOp
  rw [hsum]
  have hc : ((Fintype.card F - 3).descFactorial 3 : ℝ) =
      6 * (((Fintype.card F - 3).choose 3 : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    norm_num [Nat.factorial]
  rw [hc, mul_inv, mul_assoc]

end Sarkozy.TraceMixing
