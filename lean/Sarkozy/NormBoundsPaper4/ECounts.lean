module

public import Sarkozy.NormBoundsPaper3.MatchSym

@[expose] public section

/-!
# The singleton features of `L²(ν_E)` and their Gram (FD)

`paper/sections/21_middle_records.tex`, `lem:record:e-law`(d) and its proof ("`Π_⊥ δ_{ij} Π_⊥ =
q V_i V_j^*` on mean-zero functions", "`‖V‖² = 1/(1 − q)`"), `lem:record:e-orthogonal`(b)
("`‖h‖² ≥ (1 − 2u)‖c‖²`" for `h = Vc`).

On the injective triples `x = ((x₀, x₁), x₂)` at one prime (NB3's `ind3`), unnormalized:

* `crd i x = x_i`; `Uc u i t = ∑_x [x inj][x_i = t] u(x)` (`p(p − 1)(p − 2)/p` times the
  conditional mean `V_i^* u`); `Tu u = ∑_i ∑_t Uc u i t²`; `Nq u = ∑_x [x inj] u(x)²`;
* the counts: `cnt_one` (`∑_x [x inj] f(x_i) = (p − 1)(p − 2) ∑ f`), **`cnt_two`**
  (`∑_x [x inj] f(x_i) g(x_j) = (p − 2)(∑f ∑g − ∑ fg)` for `i ≠ j`);
* `lift c x = ∑_i c_i(x_i)` (the synthesis `V c`), **`Nq_lift`**, **`Uc_lift`** (the Gram of `V`:
  `V^* V c = (p − 2)(p c_j − ∑_i c_i)` for mean-zero `c_i`), `Nq_lift_ge`
  (`‖Vc‖² ≥ (p − 2)(p − 3) ∑‖c_i‖²`, the paper's `(1 − 2u)`);
* **`Tu_le`**: `Tu u ≤ p(p − 2) Nq u` for mean-zero `u` (the paper's `‖V‖² = 1/(1 − q)`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.NormBoundsPaper3
open Sarkozy.NormBoundsPaper2 (off)

variable {p : ℕ} [Fact p.Prime]

local notation "T3" => (ZMod p × ZMod p) × ZMod p

/-- The coordinate `x_i` of a triple. -/
def crd (i : Fin 3) (x : (ZMod p × ZMod p) × ZMod p) : ZMod p := ![x.1.1, x.1.2, x.2] i

/-- `[a = b]`. -/
noncomputable def dl (a b : ZMod p) : ℝ := if a = b then 1 else 0

/-- `Uc u i t = ∑_x [x inj][x_i = t] u(x)`. -/
noncomputable def Uc (u : T3 → ℝ) (i : Fin 3) (t : ZMod p) : ℝ :=
  ∑ x, ind3 x * dl (crd i x) t * u x

/-- `∑_i ∑_t Uc u i t²`. -/
noncomputable def Tu (u : T3 → ℝ) : ℝ := ∑ i, ∑ t, Uc u i t ^ 2

/-- `∑_x [x inj] u(x)²`. -/
noncomputable def Nq (u : T3 → ℝ) : ℝ := ∑ x, ind3 x * u x ^ 2

/-- The synthesis `V c`: `x ↦ ∑_i c_i(x_i)`. -/
noncomputable def lift (c : Fin 3 → ZMod p → ℝ) (x : T3) : ℝ := ∑ i, c i (crd i x)

/-- `∑_t f(t)²`. -/
noncomputable def n1 (f : ZMod p → ℝ) : ℝ := ∑ t, f t ^ 2

theorem Nq_nonneg (u : T3 → ℝ) : 0 ≤ Nq u :=
  sum_nonneg fun x _ => mul_nonneg (ind3_nonneg x) (sq_nonneg _)

theorem Tu_nonneg (u : T3 → ℝ) : 0 ≤ Tu u :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-! ## Counts -/

theorem sum_mid (a c : ZMod p) : ∑ b, ind3 ((a, b), c) = off (a, c) * ((p : ℝ) - 2) := by
  by_cases hac : a = c
  · subst hac
    have : ∀ b, ind3 ((a, b), a) = 0 := fun b => by unfold ind3 Inj3; simp
    simp [this, off]
  · have e : ∀ b, ind3 ((a, b), c) = 1 - dl b a - dl b c := fun b => by
      unfold ind3 Inj3 dl
      by_cases h1 : b = a
      · subst h1; simp [hac]
      · by_cases h2 : b = c
        · subst h2; simp [h1, hac]
        · simp [Ne.symm h1, Ne.symm h2, h1, h2, Ne.symm hac]
    simp only [e, sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one, dl,
      sum_ite_eq', mem_univ, ↓reduceIte, off, hac]
    ring

theorem sum_fst (b c : ZMod p) : ∑ a, ind3 ((a, b), c) = off (b, c) * ((p : ℝ) - 2) := by
  by_cases hbc : b = c
  · subst hbc
    have : ∀ a, ind3 ((a, b), b) = 0 := fun a => by unfold ind3 Inj3; simp
    simp [this, off]
  · have e : ∀ a, ind3 ((a, b), c) = 1 - dl a b - dl a c := fun a => by
      unfold ind3 Inj3 dl
      by_cases h1 : a = b
      · subst h1; simp [hbc]
      · by_cases h2 : a = c
        · subst h2; simp [h1]
        · simp [Ne.symm h2, h1, h2, Ne.symm hbc]
    simp only [e, sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one, dl,
      sum_ite_eq', mem_univ, ↓reduceIte, off, hbc]
    ring

theorem sum_off_mul (f g : ZMod p → ℝ) :
    ∑ a, ∑ b, off (a, b) * (f a * g b) = (∑ a, f a) * (∑ b, g b) - ∑ t, f t * g t := by
  have e : ∀ a b : ZMod p, off (a, b) * (f a * g b) = f a * g b - dl a b * (f a * g b) :=
    fun a b => by unfold off dl; split_ifs <;> simp_all
  simp only [e, sum_sub_distrib, sum_mul_sum]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  simp only [dl, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]

theorem cnt01 (F : ZMod p → ZMod p → ℝ) :
    ∑ x : T3, ind3 x * F x.1.1 x.1.2 = ((p : ℝ) - 2) * ∑ a, ∑ b, off (a, b) * F a b := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  have h := sum_ind3_fib (X := ZMod p) (a, b)
  rw [ZMod.card] at h
  have e : ∀ y, ind3 ((a, b), y) * F ((a, b), y).1.1 ((a, b), y).1.2 =
      ind3 ((a, b), y) * F a b := fun y => rfl
  rw [sum_congr rfl fun y _ => e y, ← sum_mul, h]
  ring

theorem cnt02 (F : ZMod p → ZMod p → ℝ) :
    ∑ x : T3, ind3 x * F x.1.1 x.2 = ((p : ℝ) - 2) * ∑ a, ∑ c, off (a, c) * F a c := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  have e : ∀ x, ind3 ((a, x), c) * F ((a, x), c).1.1 ((a, x), c).2 =
      ind3 ((a, x), c) * F a c := fun x => rfl
  rw [sum_congr rfl fun x _ => e x, ← sum_mul, sum_mid]
  ring

theorem cnt12 (F : ZMod p → ZMod p → ℝ) :
    ∑ x : T3, ind3 x * F x.1.2 x.2 = ((p : ℝ) - 2) * ∑ b, ∑ c, off (b, c) * F b c := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_comm, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  have e : ∀ x, ind3 ((x, b), c) * F ((x, b), c).1.2 ((x, b), c).2 =
      ind3 ((x, b), c) * F b c := fun x => rfl
  rw [sum_congr rfl fun x _ => e x, ← sum_mul, sum_fst]
  ring

/-- **The pair counts**: for `i ≠ j`, `∑_x [x inj] f(x_i) g(x_j) = (p − 2)(∑f ∑g − ∑ fg)`. -/
theorem cnt_two {i j : Fin 3} (hij : i ≠ j) (f g : ZMod p → ℝ) :
    ∑ x : T3, ind3 x * (f (crd i x) * g (crd j x)) =
      ((p : ℝ) - 2) * ((∑ t, f t) * (∑ t, g t) - ∑ t, f t * g t) := by
  have s1 := sum_off_mul f g
  have s2 := sum_off_mul g f
  have hs : ∀ a b : ZMod p, off (a, b) = off (b, a) := fun a b => by
    unfold off; split_ifs <;> simp_all
  have s2' : ∑ a, ∑ b, off (a, b) * (f b * g a) = (∑ t, f t) * (∑ t, g t) - ∑ t, f t * g t := by
    rw [sum_comm]
    have : ∑ b, ∑ a, off (a, b) * (f b * g a) = ∑ b, ∑ a, off (b, a) * (f b * g a) :=
      sum_congr rfl fun b _ => sum_congr rfl fun a _ => by rw [hs]
    rw [this, s1]
  have s3 : ∑ a, ∑ b, off (a, b) * (g a * f b) = (∑ t, f t) * (∑ t, g t) - ∑ t, f t * g t := by
    rw [s2, mul_comm]
    congr 1
    exact sum_congr rfl fun t _ => mul_comm _ _
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp only [crd]
  · exact (cnt01 (fun a b => f a * g b)).trans (by rw [s1])
  · exact (cnt02 (fun a b => f a * g b)).trans (by rw [s1])
  · refine (sum_congr rfl fun x _ => ?_).trans ((cnt01 (fun a b => g a * f b)).trans
      (by rw [s3]))
    change ind3 x * (f x.1.2 * g x.1.1) = ind3 x * (g x.1.1 * f x.1.2)
    ring
  · exact (cnt12 (fun a b => f a * g b)).trans (by rw [s1])
  · refine (sum_congr rfl fun x _ => ?_).trans ((cnt02 (fun a b => g a * f b)).trans
      (by rw [s3]))
    change ind3 x * (f x.2 * g x.1.1) = ind3 x * (g x.1.1 * f x.2)
    ring
  · refine (sum_congr rfl fun x _ => ?_).trans ((cnt12 (fun a b => g a * f b)).trans
      (by rw [s3]))
    change ind3 x * (f x.2 * g x.1.2) = ind3 x * (g x.1.2 * f x.2)
    ring

/-- **The single counts**: `∑_x [x inj] f(x_i) = (p − 1)(p − 2) ∑ f`. -/
theorem cnt_one (i : Fin 3) (f : ZMod p → ℝ) :
    ∑ x : T3, ind3 x * f (crd i x) = ((p : ℝ) - 1) * ((p : ℝ) - 2) * ∑ t, f t := by
  obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j := ⟨i + 1, by fin_cases i <;> decide⟩
  have h := cnt_two hij f (fun _ => 1)
  simp only [mul_one, sum_const, card_univ, ZMod.card, nsmul_eq_mul] at h
  rw [h]
  ring

/-! ## The features -/

theorem Uc_pair (u : T3 → ℝ) (i : Fin 3) (f : ZMod p → ℝ) :
    ∑ t, f t * Uc u i t = ∑ x, ind3 x * f (crd i x) * u x := by
  unfold Uc
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single (crd i x)]
  · simp [dl]; ring
  · intro t _ ht
    simp [dl, Ne.symm ht]
  · exact fun h => absurd (mem_univ _) h

theorem sum_Uc (u : T3 → ℝ) (i : Fin 3) : ∑ t, Uc u i t = ∑ x, ind3 x * u x := by
  have := Uc_pair u i (fun _ => 1)
  simp only [one_mul, mul_one] at this
  exact this

theorem Tu_eq (u : T3 → ℝ) : Tu u = ∑ x, ind3 x * u x * lift (Uc u) x := by
  unfold Tu lift
  have h : ∀ i, ∑ t, Uc u i t ^ 2 = ∑ x, ind3 x * u x * Uc u i (crd i x) := fun i => by
    have := Uc_pair u i (Uc u i)
    rw [show ∑ t, Uc u i t ^ 2 = ∑ t, Uc u i t * Uc u i t from sum_congr rfl fun t _ => sq _,
      this]
    exact sum_congr rfl fun x _ => by ring
  rw [sum_congr rfl fun i _ => h i, sum_comm]
  exact sum_congr rfl fun x _ => by rw [mul_sum]

/-- `∑_x [x inj] (V c)(x)²` for mean-zero `c_i`. -/
theorem Nq_lift (c : Fin 3 → ZMod p → ℝ) (hc : ∀ i, ∑ t, c i t = 0) :
    Nq (lift c) = ((p : ℝ) - 2) * (((p : ℝ) - 1) * ∑ i, n1 (c i) -
      ∑ i, ∑ j, (if i = j then 0 else ∑ t, c i t * c j t)) := by
  unfold Nq lift
  have e : ∀ x : T3, ind3 x * (∑ i, c i (crd i x)) ^ 2 =
      ∑ i, ∑ j, ind3 x * (c i (crd i x) * c j (crd j x)) := fun x => by
    rw [sq, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun i _ => by rw [mul_sum]
  rw [sum_congr rfl fun x _ => e x, sum_comm]
  have inner : ∀ i, ∑ x : T3, ∑ j, ind3 x * (c i (crd i x) * c j (crd j x)) =
      ((p : ℝ) - 2) * (((p : ℝ) - 1) * n1 (c i) -
        ∑ j, (if i = j then 0 else ∑ t, c i t * c j t)) := fun i => by
    rw [sum_comm]
    have hj : ∀ j, ∑ x : T3, ind3 x * (c i (crd i x) * c j (crd j x)) =
        if i = j then ((p : ℝ) - 1) * ((p : ℝ) - 2) * n1 (c i)
        else -(((p : ℝ) - 2) * ∑ t, c i t * c j t) := fun j => by
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        have := cnt_one i (fun t => c i t ^ 2)
        rw [show n1 (c i) = ∑ t, c i t ^ 2 from rfl, ← this]
        exact sum_congr rfl fun x _ => by ring
      · simp only [hij, ↓reduceIte]
        rw [cnt_two hij, hc i, hc j]
        ring
    rw [sum_congr rfl fun j _ => hj j]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    fin_cases i <;> simp <;> ring
  rw [sum_congr rfl fun i _ => inner i, ← mul_sum, sum_sub_distrib, ← mul_sum]

/-- **The Gram of `V`**: `Uc (V c) j = (p − 2)((p − 1) c_j − ∑_{i ≠ j} c_i)` for mean-zero `c_i`. -/
theorem Uc_lift (c : Fin 3 → ZMod p → ℝ) (hc : ∀ i, ∑ t, c i t = 0) (j : Fin 3) (t : ZMod p) :
    Uc (lift c) j t = ((p : ℝ) - 2) * ((p : ℝ) * c j t - ∑ i, c i t) := by
  unfold Uc lift
  have e : ∀ x : T3, ind3 x * dl (crd j x) t * ∑ i, c i (crd i x) =
      ∑ i, ind3 x * (dl (crd j x) t * c i (crd i x)) := fun x => by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [sum_congr rfl fun x _ => e x, sum_comm]
  have hi : ∀ i, ∑ x : T3, ind3 x * (dl (crd j x) t * c i (crd i x)) =
      if i = j then ((p : ℝ) - 1) * ((p : ℝ) - 2) * c j t
      else -(((p : ℝ) - 2) * c i t) := fun i => by
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      have h := cnt_one i (fun s => dl s t * c i s)
      rw [show ∑ s, dl s t * c i s = c i t by simp [dl]] at h
      rw [← h]
    · simp only [hij, ↓reduceIte]
      rw [cnt_two (Ne.symm hij) (fun s => dl s t) (c i), hc i]
      simp only [dl, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
      ring
  rw [sum_congr rfl fun i _ => hi i]
  fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

/-- `‖V c‖² ≥ (p − 2)(p − 3) ∑ ‖c_i‖²` (the paper's `(1 − 2u)‖c‖²`). -/
theorem Nq_lift_ge (hp : 3 ≤ p) (c : Fin 3 → ZMod p → ℝ) (hc : ∀ i, ∑ t, c i t = 0) :
    ((p : ℝ) - 2) * ((p : ℝ) - 3) * ∑ i, n1 (c i) ≤ Nq (lift c) := by
  rw [Nq_lift c hc]
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have key : ∑ i, ∑ j, (if i = j then (0 : ℝ) else ∑ t, c i t * c j t) ≤ 2 * ∑ i, n1 (c i) := by
    simp only [Fin.sum_univ_three, n1, Fin.isValue, ↓reduceIte]
    simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, zero_add,
      add_zero]
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib,
      ← sum_add_distrib, mul_add, mul_add, mul_sum, mul_sum, mul_sum, ← sum_add_distrib,
      ← sum_add_distrib]
    refine sum_le_sum fun t _ => ?_
    nlinarith [sq_nonneg (c 0 t - c 1 t), sq_nonneg (c 0 t - c 2 t), sq_nonneg (c 1 t - c 2 t)]
  have h2 : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left key h2]

/-- **`‖V^* u‖² ≤ ‖u‖²/(1 − q)`** in unnormalized form: `Tu u ≤ p(p − 2) Nq u` for mean-zero `u`. -/
theorem Tu_le (hp : 3 ≤ p) (u : T3 → ℝ) (hu : ∑ x, ind3 x * u x = 0) :
    Tu u ≤ (p : ℝ) * ((p : ℝ) - 2) * Nq u := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hc : ∀ i, ∑ t, Uc u i t = 0 := fun i => by rw [sum_Uc, hu]
  -- Cauchy–Schwarz
  have hcs : Tu u ^ 2 ≤ Nq u * Nq (lift (Uc u)) := by
    rw [Tu_eq]
    have := sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (ind3 x) * u x)
      (fun x => Real.sqrt (ind3 x) * lift (Uc u) x)
    have e1 : ∀ x, Real.sqrt (ind3 x) * u x * (Real.sqrt (ind3 x) * lift (Uc u) x) =
        ind3 x * u x * lift (Uc u) x := fun x => by
      rw [show Real.sqrt (ind3 x) * u x * (Real.sqrt (ind3 x) * lift (Uc u) x) =
        (Real.sqrt (ind3 x) * Real.sqrt (ind3 x)) * u x * lift (Uc u) x by ring,
        Real.mul_self_sqrt (ind3_nonneg x)]
    have e2 : ∀ (w : T3 → ℝ) x, (Real.sqrt (ind3 x) * w x) ^ 2 = ind3 x * w x ^ 2 :=
      fun w x => by rw [mul_pow, Real.sq_sqrt (ind3_nonneg x)]
    simp only [e1, e2] at this
    exact this
  -- the Gram bound
  have hG : Nq (lift (Uc u)) ≤ (p : ℝ) * ((p : ℝ) - 2) * Tu u := by
    rw [Nq_lift _ hc]
    have key : -(∑ i, ∑ j, (if i = j then (0 : ℝ) else ∑ t, Uc u i t * Uc u j t)) ≤ Tu u := by
      unfold Tu
      simp only [Fin.sum_univ_three, Fin.isValue, ↓reduceIte]
      simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
        show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, zero_add,
        add_zero]
      rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib,
        ← sum_add_distrib, ← sum_neg_distrib, ← sum_add_distrib, ← sum_add_distrib]
      refine sum_le_sum fun t _ => ?_
      nlinarith [sq_nonneg (Uc u 0 t + Uc u 1 t + Uc u 2 t)]
    have h2 : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
    unfold Tu at key ⊢
    simp only [n1]
    nlinarith [mul_le_mul_of_nonneg_left key h2]
  have hT := Tu_nonneg u
  have hN := Nq_nonneg u
  have hpp : (0 : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
  -- `T² ≤ N · p(p − 2) T`
  have h3 : Tu u ^ 2 ≤ (p : ℝ) * ((p : ℝ) - 2) * Nq u * Tu u := by
    have := mul_le_mul_of_nonneg_left hG hN
    nlinarith
  rcases hT.lt_or_eq with hT' | hT'
  · nlinarith
  · rw [← hT']; positivity

end Sarkozy.NormBoundsPaper4
