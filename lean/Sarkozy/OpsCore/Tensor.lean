module

public import Sarkozy.OpsCore.RecordOp

@[expose] public section

/-!
# Tensor products of operators on product half spaces, and the star-tensor error (OPS-L)

`paper/sections/23_envelopes.tex`, `eq:oct24:star-tensor-error`, Step 1 of the proof of
`thm:envelopes`; the star form (N1)–(N4).

On `L²(⊗_b m_b)` over the product objects `∀ b, O b`:

* `coordOp j A`: the operator `A` acting on the coordinate `j`; **`opNormLE_coordOp`**: it has the
  norm bound of `A` (`m ≥ 0`; fibrewise, through `Equiv.piSplitAt`).
* **`tensorOp A`**: the composition of the coordinate operators over all blocks;
  **`tensorOp_delta`**: `(⊗A δ_y)(x) = ∏_b (A_b δ_{y_b})(x_b)`; **`kern_tensorOp`**: its kernel
  relative to the product marginal is the product of the kernels (the hypothesis `hK` of B11's
  `place_tensor` and `hN4_of_records`); **`opNormLE_tensorOp`**: `‖⊗A_b‖ ≤ ∏ a_b`.
* **`tensorOp_add`**: the expansion `⊗(L_b + E_b) = ∑_t ⊗(E on t, L off t)`.
* **`star_tensor_error`** (`eq:oct24:star-tensor-error`): `Υ = ⊗(L + E) − ⊗L` satisfies
  `|⟨f, Υ f⟩| ≤ (∏(ℓ_b + ρ_b) − ∏ ℓ_b) ‖f‖²` from `‖L_b‖ ≤ ℓ_b`, `‖E_b‖ ≤ ρ_b`.
* **`symm_tensorOp_sub`**: `Υ` is symmetric when every `L_b`, `E_b` has an `ε_b`-symmetric kernel
  (`ε_b = −1` for a skew record) and `∏ ε_b = 1` (an even number of skew factors).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.EnvelopeSteps

/-! ## Norm bounds in `L²(m)` -/

section Norm

variable {O : Type*} [Fintype O]

/-- **The operator norm bound** `‖K g‖_m ≤ a ‖g‖_m` (squared), `a ≥ 0`. -/
def OpNormLE (m : O → ℝ) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (a : ℝ) : Prop :=
  0 ≤ a ∧ ∀ g, ip m (K g) (K g) ≤ a ^ 2 * ip m g g

theorem ip_self_nonneg {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (g : O → ℝ) : 0 ≤ ip m g g :=
  sum_nonneg fun x _ => mul_nonneg (hm x) (mul_self_nonneg _)

theorem ip_comm (m f g : O → ℝ) : ip m f g = ip m g f := by
  unfold ip
  exact sum_congr rfl fun x _ => by ring

/-- Cauchy–Schwarz in `L²(m)`, `m ≥ 0`. -/
theorem abs_ip_le {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (f g : O → ℝ) :
    |ip m f g| ≤ Real.sqrt (ip m f f) * Real.sqrt (ip m g g) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (m x) * f x)
    (fun x => Real.sqrt (m x) * g x)
  have e1 : ∀ x, Real.sqrt (m x) * f x * (Real.sqrt (m x) * g x) = m x * (f x * g x) := by
    intro x
    have := Real.mul_self_sqrt (hm x)
    calc _ = (Real.sqrt (m x) * Real.sqrt (m x)) * (f x * g x) := by ring
      _ = _ := by rw [this]
  have e2 : ∀ (h : O → ℝ) x, (Real.sqrt (m x) * h x) ^ 2 = m x * (h x * h x) := by
    intro h x
    rw [mul_pow, Real.sq_sqrt (hm x)]
    ring
  simp only [e1, e2] at h
  rw [← Real.sqrt_mul (ip_self_nonneg hm f)]
  exact Real.abs_le_sqrt h

/-- A norm bound gives the bilinear bound `|⟨f, K g⟩| ≤ a ‖f‖ ‖g‖` (B8's `FormBound` form). -/
theorem OpNormLE.formLE {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) {K : (O → ℝ) →ₗ[ℝ] (O → ℝ)} {a : ℝ}
    (h : OpNormLE m K a) : FormLE m K a := by
  refine ⟨h.1, fun f g => (abs_ip_le hm f (K g)).trans ?_⟩
  have h1 : Real.sqrt (ip m (K g) (K g)) ≤ a * Real.sqrt (ip m g g) := by
    rw [← Real.sqrt_sq h.1, ← Real.sqrt_mul (sq_nonneg a)]
    exact Real.sqrt_le_sqrt (h.2 g)
  calc Real.sqrt (ip m f f) * Real.sqrt (ip m (K g) (K g))
      ≤ Real.sqrt (ip m f f) * (a * Real.sqrt (ip m g g)) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = a * Real.sqrt (ip m f f) * Real.sqrt (ip m g g) := by ring

/-- The bilinear bound gives the norm bound (take `f = K g`). -/
theorem FormLE.opNormLE {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) {K : (O → ℝ) →ₗ[ℝ] (O → ℝ)} {a : ℝ}
    (h : FormLE m K a) : OpNormLE m K a := by
  refine ⟨h.1, fun g => ?_⟩
  have h1 := h.2 (K g) g
  set u := Real.sqrt (ip m (K g) (K g))
  set v := Real.sqrt (ip m g g)
  have hu : u * u = ip m (K g) (K g) := Real.mul_self_sqrt (ip_self_nonneg hm _)
  have hv : v * v = ip m g g := Real.mul_self_sqrt (ip_self_nonneg hm _)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  rw [abs_of_nonneg (ip_self_nonneg hm _), ← hu] at h1
  -- `u² ≤ a u v` gives `u ≤ a v`
  have h2 : u ≤ a * v := by
    rcases hu0.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact mul_nonneg h.1 hv0
    · nlinarith
  rw [← hu, ← hv]
  nlinarith [mul_nonneg h.1 hv0]

theorem opNormLE_id (m : O → ℝ) : OpNormLE m LinearMap.id 1 :=
  ⟨zero_le_one, fun g => by simp⟩

theorem OpNormLE.comp {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) {K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)} {a b : ℝ}
    (h : OpNormLE m K a) (h' : OpNormLE m K' b) : OpNormLE m (K ∘ₗ K') (a * b) := by
  refine ⟨mul_nonneg h.1 h'.1, fun g => ?_⟩
  have h1 := h.2 (K' g)
  have h2 := mul_le_mul_of_nonneg_left (h'.2 g) (sq_nonneg a)
  have _ := ip_self_nonneg hm g
  simp only [LinearMap.comp_apply]
  calc ip m (K (K' g)) (K (K' g)) ≤ a ^ 2 * ip m (K' g) (K' g) := h1
    _ ≤ a ^ 2 * (b ^ 2 * ip m g g) := h2
    _ = (a * b) ^ 2 * ip m g g := by ring

end Norm

/-! ## Coordinate operators and tensor products -/

variable {S : Type*} [Fintype S] [DecidableEq S] {O : S → Type*} [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)]

/-- **The operator `A` acting on the coordinate `j`** of `∀ b, O b`. -/
noncomputable def coordOp (j : S) (A : (O j → ℝ) →ₗ[ℝ] (O j → ℝ)) :
    ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ) where
  toFun g x := A (fun t => g (Function.update x j t)) (x j)
  map_add' g g' := by
    funext x
    exact congrFun (A.map_add (fun t => g (Function.update x j t))
      (fun t => g' (Function.update x j t))) (x j)
  map_smul' a g := by
    funext x
    exact congrFun (A.map_smul a (fun t => g (Function.update x j t))) (x j)

/-- The splitting of the objects at the coordinate `j`. -/
abbrev splitAt (j : S) := Equiv.piSplitAt j O

omit [Fintype S] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem splitAt_symm_apply_self (j : S) (t : O j) (r : ∀ b : {b // b ≠ j}, O b) :
    (splitAt (O := O) j).symm (t, r) j = t := by
  rw [Equiv.piSplitAt_symm_apply]
  simp

omit [Fintype S] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem update_splitAt_symm (j : S) (t t' : O j) (r : ∀ b : {b // b ≠ j}, O b) :
    Function.update ((splitAt (O := O) j).symm (t, r)) j t' =
      (splitAt (O := O) j).symm (t', r) := by
  funext b
  by_cases hb : b = j
  · subst hb
    rw [Function.update_self, splitAt_symm_apply_self]
  · rw [Function.update_of_ne hb, Equiv.piSplitAt_symm_apply, Equiv.piSplitAt_symm_apply]
    simp [hb]

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem prodWeight_splitAt_symm (m : ∀ b, O b → ℝ) (j : S) (t : O j)
    (r : ∀ b : {b // b ≠ j}, O b) :
    prodWeight m ((splitAt (O := O) j).symm (t, r)) = m j t * ∏ b : {b // b ≠ j}, m b (r b) := by
  unfold prodWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j, splitAt_symm_apply_self]
  congr 1
  refine prod_congr rfl fun b _ => ?_
  rw [Equiv.piSplitAt_symm_apply]
  simp [b.2]

omit [∀ j, DecidableEq (O j)] in
/-- The sum over the objects, split at the coordinate `j`. -/
theorem sum_splitAt (j : S) (F : (∀ b, O b) → ℝ) :
    ∑ x, F x =
      ∑ r : (∀ b : {b // b ≠ j}, O b), ∑ t : O j, F ((splitAt (O := O) j).symm (t, r)) := by
  rw [← Fintype.sum_equiv (splitAt (O := O) j).symm (fun q => F ((splitAt j).symm q)) F
    (fun _ => rfl), Fintype.sum_prod_type, sum_comm]

omit [∀ j, DecidableEq (O j)] in
/-- **A coordinate operator has the norm bound of its factor** (fibrewise, `m ≥ 0`). -/
theorem opNormLE_coordOp {m : ∀ b, O b → ℝ} (hm : ∀ b x, 0 ≤ m b x) (j : S)
    {A : (O j → ℝ) →ₗ[ℝ] (O j → ℝ)} {a : ℝ} (h : OpNormLE (m j) A a) :
    OpNormLE (prodWeight m) (coordOp j A) a := by
  refine ⟨h.1, fun g => ?_⟩
  unfold ip
  rw [sum_splitAt j, sum_splitAt j, mul_sum]
  refine sum_le_sum fun r _ => ?_
  set W := ∏ b : {b // b ≠ j}, m b (r b)
  have hW : 0 ≤ W := prod_nonneg fun b _ => hm b _
  set gr : O j → ℝ := fun t => g ((splitAt (O := O) j).symm (t, r))
  have hact : ∀ t, coordOp j A g ((splitAt (O := O) j).symm (t, r)) = A gr t := by
    intro t
    change A (fun t' => g (Function.update ((splitAt (O := O) j).symm (t, r)) j t'))
      (((splitAt (O := O) j).symm (t, r)) j) = _
    rw [splitAt_symm_apply_self]
    rw [show (fun t' => g (Function.update ((splitAt (O := O) j).symm (t, r)) j t')) = gr from
      funext fun t' => by rw [update_splitAt_symm]]
  have h1 := h.2 gr
  unfold ip at h1
  simp only [prodWeight_splitAt_symm, hact]
  have e1 : ∑ t, m j t * W * (A gr t * A gr t) = W * ∑ t, m j t * (A gr t * A gr t) := by
    rw [mul_sum]
    exact sum_congr rfl fun t _ => by ring
  have e2 : ∑ t, m j t * W * (gr t * gr t) = W * ∑ t, m j t * (gr t * gr t) := by
    rw [mul_sum]
    exact sum_congr rfl fun t _ => by ring
  rw [e1, e2]
  calc W * ∑ t, m j t * (A gr t * A gr t) ≤ W * (a ^ 2 * ∑ t, m j t * (gr t * gr t)) :=
        mul_le_mul_of_nonneg_left h1 hW
    _ = a ^ 2 * (W * ∑ t, m j t * (gr t * gr t)) := by ring

/-- The composition of coordinate operators along a list of blocks. -/
noncomputable def listOp (A : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)) :
    List S → ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)
  | [] => LinearMap.id
  | j :: l => coordOp j (A j) ∘ₗ listOp A l

/-- **The tensor product `⊗_b A_b`** on `∀ b, O b` (the coordinate operators over all blocks). -/
noncomputable def tensorOp (A : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)) :
    ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ) :=
  listOp A (univ : Finset S).toList

omit [∀ j, DecidableEq (O j)] in
theorem opNormLE_listOp {m : ∀ b, O b → ℝ} (hm : ∀ b x, 0 ≤ m b x)
    {A : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)} {a : S → ℝ} (h : ∀ j, OpNormLE (m j) (A j) (a j)) :
    ∀ l : List S, OpNormLE (prodWeight m) (listOp A l) (l.map a).prod
  | [] => opNormLE_id _
  | j :: l => by
    have hpw : ∀ x, 0 ≤ prodWeight m x := fun x => prod_nonneg fun b _ => hm b _
    rw [List.map_cons, List.prod_cons]
    exact (opNormLE_coordOp hm j (h j)).comp hpw (opNormLE_listOp hm h l)

omit [∀ j, DecidableEq (O j)] in
/-- **`‖⊗_b A_b‖ ≤ ∏_b a_b`** in `L²(⊗ m_b)`, `m ≥ 0`. -/
theorem opNormLE_tensorOp {m : ∀ b, O b → ℝ} (hm : ∀ b x, 0 ≤ m b x)
    {A : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)} {a : S → ℝ} (h : ∀ j, OpNormLE (m j) (A j) (a j)) :
    OpNormLE (prodWeight m) (tensorOp A) (∏ j, a j) := by
  have h1 := opNormLE_listOp hm h (univ : Finset S).toList
  rwa [Finset.prod_map_toList] at h1

omit [∀ j, Fintype (O j)] in
/-- The action of `listOp` on a point mass, along a list without repetition. -/
theorem listOp_delta (A : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)) (y : ∀ b, O b) :
    ∀ l : List S, l.Nodup → ∀ x : ∀ b, O b,
      listOp A l (EnvelopeSteps.delta y) x =
        (if ∀ b, b ∉ l → x b = y b then 1 else 0) *
          ∏ b ∈ l.toFinset, A b (EnvelopeSteps.delta (y b)) (x b)
  | [], _, x => by
    simp only [listOp, LinearMap.id_apply, EnvelopeSteps.delta, List.not_mem_nil,
      not_false_eq_true, forall_const, List.toFinset_nil, prod_empty, mul_one]
    congr 1
    exact propext ⟨fun h b => congrFun h b, fun h => funext h⟩
  | j :: l, hnd, x => by
    have hj : j ∉ l := (List.nodup_cons.mp hnd).1
    have hl : l.Nodup := (List.nodup_cons.mp hnd).2
    have ih := listOp_delta A y l hl
    set P := ∏ b ∈ l.toFinset, A b (EnvelopeSteps.delta (y b)) (x b)
    set c : ℝ := if ∀ b, b ∉ j :: l → x b = y b then 1 else 0
    -- the slice at `j` is `c P δ_{y_j}`
    have hslice : (fun t => listOp A l (EnvelopeSteps.delta y) (Function.update x j t)) =
        (c * P) • EnvelopeSteps.delta (y j) := by
      funext t
      rw [ih (Function.update x j t)]
      have hP : ∏ b ∈ l.toFinset, A b (EnvelopeSteps.delta (y b)) (Function.update x j t b) = P :=
        prod_congr rfl fun b hb => by
          rw [Function.update_of_ne (by rintro rfl; exact hj (List.mem_toFinset.mp hb))]
      rw [hP, Pi.smul_apply, smul_eq_mul]
      unfold EnvelopeSteps.delta
      by_cases ht : t = y j
      · subst ht
        have : (∀ b, b ∉ l → Function.update x j (y j) b = y b) ↔
            (∀ b, b ∉ j :: l → x b = y b) := by
          constructor
          · intro h b hb
            have hbj : b ≠ j := fun e => hb (e ▸ List.mem_cons_self)
            have := h b (fun hm => hb (List.mem_cons_of_mem j hm))
            rwa [Function.update_of_ne hbj] at this
          · intro h b hb
            by_cases hbj : b = j
            · subst hbj
              rw [Function.update_self]
            · rw [Function.update_of_ne hbj]
              exact h b (fun hm => by
                rcases List.mem_cons.mp hm with e | e
                · exact hbj e
                · exact hb e)
        simp only [this, c, ↓reduceIte, mul_one]
      · have hfalse : ¬ ∀ b, b ∉ l → Function.update x j t b = y b := by
          intro h
          have := h j hj
          rw [Function.update_self] at this
          exact ht this
        simp only [hfalse, ↓reduceIte, ht, zero_mul, mul_zero]
    change A j (fun t => listOp A l (EnvelopeSteps.delta y) (Function.update x j t)) (x j) = _
    rw [hslice, map_smul, Pi.smul_apply, smul_eq_mul, List.toFinset_cons,
      prod_insert (fun h => hj (List.mem_toFinset.mp h))]
    ring

omit [∀ j, Fintype (O j)] in
/-- **The tensor product on a point mass**: `(⊗A δ_y)(x) = ∏_b (A_b δ_{y_b})(x_b)`. -/
theorem tensorOp_delta (A : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)) (x y : ∀ b, O b) :
    tensorOp A (EnvelopeSteps.delta y) x = ∏ b, A b (EnvelopeSteps.delta (y b)) (x b) := by
  unfold tensorOp
  rw [listOp_delta A y _ (nodup_toList _) x, Finset.toList_toFinset]
  simp

omit [∀ j, Fintype (O j)] in
/-- **The kernel of `⊗A` is the product of the kernels** (the hypothesis `hK` of B11's
`place_tensor`). -/
theorem kern_tensorOp (m : ∀ b, O b → ℝ) (A : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ))
    (x y : ∀ b, O b) :
    kern (prodWeight m) (tensorOp A) x y = ∏ b, kern (m b) (A b) (x b) (y b) := by
  unfold kern prodWeight
  rw [tensorOp_delta, ← prod_mul_distrib]

/-- Two operators with the same action on point masses are equal. -/
theorem linearMap_ext_delta {Q : Type*} [Fintype Q] [DecidableEq Q]
    {K K' : (Q → ℝ) →ₗ[ℝ] (Q → ℝ)}
    (h : ∀ x y, K (EnvelopeSteps.delta y) x = K' (EnvelopeSteps.delta y) x) : K = K' := by
  refine LinearMap.ext fun g => funext fun x => ?_
  rw [apply_eq_sum K g x, apply_eq_sum K' g x]
  exact sum_congr rfl fun y _ => by rw [h x y]

/-- `∏_b (g_b + f_b) = ∑_t ∏_b (f on t, g off t)`. -/
theorem prod_add_ite (f g : S → ℝ) :
    ∏ b, (g b + f b) = ∑ t : Finset S, ∏ b, if b ∈ t then f b else g b := by
  rw [show (∏ b, (g b + f b)) = ∏ b, (f b + g b) from prod_congr rfl fun b _ => add_comm _ _,
    Fintype.prod_add]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_ite]
  congr 1
  · congr 1
    ext b
    simp
  · congr 1
    ext b
    simp

/-- The tensor with `E` on the blocks of `t` and `L` off `t`. -/
noncomputable def mixOp (L E : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)) (t : Finset S) :
    ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ) :=
  tensorOp fun b => if b ∈ t then E b else L b

/-- **The expansion by the set of remainder factors**: `⊗(L_b + E_b) = ∑_t ⊗(E on t, L off t)`. -/
theorem tensorOp_add (L E : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)) :
    tensorOp (fun b => L b + E b) = ∑ t : Finset S, mixOp L E t := by
  refine linearMap_ext_delta fun x y => ?_
  rw [tensorOp_delta, LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.add_apply, Pi.add_apply]
  rw [prod_add_ite]
  refine sum_congr rfl fun t _ => ?_
  rw [mixOp, tensorOp_delta]
  refine prod_congr rfl fun b _ => ?_
  split_ifs <;> rfl

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem mixOp_empty (L E : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)) : mixOp L E ∅ = tensorOp L := by
  simp [mixOp]

/-- **The star-tensor error** (`eq:oct24:star-tensor-error`): with `‖L_b‖ ≤ ℓ_b` and
`‖E_b‖ ≤ ρ_b` in `L²(m_b)`, `m ≥ 0`, the error `Υ = ⊗(L_b + E_b) − ⊗L_b` satisfies
`|⟨f, Υ f⟩| ≤ (∏(ℓ_b + ρ_b) − ∏ ℓ_b) ‖f‖²`. -/
theorem star_tensor_error {m : ∀ b, O b → ℝ} (hm : ∀ b x, 0 ≤ m b x)
    {L E : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)} {ℓ ρ : S → ℝ}
    (hL : ∀ j, OpNormLE (m j) (L j) (ℓ j)) (hE : ∀ j, OpNormLE (m j) (E j) (ρ j))
    (f : (∀ b, O b) → ℝ) :
    |ip (prodWeight m) f ((tensorOp (fun b => L b + E b) - tensorOp L) f)| ≤
      ((∏ b, (ℓ b + ρ b)) - ∏ b, ℓ b) * ip (prodWeight m) f f := by
  have hpw : ∀ x, 0 ≤ prodWeight m x := fun x => prod_nonneg fun b _ => hm b _
  have hff := ip_self_nonneg hpw f
  -- every mixed tensor is bounded
  have hmix : ∀ t : Finset S, |ip (prodWeight m) f (mixOp L E t f)| ≤
      (∏ b, if b ∈ t then ρ b else ℓ b) * ip (prodWeight m) f f := by
    intro t
    have hn : OpNormLE (prodWeight m) (mixOp L E t) (∏ b, if b ∈ t then ρ b else ℓ b) := by
      refine opNormLE_tensorOp hm fun b => ?_
      by_cases hb : b ∈ t
      · simp only [hb, ↓reduceIte]
        exact hE b
      · simp only [hb, ↓reduceIte]
        exact hL b
    have h1 := (hn.formLE hpw).2 f f
    have e : Real.sqrt (ip (prodWeight m) f f) * Real.sqrt (ip (prodWeight m) f f) =
        ip (prodWeight m) f f := Real.mul_self_sqrt hff
    calc _ ≤ _ := h1
      _ = _ := by rw [mul_assoc, e]
  have hsplit : ip (prodWeight m) f ((tensorOp (fun b => L b + E b) - tensorOp L) f) =
      ∑ t ∈ (univ : Finset (Finset S)).erase ∅, ip (prodWeight m) f (mixOp L E t f) := by
    rw [LinearMap.sub_apply, ip_sub_right, tensorOp_add, LinearMap.sum_apply,
      ← add_sum_erase _ _ (mem_univ (∅ : Finset S)), mixOp_empty]
    have : ∀ (s : Finset (Finset S)) (g : Finset S → (∀ b, O b) → ℝ),
        ip (prodWeight m) f (∑ t ∈ s, g t) = ∑ t ∈ s, ip (prodWeight m) f (g t) := by
      intro s g
      induction s using Finset.induction_on with
      | empty => simp [ip]
      | insert a s ha ih => rw [sum_insert ha, sum_insert ha, ip_add_right, ih]
    rw [ip_add_right, this]
    ring
  have hsum : ∑ t ∈ (univ : Finset (Finset S)).erase ∅, (∏ b, if b ∈ t then ρ b else ℓ b) =
      (∏ b, (ℓ b + ρ b)) - ∏ b, ℓ b := by
    rw [prod_add_ite ρ ℓ, ← add_sum_erase _ _ (mem_univ (∅ : Finset S))]
    simp
  rw [hsplit, ← hsum, sum_mul]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => hmix t)

/-- An operator whose kernel is symmetric is symmetric in `L²(m)`. -/
theorem symm_of_kern {Q : Type*} [Fintype Q] [DecidableEq Q] {m : Q → ℝ}
    {K : (Q → ℝ) →ₗ[ℝ] (Q → ℝ)} (h : ∀ x y, kern m K x y = kern m K y x) (f g : Q → ℝ) :
    ip m f (K g) = ip m g (K f) := by
  rw [ip_eq_kern, ip_eq_kern, sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
  rw [h x y]
  ring

/-- **The error tensor is symmetric** when every `L_b` and `E_b` has an `ε_b`-symmetric kernel and
`∏ ε_b = 1` (an even number of skew factors; `thm:envelopes`, Step 1). -/
theorem symm_tensorOp_sub (m : ∀ b, O b → ℝ) {L E : ∀ j, (O j → ℝ) →ₗ[ℝ] (O j → ℝ)}
    (ε : S → ℝ) (hε : ∏ b, ε b = 1)
    (hLs : ∀ b x y, kern (m b) (L b) y x = ε b * kern (m b) (L b) x y)
    (hEs : ∀ b x y, kern (m b) (E b) y x = ε b * kern (m b) (E b) x y) (f g : (∀ b, O b) → ℝ) :
    ip (prodWeight m) f ((tensorOp (fun b => L b + E b) - tensorOp L) g) =
      ip (prodWeight m) g ((tensorOp (fun b => L b + E b) - tensorOp L) f) := by
  refine symm_of_kern (fun x y => ?_) f g
  rw [kern_sub, kern_sub, kern_tensorOp, kern_tensorOp, kern_tensorOp, kern_tensorOp]
  have hA : ∀ b x y, kern (m b) (L b + E b) y x = ε b * kern (m b) (L b + E b) x y := by
    intro b x y
    rw [kern_add, kern_add, hLs, hEs]
    ring
  have h1 : ∏ b, kern (m b) (L b + E b) (y b) (x b) =
      ∏ b, kern (m b) (L b + E b) (x b) (y b) := by
    rw [prod_congr rfl fun b _ => hA b (x b) (y b), prod_mul_distrib, hε, one_mul]
  have h2 : ∏ b, kern (m b) (L b) (y b) (x b) = ∏ b, kern (m b) (L b) (x b) (y b) := by
    rw [prod_congr rfl fun b _ => hLs b (x b) (y b), prod_mul_distrib, hε, one_mul]
  rw [h1, h2]

end Sarkozy.OpsCore
