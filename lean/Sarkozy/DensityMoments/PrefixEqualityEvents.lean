module

public import Sarkozy.DensityMoments.IidPrefix
public import Sarkozy.DensityMoments.PrefixDeletion

/-!
# The six query-equality events of the replacement prefix (`thm:density:iid-prefix`(c))

`paper/sections/30_density_moment_upgrade.tex`, proof of `thm:density:iid-prefix`(c). For the
replacement prefix `μ_p = cliqueIidLaw p ℓ` and the six actual queries
`(querySource j, queryTarget j)` (`Slots.lean`), which cross the reserved cut `reservedCut` and
have twelve distinct endpoints:

* `deletedWeight`: `E_p`, the restriction of `μ_p` to the union of the equality events;
* `prefixEta ℓ = 1 - (1 - 2^{-ℓ})^6`;
* `halfMarginal`: `h_p`, the plus-half marginal of `μ_p`;
* `deletion_marginals_iid`: **both reserved-half marginals of `E_p` equal `η h_p`**. Conditional
  on the clique data, the affine map and the labels of one half, the six labels at the other
  endpoints are independent uniform choices among the `2^ℓ` clique elements;
* `iidPrefix_bracket`, `iidPrefix_sym_skew_le`: the bracket of (c) and the operator-norm bounds
  of the symmetric and skew parts of `E_p` (from `PrefixDeletion.lean`);
* `deleted_mass`, `prefixEta_le`, `prefixEta_lt_one`, `remaining_accepts`: `ν_p = μ_p - E_p` is
  nonnegative with mass `1 - η > 0` (`ℓ ≥ 1`), `η ≤ 6 · 2^{-ℓ}`, and on the support of `ν_p` every
  query difference is nonzero, `p^{2i}` times a unit square (`p ≡ 1 (mod 4)`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open CliqueCopies ReflectionCut

/-- Independent pushforwards: the product of images is the image of the product. -/
theorem expect_pi_map {I : Type*} [Fintype I] [DecidableEq I] {Ω X : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (lam : ∀ i, FiniteLaw (Ω i)) (φ : ∀ i, Ω i → X i) (F : (∀ i, X i) → ℝ) :
    (FiniteLaw.pi (fun i => (lam i).map (φ i))).expect F =
      (FiniteLaw.pi lam).expect (fun x => F (fun i => φ i (x i))) := by
  classical
  unfold FiniteLaw.expect
  have hw : ∀ y : ∀ i, X i, (FiniteLaw.pi (fun i => (lam i).map (φ i))).weight y =
      ∑ x : ∀ i, Ω i, if (fun i => φ i (x i)) = y then ∏ i, (lam i).weight (x i) else 0 := by
    intro y
    simp only [FiniteLaw.pi, FiniteLaw.map]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.prod_ite_zero]
    congr 1
    exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩
  simp_rw [hw, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  rfl

/-- Splitting a labelling of the slots of a cut into its two half labellings. -/
def halfSplit {V : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V) (B : Type*) :
    (V → B) ≃ (c.Half → B) × (c.Half → B) where
  toFun x := (fun u => x u.1, fun u => x (c.flip u.1))
  invFun y v := if hv : v ∈ c.half then y.1 ⟨v, hv⟩ else y.2 ⟨c.flip v, (c.crosses v).2 hv⟩
  left_inv x := by
    funext v
    by_cases hv : v ∈ c.half
    · simp only [dite_eq_left hv]
    · simp only [dite_eq_right hv, c.flip_flip]
  right_inv y := by
    refine Prod.ext (funext fun u => ?_) (funext fun u => ?_)
    · simp only [dite_eq_left u.2]
    · simp only [dite_eq_right (c.flip_not_mem u.2)]
      exact congrArg y.2 (Subtype.ext (c.flip_flip u.1))

theorem halfSplit_symm_half {V : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)
    {B : Type*} (y : (c.Half → B) × (c.Half → B)) {v : V} (hv : v ∈ c.half) :
    (halfSplit c B).symm y v = y.1 ⟨v, hv⟩ := by
  change (if hv : v ∈ c.half then y.1 ⟨v, hv⟩ else _) = _
  rw [dite_eq_left hv]

theorem halfSplit_symm_out {V : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)
    {B : Type*} (y : (c.Half → B) × (c.Half → B)) {v : V} (hv : v ∉ c.half) :
    (halfSplit c B).symm y v = y.2 ⟨c.flip v, (c.crosses v).2 hv⟩ := by
  change (if hv : v ∈ c.half then _ else y.2 ⟨c.flip v, (c.crosses v).2 hv⟩) = _
  rw [dite_eq_right hv]

/-- Uniform labellings of a cut split into independent uniform half labellings. -/
theorem expect_uniform_halfSplit {V : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)
    {B : Type*} [Fintype B] [Nonempty B] (Ψ : (V → B) → ℝ) :
    (FiniteLaw.uniform (V → B)).expect Ψ =
      (FiniteLaw.uniform (c.Half → B)).expect (fun xp =>
        (FiniteLaw.uniform (c.Half → B)).expect (fun xm =>
          Ψ ((halfSplit c B).symm (xp, xm)))) := by
  classical
  rw [← expect_uniform_equiv (halfSplit c B).symm, ← FiniteLaw.uniform_product,
    FiniteLaw.expect_product]

/-- **The equality events of independent uniform coordinates**: for an injective `t` and any
targets `a`, `P(∃ j, y (t j) = a j) = 1 - (1 - 1/|B|)^{|J|}`. -/
theorem expect_exists_eq {H J B : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] [Nonempty B] (t : J → H) (ht : Function.Injective t)
    (a : J → B) :
    (FiniteLaw.uniform (H → B)).expect (fun y => if ∃ j, y (t j) = a j then (1 : ℝ) else 0) =
      1 - (1 - 1 / (Fintype.card B : ℝ)) ^ Fintype.card J := by
  set g : J → B → ℝ := fun j b => if b = a j then 0 else 1 with hg
  have h1 : ∀ y : H → B, (if ∃ j, y (t j) = a j then (1 : ℝ) else 0) =
      1 - ∏ j, g j (y (t j)) := by
    intro y
    by_cases hex : ∃ j, y (t j) = a j
    · obtain ⟨j, hj⟩ := hex
      have hz : ∏ j, g j (y (t j)) = 0 :=
        Finset.prod_eq_zero (mem_univ j) (by simp only [hg, hj, ↓reduceIte])
      simp only [show (∃ j, y (t j) = a j) from ⟨j, hj⟩, ↓reduceIte, hz, sub_zero]
    · push Not at hex
      have ho : ∏ j, g j (y (t j)) = 1 :=
        Finset.prod_eq_one fun j _ => by simp only [hg, hex j, ↓reduceIte]
      have hn : ¬ ∃ j, y (t j) = a j := fun ⟨j, hj⟩ => hex j hj
      simp only [hn, ↓reduceIte, ho, sub_self]
  simp_rw [h1]
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
  congr 1
  -- independence of the distinct coordinates `t j`
  set fib : H → Finset J := fun u => univ.filter (fun j => t j = u) with hfib
  have hprod : ∀ y : H → B, ∏ j, g j (y (t j)) = ∏ u, ∏ j ∈ fib u, g j (y u) := by
    intro y
    rw [← Finset.prod_fiberwise univ t (fun j => g j (y (t j)))]
    refine Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun j hj => ?_
    rw [(mem_filter.mp hj).2]
  simp_rw [hprod]
  rw [← pi_uniform (Ω := fun _ : H => B)]
  rw [FiniteLaw.expect_pi_product (fun _ : H => FiniteLaw.uniform B)
    (fun u b => ∏ j ∈ fib u, g j b)]
  have hc : ∀ j, (FiniteLaw.uniform B).expect (g j) = 1 - 1 / (Fintype.card B : ℝ) := by
    intro j
    have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
    rw [FiniteLaw.expect_uniform]
    have hs : ∑ b, g j b = (Fintype.card B : ℝ) - 1 := by
      have : ∀ b, g j b = 1 - (if b = a j then 1 else 0) := by
        intro b
        simp only [hg]
        split_ifs <;> ring
      simp only [this, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
        sum_ite_eq', mem_univ, ↓reduceIte]
    rw [hs]
    field_simp
  have hfac : ∀ u, (FiniteLaw.uniform B).expect (fun b => ∏ j ∈ fib u, g j b) =
      ∏ _j ∈ fib u, (1 - 1 / (Fintype.card B : ℝ)) := by
    intro u
    rcases (fib u).eq_empty_or_nonempty with h0 | ⟨j, hj⟩
    · simp only [h0, prod_empty, FiniteLaw.expect_const]
    · have hsing : fib u = {j} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hj, fun j' hj' => ht ?_⟩
        exact (mem_filter.mp hj').2.trans (mem_filter.mp hj).2.symm
      simp only [hsing, prod_singleton]
      exact hc j
  simp_rw [hfac]
  rw [Finset.prod_fiberwise univ t (fun _ => 1 - 1 / (Fintype.card B : ℝ)), prod_const,
    card_univ]

variable (p : ℕ) [hp : Fact p.Prime] (ℓ : ℕ)

/-- The prefix label is injective in the choice vector. -/
theorem prefixLabel_injective (q : PrefixData p ℓ) : Function.Injective (prefixLabel p ℓ q) := by
  intro x x' h
  have hu := unitSquares_isUnit p ℓ _ q.2.1.2
  unfold prefixLabel at h
  exact cliqueElt_injective ℓ q.1 (hu.mul_left_cancel (add_right_cancel h))

/-- The label law of the replacement prefix is the image of the uniform choice vector. -/
theorem affineLabelLaw_eq_map (q : PrefixData p ℓ) :
    affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ) q =
      (FiniteLaw.uniform (Fin ℓ → Bool)).map (prefixLabel p ℓ q) := by
  apply law_eq_of_expect
  intro F
  rw [expect_affineLabelLaw, FiniteLaw.expect_map]
  rfl

/-- **The replacement prefix as data and independent choice vectors**, for all test functions. -/
theorem expect_cliqueIidLaw (Φ : (Slot → ZMod (p ^ (2 * ℓ))) → ℝ) :
    (cliqueIidLaw p ℓ).expect Φ =
      (FiniteLaw.uniform (PrefixData p ℓ)).expect (fun q =>
        (FiniteLaw.uniform (Slot → Fin ℓ → Bool)).expect (fun x =>
          Φ (fun v => prefixLabel p ℓ q (x v)))) := by
  unfold cliqueIidLaw affineSlotLaw
  rw [expect_slotIidLaw]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  have h := expect_pi_map (fun _ : Slot => FiniteLaw.uniform (Fin ℓ → Bool))
    (fun _ => prefixLabel p ℓ q) Φ
  rw [pi_uniform] at h
  beta_reduce
  rw [← h, affineLabelLaw_eq_map]
  rfl

/-- The union of the six query-equality events. -/
def QueryEq {X : Type*} (z : Slot → X) : Prop :=
  ∃ j : Chamber, z (querySource j) = z (queryTarget j)

instance {X : Type*} [DecidableEq X] (z : Slot → X) : Decidable (QueryEq z) := by
  unfold QueryEq
  infer_instance

/-- `E_p`: the restriction of the replacement prefix to the union of the equality events. -/
noncomputable def deletedWeight (z : Slot → ZMod (p ^ (2 * ℓ))) : ℝ :=
  if QueryEq z then (cliqueIidLaw p ℓ).weight z else 0

/-- `η = 1 - (1 - 2^{-ℓ})^6`. -/
noncomputable def prefixEta : ℝ := 1 - (1 - 1 / (2 : ℝ) ^ ℓ) ^ 6

/-- `h_p`: the actual half marginal of the replacement prefix at the reserved cut. -/
noncomputable def halfMarginal : FiniteLaw (reservedCut.Half → ZMod (p ^ (2 * ℓ))) :=
  (cliqueIidLaw p ℓ).map (fun z v => z v.1)

theorem querySource_mem : ∀ j : Chamber, querySource j ∈ reservedCut.half := by decide

theorem queryTarget_not_mem : ∀ j : Chamber, queryTarget j ∉ reservedCut.half := by decide

/-- The query sources, as plus-half slots. -/
def sourceHalf (j : Chamber) : reservedCut.Half := ⟨querySource j, querySource_mem j⟩

/-- The mirrors of the query targets, as plus-half slots. -/
def targetHalf (j : Chamber) : reservedCut.Half :=
  ⟨reservedCut.flip (queryTarget j), (reservedCut.crosses _).2 (queryTarget_not_mem j)⟩

theorem sourceHalf_injective : Function.Injective sourceHalf := by
  intro j j' h
  have h' : querySource j = querySource j' := congrArg Subtype.val h
  have := query_endpoints_injective (a₁ := (j, false)) (a₂ := (j', false)) (by simpa using h')
  exact congrArg Prod.fst this

theorem targetHalf_injective : Function.Injective targetHalf := by
  intro j j' h
  have h' : reservedCut.flip (queryTarget j) = reservedCut.flip (queryTarget j') :=
    congrArg Subtype.val h
  have h'' : queryTarget j = queryTarget j' := reservedCut.flip.injective h'
  have := query_endpoints_injective (a₁ := (j, true)) (a₂ := (j', true)) (by simpa using h'')
  exact congrArg Prod.fst this

/-- The equality events in half coordinates. -/
theorem queryEq_split (q : PrefixData p ℓ) (xp xm : reservedCut.Half → Fin ℓ → Bool) :
    QueryEq (fun v => prefixLabel p ℓ q ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) v))
      ↔ ∃ j, xm (targetHalf j) = xp (sourceHalf j) := by
  unfold QueryEq
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have h := prefixLabel_injective p ℓ q hj
    rw [halfSplit_symm_half _ _ (querySource_mem j),
      halfSplit_symm_out _ _ (queryTarget_not_mem j)] at h
    exact h.symm
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    simp only
    rw [halfSplit_symm_half _ _ (querySource_mem j),
      halfSplit_symm_out _ _ (queryTarget_not_mem j)]
    exact congrArg (prefixLabel p ℓ q) hj.symm

/-- The probability of the union of the six equality events, given the other half. -/
theorem card_chamber : Fintype.card Chamber = 6 := rfl

theorem expect_queryEq_given (a : Chamber → Fin ℓ → Bool) (t : Chamber → reservedCut.Half)
    (ht : Function.Injective t) :
    (FiniteLaw.uniform (reservedCut.Half → Fin ℓ → Bool)).expect
      (fun y => if ∃ j, y (t j) = a j then (1 : ℝ) else 0) = prefixEta ℓ := by
  rw [expect_exists_eq t ht a, card_chamber, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  unfold prefixEta
  push_cast
  rfl

theorem deletedWeight_eq_ite (Φ : (Slot → ZMod (p ^ (2 * ℓ))) → ℝ) :
    ∑ z, deletedWeight p ℓ z * Φ z =
      (cliqueIidLaw p ℓ).expect (fun z => if QueryEq z then Φ z else 0) := by
  unfold FiniteLaw.expect deletedWeight
  refine sum_congr rfl fun z _ => ?_
  by_cases h : QueryEq z <;> simp only [h, ↓reduceIte, mul_zero, zero_mul]

theorem expect_halfMarginal (F : (reservedCut.Half → ZMod (p ^ (2 * ℓ))) → ℝ) :
    (halfMarginal p ℓ).expect F = (cliqueIidLaw p ℓ).expect (fun z => F (fun v => z v.1)) := by
  unfold halfMarginal
  rw [FiniteLaw.expect_map]
  rfl

/-- The half marginal in data and choice-vector coordinates. -/
theorem expect_halfMarginal_split (F : (reservedCut.Half → ZMod (p ^ (2 * ℓ))) → ℝ) :
    (halfMarginal p ℓ).expect F =
      (FiniteLaw.uniform (PrefixData p ℓ)).expect (fun q =>
        (FiniteLaw.uniform (reservedCut.Half → Fin ℓ → Bool)).expect (fun xp =>
          F (fun v => prefixLabel p ℓ q (xp v)))) := by
  rw [expect_halfMarginal, expect_cliqueIidLaw]
  refine FiniteLaw.expect_congr _ fun q => ?_
  rw [expect_uniform_halfSplit reservedCut]
  refine FiniteLaw.expect_congr _ fun xp => ?_
  have hres : ∀ xm, (fun v : reservedCut.Half =>
      prefixLabel p ℓ q ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) v.1)) =
      fun v => prefixLabel p ℓ q (xp v) := by
    intro xm
    funext v
    rw [halfSplit_symm_half _ _ v.2]
  simp only [hres, FiniteLaw.expect_const]

/-- **The plus-half marginal of `E_p` is `η h_p`.** -/
theorem deletion_plus (F : (reservedCut.Half → ZMod (p ^ (2 * ℓ))) → ℝ) :
    ∑ z, deletedWeight p ℓ z * F (fun v => z v.1) = prefixEta ℓ * (halfMarginal p ℓ).expect F := by
  rw [deletedWeight_eq_ite, expect_halfMarginal_split, expect_cliqueIidLaw,
    ← FiniteLaw.expect_const_mul]
  refine FiniteLaw.expect_congr _ fun q => ?_
  rw [expect_uniform_halfSplit reservedCut, ← FiniteLaw.expect_const_mul]
  refine FiniteLaw.expect_congr _ fun xp => ?_
  have hres : ∀ xm, (fun v : reservedCut.Half =>
      prefixLabel p ℓ q ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) v.1)) =
      fun v => prefixLabel p ℓ q (xp v) := by
    intro xm
    funext v
    rw [halfSplit_symm_half _ _ v.2]
  have hq : ∀ xm, (if QueryEq (fun v => prefixLabel p ℓ q
      ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) v)) then
        F (fun v : reservedCut.Half =>
          prefixLabel p ℓ q ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) v.1))
      else 0) = F (fun v => prefixLabel p ℓ q (xp v)) *
        (if ∃ j, xm (targetHalf j) = xp (sourceHalf j) then 1 else 0) := by
    intro xm
    rw [hres xm]
    by_cases h : ∃ j, xm (targetHalf j) = xp (sourceHalf j)
    · have h' := (queryEq_split p ℓ q xp xm).mpr h
      simp only [h, h', ↓reduceIte, mul_one]
    · have h' : ¬ QueryEq (fun v => prefixLabel p ℓ q
          ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) v)) :=
        fun hh => h ((queryEq_split p ℓ q xp xm).mp hh)
      simp only [h, h', ↓reduceIte, mul_zero]
  simp only [hq]
  rw [FiniteLaw.expect_const_mul,
    expect_queryEq_given ℓ (fun j => xp (sourceHalf j)) targetHalf targetHalf_injective]
  ring

/-- **The minus-half marginal of `E_p` is `η h_p`.** -/
theorem deletion_minus (G : (reservedCut.Half → ZMod (p ^ (2 * ℓ))) → ℝ) :
    ∑ z, deletedWeight p ℓ z * G (fun v => z (reservedCut.flip v.1)) =
      prefixEta ℓ * (halfMarginal p ℓ).expect G := by
  rw [deletedWeight_eq_ite, expect_halfMarginal_split, expect_cliqueIidLaw,
    ← FiniteLaw.expect_const_mul]
  refine FiniteLaw.expect_congr _ fun q => ?_
  rw [expect_uniform_halfSplit reservedCut, expect_comm, ← FiniteLaw.expect_const_mul]
  refine FiniteLaw.expect_congr _ fun xm => ?_
  have hres : ∀ xp, (fun v : reservedCut.Half =>
      prefixLabel p ℓ q ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm)
        (reservedCut.flip v.1))) = fun v => prefixLabel p ℓ q (xm v) := by
    intro xp
    funext v
    rw [halfSplit_symm_out _ _ (reservedCut.flip_not_mem v.2)]
    exact congrArg (fun u => prefixLabel p ℓ q (xm u)) (Subtype.ext (reservedCut.flip_flip v.1))
  have hq : ∀ xp, (if QueryEq (fun v => prefixLabel p ℓ q
      ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) v)) then
        G (fun v : reservedCut.Half => prefixLabel p ℓ q
          ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) (reservedCut.flip v.1)))
      else 0) = G (fun v => prefixLabel p ℓ q (xm v)) *
        (if ∃ j, xp (sourceHalf j) = xm (targetHalf j) then 1 else 0) := by
    intro xp
    rw [hres xp]
    by_cases h : ∃ j, xp (sourceHalf j) = xm (targetHalf j)
    · have h' := (queryEq_split p ℓ q xp xm).mpr (by
        obtain ⟨j, hj⟩ := h
        exact ⟨j, hj.symm⟩)
      simp only [h, h', ↓reduceIte, mul_one]
    · have h' : ¬ QueryEq (fun v => prefixLabel p ℓ q
          ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) v)) := by
        intro hh
        obtain ⟨j, hj⟩ := (queryEq_split p ℓ q xp xm).mp hh
        exact h ⟨j, hj.symm⟩
      simp only [h, h', ↓reduceIte, mul_zero]
  simp only [hq]
  rw [FiniteLaw.expect_const_mul,
    expect_queryEq_given ℓ (fun j => xm (targetHalf j)) sourceHalf sourceHalf_injective]
  ring

/-- **`thm:density:iid-prefix`(c), marginals**: both reserved-half marginals of `E_p` equal
`η h_p`. -/
theorem deletion_marginals_iid :
    DeletionMarginals reservedCut (deletedWeight p ℓ) (prefixEta ℓ) (halfMarginal p ℓ) :=
  ⟨deletion_plus p ℓ, deletion_minus p ℓ⟩

theorem deletedWeight_nonneg (z : Slot → ZMod (p ^ (2 * ℓ))) : 0 ≤ deletedWeight p ℓ z := by
  unfold deletedWeight
  split_ifs
  · exact (cliqueIidLaw p ℓ).nonneg z
  · exact le_rfl

theorem prefixEta_nonneg : 0 ≤ prefixEta ℓ := by
  unfold prefixEta
  have h0 : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ ℓ := by positivity
  have h1 : 1 / (2 : ℝ) ^ ℓ ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have h2 : (1 - 1 / (2 : ℝ) ^ ℓ) ^ 6 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  linarith

/-- `η ≤ 6 · 2^{-ℓ}`. -/
theorem prefixEta_le : prefixEta ℓ ≤ 6 * (1 / (2 : ℝ) ^ ℓ) := by
  unfold prefixEta
  have h0 : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ ℓ := by positivity
  have h1 : 1 / (2 : ℝ) ^ ℓ ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hb := one_add_mul_le_pow (a := -(1 / (2 : ℝ) ^ ℓ)) (by linarith) 6
  push_cast at hb
  linarith

/-- `η < 1` when there is at least one digit pair. -/
theorem prefixEta_lt_one (hℓ : 1 ≤ ℓ) : prefixEta ℓ < 1 := by
  unfold prefixEta
  have h1 : 1 / (2 : ℝ) ^ ℓ < 1 := by
    rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have : 0 < (1 - 1 / (2 : ℝ) ^ ℓ) ^ 6 := pow_pos (by linarith) 6
  linarith

/-- **`ν_p = μ_p - E_p` has mass `1 - η`.** -/
theorem deleted_mass :
    ∑ z, ((cliqueIidLaw p ℓ).weight z - deletedWeight p ℓ z) = 1 - prefixEta ℓ := by
  have h := deletion_plus p ℓ (fun _ => 1)
  simp only [mul_one, FiniteLaw.expect_const] at h
  rw [Finset.sum_sub_distrib, (cliqueIidLaw p ℓ).total, h]

/-- **`ν_p` is nonnegative and accepts all six queries**: on its support every query difference
is nonzero, and (for `p ≡ 1 (mod 4)`) is `p^{2i}` times a unit square with `i < ℓ`. -/
theorem remaining_accepts (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3) (z : Slot → ZMod (p ^ (2 * ℓ)))
    (hz : (cliqueIidLaw p ℓ).weight z - deletedWeight p ℓ z ≠ 0) (j : Chamber) :
    z (querySource j) ≠ z (queryTarget j) ∧
      ∃ i : ℕ, i < ℓ ∧ ∃ w : ZMod (p ^ (2 * ℓ)),
        z (querySource j) - z (queryTarget j) = (p : ZMod (p ^ (2 * ℓ))) ^ (2 * i) * w ∧
          IsUnit w ∧ IsSquare w := by
  unfold deletedWeight at hz
  by_cases hq : QueryEq z
  · simp only [hq, ↓reduceIte, sub_self, ne_eq, not_true_eq_false] at hz
  · simp only [hq, ↓reduceIte, sub_zero] at hz
    have hne : z (querySource j) ≠ z (queryTarget j) := fun h => hq ⟨j, h⟩
    exact ⟨hne, cliqueIidLaw_support_sub p ℓ hp2 hp4 hz hne⟩

theorem remaining_nonneg (z : Slot → ZMod (p ^ (2 * ℓ))) :
    0 ≤ (cliqueIidLaw p ℓ).weight z - deletedWeight p ℓ z := by
  unfold deletedWeight
  split_ifs
  · simp
  · simpa using (cliqueIidLaw p ℓ).nonneg z

/-- **`thm:density:iid-prefix`(c), the bracket**: with `D_p = Diag_ι(h_p)` and
`ν_p = μ_p - E_p`, `[[μ_p + η D_p, ν_p], [ν_p^*, μ_p + η D_p]] ⪰_ι 0` at the reserved cut. -/
theorem iidPrefix_bracket :
    reservedCut.Bracket
      (signedIntegral (cliqueIidLaw p ℓ).weight +
        prefixEta ℓ • signedIntegral (diagLaw reservedCut (halfMarginal p ℓ)).weight)
      (signedIntegral (cliqueIidLaw p ℓ).weight - signedIntegral (deletedWeight p ℓ))
      (signedIntegral (cliqueIidLaw p ℓ).weight +
        prefixEta ℓ • signedIntegral (diagLaw reservedCut (halfMarginal p ℓ)).weight) :=
  deletion_bracket reservedCut (cliqueIidLaw p ℓ) (cliqueIidLaw_positive p ℓ reservedCut)
    (deletedWeight_nonneg p ℓ) (prefixEta_nonneg ℓ) (deletion_marginals_iid p ℓ)

/-- **`thm:density:iid-prefix`(c), operator norms**: the symmetric and skew parts of `E_p` have
operator norm at most `η` between the actual half `L²(h_p)` spaces. -/
theorem iidPrefix_sym_skew_le (F G : (reservedCut.Half → ZMod (p ^ (2 * ℓ))) → ℝ) :
    |(reservedCut.form (signedIntegral (deletedWeight p ℓ)) F G +
        reservedCut.form (signedIntegral (deletedWeight p ℓ)) G F) / 2| ≤
        prefixEta ℓ * (halfL2 (halfMarginal p ℓ) F * halfL2 (halfMarginal p ℓ) G) ∧
      |(reservedCut.form (signedIntegral (deletedWeight p ℓ)) F G -
        reservedCut.form (signedIntegral (deletedWeight p ℓ)) G F) / 2| ≤
        prefixEta ℓ * (halfL2 (halfMarginal p ℓ) F * halfL2 (halfMarginal p ℓ) G) :=
  deletion_sym_skew_le reservedCut (deletedWeight_nonneg p ℓ) (prefixEta_nonneg ℓ)
    (deletion_marginals_iid p ℓ) F G

end Sarkozy.DensityMoments
