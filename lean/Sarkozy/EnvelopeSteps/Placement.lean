module

public import Sarkozy.RecordExpansion.Variance

@[expose] public section

/-!
# The placement map `K ↦ [K]_ω` (`subsec:reflection-averaging`, "Record assignments and placed
measures")

`paper/sections/23_envelopes.tex`, `subsec:reflection-averaging`, the paragraph "Record assignments
and placed measures"; `paper/sections/05_reflection.tex`, `lem:commoncut`(v) (the cut matrix of a
half-local placement is the pull-back).

For a record assignment `ω` on a set `X` of middle blocks, the paper places an operator `K` on
`L²(m_ω)` as the signed measure `[K]_ω` on two-layer labellings whose cut operator at `ι`
relative to `m_ω` is `K`, the slot `(u₀, u₁, ℓ)` receiving the layer-`ℓ` label of the object
`ω(𝔅)(u₀)`. In the finite setting of the formalization:

* the objects form a finite type `O` (the object triples of the blocks of `X`), with the actual
  half marginal `m : O → ℝ` (`m_ω`), and the placement is a map `φ : O → (c.Half → X)` from
  objects to half labellings (the slot map of `ω`, which is half-local);
* an operator is a linear map `K : (O → ℝ) →ₗ[ℝ] (O → ℝ)`; its kernel relative to `m` is
  `kern m K x y = m(x) (K 1_y)(x)`, so that `⟨f, K g⟩_m = ∑_{x,y} f(x) kern(x, y) g(y)`;
* `place c m φ K` puts the mass `kern m K x y` on the labelling that joins `φ x` (plus half) and
  `φ y` (minus half).

Proved here, as the paper states them:

* **`form_place`**: the cut form of `[K]_ω` is the pull-back of `K`:
  `c.form [K] F G = ⟨F ∘ φ, K (G ∘ φ)⟩_m`;
* **linearity** (`place_add`, `place_sub`, `place_smul`, `place_zero`);
* **positivity and monotonicity** (`place_positive`, `place_mono`): `K ⪰ 0` in `L²(m)` gives
  `[K]_ω ⪰_ι 0`, and `K ⪯ K'` gives `[K]_ω ⪯_ι [K']_ω`;
* **`place_id`**: `[I]_ω = Diag_ι(φ_* m)`, the diagonal copy of the half marginal (`Diag_ω`);
* **`place_J`**: `[𝒥]_ω = J_ι(φ_* m)`, the product of the half marginals (`J_ω`), for the
  projection `𝒥` onto the constants of `L²(m)`.

The order on operators is the order of `L²(m)`: `OpPos m K` says that `K` is symmetric and positive
semidefinite for `⟨f, g⟩_m = ∑ m f g`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

open Sarkozy.RecordExpansion

variable {O : Type*} [Fintype O]

/-! ## The space `L²(m)` and its order -/

/-- The bilinear form of `L²(m)`: `⟨f, g⟩_m = ∑_x m(x) f(x) g(x)`. -/
noncomputable def ip (m : O → ℝ) (f g : O → ℝ) : ℝ := ∑ x, m x * (f x * g x)

/-- `K ⪰ 0` in `L²(m)`: symmetric and positive semidefinite for `⟨·,·⟩_m`. -/
structure OpPos (m : O → ℝ) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) : Prop where
  symm : ∀ f g, ip m f (K g) = ip m g (K f)
  nonneg : ∀ f, 0 ≤ ip m f (K f)

/-- `K ⪯ K'` in `L²(m)`. -/
def OpLE (m : O → ℝ) (K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)) : Prop := OpPos m (K' - K)

theorem ip_add_right (m f g g' : O → ℝ) : ip m f (g + g') = ip m f g + ip m f g' := by
  unfold ip
  rw [← sum_add_distrib]
  exact sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring

theorem ip_sub_right (m f g g' : O → ℝ) : ip m f (g - g') = ip m f g - ip m f g' := by
  unfold ip
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun x _ => by simp only [Pi.sub_apply]; ring

theorem ip_smul_right (m f g : O → ℝ) (a : ℝ) : ip m f (a • g) = a * ip m f g := by
  unfold ip
  rw [mul_sum]
  exact sum_congr rfl fun x _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem OpPos.add {m : O → ℝ} {K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (h : OpPos m K)
    (h' : OpPos m K') : OpPos m (K + K') := by
  constructor
  · intro f g
    simp only [LinearMap.add_apply, ip_add_right, h.symm f g, h'.symm f g]
  · intro f
    simp only [LinearMap.add_apply, ip_add_right]
    exact add_nonneg (h.nonneg f) (h'.nonneg f)

theorem OpPos.smul {m : O → ℝ} {K : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (h : OpPos m K) {a : ℝ}
    (ha : 0 ≤ a) : OpPos m (a • K) := by
  constructor
  · intro f g
    simp only [LinearMap.smul_apply, ip_smul_right, h.symm f g]
  · intro f
    simp only [LinearMap.smul_apply, ip_smul_right]
    exact mul_nonneg ha (h.nonneg f)

/-- The identity is positive for `m ≥ 0`. -/
theorem opPos_id {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) : OpPos m LinearMap.id := by
  constructor
  · intro f g
    unfold ip
    exact sum_congr rfl fun x _ => by simp only [LinearMap.id_apply]; ring
  · intro f
    unfold ip
    refine sum_nonneg fun x _ => mul_nonneg (hm x) ?_
    simp only [LinearMap.id_apply]
    exact mul_self_nonneg _

/-! ## The kernel of an operator relative to `m` -/

variable [DecidableEq O]

/-- The indicator `1_y` of a point. -/
def delta (y : O) : O → ℝ := fun z => if z = y then 1 else 0

theorem eq_sum_delta (g : O → ℝ) : g = ∑ y, g y • delta y := by
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, delta, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_univ, ↓reduceIte]

/-- `(K g)(x) = ∑_y g(y) (K 1_y)(x)`. -/
theorem apply_eq_sum (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (g : O → ℝ) (x : O) :
    K g x = ∑ y, g y * K (delta y) x := by
  conv_lhs => rw [eq_sum_delta g, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]

/-- The kernel of `K` relative to `m`: `kern(x, y) = m(x) (K 1_y)(x) = ⟨1_x, K 1_y⟩_m`. -/
noncomputable def kern (m : O → ℝ) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (x y : O) : ℝ :=
  m x * K (delta y) x

/-- `⟨f, K g⟩_m = ∑_{x,y} f(x) kern(x, y) g(y)`. -/
theorem ip_eq_kern (m : O → ℝ) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (f g : O → ℝ) :
    ip m f (K g) = ∑ x, ∑ y, kern m K x y * (f x * g y) := by
  unfold ip kern
  refine sum_congr rfl fun x _ => ?_
  rw [apply_eq_sum K g x, mul_sum, mul_sum]
  exact sum_congr rfl fun y _ => by ring

/-! ## The placement -/

variable {V X : Type*} [Fintype V] [DecidableEq V]

/-- **The placement `[K]_ω`**: the signed law on labellings `V → X` with the mass
`kern m K x y` at the labelling joining `φ x` (plus half of the cut `c`) and `φ y` (minus
half). -/
noncomputable def place (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X))
    (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) : ((V → X) → ℝ) →ₗ[ℝ] ℝ :=
  sampleIntegral (fun q : O × O => kern m K q.1 q.2) (fun q => c.join (φ q.1) (φ q.2))

/-- **The cut form of `[K]_ω` is the pull-back of `K`** (`lem:commoncut`(v)):
`c.form [K] F G = ⟨F ∘ φ, K (G ∘ φ)⟩_m`. -/
theorem form_place (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X))
    (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (F G : (c.Half → X) → ℝ) :
    c.form (place c m φ K) F G = ip m (fun x => F (φ x)) (K (fun y => G (φ y))) := by
  rw [ip_eq_kern]
  change (∑ q : O × O, kern m K q.1 q.2 * (F (fun v => c.join (φ q.1) (φ q.2) v.1) *
    G (fun v => c.join (φ q.1) (φ q.2) (c.flip v.1)))) = _
  simp only [ReflectionCut.join_plus, ReflectionCut.join_minus]
  rw [Fintype.sum_prod_type]

omit [Fintype O] in
theorem kern_add (m : O → ℝ) (K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (x y : O) :
    kern m (K + K') x y = kern m K x y + kern m K' x y := by
  simp only [kern, LinearMap.add_apply, Pi.add_apply]
  ring

omit [Fintype O] in
theorem kern_sub (m : O → ℝ) (K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (x y : O) :
    kern m (K - K') x y = kern m K x y - kern m K' x y := by
  simp only [kern, LinearMap.sub_apply, Pi.sub_apply]
  ring

omit [Fintype O] in
theorem kern_smul (m : O → ℝ) (a : ℝ) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (x y : O) :
    kern m (a • K) x y = a * kern m K x y := by
  simp only [kern, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `[K + K']_ω = [K]_ω + [K']_ω`. -/
theorem place_add (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X))
    (K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)) :
    place c m φ (K + K') = place c m φ K + place c m φ K' := by
  ext Φ
  simp only [place, sampleIntegral, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    kern_add, add_mul, sum_add_distrib]

/-- `[K − K']_ω = [K]_ω − [K']_ω`. -/
theorem place_sub (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X))
    (K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)) :
    place c m φ (K - K') = place c m φ K - place c m φ K' := by
  ext Φ
  simp only [place, sampleIntegral, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
    kern_sub, sub_mul, sum_sub_distrib]

/-- `[a K]_ω = a [K]_ω`. -/
theorem place_smul (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X)) (a : ℝ)
    (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) : place c m φ (a • K) = a • place c m φ K := by
  ext Φ
  simp only [place, sampleIntegral, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    kern_smul, smul_eq_mul, mul_sum, mul_assoc]

/-- `[0]_ω = 0`. -/
theorem place_zero (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X)) :
    place c m φ 0 = 0 := by
  have h := place_smul c m φ 0 0
  rwa [zero_smul, zero_smul] at h

/-- **`K ⪰ 0` in `L²(m)` gives `[K]_ω ⪰_ι 0`.** -/
theorem place_positive (c : ReflectionCut V) {m : O → ℝ} (φ : O → (c.Half → X))
    {K : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (hK : OpPos m K) : c.Positive (place c m φ K) := by
  constructor
  · intro F G
    rw [form_place, form_place]
    exact hK.symm _ _
  · intro F
    rw [form_place]
    exact hK.nonneg _

/-- **Monotonicity** (`subsec:reflection-averaging`): `K ⪯ K'` in `L²(m)` gives
`[K]_ω ⪯_ι [K']_ω`. -/
theorem place_mono (c : ReflectionCut V) {m : O → ℝ} (φ : O → (c.Half → X))
    {K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (h : OpLE m K K') :
    c.Below (place c m φ K) (place c m φ K') := by
  unfold ReflectionCut.Below
  rw [← place_sub]
  exact place_positive c φ h

/-! ## `[I]_ω = Diag_ω` and `[𝒥]_ω = J_ω` -/

/-- The half marginal pushed to half labellings: `(φ_* m)(h) = ∑_{φ x = h} m(x)`. -/
noncomputable def push {H : Type*} [DecidableEq H] (m : O → ℝ) (φ : O → H) (h : H) : ℝ :=
  ∑ x ∈ univ.filter (fun x => φ x = h), m x

omit [DecidableEq O] in
theorem sum_push {H : Type*} [Fintype H] [DecidableEq H] (m : O → ℝ) (φ : O → H)
    (g : H → ℝ) : ∑ h, push m φ h * g h = ∑ x, m x * g (φ x) := by
  unfold push
  simp only [sum_mul]
  rw [← sum_fiberwise univ φ (fun x => m x * g (φ x))]
  refine sum_congr rfl fun h _ => sum_congr rfl fun x hx => ?_
  rw [(mem_filter.mp hx).2]

omit [Fintype O] in
theorem kern_id (m : O → ℝ) (x y : O) :
    kern m LinearMap.id x y = if x = y then m x else 0 := by
  simp only [kern, LinearMap.id_apply, delta, mul_ite, mul_one, mul_zero]

variable [Fintype X] [DecidableEq X]

/-- **`[I]_ω = Diag_ι(φ_* m)`**: the identity is placed as the diagonal copy of the half
marginal. -/
theorem place_id (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X)) :
    place c m φ LinearMap.id = c.diagonalLaw (push m φ) := by
  refine LinearMap.ext fun Φ => ?_
  change (∑ q : O × O, kern m LinearMap.id q.1 q.2 * Φ (c.join (φ q.1) (φ q.2))) =
    ∑ h, push m φ h * Φ (c.join h h)
  rw [sum_push m φ (fun h => Φ (c.join h h)), Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  simp only [kern_id, ite_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]

/-- The projection `𝒥 g = (∑ m g / ∑ m) 1` onto the constants of `L²(m)`. -/
noncomputable def Jproj (m : O → ℝ) : (O → ℝ) →ₗ[ℝ] (O → ℝ) where
  toFun g := fun _ => (∑ x, m x * g x) / ∑ x, m x
  map_add' f g := by
    funext z
    simp only [Pi.add_apply, mul_add, sum_add_distrib, add_div]
  map_smul' a g := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm, ← mul_sum,
      mul_div_assoc]

theorem kern_J (m : O → ℝ) (x y : O) : kern m (Jproj m) x y = m x * m y / ∑ z, m z := by
  simp only [kern, Jproj, LinearMap.coe_mk, AddHom.coe_mk, delta, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, ↓reduceIte]
  ring

/-- **`[𝒥]_ω = J_ι(φ_* m)`**: the projection onto the constants is placed as the product of the
half marginals. -/
theorem place_J (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X)) :
    place c m φ (Jproj m) = indepLaw c (push m φ) := by
  refine LinearMap.ext fun Φ => ?_
  change (∑ q : O × O, kern m (Jproj m) q.1 q.2 * Φ (c.join (φ q.1) (φ q.2))) =
    (1 / ∑ h, push m φ h) * ∑ q : (c.Half → X) × (c.Half → X),
      push m φ q.1 * push m φ q.2 * Φ (c.join q.1 q.2)
  have htot : ∑ h, push m φ h = ∑ x, m x := by
    have := sum_push m φ (fun _ => 1)
    simpa only [mul_one] using this
  rw [htot, Fintype.sum_prod_type, Fintype.sum_prod_type, mul_sum]
  simp only [kern_J]
  have e1 : ∀ h₁ : c.Half → X, ∑ h₂, push m φ h₁ * push m φ h₂ * Φ (c.join h₁ h₂) =
      push m φ h₁ * ∑ y, m y * Φ (c.join h₁ (φ y)) := by
    intro h₁
    rw [← sum_push m φ (fun h₂ => Φ (c.join h₁ h₂)), mul_sum]
    exact sum_congr rfl fun h₂ _ => by ring
  simp only [e1]
  rw [← mul_sum, sum_push m φ (fun h₁ => ∑ y, m y * Φ (c.join h₁ (φ y))), mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  ring

end Sarkozy.EnvelopeSteps
