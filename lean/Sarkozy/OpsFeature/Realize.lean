module

public import Sarkozy.OpsFeature.Label3

@[expose] public section

/-!
# The realization of `L²(m)` in W2's space and the couplings as projections

`paper/sections/23_envelopes.tex`, `lem:oct24:pure-pair-substitute` and
`lem:oct24:mask-schur`(a): the couplings `M_aa = P_a`, `P₁₂`, `𝒥` of a fold factor are the
conditional expectations (orthogonal projections of `L²(m)`) onto the functions of `x_a`, of
`(x₁, x₂)`, and the constants; `V_a V_a^* = P_a − 𝒥`,
`Q₁₂ = P₁₂ − (P₁ + P₂)/(1 + ρ) + ((1 − ρ)/(1 + ρ))𝒥`.

For a weight `m ≥ 0` on a finite `O`:
* `embW m f = √m · f ∈ EuclideanSpace ℝ O` (`inner_embW`: `⟪embW f, embW g⟫ = ⟨f, g⟩_m`);
* `condExp m π`: the conditional expectation on the fibres of `π : O → A`; `coordSpace m π`, the
  image of the functions of `π`; **`starProjection_coordSpace`**: `Π_{coordSpace} (embW f) =
  embW (E[f | π])`;
* `qOp`: the substitute `Q₁₂` in conditional expectations; **`pureSubstitute_embW`**;
* `hcor_embW`, `embW_mem_pureSpace`: W2's hypotheses from statements in `L²(m)`;
* **`label3_realized`**, **`singleton_realized`**: `label3_le_substitute` and `singleton_le_proj`
  with W2's space `E = EuclideanSpace ℝ O` and the projections realized, so that every hypothesis
  is a statement in `L²(m)`: the correlation of the centred functions of `x₁` and `x₂` (`hcor`,
  edge `12`), the arms `y_{p,z}` functions of `(x₁, x₂)` orthogonal to the functions of `x₁` and of
  `x₂` (`𝒦₁₂`), orthogonal across the sectors, contractions, and `Ξ_p(x, z) = m(x) y_{p,z}(x)`.
-/

open Finset Matrix
open scoped BigOperators RealInnerProductSpace

namespace Sarkozy.OpsFeature

open Sarkozy.Envelopes Sarkozy.EnvelopeSteps

section Realize

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- **The realization of `L²(m)`**: `f ↦ √m · f`. -/
noncomputable def embW (m : O → ℝ) : (O → ℝ) →ₗ[ℝ] EuclideanSpace ℝ O where
  toFun f := WithLp.toLp 2 (fun x => Real.sqrt (m x) * f x)
  map_add' f g := by
    rw [← WithLp.toLp_add]
    congr 1
    funext x
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    rw [← WithLp.toLp_smul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [DecidableEq O] in
theorem inner_embW {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (f g : O → ℝ) :
    ⟪embW m f, embW m g⟫ = ip m f g := by
  simp only [embW, LinearMap.coe_mk, AddHom.coe_mk, EuclideanSpace.inner_toLp_toLp, dotProduct,
    star_trivial, ip]
  refine sum_congr rfl fun x _ => ?_
  have := Real.mul_self_sqrt (hm x)
  calc Real.sqrt (m x) * g x * (Real.sqrt (m x) * f x)
      = (Real.sqrt (m x) * Real.sqrt (m x)) * (f x * g x) := by ring
    _ = m x * (f x * g x) := by rw [this]

variable {A : Type*} [DecidableEq A]

/-- The marginal of `m` on the fibres of `π`. -/
noncomputable def margW (m : O → ℝ) (π : O → A) (a : A) : ℝ :=
  ∑ y, if π y = a then m y else 0

/-- **The conditional expectation** `E[f | π]`. -/
noncomputable def condExp (m : O → ℝ) (π : O → A) : (O → ℝ) →ₗ[ℝ] (O → ℝ) where
  toFun f x := (margW m π (π x))⁻¹ * ∑ y, if π y = π x then m y * f y else 0
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, mul_add, ite_add_zero, sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    split_ifs <;> ring

/-- The image of the functions of `π` in the realization. -/
noncomputable def coordSpace (m : O → ℝ) (π : O → A) : Submodule ℝ (EuclideanSpace ℝ O) :=
  LinearMap.range ((embW m).comp (LinearMap.funLeft ℝ ℝ π))

omit [DecidableEq O] in
/-- `E[f | π]` is a function of `π`. -/
theorem condExp_eq_funLeft (m : O → ℝ) (π : O → A) (f : O → ℝ) :
    condExp m π f = LinearMap.funLeft ℝ ℝ π
      (fun a => (margW m π a)⁻¹ * ∑ y, if π y = a then m y * f y else 0) := rfl

omit [DecidableEq O] in
/-- `⟨f − E[f | π], g ∘ π⟩_m = 0`. -/
theorem ip_condExp {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π : O → A) (f : O → ℝ) (g : A → ℝ) :
    ip m (condExp m π f) (fun x => g (π x)) = ip m f (fun x => g (π x)) := by
  have hmarg : ∀ y, margW m π (π y) = 0 → m y = 0 := by
    intro y hy
    have hle : m y ≤ margW m π (π y) := by
      unfold margW
      have := single_le_sum (f := fun z => if π z = π y then m z else 0)
        (fun z _ => by split_ifs <;> simp [hm z]) (mem_univ y)
      simpa using this
    exact le_antisymm (hy ▸ hle) (hm y)
  unfold ip condExp
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- `∑_x m x (M⁻¹ ∑_y [π y = π x] m y f y) g(π x) = ∑_y m y f y g(π y)`
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  have e2 : ∀ x, m x * ((margW m π (π x))⁻¹ * (if π y = π x then m y * f y else 0) * g (π x)) =
      (if π x = π y then m x else 0) * ((margW m π (π y))⁻¹ * (m y * f y * g (π y))) := by
    intro x
    by_cases h : π x = π y
    · simp only [h, ↓reduceIte]
      ring
    · have h' : ¬ π y = π x := fun e => h e.symm
      simp only [h, h', ↓reduceIte, mul_zero, zero_mul]
  simp only [e2, ← sum_mul]
  change margW m π (π y) * _ = _
  by_cases h0 : margW m π (π y) = 0
  · rw [hmarg y h0]; simp
  · rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]; ring

omit [DecidableEq O] in
/-- **The coupling is the orthogonal projection**: `Π_{coordSpace π}(embW f) = embW(E[f | π])`. -/
theorem starProjection_coordSpace {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π : O → A) (f : O → ℝ) :
    (coordSpace m π).starProjection (embW m f) = embW m (condExp m π f) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [condExp_eq_funLeft]
    exact ⟨_, rfl⟩
  · rintro w ⟨g, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [← map_sub, inner_embW hm]
    unfold ip
    simp only [Pi.sub_apply, LinearMap.funLeft_apply]
    have := ip_condExp hm π f g
    unfold ip at this
    simp only [mul_sub, sub_mul, sum_sub_distrib]
    rw [this]
    ring

omit [Fintype O] [DecidableEq O] [DecidableEq A] in
/-- Functions of `κ ∘ π` are functions of `π`. -/
theorem coordSpace_mono {B : Type*} (m : O → ℝ) (π : O → A) (κ : A → B) :
    coordSpace m (fun x => κ (π x)) ≤ coordSpace m π := by
  rintro w ⟨g, rfl⟩
  exact ⟨fun a => g (κ a), rfl⟩

end Realize

/-! ## The substitute `Q₁₂` and the singleton units, realized -/

section Units

variable {O : Type*} [Fintype O] {A1 A2 : Type*} [DecidableEq A1] [DecidableEq A2]

/-- The constants. -/
def piC : O → Unit := fun _ => ()

/-- **The substitute `Q₁₂`** in conditional expectations, for the pair `π₁₂ = (x₁, x₂)`. -/
noncomputable def qOp (m : O → ℝ) (π12 : O → A1 × A2) (ρ : ℝ) : (O → ℝ) →ₗ[ℝ] (O → ℝ) :=
  condExp m π12 - (1 + ρ)⁻¹ • (condExp m (fun x => (π12 x).1) + condExp m (fun x => (π12 x).2)) +
    ((1 - ρ) / (1 + ρ)) • condExp m (piC (O := O))

/-- **The singleton unit `V_a V_a^* = P_a − 𝒥`** in conditional expectations. -/
noncomputable def uOp {Aa : Type*} [DecidableEq Aa] (m : O → ℝ) (πa : O → Aa) :
    (O → ℝ) →ₗ[ℝ] (O → ℝ) :=
  condExp m πa - condExp m (piC (O := O))

theorem pureSubstitute_embW {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π12 : O → A1 × A2) (ρ : ℝ)
    (f : O → ℝ) :
    pureSubstitute (coordSpace m (piC (O := O))) (coordSpace m fun x => (π12 x).1)
        (coordSpace m fun x => (π12 x).2) (coordSpace m π12) ρ (embW m f) =
      embW m (qOp m π12 ρ f) := by
  simp only [pureSubstitute, _root_.add_apply, _root_.sub_apply,
    _root_.smul_apply, starProjection_coordSpace hm, qOp, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub, map_smul]

theorem featureSpace_embW {Aa : Type*} [DecidableEq Aa] {m : O → ℝ} (hm : ∀ x, 0 ≤ m x)
    (πa : O → Aa) (f : O → ℝ) :
    (featureSpace (coordSpace m (piC (O := O))) (coordSpace m πa)).starProjection (embW m f) =
      embW m (uOp m πa f) := by
  rw [← proj_sub_proj_of_le (coordSpace_mono m πa (fun _ => ())), starProjection_coordSpace hm,
    starProjection_coordSpace hm, uOp, LinearMap.sub_apply, map_sub]

omit [DecidableEq A1] [DecidableEq A2] in
theorem ip_comm (m f g : O → ℝ) : ip m f g = ip m g f := by
  unfold ip
  exact sum_congr rfl fun x _ => by ring

end Units

/-! ## `hUa` with the realization -/

section Labels

variable {O : Type*} [Fintype O] [DecidableEq O] {A1 A2 : Type*} [DecidableEq A1]
  [DecidableEq A2]

omit [DecidableEq O] [DecidableEq A1] [DecidableEq A2] in
theorem norm_embW {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (f : O → ℝ) :
    ‖embW m f‖ = Real.sqrt (ip m f f) := by
  rw [← inner_embW hm, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq O] [DecidableEq A1] [DecidableEq A2] in
/-- The correlation hypothesis of W2 in the realization, from the correlation of the centred
functions of `x₁` and `x₂` in `L²(m)` (edge `12`). -/
theorem hcor_embW {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π12 : O → A1 × A2) {ρ : ℝ}
    (hcor : ∀ (u : A1 → ℝ) (v : A2 → ℝ), ip m (fun x => u (π12 x).1) (fun _ => 1) = 0 →
      ip m (fun x => v (π12 x).2) (fun _ => 1) = 0 →
      |ip m (fun x => u (π12 x).1) (fun x => v (π12 x).2)| ≤
        ρ * Real.sqrt (ip m (fun x => u (π12 x).1) (fun x => u (π12 x).1)) *
          Real.sqrt (ip m (fun x => v (π12 x).2) (fun x => v (π12 x).2))) :
    ∀ f ∈ featureSpace (coordSpace m (piC (O := O))) (coordSpace m fun x => (π12 x).1),
      ∀ h ∈ featureSpace (coordSpace m (piC (O := O))) (coordSpace m fun x => (π12 x).2),
        |⟪f, h⟫| ≤ ρ * ‖f‖ * ‖h‖ := by
  rintro f ⟨⟨u, rfl⟩, hf⟩ h ⟨⟨v, rfl⟩, hh⟩
  have hc1 : ⟪(embW m) ((LinearMap.funLeft ℝ ℝ fun x => (π12 x).1) u),
      embW m (fun _ => 1)⟫ = 0 := by
    have hmem : embW m (fun _ : O => (1 : ℝ)) ∈ coordSpace m (piC (O := O)) :=
      ⟨fun _ => 1, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hmem hf |> fun e => by
      rw [real_inner_comm]; exact e
  have hc2 : ⟪(embW m) ((LinearMap.funLeft ℝ ℝ fun x => (π12 x).2) v),
      embW m (fun _ => 1)⟫ = 0 := by
    have hmem : embW m (fun _ : O => (1 : ℝ)) ∈ coordSpace m (piC (O := O)) :=
      ⟨fun _ => 1, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hmem hh |> fun e => by
      rw [real_inner_comm]; exact e
  simp only [LinearMap.comp_apply] at hc1 hc2 ⊢
  rw [inner_embW hm] at hc1 hc2 ⊢
  rw [norm_embW hm, norm_embW hm]
  exact hcor u v hc1 hc2

omit [DecidableEq O] in
theorem ip_qOp {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π12 : O → A1 × A2) (ρ : ℝ) (f : O → ℝ) :
    ip m f (qOp m π12 ρ f) =
      ⟪pureSubstitute (coordSpace m (piC (O := O))) (coordSpace m fun x => (π12 x).1)
        (coordSpace m fun x => (π12 x).2) (coordSpace m π12) ρ (embW m f), embW m f⟫ := by
  rw [pureSubstitute_embW hm, real_inner_comm, inner_embW hm]

omit [DecidableEq O] in
theorem qOp_symm {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π12 : O → A1 × A2) (ρ : ℝ) (f g : O → ℝ) :
    ip m f (qOp m π12 ρ g) = ip m g (qOp m π12 ρ f) := by
  rw [← inner_embW hm, ← inner_embW hm, ← pureSubstitute_embW hm, ← pureSubstitute_embW hm,
    ← pureSubstitute_form_symm, real_inner_comm]

omit [DecidableEq O] [DecidableEq A1] [DecidableEq A2] in
theorem norm_sq_embW {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (f : O → ℝ) :
    ‖embW m f‖ ^ 2 = ip m f f := by
  rw [← real_inner_self_eq_norm_sq, inner_embW hm]

omit [DecidableEq O] [DecidableEq A1] [DecidableEq A2] in
/-- **The pure-pair space in the realization**: a function of `(x₁, x₂)` orthogonal in `L²(m)` to
every function of `x₁` and of `x₂` (constants included) lies in `𝒦₁₂`. -/
theorem embW_mem_pureSpace {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π12 : O → A1 × A2)
    (y : O → ℝ) (hy : ∃ g : A1 × A2 → ℝ, y = fun x => g (π12 x))
    (hy1 : ∀ u : A1 → ℝ, ip m y (fun x => u (π12 x).1) = 0)
    (hy2 : ∀ v : A2 → ℝ, ip m y (fun x => v (π12 x).2) = 0) :
    embW m y ∈ pureSpace (coordSpace m (piC (O := O))) (coordSpace m fun x => (π12 x).1)
      (coordSpace m fun x => (π12 x).2) (coordSpace m π12) := by
  obtain ⟨g, rfl⟩ := hy
  have hS1 : ∀ w ∈ coordSpace m (fun x => (π12 x).1), ⟪w, embW m (fun x => g (π12 x))⟫ = 0 := by
    rintro w ⟨u, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [inner_embW hm, ip_comm]
    exact hy1 u
  have hS2 : ∀ w ∈ coordSpace m (fun x => (π12 x).2), ⟪w, embW m (fun x => g (π12 x))⟫ = 0 := by
    rintro w ⟨v, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [inner_embW hm, ip_comm]
    exact hy2 v
  have hC : ∀ w ∈ coordSpace m (piC (O := O)), ⟪w, embW m (fun x => g (π12 x))⟫ = 0 := by
    rintro w ⟨c, rfl⟩
    exact hS1 _ ⟨fun _ => c (), rfl⟩
  refine ⟨⟨⟨g, rfl⟩, (Submodule.mem_orthogonal _ _).2 hC⟩, ?_⟩
  rw [← Submodule.inf_orthogonal]
  refine ⟨(Submodule.mem_orthogonal _ _).2 fun w hw => hS1 w hw.1,
    (Submodule.mem_orthogonal _ _).2 fun w hw => hS2 w hw.1⟩

/-- **The label-`3` inequality `hUa`, realized** (`U(3,3) = Q₁₂` as conditional expectations,
`qOp`): every hypothesis is a statement in `L²(m)`. `hcor`: the centred functions of `x₁`, `x₂`
have correlation `≤ ρ` (edge `12`); the arms `y_{p,z}` are functions of `(x₁, x₂)` orthogonal to
the functions of `x₁` and of `x₂` (`𝒦₁₂`), orthogonal across the sectors, contractions; and
`Ξ_p(x, z) = m(x) y_{p,z}(x)`. -/
theorem label3_realized {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π12 : O → A1 × A2) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcor : ∀ (u : A1 → ℝ) (v : A2 → ℝ), ip m (fun x => u (π12 x).1) (fun _ => 1) = 0 →
      ip m (fun x => v (π12 x).2) (fun _ => 1) = 0 →
      |ip m (fun x => u (π12 x).1) (fun x => v (π12 x).2)| ≤
        ρ * Real.sqrt (ip m (fun x => u (π12 x).1) (fun x => u (π12 x).1)) *
          Real.sqrt (ip m (fun x => v (π12 x).2) (fun x => v (π12 x).2)))
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : ι → Type*} [∀ p, Fintype (Z p)]
    (y : ∀ p, Z p → O → ℝ) (hyK : ∀ p z, ∃ g : A1 × A2 → ℝ, y p z = fun x => g (π12 x))
    (hy1 : ∀ p z (u : A1 → ℝ), ip m (y p z) (fun x => u (π12 x).1) = 0)
    (hy2 : ∀ p z (v : A2 → ℝ), ip m (y p z) (fun x => v (π12 x).2) = 0)
    (horth : ∀ p q, p ≠ q → ∀ z z', ip m (y p z) (y q z') = 0)
    (hcon : ∀ p (a : Z p → ℝ), ip m (∑ z, a z • y p z) (∑ z, a z • y p z) ≤ ∑ z, a z ^ 2)
    (Ξ : ∀ p, Matrix O (Z p) ℝ) (hΞ : ∀ p x z, Ξ p x z = m x * y p z x) :
    (Matrix.of fun x x' : O => kern m (qOp m π12 ρ) x x' -
      ∑ p, ∑ z, Ξ p x z * Ξ p x' z).PosSemidef := by
  have hK : ∀ p z, embW m (y p z) ∈ pureSpace (coordSpace m (piC (O := O)))
      (coordSpace m fun x => (π12 x).1) (coordSpace m fun x => (π12 x).2) (coordSpace m π12) :=
    fun p z => embW_mem_pureSpace hm π12 (y p z) (hyK p z) (hy1 p z) (hy2 p z)
  have hO : ∀ p q, p ≠ q → ∀ z z', ⟪embW m (y p z), embW m (y q z')⟫ = 0 := by
    intro p q hpq z z'
    rw [inner_embW hm]
    exact horth p q hpq z z'
  have hC : ∀ p (a : Z p → ℝ), ‖∑ z, a z • embW m (y p z)‖ ^ 2 ≤ ∑ z, a z ^ 2 := by
    intro p a
    have e : ∑ z, a z • embW m (y p z) = embW m (∑ z, a z • y p z) := by
      rw [map_sum]
      simp only [map_smul]
    rw [e, norm_sq_embW hm]
    exact hcon p a
  have hX : ∀ p z (f : O → ℝ), ∑ x, f x * Ξ p x z = ⟪embW m f, embW m (y p z)⟫ := by
    intro p z f
    rw [inner_embW hm]
    unfold ip
    exact sum_congr rfl fun x _ => by rw [hΞ]; ring
  have h01 := coordSpace_mono m (fun x => (π12 x).1) (fun _ => ())
  have h02 := coordSpace_mono m (fun x => (π12 x).2) (fun _ => ())
  have h1 := coordSpace_mono m π12 Prod.fst
  have h2 := coordSpace_mono m π12 Prod.snd
  exact label3_le_substitute h01 h02 h1 h2 hρ hρ1 (hcor_embW hm π12 hcor)
    (fun p z => embW m (y p z)) hK hO hC m (embW m) (qOp m π12 ρ) (ip_qOp hm π12 ρ)
    (qOp_symm hm π12 ρ) Ξ hX

omit [DecidableEq A1] [DecidableEq A2] in
/-- **The singleton labels `a = 0, 1, 2`, realized** (`U(a,a) = V_aV_a^* = P_a − 𝒥` as conditional
expectations, `uOp`): the arms `y_{p,z}` are centred functions of `x_a`, orthogonal across the
sectors, contractions, and `Ξ_p(x, z) = m(x) y_{p,z}(x)`. -/
theorem singleton_realized {Aa : Type*} [DecidableEq Aa] {m : O → ℝ} (hm : ∀ x, 0 ≤ m x)
    (πa : O → Aa) {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : ι → Type*} [∀ p, Fintype (Z p)]
    (y : ∀ p, Z p → O → ℝ) (hyK : ∀ p z, ∃ g : Aa → ℝ, y p z = fun x => g (πa x))
    (hy0 : ∀ p z, ip m (y p z) (fun _ => 1) = 0)
    (horth : ∀ p q, p ≠ q → ∀ z z', ip m (y p z) (y q z') = 0)
    (hcon : ∀ p (a : Z p → ℝ), ip m (∑ z, a z • y p z) (∑ z, a z • y p z) ≤ ∑ z, a z ^ 2)
    (Ξ : ∀ p, Matrix O (Z p) ℝ) (hΞ : ∀ p x z, Ξ p x z = m x * y p z x) :
    (Matrix.of fun x x' : O => kern m (uOp m πa) x x' -
      ∑ p, ∑ z, Ξ p x z * Ξ p x' z).PosSemidef := by
  set H := featureSpace (coordSpace m (piC (O := O))) (coordSpace m πa) with hH
  have hK : ∀ p z, embW m (y p z) ∈ H := by
    intro p z
    obtain ⟨g, hg⟩ := hyK p z
    refine ⟨⟨g, by rw [hg]; rfl⟩, (Submodule.mem_orthogonal _ _).2 ?_⟩
    rintro w ⟨c, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [inner_embW hm, ip_comm]
    have := hy0 p z
    have e : (LinearMap.funLeft ℝ ℝ (piC (O := O)) c) = fun _ => c () := rfl
    rw [e]
    unfold ip at this ⊢
    rw [show (∑ x, m x * (y p z x * c ())) = c () * ∑ x, m x * (y p z x * 1) by
      rw [mul_sum]; exact sum_congr rfl fun x _ => by ring, this, mul_zero]
  have hO : ∀ p q, p ≠ q → ∀ z z', ⟪embW m (y p z), embW m (y q z')⟫ = 0 := by
    intro p q hpq z z'
    rw [inner_embW hm]
    exact horth p q hpq z z'
  have hC : ∀ p (a : Z p → ℝ), ‖∑ z, a z • embW m (y p z)‖ ^ 2 ≤ ∑ z, a z ^ 2 := by
    intro p a
    have e : ∑ z, a z • embW m (y p z) = embW m (∑ z, a z • y p z) := by
      rw [map_sum]
      simp only [map_smul]
    rw [e, norm_sq_embW hm]
    exact hcon p a
  have hX : ∀ p z (f : O → ℝ), ∑ x, f x * Ξ p x z = ⟪embW m f, embW m (y p z)⟫ := by
    intro p z f
    rw [inner_embW hm]
    unfold ip
    exact sum_congr rfl fun x _ => by rw [hΞ]; ring
  have hU : ∀ f, ip m f (uOp m πa f) = ⟪H.starProjection (embW m f), embW m f⟫ := by
    intro f
    rw [hH, featureSpace_embW hm, inner_embW hm, ip_comm]
  have hUs : ∀ f g, ip m f (uOp m πa g) = ip m g (uOp m πa f) := by
    intro f g
    rw [← inner_embW hm, ← inner_embW hm, ← featureSpace_embW hm, ← featureSpace_embW hm,
      ← hH, ← Submodule.inner_starProjection_left_eq_right, real_inner_comm]
  exact singleton_le_proj H (fun p z => embW m (y p z)) hK hO hC m (embW m) (uOp m πa) hU hUs Ξ hX

end Labels

/-! ## `hUa` at a fold block and at a matching block -/

section Blocks

variable {O : Type*} [Fintype O] [DecidableEq O] {A : Type*} [DecidableEq A]

/-- **`hUa` of `hdom_of_units` at a fold block** (labels `0..3`, unit lifts on the five labels):
with the unit lifts `U(a,a) = P_a − 𝒥` (`a = 0, 1, 2`) and `U(3,3) = Q₁₂` as conditional
expectations on the coordinates `π a` (`hU`, `hU3`), and the label-`a` columns of the sector maps
`Ξ_p(x, (a, z)) = m(x) y_{a,p,z}(x)` with the arm facts of `singleton_realized` (labels `0, 1, 2`)
and `label3_realized` (label `3`). -/
theorem hUa_fold {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π : Fin 3 → O → A) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρ1 : ρ < 1) (U : Fin 5 → Fin 5 → (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hU : ∀ a : Fin 3, U (Fin.castSucc (Fin.castSucc a)) (Fin.castSucc (Fin.castSucc a)) =
      uOp m (π a))
    (hU3 : U 3 3 = qOp m (fun x => (π 1 x, π 2 x)) ρ)
    (hcor : ∀ (u v : A → ℝ), ip m (fun x => u (π 1 x)) (fun _ => 1) = 0 →
      ip m (fun x => v (π 2 x)) (fun _ => 1) = 0 →
      |ip m (fun x => u (π 1 x)) (fun x => v (π 2 x))| ≤
        ρ * Real.sqrt (ip m (fun x => u (π 1 x)) (fun x => u (π 1 x))) *
          Real.sqrt (ip m (fun x => v (π 2 x)) (fun x => v (π 2 x))))
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : ι → Type*} [∀ p, Fintype (Z p)]
    (y : Fin 4 → ∀ p, Z p → O → ℝ)
    (hyK : ∀ (a : Fin 3) p z, ∃ g : A → ℝ, y (Fin.castSucc a) p z = fun x => g (π a x))
    (hy0 : ∀ (a : Fin 3) p z, ip m (y (Fin.castSucc a) p z) (fun _ => 1) = 0)
    (hyK3 : ∀ p z, ∃ g : A × A → ℝ, y 3 p z = fun x => g (π 1 x, π 2 x))
    (hy1 : ∀ p z (u : A → ℝ), ip m (y 3 p z) (fun x => u (π 1 x)) = 0)
    (hy2 : ∀ p z (v : A → ℝ), ip m (y 3 p z) (fun x => v (π 2 x)) = 0)
    (horth : ∀ a p q, p ≠ q → ∀ z z', ip m (y a p z) (y a q z') = 0)
    (hcon : ∀ a p (c : Z p → ℝ), ip m (∑ z, c z • y a p z) (∑ z, c z • y a p z) ≤ ∑ z, c z ^ 2)
    (Ξ : ∀ p, Matrix O (Fin 4 × Z p) ℝ) (hΞ : ∀ p x a z, Ξ p x (a, z) = m x * y a p z x)
    (a : Fin 4) :
    (Matrix.of fun x x' : O => kern m (U (Fin.castSucc a) (Fin.castSucc a)) x x' -
      ∑ p, ∑ z, Ξ p x (a, z) * Ξ p x' (a, z)).PosSemidef := by
  fin_cases a
  · have := singleton_realized hm (π 0) (y 0) (hyK 0) (hy0 0) (horth 0) (hcon 0)
      (fun p => Matrix.of fun x z => Ξ p x (0, z)) (fun p x z => hΞ p x 0 z)
    rw [← hU 0] at this
    simpa using this
  · have := singleton_realized hm (π 1) (y 1) (hyK 1) (hy0 1) (horth 1) (hcon 1)
      (fun p => Matrix.of fun x z => Ξ p x (1, z)) (fun p x z => hΞ p x 1 z)
    rw [← hU 1] at this
    simpa using this
  · have := singleton_realized hm (π 2) (y 2) (hyK 2) (hy0 2) (horth 2) (hcon 2)
      (fun p => Matrix.of fun x z => Ξ p x (2, z)) (fun p x z => hΞ p x 2 z)
    rw [← hU 2] at this
    simpa using this
  · have := label3_realized hm (fun x => (π 1 x, π 2 x)) hρ hρ1 hcor (y 3) hyK3 hy1 hy2
      (horth 3) (hcon 3) (fun p => Matrix.of fun x z => Ξ p x (3, z)) (fun p x z => hΞ p x 3 z)
    rw [← hU3] at this
    simpa using this

/-- **`hUa` at a matching block** (labels `0, 1`, unit lifts on the three labels): `U(a,a) =
P_a − 𝒥` on the coordinates `π a`, the arms centred functions of `x_a`. -/
theorem hUa_match {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) (π : Fin 2 → O → A)
    (U : Fin 3 → Fin 3 → (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hU : ∀ a : Fin 2, U (Fin.castSucc a) (Fin.castSucc a) = uOp m (π a))
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : ι → Type*} [∀ p, Fintype (Z p)]
    (y : Fin 2 → ∀ p, Z p → O → ℝ)
    (hyK : ∀ (a : Fin 2) p z, ∃ g : A → ℝ, y a p z = fun x => g (π a x))
    (hy0 : ∀ (a : Fin 2) p z, ip m (y a p z) (fun _ => 1) = 0)
    (horth : ∀ a p q, p ≠ q → ∀ z z', ip m (y a p z) (y a q z') = 0)
    (hcon : ∀ a p (c : Z p → ℝ), ip m (∑ z, c z • y a p z) (∑ z, c z • y a p z) ≤ ∑ z, c z ^ 2)
    (Ξ : ∀ p, Matrix O (Fin 2 × Z p) ℝ) (hΞ : ∀ p x a z, Ξ p x (a, z) = m x * y a p z x)
    (a : Fin 2) :
    (Matrix.of fun x x' : O => kern m (U (Fin.castSucc a) (Fin.castSucc a)) x x' -
      ∑ p, ∑ z, Ξ p x (a, z) * Ξ p x' (a, z)).PosSemidef := by
  have := singleton_realized hm (π a) (y a) (hyK a) (hy0 a) (horth a) (hcon a)
    (fun p => Matrix.of fun x z => Ξ p x (a, z)) (fun p x z => hΞ p x a z)
  rw [← hU a] at this
  simpa using this

end Blocks

end Sarkozy.OpsFeature
