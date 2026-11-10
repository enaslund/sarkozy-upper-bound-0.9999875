module

public import Sarkozy.Spectral.GlueRoute
public import Sarkozy.Cuts.CutInvariance

/-!
# Glue, VII: the star operator and `lem:spec:stars` (b), (c) in the cut realization

The star part of the character expansion `eq:record:root-kernel` of the cut kernel, for spectral
data `D` at `𝔽_p`. Here `ς_jk` are the cross signs (`SpecData.sgn`, cast to `𝔽_p`),
`N(k) = SpecData.Nset k`, and `μ = λ(G⁺)` is WP-P's half law.

* `colChar k J`: the character `χ_S(x, x') = ∏_{j ∈ J} χ(ς_jk(x'_k - x_j))` of the column star
  `S = J × {k}`. `rowChar j K`: the character `∏_{k ∈ K} χ(ς_jk(x'_k - x_j))` of the row star
  `{j} × K`. The single pairs are column stars, so the row stars are taken with `|K| ≥ 2`.
* `starKer = ∑_{S star} χ_S` and `starOp = T_star`, its operator on `L²(μ)` (`kernelOp`).

Results:
* `expect_colChar` (`lem:spec:stars` (a)): on injective `x`,
  `E_{x'}[χ_{J×{k}}(x, x')] = (ε_J)_k w_J(x)` with `(ε_J)_k = ∏_{j∈J} χ(ς_jk)` (`starCoef`) and
  `w_J(x) = starTrace(x(J))`. This uses the uniform one-vertex marginal of `μ`
  (WP-P's `graphLaw_vertex_uniform`).
* `expect_rowChar` (`lem:spec:stars` (b)): `T_S 1` is constant for a row star. This uses the
  translation invariance of `μ` (WP-P's `graphLaw_affine`).
* `rowChar_swap`, `rowOp_adjoint` (`lem:spec:stars` (b)): `χ_{{k}×J}(x, x') = χ_{J×{k}}(x', x)`,
  so `T_{row} = (T_{col})^*`. This uses `ς_kj = -ς_jk` (WP-P's `sgn_antisymm`).
* `sum_rows_eq_mean` (`lem:spec:stars` (c)): the row stars together give the constant `E_μ h_⋆`.
* `stars_c` (`lem:spec:stars` (c)): `T_star 1 = h_⋆ + E_μ h_⋆`, with
  `h_⋆ = Spectral.starFunction N (ε_J)_k`.
* `starOp_perp` (`prop:spec2:mucentre` (a)): `⟪h', T_star h⟫ = 0` when `h`, `h'` are orthogonal to
  every function of one coordinate, the hypothesis `hstar` of `mucentre_inputs` on `H_⊥`.
* `glue_mucentre_star_closed`: `glue_mucentre_star` with `T_star = starOp`. No star hypothesis
  remains; the inputs are `Target.Weil`, `Target.MovingRoot` and the count errors.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.Spectral

open Sarkozy Sarkozy.InfluenceGlue Sarkozy.Cuts

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U) {p : ℕ} [Fact p.Prime]

/-- The cross sign `ς_jk ∈ {0, ±1}`, in `𝔽_p`. -/
def sgnF (j k : D.cut.Half) : ZMod p := ((D.sgn j k : ℤ) : ZMod p)

theorem sgnF_antisymm (j k : D.cut.Half) : sgnF (p := p) D k j = -sgnF D j k := by
  unfold sgnF
  rw [D.sgn_antisymm j k, Int.cast_neg]

/-- The column-star character `∏_{j ∈ J} χ(ς_jk(x'_k - x_j))`. -/
noncomputable def colChar (k : D.cut.Half) (J : Finset D.cut.Half)
    (x x' : D.cut.Half → ZMod p) : ℝ :=
  ∏ j ∈ J, (quadraticChar (ZMod p) (sgnF D j k * (x' k - x j)) : ℝ)

/-- The row-star character `∏_{k ∈ K} χ(ς_jk(x'_k - x_j))`. -/
noncomputable def rowChar (j : D.cut.Half) (K : Finset D.cut.Half)
    (x x' : D.cut.Half → ZMod p) : ℝ :=
  ∏ k ∈ K, (quadraticChar (ZMod p) (sgnF D j k * (x' k - x j)) : ℝ)

/-- **The star kernel** `∑_{S star} χ_S`. -/
noncomputable def starKer (x x' : D.cut.Half → ZMod p) : ℝ :=
  (∑ k, ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.Nonempty), colChar D k J x x') +
    ∑ j, ∑ K ∈ (D.Nset j).powerset.filter (fun K => 2 ≤ K.card), rowChar D j K x x'

/-- **The star operator** `T_star` on `L²(μ)`, `μ = λ(G⁺)`. -/
noncomputable def starOp (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) :
    EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ] EuclideanSpace ℝ (D.cut.Half → ZMod p) :=
  kernelOp (D.halfLaw hne) (starKer D)

/-- The star coefficients `(ε_J)_k = ∏_{j∈J} χ(ς_jk)`. -/
noncomputable def starCoef (k : D.cut.Half) (J : Finset D.cut.Half) : ℝ :=
  ∏ j ∈ J, (quadraticChar (ZMod p) (sgnF D j k) : ℝ)

/-- On the support of the half law, labellings are injective. -/
theorem injective_of_halfLaw_ne_zero (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    {x : D.cut.Half → ZMod p} (hx : (D.halfLaw hne).weight x ≠ 0) : Function.Injective x := by
  have hmem : x ∈ Labellings.injLabellings (ZMod p) D.halfGraph := by
    by_contra h
    apply hx
    simp only [SpecData.halfLaw, Labellings.graphLaw, h, ↓reduceIte]
  rw [SpecData.mem_inj] at hmem
  exact fun a b hab => hmem.1 a (Finset.mem_univ a) b (Finset.mem_univ b) hab

/-- **`lem:spec:stars` (a)**: the column star `J × {k}` maps `1` to `(ε_J)_k w_J` on injective
labellings. -/
theorem expect_colChar (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (k : D.cut.Half) (J : Finset D.cut.Half) {x : D.cut.Half → ZMod p}
    (hx : Function.Injective x) :
    (D.halfLaw hne).expect (fun x' => colChar D k J x x') =
      starCoef (p := p) D k J * starTrace (J.image x) := by
  have h := graphLaw_vertex_uniform D.halfGraph (D.half_nonempty hne) k
    (fun t => ∏ j ∈ J, (quadraticChar (ZMod p) (sgnF D j k * (t - x j)) : ℝ))
  change (D.halfLaw hne).expect (fun y => ∏ j ∈ J,
    (quadraticChar (ZMod p) (sgnF D j k * (y k - x j)) : ℝ)) = _ at h
  rw [show (fun x' => colChar D k J x x') = (fun y => ∏ j ∈ J,
    (quadraticChar (ZMod p) (sgnF D j k * (y k - x j)) : ℝ)) from rfl, h,
    FiniteLaw.expect_uniform, starCoef, starTrace, ZMod.card]
  have e : ∀ t, ∏ j ∈ J, (quadraticChar (ZMod p) (sgnF D j k * (t - x j)) : ℝ) =
      (∏ j ∈ J, (quadraticChar (ZMod p) (sgnF D j k) : ℝ)) *
        (quadraticChar (ZMod p) (∏ a ∈ J.image x, (t - a)) : ℝ) := fun t => by
    rw [← prod_char_eq J x (hx.injOn) t]
    push_cast
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [map_mul]; push_cast; ring
  rw [Finset.sum_congr rfl fun t _ => e t, ← Finset.mul_sum]
  ring

/-- **`lem:spec:stars` (b)**: a row star maps `1` to a constant. -/
theorem expect_rowChar (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (j : D.cut.Half) (K : Finset D.cut.Half) (x : D.cut.Half → ZMod p) :
    (D.halfLaw hne).expect (fun x' => rowChar D j K x x') =
      (D.halfLaw hne).expect (fun x' => rowChar D j K 0 x') := by
  have h := graphLaw_affine D.halfGraph (D.half_nonempty hne) (a := (1 : ZMod p))
    (by simp) (-x j) (fun y => rowChar D j K 0 y)
  change (D.halfLaw hne).expect _ = (D.halfLaw hne).expect _ at h
  rw [← h]
  refine (D.halfLaw hne).expect_congr fun y => ?_
  simp only [rowChar, affineMap, one_mul, Pi.zero_apply, sub_eq_add_neg, neg_zero, add_zero]

/-- **`lem:spec:stars` (b)**: `χ_{{k}×J}(x, x') = χ_{J×{k}}(x', x)` (`ς_kj = -ς_jk`). -/
theorem rowChar_swap (k : D.cut.Half) (J : Finset D.cut.Half) (x x' : D.cut.Half → ZMod p) :
    rowChar D k J x x' = colChar D k J x' x := by
  unfold rowChar colChar
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [sgnF_antisymm D j k]
  congr 2
  ring

omit [DecidableEq U] in
/-- The operator of the transposed kernel is the adjoint: `⟪u, T_{kᵀ} v⟫ = ⟪T_k u, v⟫`. -/
theorem kernelOp_transpose {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ)
    (u v : EuclideanSpace ℝ Ω) :
    ⟪u, kernelOp μ (fun x x' => k x' x) v⟫_ℝ = ⟪kernelOp μ k u, v⟫_ℝ := by
  rw [← real_inner_comm (kernelOp μ k u) v, inner_kernelOp, inner_kernelOp, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring

/-- **`lem:spec:stars` (b)**, operator form: the row star `{k} × J` is the adjoint of the column
star `J × {k}`. -/
theorem rowOp_adjoint (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (k : D.cut.Half) (J : Finset D.cut.Half) (u v : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    ⟪u, kernelOp (D.halfLaw hne) (rowChar D k J) v⟫_ℝ =
      ⟪kernelOp (D.halfLaw hne) (colChar D k J) u, v⟫_ℝ := by
  have h : rowChar (p := p) D k J = fun x x' => colChar D k J x' x :=
    funext fun x => funext fun x' => rowChar_swap D k J x x'
  rw [h, kernelOp_transpose]

/-- The symmetry of `μ ⊗ μ`. -/
theorem expect_expect_swap (μ : FiniteLaw (D.cut.Half → ZMod p))
    (g : (D.cut.Half → ZMod p) → (D.cut.Half → ZMod p) → ℝ) :
    μ.expect (fun x => μ.expect (fun x' => g x x')) =
      μ.expect (fun x => μ.expect (fun x' => g x' x)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring

/-- `E_μ` only sees the support. -/
theorem expect_congr_supp (μ : FiniteLaw (D.cut.Half → ZMod p)) {f g : (D.cut.Half → ZMod p) → ℝ}
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) : μ.expect f = μ.expect g := by
  unfold FiniteLaw.expect
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : μ.weight x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

/-- **`lem:spec:stars` (c), the row stars**: together they give the constant `E_μ h_⋆`. -/
theorem sum_rows_eq_mean (hp2 : p ≠ 2) (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (x : D.cut.Half → ZMod p) :
    ∑ j, ∑ K ∈ (D.Nset j).powerset.filter (fun K => 2 ≤ K.card),
        (D.halfLaw hne).expect (fun x' => rowChar D j K x x') =
      (D.halfLaw hne).expect (starFunction D.Nset (starCoef (p := p) D)) := by
  set μ := D.halfLaw hne with hμ
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  -- the mean of `h_⋆` through the column stars
  have h1 : μ.expect (starFunction D.Nset (starCoef (p := p) D)) =
      ∑ k, ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.Nonempty),
        μ.expect (fun x => μ.expect (fun x' => colChar D k J x x')) := by
    rw [show μ.expect (starFunction D.Nset (starCoef (p := p) D)) = μ.expect (fun x =>
        ∑ k, ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.Nonempty),
          μ.expect (fun x' => colChar D k J x x')) from
      expect_congr_supp D μ fun x hx => by
        simp only [starFunction]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun J _ => ?_
        rw [expect_colChar D hne k J (injective_of_halfLaw_ne_zero D hne hx)]]
    simp only [FiniteLaw.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
  -- the singletons vanish
  have h2 : ∀ k, ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.Nonempty),
      μ.expect (fun x => μ.expect (fun x' => colChar D k J x x')) =
      ∑ J ∈ (D.Nset k).powerset.filter (fun J => 2 ≤ J.card),
        μ.expect (fun x => μ.expect (fun x' => colChar D k J x x')) := by
    intro k
    have hsplit : (D.Nset k).powerset.filter (fun J => J.Nonempty) =
        (D.Nset k).powerset.filter (fun J => J.card = 1) ∪
          (D.Nset k).powerset.filter (fun J => 2 ≤ J.card) := by
      ext J
      simp only [Finset.mem_filter, Finset.mem_union, ← Finset.card_pos]
      constructor
      · rintro ⟨hs, h⟩
        by_cases h1 : J.card = 1
        · exact Or.inl ⟨hs, h1⟩
        · exact Or.inr ⟨hs, by omega⟩
      · rintro (⟨hs, h⟩ | ⟨hs, h⟩) <;> exact ⟨hs, by omega⟩
    rw [hsplit, Finset.sum_union]
    · have h0 : ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.card = 1),
          μ.expect (fun x => μ.expect (fun x' => colChar D k J x x')) = 0 := by
        refine Finset.sum_eq_zero fun J hJ => ?_
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hJ).2
        rw [show μ.expect (fun x => μ.expect (fun x' => colChar D k {a} x x')) =
            μ.expect (fun _ => (0 : ℝ)) from expect_congr_supp D μ fun x hx => by
          rw [expect_colChar D hne k {a} (injective_of_halfLaw_ne_zero D hne hx),
            Finset.image_singleton, starTrace_singleton hF, mul_zero]]
        exact FiniteLaw.expect_const μ 0
      rw [h0, zero_add]
    · rw [Finset.disjoint_filter]
      intro J _ h1 h2
      omega
  rw [h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h2 k]
  refine Finset.sum_congr rfl fun J _ => ?_
  -- `E_x E_{x'} χ_{J×{k}}(x, x') = E_x E_{x'} χ_{{k}×J}(x, x') = T_{row} 1`, a constant
  rw [expect_expect_swap D μ (fun x x' => colChar D k J x x')]
  have hrow : ∀ y, μ.expect (fun x' => colChar D k J x' y) =
      μ.expect (fun x' => rowChar D k J x x') := fun y => by
    have e1 : μ.expect (fun x' => colChar D k J x' y) = μ.expect (fun x' => rowChar D k J y x') :=
      μ.expect_congr fun x' => (rowChar_swap D k J y x').symm
    exact e1.trans ((expect_rowChar D hne k J y).trans (expect_rowChar D hne k J x).symm)
  rw [μ.expect_congr hrow, FiniteLaw.expect_const]

/-- **`lem:spec:stars` (c)**: `T_star 1 = h_⋆ + E_μ h_⋆` in the cut realization. -/
theorem stars_c (hp2 : p ≠ 2) (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) :
    starOp D hne (cutOne D hne) =
      l2Map (D.halfLaw hne) (starFunction D.Nset (starCoef (p := p) D)) +
        ⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction D.Nset (starCoef (p := p) D))⟫_ℝ •
          cutOne D hne := by
  have hmean : ⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction D.Nset (starCoef (p := p) D))⟫_ℝ =
      (D.halfLaw hne).expect (starFunction D.Nset (starCoef (p := p) D)) := by
    rw [cutOne, inner_l2Map]
    exact (D.halfLaw hne).expect_congr fun x => one_mul _
  rw [hmean]
  ext x
  simp only [starOp, kernelOp_ofLp, cutOne, l2Map_ofLp, mul_one, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  by_cases hx : (D.halfLaw hne).weight x = 0
  · simp [hx]
  -- the coordinate is `√μ(x) E_{x'}[starKer(x, x')]`
  have hcoord : ∑ x', √((D.halfLaw hne).weight x) * starKer D x x' *
      √((D.halfLaw hne).weight x') * √((D.halfLaw hne).weight x') =
      √((D.halfLaw hne).weight x) * (D.halfLaw hne).expect (fun x' => starKer D x x') := by
    rw [FiniteLaw.expect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    have := Real.mul_self_sqrt ((D.halfLaw hne).nonneg x')
    calc √((D.halfLaw hne).weight x) * starKer D x x' * √((D.halfLaw hne).weight x') *
          √((D.halfLaw hne).weight x')
        = √((D.halfLaw hne).weight x) * ((√((D.halfLaw hne).weight x') *
            √((D.halfLaw hne).weight x')) * starKer D x x') := by ring
      _ = √((D.halfLaw hne).weight x) * ((D.halfLaw hne).weight x' * starKer D x x') := by
          rw [this]
  rw [hcoord]
  have hinj := injective_of_halfLaw_ne_zero D hne hx
  have hker : (D.halfLaw hne).expect (fun x' => starKer D x x') =
      starFunction D.Nset (starCoef (p := p) D) x +
        (D.halfLaw hne).expect (starFunction D.Nset (starCoef (p := p) D)) := by
    rw [← sum_rows_eq_mean D hp2 hne x]
    simp only [starKer]
    rw [FiniteLaw.expect_add]
    congr 1
    · simp only [starFunction]
      rw [show (fun x' => ∑ k, ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.Nonempty),
          colChar D k J x x') = (fun x' => ∑ k, (fun k x' => ∑ J ∈ (D.Nset k).powerset.filter
            (fun J => J.Nonempty), colChar D k J x x') k x') from rfl]
      rw [show (D.halfLaw hne).expect (fun x' => ∑ k, ∑ J ∈ (D.Nset k).powerset.filter
          (fun J => J.Nonempty), colChar D k J x x') =
          ∑ k, ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.Nonempty),
            (D.halfLaw hne).expect (fun x' => colChar D k J x x') by
        simp only [FiniteLaw.expect, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun J _ =>
        expect_colChar D hne k J hinj
    · simp only [FiniteLaw.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  rw [hker]
  ring

omit [DecidableEq U] in
/-- The inner product with an `l2Map` vector, in coordinates. -/
theorem inner_l2Map_left {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (G : Ω → ℝ)
    (h : EuclideanSpace ℝ Ω) :
    ⟪l2Map μ G, h⟫_ℝ = ∑ x, √(μ.weight x) * G x * h.ofLp x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [l2Map_ofLp, star_trivial]
  ring

/-- **`T_star` vanishes on `H_⊥`** (`prop:spec2:mucentre` (a), from `lem:spec:stars` (a), (b)): if
`h` and `h'` are orthogonal to every function of one coordinate `x_k` (as the functions of
`H_⊥ = (ℂ1 ⊕ 𝒱)^⊥` are, since a function of `x_k` is a constant plus an element of `𝒱_k`), then
`⟪h', T_star h⟫ = 0`: a column star sees `h` only through a function of `x'_k`, and a row star
sees `h'` only through a function of `x_j`. -/
theorem starOp_perp (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (h h' : EuclideanSpace ℝ (D.cut.Half → ZMod p))
    (hh : ∀ k (g : ZMod p → ℝ), ⟪l2Map (D.halfLaw hne) (fun x => g (x k)), h⟫_ℝ = 0)
    (hh' : ∀ k (g : ZMod p → ℝ), ⟪l2Map (D.halfLaw hne) (fun x => g (x k)), h'⟫_ℝ = 0) :
    ⟪h', starOp D hne h⟫_ℝ = 0 := by
  rw [starOp, inner_kernelOp]
  set w := (D.halfLaw hne).weight with hw
  -- the column stars: the sum over `x'` is an inner product with a function of `x'_k`
  have hcol : ∀ k J x, ∑ x', colChar D k J x x' * √(w x') * h.ofLp x' = 0 := by
    intro k J x
    have := hh k (fun t => ∏ j ∈ J, (quadraticChar (ZMod p) (sgnF D j k * (t - x j)) : ℝ))
    rw [inner_l2Map_left] at this
    rw [← this]
    refine Finset.sum_congr rfl fun x' _ => ?_
    simp only [colChar]
    ring
  -- the row stars: the sum over `x` is an inner product with a function of `x_j`
  have hrow : ∀ j K x', ∑ x, h'.ofLp x * √(w x) * rowChar D j K x x' = 0 := by
    intro j K x'
    have := hh' j (fun s => ∏ k ∈ K, (quadraticChar (ZMod p) (sgnF D j k * (x' k - s)) : ℝ))
    rw [inner_l2Map_left] at this
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [rowChar]
    ring
  have e : ∀ x x', h'.ofLp x * (√(w x) * starKer D x x' * √(w x')) * h.ofLp x' =
      (∑ k, ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.Nonempty),
        h'.ofLp x * √(w x) * (colChar D k J x x' * √(w x') * h.ofLp x')) +
      ∑ j, ∑ K ∈ (D.Nset j).powerset.filter (fun K => 2 ≤ K.card),
        (h'.ofLp x * √(w x) * rowChar D j K x x') * (√(w x') * h.ofLp x') := by
    intro x x'
    simp only [starKer, Finset.mul_sum, Finset.sum_mul, add_mul, mul_add]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun J _ => by ring
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun K _ => by ring
  simp only [e, Finset.sum_add_distrib]
  have h1 : ∑ x, ∑ x', ∑ k, ∑ J ∈ (D.Nset k).powerset.filter (fun J => J.Nonempty),
      h'.ofLp x * √(w x) * (colChar D k J x x' * √(w x') * h.ofLp x') = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun J _ => ?_
    rw [← Finset.mul_sum, hcol k J x, mul_zero]
  have h2 : ∑ x, ∑ x', ∑ j, ∑ K ∈ (D.Nset j).powerset.filter (fun K => 2 ≤ K.card),
      (h'.ofLp x * √(w x) * rowChar D j K x x') * (√(w x') * h.ofLp x') = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun x' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun K _ => ?_
    rw [← Finset.sum_mul, hrow j K x', zero_mul]
  rw [h1, h2, add_zero]

/-- **The star chain, closed**: `glue_mucentre_star` with `T_star = starOp D hne`. -/
theorem glue_mucentre_star_closed [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (hp2 : p ≠ 2)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1) :
    let L := SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2) D.halfGraph
      (D.half_nonempty hne) he
    ‖starOp D hne (cutOne D hne) -
        ⟪cutOne D hne, starOp D hne (cutOne D hne)⟫_ℝ • cutOne D hne‖ ≤
      starMstar L D.Nset (starCoef (p := p) D) ∧
    ⟪cutOne D hne, starOp D hne (cutOne D hne)⟫_ℝ =
      2 * ⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction D.Nset (starCoef (p := p) D))⟫_ℝ ∧
    2 * |⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction D.Nset (starCoef (p := p) D))⟫_ℝ| ≤
      2 * starZstar L D.Nset (starCoef (p := p) D) :=
  glue_mucentre_star D hW hMR hp2 hne he D.Nset (starCoef (p := p) D) (starOp D hne)
    (stars_c D hp2 hne)

end Sarkozy.Spectral
