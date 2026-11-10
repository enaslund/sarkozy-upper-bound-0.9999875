module

public import Sarkozy.Angles.Friedrichs
public import Sarkozy.Peyre.Correlation
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `L²` of a finite law as a Euclidean space, and Friedrichs angles of `L²(X)`

For a finite law `μ` on `Ω` (zero weights allowed), `l2Map μ f = (√μ(ω) f(ω))_ω` is a linear
map `(Ω → ℝ) → EuclideanSpace ℝ Ω` with `⟪l2Map μ f, l2Map μ g⟫ = E_μ[f g]`
(`inner_l2Map`). It identifies `L²(μ)` (functions modulo `μ`-null sets) with its image, a
real finite-dimensional inner product space. For a random variable `X : Ω → α`, `l2 μ X` is
the image of the functions of `X`, i.e. `L²(X)` (`def:prelim:maxcorr`).

* `friedrichsCos_l2_eq_maxCorr`: if `L²(X) ∩ L²(Y)` is the constants, the Friedrichs cosine
  of `L²(X)` and `L²(Y)` (`def:prelim:angle`) is the maximal correlation `ρ(X;Y)`
  (`maxCorr`). This is the identification used in `lem:mid:subspaces` (iii).
* `friedrichsCos_l2_le_of_cond`: if `A` is a function of `(X, Z)`, `B` of `(Y, Z)`, `Z` a
  function of both, and `ρ(X;Y | Z = z) ≤ ε` for all `z`, then `cos∠(L²(A), L²(B)) ≤ ε`.
  This is the argument of `lem:mid:subspaces` (ii), via `cor:cond-decorrelation`
  (`cond_decorrelation_maxCorr`).
* `l2_inf_le`, `l2_mono`, `l2_congr`: lattice facts, stated on the support of `μ`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.InfluenceGlue

open Sarkozy Sarkozy.Peyre Sarkozy.Angles

variable {Ω : Type*} [Fintype Ω] {α β γ δ : Type*}

/-- The isometric embedding `f ↦ (√μ(ω) f(ω))_ω` of `L²(μ)` into `EuclideanSpace ℝ Ω`. -/
noncomputable def l2Map (μ : FiniteLaw Ω) : (Ω → ℝ) →ₗ[ℝ] EuclideanSpace ℝ Ω where
  toFun f := WithLp.toLp 2 (fun ω => √(μ.weight ω) * f ω)
  map_add' f g := by
    ext ω
    simp [mul_add]
  map_smul' c f := by
    ext ω
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.smul_apply]
    ring

theorem l2Map_ofLp (μ : FiniteLaw Ω) (f : Ω → ℝ) (ω : Ω) :
    (l2Map μ f).ofLp ω = √(μ.weight ω) * f ω := rfl

/-- `⟪l2Map μ f, l2Map μ g⟫ = E_μ[f g]`. -/
theorem inner_l2Map (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    ⟪l2Map μ f, l2Map μ g⟫_ℝ = μ.expect (fun ω => f ω * g ω) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold FiniteLaw.expect dotProduct
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [l2Map_ofLp, star_trivial]
  have h := Real.mul_self_sqrt (μ.nonneg ω)
  calc √(μ.weight ω) * g ω * (√(μ.weight ω) * f ω)
      = (√(μ.weight ω) * √(μ.weight ω)) * (f ω * g ω) := by ring
    _ = μ.weight ω * (f ω * g ω) := by rw [h]

theorem norm_l2Map_sq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ‖l2Map μ f‖ ^ 2 = μ.expect (fun ω => f ω ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_l2Map]
  exact μ.expect_congr fun ω => (sq (f ω)).symm

theorem norm_l2Map (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ‖l2Map μ f‖ = √(μ.expect (fun ω => f ω ^ 2)) := by
  rw [← norm_l2Map_sq, Real.sqrt_sq (norm_nonneg _)]

/-- `l2Map μ f = l2Map μ g` iff `f = g` on the support of `μ`. -/
theorem l2Map_eq_iff (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    l2Map μ f = l2Map μ g ↔ ∀ ω, μ.weight ω ≠ 0 → f ω = g ω := by
  constructor
  · intro h ω hω
    have h1 := congrArg (fun x : EuclideanSpace ℝ Ω => x.ofLp ω) h
    simp only [l2Map_ofLp] at h1
    have hs : √(μ.weight ω) ≠ 0 := by
      rw [Real.sqrt_ne_zero (μ.nonneg ω)]
      exact hω
    exact mul_left_cancel₀ hs h1
  · intro h
    ext ω
    simp only [l2Map_ofLp]
    by_cases hω : μ.weight ω = 0
    · rw [hω, Real.sqrt_zero, zero_mul, zero_mul]
    · rw [h ω hω]

/-- `L²(X)`: the image under `l2Map μ` of the functions of `X`. -/
noncomputable def l2 (μ : FiniteLaw Ω) (X : Ω → α) : Submodule ℝ (EuclideanSpace ℝ Ω) :=
  LinearMap.range ((l2Map μ).comp (LinearMap.funLeft ℝ ℝ X))

theorem mem_l2 {μ : FiniteLaw Ω} {X : Ω → α} {x : EuclideanSpace ℝ Ω} :
    x ∈ l2 μ X ↔ ∃ φ : α → ℝ, l2Map μ (fun ω => φ (X ω)) = x := by
  simp only [l2, LinearMap.mem_range, LinearMap.comp_apply]
  rfl

theorem l2Map_mem_l2 (μ : FiniteLaw Ω) (X : Ω → α) (φ : α → ℝ) :
    l2Map μ (fun ω => φ (X ω)) ∈ l2 μ X :=
  mem_l2.mpr ⟨φ, rfl⟩

/-- A function that is constant on the level sets of `X` inside the support gives an element
of `L²(X)`. -/
theorem l2Map_mem_l2_of_supp {μ : FiniteLaw Ω} {X : Ω → α} {f : Ω → ℝ}
    (hf : ∀ ω ω', μ.weight ω ≠ 0 → μ.weight ω' ≠ 0 → X ω = X ω' → f ω = f ω') :
    l2Map μ f ∈ l2 μ X := by
  obtain ⟨φ, hφ⟩ := exists_fun_on X (fun ω => μ.weight ω ≠ 0) f hf
  refine mem_l2.mpr ⟨φ, ?_⟩
  rw [l2Map_eq_iff]
  exact fun ω hω => (hφ ω hω).symm

/-- `L²(X) ≤ L²(Y)` when `X` is a function of `Y` on the support. -/
theorem l2_mono {μ : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β}
    (h : ∀ ω ω', μ.weight ω ≠ 0 → μ.weight ω' ≠ 0 → Y ω = Y ω' → X ω = X ω') :
    l2 μ X ≤ l2 μ Y := by
  intro x hx
  obtain ⟨φ, rfl⟩ := mem_l2.mp hx
  exact l2Map_mem_l2_of_supp fun ω ω' hω hω' hY => by rw [h ω ω' hω hω' hY]

/-- `L²(X) = L²(Y)` when `X` and `Y` have the same level sets on the support. -/
theorem l2_congr {μ : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β}
    (h : ∀ ω ω', μ.weight ω ≠ 0 → μ.weight ω' ≠ 0 → (X ω = X ω' ↔ Y ω = Y ω')) :
    l2 μ X = l2 μ Y :=
  le_antisymm (l2_mono fun ω ω' hω hω' hY => (h ω ω' hω hω').mpr hY)
    (l2_mono fun ω ω' hω hω' hX => (h ω ω' hω hω').mp hX)

/-- If every function of `A` and of `B` (on the support) is a function of `C`, then
`L²(A) ⊓ L²(B) ≤ L²(C)`. -/
theorem l2_inf_le {μ : FiniteLaw Ω} {A : Ω → α} {B : Ω → β} {C : Ω → γ}
    (h : ∀ φ : α → ℝ, ∀ ψ : β → ℝ,
      (∀ ω, μ.weight ω ≠ 0 → φ (A ω) = ψ (B ω)) →
        ∀ ω ω', μ.weight ω ≠ 0 → μ.weight ω' ≠ 0 → C ω = C ω' → φ (A ω) = φ (A ω')) :
    l2 μ A ⊓ l2 μ B ≤ l2 μ C := by
  intro x hx
  obtain ⟨hxA, hxB⟩ := Submodule.mem_inf.mp hx
  obtain ⟨φ, rfl⟩ := mem_l2.mp hxA
  obtain ⟨ψ, hψ⟩ := mem_l2.mp hxB
  have hagree : ∀ ω, μ.weight ω ≠ 0 → φ (A ω) = ψ (B ω) :=
    (l2Map_eq_iff μ _ _).mp hψ.symm
  exact l2Map_mem_l2_of_supp (h φ ψ hagree)

/-- The constants: `L²` of a constant variable. -/
noncomputable abbrev l2Const (μ : FiniteLaw Ω) : Submodule ℝ (EuclideanSpace ℝ Ω) :=
  l2 μ (fun _ : Ω => ())

/-- `l2Map μ f ⊥` the constants iff `E_μ f = 0`. -/
theorem l2Map_mem_orthogonal_const_iff (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    l2Map μ f ∈ (l2Const μ)ᗮ ↔ μ.expect f = 0 := by
  constructor
  · intro h
    have h1 := Submodule.inner_right_of_mem_orthogonal
      (l2Map_mem_l2 μ (fun _ : Ω => ()) (fun _ => 1)) h
    rw [inner_l2Map] at h1
    simpa using h1
  · intro h
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨φ, rfl⟩ := mem_l2.mp hu
    rw [inner_l2Map]
    rw [show (fun ω => φ () * f ω) = fun ω => φ () * f ω from rfl, μ.expect_const_mul, h,
      mul_zero]

theorem l2Const_le (μ : FiniteLaw Ω) (X : Ω → α) : l2Const μ ≤ l2 μ X :=
  l2_mono fun _ _ _ _ _ => rfl

/-- **The Friedrichs cosine of `L²(X)` and `L²(Y)` is the maximal correlation** when
`L²(X) ∩ L²(Y)` is the constants (`lem:mid:subspaces` (iii), `def:prelim:maxcorr`). -/
theorem friedrichsCos_l2_eq_maxCorr (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β)
    (h : l2 μ X ⊓ l2 μ Y = l2Const μ) :
    friedrichsCos (l2 μ X) (l2 μ Y) = maxCorr μ X Y := by
  unfold friedrichsCos maxCorr
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, hx', hy', hnx, hny, rfl⟩
    obtain ⟨φ, rfl⟩ := mem_l2.mp hx
    obtain ⟨ψ, rfl⟩ := mem_l2.mp hy
    rw [h, l2Map_mem_orthogonal_const_iff] at hx' hy'
    refine ⟨φ, ψ, hx', hy', ?_, ?_, ?_⟩
    · rw [← norm_l2Map_sq, hnx, one_pow]
    · rw [← norm_l2Map_sq, hny, one_pow]
    · rw [inner_l2Map]
  · rintro ⟨φ, ψ, hφ, hψ, hφ2, hψ2, rfl⟩
    refine ⟨l2Map μ (fun ω => φ (X ω)), l2Map_mem_l2 μ X φ, l2Map μ (fun ω => ψ (Y ω)),
      l2Map_mem_l2 μ Y ψ, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h, l2Map_mem_orthogonal_const_iff]
      exact hφ
    · rw [h, l2Map_mem_orthogonal_const_iff]
      exact hψ
    · rw [norm_l2Map, hφ2, Real.sqrt_one]
    · rw [norm_l2Map, hψ2, Real.sqrt_one]
    · rw [inner_l2Map]

omit [Fintype Ω] in
/-- The indicator of a level set of `Z` is a function of `Z`. -/
theorem ind_lv_eq (Z : Ω → γ) (ω : Ω) [DecidableEq γ] :
    ind (lv Z ω) = fun ω' => (fun c => if c = Z ω then (1 : ℝ) else 0) (Z ω') := by
  funext ω'
  by_cases h : Z ω' = Z ω
  · rw [ind_of_pos (show lv Z ω ω' from h)]
    simp [h]
  · rw [ind_of_neg (show ¬ lv Z ω ω' from h)]
    simp [h]

/-- An element of `L²(A)` orthogonal to `L²(Z)` has vanishing conditional expectation given
`Z` (at points of positive mass, and in fact everywhere by the level-set formula). -/
theorem condExp_eq_zero_of_orthogonal (μ : FiniteLaw Ω) (Z : Ω → γ) {f : Ω → ℝ}
    (hf : l2Map μ f ∈ (l2 μ Z)ᗮ) (ω : Ω) : condExp μ Z f ω = 0 := by
  classical
  have h1 := Submodule.inner_right_of_mem_orthogonal
    (l2Map_mem_l2 μ Z (fun c => if c = Z ω then (1 : ℝ) else 0)) hf
  rw [inner_l2Map] at h1
  unfold condExp
  rw [ind_lv_eq Z ω, h1, zero_div]

/-- **`lem:mid:subspaces` (ii), abstract form.** Let `A` be a function of `(X, Z)` and `B` a
function of `(Y, Z)`, with `Z` a function of `A` and of `B`. If `ρ(X;Y | Z = z) ≤ ε` for every
`z` of positive probability, then `cos∠(L²(A), L²(B)) ≤ ε`. -/
theorem friedrichsCos_l2_le_of_cond (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (A : Ω → δ) {ε' : Type*} (B : Ω → ε') {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ ω ω', X ω = X ω' → Z ω = Z ω' → A ω = A ω')
    (hB : ∀ ω ω', Y ω = Y ω' → Z ω = Z ω' → B ω = B ω')
    (hZA : ∀ ω ω', A ω = A ω' → Z ω = Z ω') (hZB : ∀ ω ω', B ω = B ω' → Z ω = Z ω')
    (hyp : ∀ z, ∀ hz : 0 < prob μ (fun ω => Z ω = z),
      maxCorr (condLaw μ (fun ω => Z ω = z) hz) X Y ≤ ε) :
    friedrichsCos (l2 μ A) (l2 μ B) ≤ ε := by
  have hZle : l2 μ Z ≤ l2 μ A ⊓ l2 μ B :=
    le_inf (l2_mono fun ω ω' _ _ h => hZA ω ω' h) (l2_mono fun ω ω' _ _ h => hZB ω ω' h)
  refine friedrichsCos_le_of_forall hε fun x hx y hy hx' _ => ?_
  obtain ⟨φ, rfl⟩ := mem_l2.mp hx
  obtain ⟨ψ, rfl⟩ := mem_l2.mp hy
  have hx'' : l2Map μ (fun ω => φ (A ω)) ∈ (l2 μ Z)ᗮ := Submodule.orthogonal_le hZle hx'
  have h := (cond_decorrelation_maxCorr μ X Y Z hε hyp (f := fun ω => φ (A ω))
    (g := fun ω => ψ (B ω)) (fun ω ω' h1 h2 => by rw [hA ω ω' h1 h2])
    (fun ω _ => condExp_eq_zero_of_orthogonal μ Z hx'' ω)
    (fun ω ω' h1 h2 => by rw [hB ω ω' h1 h2]))
  rw [inner_l2Map, norm_l2Map, norm_l2Map]
  exact h.1.trans h.2

end Sarkozy.InfluenceGlue
