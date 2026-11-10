module

public import Sarkozy.FiveType.Datum

/-!
# Two coordinates: the slice principle

Sources: `def:two-coordinate-five-type` and `lem:five-type`(d),
`paper/sections/17_completion_repair.tex`.

**The setting** (`def:two-coordinate-five-type`). Labels lie in a finite set `X`, layers in a
finite set `Λ`, and the slots are `W = ℤ/6ℤ × ℤ/6ℤ × Λ`.
* The field types are `L, F, E` (`FieldTy`), with objects `O_L = ℤ/6ℤ` and `O_F = O_E = {0,1,2}`
  (`FieldTy.Obj`).
* The five types have the field types `𝔣(L) = L`, `𝔣(D) = F`, `𝔣(S) = 𝔣(R) = 𝔣(C) = E`
  (`fieldOf`).
* Their pattern sets are indexed by `PatIdx t` and given by `patMap t`: `P_L = {id}`,
  `P_D = {F_0, F_1, F_2}`, `P_S = {E_0, E_1}`, `P_R = {G_{sk}}` and `P_C = {C_0, C_1}`. Here the
  merges `G_{sk}` take the values `0, 1 ∈ O_E`, and `C_0 = C_1` is the constant map `0`.
* For each pair of field types there is a law `λ_{𝔣₀𝔣₁}` on `X^{O_{𝔣₀} × O_{𝔣₁} × Λ}` (`lam`).
* A state is `t = (t₀, t₁)`, of degree `deg t₀ + deg t₁` (`stateDeg`).
* The component `Π_{t,φ}` is the law of `e_φ(y)`, where
  `e_φ(y)_{(u₀,u₁,ℓ)} = y_{φ₀(u₀), φ₁(u₁), ℓ}` and `y ∼ λ_{𝔣(t₀)𝔣(t₁)}` (`comp`).
  Then `π_t = ∑_φ Π_{t,φ}` (`piT2`) and `𝒬 = ∑_t a_t π_t` (`Q2`).
* The **row data of the coordinate 0 at `𝔣'`** live on the row space `𝔛 = X^{O_{𝔣'} × Λ}`. They
  are the laws of the row families `(y_{o,·,·})_o` (`rows0`) of `y ∼ λ_{L𝔣'}`, `λ_{F𝔣'}` and
  `λ_{E𝔣'}`, the law `Γ` of the rows `0, 1` of `λ_{E𝔣'}`, and the law `ν` of its row `0`.
  `RowDatum0 lam 𝔣' D` says that these are the laws `π_L, π_F, π_E, Γ, ν` of the five-type datum
  `D` on `𝔛`. Then `D` carries the conditional laws `ν^b` and the kernels, consistently with
  these laws, by `def:five-type-datum`. The coordinate 1 is the same with the coordinates
  exchanged (`rows1`, `RowDatum1`).
* The chamber cut `ϑ_{c,i}` (the reflection `ϑ_i` in the coordinate `c`) is `cut0 i` or
  `cut1 i`. For `Λ = ℤ/2ℤ` these are `firstChamberCut i` and `secondChamberCut i` of
  `Slots.lean`.

**`lem:five-type`(d), the slice principle.** For fixed `c`, `t'` and `φ' ∈ P_{t'}`, the sum of
the components `a_t Π_{t,φ}` with `t_{1-c} = t'` and `φ_{1-c} = φ'` is the image of the
five-type measure of the row data (with the weights `a_{(·, t')}`) under the emission
`e_{φ'}(Ψ)_{(u₀,u₁,ℓ)} = Ψ_{u_c}(φ'(u_{1-c}), ℓ)` (`slice0_eq`, `slice1_eq`). `𝒬` is the sum of
these slices (`Q2_eq_slices0`, `Q2_eq_slices1`). The emission is half-local for `ϑ_i` and
`ϑ_{c,i}` (`form_push_halfLocal`, `positive_emitRow0`, `positive_emitRow1`), so it carries
reflection positivity at `ϑ_i` to reflection positivity at `ϑ_{c,i}` (`lem:commoncut`(v)).

Hence (**`two_coordinate_rp`**): if every row five-type measure is reflection positive at every
chamber cut, then `𝒬` is reflection positive at every `ϑ_{c,i}`, for both coordinates.

**How this combines with (b), (c) and (f).** The paper's hypothesis is that the five weights
`a_{(·, t')}` satisfy the hypotheses of (b), (c) or (f) for the row data of `c` at `𝔣(t')`,
together with the root envelope and `a_D ≥ δ a_L`. The conclusion of each of (b), (c) and (f)
is `RPAll (D.Q a')` for the row datum `D` (`FiveType/Criteria.lean`). That conclusion is the
hypothesis `hRP0`/`hRP1` here, so the two results compose directly.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings ReflectionCut

namespace TwoCoord

/-! ## Field types, objects and patterns -/

/-- The field types `L, F, E`: the named graphs `G_L, G_F, G_E` from which a coordinate law is
taken (`def:two-coordinate-five-type`). -/
inductive FieldTy
  | L
  | F
  | E
  deriving DecidableEq

/-- The objects of a field type: `O_L = ℤ/6ℤ`, `O_F = O_E = {0, 1, 2}`. -/
def FieldTy.Obj : FieldTy → Type
  | .L => ZMod 6
  | .F => Fin 3
  | .E => Fin 3

instance FieldTy.instFintypeObj : (f : FieldTy) → Fintype f.Obj
  | .L => inferInstanceAs (Fintype (ZMod 6))
  | .F => inferInstanceAs (Fintype (Fin 3))
  | .E => inferInstanceAs (Fintype (Fin 3))

instance FieldTy.instDecEqObj : (f : FieldTy) → DecidableEq f.Obj
  | .L => inferInstanceAs (DecidableEq (ZMod 6))
  | .F => inferInstanceAs (DecidableEq (Fin 3))
  | .E => inferInstanceAs (DecidableEq (Fin 3))

/-- The field type `𝔣(t)` of a type: `𝔣(L) = L`, `𝔣(D) = F`, `𝔣(S) = 𝔣(R) = 𝔣(C) = E`. -/
def fieldOf : Ty → FieldTy
  | .L => .L
  | .D => .F
  | .S => .E
  | .R => .E
  | .C => .E

/-- The index set of the pattern set `P_t`: one root, three folds, two matchings, six merges,
two constants. -/
def PatIdx : Ty → Type
  | .L => Unit
  | .D => Fin 3
  | .S => Fin 2
  | .R => Fin 2 × Fin 3
  | .C => Fin 2

instance instFintypePatIdx : (t : Ty) → Fintype (PatIdx t)
  | .L => inferInstanceAs (Fintype Unit)
  | .D => inferInstanceAs (Fintype (Fin 3))
  | .S => inferInstanceAs (Fintype (Fin 2))
  | .R => inferInstanceAs (Fintype (Fin 2 × Fin 3))
  | .C => inferInstanceAs (Fintype (Fin 2))

/-- The patterns `P_t` as maps `ℤ/6ℤ → O_{𝔣(t)}`: the identity, the folds `F_j`, the matchings
`E_s`, the merges `G_{sk}` (values `0, 1 ∈ O_E`) and the constants `C_0 = C_1 = 0`. -/
def patMap : (t : Ty) → PatIdx t → ZMod 6 → (fieldOf t).Obj
  | .L, _ => fun u => (u : ZMod 6)
  | .D, j => fold (j : Fin 3)
  | .S, s => matching (s : Fin 2)
  | .R, sk => fun u => (merge (sk : Fin 2 × Fin 3).1 (sk : Fin 2 × Fin 3).2 u).castSucc
  | .C, _ => fun _ => (0 : Fin 3)

/-- The degree `deg t₀ + deg t₁` of a state. -/
def stateDeg (t0 t1 : Ty) : ℕ := t0.deg + t1.deg

/-! ## Emissions, components and the measure `𝒬` -/

variable {X Λ : Type*} [Fintype X] [DecidableEq X] [Fintype Λ] [DecidableEq Λ]

/-- The emission `e_φ(y)_{(u₀,u₁,ℓ)} = y_{φ₀(u₀), φ₁(u₁), ℓ}`. -/
def emit {O0 O1 : Type*} (φ0 : ZMod 6 → O0) (φ1 : ZMod 6 → O1) (y : O0 × O1 × Λ → X) :
    ZMod 6 × ZMod 6 × Λ → X :=
  fun w => y (φ0 w.1, φ1 w.2.1, w.2.2)

variable (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))

/-- **The component `Π_{t,φ}`**: the law of `e_φ(y)` for `y ∼ λ_{𝔣(t₀)𝔣(t₁)}`. -/
noncomputable def comp (t0 : Ty) (φ0 : PatIdx t0) (t1 : Ty) (φ1 : PatIdx t1) :
    ((ZMod 6 × ZMod 6 × Λ → X) → ℝ) →ₗ[ℝ] ℝ :=
  pushFunctional (lawL (lam (fieldOf t0) (fieldOf t1))) (emit (patMap t0 φ0) (patMap t1 φ1))

/-- `π_t = ∑_{φ ∈ P_{t₀} × P_{t₁}} Π_{t,φ}` for the state `t = (t₀, t₁)`. -/
noncomputable def piT2 (t0 t1 : Ty) : ((ZMod 6 × ZMod 6 × Λ → X) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ φ0 : PatIdx t0, ∑ φ1 : PatIdx t1, comp lam t0 φ0 t1 φ1

/-- **The two-coordinate measure** `𝒬 = ∑_t a_t π_t`. -/
noncomputable def Q2 (a : Ty → Ty → ℝ) : ((ZMod 6 × ZMod 6 × Λ → X) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ t0, ∑ t1, a t0 t1 • piT2 lam t0 t1

/-! ## Row data -/

/-- The rows of the coordinate 0: `(y_{o,·,·})_o`. -/
def rows0 {O0 O' : Type*} (y : O0 × O' × Λ → X) (o : O0) : O' × Λ → X :=
  fun p => y (o, p.1, p.2)

/-- The rows of the coordinate 1: `(y_{·,o,·})_o`. -/
def rows1 {O' O1 : Type*} (y : O' × O1 × Λ → X) (o : O1) : O' × Λ → X :=
  fun p => y (p.1, o, p.2)

/-- **The row data of the coordinate 0 at `𝔣'` form the five-type datum `D`**
(`def:two-coordinate-five-type`, hypothesis of `lem:five-type`(d)). Field by field:
* `piL`: `π_L` is the law of the six rows of `y ∼ λ_{L𝔣'}`;
* `piF`: `π_F` is the law of the three rows of `y ∼ λ_{F𝔣'}`;
* `piE`: `π_E` is the law of the three rows of `y ∼ λ_{E𝔣'}`;
* `Gam`: `Γ` is the law of the rows `0, 1` of `λ_{E𝔣'}`;
* `nu`: `ν` is the law of the row `0` of `λ_{E𝔣'}`.

The conditional references `ν^b` and the kernels are those of `D`; the datum's own fields make
them consistent with these laws. -/
structure RowDatum0 (f' : FieldTy) (D : Datum (f'.Obj × Λ → X)) : Prop where
  piL : D.piL = (lam .L f').map (fun y => (rows0 y : ZMod 6 → f'.Obj × Λ → X))
  piF : D.piF = (lam .F f').map (fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X))
  piE : D.piE = (lam .E f').map (fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X))
  Gam : D.Gam = (lam .E f').map (fun y (i : Fin 2) => rows0 y (Fin.castSucc i : Fin 3))
  nu : D.nu = (lam .E f').map (fun y => rows0 y (0 : Fin 3))

/-- **The row data of the coordinate 1 at `𝔣'` form the five-type datum `D`**: as
`RowDatum0`, with the coordinates exchanged (the laws `λ_{𝔣'L}`, `λ_{𝔣'F}`, `λ_{𝔣'E}`). -/
structure RowDatum1 (f' : FieldTy) (D : Datum (f'.Obj × Λ → X)) : Prop where
  piL : D.piL = (lam f' .L).map (fun y => (rows1 y : ZMod 6 → f'.Obj × Λ → X))
  piF : D.piF = (lam f' .F).map (fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X))
  piE : D.piE = (lam f' .E).map (fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X))
  Gam : D.Gam = (lam f' .E).map (fun y (i : Fin 2) => rows1 y (Fin.castSucc i : Fin 3))
  nu : D.nu = (lam f' .E).map (fun y => rows1 y (0 : Fin 3))

/-- The emission of a row configuration in the coordinate 0:
`e_{φ'}(Ψ)_{(u₀,u₁,ℓ)} = Ψ_{u₀}(φ'(u₁), ℓ)`. -/
def emitRow0 {O' : Type*} (φ' : ZMod 6 → O') (Ψ : ZMod 6 → O' × Λ → X) :
    ZMod 6 × ZMod 6 × Λ → X :=
  fun w => Ψ w.1 (φ' w.2.1, w.2.2)

/-- The emission of a row configuration in the coordinate 1:
`e_{φ'}(Ψ)_{(u₀,u₁,ℓ)} = Ψ_{u₁}(φ'(u₀), ℓ)`. -/
def emitRow1 {O' : Type*} (φ' : ZMod 6 → O') (Ψ : ZMod 6 → O' × Λ → X) :
    ZMod 6 × ZMod 6 × Λ → X :=
  fun w => Ψ w.2.1 (φ' w.1, w.2.2)

/-! ## Pushforwards are linear in the measure -/

theorem push_sum {Ω Ξ ι : Type*} (s : Finset ι) (L : ι → (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω → Ξ) :
    pushFunctional (∑ i ∈ s, L i) e = ∑ i ∈ s, pushFunctional (L i) e := by
  refine LinearMap.ext fun f => ?_
  change (∑ i ∈ s, L i) (f ∘ e) = (∑ i ∈ s, pushFunctional (L i) e) f
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  rfl

theorem push_smul {Ω Ξ : Type*} (c : ℝ) (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω → Ξ) :
    pushFunctional (c • L) e = c • pushFunctional L e := by
  refine LinearMap.ext fun f => ?_
  rfl

/-! ## The slice identity in the coordinate 0 -/

section Slice0

variable (t1 : Ty) (φ1 : PatIdx t1) (D : Datum ((fieldOf t1).Obj × Λ → X))

/-- The root slice: `Π_{(L,t'),(id,φ')} = (e_{φ'})_* π_L`. -/
theorem comp_root0 (hD : RowDatum0 lam (fieldOf t1) D) (φ0 : PatIdx .L) :
    comp lam .L φ0 t1 φ1 = pushFunctional D.compL (emitRow0 (patMap t1 φ1)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf .L) (fieldOf t1)).expect (f ∘ emit (patMap .L φ0) (patMap t1 φ1)) =
    D.piL.expect (f ∘ emitRow0 (patMap t1 φ1))
  rw [hD.piL, FiniteLaw.expect_map]
  rfl

/-- The fold slices: `Π_{(D,t'),(F_j,φ')} = (e_{φ'})_* Π_{F_j}(π_F)`. -/
theorem comp_fold0 (hD : RowDatum0 lam (fieldOf t1) D) (j : Fin 3) :
    comp lam .D j t1 φ1 = pushFunctional (D.compF j) (emitRow0 (patMap t1 φ1)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf .D) (fieldOf t1)).expect (f ∘ emit (patMap .D j) (patMap t1 φ1)) =
    (patternLaw (fold j) D.piF).expect (f ∘ emitRow0 (patMap t1 φ1))
  rw [patternLaw, FiniteLaw.expect_map, hD.piF, FiniteLaw.expect_map]
  rfl

/-- The matching slices: `Π_{(S,t'),(E_s,φ')} = (e_{φ'})_* Π_{E_s}(π_E)`. -/
theorem comp_matching0 (hD : RowDatum0 lam (fieldOf t1) D) (s : Fin 2) :
    comp lam .S s t1 φ1 = pushFunctional (D.compE s) (emitRow0 (patMap t1 φ1)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf .S) (fieldOf t1)).expect (f ∘ emit (patMap .S s) (patMap t1 φ1)) =
    (patternLaw (matching s) D.piE).expect (f ∘ emitRow0 (patMap t1 φ1))
  rw [patternLaw, FiniteLaw.expect_map, hD.piE, FiniteLaw.expect_map]
  rfl

/-- The merge slices: `Π_{(R,t'),(G_{sk},φ')} = (e_{φ'})_* Π_{G_{sk}}(Γ)`; a merge reads only
the rows `0, 1`. -/
theorem comp_merge0 (hD : RowDatum0 lam (fieldOf t1) D) (s : Fin 2) (k : Fin 3) :
    comp lam .R ((s, k) : Fin 2 × Fin 3) t1 φ1 =
      pushFunctional (D.compG s k) (emitRow0 (patMap t1 φ1)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf .R) (fieldOf t1)).expect
      (f ∘ emit (patMap .R ((s, k) : Fin 2 × Fin 3)) (patMap t1 φ1)) =
    (patternLaw (merge s k) D.Gam).expect (f ∘ emitRow0 (patMap t1 φ1))
  rw [patternLaw, FiniteLaw.expect_map, hD.Gam, FiniteLaw.expect_map]
  rfl

/-- The constant slices: `Π_{(C,t'),(C_k,φ')} = (e_{φ'})_* Π_0(ν)`; a constant reads only the
row `0`. -/
theorem comp_const0 (hD : RowDatum0 lam (fieldOf t1) D) (k : PatIdx .C) :
    comp lam .C k t1 φ1 = pushFunctional D.compC (emitRow0 (patMap t1 φ1)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf .C) (fieldOf t1)).expect (f ∘ emit (patMap .C k) (patMap t1 φ1)) =
    (patternLaw Datum.constPat D.nu1).expect (f ∘ emitRow0 (patMap t1 φ1))
  rw [patternLaw, FiniteLaw.expect_map, Datum.nu1, FiniteLaw.expect_map, hD.nu,
    FiniteLaw.expect_map]
  rfl

/-- **The type slices**: for each type `t₀`, `∑_{φ₀ ∈ P_{t₀}} Π_{(t₀,t'),(φ₀,φ')}` is the image
of `π_{t₀}` of the row data under the emission `e_{φ'}`. -/
theorem typeSlice0 (hD : RowDatum0 lam (fieldOf t1) D) (t0 : Ty) :
    ∑ φ0 : PatIdx t0, comp lam t0 φ0 t1 φ1 =
      pushFunctional (D.piT t0) (emitRow0 (patMap t1 φ1)) := by
  cases t0 with
  | L =>
    change ∑ φ0 : Unit, comp lam .L φ0 t1 φ1 = pushFunctional D.compL _
    rw [Fintype.sum_unique]
    exact comp_root0 lam t1 φ1 D hD _
  | D =>
    change ∑ j : Fin 3, comp lam .D j t1 φ1 = pushFunctional (∑ j, D.compF j) _
    rw [push_sum]
    exact Finset.sum_congr rfl fun j _ => comp_fold0 lam t1 φ1 D hD j
  | S =>
    change ∑ s : Fin 2, comp lam .S s t1 φ1 = pushFunctional (∑ s, D.compE s) _
    rw [push_sum]
    exact Finset.sum_congr rfl fun s _ => comp_matching0 lam t1 φ1 D hD s
  | R =>
    change ∑ sk : Fin 2 × Fin 3, comp lam .R sk t1 φ1 =
      pushFunctional (∑ s, ∑ k, D.compG s k) _
    rw [Fintype.sum_prod_type, push_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [push_sum]
    exact Finset.sum_congr rfl fun k _ => comp_merge0 lam t1 φ1 D hD s k
  | C =>
    change ∑ k : Fin 2, comp lam .C k t1 φ1 = pushFunctional (∑ _k : Fin 2, D.compC) _
    rw [push_sum]
    exact Finset.sum_congr rfl fun k _ => comp_const0 lam t1 φ1 D hD k

end Slice0

/-- The slice of `𝒬` in the coordinate 0 at the coordinate-1 state `t'` and pattern `φ'`:
`∑_{t₀} a_{(t₀,t')} ∑_{φ₀} Π_{(t₀,t'),(φ₀,φ')}`. -/
noncomputable def slice0 (a : Ty → Ty → ℝ) (t1 : Ty) (φ1 : PatIdx t1) :
    ((ZMod 6 × ZMod 6 × Λ → X) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ t0, a t0 t1 • ∑ φ0 : PatIdx t0, comp lam t0 φ0 t1 φ1

/-- **`lem:five-type`(d), slice decomposition, coordinate 0.** The sum of the components
`a_t Π_{t,φ}` with `t₁ = t'` and `φ₁ = φ'` is the image of the five-type measure of the row data
of the coordinate 0 at `𝔣(t')`, with the weights `a_{(·,t')}`, under the emission `e_{φ'}`. -/
theorem slice0_eq (a : Ty → Ty → ℝ) (t1 : Ty) (φ1 : PatIdx t1)
    (D : Datum ((fieldOf t1).Obj × Λ → X)) (hD : RowDatum0 lam (fieldOf t1) D) :
    slice0 lam a t1 φ1 =
      pushFunctional (D.Q (fun t0 => a t0 t1)) (emitRow0 (patMap t1 φ1)) := by
  rw [slice0, Datum.Q, push_sum]
  refine Finset.sum_congr rfl fun t0 _ => ?_
  rw [push_smul, typeSlice0 lam t1 φ1 D hD t0]

omit [DecidableEq X] in
/-- **`𝒬` is the sum of its coordinate-0 slices**, over the coordinate-1 states and patterns. -/
theorem Q2_eq_slices0 (a : Ty → Ty → ℝ) :
    Q2 lam a = ∑ t1, ∑ φ1 : PatIdx t1, slice0 lam a t1 φ1 := by
  rw [Q2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t1 _ => ?_
  have h : ∀ t0, a t0 t1 • ∑ φ0 : PatIdx t0, ∑ φ1 : PatIdx t1, comp lam t0 φ0 t1 φ1 =
      ∑ φ1 : PatIdx t1, a t0 t1 • ∑ φ0 : PatIdx t0, comp lam t0 φ0 t1 φ1 := by
    intro t0
    rw [Finset.sum_comm, Finset.smul_sum]
  simp only [slice0, piT2]
  rw [Finset.sum_congr rfl fun t0 _ => h t0, Finset.sum_comm]

/-! ## The slice identity in the coordinate 1 -/

section Slice1

variable (t0 : Ty) (φ0 : PatIdx t0) (D : Datum ((fieldOf t0).Obj × Λ → X))

/-- The root slice in the coordinate 1. -/
theorem comp_root1 (hD : RowDatum1 lam (fieldOf t0) D) (φ1 : PatIdx .L) :
    comp lam t0 φ0 .L φ1 = pushFunctional D.compL (emitRow1 (patMap t0 φ0)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf t0) (fieldOf .L)).expect (f ∘ emit (patMap t0 φ0) (patMap .L φ1)) =
    D.piL.expect (f ∘ emitRow1 (patMap t0 φ0))
  rw [hD.piL, FiniteLaw.expect_map]
  rfl

/-- The fold slices in the coordinate 1. -/
theorem comp_fold1 (hD : RowDatum1 lam (fieldOf t0) D) (j : Fin 3) :
    comp lam t0 φ0 .D j = pushFunctional (D.compF j) (emitRow1 (patMap t0 φ0)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf t0) (fieldOf .D)).expect (f ∘ emit (patMap t0 φ0) (patMap .D j)) =
    (patternLaw (fold j) D.piF).expect (f ∘ emitRow1 (patMap t0 φ0))
  rw [patternLaw, FiniteLaw.expect_map, hD.piF, FiniteLaw.expect_map]
  rfl

/-- The matching slices in the coordinate 1. -/
theorem comp_matching1 (hD : RowDatum1 lam (fieldOf t0) D) (s : Fin 2) :
    comp lam t0 φ0 .S s = pushFunctional (D.compE s) (emitRow1 (patMap t0 φ0)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf t0) (fieldOf .S)).expect (f ∘ emit (patMap t0 φ0) (patMap .S s)) =
    (patternLaw (matching s) D.piE).expect (f ∘ emitRow1 (patMap t0 φ0))
  rw [patternLaw, FiniteLaw.expect_map, hD.piE, FiniteLaw.expect_map]
  rfl

/-- The merge slices in the coordinate 1. -/
theorem comp_merge1 (hD : RowDatum1 lam (fieldOf t0) D) (s : Fin 2) (k : Fin 3) :
    comp lam t0 φ0 .R ((s, k) : Fin 2 × Fin 3) =
      pushFunctional (D.compG s k) (emitRow1 (patMap t0 φ0)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf t0) (fieldOf .R)).expect
      (f ∘ emit (patMap t0 φ0) (patMap .R ((s, k) : Fin 2 × Fin 3))) =
    (patternLaw (merge s k) D.Gam).expect (f ∘ emitRow1 (patMap t0 φ0))
  rw [patternLaw, FiniteLaw.expect_map, hD.Gam, FiniteLaw.expect_map]
  rfl

/-- The constant slices in the coordinate 1. -/
theorem comp_const1 (hD : RowDatum1 lam (fieldOf t0) D) (k : PatIdx .C) :
    comp lam t0 φ0 .C k = pushFunctional D.compC (emitRow1 (patMap t0 φ0)) := by
  refine LinearMap.ext fun f => ?_
  change (lam (fieldOf t0) (fieldOf .C)).expect (f ∘ emit (patMap t0 φ0) (patMap .C k)) =
    (patternLaw Datum.constPat D.nu1).expect (f ∘ emitRow1 (patMap t0 φ0))
  rw [patternLaw, FiniteLaw.expect_map, Datum.nu1, FiniteLaw.expect_map, hD.nu,
    FiniteLaw.expect_map]
  rfl

/-- **The type slices in the coordinate 1.** -/
theorem typeSlice1 (hD : RowDatum1 lam (fieldOf t0) D) (t1 : Ty) :
    ∑ φ1 : PatIdx t1, comp lam t0 φ0 t1 φ1 =
      pushFunctional (D.piT t1) (emitRow1 (patMap t0 φ0)) := by
  cases t1 with
  | L =>
    refine (Fintype.sum_unique (ι := Unit) (fun φ1 => comp lam t0 φ0 .L φ1)).trans ?_
    exact comp_root1 lam t0 φ0 D hD _
  | D =>
    change ∑ j : Fin 3, comp lam t0 φ0 .D j = pushFunctional (∑ j, D.compF j) _
    rw [push_sum]
    exact Finset.sum_congr rfl fun j _ => comp_fold1 lam t0 φ0 D hD j
  | S =>
    change ∑ s : Fin 2, comp lam t0 φ0 .S s = pushFunctional (∑ s, D.compE s) _
    rw [push_sum]
    exact Finset.sum_congr rfl fun s _ => comp_matching1 lam t0 φ0 D hD s
  | R =>
    refine (Fintype.sum_prod_type (fun sk : Fin 2 × Fin 3 => comp lam t0 φ0 .R sk)).trans ?_
    change _ = pushFunctional (∑ s, ∑ k, D.compG s k) _
    rw [push_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [push_sum]
    exact Finset.sum_congr rfl fun k _ => comp_merge1 lam t0 φ0 D hD s k
  | C =>
    change ∑ k : Fin 2, comp lam t0 φ0 .C k = pushFunctional (∑ _k : Fin 2, D.compC) _
    rw [push_sum]
    exact Finset.sum_congr rfl fun k _ => comp_const1 lam t0 φ0 D hD k

end Slice1

/-- The slice of `𝒬` in the coordinate 1 at the coordinate-0 state `t'` and pattern `φ'`:
`∑_{t₁} a_{(t',t₁)} ∑_{φ₁} Π_{(t',t₁),(φ',φ₁)}`. -/
noncomputable def slice1 (a : Ty → Ty → ℝ) (t0 : Ty) (φ0 : PatIdx t0) :
    ((ZMod 6 × ZMod 6 × Λ → X) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ t1, a t0 t1 • ∑ φ1 : PatIdx t1, comp lam t0 φ0 t1 φ1

/-- **`lem:five-type`(d), slice decomposition, coordinate 1.** -/
theorem slice1_eq (a : Ty → Ty → ℝ) (t0 : Ty) (φ0 : PatIdx t0)
    (D : Datum ((fieldOf t0).Obj × Λ → X)) (hD : RowDatum1 lam (fieldOf t0) D) :
    slice1 lam a t0 φ0 =
      pushFunctional (D.Q (fun t1 => a t0 t1)) (emitRow1 (patMap t0 φ0)) := by
  rw [slice1, Datum.Q, push_sum]
  refine Finset.sum_congr rfl fun t1 _ => ?_
  rw [push_smul, typeSlice1 lam t0 φ0 D hD t1]

omit [DecidableEq X] in
/-- **`𝒬` is the sum of its coordinate-1 slices**, over the coordinate-0 states and patterns. -/
theorem Q2_eq_slices1 (a : Ty → Ty → ℝ) :
    Q2 lam a = ∑ t0, ∑ φ0 : PatIdx t0, slice1 lam a t0 φ0 := by
  rw [Q2]
  refine Finset.sum_congr rfl fun t0 _ => ?_
  simp only [slice1, piT2, Finset.smul_sum]
  rw [Finset.sum_comm]

/-! ## Half-locality of the emissions and reflection positivity -/

/-- The chamber cut `ϑ_{0,i}`: the reflection `ϑ_i` in the coordinate 0, with plus half
`H_i × ℤ/6ℤ × Λ`. -/
def cut0 (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (i : ZMod 6) :
    ReflectionCut (ZMod 6 × ZMod 6 × Λ) :=
  (chamberCut i).prodLeft (ZMod 6 × Λ)

/-- The chamber cut `ϑ_{1,i}`: the reflection `ϑ_i` in the coordinate 1, with plus half
`ℤ/6ℤ × H_i × Λ`. -/
def cut1 (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (i : ZMod 6) :
    ReflectionCut (ZMod 6 × ZMod 6 × Λ) :=
  ((chamberCut i).prodLeft Λ).prodRight (ZMod 6)

/-- **Half-local maps carry cut forms** (`lem:commoncut`(v)): if `e` maps the plus half and the
reflected half of a configuration by the same map `φ` of half configurations, then the cut
form of the image at `d` is the cut form at `c` of the pulled-back half functions. -/
theorem form_push_halfLocal {V W A B : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (c : ReflectionCut V) (d : ReflectionCut W) (L : ((V → A) → ℝ) →ₗ[ℝ] ℝ)
    (e : (V → A) → (W → B)) (φ : (c.Half → A) → (d.Half → B))
    (hplus : ∀ z, (fun w : d.Half => e z w.1) = φ (fun v : c.Half => z v.1))
    (hminus : ∀ z, (fun w : d.Half => e z (d.flip w.1)) = φ (fun v : c.Half => z (c.flip v.1)))
    (F G : (d.Half → B) → ℝ) :
    d.form (pushFunctional L e) F G = c.form L (F ∘ φ) (G ∘ φ) := by
  change L (fun z => F (fun w => e z w.1) * G (fun w => e z (d.flip w.1))) =
    L (fun z => F (φ (fun v => z v.1)) * G (φ (fun v => z (c.flip v.1))))
  congr 1
  funext z
  rw [hplus z, hminus z]

/-- **Half-local maps preserve reflection positivity** (`lem:commoncut`(v)). -/
theorem positive_push_halfLocal {V W A B : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {c : ReflectionCut V} (d : ReflectionCut W) {L : ((V → A) → ℝ) →ₗ[ℝ] ℝ}
    (hL : c.Positive L) (e : (V → A) → (W → B)) (φ : (c.Half → A) → (d.Half → B))
    (hplus : ∀ z, (fun w : d.Half => e z w.1) = φ (fun v : c.Half => z v.1))
    (hminus : ∀ z, (fun w : d.Half => e z (d.flip w.1)) = φ (fun v : c.Half => z (c.flip v.1))) :
    d.Positive (pushFunctional L e) := by
  constructor
  · intro F G
    rw [form_push_halfLocal c d L e φ hplus hminus, form_push_halfLocal c d L e φ hplus hminus]
    exact hL.symmetric _ _
  · intro F
    rw [form_push_halfLocal c d L e φ hplus hminus]
    exact hL.nonneg _

omit [Fintype X] [DecidableEq X] in
/-- **The coordinate-0 emission is half-local** for `ϑ_i` and `ϑ_{0,i}`, so it carries
reflection positivity at `ϑ_i` to reflection positivity at `ϑ_{0,i}`. -/
theorem positive_emitRow0 {O' : Type*} (ψ : ZMod 6 → O') (i : ZMod 6)
    {L : ((ZMod 6 → O' × Λ → X) → ℝ) →ₗ[ℝ] ℝ} (hL : (chamberCut i).Positive L) :
    (cut0 Λ i).Positive (pushFunctional L (emitRow0 ψ)) :=
  positive_push_halfLocal (cut0 Λ i) hL (emitRow0 ψ)
    (fun x w => x ⟨w.1.1, (Finset.mem_product.mp w.2).1⟩ (ψ w.1.2.1, w.1.2.2))
    (fun _ => rfl) (fun _ => rfl)

omit [Fintype X] [DecidableEq X] in
/-- **The coordinate-1 emission is half-local** for `ϑ_i` and `ϑ_{1,i}`. -/
theorem positive_emitRow1 {O' : Type*} (ψ : ZMod 6 → O') (i : ZMod 6)
    {L : ((ZMod 6 → O' × Λ → X) → ℝ) →ₗ[ℝ] ℝ} (hL : (chamberCut i).Positive L) :
    (cut1 Λ i).Positive (pushFunctional L (emitRow1 ψ)) :=
  positive_push_halfLocal (cut1 Λ i) hL (emitRow1 ψ)
    (fun x w => x ⟨w.1.2.1, (Finset.mem_product.mp (Finset.mem_product.mp w.2).2).1⟩
      (ψ w.1.1, w.1.2.2))
    (fun _ => rfl) (fun _ => rfl)

/-- **`lem:five-type`(d), coordinate 0.** If, for each field type `𝔣'`, the row data of the
coordinate 0 at `𝔣'` form the five-type datum `D0 𝔣'`, and for each type `t'` the row
five-type measure with the weights `a_{(·,t')}` is reflection positive at every chamber cut
(the conclusion of (b), (c) or (f)), then `𝒬` is reflection positive at every `ϑ_{0,i}`. -/
theorem two_coordinate_rp0 (a : Ty → Ty → ℝ) (D0 : (f' : FieldTy) → Datum (f'.Obj × Λ → X))
    (hD0 : ∀ f', RowDatum0 lam f' (D0 f'))
    (hRP0 : ∀ t1, RPAll ((D0 (fieldOf t1)).Q (fun t0 => a t0 t1))) (i : ZMod 6) :
    (cut0 Λ i).Positive (Q2 lam a) := by
  rw [Q2_eq_slices0]
  refine Positive.sum _ fun t1 _ => Positive.sum _ fun φ1 _ => ?_
  rw [slice0_eq lam a t1 φ1 (D0 (fieldOf t1)) (hD0 _)]
  exact positive_emitRow0 _ i (hRP0 t1 i)

/-- **`lem:five-type`(d), coordinate 1.** -/
theorem two_coordinate_rp1 (a : Ty → Ty → ℝ) (D1 : (f' : FieldTy) → Datum (f'.Obj × Λ → X))
    (hD1 : ∀ f', RowDatum1 lam f' (D1 f'))
    (hRP1 : ∀ t0, RPAll ((D1 (fieldOf t0)).Q (fun t1 => a t0 t1))) (i : ZMod 6) :
    (cut1 Λ i).Positive (Q2 lam a) := by
  rw [Q2_eq_slices1]
  refine Positive.sum _ fun t0 _ => Positive.sum _ fun φ0 _ => ?_
  rw [slice1_eq lam a t0 φ0 (D1 (fieldOf t0)) (hD1 _)]
  exact positive_emitRow1 _ i (hRP1 t0 i)

/-- **`lem:five-type`(d), the slice principle.** Suppose that for each coordinate `c` and each
field type `𝔣'` the row data of `c` at `𝔣'` form a five-type datum (`D0 𝔣'`, `D1 𝔣'`), and
that for each type `t'` the row five-type measure with the weights of the states `t` with
`t_{1-c} = t'` is reflection positive at every chamber cut. Then `𝒬` is reflection positive at
every chamber cut `ϑ_{c,i}` of both coordinates.

The paper's hypothesis on the weights (those of (b), (c) or (f), with the root envelope and
`a_D ≥ δ a_L`) enters through its conclusion `RPAll`, proved in `FiveType/Criteria.lean`. -/
theorem two_coordinate_rp (a : Ty → Ty → ℝ)
    (D0 D1 : (f' : FieldTy) → Datum (f'.Obj × Λ → X))
    (hD0 : ∀ f', RowDatum0 lam f' (D0 f')) (hD1 : ∀ f', RowDatum1 lam f' (D1 f'))
    (hRP0 : ∀ t1, RPAll ((D0 (fieldOf t1)).Q (fun t0 => a t0 t1)))
    (hRP1 : ∀ t0, RPAll ((D1 (fieldOf t0)).Q (fun t1 => a t0 t1))) :
    ∀ i : ZMod 6, (cut0 Λ i).Positive (Q2 lam a) ∧ (cut1 Λ i).Positive (Q2 lam a) :=
  fun i => ⟨two_coordinate_rp0 lam a D0 hD0 hRP0 i, two_coordinate_rp1 lam a D1 hD1 hRP1 i⟩

end TwoCoord

end Sarkozy.FiveType
