module

public import Sarkozy.IndexSupport.Sectors
public import Sarkozy.ProbabilityConstructions
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The index-support inequality for an abstract sector decomposition

This file proves the inequality behind `lem:record:common-mean` (Index-support lemma)
for an arbitrary orthogonal sector decomposition `L²(Ω) = ⊕_s H_s` of the functions on
a finite index space `Ω` with its uniform probability, an arbitrary random set of
retained sectors, and an arbitrary operator `𝒯` that preserves every sector, is the
identity on the constants, and has norm at most `δ_s` on `H_s`.

Vector-valued maps `Z : Ω → (ι → ℝ)` (the paper's maps `Ω → ℝ^{𝒳_+}`) are acted on
componentwise (`act`). For a real matrix `M` on `ι`,
`pairing M X Y = E_ω ⟨X(ω), M Y(ω)⟩` with `E_ω` the uniform expectation.

The retained sectors are described by a finite law on a set `R` of revelation values
and a map `retained : R → Finset S`; the revealed projection of `Z` at `r` is
`Z^r = (∑_{s ∈ retained r} Π_s) Z`. The paper's depth law is the special case of
`Sarkozy/IndexSupport/Filtration.lean`. The proof needs only
`δ_s ≤ Pr(s ∈ retained r)` (the paper's laws have equality; compare the remark after
`lem:record:common-mean`, "The proof uses only `Pr(S ⊆ 𝒥) ≥ δ_S`").

Main results (`IndexSupport.mean_le_energy`, `IndexSupport.common_mean`,
`IndexSupport.form_le_energies`): `V_L ≥ e_L ≥ 0`, `V_R ≥ e_R ≥ 0`,

* (a) `|𝖩 - ⟨E X, Γ E Y⟩| ≤ ½[(V_L - e_L) + (V_R - e_R)]`,
* (b) `|𝖩| ≤ V_L^{1/2} V_R^{1/2}`.

The proof follows the paper's: orthogonality of the sectors for every form
`E_ω⟨·, M ·⟩`, the energy identity `V = ∑_s Pr(s retained) ‖Z_s‖²_M`, and on each sector
the bound `|E_ω⟨X_s, Γ 𝒯 Y_s⟩| ≤ δ_s ‖X_s‖_{M_L} ‖Y_s‖_{M_R}`. Instead of the factorization
`Γ = M_L^{1/2} C M_R^{1/2}` of `lem:record:block-gram`(a) we use the equivalent
discriminant form of the joint Gram positivity, lifted to `L²(Ω; ℝ^ι)`, together with a
sum-of-squares decomposition `M_R = ∑_i v_i v_iᵀ` (`Matrix.posSemidef_iff_eq_sum_vecMulVec`)
to show `‖𝒯 Z‖_{M_R} ≤ δ_s ‖Z‖_{M_R}` on `H_s ⊗ ℝ^ι`.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

section VectorMaps

variable {Ω ι : Type*} [Fintype Ω]

/-- Componentwise action of a scalar operator (a matrix on `Ω`) on a vector-valued map. -/
def act (A : Matrix Ω Ω ℝ) (Z : Ω → ι → ℝ) : Ω → ι → ℝ :=
  fun ω a => ∑ η, A ω η * Z η a

/-- The component of a vector-valued map at the label `a`. -/
def col (Z : Ω → ι → ℝ) (a : ι) : Ω → ℝ := fun ω => Z ω a

/-- The scalar map `ω ↦ ⟨w, Z(ω)⟩`. -/
def vproj [Fintype ι] (w : ι → ℝ) (Z : Ω → ι → ℝ) : Ω → ℝ := fun ω => w ⬝ᵥ Z ω

/-- The pointwise action `ω ↦ M Z(ω)` of a matrix on the labels. -/
def pmul [Fintype ι] (M : Matrix ι ι ℝ) (Z : Ω → ι → ℝ) : Ω → ι → ℝ := fun ω => M *ᵥ Z ω

/-- The mean `E_ω Z(ω)` for the uniform probability on `Ω`. -/
noncomputable def vmean [Nonempty Ω] (Z : Ω → ι → ℝ) : ι → ℝ :=
  fun a => (FiniteLaw.uniform Ω).expect (fun ω => Z ω a)

/-- The form `E_ω ⟨X(ω), M Y(ω)⟩` for the uniform probability on `Ω`. -/
noncomputable def pairing [Fintype ι] (M : Matrix ι ι ℝ) (X Y : Ω → ι → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, X ω ⬝ᵥ (M *ᵥ Y ω)

theorem pairing_eq_expect [Fintype ι] [Nonempty Ω] (M : Matrix ι ι ℝ) (X Y : Ω → ι → ℝ) :
    pairing M X Y = (FiniteLaw.uniform Ω).expect (fun ω => X ω ⬝ᵥ (M *ᵥ Y ω)) := by
  rw [FiniteLaw.expect_uniform, pairing, div_eq_inv_mul]

theorem col_act (A : Matrix Ω Ω ℝ) (Z : Ω → ι → ℝ) (a : ι) :
    col (act A Z) a = A *ᵥ col Z a := by
  ext ω
  simp only [col, act, Matrix.mulVec, dotProduct]

omit [Fintype Ω] in
theorem ext_col {Z Z' : Ω → ι → ℝ} (h : ∀ a, col Z a = col Z' a) : Z = Z' := by
  funext ω a
  exact congrFun (h a) ω

theorem act_act (A B : Matrix Ω Ω ℝ) (Z : Ω → ι → ℝ) : act A (act B Z) = act (A * B) Z := by
  apply ext_col
  intro a
  simp only [col_act, Matrix.mulVec_mulVec]

theorem act_one [DecidableEq Ω] (Z : Ω → ι → ℝ) : act 1 Z = Z := by
  apply ext_col
  intro a
  simp only [col_act, Matrix.one_mulVec]

theorem act_sum_left {S : Type*} (F : Finset S) (A : S → Matrix Ω Ω ℝ) (Z : Ω → ι → ℝ) :
    act (∑ s ∈ F, A s) Z = ∑ s ∈ F, act (A s) Z := by
  funext ω a
  simp only [act, Finset.sum_apply, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem act_sum_right {S : Type*} (A : Matrix Ω Ω ℝ) (F : Finset S) (Z : S → Ω → ι → ℝ) :
    act A (∑ s ∈ F, Z s) = ∑ s ∈ F, act A (Z s) := by
  funext ω a
  simp only [act, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem act_meanMatrix [Nonempty Ω] (Z : Ω → ι → ℝ) :
    act (meanMatrix Ω) Z = fun _ => vmean Z := by
  funext ω a
  simp only [act, meanMatrix_apply, vmean, FiniteLaw.expect, FiniteLaw.uniform]

variable [Fintype ι]

theorem vproj_act (w : ι → ℝ) (A : Matrix Ω Ω ℝ) (Z : Ω → ι → ℝ) :
    vproj w (act A Z) = A *ᵥ vproj w Z := by
  funext ω
  simp only [vproj, act, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro η _
  apply sum_congr rfl
  intro a _
  ring

theorem act_pmul (A : Matrix Ω Ω ℝ) (M : Matrix ι ι ℝ) (Z : Ω → ι → ℝ) :
    act A (pmul M Z) = pmul M (act A Z) := by
  funext ω a
  simp only [act, pmul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro η _
  ring

theorem pairing_eq_sum_col (M : Matrix ι ι ℝ) (X Y : Ω → ι → ℝ) :
    pairing M X Y = (Fintype.card Ω : ℝ)⁻¹ * ∑ a, col X a ⬝ᵥ col (pmul M Y) a := by
  rw [pairing]
  congr 1
  simp only [dotProduct, col, pmul]
  rw [Finset.sum_comm]

theorem pairing_sum_left {S : Type*} (F : Finset S) (M : Matrix ι ι ℝ)
    (X : S → Ω → ι → ℝ) (Y : Ω → ι → ℝ) :
    pairing M (∑ s ∈ F, X s) Y = ∑ s ∈ F, pairing M (X s) Y := by
  simp only [pairing, Finset.sum_apply, sum_dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem pairing_sum_right {S : Type*} (F : Finset S) (M : Matrix ι ι ℝ)
    (X : Ω → ι → ℝ) (Y : S → Ω → ι → ℝ) :
    pairing M X (∑ s ∈ F, Y s) = ∑ s ∈ F, pairing M X (Y s) := by
  simp only [pairing, Finset.sum_apply, Matrix.mulVec_sum, dotProduct_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem pairing_const [Nonempty Ω] (M : Matrix ι ι ℝ) (x y : ι → ℝ) :
    pairing M (fun _ : Ω => x) (fun _ => y) = x ⬝ᵥ (M *ᵥ y) := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [pairing, sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem pairing_smul_left (M : Matrix ι ι ℝ) (t : ℝ) (X Y : Ω → ι → ℝ) :
    pairing M (t • X) Y = t * pairing M X Y := by
  simp only [pairing, Pi.smul_apply, smul_dotProduct, smul_eq_mul, Finset.mul_sum]
  apply sum_congr rfl
  intro ω _
  ring

theorem pairing_nonneg {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (Z : Ω → ι → ℝ) :
    0 ≤ pairing M Z Z :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun ω _ => quadratic_nonneg_of_posSemidef hM (Z ω)))

/-- The quadratic form of the joint Gram block matrix. -/
theorem fromBlocks_quadratic (ML Γ MR : Matrix ι ι ℝ) (u v : ι → ℝ) :
    Sum.elim u v ⬝ᵥ (Matrix.fromBlocks ML Γ Γᵀ MR *ᵥ Sum.elim u v) =
      u ⬝ᵥ (ML *ᵥ u) + 2 * (u ⬝ᵥ (Γ *ᵥ v)) + v ⬝ᵥ (MR *ᵥ v) := by
  rw [Matrix.fromBlocks_mulVec]
  change Sum.elim u v ⬝ᵥ Sum.elim (ML *ᵥ u + Γ *ᵥ v) (Γᵀ *ᵥ u + MR *ᵥ v) = _
  rw [sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_add,
    Matrix.dotProduct_transpose_mulVec]
  ring

omit [Fintype ι] in
theorem joint_left {ML Γ MR : Matrix ι ι ℝ} (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef) :
    ML.PosSemidef := by
  have h := hG.submatrix (Sum.inl : ι → ι ⊕ ι)
  have he : (Matrix.fromBlocks ML Γ Γᵀ MR).submatrix Sum.inl Sum.inl = ML := by
    ext i j
    rfl
  rwa [he] at h

omit [Fintype ι] in
theorem joint_right {ML Γ MR : Matrix ι ι ℝ} (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef) :
    MR.PosSemidef := by
  have h := hG.submatrix (Sum.inr : ι → ι ⊕ ι)
  have he : (Matrix.fromBlocks ML Γ Γᵀ MR).submatrix Sum.inr Sum.inr = MR := by
    ext i j
    rfl
  rwa [he] at h

/-- Lifted Cauchy--Schwarz: the joint Gram positivity `[[M_L, Γ], [Γᵀ, M_R]] ⪰ 0` gives
`E_ω⟨X, Γ Y⟩² ≤ E_ω⟨X, M_L X⟩ · E_ω⟨Y, M_R Y⟩` for all vector-valued maps. -/
theorem pairing_sq_le {ML Γ MR : Matrix ι ι ℝ}
    (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef) (X Y : Ω → ι → ℝ) :
    pairing Γ X Y ^ 2 ≤ pairing ML X X * pairing MR Y Y := by
  have hpt (u v : ι → ℝ) : 0 ≤ u ⬝ᵥ (ML *ᵥ u) + 2 * (u ⬝ᵥ (Γ *ᵥ v)) + v ⬝ᵥ (MR *ᵥ v) := by
    rw [← fromBlocks_quadratic]
    exact quadratic_nonneg_of_posSemidef hG _
  have hquad (t : ℝ) : 0 ≤ pairing ML X X * (t * t) + (2 * pairing Γ X Y) * t +
      pairing MR Y Y := by
    have hsum : 0 ≤ (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, ((t • X ω) ⬝ᵥ (ML *ᵥ (t • X ω)) +
        2 * ((t • X ω) ⬝ᵥ (Γ *ᵥ Y ω)) + Y ω ⬝ᵥ (MR *ᵥ Y ω)) :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg (fun ω _ => hpt _ _))
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      Finset.sum_add_distrib, mul_add, ← Finset.mul_sum] at hsum
    simp only [pairing]
    nlinarith [hsum]
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

/-- The quadratic form of a positive semidefinite matrix is a sum of squares of linear
forms (from `Matrix.posSemidef_iff_eq_sum_vecMulVec`). -/
theorem exists_sum_sq {M : Matrix ι ι ℝ} (hM : M.PosSemidef) :
    ∃ (m : ℕ) (v : Fin m → ι → ℝ), ∀ z : ι → ℝ, z ⬝ᵥ (M *ᵥ z) = ∑ i, (v i ⬝ᵥ z) ^ 2 := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  refine ⟨m, v, fun z => ?_⟩
  rw [hv, Matrix.sum_mulVec, dotProduct_sum]
  apply sum_congr rfl
  intro i _
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq,
    Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

end VectorMaps

section Abstract

variable {Ω ι S : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Fintype S] [DecidableEq S]

/-- `𝒯` preserves every sector `H_s`, acts as the identity on the sector of constants,
and has norm at most `δ s` on `H_s`. (Norms are Euclidean on `ℝ^Ω`, equivalently
those of `L²(Ω)` for the uniform probability.) -/
structure SectorOperator (H : SectorSystem Ω S) (T : Matrix Ω Ω ℝ) (δ : S → ℝ) : Prop where
  maps : ∀ s f, H.proj s *ᵥ f = f → H.proj s *ᵥ (T *ᵥ f) = T *ᵥ f
  id_zero : ∀ f, H.proj H.zero *ᵥ f = f → T *ᵥ f = f
  norm_le : ∀ s f, H.proj s *ᵥ f = f → (T *ᵥ f) ⬝ᵥ (T *ᵥ f) ≤ δ s ^ 2 * (f ⬝ᵥ f)

/-- A random set of retained sectors: a finite law on revelation values `R`, and for
each value the finite set of sectors that its projection retains, always including the
constants. -/
structure Revelation (H : SectorSystem Ω S) (R : Type*) [Fintype R] where
  law : FiniteLaw R
  retained : R → Finset S
  zero_mem : ∀ r, H.zero ∈ retained r

variable {H : SectorSystem Ω S} {R : Type*} [Fintype R]

/-- The revealed projection `Z^r = (∑_{s ∈ retained r} Π_s) Z`. -/
def Revelation.reveal (V : Revelation H R) (r : R) (Z : Ω → ι → ℝ) : Ω → ι → ℝ :=
  act (∑ s ∈ V.retained r, H.proj s) Z

/-- The probability that sector `s` is retained. -/
noncomputable def Revelation.prob (V : Revelation H R) (s : S) : ℝ :=
  V.law.expect (fun r => if s ∈ V.retained r then 1 else 0)

/-- The random-inclusion energy `V_M(Z) = E_r E_ω ⟨Z^r(ω), M Z^r(ω)⟩`. -/
noncomputable def Revelation.energy (V : Revelation H R) (M : Matrix ι ι ℝ)
    (Z : Ω → ι → ℝ) : ℝ :=
  V.law.expect (fun r => pairing M (V.reveal r Z) (V.reveal r Z))

/-- The sector component `Z_s = Π_s Z`. -/
def SectorSystem.comp (H : SectorSystem Ω S) (s : S) (Z : Ω → ι → ℝ) : Ω → ι → ℝ :=
  act (H.proj s) Z

omit [Fintype ι] in
theorem SectorSystem.sum_comp (H : SectorSystem Ω S) (Z : Ω → ι → ℝ) :
    ∑ s, H.comp s Z = Z := by
  simp only [SectorSystem.comp]
  rw [← act_sum_left, H.sum_proj, act_one]

omit [Fintype ι] in
theorem SectorSystem.act_comp (H : SectorSystem Ω S) (s : S) (Z : Ω → ι → ℝ) :
    act (H.proj s) (H.comp s Z) = H.comp s Z := by
  rw [SectorSystem.comp, act_act, H.proj_mul_self]

omit [Fintype ι] in
theorem SectorSystem.col_mem (H : SectorSystem Ω S) {s : S} {Z : Ω → ι → ℝ}
    (hZ : act (H.proj s) Z = Z) (a : ι) : H.proj s *ᵥ col Z a = col Z a := by
  rw [← col_act, hZ]

omit [Fintype ι] in
theorem SectorSystem.act_of_col (H : SectorSystem Ω S) {s : S} {Z : Ω → ι → ℝ}
    (hZ : ∀ a, H.proj s *ᵥ col Z a = col Z a) : act (H.proj s) Z = Z := by
  apply ext_col
  intro a
  rw [col_act, hZ]

/-- Sectors are orthogonal for every form `E_ω ⟨·, M ·⟩`. -/
theorem SectorSystem.pairing_eq_zero (H : SectorSystem Ω S) (M : Matrix ι ι ℝ) {s t : S}
    (hst : s ≠ t) {X Y : Ω → ι → ℝ} (hX : act (H.proj s) X = X)
    (hY : act (H.proj t) Y = Y) : pairing M X Y = 0 := by
  have hMY : act (H.proj t) (pmul M Y) = pmul M Y := by rw [act_pmul, hY]
  rw [pairing_eq_sum_col]
  have h0 : ∑ a, col X a ⬝ᵥ col (pmul M Y) a = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact H.dotProduct_eq_zero hst (H.col_mem hX a) (H.col_mem hMY a)
  rw [h0, mul_zero]

omit [DecidableEq Ω] in
/-- On a sector, a sector-bounded operator contracts every form `E_ω⟨·, M ·⟩` with
`M ⪰ 0` by `δ_s²`. -/
theorem pairing_act_le {T : Matrix Ω Ω ℝ} {M : Matrix ι ι ℝ} {P : Matrix Ω Ω ℝ} {c : ℝ}
    (hM : M.PosSemidef) (hT : ∀ f, P *ᵥ f = f → (T *ᵥ f) ⬝ᵥ (T *ᵥ f) ≤ c ^ 2 * (f ⬝ᵥ f))
    {Z : Ω → ι → ℝ} (hZ : act P Z = Z) :
    pairing M (act T Z) (act T Z) ≤ c ^ 2 * pairing M Z Z := by
  obtain ⟨m, v, hv⟩ := exists_sum_sq hM
  have hrw (W : Ω → ι → ℝ) :
      pairing M W W = (Fintype.card Ω : ℝ)⁻¹ * ∑ i, vproj (v i) W ⬝ᵥ vproj (v i) W := by
    simp only [pairing, hv]
    rw [Finset.sum_comm]
    simp only [dotProduct, vproj, sq]
  rw [hrw, hrw]
  simp only [vproj_act]
  have hsum : ∑ i, (T *ᵥ vproj (v i) Z) ⬝ᵥ (T *ᵥ vproj (v i) Z) ≤
      c ^ 2 * ∑ i, vproj (v i) Z ⬝ᵥ vproj (v i) Z := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply hT
    rw [← vproj_act, hZ]
  have hc0 : 0 ≤ (Fintype.card Ω : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  calc _ ≤ (Fintype.card Ω : ℝ)⁻¹ * (c ^ 2 * ∑ i, vproj (v i) Z ⬝ᵥ vproj (v i) Z) :=
        mul_le_mul_of_nonneg_left hsum hc0
    _ = _ := by ring

/-- The decomposition of a component of the pairing over sectors. -/
theorem SectorSystem.pairing_decomp (H : SectorSystem Ω S) (Γ : Matrix ι ι ℝ)
    (T : Matrix Ω Ω ℝ) (hT : ∀ s f, H.proj s *ᵥ f = f → H.proj s *ᵥ (T *ᵥ f) = T *ᵥ f)
    (X Y : Ω → ι → ℝ) :
    pairing Γ X (act T Y) = ∑ s, pairing Γ (H.comp s X) (act T (H.comp s Y)) := by
  have hTs (t : S) : act (H.proj t) (act T (H.comp t Y)) = act T (H.comp t Y) := by
    apply H.act_of_col
    intro a
    rw [col_act]
    exact hT t _ (H.col_mem (H.act_comp t Y) a)
  conv_lhs => rw [← H.sum_comp X, ← H.sum_comp Y, act_sum_right, pairing_sum_left]
  apply sum_congr rfl
  intro s _
  rw [pairing_sum_right, Finset.sum_eq_single s]
  · intro t _ hts
    exact H.pairing_eq_zero Γ (Ne.symm hts) (H.act_comp s X) (hTs t)
  · intro h
    exact absurd (mem_univ s) h

/-- The energy identity `V_M(Z) = ∑_s Pr(s retained) ‖Z_s‖²_M`. -/
theorem Revelation.energy_eq (V : Revelation H R) (M : Matrix ι ι ℝ) (Z : Ω → ι → ℝ) :
    V.energy M Z = ∑ s, V.prob s * pairing M (H.comp s Z) (H.comp s Z) := by
  have hr (r : R) : pairing M (V.reveal r Z) (V.reveal r Z) =
      ∑ s, (if s ∈ V.retained r then 1 else 0) * pairing M (H.comp s Z) (H.comp s Z) := by
    rw [Revelation.reveal, act_sum_left, pairing_sum_left]
    simp only [pairing_sum_right]
    have hdiag (s : S) (_ : s ∈ V.retained r) :
        ∑ t ∈ V.retained r, pairing M (act (H.proj s) Z) (act (H.proj t) Z) =
          pairing M (H.comp s Z) (H.comp s Z) := by
      rw [Finset.sum_eq_single s]
      · rfl
      · intro t _ hts
        exact H.pairing_eq_zero M (Ne.symm hts) (H.act_comp s Z) (H.act_comp t Z)
      · intro h
        exact absurd ‹s ∈ V.retained r› h
    rw [Finset.sum_congr rfl hdiag]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [Revelation.energy, hr, Revelation.prob, FiniteLaw.expect, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro r _
  ring

theorem Revelation.prob_zero (V : Revelation H R) : V.prob H.zero = 1 := by
  have h : (fun r => if H.zero ∈ V.retained r then (1 : ℝ) else 0) = fun _ => 1 :=
    funext fun r => by simp [V.zero_mem r]
  rw [Revelation.prob, h, FiniteLaw.expect_const]

theorem Revelation.prob_nonneg (V : Revelation H R) (s : S) : 0 ≤ V.prob s :=
  V.law.expect_nonneg (fun r => by split <;> norm_num)

omit [Fintype ι] in
theorem SectorSystem.comp_zero [Nonempty Ω] (H : SectorSystem Ω S) (Z : Ω → ι → ℝ) :
    H.comp H.zero Z = fun _ => vmean Z := by
  rw [SectorSystem.comp, H.proj_zero, act_meanMatrix]

/-- The empty-support component of the energy is the mean energy:
`‖Z_0‖²_M = ⟨E Z, M E Z⟩`. -/
theorem SectorSystem.pairing_comp_zero [Nonempty Ω] (H : SectorSystem Ω S)
    (M : Matrix ι ι ℝ) (X Y : Ω → ι → ℝ) :
    pairing M (H.comp H.zero X) (H.comp H.zero Y) = vmean X ⬝ᵥ (M *ᵥ vmean Y) := by
  rw [H.comp_zero, H.comp_zero, pairing_const]

/-- The energy minus its mean energy is the sum over the nonzero sectors. -/
theorem Revelation.energy_sub_mean [Nonempty Ω] (V : Revelation H R) (M : Matrix ι ι ℝ)
    (Z : Ω → ι → ℝ) :
    V.energy M Z - vmean Z ⬝ᵥ (M *ᵥ vmean Z) =
      ∑ s ∈ univ.erase H.zero, V.prob s * pairing M (H.comp s Z) (H.comp s Z) := by
  rw [V.energy_eq, ← Finset.add_sum_erase _ _ (mem_univ H.zero), V.prob_zero, one_mul,
    H.pairing_comp_zero]
  ring

/-- `V_M(Z) ≥ e_M(Z) ≥ 0` for `M ⪰ 0`, where `e_M(Z) = ⟨E Z, M E Z⟩`. -/
theorem mean_le_energy [Nonempty Ω] (V : Revelation H R) {M : Matrix ι ι ℝ}
    (hM : M.PosSemidef) (Z : Ω → ι → ℝ) :
    vmean Z ⬝ᵥ (M *ᵥ vmean Z) ≤ V.energy M Z ∧ 0 ≤ vmean Z ⬝ᵥ (M *ᵥ vmean Z) := by
  refine ⟨?_, quadratic_nonneg_of_posSemidef hM _⟩
  have h := V.energy_sub_mean M Z
  have hnn : 0 ≤ ∑ s ∈ univ.erase H.zero, V.prob s * pairing M (H.comp s Z) (H.comp s Z) :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (V.prob_nonneg s) (pairing_nonneg hM _))
  linarith

/-- The per-sector bound `E_ω⟨X_s, Γ 𝒯 Y_s⟩² ≤ δ_s² ‖X_s‖²_{M_L} ‖Y_s‖²_{M_R}`. -/
theorem sector_term_sq_le {ML Γ MR : Matrix ι ι ℝ}
    (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef) {T : Matrix Ω Ω ℝ} {δ : S → ℝ}
    (hT : SectorOperator H T δ) (s : S) (X Y : Ω → ι → ℝ) :
    pairing Γ (H.comp s X) (act T (H.comp s Y)) ^ 2 ≤
      δ s ^ 2 * (pairing ML (H.comp s X) (H.comp s X) *
        pairing MR (H.comp s Y) (H.comp s Y)) := by
  have hMR : MR.PosSemidef := joint_right hG
  have hML : ML.PosSemidef := joint_left hG
  have h1 := pairing_sq_le hG (H.comp s X) (act T (H.comp s Y))
  have h2 := pairing_act_le hMR (hT.norm_le s) (H.act_comp s Y)
  have h3 := pairing_nonneg hML (H.comp s X)
  calc _ ≤ _ := h1
    _ ≤ pairing ML (H.comp s X) (H.comp s X) *
        (δ s ^ 2 * pairing MR (H.comp s Y) (H.comp s Y)) := mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring

theorem abs_le_half_sum_of_sq_le {x p a b : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ p ^ 2 * (a * b)) : |x| ≤ p * ((a + b) / 2) := by
  apply abs_le_of_sq_le_sq _ (mul_nonneg hp (by linarith))
  have hab : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc x ^ 2 ≤ p ^ 2 * (a * b) := h
    _ ≤ p ^ 2 * ((a + b) / 2) ^ 2 := mul_le_mul_of_nonneg_left hab (sq_nonneg p)
    _ = _ := by ring

/-- **Index-support lemma (a)**, abstract form (`lem:record:common-mean`(a)):
`|𝖩 - ⟨E X, Γ E Y⟩| ≤ ½[(V_L - e_L) + (V_R - e_R)]`. -/
theorem common_mean [Nonempty Ω] (V : Revelation H R) {δ : S → ℝ} (hδ0 : ∀ s, 0 ≤ δ s)
    (hδ : ∀ s, δ s ≤ V.prob s) {T : Matrix Ω Ω ℝ} (hT : SectorOperator H T δ)
    {ML Γ MR : Matrix ι ι ℝ} (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef)
    (X Y : Ω → ι → ℝ) :
    |pairing Γ X (act T Y) - vmean X ⬝ᵥ (Γ *ᵥ vmean Y)| ≤
      (1 / 2) * ((V.energy ML X - vmean X ⬝ᵥ (ML *ᵥ vmean X)) +
        (V.energy MR Y - vmean Y ⬝ᵥ (MR *ᵥ vmean Y))) := by
  have hML : ML.PosSemidef := joint_left hG
  have hMR : MR.PosSemidef := joint_right hG
  have hzero : pairing Γ (H.comp H.zero X) (act T (H.comp H.zero Y)) =
      vmean X ⬝ᵥ (Γ *ᵥ vmean Y) := by
    have hid : act T (H.comp H.zero Y) = H.comp H.zero Y := by
      apply ext_col
      intro a
      rw [col_act]
      exact hT.id_zero _ (H.col_mem (H.act_comp H.zero Y) a)
    rw [hid, H.pairing_comp_zero]
  rw [H.pairing_decomp Γ T hT.maps X Y, ← Finset.add_sum_erase _ _ (mem_univ H.zero), hzero,
    add_sub_cancel_left, V.energy_sub_mean, V.energy_sub_mean, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s _
  have hb := abs_le_half_sum_of_sq_le (V.prob_nonneg s) (pairing_nonneg hML (H.comp s X))
    (pairing_nonneg hMR (H.comp s Y))
    ((sector_term_sq_le hG hT s X Y).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hδ0 s) (hδ s) 2)
      (mul_nonneg (pairing_nonneg hML _) (pairing_nonneg hMR _))))
  calc _ ≤ _ := hb
    _ = _ := by ring

/-- **Index-support lemma (b)**, abstract form (`lem:record:common-mean`(b)):
`|𝖩| ≤ V_L^{1/2} V_R^{1/2}`. -/
theorem form_le_energies [Nonempty Ω] (V : Revelation H R) {δ : S → ℝ} (hδ0 : ∀ s, 0 ≤ δ s)
    (hδ : ∀ s, δ s ≤ V.prob s) {T : Matrix Ω Ω ℝ} (hT : SectorOperator H T δ)
    {ML Γ MR : Matrix ι ι ℝ} (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef)
    (X Y : Ω → ι → ℝ) :
    |pairing Γ X (act T Y)| ≤ Real.sqrt (V.energy ML X) * Real.sqrt (V.energy MR Y) := by
  have hML : ML.PosSemidef := joint_left hG
  have hMR : MR.PosSemidef := joint_right hG
  set x : S → ℝ := fun s => pairing Γ (H.comp s X) (act T (H.comp s Y)) with hx
  set a : S → ℝ := fun s => pairing ML (H.comp s X) (H.comp s X) with ha
  set b : S → ℝ := fun s => pairing MR (H.comp s Y) (H.comp s Y) with hb
  have ha0 (s : S) : 0 ≤ a s := pairing_nonneg hML _
  have hb0 (s : S) : 0 ≤ b s := pairing_nonneg hMR _
  have hp0 (s : S) : 0 ≤ V.prob s := V.prob_nonneg s
  have hxs (s : S) : x s ^ 2 ≤ V.prob s ^ 2 * (a s * b s) :=
    (sector_term_sq_le hG hT s X Y).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hδ0 s) (hδ s) 2) (mul_nonneg (ha0 s) (hb0 s)))
  have hJ : pairing Γ X (act T Y) = ∑ s, x s := H.pairing_decomp Γ T hT.maps X Y
  have hVL : V.energy ML X = ∑ s, V.prob s * a s := V.energy_eq ML X
  have hVR : V.energy MR Y = ∑ s, V.prob s * b s := V.energy_eq MR Y
  -- every term is a nonnegative quadratic in `t`, hence so is the sum
  have hterm (s : S) (t : ℝ) : 0 ≤ V.prob s * a s * (t * t) + 2 * x s * t + V.prob s * b s := by
    rcases (mul_nonneg (hp0 s) (ha0 s)).lt_or_eq with hpos | hz
    · have h' : 0 ≤ (V.prob s * a s) *
          (V.prob s * a s * (t * t) + 2 * x s * t + V.prob s * b s) := by
        nlinarith [sq_nonneg (V.prob s * a s * t + x s), hxs s]
      by_contra hneg
      have hneg' := lt_of_not_ge hneg
      nlinarith [mul_neg_of_pos_of_neg hpos hneg']
    · have hx0 : x s = 0 := by
        have : x s ^ 2 ≤ 0 := by
          calc x s ^ 2 ≤ V.prob s ^ 2 * (a s * b s) := hxs s
            _ = (V.prob s * a s) * (V.prob s * b s) := by ring
            _ = 0 := by rw [← hz, zero_mul]
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
      rw [hx0, ← hz]
      nlinarith [mul_nonneg (hp0 s) (hb0 s)]
  have hquad (t : ℝ) : 0 ≤ V.energy ML X * (t * t) + (2 * pairing Γ X (act T Y)) * t +
      V.energy MR Y := by
    rw [hVL, hVR, hJ, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro s _
    have := hterm s t
    linarith
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  have hVL0 : 0 ≤ V.energy ML X := by
    rw [hVL]; exact Finset.sum_nonneg (fun s _ => mul_nonneg (hp0 s) (ha0 s))
  have hsq : pairing Γ X (act T Y) ^ 2 ≤ V.energy ML X * V.energy MR Y := by nlinarith
  have hs := Real.abs_le_sqrt hsq
  rwa [Real.sqrt_mul hVL0] at hs

end Abstract

end Sarkozy.IndexSupport
