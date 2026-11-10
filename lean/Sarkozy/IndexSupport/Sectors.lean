module

public import Sarkozy.IndexSupport.Kronecker

/-!
# Sector decompositions and sector-bounded operators

A *sector system* on a finite set `Ω` is an orthogonal decomposition of the real
functions on `Ω` (with the uniform inner product, equivalently the Euclidean dot
product) into finitely many sectors: the orthogonal projections onto the sectors are
symmetric, mutually orthogonal idempotent matrices summing to the identity, and a
distinguished zero sector is the line of constants. This is the abstract form of the
sector decompositions `L²(Ω) = ⊕_l H_l` used in `lem:record:common-mean` and
`lem:sector` of the paper.

`RangeBound P A c` says that `A` maps the range of the projection `P` into itself and
has operator norm at most `c` there. We prove:

* the equivalence with the vector form (`RangeBound.of_vec`, `RangeBound.mem`,
  `RangeBound.norm_le`);
* products of sector systems (`SectorSystem.pi`), the tensor product of sectors;
* tensorization of range bounds (`RangeBound.piKron`): on a product sector the norm
  of `⊗_e A_e` is at most the product of the factor norms (the bound
  `‖T_0 ⊗ ⊗_j T_j^∘‖ ≤ ∏ ‖T_j^∘‖` of `lem:sector`(a), and the tensoring step in the
  proof of `cor:index-support-frame`(i));
* adjoints (`SectorSystem.rangeBound_transpose`): an operator preserving every sector
  commutes with the sector projections, and its adjoint obeys the same norm bounds
  (the "likewise `𝒯^*`" of `cor:index-support-frame`(i)).

Operator norms are expressed through the Loewner inequality
`P Aᵀ A P ⪯ c² P`; the tensor bound then follows from Loewner monotonicity of
Kronecker products (`piKron_sub_posSemidef`).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

section Helpers

variable {Ω : Type*} [Fintype Ω]

theorem posSemidef_of_quadratic {M : Matrix Ω Ω ℝ} (hsym : Mᵀ = M)
    (h : ∀ x, 0 ≤ x ⬝ᵥ (M *ᵥ x)) : M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hsym]
  · intro x
    simpa only [star_trivial] using h x

theorem quadratic_nonneg_of_posSemidef {M : Matrix Ω Ω ℝ} (hM : M.PosSemidef) (x : Ω → ℝ) :
    0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  simpa only [star_trivial] using hM.dotProduct_mulVec_nonneg x

omit [Fintype Ω] in
theorem transpose_eq_of_posSemidef {M : Matrix Ω Ω ℝ} (hM : M.PosSemidef) : Mᵀ = M := by
  have h := hM.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- Moving a symmetric matrix across the dot product. -/
theorem dotProduct_mulVec_symm {P : Matrix Ω Ω ℝ} (hP : Pᵀ = P) (f g : Ω → ℝ) :
    f ⬝ᵥ (P *ᵥ g) = (P *ᵥ f) ⬝ᵥ g := by
  rw [← Matrix.dotProduct_transpose_mulVec, hP, dotProduct_comm]

theorem dotProduct_mulVec_self (A : Matrix Ω Ω ℝ) (f : Ω → ℝ) :
    (A *ᵥ f) ⬝ᵥ (A *ᵥ f) = f ⬝ᵥ (Aᵀ *ᵥ (A *ᵥ f)) := by
  rw [Matrix.dotProduct_transpose_mulVec]

theorem dotProduct_self_nonneg (f : Ω → ℝ) : 0 ≤ f ⬝ᵥ f :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (f i))

/-- Cauchy--Schwarz for the dot product, in squared form. -/
theorem dotProduct_sq_le (f g : Ω → ℝ) : (f ⬝ᵥ g) ^ 2 ≤ (f ⬝ᵥ f) * (g ⬝ᵥ g) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simpa only [dotProduct, sq] using h

end Helpers

section RangeBound

variable {Ω : Type*} [Fintype Ω]

/-- `A` maps the range of `P` into itself and has norm at most `c` on it, in matrix
form: `A P = P A P` and `P Aᵀ A P ⪯ c² P`. For an orthogonal projection `P` this is
equivalent to the vector form (`RangeBound.of_vec`, `RangeBound.mem`,
`RangeBound.norm_le`). -/
structure RangeBound (P A : Matrix Ω Ω ℝ) (c : ℝ) : Prop where
  maps : A * P = P * A * P
  norm : (c ^ 2 • P - P * Aᵀ * A * P).PosSemidef

theorem RangeBound.mem {P A : Matrix Ω Ω ℝ} {c : ℝ} (h : RangeBound P A c) {f : Ω → ℝ}
    (hf : P *ᵥ f = f) : P *ᵥ (A *ᵥ f) = A *ᵥ f := by
  have h' := congrArg (· *ᵥ f) h.maps
  simp only [← Matrix.mulVec_mulVec, hf] at h'
  exact h'.symm

theorem RangeBound.norm_le {P A : Matrix Ω Ω ℝ} {c : ℝ} (h : RangeBound P A c)
    (hP : Pᵀ = P) {f : Ω → ℝ} (hf : P *ᵥ f = f) :
    (A *ᵥ f) ⬝ᵥ (A *ᵥ f) ≤ c ^ 2 * (f ⬝ᵥ f) := by
  have hq := quadratic_nonneg_of_posSemidef h.norm f
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, hf,
    smul_eq_mul] at hq
  simp only [← Matrix.mulVec_mulVec, hf] at hq
  rw [dotProduct_mulVec_symm hP, hf, ← dotProduct_mulVec_self] at hq
  linarith

theorem RangeBound.of_vec {P A : Matrix Ω Ω ℝ} {c : ℝ} (hP : Pᵀ = P) (hPP : P * P = P)
    (hmaps : ∀ f, P *ᵥ f = f → P *ᵥ (A *ᵥ f) = A *ᵥ f)
    (hnorm : ∀ f, P *ᵥ f = f → (A *ᵥ f) ⬝ᵥ (A *ᵥ f) ≤ c ^ 2 * (f ⬝ᵥ f)) :
    RangeBound P A c := by
  have hfix (g : Ω → ℝ) : P *ᵥ (P *ᵥ g) = P *ᵥ g := by rw [Matrix.mulVec_mulVec, hPP]
  refine ⟨?_, ?_⟩
  · rw [Matrix.ext_iff_mulVec]
    intro g
    simp only [← Matrix.mulVec_mulVec]
    exact (hmaps _ (hfix g)).symm
  · apply posSemidef_of_quadratic
    · simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
        Matrix.transpose_transpose, hP]
      noncomm_ring
    · intro g
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
        smul_eq_mul]
      simp only [← Matrix.mulVec_mulVec]
      rw [dotProduct_mulVec_symm hP g (Aᵀ *ᵥ _), ← dotProduct_mulVec_self]
      have hgg : g ⬝ᵥ (P *ᵥ g) = (P *ᵥ g) ⬝ᵥ (P *ᵥ g) := by
        rw [dotProduct_mulVec_symm hP (P *ᵥ g) g, hfix, dotProduct_comm]
      rw [hgg]
      linarith [hnorm _ (hfix g)]

/-- On the range of `P`, an operator with `A P = P` is the identity. -/
theorem mulVec_eq_of_mul_eq {P A : Matrix Ω Ω ℝ} (h : A * P = P) {f : Ω → ℝ}
    (hf : P *ᵥ f = f) : A *ᵥ f = f := by
  rw [← hf, Matrix.mulVec_mulVec, h]

theorem mul_eq_of_mulVec_eq {P A : Matrix Ω Ω ℝ} (hPP : P * P = P)
    (h : ∀ f, P *ᵥ f = f → A *ᵥ f = f) : A * P = P := by
  rw [Matrix.ext_iff_mulVec]
  intro g
  rw [← Matrix.mulVec_mulVec]
  exact h _ (by rw [Matrix.mulVec_mulVec, hPP])

end RangeBound

/-- An orthogonal decomposition of the real functions on a finite set `Ω` into sectors
indexed by `S`, with the zero sector equal to the constants. -/
structure SectorSystem (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (S : Type*) [Fintype S] [DecidableEq S] where
  /-- the orthogonal projection onto each sector -/
  proj : S → Matrix Ω Ω ℝ
  /-- the sector of constants -/
  zero : S
  transpose_proj : ∀ s, (proj s)ᵀ = proj s
  proj_mul_proj : ∀ s t, proj s * proj t = if s = t then proj s else 0
  sum_proj : ∑ s, proj s = 1
  proj_zero : proj zero = meanMatrix Ω

namespace SectorSystem

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {S : Type*} [Fintype S] [DecidableEq S]

theorem proj_mul_self (H : SectorSystem Ω S) (s : S) : H.proj s * H.proj s = H.proj s := by
  rw [H.proj_mul_proj, ite_eq_left rfl]

theorem proj_mul_ne (H : SectorSystem Ω S) {s t : S} (hst : s ≠ t) :
    H.proj s * H.proj t = 0 := by
  rw [H.proj_mul_proj, ite_eq_right hst]

theorem proj_proj_mulVec (H : SectorSystem Ω S) (s : S) (f : Ω → ℝ) :
    H.proj s *ᵥ (H.proj s *ᵥ f) = H.proj s *ᵥ f := by
  rw [Matrix.mulVec_mulVec, H.proj_mul_self]

theorem sum_proj_mulVec (H : SectorSystem Ω S) (f : Ω → ℝ) :
    ∑ s, H.proj s *ᵥ f = f := by
  rw [← Matrix.sum_mulVec, H.sum_proj, Matrix.one_mulVec]

/-- Functions in different sectors are orthogonal. -/
theorem dotProduct_eq_zero (H : SectorSystem Ω S) {s t : S} (hst : s ≠ t) {f g : Ω → ℝ}
    (hf : H.proj s *ᵥ f = f) (hg : H.proj t *ᵥ g = g) : f ⬝ᵥ g = 0 := by
  rw [← hf, ← hg, ← dotProduct_mulVec_symm (H.transpose_proj s), Matrix.mulVec_mulVec,
    H.proj_mul_ne hst, Matrix.zero_mulVec, dotProduct_zero]

/-- An operator mapping every sector into itself commutes with every sector projection. -/
theorem proj_mul_comm (H : SectorSystem Ω S) {A : Matrix Ω Ω ℝ}
    (hA : ∀ t, A * H.proj t = H.proj t * A * H.proj t) (s : S) :
    H.proj s * A = A * H.proj s := by
  calc H.proj s * A = H.proj s * A * ∑ t, H.proj t := by rw [H.sum_proj, Matrix.mul_one]
    _ = ∑ t, (H.proj s * H.proj t) * A * H.proj t := by
        rw [Matrix.mul_sum]
        apply sum_congr rfl
        intro t _
        rw [Matrix.mul_assoc, hA t, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          Matrix.mul_assoc (H.proj s)]
    _ = H.proj s * A * H.proj s := by
        rw [Finset.sum_eq_single s]
        · rw [H.proj_mul_self]
        · intro t _ hts
          rw [H.proj_mul_ne (Ne.symm hts), Matrix.zero_mul, Matrix.zero_mul]
        · intro h
          exact absurd (mem_univ s) h
    _ = A * H.proj s := (hA s).symm

/-- The adjoint of an operator that maps every sector into itself, with norm at most
`c s` on sector `s`, has the same property. -/
theorem rangeBound_transpose (H : SectorSystem Ω S) {A : Matrix Ω Ω ℝ} {c : S → ℝ}
    (hA : ∀ s, RangeBound (H.proj s) A (c s)) (s : S) :
    RangeBound (H.proj s) Aᵀ (c s) := by
  have hcomm := H.proj_mul_comm (fun t => (hA t).maps)
  have hcommT : ∀ t, H.proj t * Aᵀ = Aᵀ * H.proj t := by
    intro t
    have h := congrArg Matrix.transpose (hcomm t)
    simpa only [Matrix.transpose_mul, H.transpose_proj] using h.symm
  have hP := H.transpose_proj s
  apply RangeBound.of_vec hP (H.proj_mul_self s)
  · intro f hf
    rw [Matrix.mulVec_mulVec, hcommT s, ← Matrix.mulVec_mulVec, hf]
  · intro u hu
    set h := Aᵀ *ᵥ u with hh
    have hPh : H.proj s *ᵥ h = h := by
      rw [hh, Matrix.mulVec_mulVec, hcommT s, ← Matrix.mulVec_mulVec, hu]
    have hnormA := (hA s).norm_le hP hPh
    have hkey : h ⬝ᵥ h = (A *ᵥ h) ⬝ᵥ u := by
      rw [hh, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    have hcs := dotProduct_sq_le (A *ᵥ h) u
    rw [← hkey] at hcs
    have hh0 := dotProduct_self_nonneg h
    have hu0 := dotProduct_self_nonneg u
    have hAh0 := dotProduct_self_nonneg (A *ᵥ h)
    rcases hh0.lt_or_eq with hpos | hzero
    · have h2 : (h ⬝ᵥ h) ^ 2 ≤ c s ^ 2 * (h ⬝ᵥ h) * (u ⬝ᵥ u) := by
        calc (h ⬝ᵥ h) ^ 2 ≤ ((A *ᵥ h) ⬝ᵥ (A *ᵥ h)) * (u ⬝ᵥ u) := hcs
          _ ≤ (c s ^ 2 * (h ⬝ᵥ h)) * (u ⬝ᵥ u) := mul_le_mul_of_nonneg_right hnormA hu0
      have h3 : (h ⬝ᵥ h) * (h ⬝ᵥ h) ≤ (h ⬝ᵥ h) * (c s ^ 2 * (u ⬝ᵥ u)) := by nlinarith
      exact le_of_mul_le_mul_left h3 hpos
    · rw [← hzero]
      exact mul_nonneg (sq_nonneg _) hu0

theorem mul_proj_zero_transpose (H : SectorSystem Ω S) {A : Matrix Ω Ω ℝ}
    (hA : ∀ t, A * H.proj t = H.proj t * A * H.proj t) (h0 : A * H.proj H.zero = H.proj H.zero) :
    Aᵀ * H.proj H.zero = H.proj H.zero := by
  have hc := H.proj_mul_comm hA H.zero
  have h := congrArg Matrix.transpose (hc.trans h0)
  simpa only [Matrix.transpose_mul, H.transpose_proj] using h

/-- The product of sector systems: the sectors of `∀ e, Ω e` are the tensor products of
sectors, `H_s = ⊗_e H_{e, s_e}`. -/
def pi {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*} [∀ e, Fintype (Ω e)]
    [∀ e, DecidableEq (Ω e)] {S : E → Type*} [∀ e, Fintype (S e)] [∀ e, DecidableEq (S e)]
    (H : ∀ e, SectorSystem (Ω e) (S e)) : SectorSystem (∀ e, Ω e) (∀ e, S e) where
  proj s := piKron (fun e => (H e).proj (s e))
  zero := fun e => (H e).zero
  transpose_proj s := by
    rw [piKron_transpose]
    simp only [(H _).transpose_proj]
  proj_mul_proj s t := by
    rw [piKron_mul]
    by_cases hst : s = t
    · subst hst
      rw [ite_eq_left rfl]
      congr 1
      funext e
      exact (H e).proj_mul_self (s e)
    · obtain ⟨e, he⟩ : ∃ e, s e ≠ t e := by
        by_contra h'
        exact hst (funext fun e => not_not.mp (fun hne => h' ⟨e, hne⟩))
      rw [ite_eq_right hst]
      exact piKron_eq_zero e (by rw [(H e).proj_mul_ne he])
  sum_proj := by
    rw [piKron_sum]
    simp only [(H _).sum_proj]
    exact piKron_one
  proj_zero := by
    simp only [(H _).proj_zero]
    exact piKron_meanMatrix

theorem pi_proj {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*} [∀ e, Fintype (Ω e)]
    [∀ e, DecidableEq (Ω e)] {S : E → Type*} [∀ e, Fintype (S e)] [∀ e, DecidableEq (S e)]
    (H : ∀ e, SectorSystem (Ω e) (S e)) (s : ∀ e, S e) :
    (pi H).proj s = piKron (fun e => (H e).proj (s e)) := rfl

end SectorSystem

section Tensor

variable {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*} [∀ e, Fintype (Ω e)]

/-- Tensorization of range bounds: if each `A e` maps the range of `P e` into itself with
norm at most `c e`, then `⊗_e A_e` maps the range of `⊗_e P_e` into itself with norm at
most `∏_e c_e`. -/
theorem RangeBound.piKron {P A : ∀ e, Matrix (Ω e) (Ω e) ℝ} {c : E → ℝ}
    (hP : ∀ e, (P e)ᵀ = P e) (h : ∀ e, RangeBound (P e) (A e) (c e)) :
    RangeBound (piKron P) (piKron A) (∏ e, c e) := by
  refine ⟨?_, ?_⟩
  · rw [piKron_mul, piKron_mul, piKron_mul]
    congr 1
    funext e
    exact (h e).maps
  · have hL : (∏ e, c e) ^ 2 • IndexSupport.piKron P =
        IndexSupport.piKron (fun e => c e ^ 2 • P e) := by
      rw [piKron_smul, Finset.prod_pow]
    have hR : IndexSupport.piKron P * (IndexSupport.piKron A)ᵀ * IndexSupport.piKron A *
        IndexSupport.piKron P =
        IndexSupport.piKron (fun e => P e * (A e)ᵀ * A e * P e) := by
      rw [piKron_transpose, piKron_mul, piKron_mul, piKron_mul]
    rw [hL, hR]
    apply piKron_sub_posSemidef
    · intro e
      have h0 := Matrix.posSemidef_conjTranspose_mul_self (A e * P e)
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hP e] at h0
      simpa only [Matrix.mul_assoc] using h0
    · intro e
      exact (h e).norm

/-- If each `A e` is the identity on the range of `P e` (`A_e P_e = P_e`), then so is
`⊗_e A_e` on the range of `⊗_e P_e`. -/
theorem piKron_mul_eq_of {P A : ∀ e, Matrix (Ω e) (Ω e) ℝ} (h : ∀ e, A e * P e = P e) :
    IndexSupport.piKron A * IndexSupport.piKron P = IndexSupport.piKron P := by
  rw [piKron_mul]
  congr 1
  funext e
  exact h e

end Tensor

end Sarkozy.IndexSupport
