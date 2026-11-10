module

public import Sarkozy.IndexSupport.Filtration

/-!
# Sector operators: tensor products, adjoints, signed combinations; product revelations

Closure properties of the hypothesis on the index operator `𝒯` of
`lem:record:common-mean` (`SectorOperator`: preserves every sector, identity on the
constants, norm at most `δ_s` on `H_s`):

* `SectorOperator.pi`: a tensor product `⊗_e A_e` of sector operators is a sector
  operator for the product sectors, with weights `∏_e δ_{e,s_e}` (`lem:sector`(a); the
  tensoring step of `cor:index-support-frame`(i));
* `SectorOperator.transpose`: the adjoint of a sector operator is a sector operator with
  the same weights ("and likewise `𝒯^*`" in `cor:index-support-frame`(i));
* `SectorOperator.signed`: if `δ_0 = 1`, then `2P - T` is a sector operator with the same
  weights, where `P` is the projection onto the constants: it is the identity on the
  constants and equals `-T` on every other sector (proof of
  `cor:index-support-frame`(i));
* `SectorOperator.chain`: per-coordinate operators that preserve the exact-depth spaces
  `ran Π_{j,l}` with norm at most `δ_{j,l}` and fix the constants give a sector operator
  for the product of chains, with the weights `δ_l = ∏_j δ_{j,l_j}`.

`Revelation.pi` is the product of independent revelations; `Revelation.pi_prob` gives
the product formula `Pr(s retained) = ∏_e Pr(s_e retained)`.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

section General

variable {Ω S : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype S] [DecidableEq S]
  {H : SectorSystem Ω S} {T : Matrix Ω Ω ℝ} {δ : S → ℝ}

theorem SectorOperator.toRangeBound (hT : SectorOperator H T δ) (s : S) :
    RangeBound (H.proj s) T (δ s) :=
  RangeBound.of_vec (H.transpose_proj s) (H.proj_mul_self s) (hT.maps s) (hT.norm_le s)

theorem SectorOperator.mul_proj_zero (hT : SectorOperator H T δ) :
    T * H.proj H.zero = H.proj H.zero :=
  mul_eq_of_mulVec_eq (H.proj_mul_self _) hT.id_zero

theorem SectorOperator.of_rangeBound (h : ∀ s, RangeBound (H.proj s) T (δ s))
    (h0 : T * H.proj H.zero = H.proj H.zero) : SectorOperator H T δ :=
  ⟨fun s _ hf => (h s).mem hf, fun _ hf => mulVec_eq_of_mul_eq h0 hf,
    fun s _ hf => (h s).norm_le (H.transpose_proj s) hf⟩

/-- The adjoint of a sector operator is a sector operator with the same weights. -/
theorem SectorOperator.transpose (hT : SectorOperator H T δ) : SectorOperator H Tᵀ δ :=
  SectorOperator.of_rangeBound (H.rangeBound_transpose (fun s => hT.toRangeBound s))
    (H.mul_proj_zero_transpose (fun t => (hT.toRangeBound t).maps) hT.mul_proj_zero)

/-- The signed combination `2P - T`, with `P` the projection onto the constants: the
identity on the constants and `-T` on every other sector. -/
theorem SectorOperator.signed (hT : SectorOperator H T δ) (hδ0 : δ H.zero = 1) :
    SectorOperator H ((2 : ℝ) • H.proj H.zero - T) δ := by
  have hkill (s : S) (hs : s ≠ H.zero) {f : Ω → ℝ} (hf : H.proj s *ᵥ f = f) :
      H.proj H.zero *ᵥ f = 0 := by
    rw [← hf, Matrix.mulVec_mulVec, H.proj_mul_ne (Ne.symm hs), Matrix.zero_mulVec]
  have hval (s : S) {f : Ω → ℝ} (hf : H.proj s *ᵥ f = f) :
      ((2 : ℝ) • H.proj H.zero - T) *ᵥ f = if s = H.zero then f else -(T *ᵥ f) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec]
    split_ifs with hs
    · subst hs
      rw [hf, hT.id_zero f hf]
      ext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [hkill s hs hf, smul_zero, zero_sub]
  refine ⟨?_, ?_, ?_⟩
  · intro s f hf
    rw [hval s hf]
    split_ifs
    · exact hf
    · rw [Matrix.mulVec_neg, hT.maps s f hf]
  · intro f hf
    rw [hval H.zero hf, ite_eq_left rfl]
  · intro s f hf
    rw [hval s hf]
    split_ifs with hs
    · subst hs
      rw [hδ0, one_pow, one_mul]
    · rw [neg_dotProduct, dotProduct_neg, neg_neg]
      exact hT.norm_le s f hf

end General

section Product

variable {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*} [∀ e, Fintype (Ω e)]
  [∀ e, DecidableEq (Ω e)] {S : E → Type*} [∀ e, Fintype (S e)] [∀ e, DecidableEq (S e)]

/-- A tensor product of sector operators is a sector operator for the product sectors,
with the product weights. -/
theorem SectorOperator.pi {H : ∀ e, SectorSystem (Ω e) (S e)} {A : ∀ e, Matrix (Ω e) (Ω e) ℝ}
    {δ : ∀ e, S e → ℝ} (hA : ∀ e, SectorOperator (H e) (A e) (δ e)) :
    SectorOperator (SectorSystem.pi H) (piKron A) (fun s => ∏ e, δ e (s e)) :=
  SectorOperator.of_rangeBound
    (fun s => RangeBound.piKron (fun e => (H e).transpose_proj (s e))
      (fun e => (hA e).toRangeBound (s e)))
    (piKron_mul_eq_of (fun e => (hA e).mul_proj_zero))

/-- Product of independent revelations. -/
noncomputable def Revelation.pi {H : ∀ e, SectorSystem (Ω e) (S e)} {R : E → Type*}
    [∀ e, Fintype (R e)] (V : ∀ e, Revelation (H e) (R e)) :
    Revelation (SectorSystem.pi H) (∀ e, R e) where
  law := FiniteLaw.pi (fun e => (V e).law)
  retained r := univ.filter (fun s => ∀ e, s e ∈ (V e).retained (r e))
  zero_mem r := by
    simp only [mem_filter, mem_univ, true_and]
    intro e
    exact (V e).zero_mem (r e)

theorem Revelation.pi_prob {H : ∀ e, SectorSystem (Ω e) (S e)} {R : E → Type*}
    [∀ e, Fintype (R e)] (V : ∀ e, Revelation (H e) (R e)) (s : ∀ e, S e) :
    (Revelation.pi V).prob s = ∏ e, (V e).prob (s e) := by
  unfold Revelation.prob
  have he : (fun r : ∀ e, R e => if s ∈ (Revelation.pi V).retained r then (1 : ℝ) else 0) =
      fun r => ∏ e, (if s e ∈ (V e).retained (r e) then (1 : ℝ) else 0) := by
    funext r
    rw [prod_indicator_forall]
    simp only [Revelation.pi, mem_filter, mem_univ, true_and]
  rw [he]
  change (FiniteLaw.pi (fun e => (V e).law)).expect _ = _
  exact FiniteLaw.expect_pi_product (fun e => (V e).law)
    (fun e u => if s e ∈ (V e).retained u then 1 else 0)

theorem Revelation.pi_sum_proj {H : ∀ e, SectorSystem (Ω e) (S e)} {R : E → Type*}
    [∀ e, Fintype (R e)] (V : ∀ e, Revelation (H e) (R e)) (r : ∀ e, R e) :
    ∑ s ∈ (Revelation.pi V).retained r, (SectorSystem.pi H).proj s =
      piKron (fun e => ∑ u ∈ (V e).retained (r e), (H e).proj u) := by
  have hset : (Revelation.pi V).retained r = Fintype.piFinset (fun e => (V e).retained (r e)) := by
    ext s
    simp only [Revelation.pi, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rw [hset]
  simp only [SectorSystem.pi_proj]
  exact piKron_sum_piFinset (fun e => (V e).retained (r e)) (fun e u => (H e).proj u)

end Product

section Chains

variable {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*} [∀ j, Fintype (Ω j)]
  [∀ j, DecidableEq (Ω j)]

theorem depthRevelation_sum_proj (C : ∀ j, Chain (Ω j)) (t : ∀ j, Tails (C j).depth)
    (J : ∀ j, Fin ((C j).depth + 1)) :
    ∑ l ∈ (depthRevelation C t).retained J, (productSectors C).proj l =
      piKron (fun j => (C j).cond (J j)) := by
  have hset : univ.filter (fun l : ∀ j, Fin ((C j).depth + 1) => ∀ j, l j ≤ J j) =
      Fintype.piFinset (fun j => univ.filter (fun u => u ≤ J j)) := by
    ext l
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  change ∑ l ∈ univ.filter (fun l : ∀ j, Fin ((C j).depth + 1) => ∀ j, l j ≤ J j),
    (productSectors C).proj l = _
  rw [hset]
  simp only [productSectors_proj]
  rw [piKron_sum_piFinset (fun j => univ.filter (fun u => u ≤ J j))
    (fun j u => (C j).diff u)]
  congr 1
  funext j
  exact (C j).sum_sectors_le (J j)

/-- Per-coordinate operators that map every exact-depth space `ran Π_{j,l}` into itself with
norm at most `δ_{j,l}` and fix the constants give, by tensoring, a sector operator for the
exact-depth sectors `H_l` with the weights `δ_l = ∏_j δ_{j,l_j}`. -/
theorem SectorOperator.chain (C : ∀ j, Chain (Ω j)) (t : ∀ j, Tails (C j).depth)
    {A : ∀ j, Matrix (Ω j) (Ω j) ℝ}
    (hA : ∀ j (l : Fin ((C j).depth + 1)), RangeBound ((C j).diff l) (A j) ((t j).tail l))
    (hA0 : ∀ j, A j * (C j).cond 0 = (C j).cond 0) :
    SectorOperator (productSectors C) (piKron A) (sectorWeight C t) := by
  have hsec (j : K) : SectorOperator (C j).sectors (A j) (fun l => (t j).tail l) := by
    apply SectorOperator.of_rangeBound (fun l => hA j l)
    change A j * (C j).diff 0 = (C j).diff 0
    rw [Chain.diff, ite_eq_left rfl]
    exact hA0 j
  exact SectorOperator.pi hsec

end Chains

end Sarkozy.IndexSupport
