module

public import Sarkozy.Comparison.ConcreteFrame
public import Sarkozy.Functional.SignedIndex

@[expose] public section

/-!
# The signed index form of the frame and `eq:record:expansion`

`Sarkozy.Comparison.signedIndexForm` (`Comparison/ConcreteFrame.lean`) is the signed index
form `J_ν = E_ω Q_ν(X_ω, (𝒯Y)_ω)` of `def:hyb:coupled`(d), written with WP-S's matrices:
`productHalf` for the half-functions, `act` for the operators and
`signedIndexOp Tc = ⊗_e (2·meanMatrix − ⊗_j Tc e j)` for `𝒯`. `Sarkozy.Functional.signedForm`
(`Functional/SignedIndex.lean`) is the same object written with kernels, for an arbitrary
bilinear form; there `eq:record:expansion` is proved:
`J = ∑_{𝒮 ⊆ E} (−1)^{|𝒮|} 2^{k−|𝒮|} I_𝒮` and `I_∅ = Q(X̄, X̄)`.

This module proves that the two agree when the same inputs sit at both ends of the queries
(`φ = ψ`; the paper's inputs `g^{I_b,M₀,s}`), for every coupled index, every family of
per-atom laws `ν` and every `F`:

* `cutBilin κ`: the cut form `(X, Y) ↦ reservedCut.form κ X Y` as a bilinear form;
* `productHalf_eq_halfFunction`, `act_signedIndexOp`, `act_mixedOp`: the two encodings of
  the half-functions, of `𝒯` and of `⊗_{e ∈ 𝒮} T_e ⊗_{e ∉ 𝒮} P_e` coincide;
* `signedIndexForm_eq_signedForm`: the bridge;
* `signedIndexForm_expansion`: `eq:record:expansion` for `signedIndexForm`;
* `coupledForm_eq_operatorForm`: the coupled forms `I_𝒮` in WP-S's operator form;
* `signedIndexForm_sub_eq`: under the mean identity (`lem:twointerval`(iii) in the
  application), `J_ν − 2^k Y_ν = ∑_{𝒮 ≠ ∅} (−1)^{|𝒮|} 2^{k−|𝒮|} I_𝒮`, in the form of the
  hypothesis `hexp` of `Sarkozy.Comparison.wrap_summation` (`Comparison/WrapAssembly.lean`),
  before its further split of `I_𝒮` by the wrapping queries.
-/

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.PaperFrame

open Sarkozy.IndexSupport Sarkozy.Comparison

/-! ### The cut form as a bilinear form -/

section CutBilin

variable {V : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V) {X : Type*}

/-- The cut form `(F, G) ↦ c.form κ F G = κ(z ↦ F(z|₊) G(z|₋))` is bilinear. -/
noncomputable def cutBilin (κ : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    LinearMap.BilinForm ℝ ((c.Half → X) → ℝ) :=
  LinearMap.mk₂ ℝ (fun F G => c.form κ F G)
    (fun F₁ F₂ G => by
      unfold ReflectionCut.form
      rw [← map_add]
      congr 1
      funext z
      simp only [Pi.add_apply, add_mul])
    (fun a F G => by
      unfold ReflectionCut.form
      rw [smul_eq_mul, ← smul_eq_mul, ← map_smul]
      congr 1
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc])
    (fun F G₁ G₂ => by
      unfold ReflectionCut.form
      rw [← map_add]
      congr 1
      funext z
      simp only [Pi.add_apply, mul_add])
    (fun a F G => by
      unfold ReflectionCut.form
      rw [smul_eq_mul, ← smul_eq_mul, ← map_smul]
      congr 1
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)

@[simp] theorem cutBilin_apply (κ : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (F G : (c.Half → X) → ℝ) :
    cutBilin c κ F G = c.form κ F G := rfl

end CutBilin

/-! ### The two encodings of half-functions and operators -/

section Encodings

variable {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*} [∀ e, Fintype (Ω e)]
  {W H : Type*} [Fintype W] [DecidableEq W]

omit [DecidableEq E] [∀ e, Fintype (Ω e)] in
/-- WP-S's `productHalf` is fork A's `halfFunction` (`def:hyb:coupled`(b)). -/
theorem productHalf_eq_halfFunction (u : E → W) (g : ∀ e, Ω e → H → ℝ) (F : H → ℝ) :
    productHalf u g F = Sarkozy.Functional.halfFunction u g F := by
  funext ω x
  simp only [productHalf, Sarkozy.Functional.halfFunction, compl_eq_univ_sdiff]

/-- `meanMatrix` is the averaging kernel `uniformKernel` (`P_e`). -/
theorem meanMatrix_eq_uniformKernel (Ω' : Type*) [Fintype Ω'] :
    meanMatrix Ω' = Sarkozy.Functional.uniformKernel Ω' := rfl

omit [Fintype W] [DecidableEq W] in
/-- The tensor product `⊗_e A_e` acting on the index is fork A's `kernelOp`. -/
theorem act_piKron (A : ∀ e, Matrix (Ω e) (Ω e) ℝ) (Z : (∀ e, Ω e) → W → ℝ) (ω : ∀ e, Ω e)
    (x : W) :
    act (piKron A) Z ω x = Sarkozy.Functional.kernelOp (fun e => A e) (fun ω' => Z ω' x) ω := by
  simp only [act, piKron_apply, Sarkozy.Functional.kernelOp]

variable {Kq : E → Type*} [∀ e, Fintype (Kq e)] [∀ e, DecidableEq (Kq e)]
  {Ωc : ∀ e, Kq e → Type*} [∀ e j, Fintype (Ωc e j)] [∀ e j, DecidableEq (Ωc e j)]

omit [Fintype W] [DecidableEq W] [∀ e j, DecidableEq (Ωc e j)] in
/-- `𝒯 = ⊗_e (2P_e − T_e)` (`def:hyb:coupled`(d)): WP-S's `signedIndexOp` is the kernel
operator of fork A's `signedKernel`, with `T_e = ⊗_j Tc e j`. -/
theorem act_signedIndexOp (Tc : ∀ e j, Matrix (Ωc e j) (Ωc e j) ℝ)
    (Z : (∀ e, ∀ j, Ωc e j) → W → ℝ) (ω : ∀ e, ∀ j, Ωc e j) (x : W) :
    act (signedIndexOp Tc) Z ω x =
      Sarkozy.Functional.kernelOp (Ωe := fun e => ∀ j, Ωc e j)
        (Sarkozy.Functional.signedKernel (fun e => piKron (Tc e))) (fun ω' => Z ω' x) ω := by
  unfold signedIndexOp
  rw [act_piKron]
  congr 1

omit [Fintype W] [DecidableEq W] [∀ e j, DecidableEq (Ωc e j)] in
/-- `⊗_{e ∈ 𝒮} T_e ⊗_{e ∉ 𝒮} P_e`: WP-S's operator form is the kernel operator of fork A's
`mixedKernel`. -/
theorem act_mixedOp (Tc : ∀ e j, Matrix (Ωc e j) (Ωc e j) ℝ) (S : Finset E)
    (Z : (∀ e, ∀ j, Ωc e j) → W → ℝ) (ω : ∀ e, ∀ j, Ωc e j) (x : W) :
    act (piKron (fun e => if e ∈ S then piKron (Tc e) else meanMatrix (∀ j, Ωc e j))) Z ω x =
      Sarkozy.Functional.kernelOp (Ωe := fun e => ∀ j, Ωc e j)
        (Sarkozy.Functional.mixedKernel (fun e => piKron (Tc e)) S) (fun ω' => Z ω' x) ω := by
  rw [act_piKron]
  congr 1

end Encodings

/-! ### The bridge and `eq:record:expansion` for the frame's signed index form -/

section Bridge

variable {E : Type} [Fintype E] [DecidableEq E] {Kq : E → Type} [∀ e, Fintype (Kq e)]
  [∀ e, DecidableEq (Kq e)] {Ωc : ∀ e, Kq e → Type} [∀ e j, Fintype (Ωc e j)]
  [∀ e j, DecidableEq (Ωc e j)] [∀ e j, Nonempty (Ωc e j)]
  {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
  {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]
  (I : CoupledIndex E Kq Ωc) (ν : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
  (g : ∀ L : ℕ, Finset ℤ → ∀ e, (∀ j, Ωc e j) → (∀ b, Xb L b) → ℝ)
  (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)

/-- The coupled forms `I_𝒮 = E_ω Q_ν(X_ω, (⊗_{e∈𝒮}T_e ⊗_{e∉𝒮}P_e Y)_ω)` of
`def:hyb:coupled`(d) for the frame, in fork A's kernel form. -/
noncomputable def frameCoupledForm (L : ℕ) (A : Finset ℤ) (S : Finset E) : ℝ :=
  Sarkozy.Functional.coupledForm (Ωe := fun e => ∀ j, Ωc e j)
    (cutBilin reservedCut (tensorLaw (ν L))) I.u I.w (g L A) (F L A)
    (fun e => piKron (I.Tc e)) S

/-- **The bridge** (`def:hyb:coupled`(d)): with the same inputs `g` at both ends of the
queries, the frame's signed index form is fork A's `signedForm` for the cut form of
`⊗_b ν_b` and the transitions `T_e = ⊗_j Tc e j`. -/
theorem signedIndexForm_eq_signedForm (L : ℕ) (A : Finset ℤ) :
    signedIndexForm I ν g g F L A =
      Sarkozy.Functional.signedForm (Ωe := fun e => ∀ j, Ωc e j)
        (cutBilin reservedCut (tensorLaw (ν L))) I.u I.w (g L A) (F L A)
        (fun e => piKron (I.Tc e)) := by
  unfold signedIndexForm Sarkozy.Functional.signedForm
  apply FiniteLaw.expect_congr
  intro ω
  rw [cutBilin_apply, productHalf_eq_halfFunction, productHalf_eq_halfFunction]
  congr 1

/-- **`eq:record:expansion`** for the frame's signed index form:
`J_ν = ∑_{𝒮 ⊆ E} (−1)^{|𝒮|} 2^{k−|𝒮|} I_{ν,𝒮}`. -/
theorem signedIndexForm_expansion (L : ℕ) (A : Finset ℤ) :
    signedIndexForm I ν g g F L A =
      ∑ S : Finset E, (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
        frameCoupledForm I ν g F L A S := by
  rw [signedIndexForm_eq_signedForm]
  exact Sarkozy.Functional.signedForm_expansion _ _ _ _ _ _

/-- The coupled forms in WP-S's operator form:
`I_𝒮 = E_ω Q_ν(X_ω, (⊗_e (if e ∈ 𝒮 then ⊗_j Tc e j else meanMatrix)) Y)_ω`. -/
theorem coupledForm_eq_operatorForm (L : ℕ) (A : Finset ℤ) (S : Finset E) :
    frameCoupledForm I ν g F L A S =
      (FiniteLaw.uniform (∀ e, ∀ j, Ωc e j)).expect (fun ω =>
        reservedCut.form (tensorLaw (ν L)) (productHalf I.u (g L A) (F L A) ω)
          (act (piKron (fun e => if e ∈ S then piKron (I.Tc e) else meanMatrix (∀ j, Ωc e j)))
            (productHalf I.w (g L A) (F L A)) ω)) := by
  unfold frameCoupledForm Sarkozy.Functional.coupledForm
  apply FiniteLaw.expect_congr
  intro ω
  rw [cutBilin_apply, productHalf_eq_halfFunction, productHalf_eq_halfFunction]
  congr 1

/-- `I_∅ = Y_ν` (`eq:record:expansion`, second identity) for the frame, under the mean
identity of the inputs (`lem:twointerval`(iii) in the application). -/
theorem frameCoupledForm_empty
    (hg : ∀ L A e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => g L A e η y) = F L A y)
    (L : ℕ) (A : Finset ℤ) :
    frameCoupledForm I ν g F L A ∅ = energyComparison ν F L A := by
  exact Sarkozy.Functional.coupledForm_empty (Ωe := fun e => ∀ j, Ωc e j)
    (cutBilin reservedCut (tensorLaw (ν L))) I.hu I.hw (hg L A) (fun e => piKron (I.Tc e))

/-- **`J_ν − 2^k Y_ν = ∑_{𝒮 ≠ ∅} (−1)^{|𝒮|} 2^{k−|𝒮|} I_{ν,𝒮}`** for the frame, with the
coupled forms in WP-S's operator form; this is the hypothesis `hexp` of
`Sarkozy.Comparison.wrap_summation` before the split of `I_𝒮` by the wrapping queries. -/
theorem signedIndexForm_sub_eq
    (hg : ∀ L A e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => g L A e η y) = F L A y)
    (L : ℕ) (A : Finset ℤ) :
    signedIndexForm I ν g g F L A - 2 ^ Fintype.card E * energyComparison ν F L A =
      ∑ S ∈ (univ : Finset E).powerset.filter (fun S => S ≠ ∅),
        (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
          (FiniteLaw.uniform (∀ e, ∀ j, Ωc e j)).expect (fun ω =>
            reservedCut.form (tensorLaw (ν L)) (productHalf I.u (g L A) (F L A) ω)
              (act (piKron (fun e => if e ∈ S then piKron (I.Tc e) else meanMatrix (∀ j, Ωc e j)))
                (productHalf I.w (g L A) (F L A)) ω)) := by
  rw [signedIndexForm_expansion, ← sum_erase_add _ _ (mem_univ (∅ : Finset E)),
    frameCoupledForm_empty I ν g F hg]
  simp only [card_empty, pow_zero, one_mul, Nat.sub_zero, add_sub_cancel_right]
  rw [powerset_univ, filter_ne']
  apply sum_congr rfl
  intro S _
  rw [coupledForm_eq_operatorForm]

end Bridge

end Sarkozy.PaperFrame
