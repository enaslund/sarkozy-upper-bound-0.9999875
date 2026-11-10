module

public import Sarkozy.Kernel.UniformRates

@[expose] public section

/-!
# Kernel library: `DualCoordinates` (adapted from OpenAI)

This module is adapted, with minimal changes, from
`lean/OAI/Combinatorics/SquareDifference/DualCoordinates.lean` of OpenAI's math
repository (revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, Apache
License 2.0; see `LICENSE.openai` and `NOTICES.md`). It belongs to the
dependency chain of the actual-square kernel estimate (paper,
`prop:record:kernel20`, Appendix C).

Changes: the namespace `OAI.SquareDifference` is renamed `Sarkozy.Kernel` and
the explicit module header is added; no proof needed changes for the pinned
Lean/mathlib versions. Declarations of the upstream file outside the dependency
closure of this project's kernel theorems were removed (the closure was computed
from the compiled proof terms); the remaining declarations are verbatim. The
import chain is the upstream linear chain restricted to the kernel files
(upstream `PrimeGauss.lean` imported `ScaleTransfer.lean`; here it imports
mathlib only, which suffices).
-/

namespace Sarkozy

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Kernel

section CyclicFourier

variable {q : ℕ} [NeZero q]

noncomputable def cyclicChar (a x : ZMod q) : ℂ := ZMod.stdAddChar (a*x)

lemma cyclicChar_sub_right (a x y : ZMod q) :
    cyclicChar a (x-y)=cyclicChar a x*conj (cyclicChar a y) := by
  simp only [cyclicChar, mul_sub]
  simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]

lemma cyclicChar_neg (a x : ZMod q) : cyclicChar (-a) x=conj (cyclicChar a x) := by
  simp only [cyclicChar, neg_mul, AddChar.map_neg_eq_conj]

lemma cyclicChar_symm (a x : ZMod q) : cyclicChar a x=cyclicChar x a := by
  simp only [cyclicChar, mul_comm]

lemma cyclicChar_expect (a : ZMod q) :
    (𝔼 x, cyclicChar a x)=if a=0 then 1 else 0 := by
  classical
  rw [expect_eq_sum_div_card]
  simp only [cyclicChar, mul_comm a]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp only [card_univ,  ZMod.card]
  split_ifs <;> simp_all

lemma cyclicChar_orthogonal (a b : ZMod q) :
    (𝔼 x, cyclicChar a x*conj (cyclicChar b x))=if a=b then 1 else 0 := by
  classical
  have he x : cyclicChar (a-b) x=cyclicChar a x*conj (cyclicChar b x) := by
    simp only [cyclicChar, sub_mul]
    simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  simp_rw [← he]
  rw [cyclicChar_expect]
  simp only [sub_eq_zero]

noncomputable def cyclicPolynomial (c : ZMod q → ℂ) (x : ZMod q) : ℂ :=
  ∑a, c a*cyclicChar a x

noncomputable def cyclicFourier (f : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  𝔼 x, f x*conj (cyclicChar a x)

lemma cyclicPolynomial_parseval (c : ZMod q → ℂ) :
    (𝔼 x, ‖cyclicPolynomial c x‖^2)=∑a, ‖c a‖^2 := by
  classical
  have he : (𝔼 x, cyclicPolynomial c x*conj (cyclicPolynomial c x))=
      ∑a, c a*conj (c a) := by
    simp only [cyclicPolynomial, map_sum, sum_mul, mul_sum, map_mul]
    rw [expect_sum_comm]
    apply sum_congr rfl; intro a _
    rw [expect_sum_comm]
    have he a b x : c a*cyclicChar a x*(conj (c b)*conj (cyclicChar b x))=
        c a*conj (c b)*(cyclicChar a x*conj (cyclicChar b x)) := by ring
    simp only [he, ← mul_expect, cyclicChar_orthogonal]
    simp
  apply Complex.ofReal_injective
  simpa only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_expect] using he

lemma cyclicFourier_reconstruction (f : ZMod q → ℂ) (z : ZMod q) :
    cyclicPolynomial (cyclicFourier f) z=f z := by
  classical
  unfold cyclicPolynomial cyclicFourier
  simp_rw [Finset.expect_mul]
  rw [← expect_sum_comm]
  have he x : (∑a, f x*conj (cyclicChar a x)*cyclicChar a z)=
      f x*q*(if z=x then 1 else 0) := by
    simp_rw [mul_assoc, mul_comm (conj _), ← cyclicChar_sub_right]
    rw [← mul_sum]
    have hs := cyclicChar_expect (z-x)
    simp_rw [cyclicChar_symm _ (z-x)]
    rw [expect_eq_sum_div_card] at hs
    have hc : (Fintype.card (ZMod q) : ℂ)≠0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hs' := (div_eq_iff hc).mp hs
    rw [hs']
    simp only [sub_eq_zero, ZMod.card]
    ring
  simp only [he, expect_eq_sum_div_card, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ite_true, card_univ, ZMod.card]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))

lemma cyclicFourier_parseval (f : ZMod q → ℂ) :
    (∑a, ‖cyclicFourier f a‖^2)=𝔼 x, ‖f x‖^2 := by
  rw [← cyclicPolynomial_parseval]
  simp only [cyclicFourier_reconstruction]

lemma cyclicFourier_neg (f : ZMod q → ℂ) (a : ZMod q) :
    cyclicFourier f (-a)=𝔼 x, f x*cyclicChar a x := by
  simp only [cyclicFourier, cyclicChar_neg, Complex.conj_conj]

lemma cyclic_bilinear_fourier (F G k : ZMod q → ℂ) :
    (𝔼 x, 𝔼 y, F x*G y*k (y-x))=
      ∑a, cyclicFourier k a*cyclicFourier F a*cyclicFourier G (-a) := by
  have hk z : k z=∑a, cyclicFourier k a*cyclicChar a z :=
    (cyclicFourier_reconstruction k z).symm
  simp_rw [hk, mul_sum, cyclicChar_sub_right, expect_sum_comm]
  apply sum_congr rfl
  intro a _
  have he x y : F x*G y*(cyclicFourier k a*(cyclicChar a y*conj (cyclicChar a x)))=
      cyclicFourier k a*(F x*conj (cyclicChar a x))*(G y*cyclicChar a y) := by ring
  simp_rw [he, ← mul_expect, ← expect_mul]
  rw [cyclicFourier_neg, ← mul_expect]
  rfl

lemma cyclic_bilinear_multiplier (F G k : ZMod q → ℂ)
    (δ : ℝ) (hδ : 0≤δ) (hk : ∀a, ‖cyclicFourier k a‖≤δ) :
    ‖𝔼 x, 𝔼 y, F x*G y*k (y-x)‖≤
      δ*Real.sqrt (𝔼 x, ‖F x‖^2)*Real.sqrt (𝔼 x, ‖G x‖^2) := by
  rw [cyclic_bilinear_fourier]
  calc
    _ ≤ ∑a, ‖cyclicFourier k a*cyclicFourier F a*cyclicFourier G (-a)‖ := norm_sum_le _ _
    _ ≤ δ*∑a, ‖cyclicFourier F a‖*‖cyclicFourier G (-a)‖ := by
      rw [mul_sum]
      apply sum_le_sum
      intro a _
      simp only [norm_mul]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hk a) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ δ*(Real.sqrt (∑a, ‖cyclicFourier F a‖^2)*
        Real.sqrt (∑a, ‖cyclicFourier G (-a)‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hδ
    _ = _ := by
      have hs : (∑a, ‖cyclicFourier G (-a)‖^2)=∑a, ‖cyclicFourier G a‖^2 :=
        Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ (fun a => rfl)
      rw [hs, cyclicFourier_parseval, cyclicFourier_parseval]
      ring

lemma cyclic_bilinear_counting (F G k : ZMod q → ℂ)
    (δ : ℝ) (hδ : 0≤δ) (hk : ∀a, ‖∑x, k x*conj (cyclicChar a x)‖≤δ) :
    ‖∑x, ∑y, F x*G y*k (y-x)‖≤
      δ*Real.sqrt (∑x, ‖F x‖^2)*Real.sqrt (∑x, ‖G x‖^2) := by
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq' : (q:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hf (a : ZMod q) : ‖cyclicFourier k a‖≤δ/q := by
    simp only [cyclicFourier,expect_eq_sum_div_card,card_univ,ZMod.card,norm_div,
      Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hk a) hq.le
  have h := cyclic_bilinear_multiplier F G k (δ/q) (div_nonneg hδ hq.le) hf
  have he : (𝔼 x, 𝔼 y, F x*G y*k (y-x))=
      (∑x, ∑y, F x*G y*k (y-x))/(q:ℂ)^2 := by
    simp only [expect_eq_sum_div_card,card_univ,ZMod.card,← sum_div]
    field_simp
  rw [he,norm_div,norm_pow,Complex.norm_natCast] at h
  simp only [expect_eq_sum_div_card,card_univ,ZMod.card] at h
  simp only [Real.sqrt_div' _ hq.le] at h
  have hs : Real.sqrt (q:ℝ)*Real.sqrt q=q := Real.mul_self_sqrt hq.le
  have hs0 : 0<Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hq
  have hr : δ/q*(Real.sqrt (∑x, ‖F x‖^2)/Real.sqrt q)*
      (Real.sqrt (∑x, ‖G x‖^2)/Real.sqrt q)=
      (δ*Real.sqrt (∑x, ‖F x‖^2)*Real.sqrt (∑x, ‖G x‖^2))/q^2 := by
    field_simp
    rw [Real.sq_sqrt hq.le]
    ring
  rw [hr] at h
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hq)).mp h

end CyclicFourier

end Kernel

namespace Kernel

open Finset

lemma cyclicChar_nat {q : ℕ} [NeZero q] (a : ZMod q) (n : ℕ) :
    cyclicChar a (n:ZMod q)=expPhase (((a.val:ℝ)/q)*n) := by
  have hs := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=q)) n a
  simp only [nsmul_eq_mul] at hs
  rw [cyclicChar,mul_comm a _,hs,stdAddChar_eq_expPhase,← expPhase_nat_mul,mul_comm]

section SequenceKernel

variable {q : ℕ} [instNeZeroq : NeZero q]

noncomputable def cyclicPush {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (z : ZMod q) : ℂ := ∑t∈s, if shift t=z then w t else 0

lemma cyclicPush_transform {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (a : ZMod q) :
    (∑z, cyclicPush s shift w z*conj (cyclicChar a z))=
      ∑t∈s, w t*conj (cyclicChar a (shift t)) := by
  classical
  simp only [cyclicPush,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro t ht
  simp only [ite_mul,zero_mul]
  simp

lemma cyclicPush_point {q : ℕ}
    [NeZero q] {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (hinj : Set.InjOn shift s) (t : T) (ht : t∈s) :
    cyclicPush s shift w (shift t)=w t := by
  classical
  unfold cyclicPush
  rw [sum_eq_single t]
  · simp
  · intro u hu hut
    exact ite_eq_right (fun h => hut (hinj hu ht h))
  · exact fun hh => (hh ht).elim

lemma cyclicPush_bilinear_zero {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (F G : ZMod q → ℂ)
    (hz : ∀x y t, t∈s → shift t=y-x → F x*G y=0) :
    (∑x, ∑y, F x*G y*cyclicPush s shift w (y-x))=0 := by
  classical
  apply sum_eq_zero; intro x _
  apply sum_eq_zero; intro y _
  rw [cyclicPush,mul_sum]
  apply sum_eq_zero; intro t ht
  split_ifs with h
  · rw [hz x y t ht h,zero_mul]
  · exact mul_zero _

lemma cyclic_interval_injective {q : ℕ}
    [NeZero q] (N : ℕ) (hN : N<q) :
    Set.InjOn (fun n : ℕ => ((n+1:ℕ):ZMod q)) (range N) := by
  intro n hn m hm he
  have hn' : n+1<q := lt_of_le_of_lt (by simpa using Nat.succ_le_of_lt (mem_range.mp hn)) hN
  have hm' : m+1<q := lt_of_le_of_lt (by simpa using Nat.succ_le_of_lt (mem_range.mp hm)) hN
  have h := congrArg ZMod.val he
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hn',Nat.mod_eq_of_lt hm'] at h
  omega

lemma cyclic_interval_point (N : ℕ) (hN : N<q) (w : ℕ → ℂ) (z : ZMod q)
    (hz : 1≤z.val ∧ z.val≤N) :
    cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q)) w z=w (z.val-1) := by
  have hh : ((z.val-1+1:ℕ):ZMod q)=z := by
    rw [Nat.sub_add_cancel hz.1,ZMod.natCast_zmod_val]
  rw [← hh]
  have hn : z.val-1∈range N := mem_range.mpr (by omega)
  convert cyclicPush_point (range N) _ w (cyclic_interval_injective N hN) _ hn using 1
  rw [hh]

end SequenceKernel

end Kernel

namespace Kernel

open Finset

section OrderedModel

variable {q : ℕ} [NeZero q]

noncomputable def intervalFourier (N : ℕ) (F : ZMod q → ℂ) (α : ℝ) : ℂ :=
  (N:ℂ)⁻¹*∑x, F x*expPhase (-(x.val:ℝ)*α)

noncomputable def intervalModelWeight {B : Type*} [Fintype B]
    (N : ℕ) (β : B → ℝ) (c : B → ℂ) (n : ℕ) : ℂ :=
  (N:ℂ)⁻¹*∑b, c b*expPhase (-β b*((n:ℝ)+1))

lemma intervalModel_bilinear {B : Type*} [Fintype B]
    (N : ℕ) (hN : N<q) (β : B → ℝ) (c : B → ℂ) (F G : ZMod q → ℂ)
    (hord : ∀x y, F x*G y≠0 → x.val<y.val ∧ y.val≤N) :
    ((∑x, ∑y, F x*G y*cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q))
      (intervalModelWeight N β c) (y-x)) : ℂ)/N=
      ∑b, c b*intervalFourier N F (-β b)*intervalFourier N G (β b) := by
  classical
  have he (x y : ZMod q) : F x*G y*cyclicPush (range N)
      (fun n => ((n+1:ℕ):ZMod q)) (intervalModelWeight N β c) (y-x)=
      (N:ℂ)⁻¹*∑b, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
        (G y*expPhase (-(y.val:ℝ)*β b)) := by
    by_cases hz : F x*G y=0
    · rw [hz,zero_mul]
      symm
      rw [mul_eq_zero]
      refine Or.inr (sum_eq_zero (fun b _ => ?_))
      calc
        _ = c b*(F x*G y)*(expPhase (-(x.val:ℝ)*(-β b))*expPhase (-(y.val:ℝ)*β b)) := by ring
        _ = 0 := by rw [hz]; ring
    · obtain ⟨hxy,hy⟩ := hord x y hz
      have hval : (y-x).val=y.val-x.val := ZMod.val_sub (le_of_lt hxy)
      rw [cyclic_interval_point N hN _ _ (by rw [hval]; omega),intervalModelWeight]
      have hv : (((y-x).val-1:ℕ):ℝ)+1=(y.val:ℝ)-(x.val:ℝ) := by
        rw [hval,Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
        norm_num
      rw [hv]
      simp only [mul_sum]
      apply sum_congr rfl
      intro b _
      have hp : expPhase (-β b*((y.val:ℝ)-(x.val:ℝ)))=
          expPhase (-(x.val:ℝ)*(-β b))*expPhase (-(y.val:ℝ)*β b) := by
        rw [← expPhase_add]
        congr 1
        ring
      rw [hp]
      ring
  have hswap : (∑x, ∑y, ∑b, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
      (G y*expPhase (-(y.val:ℝ)*β b)))=
      ∑b, ∑x, ∑y, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
        (G y*expPhase (-(y.val:ℝ)*β b)) := by
    have hh (x : ZMod q) : (∑y, ∑b, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
        (G y*expPhase (-(y.val:ℝ)*β b)))=
        ∑b, ∑y, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
          (G y*expPhase (-(y.val:ℝ)*β b)) := sum_comm
    simp_rw [hh]
    exact sum_comm
  simp_rw [he]
  simp only [← mul_sum]
  rw [hswap]
  simp only [← mul_sum,← sum_mul]
  rw [mul_sum,sum_div]
  apply sum_congr rfl
  intro b _
  unfold intervalFourier
  ring

end OrderedModel

end Kernel

namespace Kernel

open Finset

section KernelTransforms

variable {q : ℕ} [NeZero q]

lemma cyclic_square_transform (M N : ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑z, cyclicPush (range M) (fun m => (((m+1)^2:ℕ):ZMod q))
      (fun m => (2*((m:ℝ)+1)/(N:ℝ):ℝ) • w (m+1)) z*conj (cyclicChar a z))=
      ∑m∈range M, squareWeight N (-(a.val:ℝ)/q) m*w (m+1) := by
  rw [cyclicPush_transform]
  apply sum_congr rfl
  intro m hm
  rw [cyclicChar_nat,← expPhase_neg]
  have he : -((a.val:ℝ)/q*((((m+1)^2:ℕ):ℝ)))=
      (-(a.val:ℝ)/q)*((m:ℝ)+1)^2 := by push_cast; ring
  rw [he]
  simp only [squareWeight,Complex.real_smul]
  ring

lemma cyclic_model_transform {B : Type*} [Fintype B]
    (N : ℕ) (β : B → ℝ) (c : B → ℂ) (a : ZMod q) :
    (∑z, cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q))
      (intervalModelWeight N β c) z*conj (cyclicChar a z))=
      ∑b, c b*normalizedLinearSum N (-(a.val:ℝ)/q-β b) := by
  rw [cyclicPush_transform]
  simp only [intervalModelWeight,cyclicChar_nat,← expPhase_neg,mul_sum,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  unfold normalizedLinearSum
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,mul_sum]
  apply sum_congr rfl
  intro n hn
  have he : expPhase (-β b*((n:ℝ)+1))*expPhase (-((a.val:ℝ)/q*((n+1:ℕ):ℝ)))=
      expPhase ((-(a.val:ℝ)/q-β b)*((n:ℝ)+1)) := by
    rw [← expPhase_add]
    congr 1
    push_cast
    ring
  calc
    _ = c b*((N:ℂ)⁻¹*(expPhase (-β b*((n:ℝ)+1))*
        expPhase (-((a.val:ℝ)/q*((n+1:ℕ):ℝ))))) := by ring
    _ = _ := by rw [he]

end KernelTransforms

end Kernel

end

end Sarkozy
