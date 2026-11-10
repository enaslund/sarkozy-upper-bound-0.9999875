module

public import Sarkozy.SpectralC.Gauss

@[expose] public section

/-!
# Fourier analysis on a block `∏_{p ∈ 𝔅} 𝔽_p` and the norm of a convolution form

`paper/sections/21_middle_records.tex`, proof of `lem:record:accepting-c2` ("On uniform field
`L²`, the old and new operators … commute and are normal. On a nonconstant complex Fourier mode
their eigenvalues are …").

On the block alphabet `X = ∏_i ℤ/p_iℤ` (primes `pr i`, `i ∈ ι`) with the uniform law, the
characters are `Ψ_ξ(d) = ∏_i e(ξ_i d_i / p_i)` (`Ψ`, built from SpectralC's one-prime `ech`).
Proved here:

* `Ψ_add`, `conj_Ψ`, **`sum_Ψ`** (`∑_ξ Ψ_ξ(d) = N [d = 0]`, `N = |X|`);
* **`parseval`**: `∑_ξ |f̂(ξ)|² = N ∑_a f(a)²` for real `f`, `f̂(ξ) = ∑_a f(a) Ψ_ξ(a)`;
* **`khat_prod`**: the transform of a product kernel `∏_i k_i(d_i)` is `∏_i k̂_i(ξ_i)`;
* `khat_neg`: the transform of `d ↦ k(-d)` is the conjugate;
* **`conv_form_le`**: if `|k̂(ξ)| ≤ M` for every `ξ`, then
  `|∑_{a,b} k(b - a) f(a) g(b)| ≤ M ‖f‖₂ ‖g‖₂`. This is the operator-norm bound of a
  translation-invariant kernel by its largest eigenvalue, which the paper uses for every
  support-diagonal operator of `lem:record:accepting-c2`.
-/

namespace Sarkozy.NormBoundsPaper

open Finset Complex Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- The character `Ψ_ξ(d) = ∏_i e(ξ_i d_i / p_i)` of the block alphabet. -/
noncomputable def Ψ (ξ d : ∀ i, ZMod (pr i)) : ℂ := ∏ i, ech (ξ i) (d i)

/-- The number of labels, `N = ∏_i p_i`, as a complex number. -/
noncomputable def cardC (pr : ι → ℕ) : ℂ := ∏ i, ((pr i : ℕ) : ℂ)

omit [DecidableEq ι] in
theorem cardC_ne_zero : cardC pr ≠ 0 :=
  prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Fact.out : (pr i).Prime).ne_zero

theorem cardC_eq : cardC pr = ((Fintype.card (∀ i, ZMod (pr i)) : ℕ) : ℂ) := by
  rw [Fintype.card_pi]
  unfold cardC
  push_cast
  exact prod_congr rfl fun i _ => by rw [ZMod.card]

omit [DecidableEq ι] in
theorem Ψ_add (ξ a b : ∀ i, ZMod (pr i)) : Ψ ξ (a + b) = Ψ ξ a * Ψ ξ b := by
  unfold Ψ
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by rw [Pi.add_apply, ech_add_right]

omit [DecidableEq ι] in
theorem conj_Ψ (ξ d : ∀ i, ZMod (pr i)) : conj (Ψ ξ d) = Ψ ξ (-d) := by
  unfold Ψ
  rw [map_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [conj_ech, Pi.neg_apply]
  unfold ech
  rw [neg_mul, mul_neg]

omit [DecidableEq ι] in
theorem Ψ_mul_conj (ξ a b : ∀ i, ZMod (pr i)) : Ψ ξ a * conj (Ψ ξ b) = Ψ ξ (a - b) := by
  rw [conj_Ψ, ← Ψ_add, sub_eq_add_neg]

/-- **Orthogonality of the characters**: `∑_ξ Ψ_ξ(d) = N [d = 0]`. -/
theorem sum_Ψ (d : ∀ i, ZMod (pr i)) :
    ∑ ξ : ∀ i, ZMod (pr i), Ψ ξ d = if d = 0 then cardC pr else 0 := by
  unfold Ψ
  rw [← Fintype.prod_sum (fun i x => ech x (d i))]
  have h : ∀ i, ∑ x : ZMod (pr i), ech x (d i) = if d i = 0 then ((pr i : ℕ) : ℂ) else 0 := by
    intro i
    simp_rw [ech_comm _ (d i)]
    exact sum_ech (d i)
  simp_rw [h]
  by_cases hd : d = 0
  · rw [ite_eq_left hd]
    unfold cardC
    exact prod_congr rfl fun i _ => by rw [hd, Pi.zero_apply, ite_eq_left rfl]
  · rw [ite_eq_right hd]
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hd (funext hc)
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

/-- The transform `k̂(ξ) = ∑_d k(d) Ψ_ξ(d)` of a real kernel. -/
noncomputable def khat (k : (∀ i, ZMod (pr i)) → ℝ) (ξ : ∀ i, ZMod (pr i)) : ℂ :=
  ∑ d, (k d : ℂ) * Ψ ξ d

/-- The transform `f̂(ξ) = ∑_a f(a) Ψ_ξ(a)` of a real function (the same formula). -/
theorem khat_def (k : (∀ i, ZMod (pr i)) → ℝ) (ξ : ∀ i, ZMod (pr i)) :
    khat k ξ = ∑ d, (k d : ℂ) * Ψ ξ d := rfl

/-- **The transform of a product kernel** is the product of the one-prime transforms. -/
theorem khat_prod (kk : ∀ i, ZMod (pr i) → ℝ) (ξ : ∀ i, ZMod (pr i)) :
    khat (fun d => ∏ i, kk i (d i)) ξ = ∏ i, ∑ x : ZMod (pr i), (kk i x : ℂ) * ech (ξ i) x := by
  unfold khat Ψ
  rw [Fintype.prod_sum (fun i x => (kk i x : ℂ) * ech (ξ i) x)]
  refine sum_congr rfl fun d _ => ?_
  push_cast
  rw [prod_mul_distrib]

/-- The transform of the reversed kernel `d ↦ k(-d)` is the conjugate transform. -/
theorem khat_neg (k : (∀ i, ZMod (pr i)) → ℝ) (ξ : ∀ i, ZMod (pr i)) :
    khat (fun d => k (-d)) ξ = conj (khat k ξ) := by
  unfold khat
  rw [map_sum]
  rw [← Fintype.sum_equiv (Equiv.neg _) (fun d => (k d : ℂ) * Ψ ξ (-d))
    (fun d => (k (-d) : ℂ) * Ψ ξ d) (fun d => by simp)]
  refine sum_congr rfl fun d _ => ?_
  rw [map_mul, Complex.conj_ofReal, conj_Ψ]

theorem khat_add (k l : (∀ i, ZMod (pr i)) → ℝ) (ξ : ∀ i, ZMod (pr i)) :
    khat (fun d => k d + l d) ξ = khat k ξ + khat l ξ := by
  unfold khat
  rw [← sum_add_distrib]
  refine sum_congr rfl fun d _ => ?_
  push_cast
  ring

theorem khat_sub (k l : (∀ i, ZMod (pr i)) → ℝ) (ξ : ∀ i, ZMod (pr i)) :
    khat (fun d => k d - l d) ξ = khat k ξ - khat l ξ := by
  unfold khat
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  push_cast
  ring

theorem khat_smul (c : ℝ) (k : (∀ i, ZMod (pr i)) → ℝ) (ξ : ∀ i, ZMod (pr i)) :
    khat (fun d => c * k d) ξ = (c : ℂ) * khat k ξ := by
  unfold khat
  rw [mul_sum]
  refine sum_congr rfl fun d _ => ?_
  push_cast
  ring

/-- `f̂(ξ) \overline{ĝ(ξ)}` as a double sum. -/
theorem khat_mul_conj (f g : (∀ i, ZMod (pr i)) → ℝ) (ξ : ∀ i, ZMod (pr i)) :
    khat f ξ * conj (khat g ξ) =
      ∑ a, ∑ b, ((f a : ℂ) * Ψ ξ a) * ((g b : ℂ) * conj (Ψ ξ b)) := by
  rw [khat_def f, khat_def g, map_sum, sum_mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [map_mul, Complex.conj_ofReal]

/-- **Parseval** on the block: `∑_ξ |f̂(ξ)|² = N ∑_a f(a)²`. -/
theorem parseval (f : (∀ i, ZMod (pr i)) → ℝ) :
    ((∑ ξ, ‖khat f ξ‖ ^ 2 : ℝ) : ℂ) = cardC pr * ((∑ a, f a ^ 2 : ℝ) : ℂ) := by
  have h1 : ∀ ξ, ((‖khat f ξ‖ ^ 2 : ℝ) : ℂ) = khat f ξ * conj (khat f ξ) := by
    intro ξ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : ∀ a b : ∀ i, ZMod (pr i),
      ∑ ξ : ∀ i, ZMod (pr i), (f a : ℂ) * Ψ ξ a * ((f b : ℂ) * conj (Ψ ξ b)) =
        (f a : ℂ) * (f b : ℂ) * (if a - b = 0 then cardC pr else 0) := by
    intro a b
    rw [← sum_Ψ (a - b), mul_sum]
    refine sum_congr rfl fun ξ _ => ?_
    rw [← Ψ_mul_conj]
    ring
  have h3 : ∀ a : ∀ i, ZMod (pr i), ∑ b, (f a : ℂ) * (f b : ℂ) *
      (if a - b = 0 then cardC pr else 0) = cardC pr * ((f a ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [sum_eq_single a (fun b _ hb => by rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm hb)),
      mul_zero]) (fun h => absurd (mem_univ a) h), sub_self, ite_eq_left rfl]
    push_cast
    ring
  calc ((∑ ξ, ‖khat f ξ‖ ^ 2 : ℝ) : ℂ)
      = ∑ ξ, ∑ a, ∑ b, ((f a : ℂ) * Ψ ξ a) * ((f b : ℂ) * conj (Ψ ξ b)) := by
        rw [Complex.ofReal_sum]
        exact sum_congr rfl fun ξ _ => (h1 ξ).trans (khat_mul_conj f f ξ)
    _ = ∑ a, ∑ b, ∑ ξ, ((f a : ℂ) * Ψ ξ a) * ((f b : ℂ) * conj (Ψ ξ b)) :=
        sum_comm.trans (sum_congr rfl fun a _ => sum_comm)
    _ = ∑ a, cardC pr * ((f a ^ 2 : ℝ) : ℂ) := by
        refine sum_congr rfl fun a _ => ?_
        rw [← h3 a]
        exact sum_congr rfl fun b _ => h2 a b
    _ = cardC pr * ((∑ a, f a ^ 2 : ℝ) : ℂ) := by
        rw [← mul_sum, Complex.ofReal_sum]

/-- **Fourier inversion** of a real kernel: `N k(e) = ∑_ξ k̂(ξ) \overline{Ψ_ξ(e)}`. -/
theorem kernel_inv (k : (∀ i, ZMod (pr i)) → ℝ) (e : ∀ i, ZMod (pr i)) :
    cardC pr * (k e : ℂ) = ∑ ξ, khat k ξ * conj (Ψ ξ e) := by
  unfold khat
  simp_rw [sum_mul]
  rw [sum_comm]
  have h : ∀ d : ∀ i, ZMod (pr i), ∑ ξ : ∀ i, ZMod (pr i), (k d : ℂ) * Ψ ξ d * conj (Ψ ξ e) =
      (k d : ℂ) * (if d - e = 0 then cardC pr else 0) := by
    intro d
    rw [← sum_Ψ (d - e), mul_sum]
    refine sum_congr rfl fun ξ _ => ?_
    rw [← Ψ_mul_conj]
    ring
  simp_rw [h]
  rw [sum_eq_single e (fun d _ hd => by rw [ite_eq_right (sub_ne_zero.mpr hd), mul_zero])
    (fun h => absurd (mem_univ e) h), sub_self, ite_eq_left rfl]
  ring

/-- **The form of a convolution kernel in Fourier variables**:
`N ∑_{a,b} k(b - a) f(a) g(b) = ∑_ξ k̂(ξ) f̂(ξ) \overline{ĝ(ξ)}`. -/
theorem conv_form_fourier (k f g : (∀ i, ZMod (pr i)) → ℝ) :
    cardC pr * ((∑ a, ∑ b, k (b - a) * f a * g b : ℝ) : ℂ) =
      ∑ ξ, khat k ξ * khat f ξ * conj (khat g ξ) := by
  push_cast
  rw [mul_sum]
  simp_rw [mul_sum]
  have h : ∀ a b : ∀ i, ZMod (pr i), cardC pr * ((k (b - a) : ℂ) * (f a : ℂ) * (g b : ℂ)) =
      ∑ ξ, khat k ξ * ((f a : ℂ) * Ψ ξ a) * ((g b : ℂ) * conj (Ψ ξ b)) := by
    intro a b
    have hk := kernel_inv k (b - a)
    rw [← mul_assoc, ← mul_assoc, hk, sum_mul, sum_mul]
    refine sum_congr rfl fun ξ _ => ?_
    have : conj (Ψ ξ (b - a)) = Ψ ξ a * conj (Ψ ξ b) := by
      rw [Ψ_mul_conj, conj_Ψ, neg_sub]
    rw [this]
    ring
  simp_rw [h]
  have hfg : ∀ ξ, khat k ξ * khat f ξ * conj (khat g ξ) =
      ∑ a, ∑ b, khat k ξ * ((f a : ℂ) * Ψ ξ a) * ((g b : ℂ) * conj (Ψ ξ b)) := by
    intro ξ
    rw [mul_assoc, khat_mul_conj, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    ring
  simp_rw [hfg]
  exact (sum_comm.trans (sum_congr rfl fun a _ => sum_comm)).symm

/-- **The norm of a convolution form is at most its largest eigenvalue**: if `|k̂(ξ)| ≤ M` for
every `ξ`, then `|∑_{a,b} k(b - a) f(a) g(b)| ≤ M ‖f‖₂ ‖g‖₂`. -/
theorem conv_form_le (k f g : (∀ i, ZMod (pr i)) → ℝ) {M : ℝ} (hM : ∀ ξ, ‖khat k ξ‖ ≤ M) :
    |∑ a, ∑ b, k (b - a) * f a * g b| ≤
      M * Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ b, g b ^ 2) := by
  set N : ℝ := ∏ i, ((pr i : ℕ) : ℝ) with hN
  have hNC : cardC pr = (N : ℂ) := by unfold cardC; rw [hN]; push_cast; rfl
  have hNpos : 0 < N := prod_pos fun i _ => by exact_mod_cast (Fact.out : (pr i).Prime).pos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hF := conv_form_fourier k f g
  rw [hNC] at hF
  -- `N |Q| ≤ M ∑ |f̂| |ĝ|`
  have h1 : N * |∑ a, ∑ b, k (b - a) * f a * g b| ≤ M * ∑ ξ, ‖khat f ξ‖ * ‖khat g ξ‖ := by
    have : N * |∑ a, ∑ b, k (b - a) * f a * g b| =
        ‖∑ ξ, khat k ξ * khat f ξ * conj (khat g ξ)‖ := by
      rw [← hF, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hNpos.le,
        Real.norm_eq_abs]
    rw [this, mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun ξ _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hM ξ) (norm_nonneg _))
      (norm_nonneg _)
  -- Cauchy–Schwarz and Parseval
  have h2 : ∑ ξ, ‖khat f ξ‖ * ‖khat g ξ‖ ≤
      Real.sqrt (∑ ξ, ‖khat f ξ‖ ^ 2) * Real.sqrt (∑ ξ, ‖khat g ξ‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hp : ∀ u : (∀ i, ZMod (pr i)) → ℝ, ∑ ξ, ‖khat u ξ‖ ^ 2 = N * ∑ a, u a ^ 2 := by
    intro u
    have := parseval u
    rw [hNC] at this
    exact_mod_cast this
  rw [hp f, hp g, Real.sqrt_mul hNpos.le, Real.sqrt_mul hNpos.le] at h2
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have h3 : N * |∑ a, ∑ b, k (b - a) * f a * g b| ≤
      N * (M * Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ b, g b ^ 2)) := by
    calc N * |∑ a, ∑ b, k (b - a) * f a * g b|
        ≤ M * (Real.sqrt N * Real.sqrt (∑ a, f a ^ 2) *
            (Real.sqrt N * Real.sqrt (∑ a, g a ^ 2))) := h1.trans
          (mul_le_mul_of_nonneg_left h2 hM0)
      _ = (Real.sqrt N * Real.sqrt N) *
            (M * Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ b, g b ^ 2)) := by ring
      _ = N * (M * Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ b, g b ^ 2)) := by rw [hsN]
  exact le_of_mul_le_mul_left h3 hNpos

end Sarkozy.NormBoundsPaper
