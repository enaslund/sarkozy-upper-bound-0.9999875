module

public import Sarkozy.CancellationSteps.Main

/-!
# The structural clauses of `FibreRest`: coprimality, coverage and the size of `D`

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 3, and
`lem:scale-conditions`(v), (vi). The fibre modulus is `D = M₀ ∏_{c ∈ E} m_c` with `E` the
conditioned atoms (prefix, tail primes below `P₅`, the primes of `U`). From elementary facts
about the data:

* `coprime_free_fibreModulus`: if `M₀` is coprime to every atom modulus and the atom moduli are
  pairwise coprime, then `D` is prime to every free tail prime;
* `cover_free_of_cover`: if every prime `ℓ ≤ N^{1/40}` divides `M₀` or a prefix modulus or is a
  tail prime (the atoms cover the small primes, `lem:scale-conditions`(v)), then every such `ℓ`
  not dividing `D` is a free tail prime;
* `prod_frozenCoords_eq`: `∏_{c ∈ E} m_c = Q_pre(L) q_U`, with
  `Q_pre(L) = ∏_{J₀} m₀ ∏_{p_j < P₅} p_j` (`lowModulus`) and `q_U` the support conductor;
  `lowModulus_le`: `Q_pre(L) ≤ ∏ m₀ (P₅ − 1)!` for distinct tail primes (`lowBound`);
* `fibre_sizes`: for `N ≥ (K M₀ Q_pre)^{120}` and `q_U ≤ N^{1/60}`: `N^{1/40} ∏_E m ≤ N^{1/20}`
  (`H D_E ≤ Q`), `D ≤ N^{1/20}` and `D ≤ N/K = L` (`lem:scale-conditions`(vi)).

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset
open scoped BigOperators
open Sarkozy.Cancellation Sarkozy.Mixing Sarkozy.PaperFrame Sarkozy.FourierArithmetic
  Sarkozy.Functional

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-! ## Coprimality -/

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
/-- **`D` is prime to the free tail primes**, when `M₀` is coprime to every atom modulus and the
atom moduli are pairwise coprime. -/
theorem coprime_free_fibreModulus (L P5 : ℕ) (U : TailIdx p L P5 → Bool) {M : ℕ}
    (hcop0 : ∀ c : J₀ ⊕ J L, Nat.Coprime M (joinModuli m₀ (p L) c))
    (hcopE : ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (k : {k : TailIdx p L P5 // U k = false}) :
    Nat.Coprime (tailQ p L P5 k.1) (fibreModulus m₀ p L P5 U M) := by
  unfold fibreModulus
  have hfree : (Sum.inr k.1.1 : J₀ ⊕ J L) ∉ frozenCoords (J₀ := J₀) p L P5 U :=
    (not_mem_frozenCoords p L P5 U _).mpr ⟨k.1.2, k.2⟩
  refine Nat.Coprime.mul_right (hcop0 (Sum.inr k.1.1)).symm ?_
  refine Nat.Coprime.prod_right fun c hc => ?_
  exact hcopE (Sum.inr k.1.1) c (fun h => hfree (h ▸ hc))

/-! ## Coverage -/

omit [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
/-- **Every small prime not dividing `D` is a free tail prime**, when every prime `ℓ ≤ N^{1/40}`
divides `M₀` or a prefix modulus or is a tail prime. -/
theorem cover_free_of_cover (L P5 : ℕ) (U : TailIdx p L P5 → Bool) {M : ℕ} (H : ℝ)
    (hcover : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ H →
      ℓ ∣ M ∨ (∃ i, ℓ ∣ m₀ i) ∨ ∃ j, p L j = ℓ) :
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ H → ¬ ℓ ∣ fibreModulus m₀ p L P5 U M →
      ∃ k : {k : TailIdx p L P5 // U k = false}, tailQ p L P5 k.1 = ℓ := by
  intro ℓ hℓ hH hnd
  unfold fibreModulus at hnd
  rcases hcover ℓ hℓ hH with hM | ⟨i, hi⟩ | ⟨j, hj⟩
  · exact absurd (dvd_mul_of_dvd_left hM _) hnd
  · have hc : (Sum.inl i : J₀ ⊕ J L) ∈ frozenCoords (J₀ := J₀) p L P5 U := by
      by_contra h
      exact (not_mem_frozenCoords p L P5 U _).mp h
    exact absurd (dvd_mul_of_dvd_right ((show ℓ ∣ joinModuli m₀ (p L) (Sum.inl i) from
      hi).trans (dvd_prod_of_mem _ hc)) M) hnd
  · by_cases hc : (Sum.inr j : J₀ ⊕ J L) ∈ frozenCoords (J₀ := J₀) p L P5 U
    · exact absurd (dvd_mul_of_dvd_right ((show ℓ ∣ joinModuli m₀ (p L) (Sum.inr j) from
        hj ▸ dvd_refl _).trans (dvd_prod_of_mem _ hc)) M) hnd
    · obtain ⟨h1, h2⟩ := (not_mem_frozenCoords p L P5 U _).mp hc
      exact ⟨⟨⟨j, h1⟩, h2⟩, hj⟩

/-! ## The size of `D` -/

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
/-- `∏_{c ∈ E} m_c = ∏_{J₀} m₀ · ∏_{p_j < P₅} p_j · ∏_{k ∈ U} p_k`. -/
theorem prod_frozenCoords_nat (L P5 : ℕ) (U : TailIdx p L P5 → Bool) :
    ∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c =
      (∏ i, m₀ i) * (∏ j ∈ univ.filter (fun j => p L j < P5), p L j) *
        ∏ k : TailIdx p L P5, (if U k then p L k.1 else 1) := by
  classical
  unfold frozenCoords
  rw [prod_filter, Fintype.prod_sum_type]
  have h1 : ∀ i : J₀, (if ¬ IsFreeCoord (J₀ := J₀) p L P5 U (Sum.inl i) then
      joinModuli m₀ (p L) (Sum.inl i) else 1) = m₀ i := by
    intro i
    simp only [IsFreeCoord, not_false_eq_true, ↓reduceIte]
    rfl
  have h2 : ∀ j : J L, (if ¬ IsFreeCoord (J₀ := J₀) p L P5 U (Sum.inr j) then
      joinModuli m₀ (p L) (Sum.inr j) else 1) =
      if h : P5 ≤ p L j then (if U ⟨j, h⟩ then p L j else 1) else p L j := by
    intro j
    show (if ¬ (∃ h : P5 ≤ p L j, U ⟨j, h⟩ = false) then p L j else 1) = _
    by_cases hc : ∃ h : P5 ≤ p L j, U ⟨j, h⟩ = false
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not.mpr hc))]
      obtain ⟨hj, hU⟩ := hc
      simp only [hj, ↓reduceDIte, hU, Bool.false_eq_true, ↓reduceIte]
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      by_cases hj : P5 ≤ p L j
      · have hU : U ⟨j, hj⟩ = true := by
          by_contra h
          exact hc ⟨hj, by simpa using h⟩
        simp only [hj, ↓reduceDIte, hU, ↓reduceIte]
      · simp only [hj, ↓reduceDIte]
  simp_rw [h1, h2]
  rw [mul_assoc]
  congr 1
  rw [← prod_filter_mul_prod_filter_not univ (fun j => p L j < P5)]
  congr 1
  · refine prod_congr rfl fun j hj => ?_
    have hj' : ¬ P5 ≤ p L j := not_le.mpr (mem_filter.mp hj).2
    simp only [hj', ↓reduceDIte]
  · rw [show univ.filter (fun j => ¬ p L j < P5) = univ.filter (fun j => P5 ≤ p L j) by
      ext j; simp]
    rw [prod_subtype (univ.filter (fun j => P5 ≤ p L j)) (p := fun j => P5 ≤ p L j)
      (fun j => by simp)]
    refine Fintype.prod_congr _ _ fun k => ?_
    simp only [k.2, ↓reduceDIte]

/-- The low part `Q_pre(L) = ∏_{J₀} m₀ ∏_{p_j < P₅} p_j` of `∏_E m`. -/
def lowModulus (L P5 : ℕ) : ℕ := (∏ i, m₀ i) * ∏ j ∈ univ.filter (fun j => p L j < P5), p L j

/-- The bound `∏_{J₀} m₀ ∏_{1 ≤ n ≤ P₅} n` of `Q_pre(L)`, independent of `L`. -/
def lowBound (P5 : ℕ) : ℕ := (∏ i, m₀ i) * ∏ n ∈ Icc 1 P5, n

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, DecidableEq (J L)] in
/-- For distinct tail primes, `Q_pre(L) ≤ lowBound`. -/
theorem lowModulus_le (L P5 : ℕ) (hinj : Function.Injective (p L)) :
    lowModulus m₀ p L P5 ≤ lowBound m₀ P5 := by
  classical
  unfold lowModulus lowBound
  refine Nat.mul_le_mul_left _ ?_
  have himg : ∏ j ∈ univ.filter (fun j => p L j < P5), p L j =
      ∏ n ∈ (univ.filter (fun j => p L j < P5)).image (p L), n :=
    (prod_image (f := fun n : ℕ => n) (g := p L) (fun a _ b _ h => hinj h)).symm
  rw [himg]
  refine prod_le_prod_of_subset_of_one_le ?_ fun n hn _ => (mem_Icc.mp hn).1
  intro n hn
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
  have h1 : 1 ≤ p L j := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  exact mem_Icc.mpr ⟨h1, (mem_filter.mp hj).2.le⟩

omit [DecidableEq J₀] in
theorem one_le_lowBound (P5 : ℕ) : 1 ≤ lowBound m₀ P5 := by
  unfold lowBound
  refine Nat.one_le_iff_ne_zero.mpr (mul_ne_zero ?_ ?_)
  · exact prod_ne_zero_iff.mpr fun i _ => NeZero.ne _
  · exact prod_ne_zero_iff.mpr fun n hn => by have := (mem_Icc.mp hn).1; omega

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
/-- `∏_E m = Q_pre(L) q_U` (as reals). -/
theorem prod_frozenCoords_real (L P5 : ℕ) (U : TailIdx p L P5 → Bool) :
    ((∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c : ℕ) : ℝ) =
      (lowModulus m₀ p L P5 : ℝ) * supportConductor (tailQ p L P5) U := by
  rw [prod_frozenCoords_nat, lowModulus, supportConductor]
  push_cast
  rfl

/-- `N^{1/120} ≥ T` when `T^{120} ≤ N`. -/
lemma le_rpow_of_pow_le {T N : ℝ} (hT : 0 ≤ T) (h : T ^ 120 ≤ N) :
    T ≤ N ^ (1 / 120 : ℝ) := by
  have hN : 0 ≤ N := le_trans (by positivity) h
  calc T = (T ^ 120) ^ (1 / 120 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT]; norm_num
    _ ≤ N ^ (1 / 120 : ℝ) := Real.rpow_le_rpow (by positivity) h (by norm_num)

/-- **The size conditions of Step 3** (`lem:scale-conditions`(vi)), for `N = K L` with
`(K M Q)^{120} ≤ N`, `Q_pre(L) ≤ Q` and `q_U ≤ N^{1/60}`: `N^{1/40} Q_pre(L) q_U ≤ N^{1/20}`,
`M Q_pre(L) q_U ≤ N^{1/20}` and `M Q_pre(L) q_U ≤ L`. -/
theorem fibre_sizes {K M Q L : ℕ} (hK : 1 ≤ K) (hM : 1 ≤ M) (hQ : 1 ≤ Q) {Qpre : ℕ}
    (hQpre : Qpre ≤ Q) {qU : ℝ} (hqU0 : 0 ≤ qU)
    (hqU : qU ≤ ((K * L : ℕ) : ℝ) ^ (1 / 60 : ℝ))
    (hN : ((K * M * Q : ℕ) : ℝ) ^ 120 ≤ ((K * L : ℕ) : ℝ)) :
    ((K * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) * ((Qpre : ℝ) * qU) ≤ ((K * L : ℕ) : ℝ) ^ (1 / 20 : ℝ) ∧
      (M : ℝ) * ((Qpre : ℝ) * qU) ≤ ((K * L : ℕ) : ℝ) ^ (1 / 20 : ℝ) ∧
      (M : ℝ) * ((Qpre : ℝ) * qU) ≤ (L : ℝ) := by
  set N : ℝ := ((K * L : ℕ) : ℝ) with hNdef
  have hT1 : (1 : ℝ) ≤ ((K * M * Q : ℕ) : ℝ) := by
    have : 1 ≤ K * M * Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hN1 : 1 ≤ N := le_trans (one_le_pow₀ hT1) hN
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hT := le_rpow_of_pow_le (by positivity) hN
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (Qpre : ℝ) ≤ Q := by exact_mod_cast hQpre
  have hTe : ((K * M * Q : ℕ) : ℝ) = K * M * Q := by push_cast; ring
  rw [hTe] at hT
  -- the powers of `N`
  have e1 : N ^ (1 / 40 : ℝ) * N ^ (1 / 60 : ℝ) * N ^ (1 / 120 : ℝ) = N ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; norm_num
  have e2 : N ^ (1 / 60 : ℝ) * N ^ (1 / 120 : ℝ) = N ^ (1 / 40 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have m1 : N ^ (1 / 40 : ℝ) ≤ N ^ (1 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have m2 : N ^ (1 / 40 : ℝ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  rw [Real.rpow_one] at m2
  have hp40 : 0 ≤ N ^ (1 / 40 : ℝ) := by positivity
  have hp60 : 0 ≤ N ^ (1 / 60 : ℝ) := by positivity
  have hp120 : 0 ≤ N ^ (1 / 120 : ℝ) := by positivity
  have hQpre0 : (0 : ℝ) ≤ Qpre := by positivity
  -- `Qpre qU ≤ Q N^{1/60}`
  have hb : (Qpre : ℝ) * qU ≤ Q * N ^ (1 / 60 : ℝ) :=
    mul_le_mul hQp hqU hqU0 (by positivity)
  have hKM : (1 : ℝ) ≤ K * M := one_le_mul_of_one_le_of_one_le hKr hMr
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hKMQT : (K : ℝ) * (M * Q) ≤ N ^ (1 / 120 : ℝ) := by rw [← mul_assoc]; exact hT
  have hMQT : (M : ℝ) * Q ≤ N ^ (1 / 120 : ℝ) := by
    refine le_trans ?_ hKMQT
    calc (M : ℝ) * Q = 1 * (M * Q) := (one_mul _).symm
      _ ≤ K * (M * Q) := mul_le_mul_of_nonneg_right hKr (by positivity)
  have hQT : (Q : ℝ) ≤ N ^ (1 / 120 : ℝ) := by
    refine le_trans ?_ hT
    calc (Q : ℝ) = 1 * Q := (one_mul _).symm
      _ ≤ (K * M) * Q := mul_le_mul_of_nonneg_right hKM hQ0
  refine ⟨?_, ?_, ?_⟩
  · calc N ^ (1 / 40 : ℝ) * ((Qpre : ℝ) * qU) ≤ N ^ (1 / 40 : ℝ) * (Q * N ^ (1 / 60 : ℝ)) :=
          mul_le_mul_of_nonneg_left hb hp40
      _ ≤ N ^ (1 / 40 : ℝ) * (N ^ (1 / 120 : ℝ) * N ^ (1 / 60 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hp40
          exact mul_le_mul_of_nonneg_right hQT hp60
      _ = N ^ (1 / 20 : ℝ) := by rw [← e1]; ring
  · calc (M : ℝ) * ((Qpre : ℝ) * qU) ≤ M * (Q * N ^ (1 / 60 : ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (M * Q) * N ^ (1 / 60 : ℝ) := by ring
      _ ≤ N ^ (1 / 120 : ℝ) * N ^ (1 / 60 : ℝ) := mul_le_mul_of_nonneg_right hMQT hp60
      _ = N ^ (1 / 40 : ℝ) := by rw [← e2]; ring
      _ ≤ N ^ (1 / 20 : ℝ) := m1
  · have hNL : N = (K : ℝ) * L := by rw [hNdef]; push_cast; ring
    have hstep : (K : ℝ) * ((M : ℝ) * ((Qpre : ℝ) * qU)) ≤ N := by
      calc (K : ℝ) * ((M : ℝ) * ((Qpre : ℝ) * qU)) ≤ K * (M * (Q * N ^ (1 / 60 : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (K * (M * Q)) * N ^ (1 / 60 : ℝ) := by ring
        _ ≤ N ^ (1 / 120 : ℝ) * N ^ (1 / 60 : ℝ) := mul_le_mul_of_nonneg_right hKMQT hp60
        _ = N ^ (1 / 40 : ℝ) := by rw [← e2]; ring
        _ ≤ N := m2
    rw [hNL] at hstep
    have hK0 : (0 : ℝ) < K := by linarith
    nlinarith

end Sarkozy.CancellationSteps
