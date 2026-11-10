module

public import Sarkozy.Moments.CliqueCopies
public import Sarkozy.Moments.CoarseDeficit

/-!
# Choice-vector classes of clique draws (`lem:density:clique36`, analytic part)

`paper/sections/30_density_moment_upgrade.tex`, proof of `lem:density:clique36`. A random pair
`(a ω, b ω)` of labels in a finite alphabet `X` is given by a law `μ` on `Ω`; conditional on it,
draws are independent and uniform on `{a ω, b ω}` (`CliqueCopies.drawLaw`).

* `expect_drawLaw_eq_mixture`: the paper's expansion "into choice vectors". The draw law is the
  uniform mixture, over the coin vectors `c : T → Bool`, of the class laws `classLaw μ a b c`
  (draw `t` is `a ω` if `c t` and `b ω` otherwise).
* `classLaw_mixed_pair`: a class with `m` draws equal to `a ω` and `n` equal to `b ω` has unit
  mixed `L^v` for every `v ≥ max(m, n) r`, if the pair `(a, b)` has unit mixed `L^r`
  (`PairLpBound`): apply the pair moment to the two products, then Hölder within each product
  (`lpNorm_prod_le`). For the balanced class `m = n = 18` this is the paper's `L^{18 r}`.
* `classLaw_uniformMarginals`: every class law has uniform coordinates when `a` and `b` are
  uniform, so it has unit mixed `L^{|T|}` (the truncation `min{36, ·}` of the paper).
* `card_choice_count`, `sum_range_fold`: the counting of choice vectors by the number of `true`
  coins (binomial coefficients) and the folding of the counts `m`, `36 - m` into the minority
  count `k < 18`.
* `coarseGapConstant_le`: the constant of the coarse typed-mixture cost
  (`Sarkozy.coarseGapConstant`, `Moments/CoarseDeficit.lean`) equals the paper's `2/κ` in the
  regime of the clique bands, so `typedCost` is the paper's
  `C_v(Q) ≤ (2d/(κv)) Q^{d/R - d/v}` (`eq:density:typed-mixture-coarse`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open CliqueCopies

/-- Mixed bounds only see expectations. -/
theorem mixedLpBound_of_expect_eq {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]
    [Nonempty X] {μ ν : FiniteLaw (V → X)} (h : ∀ F, μ.expect F = ν.expect F) {p C : ℝ}
    (hν : MixedLpBound ν p C) : MixedLpBound μ p C := by
  intro f
  rw [h]
  exact hν f

/-- Fubini for two finite laws. -/
theorem expect_comm {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (g : Ω → Ξ → ℝ) :
    μ.expect (fun ω => ν.expect (fun c => g ω c)) =
      ν.expect (fun c => μ.expect (fun ω => g ω c)) := by
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun c _ => sum_congr rfl fun ω _ => ?_
  ring

/-- **Hölder within a product**: `‖∏_{t ∈ S} f_t‖_r ≤ ∏_{t ∈ S} ‖f_t‖_{|S| r}` for the uniform
probability on a finite alphabet. -/
theorem lpNorm_prod_le {X ι : Type*} [Fintype X] [Nonempty X] (S : Finset ι) {r : ℝ}
    (hr : 0 < r) (f : ι → X → ℝ) :
    (FiniteLaw.uniform X).lpNorm r (fun x => ∏ t ∈ S, f t x) ≤
      ∏ t ∈ S, (FiniteLaw.uniform X).lpNorm (S.card * r) (f t) := by
  set ν := FiniteLaw.uniform X
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [FiniteLaw.lpNorm, FiniteLaw.moment]
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hsum : ∑ _i : S, 1 / (S.card : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      mul_one_div_cancel hn.ne']
  have hH := ν.abs_expect_prod_le_lpNorm (fun _ : S => (S.card : ℝ)) (fun _ => hn) hsum
    (fun i x => |f i x| ^ r)
  have hfac : ∀ t : ι, ν.lpNorm (S.card) (fun x => |f t x| ^ r) =
      ν.lpNorm (S.card * r) (f t) ^ r := by
    intro t
    unfold FiniteLaw.lpNorm
    rw [ν.moment_rpow_of_nonneg _ _ (fun x => abs_nonneg (f t x))]
    have hm : ν.moment (r * S.card) (fun x => |f t x|) = ν.moment (S.card * r) (f t) := by
      unfold FiniteLaw.moment
      simp only [abs_abs, mul_comm r]
    rw [hm, ← Real.rpow_mul (ν.moment_nonneg _ _)]
    congr 1
    field_simp
  have hmom : ν.moment r (fun x => ∏ t ∈ S, f t x) ≤
      ∏ t ∈ S, ν.lpNorm (S.card * r) (f t) ^ r := by
    have he : ν.moment r (fun x => ∏ t ∈ S, f t x) =
        ν.expect (fun x => ∏ i : S, |f i x| ^ r) := by
      unfold FiniteLaw.moment
      apply ν.expect_congr
      intro x
      rw [Finset.prod_coe_sort S (fun i => |f i x| ^ r), Finset.abs_prod,
        Real.finsetProd_rpow S _ (fun i _ => abs_nonneg (f i x))]
    rw [he]
    refine (le_abs_self _).trans (hH.trans_eq ?_)
    rw [Finset.prod_coe_sort S (fun i => ν.lpNorm (S.card) (fun x => |f i x| ^ r))]
    exact Finset.prod_congr rfl fun t _ => hfac t
  have hL0 : ∀ t, 0 ≤ ν.lpNorm (S.card * r) (f t) := fun t => ν.lpNorm_nonneg _ _
  calc ν.lpNorm r (fun x => ∏ t ∈ S, f t x)
      = ν.moment r (fun x => ∏ t ∈ S, f t x) ^ (1 / r) := rfl
    _ ≤ (∏ t ∈ S, ν.lpNorm (S.card * r) (f t) ^ r) ^ (1 / r) :=
        Real.rpow_le_rpow (ν.moment_nonneg _ _) hmom (by positivity)
    _ = ∏ t ∈ S, ν.lpNorm (S.card * r) (f t) := by
        rw [Real.finsetProd_rpow S _ (fun t _ => hL0 t),
          ← Real.rpow_mul (Finset.prod_nonneg fun t _ => hL0 t), mul_one_div_cancel hr.ne',
          Real.rpow_one]

section Classes

variable {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X] (μ : FiniteLaw Ω) (a b : Ω → X)

/-- The class law of a choice vector `c`: given `ω`, draw `t` is `a ω` if `c t` and `b ω`
otherwise. -/
noncomputable def classLaw {T : Type*} [Fintype T] [DecidableEq T] (c : T → Bool) :
    FiniteLaw (T → X) :=
  μ.map (fun ω t => label a b ω (c t))

theorem expect_classLaw {T : Type*} [Fintype T] [DecidableEq T] (c : T → Bool)
    (F : (T → X) → ℝ) :
    (classLaw μ a b c).expect F = μ.expect (fun ω => F (fun t => label a b ω (c t))) := by
  unfold classLaw
  rw [FiniteLaw.expect_map]
  rfl

/-- **Expansion into choice vectors** (proof of `lem:density:clique36`): the draw law is the
uniform mixture of the class laws over the coin vectors. -/
theorem expect_drawLaw_eq_mixture (T : Type*) [Fintype T] [DecidableEq T] (F : (T → X) → ℝ) :
    (drawLaw μ a b T).expect F = (FiniteLaw.mixture (coins T) (classLaw μ a b)).expect F := by
  rw [expect_drawLaw, FiniteLaw.expect_mixture]
  simp only [expect_classLaw]
  exact expect_comm μ (coins T) _

/-- **A class with both labels** (proof of `lem:density:clique36`): if the pair `(a, b)` has unit
mixed `L^r`, a class with `m` draws equal to `a ω` and `n` equal to `b ω` has unit mixed `L^v`
whenever `m r ≤ v` and `n r ≤ v`. -/
theorem classLaw_mixed_pair [Nonempty X] {T : Type*} [Fintype T] [DecidableEq T] (c : T → Bool)
    {r v : ℝ} (hr : 0 < r) (hpair : PairLpBound μ a b r)
    (hA : ((univ.filter (fun t => c t = true)).card : ℝ) * r ≤ v)
    (hB : ((univ.filter (fun t => ¬ c t = true)).card : ℝ) * r ≤ v) :
    MixedLpBound (classLaw μ a b c) v 1 := by
  intro f
  set S := univ.filter (fun t => c t = true) with hSdef
  set Sc := univ.filter (fun t => ¬ c t = true) with hScdef
  rw [expect_classLaw, one_mul]
  have hsplit : ∀ ω, ∏ t, f t (label a b ω (c t)) =
      (∏ t ∈ S, f t (a ω)) * ∏ t ∈ Sc, f t (b ω) := by
    intro ω
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun t => c t = true)]
    congr 1
    · refine Finset.prod_congr rfl fun t ht => ?_
      rw [(mem_filter.mp ht).2]
      rfl
    · refine Finset.prod_congr rfl fun t ht => ?_
      have : c t = false := by simpa using (mem_filter.mp ht).2
      rw [this]
      rfl
  simp_rw [hsplit]
  refine (hpair (fun x => ∏ t ∈ S, f t x) (fun x => ∏ t ∈ Sc, f t x)).trans ?_
  have hmono : ∀ U : Finset T, (U.card : ℝ) * r ≤ v →
      (FiniteLaw.uniform X).lpNorm r (fun x => ∏ t ∈ U, f t x) ≤
        ∏ t ∈ U, (FiniteLaw.uniform X).lpNorm v (f t) := by
    intro U hU
    refine (lpNorm_prod_le U hr f).trans (Finset.prod_le_prod₀
      (fun t _ => (FiniteLaw.uniform X).lpNorm_nonneg _ _) fun t ht => ?_)
    have hc : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr ⟨t, ht⟩
    exact (FiniteLaw.uniform X).lpNorm_mono (mul_pos hc hr) hU (f t)
  calc _ ≤ (∏ t ∈ S, (FiniteLaw.uniform X).lpNorm v (f t)) *
        ∏ t ∈ Sc, (FiniteLaw.uniform X).lpNorm v (f t) :=
        mul_le_mul (hmono S hA) (hmono Sc hB) ((FiniteLaw.uniform X).lpNorm_nonneg _ _)
          (Finset.prod_nonneg fun t _ => (FiniteLaw.uniform X).lpNorm_nonneg _ _)
    _ = ∏ t, (FiniteLaw.uniform X).lpNorm v (f t) :=
        Finset.prod_filter_mul_prod_filter_not _ _ _

/-- Every class law has uniform coordinates when `a` and `b` are uniform. -/
theorem classLaw_uniformMarginals [Nonempty X] {T : Type*} [Fintype T] [DecidableEq T]
    (c : T → Bool)
    (ha : ∀ g : X → ℝ, μ.expect (fun ω => g (a ω)) = (FiniteLaw.uniform X).expect g)
    (hb : ∀ g : X → ℝ, μ.expect (fun ω => g (b ω)) = (FiniteLaw.uniform X).expect g) :
    HasUniformMarginals (classLaw μ a b c) := by
  intro t g
  rw [expect_classLaw]
  cases h : c t
  · simp only [h, label, Bool.cond_false]
    exact hb g
  · simp only [h, label, Bool.cond_true]
    exact ha g

end Classes

/-! ## Counting choice vectors -/

/-- The number of `true` coins of a choice vector. -/
def trueCount {n : ℕ} (c : Fin n → Bool) : ℕ := (univ.filter (fun t => c t = true)).card

theorem trueCount_le {n : ℕ} (c : Fin n → Bool) : trueCount c ≤ n := by
  unfold trueCount
  exact (card_filter_le _ _).trans (by rw [card_univ, Fintype.card_fin])

theorem falseCount_eq {n : ℕ} (c : Fin n → Bool) :
    (univ.filter (fun t => ¬ c t = true)).card = n - trueCount c := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun t => c t = true)
  rw [card_univ, Fintype.card_fin] at h
  unfold trueCount
  omega

/-- **Choice vectors with `m` true coins**: there are `C(n, m)` of them. -/
theorem card_choice_count (n m : ℕ) :
    (univ.filter (fun c : Fin n → Bool => trueCount c = m)).card = n.choose m := by
  have h := Finset.card_powersetCard m (univ : Finset (Fin n))
  rw [card_univ, Fintype.card_fin] at h
  rw [← h]
  apply Finset.card_nbij' (fun c => univ.filter (fun t => c t = true))
    (fun S t => decide (t ∈ S))
  · intro c hc
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc
    simp only [mem_coe, mem_powersetCard]
    exact ⟨subset_univ _, hc⟩
  · intro S hS
    simp only [mem_coe, mem_powersetCard] at hS
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    unfold trueCount
    have : (univ.filter (fun t => decide (t ∈ S) = true)) = S := by
      ext t
      simp
    rw [this]
    exact hS.2
  · intro c _
    funext t
    simp
  · intro S _
    ext t
    simp

/-- Sums over choice vectors of a function of the number of true coins. -/
theorem sum_choice_count (n : ℕ) (φ : ℕ → ℝ) :
    ∑ c : Fin n → Bool, φ (trueCount c) = ∑ m ∈ range (n + 1), (n.choose m : ℝ) * φ m := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range (n + 1)) (g := trueCount)
    (fun c _ => mem_range.mpr (Nat.lt_succ_of_le (trueCount_le c)))]
  refine sum_congr rfl fun m _ => ?_
  rw [Finset.sum_congr rfl (fun c hc => by rw [(mem_filter.mp hc).2]), sum_const,
    card_choice_count, nsmul_eq_mul]

/-- **Folding the counts `m` and `36 - m` into the minority count.** -/
theorem sum_range_fold (φ : ℕ → ℝ) :
    ∑ m ∈ range 37, ((Nat.choose 36 m : ℕ) : ℝ) * φ (min m (36 - m)) =
      ∑ k ∈ range 18, 2 * ((Nat.choose 36 k : ℕ) : ℝ) * φ k +
        ((Nat.choose 36 18 : ℕ) : ℝ) * φ 18 := by
  set g : ℕ → ℝ := fun m => ((Nat.choose 36 m : ℕ) : ℝ) * φ (min m (36 - m)) with hg
  have h1 : ∑ m ∈ range 37, g m = ∑ m ∈ range 18, g m + (g 18 + ∑ m ∈ Ico 19 37, g m) := by
    rw [range_eq_Ico, range_eq_Ico, ← Finset.sum_Ico_consecutive g (by norm_num : 0 ≤ 18)
      (by norm_num : 18 ≤ 37), Finset.sum_eq_sum_Ico_succ_bot (by norm_num : 18 < 37)]
  have h2 : ∑ m ∈ Ico 19 37, g m = ∑ k ∈ range 18, g (36 - k) := by
    rw [Finset.sum_Ico_eq_sum_range, show 37 - 19 = 18 by norm_num,
      ← Finset.sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    congr 1
    omega
  have h3 : ∀ k ∈ range 18, g (36 - k) = g k := by
    intro k hk
    have hk' := mem_range.mp hk
    simp only [hg]
    rw [Nat.choose_symm (by omega : k ≤ 36), show min (36 - k) (36 - (36 - k)) = min k (36 - k) by
      rw [min_comm]; congr 1; omega]
  have h4 : ∀ k ∈ range 18, g k = ((Nat.choose 36 k : ℕ) : ℝ) * φ k := by
    intro k hk
    have hk' := mem_range.mp hk
    simp only [hg]
    rw [min_eq_left (by omega)]
  rw [h1, h2, Finset.sum_congr rfl h3, Finset.sum_congr rfl h4]
  have h18 : g 18 = ((Nat.choose 36 18 : ℕ) : ℝ) * φ 18 := by simp [hg]
  rw [h18, ← add_assoc, add_comm (∑ k ∈ range 18, _) (((Nat.choose 36 18 : ℕ) : ℝ) * φ 18),
    add_assoc, ← Finset.sum_add_distrib, add_comm]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  ring

/-! ## The coarse constant in the band regime -/

/-- **The coarse constant is `2/κ`** when `κ ∈ (0, 1)`, `ℓ > 1`, `ℓ + κ ≤ 2` and
`2 ℓ (ℓ - 1) ≤ κ² (1 - κ)`: the curvature branch of `coarseGapConstant` is then dominated. With
it, `typedCost s R v d Q = (d/v) (2/κ) Q^{d/R - d/v}`, the paper's coarse charge
`eq:density:typed-mixture-coarse`. -/
theorem coarseGapConstant_le {κ ℓ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) (hℓ : 1 < ℓ)
    (hsum : ℓ + κ ≤ 2) (hcurv : 2 * ℓ * (ℓ - 1) ≤ κ ^ 2 * (1 - κ)) :
    coarseGapConstant κ ℓ ≤ 2 / κ := by
  unfold coarseGapConstant
  apply max_le _ le_rfl
  have h1κ : 0 < 1 - κ := by linarith
  set T := (2 / κ) ^ (1 / (1 - κ)) with hT
  have h2k : 1 ≤ 2 / κ := by rw [le_div_iff₀ hκ]; linarith
  have hT1 : 1 ≤ T := Real.one_le_rpow h2k (by positivity)
  rw [max_eq_right hT1]
  have hTpow : T ^ (ℓ - κ) ≤ (2 / κ) ^ 2 := by
    rw [hT, ← Real.rpow_mul (by positivity)]
    have hexp : 1 / (1 - κ) * (ℓ - κ) ≤ 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h1κ]
      linarith
    calc (2 / κ) ^ (1 / (1 - κ) * (ℓ - κ)) ≤ (2 / κ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h2k hexp
      _ = (2 / κ) ^ 2 := by rw [Real.rpow_two]
  have hc : 0 ≤ ℓ * (ℓ - 1) / (κ * (1 - κ)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hκ.le h1κ.le)
  calc ℓ * (ℓ - 1) / (κ * (1 - κ)) * T ^ (ℓ - κ)
      ≤ ℓ * (ℓ - 1) / (κ * (1 - κ)) * (2 / κ) ^ 2 := mul_le_mul_of_nonneg_left hTpow hc
    _ = 2 / κ * (2 * ℓ * (ℓ - 1) / (κ ^ 2 * (1 - κ))) := by
        field_simp
    _ ≤ 2 / κ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one (by positivity)]
        exact hcurv
    _ = 2 / κ := mul_one _

end Sarkozy.DensityMoments
