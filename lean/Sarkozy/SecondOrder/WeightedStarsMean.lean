module

public import Sarkozy.SecondOrder.WeightedStars

/-!
# Weighted star marginals: the conditional mean and the cross terms (`lem:wt:stars`(b), (c))

`paper/sections/15_second_order.tex`, `lem:wt:stars`. Fix a support `T` (`|T| ≥ 3`), a vertex
`j ∈ T` with in-half neighbourhood `N = N⁰(j)` (`d = |N|`, `o = |N ∩ T|`, `s = |T| - 1`), and an
injective labelling. With `R = x(T∖{j})`, `f = ∏_{a∈R}(X - a)` and `g_A = ∏_{b∈A}(X - b)`:

* `sum_chiA_kernelG`: `∑_ξ χ_A(ξ) 𝒢_R(ξ) = Σ(R, A)/p`, where `Σ(R, A) = ∑_{y,ξ} χ(f(y) g_A(ξ)(y - ξ))`
  (`sigmaRA`);
* `sigmaRA_empty` (`Σ = 0`), `abs_sigmaRA_singleton` (`|Σ|/p ≤ |χ(f(b))| + (s - 1) r`, Weil) and
  `abs_sigmaRA_le` (`|Σ| ≤ p 𝓑_min(s, |A|, |R ∩ A|)`, H4 = `Target.TwoVariable` in both forms);
* `abs_sum_phi_kernelG_le`: on the admissible set `Φ_j`,
  `|∑_{ξ∈Φ_j} 𝒢(ξ)| ≤ 2^{-d}[(d - o) + d(s - 1)r + ∑_{P⊆N, |P|≥2} 𝓑_min(s, |P|, |P ∩ T|) + 2^d(n - 1)s r]`
  (`wtBracket`);
* `wt_cond_first`: **`lem:wt:stars`(b)**, `|E_μ[w_T | x_{-j}]| ≤ β_{T,j}` for a pinned half law,
  with `β_{T,j} = q(1 - e_j)^{-1}·wtBracket` (`wtBeta`). The paper's sum over `a` and `u` with
  binomial weights is the sum over the subsets `P` grouped by `|P| = a`, `|P ∩ T| = u`.
* `wt_cross`: **`lem:wt:stars`(c)**, `|E_μ w_T w_{T'}| ≤ β_{T,j} (D')^{1/2} r` for `j ∈ T∖T'`,
  whenever `E_μ w_{T'}² ≤ q D'`.

The paper's count error `e⁻_d(n)` in `β` is the law's `e_j` here (any count error that the law
satisfies).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target Sarkozy.Labellings

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [hp : Fact p.Prime]

/-- `𝓑_min(m, a, u) = min(𝓑(m, a, u), 𝓑(a, m, u))`. -/
noncomputable def bMin (p m a u : ℕ) : ℝ := min (twoVarBound p m a u) (twoVarBound p a m u)

/-- `Σ(R, A) = ∑_{y,ξ} χ(f_R(y) g_A(ξ) (y - ξ))`. -/
noncomputable def sigmaRA (p : ℕ) [Fact p.Prime] (R A : Finset (ZMod p)) : ℤ :=
  ∑ y, ∑ z, quadraticChar (ZMod p) ((∏ a ∈ R, (y - a)) * (∏ b ∈ A, (z - b)) * (y - z))

theorem sum_chiA_kernelG (R A : Finset (ZMod p)) :
    ∑ z, chiA p A z * kernelG p R z = (1 / (p : ℝ)) * (sigmaRA p R A : ℝ) := by
  have e : ∀ z, chiA p A z * kernelG p R z = (1 / (p : ℝ)) * ∑ y,
      ((quadraticChar (ZMod p) ((∏ a ∈ R, (y - a)) * (∏ b ∈ A, (z - b)) * (y - z)) : ℤ) : ℝ) := by
    intro z
    unfold chiA kernelG
    have h1 : ((quadraticChar (ZMod p) (∏ b ∈ A, (z - b)) : ℤ) : ℝ) *
        ((1 / (p : ℝ)) * ((∑ y, quadraticChar (ZMod p) ((∏ a ∈ R, (y - a)) * (y - z)) : ℤ) : ℝ)) =
        (1 / (p : ℝ)) * ∑ y, ((quadraticChar (ZMod p) (∏ b ∈ A, (z - b)) : ℤ) : ℝ) *
          ((quadraticChar (ZMod p) ((∏ a ∈ R, (y - a)) * (y - z)) : ℤ) : ℝ) := by
      rw [Int.cast_sum, mul_sum, mul_sum, mul_sum]
      exact sum_congr rfl fun y _ => by ring
    rw [h1]
    congr 1
    refine sum_congr rfl fun y _ => ?_
    rw [← Int.cast_mul, ← map_mul, show (∏ b ∈ A, (z - b)) * ((∏ a ∈ R, (y - a)) * (y - z)) =
      (∏ a ∈ R, (y - a)) * (∏ b ∈ A, (z - b)) * (y - z) by ring]
  rw [sum_congr rfl fun z _ => e z, ← mul_sum]
  congr 1
  unfold sigmaRA
  push_cast
  exact sum_comm

theorem sum_chi_sub_left (hp2 : p ≠ 2) (y : ZMod p) :
    ∑ z, ((quadraticChar (ZMod p) (y - z) : ℤ) : ℝ) = 0 := by
  have h := (Equiv.sum_comp (Equiv.subLeft y) (fun w => quadraticChar (ZMod p) w)).trans
    (quadraticChar_sum_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2))
  have : ∑ z, ((quadraticChar (ZMod p) (y - z) : ℤ) : ℝ) =
      ((∑ z, quadraticChar (ZMod p) (Equiv.subLeft y z) : ℤ) : ℝ) := by
    push_cast; rfl
  rw [this, h, Int.cast_zero]

/-- `Σ(R, ∅) = 0`. -/
theorem sigmaRA_empty (hp2 : p ≠ 2) (R : Finset (ZMod p)) : (sigmaRA p R ∅ : ℝ) = 0 := by
  unfold sigmaRA
  push_cast
  have e : ∀ y, ∑ z, ((quadraticChar (ZMod p) ((∏ a ∈ R, (y - a)) * (∏ b ∈ (∅ : Finset (ZMod p)),
      (z - b)) * (y - z)) : ℤ) : ℝ) =
      ((quadraticChar (ZMod p) (∏ a ∈ R, (y - a)) : ℤ) : ℝ) *
        ∑ z, ((quadraticChar (ZMod p) (y - z) : ℤ) : ℝ) := by
    intro y
    rw [mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [prod_empty, mul_one, map_mul, Int.cast_mul]
  rw [sum_congr rfl fun y _ => e y]
  simp only [sum_chi_sub_left hp2, mul_zero, sum_const_zero]

/-- `|Σ(R, {b})|/p ≤ |χ(f_R(b))| + (|R| - 1) r`, from Weil. -/
theorem abs_sigmaRA_singleton (hW : Target.Weil) (hp2 : p ≠ 2) (R : Finset (ZMod p))
    (hR : R.Nonempty) (b : ZMod p) :
    (1 / (p : ℝ)) * |(sigmaRA p R {b} : ℝ)| ≤
      |((quadraticChar (ZMod p) (∏ a ∈ R, (b - a)) : ℤ) : ℝ)| +
        ((R.card : ℝ) - 1) * (1 / Real.sqrt p) := by
  have hWB := weilBound_of_target hW p hp2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set fy : ZMod p → ℝ := fun y => ((quadraticChar (ZMod p) (∏ a ∈ R, (y - a)) : ℤ) : ℝ)
  set cm : ℝ := ((quadraticChar (ZMod p) (-1) : ℤ) : ℝ)
  -- `∑_ξ χ((ξ - b)(y - ξ)) = χ(-1)(p[y = b] - 1)`
  have hinner : ∀ y, ∑ z, ((quadraticChar (ZMod p) ((∏ a ∈ R, (y - a)) * (∏ c ∈ ({b} : Finset (ZMod p)),
      (z - c)) * (y - z)) : ℤ) : ℝ) = fy y * (cm * ((p : ℝ) * (if b = y then 1 else 0) - 1)) := by
    intro y
    rw [← sum_chi_mul_chi hp2 b y, mul_sum, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [prod_singleton]
    simp only [fy, cm]
    rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    ring
  have hsig : (sigmaRA p R {b} : ℝ) = cm * ((p : ℝ) * fy b - ∑ y, fy y) := by
    unfold sigmaRA
    push_cast
    rw [sum_congr rfl fun y _ => hinner y]
    have e : ∀ y, fy y * (cm * ((p : ℝ) * (if b = y then 1 else 0) - 1)) =
        cm * ((p : ℝ) * (if b = y then fy y else 0) - fy y) := by
      intro y; split_ifs <;> ring
    rw [sum_congr rfl fun y _ => e y, ← mul_sum, sum_sub_distrib, ← mul_sum, sum_ite_eq]
    simp
  have hcm : |cm| ≤ 1 := by
    simp only [cm]
    rcases quadraticChar_isQuadratic (ZMod p) (-1) with h | h | h <;> rw [h] <;> norm_num
  have hsumf : |∑ y, fy y| ≤ ((R.card : ℝ) - 1) * Real.sqrt p := by
    have hb := hWB R hR
    rw [ZMod.card] at hb
    have : ∑ y, fy y = (rootSum R : ℝ) := by
      simp only [fy, rootSum]; push_cast; rfl
    rw [this]; exact hb
  rw [hsig, abs_mul]
  calc 1 / (p : ℝ) * (|cm| * |(p : ℝ) * fy b - ∑ y, fy y|)
      ≤ 1 / (p : ℝ) * (1 * (|(p : ℝ) * fy b| + |∑ y, fy y|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hcm (abs_sub _ _) (abs_nonneg _) (by norm_num)
    _ ≤ 1 / (p : ℝ) * ((p : ℝ) * |fy b| + ((R.card : ℝ) - 1) * Real.sqrt p) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [one_mul, abs_mul, abs_of_pos hp0]
        linarith
    _ = |fy b| + ((R.card : ℝ) - 1) * (1 / Real.sqrt p) := by
        rw [mul_add, ← mul_assoc, one_div_mul_cancel hp0.ne', one_mul]
        congr 1
        rw [show 1 / (p : ℝ) * (((R.card : ℝ) - 1) * Real.sqrt p) =
          ((R.card : ℝ) - 1) * (Real.sqrt p / p) by ring, Real.sqrt_div_self']

/-- `|Σ(R, A)| ≤ p 𝓑_min(|R|, |A|, |R ∩ A|)` for `|R|, |A| ≥ 2`, from H4 in both forms. -/
theorem abs_sigmaRA_le (hTV : Target.TwoVariable) (hp2 : p ≠ 2) (R A : Finset (ZMod p))
    (hR : 2 ≤ R.card) (hA : 2 ≤ A.card) :
    (1 / (p : ℝ)) * |(sigmaRA p R A : ℝ)| ≤ bMin p R.card A.card (R ∩ A).card := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have h := hTV p hp2 R A 1 1 one_ne_zero one_ne_zero hR (by omega)
  simp only [one_mul] at h
  have hsig : (sigmaRA p R A : ℝ) = ((∑ y, ∑ z, quadraticChar (ZMod p)
      ((∏ x ∈ R, (y - x)) * (∏ x ∈ A, (z - x)) * (y - z)) : ℤ) : ℝ) := rfl
  obtain ⟨h1, h2⟩ := h
  have h2' := h2 hA
  rw [hsig]
  unfold bMin
  rw [le_min_iff]
  constructor
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hp0, mul_comm]; exact h1
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hp0, mul_comm]; exact h2'

variable {U : Type*} [DecidableEq U]

/-- The bracket of `eq:wt:beta`:
`(d - o) + d(s - 1) r + ∑_{P ⊆ N, |P| ≥ 2} 𝓑_min(s, |P|, |P ∩ T|) + 2^d (n - 1) s r`. -/
noncomputable def wtBracket (p : ℕ) (N T : Finset U) (s n : ℕ) : ℝ :=
  ((N \ T).card : ℝ) + N.card * ((s : ℝ) - 1) * (1 / Real.sqrt p) +
    ∑ P ∈ N.powerset.filter (fun P => 2 ≤ P.card), bMin p s P.card (P ∩ T).card +
    2 ^ N.card * ((n : ℝ) - 1) * s * (1 / Real.sqrt p)


omit [DecidableEq U] in
/-- The pin product over a finset of pins expands over its subsets. -/
theorem pinFin_expand {N : Finset U} {x : U → ZMod p} (hx : Function.Injective x)
    (ς : U → ZMod p) (z : ZMod p) :
    ∏ k ∈ N, (1 + ((quadraticChar (ZMod p) (ς k * (z - x k)) : ℤ) : ℝ)) =
      ∑ J ∈ N.powerset, (∏ k ∈ J, ((quadraticChar (ZMod p) (ς k) : ℤ) : ℝ)) *
        chiA p (J.image x) z := by
  rw [prod_one_add]
  refine sum_congr rfl fun J _ => ?_
  unfold chiA
  rw [prod_image (fun a _ b _ h => hx h), map_prod, Int.cast_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  rw [map_mul, Int.cast_mul]

omit [DecidableEq U] in
theorem pinFin_prod_le (N : Finset U) (x ς : U → ZMod p) (z : ZMod p) :
    ∏ k ∈ N, (1 + ((quadraticChar (ZMod p) (ς k * (z - x k)) : ℤ) : ℝ)) ≤ 2 ^ N.card := by
  calc ∏ k ∈ N, (1 + ((quadraticChar (ZMod p) (ς k * (z - x k)) : ℤ) : ℝ))
      ≤ ∏ _k ∈ N, (2 : ℝ) := by
        refine prod_le_prod₀ (fun k _ => one_add_chi_nonneg _) fun k _ => ?_
        rcases quadraticChar_isQuadratic (ZMod p) (ς k * (z - x k)) with h | h | h <;>
          rw [h] <;> norm_num
    _ = 2 ^ N.card := prod_const _

omit [DecidableEq U] in
/-- With the excluded set containing the pins, `2^d ∑_{z∈Φ} F z = ∑_z P F - ∑_{z∈E} P F`. -/
theorem pinFin_indicator {N : Finset U} (x ς : U → ZMod p) (hς : ∀ k ∈ N, ς k ≠ 0)
    (E : Finset (ZMod p)) (hE : ∀ k ∈ N, x k ∈ E) (F : ZMod p → ℝ) :
    (2 : ℝ) ^ N.card * ∑ z ∈ univ.filter (fun z => z ∉ E ∧
        ∀ k ∈ N, quadraticChar (ZMod p) (ς k * (z - x k)) = 1), F z =
      ∑ z, (∏ k ∈ N, (1 + ((quadraticChar (ZMod p) (ς k * (z - x k)) : ℤ) : ℝ))) * F z -
        ∑ z ∈ E, (∏ k ∈ N, (1 + ((quadraticChar (ZMod p) (ς k * (z - x k)) : ℤ) : ℝ))) * F z := by
  set Φ := univ.filter (fun z => z ∉ E ∧ ∀ k ∈ N, quadraticChar (ZMod p) (ς k * (z - x k)) = 1)
  set P : ZMod p → ℝ := fun z => ∏ k ∈ N, (1 + ((quadraticChar (ZMod p) (ς k * (z - x k)) : ℤ) : ℝ))
  have hPout : ∀ z, z ∉ E → P z = if z ∈ Φ then 2 ^ N.card else 0 := by
    intro z hzE
    by_cases hz : z ∈ Φ
    · simp only [hz, ↓reduceIte]
      have hz' := (mem_filter.mp hz).2.2
      simp only [P]
      rw [prod_congr rfl fun k hk => by rw [hz' k hk]]
      simp only [Int.cast_one]
      rw [prod_const]
      norm_num
    · simp only [hz, ↓reduceIte]
      have hex : ∃ k ∈ N, quadraticChar (ZMod p) (ς k * (z - x k)) ≠ 1 := by
        by_contra hcon
        simp only [not_exists, not_and, not_not] at hcon
        exact hz (mem_filter.mpr ⟨mem_univ _, hzE, hcon⟩)
      obtain ⟨k, hk, hne1⟩ := hex
      have hne : ς k * (z - x k) ≠ 0 :=
        mul_ne_zero (hς k hk) (sub_ne_zero.mpr fun h => hzE (h ▸ hE k hk))
      have hm1 : quadraticChar (ZMod p) (ς k * (z - x k)) = -1 := by
        rcases quadraticChar_dichotomy hne with h | h
        · exact absurd h hne1
        · exact h
      exact prod_eq_zero hk (by rw [hm1]; norm_num)
  have hind : ∀ z, (if z ∈ Φ then (2 : ℝ) ^ N.card * F z else 0) =
      P z * F z - (if z ∈ E then P z * F z else 0) := by
    intro z
    by_cases hzE : z ∈ E
    · have hzΦ : z ∉ Φ := fun h => (mem_filter.mp h).2.1 hzE
      simp only [hzΦ, hzE, ↓reduceIte, sub_self]
    · rw [hPout z hzE]
      by_cases hzΦ : z ∈ Φ
      · simp only [hzΦ, hzE, ↓reduceIte, sub_zero]
      · simp only [hzΦ, hzE, ↓reduceIte, zero_mul, sub_zero]
  have h1 : ∑ z, (if z ∈ Φ then (2 : ℝ) ^ N.card * F z else 0) =
      (2 : ℝ) ^ N.card * ∑ z ∈ Φ, F z := by
    rw [sum_ite_mem, univ_inter, mul_sum]
  have h2 : ∑ z, (if z ∈ E then P z * F z else 0) = ∑ z ∈ E, P z * F z := by
    rw [sum_ite_mem, univ_inter]
  rw [← h1, ← h2, ← sum_sub_distrib]
  exact sum_congr rfl fun z _ => hind z

variable [Fintype U]

/-- **The fibre computation of `lem:wt:stars`(b)**:
`|∑_{ξ∈Φ_j} 𝒢(ξ)| ≤ 2^{-d} · wtBracket`, from Weil and H4. -/
theorem abs_sum_phi_kernelG_le (hW : Target.Weil) (hTV : Target.TwoVariable) (hp2 : p ≠ 2)
    {N T : Finset U} {j : U} (hjN : j ∉ N) (hjT : j ∈ T) (hT3 : 3 ≤ T.card)
    {x : U → ZMod p} (hx : Function.Injective x) (ς : U → ZMod p) (hς : ∀ k ∈ N, ς k ≠ 0) :
    |∑ z ∈ univ.filter (fun z => z ∉ (univ.erase j).image x ∧
        ∀ k ∈ N, quadraticChar (ZMod p) (ς k * (z - x k)) = 1),
        kernelG p ((T.erase j).image x) z| ≤
      (1 / 2 ^ N.card) * wtBracket p N T (T.card - 1) (Fintype.card U) := by
  set R := (T.erase j).image x with hRdef
  set E := (univ.erase j).image x with hEdef
  set r := 1 / Real.sqrt p with hr
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr0 : 0 ≤ r := by positivity
  have hRcard : R.card = T.card - 1 := by
    rw [hRdef, card_image_of_injective _ hx, card_erase_of_mem hjT]
  have hR2 : 2 ≤ R.card := by omega
  have hRne : R.Nonempty := card_pos.mp (by omega)
  have hEcard : E.card = Fintype.card U - 1 := by
    rw [hEdef, card_image_of_injective _ hx, card_erase_of_mem (mem_univ j), card_univ]
  have hjk : ∀ k ∈ N, k ≠ j := fun k hk h => hjN (h ▸ hk)
  have hE : ∀ k ∈ N, x k ∈ E := fun k hk =>
    mem_image_of_mem x (mem_erase.mpr ⟨hjk k hk, mem_univ _⟩)
  set P : ZMod p → ℝ := fun z =>
    ∏ k ∈ N, (1 + ((quadraticChar (ZMod p) (ς k * (z - x k)) : ℤ) : ℝ))
  have hind := pinFin_indicator x ς hς E hE (kernelG p R)
  have h2d : (0 : ℝ) < 2 ^ N.card := by positivity
  -- 1. the complete sum
  have hfull : ∑ z, P z * kernelG p R z = ∑ J ∈ N.powerset,
      (∏ k ∈ J, ((quadraticChar (ZMod p) (ς k) : ℤ) : ℝ)) *
        ((1 / (p : ℝ)) * (sigmaRA p R (J.image x) : ℝ)) := by
    have e : ∀ z, P z * kernelG p R z = ∑ J ∈ N.powerset,
        (∏ k ∈ J, ((quadraticChar (ZMod p) (ς k) : ℤ) : ℝ)) * (chiA p (J.image x) z * kernelG p R z) := by
      intro z
      simp only [P]
      rw [pinFin_expand hx ς z, sum_mul]
      exact sum_congr rfl fun J _ => by ring
    rw [sum_congr rfl fun z _ => e z, sum_comm]
    refine sum_congr rfl fun J _ => ?_
    rw [← mul_sum, sum_chiA_kernelG]
  -- 2. each subset of pins
  have hfx : ∀ k ∈ N, |((quadraticChar (ZMod p) (∏ a ∈ R, (x k - a)) : ℤ) : ℝ)| =
      if k ∈ T then 0 else 1 := by
    intro k hk
    by_cases hkT : k ∈ T
    · have hmem : x k ∈ R := mem_image_of_mem x (mem_erase.mpr ⟨hjk k hk, hkT⟩)
      simp only [hkT, ↓reduceIte]
      rw [prod_eq_zero hmem (sub_self _), quadraticChar_zero]
      simp
    · have hnot : x k ∉ R := by
        intro h
        obtain ⟨t, ht, hxt⟩ := mem_image.mp h
        exact hkT (hx hxt ▸ (mem_erase.mp ht).2)
      have hne : ∏ a ∈ R, (x k - a) ≠ 0 := prod_ne_zero_iff.mpr fun a ha =>
        sub_ne_zero.mpr fun h => hnot (h ▸ ha)
      simp only [hkT, ↓reduceIte]
      rcases quadraticChar_dichotomy hne with h | h <;> rw [h] <;> norm_num
  have hJ : ∀ J ∈ N.powerset, (1 / (p : ℝ)) * |(sigmaRA p R (J.image x) : ℝ)| ≤
      (if J.card = 1 then (∑ k ∈ J, |((quadraticChar (ZMod p) (∏ a ∈ R, (x k - a)) : ℤ) : ℝ)|) +
          ((T.card - 1 : ℕ) - 1) * r else 0) +
        (if 2 ≤ J.card then bMin p (T.card - 1) J.card (J ∩ T).card else 0) := by
    intro J hJ
    have hJN := mem_powerset.mp hJ
    have hJcard : (J.image x).card = J.card := card_image_of_injective _ hx
    rcases Nat.lt_or_ge J.card 2 with hlt | hge
    · have h2 : ¬ 2 ≤ J.card := by omega
      rcases (by omega : J.card = 0 ∨ J.card = 1) with h0 | h1
      · rw [card_eq_zero.mp h0, image_empty, sigmaRA_empty hp2]
        simp
      · obtain ⟨k, rfl⟩ := card_eq_one.mp h1
        rw [image_singleton]
        have hb := abs_sigmaRA_singleton hW hp2 R hRne (x k)
        rw [hRcard] at hb
        simp only [h2, ↓reduceIte, add_zero]
        simp only [eq_true h1, ↓reduceIte, sum_singleton]
        exact hb
    · have h1 : J.card ≠ 1 := by omega
      have hb := abs_sigmaRA_le hTV hp2 R (J.image x) hR2 (by rw [hJcard]; exact hge)
      have hint : R ∩ J.image x = (J ∩ T).image x := by
        rw [hRdef, ← image_inter _ _ hx]
        congr 1
        ext k
        simp only [mem_inter, mem_erase]
        constructor
        · rintro ⟨⟨_, hkT⟩, hkJ⟩; exact ⟨hkJ, hkT⟩
        · rintro ⟨hkJ, hkT⟩; exact ⟨⟨hjk k (hJN hkJ), hkT⟩, hkJ⟩
      rw [hint, hRcard, hJcard, card_image_of_injective (J ∩ T) hx] at hb
      simp only [h1, hge, ↓reduceIte, zero_add]
      exact hb
  -- 3. sum over the subsets
  have hsumJ : |∑ z, P z * kernelG p R z| ≤ ((N \ T).card : ℝ) +
      N.card * (((T.card - 1 : ℕ) : ℝ) - 1) * r +
      ∑ J ∈ N.powerset.filter (fun J => 2 ≤ J.card), bMin p (T.card - 1) J.card (J ∩ T).card := by
    rw [hfull]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hstep : ∀ J ∈ N.powerset, |(∏ k ∈ J, ((quadraticChar (ZMod p) (ς k) : ℤ) : ℝ)) *
        ((1 / (p : ℝ)) * (sigmaRA p R (J.image x) : ℝ))| ≤
        (if J.card = 1 then (∑ k ∈ J, |((quadraticChar (ZMod p) (∏ a ∈ R, (x k - a)) : ℤ) : ℝ)|) +
            ((T.card - 1 : ℕ) - 1) * r else 0) +
          (if 2 ≤ J.card then bMin p (T.card - 1) J.card (J ∩ T).card else 0) := by
      intro J hJmem
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / p)]
      exact (mul_le_of_le_one_left (by positivity) (abs_sign_prod_le ς J)).trans (hJ J hJmem)
    refine (sum_le_sum hstep).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_filter, ← sum_filter, ← powersetCard_eq_filter,
      powersetCard_one, sum_map]
    simp only [Function.Embedding.coeFn_mk, sum_singleton, sum_add_distrib, sum_const,
      nsmul_eq_mul]
    have hcnt : ∑ k ∈ N, |((quadraticChar (ZMod p) (∏ a ∈ R, (x k - a)) : ℤ) : ℝ)| =
        ((N \ T).card : ℝ) := by
      rw [sum_congr rfl hfx, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul,
        mul_one, sdiff_eq_filter]
    rw [hcnt]
    ring
  -- 4. the excluded labels
  have hexcl : |∑ z ∈ E, P z * kernelG p R z| ≤
      2 ^ N.card * (((Fintype.card U : ℕ) : ℝ) - 1) * ((T.card - 1 : ℕ) : ℝ) * r := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hn : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨j⟩
    calc ∑ z ∈ E, |P z * kernelG p R z| ≤ ∑ _z ∈ E, 2 ^ N.card * (((T.card - 1 : ℕ) : ℝ) * r) := by
          refine sum_le_sum fun z _ => ?_
          rw [abs_mul, abs_of_nonneg (prod_nonneg fun k _ => one_add_chi_nonneg _)]
          have hG := abs_kernelG_le hW hp2 R hR2 z
          rw [hRcard] at hG
          exact mul_le_mul (pinFin_prod_le N x ς z) hG (abs_nonneg _) h2d.le
      _ = 2 ^ N.card * (((Fintype.card U : ℕ) : ℝ) - 1) * ((T.card - 1 : ℕ) : ℝ) * r := by
          rw [sum_const, nsmul_eq_mul, hEcard, Nat.cast_sub hn, Nat.cast_one]
          ring
  -- 5. assemble
  have hsplit : ∑ z ∈ univ.filter (fun z => z ∉ E ∧
      ∀ k ∈ N, quadraticChar (ZMod p) (ς k * (z - x k)) = 1), kernelG p R z =
      (1 / 2 ^ N.card) * (∑ z, P z * kernelG p R z - ∑ z ∈ E, P z * kernelG p R z) := by
    rw [← hind]; field_simp
  rw [hsplit, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ N.card)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (abs_sub _ _).trans ?_
  unfold wtBracket
  rw [← hr]
  linarith


/-- `β_{T,j} = q (1 - e_j)^{-1} · wtBracket` (`eq:wt:beta`). -/
noncomputable def wtBeta (L : PinnedHalfLaw p U) (T : Finset U) (j : U) : ℝ :=
  (1 / (p : ℝ)) / (1 - L.e j) * wtBracket p (L.N j) T (T.card - 1) (Fintype.card U)

/-- **`lem:wt:stars`(b)**, fibrewise: `|E_μ[w_T | x_{-j}]| ≤ β_{T,j}`, from Weil and H4. -/
theorem wt_cond_first (hW : Target.Weil) (hTV : Target.TwoVariable) (hp2 : p ≠ 2)
    (L : PinnedHalfLaw p U) {T : Finset U} {j : U} (hj : j ∈ T) (hT3 : 3 ≤ T.card)
    (x : U → ZMod p) :
    |∑ z, L.μ (Function.update x j z) * starW (Function.update x j z) T| ≤
      wtBeta L T j * ∑ z, L.μ (Function.update x j z) := by
  by_cases h0 : ∃ z₀, 0 < L.μ (Function.update x j z₀)
  · obtain ⟨z₀, hz₀⟩ := h0
    have hx' := L.μ_inj _ hz₀
    rw [L.fibre_sum j x z₀ hz₀]
    have hval : ∀ z ∈ pinnedPhi L.N L.sign j x, starW (Function.update x j z) T =
        kernelG p ((T.erase j).image x) z := by
      intro z hz
      have hinj := L.μ_inj _ (L.pos_of_mem_phi j x z₀ hz₀ hz)
      rw [starW_eq_kernelG hinj hj, image_erase_update, Function.update_self]
    rw [sum_congr rfl hval]
    have hmain := abs_sum_phi_kernelG_le hW hTV hp2 (L.not_mem_N j) hj hT3 hx' (L.sign j)
      (fun k _ => L.sign_ne j k)
    change |∑ z ∈ pinnedPhi L.N L.sign j (Function.update x j z₀),
      kernelG p ((T.erase j).image (Function.update x j z₀)) z| ≤ _ at hmain
    rw [pinnedPhi_update L.N L.sign L.not_mem_N, image_erase_update] at hmain
    have hinv := L.inv_phi_card_le j _ hz₀
    rw [pinnedPhi_update L.N L.sign L.not_mem_N] at hinv
    have hM0 : 0 ≤ ∑ z, L.μ (Function.update x j z) := sum_nonneg fun z _ => L.μ_nonneg _
    have hpos := L.phi_card_pos j _ hz₀
    rw [pinnedPhi_update L.N L.sign L.not_mem_N] at hpos
    have he : 0 < 1 - L.e j := by linarith [L.e_lt j]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    have h2d : (0 : ℝ) < 2 ^ (L.N j).card := by positivity
    have hbr : 0 ≤ (1 / 2 ^ (L.N j).card) *
        wtBracket p (L.N j) T (T.card - 1) (Fintype.card U) := (abs_nonneg _).trans hmain
    rw [abs_mul, abs_of_nonneg hM0, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / ((pinnedPhi L.N L.sign j x).card : ℝ))]
    calc (∑ z, L.μ (Function.update x j z)) * (1 / ((pinnedPhi L.N L.sign j x).card : ℝ) *
          |∑ z ∈ pinnedPhi L.N L.sign j x, kernelG p ((T.erase j).image x) z|)
        ≤ (∑ z, L.μ (Function.update x j z)) * (1 / ((pinnedPhi L.N L.sign j x).card : ℝ) *
            ((1 / 2 ^ (L.N j).card) * wtBracket p (L.N j) T (T.card - 1) (Fintype.card U))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain (by positivity)) hM0
      _ ≤ (∑ z, L.μ (Function.update x j z)) * ((1 / (p : ℝ)) * (2 ^ (L.N j).card / (1 - L.e j)) *
            ((1 / 2 ^ (L.N j).card) * wtBracket p (L.N j) T (T.card - 1) (Fintype.card U))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv hbr) hM0
      _ = wtBeta L T j * ∑ z, L.μ (Function.update x j z) := by
          unfold wtBeta
          field_simp
  · have hz := L.fibre_zero j x h0
    simp [hz]

omit [Fintype U] in
theorem starW_update_of_not_mem {T : Finset U} {j : U} (hj : j ∉ T) (x : U → ZMod p)
    (z : ZMod p) : starW (Function.update x j z) T = starW x T := by
  unfold starW
  congr 1
  refine sum_congr rfl fun w _ => prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (fun h : k = j => hj (h ▸ hk))]

/-- **`lem:wt:stars`(c)**: for `j ∈ T ∖ T'`, if `E_μ w_{T'}² ≤ q D'`, then
`|E_μ w_T w_{T'}| ≤ β_{T,j} (D')^{1/2} r`. -/
theorem wt_cross (hW : Target.Weil) (hTV : Target.TwoVariable) (hp2 : p ≠ 2)
    (L : PinnedHalfLaw p U) {T T' : Finset U} {j : U} (hjT : j ∈ T) (hjT' : j ∉ T')
    (hT3 : 3 ≤ T.card) {D' : ℝ} (hD' : ∑ x, L.μ x * starW x T' ^ 2 ≤ (1 / (p : ℝ)) * D') :
    |∑ x, L.μ x * (starW x T * starW x T')| ≤
      wtBeta L T j * (Real.sqrt D' * (1 / Real.sqrt p)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hX : (0 : ℝ) < Fintype.card (ZMod p) := by exact_mod_cast Fintype.card_pos
  have havg : ∀ g : (U → ZMod p) → ℝ, ∑ x, g x =
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, ∑ z, g (Function.update x j z) := by
    intro g
    rw [sum_sum_update, ← mul_assoc, inv_mul_cancel₀ hX.ne', one_mul]
  have hcond := wt_cond_first hW hTV hp2 L hjT hT3
  -- `β ≥ 0`: some fibre has positive mass
  have hβ : 0 ≤ wtBeta L T j := by
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, 0 < L.μ x₀ := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have : ∑ x, L.μ x ≤ 0 := sum_nonpos fun x _ => h x
      linarith [L.μ_sum]
    have hM : 0 < ∑ z, L.μ (Function.update x₀ j z) :=
      lt_of_lt_of_le (by rw [Function.update_eq_self]; exact hx₀)
        (single_le_sum (fun z _ => L.μ_nonneg _) (mem_univ (x₀ j)))
    have := (abs_nonneg _).trans (hcond x₀)
    exact nonneg_of_mul_nonneg_left this hM
  -- condition on everything but `x_j`
  have hre : ∀ x, ∑ z, L.μ (Function.update x j z) *
      (starW (Function.update x j z) T * starW (Function.update x j z) T') =
      starW x T' * ∑ z, L.μ (Function.update x j z) * starW (Function.update x j z) T := by
    intro x
    rw [mul_sum]
    exact sum_congr rfl fun z _ => by rw [starW_update_of_not_mem hjT']; ring
  have hR : ∀ x, ∑ z, L.μ (Function.update x j z) * |starW (Function.update x j z) T'| =
      |starW x T'| * ∑ z, L.μ (Function.update x j z) := by
    intro x
    rw [mul_sum]
    exact sum_congr rfl fun z _ => by rw [starW_update_of_not_mem hjT']; ring
  have habs : ∑ x, L.μ x * |starW x T'| ≤ Real.sqrt (∑ x, L.μ x * starW x T' ^ 2) := by
    have hcs := sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (L.μ x))
      (fun x => Real.sqrt (L.μ x) * |starW x T'|)
    have e1 : ∀ x, Real.sqrt (L.μ x) * (Real.sqrt (L.μ x) * |starW x T'|) = L.μ x * |starW x T'| :=
      fun x => by rw [← mul_assoc, Real.mul_self_sqrt (L.μ_nonneg x)]
    have e2 : ∀ x, Real.sqrt (L.μ x) ^ 2 = L.μ x := fun x => Real.sq_sqrt (L.μ_nonneg x)
    have e3 : ∀ x, (Real.sqrt (L.μ x) * |starW x T'|) ^ 2 = L.μ x * starW x T' ^ 2 :=
      fun x => by rw [mul_pow, Real.sq_sqrt (L.μ_nonneg x), sq_abs]
    simp only [e1, e2, e3, L.μ_sum, one_mul] at hcs
    have h0 : 0 ≤ ∑ x, L.μ x * |starW x T'| :=
      sum_nonneg fun x _ => mul_nonneg (L.μ_nonneg x) (abs_nonneg _)
    rw [← Real.sqrt_sq h0]
    exact Real.sqrt_le_sqrt hcs
  have hD0 : 0 ≤ D' := by
    have : 0 ≤ ∑ x, L.μ x * starW x T' ^ 2 :=
      sum_nonneg fun x _ => mul_nonneg (L.μ_nonneg x) (sq_nonneg _)
    have h1 : 0 ≤ (1 / (p : ℝ)) * D' := this.trans hD'
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < 1 / p)
  have hsqrt : Real.sqrt (∑ x, L.μ x * starW x T' ^ 2) ≤ Real.sqrt D' * (1 / Real.sqrt p) := by
    calc Real.sqrt (∑ x, L.μ x * starW x T' ^ 2) ≤ Real.sqrt ((1 / (p : ℝ)) * D') :=
          Real.sqrt_le_sqrt hD'
      _ = Real.sqrt D' * (1 / Real.sqrt p) := by
          rw [Real.sqrt_mul (by positivity), one_div, Real.sqrt_inv, mul_comm, one_div]
  rw [havg (fun x => L.μ x * (starW x T * starW x T'))]
  simp_rw [hre]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hX)]
  calc (Fintype.card (ZMod p) : ℝ)⁻¹ * |∑ x, starW x T' *
        ∑ z, L.μ (Function.update x j z) * starW (Function.update x j z) T|
      ≤ (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, |starW x T'| *
          (wtBeta L T j * ∑ z, L.μ (Function.update x j z)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcond x) (abs_nonneg _)
    _ = wtBeta L T j * ((Fintype.card (ZMod p) : ℝ)⁻¹ *
          ∑ x, ∑ z, L.μ (Function.update x j z) * |starW (Function.update x j z) T'|) := by
        simp_rw [hR]
        have hc : ∀ x, |starW x T'| * (wtBeta L T j * ∑ z, L.μ (Function.update x j z)) =
            wtBeta L T j * (|starW x T'| * ∑ z, L.μ (Function.update x j z)) := fun x => by ring
        simp_rw [hc, ← mul_sum]
        ring
    _ = wtBeta L T j * ∑ x, L.μ x * |starW x T'| := by
        rw [← havg (fun x => L.μ x * |starW x T'|)]
    _ ≤ wtBeta L T j * (Real.sqrt D' * (1 / Real.sqrt p)) :=
        mul_le_mul_of_nonneg_left (habs.trans hsqrt) hβ

/-- **`lem:wt:stars`, the consequence**: if `E_μ w_T² ≤ q D_T` and `|E_μ w_T w_{T'}| ≤ Ξ_{TT'}`
for `T ≠ T'`, then `‖∑_T c_T w_T‖²_μ ≤ q ∑_T c_T² D_T + ∑_{T ≠ T'} |c_T c_{T'}| Ξ_{TT'}`. -/
theorem wt_norm_sum (L : PinnedHalfLaw p U) (𝒯 : Finset (Finset U)) (c D : Finset U → ℝ)
    (Ξ : Finset U → Finset U → ℝ)
    (hdiag : ∀ T ∈ 𝒯, ∑ x, L.μ x * starW x T ^ 2 ≤ (1 / (p : ℝ)) * D T)
    (hoff : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → |∑ x, L.μ x * (starW x T * starW x T')| ≤ Ξ T T') :
    ∑ x, L.μ x * (∑ T ∈ 𝒯, c T * starW x T) ^ 2 ≤
      (1 / (p : ℝ)) * ∑ T ∈ 𝒯, c T ^ 2 * D T +
        ∑ T ∈ 𝒯, ∑ T' ∈ 𝒯.erase T, |c T * c T'| * Ξ T T' := by
  have hexp : ∑ x, L.μ x * (∑ T ∈ 𝒯, c T * starW x T) ^ 2 =
      ∑ T ∈ 𝒯, ∑ T' ∈ 𝒯, c T * c T' * ∑ x, L.μ x * (starW x T * starW x T') := by
    have e : ∀ x, L.μ x * (∑ T ∈ 𝒯, c T * starW x T) ^ 2 =
        ∑ T ∈ 𝒯, ∑ T' ∈ 𝒯, c T * c T' * (L.μ x * (starW x T * starW x T')) := by
      intro x
      rw [sq, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun T _ => by rw [mul_sum]; exact sum_congr rfl fun T' _ => by ring
    rw [sum_congr rfl fun x _ => e x, sum_comm]
    refine sum_congr rfl fun T _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun T' _ => by rw [mul_sum]
  rw [hexp]
  have hsplit : ∀ T ∈ 𝒯, ∑ T' ∈ 𝒯, c T * c T' * ∑ x, L.μ x * (starW x T * starW x T') =
      c T * c T * ∑ x, L.μ x * (starW x T * starW x T) +
        ∑ T' ∈ 𝒯.erase T, c T * c T' * ∑ x, L.μ x * (starW x T * starW x T') := by
    intro T hT
    rw [← add_sum_erase _ _ hT]
  rw [sum_congr rfl hsplit, sum_add_distrib, mul_sum]
  apply add_le_add
  · refine sum_le_sum fun T hT => ?_
    have h := hdiag T hT
    have e : ∑ x, L.μ x * (starW x T * starW x T) = ∑ x, L.μ x * starW x T ^ 2 :=
      sum_congr rfl fun x _ => by ring
    rw [e]
    calc c T * c T * ∑ x, L.μ x * starW x T ^ 2 ≤ c T * c T * ((1 / (p : ℝ)) * D T) :=
          mul_le_mul_of_nonneg_left h (mul_self_nonneg _)
      _ = (1 / (p : ℝ)) * (c T ^ 2 * D T) := by ring
  · refine sum_le_sum fun T hT => sum_le_sum fun T' hT' => ?_
    have hne : T' ≠ T := (mem_erase.mp hT').1
    have h := hoff T hT T' (mem_erase.mp hT').2 (Ne.symm hne)
    calc c T * c T' * ∑ x, L.μ x * (starW x T * starW x T')
        ≤ |c T * c T' * ∑ x, L.μ x * (starW x T * starW x T')| := le_abs_self _
      _ = |c T * c T'| * |∑ x, L.μ x * (starW x T * starW x T')| := abs_mul _ _
      _ ≤ |c T * c T'| * Ξ T T' := mul_le_mul_of_nonneg_left h (abs_nonneg _)

end Sarkozy.SecondOrder
