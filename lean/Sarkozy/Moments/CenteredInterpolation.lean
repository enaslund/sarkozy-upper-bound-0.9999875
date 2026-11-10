module

public import Sarkozy.Moments.CenteredConvexity

/-!
# Centered `Lʳ` forms from bounded density and centered `L²` correlations

In the proof of `lem:density:global-moment` (`paper/sections/31_density_induction_upgrade.tex`)
a fixed tail graph law has unit mixed `Lʳ` norm, `1 < r ≤ 2`, for all large primes:
bounded joint density relative to independent uniform labels and centered `L²`
correlations of size `O(p^(-1/2))` make every centered subset form small in `Lʳ`,
and the uniform-convexity criterion then gives the unit bound. The paper passes from
`L²` to `Lʳ` by interpolation. This module proves that step by truncation, which
needs no multilinear interpolation theorem:

`|E_μ ∏_{v∈S} hᵥ(zᵥ)| ≤ (ε t^(|S|(1 - r/2)) + 4^|S| D t^(1-r)) ∏_{v∈S} ‖hᵥ‖ᵣ`

for centered inputs, every `t ≥ 1`, when the `S`-marginal has density at most `D` and
centered `L²` forms are bounded by `ε`. Combined with
`Sarkozy.mixedLpBound_of_centered_tolerance`, small `ε` at fixed `D` gives a unit mixed
`Lʳ` norm, uniformly in the alphabet.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]

/-- The multilinear form of `μ` on the slots of `S`. -/
noncomputable def slotForm (μ : FiniteLaw (V → X)) (S : Finset V) (g : V → X → ℝ) : ℝ :=
  μ.expect (fun z => ∏ v ∈ S, g v (z v))

theorem centeredForm_eq_slotForm (μ : FiniteLaw (V → X)) (f : V → X → ℝ) (S : Finset V) :
    centeredForm μ f S = slotForm μ S (fun v => centeredInput (f v)) := rfl

section Truncation

variable (h : X → ℝ)

/-- The part of `h` of absolute value at most `c`. -/
noncomputable def lowPart (c : ℝ) (x : X) : ℝ := if |h x| ≤ c then h x else 0

omit [Fintype X] [Nonempty X] in
theorem abs_lowPart_le (c : ℝ) (x : X) : |lowPart h c x| ≤ |h x| := by
  unfold lowPart
  split_ifs <;> simp

omit [Fintype X] [Nonempty X] in
theorem lowPart_sq_le {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 2) (x : X) :
    lowPart h c x ^ 2 ≤ c ^ (2 - r) * |h x| ^ r := by
  unfold lowPart
  split_ifs with hx
  · have hsplit : |h x| ^ (2 : ℝ) = |h x| ^ (2 - r) * |h x| ^ r := by
      rw [← Real.rpow_add' (abs_nonneg _) (by norm_num)]
      norm_num
    have hle : |h x| ^ (2 - r) ≤ c ^ (2 - r) :=
      Real.rpow_le_rpow (abs_nonneg _) hx (by linarith)
    calc h x ^ 2 = |h x| ^ (2 : ℝ) := by rw [Real.rpow_two, sq_abs]
      _ = |h x| ^ (2 - r) * |h x| ^ r := hsplit
      _ ≤ c ^ (2 - r) * |h x| ^ r :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (abs_nonneg _) _)
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (Real.rpow_nonneg hc _) (Real.rpow_nonneg (abs_nonneg _) _)

omit [Fintype X] [Nonempty X] in
theorem abs_highPart_le {c r : ℝ} (hc : 0 < c) (hr : 1 ≤ r) (x : X) :
    |h x - lowPart h c x| ≤ c ^ (1 - r) * |h x| ^ r := by
  unfold lowPart
  split_ifs with hx
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (abs_nonneg _) _)
  · have hlt : c < |h x| := lt_of_not_ge hx
    have hpos : 0 < |h x| := hc.trans hlt
    have hsplit : |h x| = |h x| ^ (1 - r) * |h x| ^ r := by
      rw [← Real.rpow_add hpos]
      norm_num
    have hle : |h x| ^ (1 - r) ≤ c ^ (1 - r) :=
      Real.rpow_le_rpow_of_nonpos hc hlt.le (by linarith)
    rw [sub_zero]
    calc |h x| = |h x| ^ (1 - r) * |h x| ^ r := hsplit
      _ ≤ c ^ (1 - r) * |h x| ^ r :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (abs_nonneg _) _)

end Truncation

/-- Centering does not increase the second moment. -/
theorem expect_centered_sq_le (g : X → ℝ) :
    (FiniteLaw.uniform X).expect (fun x => (g x - (FiniteLaw.uniform X).expect g) ^ 2) ≤
      (FiniteLaw.uniform X).expect (fun x => g x ^ 2) := by
  rw [FiniteLaw.expect_sq_sub_mean]
  nlinarith [sq_nonneg ((FiniteLaw.uniform X).expect g)]

/-- Centering at most doubles the first absolute moment. -/
theorem expect_abs_centered_le (g : X → ℝ) :
    (FiniteLaw.uniform X).expect (fun x => |g x - (FiniteLaw.uniform X).expect g|) ≤
      2 * (FiniteLaw.uniform X).expect (fun x => |g x|) := by
  set μ := FiniteLaw.uniform X
  have hmean : |μ.expect g| ≤ μ.expect (fun x => |g x|) := μ.abs_expect_le g
  have hpt (x : X) : |g x - μ.expect g| ≤ |g x| + |μ.expect g| := abs_sub _ _
  have h := μ.expect_mono hpt
  rw [FiniteLaw.expect_add, FiniteLaw.expect_const] at h
  linarith

/-- The first absolute moment is at most the `Lʳ` norm, `r ≥ 1`. -/
theorem expect_abs_le_lpNorm {r : ℝ} (hr : 1 ≤ r) (g : X → ℝ) :
    (FiniteLaw.uniform X).expect (fun x => |g x|) ≤ (FiniteLaw.uniform X).lpNorm r g := by
  have h := (FiniteLaw.uniform X).abs_expect_le_lpNorm hr (fun x => |g x|)
  rw [FiniteLaw.lpNorm_abs] at h
  exact (le_abs_self _).trans h

/-- **Centered `Lʳ` forms from bounded density and centered `L²` bounds.** If the
`S`-marginal of `μ` has density at most `D` with respect to independent uniform labels
(stated as the first-moment bound `hdens`), and centered inputs have
`|E_μ ∏_{v∈S} gᵥ| ≤ ε ∏ ‖gᵥ‖₂`, then for `1 < r ≤ 2`, every `t ≥ 1` and centered
inputs `h`, `|E_μ ∏_{v∈S} hᵥ| ≤ (ε t^(|S|(1-r/2)) + 4^|S| D t^(1-r)) ∏ ‖hᵥ‖ᵣ`. -/
theorem slotForm_centered_lr_le (μ : FiniteLaw (V → X)) (S : Finset V) {D ε r t : ℝ}
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hr1 : 1 < r) (hr2 : r ≤ 2) (ht : 1 ≤ t)
    (hdens : ∀ g : V → X → ℝ,
      |slotForm μ S g| ≤ D * ∏ v ∈ S, (FiniteLaw.uniform X).expect (fun x => |g v x|))
    (hL2 : ∀ g : V → X → ℝ, (∀ v ∈ S, (FiniteLaw.uniform X).expect (g v) = 0) →
      |slotForm μ S g| ≤
        ε * ∏ v ∈ S, Real.sqrt ((FiniteLaw.uniform X).expect (fun x => g v x ^ 2)))
    (h : V → X → ℝ) (hc : ∀ v ∈ S, (FiniteLaw.uniform X).expect (h v) = 0) :
    |slotForm μ S h| ≤
      (ε * t ^ ((S.card : ℝ) * (1 - r / 2)) + 4 ^ S.card * D * t ^ (1 - r)) *
        ∏ v ∈ S, (FiniteLaw.uniform X).lpNorm r (h v) := by
  classical
  set U := FiniteLaw.uniform X with hUdef
  set N : V → ℝ := fun v => U.lpNorm r (h v) with hNdef
  have hN0 (v : V) : 0 ≤ N v := U.lpNorm_nonneg _ _
  have ht0 : 0 < t := by linarith
  have hcoef : 0 ≤ ε * t ^ ((S.card : ℝ) * (1 - r / 2)) + 4 ^ S.card * D * t ^ (1 - r) := by
    positivity
  by_cases hzero : ∃ v ∈ S, N v = 0
  · obtain ⟨v, hv, hNv⟩ := hzero
    have hh := FiniteLaw.uniform_function_eq_zero_of_lpNorm_eq_zero
      (by linarith : (0 : ℝ) < r) hNv
    have hform : slotForm μ S h = 0 := by
      unfold slotForm
      have hfun : (fun z : V → X => ∏ w ∈ S, h w (z w)) = fun _ => 0 := by
        funext z
        exact Finset.prod_eq_zero hv (hh _)
      rw [hfun, FiniteLaw.expect_const]
    rw [hform, abs_zero]
    exact mul_nonneg hcoef (Finset.prod_nonneg fun w _ => hN0 w)
  simp only [not_exists, not_and] at hzero
  have hNpos : ∀ v ∈ S, 0 < N v := fun v hv => lt_of_le_of_ne (hN0 v) (Ne.symm (hzero v hv))
  set c : V → ℝ := fun v => t * N v with hcdef
  set a : V → X → ℝ := fun v => lowPart (h v) (c v) with hadef
  set b : V → X → ℝ := fun v x => h v x - a v x with hbdef
  set a' : V → X → ℝ := fun v x => a v x - U.expect (a v) with ha'def
  set b' : V → X → ℝ := fun v x => b v x - U.expect (b v) with hb'def
  have hsplit : ∀ v ∈ S, ∀ x, h v x = b' v x + a' v x := by
    intro v hv x
    have hmean : U.expect (a v) + U.expect (b v) = 0 := by
      rw [← FiniteLaw.expect_add]
      have hfun : (fun x => a v x + b v x) = h v := by
        funext y
        simp only [hbdef]
        ring
      rw [hfun]
      exact hc v hv
    simp only [ha'def, hb'def, hbdef]
    linarith
  -- The moment of `h v` is `N v ^ r`.
  have hmom (v : V) : U.expect (fun x => |h v x| ^ r) = N v ^ r :=
    (U.lpNorm_rpow (by linarith) (h v)).symm
  -- Norm bounds for the pieces.
  have hb1 : ∀ v ∈ S, U.expect (fun x => |b' v x|) ≤ 2 * (t ^ (1 - r) * N v) := by
    intro v hv
    have hc0 : 0 < c v := mul_pos ht0 (hNpos v hv)
    have hpt (x : X) : |b v x| ≤ c v ^ (1 - r) * |h v x| ^ r :=
      abs_highPart_le (h v) hc0 hr1.le x
    have hE := U.expect_mono hpt
    rw [FiniteLaw.expect_const_mul, hmom] at hE
    have hval : c v ^ (1 - r) * N v ^ r = t ^ (1 - r) * N v := by
      rw [hcdef, Real.mul_rpow ht0.le (hN0 v), mul_assoc, ← Real.rpow_add (hNpos v hv)]
      norm_num
    rw [hval] at hE
    exact (expect_abs_centered_le (b v)).trans (by linarith)
  have ha1 : ∀ v ∈ S, U.expect (fun x => |a' v x|) ≤ 2 * N v := by
    intro v _
    have hpt (x : X) : |a v x| ≤ |h v x| := abs_lowPart_le (h v) (c v) x
    have hE := U.expect_mono hpt
    have hh := expect_abs_le_lpNorm hr1.le (h v)
    exact (expect_abs_centered_le (a v)).trans (by linarith)
  have ha2 : ∀ v ∈ S, Real.sqrt (U.expect (fun x => a' v x ^ 2)) ≤ t ^ (1 - r / 2) * N v := by
    intro v hv
    have hc0 : 0 ≤ c v := (mul_pos ht0 (hNpos v hv)).le
    have hpt (x : X) : a v x ^ 2 ≤ c v ^ (2 - r) * |h v x| ^ r := lowPart_sq_le (h v) hc0 hr2 x
    have hE := U.expect_mono hpt
    rw [FiniteLaw.expect_const_mul, hmom] at hE
    have e1 : c v ^ (2 - r) * N v ^ r = t ^ (2 - r) * N v ^ 2 := by
      rw [hcdef]
      simp only
      rw [Real.mul_rpow ht0.le (hN0 v), mul_assoc, ← Real.rpow_add (hNpos v hv),
        show 2 - r + r = (2 : ℝ) by ring, Real.rpow_two]
    have e2 : (t ^ (1 - r / 2) * N v) ^ 2 = t ^ (2 - r) * N v ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast (t ^ (1 - r / 2)), ← Real.rpow_mul ht0.le]
      congr 2
      push_cast
      ring
    have hval : c v ^ (2 - r) * N v ^ r = (t ^ (1 - r / 2) * N v) ^ 2 := by rw [e1, e2]
    rw [hval] at hE
    have hcen := expect_centered_sq_le (a v)
    have hle : U.expect (fun x => a' v x ^ 2) ≤ (t ^ (1 - r / 2) * N v) ^ 2 := hcen.trans hE
    calc Real.sqrt (U.expect (fun x => a' v x ^ 2)) ≤ Real.sqrt ((t ^ (1 - r / 2) * N v) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = t ^ (1 - r / 2) * N v :=
          Real.sqrt_sq (mul_nonneg (Real.rpow_nonneg ht0.le _) (hN0 v))
  -- Expansion over the subsets carrying the large parts.
  have hexpand : slotForm μ S h = ∑ B ∈ S.powerset,
      slotForm μ S (fun v => if v ∈ B then b' v else a' v) := by
    unfold slotForm
    rw [← FiniteLaw.expect_sum]
    congr 1
    funext z
    rw [Finset.prod_congr rfl (fun v hv => hsplit v hv (z v)), Finset.prod_add]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hBS := Finset.mem_powerset.mp hB
    rw [show (∏ v ∈ S, (if v ∈ B then b' v else a' v) (z v)) =
        ∏ v ∈ S, (if v ∈ B then b' v (z v) else a' v (z v)) by
      refine Finset.prod_congr rfl fun v _ => ?_
      split_ifs <;> rfl]
    rw [Finset.prod_ite]
    congr 1
    · refine Finset.prod_congr ?_ fun _ _ => rfl
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun hv => ⟨hBS hv, hv⟩, fun hv => hv.2⟩
    · refine Finset.prod_congr ?_ fun _ _ => rfl
      ext v
      simp only [Finset.mem_filter, Finset.mem_sdiff]
  set X0 := ε * t ^ ((S.card : ℝ) * (1 - r / 2)) * ∏ v ∈ S, N v with hX0
  set Y0 := 2 ^ S.card * D * t ^ (1 - r) * ∏ v ∈ S, N v with hY0
  have hprodN : 0 ≤ ∏ v ∈ S, N v := Finset.prod_nonneg fun v _ => hN0 v
  have hY0nn : 0 ≤ Y0 := by positivity
  have htr : t ^ (1 - r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
  have hterm : ∀ B ∈ S.powerset,
      |slotForm μ S (fun v => if v ∈ B then b' v else a' v)| ≤ if B = ∅ then X0 else Y0 := by
    intro B hB
    have hBS := Finset.mem_powerset.mp hB
    split_ifs with hBe
    · subst hBe
      simp only [Finset.notMem_empty, ↓reduceIte]
      have hcen : ∀ v ∈ S, U.expect (a' v) = 0 := by
        intro v _
        simp only [ha'def]
        rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self]
      refine (hL2 a' hcen).trans ?_
      have hp := Finset.prod_le_prod₀ (fun v _ => Real.sqrt_nonneg _) ha2
      rw [Finset.prod_mul_distrib, Finset.prod_const] at hp
      have hpow : (t ^ (1 - r / 2)) ^ S.card = t ^ ((S.card : ℝ) * (1 - r / 2)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le, mul_comm]
      rw [hpow] at hp
      rw [hX0, mul_assoc]
      exact mul_le_mul_of_nonneg_left hp hε
    · refine (hdens _).trans ?_
      have hfac : ∀ v ∈ S, U.expect (fun x => |(if v ∈ B then b' v else a' v) x|) ≤
          (if v ∈ B then 2 * t ^ (1 - r) else 2) * N v := by
        intro v hv
        split_ifs with hvB
        · simpa only [mul_assoc] using hb1 v hv
        · exact ha1 v hv
      have hp := Finset.prod_le_prod₀ (fun v _ => U.expect_nonneg fun x => abs_nonneg _) hfac
      rw [Finset.prod_mul_distrib] at hp
      have hconst : ∏ v ∈ S, (if v ∈ B then 2 * t ^ (1 - r) else (2 : ℝ)) ≤
          2 ^ S.card * t ^ (1 - r) := by
        rw [Finset.prod_ite]
        have hB' : (S.filter fun v => v ∈ B) = B := by
          ext v
          simp only [Finset.mem_filter]
          exact ⟨fun hv => hv.2, fun hv => ⟨hBS hv, hv⟩⟩
        rw [hB', Finset.prod_const, Finset.prod_const, mul_pow]
        have hcard : B.card + (S.filter fun v => v ∉ B).card = S.card := by
          have hc := Finset.card_filter_add_card_filter_not (s := S) (fun v => v ∈ B)
          rw [hB'] at hc
          exact hc
        have hBpos : 1 ≤ B.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hBe)
        have htpow : (t ^ (1 - r)) ^ B.card ≤ t ^ (1 - r) :=
          pow_le_of_le_one (Real.rpow_nonneg ht0.le _) htr (by omega)
        calc 2 ^ B.card * (t ^ (1 - r)) ^ B.card * 2 ^ (S.filter fun v => v ∉ B).card =
              2 ^ S.card * (t ^ (1 - r)) ^ B.card := by
                rw [← hcard, pow_add]
                ring
          _ ≤ 2 ^ S.card * t ^ (1 - r) :=
                mul_le_mul_of_nonneg_left htpow (by positivity)
      calc D * ∏ v ∈ S, U.expect (fun x => |(if v ∈ B then b' v else a' v) x|) ≤
            D * ((∏ v ∈ S, (if v ∈ B then 2 * t ^ (1 - r) else 2)) * ∏ v ∈ S, N v) :=
            mul_le_mul_of_nonneg_left hp hD
        _ ≤ D * ((2 ^ S.card * t ^ (1 - r)) * ∏ v ∈ S, N v) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hconst hprodN) hD
        _ = Y0 := by rw [hY0]; ring
  rw [hexpand]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have hempty : (S.powerset.filter fun B => B = ∅) = {∅} := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    exact ⟨fun hB => hB.2, fun hB => ⟨hB ▸ Finset.empty_subset S, hB⟩⟩
  rw [hempty, Finset.card_singleton, one_smul, nsmul_eq_mul]
  have hcardle : ((S.powerset.filter fun B => ¬B = ∅).card : ℝ) ≤ 2 ^ S.card := by
    have h1 : (S.powerset.filter fun B => ¬B = ∅).card ≤ S.powerset.card :=
      Finset.card_filter_le _ _
    rw [Finset.card_powerset] at h1
    exact_mod_cast h1
  have hfour : (4 : ℝ) ^ S.card = 2 ^ S.card * 2 ^ S.card := by
    rw [← mul_pow]
    norm_num
  calc X0 + ((S.powerset.filter fun B => ¬B = ∅).card : ℝ) * Y0 ≤ X0 + 2 ^ S.card * Y0 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcardle hY0nn)
    _ = (ε * t ^ ((S.card : ℝ) * (1 - r / 2)) + 4 ^ S.card * D * t ^ (1 - r)) *
          ∏ v ∈ S, N v := by
        rw [hX0, hY0, hfour]
        ring

/-- **Unit mixed `Lʳ` norm from bounded density and small centered `L²` forms.** -/
theorem mixedLpBound_of_density_and_centeredL2 [Nonempty V] (μ : FiniteLaw (V → X))
    (hm : HasUniformMarginals μ) {r D ε t : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2) (hD : 0 ≤ D)
    (hε : 0 ≤ ε) (ht : 1 ≤ t)
    (hsmall : ε * t ^ ((Fintype.card V : ℝ) * (1 - r / 2)) +
      4 ^ Fintype.card V * D * t ^ (1 - r) ≤ centeredTolerance V r)
    (hdens : ∀ S ∈ centeredSets V, ∀ g : V → X → ℝ,
      |slotForm μ S g| ≤ D * ∏ v ∈ S, (FiniteLaw.uniform X).expect (fun x => |g v x|))
    (hL2 : ∀ S ∈ centeredSets V, ∀ g : V → X → ℝ,
      (∀ v ∈ S, (FiniteLaw.uniform X).expect (g v) = 0) →
      |slotForm μ S g| ≤
        ε * ∏ v ∈ S, Real.sqrt ((FiniteLaw.uniform X).expect (fun x => g v x ^ 2))) :
    MixedLpBound μ r 1 := by
  apply mixedLpBound_of_centered_tolerance μ hm hr1 hr2
  intro f S hS
  rw [centeredForm_eq_slotForm]
  have hcen : ∀ v ∈ S, (FiniteLaw.uniform X).expect (centeredInput (f v)) = 0 := by
    intro v _
    unfold centeredInput
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self]
  have h := slotForm_centered_lr_le μ S hD hε hr1 hr2 ht (hdens S hS) (hL2 S hS) _ hcen
  refine h.trans (mul_le_mul_of_nonneg_right ?_
    (Finset.prod_nonneg fun v _ => (FiniteLaw.uniform X).lpNorm_nonneg _ _))
  have hcard : S.card ≤ Fintype.card V := Finset.card_le_univ S
  have ht0 : 0 < t := by linarith
  have h1 : t ^ ((S.card : ℝ) * (1 - r / 2)) ≤ t ^ ((Fintype.card V : ℝ) * (1 - r / 2)) :=
    Real.rpow_le_rpow_of_exponent_le ht
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by linarith))
  have h2 : (4 : ℝ) ^ S.card ≤ 4 ^ Fintype.card V := pow_le_pow_right₀ (by norm_num) hcard
  have htr : 0 ≤ t ^ (1 - r) := Real.rpow_nonneg ht0.le _
  calc ε * t ^ ((S.card : ℝ) * (1 - r / 2)) + 4 ^ S.card * D * t ^ (1 - r) ≤
        ε * t ^ ((Fintype.card V : ℝ) * (1 - r / 2)) + 4 ^ Fintype.card V * D * t ^ (1 - r) := by
        gcongr
    _ ≤ centeredTolerance V r := hsmall

/-- **Eventual unit mixed `Lʳ` norm.** A family of laws with uniform marginals, a common
density bound `D` on every centered set, and centered `L²` constants `ε n → 0` has unit
mixed `Lʳ` norm for all large `n`. This is the form in which the proof of
`lem:density:global-moment` uses the tail graph laws. -/
theorem eventually_mixedLpBound_of_density_and_centeredL2 [Nonempty V]
    (μ : ℕ → FiniteLaw (V → X)) (hm : ∀ n, HasUniformMarginals (μ n)) {r D : ℝ}
    (hr1 : 1 < r) (hr2 : r ≤ 2) (hD : 0 ≤ D) (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hdens : ∀ n, ∀ S ∈ centeredSets V, ∀ g : V → X → ℝ,
      |slotForm (μ n) S g| ≤ D * ∏ v ∈ S, (FiniteLaw.uniform X).expect (fun x => |g v x|))
    (hL2 : ∀ n, ∀ S ∈ centeredSets V, ∀ g : V → X → ℝ,
      (∀ v ∈ S, (FiniteLaw.uniform X).expect (g v) = 0) →
      |slotForm (μ n) S g| ≤
        ε n * ∏ v ∈ S, Real.sqrt ((FiniteLaw.uniform X).expect (fun x => g v x ^ 2))) :
    ∀ᶠ n in Filter.atTop, MixedLpBound (μ n) r 1 := by
  set τ := centeredTolerance V r
  have hτ : 0 < τ := centeredTolerance_pos hr1
  set M : ℝ := 4 ^ Fintype.card V * D
  have hM : 0 ≤ M := by positivity
  -- A scale `t ≥ 1` with `M t^(1-r) ≤ τ/2`.
  have hlim : Filter.Tendsto (fun t : ℝ => M * t ^ (1 - r)) Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < r - 1)).const_mul M
    simpa only [neg_sub, mul_zero] using h
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < τ / 2)))
  set t : ℝ := max 1 t₀
  have ht : 1 ≤ t := le_max_left _ _
  have hMt : M * t ^ (1 - r) < τ / 2 := ht₀ t (le_max_right _ _)
  set P : ℝ := t ^ ((Fintype.card V : ℝ) * (1 - r / 2))
  have hP : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  have hεP : Filter.Tendsto (fun n => ε n * P) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using hε.mul_const P
  filter_upwards [hεP.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < τ / 2))] with n hn
  apply mixedLpBound_of_density_and_centeredL2 (μ n) (hm n) hr1 hr2 hD (hε0 n) ht _
    (hdens n) (hL2 n)
  change ε n * P + M * t ^ (1 - r) ≤ τ
  linarith

end Sarkozy
