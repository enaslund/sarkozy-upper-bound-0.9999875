module

public import Sarkozy.TraceMixing.PhiBound

/-!
# One vertex given the others (`lem:graphs:vertex`(a), (b))

`paper/sections/12_labellings.tex`, `lem:graphs:vertex`, over any finite field `F` with `q`
elements.

* (a) is `graphLaw_weight_affine` (invariance under `z ↦ (α z_w + β)_w`, `χ(α) = 1`) and
  `srcWeight_graphSlot` (uniform one-vertex marginals), in `Slot.lean`.
* (b) `condMatrix_graphSlot`: conditionally on `z_{W∖{w}}`, the label `z_w` is uniform on its
  admissible set `Φ_w` (`slotAdmissible`); `card_slotAdmissible_ge`:
  `|Φ_w| ≥ q 2^{-d_w}(1 - e_{d_w}(q, n))` for `|W| ≤ n`; `condDensity_graphSlot_le`: the
  conditional density with respect to the uniform law is at most `2^{d_w}/(1 - e_{d_w}(q, n))`;
  `condMatrix_slot_of_density`: under a law `m` on `Inj(G)` whose density with respect to `λ`
  lies in `[c, Rc]`, each value of `z_w` has conditional probability at most `R/|Φ_w|`.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W)

/-- The admissible labels `Φ_w` of `w` given the other labels `r`. -/
noncomputable def slotAdmissible (w : W) (r : {u // u ≠ w} → F) : Finset F :=
  univ.filter fun x => (Equiv.funSplitAt w F).symm (x, r) ∈ injLabellings F G

variable (hne : (injLabellings F G).Nonempty)

theorem graphSlot_weight (w : W) (x : F) (r : {u // u ≠ w} → F) :
    (slotJoint (graphLaw G hne) w).weight (x, r) =
      if x ∈ slotAdmissible G w r then 1 / ((injLabellings F G).card : ℝ) else 0 := by
  rw [slotJoint_weight]
  unfold graphLaw slotAdmissible
  simp only [mem_filter, mem_univ, true_and]

theorem tgtWeight_graphSlot (w : W) (r : {u // u ≠ w} → F) :
    tgtWeight (slotJoint (graphLaw G hne) w) r =
      1 / ((injLabellings F G).card : ℝ) * (slotAdmissible G w r).card := by
  have hfilt : univ.filter (fun x => x ∈ slotAdmissible G w r) = slotAdmissible G w r := by
    ext x
    simp
  unfold tgtWeight
  simp only [graphSlot_weight G hne]
  rw [← Finset.sum_filter, hfilt, sum_const, nsmul_eq_mul, mul_comm]

/-- **`lem:graphs:vertex`(b): `z_w` is uniform on `Φ_w` given the other labels.** -/
theorem condMatrix_graphSlot (w : W) (r : {u // u ≠ w} → F)
    (hr : tgtWeight (slotJoint (graphLaw G hne) w) r ≠ 0) (x : F) :
    condMatrix (slotJoint (graphLaw G hne) w) r x =
      (if x ∈ slotAdmissible G w r then 1 else 0) / ((slotAdmissible G w r).card : ℝ) := by
  have hc0 : (1 / ((injLabellings F G).card : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
    positivity
  unfold condMatrix
  rw [ite_eq_right hr, graphSlot_weight G hne, tgtWeight_graphSlot G hne]
  split_ifs
  · rw [div_mul_eq_div_div, div_self hc0]
  · simp

/-- **`|Φ_w| ≥ q 2^{-d_w}(1 - e_{d_w}(q, n))`** on the support, for `|W| ≤ n`. -/
theorem card_slotAdmissible_ge (hW : WeilBound F) (w : W) (r : {u // u ≠ w} → F)
    (hr : tgtWeight (slotJoint (graphLaw G hne) w) r ≠ 0) {n : ℕ} (hn : Fintype.card W ≤ n)
    {e : ℝ} (he : coarseErr (Fintype.card F) (degree G w) n ≤ e) :
    (Fintype.card F : ℝ) / 2 ^ degree G w * (1 - e) ≤ (slotAdmissible G w r).card := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < 2 ^ degree G w := pow_pos two_pos _
  have h := card_admissible_slot_ge hW G hne w r hr
  have hle : lowerErr (Fintype.card F) (degree G w) (Fintype.card W - 1) ≤ e :=
    (lowerErr_le_coarseErr hq1 _ _).trans ((coarseErr_mono hq0 le_rfl (by omega)).trans he)
  have h1 : (Fintype.card F : ℝ) * (1 - e) ≤
      (Fintype.card F : ℝ) * (1 - lowerErr (Fintype.card F) (degree G w) (Fintype.card W - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hq0.le
  have h2 := h1.trans h
  unfold slotAdmissible
  rw [div_mul_eq_mul_div, div_le_iff₀ hpow]
  linarith

/-- **The conditional density of `z_w` with respect to the uniform law is at most
`2^{d_w}/(1 - e_{d_w}(q, n))`.** -/
theorem condDensity_graphSlot_le (hW : WeilBound F) (w : W) (r : {u // u ≠ w} → F)
    (hr : tgtWeight (slotJoint (graphLaw G hne) w) r ≠ 0) {n : ℕ} (hn : Fintype.card W ≤ n)
    {e : ℝ} (he1 : e < 1) (he : coarseErr (Fintype.card F) (degree G w) n ≤ e) (x : F) :
    (Fintype.card F : ℝ) * condMatrix (slotJoint (graphLaw G hne) w) r x ≤
      2 ^ degree G w / (1 - e) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have he1' : 0 < 1 - e := by linarith
  have hpow : (0 : ℝ) < 2 ^ degree G w := pow_pos two_pos _
  have hcard := card_slotAdmissible_ge G hne hW w r hr hn he
  have hpos : (0 : ℝ) < (slotAdmissible G w r).card :=
    lt_of_lt_of_le (mul_pos (div_pos hq0 hpow) he1') hcard
  rw [condMatrix_graphSlot G hne w r hr x]
  have h01 : (if x ∈ slotAdmissible G w r then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have h00 : (0 : ℝ) ≤ if x ∈ slotAdmissible G w r then (1 : ℝ) else 0 := by
    split_ifs <;> norm_num
  calc (Fintype.card F : ℝ) * ((if x ∈ slotAdmissible G w r then 1 else 0) /
        ((slotAdmissible G w r).card : ℝ))
      ≤ (Fintype.card F : ℝ) * (1 / ((slotAdmissible G w r).card : ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h01 hpos.le) hq0.le
    _ ≤ 2 ^ degree G w / (1 - e) := by
        rw [mul_one_div, div_le_div_iff₀ hpos he1']
        rw [div_mul_eq_mul_div, div_le_iff₀ hpow] at hcard
        linarith

/-- **`lem:graphs:vertex`(b), the perturbed law**: if `m` is a law on `Inj(G)` with density in
`[c, Rc]` with respect to `λ`, then given the other labels each value of `z_w` has
conditional probability at most `R/|Φ_w|`. -/
theorem condMatrix_slot_of_density (m : FiniteLaw (W → F))
    (hm0 : ∀ z, z ∉ injLabellings F G → m.weight z = 0) {c R : ℝ} (hc : 0 < c)
    (hm : ∀ z ∈ injLabellings F G, c * (graphLaw G hne).weight z ≤ m.weight z ∧
      m.weight z ≤ R * c * (graphLaw G hne).weight z)
    (w : W) (r : {u // u ≠ w} → F) (hr : tgtWeight (slotJoint m w) r ≠ 0) (x : F) :
    condMatrix (slotJoint m w) r x ≤ R / ((slotAdmissible G w r).card : ℝ) := by
  set c₀ : ℝ := 1 / ((injLabellings F G).card : ℝ) with hc₀
  have hc₀0 : 0 < c₀ := by
    have : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
    positivity
  set e := Equiv.funSplitAt w F
  have hlam (x' : F) : (graphLaw G hne).weight (e.symm (x', r)) =
      if x' ∈ slotAdmissible G w r then c₀ else 0 := by
    have := graphSlot_weight G hne w x' r
    rwa [slotJoint_weight] at this
  have hmw (x' : F) : (slotJoint m w).weight (x', r) = m.weight (e.symm (x', r)) :=
    slotJoint_weight m w (x', r)
  -- the bounds on the weights
  have hup (x' : F) : (slotJoint m w).weight (x', r) ≤
      R * c * (if x' ∈ slotAdmissible G w r then c₀ else 0) := by
    rw [hmw, ← hlam]
    by_cases hz : e.symm (x', r) ∈ injLabellings F G
    · exact (hm _ hz).2
    · rw [hm0 _ hz]
      have : (graphLaw G hne).weight (e.symm (x', r)) = 0 := by
        unfold graphLaw
        simp only []
        rw [ite_eq_right hz]
      rw [this, mul_zero]
  have hlo (x' : F) : c * (if x' ∈ slotAdmissible G w r then c₀ else 0) ≤
      (slotJoint m w).weight (x', r) := by
    rw [hmw, ← hlam]
    by_cases hz : e.symm (x', r) ∈ injLabellings F G
    · exact (hm _ hz).1
    · have : (graphLaw G hne).weight (e.symm (x', r)) = 0 := by
        unfold graphLaw
        simp only []
        rw [ite_eq_right hz]
      rw [this, mul_zero]
      exact m.nonneg _
  have htgt : c * c₀ * (slotAdmissible G w r).card ≤ tgtWeight (slotJoint m w) r := by
    unfold tgtWeight
    calc c * c₀ * ((slotAdmissible G w r).card : ℝ)
        = ∑ x', c * (if x' ∈ slotAdmissible G w r then c₀ else 0) := by
          simp only [mul_ite, mul_zero]
          rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
          have : (univ.filter fun x' => x' ∈ slotAdmissible G w r) = slotAdmissible G w r := by
            ext y
            simp
          rw [this]
          ring
      _ ≤ ∑ x', (slotJoint m w).weight (x', r) := Finset.sum_le_sum (fun x' _ => hlo x')
  have htgt0 : 0 < tgtWeight (slotJoint m w) r :=
    lt_of_le_of_ne (tgtWeight_nonneg _ _) (Ne.symm hr)
  -- `Φ_w` is nonempty
  have hΦ : 0 < ((slotAdmissible G w r).card : ℝ) := by
    by_contra h
    push Not at h
    have h0 : ((slotAdmissible G w r).card : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    apply hr
    unfold tgtWeight
    apply Finset.sum_eq_zero
    intro x' _
    have hx' : x' ∉ slotAdmissible G w r := by
      intro hmem
      have : (slotAdmissible G w r).card ≠ 0 := card_ne_zero.mpr ⟨x', hmem⟩
      exact this (by exact_mod_cast h0)
    have := hup x'
    rw [ite_eq_right hx', mul_zero] at this
    exact le_antisymm this ((slotJoint m w).nonneg _)
  have hR0 : 0 ≤ R := by
    rcases id hne with ⟨z, hz⟩
    have h := hm z hz
    have hlamz : (graphLaw G hne).weight z = c₀ := by
      unfold graphLaw
      simp only []
      rw [ite_eq_left hz]
    rw [hlamz] at h
    have h1 : c * c₀ ≤ R * c * c₀ := h.1.trans h.2
    have h2 : 0 < c * c₀ := mul_pos hc hc₀0
    nlinarith
  unfold condMatrix
  rw [ite_eq_right hr, div_le_div_iff₀ htgt0 hΦ]
  have hRc : 0 ≤ R * c * c₀ := mul_nonneg (mul_nonneg hR0 hc.le) hc₀0.le
  have h1 : (slotJoint m w).weight (x, r) ≤ R * c * c₀ := by
    have := hup x
    split_ifs at this
    · exact this
    · rw [mul_zero] at this
      linarith
  calc (slotJoint m w).weight (x, r) * ((slotAdmissible G w r).card : ℝ)
      ≤ R * c * c₀ * ((slotAdmissible G w r).card : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hΦ.le
    _ = R * (c * c₀ * ((slotAdmissible G w r).card : ℝ)) := by ring
    _ ≤ R * tgtWeight (slotJoint m w) r := mul_le_mul_of_nonneg_left htgt hR0

end Sarkozy.TraceMixing
