module

public import Mathlib

/-!
# Distinct choices (`lem:distinct-choice`)

`paper/sections/22_variance.tex`. For weights `0 ≤ w_B ≤ M` on a finite set `s` of blocks with
total weight at least `Σ`, the `r`-th elementary symmetric sum satisfies
`e_r(w) = ∑_{Z ⊆ s, |Z| = r} ∏_{B∈Z} w_B ≥ (1/r!) ∏_{j<r} (Σ - jM)_+` (`esym_ge`). The proof is the
paper's: count ordered tuples, and note that after `j` choices the remaining blocks have total
weight at least `Σ - jM`. Here it is organized by the identity
`(r + 1) e_{r+1}(s) = ∑_{B∈s} w_B e_r(s∖{B})` (`esym_succ_mul`).

* `distinct_choice_piece`: part (a) for one piece `i`. The blocks of the piece outside `X` (`m_i`
  of its blocks lie in `X`) carry weights `c_i b_B^{-1} ≤ c_i/X_i` with total at least
  `c_i(Σ_i - m_i/X_i)`, so their `r_i`-subsets have weight at least
  `(c_i^{r_i}/r_i!) ∏_{j<r_i} (Σ_i - (m_i + j)/X_i)_+`. The product over pieces in (a) is the
  independence of the choices in different pieces; it is not formalized here.
* `distinct_choice_mixed`: part (b), for the `k`-subsets of the blocks of the pieces of `Ps` outside
  `X`, with `𝔪(c) = ∑ c_i Σ_i`, `𝔲(c) = max c_i/X_i` and `𝔢_m(c) = ∑ m_i c_i/X_i`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DistinctChoice

variable {β : Type*} [DecidableEq β]

/-- `e_r(w) = ∑_{Z ⊆ s, |Z| = r} ∏_{B∈Z} w_B`. -/
noncomputable def esym (s : Finset β) (w : β → ℝ) (r : ℕ) : ℝ :=
  ∑ Z ∈ s.powersetCard r, ∏ B ∈ Z, w B

omit [DecidableEq β] in
theorem esym_zero (s : Finset β) (w : β → ℝ) : esym s w 0 = 1 := by
  simp [esym]

/-- `(r + 1) e_{r+1}(s) = ∑_{B∈s} w_B e_r(s ∖ {B})`. -/
theorem esym_succ_mul (s : Finset β) (w : β → ℝ) (r : ℕ) :
    ((r : ℝ) + 1) * esym s w (r + 1) = ∑ B ∈ s, w B * esym (s.erase B) w r := by
  unfold esym
  -- left side: each `(r+1)`-set counted once for each of its elements
  have hL : ((r : ℝ) + 1) * ∑ Z ∈ s.powersetCard (r + 1), ∏ B ∈ Z, w B =
      ∑ Z ∈ s.powersetCard (r + 1), ∑ _B ∈ Z, ∏ C ∈ Z, w C := by
    rw [mul_sum]
    refine sum_congr rfl fun Z hZ => ?_
    rw [sum_const, (mem_powersetCard.mp hZ).2, nsmul_eq_mul]
    push_cast
    ring
  have hR : ∑ B ∈ s, w B * ∑ Z ∈ (s.erase B).powersetCard r, ∏ C ∈ Z, w C =
      ∑ B ∈ s, ∑ Z ∈ (s.erase B).powersetCard r, ∏ C ∈ insert B Z, w C := by
    refine sum_congr rfl fun B _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun Z hZ => ?_
    have hBZ : B ∉ Z := fun h => by
      have := (mem_powersetCard.mp hZ).1 h
      simp at this
    rw [prod_insert hBZ]
  rw [hL, hR, sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2, x.1.erase x.2⟩) (fun y _ => ⟨insert y.1 y.2, y.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨Z, B⟩ h
    simp only [mem_sigma, mem_powersetCard] at h ⊢
    obtain ⟨⟨hZs, hZc⟩, hBZ⟩ := h
    refine ⟨hZs hBZ, erase_subset_erase B hZs, ?_⟩
    rw [card_erase_of_mem hBZ, hZc]
    rfl
  · rintro ⟨B, Z⟩ h
    simp only [mem_sigma, mem_powersetCard] at h ⊢
    obtain ⟨hBs, hZs, hZc⟩ := h
    have hBZ : B ∉ Z := fun hb => by
      have := hZs hb
      simp at this
    refine ⟨⟨insert_subset hBs (hZs.trans (erase_subset B s)), ?_⟩, mem_insert_self B Z⟩
    rw [card_insert_of_notMem hBZ, hZc]
  · rintro ⟨Z, B⟩ h
    simp only [mem_sigma] at h
    simp only [insert_erase h.2]
  · rintro ⟨B, Z⟩ h
    simp only [mem_sigma, mem_powersetCard] at h
    have hBZ : B ∉ Z := fun hb => by
      have := h.2.1 hb
      simp at this
    simp only [erase_insert hBZ]
  · rintro ⟨Z, B⟩ h
    simp only [mem_sigma] at h
    simp only [insert_erase h.2]

omit [DecidableEq β] in
theorem esym_nonneg (s : Finset β) {w : β → ℝ} (hw : ∀ B ∈ s, 0 ≤ w B) (r : ℕ) :
    0 ≤ esym s w r :=
  sum_nonneg fun _ hZ => prod_nonneg fun B hB => hw B ((mem_powersetCard.mp hZ).1 hB)

/-- `∏_{j<r} (S - jM)_+`. -/
noncomputable def fallingPos (S M : ℝ) (r : ℕ) : ℝ := ∏ j ∈ range r, max 0 (S - j * M)

theorem fallingPos_nonneg (S M : ℝ) (r : ℕ) : 0 ≤ fallingPos S M r :=
  prod_nonneg fun _ _ => le_max_left _ _

theorem fallingPos_mono {S S' : ℝ} (h : S ≤ S') (M : ℝ) (r : ℕ) :
    fallingPos S M r ≤ fallingPos S' M r :=
  prod_le_prod₀ (fun _ _ => le_max_left _ _) fun j _ => max_le_max le_rfl (by linarith)

/-- `(S)_+ ∏_{j<r} (S - (j+1)M)_+ = ∏_{j<r+1} (S - jM)_+`. -/
theorem fallingPos_succ (S M : ℝ) (r : ℕ) :
    fallingPos S M (r + 1) = max 0 S * fallingPos (S - M) M r := by
  unfold fallingPos
  rw [prod_range_succ']
  simp only [Nat.cast_zero, zero_mul, sub_zero, Nat.cast_succ]
  rw [mul_comm]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  congr 1
  ring

/-- **The core bound of `lem:distinct-choice`**: for `0 ≤ w_B ≤ M` and `∑_{B∈s} w_B ≥ S`,
`e_r(w) ≥ (1/r!) ∏_{j<r} (S - jM)_+`. -/
theorem esym_ge {M : ℝ} :
    ∀ (r : ℕ) (s : Finset β) (w : β → ℝ) (S : ℝ), (∀ B ∈ s, 0 ≤ w B ∧ w B ≤ M) →
      S ≤ ∑ B ∈ s, w B → fallingPos S M r / r.factorial ≤ esym s w r
  | 0, s, w, S, _, _ => by simp [fallingPos, esym_zero]
  | r + 1, s, w, S, hw, hS => by
    have hw0 : ∀ B ∈ s, 0 ≤ w B := fun B hB => (hw B hB).1
    -- each `e_r(s ∖ {B})` is at least `fallingPos (S - M) M r / r!`
    have hstep : ∀ B ∈ s, fallingPos (S - M) M r / r.factorial ≤ esym (s.erase B) w r := by
      intro B hB
      refine esym_ge r (s.erase B) w (S - M) (fun C hC => hw C (mem_of_mem_erase hC)) ?_
      have := sum_erase_add s w hB
      linarith [(hw B hB).2]
    have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    have hsum : (∑ B ∈ s, w B) * (fallingPos (S - M) M r / r.factorial) ≤
        ((r : ℝ) + 1) * esym s w (r + 1) := by
      rw [esym_succ_mul, sum_mul]
      exact sum_le_sum fun B hB => mul_le_mul_of_nonneg_left (hstep B hB) (hw0 B hB)
    have hS0 : 0 ≤ ∑ B ∈ s, w B := sum_nonneg hw0
    have hmax : max 0 S ≤ ∑ B ∈ s, w B := max_le hS0 hS
    have hF := fallingPos_nonneg (S - M) M r
    rw [fallingPos_succ, Nat.factorial_succ]
    push_cast
    have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc max 0 S * fallingPos (S - M) M r
        ≤ (∑ B ∈ s, w B) * fallingPos (S - M) M r := mul_le_mul_of_nonneg_right hmax hF
      _ = (∑ B ∈ s, w B) * (fallingPos (S - M) M r / r.factorial) * r.factorial := by
          field_simp
      _ ≤ ((r : ℝ) + 1) * esym s w (r + 1) * r.factorial :=
          mul_le_mul_of_nonneg_right hsum hfac.le
      _ = esym s w (r + 1) * (((r : ℝ) + 1) * r.factorial) := by ring


/-- The removed blocks: their weights total at most `m/X` when each is at most `1/X`. -/
theorem sum_filter_not_ge (s X : Finset β) (w : β → ℝ) {Xi Sig : ℝ}
    (hw : ∀ B ∈ s, w B ≤ 1 / Xi) (hSig : Sig ≤ ∑ B ∈ s, w B) :
    Sig - ((s.filter (fun B => B ∈ X)).card : ℝ) / Xi ≤ ∑ B ∈ s.filter (fun B => B ∉ X), w B := by
  have hsplit := sum_filter_add_sum_filter_not s (fun B => B ∈ X) w
  have hle : ∑ B ∈ s.filter (fun B => B ∈ X), w B ≤
      ((s.filter (fun B => B ∈ X)).card : ℝ) / Xi := by
    calc ∑ B ∈ s.filter (fun B => B ∈ X), w B ≤ ∑ _B ∈ s.filter (fun B => B ∈ X), 1 / Xi :=
          sum_le_sum fun B hB => hw B (mem_filter.mp hB).1
      _ = ((s.filter (fun B => B ∈ X)).card : ℝ) / Xi := by rw [sum_const, nsmul_eq_mul]; ring
  linarith

/-- **`lem:distinct-choice`(a), one piece**: the `r`-subsets `Z` of the blocks of a piece outside
`X` satisfy `∑_Z ∏_{B∈Z} c b_B^{-1} ≥ (c^r/r!) ∏_{j<r} (Σ - (m + j)/X)_+`, where `m` is the
number of blocks of the piece in `X`, `b_B^{-1} ≤ 1/X` and `∑_{piece} b_B^{-1} ≥ Σ`. -/
theorem distinct_choice_piece (s X : Finset β) (w : β → ℝ) {c Sig Xi : ℝ} (hc : 0 ≤ c)
    (hXi : 0 < Xi) (hw : ∀ B ∈ s, 0 ≤ w B ∧ w B ≤ 1 / Xi) (hSig : Sig ≤ ∑ B ∈ s, w B) (r : ℕ) :
    c ^ r / r.factorial *
        ∏ j ∈ range r, max 0 (Sig - (((s.filter (fun B => B ∈ X)).card : ℝ) + j) / Xi) ≤
      esym (s.filter (fun B => B ∉ X)) (fun B => c * w B) r := by
  set m : ℝ := ((s.filter (fun B => B ∈ X)).card : ℝ)
  have htot := sum_filter_not_ge s X w (fun B hB => (hw B hB).2) hSig
  have h := esym_ge (M := c / Xi) r (s.filter (fun B => B ∉ X)) (fun B => c * w B) (c * (Sig - m / Xi))
    (fun B hB => by
      have hwB := hw B (mem_filter.mp hB).1
      refine ⟨mul_nonneg hc hwB.1, ?_⟩
      calc c * w B ≤ c * (1 / Xi) := mul_le_mul_of_nonneg_left hwB.2 hc
        _ = c / Xi := by ring)
    (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left htot hc)
  have hfp : fallingPos (c * (Sig - m / Xi)) (c / Xi) r =
      c ^ r * ∏ j ∈ range r, max 0 (Sig - (m + j) / Xi) := by
    unfold fallingPos
    have e : ∀ j ∈ range r, max 0 (c * (Sig - m / Xi) - (j : ℝ) * (c / Xi)) =
        c * max 0 (Sig - (m + j) / Xi) := by
      intro j _
      rw [mul_max_of_nonneg _ _ hc, mul_zero]
      congr 1
      field_simp
      ring
    rw [prod_congr rfl e, prod_mul_distrib, prod_const, card_range]
  rw [hfp] at h
  calc c ^ r / r.factorial * ∏ j ∈ range r, max 0 (Sig - (m + j) / Xi)
      = (c ^ r * ∏ j ∈ range r, max 0 (Sig - (m + j) / Xi)) / r.factorial := by ring
    _ ≤ esym (s.filter (fun B => B ∉ X)) (fun B => c * w B) r := h

/-- **`lem:distinct-choice`(b)**: the `k`-subsets of the blocks of the pieces of `Ps` outside `X`
satisfy `∑_Z ∏_{B∈Z} c_{i(B)} b_B^{-1} ≥ (1/k!) ∏_{j<k} [𝔪(c) - 𝔢_m(c) - j 𝔲(c)]_+`, where
`𝔪(c) = ∑_{i∈𝒫} c_i Σ_i`, `𝔢_m(c) = ∑_{i∈𝒫} m_i c_i/X_i` and `c_i/X_i ≤ 𝔲(c)` for `i ∈ 𝒫` (`Ps` in Lean). -/
theorem distinct_choice_mixed {I : Type*} [DecidableEq I] (piece : β → I) (Ps : Finset I)
    (blocks X : Finset β) (w : β → ℝ) (c Sig Xi : I → ℝ) (u : ℝ)
    (hc : ∀ i ∈ Ps, 0 ≤ c i)
    (hw : ∀ B ∈ blocks, 0 ≤ w B ∧ w B ≤ 1 / Xi (piece B))
    (hSig : ∀ i ∈ Ps, Sig i ≤ ∑ B ∈ blocks.filter (fun B => piece B = i), w B)
    (hu : ∀ i ∈ Ps, c i / Xi i ≤ u) (k : ℕ) :
    fallingPos (∑ i ∈ Ps, c i * Sig i - ∑ i ∈ Ps,
        (((blocks.filter (fun B => piece B = i)).filter (fun B => B ∈ X)).card : ℝ) * c i / Xi i)
        u k / k.factorial ≤
      esym ((blocks.filter (fun B => piece B ∈ Ps)).filter (fun B => B ∉ X))
        (fun B => c (piece B) * w B) k := by
  set S := (blocks.filter (fun B => piece B ∈ Ps)).filter (fun B => B ∉ X)
  refine esym_ge k S _ _ (fun B hB => ?_) ?_
  · have hB' := mem_filter.mp hB
    have hBb := (mem_filter.mp hB'.1).1
    have hBP := (mem_filter.mp hB'.1).2
    have hwB := hw B hBb
    refine ⟨mul_nonneg (hc _ hBP) hwB.1, ?_⟩
    calc c (piece B) * w B ≤ c (piece B) * (1 / Xi (piece B)) :=
          mul_le_mul_of_nonneg_left hwB.2 (hc _ hBP)
      _ = c (piece B) / Xi (piece B) := by ring
      _ ≤ u := hu _ hBP
  · -- regroup the total weight by pieces
    have hmaps : ∀ B ∈ S, piece B ∈ Ps := fun B hB => (mem_filter.mp (mem_filter.mp hB).1).2
    rw [← sum_fiberwise_of_maps_to hmaps]
    rw [← sum_sub_distrib]
    refine sum_le_sum fun i hi => ?_
    have hpiece : S.filter (fun B => piece B = i) =
        (blocks.filter (fun B => piece B = i)).filter (fun B => B ∉ X) := by
      ext B
      simp only [S, mem_filter]
      constructor
      · rintro ⟨⟨⟨hb, _⟩, hX⟩, hpi⟩; exact ⟨⟨hb, hpi⟩, hX⟩
      · rintro ⟨⟨hb, hpi⟩, hX⟩; exact ⟨⟨⟨hb, hpi ▸ hi⟩, hX⟩, hpi⟩
    rw [hpiece, sum_congr rfl fun B hB => by rw [(mem_filter.mp (mem_filter.mp hB).1).2],
      ← mul_sum]
    have htot := sum_filter_not_ge (blocks.filter (fun B => piece B = i)) X w
      (fun B hB => by
        have := (hw B (mem_filter.mp hB).1).2
        rwa [(mem_filter.mp hB).2] at this) (hSig i hi)
    have hci := hc i hi
    calc c i * Sig i - (((blocks.filter (fun B => piece B = i)).filter (fun B => B ∈ X)).card : ℝ) *
          c i / Xi i
        = c i * (Sig i - (((blocks.filter (fun B => piece B = i)).filter
            (fun B => B ∈ X)).card : ℝ) / Xi i) := by ring
      _ ≤ c i * ∑ B ∈ (blocks.filter (fun B => piece B = i)).filter (fun B => B ∉ X), w B :=
          mul_le_mul_of_nonneg_left htot hci

end Sarkozy.DistinctChoice
