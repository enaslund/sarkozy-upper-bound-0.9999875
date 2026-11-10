module

public import Sarkozy.TraceMixing.Paley
public import Sarkozy.PartVRecords.Prices

@[expose] public section

/-!
# The one-stage replacement of the folded matching records at one prime
(`lem:record:one-stage-folded-e`(a), (b), (e))

`paper/sections/20c_middle_frame.tex`, paragraph "The folded matching records" and
`lem:record:one-stage-folded-e`. Over a finite field `F` with `q ≡ 3 (mod 4)` elements (in the
paper `F = 𝔽_p`, `p ≥ 11`), `k = (q - 3)/4`, `a → a'` means `χ(a' - a) = 1`. For a shared label
`c`, `V_c = F ∖ {c}` and `V_c^± = {a ∈ V_c : χ(a - c) = ±1}`; `M_c` is the `0/1` matrix of `→` on
`V_c` (`Mrel`), `M_c^{+-}` its restriction to `V_c^+ × V_c^-` (`Mpm`), and
`𝒦₊ = M_c/(2k) - M_c^{+-}/(2k(k+1))` (`Kplus`).

**Proved.**
* (a) the four blocks of `M_c` have equal row and column degrees `k, k + 1, k, k`
  (`rowCount`, `colCount`, as `4 · # = q - 3 + 4 [block (+,-)]`, from WP-S's Paley count
  `Sarkozy.TraceMixing.card_sign_pair`);
* (b) `𝒦₊` is doubly stochastic on `V_c` (`Kplus_row_sum`, `Kplus_col_sum`), supported on the pairs
  `a → a'` (`Kplus_eq_zero_of_not`), with entries `1/(2(k+1))` on the block `(+,-)` and `1/(2k)`
  elsewhere (`Kplus_of_arrow`); from each `a` it puts mass `1/2` on each destination sector, and
  each column receives `1/2` from each source sector (`Kplus_row_sector`, `Kplus_col_sector`);
* the replacement law at one prime (`plusLaw`, (e)): the shared label `c` (object `2`) uniform,
  the first private label `a` (object `0`) uniform on `V_c`, and `a' ∼ 𝒦₊(a, ·)` (object `1`);
  equivalently the weight `𝒦₊^{(c)}(a, a')/(q(q-1))` on `(a, a', c)`. Proved: it is a probability
  law (`tripleLaw`); it is supported on `a → a'` with `a, a' ≠ c` (`plusLaw_support`), so the
  queried edge `y₀ → y₁` is strict-square and the three labels are distinct; it is invariant
  under the maps `z ↦ αz + β`, `χ(α) = 1` (`plusLaw_affine`); the half marginals at the record's
  own cut, the laws of `(c, a)` and of `(c, a')`, are uniform on the ordered distinct pairs, as for
  the record being replaced (`plusLaw_pair02`, `plusLaw_pair12`); the queried pair `(a, a')` is
  uniform on the strict-square pairs, weight `2/(q(q-1))` (`plusLaw_pair01`); and every one-slot
  marginal is uniform (`plusLaw_vertex_uniform`).
* The coupling is direct: no label is resampled at coincidences (the law is defined by the
  kernel alone).

**Elsewhere:** the operator norms of (c) are in `Sarkozy.PartVRecords.OneStageNorms`
(`‖𝒦₊‖ ≤ κ^{fold}_p`, `𝒦₀ = -I/(p - 2)`, `Δ 𝐡_c = 𝐡_c/(p - 2)`), `OneStageDelta`
(`‖Δ‖ ≤ k_new(p) r`) and `OneStageSym` (`‖Sym Δ‖ = 1/(p - 2)`); the block law and its acceptance
in `OneStageBlock`, its half laws in `OneStageMarginals`. **Not proved:** the block bounds of (d);
the sharp constant `k_new(X) b^{-1/2}` enters the prices (`Sarkozy.PartVRecords.Prices`) as a
parameter.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.TraceMixing

section OnePrime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- `k = (q - 3)/4`. -/
noncomputable def kP (F : Type*) [Fintype F] : ℝ := ((Fintype.card F : ℝ) - 3) / 4

/-- The `0/1` matrix `M_c` of the relation `a → a'` on `V_c = F ∖ {c}`. -/
noncomputable def Mrel (c a a' : F) : ℝ := if a ≠ c ∧ a' ≠ c ∧ χ (a' - a) = 1 then 1 else 0

/-- Its restriction `M_c^{+-}` to `V_c^+ × V_c^-`, extended by zero. -/
noncomputable def Mpm (c a a' : F) : ℝ :=
  if χ (a - c) = 1 ∧ χ (a' - c) = -1 ∧ χ (a' - a) = 1 then 1 else 0

/-- **The sector-balanced coupling** `𝒦₊ = M_c/(2k) - M_c^{+-}/(2k(k+1))`
(`lem:record:one-stage-folded-e`(b)). -/
noncomputable def Kplus (c a a' : F) : ℝ :=
  Mrel c a a' / (2 * kP F) - Mpm c a a' / (2 * kP F * (kP F + 1))

theorem ne_of_chi_eq {x y : F} {σ : ℤ} (h : χ (x - y) = σ) (hσ : σ = 1 ∨ σ = -1) : x ≠ y := by
  rintro rfl
  rw [sub_self, quadraticChar_zero] at h
  rcases hσ with rfl | rfl <;> simp at h

theorem chi_pm {x y : F} (h : x ≠ y) : χ (x - y) = 1 ∨ χ (x - y) = -1 :=
  quadraticChar_dichotomy (sub_ne_zero.mpr h)

/-! ### (a) The degrees of the four blocks -/

/-- **(a), row degrees**: for `a ∈ V_c` and a sector sign `σ'`,
`4 · #{a' : a → a', χ(a' - c) = σ'} = q - 3 + 4 [χ(a - c) = 1, σ' = -1]`: the blocks `(+,+)`,
`(+,-)`, `(-,+)`, `(-,-)` have row degrees `k, k + 1, k, k`. -/
theorem rowCount (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {c a : F} (hac : a ≠ c)
    {σ' : ℤ} (hσ' : σ' = 1 ∨ σ' = -1) :
    4 * ((univ.filter fun a' => χ (a' - a) = 1 ∧ χ (a' - c) = σ').card : ℤ) =
      Fintype.card F - 3 + 4 * (if χ (a - c) = 1 ∧ σ' = -1 then 1 else 0) := by
  rw [card_sign_pair hF hac (Or.inl rfl) hσ', chi_swap h3 c a]
  rcases chi_pm hac with h | h <;> rcases hσ' with rfl | rfl <;> rw [h] <;> norm_num <;> ring

/-- **(a), column degrees**: for `a' ∈ V_c` and a source sector sign `σ`,
`4 · #{a : a → a', χ(a - c) = σ} = q - 3 + 4 [σ = 1, χ(a' - c) = -1]`. -/
theorem colCount (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {c a' : F} (hac : a' ≠ c)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    4 * ((univ.filter fun a => χ (a' - a) = 1 ∧ χ (a - c) = σ).card : ℤ) =
      Fintype.card F - 3 + 4 * (if σ = 1 ∧ χ (a' - c) = -1 then 1 else 0) := by
  have hfilt : (univ.filter fun a => χ (a' - a) = 1 ∧ χ (a - c) = σ) =
      univ.filter fun a => χ (a - a') = -1 ∧ χ (a - c) = σ := by
    ext a
    simp only [mem_filter, mem_univ, true_and, chi_swap h3 a' a]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩
  rw [hfilt, card_sign_pair hF hac (Or.inr rfl) hσ, chi_swap h3 c a']
  rcases chi_pm hac with h | h <;> rcases hσ with rfl | rfl <;> rw [h] <;> norm_num <;> ring

/-! ### (b) The coupling -/

omit [Field F] [DecidableEq F] in
variable (F) in
theorem kP_pos (h7 : 7 ≤ Fintype.card F) : 0 < kP F := by
  unfold kP
  have : (7 : ℝ) ≤ Fintype.card F := by exact_mod_cast h7
  linarith

theorem Kplus_eq_zero_of_not {c a a' : F} (h : ¬ χ (a' - a) = 1) : Kplus c a a' = 0 := by
  simp only [Kplus, Mrel, Mpm, h, and_false, ↓reduceIte, zero_div, sub_zero]

theorem Kplus_left_eq {c a' : F} : Kplus c c a' = 0 := by
  have h0 : ¬ χ (c - c) = 1 := by rw [sub_self, quadraticChar_zero]; decide
  simp only [Kplus, Mrel, Mpm, h0, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
    zero_div, sub_zero]

theorem Kplus_right_eq {c a : F} : Kplus c a c = 0 := by
  have h0 : ¬ χ (c - c) = -1 := by rw [sub_self, quadraticChar_zero]; decide
  simp only [Kplus, Mrel, Mpm, h0, ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte,
    zero_div, sub_zero]

/-- **(b), the entries**: on the pairs `a → a'` of `V_c`, `𝒦₊ = 1/(2(k+1))` on the block `(+,-)`
and `1/(2k)` elsewhere. -/
theorem Kplus_of_arrow (hk : 0 < kP F) {c a a' : F} (ha : a ≠ c) (ha' : a' ≠ c)
    (h : χ (a' - a) = 1) :
    Kplus c a a' = if χ (a - c) = 1 ∧ χ (a' - c) = -1 then 1 / (2 * (kP F + 1))
      else 1 / (2 * kP F) := by
  unfold Kplus Mrel Mpm
  by_cases hs : χ (a - c) = 1 ∧ χ (a' - c) = -1
  · simp only [hs, h, ha, ha', ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    field_simp
    ring
  · simp only [hs, h, ha, ha', ne_eq, not_false_eq_true, and_self, and_true, ↓reduceIte]
    ring

theorem Kplus_nonneg (hk : 0 < kP F) (c a a' : F) : 0 ≤ Kplus c a a' := by
  by_cases h : χ (a' - a) = 1
  · by_cases ha : a = c
    · rw [ha, Kplus_left_eq]
    · by_cases ha' : a' = c
      · rw [ha', Kplus_right_eq]
      · rw [Kplus_of_arrow hk ha ha' h]
        split_ifs <;> positivity
  · rw [Kplus_eq_zero_of_not h]

/-- On the sector `χ(a' - c) = σ'`, the coupling from `a ∈ V_c` is the constant `e(σ')` on the
out-neighbours of `a`. -/
theorem Kplus_sector_pt (hk : 0 < kP F) {c a : F} (ha : a ≠ c) {σ' : ℤ} (hσ' : σ' = 1 ∨ σ' = -1)
    (a' : F) :
    (if χ (a' - c) = σ' then Kplus c a a' else 0) =
      if χ (a' - a) = 1 ∧ χ (a' - c) = σ' then
        (if χ (a - c) = 1 ∧ σ' = -1 then 1 / (2 * (kP F + 1)) else 1 / (2 * kP F)) else 0 := by
  by_cases hs : χ (a' - c) = σ'
  · have ha' : a' ≠ c := ne_of_chi_eq hs hσ'
    by_cases h : χ (a' - a) = 1
    · rw [ite_eq_left hs, ite_eq_left ⟨h, hs⟩, Kplus_of_arrow hk ha ha' h, hs]
    · rw [ite_eq_left hs, ite_eq_right (fun h' => h h'.1), Kplus_eq_zero_of_not h]
  · rw [ite_eq_right hs, ite_eq_right (fun h' => hs h'.2)]

theorem card_real_of_four {n : ℕ} {m : ℤ} (h : 4 * (n : ℤ) = m) : (n : ℝ) = (m : ℝ) / 4 := by
  have : (4 : ℝ) * n = m := by exact_mod_cast h
  linarith

/-- **(b), sector balance of the rows**: from each `a ∈ V_c`, `𝒦₊` puts mass `1/2` on each
destination sector. -/
theorem Kplus_row_sector (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    {c a : F} (ha : a ≠ c) {σ' : ℤ} (hσ' : σ' = 1 ∨ σ' = -1) :
    ∑ a', (if χ (a' - c) = σ' then Kplus c a a' else 0) = 1 / 2 := by
  simp only [Kplus_sector_pt hk ha hσ']
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
  have hc := card_real_of_four (rowCount hF h3 ha hσ')
  rw [hc]
  have hq : (Fintype.card F : ℝ) = 4 * kP F + 3 := by
    unfold kP
    ring
  by_cases hs : χ (a - c) = 1 ∧ σ' = -1
  · simp only [hs, and_self, ↓reduceIte]
    push_cast
    rw [hq]
    field_simp
    ring
  · simp only [hs, ↓reduceIte]
    push_cast
    rw [hq]
    field_simp
    ring

/-- **(b), sector balance of the columns**: every `a' ∈ V_c` receives mass `1/2` from each source
sector. -/
theorem Kplus_col_sector (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    {c a' : F} (ha' : a' ≠ c) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ∑ a, (if χ (a - c) = σ then Kplus c a a' else 0) = 1 / 2 := by
  have hpt (a : F) : (if χ (a - c) = σ then Kplus c a a' else 0) =
      if χ (a' - a) = 1 ∧ χ (a - c) = σ then
        (if σ = 1 ∧ χ (a' - c) = -1 then 1 / (2 * (kP F + 1)) else 1 / (2 * kP F)) else 0 := by
    by_cases hs : χ (a - c) = σ
    · have ha : a ≠ c := ne_of_chi_eq hs hσ
      by_cases h : χ (a' - a) = 1
      · rw [ite_eq_left hs, ite_eq_left ⟨h, hs⟩, Kplus_of_arrow hk ha ha' h, hs]
      · rw [ite_eq_left hs, ite_eq_right (fun h' => h h'.1), Kplus_eq_zero_of_not h]
    · rw [ite_eq_right hs, ite_eq_right (fun h' => hs h'.2)]
  simp only [hpt]
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
  have hc := card_real_of_four (colCount hF h3 ha' hσ)
  rw [hc]
  have hq : (Fintype.card F : ℝ) = 4 * kP F + 3 := by
    unfold kP
    ring
  by_cases hs : σ = 1 ∧ χ (a' - c) = -1
  · simp only [hs, and_self, ↓reduceIte]
    push_cast
    rw [hq]
    field_simp
    ring
  · simp only [hs, ↓reduceIte]
    push_cast
    rw [hq]
    field_simp
    ring

/-- Splitting a function of `a'` that vanishes at `c` along the two sectors. -/
theorem sum_split_sectors {c : F} (g : F → ℝ) (hg : g c = 0) :
    ∑ a', g a' = ∑ a', (if χ (a' - c) = 1 then g a' else 0) +
      ∑ a', (if χ (a' - c) = -1 then g a' else 0) := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun a' _ => ?_
  by_cases h : a' = c
  · subst h
    simp [hg]
  · rcases chi_pm h with h1 | h1
    · rw [ite_eq_left h1, ite_eq_right (by rw [h1]; decide), add_zero]
    · rw [ite_eq_right (by rw [h1]; decide), ite_eq_left h1, zero_add]

/-- **(b), the rows are stochastic**: `∑_{a'} 𝒦₊(a, a') = 1` for `a ∈ V_c`. -/
theorem Kplus_row_sum (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    {c a : F} (ha : a ≠ c) : ∑ a', Kplus c a a' = 1 := by
  rw [sum_split_sectors (fun a' => Kplus c a a') Kplus_right_eq,
    Kplus_row_sector hF h3 hk ha (Or.inl rfl), Kplus_row_sector hF h3 hk ha (Or.inr rfl)]
  norm_num

/-- **(b), the columns are stochastic**: `∑_a 𝒦₊(a, a') = 1` for `a' ∈ V_c`. -/
theorem Kplus_col_sum (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    {c a' : F} (ha' : a' ≠ c) : ∑ a, Kplus c a a' = 1 := by
  rw [sum_split_sectors (fun a => Kplus c a a') Kplus_left_eq,
    Kplus_col_sector hF h3 hk ha' (Or.inl rfl), Kplus_col_sector hF h3 hk ha' (Or.inr rfl)]
  norm_num

/-- `∑_{a'} 𝒦₊(a, a')` is `[a ≠ c]`. -/
theorem Kplus_row_sum' (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c a : F) : ∑ a', Kplus c a a' = if a = c then 0 else 1 := by
  by_cases ha : a = c
  · subst ha
    simp [Kplus_left_eq]
  · rw [ite_eq_right ha, Kplus_row_sum hF h3 hk ha]

theorem Kplus_col_sum' (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (c a' : F) : ∑ a, Kplus c a a' = if a' = c then 0 else 1 := by
  by_cases ha : a' = c
  · subst ha
    simp [Kplus_right_eq]
  · rw [ite_eq_right ha, Kplus_col_sum hF h3 hk ha]

/-- **The sum over the shared label**: `∑_c 𝒦₊^{(c)}(a, a') = 2 [a → a']` (the queried pair of the
replacement is uniform on the strict-square pairs). -/
theorem Kplus_sum_shared (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (a a' : F) : ∑ c, Kplus c a a' = if χ (a' - a) = 1 then 2 else 0 := by
  by_cases h : χ (a' - a) = 1
  · rw [ite_eq_left h]
    have haa : a ≠ a' := (ne_of_chi_eq h (Or.inl rfl)).symm
    -- split `c` into `{a, a'}` and the rest
    have hpt (c : F) : Kplus c a a' =
        (if c ≠ a ∧ c ≠ a' then 1 / (2 * kP F) else 0) -
          (if χ (c - a) = -1 ∧ χ (c - a') = 1 then 1 / (2 * kP F) - 1 / (2 * (kP F + 1))
            else 0) := by
      by_cases hca : c = a
      · subst hca
        have : ¬ (χ (c - c) = -1 ∧ χ (c - a') = 1) := by
          rw [sub_self, quadraticChar_zero]
          rintro ⟨h0, -⟩
          norm_num at h0
        rw [Kplus_left_eq, ite_eq_right (by tauto), ite_eq_right this]
        ring
      · by_cases hca' : c = a'
        · subst hca'
          have : ¬ (χ (c - a) = -1 ∧ χ (c - c) = 1) := by
            rw [sub_self, quadraticChar_zero]
            rintro ⟨-, h0⟩
            norm_num at h0
          rw [Kplus_right_eq, ite_eq_right (by tauto), ite_eq_right this]
          ring
        · rw [Kplus_of_arrow hk (Ne.symm hca) (Ne.symm hca') h,
            ite_eq_left (show c ≠ a ∧ c ≠ a' from ⟨hca, hca'⟩)]
          have e1 : χ (a - c) = 1 ↔ χ (c - a) = -1 := by
            rw [chi_swap h3 a c]
            constructor <;> intro h' <;> linarith
          have e2 : χ (a' - c) = -1 ↔ χ (c - a') = 1 := by
            rw [chi_swap h3 a' c]
            constructor <;> intro h' <;> linarith
          by_cases hs : χ (c - a) = -1 ∧ χ (c - a') = 1
          · rw [ite_eq_left (show χ (a - c) = 1 ∧ χ (a' - c) = -1 from
              ⟨e1.mpr hs.1, e2.mpr hs.2⟩), ite_eq_left hs]
            ring
          · rw [ite_eq_right (show ¬(χ (a - c) = 1 ∧ χ (a' - c) = -1) from
              fun h' => hs ⟨e1.mp h'.1, e2.mp h'.2⟩), ite_eq_right hs]
            ring
    simp only [hpt]
    rw [sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter, sum_const, sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
    have hcount := card_real_of_four (card_sign_pair hF haa (Or.inr rfl) (Or.inl rfl))
    rw [hcount, chi_swap h3 a a', h]
    have hpair : ((univ.filter fun c : F => c ≠ a ∧ c ≠ a').card : ℝ) =
        (Fintype.card F : ℝ) - 2 := by
      have hfilt : (univ.filter fun c : F => c ≠ a ∧ c ≠ a') = (univ.erase a).erase a' := by
        ext c
        simp only [mem_filter, mem_univ, true_and, mem_erase, ne_eq]
        tauto
      rw [hfilt, card_erase_of_mem (mem_erase.mpr ⟨haa.symm, mem_univ _⟩),
        card_erase_of_mem (mem_univ _), card_univ]
      have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card (α := F)
      push_cast [Nat.sub_sub, Nat.cast_sub h2]
      ring
    rw [hpair]
    have hq : (Fintype.card F : ℝ) = 4 * kP F + 3 := by
      unfold kP
      ring
    push_cast
    rw [hq]
    field_simp
    ring
  · rw [ite_eq_right h]
    exact sum_eq_zero fun c _ => Kplus_eq_zero_of_not h

/-! ### The replacement law at one prime (`lem:record:one-stage-folded-e`(e)) -/

/-- The weight `𝒦₊^{(c)}(a, a')/(q(q - 1))` of the triple `(a, a', c)`: object `0` carries `a`,
object `1` carries `a'`, object `2` (shared) carries `c`. -/
noncomputable def tripleWeight (t : F × F × F) : ℝ :=
  ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ * Kplus t.2.2 t.1 t.2.1

theorem card_ne_self_real (c : F) :
    ((univ.filter fun a : F => a ≠ c).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
  rw [filter_ne' univ c, card_erase_of_mem (mem_univ _), card_univ]
  have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
  push_cast [Nat.cast_sub h1]
  ring

omit [DecidableEq F] in
theorem card_gt_one_real : (1 : ℝ) < Fintype.card F := by
  have := Fintype.one_lt_card (α := F)
  exact_mod_cast this

omit [Field F] in
theorem sum_ite_eq_zero_one (a : F) :
    ∑ c : F, (if a = c then (0 : ℝ) else 1) = (Fintype.card F : ℝ) - 1 := by
  have hpt : ∀ c : F, (if a = c then (0 : ℝ) else 1) = 1 - (if a = c then 1 else 0) := by
    intro c
    split_ifs <;> norm_num
  simp only [hpt, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, Finset.sum_ite_eq,
    mem_univ, ↓reduceIte]

variable (F) in
/-- **The replacement law of the folded matching record at one prime**, on triples
`(a, a', c)`. -/
noncomputable def tripleLaw (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (hk : 0 < kP F) : FiniteLaw (F × F × F) where
  weight := tripleWeight
  nonneg t := by
    unfold tripleWeight
    have := card_gt_one_real (F := F)
    exact mul_nonneg (inv_nonneg.mpr (by nlinarith)) (Kplus_nonneg hk _ _ _)
  total := by
    unfold tripleWeight
    rw [← mul_sum]
    have hsum : ∑ t : F × F × F, Kplus t.2.2 t.1 t.2.1 =
        (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_prod_type]
      have h1 : ∀ a : F, ∑ a', ∑ c, Kplus c a a' = (Fintype.card F : ℝ) - 1 := by
        intro a
        rw [sum_comm]
        simp only [Kplus_row_sum' hF h3 hk]
        exact sum_ite_eq_zero_one a
      simp only [h1, sum_const, card_univ, nsmul_eq_mul]
    rw [hsum]
    have := card_gt_one_real (F := F)
    have h0 : (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) ≠ 0 := by
      apply mul_ne_zero <;> linarith
    exact inv_mul_cancel₀ h0

/-- The configuration of the three objects (one layer) carried by a triple `(a, a', c)`. -/
def tripleConfig (t : F × F × F) : Fin 3 × Fin 1 → F := fun o => ![t.1, t.2.1, t.2.2] o.1

variable (F) in
/-- **The replacement law** at one prime, on the labellings of the three one-layer objects. -/
noncomputable def plusLaw (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (hk : 0 < kP F) : FiniteLaw (Fin 3 × Fin 1 → F) :=
  (tripleLaw F hF h3 hk).map tripleConfig

theorem expect_plusLaw (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (H : (Fin 3 × Fin 1 → F) → ℝ) :
    (plusLaw F hF h3 hk).expect H = ∑ t, tripleWeight t * H (tripleConfig t) := by
  unfold plusLaw
  rw [FiniteLaw.expect_map]
  rfl

/-- **Support** (`lem:record:one-stage-folded-e`(e)): a configuration charged by the replacement
has `y₀ → y₁` (a strict-square edge) and `y₀, y₁ ≠ y₂`; so the three labels are distinct. -/
theorem plusLaw_support (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    {y : Fin 3 × Fin 1 → F} (hy : (plusLaw F hF h3 hk).weight y ≠ 0) :
    χ (y (1, 0) - y (0, 0)) = 1 ∧ y (0, 0) ≠ y (2, 0) ∧ y (1, 0) ≠ y (2, 0) := by
  unfold plusLaw FiniteLaw.map at hy
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  split_ifs at ht with hyt
  · subst hyt
    change tripleWeight t ≠ 0 at ht
    unfold tripleWeight at ht
    have hK : Kplus t.2.2 t.1 t.2.1 ≠ 0 := right_ne_zero_of_mul ht
    simp only [tripleConfig, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      exact hK (Kplus_eq_zero_of_not h)
    · intro h
      rw [h] at hK
      exact hK Kplus_left_eq
    · intro h
      rw [h] at hK
      exact hK Kplus_right_eq
  · exact absurd rfl ht

/-- The expectation of a function of one triple coordinate pair, as a triple sum. -/
theorem expect_plusLaw_triple (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (hk : 0 < kP F) (g : F → F → F → ℝ) :
    (plusLaw F hF h3 hk).expect (fun y => g (y (0, 0)) (y (1, 0)) (y (2, 0))) =
      ∑ a, ∑ a', ∑ c, ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ *
        Kplus c a a' * g a a' c := by
  rw [expect_plusLaw, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => sum_congr rfl fun c _ => ?_
  simp only [tripleWeight, tripleConfig, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **The half marginal `(c, a)`** at the record's own cut (objects `2` and `0`): uniform on the
ordered distinct pairs, `P(y₂ = c, y₀ = a) = [a ≠ c]/(q(q - 1))`, as for the record replaced. -/
theorem plusLaw_pair02 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (g : F → F → ℝ) :
    (plusLaw F hF h3 hk).expect (fun y => g (y (2, 0)) (y (0, 0))) =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ *
        ∑ c, ∑ a, if a = c then 0 else g c a := by
  have h := expect_plusLaw_triple hF h3 hk (fun a _ c => g c a)
  rw [h]
  set w := ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹
  have hin : ∀ a : F, ∑ a', ∑ c, w * Kplus c a a' * g c a =
      ∑ c, w * (if a = c then 0 else g c a) := by
    intro a
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    have e : ∑ a', w * Kplus c a a' * g c a = w * g c a * ∑ a', Kplus c a a' := by
      rw [mul_sum]
      exact sum_congr rfl fun a' _ => by ring
    rw [e, Kplus_row_sum' hF h3 hk c a]
    split_ifs <;> ring
  simp only [hin]
  rw [sum_comm]
  simp only [mul_sum]

/-- **The half marginal `(c, a')`** (objects `2` and `1`): uniform on the ordered distinct pairs. -/
theorem plusLaw_pair12 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (g : F → F → ℝ) :
    (plusLaw F hF h3 hk).expect (fun y => g (y (2, 0)) (y (1, 0))) =
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹ *
        ∑ c, ∑ a', if a' = c then 0 else g c a' := by
  have h := expect_plusLaw_triple hF h3 hk (fun _ a' c => g c a')
  rw [h, sum_comm]
  set w := ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹
  have hin : ∀ a' : F, ∑ a, ∑ c, w * Kplus c a a' * g c a' =
      ∑ c, w * (if a' = c then 0 else g c a') := by
    intro a'
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    have e : ∑ a, w * Kplus c a a' * g c a' = w * g c a' * ∑ a, Kplus c a a' := by
      rw [mul_sum]
      exact sum_congr rfl fun a _ => by ring
    rw [e, Kplus_col_sum' hF h3 hk c a']
    split_ifs <;> ring
  simp only [hin]
  rw [sum_comm]
  simp only [mul_sum]

/-- **The queried pair `(a, a')`** (objects `0` and `1`) is uniform on the strict-square pairs:
`P(y₀ = a, y₁ = a') = 2 [a → a']/(q(q - 1))`. -/
theorem plusLaw_pair01 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    (g : F → F → ℝ) :
    (plusLaw F hF h3 hk).expect (fun y => g (y (0, 0)) (y (1, 0))) =
      ∑ a, ∑ a', if χ (a' - a) = 1 then
        2 / ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1)) * g a a' else 0 := by
  have h := expect_plusLaw_triple hF h3 hk (fun a a' _ => g a a')
  rw [h]
  refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
  set w := ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1))⁻¹
  have e : ∑ c, w * Kplus c a a' * g a a' = w * g a a' * ∑ c, Kplus c a a' := by
    rw [mul_sum]
    exact sum_congr rfl fun c _ => by ring
  rw [e, Kplus_sum_shared hF h3 hk a a']
  split_ifs <;> ring

/-- **Uniform one-slot marginals** of the replacement at one prime. -/
theorem plusLaw_vertex_uniform (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (hk : 0 < kP F) (o : Fin 3 × Fin 1) (g : F → ℝ) :
    (plusLaw F hF h3 hk).expect (fun y => g (y o)) = (FiniteLaw.uniform F).expect g := by
  have hq := card_gt_one_real (F := F)
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  rw [FiniteLaw.expect_uniform]
  obtain ⟨o1, o2⟩ := o
  have ho2 : o2 = 0 := Subsingleton.elim _ _
  subst ho2
  -- reduce to the pair marginals with the shared label
  have hS1 : ∑ c : F, ∑ a : F, (if a = c then (0 : ℝ) else g a) =
      ((Fintype.card F : ℝ) - 1) * ∑ a, g a := by
    rw [sum_comm]
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    have : ∑ c : F, (if a = c then (0 : ℝ) else g a) = ∑ c : F, (if c ≠ a then g a else 0) := by
      refine sum_congr rfl fun c _ => ?_
      by_cases h : a = c
      · subst h; simp
      · rw [ite_eq_right h, ite_eq_left (Ne.symm h)]
    rw [this, ← sum_filter, sum_const, nsmul_eq_mul, card_ne_self_real a]
  have hS2 : ∑ c : F, ∑ a : F, (if a = c then (0 : ℝ) else g c) =
      ((Fintype.card F : ℝ) - 1) * ∑ c, g c := by
    rw [mul_sum]
    refine sum_congr rfl fun c _ => ?_
    have : ∑ a : F, (if a = c then (0 : ℝ) else g c) = ∑ a : F, (if a ≠ c then g c else 0) := by
      refine sum_congr rfl fun a _ => ?_
      by_cases h : a = c
      · subst h; simp
      · rw [ite_eq_right h, ite_eq_left h]
    rw [this, ← sum_filter, sum_const, nsmul_eq_mul, card_ne_self_real c]
  fin_cases o1
  · have h := plusLaw_pair02 hF h3 hk (fun _ a => g a)
    change (plusLaw F hF h3 hk).expect (fun y => g (y (0, 0))) = _
    rw [h, hS1]
    field_simp
  · have h := plusLaw_pair12 hF h3 hk (fun _ a' => g a')
    change (plusLaw F hF h3 hk).expect (fun y => g (y (1, 0))) = _
    rw [h, hS1]
    field_simp
  · have h := plusLaw_pair02 hF h3 hk (fun c _ => g c)
    change (plusLaw F hF h3 hk).expect (fun y => g (y (2, 0))) = _
    rw [h, hS2]
    field_simp

/-- **Invariance under `𝒢_p`** (`lem:record:one-stage-folded-e`(e)): the maps `z ↦ αz + β` with
`χ(α) = 1` preserve the sectors and the relation `→`, so the coupling, hence the law. -/
theorem Kplus_affine {α : F} (hα : χ α = 1) (β c a a' : F) :
    Kplus (α * c + β) (α * a + β) (α * a' + β) = Kplus c a a' := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [quadraticChar_zero] at hα
    exact zero_ne_one hα
  have hd : ∀ x y : F, (α * x + β) - (α * y + β) = α * (x - y) := fun x y => by ring
  have hχ : ∀ x y : F, χ ((α * x + β) - (α * y + β)) = χ (x - y) := fun x y => by
    rw [hd, map_mul, hα, one_mul]
  have hne : ∀ x y : F, (α * x + β ≠ α * y + β) ↔ x ≠ y := fun x y => by
    constructor
    · intro h e
      exact h (by rw [e])
    · intro h e
      exact h (mul_left_cancel₀ hα0 (add_right_cancel e))
  unfold Kplus Mrel Mpm
  simp only [hχ, hne]

theorem plusLaw_affine (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
    {α : F} (hα : χ α = 1) (β : F) (H : (Fin 3 × Fin 1 → F) → ℝ) :
    (plusLaw F hF h3 hk).expect (fun y => H (fun o => α * y o + β)) =
      (plusLaw F hF h3 hk).expect H := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [quadraticChar_zero] at hα
    exact zero_ne_one hα
  rw [expect_plusLaw, expect_plusLaw]
  let e : F ≃ F := ⟨fun x => α * x + β, fun x => α⁻¹ * (x - β), fun x => by
    simp only; field_simp; ring, fun x => by simp only; field_simp; ring⟩
  let E : F × F × F ≃ F × F × F := Equiv.prodCongr e (Equiv.prodCongr e e)
  refine Fintype.sum_equiv E _ _ fun t => ?_
  have hc : (fun o => α * tripleConfig t o + β) = tripleConfig (E t) := by
    funext o
    obtain ⟨o1, o2⟩ := o
    fin_cases o1 <;> rfl
  rw [hc]
  congr 1
  unfold tripleWeight
  change _ = _ * Kplus (α * t.2.2 + β) (α * t.1 + β) (α * t.2.1 + β)
  rw [Kplus_affine hα]

end OnePrime

end Sarkozy.PartVRecords
