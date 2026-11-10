module

public import Sarkozy.L20Cap.Mass

/-!
# The singleton Grams of the core (`prop:l20-rank4`(a))

`paper/sections/20_middle_reference.tex`, `prop:l20-rank4`(a), proof: "Two core coordinates on the
same side form a uniform distinct pair, and `(a_i, c_j)` a uniform directed pair." Notation of
`Sarkozy.L20Cap.Rectangle`; `‖h‖² = E_z h(z)²` on the labels, `q = 1/p`.

* `pair_const`: a function of the ordered distinct pairs invariant under the square-affine maps
  and the exchange is constant (`χ(-1) = -1`); `dir_const`: a function invariant under the
  square-affine maps is constant on the directed pairs `χ(y' - y) = 1`;
* `coreLaw_same`, `coreLaw_dir`: the laws of `(a₀, a₁)`, `(c₀, c₁)` under `μ^core` are uniform on
  the ordered distinct pairs, those of `(a_i, c_j)` uniform on the directed pairs;
* `core_cross`: for a real `h` of mean zero and two distinct core coordinates `k ≠ k'`,
  `E_C h(C_k)h(C_{k'}) = -q/(1 - q) ‖h‖²` (for a directed pair the Paley part `⟨h, Φ̂h⟩`
  vanishes, as `χ(-1) = -1`), and `core_diag`: `E_C h(C_k)² = ‖h‖²`;
* **`core_lin_sq`**: `E_C(∑_k c_k h(C_k))² = (∑c_k² - q/(1 - q)((∑c_k)² - ∑c_k²))‖h‖²`; in
  particular **`uvec_sq`** (`𝐮^*𝐮 = I/(1 - q)`) and **`wvec_sq`** (`𝐰^*𝐰 = (1 - 4q)/(1 - q) I`)
  as quadratic forms on real `h ∈ 𝓗`.

For (b), the pointwise identities of `𝖪_⋆` used in the proof: `sum_Kstar` (`E_z𝖪_⋆ = \bar𝖪 - 1`),
`sum_Kstar_sq` (`E_z𝖪_⋆² = 6\bar𝖪 + 5`), `sum_chi_Kstar` (`E_zχ(z - x_k)𝖪_⋆ = s_k(\bar𝖪 - 1)`).

Not here: the Paley part of `𝐮^*𝐰 = 2rΦ̂/(1 - q)` (an off-diagonal identity); the operator Grams
of (b)–(d), which need the commutant `lem:spec:affpair`(d).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Orbits of the square-affine maps on pairs -/

/-- **Transitivity on the directed pairs**: a function on `F × F` invariant under the
square-affine maps takes one value on the pairs with `χ(y' - y) = 1`. -/
theorem dir_const {m : F → F → ℝ}
    (hm : ∀ (α β : F), quadraticChar F α = 1 → ∀ y y', m (α * y + β) (α * y' + β) = m y y')
    {y y' z z' : F} (h : quadraticChar F (y' - y) = 1) (h' : quadraticChar F (z' - z) = 1) :
    m y y' = m z z' := by
  have hd : y' - y ≠ 0 := by intro h0; rw [h0] at h; simp at h
  have hd' : z' - z ≠ 0 := by intro h0; rw [h0] at h'; simp at h'
  set α := (z' - z) / (y' - y) with hαdef
  have hα : quadraticChar F α = 1 := by
    rw [hαdef, div_eq_mul_inv, map_mul, h', quadraticChar_inv' hd, h, one_mul]
  have e1 : α * y + (z - α * y) = z := by ring
  have e2 : α * y' + (z - α * y) = z' := by
    rw [hαdef]; field_simp; ring
  rw [← hm α (z - α * y) hα y y', e1, e2]

/-- **The two orbits joined by the exchange**: a function on `F × F` invariant under the
square-affine maps and symmetric takes one value on the ordered distinct pairs. -/
theorem pair_const (hm1 : quadraticChar F (-1) = -1) {m : F → F → ℝ}
    (hm : ∀ (α β : F), quadraticChar F α = 1 → ∀ y y', m (α * y + β) (α * y' + β) = m y y')
    (hs : ∀ y y', m y' y = m y y') {y y' z z' : F} (h : y ≠ y') (h' : z ≠ z') :
    m y y' = m z z' := by
  have hd : y' - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hd' : z' - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h')
  have hneg : ∀ a b : F, quadraticChar F (b - a) = -quadraticChar F (a - b) := by
    intro a b
    have e : b - a = (-1) * (a - b) := by ring
    rw [e, map_mul, hm1, neg_one_mul]
  -- normalize both pairs to a directed pair
  have norm : ∀ a b : F, a ≠ b → ∃ c c', quadraticChar F (c' - c) = 1 ∧ m a b = m c c' := by
    intro a b hab
    have hab' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    rcases quadraticChar_dichotomy hab' with h1 | h1
    · exact ⟨a, b, h1, rfl⟩
    · refine ⟨b, a, ?_, (hs a b).symm⟩
      rw [hneg, h1, neg_neg]
  obtain ⟨c, c', hc, ec⟩ := norm y y' h
  obtain ⟨e, e', he, ee⟩ := norm z z' h'
  rw [ec, ee]
  exact dir_const hm hc he

/-! ## The two-coordinate laws of the core -/

variable [Nonempty (CoreT F)]

/-- The probability that the coordinates `i, j` of the core are `y, y'`. -/
noncomputable def wPair (i j : Fin 4) (y y' : F) : ℝ :=
  (coreLaw (F := F)).expect fun C => if C.1 i = y ∧ C.1 j = y' then 1 else 0

theorem expect_pair (i j : Fin 4) (g : F → F → ℝ) :
    (coreLaw (F := F)).expect (fun C => g (C.1 i) (C.1 j)) =
      ∑ y, ∑ y', wPair i j y y' * g y y' := by
  unfold wPair
  have e : ∀ C : CoreT F, g (C.1 i) (C.1 j) =
      ∑ y, ∑ y', (if C.1 i = y ∧ C.1 j = y' then (1 : ℝ) else 0) * g y y' := by
    intro C
    rw [sum_eq_single (C.1 i) (fun y _ hy => sum_eq_zero fun y' _ => by simp [Ne.symm hy])
      (by simp), sum_eq_single (C.1 j) (fun y' _ hy' => by simp [Ne.symm hy']) (by simp)]
    simp
  rw [(coreLaw (F := F)).expect_congr e]
  unfold FiniteLaw.expect
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y' _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun C _ => ?_
  ring

theorem wPair_affine (i j : Fin 4) (α β : F) (hα : quadraticChar F α = 1) (y y' : F) :
    wPair i j (α * y + β) (α * y' + β) = wPair i j y y' := by
  have hα0 := ne_zero_of_chi hα
  unfold wPair coreLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  rw [← Equiv.sum_comp (affCoreEquiv hα β)]
  refine sum_congr rfl fun C _ => ?_
  simp only [affCoreEquiv, Equiv.coe_fn_mk, affCore]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mul_left_cancel₀ hα0 (add_right_cancel h1), mul_left_cancel₀ hα0 (add_right_cancel h2)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    exact ⟨rfl, rfl⟩

theorem sum_wPair (i j : Fin 4) : ∑ y : F, ∑ y' : F, wPair i j y y' = 1 := by
  have := expect_pair (F := F) i j (fun (_ : F) (_ : F) => (1 : ℝ))
  simp only [mul_one, FiniteLaw.expect_const] at this
  exact this.symm

theorem wPair_diag (i j : Fin 4) (hij : i ≠ j) (y : F) : wPair i j y y = 0 := by
  unfold wPair
  have : ∀ C : CoreT F, (if C.1 i = y ∧ C.1 j = y then (1 : ℝ) else 0) = 0 := by
    intro C
    have hne : C.1 i ≠ C.1 j := C.2.1.ne hij
    split_ifs with h
    · exact absurd (h.1.trans h.2.symm) hne
    · rfl
  rw [(coreLaw (F := F)).expect_congr this, FiniteLaw.expect_const]

theorem sw01_0 : Equiv.swap (0 : Fin 4) 1 0 = 1 := by decide
theorem sw01_1 : Equiv.swap (0 : Fin 4) 1 1 = 0 := by decide
theorem sw01_2 : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
theorem sw01_3 : Equiv.swap (0 : Fin 4) 1 3 = 3 := by decide
theorem sw23_0 : Equiv.swap (2 : Fin 4) 3 0 = 0 := by decide
theorem sw23_1 : Equiv.swap (2 : Fin 4) 3 1 = 1 := by decide
theorem sw23_2 : Equiv.swap (2 : Fin 4) 3 2 = 3 := by decide
theorem sw23_3 : Equiv.swap (2 : Fin 4) 3 3 = 2 := by decide

/-- The exchange `a₀ ↔ a₁` of an admissible core. -/
def swapA (C : CoreT F) : CoreT F :=
  ⟨C.1 ∘ Equiv.swap 0 1, by
    obtain ⟨hinj, h20, h30, h21, h31⟩ := C.2
    refine ⟨hinj.comp (Equiv.injective _), ?_, ?_, ?_, ?_⟩
    · show quadraticChar F (C.1 (Equiv.swap 0 1 2) - C.1 (Equiv.swap 0 1 0)) = 1
      rw [sw01_2, sw01_0]; exact h21
    · show quadraticChar F (C.1 (Equiv.swap 0 1 3) - C.1 (Equiv.swap 0 1 0)) = 1
      rw [sw01_3, sw01_0]; exact h31
    · show quadraticChar F (C.1 (Equiv.swap 0 1 2) - C.1 (Equiv.swap 0 1 1)) = 1
      rw [sw01_2, sw01_1]; exact h20
    · show quadraticChar F (C.1 (Equiv.swap 0 1 3) - C.1 (Equiv.swap 0 1 1)) = 1
      rw [sw01_3, sw01_1]; exact h30⟩

/-- The exchange `c₀ ↔ c₁` of an admissible core. -/
def swapCc (C : CoreT F) : CoreT F :=
  ⟨C.1 ∘ Equiv.swap 2 3, by
    obtain ⟨hinj, h20, h30, h21, h31⟩ := C.2
    refine ⟨hinj.comp (Equiv.injective _), ?_, ?_, ?_, ?_⟩
    · show quadraticChar F (C.1 (Equiv.swap 2 3 2) - C.1 (Equiv.swap 2 3 0)) = 1
      rw [sw23_2, sw23_0]; exact h30
    · show quadraticChar F (C.1 (Equiv.swap 2 3 3) - C.1 (Equiv.swap 2 3 0)) = 1
      rw [sw23_3, sw23_0]; exact h20
    · show quadraticChar F (C.1 (Equiv.swap 2 3 2) - C.1 (Equiv.swap 2 3 1)) = 1
      rw [sw23_2, sw23_1]; exact h31
    · show quadraticChar F (C.1 (Equiv.swap 2 3 3) - C.1 (Equiv.swap 2 3 1)) = 1
      rw [sw23_3, sw23_1]; exact h21⟩

omit [Nonempty (CoreT F)] in
theorem swapA_invol (C : CoreT F) : swapA (swapA C) = C := by
  apply Subtype.ext; funext k; simp [swapA]

omit [Nonempty (CoreT F)] in
theorem swapCc_invol (C : CoreT F) : swapCc (swapCc C) = C := by
  apply Subtype.ext; funext k; simp [swapCc]

theorem wPair_swap01 (y y' : F) : wPair 0 1 y' y = wPair 0 1 y y' := by
  unfold wPair coreLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  let e : CoreT F ≃ CoreT F := ⟨swapA, swapA, swapA_invol, swapA_invol⟩
  rw [← Equiv.sum_comp e]
  refine sum_congr rfl fun C _ => ?_
  simp only [e, Equiv.coe_fn_mk, swapA, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  congr 1
  exact propext and_comm

theorem wPair_swap23 (y y' : F) : wPair 2 3 y' y = wPair 2 3 y y' := by
  unfold wPair coreLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  let e : CoreT F ≃ CoreT F := ⟨swapCc, swapCc, swapCc_invol, swapCc_invol⟩
  rw [← Equiv.sum_comp e]
  refine sum_congr rfl fun C _ => ?_
  simp only [e, Equiv.coe_fn_mk, swapCc, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  congr 1
  exact propext and_comm

/-! ## Uniformity of the two-coordinate laws -/

omit [DecidableEq F] [Nonempty (CoreT F)] in
theorem card_ne_one_sub : ((Fintype.card F : ℝ) - 1) ≠ 0 := by
  have : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  linarith

omit [Field F] [Nonempty (CoreT F)] in
theorem sum_offdiag_const (c : ℝ) :
    ∑ y : F, ∑ y' : F, (if y = y' then 0 else c) =
      (Fintype.card F : ℝ) * (Fintype.card F - 1) * c := by
  have e : ∀ y : F, ∑ y' : F, (if y = y' then (0 : ℝ) else c) = (Fintype.card F - 1) * c := by
    intro y
    have : ∀ y' : F, (if y = y' then (0 : ℝ) else c) = c - if y = y' then c else 0 := by
      intro y'; split_ifs <;> ring
    rw [sum_congr rfl fun y' _ => this y', sum_sub_distrib, sum_ite_eq univ y (fun _ => c)]
    simp only [sum_const, card_univ, nsmul_eq_mul, mem_univ, ↓reduceIte]
    ring
  rw [sum_congr rfl fun y _ => e y, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- **The same-side pairs are uniform**: if `wPair i j` is symmetric, then
`wPair i j y y' = 1/(p(p - 1))` for `y ≠ y'`. -/
theorem wPair_unif (hm1 : quadraticChar F (-1) = -1) {i j : Fin 4} (hij : i ≠ j)
    (hs : ∀ y y' : F, wPair i j y' y = wPair i j y y') {y y' : F} (h : y ≠ y') :
    wPair i j y y' = 1 / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
  have hc : ∀ z z' : F, wPair i j z z' = if z = z' then 0 else wPair i j y y' := by
    intro z z'
    split_ifs with hz
    · rw [hz]; exact wPair_diag i j hij z'
    · exact pair_const hm1 (m := wPair i j) (fun α β hα z z' => wPair_affine i j α β hα z z')
        (fun z z' => hs z z') hz h
  have htot := sum_wPair (F := F) i j
  rw [sum_congr rfl fun z _ => sum_congr rfl fun z' _ => hc z z', sum_offdiag_const] at htot
  have hp0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := card_ne_one_sub (F := F)
  field_simp
  linarith

omit [Nonempty (CoreT F)] in
/-- The number of directed pairs: `∑_{y,y'} 𝟙[χ(y' - y) = 1] = p(p - 1)/2`. -/
theorem card_dir (hF : ringChar F ≠ 2) :
    ∑ y : F, ∑ y' : F, (if quadraticChar F (y' - y) = 1 then (1 : ℝ) else 0) =
      (Fintype.card F : ℝ) * (Fintype.card F - 1) / 2 := by
  have hind : ∀ d : F,
      (if quadraticChar F d = 1 then (1 : ℝ) else 0) = (chi d ^ 2 + chi d) / 2 := by
    intro d
    by_cases hd : d = 0
    · subst hd; simp [chi]
    · rcases quadraticChar_dichotomy hd with h | h <;> simp [h, chi]
  have hsq : ∑ d : F, chi d ^ 2 = Fintype.card F - 1 := by
    have := sum_chi_mul_chi (F := F) hF 0 0
    simp only [sub_zero, ↓reduceIte] at this
    rw [← this]
    exact sum_congr rfl fun d _ => sq _
  have hlin : ∑ d : F, chi d = 0 := by
    have := sum_chi_shift (F := F) hF 0
    simpa using this
  have inner : ∀ y : F, ∑ y' : F, (if quadraticChar F (y' - y) = 1 then (1 : ℝ) else 0) =
      (Fintype.card F - 1) / 2 := by
    intro y
    rw [show (∑ y' : F, (if quadraticChar F (y' - y) = 1 then (1 : ℝ) else 0)) =
        ∑ d : F, (if quadraticChar F d = 1 then (1 : ℝ) else 0) from
      Fintype.sum_equiv (Equiv.subRight y) _ _ fun y' => rfl]
    rw [sum_congr rfl fun d _ => hind d, ← sum_div, sum_add_distrib, hsq, hlin]
    ring
  rw [sum_congr rfl fun y _ => inner y, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- **The directed pairs are uniform**: if `χ(C_j - C_i) = 1` on every admissible core, then
`wPair i j y y' = 2/(p(p - 1))` for `χ(y' - y) = 1`, and `0` off the directed pairs. -/
theorem wPair_dir (hF : ringChar F ≠ 2) {i j : Fin 4}
    (hdir : ∀ C : CoreT F, quadraticChar F (C.1 j - C.1 i) = 1) (z z' : F) :
    wPair i j z z' = if quadraticChar F (z' - z) = 1 then
      2 / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) else 0 := by
  have hzero : ∀ z z' : F, quadraticChar F (z' - z) ≠ 1 → wPair i j z z' = 0 := by
    intro z z' hzz
    unfold wPair
    have : ∀ C : CoreT F, (if C.1 i = z ∧ C.1 j = z' then (1 : ℝ) else 0) = 0 := by
      intro C
      split_ifs with hC
      · exfalso; apply hzz; rw [← hC.1, ← hC.2]; exact hdir C
      · rfl
    rw [(coreLaw (F := F)).expect_congr this, FiniteLaw.expect_const]
  -- a directed pair exists, by the support of `μ^core`
  obtain ⟨C₀⟩ := (inferInstance : Nonempty (CoreT F))
  set c := wPair i j (C₀.1 i) (C₀.1 j) with hcdef
  have hc : ∀ z z' : F, wPair i j z z' = if quadraticChar F (z' - z) = 1 then c else 0 := by
    intro z z'
    split_ifs with hzz
    · exact dir_const (m := wPair i j) (fun α β hα y y' => wPair_affine i j α β hα y y') hzz
        (hdir C₀)
    · exact hzero z z' hzz
  have htot := sum_wPair (F := F) i j
  have e : ∀ z z' : F, wPair i j z z' =
      c * (if quadraticChar F (z' - z) = 1 then (1 : ℝ) else 0) := by
    intro z z'; rw [hc]; split_ifs <;> ring
  rw [sum_congr rfl fun z _ => sum_congr rfl fun z' _ => e z z'] at htot
  simp only [← mul_sum] at htot
  rw [card_dir hF] at htot
  have hp0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := card_ne_one_sub (F := F)
  have hcv : c = 2 / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
    field_simp
    linarith
  rw [hc, hcv]

/-! ## The Grams of the core singletons -/

omit [Field F] [Nonempty (CoreT F)] in
theorem sum_offdiag_mul (h : F → ℝ) (h0 : ∑ z, h z = 0) (c : ℝ) :
    ∑ y : F, ∑ y' : F, (if y = y' then 0 else c) * (h y * h y') = -c * ∑ y, h y ^ 2 := by
  have e : ∀ y y' : F, (if y = y' then 0 else c) * (h y * h y') =
      c * (h y * h y') - if y = y' then c * (h y * h y') else 0 := by
    intro y y'; split_ifs <;> ring
  simp only [e, sum_sub_distrib]
  have h2 : ∀ y : F, (∑ y' : F, if y = y' then c * (h y * h y') else 0) = c * h y ^ 2 := by
    intro y
    rw [sum_ite_eq univ y (fun y' => c * (h y * h y'))]
    simp only [mem_univ, ↓reduceIte]
    ring
  simp only [h2, ← mul_sum]
  rw [← sum_mul, h0]
  ring

omit [Nonempty (CoreT F)] in
theorem sum_antisym (hm1 : quadraticChar F (-1) = -1) (h : F → ℝ) :
    ∑ y : F, ∑ y' : F, chi (y' - y) * (h y * h y') = 0 := by
  have hA : ∑ y : F, ∑ y' : F, chi (y' - y) * (h y * h y') =
      -∑ y : F, ∑ y' : F, chi (y' - y) * (h y * h y') := by
    conv_lhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun y' _ => ?_
    rw [chi_sub_comm hm1]
    ring
  linarith

/-- **Same-side core coordinates** (`(a₀, a₁)` or `(c₀, c₁)`): for real `h` of mean zero,
`E_C h(C_i)h(C_j) = -(∑h²)/(p(p - 1)) = -q/(1 - q) ‖h‖²`. -/
theorem core_cross_same (hm1 : quadraticChar F (-1) = -1) {i j : Fin 4} (hij : i ≠ j)
    (hs : ∀ y y' : F, wPair i j y' y = wPair i j y y') (h : F → ℝ) (h0 : ∑ z, h z = 0) :
    (coreLaw (F := F)).expect (fun C => h (C.1 i) * h (C.1 j)) =
      -(∑ z, h z ^ 2) / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
  rw [expect_pair i j (fun y y' => h y * h y')]
  have e : ∀ y y' : F, wPair i j y y' * (h y * h y') =
      (if y = y' then 0 else 1 / ((Fintype.card F : ℝ) * (Fintype.card F - 1))) *
        (h y * h y') := by
    intro y y'
    split_ifs with hy
    · rw [hy, wPair_diag i j hij]
    · rw [wPair_unif hm1 hij hs hy]
  rw [sum_congr rfl fun y _ => sum_congr rfl fun y' _ => e y y', sum_offdiag_mul h h0]
  ring

/-- **Directed core coordinates** (`(a_i, c_j)`): for real `h` of mean zero,
`E_C h(a_i)h(c_j) = -(∑h²)/(p(p - 1))`; the Paley part `⟨h, Φ̂h⟩` of `V_{a_i}^*V_{c_j}` vanishes
on real `h`. -/
theorem core_cross_dir (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) {i j : Fin 4}
    (hdir : ∀ C : CoreT F, quadraticChar F (C.1 j - C.1 i) = 1) (h : F → ℝ)
    (h0 : ∑ z, h z = 0) :
    (coreLaw (F := F)).expect (fun C => h (C.1 i) * h (C.1 j)) =
      -(∑ z, h z ^ 2) / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
  rw [expect_pair i j (fun y y' => h y * h y')]
  set c := 2 / ((Fintype.card F : ℝ) * (Fintype.card F - 1))
  have e : ∀ y y' : F, wPair i j y y' * (h y * h y') =
      c / 2 * ((if y = y' then 0 else 1) * (h y * h y')) +
        c / 2 * (chi (y' - y) * (h y * h y')) := by
    intro y y'
    rw [wPair_dir hF hdir]
    by_cases hy : y = y'
    · subst hy; simp [chi_zero]
    · have hd : y' - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
      rcases quadraticChar_dichotomy hd with hc | hc
      · simp only [hc, ↓reduceIte, hy, chi]; push_cast; ring
      · have : (-1 : ℤ) ≠ 1 := by decide
        simp only [hc, this, ↓reduceIte, hy, chi]; push_cast; ring
  rw [sum_congr rfl fun y _ => sum_congr rfl fun y' _ => e y y']
  simp only [sum_add_distrib, ← mul_sum]
  rw [sum_offdiag_mul h h0, sum_antisym hm1]
  ring

/-- The single coordinates: `E_C h(C_i)² = E_C h(C_j)² = (∑h²)/p` for a same-side pair. -/
theorem core_sq_same (hm1 : quadraticChar F (-1) = -1) {i j : Fin 4} (hij : i ≠ j)
    (hs : ∀ y y' : F, wPair i j y' y = wPair i j y y') (h : F → ℝ) :
    (coreLaw (F := F)).expect (fun C => h (C.1 i) * h (C.1 i)) = (∑ z, h z ^ 2) / Fintype.card F ∧
      (coreLaw (F := F)).expect (fun C => h (C.1 j) * h (C.1 j)) =
        (∑ z, h z ^ 2) / Fintype.card F := by
  have hp0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := card_ne_one_sub (F := F)
  set c := 1 / ((Fintype.card F : ℝ) * (Fintype.card F - 1))
  have hw : ∀ y y' : F, wPair i j y y' = if y = y' then 0 else c := by
    intro y y'
    split_ifs with hy
    · rw [hy, wPair_diag i j hij]
    · exact wPair_unif hm1 hij hs hy
  have row : ∀ y : F, ∑ y' : F, (if y = y' then (0 : ℝ) else c) = (Fintype.card F - 1) * c := by
    intro y
    have : ∀ y' : F, (if y = y' then (0 : ℝ) else c) = c - if y = y' then c else 0 := by
      intro y'; split_ifs <;> ring
    rw [sum_congr rfl fun y' _ => this y', sum_sub_distrib, sum_ite_eq univ y (fun _ => c)]
    simp only [sum_const, card_univ, nsmul_eq_mul, mem_univ, ↓reduceIte]
    ring
  have col : ∀ y' : F, ∑ y : F, (if y = y' then (0 : ℝ) else c) = (Fintype.card F - 1) * c := by
    intro y'
    have : ∀ y : F, (if y = y' then (0 : ℝ) else c) = c - if y = y' then c else 0 := by
      intro y; split_ifs <;> ring
    rw [sum_congr rfl fun y _ => this y, sum_sub_distrib, sum_ite_eq' univ y' (fun _ => c)]
    simp only [sum_const, card_univ, nsmul_eq_mul, mem_univ, ↓reduceIte]
    ring
  have hval : (Fintype.card F - 1) * c = 1 / Fintype.card F := by
    simp only [c]; field_simp
  constructor
  · rw [expect_pair i j (fun y _ => h y * h y)]
    simp only [hw]
    have : ∀ y : F, ∑ y' : F, (if y = y' then (0 : ℝ) else c) * (h y * h y) =
        h y ^ 2 * ((Fintype.card F - 1) * c) := by
      intro y; rw [← sum_mul, row]; ring
    rw [sum_congr rfl fun y _ => this y, ← sum_mul, hval]
    ring
  · rw [expect_pair i j (fun _ y' => h y' * h y'), sum_comm]
    simp only [hw]
    have : ∀ y' : F, ∑ y : F, (if y = y' then (0 : ℝ) else c) * (h y' * h y') =
        h y' ^ 2 * ((Fintype.card F - 1) * c) := by
      intro y'; rw [← sum_mul, col]; ring
    rw [sum_congr rfl fun y' _ => this y', ← sum_mul, hval]
    ring

/-- **The Grams of the core singletons** (`prop:l20-rank4`(a), proof): for real `h` of mean
zero, `E_C h(C_k)h(C_{k'}) = ‖h‖²` if `k = k'` and `-q/(1 - q)‖h‖²` otherwise,
`‖h‖² = (∑h²)/p`, `q/(1 - q) = 1/(p - 1)`. -/
theorem core_gram (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) (h : F → ℝ)
    (h0 : ∑ z, h z = 0) (k k' : Fin 4) :
    (coreLaw (F := F)).expect (fun C => h (C.1 k) * h (C.1 k')) =
      if k = k' then (∑ z, h z ^ 2) / Fintype.card F
      else -(∑ z, h z ^ 2) / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
  have s01 := core_sq_same hm1 (i := 0) (j := 1) (by decide) wPair_swap01 h
  have s23 := core_sq_same hm1 (i := 2) (j := 3) (by decide) wPair_swap23 h
  have c01 := core_cross_same hm1 (i := 0) (j := 1) (by decide) wPair_swap01 h h0
  have c23 := core_cross_same hm1 (i := 2) (j := 3) (by decide) wPair_swap23 h h0
  have d02 := core_cross_dir hm1 hF (i := 0) (j := 2) (fun C => C.2.2.1) h h0
  have d03 := core_cross_dir hm1 hF (i := 0) (j := 3) (fun C => C.2.2.2.1) h h0
  have d12 := core_cross_dir hm1 hF (i := 1) (j := 2) (fun C => C.2.2.2.2.1) h h0
  have d13 := core_cross_dir hm1 hF (i := 1) (j := 3) (fun C => C.2.2.2.2.2) h h0
  have comm : ∀ a b : Fin 4, (coreLaw (F := F)).expect (fun C => h (C.1 a) * h (C.1 b)) =
      (coreLaw (F := F)).expect (fun C => h (C.1 b) * h (C.1 a)) :=
    fun a b => (coreLaw (F := F)).expect_congr fun C => mul_comm _ _
  fin_cases k <;> fin_cases k' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Fin.isValue, ↓reduceIte, Fin.reduceEq]
  · exact s01.1
  · exact c01
  · exact d02
  · exact d03
  · rw [comm]; exact c01
  · exact s01.2
  · exact d12
  · exact d13
  · rw [comm]; exact d02
  · rw [comm]; exact d12
  · exact s23.1
  · exact c23
  · rw [comm]; exact d03
  · rw [comm]; exact d13
  · rw [comm]; exact c23
  · exact s23.2

/-- **`E_C(∑_k c_k h(C_k))² = (∑c_k² - q/(1 - q)((∑c_k)² - ∑c_k²))‖h‖²`** for real `h` of mean
zero (`prop:l20-rank4`(a)). -/
theorem core_lin_sq (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) (h : F → ℝ)
    (h0 : ∑ z, h z = 0) (c : Fin 4 → ℝ) :
    (coreLaw (F := F)).expect (fun C => (∑ k, c k * h (C.1 k)) ^ 2) =
      ((∑ k, c k ^ 2) - ((∑ k, c k) ^ 2 - ∑ k, c k ^ 2) / ((Fintype.card F : ℝ) - 1)) *
        ((∑ z, h z ^ 2) / Fintype.card F) := by
  have hp0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := card_ne_one_sub (F := F)
  have e : ∀ C : CoreT F, (∑ k, c k * h (C.1 k)) ^ 2 =
      ∑ k, ∑ k', c k * c k' * (h (C.1 k) * h (C.1 k')) := by
    intro C
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun k _ => sum_congr rfl fun k' _ => by ring
  rw [(coreLaw (F := F)).expect_congr e]
  have lin : ∀ (G : CoreT F → Fin 4 → Fin 4 → ℝ),
      (coreLaw (F := F)).expect (fun C => ∑ k, ∑ k', G C k k') =
        ∑ k, ∑ k', (coreLaw (F := F)).expect (fun C => G C k k') := by
    intro G
    unfold FiniteLaw.expect
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun k _ => by rw [sum_comm]
  rw [lin]
  simp only [FiniteLaw.expect_const_mul]
  simp only [core_gram hm1 hF h h0]
  simp only [Fin.sum_univ_four, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  field_simp
  ring

/-- **`𝐮^*𝐮 = I/(1 - q)`** (`prop:l20-rank4`(a)), as a quadratic form on real `h ∈ 𝓗`:
`E_C(𝐮h)² = ‖h‖²/(1 - q)` for `𝐮h = (h(a₀) + h(a₁) - h(c₀) - h(c₁))/2`. -/
theorem uvec_sq (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) (h : F → ℝ)
    (h0 : ∑ z, h z = 0) :
    (coreLaw (F := F)).expect (fun C => ((h (C.1 0) + h (C.1 1) - h (C.1 2) - h (C.1 3)) / 2) ^ 2) =
      1 / (1 - (Fintype.card F : ℝ)⁻¹) * ((∑ z, h z ^ 2) / Fintype.card F) := by
  have hl := core_lin_sq hm1 hF h h0 ![1 / 2, 1 / 2, -1 / 2, -1 / 2]
  have e : ∀ C : CoreT F, ((h (C.1 0) + h (C.1 1) - h (C.1 2) - h (C.1 3)) / 2) ^ 2 =
      (∑ k, (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ) k * h (C.1 k)) ^ 2 := by
    intro C
    simp only [Fin.sum_univ_four]
    simp
    ring
  rw [(coreLaw (F := F)).expect_congr e, hl]
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have h1 := card_ne_one_sub (F := F)
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have hcoef : (∑ k, (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ) k ^ 2 -
      ((∑ k, (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ) k) ^ 2 -
        ∑ k, (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ) k ^ 2) / ((Fintype.card F : ℝ) - 1)) =
      1 / (1 - (Fintype.card F : ℝ)⁻¹) := by
    norm_num [Fin.sum_univ_four]
    field_simp
    ring
  rw [hcoef]

/-- **`𝐰^*𝐰 = (1 - 4q)/(1 - q) I`** (`prop:l20-rank4`(a)), as a quadratic form on real `h ∈ 𝓗`:
`E_C(𝐰h)² = (1 - 4q)/(1 - q)‖h‖²` for `𝐰h = (h(a₀) + h(a₁) + h(c₀) + h(c₁))/2`; in particular
`‖𝐰‖ ≤ 1`. -/
theorem wvec_sq (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) (h : F → ℝ)
    (h0 : ∑ z, h z = 0) :
    (coreLaw (F := F)).expect (fun C => ((h (C.1 0) + h (C.1 1) + h (C.1 2) + h (C.1 3)) / 2) ^ 2) =
      (1 - 4 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) *
        ((∑ z, h z ^ 2) / Fintype.card F) := by
  have hl := core_lin_sq hm1 hF h h0 ![1 / 2, 1 / 2, 1 / 2, 1 / 2]
  have e : ∀ C : CoreT F, ((h (C.1 0) + h (C.1 1) + h (C.1 2) + h (C.1 3)) / 2) ^ 2 =
      (∑ k, (![1 / 2, 1 / 2, 1 / 2, 1 / 2] : Fin 4 → ℝ) k * h (C.1 k)) ^ 2 := by
    intro C
    simp only [Fin.sum_univ_four]
    simp
    ring
  rw [(coreLaw (F := F)).expect_congr e, hl]
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have h1 := card_ne_one_sub (F := F)
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have hcoef : (∑ k, (![1 / 2, 1 / 2, 1 / 2, 1 / 2] : Fin 4 → ℝ) k ^ 2 -
      ((∑ k, (![1 / 2, 1 / 2, 1 / 2, 1 / 2] : Fin 4 → ℝ) k) ^ 2 -
        ∑ k, (![1 / 2, 1 / 2, 1 / 2, 1 / 2] : Fin 4 → ℝ) k ^ 2) / ((Fintype.card F : ℝ) - 1)) =
      (1 - 4 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) := by
    norm_num [Fin.sum_univ_four]
    field_simp
    ring
  rw [hcoef]

/-! ## (b): the identities of `𝖪_⋆` behind the Grams of `W_⋆` -/

omit [Nonempty (CoreT F)] in
/-- `∑_z ℓ(z, C) = 0`. -/
theorem sum_ell (hF : ringChar F ≠ 2) (C : Fin 4 → F) : ∑ z, ell z C = 0 := by
  simp only [ell_four, sum_add_distrib, sum_sub_distrib, sum_neg_distrib, sum_chi_shift hF]
  ring

omit [Nonempty (CoreT F)] in
/-- **`E_z 𝖪_⋆ = \bar𝖪 - 1`** (proof of `prop:l20-rank4`(b)). -/
theorem sum_Kstar (hF : ringChar F ≠ 2) (C : Fin 4 → F) :
    ∑ z, Kstar z C = ∑ z, Kz z C - Fintype.card F := by
  simp only [Kstar, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, sum_ell hF]
  ring

omit [Nonempty (CoreT F)] in
/-- **`E_z 𝖪_⋆² = 6\bar𝖪 + 5`** (proof of `prop:l20-rank4`(b)): `16\bar𝖪 + 1 + 4 - 2\bar𝖪 - 8\bar𝖪`,
by `𝖪² = 16𝖪`, `𝖪ℓ = 4𝖪`, `E_zℓ² = 4`, `E_zℓ = 0`. -/
theorem sum_Kstar_sq (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) {C : Fin 4 → F}
    (hC : Adm C) : ∑ z, Kstar z C ^ 2 = 6 * ∑ z, Kz z C + 5 * Fintype.card F := by
  have e : ∀ z, Kstar z C ^ 2 = Kz z C ^ 2 + 1 + ell z C ^ 2 - 2 * Kz z C -
      2 * (Kz z C * ell z C) + 2 * ell z C := by
    intro z; unfold Kstar; ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul,
    mul_one]
  rw [sum_Kz_sq hm1 hC, sum_ell_sq hF hC.1, sum_ell hF,
    sum_congr rfl fun z _ => Kz_mul_ell hm1 hC z, ← mul_sum]
  ring

omit [Nonempty (CoreT F)] in
/-- **`E_z χ(z - x_k) 𝖪_⋆ = s_k(\bar𝖪 - 1)`** (proof of `prop:l20-rank4`(b)): where `𝖪 ≠ 0`,
`χ(z - x_k) = s_k`, and `E_z χ(z - x_k) ℓ = s_k`. -/
theorem sum_chi_Kstar (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) {C : Fin 4 → F}
    (hC : Adm C) (k : Fin 4) :
    ∑ z, chi (z - C k) * Kstar z C = sgn k * (∑ z, Kz z C - Fintype.card F) := by
  -- `χ(z - C_k) 𝖪 = s_k 𝖪`
  have hK : ∀ z, chi (z - C k) * Kz z C = sgn k * Kz z C := by
    intro z
    rcases Kz_dichotomy hm1 hC z with ⟨hA, h16⟩ | ⟨-, h0⟩
    · rw [h16]
      obtain ⟨a0, a1, a2, a3⟩ := hA
      fin_cases k
      · simp only [Fin.zero_eta, Fin.isValue] at a0 ⊢; rw [a0, sgn_zero]
      · simp only [Fin.mk_one, Fin.isValue] at a1 ⊢; rw [a1, sgn_one]
      · simp only [Fin.reduceFinMk, Fin.isValue] at a2 ⊢; rw [a2, sgn_two]
      · simp only [Fin.reduceFinMk, Fin.isValue] at a3 ⊢; rw [a3, sgn_three]
    · rw [h0]; ring
  -- `∑_z χ(z - C_k) ℓ = s_k p`
  have hl : ∑ z, chi (z - C k) * ell z C = sgn k * Fintype.card F := by
    have e : ∀ z, chi (z - C k) * ell z C = ∑ k', sgn k' * (chi (z - C k) * chi (z - C k')) := by
      intro z; rw [ell, mul_sum]; exact sum_congr rfl fun k' _ => by ring
    rw [sum_congr rfl fun z _ => e z, sum_comm]
    simp only [← mul_sum, sum_chi_mul_chi hF, hC.1.eq_iff]
    fin_cases k <;> simp [Fin.sum_univ_four, sgn_zero, sgn_one, sgn_two, sgn_three] <;> ring
  have e : ∀ z, chi (z - C k) * Kstar z C =
      chi (z - C k) * Kz z C - chi (z - C k) - chi (z - C k) * ell z C := by
    intro z; unfold Kstar; ring
  rw [sum_congr rfl fun z _ => e z, sum_sub_distrib, sum_sub_distrib,
    sum_congr rfl fun z _ => hK z, ← mul_sum, sum_chi_shift hF, hl]
  ring

end Sarkozy.L20Cap
