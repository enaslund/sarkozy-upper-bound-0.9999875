module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Root sums and the graded extension count (`thm:weil`(b), `eq:two-root`, `lem:extension`)

`paper/sections/04_notation.tex` (`thm:weil`) and `paper/sections/12_labellings.tex`
(`lem:extension`). Throughout `F` is a finite field of odd characteristic with `q` elements and
quadratic character `χ = quadraticChar F` (for `F = 𝔽_p`, `q = p`). For a finite set `S` of
roots, `rootSum S = ∑_x χ(∏_{a∈S} (x - a))` is the paper's `W_S`.

* `WeilBound F` is Weil's theorem `thm:weil`(a), `|W_S| ≤ (|S| - 1)√q` for nonempty `S`. It is
  the external input (the paper cites Iwaniec–Kowalski, Thm 11.23) and enters only as a
  hypothesis.
* `rootSum_even_add_one`: the substitution `x = a₀ + 1/u` of the paper's proof of (b),
  `W_S + 1 = χ(c) W_T` with `|T| = |S| - 1`, for every set `S` of even size; unconditional.
  Consequences: `two_root` (`eq:two-root`, `W_{a,b} = -1` for `a ≠ b`, unconditional) and
  `weil_even` (`thm:weil`(b) from (a)).
* `soft_count_bound` is `lem:extension`(a): `|𝔖 - q| ≤ a_t √q + b_t`, with the paper's graded
  coefficients `a_t = (t-3)2^{t-1} + 2`, `b_t = 2^{t-1} - 1` (`a_0 = b_0 = 0`), from
  `WeilBound`.
* `extension_bounds` is `lem:extension`(b), (c):
  `|Φ| ≤ q 2^{-t} + 2^{-t}(a_t √q + b_t)` whatever the excluded set, and
  `|Φ| ≥ q 2^{-t} - 2^{-t}(a_t √q + b_t) - |𝒳|`; dividing by `q 2^{-t}` gives the forms
  `1 ± e_t^±` of the paper.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The root sum `W_S = ∑_x χ(∏_{a∈S}(x - a))`. -/
def rootSum (S : Finset F) : ℤ := ∑ x, quadraticChar F (∏ a ∈ S, (x - a))

variable (F) in
/-- **Weil's bound** `thm:weil`(a), as a hypothesis: `|W_S| ≤ (|S| - 1)√q` for nonempty `S`. -/
def WeilBound : Prop :=
  ∀ S : Finset F, S.Nonempty →
    |(rootSum S : ℝ)| ≤ ((S.card : ℝ) - 1) * Real.sqrt (Fintype.card F)

theorem rootSum_empty : rootSum (∅ : Finset F) = Fintype.card F := by
  simp [rootSum]

theorem rootSum_singleton (hF : ringChar F ≠ 2) (a : F) : rootSum {a} = 0 := by
  simp only [rootSum, prod_singleton]
  rw [← quadraticChar_sum_zero hF]
  exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

theorem quadraticChar_abs_eq_one {c : F} (hc : c ≠ 0) : |quadraticChar F c| = 1 := by
  rcases quadraticChar_dichotomy hc with h | h <;> simp [h]

/-- The substitution of the proof of `thm:weil`(b): for `S` of even size containing `a₀`,
`W_S + 1 = χ(c) W_T` with `c = ∏_{b ∈ S \ {a₀}} (a₀ - b)` and `T` the image of `S \ {a₀}` under
`b ↦ (b - a₀)⁻¹`, a set with `|S| - 1` elements. -/
theorem rootSum_even_add_one {S : Finset F} {a₀ : F} (ha₀ : a₀ ∈ S) (hS : Even S.card) :
    rootSum S + 1 = quadraticChar F (∏ b ∈ S.erase a₀, (a₀ - b)) *
        rootSum ((S.erase a₀).image fun b => (b - a₀)⁻¹) ∧
      ((S.erase a₀).image fun b => (b - a₀)⁻¹).card = S.card - 1 := by
  set S' := S.erase a₀
  set β : F → F := fun b => (b - a₀)⁻¹
  set c := ∏ b ∈ S', (a₀ - b)
  have hinj : Set.InjOn β S' := by
    intro x _ y _ hxy
    have := inv_injective hxy
    simpa using this
  have hcard : (S'.image β).card = S.card - 1 := by
    rw [card_image_of_injOn hinj, card_erase_of_mem ha₀]
  refine ⟨?_, hcard⟩
  have hc : c ≠ 0 := prod_ne_zero_iff.mpr fun b hb => sub_ne_zero.mpr (Ne.symm (ne_of_mem_erase hb))
  -- the pointwise identity at `x = a₀ + u⁻¹`
  set g : F → F := fun u => ∏ b ∈ S', (u - β b)
  have hpoint (u : F) : quadraticChar F (∏ a ∈ S, (a₀ + u⁻¹ - a)) =
      if u = 0 then 0 else quadraticChar F c * quadraticChar F (g u) := by
    split_ifs with hu
    · rw [hu, inv_zero, add_zero, prod_eq_zero ha₀ (sub_self a₀), quadraticChar_zero]
    · have hsplit : ∏ a ∈ S, (a₀ + u⁻¹ - a) = (a₀ + u⁻¹ - a₀) * ∏ b ∈ S', (a₀ + u⁻¹ - b) :=
        (mul_prod_erase S _ ha₀).symm
      have hfac : ∀ b ∈ S', a₀ + u⁻¹ - b = (a₀ - b) * (u - β b) * u⁻¹ := by
        intro b hb
        have hb0 : b - a₀ ≠ 0 := sub_ne_zero.mpr (ne_of_mem_erase hb)
        simp only [β]
        field_simp
        ring
      rw [hsplit, prod_congr rfl hfac, prod_mul_distrib, prod_mul_distrib, prod_const,
        add_sub_cancel_left]
      have hu' : u⁻¹ ≠ 0 := inv_ne_zero hu
      have hpow : quadraticChar F (u⁻¹ * u⁻¹ ^ S'.card) = 1 := by
        rw [← pow_succ', card_erase_of_mem ha₀]
        obtain ⟨k, hk⟩ := hS
        have hk1 : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (card_pos.mpr ⟨a₀, ha₀⟩)
        rw [hk1, hk, ← two_mul, pow_mul, map_pow, quadraticChar_sq_one' hu', one_pow]
      calc quadraticChar F (u⁻¹ * (c * g u * u⁻¹ ^ S'.card))
          = quadraticChar F (u⁻¹ * u⁻¹ ^ S'.card) * (quadraticChar F c * quadraticChar F (g u)) := by
            rw [← map_mul, ← map_mul]; ring_nf
        _ = quadraticChar F c * quadraticChar F (g u) := by rw [hpow, one_mul]
  -- sum over `x` through the bijection `u ↦ a₀ + u⁻¹`
  have hsum : rootSum S = ∑ u, (if u = 0 then 0 else quadraticChar F c * quadraticChar F (g u)) := by
    unfold rootSum
    rw [← Fintype.sum_equiv ((Equiv.inv F).trans (Equiv.addLeft a₀))
      (fun u => quadraticChar F (∏ a ∈ S, (((Equiv.inv F).trans (Equiv.addLeft a₀)) u - a)))
      (fun x => quadraticChar F (∏ a ∈ S, (x - a))) (fun _ => rfl)]
    exact Fintype.sum_congr _ _ fun u => by simpa using hpoint u
  have hg0 : quadraticChar F c * quadraticChar F (g 0) = 1 := by
    have : g 0 = c⁻¹ := by
      simp only [g, β, zero_sub, c, ← prod_inv_distrib]
      refine prod_congr rfl fun b _ => ?_
      rw [← inv_neg, neg_sub]
    rw [this, ← map_mul, mul_inv_cancel₀ hc, map_one]
  have hT : rootSum (S'.image β) = ∑ u, quadraticChar F (g u) := by
    unfold rootSum
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [prod_image hinj]
  rw [hsum, hT, Finset.mul_sum]
  rw [Fintype.sum_eq_add_sum_compl 0, Fintype.sum_eq_add_sum_compl 0 (fun u => _ * _)]
  simp only [↓reduceIte]
  rw [← hg0]
  have hrest : ∑ u ∈ ({0}ᶜ : Finset F), (if u = 0 then (0 : ℤ) else quadraticChar F c * quadraticChar F (g u)) =
      ∑ u ∈ ({0}ᶜ : Finset F), quadraticChar F c * quadraticChar F (g u) :=
    sum_congr rfl fun u hu => by
      have hu0 : u ≠ 0 := by simpa using hu
      simp only [hu0, ↓reduceIte]
  rw [hrest]
  ring

/-- **The two-root identity** `eq:two-root`: `∑_x χ((x - a)(x - b)) = -1` for `a ≠ b`. -/
theorem two_root (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    rootSum ({a, b} : Finset F) = -1 := by
  have hmem : a ∈ ({a, b} : Finset F) := mem_insert_self a {b}
  have hcard2 : ({a, b} : Finset F).card = 2 := card_pair hab
  obtain ⟨h, hc⟩ := rootSum_even_add_one hmem (by rw [hcard2]; exact even_two)
  rw [hcard2] at hc
  obtain ⟨y, hy⟩ := card_eq_one.mp hc
  rw [hy, rootSum_singleton hF, mul_zero] at h
  linarith

/-- **`thm:weil`(b) from (a)**: for `|S| ≥ 2` even, `|W_S + 1| ≤ (|S| - 2)√q`. -/
theorem weil_even (hW : WeilBound F) {S : Finset F} (hS : Even S.card) (h2 : 2 ≤ S.card) :
    |(rootSum S : ℝ) + 1| ≤ ((S.card : ℝ) - 2) * Real.sqrt (Fintype.card F) := by
  obtain ⟨a₀, ha₀⟩ : S.Nonempty := card_pos.mp (by omega)
  obtain ⟨h, hc⟩ := rootSum_even_add_one ha₀ hS
  set T := (S.erase a₀).image fun b => (b - a₀)⁻¹
  have hTne : T.Nonempty := card_pos.mp (by omega)
  have hcne : (∏ b ∈ S.erase a₀, (a₀ - b)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun b hb => sub_ne_zero.mpr (Ne.symm (ne_of_mem_erase hb))
  have hcast : (rootSum S : ℝ) + 1 =
      (quadraticChar F (∏ b ∈ S.erase a₀, (a₀ - b)) : ℝ) * (rootSum T : ℝ) := by
    exact_mod_cast h
  rw [hcast, abs_mul]
  have hχ : |(quadraticChar F (∏ b ∈ S.erase a₀, (a₀ - b)) : ℝ)| = 1 := by
    exact_mod_cast quadraticChar_abs_eq_one hcne
  rw [hχ, one_mul]
  have hb := hW T hTne
  rw [hc] at hb
  have : ((S.card - 1 : ℕ) : ℝ) - 1 = (S.card : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rwa [this] at hb

/-! ## The graded extension count -/

/-- The graded coefficient `a_t = (t-3)2^{t-1} + 2` (`a_0 = 0`) of `eq:graphs:graded`. -/
noncomputable def gradedA (t : ℕ) : ℝ := if t = 0 then 0 else ((t : ℝ) - 3) * 2 ^ (t - 1) + 2

/-- The graded coefficient `b_t = 2^{t-1} - 1` (`b_0 = 0`) of `eq:graphs:graded`. -/
noncomputable def gradedB (t : ℕ) : ℝ := if t = 0 then 0 else 2 ^ (t - 1) - 1

/-- The bound for one root set of size `k ≥ 1`: `(k - 1 - [k even])√q + [k even]`. -/
noncomputable def subsetBound (σ : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) - 1 - (1 + (-1) ^ k) / 2) * σ + (1 + (-1) ^ k) / 2

theorem sum_subsetBound (σ : ℝ) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∑ S ∈ ((univ : Finset ι).powerset.erase ∅), subsetBound σ S.card =
      gradedA (Fintype.card ι) * σ + gradedB (Fintype.card ι) := by
  set t := Fintype.card ι with htdef
  rcases Nat.eq_zero_or_pos t with h0 | ht
  · have hemp : (univ : Finset ι) = ∅ := univ_eq_empty_iff.mpr (Fintype.card_eq_zero_iff.mp h0)
    simp [hemp, gradedA, gradedB, h0]
  have hall : ∑ S ∈ (univ : Finset ι).powerset, subsetBound σ S.card =
      ((t : ℝ) * 2 ^ (t - 1) - 2 ^ t - 2 ^ (t - 1)) * σ + 2 ^ (t - 1) := by
    have hk : ∑ S ∈ (univ : Finset ι).powerset, ((S.card : ℝ)) = t * 2 ^ (t - 1) := by
      rw [sum_powerset_apply_card (fun k => (k : ℝ)), card_univ, ← htdef]
      have := Nat.sum_range_mul_choose t
      have hc : ((∑ i ∈ range (t + 1), i * t.choose i : ℕ) : ℝ) = ((t * 2 ^ (t - 1) : ℕ) : ℝ) := by
        rw [this]
      push_cast at hc
      rw [← hc]
      refine sum_congr rfl fun i _ => ?_
      rw [nsmul_eq_mul]; ring
    have h1 : ∑ S ∈ (univ : Finset ι).powerset, (1 : ℝ) = 2 ^ t := by
      rw [sum_const, card_powerset, card_univ, ← htdef, nsmul_eq_mul, mul_one]
      push_cast; ring
    have hneg : ∑ S ∈ (univ : Finset ι).powerset, ((-1 : ℝ) ^ S.card) = 0 := by
      have := sum_powerset_neg_one_pow_card_of_nonempty
        (x := (univ : Finset ι)) (univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp ht))
      exact_mod_cast this
    have h2 : (2 : ℝ) ^ Fintype.card ι = 2 * 2 ^ (t - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [subsetBound]
    have hexp : ∀ S : Finset ι, (((S.card : ℝ) - 1 - (1 + (-1) ^ S.card) / 2) * σ +
        (1 + (-1) ^ S.card) / 2) = σ * (S.card : ℝ) + (1 / 2 - 3 / 2 * σ) * 1 +
          (1 / 2 - σ / 2) * (-1) ^ S.card := fun S => by ring
    simp only [hexp, sum_add_distrib, ← mul_sum, hk, h1, hneg]
    rw [h2]; ring
  have hempty : subsetBound σ (∅ : Finset ι).card = 1 - 2 * σ := by
    simp [subsetBound]; ring
  rw [← add_sum_erase _ _ (empty_mem_powerset _), hempty] at hall
  have h2 : (2 : ℝ) ^ Fintype.card ι = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ']; congr 1; omega
  simp only [gradedA, gradedB, Nat.pos_iff_ne_zero.mp ht, ↓reduceIte]
  rw [h2] at hall
  linarith

/-- The per-set bound: `|W_S| ≤ subsetBound √q |S|` for every nonempty `S`. -/
theorem abs_rootSum_le (hW : WeilBound F) {S : Finset F} (hS : S.Nonempty) :
    |(rootSum S : ℝ)| ≤ subsetBound (Real.sqrt (Fintype.card F)) S.card := by
  rcases Nat.even_or_odd S.card with he | ho
  · have h2 : 2 ≤ S.card := by
      obtain ⟨k, hk⟩ := he
      have := card_pos.mpr hS
      omega
    have hb := weil_even hW he h2
    have hneg : ((-1 : ℝ) ^ S.card) = 1 := he.neg_one_pow
    simp only [subsetBound, hneg]
    have := abs_sub_abs_le_abs_sub ((rootSum S : ℝ)) (-1)
    rw [sub_neg_eq_add] at this
    norm_num at this ⊢
    nlinarith [this, hb]
  · have hb := hW S hS
    have hneg : ((-1 : ℝ) ^ S.card) = -1 := ho.neg_one_pow
    simp only [subsetBound, hneg]
    norm_num
    linarith

/-- **`lem:extension`(a), the soft count**: for distinct roots `β_i` and signs `s_i = ±1`,
`|∑_x ∏_i (1 + s_i χ(x - β_i)) - q| ≤ a_t √q + b_t`. -/
theorem soft_count_bound (hW : WeilBound F) {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → F) (hβ : Function.Injective β)
    (s : ι → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    |((∑ x, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ) - Fintype.card F| ≤
      gradedA (Fintype.card ι) * Real.sqrt (Fintype.card F) + gradedB (Fintype.card ι) := by
  -- expansion over subsets of roots
  have hexp : (∑ x, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) =
      ∑ S ∈ (univ : Finset ι).powerset, (∏ i ∈ S, s i) * rootSum (S.image β) := by
    simp_rw [prod_one_add]
    rw [sum_comm]
    refine sum_congr rfl fun S _ => ?_
    unfold rootSum
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [prod_mul_distrib, prod_image (fun i _ j _ h => hβ h), map_prod]
  have hsign : ∀ S : Finset ι, |∏ i ∈ S, (s i : ℝ)| = 1 := by
    intro S
    rw [abs_prod]
    exact prod_eq_one fun i _ => by rcases hs i with h | h <;> simp [h]
  rw [hexp, ← add_sum_erase _ _ (empty_mem_powerset _)]
  simp only [prod_empty, image_empty, rootSum_empty, one_mul]
  push_cast
  rw [add_sub_cancel_left, ← sum_subsetBound _ ι]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun S hS => ?_)
  have hSne : S.Nonempty := nonempty_iff_ne_empty.mpr (ne_of_mem_erase hS)
  rw [abs_mul, hsign, one_mul]
  have hcard : (S.image β).card = S.card := card_image_of_injective _ hβ
  have := abs_rootSum_le hW (hSne.image β)
  rwa [hcard] at this

/-- The pointwise value of the soft-count product: `∏_i (1 + s_i χ(x - β_i))` is `2^t` times the
indicator of the conditions `χ(x - β_i) = s_i` when `x` is not a root, and lies in `[0, 2^t]`. -/
theorem prod_soft_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → F) (s : ι → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    {x : F} (hx : ∀ i, x ≠ β i) :
    (∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) =
      if ∀ i, quadraticChar F (x - β i) = s i then 2 ^ Fintype.card ι else 0 := by
  have hval : ∀ i, (1 + s i * quadraticChar F (x - β i)) =
      if quadraticChar F (x - β i) = s i then 2 else 0 := by
    intro i
    have hne : x - β i ≠ 0 := sub_ne_zero.mpr (hx i)
    rcases quadraticChar_dichotomy hne with h | h <;> rcases hs i with h' | h' <;> simp [h, h']
  simp_rw [hval]
  split_ifs with hall
  · rw [prod_congr rfl (g := fun _ => (2 : ℤ)) fun i _ => by simp only [hall i, ↓reduceIte],
      prod_const, card_univ]
  · simp only [not_forall] at hall
    obtain ⟨i, hi⟩ := hall
    exact prod_eq_zero (mem_univ i) (by simp only [hi, ↓reduceIte])

theorem prod_soft_nonneg_le {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → F) (s : ι → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (x : F) :
    0 ≤ (∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) ∧
      (∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) ≤ 2 ^ Fintype.card ι := by
  have hfac : ∀ i, 0 ≤ (1 + s i * quadraticChar F (x - β i)) ∧
      (1 + s i * quadraticChar F (x - β i)) ≤ 2 := by
    intro i
    by_cases h0 : x - β i = 0
    · simp [h0]
    · rcases quadraticChar_dichotomy h0 with h | h <;> rcases hs i with h' | h' <;> simp [h, h']
  refine ⟨prod_nonneg fun i _ => (hfac i).1, ?_⟩
  calc (∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) ≤ ∏ _i : ι, (2 : ℤ) :=
        prod_le_prod₀ (fun i _ => (hfac i).1) (fun i _ => (hfac i).2)
    _ = 2 ^ Fintype.card ι := by rw [prod_const, card_univ]

/-- The admissible labels `Φ = {x ∉ 𝒳 : χ(x - β_i) = s_i ∀ i}` of `lem:extension`. -/
def admissible {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → F) (s : ι → ℤ) (𝒳 : Finset F) : Finset F :=
  univ.filter fun x => x ∉ 𝒳 ∧ ∀ i, quadraticChar F (x - β i) = s i

/-- The split `eq:ext:split`: `2^t |Φ| = 𝔖 - ∑_{x∈𝒳} ∏_i(…)`. -/
theorem two_pow_card_admissible {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → F) (s : ι → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (𝒳 : Finset F) (h𝒳 : ∀ i, β i ∈ 𝒳) :
    (2 ^ Fintype.card ι * (admissible β s 𝒳).card : ℤ) =
      (∑ x, ∏ i, (1 + s i * quadraticChar F (x - β i))) -
        ∑ x ∈ 𝒳, ∏ i, (1 + s i * quadraticChar F (x - β i)) := by
  rw [← sum_compl_add_sum 𝒳, add_sub_cancel_right]
  have hpt : ∀ x ∈ 𝒳ᶜ, (∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) =
      if ∀ i, quadraticChar F (x - β i) = s i then 2 ^ Fintype.card ι else 0 := by
    intro x hx
    refine prod_soft_eq β s hs fun i h => ?_
    rw [h] at hx
    exact (mem_compl.mp hx) (h𝒳 i)
  rw [sum_congr rfl hpt, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  · unfold admissible
    congr 1
    ext x
    simp [mem_filter, mem_compl]

/-- **`lem:extension`(b), (c)**: with `𝔈 = a_t √q + b_t`,
`q - 𝔈 - 2^t|𝒳| ≤ 2^t |Φ| ≤ q + 𝔈` whenever the excluded set `𝒳` contains the roots. -/
theorem extension_bounds (hW : WeilBound F) {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → F) (hβ : Function.Injective β)
    (s : ι → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (𝒳 : Finset F) (h𝒳 : ∀ i, β i ∈ 𝒳) :
    (2 : ℝ) ^ Fintype.card ι * (admissible β s 𝒳).card ≤
        Fintype.card F + (gradedA (Fintype.card ι) * Real.sqrt (Fintype.card F) + gradedB (Fintype.card ι)) ∧
      (Fintype.card F : ℝ) - (gradedA (Fintype.card ι) * Real.sqrt (Fintype.card F) + gradedB (Fintype.card ι)) -
          2 ^ Fintype.card ι * 𝒳.card ≤ 2 ^ Fintype.card ι * (admissible β s 𝒳).card := by
  have hsplit := two_pow_card_admissible β s hs 𝒳 h𝒳
  have hsoft := soft_count_bound hW β hβ s hs
  have hX0 : 0 ≤ (∑ x ∈ 𝒳, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) :=
    sum_nonneg fun x _ => (prod_soft_nonneg_le β s hs x).1
  have hX1 : (∑ x ∈ 𝒳, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) ≤ 2 ^ Fintype.card ι * 𝒳.card := by
    calc (∑ x ∈ 𝒳, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) ≤ ∑ _x ∈ 𝒳, (2 : ℤ) ^ Fintype.card ι :=
          sum_le_sum fun x _ => (prod_soft_nonneg_le β s hs x).2
      _ = 2 ^ Fintype.card ι * 𝒳.card := by rw [sum_const, nsmul_eq_mul, mul_comm]
  have hsplitR : (2 : ℝ) ^ Fintype.card ι * (admissible β s 𝒳).card =
      ((∑ x, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ) -
        ((∑ x ∈ 𝒳, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ) := by
    exact_mod_cast hsplit
  have hX0R : (0 : ℝ) ≤ ((∑ x ∈ 𝒳, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ) := by
    exact_mod_cast hX0
  have hX1R : ((∑ x ∈ 𝒳, ∏ i, (1 + s i * quadraticChar F (x - β i)) : ℤ) : ℝ) ≤
      (2 : ℝ) ^ Fintype.card ι * 𝒳.card := by exact_mod_cast hX1
  have habs := abs_le.mp hsoft
  constructor <;> linarith [habs.1, habs.2]

end Sarkozy.Labellings
