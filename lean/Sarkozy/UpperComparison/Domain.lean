module

public import Sarkozy.Certificates.Majorant

@[expose] public section

/-!
# The domain of the upper formulas (`lem:record:domain`)

`paper/sections/26_upper_comparison.tex`, subsection "A bound at a band start holds at every
larger prime in the band", `lem:record:domain` and the block gates `eq:upper-block-gate`.

The lemma has three steps. Step 1 (the size of `p` enters the formulas (F1)–(F9) only through
their gates) is a reading of the cited formulas and is not a separate statement. Steps 2 and 3
are formalized here.

**Step 2, part (i): monotonicity in `(r, l)`.** Every scalar error of a prime-level gate, and
every normalized coefficient, is an admissible function of `r` and of the block count `l`
(`def:majorant`, `lem:majorant` (i)–(iii), `Sarkozy.Majorant`). The box is
`UpperBox r₀ l₀ = [0, r₀] × [0, l₀]` with the componentwise order and the endpoint
`(r₀, l₀)` (`UpperBox.top`). Proved:
* `domain_gates`: a finite family of admissible gate quantities whose strict gates hold at the
  endpoint satisfies them on the whole box;
* `domain_coeffs`: an admissible normalized coefficient is at most its endpoint value;
* `primePoint`, `primePoint_le_top`: a prime `p ≥ p₀ > 1` with block count `l ≤ L'/log p₀` is a
  point of the box with `r₀ = p₀^{-1/2}`, `l₀ = L'/log p₀`, below the endpoint;
* `block_count_le`: a block of primes `≥ X ≥ p₀` with product at most `e^{L'}` has at most
  `L'/log p₀` primes (`lem:majorant`(c));
* `prime_coeff_le`: the value `r_p^d κ` of a coefficient at `p` is at most `r_p^d κ(r₀, l₀)`.

The admissibility of each concrete error of (F1)–(F9) is the content of the cited
`lem:majorant` rules (`Sarkozy.Majorant.admissible_*`); here it is a hypothesis of
`domain_gates` and `domain_coeffs`, one per gate.

**Step 3, part (ii): blocks.** By the closing clause of `lem:sector`(b), the norms of the
symmetric and skew parts of the block difference of a changed record are the maxima, over the
nonempty sets `S` of primes of the block, of the norms of their restrictions to the sector of
`S`: for `S = {p}` the parts of the prime difference, and for `|S| ≥ 2` at most
`∏_S δ + ∏_S δ'` (respectively `∏_S δ'`, the old law being self-adjoint), where `δ_p`, `δ'_p` are
the centred norms of the old and new laws at `p`. Proved:
* `prod_le_two`: `∏_S δ ≤ δ_j δ_k` for two distinct primes `j, k ∈ S` when `0 ≤ δ ≤ 1`;
* `sector_bound_two`: the block gates `c_old² + c_new² ≤ C^s r₀`, `c_new² ≤ C^a r₀`
  (`eq:upper-block-gate`) and `δ_p ≤ c_old r_p/r₀`, `δ'_p ≤ c_new r_p/r₀` give the bounds
  `C^s b^{-1/2}` and `C^a b^{-1/2}` on the sectors with `|S| ≥ 2`;
* `block_sectors_le`: all sectors, given the sector bounds of `lem:sector` (hypotheses);
* `block_gate_oneway`, `block_gate_forest`, `block_gate_forest_diff`, `block_gate_dense`: the
  block gates follow from the gates of (F7), of `prop:forest-records`(c) (FF, and FE/EF) and of
  `prop:dense-comparison`(c), `prop:le-mixture`; `dense_coef_ge` is the inequality
  `k r₀ ≤ e^{ℓ₀}(Γ k r₀ + E + 2F(C + u))` used for the dense laws (`e^{ℓ₀} ≥ 1`, `Γ ≥ 1`).

Here `r_p = p^{-1/2}`, `r₀ = p₀^{-1/2}` and `r_b = b^{-1/2}` for the least prime `b` of the
block; they enter as reals with the order relations the lemma uses.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperComparison

open Sarkozy.Majorant

/-! ## Step 2: the box and the endpoint -/

/-- The box `[0, r₀] × [0, l₀]` of `(r, l)` (`lem:record:domain`, Step 2), ordered
componentwise. -/
abbrev UpperBox (r₀ l₀ : ℝ) : Type := {x : ℝ × ℝ // 0 ≤ x.1 ∧ x.1 ≤ r₀ ∧ 0 ≤ x.2 ∧ x.2 ≤ l₀}

/-- The endpoint `(r₀, l₀)` of the box: the evaluation point `r₀ = p₀^{-1/2}` with the block
count `l₀ = L'/log p₀`. -/
def UpperBox.top {r₀ l₀ : ℝ} (hr : 0 ≤ r₀) (hl : 0 ≤ l₀) : UpperBox r₀ l₀ :=
  ⟨(r₀, l₀), hr, le_rfl, hl, le_rfl⟩

theorem UpperBox.le_top {r₀ l₀ : ℝ} (hr : 0 ≤ r₀) (hl : 0 ≤ l₀) (x : UpperBox r₀ l₀) :
    x ≤ UpperBox.top hr hl := by
  show x.1 ≤ (r₀, l₀)
  exact ⟨x.2.2.1, x.2.2.2.2⟩

/-- **`lem:record:domain`(i), the gates.** If every gate quantity `g_i` is admissible on the box
(`lem:majorant`) and its strict gate `g_i < θ_i` holds at the endpoint `(r₀, l₀)`, the gate holds
at every point of the box. -/
theorem domain_gates {ι : Type*} (s : Finset ι) {r₀ l₀ : ℝ} (hr : 0 ≤ r₀) (hl : 0 ≤ l₀)
    (g : ι → UpperBox r₀ l₀ → ℝ) (θ : ι → ℝ) (hadm : ∀ i ∈ s, Admissible (g i))
    (hgate : ∀ i ∈ s, g i (UpperBox.top hr hl) < θ i) (x : UpperBox r₀ l₀) :
    ∀ i ∈ s, g i x < θ i := fun i hi =>
  lt_of_le_of_lt (endpoint_le (hadm i hi) (UpperBox.le_top hr hl x)) (hgate i hi)

/-- **`lem:record:domain`(i), the coefficients.** An admissible normalized coefficient (the row
coefficients `f`, `h`, the spectral `g`, `B_top`, and the symmetric and skew coefficients of the
changed records, each divided by its power of `r`) is at most its endpoint value. -/
theorem domain_coeffs {ι : Type*} (s : Finset ι) {r₀ l₀ : ℝ} (hr : 0 ≤ r₀) (hl : 0 ≤ l₀)
    (κ : ι → UpperBox r₀ l₀ → ℝ) (hadm : ∀ i ∈ s, Admissible (κ i)) (x : UpperBox r₀ l₀) :
    ∀ i ∈ s, κ i x ≤ κ i (UpperBox.top hr hl) := fun i hi =>
  endpoint_le (hadm i hi) (UpperBox.le_top hr hl x)

/-- `p^{-1/2} ≤ p₀^{-1/2}` for `0 < p₀ ≤ p`. -/
theorem rpow_neg_half_le {p₀ p : ℝ} (hp₀ : 0 < p₀) (hp : p₀ ≤ p) :
    p ^ (-(1 : ℝ) / 2) ≤ p₀ ^ (-(1 : ℝ) / 2) :=
  Real.rpow_le_rpow_of_nonpos hp₀ hp (by norm_num)

/-- **The point of a prime.** A prime `p ≥ p₀ > 1` (as a real) with block count
`0 ≤ l ≤ L'/log p₀` is the point `(p^{-1/2}, l)` of the box with endpoint
`(p₀^{-1/2}, L'/log p₀)`. -/
noncomputable def primePoint {p₀ p L' l : ℝ} (hp₀ : 1 < p₀) (hp : p₀ ≤ p) (hl0 : 0 ≤ l)
    (hl : l ≤ L' / Real.log p₀) : UpperBox (p₀ ^ (-(1 : ℝ) / 2)) (L' / Real.log p₀) :=
  ⟨(p ^ (-(1 : ℝ) / 2), l), Real.rpow_nonneg (by linarith) _,
    rpow_neg_half_le (by linarith) hp, hl0, hl⟩

/-- The point of a prime lies below the endpoint, so `domain_gates` and `domain_coeffs` apply
at `p`. -/
theorem primePoint_le_top {p₀ p L' l : ℝ} (hp₀ : 1 < p₀) (hp : p₀ ≤ p) (hl0 : 0 ≤ l)
    (hl : l ≤ L' / Real.log p₀) (hL : 0 ≤ L') :
    primePoint hp₀ hp hl0 hl ≤
      UpperBox.top (Real.rpow_nonneg (by linarith) _) (div_nonneg hL (Real.log_pos hp₀).le) :=
  UpperBox.le_top _ _ _

/-- **The block count** (Step 2, `lem:majorant`(c)): a block of primes all at least `X ≥ p₀ > 1`,
with product at most `e^{L'}` (`log q_𝔅 ≤ L'`), has at most `L'/log p₀` primes. -/
theorem block_count_le {s : Finset ℝ} {p₀ X L' : ℝ} (hp₀ : 1 < p₀) (hX : p₀ ≤ X)
    (hs : ∀ p ∈ s, X ≤ p) (hprod : ∏ p ∈ s, p ≤ Real.exp L') (hL : 0 ≤ L') :
    (s.card : ℝ) ≤ L' / Real.log p₀ := by
  have hX1 : 1 < X := lt_of_lt_of_le hp₀ hX
  have h := block_inflation_card hX1 hs hprod
  have hlog : Real.log p₀ ≤ Real.log X := Real.log_le_log (by linarith) hX
  exact h.trans (div_le_div_of_nonneg_left hL (Real.log_pos hp₀) hlog)

/-- **A coefficient at a larger prime.** If a quantity at `p` is `r_p^d κ(x_p)` with `κ`
admissible, it is at most `r_p^d κ(r₀, l₀)`: the coefficient certified at the evaluation point
holds at `p` (`lem:record:domain`(i)). -/
theorem prime_coeff_le {r₀ l₀ : ℝ} (hr : 0 ≤ r₀) (hl : 0 ≤ l₀) {κ : UpperBox r₀ l₀ → ℝ}
    (hκ : Admissible κ) (x : UpperBox r₀ l₀) (d : ℕ) :
    x.1.1 ^ d * κ x ≤ x.1.1 ^ d * κ (UpperBox.top hr hl) :=
  mul_le_mul_of_nonneg_left (endpoint_le hκ (UpperBox.le_top hr hl x)) (pow_nonneg x.2.1 _)

/-! ## Step 3: blocks -/

/-- `∏_S f ≤ f_j f_k` for two distinct `j, k ∈ S` when `0 ≤ f ≤ 1` on `S`. -/
theorem prod_le_two {P : Type*} [DecidableEq P] {S : Finset P} {f : P → ℝ}
    (h0 : ∀ p ∈ S, 0 ≤ f p) (h1 : ∀ p ∈ S, f p ≤ 1) {j k : P} (hj : j ∈ S) (hk : k ∈ S)
    (hjk : j ≠ k) : ∏ p ∈ S, f p ≤ f j * f k := by
  have hk' : k ∈ S.erase j := Finset.mem_erase.mpr ⟨hjk.symm, hk⟩
  rw [← Finset.mul_prod_erase S f hj, ← Finset.mul_prod_erase (S.erase j) f hk']
  have hsub : (S.erase j).erase k ⊆ S := fun x hx =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
  have hP1 : ∏ p ∈ (S.erase j).erase k, f p ≤ 1 :=
    Finset.prod_le_one₀ (fun p hp => h0 p (hsub hp)) (fun p hp => h1 p (hsub hp))
  have hP0 : 0 ≤ ∏ p ∈ (S.erase j).erase k, f p :=
    Finset.prod_nonneg fun p hp => h0 p (hsub hp)
  have hjk0 : 0 ≤ f j * f k := mul_nonneg (h0 j hj) (h0 k hk)
  calc f j * (f k * ∏ p ∈ (S.erase j).erase k, f p) =
        (f j * f k) * ∏ p ∈ (S.erase j).erase k, f p := by ring
    _ ≤ (f j * f k) * 1 := mul_le_mul_of_nonneg_left hP1 hjk0
    _ = f j * f k := mul_one _

/-- The two-prime estimate `δ_j δ_k ≤ c² r_b / r₀` from `δ_p ≤ c r_p / r₀`, `r_j ≤ r_b`,
`r_k ≤ r₀`. -/
theorem two_prime_le {δj δk rj rk rb r₀ c : ℝ} (hr0 : 0 < r₀) (hc : 0 ≤ c) (hj0 : 0 ≤ δj)
    (hk0 : 0 ≤ δk) (hj : δj ≤ c * rj / r₀) (hk : δk ≤ c * rk / r₀)
    (hjb : rj ≤ rb) (hk0' : rk ≤ r₀) : δj * δk ≤ c ^ 2 * rb / r₀ := by
  have hk1 : δk ≤ c := by
    calc δk ≤ c * rk / r₀ := hk
      _ ≤ c * r₀ / r₀ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk0' hc) hr0.le
      _ = c := by field_simp
  have hj1 : δj ≤ c * rb / r₀ :=
    hj.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hjb hc) hr0.le)
  have hrb0 : 0 ≤ c * rb / r₀ := hj0.trans hj1
  calc δj * δk ≤ (c * rb / r₀) * c := mul_le_mul hj1 hk1 hk0 hrb0
    _ = c ^ 2 * rb / r₀ := by ring

/-- **`lem:record:domain`(ii), Step 3, the sectors with at least two primes.** Let `δ_p`, `δ'_p`
(the centred norms of the old and the new law at the primes `p` of the sector `S`) lie in `[0, 1]`
with `δ_p ≤ c_old r_p/r₀` and `δ'_p ≤ c_new r_p/r₀` (part (i)), where `r_p ≤ r_b` (`p ≥ b`) and
`r_p ≤ r₀` (`p ≥ p₀`). Under the block gates `c_old² + c_new² ≤ C^s r₀` and `c_new² ≤ C^a r₀`
(`eq:upper-block-gate`), for `|S| ≥ 2`: `∏_S δ + ∏_S δ' ≤ C^s r_b` and `∏_S δ' ≤ C^a r_b`. -/
theorem sector_bound_two {P : Type*} [DecidableEq P] (S : Finset P) (r δ δ' : P → ℝ)
    {r₀ rb cold cnew Cs Ca : ℝ} (hr0 : 0 < r₀) (hcold : 0 ≤ cold) (hcnew : 0 ≤ cnew)
    (hr : ∀ p ∈ S, 0 ≤ r p) (hrb : ∀ p ∈ S, r p ≤ rb) (hrr0 : ∀ p ∈ S, r p ≤ r₀)
    (hδ0 : ∀ p ∈ S, 0 ≤ δ p) (hδ1 : ∀ p ∈ S, δ p ≤ 1) (hδ : ∀ p ∈ S, δ p ≤ cold * r p / r₀)
    (hδ'0 : ∀ p ∈ S, 0 ≤ δ' p) (hδ'1 : ∀ p ∈ S, δ' p ≤ 1)
    (hδ' : ∀ p ∈ S, δ' p ≤ cnew * r p / r₀)
    (hgs : cold ^ 2 + cnew ^ 2 ≤ Cs * r₀) (hga : cnew ^ 2 ≤ Ca * r₀) (hS : 2 ≤ S.card) :
    ∏ p ∈ S, δ p + ∏ p ∈ S, δ' p ≤ Cs * rb ∧ ∏ p ∈ S, δ' p ≤ Ca * rb := by
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have h1 : ∏ p ∈ S, δ p ≤ δ j * δ k := prod_le_two hδ0 hδ1 hj hk hjk
  have h2 : ∏ p ∈ S, δ' p ≤ δ' j * δ' k := prod_le_two hδ'0 hδ'1 hj hk hjk
  have e1 : δ j * δ k ≤ cold ^ 2 * rb / r₀ :=
    two_prime_le hr0 hcold (hδ0 j hj) (hδ0 k hk) (hδ j hj) (hδ k hk)
      (hrb j hj) (hrr0 k hk)
  have e2 : δ' j * δ' k ≤ cnew ^ 2 * rb / r₀ :=
    two_prime_le hr0 hcnew (hδ'0 j hj) (hδ'0 k hk) (hδ' j hj) (hδ' k hk)
      (hrb j hj) (hrr0 k hk)
  have hrb0 : 0 ≤ rb := (hr j hj).trans (hrb j hj)
  constructor
  · calc ∏ p ∈ S, δ p + ∏ p ∈ S, δ' p ≤ cold ^ 2 * rb / r₀ + cnew ^ 2 * rb / r₀ :=
          add_le_add (h1.trans e1) (h2.trans e2)
      _ = (cold ^ 2 + cnew ^ 2) * rb / r₀ := by ring
      _ ≤ (Cs * r₀) * rb / r₀ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hgs hrb0) hr0.le
      _ = Cs * rb := by field_simp
  · calc ∏ p ∈ S, δ' p ≤ cnew ^ 2 * rb / r₀ := h2.trans e2
      _ ≤ (Ca * r₀) * rb / r₀ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hga hrb0) hr0.le
      _ = Ca * rb := by field_simp

/-- **`lem:record:domain`(ii), Step 3, all sectors.** Let `σ^s_S`, `σ^a_S` be the norms of the
restrictions of the symmetric and skew parts of the block difference to the sector of `S`.
Assume the bounds that `lem:sector`(b) provides (hypotheses): `σ^ε_{p} ≤ C^ε r_p` for a single
prime (part (i) at `p`), and for `|S| ≥ 2`, `σ^s_S ≤ ∏_S δ + ∏_S δ'` and `σ^a_S ≤ ∏_S δ'`. With the
per-prime bounds of part (i) and the block gates, every nonempty sector has
`σ^s_S ≤ C^s r_b` and `σ^a_S ≤ C^a r_b`: by the closing clause of `lem:sector`(b) the block
difference has symmetric and skew norms at most `C^s b^{-1/2}` and `C^a b^{-1/2}`. -/
theorem block_sectors_le {P : Type*} [DecidableEq P] (B : Finset P) (r δ δ' : P → ℝ)
    (σs σa : Finset P → ℝ) {r₀ rb cold cnew Cs Ca : ℝ} (hr0 : 0 < r₀) (hcold : 0 ≤ cold)
    (hcnew : 0 ≤ cnew) (hCs : 0 ≤ Cs) (hCa : 0 ≤ Ca)
    (hr : ∀ p ∈ B, 0 ≤ r p) (hrb : ∀ p ∈ B, r p ≤ rb) (hrr0 : ∀ p ∈ B, r p ≤ r₀)
    (hδ0 : ∀ p ∈ B, 0 ≤ δ p) (hδ1 : ∀ p ∈ B, δ p ≤ 1) (hδ : ∀ p ∈ B, δ p ≤ cold * r p / r₀)
    (hδ'0 : ∀ p ∈ B, 0 ≤ δ' p) (hδ'1 : ∀ p ∈ B, δ' p ≤ 1)
    (hδ' : ∀ p ∈ B, δ' p ≤ cnew * r p / r₀)
    (hgs : cold ^ 2 + cnew ^ 2 ≤ Cs * r₀) (hga : cnew ^ 2 ≤ Ca * r₀)
    (hσs1 : ∀ p ∈ B, σs {p} ≤ Cs * r p) (hσa1 : ∀ p ∈ B, σa {p} ≤ Ca * r p)
    (hσs : ∀ S ⊆ B, 2 ≤ S.card → σs S ≤ ∏ p ∈ S, δ p + ∏ p ∈ S, δ' p)
    (hσa : ∀ S ⊆ B, 2 ≤ S.card → σa S ≤ ∏ p ∈ S, δ' p) :
    ∀ S ⊆ B, S.Nonempty → σs S ≤ Cs * rb ∧ σa S ≤ Ca * rb := by
  intro S hSB hne
  rcases Nat.lt_or_ge S.card 2 with hlt | hge
  · obtain ⟨p, rfl⟩ : ∃ p, S = {p} := by
      apply Finset.card_eq_one.mp
      have := hne.card_pos
      omega
    have hp : p ∈ B := hSB (Finset.mem_singleton_self p)
    exact ⟨(hσs1 p hp).trans (mul_le_mul_of_nonneg_left (hrb p hp) hCs),
      (hσa1 p hp).trans (mul_le_mul_of_nonneg_left (hrb p hp) hCa)⟩
  · have h := sector_bound_two S r δ δ' hr0 hcold hcnew (fun p hp => hr p (hSB hp))
      (fun p hp => hrb p (hSB hp)) (fun p hp => hrr0 p (hSB hp)) (fun p hp => hδ0 p (hSB hp))
      (fun p hp => hδ1 p (hSB hp)) (fun p hp => hδ p (hSB hp)) (fun p hp => hδ'0 p (hSB hp))
      (fun p hp => hδ'1 p (hSB hp)) (fun p hp => hδ' p (hSB hp)) hgs hga hge
    exact ⟨(hσs S hSB hge).trans h.1, (hσa S hSB hge).trans h.2⟩

/-! ## The block gates of the three kinds of changed records -/

/-- **The block gates for a one-way repair** (Step 3, (F7)): `c_old = ρ_old`, `c_new = ρ'` are
below `1/2` by (G5), and `C^s r₀ ≥ ρ_old + ρ'`, `C^a r₀ ≥ ρ'` (the coefficients are `ρ_old + ρ'`
and `ρ'` divided by `r₀`, rounded upward). -/
theorem block_gate_oneway {ρold ρ' Cs Ca r₀ : ℝ} (h0 : 0 ≤ ρold) (h0' : 0 ≤ ρ')
    (hold : ρold < 1 / 2) (hnew : ρ' < 1 / 2) (hs : ρold + ρ' ≤ Cs * r₀) (ha : ρ' ≤ Ca * r₀) :
    ρold ^ 2 + ρ' ^ 2 ≤ Cs * r₀ ∧ ρ' ^ 2 ≤ Ca * r₀ := by
  constructor <;> nlinarith

/-- **The block gates for an FF forest record** (Step 3, `prop:forest-records`(c)):
`c_old = ρ_old < 1/2`, `c_new² < min(s_new, a_new)`, `C^s r₀ ≥ ρ_old + s_new` and
`C^a r₀ ≥ a_new`. -/
theorem block_gate_forest {ρold cnew snew anew Cs Ca r₀ : ℝ} (h0 : 0 ≤ ρold)
    (hold : ρold < 1 / 2) (hc : cnew ^ 2 < min snew anew) (hs : ρold + snew ≤ Cs * r₀)
    (ha : anew ≤ Ca * r₀) : ρold ^ 2 + cnew ^ 2 ≤ Cs * r₀ ∧ cnew ^ 2 ≤ Ca * r₀ := by
  have h1 : cnew ^ 2 < snew := lt_of_lt_of_le hc (min_le_left _ _)
  have h2 : cnew ^ 2 < anew := lt_of_lt_of_le hc (min_le_right _ _)
  constructor
  · nlinarith
  · linarith

/-- **The block gates for an FE or EF forest record** (Step 3, `prop:forest-records`(c)):
`ρ_old² + c_new² < d_sym ≤ C^s r₀` and `c_new² < a_new ≤ C^a r₀`. -/
theorem block_gate_forest_diff {ρold cnew anew dsym Cs Ca r₀ : ℝ}
    (hd : ρold ^ 2 + cnew ^ 2 < dsym) (hs : dsym ≤ Cs * r₀) (hc : cnew ^ 2 < anew)
    (ha : anew ≤ Ca * r₀) : ρold ^ 2 + cnew ^ 2 ≤ Cs * r₀ ∧ cnew ^ 2 ≤ Ca * r₀ :=
  ⟨by linarith, by linarith⟩

/-- **The block gates for the dense laws and the LE mixture** (Step 3,
`prop:dense-comparison`(c), `prop:le-mixture`): `c_old = c₀`, `c_new = c₁`,
`c₀² + c₁² < min(k_s, k_a) r₀ ≤ min(d_s, d_a) ≤ min(C^s, C^a) r₀`. -/
theorem block_gate_dense {c0 c1 ks ka ds da Cs Ca r₀ : ℝ} (hg : c0 ^ 2 + c1 ^ 2 < min ks ka * r₀)
    (hr0 : 0 ≤ r₀) (hds : ks * r₀ ≤ ds) (hda : ka * r₀ ≤ da) (hCs : ds ≤ Cs * r₀)
    (hCa : da ≤ Ca * r₀) : c0 ^ 2 + c1 ^ 2 ≤ Cs * r₀ ∧ c1 ^ 2 ≤ Ca * r₀ := by
  have hs : min ks ka * r₀ ≤ ks * r₀ := mul_le_mul_of_nonneg_right (min_le_left _ _) hr0
  have ha : min ks ka * r₀ ≤ ka * r₀ := mul_le_mul_of_nonneg_right (min_le_right _ _) hr0
  constructor
  · linarith
  · nlinarith [sq_nonneg c0]

/-- `k r₀ ≤ e^{ℓ₀}(Γ k r₀ + E + 2F(C + u))` when `ℓ₀ ≥ 0`, `Γ ≥ 1` and the other terms are
nonnegative: the step `min(k_s, k_a) r₀ ≤ min(d_s, d_a)` of the dense laws in Step 3
(`prop:dense-comparison`(b), `prop:le-mixture`). -/
theorem dense_coef_ge {k r₀ ℓ₀ Γ E F C u : ℝ} (hk : 0 ≤ k) (hr0 : 0 ≤ r₀) (hℓ : 0 ≤ ℓ₀)
    (hΓ : 1 ≤ Γ) (hE : 0 ≤ E) (hF : 0 ≤ F) (hCu : 0 ≤ C + u) :
    k * r₀ ≤ Real.exp ℓ₀ * (Γ * k * r₀ + E + 2 * F * (C + u)) := by
  have hkr : 0 ≤ k * r₀ := mul_nonneg hk hr0
  have h1 : k * r₀ ≤ Γ * k * r₀ + E + 2 * F * (C + u) := by
    have h2 : k * r₀ ≤ Γ * (k * r₀) := le_mul_of_one_le_left hkr hΓ
    have h3 : 0 ≤ 2 * F * (C + u) := mul_nonneg (mul_nonneg (by norm_num) hF) hCu
    nlinarith
  have hexp : 1 ≤ Real.exp ℓ₀ := Real.one_le_exp hℓ
  have h0 : 0 ≤ Γ * k * r₀ + E + 2 * F * (C + u) := hkr.trans h1
  nlinarith

end Sarkozy.UpperComparison
