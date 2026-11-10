module

public import Sarkozy.RecordExpansion.Replacement

@[expose] public section

/-!
# Class bounds as polynomials in auxiliary prices (`def:cp5`)

`paper/sections/09_comparison_theorem.tex`, `def:cp5`: a class bound `φ_ω` is a polynomial with
nonnegative coefficients in the auxiliary prices `y_{𝔟,j}`, each of whose monomials takes one
auxiliary price, attached to the record and type of `ω` there, at every atom of `ω`. The structure
`TheoremCBlock.ClassBounds` stores `φ_ω = ∑_m coeff(ω, m) ∏_𝔟 y_{𝔟, m_𝔟}` over the maps `m : ∀ 𝔟,
Option (Jaux 𝔟)`.

Here every record and type `(t, ε)` of an atom carries four auxiliary prices, labelled by `Fin 4`:
`0` the price `π^ε_{𝔟,t}` itself, `1` the raw-arm price, `2` the leading price, `3` the remainder
price (`lem:middle-comparison-prices`, `thm:envelopes`(i)); `Jaux 𝔟 = T_𝔟 × {s, a} × Fin 4`,
attached to `(t, ε)`.

* `auxCoeff K ω m`: the coefficient `1` on the maps `m` that take, at every atom of `ω`, a label in
  `K` on the record and type of `ω`, and nothing off `ω`; `0` otherwise.
* `sum_auxCoeff`: `∑_m auxCoeff K ω m ∏_𝔟 y_{𝔟,m_𝔟} = ∏_{𝔟 ∈ ω} ∑_{k ∈ K} y^k_{𝔟,ω_𝔟}`.
* `replCoeff`, `sum_replCoeff`: the class bound `C_n π^arm_ω + B'(∏(π^lead + π^rem) − ∏ π^lead)` of
  the degree-class replacement (`lem:record:record-expansion`(v); WP-R's `replacementBound`) in this
  form, with nonnegative coefficients (`replCoeff_nonneg`).
* `costCoeff`, `sum_costCoeff`: a class cost `c π_ω` (`def:cp5`) in this form.
* `auxCoeff_support`: every monomial with a nonzero coefficient takes the records and types of `ω`
  (the `coeff_support` field of `ClassBounds`).

All proved.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-- The attachment `(t, ε, k) ↦ (t, ε)` of an auxiliary price to its record and type. -/
def auxAttach {α : Type*} (x : α × ChangeType × Fin 4) : α × ChangeType := (x.1, x.2.1)

/-- The factor of `auxCoeff` at one atom: `1` if the entry `q` of the monomial is compatible with
the entry `o` of the selection and carries a label in `K` (or both are empty), `0` otherwise. -/
def auxChi {α : Type*} [DecidableEq α] (K : Finset (Fin 4)) (o : Option (α × ChangeType)) :
    Option (α × ChangeType × Fin 4) → ℝ
  | none => if o = none then 1 else 0
  | some x => if o = some (auxAttach x) ∧ x.2.2 ∈ K then 1 else 0

theorem auxChi_nonneg {α : Type*} [DecidableEq α] (K : Finset (Fin 4))
    (o : Option (α × ChangeType)) (q : Option (α × ChangeType × Fin 4)) : 0 ≤ auxChi K o q := by
  rcases q with _ | x <;> simp only [auxChi] <;> split_ifs <;> norm_num

theorem auxChi_mono {α : Type*} [DecidableEq α] {K K' : Finset (Fin 4)} (h : K ⊆ K')
    (o : Option (α × ChangeType)) (q : Option (α × ChangeType × Fin 4)) :
    auxChi K o q ≤ auxChi K' o q := by
  rcases q with _ | x
  · exact le_rfl
  · simp only [auxChi]
    by_cases h1 : o = some (auxAttach x) ∧ x.2.2 ∈ K
    · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, h h1.2⟩]
    · rw [ite_eq_right h1]
      split_ifs <;> norm_num

theorem auxChi_support {α : Type*} [DecidableEq α] (K : Finset (Fin 4))
    (o : Option (α × ChangeType)) (q : Option (α × ChangeType × Fin 4))
    (h : auxChi K o q ≠ 0) : q.map auxAttach = o := by
  rcases q with _ | x
  · simp only [auxChi] at h
    split_ifs at h with h1
    · simp [h1]
    · exact absurd rfl h
  · simp only [auxChi] at h
    split_ifs at h with h1
    · simp [h1.1]
    · exact absurd rfl h

theorem sum_auxChi {α : Type*} [Fintype α] [DecidableEq α] (K : Finset (Fin 4))
    (o : Option (α × ChangeType)) (w : α × ChangeType × Fin 4 → ℝ) :
    ∑ q, auxChi K o q * q.elim 1 w = entryPrice (fun t e => ∑ k ∈ K, w (t, e, k)) o := by
  rw [Fintype.sum_option]
  rcases o with _ | ⟨t0, e0⟩
  · simp [auxChi, entryPrice]
  · simp only [auxChi, entryPrice, Option.elim, reduceCtorEq, ↓reduceIte, zero_mul, zero_add]
    have hf : ∀ x : α × ChangeType × Fin 4,
        (if some (t0, e0) = some (auxAttach x) ∧ x.2.2 ∈ K then (1 : ℝ) else 0) * w x =
          if x ∈ K.image (fun k => (t0, e0, k)) then w x else 0 := by
      intro x
      obtain ⟨t, e, k⟩ := x
      simp only [auxAttach, Option.some.injEq, Prod.mk.injEq, mem_image]
      by_cases h : t0 = t ∧ e0 = e ∧ k ∈ K
      · obtain ⟨rfl, rfl, hk⟩ := h
        simp [hk]
      · have h' : ¬ ∃ a ∈ K, t0 = t ∧ e0 = e ∧ a = k := by
          rintro ⟨a, ha, h1, h2, rfl⟩
          exact h ⟨h1, h2, ha⟩
        have h'' : ¬ ((t0 = t ∧ e0 = e) ∧ k ∈ K) := fun hh => h ⟨hh.1.1, hh.1.2, hh.2⟩
        simp only [h', h'', ↓reduceIte, zero_mul]
    rw [Finset.sum_congr rfl (fun x _ => hf x), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_image]
    intro k _ k' _ hk
    simpa using hk

section Coeff

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)]

/-- The coefficient `1` on the monomials compatible with `ω` with labels in `K`. -/
noncomputable def auxCoeff (K : Finset (Fin 4)) (ω : Choice T)
    (m : ∀ b, Option (T b × ChangeType × Fin 4)) : ℝ :=
  ∏ b, auxChi K (ω b) (m b)

/-- The auxiliary prices of an atom from four price functions on the price variables: `y_{𝔟,(t,ε,k)}
= z_k(x^ε_{𝔟,t})`. -/
def auxY (z : Fin 4 → PriceVar T → ℝ) (b : J) (x : T b × ChangeType × Fin 4) : ℝ :=
  z x.2.2 ⟨b, (x.1, x.2.1)⟩

omit [Fintype J] [DecidableEq J] [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] in
theorem auxY_nonneg {z : Fin 4 → PriceVar T → ℝ} (hz : ∀ k v, 0 ≤ z k v) (b : J)
    (x : T b × ChangeType × Fin 4) : 0 ≤ auxY z b x := hz _ _

omit [DecidableEq J] [∀ b, Fintype (T b)] in
theorem auxCoeff_nonneg (K : Finset (Fin 4)) (ω : Choice T)
    (m : ∀ b, Option (T b × ChangeType × Fin 4)) : 0 ≤ auxCoeff K ω m :=
  prod_nonneg fun b _ => auxChi_nonneg K (ω b) (m b)

omit [DecidableEq J] [∀ b, Fintype (T b)] in
theorem auxCoeff_mono {K K' : Finset (Fin 4)} (h : K ⊆ K') (ω : Choice T)
    (m : ∀ b, Option (T b × ChangeType × Fin 4)) : auxCoeff K ω m ≤ auxCoeff K' ω m :=
  prod_le_prod₀ (fun b _ => auxChi_nonneg K (ω b) (m b)) (fun b _ => auxChi_mono h (ω b) (m b))

omit [DecidableEq J] [∀ b, Fintype (T b)] in
theorem auxCoeff_support (K : Finset (Fin 4)) (ω : Choice T)
    (m : ∀ b, Option (T b × ChangeType × Fin 4)) (h : auxCoeff K ω m ≠ 0) (b : J) :
    (m b).map auxAttach = ω b :=
  auxChi_support K (ω b) (m b) fun h0 => h (prod_eq_zero (mem_univ b) h0)

/-- `∑_m auxCoeff K ω m ∏_𝔟 y_{𝔟,m_𝔟} = ∏_{𝔟 ∈ ω} ∑_{k ∈ K} z_k(x^{ε_𝔟}_{𝔟,t_𝔟})`. -/
theorem sum_auxCoeff (K : Finset (Fin 4)) (ω : Choice T) (z : Fin 4 → PriceVar T → ℝ) :
    ∑ m : (∀ b, Option (T b × ChangeType × Fin 4)),
        auxCoeff K ω m * ∏ b, (m b).elim 1 (auxY z b) =
      monomial (fun b t e => ∑ k ∈ K, z k ⟨b, (t, e)⟩) ω := by
  unfold auxCoeff monomial
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun b (q : Option (T b × ChangeType × Fin 4)) =>
    auxChi K (ω b) q * q.elim 1 (auxY z b))]
  apply prod_congr rfl
  intro b _
  exact sum_auxChi K (ω b) (auxY z b)

/-- The four price functions `(π, y^arm, y^lead, y^rem)`. -/
def auxPrices (π : ∀ b, T b → ChangeType → ℝ) (yarm ylead yrem : PriceVar T → ℝ) :
    Fin 4 → PriceVar T → ℝ :=
  ![priceVec π, yarm, ylead, yrem]

/-- The coefficients of the replacement class bound `C_n π^arm_ω + B'(∏ (π^lead + π^rem) − ∏
π^lead)`. -/
noncomputable def replCoeff (Cn B' : ℝ) (ω : Choice T)
    (m : ∀ b, Option (T b × ChangeType × Fin 4)) : ℝ :=
  Cn * auxCoeff {1} ω m + B' * (auxCoeff {2, 3} ω m - auxCoeff {2} ω m)

/-- The coefficients of a class cost `c π_ω`. -/
noncomputable def costCoeff (c : ℝ) (ω : Choice T) (m : ∀ b, Option (T b × ChangeType × Fin 4)) :
    ℝ :=
  c * auxCoeff {0} ω m

omit [DecidableEq J] [∀ b, Fintype (T b)] in
theorem replCoeff_nonneg {Cn B' : ℝ} (hC : 0 ≤ Cn) (hB : 0 ≤ B') (ω : Choice T)
    (m : ∀ b, Option (T b × ChangeType × Fin 4)) : 0 ≤ replCoeff Cn B' ω m := by
  unfold replCoeff
  have h1 := auxCoeff_nonneg {1} ω m
  have h2 : auxCoeff {2} ω m ≤ auxCoeff {2, 3} ω m := auxCoeff_mono (by decide) ω m
  have h3 : 0 ≤ auxCoeff {2, 3} ω m - auxCoeff {2} ω m := by linarith
  positivity

omit [DecidableEq J] [∀ b, Fintype (T b)] in
theorem costCoeff_nonneg {c : ℝ} (hc : 0 ≤ c) (ω : Choice T)
    (m : ∀ b, Option (T b × ChangeType × Fin 4)) : 0 ≤ costCoeff c ω m :=
  mul_nonneg hc (auxCoeff_nonneg {0} ω m)

omit [DecidableEq J] [∀ b, Fintype (T b)] in
theorem replCoeff_support {Cn B' : ℝ} (ω : Choice T) (m : ∀ b, Option (T b × ChangeType × Fin 4))
    (h : replCoeff Cn B' ω m ≠ 0) (b : J) : (m b).map auxAttach = ω b := by
  by_contra hb
  have h0 : ∀ K : Finset (Fin 4), auxCoeff K ω m = 0 := fun K => by
    by_contra hK
    exact hb (auxCoeff_support K ω m hK b)
  apply h
  simp [replCoeff, h0]

omit [DecidableEq J] [∀ b, Fintype (T b)] in
theorem costCoeff_support {c : ℝ} (ω : Choice T) (m : ∀ b, Option (T b × ChangeType × Fin 4))
    (h : costCoeff c ω m ≠ 0) (b : J) : (m b).map auxAttach = ω b := by
  by_contra hb
  have h0 : auxCoeff {0} ω m = 0 := by
    by_contra hK
    exact hb (auxCoeff_support {0} ω m hK b)
  apply h
  simp [costCoeff, h0]

omit [DecidableEq J] in
/-- `mono z (selMono ω)` is the monomial of `ω` in the prices `z`. -/
theorem mono_selMono_eq (z : PriceVar T → ℝ) (ω : Choice T) :
    mono z (selMono ω) = monomial (fun b t e => z ⟨b, (t, e)⟩) ω :=
  mono_selMono (fun b t e => z ⟨b, (t, e)⟩) ω

/-- **The replacement class bound as a polynomial in the auxiliary prices**: `∑_m replCoeff(ω, m)
∏_𝔟 y_{𝔟,m_𝔟} = C_n π^arm_ω + B'(∏(π^lead + π^rem) − ∏ π^lead)` (`replacementBound`). -/
theorem sum_replCoeff (Cn B' : ℝ) (π : ∀ b, T b → ChangeType → ℝ)
    (yarm ylead yrem : PriceVar T → ℝ) (ω : Choice T) :
    ∑ m : (∀ b, Option (T b × ChangeType × Fin 4)),
        replCoeff Cn B' ω m * ∏ b, (m b).elim 1 (auxY (auxPrices π yarm ylead yrem) b) =
      replacementBound Cn B' yarm ylead yrem ω := by
  have e : ∀ m : (∀ b, Option (T b × ChangeType × Fin 4)),
      replCoeff Cn B' ω m * ∏ b, (m b).elim 1 (auxY (auxPrices π yarm ylead yrem) b) =
        Cn * (auxCoeff {1} ω m * ∏ b, (m b).elim 1 (auxY (auxPrices π yarm ylead yrem) b)) +
        B' * (auxCoeff {2, 3} ω m * ∏ b, (m b).elim 1 (auxY (auxPrices π yarm ylead yrem) b) -
          auxCoeff {2} ω m * ∏ b, (m b).elim 1 (auxY (auxPrices π yarm ylead yrem) b)) := by
    intro m
    unfold replCoeff
    ring
  rw [Finset.sum_congr rfl (fun m _ => e m), sum_add_distrib, ← mul_sum, ← mul_sum,
    sum_sub_distrib, sum_auxCoeff, sum_auxCoeff, sum_auxCoeff]
  unfold replacementBound
  rw [mono_selMono_eq, mono_selMono_eq, mono_selMono_eq]
  simp only [Finset.sum_singleton, Finset.sum_insert (show (2 : Fin 4) ∉ ({3} : Finset _) by
    decide), auxPrices]
  rfl

/-- **A class cost as a polynomial in the auxiliary prices**: `∑_m costCoeff(ω, m) ∏_𝔟 y_{𝔟,m_𝔟} = c
π_ω`. -/
theorem sum_costCoeff (c : ℝ) (π : ∀ b, T b → ChangeType → ℝ) (yarm ylead yrem : PriceVar T → ℝ)
    (ω : Choice T) :
    ∑ m : (∀ b, Option (T b × ChangeType × Fin 4)),
        costCoeff c ω m * ∏ b, (m b).elim 1 (auxY (auxPrices π yarm ylead yrem) b) =
      c * monomial π ω := by
  unfold costCoeff
  simp_rw [mul_assoc]
  rw [← mul_sum, sum_auxCoeff]
  simp only [Finset.sum_singleton, auxPrices]
  rfl

end Coeff

end Sarkozy.ClassBoundsPaper
