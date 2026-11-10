module

public import Sarkozy.RecordExpansion.Monomials

@[expose] public section

/-!
# The completion of a positive series over distinct atoms

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean` (last paragraph of the proof:
"allowing repeated block labels enlarges the sum over distinct blocks and gives the displayed
exponential series; this step is legitimate because the residual coefficients are nonnegative"),
`prop:joint-upper-mean` ("Complete this positive residual series as above");
`paper/sections/10_comparison_lemmas.tex`, `lem:record:record-expansion`(ii).

The terms of the record expansion are choices `ω` of at most one record and change type per atom
(`RecordExpansion.Choice`), with monomial `π_ω = ∏_{b ∈ supp ω} π_{b, ω_b}`. Give every entry
`(b, t, e)` a letter `ℓ(b,t,e) ∈ Λ` (fold or matching arm, invariant or generic outside factor, raw
arm or remainder, ...); the letter degree `deg ω : Λ → ℕ` counts the entries of each letter, and
`X_l = ∑_{ℓ(b,t,e) = l} π_{b,t,e}` is the total price of the letter `l`.

* **`sum_powersetCard_prod_le`**: `e_n(x) ≤ (∑ x)^n / n!` for nonnegative `x` (one letter);
* **`sum_deg_eq_le`**: `∑_{deg ω = d} π_ω ≤ ∏_l X_l^{d_l} / d_l!` (all letters);
* **`completion_le`**: for a coefficient `R(d) ≥ 0` of the letter degree,
  `∑_{ω ∈ S} R(deg ω) π_ω ≤ ∑_{d ∈ Ds} R(d) ∏_l X_l^{d_l} / d_l!`.

The right side is the partial sum of the completed exponential series in the letter totals; the
nonnegativity of `R` is exactly the paper's condition (the residual gates `63c − b ≥ 0`). The prices
are arbitrary nonnegative reals.
-/

open Finset

namespace Sarkozy.MeanCredit

/-- `X^{n+1} + (n+1) y X^n ≤ (X + y)^{n+1}` for `X, y ≥ 0` (the first two binomial terms). -/
theorem pow_succ_ge_add {X y : ℝ} (hX : 0 ≤ X) (hy : 0 ≤ y) (n : ℕ) :
    X ^ (n + 1) + (n + 1) * y * X ^ n ≤ (X + y) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ X + y := add_nonneg hX hy
    have h2 := mul_le_mul_of_nonneg_left ih h1
    have h3 : 0 ≤ ((n : ℝ) + 1) * y * y * X ^ n := by positivity
    have e1 : X ^ (n + 1 + 1) + ((((n + 1 : ℕ) : ℝ)) + 1) * y * X ^ (n + 1) =
        (X + y) * (X ^ (n + 1) + ((n : ℝ) + 1) * y * X ^ n) - ((n : ℝ) + 1) * y * y * X ^ n := by
      push_cast; ring
    have e2 : (X + y) ^ (n + 1 + 1) = (X + y) * (X + y) ^ (n + 1) := by ring
    rw [e1, e2]
    linarith

/-- **The elementary symmetric sums are dominated by the completed power**:
`e_n(x) = ∑_{t ⊆ s, |t| = n} ∏_{i ∈ t} x_i ≤ (∑_{i ∈ s} x_i)^n / n!` for nonnegative `x`. -/
theorem sum_powersetCard_prod_le {ι : Type*} [DecidableEq ι] (x : ι → ℝ) (s : Finset ι)
    (hx : ∀ i ∈ s, 0 ≤ x i) (n : ℕ) :
    ∑ t ∈ s.powersetCard n, ∏ i ∈ t, x i ≤ (∑ i ∈ s, x i) ^ n / n.factorial := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp
    | succ n => rw [powersetCard_eq_empty.mpr (by simp)]; simp
  | insert a s ha ih =>
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have hxa : 0 ≤ x a := hx a (mem_insert_self a s)
    have hX : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hxs
    cases n with
    | zero => simp
    | succ n =>
      have hdisj : Disjoint (s.powersetCard (n + 1)) ((s.powersetCard n).image (insert a)) := by
        rw [disjoint_left]
        intro t ht ht'
        obtain ⟨u, -, rfl⟩ := mem_image.mp ht'
        exact ha ((mem_powersetCard.mp ht).1 (mem_insert_self a u))
      have hinj : Set.InjOn (insert a) (s.powersetCard n : Set (Finset ι)) := by
        intro u hu v hv huv
        have hau : a ∉ u := fun h => ha ((mem_powersetCard.mp hu).1 h)
        have hav : a ∉ v := fun h => ha ((mem_powersetCard.mp hv).1 h)
        rw [← erase_insert hau, ← erase_insert hav]
        exact congrArg (fun w => Finset.erase w a) huv
      rw [powersetCard_succ_insert ha, sum_union hdisj, sum_image hinj, sum_insert ha]
      have e : ∀ t ∈ s.powersetCard n, ∏ i ∈ insert a t, x i = x a * ∏ i ∈ t, x i := by
        intro t ht
        have hat : a ∉ t := fun h => ha ((mem_powersetCard.mp ht).1 h)
        rw [prod_insert hat]
      rw [sum_congr rfl e, ← mul_sum]
      have h1 := ih hxs (n + 1)
      have h2 := mul_le_mul_of_nonneg_left (ih hxs n) hxa
      have h3 := pow_succ_ge_add hX hxa n
      have hF : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      have hF1 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
        push_cast [Nat.factorial_succ]; ring
      have e2 : x a * ((∑ i ∈ s, x i) ^ n / n.factorial) =
          ((n : ℝ) + 1) * x a * (∑ i ∈ s, x i) ^ n / (n + 1).factorial := by
        rw [hF1]; field_simp
      rw [e2] at h2
      have h4 : ((∑ i ∈ s, x i) ^ (n + 1) + ((n : ℝ) + 1) * x a * (∑ i ∈ s, x i) ^ n) /
          (n + 1).factorial ≤ (x a + ∑ i ∈ s, x i) ^ (n + 1) / (n + 1).factorial := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [add_comm (x a)]
        exact h3
      rw [add_div] at h4
      linarith

/-! ## Choices graded by letters -/

section Choices

open Sarkozy.RecordExpansion

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)]

/-- An entry of the record expansion: an atom `b`, a record `t` at `b` and a change type. -/
abbrev Entry (T : J → Type*) : Type _ := Σ b : J, T b × ChangeType

/-- The entries of a choice: the pairs `(b, ω_b)` with `ω_b ≠ none`. -/
def entries (ω : Choice T) : Finset (Entry T) := univ.sigma fun b => (ω b).toFinset

omit [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] [DecidableEq J] in
theorem mem_entries {ω : Choice T} {e : Entry T} : e ∈ entries ω ↔ ω e.1 = some e.2 := by
  obtain ⟨b, te⟩ := e
  simp [entries, Option.mem_def]

omit [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] [DecidableEq J] in
/-- A choice is determined by its entries. -/
theorem entries_injective : Function.Injective (entries (T := T)) := by
  intro ω ω' h
  funext b
  rcases hω : ω b with _ | te
  · rcases hω' : ω' b with _ | te'
    · rfl
    · have h1 : (⟨b, te'⟩ : Entry T) ∈ entries ω := by rw [h, mem_entries]; exact hω'
      rw [mem_entries] at h1
      simp_all
  · have h1 : (⟨b, te⟩ : Entry T) ∈ entries ω' := by rw [← h, mem_entries]; exact hω
    rw [mem_entries] at h1
    exact h1.symm

omit [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] [DecidableEq J] in
/-- The monomial of a choice is the product of the prices of its entries. -/
theorem monomial_eq_prod_entries (π : ∀ b, T b → ChangeType → ℝ) (ω : Choice T) :
    monomial π ω = ∏ e ∈ entries ω, π e.1 e.2.1 e.2.2 := by
  unfold monomial entries
  rw [prod_sigma]
  refine prod_congr rfl fun b _ => ?_
  rcases ω b with _ | ⟨t, e⟩
  · simp [entryPrice]
  · simp [entryPrice]

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The letter degree of a choice: the number of its entries with letter `l`, for each `l`. -/
def deg (ℓ : Entry T → Λ) (ω : Choice T) : Λ → ℕ :=
  fun l => ((entries ω).filter fun e => ℓ e = l).card

/-- The total price `X_l = ∑_{ℓ(e) = l} π_e` of the letter `l`, over all atoms. -/
noncomputable def letterTotal (ℓ : Entry T → Λ) (π : ∀ b, T b → ChangeType → ℝ) (l : Λ) : ℝ :=
  ∑ e ∈ univ.filter (fun e : Entry T => ℓ e = l), π e.1 e.2.1 e.2.2

/-- The completed monomial `∏_l X_l^{d_l} / d_l!` of a letter degree `d`. -/
noncomputable def completedMono (ℓ : Entry T → Λ) (π : ∀ b, T b → ChangeType → ℝ)
    (d : Λ → ℕ) : ℝ :=
  ∏ l, letterTotal ℓ π l ^ d l / (d l).factorial

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
theorem completedMono_nonneg (ℓ : Entry T → Λ) {π : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) (d : Λ → ℕ) : 0 ≤ completedMono ℓ π d :=
  prod_nonneg fun _ _ => div_nonneg (pow_nonneg (sum_nonneg fun _ _ => hπ _ _ _) _)
    (Nat.cast_nonneg _)

/-- The entries of a choice with a given letter. -/
def letterEntries (ℓ : Entry T → Λ) (ω : Choice T) (l : Λ) : Finset (Entry T) :=
  (entries ω).filter fun e => ℓ e = l

omit [DecidableEq J] [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] in
theorem monomial_eq_prod_letters (ℓ : Entry T → Λ) (π : ∀ b, T b → ChangeType → ℝ)
    (ω : Choice T) :
    monomial π ω = ∏ l, ∏ e ∈ letterEntries ℓ ω l, π e.1 e.2.1 e.2.2 := by
  rw [monomial_eq_prod_entries]
  exact (prod_fiberwise (entries ω) ℓ fun e => π e.1 e.2.1 e.2.2).symm

omit [DecidableEq J] [Fintype Λ] [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] in
theorem letterEntries_injective (ℓ : Entry T → Λ) :
    Function.Injective (letterEntries (T := T) ℓ) := by
  intro ω ω' h
  apply entries_injective
  ext e
  have h1 : e ∈ letterEntries ℓ ω (ℓ e) ↔ e ∈ letterEntries ℓ ω' (ℓ e) := by rw [h]
  simpa [letterEntries] using h1

omit [DecidableEq J] [Fintype Λ] [∀ b, DecidableEq (T b)] in
theorem letterEntries_mem (ℓ : Entry T → Λ) (ω : Choice T) (l : Λ) :
    letterEntries ℓ ω l ∈ (univ.filter fun e : Entry T => ℓ e = l).powersetCard (deg ℓ ω l) := by
  rw [mem_powersetCard]
  refine ⟨fun e he => ?_, rfl⟩
  rw [letterEntries, mem_filter] at he
  rw [mem_filter]
  exact ⟨mem_univ _, he.2⟩

/-- **One letter degree, completed** (`lem:record:record-expansion`(ii), the completion with
repeated block labels in the proof of `prop:joint-middle-mean`): the sum of the monomials of the
choices of letter degree `d`, over distinct atoms, is at most `∏_l X_l^{d_l} / d_l!`. -/
theorem sum_deg_eq_le (ℓ : Entry T → Λ) {π : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) (d : Λ → ℕ) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => deg ℓ ω = d), monomial π ω ≤ completedMono ℓ π d := by
  have hP0 : ∀ t : Finset (Entry T), 0 ≤ ∏ e ∈ t, π e.1 e.2.1 e.2.2 :=
    fun t => prod_nonneg fun e _ => hπ _ _ _
  have hinj : Set.InjOn (letterEntries ℓ)
      ((univ.filter (fun ω : Choice T => deg ℓ ω = d) : Finset (Choice T)) : Set (Choice T)) :=
    (letterEntries_injective ℓ).injOn
  have hsub : (univ.filter (fun ω : Choice T => deg ℓ ω = d)).image (letterEntries ℓ) ⊆
      Fintype.piFinset fun l => (univ.filter fun e : Entry T => ℓ e = l).powersetCard (d l) := by
    intro p hp
    obtain ⟨ω, hω, rfl⟩ := mem_image.mp hp
    rw [Fintype.mem_piFinset]
    intro l
    have hd : deg ℓ ω = d := (mem_filter.mp hω).2
    rw [← hd]
    exact letterEntries_mem ℓ ω l
  calc ∑ ω ∈ univ.filter (fun ω : Choice T => deg ℓ ω = d), monomial π ω
      = ∑ ω ∈ univ.filter (fun ω : Choice T => deg ℓ ω = d),
          ∏ l, ∏ e ∈ letterEntries ℓ ω l, π e.1 e.2.1 e.2.2 :=
        sum_congr rfl fun ω _ => monomial_eq_prod_letters ℓ π ω
    _ = ∑ p ∈ (univ.filter (fun ω : Choice T => deg ℓ ω = d)).image (letterEntries ℓ),
          ∏ l, ∏ e ∈ p l, π e.1 e.2.1 e.2.2 :=
        (sum_image (f := fun p : Λ → Finset (Entry T) => ∏ l, ∏ e ∈ p l, π e.1 e.2.1 e.2.2)
          hinj).symm
    _ ≤ ∑ p ∈ Fintype.piFinset fun l =>
            (univ.filter fun e : Entry T => ℓ e = l).powersetCard (d l),
          ∏ l, ∏ e ∈ p l, π e.1 e.2.1 e.2.2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => prod_nonneg fun l _ => hP0 _
    _ = ∏ l, ∑ t ∈ (univ.filter fun e : Entry T => ℓ e = l).powersetCard (d l),
          ∏ e ∈ t, π e.1 e.2.1 e.2.2 :=
        (prod_univ_sum (fun l => (univ.filter fun e : Entry T => ℓ e = l).powersetCard (d l))
          fun _ t => ∏ e ∈ t, π e.1 e.2.1 e.2.2).symm
    _ ≤ completedMono ℓ π d := by
        unfold completedMono letterTotal
        refine prod_le_prod₀ (fun l _ => sum_nonneg fun t _ => hP0 t) fun l _ => ?_
        exact sum_powersetCard_prod_le (fun e : Entry T => π e.1 e.2.1 e.2.2) _
          (fun e _ => hπ _ _ _) (d l)

/-- **The completion of a positive series over distinct atoms** (`prop:joint-middle-mean`, last
paragraph of the proof: "allowing repeated block labels enlarges the sum over distinct blocks and
gives the displayed exponential series; this step is legitimate because the residual coefficients
are nonnegative"; `lem:record:record-expansion`(ii)). For any set `S` of choices and any
coefficient `R` of the letter degree that is nonnegative on a set `Ds` containing the degrees of
`S`: `∑_{ω ∈ S} R(deg ω) π_ω ≤ ∑_{d ∈ Ds} R(d) ∏_l X_l^{d_l}/d_l!`. -/
theorem completion_le (ℓ : Entry T → Λ) {π : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) (S : Finset (Choice T)) (Ds : Finset (Λ → ℕ))
    (hS : ∀ ω ∈ S, deg ℓ ω ∈ Ds) (R : (Λ → ℕ) → ℝ) (hR : ∀ d ∈ Ds, 0 ≤ R d) :
    ∑ ω ∈ S, R (deg ℓ ω) * monomial π ω ≤ ∑ d ∈ Ds, R d * completedMono ℓ π d := by
  rw [← sum_fiberwise_of_maps_to hS]
  refine sum_le_sum fun d hd => ?_
  have e : ∑ ω ∈ S with deg ℓ ω = d, R (deg ℓ ω) * monomial π ω =
      R d * ∑ ω ∈ S with deg ℓ ω = d, monomial π ω := by
    rw [mul_sum]
    exact sum_congr rfl fun ω hω => by rw [(mem_filter.mp hω).2]
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (hR d hd)
  calc ∑ ω ∈ S with deg ℓ ω = d, monomial π ω
      ≤ ∑ ω ∈ univ.filter (fun ω : Choice T => deg ℓ ω = d), monomial π ω := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun ω _ _ => monomial_nonneg hπ ω
        intro ω hω
        simp only [mem_filter] at hω ⊢
        exact ⟨mem_univ _, hω.2⟩
    _ ≤ completedMono ℓ π d := sum_deg_eq_le ℓ hπ d

end Choices

end Sarkozy.MeanCredit
