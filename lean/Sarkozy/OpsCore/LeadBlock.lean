module

public import Sarkozy.OpsCore.LeadPrime

@[expose] public section

/-!
# The leading star of a block: the sector assembly with the singleton forms split off (OPS-L)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(b) ("`Skew D_t = L_{t,𝔅} + R_{t,𝔅}`,
where `L_{t,𝔅}` is `L°_{t,p}` on the sector of exact support `{p}` and zero on the other
sectors"), and Step 4 of its proof; `rem:signed-mixture-sectors`.

FD's `mix_change_le` bounds the block form of a signed mixture sector by sector, with one constant
for the singleton sectors and the larger ones. Here the singleton forms are split:

* `sing j`, **`comp1`**: the component of `φ` in the singleton sector `{j}`, as a function of
  `x_j`; **`singForm Λ`**: the block form `∑_j Λ_j(comp_j φ, comp_j ψ)` of one-coordinate forms
  `Λ_j` placed on the singleton sectors (the paper's `L_{t,𝔅}` for `Λ_j = L°_{t,p_j}`);
* **`mix_change_sub_le`**: if every one-coordinate remainder `mixChg1_j − Λ_j` is at most `e` on
  mean-zero functions and the larger sectors are at most `e` (FD's `hmulti`), then
  `|mixChg − singForm Λ| ≤ e ‖φ‖ ‖ψ‖` (the remainder `R_{t,𝔅}`);
* **`singForm_le`**: if every `Λ_j` is at most `ℓ` on mean-zero functions, then
  `|singForm Λ| ≤ ℓ ‖φ‖ ‖ψ‖` (the leading star `L_{t,𝔅}`: an orthogonal sum over the sectors).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram Sarkozy.NormBoundsPaper4
open Sarkozy.NormBoundsPaper2 (ip ip_nonneg bilin_le_of_sectors SP_single_eq SP_empty_eq
  ip_one_SP ip_single abs_le_of_sq_le')

variable {K : Type} [Fintype K] [DecidableEq K] {A : K → Type} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)] {m : ∀ j, A j → ℝ}

/-- The singleton sector `{j}`. -/
def sing (j : K) : K → Bool := fun k => decide (k = j)

theorem sing_filter (j : K) : univ.filter (fun k => sing j k = true) = {j} := by
  ext k
  simp [sing]

variable (m) in
/-- **The component of `φ` in the singleton sector `{j}`**, as a function of `x_j`. -/
noncomputable def comp1 (x₀ : ∀ j, A j) (j : K) (φ : (∀ j, A j) → ℝ) : A j → ℝ :=
  fun a => (SP m (sing j) *ᵥ φ) (Function.update x₀ j a)

variable (m) in
/-- **The block form of one-coordinate forms placed on the singleton sectors**. -/
noncomputable def singForm (x₀ : ∀ j, A j) (Λ : ∀ j, (A j → ℝ) → (A j → ℝ) → ℝ)
    (φ ψ : (∀ j, A j) → ℝ) : ℝ :=
  ∑ j, Λ j (comp1 m x₀ j φ) (comp1 m x₀ j ψ)

/-- The component of a sector projection: `comp_j (P_l φ) = comp_j φ` if `l = {j}`, else `0`. -/
theorem comp1_SP (hm1 : ∀ j, ∑ a, m j a = 1) (x₀ : ∀ j, A j) (j : K) (l : K → Bool)
    (φ : (∀ j, A j) → ℝ) :
    comp1 m x₀ j (SP m l *ᵥ φ) = if l = sing j then comp1 m x₀ j φ else 0 := by
  unfold comp1
  rw [Matrix.mulVec_mulVec]
  by_cases hl : l = sing j
  · subst hl
    rw [SP_mul_self m hm1]
    simp only [↓reduceIte]
  · rw [SP_mul_SP hm1 (Ne.symm hl), Matrix.zero_mulVec]
    simp only [hl, ↓reduceIte]
    rfl

/-- `singForm` splits over the sectors (it lives on the singleton sectors). -/
theorem singForm_decomp (hm1 : ∀ j, ∑ a, m j a = 1) (x₀ : ∀ j, A j)
    (Λ : ∀ j, (A j → ℝ) → (A j → ℝ) → ℝ) (hΛ : ∀ j, Λ j 0 0 = 0) (φ ψ : (∀ j, A j) → ℝ) :
    singForm m x₀ Λ φ ψ = ∑ l, singForm m x₀ Λ (SP m l *ᵥ φ) (SP m l *ᵥ ψ) := by
  unfold singForm
  simp only [comp1_SP hm1]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_eq_single (sing j)]
  · simp
  · intro l _ hl
    simp only [hl, ↓reduceIte, hΛ]
  · simp

/-- On a sector other than `{j}`, the `j`-th component vanishes. -/
theorem singForm_SP_of_ne (hm1 : ∀ j, ∑ a, m j a = 1) (x₀ : ∀ j, A j)
    (Λ : ∀ j, (A j → ℝ) → (A j → ℝ) → ℝ) (hΛ : ∀ j, Λ j 0 0 = 0) (l : K → Bool)
    (hl : ∀ j, l ≠ sing j) (φ ψ : (∀ j, A j) → ℝ) :
    singForm m x₀ Λ (SP m l *ᵥ φ) (SP m l *ᵥ ψ) = 0 := by
  unfold singForm
  refine sum_eq_zero fun j _ => ?_
  rw [comp1_SP hm1, comp1_SP hm1]
  simp only [hl j, ↓reduceIte, hΛ]

/-- On the singleton sector `{i}`, only the `i`-th component remains, and it is the restriction
`a ↦ (P_l φ)(x₀[i ↦ a])`. -/
theorem singForm_SP_sing (hm1 : ∀ j, ∑ a, m j a = 1) (x₀ : ∀ j, A j)
    (Λ : ∀ j, (A j → ℝ) → (A j → ℝ) → ℝ) (hΛ : ∀ j, Λ j 0 0 = 0) (i : K)
    (φ ψ : (∀ j, A j) → ℝ) :
    singForm m x₀ Λ (SP m (sing i) *ᵥ φ) (SP m (sing i) *ᵥ ψ) =
      Λ i (fun a => (SP m (sing i) *ᵥ φ) (Function.update x₀ i a))
        (fun a => (SP m (sing i) *ᵥ ψ) (Function.update x₀ i a)) := by
  unfold singForm
  rw [sum_eq_single i]
  · rw [comp1_SP hm1, comp1_SP hm1]
    simp only [↓reduceIte]
    rfl
  · intro j _ hj
    have hne : sing i ≠ sing j := by
      intro h
      have := congrFun h i
      simp [sing, Ne.symm hj] at this
    rw [comp1_SP hm1, comp1_SP hm1]
    simp only [hne, ↓reduceIte, hΛ]
  · simp

theorem sing_of_card_one {l : K → Bool} {i : K} (hi : univ.filter (fun j => l j = true) = {i}) :
    l = sing i := by
  funext k
  have h := congrArg (fun s => k ∈ s) hi
  simp only [mem_filter, mem_univ, true_and, mem_singleton, eq_iff_iff] at h
  unfold sing
  cases hk : l k
  · rw [hk] at h
    simp only [Bool.false_eq_true, false_iff] at h
    simp [h]
  · rw [hk] at h
    simp only [true_iff] at h
    simp [h]

/-- **The remainder of the signed mixture after the singleton forms** (`prop:signed-bounds`(b),
`R_{t,𝔅}`): with the one-coordinate remainders `mixChg1_j − Λ_j ≤ e` on mean-zero functions and
FD's bound `hmulti` on the larger sectors,
`|mixChg φ ψ − singForm Λ φ ψ| ≤ e ‖φ‖ ‖ψ‖`. -/
theorem mix_change_sub_le (hm : ∀ j a, 0 ≤ m j a) (hm1 : ∀ j, ∑ a, m j a = 1)
    {P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ} {C : ∀ j, Matrix (A j) (A j) ℝ}
    (hP : ∀ c, IsCoupling m (P c)) (hC : IsCoupling m C)
    (hPn : ∀ c j a b, 0 ≤ P c j a b) (hCn : ∀ j a b, 0 ≤ C j a b) {w : Fin 3 → ℝ}
    {α₁ α₂ β : ℝ} (hαβ : (∑ c, w c) * (α₁ + α₂) = β) {ρ d e : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hρ : ∀ c j, CentredNorm (m j) (P c j) ρ)
    (hd : ∀ j, CentredNorm (m j) (C j) d) (he : 0 ≤ e)
    (hmulti : (∑ c, |w c|) * (|α₁| + |α₂|) * ρ ^ 2 + |β| * d ^ 2 ≤ e)
    (Λ : ∀ j, (A j → ℝ) → (A j → ℝ) → ℝ) (hΛ : ∀ j, Λ j 0 0 = 0)
    (hsingle : ∀ j (u v : A j → ℝ), ∑ a, m j a * u a = 0 → ∑ a, m j a * v a = 0 →
      |mixChg1 (fun c => P c j) (C j) w α₁ α₂ β u v - Λ j u v| ≤
        e * Real.sqrt (∑ a, m j a * u a ^ 2) * Real.sqrt (∑ a, m j a * v a ^ 2))
    (x₀ : ∀ j, A j) (φ ψ : (∀ j, A j) → ℝ) :
    |mixChg P C w α₁ α₂ β φ ψ - singForm m x₀ Λ φ ψ| ≤
      e * Real.sqrt (ip m φ φ) * Real.sqrt (ip m ψ ψ) := by
  have hdP : ∀ c (φ ψ : (∀ j, A j) → ℝ), φ ⬝ᵥ (piKron (P c) *ᵥ ψ) =
      ∑ l, (SP m l *ᵥ φ) ⬝ᵥ (piKron (P c) *ᵥ (SP m l *ᵥ ψ)) :=
    fun c φ ψ => dot_decomp hm1 (fun l => SP_comm (hP c) l) φ ψ
  have hmix : ∀ φ ψ : (∀ j, A j) → ℝ, mixChg P C w α₁ α₂ β φ ψ =
      ∑ l, mixChg P C w α₁ α₂ β (SP m l *ᵥ φ) (SP m l *ᵥ ψ) := by
    intro φ ψ
    unfold mixChg
    have e1 : ∑ c, w c * (α₁ * (φ ⬝ᵥ (piKron (P c) *ᵥ ψ)) + α₂ * (ψ ⬝ᵥ (piKron (P c) *ᵥ φ))) =
        ∑ l, ∑ c, w c * (α₁ * ((SP m l *ᵥ φ) ⬝ᵥ (piKron (P c) *ᵥ (SP m l *ᵥ ψ))) +
          α₂ * ((SP m l *ᵥ ψ) ⬝ᵥ (piKron (P c) *ᵥ (SP m l *ᵥ φ)))) := by
      rw [Finset.sum_comm]
      refine sum_congr rfl fun c _ => ?_
      rw [hdP c φ ψ, hdP c ψ φ, mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
    rw [e1, dot_decomp hm1 (fun l => SP_comm hC l) φ ψ, mul_sum, ← sum_sub_distrib]
  refine bilin_le_of_sectors hm hm1
    (fun φ ψ => mixChg P C w α₁ α₂ β φ ψ - singForm m x₀ Λ φ ψ) (fun φ ψ => ?_) he
    (fun l φ ψ => ?_) φ ψ
  · rw [hmix φ ψ, singForm_decomp hm1 x₀ Λ hΛ φ ψ, ← sum_sub_distrib]
  set S := univ.filter fun j => l j = true
  set f := SP m l *ᵥ φ
  set g := SP m l *ᵥ ψ
  have hf0 := ip_nonneg hm f
  have hg0 := ip_nonneg hm g
  rcases Nat.lt_or_ge S.card 2 with hS | hS
  · rcases Nat.lt_or_ge S.card 1 with hS0 | hS1
    · -- the empty sector
      have hSe : S = ∅ := card_eq_zero.mp (by omega)
      have hlne : ∀ j, l ≠ sing j := by
        intro j hj
        have : j ∈ S := by
          simp only [S, mem_filter, mem_univ, true_and, hj, sing, decide_true]
        rw [hSe] at this
        exact notMem_empty j this
      have ef : f = fun _ => f x₀ := SP_empty_eq l hSe x₀ φ
      have eg : g = fun _ => g x₀ := SP_empty_eq l hSe x₀ ψ
      have hconst : ∀ c (a b' : ℝ), (fun _ : ∀ j, A j => a) ⬝ᵥ (piKron (P c) *ᵥ fun _ => b') =
          a * b' := fun c => dot_piKron_const (hP c) hm1
      have hz : mixChg P C w α₁ α₂ β f g = 0 := by
        unfold mixChg
        rw [ef, eg]
        simp only [hconst, dot_piKron_const hC hm1]
        have hs : ∑ c, w c * (α₁ * (f x₀ * g x₀) + α₂ * (g x₀ * f x₀)) =
            (∑ c, w c) * (α₁ + α₂) * (f x₀ * g x₀) := by
          rw [sum_mul, sum_mul]
          exact sum_congr rfl fun c _ => by ring
        rw [hs, hαβ]
        ring
      rw [hz, singForm_SP_of_ne hm1 x₀ Λ hΛ l hlne φ ψ, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg he (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    · -- a singleton sector
      obtain ⟨i, hi⟩ := card_eq_one.mp (show S.card = 1 by omega)
      have hli : l = sing i := sing_of_card_one hi
      have hl : l ≠ fun _ => false := by
        intro h
        have : i ∈ S := by rw [hi]; exact mem_singleton_self i
        simp [S, h] at this
      set u := fun a => f (Function.update x₀ i a)
      set v := fun a => g (Function.update x₀ i a)
      have ef : f = fun x => u (x i) := SP_single_eq l hi x₀ φ
      have eg : g = fun x => v (x i) := SP_single_eq l hi x₀ ψ
      have hu : ∑ a, m i a * u a = 0 := by
        have h := ip_one_SP hm1 hl φ
        change ip m (fun _ => 1) f = 0 at h
        rw [ef, show (fun _ : ∀ j, A j => (1 : ℝ)) = fun x => (fun _ : A i => (1 : ℝ)) (x i)
          from rfl, ip_single hm1 i (fun _ => (1 : ℝ)) u] at h
        simpa using h
      have hv : ∑ a, m i a * v a = 0 := by
        have h := ip_one_SP hm1 hl ψ
        change ip m (fun _ => 1) g = 0 at h
        rw [eg, show (fun _ : ∀ j, A j => (1 : ℝ)) = fun x => (fun _ : A i => (1 : ℝ)) (x i)
          from rfl, ip_single hm1 i (fun _ => (1 : ℝ)) v] at h
        simpa using h
      have h1 := hsingle i u v hu hv
      have hsing : ∀ c (u' v' : A i → ℝ),
          (fun x : ∀ j, A j => u' (x i)) ⬝ᵥ (piKron (P c) *ᵥ fun y => v' (y i)) =
            u' ⬝ᵥ (P c i *ᵥ v') := fun c => dot_piKron_single (hP c) hm1 i
      have hc : mixChg P C w α₁ α₂ β f g = mixChg1 (fun c => P c i) (C i) w α₁ α₂ β u v := by
        unfold mixChg mixChg1
        rw [ef, eg]
        simp only [hsing, dot_piKron_single hC hm1]
      have hΛi : singForm m x₀ Λ f g = Λ i u v := by
        change singForm m x₀ Λ (SP m l *ᵥ φ) (SP m l *ᵥ ψ) = _
        rw [hli, singForm_SP_sing hm1 x₀ Λ hΛ i φ ψ]
        simp only [u, v, f, g, hli]
      have hnu : ip m f f = ∑ a, m i a * u a ^ 2 := by
        rw [ef, ip_single hm1]
        exact sum_congr rfl fun a _ => by ring
      have hnv : ip m g g = ∑ a, m i a * v a ^ 2 := by
        rw [eg, ip_single hm1]
        exact sum_congr rfl fun a _ => by ring
      rw [hc, hΛi, hnu, hnv]
      exact h1
  · -- a sector of at least two coordinates: the singleton forms vanish
    have hlne : ∀ j, l ≠ sing j := by
      intro j hj
      have : S = {j} := by
        simp only [S, hj]
        exact sing_filter j
      rw [this, card_singleton] at hS
      omega
    rw [singForm_SP_of_ne hm1 x₀ Λ hΛ l hlne φ ψ, sub_zero]
    have hpρ : ∏ j ∈ S, ρ ≤ ρ ^ 2 :=
      prod_filter_le (δ := fun _ => ρ) (fun _ => hρ0) (fun _ => le_rfl) hρ0 hρ1 S hS
    have hpd : ∏ j ∈ S, d ≤ d ^ 2 :=
      prod_filter_le (δ := fun _ => d) (fun _ => hd0) (fun _ => le_rfl) hd0 hd1 S hS
    have hρS : 0 ≤ ∏ j ∈ S, ρ := prod_nonneg fun _ _ => hρ0
    have hdS : 0 ≤ ∏ j ∈ S, d := prod_nonneg fun _ _ => hd0
    set F := Real.sqrt (ip m f f)
    set G := Real.sqrt (ip m g g)
    have hF : 0 ≤ F := Real.sqrt_nonneg _
    have hG : 0 ≤ G := Real.sqrt_nonneg _
    have hFG : 0 ≤ F * G := mul_nonneg hF hG
    have t1 : ∀ c, |f ⬝ᵥ (piKron (P c) *ᵥ g)| ≤ ρ ^ 2 * (F * G) := fun c => by
      have h : |f ⬝ᵥ (piKron (P c) *ᵥ g)| ≤ (∏ j ∈ S, ρ) * F * G := abs_le_of_sq_le' hf0 hρS
        (sector_dot_sq_le hm hm1 (hP c) (hPn c) (fun _ => ρ) (hρ c) l f ψ)
      refine h.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hpρ hFG
    have t2 : ∀ c, |g ⬝ᵥ (piKron (P c) *ᵥ f)| ≤ ρ ^ 2 * (F * G) := fun c => by
      have h : |g ⬝ᵥ (piKron (P c) *ᵥ f)| ≤ (∏ j ∈ S, ρ) * G * F := abs_le_of_sq_le' hg0 hρS
        (sector_dot_sq_le hm hm1 (hP c) (hPn c) (fun _ => ρ) (hρ c) l g φ)
      refine h.trans ?_
      rw [mul_assoc, mul_comm G F]
      exact mul_le_mul_of_nonneg_right hpρ hFG
    have t3 : |f ⬝ᵥ (piKron C *ᵥ g)| ≤ d ^ 2 * (F * G) := by
      have h : |f ⬝ᵥ (piKron C *ᵥ g)| ≤ (∏ j ∈ S, d) * F * G := abs_le_of_sq_le' hf0 hdS
        (sector_dot_sq_le hm hm1 hC hCn (fun _ => d) hd l f ψ)
      refine h.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hpd hFG
    have tc : ∀ c, |w c * (α₁ * (f ⬝ᵥ (piKron (P c) *ᵥ g)) + α₂ * (g ⬝ᵥ (piKron (P c) *ᵥ f)))| ≤
        |w c| * ((|α₁| + |α₂|) * ρ ^ 2 * (F * G)) := fun c => by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |α₁ * (f ⬝ᵥ (piKron (P c) *ᵥ g)) + α₂ * (g ⬝ᵥ (piKron (P c) *ᵥ f))|
          ≤ |α₁| * |f ⬝ᵥ (piKron (P c) *ᵥ g)| + |α₂| * |g ⬝ᵥ (piKron (P c) *ᵥ f)| := by
            rw [← abs_mul, ← abs_mul]
            exact abs_add_le _ _
        _ ≤ |α₁| * (ρ ^ 2 * (F * G)) + |α₂| * (ρ ^ 2 * (F * G)) :=
            add_le_add (mul_le_mul_of_nonneg_left (t1 c) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (t2 c) (abs_nonneg _))
        _ = (|α₁| + |α₂|) * ρ ^ 2 * (F * G) := by ring
    unfold mixChg
    calc |∑ c, w c * (α₁ * (f ⬝ᵥ (piKron (P c) *ᵥ g)) + α₂ * (g ⬝ᵥ (piKron (P c) *ᵥ f))) -
          β * (f ⬝ᵥ (piKron C *ᵥ g))|
        ≤ |∑ c, w c * (α₁ * (f ⬝ᵥ (piKron (P c) *ᵥ g)) + α₂ * (g ⬝ᵥ (piKron (P c) *ᵥ f)))| +
          |β * (f ⬝ᵥ (piKron C *ᵥ g))| := abs_sub _ _
      _ ≤ ∑ c, |w c| * ((|α₁| + |α₂|) * ρ ^ 2 * (F * G)) + |β| * (d ^ 2 * (F * G)) := by
          refine add_le_add ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ => tc c)) ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left t3 (abs_nonneg _)
      _ = ((∑ c, |w c|) * (|α₁| + |α₂|) * ρ ^ 2 + |β| * d ^ 2) * (F * G) := by
          rw [← sum_mul]
          ring
      _ ≤ e * (F * G) := mul_le_mul_of_nonneg_right hmulti hFG
      _ = e * F * G := by ring

/-- **The leading star of the block is bounded by the prime bounds** (`prop:signed-bounds`(b),
`‖L_{t,𝔅}‖ ≤ ℓ_t b^{-1/2}`): if every `Λ_j` is at most `ℓ` on mean-zero functions, then
`|singForm Λ φ ψ| ≤ ℓ ‖φ‖ ‖ψ‖` (an orthogonal sum over the singleton sectors). -/
theorem singForm_le (hm : ∀ j a, 0 ≤ m j a) (hm1 : ∀ j, ∑ a, m j a = 1) (x₀ : ∀ j, A j)
    (Λ : ∀ j, (A j → ℝ) → (A j → ℝ) → ℝ) (hΛ : ∀ j, Λ j 0 0 = 0) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hbound : ∀ j (u v : A j → ℝ), ∑ a, m j a * u a = 0 → ∑ a, m j a * v a = 0 →
      |Λ j u v| ≤ ℓ * Real.sqrt (∑ a, m j a * u a ^ 2) * Real.sqrt (∑ a, m j a * v a ^ 2))
    (φ ψ : (∀ j, A j) → ℝ) :
    |singForm m x₀ Λ φ ψ| ≤ ℓ * Real.sqrt (ip m φ φ) * Real.sqrt (ip m ψ ψ) := by
  refine bilin_le_of_sectors hm hm1 (singForm m x₀ Λ)
    (fun φ ψ => singForm_decomp hm1 x₀ Λ hΛ φ ψ) hℓ (fun l φ ψ => ?_) φ ψ
  by_cases hsl : ∃ i, l = sing i
  · obtain ⟨i, rfl⟩ := hsl
    set f := SP m (sing i) *ᵥ φ
    set g := SP m (sing i) *ᵥ ψ
    have hl : sing i ≠ fun _ => false := by
      intro h
      have := congrFun h i
      simp [sing] at this
    set u := fun a => f (Function.update x₀ i a)
    set v := fun a => g (Function.update x₀ i a)
    have ef : f = fun x => u (x i) := SP_single_eq (sing i) (sing_filter i) x₀ φ
    have eg : g = fun x => v (x i) := SP_single_eq (sing i) (sing_filter i) x₀ ψ
    have hu : ∑ a, m i a * u a = 0 := by
      have h := ip_one_SP hm1 hl φ
      change ip m (fun _ => 1) f = 0 at h
      rw [ef, show (fun _ : ∀ j, A j => (1 : ℝ)) = fun x => (fun _ : A i => (1 : ℝ)) (x i)
        from rfl, ip_single hm1 i (fun _ => (1 : ℝ)) u] at h
      simpa using h
    have hv : ∑ a, m i a * v a = 0 := by
      have h := ip_one_SP hm1 hl ψ
      change ip m (fun _ => 1) g = 0 at h
      rw [eg, show (fun _ : ∀ j, A j => (1 : ℝ)) = fun x => (fun _ : A i => (1 : ℝ)) (x i)
        from rfl, ip_single hm1 i (fun _ => (1 : ℝ)) v] at h
      simpa using h
    have hnu : ip m f f = ∑ a, m i a * u a ^ 2 := by
      rw [ef, ip_single hm1]
      exact sum_congr rfl fun a _ => by ring
    have hnv : ip m g g = ∑ a, m i a * v a ^ 2 := by
      rw [eg, ip_single hm1]
      exact sum_congr rfl fun a _ => by ring
    rw [singForm_SP_sing hm1 x₀ Λ hΛ i φ ψ, hnu, hnv]
    exact hbound i u v hu hv
  · push Not at hsl
    rw [singForm_SP_of_ne hm1 x₀ Λ hΛ l hsl φ ψ, abs_zero]
    exact mul_nonneg (mul_nonneg hℓ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Sarkozy.OpsCore
