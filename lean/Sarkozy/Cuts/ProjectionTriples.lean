module

public import Sarkozy.Cuts.CutInvariance
public import Sarkozy.Cuts.CutTransport

/-!
# Cuts, V′: the density constants of `lem:record:projection` (b)

`13_cuts_correlations.tex`, `lem:record:projection` (b), over a finite field `F` of odd
characteristic with `p = |F| ≥ 3` (the paper: `F = 𝔽_p`), and `q = 1/p`.
* `ν_F = λ(graphF)` is the uniform law on triples of distinct labels with `x₂ - x₀ ∈ Q`, the law of
  the graph on `{0, 1, 2}` with the single edge `0 → 2`.
* `ν_E = λ(graphE)` is the uniform law on triples of distinct labels.

A density `ϱ_I ≥ max dν_I/dυ_I` is stated as: every value of the marginal on `I` has
probability at most `ϱ_I/p^{|I|}`.

* `vertex_marginal`: `ϱ_I = 1` for one label, for both laws.
* `nuE_pair02`, `nuE_pair`, `nuE_triple`: for `ν_E`, `ϱ_I = 1/(1 - q)` for two labels (the pair
  `{0, 2}` first; any pair by permuting the labels, `nuE_perm`) and `ϱ = 1/((1 - q)(1 - 2q))` for
  all three.
* `nuF_pair02`, `nuF_pair01`, `nuF_pair12`, `nuF_triple`: for `ν_F`, `ϱ_{0,2} = 2/(1 - q)`,
  `ϱ_{0,1} = ϱ_{1,2} = 1/(1 - 2q)`, and `ϱ_{0,1,2} = 2/((1 - q)(1 - 2q))`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Labellings

section Fin3

variable {F : Type*}

theorem injective_fin3_iff (y : Fin 3 → F) :
    Function.Injective y ↔ y 0 ≠ y 1 ∧ y 0 ≠ y 2 ∧ y 1 ≠ y 2 := by
  constructor
  · intro h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> have := h e <;> simp at this
  · rintro ⟨h01, h02, h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem vec3_eta (y : Fin 3 → F) : ![y 0, y 1, y 2] = y := by
  funext i
  fin_cases i <;> rfl

end Fin3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The graph on `{0, 1, 2}` with no edges (`ν_E`). -/
def graphE : OrientedGraph (Fin 3) where
  E := ∅
  loopless _ h := absurd h (Finset.notMem_empty _)
  oriented _ _ h _ := absurd h (Finset.notMem_empty _)

/-- The graph on `{0, 1, 2}` with the single edge `0 → 2` (`ν_F`). -/
def graphF : OrientedGraph (Fin 3) where
  E := {(0, 2)}
  loopless u h := by
    rw [Finset.mem_singleton, Prod.mk.injEq] at h
    exact absurd (h.1.symm.trans h.2) (by decide)
  oriented u v h h' := by
    rw [Finset.mem_singleton, Prod.mk.injEq] at h h'
    exact absurd (h'.1.symm.trans h.2) (by decide)

theorem mem_inj_graphE (y : Fin 3 → F) :
    y ∈ injLabellings F graphE ↔ Function.Injective y ∧ True := by
  rw [SpecData.mem_inj]
  constructor
  · rintro ⟨h1, _⟩
    exact ⟨fun a b h => h1 a (Finset.mem_univ _) b (Finset.mem_univ _) h, trivial⟩
  · rintro ⟨h, _⟩
    exact ⟨fun a _ b _ hab => h hab, fun e he => absurd he (Finset.notMem_empty _)⟩

theorem mem_inj_graphF (y : Fin 3 → F) :
    y ∈ injLabellings F graphF ↔ Function.Injective y ∧ quadraticChar F (y 2 - y 0) = 1 := by
  rw [SpecData.mem_inj]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b h => h1 a (Finset.mem_univ _) b (Finset.mem_univ _) h,
      h2 (0, 2) (Finset.mem_singleton_self _) (Finset.mem_univ _) (Finset.mem_univ _)⟩
  · rintro ⟨h, hc⟩
    refine ⟨fun a _ b _ hab => h hab, fun e he _ _ => ?_⟩
    rw [show graphF.E = {(0, 2)} from rfl, Finset.mem_singleton] at he
    subst he
    exact hc

/-! ### Counting -/

/-- The fibre of `(x₀, x₂)` at an admissible pair has `p - 2` points. -/
theorem card_fibre02 (G : OrientedGraph (Fin 3)) (R : F → F → Prop) [DecidableRel R]
    (hG : ∀ y : Fin 3 → F, y ∈ injLabellings F G ↔ Function.Injective y ∧ R (y 0) (y 2))
    (a b : F) :
    ((injLabellings F G).filter (fun y => y 0 = a ∧ y 2 = b)).card =
      if a ≠ b ∧ R a b then Fintype.card F - 2 else 0 := by
  classical
  by_cases hab : a ≠ b ∧ R a b
  · rw [ite_eq_left hab]
    have hcard : (Finset.univ.filter (fun c : F => c ≠ a ∧ c ≠ b)).card = Fintype.card F - 2 := by
      have e : Finset.univ.filter (fun c : F => c ≠ a ∧ c ≠ b) = Finset.univ \ {a, b} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
          Finset.mem_insert, Finset.mem_singleton, not_or]
      rw [e, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Finset.card_pair hab.1]
    rw [← hcard]
    refine Finset.card_nbij' (fun y => y 1) (fun c => ![a, c, b]) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨hyI, h0, h2⟩ := hy
      obtain ⟨hinj, _⟩ := (hG y).1 hyI
      obtain ⟨h01, _, h12⟩ := (injective_fin3_iff y).1 hinj
      exact ⟨fun h => h01 (h0.trans h.symm), fun h => h12 (h.trans h2.symm)⟩
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hc ⊢
      refine ⟨(hG _).2 ⟨(injective_fin3_iff _).2 ?_, ?_⟩, ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        exact ⟨fun h => hc.1 h.symm, hab.1, hc.2⟩
      · simpa using hab.2
      · simp
      · simp
    · intro y hy
      simp only [Finset.coe_filter] at hy
      obtain ⟨_, h0, h2⟩ := hy
      rw [← h0, ← h2]
      exact vec3_eta y
    · intro c _
      simp
  · rw [ite_eq_right hab, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hab'
    obtain ⟨hinj, hR⟩ := (hG y).1 hy
    obtain ⟨_, h02, _⟩ := (injective_fin3_iff y).1 hinj
    apply hab
    rw [← hab'.1, ← hab'.2]
    exact ⟨h02, hR⟩

/-- `|Inj(G)| = ∑_{a,b} #(fibre of (a, b))`. -/
theorem card_inj_fiberwise (G : OrientedGraph (Fin 3)) :
    ((injLabellings F G).card : ℝ) =
      ∑ a : F, ∑ b : F, (((injLabellings F G).filter (fun y => y 0 = a ∧ y 2 = b)).card : ℝ) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun y : Fin 3 → F => (y 0, y 2))
    (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  push_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp only [Prod.mk.injEq]

/-- The `(x₀, x₂)`-marginal: `P(x₀ = a, x₂ = b) = #(fibre)/|Inj(G)|`. -/
theorem prob_pair02 (G : OrientedGraph (Fin 3)) (hne : (injLabellings F G).Nonempty) (a b : F) :
    (graphLaw G hne).expect (fun y => if y 0 = a ∧ y 2 = b then (1 : ℝ) else 0) =
      ((injLabellings F G).filter (fun y => y 0 = a ∧ y 2 = b)).card /
        (injLabellings F G).card := by
  classical
  rw [SpecData.graphLaw_expect', Finset.sum_boole]

/-- `2 #Q = p - 1` for the nonzero squares `Q` of a finite field of odd characteristic. -/
theorem two_mul_card_sq (hF : ringChar F ≠ 2) :
    2 * ((Finset.univ.filter (fun d : F => quadraticChar F d = 1)).card : ℝ) =
      Fintype.card F - 1 := by
  classical
  have hpt : ∀ d : F, (quadraticChar F d : ℤ) =
      (if quadraticChar F d = 1 then 1 else 0) - (if quadraticChar F d = -1 then 1 else 0) := by
    intro d
    by_cases hd : d = 0
    · subst hd
      simp
    · rcases quadraticChar_dichotomy hd with h | h <;> simp [h]
  have hpt2 : ∀ d : F, (if d = 0 then (1 : ℤ) else 0) + (if quadraticChar F d = 1 then 1 else 0) +
      (if quadraticChar F d = -1 then 1 else 0) = 1 := by
    intro d
    by_cases hd : d = 0
    · subst hd
      simp
    · rcases quadraticChar_dichotomy hd with h | h <;> simp [h, hd]
  have hsum := quadraticChar_sum_zero hF
  rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.sum_boole] at hsum
  have hsum2 : ∑ d : F, ((if d = 0 then (1 : ℤ) else 0) + (if quadraticChar F d = 1 then 1 else 0) +
      (if quadraticChar F d = -1 then 1 else 0)) = Fintype.card F := by
    rw [Finset.sum_congr rfl (fun d _ => hpt2 d)]
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
    Finset.sum_boole] at hsum2
  have h0 : (Finset.univ.filter (fun d : F => d = 0)).card = 1 := by
    rw [Finset.filter_eq' Finset.univ (0 : F)]
    simp
  rw [h0] at hsum2
  have h1 : (2 : ℤ) * (Finset.univ.filter (fun d : F => quadraticChar F d = 1)).card =
      Fintype.card F - 1 := by
    push_cast at hsum hsum2 ⊢
    linarith
  exact_mod_cast h1

/-- Translation: `#{b : χ(b - a) = 1} = #Q`. -/
theorem card_sq_shift (a : F) :
    (Finset.univ.filter (fun b : F => quadraticChar F (b - a) = 1)).card =
      (Finset.univ.filter (fun d : F => quadraticChar F d = 1)).card := by
  refine Finset.card_nbij' (fun b => b - a) (fun d => d + a) ?_ ?_ ?_ ?_
  · intro b hb
    simpa using hb
  · intro d hd
    simpa using hd
  · intro b _
    simp
  · intro d _
    simp

/-! ### One label -/

/-- **`lem:record:projection` (b), one label.** Every one-vertex marginal is uniform, so `ϱ = 1`. -/
theorem vertex_marginal [Nonempty F] (G : OrientedGraph (Fin 3))
    (hne : (injLabellings F G).Nonempty) (i : Fin 3) (a : F) :
    (graphLaw G hne).expect (fun y => if y i = a then (1 : ℝ) else 0) = 1 / Fintype.card F := by
  rw [graphLaw_vertex_uniform G hne i (fun c => if c = a then (1 : ℝ) else 0),
    FiniteLaw.expect_uniform, Finset.sum_boole]
  simp [Finset.filter_eq']

/-! ### `ν_E` -/

section NuE

variable (hp : 3 ≤ Fintype.card F)
include hp

theorem card_inj_graphE :
    ((injLabellings F graphE).card : ℝ) =
      Fintype.card F * ((Fintype.card F - 1) * (Fintype.card F - 2)) := by
  rw [card_inj_fiberwise]
  have hf : ∀ a b : F, (((injLabellings F graphE).filter (fun y => y 0 = a ∧ y 2 = b)).card : ℝ) =
      if a = b then 0 else ((Fintype.card F : ℝ) - 2) := by
    intro a b
    rw [card_fibre02 graphE (fun _ _ => True) (fun y => mem_inj_graphE y) a b]
    by_cases hab : a = b
    · simp [hab]
    · rw [ite_eq_left (show a ≠ b ∧ True from ⟨hab, trivial⟩), ite_eq_right hab,
        Nat.cast_sub (by omega)]
      norm_num
  simp only [hf]
  have hrow : ∀ a : F, ∑ b : F, (if a = b then (0 : ℝ) else ((Fintype.card F : ℝ) - 2)) =
      ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) := by
    intro a
    have e : ∀ b : F, (if a = b then (0 : ℝ) else ((Fintype.card F : ℝ) - 2)) =
        ((Fintype.card F : ℝ) - 2) - (if a = b then ((Fintype.card F : ℝ) - 2) else 0) := by
      intro b
      split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit hp in
theorem graphE_nonempty (hF : ringChar F ≠ 2) : (injLabellings F graphE).Nonempty := by
  refine ⟨![0, 1, -1], (mem_inj_graphE _).2 ⟨(injective_fin3_iff _).2 ?_, trivial⟩⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨zero_ne_one, ?_, ?_⟩
  · intro h
    exact one_ne_zero (neg_eq_zero.mp h.symm)
  · intro h
    exact (Ring.neg_one_ne_one_of_char_ne_two hF) h.symm

/-- **`lem:record:projection` (b), `ν_E`, two labels.** `P(x₀ = a, x₂ = b) ≤ ϱ/p²` with
`ϱ = 1/(1 - q)`. -/
theorem nuE_pair02 (hne : (injLabellings F graphE).Nonempty) (a b : F) :
    (graphLaw graphE hne).expect (fun y => if y 0 = a ∧ y 2 = b then (1 : ℝ) else 0) ≤
      (1 / (1 - 1 / (Fintype.card F : ℝ))) / (Fintype.card F : ℝ) ^ 2 := by
  have hp3 : (3 : ℝ) ≤ Fintype.card F := by exact_mod_cast hp
  rw [prob_pair02, card_inj_graphE hp]
  rw [card_fibre02 graphE (fun _ _ => True) (fun y => mem_inj_graphE y) a b]
  have hpos : (0 : ℝ) < Fintype.card F * ((Fintype.card F - 1) * (Fintype.card F - 2)) :=
    mul_pos (by linarith) (mul_pos (by linarith) (by linarith))
  have hrhs : (1 / (1 - 1 / (Fintype.card F : ℝ))) / (Fintype.card F : ℝ) ^ 2 =
      1 / (Fintype.card F * (Fintype.card F - 1)) := by
    have h1 : (Fintype.card F : ℝ) ≠ 0 := by positivity
    have h2 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hrhs]
  split_ifs with hab
  · rw [Nat.cast_sub (by omega), div_le_div_iff₀ hpos (by nlinarith)]
    push_cast
    nlinarith
  · simp only [Nat.cast_zero, zero_div]
    have : (0 : ℝ) < Fintype.card F * (Fintype.card F - 1) := by nlinarith
    positivity

/-- **`lem:record:projection` (b), `ν_E`, three labels.** Every point has probability at most
`ϱ/p³` with `ϱ = 1/((1 - q)(1 - 2q))`. -/
theorem nuE_triple (hne : (injLabellings F graphE).Nonempty) (z : Fin 3 → F) :
    (graphLaw graphE hne).weight z ≤
      (1 / ((1 - 1 / (Fintype.card F : ℝ)) * (1 - 2 / (Fintype.card F : ℝ)))) /
        (Fintype.card F : ℝ) ^ 3 := by
  have hp3 : (3 : ℝ) ≤ Fintype.card F := by exact_mod_cast hp
  have hrhs : (1 / ((1 - 1 / (Fintype.card F : ℝ)) * (1 - 2 / (Fintype.card F : ℝ)))) /
      (Fintype.card F : ℝ) ^ 3 = 1 / (Fintype.card F * ((Fintype.card F - 1) *
        (Fintype.card F - 2))) := by
    have h1 : (Fintype.card F : ℝ) ≠ 0 := by positivity
    have h2 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
    have h3 : (Fintype.card F : ℝ) - 2 ≠ 0 := by linarith
    field_simp
  rw [hrhs, ← card_inj_graphE hp]
  change (if z ∈ injLabellings F graphE then 1 / ((injLabellings F graphE).card : ℝ) else 0) ≤ _
  split_ifs
  · exact le_rfl
  · have : (0 : ℝ) < (injLabellings F graphE).card := by exact_mod_cast Finset.card_pos.mpr hne
    positivity

omit hp in
/-- `ν_E` is invariant under permutations of the labels, so all pairs behave like `{0, 2}`. -/
theorem nuE_perm (hne : (injLabellings F graphE).Nonempty) (σ : Equiv.Perm (Fin 3))
    (Φ : (Fin 3 → F) → ℝ) :
    (graphLaw graphE hne).expect Φ =
      (graphLaw graphE hne).expect (fun y => Φ (fun i => y (σ.symm i))) :=
  graphLaw_iso graphE graphE σ (fun u w => by
    show (u, w) ∈ (∅ : Finset (Fin 3 × Fin 3)) ↔ (σ u, σ w) ∈ (∅ : Finset (Fin 3 × Fin 3))
    simp) hne hne Φ

/-- **`lem:record:projection` (b), `ν_E`, any two labels.** `P(x_i = a, x_j = b) ≤ ϱ/p²` with
`ϱ = 1/(1 - q)`, for `i ≠ j`. -/
theorem nuE_pair (hne : (injLabellings F graphE).Nonempty) {i j : Fin 3} (hij : i ≠ j) (a b : F) :
    (graphLaw graphE hne).expect (fun y => if y i = a ∧ y j = b then (1 : ℝ) else 0) ≤
      (1 / (1 - 1 / (Fintype.card F : ℝ))) / (Fintype.card F : ℝ) ^ 2 := by
  obtain ⟨τ, h0, h2⟩ : ∃ τ : Equiv.Perm (Fin 3), τ 0 = i ∧ τ 2 = j := by
    revert i j
    decide
  have h := nuE_perm hne τ.symm (fun z => if z 0 = a ∧ z 2 = b then (1 : ℝ) else 0)
  simp only [Equiv.symm_symm, h0, h2] at h
  rw [← h]
  exact nuE_pair02 hp hne a b

end NuE

/-! ### `ν_F` -/

section NuF

variable (hF : ringChar F ≠ 2) (hp : 3 ≤ Fintype.card F)
include hF hp

theorem card_inj_graphF :
    2 * ((injLabellings F graphF).card : ℝ) =
      Fintype.card F * ((Fintype.card F - 1) * (Fintype.card F - 2)) := by
  rw [card_inj_fiberwise]
  have hf : ∀ a b : F, (((injLabellings F graphF).filter (fun y => y 0 = a ∧ y 2 = b)).card : ℝ) =
      if quadraticChar F (b - a) = 1 then ((Fintype.card F : ℝ) - 2) else 0 := by
    intro a b
    rw [card_fibre02 graphF (fun a b => quadraticChar F (b - a) = 1) (fun y => mem_inj_graphF y) a b]
    by_cases hR : quadraticChar F (b - a) = 1
    · have hab : a ≠ b := by
        intro h
        rw [h, sub_self, quadraticChar_zero] at hR
        exact zero_ne_one hR
      rw [ite_eq_left (show a ≠ b ∧ quadraticChar F (b - a) = 1 from ⟨hab, hR⟩), ite_eq_left hR,
        Nat.cast_sub (by omega)]
      norm_num
    · rw [ite_eq_right (fun h : a ≠ b ∧ quadraticChar F (b - a) = 1 => hR h.2), ite_eq_right hR]
      norm_num
  simp only [hf]
  have hrow : ∀ a : F, ∑ b : F, (if quadraticChar F (b - a) = 1 then ((Fintype.card F : ℝ) - 2)
      else 0) = ((Fintype.card F : ℝ) - 2) *
        (Finset.univ.filter (fun d : F => quadraticChar F d = 1)).card := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_sq_shift a]
    ring
  simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hQ := two_mul_card_sq hF
  linear_combination ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 2)) * hQ

omit hp in
theorem graphF_nonempty : (injLabellings F graphF).Nonempty := by
  refine ⟨![0, -1, 1], (mem_inj_graphF _).2 ⟨(injective_fin3_iff _).2 ?_, ?_⟩⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨?_, zero_ne_one, ?_⟩
    · intro h
      exact one_ne_zero (neg_eq_zero.mp h.symm)
    · exact Ring.neg_one_ne_one_of_char_ne_two hF
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      sub_zero]
    exact MulChar.map_one (quadraticChar F)

/-- **`lem:record:projection` (b), `ν_F`, the pair `{0, 2}`.** `ϱ_{0,2} = 2/(1 - q)`. -/
theorem nuF_pair02 (hne : (injLabellings F graphF).Nonempty) (a b : F) :
    (graphLaw graphF hne).expect (fun y => if y 0 = a ∧ y 2 = b then (1 : ℝ) else 0) ≤
      (2 / (1 - 1 / (Fintype.card F : ℝ))) / (Fintype.card F : ℝ) ^ 2 := by
  have hp3 : (3 : ℝ) ≤ Fintype.card F := by exact_mod_cast hp
  have hI := card_inj_graphF hF hp
  rw [prob_pair02,
    card_fibre02 graphF (fun a b => quadraticChar F (b - a) = 1) (fun y => mem_inj_graphF y) a b]
  have hInj : (0 : ℝ) < (injLabellings F graphF).card := by exact_mod_cast Finset.card_pos.mpr hne
  have hrhs : (2 / (1 - 1 / (Fintype.card F : ℝ))) / (Fintype.card F : ℝ) ^ 2 =
      2 / (Fintype.card F * (Fintype.card F - 1)) := by
    have h1 : (Fintype.card F : ℝ) ≠ 0 := by positivity
    have h2 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hrhs]
  split_ifs with hab
  · rw [Nat.cast_sub (by omega), div_le_div_iff₀ hInj (by nlinarith)]
    push_cast
    nlinarith
  · simp only [Nat.cast_zero, zero_div]
    have : (0 : ℝ) < Fintype.card F * (Fintype.card F - 1) := by nlinarith
    positivity

omit hF hp in
/-- A fibre of `(x₀, x₁)` or `(x₁, x₂)` has at most `#Q` points. -/
theorem card_fibre_le_sq (a c : F) :
    ((injLabellings F graphF).filter (fun y => y 0 = a ∧ y 1 = c)).card ≤
        (Finset.univ.filter (fun d : F => quadraticChar F d = 1)).card ∧
      ((injLabellings F graphF).filter (fun y => y 1 = c ∧ y 2 = a)).card ≤
        (Finset.univ.filter (fun d : F => quadraticChar F d = 1)).card := by
  constructor
  · rw [← card_sq_shift a]
    refine Finset.card_le_card_of_injOn (fun y => y 2) (fun y hy => ?_) (fun y hy y' hy' h => ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨hyI, h0, _⟩ := hy
      rw [← h0]
      exact ((mem_inj_graphF y).1 hyI).2
    · simp only [Finset.coe_filter] at hy hy'
      obtain ⟨_, h0, h1⟩ := hy
      obtain ⟨_, h0', h1'⟩ := hy'
      rw [← vec3_eta y, ← vec3_eta y', h0, h1, h0', h1']
      simp only at h
      rw [h]
  · have e : (Finset.univ.filter (fun d : F => quadraticChar F d = 1)).card =
        (Finset.univ.filter (fun b : F => quadraticChar F (a - b) = 1)).card := by
      refine Finset.card_nbij' (fun d => a - d) (fun b => a - b) ?_ ?_ ?_ ?_
      · intro d hd
        simpa using hd
      · intro b hb
        simpa using hb
      · intro d _
        simp
      · intro b _
        simp
    rw [e]
    refine Finset.card_le_card_of_injOn (fun y => y 0) (fun y hy => ?_) (fun y hy y' hy' h => ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨hyI, _, h2⟩ := hy
      rw [← h2]
      exact ((mem_inj_graphF y).1 hyI).2
    · simp only [Finset.coe_filter] at hy hy'
      obtain ⟨_, h1, h2⟩ := hy
      obtain ⟨_, h1', h2'⟩ := hy'
      rw [← vec3_eta y, ← vec3_eta y', h1, h2, h1', h2']
      simp only at h
      rw [h]

/-- **`lem:record:projection` (b), `ν_F`, the pairs `{0, 1}`, `{1, 2}`.** `ϱ = 1/(1 - 2q)`. -/
theorem nuF_pair01 (hne : (injLabellings F graphF).Nonempty) (a c : F) :
    (graphLaw graphF hne).expect (fun y => if y 0 = a ∧ y 1 = c then (1 : ℝ) else 0) ≤
      (1 / (1 - 2 / (Fintype.card F : ℝ))) / (Fintype.card F : ℝ) ^ 2 ∧
    (graphLaw graphF hne).expect (fun y => if y 1 = c ∧ y 2 = a then (1 : ℝ) else 0) ≤
      (1 / (1 - 2 / (Fintype.card F : ℝ))) / (Fintype.card F : ℝ) ^ 2 := by
  classical
  have hp3 : (3 : ℝ) ≤ Fintype.card F := by exact_mod_cast hp
  have hI := card_inj_graphF hF hp
  have hQ := two_mul_card_sq hF
  obtain ⟨hf1, hf2⟩ := card_fibre_le_sq a c
  have hInj : (0 : ℝ) < (injLabellings F graphF).card := by exact_mod_cast Finset.card_pos.mpr hne
  have hrhs : (1 / (1 - 2 / (Fintype.card F : ℝ))) / (Fintype.card F : ℝ) ^ 2 =
      1 / (Fintype.card F * (Fintype.card F - 2)) := by
    have h1 : (Fintype.card F : ℝ) ≠ 0 := by positivity
    have h2 : (Fintype.card F : ℝ) - 2 ≠ 0 := by linarith
    field_simp
  rw [hrhs]
  have key : ∀ (P : (Fin 3 → F) → Prop) [DecidablePred P],
      ((injLabellings F graphF).filter P).card ≤
        (Finset.univ.filter (fun d : F => quadraticChar F d = 1)).card →
      (graphLaw graphF hne).expect (fun y => if P y then (1 : ℝ) else 0) ≤
        1 / (Fintype.card F * (Fintype.card F - 2)) := by
    intro P _ hP
    rw [SpecData.graphLaw_expect', Finset.sum_boole]
    have hP' : (((injLabellings F graphF).filter P).card : ℝ) ≤
        (Finset.univ.filter (fun d : F => quadraticChar F d = 1)).card := by exact_mod_cast hP
    rw [div_le_div_iff₀ hInj (by nlinarith)]
    nlinarith
  exact ⟨key _ hf1, key _ hf2⟩

/-- **`lem:record:projection` (b), `ν_F`, three labels.** `ϱ_{0,1,2} = 2/((1 - q)(1 - 2q))`. -/
theorem nuF_triple (hne : (injLabellings F graphF).Nonempty) (z : Fin 3 → F) :
    (graphLaw graphF hne).weight z ≤
      (2 / ((1 - 1 / (Fintype.card F : ℝ)) * (1 - 2 / (Fintype.card F : ℝ)))) /
        (Fintype.card F : ℝ) ^ 3 := by
  have hp3 : (3 : ℝ) ≤ Fintype.card F := by exact_mod_cast hp
  have hI := card_inj_graphF hF hp
  have hrhs : (2 / ((1 - 1 / (Fintype.card F : ℝ)) * (1 - 2 / (Fintype.card F : ℝ)))) /
      (Fintype.card F : ℝ) ^ 3 = 1 / (injLabellings F graphF).card := by
    have h1 : (Fintype.card F : ℝ) ≠ 0 := by positivity
    have h2 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
    have h3 : (Fintype.card F : ℝ) - 2 ≠ 0 := by linarith
    have hc : ((injLabellings F graphF).card : ℝ) =
        Fintype.card F * ((Fintype.card F - 1) * (Fintype.card F - 2)) / 2 := by linarith
    rw [hc]
    field_simp
  rw [hrhs]
  change (if z ∈ injLabellings F graphF then 1 / ((injLabellings F graphF).card : ℝ) else 0) ≤ _
  split_ifs
  · exact le_rfl
  · have : (0 : ℝ) < (injLabellings F graphF).card := by exact_mod_cast Finset.card_pos.mpr hne
    positivity

end NuF

end Sarkozy.Cuts
