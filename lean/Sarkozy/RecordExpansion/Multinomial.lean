module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Algebra.BigOperators.Field

/-!
# The multinomial theorem over kinds of variables

Used by the degree-class replacement, `lem:record:record-expansion` (v) of the
paper: the variables `v ∈ ι` are divided into kinds `l ∈ L` by
`kind : ι → Option L` (`none`: no kind), `ℛ_l = kindSet kind l`, and for a
degree vector `n : L → ℕ`, `kindMonos kind n` is the set of monomials `x^m`
supported on the kinds with degree `n_l` in the variables of kind `l`. The
multinomial theorem in the form used in the proof of (v) is

  `∏_l (∑_{v ∈ ℛ_l} z_v)^{n_l} / n_l! = ∑_{m ∈ kindMonos kind n} ∏_v z_v^{m_v} / m_v!`

(`prod_kind_pow_div`), from Mathlib's `Finset.sum_pow_eq_sum_piAntidiag` and
`Nat.multinomial_spec` for one kind.
-/

@[expose] public section

open Finset
open scoped BigOperators Nat

namespace Sarkozy.RecordExpansion

section OneKind

variable {ι : Type*} [DecidableEq ι]

/-- The multinomial theorem for one kind:
`(∑_{v ∈ R} z_v)^n / n! = ∑_{k} ∏_{v ∈ R} z_v^{k_v} / k_v!`, the sum over the
exponent vectors `k` supported on `R` with total `n`. -/
theorem sum_pow_div_factorial (R : Finset ι) (n : ℕ) (z : ι → ℝ) :
    (∑ v ∈ R, z v) ^ n / (n ! : ℝ) =
      ∑ k ∈ Finset.piAntidiag R n, ∏ v ∈ R, z v ^ k v / ((k v)! : ℝ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_piAntidiag] at hk
  have hspec := Nat.multinomial_spec R k
  rw [hk.1] at hspec
  have hpos : (0 : ℝ) < ∏ v ∈ R, ((k v)! : ℝ) := Finset.prod_pos fun v _ => by positivity
  have hmul : (0 : ℝ) < (Nat.multinomial R k : ℝ) := by
    exact_mod_cast Nat.multinomial_pos R k
  have hn : (n ! : ℝ) = (∏ v ∈ R, ((k v)! : ℝ)) * (Nat.multinomial R k : ℝ) := by
    rw [← hspec]
    push_cast
    ring
  rw [Finset.prod_div_distrib, hn]
  field_simp

end OneKind

section Kinds

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

/-- The variables of kind `l`. -/
def kindSet (kind : ι → Option L) (l : L) : Finset ι := univ.filter fun v => kind v = some l

/-- The monomials `x^m` supported on the variables of some kind, of degree `n_l` in
the variables of kind `l` for every `l`. -/
def kindMonos (kind : ι → Option L) (n : L → ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ => range (∑ l, n l + 1)).filter fun m =>
    (∀ v, kind v = none → m v = 0) ∧ ∀ l, ∑ v ∈ kindSet kind l, m v = n l

omit [DecidableEq ι] [Fintype L] in
theorem mem_kindSet {kind : ι → Option L} {l : L} {v : ι} :
    v ∈ kindSet kind l ↔ kind v = some l := by
  simp [kindSet]

theorem mem_kindMonos {kind : ι → Option L} {n : L → ℕ} {m : ι → ℕ} :
    m ∈ kindMonos kind n ↔
      (∀ v, kind v = none → m v = 0) ∧ ∀ l, ∑ v ∈ kindSet kind l, m v = n l := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    refine mem_filter.mpr ⟨?_, h⟩
    rw [Fintype.mem_piFinset]
    intro v
    rw [mem_range]
    rcases hv : kind v with _ | l
    · rw [h.1 v hv]
      omega
    · have h1 : m v ≤ ∑ w ∈ kindSet kind l, m w :=
        Finset.single_le_sum (fun w _ => Nat.zero_le _) (mem_kindSet.mpr hv)
      have h2 : n l ≤ ∑ l', n l' :=
        Finset.single_le_sum (fun w _ => Nat.zero_le _) (mem_univ l)
      rw [h.2 l] at h1
      omega

/-- **The multinomial theorem over kinds**:
`∏_l (∑_{v ∈ ℛ_l} z_v)^{n_l} / n_l! = ∑_{m ∈ kindMonos kind n} ∏_v z_v^{m_v} / m_v!`. -/
theorem prod_kind_pow_div (kind : ι → Option L) (n : L → ℕ) (z : ι → ℝ) :
    ∏ l, (∑ v ∈ kindSet kind l, z v) ^ n l / ((n l)! : ℝ) =
      ∑ m ∈ kindMonos kind n, ∏ v, z v ^ m v / ((m v)! : ℝ) := by
  simp_rw [sum_pow_div_factorial]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_nbij' (fun K v => (kind v).elim 0 (fun l => K l v))
    (fun m l v => if kind v = some l then m v else 0)
  · intro K hK
    rw [Fintype.mem_piFinset] at hK
    rw [mem_kindMonos]
    constructor
    · intro v hv
      simp [hv]
    · intro l
      rw [← (Finset.mem_piAntidiag.mp (hK l)).1]
      apply Finset.sum_congr rfl
      intro v hv
      simp [mem_kindSet.mp hv]
  · intro m hm
    rw [mem_kindMonos] at hm
    rw [Fintype.mem_piFinset]
    intro l
    rw [Finset.mem_piAntidiag]
    constructor
    · rw [← hm.2 l]
      apply Finset.sum_congr rfl
      intro v hv
      simp [mem_kindSet.mp hv]
    · intro v hv
      by_contra hvl
      apply hv
      have : kind v ≠ some l := fun h => hvl (mem_kindSet.mpr h)
      simp [this]
  · intro K hK
    rw [Fintype.mem_piFinset] at hK
    funext l v
    by_cases h : kind v = some l
    · simp [h]
    · simp only [h, ↓reduceIte]
      by_contra hne
      exact h (mem_kindSet.mp ((Finset.mem_piAntidiag.mp (hK l)).2 v (Ne.symm hne)))
  · intro m hm
    rw [mem_kindMonos] at hm
    funext v
    rcases h : kind v with _ | l
    · simp [hm.1 v h]
    · simp [h]
  · intro K hK
    rw [Fintype.mem_piFinset] at hK
    rw [← Finset.prod_fiberwise univ kind, Fintype.prod_option]
    have hnone : ∏ v ∈ univ with kind v = none,
        z v ^ ((kind v).elim 0 (fun l => K l v)) / (((kind v).elim 0 (fun l => K l v))! : ℝ) =
          1 := by
      apply Finset.prod_eq_one
      intro v hv
      rw [mem_filter] at hv
      simp [hv.2]
    rw [hnone, one_mul]
    apply Finset.prod_congr rfl
    intro l _
    apply Finset.prod_congr (by ext v; simp [kindSet])
    intro v hv
    simp [mem_kindSet.mp hv]

end Kinds

end Sarkozy.RecordExpansion
