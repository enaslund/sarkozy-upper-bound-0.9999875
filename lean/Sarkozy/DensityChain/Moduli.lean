module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section

/-!
# The modulus conditions of `def:record:structured-energy` and the large unions

`def:record:structured-energy`(a) asks a selected set `E` with `q_E ≤ N^τ`, where `D_E = q_E c_E`
with `q_E` the product of the primes with `e_p = 1` (squarefree) and `c_E` the product of the
prime powers with `e_p` even (a square, at most `Q_cl`). The sets with `q_E > N^τ` are the large
unions of `lem:record:density-lp`. This file proves the dichotomy from a per-atom factorization:

* **`moduli_dichotomy`**: if every atom modulus factors as `m_𝔟 = w_𝔟 c_𝔟` (`w_𝔟` squarefree,
  `c_𝔟` a nonzero square, coprime), the moduli are pairwise coprime and `∏_𝔟 c_𝔟 ≤ Q_cl`, then
  every set `S` of atoms either satisfies the modulus conditions (`q_S = ∏_S w`, `c_S = ∏_S c`,
  `q_S ≤ T`), or is large: `T < ∏_{𝔟 ∈ S} w_𝔟`;
* `prod_ne_one_of_nonempty`: `D_S ≠ 1` for nonempty `S` when every modulus is at least `2`.
-/

namespace Sarkozy.DensityChain

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem squarefree_prod_of_coprime (s : Finset ι) (w : ι → ℕ) (hw : ∀ b ∈ s, Squarefree (w b))
    (hcop : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' → (w b).Coprime (w b')) : Squarefree (∏ b ∈ s, w b) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi]
    apply (Nat.squarefree_mul (Nat.Coprime.prod_right fun j hj =>
      hcop i (mem_insert_self i s) j (mem_insert_of_mem hj) (fun h => hi (h ▸ hj)))).mpr
    exact ⟨hw i (mem_insert_self i s), ih (fun b hb => hw b (mem_insert_of_mem hb))
      (fun b hb b' hb' hne => hcop b (mem_insert_of_mem hb) b' (mem_insert_of_mem hb') hne)⟩

theorem isSquare_prod (s : Finset ι) (c : ι → ℕ) (hc : ∀ b ∈ s, IsSquare (c b)) :
    IsSquare (∏ b ∈ s, c b) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi]
    exact (hc i (mem_insert_self i s)).mul (ih fun b hb => hc b (mem_insert_of_mem hb))

/-- **The modulus conditions or a large union** (see the module docstring). -/
theorem moduli_dichotomy [Fintype ι] (m w c : ι → ℕ) (hm : ∀ b, m b = w b * c b)
    (hw : ∀ b, Squarefree (w b)) (hc : ∀ b, IsSquare (c b)) (hc0 : ∀ b, c b ≠ 0)
    (hwc : ∀ b, (w b).Coprime (c b)) (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Qcl : ℕ} (hQ : ∏ b, c b ≤ Qcl) (T : ℝ) (S : Finset ι) :
    (∃ qE cE : ℕ, ∏ b ∈ S, m b = qE * cE ∧ Squarefree qE ∧ IsSquare cE ∧ cE ≠ 0 ∧
      cE ≤ Qcl ∧ qE.Coprime cE ∧ (qE : ℝ) ≤ T) ∨
      T < ∏ b, ((if b ∈ S then w b else 1 : ℕ) : ℝ) := by
  have hcopw : ∀ b b', b ≠ b' → (w b).Coprime (w b') := fun b b' hne =>
    Nat.Coprime.coprime_dvd_left (by rw [hm b]; exact dvd_mul_right _ _)
      (Nat.Coprime.coprime_dvd_right (by rw [hm b']; exact dvd_mul_right _ _) (hpair hne))
  have hcopwc : ∀ b b', (w b).Coprime (c b') := by
    intro b b'
    by_cases hbb : b = b'
    · rw [← hbb]; exact hwc b
    · exact Nat.Coprime.coprime_dvd_left (by rw [hm b]; exact dvd_mul_right _ _)
        (Nat.Coprime.coprime_dvd_right (by rw [hm b']; exact dvd_mul_left _ _) (hpair hbb))
  have hprod : ∏ b ∈ S, m b = (∏ b ∈ S, w b) * ∏ b ∈ S, c b := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b _ => hm b
  have hW : ∏ b, ((if b ∈ S then w b else 1 : ℕ) : ℝ) = ((∏ b ∈ S, w b : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    simp only [Nat.cast_ite, Nat.cast_one]
    rw [← prod_filter]
    congr 1
    ext b
    simp
  by_cases hT : ((∏ b ∈ S, w b : ℕ) : ℝ) ≤ T
  · left
    refine ⟨∏ b ∈ S, w b, ∏ b ∈ S, c b, hprod,
      squarefree_prod_of_coprime S w (fun b _ => hw b) (fun b _ b' _ hne => hcopw b b' hne),
      isSquare_prod S c (fun b _ => hc b), ?_, ?_, ?_, hT⟩
    · exact prod_ne_zero_iff.mpr fun b _ => hc0 b
    · refine le_trans ?_ hQ
      exact prod_le_prod_of_subset_of_one_le (subset_univ S)
        (fun b _ _ => Nat.one_le_iff_ne_zero.mpr (hc0 b))
    · exact Nat.Coprime.prod_left fun b _ => Nat.Coprime.prod_right fun b' _ => hcopwc b b'
  · right
    rw [hW]
    exact lt_of_not_ge hT

omit [DecidableEq ι] in
/-- `D_S ≠ 1` for a nonempty set of atoms whose moduli are at least `2`. -/
theorem prod_ne_one_of_nonempty (m : ι → ℕ) (hm : ∀ b, 2 ≤ m b) {S : Finset ι}
    (hS : S.Nonempty) : ∏ b ∈ S, m b ≠ 1 := by
  obtain ⟨b, hb⟩ := hS
  intro h1
  have h2 : m b ∣ ∏ b ∈ S, m b := dvd_prod_of_mem m hb
  rw [h1, Nat.dvd_one] at h2
  have := hm b
  omega

end Sarkozy.DensityChain
