module

public import Sarkozy.DensityChain2.PaperTail
public import Sarkozy.BlockAnchor.Prices

@[expose] public section

/-!
# The parity condition and the factorization `D_𝔟 = q_𝔟 c_𝔟` (`def:record:structured-energy`(a))

The paper (`subsec:scale:fibres`): "`q_E` [is] the product of the primes of the atoms of `E` with
`e_p = 1`, and `E_cl = E ∩ 𝒫₁` [its] clique primes. Thus `D_E = q_E ∏_{p ∈ E_cl} p^{e_p}`", and
`eq:square-step`, `sq(D) = sq(D₀) q_E² ∏_{E_cl} p^{e_p}`, "because `sq` is multiplicative on coprime
factors, `q_E` is squarefree and every `e_p` is even". The parity `e_p ∈ {1} ∪ 2ℕ` is fixed in
`def:record:functional`(a) (`e_p = 2m_p` on `𝒫₁`, `e_p = 1` elsewhere). `StandingData` records only
`m₀ i = pp i ^ ep i` with `ep i ≥ 1`; here the parity is a separate hypothesis
(`ParityCondition`), proved for the paper's exponents (`paperEP_parity`).

* `atomQ`, `atomC`: `q_𝔟` (the primes of `𝔟` with `e_p = 1`; the prime itself at a tail atom) and
  `c_𝔟` (the clique powers `p^{e_p}` of `𝔟`; `1` at a tail atom);
* **`crtModuli_eq_atomQ_mul_atomC`**: `D_𝔟 = q_𝔟 c_𝔟` (no parity needed);
* `squarefree_atomQ`, `coprime_atomQ_atomC`, `atomC_ne_zero`: from distinct primes (the prefix
  moduli pairwise coprime);
* **`isSquare_atomC`**: `c_𝔟` is a square, *from the parity condition*;
* `prod_atomC_eq`: `∏_𝔟 c_𝔟 = Q_cl⁰ := ∏_{e_p ≠ 1} p^{e_p}`, independent of the scale;
* `two_le_crtModuli`: `D_𝔟 ≥ 2` when every block is nonempty;
* **`leastSquare_rpow_eq_blockSel`**, **`hselF_of_parity`**: `sq(D_β)^a = q_β^{2a}` in the paper's
  `def:price` reading (`BlockAnchor.blockSel`), *from the parity condition*, and `sq(p)^a = p^{2a}`
  at a tail prime; hence DC1's `_hselF` whenever `blockSel ≤ selPre` (equality for the paper's
  `paperSel`, `paperSelAt`).
-/

namespace Sarkozy.DensityChain2

open Finset Function
open scoped BigOperators
open Sarkozy.EnvelopeEnergiesPaper Sarkozy.BlockFrame Sarkozy.Functional
  Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.EnvelopeInputs

/-- **The parity condition** `e_p ∈ {1} ∪ 2ℕ` of `def:record:functional`(a). -/
def ParityCondition {J₀ : Type} (ep : J₀ → ℕ) : Prop := ∀ i, ep i = 1 ∨ Even (ep i)

/-- The paper's exponents satisfy the parity condition: `e_p = 2𝔪` at `p ≡ 1 (4)`, `1` otherwise. -/
theorem paperEP_parity : ParityCondition paperEP := by
  intro i
  unfold paperEP
  split_ifs
  · right
    unfold PartV.prefixExponent
    exact even_two_mul _
  · left
    rfl

/-- A product of pairwise coprime squarefree numbers is squarefree. -/
theorem squarefree_prod_of_coprime {ι : Type} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, Squarefree (f i)) (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j)) :
    Squarefree (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi]
    have hcop : (f i).Coprime (∏ j ∈ s, f j) := Nat.Coprime.prod_right fun j hj =>
      hc i (mem_insert_self i s) j (mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    refine (Nat.squarefree_mul hcop).mpr ⟨hf i (mem_insert_self i s), ih (fun j hj =>
      hf j (mem_insert_of_mem hj)) fun j hj k hk => hc j (mem_insert_of_mem hj) k
        (mem_insert_of_mem hk)⟩

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]

variable (blk p) in
/-- `q_𝔟`: the product of the primes of the atom with `e_p = 1` (a tail atom is its prime). -/
def atomQ (pp ep : J₀ → ℕ) (L : ℕ) : BlockAtom Bk J L → ℕ
  | .inl β => ∏ i ∈ univ.filter (fun i : BlockIdx blk β => ep i.1 = 1), pp i.1
  | .inr j => p L j

variable (m₀ blk) in
/-- `c_𝔟`: the product of the clique powers `p^{e_p}` (`e_p ≠ 1`) of the atom (`1` at a tail
atom). -/
def atomC (ep : J₀ → ℕ) (L : ℕ) : BlockAtom Bk J L → ℕ
  | .inl β => ∏ i ∈ univ.filter (fun i : BlockIdx blk β => ¬ep i.1 = 1), m₀ i.1
  | .inr _ => 1

omit [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] [(L : ℕ) → Fintype (J L)]
  [(L : ℕ) → DecidableEq (J L)] [∀ (L : ℕ) (j : J L), NeZero (p L j)] in
/-- **`D_𝔟 = q_𝔟 c_𝔟`**. -/
theorem crtModuli_eq_atomQ_mul_atomC {pp ep : J₀ → ℕ} (hm : ∀ i, m₀ i = pp i ^ ep i) (L : ℕ)
    (b : BlockAtom Bk J L) :
    crtModuli m₀ blk p L b = atomQ blk p pp ep L b * atomC m₀ blk ep L b := by
  cases b with
  | inl β =>
    change ∏ i : BlockIdx blk β, m₀ i.1 = _
    rw [← prod_filter_mul_prod_filter_not univ (fun i : BlockIdx blk β => ep i.1 = 1)]
    congr 1
    apply prod_congr rfl
    intro i hi
    rw [mem_filter] at hi
    rw [hm, hi.2, pow_one]
  | inr j => exact (mul_one _).symm

omit [Fintype J₀] [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] in
theorem coprime_pp_m₀ {pp ep : J₀ → ℕ} (hm : ∀ i, m₀ i = pp i ^ ep i) (hep : ∀ i, 1 ≤ ep i)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) {i j : J₀} (hij : i ≠ j) :
    (pp i).Coprime (m₀ j) := by
  have hd : pp i ∣ m₀ i := by
    rw [hm i]
    exact dvd_pow_self _ (by have := hep i; omega)
  exact Nat.Coprime.coprime_dvd_left hd (h0 hij)

omit [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] [(L : ℕ) → Fintype (J L)]
  [(L : ℕ) → DecidableEq (J L)] [∀ (L : ℕ) (j : J L), NeZero (p L j)] in
/-- `q_𝔟` is squarefree. -/
theorem squarefree_atomQ {pp ep : J₀ → ℕ} (hm : ∀ i, m₀ i = pp i ^ ep i)
    (hpp : ∀ i, (pp i).Prime) (hep : ∀ i, 1 ≤ ep i)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (hp : ∀ L j, (p L j).Prime) (L : ℕ)
    (b : BlockAtom Bk J L) : Squarefree (atomQ blk p pp ep L b) := by
  cases b with
  | inl β =>
    apply squarefree_prod_of_coprime
    · intro i _
      exact (hpp i.1).prime.squarefree
    · intro i hi j _ hij
      have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have h := coprime_pp_m₀ hm hep h0 hij'
      rw [hm j.1] at h
      exact Nat.Coprime.coprime_dvd_right (dvd_pow_self _ (by have := hep j.1; omega)) h
  | inr j => exact (hp L j).prime.squarefree

omit [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] [(L : ℕ) → Fintype (J L)]
  [(L : ℕ) → DecidableEq (J L)] [∀ (L : ℕ) (j : J L), NeZero (p L j)] in
/-- `q_𝔟` and `c_𝔟` are coprime. -/
theorem coprime_atomQ_atomC {pp ep : J₀ → ℕ} (hm : ∀ i, m₀ i = pp i ^ ep i)
    (hep : ∀ i, 1 ≤ ep i) (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ)
    (b : BlockAtom Bk J L) : (atomQ blk p pp ep L b).Coprime (atomC m₀ blk ep L b) := by
  cases b with
  | inl β =>
    apply Nat.Coprime.prod_left
    intro i hi
    apply Nat.Coprime.prod_right
    intro j hj
    rw [mem_filter] at hi hj
    have hij : i.1 ≠ j.1 := fun h => hj.2 (h ▸ hi.2)
    exact coprime_pp_m₀ hm hep h0 hij
  | inr j => exact Nat.coprime_one_right _

omit [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] [(L : ℕ) → Fintype (J L)]
  [(L : ℕ) → DecidableEq (J L)] in
/-- **`c_𝔟` is a square**, by the parity condition. -/
theorem isSquare_atomC {pp ep : J₀ → ℕ} (hm : ∀ i, m₀ i = pp i ^ ep i)
    (hpar : ParityCondition ep) (L : ℕ) (b : BlockAtom Bk J L) :
    IsSquare (atomC m₀ blk ep L b) := by
  cases b with
  | inl β =>
    apply isSquare_prod
    intro i hi
    rw [mem_filter] at hi
    rw [hm i.1]
    exact ((hpar i.1).resolve_left hi.2).isSquare_pow _
  | inr j => exact ⟨1, rfl⟩

omit [DecidableEq J₀] [Fintype Bk] [(L : ℕ) → Fintype (J L)] [(L : ℕ) → DecidableEq (J L)] in
theorem atomC_ne_zero (ep : J₀ → ℕ) (L : ℕ) (b : BlockAtom Bk J L) :
    atomC (J := J) m₀ blk ep L b ≠ 0 := by
  cases b with
  | inl β => exact prod_ne_zero_iff.mpr fun i _ => NeZero.ne _
  | inr j => exact one_ne_zero

variable (m₀) in
/-- The clique constant `Q_cl⁰ = ∏_{e_p ≠ 1} p^{e_p}` of the prefix. -/
def cliqueConstant (ep : J₀ → ℕ) : ℕ := ∏ i ∈ univ.filter (fun i => ¬ep i = 1), m₀ i

omit [DecidableEq J₀] [∀ (i : J₀), NeZero (m₀ i)] [(L : ℕ) → DecidableEq (J L)] in
/-- `∏_𝔟 c_𝔟 = Q_cl⁰` at every scale. -/
theorem prod_atomC_eq (ep : J₀ → ℕ) (L : ℕ) :
    ∏ b, atomC (J := J) m₀ blk ep L b = cliqueConstant m₀ ep := by
  rw [Fintype.prod_sum_type]
  simp only [atomC, prod_const_one, mul_one]
  unfold cliqueConstant
  simp only [prod_filter]
  exact Fintype.prod_fiberwise blk (fun i => if ¬ep i = 1 then m₀ i else 1)

omit [DecidableEq J₀] [Fintype Bk] [(L : ℕ) → Fintype (J L)] [(L : ℕ) → DecidableEq (J L)]
  [∀ (L : ℕ) (j : J L), NeZero (p L j)] in
/-- `D_𝔟 ≥ 2` when every block is nonempty. -/
theorem two_le_crtModuli {pp ep : J₀ → ℕ} (hm : ∀ i, m₀ i = pp i ^ ep i)
    (hpp : ∀ i, (pp i).Prime) (hep : ∀ i, 1 ≤ ep i) (hne : ∀ β, ∃ i, blk i = β)
    (hp : ∀ L j, (p L j).Prime) (L : ℕ) (b : BlockAtom Bk J L) :
    2 ≤ crtModuli m₀ blk p L b := by
  cases b with
  | inl β =>
    obtain ⟨i, hi⟩ := hne β
    change 2 ≤ ∏ k : BlockIdx blk β, m₀ k.1
    have h2 : 2 ≤ m₀ i := by
      rw [hm i]
      exact (hpp i).two_le.trans (Nat.le_self_pow (by have := hep i; omega) _)
    have hpos : 0 < ∏ k : BlockIdx blk β, m₀ k.1 :=
      prod_pos fun k _ => Nat.pos_of_ne_zero (NeZero.ne _)
    exact h2.trans (Nat.le_of_dvd hpos
      (dvd_prod_of_mem (fun k : BlockIdx blk β => m₀ k.1) (mem_univ ⟨i, hi⟩)))
  | inr j => exact (hp L j).two_le

omit [∀ (i : J₀), NeZero (m₀ i)] [Fintype Bk] in
/-- **`sq(D_β)^a = q_β^{2a}`** in the paper's reading `def:price` (`BlockAnchor.blockSel`:
`p^{2a}` at `e_p = 1`, `p^{e_p a}` at a clique prime), by the parity condition. -/
theorem leastSquare_rpow_eq_blockSel {pp ep : J₀ → ℕ} (hm : ∀ i, m₀ i = pp i ^ ep i)
    (hpp : ∀ i, (pp i).Prime) (hpar : ParityCondition ep)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (a : ℝ) (β : Bk) :
    ((leastSquare (blockModulus m₀ blk β) : ℕ) : ℝ) ^ a = blockSel a pp ep blk β := by
  have hpair : Pairwise fun i j : BlockIdx blk β => (m₀ i.1).Coprime (m₀ j.1) :=
    fun i j hij => h0 fun h => hij (Subtype.ext h)
  change ((leastSquare (∏ i : BlockIdx blk β, m₀ i.1) : ℕ) : ℝ) ^ a = _
  rw [leastSquare_prod_coprime (fun i : BlockIdx blk β => m₀ i.1) hpair univ, Nat.cast_prod,
    ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  unfold blockSel
  apply prod_congr rfl
  intro i _
  unfold coordSel
  rw [hm i.1]
  rcases hpar i.1 with h1 | ⟨k, hk⟩
  · simp only [h1, ↓reduceIte]
    rw [pow_one, leastSquare_prime (hpp i.1), Nat.cast_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  · have hk2 : ep i.1 = 2 * k := by omega
    have hne : ep i.1 ≠ 1 := by omega
    simp only [hne, ↓reduceIte]
    rw [hk2, leastSquare_prime_pow_two_mul (hpp i.1), Nat.cast_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]

end Sarkozy.DensityChain2
