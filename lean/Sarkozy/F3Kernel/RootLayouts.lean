module

public import Sarkozy.F3Kernel.ClassRootsB

/-!
# Root masks in the two layouts

Rows, columns, and initial segments of the edge order have the same interpretation in
the checker's two packed layouts. These identities supply coherence at class roots.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

theorem decM_row (G : Consts) (x : ℕ) :
    decM (rowM G x) = (decM G.EM).filter (fun e => e.1.val = x) := by
  rw [rowM, decM_land]
  ext e
  simp only [mem_inter, mem_filter, mem_decM]
  exact and_congr Iff.rfl (bit_shifted_FULL64 x e.2 e.1)

theorem decM_col (G : Consts) {y : ℕ} (hy : y < 36) :
    decM (colM G y) = (decM G.EM).filter (fun e => e.2.val = y) := by
  rw [colM, decM_land]
  ext e
  simp only [mem_inter, mem_filter, mem_decM, bit_shifted_LANE0 hy]

theorem edgeRank_low (e : Fin 36 × Fin 36) : Nat.land (edgeRank e) 63 = e.1.val := by
  change edgeRank e &&& (2 ^ 6 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := e.1.isLt
  dsimp [edgeRank]
  omega

theorem edgeRank_high (e : Fin 36 × Fin 36) : Nat.shiftRight (edgeRank e) 6 = e.2.val := by
  change edgeRank e >>> 6 = _
  rw [Nat.shiftRight_eq_div_pow]
  have := e.1.isLt
  dsimp [edgeRank]
  omega

theorem decM_LANE0_mul_low {y : ℕ} (hy : y < 36) :
    decM (Nat.mul LANE0 (Nat.shiftLeft 1 y - 1)) =
      univ.filter (fun e : Fin 36 × Fin 36 => e.2.val < y) := by
  change decM (LANE0 * ((1 <<< y) - 1)) = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.mul_comm, decM_cover_cols (by
    have hp : 2 ^ y ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    have hpos : 0 < 2 ^ y := Nat.pow_pos (by decide)
    omega)]
  ext e
  simp only [mem_product, mem_univ, mem_decV, ← mem_bits, bits_two_pow_sub_one,
    mem_range, true_and, mem_filter]

theorem bits_LANE0_before {x : ℕ} (hx : x ≤ 36) :
    bits (Nat.land LANE0 (Nat.shiftLeft 1 (64 * x) - 1)) = (range x).image (64 * ·) := by
  change bits (Nat.land LANE0 ((1 <<< (64 * x)) - 1)) = _
  rw [bits_land, Nat.shiftLeft_eq, one_mul, bits_two_pow_sub_one, bits_LANE0]
  ext p
  simp only [mem_inter, mem_image, mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hp⟩
    exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by omega, rfl⟩, by omega⟩

theorem decM_partial_column {x y : ℕ} (hx : x ≤ 36) (hy : y < 36) :
    decM (Nat.shiftLeft (Nat.land LANE0 (Nat.shiftLeft 1 (64 * x) - 1)) y) =
      univ.filter (fun e : Fin 36 × Fin 36 => e.1.val < x ∧ e.2.val = y) := by
  ext e
  simp only [mem_decM, ← mem_bits, bits_shiftLeft, bits_LANE0_before hx,
    mem_filter, mem_univ, true_and, mem_image, mem_range]
  constructor
  · rintro ⟨p, ⟨i, hi, rfl⟩, hp⟩
    have he := e.2.isLt
    constructor <;> omega
  · rintro ⟨hi, he⟩
    exact ⟨64 * e.1.val, ⟨e.1.val, hi, rfl⟩, by omega⟩

theorem decM_before_rank (G : Consts) (e : Fin 36 × Fin 36) :
    decM (beforeM G (edgeRank e)) =
      (decM G.EM).filter (fun q => edgeRank q < edgeRank e) := by
  unfold beforeM
  rw [edgeRank_low, edgeRank_high]
  dsimp only
  change decM (Nat.land G.EM (Nat.lor (Nat.mul LANE0 (Nat.shiftLeft 1 e.2.val - 1))
    (Nat.shiftLeft (Nat.land LANE0 (Nat.shiftLeft 1 (64 * e.1.val) - 1)) e.2.val))) = _
  rw [decM_land, decM_lor, decM_LANE0_mul_low e.2.isLt,
    decM_partial_column (Nat.le_of_lt e.1.isLt) e.2.isLt]
  ext q
  change q ∈ (decM G.EM ∩ ((univ.filter fun q : Fin 36 × Fin 36 => q.2.val < e.2.val) ∪
    (univ.filter fun q : Fin 36 × Fin 36 => q.1.val < e.1.val ∧ q.2.val = e.2.val))) ↔
    q ∈ (decM G.EM).filter (fun q => edgeRank q < edgeRank e)
  simp only [mem_inter, mem_union, mem_filter, mem_univ, true_and]
  change (q ∈ decM G.EM ∧ (q.2.val < e.2.val ∨ q.1.val < e.1.val ∧ q.2.val = e.2.val)) ↔
    q ∈ decM G.EM ∧ 64 * q.2.val + q.1.val < 64 * e.2.val + e.1.val
  have hq := q.1.isLt
  have he := e.1.isLt
  constructor
  · rintro ⟨hmem, hlt⟩
    exact ⟨hmem, by omega⟩
  · rintro ⟨hmem, hlt⟩
    exact ⟨hmem, by omega⟩

theorem before_coherent {G : Consts} (hG : G.Coherent) (e : Fin 36 × Fin 36) :
    decM (beforeM G (edgeRank e)) = decT (beforeT G (edgeRank e)) := by
  rw [decM_before_rank, decT_before, hG]
  rfl

theorem decM_single (e : Fin 36 × Fin 36) :
    decM (Nat.shiftLeft 1 (64 * e.1.val + e.2.val)) = {e} := by
  have he := decM_insert 0 e
  change decM (0 ||| (1 <<< (64 * e.1.val + e.2.val))) = insert e (decM 0) at he
  rw [Nat.zero_or, decM_zero] at he
  exact he

/-- Equality of the decoded masks is preserved by every Boolean mask operation. -/
def SameMask (m t : ℕ) : Prop := decM m = decT t

theorem SameMask.lor {m t m' t' : ℕ} (h : SameMask m t) (h' : SameMask m' t') :
    SameMask (Nat.lor m m') (Nat.lor t t') := by
  change decM _ = decT _
  rw [decM_lor, decT_lor, h, h']

theorem SameMask.land {m t m' t' : ℕ} (h : SameMask m t) (h' : SameMask m' t') :
    SameMask (Nat.land m m') (Nat.land t t') := by
  change decM _ = decT _
  rw [decM_land, decT_land, h, h']

theorem SameMask.xor {m t m' t' : ℕ} (h : SameMask m t) (h' : SameMask m' t') :
    SameMask (Nat.xor m m') (Nat.xor t t') := by
  ext e
  have hp : e ∈ decM m ↔ e ∈ decT t := by rw [h]
  have hp' : e ∈ decM m' ↔ e ∈ decT t' := by rw [h']
  simp only [mem_decM, mem_decT, bit_eq_testBit] at hp hp' ⊢
  change (m ^^^ m').testBit (64 * e.1.val + e.2.val) = true ↔
    (t ^^^ t').testBit (64 * e.2.val + e.1.val) = true
  rw [Nat.testBit_xor, Nat.testBit_xor, Bool.eq_iff_iff.mpr hp, Bool.eq_iff_iff.mpr hp']

theorem single_coherent (e : Fin 36 × Fin 36) :
    SameMask (Nat.shiftLeft 1 (64 * e.1.val + e.2.val)) (Nat.shiftLeft 1 (edgeRank e)) := by
  change decM _ = decT _
  rw [decM_single, decT_single]

theorem row_coherent {G : Consts} (hG : G.Coherent) {x : ℕ} (hx : x < 36) :
    SameMask (rowM G x) (rowT G x) := by
  change decM _ = decT _
  rw [decM_row, decT_row G hx, hG]

theorem col_coherent {G : Consts} (hG : G.Coherent) {y : ℕ} (hy : y < 36) :
    SameMask (colM G y) (colT G y) := by
  change decM _ = decT _
  rw [decM_col G hy, decT_col, hG]

def classBPM (e f g : Fin 36 × Fin 36) : ℕ :=
  Nat.lor (Nat.shiftLeft 1 (64 * e.1.val + e.2.val))
    (Nat.lor (Nat.shiftLeft 1 (64 * f.1.val + f.2.val))
      (Nat.shiftLeft 1 (64 * g.1.val + g.2.val)))

def disjointM (G : Consts) (e : Fin 36 × Fin 36) : ℕ :=
  Nat.xor G.EM (Nat.lor (rowM G e.1.val) (colM G e.2.val))

def classBAM (G : Consts) (e f g : Fin 36 × Fin 36) : ℕ :=
  Nat.lor (disjointM G e) (Nat.lor (beforeM G (edgeRank e))
    (Nat.lor (Nat.land (rowM G e.1.val) (beforeM G (edgeRank f)))
      (Nat.land (colM G e.2.val) (beforeM G (edgeRank g)))))

theorem classBP_coherent (e f g : Fin 36 × Fin 36) :
    SameMask (classBPM e f g) (classBP e f g) :=
  (single_coherent e).lor ((single_coherent f).lor (single_coherent g))

theorem disjoint_coherent {G : Consts} (hG : G.Coherent) (e : Fin 36 × Fin 36) :
    SameMask (disjointM G e) (disjointT G e) :=
  SameMask.xor hG ((row_coherent hG e.1.isLt).lor (col_coherent hG e.2.isLt))

theorem classBA_coherent {G : Consts} (hG : G.Coherent) (e f g : Fin 36 × Fin 36) :
    SameMask (classBAM G e f g) (classBA G e f g) :=
  (disjoint_coherent hG e).lor (SameMask.lor (before_coherent hG e)
    (((row_coherent hG e.1.isLt).land (before_coherent hG f)).lor
      ((col_coherent hG e.2.isLt).land (before_coherent hG g))))

end Sarkozy.F3Kernel
