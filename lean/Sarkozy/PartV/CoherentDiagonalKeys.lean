module

public import Sarkozy.PartV.CoherentDiagonalData

/-!
# Supports as membership vectors

A support is determined by its membership vector over the twelve vertices (`vec_inj`), and
the vector of a symmetric difference is the pointwise exclusive or (`vec_symmDiff`). The
diagonal coefficients and multiplicities, which compare symmetric differences of dictionary
supports, are rewritten as sums over these vectors (`coefExpr_eq`, `multExpr_eq`), so that the
generated diagonal checks compare short Boolean lists instead of finsets.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset
open scoped symmDiff

/-- The twelve vertices. -/
def allVertices : List Vertex :=
  (List.finRange 6).flatMap fun i => (List.finRange 2).map fun j => ((i.val : ZMod 6), j)

theorem mem_allVertices : ∀ v : Vertex, v ∈ allVertices := by
  decide +kernel

/-- The membership vector of a support. -/
def vec (s : Support) : List Bool := allVertices.map fun v => decide (v ∈ s)

theorem vec_inj {s t : Support} : vec s = vec t ↔ s = t := by
  constructor
  · intro h
    ext v
    have := (List.map_inj_left.mp h) v (mem_allVertices v)
    simpa using this
  · rintro rfl
    rfl

/-- Pointwise exclusive or of two Boolean lists. -/
def xorV (a b : List Bool) : List Bool := List.zipWith (fun x y => x != y) a b

theorem zipWith_map_self {α β : Type*} (l : List α) (f g : α → β) (h : β → β → β) :
    List.zipWith h (l.map f) (l.map g) = l.map fun v => h (f v) (g v) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem vec_symmDiff (s t : Support) : vec (s ∆ t) = xorV (vec s) (vec t) := by
  unfold vec xorV
  rw [zipWith_map_self]
  apply List.map_congr_left
  intro v _
  by_cases hs : v ∈ s <;> by_cases ht : v ∈ t <;> simp [Finset.mem_symmDiff, hs, ht]

theorem symmDiff_eq_iff (s t S : Support) : s ∆ t = S ↔ xorV (vec s) (vec t) = vec S := by
  rw [← vec_symmDiff, vec_inj]

/-! ### Supports as numbers -/

/-- The number with binary digits `l`, least significant first. -/
def ofBitsR (l : List Bool) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun b _ ih => Nat.bit b ih) l

theorem ofBitsR_xorV (l l' : List Bool) (h : l.length = l'.length) :
    ofBitsR (xorV l l') = Nat.xor (ofBitsR l) (ofBitsR l') := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons b l' => simp at h
  | cons a l ih =>
    cases l' with
    | nil => simp at h
    | cons b l' =>
      simp only [List.length_cons, add_left_inj] at h
      change Nat.bit (a != b) (ofBitsR (xorV l l')) =
        Nat.bit a (ofBitsR l) ^^^ Nat.bit b (ofBitsR l')
      rw [Nat.xor_bit, ih l' h]
      rfl

theorem ofBitsR_inj (l l' : List Bool) (h : l.length = l'.length)
    (he : ofBitsR l = ofBitsR l') : l = l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons b l' => simp at h
  | cons a l ih =>
    cases l' with
    | nil => simp at h
    | cons b l' =>
      simp only [List.length_cons, add_left_inj] at h
      change Nat.bit a (ofBitsR l) = Nat.bit b (ofBitsR l') at he
      have h1 := congrArg (· / 2) he
      have h2 := congrArg (· % 2) he
      simp only [Nat.bit_div_two, Nat.bit_mod_two] at h1 h2
      have hab : a = b := by cases a <;> cases b <;> simp_all
      rw [hab, ih l' h h1]

theorem length_vec (s : Support) : (vec s).length = allVertices.length := by
  simp [vec]

/-- The number of a support: its membership vector in binary. -/
def code (s : Support) : ℕ := ofBitsR (vec s)

theorem code_symmDiff (s t : Support) : code (s ∆ t) = Nat.xor (code s) (code t) := by
  unfold code
  rw [vec_symmDiff, ofBitsR_xorV _ _ ((length_vec s).trans (length_vec t).symm)]

theorem code_inj {s t : Support} : code s = code t ↔ s = t := by
  constructor
  · intro h
    exact vec_inj.mp (ofBitsR_inj _ _ ((length_vec s).trans (length_vec t).symm) h)
  · rintro rfl
    rfl

/-! ### Signs of the dictionary coefficients -/

/-- The sign of a dictionary coefficient. -/
def sgnQ (q : ℚ) : ℤ := if 0 < q then 1 else -1

theorem dictionary39_sgn : ∀ sc ∈ dictionary39, sc.2 = (sgnQ sc.2 : ℚ) / 15 := by
  decide +kernel

/-- The codes and signs of the dictionary entries. -/
def dictKeys : List (ℕ × ℤ) := dictionary39.map fun sc => (code sc.1, sgnQ sc.2)

/-- The products of all ordered pairs of dictionary keys. -/
def pairKeys : List (ℕ × ℤ) :=
  dictKeys.flatMap fun k => dictKeys.map fun l => (Nat.xor k.1 l.1, k.2 * l.2)

/-- The signed number of ordered pairs with symmetric difference of code `c`. -/
def pairSum (c : ℕ) : ℤ := (pairKeys.map fun p => if p.1 = c then p.2 else 0).sum

theorem sum_flatMap_map' {α β M : Type*} [AddCommMonoid M]
    (A : List α) (B : α → List β) (f : β → M) :
    ((A.flatMap B).map f).sum = (A.map fun a => ((B a).map f).sum).sum := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [List.flatMap_cons, ih]

/-- The body of `diagonalCoefficient`. -/
def coefExpr (S : Support) : ℚ :=
  (dictionary39.map fun sc => (dictionary39.map fun tc =>
    if sc.1 ∆ tc.1 = S then sc.2 * tc.2 else 0).sum).sum

theorem coefExpr_eq (S : Support) : coefExpr S = (pairSum (code S) : ℚ) / 225 := by
  have hterm : ∀ sc ∈ dictionary39, ∀ tc ∈ dictionary39,
      (if sc.1 ∆ tc.1 = S then sc.2 * tc.2 else 0) =
        ((if Nat.xor (code sc.1) (code tc.1) = code S then sgnQ sc.2 * sgnQ tc.2 else 0 : ℤ)
          : ℚ) *
          (1 / 225) := by
    intro sc hs tc ht
    by_cases h : Nat.xor (code sc.1) (code tc.1) = code S
    · have h' : sc.1 ∆ tc.1 = S := code_inj.mp ((code_symmDiff _ _).trans h)
      simp only [h', h, ite_true]
      conv_lhs => rw [dictionary39_sgn sc hs, dictionary39_sgn tc ht]
      push_cast
      ring
    · have h' : ¬sc.1 ∆ tc.1 = S := fun h' => h ((code_symmDiff _ _).symm.trans (h' ▸ rfl))
      rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false h)]
      simp
  unfold coefExpr
  rw [List.map_congr_left (fun sc hs => congrArg List.sum
    (List.map_congr_left (fun tc ht => hterm sc hs tc ht)))]
  unfold pairSum pairKeys dictKeys
  simp only [List.flatMap_map, List.map_map, Function.comp_def,
    Int.cast_list_sum, List.sum_map_mul_right, div_eq_mul_inv, one_mul]
  rw [sum_flatMap_map']
  simp only [List.map_map, Function.comp_def]

/-- The body of `diagonalMultiplicity`, for a list of blocks. -/
def multExpr (B : List Dictionary) (S : Support) : ℚ :=
  (B.map fun D => (D.map fun sc => if sc.1 = S then 1 else 0).sum).sum

/-- The codes of the supports of a list of blocks. -/
def blockCodesOf (B : List Dictionary) : List ℕ :=
  B.flatMap fun D => D.map fun sc => code sc.1

/-- The number of entries of `l` equal to `c`. -/
def countCode (l : List ℕ) (c : ℕ) : ℕ :=
  (l.map fun w => if w = c then 1 else 0).sum

theorem multExpr_eq (B : List Dictionary) (S : Support) :
    multExpr B S = (countCode (blockCodesOf B) (code S) : ℚ) := by
  unfold multExpr countCode blockCodesOf
  rw [sum_flatMap_map', Nat.cast_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro D _
  simp only [Function.comp_apply, Nat.cast_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc _
  simp only [Function.comp_apply, code_inj]
  split_ifs <;> simp

end Sarkozy.PartV.CoherentDictionary
