module

public import Sarkozy.SpectralD.ClassOneModels

/-!
# Common neighbourhoods and coverable counts as computations on codes

The class-one tables count subsets of a common cross neighbourhood. Through an injective code
`e : U → ℕ`, the finset quantities `(N k ∩ N l).card` and `coverCount N Adj k l` become
computations on lists of codes (`card_inter_eq_commonR`, `coverCount_eq_coverMaskCount`).

The functions that the kernel evaluates are written with `List.rec` directly, and the coverable
count enumerates subsets as bit masks with `Nat.lor` and `Nat.pow` only. These operations, and
`Nat.beq`, `Nat.mod` and `Nat.shiftRight` in the tabulation checks, are among the natural-number
operations that the Lean kernel and the independent checkers evaluate on numerals (`Nat.land` is
avoided, since not every checker evaluates it on numerals). No evaluation happens in this file.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Finset

/-! ### The evaluated functions -/

/-- The code list of `x` in a table of code lists (`[]` past the end). -/
def codeTable (T : List (List ℕ)) (x : ℕ) : List ℕ := T.getD x []

/-- The entry `x` of a table of numbers (`0` past the end). -/
def maskTable (T : List ℕ) (x : ℕ) : ℕ := T.getD x 0

/-- Membership of `x` in a list of numbers. -/
def memR (x : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Nat.beq a x || ih) l

/-- The entries of `l₁` that occur in `l₂`. -/
def commonR (l₁ l₂ : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun a _ ih => cond (memR a l₂) (a :: ih) ih) l₁

/-- The number of sublists `J` of `S` for which the mask `m ||| ⋁_{x ∈ J} 2^x` is nonzero and
its bits lie in `U ||| ⋁_{x ∈ J} A x` (`coverMaskCount_eq_card`). At `m = U = 0`, with `A x` the
mask of the codes that `x` covers, it counts the nonempty subsets in which every code is
covered by another one. -/
def coverMaskCount (A : ℕ → ℕ) (S : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun m U => cond (!(Nat.beq m 0) && Nat.beq (Nat.lor m U) U) 1 0)
    (fun x _ ih => fun m U => Nat.add (ih m U) (ih (Nat.lor m (Nat.pow 2 x)) (Nat.lor U (A x))))
    S

/-! ### Basic facts -/

theorem memR_iff (x : ℕ) (l : List ℕ) : memR x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memR]
  | cons a l ih =>
    change (Nat.beq a x || memR x l) = true ↔ _
    rw [Bool.or_eq_true, ih, Nat.beq_eq, List.mem_cons, eq_comm]

theorem commonR_eq_filter (l₁ l₂ : List ℕ) :
    commonR l₁ l₂ = l₁.filter (fun z => memR z l₂) := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    change cond (memR a l₂) (a :: commonR l l₂) (commonR l l₂) = _
    rw [List.filter_cons, ih]
    cases memR a l₂ <;> rfl

theorem mem_commonR (x : ℕ) (l₁ l₂ : List ℕ) :
    x ∈ commonR l₁ l₂ ↔ x ∈ l₁ ∧ x ∈ l₂ := by
  rw [commonR_eq_filter, List.mem_filter, memR_iff]

theorem nodup_commonR {l₁ : List ℕ} (h : l₁.Nodup) (l₂ : List ℕ) :
    (commonR l₁ l₂).Nodup := by
  rw [commonR_eq_filter]
  exact h.filter _

theorem lor_eq_right_iff (m U : ℕ) :
    Nat.lor m U = U ↔ ∀ y, m.testBit y = true → U.testBit y = true := by
  constructor
  · intro h y hy
    rw [← h]
    change (m ||| U).testBit y = true
    rw [Nat.testBit_or, hy, Bool.true_or]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro y
    change (m ||| U).testBit y = U.testBit y
    rw [Nat.testBit_or]
    cases hm : m.testBit y
    · rfl
    · rw [h y hm, Bool.true_or]

theorem testBit_iff_shiftRight_mod (m y : ℕ) : m.testBit y = true ↔ (m >>> y) % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_iff]

/-! ### The mask count as a count of sub-multisets -/

/-- The condition counted by `coverMaskCount`, for the multiset `J` of chosen codes. -/
def maskLeaf (A : ℕ → ℕ) (m U : ℕ) (J : Multiset ℕ) : Prop :=
  (m ≠ 0 ∨ J ≠ 0) ∧ ∀ y, (m.testBit y = true ∨ y ∈ J) →
    (U.testBit y = true ∨ ∃ x ∈ J, (A x).testBit y = true)

theorem maskLeaf_cons (A : ℕ → ℕ) (m U a : ℕ) (J : Multiset ℕ) :
    maskLeaf A m U (a ::ₘ J) ↔ maskLeaf A (Nat.lor m (Nat.pow 2 a)) (Nat.lor U (A a)) J := by
  have hm : Nat.lor m (Nat.pow 2 a) ≠ 0 := by
    intro h
    have h2 := congrArg (fun n => n.testBit a) h
    change (m ||| 2 ^ a).testBit a = (0 : ℕ).testBit a at h2
    rw [Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true, Nat.zero_testBit] at h2
    exact Bool.noConfusion h2
  have hbm : ∀ y, (Nat.lor m (Nat.pow 2 a)).testBit y = (m.testBit y || decide (a = y)) := by
    intro y
    change (m ||| 2 ^ a).testBit y = _
    rw [Nat.testBit_or, Nat.testBit_two_pow]
  have hbU : ∀ y, (Nat.lor U (A a)).testBit y = (U.testBit y || (A a).testBit y) := by
    intro y
    change (U ||| A a).testBit y = _
    rw [Nat.testBit_or]
  unfold maskLeaf
  simp only [hbm, hbU, Bool.or_eq_true, decide_eq_true_eq, Multiset.mem_cons, ne_eq,
    Multiset.cons_ne_zero, not_false_eq_true, or_true, true_and, hm, true_or]
  constructor
  · intro h y hy
    rcases h y (by tauto) with h1 | ⟨x, hx, h2⟩
    · exact Or.inl (Or.inl h1)
    · rcases hx with rfl | hx
      · exact Or.inl (Or.inr h2)
      · exact Or.inr ⟨x, hx, h2⟩
  · intro h y hy
    rcases h y (by tauto) with (h1 | h1) | ⟨x, hx, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨a, Or.inl rfl, h1⟩
    · exact Or.inr ⟨x, Or.inr hx, h2⟩

theorem coverMaskCount_eq_card (A : ℕ → ℕ) (S : List ℕ) (m U : ℕ)
    [DecidablePred (maskLeaf A m U)] :
    coverMaskCount A S m U =
      Multiset.card ((Multiset.powerset (S : Multiset ℕ)).filter (maskLeaf A m U)) := by
  classical
  induction S generalizing m U with
  | nil =>
    change cond (!(Nat.beq m 0) && Nat.beq (Nat.lor m U) U) 1 0 = _
    rw [Multiset.coe_nil, Multiset.powerset_zero, Multiset.filter_singleton]
    have h : maskLeaf A m U 0 ↔ (!(Nat.beq m 0) && Nat.beq (Nat.lor m U) U) = true := by
      rw [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, lor_eq_right_iff]
      simp only [maskLeaf, ne_eq, not_true_eq_false, or_false, Multiset.notMem_zero, false_and,
        exists_false]
      rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
    split_ifs with h0
    · rw [h.mp h0]
      rfl
    · have h1 : (!(Nat.beq m 0) && Nat.beq (Nat.lor m U) U) = false :=
        Bool.eq_false_iff.mpr (fun h1 => h0 (h.mpr h1))
      rw [h1]
      rfl
  | cons a S ih =>
    change Nat.add (coverMaskCount A S m U)
      (coverMaskCount A S (Nat.lor m (Nat.pow 2 a)) (Nat.lor U (A a))) = _
    rw [ih, ih, ← Multiset.cons_coe, Multiset.powerset_cons, Multiset.filter_add,
      Multiset.card_add, Multiset.filter_map, Multiset.card_map]
    congr 2
    apply Multiset.filter_congr
    intro J _
    exact (maskLeaf_cons A m U a J).symm

/-! ### Transfer from finsets to codes -/

theorem multiset_powerset_map {α β : Type*} (f : α → β) (s : Multiset α) :
    (s.map f).powerset = s.powerset.map (Multiset.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.powerset_cons, ih, Multiset.map_map]

theorem card_filter_powerset_val {U : Type*} (s : Finset U) (Q : Multiset U → Prop)
    [DecidablePred Q] :
    (s.powerset.filter (fun J => Q J.val)).card = Multiset.card (s.val.powerset.filter Q) := by
  calc (s.powerset.filter (fun J => Q J.val)).card
      = Multiset.card ((s.powerset.val.filter (fun J => Q J.val)).map Finset.val) := by
        rw [Multiset.card_map]; rfl
    _ = Multiset.card ((s.powerset.val.map Finset.val).filter Q) := by
        rw [Multiset.filter_map]; rfl
    _ = Multiset.card (s.val.powerset.filter Q) := by
        congr 2
        simp [Finset.powerset, Multiset.map_pmap, Multiset.pmap_eq_map]

variable {U : Type*} [DecidableEq U] (e : U → ℕ) (N : U → Finset U) (L : ℕ → List ℕ)

theorem map_inter_eq_commonR (he : Function.Injective e)
    (hN : ∀ k j, j ∈ N k ↔ e j ∈ L (e k)) (hcod : ∀ k, ∀ x ∈ L (e k), ∃ j, e j = x)
    (hnd : ∀ k, (L (e k)).Nodup) (k l : U) :
    (N k ∩ N l).val.map e = (commonR (L (e k)) (L (e l)) : Multiset ℕ) := by
  rw [Multiset.Nodup.ext ((N k ∩ N l).nodup.map he)
    (Multiset.coe_nodup.mpr (nodup_commonR (hnd k) _))]
  intro x
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_inter, hN, Multiset.mem_coe,
    mem_commonR]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨j, rfl⟩ := hcod k x h1
    exact ⟨j, ⟨h1, h2⟩, rfl⟩

theorem card_inter_eq_commonR (he : Function.Injective e)
    (hN : ∀ k j, j ∈ N k ↔ e j ∈ L (e k)) (hcod : ∀ k, ∀ x ∈ L (e k), ∃ j, e j = x)
    (hnd : ∀ k, (L (e k)).Nodup) (k l : U) :
    (N k ∩ N l).card = (commonR (L (e k)) (L (e l))).length := by
  rw [Finset.card_def, ← Multiset.card_map e, map_inter_eq_commonR e N L he hN hcod hnd,
    Multiset.coe_card]

theorem coverCount_eq_coverMaskCount [Fintype U] (he : Function.Injective e)
    (hN : ∀ k j, j ∈ N k ↔ e j ∈ L (e k)) (hcod : ∀ k, ∀ x ∈ L (e k), ∃ j, e j = x)
    (hnd : ∀ k, (L (e k)).Nodup) (Adj : U → U → Prop) [DecidableRel Adj] (A : ℕ → ℕ)
    (hA : ∀ i j, (i ≠ j ∧ Adj i j) ↔ (A (e i) >>> e j) % 2 = 1) (k l : U) :
    coverCount N Adj k l = coverMaskCount A (commonR (L (e k)) (L (e l))) 0 0 := by
  classical
  have hA' : ∀ i j, (i ≠ j ∧ Adj i j) ↔ (A (e i)).testBit (e j) = true := fun i j => by
    rw [hA, testBit_iff_shiftRight_mod]
  have hQ : ∀ J : Finset U,
      (2 ≤ J.card ∧ PaleyB.Coverable Adj J) ↔ maskLeaf A 0 0 (J.val.map e) := by
    intro J
    simp only [maskLeaf, ne_eq, Nat.zero_testBit, Bool.false_eq_true, not_true_eq_false,
      false_or, Multiset.map_eq_zero, Finset.val_eq_zero, Multiset.mem_map, Finset.mem_val]
    constructor
    · rintro ⟨h2, hc⟩
      refine ⟨?_, ?_⟩
      · rintro rfl
        simp at h2
      · rintro _ ⟨j, hj, rfl⟩
        obtain ⟨i, hi, hij, ha⟩ := hc j hj
        exact ⟨e i, ⟨i, hi, rfl⟩, (hA' i j).mp ⟨hij, ha⟩⟩
    · rintro ⟨hne, hc⟩
      have hcov : PaleyB.Coverable Adj J := by
        intro j hj
        obtain ⟨_, ⟨i, hi, rfl⟩, hb⟩ := hc (e j) ⟨j, hj, rfl⟩
        obtain ⟨hij, ha⟩ := (hA' i j).mpr hb
        exact ⟨i, hi, hij, ha⟩
      refine ⟨?_, hcov⟩
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨i, hi, hij, _⟩ := hcov j hj
      exact Finset.one_lt_card.mpr ⟨i, hi, j, hj, hij⟩
  unfold coverCount
  rw [Finset.filter_congr (fun J _ => hQ J),
    card_filter_powerset_val _ (fun m => maskLeaf A 0 0 (m.map e)),
    show Multiset.filter (fun m => maskLeaf A 0 0 (Multiset.map e m)) (N k ∩ N l).val.powerset
      = Multiset.filter (maskLeaf A 0 0 ∘ Multiset.map e) (N k ∩ N l).val.powerset from rfl,
    ← Multiset.card_map (Multiset.map e), ← Multiset.filter_map, ← multiset_powerset_map,
    map_inter_eq_commonR e N L he hN hcod hnd, coverMaskCount_eq_card]

end Sarkozy.SpectralD.Root
