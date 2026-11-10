module

public import Sarkozy.PositiveRoots.CoherentOffdiagPair

/-!
# The off-diagonal cost masses as sums over explicit keys

`coreCostMass` and `privateCostMass` compare support intersections for each of the 1,521
ordered pairs of dictionary entries. Each comparison only needs, for each support, the class
of each of six derived sets among their values over the dictionary (`clsOf`), and for the two
private intersections whether they are empty or singletons (`GoodPair` reduces to this,
`goodPair_iff`). These keys are evaluated once per entry (`offKeys_eq`); the masses are then
sums over pairs of keys (`core_cost_keys`, `private_cost_keys`).
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV.CoherentDictionary

theorem goodPair_iff {α : Type*} [DecidableEq α] (A B : Finset α) :
    GoodPair A B ↔ A.Nonempty ∧ B.Nonempty ∧ ¬(A = B ∧ A.card = 1) := by
  unfold GoodPair
  constructor
  · rintro ⟨hA, hB, h2⟩
    refine ⟨hA, hB, ?_⟩
    rintro ⟨rfl, h1⟩
    rw [Finset.union_self] at h2
    omega
  · rintro ⟨hA, hB, h⟩
    refine ⟨hA, hB, ?_⟩
    by_contra hlt
    have hle : (A ∪ B).card ≤ 1 := by omega
    have : Nonempty α := ⟨hA.choose⟩
    obtain ⟨v, hv⟩ := Finset.card_le_one_iff_subset_singleton.mp hle
    have hAv : A = {v} :=
      (Finset.Nonempty.subset_singleton_iff hA).mp ((Finset.subset_union_left).trans hv)
    have hBv : B = {v} :=
      (Finset.Nonempty.subset_singleton_iff hB).mp ((Finset.subset_union_right).trans hv)
    exact h ⟨hAv.trans hBv.symm, by rw [hAv, Finset.card_singleton]⟩

/-- The class of `X s` among the values of `X` over the dictionary. -/
def clsOf {β : Type*} [DecidableEq β] (X : Support → β) (s : Support) : ℕ :=
  (dictionary39.map fun sc => X sc.1).idxOf (X s)

theorem clsOf_eq_iff {β : Type*} [DecidableEq β] (X : Support → β) {sc tc : Support × ℚ}
    (hs : sc ∈ dictionary39) : clsOf X sc.1 = clsOf X tc.1 ↔ X sc.1 = X tc.1 :=
  List.idxOf_inj (List.mem_map.mpr ⟨sc, hs, rfl⟩)

/-- `1` if `p` holds, else `0`. -/
def bit (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

theorem bit_eq_one (p : Prop) [Decidable p] : bit p = 1 ↔ p := by
  unfold bit
  split_ifs with h <;> simp [h]

/-- The private intersection on side `b`. -/
def privCut (b : Bool) (s : Support) : Support :=
  if b then s ∩ privateCore else s ∩ privateCore.image reflect

/-- The key of a dictionary entry: classes, emptiness and singleton bits of the private
intersections, and classes of the core and private chamber supports. -/
def offKey (sc : Support × ℚ) : List ℕ :=
  [clsOf (privCut true) sc.1, bit (privCut true sc.1).Nonempty,
    bit ((privCut true sc.1).card = 1),
    clsOf (privCut false) sc.1, bit (privCut false sc.1).Nonempty,
    bit ((privCut false sc.1).card = 1),
    clsOf (coreSupport true) sc.1, clsOf (coreSupport false) sc.1,
    clsOf (privateSupport true) sc.1, clsOf (privateSupport false) sc.1]

/-- The private case of a pair of keys (`ChamberPrivate`). -/
def privK (k l : List ℕ) : Bool :=
  (k.getD 1 0 == 1 && l.getD 1 0 == 1 && !(k.getD 0 0 == l.getD 0 0 && k.getD 2 0 == 1)) &&
    (k.getD 4 0 == 1 && l.getD 4 0 == 1 && !(k.getD 3 0 == l.getD 3 0 && k.getD 5 0 == 1))

/-- The core cost of a pair of keys outside the private case. -/
def coreK (k l : List ℕ) : ℕ :=
  if privK k l then 0 else
    16 * (if k.getD 6 0 = l.getD 6 0 then 2 else 1) * (if k.getD 7 0 = l.getD 7 0 then 2 else 1)

/-- The private cost of a pair of keys in the private case. -/
def privCostK (k l : List ℕ) : ℕ :=
  if privK k l then
    (if k.getD 8 0 = l.getD 8 0 then 2 else 1) * (if k.getD 9 0 = l.getD 9 0 then 2 else 1)
  else 0

theorem prop_shape (a b c d e f g h : Prop) :
    ((a ∧ b ∧ ¬(c ∧ d)) ∧ e ∧ f ∧ ¬(g ∧ h)) ↔
      ((a ∧ b) ∧ (¬c ∨ ¬d)) ∧ (e ∧ f) ∧ (¬g ∨ ¬h) := by
  tauto

theorem covarianceCase_fst_keys {sc tc : Support × ℚ} (hs : sc ∈ dictionary39) :
    (covarianceCase sc.1 tc.1).1 = privK (offKey sc) (offKey tc) := by
  have hc : (covarianceCase sc.1 tc.1).1 = decide (ChamberPrivate sc.1 tc.1) := by
    unfold covarianceCase
    split_ifs with h <;> simp [h]
  rw [hc, Bool.eq_iff_iff, decide_eq_true_iff]
  have h1 := clsOf_eq_iff (privCut true) (tc := tc) hs
  have h2 := clsOf_eq_iff (privCut false) (tc := tc) hs
  simp only [privCut, ite_true, Bool.false_eq_true, ite_false] at h1 h2
  simp only [ChamberPrivate, goodPair_iff, privK, offKey, privCut, ite_true,
    Bool.false_eq_true, ite_false, List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', Bool.and_eq_false_iff]
  simp only [beq_eq_false_iff_ne, ne_eq, h1, h2, bit_eq_one]
  exact prop_shape _ _ _ _ _ _ _ _

theorem corePairCost_keys {sc tc : Support × ℚ} (hs : sc ∈ dictionary39) :
    corePairCost sc.1 tc.1 = 16 * (if (offKey sc).getD 6 0 = (offKey tc).getD 6 0 then 2 else 1) *
      (if (offKey sc).getD 7 0 = (offKey tc).getD 7 0 then 2 else 1) := by
  simp only [corePairCost, offKey, List.getD_cons_zero, List.getD_cons_succ,
    clsOf_eq_iff (coreSupport true) (tc := tc) hs, clsOf_eq_iff (coreSupport false) (tc := tc) hs]

theorem privatePairCost_keys {sc tc : Support × ℚ} (hs : sc ∈ dictionary39) :
    privatePairCost sc.1 tc.1 = (if (offKey sc).getD 8 0 = (offKey tc).getD 8 0 then 2 else 1) *
      (if (offKey sc).getD 9 0 = (offKey tc).getD 9 0 then 2 else 1) := by
  simp only [privatePairCost, offKey, List.getD_cons_zero, List.getD_cons_succ,
    clsOf_eq_iff (privateSupport true) (tc := tc) hs,
    clsOf_eq_iff (privateSupport false) (tc := tc) hs]

theorem dictionary39_abs : ∀ sc ∈ dictionary39, |sc.2| = 1 / 15 := by
  decide +kernel

theorem abs_mul_dictionary {sc tc : Support × ℚ} (hs : sc ∈ dictionary39)
    (ht : tc ∈ dictionary39) : |sc.2 * tc.2| = 1 / 225 := by
  rw [abs_mul, dictionary39_abs sc hs, dictionary39_abs tc ht]
  norm_num

/-- The body of `coreCostMass`. -/
def coreMassK (st : (Support × ℚ) × (Support × ℚ)) : ℚ :=
  if (covarianceCase st.1.1 st.2.1).1 then 0
  else |st.1.2 * st.2.2| * (corePairCost st.1.1 st.2.1 : ℚ)

/-- The body of `privateCostMass`. -/
def privateMassK (st : (Support × ℚ) × (Support × ℚ)) : ℚ :=
  if (covarianceCase st.1.1 st.2.1).1 then
    |st.1.2 * st.2.2| * (privatePairCost st.1.1 st.2.1 : ℚ)
  else 0

theorem coreCostMass_keys {sc tc : Support × ℚ} (hs : sc ∈ dictionary39)
    (ht : tc ∈ dictionary39) :
    coreMassK (sc, tc) = (coreK (offKey sc) (offKey tc) : ℚ) / 225 := by
  unfold coreMassK coreK
  dsimp only
  rw [covarianceCase_fst_keys hs]
  by_cases h : privK (offKey sc) (offKey tc) = true
  · simp only [h, ite_true, Nat.cast_zero, zero_div]
  · simp only [h, Bool.false_eq_true, ite_false]
    rw [abs_mul_dictionary hs ht, corePairCost_keys hs]
    push_cast
    ring

theorem privateCostMass_keys {sc tc : Support × ℚ} (hs : sc ∈ dictionary39)
    (ht : tc ∈ dictionary39) :
    privateMassK (sc, tc) = (privCostK (offKey sc) (offKey tc) : ℚ) / 225 := by
  unfold privateMassK privCostK
  dsimp only
  rw [covarianceCase_fst_keys hs]
  by_cases h : privK (offKey sc) (offKey tc) = true
  · simp only [h, ite_true]
    rw [abs_mul_dictionary hs ht, privatePairCost_keys hs]
    push_cast
    ring
  · simp only [h, Bool.false_eq_true, ite_false, Nat.cast_zero, zero_div]

theorem map_product_keys {α β γ : Type*} (l : List α) (f : α → β) (g : β → β → γ) :
    (l.product l).map (fun st => g (f st.1) (f st.2)) =
      ((l.map f).product (l.map f)).map (fun kk => g kk.1 kk.2) := by
  simp [List.product, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

/-- The keys of the entries of `dictionary39`. -/
def offKeys : List (List ℕ) :=
  [
    [0, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 1],
    [0, 1, 0, 2, 1, 1, 0, 0, 0, 2], [0, 1, 0, 1, 1, 0, 0, 3, 0, 1],
    [0, 1, 0, 1, 1, 0, 0, 4, 0, 1], [5, 1, 1, 1, 1, 0, 0, 0, 5, 1],
    [5, 1, 1, 2, 1, 1, 0, 0, 5, 2], [7, 1, 1, 0, 1, 1, 0, 0, 7, 0],
    [7, 1, 1, 1, 1, 0, 0, 0, 7, 1], [9, 0, 0, 9, 0, 0, 9, 9, 9, 9],
    [9, 0, 0, 9, 0, 0, 9, 10, 9, 9], [9, 0, 0, 9, 0, 0, 9, 11, 9, 9],
    [9, 0, 0, 9, 0, 0, 9, 12, 9, 9], [9, 0, 0, 9, 0, 0, 9, 13, 9, 9],
    [9, 0, 0, 9, 0, 0, 14, 10, 9, 9], [9, 0, 0, 9, 0, 0, 14, 11, 9, 9],
    [9, 0, 0, 9, 0, 0, 16, 9, 9, 9], [9, 0, 0, 9, 0, 0, 16, 10, 9, 9],
    [0, 1, 0, 1, 1, 0, 18, 0, 0, 1], [0, 1, 0, 1, 1, 0, 18, 4, 0, 1],
    [9, 0, 0, 9, 0, 0, 20, 10, 9, 9], [9, 0, 0, 9, 0, 0, 20, 13, 9, 9],
    [0, 1, 0, 1, 1, 0, 22, 0, 0, 1], [0, 1, 0, 1, 1, 0, 22, 3, 0, 1],
    [9, 0, 0, 9, 0, 0, 24, 10, 9, 9], [9, 0, 0, 9, 0, 0, 24, 12, 9, 9],
    [0, 1, 0, 1, 1, 0, 26, 26, 0, 1], [0, 1, 0, 1, 1, 0, 26, 27, 0, 1],
    [0, 1, 0, 1, 1, 0, 26, 28, 0, 1], [0, 1, 0, 0, 1, 1, 26, 27, 0, 0],
    [0, 1, 0, 2, 1, 1, 26, 27, 0, 2], [0, 1, 0, 1, 1, 0, 31, 27, 0, 1],
    [0, 1, 0, 1, 1, 0, 31, 28, 0, 1], [0, 1, 0, 1, 1, 0, 33, 26, 0, 1],
    [0, 1, 0, 1, 1, 0, 33, 27, 0, 1], [5, 1, 1, 1, 1, 0, 26, 27, 5, 1],
    [5, 1, 1, 2, 1, 1, 26, 27, 5, 2], [7, 1, 1, 1, 1, 0, 26, 27, 7, 1],
    [7, 1, 1, 0, 1, 1, 26, 27, 7, 0]]

theorem offKeys_eq : dictionary39.map offKey = offKeys := by
  decide +kernel

theorem core_keys_sum :
    ((offKeys.product offKeys).map fun kk => coreK kk.1 kk.2).sum = 17280 := by
  decide +kernel

theorem private_keys_sum :
    ((offKeys.product offKeys).map fun kk => privCostK kk.1 kk.2).sum = 1448 := by
  decide +kernel

theorem sum_mass_keys (m : (Support × ℚ) × (Support × ℚ) → ℚ)
    (g : List ℕ → List ℕ → ℕ)
    (hm : ∀ sc ∈ dictionary39, ∀ tc ∈ dictionary39,
      m (sc, tc) = (g (offKey sc) (offKey tc) : ℚ) / 225) :
    ((dictionary39.product dictionary39).map m).sum =
      (((offKeys.product offKeys).map fun kk => g kk.1 kk.2).sum : ℚ) / 225 := by
  rw [List.map_congr_left (fun st hst => by
      obtain ⟨h1, h2⟩ := List.mem_product.mp hst
      exact hm st.1 h1 st.2 h2), ← offKeys_eq,
    ← map_product_keys dictionary39 offKey g, Nat.cast_list_sum, List.map_map]
  simp only [div_eq_mul_inv]
  rw [List.sum_map_mul_right]
  rfl

theorem core_cost_keys : ((dictionary39.product dictionary39).map coreMassK).sum =
    17280 / 225 := by
  rw [sum_mass_keys coreMassK coreK (fun sc hs tc ht => coreCostMass_keys hs ht),
    core_keys_sum]
  norm_num

theorem private_cost_keys : ((dictionary39.product dictionary39).map privateMassK).sum =
    1448 / 225 := by
  rw [sum_mass_keys privateMassK privCostK (fun sc hs tc ht => privateCostMass_keys hs ht),
    private_keys_sum]
  norm_num

end Sarkozy.PositiveRoots.CoherentFrame
