module

public import Sarkozy.Envelopes.MaskCheck
public import Sarkozy.Envelopes.MaskSchur

@[expose] public section

/-!
# From the kernel check to the envelope (`lem:oct24:mask-schur`(c), `cert:envelopes`(b))

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(c) and `cert:envelopes`(b): the reduction
of a general mask to its counts, which turns the kernel checks of `MaskCheck` into the hypothesis
of `mask_schur` for every mask, and hence into the envelope property.

**The features.** For a class with `n` fold and `m` matching factors, a feature that is a centre or
an arm at every factor is a pair of label vectors `Fin n → Fin 4` (centre `0`, arms `1, 2, 3`) and
`Fin m → Fin 2` (centre `0`, arm `1`) (`Feat`). Its mask is the pair of arm sets (`featMask`), the
complement of masks is `maskCompl`, `α(v)` is the product of the fold arm magnitudes
`1, t, 1 - t` at the arm positions (`featAlpha`), and `d_v` is the table's weight of the sorted
label words of `v` (`featWeight`).

**Proved.**
* `sortNat_perm_eq`: `sortNat` depends only on the multiset;
* `mask_reduction`: `∑_{featMask v = (A, B)} α(v)²/d_v = maskSum T n m |A| |B|` for every mask;
* `mask_condition_all`: the mask conditions `eq:oct24:mask-schur` for every complementary pair of
  masks, from `tablePos` and `maskCheck`;
* `checked_table_envelope`: for a checked table, `-D ⪯ T ⪯ D` for every block operator `T` with the
  sector structure of a tensor of stars (`T_{wv} = 0` unless the masks are complementary, and
  `‖T_{wv}‖ ≤ α(v) α(w)`), with `D` the diagonal of the table's weights.
-/

namespace Sarkozy.Envelopes

open Finset

/-! ### `sortNat` is the insertion sort and depends only on the multiset -/

theorem insOrd_eq (a : ℕ) (l : List ℕ) : insOrd a l = l.orderedInsert (· ≤ ·) a := by
  induction l with
  | nil => simp [insOrd]
  | cons b l ih =>
    simp only [insOrd, List.orderedInsert_cons, ih]
    by_cases h : a ≤ b
    · simp [Nat.ble_eq_true_of_le h, h]
    · have : Nat.ble a b = false := by
        cases hb : Nat.ble a b
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true hb) h
      simp [this, h]

theorem sortNat_eq (l : List ℕ) : sortNat l = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => simp [sortNat]
  | cons a l ih => simp only [sortNat, List.insertionSort_cons, ih, insOrd_eq]

theorem sortNat_perm_eq {l l' : List ℕ} (h : l.Perm l') : sortNat l = sortNat l' := by
  rw [sortNat_eq, sortNat_eq]
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact List.pairwise_insertionSort _ _
  · exact List.pairwise_insertionSort _ _
  · exact (List.perm_insertionSort _ l).trans (h.trans (List.perm_insertionSort _ l').symm)



/-! ### Fold label vectors with arms on a set `A` -/

section Fold

variable {n : ℕ}

/-- The fold arm positions of a fold label vector (labels `1, 2, 3`). -/
def fArms (v : Fin n → Fin 4) : Finset (Fin n) := univ.filter fun i => v i ≠ 0

/-- The extension of an arm labelling `g : A → {1, 2, 3}` (coded in `Fin 3`) by centres. -/
def extF (A : Finset (Fin n)) (g : A → Fin 3) : Fin n → Fin 4 :=
  fun i => if h : i ∈ A then ⟨(g ⟨i, h⟩ : ℕ) + 1, by have := (g ⟨i, h⟩).isLt; omega⟩ else 0

/-- The restriction to `A`, inverse of `extF` on the vectors with arms exactly `A`. -/
def resF (A : Finset (Fin n)) (v : Fin n → Fin 4) : A → Fin 3 :=
  fun a => ⟨((v a : ℕ) - 1) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem fArms_extF (A : Finset (Fin n)) (g : A → Fin 3) : fArms (extF A g) = A := by
  ext i
  rw [fArms, Finset.mem_filter]
  simp only [mem_univ, true_and, extF]
  by_cases h : i ∈ A
  · simp only [h, dite_true, iff_true]
    intro h0
    have := congrArg Fin.val h0
    simp at this
  · simp [h]

theorem extF_resF {A : Finset (Fin n)} {v : Fin n → Fin 4} (hv : fArms v = A) :
    extF A (resF A v) = v := by
  funext i
  simp only [extF, resF]
  by_cases h : i ∈ A
  · simp only [h, dite_true]
    have hi : v i ≠ 0 := by
      rw [← hv, fArms, Finset.mem_filter] at h; exact h.2
    have hi' : (v i : ℕ) ≠ 0 := fun h0 => hi (Fin.ext h0)
    have hlt := (v i).isLt
    ext
    simp only
    omega
  · simp only [h, dite_false]
    have : v i = 0 := by
      rw [← hv, fArms, Finset.mem_filter] at h; simpa using h
    exact this.symm

theorem resF_extF (A : Finset (Fin n)) (g : A → Fin 3) : resF A (extF A g) = g := by
  funext a
  simp only [resF, extF, a.2, dite_true]
  ext
  simp only [Subtype.coe_eta]
  have := (g a).isLt
  omega

theorem sum_fArms (A : Finset (Fin n)) (G : (Fin n → Fin 4) → ℚ) :
    ∑ v ∈ univ.filter (fun v => fArms v = A), G v = ∑ g : A → Fin 3, G (extF A g) := by
  apply Finset.sum_nbij' (resF A) (extF A)
  · intro v _; exact mem_univ _
  · intro g _; simp [fArms_extF]
  · intro v hv; exact extF_resF (mem_filter.1 hv).2
  · intro g _; exact resF_extF A g
  · intro v hv; rw [extF_resF (mem_filter.1 hv).2]

end Fold

/-! ### The sorted words -/

theorem zeros_eq (p : ℕ) : zeros p = List.replicate p 0 := by
  induction p with
  | zero => simp [zeros]
  | succ p ih => simp [zeros, ih, List.replicate_succ]

theorem ones_eq (p : ℕ) : ones p = List.replicate p 1 := by
  induction p with
  | zero => simp [ones]
  | succ p ih => simp [ones, ih, List.replicate_succ]

theorem ofFn_extF_perm {n : ℕ} (A : Finset (Fin n)) (f : Fin A.card → Fin 3) :
    (List.ofFn fun i => (extF A (f ∘ A.equivFin) i : ℕ)).Perm
      (zeros (n - A.card) ++ List.ofFn fun j => (f j : ℕ) + 1) := by
  set h1 : Fin n → ℕ := fun i => (extF A (f ∘ A.equivFin) i : ℕ) with hh1
  set h2 : Fin A.card → ℕ := fun j => (f j : ℕ) + 1 with hh2
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Fin.univ_val_map, ← Fin.univ_val_map, zeros_eq,
    Multiset.coe_replicate]
  have hA : univ.filter (· ∈ A) = A := by ext i; simp
  have hsplit : (univ : Finset (Fin n)).val =
      (univ.filter (· ∈ A)).val + (univ.filter (· ∉ A)).val := by
    rw [Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]
  rw [hsplit, Multiset.map_add, hA]
  have hon : A.val.map h1 = (univ : Finset (Fin A.card)).val.map h2 := by
    rw [← Multiset.attach_map_val' A.val h1, ← Finset.attach_val, ← Finset.univ_eq_attach,
      ← Multiset.map_univ_val_equiv A.equivFin.symm, Multiset.map_map]
    congr 1
    funext j
    have hm : ((A.equivFin.symm j : A) : Fin n) ∈ A := (A.equivFin.symm j).2
    simp only [Function.comp_apply, hh1, hh2, extF, hm, ↓reduceDIte, Subtype.coe_eta,
      Equiv.apply_symm_apply]
  have hcard : (univ.filter (· ∉ A)).card = n - A.card := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (p := (· ∈ A))
    rw [hA, card_univ, Fintype.card_fin] at this
    omega
  have hoff : (univ.filter (· ∉ A)).val.map h1 = Multiset.replicate (n - A.card) 0 := by
    rw [Multiset.map_congr rfl (g := fun _ => 0) (fun x hx => ?_), Multiset.map_const',
      Finset.card_val, hcard]
    rw [Finset.mem_val, Finset.mem_filter] at hx
    simp only [hh1, extF, hx.2, dite_false, Fin.val_zero]
  rw [hon, hoff, add_comm]

/-! ### The matching part -/

section Match

variable {m : ℕ}

/-- The matching arm positions (label `1`). -/
def eArms (v : Fin m → Fin 2) : Finset (Fin m) := univ.filter fun j => v j ≠ 0

/-- The matching label vector with arms exactly `B`. -/
def indE (B : Finset (Fin m)) : Fin m → Fin 2 := fun j => if j ∈ B then 1 else 0

theorem eArms_eq_iff (B : Finset (Fin m)) (v : Fin m → Fin 2) : eArms v = B ↔ v = indE B := by
  constructor
  · intro hv
    funext j
    simp only [indE]
    by_cases h : j ∈ B
    · have hj : v j ≠ 0 := by rw [← hv, eArms, Finset.mem_filter] at h; exact h.2
      have hj' : (v j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext h0)
      have hlt := (v j).isLt
      simp only [h, ↓reduceIte]
      ext
      simp only [Fin.val_one]
      omega
    · have hj : v j = 0 := by rw [← hv, eArms, Finset.mem_filter] at h; simpa using h
      simp only [h, ↓reduceIte, hj]
  · rintro rfl
    ext j
    rw [eArms, Finset.mem_filter]
    by_cases h : j ∈ B <;> simp [indE, h]

theorem ofFn_indE_perm (B : Finset (Fin m)) :
    (List.ofFn fun j => (indE B j : ℕ)).Perm (zeros (m - B.card) ++ ones B.card) := by
  set h1 : Fin m → ℕ := fun j => (indE B j : ℕ) with hh1
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Fin.univ_val_map, zeros_eq, ones_eq,
    Multiset.coe_replicate, Multiset.coe_replicate]
  have hB : univ.filter (· ∈ B) = B := by ext i; simp
  have hsplit : (univ : Finset (Fin m)).val =
      (univ.filter (· ∈ B)).val + (univ.filter (· ∉ B)).val := by
    rw [Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]
  have hcard : (univ.filter (· ∉ B)).card = m - B.card := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (p := (· ∈ B))
    rw [hB, card_univ, Fintype.card_fin] at this
    omega
  rw [hsplit, Multiset.map_add, hB]
  have hon : B.val.map h1 = Multiset.replicate B.card 1 := by
    rw [Multiset.map_congr rfl (g := fun _ => 1) (fun x hx => ?_), Multiset.map_const',
      Finset.card_val]
    rw [Finset.mem_val] at hx
    simp [hh1, indE, hx]
  have hoff : (univ.filter (· ∉ B)).val.map h1 = Multiset.replicate (m - B.card) 0 := by
    rw [Multiset.map_congr rfl (g := fun _ => 0) (fun x hx => ?_), Multiset.map_const',
      Finset.card_val, hcard]
    rw [Finset.mem_val, Finset.mem_filter] at hx
    simp [hh1, indE, hx.2]
  rw [hon, hoff, add_comm]

theorem sortNat_zeros_ones (p r : ℕ) : sortNat (zeros p ++ ones r) = zeros p ++ ones r := by
  rw [sortNat_eq]
  apply List.Pairwise.insertionSort_eq
  rw [zeros_eq, ones_eq, List.pairwise_append]
  refine ⟨List.pairwise_replicate.2 (Or.inr (le_refl 0)),
    List.pairwise_replicate.2 (Or.inr (le_refl 1)), ?_⟩
  intro a ha b hb
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

theorem sortedWord_indE (B : Finset (Fin m)) :
    sortNat (List.ofFn fun j => (indE B j : ℕ)) = matchWord m B.card := by
  rw [sortNat_perm_eq (ofFn_indE_perm B), sortNat_zeros_ones]
  rfl

end Match

/-! ### The words `{1, 2, 3}^k` -/

theorem sum_armWords (k : ℕ) (F : List ℕ → ℚ) :
    ((armWords k).map F).sum = ∑ f : Fin k → Fin 3, F (List.ofFn fun j => (f j : ℕ) + 1) := by
  induction k generalizing F with
  | zero => simp [armWords]
  | succ k ih =>
    have hflat : ∀ L : List (List ℕ), ((L.flatMap fun ls => [1 :: ls, 2 :: ls, 3 :: ls]).map F).sum
        = (L.map fun ls => F (1 :: ls) + F (2 :: ls) + F (3 :: ls)).sum := by
      intro L
      induction L with
      | nil => simp
      | cons ls L ihL =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append, ihL, List.map_cons,
          List.sum_cons, List.map_nil, List.sum_nil]
        ring
    simp only [armWords]
    rw [hflat, ih]
    rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-! ### The reduction of a mask to its counts -/

/-- The tensor features of a class with `n` fold and `m` matching factors that are centres or arms:
fold labels in `{0, 1, 2, 3}` (centre `0`, arms `1, 2, 3`; the inactive label `4` is excluded) and
matching labels in `{0, 1}` (centre `0`, arm `1`; the inactive label `2` is excluded). -/
abbrev Feat (n m : ℕ) := (Fin n → Fin 4) × (Fin m → Fin 2)

/-- The mask of a feature: its fold and matching arm positions. -/
def featMask {n m : ℕ} (v : Feat n m) : Finset (Fin n) × Finset (Fin m) := (fArms v.1, eArms v.2)

/-- The complement of masks. -/
def maskCompl {n m : ℕ} (A : Finset (Fin n) × Finset (Fin m)) : Finset (Fin n) × Finset (Fin m) :=
  (A.1ᶜ, A.2ᶜ)

/-- `α(v)`, the product of the arm magnitudes at the arm positions (the matching arm has
magnitude `1`). -/
def featAlpha {n m : ℕ} (v : Feat n m) : ℚ := ∏ i ∈ fArms v.1, armMag (v.1 i : ℕ)

/-- `d_v`, the weight of the sorted words of the labels of `v`. -/
def featWeight (T : EnvTable) {n m : ℕ} (v : Feat n m) : ℚ :=
  weight T (sortNat (List.ofFn fun i => (v.1 i : ℕ))) (sortNat (List.ofFn fun j => (v.2 j : ℕ)))

theorem featAlpha_extF {n m : ℕ} (A : Finset (Fin n)) (f : Fin A.card → Fin 3)
    (w : Fin m → Fin 2) :
    featAlpha (extF A (f ∘ A.equivFin), w) ^ 2 =
      ((List.ofFn fun j => (f j : ℕ) + 1).map fun l => armMag l ^ 2).prod := by
  unfold featAlpha
  simp only [fArms_extF]
  rw [List.map_ofFn, List.prod_ofFn, ← Finset.prod_pow]
  rw [← Finset.prod_coe_sort A]
  refine Fintype.prod_equiv A.equivFin _ _ fun a => ?_
  simp only [Function.comp_apply, extF, a.2, ↓reduceDIte, Subtype.coe_eta]

/-- **The reduction of a mask to its counts.** For every mask `(A, B)`,
`∑_{featMask v = (A, B)} α(v)²/d_v = maskSum T n m |A| |B|`: the weights depend only on the sorted
words, so the sum over the features with arms exactly at `(A, B)` is the sum over `{1, 2, 3}^{|A|}`
of `maskSum`. -/
theorem mask_reduction (T : EnvTable) {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) :
    ∑ v ∈ univ.filter (fun v : Feat n m => featMask v = (A, B)), featAlpha v ^ 2 / featWeight T v
      = maskSum T n m A.card B.card := by
  have hfilt : univ.filter (fun v : Feat n m => featMask v = (A, B)) =
      (univ.filter (fun v1 : Fin n → Fin 4 => fArms v1 = A)) ×ˢ
        (univ.filter (fun v2 : Fin m → Fin 2 => eArms v2 = B)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, featMask,
      Prod.ext_iff]
  have hE : univ.filter (fun v2 : Fin m → Fin 2 => eArms v2 = B) = {indE B} := by
    ext v2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, eArms_eq_iff]
  rw [hfilt, Finset.sum_product, hE]
  simp only [Finset.sum_singleton]
  rw [sum_fArms A (fun v1 => featAlpha (v1, indE B) ^ 2 / featWeight T (v1, indE B))]
  rw [← (Equiv.arrowCongr A.equivFin (Equiv.refl (Fin 3))).symm.sum_comp]
  rw [maskSum, sum_armWords]
  refine Finset.sum_congr rfl fun f _ => ?_
  have harrow : (Equiv.arrowCongr A.equivFin (Equiv.refl (Fin 3))).symm f = f ∘ A.equivFin := by
    funext a
    simp [Equiv.arrowCongr]
  rw [harrow, featAlpha_extF]
  congr 1
  unfold featWeight foldWord
  rw [sortNat_perm_eq (ofFn_extF_perm A f), sortedWord_indE]

/-! ### The mask conditions for every mask, and the envelope -/

theorem mem_armWords :
    ∀ (k : ℕ) (f : Fin k → Fin 3), (List.ofFn fun j => (f j : ℕ) + 1) ∈ armWords k
  | 0, _ => by simp [armWords]
  | k + 1, f => by
    rw [List.ofFn_succ]
    simp only [armWords, List.mem_flatMap]
    refine ⟨List.ofFn fun j => (f j.succ : ℕ) + 1, mem_armWords k _, ?_⟩
    have h := (f 0).isLt
    have : (f 0 : ℕ) = 0 ∨ (f 0 : ℕ) = 1 ∨ (f 0 : ℕ) = 2 := by omega
    rcases this with h0 | h0 | h0 <;> simp [h0]

theorem weightQP_snd_pos {T : EnvTable} {n m : ℕ} (hT : tablePos T n m = true) (fw ew : List ℕ) :
    0 < (weightQP T fw ew).2 := by
  unfold tablePos at hT
  simp only [Bool.and_eq_true] at hT
  unfold weightQP
  cases h : T.find? (fun e => e.1 == (fw, ew)) with
  | none => simp
  | some e =>
    have hmem := List.mem_of_find?_eq_some h
    have := List.all_eq_true.1 hT.1 e hmem
    simp only [decide_eq_true_eq] at this
    obtain ⟨_, a, b⟩ := e
    exact this.2

theorem featWeight_eq {T : EnvTable} {n m : ℕ} (v : Feat n m) :
    ∃ f : Fin (fArms v.1).card → Fin 3, featWeight T v =
      weight T (foldWord n (fArms v.1).card (List.ofFn fun j => (f j : ℕ) + 1))
        (matchWord m (eArms v.2).card) := by
  set A := fArms v.1
  set B := eArms v.2
  have h1 : v.1 = extF A (resF A v.1) := (extF_resF rfl).symm
  have h2 : v.2 = indE B := (eArms_eq_iff B v.2).1 rfl
  refine ⟨resF A v.1 ∘ A.equivFin.symm, ?_⟩
  have h3 : resF A v.1 = (resF A v.1 ∘ A.equivFin.symm) ∘ A.equivFin := by
    funext a; simp
  unfold featWeight foldWord
  conv_lhs => rw [h1, h2, h3]
  rw [sortNat_perm_eq (ofFn_extF_perm A _), sortedWord_indE]

theorem featWeight_pos {T : EnvTable} {n m : ℕ} (hT : tablePos T n m = true) (v : Feat n m) :
    0 < featWeight T v := by
  obtain ⟨f, hf⟩ := featWeight_eq (T := T) v
  rw [hf]
  have hk : (fArms v.1).card ≤ n := by
    simpa using Finset.card_le_univ (fArms v.1)
  have ha : (eArms v.2).card ≤ m := by
    simpa using Finset.card_le_univ (eArms v.2)
  have hnum := weight_pos_of_mem hT hk ha (mem_armWords _ f)
  have hden := weightQP_snd_pos hT (foldWord n (fArms v.1).card (List.ofFn fun j => (f j : ℕ) + 1))
    (matchWord m (eArms v.2).card)
  unfold weight QP.toQ
  exact div_pos (by exact_mod_cast hnum) (by exact_mod_cast hden)

theorem armMag_nonneg (l : ℕ) : 0 ≤ armMag l := by
  unfold armMag; split_ifs <;> norm_num

theorem featAlpha_nonneg {n m : ℕ} (v : Feat n m) : 0 ≤ featAlpha v :=
  Finset.prod_nonneg fun _ _ => armMag_nonneg _

/-- **The mask conditions `eq:oct24:mask-schur` for every mask** of a checked table. -/
theorem mask_condition_all {T : EnvTable} {n m : ℕ} (hT : tablePos T n m = true)
    (hC : maskCheck T n m = true) (A : Finset (Fin n) × Finset (Fin m)) :
    (∑ v ∈ univ.filter (fun v : Feat n m => featMask v = A), featAlpha v ^ 2 / featWeight T v) *
      (∑ w ∈ univ.filter (fun w : Feat n m => featMask w = maskCompl A),
        featAlpha w ^ 2 / featWeight T w) ≤ 1 := by
  obtain ⟨A, B⟩ := A
  rw [mask_reduction, show maskCompl (A, B) = (Aᶜ, Bᶜ) from rfl, mask_reduction,
    Finset.card_compl, Finset.card_compl, Fintype.card_fin, Fintype.card_fin]
  have hk : A.card ≤ n := by simpa using Finset.card_le_univ A
  have ha : B.card ≤ m := by simpa using Finset.card_le_univ B
  exact mask_sound hT hC hk ha

/-- **A checked diagonal table is an envelope** (`lem:oct24:mask-schur`(c)). If the kernel checks
`tablePos` and `maskCheck` hold, then for every block operator `T_{wv}` on the features of the
class with the sector structure of a tensor of stars (`T_{wv} = 0` unless the mask of `w` is the
complement of that of `v`, and `‖T_{wv}‖ ≤ α(v) α(w)`), `-D ⪯ T ⪯ D` for the diagonal `D` with the
table's weights: `|∑ ⟨x_w, T_{wv} x_v⟩| ≤ ∑ d_v ‖x_v‖²`. -/
theorem checked_table_envelope {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : EnvTable} {n m : ℕ} (hT : tablePos T n m = true) (hC : maskCheck T n m = true)
    (Top : Feat n m → Feat n m → E →ₗ[ℝ] E)
    (hsec : ∀ v w, featMask w ≠ maskCompl (featMask v) → Top w v = 0)
    (hnorm : ∀ v w y, ‖Top w v y‖ ≤ (featAlpha v : ℝ) * (featAlpha w : ℝ) * ‖y‖)
    (x : Feat n m → E) :
    |∑ v, ∑ w, inner ℝ (x w) (Top w v (x v))| ≤ ∑ v, (featWeight T v : ℝ) * ‖x v‖ ^ 2 := by
  refine mask_schur featMask maskCompl (fun A => by simp [maskCompl]) Top
    (fun v => (featAlpha v : ℝ)) (fun v => (featWeight T v : ℝ))
    (fun v => by exact_mod_cast featAlpha_nonneg v)
    (fun v => by exact_mod_cast featWeight_pos hT v) hsec hnorm ?_ x
  intro A
  have h := mask_condition_all hT hC A
  have h' : ((((∑ v ∈ univ.filter (fun v : Feat n m => featMask v = A),
      featAlpha v ^ 2 / featWeight T v) *
      (∑ w ∈ univ.filter (fun w : Feat n m => featMask w = maskCompl A),
        featAlpha w ^ 2 / featWeight T w) : ℚ)) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  exact h'

end Sarkozy.Envelopes
