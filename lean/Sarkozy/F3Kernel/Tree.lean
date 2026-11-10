module

public import Sarkozy.F3Kernel.Split

@[expose] public section




namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

/-- The decoded class datum `(P, A)` of a cylinder (`T` layout). -/
def dec (c : Cyl) : Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36) := (decT c.pt, decT c.qt)

/-- The pending cylinders of a state: the current one, then the stack. -/
def pend (st : St) : List Cyl := st.cur.toList ++ st.stack

/-- `l` tiles `U`: class data of `Ex` whose classes are pairwise disjoint with union `U`. -/
structure Tiling (Ex : Finset (Fin 36 × Fin 36))
    (l : List (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36)))
    (U : Finset (Finset (Fin 36 × Fin 36))) : Prop where
  datum : ∀ x ∈ l, IsClassDatum Ex x
  disj : l.Pairwise fun a b => Disjoint (cls Ex a.1 a.2) (cls Ex b.1 b.2)
  union : ∀ S, S ∈ U ↔ ∃ x ∈ l, S ∈ cls Ex x.1 x.2

section Tiling

variable {Ex : Finset (Fin 36 × Fin 36)} {U : Finset (Finset (Fin 36 × Fin 36))}

/-- A tiling does not depend on the order of the list. -/
theorem Tiling.perm {l l' : List (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36))}
    (h : l.Perm l') (t : Tiling Ex l U) : Tiling Ex l' U where
  datum x hx := t.datum x (h.mem_iff.2 hx)
  disj := (h.pairwise_iff fun hab => hab.symm).1 t.disj
  union S := (t.union S).trans
    ⟨fun ⟨x, hx, hS⟩ => ⟨x, h.mem_iff.1 hx, hS⟩, fun ⟨x, hx, hS⟩ => ⟨x, h.mem_iff.2 hx, hS⟩⟩

/-- Replacing the first class datum by its two children at a free pair keeps a tiling. -/
theorem Tiling.split {P A : Finset (Fin 36 × Fin 36)}
    {rest : List (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36))} {g : Fin 36 × Fin 36}
    (t : Tiling Ex ((P, A) :: rest) U) (hg : g ∈ Ex \ (P ∪ A)) :
    Tiling Ex ((insert g P, A) :: (P, insert g A) :: rest) U := by
  have hd := t.datum
  have hdisj := t.disj
  rw [List.pairwise_cons] at hdisj
  obtain ⟨hhead, hrest⟩ := hdisj
  have hch := (hd (P, A) List.mem_cons_self).children hg
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hch.1
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hch.2
    exact hd x (List.mem_cons_of_mem _ hx)
  · rw [List.pairwise_cons, List.pairwise_cons]
    refine ⟨?_, ⟨?_, hrest⟩⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact cls_children_disjoint Ex P A g
      · exact (hhead y hy).mono_left (cls_present_subset Ex P A g)
    · intro y hy
      exact (hhead y hy).mono_left (cls_absent_subset Ex P A g)
  · intro S
    rw [t.union S]
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [← cls_children_union Ex P A g, mem_union, or_assoc]

/-- For a symmetric relation, a pairwise list relates any two distinct members. -/
theorem pairwise_mem {α : Type*} {R : α → α → Prop} (hS : ∀ {x y}, R x y → R y x) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha'
    · rcases List.mem_cons.1 hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.1 hb with hb' | hb'
      · rw [hb']; exact hS (h.1 a ha')
      · exact pairwise_mem hS h.2 ha' hb' hab

/-- A tiling gives an exact partition (`IsExactPartition`) of its union. -/
theorem Tiling.isExactPartition
    {l : List (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36))} (t : Tiling Ex l U) :
    IsExactPartition Ex l.toFinset U := by
  refine ⟨fun c hc => t.datum c (List.mem_toFinset.1 hc), ?_, ?_⟩
  · intro a ha b hb hab
    exact pairwise_mem (fun h => h.symm) t.disj (List.mem_toFinset.1 ha)
      (List.mem_toFinset.1 hb) hab
  · ext S
    simp only [mem_biUnion, List.mem_toFinset]
    exact (t.union S).symm

end Tiling

/-! ### The token machine -/

/-- The cylinders at which leaf tokens are consumed along a run (a ghost of `run`). -/
noncomputable def trace (G : Consts) : List Nat → St → List Cyl
  | [], _ => []
  | t :: ts, st =>
    match step G st t with
    | none => []
    | some st' => (if Nat.land t 3 = 2 then st.cur.toList else []) ++ trace G ts st'

theorem run_nil (G : Consts) (st : St) : run G [] st = some st := rfl

theorem run_cons (G : Consts) (t : Nat) (ts : List Nat) (st : St) :
    run G (t :: ts) st = (step G st t).bind (run G ts) := by
  show (match step G st t with | none => none | some st' => run G ts st') = _
  cases step G st t <;> rfl

/-- A split token `4 pay + 1` accepted on the current cylinder `c` replaces it, in the pending
list, by its two decoded children at a free pair. -/
theorem step_split_pend {G : Consts} (hG : G.WellFormedT) {st st' : St} {c : Cyl} {pay : Nat}
    (hc : st.cur = some c) (h : step G st (4 * pay + 1) = some st') :
    ∃ g ∈ decT G.ET \ (decT c.pt ∪ decT c.qt), ∃ c₁ c₂ : Cyl,
      pend st' = c₁ :: c₂ :: st.stack ∧ dec c₁ = (insert g (decT c.pt), decT c.qt) ∧
      dec c₂ = (decT c.pt, insert g (decT c.qt)) := by
  obtain ⟨htag, hpay⟩ := split_token pay
  obtain ⟨hx, hy, hg, -, -⟩ := step_split hG hc h
  refine ⟨pairOf pay hx hy, hg, ?_⟩
  unfold step at h
  simp only [htag, hpay, hc, Nat.beq_refl, Bool.cond_true] at h
  have hguard : (Nat.blt pay 2304 && isEdge G pay && !bit (Nat.lor c.pt c.qt) pay) = true := by
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rw [hne, Bool.cond_false] at h
    cases h
  rw [hguard, Bool.cond_true, Option.some.injEq] at h
  subst h
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp only [dec, decT_lor_bit _ _ hx hy]
  · simp only [dec, decT_lor_bit _ _ hx hy]

/-- A leaf token accepted on the current cylinder `c` pops the stack: the pending list becomes
the stack. -/
theorem step_leaf_pend {G : Consts} {st st' : St} {c : Cyl} {t : Nat} (ht : Nat.land t 3 = 2)
    (hc : st.cur = some c) (h : step G st t = some st') : pend st' = st.stack := by
  unfold step at h
  simp only [ht, hc, show Nat.beq 2 1 = false from rfl, show Nat.beq 2 2 = true from rfl,
    Bool.cond_false, Bool.cond_true] at h
  split at h
  · cases h
  · rename_i k v free _
    revert h
    cases Nat.beq _ 0 <;> simp only [Bool.cond_true, Bool.cond_false]
    · intro h
      rw [Option.some.injEq] at h
      subst h
      unfold popNext pend
      cases st.stack <;> rfl
    · intro h
      cases h

/-- **The run invariant.** On split and leaf tokens, an accepted run keeps the pending
cylinders plus the traced leaves a tiling (with the given leaves `L` already consumed). -/
theorem run_tiling {G : Consts} (hG : G.WellFormedT) {U : Finset (Finset (Fin 36 × Fin 36))} :
    ∀ (toks : List Nat) (st st' : St) (L : List Cyl),
      (∀ t ∈ toks, Nat.land t 3 = 1 ∨ Nat.land t 3 = 2) → run G toks st = some st' →
      Tiling (decT G.ET) ((pend st ++ L).map dec) U →
      Tiling (decT G.ET) ((pend st' ++ (L ++ trace G toks st)).map dec) U
  | [], st, st', L, _, h, hT => by
    rw [run_nil, Option.some.injEq] at h
    subst h
    simpa [trace] using hT
  | t :: ts, st, st', L, htoks, h, hT => by
    rw [run_cons] at h
    cases hs : step G st t with
    | none => rw [hs] at h; cases h
    | some st₁ =>
      rw [hs, Option.bind_some] at h
      have hts : ∀ t' ∈ ts, Nat.land t' 3 = 1 ∨ Nat.land t' 3 = 2 :=
        fun t' ht' => htoks t' (List.mem_cons_of_mem _ ht')
      -- the current cylinder exists (a split or leaf token needs one)
      obtain ⟨c, hc⟩ : ∃ c, st.cur = some c := by
        cases hcur : st.cur with
        | some c => exact ⟨c, rfl⟩
        | none =>
          exfalso
          unfold step at hs
          rcases htoks t List.mem_cons_self with ht | ht
          · simp only [ht, hcur, Nat.beq_refl, Bool.cond_true] at hs
            cases hs
          · simp only [ht, hcur, show Nat.beq 2 1 = false from rfl,
              show Nat.beq 2 2 = true from rfl, Bool.cond_false, Bool.cond_true] at hs
            cases hs
      have htr : trace G (t :: ts) st =
          (if Nat.land t 3 = 2 then st.cur.toList else []) ++ trace G ts st₁ := by
        rw [trace, hs]
      rcases htoks t List.mem_cons_self with ht | ht
      · -- split
        have ht4 : t = 4 * Nat.shiftRight t 2 + 1 := by
          rw [show Nat.shiftRight t 2 = t >>> 2 from rfl, Nat.shiftRight_eq_div_pow]
          rw [show Nat.land t 3 = t &&& (2 ^ 2 - 1) from rfl,
            Nat.and_two_pow_sub_one_eq_mod] at ht
          omega
        rw [ht4] at hs
        obtain ⟨g, hg, c₁, c₂, hpend, hd₁, hd₂⟩ := step_split_pend hG hc hs
        have e0 : (pend st ++ L).map dec = (decT c.pt, decT c.qt) :: (st.stack ++ L).map dec := by
          simp only [pend, hc, Option.toList_some, List.cons_append, List.nil_append,
            List.map_cons]
          rfl
        have hsplit := (e0 ▸ hT).split hg
        have hT₁ : Tiling (decT G.ET) ((pend st₁ ++ L).map dec) U := by
          rw [hpend, List.cons_append, List.cons_append, List.map_cons, List.map_cons, hd₁, hd₂]
          exact hsplit
        have := run_tiling hG ts st₁ st' L hts h hT₁
        have hne : ¬ Nat.land t 3 = 2 := by rw [ht]; decide
        rw [htr]
        simp only [hne, ↓reduceIte, List.nil_append]
        exact this
      · -- leaf
        have hpend := step_leaf_pend ht hc hs
        have hT₁ : Tiling (decT G.ET) ((pend st₁ ++ (L ++ [c])).map dec) U := by
          refine hT.perm ?_
          have e1 : (pend st ++ L).map dec = [dec c] ++ (st.stack ++ L).map dec := by
            simp only [pend, hc, Option.toList_some, List.cons_append, List.nil_append,
              List.map_cons]
          have e2 : (pend st₁ ++ (L ++ [c])).map dec = (st.stack ++ L).map dec ++ [dec c] := by
            rw [hpend, ← List.append_assoc, List.map_append, List.map_singleton]
          rw [e1, e2]
          exact List.perm_append_comm
        have := run_tiling hG ts st₁ st' (L ++ [c]) hts h hT₁
        rw [htr]
        simp only [ht, ↓reduceIte, hc, Option.toList_some]
        simpa [List.append_assoc] using this

/-- **The leaves of an accepted class body form an exact partition of the root's class.** If
the current cylinder is `root` with an empty stack and no leaves consumed, `root` decodes to a
class datum, and the machine accepts a body of split and leaf tokens ending with no pending
cylinder, then the traced leaves form an exact partition of `𝒞(P, A)`, `(P, A)` = `dec root`. -/
theorem body_isExactPartition {G : Consts} (hG : G.WellFormedT) {st st' : St} {root : Cyl}
    {toks : List Nat} (hroot : st.cur = some root) (hstack : st.stack = [])
    (hdat : IsClassDatum (decT G.ET) (dec root))
    (htoks : ∀ t ∈ toks, Nat.land t 3 = 1 ∨ Nat.land t 3 = 2)
    (h : run G toks st = some st') (hend : pend st' = []) :
    IsExactPartition (decT G.ET) ((trace G toks st).map dec).toFinset
      (cls (decT G.ET) (dec root).1 (dec root).2) := by
  have h0 : Tiling (decT G.ET) ((pend st ++ []).map dec)
      (cls (decT G.ET) (dec root).1 (dec root).2) := by
    simp only [pend, hroot, hstack, Option.toList_some, List.append_nil, List.map_cons,
      List.map_nil]
    refine ⟨fun x hx => by rw [List.mem_singleton.1 hx]; exact hdat, List.pairwise_singleton _ _,
      fun S => ?_⟩
    simp
  have := run_tiling hG toks st st' [] htoks h h0
  rw [hend, List.nil_append, List.nil_append] at this
  exact this.isExactPartition

/-! ### A bit-level criterion for class data, and the sanity class -/

/-- `decT` is monotone along `Nat.land`: if `a &&& b = a`, then `decT a ⊆ decT b`. -/
theorem decT_subset_of_land {a b : Nat} (h : Nat.land a b = a) : decT a ⊆ decT b := by
  intro e he
  simp only [decT, mem_filter, mem_univ, true_and] at he ⊢
  rw [← h, show Nat.land a b = a &&& b from rfl, Nat.testBit_and, Bool.and_eq_true] at he
  exact he.2

/-- Disjoint masks decode to disjoint sets. -/
theorem decT_disjoint_of_land {a b : Nat} (h : Nat.land a b = 0) : Disjoint (decT a) (decT b) := by
  rw [Finset.disjoint_left]
  intro e ha hb
  simp only [decT, mem_filter, mem_univ, true_and] at ha hb
  have := Nat.testBit_and a b (64 * (e.2 : Nat) + e.1)
  rw [show a &&& b = Nat.land a b from rfl, h, Nat.zero_testBit, ha, hb] at this
  exact Bool.false_ne_true this

/-- The bit-level test for a class datum: `P, A ⊆ Ex`, `P ∩ A = ∅` (`T` layout). -/
def classDatumB (G : Consts) (c : Cyl) : Bool :=
  Nat.beq (Nat.land c.pt G.ET) c.pt && Nat.beq (Nat.land c.qt G.ET) c.qt &&
    Nat.beq (Nat.land c.pt c.qt) 0

theorem isClassDatum_of_classDatumB {G : Consts} {c : Cyl} (h : classDatumB G c = true) :
    IsClassDatum (decT G.ET) (dec c) := by
  simp only [classDatumB, Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨decT_subset_of_land h.1.1, decT_subset_of_land h.1.2, decT_disjoint_of_land h.2⟩

/-- The decidable form of the hypotheses of `body_isExactPartition` for a class token followed by
a body: the class token is accepted, giving a root that is a class datum and an empty stack;
the body has split and leaf tokens only; it is accepted and ends with nothing pending. -/
noncomputable def bodyCheck (G : Consts) (st₀ : St) (key : Nat) (body : List Nat) : Bool :=
  match step G st₀ key with
  | none => false
  | some st₁ =>
    match st₁.cur with
    | none => false
    | some root =>
      st₁.stack.isEmpty && classDatumB G root &&
        body.all (fun t => Nat.beq (Nat.land t 3) 1 || Nat.beq (Nat.land t 3) 2) &&
        match run G body st₁ with
        | none => false
        | some st' => (pend st').isEmpty

/-- From `bodyCheck`: the traced leaves of the body form an exact partition of the class of the
root produced by the class token. -/
theorem bodyCheck_sound {G : Consts} (hG : G.WellFormedT) {st₀ : St} {key : Nat}
    {body : List Nat} (h : bodyCheck G st₀ key body = true) :
    ∃ st₁ root, step G st₀ key = some st₁ ∧ st₁.cur = some root ∧
      IsExactPartition (decT G.ET) ((trace G body st₁).map dec).toFinset
        (cls (decT G.ET) (dec root).1 (dec root).2) := by
  unfold bodyCheck at h
  split at h
  · cases h
  rename_i st₁ hst₁
  split at h
  · cases h
  rename_i root hroot
  split at h
  · simp at h
  rename_i st' hrun
  simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.or_eq_true,
    Nat.beq_eq] at h
  obtain ⟨⟨⟨hstack, hdat⟩, htoks⟩, hend⟩ := h
  exact ⟨st₁, root, hst₁, hroot, body_isExactPartition hG hroot hstack
    (isClassDatum_of_classDatumB hdat) htoks hrun hend⟩

/-- `bodyCheck` holds for the class `Sanity.good` (a class token, then three splits and four
leaves), so its four traced leaves form an exact partition of its root's class (next theorem). -/
theorem good_bodyCheck :
    bodyCheck LL20 ⟨none, [], 0, 0, 0, 0, 0, 0, 0⟩ (Sanity.good.getD 0 0) Sanity.good.tail = true := by
  decide +kernel

/-- **Non-vacuity of `body_isExactPartition`**: the leaves of the sanity class form an exact
partition of the class of its root (the A/B class of its key). -/
theorem good_isExactPartition :
    ∃ st₁ root, step LL20 ⟨none, [], 0, 0, 0, 0, 0, 0, 0⟩ (Sanity.good.getD 0 0) = some st₁ ∧
      st₁.cur = some root ∧
      IsExactPartition (decT LL20.ET) ((trace LL20 Sanity.good.tail st₁).map dec).toFinset
        (cls (decT LL20.ET) (dec root).1 (dec root).2) :=
  bodyCheck_sound LL20_wellFormedT good_bodyCheck

end Sarkozy.F3Kernel
