module

public import Sarkozy.F3Kernel.WitnessExponent

/-!
# Products of exact graph counts along the certificate scan

The packed loops multiply factors at the free degree plus the number of neighbours already
visited. These identities include the insertion of all witnesses between the cover and
integrated phases. No factor-table estimates enter these equalities.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

variable (E : Fin 36 → Fin 36 → Prop) [DecidableRel E]

noncomputable def countProd (f : ℕ → ℝ) (h : Fin 36 → ℕ) :
    List ℕ → List ℕ → ℝ
  | _, [] => 1
  | p, u :: s => f (vertexValue (countState E h p) u) * countProd f h (p ++ [u]) s

noncomputable def sideCountProd (m rho : ℕ → ℝ) (h : Fin 36 → ℕ)
    (C : ℕ) (w : List ℕ) : List ℕ → List ℕ → ℝ
  | _, [] => 1
  | p, u :: s =>
      if bit C u then
        rho (vertexValue (countState E h p) u) * sideCountProd m rho h C w (p ++ [u]) s
      else countProd E m h (p ++ w) (u :: s)

theorem integratedProd_counts {G : Consts} (hG : AdjacencyCounts G E)
    (m : ℕ → ℝ) {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36)
    {n r : ℕ} {p : List ℕ} (hlen : p.length + n ≤ 36)
    (hs : ∀ u ∈ packedList n r, u < 36) :
    integratedProd G m n r (packCounts (countState E h p)) =
      countProd E m h p (packedList n r) := by
  induction n generalizing r p with
  | zero => rfl
  | succ n ih =>
      have hu : firstVertex r < 36 := hs _ (List.mem_cons_self)
      have htail : ∀ u ∈ packedList n (Nat.shiftRight r 6), u < 36 :=
        fun u hu => hs u (List.mem_cons_of_mem _ hu)
      change m (signature (packCounts (countState E h p)) (firstVertex r)) *
          integratedProd G m n (Nat.shiftRight r 6)
            (packCounts (countState E h p) + adj64 G (firstVertex r)) =
        m (vertexValue (countState E h p) (firstVertex r)) *
          countProd E m h (p ++ [firstVertex r]) (packedList n (Nat.shiftRight r 6))
      rw [add_adj64_countState E hG h p ⟨_, hu⟩, ih (by simp; omega) htail]
      congr 1
      apply congrArg m
      rw [vertexValue, dite_eq_left hu]
      exact signature_countState E hh (s := p) (by omega) ⟨_, hu⟩

theorem sideProd_counts {G : Consts} (hG : AdjacencyCounts G E)
    (m rho : ℕ → ℝ) {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36)
    {C wl k hw n r : ℕ} {p : List ℕ} (hlen : p.length + n + k ≤ 36)
    (hwit : ∀ u ∈ packedList k wl, u < 36)
    (hs : ∀ u ∈ packedList n r, u < 36) :
    sideProd G m rho C wl k hw n r (packCounts (countState E h p)) =
      sideCountProd E m rho h C (packedList k wl) p (packedList n r) := by
  induction n generalizing r p with
  | zero => rfl
  | succ n ih =>
      have hu : firstVertex r < 36 := hs _ List.mem_cons_self
      have htail : ∀ u ∈ packedList n (Nat.shiftRight r 6), u < 36 :=
        fun u hu => hs u (List.mem_cons_of_mem _ hu)
      change (if bit C (firstVertex r) then _ else _) =
        (if bit C (firstVertex r) then _ else _)
      split
      · rw [add_adj64_countState E hG h p ⟨_, hu⟩, ih (by simp; omega) htail]
        congr 1
        apply congrArg rho
        change _ = vertexValue (countState E h p) (firstVertex r)
        rw [vertexValue, dite_eq_left hu]
        exact signature_countState E hh (s := p) (by omega) ⟨_, hu⟩
      · rw [witSwitch_counts E hG h p hwit]
        exact integratedProd_counts E hG m hh (by
          simp only [List.length_append, packedList_length]
          omega) hs

theorem sideCountProd_split (m rho : ℕ → ℝ) (h : Fin 36 → ℕ)
    (C : ℕ) (w p s : List ℕ) :
    sideCountProd E m rho h C w p s =
      countProd E rho h p (s.takeWhile (bit C)) *
        countProd E m h (p ++ s.takeWhile (bit C) ++ w) (s.dropWhile (bit C)) := by
  induction s generalizing p with
  | nil => simp only [sideCountProd, List.takeWhile_nil, List.dropWhile_nil, countProd,
      mul_one]
  | cons u s ih =>
      by_cases hu : bit C u = true
      · simp only [sideCountProd, hu, ite_true, List.takeWhile_cons_of_pos,
          List.dropWhile_cons_of_pos, countProd]
        rw [ih, mul_assoc]
        simp only [List.append_assoc, List.singleton_append]
      · have hf : bit C u = false := Bool.eq_false_iff.mpr hu
        simp only [sideCountProd, hf, Bool.false_eq_true, ite_false,
          List.takeWhile_cons_of_neg hu, List.dropWhile_cons_of_neg hu,
          countProd, List.append_nil, one_mul]

end Sarkozy.F3Kernel
