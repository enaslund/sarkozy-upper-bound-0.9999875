module

public import Sarkozy.SpectralD.SmallMatrixDefs

/-!
# The residual checks of the smaller cuts as computations on codes

`ResidualChecks c` is stated over the subtype half `c.data.cut.Half`, with every residual
entry recomputing a Gram sum over the half. Through the code `code c`, which maps the half
bijectively onto `range n`, the half sums become sums over `range n`
(`sum_half_eq_range`). The Gram sums become dot products of table columns (`dotZ`,
`colOf`), written with `List.rec`, so that each residual entry costs `4 n` integer
products. The symmetry of the residual matrices follows from that of the test tables, since
the Gram parts are symmetric and antisymmetric for every factor (`gramReal_symm`,
`gramImag_antisymm`). `residualChecks_of` assembles `ResidualChecks c` from checks on codes.
No evaluation happens in this file.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Finset Sarkozy.PartVLaws.FieldGraphs Sarkozy.SpectralC

/-! ### Columns and dot products -/

/-- The column `x` of a table, entries past a row's end read as `0`. -/
def colOf (T : List (List ℤ)) (x : ℕ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun r _ ih => r.getD x 0 :: ih) T

/-- The dot product of two integer lists, truncated to the shorter one. -/
def dotZ (l₁ l₂ : List ℤ) : ℤ :=
  List.rec (motive := fun _ => List ℤ → ℤ) (fun _ => 0)
    (fun a _ ih l => List.casesOn (motive := fun _ => ℤ) l 0 (fun b l' => a * b + ih l'))
    l₁ l₂

/-- The column `x` of the first `x + 1` rows of a table: the column of an upper triangular
factor without its trailing zeros. -/
def colUpTo (T : List (List ℤ)) (x : ℕ) : List ℤ := colOf (T.take (x + 1)) x

theorem length_colOf (T : List (List ℤ)) (x : ℕ) : (colOf T x).length = T.length := by
  induction T with
  | nil => rfl
  | cons r T ih => exact congrArg (· + 1) ih

theorem getD_colOf (T : List (List ℤ)) (x k : ℕ) : (colOf T x).getD k 0 = entry T k x := by
  induction T generalizing k with
  | nil => simp [colOf, entry]
  | cons r T ih =>
    cases k with
    | zero => simp [colOf, entry]
    | succ k =>
      change (colOf T x).getD k 0 = _
      rw [ih]
      simp [entry]

theorem dotZ_eq_sum (l₁ l₂ : List ℤ) (n : ℕ) (h₁ : l₁.length ≤ n) :
    dotZ l₁ l₂ = ∑ k ∈ range n, l₁.getD k 0 * l₂.getD k 0 := by
  induction l₁ generalizing l₂ n with
  | nil => simp [dotZ]
  | cons a l₁ ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h₁; omega⟩
    rw [Finset.sum_range_succ']
    cases l₂ with
    | nil => simp [dotZ]
    | cons b l₂ =>
      change a * b + dotZ l₁ l₂ = _
      rw [ih l₂ m (by simp at h₁; omega)]
      simp [add_comm]

theorem entry_take (T : List (List ℤ)) (m k x : ℕ) :
    entry (T.take m) k x = if k < m then entry T k x else 0 := by
  unfold entry
  by_cases h : k < m
  · simp [h]
  · simp [h]

/-! ### Sums over the half -/

theorem sum_half_eq_range (c : SmallCut) (n : ℕ)
    (hlt : ∀ h : c.data.cut.Half, code c h.1 < n)
    (honto : ∀ x, x < n → ∃ h : c.data.cut.Half, code c h.1 = x)
    (hinj : ∀ h₁ h₂ : c.data.cut.Half, code c h₁.1 = code c h₂.1 → h₁ = h₂)
    (f : ℕ → ℤ) : ∑ j : c.data.cut.Half, f (code c j.1) = ∑ y ∈ range n, f y := by
  rw [← Finset.sum_image (fun a _ b _ h => hinj a b h)]
  congr 1
  ext y
  simp only [mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨h, rfl⟩
    exact hlt h
  · exact honto y

/-! ### Gram parts -/

variable {U K : Type*} [Fintype K]

theorem gramReal_symm (R I : K → U → ℤ) (i j : U) : gramReal R I i j = gramReal R I j i := by
  unfold gramReal
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem gramImag_antisymm (R I : K → U → ℤ) (i j : U) :
    gramImag R I i j = -gramImag R I j i := by
  unfold gramImag
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ### Residual entries on codes -/

/-- The real residual entry at the codes `x`, `y`, with the Gram sum as dot products of
columns of the factor tables. -/
def resRCode (c : SmallCut) (a : Fin 2) (e : Fin 3) (x y : ℕ) : ℤ :=
  1000000000000 * entry (testRealTable c a e) x y -
    (dotZ (colUpTo (factorRealTable c a e) x) (colUpTo (factorRealTable c a e) y) +
      dotZ (colUpTo (factorImagTable c a e) x) (colUpTo (factorImagTable c a e) y))

/-- The imaginary residual entry at the codes `x`, `y`. -/
def resICode (c : SmallCut) (a : Fin 2) (e : Fin 3) (x y : ℕ) : ℤ :=
  1000000000000 * entry (testImagTable c a e) x y -
    (dotZ (colUpTo (factorRealTable c a e) x) (colUpTo (factorImagTable c a e) y) -
      dotZ (colUpTo (factorImagTable c a e) x) (colUpTo (factorRealTable c a e) y))

/-- The term of the residual row sum at the codes `x`, `y`. -/
def rowTermCode (c : SmallCut) (a : Fin 2) (e : Fin 3) (x y : ℕ) : ℤ :=
  ((((if x = y then shift c a e else 0) - resRCode c a e x y).natAbs : ℕ) : ℤ) +
    ((resICode c a e x y).natAbs : ℤ)

section Bridge

variable (c : SmallCut) (n : ℕ)
  (hlt : ∀ h : c.data.cut.Half, code c h.1 < n)
  (honto : ∀ x, x < n → ∃ h : c.data.cut.Half, code c h.1 = x)
  (hinj : ∀ h₁ h₂ : c.data.cut.Half, code c h₁.1 = code c h₂.1 → h₁ = h₂)

include hlt honto hinj

theorem sum_entry_mul (T₁ T₂ : List (List ℤ)) (h₁ : T₁.length = n)
    (hz₁ : ∀ k, k < n → ∀ x, x < k → entry T₁ k x = 0)
    (hz₂ : ∀ k, k < n → ∀ x, x < k → entry T₂ k x = 0) (x y : ℕ) :
    ∑ k : c.data.cut.Half, entry T₁ (code c k.1) x * entry T₂ (code c k.1) y =
      dotZ (colUpTo T₁ x) (colUpTo T₂ y) := by
  have h := sum_half_eq_range c n hlt honto hinj (fun k => entry T₁ k x * entry T₂ k y)
  have hl : (colUpTo T₁ x).length ≤ n := by
    rw [colUpTo, length_colOf, List.length_take, h₁]
    exact Nat.min_le_right _ _
  rw [h, dotZ_eq_sum _ _ n hl]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [mem_range] at hk
  have ht : ∀ (T : List (List ℤ)) z, (∀ k, k < n → ∀ x, x < k → entry T k x = 0) →
      (colUpTo T z).getD k 0 = entry T k z := by
    intro T z hz
    rw [colUpTo, getD_colOf, entry_take]
    split_ifs with hkz
    · rfl
    · exact (hz k hk z (by omega)).symm
  rw [ht T₁ x hz₁, ht T₂ y hz₂]

variable (hlen : ∀ a e, (factorRealTable c a e).length = n ∧ (factorImagTable c a e).length = n)
  (htri : ∀ a e, ∀ k, k < n → ∀ x, x < k →
    entry (factorRealTable c a e) k x = 0 ∧ entry (factorImagTable c a e) k x = 0)

include hlen htri

theorem residualReal_code (a : Fin 2) (e : Fin 3) (i j : c.data.cut.Half) :
    residualReal c a e i j = resRCode c a e (code c i.1) (code c j.1) := by
  unfold residualReal resRCode gramReal testReal factorReal factorImag atTable
  rw [Finset.sum_add_distrib,
    sum_entry_mul c n hlt honto hinj _ _ (hlen a e).1 (fun k hk x hx => (htri a e k hk x hx).1)
      (fun k hk x hx => (htri a e k hk x hx).1),
    sum_entry_mul c n hlt honto hinj _ _ (hlen a e).2 (fun k hk x hx => (htri a e k hk x hx).2)
      (fun k hk x hx => (htri a e k hk x hx).2)]

theorem residualImag_code (a : Fin 2) (e : Fin 3) (i j : c.data.cut.Half) :
    residualImag c a e i j = resICode c a e (code c i.1) (code c j.1) := by
  unfold residualImag resICode gramImag testImag factorReal factorImag atTable
  rw [Finset.sum_sub_distrib,
    sum_entry_mul c n hlt honto hinj _ _ (hlen a e).1 (fun k hk x hx => (htri a e k hk x hx).1)
      (fun k hk x hx => (htri a e k hk x hx).2),
    sum_entry_mul c n hlt honto hinj _ _ (hlen a e).2 (fun k hk x hx => (htri a e k hk x hx).2)
      (fun k hk x hx => (htri a e k hk x hx).1)]

theorem residualChecks_of
    (hsym : ∀ a e, ∀ x, x < n → ∀ y, y < n →
      entry (testRealTable c a e) x y = entry (testRealTable c a e) y x ∧
        entry (testImagTable c a e) x y = -entry (testImagTable c a e) y x)
    (hrow : ∀ a e, ∀ x, x < n → ∑ y ∈ range n, rowTermCode c a e x y ≤ shift c a e) :
    ResidualChecks c := by
  intro a e
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · unfold residualReal
    rw [gramReal_symm (factorReal c a e) (factorImag c a e) i j]
    simp only [testReal, atTable]
    rw [(hsym a e _ (hlt i) _ (hlt j)).1]
  · unfold residualImag
    rw [gramImag_antisymm (factorReal c a e) (factorImag c a e) i j]
    simp only [testImag, atTable]
    rw [(hsym a e _ (hlt i) _ (hlt j)).2]
    ring
  · have hterm : ∀ j, |(if i = j then shift c a e else 0) - residualReal c a e i j| +
        |residualImag c a e i j| = rowTermCode c a e (code c i.1) (code c j.1) := by
      intro j
      rw [residualReal_code c n hlt honto hinj hlen htri,
        residualImag_code c n hlt honto hinj hlen htri,
        rowTermCode, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      by_cases h : i = j
      · subst h
        simp
      · have h2 : code c i.1 ≠ code c j.1 := fun h' => h (hinj i j h')
        simp only [h, h2, ite_false]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    have h := sum_half_eq_range c n hlt honto hinj (rowTermCode c a e (code c i.1))
    rw [h]
    exact hrow a e _ (hlt i)

end Bridge

end Sarkozy.SpectralD.SmallMatrices
