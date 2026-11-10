module

public import Sarkozy.TailCorr.Schur

@[expose] public section

/-!
# Counting injective row configurations

`paper/sections/12_labellings.tex` (the labelling counts of a graph without edges, where every
injective labelling is admissible); used for the matching rows of the field type `E`
(`TailCorr.MatchingE`).

For rows `x, b, y : Q → F` with `|Q| = k` and `|F| = N`:
* `card_avoid`: the injective `y` avoiding a set `R` number `(N - |R|)_k` (falling factorial);
* `inj2_iff`, `inj3_iff`: joint injectivity of `(x, b)` and of `(x, b, y)` row by row;
* `card_inj2`: `#{x : (x, b) injective} = (N - k)_k` for injective `b`;
* `card_inj3`: `#{y : (x, b, y) injective} = (N - 2k)_k` for injective `(x, b)`;
* `descFactorial_ratio`: `(a + k)_j ≤ (1 + k/(a - k))^j (a)_j` for `j ≤ k < a`.
-/

namespace Sarkozy.TailCorr

open Finset

variable {F : Type*} [Fintype F] [DecidableEq F] {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- `(x_0, …, x_{n-1})` is jointly injective: `(i, q) ↦ x_i(q)` is injective. -/
def JInj {n : ℕ} (ω : Fin n → Q → F) : Prop := Function.Injective fun z : Fin n × Q => ω z.1 z.2

instance {n : ℕ} (ω : Fin n → Q → F) : Decidable (JInj ω) := by
  unfold JInj
  infer_instance

/-- **Injective rows avoiding a set**: `#{y : Q → F injective, y(Q) ∩ R = ∅} = (N - |R|)_k`. -/
theorem card_avoid (R : Finset F) :
    (univ.filter fun y : Q → F => Function.Injective y ∧ ∀ q, y q ∉ R).card =
      (Fintype.card F - R.card).descFactorial (Fintype.card Q) := by
  classical
  rw [← Fintype.card_subtype]
  have e : {y : Q → F // Function.Injective y ∧ ∀ q, y q ∉ R} ≃ (Q ↪ {z : F // z ∉ R}) :=
    { toFun := fun y => ⟨fun q => ⟨y.1 q, y.2.2 q⟩, fun a b h => y.2.1 (congrArg Subtype.val h)⟩
      invFun := fun f => ⟨fun q => (f q).1, fun a b h => f.injective (Subtype.ext h),
        fun q => (f q).2⟩
      left_inv := fun y => rfl
      right_inv := fun f => rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq]
  congr 1
  rw [Fintype.card_subtype, ← Finset.card_compl]
  congr 1
  ext z
  simp

omit [Fintype F] [DecidableEq Q] in
/-- `(x, b)` is jointly injective iff `b` is injective, `x` is injective and `x` avoids `b(Q)`. -/
theorem inj2_iff (x b : Q → F) :
    JInj ![x, b] ↔ Function.Injective b ∧ (Function.Injective x ∧ ∀ q, x q ∉ univ.image b) := by
  constructor
  · intro h
    refine ⟨fun q q' hq => ?_, fun q q' hq => ?_, fun q hq => ?_⟩
    · have := h (a₁ := ((1 : Fin 2), q)) (a₂ := ((1 : Fin 2), q')) hq
      exact (Prod.mk.inj this).2
    · have := h (a₁ := ((0 : Fin 2), q)) (a₂ := ((0 : Fin 2), q')) hq
      exact (Prod.mk.inj this).2
    · obtain ⟨q', -, hq'⟩ := mem_image.mp hq
      have := h (a₁ := ((0 : Fin 2), q)) (a₂ := ((1 : Fin 2), q')) hq'.symm
      exact absurd (Prod.mk.inj this).1 (by decide)
  · rintro ⟨hb, hx, hxb⟩ ⟨i, q⟩ ⟨j, q'⟩ h
    simp only at h
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at h
      rw [hx h]
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one] at h
      exact absurd (mem_image.mpr ⟨q', mem_univ _, h.symm⟩) (hxb q)
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Fin.zero_eta,
        Matrix.cons_val_zero] at h
      exact absurd (mem_image.mpr ⟨q, mem_univ _, h⟩) (hxb q')
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one] at h
      rw [hb h]

/-- The values of the rows `(x, b)`. -/
def rng2 (x b : Q → F) : Finset F := univ.image fun z : Fin 2 × Q => ![x, b] z.1 z.2

omit [Fintype F] [DecidableEq Q] in
/-- `(x, b, y)` is jointly injective iff `(x, b)` is, `y` is injective and `y` avoids the
values of `(x, b)`. -/
theorem inj3_iff (x b y : Q → F) :
    JInj ![x, b, y] ↔ JInj ![x, b] ∧ (Function.Injective y ∧ ∀ q, y q ∉ rng2 x b) := by
  constructor
  · intro h
    refine ⟨fun ⟨i, q⟩ ⟨j, q'⟩ hq => ?_, fun q q' hq => ?_, fun q hq => ?_⟩
    · have := h (a₁ := (i.castSucc, q)) (a₂ := (j.castSucc, q')) (by
        simp only
        fin_cases i <;> fin_cases j <;> exact hq)
      obtain ⟨h1, h2⟩ := Prod.mk.inj this
      exact Prod.ext (Fin.castSucc_injective _ h1) h2
    · have := h (a₁ := ((2 : Fin 3), q)) (a₂ := ((2 : Fin 3), q')) hq
      exact (Prod.mk.inj this).2
    · obtain ⟨⟨i, q'⟩, -, hq'⟩ := mem_image.mp hq
      have := h (a₁ := ((2 : Fin 3), q)) (a₂ := (i.castSucc, q')) (by
        simp only at hq' ⊢
        fin_cases i <;> exact hq'.symm)
      have h1 := (Prod.mk.inj this).1
      fin_cases i <;> exact absurd h1 (by decide)
  · rintro ⟨hxb, hy, hyr⟩ ⟨i, q⟩ ⟨j, q'⟩ h
    simp only at h
    have key : ∀ (i : Fin 2) (q : Q), ![x, b, y] i.castSucc q = ![x, b] i q := by
      intro i q
      fin_cases i <;> rfl
    have mem : ∀ (i : Fin 2) (q : Q), ![x, b, y] i.castSucc q ∈ rng2 x b := by
      intro i q
      rw [key]
      exact mem_image.mpr ⟨(i, q), mem_univ _, rfl⟩
    have last : ∀ q : Q, ![x, b, y] (Fin.last 2) q = y q := fun _ => rfl
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        rw [last, last] at h
        rw [hy h]
      | cast j =>
        rw [last] at h
        exact absurd (h ▸ mem j q') (hyr q)
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [last] at h
        exact absurd (h.symm ▸ mem i q) (hyr q')
      | cast j =>
        rw [key, key] at h
        have := hxb (a₁ := (i, q)) (a₂ := (j, q')) h
        obtain ⟨h1, h2⟩ := Prod.mk.inj this
        rw [h1, h2]

omit [Fintype F] [DecidableEq Q] in
/-- The values of jointly injective `(x, b)` number `2k`. -/
theorem card_rng2 {x b : Q → F} (h : JInj ![x, b]) : (rng2 x b).card = 2 * Fintype.card Q := by
  unfold rng2
  rw [card_image_of_injective _ h, card_univ, Fintype.card_prod, Fintype.card_fin]

/-- **`#{x : (x, b) injective} = (N - k)_k`** for injective `b`. -/
theorem card_inj2 {b : Q → F} (hb : Function.Injective b) :
    (univ.filter fun x : Q → F => JInj ![x, b]).card =
      (Fintype.card F - Fintype.card Q).descFactorial (Fintype.card Q) := by
  have e : (univ.filter fun x : Q → F => JInj ![x, b]) =
      univ.filter fun x : Q → F => Function.Injective x ∧ ∀ q, x q ∉ univ.image b := by
    ext x
    simp only [mem_filter, mem_univ, true_and, inj2_iff, hb]
  rw [e, card_avoid, card_image_of_injective _ hb, card_univ]

/-- **`#{y : (x, b, y) injective} = (N - 2k)_k`** for jointly injective `(x, b)`. -/
theorem card_inj3 {x b : Q → F} (h : JInj ![x, b]) :
    (univ.filter fun y : Q → F => JInj ![x, b, y]).card =
      (Fintype.card F - 2 * Fintype.card Q).descFactorial (Fintype.card Q) := by
  have e : (univ.filter fun y : Q → F => JInj ![x, b, y]) =
      univ.filter fun y : Q → F => Function.Injective y ∧ ∀ q, y q ∉ rng2 x b := by
    ext y
    simp only [mem_filter, mem_univ, true_and, inj3_iff, h]
  rw [e, card_avoid, card_rng2 h]

omit [Fintype F] [DecidableEq F] [Fintype Q] [DecidableEq Q] in
/-- `(x, b, y)` injective iff `(y, b, x)` injective. -/
theorem inj3_swap (x b y : Q → F) : JInj ![x, b, y] ↔ JInj ![y, b, x] := by
  have key : ∀ x y : Q → F, JInj ![x, b, y] → JInj ![y, b, x] := by
    intro x y h ⟨i, q⟩ ⟨j, q'⟩ hij
    have := h (a₁ := (Equiv.swap (0 : Fin 3) 2 i, q)) (a₂ := (Equiv.swap (0 : Fin 3) 2 j, q')) (by
      simp only at hij ⊢
      fin_cases i <;> fin_cases j <;> exact hij)
    obtain ⟨h1, h2⟩ := Prod.mk.inj this
    exact Prod.ext ((Equiv.swap (0 : Fin 3) 2).injective h1) h2
  exact ⟨key x y, key y x⟩

omit [Fintype F] [DecidableEq Q] in
/-- `(x, b, y)` injective implies `(y, b)` injective. -/
theorem inj2_of_inj3 {x b y : Q → F} (h : JInj ![x, b, y]) : JInj ![y, b] :=
  ((inj3_iff y b x).mp ((inj3_swap x b y).mp h)).1

/-! ## The falling-factorial ratio -/

/-- **`(a + k)_j ≤ (1 + k/(a - k))^j (a)_j`** for `j ≤ k < a`. -/
theorem descFactorial_ratio {a k : ℕ} (hka : k < a) :
    ∀ j : ℕ, j ≤ k → ((a + k).descFactorial j : ℝ) ≤
      (1 + (k : ℝ) / ((a : ℝ) - k)) ^ j * (a.descFactorial j : ℝ)
  | 0, _ => by simp
  | j + 1, hj => by
      have ih := descFactorial_ratio hka j (Nat.le_of_succ_le hj)
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul, pow_succ]
      have hja : j ≤ a := by omega
      have hjak : j ≤ a + k := by omega
      rw [Nat.cast_sub hjak, Nat.cast_sub hja, Nat.cast_add]
      have hak : (0 : ℝ) < (a : ℝ) - k := by
        have : (k : ℝ) < a := by exact_mod_cast hka
        linarith
      have hjk : (j : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_succ_le hj)
      have haj : (0 : ℝ) ≤ (a : ℝ) - j := by
        have : (j : ℝ) ≤ a := by exact_mod_cast hja
        linarith
      have hstep : (a : ℝ) + k - j ≤ (1 + (k : ℝ) / ((a : ℝ) - k)) * ((a : ℝ) - j) := by
        have h1 : (k : ℝ) ≤ (k : ℝ) / ((a : ℝ) - k) * ((a : ℝ) - j) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hak]
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
        nlinarith
      have hD : (0 : ℝ) ≤ ((a + k).descFactorial j : ℝ) := Nat.cast_nonneg _
      have hpow : (0 : ℝ) ≤ (1 + (k : ℝ) / ((a : ℝ) - k)) ^ j :=
        pow_nonneg (by positivity) j
      calc ((a : ℝ) + k - j) * ((a + k).descFactorial j : ℝ)
          ≤ ((1 + (k : ℝ) / ((a : ℝ) - k)) * ((a : ℝ) - j)) *
              ((1 + (k : ℝ) / ((a : ℝ) - k)) ^ j * (a.descFactorial j : ℝ)) :=
            mul_le_mul hstep ih hD (mul_nonneg (by positivity) haj)
        _ = (1 + (k : ℝ) / ((a : ℝ) - k)) ^ j * (1 + (k : ℝ) / ((a : ℝ) - k)) *
              (((a : ℝ) - j) * (a.descFactorial j : ℝ)) := by ring

end Sarkozy.TailCorr
