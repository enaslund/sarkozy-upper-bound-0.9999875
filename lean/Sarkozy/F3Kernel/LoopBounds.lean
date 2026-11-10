module

public import Sarkozy.F3Kernel.FixedPoint

/-!
# Real product bounds for accepted certificate loops

An accepted loop preserves an upper bound on the product of its real factors, provided the
factor-table entries bound those factors. The signature sequence and the switch between cover
and integrated vertices are exactly those read and computed by the checker. Identifying these
signatures with the graph-theoretic counts is a separate step.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def firstVertex (r : ℕ) : ℕ := Nat.land r 63

def signature (T u : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.shiftLeft u 6)) 127

def factorEntry (G : Consts) (table s : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight table (G.W * s)) (maskW G)

/-- The real product over the integrated part of a packed order. -/
noncomputable def integratedProd (G : Consts) (m : ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 1
  | n + 1, r, T =>
      m (signature T (firstVertex r)) *
        integratedProd G m n (Nat.shiftRight r 6) (T + adj64 G (firstVertex r))

theorem integratedProd_nonneg (G : Consts) {m : ℕ → ℝ} (hm : ∀ s, 0 ≤ m s)
    (n r T : ℕ) : 0 ≤ integratedProd G m n r T := by
  induction n generalizing r T with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hm _) (ih _ _)

/-- One unfolding of the checker's integrated loop, in terms of the arithmetic interface. -/
theorem uLoop_succ (G : Consts) (n r mask T acc : ℕ) :
    uLoop G (n + 1) r mask T acc =
      (bif bit mask (firstVertex r) then none else
        bif Nat.ble (signature T (firstVertex r)) G.d then
          uLoop G n (Nat.shiftRight r 6)
            (Nat.lor mask (Nat.shiftLeft 1 (firstVertex r)))
            (T + adj64 G (firstVertex r))
            (mul64 acc (factorEntry G G.FT (signature T (firstVertex r))))
        else none) := rfl

/-- An accepted integrated loop gives an upper bound for the product of the intended factors. -/
theorem uLoop_bound (G : Consts) {m : ℕ → ℝ} (hm : ∀ s, 0 ≤ m s)
    (hFT : ∀ s ≤ G.d, m s ≤ value64 (factorEntry G G.FT s))
    {n r mask T acc rest out : ℕ} (h : uLoop G n r mask T acc = some (rest, out))
    {x : ℝ} (hx : 0 ≤ x) (hacc : x ≤ value64 acc) :
    x * integratedProd G m n r T ≤ value64 out := by
  induction n generalizing r mask T acc x with
  | zero =>
      change (bif Nat.beq mask FULL64 then some (r, acc) else none) = some (rest, out) at h
      simp only [Bool.cond_eq_ite] at h
      split at h
      · cases h
        simpa only [integratedProd, mul_one] using hacc
      · cases h
  | succ n ih =>
      rw [uLoop_succ] at h
      simp only [Bool.cond_eq_ite] at h
      split at h
      · cases h
      next =>
        split at h
        next hs =>
          have hs' : signature T (firstVertex r) ≤ G.d := by simpa using hs
          have hb := mul64_sound hx (hm _) hacc (hFT _ hs')
          have hi := ih h (mul_nonneg hx (hm _)) hb
          simpa only [integratedProd, mul_assoc] using hi
        next => cases h

/-- The real product for a side: cover factors first, then the witness update, then the
integrated factors. Witness vertices themselves contribute to the exponent, not this product. -/
noncomputable def sideProd (G : Consts) (m rho : ℕ → ℝ) (cmask wl k hw : ℕ) :
    ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 1
  | n + 1, r, T =>
      if bit cmask (firstVertex r) then
        rho (signature T (firstVertex r)) *
          sideProd G m rho cmask wl k hw n (Nat.shiftRight r 6)
            (T + adj64 G (firstVertex r))
      else integratedProd G m (n + 1) r (witSwitch G k wl hw T).2

theorem sideProd_nonneg (G : Consts) {m rho : ℕ → ℝ}
    (hm : ∀ s, 0 ≤ m s) (hr : ∀ s, 0 ≤ rho s) (cmask wl k hw n r T : ℕ) :
    0 ≤ sideProd G m rho cmask wl k hw n r T := by
  induction n generalizing r T with
  | zero => exact zero_le_one
  | succ n ih =>
      simp only [sideProd]
      split
      · exact mul_nonneg (hr _) (ih _ _)
      · exact integratedProd_nonneg G hm _ _ _

theorem cLoop_succ (G : Consts) (FTr cmask wl k hw n r mask T acc : ℕ) :
    cLoop G FTr cmask wl k hw (n + 1) r mask T acc =
      (bif bit cmask (firstVertex r) then
        bif bit mask (firstVertex r) then none else
          bif Nat.ble (signature T (firstVertex r)) G.d then
            cLoop G FTr cmask wl k hw n (Nat.shiftRight r 6)
              (Nat.lor mask (Nat.shiftLeft 1 (firstVertex r)))
              (T + adj64 G (firstVertex r))
              (mul64 acc (factorEntry G FTr (signature T (firstVertex r))))
          else none
      else bif Nat.beq (Nat.land cmask mask) cmask then
        match uLoop G (n + 1) r mask (witSwitch G k wl hw T).2 acc with
        | none => none
        | some (r1, acc1) => some (r1, (witSwitch G k wl hw T).1, acc1)
      else none) := rfl

/-- The cover loop and its transition to the integrated loop preserve the real upper bound. -/
theorem cLoop_bound (G : Consts) {m rho : ℕ → ℝ}
    (hm : ∀ s, 0 ≤ m s) (hr : ∀ s, 0 ≤ rho s)
    (hFT : ∀ s ≤ G.d, m s ≤ value64 (factorEntry G G.FT s))
    {FTr : ℕ} (hFR : ∀ s ≤ G.d, rho s ≤ value64 (factorEntry G FTr s))
    {cmask wl k hw n r mask T acc rest exponent out : ℕ}
    (h : cLoop G FTr cmask wl k hw n r mask T acc = some (rest, exponent, out))
    {x : ℝ} (hx : 0 ≤ x) (hacc : x ≤ value64 acc) :
    x * sideProd G m rho cmask wl k hw n r T ≤ value64 out := by
  induction n generalizing r mask T acc x with
  | zero =>
      change (bif Nat.beq mask FULL64 then some (r, (witSwitch G k wl hw T).1, acc)
        else none) = some (rest, exponent, out) at h
      simp only [Bool.cond_eq_ite] at h
      split at h
      · cases h
        simpa only [sideProd, mul_one] using hacc
      · cases h
  | succ n ih =>
      rw [cLoop_succ] at h
      simp only [Bool.cond_eq_ite] at h
      split at h
      next hc =>
        split at h
        · cases h
        next =>
          split at h
          next hs =>
            have hs' : signature T (firstVertex r) ≤ G.d := by simpa using hs
            have hb := mul64_sound hx (hr _) hacc (hFR _ hs')
            have hi := ih h (mul_nonneg hx (hr _)) hb
            simpa only [sideProd, hc, ite_true, mul_assoc] using hi
          next => cases h
      next hc =>
        split at h
        next =>
          split at h
          · cases h
          next r1 acc1 hu =>
            cases h
            simpa only [sideProd, hc, Bool.false_eq_true, ite_false] using
              uLoop_bound G hm hFT hu hx hacc
        next => cases h

end Sarkozy.F3Kernel
