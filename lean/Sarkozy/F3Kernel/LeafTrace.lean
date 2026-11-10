module

public import Sarkozy.F3Kernel.WitnessChecks
public import Sarkozy.F3Kernel.LoopBounds

/-!
# Extracting the checks performed by an accepted leaf

`leafCheck_trace` exposes the successful checks and intermediate results of the actual
certificate checker. This connects its executable control flow to the separate semantic
proofs for witnesses, covers, components, and products.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

namespace Record

def k (r : ℕ) : ℕ := Nat.land r 3 + 2
def xs (r : ℕ) : ℕ := Nat.land (Nat.shiftRight r 2) 16777215
def ys (r : ℕ) : ℕ := Nat.land (Nat.shiftRight r 26) 16777215
def cx (r : ℕ) : ℕ := Nat.land (Nat.shiftRight r 50) FULL36
def cy (r : ℕ) : ℕ := Nat.land (Nat.shiftRight r 86) FULL36
def order (r : ℕ) : ℕ := Nat.shiftRight r 122

end Record

def componentTable (G : Consts) (k : ℕ) : ℕ :=
  bif Nat.beq k 2 then G.SCC2 else bif Nat.beq k 3 then G.SCC3 else G.SCC4

theorem componentTable_eq (G : Consts) (k : ℕ) : componentTable G k =
    (bif Nat.beq k 2 then G.SCC2 else bif Nat.beq k 3 then G.SCC3 else G.SCC4) := rfl

def freeRows (G : Consts) (c : Cyl) : ℕ := swar (Nat.xor G.EM (Nat.lor c.pm c.am))
def freeCols (G : Consts) (c : Cyl) : ℕ := swar (Nat.xor G.ET (Nat.lor c.pt c.qt))
def rhoTable (G : Consts) : ℕ := Nat.shiftRight G.FT (G.W * (G.d + 1))

def leafExponent (ent fV fW eX eZ : ℕ) : ℕ :=
  2 * (ent - 1) + (fV + fW) + (eX + eZ)

/-- The intermediate values and proved checks of a successful leaf evaluation. -/
structure LeafTrace (G : Consts) (c : Cyl) (rec k value free : ℕ) where
  V : ℕ
  W : ℕ
  pattern : ℕ
  rest : ℕ
  eX : ℕ
  eZ : ℕ
  accX : ℕ
  accZ : ℕ
  size : k = Record.k rec
  admissible : k = 2 ∨ k = 3 ∨ k = 4
  maskX : vmask k (Record.xs rec) 0 = some V
  maskY : vmask k (Record.ys rec) 0 = some W
  rectFree : Nat.land (rectangleMask G V W) (Nat.xor G.EM (Nat.lor c.pm c.am)) = 0
  disjX : Nat.land (Record.cx rec) V = 0
  disjY : Nat.land (Record.cy rec) W = 0
  cover : Nat.land (Nat.xor G.EM c.am) (coverMask G V W (Record.cx rec) (Record.cy rec)) =
    Nat.xor G.EM c.am
  rectangle : rectPat (Nat.land (rectangleMask G V W) c.pm)
    (Record.xs rec) (Record.ys rec) k (k * k) 0 = some pattern
  component : Components.entry (componentTable G k) pattern ≠ 0
  loopX : cLoop G (rhoTable G) (Record.cx rec) (Record.xs rec) k
    (hSum (freeRows G c) k (Record.xs rec)) (36 - k) (Record.order rec)
    (Nat.lor V (FULL64 - FULL36)) (freeRows G c) (2 ^ 64) = some (rest, eX, accX)
  loopY : cLoop G (rhoTable G) (Record.cy rec) (Record.ys rec) k
    (hSum (freeCols G c) k (Record.ys rec)) (36 - k) rest
    (Nat.lor W (FULL64 - FULL36)) (freeCols G c) accX = some (0, eZ, accZ)
  amount : value = pow64 G.SQ2
    (leafExponent (Components.entry (componentTable G k) pattern)
      (hSum (freeRows G c) k (Record.xs rec)) (hSum (freeCols G c) k (Record.ys rec)) eX eZ) accZ
  freeCount : free = Nat.land (Nat.shiftRight (freeRows G c * LANE0) 2240) FULL64

theorem leafCheck_trace {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (h : leafCheck G c rec = some (k, value, free)) :
    Nonempty (LeafTrace G c rec k value free) := by
  unfold leafCheck at h
  simp only [Bool.cond_eq_ite] at h
  generalize htable : (if Nat.beq (Nat.land rec 3 + 2) 2 = true then G.SCC2
    else if Nat.beq (Nat.land rec 3 + 2) 3 = true then G.SCC3 else G.SCC4) = table at h
  have htable' : componentTable G (Record.k rec) = table := by
    simpa only [componentTable, Record.k, Bool.cond_eq_ite] using htable
  split at h
  next V W hV hW =>
    split at h
    · cases h
    next hk =>
      split at h
      next hrect =>
        split at h
        next hcover =>
          split at h
          · cases h
          next pat hpat =>
            split at h
            · cases h
            next hent =>
              split at h
              · cases h
              next r1 eX accX hX =>
                split at h
                · cases h
                next r2 eZ accZ hY =>
                  split at h
                  next hr =>
                    have hr' : r2 = 0 := by simpa using hr
                    subst r2
                    cases h
                    have hrect' : Nat.land (rectangleMask G V W)
                        (Nat.xor G.EM (Nat.lor c.pm c.am)) = 0 ∧
                        Nat.land (Record.cx rec) V = 0 ∧ Nat.land (Record.cy rec) W = 0 := by
                      simp only [Bool.and_eq_true, Nat.beq_eq, and_assoc] at hrect
                      exact hrect
                    refine ⟨{
                      V := V, W := W, pattern := pat, rest := r1, eX := eX, eZ := eZ,
                      accX := accX, accZ := accZ, size := rfl,
                      admissible := ?_, maskX := hV, maskY := hW,
                      rectFree := hrect'.1, disjX := hrect'.2.1, disjY := hrect'.2.2,
                      cover := ?_, rectangle := hpat, component := ?_,
                      loopX := hX, loopY := hY, amount := ?_, freeCount := rfl }⟩
                    · have hn : Nat.land rec 3 < 4 := by
                        change rec &&& (2 ^ 2 - 1) < 4
                        rw [Nat.and_two_pow_sub_one_eq_mod]
                        exact Nat.mod_lt _ (by decide)
                      have hk' : Nat.land rec 3 ≠ 3 := by simpa using hk
                      change Nat.land rec 3 + 2 = 2 ∨ Nat.land rec 3 + 2 = 3 ∨
                        Nat.land rec 3 + 2 = 4
                      omega
                    · simp only [Nat.beq_eq] at hcover
                      exact hcover
                    · change Components.entry (componentTable G (Record.k rec)) pat ≠ 0
                      rw [htable']
                      change Nat.land (Nat.shiftRight table (Nat.mul 2 pat)) 3 ≠ 0
                      simpa only [Nat.beq_eq] using hent
                    · unfold pow64 leafExponent Components.entry
                      rw [show componentTable G (Nat.land rec 3 + 2) = table from htable']
                      simp only [Nat.beq_eq]
                      congr 1
                  next => cases h
        next => cases h
      next => cases h
  next => cases h

end Sarkozy.F3Kernel
