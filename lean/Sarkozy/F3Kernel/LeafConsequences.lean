module

public import Sarkozy.F3Kernel.LeafTrace
public import Sarkozy.F3Kernel.ComponentTables
public import Sarkozy.F3Kernel.GraphData

/-!
# Mathematical consequences of an accepted leaf

An actual successful `leafCheck` now gives the paper's witness and cover conditions, the
correct number of two-vertex components, and a real upper bound for the product along the
computed signature sequence. The remaining bridges are the order conditions and the equality
of the computed signatures and exponent with the graph-theoretic quantities in `leafCoef`.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Sarkozy.Extraction Sarkozy.ExtractionK

namespace LeafTrace

variable {G : Consts} {c : Cyl} {rec k value free : ℕ} (t : LeafTrace G c rec k value free)

def witness : Fin k → Fin 36 × Fin 36 := witnessOf t.maskX t.maskY

theorem isWitness (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am)) :
    IsWitness (decM G.EM) (decM c.pm) (decM c.am) t.witness :=
  isWitness_of_checks G c hclass t.maskX t.maskY t.rectFree t.rectangle

theorem isCover (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am)) :
    IsCover (decM G.EM) (decM c.pm) (decM c.am) t.witness
      (decV (Record.cx rec)) (decV (Record.cy rec)) :=
  isCover_of_checks G c hclass t.maskX t.maskY (land_FULL36_lt _) (land_FULL36_lt _)
    t.disjX t.disjY t.cover

theorem pattern_eq (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am)) :
    Components.rectangle k t.pattern = witnessIdx (decM c.pm) t.witness := by
  rw [← witnessIdx_of_rectPat t.maskX t.maskY t.rectangle,
    witnessIdx_rectangleMask G c.pm t.maskX t.maskY hclass.1]
  rfl

theorem pattern_lt : t.pattern < 2 ^ (k * k) := rectPat_lt t.rectangle

theorem pattern_diagZero : Components.DiagZero k t.pattern := rectPat_diagonal_zero t.rectangle

/-- The actual exponent used by the accepted checker run. -/
noncomputable def exponent : ℕ :=
  leafExponent (Components.entry (componentTable G k) t.pattern)
    (hSum (freeRows G c) k (Record.xs rec)) (hSum (freeCols G c) k (Record.ys rec)) t.eX t.eZ

/-- The intended factors evaluated at the checker's signature sequence on both sides. -/
noncomputable def product (m rho : ℕ → ℝ) : ℝ :=
  sideProd G m rho (Record.cx rec) (Record.xs rec) k
    (hSum (freeRows G c) k (Record.xs rec)) (36 - k) (Record.order rec) (freeRows G c) *
  sideProd G m rho (Record.cy rec) (Record.ys rec) k
    (hSum (freeCols G c) k (Record.ys rec)) (36 - k) t.rest (freeCols G c)

/-- End-to-end arithmetic bound for an actual accepted leaf, assuming certified factor tables. -/
theorem product_bound {m rho : ℕ → ℝ} (hm : ∀ s, 0 ≤ m s) (hr : ∀ s, 0 ≤ rho s)
    (hFT : ∀ s ≤ G.d, m s ≤ value64 (factorEntry G G.FT s))
    (hFR : ∀ s ≤ G.d, rho s ≤ value64 (factorEntry G (rhoTable G) s))
    (hsq : Real.sqrt 2 ≤ value64 G.SQ2) :
    Real.sqrt ((2 : ℝ) ^ t.exponent) * t.product m rho ≤ value64 value := by
  have hx := cLoop_bound G hm hr hFT hFR t.loopX (x := 1) (by norm_num)
    (by rw [value64_one])
  rw [one_mul] at hx
  have hy := cLoop_bound G hm hr hFT hFR t.loopY
    (sideProd_nonneg G hm hr _ _ _ _ _ _ _) hx
  have hp : 0 ≤ t.product m rho :=
    mul_nonneg (sideProd_nonneg G hm hr _ _ _ _ _ _ _)
      (sideProd_nonneg G hm hr _ _ _ _ _ _ _)
  exact (pow64_sound (ex := t.exponent) hp hy hsq).trans_eq (congrArg value64 t.amount.symm)

end LeafTrace

theorem LL20_validEntry {k p : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4)
    (hp : p < 2 ^ (k * k)) (hd : Components.DiagZero k p) :
    Components.ValidEntry (componentTable LL20 k) k p := by
  rcases hk with rfl | rfl | rfl
  · exact Components.LL20_table_two ⟨p, hp⟩ hd
  · exact Components.LL20_table_three ⟨p, hp⟩ hd
  · exact Components.LL20_table_four ⟨p, hp⟩ hd

theorem LL22_validEntry {k p : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4)
    (hp : p < 2 ^ (k * k)) (hd : Components.DiagZero k p) :
    Components.ValidEntry (componentTable LL22 k) k p := by
  have he : componentTable LL22 k = componentTable LL20 k := by
    simp only [componentTable, Components.tables_eq.1, Components.tables_eq.2.1,
      Components.tables_eq.2.2]
  rw [he]
  exact LL20_validEntry hk hp hd

theorem LeafTrace.components {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free)
    (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am))
    (ht : Components.ValidEntry (componentTable G k) k t.pattern) :
    (∀ i, (twoCycleComponent (witnessIdx (decM c.pm) t.witness) i).card ≤ 2) ∧
      Components.entry (componentTable G k) t.pattern =
        1 + twoCycleCount (witnessIdx (decM c.pm) t.witness) := by
  simpa only [t.pattern_eq hclass] using Components.entry_sound ht t.component

theorem LeafTrace.LL20_components {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace LL20 c rec k value free)
    (hclass : IsClassDatum (decM LL20.EM) (decM c.pm, decM c.am)) :
    (∀ i, (twoCycleComponent (witnessIdx (decM c.pm) t.witness) i).card ≤ 2) ∧
      Components.entry (componentTable LL20 k) t.pattern =
        1 + twoCycleCount (witnessIdx (decM c.pm) t.witness) :=
  t.components hclass (LL20_validEntry t.admissible t.pattern_lt t.pattern_diagZero)

theorem LeafTrace.LL22_components {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace LL22 c rec k value free)
    (hclass : IsClassDatum (decM LL22.EM) (decM c.pm, decM c.am)) :
    (∀ i, (twoCycleComponent (witnessIdx (decM c.pm) t.witness) i).card ≤ 2) ∧
      Components.entry (componentTable LL22 k) t.pattern =
        1 + twoCycleCount (witnessIdx (decM c.pm) t.witness) :=
  t.components hclass (LL22_validEntry t.admissible t.pattern_lt t.pattern_diagZero)

end Sarkozy.F3Kernel
