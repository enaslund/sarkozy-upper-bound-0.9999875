module

public import Sarkozy.CancellationSteps.Paper

/-!
# Every prime below `P₄` is dispatched to `M₀`, a prefix atom, a middle piece or an upper band

`paper/sections/18_design.tex`, `def:record:parameters`(c) and `tab:ranges`.

A check of V1's dispatch of the primes (`Sarkozy.PartV.Parameters`):
* `prime_lt_P4_dispatch` (`Paper.lean`): every prime below `P₄` divides `M₀` or is a fixed
  coordinate (prefix, middle or upper), and not both;
* `middlePrime_mem_piece`: every middle prime lies in one of the 33 pieces `[X_i, X_{i+1})`;
* `upperPrime_mem_band`: every upper prime lies in one of the 310 bands (V1's `bandOf i` is
  `upperBands.getD i (0, 0)`).

The block partitions of the pieces and bands (`def:record:exact-blocks`, `def:record:upper-bands`)
are parameters in V1's files and are not checked here. `DensityCancellation` does not use them:
WP-FI's frame merges all the fixed coordinates into the single atom `none`.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset

/-- If consecutive intervals `[f i, g i)` tile `[f 0, g n)`, every point of `[f 0, g n)` lies in
one of them. -/
theorem exists_mem_tile {n : ℕ} (f g : Fin (n + 1) → ℕ)
    (hcons : ∀ i : Fin n, g i.castSucc = f i.succ) {x : ℕ} (h0 : f 0 ≤ x)
    (hn : x < g (Fin.last n)) : ∃ i, f i ≤ x ∧ x < g i := by
  classical
  have hne : (univ.filter fun i : Fin (n + 1) => f i ≤ x).Nonempty :=
    ⟨0, mem_filter.mpr ⟨mem_univ _, h0⟩⟩
  obtain ⟨i, hiS, himax⟩ : ∃ i ∈ univ.filter (fun i : Fin (n + 1) => f i ≤ x),
      ∀ k ∈ univ.filter (fun i : Fin (n + 1) => f i ≤ x), k ≤ i :=
    ⟨_, max'_mem _ hne, fun k hk => le_max' _ k hk⟩
  refine ⟨i, (mem_filter.mp hiS).2, ?_⟩
  by_cases hlast : i = Fin.last n
  · rw [hlast]
    exact hn
  · have hlt : i.val < n := by
      have h1 := i.isLt
      have h2 : i.val ≠ n := fun h => hlast (Fin.ext h)
      omega
    have hij : (⟨i.val, hlt⟩ : Fin n).castSucc = i := Fin.ext rfl
    rw [← hij, hcons ⟨i.val, hlt⟩]
    by_contra hge
    have hmem := himax _ (mem_filter.mpr ⟨mem_univ _, not_lt.mp hge⟩)
    have h3 : ((⟨i.val, hlt⟩ : Fin n).succ).val ≤ i.val := hmem
    simp only [Fin.val_succ] at h3
    omega

/-- **Every middle prime lies in one of the 33 middle pieces** `[X_i, X_{i+1})`
(`def:record:parameters`(c), `tab:record:middle-pieces`). -/
theorem middlePrime_mem_piece {x : ℕ} (hx : PartV.IsMiddlePrime x) :
    ∃ i : Fin 33, PartV.pieceStart i ≤ x ∧ x < PartV.pieceStop i := by
  have h0 : PartV.pieceStart 0 = PartV.Q3 := by
    unfold PartV.pieceStart PartV.pieceEnds PartV.Q3
    decide +kernel
  have hn : PartV.pieceStop (Fin.last 32) = PartV.P3 := by
    unfold PartV.pieceStop PartV.pieceEnds PartV.P3
    decide +kernel
  exact exists_mem_tile PartV.pieceStart PartV.pieceStop PartV.pieceStop_eq_pieceStart
    (h0 ▸ hx.2.2.1) (hn ▸ hx.2.2.2)

/-- The band `i` of `def:record:upper-bands`(a) (V1's `bandOf`). -/
def upperBand (i : Fin 310) : ℕ × ℕ := PartV.upperBands.getD i.val (0, 0)

/-- **Every upper prime lies in one of the 310 upper bands** (`def:record:parameters`(c),
`def:record:upper-bands`(a)). -/
theorem upperPrime_mem_band {x : ℕ} (hx : PartV.IsUpperPrime x) :
    ∃ i : Fin 310, (upperBand i).1 ≤ x ∧ x < (upperBand i).2 := by
  have hcons : ∀ i : Fin 309, (upperBand i.castSucc).2 = (upperBand i.succ).1 := by
    unfold upperBand PartV.upperBands PartV.bandsA PartV.bandsB PartV.bandsC PartV.bandsD
      PartV.bandsDExponents
    decide +kernel
  have h0 : (upperBand 0).1 = PartV.P3 := by
    unfold upperBand PartV.upperBands PartV.bandsA PartV.bandsB PartV.bandsC PartV.bandsD
      PartV.bandsDExponents PartV.P3
    decide +kernel
  have hn : (upperBand (Fin.last 309)).2 = PartV.P4 := by
    unfold upperBand PartV.upperBands PartV.bandsA PartV.bandsB PartV.bandsC PartV.bandsD
      PartV.bandsDExponents PartV.P4
    decide +kernel
  exact exists_mem_tile (fun i => (upperBand i).1) (fun i => (upperBand i).2) hcons
    (h0 ▸ hx.2.2.1) (hn ▸ hx.2.2.2)

end Sarkozy.CancellationSteps
