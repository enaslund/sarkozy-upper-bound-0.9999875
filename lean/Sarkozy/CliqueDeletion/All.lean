module

public import Sarkozy.CliqueDeletion.Event
public import Sarkozy.CliqueDeletion.Prefix
public import Sarkozy.CliqueDeletion.Paper
public import Sarkozy.CliqueDeletion.Agreement
public import Sarkozy.CliqueDeletion.Price
public import Sarkozy.CliqueDeletion.MainFinal

@[expose] public section

/-!
# C10: the square-clique deletions (`lem:frontier:iidenergy`(ii), `lem:frontier:iidlocal`(iv),(v))

* `Event` — `DeletionInputs` from the restriction of a law to an event (`ofEvent`); the query
  event `queryEq` and its `ι`-closure `symQueryEq`.
* `Prefix` — the prefix law on `ℤ/p^{2𝔪}`: invariance under `ι` and the translations, the square
  property of its support, the masses of the query events (`≤ 6·2^{-𝔪}`, `≤ 12·2^{-𝔪}`).
* `Paper` — the paper's square-clique atoms: **`cliqueDeletion`**, **`paperCliqueDeletion`**
  (B2's and K1's clique field, proved), `ω ≤ 12·2^{-𝔪}`.
* `Agreement` — for `p < 2¹⁶` the deleted measure is exactly the paper's `λ^ex_p`.
* `Price` — `∑_p ω_p q_p^{2a_T} ≤ 12·2^{-534}` (`lem:frontier:iidenergy`(iii),(iv)).
* `MainFinal` — K1's field `cliqueK1`, `comparisonPartsOfProvedClique`, and its clique price.
-/
