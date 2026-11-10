module

public import Sarkozy.CompSharp.Numeric
public import Sarkozy.CompSharp.Form
public import Sarkozy.CompSharp.Paper
public import Sarkozy.CompSharp.FoldGen
public import Sarkozy.CompSharp.Constructor
public import Sarkozy.CompSharp.Sanity

/-!
# C38: the component norms of `prop:signed-bounds`(c), Step 1, at `34 r + 1000 q` (umbrella)

* `Numeric`: the numerical step of SD2's separable Paley + Schur argument, `CompNumeric δ`;
  `compNumeric_34` (`34/s + 1000/s²`), `compNumeric_35`, `compNumeric_38`.
* `Form`: `comp_form_of`, `comp_centred_of` (SD2's proof with the numerical step abstracted);
  `comp_centred34`, `comp_centred35`, `comp_centred38`.
* `Paper`: `comp34_paper`, `comp35_paper`, `comp38_paper` (every prime of every middle block,
  any defect constants).
* `FoldGen`: `FoldInputsC` (FD's `FoldInputs` with `comp` at `c_B r + R q`), `ofPaper34`,
  `ofPaper38`, `ofFoldInputs`; `fold_paper_gen` (FD's `fold_paper` at `c' = c_B + R r_X`).
* `Constructor`: `SpecFoldInputsC`, `SpecSymSkew`, `FoldSides`, `hNr4_of_inputsC`,
  `hNr4_of_symSkew34`, `hNr4_of_symSkew38` (NB3's `hNr4` at any piece table `κ`).
* `Sanity`: `compNumeric_ge` (`34` is optimal for the numerical step), `foldInputsC_crude`.
-/
