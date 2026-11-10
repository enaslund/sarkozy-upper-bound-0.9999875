module

public import Sarkozy.MiddleCertificates.GridData
public import Sarkozy.BlockAdapter.Layer
public import Sarkozy.SpectralD.BooleanModels
public import Sarkozy.SpectralD.GaussianCertificate
public import Sarkozy.BlockSpecPaper.AllpConsts

/-!
# The class-three grid tests of the middle cuts L10 and L21: definitions

`paper/sections/20_middle_reference.tex`, `lem:layer12-caps`(a) and `cert:layer12-grid`;
`paper/sections/14_spectral.tex`, `thm:spectral-criterion`, the finite test `eq:spectral-test`.

The two cuts, with B6's spectral data (`BlockAdapter.recordData (Fin 1)`, `recordLayer`):

* **L10**: the first chamber cut `ϑ₀` of `G_{L,1}` (half `{0, 1, 2}`, three vertices);
* **L21**: the layer swap `ι` of `G_{L,2}` (half: layer `0`, six vertices).

For each, the half vertices are coded by `u ∈ ℤ/6ℤ`, and the generated tables of `GridData` are
read through these codes:

* `modelD c`: the cross signs `ς_{jk}` (at class three `Δ^E = ς`, `FiniteModel.deltaE_three`);
* `modelH c`: the model matrix `𝐇` (`eq:spec:H`; at class three `𝐇⁺ = 𝐇`);
* per piece `i` (the threshold `X = pieceStart i`): the recorded `τ^sp`, the bars
  `c̄_⊥`, `η̄_Q`, `ε̄_V` (rounded up), the integer `base`, and `η̄_B` defined from `base`;
* `testReal`, `testImag`: the scaled test matrix `10⁸ M_{3,±}(τ)` of `eq:spectral-test` for the
  three Fourier coefficients `χ(ξ)ε_G ∈ {-i, 0, i}` (`e = 0, 1, 2`), in the form of
  `SpectralD.complexTest`;
* `factorReal`, `factorImag`, `shift`: the untrusted Gaussian-integer Gram factor and the
  residual shift, checked in `Checks.lean` (`ResidualChecks`).
-/

@[expose] public section

namespace Sarkozy.MiddleCertificates

open Finset Sarkozy.Labellings Sarkozy.SpectralD

/-- The two middle cuts with recorded route-A grids used by the ALLp closing. -/
inductive MidCut
  | l10 | l21
  deriving DecidableEq

namespace MidCut

/-- The vertex set: `ℤ/6ℤ × Fin 1` (`G_{L,1}`) or `ℤ/6ℤ × Fin 2` (`G_{L,2}`). -/
def Vertex : MidCut → Type
  | .l10 => ZMod 6 × Fin 1
  | .l21 => ZMod 6 × Fin 2

instance (c : MidCut) : Fintype c.Vertex := by cases c <;> unfold Vertex <;> infer_instance

instance (c : MidCut) : DecidableEq c.Vertex := by cases c <;> unfold Vertex <;> infer_instance

/-- The spectral data: B6's `recordData (Fin 1)` (L10) and `recordLayer` (L21). -/
noncomputable def data : (c : MidCut) → Cuts.SpecData c.Vertex
  | .l10 => BlockAdapter.recordData (Fin 1)
  | .l21 => BlockAdapter.recordLayer

/-- The Boolean edge test of `G_L`: `(u, ℓ) → (rot u, ℓ')`. -/
def edge : (c : MidCut) → c.Vertex → c.Vertex → Bool
  | .l10 => fun u w => decide (w.1 = rot u.1)
  | .l21 => fun u w => decide (w.1 = rot u.1)

theorem mem_edge (c : MidCut) (i j : c.Vertex) : (i, j) ∈ c.data.G.E ↔ c.edge i j = true := by
  cases c
  · exact (mem_recordGraph (Fin 1) ((i, j) : (ZMod 6 × Fin 1) × (ZMod 6 × Fin 1))).trans
      (by simp [edge])
  · exact (mem_recordGraph (Fin 2) ((i, j) : (ZMod 6 × Fin 2) × (ZMod 6 × Fin 2))).trans
      (by simp [edge])

/-- The code `u` of a vertex `(u, ℓ)`. -/
def code : (c : MidCut) → c.Vertex → ℕ
  | .l10, v => v.1.val
  | .l21, v => v.1.val

/-- The cross-sign table. -/
def signTable : MidCut → List (List ℤ)
  | .l10 => l10Sign
  | .l21 => l21Sign

/-- The table of `𝐇`. -/
def gramTable : MidCut → List (List ℤ)
  | .l10 => l10Gram
  | .l21 => l21Gram

/-- The per-piece rational data. -/
def tauList : MidCut → List ℚ
  | .l10 => l10Tau
  | .l21 => l21Tau

def cbarList : MidCut → List ℚ
  | .l10 => l10Cbar
  | .l21 => l21Cbar

def etaQList : MidCut → List ℚ
  | .l10 => l10EtaQ
  | .l21 => l21EtaQ

def epsVList : MidCut → List ℚ
  | .l10 => l10EpsV
  | .l21 => l21EpsV

def g3List : MidCut → List ℚ
  | .l10 => l10G3
  | .l21 => l21G3

def linearList : MidCut → List ℤ
  | .l10 => l10Linear
  | .l21 => l21Linear

def baseList : MidCut → List ℤ
  | .l10 => l10Base
  | .l21 => l21Base

def shiftList : MidCut → List (List ℤ)
  | .l10 => l10Shift
  | .l21 => l21Shift

def factorReList : MidCut → List (List (List (List ℤ)))
  | .l10 => l10FactorRe
  | .l21 => l21FactorRe

def factorImList : MidCut → List (List (List (List ℤ)))
  | .l10 => l10FactorIm
  | .l21 => l21FactorIm

/-- The column of `ALLp` constants of the cut (`AllpData.allpG i c`): `1` for L10, `2` for
L21. -/
def allpIdx : MidCut → Fin 5
  | .l10 => 1
  | .l21 => 2

end MidCut

open MidCut

/-- Entry `(i, j)` of a table, `0` outside. -/
def entry (T : List (List ℤ)) (i j : ℕ) : ℤ := (T.getD i []).getD j 0

/-- A table read on the half through the codes. -/
noncomputable def atTable (c : MidCut) (T : List (List ℤ)) (i j : c.data.cut.Half) : ℤ :=
  entry T (c.code i.1) (c.code j.1)

/-- The cross signs `ς` as an integer matrix on the half. -/
noncomputable def modelD (c : MidCut) : c.data.cut.Half → c.data.cut.Half → ℤ :=
  atTable c c.signTable

/-- The model matrix `𝐇` as an integer matrix on the half. -/
noncomputable def modelH (c : MidCut) : c.data.cut.Half → c.data.cut.Half → ℤ :=
  atTable c c.gramTable

/-- The recorded class-three `τ^sp` at the start of piece `i`. -/
def tau (c : MidCut) (i : Fin 33) : ℚ := c.tauList.getD i.val 0

/-- `c̄_⊥` at the start of piece `i`. -/
def cbar (c : MidCut) (i : Fin 33) : ℚ := c.cbarList.getD i.val 0

/-- `η̄_Q` at the start of piece `i`. -/
def etaQ (c : MidCut) (i : Fin 33) : ℚ := c.etaQList.getD i.val 0

/-- `ε̄_V` at the start of piece `i`. -/
def epsV (c : MidCut) (i : Fin 33) : ℚ := c.epsVList.getD i.val 0

/-- The recorded class-three constant `g₃` at the start of piece `i`. -/
def g3 (c : MidCut) (i : Fin 33) : ℚ := c.g3List.getD i.val 0

/-- `10⁸ τ`. -/
def linear (c : MidCut) (i : Fin 33) : ℤ := c.linearList.getD i.val 0

/-- `base`, with `base / 10⁸ = τ(c̄ + τ - η̄_Q) - η̄_B`. -/
def base (c : MidCut) (i : Fin 33) : ℤ := c.baseList.getD i.val 0

/-- `η̄_B := τ(c̄_⊥ + τ - η̄_Q) - base/10⁸`; the generator rounds `base` down, so `η̄_B` is at
least the recorded upper end of `η_B`. -/
def etaB (c : MidCut) (i : Fin 33) : ℚ :=
  tau c i * (cbar c i + tau c i - etaQ c i) - base c i / 100000000

/-- The coefficient `χ(ξ)ε_G = (e - 1) i`. -/
def char (e : Fin 3) : ℤ := (e.val : ℤ) - 1

/-- The real part of the scaled test matrix (`SpectralD.complexTest` at class three). -/
noncomputable def testReal (c : MidCut) (i : Fin 33) (e : Fin 3) (a b : c.data.cut.Half) : ℤ :=
  (if a = b then base c i else 0) +
    100000000 * char e ^ 2 * (∑ k, modelD c k a * modelD c k b) - 100000000 * modelH c a b

/-- The imaginary part of the scaled test matrix. -/
noncomputable def testImag (c : MidCut) (i : Fin 33) (e : Fin 3) (a b : c.data.cut.Half) : ℤ :=
  char e * linear c i * modelD c a b

/-- The factor table of piece `i` and coefficient `e`. -/
def factorTable (L : List (List (List (List ℤ)))) (i : Fin 33) (e : Fin 3) : List (List ℤ) :=
  (L.getD i.val []).getD e.val []

noncomputable def factorReal (c : MidCut) (i : Fin 33) (e : Fin 3) :
    c.data.cut.Half → c.data.cut.Half → ℤ :=
  atTable c (factorTable c.factorReList i e)

noncomputable def factorImag (c : MidCut) (i : Fin 33) (e : Fin 3) :
    c.data.cut.Half → c.data.cut.Half → ℤ :=
  atTable c (factorTable c.factorImList i e)

/-- The residual shift. -/
def shift (c : MidCut) (i : Fin 33) (e : Fin 3) : ℤ := (c.shiftList.getD i.val []).getD e.val 0

/-- The residual `10¹² M - B^*B`, real part. -/
noncomputable def residualReal (c : MidCut) (i : Fin 33) (e : Fin 3) (a b : c.data.cut.Half) : ℤ :=
  1000000000000 * testReal c i e a b - gramReal (factorReal c i e) (factorImag c i e) a b

/-- The residual `10¹² M - B^*B`, imaginary part. -/
noncomputable def residualImag (c : MidCut) (i : Fin 33) (e : Fin 3) (a b : c.data.cut.Half) : ℤ :=
  1000000000000 * testImag c i e a b - gramImag (factorReal c i e) (factorImag c i e) a b

/-- The tables `ς`, `𝐇` are those of the actual spectral data. -/
def ModelChecks (c : MidCut) : Prop := ∀ a b : c.data.cut.Half,
  edgeSign c.edge c.data.cut.flip a.1 b.1 = modelD c a b ∧
    FiniteModel.gramThree c.edge c.data.cut a b = modelH c a b

/-- The residuals are Hermitian and diagonally dominant with shift `C`. -/
def ResidualChecks (c : MidCut) (i : Fin 33) : Prop := ∀ e : Fin 3,
  (∀ a b, residualReal c i e a b = residualReal c i e b a) ∧
  (∀ a b, residualImag c i e a b = -residualImag c i e b a) ∧
  ∀ a, ∑ b, (|(if a = b then shift c i e else 0) - residualReal c i e a b| +
    |residualImag c i e a b|) ≤ shift c i e

/-- The rational side conditions: `10⁸ τ` is `linear`, `τ > 0`, and the recorded constant
`g₃ ≥ (c̄_⊥ + τ)/(1 - ε̄_V)` (`thm:spectral-criterion`, choice of `g_𝔠`), with `ε̄_V < 1`. -/
def ScalarChecks (c : MidCut) (i : Fin 33) : Prop :=
  (linear c i : ℚ) = 100000000 * tau c i ∧ 0 < tau c i ∧ 0 ≤ cbar c i ∧ 0 ≤ epsV c i ∧
    epsV c i < 1 ∧ (cbar c i + tau c i) / (1 - epsV c i) ≤ g3 c i ∧
    g3 c i ≤ BlockSpecPaper.AllpData.allpG i c.allpIdx

end Sarkozy.MiddleCertificates
