module

@[expose] public section







namespace Sarkozy.F3Kernel

/-- The fixed data of one cross graph and one factor table (generated). -/
structure Consts where
  /-- the cross edges, layout `M` -/
  EM : Nat
  /-- the cross edges, layout `T` -/
  ET : Nat
  /-- base-graph neighbourhoods as 64-bit lane vectors, `2304 u` bits per vertex `u` -/
  ADJ64 : Nat
  /-- factor table: `⌈√𝖿_m(s) 2^64⌉` at `W s`, `⌈√𝖿_ρ(s) 2^64⌉` at `W (d + 1 + s)` -/
  FT : Nat
  /-- width of a factor-table entry -/
  W : Nat
  /-- largest signature index `d` -/
  d : Nat
  /-- `⌈√2 · 2^64⌉` -/
  SQ2 : Nat
  /-- strongly-connected-component tables for `k = 2, 3, 4`, two bits per off-diagonal
  presence pattern: `0` = a component with at least three vertices, else `1 + b` -/
  SCC2 : Nat
  /-- see `SCC2` -/
  SCC3 : Nat
  /-- see `SCC2` -/
  SCC4 : Nat

/-- `∑_{i < 36} 2^{64 i}`. -/
def LANE0 : Nat := Nat.div (Nat.sub (Nat.pow 2 2304) 1) (Nat.sub (Nat.pow 2 64) 1)
/-- `∑_{j < 36} 2^{63 j}` (bit spreading by one multiplication). -/
def REP63 : Nat := Nat.div (Nat.sub (Nat.pow 2 2268) 1) (Nat.sub (Nat.pow 2 63) 1)
/-- `2^36 - 1`. -/
def FULL36 : Nat := 68719476735
/-- `2^64 - 1`. -/
def FULL64 : Nat := 18446744073709551615
/-- SWAR masks, repeated in every 64-bit lane. -/
def MK1 : Nat := Nat.mul 6148914691236517205 LANE0
/-- see `MK1` -/
def MK2 : Nat := Nat.mul 3689348814741910323 LANE0
/-- see `MK1` -/
def MK4 : Nat := Nat.mul 1085102592571150095 LANE0
/-- see `MK1` -/
def MK8 : Nat := Nat.mul 71777214294589695 LANE0
/-- see `MK1` -/
def MK16 : Nat := Nat.mul 281470681808895 LANE0
/-- see `MK1` -/
def MK32 : Nat := Nat.mul 4294967295 LANE0

/-- Per-lane popcount of a number whose 64-bit lanes are below `2^36`. -/
def swar (x : Nat) : Nat :=
  let x1 := Nat.sub x (Nat.land (Nat.shiftRight x 1) MK1)
  let x2 := Nat.add (Nat.land x1 MK2) (Nat.land (Nat.shiftRight x1 2) MK2)
  let x3 := Nat.land (Nat.add x2 (Nat.shiftRight x2 4)) MK4
  let x4 := Nat.land (Nat.add x3 (Nat.shiftRight x3 8)) MK8
  let x5 := Nat.land (Nat.add x4 (Nat.shiftRight x4 16)) MK16
  Nat.land (Nat.add x5 (Nat.shiftRight x5 32)) MK32

/-- Bit `i` of `x`. -/
def bit (x i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight x i) 1) 1

/-- A cylinder `(P, A)` in both layouts. -/
structure Cyl where
  /-- present edges, layout `M` -/
  pm : Nat
  /-- absent edges, layout `M` -/
  am : Nat
  /-- present edges, layout `T` -/
  pt : Nat
  /-- absent edges, layout `T` -/
  qt : Nat

section ClassRoots

variable (G : Consts)

/-- Edges before the edge at `T`-position `p` (the refiner's edge order), layout `T`. -/
def beforeT (p : Nat) : Nat := Nat.land G.ET (Nat.sub (Nat.shiftLeft 1 p) 1)

/-- Edges before the edge at `T`-position `p`, layout `M`. -/
def beforeM (p : Nat) : Nat :=
  let x := Nat.land p 63
  let y := Nat.shiftRight p 6
  Nat.land G.EM (Nat.lor (Nat.mul LANE0 (Nat.sub (Nat.shiftLeft 1 y) 1))
    (Nat.shiftLeft (Nat.land LANE0 (Nat.sub (Nat.shiftLeft 1 (Nat.mul 64 x)) 1)) y))

/-- Row `x`, layout `M`. -/
def rowM (x : Nat) : Nat := Nat.land G.EM (Nat.shiftLeft FULL64 (Nat.mul 64 x))
/-- Column `y`, layout `M`. -/
def colM (y : Nat) : Nat := Nat.land G.EM (Nat.shiftLeft LANE0 y)
/-- Row `x`, layout `T`. -/
def rowT (x : Nat) : Nat := Nat.land G.ET (Nat.shiftLeft LANE0 x)
/-- Column `y`, layout `T`. -/
def colT (y : Nat) : Nat := Nat.land G.ET (Nat.shiftLeft FULL64 (Nat.mul 64 y))

/-- Is the `T`-position `p` an edge? -/
def isEdge (p : Nat) : Bool := bit G.ET p

/-- Decide a connector `(cx, cy)` of a `B` class: present (`q = 1`) or absent if it is a free
edge; `q = 0` is required otherwise. -/
def connector (c : Cyl) (cx cy q : Nat) : Option Cyl :=
  let pT := Nat.add (Nat.mul 64 cy) cx
  let pM := Nat.add (Nat.mul 64 cx) cy
  bif isEdge G pT && !(bit c.qt pT) then
    bif Nat.beq q 1 then
      some ⟨Nat.lor c.pm (Nat.shiftLeft 1 pM), c.am, Nat.lor c.pt (Nat.shiftLeft 1 pT), c.qt⟩
    else
      some ⟨c.pm, Nat.lor c.am (Nat.shiftLeft 1 pM), c.pt, Nat.lor c.qt (Nat.shiftLeft 1 pT)⟩
  else bif Nat.beq q 0 then some c else none

/-- The root of the A/B class with the given key (`none` if the key is not a class). -/
def classRoot (key : Nat) : Option Cyl :=
  let third := Nat.land key 4095
  let p2 := Nat.land (Nat.shiftRight key 12) 4095
  let kind := Nat.land (Nat.shiftRight key 24) 1
  let p1 := Nat.shiftRight key 25
  bif Nat.blt p1 4096 && isEdge G p1 && isEdge G p2 && Nat.blt p1 p2 then
    let x1 := Nat.land p1 63
    let y1 := Nat.shiftRight p1 6
    let x2 := Nat.land p2 63
    let y2 := Nat.shiftRight p2 6
    let dM := Nat.xor G.EM (Nat.lor (rowM G x1) (colM G y1))
    let dT := Nat.xor G.ET (Nat.lor (rowT G x1) (colT G y1))
    bif Nat.beq kind 0 then
      let p3 := third
      let x3 := Nat.land p3 63
      bif isEdge G p3 && Nat.beq x2 x1 && Nat.beq (Nat.shiftRight p3 6) y1 && Nat.blt p1 p3 then
        let PM := Nat.lor (Nat.shiftLeft 1 (Nat.add (Nat.mul 64 x1) y1))
          (Nat.lor (Nat.shiftLeft 1 (Nat.add (Nat.mul 64 x2) y2))
            (Nat.shiftLeft 1 (Nat.add (Nat.mul 64 x3) y1)))
        let PT := Nat.lor (Nat.shiftLeft 1 p1) (Nat.lor (Nat.shiftLeft 1 p2) (Nat.shiftLeft 1 p3))
        let AM := Nat.lor dM (Nat.lor (beforeM G p1)
          (Nat.lor (Nat.land (rowM G x1) (beforeM G p2)) (Nat.land (colM G y1) (beforeM G p3))))
        let AT := Nat.lor dT (Nat.lor (beforeT G p1)
          (Nat.lor (Nat.land (rowT G x1) (beforeT G p2)) (Nat.land (colT G y1) (beforeT G p3))))
        some ⟨PM, Nat.xor AM (Nat.land AM PM), PT, Nat.xor AT (Nat.land AT PT)⟩
      else none
    else
      bif !(Nat.beq x2 x1) && !(Nat.beq y2 y1) && Nat.blt third 4 then
        let PM := Nat.lor (Nat.shiftLeft 1 (Nat.add (Nat.mul 64 x1) y1))
          (Nat.shiftLeft 1 (Nat.add (Nat.mul 64 x2) y2))
        let PT := Nat.lor (Nat.shiftLeft 1 p1) (Nat.shiftLeft 1 p2)
        let AM := Nat.lor (beforeM G p1) (Nat.land dM (beforeM G p2))
        let AT := Nat.lor (beforeT G p1) (Nat.land dT (beforeT G p2))
        let c0 : Cyl := ⟨PM, Nat.xor AM (Nat.land AM PM), PT, Nat.xor AT (Nat.land AT PT)⟩
        match connector G c0 x1 y2 (Nat.land third 1) with
        | none => none
        | some c1 => connector G c1 x2 y1 (Nat.shiftRight third 1)
      else none
  else none

end ClassRoots

section Leaf

variable (G : Consts)

/-- `∑_{i < k}` of the 64-bit lane of `H` at the `i`-th vertex of the packed list `wl`. -/
noncomputable def hSum (H : Nat) (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih wl => Nat.add (Nat.land (Nat.shiftRight H (Nat.shiftLeft (Nat.land wl 63) 6)) 127)
      (ih (Nat.shiftRight wl 6))) n

/-- `2^2304 - 1`. -/
def MASK2304 : Nat := Nat.sub (Nat.pow 2 2304) 1

/-- The base-graph neighbourhood of `u` as a 64-bit lane vector (bit `64 w` for `w ∼ u`). -/
def adj64 (u : Nat) : Nat := Nat.land (Nat.shiftRight G.ADJ64 (Nat.mul 2304 u)) MASK2304

/-- `∑_{i < k}` of the lane vectors of the vertices of `wl`. -/
noncomputable def adjSum (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih wl => Nat.add (adj64 G (Nat.land wl 63)) (ih (Nat.shiftRight wl 6))) n

/-- The mask of a factor-table entry. -/
def maskW : Nat := Nat.sub (Nat.shiftLeft 1 G.W) 1

/-- The integrated vertices of one side, in the order `r` (6 bits per vertex). `mask` is the set
of labelled vertices (bits `36`–`63` preset, so a vertex id `≥ 36` fails), `T` the lane vector
of `s_u = h_u + t_u` (initially `h_u`, plus the neighbourhood of every labelled vertex), `acc`
the fixed-point product, multiplied by `⌈√𝖿_m(s_u) 2^64⌉ / 2^64` rounded up. -/
noncomputable def uLoop (n : Nat) : Nat → Nat → Nat → Nat → Option (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Option (Nat × Nat))
    (fun r mask _ acc => bif Nat.beq mask FULL64 then some (r, acc) else none)
    (fun _ ih r mask T acc =>
      let u := Nat.land r 63
      bif Nat.beq (Nat.land (Nat.shiftRight mask u) 1) 1 then none
      else
        let s := Nat.land (Nat.shiftRight T (Nat.shiftLeft u 6)) 127
        bif Nat.ble s G.d then
          ih (Nat.shiftRight r 6) (Nat.lor mask (Nat.shiftLeft 1 u)) (Nat.add T (adj64 G u))
            (Nat.shiftRight (Nat.add (Nat.mul acc
              (Nat.land (Nat.shiftRight G.FT (Nat.mul G.W s)) (maskW G))) FULL64) 64)
        else none) n

/-- The labelling of the witness `wl` between the cover and the integrated set: the exponent
part `e(V, C) + e(V)` (from the lanes of `T` before and after, minus the `h`-part `hw`) and the
new lane vector. -/
noncomputable def witSwitch (k wl hw T : Nat) : Nat × Nat :=
  let T1 := Nat.add T (adjSum G k wl)
  let tb := Nat.sub (hSum T k wl) hw
  let ta := Nat.sub (hSum T1 k wl) hw
  (Nat.add tb (Nat.div (Nat.sub ta tb) 2), T1)

/-- One side of a leaf: the cover vertices `cmask` first (factor `𝖿_ρ`, table `FTr`), then the
witness, then the integrated vertices (`uLoop`). Returns `(rest of r, e(V, C) + e(V), acc)`. -/
noncomputable def cLoop (FTr cmask wl k hw : Nat) (n : Nat) :
    Nat → Nat → Nat → Nat → Option (Nat × Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Option (Nat × Nat × Nat))
    (fun r mask T acc =>
      bif Nat.beq mask FULL64 then some (r, (witSwitch G k wl hw T).1, acc) else none)
    (fun f ih r mask T acc =>
      let u := Nat.land r 63
      bif Nat.beq (Nat.land (Nat.shiftRight cmask u) 1) 1 then
        bif Nat.beq (Nat.land (Nat.shiftRight mask u) 1) 1 then none
        else
          let s := Nat.land (Nat.shiftRight T (Nat.shiftLeft u 6)) 127
          bif Nat.ble s G.d then
            ih (Nat.shiftRight r 6) (Nat.lor mask (Nat.shiftLeft 1 u)) (Nat.add T (adj64 G u))
              (Nat.shiftRight (Nat.add (Nat.mul acc
                (Nat.land (Nat.shiftRight FTr (Nat.mul G.W s)) (maskW G))) FULL64) 64)
          else none
      else
        bif Nat.beq (Nat.land cmask mask) cmask then
          match witSwitch G k wl hw T with
          | (e, T1) =>
            match uLoop G (f + 1) r mask T1 acc with
            | none => none
            | some (r1, acc1) => some (r1, e, acc1)
        else none) n

/-- The off-diagonal presence pattern of the witness rectangle (`k²` bits, row-major) and the
diagonal check; `PR` is the present part of the rectangle, layout `M`. -/
def rectPat (PR xs ys k : Nat) : Nat → Nat → Option Nat
  | 0, pat => some pat
  | f + 1, pat =>
    let idx := f
    let i := Nat.div idx k
    let j := Nat.mod idx k
    let xi := Nat.land (Nat.shiftRight xs (Nat.mul 6 i)) 63
    let yj := Nat.land (Nat.shiftRight ys (Nat.mul 6 j)) 63
    let b := bit PR (Nat.add (Nat.mul 64 xi) yj)
    bif Nat.beq i j then
      bif b then rectPat PR xs ys k f pat else none
    else rectPat PR xs ys k f (bif b then Nat.lor pat (Nat.shiftLeft 1 idx) else pat)

/-- The vertex mask of a packed list of `k` distinct vertices below `36` (`none` otherwise). -/
def vmask : Nat → Nat → Nat → Option Nat
  | 0, _, m => some m
  | f + 1, l, m =>
    let v := Nat.land l 63
    bif Nat.blt v 36 && !(bit m v) then vmask f (Nat.shiftRight l 6) (Nat.lor m (Nat.shiftLeft 1 v))
    else none

/-- The check of one leaf with record `rec` on the cylinder `c` (witness size `k ∈ {2, 3, 4}`;
the field value `3`, i.e. `k = 5`, is rejected): `some (k, value, free)`, the
value being the fixed-point upper bound (scale `2^64`) of `2^{ex*/2} ∏_u √𝖿(s_u)` and `free`
the number of free edges. -/
noncomputable def leafCheck (c : Cyl) (rec : Nat) : Option (Nat × Nat × Nat) :=
  let k := Nat.add (Nat.land rec 3) 2
  let xs := Nat.land (Nat.shiftRight rec 2) 16777215
  let ys := Nat.land (Nat.shiftRight rec 26) 16777215
  let cxm := Nat.land (Nat.shiftRight rec 50) FULL36
  let cym := Nat.land (Nat.shiftRight rec 86) FULL36
  let r := Nat.shiftRight rec 122
  match vmask k xs 0, vmask k ys 0 with
  | some V, some Wm =>
    bif Nat.beq (Nat.land rec 3) 3 then none else
    let FM := Nat.xor G.EM (Nat.lor c.pm c.am)
    let FT := Nat.xor G.ET (Nat.lor c.pt c.qt)
    let RECT := Nat.land (Nat.mul (Nat.land (Nat.mul V REP63) LANE0) Wm) G.EM
    bif Nat.beq (Nat.land RECT FM) 0 && Nat.beq (Nat.land cxm V) 0 &&
        Nat.beq (Nat.land cym Wm) 0 then
      let NA := Nat.xor G.EM c.am
      let X := Nat.lor RECT (Nat.lor (Nat.mul (Nat.land (Nat.mul cxm REP63) LANE0) FULL64)
        (Nat.mul cym LANE0))
      bif Nat.beq (Nat.land NA X) NA then
        match rectPat (Nat.land RECT c.pm) xs ys k (Nat.mul k k) 0 with
        | none => none
        | some pat =>
          let tbl := bif Nat.beq k 2 then G.SCC2 else bif Nat.beq k 3 then G.SCC3 else G.SCC4
          let ent := Nat.land (Nat.shiftRight tbl (Nat.mul 2 pat)) 3
          bif Nat.beq ent 0 then none
          else
            let HM := swar FM
            let HT := swar FT
            let fV := hSum HM k xs
            let fW := hSum HT k ys
            let FTr := Nat.shiftRight G.FT (Nat.mul G.W (Nat.add G.d 1))
            let hi := Nat.sub FULL64 FULL36
            match cLoop G FTr cxm xs k fV (Nat.sub 36 k) r (Nat.lor V hi) HM (Nat.pow 2 64) with
            | none => none
            | some (r1, eX, acc1) =>
              match cLoop G FTr cym ys k fW (Nat.sub 36 k) r1 (Nat.lor Wm hi) HT acc1 with
              | none => none
              | some (r2, eZ, acc2) =>
                let ex2 := Nat.add (Nat.add (Nat.mul 2 (Nat.sub ent 1)) (Nat.add fV fW))
                  (Nat.add eX eZ)
                bif Nat.beq r2 0 then
                  let acc3 := bif Nat.beq (Nat.land ex2 1) 1 then
                    Nat.shiftRight (Nat.add (Nat.mul acc2 G.SQ2) FULL64) 64 else acc2
                  let free := Nat.land (Nat.shiftRight (Nat.mul HM LANE0) 2240) FULL64
                  some (k, Nat.shiftLeft acc3 (Nat.shiftRight ex2 1), free)
                else none
      else none
    else none
  | _, _ => none

end Leaf

/-- The state of the token machine. -/
structure St where
  /-- the current cylinder (`none` between classes) -/
  cur : Option Cyl
  /-- the pending absent children -/
  stack : List Cyl
  /-- one more than the last class key -/
  last : Nat
  /-- fixed-point sum for `k = 2` -/
  s2 : Nat
  /-- fixed-point sum for `k = 3` -/
  s3 : Nat
  /-- fixed-point sum for `k = 4` -/
  s4 : Nat
  /-- `∑ 2^{free}` over the classes -/
  cmass : Nat
  /-- `∑ 2^{free}` over the leaves -/
  lmass : Nat
  /-- number of leaves -/
  nl : Nat

/-- The result of a chunk. -/
structure Summary where
  /-- fixed-point sums -/
  s2 : Nat
  /-- see `s2` -/
  s3 : Nat
  /-- see `s2` -/
  s4 : Nat
  /-- `∑ 2^{free}` over the classes (= over the leaves) -/
  mass : Nat
  /-- number of leaves -/
  nl : Nat
  /-- one more than the last class key -/
  last : Nat
deriving DecidableEq

/-- Pop the next pending cylinder. -/
def popNext (st : St) : St :=
  match st.stack with
  | [] => { st with cur := none }
  | c :: cs => { st with cur := some c, stack := cs }

/-- One token. The accumulators are forced at every step (`Nat.beq` on their sum), so that
no chain of unevaluated additions builds up in the kernel. -/
noncomputable def step (G : Consts) (st : St) (tok : Nat) : Option St :=
  let tag := Nat.land tok 3
  let pay := Nat.shiftRight tok 2
  bif Nat.beq tag 1 then
    match st.cur with
    | none => none
    | some c =>
      let x := Nat.land pay 63
      let y := Nat.shiftRight pay 6
      let bM := Nat.shiftLeft 1 (Nat.add (Nat.mul 64 x) y)
      let bT := Nat.shiftLeft 1 pay
      bif Nat.blt pay 2304 && isEdge G pay && !(bit (Nat.lor c.pt c.qt) pay) then
        some { st with cur := some ⟨Nat.lor c.pm bM, c.am, Nat.lor c.pt bT, c.qt⟩,
                       stack := ⟨c.pm, Nat.lor c.am bM, c.pt, Nat.lor c.qt bT⟩ :: st.stack }
      else none
  else bif Nat.beq tag 2 then
    match st.cur with
    | none => none
    | some c =>
      match leafCheck G c pay with
      | none => none
      | some (k, v, free) =>
        let s2 := bif Nat.beq k 2 then Nat.add st.s2 v else st.s2
        let s3 := bif Nat.beq k 3 then Nat.add st.s3 v else st.s3
        let s4 := bif Nat.beq k 4 then Nat.add st.s4 v else st.s4
        let lm := Nat.add st.lmass (Nat.shiftLeft 1 free)
        bif Nat.beq (Nat.add (Nat.add s2 s3) (Nat.add s4 lm)) 0 then none
        else some (popNext { st with s2 := s2, s3 := s3, s4 := s4, lmass := lm,
                                     nl := Nat.add st.nl 1 })
  else bif Nat.beq tag 0 then
    match st.cur with
    | some _ => none
    | none =>
      bif Nat.ble st.last pay then
        match classRoot G pay with
        | none => none
        | some c =>
          let free := Nat.land (Nat.shiftRight (Nat.mul (swar (Nat.xor G.EM (Nat.lor c.pm c.am)))
            LANE0) 2240) FULL64
          let cm := Nat.add st.cmass (Nat.shiftLeft 1 free)
          bif Nat.beq cm 0 then none
          else some { st with cur := some c, last := Nat.add pay 1, cmass := cm }
      else none
  else none

/-- Run the token machine over a chunk. -/
noncomputable def run (G : Consts) (l : List Nat) : St → Option St :=
  List.rec (motive := fun _ => St → Option St) (fun st => some st)
    (fun t _ ih st =>
      match step G st t with
      | none => none
      | some st' => ih st') l

/-- The summary of a chunk that starts after the class key `last - 1` (`last = 0`: no
constraint): every class tree complete, and class mass = leaf mass. -/
noncomputable def chunk (G : Consts) (last : Nat) (toks : List Nat) : Option Summary :=
  match run G toks ⟨none, [], last, 0, 0, 0, 0, 0, 0⟩ with
  | none => none
  | some st =>
    match st.cur, st.stack with
    | none, [] =>
      bif Nat.beq st.cmass st.lmass then
        some ⟨st.s2, st.s3, st.s4, st.cmass, st.nl, st.last⟩
      else none
    | _, _ => none

end Sarkozy.F3Kernel
