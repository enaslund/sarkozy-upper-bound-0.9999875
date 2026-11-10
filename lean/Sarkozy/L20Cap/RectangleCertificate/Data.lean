module

public import Sarkozy.L20Cap.RectNonstar
public import Sarkozy.L20Cap.RectGraph
public import Sarkozy.ExtractionK.Leaf


@[expose] public section

namespace Sarkozy.L20Cap.RectangleCertificate

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

abbrev Edge := Fin 6 × Fin 6
abbrev ClassDatum := Finset Edge × Finset Edge

def datum0 : ClassDatum :=
  ({(0, 2), (0, 3), (1, 2)}, {(1, 3), (4, 3), (5, 3)})

def record0 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 3), (1, 2)]
  Cx := {2, 3, 4, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 2, 3, 0, 1]
  ordZ := ![0, 2, 5, 4, 1, 3]

def datum1 : ClassDatum :=
  ({(0, 2), (0, 3), (4, 2)}, {(1, 2), (1, 3), (4, 3), (5, 3)})

def record1 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 3), (4, 2)]
  Cx := {2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![3, 5, 1, 2, 4, 0]
  ordZ := ![0, 2, 5, 4, 1, 3]

def datum2 : ClassDatum :=
  ({(0, 2), (0, 3), (5, 2)}, {(1, 2), (1, 3), (4, 2), (4, 3), (5, 3)})

def record2 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 3), (5, 2)]
  Cx := {2, 3}
  Cz := {0, 1, 4, 5}
  ordX := ![2, 4, 0, 1, 5, 3]
  ordZ := ![0, 2, 5, 4, 1, 3]

def datum3 : ClassDatum :=
  ({(0, 2), (1, 3)}, {(0, 3), (1, 2)})

def record3 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (1, 3)]
  Cx := {2, 3, 4, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 2, 3, 0, 1]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum4 : ClassDatum :=
  ({(0, 2), (1, 2), (1, 3)}, {(0, 3)})

def record4 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (1, 3)]
  Cx := {2, 3, 4, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 2, 3, 0, 1]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum5 : ClassDatum :=
  ({(0, 2), (0, 3), (1, 3)}, {(1, 2)})

def record5 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (1, 3)]
  Cx := {2, 3, 4, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 2, 3, 0, 1]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum6 : ClassDatum :=
  ({(0, 2), (0, 3), (1, 2), (1, 3)}, ∅)

def record6 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (1, 3)]
  Cx := {2, 3, 4, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 2, 3, 0, 1]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum7 : ClassDatum :=
  ({(0, 2), (4, 3)}, {(0, 3), (1, 3), (4, 2)})

def record7 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (4, 3)]
  Cx := {1, 2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 1, 2, 3, 5, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum8 : ClassDatum :=
  ({(0, 2), (4, 2), (4, 3)}, {(0, 3), (1, 3)})

def record8 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (4, 3)]
  Cx := {1, 2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 1, 2, 3, 5, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum9 : ClassDatum :=
  ({(0, 2), (0, 3), (4, 3)}, {(1, 3), (4, 2)})

def record9 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (4, 3)]
  Cx := {1, 2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 1, 2, 3, 5, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum10 : ClassDatum :=
  ({(0, 2), (0, 3), (4, 2), (4, 3)}, {(1, 3)})

def record10 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (4, 3)]
  Cx := {1, 2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 1, 2, 3, 5, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum11 : ClassDatum :=
  ({(0, 2), (5, 3)}, {(0, 3), (1, 3), (4, 3), (5, 2)})

def record11 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (5, 3)]
  Cx := {1, 2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 0, 2, 3, 1, 5]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum12 : ClassDatum :=
  ({(0, 2), (5, 2), (5, 3)}, {(0, 3), (1, 3), (4, 3)})

def record12 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (5, 3)]
  Cx := {1, 2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 0, 2, 3, 1, 5]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum13 : ClassDatum :=
  ({(0, 2), (0, 3), (5, 3)}, {(1, 3), (4, 3), (5, 2)})

def record13 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (5, 3)]
  Cx := {1, 2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 0, 2, 3, 1, 5]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum14 : ClassDatum :=
  ({(0, 2), (0, 3), (5, 2), (5, 3)}, {(1, 3), (4, 3)})

def record14 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(0, 2), (5, 3)]
  Cx := {1, 2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 0, 2, 3, 1, 5]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum15 : ClassDatum :=
  ({(1, 2), (1, 3), (4, 2)}, {(0, 2), (0, 3), (4, 3), (5, 3)})

def record15 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 3), (4, 2)]
  Cx := {2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 3, 1, 2, 4, 0]
  ordZ := ![0, 2, 5, 4, 1, 3]

def datum16 : ClassDatum :=
  ({(1, 2), (1, 3), (5, 2)}, {(0, 2), (0, 3), (4, 2), (4, 3), (5, 3)})

def record16 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 3), (5, 2)]
  Cx := {2, 3}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 2, 0, 1, 5, 3]
  ordZ := ![0, 2, 5, 4, 1, 3]

def datum17 : ClassDatum :=
  ({(0, 3), (1, 2)}, {(0, 2), (1, 3)})

def record17 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (0, 3)]
  Cx := {2, 3, 4, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 4, 2, 3, 0, 1]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum18 : ClassDatum :=
  ({(0, 3), (1, 2), (1, 3)}, {(0, 2)})

def record18 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (0, 3)]
  Cx := {2, 3, 4, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 4, 2, 3, 0, 1]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum19 : ClassDatum :=
  ({(1, 2), (4, 3)}, {(0, 2), (0, 3), (1, 3), (4, 2)})

def record19 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (4, 3)]
  Cx := {2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 3, 1, 2, 4, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum20 : ClassDatum :=
  ({(1, 2), (4, 2), (4, 3)}, {(0, 2), (0, 3), (1, 3)})

def record20 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (4, 3)]
  Cx := {2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 3, 1, 2, 4, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum21 : ClassDatum :=
  ({(1, 2), (1, 3), (4, 3)}, {(0, 2), (0, 3), (4, 2)})

def record21 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (4, 3)]
  Cx := {2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 3, 1, 2, 4, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum22 : ClassDatum :=
  ({(1, 2), (1, 3), (4, 2), (4, 3)}, {(0, 2), (0, 3)})

def record22 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (4, 3)]
  Cx := {2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 3, 1, 2, 4, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum23 : ClassDatum :=
  ({(1, 2), (5, 3)}, {(0, 2), (0, 3), (1, 3), (4, 3), (5, 2)})

def record23 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (5, 3)]
  Cx := {2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 3, 1, 2, 0, 4]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum24 : ClassDatum :=
  ({(1, 2), (5, 2), (5, 3)}, {(0, 2), (0, 3), (1, 3), (4, 3)})

def record24 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (5, 3)]
  Cx := {2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 3, 1, 2, 0, 4]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum25 : ClassDatum :=
  ({(1, 2), (1, 3), (5, 3)}, {(0, 2), (0, 3), (4, 3), (5, 2)})

def record25 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (5, 3)]
  Cx := {2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 3, 1, 2, 0, 4]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum26 : ClassDatum :=
  ({(1, 2), (1, 3), (5, 2), (5, 3)}, {(0, 2), (0, 3), (4, 3)})

def record26 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(1, 2), (5, 3)]
  Cx := {2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 3, 1, 2, 0, 4]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum27 : ClassDatum :=
  ({(4, 2), (4, 3), (5, 2)}, {(0, 2), (0, 3), (1, 2), (1, 3), (5, 3)})

def record27 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(4, 3), (5, 2)]
  Cx := {2, 3}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 0, 1, 2, 3]
  ordZ := ![0, 2, 5, 4, 1, 3]

def datum28 : ClassDatum :=
  ({(0, 3), (4, 2)}, {(0, 2), (1, 2), (4, 3)})

def record28 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(4, 2), (0, 3)]
  Cx := {1, 2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 1, 2, 3, 4, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum29 : ClassDatum :=
  ({(0, 3), (4, 2), (4, 3)}, {(0, 2), (1, 2)})

def record29 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(4, 2), (0, 3)]
  Cx := {1, 2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 1, 2, 3, 4, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum30 : ClassDatum :=
  ({(1, 3), (4, 2)}, {(0, 2), (0, 3), (1, 2), (4, 3)})

def record30 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(4, 2), (1, 3)]
  Cx := {2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 4, 1, 2, 3, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum31 : ClassDatum :=
  ({(1, 3), (4, 2), (4, 3)}, {(0, 2), (0, 3), (1, 2)})

def record31 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(4, 2), (1, 3)]
  Cx := {2, 3, 5}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 4, 1, 2, 3, 0]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum32 : ClassDatum :=
  ({(4, 2), (5, 3)}, {(0, 2), (0, 3), (1, 2), (1, 3), (4, 3), (5, 2)})

def record32 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(4, 2), (5, 3)]
  Cx := {2, 3}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 0, 1, 2, 3]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum33 : ClassDatum :=
  ({(4, 2), (5, 2), (5, 3)}, {(0, 2), (0, 3), (1, 2), (1, 3), (4, 3)})

def record33 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(4, 2), (5, 3)]
  Cx := {2, 3}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 0, 1, 2, 3]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum34 : ClassDatum :=
  ({(4, 2), (4, 3), (5, 3)}, {(0, 2), (0, 3), (1, 2), (1, 3), (5, 2)})

def record34 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(4, 2), (5, 3)]
  Cx := {2, 3}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 0, 1, 2, 3]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum35 : ClassDatum :=
  ({(4, 2), (4, 3), (5, 2), (5, 3)}, {(0, 2), (0, 3), (1, 2), (1, 3)})

def record35 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(4, 2), (5, 3)]
  Cx := {2, 3}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 0, 1, 2, 3]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum36 : ClassDatum :=
  ({(0, 3), (5, 2)}, {(0, 2), (1, 2), (4, 2), (5, 3)})

def record36 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(5, 2), (0, 3)]
  Cx := {1, 2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 0, 2, 3, 1, 4]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum37 : ClassDatum :=
  ({(0, 3), (5, 2), (5, 3)}, {(0, 2), (1, 2), (4, 2)})

def record37 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(5, 2), (0, 3)]
  Cx := {1, 2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 0, 2, 3, 1, 4]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum38 : ClassDatum :=
  ({(1, 3), (5, 2)}, {(0, 2), (0, 3), (1, 2), (4, 2), (5, 3)})

def record38 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(5, 2), (1, 3)]
  Cx := {2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 4, 1, 2, 0, 3]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum39 : ClassDatum :=
  ({(1, 3), (5, 2), (5, 3)}, {(0, 2), (0, 3), (1, 2), (4, 2)})

def record39 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(5, 2), (1, 3)]
  Cx := {2, 3, 4}
  Cz := {0, 1, 4, 5}
  ordX := ![5, 4, 1, 2, 0, 3]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum40 : ClassDatum :=
  ({(4, 3), (5, 2)}, {(0, 2), (0, 3), (1, 2), (1, 3), (4, 2), (5, 3)})

def record40 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(5, 2), (4, 3)]
  Cx := {2, 3}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 0, 1, 3, 2]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum41 : ClassDatum :=
  ({(4, 3), (5, 2), (5, 3)}, {(0, 2), (0, 3), (1, 2), (1, 3), (4, 2)})

def record41 : LeafRecordData (Fin 6) where
  k := 2
  w := ![(5, 2), (4, 3)]
  Cx := {2, 3}
  Cz := {0, 1, 4, 5}
  ordX := ![4, 5, 0, 1, 3, 2]
  ordZ := ![0, 2, 4, 5, 1, 3]

def datum : Fin 42 → ClassDatum
  | 0 => datum0
  | 1 => datum1
  | 2 => datum2
  | 3 => datum3
  | 4 => datum4
  | 5 => datum5
  | 6 => datum6
  | 7 => datum7
  | 8 => datum8
  | 9 => datum9
  | 10 => datum10
  | 11 => datum11
  | 12 => datum12
  | 13 => datum13
  | 14 => datum14
  | 15 => datum15
  | 16 => datum16
  | 17 => datum17
  | 18 => datum18
  | 19 => datum19
  | 20 => datum20
  | 21 => datum21
  | 22 => datum22
  | 23 => datum23
  | 24 => datum24
  | 25 => datum25
  | 26 => datum26
  | 27 => datum27
  | 28 => datum28
  | 29 => datum29
  | 30 => datum30
  | 31 => datum31
  | 32 => datum32
  | 33 => datum33
  | 34 => datum34
  | 35 => datum35
  | 36 => datum36
  | 37 => datum37
  | 38 => datum38
  | 39 => datum39
  | 40 => datum40
  | _ => datum41

def record : Fin 42 → LeafRecordData (Fin 6)
  | 0 => record0
  | 1 => record1
  | 2 => record2
  | 3 => record3
  | 4 => record4
  | 5 => record5
  | 6 => record6
  | 7 => record7
  | 8 => record8
  | 9 => record9
  | 10 => record10
  | 11 => record11
  | 12 => record12
  | 13 => record13
  | 14 => record14
  | 15 => record15
  | 16 => record16
  | 17 => record17
  | 18 => record18
  | 19 => record19
  | 20 => record20
  | 21 => record21
  | 22 => record22
  | 23 => record23
  | 24 => record24
  | 25 => record25
  | 26 => record26
  | 27 => record27
  | 28 => record28
  | 29 => record29
  | 30 => record30
  | 31 => record31
  | 32 => record32
  | 33 => record33
  | 34 => record34
  | 35 => record35
  | 36 => record36
  | 37 => record37
  | 38 => record38
  | 39 => record39
  | 40 => record40
  | _ => record41

def exponent : Fin 42 → ℕ
  | 0 => 6
  | 1 => 3
  | 2 => 1
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 10
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 8
  | 11 => 5
  | 12 => 5
  | 13 => 5
  | 14 => 7
  | 15 => 3
  | 16 => 1
  | 17 => 8
  | 18 => 8
  | 19 => 4
  | 20 => 4
  | 21 => 4
  | 22 => 6
  | 23 => 3
  | 24 => 3
  | 25 => 3
  | 26 => 5
  | 27 => 0
  | 28 => 6
  | 29 => 6
  | 30 => 4
  | 31 => 4
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | 35 => 2
  | 36 => 5
  | 37 => 5
  | 38 => 3
  | 39 => 3
  | 40 => 0
  | _ => 0

def partition : Finset ClassDatum := univ.image datum

end Sarkozy.L20Cap.RectangleCertificate
