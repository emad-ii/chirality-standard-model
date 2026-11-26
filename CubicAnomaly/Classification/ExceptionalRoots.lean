import Std.Data.HashSet.Basic

/-!
# Shared exact exceptional root generator

This is the unchanged integral Cartan-data and reflection-closure generator
used by the exceptional census. Keeping its pure definitions separate allows
the constructive root and Lie-algebra proofs to import only their required
mathematics. No census assertion or root-classification premise is added.
-/

namespace CubicAnomaly.Classification.Exceptional

abbrev RootCoordinates := Array Int
abbrev Grading := Array Int

structure RootDatum where
  cartan : Array (Array Int)
  symmetrizer : Array Int

def g2Datum : RootDatum := {
  cartan := #[#[2, -1], #[-3, 2]]
  symmetrizer := #[1, 3]
}

def f4Datum : RootDatum := {
  cartan := #[
    #[2, -1, 0, 0],
    #[-1, 2, -2, 0],
    #[0, -1, 2, -1],
    #[0, 0, -1, 2]
  ]
  symmetrizer := #[2, 2, 1, 1]
}

def e6Datum : RootDatum := {
  cartan := #[
    #[2, 0, -1, 0, 0, 0],
    #[0, 2, 0, -1, 0, 0],
    #[-1, 0, 2, -1, 0, 0],
    #[0, -1, -1, 2, -1, 0],
    #[0, 0, 0, -1, 2, -1],
    #[0, 0, 0, 0, -1, 2]
  ]
  symmetrizer := #[1, 1, 1, 1, 1, 1]
}

def e7Datum : RootDatum := {
  cartan := #[
    #[2, 0, -1, 0, 0, 0, 0],
    #[0, 2, 0, -1, 0, 0, 0],
    #[-1, 0, 2, -1, 0, 0, 0],
    #[0, -1, -1, 2, -1, 0, 0],
    #[0, 0, 0, -1, 2, -1, 0],
    #[0, 0, 0, 0, -1, 2, -1],
    #[0, 0, 0, 0, 0, -1, 2]
  ]
  symmetrizer := #[1, 1, 1, 1, 1, 1, 1]
}

def e8Datum : RootDatum := {
  cartan := #[
    #[2, 0, -1, 0, 0, 0, 0, 0],
    #[0, 2, 0, -1, 0, 0, 0, 0],
    #[-1, 0, 2, -1, 0, 0, 0, 0],
    #[0, -1, -1, 2, -1, 0, 0, 0],
    #[0, 0, 0, -1, 2, -1, 0, 0],
    #[0, 0, 0, 0, -1, 2, -1, 0],
    #[0, 0, 0, 0, 0, -1, 2, -1],
    #[0, 0, 0, 0, 0, 0, -1, 2]
  ]
  symmetrizer := #[1, 1, 1, 1, 1, 1, 1, 1]
}

private def indices (n : Nat) : List Nat := List.range n

private def simpleRoot (rank index : Nat) : RootCoordinates :=
  (indices rank).map (fun j => if j = index then 1 else 0) |>.toArray

private def negRoot (root : RootCoordinates) : RootCoordinates :=
  root.map (fun coordinate => -coordinate)

private def addRoot
    (left right : RootCoordinates) : RootCoordinates :=
  (indices left.size).map (fun i => left[i]! + right[i]!) |>.toArray

private def reflectRoot
    (datum : RootDatum) (root : RootCoordinates) (simple : Nat) :
    RootCoordinates :=
  let coefficient := (indices datum.cartan.size).foldl
    (fun total j => total + root[j]! * (datum.cartan[j]!)[simple]!) 0
  (indices datum.cartan.size).map (fun j =>
    if j = simple then root[j]! - coefficient else root[j]!) |>.toArray

private def closure {α : Type} [BEq α] [Hashable α] [Inhabited α]
    (next : α → Array α) (seeds : Array α) : Array α := Id.run do
  let mut seen : Std.HashSet α := Std.HashSet.emptyWithCapacity 256
  let mut queue : Array α := #[]
  for seed in seeds do
    if !seen.contains seed then
      seen := seen.insert seed
      queue := queue.push seed
  let mut cursor := 0
  while cursor < queue.size do
    let current := queue[cursor]!
    cursor := cursor + 1
    for image in next current do
      if !seen.contains image then
        seen := seen.insert image
        queue := queue.push image
  return queue

/-- Generate a finite exceptional root system from its simple roots. -/
def roots (datum : RootDatum) : Array RootCoordinates :=
  let rank := datum.cartan.size
  let seeds := (Array.range rank).foldl (fun acc i =>
    let root := simpleRoot rank i
    (acc.push root).push (negRoot root)) #[]
  closure (fun root =>
    (Array.range rank).map (reflectRoot datum root)) seeds

end CubicAnomaly.Classification.Exceptional
