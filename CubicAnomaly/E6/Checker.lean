import CubicAnomaly.E6.Data

/-!
Executable reconstruction of the finite E6 incidence calculation.

The JSON certificate contributes coordinates, six simple-reflection tables,
and one seed for each claimed cell.  This module checks those tables against
the Bourbaki E6 Cartan matrix, reconstructs all relevant orbits, and computes
the incidence statistics independently of the JSON's claimed counts.
-/

namespace CubicAnomaly.E6

open Data

private def expectedCartan : Array (Array Int) := #[
  #[2, 0, -1, 0, 0, 0],
  #[0, 2, 0, -1, 0, 0],
  #[-1, 0, 2, -1, 0, 0],
  #[0, -1, -1, 2, -1, 0],
  #[0, 0, 0, -1, 2, -1],
  #[0, 0, 0, 0, -1, 2]
]

private def expectedHighestRoot : Array Int := #[1, 2, 2, 3, 2, 1]

def rootCount : Nat := roots.size

def maskSize (mask : RootMask) : Nat :=
  (List.range rootCount).countP fun index => mask.testBit index

def maskIndices (mask : RootMask) : Array Nat :=
  ((List.range rootCount).filter fun index => mask.testBit index).toArray

def maskSubset (left right : RootMask) : Bool :=
  (List.range rootCount).all fun index => !left.testBit index || right.testBit index

def properMaskSubset (left right : RootMask) : Bool :=
  left != right && maskSubset left right

def intersectionSize (left right : RootMask) : Nat :=
  maskSize (left &&& right)

def commonMask (triple : Triple) : RootMask :=
  triple.d &&& triple.a &&& triple.theta

def commonSize (triple : Triple) : Nat := maskSize (commonMask triple)

def profile (triple : Triple) : Profile := {
  da := intersectionSize triple.d triple.a
  dtheta := intersectionSize triple.d triple.theta
  atheta := intersectionSize triple.a triple.theta
}

def cellKey (triple : Triple) : CellKey := {
  profile := profile triple
  common := commonSize triple
}

def uniqueArray {α : Type} [BEq α] [Hashable α] (items : Array α) : Bool :=
  (Std.HashSet.ofList items.toList).size == items.size

def generatedOrbit {α : Type} [BEq α] [Hashable α] [Inhabited α]
    (next : α → Array α) (seed : α) : Array α := Id.run do
  let mut seen : Std.HashSet α := Std.HashSet.emptyWithCapacity 64
  let mut queue : Array α := #[seed]
  seen := seen.insert seed
  let mut cursor := 0
  while cursor < queue.size do
    let current := queue[cursor]!
    cursor := cursor + 1
    for image in next current do
      if !seen.contains image then
        seen := seen.insert image
        queue := queue.push image
  return queue

def permuteMask (permutation : Array Nat) (mask : RootMask) : RootMask :=
  (List.range rootCount).foldl (fun result index =>
    if mask.testBit index then
      result ||| Nat.shiftLeft 1 permutation[index]!
    else
      result) 0

def rootIndexNext (index : Nat) : Array Nat :=
  simpleReflections.map fun permutation => permutation[index]!

def maskNext (mask : RootMask) : Array RootMask :=
  simpleReflections.map fun permutation => permuteMask permutation mask

def tripleNext (triple : Triple) : Array Triple :=
  simpleReflections.map fun permutation => {
    d := permuteMask permutation triple.d
    a := permuteMask permutation triple.a
    theta := permuteMask permutation triple.theta
  }

def contextNext (context : Context) : Array Context :=
  simpleReflections.map fun permutation => {
    d := permuteMask permutation context.d
    theta := permuteMask permutation context.theta
  }

def reflectedRoot (root : Array Int) (simple : Nat) : Array Int :=
  let coefficient := (List.range 6).foldl
    (fun total index => total + root[index]! * (cartan[index]!)[simple]!) 0
  (List.range 6).map (fun index =>
    if index == simple then root[index]! - coefficient else root[index]!) |>.toArray

def rootInnerByIndex (left right : Nat) : Int :=
  (List.range 6).foldl (fun outer i =>
    (List.range 6).foldl (fun inner j =>
      inner + (roots[left]!)[i]! * (cartan[i]!)[j]! * (roots[right]!)[j]!) outer
  ) 0

def rootSumByIndex (left right : Nat) : Array Int :=
  (List.range 6).map (fun index =>
    (roots[left]!)[index]! + (roots[right]!)[index]!) |>.toArray

def rootNegationClosed (mask : RootMask) : Bool :=
  (maskIndices mask).all fun index =>
    let negative := roots[index]!.map fun coordinate => -coordinate
    (List.range rootCount).any fun candidate =>
      mask.testBit candidate && roots[candidate]! == negative

def rootAdditionClosed (mask : RootMask) : Bool :=
  let indices := maskIndices mask
  indices.all fun left =>
    indices.all fun right =>
      let sum := rootSumByIndex left right
      (List.range rootCount).all fun candidate =>
        roots[candidate]! != sum || mask.testBit candidate

/-- The bit mask is a closed root subsystem of the fixed E6 root table. -/
def closedRootSubsystem (mask : RootMask) : Bool :=
  rootNegationClosed mask && rootAdditionClosed mask

def rootComponentNext (mask : RootMask) (index : Nat) : Array Nat :=
  ((List.range rootCount).filter fun candidate =>
    mask.testBit candidate && rootInnerByIndex index candidate != 0).toArray

def rootComponent (mask : RootMask) (seed : Nat) : Array Nat :=
  generatedOrbit (rootComponentNext mask) seed

def rootComponents (mask : RootMask) : Array (Array Nat) := Id.run do
  let mut seen : Std.HashSet Nat := Std.HashSet.emptyWithCapacity (maskSize mask)
  let mut components : Array (Array Nat) := #[]
  for index in maskIndices mask do
    if !seen.contains index then
      let component := rootComponent mask index
      for member in component do
        seen := seen.insert member
      components := components.push component
  return components

private def rowPivot (row : Array Int) : Option Nat :=
  (List.range row.size).find? fun index => row[index]! != 0

/-- Fraction-free rank of integer root-coordinate rows. -/
def vectorRank (vectors : Array (Array Int)) : Nat := Id.run do
  let mut basis : Array (Array Int) := #[]
  for vector in vectors do
    let mut row := vector
    for old in basis do
      if let some pivot := rowPivot old then
        let oldPivot := old[pivot]!
        let rowPivotValue := row[pivot]!
        if rowPivotValue != 0 then
          row := (List.range row.size).map (fun index =>
            oldPivot * row[index]! - rowPivotValue * old[index]!) |>.toArray
    if (rowPivot row).isSome then
      basis := basis.push row
  return basis.size

/-- Rank computed from the actual root coordinates, independently of root counts. -/
def rootRank (mask : RootMask) : Nat :=
  vectorRank ((maskIndices mask).map fun index => roots[index]!)

/-- The numerical dimension of the root-generated semisimple algebra: rank plus
root count. Identifying this number with a Lie-algebra dimension uses the usual
root-space dimension formula; no central torus is counted here. -/
def rootGeneratedDimension (mask : RootMask) : Nat :=
  rootRank mask + maskSize mask

/-- Check each pair once, sharing its computed root count and exact rank across
the allowed signatures. Triple-level claims reuse these pair-level results. -/
def pairSignaturesValid (left right : Array RootMask)
    (allowed : Array (Nat × Nat)) : Bool :=
  left.all fun l => right.all fun r =>
    let mask := l &&& r
    let signature := (maskSize mask, rootRank mask)
    allowed.contains signature

/-- Root count and lattice rank of every irreducible component. -/
def rootComponentSignatures (mask : RootMask) : Array (Nat × Nat) :=
  (rootComponents mask).map fun component =>
    (component.size, vectorRank (component.map fun index => roots[index]!))

def componentSignaturesMatch
    (mask : RootMask) (expected : Array (Nat × Nat)) : Bool :=
  let observed := rootComponentSignatures mask
  observed.size == expected.size &&
    expected.all fun signature =>
      observed.toList.count signature == expected.toList.count signature

def permutationValid (permutation : Array Nat) : Bool :=
  permutation.size == rootCount &&
    (List.range rootCount).all fun image => permutation.toList.count image == 1

def reflectionTableValid : Bool :=
  simpleReflections.size == 6 &&
    (List.range 6).all fun simple =>
      let permutation := simpleReflections[simple]!
      permutationValid permutation &&
        (List.range rootCount).all fun index =>
          permutation[index]! < rootCount &&
            roots[permutation[index]!]! == reflectedRoot roots[index]! simple

def nonnegativeRoot (root : Array Int) : Bool :=
  root.size == 6 && (List.range 6).all fun index => 0 ≤ root[index]!

/-- The supplied vector is the greatest positive root in the simple-root order. -/
def highestRootValid : Bool :=
  nonnegativeRoot highestRoot &&
  roots.contains highestRoot &&
  roots.all fun root =>
    !nonnegativeRoot root ||
      (List.range 6).all fun index => root[index]! ≤ highestRoot[index]!

def rootTableValid : Bool :=
  certificateVersion == 8 &&
  cartan == expectedCartan &&
  highestRoot == expectedHighestRoot &&
  highestRootValid &&
  rootCount == 72 &&
  roots.all (fun root => root.size == 6) &&
  uniqueArray roots &&
  simpleRootIndex < rootCount &&
  roots[simpleRootIndex]! == #[1, 0, 0, 0, 0, 0] &&
  reflectionTableValid &&
  (generatedOrbit rootIndexNext simpleRootIndex).size == 72 &&
  (List.range rootCount).all (fun index => rootInnerByIndex index index == 2) &&
  (List.range rootCount).all fun index =>
    roots.any fun candidate => candidate == roots[index]!.map (fun coordinate => -coordinate)

private def firstSeed : Triple := cellSeeds[0]!

def dOrbit : Array RootMask := generatedOrbit maskNext firstSeed.d
def aOrbit : Array RootMask := generatedOrbit maskNext firstSeed.a
def thetaOrbit : Array RootMask := generatedOrbit maskNext firstSeed.theta

/-- Exhaustive pair data for the intrinsic selector. Only 27*36 + 27*40 +
36*40 = 3492 coordinate-rank computations are needed for all 38880 triples.
The expected signatures are checked against the reconstructed intersections;
they do not supply the ranks used in `rootGeneratedDimension`. -/
def intrinsicPairDataValid : Bool :=
  pairSignaturesValid dOrbit aOrbit #[(16, 5), (20, 4)] &&
  pairSignaturesValid dOrbit thetaOrbit #[(10, 4)] &&
  pairSignaturesValid aOrbit thetaOrbit #[(6, 3), (14, 5)]

def subsystemOrbitsValid : Bool :=
  cellSeeds.size == 6 &&
  dOrbit.size == 27 && uniqueArray dOrbit && dOrbit.all (fun mask =>
    maskSize mask == 40 && closedRootSubsystem mask &&
      componentSignaturesMatch mask #[(40, 5)]) &&
  aOrbit.size == 36 && uniqueArray aOrbit && aOrbit.all (fun mask =>
    maskSize mask == 32 && closedRootSubsystem mask &&
      componentSignaturesMatch mask #[(30, 5), (2, 1)]) &&
  thetaOrbit.size == 40 && uniqueArray thetaOrbit && thetaOrbit.all (fun mask =>
    maskSize mask == 18 && closedRootSubsystem mask &&
      componentSignaturesMatch mask #[(6, 2), (6, 2), (6, 2)])

def tripleUniverse : Array Triple := Id.run do
  let mut result : Array Triple := #[]
  for d in dOrbit do
    for a in aOrbit do
      for theta in thetaOrbit do
        result := result.push { d := d, a := a, theta := theta }
  return result

def cellOrbits : Array (Array Triple) :=
  cellSeeds.map fun seed => generatedOrbit tripleNext seed

def cellPartitionValid : Bool := Id.run do
  let mut seen : Std.HashSet Triple := Std.HashSet.emptyWithCapacity 38880
  for orbit in cellOrbits do
    for triple in orbit do
      if seen.contains triple then
        return false
      seen := seen.insert triple
  if seen.size != tripleUniverse.size then
    return false
  return tripleUniverse.all seen.contains

def knownCellKeys : Array CellKey := #[
  { profile := { da := 16, dtheta := 10, atheta := 6 }, common := 2 },
  { profile := { da := 16, dtheta := 10, atheta := 6 }, common := 6 },
  { profile := { da := 16, dtheta := 10, atheta := 14 }, common := 6 },
  { profile := { da := 16, dtheta := 10, atheta := 14 }, common := 10 },
  { profile := { da := 20, dtheta := 10, atheta := 6 }, common := 4 },
  { profile := { da := 20, dtheta := 10, atheta := 14 }, common := 8 }
]

def expectedCellCounts : Array Nat := #[12960, 3240, 3240, 2160, 12960, 4320]

def observedCellCounts : Array Nat :=
  knownCellKeys.map fun key => tripleUniverse.countP fun triple => cellKey triple == key

def cellOrbitClassificationValid : Bool :=
  cellOrbits.size == 6 &&
  uniqueArray (cellOrbits.map fun orbit => cellKey orbit[0]!) &&
  cellOrbits.all (fun orbit =>
    !orbit.isEmpty &&
    let key := cellKey orbit[0]!
    knownCellKeys.contains key &&
    orbit.all (fun triple => cellKey triple == key) &&
    orbit.size == tripleUniverse.countP (fun triple => cellKey triple == key))

def pairwiseMaximal (triple : Triple) : Bool :=
  profile triple == { da := 20, dtheta := 10, atheta := 14 }

def commonMaximal (triple : Triple) : Bool := commonSize triple == 10

def extremaValid : Bool :=
  tripleUniverse.countP pairwiseMaximal == 4320 &&
  tripleUniverse.countP commonMaximal == 2160 &&
  tripleUniverse.all (fun triple =>
    let value := profile triple
    value.da ≤ 20 && value.dtheta ≤ 10 && value.atheta ≤ 14 && commonSize triple ≤ 10)

def hasA2Component (mask : RootMask) : Bool :=
  closedRootSubsystem mask && (rootComponentSignatures mask).contains (6, 2)

def colorClassificationValid : Bool :=
  tripleUniverse.all fun triple =>
    hasA2Component (commonMask triple) == (pairwiseMaximal triple || commonMaximal triple)

def selectedCommonMasks (predicate : Triple → Bool) : Array RootMask :=
  (tripleUniverse.filter predicate).map commonMask

def commonMultiplicityValid (predicate : Triple → Bool)
    (expectedDistinct expectedMultiplicity : Nat) : Bool :=
  let selected := selectedCommonMasks predicate
  let distinct := (Std.HashSet.ofList selected.toList).toArray
  distinct.size == expectedDistinct &&
  distinct.all fun mask => selected.count mask == expectedMultiplicity

def contexts : Array Context := Id.run do
  let mut result : Array Context := #[]
  for d in dOrbit do
    for theta in thetaOrbit do
      result := result.push { d := d, theta := theta }
  return result

def contextOrbit : Array Context :=
  generatedOrbit contextNext { d := firstSeed.d, theta := firstSeed.theta }

def pairwiseAs (context : Context) : Array RootMask :=
  aOrbit.filter fun a => pairwiseMaximal { d := context.d, a := a, theta := context.theta }

def commonAs (context : Context) : Array RootMask :=
  aOrbit.filter fun a => commonMaximal { d := context.d, a := a, theta := context.theta }

def contextValid : Bool :=
  contexts.size == 1080 && uniqueArray contexts &&
  contextOrbit.size == 1080 && uniqueArray contextOrbit &&
  let orbitSet := Std.HashSet.ofList contextOrbit.toList
  contexts.all orbitSet.contains &&
  contexts.all (fun context =>
    let pairwise := pairwiseAs context
    let common := commonAs context
    pairwise.size == 4 && common.size == 2 &&
    let commonMasks := common.map fun a => commonMask { d := context.d, a := a, theta := context.theta }
    commonMasks.size == 2 && commonMasks[0]! == commonMasks[1]!)

structure InclusionSummary where
  labelled : Nat
  distinct : Nat
  allProper : Bool
  pairIntersectionExact : Bool
deriving BEq, DecidableEq, Inhabited, Repr

def inclusionSummary : InclusionSummary := Id.run do
  let mut labelled := 0
  let mut inclusions : Std.HashSet Inclusion := Std.HashSet.emptyWithCapacity 2160
  let mut allProper := true
  let mut pairIntersectionExact := true
  for context in contexts do
    for pairwiseA in pairwiseAs context do
      let smaller := commonMask { d := context.d, a := pairwiseA, theta := context.theta }
      for commonA in commonAs context do
        let larger := commonMask { d := context.d, a := commonA, theta := context.theta }
        labelled := labelled + 1
        allProper := allProper && properMaskSubset smaller larger
        pairIntersectionExact := pairIntersectionExact &&
          ((context.d &&& pairwiseA) &&& (context.d &&& commonA) == smaller)
        inclusions := inclusions.insert { smaller := smaller, larger := larger }
  return {
    labelled := labelled
    distinct := inclusions.size
    allProper := allProper
    pairIntersectionExact := pairIntersectionExact
  }

def inclusionValid : Bool :=
  inclusionSummary == {
    labelled := 8640
    distinct := 2160
    allProper := true
    pairIntersectionExact := true
  }

end CubicAnomaly.E6
