import Mathlib

/-!
Small executable types used by the E6 certificate checker.

A subsystem of the 72-root table is encoded by a natural-number bit mask.
This representation keeps the trusted input compact and makes intersections
and equality native operations.
-/

namespace CubicAnomaly.E6

abbrev RootMask := Nat

structure Triple where
  d : RootMask
  a : RootMask
  theta : RootMask
deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure Context where
  d : RootMask
  theta : RootMask
deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure Inclusion where
  smaller : RootMask
  larger : RootMask
deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure Profile where
  da : Nat
  dtheta : Nat
  atheta : Nat
deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure CellKey where
  profile : Profile
  common : Nat
deriving BEq, DecidableEq, Hashable, Inhabited, Repr

end CubicAnomaly.E6
