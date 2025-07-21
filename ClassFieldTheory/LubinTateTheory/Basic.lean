import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs

universe u

class IsNonArchLF (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] : Prop extends
  IsTopologicalDivisionRing K,
  LocallyCompactSpace K,
  CompleteSpace K,
  ValuativeTopology K,
  ValuativeRel.IsNontrivial K,
  ValuativeRel.IsRankLeOne K,
  ValuativeRel.IsDiscrete K

variable (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K]

open scoped ValuativeRel

instance : IsDiscreteValuationRing 𝒪[K] :=
  sorry
