import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact

open ValuativeRel

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K]

class IsNonArchLF : Prop extends
  IsTopologicalDivisionRing K,
  LocallyCompactSpace K,
  CompleteSpace K,
  ValuativeTopology K,
  ValuativeRel.IsNontrivial K,
  ValuativeRel.IsRankLeOne K,
  ValuativeRel.IsDiscrete K

variable [IsNonArchLF K]

instance : IsUniformAddGroup K where
  uniformContinuous_sub := sorry

instance : (Valued.v : Valuation K (ValueGroupWithZero K)).IsNontrivial :=
  ValuativeRel.isNontrivial_iff_isNontrivial.mp inferInstance

noncomputable instance : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne where
  hom := IsRankLeOne.nonempty.some.emb
  strictMono' := IsRankLeOne.nonempty.some.strictMono

open scoped Valued in
instance : ProperSpace K :=
  ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K

instance : IsDiscreteValuationRing 𝒪[K] :=
  (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp inferInstance).2.1
