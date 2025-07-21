import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc

open ValuativeRel MvPowerSeries

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


variable (π : 𝒪[K])

instance : Finite 𝓀[K] := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp inferInstance).2.2

include K in
noncomputable def residue_size : ℕ := @Fintype.card 𝓀[K] (Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[K]))


structure LubinTateF  where
toFun : PowerSeries 𝒪[K]
trunc_degree_two : PowerSeries.trunc 2 toFun = (Polynomial.C π) * Polynomial.X
mod_pi : toFun.coeff (𝒪[K]) (residue_size K) ≡ 1 [SMOD (IsLocalRing.maximalIdeal (𝒪[K]))]
  ∧ ∀ n, n ≠ (residue_size K) →  toFun.coeff _ n ≡ 0 [SMOD (IsLocalRing.maximalIdeal (𝒪[K]))]

noncomputable section

variable {σ : Type*} [DecidableEq σ] [Finite σ] {R : Type*} [CommRing R]


abbrev deg_map (n : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.invFun (fun _ => n)

abbrev subst_aux (f : PowerSeries R) : σ → MvPowerSeries σ R :=
  (fun i => PowerSeries.subst (X i) f)

def MvPowerSeries.truncDegFun (n : ℕ) (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  MvPowerSeries.truncFun (deg_map n) φ

variable (R) in
def MvPowerSeries.trunc_deg (n : ℕ) := trunc R (deg_map n) (σ := σ)


theorem constructive_lemma (n : ℕ) {ϕ₁ : MvPowerSeries (Fin n) 𝒪[K]}
  {a : Fin n → 𝒪[K]}
  (h_phi₁ : ϕ₁ = ∑ (i : Fin n), (C (Fin n) 𝒪[K] (a i)) * X i)
  (f g : LubinTateF K π)
  :
  ∃! (ϕ : MvPowerSeries (Fin n) 𝒪[K]), trunc_deg (𝒪[K]) 2 ϕ = ϕ₁ ∧
  PowerSeries.subst ϕ f.toFun = subst (subst_aux g.toFun) ϕ := sorry
