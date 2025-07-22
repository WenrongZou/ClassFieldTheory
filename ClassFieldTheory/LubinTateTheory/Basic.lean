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
import ClassFieldTheory.LubinTateTheory.FormalGroupLaws.Basic

open ValuativeRel MvPowerSeries Classical

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

-- Proposition 2.11
theorem constructive_lemma (n : ℕ) {ϕ₁ : MvPowerSeries (Fin n) 𝒪[K]}
  {a : Fin n → 𝒪[K]}
  (h_phi₁ : ϕ₁ = ∑ (i : Fin n), (C (Fin n) 𝒪[K] (a i)) * X i)
  (f g : LubinTateF K π) :
  ∃! (ϕ : MvPowerSeries (Fin n) 𝒪[K]), trunc_deg (𝒪[K]) 2 ϕ = ϕ₁ ∧
  PowerSeries.subst ϕ f.toFun = subst (subst_aux g.toFun) ϕ := sorry


/-- For every `f ∈ LubinTateF K π`, there is a unique formal group law
  `F_f` with coefficient in `𝒪[K]` admitting `f` as an endomorphism.-/
theorem existence_of_LubinTateFormalGroup (f : LubinTateF K π) :
  ∃! (F_f : FormalGroup (𝒪[K])), ∃ (α : FormalGroupHom F_f F_f),
  α.toFun = f.toFun := by
  let ϕ₁ : MvPowerSeries (Fin 2) (𝒪[K]) :=
    X (0 : Fin 2) + X (1 : Fin 2)
  let a : Fin 2 → 𝒪[K] := fun _ => 1
  have phi_eq : ϕ₁ = ∑ (i : Fin 2), (C (Fin 2) 𝒪[K] (a i)) * X i := by
    simp [ϕ₁,a]
  let F_f : FormalGroup (𝒪[K]) := {
    toFun := choose (constructive_lemma K π 2 phi_eq f f)
    zero_coeff := by
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 2 phi_eq f f)
      obtain ⟨h₁, h_hom⟩ := h₁
      calc
        _ = (constantCoeff (Fin 2) ↥𝒪[K]) (↑((trunc_deg (↥𝒪[K]) 2)
          (choose (constructive_lemma K π 2 phi_eq f f)))) := by
          unfold trunc_deg deg_map
          simp [←coeff_zero_eq_constantCoeff, coeff_trunc]
          intro h₃
          have contra : 0 < Finsupp.equivFunOnFinite.symm fun (x : Fin 2) ↦ 2 := by
            have aux : 0 < fun (x : Fin 2) ↦ 2 := by
              exact Nat.ofNat_pos'

            exact aux
          contradiction
        _ = 0 := by
          rw [h₁]
          simp [ϕ₁]
    lin_coeff_X := by
      -- maybe we could delete this two part according to milne remark 2.4

      sorry
    lin_coeff_Y := sorry
    assoc := by
      let G₁ := subst (subst_fir (choose (constructive_lemma K π 2 phi_eq f f)))
        (choose (constructive_lemma K π 2 phi_eq f f))
      let G₂ := subst (subst_sec (choose (constructive_lemma K π 2 phi_eq f f)))
        (choose (constructive_lemma K π 2 phi_eq f f))
      let b : Fin 3 → 𝒪[K] := fun x => 1
      let φ : MvPowerSeries (Fin 3) 𝒪[K] := X (0 : Fin 3) + X 1 + X 2
      have phi_eq' : φ = ∑ i, (C (Fin 3) ↥𝒪[K]) (b i) * X i := by
        unfold φ b
        simp [(Fin.sum_univ_three X)]
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 3 phi_eq' f f)
      obtain G₀ := choose (constructive_lemma K π 3 phi_eq' f f)
      have aux₁ : (fun ϕ ↦ ↑((trunc_deg (↥𝒪[K]) 2) ϕ) = φ ∧
        PowerSeries.subst ϕ f.toFun = subst (subst_aux f.toFun) ϕ) G₁ := by
        simp
        constructor
        ·

          sorry
        · sorry

      have aux₂ : (fun ϕ ↦ ↑((trunc_deg (↥𝒪[K]) 2) ϕ) = φ ∧
        PowerSeries.subst ϕ f.toFun = subst (subst_aux f.toFun) ϕ) G₂ := by
        simp
        constructor
        · sorry
        · sorry

      obtain eq_aux₁ := h₂ _ aux₁
      obtain eq_aux₂ := h₂ _ aux₂
      unfold G₁ at eq_aux₁
      unfold G₂ at eq_aux₂
      rw [eq_aux₁, ←eq_aux₂]
  }
  let Hom_f : FormalGroupHom F_f F_f := {
    toFun := f.toFun
    zero_constantCoeff := by
      obtain h₁ := f.trunc_degree_two
      have coeff_aux₁ : (PowerSeries.constantCoeff ↥𝒪[K])
        (PowerSeries.trunc 2 f.toFun) = Polynomial.constantCoeff
        (Polynomial.C π * Polynomial.X) := by
        simp [h₁]
      calc
        _ = (PowerSeries.constantCoeff ↥𝒪[K]) (PowerSeries.trunc 2 f.toFun) := by
          simp [PowerSeries.coeff_trunc]
        _ = 0 := by
          simp [coeff_aux₁]
    hom := by
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 2 phi_eq f f)
      obtain ⟨h₁, h_hom⟩ := h₁
      have map_eq_aux : subst_aux f.toFun = subst_hom f.toFun := by
        ext x t
        congr
        unfold subst_aux subst_hom
        by_cases hx0 : x = 0
        · simp [hx0]
        · simp [show x = 1 by omega]
      rw [←map_eq_aux, h_hom]
  }
  refine existsUnique_of_exists_of_unique ?_ ?_
  · use F_f, Hom_f
  ·
    obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 2 phi_eq f f)
    obtain ⟨h₁, h_hom⟩ := h₁

    sorry




def LubinTateFormalGroup (f : LubinTateF K π) :=
  Classical.choose (existence_of_LubinTateFormalGroup K π f)

-- Proposition 2.14
theorem existence_of_scalar_mul (f g : LubinTateF K π) (a : 𝒪[K]) :
  ∃! (scalarHom : FormalGroupHom (LubinTateFormalGroup K π f) (LubinTateFormalGroup K π g)),
  PowerSeries.trunc 2 scalarHom.toFun = (Polynomial.C a) * (Polynomial.X) ∧
  PowerSeries.subst scalarHom.toFun g.toFun  = PowerSeries.subst f.toFun scalarHom.toFun := by sorry


def ScalarHom (f g : LubinTateF K π) (a : 𝒪[K]) :=
  Classical.choose (existence_of_scalar_mul K π f g a)

-- Proposition 2.15.1
theorem additive_of_ScalarHom (f g : LubinTateF K π) (a b : 𝒪[K]) :
  (ScalarHom K π f g (a + b)).toFun = (ScalarHom K π f g a).toFun + (ScalarHom K π f g b).toFun := by
  sorry

-- Proposition 2.15.2
theorem multiplicative_of_ScalarHom (f g h : LubinTateF K π) (a b : 𝒪[K]) :
  (ScalarHom K π f h (a * b)).toFun = PowerSeries.subst (ScalarHom K π f g b).toFun
    (ScalarHom K π g h a).toFun := by sorry

-- Corollary 2.16
theorem LubinTateFormalGroup_of_SameClass (f g : LubinTateF K π) :
  ∃! (α : FormalGroupStrictIso (LubinTateFormalGroup K π f) (LubinTateFormalGroup K π g)),
  PowerSeries.subst α.toHom.toFun g.toFun = PowerSeries.subst f.toFun α.toHom.toFun := by sorry


-- formalize the Corollary 2.17, give the definition of `End(F_f)`
