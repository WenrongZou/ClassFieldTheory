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
  (π : 𝒪[K]) {R : Type*} [CommRing R]

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

noncomputable section

variable {σ : Type*} [DecidableEq σ] [Fintype σ] {R : Type*} [CommRing R]

/--
Given a power series p(X) ∈ R⟦X⟧ and an index i, we may view it as a
multivariate power series p(X_i) ∈ R⟦X_1, ..., X_n⟧.
-/
abbrev PowerSeries.toMvPowerSeries (f : PowerSeries R) (i : σ) : MvPowerSeries σ R :=
  PowerSeries.subst (MvPowerSeries.X i) f

/-- The part of a multivariate power series with total degree n.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `truncTotalDeg R n p` is the multivariable power series obtained from `p`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `∑ a_i = n`.

TODO: FIX NAME
TODO: Remove [Fintype σ] typeclass requirement
-/
def MvPowerSeries.truncTotalDegEq (n : ℕ) (p : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ Finset.univ.finsuppAntidiag n, MvPolynomial.monomial m (coeff R m p)

lemma MvPowerSeries.truncTotalDegEq_eq (n : ℕ) (p : MvPowerSeries σ R) :
    p.truncTotalDegEq n
      = ∑ m ∈ Finset.univ.finsuppAntidiag n, MvPolynomial.monomial m (coeff R m p) :=
  rfl

/-- The part of a multivariate power series with total degree at most n.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `truncTotalDeg R n p` is the multivariable power series obtained from `p`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `∑ a_i ≤ n`.
-/
def MvPowerSeries.truncTotalDeg (n : ℕ) (p : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ i ∈ Finset.range n, p.truncTotalDegEq i

lemma MvPowerSeries.truncTotalDeg_eq (n : ℕ) (p : MvPowerSeries σ R) :
    p.truncTotalDeg n = ∑ i ∈ Finset.range n, p.truncTotalDegEq i :=
  rfl

theorem coeff_truncTotalDegEq (n : ℕ) (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncTotalDegEq n φ).coeff m = if Finset.univ.sum m = n then coeff R m φ else 0 := by
  simp [truncTotalDegEq, MvPolynomial.coeff_sum]

theorem coeff_truncTotalDeg (n : ℕ) (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncTotalDeg n φ).coeff m = if Finset.univ.sum m < n then coeff R m φ else 0 := by
  simp_rw [truncTotalDeg, MvPolynomial.coeff_sum, coeff_truncTotalDegEq,
    Finset.sum_ite_eq, Finset.mem_range]

theorem coeff_truncTotalDegEq_of_totalDeg_eq (n : ℕ) (m : σ →₀ ℕ) (hm : Finset.univ.sum m = n) (φ : MvPowerSeries σ R) :
    (truncTotalDegEq n φ).coeff m = coeff R m φ := by
  simp only [coeff_truncTotalDegEq, hm, if_true]

theorem coeff_truncTotalDeg_of_totalDeg_lt (n : ℕ) (m : σ →₀ ℕ) (hm : Finset.univ.sum m < n) (φ : MvPowerSeries σ R) :
    (truncTotalDeg n φ).coeff m = coeff R m φ := by
  simp only [coeff_truncTotalDeg, hm, if_true]

-- #check PowerSeries.monomial
-- theorem truncTotalDeg_powerSeries (n : ℕ) (ϕ : PowerSeries R) :
--     truncTotalDegEq n ϕ
--       = (MvPolynomial.pUnitAlgEquiv _).symm (Polynomial.monomial n (PowerSeries.coeff _ n ϕ)) := by
--   ext w
--   simp [coeff_truncTotalDegEq, MvPolynomial.coeff_X_pow]
--   split_ifs with h₁ h₂
--   · subst h₂
--     simp

theorem truncTotalDeg_powerSeries (n : ℕ) (ϕ : PowerSeries R) :
    truncTotalDeg n ϕ = (MvPolynomial.pUnitAlgEquiv _).symm (ϕ.trunc n) := by
  rw [(MvPolynomial.pUnitAlgEquiv _).eq_symm_apply]
  ext d
  simp_rw [PowerSeries.coeff_trunc, truncTotalDeg, map_sum, truncTotalDegEq,
    map_sum, MvPolynomial.pUnitAlgEquiv_monomial, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial]
  sorry

/--
`MvPowerSeries.truncTotalDeg` as a monoid homomorphism.
-/
def MvPowerSeries.truncTotalDegHom (n : ℕ) : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncTotalDeg n
  map_zero' := by
    simp [truncTotalDeg, truncTotalDegEq]
  map_add' := by
    intro x y
    ext m
    rw [MvPolynomial.coeff_add]
    rw [coeff_truncTotalDeg, coeff_truncTotalDeg, coeff_truncTotalDeg]
    split_ifs <;> simp

end

section LubinTateF

variable (π : 𝒪[K])

instance : Finite 𝓀[K] := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp inferInstance).2.2
noncomputable instance : Fintype 𝓀[K] := Fintype.ofFinite _

structure LubinTateF where
  toFun : PowerSeries 𝒪[K]
  trunc_degree_two : PowerSeries.trunc 2 toFun = Polynomial.C π * Polynomial.X
  mod_pi : PowerSeries.C _ π ∣ toFun - PowerSeries.X ^ Fintype.card 𝓀[K]

namespace LubinTateF

variable (F : LubinTateF K π)

lemma toMvPowerSeries_trunc_degree_two :
    (F.toFun : MvPowerSeries Unit 𝒪[K]).truncTotalDeg 2
      = MvPolynomial.C π * MvPolynomial.X default := by
  rw [truncTotalDeg_powerSeries, (MvPolynomial.pUnitAlgEquiv _).symm_apply_eq]
  sorry
  -- convert F.trunc_degree_two

lemma toMvPowerSeries_mod_pi :
    MvPowerSeries.C _ _ π ∣ F.toFun - MvPowerSeries.X default ^ Fintype.card 𝓀[K] :=
  F.mod_pi

end LubinTateF

end LubinTateF

noncomputable section

variable {σ : Type*} [DecidableEq σ] [Fintype σ] {R : Type*} [CommRing R]

section Prop_2_11

namespace MvPowerSeries

-- Proposition 2.11
lemma constructive_lemma_ind_hyp
    (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
    (h_ϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
    {a : Fin n → 𝒪[K]} (f g : LubinTateF K π) (r : ℕ) (hr : 2 ≤ r) :
    ∃! ϕr : MvPolynomial (Fin n) 𝒪[K],
      ϕr.totalDegree < r
        ∧ truncTotalDegHom 2 ϕr = ϕ₁
          ∧ truncTotalDegHom r (f.toFun.subst ϕr.toMvPowerSeries)
            = truncTotalDegHom r (ϕr.toMvPowerSeries.subst g.toFun.toMvPowerSeries) := by
  induction r, hr using Nat.le_induction with
  | base => sorry
  | succ n hmn ih =>
    obtain ⟨p, ⟨hp_deg, hp_trunc, hp_comm⟩, hp_unique⟩ := ih
    simp only at hp_unique

    -- f(X) = X^q mod π
    have h₁ := f.mod_pi
    -- f(X) = πX + ...
    have h₂ := f.trunc_degree_two
    -- wts: f ∘ p = p(x1, ..., xn)^q
    sorry
    -- hav_mv : (C _ _) π ∣ f.toFun.subst p.toMvPowerSeries - p.toMvPowerSeries ^ residue_size K := by
    --   sorry


    -- have h₁ : (MvPolynomial.C (Fin n) 𝒪[K]) π ∣ f.toFun.subst p.toMvPowerSeries - p.toMvPowerSeries.subst g.toFun.toMvPowerSeries
#check MvPowerSeries.subst

-- Proposition 2.11
theorem constructive_lemma
    (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
    (h_ϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
    (f g : LubinTateF K π) :
    ∃! ϕ : MvPowerSeries (Fin n) 𝒪[K],
      truncTotalDegHom 2 ϕ = ϕ₁
        ∧ PowerSeries.subst ϕ f.toFun = subst g.toFun.toMvPowerSeries ϕ := by
  sorry


theorem constructive_lemma_two
    (f g : LubinTateF K π) :
    ∃! (ϕ : MvPowerSeries (Fin 2) 𝒪[K]), ((truncTotalDegHom 2 ϕ) : MvPowerSeries (Fin 2) 𝒪[K])
    = X (0 : Fin 2) + X (1 : Fin 2) ∧
    PowerSeries.subst ϕ f.toFun = subst g.toFun.toMvPowerSeries ϕ := by
  let a := fun (x : Fin 2) => 1

  sorry


lemma truncTotalDegHom_of_subst (f g : MvPowerSeries (Fin 2) R) :
  truncTotalDegHom 2 (subst (subst_fir g) f) =
  truncTotalDegHom 2 (subst (subst_fir g) (truncTotalDegHom 2 f) (R := R)) := by
  sorry

lemma truncTotalDegHom_of_subst' (g : MvPowerSeries (Fin 2) R) :
  truncTotalDegHom 2 (subst subst_fir_aux g) =
  truncTotalDegHom 2 (subst (subst_fir_aux (R := R)) (truncTotalDegHom 2 g) (R := R) ):= by
  sorry

end MvPowerSeries

end Prop_2_11

/-- For every `f ∈ LubinTateF K π`, there is a unique formal group law
  `F_f` with coefficient in `𝒪[K]` admitting `f` as an endomorphism.-/
theorem existence_of_LubinTateFormalGroup (f : LubinTateF K π) :
  ∃! (F_f : FormalGroup (𝒪[K])), ∃ (α : FormalGroupHom F_f F_f),
  α.toFun = f.toFun := by
  let ϕ₁ : MvPolynomial (Fin 2) (𝒪[K]) :=
    MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)
  have phi_supp : ∀ i ∈ ϕ₁.support, Finset.univ.sum ⇑i = 1 := by
    sorry
  have phi_eq :ϕ₁ = MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) := rfl
  let F_f : FormalGroup (𝒪[K]) := {
    toFun := choose (constructive_lemma K π 2 phi_supp f f)
    zero_coeff := by
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 2 phi_supp  f f)
      obtain ⟨h₁, h_hom⟩ := h₁
      calc
        _ = (constantCoeff (Fin 2) ↥𝒪[K]) (↑((truncTotalDegHom 2)
          (choose (constructive_lemma K π 2 phi_supp f f)))) := by
          unfold truncTotalDegHom
          simp [←coeff_zero_eq_constantCoeff, coeff_truncTotalDeg]
        _ = 0 := by
          rw [h₁]
          simp [ϕ₁]
    lin_coeff_X := by
      -- maybe we could delete this two part according to milne remark 2.4
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 2 phi_supp f f)
      let F_f := choose (constructive_lemma K π 2 phi_supp f f)
      have eq_aux : F_f = choose (constructive_lemma K π 2 phi_supp f f) := rfl
      obtain ⟨htrunc, hsubst⟩ := h₁
      rw [←eq_aux]  at htrunc ⊢
      have eq_aux₁ : (coeff (↥𝒪[K]) (Finsupp.single 0 1)) F_f
        = (coeff (↥𝒪[K]) (Finsupp.single 0 1)) ϕ₁.toMvPowerSeries := by
        rw [←htrunc]
        simp [truncTotalDegHom, coeff_truncTotalDeg]
      rw [eq_aux₁, phi_eq]
      simp  [a]
      rw [coeff_X, if_neg]
      refine Finsupp.ne_iff.mpr ?_
      use 0
      simp
    lin_coeff_Y := by
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 2 phi_supp f f)
      let F_f := choose (constructive_lemma K π 2 phi_supp f f)
      have eq_aux : F_f = choose (constructive_lemma K π 2 phi_supp f f) := rfl
      obtain ⟨htrunc, hsubst⟩ := h₁
      rw [←eq_aux]  at htrunc ⊢
      have eq_aux₁ : (coeff (↥𝒪[K]) (Finsupp.single 1 1)) F_f
        = (coeff (↥𝒪[K]) (Finsupp.single 1 1)) ϕ₁.toMvPowerSeries := by
        rw [←htrunc]
        simp [truncTotalDegHom, coeff_truncTotalDeg]
      rw [eq_aux₁, phi_eq]
      simp  [a]
      rw [coeff_X, if_neg]
      refine Finsupp.ne_iff.mpr ?_
      use 0
      simp
    assoc := by
      let G₁ := subst (subst_fir (choose (constructive_lemma K π 2 phi_supp f f)))
        (choose (constructive_lemma K π 2 phi_supp f f))
      let G₂ := subst (subst_sec (choose (constructive_lemma K π 2 phi_supp f f)))
        (choose (constructive_lemma K π 2 phi_supp f f))
      let b : Fin 3 → 𝒪[K] := fun x => 1
      -- φ = X 0 + X 1 + X 2
      let φ : MvPolynomial (Fin 3) 𝒪[K] := MvPolynomial.X (0 : Fin 3) +
        MvPolynomial.X 1 + MvPolynomial.X 2
      have phi_supp' : ∀ i ∈ φ.support, Finset.univ.sum ⇑i = 1 := by
        sorry
      have phi_eq' : φ = MvPolynomial.X (0 : Fin 3) +
        MvPolynomial.X 1 + MvPolynomial.X 2 := by rfl
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 3 phi_supp' f f)
      obtain G₀ := choose (constructive_lemma K π 3 phi_supp' f f)
      obtain ⟨h, hunique⟩ := choose_spec (constructive_lemma K π 2 phi_supp f f)
      obtain ⟨htrunc, hsubst⟩ := h
      have aux₁ : (fun ϕ ↦ ↑((truncTotalDegHom  2) ϕ) = φ ∧
        PowerSeries.subst ϕ f.toFun = subst f.toFun.toMvPowerSeries ϕ) G₁ := by
        simp
        constructor
        ·
          let choose_f := choose (constructive_lemma K π 2 phi_supp f f)
          rw [truncTotalDegHom_of_subst, htrunc]
          unfold ϕ₁
          have eq_aux : (subst (subst_fir choose_f)
            ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
              MvPolynomial (Fin 2) 𝒪[K]) : MvPowerSeries (Fin 2) 𝒪[K]) (R := 𝒪[K]) )
            = (subst (subst_fir_aux) choose_f) + X (2 : Fin 3) := by
            sorry
          rw [eq_aux]
          simp
          unfold φ
          have eq_aux₂ : MvPolynomial.toMvPowerSeries ((truncTotalDegHom 2)
            (X (2 : Fin 3)))  = X (2 : Fin 3) := by
            simp [truncTotalDegHom]
            refine MvPowerSeries.ext_iff.mpr ?_
            intro n
            simp [coeff_truncTotalDeg]
            intro h
            simp [coeff_X]
            refine Finsupp.ne_iff.mpr ?_
            by_contra hc
            simp at hc
            have aux : Finset.univ.sum ⇑n = 1 := by
              simp [hc]
            linarith
          have eq_aux₃ : MvPolynomial.toMvPowerSeries
            ((truncTotalDegHom (↥𝒪[K]) 2) (subst subst_fir_aux choose_f))
            = X (0 : Fin 3) + X (1 : Fin 3) := by
            rw [truncTotalDegHom_of_subst', htrunc]
            unfold ϕ₁
            rw [subst_add has_subst_fir_aux (X 0) (X 1), subst_X has_subst_fir_aux, subst_X has_subst_fir_aux]
            simp [subst_fir_aux, truncTotalDegHom, Y₀, Y₁]
            ext d
            simp [coeff_truncTotalDeg, coeff_X]
            by_cases deq1 : d = Finsupp.single (0 : Fin 3) 1
            · simp [deq1]
            by_cases deq2 : d = Finsupp.single (1 : Fin 3) 1
            · simp [deq2]
            simp [deq1, deq2]
          simp [eq_aux₃,eq_aux₂]
        ·


          sorry

      have aux₂ : (fun ϕ ↦ ↑((truncTotalDegHom 2) ϕ) = φ ∧
        PowerSeries.subst ϕ f.toFun = subst f.toFun.toMvPowerSeries ϕ) G₂ := by
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
      have map_eq_aux : f.toFun.toMvPowerSeries = subst_hom f.toFun := by
        ext x t
        congr
        unfold subst_hom
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
    intro y₁ y₂ hy₁ hy₂
    obtain ⟨α, ha⟩ := hy₁
    obtain ⟨β, hb⟩ := hy₂
    obtain uni₁ := constructive_lemma_two K π f f
    obtain ha₁ := α.hom
    obtain ⟨F_f', h1, h2⟩ := uni₁
    have eq_aux_y₁ : MvPolynomial.toMvPowerSeries ((truncTotalDegHom (↥𝒪[K]) 2) y₁.toFun) = X (0 : Fin 2) + X 1 := by
      sorry
    have eq_aux_y₂ : MvPolynomial.toMvPowerSeries ((truncTotalDegHom (↥𝒪[K]) 2) y₂.toFun) = X 0 + X 1 := by
      sorry
    have eq_aux_y : (fun ϕ ↦ ↑((truncTotalDegHom (↥𝒪[K]) 2) ϕ : MvPowerSeries (Fin 2) 𝒪[K]) = X 0 + X 1 ∧ PowerSeries.subst ϕ f.toFun = subst (subst_aux f.toFun) ϕ)
      y₁.toFun := by
      sorry
    have eq_aux_y' : (fun ϕ ↦ ↑((truncTotalDegHom (↥𝒪[K]) 2) ϕ : MvPowerSeries (Fin 2) 𝒪[K]) = X 0 + X 1 ∧ PowerSeries.subst ϕ f.toFun = subst (subst_aux f.toFun) ϕ)
      y₂.toFun := by
      sorry
    obtain eq₁ := h2 y₁.toFun eq_aux_y
    obtain eq₂ := h2 y₂.toFun eq_aux_y'



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
