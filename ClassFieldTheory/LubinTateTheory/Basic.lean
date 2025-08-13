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

variable {K : Type u} [Field K] [ValuativeRel K] [UniformSpace K]
  (π : 𝒪[K]) {R : Type*} [CommRing R]

variable (K) in
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

variable {σ : Type*} [DecidableEq σ] [Fintype σ]



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

theorem truncTotalDegEq_powerSeries (n : ℕ) (ϕ : PowerSeries R) :
  truncTotalDegEq n ϕ
    = (MvPolynomial.pUnitAlgEquiv _).symm (Polynomial.monomial n (PowerSeries.coeff _ n ϕ)) := by
  ext w
  simp [coeff_truncTotalDegEq, MvPolynomial.coeff_X_pow]
  split_ifs with h₁ h₂ h₃
  · subst h₂
    rfl
  · subst h₁
    simpa using Finsupp.ext_iff.not.mp h₂
  · subst h₃
    simp at h₁
  · rfl

theorem truncTotalDeg_powerSeries (n : ℕ) (ϕ : PowerSeries R) :
    truncTotalDeg n ϕ = (MvPolynomial.pUnitAlgEquiv _).symm (ϕ.trunc n) := by
  rw [(MvPolynomial.pUnitAlgEquiv _).eq_symm_apply, truncTotalDeg]
  ext d
  simp_rw [truncTotalDegEq_powerSeries, map_sum,
    (MvPolynomial.pUnitAlgEquiv _).apply_symm_apply, PowerSeries.trunc,
    Finset.range_eq_Ico]

lemma MvPowerSeries.truncTotalDeg_map_add (f g : MvPowerSeries σ R) (n : ℕ) :
  truncTotalDeg n (f + g) = truncTotalDeg n f + truncTotalDeg n g := by
  ext m
  rw [MvPolynomial.coeff_add]
  rw [coeff_truncTotalDeg, coeff_truncTotalDeg, coeff_truncTotalDeg]
  split_ifs <;> simp

/--
`MvPowerSeries.truncTotalDeg` as a monoid homomorphism.
-/
def MvPowerSeries.truncTotalDegHom (n : ℕ) : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncTotalDeg n
  map_zero' := by
    simp [truncTotalDeg, truncTotalDegEq]
  map_add' := by
    intro x y
    apply truncTotalDeg_map_add

theorem MvPowerSeries.truncTotalDegHom_apply (n : ℕ) (p : MvPowerSeries σ R) :
    p.truncTotalDegHom n = p.truncTotalDeg n :=
  rfl

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

variable (F : LubinTateF π)

lemma toMvPowerSeries_trunc_degree_two :
    (F.toFun : MvPowerSeries Unit 𝒪[K]).truncTotalDeg 2
      = MvPolynomial.C π * MvPolynomial.X default := by
  rw [truncTotalDeg_powerSeries, (MvPolynomial.pUnitAlgEquiv _).symm_apply_eq]
  simpa using F.trunc_degree_two

lemma toMvPowerSeries_mod_pi :
    MvPowerSeries.C _ _ π ∣ F.toFun - MvPowerSeries.X default ^ Fintype.card 𝓀[K] :=
  F.mod_pi

/-- constant coefficient of `f` in Lubin Tate `F_π` is zero.-/
lemma constantCoeff_LubinTateF : PowerSeries.constantCoeff _ F.toFun = 0 := by
  sorry


end LubinTateF

end LubinTateF

noncomputable section

variable {σ : Type*} {R : Type*} [CommRing R]

section Prop_2_11

namespace MvPowerSeries

lemma C_dvd_iff_forall_dvd_coeff (c : R) (p : MvPowerSeries σ R) :
    (C _ _) c ∣ p ↔ ∀ n, c ∣ (coeff R n) p := by
  constructor <;> intro hp
  · intro n
    obtain ⟨d, rfl⟩ := hp
    simp
  · use fun n ↦ Classical.choose (hp n)
    ext n
    simp
    rw [Classical.choose_spec (hp n)]
    rfl

lemma dvd_prod_pow_sub_prod_pow_of_dvd_sub {d : R} {a b : σ → R}
    (h : ∀ i : σ, d ∣ a i - b i)
    (i : σ →₀ ℕ) :
    d ∣ (i.prod fun j e ↦ a j ^ e) - (i.prod fun j e ↦ b j ^ e) := by
  induction i using Finsupp.induction₂ with
  | zero => simp
  | add_single i e f ha hb₀ ih =>
    rw [Finsupp.prod_add_index_of_disjoint, Finsupp.prod_add_index_of_disjoint,
      Finsupp.prod_single_index, Finsupp.prod_single_index]
    · obtain ⟨q, hq⟩ := ih
      rw [sub_eq_iff_eq_add] at hq
      rw [hq, add_mul, add_sub_assoc, ← mul_sub, mul_assoc]
      apply dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right _ _)
      exact (h i).trans (sub_dvd_pow_sub_pow ..)
    · simp
    · simp
    · apply Finset.disjoint_iff_inter_eq_empty.mpr
      ext w
      simp [Finsupp.single, hb₀]
      contrapose!
      rintro rfl
      simpa using ha
    · apply Finset.disjoint_iff_inter_eq_empty.mpr
      ext w
      simp [Finsupp.single, hb₀]
      contrapose!
      rintro rfl
      simpa using ha

variable [DecidableEq σ] [Fintype σ]

-- Proposition 2.11
lemma constructive_lemma_ind_hyp
    (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
    (hϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
    {a : Fin n → 𝒪[K]} (f g : LubinTateF π) (r : ℕ) (hr : 2 ≤ r) : ∃! ϕr : MvPolynomial (Fin n) 𝒪[K], ϕr.totalDegree < r
        ∧ truncTotalDegHom 2 ϕr = ϕ₁
          ∧ truncTotalDegHom r (f.toFun.subst ϕr.toMvPowerSeries)
            = truncTotalDegHom r (ϕr.toMvPowerSeries.subst g.toFun.toMvPowerSeries) := by
  induction r, hr using Nat.le_induction with
  | base => sorry
  | succ d hd ih =>
    obtain ⟨p, ⟨hp_deg, hp_trunc, hp_comm⟩, hp_unique⟩ := ih
    simp only at hp_unique

    -- f(X) = X^q mod π
    have h₁ := f.toMvPowerSeries_mod_pi
    -- f(X) = πX + ...
    -- have h₂ := f.trunc_degree_two
    -- wts: f ∘ p = p(x1, ..., xn)^q mod π
    have hϕ₁_constantCoeff : ϕ₁.constantCoeff = 0 := by
      contrapose! hϕ₁
      use 0, ?_, by simp
      simpa using hϕ₁
    have hp_constantCoeff : p.constantCoeff = 0 := by
      apply_fun MvPolynomial.coeff 0 at hp_trunc
      rw [truncTotalDegHom_apply, coeff_truncTotalDeg_of_totalDeg_lt _ _ (by simp)] at hp_trunc
      convert hp_trunc
      exact hϕ₁_constantCoeff.symm
    have hp_hasSubst : PowerSeries.HasSubst p.toMvPowerSeries := by
      simpa using hp_constantCoeff
    -- construction: (f ∘ p - p ∘ g) / (π^r - 1)π
    have h_first_term : (C _ _) π ∣ ((PowerSeries.substAlgHom hp_hasSubst) f.toFun - p.toMvPowerSeries ^ Fintype.card 𝓀[K]) := by
      -- f(X) - X^q = π * u(X)
      -- show f(p(x1, ..., xn)) - p(x1, ..., xn)^q = π * u(p(x1, ..., xn))
      obtain ⟨u, hu⟩ := f.mod_pi
      use (PowerSeries.substAlgHom hp_hasSubst) u
      convert congrArg (PowerSeries.substAlgHom hp_hasSubst) hu
      · rw [map_sub, map_pow, PowerSeries.substAlgHom_X]
      · -- TODO: Add this (subst_C) to mathlib
        rw [map_mul, ← Polynomial.coe_C, PowerSeries.substAlgHom_coe, Polynomial.aeval_C]
        rfl
    -- show p(g(x)) = p(x1^q, ..., xn^q) mod π
    have h_second_term_inner {d : ℕ} (i : Fin d) : (C _ _) π ∣ g.toFun.toMvPowerSeries i - X i ^ Fintype.card 𝓀[K] := by
      obtain ⟨u, hu⟩ := g.mod_pi
      use (PowerSeries.substAlgHom (PowerSeries.HasSubst.X i)) u
      convert congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := 𝒪[K]) i)) hu
      · rw [map_sub, map_pow, PowerSeries.substAlgHom_X, PowerSeries.toMvPowerSeries,
          PowerSeries.subst, PowerSeries.substAlgHom, substAlgHom_apply]
      · rw [map_mul, ← Polynomial.coe_C, PowerSeries.substAlgHom_coe, Polynomial.aeval_C]
        rfl
    have h_second_term : (C _ _) π ∣ p.toMvPowerSeries.subst g.toFun.toMvPowerSeries - p.toMvPowerSeries.subst (X · ^ Fintype.card 𝓀[K]) := by
      -- p is a polynomial so we may use MvPolynomial
      rw [subst_coe, subst_coe]
      -- this means we can write stuff like p.sum!
      -- In fact, p(g1(x),g2(x),...)-p(h1(x),h2(x),...) = sum(p_I (g(x)^I-h(x)^I))
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.aeval_def,
        MvPolynomial.eval₂_eq, ← Finset.sum_sub_distrib]
      apply Finset.dvd_sum fun i hi ↦ ?_
      simp_rw [← mul_sub]
      apply dvd_mul_of_dvd_right
      apply dvd_prod_pow_sub_prod_pow_of_dvd_sub h_second_term_inner
    have h_diff_terms : (C _ _) π ∣ p.toMvPowerSeries ^ Fintype.card 𝓀[K] - p.toMvPowerSeries.subst (X · ^ Fintype.card 𝓀[K]) := by
      sorry
    sorry
    --   sorry
    -- hav_mv : (C _ _) π ∣ f.toFun.subst p.toMvPowerSeries - p.toMvPowerSeries ^ residue_size K := by
    --   sorry

    -- have h₁ : (sMvPolynomial.C (Fin n) 𝒪[K]) π ∣ f.toFun.subst p.toMvPowerSeries - p.toMvPowerSeries.subst g.toFun.toMvPowerSeries

-- Proposition 2.11
theorem constructive_lemma
    (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
    (h_ϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
    (f g : LubinTateF π) :
    ∃! ϕ : MvPowerSeries (Fin n) 𝒪[K],
      truncTotalDegHom 2 ϕ = ϕ₁
        ∧ PowerSeries.subst ϕ f.toFun = subst g.toFun.toMvPowerSeries ϕ := by
  sorry

/-- This is constructive lemma in two variable. More specific, given two `f, g ∈ F_π`,
  then there exist unique `ϕ ∈ 𝒪[K]⟦X,Y⟧`, such that `ϕ ≡ X + Y mod (deg 2)` and
  `g (ϕ (X, Y)) = ϕ (f(X), f(Y))`. -/
theorem constructive_lemma_two
    (f g : LubinTateF π) :
    ∃! (ϕ : MvPowerSeries (Fin 2) 𝒪[K]), (truncTotalDegHom 2 ϕ)
    = MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) ∧
    PowerSeries.subst ϕ g.toFun = subst f.toFun.toMvPowerSeries ϕ := by
  let a := fun (x : Fin 2) => 1

  sorry

/-- This is constructive lemma in two variable. More specific, given two `f, g ∈ F_π`,
  then there exist unique `ϕ ∈ 𝒪[K]⟦X,Y⟧`, such that `ϕ ≡ X + Y mod (deg 2)` and
  `g (ϕ (X, Y)) = ϕ (f(X), f(Y))`. -/
theorem constructive_lemma_two'
    (f g : LubinTateF π) (a : 𝒪[K]):
    ∃! (ϕ : MvPowerSeries (Fin 2) 𝒪[K]), (truncTotalDegHom 2 ϕ)
    = MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) + MvPolynomial.C a * MvPolynomial.X (1 : Fin 2) ∧
    PowerSeries.subst ϕ g.toFun = subst f.toFun.toMvPowerSeries ϕ := by
  let a := fun (x : Fin 2) => 1

  sorry






end MvPowerSeries

end Prop_2_11

variable [DecidableEq σ] [Fintype σ]

open LubinTateF

/-- This is a special case from the constructive lemma, namely for `f, g` in the class
  `LubinTateF` and forall element `a : 𝒪[K]` there is a PowerSeries `ϕ`, such that
  truncation of `ϕ` of degree 2 is `a * X`, and `g ∘ ϕ = ϕ ∘ f`-/
theorem constructive_lemma_poly
  (f g : LubinTateF π) (a : 𝒪[K]) :
  ∃! (ϕ : PowerSeries 𝒪[K]), (PowerSeries.trunc 2 ϕ)
  = Polynomial.C a * Polynomial.X  ∧
  PowerSeries.subst ϕ g.toFun = PowerSeries.subst f.toFun ϕ := by
  let a := fun (x : Fin 2) => 1

  sorry

/-- Given `g` a multi variate power series with two variables, `g (X, Y) ≡ g₂ (X, Y) mod (deg 2)`
  as a multi variate power series with two variables, then `g (X, Y) ≡ g₂ (X, Y) mod (deg 2)`
  as a multi variate power series with three variables, where `X, Y` is first two variables.-/
lemma truncTotalDegHom_of_subst' (g : MvPowerSeries (Fin 2) R) (hg : constantCoeff _ _ g = 0) :
  truncTotalDegHom 2 (subst subst_fir_aux g) =
  truncTotalDegHom 2 (subst (subst_fir_aux (R := R)) (truncTotalDegHom 2 g) (R := R)) := by

  sorry

/-- Given `g` a multi variate power series with two variables, `g (X, Y) ≡ g₂ (X, Y) mod (deg 2)`
  as a multi variate power series with two variables, then `g (Y, Z) ≡ g₂ (Y, Z) mod (deg 2)`
  as a multi variate power series with three variables, where `Y, Z` is last two variables.-/
lemma truncTotalDegHom_of_subst₂' (g : MvPowerSeries (Fin 2) R) (hg : constantCoeff _ _ g = 0):
  truncTotalDegHom 2 (subst subst_sec_aux g) =
  truncTotalDegHom 2 (subst (subst_sec_aux (R := R)) (truncTotalDegHom 2 g) (R := R) ):= by
  sorry

/-- Given `f, g` to be multi variate power series with two variable, let
  `f₂(X, Y) ≡ f(X,Y) mod (deg 2)`, and the constant coefficient of `g` is zero,
  then `f (g (X, Y), Z) ≡ f₂ (g (X, Y), Z) mod (deg 2)` -/
lemma truncTotalDegHom_of_subst (f g : MvPowerSeries (Fin 2) R) (hg : constantCoeff _ _ g = 0) :
  truncTotalDegHom 2 (subst (subst_fir g) f) =
  truncTotalDegHom 2 (subst (subst_fir g) (truncTotalDegHom 2 f) (R := R)) := by
  sorry

/-- Given `f, g` to be multi variate power series with two variable, let
  `f₂(X, Y) ≡ f(X,Y) mod (deg 2)`, and the constant coefficient of `g` is zero,
  then `f (X, g (Y, Z)) ≡ f₂ (X, g (Y, Z)) mod (deg 2)` -/
lemma truncTotalDegHom_of_subst₂ (f g : MvPowerSeries (Fin 2) R) (hg : constantCoeff _ _ g = 0) :
  truncTotalDegHom 2 (subst (subst_sec g) f) =
  truncTotalDegHom 2 (subst (subst_sec g) (truncTotalDegHom 2 f) (R := R)) := by
  sorry


/-- truncation of total degree `2` of multi variate power series `X (x : σ)` is `X (x : σ)`. -/
theorem truncTotalDegTwo.X {x : σ}  :
  (truncTotalDeg 2 (X x)).toMvPowerSeries = X x (R := R) := by
  ext d
  simp [truncTotalDeg_eq, MvPolynomial.coeff_sum, coeff_truncTotalDegEq, coeff_X]
  by_cases hd : d = Finsupp.single x 1
  all_goals simp [hd]


/-- Given a formal group law `F (X, Y)` over ring `R`, `F (X, Y)≅ X + Y (mod deg 2)` -/
theorem FormalGroup.truncTotalDegTwo (F : FormalGroup R) :
  ((truncTotalDegHom 2) F.toFun) = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  ext d
  simp [truncTotalDegHom, truncTotalDeg_eq, MvPolynomial.coeff_sum, coeff_truncTotalDegEq]
  by_cases hd : d = Finsupp.single 0 1
  · simp [hd, F.lin_coeff_X]
  · by_cases hd₁ : d = Finsupp.single 1 1
    · simp [hd₁, F.lin_coeff_Y]
    · simp [MvPolynomial.coeff_X', if_neg (Ne.symm hd), if_neg (Ne.symm hd₁)]
      by_cases hd₂ : d = 0
      · simp [hd₂, F.zero_constantCoeff]
      · intro h
        have heq : d 0 + d 1 = d 1 + d 0 := by ring_nf
        interval_cases (d 0 + d 1)
        · have d₀eq : d 0 = 0 := by linarith
          have d₁eq : d 1 = 0 := by linarith
          have deq_zero : d = 0 := by
            ext x
            fin_cases x
            all_goals simp [d₀eq, d₁eq]
          contradiction
        · have d₁eq : (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by
            omega
          obtain deq | deq := d₁eq
          · have hc : d = Finsupp.single 0 1 := by
              ext x
              fin_cases x
              all_goals simp [deq]
            contradiction
          · have hc : d = Finsupp.single 1 1 := by
              ext x
              fin_cases x
              all_goals simp [deq]
            contradiction

theorem truncTotalDeg_smul (f : MvPowerSeries σ R) {a : R} {n : ℕ} : truncTotalDeg n (a • f)
  = a • truncTotalDeg n f := by sorry



/-- For any Multi-variable PowerSeries `f`, assume `d ≥ 1` , then constant coefficient of  truncation of
  total degree `d` of `f` is equal to `f` -/
theorem constantCoeff_of_truncTotalDeg_ge_one (f : MvPowerSeries σ R) {d : ℕ} (hd : d ≥ 1):
  constantCoeff _ R f = MvPolynomial.constantCoeff (truncTotalDegHom d f) := by
  simp [truncTotalDegHom, truncTotalDeg_eq, MvPolynomial.constantCoeff]
  simp_rw [coeff_truncTotalDegEq]
  rw [show (constantCoeff σ R) f = (coeff R 0) f by simp]
  apply Eq.symm
  rw [Finset.sum_eq_single 0]
  simp
  · intro x hx₁ hx₂
    simp
    intro hc
    by_contra
    exact hx₂ (Eq.symm hc)
  · intro hx
    simp
    have hc : 0 ∈ Finset.range d := by
      simp
      linarith
    exfalso
    contradiction

/-- Given a multi variate power series `f` with two variables, assume `f` satisfies the condition
  of Lubin Tate Formal Group condition with respect to `π`. -/
def LubinTateFormalGroupAux (f : LubinTateF π) :  FormalGroup (𝒪[K]) :=
  let ϕ₁ : MvPolynomial (Fin 2) (𝒪[K]) :=
    MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)
  have phi_supp : ∀ i ∈ ϕ₁.support, Finset.univ.sum ⇑i = 1 := by
    intro i
    have supp_eq : ϕ₁.support =
      {(Finsupp.single 0 1), (Finsupp.single 1 1)} := by
      refine Finset.ext_iff.mpr ?_
      intro d
      constructor
      · intro hd
        simp [ϕ₁] at hd ⊢
        by_contra hc
        simp at hc
        obtain ⟨hc₁, hc₂⟩ := hc
        simp [MvPolynomial.coeff_X', Ne.symm hc₁, Ne.symm hc₂] at hd
      · simp
        intro h
        have neg_aux : ¬ Finsupp.single (1 : Fin 2) 1 = Finsupp.single 0 1 := by
          refine Finsupp.ne_iff.mpr ?_
          use 1
          simp
        obtain h1 | h2 := h
        · simp [ϕ₁, MvPolynomial.coeff_X', h1, neg_aux]
        · simp [ϕ₁, MvPolynomial.coeff_X', h2, Ne.symm neg_aux]
    simp [supp_eq]
    intro h
    obtain h1 | h2 := h
    simp [h1]
    simp [h2]
  have phi_eq : ϕ₁ = MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) := rfl
  let F_f := choose (constructive_lemma π 2 phi_supp f f)
  have eq_aux : F_f = choose (constructive_lemma π 2 phi_supp f f) := rfl
  {
  toFun := choose (constructive_lemma π 2 phi_supp f f)
  zero_constantCoeff := by
    obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 2 phi_supp  f f)
    obtain ⟨h₁, h_hom⟩ := h₁
    calc
      _ = (constantCoeff (Fin 2) ↥𝒪[K]) (↑((truncTotalDegHom 2)
        (choose (constructive_lemma π 2 phi_supp f f)))) := by
        unfold truncTotalDegHom
        simp [←coeff_zero_eq_constantCoeff, coeff_truncTotalDeg]
      _ = 0 := by
        rw [h₁]
        simp [ϕ₁]
  lin_coeff_X := by
    obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 2 phi_supp f f)
    obtain ⟨htrunc, hsubst⟩ := h₁
    rw [←eq_aux]  at htrunc ⊢
    have eq_aux₁ : (coeff (↥𝒪[K]) (Finsupp.single 0 1)) F_f
      = (coeff (↥𝒪[K]) (Finsupp.single 0 1)) ϕ₁.toMvPowerSeries := by
      rw [←htrunc]
      simp [truncTotalDegHom, coeff_truncTotalDeg]
    rw [eq_aux₁, phi_eq]
    simp
    rw [coeff_X, if_neg]
    refine Finsupp.ne_iff.mpr ?_
    use 0
    simp
  lin_coeff_Y := by
    obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 2 phi_supp f f)
    obtain ⟨htrunc, hsubst⟩ := h₁
    rw [←eq_aux]  at htrunc ⊢
    have eq_aux₁ : (coeff (↥𝒪[K]) (Finsupp.single 1 1)) F_f
      = (coeff (↥𝒪[K]) (Finsupp.single 1 1)) ϕ₁.toMvPowerSeries := by
      simp [←htrunc, truncTotalDegHom, coeff_truncTotalDeg]
    rw [eq_aux₁, phi_eq]
    simp
    rw [coeff_X, if_neg]
    refine Finsupp.ne_iff.mpr ?_
    use 0
    simp
  assoc := by
    let hf := choose_spec (constructive_lemma π 2 phi_supp f f)
    obtain ⟨⟨hf₁, hf₂⟩, hf₃⟩ := hf
    rw [←eq_aux] at hf₂
    let G₁ := subst (subst_fir F_f) F_f
    let G₂ := subst (subst_sec F_f) F_f
    have G_eq₁ : G₁ = subst (subst_fir F_f) F_f := rfl
    have G_eq₂ : G₂ = subst (subst_sec F_f) F_f := rfl
    -- φ = X 0 + X 1 + X 2
    let φ : MvPolynomial (Fin 3) 𝒪[K] := MvPolynomial.X (0 : Fin 3) +
      MvPolynomial.X 1 + MvPolynomial.X 2
    have phi_eq' : φ = MvPolynomial.X (0 : Fin 3) +
      MvPolynomial.X 1 + MvPolynomial.X 2 := by rfl
    have h_Ff : constantCoeff _ _ F_f = 0 := by
      rw [constantCoeff_of_truncTotalDeg_ge_one _ (show 2 ≥ 1 by norm_num),
        hf₁, phi_eq]
      simp
    have hf_constant : PowerSeries.constantCoeff _ f.toFun = 0 := constantCoeff_LubinTateF _ _
    have phi_supp' : ∀ i ∈ φ.support, Finset.univ.sum ⇑i = 1 := by
      -- same as above
      intro i
      have supp_eq : φ.support =
      {(Finsupp.single 0 1), (Finsupp.single 1 1), (Finsupp.single 2 1)} := by
        refine Finset.ext_iff.mpr ?_
        intro d
        constructor
        · intro hd
          simp [φ] at hd ⊢
          by_contra hc
          simp at hc
          obtain ⟨hc₁, hc₂, hc₃⟩ := hc
          simp [MvPolynomial.coeff_X', Ne.symm hc₁, Ne.symm hc₂, Ne.symm hc₃] at hd
        · simp
          intro h
          obtain h | h | h := h
          all_goals simp [h, phi_eq']
      simp [supp_eq]
      intro hi
      obtain h | h | h := hi
      all_goals simp [h]
    have constantF_f : constantCoeff _ _  F_f = 0  := by
      rw [←eq_aux] at hf₁
      rw [constantCoeff_of_truncTotalDeg_ge_one _ (show 2 ≥ 1 by linarith), hf₁, phi_eq]
      simp
    obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 3 phi_supp' f f)
    obtain G₀ := choose (constructive_lemma π 3 phi_supp' f f)
    obtain ⟨h, hunique⟩ := choose_spec (constructive_lemma π 2 phi_supp f f)
    obtain ⟨htrunc, hsubst⟩ := h
    -- here prove `truncTotalDeg 2 G₁ = φ` and `f (G₁(X, Y, Z)) = G₁ (f(X), f(Y), f(Z))`.
    have aux₁ : ↑((truncTotalDegHom  2) G₁) = φ ∧
      PowerSeries.subst G₁ f.toFun = subst f.toFun.toMvPowerSeries G₁ := by
      constructor
      · rw [truncTotalDegHom_of_subst _ _ h_Ff, htrunc]
        unfold ϕ₁
        have eq_aux : (subst (subst_fir F_f)
          ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
            MvPolynomial (Fin 2) 𝒪[K]) : MvPowerSeries (Fin 2) 𝒪[K]) (R := 𝒪[K]) )
          = (subst (subst_fir_aux) F_f) + X (2 : Fin 3) := by
          simp
          have has_subst : (constantCoeff _ (𝒪[K]) F_f) = 0 := by
            rw [←eq_aux] at hf₁
            simp [constantCoeff_of_truncTotalDeg_ge_one F_f (by linarith) (d := 2), hf₁, phi_eq]
          rw [subst_add (has_subst_fir _ has_subst), subst_X (has_subst_fir _ has_subst),
            subst_X (has_subst_fir _ has_subst)]
        rw [eq_aux]
        simp
        unfold φ
        have eq_aux₂ : ((truncTotalDegHom 2)
          (X (2 : Fin 3)))  = MvPolynomial.X (2 : Fin 3) (R := 𝒪[K]) := by
          simp [truncTotalDegHom]
          refine MvPolynomial.ext_iff.mpr ?_
          intro n
          simp [coeff_truncTotalDeg, MvPolynomial.coeff_X']
          by_cases h1 : Finsupp.single 2 1 = n
          · have haux : Finset.univ.sum ⇑n < 2 := by
              simp [←h1]
            simp [←h1, coeff_X]
          · simp [h1, coeff_X, Ne.symm h1]
        have eq_aux₃ : ((truncTotalDegHom 2) (subst subst_fir_aux F_f))
          = MvPolynomial.X (0 : Fin 3) + MvPolynomial.X (1 : Fin 3) (R := 𝒪[K]) := by
          have aux : ((truncTotalDegHom 2) (subst subst_fir_aux F_f)).toMvPowerSeries
          = (MvPolynomial.X (0 : Fin 3) + MvPolynomial.X (1 : Fin 3) (R := 𝒪[K])).toMvPowerSeries := by
            rw [truncTotalDegHom_of_subst' _ h_Ff, htrunc]
            unfold ϕ₁
            simp [subst_add has_subst_fir_aux (X 0) (X 1), subst_X has_subst_fir_aux]
            simp [subst_fir_aux, truncTotalDegHom, Y₀, Y₁, truncTotalDegTwo.X]
          norm_cast at aux
        rw [eq_aux₂, eq_aux₃]
      ·
        rw [G_eq₁]
        have eq_aux₁ : PowerSeries.subst (subst (subst_fir F_f) F_f) f.toFun
          = subst (subst_fir F_f) (PowerSeries.subst F_f f.toFun) := by
          simp [PowerSeries.subst]
          rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero constantF_f))
            (has_subst_fir F_f constantF_f)]
        rw [eq_aux₁, hf₂]
        let map_aux : Fin 2 → MvPowerSeries (Fin 3) (𝒪[K])
        | ⟨0, _⟩ => PowerSeries.subst (subst subst_fir_aux F_f) f.toFun
        | ⟨1, _⟩ => f.toFun.toMvPowerSeries 2
        have eq_aux₂ : subst (subst_fir F_f) (subst f.toFun.toMvPowerSeries F_f)
          = subst map_aux F_f := by
          rw [subst_comp_subst_apply]
          apply subst_congr
          funext s
          by_cases hs₀ : s = 0
          · unfold subst_fir
            simp [map_aux, hs₀, PowerSeries.toMvPowerSeries, PowerSeries.subst]
            rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 0))
              (has_subst_fir F_f constantF_f)]
            apply subst_congr
            funext t
            rw [subst_X (has_subst_fir F_f constantF_f)]
          · have hs₁ : s = 1 := by omega
            unfold subst_fir
            simp [map_aux, hs₁, PowerSeries.toMvPowerSeries, PowerSeries.subst]
            rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 1))
              (has_subst_fir F_f constantF_f)]
            apply subst_congr
            funext t
            rw [subst_X (has_subst_fir F_f constantF_f)]
          exact (has_subst_toMvPowerSeries hf_constant)
          exact (has_subst_fir F_f constantF_f)
        rw [eq_aux₂]
        unfold map_aux
        let map_aux' : Fin 2 → MvPowerSeries (Fin 3) (𝒪[K])
        | ⟨0, _⟩ => f.toFun.toMvPowerSeries 0
        | ⟨1, _⟩ => f.toFun.toMvPowerSeries 1
        have eq_aux₃ : PowerSeries.subst (subst subst_fir_aux F_f) f.toFun
          = subst map_aux' F_f := by
          have eq_aux : subst subst_fir_aux (PowerSeries.subst F_f f.toFun)
            = subst subst_fir_aux (subst f.toFun.toMvPowerSeries F_f) (S := 𝒪[K]) := by
            rw [hf₂]
          rw [PowerSeries.subst] at eq_aux
          rw [PowerSeries.subst, ←subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun s ↦ constantF_f)
            has_subst_fir_aux , eq_aux, subst_comp_subst_apply (has_subst_toMvPowerSeries hf_constant) has_subst_fir_aux]
          apply subst_congr
          simp [map_aux']
          unfold subst_fir_aux PowerSeries.toMvPowerSeries
          funext s
          by_cases hs₀ : s = 0
          · simp [hs₀]
            unfold PowerSeries.subst
            rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 0)) has_subst_fir_aux]
            apply subst_congr
            funext t
            rw [subst_X has_subst_fir_aux]
          · have hs₁ : s = 1 := by omega
            simp [hs₁]
            rw [PowerSeries.subst, subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 1)) has_subst_fir_aux]
            apply subst_congr
            funext t
            rw [subst_X has_subst_fir_aux ]
        rw [eq_aux₃, subst_comp_subst_apply (has_subst_fir F_f constantF_f) (has_subst_toMvPowerSeries hf_constant)]
        apply subst_congr
        funext x t
        fin_cases x
        · -- the cases `x = 0`
          unfold map_aux' subst_fir subst_fir_aux
          simp
          rw [subst_comp_subst_apply has_subst_fir_aux (has_subst_toMvPowerSeries hf_constant)]
          congr
          funext x' t'
          fin_cases x'
          all_goals rw [subst_X (has_subst_toMvPowerSeries hf_constant)]
        · -- the case `x = 1`
          unfold subst_fir
          simp [Y₂]
          rw [subst_X (has_subst_toMvPowerSeries hf_constant)]

    -- here prove  `truncTotalDegHom 2 G₂ = φ` and `f (G₂ (X, Y, Z)) = G₂ (f (X), f (Y), f (Z))`.
    have aux₂ : ↑((truncTotalDegHom 2) G₂) = φ ∧
      PowerSeries.subst G₂ f.toFun = subst f.toFun.toMvPowerSeries G₂ := by

      constructor
      ·
        rw [truncTotalDegHom_of_subst₂ _ _ h_Ff, htrunc, phi_eq]
        have eq_aux : (subst (subst_sec F_f)
          ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
            MvPolynomial (Fin 2) 𝒪[K]) : MvPowerSeries (Fin 2) 𝒪[K]) (R := 𝒪[K]) )
          = X (0 : Fin 3) + (subst (subst_sec_aux) F_f)  := by
          simp
          have has_subst : (constantCoeff _ (𝒪[K]) F_f) = 0 := by
            rw [←eq_aux] at hf₁
            simp [constantCoeff_of_truncTotalDeg_ge_one F_f (by linarith) (d := 2), hf₁, phi_eq]
          rw [subst_add (has_subst_sec _ has_subst), subst_X (has_subst_sec _ has_subst),
            subst_X (has_subst_sec _ has_subst)]
        rw [eq_aux]
        simp
        unfold φ
        have eq_aux₂ : ((truncTotalDegHom 2)
          (X (0 : Fin 3)))  = MvPolynomial.X (0 : Fin 3) (R := 𝒪[K]) := by
          simp [truncTotalDegHom]
          refine MvPolynomial.ext_iff.mpr ?_
          intro n
          simp [coeff_truncTotalDeg, MvPolynomial.coeff_X']
          by_cases h1 : Finsupp.single 0 1 = n
          · have haux : Finset.univ.sum ⇑n < 2 := by
              simp [←h1]
            simp [←h1, coeff_X]
          · simp [h1, coeff_X, Ne.symm h1]
        have eq_aux₃ : ((truncTotalDegHom 2) (subst subst_sec_aux F_f))
          = MvPolynomial.X (1 : Fin 3) + MvPolynomial.X (2 : Fin 3) (R := 𝒪[K]) := by
          have aux : ((truncTotalDegHom 2) (subst subst_sec_aux F_f)).toMvPowerSeries
          = (MvPolynomial.X (1 : Fin 3) + MvPolynomial.X (2 : Fin 3) (R := 𝒪[K])).toMvPowerSeries := by
            rw [truncTotalDegHom_of_subst₂' _ h_Ff, htrunc]
            unfold ϕ₁
            simp [subst_add has_subst_sec_aux (X 0) (X 1), subst_X has_subst_sec_aux]
            simp [subst_sec_aux, truncTotalDegHom, Y₁, truncTotalDegTwo.X]
          norm_cast at aux
        rw [eq_aux₂, eq_aux₃]
        ring_nf
      ·
        rw [G_eq₂]
        have eq_aux₁ : PowerSeries.subst (subst (subst_sec F_f) F_f) f.toFun
          = subst (subst_sec F_f) (PowerSeries.subst F_f f.toFun) := by
          simp [PowerSeries.subst]
          rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero constantF_f))
            (has_subst_sec F_f constantF_f)]
        rw [eq_aux₁, hf₂, subst_comp_subst_apply (has_subst_sec F_f constantF_f)
          (has_subst_toMvPowerSeries hf_constant), subst_comp_subst_apply
          (has_subst_toMvPowerSeries hf_constant) (has_subst_sec F_f constantF_f)]
        apply subst_congr
        funext x
        fin_cases x
        · -- the case `x = 0`
          simp [subst_sec, Y₀]
          rw [subst_X]
          rw [PowerSeries.toMvPowerSeries, PowerSeries.toMvPowerSeries,
            PowerSeries.subst, subst_comp_subst_apply , PowerSeries.subst]
          apply subst_congr
          funext t
          unfold subst_sec
          rw [subst_X]
          exact has_subst_sec F_f constantF_f
          refine hasSubst_of_constantCoeff_zero ?_
          simp
          exact has_subst_sec F_f constantF_f
          exact has_subst_toMvPowerSeries hf_constant
        · -- the case `x = 1`
          simp [subst_sec]
          unfold subst_sec PowerSeries.toMvPowerSeries PowerSeries.subst
          rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero
            (fun s ↦ constantCoeff_X 1)) (has_subst_sec F_f constantF_f),
            subst_X (has_subst_sec F_f constantF_f)]
          have eq_aux : subst subst_sec_aux (PowerSeries.subst F_f f.toFun) =
            subst subst_sec_aux (subst f.toFun.toMvPowerSeries F_f) (S := 𝒪[K])  := by
            rw [hf₂]
          rw [PowerSeries.subst, subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero fun s ↦ constantF_f)
            has_subst_sec_aux ] at eq_aux
          rw [eq_aux]
          rw [subst_comp_subst_apply (has_subst_toMvPowerSeries hf_constant)
            has_subst_sec_aux, subst_comp_subst_apply has_subst_sec_aux]
          apply subst_congr
          funext t
          fin_cases t
          · -- the case `t = 0`
            unfold subst_sec_aux
            simp
            rw [subst_X, PowerSeries.toMvPowerSeries, PowerSeries.subst,
              subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 0))
              has_subst_sec_aux]
            apply subst_congr
            rw [subst_X has_subst_sec_aux]
            exact has_subst_toMvPowerSeries hf_constant
          · -- the cases `t = 1`
            unfold subst_sec_aux
            simp
            rw [subst_X, PowerSeries.toMvPowerSeries, PowerSeries.subst,
              subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 1))
              has_subst_sec_aux]
            apply subst_congr
            rw [subst_X has_subst_sec_aux]
            exact has_subst_toMvPowerSeries hf_constant
          exact has_subst_toMvPowerSeries hf_constant
    obtain eq_aux₁ := h₂ _ aux₁
    obtain eq_aux₂ := h₂ _ aux₂
    unfold G₁ at eq_aux₁
    unfold G₂ at eq_aux₂
    rw [eq_aux₁, ←eq_aux₂]
}



/-- For every `f ∈ LubinTateF K π`, there is a unique formal group law
  `F_f` with coefficient in `𝒪[K]` admitting `f` as an endomorphism.-/
theorem existence_of_LubinTateFormalGroup (f : LubinTateF π) :
  ∃! (F_f : FormalGroup (𝒪[K])), ∃ (α : FormalGroupHom F_f F_f),
  α.toFun = f.toFun := by
  let ϕ₁ : MvPolynomial (Fin 2) (𝒪[K]) :=
    MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)
  have phi_supp : ∀ i ∈ ϕ₁.support, Finset.univ.sum ⇑i = 1 := by
    intro i
    have supp_eq : ϕ₁.support =
      {(Finsupp.single 0 1), (Finsupp.single 1 1)} := by
      refine Finset.ext_iff.mpr ?_
      intro d
      constructor
      · intro hd
        simp [ϕ₁] at hd ⊢
        by_contra hc
        simp at hc
        obtain ⟨hc₁, hc₂⟩ := hc
        simp [MvPolynomial.coeff_X', Ne.symm hc₁, Ne.symm hc₂] at hd
      · simp
        intro h
        have neg_aux : ¬ Finsupp.single (1 : Fin 2) 1 = Finsupp.single 0 1 := by
          refine Finsupp.ne_iff.mpr ?_
          use 1
          simp
        obtain h1 | h2 := h
        · simp [ϕ₁, MvPolynomial.coeff_X', h1, neg_aux]
        · simp [ϕ₁, MvPolynomial.coeff_X', h2, Ne.symm neg_aux]
    simp [supp_eq]
    intro h
    obtain h1 | h2 := h
    simp [h1]
    simp [h2]
  have phi_eq : ϕ₁ = MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) := rfl
  let F_f : FormalGroup (𝒪[K]) := LubinTateFormalGroupAux π f
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
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 2 phi_supp f f)
      obtain ⟨h₁, h_hom⟩ := h₁
      unfold F_f LubinTateFormalGroupAux
      rw [h_hom]
  }
  refine existsUnique_of_exists_of_unique ?_ ?_
  · use F_f, Hom_f
  · obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 2 phi_supp f f)
    obtain ⟨h₁, h_hom⟩ := h₁
    intro y₁ y₂ hy₁ hy₂
    obtain ⟨α, ha⟩ := hy₁
    obtain ⟨β, hb⟩ := hy₂
    obtain uni₁ := constructive_lemma_two π f f
    obtain ha₁ := α.hom
    obtain hb₁ := β.hom
    obtain ⟨F_f', h1, h2⟩ := uni₁
    obtain eq₁ := h2 y₁.toFun ⟨FormalGroup.truncTotalDegTwo y₁, by rw [←ha,ha₁]⟩
    obtain eq₂ := h2 y₂.toFun ⟨FormalGroup.truncTotalDegTwo y₂, by rw [←hb,hb₁]⟩
    have toFun_eq : y₁.toFun = y₂.toFun := by
      rw [eq₁, ←eq₂]
    exact FormalGroup.ext_iff.mpr toFun_eq




def LubinTateFormalGroup (f : LubinTateF π) :=
  Classical.choose (existence_of_LubinTateFormalGroup π f)

/-- Given a `f ∈ LubinTateF π`, and `F_f` be the unique Lubin Tate Formal Group associate to
  `f`, then the constant coefficient of `F_f` is zero. -/
theorem LubinTateFormalGroup.constantCoeff_zero (f : LubinTateF π) :
  constantCoeff _ _ (LubinTateFormalGroup π f).toFun = 0 := by sorry


theorem LubinTateFormalGroup.endomorphism (f : LubinTateF π) :
  PowerSeries.subst (LubinTateFormalGroup π f).toFun f.toFun =
  subst f.toFun.toMvPowerSeries (LubinTateFormalGroup π f).toFun := by sorry


/-- Given a `f ∈ LubinTateF π`, and `F_f` be the unique Lubin Tate Formal Group associate to
  `f`, then the truncation of total degree `2` of `F_f ∈ 𝒪[K]⟦X, Y⟧` is `X + Y`. -/
theorem LubinTateFormalGroup.truncTotalDegTwo (f : LubinTateF π) :
  truncTotalDeg 2 (LubinTateFormalGroup π f).toFun = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  sorry

theorem truncTotalDeg.PowerSeries_subst_n (f : MvPowerSeries σ R) (g : PowerSeries R) (n : ℕ)
  (hf : constantCoeff _ _ f = 0) : truncTotalDeg n (PowerSeries.subst f g) =
  truncTotalDeg n (PowerSeries.subst f (PowerSeries.trunc n g).toPowerSeries) := by sorry

theorem truncTotalDeg.MvPowerSeries_subst_two
  (f : σ → MvPowerSeries σ  R) (g : MvPowerSeries σ R)
  (hf : ∀ (x : σ), constantCoeff _ _ (f x) = 0) : truncTotalDeg 2 (subst f g) =
  truncTotalDeg 2 (subst f (truncTotalDeg 2 g).toMvPowerSeries) := by sorry


open LubinTateFormalGroup

-- Proposition 2.14
/-- Forall `f, g ∈ F_π` there is a unique power series`[a]_g,f` such that
  `PowerSeries.trunc 2 [a]_g,f = a * X` and `g ∘ [a]_g,f = [a]_g,f ∘ f`, and this
  `[a]_g,f` turn out to be a formal group homomorphim from `F_f` to `F_g`. -/
theorem existence_of_scalar_mul (f g : LubinTateF π) (a : 𝒪[K]) :
  ∃! (scalarHom : FormalGroupHom (LubinTateFormalGroup π f) (LubinTateFormalGroup π g)),
  PowerSeries.trunc 2 scalarHom.toFun = (Polynomial.C a) * (Polynomial.X) ∧
  PowerSeries.subst scalarHom.toFun g.toFun  = PowerSeries.subst f.toFun scalarHom.toFun := by
  /- Existence of homomorphism of formal group induced by `a ∈ 𝒪[K]`.-/
  let scalarHom : FormalGroupHom (LubinTateFormalGroup π f) (LubinTateFormalGroup π g) :=
    let hom_a := choose (constructive_lemma_poly π f g a)
    have hom_a_eq : hom_a = choose (constructive_lemma_poly π f g a) := rfl

    { toFun := choose (constructive_lemma_poly π f g a)
      zero_constantCoeff := by
        obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma_poly π f g a)
        rw [←hom_a_eq] at h₁ ⊢
        obtain ⟨htrunc, hsubst⟩ := h₁
        have aux : (PowerSeries.constantCoeff ↥𝒪[K]) hom_a
          = Polynomial.constantCoeff (PowerSeries.trunc 2 hom_a) := by
          rw [Polynomial.constantCoeff_apply, ←PowerSeries.coeff_zero_eq_constantCoeff,
            PowerSeries.coeff_trunc, if_pos (by norm_num)]
        simp [aux, Polynomial.constantCoeff_apply, htrunc]
      hom := by
        rw [←hom_a_eq]
        obtain ⟨ϕ, h₁, h₂⟩ := constructive_lemma_two' π f g a
        obtain ⟨htrunc, hsubst⟩ := h₁
        simp at h₂
        obtain ⟨hom_a_spec₁, hom_a_spec₂⟩ := choose_spec (constructive_lemma_poly π f g a)
        rw [←hom_a_eq] at hom_a_spec₁ hom_a_spec₂
        obtain ⟨hom_a_trunc, hom_a_subst⟩ := hom_a_spec₁
        have eq_aux₁ : MvPowerSeries.truncTotalDeg 2 (PowerSeries.subst
          (LubinTateFormalGroup π f).toFun hom_a)
          = MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 := by
          rw [truncTotalDeg.PowerSeries_subst_n _ _ 2 (constantCoeff_zero π f), hom_a_trunc]
          simp
          rw [←(PowerSeries.smul_eq_C_mul PowerSeries.X a), PowerSeries.subst_smul
            (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_zero π f)),
            PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero
            (constantCoeff_zero π f)), truncTotalDeg_smul, truncTotalDegTwo,
            MvPolynomial.smul_eq_C_mul _ a]
          ring
        have hom_a_constantCoeff : PowerSeries.constantCoeff _ hom_a = 0 := by
          rw [←PowerSeries.coeff_zero_eq_constantCoeff]
          calc
            _ = Polynomial.coeff (PowerSeries.trunc 2 hom_a) 0 := by
              rw [PowerSeries.coeff_trunc, if_pos (by norm_num)]
            _ = 0 := by
              rw [hom_a_trunc]
              simp
        have eq_aux₂ : truncTotalDeg 2 (subst
          hom_a.toMvPowerSeries (LubinTateFormalGroup π g).toFun)
          = MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 := by
          have aux : ∀ (x : Fin 2), constantCoeff _ _ (hom_a.toMvPowerSeries x) = 0 := by
            intro x
            fin_cases x
            · rw [PowerSeries.toMvPowerSeries, ←coeff_zero_eq_constantCoeff, PowerSeries.coeff_subst
                (PowerSeries.HasSubst.X _)]
              simp
              apply finsum_eq_zero_of_forall_eq_zero
              intro d
              by_cases hd₀ : d = 0
              · simp [hd₀, hom_a_constantCoeff]
              · simp [zero_pow hd₀]
            · rw [PowerSeries.toMvPowerSeries, ←coeff_zero_eq_constantCoeff, PowerSeries.coeff_subst
                (PowerSeries.HasSubst.X _)]
              simp
              apply finsum_eq_zero_of_forall_eq_zero
              intro d
              by_cases hd₀ : d = 0
              · simp [hd₀, hom_a_constantCoeff]
              · simp [zero_pow hd₀]
          rw [truncTotalDeg.MvPowerSeries_subst_two _ _ aux, LubinTateFormalGroup.truncTotalDegTwo]
          simp
          rw [subst_add (hasSubst_of_constantCoeff_zero aux),
            subst_X (hasSubst_of_constantCoeff_zero aux),
            subst_X (hasSubst_of_constantCoeff_zero aux),
            PowerSeries.toMvPowerSeries, PowerSeries.toMvPowerSeries,
            truncTotalDeg_map_add, truncTotalDeg.PowerSeries_subst_n _ _ 2 (constantCoeff_X 0),
            hom_a_trunc]
          simp
          rw [←(PowerSeries.smul_eq_C_mul PowerSeries.X a), PowerSeries.subst_smul
            (PowerSeries.HasSubst.X 0), PowerSeries.subst_X (PowerSeries.HasSubst.X 0),
            truncTotalDeg.PowerSeries_subst_n _ _ 2 (constantCoeff_X 1), hom_a_trunc]
          simp
          rw [←(PowerSeries.smul_eq_C_mul PowerSeries.X a), PowerSeries.subst_smul
            (PowerSeries.HasSubst.X 1), PowerSeries.subst_X (PowerSeries.HasSubst.X 1)]
          ext m
          rw [MvPolynomial.coeff_add]
          rw [coeff_truncTotalDeg, coeff_truncTotalDeg]
          by_cases ha : Finset.univ.sum ⇑m < 2
          · rw [if_pos ha, if_pos ha]
            simp [MvPolynomial.coeff_X']
            by_cases hb : Finsupp.single 0 1 = m
            · have neq : Finsupp.single 1 1 ≠ m := by
                rw [←hb]
                by_contra hc
                have aux' : Finsupp.single (1 : Fin 2) 1 0 = Finsupp.single (0 : Fin 2) 1 0 := by
                  rw [hc]
                simp at aux'
              rw [if_neg neq, if_pos hb, coeff_X, coeff_X, if_neg (Ne.symm neq),
                if_pos (Eq.symm hb)]
              simp
            · by_cases hb' : Finsupp.single 1 1 = m
              rw [if_neg hb, if_pos hb', coeff_X, coeff_X, if_neg (Ne.symm hb),
                if_pos (Eq.symm hb')]
              simp
              rw [if_neg hb', if_neg hb, coeff_X, coeff_X, if_neg (Ne.symm hb),
                if_neg (Ne.symm hb')]
              simp
          · rw [if_neg ha, if_neg ha]
            simp [MvPolynomial.coeff_X']
            have neq₁ : Finsupp.single (0 : Fin 2) 1 ≠ m := by
              simp at ha
              by_contra hc
              have add_aux : m 0 + m 1 = 1 := by
                simp [←hc]
              linarith
            have neq₂ : Finsupp.single (1 : Fin 2) 1 ≠ m := by
              simp at ha
              by_contra hc
              have add_aux : m 0 + m 1 = 1 := by
                simp [←hc]
              linarith
            simp [if_neg neq₁, if_neg neq₂]
        /- `g ∘ hom_a (F_f (X, Y)) = hom_a (F_f (f(X), f(Y)))`. -/
        have eq_aux₃ : PowerSeries.subst (PowerSeries.subst
          (LubinTateFormalGroup π f).toFun hom_a) g.toFun = subst f.toFun.toMvPowerSeries
          (PowerSeries.subst (LubinTateFormalGroup π f).toFun hom_a) := by
          obtain has_subst₃:=  PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero
            (LubinTateFormalGroup.constantCoeff_zero π f))
          obtain has_subst₄ := has_subst_toMvPowerSeries (constantCoeff_LubinTateF π f) (σ := Fin 2)
          obtain has_subst₁ := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_LubinTateF π f)
          obtain has_subst₂ := PowerSeries.HasSubst.of_constantCoeff_zero (LubinTateFormalGroup.constantCoeff_zero π f)
          rw [←PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero'
            hom_a_constantCoeff) (PowerSeries.HasSubst.of_constantCoeff_zero
            (LubinTateFormalGroup.constantCoeff_zero π f)), hom_a_subst,
            PowerSeries.subst_comp_subst_apply has_subst₁ has_subst₂, PowerSeries.subst,
            PowerSeries.subst, PowerSeries.subst,subst_comp_subst_apply has_subst₃ has_subst₄]
          apply subst_congr
          funext s
          rw [←LubinTateFormalGroup.endomorphism, PowerSeries.subst]
        /- `g ∘ F_g (hom_a (X), hom_a (Y)) = F_g (hom_a (f (X)), hom_a (f (Y)))`. -/
        have eq_aux₄ : PowerSeries.subst (subst hom_a.toMvPowerSeries
          (LubinTateFormalGroup π g).toFun) g.toFun = subst f.toFun.toMvPowerSeries
          (subst hom_a.toMvPowerSeries (LubinTateFormalGroup π g).toFun) := by
          obtain has_subst₁ := PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero (LubinTateFormalGroup.constantCoeff_zero π g))
          obtain has_subst₂ := has_subst_toMvPowerSeries hom_a_constantCoeff (σ := Fin 2)
          rw [PowerSeries.subst, ←subst_comp_subst_apply has_subst₁ has_subst₂, ←PowerSeries.subst,
          LubinTateFormalGroup.endomorphism, subst_comp_subst_apply
          (has_subst_toMvPowerSeries (constantCoeff_LubinTateF π g))
          has_subst₂, subst_comp_subst_apply
          has_subst₂ (has_subst_toMvPowerSeries (constantCoeff_LubinTateF π f))]
          apply subst_congr
          funext s
          have subst_eq : subst hom_a.toMvPowerSeries (g.toFun.toMvPowerSeries s)
            = PowerSeries.toMvPowerSeries (PowerSeries.subst hom_a g.toFun) s := by
            simp [PowerSeries.toMvPowerSeries, PowerSeries.subst]
            rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X s))
            has_subst₂, subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero fun s ↦ hom_a_constantCoeff)
            (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X s))]
            apply subst_congr
            funext t
            rw [subst_X has_subst₂]
            rfl
          have subst_eq' : subst f.toFun.toMvPowerSeries (hom_a.toMvPowerSeries s)
            = PowerSeries.toMvPowerSeries (PowerSeries.subst f.toFun hom_a) s := by
            simp [PowerSeries.toMvPowerSeries, PowerSeries.subst]
            rw [subst_comp_subst_apply (PowerSeries.HasSubst.const
            (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_LubinTateF π f)))
            (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X s)), subst_comp_subst_apply
            (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X s))
            (has_subst_toMvPowerSeries (constantCoeff_LubinTateF π f))]
            apply subst_congr
            funext t
            rw [subst_X (has_subst_toMvPowerSeries (constantCoeff_LubinTateF π f))]
            rfl
          rw [subst_eq, hom_a_subst, ←subst_eq']
        obtain eq₁ := h₂ _ eq_aux₁ eq_aux₃
        obtain eq₂ := h₂ _ eq_aux₂ eq_aux₄
        rw [eq₁, ←eq₂]
        }
  use scalarHom
  /- Uniqueness of this homomorphism of formal group induced by `a ∈ 𝒪[K]`. -/
  have scalarHom_eq : scalarHom.toFun = choose (constructive_lemma_poly π f g a) := rfl
  obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma_poly π f g a)
  simp
  constructor
  · exact h₁
  · intro a' ha₁' ha₂'
    apply  FormalGroupHom.ext_iff.mpr
    obtain h1 := h₂ a'.toFun ⟨ha₁',ha₂'⟩
    rw [scalarHom_eq]
    exact h1


/-- -/
def ScalarHom (f g : LubinTateF π) (a : 𝒪[K]) :=
  choose (existence_of_scalar_mul π f g a)

-- variable (a : 𝒪[K]) (f g : LubinTateF π)

-- notation "[" a "]" π f g => choose (existence_of_scalar_mul π f g a)

-- #check [ a ] π f g



-- Proposition 2.15.1
theorem additive_of_ScalarHom (f g : LubinTateF π) (a b : 𝒪[K]) :
  (ScalarHom π f g (a + b)).toFun = (ScalarHom π f g a).toFun +
    (ScalarHom π f g b).toFun := by
  sorry

-- Proposition 2.15.2
theorem multiplicative_of_ScalarHom (f g h : LubinTateF π) (a b : 𝒪[K]) :
  (ScalarHom π f h (a * b)).toFun = PowerSeries.subst (ScalarHom π f g b).toFun
    (ScalarHom π g h a).toFun := by sorry

-- Corollary 2.16
theorem LubinTateFormalGroup_of_SameClass (f g : LubinTateF π) :
  ∃! (α : FormalGroupStrictIso (LubinTateFormalGroup π f) (LubinTateFormalGroup π g)),
  PowerSeries.subst α.toHom.toFun g.toFun = PowerSeries.subst f.toFun α.toHom.toFun := by sorry


-- formalize the Corollary 2.17, give the definition of `End(F_f)`
