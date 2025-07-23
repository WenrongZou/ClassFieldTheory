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

-- /--
-- Given a power series p(X) ∈ R⟦X⟧ and an index i, we may view it as a
-- multivariate power series p(X_i) ∈ R⟦X_1, ..., X_n⟧.
-- -/
-- abbrev PowerSeries.toMvPowerSeries (f : PowerSeries R) (i : σ) : MvPowerSeries σ R :=
--   PowerSeries.subst (MvPowerSeries.X i) f

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

variable (F : LubinTateF K π)

lemma toMvPowerSeries_trunc_degree_two :
    (F.toFun : MvPowerSeries Unit 𝒪[K]).truncTotalDeg 2
      = MvPolynomial.C π * MvPolynomial.X default := by
  rw [truncTotalDeg_powerSeries, (MvPolynomial.pUnitAlgEquiv _).symm_apply_eq]
  simpa using F.trunc_degree_two

lemma toMvPowerSeries_mod_pi :
    MvPowerSeries.C _ _ π ∣ F.toFun - MvPowerSeries.X default ^ Fintype.card 𝓀[K] :=
  F.mod_pi

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
    {a : Fin n → 𝒪[K]} (f g : LubinTateF K π) (r : ℕ) (hr : 2 ≤ r) : ∃! ϕr : MvPolynomial (Fin n) 𝒪[K], ϕr.totalDegree < r
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
    --   sorry
    -- hav_mv : (C _ _) π ∣ f.toFun.subst p.toMvPowerSeries - p.toMvPowerSeries ^ residue_size K := by
    --   sorry

    -- have h₁ : (MvPolynomial.C (Fin n) 𝒪[K]) π ∣ f.toFun.subst p.toMvPowerSeries - p.toMvPowerSeries.subst g.toFun.toMvPowerSeries

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
    ∃! (ϕ : MvPowerSeries (Fin 2) 𝒪[K]), (truncTotalDegHom 2 ϕ)
    = MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) ∧
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

theorem truncTotalDegTwo.X {x : σ} :
  (truncTotalDeg 2 (X x)).toMvPowerSeries = X x (R := R) := by
  sorry

theorem FormalGroup.ext_iff (F₁ F₂ : FormalGroup R) :
  F₁ = F₂ ↔ F₁.toFun = F₂.toFun := by
  constructor
  · intro h
    simp [h]
  · intro h
    sorry

theorem FormalGroup.truncTotalDegTwo (F : FormalGroup R) :
  ((truncTotalDegHom 2) F.toFun) = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  sorry

/-- For every `f ∈ LubinTateF K π`, there is a unique formal group law
  `F_f` with coefficient in `𝒪[K]` admitting `f` as an endomorphism.-/
theorem existence_of_LubinTateFormalGroup (f : LubinTateF K π) :
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
      ·
        simp
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
      simp
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
      simp
      rw [coeff_X, if_neg]
      refine Finsupp.ne_iff.mpr ?_
      use 0
      simp
    assoc := by
      let F_f := choose (constructive_lemma K π 2 phi_supp f f)
      have F_feq : F_f = choose (constructive_lemma K π 2 phi_supp f f) := by
        sorry
      let hf := choose_spec (constructive_lemma K π 2 phi_supp f f)
      obtain ⟨⟨hf₁, hf₂⟩, hf₃⟩ := hf
      rw [←F_feq] at hf₂
      let G₁ := subst (subst_fir F_f) F_f
      let G₂ := subst (subst_sec F_f) F_f
      have G_eq₁ : G₁ = subst (subst_fir F_f) F_f := rfl
      have G_eq₂ : G₂ = subst (subst_sec F_f) F_f := rfl
      -- φ = X 0 + X 1 + X 2
      let φ : MvPolynomial (Fin 3) 𝒪[K] := MvPolynomial.X (0 : Fin 3) +
        MvPolynomial.X 1 + MvPolynomial.X 2
      have phi_supp' : ∀ i ∈ φ.support, Finset.univ.sum ⇑i = 1 := by
        -- same as above
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

          rw [truncTotalDegHom_of_subst, htrunc]
          unfold ϕ₁
          have eq_aux : (subst (subst_fir F_f)
            ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
              MvPolynomial (Fin 2) 𝒪[K]) : MvPowerSeries (Fin 2) 𝒪[K]) (R := 𝒪[K]) )
            = (subst (subst_fir_aux) F_f) + X (2 : Fin 3) := by
            simp
            have has_subst : (constantCoeff _ (𝒪[K]) F_f) = 0 := by
              sorry
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
              rw [truncTotalDegHom_of_subst', htrunc]
              unfold ϕ₁
              simp [subst_add has_subst_fir_aux (X 0) (X 1), subst_X has_subst_fir_aux]
              simp [subst_fir_aux, truncTotalDegHom, Y₀, Y₁, truncTotalDegTwo.X]
            norm_cast at aux
          rw [eq_aux₂, eq_aux₃]
        ·
          rw [G_eq₁]
          have eq_aux₁ : PowerSeries.subst (subst (subst_fir F_f) F_f) f.toFun
            = subst (subst_fir F_f) (PowerSeries.subst F_f f.toFun) := by
            sorry
          rw [eq_aux₁, hf₂]
          let map_aux : Fin 2 → MvPowerSeries (Fin 3) (𝒪[K])
          | ⟨0, _⟩ => PowerSeries.subst (subst subst_fir_aux F_f) f.toFun
          | ⟨1, _⟩ => f.toFun.toMvPowerSeries 2
          have eq_aux₂ : subst (subst_fir F_f) (subst f.toFun.toMvPowerSeries F_f)
            = subst map_aux F_f := by sorry
          -- have eq_aux₃ : PowerSeries.subst (subst subst_fir_aux F_f) f.toFun
          --   =
          rw [eq_aux₂]
          unfold map_aux


          -- use hf₂



          sorry
      -- should be something same as aux₁
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
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 2 phi_supp f f)
      obtain ⟨h₁, h_hom⟩ := h₁
      rw [h_hom]
  }
  refine existsUnique_of_exists_of_unique ?_ ?_
  · use F_f, Hom_f
  · obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma K π 2 phi_supp f f)
    obtain ⟨h₁, h_hom⟩ := h₁
    intro y₁ y₂ hy₁ hy₂
    obtain ⟨α, ha⟩ := hy₁
    obtain ⟨β, hb⟩ := hy₂
    obtain uni₁ := constructive_lemma_two K π f f
    obtain ha₁ := α.hom
    obtain hb₁ := β.hom
    obtain ⟨F_f', h1, h2⟩ := uni₁
    obtain eq₁ := h2 y₁.toFun ⟨FormalGroup.truncTotalDegTwo y₁, by rw [←ha,ha₁]⟩
    obtain eq₂ := h2 y₂.toFun ⟨FormalGroup.truncTotalDegTwo y₂, by rw [←hb,hb₁]⟩
    have toFun_eq : y₁.toFun = y₂.toFun := by
      rw [eq₁, ←eq₂]
    exact (FormalGroup.ext_iff y₁ y₂).mpr toFun_eq







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
