import Mathlib
import ClassFieldTheory.GroupCohomology._1_Basic
import ClassFieldTheory.GroupCohomology._2_restriction
import ClassFieldTheory.GroupCohomology._4_TateCohomology_def

/-!
An object `M : Rep R G` is has *trivial cohomology* if
`Hⁿ(S,M)=0` for all `n > 0` and all subgroup `S` of `G`.

`M` has *trivial homology* if for all subgroups `S` and all `n > 0`
we have `Hₙ(S,M) ≅ 0`.

`M` has *trivial Tate cohomology* if for all subgroups `S` and all `n : ℤ`
we have `Hⁿ_{Tate}(S,M) ≅ 0`.

We define these three classes of representation, and prove that they are preserved
by isomorphisms.
-/

open
  CategoryTheory
  CategoryTheory.Limits
  groupCohomology

variable {R G : Type _} [CommRing R]  [Group G]
/--
A representation `M : Rep R G` has trivial cohomology if the cohomology groups `Hⁿ(H,M)`
are zero for every subgroup `H` of `G` and every `n > 0`.
-/
class Rep.TrivialCohomology (M : Rep R G) : Prop where
  zero {H : Type} [Group H] [DecidableEq H] {φ : H →* G} (inj : Function.Injective φ) {n : ℕ} :
    IsZero (groupCohomology (M ↓ φ) (n + 1))

lemma Rep.trivialCohomology_of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialCohomology] :
    M.TrivialCohomology := by
  constructor
  intro H _ _ φ inj n
  have : (functor R H n.succ).obj (M ↓ φ) ≅ (functor R H n.succ).obj (N ↓ φ)
  · apply (functor _ _ n.succ).mapIso
    exact (res φ).mapIso f
  apply IsZero.of_iso _ this
  apply TrivialCohomology.zero inj

class Rep.TrivialHomology (M : Rep R G) : Prop where
  zero {H : Type} [Group H] [DecidableEq H] {φ : H →* G} (inj : Function.Injective φ) {n : ℕ} :
    IsZero (groupHomology (M ↓ φ : Rep R H) (n + 1))

lemma Rep.trivialHomology_of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialHomology] :
    M.TrivialHomology := by
  constructor
  intro S _ _ φ inj n
  have : (groupHomology.functor R S n.succ).obj (M ↓ φ) ≅
      (groupHomology.functor R S n.succ).obj (N ↓ φ)
  · apply (groupHomology.functor R S n.succ).mapIso
    exact (res φ).mapIso f
  apply IsZero.of_iso _ this
  apply TrivialHomology.zero inj

lemma groupCohomology.isZero_of_trivialCohomology [DecidableEq G] {M : Rep R G}
    [M.TrivialCohomology] (n : ℕ) :
    IsZero (groupCohomology M (n + 1)) := by
  apply IsZero.of_iso
  apply Rep.TrivialCohomology.zero (M := M) (φ := (MonoidHom.id G))
  exact fun ⦃a₁ a₂⦄ a ↦ a
  exact n
  apply Iso.refl

class Rep.TrivialTateCohomology [Finite G] (M : Rep R G) : Prop where
  zero {H : Type} [Group H] [DecidableEq H] {φ : H →* G} (inj : Function.Injective φ) {n : ℤ} :
    let _ := Finite.of_injective φ inj
    IsZero ((TateCohomology n).obj (M ↓ φ : Rep R H))

lemma Rep.trivialTateCohomology_of_iso [Finite G] {M N : Rep R G} (f : M ≅ N)
    [N.TrivialTateCohomology] :
    M.TrivialTateCohomology := by
  constructor
  intro S _ _ φ hφ n
  have _ : Finite S := Finite.of_injective φ hφ
  have : (TateCohomology n).obj (M ↓ φ) ≅ (TateCohomology n).obj (N ↓ φ)
  · apply (TateCohomology n).mapIso
    exact (res φ).mapIso f
  apply IsZero.of_iso _ this
  exact TrivialTateCohomology.zero hφ
