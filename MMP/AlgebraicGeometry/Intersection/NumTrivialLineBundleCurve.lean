module

import MMP.AlgebraicGeometry.Intersection.EulerPolynomialGenericRank
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Cohomology.ProperCoherentSections
public import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.PlaneConic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerThickenings
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericDominantDimensionFormula
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecQuotientInSite
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionFromCechVanishing

/-!
# Numerically trivial line bundles on curves with vanishing `H¹(𝒪)`

**Numerically trivial line bundles on a curve with `H¹(𝒪) = 0`.** Let `F` be a connected
projective scheme of dimension at most one over `k` with `H¹(F, 𝒪_F) = 0`. An invertible sheaf
`L` of degree zero on every integral closed curve of `F` is trivial. Restriction to the
reduction `F_red`, cut out by the nilradical `J`, is injective on isomorphism classes of
invertible sheaves: `H¹(F, J) = 0`, and in characteristic zero the truncated exponential
identifies `1 + J` with `J`. On `F_red`, `χ(L|_{F_red}) = χ(𝒪_{F_red}) = 1`, so `L|_{F_red}` has a
nonzero section, which by degree zero and connectedness vanishes nowhere.

## Main results

* `MMP.Mori.nonempty_iso_unit_of_degreeOn_eq_zero`: a numerically trivial invertible sheaf on a
  connected projective curve with `H¹(𝒪) = 0` is isomorphic to the structure sheaf.

## Implementation notes

The reduced irreducible components of `F` of dimension one are exactly its integral closed
subschemes of dimension one, so the curve hypothesis is stated for every closed immersion
`i : C ⟶ F` from an integral scheme `C` of dimension at most one; on a closed point the degree
of an invertible sheaf vanishes automatically. The properness of `C` over `k`, which
`MMP.Mori.degreeOn` takes as an instance, is a binder of the hypothesis; it always holds. The
degree is `MMP.Mori.degreeOn`, and `H¹(F, 𝒪_F)` is `AlgebraicGeometry.cohomologyOverField`.

The injectivity of `Pic F → Pic F_red` is proved globally, by a Čech argument on an affine cover
with the exponential `J ≅ 1 + J`, and not through the filtration by powers of `J`:
`H¹(J^i/J^{i+1})` need not vanish.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, 3.22–3.23
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

section CurveFibre

open TopologicalSpace Opposite CategoryTheory.Limits
open Stacks.SheafOfModules (nonvanishingLocus sectionsOfTop)
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

/-- `H¹` of the structure sheaf of a closed subscheme of a proper scheme of dimension at most one
vanishes once that of the ambient scheme does: `H¹(F, 𝒪_F) → H¹(F, i_* 𝒪_Z)` is onto because
`H²` of the ideal sheaf vanishes. -/
private theorem subsingleton_H1_subscheme (k : Type u) [Field k] {F : Scheme.{u}}
    (f : F ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim F ≤ 1)
    (hH1 : Subsingleton (cohomologyOverField k f (SheafOfModules.unit F.ringCatSheaf) 1))
    (I : F.IdealSheafData) :
    Subsingleton (cohomologyOverField k (I.subschemeι ≫ f)
      (SheafOfModules.unit I.subscheme.ringCatSheaf) 1) := by
  obtain ⟨hz, hT⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact I
  have h2 := isZero_cohomologyOverField_of_topologicalKrullDim_le k f
    (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom) (d := 1) (i := 2) hdim
    (by omega)
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence k f hT
  have := ModuleCat.subsingleton_of_isZero h2
  have hsurj : Function.Surjective (cohomologyOverFieldMap k f
      (ShortComplex.mk _ _ hz).g 1) := fun b => (hgd 1 b).mp (Subsingleton.elim _ _)
  have e := cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k I.subschemeι f
    (SheafOfModules.unit I.subscheme.ringCatSheaf) 1
  have h3 : Subsingleton (cohomologyOverField k f
      ((Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) 1) := by
    have : Subsingleton (cohomologyOverField k f
        (SheafOfModules.unit (structureSheafRing F.toRingedSpace)) 1) := hH1
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [Subsingleton.elim a' b']
  exact (e.toLinearEquiv.toEquiv.subsingleton_congr).mpr h3

/-- A numerically trivial invertible sheaf has degree zero on every closed subscheme of
dimension at most one: the degree is a sum of degrees on integral components. -/
private theorem curveDegree_subscheme_eq_zero (k : Type u) [Field k] {F : Scheme.{u}}
    (f : F ⟶ Spec (.of k)) [IsProper f] (I : F.IdealSheafData)
    (hI : topologicalKrullDim I.subscheme ≤ 1)
    (L : F.Modules) [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L]
    (hL : ∀ (C : Scheme.{u}) (i : C ⟶ F) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ f)] (hC : topologicalKrullDim C ≤ 1), MMP.Mori.degreeOn k f i hC L = 0) :
    invertibleCurveDegree k (I.subschemeι ≫ f) hI ((Scheme.Modules.pullback I.subschemeι).obj L)
      = 0 := by
  rw [← intersectionNumber_one_eq_invertibleCurveDegree k f I.subschemeι hI L,
    intersectionNumber_eq_sum_dimComponents k f I.subschemeι 1 hI (fun _ => L)]
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  obtain ⟨hW, -, hWd⟩ := W.2
  have hle : topologicalKrullDim W.1.subscheme ≤ 1 := by simp [hWd]
  have key : ∀ h, intersectionNumber k f W.1.subschemeι 1 h (fun _ => L) = 0 := fun h => by
    rw [intersectionNumber_one_eq_invertibleCurveDegree k f W.1.subschemeι h L]
    exact hL W.1.subscheme W.1.subschemeι hle
  exact mul_eq_zero_of_right _ (key _)

/-- On a proper scheme of dimension at most one the Euler characteristic is `h⁰ - h¹`. -/
private theorem finsum_finrank_cohomologyOverField_eq_sub (k : Type u) [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim Z ≤ 1) (M : Z.Modules) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k g M n) : ℤ)) =
      (Module.finrank k (cohomologyOverField k g M 0) : ℤ) -
        Module.finrank k (cohomologyOverField k g M 1) := by
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, sub_eq_add_neg]
  · intro n hn
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    have h2 := isZero_cohomologyOverField_of_topologicalKrullDim_le k g M (d := 1) (i := n)
      hdim (by omega)
    have := ModuleCat.subsingleton_of_isZero h2
    exact hn.2 (by simp [Module.finrank_zero_of_subsingleton])

/-- `H⁰` of the structure sheaf of a nonempty proper scheme is nonzero. -/
private theorem nontrivial_H0_unit (k : Type u) [Field k] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    [IsProper g] [Nonempty Z] :
    Nontrivial (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 0) := by
  have h : Nontrivial Γ(SheafOfModules.unit Z.ringCatSheaf, ⊤) :=
    (inferInstance : Nontrivial Γ(Z, ⊤))
  have e := (cohomologyOverFieldZeroLinearIso k g (SheafOfModules.unit
      Z.ringCatSheaf)).toLinearEquiv
  have : Nontrivial ((restrictScalarsOverBase k g).obj
      ((SheafOfModules.evaluation Z.ringCatSheaf (Opposite.op ⊤)).obj
        (SheafOfModules.unit Z.ringCatSheaf))) := h
  exact e.toEquiv.nontrivial

/-- An invertible sheaf of degree zero on a nonempty proper scheme of dimension at most one with
`H¹(𝒪) = 0` has a nonzero global section (`χ(M) = χ(𝒪) = h⁰(𝒪) ≥ 1`). -/
private theorem nontrivial_sections_of_curveDegree_eq_zero (k : Type u) [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [IsProper g] [Nonempty Z] (hdim : topologicalKrullDim Z ≤ 1)
    (hH1 : Subsingleton (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 1))
    (M : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M]
    (hdeg : invertibleCurveDegree k g hdim M = 0) : Nontrivial Γ(M, ⊤) := by
  by_contra hns
  have hsub : Subsingleton Γ(M, ⊤) := not_nontrivial_iff_subsingleton.mp hns
  have h0M : Limits.IsZero (cohomologyOverField k g M 0) :=
    letI : Subsingleton ((restrictScalarsOverBase k g).obj
        ((SheafOfModules.evaluation Z.ringCatSheaf (Opposite.op (⊤ : Z.Opens))).obj M)) := hsub
    Limits.IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
      (cohomologyOverFieldZeroLinearIso k g M)
  have hM0 : Module.finrank k (cohomologyOverField k g M 0) = 0 := by
    have := ModuleCat.subsingleton_of_isZero h0M
    exact Module.finrank_zero_of_subsingleton
  have hO1 : Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 1)
      = 0 := Module.finrank_zero_of_subsingleton
  have : Nontrivial (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 0) :=
    nontrivial_H0_unit k g
  have : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g
  have hfin := finiteDimensional_cohomologyOverField_of_isProper k g
    (SheafOfModules.unit Z.ringCatSheaf) 0
  have hpos := Module.finrank_pos (R := k)
    (M := cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 0)
  have hdeg' : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k g M n) : ℤ)) -
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k g
          (SheafOfModules.unit Z.ringCatSheaf) n) : ℤ) = 0 := hdeg
  rw [finsum_finrank_cohomologyOverField_eq_sub k g hdim M,
    finsum_finrank_cohomologyOverField_eq_sub k g hdim (SheafOfModules.unit Z.ringCatSheaf)]
    at hdeg'
  omega

/-- The nonvanishing-locus argument of Stacks Tag 0E22, for a reduced connected proper scheme of
dimension at most one: a nonzero section of an invertible sheaf of nonpositive degree on every
irreducible component trivialises it. (The source's equidimensionality is not used.) -/
private theorem isTrivial_of_nontrivial_sections_of_curveDegree_nonpos (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X]
    [ConnectedSpace X] (hdim : topologicalKrullDim (X : Type u) ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Nontrivial Γ(L, ⊤)]
    (hdeg : ∀ (C : Set X) (hC : C ∈ irreducibleComponents (X : Type u)),
      haveI : SheafOfModules.IsInvertible
          (Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subscheme.presheaf
          (Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subscheme.ringCatSheaf.2
          ((RingedSpaceModuleAdjunction.modulePullback
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι.toLRSHom.toShHom).obj
            L) :=
        RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme _ L
      invertibleCurveDegree k
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι ≫ f)
          ((StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι).trans hdim)
          ((RingedSpaceModuleAdjunction.modulePullback
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι.toLRSHom.toShHom).obj
            L) ≤ 0) :
    SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.2 L := by
  classical
  obtain ⟨s, hs⟩ := exists_ne (0 : Γ(L, ⊤))
  have _ : ∀ x : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace x) :=
    X.isLocalRing
  have hLs : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  set sf : L.sections := sectionsOfTop L s
  set U : Set X := nonvanishingLocus (X := X.toRingedSpace) L sf
  have hUopen : IsOpen U := Stacks.SheafOfModules.isOpen_nonvanishingLocus
    (X := X.toRingedSpace) L sf
  have hUne : U.Nonempty := nonempty_nonvanishingLocus_of_ne_zero L s hs
  have hcov : ∀ x : X, ∀ C ∈ irreducibleComponents (X : Type u), x ∈ C → x ∈ U → C ⊆ U :=
    fun x C hC hxC hxU => subset_nonvanishingLocus_of_mem_nonvanishingLocus k f hdim L hC
      (hdeg C hC) sf hxC hxU
  have hfin : (irreducibleComponents (X : Type u)).Finite := by
    have _ : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
    have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have _ : IsNoetherian X := {}
    exact finite_irreducibleComponents_of_isNoetherian
  have hUeq : U = ⋃₀ {C | C ∈ irreducibleComponents (X : Type u) ∧ C ⊆ U} := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp
        (show x ∈ ⋃₀ irreducibleComponents (X : Type u) by
          rw [sUnion_irreducibleComponents]; exact Set.mem_univ x)
      exact Set.mem_sUnion.mpr ⟨C, ⟨hC, hcov x C hC hxC hx⟩, hxC⟩
    · obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hx
      exact hC.2 hxC
  have hUclosed : IsClosed U := by
    rw [hUeq, Set.sUnion_eq_biUnion]
    exact (hfin.subset fun C hC => hC.1).isClosed_biUnion fun C hC =>
      isClosed_of_mem_irreducibleComponents C hC.1
  exact isTrivial_of_nonvanishingLocus_eq_univ L sf (IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUne)

/-- Every global function on a connected reduced proper `k`-scheme, `k` algebraically closed, is
a constant. -/
private theorem surjective_structMap_of_connected_reduced (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [ConnectedSpace X] [IsReduced X] :
    Function.Surjective (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom : k →+* Γ(X, ⊤)) := by
  have hF := open Stacks.AlgebraicGeometry.ProperSectionsGeom in
    isField_globalSections_of_connectedSpace_of_isReduced k f
  letI : Field Γ(X, ⊤) := hF.toField
  haveI : IsDomain Γ(X, ⊤) := @Field.isDomain _ hF.toField
  letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : Algebra.IsIntegral k Γ(X, ⊤) := ⟨fun x => by
    rw [_root_.IsIntegral, RingHom.algebraMap_toAlgebra]
    exact Stacks.AlgebraicGeometry.ProperGeomConnected.isIntegral_toSpecΓ_algebraMap f x⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2

/-- Global functions on a connected reduced closed subscheme are restrictions of global
functions of the ambient proper scheme (the constants). -/
private theorem surjective_appTop_of_connected_reduced (k : Type u) [Field k] [IsAlgClosed k]
    {F : Scheme.{u}} (f : F ⟶ Spec (.of k)) [IsProper f]
    (I : F.IdealSheafData) [ConnectedSpace I.subscheme] [IsReduced I.subscheme] :
    Function.Surjective I.subschemeι.appTop := by
  have hp : IsProper (I.subschemeι ≫ f) := inferInstance
  have := surjective_structMap_of_connected_reduced (X := I.subscheme) k (I.subschemeι ≫ f)
  intro y
  obtain ⟨c, hc⟩ := this y
  refine ⟨((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c, ?_⟩
  rw [← hc]
  have e : (Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ f).appTop =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫ I.subschemeι.appTop := by
    rw [Scheme.Hom.comp_appTop, Category.assoc]
  rw [e]
  rfl

/-- `H¹(F, J) = 0` for the ideal sheaf `J` of a connected reduced closed subscheme, given
`H¹(F, 𝒪_F) = 0`: `H⁰(𝒪_F) → H⁰(𝒪_Z) = k` is onto. -/
private theorem subsingleton_H1_ideal (k : Type u) [Field k] [IsAlgClosed k] {F : Scheme.{u}}
    (f : F ⟶ Spec (.of k)) [IsProper f]
    (hH1 : Subsingleton (cohomologyOverField k f (SheafOfModules.unit F.ringCatSheaf) 1))
    (I : F.IdealSheafData) [ConnectedSpace I.subscheme] [IsReduced I.subscheme] :
    Subsingleton (cohomologyOverField k f
      (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom) 1) := by
  obtain ⟨hz, hT⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact I
  obtain ⟨d, -, -, hgd, hdf⟩ := exists_cohomologyOverField_longExactSequence k f hT
  have hsurj0 : Function.Surjective (cohomologyOverFieldMap k f
      (ShortComplex.mk _ _ hz).g 0) := by
    intro y
    obtain ⟨z', hz'⟩ := surjective_appTop_of_connected_reduced k f I
      (cohomologyOverFieldZeroEquivSections k f _ y)
    refine ⟨(cohomologyOverFieldZeroEquivSections k f _).symm z', ?_⟩
    apply (cohomologyOverFieldZeroEquivSections k f _).injective
    refine (cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f
      (Stacks.IdealSheafSequence.divisorQuotientMap I) _).trans ?_
    erw [Equiv.apply_symm_apply]
    exact hz'
  have h2 : Subsingleton (cohomologyOverField k f
      (SheafOfModules.unit (structureSheafRing F.toRingedSpace)) 1) := hH1
  refine ⟨fun x y => ?_⟩
  have key : ∀ x : cohomologyOverField k f
      (ShortComplex.mk _ _ hz).X₁ 1, x = 0 := by
    intro x
    have hx : cohomologyOverFieldMap k f (ShortComplex.mk _ _ hz).f 1 x = 0 :=
      Subsingleton.elim _ _
    obtain ⟨w, hw⟩ := (hdf 0 x).mp hx
    obtain ⟨v, rfl⟩ := hsurj0 w
    rw [← hw]
    exact (hgd 0 _).mpr ⟨v, rfl⟩
  rw [key x, key y]

section Exponential

open IsNilpotent

/-- `exp b ≡ 1 + b` modulo `J^{m+1}` for `b ∈ J^m`. -/
private theorem exp_sub_one_sub_mem {R : Type*} [CommRing R] [Algebra ℚ R] {J : Ideal R} {N : ℕ}
    (hJ : J ^ N = ⊥) {m : ℕ} (hm : 1 ≤ m) {b : R} (hb : b ∈ J ^ m) :
    exp b - 1 - b ∈ J ^ (m + 1) := by
  have hbJ : b ∈ J := Ideal.pow_le_self (by omega) hb
  have hJ2 : J ^ (N + 2) = ⊥ := by
    rw [pow_add, hJ, Ideal.bot_mul]
  have hbN : b ^ (N + 2) = 0 := by
    have : b ^ (N + 2) ∈ J ^ (N + 2) := Ideal.pow_mem_pow hbJ _
    rw [hJ2] at this
    simpa using this
  rw [exp_eq_sum hbN, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
    one_smul, zero_add]
  have : ∑ i ∈ Finset.range N, ((i + 1 + 1).factorial : ℚ)⁻¹ • b ^ (i + 1 + 1) ∈ J ^ (m + 1) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : b ^ (i + 1 + 1) ∈ J ^ (m * (i + 2)) := by
      rw [pow_mul]; exact Ideal.pow_mem_pow hb _
    have h2 : J ^ (m * (i + 2)) ≤ J ^ (m + 1) := Ideal.pow_le_pow_right (by nlinarith)
    have h3 : ((i + 1 + 1).factorial : ℚ)⁻¹ • b ^ (i + 1 + 1) =
        algebraMap ℚ R ((i + 1 + 1).factorial : ℚ)⁻¹ * b ^ (i + 1 + 1) := by
      rw [Algebra.smul_def]
    rw [h3]
    exact Ideal.mul_mem_left _ _ (h2 h1)
  convert this using 1
  ring

private theorem exp_sub_one_mem {R : Type*} [CommRing R] [Algebra ℚ R] {J : Ideal R} {N : ℕ}
    (hJ : J ^ N = ⊥) {a : R} (ha : a ∈ J) : exp a - 1 ∈ J := by
  have := exp_sub_one_sub_mem hJ (m := 1) le_rfl (by simpa using ha)
  have h2 : exp a - 1 = (exp a - 1 - a) + a := by ring
  rw [h2]
  exact J.add_mem (Ideal.pow_le_self (by omega) this) ha

/-- Every element of `1 + J` is an exponential of an element of `J`, for `J` nilpotent in a
`ℚ`-algebra. -/
private theorem exists_exp_eq_of_sub_one_mem {R : Type*} [CommRing R] [Algebra ℚ R]
    {J : Ideal R} {N : ℕ} (hJ : J ^ N = ⊥) {u : R} (hu : u - 1 ∈ J) : ∃ a ∈ J, exp a = u := by
  have key : ∀ m : ℕ, ∃ a ∈ J, u - exp a ∈ J ^ (m + 1) := by
    intro m
    induction m with
    | zero => exact ⟨0, J.zero_mem, by simpa using hu⟩
    | succ m ih =>
      obtain ⟨a, haJ, hw⟩ := ih
      set w := u - exp a with hwdef
      have hwJ : w ∈ J := Ideal.pow_le_self (by omega) hw
      refine ⟨a + w, J.add_mem haJ hwJ, ?_⟩
      have hnil : ∀ x ∈ J, IsNilpotent x := fun x hx =>
        ⟨N, by simpa [hJ] using Ideal.pow_mem_pow hx N⟩
      rw [exp_add_of_commute (Commute.all _ _) (hnil a haJ) (hnil w hwJ)]
      have ht := exp_sub_one_sub_mem hJ (m := m + 1) (by omega) hw
      have : u - exp a * exp w = w * (1 - exp a) - exp a * (exp w - 1 - w) := by
        rw [hwdef]; ring
      rw [this]
      refine Ideal.sub_mem _ ?_ (Ideal.mul_mem_left _ _ ht)
      have h1 : 1 - exp a ∈ J := by
        have := exp_sub_one_mem hJ haJ
        simpa using J.neg_mem this
      rw [_root_.pow_succ]
      exact Ideal.mul_mem_mul hw h1
  obtain ⟨a, haJ, hw⟩ := key N
  refine ⟨a, haJ, ?_⟩
  have : J ^ (N + 1) = ⊥ := by rw [_root_.pow_succ, hJ, Ideal.bot_mul]
  rw [this] at hw
  exact (sub_eq_zero.mp (by simpa using hw)).symm

/-- The exponential is injective on a nilpotent ideal of a `ℚ`-algebra. -/
private theorem eq_zero_of_exp_eq_one {R : Type*} [CommRing R] [Algebra ℚ R] {J : Ideal R} {N : ℕ}
    (hJ : J ^ N = ⊥) {a : R} (haJ : a ∈ J) (h : exp a = 1) : a = 0 := by
  have key : ∀ m : ℕ, a ∈ J ^ (m + 1) := by
    intro m
    induction m with
    | zero => simpa using haJ
    | succ m ih =>
      have := exp_sub_one_sub_mem hJ (m := m + 1) (by omega) ih
      rw [h] at this
      simpa using this
  have h2 : J ^ (N + 1) = ⊥ := by rw [_root_.pow_succ, hJ, Ideal.bot_mul]
  simpa [h2] using key N

/-- In a Noetherian `ℚ`-algebra a unit congruent to `1` modulo the nilradical is the exponential
of a unique nilpotent element. -/
private theorem existsUnique_exp_eq_of_isNilpotent_sub_one {R : Type*} [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R] {u : R} (hu : IsNilpotent (u - 1)) :
    ∃! a : R, IsNilpotent a ∧ exp a = u := by
  obtain ⟨N, hN⟩ := IsNoetherianRing.isNilpotent_nilradical R
  have hN' : (nilradical R) ^ N = ⊥ := by simpa using hN
  obtain ⟨a, ha, hau⟩ := exists_exp_eq_of_sub_one_mem hN'
    (u := u) (mem_nilradical.mpr hu)
  refine ⟨a, ⟨mem_nilradical.mp ha, hau⟩, ?_⟩
  rintro b ⟨hb, hbu⟩
  have ha' : IsNilpotent a := mem_nilradical.mp ha
  have hab : IsNilpotent (a - b) := Commute.isNilpotent_sub (Commute.all _ _) ha' hb
  have h1 : exp (a - b) = 1 := by
    rw [sub_eq_add_neg, exp_add_of_commute (Commute.all _ _) ha' hb.neg, hau, ← hbu]
    exact exp_mul_exp_neg_self hb
  exact (sub_eq_zero.mp
    (eq_zero_of_exp_eq_one hN' (mem_nilradical.mpr hab) h1)).symm

end Exponential

/-- The ideal sheaf of the nilradical, as a module on `F`. -/
private noncomputable abbrev nilradicalModule (F : Scheme.{u}) : F.Modules :=
  Stacks.ClosedImmersion.idealSheaf F.nilradical.subschemeι.toLRSHom.toShHom

/-- The presheaf of sections of `nilradicalModule F`, as abelian groups. -/
private noncomputable abbrev nilradicalSections (F : Scheme.{u}) :
    (F.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} := (nilradicalModule F).presheaf

/-- The reduction `F_red` is reduced. -/
private theorem isReduced_nilradical_subscheme (F : Scheme.{u}) :
    IsReduced F.nilradical.subscheme := by
  simpa using Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := F) ⊤

/-- The reduction `F_red` of a connected scheme is connected: `F_red → F` is a homeomorphism. -/
private theorem connectedSpace_nilradical_subscheme (F : Scheme.{u}) [ConnectedSpace F] :
    ConnectedSpace F.nilradical.subscheme :=
  (universalHomeomorphism_isHomeomorph F.nilradical.subschemeι).homeomorph.connectedSpace_iff.mpr
    inferInstance

/-! ### The explicit finite-cover argument -/

section Cover

variable {F : Scheme.{u}}

/-- The reduction map `L ⟶ ι_* 𝒪_red` attached to a trivialization of `L|F_red`. -/
private noncomputable def redMap (L : F.Modules)
    (e : (Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) :
    L ⟶ (Scheme.Modules.pushforward F.nilradical.subschemeι).obj
      (SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction F.nilradical.subschemeι).unit.app L ≫
    (Scheme.Modules.pushforward F.nilradical.subschemeι).map e.hom

/-- `a ∈ Γ(L, W)` generates `L` over `W`: multiplication by `a` is bijective on every smaller
open. -/
private def IsGenOn (L : F.Modules) (W : F.Opens) (a : Γ(L, W)) : Prop :=
  ∀ (V : F.Opens) (h : V ≤ W), Function.Bijective fun c : Γ(F, V) =>
    c • (L.presheaf.map (homOfLE h).op).hom a

/-- The inclusion of the ideal sheaf of the nilradical into the structure sheaf. -/
private noncomputable abbrev jinc (F : Scheme.{u}) :
    nilradicalModule F ⟶ SheafOfModules.unit F.ringCatSheaf :=
  Stacks.IdealSheafSequence.divisorIdealMap F.nilradical

private theorem mem_ker_nilradical_iff (U : F.affineOpens) (a : Γ(F, U)) :
    a ∈ RingHom.ker (F.nilradical.subschemeι.app U).hom ↔ IsNilpotent a := by
  rw [F.nilradical.ker_subschemeι_app U]
  change a ∈ ((⊥ : F.IdealSheafData).radical.ideal U) ↔ _
  rw [Scheme.IdealSheafData.radical_ideal]
  exact Iff.rfl

/-- Over an affine open, the sections of the ideal sheaf of the nilradical are exactly the
nilpotent functions, embedded injectively in `Γ(F, U)`. -/
private theorem sections_nilradicalModule_affine (U : F.Opens) (hU : IsAffineOpen U) :
    Function.Injective ((jinc F).app U) ∧
      ∀ a : Γ(F, U), a ∈ Set.range ((jinc F).app U) ↔ IsNilpotent a := by
  obtain ⟨hz, hT⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact F.nilradical
  refine ⟨Stacks.Cohomology.injective_sections_of_shortExact F U hT, fun a => ?_⟩
  have hker : Scheme.Modules.Hom.app (Stacks.IdealSheafSequence.divisorQuotientMap F.nilradical)
      U a = 0 ↔ IsNilpotent a :=
    mem_ker_nilradical_iff (F := F) ⟨U, hU⟩ a
  rw [← hker]
  constructor
  · rintro ⟨b, rfl⟩
    exact congr_arg (fun φ : nilradicalModule F ⟶
      (Scheme.Modules.pushforward F.nilradical.subschemeι).obj
        (SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) =>
          Scheme.Modules.Hom.app φ U b) hz
  · intro h
    exact Stacks.Cohomology.exists_sections_of_sections_eq_zero F U hT a h

/-- The reduction of a section of `L` over `U`, as a function on `F_red` over `ι⁻¹U`. -/
private noncomputable def redSec (L : F.Modules)
    (e : (Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) (U : F.Opens) :
    Γ(L, U) →+ Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ U) :=
  (Scheme.Modules.Hom.app (redMap L e) U).hom

/-- Over an affine open the reduction map is surjective on sections. -/
private theorem redSec_surjective (L : F.Modules) [L.IsQuasicoherent]
    (e : (Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) (U : F.Opens)
    (hU : IsAffineOpen U) : Function.Surjective (redSec L e U) := by
  intro y
  have hη := AlgebraicGeometry.GrothendieckExistence.surjective_unit_app_of_isClosedImmersion
      F.nilradical.subschemeι L U hU
  have hbij : Function.Bijective
      ((Scheme.Modules.Hom.app e.hom (F.nilradical.subschemeι ⁻¹ᵁ U)).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      (Scheme.Modules.Hom.isIso_iff_isIso_app.mp (Iso.isIso_hom e) _)
  obtain ⟨z, hz⟩ := hbij.2 y
  obtain ⟨s, hs⟩ := hη z
  exact ⟨s,
    (congrArg (Scheme.Modules.Hom.app e.hom (F.nilradical.subschemeι ⁻¹ᵁ U)).hom hs).trans hz⟩

/-- The reduction map is linear over `𝒪_F`. -/
private theorem redSec_smul (L : F.Modules)
    (e : (Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) (U : F.Opens)
    (c : Γ(F, U)) (s : Γ(L, U)) :
    redSec L e U (c • s) = (show Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ U) from
      ((F.nilradical.subschemeι.app U).hom c *
        (show Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ U) from redSec L e U s))) :=
  Scheme.Modules.Hom.app_smul (redMap L e) c s

/-- The reduction map commutes with restriction. -/
private theorem redSec_map (L : F.Modules)
    (e : (Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) {U V : F.Opens} (h : V ≤ U)
    (s : Γ(L, U)) :
    redSec L e V ((L.presheaf.map (homOfLE h).op).hom s) =
      (F.nilradical.subscheme.presheaf.map
        (homOfLE (show F.nilradical.subschemeι ⁻¹ᵁ V ≤ F.nilradical.subschemeι ⁻¹ᵁ U from
          fun x hx => h hx)).op).hom (redSec L e U s) :=
  congrArg (fun φ => φ.hom s)
    ((Scheme.Modules.Hom.mapPresheaf (redMap L e)).naturality (homOfLE h).op)

private theorem presheaf_map_self (L : F.Modules) (U : F.Opens) (a : Γ(L, U)) :
    (L.presheaf.map (homOfLE (le_refl U)).op).hom a = a := by
  rw [show (homOfLE (le_refl U)).op = 𝟙 (op U) from Subsingleton.elim _ _, L.presheaf.map_id]
  rfl

private theorem presheaf_map_comp (L : F.Modules) {U V W : F.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (a : Γ(L, U)) :
    (L.presheaf.map (homOfLE h2).op).hom ((L.presheaf.map (homOfLE h1).op).hom a) =
      (L.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
  rw [← ConcreteCategory.comp_apply, ← L.presheaf.map_comp]
  rfl

/-- A generator over `U` restricts to a generator over every smaller open. -/
private theorem IsGenOn.restrict {L : F.Modules} {U : F.Opens} {a : Γ(L, U)}
    (ha : IsGenOn L U a) {V : F.Opens} (h : V ≤ U) :
    IsGenOn L V ((L.presheaf.map (homOfLE h).op).hom a) := by
  intro W hW
  have := ha W (hW.trans h)
  rwa [← presheaf_map_comp L h hW a] at this

/-- A unit multiple of a generator is a generator. -/
private theorem IsGenOn.smul_unit {L : F.Modules} {U : F.Opens} {a : Γ(L, U)}
    (ha : IsGenOn L U a) {c : Γ(F, U)} (hc : IsUnit c) : IsGenOn L U (c • a) := by
  intro V h
  obtain ⟨u, hu⟩ := hc.map (F.presheaf.map (homOfLE h).op).hom
  have key : (fun d : Γ(F, V) => d • (L.presheaf.map (homOfLE h).op).hom (c • a)) =
      (fun d : Γ(F, V) => d • (L.presheaf.map (homOfLE h).op).hom a) ∘
        (fun d : Γ(F, V) => d * ((F.presheaf.map (homOfLE h).op).hom c)) := by
    funext d
    simp only [Function.comp, Scheme.Modules.map_smul, smul_smul]
  rw [key]
  refine (ha V h).comp ?_
  rw [← hu]
  exact (Units.mulRight u).bijective

/-- Over an affine open, `c` is a unit as soon as its reduction is. -/
private theorem isUnit_of_isUnit_map (U : F.Opens) (hU : IsAffineOpen U) (c : Γ(F, U))
    (h : IsUnit ((F.nilradical.subschemeι.app U).hom c)) : IsUnit c := by
  obtain ⟨c', hc'⟩ := F.nilradical.subschemeι_app_surjective ⟨U, hU⟩
    (↑h.unit⁻¹ : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ U))
  have hmem : c * c' - 1 ∈ RingHom.ker (F.nilradical.subschemeι.app U).hom := by
    simp [RingHom.mem_ker, hc']
  have hnil : IsNilpotent (c * c' - 1) := (mem_ker_nilradical_iff ⟨U, hU⟩ _).mp hmem
  have hu : IsUnit (c * c') := by
    have h := hnil.isUnit_one_add
    rwa [show (1 : Γ(F, U)) + (c * c' - 1) = c * c' by ring] at h
  exact isUnit_of_mul_isUnit_left hu

/-- Over an affine open on which `L` has a generator, there is a generator whose
reduction is `1`. -/
private theorem exists_lift_generators (L : F.Modules) [L.IsQuasicoherent]
    (e : (Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) (U : F.Opens)
    (hU : IsAffineOpen U) (E : Γ(L, U)) (hE : IsGenOn L U E) :
    ∃ s : Γ(L, U), IsGenOn L U s ∧
      redSec L e U s = (1 : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ U)) := by
  obtain ⟨s0, hs0⟩ := redSec_surjective L e U hU
    (1 : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ U))
  obtain ⟨c, hc⟩ := (hE U le_rfl).2 s0
  rw [presheaf_map_self] at hc
  have hc2 : c • E = s0 := hc
  have h1 : (F.nilradical.subschemeι.app U).hom c *
      (show Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ U) from redSec L e U E) = 1 :=
    (redSec_smul L e U c E).symm.trans (by rwa [hc2])
  exact ⟨c • E, hE.smul_unit (isUnit_of_isUnit_map U hU c (.of_mul_eq_one _ h1)),
    (redSec_smul L e U c E).trans h1⟩

/-- Two generators over an affine open `W` with reduction `1` differ by `exp a` for a unique
section `a` of the ideal sheaf of the nilradical. -/
private theorem existsUnique_transition [IsLocallyNoetherian F] (L : F.Modules)
    (e : (Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) (W : F.Opens)
    (hW : IsAffineOpen W) [Algebra ℚ Γ(F, W)] (s s' : Γ(L, W)) (hs : IsGenOn L W s)
    (h1 : redSec L e W s = (1 : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ W)))
    (h1' : redSec L e W s' = (1 : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ W))) :
    ∃! a : Γ(nilradicalModule F, W),
      s' = IsNilpotent.exp (show Γ(F, W) from (jinc F).app W a) • s := by
  haveI : IsNoetherianRing Γ(F, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨u, hu⟩ := (hs W le_rfl).2 s'
  rw [presheaf_map_self] at hu
  have hu2 : u • s = s' := hu
  have hred : (F.nilradical.subschemeι.app W).hom u =
      (1 : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ W)) := by
    have := redSec_smul L e W u s
    rw [hu2, h1', h1, mul_one] at this
    exact this.symm
  have hnil : IsNilpotent (u - 1) := by
    refine (mem_ker_nilradical_iff ⟨W, hW⟩ _).mp ?_
    simp [RingHom.mem_ker, hred]
  obtain ⟨b, ⟨hb, hbu⟩, hbuniq⟩ := existsUnique_exp_eq_of_isNilpotent_sub_one hnil
  obtain ⟨hinj, hrange⟩ := sections_nilradicalModule_affine (F := F) W hW
  obtain ⟨a, ha⟩ := (hrange b).mpr hb
  refine ⟨a, ?_, ?_⟩
  · have : (show Γ(F, W) from (jinc F).app W a) = b := ha
    simp only [this, hbu]
    exact hu2.symm
  · intro a' ha'
    have hnil' : IsNilpotent (show Γ(F, W) from (jinc F).app W a') := (hrange _).mp ⟨a', rfl⟩
    have heq : IsNilpotent.exp (show Γ(F, W) from (jinc F).app W a') = u := by
      refine (hs W le_rfl).1 ?_
      simp only [presheaf_map_self]
      exact ha'.symm.trans hu2.symm
    have := hbuniq _ ⟨hnil', heq⟩
    exact hinj (this.trans ha.symm)

/-- Restriction of sections of the ideal sheaf of the nilradical commutes with the inclusion into
the structure sheaf. -/
private theorem jinc_map (U V : F.Opens) (h : V ≤ U) (a : Γ(nilradicalModule F, U)) :
    (jinc F).app V ((nilradicalModule F).presheaf.map (homOfLE h).op a) =
      (F.presheaf.map (homOfLE h).op).hom ((jinc F).app U a) := by
  have := (Scheme.Modules.Hom.mapPresheaf (jinc F)).naturality (homOfLE h).op
  exact congrArg (fun φ => φ.hom a) this

/-- The exponential commutes with restriction. -/
private theorem map_exp_restrict (U V : F.Opens) (h : V ≤ U) [Algebra ℚ Γ(F, U)]
    [Algebra ℚ Γ(F, V)] (x : Γ(F, U)) (hx : IsNilpotent x) :
    (F.presheaf.map (homOfLE h).op).hom (IsNilpotent.exp x) =
      IsNilpotent.exp ((F.presheaf.map (homOfLE h).op).hom x) :=
  IsNilpotent.map_exp hx (F.presheaf.map (homOfLE h).op).hom

/-- Restricting a transition relation. -/
private theorem transition_restrict (L : F.Modules) {U V : F.Opens} (h : V ≤ U)
    [Algebra ℚ Γ(F, U)] [Algebra ℚ Γ(F, V)] (s s' : Γ(L, U)) (a : Γ(nilradicalModule F, U))
    (hnil : IsNilpotent (show Γ(F, U) from (jinc F).app U a))
    (ha : s' = IsNilpotent.exp (show Γ(F, U) from (jinc F).app U a) • s) :
    (L.presheaf.map (homOfLE h).op).hom s' =
      IsNilpotent.exp (show Γ(F, V) from
        (jinc F).app V ((nilradicalModule F).presheaf.map (homOfLE h).op a)) •
        (L.presheaf.map (homOfLE h).op).hom s := by
  rw [ha, jinc_map U V h a]
  have := Scheme.Modules.map_smul L (homOfLE h) (IsNilpotent.exp (show Γ(F, U) from
    (jinc F).app U a)) s
  refine this.trans ?_
  rw [map_exp_restrict U V h _ hnil]

/-- Composition of transitions. -/
private theorem transition_comp [IsLocallyNoetherian F] (L : F.Modules)
    (e : (Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) (W : F.Opens)
    (hW : IsAffineOpen W) [Algebra ℚ Γ(F, W)] (s0 s1 s2 : Γ(L, W)) (hs0 : IsGenOn L W s0)
    (h0 : redSec L e W s0 = (1 : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ W)))
    (h2 : redSec L e W s2 = (1 : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ W)))
    (a01 a12 a02 : Γ(nilradicalModule F, W))
    (h01 : s1 = IsNilpotent.exp (show Γ(F, W) from (jinc F).app W a01) • s0)
    (h12 : s2 = IsNilpotent.exp (show Γ(F, W) from (jinc F).app W a12) • s1)
    (h02 : s2 = IsNilpotent.exp (show Γ(F, W) from (jinc F).app W a02) • s0) :
    a02 = a01 + a12 := by
  obtain ⟨hinj, hrange⟩ := sections_nilradicalModule_affine (F := F) W hW
  have n01 : IsNilpotent (show Γ(F, W) from (jinc F).app W a01) := (hrange _).mp ⟨a01, rfl⟩
  have n12 : IsNilpotent (show Γ(F, W) from (jinc F).app W a12) := (hrange _).mp ⟨a12, rfl⟩
  have hu := (existsUnique_transition L e W hW s0 s2 hs0 h0 h2)
  refine hu.unique h02 ?_
  rw [h12, h01, smul_smul, map_add]
  show _ = IsNilpotent.exp ((show Γ(F, W) from (jinc F).app W a01) +
    (show Γ(F, W) from (jinc F).app W a12)) • s0
  rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) n01 n12, mul_comm]

/-- Sections of `L` that agree on a cover of `V` are equal. -/
private theorem eq_of_restrict_eq (L : F.Modules) {I : Type u} (V : F.Opens) (Vi : I → F.Opens)
    (hle : ∀ i, Vi i ≤ V) (hcov : V ≤ ⨆ i, Vi i) (x y : Γ(L, V))
    (h : ∀ i, (L.presheaf.map (homOfLE (hle i)).op).hom x =
      (L.presheaf.map (homOfLE (hle i)).op).hom y) : x = y := by
  refine TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u}) ⟨L.presheaf, Scheme.Modules.isSheaf L⟩
    V x y fun z hz => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hz)
  have := congrArg (L.presheaf.germ (Vi i) z hi) (h i)
  simp only [TopCat.Presheaf.germ_res_apply] at this
  exact this

/-- Functions that agree on a cover of `V` are equal. -/
private theorem eq_of_restrict_eq_ring {I : Type u} (V : F.Opens) (Vi : I → F.Opens)
    (hle : ∀ i, Vi i ≤ V) (hcov : V ≤ ⨆ i, Vi i) (x y : Γ(F, V))
    (h : ∀ i, (F.presheaf.map (homOfLE (hle i)).op).hom x =
      (F.presheaf.map (homOfLE (hle i)).op).hom y) : x = y := by
  refine TopCat.Presheaf.section_ext F.sheaf V x y fun z hz => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hz)
  have := congrArg (F.presheaf.germ (Vi i) z hi) (h i)
  simp only [TopCat.Presheaf.germ_res_apply] at this
  exact this

/-- Gluing of compatible families of functions. -/
private theorem exists_glue_ring {I : Type u} (V : F.Opens) (Vi : I → F.Opens)
    (hle : ∀ i, Vi i ≤ V) (hcov : V ≤ ⨆ i, Vi i) (d : ∀ i, Γ(F, Vi i))
    (hd : ∀ i j, (F.presheaf.map (homOfLE (inf_le_left : Vi i ⊓ Vi j ≤ Vi i)).op).hom (d i) =
      (F.presheaf.map (homOfLE (inf_le_right : Vi i ⊓ Vi j ≤ Vi j)).op).hom (d j)) :
    ∃ x : Γ(F, V), ∀ i, (F.presheaf.map (homOfLE (hle i)).op).hom x = d i := by
  obtain ⟨x, hx, -⟩ := TopCat.Sheaf.existsUnique_gluing' F.sheaf Vi V
    (fun i => homOfLE (hle i)) hcov d hd
  exact ⟨x, hx⟩

/-- Being a generator is local on `W`. -/
private theorem isGenOn_of_local (L : F.Modules) {I : Type u} (U : I → F.Opens) (W : F.Opens)
    (hUW : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i) (t : Γ(L, W))
    (h : ∀ i, IsGenOn L (U i) ((L.presheaf.map (homOfLE (hUW i)).op).hom t)) :
    IsGenOn L W t := by
  intro V hV
  let Vi : I → F.Opens := fun i => V ⊓ U i
  have hle : ∀ i, Vi i ≤ V := fun i => inf_le_left
  have hcovV : V ≤ ⨆ i, Vi i := by
    intro z hz
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov (hV hz))
    exact Opens.mem_iSup.mpr ⟨i, hz, hi⟩
  have hgen : ∀ i (V' : F.Opens) (h' : V' ≤ Vi i), Function.Bijective fun c : Γ(F, V') =>
      c • (L.presheaf.map (homOfLE (h'.trans ((inf_le_right : Vi i ≤ U i).trans (hUW i)))).op).hom
        t := by
    intro i V' h'
    have := h i V' (h'.trans inf_le_right)
    rwa [presheaf_map_comp L (hUW i) (h'.trans inf_le_right) t] at this
  constructor
  · intro c c' hcc
    refine eq_of_restrict_eq_ring V Vi hle hcovV c c' fun i => ?_
    refine (hgen i (Vi i) le_rfl).1 ?_
    simpa only [Scheme.Modules.map_smul, presheaf_map_comp] using
      congrArg (fun x => (L.presheaf.map (homOfLE (hle i)).op).hom x) hcc
  · intro m
    choose d hd using fun i =>
      (hgen i (Vi i) le_rfl).2 ((L.presheaf.map (homOfLE (hle i)).op).hom m)
    have hcomp : ∀ i j, (F.presheaf.map (homOfLE (inf_le_left : Vi i ⊓ Vi j ≤ Vi i)).op).hom (d i) =
        (F.presheaf.map (homOfLE (inf_le_right : Vi i ⊓ Vi j ≤ Vi j)).op).hom (d j) := by
      intro i j
      refine (hgen i (Vi i ⊓ Vi j) inf_le_left).1 ?_
      have e1 := congrArg (fun x => (L.presheaf.map (homOfLE
        (inf_le_left : Vi i ⊓ Vi j ≤ Vi i)).op).hom x) (hd i)
      have e2 := congrArg (fun x => (L.presheaf.map (homOfLE
        (inf_le_right : Vi i ⊓ Vi j ≤ Vi j)).op).hom x) (hd j)
      simp only [Scheme.Modules.map_smul, presheaf_map_comp] at e1 e2 ⊢
      exact e1.trans e2.symm
    obtain ⟨x, hx⟩ := exists_glue_ring V Vi hle hcovV d hcomp
    refine ⟨x, eq_of_restrict_eq L V Vi hle hcovV _ _ fun i => ?_⟩
    simp only [Scheme.Modules.map_smul, presheaf_map_comp, hx]
    exact hd i

/-- A global generator trivializes `L`. -/
private theorem nonempty_iso_unit_of_isGenOn_top (L : F.Modules)
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L] (T : Γ(L, ⊤))
    (hT : IsGenOn L ⊤ T) : Nonempty (L ≅ SheafOfModules.unit F.ringCatSheaf) := by
  let φ := L.unitHomEquiv.symm (sectionsOfTop L T)
  have : IsIso φ := by
    refine Stacks.SheafOfModules.isIso_of_isIso_val_app φ fun A => ?_
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hT A.unop le_top
  exact ⟨(asIso φ).symm⟩

/-- Local generators that agree on overlaps glue to a global generator. -/
private theorem nonempty_iso_unit_of_local_generators (L : F.Modules)
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L] {I : Type u} (U : I → F.Opens)
    (hU : (⊤ : F.Opens) ≤ ⨆ i, U i) (t : ∀ i, Γ(L, U i)) (hgen : ∀ i, IsGenOn L (U i) (t i))
    (hcomp : ∀ i j, (L.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (t i) =
      (L.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (t j)) :
    Nonempty (L ≅ SheafOfModules.unit F.ringCatSheaf) := by
  obtain ⟨T, hT, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨L.presheaf, Scheme.Modules.isSheaf L⟩ : TopCat.Sheaf AddCommGrpCat.{u} F) U ⊤
    (fun _ => homOfLE le_top) hU t hcomp
  refine nonempty_iso_unit_of_isGenOn_top L T ?_
  refine isGenOn_of_local L U ⊤ (fun i => le_top) hU T fun i => ?_
  rw [hT i]
  exact hgen i

/-- Around every point there is an affine open on which `L` has a generator. -/
private theorem exists_isAffineOpen_isGenOn (L : F.Modules)
    [hL : SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L] (x : F) :
    ∃ W : F.Opens, x ∈ W ∧ IsAffineOpen W ∧ ∃ E : Γ(L, W), IsGenOn L W E := by
  have : ∀ z : F.toRingedSpace.carrier, IsLocalRing (ringStalk F.toRingedSpace z) :=
    F.isLocalRing
  have hLs : Stacks.SheafOfModules.IsInvertible F.toRingedSpace.presheaf
      (structureSheafRing F.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  obtain ⟨W, hxW, a, ha⟩ := Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible
    (X := F.toRingedSpace) L x
  obtain ⟨W', hW'aff, hxW', hW'W⟩ := exists_isAffineOpen_mem_and_subset hxW
  exact ⟨W', hxW', hW'aff, _, (show IsGenOn L W a from ha).restrict hW'W⟩

/-- Čech vanishing for the ideal sheaf of the nilradical on an affine cover. -/
private theorem subsingleton_cechH1_nilradical (k : Type u) [Field k]
    (f : F ⟶ Spec (.of k)) [IsProper f]
    (hH1 : Subsingleton (cohomologyOverField k f (nilradicalModule F) 1))
    (E : PreZeroHypercover.{u} (⊤ : F.Opens)) (hcov : (⊤ : F.Opens) ≤ ⨆ i, E.X i)
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀), IsAffineOpen (⨅ j, E.X (s j))) :
    Subsingleton (Stacks.CechSite.cechH1 E (nilradicalSections F)) := by
  have hU : (⊤ : F.Opens) = ⨆ i, E.X i := (top_le_iff.mp hcov).symm
  have hz : IsZero (cohomologyOverField k f (nilradicalModule F) 1) :=
    ModuleCat.isZero_of_subsingleton _
  have h1 := (isZero_cohomologyOverField_iff_isZero_hgroup k f (nilradicalModule F) 1).mp hz
  have h2 := (Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology F ⊤ E.X hU
    haff (nilradicalModule F) 1).mp h1
  let G := Stacks.Cohomology.CechSheaf.sectionsPresheaf (R := F.ringCatSheaf) ⊤
    (nilradicalModule F)
  have h3 : IsZero (Stacks.CechSite.sliceCechCohomology E G 1) := h2
  have e : (Over.forget (⊤ : F.Opens)).op ⋙ nilradicalSections F ≅
      G ⋙ forget₂ (ModuleCat.{u} ↑(Stacks.Cohomology.CechSheaf.SectionRing F.ringCatSheaf ⊤))
        AddCommGrpCat.{u} := Iso.refl _
  have h4 := Stacks.CechSite.isZero_cechCohomology_of_isZero_sliceModule (E := E)
    (R := ↑(Stacks.Cohomology.CechSheaf.SectionRing F.ringCatSheaf ⊤))
    (nilradicalSections F) G e 1 h3
  have hs : Subsingleton (Stacks.CechSite.cechCohomology E (A := AddCommGrpCat.{u})
      (nilradicalSections F) 1 : Type u) := AddCommGrpCat.isZero_iff_subsingleton.mp h4
  exact (Stacks.CechSite.cechCohomologyOneEquiv E (nilradicalSections
      F)).toEquiv.subsingleton_congr.mp hs

section CechProducts

variable (E : PreZeroHypercover.{u} (⊤ : F.Opens))

/-- The iterated fibre product of members of a family of opens, as an open of `F`. -/
private noncomputable abbrev prodOpen {n : ℕ} (k : Fin (n + 1) → E.I₀) : F.Opens :=
  (∏ᶜ (fun j => Over.mk (E.f (k j))) : Over (⊤ : F.Opens)).left

private theorem prodOpen_le {n : ℕ} (k : Fin (n + 1) → E.I₀) (m : Fin (n + 1)) :
    prodOpen E k ≤ E.X (k m) :=
  (Stacks.CechSite.cechProj E k m).le

private theorem le_prodOpen {n : ℕ} (k : Fin (n + 1) → E.I₀) (W : F.Opens)
    (h : ∀ m, W ≤ E.X (k m)) : W ≤ prodOpen E k := by
  let g : Over.mk (homOfLE (le_top : W ≤ ⊤)) ⟶
      (∏ᶜ (fun j => Over.mk (E.f (k j))) : Over (⊤ : F.Opens)) :=
    Limits.Pi.lift fun m => Over.homMk (homOfLE (h m))
  exact g.left.le

private theorem prodOpen_eq_iInf {n : ℕ} (k : Fin (n + 1) → E.I₀) :
    prodOpen E k = ⨅ m, E.X (k m) :=
  le_antisymm (le_iInf (prodOpen_le E k)) (le_prodOpen E k _ (fun m => iInf_le _ m))

private theorem prodOpen_face_le {n : ℕ} (k : Fin (n + 2) → E.I₀) (j : Fin (n + 2)) :
    prodOpen E k ≤ prodOpen E (fun b => k (j.succAbove b)) :=
  (Stacks.CechSite.faceProjection E k j).left.le

end CechProducts

/-- The Čech argument: from vanishing of `Ȟ¹` of the ideal sheaf of the nilradical, local
generators with reduction `1` can be corrected to local generators agreeing on overlaps. -/
private theorem exists_corrected_generators [IsLocallyNoetherian F]
    [∀ W : F.Opens, Algebra ℚ Γ(F, W)] (L : F.Modules)
    (e : (Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf)
    (E : PreZeroHypercover.{u} (⊤ : F.Opens))
    (haffI : ∀ (r : ℕ) (σ : Fin (r + 1) → E.I₀), IsAffineOpen (⨅ j, E.X (σ j)))
    (hCech : Subsingleton (Stacks.CechSite.cechH1 E (nilradicalSections F)))
    (s : ∀ i, Γ(L, E.X i)) (hsgen : ∀ i, IsGenOn L (E.X i) (s i))
    (hsred : ∀ i, redSec L e (E.X i) (s i) =
      (1 : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ E.X i))) :
    ∃ t : ∀ i, Γ(L, E.X i), (∀ i, IsGenOn L (E.X i) (t i)) ∧
      ∀ i j, (L.presheaf.map (homOfLE (inf_le_left : E.X i ⊓ E.X j ≤ E.X i)).op).hom (t i) =
        (L.presheaf.map (homOfLE (inf_le_right : E.X i ⊓ E.X j ≤ E.X j)).op).hom (t j) := by
  have hPaff : ∀ {n : ℕ} (k : Fin (n + 1) → E.I₀), IsAffineOpen (prodOpen E k) := fun k => by
    rw [prodOpen_eq_iInf]; exact haffI _ k
  -- restriction of the chosen generators to a smaller open
  let rs : ∀ (i : E.I₀) (V : F.Opens), V ≤ E.X i → Γ(L, V) :=
    fun i V h => (L.presheaf.map (homOfLE h).op).hom (s i)
  have rs_gen : ∀ i V (h : V ≤ E.X i), IsGenOn L V (rs i V h) := fun i V h => (hsgen i).restrict h
  have rs_red : ∀ i V (h : V ≤ E.X i), redSec L e V (rs i V h) =
      (1 : Γ(F.nilradical.subscheme, F.nilradical.subschemeι ⁻¹ᵁ V)) := by
    intro i V h
    show redSec L e V ((L.presheaf.map (homOfLE h).op).hom (s i)) = 1
    rw [redSec_map, hsred, map_one]
  have rs_res : ∀ i V V' (h : V ≤ E.X i) (h' : V' ≤ V), (L.presheaf.map (homOfLE h').op).hom
      (rs i V h) = rs i V' (h'.trans h) := fun i V V' h h' => presheaf_map_comp L h h' (s i)
  -- the transition between the first two generators on each pairwise product
  have htrans : ∀ k : Fin 2 → E.I₀, ∃! a : Γ(nilradicalModule F, prodOpen E k),
      rs (k 1) _ (prodOpen_le E k 1) = IsNilpotent.exp
        (show Γ(F, prodOpen E k) from (jinc F).app _ a) • rs (k 0) _ (prodOpen_le E k 0) :=
    fun k => existsUnique_transition L e (prodOpen E k) (hPaff k) _ _
      (rs_gen _ _ _) (rs_red _ _ _) (rs_red _ _ _)
  choose a ha huniq using htrans
  have hnil : ∀ (V : F.Opens) (hV : IsAffineOpen V) (x : Γ(nilradicalModule F, V)),
      IsNilpotent (show Γ(F, V) from (jinc F).app V x) := fun V hV x =>
    ((sections_nilradicalModule_affine (F := F) V hV).2 _).mp ⟨x, rfl⟩
  have hcoc : (a : Stacks.CechSite.cechCochain E (nilradicalSections F) 1) ∈
      Stacks.CechSite.cocycles1 E (nilradicalSections F) := by
    rw [Stacks.CechSite.mem_cocycles1_iff']
    intro k
    have hface : ∀ j : Fin 3, (nilradicalSections F).map (Stacks.CechSite.faceProjection E k
        j).left.op =
        (nilradicalModule F).presheaf.map (homOfLE (prodOpen_face_le E k j)).op := fun j =>
      congrArg Quiver.Hom.op (Subsingleton.elim _ _) |> congrArg (nilradicalSections F).map
    -- transition relations restricted to `W = prodOpen E k`
    have rel : ∀ j : Fin 3, rs (k (j.succAbove 1)) (prodOpen E k) (prodOpen_le E k _) =
        IsNilpotent.exp (show Γ(F, prodOpen E k) from (jinc F).app _
          ((nilradicalModule F).presheaf.map (homOfLE (prodOpen_face_le E k j)).op
            (a fun b => k (j.succAbove b)))) •
          rs (k (j.succAbove 0)) (prodOpen E k) (prodOpen_le E k _) := by
      intro j
      have h := transition_restrict L (prodOpen_face_le E k j) _ _ _
        (hnil _ (hPaff _) _) (ha fun b => k (j.succAbove b))
      rw [rs_res, rs_res] at h
      exact h
    have hsum := transition_comp L e (prodOpen E k) (hPaff k) (rs (k 0) _ (prodOpen_le E k 0))
      (rs (k 1) _ (prodOpen_le E k 1)) (rs (k 2) _ (prodOpen_le E k 2)) (rs_gen _ _ _)
      (rs_red _ _ _) (rs_red _ _ _)
      ((nilradicalModule F).presheaf.map (homOfLE (prodOpen_face_le E k 2)).op
        (a fun b => k ((2 : Fin 3).succAbove b)))
      ((nilradicalModule F).presheaf.map (homOfLE (prodOpen_face_le E k 0)).op
        (a fun b => k ((0 : Fin 3).succAbove b)))
      ((nilradicalModule F).presheaf.map (homOfLE (prodOpen_face_le E k 1)).op
        (a fun b => k ((1 : Fin 3).succAbove b)))
      (rel 2) (rel 0) (rel 1)
    rw [hface, hface, hface, hsum]
    exact add_comm _ _
  obtain ⟨t, ht⟩ := (Stacks.CechSite.subsingleton_cechH1_iff E (nilradicalSections F)).mp hCech ⟨a, hcoc⟩
  -- the degree-zero cochain `t` gives sections `b i` of the ideal sheaf over each `E.X i`
  have hX : ∀ i : E.I₀, E.X i ≤ prodOpen E (fun _ : Fin 1 => i) :=
    fun i => le_prodOpen E _ _ (fun _ => le_rfl)
  let b : ∀ i : E.I₀, Γ(nilradicalModule F, E.X i) := fun i =>
    (nilradicalModule F).presheaf.map (homOfLE (hX i)).op (t (fun _ => i))
  have hcoface : ∀ (l : Fin 1 → E.I₀) (W : F.Opens) (h1 : W ≤ prodOpen E l) (i : E.I₀)
      (hl : l 0 = i) (h2 : W ≤ E.X i),
      (nilradicalModule F).presheaf.map (homOfLE h1).op (t l) =
        (nilradicalModule F).presheaf.map (homOfLE h2).op (b i) := by
    intro l W h1 i hl h2
    obtain rfl : l = fun _ => i := funext fun x => by
      obtain rfl : x = 0 := Subsingleton.elim _ _
      exact hl
    exact (presheaf_map_comp (nilradicalModule F) (hX i) h2 (t fun _ => i)).symm
  have hdiff : ∀ k : Fin 2 → E.I₀, a k =
      (nilradicalModule F).presheaf.map (homOfLE (prodOpen_le E k 1)).op (b (k 1)) -
        (nilradicalModule F).presheaf.map (homOfLE (prodOpen_le E k 0)).op (b (k 0)) := by
    intro k
    have h := congrFun ht k
    rw [Stacks.CechSite.cechDifferential_zero_apply] at h
    have hf : ∀ j : Fin 2, (nilradicalSections F).map (Stacks.CechSite.faceProjection E k j).left.op
        =
        (nilradicalModule F).presheaf.map (homOfLE (prodOpen_face_le E k j)).op := fun j =>
      congrArg Quiver.Hom.op (Subsingleton.elim _ _) |> congrArg (nilradicalSections F).map
    rw [hf, hf] at h
    rw [← hcoface _ _ (prodOpen_face_le E k 0) (k 1) rfl,
      ← hcoface _ _ (prodOpen_face_le E k 1) (k 0) rfl]
    exact h.symm
  have hbnil : ∀ i, IsNilpotent (show Γ(F, E.X i) from (jinc F).app _ (b i)) := fun i =>
    hnil _ (by simpa using haffI 0 (fun _ => i)) (b i)
  refine ⟨fun i => IsNilpotent.exp (-(show Γ(F, E.X i) from (jinc F).app _ (b i))) • s i,
    fun i => (hsgen i).smul_unit (IsNilpotent.isUnit_exp (hbnil i).neg), ?_⟩
  intro i j
  have hWP : E.X i ⊓ E.X j ≤ prodOpen E ![i, j] := le_prodOpen E _ _ (fun m => by
    fin_cases m
    · exact inf_le_left
    · exact inf_le_right)
  have hrel := transition_restrict L hWP _ _ _ (hnil _ (hPaff ![i, j]) _) (ha ![i, j])
  rw [rs_res, rs_res] at hrel
  have hWi : E.X i ⊓ E.X j ≤ E.X i := inf_le_left
  have hWj : E.X i ⊓ E.X j ≤ E.X j := inf_le_right
  have hja : (show Γ(F, E.X i ⊓ E.X j) from (jinc F).app _
      ((nilradicalModule F).presheaf.map (homOfLE hWP).op (a ![i, j]))) =
      (F.presheaf.map (homOfLE hWj).op).hom ((jinc F).app _ (b j)) -
        (F.presheaf.map (homOfLE hWi).op).hom ((jinc F).app _ (b i)) := by
    have c1 : (nilradicalModule F).presheaf.map (homOfLE hWP).op
        ((nilradicalModule F).presheaf.map (homOfLE (prodOpen_le E ![i, j] 1)).op
          (b (![i, j] 1))) = (nilradicalModule F).presheaf.map (homOfLE hWj).op (b j) :=
      presheaf_map_comp (nilradicalModule F) (prodOpen_le E ![i, j] 1) hWP (b j)
    have c0 : (nilradicalModule F).presheaf.map (homOfLE hWP).op
        ((nilradicalModule F).presheaf.map (homOfLE (prodOpen_le E ![i, j] 0)).op
          (b (![i, j] 0))) = (nilradicalModule F).presheaf.map (homOfLE hWi).op (b i) :=
      presheaf_map_comp (nilradicalModule F) (prodOpen_le E ![i, j] 0) hWP (b i)
    rw [hdiff ![i, j], map_sub, c1, c0, map_sub, jinc_map _ _ hWj (b j), jinc_map _ _ hWi (b i)]
    rfl
  have hrel' : rs j (E.X i ⊓ E.X j) hWj = IsNilpotent.exp
      ((F.presheaf.map (homOfLE hWj).op).hom ((jinc F).app _ (b j)) -
        (F.presheaf.map (homOfLE hWi).op).hom ((jinc F).app _ (b i))) •
      rs i (E.X i ⊓ E.X j) hWi := by
    rw [← hja]; exact hrel
  have nBi : IsNilpotent ((F.presheaf.map (homOfLE hWi).op).hom ((jinc F).app _ (b i))) :=
    (hbnil i).map _
  have nBj : IsNilpotent ((F.presheaf.map (homOfLE hWj).op).hom ((jinc F).app _ (b j))) :=
    (hbnil j).map _
  show (L.presheaf.map (homOfLE hWi).op).hom (IsNilpotent.exp (-(show Γ(F, E.X i) from
      (jinc F).app _ (b i))) • s i) =
    (L.presheaf.map (homOfLE hWj).op).hom (IsNilpotent.exp (-(show Γ(F, E.X j) from
      (jinc F).app _ (b j))) • s j)
  rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul,
    map_exp_restrict _ _ hWi _ (hbnil i).neg, map_exp_restrict _ _ hWj _ (hbnil j).neg,
    map_neg, map_neg]
  show IsNilpotent.exp (-_) • rs i (E.X i ⊓ E.X j) hWi = IsNilpotent.exp (-_) •
    rs j (E.X i ⊓ E.X j) hWj
  rw [hrel', smul_smul, ← IsNilpotent.exp_add_of_commute (Commute.all _ _) nBj.neg
    (Commute.isNilpotent_sub (Commute.all _ _) nBj nBi)]
  congr 2
  abel

/-- A `ℚ`-algebra structure on all rings of sections, from the base field of characteristic
zero. -/
private noncomputable abbrev ratAlgebraSections (k : Type u) [Field k] [CharZero k]
    (f : F ⟶ Spec (.of k)) (W : F.Opens) : Algebra ℚ Γ(F, W) :=
  (((F.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).comp (algebraMap ℚ k)).toAlgebra

/-- Restriction to the reduction is injective on isomorphism classes of invertible sheaves, for a
connected proper scheme `F` over a field of characteristic zero with `H¹(F, 𝒪_F) = 0`: local
generators of `L` lifting a trivialization of `L|F_red` differ on overlaps by exponentials of
sections of the nilradical, and the vanishing of `Ȟ¹` of the nilradical corrects them to agree. -/
private theorem nonempty_iso_unit_of_pullback_nilradical (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] (f : F ⟶ Spec (.of k)) [IsProper f] [ConnectedSpace F]
    (hH1 : Subsingleton (cohomologyOverField k f (SheafOfModules.unit F.ringCatSheaf) 1))
    (L : F.Modules) [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L]
    (hred : Nonempty ((Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf)) :
    Nonempty (L ≅ SheafOfModules.unit F.ringCatSheaf) := by
  obtain ⟨e⟩ := hred
  haveI : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian f
  letI : ∀ W : F.Opens, Algebra ℚ Γ(F, W) := ratAlgebraSections k f
  have hsep : IsAffineHom (pullback.diagonal (terminal.from F)) := by
    have : IsSeparated (terminal.from F) := by
      have e : terminal.from F = f ≫ terminal.from (Spec (.of k)) := Subsingleton.elim _ _
      rw [e]
      infer_instance
    infer_instance
  choose W hxW hWaff Eg hEg using fun x : F => exists_isAffineOpen_isGenOn L x
  choose s hsgen hsred using fun x : F =>
    exists_lift_generators L e (W x) (hWaff x) (Eg x) (hEg x)
  let E : PreZeroHypercover.{u} (⊤ : F.Opens) := ⟨F, W, fun x => homOfLE le_top⟩
  have hcov : (⊤ : F.Opens) ≤ ⨆ i, E.X i := fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩
  have haffI : ∀ (r : ℕ) (σ : Fin (r + 1) → E.I₀), IsAffineOpen (⨅ j, E.X (σ j)) :=
    fun r σ => IsAffineOpen.iInf (fun j => hWaff (σ j))
  have := isReduced_nilradical_subscheme F
  have := connectedSpace_nilradical_subscheme F
  have hCech := subsingleton_cechH1_nilradical k f (subsingleton_H1_ideal k f hH1 F.nilradical) E
    hcov haffI
  obtain ⟨t, htgen, htcomp⟩ := exists_corrected_generators L e E haffI hCech s hsgen hsred
  exact nonempty_iso_unit_of_local_generators L E.X hcov t htgen htcomp

end Cover

/-- A numerically trivial invertible sheaf is trivial on the reduction `F_red`. -/
private theorem nonempty_pullback_nilradical_iso_unit (k : Type u) [Field k] {F : Scheme.{u}}
    (f : F ⟶ Spec (.of k)) [IsProper f] [ConnectedSpace F] (hdim : topologicalKrullDim F ≤ 1)
    (hH1 : Subsingleton (cohomologyOverField k f (SheafOfModules.unit F.ringCatSheaf) 1))
    (L : F.Modules) [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L]
    (hL : ∀ (C : Scheme.{u}) (i : C ⟶ F) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ f)] (hC : topologicalKrullDim C ≤ 1), MMP.Mori.degreeOn k f i hC L = 0) :
    Nonempty ((Scheme.Modules.pullback F.nilradical.subschemeι).obj L ≅
      SheafOfModules.unit F.nilradical.subscheme.ringCatSheaf) := by
  have := isReduced_nilradical_subscheme F
  have := connectedSpace_nilradical_subscheme F
  have hdimred : topologicalKrullDim F.nilradical.subscheme ≤ 1 :=
    (StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion F.nilradical.subschemeι).trans hdim
  have : SheafOfModules.IsInvertible F.nilradical.subscheme.presheaf
      F.nilradical.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback F.nilradical.subschemeι).obj L) :=
    MMP.Mori.isInvertible_pullback_obj F.nilradical.subschemeι L
  have hH1red := subsingleton_H1_subscheme k f hdim hH1 F.nilradical
  have hX := curveDegree_subscheme_eq_zero k f F.nilradical hdimred L hL
  have : Nonempty F.nilradical.subscheme := ConnectedSpace.toNonempty
  have := nontrivial_sections_of_curveDegree_eq_zero k (F.nilradical.subschemeι ≫ f) hdimred
    hH1red _ hX
  refine isTrivial_of_nontrivial_sections_of_curveDegree_nonpos k (F.nilradical.subschemeι ≫ f)
    hdimred _ ?_
  intro C hC
  set V : F.nilradical.subscheme.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
      (⟨C, isClosed_of_mem_irreducibleComponents C hC⟩ : TopologicalSpace.Closeds
        F.nilradical.subscheme)
  have hVint : IsIntegral V.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hC.1
  have hVd : topologicalKrullDim V.subscheme ≤ 1 :=
    (StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion V.subschemeι).trans hdimred
  have h0 := hL V.subscheme (V.subschemeι ≫ F.nilradical.subschemeι) hVd
  refine le_of_eq (Eq.trans ?_ h0)
  have : SheafOfModules.IsInvertible V.subscheme.presheaf V.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (V.subschemeι ≫ F.nilradical.subschemeι)).obj L) :=
    MMP.Mori.isInvertible_pullback_obj _ L
  have : SheafOfModules.IsInvertible V.subscheme.presheaf V.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback V.subschemeι).obj
        ((Scheme.Modules.pullback F.nilradical.subschemeι).obj L)) :=
    MMP.Mori.isInvertible_pullback_obj _ _
  exact invertibleCurveDegree_eq_of_iso k _ hVd
    ((Scheme.Modules.pullbackComp V.subschemeι F.nilradical.subschemeι).app L)

/-- **Numerically trivial line bundles on a curve with `H¹(𝒪) = 0` are trivial.** Let `F` be a
connected projective scheme of dimension at most one over an algebraically closed field `k` of
characteristic zero with `H¹(F, 𝒪_F) = 0`. An invertible `𝒪_F`-module `L` with
`MMP.Mori.degreeOn` equal to zero along every integral closed curve `i : C ⟶ F` is isomorphic
to the structure sheaf. -/
@[mmp "lem_mmp_lc_bpf_curve_fibre_trivial_line"]
public theorem nonempty_iso_unit_of_degreeOn_eq_zero (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] {F : Scheme.{u}} (f : F ⟶ Spec (.of k)) (hf : IsProjective f) [ConnectedSpace F]
    (hdim : topologicalKrullDim F ≤ 1)
    (hH1 : Subsingleton (cohomologyOverField k f (SheafOfModules.unit F.ringCatSheaf) 1))
    (L : F.Modules) [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L]
    (hL : ∀ (C : Scheme.{u}) (i : C ⟶ F) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ f)] (hC : topologicalKrullDim C ≤ 1), degreeOn k f i hC L = 0) :
    Nonempty (L ≅ SheafOfModules.unit F.ringCatSheaf) := by
  have := hf.isProper
  exact nonempty_iso_unit_of_pullback_nilradical k f hH1 L
    (nonempty_pullback_nilradical_iso_unit k f hdim hH1 L hL)

end CurveFibre

end MMP.Mori

end
