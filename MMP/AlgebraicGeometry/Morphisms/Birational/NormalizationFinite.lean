module
public import MMP.AlgebraicGeometry.Variety.Basic
public import MMP.AlgebraicGeometry.Normalization.IntegralScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiAffineSource.Basic

/-!
# The normalization of a variety is a finite birational normal variety

Let `X` be a variety over a field `K`, that is an integral scheme of finite type over `Spec K`.
Its normalization `X̃ = MMP.Intersection.Scheme.integralNormalization X`, glued from the spectra
of the integral closures of the coordinate rings of the affine opens of `X` in the function field
`R(X)`, is again a variety over `K` (with the structure morphism `X̃ ⟶ X ⟶ Spec K`), it is a
normal variety, and the normalization morphism `X̃ ⟶ X` is finite and birational.

## Main results

* `MMP.Intersection.Scheme.isNormalVariety_integralNormalization_and_isFinite_and_isBirational`

## Implementation notes

Finiteness is Mathlib's `AlgebraicGeometry.IsFinite` and birationality is
`AlgebraicGeometry.IsBirational`: the morphism is a bijection on generic points of irreducible
components and induces isomorphisms of the local rings there.

`integralNormalization X` is the relative normalization of `X` in `Spec 𝒪_{X,η}` at the generic
point `η`. The relative normalization of `Y` in `X` depends on `X ⟶ Y` only up to isomorphism
over `Y`, and since `𝒪_{X,η} = κ(η)` is a field, `Spec 𝒪_{X,η} ⟶ X` is isomorphic over `X` to
the inclusion of the spectrum of the residue field at the generic point, along which the
finiteness, normality and birationality of the normalization are known.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.2.6.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Intersection.Scheme

/-- The relative normalization depends on the morphism only up to isomorphism of its source:
if `f = e.hom ≫ f'` for an isomorphism `e`, the normalizations of `Y` in `X` and `X'` are
isomorphic over `Y`. -/
private noncomputable def normalizationIsoOfIso {X X' Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f']
    [QuasiSeparated f'] (e : X ≅ X') (H : f = e.hom ≫ f') :
    f.normalization ≅ f'.normalization where
  hom := f.normalizationDesc (e.hom ≫ f'.toNormalization) f'.fromNormalization (by simp [H])
  inv := f'.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization (by simp [H])
  hom_inv_id := by
    refine Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization ?_ (by simp) (by simp)
    simp
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext f' _ _ f'.fromNormalization ?_ (by simp) (by simp)
    simp

private theorem normalizationIsoOfIso_hom_fromNormalization {X X' Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f']
    [QuasiSeparated f'] (e : X ≅ X') (H : f = e.hom ≫ f') :
    (normalizationIsoOfIso f f' e H).hom ≫ f'.fromNormalization = f.fromNormalization := by
  simp [normalizationIsoOfIso]

/-- At the generic point of an integral scheme the residue map `𝒪_{X,η} ⟶ κ(η)` is an
isomorphism, the local ring being a field. -/
private theorem isIso_residue_genericPoint (X : AlgebraicGeometry.Scheme.{u}) [IsIntegral X] :
    IsIso (X.residue (genericPoint X)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(IsLocalRing.residue X.functionField).injective, X.residue_surjective _⟩

/-- For an integral scheme `X`, the normalization of `X` in `Spec 𝒪_{X,η}` is isomorphic over
`X` to its normalization in the spectrum of the residue field at the generic point. -/
private noncomputable def integralNormalizationIso (X : AlgebraicGeometry.Scheme.{u})
    [IsIntegral X] :
    letI := X.quasiCompactFromGenericPointResidueFields
      (MMP.finite_irreducibleComponents_of_isIntegral X)
    letI := X.quasiSeparatedFromGenericPointResidueFields
    integralNormalization X ≅ X.fromGenericPointResidueFields.normalization :=
  letI := X.quasiCompactFromGenericPointResidueFields
    (MMP.finite_irreducibleComponents_of_isIntegral X)
  letI := X.quasiSeparatedFromGenericPointResidueFields
  letI := isIso_residue_genericPoint X
  normalizationIsoOfIso _ _
    ((asIso (Spec.map (X.residue (genericPoint X)))).symm ≪≫
      asIso (MMP.specFunctionFieldToGenericPointResidueSpectrum X))
    (by
      simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
        MMP.specFunctionFieldToGenericPointResidueSpectrum_comp]
      simp [AlgebraicGeometry.Scheme.fromSpecResidueField])

/-- An isomorphism of integral schemes is birational. -/
private theorem isBirational_of_isIso {X Y : AlgebraicGeometry.Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsIso f] : IsBirational f := by
  refine ⟨?_, fun _ _ ↦ inferInstance⟩
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
  exact genericPoint_eq_of_isOpenImmersion f

/-- An integral normal scheme is a normal variety: the ring of sections over every nonempty
affine open is integrally closed in the function field. -/
private theorem isNormalVariety_of_isNormal (X : AlgebraicGeometry.Scheme.{u}) [IsIntegral X]
    [IsNormal X] : IsNormalVariety X := by
  intro U hU _
  have hU' := (isNormal_iff_forall_affineOpen_normal X).1 inferInstance ⟨U, hU⟩ inferInstance
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField).1 hU'

/-- The normalization `X̃` of a variety `X` over a field `K` is a normal variety over `K`, and the
normalization morphism `X̃ ⟶ X` is finite and birational. -/
@[mmp "lem_mmp_foundation_normalization_finite_birational"]
public theorem isNormalVariety_integralNormalization_and_isFinite_and_isBirational
    (K : Type u) [Field K] (X : AlgebraicGeometry.Scheme.{u}) [X.Over (Spec (.of K))]
    [hX : IsIntegralAlgebraicScheme K X] :
    letI : (integralNormalization X).Over (Spec (.of K)) :=
      ⟨fromIntegralNormalization X ≫ X ↘ Spec (.of K)⟩
    (∃ _ : IsIntegralAlgebraicScheme K (integralNormalization X),
        IsNormalVariety (integralNormalization X)) ∧
      IsFinite (fromIntegralNormalization X) ∧ IsBirational (fromIntegralNormalization X) := by
  letI : (integralNormalization X).Over (Spec (.of K)) :=
    ⟨fromIntegralNormalization X ≫ X ↘ Spec (.of K)⟩
  have hfin := MMP.finite_irreducibleComponents_of_isIntegral X
  have := X.quasiCompactFromGenericPointResidueFields hfin
  have := X.quasiSeparatedFromGenericPointResidueFields
  have : LocallyOfFiniteType (X ↘ Spec (.of K)) := hX.locallyOfFiniteType
  have : QuasiCompact (X ↘ Spec (.of K)) := hX.quasiCompact
  set φ := integralNormalizationIso X
  have hφ : φ.hom ≫ X.normalization hfin = fromIntegralNormalization X :=
    normalizationIsoOfIso_hom_fromNormalization _ _ _ _
  have : IsIntegral (integralNormalization X) :=
    inferInstanceAs (IsIntegral (X.fromSpecStalk (genericPoint X)).normalization)
  have : IsIntegral (X.normalizationScheme hfin) := isIntegral_of_isOpenImmersion φ.inv
  have := normalization_isFinite X (isJapaneseScheme_of_isNagataScheme X
    (isNagataScheme_of_locallyOfFiniteType_over_field K (X ↘ Spec (.of K))))
  have := X.isNormal_normalizationScheme hfin
  have : IsNormal (integralNormalization X) := isNormal_of_iso φ
  refine ⟨⟨?_, isNormalVariety_of_isNormal _⟩, hφ ▸ inferInstance,
    hφ ▸ (isBirational_of_isIso φ.hom).comp (X.isBirational_normalization hfin)⟩
  exact
    { locallyOfFiniteType := hφ ▸ inferInstanceAs (LocallyOfFiniteType (φ.hom ≫ _ ≫ X ↘ _))
      quasiCompact := hφ ▸ inferInstanceAs (QuasiCompact (φ.hom ≫ _ ≫ X ↘ _)) }

end MMP.Intersection.Scheme
