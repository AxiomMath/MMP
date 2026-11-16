module
public import MMP.Attr
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import MMP.AlgebraicGeometry.Resolution.Surface.CurveMultiplicity
public import MMP.AlgebraicGeometry.Curves.DegreeEuler
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import MMP.RingTheory.RegularLocalRing.LeadingTerm
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupFactorization
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothFibreTwist

/-!
# Degrees of line bundles on curves, and the exceptional curve of a point blow-up

Let `C` be a projective curve over a field `k`. Kollár's degree `deg_C` of a line bundle on `C`
(`MMP.Resolution.degree`) is additive on tensor products,
`deg_C(L₁ ⊗ ⋯ ⊗ Lₘ) = deg_C L₁ + ⋯ + deg_C Lₘ`, and multiplicative along a finite surjective
`k`-morphism `π : C' ⟶ C` of integral projective curves,
`deg_{C'} π^*L = [k(C') : k(C)] · deg_C L`.

Let `S` be a scheme and `p ∈ S` a closed point whose local ring `𝒪_{S,p}` is regular
of dimension `2`. The exceptional curve `E = π⁻¹(p)` of the blow-up `π : B_pS → S` of the
reduced point `p` is isomorphic over the residue field `κ(p)` to the projective line
`ℙ¹_{κ(p)}`.

## Main results

* `MMP.Resolution.degree_foldl_tensorObj`: `deg_C(𝒪_C ⊗ L₁ ⊗ ⋯ ⊗ Lₘ) = ∑ᵢ deg_C Lᵢ`.
* `MMP.Resolution.degree_pullback_eq_degreeOver_mul`: `deg_{C'} π^*L = [k(C') : k(C)] · deg_C L`.
* `MMP.Resolution.exists_exceptionalIdeal_subscheme_iso_projSpace`: `E ≅ ℙ¹_{κ(p)}` over `κ(p)`.

## Implementation notes

The family `L₁, …, Lₘ` is a list, and its tensor product is the left fold
`(⋯((𝒪_C ⊗ L₁) ⊗ L₂) ⋯) ⊗ Lₘ` in the monoidal category of `𝒪_C`-modules, which is canonically
isomorphic to `L₁ ⊗ ⋯ ⊗ Lₘ`. Starting from the unit makes the empty list (`m = 0`, with
`deg_C 𝒪_C = 0`) part of the statement, and the list `[L, …, L]` of length `n` gives exactly
`MMP.Intersection.Scheme.tensorPow L n`.

Both degree statements go through the Euler-characteristic degree `χ(C, L) - χ(C, 𝒪_C)`
(`MMP.Resolution.degree_eq_invertibleCurveDegree`), which is additive on tensor products
([Stacks, Tag 0AYX]) and multiplicative along nonconstant morphisms of proper curves
([Stacks, Tag 0AYZ]). In the first, `[k(C') : k(C)]` is `AlgebraicGeometry.degreeOver π`.

For the exceptional curve, the blow-up is `AlgebraicGeometry.blowUp` of the vanishing ideal of
the closed set `{p}`, `E` is the subscheme of `AlgebraicGeometry.exceptionalIdeal`, and the
projective line is `MMP.Intersection.ProjSpace κ(p) (ULift (Fin 2))`, that is
`Proj κ(p)[T₀, T₁]`. Since `Spec κ(p) → S` is a monomorphism, `E` has at most one
`κ(p)`-structure compatible with its map to `S`; being an isomorphism over `κ(p)` is therefore
phrased as compatibility of the maps to `S`. Rather than glueing the two charts `Spec κ[y/x]`
and `Spec κ[x/y]` as the source does, both `E` and `ℙ¹_{κ(p)}` are exhibited as the fibre
product of `π` with `Spec κ(p) ⟶ S`: for `E` this is the cartesian square of closed immersions,
and for `ℙ¹_{κ(p)}` it is the local computation of [Stacks, Tag 0AGQ] at `𝒪_{S,p}`, carried to
`S` along the flat base change `Spec 𝒪_{S,p} ⟶ S` ([Stacks, Tag 0805]).

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.12–1.13, 1.20, 1.36
* [Stacks Project, Tags 0AYX, 0AYZ, 0AGQ, 0805](https://stacks.math.columbia.edu)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry CategoryTheory.Limits IsLocalRing

namespace MMP.Resolution

section TensorPower

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  [MMP.Mori.IsCurve k sC] [MMP.Mori.IsProjectiveVariety k sC]

/-- The tensor product of two invertible sheaves is invertible. -/
private theorem isInvertibleModule_tensorObj (L M : C.Modules)
    [Stacks.Ample.IsInvertibleModule C L] [Stacks.Ample.IsInvertibleModule C M] :
    Stacks.Ample.IsInvertibleModule C (L ⊗ M) :=
  Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible C.presheaf C.ringCatSheaf.2 L M

/-- `deg_C(L ⊗ M) = deg_C L + deg_C M` for invertible sheaves `L` and `M`. -/
private theorem degree_tensorObj (L M : C.Modules)
    [Stacks.Ample.IsInvertibleModule C L] [Stacks.Ample.IsInvertibleModule C M] :
    degree sC (L ⊗ M) = degree sC L + degree sC M := by
  have hdim := (IsCurve.topologicalKrullDim_eq_one sC).le
  have := isInvertibleModule_tensorObj L M
  simp only [degree_eq_invertibleCurveDegree sC _ hdim]
  exact invertibleCurveDegree_tensorSheaf_eq_add k sC hdim L M

/-- The degree of the left fold `(⋯(M ⊗ L₁) ⊗ ⋯) ⊗ Lₘ` of invertible sheaves is
`deg_C M + ∑ᵢ deg_C Lᵢ`. -/
private theorem degree_foldl_tensorObj_eq_add (Ls : List C.Modules)
    (hLs : ∀ L ∈ Ls, Stacks.Ample.IsInvertibleModule C L) (M : C.Modules)
    [Stacks.Ample.IsInvertibleModule C M] :
    degree sC (Ls.foldl (· ⊗ ·) M) = degree sC M + (Ls.map (degree sC)).sum := by
  induction Ls generalizing M with
  | nil => simp
  | cons L Ls ih =>
    have := hLs L (List.mem_cons_self ..)
    have := isInvertibleModule_tensorObj M L
    rw [List.foldl_cons, ih (fun L' hL' => hLs L' (List.mem_cons_of_mem _ hL')),
      degree_tensorObj sC M L, List.map_cons, List.sum_cons, add_assoc]

end TensorPower

/-- **Additivity of the degree** (Kollár 1.12–1.13, 1.20): for line bundles `L₁, …, Lₘ` on a
projective curve `C` over `k`, `deg_C(L₁ ⊗ ⋯ ⊗ Lₘ) = ∑ᵢ deg_C Lᵢ`, the tensor product being the
left fold `(⋯(𝒪_C ⊗ L₁) ⊗ ⋯) ⊗ Lₘ`. -/
@[mmp "lem_kr1a_degree_of_tensor_power"]
public theorem degree_foldl_tensorObj {k : Type u} [Field k] {C : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) [MMP.Mori.IsCurve k sC] [MMP.Mori.IsProjectiveVariety k sC]
    (Ls : List C.Modules) (hLs : ∀ L ∈ Ls, Stacks.Ample.IsInvertibleModule C L) :
    degree sC (Ls.foldl (· ⊗ ·) (𝟙_ C.Modules)) = (Ls.map (degree sC)).sum := by
  have : Stacks.Ample.IsInvertibleModule C (𝟙_ C.Modules) := Scheme.Modules.isInvertible_unit C
  have hdim := (IsCurve.topologicalKrullDim_eq_one sC).le
  rw [degree_foldl_tensorObj_eq_add sC Ls hLs, degree_eq_invertibleCurveDegree sC _ hdim,
    show invertibleCurveDegree k sC hdim (𝟙_ C.Modules) = 0 from
      invertibleCurveDegree_unit_eq_zero k sC hdim, zero_add]

/-- A surjective morphism onto a curve is not constant: a curve has dimension one, so it has
at least two points. -/
private theorem not_exists_forall_eq_of_surjective {k : Type u} [Field k] {C C' : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) [MMP.Mori.IsCurve k sC] (π : C' ⟶ C) [Surjective π] :
    ¬ ∃ y : C, ∀ x : C', π.base x = y := by
  rintro ⟨y, hy⟩
  have : Subsingleton C := ⟨π.surjective.forall₂.2 fun a b => (hy a).trans (hy b).symm⟩
  have h := topologicalKrullDim_zero_of_discreteTopology C
  rw [IsCurve.topologicalKrullDim_eq_one (f := sC)] at h
  exact absurd h (by decide)

/-- **Degree under a finite morphism of curves.** Let `π : C' ⟶ C` be a finite surjective
`k`-morphism of integral projective curves over `k` and `L` an invertible sheaf on `C`. Then
Kollár's degree satisfies `deg_{C'} π^*L = [k(C') : k(C)] · deg_C L`. -/
@[mmp "lem_mmp_foundation_kr_finite_curve_degree_pullback"]
public theorem degree_pullback_eq_degreeOver_mul {k : Type u} [Field k] {C C' : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) (sC' : C' ⟶ Spec (.of k))
    [MMP.Mori.IsCurve k sC] [MMP.Mori.IsProjectiveVariety k sC]
    [MMP.Mori.IsCurve k sC'] [MMP.Mori.IsProjectiveVariety k sC']
    (π : C' ⟶ C) [IsFinite π] [Surjective π] (hπ : π ≫ sC = sC')
    (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L] :
    degree sC' ((Scheme.Modules.pullback π).obj L) = (degreeOver π : ℤ) * degree sC L := by
  rw [degree_eq_invertibleCurveDegree sC' _ (IsCurve.topologicalKrullDim_eq_one (f := sC')).le,
    degree_eq_invertibleCurveDegree sC L (IsCurve.topologicalKrullDim_eq_one (f := sC)).le,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact curveDegree_pullback_eq_degreeOver_mul k sC' sC π hπ
    (not_exists_forall_eq_of_surjective sC π) L 1

section ExceptionalCurve

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The two structure morphisms `Proj R[T₀, T₁] ⟶ Spec R` agree. -/
private theorem projSpaceToSpec_two_eq (R : Type u) [CommRing R] :
    Stacks.Blowup.projSpaceToSpec R 2 =
      Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R 1 := by
  rw [Stacks.Blowup.projSpaceToSpec, Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff]
  congr 3
  ext r : 1
  change AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv (Fin 2) R r =
    GradedRing.projZeroRingHom' (MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (algebraMap R (MvPolynomial (Fin 2) R) r)
  rw [← SetLike.GradeZero.coe_algebraMap (MvPolynomial.homogeneousSubmodule (Fin 2) R) r,
    GradedRing.projZeroRingHom'_apply_coe]
  rfl

/-- Changing the coefficients of `Proj R[T₀, T₁]` along `R → R/I` lies over
`Spec (R/I) ⟶ Spec R`. -/
private theorem projMap_polyGradedMap_comp_projSpaceToSpec (R : Type u) [CommRing R]
    (I : Ideal R) :
    Proj.map (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (Ideal.Quotient.mk I))
        (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
          (Ideal.Quotient.mk I)) ≫ Stacks.Blowup.projSpaceToSpec R 2 =
      Stacks.Blowup.projSpaceToSpec (R ⧸ I) 2 ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [Stacks.Blowup.projSpaceToSpec, Proj.map_toSpecZero_assoc, Stacks.Blowup.projSpaceToSpec,
    Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext r : 2
  apply Subtype.ext
  change MvPolynomial.map (Ideal.Quotient.mk I) (MvPolynomial.C r) =
    MvPolynomial.C (Ideal.Quotient.mk I r)
  rw [MvPolynomial.map_C]

/-- The inverse image of a closed subscheme is its fibre product. -/
private theorem isPullback_comap_subschemeι {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) :
    IsPullback (J.comap f).subschemeι ((J.comap f).subschemeMap J f (J.le_map_comap f)) f
      J.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])

/-- **The local computation** (part (1) of [Stacks, Tag 0AGQ], as a fibre square). For a regular
local ring `A` of dimension two, `ℙ¹_κ` is the fibre of the blow-up of `Spec A` in `𝔪` over the
closed point. -/
private theorem exists_isPullback_blowUpSpec (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) :
    ∃ s : AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin 2) (A ⧸ maximalIdeal A)) ⟶
          Stacks.Blowup.blowUpSpec (maximalIdeal A),
      IsPullback s (Stacks.Blowup.projSpaceToSpec (A ⧸ maximalIdeal A) 2)
        (Stacks.Blowup.toSpec (maximalIdeal A))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))) := by
  obtain ⟨r, -, hr, ρ, hρ, -⟩ :=
    Stacks.Blowup.exists_isClosedImmersion_blowUpSpec_maximalIdeal_exceptional_projectiveLine
      A hdim
  haveI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  -- `E` is the fibre of the blow-up over the closed subscheme `V(𝔪)`
  have hpb := isPullback_comap_subschemeι (Stacks.Blowup.toSpec (maximalIdeal A))
    (Scheme.IdealSheafData.ofIdealTop
      (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (maximalIdeal A)))
  have hq := Stacks.Blowup.specQuotientIsoSubscheme_hom_comp_subschemeι (maximalIdeal A)
  rw [← Iso.eq_inv_comp] at hq
  refine ⟨ρ.inv ≫ (Stacks.Blowup.exceptionalIdealData (maximalIdeal A)).subschemeι,
    hpb.of_iso ρ (Iso.refl _) (Stacks.Blowup.specQuotientIsoSubscheme (maximalIdeal A)).symm
      (Iso.refl _) (by rw [Iso.refl_hom, Category.comp_id]; exact (Iso.hom_inv_id_assoc ρ _).symm)
      ?_ (by simp) (by simpa using hq)⟩
  rw [Iso.symm_hom,
    ← cancel_mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))),
    Category.assoc, ← hq, Scheme.IdealSheafData.subschemeMap_subschemeι, Category.assoc,
    ← projMap_polyGradedMap_comp_projSpaceToSpec]
  exact (congrArg (_ ≫ ·) hr.symm).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hρ).trans (Category.assoc _ _ _)))

/-- The same fibre square for `AlgebraicGeometry.blowUp` of the ideal sheaf of the closed
point. -/
private theorem exists_isPullback_blowUp_specIdealSheaf (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (K : (Spec (CommRingCat.of A)).IdealSheafData)
    (hK : K = Stacks.Blowup.AffineModel.specIdealSheaf (maximalIdeal A)) :
    ∃ s : AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin 2) (A ⧸ maximalIdeal A)) ⟶ blowUp K,
      IsPullback s (Stacks.Blowup.projSpaceToSpec (A ⧸ maximalIdeal A) 2) (blowUpToBase K)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))) := by
  subst hK
  obtain ⟨s, hs⟩ := exists_isPullback_blowUpSpec A hdim
  obtain ⟨d, hd, -⟩ := Stacks.Blowup.AffineModel.exists_iso_blowUpTwist (maximalIdeal A)
  exact ⟨s ≫ d.hom, hs.of_iso (Iso.refl _) d (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (by simp [hd]) (by simp)⟩

/-- **`E` is the fibre of the blow-up over `Spec κ(p)`.** For a closed point `p` of a scheme `S`,
the exceptional subscheme of the blow-up of `S` in `p` is the fibre product of `blowUpToBase`
with `S.fromSpecResidueField p`. -/
private theorem exists_isPullback_exceptionalIdeal_subschemeι {S : Scheme.{u}} {p : S}
    (hp : IsClosed ({p} : Set S)) :
    ∃ g, IsPullback (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).subschemeι
      g (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
      (S.fromSpecResidueField p) := by
  set Z := Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : TopologicalSpace.Closeds S)
  haveI : IsClosedImmersion (S.fromSpecResidueField p) :=
    isClosed_singleton_iff_isClosedImmersion.1 hp
  have hker : (S.fromSpecResidueField p).ker ≤
      ((exceptionalIdeal Z).subschemeι ≫ blowUpToBase Z).ker := by
    rw [fromSpecResidueField_ker_eq_vanishingIdeal p hp,
      ← Scheme.IdealSheafData.subschemeMap_subschemeι (exceptionalIdeal Z) Z (blowUpToBase Z)
        (Z.le_map_comap (blowUpToBase Z))]
    refine le_trans ?_ (Scheme.Hom.le_ker_comp _ _)
    rw [Scheme.IdealSheafData.ker_subschemeι]
  exact ⟨_, isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ hker).symm
    (by rw [fromSpecResidueField_ker_eq_vanishingIdeal p hp, Scheme.IdealSheafData.ker_subschemeι])⟩

/-- **`ℙ¹_{κ(p)}` is the fibre of the blow-up over `Spec κ(p)`.** The local computation
`exists_isPullback_blowUp_specIdealSheaf` at `𝒪_{S,p}`, carried to `S` along the flat morphism
`Spec 𝒪_{S,p} ⟶ S`. -/
private theorem exists_isPullback_projSpace_blowUpToBase {S : Scheme.{u}} {p : S}
    (hp : IsClosed ({p} : Set S)) [IsRegularLocalRing (S.presheaf.stalk p)]
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2) :
    ∃ s, IsPullback s (MMP.Intersection.ProjSpace.toSpec (S.residueField p) (ULift.{u} (Fin 2)))
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
      (S.fromSpecResidueField p) := by
  set Z := Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : TopologicalSpace.Closeds S)
  haveI : Flat (S.fromSpecStalk p) := flat_fromSpecStalk S p
  obtain ⟨h, hpb⟩ := exists_isPullback_blowUpToBase_comap (S.fromSpecStalk p) Z
  obtain ⟨s, hs⟩ := exists_isPullback_blowUp_specIdealSheaf _ hdim (Z.comap (S.fromSpecStalk p))
    (Stacks.Blowup.vanishingIdeal_comap_fromSpecStalk_eq_specIdealSheaf p hp)
  refine ⟨_, (hs.paste_horiz hpb.flip).of_iso
    (MMP.Intersection.ProjSpace.isoPolyGrading (S.residueField p) 1).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans
      (Iso.inv_hom_id_assoc _ _).symm) ?_ (by simp)
    ((Category.comp_id _).trans (Category.id_comp _).symm)⟩
  exact (Category.comp_id _).trans ((projSpaceToSpec_two_eq _).trans
    (MMP.Threefold.Resolution.isoPolyGrading_inv_comp_toSpec (S.residueField p) 1).symm)

end ExceptionalCurve

/-- **The exceptional curve is a projective line** (Kollár 1.36). Let `S` be a scheme and
`p ∈ S` a closed point with `𝒪_{S,p}` regular of dimension `2`. Then the exceptional curve
`E = π⁻¹(p)` of the blow-up `π : B_pS → S` of `p` is isomorphic over `κ(p)` to `ℙ¹_{κ(p)}`. -/
@[mmp "lem_kr1b_exceptional_curve_projective_line"]
public theorem exists_exceptionalIdeal_subscheme_iso_projSpace {S : Scheme.{u}}
    {p : S} (hp : IsClosed ({p} : Set S)) [IsRegularLocalRing (S.presheaf.stalk p)]
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2) :
    ∃ e : (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).subscheme ≅
        MMP.Intersection.ProjSpace (S.residueField p) (ULift.{u} (Fin 2)),
      e.hom ≫ MMP.Intersection.ProjSpace.toSpec (S.residueField p) _ ≫
          S.fromSpecResidueField p =
        (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).subschemeι ≫
          blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) := by
  obtain ⟨g, hE⟩ := exists_isPullback_exceptionalIdeal_subschemeι hp
  obtain ⟨s, hP⟩ := exists_isPullback_projSpace_blowUpToBase hp hdim
  refine ⟨hE.isoIsPullback _ _ hP, ?_⟩
  rw [← Category.assoc, hE.isoIsPullback_hom_snd]
  exact hE.w.symm

end MMP.Resolution

end
