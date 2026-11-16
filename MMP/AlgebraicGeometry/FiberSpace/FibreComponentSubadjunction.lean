module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
public import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
public import MMP.AlgebraicGeometry.Singularities.CurveFibreSubadjunction
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Bertini.GeneralHyperplane
public import MMP.AlgebraicGeometry.Geometrically.BertiniGenericFibres
public import MMP.AlgebraicGeometry.Geometrically.HyperplaneSectionIntegralFibres
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Divisor.Canonical.SmoothAdjunction
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
public import MMP.AlgebraicGeometry.SpreadingOut.GenericFibreDimension
public import MMP.AlgebraicGeometry.MMP.Abundance.NumericalDimensionOnePencil
public import MMP.AlgebraicGeometry.Singularities.Bertini.HyperplaneDiscrepancyBound
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Divisor.GeneralMemberAdjunction
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Chow.FieldSituation

section

/-!
# Weak subadjunction on a component of maximal dimension of a fibre

Let `(X, B)` be a klt pair with `B` an effective `ℚ`-divisor on a projective variety `X` of
dimension `n` over an algebraically closed field `k` of characteristic zero, and let
`f : X ⟶ S` be a projective morphism of `k`-schemes. Let `E` be an integral closed subscheme of
a fibre `f⁻¹(s)` whose dimension `r` equals that of the whole fibre, with `1 ≤ r ≤ n - 1`, and
let `ν : Eᵛ ⟶ E` be its normalization. For a general complete intersection
`C = E ∩ H₁ ∩ ⋯ ∩ H_{r-1}` of hyperplanes of a projective embedding of `X`, the preimage
`Cᵛ = ν⁻¹(C)` is a smooth curve inside the smooth locus of `Eᵛ`, and
`(K_X + B) · C ≥ K_{Eᵛ} · Cᵛ`, the right side being the degree on `Cᵛ` of the restriction of the
canonical sheaf of the smooth locus of `Eᵛ`.

Cutting `X` by the general hyperplanes gives a klt pair `(X₀, B₀)` whose fibre over `s` has
dimension at most one, so
`MMP.Fourfold.invertibleCurveDegree_relativeDifferentials_normalization_le_intersectionNumber`
applies to it; adjunction on the smooth locus of `Eᵛ` gives
`deg ω_{Cᵛ} = K_{Eᵛ} · Cᵛ + (r - 1) H · C`, and `K_{X₀} + B₀ = (K_X + B + (r - 1) H)|_{X₀}`.

## Main results

* `MMP.Fourfold.exists_invertibleCurveDegree_canonicalSheaf_normalization_le_intersectionNumber`:
  the inequality above, for all complete intersections off a proper Zariski-closed subset of the
  parameter space of `(r - 1)`-tuples of hyperplanes.

## Implementation notes

* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero.
* "`H` sufficiently ample" is realised by an arbitrary closed embedding `φ : X ⟶ ℙᴺ_k` over `k`,
  the hyperplanes being `MMP.Threefold.Bridges.hyperplaneSection`; only very ampleness is used.
  "General" means: off the zero locus of a nonzero polynomial in the hyperplane coefficients.
* `K_{Eᵛ} · Cᵛ` is `AlgebraicGeometry.invertibleCurveDegree` of the pullback to `Cᵛ` of
  `MMP.Mori.canonicalSheaf` on the smooth locus of `Eᵛ`; no global `ℚ`-Cartier hypothesis on
  `K_{Eᵛ}` is made. Smoothness of `Cᵛ`, its containment in the smooth locus and invertibility of
  the restricted canonical sheaf are part of the conclusion.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Threefold.Bridges

namespace MMP.FourfoldProofs.FourfoldMaximalFibreComponentWeakSubadjunctionProof

/-- The degree of the sheaf of differentials of a proper curve is invariant under an
isomorphism over the base field. -/
private theorem invertibleCurveDegree_relativeDifferentials_eq_of_isIso {k : Type} [Field k]
    {C D : Scheme.{0}} {gC : C ⟶ Spec (.of k)} {gD : D ⟶ Spec (.of k)} (e : C ⟶ D) [IsIso e]
    (he : e ≫ gD = gC) [IsProper gC] [IsProper gD] (hC : topologicalKrullDim C ≤ 1)
    (hD : topologicalKrullDim D ≤ 1)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 (Scheme.Hom.relativeDifferentials gC)]
    [SheafOfModules.IsInvertible D.presheaf D.ringCatSheaf.2 (Scheme.Hom.relativeDifferentials gD)] :
    invertibleCurveDegree k gC hC (Scheme.Hom.relativeDifferentials gC) =
      invertibleCurveDegree k gD hD (Scheme.Hom.relativeDifferentials gD) := by
  subst he
  rw [← invertibleCurveDegree_pullback_of_isIso e gD hC hD]
  have := Scheme.Hom.isIso_relativeDifferentialsMap_of_isIso e gD (e ≫ gD) (𝟙 _) (Category.comp_id _).symm
  exact (invertibleCurveDegree_eq_of_iso k _ hC
    (asIso (Scheme.Hom.relativeDifferentialsMap e gD (e ≫ gD) (𝟙 _) (Category.comp_id _).symm))).symm

/-- **The differentials of a smooth model of a curve have the degree of those of its
normalization.** If `α : C' ⟶ C` is a finite birational morphism from a normal scheme `C'`,
smooth over `k`, to a proper curve `C`, then `C'` is the normalization of `C`, so
`deg Ω_{C'/k} = deg Ω_{Cᵛ/k}`. -/
private theorem invertibleCurveDegree_relativeDifferentials_eq_normalization {k : Type} [Field k]
    [PerfectField k] {C C' : Scheme.{0}} (sC : C ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k sC]
    [IsProper sC] (α : C' ⟶ C) [IsFinite α] [IsNormal C'] (hα : IsBirational α)
    [AlgebraicGeometry.IsCurve k (α ≫ sC)] [Smooth (α ≫ sC)] (hC' : topologicalKrullDim C' ≤ 1)
    (hN : topologicalKrullDim (normalizationSchemeOverField k sC) ≤ 1) :
    haveI := isProper_normalizationOverField_comp k sC
    @invertibleCurveDegree k _ _ (α ≫ sC) _ hC' (Scheme.Hom.relativeDifferentials (α ≫ sC))
        (isInvertible_relativeDifferentials_of_isCurve (k := k) (α ≫ sC)) =
      @invertibleCurveDegree k _ _ (normalizationOverField k sC ≫ sC) _ hN
        (Scheme.Hom.relativeDifferentials (normalizationOverField k sC ≫ sC))
        (MMP.Fourfold.isInvertible_relativeDifferentials_normalization_comp sC _) := by
  haveI := isProper_normalizationOverField_comp k sC
  haveI : SheafOfModules.IsInvertible _ _
      (Scheme.Hom.relativeDifferentials (normalizationOverField k sC ≫ sC)) :=
    MMP.Fourfold.isInvertible_relativeDifferentials_normalization_comp sC _
  haveI := isInvertible_relativeDifferentials_of_isCurve (k := k) (α ≫ sC)
  obtain ⟨e, he⟩ := Scheme.exists_iso_normalizationScheme_of_isIntegralHom_of_isBirational
    (finite_irreducibleComponents_of_locallyOfFiniteType k sC) α
    (fun U hU => finite_irreducibleComponents_of_locallyOfFiniteType k (α ≫ sC) _
      (QuasiCompact.isCompact_preimage (f := α) _ U.2 hU))
    (fun U _ => hα.restrict U)
  have he' : e.hom ≫ normalizationOverField k sC ≫ sC = α ≫ sC := by
    rw [← Category.assoc, he]
  exact @invertibleCurveDegree_relativeDifferentials_eq_of_isIso k _ C' _ (α ≫ sC)
    (normalizationOverField k sC ≫ sC) e.hom _ he' _ _ hC' hN _
    (MMP.Fourfold.isInvertible_relativeDifferentials_normalization_comp sC _)

/-- On a curve, the canonical sheaf of the smooth locus, pulled back along an isomorphism onto
the smooth locus, is the sheaf of differentials. -/
private theorem nonempty_pullback_canonicalSheaf_one_iso {k : Type} [Field k] {Y V : Scheme.{0}}
    (g : Y ⟶ Spec (.of k)) (j : V ⟶ Y) (hj : Set.range j ⊆ Set.range (smoothLocus g).ι)
    [IsIso (IsOpenImmersion.lift (smoothLocus g).ι j hj)] :
    Nonempty ((Scheme.Modules.pullback (IsOpenImmersion.lift (smoothLocus g).ι j hj)).obj
      (canonicalSheaf g 1) ≅ Scheme.Hom.relativeDifferentials (j ≫ g)) := by
  set ℓ := IsOpenImmersion.lift (smoothLocus g).ι j hj
  have hℓ : ℓ ≫ ((smoothLocus g).ι ≫ g) = (j ≫ g) ≫ 𝟙 _ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialsMap_of_isIso ℓ _ _ (𝟙 _) hℓ
  exact ⟨(Scheme.Modules.pullback ℓ).mapIso (Scheme.Modules.exteriorPowerOneIsoSelf _) ≪≫
    asIso (Scheme.Hom.relativeDifferentialsMap ℓ _ _ (𝟙 _) hℓ)⟩

/-- The degree of the sheaf of differentials depends on the structure morphism only through its
value. -/
private theorem invertibleCurveDegree_relativeDifferentials_congr {k : Type} [Field k]
    {C : Scheme.{0}} {p p' : C ⟶ Spec (.of k)} (h : p = p') [IsProper p] [IsProper p']
    {hdim : topologicalKrullDim C ≤ 1}
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 (Scheme.Hom.relativeDifferentials p)]
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Scheme.Hom.relativeDifferentials p')] :
    invertibleCurveDegree k p hdim (Scheme.Hom.relativeDifferentials p) =
      invertibleCurveDegree k p' hdim (Scheme.Hom.relativeDifferentials p') := by
  subst h; rfl

/-- The inclusion of the open subscheme `⊤` is an isomorphism. -/
private theorem isIso_ι_of_eq_top {Y : Scheme.{0}} {U : Y.Opens} (hU : U = ⊤) : IsIso U.ι := by
  subst hU; rw [← Scheme.topIso_hom]; infer_instance

/-- An isomorphism of schemes preserves the Krull dimension. -/
private theorem topologicalKrullDim_eq_of_isIso {Y Z : Scheme.{0}} (e : Y ⟶ Z) [IsIso e] :
    topologicalKrullDim Y = topologicalKrullDim Z :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso e)).isHomeomorph

/-- A point of the base over which the fibre contains the image of a nonempty proper scheme is
closed: that image is closed and lies in the point. -/
private theorem isClosed_singleton_of_range_subset {X S E : Scheme.{0}} (f : X ⟶ S)
    (hf : IsProjectiveMorphism f) (i : E ⟶ X) [IsClosedImmersion i] [Nonempty E] {s : S}
    (hEs : Set.range i ⊆ f ⁻¹' {s}) : IsClosed ({s} : Set S) := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  have hrange : Set.range (i ≫ f) = {s} := by
    obtain ⟨e⟩ := ‹Nonempty E›
    refine Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨⟨_, e, rfl⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hEs ⟨x, rfl⟩
  rw [← hrange]
  exact (i ≫ f).isClosedMap.isClosed_range

/-- A Noetherian `T₀` space of dimension at most zero is finite: its irreducible components are
points. -/
private theorem finite_of_topologicalKrullDim_nonpos {Z : Type*} [TopologicalSpace Z] [T0Space Z]
    [TopologicalSpace.NoetherianSpace Z] (h : topologicalKrullDim Z ≤ 0) : Finite Z := by
  have hmin := Order.krullDim_nonpos_iff_forall_isMin.1 h
  have hcl : ∀ C ∈ irreducibleComponents Z, ∀ x ∈ C, closure {x} = C := by
    intro C hC x hx
    have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
    let C' : TopologicalSpace.IrreducibleCloseds Z := ⟨C, hC.1, hCc⟩
    let D : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hDC : D ≤ C' := closure_minimal (Set.singleton_subset_iff.2 hx) hCc
    exact le_antisymm hDC (hmin C' hDC)
  have hcomp : ∀ C ∈ irreducibleComponents Z, C.Subsingleton := by
    intro C hC x hx y hy
    exact (inseparable_iff_closure_eq.2 ((hcl C hC x hx).trans (hcl C hC y hy).symm)).eq
  have hU : ⋃₀ irreducibleComponents Z = Set.univ := sUnion_irreducibleComponents
  exact Set.finite_univ_iff.mp (hU ▸ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).sUnion
    fun C hC => (hcomp C hC).finite)

/-! ### Closed subschemes of closed subschemes -/

/-- The kernel of `V(J|_{V(I)}) ⟶ V(I) ⟶ Y` contains `I ⊔ J`. -/
private theorem sup_le_ker_comap_subschemeι {Y : Scheme.{0}} (I J : Y.IdealSheafData) :
    (I ⊔ J).subschemeι.ker ≤ ((J.comap I.subschemeι).subschemeι ≫ I.subschemeι).ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_ker,
    Scheme.IdealSheafData.ker_subschemeι]
  refine sup_le ?_ (Scheme.IdealSheafData.le_map_comap _ _)
  conv_lhs => rw [← I.ker_subschemeι, ← Scheme.IdealSheafData.map_bot]
  exact Scheme.IdealSheafData.map_mono _ bot_le

/-- **`V(J) ∩ V(I)` two ways.** The closed subscheme of `V(I)` cut out by the pull-back of `J` is
the closed subscheme `V(I ⊔ J)` of `Y`. -/
private noncomputable def comapSubschemeιIso {Y : Scheme.{0}} (I J : Y.IdealSheafData) :
    (J.comap I.subschemeι).subscheme ≅ (I ⊔ J).subscheme where
  hom := IsClosedImmersion.lift (I ⊔ J).subschemeι
    ((J.comap I.subschemeι).subschemeι ≫ I.subschemeι) (sup_le_ker_comap_subschemeι I J)
  inv := Limits.pullback.lift (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J))
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J))
      (by rw [Scheme.IdealSheafData.inclusion_subschemeι,
        Scheme.IdealSheafData.inclusion_subschemeι]) ≫
    (J.comapIso I.subschemeι).inv
  hom_inv_id := by
    rw [← cancel_mono ((J.comap I.subschemeι).subschemeι ≫ I.subschemeι)]
    simp only [Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc,
      Category.id_comp]
    rw [Limits.pullback.lift_fst_assoc, Scheme.IdealSheafData.inclusion_subschemeι,
      IsClosedImmersion.lift_fac]
  inv_hom_id := by
    rw [← cancel_mono (I ⊔ J).subschemeι]
    simp only [Category.assoc, IsClosedImmersion.lift_fac, Category.id_comp,
      Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc]
    rw [Limits.pullback.lift_fst_assoc, Scheme.IdealSheafData.inclusion_subschemeι]

@[reassoc]
private theorem comapSubschemeιIso_hom_subschemeι {Y : Scheme.{0}} (I J : Y.IdealSheafData) :
    (comapSubschemeιIso I J).hom ≫ (I ⊔ J).subschemeι =
      (J.comap I.subschemeι).subschemeι ≫ I.subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

/-! ### Weak subadjunction along a closed subscheme of the component -/

section Subadjunction

variable {k : Type} [Field k] {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of k)) [IsProper sX] {E Eν : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i]
  (ν : Eν ⟶ E) [IsFinite ν] (d : ℕ) (A : E.IdealSheafData)

/-- The closed subscheme `C = V(A)` of `E ⊆ X` is a *smooth curve cut* for the normal model
`ν : Eᵛ ⟶ E`: `C` is a curve, its preimage `Cᵛ = V(ν^* A)` is a smooth curve inside the smooth
locus of `Eᵛ`, and the canonical sheaf of that smooth locus (in dimension `d`) restricts to an
invertible sheaf on `Cᵛ`. -/
private structure IsSmoothCurveCut : Prop where
  dim_eq : topologicalKrullDim A.subscheme = 1
  dim_le : topologicalKrullDim (A.comap ν).subscheme ≤ 1
  range_subset : Set.range (A.comap ν).subschemeι ⊆ smoothLocus (ν ≫ i ≫ sX)
  smooth : Smooth ((A.comap ν).subschemeι ≫ ν ≫ i ≫ sX)
  isInvertible : SheafOfModules.IsInvertible _ _ ((Scheme.Modules.pullback (IsOpenImmersion.lift
      (smoothLocus (ν ≫ i ≫ sX)).ι (A.comap ν).subschemeι
        (range_subset.trans_eq (Scheme.Opens.range_ι _).symm))).obj
      (canonicalSheaf (ν ≫ i ≫ sX) d))

/-- A *good curve* is a smooth curve cut `C = V(A)` such that `C` and `Cᵛ` are integral. -/
private structure IsGoodCurve : Prop extends IsSmoothCurveCut sX i ν d A where
  isIntegral : IsIntegral A.subscheme
  isIntegral_comap : IsIntegral (A.comap ν).subscheme

variable {sX i ν d A}

/-- The degree `K_{Eᵛ} · Cᵛ` of the canonical sheaf of the smooth locus of `Eᵛ` on `Cᵛ`. -/
private noncomputable def IsSmoothCurveCut.canonicalDegree (h : IsSmoothCurveCut sX i ν d A) :
    ℚ :=
  @invertibleCurveDegree k _ _ ((A.comap ν).subschemeι ≫ ν ≫ i ≫ sX) _ h.dim_le
    ((Scheme.Modules.pullback (IsOpenImmersion.lift (smoothLocus (ν ≫ i ≫ sX)).ι
      (A.comap ν).subschemeι (h.range_subset.trans_eq (Scheme.Opens.range_ι _).symm))).obj
      (canonicalSheaf (ν ≫ i ≫ sX) d)) h.isInvertible

/-- The intersection number `(K_X + B) · C`. -/
private noncomputable def IsSmoothCurveCut.intersectionNumber (h : IsSmoothCurveCut sX i ν d A)
    {K : Divisor X} {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier) : ℚ :=
  (Divisor.toQDivisor K + B).intersectionNumber k sX (A.subschemeι ≫ i) h.dim_eq.le hKB

variable (sX i ν d A) in
/-- The weak subadjunction inequality `K_{Eᵛ} · Cᵛ ≤ (K_X + B) · C` along `C = V(A)`, whenever
`C` is a good curve. -/
private def SubadjunctionAt {K : Divisor X} {B : QDivisor X}
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) : Prop :=
  ∀ h : IsGoodCurve sX i ν d A, h.canonicalDegree ≤ h.intersectionNumber hKB

end Subadjunction

/-! ### Transferring weak subadjunction from a hyperplane section -/

/-- The tensor product of two modules on a scheme, in the spelling of
`AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add`. -/
private noncomputable abbrev tensorModules {C : Scheme.{0}} (M N : C.Modules) : C.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨C.toRingedSpace.presheaf,
    C.toRingedSpace.IsSheaf⟩).obj M).obj N

/-- The tensor product of two invertible modules is invertible. -/
private theorem isInvertible_tensorModules {C : Scheme.{0}} (M N : C.Modules)
    [hM : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M]
    [hN : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N] :
    SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 (tensorModules M N) := by
  haveI := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    C.presheaf C.ringCatSheaf.2 M).mpr hM
  haveI := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    C.presheaf C.ringCatSheaf.2 N).mpr hN
  exact (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    C.presheaf C.ringCatSheaf.2 _).mp
    (Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible C.presheaf C.ringCatSheaf.2 M N)

/-- Equal ideal sheaves have isomorphic closed subschemes, over the ambient scheme. -/
private noncomputable def subschemeIsoOfEq {Y : Scheme.{0}} {J J' : Y.IdealSheafData}
    (h : J = J') : J.subscheme ≅ J'.subscheme where
  hom := Scheme.IdealSheafData.inclusion h.ge
  inv := Scheme.IdealSheafData.inclusion h.le
  hom_inv_id := by
    rw [← cancel_mono J.subschemeι]
    simp [Scheme.IdealSheafData.inclusion_subschemeι]
  inv_hom_id := by
    rw [← cancel_mono J'.subschemeι]
    simp [Scheme.IdealSheafData.inclusion_subschemeι]

@[reassoc]
private theorem subschemeIsoOfEq_hom_subschemeι {Y : Scheme.{0}} {J J' : Y.IdealSheafData}
    (h : J = J') : (subschemeIsoOfEq h).hom ≫ J'.subschemeι = J.subschemeι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The intersection number with a curve is unchanged by an isomorphism of curves over `X`. -/
private theorem intersectionNumber_eq_of_iso_comp {k : Type} [Field k] {X C C' : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    (j : C ⟶ X) (j' : C' ⟶ X) [IsProper (j ≫ sX)] [IsProper (j' ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C')
    (he : e.hom ≫ j' = j) (D : QDivisor X) (hD : D.IsQCartier) :
    D.intersectionNumber k sX j hdim hD = D.intersectionNumber k sX j' hdim' hD := by
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX j j' hdim hdim' e he]

/-- **Weak subadjunction descends from a hyperplane section.** Let `H ⊆ E` be a closed subscheme
lying in a closed subscheme `X₁ ⊆ X`, with `H ∩ Eᵛ ⟶ H` the restriction `ν₁` of `ν`, and let `L` be
an invertible sheaf on `X`. Suppose the smooth locus of `Eᵛ` meets `H ∩ Eᵛ` inside the smooth
locus of `H ∩ Eᵛ`, the canonical sheaves satisfy the adjunction
`ω_{H ∩ Eᵛ} ≅ ω_{Eᵛ} ⊗ L` along curves in both smooth loci, the pairs satisfy
`(K₁ + B₁) · C = (K + B) · C + L · C` for curves in `X₁`, and `L` has the same degree on a good
curve `C = V(H ⊔ A)` and on its preimage `Cᵛ`. Then weak subadjunction along `V(A) ∩ H` in `H`
gives weak subadjunction along `C` in `E`. -/
private theorem subadjunctionAt_sup_of_subadjunctionAt_comap {k : Type} [Field k]
    {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [IsProper sX]
    {E Eν : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] (ν : Eν ⟶ E) [IsFinite ν] {d : ℕ}
    {K : Divisor X} {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    {X₁ : Scheme.{0}} [IsLocallyNoetherian X₁] [IsNormal X₁] (ι : X₁ ⟶ X) [IsClosedImmersion ι]
    {K₁ : Divisor X₁} {B₁ : QDivisor X₁} (hKB₁ : (Divisor.toQDivisor K₁ + B₁).IsQCartier)
    (H : E.IdealSheafData) (i₁ : H.subscheme ⟶ X₁) [IsClosedImmersion i₁]
    (hi₁ : i₁ ≫ ι = H.subschemeι ≫ i) (Hν : Eν.IdealSheafData) (hHν : Hν = H.comap ν)
    (ν₁ : Hν.subscheme ⟶ H.subscheme) [IsFinite ν₁]
    (hν₁ : ν₁ ≫ H.subschemeι = Hν.subschemeι ≫ ν)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hsm : ∀ x : Hν.subscheme, Hν.subschemeι x ∈ smoothLocus (ν ≫ i ≫ sX) →
      x ∈ smoothLocus (ν₁ ≫ i₁ ≫ ι ≫ sX))
    (hadjω : ∀ (C : Scheme.{0}) (j : C ⟶ Hν.subscheme)
      (hj₁ : Set.range j ⊆ Set.range (smoothLocus (ν₁ ≫ i₁ ≫ ι ≫ sX)).ι)
      (hj : Set.range (j ≫ Hν.subschemeι) ⊆ Set.range (smoothLocus (ν ≫ i ≫ sX)).ι),
      Nonempty ((Scheme.Modules.pullback (IsOpenImmersion.lift _ j hj₁)).obj
          (canonicalSheaf (ν₁ ≫ i₁ ≫ ι ≫ sX) d) ≅
        tensorModules ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hj)).obj
          (canonicalSheaf (ν ≫ i ≫ sX) (d + 1)))
          ((Scheme.Modules.pullback (j ≫ Hν.subschemeι ≫ ν ≫ i)).obj L)))
    (hadjK : ∀ (C : Scheme.{0}) (j : C ⟶ X₁) [IsProper ((j ≫ ι) ≫ sX)]
      (hdim : topologicalKrullDim C ≤ 1),
      haveI : IsProper (j ≫ ι ≫ sX) := by rw [← Category.assoc]; infer_instance
      (Divisor.toQDivisor K₁ + B₁).intersectionNumber k (ι ≫ sX) j hdim hKB₁ =
        (Divisor.toQDivisor K + B).intersectionNumber k sX (j ≫ ι) hdim hKB +
          degreeOn k sX (j ≫ ι) hdim L)
    (A : E.IdealSheafData)
    (hdeg : ∀ h : IsGoodCurve sX i ν (d + 1) (H ⊔ A),
      degreeOn k sX (((H ⊔ A).comap ν).subschemeι ≫ ν ≫ i) h.dim_le L =
        degreeOn k sX ((H ⊔ A).subschemeι ≫ i) h.dim_eq.le L)
    (hA : SubadjunctionAt (ι ≫ sX) i₁ ν₁ d (A.comap H.subschemeι) hKB₁) :
    SubadjunctionAt sX i ν (d + 1) (H ⊔ A) hKB := by
  subst hHν
  intro h
  -- the curve `C₁ = V(A) ∩ H` of `H`, its preimage `Cᵛ₁` in `H ∩ Eᵛ`, and their isomorphisms
  -- with `C = V(H ⊔ A)` and `Cᵛ`
  set A₁ := A.comap H.subschemeι with hA₁
  have hcomap : A₁.comap ν₁ = (A.comap ν).comap (H.comap ν).subschemeι := by
    rw [hA₁, ← Scheme.IdealSheafData.comap_comp, hν₁, Scheme.IdealSheafData.comap_comp]
  have hsup : H.comap ν ⊔ A.comap ν = (H ⊔ A).comap ν :=
    (Scheme.IdealSheafData.comap_sup _ _ _).symm
  let e : A₁.subscheme ≅ (H ⊔ A).subscheme := comapSubschemeιIso H A
  let eν : (A₁.comap ν₁).subscheme ≅ ((H ⊔ A).comap ν).subscheme :=
    subschemeIsoOfEq hcomap ≪≫ comapSubschemeιIso (H.comap ν) (A.comap ν) ≪≫
      subschemeIsoOfEq hsup
  have he : e.hom ≫ (H ⊔ A).subschemeι = A₁.subschemeι ≫ H.subschemeι :=
    comapSubschemeιIso_hom_subschemeι H A
  have heν : eν.hom ≫ ((H ⊔ A).comap ν).subschemeι =
      (A₁.comap ν₁).subschemeι ≫ (H.comap ν).subschemeι := by
    simp only [eν, Iso.trans_hom, Category.assoc, subschemeIsoOfEq_hom_subschemeι]
    rw [comapSubschemeιIso_hom_subschemeι, subschemeIsoOfEq_hom_subschemeι_assoc]
  have hmor : (A₁.subschemeι ≫ i₁) ≫ ι = e.hom ≫ (H ⊔ A).subschemeι ≫ i := by
    rw [Category.assoc, hi₁, reassoc_of% he]
  have hmorν : (A₁.comap ν₁).subschemeι ≫ ν₁ ≫ i₁ ≫ ι ≫ sX =
      eν.hom ≫ ((H ⊔ A).comap ν).subschemeι ≫ ν ≫ i ≫ sX := by
    rw [reassoc_of% heν, reassoc_of% hi₁, reassoc_of% hν₁]
  -- `C₁` is a good curve for the cut
  have hrange₁ : Set.range (A₁.comap ν₁).subschemeι ⊆ smoothLocus (ν₁ ≫ i₁ ≫ ι ≫ sX) := by
    rintro _ ⟨y, rfl⟩
    apply hsm
    have := h.range_subset ⟨eν.hom y, rfl⟩
    rwa [← Scheme.Hom.comp_apply, heν, Scheme.Hom.comp_apply] at this
  have hj₁ : Set.range (A₁.comap ν₁).subschemeι ⊆
      Set.range (smoothLocus (ν₁ ≫ i₁ ≫ ι ≫ sX)).ι :=
    hrange₁.trans_eq (Scheme.Opens.range_ι _).symm
  have hj : Set.range ((A₁.comap ν₁).subschemeι ≫ (H.comap ν).subschemeι) ⊆
      Set.range (smoothLocus (ν ≫ i ≫ sX)).ι := by
    rw [← heν, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (Set.range_comp_subset_range _ _).trans
      (h.range_subset.trans_eq (Scheme.Opens.range_ι _).symm)
  set ℓ := IsOpenImmersion.lift (smoothLocus (ν ≫ i ≫ sX)).ι ((H ⊔ A).comap ν).subschemeι
    (h.range_subset.trans_eq (Scheme.Opens.range_ι _).symm) with hℓ
  have hℓ₁ : IsOpenImmersion.lift (smoothLocus (ν ≫ i ≫ sX)).ι
      ((A₁.comap ν₁).subschemeι ≫ (H.comap ν).subschemeι) hj = eν.hom ≫ ℓ := by
    rw [← cancel_mono (smoothLocus (ν ≫ i ≫ sX)).ι, IsOpenImmersion.lift_fac, Category.assoc,
      hℓ, IsOpenImmersion.lift_fac, heν]
  haveI hω : SheafOfModules.IsInvertible ((H ⊔ A).comap ν).subscheme.presheaf
      ((H ⊔ A).comap ν).subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback ℓ).obj
      (canonicalSheaf (ν ≫ i ≫ sX) (d + 1))) := h.isInvertible
  obtain ⟨eω⟩ := hadjω _ (A₁.comap ν₁).subschemeι hj₁ hj
  haveI hω₁ : SheafOfModules.IsInvertible (A₁.comap ν₁).subscheme.presheaf
      (A₁.comap ν₁).subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback
      (IsOpenImmersion.lift _ _ hj)).obj (canonicalSheaf (ν ≫ i ≫ sX) (d + 1))) := by
    rw [hℓ₁]
    haveI h1 : SheafOfModules.IsInvertible (A₁.comap ν₁).subscheme.presheaf
        (A₁.comap ν₁).subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback eν.hom).obj
        ((Scheme.Modules.pullback ℓ).obj (canonicalSheaf (ν ≫ i ≫ sX) (d + 1)))) :=
      inferInstance
    exact @Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso _ _ _ h1
      ((Scheme.Modules.pullbackComp eν.hom ℓ).app _)
  haveI hT : SheafOfModules.IsInvertible (A₁.comap ν₁).subscheme.presheaf
      (A₁.comap ν₁).subscheme.ringCatSheaf.2 (tensorModules
      ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hj)).obj
        (canonicalSheaf (ν ≫ i ≫ sX) (d + 1)))
      ((Scheme.Modules.pullback
        ((A₁.comap ν₁).subschemeι ≫ (H.comap ν).subschemeι ≫ ν ≫ i)).obj L)) :=
    isInvertible_tensorModules _ _
  have h₁ : IsGoodCurve (ι ≫ sX) i₁ ν₁ d A₁ :=
    { dim_eq := (topologicalKrullDim_eq_of_isIso e.hom).trans h.dim_eq
      dim_le := (topologicalKrullDim_eq_of_isIso eν.hom).trans_le h.dim_le
      range_subset := hrange₁
      smooth := by
        haveI := h.smooth
        rw [hmorν]
        infer_instance
      isInvertible := Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso eω.symm
      isIntegral := haveI := h.isIntegral; IsIntegral.of_isIso e.inv
      isIntegral_comap := haveI := h.isIntegral_comap; IsIntegral.of_isIso eν.inv }
  have key := hA h₁
  -- the canonical degrees: `K_{Hᵛ} · Cᵛ₁ = K_{Eᵛ} · Cᵛ + L · Cᵛ`
  have hcan : h₁.canonicalDegree = h.canonicalDegree +
      degreeOn k sX (((H ⊔ A).comap ν).subschemeι ≫ ν ≫ i) h.dim_le L := by
    unfold IsSmoothCurveCut.canonicalDegree
    rw [@invertibleCurveDegree_eq_of_iso k _ _ _ _ h₁.dim_le _ _ h₁.isInvertible hT eω,
      invertibleCurveDegree_tensorSheaf_eq_add]
    push_cast
    congr 1
    · have e₁ : (Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hj)).obj
          (canonicalSheaf (ν ≫ i ≫ sX) (d + 1)) ≅ (Scheme.Modules.pullback eν.hom).obj
            ((Scheme.Modules.pullback ℓ).obj (canonicalSheaf (ν ≫ i ≫ sX) (d + 1))) :=
        eqToIso (by rw [hℓ₁]) ≪≫ ((Scheme.Modules.pullbackComp eν.hom ℓ).app _).symm
      rw [invertibleCurveDegree_eq_of_iso k _ h₁.dim_le e₁,
        MMP.Threefold.Resolution.invertibleCurveDegree_congr k hmorν]
      exact congrArg (fun z : ℤ => (z : ℚ)) (invertibleCurveDegree_pullback_of_isIso eν.hom
        (((H ⊔ A).comap ν).subschemeι ≫ ν ≫ i ≫ sX) h₁.dim_le h.dim_le
        ((Scheme.Modules.pullback ℓ).obj (canonicalSheaf (ν ≫ i ≫ sX) (d + 1))))
    · rw [MMP.Threefold.Resolution.invertibleCurveDegree_congr k
        (show (A₁.comap ν₁).subschemeι ≫ ν₁ ≫ i₁ ≫ ι ≫ sX =
          ((A₁.comap ν₁).subschemeι ≫ (H.comap ν).subschemeι ≫ ν ≫ i) ≫ sX by
            rw [reassoc_of% hi₁, reassoc_of% hν₁]; simp)]
      exact congrArg (fun z : ℤ => (z : ℚ)) (MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k
        sX _ _ h₁.dim_le h.dim_le eν (by rw [reassoc_of% heν]) L)
  -- the intersection numbers: `(K₁ + B₁) · C₁ = (K + B) · C + L · C`
  have hint : h₁.intersectionNumber hKB₁ = h.intersectionNumber hKB +
      degreeOn k sX ((H ⊔ A).subschemeι ≫ i) h.dim_eq.le L := by
    unfold IsSmoothCurveCut.intersectionNumber
    rw [hadjK _ (A₁.subschemeι ≫ i₁) h₁.dim_eq.le,
      intersectionNumber_eq_of_iso_comp sX _ ((H ⊔ A).subschemeι ≫ i) _ h.dim_eq.le e hmor.symm,
      MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX _ ((H ⊔ A).subschemeι ≫ i) _
        h.dim_eq.le e hmor.symm L]
  rw [hcan, hint, hdeg h] at key
  linarith

/-- **Weak subadjunction for the whole component, when it is a curve.** If `E` is a curve in a
fibre of dimension at most one and `ν : Eᵛ ⟶ E` is a normal finite birational model, the weak
subadjunction inequality holds along `C = E` itself: `Eᵛ` is the normalization of `E`, and the
inequality is the weak subadjunction for curves in a fibre of dimension at most one. -/
private theorem subadjunctionAt_bot {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f) (s : S)
    (hs : IsClosed ({s} : Set S))
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E]
    (hEs : Set.range i ⊆ f ⁻¹' {s}) (hfib : topologicalKrullDim (f ⁻¹' {s}) ≤ (1 : ℕ))
    {Eν : Scheme.{0}} (ν : Eν ⟶ E) [IsFinite ν] [IsIntegral Eν] [IsNormal Eν]
    (hν : IsBirational ν) :
    SubadjunctionAt sX i ν 1 ⊥ hklt.1.2.2 := by
  intro h
  set IC : E.IdealSheafData := ⊥
  set ICν := IC.comap ν with hICν
  haveI : IsIso IC.subschemeι := inferInstanceAs (IsIso (⊥ : E.IdealSheafData).subschemeι)
  haveI : IsIso ICν.subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 (Scheme.IdealSheafData.comap_bot _)
  have hEr : topologicalKrullDim E = 1 :=
    (topologicalKrullDim_eq_of_isIso IC.subschemeι).symm.trans h.dim_eq
  haveI : AlgebraicGeometry.IsVariety k (i ≫ sX) := {}
  haveI : AlgebraicGeometry.IsCurve k (i ≫ sX) := { topologicalKrullDim_eq_one := hEr }
  set g := ν ≫ i ≫ sX with hg
  -- `Eᵛ` is the normalization of `E`
  obtain ⟨eN, heN⟩ := Scheme.exists_iso_normalizationScheme_of_isIntegralHom_of_isBirational
    (finite_irreducibleComponents_of_locallyOfFiniteType k (i ≫ sX)) ν
    (fun U hU => finite_irreducibleComponents_of_locallyOfFiniteType k g _
      (QuasiCompact.isCompact_preimage (f := ν) _ U.2 hU))
    (fun U _ => hν.restrict U)
  have hgN : g = eN.hom ≫ normalizationOverField k (i ≫ sX) ≫ i ≫ sX := by
    rw [hg, ← Category.assoc, ← Category.assoc, ← heN]; rfl
  haveI hsmN : Smooth (normalizationOverField k (i ≫ sX) ≫ i ≫ sX) :=
    (normalizationModel' k (i ≫ sX)).smooth_structureMap
  haveI hcN : AlgebraicGeometry.IsCurve k (normalizationOverField k (i ≫ sX) ≫ i ≫ sX) :=
    (normalizationModel' k (i ≫ sX)).isCurve
  haveI : Smooth g := by rw [hgN]; infer_instance
  have hdimEν : topologicalKrullDim Eν = 1 :=
    (topologicalKrullDim_eq_of_isIso eN.hom).trans hcN.topologicalKrullDim_eq_one
  haveI hgc : AlgebraicGeometry.IsCurve k g := { topologicalKrullDim_eq_one := hdimEν }
  have hsmtop : smoothLocus g = ⊤ := by
    refine top_le_iff.1 (le_smoothLocus g ?_)
    haveI : IsIso (⊤ : Eν.Opens).ι := isIso_ι_of_eq_top rfl
    infer_instance
  have hj : Set.range ICν.subschemeι ⊆ Set.range (smoothLocus g).ι :=
    h.range_subset.trans_eq (Scheme.Opens.range_ι _).symm
  haveI : IsIso (smoothLocus g).ι := isIso_ι_of_eq_top hsmtop
  haveI : IsIso (IsOpenImmersion.lift (smoothLocus g).ι ICν.subschemeι hj) :=
    IsIso.of_isIso_fac_right (IsOpenImmersion.lift_fac _ _ _)
  obtain ⟨e⟩ := nonempty_pullback_canonicalSheaf_one_iso g ICν.subschemeι hj
  haveI : IsIntegral ICν.subscheme := IsIntegral.of_isIso (inv ICν.subschemeι)
  haveI : AlgebraicGeometry.IsVariety k (ICν.subschemeι ≫ g) := {}
  haveI : AlgebraicGeometry.IsCurve k (ICν.subschemeι ≫ g) :=
    { topologicalKrullDim_eq_one :=
        (topologicalKrullDim_eq_of_isIso ICν.subschemeι).trans hgc.topologicalKrullDim_eq_one }
  haveI hΩ : SheafOfModules.IsInvertible _ _
      (Scheme.Hom.relativeDifferentials (ICν.subschemeι ≫ g)) :=
    isInvertible_relativeDifferentials_of_isCurve (k := k) _
  unfold IsSmoothCurveCut.canonicalDegree
  rw [@invertibleCurveDegree_eq_of_iso k _ _ _ _ h.dim_le _ _ h.isInvertible hΩ e]
  haveI : IsNormal ICν.subscheme := isNormal_of_isOpenImmersion ICν.subschemeι
  haveI : IsIntegral IC.subscheme := IsIntegral.of_isIso (inv IC.subschemeι)
  haveI : AlgebraicGeometry.IsVariety k ((IC.subschemeι ≫ i) ≫ sX) := {}
  haveI : AlgebraicGeometry.IsCurve k ((IC.subschemeι ≫ i) ≫ sX) :=
    { topologicalKrullDim_eq_one := h.dim_eq }
  set α := ICν.subschemeι ≫ ν ≫ inv IC.subschemeι with hαdef
  have hα : α ≫ (IC.subschemeι ≫ i) ≫ sX = ICν.subschemeι ≫ g := by
    simp [α, g]
  haveI : IsFinite α := by rw [hαdef]; infer_instance
  have hαb : IsBirational α :=
    (isBirational_of_iso (asIso ICν.subschemeι)).comp
      (hν.comp (isBirational_of_iso (asIso (inv IC.subschemeι))))
  haveI : AlgebraicGeometry.IsCurve k (α ≫ (IC.subschemeι ≫ i) ≫ sX) := by
    rw [hα]; infer_instance
  haveI : Smooth (α ≫ (IC.subschemeι ≫ i) ≫ sX) := by rw [hα]; infer_instance
  have hN : topologicalKrullDim
      (normalizationSchemeOverField k ((IC.subschemeι ≫ i) ≫ sX)) ≤ 1 :=
    ((topologicalKrullDim_normalizationSchemeOverField k _).trans h.dim_eq).le
  have key := invertibleCurveDegree_relativeDifferentials_eq_normalization
    ((IC.subschemeι ≫ i) ≫ sX) α hαb h.dim_le hN
  have hcurve :=
    MMP.Fourfold.invertibleCurveDegree_relativeDifferentials_normalization_le_intersectionNumber
      sX hklt hB sS f hfs hf s hs (by exact_mod_cast hfib) (IC.subschemeι ≫ i)
      (by rw [Scheme.Hom.comp_base, TopCat.coe_comp]
          exact (Set.range_comp_subset_range _ _).trans hEs)
  rw [invertibleCurveDegree_relativeDifferentials_congr hα.symm, key]
  exact hcurve

/-- **The case `r = 1`.** When the component `E` is a curve, the complete intersection is `E`
itself, its preimage is the normalization `Eᵛ`, which is a smooth curve, and the inequality is
the weak subadjunction for curves in a fibre of dimension at most one. -/
private theorem case_one {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f) (s : S)
    (hs : IsClosed ({s} : Set S))
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E]
    (hEs : Set.range i ⊆ f ⁻¹' {s}) (hEr : topologicalKrullDim E = 1)
    (hfib : topologicalKrullDim (f ⁻¹' {s}) = 1) :
    haveI := isFinite_normalizationOverField k (i ≫ sX)
    let IC : E.IdealSheafData := ⊥
    let ICν := IC.comap (normalizationOverField k (i ≫ sX))
    ∃ (hC : topologicalKrullDim IC.subscheme = 1)
      (hCν : topologicalKrullDim ICν.subscheme ≤ 1)
      (hsm : Set.range ICν.subschemeι ⊆
        smoothLocus (normalizationOverField k (i ≫ sX) ≫ i ≫ sX)),
      Smooth (ICν.subschemeι ≫ normalizationOverField k (i ≫ sX) ≫ i ≫ sX) ∧
      let ω := (Scheme.Modules.pullback (IsOpenImmersion.lift
          (smoothLocus (normalizationOverField k (i ≫ sX) ≫ i ≫ sX)).ι ICν.subschemeι
            (hsm.trans_eq (Scheme.Opens.range_ι _).symm))).obj
          (canonicalSheaf (normalizationOverField k (i ≫ sX) ≫ i ≫ sX) 1)
      ∃ hω : SheafOfModules.IsInvertible _ _ ω,
        (@invertibleCurveDegree k _ _
            (ICν.subschemeι ≫ normalizationOverField k (i ≫ sX) ≫ i ≫ sX) _ hCν ω hω : ℚ) ≤
          (Divisor.toQDivisor K + B).intersectionNumber k sX (IC.subschemeι ≫ i) hC.le
            hklt.1.2.2 := by
  haveI := isFinite_normalizationOverField k (i ≫ sX)
  intro IC ICν
  set ν := normalizationOverField k (i ≫ sX) with hν
  haveI : AlgebraicGeometry.IsVariety k (i ≫ sX) := {}
  haveI : AlgebraicGeometry.IsCurve k (i ≫ sX) := { topologicalKrullDim_eq_one := hEr }
  set g := ν ≫ i ≫ sX with hg
  haveI : Smooth g := (normalizationModel' k (i ≫ sX)).smooth_structureMap
  haveI hgc : AlgebraicGeometry.IsCurve k g := (normalizationModel' k (i ≫ sX)).isCurve
  haveI : IsProper g := isProper_normalizationOverField_comp k (i ≫ sX)
  haveI : IsIso IC.subschemeι := inferInstanceAs (IsIso (⊥ : E.IdealSheafData).subschemeι)
  haveI : IsIso ICν.subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 (Scheme.IdealSheafData.comap_bot _)
  have hsmtop : smoothLocus g = ⊤ := by
    refine top_le_iff.1 (le_smoothLocus g ?_)
    haveI : IsIso (⊤ : (normalizationSchemeOverField k (i ≫ sX)).Opens).ι :=
      isIso_ι_of_eq_top rfl
    infer_instance
  have hdimC : topologicalKrullDim IC.subscheme = 1 :=
    (topologicalKrullDim_eq_of_isIso IC.subschemeι).trans hEr
  have hdimCν : topologicalKrullDim ICν.subscheme ≤ 1 :=
    ((topologicalKrullDim_eq_of_isIso ICν.subschemeι).trans
      (hgc.topologicalKrullDim_eq_one)).le
  have hsm : Set.range ICν.subschemeι ⊆ smoothLocus g := by
    rw [hsmtop]; exact Set.subset_univ _
  refine ⟨hdimC, hdimCν, hsm, inferInstance, ?_⟩
  intro ω
  have hj : Set.range ICν.subschemeι ⊆ Set.range (smoothLocus g).ι :=
    hsm.trans_eq (Scheme.Opens.range_ι _).symm
  haveI : IsIso (smoothLocus g).ι := isIso_ι_of_eq_top hsmtop
  haveI : IsIso (IsOpenImmersion.lift (smoothLocus g).ι ICν.subschemeι hj) :=
    IsIso.of_isIso_fac_right (IsOpenImmersion.lift_fac _ _ _)
  obtain ⟨e⟩ := nonempty_pullback_canonicalSheaf_one_iso g ICν.subschemeι hj
  haveI : IsIntegral ICν.subscheme := IsIntegral.of_isIso (inv ICν.subschemeι)
  haveI : AlgebraicGeometry.IsVariety k (ICν.subschemeι ≫ g) := {}
  haveI : AlgebraicGeometry.IsCurve k (ICν.subschemeι ≫ g) :=
    { topologicalKrullDim_eq_one :=
        (topologicalKrullDim_eq_of_isIso ICν.subschemeι).trans hgc.topologicalKrullDim_eq_one }
  haveI hΩ : SheafOfModules.IsInvertible _ _
      (Scheme.Hom.relativeDifferentials (ICν.subschemeι ≫ g)) :=
    isInvertible_relativeDifferentials_of_isCurve (k := k) _
  have hω : SheafOfModules.IsInvertible _ _ ω :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso e.symm
  refine ⟨hω, ?_⟩
  haveI : IsNormal (normalizationSchemeOverField k (i ≫ sX)) :=
    Scheme.isNormal_normalizationScheme E _
  exact subadjunctionAt_bot sX hklt hB sS f hfs hf s hs i hEs (by exact_mod_cast hfib.le) ν
    (Scheme.isBirational_normalization E _) ⟨⟨hdimC, hdimCν, hsm, inferInstance, hω⟩,
      IsIntegral.of_isIso (inv IC.subschemeι), inferInstance⟩

/-! ### The inequality at one general complete intersection, by cutting one hyperplane at a time -/

/-- The supremum over `Fin (m + 1)` splits off the first index. -/
private theorem iSup_fin_succ' {α : Type*} [CompleteLattice α] {m : ℕ} (g : Fin (m + 1) → α) :
    ⨆ j, g j = g 0 ⊔ ⨆ j : Fin m, g j.succ :=
  le_antisymm
    (iSup_le fun j => Fin.cases le_sup_left
      (fun j => le_sup_of_le_right (le_iSup (fun j : Fin m => g j.succ) j)) j)
    (sup_le (le_iSup _ 0) (iSup_le fun j => le_iSup _ _))

/-- Evaluating a polynomial in two sets of variables, viewed through `MvPolynomial.sumAlgEquiv`
as a polynomial in the first set with coefficients polynomials in the second, is evaluation at
the combined point. -/
private theorem eval_map_eval_sumAlgEquiv {R : Type*} [CommRing R] {S₁ S₂ : Type*}
    (P : MvPolynomial (S₁ ⊕ S₂) R) (c' : S₁ → R) (c₀ : S₂ → R) :
    MvPolynomial.eval c' (MvPolynomial.map (MvPolynomial.eval c₀)
      (MvPolynomial.sumAlgEquiv R S₁ S₂ P)) = MvPolynomial.eval (Sum.elim c' c₀) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.sumAlgEquiv_C_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    rw [map_mul, map_mul, map_mul, hp, map_mul]
    cases n <;> simp [MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr]

/-- **Separating the first hyperplane of a tuple.** A nonzero polynomial `Q` in the coefficients
of `m + 1` hyperplanes stays nonzero, as a polynomial in the last `m` of them, after the first is
specialized at any `c₀` off the zero locus of a nonzero polynomial `R`. -/
private theorem exists_specialize_ne_zero {k : Type} [Field k] {m N : ℕ}
    (Q : MvPolynomial (Fin (m + 1) × Fin (N + 1)) k) (hQ : Q ≠ 0) :
    ∃ R : MvPolynomial (Fin (N + 1)) k, R ≠ 0 ∧ ∀ c₀ : Fin (N + 1) → k,
      MvPolynomial.eval c₀ R ≠ 0 → ∃ Q₀ : MvPolynomial (Fin m × Fin (N + 1)) k, Q₀ ≠ 0 ∧
        ∀ c' : Fin m → Fin (N + 1) → k, MvPolynomial.eval (fun p => c' p.1 p.2) Q₀ =
          MvPolynomial.eval (fun p => (Fin.cons c₀ c' : Fin (m + 1) → Fin (N + 1) → k) p.1 p.2) Q := by
  classical
  let g : Fin (m + 1) × Fin (N + 1) → (Fin m × Fin (N + 1)) ⊕ Fin (N + 1) :=
    fun p => Fin.cases (Sum.inr p.2) (fun j => Sum.inl (j, p.2)) p.1
  have hginj : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    cases a using Fin.cases <;> cases a' using Fin.cases <;> simp_all [g]
  set Q' := MvPolynomial.sumAlgEquiv k _ _ (MvPolynomial.rename g Q)
  have hQ' : Q' ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (AlgEquiv.injective _)]
    exact fun h => hQ (MvPolynomial.rename_injective g hginj (by rw [h, map_zero]))
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.1 hQ'
  refine ⟨Q'.coeff d, hd, fun c₀ hc₀ => ⟨MvPolynomial.map (MvPolynomial.eval c₀) Q', ?_,
    fun c' => ?_⟩⟩
  · exact MvPolynomial.ne_zero_iff.2 ⟨d, by rwa [MvPolynomial.coeff_map]⟩
  · rw [eval_map_eval_sumAlgEquiv, MvPolynomial.eval_rename]
    congr 2
    funext ⟨a, b⟩
    cases a using Fin.cases <;> rfl

/-- A dense open of the dual projective space contains the hyperplane of some nonzero `c₀` off
the zero locus of any given nonzero polynomial. -/
private theorem exists_dualPoint_mem_of_dense {k : Type} [Field k] [IsAlgClosed k] {N : ℕ}
    (U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens) (hU : Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))))
    (R : MvPolynomial (Fin (N + 1)) k) (hR : R ≠ 0) :
    ∃ (c₀ : Fin (N + 1) → k) (hc₀ : c₀ ≠ 0), dualPoint c₀ hc₀ ∈ U ∧ MvPolynomial.eval c₀ R ≠ 0 := by
  classical
  -- `U` contains a basic open `D₊(f)`; a homogeneous component `Q` of `f` not vanishing at a
  -- point of `D₊(f)` has `D₊(Q) ⊆ U` on the points `[c]`
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).exists_subset_of_mem_open hp U.isOpen
  have hpf' : f ∉ (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      from p).asHomogeneousIdeal :=
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp hpf
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d f ∉
      (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        from p).asHomogeneousIdeal := by
    by_contra h
    push Not at h
    apply hpf'
    rw [← MvPolynomial.sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => h i
  set Q := MvPolynomial.homogeneousComponent d f
  have hQ0 : Q ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  have hmem : ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), MvPolynomial.eval c Q ≠ 0 →
      dualPoint c hc ∈ U := by
    intro c hc hcQ
    refine hfU ((ProjectiveSpectrum.mem_basicOpen _ f
      (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) from
        dualPoint c hc)).mpr fun hf => hcQ ?_)
    change f ∈ ((RingHom.ker (MvPolynomial.eval c)).homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal at hf
    have hcore := (HomogeneousIdeal.isHomogeneous ((RingHom.ker
      (MvPolynomial.eval c)).homogeneousCore
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))).mem_iff.mp hf d
    have hdec : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f d :
        MvPolynomial (Fin (N + 1)) k)) = Q :=
      MvPolynomial.decomposition.decompose'_apply f d
    rw [hdec] at hcore
    exact RingHom.mem_ker.mp (Ideal.toIdeal_homogeneousCore_le _ _ hcore)
  -- a point where `Q`, `R` and the coordinate `T₀` do not vanish
  have hP : Q * R * MvPolynomial.X 0 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hQ0 hR) (MvPolynomial.X_ne_zero _)
  obtain ⟨c, hc⟩ : ∃ c : Fin (N + 1) → k, MvPolynomial.eval c (Q * R * MvPolynomial.X 0) ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun c => by rw [h c, map_zero])
  simp only [map_mul, MvPolynomial.eval_X, ne_eq, mul_eq_zero, not_or] at hc
  have hc0 : c ≠ 0 := fun h => hc.2 (by rw [h, Pi.zero_apply])
  exact ⟨c, hc0, hmem c hc0 hc.1.1, hc.1.2⟩

/-- The hyperplane section along a composite is the pull-back of the hyperplane section. -/
private theorem hyperplaneSection_comp {k : Type} [Field k] {N : ℕ} {Y Z : Scheme.{0}}
    (g : Y ⟶ Z) (ψ : Z ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) (c : Fin (N + 1) → k) :
    hyperplaneSection (g ≫ ψ) c = (hyperplaneSection ψ c).comap g :=
  Scheme.IdealSheafData.comap_comp _ _ _

/-- The restriction `Eᵛ ∩ ψ⁻¹(H) ⟶ E ∩ ψ⁻¹(H)` of `ν : Eᵛ ⟶ E` to the hyperplane sections. -/
private noncomputable def cutMap {k : Type} [Field k] {N : ℕ} {E Eν : Scheme.{0}} (ν : Eν ⟶ E)
    (ψ : E ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) (c₀ : Fin (N + 1) → k) :
    (hyperplaneSection (ν ≫ ψ) c₀).subscheme ⟶ (hyperplaneSection ψ c₀).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ (hyperplaneSection ψ c₀) ν (by
    rw [hyperplaneSection, hyperplaneSection, Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.le_map_comap _ ν)

@[reassoc]
private theorem cutMap_subschemeι {k : Type} [Field k] {N : ℕ} {E Eν : Scheme.{0}} (ν : Eν ⟶ E)
    (ψ : E ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) (c₀ : Fin (N + 1) → k) :
    cutMap ν ψ c₀ ≫ (hyperplaneSection ψ c₀).subschemeι =
      (hyperplaneSection (ν ≫ ψ) c₀).subschemeι ≫ ν :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

private theorem isFinite_cutMap {k : Type} [Field k] {N : ℕ} {E Eν : Scheme.{0}} (ν : Eν ⟶ E)
    [IsFinite ν] (ψ : E ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) (c₀ : Fin (N + 1) → k) :
    IsFinite (cutMap ν ψ c₀) := by
  haveI : IsFinite (cutMap ν ψ c₀ ≫ (hyperplaneSection ψ c₀).subschemeι) := by
    rw [cutMap_subschemeι]; infer_instance
  exact IsFinite.of_comp _ (hyperplaneSection ψ c₀).subschemeι

/-- A closed immersion followed by a projective morphism is projective. -/
private theorem isProjectiveMorphism_comp_isClosedImmersion {X₁ X S : Scheme.{0}} (ι : X₁ ⟶ X)
    [IsClosedImmersion ι] (f : X ⟶ S) (hf : IsProjectiveMorphism f) :
    IsProjectiveMorphism (ι ≫ f) := by
  obtain ⟨n, j, hj, rfl⟩ := hf
  exact ⟨n, ι ≫ j, inferInstance, Category.assoc _ _ _⟩

/-- **Restrictions of a finite model over an isomorphism locus.** If `ν : Eᵛ ⟶ E` is an
isomorphism over an open `V`, then for any closed subscheme `C = V(A)` of `E` the restriction
`V(ν^* A) ⟶ C` of `ν` is an isomorphism over `C ∩ V`: the square of closed immersions is
cartesian, and so is its restriction over `V`. -/
private theorem isIso_subschemeMap_morphismRestrict {E Eν : Scheme.{0}} (ν : Eν ⟶ E)
    (V : E.Opens) [IsIso (ν ∣_ V)] (A : E.IdealSheafData) (J : Eν.IdealSheafData)
    (hJ : J = A.comap ν) (π : J.subscheme ⟶ A.subscheme)
    (hπ : π ≫ A.subschemeι = J.subschemeι ≫ ν) : IsIso (π ∣_ (A.subschemeι ⁻¹ᵁ V)) := by
  subst hJ
  set W := A.subschemeι ⁻¹ᵁ V with hW
  have sq0 : IsPullback (A.comap ν).subschemeι π ν A.subschemeι :=
    isPullback_of_isClosedImmersion _ _ π ν hπ.symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])
  have big := (isPullback_morphismRestrict π W).paste_vert sq0.flip
  have hrange : Set.range ((π ⁻¹ᵁ W).ι ≫ (A.comap ν).subschemeι) ⊆ Set.range (ν ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (ν ((A.comap ν).subschemeι ((π ⁻¹ᵁ W).ι z))) ∈ V
    rw [← Scheme.Hom.comp_apply, ← hπ, Scheme.Hom.comp_apply]
    exact z.2
  set t := IsOpenImmersion.lift (ν ⁻¹ᵁ V).ι _ hrange with ht
  have hsq : IsPullback (π ∣_ W) t (A.subschemeι ∣_ V) (ν ∣_ V) := by
    refine IsPullback.of_bot (h₂₁ := ν ∣_ V) ?_ ?_ (isPullback_morphismRestrict ν V)
    · rw [ht, IsOpenImmersion.lift_fac, morphismRestrict_ι]
      exact big
    · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
        morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, ht,
        IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, ← hπ]
  exact hsq.isIso_fst_of_isIso

/-- **The degree on a good curve and on its preimage.** If `ν` is an isomorphism over an open
`V ⊆ E` meeting the good curve `C = V(A)` in all but finitely many points, then an invertible
sheaf `L` on `X` has the same degree on `C` and on its preimage `Cᵛ`: `Cᵛ ⟶ C` is a finite
birational morphism of integral curves. -/
private theorem degreeOn_comap_eq_of_finite {k : Type} [Field k] {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [IsProper sX]
    {E Eν : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] (ν : Eν ⟶ E) [IsFinite ν]
    (V : E.Opens) [IsIso (ν ∣_ V)] {d : ℕ} {A : E.IdealSheafData} (h : IsGoodCurve sX i ν d A)
    (hfin : (A.subschemeι ⁻¹' (V : Set E)ᶜ).Finite) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    degreeOn k sX ((A.comap ν).subschemeι ≫ ν ≫ i) h.dim_le L =
      degreeOn k sX (A.subschemeι ≫ i) h.dim_eq.le L := by
  haveI := h.isIntegral
  haveI := h.isIntegral_comap
  -- the restriction `π : Cᵛ ⟶ C` of `ν`
  let π := Scheme.IdealSheafData.subschemeMap (A.comap ν) A ν
    (Scheme.IdealSheafData.le_map_comap _ _)
  have hπ : π ≫ A.subschemeι = (A.comap ν).subschemeι ≫ ν :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  haveI : IsFinite (π ≫ A.subschemeι) := by rw [hπ]; infer_instance
  haveI : IsFinite π := IsFinite.of_comp _ A.subschemeι
  -- `π` is an isomorphism over `W = C ∩ V`
  set W := A.subschemeι ⁻¹ᵁ V with hW
  haveI : IsIso (π ∣_ W) := isIso_subschemeMap_morphismRestrict ν V A _ rfl π hπ
  -- the curve `C` is infinite
  haveI : JacobsonSpace A.subscheme := LocallyOfFiniteType.jacobsonSpace (A.subschemeι ≫ i ≫ sX)
  have hCinf : ¬ Finite A.subscheme := by
    intro hfin'
    haveI := JacobsonSpace.discreteTopology (X := A.subscheme) (Set.toFinite _)
    have h0 := topologicalKrullDim_zero_of_discreteTopology A.subscheme
    rw [h.dim_eq] at h0
    exact absurd h0 (by decide)
  -- `π` is surjective: it is finite and dominant
  haveI : IsDominant π := by
    obtain ⟨y, hy⟩ : ((W : Set A.subscheme)).Nonempty := by
      by_contra hne
      exact hCinf (Set.finite_univ_iff.mp (hfin.subset fun x _ hx => hne ⟨x, hx⟩))
    exact (MMP.Flips.isBirationalMorphism_of_isIso_resLE π (π ⁻¹ᵁ W) W
      ⟨_, ((inv (π ∣_ W)) ⟨y, hy⟩).2⟩ ⟨y, hy⟩ le_rfl (by
        rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance)).isDominant
  have hsurj : Function.Surjective π := by
    have hr : Set.range π = Set.univ :=
      π.isClosedMap.isClosed_range.closure_eq.symm.trans π.denseRange.closure_range
    exact fun z => (Set.mem_range).1 (hr ▸ Set.mem_univ z)
  have hbir : IsBirationalMorphism π := by
    obtain ⟨y, hy⟩ : ((W : Set A.subscheme)).Nonempty := by
      by_contra hne
      exact hCinf (Set.finite_univ_iff.mp (hfin.subset fun x _ hx => hne ⟨x, hx⟩))
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE π (π ⁻¹ᵁ W) W
      ⟨_, ((inv (π ∣_ W)) ⟨y, hy⟩).2⟩ ⟨y, hy⟩ le_rfl ?_
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  -- the degree formula for the finite birational morphism `π`
  haveI : AlgebraicGeometry.IsVariety k (A.subschemeι ≫ i ≫ sX) := {}
  haveI hcC : AlgebraicGeometry.IsCurve k (A.subschemeι ≫ i ≫ sX) :=
    { topologicalKrullDim_eq_one := h.dim_eq }
  haveI : AlgebraicGeometry.IsVariety k ((A.comap ν).subschemeι ≫ ν ≫ i ≫ sX) := {}
  have hnc : ¬ ∃ y : A.subscheme, ∀ x : (A.comap ν).subscheme, π x = y := by
    rintro ⟨y, hy⟩
    haveI : Subsingleton A.subscheme := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hsurj a
      obtain ⟨x', rfl⟩ := hsurj b
      rw [hy x, hy x']⟩
    exact hCinf inferInstance
  have hdimν : topologicalKrullDim (A.comap ν).subscheme = 1 := by
    haveI : IsLocallyNoetherian (A.comap ν).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian ((A.comap ν).subschemeι ≫ ν ≫ i ≫ sX)
    haveI : CompactSpace (A.comap ν).subscheme :=
      QuasiCompact.compactSpace_of_compactSpace ((A.comap ν).subschemeι ≫ ν ≫ i ≫ sX)
    haveI : IsNoetherian (A.comap ν).subscheme := {}
    have hpos : ¬ topologicalKrullDim (A.comap ν).subscheme ≤ 0 := by
      intro h0
      haveI := finite_of_topologicalKrullDim_nonpos h0
      exact hCinf (Finite.of_surjective _ hsurj)
    have hle := h.dim_le
    revert hpos hle
    generalize topologicalKrullDim (A.comap ν).subscheme = x
    intro hpos hle
    induction x using WithBot.recBotCoe with
    | bot => exact absurd bot_le hpos
    | coe x =>
      induction x using ENat.recTopCoe with
      | top => exact absurd hle (by decide)
      | coe x =>
        have h1 : x ≤ 1 := by exact_mod_cast hle
        have h2 : ¬ x ≤ 0 := fun h' => hpos (by exact_mod_cast h')
        have : x = 1 := by omega
        subst this
        rfl
  haveI : AlgebraicGeometry.IsCurve k ((A.comap ν).subschemeι ≫ ν ≫ i ≫ sX) :=
    { topologicalKrullDim_eq_one := hdimν }
  have hstr : π ≫ A.subschemeι ≫ i ≫ sX = (A.comap ν).subschemeι ≫ ν ≫ i ≫ sX := by
    rw [reassoc_of% hπ]
  have key := curveDegree_pullback_eq_degreeOver_mul k ((A.comap ν).subschemeι ≫ ν ≫ i ≫ sX)
    (A.subschemeι ≫ i ≫ sX) π hstr hnc ((Scheme.Modules.pullback (A.subschemeι ≫ i)).obj L) 1
  rw [MMP.Fourfold.Oai4C1.Negativity.degreeOver_eq_one π hbir, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback ((A.comap ν).subschemeι ≫ ν ≫ i)).obj L ≅
      (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback (A.subschemeι ≫ i)).obj L) :=
    eqToIso (by rw [← Category.assoc, ← hπ, Category.assoc]) ≪≫
      ((Scheme.Modules.pullbackComp π (A.subschemeι ≫ i)).app L).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc _ _ _) h.dim_le,
    invertibleCurveDegree_eq_of_iso k _ h.dim_le e,
    invertibleCurveDegree_congr_structure (Category.assoc _ _ _) h.dim_eq.le,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

/-- In `WithBot ℕ∞`, `d + 1 ≤ m + 1` gives `d ≤ m`. -/
private theorem withBot_le_natCast_of_add_one_le {d : WithBot ℕ∞} {m : ℕ}
    (h : d + 1 ≤ ((m + 1 : ℕ) : WithBot ℕ∞)) : d ≤ (m : ℕ) := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add] at h
      exact (WithBot.coe_lt_coe.2 (ENat.coe_lt_top (m + 1))).not_ge h
    | coe d =>
      have h' : d + 1 ≤ m + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : d ≤ m)

/-- In `WithBot ℕ∞`, `d + 1 = m + 1` gives `d = m`. -/
private theorem withBot_eq_natCast_of_add_one_eq {d : WithBot ℕ∞} {m : ℕ}
    (h : d + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : d = (m : ℕ) := by
  induction d using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add] at h
    exact absurd h WithBot.bot_ne_coe
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add] at h
      exact ENat.top_ne_coe (m + 1) (WithBot.coe_eq_coe.mp h)
    | coe d =>
      have h' : d + 1 = m + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : d = m)

/-- The image of a closed immersion has the dimension of its source. -/
private theorem topologicalKrullDim_range_eq {Y Z : Scheme.{0}} (g : Y ⟶ Z) [IsClosedImmersion g] :
    topologicalKrullDim (Set.range g) = topologicalKrullDim Y := by
  rw [← Set.image_univ, topologicalKrullDim_image_of_isEmbedding g.isClosedEmbedding.isEmbedding,
    (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq]

/-- `ℙᴺ_k = Proj k[T₀, …, T_N]` over `Spec k` through Stacks' structure morphism
`projToSpecCoeff k N`. -/
@[reducible] private noncomputable def projectiveSpaceOver (k : Type) [Field k] (N : ℕ) :
    (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Over
      (Spec (.of k)) :=
  ⟨Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k N⟩

attribute [local instance high] projectiveSpaceOver

/-- The structure morphism of `ℙᴺ_k` is the one of its projective model. -/
private theorem over_projectiveSpace_eq {k : Type} [Field k] {N : ℕ} :
    (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) ↘ Spec (.of k)) = Stacks.ProjectiveCohomology.projModelToSpec k N :=
  Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec k N

/-! ### Dimension counts for general hyperplanes -/

/-- **A general hyperplane cuts closed subsets properly.** Let `g : Y ⟶ ℙᴺ_k` be a closed
immersion and `T l` finitely many closed subsets of `Y`. For a general hyperplane `H`, each
`T l ∩ g⁻¹(H)` is empty if `dim T l < 1`, and is nonempty of dimension `dim T l - 1`
otherwise. -/
private theorem exists_dense_open_topologicalKrullDim_inter_hyperplaneSection {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}} {N : ℕ}
    (g : Y ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion g] {ι : Type*} [Finite ι]
    (T : ι → Set Y) (hT : ∀ l, IsClosed (T l)) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U → ∀ l,
        (topologicalKrullDim (T l) < 1 → T l ∩ (hyperplaneSection g c).support = ∅) ∧
        (1 ≤ topologicalKrullDim (T l) →
          (T l ∩ (hyperplaneSection g c).support).Nonempty ∧
          topologicalKrullDim ↥(T l ∩ (hyperplaneSection g c).support) + 1 =
            topologicalKrullDim (T l)) := by
  classical
  letI : Y.Over (Spec (.of k)) := ⟨g ≫ Stacks.ProjectiveCohomology.projModelToSpec k N⟩
  haveI := LocallyOfFiniteType.isLocallyNoetherian (Stacks.ProjectiveCohomology.projModelToSpec k N)
  haveI : CompactSpace (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) :=
    QuasiCompact.compactSpace_of_compactSpace (Stacks.ProjectiveCohomology.projModelToSpec k N)
  haveI : IsNoetherian (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) := {}
  have hcons : ∀ l, Topology.IsConstructible (g '' T l) := fun l =>
    Topology.isConstructible_compl.mp ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible
      ((g.isClosedEmbedding.isClosedMap _ (hT l)).isOpen_compl))
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_inter_hyperplanes (fun l => g '' T l) hcons 1
  obtain ⟨U, hU, hgood⟩ := exists_dense_open_of_polynomial hP0
  refine ⟨U, hU, fun c hc hmem l => ?_⟩
  obtain ⟨t, ht, hPt⟩ := hgood c hc hmem
  have hH := hP (fun _ => t • c) hPt l
  rw [Set.iInter_const, support_hyperplane_linearForm_smul c ht, Nat.cast_one] at hH
  have himg : g '' (T l ∩ (hyperplaneSection g c).support) =
      g '' T l ∩ (Stacks.ProjectiveSpace.hyperplane (linearForm c)).support := by
    rw [coe_support_hyperplaneSection, Set.image_inter_preimage]
  have hdT := topologicalKrullDim_image_of_isEmbedding g.isClosedEmbedding.isEmbedding (T l)
  have hdTH := topologicalKrullDim_image_of_isEmbedding g.isClosedEmbedding.isEmbedding
    (T l ∩ (hyperplaneSection g c).support)
  rw [himg] at hdTH
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have h := hH.1 (hdT ▸ hlt)
    rw [← himg, Set.image_eq_empty] at h
    exact h
  · obtain ⟨hne, hd⟩ := hH.2 (hdT ▸ hge)
    rw [← himg, Set.image_nonempty] at hne
    rw [hdTH, hdT] at hd
    exact ⟨hne, hd⟩

/-- The support of a complete intersection of hyperplane sections is the preimage of the
intersection of the hyperplanes. -/
private theorem coe_support_iSup_hyperplaneSection {k : Type} [Field k] {Y : Scheme.{0}} {N c : ℕ}
    (g : Y ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) (f : Fin c → Fin (N + 1) → k) :
    (((⨆ j, hyperplaneSection g (f j)).support : TopologicalSpace.Closeds Y) : Set Y) =
      g ⁻¹' ⋂ j, ((Stacks.ProjectiveSpace.hyperplane (linearForm (f j))).support :
        Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) := by
  letI : Y.Over (Spec (.of k)) := ⟨g ≫ Stacks.ProjectiveCohomology.projModelToSpec k N⟩
  rw [Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf, Set.preimage_iInter]
  exact Set.iInter_congr fun j => coe_support_hyperplaneSection (φ := g) _

/-- **General complete intersections cut closed subsets properly.** Let `g : Y ⟶ ℙᴺ_k` be a
closed immersion and `T l` finitely many closed subsets of `Y`. Off the zero locus of a nonzero
polynomial in the coefficients of `c` hyperplanes, each `T l ∩ g⁻¹(H₁ ∩ ⋯ ∩ H_c)` is empty if
`dim T l < c`, and is nonempty of dimension `dim T l - c` otherwise. -/
private theorem exists_polynomial_topologicalKrullDim_inter_iSup_hyperplaneSection {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}} {N : ℕ}
    (g : Y ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion g] {ι : Type*} [Finite ι]
    (T : ι → Set Y) (hT : ∀ l, IsClosed (T l)) (c : ℕ) :
    ∃ P : MvPolynomial (Fin c × Fin (N + 1)) k, P ≠ 0 ∧
      ∀ f : Fin c → Fin (N + 1) → k, MvPolynomial.eval (fun p => f p.1 p.2) P ≠ 0 → ∀ l,
        (topologicalKrullDim (T l) < c →
          T l ∩ (⨆ j, hyperplaneSection g (f j)).support = ∅) ∧
        ((c : WithBot ℕ∞) ≤ topologicalKrullDim (T l) →
          (T l ∩ (⨆ j, hyperplaneSection g (f j)).support).Nonempty ∧
          topologicalKrullDim ↥(T l ∩ (⨆ j, hyperplaneSection g (f j)).support) + c =
            topologicalKrullDim (T l)) := by
  classical
  haveI := LocallyOfFiniteType.isLocallyNoetherian (Stacks.ProjectiveCohomology.projModelToSpec k N)
  haveI : CompactSpace (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) :=
    QuasiCompact.compactSpace_of_compactSpace (Stacks.ProjectiveCohomology.projModelToSpec k N)
  haveI : IsNoetherian (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) := {}
  have hcons : ∀ l, Topology.IsConstructible (g '' T l) := fun l =>
    Topology.isConstructible_compl.mp ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible
      ((g.isClosedEmbedding.isClosedMap _ (hT l)).isOpen_compl))
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_inter_hyperplanes (fun l => g '' T l) hcons c
  refine ⟨P, hP0, fun f hf l => ?_⟩
  have hH := hP f hf l
  have himg : g '' (T l ∩ (⨆ j, hyperplaneSection g (f j)).support) =
      g '' T l ∩ ⋂ j, ((Stacks.ProjectiveSpace.hyperplane (linearForm (f j))).support :
        Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) := by
    rw [coe_support_iSup_hyperplaneSection, Set.image_inter_preimage]
  have hdT := topologicalKrullDim_image_of_isEmbedding g.isClosedEmbedding.isEmbedding (T l)
  have hdTH := topologicalKrullDim_image_of_isEmbedding g.isClosedEmbedding.isEmbedding
    (T l ∩ (⨆ j, hyperplaneSection g (f j)).support)
  rw [himg] at hdTH
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have h := hH.1 (hdT ▸ hlt)
    rw [← himg, Set.image_eq_empty] at h
    exact h
  · obtain ⟨hne, hd⟩ := hH.2 (hdT ▸ hge)
    rw [← himg, Set.image_nonempty] at hne
    rw [hdTH, hdT] at hd
    exact ⟨hne, hd⟩

/-! ### Divisors on a scheme and on its open subscheme `⊤` -/

/-- Every prime divisor of `S` is the closure of a prime divisor of the open subscheme `U = ⊤`. -/
private theorem primeDivisorMap_surjective_of_eq_top {S : Scheme.{0}} {U : S.Opens}
    (hU : U = ⊤) : Function.Surjective (OpenWeilRestriction.primeDivisorMap U.ι) := fun E =>
  (OpenWeilRestriction.mem_range_primeDivisorMap_iff U.ι E).2
    (by rw [Scheme.Opens.range_ι, hU]; trivial)

/-- Restriction of divisors to the open subscheme `U = ⊤` is injective. -/
private theorem restrictOpen_injective_of_eq_top {R : Type*} [Zero R] {S : Scheme.{0}}
    {U : S.Opens} (hU : U = ⊤) :
    Function.Injective (DivisorWithCoeffs.restrictOpen (R := R) U) := by
  intro D D' h
  refine DivisorWithCoeffs.ext' fun E => ?_
  obtain ⟨W, rfl⟩ := primeDivisorMap_surjective_of_eq_top hU E
  have := congrArg (fun F : DivisorWithCoeffs R U.toScheme => F.coeff W) h
  simpa only [DivisorWithCoeffs.coeff_restrictOpen] using this

/-- Every divisor of the open subscheme `U = ⊤` is the restriction of a divisor of `S`. -/
private theorem exists_restrictOpen_eq_of_eq_top {R : Type*} [AddCommMonoid R] {S : Scheme.{0}}
    {U : S.Opens} (hU : U = ⊤) (D' : DivisorWithCoeffs R U.toScheme) :
    ∃ D : DivisorWithCoeffs R S, D.restrictOpen U = D' := by
  classical
  refine ⟨Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap U.ι) D',
    DivisorWithCoeffs.ext' fun W => ?_⟩
  rw [DivisorWithCoeffs.coeff_restrictOpen, DivisorWithCoeffs.coeff_apply,
    DivisorWithCoeffs.coeff_apply,
    Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective U.ι)]

/-- Restriction to an open subscheme commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem restrictOpen_toQDivisor {S : Scheme.{0}} (U : S.Opens) (D : Divisor S) :
    (Divisor.toQDivisor D).restrictOpen U = Divisor.toQDivisor (D.restrictOpen U) :=
  DivisorWithCoeffs.ext' fun W => by
    simp only [DivisorWithCoeffs.coeff_restrictOpen, Divisor.coeff_toQDivisor]

/-- **Restriction by components along an open subscheme.** Restricting `B` by components along
`U.ι ≫ f` is restricting it along `f` and then to `U`. -/
private theorem restrictComponents_comp_eq_restrictOpen {R : Type*} [AddCommMonoid R]
    {S X : Scheme.{0}} (f : S ⟶ X) (U : S.Opens) (B : DivisorWithCoeffs R X)
    (h₁ : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff f B)).Finite)
    (h₂ : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff (U.ι ≫ f) B)).Finite) :
    B.restrictComponents (U.ι ≫ f) = (B.restrictComponents f).restrictOpen U := by
  classical
  refine DivisorWithCoeffs.ext' fun W => ?_
  have hg : MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι W) =
      U.ι W.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W
  rw [DivisorWithCoeffs.coeff_restrictOpen, DivisorWithCoeffs.coeff_restrictComponents _ h₂,
    DivisorWithCoeffs.coeff_restrictComponents _ h₁, hg, Scheme.Hom.comp_apply]

/-! ### Hyperplane sections as zero divisors of a Cartier divisor -/

section HyperplaneDivisor

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)

attribute [local instance] globalSectionsModule

/-- **Hyperplane sections are the zero divisors of a linear system of a Cartier divisor.** For
a morphism `φ : X ⟶ ℙᴺ_k` of a normal integral quasi-compact `k`-scheme there are a Cartier
divisor `M` with `𝒪_X(M) ≅ φ^*𝒪(1)` and sections `tⱼ` of `𝒪_X(M)`, the coordinates, without
common zero, such that the zero divisor of `∑ cⱼ tⱼ` is supported on the hyperplane section
`φ⁻¹(V(c))`. -/
private theorem exists_isCartier_sections_supp_zeroDivisor {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX) :
    ∃ (M : Divisor X) (_ : M.IsCartier) (t : Fin (N + 1) → M.divisorialSubmodule ⊤),
      (∀ x : X, ∃ (j : Fin (N + 1)) (hj : t j ≠ 0), x ∉ (M.zeroDivisor (t j) hj).supp) ∧
      ∀ (c : Fin (N + 1) → k) (hσ : ∑ j, scalarsToGlobalSections k sX (c j) • t j ≠ 0),
        ((M.zeroDivisor (∑ j, scalarsToGlobalSections k sX (c j) • t j) hσ).supp : Set X) =
          ((hyperplaneSection φ c).support : Set X) := by
  classical
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have hφ' : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = X ↘ Spec (.of k) := hφ
  -- `φ^*𝒪(1)` is `𝒪_X(M)` for the Cartier divisor `M` of a local frame
  obtain ⟨M, hM, ⟨e⟩⟩ : ∃ M : Divisor X, M.IsCartier ∧ Nonempty (M.divisorialSheaf ≅ pullTwist φ) := by
    have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := X.toRingedSpace)
      (pullTwist φ)
    have : ∀ z : X.toRingedSpace.carrier,
        IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace z) :=
      fun z => X.isLocalRing z
    choose W hW a ha using fun y : X =>
      Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := X.toRingedSpace)
        (pullTwist φ) y
    obtain ⟨y₀⟩ : Nonempty X := inferInstance
    let F : LocalFrame (pullTwist φ) :=
      { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
    exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
      ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩
  haveI := hM.isInvertibleModule_divisorialSheaf
  let t : Fin (N + 1) → M.divisorialSubmodule ⊤ := fun j => e.inv.app ⊤ (pulledSystem φ j)
  have ht : ∀ c : Fin (N + 1) → k, ∑ j, scalarsToGlobalSections k sX (c j) • t j =
      e.inv.app ⊤ (systemSection (pulledSystem φ) c) := by
    intro c
    rw [systemSection_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Scheme.Modules.Hom.app_smul e.inv _ _).symm
  -- the zero divisor of `e⁻¹ s` is supported on the zero scheme of `s`
  have hsupp : ∀ (s : Γ(pullTwist φ, ⊤)) (hs : (e.inv.app ⊤ s : M.divisorialSubmodule ⊤) ≠ 0),
      ((M.zeroDivisor (e.inv.app ⊤ s) hs).supp : Set X) =
        (Stacks.Divisors.zeroScheme X (pullTwist φ) s).supportSet := by
    intro s hs
    have h1 := Divisor.nonvanishingLocus_eq_compl_supp_zeroDivisor hM (e.inv.app ⊤ s) hs
    have h2 := Stacks.CokernelSupport.nonvanishingLocus_iso_app e.symm s
    ext x
    rw [← not_iff_not, ← Set.mem_compl_iff, ← h1]
    change x ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf (e.symm.hom.app ⊤ s) ↔ _
    rw [h2, mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme]
  have hzsec : ∀ (σ σ' : M.divisorialSubmodule ⊤) (_ : σ = σ') (h₁ : σ ≠ 0) (h₂ : σ' ≠ 0),
      (M.zeroDivisor σ h₁).supp = (M.zeroDivisor σ' h₂).supp := by
    rintro _ _ rfl _ _; rfl
  refine ⟨M, hM, t, fun x => ?_, fun c hσ => ?_⟩
  · obtain ⟨j, hj⟩ := exists_X_notMem (φ x)
    have hsys : systemSection (pulledSystem φ) (Pi.single j (1 : k)) = pulledSystem φ j := by
      rw [systemSection_apply]
      simp [Pi.single_apply]
    have hx : x ∈ Stacks.Ample.nonvanishingLocus (pullTwist φ) (pulledSystem φ j) := by
      have := (mem_nonvanishingOpen_pulledSystem_iff hφ' (Pi.single j (1 : k)) x).2
        (by rw [linearForm_single]; exact hj)
      rwa [hsys] at this
    have hxz := (mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme _ _ x).1 hx
    have htj : t j ≠ 0 := by
      intro h0
      have h1 : pulledSystem φ j = 0 := by
        have h2 : e.hom.app ⊤ (t j) = pulledSystem φ j := by
          change (e.inv ≫ e.hom).app ⊤ _ = _
          rw [Iso.inv_hom_id]; rfl
        have h3 : e.hom.app ⊤ (t j) = 0 := by rw [h0]; exact map_zero _
        rw [← h2, h3]
      rw [h1, AlgebraicGeometry.zeroScheme_zero] at hxz
      exact hxz (by simp; trivial)
    refine ⟨j, htj, ?_⟩
    have h4 := hsupp (pulledSystem φ j) htj
    change x ∉ ((M.zeroDivisor (t j) htj).supp : Set X)
    rw [show ((M.zeroDivisor (t j) htj).supp : Set X) = _ from h4]
    exact hxz
  · have hσ' : (e.inv.app ⊤ (systemSection (pulledSystem φ) c) : M.divisorialSubmodule ⊤) ≠ 0 :=
      ht c ▸ hσ
    rw [hzsec _ _ (ht c) hσ hσ', hsupp _ hσ']
    exact congrArg (fun I : X.IdealSheafData => (I.support : Set X))
      (zeroScheme_pulledSystem hφ' c)

end HyperplaneDivisor

/-! ### General position of a hyperplane section with respect to a boundary -/

/-- **Two distinct prime divisors meet in codimension two.** On an integral `k`-scheme of finite
type of dimension `d + 2`, the points of `E ∩ E'` for distinct prime divisors `E ≠ E'` have
coheight at least two, so `E ∩ E'` has dimension at most `d`. -/
private theorem topologicalKrullDim_inter_support_le {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = (d + 2 : ℕ)) {E E' : MMP.Mori.PrimeDivisor X} (hEE : E ≠ E') :
    topologicalKrullDim ↥((E.support : Set X) ∩ E'.support) ≤ (d : ℕ) := by
  have hcl : ∀ F : MMP.Mori.PrimeDivisor X, IsClosed (F.support : Set X) := fun F => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  refine topologicalKrullDim_le_of_forall_closure ((hcl E).inter (hcl E')) fun x hx => ?_
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  rw [hd] at h
  have hc : (2 : ℕ∞) ≤ Order.coheight x := by
    by_contra hlt
    have hle1 : Order.coheight x ≤ 1 := Order.le_of_lt_add_one (lt_of_not_ge hlt)
    have hge : 1 ≤ Order.coheight x := by
      have hx₁ := hx.1
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx₁
      calc (1 : ℕ∞) = Order.coheight E.genericPoint := E.coheight_genericPoint.symm
        _ ≤ Order.coheight x := Order.coheight_anti (specializes_iff_mem_closure.mpr hx₁)
    have h1 : Order.coheight x = 1 := le_antisymm hle1 hge
    exact hEE (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((E.eq_genericPoint_of_mem_support hx.1 h1).symm.trans
        (E'.eq_genericPoint_of_mem_support hx.2 h1)))
  have h2 : topologicalKrullDim (closure {x} : Set X) + 1 + 1 ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [add_assoc, ← h]
    refine add_le_add (le_refl _) ?_
    rw [one_add_one_eq_two]
    have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight x : ℕ∞) : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr hc
    simpa using this
  exact withBot_le_natCast_of_add_one_le (withBot_le_natCast_of_add_one_le h2)

/-- **A general hyperplane section is in general position with respect to a divisor.** Let `X`
be a variety of dimension `d + 3` with a closed immersion `φ : X ⟶ ℙᴺ_k` and `B` a divisor. For a
general hyperplane `H`, if `X ∩ H` is a variety of dimension `d + 2`, no prime divisor of
`X ∩ H` lies in two distinct components of `B`. -/
private theorem exists_dense_open_restrictComponents_unique {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = (d + 3 : ℕ)) {N : ℕ}
    (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ] {R : Type*} [Zero R]
    (B : DivisorWithCoeffs R X) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        ∀ [IsIntegral (hyperplaneSection φ c).subscheme],
        topologicalKrullDim (hyperplaneSection φ c).subscheme = (d + 2 : ℕ) →
        ∀ (C : MMP.Mori.PrimeDivisor (hyperplaneSection φ c).subscheme), ∀ E ∈ B.support, ∀ E' ∈ B.support,
          (hyperplaneSection φ c).subschemeι C.genericPoint ∈ E.support →
          (hyperplaneSection φ c).subschemeι C.genericPoint ∈ E'.support → E = E' := by
  classical
  have hcl : ∀ F : MMP.Mori.PrimeDivisor X, IsClosed (F.support : Set X) := fun F => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  obtain ⟨U, hU, hgood⟩ := exists_dense_open_topologicalKrullDim_inter_hyperplaneSection φ
    (fun p : {p : B.support × B.support // p.1 ≠ p.2} =>
      ((p.1.1.1.support : Set X) ∩ p.1.2.1.support))
    (fun p => (hcl _).inter (hcl _))
  refine ⟨U, hU, fun c hc hcU _ hdimS C E hE E' hE' h₁ h₂ => ?_⟩
  by_contra hne
  have hyS : (hyperplaneSection φ c).subschemeι C.genericPoint ∈
      ((hyperplaneSection φ c).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩
  have hT := topologicalKrullDim_inter_support_le sX (d := d + 1) (by rw [hd]) hne
  obtain ⟨hlt, hge⟩ := hgood c hc hcU ⟨(⟨E, hE⟩, ⟨E', hE'⟩), fun h => hne
    (congrArg Subtype.val h)⟩
  -- the closure of the generic point of `C` lies in `E ∩ E' ∩ H`
  have hsub : closure ({(hyperplaneSection φ c).subschemeι C.genericPoint} : Set X) ⊆
      ((E.support : Set X) ∩ E'.support) ∩ (hyperplaneSection φ c).support :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨⟨h₁, h₂⟩, hyS⟩)
      (((hcl E).inter (hcl E')).inter (hyperplaneSection φ c).support.isClosed)
  -- and has dimension `d + 1`
  have hdy : topologicalKrullDim (closure
      ({(hyperplaneSection φ c).subschemeι C.genericPoint} : Set X)) = (d + 1 : ℕ) := by
    have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
      ((hyperplaneSection φ c).subschemeι ≫ sX) C.genericPoint
    rw [C.coheight_genericPoint, hdimS] at h1
    rw [← Set.image_singleton,
      (hyperplaneSection φ c).subschemeι.isClosedEmbedding.closure_image_eq,
      topologicalKrullDim_image_of_isEmbedding
        (hyperplaneSection φ c).subschemeι.isClosedEmbedding.isEmbedding]
    exact withBot_eq_natCast_of_add_one_eq (by exact_mod_cast h1)
  by_cases h1 : 1 ≤ topologicalKrullDim ↥((E.support : Set X) ∩ E'.support)
  · obtain ⟨-, hdim⟩ := hge h1
    have hle := topologicalKrullDim_le_of_subset hsub
    rw [hdy] at hle
    have : ((d + 1 : ℕ) : WithBot ℕ∞) + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
      ((add_le_add_left hle 1).trans_eq hdim).trans hT
    exact absurd this (by
      rw [← WithBot.coe_natCast, ← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
      exact_mod_cast (by omega : ¬ d + 1 + 1 ≤ d + 1))
  · have hempty := hlt (lt_of_not_ge h1)
    have : (hyperplaneSection φ c).subschemeι C.genericPoint ∈
        ((E.support : Set X) ∩ E'.support) ∩ (hyperplaneSection φ c).support :=
      ⟨⟨h₁, h₂⟩, hyS⟩
    rw [hempty] at this
    exact this

/-! ### Cartier divisors, restriction and the open subscheme `⊤` -/

/-- **Cartier divisors and the open subscheme `⊤`.** A divisor of a normal integral Noetherian
scheme `S` is Cartier as soon as its restriction to the open subscheme `U = ⊤` is: it is the
pull-back of that restriction along the isomorphism `S ≅ U`. -/
private theorem isCartier_of_isCartier_restrictOpen_of_eq_top {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] {U : S.Opens} (hU : U = ⊤)
    {D : Divisor S} (h : Divisor.IsCartier (D.restrictOpen U)) : D.IsCartier := by
  subst hU
  haveI : IsIso (⊤ : S.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  haveI : IsNormal (⊤ : S.Opens).toScheme := isNormal_of_isOpenImmersion (⊤ : S.Opens).ι
  let g : S ⟶ (⊤ : S.Opens).toScheme := inv (⊤ : S.Opens).ι
  haveI : IsIntegral (⊤ : S.Opens).toScheme := IsIntegral.of_isIso g
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g (D.restrictOpen ⊤)
  obtain ⟨D₁, hD₁⟩ := Divisor.IsCartier.exists_isPullback (f := g) h hB
  have hc : D₁.IsCartier := Divisor.IsPullback.isCartier hD₁ h
  have hgι : ∀ x, g ((⊤ : S.Opens).ι x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have : D₁ = D := by
    refine DivisorWithCoeffs.ext' fun E => ?_
    obtain ⟨P, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff (⊤ : S.Opens).ι E).2
      (by rw [Scheme.Opens.range_ι]; trivial)
    have heq : g (OpenWeilRestriction.primeDivisorMap (⊤ : S.Opens).ι P).genericPoint =
        P.genericPoint := by
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap, hgι]
    rw [MMP.Positivity.coeff_eq_of_isPullback _ P heq h hD₁, DivisorWithCoeffs.coeff_restrictOpen]
  exact this ▸ hc

/-- Restriction to an open subscheme commutes with integer multiples. -/
private theorem restrictOpen_zsmul {S : Scheme.{0}} (U : S.Opens) (m : ℤ) (D : QDivisor S) :
    (m • D).restrictOpen U = m • D.restrictOpen U :=
  Finsupp.comapDomain_smul _ _ _ _

/-- Restriction to an open subscheme is additive. -/
private theorem restrictOpen_add {S : Scheme.{0}} (U : S.Opens) (D D' : QDivisor S) :
    (D + D').restrictOpen U = D.restrictOpen U + D'.restrictOpen U :=
  Finsupp.comapDomain_add _ _ _ _ _

/-- **Restriction by components along `⊤ ⟶ S`.** Restricting `B` by components along
`U.ι ≫ f`, for the open subscheme `U = ⊤`, is restricting it along `f` and then to `U`. -/
private theorem restrictComponents_comp_eq_restrictOpen_of_eq_top {R : Type*} [AddCommMonoid R]
    {S X : Scheme.{0}} (f : S ⟶ X) {U : S.Opens} (hU : U = ⊤) (B : DivisorWithCoeffs R X) :
    B.restrictComponents (U.ι ≫ f) = (B.restrictComponents f).restrictOpen U := by
  classical
  have hc : ∀ P, DivisorWithCoeffs.restrictComponentsCoeff (U.ι ≫ f) B P =
      DivisorWithCoeffs.restrictComponentsCoeff f B
        (OpenWeilRestriction.primeDivisorMap U.ι P) := fun P => by
    have hg : MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι P) =
        U.ι P.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P
    unfold DivisorWithCoeffs.restrictComponentsCoeff
    rw [hg, Scheme.Hom.comp_apply]
  by_cases h₁ : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff f B)).Finite
  · have h₂ : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff (U.ι ≫ f) B)).Finite :=
      (h₁.preimage (OpenWeilRestriction.primeDivisorMap_injective U.ι).injOn).subset
        fun P hP => by
          rw [Function.mem_support, hc] at hP
          exact hP
    exact restrictComponents_comp_eq_restrictOpen f U B h₁ h₂
  · have h₂ : ¬ (Function.support
        (DivisorWithCoeffs.restrictComponentsCoeff (U.ι ≫ f) B)).Finite := by
      intro h₂
      refine h₁ ((h₂.image (OpenWeilRestriction.primeDivisorMap U.ι)).subset fun E hE => ?_)
      obtain ⟨P, rfl⟩ := primeDivisorMap_surjective_of_eq_top hU E
      refine ⟨P, ?_, rfl⟩
      rw [Function.mem_support, hc]
      exact hE
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [DivisorWithCoeffs.coeff_restrictOpen, DivisorWithCoeffs.restrictComponents,
      DivisorWithCoeffs.restrictComponents, dif_neg h₂, dif_neg h₁]
    rfl

/-- **The restriction of a boundary in general position.** If every coefficient of an effective
`B` is `< 1` and no prime divisor of `S` lies in two components of `B`, then `B|_S` is effective
with every coefficient `< 1`. -/
private theorem zero_le_and_coeff_lt_one_restrictComponents {S X : Scheme.{0}} (f : S ⟶ X)
    {B : QDivisor X} (hB : 0 ≤ B) (hB1 : ∀ P, B.coeff P < 1)
    (huniq : ∀ (C : MMP.Mori.PrimeDivisor S), ∀ E ∈ B.support, ∀ E' ∈ B.support,
      f C.genericPoint ∈ E.support → f C.genericPoint ∈ E'.support → E = E') :
    0 ≤ B.restrictComponents f ∧ ∀ C, (B.restrictComponents f).coeff C < 1 := by
  classical
  have hB0 : ∀ E, 0 ≤ B E := fun E => Finsupp.le_def.1 hB E
  by_cases hfin : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff f B)).Finite
  swap
  · have h0 : B.restrictComponents f = 0 := by
      rw [DivisorWithCoeffs.restrictComponents, dif_neg hfin]
    rw [h0]
    exact ⟨le_rfl, fun C => by rw [DivisorWithCoeffs.coeff_apply]; simp⟩
  have hc := DivisorWithCoeffs.coeff_restrictComponents f hfin
  refine ⟨Finsupp.le_def.2 fun C => ?_, fun C => ?_⟩
  · rw [Finsupp.zero_apply, ← DivisorWithCoeffs.coeff_apply, hc, Finsupp.sum]
    refine Finset.sum_nonneg fun E _ => ?_
    split_ifs
    · exact hB0 E
    · exact le_rfl
  · rw [hc, Finsupp.sum]
    by_cases h : ∃ E ∈ B.support, f C.genericPoint ∈ E.support
    · obtain ⟨E₀, hE₀, hC₀⟩ := h
      rw [Finset.sum_eq_single E₀ (fun E hE hne => by
        rw [if_neg (fun hC => hne (huniq C E hE E₀ hE₀ hC hC₀))]) (fun h => absurd hE₀ h),
        if_pos hC₀]
      exact hB1 E₀
    · push Not at h
      rw [Finset.sum_eq_zero fun E hE => if_neg (h E hE)]
      exact zero_lt_one

/-- The degree along a curve depends only on the morphism, not on how it is written. -/
private theorem degreeOn_congr_hom {k : Type} [Field k] {X C : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) {i i' : C ⟶ X} (h : i = i') [IsProper (i ≫ sX)]
    [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    degreeOn k sX i hdim L = degreeOn k sX i' hdim L := by
  subst h; rfl

open MonoidalCategory in
open MMP.Intersection.Scheme.Modules (tensorPow) in
/-- **Degrees of tensor powers.** The positive tensor powers `L^{⊗ (n+1)}` of an invertible sheaf
are invertible, and `deg_C L^{⊗ (n+1)} = (n + 1) deg_C L`. -/
private theorem exists_isInvertible_degreeOn_tensorPow_succ {k : Type} [Field k]
    {X C : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (n : ℕ) :
    ∃ _ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (tensorPow L (n + 1)),
      degreeOn k sX i hdim (tensorPow L (n + 1)) =
        ((n + 1 : ℕ) : ℤ) * degreeOn k sX i hdim L := by
  induction n with
  | zero =>
    let e : tensorPow L (0 + 1) ≅ L := λ_ L
    haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (tensorPow L (0 + 1)) :=
      Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso e.symm
    exact ⟨this, by rw [degreeOn_eq_of_iso k sX i hdim e]; simp⟩
  | succ n ih =>
    obtain ⟨hinv, hdeg⟩ := ih
    haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (tensorPow L (n + 1 + 1)) :=
      isInvertible_tensorModules (tensorPow L (n + 1)) L
    refine ⟨this, ?_⟩
    have h : degreeOn k sX i hdim (tensorPow L (n + 1 + 1)) =
        degreeOn k sX i hdim (tensorPow L (n + 1)) + degreeOn k sX i hdim L :=
      degreeOn_tensorSheaf k sX i hdim (tensorPow L (n + 1)) L (hLM := this)
    rw [h, hdeg]
    push_cast
    ring

/-! ### The four genericity statements for one hyperplane -/

open MonoidalCategory in
/-- **klt and adjunction on a general hyperplane section of `X`.** For a general hyperplane
`H = V(c)`, the section `X_H` is a normal projective variety carrying a klt pair
`(X_H, B|_{X_H})` of dimension `n - 1` with effective boundary, and
`(K_{X_H} + B|_{X_H}) · C = (K_X + B) · C + H · C` for every curve `C ⊆ X_H`. -/
private theorem exists_dense_open_isKltPair_hyperplaneSection {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    (hn : 3 ≤ n) {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
      ∃ (_ : IsIntegral (hyperplaneSection φ c).subscheme)
        (_ : IsLocallyNoetherian (hyperplaneSection φ c).subscheme)
        (_ : IsNormal (hyperplaneSection φ c).subscheme)
        (_ : AlgebraicGeometry.IsProjectiveVariety k ((hyperplaneSection φ c).subschemeι ≫ sX))
        (K₁ : Divisor (hyperplaneSection φ c).subscheme)
        (B₁ : QDivisor (hyperplaneSection φ c).subscheme)
        (hklt₁ : MMP.Mori.IsKltPair ((hyperplaneSection φ c).subschemeι ≫ sX) (n - 1) K₁ B₁),
        0 ≤ B₁ ∧
        ∀ (C : Scheme.{0}) (j : C ⟶ (hyperplaneSection φ c).subscheme)
          [IsProper ((j ≫ (hyperplaneSection φ c).subschemeι) ≫ sX)]
          (hdim : topologicalKrullDim C ≤ 1),
          haveI : IsProper (j ≫ (hyperplaneSection φ c).subschemeι ≫ sX) := by
            rw [← Category.assoc]; infer_instance
          (Divisor.toQDivisor K₁ + B₁).intersectionNumber k
              ((hyperplaneSection φ c).subschemeι ≫ sX) j hdim hklt₁.1.2.2 =
            (Divisor.toQDivisor K + B).intersectionNumber k sX
              (j ≫ (hyperplaneSection φ c).subschemeι) hdim hklt.1.2.2 +
              degreeOn k sX (j ≫ (hyperplaneSection φ c).subschemeι) hdim
                ((Scheme.Modules.pullback φ).obj (twistOne k N)) := by
  classical
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have hX : IsNormalVariety k sX := hklt.1.1
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (X ↘ Spec (.of k)) :=
    (inferInstance : AlgebraicGeometry.IsVariety k sX)
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : PerfectField k := PerfectField.ofCharZero
  have hK : K.IsCanonicalDivisor sX n := hklt.1.2.1
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 3 := ⟨n - 3, by omega⟩
  rw [show d + 3 - 1 = d + 2 by omega]
  have hdimX : topologicalKrullDim X = ((d + 3 : ℕ) : WithBot ℕ∞) := hK.1
  have hdim2 : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    rw [hdimX]; exact_mod_cast (by omega : 2 ≤ d + 3)
  haveI : φ.IsOver (Spec (.of k)) := ⟨by rw [over_projectiveSpace_eq]; exact hφ⟩
  have hrange : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure (Set.range φ.base)) := by
    rw [φ.isClosedEmbedding.isClosed_range.closure_eq]
    erw [topologicalKrullDim_range_eq φ]
    exact hdim2
  -- Bertini: a general `S = X ∩ H` is a normal variety of dimension `n - 1`
  obtain ⟨U₁, hU₁, h₁⟩ := exists_dense_open_hyperplaneSection_restrictComponents
    (Z := X) φ (by rw [Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec]; exact hφ)
    (J := Empty) (fun e => e.elim) (fun e => e.elim)
  -- general position with respect to the components of `B`
  obtain ⟨U₂, hU₂, h₂⟩ := exists_dense_open_restrictComponents_unique sX (d := d) hdimX φ B
  -- the discrepancy does not drop on a general member (Kollár–Mori 5.17(1))
  obtain ⟨M, -, s, hs, hsupp⟩ := exists_isCartier_sections_supp_zeroDivisor sX φ hφ
  obtain ⟨Q, hQ, hQc⟩ :=
    IsPair.exists_polynomial_discrep_le_discrep_restrict_connectedComponent hdim2 hklt.isPair s hs
  obtain ⟨U₃, hU₃, h₃⟩ := exists_dense_open_of_polynomial
    (P := MvPolynomial.rename (fun i : Fin (N + 1) => ((0 : Fin 1), i)) Q)
    (fun h => hQ (MvPolynomial.rename_injective _ (fun i j hij => (Prod.ext_iff.1 hij).2)
      (h.trans (map_zero _).symm)))
  -- adjunction on a general member
  obtain ⟨U₄, hU₄, h₄⟩ := IsPair.exists_dense_open_adjunction_connectedComponent_zeroScheme
    (hklt.isPair : IsPair (X ↘ Spec (.of k)) B) hdim2 (pulledSystem φ)
    (iSup_nonvanishingOpen_pulledSystem hφ)
  refine ⟨U₁ ⊓ U₂ ⊓ U₃ ⊓ U₄, ?_, fun c hc hcU => ?_⟩
  · simp only [TopologicalSpace.Opens.coe_inf]
    exact ((hU₁.inter_of_isOpen_left hU₂ U₁.isOpen).inter_of_isOpen_left hU₃
      (U₁.isOpen.inter U₂.isOpen)).inter_of_isOpen_left hU₄
      ((U₁.isOpen.inter U₂.isOpen).inter U₃.isOpen)
  rw [TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_inf,
    TopologicalSpace.Opens.mem_inf] at hcU
  obtain ⟨⟨⟨hc₁, hc₂⟩, hc₃⟩, hc₄⟩ := hcU
  -- the section `S = X ∩ H`
  obtain ⟨hgen, -, hSln, hSn, -⟩ := h₁ c hc hc₁
  obtain ⟨hSvar, -, hdimS⟩ := hgen hrange
  haveI := hSln
  haveI := hSn
  haveI : AlgebraicGeometry.IsVariety k ((hyperplaneSection φ c).subschemeι ≫ sX) := hSvar
  haveI : IsIntegral (hyperplaneSection φ c).subscheme := hSvar.toIsIntegral
  haveI : CompactSpace (hyperplaneSection φ c).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace ((hyperplaneSection φ c).subschemeι ≫ sX)
  have hSnv : IsNormalVariety k ((hyperplaneSection φ c).subschemeι ≫ sX) := ⟨hSvar, hSn⟩
  have hdimS' : topologicalKrullDim (hyperplaneSection φ c).subscheme =
      ((d + 2 : ℕ) : WithBot ℕ∞) := by
    rw [hdimX] at hdimS
    exact withBot_eq_natCast_of_add_one_eq hdimS
  haveI hSproj : AlgebraicGeometry.IsProjectiveVariety k
      ((hyperplaneSection φ c).subschemeι ≫ sX) :=
    { toIsVariety := hSvar
      isProjective := isProjectiveMorphism_comp_isClosedImmersion _ sX
        (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sX).isProjective }
  obtain ⟨K₁, hK₁⟩ := exists_isCanonicalDivisor_of_isNormalVariety _ hSnv hdimS'
  -- the restricted boundary is effective with coefficients `< 1`
  obtain ⟨hB₁0, hB₁1⟩ := zero_le_and_coeff_lt_one_restrictComponents
    (hyperplaneSection φ c).subschemeι hB (roundDown_nonpos_iff.1 hklt.2.2)
    (h₂ c hc hc₂ hdimS')
  -- the discrepancy of `(S, B|_S)`
  obtain ⟨t, ht0, hQt⟩ := h₃ c hc hc₃
  rw [MvPolynomial.eval_rename] at hQt
  obtain ⟨hσ, hZ⟩ := hQc (t • c) hQt
  have hsuppS := hsupp (t • c) hσ
  rw [hyperplaneSection_smul φ c ht0] at hsuppS
  obtain ⟨x₀⟩ : Nonempty (hyperplaneSection φ c).subscheme := inferInstance
  have hirr : IsIrreducible ((hyperplaneSection φ c).support : Set X) := by
    have := (IrreducibleSpace.isIrreducible_univ (hyperplaneSection φ c).subscheme).image
      (hyperplaneSection φ c).subschemeι ((hyperplaneSection φ c).subschemeι.continuous).continuousOn
    rwa [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at this
  have hx₀S : (hyperplaneSection φ c).subschemeι x₀ ∈
      ((hyperplaneSection φ c).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x₀, rfl⟩
  have hx₀ : (hyperplaneSection φ c).subschemeι x₀ ∈
      ((M.zeroDivisor (∑ j, scalarsToGlobalSections k sX ((t • c) j) • s j) hσ).supp :
        Set X) := by
    rw [hsuppS]; exact hx₀S
  have hcc : connectedComponentIn
      ((M.zeroDivisor (∑ j, scalarsToGlobalSections k sX ((t • c) j) • s j) hσ).supp : Set X)
      ((hyperplaneSection φ c).subschemeι x₀) =
        (((hyperplaneSection φ c).support : TopologicalSpace.Closeds X) : Set X) := by
    rw [hsuppS]
    exact (IsPreirreducible.isPreconnected hirr.2).connectedComponentIn hx₀S
  have h5 := hZ (hyperplaneSection φ c).support _ hx₀ hcc
  generalize hJ : Scheme.IdealSheafData.vanishingIdeal (hyperplaneSection φ c).support = J at h5
  rw [MMP.Positivity.vanishingIdeal_support_of_isReduced] at hJ
  subst hJ
  obtain ⟨_hH5, hdisc⟩ := h5
  have hdisc' := hdisc (d + 3) (d + 2) K K₁ hK
  -- adjunction on `S`, read on the open subscheme `⊤`
  have hZeq : Stacks.Divisors.zeroScheme X (pullTwist φ) (systemSection (pulledSystem φ) c) =
      hyperplaneSection φ c := zeroScheme_pulledSystem hφ c
  have h6 := h₄ c hc hc₄
  rw [hZeq] at h6
  haveI : IsIso (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι := isIso_ι_of_eq_top rfl
  haveI : Nonempty (⊤ : (hyperplaneSection φ c).subscheme.Opens) := ⟨⟨x₀, trivial⟩⟩
  have hconn : _root_.IsConnected ((⊤ : (hyperplaneSection φ c).subscheme.Opens) :
      Set (hyperplaneSection φ c).subscheme) := by
    rw [TopologicalSpace.Opens.coe_top]; exact isConnected_univ
  obtain ⟨hWnv, -, hadj⟩ := h6 ⊤
    (by rw [TopologicalSpace.Opens.coe_top]; exact isClopen_univ) hconn
  have hK' := Divisor.IsCanonicalDivisor.restrictOpen hSnv hK₁ ⊤
  obtain ⟨m, hmdef⟩ : ∃ m, (Divisor.toQDivisor K + B).cartierIndex hklt.1.2.2 = m := ⟨_, rfl⟩
  have hm : 0 < m := by rw [← hmdef]; exact QDivisor.cartierIndex_pos hklt.1.2.2
  obtain ⟨D, hD, hDc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hklt.1.2.2
  rw [hmdef] at hD
  obtain ⟨D', hD'eq, hD'c, ⟨eD'⟩⟩ := hadj m hm (d + 3) (d + 2) K (K₁.restrictOpen ⊤) hK hK' D hD hDc
  -- the Cartier divisor `D'' = m (K_S + B|_S)` on `S`
  obtain ⟨D'', hD''⟩ := exists_restrictOpen_eq_of_eq_top
    (rfl : (⊤ : (hyperplaneSection φ c).subscheme.Opens) = ⊤) D'
  have hD''c : Divisor.IsCartier D'' := isCartier_of_isCartier_restrictOpen_of_eq_top rfl
    (by rw [hD'']; exact hD'c)
  have hres : (Divisor.toQDivisor K₁ +
      B.restrictComponents (hyperplaneSection φ c).subschemeι).restrictOpen ⊤ =
      Divisor.toQDivisor (K₁.restrictOpen ⊤) + B.restrictComponents
        ((⊤ : (hyperplaneSection φ c).subscheme.Opens).ι ≫ (hyperplaneSection φ c).subschemeι) := by
    rw [restrictComponents_comp_eq_restrictOpen_of_eq_top _ rfl, ← restrictOpen_toQDivisor,
      restrictOpen_add]
  have hD'q : Divisor.toQDivisor D' = (m : ℤ) • (Divisor.toQDivisor K₁ +
      B.restrictComponents (hyperplaneSection φ c).subschemeι).restrictOpen ⊤ := by
    rw [hres]; exact hD'eq
  have hD''eq : Divisor.toQDivisor D'' = (m : ℤ) • (Divisor.toQDivisor K₁ +
      B.restrictComponents (hyperplaneSection φ c).subschemeι) := by
    apply restrictOpen_injective_of_eq_top
      (rfl : (⊤ : (hyperplaneSection φ c).subscheme.Opens) = ⊤)
    rw [restrictOpen_toQDivisor, hD'', hD'q, restrictOpen_zsmul]
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hQC : (Divisor.toQDivisor K₁ +
      B.restrictComponents (hyperplaneSection φ c).subschemeι).IsQCartier :=
    ⟨(m : ℤ), hm0, hD''eq ▸ QDivisor.isCartierDivisor_toQDivisor.mpr hD''c⟩
  have hklt₁ : IsKltPair ((hyperplaneSection φ c).subschemeι ≫ sX) (d + 2) K₁
      (B.restrictComponents (hyperplaneSection φ c).subschemeι) :=
    ⟨⟨hSnv, hK₁, hQC⟩, lt_of_lt_of_le hklt.2.1 hdisc', roundDown_nonpos_iff.2 hB₁1⟩
  refine ⟨inferInstance, inferInstance, inferInstance, hSproj, K₁,
    B.restrictComponents (hyperplaneSection φ c).subschemeι, hklt₁, hB₁0, ?_⟩
  intro C j _ hdim
  -- the intersection numbers, computed on `⊤` and through `D'`
  obtain ⟨j', rfl⟩ : ∃ j' : C ⟶ (⊤ : (hyperplaneSection φ c).subscheme.Opens).toScheme,
      j' ≫ (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι = j :=
    ⟨j ≫ inv (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι, by simp⟩
  haveI : IsIntegral (⊤ : (hyperplaneSection φ c).subscheme.Opens).toScheme :=
    hWnv.1.toIsIntegral
  haveI : IsNormal (⊤ : (hyperplaneSection φ c).subscheme.Opens).toScheme := hWnv.2
  haveI : LocallyOfFiniteType ((⊤ : (hyperplaneSection φ c).subscheme.Opens).ι ≫
      (hyperplaneSection φ c).subschemeι ≫ sX) := hWnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (⊤ : (hyperplaneSection φ c).subscheme.Opens).toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((⊤ : (hyperplaneSection φ c).subscheme.Opens).ι ≫
      (hyperplaneSection φ c).subschemeι ≫ sX)
  haveI : CompactSpace (⊤ : (hyperplaneSection φ c).subscheme.Opens).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace ((⊤ : (hyperplaneSection φ c).subscheme.Opens).ι ≫
      (hyperplaneSection φ c).subschemeι ≫ sX)
  haveI : IsProper (j' ≫ (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι ≫
      (hyperplaneSection φ c).subschemeι ≫ sX) := by
    have := (inferInstance : IsProper (((j' ≫ (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι) ≫
      (hyperplaneSection φ c).subschemeι) ≫ sX))
    simpa only [Category.assoc] using this
  haveI : IsProper ((j' ≫ (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι ≫
      (hyperplaneSection φ c).subschemeι) ≫ sX) := by
    have := (inferInstance : IsProper (((j' ≫ (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι) ≫
      (hyperplaneSection φ c).subschemeι) ≫ sX))
    simpa only [Category.assoc] using this
  haveI : IsDominant (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι := inferInstance
  have hLU : QDivisor.IsQCartier ((Divisor.toQDivisor K₁ +
      B.restrictComponents (hyperplaneSection φ c).subschemeι).restrictOpen ⊤) :=
    ⟨(m : ℤ), hm0, hD'q ▸ QDivisor.isCartierDivisor_toQDivisor.mpr hD'c⟩
  have e1 := MMP.Flips.intersectionNumber_restrictOpen ((hyperplaneSection φ c).subschemeι ≫ sX) ⊤
    (Divisor.toQDivisor K₁ + B.restrictComponents (hyperplaneSection φ c).subschemeι)
    hklt₁.1.2.2 hLU j' hdim
  rw [← e1, QDivisor.intersectionNumber_eq_of_smul k _ j' hdim _ hLU hm D' hD'c hD'q,
    QDivisor.intersectionNumber_eq_of_smul k sX _ hdim _ hklt.1.2.2 hm D hDc hD]
  -- the degree of `𝒪(D') ≅ (𝒪(D) ⊗ L^{⊗ m})|_S`
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  haveI := hDc.isInvertibleModule_divisorialSheaf
  haveI := hD'c.isInvertibleModule_divisorialSheaf
  obtain ⟨hpow, hdeg⟩ := exists_isInvertible_degreeOn_tensorPow_succ (k := k) sX
    ((j' ≫ (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι) ≫ (hyperplaneSection φ c).subschemeι)
    hdim (pullTwist φ) m'
  haveI := hpow
  haveI hF : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (D.divisorialSheaf ⊗ MMP.Intersection.Scheme.Modules.tensorPow (pullTwist φ) (m' + 1) :
        X.Modules) :=
    isInvertible_tensorModules D.divisorialSheaf
      (MMP.Intersection.Scheme.Modules.tensorPow (pullTwist φ) (m' + 1))
  have hdeg' : (D'.degreeOn k ((⊤ : (hyperplaneSection φ c).subscheme.Opens).ι ≫
      (hyperplaneSection φ c).subschemeι ≫ sX) j' hdim hD'c : ℤ) =
      D.degreeOn k sX ((j' ≫ (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι) ≫
        (hyperplaneSection φ c).subschemeι) hdim hDc +
      ((m' + 1 : ℕ) : ℤ) * degreeOn k sX ((j' ≫ (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι) ≫
        (hyperplaneSection φ c).subschemeι) hdim (pullTwist φ) := by
    change degreeOn k _ j' hdim D'.divisorialSheaf = degreeOn k sX _ hdim D.divisorialSheaf + _
    rw [degreeOn_eq_of_iso k _ j' hdim eD',
      degreeOn_pullback_eq_degreeOn_comp (sX := (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι ≫
        (hyperplaneSection φ c).subschemeι ≫ sX) (sY := sX)
        (f := (⊤ : (hyperplaneSection φ c).subscheme.Opens).ι ≫ (hyperplaneSection φ c).subschemeι)
        (i := j') (Category.assoc _ _ _) hdim,
      degreeOn_congr_hom sX (Category.assoc _ _ _).symm hdim, ← hdeg]
    exact degreeOn_tensorSheaf k sX _ hdim D.divisorialSheaf
      (MMP.Intersection.Scheme.Modules.tensorPow (pullTwist φ) (m' + 1)) (hLM := hF)
  rw [hdeg']
  have hm1 : (m' : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  rw [add_div, mul_div_cancel_left₀ _ hm1]

/-- **A general hyperplane section of the component and of its normal model.** For a general
hyperplane `H = V(c)`, the cut `E ∩ H` is integral of dimension `dim E - 1`, `Eᵛ ∩ H` is a normal
integral scheme, the restriction `Eᵛ ∩ H ⟶ E ∩ H` of `ν` is birational and an isomorphism over
`V ∩ H`, and `(V ∩ H)ᶜ` has dimension one less than `Vᶜ`. -/
private theorem exists_dense_open_cutMap {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E] {m : ℕ}
    (hEr : topologicalKrullDim E = (m + 2 : ℕ))
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX)
    {Eν : Scheme.{0}} (ν : Eν ⟶ E) [IsFinite ν] [IsIntegral Eν] [IsNormal Eν]
    (hν : IsBirational ν) (V : E.Opens) [IsIso (ν ∣_ V)]
    (hV : topologicalKrullDim ↥((V : Set E)ᶜ) ≤ (m + 1 : ℕ)) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c₀ : Fin (N + 1) → k) (hc₀ : c₀ ≠ 0), dualPoint c₀ hc₀ ∈ U →
      haveI := isFinite_cutMap ν (i ≫ φ) c₀
      IsIntegral (hyperplaneSection (i ≫ φ) c₀).subscheme ∧
      IsIntegral (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme ∧
      IsNormal (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme ∧
      IsIso (cutMap ν (i ≫ φ) c₀ ∣_ ((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V)) ∧
      topologicalKrullDim (hyperplaneSection (i ≫ φ) c₀).subscheme = (m + 1 : ℕ) ∧
      IsBirational (cutMap ν (i ≫ φ) c₀) ∧
      topologicalKrullDim ↥((((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V :
          TopologicalSpace.Opens _) : Set (hyperplaneSection (i ≫ φ) c₀).subscheme)ᶜ) ≤
        (m : ℕ) := by
  classical
  letI : E.Over (Spec (.of k)) := ⟨i ≫ sX⟩
  letI : Eν.Over (Spec (.of k)) := ⟨ν ≫ i ≫ sX⟩
  haveI : AlgebraicGeometry.IsVariety k (i ≫ sX) := {}
  haveI : AlgebraicGeometry.IsVariety k (E ↘ Spec (.of k)) :=
    (inferInstance : AlgebraicGeometry.IsVariety k (i ≫ sX))
  haveI : AlgebraicGeometry.IsVariety k (ν ≫ i ≫ sX) := {}
  haveI : AlgebraicGeometry.IsVariety k (Eν ↘ Spec (.of k)) :=
    (inferInstance : AlgebraicGeometry.IsVariety k (ν ≫ i ≫ sX))
  haveI : IsLocallyNoetherian Eν := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ i ≫ sX)
  have hφν : (ν ≫ i ≫ φ) ≫ Stacks.ProjectiveCohomology.projModelToSpec k N =
      Eν ↘ Spec (.of k) := by
    rw [Category.assoc, Category.assoc, hφ]; rfl
  haveI : (ν ≫ i ≫ φ).IsOver (Spec (.of k)) := ⟨by rw [over_projectiveSpace_eq]; exact hφν⟩
  have hφE : (i ≫ φ) ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = E ↘ Spec (.of k) := by
    rw [Category.assoc, hφ]; rfl
  have hdimE : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure (Set.range (i ≫ φ).base)) := by
    rw [(i ≫ φ).isClosedEmbedding.isClosed_range.closure_eq]
    erw [topologicalKrullDim_range_eq (i ≫ φ), hEr]
    exact_mod_cast (by omega : 2 ≤ m + 2)
  -- `ν` is surjective: it is closed and its image contains the generic point of `E`
  have hsurj : Function.Surjective ν := by
    have hgen : ν (genericPoint Eν) = genericPoint E := by
      have h := hν.bijOn.mapsTo (show genericPoint Eν ∈ genericPoints Eν by
        rw [genericPoints_eq_singleton]; rfl)
      rwa [genericPoints_eq_singleton] at h
    have hr : Set.range ν = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      have hcl : closure ({genericPoint E} : Set E) = Set.univ := genericPoint_spec E
      rw [← hcl]
      exact closure_minimal (Set.singleton_subset_iff.mpr ⟨_, hgen⟩)
        ν.isClosedMap.isClosed_range
    exact fun z => (Set.mem_range).1 (hr ▸ Set.mem_univ z)
  have himage : (2 : WithBot ℕ∞) ≤
      topologicalKrullDim (closure (Set.range (ν ≫ i ≫ φ).base)) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]
    exact hdimE
  -- Bertini on the normal variety `Eᵛ`
  obtain ⟨U₁, hU₁, h₁⟩ := exists_dense_open_hyperplaneSection_restrictComponents
    (Z := Eν) (ν ≫ i ≫ φ)
    (by rw [Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec]; exact hφν)
    (J := Empty) (fun e => e.elim) (fun e => e.elim)
  -- Bertini on the variety `E`: irreducibility, reducedness and dimensions
  obtain ⟨U₂, hU₂, h₂⟩ : ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c₀ : Fin (N + 1) → k) (hc₀ : c₀ ≠ 0), dualPoint c₀ hc₀ ∈ U →
      IsIntegral (hyperplaneSection (i ≫ φ) c₀).subscheme ∧
      topologicalKrullDim (hyperplaneSection (i ≫ φ) c₀).subscheme = (m + 1 : ℕ) ∧
      topologicalKrullDim ↥((((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V :
          TopologicalSpace.Opens _) : Set (hyperplaneSection (i ≫ φ) c₀).subscheme)ᶜ) ≤
        (m : ℕ) := by
    obtain ⟨Ud, hUd, hd⟩ := exists_dense_open_topologicalKrullDim_inter_hyperplaneSection (i ≫ φ)
      (fun b : Bool => if b then Set.univ else ((V : Set E)ᶜ))
      (fun b => by cases b <;> [exact V.isOpen.isClosed_compl; exact isClosed_univ])
    obtain ⟨⟨Ui, hUi, hirr⟩, -⟩ := exists_dense_open_hyperplaneSection k (V := E) (i ≫ φ) hφE
      (fun e : Empty => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun e : Empty => e.elim) (fun e => e.elim) 0
    obtain ⟨-, Ur, hUr, hred⟩ := exists_dense_open_isReduced_zeroScheme (X := E)
      (pulledSystem (i ≫ φ)) (iSup_nonvanishingOpen_pulledSystem hφE)
    refine ⟨Ud ⊓ Ui ⊓ Ur, ?_, fun c₀ hc₀ hmem => ?_⟩
    · simp only [TopologicalSpace.Opens.coe_inf]
      exact (hUd.inter_of_isOpen_left hUi Ud.isOpen).inter_of_isOpen_left hUr
        (Ud.isOpen.inter Ui.isOpen)
    rw [TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_inf] at hmem
    obtain ⟨⟨hm₁, hm₂⟩, hm₃⟩ := hmem
    have hR : IsReduced (hyperplaneSection (i ≫ φ) c₀).subscheme := by
      have := hred c₀ hc₀ hm₃
      rwa [zeroScheme_pulledSystem hφE] at this
    have hI : IsIrreducible ((hyperplaneSection (i ≫ φ) c₀).support : Set E) :=
      (hirr c₀ hc₀ hm₂).2.1 hdimE
    haveI : IrreducibleSpace (hyperplaneSection (i ≫ φ) c₀).subscheme := by
      have h := hI
      rw [← Scheme.IdealSheafData.range_subschemeι] at h
      haveI := Subtype.irreducibleSpace h
      let e := (hyperplaneSection (i ≫ φ) c₀).subschemeι.isEmbedding.toHomeomorph
      exact e.symm.surjective.irreducibleSpace e.symm.continuous
    refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, ?_, ?_⟩
    · have h1 : (1 : WithBot ℕ∞) ≤ topologicalKrullDim (Set.univ : Set E) := by
        rw [(Homeomorph.Set.univ E).isHomeomorph.topologicalKrullDim_eq, hEr]
        exact_mod_cast (by omega : 1 ≤ m + 2)
      obtain ⟨-, hdim⟩ := (hd c₀ hc₀ hm₁ true).2 h1
      rw [if_pos rfl, Set.univ_inter] at hdim
      rw [(Homeomorph.Set.univ E).isHomeomorph.topologicalKrullDim_eq, hEr] at hdim
      rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
      exact withBot_eq_natCast_of_add_one_eq hdim
    · have himg : (hyperplaneSection (i ≫ φ) c₀).subschemeι ''
          ((((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V : TopologicalSpace.Opens _) :
            Set (hyperplaneSection (i ≫ φ) c₀).subscheme)ᶜ) =
          (V : Set E)ᶜ ∩ (hyperplaneSection (i ≫ φ) c₀).support := by
        rw [Scheme.Hom.coe_preimage, ← Set.preimage_compl, Set.image_preimage_eq_inter_range,
          Scheme.IdealSheafData.range_subschemeι]
      rw [← topologicalKrullDim_image_of_isEmbedding
        (hyperplaneSection (i ≫ φ) c₀).subschemeι.isClosedEmbedding.isEmbedding, himg]
      obtain ⟨hlt, hge⟩ := hd c₀ hc₀ hm₁ false
      simp only [Bool.false_eq_true, if_false] at hlt hge
      by_cases h1 : 1 ≤ topologicalKrullDim ↥((V : Set E)ᶜ)
      · obtain ⟨-, hdim⟩ := hge h1
        exact withBot_le_natCast_of_add_one_le (hdim.trans_le hV)
      · rw [hlt (lt_of_not_ge h1)]
        rw [show topologicalKrullDim (∅ : Set E) = ⊥ from
          (topologicalKrullDim_eq_bot_iff_isEmpty _).2 (Set.isEmpty_coe_sort.2 rfl)]
        exact bot_le
  refine ⟨U₁ ⊓ U₂, ?_, fun c₀ hc₀ hmem => ?_⟩
  · rw [TopologicalSpace.Opens.coe_inf]
    exact hU₁.inter_of_isOpen_left hU₂ U₁.isOpen
  rw [TopologicalSpace.Opens.mem_inf] at hmem
  obtain ⟨hm₁, hm₂⟩ := hmem
  obtain ⟨hA, -, -⟩ := h₁ c₀ hc₀ hm₁
  obtain ⟨hvar, hnorm, -⟩ := hA himage
  obtain ⟨hint, hdim, hdimV⟩ := h₂ c₀ hc₀ hm₂
  haveI : IsIntegral (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme := hvar.toIsIntegral
  haveI := isFinite_cutMap ν (i ≫ φ) c₀
  have hiso : IsIso (cutMap ν (i ≫ φ) c₀ ∣_ ((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V)) :=
    isIso_subschemeMap_morphismRestrict ν V _ _ (hyperplaneSection_comp ν (i ≫ φ) c₀) _
      (cutMap_subschemeι _ _ _)
  refine ⟨hint, inferInstance, hnorm, hiso, hdim, ?_, hdimV⟩
  -- birationality: `cutMap` is an isomorphism over the dense open `V ∩ H`
  haveI := hint
  have hWne : (((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V : TopologicalSpace.Opens _) :
      Set (hyperplaneSection (i ≫ φ) c₀).subscheme).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.compl_empty, (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq,
      hdim] at hdimV
    have : m + 1 ≤ m := by exact_mod_cast hdimV
    omega
  obtain ⟨y, hy⟩ := hWne
  have hsrc : ((cutMap ν (i ≫ φ) c₀ ⁻¹ᵁ ((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V) :
      TopologicalSpace.Opens _) : Set (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme).Nonempty :=
    ⟨_, ((inv (cutMap ν (i ≫ φ) c₀ ∣_ ((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V)))
      ⟨y, hy⟩).2⟩
  refine isBirational_of_isIso_morphismRestrict _ _ hiso (fun x hx => ?_) (fun z hz => ?_)
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).2
      ⟨hsrc.some, Set.mem_univ _, hsrc.some_mem⟩
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hz
    subst hz
    exact ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).2
      ⟨y, Set.mem_univ _, hy⟩

/-- **A general hyperplane cuts the fibre down by one dimension.** -/
private theorem exists_dense_open_topologicalKrullDim_fibre {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {S : Scheme.{0}} (f : X ⟶ S) (s : S) (hs : IsClosed ({s} : Set S)) {m : ℕ}
    (hfib : topologicalKrullDim (f ⁻¹' {s}) ≤ (m + 2 : ℕ))
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ] :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        topologicalKrullDim (((hyperplaneSection φ c).subschemeι ≫ f) ⁻¹' {s}) ≤
          (m + 1 : ℕ) := by
  obtain ⟨U, hU, h⟩ := exists_dense_open_topologicalKrullDim_inter_hyperplaneSection φ
    (fun _ : Unit => f ⁻¹' {s}) (fun _ => hs.preimage f.continuous)
  refine ⟨U, hU, fun c hc hmem => ?_⟩
  obtain ⟨hlt, hge⟩ := h c hc hmem ()
  have himg : (hyperplaneSection φ c).subschemeι ''
      (((hyperplaneSection φ c).subschemeι ≫ f) ⁻¹' {s}) =
        f ⁻¹' {s} ∩ (hyperplaneSection φ c).support := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range,
      Scheme.IdealSheafData.range_subschemeι]
  have hd := topologicalKrullDim_image_of_isEmbedding
    (hyperplaneSection φ c).subschemeι.isClosedEmbedding.isEmbedding
    (((hyperplaneSection φ c).subschemeι ≫ f) ⁻¹' {s})
  rw [himg] at hd
  rw [← hd]
  by_cases h1 : 1 ≤ topologicalKrullDim ↥(f ⁻¹' {s})
  · obtain ⟨-, hdim⟩ := hge h1
    exact withBot_le_natCast_of_add_one_le (hdim.trans_le hfib)
  · rw [hlt (lt_of_not_ge h1)]
    rw [show topologicalKrullDim (∅ : Set X) = ⊥ from
      (topologicalKrullDim_eq_bot_iff_isEmpty _).2 (Set.isEmpty_coe_sort.2 rfl)]
    exact bot_le

open MonoidalCategory in
/-- **Adjunction for the zero scheme of a section, on the smooth locus.** Let `g : Y ⟶ Spec k`
have smooth locus `W`, a smooth integral scheme of dimension `m + 2`, let `L` be an invertible
sheaf on `P` pulled back along `p ≫ φ : Y ⟶ P`, and let `H ⊆ Y` be a closed subscheme meeting `W`
in the smooth zero scheme of the nonzero section `s|_W`. If the points of `H` over `W` lie in the
smooth locus of `H`, then along every `j : C ⟶ H` inside both smooth loci,
`ω_H|_C ≅ (ω_W ⊗ (p ≫ φ)^*L)|_C`. -/
private theorem nonempty_canonicalSheaf_iso_of_zeroScheme {k : Type} [Field k] {m : ℕ}
    {Y X P : Scheme.{0}} (g : Y ⟶ Spec (.of k)) (p : Y ⟶ X) (φ : X ⟶ P) (L : P.Modules)
    [SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L] (s : Γ(L, ⊤))
    (H : Y.IdealSheafData)
    [IsIntegral (smoothLocus g).toScheme] [IsSeparated ((smoothLocus g).ι ≫ g)]
    [SmoothOfRelativeDimension (m + 1 + 1) ((smoothLocus g).ι ≫ g)]
    (hσ : pullbackGlobalSections ((smoothLocus g).ι ≫ p ≫ φ) L s ≠ 0)
    (hT : Stacks.Divisors.zeroScheme (smoothLocus g).toScheme
      ((Scheme.Modules.pullback ((smoothLocus g).ι ≫ p ≫ φ)).obj L)
      (pullbackGlobalSections ((smoothLocus g).ι ≫ p ≫ φ) L s) = H.comap (smoothLocus g).ι)
    (hsmT : Smooth ((H.comap (smoothLocus g).ι).subschemeι ≫ (smoothLocus g).ι ≫ g))
    (hle : ∀ x : H.subscheme, H.subschemeι x ∈ smoothLocus g →
      x ∈ smoothLocus (H.subschemeι ≫ g))
    (C : Scheme.{0}) (j : C ⟶ H.subscheme)
    (hj₁ : Set.range j ⊆ Set.range (smoothLocus (H.subschemeι ≫ g)).ι)
    (hj : Set.range (j ≫ H.subschemeι) ⊆ Set.range (smoothLocus g).ι) :
    Nonempty ((Scheme.Modules.pullback (IsOpenImmersion.lift _ j hj₁)).obj
        (canonicalSheaf (H.subschemeι ≫ g) (m + 1)) ≅
      tensorModules ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hj)).obj
          (canonicalSheaf g (m + 1 + 1)))
        ((Scheme.Modules.pullback (j ≫ H.subschemeι ≫ p)).obj
          ((Scheme.Modules.pullback φ).obj L))) := by
  classical
  -- adjunction for the zero scheme `H ∩ W`
  haveI : Smooth ((Stacks.Divisors.zeroScheme (smoothLocus g).toScheme
      ((Scheme.Modules.pullback ((smoothLocus g).ι ≫ p ≫ φ)).obj L)
      (pullbackGlobalSections ((smoothLocus g).ι ≫ p ≫ φ) L s)).subschemeι ≫
        (smoothLocus g).ι ≫ g) := by
    rw [hT]; exact hsmT
  have hA := nonempty_pullback_canonical_twist_iso_zeroScheme ((smoothLocus g).ι ≫ g)
    (n := m + 1) ((Scheme.Modules.pullback ((smoothLocus g).ι ≫ p ≫ φ)).obj L)
    (pullbackGlobalSections ((smoothLocus g).ι ≫ p ≫ φ) L s) hσ
  rw [hT] at hA
  obtain ⟨eA⟩ := hA
  -- the maps `C ⟶ H ∩ W ⟶ H_sm`
  obtain ⟨ι₀, hι₀⟩ : ∃ ι₀, IsOpenImmersion.lift (smoothLocus g).ι (j ≫ H.subschemeι) hj = ι₀ :=
    ⟨_, rfl⟩
  have hι₀W : ι₀ ≫ (smoothLocus g).ι = j ≫ H.subschemeι := by
    rw [← hι₀]; exact IsOpenImmersion.lift_fac _ _ _
  rw [hι₀]
  obtain ⟨t, ht⟩ : ∃ t : C ⟶ (H.comap (smoothLocus g).ι).subscheme,
      Limits.pullback.lift ι₀ j hι₀W ≫ (H.comapIso (smoothLocus g).ι).inv = t := ⟨_, rfl⟩
  have htT : t ≫ (H.comap (smoothLocus g).ι).subschemeι = ι₀ := by
    rw [← ht, Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι,
      Limits.pullback.lift_fst]
  obtain ⟨τ, hτdef⟩ : ∃ τ : (H.comap (smoothLocus g).ι).subscheme ⟶ H.subscheme,
      (H.comapIso (smoothLocus g).ι).hom ≫ Limits.pullback.snd _ _ = τ := ⟨_, rfl⟩
  haveI : IsOpenImmersion τ := by rw [← hτdef]; infer_instance
  have h1 : (H.comapIso (smoothLocus g).ι).hom ≫
      Limits.pullback.fst (smoothLocus g).ι H.subschemeι =
      (H.comap (smoothLocus g).ι).subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_inv_subschemeι, Iso.hom_inv_id_assoc]
  have hτ : τ ≫ H.subschemeι = (H.comap (smoothLocus g).ι).subschemeι ≫ (smoothLocus g).ι := by
    rw [← hτdef, Category.assoc, ← Limits.pullback.condition, reassoc_of% h1]
  have htτ : t ≫ τ = j := by
    rw [← ht, ← hτdef, Category.assoc, Iso.inv_hom_id_assoc, Limits.pullback.lift_snd]
  have hτr : Set.range τ ⊆ Set.range (smoothLocus (H.subschemeι ≫ g)).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hle
    rw [← Scheme.Hom.comp_apply, hτ, Scheme.Hom.comp_apply]
    exact ((H.comap (smoothLocus g).ι).subschemeι x).2
  obtain ⟨ρ, hρ⟩ : ∃ ρ, IsOpenImmersion.lift (smoothLocus (H.subschemeι ≫ g)).ι τ hτr = ρ :=
    ⟨_, rfl⟩
  have hρι : ρ ≫ (smoothLocus (H.subschemeι ≫ g)).ι = τ := by
    rw [← hρ]; exact IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (ρ ≫ (smoothLocus (H.subschemeι ≫ g)).ι) := by
    rw [hρι]; infer_instance
  haveI : IsOpenImmersion ρ := IsOpenImmersion.of_comp ρ (smoothLocus (H.subschemeι ≫ g)).ι
  have hℓ : IsOpenImmersion.lift _ j hj₁ = t ≫ ρ := by
    rw [← cancel_mono (smoothLocus (H.subschemeι ≫ g)).ι, IsOpenImmersion.lift_fac,
      Category.assoc, hρι, htτ]
  have hc : ρ ≫ (smoothLocus (H.subschemeι ≫ g)).ι ≫ H.subschemeι ≫ g =
      ((H.comap (smoothLocus g).ι).subschemeι ≫ (smoothLocus g).ι ≫ g) ≫ 𝟙 _ := by
    rw [reassoc_of% hρι, reassoc_of% hτ, Category.comp_id]
  have hM : ι₀ ≫ (smoothLocus g).ι ≫ p ≫ φ = (j ≫ H.subschemeι ≫ p) ≫ φ := by
    simp only [Category.assoc, reassoc_of% hι₀W]
  have hΩ : Scheme.Hom.relativeDifferentialForms ((smoothLocus g).ι ≫ g) (((m + 1 : ℕ) : ℤ) + 1) =
      canonicalSheaf g (m + 1 + 1) := by
    rw [canonicalSheaf, show ((m + 1 + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring]
  -- the isomorphism, step by step
  have e₁ : (Scheme.Modules.pullback (IsOpenImmersion.lift _ j hj₁)).obj
      (canonicalSheaf (H.subschemeι ≫ g) (m + 1)) ≅ (Scheme.Modules.pullback t).obj
        ((Scheme.Modules.pullback ρ).obj (canonicalSheaf (H.subschemeι ≫ g) (m + 1))) :=
    eqToIso (by rw [hℓ]) ≪≫ ((Scheme.Modules.pullbackComp t ρ).app _).symm
  have e₂ : (Scheme.Modules.pullback ρ).obj (canonicalSheaf (H.subschemeι ≫ g) (m + 1)) ≅
      Scheme.Hom.relativeDifferentialForms
        ((H.comap (smoothLocus g).ι).subschemeι ≫ (smoothLocus g).ι ≫ g) ((m + 1 : ℕ) : ℤ) :=
    @asIso _ _ _ _ (Scheme.Hom.relativeDifferentialFormsMap ρ _ _ (𝟙 _) hc ((m + 1 : ℕ) : ℤ))
      (Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ρ _ _ (𝟙 _) hc _)
  have e₃ : (Scheme.Modules.pullback ι₀).obj
      (Scheme.Hom.relativeDifferentialForms ((smoothLocus g).ι ≫ g) (((m + 1 : ℕ) : ℤ) + 1) ⊗
        (Scheme.Modules.pullback ((smoothLocus g).ι ≫ p ≫ φ)).obj L) ≅
      (Scheme.Modules.pullback t).obj (Scheme.Hom.relativeDifferentialForms
        ((H.comap (smoothLocus g).ι).subschemeι ≫ (smoothLocus g).ι ≫ g) ((m + 1 : ℕ) : ℤ)) :=
    eqToIso (by rw [htT]) ≪≫
      ((Scheme.Modules.pullbackComp t (H.comap (smoothLocus g).ι).subschemeι).app _).symm ≪≫
      (Scheme.Modules.pullback t).mapIso eA
  have eM : (Scheme.Modules.pullback ι₀).obj
      ((Scheme.Modules.pullback ((smoothLocus g).ι ≫ p ≫ φ)).obj L) ≅
      (Scheme.Modules.pullback (j ≫ H.subschemeι ≫ p)).obj ((Scheme.Modules.pullback φ).obj L) :=
    (Scheme.Modules.pullbackComp ι₀ ((smoothLocus g).ι ≫ p ≫ φ)).app L ≪≫
      eqToIso (by rw [hM]) ≪≫ ((Scheme.Modules.pullbackComp (j ≫ H.subschemeι ≫ p) φ).app L).symm
  have e₄ : (Scheme.Modules.pullback ι₀).obj
      (Scheme.Hom.relativeDifferentialForms ((smoothLocus g).ι ≫ g) (((m + 1 : ℕ) : ℤ) + 1) ⊗
        (Scheme.Modules.pullback ((smoothLocus g).ι ≫ p ≫ φ)).obj L) ≅
      (Scheme.Modules.pullback ι₀).obj (canonicalSheaf g (m + 1 + 1)) ⊗
        (Scheme.Modules.pullback (j ≫ H.subschemeι ≫ p)).obj
          ((Scheme.Modules.pullback φ).obj L) :=
    Stacks.RelativeVeryAmple.pullbackTensorModulesIso ι₀ _ _ ≪≫
      MonoidalCategory.whiskerRightIso ((Scheme.Modules.pullback ι₀).mapIso (eqToIso hΩ)) _ ≪≫
      MonoidalCategory.whiskerLeftIso _ eM
  exact ⟨e₁ ≪≫ (Scheme.Modules.pullback t).mapIso e₂ ≪≫ e₃.symm ≪≫ e₄⟩

/-- **Smoothness and adjunction on the smooth locus of `Eᵛ`.** For a general hyperplane
`H = V(c)`, the points of `Eᵛ ∩ H` over the smooth locus of `Eᵛ` lie in the smooth locus of
`Eᵛ ∩ H`, and there `ω_{Eᵛ ∩ H} ≅ (ω_{Eᵛ} ⊗ 𝒪(H))|_{Eᵛ ∩ H}`, read along any curve. -/
private theorem exists_dense_open_canonicalSheaf_adjunction {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E] {m : ℕ}
    (hEr : topologicalKrullDim E = (m + 2 : ℕ))
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX)
    {Eν : Scheme.{0}} (ν : Eν ⟶ E) [IsFinite ν] [IsIntegral Eν] [IsNormal Eν]
    (hν : IsBirational ν) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c₀ : Fin (N + 1) → k) (hc₀ : c₀ ≠ 0), dualPoint c₀ hc₀ ∈ U →
      (∀ x : (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme,
          (hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι x ∈ smoothLocus (ν ≫ i ≫ sX) →
            x ∈ smoothLocus ((hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι ≫ ν ≫ i ≫ sX)) ∧
      ∀ (C : Scheme.{0}) (j : C ⟶ (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme)
          (hj₁ : Set.range j ⊆ Set.range (smoothLocus
            ((hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι ≫ ν ≫ i ≫ sX)).ι)
          (hj : Set.range (j ≫ (hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι) ⊆
            Set.range (smoothLocus (ν ≫ i ≫ sX)).ι),
          Nonempty ((Scheme.Modules.pullback (IsOpenImmersion.lift _ j hj₁)).obj
              (canonicalSheaf ((hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι ≫ ν ≫ i ≫ sX)
                (m + 1)) ≅
            tensorModules ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hj)).obj
              (canonicalSheaf (ν ≫ i ≫ sX) (m + 1 + 1)))
              ((Scheme.Modules.pullback
                (j ≫ (hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι ≫ ν ≫ i)).obj
                ((Scheme.Modules.pullback φ).obj (twistOne k N)))) := by
  classical
  set g := ν ≫ i ≫ sX with hg
  letI : E.Over (Spec (.of k)) := ⟨i ≫ sX⟩
  haveI : AlgebraicGeometry.IsVariety k (i ≫ sX) := {}
  haveI : AlgebraicGeometry.IsVariety k (E ↘ Spec (.of k)) :=
    (inferInstance : AlgebraicGeometry.IsVariety k (i ≫ sX))
  haveI : AlgebraicGeometry.IsVariety k g := {}
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : IsLocallyNoetherian Eν := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : CompactSpace Eν := QuasiCompact.compactSpace_of_compactSpace g
  haveI : IsNoetherian Eν := {}
  have hφE : (i ≫ φ) ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = E ↘ Spec (.of k) := by
    rw [Category.assoc, hφ]; rfl
  haveI : (i ≫ φ).IsOver (Spec (.of k)) := ⟨by rw [over_projectiveSpace_eq]; exact hφE⟩
  -- the smooth locus `W` of `Eᵛ` is a smooth variety: it contains the generic point
  set Wo := smoothLocus g with hWo
  have hgen : genericPoint Eν ∈ Wo := by
    rw [hWo, smoothLocus_eq_smoothLocus]
    exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField g
  haveI : Nonempty Wo := ⟨⟨_, hgen⟩⟩
  letI : Wo.toScheme.Over (Spec (.of k)) := ⟨Wo.ι ≫ g⟩
  haveI : IsIntegral Wo.toScheme := isIntegral_of_isOpenImmersion Wo.ι
  haveI : QuasiCompact Wo.ι :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  haveI : AlgebraicGeometry.IsVariety k (Wo.ι ≫ g) := {}
  haveI : AlgebraicGeometry.IsVariety k (Wo.toScheme ↘ Spec (.of k)) :=
    (inferInstance : AlgebraicGeometry.IsVariety k (Wo.ι ≫ g))
  haveI : Smooth (Wo.ι ≫ g) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    intro x _
    have hW : (Wo : Set Eν) = (g.smoothLocus : Set Eν) := by
      rw [hWo, smoothLocus_eq_smoothLocus]
    show Wo.ι x ∈ (g.smoothLocus : Set Eν)
    rw [← hW]
    exact x.2
  haveI : Smooth (Wo.toScheme ↘ Spec (.of k)) := (inferInstance : Smooth (Wo.ι ≫ g))
  haveI : (Wo.ι ≫ ν).IsOver (Spec (.of k)) := ⟨rfl⟩
  obtain ⟨U, hU, hU'⟩ := exists_dense_open_hyperplaneSection_stratified (X := E) (i ≫ φ)
    (by rw [Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec]; exact hφE)
    (W := Wo.toScheme) (Wo.ι ≫ ν) (A := PUnit) (S := fun _ => Wo.toScheme) (fun _ => 𝟙 _)
    (J := PUnit) (fun _ => (∅ : Set E))
  refine ⟨U, hU, fun c₀ hc₀ hmem => ?_⟩
  obtain ⟨-, hsmT, hint, -⟩ := hU' c₀ hc₀ hmem
  -- the trace `Eᵛ ∩ H ∩ W` of the hyperplane on `W`
  set Hν := hyperplaneSection (ν ≫ i ≫ φ) c₀ with hHν
  have hcomap : (hyperplaneSection (i ≫ φ) c₀).comap (Wo.ι ≫ ν) = Hν.comap Wo.ι := by
    rw [hHν, hyperplaneSection_comp ν (i ≫ φ) c₀, Scheme.IdealSheafData.comap_comp]
  set O := Hν.subschemeι ⁻¹ᵁ Wo with hO
  -- `O ≅ V(Hν|_W)` over `Eᵛ`
  let eO : O.toScheme ≅ (Hν.comap Wo.ι).subscheme :=
    (pullbackRestrictIsoRestrict Hν.subschemeι Wo).symm ≪≫ Limits.pullbackSymmetry _ _ ≪≫
      (Hν.comapIso Wo.ι).symm
  have heO : eO.hom ≫ (Hν.comap Wo.ι).subschemeι ≫ Wo.ι = O.ι ≫ Hν.subschemeι := by
    simp only [eO, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc]
    rw [Limits.pullback.condition, Limits.pullbackSymmetry_hom_comp_snd_assoc,
      pullbackRestrictIsoRestrict_inv_fst_assoc]
  have hsmO : Smooth (O.ι ≫ Hν.subschemeι ≫ g) := by
    have : Smooth ((Hν.comap Wo.ι).subschemeι ≫ Wo.toScheme ↘ Spec (.of k)) := by
      rw [← hcomap]; exact hsmT
    have h2 : O.ι ≫ Hν.subschemeι ≫ g =
        eO.hom ≫ (Hν.comap Wo.ι).subschemeι ≫ Wo.toScheme ↘ Spec (.of k) := by
      rw [← Category.assoc, ← heO]; rfl
    rw [h2]
    infer_instance
  have hOle : O ≤ smoothLocus (Hν.subschemeι ≫ g) := le_smoothLocus _ hsmO
  refine ⟨fun x hx => hOle hx, ?_⟩
  -- `Eᵛ ∩ H ∩ W` is the zero scheme of the section `σ` of `ψ^*𝒪(1)` on `W`
  have hT : Stacks.Divisors.zeroScheme Wo.toScheme
      ((Scheme.Modules.pullback (Wo.ι ≫ (ν ≫ i) ≫ φ)).obj (twistOne k N))
      (pullbackGlobalSections (Wo.ι ≫ (ν ≫ i) ≫ φ) (twistOne k N)
        (formSection (linearForm c₀))) = Hν.comap Wo.ι :=
    (Stacks.Divisors.zeroScheme_pullback (Wo.ι ≫ (ν ≫ i) ≫ φ) (twistOne k N)
      (formSection (linearForm c₀))).trans ((Scheme.IdealSheafData.comap_comp _ _ _).trans
        (congrArg (fun ψ => (hyperplaneSection ψ c₀).comap Wo.ι) (Category.assoc ν i φ)))
  -- `σ ≠ 0`, as `H` does not contain `W`
  have hσ : pullbackGlobalSections (Wo.ι ≫ (ν ≫ i) ≫ φ) (twistOne k N)
      (formSection (linearForm c₀)) ≠ 0 := by
    intro h0
    have h := (hint PUnit.unit).2
    simp only [Scheme.IdealSheafData.comap_id] at h
    rw [hcomap, ← hT, h0, Stacks.Divisors.zeroScheme_zero_eq_bot,
      Scheme.IdealSheafData.support_bot] at h
    simp only [TopologicalSpace.Closeds.coe_top, interior_univ, Set.univ_eq_empty_iff] at h
    exact h.elim (⟨_, hgen⟩ : Wo)
  have hsmT' : Smooth ((Hν.comap Wo.ι).subschemeι ≫ Wo.ι ≫ g) := by
    rw [← hcomap]; exact hsmT
  -- `W` is smooth of relative dimension `m + 2`
  haveI : IsSeparated (Wo.ι ≫ g) := inferInstance
  haveI := hν.isDominant
  have hdimW : topologicalKrullDim Wo.toScheme = ((m + 2 : ℕ) : WithBot ℕ∞) :=
    (Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens k g Wo).trans
      ((topologicalKrullDim_eq_of_isFinite_of_isDominant ν).trans hEr)
  haveI : SmoothOfRelativeDimension (m + 1 + 1) (Wo.ι ≫ g) :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety (Wo.ι ≫ g) (m + 1 + 1) hdimW
  intro C j hj₁ hj
  exact nonempty_canonicalSheaf_iso_of_zeroScheme g (ν ≫ i) φ (twistOne k N)
    (formSection (linearForm c₀)) Hν hσ hT hsmT' (fun x hx => hOle hx) C j hj₁ hj

/-- **The geometry of one general hyperplane section.** For a general hyperplane `H = V(c₀)`,
the section `X₁ = X ∩ H` carries a klt pair `(X₁, B₁)` with `B₁ ≥ 0`, the cut `E₁ = E ∩ H` lies in
the fibre of `X₁ ⟶ S`, which has dimension one less, `Eᵛ ∩ H` is a normal finite birational model of
`E₁`, and, for the invertible sheaf `L = 𝒪_X(H)`, the adjunction formulas
`ω_{Eᵛ ∩ H} = (ω_{Eᵛ} ⊗ L)|` (on the smooth loci) and `K_{X₁} + B₁ = (K_X + B + H)|_{X₁}` hold. -/
private theorem exists_dense_open_cut_data (m : ℕ) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f) (s : S)
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E]
    (hEs : Set.range i ⊆ f ⁻¹' {s}) (hmn : m + 3 ≤ n)
    (hEr : topologicalKrullDim E = (m + 2 : ℕ))
    (hfib : topologicalKrullDim (f ⁻¹' {s}) ≤ (m + 2 : ℕ))
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX)
    {Eν : Scheme.{0}} (ν : Eν ⟶ E) [IsFinite ν] [IsIntegral Eν] [IsNormal Eν]
    (hν : IsBirational ν) (V : E.Opens) [IsIso (ν ∣_ V)]
    (hV : topologicalKrullDim ↥((V : Set E)ᶜ) ≤ (m + 1 : ℕ)) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c₀ : Fin (N + 1) → k) (hc₀ : c₀ ≠ 0), dualPoint c₀ hc₀ ∈ U →
      haveI := isFinite_cutMap ν (i ≫ φ) c₀
      ∃ (X₁ : Scheme.{0}) (ι : X₁ ⟶ X) (h₁ : IsClosedImmersion ι) (h₂ : IsIntegral X₁)
        (h₃ : IsLocallyNoetherian X₁) (h₄ : IsNormal X₁)
        (h₅ : AlgebraicGeometry.IsProjectiveVariety k (ι ≫ sX))
        (K₁ : Divisor X₁) (B₁ : QDivisor X₁) (hklt₁ : MMP.Mori.IsKltPair (ι ≫ sX) (n - 1) K₁ B₁)
        (i₁ : (hyperplaneSection (i ≫ φ) c₀).subscheme ⟶ X₁) (h₆ : IsClosedImmersion i₁)
        (h₇ : IsIntegral (hyperplaneSection (i ≫ φ) c₀).subscheme)
        (h₈ : IsIntegral (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme)
        (h₉ : IsNormal (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme)
        (h₁₀ : IsIso (cutMap ν (i ≫ φ) c₀ ∣_
            ((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V))),
        0 ≤ B₁ ∧ i₁ ≫ ι = (hyperplaneSection (i ≫ φ) c₀).subschemeι ≫ i ∧
        Set.range i₁ ⊆ (ι ≫ f) ⁻¹' {s} ∧
        topologicalKrullDim (hyperplaneSection (i ≫ φ) c₀).subscheme = (m + 1 : ℕ) ∧
        topologicalKrullDim ((ι ≫ f) ⁻¹' {s}) ≤ (m + 1 : ℕ) ∧
        IsBirational (cutMap ν (i ≫ φ) c₀) ∧
        topologicalKrullDim ↥((((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V :
          TopologicalSpace.Opens _) : Set (hyperplaneSection (i ≫ φ) c₀).subscheme)ᶜ) ≤ (m : ℕ) ∧
        ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
        (∀ x : (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme,
          (hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι x ∈ smoothLocus (ν ≫ i ≫ sX) →
            x ∈ smoothLocus (cutMap ν (i ≫ φ) c₀ ≫ i₁ ≫ ι ≫ sX)) ∧
        (∀ (C : Scheme.{0}) (j : C ⟶ (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme)
          (hj₁ : Set.range j ⊆
            Set.range (smoothLocus (cutMap ν (i ≫ φ) c₀ ≫ i₁ ≫ ι ≫ sX)).ι)
          (hj : Set.range (j ≫ (hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι) ⊆
            Set.range (smoothLocus (ν ≫ i ≫ sX)).ι),
          Nonempty ((Scheme.Modules.pullback (IsOpenImmersion.lift _ j hj₁)).obj
              (canonicalSheaf (cutMap ν (i ≫ φ) c₀ ≫ i₁ ≫ ι ≫ sX) (m + 1)) ≅
            tensorModules ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hj)).obj
              (canonicalSheaf (ν ≫ i ≫ sX) (m + 1 + 1)))
              ((Scheme.Modules.pullback
                (j ≫ (hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι ≫ ν ≫ i)).obj L))) ∧
        ∀ (C : Scheme.{0}) (j : C ⟶ X₁) [IsProper ((j ≫ ι) ≫ sX)]
          (hdim : topologicalKrullDim C ≤ 1),
          haveI : IsProper (j ≫ ι ≫ sX) := Category.assoc j ι sX ▸ ‹IsProper ((j ≫ ι) ≫ sX)›
          (Divisor.toQDivisor K₁ + B₁).intersectionNumber k (ι ≫ sX) j hdim hklt₁.1.2.2 =
            (Divisor.toQDivisor K + B).intersectionNumber k sX (j ≫ ι) hdim hklt.1.2.2 +
              degreeOn k sX (j ≫ ι) hdim L := by
  obtain ⟨U₁, hU₁, h₁⟩ :=
    exists_dense_open_isKltPair_hyperplaneSection sX hklt hB (by omega) φ hφ
  obtain ⟨U₂, hU₂, h₂⟩ := exists_dense_open_cutMap sX i hEr φ hφ ν hν V hV
  obtain ⟨U₃, hU₃, h₃⟩ := exists_dense_open_topologicalKrullDim_fibre sX f s
    (isClosed_singleton_of_range_subset f hf i hEs) hfib φ
  obtain ⟨U₄, hU₄, h₄⟩ := exists_dense_open_canonicalSheaf_adjunction sX i hEr φ hφ ν hν
  refine ⟨U₁ ⊓ U₂ ⊓ U₃ ⊓ U₄, ?_, fun c₀ hc₀ hmem => ?_⟩
  · simp only [TopologicalSpace.Opens.coe_inf]
    exact ((hU₁.inter_of_isOpen_left hU₂ U₁.isOpen).inter_of_isOpen_left hU₃
      (U₁.isOpen.inter U₂.isOpen)).inter_of_isOpen_left hU₄
      ((U₁.isOpen.inter U₂.isOpen).inter U₃.isOpen)
  haveI := isFinite_cutMap ν (i ≫ φ) c₀
  rw [TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_inf,
    TopologicalSpace.Opens.mem_inf] at hmem
  obtain ⟨⟨⟨hm₁, hm₂⟩, hm₃⟩, hm₄⟩ := hmem
  obtain ⟨hint, hln, hnorm, hproj, K₁, B₁, hklt₁, hB₁, hadjK⟩ := h₁ c₀ hc₀ hm₁
  obtain ⟨hE₁, hEν₁, hEν₁n, hiso, hdimE₁, hbir, hdimV⟩ := h₂ c₀ hc₀ hm₂
  have hfib₁ := h₃ c₀ hc₀ hm₃
  obtain ⟨hsm, hadjω⟩ := h₄ c₀ hc₀ hm₄
  have hle : hyperplaneSection φ c₀ ≤ (hyperplaneSection (i ≫ φ) c₀).map i := by
    rw [hyperplaneSection_comp]
    exact Scheme.IdealSheafData.le_map_comap _ _
  let i₁ := Scheme.IdealSheafData.subschemeMap (hyperplaneSection (i ≫ φ) c₀)
    (hyperplaneSection φ c₀) i hle
  have hi₁ : i₁ ≫ (hyperplaneSection φ c₀).subschemeι =
      (hyperplaneSection (i ≫ φ) c₀).subschemeι ≫ i :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  haveI : IsClosedImmersion i₁ := by
    haveI : IsClosedImmersion (i₁ ≫ (hyperplaneSection φ c₀).subschemeι) := by
      rw [hi₁]; infer_instance
    exact IsClosedImmersion.of_comp _ (hyperplaneSection φ c₀).subschemeι
  have hstr : cutMap ν (i ≫ φ) c₀ ≫ i₁ ≫ (hyperplaneSection φ c₀).subschemeι ≫ sX =
      (hyperplaneSection (ν ≫ i ≫ φ) c₀).subschemeι ≫ ν ≫ i ≫ sX := by
    rw [reassoc_of% hi₁, cutMap_subschemeι_assoc]
  refine ⟨_, (hyperplaneSection φ c₀).subschemeι, inferInstance, hint, hln, hnorm, hproj, K₁, B₁,
    hklt₁, i₁, inferInstance, hE₁, hEν₁, hEν₁n, hiso, hB₁, hi₁, ?_, hdimE₁, hfib₁, hbir, hdimV,
    (Scheme.Modules.pullback φ).obj (twistOne k N), inferInstance, ?_, ?_, hadjK⟩
  · rintro _ ⟨x, rfl⟩
    rw [Set.mem_preimage, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply i₁, hi₁,
      Scheme.Hom.comp_apply]
    exact hEs ⟨_, rfl⟩
  · rw [hstr]
    exact hsm
  · rw [hstr]
    exact hadjω

/-- **Cutting by one general hyperplane.** For a general hyperplane `H = V(c₀)`, the section
`X₁ = X ∩ H` carries a klt pair `(X₁, B₁)` with `B₁ ≥ 0`, the cut `E₁ = E ∩ H` is a component of
the fibre of `X₁ ⟶ S` of dimension one less, its preimage `Eᵛ₁ = Eᵛ ∩ H` is a normal finite
birational model of `E₁`, and weak subadjunction along a closed subscheme `V(A) ∩ E₁` of `E₁`
implies it along `V(H ⊔ A)` in `E`. -/
private theorem exists_dense_open_cut (m : ℕ) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f) (s : S)
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E]
    (hEs : Set.range i ⊆ f ⁻¹' {s}) (hmn : m + 3 ≤ n)
    (hEr : topologicalKrullDim E = (m + 2 : ℕ))
    (hfib : topologicalKrullDim (f ⁻¹' {s}) ≤ (m + 2 : ℕ))
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX)
    {Eν : Scheme.{0}} (ν : Eν ⟶ E) [IsFinite ν] [IsIntegral Eν] [IsNormal Eν]
    (hν : IsBirational ν) (V : E.Opens) [IsIso (ν ∣_ V)]
    (hV : topologicalKrullDim ↥((V : Set E)ᶜ) ≤ (m + 1 : ℕ)) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c₀ : Fin (N + 1) → k) (hc₀ : c₀ ≠ 0), dualPoint c₀ hc₀ ∈ U →
      haveI := isFinite_cutMap ν (i ≫ φ) c₀
      ∃ (X₁ : Scheme.{0}) (ι : X₁ ⟶ X) (h₁ : IsClosedImmersion ι) (h₂ : IsIntegral X₁)
        (h₃ : IsLocallyNoetherian X₁) (h₄ : IsNormal X₁)
        (h₅ : AlgebraicGeometry.IsProjectiveVariety k (ι ≫ sX))
        (K₁ : Divisor X₁) (B₁ : QDivisor X₁) (hklt₁ : MMP.Mori.IsKltPair (ι ≫ sX) (n - 1) K₁ B₁)
        (i₁ : (hyperplaneSection (i ≫ φ) c₀).subscheme ⟶ X₁) (h₆ : IsClosedImmersion i₁)
        (h₇ : IsIntegral (hyperplaneSection (i ≫ φ) c₀).subscheme)
        (h₈ : IsIntegral (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme)
        (h₉ : IsNormal (hyperplaneSection (ν ≫ i ≫ φ) c₀).subscheme)
        (h₁₀ : IsIso (cutMap ν (i ≫ φ) c₀ ∣_
            ((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V))),
        0 ≤ B₁ ∧ i₁ ≫ ι = (hyperplaneSection (i ≫ φ) c₀).subschemeι ≫ i ∧
        Set.range i₁ ⊆ (ι ≫ f) ⁻¹' {s} ∧
        topologicalKrullDim (hyperplaneSection (i ≫ φ) c₀).subscheme = (m + 1 : ℕ) ∧
        topologicalKrullDim ((ι ≫ f) ⁻¹' {s}) ≤ (m + 1 : ℕ) ∧
        IsBirational (cutMap ν (i ≫ φ) c₀) ∧
        topologicalKrullDim ↥((((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V :
          TopologicalSpace.Opens _) : Set (hyperplaneSection (i ≫ φ) c₀).subscheme)ᶜ) ≤ (m : ℕ) ∧
        ∀ A : E.IdealSheafData,
          (((A.comap (hyperplaneSection (i ≫ φ) c₀).subschemeι).subschemeι ⁻¹'
            (((hyperplaneSection (i ≫ φ) c₀).subschemeι ⁻¹ᵁ V : TopologicalSpace.Opens _) :
              Set (hyperplaneSection (i ≫ φ) c₀).subscheme)ᶜ)).Finite →
          SubadjunctionAt (ι ≫ sX) i₁ (cutMap ν (i ≫ φ) c₀) (m + 1)
            (A.comap (hyperplaneSection (i ≫ φ) c₀).subschemeι) hklt₁.1.2.2 →
          (((hyperplaneSection (i ≫ φ) c₀ ⊔ A).subschemeι ⁻¹' (V : Set E)ᶜ)).Finite ∧
          SubadjunctionAt sX i ν (m + 2) (hyperplaneSection (i ≫ φ) c₀ ⊔ A) hklt.1.2.2 := by
  obtain ⟨U, hU, hcut⟩ := exists_dense_open_cut_data m sX hklt hB sS f hfs hf s i hEs hmn hEr hfib
    φ hφ ν hν V hV
  refine ⟨U, hU, fun c₀ hc₀ hmem => ?_⟩
  haveI := isFinite_cutMap ν (i ≫ φ) c₀
  obtain ⟨X₁, ι, h₁, h₂, h₃, h₄, h₅, K₁, B₁, hklt₁, i₁, h₆, h₇, h₈, h₉, h₁₀, hB₁, hi₁, hEs₁,
    hEr₁, hfib₁, hbir₁, hV₁, L, hL, hsm, hadjω, hadjK⟩ := hcut c₀ hc₀ hmem
  refine ⟨X₁, ι, h₁, h₂, h₃, h₄, h₅, K₁, B₁, hklt₁, i₁, h₆, h₇, h₈, h₉, h₁₀, hB₁, hi₁, hEs₁,
    hEr₁, hfib₁, hbir₁, hV₁, fun A hfinA hA => ?_⟩
  -- `C = V(H ⊔ A)` is `V(A) ∩ H` read in `E`
  have hfin : ((hyperplaneSection (i ≫ φ) c₀ ⊔ A).subschemeι ⁻¹' (V : Set E)ᶜ).Finite := by
    refine ((hfinA.image (comapSubschemeιIso (hyperplaneSection (i ≫ φ) c₀) A).hom).subset ?_)
    intro x hx
    refine ⟨(comapSubschemeιIso (hyperplaneSection (i ≫ φ) c₀) A).inv x, ?_, ?_⟩
    · change (((comapSubschemeιIso (hyperplaneSection (i ≫ φ) c₀) A).inv ≫
        (A.comap (hyperplaneSection (i ≫ φ) c₀).subschemeι).subschemeι) ≫
          (hyperplaneSection (i ≫ φ) c₀).subschemeι) x ∉ (V : Set E)
      rw [Category.assoc, ← comapSubschemeιIso_hom_subschemeι, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]
      exact hx
    · change ((comapSubschemeιIso (hyperplaneSection (i ≫ φ) c₀) A).inv ≫
        (comapSubschemeιIso (hyperplaneSection (i ≫ φ) c₀) A).hom) x = x
      rw [Iso.inv_hom_id]
      rfl
  exact ⟨hfin, subadjunctionAt_sup_of_subadjunctionAt_comap sX i ν hklt.1.2.2 ι hklt₁.1.2.2
    (hyperplaneSection (i ≫ φ) c₀) i₁ hi₁ _ (hyperplaneSection_comp ν (i ≫ φ) c₀)
    (cutMap ν (i ≫ φ) c₀) (cutMap_subschemeι _ _ _) L hsm hadjω hadjK A
    (fun h => degreeOn_comap_eq_of_finite sX i ν V h hfin L) hA⟩

/-- The preimage of `V(A) ∩ H` in a cut `Hᵛ = ν⁻¹(H)` is the preimage of `V(H ⊔ A)` in `Eᵛ`. -/
private theorem nonempty_comapCutIso {E Eν : Scheme.{0}} (ν : Eν ⟶ E) (H A : E.IdealSheafData)
    (Hν : Eν.IdealSheafData) (hHν : Hν = H.comap ν) (ν₁ : Hν.subscheme ⟶ H.subscheme)
    (hν₁ : ν₁ ≫ H.subschemeι = Hν.subschemeι ≫ ν) :
    Nonempty (((A.comap H.subschemeι).comap ν₁).subscheme ≅ ((H ⊔ A).comap ν).subscheme) := by
  subst hHν
  exact ⟨subschemeIsoOfEq (by rw [← Scheme.IdealSheafData.comap_comp, hν₁,
      Scheme.IdealSheafData.comap_comp]) ≪≫
    comapSubschemeιIso (H.comap ν) (A.comap ν) ≪≫
    subschemeIsoOfEq (Scheme.IdealSheafData.comap_sup _ _ _).symm⟩

/-- **Weak subadjunction at some general complete intersection.** For every nonzero polynomial
`Q` in the coefficients of `m` hyperplanes there is a tuple `c` with `Q(c) ≠ 0` such that the weak
subadjunction inequality holds along `C_c = E ∩ H_{c₁} ∩ ⋯ ∩ H_{c_m}`, for any normal finite
birational model `ν : Eᵛ ⟶ E` of the `(m + 1)`-dimensional component `E`, and `C_c` meets the
complement of an open `V` over which `ν` is an isomorphism in finitely many points. -/
private theorem exists_eval_ne_zero_subadjunctionAt (m : ℕ) :
    ∀ {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (_hB : 0 ≤ B)
    {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (f : X ⟶ S) (_hfs : f ≫ sS = sX) (_hf : IsProjectiveMorphism f) (s : S)
    (_hs : IsClosed ({s} : Set S))
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E]
    (_hEs : Set.range i ⊆ f ⁻¹' {s}) (_hmn : m + 2 ≤ n)
    (_hEr : topologicalKrullDim E = (m + 1 : ℕ))
    (_hfib : topologicalKrullDim (f ⁻¹' {s}) ≤ (m + 1 : ℕ))
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ]
    (_hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX)
    {Eν : Scheme.{0}} (ν : Eν ⟶ E) [IsFinite ν] [IsIntegral Eν] [IsNormal Eν]
    (_hν : IsBirational ν) (V : E.Opens) [IsIso (ν ∣_ V)]
    (_hV : topologicalKrullDim ↥((V : Set E)ᶜ) ≤ (m : ℕ))
    (Q : MvPolynomial (Fin m × Fin (N + 1)) k), Q ≠ 0 →
    ∃ c : Fin m → Fin (N + 1) → k, MvPolynomial.eval (fun p => c p.1 p.2) Q ≠ 0 ∧
      (((⨆ j, hyperplaneSection (i ≫ φ) (c j)).subschemeι ⁻¹' (V : Set E)ᶜ)).Finite ∧
      SubadjunctionAt sX i ν (m + 1) (⨆ j, hyperplaneSection (i ≫ φ) (c j)) hklt.1.2.2 ∧
      IsIntegral (⨆ j, hyperplaneSection (i ≫ φ) (c j)).subscheme ∧
      IsIntegral ((⨆ j, hyperplaneSection (i ≫ φ) (c j)).comap ν).subscheme ∧
      IsNormal ((⨆ j, hyperplaneSection (i ≫ φ) (c j)).comap ν).subscheme := by
  induction m with
  | zero =>
    intro k _ _ _ X _ _ _ sX _ n K B hklt hB S sS _ f hfs hf s hs E i _ _ hEs hmn hEr hfib N φ _
      hφ Eν ν _ _ _ hν V _ hV Q hQ
    have hbot : (⨆ j : Fin 0, hyperplaneSection (i ≫ φ) ((fun j => j.elim0) j)) = ⊥ :=
      iSup_of_empty _
    refine ⟨fun j => j.elim0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [MvPolynomial.eq_C_of_isEmpty Q] at hQ ⊢
      rw [MvPolynomial.eval_C]
      exact fun h => hQ (by rw [h, map_zero])
    · rw [hbot]
      haveI : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
      haveI : CompactSpace E := QuasiCompact.compactSpace_of_compactSpace (i ≫ sX)
      haveI : IsNoetherian E := {}
      haveI := finite_of_topologicalKrullDim_nonpos (Z := ↥((V : Set E)ᶜ)) (by exact_mod_cast hV)
      exact (Set.toFinite _).preimage
        (Scheme.IdealSheafData.subschemeι (⊥ : E.IdealSheafData)).isEmbedding.injective.injOn
    · have hbot : (⨆ j : Fin 0, hyperplaneSection (i ≫ φ) ((fun j => j.elim0) j)) = ⊥ :=
        iSup_of_empty _
      rw [hbot]
      exact subadjunctionAt_bot sX hklt hB sS f hfs hf s hs i hEs hfib ν hν
    · rw [hbot]
      haveI : IsIso (⊥ : E.IdealSheafData).subschemeι := inferInstance
      exact IsIntegral.of_isIso (inv (⊥ : E.IdealSheafData).subschemeι)
    · rw [hbot, Scheme.IdealSheafData.comap_bot]
      haveI : IsIso (⊥ : Eν.IdealSheafData).subschemeι := inferInstance
      exact IsIntegral.of_isIso (inv (⊥ : Eν.IdealSheafData).subschemeι)
    · rw [hbot, Scheme.IdealSheafData.comap_bot]
      exact isNormal_of_isOpenImmersion (⊥ : Eν.IdealSheafData).subschemeι
  | succ m ih =>
    intro k _ _ _ X _ _ _ sX _ n K B hklt hB S sS _ f hfs hf s hs E i _ _ hEs hmn hEr hfib N φ _
      hφ Eν ν _ _ _ hν V _ hV Q hQ
    obtain ⟨U, hU, hcut⟩ := exists_dense_open_cut m sX hklt hB sS f hfs hf s i hEs hmn hEr hfib φ
      hφ ν hν V hV
    obtain ⟨R, hR0, hR⟩ := exists_specialize_ne_zero Q hQ
    obtain ⟨c₀, hc₀, hc₀U, hc₀R⟩ := exists_dualPoint_mem_of_dense U hU R hR0
    obtain ⟨Q₀, hQ₀, hQ₀Q⟩ := hR c₀ hc₀R
    haveI := isFinite_cutMap ν (i ≫ φ) c₀
    obtain ⟨X₁, ι, _, _, _, _, _, K₁, B₁, hklt₁, i₁, _, _, _, _, _, hB₁, hi₁, hEs₁, hEr₁, hfib₁,
      hν₁, hV₁, htransfer⟩ := hcut c₀ hc₀ hc₀U
    obtain ⟨c', hc'Q, hc'fin, hc'sub, hc'int, hc'intν, hc'norm⟩ := ih (ι ≫ sX) hklt₁ hB₁ sS (ι ≫ f)
      (by rw [Category.assoc, hfs]) (isProjectiveMorphism_comp_isClosedImmersion ι f hf) s hs i₁
      hEs₁ (by omega) hEr₁ hfib₁ (ι ≫ φ) (by rw [Category.assoc, hφ]) _ hν₁ _ hV₁ Q₀ hQ₀
    set A := ⨆ j, hyperplaneSection (i ≫ φ) (c' j) with hAdef
    have hA : A.comap (hyperplaneSection (i ≫ φ) c₀).subschemeι =
        ⨆ j, hyperplaneSection (i₁ ≫ ι ≫ φ) (c' j) := by
      rw [hAdef, (Scheme.IdealSheafData.map_gc _).l_iSup]
      refine iSup_congr fun j => ?_
      rw [← hyperplaneSection_comp, ← Category.assoc, ← hi₁, Category.assoc]
    have hIC : (⨆ j, hyperplaneSection (i ≫ φ)
        ((Fin.cons c₀ c' : Fin (m + 1) → Fin (N + 1) → k) j)) =
        hyperplaneSection (i ≫ φ) c₀ ⊔ A := by
      rw [iSup_fin_succ']; simp [hAdef]
    rw [← hA] at hc'fin hc'sub hc'int hc'intν hc'norm
    obtain ⟨hfin, hsub⟩ := htransfer A hc'fin hc'sub
    obtain ⟨eν⟩ := nonempty_comapCutIso ν (hyperplaneSection (i ≫ φ) c₀) A _
      (hyperplaneSection_comp ν (i ≫ φ) c₀) (cutMap ν (i ≫ φ) c₀) (cutMap_subschemeι _ _ _)
    refine ⟨Fin.cons c₀ c', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hQ₀Q]; exact hc'Q
    · rw [hIC]; exact hfin
    · rw [hIC]; exact hsub
    · rw [hIC]
      exact IsIntegral.of_isIso (comapSubschemeιIso (hyperplaneSection (i ≫ φ) c₀) A).hom
    · rw [hIC]
      exact IsIntegral.of_isIso eν.hom
    · rw [hIC]
      exact isNormal_of_isOpenImmersion eν.inv

/-- The normalization of an `(m + 1)`-dimensional variety is an isomorphism over an open subset
whose complement has dimension at most `m`. -/
private theorem exists_opens_isIso_morphismRestrict_normalizationOverField {k : Type} [Field k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E] {m : ℕ}
    (hEr : topologicalKrullDim E = (m + 1 : ℕ)) :
    ∃ (V : E.Opens) (_hV : IsIso (normalizationOverField k (i ≫ sX) ∣_ V)),
      topologicalKrullDim ↥((V : Set E)ᶜ) ≤ (m : ℕ) := by
  haveI : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  haveI : CompactSpace E := QuasiCompact.compactSpace_of_compactSpace (i ≫ sX)
  haveI : IsNoetherian E := {}
  let V : E.Opens :=
    ⟨regularLocus E, MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (i ≫ sX)⟩
  refine ⟨V, isIso_morphismRestrict_normalization_of_subset_regularLocus _ V le_rfl, ?_⟩
  -- the generic point is regular, so `V ≠ ∅` and its complement is a proper closed subset
  have hη : genericPoint E ∈ (V : Set E) :=
    MMP.Flips.isRegularLocalRing_stalk_of_coheight_eq_zero (Order.coheight_eq_zero.2
      fun y _ => (genericPoint_spec E).specializes (Set.mem_univ y))
  have hle := Topology.topologicalKrullDim_add_one_le_of_ne_univ (S := (V : Set E)ᶜ)
    V.isOpen.isClosed_compl (fun h => (h ▸ Set.mem_univ (genericPoint E) :
      genericPoint E ∈ (V : Set E)ᶜ) hη)
  rw [hEr] at hle
  exact withBot_le_natCast_of_add_one_le hle

/-! ### The universal complete intersection over the space of coefficient tuples -/

section UniversalFamily

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule baseRingHom)

attribute [local instance] globalSectionsModule

variable {k : Type} [Field k] {N : ℕ} {Y : Scheme.{0}} [Y.Over (Spec (.of k))]
  (ψ : Y ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) (ι : Type) [Fintype ι]

/-- The coordinate section `Tᵢ` of `𝒪(1)`. -/
private noncomputable def coordSection (i : Fin (N + 1)) : Γ(twistOne k N, ⊤) :=
  formSection ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩

/-- The `j`-th universal section `∑ᵢ x_{ji} ψ^*Tᵢ` on `𝔸^{ι × (N+1)}_Y`. -/
private noncomputable def univSection (j : ι) :
    Γ((Scheme.Modules.pullback ((𝔸(ι × Fin (N + 1); Y) ↘ Y) ≫ ψ)).obj (twistOne k N), ⊤) :=
  ∑ i, AffineSpace.coord Y (j, i) •
    pullbackGlobalSections ((𝔸(ι × Fin (N + 1); Y) ↘ Y) ≫ ψ) (twistOne k N) (coordSection i)

/-- The universal complete intersection. -/
private noncomputable def univFamily : (𝔸(ι × Fin (N + 1); Y)).IdealSheafData :=
  ⨆ j, Stacks.Divisors.zeroScheme _ _ (univSection (ψ := ψ) (ι := ι) j)

variable {ψ ι}

/-- The section `Y ⟶ 𝔸_Y` at the coefficient tuple `c`. -/
private noncomputable def pointSection (c : ι → Fin (N + 1) → k) : Y ⟶ 𝔸(ι × Fin (N + 1); Y) :=
  AffineSpace.homOfVector (𝟙 Y) (fun p => baseRingHom k Y (c p.1 p.2))

/-- The `k`-point of `𝔸_k` with coordinates `c`. -/
private noncomputable def parameterPoint (c : ι → Fin (N + 1) → k) :
    Spec (.of k) ⟶ 𝔸(ι × Fin (N + 1); Spec (.of k)) :=
  AffineSpace.homOfVector (𝟙 _) (fun p => (Scheme.ΓSpecIso (.of k)).inv (c p.1 p.2))

private theorem comap_univFamily_pointSection
    (hψ : ψ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = Y ↘ Spec (.of k))
    (c : ι → Fin (N + 1) → k) :
    (univFamily (ψ := ψ) (ι := ι)).comap (pointSection c) = ⨆ j, hyperplaneSection ψ (c j) := by
  rw [univFamily, (Scheme.IdealSheafData.map_gc _).l_iSup]
  refine iSup_congr fun j => ?_
  rw [← zeroScheme_pulledSystem hψ (c j), systemSection_apply]
  exact (Stacks.Bertini.zeroScheme_sum_smul_comap (twistOne k N)
    ((𝔸(ι × Fin (N + 1); Y) ↘ Y) ≫ ψ) (pointSection c) ψ
    (by rw [pointSection, ← Category.assoc, AffineSpace.homOfVector_over, Category.id_comp])
    (fun i => AffineSpace.coord Y (j, i)) (fun i => baseRingHom k Y (c j i))
    (fun i => AffineSpace.homOfVector_appTop_coord _ _ _) coordSection).symm

private theorem isPullback_pointSection (c : ι → Fin (N + 1) → k) :
    IsPullback (pointSection c) (Y ↘ Spec (.of k))
      (AffineSpace.map (ι × Fin (N + 1)) (Y ↘ Spec (.of k))) (parameterPoint c) := by
  have hY : pointSection c ≫ (𝔸(ι × Fin (N + 1); Y) ↘ Y) = 𝟙 Y :=
    AffineSpace.homOfVector_over _ _
  have hk : parameterPoint c ≫ (𝔸(ι × Fin (N + 1); Spec (.of k)) ↘ Spec (.of k)) = 𝟙 _ :=
    AffineSpace.homOfVector_over _ _
  have hcomm : pointSection c ≫ AffineSpace.map _ (Y ↘ Spec (.of k)) =
      (Y ↘ Spec (.of k)) ≫ parameterPoint c := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, hY, Category.id_comp,
        Category.assoc, hk, Category.comp_id]
    · intro p
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        CommRingCat.comp_apply, AffineSpace.map_appTop_coord, pointSection, parameterPoint,
        AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord]
      rfl
  refine IsPullback.of_right ?_ hcomm (AffineSpace.isPullback_map (n := ι × Fin (N + 1)) (Y ↘ Spec (.of k))).flip
  rw [hY, hk]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

private theorem isPullback_comap_pointSection (I : (𝔸(ι × Fin (N + 1); Y)).IdealSheafData)
    (c : ι → Fin (N + 1) → k) :
    IsPullback ((I.comapIso (pointSection c)).hom ≫ Limits.pullback.snd _ _)
      ((I.comap (pointSection c)).subschemeι ≫ (Y ↘ Spec (.of k)))
      (I.subschemeι ≫ AffineSpace.map _ (Y ↘ Spec (.of k))) (parameterPoint c) := by
  have w₁ : (I.comapIso (pointSection c)).hom ≫ Limits.pullback.fst (pointSection c) I.subschemeι =
      (I.comap (pointSection c)).subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_inv_subschemeι, Iso.hom_inv_id_assoc]
  have h₁ : IsPullback (I.comap (pointSection c)).subschemeι
      ((I.comapIso (pointSection c)).hom ≫ Limits.pullback.snd _ _) (pointSection c) I.subschemeι :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
      w₁]⟩ (I.comapIso _) w₁ rfl
  exact h₁.flip.paste_vert (isPullback_pointSection c)

end UniversalFamily

/-- **The universal complete intersection.** For a proper `k`-scheme `Y` with
`ψ : Y ⟶ ℙᴺ_k` there is a proper family `f : 𝒞 ⟶ 𝔸^{ι × (N+1)}_k` with a morphism `π : 𝒞 ⟶ Y`,
whose fibre over the `k`-point of a tuple `c` is `ψ⁻¹(H_{c₁} ∩ ⋯)`, sitting in `𝒞` over `Y`. -/
private theorem exists_univFamily {k : Type} [Field k] {N : ℕ} {Y : Scheme.{0}}
    [Y.Over (Spec (.of k))] [IsProper (Y ↘ Spec (.of k))] (ψ : Y ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    (hψ : ψ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = Y ↘ Spec (.of k))
    (ι : Type) [Fintype ι] :
    ∃ (𝒞 : Scheme.{0}) (f : 𝒞 ⟶ 𝔸(ι × Fin (N + 1); Spec (.of k))) (_ : IsProper f)
      (π : 𝒞 ⟶ Y), ∀ c : ι → Fin (N + 1) → k,
        ∃ q : (⨆ j, hyperplaneSection ψ (c j)).subscheme ⟶ 𝒞,
          q ≫ π = (⨆ j, hyperplaneSection ψ (c j)).subschemeι ∧
          IsPullback q ((⨆ j, hyperplaneSection ψ (c j)).subschemeι ≫ (Y ↘ Spec (.of k))) f
            (AffineSpace.homOfVector (𝟙 _)
              (fun p => (Scheme.ΓSpecIso (.of k)).inv (c p.1 p.2))) := by
  haveI : IsProper (AffineSpace.map (ι × Fin (N + 1)) (Y ↘ Spec (.of k))) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (AffineSpace.isPullback_map (n := ι × Fin (N + 1)) (Y ↘ Spec (.of k))).flip inferInstance
  set I := univFamily (ψ := ψ) (ι := ι) with hI
  refine ⟨I.subscheme, I.subschemeι ≫ AffineSpace.map _ (Y ↘ Spec (.of k)), inferInstance,
    I.subschemeι ≫ (𝔸(ι × Fin (N + 1); Y) ↘ Y), fun c => ?_⟩
  have key : ∀ J : Y.IdealSheafData, I.comap (pointSection c) = J →
      ∃ q : J.subscheme ⟶ I.subscheme,
        q ≫ I.subschemeι ≫ (𝔸(ι × Fin (N + 1); Y) ↘ Y) = J.subschemeι ∧
        IsPullback q (J.subschemeι ≫ (Y ↘ Spec (.of k)))
          (I.subschemeι ≫ AffineSpace.map _ (Y ↘ Spec (.of k))) (parameterPoint c) := by
    rintro J rfl
    refine ⟨_, ?_, isPullback_comap_pointSection I c⟩
    have w₁ : (I.comapIso (pointSection c)).hom ≫
        Limits.pullback.fst (pointSection c) I.subschemeι =
        (I.comap (pointSection c)).subschemeι := by
      rw [← Scheme.IdealSheafData.comapIso_inv_subschemeι, Iso.hom_inv_id_assoc]
    simp only [Category.assoc]
    rw [← Limits.pullback.condition_assoc, reassoc_of% w₁, pointSection,
      AffineSpace.homOfVector_over, Category.comp_id]
  exact key _ (comap_univFamily_pointSection hψ c)

/-! ### Spreading fibrewise properties over the space of coefficient tuples -/

/-- A point of a pullback square: points of the two corners over the same point of the base come
from a point of the pullback. -/
private theorem exists_eq_of_isPullback {W X Y Z : Scheme.{0}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y) (hxy : f x = g y) :
    ∃ w : W, fst w = x ∧ snd w = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz₁]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz₂]

/-- A fibre square over a point landing in an open `U` of the base restricts to `f ∣_ U`. -/
private theorem exists_isPullback_morphismRestrict {X S C P : Scheme.{0}} {f : X ⟶ S}
    (U : S.Opens) {q : C ⟶ X} {g : C ⟶ P} {x : P ⟶ S} (h : IsPullback q g f x)
    (hx : Set.range x ⊆ Set.range U.ι) :
    ∃ q' : C ⟶ (f ⁻¹ᵁ U).toScheme, q' ≫ (f ⁻¹ᵁ U).ι = q ∧
      IsPullback q' g (f ∣_ U) (IsOpenImmersion.lift U.ι x hx) := by
  have hq : Set.range q ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (q y) ∈ U
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    have := hx ⟨g y, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  refine ⟨IsOpenImmersion.lift _ q hq, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict f U).flip
  · rw [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac]; exact h
  · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      IsOpenImmersion.lift_fac, Category.assoc, IsOpenImmersion.lift_fac, h.w]

/-- **A nonempty open of `𝔸ⁿ_k` contains the `k`-points off a hypersurface**: there is a nonzero
polynomial `P` such that the `k`-point with coordinates `a` lies in the open whenever
`P(a) ≠ 0`. -/
private theorem exists_polynomial_homOfVector_mem {k : Type} [Field k] {n : Type}
    (U : (𝔸(n; Spec (.of k))).Opens) (hU : (U : Set (𝔸(n; Spec (.of k)))).Nonempty) :
    ∃ P : MvPolynomial n k, P ≠ 0 ∧ ∀ a : n → k, MvPolynomial.eval a P ≠ 0 →
      ∀ p : Spec (.of k), AffineSpace.homOfVector (𝟙 (Spec (.of k)))
        (fun q => (Scheme.ΓSpecIso (.of k)).inv (a q)) p ∈ U := by
  classical
  obtain ⟨p₀, hp₀⟩ := hU
  obtain ⟨-, ⟨-, ⟨G, rfl⟩, rfl⟩, hp₀G, hGU⟩ :=
    (isBasis_basicOpen (𝔸(n; Spec (.of k)))).exists_subset_of_mem_open hp₀ U.isOpen
  have hG0 : G ≠ 0 := by
    rintro rfl
    simp at hp₀G
  set e := Scheme.ΓSpecIso (CommRingCat.of k)
  set P : MvPolynomial n k :=
    MvPolynomial.map e.hom.hom ((AffineSpace.ΓIso n (Spec (.of k))).hom G) with hP
  have hPG : (AffineSpace.ΓIso n (Spec (.of k))).inv (MvPolynomial.map e.inv.hom P) = G := by
    rw [hP, MvPolynomial.map_map]
    have : e.inv.hom.comp e.hom.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, e.hom_inv_id]; rfl
    rw [this, MvPolynomial.map_id, ← CommRingCat.comp_apply, Iso.hom_inv_id]
    rfl
  have hP0 : P ≠ 0 := by
    intro h0
    apply hG0
    rw [← hPG, h0, map_zero, map_zero]
  refine ⟨P, hP0, fun a ha p => ?_⟩
  apply hGU
  have hval := AffineSpace.homOfVector_appTop_ΓIso_inv_map a P
  rw [hPG] at hval
  change p ∈ _ ⁻¹ᵁ (𝔸(n; Spec (.of k))).basicOpen G
  rw [Scheme.preimage_basicOpen_top, hval, Scheme.basicOpen_of_isUnit]
  · exact TopologicalSpace.Opens.mem_top p
  · exact IsUnit.map e.inv.hom (isUnit_iff_ne_zero.mpr ha)

open ProperFlatFibreEulerCharacteristic in
/-- **The Euler characteristic of the fibres of a proper flat family over a connected base is
constant** ([Stacks, Tag 0BDJ] with [Stacks, Tag 0B91]): the fibres over two `k`-points have the
same `χ` of the restriction of a flat module of finite presentation. -/
private theorem eulerSum_eq_of_isPullback {k : Type} [Field k] {S X : Scheme.{0}}
    [PreconnectedSpace S] (f : X ⟶ S) [IsProper f] (hfp : FinitePresentation f) (M : X.Modules)
    (hM : M.IsFinitePresentation) (hflat : IsFlatOver f.toLRSHom.toShHom M)
    {Z₁ Z₂ : Scheme.{0}} (x₁ x₂ : Spec (.of k) ⟶ S) (q₁ : Z₁ ⟶ X) (g₁ : Z₁ ⟶ Spec (.of k))
    (sq₁ : IsPullback q₁ g₁ f x₁) (q₂ : Z₂ ⟶ X) (g₂ : Z₂ ⟶ Spec (.of k))
    (sq₂ : IsPullback q₂ g₂ f x₂) :
    eulerSum k g₁ ((Scheme.Modules.pullback q₁).obj M) =
      eulerSum k g₂ ((Scheme.Modules.pullback q₂).obj M) := by
  have h₁ := chiDerivedFibre_eq_eulerSum f hfp M hM hflat k x₁ q₁ g₁ sq₁
    (IsLocalRing.closedPoint k)
  have h₂ := chiDerivedFibre_eq_eulerSum f hfp M hM hflat k x₂ q₂ g₂ sq₂
    (IsLocalRing.closedPoint k)
  have hc := DerivedFibreBetti.isLocallyConstant_chiDerivedFibre S _
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward f hfp inferInstance M
      hM hflat)
  rw [← h₁, ← h₂]
  exact hc.apply_eq_of_preconnectedSpace _ _

open ProperFlatFibreEulerCharacteristic in
/-- **Euler characteristics are constant on general fibres.** Let `j : S ⟶ 𝔸ⁿ_k` be an open
immersion of an integral scheme and `f : X ⟶ S` proper. For a quasi-coherent module `M` of finite
type on `X` there is a nonzero polynomial `P` such that, at all `k`-points `x, x'` of `S` over
coordinate tuples `a, a'` with `P(a), P(a') ≠ 0`, the fibres of `f` have the same `χ` of `M`. -/
private theorem exists_polynomial_eulerSum_eq {k : Type} [Field k] {n : Type} {S X : Scheme.{0}}
    [IsIntegral S] (j : S ⟶ 𝔸(n; Spec (.of k))) [IsOpenImmersion j] (f : X ⟶ S) [IsProper f]
    [LocallyOfFiniteType f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ P : MvPolynomial n k, P ≠ 0 ∧
      (∀ a : n → k, MvPolynomial.eval a P ≠ 0 → Set.range (AffineSpace.homOfVector
        (𝟙 (Spec (.of k))) (fun q => (Scheme.ΓSpecIso (.of k)).inv (a q))) ⊆ Set.range j) ∧
      ∀ (a a' : n → k), MvPolynomial.eval a P ≠ 0 → MvPolynomial.eval a' P ≠ 0 →
      ∀ (x x' : Spec (.of k) ⟶ S),
        x ≫ j = AffineSpace.homOfVector (𝟙 _) (fun q => (Scheme.ΓSpecIso (.of k)).inv (a q)) →
        x' ≫ j = AffineSpace.homOfVector (𝟙 _) (fun q => (Scheme.ΓSpecIso (.of k)).inv (a' q)) →
      ∀ {Z Z' : Scheme.{0}} (q : Z ⟶ X) (g : Z ⟶ Spec (.of k)) (q' : Z' ⟶ X)
        (g' : Z' ⟶ Spec (.of k)), IsPullback q g f x → IsPullback q' g' f x' →
        eulerSum k g ((Scheme.Modules.pullback q).obj M) =
          eulerSum k g' ((Scheme.Modules.pullback q').obj M) := by
  obtain ⟨U, hUd, hflat, hfp, hMflat, hMfp⟩ :=
    exists_dense_open_flat_finitePresentation_of_isIntegral f M
  have hf₁ := Scheme.Hom.resLE_eq_morphismRestrict (f := f) (U := U)
  haveI : IsProper (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by rw [hf₁]; infer_instance
  have hUne : (U : Set S).Nonempty := hUd.nonempty
  haveI : Nonempty U := hUne.to_subtype
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_homOfVector_mem (j ''ᵁ U)
    (hUne.image _)
  -- a `k`-point of `S` over such a tuple lands in `U`
  have hland : ∀ (a : n → k), MvPolynomial.eval a P ≠ 0 → ∀ (x : Spec (.of k) ⟶ S),
      x ≫ j = AffineSpace.homOfVector (𝟙 _) (fun q => (Scheme.ΓSpecIso (.of k)).inv (a q)) →
      Set.range x ⊆ Set.range U.ι := by
    rintro a ha x hx _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨y, hyU, hy⟩ := hP a ha p
    rw [← hx, Scheme.Hom.comp_apply] at hy
    exact j.isOpenEmbedding.injective hy ▸ hyU
  refine ⟨P, hP0, fun a ha => ?_, fun a a' ha ha' x x' hx hx' Z Z' q g q' g' sq sq' => ?_⟩
  · rintro _ ⟨p, rfl⟩
    obtain ⟨y, -, hy⟩ := hP a ha p
    exact ⟨y, hy⟩
  obtain ⟨q₁, hq₁, sq₁⟩ := exists_isPullback_morphismRestrict U sq (hland a ha x hx)
  obtain ⟨q₁', hq₁', sq₁'⟩ := exists_isPullback_morphismRestrict U sq' (hland a' ha' x' hx')
  rw [← hf₁] at sq₁ sq₁'
  have key := eulerSum_eq_of_isPullback _ hfp _ hMfp hMflat _ _ q₁ g sq₁ q₁' g' sq₁'
  have e₁ : (Scheme.Modules.pullback q₁).obj (M.restrict (f ⁻¹ᵁ U).ι) ≅
      (Scheme.Modules.pullback q).obj M :=
    (Scheme.Modules.pullback q₁).mapIso ((Scheme.Modules.restrictFunctorIsoPullback _).app M) ≪≫
      (Scheme.Modules.pullbackComp q₁ (f ⁻¹ᵁ U).ι).app M ≪≫ eqToIso (by rw [hq₁])
  have e₂ : (Scheme.Modules.pullback q₁').obj (M.restrict (f ⁻¹ᵁ U).ι) ≅
      (Scheme.Modules.pullback q').obj M :=
    (Scheme.Modules.pullback q₁').mapIso ((Scheme.Modules.restrictFunctorIsoPullback _).app M) ≪≫
      (Scheme.Modules.pullbackComp q₁' (f ⁻¹ᵁ U).ι).app M ≪≫ eqToIso (by rw [hq₁'])
  rwa [eulerSum_congr k g e₁, eulerSum_congr k g' e₂] at key

/-- An invertible module is quasi-coherent and of finite type: it is finite locally free of rank
one. -/
private theorem isQuasicoherent_and_isFiniteType_of_isInvertible {Z : Scheme.{0}} (L : Z.Modules)
    [h0 : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    L.IsQuasicoherent ∧ L.IsFiniteType := by
  have hS : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      Z.presheaf _ _).mpr h0
  refine ⟨Stacks.Picard.isQuasicoherent_of_isInvertible L hS, ?_⟩
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} L 1 :=
    Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible Z L h0
  have h := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L).2 h
  exact Stacks.FiniteLocallyFree.isFiniteType L

open ProperFlatFibreEulerCharacteristic in
/-- **Degrees of an invertible sheaf are constant on general fibres.** Let `j : S ⟶ 𝔸ⁿ_k` be
an open immersion of an integral scheme and `f : X ⟶ S` proper. For an invertible sheaf `L` on `X`
there is a nonzero polynomial `P` such that, on the fibres of `f` over the `k`-points of `S` above
coordinate tuples off `P = 0` which are curves, the restrictions of `L` all have the same
degree. -/
private theorem exists_polynomial_invertibleCurveDegree_eq {k : Type} [Field k] {n : Type}
    {S X : Scheme.{0}} [IsIntegral S] (j : S ⟶ 𝔸(n; Spec (.of k))) [IsOpenImmersion j]
    (f : X ⟶ S) [IsProper f] [LocallyOfFiniteType f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ P : MvPolynomial n k, P ≠ 0 ∧
      (∀ a : n → k, MvPolynomial.eval a P ≠ 0 → Set.range (AffineSpace.homOfVector
        (𝟙 (Spec (.of k))) (fun q => (Scheme.ΓSpecIso (.of k)).inv (a q))) ⊆ Set.range j) ∧
      ∀ (a a' : n → k), MvPolynomial.eval a P ≠ 0 → MvPolynomial.eval a' P ≠ 0 →
      ∀ (x x' : Spec (.of k) ⟶ S),
        x ≫ j = AffineSpace.homOfVector (𝟙 _) (fun q => (Scheme.ΓSpecIso (.of k)).inv (a q)) →
        x' ≫ j = AffineSpace.homOfVector (𝟙 _) (fun q => (Scheme.ΓSpecIso (.of k)).inv (a' q)) →
      ∀ {Z Z' : Scheme.{0}} (q : Z ⟶ X) (g : Z ⟶ Spec (.of k)) (q' : Z' ⟶ X)
        (g' : Z' ⟶ Spec (.of k)) [IsProper g] [IsProper g'] (hdim : topologicalKrullDim Z ≤ 1)
        (hdim' : topologicalKrullDim Z' ≤ 1)
        [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
          ((Scheme.Modules.pullback q).obj L)]
        [SheafOfModules.IsInvertible Z'.presheaf Z'.ringCatSheaf.2
          ((Scheme.Modules.pullback q').obj L)],
        IsPullback q g f x → IsPullback q' g' f x' →
        invertibleCurveDegree k g hdim ((Scheme.Modules.pullback q).obj L) =
          invertibleCurveDegree k g' hdim' ((Scheme.Modules.pullback q').obj L) := by
  obtain ⟨hLq, hLf⟩ := isQuasicoherent_and_isFiniteType_of_isInvertible L
  haveI : (SheafOfModules.unit X.ringCatSheaf).IsFiniteType := structureSheaf_isFiniteType X
  obtain ⟨P₁, hP₁, hj₁, h₁⟩ := exists_polynomial_eulerSum_eq j f L
  obtain ⟨P₂, hP₂, -, h₂⟩ :=
    exists_polynomial_eulerSum_eq j f (SheafOfModules.unit X.ringCatSheaf)
  refine ⟨P₁ * P₂, mul_ne_zero hP₁ hP₂, fun a ha => hj₁ a ?_, fun a a' ha ha' x x' hx hx' Z Z' q g
    q' g' _ _ hdim hdim' _ _ sq sq' => ?_⟩
  · rw [map_mul] at ha; exact left_ne_zero_of_mul ha
  rw [map_mul] at ha ha'
  have e₁ := h₁ a a' (left_ne_zero_of_mul ha) (left_ne_zero_of_mul ha') x x' hx hx' q g q' g'
    sq sq'
  have e₂ := h₂ a a' (right_ne_zero_of_mul ha) (right_ne_zero_of_mul ha') x x' hx hx' q g q' g'
    sq sq'
  have u₁ : eulerSum k g (SheafOfModules.unit Z.ringCatSheaf) =
      eulerSum k g ((Scheme.Modules.pullback q).obj (SheafOfModules.unit X.ringCatSheaf)) :=
    eulerSum_congr k g (Stacks.PullbackAlgebra.pullbackUnitIso q.toLRSHom.toShHom).symm
  have u₂ : eulerSum k g' (SheafOfModules.unit Z'.ringCatSheaf) =
      eulerSum k g' ((Scheme.Modules.pullback q').obj (SheafOfModules.unit X.ringCatSheaf)) :=
    eulerSum_congr k g' (Stacks.PullbackAlgebra.pullbackUnitIso q'.toLRSHom.toShHom).symm
  change eulerSum k g _ - eulerSum k g _ = eulerSum k g' _ - eulerSum k g' _
  rw [u₁, u₂, e₁, e₂]

/-- **Smoothness spreads from a Zariski-dense set of `k`-points.** Let `f : X ⟶ 𝔸ⁿ_k` be of
finite type with fibres `Z a` over the `k`-points. If every nonempty basic open `D(Q)` of
coefficient tuples contains a tuple with smooth fibre, then the fibres over all tuples off some
hypersurface `P = 0` are smooth: over a dense open where `f` is flat, the image of the non-smooth
locus is constructible, and it cannot contain the generic point. -/
private theorem exists_polynomial_forall_smooth {k : Type} [Field k] [Infinite k] {n : Type}
    [Finite n] {X : Scheme.{0}} (f : X ⟶ 𝔸(n; Spec (.of k))) [LocallyOfFiniteType f]
    [QuasiCompact f] (Z : (n → k) → Scheme.{0}) (q : ∀ a, Z a ⟶ X)
    (g : ∀ a, Z a ⟶ Spec (.of k)) [∀ a, LocallyOfFinitePresentation (g a)]
    (hsq : ∀ a, IsPullback (q a) (g a) f
      (AffineSpace.homOfVector (𝟙 _) (fun i => (Scheme.ΓSpecIso (.of k)).inv (a i))))
    (hex : ∀ Q : MvPolynomial n k, Q ≠ 0 → ∃ a, MvPolynomial.eval a Q ≠ 0 ∧ Smooth (g a)) :
    ∃ P : MvPolynomial n k, P ≠ 0 ∧ ∀ a, MvPolynomial.eval a P ≠ 0 → Smooth (g a) := by
  classical
  haveI : IsLocallyNoetherian 𝔸(n; Spec (.of k)) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝔸(n; Spec (.of k)) ↘ Spec (.of k))
  haveI : CompactSpace 𝔸(n; Spec (.of k)) :=
    QuasiCompact.compactSpace_of_compactSpace (𝔸(n; Spec (.of k)) ↘ Spec (.of k))
  haveI : IsNoetherian 𝔸(n; Spec (.of k)) := {}
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := {}
  haveI : (SheafOfModules.unit X.ringCatSheaf).IsFiniteType := structureSheaf_isFiniteType X
  obtain ⟨U, hUd, hflat, hfp, -, -⟩ :=
    exists_dense_open_flat_finitePresentation_of_isIntegral f (SheafOfModules.unit X.ringCatSheaf)
  have hf₁ := Scheme.Hom.resLE_eq_morphismRestrict (f := f) (U := U)
  rw [hf₁] at hflat hfp
  have hUne : (U : Set 𝔸(n; Spec (.of k))).Nonempty := hUd.nonempty
  haveI : Nonempty U := hUne.to_subtype
  haveI : LocallyOfFinitePresentation (f ∣_ U) := inferInstance
  haveI : QuasiCompact (f ∣_ U) := inferInstance
  have : QuasiSeparatedSpace (f ⁻¹ᵁ U).toScheme := NoetherianSpace.to_quasiSeparatedSpace
  have hZ : Topology.IsConstructible (((f ∣_ U).smoothLocus : Set (f ⁻¹ᵁ U).toScheme)ᶜ) := by
    rw [Topology.isConstructible_compl]
    exact (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible (f ∣_ U).smoothLocus.2
  have : QuasiSeparatedSpace U.toScheme := NoetherianSpace.to_quasiSeparatedSpace
  have hB := (f ∣_ U).isConstructible_image hZ
  obtain ⟨h₁, h₂⟩ := MMP.Threefold.Bridges.exists_isOpen_mem_subset_of_isConstructible
    (genericPoint_spec U.toScheme) hB
  -- the restricted fibre square at a tuple landing in an open `V` of `U`
  have hsqV : ∀ (V : U.toScheme.Opens) (a : n → k), (∀ p : Spec (.of k),
      AffineSpace.homOfVector (𝟙 (Spec (.of k)))
        (fun i => (Scheme.ΓSpecIso (.of k)).inv (a i)) p ∈ U.ι ''ᵁ V) →
      ∃ (hx : Set.range (AffineSpace.homOfVector (𝟙 (Spec (.of k)))
          (fun i => (Scheme.ΓSpecIso (.of k)).inv (a i))) ⊆ Set.range U.ι)
        (q' : Z a ⟶ (f ⁻¹ᵁ U).toScheme), q' ≫ (f ⁻¹ᵁ U).ι = q a ∧
        IsPullback q' (g a) (f ∣_ U) (IsOpenImmersion.lift U.ι _ hx) ∧
        ∀ w, (f ∣_ U) (q' w) ∈ V := by
    intro V a hmem
    have hx : Set.range (AffineSpace.homOfVector (𝟙 (Spec (.of k)))
        (fun i => (Scheme.ΓSpecIso (.of k)).inv (a i))) ⊆ Set.range U.ι := by
      rintro _ ⟨p, rfl⟩
      obtain ⟨y, -, hy⟩ := hmem p
      exact ⟨y, hy⟩
    obtain ⟨q', hq', sq'⟩ := exists_isPullback_morphismRestrict U (hsq a) hx
    refine ⟨hx, q', hq', sq', fun w => ?_⟩
    rw [← Scheme.Hom.comp_apply, sq'.w, Scheme.Hom.comp_apply]
    obtain ⟨y, hyV, hy⟩ := hmem (g a w)
    have : U.ι (IsOpenImmersion.lift U.ι _ hx (g a w)) = U.ι y := by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]
      exact hy.symm
    rw [U.ι.isOpenEmbedding.injective this]
    exact hyV
  by_cases hη : genericPoint U.toScheme ∈ (f ∣_ U) '' ((f ∣_ U).smoothLocus : Set _)ᶜ
  · exfalso
    obtain ⟨V, hVo, hηV, hVB⟩ := h₁ hη
    obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_homOfVector_mem (U.ι ''ᵁ ⟨V, hVo⟩)
      ⟨_, ⟨_, hηV, rfl⟩⟩
    obtain ⟨a, ha, hsm⟩ := hex Q hQ0
    obtain ⟨hx, q', -, sq', -⟩ := hsqV ⟨V, hVo⟩ a (hQ a ha)
    obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
    have hv : IsOpenImmersion.lift U.ι _ hx p ∈ V := by
      obtain ⟨y, hyV, hy⟩ := hQ a ha p
      have : U.ι (IsOpenImmersion.lift U.ι _ hx p) = U.ι y := by
        rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]
        exact hy.symm
      rw [U.ι.isOpenEmbedding.injective this]
      exact hyV
    obtain ⟨z, hzns, hz⟩ := hVB hv
    obtain ⟨w, hw, -⟩ := exists_eq_of_isPullback sq' z _ hz
    have htop := (Scheme.Hom.smoothLocus_eq_top_iff (f := g a)).2 hsm
    rw [Scheme.Hom.smoothLocus_eq_preimage_of_isPullback sq' (Or.inl hflat)] at htop
    have hw' : w ∈ q' ⁻¹ᵁ (f ∣_ U).smoothLocus := by rw [htop]; trivial
    exact hzns (hw ▸ hw')
  · obtain ⟨V, hVo, hηV, hVB⟩ := h₂ hη
    obtain ⟨P, hP0, hP⟩ := exists_polynomial_homOfVector_mem (U.ι ''ᵁ ⟨V, hVo⟩)
      ⟨_, ⟨_, hηV, rfl⟩⟩
    refine ⟨P, hP0, fun a ha => ?_⟩
    obtain ⟨hx, q', -, sq', hV⟩ := hsqV ⟨V, hVo⟩ a (hP a ha)
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,
      Scheme.Hom.smoothLocus_eq_preimage_of_isPullback sq' (Or.inl hflat), eq_top_iff]
    intro w _
    by_contra hw
    exact hVB (hV w) ⟨q' w, hw, rfl⟩

/-- **Degrees along general complete intersections are constant.** For an invertible sheaf `L`
on `X` and a closed subscheme `i : E ⟶ X` of `X ⊆ ℙᴺ_k` proper over `k`, the degree of `L` on
`E ∩ H_{c₁} ∩ ⋯ ∩ H_{c_m}` is the same for all tuples `c` off a hypersurface, whenever that
complete intersection is a curve. -/
private theorem exists_polynomial_degreeOn_eq {k : Type} [Field k] {X E : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] (i : E ⟶ X) [IsClosedImmersion i] {N : ℕ}
    (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX) (ι : Type) [Fintype ι]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ P : MvPolynomial (ι × Fin (N + 1)) k, P ≠ 0 ∧ ∀ c c' : ι → Fin (N + 1) → k,
      MvPolynomial.eval (fun p => c p.1 p.2) P ≠ 0 →
      MvPolynomial.eval (fun p => c' p.1 p.2) P ≠ 0 →
      ∀ (hd : topologicalKrullDim (⨆ j, hyperplaneSection (i ≫ φ) (c j)).subscheme ≤ 1)
        (hd' : topologicalKrullDim (⨆ j, hyperplaneSection (i ≫ φ) (c' j)).subscheme ≤ 1),
        degreeOn k sX ((⨆ j, hyperplaneSection (i ≫ φ) (c j)).subschemeι ≫ i) hd L =
          degreeOn k sX ((⨆ j, hyperplaneSection (i ≫ φ) (c' j)).subschemeι ≫ i) hd' L := by
  letI : E.Over (Spec (.of k)) := ⟨i ≫ sX⟩
  haveI : IsProper (E ↘ Spec (.of k)) := (inferInstance : IsProper (i ≫ sX))
  have hψ : (i ≫ φ) ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = E ↘ Spec (.of k) := by
    rw [Category.assoc, hφ]; rfl
  obtain ⟨𝒞, f, _, π, hfam⟩ := exists_univFamily (i ≫ φ) hψ ι
  obtain ⟨P, hP0, -, hP⟩ := exists_polynomial_invertibleCurveDegree_eq (𝟙 _) f
    ((Scheme.Modules.pullback (π ≫ i)).obj L)
  have hconv : ∀ (C : E.IdealSheafData) (hd : topologicalKrullDim C.subscheme ≤ 1)
      (q : C.subscheme ⟶ 𝒞), q ≫ π = C.subschemeι →
      degreeOn k sX (C.subschemeι ≫ i) hd L = invertibleCurveDegree k
        (C.subschemeι ≫ (E ↘ Spec (.of k))) hd
        ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback (π ≫ i)).obj L)) := by
    intro C hd q hq
    rw [MMP.Mori.degreeOn, invertibleCurveDegree_congr_structure (Category.assoc _ _ _) hd]
    exact invertibleCurveDegree_eq_of_iso k _ hd (eqToIso (by rw [← hq, Category.assoc]) ≪≫
      ((Scheme.Modules.pullbackComp q (π ≫ i)).app L).symm)
  refine ⟨P, hP0, fun c c' hc hc' hd hd' => ?_⟩
  obtain ⟨q, hq, sq⟩ := hfam c
  obtain ⟨q', hq', sq'⟩ := hfam c'
  rw [hconv _ hd q hq, hconv _ hd' q' hq']
  exact hP (fun p => c p.1 p.2) (fun p => c' p.1 p.2) hc hc' _ _ (Category.comp_id _)
    (Category.comp_id _) q _ q' _ hd hd' sq sq'

/-- The degree of the canonical sheaf of the smooth locus along a curve in it depends only on the
ideal sheaf of the curve. -/
private theorem invertibleCurveDegree_canonicalSheaf_congr {k : Type} [Field k] {Y : Scheme.{0}}
    (g : Y ⟶ Spec (.of k)) (d : ℕ) {J J' : Y.IdealSheafData} (hJ : J = J')
    [IsProper (J.subschemeι ≫ g)] [IsProper (J'.subschemeι ≫ g)]
    (hd : topologicalKrullDim J.subscheme ≤ 1) (hd' : topologicalKrullDim J'.subscheme ≤ 1)
    (hr : Set.range J.subschemeι ⊆ Set.range (smoothLocus g).ι)
    (hr' : Set.range J'.subschemeι ⊆ Set.range (smoothLocus g).ι)
    [SheafOfModules.IsInvertible (smoothLocus g).toScheme.presheaf
      (smoothLocus g).toScheme.ringCatSheaf.2 (canonicalSheaf g d)] :
    invertibleCurveDegree k (J.subschemeι ≫ g) hd
        ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hr)).obj (canonicalSheaf g d)) =
      invertibleCurveDegree k (J'.subschemeι ≫ g) hd'
        ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hr')).obj (canonicalSheaf g d)) := by
  subst hJ; rfl

/-- **Canonical degrees along general complete intersections are constant.** Let `ν : Eᵛ ⟶ E`
be finite over a closed subscheme `E` of `X ⊆ ℙᴺ_k`, and suppose the canonical sheaf of the smooth
locus of `Eᵛ` is invertible. Then the degree of that canonical sheaf on
`Eᵛ ∩ H_{c₁} ∩ ⋯ ∩ H_{c_m}` is the same for all tuples `c` off a hypersurface, whenever that
complete intersection is a curve inside the smooth locus. -/
private theorem exists_polynomial_canonicalSheaf_degree_eq {k : Type} [Field k]
    {X E Eν : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProper sX] (i : E ⟶ X)
    [IsClosedImmersion i] (ν : Eν ⟶ E) [IsFinite ν] {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX) (ι : Type) [Fintype ι]
    (d : ℕ) [SheafOfModules.IsInvertible (smoothLocus (ν ≫ i ≫ sX)).toScheme.presheaf
      (smoothLocus (ν ≫ i ≫ sX)).toScheme.ringCatSheaf.2 (canonicalSheaf (ν ≫ i ≫ sX) d)] :
    ∃ P : MvPolynomial (ι × Fin (N + 1)) k, P ≠ 0 ∧ ∀ c c' : ι → Fin (N + 1) → k,
      MvPolynomial.eval (fun p => c p.1 p.2) P ≠ 0 →
      MvPolynomial.eval (fun p => c' p.1 p.2) P ≠ 0 →
      ∀ (hd : topologicalKrullDim (⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j)).subscheme ≤ 1)
        (hd' : topologicalKrullDim (⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c' j)).subscheme ≤ 1)
        (hr : Set.range (⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j)).subschemeι ⊆
          Set.range (smoothLocus (ν ≫ i ≫ sX)).ι)
        (hr' : Set.range (⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c' j)).subschemeι ⊆
          Set.range (smoothLocus (ν ≫ i ≫ sX)).ι),
        invertibleCurveDegree k ((⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j)).subschemeι ≫
            ν ≫ i ≫ sX) hd ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hr)).obj
              (canonicalSheaf (ν ≫ i ≫ sX) d)) =
          invertibleCurveDegree k ((⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c' j)).subschemeι ≫
            ν ≫ i ≫ sX) hd' ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hr')).obj
              (canonicalSheaf (ν ≫ i ≫ sX) d)) := by
  classical
  set g := ν ≫ i ≫ sX with hg
  letI : Eν.Over (Spec (.of k)) := ⟨g⟩
  haveI : IsProper (Eν ↘ Spec (.of k)) := (inferInstance : IsProper (ν ≫ i ≫ sX))
  have hψ : (ν ≫ i ≫ φ) ≫ Stacks.ProjectiveCohomology.projModelToSpec k N =
      Eν ↘ Spec (.of k) := by
    rw [Category.assoc, Category.assoc, hφ]; rfl
  obtain ⟨𝒞, f, _, π, hfam⟩ := exists_univFamily (ν ≫ i ≫ φ) hψ ι
  -- the parameters whose fibre misses the singular locus
  set B' := f '' (π ⁻¹' ((smoothLocus g : Set Eν)ᶜ)) with hB'
  have hB'c : IsClosed B' :=
    f.isClosedMap _ ((smoothLocus g).isOpen.isClosed_compl.preimage π.continuous)
  set U₀ : (𝔸(ι × Fin (N + 1); Spec (.of k))).Opens := ⟨B'ᶜ, hB'c.isOpen_compl⟩ with hU₀
  -- a fibre inside the smooth locus lies over `U₀`
  have hland : ∀ (c : ι → Fin (N + 1) → k)
      (hr : Set.range (⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j)).subschemeι ⊆
        Set.range (smoothLocus g).ι),
      Set.range (AffineSpace.homOfVector (𝟙 (Spec (.of k)))
        (fun p => (Scheme.ΓSpecIso (.of k)).inv (c p.1 p.2))) ⊆ Set.range U₀.ι := by
    rintro c hr _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    rintro ⟨z, hz, hzp⟩
    obtain ⟨q, hq, sq⟩ := hfam c
    obtain ⟨w, hw, -⟩ := exists_eq_of_isPullback sq z p hzp
    apply hz
    rw [← hw, ← Scheme.Hom.comp_apply, hq]
    have := hr ⟨w, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  by_cases hne : (U₀ : Set (𝔸(ι × Fin (N + 1); Spec (.of k)))).Nonempty
  · haveI : Nonempty U₀ := hne.to_subtype
    haveI : IsIntegral U₀.toScheme := isIntegral_of_isOpenImmersion U₀.ι
    haveI : IsProper (f ∣_ U₀) :=
      MorphismProperty.of_isPullback (P := @IsProper) (isPullback_morphismRestrict f U₀).flip
        inferInstance
    have hρ : Set.range ((f ⁻¹ᵁ U₀).ι ≫ π) ⊆ Set.range (smoothLocus g).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      by_contra hz
      have hfz : f ((f ⁻¹ᵁ U₀).ι z) ∈ U₀ := z.2
      exact hfz ⟨_, hz, rfl⟩
    obtain ⟨P, hP0, hPj, hP⟩ := exists_polynomial_invertibleCurveDegree_eq U₀.ι (f ∣_ U₀)
      ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hρ)).obj (canonicalSheaf g d))
    -- the restricted fibre square of a curve inside the smooth locus
    have hfib : ∀ (c : ι → Fin (N + 1) → k) (hc : MvPolynomial.eval (fun p => c p.1 p.2) P ≠ 0)
        (hd : topologicalKrullDim (⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j)).subscheme ≤ 1)
        (hr : Set.range (⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j)).subschemeι ⊆
          Set.range (smoothLocus g).ι),
        ∃ (x : Spec (.of k) ⟶ U₀.toScheme) (q₁ : (⨆ j, hyperplaneSection (ν ≫ i ≫ φ)
            (c j)).subscheme ⟶ (f ⁻¹ᵁ U₀).toScheme),
          x ≫ U₀.ι = AffineSpace.homOfVector (𝟙 _)
            (fun p => (Scheme.ΓSpecIso (.of k)).inv (c p.1 p.2)) ∧
          IsPullback q₁ ((⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j)).subschemeι ≫
            (Eν ↘ Spec (.of k))) (f ∣_ U₀) x ∧
          invertibleCurveDegree k ((⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j)).subschemeι ≫
            g) hd ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hr)).obj
              (canonicalSheaf g d)) =
          invertibleCurveDegree k ((⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j)).subschemeι ≫
            (Eν ↘ Spec (.of k))) hd ((Scheme.Modules.pullback q₁).obj
              ((Scheme.Modules.pullback (IsOpenImmersion.lift _ _ hρ)).obj
                (canonicalSheaf g d))) := by
      intro c hc hd hr
      obtain ⟨q, hq, sq⟩ := hfam c
      obtain ⟨q₁, hq₁, sq₁⟩ := exists_isPullback_morphismRestrict U₀ sq (hland c hr)
      refine ⟨_, q₁, IsOpenImmersion.lift_fac _ _ _, sq₁, ?_⟩
      have hl : q₁ ≫ IsOpenImmersion.lift _ _ hρ = IsOpenImmersion.lift _ _ hr := by
        rw [← cancel_mono (smoothLocus g).ι, Category.assoc, IsOpenImmersion.lift_fac,
          IsOpenImmersion.lift_fac, reassoc_of% hq₁, hq]
      exact invertibleCurveDegree_eq_of_iso k _ hd (eqToIso (by rw [hl]) ≪≫
        ((Scheme.Modules.pullbackComp q₁ _).app _).symm)
    refine ⟨P, hP0, fun c c' hc hc' hd hd' hr hr' => ?_⟩
    obtain ⟨x, q₁, hx, sq₁, e₁⟩ := hfib c hc hd hr
    obtain ⟨x', q₁', hx', sq₁', e₁'⟩ := hfib c' hc' hd' hr'
    rw [e₁, e₁']
    exact hP (fun p => c p.1 p.2) (fun p => c' p.1 p.2) hc hc' x x' hx hx' q₁ _ q₁' _ hd hd'
      sq₁ sq₁'
  · refine ⟨1, one_ne_zero, fun c c' _ _ hd hd' hr hr' => ?_⟩
    exfalso
    obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
    obtain ⟨y, -⟩ := hland c hr ⟨p, rfl⟩
    exact hne ⟨_, y.2⟩

/-! ### General complete intersections: smoothness and constancy of the degrees -/

/-- **The canonical sheaf of the smooth locus is invertible.** On a variety of dimension `d` over a
perfect field the smooth locus is a smooth variety of dimension `d`, so its top exterior power of
differentials is invertible. -/
private theorem isInvertible_canonicalSheaf {k : Type} [Field k] [PerfectField k] {Y : Scheme.{0}}
    (g : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k g] {d : ℕ}
    (hd : topologicalKrullDim Y = d) :
    SheafOfModules.IsInvertible (smoothLocus g).toScheme.presheaf
      (smoothLocus g).toScheme.ringCatSheaf.2 (canonicalSheaf g d) := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  haveI : IsNoetherian Y := {}
  have hgen : genericPoint Y ∈ smoothLocus g := by
    rw [smoothLocus_eq_smoothLocus]
    exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField g
  haveI : Nonempty (smoothLocus g) := ⟨⟨_, hgen⟩⟩
  haveI : IsIntegral (smoothLocus g).toScheme := isIntegral_of_isOpenImmersion (smoothLocus g).ι
  haveI : QuasiCompact (smoothLocus g).ι :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  haveI : AlgebraicGeometry.IsVariety k ((smoothLocus g).ι ≫ g) := {}
  haveI : Smooth ((smoothLocus g).ι ≫ g) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    intro x _
    have hW : ((smoothLocus g : Y.Opens) : Set Y) = (g.smoothLocus : Set Y) := by
      rw [smoothLocus_eq_smoothLocus]
    show (smoothLocus g).ι x ∈ (g.smoothLocus : Set Y)
    rw [← hW]
    exact x.2
  have hdW : topologicalKrullDim (smoothLocus g).toScheme = d :=
    (Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens k g _).trans hd
  haveI := MMP.Intersection.smoothOfRelativeDimension_of_isVariety ((smoothLocus g).ι ≫ g) d hdW
  have hinv := Stacks.Discriminant.isInvertible_relativeDifferentialForms ((smoothLocus g).ι ≫ g) d
  have hM := Stacks.SheafOfModules.isInvertible_of_tensorInvertible
    (X := (smoothLocus g).toScheme.toRingedSpace) (canonicalSheaf g d) (h := hinv)
  exact (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    _ _ _).mp hM

/-- **The singular locus of a normal variety has codimension at least two.** On a normal variety
of dimension `d + 2` over a perfect field, the points off the smooth locus have coheight at least
two, so they form a closed subset of dimension at most `d`. -/
private theorem topologicalKrullDim_compl_smoothLocus_le {k : Type} [Field k] [PerfectField k]
    {Y : Scheme.{0}} [IsIntegral Y] (g : Y ⟶ Spec (.of k)) (hY : IsNormalVariety k g) {d : ℕ}
    (hd : topologicalKrullDim Y = (d + 2 : ℕ)) :
    topologicalKrullDim ↥((smoothLocus g : Set Y)ᶜ) ≤ (d : ℕ) := by
  haveI : LocallyOfFiniteType g := hY.1.toLocallyOfFiniteType
  -- points of codimension at most one are smooth: a normal variety is regular in codimension one
  have hsm1 : ∀ x : Y, Order.coheight x ≤ 1 → x ∈ smoothLocus g := by
    intro x hx
    haveI : LocallyOfFinitePresentation g :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    rcases eq_or_ne (Order.coheight x) 1 with h1 | h1
    · have hmem := MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hY
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1)
      have hg : MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1) = x :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      rwa [hg] at hmem
    · have h0 : Order.coheight x = 0 := Order.lt_one_iff.mp (lt_of_le_of_ne hx h1)
      have hle : x ≤ genericPoint Y := by
        rw [Scheme.le_iff_specializes]; exact genericPoint_specializes x
      have hge := Order.coheight_eq_zero.mp h0 hle
      rw [Scheme.le_iff_specializes] at hge
      rw [(hge.antisymm (genericPoint_specializes x)).eq, smoothLocus_eq_smoothLocus]
      exact g.genericPoint_mem_smoothLocus_of_perfectField
  refine topologicalKrullDim_le_of_forall_closure (smoothLocus g).isOpen.isClosed_compl
    fun x hx => ?_
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight g x
  rw [hd] at h
  have hc : (2 : ℕ∞) ≤ Order.coheight x := by
    by_contra hlt
    exact hx (hsm1 x (Order.le_of_lt_add_one (lt_of_not_ge hlt)))
  have h2 : topologicalKrullDim (closure {x} : Set Y) + 1 + 1 ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [add_assoc, ← h]
    refine add_le_add (le_refl _) ?_
    rw [one_add_one_eq_two]
    have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight x : ℕ∞) : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr hc
    simpa using this
  exact withBot_le_natCast_of_add_one_le (withBot_le_natCast_of_add_one_le h2)

/-- **A normal finite birational model of a proper curve is smooth**: it is the normalization. -/
private theorem smooth_comp_of_isBirational_of_isNormal {k : Type} [Field k] [IsAlgClosed k]
    {C C' : Scheme.{0}} (sC : C ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k sC] [IsProper sC]
    (α : C' ⟶ C) [IsFinite α] [IsNormal C'] (hα : IsBirational α) : Smooth (α ≫ sC) := by
  obtain ⟨e, he⟩ := Scheme.exists_iso_normalizationScheme_of_isIntegralHom_of_isBirational
    (finite_irreducibleComponents_of_locallyOfFiniteType k sC) α
    (fun U hU => finite_irreducibleComponents_of_locallyOfFiniteType k (α ≫ sC) _
      (QuasiCompact.isCompact_preimage (f := α) _ U.2 hU))
    (fun U _ => hα.restrict U)
  haveI : Smooth (normalizationOverField k sC ≫ sC) :=
    (normalizationModel' k sC).smooth_structureMap
  have he' : α ≫ sC = e.hom ≫ normalizationOverField k sC ≫ sC := by
    rw [← Category.assoc, he]
  rw [he']
  infer_instance

/-- **General complete-intersection curves are smooth curve cuts.** Let `V ⊆ E` be an open over
which the normalization `ν : Eᵛ ⟶ E` is an isomorphism. If every nonempty basic open of
coefficient tuples contains a tuple whose curve `C_c` is integral, meets `Vᶜ` in finitely many
points, and has an integral normal preimage in `Eᵛ`, then for a general `(r-1)`-tuple `c` the
complete intersection `C_c = E ∩ H_{c₁} ∩ ⋯ ∩ H_{c_{r-1}}` is a curve whose preimage in `Eᵛ` is a
smooth curve inside its smooth locus. -/
private theorem exists_polynomial_forall_isSmoothCurveCut {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E] {m : ℕ} (hm : 1 ≤ m)
    (hEr : topologicalKrullDim E = (m + 1 : ℕ))
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX) (V : E.Opens)
    [IsIso (normalizationOverField k (i ≫ sX) ∣_ V)] :
    haveI := isFinite_normalizationOverField k (i ≫ sX)
    (∀ Q : MvPolynomial (Fin m × Fin (N + 1)) k, Q ≠ 0 → ∃ c : Fin m → Fin (N + 1) → k,
      MvPolynomial.eval (fun p => c p.1 p.2) Q ≠ 0 ∧
      (((⨆ j, hyperplaneSection (i ≫ φ) (c j)).subschemeι ⁻¹' (V : Set E)ᶜ)).Finite ∧
      IsIntegral (⨆ j, hyperplaneSection (i ≫ φ) (c j)).subscheme ∧
      IsIntegral ((⨆ j, hyperplaneSection (i ≫ φ) (c j)).comap
        (normalizationOverField k (i ≫ sX))).subscheme ∧
      IsNormal ((⨆ j, hyperplaneSection (i ≫ φ) (c j)).comap
        (normalizationOverField k (i ≫ sX))).subscheme) →
    ∃ P : MvPolynomial (Fin m × Fin (N + 1)) k, P ≠ 0 ∧
      ∀ c : Fin m → Fin (N + 1) → k, MvPolynomial.eval (fun p => c p.1 p.2) P ≠ 0 →
        IsSmoothCurveCut sX i (normalizationOverField k (i ≫ sX)) (m + 1)
          (⨆ j, hyperplaneSection (i ≫ φ) (c j)) := by
  haveI := isFinite_normalizationOverField k (i ≫ sX)
  intro hex
  classical
  haveI : PerfectField k := PerfectField.ofCharZero
  set ν := normalizationOverField k (i ≫ sX) with hνdef
  haveI : IsNormal (normalizationSchemeOverField k (i ≫ sX)) :=
    Scheme.isNormal_normalizationScheme E _
  set g := ν ≫ i ≫ sX with hg
  haveI : AlgebraicGeometry.IsVariety k (i ≫ sX) := {}
  haveI : AlgebraicGeometry.IsVariety k g := {}
  have hdimEν : topologicalKrullDim (normalizationSchemeOverField k (i ≫ sX)) = (m + 1 : ℕ) :=
    (topologicalKrullDim_normalizationSchemeOverField k (i ≫ sX)).trans hEr
  haveI := isInvertible_canonicalSheaf g hdimEν
  -- the image in `E` of the singular locus of `Eᵛ` has dimension less than `m`
  have hSingc : IsClosed ((smoothLocus g : Set (normalizationSchemeOverField k (i ≫ sX)))ᶜ) :=
    (smoothLocus g).isOpen.isClosed_compl
  have hSingd := topologicalKrullDim_compl_smoothLocus_le g ⟨inferInstance, inferInstance⟩
    (d := m - 1) (by rw [hdimEν]; exact_mod_cast (by omega : m + 1 = m - 1 + 2))
  obtain ⟨hT'c, hT'd⟩ := ProjectiveSpaceOfModule.isClosed_image_and_topologicalKrullDim_image_le
    k ν g (i ≫ sX) rfl hSingc
  -- the dimension count
  obtain ⟨Pd, hPd0, hPd⟩ := exists_polynomial_topologicalKrullDim_inter_iSup_hyperplaneSection
    (i ≫ φ) (fun b : Bool => if b then Set.univ else ν.base '' (smoothLocus g : Set _)ᶜ)
    (fun b => by cases b <;> [exact hT'c; exact isClosed_univ]) m
  have hdimC : ∀ c : Fin m → Fin (N + 1) → k, MvPolynomial.eval (fun p => c p.1 p.2) Pd ≠ 0 →
      topologicalKrullDim (⨆ j, hyperplaneSection (i ≫ φ) (c j)).subscheme = 1 := by
    intro c hc
    have h1 : (m : WithBot ℕ∞) ≤ topologicalKrullDim (Set.univ : Set E) := by
      rw [(Homeomorph.Set.univ E).isHomeomorph.topologicalKrullDim_eq, hEr]
      exact_mod_cast (by omega : m ≤ m + 1)
    obtain ⟨-, hdim⟩ := (hPd c hc true).2 h1
    rw [if_pos rfl, Set.univ_inter, (Homeomorph.Set.univ E).isHomeomorph.topologicalKrullDim_eq,
      hEr] at hdim
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
    revert hdim
    generalize topologicalKrullDim ↥(((⨆ j, hyperplaneSection (i ≫ φ) (c j)).support :
      TopologicalSpace.Closeds E) : Set E) = x
    intro hdim
    induction x using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.bot_add] at hdim
      exact absurd hdim.symm (WithBot.natCast_ne_bot _)
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        rw [← WithBot.coe_natCast, ← WithBot.coe_add, top_add] at hdim
        exact ENat.top_ne_coe (m + 1) (WithBot.coe_eq_coe.mp hdim)
      | coe x =>
        have : x + m = m + 1 := by exact_mod_cast hdim
        have hx : x = 1 := by omega
        subst hx; rfl
  have hJ : ∀ c : Fin m → Fin (N + 1) → k, (⨆ j, hyperplaneSection (i ≫ φ) (c j)).comap ν =
      ⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j) := by
    intro c
    rw [(Scheme.IdealSheafData.map_gc _).l_iSup]
    exact iSup_congr fun j => (hyperplaneSection_comp _ _ _).symm
  -- the restriction `Cᵛ ⟶ C` of `ν`
  have hπ : ∀ A : E.IdealSheafData, ∃ π : (A.comap ν).subscheme ⟶ A.subscheme,
      IsFinite π ∧ π ≫ A.subschemeι = (A.comap ν).subschemeι ≫ ν := by
    intro A
    refine ⟨Scheme.IdealSheafData.subschemeMap (A.comap ν) A ν
      (Scheme.IdealSheafData.le_map_comap _ _), ?_, Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _⟩
    haveI : IsFinite (Scheme.IdealSheafData.subschemeMap (A.comap ν) A ν
        (Scheme.IdealSheafData.le_map_comap _ _) ≫ A.subschemeι) := by
      rw [Scheme.IdealSheafData.subschemeMap_subschemeι]; infer_instance
    exact IsFinite.of_comp _ A.subschemeι
  -- smoothness of `Cᵛ` at the tuples of the induction
  have hsmooth₀ : ∀ c : Fin m → Fin (N + 1) → k, MvPolynomial.eval (fun p => c p.1 p.2) Pd ≠ 0 →
      (((⨆ j, hyperplaneSection (i ≫ φ) (c j)).subschemeι ⁻¹' (V : Set E)ᶜ)).Finite →
      IsIntegral (⨆ j, hyperplaneSection (i ≫ φ) (c j)).subscheme →
      IsIntegral ((⨆ j, hyperplaneSection (i ≫ φ) (c j)).comap ν).subscheme →
      IsNormal ((⨆ j, hyperplaneSection (i ≫ φ) (c j)).comap ν).subscheme →
      Smooth (((⨆ j, hyperplaneSection (i ≫ φ) (c j)).comap ν).subschemeι ≫ g) := by
    intro c hc hfin hint hintν hnorm
    set A := ⨆ j, hyperplaneSection (i ≫ φ) (c j) with hA
    obtain ⟨π, hπf, hπ⟩ := hπ A
    haveI := hπf
    haveI : AlgebraicGeometry.IsVariety k (A.subschemeι ≫ i ≫ sX) := {}
    haveI : AlgebraicGeometry.IsCurve k (A.subschemeι ≫ i ≫ sX) :=
      { topologicalKrullDim_eq_one := hdimC c hc }
    haveI : IsIso (π ∣_ (A.subschemeι ⁻¹ᵁ V)) :=
      isIso_subschemeMap_morphismRestrict ν V A _ rfl π hπ
    -- the open `C ∩ V` contains the generic point of `C`
    haveI : JacobsonSpace A.subscheme := LocallyOfFiniteType.jacobsonSpace (A.subschemeι ≫ i ≫ sX)
    have hCinf : ¬ Finite A.subscheme := by
      intro hfin'
      haveI := JacobsonSpace.discreteTopology (X := A.subscheme) (Set.toFinite _)
      have h0 := topologicalKrullDim_zero_of_discreteTopology A.subscheme
      rw [hdimC c hc] at h0
      exact absurd h0 (by decide)
    have hWne : ((A.subschemeι ⁻¹ᵁ V : TopologicalSpace.Opens _) :
        Set A.subscheme).Nonempty := by
      by_contra hne
      exact hCinf (Set.finite_univ_iff.mp (hfin.subset fun x _ hx => hne ⟨x, hx⟩))
    obtain ⟨y, hy⟩ := hWne
    have hsrc : ((π ⁻¹ᵁ (A.subschemeι ⁻¹ᵁ V) : TopologicalSpace.Opens _) :
        Set (A.comap ν).subscheme).Nonempty :=
      ⟨_, ((inv (π ∣_ (A.subschemeι ⁻¹ᵁ V))) ⟨y, hy⟩).2⟩
    have hbir : IsBirational π := by
      refine isBirational_of_isIso_morphismRestrict π (A.subschemeι ⁻¹ᵁ V) inferInstance
        (fun x hx => ?_)
        (fun z hz => ?_)
      · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
        subst hx
        exact ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).2
          ⟨hsrc.some, Set.mem_univ _, hsrc.some_mem⟩
      · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hz
        subst hz
        exact ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).2
          ⟨y, Set.mem_univ _, hy⟩
    have := smooth_comp_of_isBirational_of_isNormal (A.subschemeι ≫ i ≫ sX) π hbir
    rwa [reassoc_of% hπ] at this
  -- smoothness spreads to general tuples, along the universal family of `Eᵛ`
  letI : (normalizationSchemeOverField k (i ≫ sX)).Over (Spec (.of k)) := ⟨g⟩
  haveI : IsProper ((normalizationSchemeOverField k (i ≫ sX)) ↘ Spec (.of k)) :=
    (inferInstance : IsProper (ν ≫ i ≫ sX))
  have hψ : (ν ≫ i ≫ φ) ≫ Stacks.ProjectiveCohomology.projModelToSpec k N =
      (normalizationSchemeOverField k (i ≫ sX)) ↘ Spec (.of k) := by
    rw [Category.assoc, Category.assoc, hφ]; rfl
  obtain ⟨𝒞, f, _, π, hfam⟩ := exists_univFamily (ν ≫ i ≫ φ) hψ (Fin m)
  choose q hq hsq using hfam
  obtain ⟨Ps, hPs0, hPs⟩ := exists_polynomial_forall_smooth f
    (fun a => (⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (fun l => a (j, l))).subscheme)
    (fun a => q (fun j l => a (j, l)))
    (fun a => (⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (fun l => a (j, l))).subschemeι ≫ g)
    (fun a => hsq (fun j l => a (j, l))) (fun Q hQ => by
      obtain ⟨c, hc, hfin, hint, hintν, hnorm⟩ := hex (Q * Pd) (mul_ne_zero hQ hPd0)
      rw [map_mul] at hc
      refine ⟨fun p => c p.1 p.2, left_ne_zero_of_mul hc, ?_⟩
      have := hsmooth₀ c (right_ne_zero_of_mul hc) hfin hint hintν hnorm
      rwa [hJ c] at this)
  refine ⟨Pd * Ps, mul_ne_zero hPd0 hPs0, fun c hc => ?_⟩
  rw [map_mul] at hc
  have hcd := left_ne_zero_of_mul hc
  set A := ⨆ j, hyperplaneSection (i ≫ φ) (c j) with hA
  obtain ⟨π', hπ'f, hπ'⟩ := hπ A
  haveI := hπ'f
  have hrange : Set.range (A.comap ν).subschemeι ⊆ smoothLocus g := by
    rintro _ ⟨x, rfl⟩
    by_contra hx
    have hlt : topologicalKrullDim ↥(ν.base '' (smoothLocus g : Set _)ᶜ) < m := by
      refine lt_of_le_of_lt (hT'd.trans hSingd) ?_
      exact_mod_cast (by omega : m - 1 < m)
    have hempty := (hPd c hcd false).1 (by rwa [if_neg Bool.false_ne_true])
    rw [if_neg Bool.false_ne_true] at hempty
    have hmem : ν ((A.comap ν).subschemeι x) ∈
        ν.base '' (smoothLocus g : Set _)ᶜ ∩ (A.support : Set E) := by
      refine ⟨⟨_, hx, rfl⟩, ?_⟩
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨π' x, by rw [← Scheme.Hom.comp_apply, hπ', Scheme.Hom.comp_apply]⟩
    rw [hempty] at hmem
    exact hmem
  haveI : SheafOfModules.IsInvertible (smoothLocus (ν ≫ i ≫ sX)).toScheme.presheaf
      (smoothLocus (ν ≫ i ≫ sX)).toScheme.ringCatSheaf.2 (canonicalSheaf (ν ≫ i ≫ sX) (m + 1)) :=
    isInvertible_canonicalSheaf (ν ≫ i ≫ sX) hdimEν
  refine
    { dim_eq := hdimC c hcd
      dim_le := (MMP.Fourfold.topologicalKrullDim_le_of_isFinite π' (T := Set.univ)
          (fun _ => Set.mem_univ _)).trans (by
            rw [(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq, hdimC c hcd])
      range_subset := hrange
      smooth := by
        have := hPs (fun p => c p.1 p.2) (right_ne_zero_of_mul hc)
        rw [hJ c]
        exact this
      isInvertible := MMP.Mori.isInvertible_pullback_obj _ _ }

/-- **The degrees are constant on general complete intersections.** Both `K_{Eᵛ} · C_cᵛ` and
`(K_X + B) · C_c` are independent of the general tuple `c`: they are degrees of invertible
sheaves along the fibres of the universal complete intersection, whose Euler characteristics are
constant where that family is flat. -/
private theorem exists_polynomial_degrees_eq {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {K : Divisor X} {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E] {m : ℕ}
    (hEr : topologicalKrullDim E = (m + 1 : ℕ))
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [IsClosedImmersion φ]
    (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX) :
    haveI := isFinite_normalizationOverField k (i ≫ sX)
    ∃ P : MvPolynomial (Fin m × Fin (N + 1)) k, P ≠ 0 ∧
      ∀ c c' : Fin m → Fin (N + 1) → k, MvPolynomial.eval (fun p => c p.1 p.2) P ≠ 0 →
        MvPolynomial.eval (fun p => c' p.1 p.2) P ≠ 0 →
        ∀ (h : IsSmoothCurveCut sX i (normalizationOverField k (i ≫ sX)) (m + 1)
            (⨆ j, hyperplaneSection (i ≫ φ) (c j)))
          (h' : IsSmoothCurveCut sX i (normalizationOverField k (i ≫ sX)) (m + 1)
            (⨆ j, hyperplaneSection (i ≫ φ) (c' j))),
          h.canonicalDegree = h'.canonicalDegree ∧
            h.intersectionNumber hKB = h'.intersectionNumber hKB := by
  haveI := isFinite_normalizationOverField k (i ≫ sX)
  haveI : PerfectField k := PerfectField.ofCharZero
  set ν := normalizationOverField k (i ≫ sX) with hνdef
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  -- the Cartier multiple of `K + B`
  set Dd := (QDivisor.isCartierDivisor_cartierIndex_smul hKB).toDivisor with hDd_def
  have hDd : Dd.IsCartier := (QDivisor.isCartierDivisor_cartierIndex_smul hKB).isCartier_toDivisor
  haveI := hDd.isInvertibleModule_divisorialSheaf
  obtain ⟨P₁, hP₁, h₁⟩ := exists_polynomial_degreeOn_eq sX i φ hφ (Fin m) Dd.divisorialSheaf
  -- the canonical sheaf of the smooth locus of the normalization
  haveI : AlgebraicGeometry.IsVariety k (i ≫ sX) := {}
  haveI hcN : AlgebraicGeometry.IsVariety k (ν ≫ i ≫ sX) := {}
  haveI := isInvertible_canonicalSheaf (ν ≫ i ≫ sX) (d := m + 1)
    ((topologicalKrullDim_normalizationSchemeOverField k (i ≫ sX)).trans hEr)
  obtain ⟨P₂, hP₂, h₂⟩ := exists_polynomial_canonicalSheaf_degree_eq sX i ν φ hφ (Fin m) (m + 1)
  have hJ : ∀ c : Fin m → Fin (N + 1) → k, (⨆ j, hyperplaneSection (i ≫ φ) (c j)).comap ν =
      ⨆ j, hyperplaneSection (ν ≫ i ≫ φ) (c j) := by
    intro c
    rw [(Scheme.IdealSheafData.map_gc _).l_iSup]
    exact iSup_congr fun j => (hyperplaneSection_comp _ _ _).symm
  refine ⟨P₁ * P₂, mul_ne_zero hP₁ hP₂, fun c c' hc hc' h h' => ⟨?_, ?_⟩⟩
  · rw [map_mul] at hc hc'
    have hr := h.range_subset.trans_eq (Scheme.Opens.range_ι _).symm
    have hr' := h'.range_subset.trans_eq (Scheme.Opens.range_ι _).symm
    have e := h₂ c c' (right_ne_zero_of_mul hc) (right_ne_zero_of_mul hc')
      (hJ c ▸ h.dim_le) (hJ c' ▸ h'.dim_le) (hJ c ▸ hr) (hJ c' ▸ hr')
    unfold IsSmoothCurveCut.canonicalDegree
    exact congrArg (fun z : ℤ => (z : ℚ))
      ((invertibleCurveDegree_canonicalSheaf_congr (ν ≫ i ≫ sX) (m + 1) (hJ c) _ _ hr
        (hJ c ▸ hr)).trans (e.trans (invertibleCurveDegree_canonicalSheaf_congr (ν ≫ i ≫ sX)
          (m + 1) (hJ c') _ _ hr' (hJ c' ▸ hr')).symm))
  · rw [map_mul] at hc hc'
    unfold IsSmoothCurveCut.intersectionNumber QDivisor.intersectionNumber
    exact congrArg (fun z : ℤ => (z : ℚ) / ((Divisor.toQDivisor K + B).cartierIndex hKB : ℚ))
      (h₁ c c' (left_ne_zero_of_mul hc) (left_ne_zero_of_mul hc') h.dim_eq.le h'.dim_eq.le)

end MMP.FourfoldProofs.FourfoldMaximalFibreComponentWeakSubadjunctionProof

open MMP.FourfoldProofs.FourfoldMaximalFibreComponentWeakSubadjunctionProof

namespace MMP.Fourfold

/-- **Weak subadjunction on a component of maximal dimension of a fibre.** Let `(X, B)` be a klt
pair with `B ≥ 0` on a projective `n`-dimensional variety over an algebraically closed field `k`
of characteristic zero, `f : X ⟶ S` a projective morphism of `k`-schemes, and `E ⊆ f⁻¹(s)` an
integral closed subscheme with `dim E = dim f⁻¹(s) = r`, `1 ≤ r ≤ n - 1`. Fix a closed embedding
`φ : X ⟶ ℙᴺ_k`. Then for `(r - 1)`-tuples of hyperplanes `c` off the zero locus of a nonzero
polynomial, the complete intersection `C = E ∩ H_{c₁} ∩ ⋯ ∩ H_{c_{r-1}}` is a curve, its preimage
`Cᵛ` in the normalization `Eᵛ` is a smooth curve inside the smooth locus of `Eᵛ`, the canonical
sheaf of that smooth locus restricts to an invertible sheaf on `Cᵛ`, and
`deg (ω_{Eᵛ}|_{Cᵛ}) ≤ (K_X + B) · C`. -/
@[mmp "lem_fourfold_maximal_fibre_component_weak_subadjunction"]
public theorem exists_invertibleCurveDegree_canonicalSheaf_normalization_le_intersectionNumber
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f) (s : S)
    {E : Scheme.{0}} (i : E ⟶ X) [IsClosedImmersion i] [IsIntegral E]
    (hEs : Set.range i ⊆ f ⁻¹' {s}) {r : ℕ} (hr₁ : 1 ≤ r) (hrn : r + 1 ≤ n)
    (hEr : topologicalKrullDim E = r) (hfib : topologicalKrullDim (f ⁻¹' {s}) = r)
    {N : ℕ} (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    [IsClosedImmersion φ] (hφ : φ ≫ Stacks.ProjectiveCohomology.projModelToSpec k N = sX) :
    haveI := isFinite_normalizationOverField k (i ≫ sX)
    ∃ P : MvPolynomial (Fin (r - 1) × Fin (N + 1)) k, P ≠ 0 ∧
      ∀ c : Fin (r - 1) → Fin (N + 1) → k, MvPolynomial.eval (fun p => c p.1 p.2) P ≠ 0 →
        let IC : E.IdealSheafData := ⨆ j, hyperplaneSection (i ≫ φ) (c j)
        let ICν := IC.comap (normalizationOverField k (i ≫ sX))
        ∃ (hC : topologicalKrullDim IC.subscheme = 1)
          (hCν : topologicalKrullDim ICν.subscheme ≤ 1)
          (hsm : Set.range ICν.subschemeι ⊆
            smoothLocus (normalizationOverField k (i ≫ sX) ≫ i ≫ sX)),
          Smooth (ICν.subschemeι ≫ normalizationOverField k (i ≫ sX) ≫ i ≫ sX) ∧
          let ω := (Scheme.Modules.pullback (IsOpenImmersion.lift
              (smoothLocus (normalizationOverField k (i ≫ sX) ≫ i ≫ sX)).ι ICν.subschemeι
                (hsm.trans_eq (Scheme.Opens.range_ι _).symm))).obj
              (canonicalSheaf (normalizationOverField k (i ≫ sX) ≫ i ≫ sX) r)
          ∃ hω : SheafOfModules.IsInvertible _ _ ω,
            (@invertibleCurveDegree k _ _
                (ICν.subschemeι ≫ normalizationOverField k (i ≫ sX) ≫ i ≫ sX) _ hCν ω hω : ℚ) ≤
              (Divisor.toQDivisor K + B).intersectionNumber k sX (IC.subschemeι ≫ i) hC.le
                hklt.1.2.2 := by
  have hs := isClosed_singleton_of_range_subset f hf i hEs
  rcases Nat.lt_or_ge r 2 with hr | hr
  · obtain rfl : r = 1 := by omega
    refine ⟨1, one_ne_zero, fun c _ => ?_⟩
    intro IC ICν
    have hIC : IC = ⊥ := by
      haveI : IsEmpty (Fin (1 - 1)) := inferInstanceAs (IsEmpty (Fin 0))
      exact iSup_of_empty _
    have hICν : ICν = IC.comap (normalizationOverField k (i ≫ sX)) := rfl
    clear_value ICν IC
    subst hIC hICν
    exact case_one sX hklt hB sS f hfs hf s hs i hEs (by exact_mod_cast hEr)
      (by exact_mod_cast hfib)
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    haveI := isFinite_normalizationOverField k (i ≫ sX)
    haveI : IsNormal (normalizationSchemeOverField k (i ≫ sX)) :=
      Scheme.isNormal_normalizationScheme E _
    obtain ⟨V, hVi, hV⟩ := exists_opens_isIso_morphismRestrict_normalizationOverField sX i hEr
    have hind := fun (Q : MvPolynomial (Fin m × Fin (N + 1)) k) (hQ : Q ≠ 0) =>
      exists_eval_ne_zero_subadjunctionAt m sX hklt hB sS f hfs hf s hs i hEs hrn hEr hfib.le φ
        hφ (normalizationOverField k (i ≫ sX)) (Scheme.isBirational_normalization E _) V hV Q hQ
    obtain ⟨P₃, hP₃, hgood⟩ := exists_polynomial_forall_isSmoothCurveCut sX i (by omega) hEr φ hφ
      V (fun Q hQ => by
        obtain ⟨c, hc, hfin, -, h₀, h₁, h₂⟩ := hind Q hQ
        exact ⟨c, hc, hfin, h₀, h₁, h₂⟩)
    obtain ⟨P₄, hP₄, hconst⟩ := exists_polynomial_degrees_eq sX hklt.1.2.2 i hEr φ hφ
    obtain ⟨c₀, hc₀, -, hsub, hint, hintν, -⟩ := hind (P₃ * P₄) (mul_ne_zero hP₃ hP₄)
    rw [map_mul] at hc₀
    refine ⟨P₃ * P₄, mul_ne_zero hP₃ hP₄, fun c hc => ?_⟩
    rw [map_mul] at hc
    have h := hgood c (left_ne_zero_of_mul hc)
    have h₀ : IsGoodCurve sX i (normalizationOverField k (i ≫ sX)) (m + 1)
        (⨆ j, hyperplaneSection (i ≫ φ) (c₀ j)) :=
      ⟨hgood c₀ (left_ne_zero_of_mul hc₀), hint, hintν⟩
    obtain ⟨e₁, e₂⟩ := hconst c c₀ (right_ne_zero_of_mul hc) (right_ne_zero_of_mul hc₀) h
      h₀.toIsSmoothCurveCut
    refine ⟨h.dim_eq, h.dim_le, h.range_subset, h.smooth, h.isInvertible, ?_⟩
    change h.canonicalDegree ≤ h.intersectionNumber hklt.1.2.2
    rw [e₁, e₂]
    exact hsub h₀

end MMP.Fourfold

end
