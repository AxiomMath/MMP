module

public import Mathlib
public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ProperFibreDimensionVanishing
public import MMP.AlgebraicGeometry.Vanishing.EtaleKltAmpleGap
public import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
public import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible

section

/-!
## Proof of weak subadjunction

If not, choose `L_C` on `C` with `ν^* L_C ≅ ω_{Cᵛ}`; then `H¹(C, L_C) ≠ 0` and
`deg L_C > (K_X + B) · C`. Extend `L_C` to the fibre with large degrees on the other components,
and then to a line bundle `𝓛` on `X ×_S S'` for an elementary étale neighbourhood `(S', s')` of
`(S, s)`. With `m (K_X + B) = D` Cartier, the invertible sheaf `𝓜` with
`𝓛^{⊗ m} ≅ q^* 𝒪(D) ⊗ 𝓜` has positive degree on every one-dimensional component of the fibre:
on `C` because `m · deg L_C > m (K_X + B) · C`, on the others because the degrees of `𝓛` there
exceed those of `𝒪(D)`. So it is ample on the fibre (Nakai) and hence relatively ample over an
affine neighbourhood `W` of `s'` over which all fibres have dimension at most one. Klt ample-gap
vanishing gives `R^i f_* 𝓛 = 0` for `i > 0`, so `H¹(X_W, 𝓛) = 0`; since `H²(X_W, -)` vanishes on
quasi-coherent modules, the restriction `H¹(X_W, 𝓛) ⟶ H¹(C, L_C)` is onto, a contradiction.
-/

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace MMP.FourfoldProofs.FourfoldCurveFibreWeakSubadjunctionProof

attribute [local instance] HasDerivedCategory.standard MMP.Fourfold.isInvertibleModule_pullback

/-- The Krull dimension of a space is that of its image under a topological embedding. -/
private theorem topologicalKrullDim_range_eq_of_isEmbedding {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {i : Y → Z} (hi : Topology.IsEmbedding i) :
    topologicalKrullDim (Set.range i) = topologicalKrullDim Y :=
  hi.toHomeomorph.symm.isHomeomorph.topologicalKrullDim_eq

/-- **A curve in a space of dimension at most one is an irreducible component.** An irreducible
closed subset `Z` of dimension at least one in a space of dimension at most one is maximal among
irreducible subsets: a strictly larger irreducible closed subset would extend a chain of length
one in `Z` to a chain of length two. -/
private theorem mem_irreducibleComponents_of_one_le_topologicalKrullDim {F : Type*}
    [TopologicalSpace F] (hF : topologicalKrullDim F ≤ 1) {Z : Set F} (hZc : IsClosed Z)
    (hZi : IsIrreducible Z) (hZ1 : 1 ≤ topologicalKrullDim Z) : Z ∈ irreducibleComponents F := by
  refine ⟨hZi, fun Y hY hZY => ?_⟩
  by_contra hYZ
  have hYc : IsIrreducible (closure Y) := hY.closure
  have hlt : Z ⊂ closure Y := ⟨hZY.trans subset_closure, fun h => hYZ (subset_closure.trans h)⟩
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp (show ((1 : ℕ) : WithBot ℕ∞) ≤ _ from hZ1)
  have hemb : Topology.IsClosedEmbedding ((↑) : Z → F) := hZc.isClosedEmbedding_subtypeVal
  let φ : TopologicalSpace.IrreducibleCloseds Z → TopologicalSpace.IrreducibleCloseds F :=
    fun W => ⟨(↑) '' (W : Set Z), W.isIrreducible.image _ continuous_subtype_val.continuousOn,
      hemb.isClosedMap _ W.isClosed⟩
  have hφ : StrictMono φ := fun a b hab =>
    (Subtype.val_injective.image_strictMono : StrictMono ((↑) '' · : Set Z → Set F))
      (show (a : Set Z) < b from hab)
  let top : TopologicalSpace.IrreducibleCloseds F := ⟨closure Y, hYc, isClosed_closure⟩
  have hlast : φ l.last < top := by
    show (↑) '' (l.last : Set Z) < closure Y
    exact lt_of_le_of_lt (Subtype.coe_image_subset Z _) hlt
  have h := Order.LTSeries.length_le_krullDim ((l.map φ hφ).snoc top hlast)
  have hlen : ((l.map φ hφ).snoc top hlast).length = 2 := by
    change l.length + 1 = 2
    omega
  rw [hlen] at h
  have h2 := h.trans hF
  norm_cast at h2

/-- **The degree on a closed curve depends only on its ideal sheaf.** Two closed immersions with
the same kernel give the same degree to the restriction of an invertible sheaf. -/
private theorem invertibleCurveDegree_pullback_eq_of_ker_eq {κ : Type} [Field κ]
    {F Z Z' : Scheme.{0}} (sF : F ⟶ Spec (.of κ)) [IsProper sF] (i : Z ⟶ F) [IsClosedImmersion i]
    (i' : Z' ⟶ F) [IsClosedImmersion i'] (h : i.ker = i'.ker) (hd : topologicalKrullDim Z ≤ 1)
    (hd' : topologicalKrullDim Z' ≤ 1) (N : F.Modules)
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 N] :
    invertibleCurveDegree κ (i ≫ sF) hd ((Scheme.Modules.pullback i).obj N) =
      invertibleCurveDegree κ (i' ≫ sF) hd' ((Scheme.Modules.pullback i').obj N) := by
  have e1 := intersectionNumber_one_eq_invertibleCurveDegree κ sF i hd N
  have e2 := intersectionNumber_one_eq_invertibleCurveDegree κ sF i' hd' N
  have e3 := MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber κ sF i 1 hd
    (fun _ => N)
  have e4 := MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber κ sF i' 1 hd'
    (fun _ => N)
  have e5 := MMP.Mori.sheafIntersectionNumber_eq_of_ker_eq κ sF i i' h 1 hd hd' (fun _ => N)
  omega

/-- **The degree along a curve depends only on its ideal sheaf**, for a sheaf pulled back from
further away: `deg (i ≫ g)^* P = deg (i' ≫ g)^* P` when `i` and `i'` have the same kernel. -/
private theorem invertibleCurveDegree_pullback_comp_eq_of_ker_eq {κ : Type} [Field κ]
    {F Z Z' Y : Scheme.{0}} (sF : F ⟶ Spec (.of κ)) [IsProper sF] (i : Z ⟶ F)
    [IsClosedImmersion i] (i' : Z' ⟶ F) [IsClosedImmersion i'] (h : i.ker = i'.ker)
    (hd : topologicalKrullDim Z ≤ 1) (hd' : topologicalKrullDim Z' ≤ 1) (g : F ⟶ Y)
    (P : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 P] :
    invertibleCurveDegree κ (i ≫ sF) hd ((Scheme.Modules.pullback (i ≫ g)).obj P) =
      invertibleCurveDegree κ (i' ≫ sF) hd' ((Scheme.Modules.pullback (i' ≫ g)).obj P) := by
  haveI : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback i).obj P) :=
    isInvertibleModule_pullback i _
  haveI : SheafOfModules.IsInvertible Z'.presheaf Z'.ringCatSheaf.2
      ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback i').obj P) :=
    isInvertibleModule_pullback i' _
  exact (invertibleCurveDegree_eq_of_iso κ _ hd
    ((Scheme.Modules.pullbackComp i g).app P).symm).trans
    ((invertibleCurveDegree_pullback_eq_of_ker_eq sF i i' h hd hd' _).trans
      (invertibleCurveDegree_eq_of_iso κ _ hd' ((Scheme.Modules.pullbackComp i' g).app P)))

/-- **Nakai's criterion on a projective scheme of dimension at most one.** An invertible sheaf on
a projective scheme of dimension at most one over a field is ample if its degree on every
one-dimensional irreducible component, with its reduced structure, is positive. -/
private theorem isAmple_of_forall_mem_irreducibleComponents {κ : Type} [Field κ]
    {F : Scheme.{0}} (sF : F ⟶ Spec (.of κ)) [IsProper sF] (hproj : IsProjective sF)
    (hdim : topologicalKrullDim F ≤ 1) (N : F.Modules) [Stacks.Ample.IsInvertibleModule F N]
    (hpos : ∀ Z : TopologicalSpace.Closeds F, (Z : Set F) ∈ irreducibleComponents F →
      ∀ hZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = 1,
        0 < invertibleCurveDegree κ ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sF)
          hZ.le ((Scheme.Modules.pullback (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).obj
            N)) :
    Stacks.Ample.IsAmple F N := by
  refine MMP.Mori.isAmple_of_sheafSelfIntersectionNumber_pos_of_dim_pos κ sF hproj N
    fun V iV _ _ d hd hd0 => ?_
  have hrange : topologicalKrullDim (Set.range iV) = d := by
    rw [topologicalKrullDim_range_eq_of_isEmbedding iV.isEmbedding, hd]
  have hd1 : d = 1 := by
    have h := (topologicalKrullDim_subspace_le F (Set.range iV)).trans hdim
    rw [hrange] at h
    have : d ≤ 1 := by exact_mod_cast h
    omega
  subst hd1
  let Z : TopologicalSpace.Closeds F := ⟨Set.range iV, iV.isClosedEmbedding.isClosed_range⟩
  have hZc : (Z : Set F) ∈ irreducibleComponents F :=
    mem_irreducibleComponents_of_one_le_topologicalKrullDim hdim Z.isClosed
      (by
        change IsIrreducible (Set.range iV)
        simpa [Set.image_univ] using
          (IrreducibleSpace.isIrreducible_univ V).image iV iV.continuous.continuousOn)
      (by
        change 1 ≤ topologicalKrullDim (Set.range iV)
        rw [hrange]
        simp)
  have hker : iV.ker = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    exact TopologicalSpace.Closeds.ext (closure_eq_iff_isClosed.mpr Z.isClosed)
  have hZ1 : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = 1 := by
    rw [← topologicalKrullDim_range_eq_of_isEmbedding
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isEmbedding,
      Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hrange
  have h := hpos Z hZc hZ1
  have hV1 : topologicalKrullDim V ≤ 1 := hd.le
  have e1 := intersectionNumber_one_eq_invertibleCurveDegree κ sF iV hV1 N
  have e2 := MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber κ sF iV 1 hV1
    (fun _ => N)
  have e3 := invertibleCurveDegree_pullback_eq_of_ker_eq sF iV _ hker hV1 hZ1.le N
  unfold MMP.Mori.sheafSelfIntersectionNumber
  omega

/-- **The degree over an isomorphic base field.** If `ψ : k ⟶ κ` is an isomorphism of fields and
`Z` is proper of dimension at most one over `κ`, the degree of an invertible sheaf on `Z` is the
same over `κ` and over `k` through `Spec ψ`. -/
private theorem invertibleCurveDegree_comp_specMap {k κ : Type} [Field k] [Field κ]
    (ψ : CommRingCat.of k ⟶ CommRingCat.of κ) (hψ : Function.Bijective ψ) {Z : Scheme.{0}}
    (g : Z ⟶ Spec (.of κ)) [IsProper g] [IsProper (g ≫ Spec.map ψ)]
    (hdim : topologicalKrullDim Z ≤ 1) (L : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    invertibleCurveDegree k (g ≫ Spec.map ψ) hdim L = invertibleCurveDegree κ g hdim L := by
  letI : Algebra k κ := ψ.hom.toAlgebra
  have hcompat : ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ Spec.map ψ).appTop).hom =
      ((Scheme.ΓSpecIso (.of κ)).inv ≫ g.appTop).hom.comp (algebraMap k κ) := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
    rfl
  have h1 : Module.finrank k κ = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId k κ) hψ).toLinearEquiv.finrank_eq]
    exact Module.finrank_self k
  have hF : ∀ (F : Z.Modules) (n : ℕ),
      Module.finrank k (cohomologyOverField k (g ≫ Spec.map ψ) F n) =
        Module.finrank κ (cohomologyOverField κ g F n) := fun F n => by
    rw [finrank_cohomologyOverField_eq_finrank_mul k κ _ g hcompat F n, h1, one_mul]
  unfold invertibleCurveDegree
  congr 1
  · exact finsum_congr fun n => by rw [hF]
  · exact finsum_congr fun n => congrArg _ (congrArg _ (hF _ n))

/-- **A curve in a fibre lies in the scheme fibre.** A closed immersion `i : C ⟶ X` of a reduced
scheme whose image lies over a closed point `s` factors through a closed immersion into the
scheme fibre `X_s`. -/
private theorem exists_isClosedImmersion_comp_fst_eq {S X C : Scheme.{0}} (f : X ⟶ S) (s : S)
    (hs : IsClosed ({s} : Set S)) (i : C ⟶ X) [IsClosedImmersion i] [IsReduced C]
    (hCs : Set.range i ⊆ f ⁻¹' {s}) :
    ∃ iF : C ⟶ pointSettingFibre f s, IsClosedImmersion iF ∧
      iF ≫ Limits.pullback.fst f (S.fromSpecResidueField s) = i := by
  haveI : IsClosedImmersion (S.fromSpecResidueField s) :=
    isClosed_singleton_iff_isClosedImmersion.mp hs
  have hker : (S.fromSpecResidueField s).ker ≤ (i ≫ f).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range (S.fromSpecResidueField s),
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range (i ≫ f)]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono (closure_mono ?_)
    rw [Scheme.range_fromSpecResidueField]
    rintro _ ⟨c, rfl⟩
    exact hCs ⟨c, rfl⟩
  let c := IsClosedImmersion.lift (S.fromSpecResidueField s) (i ≫ f) hker
  have hc : c ≫ S.fromSpecResidueField s = i ≫ f := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Limits.pullback.lift i c hc.symm, ?_, Limits.pullback.lift_fst _ _ _⟩
  haveI : IsClosedImmersion (Limits.pullback.fst f (S.fromSpecResidueField s)) := inferInstance
  rw [IsClosedImmersion.iff_isProper_and_mono]
  refine ⟨?_, ?_⟩
  · haveI : IsProper (Limits.pullback.lift i c hc.symm ≫
        Limits.pullback.fst f (S.fromSpecResidueField s)) := by
      rw [Limits.pullback.lift_fst]
      infer_instance
    exact IsProper.of_comp _ (Limits.pullback.fst f (S.fromSpecResidueField s))
  · haveI : Mono (Limits.pullback.lift i c hc.symm ≫
        Limits.pullback.fst f (S.fromSpecResidueField s)) := by
      rw [Limits.pullback.lift_fst]
      infer_instance
    exact mono_of_mono _ (Limits.pullback.fst f (S.fromSpecResidueField s))

/-- **The degree of the gap bundle.** If `M^{⊗ m} ≅ q^* A ⊗ 𝓜` for invertible sheaves on `X'`,
then for `γ : V ⟶ X'` from a proper scheme of dimension at most one and `δ = γ ≫ q`,
`m · deg γ^* M = deg δ^* A + deg γ^* 𝓜`. -/
private theorem natCast_mul_invertibleCurveDegree_eq_add_of_iso {κ : Type} [Field κ]
    {V X' X : Scheme.{0}} (g : V ⟶ Spec (.of κ)) [IsProper g] (hdim : topologicalKrullDim V ≤ 1)
    (γ : V ⟶ X') (q : X' ⟶ X) (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A]
    (M : X'.Modules) [Stacks.Ample.IsInvertibleModule X' M] (m : ℕ)
    (𝓜 : X'.Modules) [Stacks.Ample.IsInvertibleModule X' 𝓜]
    (e : Stacks.Ample.tensorPowModule X' M (m : ℤ) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback q).obj A)).obj 𝓜) {δ : V ⟶ X} (hδ : γ ≫ q = δ) :
    (m : ℤ) * invertibleCurveDegree κ g hdim ((Scheme.Modules.pullback γ).obj M) =
      invertibleCurveDegree κ g hdim ((Scheme.Modules.pullback δ).obj A) +
        invertibleCurveDegree κ g hdim ((Scheme.Modules.pullback γ).obj 𝓜) := by
  subst hδ
  haveI : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      (Stacks.Ample.tensorPowModule X' M (m : ℤ)) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule _ _ _
  haveI hT : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback q).obj A)).obj 𝓜) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X'.presheaf X'.ringCatSheaf.2 _ _
  haveI hT' : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨V.toRingedSpace.presheaf, V.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback γ).obj ((Scheme.Modules.pullback q).obj A))).obj
          ((Scheme.Modules.pullback γ).obj 𝓜)) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible V.presheaf V.ringCatSheaf.2 _ _
  haveI : Stacks.Ample.IsInvertibleModule V ((Scheme.Modules.pullback γ).obj M) :=
    isInvertibleModule_pullback γ M
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((Scheme.Modules.pullback q ⋙ Scheme.Modules.pullback γ).obj A) :=
    isInvertibleModule_pullback γ ((Scheme.Modules.pullback q).obj A)
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      (Stacks.Ample.tensorPowModule V ((Scheme.Modules.pullback γ).obj M) (m : ℤ)) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule _ _ _
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      (Stacks.Ample.tensorPowModule V
        ((RingedSpaceModuleAdjunction.modulePullback γ.toLRSHom.toShHom).obj M) (m : ℤ)) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule _ _ _
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback γ.toLRSHom.toShHom).obj
        (Stacks.Ample.tensorPowModule X' M (m : ℤ))) :=
    isInvertibleModule_pullback γ _
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((Scheme.Modules.pullback γ).obj (Stacks.Ample.tensorPowModule X' M (m : ℤ))) :=
    isInvertibleModule_pullback γ _
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((Scheme.Modules.pullback γ).obj 𝓜) :=
    isInvertibleModule_pullback γ _
  haveI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((Scheme.Modules.pullback γ).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback q).obj A)).obj 𝓜)) :=
    isInvertibleModule_pullback γ _
  have e0 : invertibleCurveDegree κ g hdim
        ((Scheme.Modules.pullback γ).obj (Stacks.Ample.tensorPowModule X' M (m : ℤ))) =
      invertibleCurveDegree κ g hdim ((Scheme.Modules.pullback γ).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
          ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).obj
            ((Scheme.Modules.pullback q).obj A)).obj 𝓜)) :=
    invertibleCurveDegree_eq_of_iso κ g hdim ((Scheme.Modules.pullback γ).mapIso e)
  have e1 : invertibleCurveDegree κ g hdim ((Scheme.Modules.pullback γ).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
          ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).obj
            ((Scheme.Modules.pullback q).obj A)).obj 𝓜)) =
      invertibleCurveDegree κ g hdim
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
          ⟨V.toRingedSpace.presheaf, V.toRingedSpace.IsSheaf⟩).obj
            ((Scheme.Modules.pullback γ).obj ((Scheme.Modules.pullback q).obj A))).obj
            ((Scheme.Modules.pullback γ).obj 𝓜)) :=
    invertibleCurveDegree_eq_of_iso κ g hdim
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso γ ((Scheme.Modules.pullback q).obj A) 𝓜)
  have e2 := invertibleCurveDegree_tensorSheaf_eq_add κ g hdim
    ((Scheme.Modules.pullback γ).obj ((Scheme.Modules.pullback q).obj A))
    ((Scheme.Modules.pullback γ).obj 𝓜)
  have e3 : invertibleCurveDegree κ g hdim
        ((Scheme.Modules.pullback γ).obj ((Scheme.Modules.pullback q).obj A)) =
      invertibleCurveDegree κ g hdim ((Scheme.Modules.pullback (γ ≫ q)).obj A) :=
    invertibleCurveDegree_eq_of_iso κ g hdim ((Scheme.Modules.pullbackComp γ q).app A)
  have e4 : invertibleCurveDegree κ g hdim
        ((Scheme.Modules.pullback γ).obj (Stacks.Ample.tensorPowModule X' M (m : ℤ))) =
      invertibleCurveDegree κ g hdim
        (Stacks.Ample.tensorPowModule V ((Scheme.Modules.pullback γ).obj M) (m : ℤ)) :=
    invertibleCurveDegree_eq_of_iso κ g hdim
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso γ M m)
  have e5 := invertibleCurveDegree_tensorPowModule_natCast g hdim
    ((Scheme.Modules.pullback γ).obj M) m
  omega

/-- **Every invertible sheaf is divisible by an invertible sheaf.** For invertible `A` and `N`
there is an invertible `𝓜` with `N ≅ A ⊗ 𝓜`: tensoring with `A` is an equivalence, and a tensor
factor of an invertible sheaf is invertible. -/
private theorem exists_iso_sheafTensor {Y : Scheme.{0}} (A N : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] [Stacks.Ample.IsInvertibleModule Y N] :
    ∃ (𝓜 : Y.Modules) (_ : Stacks.Ample.IsInvertibleModule Y 𝓜),
      Nonempty (N ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj A).obj 𝓜) := by
  obtain ⟨F, hF, ⟨a⟩⟩ := (inferInstance : Stacks.Ample.IsInvertibleModule Y A).exists_tensorFunctor
  have : F.IsEquivalence := hF
  let e : N ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj A).obj (F.objPreimage N) :=
    (F.objObjPreimageIso N).symm ≪≫
      (a.uniqueIso (AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal
        Y.presheaf _ A)).app _
  refine ⟨F.objPreimage N, ?_, ⟨e⟩⟩
  have hN : Stacks.Ample.IsInvertibleModule Y
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (F.objPreimage N)).obj A) :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
      (e ≪≫ Stacks.SheafOfModules.Invertible.tensorProductBraiding _ _ A (F.objPreimage N))
  exact Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_isInvertible _ _ _ A hN

/-- The degree does not see how the structure morphism is written. -/
private theorem invertibleCurveDegree_congr_hom {κ : Type} [Field κ] {V : Scheme.{0}}
    {g g' : V ⟶ Spec (.of κ)} [IsProper g] [IsProper g'] (h : g = g')
    (hdim : topologicalKrullDim V ≤ 1) (L : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 L] :
    invertibleCurveDegree κ g hdim L = invertibleCurveDegree κ g' hdim L := by
  subst h
  rfl

/-- **The fibre of the base change over the distinguished point.** For an elementary étale
neighbourhood `(U, u)` of `(S, s)`, the fibre of `X ×_S U ⟶ U` over `u` maps to the fibre `X_s`
compatibly with `MMP.Fourfold.localEtaleFibreMap`. -/
private theorem exists_comp_localEtaleFibreMap_eq_fiberι {S X : Scheme.{0}} (f : X ⟶ S) {s : S}
    (U : ElementaryEtaleNeighborhood S s) :
    ∃ θ : (Limits.pullback.snd f U.obj.toBase).fiber U.obj.point ⟶ pointSettingFibre f s,
      θ ≫ localEtaleFibreMap f U =
        (Limits.pullback.snd f U.obj.toBase).fiberι U.obj.point := by
  haveI : IsIso U.obj.residueFieldMap := U.property
  have hsec : Spec.map U.obj.residueFieldMap ≫ elementaryNeighborhoodSection U =
      U.obj.scheme.fromSpecResidueField U.obj.point := by
    rw [elementaryNeighborhoodSection, ← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  have hfac := Scheme.Hom.fiber_fac (Limits.pullback.snd f U.obj.toBase) U.obj.point
  refine ⟨Limits.pullback.lift
    ((Limits.pullback.snd f U.obj.toBase).fiberι U.obj.point ≫ Limits.pullback.fst f U.obj.toBase)
    ((Limits.pullback.snd f U.obj.toBase).fiberToSpecResidueField U.obj.point ≫
      Spec.map U.obj.residueFieldMap) ?_, ?_⟩
  · rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hfac, Category.assoc,
      Category.assoc, ← hsec, Category.assoc, elementaryNeighborhoodSection_comp_toBase]
  · apply Limits.pullback.hom_ext
    · rw [Category.assoc, localEtaleFibreMap_fst, Limits.pullback.lift_fst]
    · rw [Category.assoc, localEtaleFibreMap_snd, ← Category.assoc, Limits.pullback.lift_snd,
        Category.assoc, hsec, hfac]

/-- **Fibre dimension under a square with an embedded source.** If `a ≫ g = g' ≫ b` with `a` a
topological embedding, the fibre of `g'` over `y'` embeds into the fibre of `g` over `b y'`. -/
private theorem topologicalKrullDim_fiber_le_of_comp_eq {X Y X' Y' : Scheme.{0}} (g : X ⟶ Y)
    (g' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y) (hab : a ≫ g = g' ≫ b)
    (ha : Topology.IsEmbedding a) (y' : Y') :
    topologicalKrullDim (g'.fiber y') ≤ topologicalKrullDim (g.fiber (b y')) := by
  have hmem : ∀ x : g'.fiber y', a (g'.fiberι y' x) ∈ g ⁻¹' {b y'} := fun x => by
    have h1 : g (a (g'.fiberι y' x)) = b (g' (g'.fiberι y' x)) := by
      rw [← Scheme.Hom.comp_apply, hab, Scheme.Hom.comp_apply]
    have h2 : g'.fiberι y' x ∈ g' ⁻¹' {y'} := g'.range_fiberι y' ▸ Set.mem_range_self x
    rw [Set.mem_preimage, Set.mem_singleton_iff] at h2 ⊢
    rw [h1, h2]
  let Φ : g'.fiber y' → g ⁻¹' {b y'} := fun x => ⟨a (g'.fiberι y' x), hmem x⟩
  have hΦ : Topology.IsInducing Φ :=
    Topology.IsInducing.codRestrict (ha.isInducing.comp (g'.fiberι y').isEmbedding.isInducing) _
  calc topologicalKrullDim (g'.fiber y') ≤ topologicalKrullDim (g ⁻¹' {b y'}) :=
        hΦ.topologicalKrullDim_le
    _ = topologicalKrullDim (g.fiber (b y')) :=
        (g.fiberHomeo (b y')).symm.isHomeomorph.topologicalKrullDim_eq

/-- **Restriction to a curve in a family with one-dimensional fibres.** Let `g : Y ⟶ W` be proper
over an affine base, with all fibres of dimension at most one, and let `𝓛` be quasi-coherent on
`Y` with `R¹ g_* 𝓛 = 0`. Then `H¹(C, 𝓛|_C) = 0` for every closed subscheme `C` of `Y`: since `W`
is affine, `H¹(Y, 𝓛) = 0`, and `H²(Y, -)` vanishes on quasi-coherent modules, so
`H¹(Y, 𝓛) ⟶ H¹(Y, j_* j^* 𝓛) = H¹(C, j^* 𝓛)` is onto. -/
private theorem isZero_rightDerivedPlus_one_pullback_of_isZero_rightDerived_one
    {Y W C : Scheme.{0}} (g : Y ⟶ W) [IsProper g] [IsAffine W]
    (hfib : ∀ w : W, topologicalKrullDim (g.fiber w) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (𝓛 : Y.Modules) [𝓛.IsQuasicoherent]
    (h1 : Limits.IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj 𝓛))
    (j : C ⟶ Y) [IsClosedImmersion j] :
    Limits.IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections C).rightDerivedPlus 1).obj
      ((Scheme.Modules.pullback j).obj 𝓛)) := by
  haveI : IsSeparated g := inferInstance
  haveI : QuasiSeparated g := IsSeparated.instQuasiSeparated g
  have hY1 : Limits.IsZero
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections Y).rightDerivedPlus 1).obj 𝓛) :=
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_cohomology_iff_isZero_rightDerivedPlus_pushforward
      g 1 𝓛).2 (h1.of_iso
        ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward g) 1).app 𝓛).symm)
  let η : 𝓛 ⟶ (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj 𝓛) :=
    (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app 𝓛
  haveI := Stacks.ClosedImmersion.epi_unit_app j 𝓛
  have hS : (ShortComplex.mk (Limits.kernel.ι η) η (Limits.kernel.condition η)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (Limits.kernelIsKernel η))
      (Limits.mono_of_isLimit_fork (c := Limits.Fork.ofι _ _) (Limits.kernelIsKernel η))
      (Stacks.ClosedImmersion.epi_unit_app j 𝓛)
  have hqc2 :
      ((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj 𝓛)).IsQuasicoherent :=
    haveI : QuasiSeparated j := IsSeparated.instQuasiSeparated j
    ProperCoherentFiniteType.isQuasicoherent_pushforward j _
      (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback j 𝓛)
  have hqc : (Limits.kernel η).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_kernel η inferInstance hqc2
  have hK := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_cohomology_of_affine_base
    (d := 1) g hfib (Limits.kernel η) 2 (by norm_num)
  have hQ := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerivedPlus_one_of_shortExact
    hS hY1 hK
  have hQ' : Limits.IsZero
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections Y).rightDerived 1).obj
      ((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj 𝓛))) :=
    hQ.of_iso ((Stacks.DerivedIndexing.rightDerivedIso _ 1).app _)
  have hC := hQ'.of_iso (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward j _ 1).symm
  refine Limits.IsZero.of_iso ?_ ((Stacks.DerivedIndexing.rightDerivedIso _ 1).app _).symm
  rw [ModuleCat.isZero_iff_subsingleton] at hC ⊢
  exact hC

/-- **The cohomological core.** Let `X' = X ×_S T` for an étale `g : T ⟶ S`, with projections
`q` and `f'`, let `φ : F ⟶ X'` be a monomorphism onto the fibre of `f'` over `u ∈ T` (in the
sense that the fibre maps to `F` over `X'`), with `dim F ≤ 1`, and let `𝓛`, `𝓜` be line bundles
on `X'` with `𝓛^{⊗ m} ≅ q^* 𝒪_X(D) ⊗ 𝓜`, where `D = m (K_X + B)`, such that `φ^* 𝓜` is ample.
Then `H¹(C, 𝓛|_C) = 0` for every closed subscheme `C` of `F` proper over `k`. -/
private theorem isZero_rightDerivedPlus_one_of_isAmple_of_isPullback
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {S : Scheme.{0}} (sS : S ⟶ Spec (.of k))
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f)
    {T X' : Scheme.{0}} (g : T ⟶ S) [Etale g] (q : X' ⟶ X) (f' : X' ⟶ T)
    (hpb : IsPullback q f' f g) (u : T) {F : Scheme.{0}} (φ : F ⟶ X') [Mono φ]
    (hφ : ∀ x, f' (φ x) = u) (θ : f'.fiber u ⟶ F) (hθ : θ ≫ φ = f'.fiberι u)
    (hdim : topologicalKrullDim F ≤ 1)
    (𝓛 : X'.Modules) [Stacks.Ample.IsInvertibleModule _ 𝓛]
    (m : ℕ) (hm : 0 < m) (D : Divisor X) (hD : D.IsCartier)
    (hDm : Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor K + B))
    (𝓜 : X'.Modules) [Stacks.Ample.IsInvertibleModule _ 𝓜]
    (e : Stacks.Ample.tensorPowModule _ 𝓛 (m : ℤ) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback q).obj D.divisorialSheaf)).obj 𝓜)
    (hamp : Stacks.Ample.IsAmple F ((Scheme.Modules.pullback φ).obj 𝓜))
    {C : Scheme.{0}} (j : C ⟶ F) [IsClosedImmersion j] [IsProper (j ≫ φ ≫ q ≫ sX)] :
    Limits.IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections C).rightDerivedPlus 1).obj
      ((Scheme.Modules.pullback (j ≫ φ)).obj 𝓛)) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hpb inferInstance
  -- the fibre of `f'` over `u` embeds into `F`
  have hθemb : Topology.IsEmbedding θ := by
    have h : Topology.IsEmbedding (θ ≫ φ) := by
      rw [hθ]
      exact (f'.fiberι u).isEmbedding
    rw [Scheme.Hom.comp_base, TopCat.coe_comp] at h
    exact Topology.IsEmbedding.of_comp θ.continuous φ.continuous h
  have hamp' : Stacks.Ample.IsAmple (f'.fiber u)
      (Stacks.AmpleLocallyClosed.pullbackModule (f'.fiberι u) 𝓜) := by
    haveI : CompactSpace (f'.fiber u) :=
      QuasiCompact.compactSpace_of_compactSpace (f'.fiberToSpecResidueField u)
    have h1 := Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding θ _
      hamp (Or.inr (Or.inr (Or.inr ⟨inferInstance, hθemb⟩)))
    refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mp h1
    exact (Scheme.Modules.pullbackComp θ φ).app 𝓜 ≪≫ eqToIso (by rw [hθ]; rfl)
  have hdim' : topologicalKrullDim (f'.fiber u) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    hθemb.isInducing.topologicalKrullDim_le.trans hdim
  obtain ⟨V1, hu1, hV1⟩ :=
    Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre f' 𝓜 u hamp'
  obtain ⟨V2, hu2, -, -, -, -, -, hV2⟩ :=
    Stacks.AlgebraicGeometry.ProperFibreDimension.exists_affineOpen_fiberDimension_le f' u 1 hdim'
  -- klt ample-gap vanishing over `V1`
  have hvan : Limits.IsZero (((Scheme.Modules.pushforward (f' ∣_ V1)).rightDerived 1).obj
      ((Scheme.Modules.pullback (f' ⁻¹ᵁ V1).ι).obj 𝓛)) := by
    have hpb1 : IsPullback ((f' ⁻¹ᵁ V1).ι ≫ q) (f' ∣_ V1) f (V1.ι ≫ g) :=
      (isPullback_morphismRestrict f' V1).flip.paste_horiz hpb
    have e1 : Stacks.Ample.tensorPowModule _ ((Scheme.Modules.pullback (f' ⁻¹ᵁ V1).ι).obj 𝓛)
        (m : ℤ) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
          ⟨(f' ⁻¹ᵁ V1).toScheme.toRingedSpace.presheaf,
            (f' ⁻¹ᵁ V1).toScheme.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback ((f' ⁻¹ᵁ V1).ι ≫ q)).obj D.divisorialSheaf)).obj
          ((Scheme.Modules.pullback (f' ⁻¹ᵁ V1).ι).obj 𝓜) :=
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f' ⁻¹ᵁ V1).ι 𝓛 m).symm ≪≫
        (Scheme.Modules.pullback (f' ⁻¹ᵁ V1).ι).mapIso e ≪≫
        Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso (f' ⁻¹ᵁ V1).ι _ _ ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
          ⟨(f' ⁻¹ᵁ V1).toScheme.toRingedSpace.presheaf,
            (f' ⁻¹ᵁ V1).toScheme.toRingedSpace.IsSheaf⟩).mapIso
          ((Scheme.Modules.pullbackComp (f' ⁻¹ᵁ V1).ι q).app D.divisorialSheaf)).app _
    haveI := hD.isInvertibleModule_divisorialSheaf
    exact isZero_rightDerived_pushforward_of_isPullback_etale_of_isKltPair sX hklt hB sS f hfs
      hf.isProjective (V1.ι ≫ g) ((f' ⁻¹ᵁ V1).ι ≫ q) (f' ∣_ V1) hpb1 _ m hm D hD hDm _
      (IsRelativelyAmple.of_stacks _ _ hV1) e1 1 one_pos
  -- an affine neighbourhood `W` of `u` inside `V1 ∩ V2`
  obtain ⟨W, hWaff, huW, hWle⟩ := exists_isAffineOpen_mem_and_subset
    (X := V1.toScheme) (x := ⟨u, hu1⟩) (U := V1.ι ⁻¹ᵁ V2) (show V1.ι ⟨u, hu1⟩ ∈ V2 from hu2)
  haveI : IsAffine W := hWaff
  have hR1 : Limits.IsZero (((Scheme.Modules.pushforward ((f' ∣_ V1) ∣_ W)).rightDerived 1).obj
      ((Scheme.Modules.pullback ((f' ∣_ V1) ⁻¹ᵁ W).ι).obj
        ((Scheme.Modules.pullback (f' ⁻¹ᵁ V1).ι).obj 𝓛))) := by
    have h := (ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme (f' ∣_ V1) W 1).app
      ((Scheme.Modules.pullback (f' ⁻¹ᵁ V1).ι).obj 𝓛)
    have hz := (Scheme.Modules.restrictFunctor W.ι).map_isZero hvan
    refine (hz.of_iso h).of_iso ?_
    exact ((Scheme.Modules.pushforward ((f' ∣_ V1) ∣_ W)).rightDerived 1).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback _).app _).symm
  have hfibW : ∀ w : W, topologicalKrullDim (((f' ∣_ V1) ∣_ W).fiber w) ≤
      ((1 : ℕ) : WithBot ℕ∞) := by
    intro w
    refine (topologicalKrullDim_fiber_le_of_comp_eq (f' ∣_ V1) _ _ W.ι
      (morphismRestrict_ι _ _).symm (Scheme.Hom.isOpenEmbedding _).isEmbedding w).trans ?_
    refine (topologicalKrullDim_fiber_le_of_comp_eq f' _ _ V1.ι
      (morphismRestrict_ι _ _).symm (Scheme.Hom.isOpenEmbedding _).isEmbedding _).trans ?_
    exact hV2 _ (hWle w.2)
  -- the curve `C` as a closed subscheme of `X'_W`
  haveI : IsProper ((f' ∣_ V1) ∣_ W) := inferInstance
  obtain ⟨jW, hjW, hjWfac⟩ : ∃ jW : C ⟶ ((f' ∣_ V1) ⁻¹ᵁ W).toScheme, IsClosedImmersion jW ∧
      jW ≫ ((f' ∣_ V1) ⁻¹ᵁ W).ι ≫ (f' ⁻¹ᵁ V1).ι = j ≫ φ := by
    have h1 : Set.range (j ≫ φ) ⊆ Set.range (f' ⁻¹ᵁ V1).ι := by
      rintro _ ⟨c, rfl⟩
      rw [Scheme.Opens.range_ι]
      show f' (φ (j c)) ∈ V1
      rw [hφ]
      exact hu1
    let l1 := IsOpenImmersion.lift (f' ⁻¹ᵁ V1).ι (j ≫ φ) h1
    have hl1 : l1 ≫ (f' ⁻¹ᵁ V1).ι = j ≫ φ := IsOpenImmersion.lift_fac _ _ _
    have h2 : Set.range l1 ⊆ Set.range ((f' ∣_ V1) ⁻¹ᵁ W).ι := by
      rintro _ ⟨c, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (f' ∣_ V1) (l1 c) ∈ W
      have hc : (f' ∣_ V1) (l1 c) = ⟨u, hu1⟩ := by
        apply Subtype.ext
        change V1.ι ((f' ∣_ V1) (l1 c)) = u
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, ← Scheme.Hom.comp_apply,
          ← Category.assoc, hl1]
        exact hφ (j c)
      rw [hc]
      exact huW
    let l2 := IsOpenImmersion.lift ((f' ∣_ V1) ⁻¹ᵁ W).ι l1 h2
    have hl2 : l2 ≫ ((f' ∣_ V1) ⁻¹ᵁ W).ι = l1 := IsOpenImmersion.lift_fac _ _ _
    have hfac : l2 ≫ ((f' ∣_ V1) ⁻¹ᵁ W).ι ≫ (f' ⁻¹ᵁ V1).ι = j ≫ φ := by
      rw [← Category.assoc, hl2, hl1]
    refine ⟨l2, ?_, hfac⟩
    rw [IsClosedImmersion.iff_isProper_and_mono]
    refine ⟨?_, ?_⟩
    · have hsep : ((f' ∣_ V1) ⁻¹ᵁ W).ι ≫ (f' ⁻¹ᵁ V1).ι ≫ q ≫ sX =
          ((f' ∣_ V1) ∣_ W) ≫ W.ι ≫ V1.ι ≫ g ≫ sS := by
        rw [← hfs, ← Category.assoc q, hpb.w, Category.assoc, ← Category.assoc (f' ⁻¹ᵁ V1).ι,
          ← morphismRestrict_ι, Category.assoc, ← Category.assoc ((f' ∣_ V1) ⁻¹ᵁ W).ι,
          ← morphismRestrict_ι, Category.assoc]
      haveI : IsProper (l2 ≫ ((f' ∣_ V1) ⁻¹ᵁ W).ι ≫ (f' ⁻¹ᵁ V1).ι ≫ q ≫ sX) := by
        rw [← Category.assoc, ← Category.assoc, Category.assoc l2, hfac, Category.assoc]
        infer_instance
      haveI : IsSeparated (((f' ∣_ V1) ⁻¹ᵁ W).ι ≫ (f' ⁻¹ᵁ V1).ι ≫ q ≫ sX) := by
        rw [hsep]
        haveI : IsSeparated (W.ι ≫ V1.ι ≫ g ≫ sS) :=
          Scheme.instIsSeparatedOfIsSeparated _
        haveI : IsSeparated ((f' ∣_ V1) ∣_ W) := IsProper.toIsSeparated
        exact IsSeparated.instCompScheme _ _
      exact IsProper.of_comp l2 (((f' ∣_ V1) ⁻¹ᵁ W).ι ≫ (f' ⁻¹ᵁ V1).ι ≫ q ≫ sX)
    · haveI : Mono (l2 ≫ ((f' ∣_ V1) ⁻¹ᵁ W).ι ≫ (f' ⁻¹ᵁ V1).ι) := by
        rw [hfac]
        infer_instance
      exact mono_of_mono l2 (((f' ∣_ V1) ⁻¹ᵁ W).ι ≫ (f' ⁻¹ᵁ V1).ι)
  haveI := hjW
  haveI : ((Scheme.Modules.pullback ((f' ∣_ V1) ⁻¹ᵁ W).ι).obj
      ((Scheme.Modules.pullback (f' ⁻¹ᵁ V1).ι).obj 𝓛)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have key := isZero_rightDerivedPlus_one_pullback_of_isZero_rightDerived_one _ hfibW _ hR1 jW
  refine key.of_iso ((Stacks.Cohomology.AffineBase.moduleGlobalSections C).rightDerivedPlus 1
    |>.mapIso ?_)
  exact (Scheme.Modules.pullbackComp jW _).app _ ≪≫
    (Scheme.Modules.pullbackComp (jW ≫ ((f' ∣_ V1) ⁻¹ᵁ W).ι) _).app 𝓛 ≪≫
    eqToIso (by rw [Category.assoc, hjWfac]) |>.symm

/-- **The core vanishing.** In the setting of the theorem, an invertible sheaf on `C` whose
degree exceeds `(K_X + B) · C` has `H¹(C, L) = 0`. -/
private theorem subsingleton_cohomologyOverField_one_of_intersectionNumber_lt
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f)
    (s : S) (hs : IsClosed ({s} : Set S)) (hfib : topologicalKrullDim (f ⁻¹' {s}) ≤ 1)
    {C : Scheme.{0}} (i : C ⟶ X) [IsClosedImmersion i] [AlgebraicGeometry.IsCurve k (i ≫ sX)]
    (hCs : Set.range i ⊆ f ⁻¹' {s}) (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L]
    [IsProper (i ≫ sX)]
    (hlt : (Divisor.toQDivisor K + B).intersectionNumber k sX i
        (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := i ≫ sX)).le
        hklt.1.2.2 <
      (invertibleCurveDegree k (i ≫ sX)
        (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := i ≫ sX)).le L : ℚ)) :
    Subsingleton (cohomologyOverField k (i ≫ sX) L 1) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hdC := AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := i ≫ sX)
  -- the residue field at the closed point `s` is `k`
  let ψ : CommRingCat.of k ⟶ CommRingCat.of (S.residueField s) :=
    (residueFieldIsoBase sS s hs).inv
  have hψ : Function.Bijective ψ := ConcreteCategory.bijective_of_isIso _
  have hψs : Spec.map ψ = S.fromSpecResidueField s ≫ sS := SpecMap_residueFieldIsoBase_inv sS s hs
  -- the scheme fibre
  set sF := Limits.pullback.snd f (S.fromSpecResidueField s) with hsF
  haveI : IsProper sF := isProper_pointSettingFibre f hf s
  have hproj : IsProjective sF := (hf.baseChange _).isProjective
  have hdimF : topologicalKrullDim (pointSettingFibre f s) ≤ 1 :=
    (f.fiberHomeo s).isEmbedding.isInducing.topologicalKrullDim_le.trans hfib
  haveI : IsReduced C := inferInstance
  obtain ⟨iF, hiF, hiFfac⟩ := exists_isClosedImmersion_comp_fst_eq f s hs i hCs
  haveI := hiF
  -- the component `Z` of the fibre carried by `C`
  let Z : TopologicalSpace.Closeds (pointSettingFibre f s) :=
    ⟨Set.range iF, iF.isClosedEmbedding.isClosed_range⟩
  have hrange : topologicalKrullDim (Set.range iF) = 1 := by
    rw [topologicalKrullDim_range_eq_of_isEmbedding iF.isEmbedding, hdC]
  have hZ : (Z : Set (pointSettingFibre f s)) ∈ irreducibleComponents (pointSettingFibre f s) :=
    mem_irreducibleComponents_of_one_le_topologicalKrullDim hdimF Z.isClosed
      (by
        change IsIrreducible (Set.range iF)
        rw [← Set.image_univ]
        exact (IrreducibleSpace.isIrreducible_univ C).image iF iF.continuous.continuousOn)
      hrange.ge
  let ιZ := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  have hker : iF.ker = ιZ.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    exact TopologicalSpace.Closeds.ext (closure_eq_iff_isClosed.mpr Z.isClosed)
  let a : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ C :=
    IsClosedImmersion.lift iF ιZ hker.le
  have ha : a ≫ iF = ιZ := IsClosedImmersion.lift_fac _ _ _
  let c : C ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    IsClosedImmersion.lift ιZ iF hker.ge
  have hc : c ≫ ιZ = iF := IsClosedImmersion.lift_fac _ _ _
  have hca : c ≫ a = 𝟙 C := by
    rw [← cancel_mono iF, Category.assoc, ha, hc, Category.id_comp]
  -- a Cartier multiple `D = m (K + B)`
  let hQ := hklt.1.2.2
  let m := (Divisor.toQDivisor K + B).cartierIndex hQ
  have hm : 0 < m := QDivisor.cartierIndex_pos hQ
  let hDC := QDivisor.isCartierDivisor_cartierIndex_smul hQ
  let D := hDC.toDivisor
  have hD : D.IsCartier := hDC.isCartier_toDivisor
  have hDm : Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor K + B) := by
    rw [hDC.toQDivisor_toDivisor, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
  haveI := hD.isInvertibleModule_divisorialSheaf
  have hmI : (m : ℚ) * (Divisor.toQDivisor K + B).intersectionNumber k sX i hdC.le hQ =
      (invertibleCurveDegree k (i ≫ sX) hdC.le
        ((Scheme.Modules.pullback i).obj D.divisorialSheaf) : ℚ) :=
    QDivisor.cartierIndex_mul_intersectionNumber k sX i hdC.le _ hQ
  -- the degrees of `𝒪_X(D)` on the components of the fibre
  let fst₀ := Limits.pullback.fst f (S.fromSpecResidueField s)
  let deg' : TopologicalSpace.Closeds (pointSettingFibre f s) → ℤ := fun Z' =>
    haveI := isProper_subschemeι_comp_pointSettingFibre f hf s Z'
    if h : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z').subscheme = 1 then
      invertibleCurveDegree (S.residueField s)
        ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫ sF) h.le
        ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫
          fst₀)).obj D.divisorialSheaf)
    else 0
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ Z' : TopologicalSpace.Closeds (pointSettingFibre f s),
      (Z' : Set (pointSettingFibre f s)) ∈ irreducibleComponents (pointSettingFibre f s) →
        deg' Z' < N := by
    haveI : LocallyOfFiniteType sF := IsProper.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (pointSettingFibre f s) := LocallyOfFiniteType.isLocallyNoetherian
        sF
    haveI : CompactSpace (pointSettingFibre f s) := MMP.Fourfold.compactSpace_of_isProper sF
    haveI : IsNoetherian (pointSettingFibre f s) := {}
    have hfin : {Z' : TopologicalSpace.Closeds (pointSettingFibre f s) |
        (Z' : Set (pointSettingFibre f s)) ∈ irreducibleComponents (pointSettingFibre f s)}.Finite
            :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.preimage
        SetLike.coe_injective.injOn
    obtain ⟨b, hb⟩ := (hfin.image deg').bddAbove
    refine ⟨b.toNat + 1, fun Z' hZ' => ?_⟩
    have := hb ⟨Z', hZ', rfl⟩
    omega
  -- extend `L` to an elementary étale neighbourhood, with degree `≥ N` on the other components
  obtain ⟨U, M, hM, ⟨eM⟩, hMdeg⟩ := exists_elementaryEtaleNeighborhood_extension_of_component
    sS f hf s hdimF Z hZ ((Scheme.Modules.pullback a).obj L) N
  haveI := hM
  let φ := localEtaleFibreMap f U
  let q := Limits.pullback.fst f U.obj.toBase
  let f' := Limits.pullback.snd f U.obj.toBase
  have hφq : φ ≫ q = fst₀ := localEtaleFibreMap_fst f U
  have hs' : φ ≫ f' = sF ≫ elementaryNeighborhoodSection U := localEtaleFibreMap_snd f U
  haveI : Mono (elementaryNeighborhoodSection U) := by
    haveI : IsIso U.obj.residueFieldMap := U.property
    unfold elementaryNeighborhoodSection
    infer_instance
  haveI : Mono φ := ⟨fun u v huv => by
    apply Limits.pullback.hom_ext
    · have h : u ≫ φ ≫ q = v ≫ φ ≫ q := by rw [reassoc_of% huv]
      rwa [hφq] at h
    · have h : u ≫ φ ≫ f' = v ≫ φ ≫ f' := by rw [reassoc_of% huv]
      rw [hs', ← Category.assoc, ← Category.assoc] at h
      exact (cancel_mono _).mp h⟩
  have hφ : ∀ x, f' (φ x) = U.obj.point := by
    intro x
    have h1 : f' (φ x) = elementaryNeighborhoodSection U (sF x) := by
      rw [← Scheme.Hom.comp_apply, hs', Scheme.Hom.comp_apply]
    have h2 : elementaryNeighborhoodSection U (sF x) ∈
        Set.range (U.obj.scheme.fromSpecResidueField U.obj.point) := by
      rw [elementaryNeighborhoodSection, Scheme.Hom.comp_apply]
      exact Set.mem_range_self _
    rw [Scheme.range_fromSpecResidueField] at h2
    rw [h1]
    exact h2
  obtain ⟨θ, hθ⟩ := exists_comp_localEtaleFibreMap_eq_fiberι f U
  -- the gap bundle `𝓜` with `M^{⊗ m} ≅ q^* 𝒪_X(D) ⊗ 𝓜`
  haveI : Stacks.Ample.IsInvertibleModule _ (Stacks.Ample.tensorPowModule _ M (m : ℤ)) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule _ _ _
  obtain ⟨𝓜, h𝓜, ⟨e⟩⟩ := exists_iso_sheafTensor ((Scheme.Modules.pullback q).obj D.divisorialSheaf)
    (Stacks.Ample.tensorPowModule _ M (m : ℤ))
  haveI := h𝓜
  -- `M` restricts to `L` on `C`
  have hcφ : c ≫ ιZ ≫ φ = iF ≫ φ := by rw [← Category.assoc, hc]
  let eL : (Scheme.Modules.pullback (iF ≫ φ)).obj M ≅ L :=
    (pullbackCompIso hcφ M).symm ≪≫ (Scheme.Modules.pullback c).mapIso eM ≪≫
      pullbackCompIso hca L ≪≫ (Scheme.Modules.pullbackId C).app L
  -- the degrees on `C`, read over `k`
  have hcomp : (iF ≫ sF) ≫ Spec.map ψ = i ≫ sX := by
    rw [hψs, Category.assoc, ← Category.assoc sF, hsF, ← Limits.pullback.condition,
      Category.assoc, ← Category.assoc iF, hiFfac, hfs]
  haveI : IsProper ((iF ≫ sF) ≫ Spec.map ψ) := by
    rw [hcomp]
    infer_instance
  have hkκ : ∀ (P : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 P],
      invertibleCurveDegree (S.residueField s) (iF ≫ sF) hdC.le P =
        invertibleCurveDegree k (i ≫ sX) hdC.le P := fun P _ =>
    (invertibleCurveDegree_comp_specMap ψ hψ (iF ≫ sF) hdC.le P).symm.trans
      (invertibleCurveDegree_congr_hom hcomp hdC.le P)
  -- the gap bundle is ample on the fibre
  have hamp : Stacks.Ample.IsAmple (pointSettingFibre f s) ((Scheme.Modules.pullback φ).obj 𝓜) := by
    refine @isAmple_of_forall_mem_irreducibleComponents (S.residueField s) _ _ sF
      (isProper_pointSettingFibre f hf s) hproj hdimF _ _ fun Z' hZ' h1 => ?_
    haveI := isProper_subschemeι_comp_pointSettingFibre f hf s Z'
    show 0 < invertibleCurveDegree (S.residueField s) ((Scheme.IdealSheafData.vanishingIdeal
        Z').subschemeι ≫ sF) h1.le
          ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι)).obj
              ((Scheme.Modules.pullback φ).obj 𝓜))
    have e1 : invertibleCurveDegree (S.residueField s) ((Scheme.IdealSheafData.vanishingIdeal
        Z').subschemeι ≫ sF) h1.le
          ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι)).obj
              ((Scheme.Modules.pullback φ).obj 𝓜)) =
        invertibleCurveDegree (S.residueField s) ((Scheme.IdealSheafData.vanishingIdeal
            Z').subschemeι ≫ sF) h1.le
          ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫ φ)).obj
              𝓜) :=
      invertibleCurveDegree_eq_of_iso _ _ _ ((Scheme.Modules.pullbackComp
          (Scheme.IdealSheafData.vanishingIdeal Z').subschemeι φ).app 𝓜)
    rw [e1]
    have hgap := natCast_mul_invertibleCurveDegree_eq_add_of_iso (κ := S.residueField s)
      ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫ sF) h1.le
      ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫ φ) q D.divisorialSheaf M m 𝓜 e
      (δ := (Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫ fst₀)
      (by rw [Category.assoc, hφq])
    by_cases hZZ : Z' = Z
    · subst Z'
      -- on the component of `C` the degrees are those on `C`, and `deg 𝒪(D)|_C < m · deg L`
      rw [invertibleCurveDegree_pullback_comp_eq_of_ker_eq (κ := S.residueField s) sF _ iF
          hker.symm h1.le hdC.le φ M,
        invertibleCurveDegree_eq_of_iso _ _ _ eL, hkκ L,
        invertibleCurveDegree_pullback_comp_eq_of_ker_eq (κ := S.residueField s) sF _ iF
          hker.symm h1.le hdC.le fst₀ D.divisorialSheaf,
        invertibleCurveDegree_eq_of_iso _ _ _
          ((Scheme.Modules.pullbackCongr hiFfac).app D.divisorialSheaf),
        hkκ] at hgap
      have hlt' : invertibleCurveDegree k (i ≫ sX) hdC.le
          ((Scheme.Modules.pullback i).obj D.divisorialSheaf) <
          (m : ℤ) * invertibleCurveDegree k (i ≫ sX) hdC.le L := by
        have h := mul_lt_mul_of_pos_left hlt (show (0 : ℚ) < m by exact_mod_cast hm)
        rw [hmI] at h
        exact_mod_cast h
      omega
    · -- on the other components, the degree of `M` is at least `N`
      have h3 := hMdeg Z' hZ' hZZ h1
      have h4 := hN Z' hZ'
      have h5 : deg' Z' = invertibleCurveDegree (S.residueField s)
          ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫ sF) h1.le
          ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫
              fst₀)).obj D.divisorialSheaf) := dif_pos h1
      have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
      nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℤ) ≤ m),
        mul_le_mul_of_nonneg_right hm1 (Int.natCast_nonneg N)]
  have hiq : iF ≫ φ ≫ q = i := by rw [hφq, hiFfac]
  haveI : IsProper (iF ≫ φ ≫ q ≫ sX) := by
    rw [← Category.assoc φ, ← Category.assoc iF, hiq]
    infer_instance
  have hvan := isZero_rightDerivedPlus_one_of_isAmple_of_isPullback sX hklt hB sS f hfs hf
    U.obj.toBase q f' (IsPullback.of_hasPullback _ _) U.obj.point φ hφ θ hθ hdimF M m hm D hD hDm
    𝓜 e hamp iF
  have h1 : Limits.IsZero
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections C).rightDerivedPlus 1).obj L) :=
    hvan.of_iso (((Stacks.Cohomology.AffineBase.moduleGlobalSections C).rightDerivedPlus 1).mapIso
      eL.symm)
  have h2 := h1.of_iso ((Stacks.DerivedIndexing.rightDerivedIso _ 1).app L)
  rw [ModuleCat.isZero_iff_subsingleton] at h2
  exact h2

/-- **The dualizing sheaf of the normalization descends.** There is an invertible sheaf `L` on
`C` with `H¹(C, L) ≠ 0` and `deg L = deg Ω_{Cᵛ/k}`. -/
private theorem exists_invertible_nontrivial_cohomology_degree_eq
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {C : Scheme.{0}} (i : C ⟶ X) [IsClosedImmersion i] [AlgebraicGeometry.IsCurve k (i ≫ sX)]
    [IsProper (i ≫ sX)] :
    haveI : IsProper (normalizationOverField k (i ≫ sX) ≫ i ≫ sX) :=
      isProper_normalizationOverField_comp k (i ≫ sX)
    ∃ (L : C.Modules) (_ : Stacks.Ample.IsInvertibleModule C L),
      Nontrivial (cohomologyOverField k (i ≫ sX) L 1) ∧
      invertibleCurveDegree k (i ≫ sX)
          (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := i ≫ sX)).le L =
        @invertibleCurveDegree k _ _ (normalizationOverField k (i ≫ sX) ≫ i ≫ sX) _
          ((topologicalKrullDim_normalizationSchemeOverField k (i ≫ sX)).trans
            (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := i ≫ sX))).le
          (Scheme.Hom.relativeDifferentials (normalizationOverField k (i ≫ sX) ≫ i ≫ sX))
          (isInvertible_relativeDifferentials_normalization_comp (i ≫ sX) _) := by
  haveI : IsProper (normalizationOverField k (i ≫ sX) ≫ i ≫ sX) :=
    isProper_normalizationOverField_comp k (i ≫ sX)
  haveI : AlgebraicGeometry.IsProjectiveVariety k (i ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff k _).2 ⟨inferInstance, by
      obtain ⟨d, j, hj, hjf⟩ := AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f :=
          sX)
      exact ⟨d, i ≫ j, inferInstance, by rw [Category.assoc, hjf]⟩⟩
  obtain ⟨-, ⟨L, hL, ⟨e⟩⟩, hH⟩ := liftsInvertible_normalization (i ≫ sX)
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := i ≫ sX))
  refine ⟨L, hL, hH L ⟨e⟩, ?_⟩
  set ν := normalizationOverField k (i ≫ sX)
  haveI : AlgebraicGeometry.IsCurve k (ν ≫ i ≫ sX) := isCurve_normalizationOverField_comp k (i ≫ sX)
  haveI : IsDominant ν := isDominant_normalizationOverField k (i ≫ sX)
  haveI : IsFinite ν := isFinite_normalizationOverField k (i ≫ sX)
  have hC1 := AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := i ≫ sX)
  have hnc : ¬ ∃ y : C, ∀ x, ν.base x = y := by
    rintro ⟨y, hy⟩
    have hsurj : Set.range ν.base = Set.univ := by
      have hcl : IsClosed (Set.range ν.base) := ν.isClosedMap.isClosed_range
      rw [← hcl.closure_eq]
      exact ν.denseRange.closure_range
    haveI : Subsingleton C := ⟨fun a b => by
      obtain ⟨a', rfl⟩ : a ∈ Set.range ν.base := hsurj ▸ Set.mem_univ a
      obtain ⟨b', rfl⟩ : b ∈ Set.range ν.base := hsurj ▸ Set.mem_univ b
      rw [hy, hy]⟩
    haveI : Subsingleton (TopologicalSpace.IrreducibleCloseds C) :=
      ⟨fun Z₁ Z₂ => SetLike.coe_injective
        (Z₁.isIrreducible.nonempty.eq_univ.trans Z₂.isIrreducible.nonempty.eq_univ.symm)⟩
    have h0 : topologicalKrullDim C ≤ 0 := Order.krullDim_nonpos_of_subsingleton
    rw [hC1] at h0
    exact absurd h0 (by decide)
  have hdeg1 : degreeOver ν = 1 := by
    have hbir := Scheme.isBirational_normalization C
      (finite_irreducibleComponents_of_locallyOfFiniteType k (i ≫ sX))
    have hgen : genericPoint (normalizationSchemeOverField k (i ≫ sX)) ∈
        genericPoints (normalizationSchemeOverField k (i ≫ sX)) := by
      rw [genericPoints_eq_singleton]
      rfl
    haveI := hbir.isIso_stalkMap _ hgen
    have hb : Function.Bijective (dominantFunctionFieldMap ν) := by
      unfold dominantFunctionFieldMap
      dsimp only
      rw [Stacks.Chow.stalkMap_cast_target]
      exact ConcreteCategory.bijective_of_isIso _
    letI := (dominantFunctionFieldMap ν).toAlgebra
    unfold degreeOver
    rw [← (AlgEquiv.ofBijective (Algebra.ofId C.functionField _) hb).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have key := invertibleCurveDegree_pullback_eq_degreeOver_mul k (ν ≫ i ≫ sX) (i ≫ sX) ν rfl
    hnc L
  rw [hdeg1, Nat.cast_one, one_mul] at key
  rw [← key]
  exact @invertibleCurveDegree_eq_of_iso k _ _ _ _ _ _ _ _
    (isInvertible_relativeDifferentials_normalization_comp (i ≫ sX) _) e

end MMP.FourfoldProofs.FourfoldCurveFibreWeakSubadjunctionProof

end

section

/-!
# Weak subadjunction for a curve in a fibre of dimension at most one

Let `(X, B)` be a klt pair with `B` an effective `ℚ`-divisor and `X` a projective variety over an
algebraically closed field `k` of characteristic zero, and let `f : X ⟶ S` be a projective
morphism of `k`-schemes. If the fibre of `f` over a closed point `s` has dimension at most one,
then every integral curve `C` in that fibre, with normalization `ν : Cᵛ ⟶ C`, satisfies
`(K_X + B) · C ≥ deg ω_{Cᵛ}`.

If the inequality failed, an invertible sheaf `L_C` on `C` with `ν^* L_C ≅ ω_{Cᵛ}` would extend,
after an étale base change around `s`, to a line bundle `𝒪(A)` with `A - (K_X + B)` ample over
the base; klt ample-gap vanishing would give `R¹f_* 𝒪(A) = 0`, hence `H¹(C, L_C) = 0`, which
contradicts `H¹(C, L_C) ≠ 0`.

## Main results

* `MMP.Fourfold.invertibleCurveDegree_relativeDifferentials_normalization_le_intersectionNumber`:
  the inequality above.

## Implementation notes

* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero.
* The curve is a closed immersion `i : C ⟶ X` of a curve over `k` (`AlgebraicGeometry.IsCurve`
  for `i ≫ sX`) whose image lies in the fibre `f⁻¹(s)`. Since the fibre has dimension at most
  one, such a curve is an irreducible component of the fibre, so this is the source's
  "integral curve component".
* The normalization is `AlgebraicGeometry.normalizationOverField`, a smooth projective curve,
  and `ω_{Cᵛ}` is its sheaf of differentials `Ω_{Cᵛ/k}`; its degree is
  `AlgebraicGeometry.invertibleCurveDegree`.
* `(K_X + B) · C` is `MMP.Mori.QDivisor.intersectionNumber` of the `ℚ`-Cartier divisor
  `K_X + B` along `i`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Fourfold

open MMP.FourfoldProofs.FourfoldCurveFibreWeakSubadjunctionProof in
/-- **Weak subadjunction for a curve in a fibre of dimension at most one.** Let `(X, B)` be a klt
pair with `B ≥ 0` and `X` projective over an algebraically closed field `k` of characteristic
zero, and let `f : X ⟶ S` be a projective morphism of `k`-schemes, `S` locally of finite type.
Let `s ∈ S` be a closed point whose fibre `f⁻¹(s)` has dimension at most one, and let
`i : C ⟶ X` be an integral curve contained in `f⁻¹(s)`, with normalization `ν : Cᵛ ⟶ C`. Then
`deg Ω_{Cᵛ/k} ≤ (K_X + B) · C`. -/
@[mmp "lem_fourfold_curve_fibre_weak_subadjunction"]
public theorem invertibleCurveDegree_relativeDifferentials_normalization_le_intersectionNumber
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {S : Scheme.{0}} (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (f : X ⟶ S) (hfs : f ≫ sS = sX) (hf : IsProjectiveMorphism f)
    (s : S) (hs : IsClosed ({s} : Set S)) (hfib : topologicalKrullDim (f ⁻¹' {s}) ≤ 1)
    {C : Scheme.{0}} (i : C ⟶ X) [IsClosedImmersion i] [AlgebraicGeometry.IsCurve k (i ≫ sX)]
    (hCs : Set.range i ⊆ f ⁻¹' {s}) :
    haveI : IsProper (normalizationOverField k (i ≫ sX) ≫ i ≫ sX) :=
      isProper_normalizationOverField_comp k (i ≫ sX)
    (@invertibleCurveDegree k _ _ (normalizationOverField k (i ≫ sX) ≫ i ≫ sX) _
        ((topologicalKrullDim_normalizationSchemeOverField k (i ≫ sX)).trans
          (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := i ≫ sX))).le
        (Scheme.Hom.relativeDifferentials (normalizationOverField k (i ≫ sX) ≫ i ≫ sX))
        (isInvertible_relativeDifferentials_normalization_comp (i ≫ sX) _) : ℚ) ≤
      (Divisor.toQDivisor K + B).intersectionNumber k sX i
        (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := i ≫ sX)).le
        hklt.1.2.2 := by
  obtain ⟨L, hL, hnt, hdeg⟩ := exists_invertible_nontrivial_cohomology_degree_eq sX i
  by_contra hlt
  rw [not_le, ← hdeg] at hlt
  have := subsingleton_cohomologyOverField_one_of_intersectionNumber_lt sX hklt hB sS f hfs hf s
    hs hfib i hCs L hlt
  exact false_of_nontrivial_of_subsingleton (cohomologyOverField k (i ≫ sX) L 1)

end MMP.Fourfold

end
