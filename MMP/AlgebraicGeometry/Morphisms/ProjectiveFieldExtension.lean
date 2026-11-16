module

public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.PseudoCoherentByPseudoCoherentTwists
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.Components

/-!
# Foundations: base change, flat families, birational and projective morphisms, Cartier divisors

Five foundational facts used throughout the minimal model program.

* Let `k₀` be algebraically closed, `K / k₀` a field extension and `g : X ⟶ Y` a morphism of
  `k₀`-schemes of finite type with `Y` quasi-projective. An invertible module `L` on `X` is
  `g`-ample iff its pullback to `X_K = X ×_Y Y_K` is `g_K`-ample, and `g` is H-projective iff
  `g_K` is. Ampleness descends along the fpqc covering `Y_K ⟶ Y` (Stacks Tag 0D2P).
  Projectivity descends by writing `K` as the filtered union of its finitely generated
  `k₀`-subalgebras `A`, spreading a closed immersion `X_K ⟶ ℙⁿ_{Y_K}` out to some `Y_A`
  (Stacks Tags 01ZM, 01ZP), and specialising at a `k₀`-point of `Spec A`, which exists by the
  Nullstellensatz.
* For `π : X ⟶ S` flat, proper and of finite presentation over a connected base and `L`
  invertible, the Euler characteristics `χ(X_s, (L^{⊗ n})_s)` do not depend on `s`
  (Stacks Tag 0B9T). For a family of curves this makes the fibre degree
  `deg(L_s) = χ(X_s, L_s) - χ(X_s, 𝒪_{X_s})` constant.
* A proper birational morphism `f : X ⟶ Y` of varieties with `Y` normal is an isomorphism over
  a neighbourhood of every point of codimension at most one: there the local ring of `Y` is a
  valuation ring, so the valuative criterion lifts the point with isomorphic local rings.
  Hence the complement of the biregular locus has codimension at least two.
* A proper morphism from a quasi-projective variety to a variety is H-projective. Combine an
  immersion `j : Y ⟶ ℙⁿ_k` with `f` to get the immersion `(j, f) : Y ⟶ ℙⁿ_U`. It is proper
  because its composite with `ℙⁿ_U ⟶ U` is `f`, and so it is a closed immersion.
* A Weil divisor on a normal variety with support in the smooth locus is Cartier. The local
  rings along the support are regular, hence factorial, so each prime component is locally
  principal there.

## Main results

* `MMP.isRelativelyAmple_iff_and_isProjectiveMorphism_iff_of_fieldExtension`
* `MMP.fibreEulerCharacteristic_tensorPowModule_eq`
* `MMP.Mori.two_le_closedsCodimension_compl_biregularLocus`
* `MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety`
* `MMP.Mori.Divisor.isCartier_of_supp_subset_smoothLocus`

## Implementation notes

The base change of `X` to `K` is the fibre product `X ×_Y Y_K` along the projection
`Y_K ⟶ Y`. It is canonically isomorphic to `X ×_{k₀} Spec K`, and `g_K` is the second
projection. Relative ampleness is `Stacks.RelativeAmple.IsRelativelyAmple`.
Projectivity is H-projectivity, `AlgebraicGeometry.IsProjectiveMorphism`: a closed immersion
into some `ℙⁿ` over the base.

The flat-family statement assumes only that `π` is proper, flat and locally of finite
presentation. A projective morphism to a noetherian scheme, the setting of the source, has
these properties.

The projectivity criterion is stated over an arbitrary field rather than `ℂ`.

## References

* [Stacks Project, Tags 0D2P, 01ZM, 01ZP, 0B9T, 087S](https://stacks.math.columbia.edu)
* [R. Hartshorne, *Algebraic Geometry*, III, Theorem 9.9][hartshorne1977]
* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Notation 0.4
* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004]
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-! ### Relative ampleness and projectivity under extension of the ground field -/

namespace MMP

section FieldExtension

open RingedSpaceModuleAdjunction

/- These global instances of imported files unify against an arbitrary morphism and exhaust the
instance-search budget in the proofs of this section. -/
attribute [-instance]
  Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK
  Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK
  Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk
  Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth
  Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact
  AlgebraicGeometry.quasiSeparated_of_locallyOfFiniteType

/-- H-projectivity of an iterated base change `(X ×_Z Y) ×_Y T ⟶ T` is H-projectivity of the
single base change of `f` along any morphism `T ⟶ Z` equal to the composite `T ⟶ Y ⟶ Z`. -/
private theorem isProjectiveMorphism_pullback_snd_of_comp_eq {X Y Z T : Scheme.{u}} (f : X ⟶ Z)
    {a : Y ⟶ Z} {b : T ⟶ Y} {c : T ⟶ Z} (e : b ≫ a = c)
    (h : IsProjectiveMorphism (pullback.snd (pullback.snd f a) b)) :
    IsProjectiveMorphism (pullback.snd f c) :=
  (isProjectiveMorphism_pullback_snd_congr f e).mp (isProjectiveMorphism_pullback_snd_comp f a b h)

/-- The structure morphism of projective space is of finite presentation. -/
private theorem finitePresentation_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    FinitePresentation (projectiveSpaceOver n S ↘ S) := by
  have := isProper_projectiveSpaceOver n S
  have : IsSeparated (projectiveSpaceOver n S ↘ S) := this.toIsSeparated
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- `g` is H-projective as soon as its base change along a morphism `p` admitting a section is. -/
private theorem isProjectiveMorphism_of_pullback_snd_of_section {X Y T : Scheme.{u}} (g : X ⟶ Y)
    {p : T ⟶ Y} (s : Y ⟶ T) (hs : s ≫ p = 𝟙 Y)
    (h : IsProjectiveMorphism (pullback.snd g p)) : IsProjectiveMorphism g := by
  have h₁ : IsProjectiveMorphism (pullback.snd g (𝟙 Y)) :=
    isProjectiveMorphism_pullback_snd_of_comp_eq g hs (h.baseChange s)
  have h₂ : (asIso (pullback.fst g (𝟙 Y))).inv ≫ pullback.snd g (𝟙 Y) = g := by
    rw [Iso.inv_comp_eq, asIso_hom, pullback.condition, Category.comp_id]
  rw [← h₂]
  exact h₁.iso_comp (asIso (pullback.fst g (𝟙 Y))).symm

/-- H-projectivity spreads out along a cofiltered limit with affine transition maps: if `Z` is
of finite presentation over a stage `Dⱼ` and its base change to the limit is H-projective, then
its base change to some later stage is H-projective. -/
private theorem exists_isProjectiveMorphism_pullback_snd_of_isLimit
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (j : I) (Z : Over (D.obj j)) (hfp : FinitePresentation Z.hom)
    (hg : IsProjectiveMorphism (pullback.snd Z.hom (c.π.app j))) :
    ∃ (k : I) (h : k ⟶ j), IsProjectiveMorphism (pullback.snd Z.hom (D.map h)) := by
  obtain ⟨n, i, hi, hig⟩ := hg
  let P : Over (D.obj j) := Over.mk (projectiveSpaceOver n (D.obj j) ↘ D.obj j)
  have hPfp : FinitePresentation P.hom := finitePresentation_projectiveSpaceOver n (D.obj j)
  let π : c.pt ⟶ D.obj j := c.π.app j
  let ε : pullback (projectiveSpaceOver n (D.obj j) ↘ D.obj j) π ≅
      projectiveSpaceOver n c.pt :=
    projectiveSpaceOverBaseChangeIso n π
  have hε : ε.inv ≫ pullback.snd (projectiveSpaceOver n (D.obj j) ↘ D.obj j) π =
      projectiveSpaceOver n c.pt ↘ c.pt :=
    ε.inv_comp_eq.mpr (projectiveSpaceOverBaseChangeIso_hom_over n π).symm
  have hiε : (i ≫ ε.inv) ≫ pullback.snd (projectiveSpaceOver n (D.obj j) ↘ D.obj j) π =
      pullback.snd Z.hom π := by
    rw [Category.assoc, hε]
    exact hig
  let φ : (Over.pullback π).obj Z ⟶ (Over.pullback π).obj P := Over.homMk (i ≫ ε.inv) hiε
  have hφ : IsClosedImmersion φ.left := inferInstanceAs (IsClosedImmersion (i ≫ ε.inv))
  obtain ⟨k, h, ψ, α, β, -, -, hcomm⟩ :=
    exists_morphism_after_baseChange D c hc j Z P hfp hPfp φ
  have hlim : IsClosedImmersion ((Over.pullback (c.π.app k)).map ψ).left := by
    have hc' : α.hom.left ≫ φ.left =
        ((Over.pullback (c.π.app k)).map ψ).left ≫ β.hom.left :=
      congrArg Over.Hom.left hcomm
    have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso α).hom)
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso β).hom)
    have h3 : IsClosedImmersion (α.hom.left ≫ φ.left) := inferInstance
    rw [hc'] at h3
    exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ β.hom.left).mp h3
  let Zk := (Over.pullback (D.map h)).obj Z
  let Pk := (Over.pullback (D.map h)).obj P
  obtain ⟨_, _, _⟩ : FinitePresentation Zk.hom := finitePresentation_overPullback_obj _ Z hfp
  obtain ⟨-, _, _⟩ : FinitePresentation Pk.hom := finitePresentation_overPullback_obj _ P hPfp
  have : CompactSpace Zk.left := QuasiCompact.compactSpace_of_compactSpace Zk.hom
  have : QuasiSeparatedSpace Zk.left := quasiSeparatedSpace_of_quasiSeparated Zk.hom
  have : CompactSpace Pk.left := QuasiCompact.compactSpace_of_compactSpace Pk.hom
  have : QuasiSeparatedSpace Pk.left := quasiSeparatedSpace_of_quasiSeparated Pk.hom
  have : LocallyOfFiniteType ψ.left := by
    have : LocallyOfFiniteType (ψ.left ≫ Pk.hom) := by rw [Over.w ψ]; infer_instance
    exact locallyOfFiniteType_of_comp ψ.left Pk.hom
  obtain ⟨l, h', hcl⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc k Zk Pk ψ
  refine ⟨l, h' ≫ h, ?_⟩
  have hPl : IsProjectiveMorphism ((Over.pullback (D.map h')).obj Pk).hom :=
    ((isProjectiveMorphism_projectiveSpaceOver n (D.obj j)).baseChange (D.map h)).baseChange
      (D.map h')
  obtain ⟨N, ι, hι, hιf⟩ := hPl
  have hZl : IsProjectiveMorphism ((Over.pullback (D.map h')).obj Zk).hom := by
    refine ⟨N, ((Over.pullback (D.map h')).map ψ).left ≫ ι, inferInstance, ?_⟩
    rw [Category.assoc, hιf]
    exact Over.w ((Over.pullback (D.map h')).map ψ)
  exact isProjectiveMorphism_pullback_snd_of_comp_eq Z.hom (D.map_comp h' h).symm hZl

/-- A finitely generated subalgebra of an extension of an algebraically closed field `k₀` has a
`k₀`-point. -/
private theorem nonempty_algHom_fgSubalgebra {k₀ K : Type u} [Field k₀] [IsAlgClosed k₀]
    [Field K] [Algebra k₀ K] (i : FieldExtensionDescent.FGSubalgebra k₀ K) :
    Nonempty ((i : Subalgebra k₀ K) →ₐ[k₀] k₀) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (i : Subalgebra k₀ K)
  let : Field ((i : Subalgebra k₀ K) ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k₀ ((i : Subalgebra k₀ K) ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k₀ m) Ideal.Quotient.mk_surjective
  have : Module.Finite k₀ ((i : Subalgebra k₀ K) ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing k₀ ((i : Subalgebra k₀ K) ⧸ m)
  have : Algebra.IsIntegral k₀ ((i : Subalgebra k₀ K) ⧸ m) := Algebra.IsIntegral.of_finite _ _
  have hbij : Function.Bijective (algebraMap k₀ ((i : Subalgebra k₀ K) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k₀ ((i : Subalgebra k₀ K) ⧸ m)) hbij).symm.toAlgHom
    |>.comp (Ideal.Quotient.mkₐ k₀ m)⟩

open FieldExtensionDescent in
/-- H-projectivity descends along the extension `K / k₀` of an algebraically closed field, for a
morphism of `k₀`-schemes of finite type with quasi-projective target. -/
private theorem isProjectiveMorphism_of_baseChange
    (k₀ K : Type u) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K]
    {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k₀)) (g : X ⟶ Y)
    [LocallyOfFiniteType (g ≫ sY)] [QuasiCompact (g ≫ sY)]
    (hY : Stacks.HProjective.IsQuasiProjective sY)
    (h : IsProjectiveMorphism (pullback.snd g
      (pullback.fst sY (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))))) :
    IsProjectiveMorphism g := by
  obtain ⟨⟨_, _⟩, -⟩ := hY
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g sY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (g ≫ sY)
  have : IsNoetherian X := {}
  have : IsNoetherian Y := {}
  have : LocallyOfFinitePresentation g := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
    inferInstance
  have hgfp : FinitePresentation (Over.mk g).hom :=
    ⟨inferInstanceAs (LocallyOfFinitePresentation g), inferInstanceAs (QuasiCompact g),
      inferInstanceAs (QuasiSeparated g)⟩
  let φ : Spec (.of K) ⟶ Spec (.of k₀) := Spec.map (CommRingCat.ofHom (algebraMap k₀ K))
  let D := baseChangeDiagram k₀ K sY
  let c := (baseChangeLimitCone k₀ K sY).cone
  let p : ∀ i, D.obj i ⟶ Y := fun i => pullback.snd ((specDiagram k₀ K).obj i).hom sY
  have hp : ∀ {i j} (e : i ⟶ j), D.map e ≫ p j = p i := fun e =>
    Over.w ((Over.pullback sY).map ((specDiagram k₀ K).map e))
  have hcp : ∀ i, c.π.app i ≫ p i = pullback.snd φ sY := fun i =>
    Over.w ((Over.pullback sY).map ((specLimitCone k₀ K).cone.π.app i))
  have h' : IsProjectiveMorphism (pullback.snd g (pullback.snd φ sY)) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    exact isProjectiveMorphism_pullback_snd_comp _ _ _ (h.baseChange _)
  let j : (FGSubalgebra k₀ K)ᵒᵖ := Opposite.op ⟨⊥, Subalgebra.fg_bot⟩
  let Z : Over (D.obj j) := (Over.pullback (p j)).obj (Over.mk g)
  have hfp : FinitePresentation Z.hom := finitePresentation_overPullback_obj (p j) (Over.mk g) hgfp
  have hZ : IsProjectiveMorphism (pullback.snd Z.hom (c.π.app j)) := by
    change IsProjectiveMorphism (pullback.snd (pullback.snd g (p j)) (c.π.app j))
    rw [← pullbackLeftPullbackSndIso_hom_snd g (p j) (c.π.app j)]
    exact IsProjectiveMorphism.iso_comp _
      ((isProjectiveMorphism_pullback_snd_congr g (hcp j)).mpr h')
  obtain ⟨k, e, hk⟩ := exists_isProjectiveMorphism_pullback_snd_of_isLimit D c
    (baseChangeLimitCone k₀ K sY).isLimit j Z hfp hZ
  have hk' : IsProjectiveMorphism (pullback.snd g (p k)) :=
    isProjectiveMorphism_pullback_snd_of_comp_eq g (hp e) hk
  obtain ⟨ψ⟩ := nonempty_algHom_fgSubalgebra k.unop
  let A : Subalgebra k₀ K := k.unop
  let x : Spec (.of k₀) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    simp
  let s : Y ⟶ D.obj k := pullback.lift (sY ≫ x) (𝟙 Y) (by
    change (sY ≫ x) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = 𝟙 Y ≫ sY
    rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
  exact isProjectiveMorphism_of_pullback_snd_of_section g s (pullback.lift_snd _ _ _) hk'

/-- **Relative ampleness and projectivity are insensitive to extension of an algebraically
closed ground field.** For `g : X ⟶ Y` over `Spec k₀` with `X` of finite type and `Y`
quasi-projective over `k₀`, and a field extension `K / k₀`, an invertible module `L` on `X` is
`g`-ample iff its pullback to `X ×_Y (Y ×_{k₀} Spec K)` is ample relative to the base change of
`g`, and `g` is H-projective iff its base change is. -/
@[mmp "lem_mmp_field_extension_polarizations"]
public theorem isRelativelyAmple_iff_and_isProjectiveMorphism_iff_of_fieldExtension
    (k₀ K : Type u) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K]
    {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k₀)) (g : X ⟶ Y)
    [LocallyOfFiniteType (g ≫ sY)] [QuasiCompact (g ≫ sY)]
    (hY : Stacks.HProjective.IsQuasiProjective sY)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    let YK := pullback sY (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    let gK : pullback g (pullback.fst sY (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) ⟶ YK :=
      pullback.snd _ _
    (Stacks.RelativeAmple.IsRelativelyAmple g L ↔
        Stacks.RelativeAmple.IsRelativelyAmple gK
          ((modulePullback (pullback.fst g _).toLRSHom.toShHom).obj L)) ∧
      (IsProjectiveMorphism g ↔ IsProjectiveMorphism gK) := by
  intro YK gK
  let φ : Spec (.of K) ⟶ Spec (.of k₀) := Spec.map (CommRingCat.ofHom (algebraMap k₀ K))
  let q : YK ⟶ Y := pullback.fst sY φ
  have : Flat φ := Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField _) _)
  have : Surjective φ := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  refine ⟨?_, ⟨fun hg => hg.baseChange q, isProjectiveMorphism_of_baseChange k₀ K sY g hY⟩⟩
  have hcov : Presieve.ofArrows (fun _ : PUnit.{u + 1} => YK) (fun _ => q) ∈
      Scheme.fpqcPrecoverage Y := by
    rw [Presieve.ofArrows_pUnit]
    exact q.singleton_mem_fpqcPrecoverage
  exact (Stacks.Descent.isRelativelyAmple_iff_forall_of_fpqcCover hcov g L
    (fun _ => IsPullback.of_hasPullback g q)).trans ⟨fun h => h ⟨⟩, fun h _ => h⟩

end FieldExtension

/-! ### Euler characteristics in a flat proper family -/

section EulerCharacteristic

open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- An invertible module on a scheme flat over `S` is flat over `S`. -/
private theorem isFlatOver_of_isInvertibleModule {X S : Scheme.{u}} (π : X ⟶ S) [Flat π]
    (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F] :
    IsFlatOver π.toLRSHom.toShHom F := by
  have h0 : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf _ _).mp ‹_›
  have : F.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule F
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry F).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ F h0)
  obtain ⟨-, hfree⟩ :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae F).out 4 2).mp hflf
  intro x
  let := (π.stalkMap x).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (π x)) (X.presheaf.stalk x) := Flat.stalkMap π x
  have := hfree x
  let : Module (S.presheaf.stalk (π x)) (F.presheaf.stalk x) :=
    Module.compHom _ (π.stalkMap x).hom
  have : IsScalarTower (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x) := Module.Flat.of_free
  exact Module.Flat.trans (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x)

/-- The fibrewise Euler characteristic of an invertible module in a flat proper family of finite
presentation is locally constant. -/
private theorem isLocallyConstant_fibreEulerCharacteristic_of_isInvertibleModule
    {X S : Scheme.{u}} (π : X ⟶ S) [Flat π] [IsProper π] [LocallyOfFinitePresentation π]
    (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F] :
    IsLocallyConstant (fibreEulerCharacteristic π F) :=
  isLocallyConstant_fibreEulerCharacteristic π
    ⟨‹_›, inferInstanceAs (QuasiCompact π),
      @IsSeparated.instQuasiSeparated _ _ π IsProper.toIsSeparated⟩ F
    (@Stacks.Divisors.isFinitePresentation_of_isInvertible _ F
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        X.presheaf _ _).mp ‹_›))
    (isFlatOver_of_isInvertibleModule π F)

/-- On a fibre of dimension at most one, the degree of an invertible module is the difference
`χ(L_s) - χ(𝒪_{X_s})` of two fibrewise Euler characteristics. -/
private theorem invertibleCurveDegree_fiber_eq_sub {X S : Scheme.{u}} (π : X ⟶ S) [IsProper π]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (t : S)
    (hdim : topologicalKrullDim (π.fiber t) ≤ 1) :
    haveI : IsProper (π.fiberToSpecResidueField t) :=
      inferInstanceAs (IsProper (Limits.pullback.snd π (S.fromSpecResidueField t)))
    invertibleCurveDegree (S.residueField t) (π.fiberToSpecResidueField t) hdim
        ((Scheme.Modules.pullback (π.fiberι t)).obj L) =
      fibreEulerCharacteristic π L t -
        fibreEulerCharacteristic π (SheafOfModules.unit X.ringCatSheaf) t := by
  rw [show fibreEulerCharacteristic π (SheafOfModules.unit X.ringCatSheaf) t =
      eulerSum (S.residueField t) (π.fiberToSpecResidueField t)
        (SheafOfModules.unit (π.fiber t).ringCatSheaf) from
    eulerSum_congr _ _ (Scheme.Modules.pullbackUnitIso (π.fiberι t))]
  rfl

/-- **Euler characteristics are constant in a flat proper family over a connected base.** Let
`π : X ⟶ S` be flat, proper and locally of finite presentation with `S` connected, and let `L` be
an invertible `𝒪_X`-module. For every `n : ℤ` and all `s s' : S`,
`χ(X_s, (L^{⊗ n})_s) = χ(X_{s'}, (L^{⊗ n})_{s'})`. If moreover every fibre of `π` has dimension
at most one, the degree of `L` on the fibre `X_s` is independent of `s`. -/
@[mmp "lem_mmp_foundation_flat_projective_euler_characteristic"]
public theorem fibreEulerCharacteristic_tensorPowModule_eq {X S : Scheme.{u}} (π : X ⟶ S)
    [Flat π] [IsProper π] [LocallyOfFinitePresentation π] [ConnectedSpace S]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    (∀ (n : ℤ) (s s' : S),
      fibreEulerCharacteristic π (Stacks.Ample.tensorPowModule X L n) s =
        fibreEulerCharacteristic π (Stacks.Ample.tensorPowModule X L n) s') ∧
    ∀ (hdim : ∀ s : S, topologicalKrullDim (π.fiber s) ≤ 1) (s s' : S),
      haveI : IsProper (π.fiberToSpecResidueField s) :=
        inferInstanceAs (IsProper (Limits.pullback.snd π (S.fromSpecResidueField s)))
      haveI : IsProper (π.fiberToSpecResidueField s') :=
        inferInstanceAs (IsProper (Limits.pullback.snd π (S.fromSpecResidueField s')))
      invertibleCurveDegree (S.residueField s) (π.fiberToSpecResidueField s) (hdim s)
          ((Scheme.Modules.pullback (π.fiberι s)).obj L) =
        invertibleCurveDegree (S.residueField s') (π.fiberToSpecResidueField s') (hdim s')
          ((Scheme.Modules.pullback (π.fiberι s')).obj L) := by
  have hconst (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F] (s s' : S) :=
    (isLocallyConstant_fibreEulerCharacteristic_of_isInvertibleModule π F
      ).apply_eq_of_isPreconnected
      isPreconnected_univ (Set.mem_univ s) (Set.mem_univ s')
  refine ⟨fun n s s' => ?_, fun hdim s s' => ?_⟩
  · have := Stacks.Ample.isInvertibleModule_tensorPowModule X L n
    exact hconst _ s s'
  · rw [invertibleCurveDegree_fiber_eq_sub π L s, invertibleCurveDegree_fiber_eq_sub π L s',
      hconst L s s', hconst (SheafOfModules.unit X.ringCatSheaf) s s']

end EulerCharacteristic

/-! ### Proper morphisms out of quasi-projective varieties -/

/-- An immersion `j : Y ⟶ ℙⁿ_S` and a morphism `f : Y ⟶ U` over `S` give an immersion
`(j, f) : Y ⟶ ℙⁿ_S ×_S U ≅ ℙⁿ_U` over `U`. -/
private lemma exists_isImmersion_projectiveSpaceOver_comp_eq {S U Y : Scheme} {n : ℕ}
    (j : Y ⟶ projectiveSpaceOver n S) [IsImmersion j] (g : U ⟶ S) (f : Y ⟶ U)
    (h : j ≫ (projectiveSpaceOver n S ↘ S) = f ≫ g) :
    ∃ i : Y ⟶ projectiveSpaceOver n U, IsImmersion i ∧ i ≫ (projectiveSpaceOver n U ↘ U) = f := by
  let e := projectiveSpaceOverBaseChangeIso n g
  have : IsImmersion ((pullback.lift j f h ≫ e.hom) ≫ e.inv ≫ pullback.fst _ _) := by
    rwa [Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
  refine ⟨_, .of_comp (pullback.lift j f h ≫ e.hom) (e.inv ≫ pullback.fst _ _), ?_⟩
  rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, pullback.lift_snd]

/-- A proper morphism `f : Y ⟶ U` over a field `k`, from a quasi-projective variety `Y` to a
variety `U`, is projective: there is a closed immersion `Y ⟶ ℙⁿ_U` over `U`. -/
@[mmp "lem_mmp_foundation_laz_proper_quasiprojective_morphism_projective"]
public theorem isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety
    {k : Type u} [Field k] {Y U : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
    [IsQuasiProjectiveVariety k sY] [IsVariety k sU]
    (f : Y ⟶ U) [IsProper f] (hf : f ≫ sU = sY) :
    IsProjectiveMorphism f := by
  obtain ⟨-, n, j, hj, -, hjs⟩ := (isQuasiProjectiveVariety_iff_isHQuasiProjective k sY).1 ‹_›
  obtain ⟨i, hi, hif⟩ := exists_isImmersion_projectiveSpaceOver_comp_eq j sU f (hjs.trans hf.symm)
  have := isProper_projectiveSpaceOver n U
  have : IsProper (i ≫ (projectiveSpaceOver n U ↘ U)) := hif ▸ ‹IsProper f›
  have : IsProper i := .of_comp i (projectiveSpaceOver n U ↘ U)
  exact ⟨n, i, .of_isPreimmersion i i.isClosedMap.isClosed_range, hif⟩

end MMP

/-! ### Proper birational morphisms are isomorphisms in codimension one -/

namespace MMP.Mori

/-- If `U ↪ X' ⟶ X` is an open immersion for a nonempty open `U` of an irreducible `X'` and
`μ` is separated, then `μ` is an isomorphism over the image of `U`. -/
private theorem isBiregular_opensRange {X' X : Scheme.{u}} [IsIntegral X'] (μ : X' ⟶ X)
    [IsSeparated μ] (U : X'.Opens) (hU : (U : Set X').Nonempty) [IsOpenImmersion (U.ι ≫ μ)] :
    IsBiregular μ (U.ι ≫ μ).opensRange := by
  set V := (U.ι ≫ μ).opensRange
  have hUV : U ≤ μ ⁻¹ᵁ V := fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
  let e := (U.ι ≫ μ).isoOpensRange
  let s : V.toScheme ⟶ (μ ⁻¹ᵁ V).toScheme := e.inv ≫ X'.homOfLE hUV
  have hs : s ≫ μ ∣_ V = 𝟙 _ := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Category.id_comp]
    simp only [s, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [Iso.inv_comp_eq]
    exact ((U.ι ≫ μ).isoOpensRange_hom_ι).symm
  have : IsClosedImmersion (s ≫ μ ∣_ V) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (μ ∣_ V)
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (μ ⁻¹ᵁ V).toScheme := ⟨⟨x, hUV hx⟩⟩
  have : IsIntegral (μ ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (μ ⁻¹ᵁ V).ι
  have hrange : Set.range s = Set.univ :=
    IsClopen.eq_univ ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩
      ⟨_, Set.mem_range_self (e.hom ⟨x, hx⟩)⟩
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).mpr
    ⟨inferInstance, ⟨Set.range_eq_univ.mp hrange⟩⟩
  have : IsIso (s ≫ μ ∣_ V) := by rw [hs]; infer_instance
  change IsIso (μ ∣_ V)
  exact IsIso.of_isIso_comp_left s (μ ∣_ V)

/-- At a point of codimension at most one of a normal locally Noetherian integral scheme, the
local ring is a valuation ring. -/
private theorem valuationRing_stalk_of_coheight_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {y : X} (hy : Order.coheight y ≤ 1) :
    ValuationRing (X.presheaf.stalk y) := by
  rcases hy.lt_or_eq with h0 | h1
  · obtain rfl : y = genericPoint X := (Specializes.antisymm
      (Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0) (genericPoint_specializes y))
      (genericPoint_specializes y)).eq
    exact inferInstanceAs (ValuationRing X.functionField)
  · have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk h1
    infer_instance

/-- A proper birational morphism of integral schemes to a normal locally Noetherian scheme is an
isomorphism over a neighbourhood of every point of codimension at most one. -/
private theorem mem_biregularLocus_of_coheight_le_one {X' X : Scheme.{u}} [IsIntegral X']
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (μ : X' ⟶ X) [IsProper μ]
    (hμ : IsBirational μ) {y : X} (hy : Order.coheight y ≤ 1) : y ∈ biregularLocus μ := by
  have hgen : genericPoint X' ∈ genericPoints X' := by simp [genericPoints_eq_singleton]
  have hηX : μ (genericPoint X') = genericPoint X := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hμ.1.1 hgen
  have : IsDominant μ := ⟨(dense_iff_closure_eq.mpr (genericPoint_spec X)).mono
    (Set.singleton_subset_iff.mpr ⟨_, hηX⟩)⟩
  have : IsIso (μ.stalkMap (genericPoint X')) := hμ.2 _ hgen
  have hbij : Function.Bijective (functionFieldMap μ) :=
    ConcreteCategory.bijective_of_isIso
      ((X.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant μ).symm)).hom ≫
        μ.stalkMap (genericPoint X'))
  have := valuationRing_stalk_of_coheight_le_one hy
  obtain ⟨x', hx', hiso⟩ := MMP.Intersection.exists_isIso_stalkMap_of_valuationRing μ hbij y
  obtain ⟨U, hxU, hU⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap μ x'
    (by simp [irreducibleComponents_eq_singleton]) hiso
  exact le_biregularLocus (isBiregular_opensRange μ U ⟨x', hxU⟩) ⟨⟨x', hxU⟩, hx'⟩

/-- **A proper birational morphism to a normal variety is an isomorphism in codimension one.**
Let `f : X ⟶ Y` be a proper birational morphism of varieties over `k` with `Y` normal. Then the
closed complement of `MMP.Mori.biregularLocus f` has `MMP.Mori.closedsCodimension ≥ 2`. -/
@[mmp "lem_mmp_foundation_km_proper_birational_codimension_one"]
public theorem two_le_closedsCodimension_compl_biregularLocus {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [hY : IsVariety k sY]
    [hX : IsVariety k (f ≫ sY)] [IsNormal Y] [IsProper f] (hf : IsBirationalMorphism f) :
    2 ≤ closedsCodimension (biregularLocus f).compl := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  refine MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun y hy ↦ not_lt.mp fun h ↦ hy ?_
  exact mem_biregularLocus_of_coheight_le_one f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf) (Order.le_of_lt_succ h)

end MMP.Mori

/-! ### Divisors supported in the smooth locus -/

namespace MMP.Mori.Divisor

open DivisorWithCoeffs

/-- A point of the smooth locus of a morphism to a field has a factorial local ring. -/
private theorem uniqueFactorizationMonoid_stalk_of_mem_smoothLocus {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {x : X} (hx : x ∈ smoothLocus f) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  obtain ⟨V, hxV, hV⟩ := mem_smoothLocus_iff.1 hx
  have : Smooth (V.ι ≫ f) := hV
  have := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ f) ⟨x, hxV⟩
  have := IsRegularLocalRing.uniqueFactorizationMonoid (V.toScheme.presheaf.stalk ⟨x, hxV⟩)
  exact MulEquiv.uniqueFactorizationMonoid
    (V.stalkIso ⟨x, hxV⟩).commRingCatIsoToRingEquiv.toMulEquiv inferInstance

/-- A prime divisor whose generic point lies on a prime divisor `P` is `P`. -/
private theorem eq_of_genericPoint_mem_support {X : Scheme.{u}} {P E : MMP.Mori.PrimeDivisor X}
    (h : E.genericPoint ∈ P.support) : P = E := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at h
  by_contra hne
  have hlt : E.genericPoint < P.genericPoint :=
    lt_of_le_not_ge h fun hge => hne (h.antisymm hge).eq
  have := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint,
    MMP.Mori.PrimeDivisor.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- A regular section on an affine open `W` is, at the generic points of the components meeting
`W`, the value of a unit of the ring of rational functions. -/
private theorem exists_units_rationalFunctions_eq_germ {U : Scheme.{u}} [IsLocallyNoetherian U]
    [IsNormal U] {W : U.Opens} (hW : IsAffineOpen W) {f : Γ(U, W)} (hf : IsRegular f) :
    ∃ φ : (RationalFunctions U)ˣ, ∀ Z (hZ : componentGenericPoint U Z ∈ W),
      (φ : RationalFunctions U) Z = (U.presheaf.germ W _ hZ).hom f := by
  classical
  let u : ∀ Z : irreducibleComponents U, (U.presheaf.stalk (componentGenericPoint U Z))ˣ :=
    fun Z => if h : componentGenericPoint U Z ∈ W then
      (by
        letI := (RationalFunctions.isField_stalk U Z).toField
        exact (isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero
          (Stacks.Divisors.germ_mem_nonZeroDivisors hW hf _ h))).unit)
      else 1
  refine ⟨(RationalFunctions.unitsEquiv U).symm u, fun Z hZ => ?_⟩
  change ((u Z : (U.presheaf.stalk (componentGenericPoint U Z))ˣ) :
    U.presheaf.stalk (componentGenericPoint U Z)) = _
  simp only [u, hZ, ↓reduceDIte]
  rfl

/-- A nonzero local equation of a prime divisor at its generic point is prime. -/
private theorem prime_of_stalk_idealSheaf_eq_span_singleton {U : Scheme.{u}}
    (P : MMP.Mori.PrimeDivisor U)
    {g : U.presheaf.stalk P.genericPoint} (hg0 : g ≠ 0)
    (h : IdealSheafData.stalk P.idealSheaf P.genericPoint = Ideal.span {g}) : Prime g := by
  have := P.integral
  rw [← Ideal.span_singleton_prime hg0, ← h]
  obtain ⟨y', hy'⟩ : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    change P.genericPoint ∈ P.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  rw [← hy', ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
  exact RingHom.ker_isPrime _

/-- A prime divisor whose points all have factorial local rings is Cartier. -/
private theorem isCartier_single_of_uniqueFactorizationMonoid {U : Scheme.{u}}
    [IsLocallyNoetherian U] [IsNormal U] (P : MMP.Mori.PrimeDivisor U)
    (hUFD : ∀ x ∈ P.support, UniqueFactorizationMonoid (U.presheaf.stalk x)) :
    Divisor.IsCartier (Finsupp.single P 1 : Divisor U) := by
  classical
  have := P.integral
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf :=
    isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid P.idealSheaf
      P.codimension_one hUFD
  intro x
  by_cases hx : x ∈ P.support
  · obtain ⟨W, hW, hxW, f, hf, hspan⟩ :=
      Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
        P.idealSheaf hcart x
    have hgerm : ∀ y (hy : y ∈ W), IdealSheafData.stalk P.idealSheaf y =
        Ideal.span {(U.presheaf.germ W y hy).hom f} := by
      intro y hy
      rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf y ⟨W, hW⟩ hy, hspan,
        Ideal.map_span, Set.image_singleton]
    obtain ⟨φ, hφ⟩ := exists_units_rationalFunctions_eq_germ hW hf
    refine ⟨W, hxW, φ, ?_⟩
    rintro E ⟨y, hyE, hyW⟩
    have hηW : E.genericPoint ∈ W := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
      exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
    have hZW : componentGenericPoint U E.component ∈ W :=
      E.specializes_genericPoint.mem_open W.isOpen hηW
    have key : E.toComponent.hom ((U.presheaf.germ W _ hηW).hom f) =
        (φ : RationalFunctions U) E.component := by
      rw [hφ _ hZW]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    by_cases hEP : P = E
    · subst hEP
      rw [coeff_single_self]
      have hg0 := nonZeroDivisors.ne_zero (Stacks.Divisors.germ_mem_nonZeroDivisors hW hf _ hηW)
      have hprime := prime_of_stalk_idealSheaf_eq_span_singleton P hg0 (hgerm _ hηW)
      exact (P.ord_eq_one_of_irreducible hprime.irreducible key).symm
    · rw [coeff_single_of_ne hEP]
      have hnm : E.genericPoint ∉ P.support := fun h => hEP (eq_of_genericPoint_mem_support h)
      have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
        P.idealSheaf _).2 hnm
      rw [hgerm _ hηW, Ideal.span_singleton_eq_top] at htop
      exact (E.ord_eq_zero_of_isUnit htop key).symm
  · refine ⟨⟨(P.support)ᶜ, P.idealSheaf.support.isClosed.isOpen_compl⟩, hx, 1, ?_⟩
    rintro E ⟨y, hyE, hyP⟩
    rw [coeff_single_of_ne (by rintro rfl; exact hyP hyE)]
    simp

/-- A Weil divisor on a normal variety whose support lies in the smooth locus is Cartier. -/
@[mmp "lem_mmp_foundation_smooth_support_cartier"]
public theorem isCartier_of_supp_subset_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [IsVariety k f]
    (D : Divisor X) (hD : (D.supp : Set X) ⊆ smoothLocus f) : D.IsCartier := by
  classical
  rw [← Finsupp.sum_single D]
  refine Finset.sum_induction _ Divisor.IsCartier (fun _ _ => .add) Divisor.isCartier_zero ?_
  intro E hE
  have hDE : D.coeff E ≠ 0 := by simpa [coeff_apply] using Finsupp.mem_support_iff.1 hE
  simpa [Finsupp.smul_single] using (isCartier_single_of_uniqueFactorizationMonoid E fun x hx =>
    uniqueFactorizationMonoid_stalk_of_mem_smoothLocus (hD (support_subset_supp hDE hx))).zsmul
      (D E)

end MMP.Mori.Divisor

end
