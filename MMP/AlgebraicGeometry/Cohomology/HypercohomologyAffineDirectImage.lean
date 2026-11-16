module

public import MMP.AlgebraicGeometry.Cohomology.HodgeDegenerationSummand
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalTransport

/-!
# Hypercohomology along a direct image by an affine morphism

Let `f : V' ⟶ V` and `π : V ⟶ T` be morphisms of schemes. A sheaf of `(π ∘ f)⁻¹𝒪_T`-modules
`M` on `V'` has a direct image `f_* M`, a sheaf of `π⁻¹𝒪_T`-modules on `V` with sections
`(f_* M)(W) = M(f⁻¹ W)`, the scalars acting through `π⁻¹𝒪_T ⟶ f_*(π ∘ f)⁻¹𝒪_T`. If `f` is
affine and the terms of a complex `L` of `(π ∘ f)⁻¹𝒪_T`-modules are quasi-coherent
`𝒪_{V'}`-modules, then

`ℍ^j(V, f_* L) ≅ ℍ^j(V', L)`

as `Γ(T, 𝒪_T)`-modules, for schemes `V`, `V'` with affine diagonal. Indeed, for an affine open
cover `𝒰` of `V` the preimage `f⁻¹𝒰` is an affine open cover of `V'`, both hypercohomologies are
computed by Čech complexes [Stacks, Tag 01XD], and the Čech complex of `f_* L` for `𝒰` is the
Čech complex of `L` for `f⁻¹𝒰`, term by term. This is the comparison along the finite cover in
the proof that the fractional logarithmic complex degenerates at `E₁`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.relDirectImage`: the direct image
  `Mod((π ∘ f)⁻¹𝒪_T) ⥤ Mod(π⁻¹𝒪_T)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.siteCx`: the sections of a complex of sheaves of
  `h⁻¹𝒪_T`-modules over a category over the opens, read over `Γ(T, ⊤)`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.nonempty_Hc_iso_homology_cechTot`: hypercohomology is
  the cohomology of the elementwise total Čech complex of an affine cover, for complexes with
  quasi-coherent terms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.nonempty_Hc_relDirectImage_iso`:
  `ℍ^j(V, f_* L) ≅ ℍ^j(V', L)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.nonempty_Hc_single0_relDirectImage_iso`:
  `H^j(V, f_* M) ≅ H^j(V', M)` for a quasi-coherent `M`.

## Implementation notes

The direct image is the pushforward along the canonical morphism of ringed spaces
`(V', (π ∘ f)⁻¹𝒪_T) ⟶ (V, π⁻¹𝒪_T)` (`Stacks.DeRhamDirectImage.relativeInverseImagePushforward`).
The Čech complexes of the two sides are compared over the opens of `V`, through `Opens.map f`,
which preserves finite intersections; there the two complexes of presheaves of
`Γ(T, ⊤)`-modules have the same terms, and the actions of `Γ(T, ⊤)` agree because the projections
of the two inverse images of `𝒪_T` to `T` form a triangle
(`Stacks.DeRhamDirectImage.relativeInverseImageProjection_comp`).

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 0FLH](https://stacks.math.columbia.edu/tag/0FLH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open Stacks.Cohomology.CechSheaf Stacks.CategoryTheory.CechComplex
open MMP.Mori.Divisor.LogSpreadingProof (Hc overTop)
open AlgebraicGeometry.DeRhamTypeComplex (inverseImageBaseRing inverseImageBaseRingHom)

/-! ### The direct image -/

section DirectImage

variable {V V' T : Scheme.{0}} (f : V' ⟶ V) (π : V ⟶ T)

/-- The direct image `f_*` of sheaves of `(π ∘ f)⁻¹𝒪_T`-modules. -/
noncomputable abbrev relDirectImage :
    SheafOfModules.{0} (invRing (f ≫ π)) ⥤ SheafOfModules.{0} (invRing π) :=
  Stacks.DeRhamDirectImage.relativeInverseImagePushforward f π

/-- The direct image is additive. -/
instance additive_relDirectImage : (relDirectImage f π).Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

/-- The ring map `π⁻¹𝒪_T ⟶ f_*(π ∘ f)⁻¹𝒪_T` along which `f_*` is taken. -/
noncomputable abbrev relRingHom : invRing π ⟶
    ((Opens.map f.base).sheafPushforwardContinuous _ _ _).obj (invRing (f ≫ π)) :=
  toRingCatSheafHom (Stacks.DeRhamDirectImage.relativeInverseImageProjection f π)

/-- **The two maps from `Γ(T, ⊤)` agree**: the global sections of the ring map
`π⁻¹𝒪_T ⟶ f_*(π ∘ f)⁻¹𝒪_T` carry the unit of `π` to the unit of `π ∘ f`. -/
theorem relRingHom_app_top_invRingUnit (r : Γ(T, ⊤)) :
    ((relRingHom f π).hom.app (op ⊤)).hom (invRingUnit π r) = invRingUnit (f ≫ π) r := by
  have h := PresheafedSpace.congr_app (congrArg InducedCategory.Hom.hom
    (Stacks.DeRhamDirectImage.relativeInverseImageProjection_comp f π)) (op ⊤)
  refine (congrArg (fun φ => (CommRingCat.Hom.hom φ) r) h).trans ?_
  have hid : (Stacks.DeRhamDirectImage.inverseImageBase (f ≫ π)).presheaf.map
      (eqToHom rfl : (op (⊤ : Opens (Stacks.DeRhamDirectImage.inverseImageBase (f ≫ π)))) ⟶
        op ⊤) = 𝟙 _ := by
    rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  rw [CommRingCat.comp_apply]
  exact congrArg (fun φ => (CommRingCat.Hom.hom φ) _) hid

/-- The ring map `π⁻¹𝒪_T ⟶ f_*(π ∘ f)⁻¹𝒪_T` carries the restriction of the unit of `π` to an
open `W` to the restriction of the unit of `π ∘ f` to `f⁻¹ W`. -/
theorem relRingHom_app_restrict_invRingUnit (W : V.Opensᵒᵖ) (r : Γ(T, ⊤)) :
    ((relRingHom f π).hom.app W).hom ((invRing π).obj.map
        (homOfLE le_top : W.unop ⟶ ⊤).op (invRingUnit π r)) =
      (invRing (f ≫ π)).obj.map (homOfLE le_top : f ⁻¹ᵁ W.unop ⟶ ⊤).op
        (invRingUnit (f ≫ π) r) :=
  (congrArg (fun φ => φ.hom (invRingUnit π r))
    ((relRingHom f π).hom.naturality (homOfLE le_top : W.unop ⟶ ⊤).op)).trans
    (congrArg (fun a => ((invRing (f ≫ π)).obj.map
      (homOfLE le_top : f ⁻¹ᵁ W.unop ⟶ ⊤).op).hom a) (relRingHom_app_top_invRingUnit f π r))

end DirectImage

/-! ### Hypercohomology by an elementwise total Čech complex -/

section CechBridge

open scoped ZeroObject

/-- **Change of site for the total Čech complex.** For a functor `G : C ⥤ D` preserving finite
products and a family `U` in `C`, the total Čech complex of the image family `G ∘ U` with
coefficients in a complex of presheaves on `D` is that of `U` with the coefficients restricted
along `G`. -/
noncomputable def totalCechComplexSiteChangeIso {C D : Type} [Category.{0} C] [Category.{0} D]
    [HasFiniteProducts C] [HasFiniteProducts D] (G : C ⥤ D) [PreservesFiniteProducts G]
    {ι : Type} (U : ι → C) (R : Type) [CommRing R] :
    Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (fun i => G.obj (U i)) R ≅
      ((Functor.whiskeringLeft _ _ (ModuleCat.{0} R)).obj G.op).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        Stacks.Cech.LinearCupProduct.totalCechComplexFunctor U R := by
  let α : Stacks.Cech.LinearCupProduct.cechComplexFunctorInt (fun i => G.obj (U i)) R ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{0} R)).obj G.op ⋙
        Stacks.Cech.LinearCupProduct.cechComplexFunctorInt U R :=
    Functor.isoWhiskerRight (Stacks.CechSiteChange.cechComplexFunctorSiteIso
        (A := ModuleCat.{0} R) G U)
        (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} R)) ≪≫
      Functor.associator _ _ _
  haveI : ((Functor.whiskeringLeft _ _ (ModuleCat.{0} R)).obj G.op ⋙
      Stacks.Cech.LinearCupProduct.cechComplexFunctorInt U R).PreservesZeroMorphisms :=
    ⟨fun P Q => by
      change (Stacks.Cech.LinearCupProduct.cechComplexFunctorInt U R).map
        (Functor.whiskerLeft _ (0 : P ⟶ Q)) = 0
      rw [show Functor.whiskerLeft G.op (0 : P ⟶ Q) = 0 from rfl]
      exact Functor.map_zero _ _ _⟩
  exact Functor.isoWhiskerRight (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex α
    (ComplexShape.up ℤ) ≪≫ Iso.refl _) _) _

/-- `Opens.map` preserves finite products: preimages commute with finite intersections. -/
instance preservesFiniteProducts_opensMap {X Y : TopCat.{0}} (g : X ⟶ Y) :
    PreservesFiniteProducts (Opens.map g) :=
  MMP.Mori.Divisor.LogSpreadingProof.preservesFiniteProducts_opensMap g

variable {Y T : Scheme.{0}} (h : Y ⟶ T)

variable {C : Type} [Category.{0} C] (Φ : C ⥤ Y.Opens)

/-- **Sections on a site over the opens.** A sheaf of `h⁻¹𝒪_T`-modules on `Y`, read as a presheaf
of `Γ(Y, h⁻¹𝒪_T)`-modules on a category `C` over the opens of `Y`. -/
noncomputable abbrev siteSections :
    SheafOfModules.{0} (inverseImageBaseRing h) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{0} (SectionRing (inverseImageBaseRing h) ⊤)) :=
  sectionsPresheafFunctor ⊤ ⋙ (Functor.whiskeringLeft _ _ _).obj (Φ ⋙ overTop).op

/-- The functor `siteSections h Φ` preserves zero morphisms. -/
instance preservesZeroMorphisms_siteSections : (siteSections h Φ).PreservesZeroMorphisms :=
  ⟨fun M N => by
    change Functor.whiskerLeft (Φ ⋙ overTop).op
      ((sectionsPresheafFunctor (R := inverseImageBaseRing h) ⊤).map (0 : M ⟶ N)) = 0
    rw [Functor.map_zero]
    rfl⟩

/-- The complex of presheaves of `Γ(T, ⊤)`-modules on `C` underlying a complex of sheaves of
`h⁻¹𝒪_T`-modules indexed by `ℕ`. -/
noncomputable abbrev siteCx (L : CochainComplex (SheafOfModules.{0} (inverseImageBaseRing h)) ℕ) :
    CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} Γ(T, ⊤)) ℕ :=
  restrictComplex (inverseImageBaseRingHom h)
    (((siteSections h Φ).mapHomologicalComplex _).obj L)

/-- The terms of a complex indexed by `ℕ` with quasi-coherent terms, extended by zero to `ℤ`, are
quasi-coherent. -/
theorem exists_extend_X_iso_pushforward
    (L : CochainComplex (SheafOfModules.{0} (inverseImageBaseRing h)) ℕ)
    (hL : ∀ q, ∃ M : Y.Modules, M.IsQuasicoherent ∧ Nonempty (L.X q ≅
      (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase h)).obj M)) (k : ℤ) :
    ∃ M : Y.Modules, M.IsQuasicoherent ∧ Nonempty ((L.extend ComplexShape.embeddingUpNat).X k ≅
      (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase h)).obj M) := by
  rcases lt_or_ge k 0 with hk | hk
  · have hz : IsZero ((L.extend ComplexShape.embeddingUpNat).X k) :=
      HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat k fun i => by
        change ((i : ℕ) : ℤ) ≠ k
        omega
    have := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
      (isZero_zero (Y.Modules))
    exact ⟨0, _root_.isQuasicoherent_of_isCoherent _,
      ⟨hz.iso (MMP.Mori.Divisor.LogSpreadingProof.isZero_pushforward_zero h)⟩⟩
  · obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    obtain ⟨M, hM, ⟨e⟩⟩ := hL b
    exact ⟨M, hM, ⟨L.extendXIso ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f b) ≪≫ e⟩⟩

variable [HasFiniteProducts C] [PreservesFiniteProducts Φ]

/-- **Hypercohomology by an elementwise total Čech complex.** On a scheme with affine diagonal,
for a family `U` in a category `C` over the opens of `Y` whose images form an affine open cover,
the hypercohomology of a complex of `h⁻¹𝒪_T`-modules indexed by `ℕ` with quasi-coherent terms is
the cohomology of the elementwise total Čech complex `cechTot` of its sections over `C`, read over
`Γ(T, ⊤)`. -/
theorem nonempty_Hc_iso_homology_cechTot [IsAffineHom (pullback.diagonal (terminal.from Y))]
    {ι : Type} (U : ι → C) (hU : (⊤ : Y.Opens) = ⨆ i, Φ.obj (U i))
    (hUaff : ∀ i, IsAffineOpen (Φ.obj (U i)))
    (L : CochainComplex (SheafOfModules.{0} (inverseImageBaseRing h)) ℕ)
    (hL : ∀ q, ∃ M : Y.Modules, M.IsQuasicoherent ∧ Nonempty (L.X q ≅
      (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase h)).obj M)) (j : ℤ) :
    Nonempty (Hc h ⟨L.extend ComplexShape.embeddingUpNat, 0,
        CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j ≅
      (cechTot U (siteCx h Φ L)).homology j) := by
  let K : CochainComplex.Plus (SheafOfModules.{0} (inverseImageBaseRing h)) :=
    ⟨L.extend ComplexShape.embeddingUpNat, 0,
      CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩
  obtain ⟨e₁⟩ := MMP.Mori.Divisor.LogSpreadingProof.nonempty_hcIsoHypercohomology h K j
  let e₂ := AlgebraicGeometry.DeRhamTypeComplex.homologyDerivedSectionsIso h
    (fun i => Φ.obj (U i)) hU hUaff K (exists_extend_X_iso_pushforward h L hL) j
  let P := ((siteSections h Φ).mapHomologicalComplex _).obj L
  let Kp := (((Functor.whiskeringLeft _ _ _).obj (Φ ⋙ overTop).op).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (((sectionsPresheafFunctor ⊤).mapHomologicalComplex _).obj K.1)
  let e : ∀ b : ℕ, Kp.X (b : ℤ) ≅ P.X b := fun b => (siteSections h Φ).mapIso
    (L.extendXIso ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f b))
  have hz : ∀ a : ℤ, a < 0 → IsZero (Kp.X a) := fun a ha =>
    (siteSections h Φ).map_isZero (L.isZero_extend_X _ a fun i => by
      rw [ComplexShape.embeddingUpNat_f]
      omega)
  have he : ∀ b : ℕ, Kp.d b (b + 1) ≫ (e (b + 1)).hom = (e b).hom ≫ P.d b (b + 1) := by
    intro b
    change (siteSections h Φ).map ((L.extend ComplexShape.embeddingUpNat).d b (b + 1)) ≫
      (siteSections h Φ).map (L.extendXIso ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f (b + 1))).hom =
      (siteSections h Φ).map (L.extendXIso ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f b)).hom ≫ (siteSections h Φ).map (L.d b (b + 1))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [HomologicalComplex.extend_d_eq _ _ (ComplexShape.embeddingUpNat_f b)
      (show ComplexShape.embeddingUpNat.f (b + 1) = (b : ℤ) + 1 by simp)]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id]
    rw [Category.comp_id]
  let e₃ : AlgebraicGeometry.DeRhamTypeComplex.totalCechComplex h (fun i => Φ.obj (U i)) hU K.1 ≅
      cechTot U P :=
    letI := MMP.Mori.Divisor.LogSpreadingProof.secCommRing h
    (totalCechComplexSiteChangeIso (Φ ⋙ overTop) U _).app
        (((sectionsPresheafFunctor ⊤).mapHomologicalComplex _).obj K.1) ≪≫
      totalCechIso U Kp P e hz he
  let ρ := inverseImageBaseRingHom h
  have := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars ρ
  exact ⟨e₁ ≪≫ e₂ ≪≫ (ModuleCat.restrictScalars.{0} ρ).mapIso
      ((HomologicalComplex.homologyFunctor _ _ j).mapIso e₃) ≪≫
    (((cechTot U P).sc j).mapHomologyIso (ModuleCat.restrictScalars.{0} ρ)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ j).mapIso (cechTotRestrictIso _ ρ P).symm⟩

end CechBridge

/-! ### The sections of a direct image over a site -/

section DirectImageSections

variable {V V' T : Scheme.{0}} (f : V' ⟶ V) (π : V ⟶ T)

/-- A section `a` of `π⁻¹𝒪_T` over `W` acts on a section `x` of `f_*M` over `W` as its image in
`(π ∘ f)⁻¹𝒪_T` over `f⁻¹ W` acts on `x` as a section of `M`. -/
theorem relDirectImage_smul (M : SheafOfModules.{0} (invRing (f ≫ π))) (W : V.Opens)
    (a : (invRing π).obj.obj (op W)) (x : M.val.obj (op (f ⁻¹ᵁ W))) :
    (a • (show ((relDirectImage f π).obj M).val.obj (op W) from x)) =
      (show (invRing (f ≫ π)).obj.obj (op (f ⁻¹ᵁ W)) from
        ((relRingHom f π).hom.app (op W)).hom a) • x := rfl

/-- **The sections of `f_*L` over the opens of `V` are those of `L` over their preimages**, as
complexes of presheaves of `Γ(T, ⊤)`-modules on the opens of `V`. -/
noncomputable def siteCxRelDirectImageIso
    (L : CochainComplex (SheafOfModules.{0} (inverseImageBaseRing (f ≫ π))) ℕ) :
    siteCx π (𝟭 V.Opens) (((relDirectImage f π).mapHomologicalComplex _).obj L) ≅
      siteCx (f ≫ π) (Opens.map f.base) L :=
  HomologicalComplex.Hom.isoOfComponents (fun b => NatIso.ofComponents (fun W =>
    LinearEquiv.toModuleIso (show
      ↑(((siteCx π (𝟭 V.Opens) (((relDirectImage f π).mapHomologicalComplex _).obj L)).X b).obj W)
        ≃ₗ[Γ(T, ⊤)] ↑(((siteCx (f ≫ π) (Opens.map f.base) L).X b).obj W) from
      { toFun := fun x => x
        invFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => by
          change HSMul.hSMul (α := (inverseImageBaseRing (f ≫ π)).obj.obj (op (f ⁻¹ᵁ W.unop)))
              (β := (L.X b).val.obj (op (f ⁻¹ᵁ W.unop)))
              (((relRingHom f π).hom.app W).hom ((invRing π).obj.map
                (homOfLE le_top : W.unop ⟶ ⊤).op (invRingUnit π r))) x =
            HSMul.hSMul (α := (inverseImageBaseRing (f ≫ π)).obj.obj (op (f ⁻¹ᵁ W.unop)))
              (β := (L.X b).val.obj (op (f ⁻¹ᵁ W.unop)))
              ((invRing (f ≫ π)).obj.map (homOfLE le_top : f ⁻¹ᵁ W.unop ⟶ ⊤).op
                (invRingUnit (f ≫ π) r)) x
          rw [relRingHom_app_restrict_invRingUnit]
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })) (fun _ => rfl)) (fun _ _ _ => rfl)

end DirectImageSections

/-! ### Hypercohomology of a direct image -/

section Comparison

open scoped ZeroObject

variable {V V' T : Scheme.{0}} (f : V' ⟶ V) (π : V ⟶ T)

/-- **The direct image of a quasi-coherent module, read over the inverse image of `𝒪_T`.** For an
`𝒪_{V'}`-module `M`, the direct image along `f` of `M` read over `(π ∘ f)⁻¹𝒪_T` is the direct image
`f_* M` of `𝒪_{V'}`-modules read over `π⁻¹𝒪_T`. -/
noncomputable def relDirectImagePushforwardIso (M : V'.Modules) :
    (relDirectImage f π).obj
        ((_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase (f ≫ π))).obj M) ≅
      (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase π)).obj
        ((Scheme.Modules.pushforward f).obj M) :=
  ((pushforwardComp (Stacks.DeRhamDirectImage.toInverseImageBase (f ≫ π))
      (Stacks.DeRhamDirectImage.relativeInverseImageProjection f π)).app M).symm ≪≫
    eqToIso (congrArg (fun g => (_root_.pushforward g).obj M)
      (Stacks.DeRhamDirectImage.toInverseImageBase_comp_relativeInverseImageProjection f π)) ≪≫
    (pushforwardComp f.toLRSHom.toShHom (Stacks.DeRhamDirectImage.toInverseImageBase π)).app M

/-- The terms of the direct image of a complex with quasi-coherent terms along an affine morphism
are quasi-coherent. -/
theorem exists_relDirectImage_X_iso_pushforward [IsAffineHom f]
    (L : CochainComplex (SheafOfModules.{0} (invRing (f ≫ π))) ℕ)
    (hL : ∀ q, ∃ M : V'.Modules, M.IsQuasicoherent ∧ Nonempty (L.X q ≅
      (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase (f ≫ π))).obj M)) (q : ℕ) :
    ∃ M : V.Modules, M.IsQuasicoherent ∧
      Nonempty ((((relDirectImage f π).mapHomologicalComplex _).obj L).X q ≅
        (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase π)).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hL q
  exact ⟨(Scheme.Modules.pushforward f).obj M,
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward f M hM,
    ⟨(relDirectImage f π).mapIso e ≪≫ relDirectImagePushforwardIso f π M⟩⟩

/-- **Hypercohomology is unchanged by a direct image along an affine morphism.** Let
`f : V' ⟶ V` be affine, `π : V ⟶ T`, and let `V` and `V'` have affine diagonal (for instance be
separated). For a complex `L` of sheaves of `(π ∘ f)⁻¹𝒪_T`-modules on `V'` indexed by `ℕ` whose
terms are quasi-coherent `𝒪_{V'}`-modules, `ℍ^j(V, f_* L) ≅ ℍ^j(V', L)` over `Γ(T, ⊤)`. -/
theorem nonempty_Hc_relDirectImage_iso [IsAffineHom f]
    [IsAffineHom (pullback.diagonal (terminal.from V))]
    [IsAffineHom (pullback.diagonal (terminal.from V'))]
    (L : CochainComplex (SheafOfModules.{0} (invRing (f ≫ π))) ℕ)
    (hL : ∀ q, ∃ M : V'.Modules, M.IsQuasicoherent ∧ Nonempty (L.X q ≅
      (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase (f ≫ π))).obj M))
    (j : ℤ) :
    Nonempty (Hc π ⟨(((relDirectImage f π).mapHomologicalComplex _).obj L).extend
          ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j ≅
      Hc (f ≫ π) ⟨L.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j) := by
  let U : V.affineOpens → V.Opens := fun i => (i : V.Opens)
  have hU : (⊤ : V.Opens) = ⨆ i, (𝟭 V.Opens).obj (U i) := (iSup_affineOpens_eq_top V).symm
  have hU' : (⊤ : V'.Opens) = ⨆ i, (Opens.map f.base).obj (U i) := by
    change (⊤ : V'.Opens) = iSup ((Opens.map f.base).obj ∘ U)
    rw [← Opens.map_iSup, iSup_affineOpens_eq_top]
    rfl
  obtain ⟨e₁⟩ := nonempty_Hc_iso_homology_cechTot π (𝟭 V.Opens) U hU (fun i => i.2)
    (((relDirectImage f π).mapHomologicalComplex _).obj L)
    (exists_relDirectImage_X_iso_pushforward f π L hL) j
  obtain ⟨e₂⟩ := nonempty_Hc_iso_homology_cechTot (f ≫ π) (Opens.map f.base) U hU'
    (fun i => i.2.preimage f) L hL j
  exact ⟨e₁ ≪≫ (HomologicalComplex.homologyFunctor _ _ j).mapIso
    (cechTotMapIso U (siteCxRelDirectImageIso f π L)) ≪≫ e₂.symm⟩

/-- The complex `M` placed in degree `0`, indexed by `ℕ` and extended by zero to `ℤ`, is `M`
placed in degree `0`, as a bounded below complex. -/
noncomputable def extendSingleZeroPlusIso {Y : Scheme.{0}} (h : Y ⟶ T)
    (M : SheafOfModules.{0} (invRing h)) :
    (⟨((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj M).extend
        ComplexShape.embeddingUpNat, 0,
        CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ :
      CochainComplex.Plus (SheafOfModules.{0} (invRing h))) ≅
      MMP.FourfoldProofs.LogDegenerationProof.single0 h M :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (HomologicalComplex.extendSingleIso _ _ _ _ (ComplexShape.embeddingUpNat_f 0))

/-- **Cohomology is unchanged by a direct image along an affine morphism**: for a
quasi-coherent `𝒪_{V'}`-module `M` read over `(π ∘ f)⁻¹𝒪_T`, `H^j(V, f_* M) ≅ H^j(V', M)` over
`Γ(T, ⊤)`. This is `nonempty_Hc_relDirectImage_iso` for `M` placed in degree `0`. -/
theorem nonempty_Hc_single0_relDirectImage_iso [IsAffineHom f]
    [IsAffineHom (pullback.diagonal (terminal.from V))]
    [IsAffineHom (pullback.diagonal (terminal.from V'))]
    (M : SheafOfModules.{0} (invRing (f ≫ π)))
    (hM : ∃ N : V'.Modules, N.IsQuasicoherent ∧ Nonempty (M ≅
      (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase (f ≫ π))).obj N))
    (j : ℤ) :
    Nonempty (Hc π (MMP.FourfoldProofs.LogDegenerationProof.single0 π ((relDirectImage f π).obj M)) j ≅
      Hc (f ≫ π) (MMP.FourfoldProofs.LogDegenerationProof.single0 (f ≫ π) M) j) := by
  let L := (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj M
  have hL : ∀ q, ∃ N : V'.Modules, N.IsQuasicoherent ∧ Nonempty (L.X q ≅
      (_root_.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase (f ≫ π))).obj N) := by
    rintro (_ | q)
    · obtain ⟨N, hN, ⟨e⟩⟩ := hM
      exact ⟨N, hN, ⟨HomologicalComplex.singleObjXSelf _ 0 M ≪≫ e⟩⟩
    · have := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
        (isZero_zero (V'.Modules))
      exact ⟨0, _root_.isQuasicoherent_of_isCoherent _,
        ⟨(HomologicalComplex.isZero_single_obj_X _ _ _ _ q.succ_ne_zero).iso
          (MMP.Mori.Divisor.LogSpreadingProof.isZero_pushforward_zero (f ≫ π))⟩⟩
  obtain ⟨e⟩ := nonempty_Hc_relDirectImage_iso f π L hL j
  let eP₁ : (⟨(((relDirectImage f π).mapHomologicalComplex _).obj L).extend
        ComplexShape.embeddingUpNat, 0,
        CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ :
      CochainComplex.Plus (SheafOfModules.{0} (invRing π))) ≅
      ⟨((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
        ((relDirectImage f π).obj M)).extend ComplexShape.embeddingUpNat, 0,
        CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ :=
    (ObjectProperty.fullyFaithfulι _).preimageIso
      ((ComplexShape.embeddingUpNat.extendFunctor _).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (relDirectImage f π) _ 0).app M))
  exact ⟨(MMP.FourfoldProofs.LogDegenerationProof.hypIsoOfIso π
      (eP₁ ≪≫ extendSingleZeroPlusIso π ((relDirectImage f π).obj M)) j).symm ≪≫ e ≪≫
    MMP.FourfoldProofs.LogDegenerationProof.hypIsoOfIso (f ≫ π) (extendSingleZeroPlusIso (f ≫ π) M) j⟩

end Comparison

end MMP.FourfoldProofs.FractionalLogComplexProof
