module

public import MMP.AlgebraicGeometry.DeRham.Logarithmic.SncPairFiniteModel
public import MMP.AlgebraicGeometry.DeRham.LogFormsWedge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverseSeparator
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackPreservesQuasiCoherent

/-!
# Logarithmic Hodge-to-de Rham degeneration: hypercohomology, Frobenius twists, coordinates

This file and `MMP.AlgebraicGeometry.DeRham.Logarithmic.DeligneIllusieReduction` prove the degeneration at `E₁` of the
logarithmic Hodge-to-de Rham spectral sequence of a smooth projective complex variety with a
simple normal crossing divisor, following Deligne and Illusie: spread the pair out over a smooth
`ℤ`-domain, reduce modulo a large prime and use a lift over the Witt vectors of length two. The
charts and logarithmic forms are those of
`MMP.AlgebraicGeometry.DeRham.Logarithmic.SncPairSpreadingOut`.

This file provides the dimension count for a complex whose image in the derived category is a
direct sum of shifted sheaves, the invariance of hypercohomology dimensions under a twist of the
scalars by the Frobenius of a finite field, the transport of a decomposition of the Frobenius
direct image `F_*Ω^•(log D)` to the complex over `f⁻¹𝒪`, the Frobenius-linearity of the de Rham
differential on `p`-th powers, and the algebra of a quotient by some of the coordinates of a
smooth algebra.

## Main results

* `MMP.FourfoldProofs.LogDegenerationProof.finrank_hyp_eq_sum_of_iso`: the hypercohomology dimension
  of a complex isomorphic in the derived category to `⊕_q M_q[-q]` is the sum of those of the
  `M_q`.
* `MMP.FourfoldProofs.LogDegenerationProof.finrank_hyp_frobeniusTwist`: hypercohomology dimensions
  over a finite field do not change under the Frobenius twist of the scalars.
* `MMP.FourfoldProofs.LogDegenerationProof.exists_hyp_eq_and_iso_of_frobenius_decomposition`: from a
  decomposition of `F_*Ω^•(log D)` to the dimension statement over `f⁻¹𝒪`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de
  Rham*][DeligneIllusie1987]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

namespace MMP.FourfoldProofs.LogDegenerationProof

open MMP.Mori.Divisor MMP.Mori.Divisor.LogSpreadingProof

/-- A sheaf of modules `M`, viewed as a bounded below cochain complex in degree `0`. -/
noncomputable abbrev single0 {Y T : Scheme.{0}} (h : Y ⟶ T)
    (M : SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf))) :
    CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf))) :=
  ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M, 0,
    (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
      HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩

/-- **Hypercohomology of a split complex.** If a bounded below complex `L` is isomorphic in the
derived category to `⨁_{q ≤ N} M_q[-q]`, then `dim ℍ^k(L) = ∑_q dim H^{k-q}(M_q)`, provided the
cohomology groups of the `M_q` are finite free. -/
theorem finrank_hyp_eq_sum_of_iso {Y T : Scheme.{0}} (h : Y ⟶ T)
    [StrongRankCondition Γ(T, ⊤)]
    (L : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)))) {N : ℕ}
    (M : Fin (N + 1) → SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)))
    (e : DerivedCategory.Plus.Q.obj L ≅
      ⨁ fun q : Fin (N + 1) => (DerivedCategory.Plus.singleFunctor _ (q : ℤ)).obj (M q))
    (hfin : ∀ q (j : ℤ), Module.Finite Γ(T, ⊤) (Hc h (single0 h (M q)) j))
    (hfree : ∀ q (j : ℤ), Module.Free Γ(T, ⊤) (Hc h (single0 h (M q)) j)) (k : ℤ) :
    Module.finrank Γ(T, ⊤) (Hc h L k) =
      ∑ q : Fin (N + 1), Module.finrank Γ(T, ⊤) (Hc h (single0 h (M q)) (k - q)) := by
  let F := SheafOfModules.evaluation.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)) (op ⊤)
  letI := Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus F
  haveI := CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus F
  haveI : HasFiniteBiproducts (ModuleCat.{0} ((SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)).obj.obj (op ⊤))) :=
    inferInstance
  let G := F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor _ k
  -- the single complex in degree `0` is the single object of the derived category
  have hs : ∀ q, DerivedCategory.Plus.Q.obj (single0 h (M q)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj (M q) := fun q =>
    (ObjectProperty.fullyFaithfulι _).preimageIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (M q)).symm
  let φ : Γ(T, ⊤) →+* ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf).obj.obj (op ⊤) :=
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} h.base).unit.app
      T.sheaf).hom.app (op ⊤)).hom
  have E := G.mapIso e ≪≫ G.mapBiproduct _ ≪≫ biproduct.mapIso fun q =>
    G.mapIso (((DerivedCategory.Plus.singleFunctors _).shiftIso (-((q : ℕ) : ℤ)) ((q : ℕ) : ℤ) 0
      (by simp)).app (M q)).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor _ k).mapIso
        ((F.rightDerivedFunctorPlus.commShiftIso (-((q : ℕ) : ℤ))).app _) ≪≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso (-((q : ℕ) : ℤ)) k (k - q)
        (by omega)).app _ ≪≫
      (DerivedCategory.Plus.homologyFunctor _ (k - q)).mapIso
        (F.rightDerivedFunctorPlus.mapIso (hs q).symm)
  have e' := ((ModuleCat.restrictScalars φ).mapIso (E ≪≫ ModuleCat.biproductIsoPi _)).toLinearEquiv
  haveI := fun q => hfin q (k - q)
  haveI := fun q => hfree q (k - q)
  refine e'.finrank_eq.trans (Eq.trans ?_ (Module.finrank_pi_fintype (R := Γ(T, ⊤))
    (M := fun q : Fin (N + 1) => Hc h (single0 h (M q)) (k - q))))
  rfl

/-- The cohomology of a sheaf placed in degree `0` vanishes in negative degrees, and vanishes
identically for the zero sheaf. -/
theorem finrank_hyp_single0_eq_zero {Y T : Scheme.{0}} (h : Y ⟶ T)
    [Nontrivial Γ(T, ⊤)]
    (M : SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf))) (j : ℤ)
    (hj : j < 0 ∨ IsZero M) :
    Module.finrank Γ(T, ⊤) (Hc h (single0 h M) j) = 0 := by
  let F := SheafOfModules.evaluation.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)) (op ⊤)
  letI := Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus F
  haveI := CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus F
  have hs : DerivedCategory.Plus.Q.obj (single0 h M) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj M :=
    (ObjectProperty.fullyFaithfulι _).preimageIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm
  have hZ : IsZero ((DerivedCategory.Plus.homologyFunctor _ j).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj (single0 h M)))) := by
    refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ j).mapIso
      (F.rightDerivedFunctorPlus.mapIso hs))
    rcases hj with hj | hM
    · haveI := CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj F
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) 0
      exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 j hj
    · exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ hM))
  haveI hsub := ModuleCat.isZero_iff_subsingleton.1 hZ
  haveI : Subsingleton (Hc h (single0 h M) j) := hsub
  exact Module.finrank_zero_of_subsingleton

/-- **Exact functors carry split complexes to split complexes.** If a bounded below complex `X`
is isomorphic in `D(C)` to `⨁_{q ≤ N} M_q[-q]` and `F : C ⥤ D` is exact, then `F(X)` is
isomorphic in `D⁺(D)` to `⨁_{q ≤ N} F(M_q)[-q]`. -/
noncomputable def plusQMapIsoBiproductOfIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : CochainComplex.Plus C) {N : ℕ} (M : Fin (N + 1) → C)
    (e : DerivedCategory.Q.obj X.obj ≅
      ⨁ fun q : Fin (N + 1) => (DerivedCategory.singleFunctor C (q : ℤ)).obj (M q)) :
    DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj X) ≅
      ⨁ fun q : Fin (N + 1) =>
        (DerivedCategory.Plus.singleFunctor D (q : ℤ)).obj (F.obj (M q)) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((F.mapDerivedCategoryFactors.app X.obj).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫
      F.mapDerivedCategory.mapBiproduct _ ≪≫ biproduct.mapIso (fun q =>
        (F.mapDerivedCategorySingleFunctor (q : ℤ)).app (M q)) ≪≫
      (DerivedCategory.Plus.ι.mapBiproduct (fun q : Fin (N + 1) =>
        (DerivedCategory.Plus.singleFunctor D (q : ℤ)).obj (F.obj (M q)))).symm)

section ModelIndependence2

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (F : C ⥤ D)

/-- **Right derived functors commute with an autoequivalence.** If `E` is an autoequivalence
of `C` and `E ⋙ F ≅ F ⋙ G` for an exact `G`, then the homology of `RF(E K)` is `G` of that of
`RF(K)`. -/
theorem nonempty_homology_rightDerivedFunctorPlus_map_iso
    [F.Additive] [EnoughInjectives C] [HasDerivedCategory C]
    [HasDerivedCategory D] (E : C ⥤ C) [E.IsEquivalence] [E.Additive] (G : D ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : E ⋙ F ≅ F ⋙ G)
    (K : CochainComplex.Plus C) (j : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor D j).obj
        (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (E.mapCochainComplexPlus.obj K)))) ≅
      G.obj ((DerivedCategory.homologyFunctor D j).obj
        (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj K))))) := by
  obtain ⟨n, hn⟩ := K.2
  obtain ⟨L, _, φ, hφ⟩ := CochainComplex.Plus.exists_quasiIso_injective K n
  haveI : QuasiIso φ.hom := hφ
  have hinj : ∀ X : C, Injective X → Injective (E.obj X) := fun X _ =>
    Injective.injective_of_adjoint (E.asEquivalence.symm.toAdjunction) X
  let E' : InjectiveObject C ⥤ InjectiveObject C :=
    ObjectProperty.lift _ (InjectiveObject.ι C ⋙ E) fun X => hinj _ X.2
  let L' := E'.mapCochainComplexPlus.obj L
  let φ' : E.mapCochainComplexPlus.obj K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj L' :=
    E.mapCochainComplexPlus.map φ
  haveI : PreservesFiniteLimits E := inferInstance
  haveI : PreservesFiniteColimits E := inferInstance
  haveI : E.PreservesHomology := inferInstance
  haveI : QuasiIso φ'.hom := by
    change QuasiIso ((E.mapHomologicalComplex _).map φ.hom)
    exact HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  let M := ((InjectiveObject.ι C).mapCochainComplexPlus.obj L).obj
  exact ⟨homologyRightDerivedFunctorPlusIso F _ L' φ' j ≪≫
    (HomologicalComplex.homologyFunctor D _ j).mapIso
      ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app M) ≪≫
    (M.sc j |>.map F).mapHomologyIso G ≪≫
    G.mapIso (homologyRightDerivedFunctorPlusIso F K L φ j).symm⟩

end ModelIndependence2

section FrobeniusTwist

variable {X : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0})

/-- Applying `σ.hom` to a section after `σ.inv` returns that section. -/
theorem hom_app_inv_app (σ : R ≅ R) (U) (r) : σ.hom.hom.app U (σ.inv.hom.app U r) = r :=
  congrArg (fun f : R ⟶ R => f.hom.app U r) σ.inv_hom_id

/-- Applying `σ.inv` to a section after `σ.hom` returns that section. -/
theorem inv_app_hom_app (σ : R ≅ R) (U) (r) : σ.inv.hom.app U (σ.hom.hom.app U r) = r :=
  congrArg (fun f : R ⟶ R => f.hom.app U r) σ.hom_inv_id

/-- Restriction of scalars along an automorphism of a sheaf of rings is an autoequivalence of its
category of sheaves of modules. -/
noncomputable def restrictScalarsEquivalence (σ : R ≅ R) :
    SheafOfModules.{0} R ≌ SheafOfModules.{0} R where
  functor := _root_.SheafOfModules.restrictScalars σ.hom
  inverse := _root_.SheafOfModules.restrictScalars σ.inv
  unitIso := NatIso.ofComponents (fun M =>
    { hom := ⟨PresheafOfModules.homMk (𝟙 _) fun U r m => by
        change r • m = (σ.hom.hom.app U (σ.inv.hom.app U r)) • m
        rw [hom_app_inv_app]⟩
      inv := ⟨PresheafOfModules.homMk (𝟙 _) fun U r m =>
        congrArg (fun x => x • (show M.val.obj U from m)) (hom_app_inv_app R σ U r)⟩ })
    (fun f => rfl)
  counitIso := NatIso.ofComponents (fun M =>
    { hom := ⟨PresheafOfModules.homMk (𝟙 _) fun U r m =>
        congrArg (fun x => x • (show M.val.obj U from m)) (inv_app_hom_app R σ U r)⟩
      inv := ⟨PresheafOfModules.homMk (𝟙 _) fun U r m => by
        change r • m = (σ.inv.hom.app U (σ.hom.hom.app U r)) • m
        rw [inv_app_hom_app]⟩ })
    (fun f => rfl)
  functor_unitIso_comp M := rfl

end FrobeniusTwist

/-- Restriction of scalars along an endomorphism of the underlying sheaf of rings of
`f⁻¹𝒪_T` is an additive functor. -/
theorem additive_restrictScalars_underlyingRingSheaf {Y T : Scheme.{0}} (h : Y ⟶ T)
    (σ : SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf) ⟶
        SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)) :
    (_root_.SheafOfModules.restrictScalars.{0} σ).Additive :=
  _root_.SheafOfModules.instAdditiveRestrictScalars σ

attribute [local instance] additive_restrictScalars_underlyingRingSheaf

/-- **Hypercohomology dimensions are invariant under a twist of scalars by an automorphism.** -/
theorem finrank_hyp_restrictScalars {Y T : Scheme.{0}} (h : Y ⟶ T)
    (σ : SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf) ≅
        SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf))
    (τ : Γ(T, ⊤) →+* Γ(T, ⊤)) (hτ : Function.Bijective τ)
    (hστ : ∀ a : Γ(T, ⊤), (σ.hom.hom.app (op ⊤)).hom
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} h.base).unit.app
      T.sheaf).hom.app (op ⊤)).hom a) =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} h.base).unit.app
      T.sheaf).hom.app (op ⊤)).hom (τ a))
    (K : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)))) (j : ℤ) :
    Module.finrank Γ(T, ⊤)
        (Hc h ((_root_.SheafOfModules.restrictScalars.{0} σ.hom).mapCochainComplexPlus.obj K) j) =
      Module.finrank Γ(T, ⊤) (Hc h K j) := by
  let R := SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)
  let ev := SheafOfModules.evaluation.{0} R (op ⊤)
  let G := ModuleCat.restrictScalars.{0} (σ.hom.hom.app (op ⊤)).hom
  haveI : (_root_.SheafOfModules.restrictScalars.{0} σ.hom).IsEquivalence :=
    (restrictScalarsEquivalence R σ).isEquivalence_functor
  let e : _root_.SheafOfModules.restrictScalars.{0} σ.hom ⋙ ev ≅ ev ⋙ G :=
    NatIso.ofComponents (fun M => Iso.refl _) (fun f => rfl)
  obtain ⟨i⟩ := nonempty_homology_rightDerivedFunctorPlus_map_iso ev
    (_root_.SheafOfModules.restrictScalars.{0} σ.hom) G e K j
  let u : Γ(T, ⊤) →+* ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf).obj.obj (op ⊤) :=
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} h.base).unit.app
      T.sheaf).hom.app (op ⊤)).hom
  let ψ := ((ModuleCat.restrictScalars.{0} u).mapIso i).toLinearEquiv
  let j' : Hc h ((_root_.SheafOfModules.restrictScalars.{0} σ.hom).mapCochainComplexPlus.obj K) j
      ≃+ Hc h K j :=
    ψ.toAddEquiv
  let X := (DerivedCategory.homologyFunctor _ j).obj
    (DerivedCategory.Plus.ι.obj (ev.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)))
  have hrank := rank_eq_of_equiv_equiv τ j' hτ fun r m => by
    refine (ψ.map_smul r m).trans ?_
    exact congrArg (fun a => a • (show X from ψ m)) (hστ r)
  unfold Module.finrank
  rw [hrank]

section FrobeniusRingSheaf

variable {Y : Scheme.{0}} {κ : CommRingCat.{0}} (f : Y ⟶ Spec κ)

/-- The sections of the inverse image of `𝒪_{Spec κ}` are `κ`-algebras. -/
noncomputable def toPullbackSections
    (U : (TopologicalSpace.Opens Y)ᵒᵖ) :
    κ →+* ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf).obj.obj U :=
  ((Scheme.ΓSpecIso κ).inv ≫
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} f.base).unit.app
      (Spec κ).sheaf).hom.app (op ⊤) ≫
    ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf).obj.map
      (homOfLE le_top).op).hom

/-- If `p = 0` in `κ`, then `p = 0` in every ring of sections of the inverse image of
`𝒪_{Spec κ}`. -/
theorem natCast_eq_zero_pullbackSections (p : ℕ) (hp : (p : κ) = 0)
    (U : (TopologicalSpace.Opens Y)ᵒᵖ) :
    (p : ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf).obj.obj U) = 0 := by
  rw [← map_natCast (toPullbackSections f U), hp, map_zero]

end FrobeniusRingSheaf

section FrobeniusRingSheaf2

variable {Y : Scheme.{0}} {κ : CommRingCat.{0}} (f : Y ⟶ Spec κ)

/-- The `k`-th iterate of the Frobenius endomorphism of a ring of characteristic `p` sends `x`
to `x ^ p ^ k`. -/
theorem pow_primePowerEndomorphism_apply (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) (k : ℕ) (x : R) :
    (Stacks.Frobenius.primePowerEndomorphism R p hp ^ k) x = x ^ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih,
      Stacks.Frobenius.primePowerEndomorphism_apply, ← pow_mul, ← pow_succ]

/-- The `p ^ k`-th power endomorphism of the inverse image of `𝒪_{Spec κ}`, for `κ` of
characteristic `p`. -/
noncomputable def pullbackFrobeniusPow (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0) (k : ℕ) :
    (TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf ⟶
      (TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf where
  hom :=
    { app := fun U => CommRingCat.ofHom
        (Stacks.Frobenius.primePowerEndomorphism _ p
          (natCast_eq_zero_pullbackSections f p hp U) ^ k)
      naturality := fun U V g => by
        ext x
        simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom,
          pow_primePowerEndomorphism_apply, map_pow] }

/-- The `p ^ k`-th power endomorphism sends a section `x` to `x ^ p ^ k`. -/
theorem pullbackFrobeniusPow_app (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0) (k : ℕ) (U) (x) :
    (pullbackFrobeniusPow f p hp k).hom.app U x = x ^ p ^ k :=
  pow_primePowerEndomorphism_apply _ p _ k x

end FrobeniusRingSheaf2

section FrobeniusRingSheaf3

variable {Y : Scheme.{0}} {κ : CommRingCat.{0}} (f : Y ⟶ Spec κ)

/-- The composite of the `p ^ k`-th and `p ^ l`-th power endomorphisms is the
`p ^ (k + l)`-th power endomorphism. -/
theorem pullbackFrobeniusPow_comp (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0) (k l : ℕ) :
    pullbackFrobeniusPow f p hp k ≫ pullbackFrobeniusPow f p hp l =
      pullbackFrobeniusPow f p hp (k + l) := by
  refine Sheaf.hom_ext ?_
  ext U x
  change (pullbackFrobeniusPow f p hp l).hom.app U ((pullbackFrobeniusPow f p hp k).hom.app U x) =
    (pullbackFrobeniusPow f p hp (k + l)).hom.app U x
  rw [pullbackFrobeniusPow_app, pullbackFrobeniusPow_app, pullbackFrobeniusPow_app, ← pow_mul,
    ← pow_add]

/-- If `Spec κ` is a single point and `x ^ q = x` for every `x : κ`, then `a ^ q = a` for every
section `a` of `𝒪_{Spec κ}` over any open. -/
theorem pow_eq_self_Γ_Spec (hpt : ∀ a b : Spec κ, a = b) {q : ℕ} (hκ : ∀ x : κ, x ^ q = x)
    (V : (Spec κ).Opens) (a : Γ(Spec κ, V)) : a ^ q = a := by
  by_cases hV : V = ⊥
  · subst hV; exact Subsingleton.elim _ _
  · have hV' : V = ⊤ := by
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty V).mp hV
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact hpt x y ▸ hx
    subst hV'
    obtain ⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso κ).inv b = a :=
      ⟨(Scheme.ΓSpecIso κ).hom a, by simp⟩
    rw [← map_pow, hκ]

/-- If `Spec κ` is a single point and `x ^ p ^ m = x` for every `x : κ`, then the `p ^ m`-th
power endomorphism of `f⁻¹𝒪_{Spec κ}` is the identity. -/
theorem pullbackFrobeniusPow_eq_id (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0)
    (hpt : ∀ a b : Spec κ, a = b) {m : ℕ} (hκ : ∀ x : κ, x ^ p ^ m = x) :
    pullbackFrobeniusPow f p hp m = 𝟙 _ := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} f.base
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  refine Sheaf.hom_ext ?_
  ext V a
  change (pullbackFrobeniusPow f p hp m).hom.app _ ((adj.unit.app (Spec κ).sheaf).hom.app V a) =
    (adj.unit.app (Spec κ).sheaf).hom.app V a
  refine (pullbackFrobeniusPow_app f p hp m _ _).trans ?_
  exact ((map_pow ((adj.unit.app (Spec κ).sheaf).hom.app V).hom a (p ^ m)).symm).trans
    (congrArg _ (pow_eq_self_Γ_Spec hpt hκ V.unop a))

end FrobeniusRingSheaf3

section FrobeniusRingSheaf4

variable {Y : Scheme.{0}} {κ : CommRingCat.{0}} (f : Y ⟶ Spec κ)

/-- **The Frobenius automorphism of `f⁻¹𝒪_{Spec κ}`** for a finite field `κ` of characteristic
`p` with `p ^ m` elements, as an automorphism of sheaves of rings. -/
noncomputable def frobeniusRingSheafIso (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0)
    (hpt : ∀ a b : Spec κ, a = b) {m : ℕ} (hm : 1 ≤ m) (hκ : ∀ x : κ, x ^ p ^ m = x) :
    SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf) ≅
      SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf) :=
  (sheafCompose _ (forget₂ CommRingCat.{0} RingCat.{0})).mapIso
    { hom := pullbackFrobeniusPow f p hp 1
      inv := pullbackFrobeniusPow f p hp (m - 1)
      hom_inv_id := (pullbackFrobeniusPow_comp f p hp 1 (m - 1)).trans
        ((congrArg (pullbackFrobeniusPow f p hp) (show 1 + (m - 1) = m by omega)).trans
          (pullbackFrobeniusPow_eq_id f p hp hpt hκ))
      inv_hom_id := (pullbackFrobeniusPow_comp f p hp (m - 1) 1).trans
        ((congrArg (pullbackFrobeniusPow f p hp) (show m - 1 + 1 = m by omega)).trans
          (pullbackFrobeniusPow_eq_id f p hp hpt hκ)) }

/-- The Frobenius automorphism of `f⁻¹𝒪_{Spec κ}` sends a section `r` to `r ^ p`. -/
theorem frobeniusRingSheafIso_hom_app (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0)
    (hpt : ∀ a b : Spec κ, a = b) {m : ℕ} (hm : 1 ≤ m) (hκ : ∀ x : κ, x ^ p ^ m = x) (U)
    (r) : (frobeniusRingSheafIso f p hp hpt hm hκ).hom.hom.app U r = r ^ p :=
  (pullbackFrobeniusPow_app f p hp 1 U r).trans (congrArg (r ^ ·) (pow_one p))

/-- **Hypercohomology dimensions over a finite field do not change under the Frobenius twist of
the scalars.** -/
theorem finrank_hyp_frobeniusTwist (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0)
    (hpt : ∀ a b : Spec κ, a = b) {m : ℕ} (hm : 1 ≤ m) (hκ : ∀ x : κ, x ^ p ^ m = x)
    (K : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf)))) (j : ℤ) :
    Module.finrank Γ(Spec κ, ⊤)
        (Hc f ((_root_.SheafOfModules.restrictScalars.{0}
          (frobeniusRingSheafIso f p hp hpt hm hκ).hom).mapCochainComplexPlus.obj K) j) =
      Module.finrank Γ(Spec κ, ⊤) (Hc f K j) := by
  have hpΓ : (p : Γ(Spec κ, ⊤)) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso κ).inv.hom, hp, map_zero]
  let τ := Stacks.Frobenius.primePowerEndomorphism Γ(Spec κ, ⊤) p hpΓ
  have hτm : ∀ a, (τ ^ m) a = a := fun a => by
    rw [pow_primePowerEndomorphism_apply, pow_eq_self_Γ_Spec hpt hκ]
  have hτ : Function.Bijective τ := by
    refine ⟨fun a b hab => ?_, fun b => ⟨(τ ^ (m - 1)) b, ?_⟩⟩
    · have := congrArg (τ ^ (m - 1)) hab
      rwa [← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.mul_def, ← pow_succ,
        show m - 1 + 1 = m by omega, hτm, hτm] at this
    · rw [← RingHom.comp_apply, ← RingHom.mul_def, ← pow_succ', show m - 1 + 1 = m by omega, hτm]
  refine finrank_hyp_restrictScalars f _ τ hτ (fun a => ?_) K j
  exact (frobeniusRingSheafIso_hom_app f p hp hpt hm hκ _ _).trans ((map_pow _ a p).symm.trans
    (congrArg _ (Stacks.Frobenius.primePowerEndomorphism_apply _ p hpΓ a).symm))

end FrobeniusRingSheaf4

section ExtendMap

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The terms of `F` applied to an extension by zero are the terms of the extension of `F`
applied to the complex. -/
noncomputable def mapExtendXIso (K : HomologicalComplex C c) (e : c.Embedding c')
    (i' : ι') : F.obj ((K.extend e).X i') ≅ (((F.mapHomologicalComplex c).obj K).extend e).X i' :=
  match h : e.r i' with
  | some _ => F.mapIso (K.extendXIso e (e.f_eq_of_r_eq_some h)) ≪≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e (e.f_eq_of_r_eq_some h)).symm
  | none => IsZero.iso (F.map_isZero (K.isZero_extend_X' e i' h))
      (HomologicalComplex.isZero_extend_X' _ e i' h)

/-- For `i' = e.f i`, the isomorphism `mapExtendXIso F K e i'` is the composite of `F` applied
to `K.extendXIso e h` with the inverse of the corresponding isomorphism for the image
complex. -/
theorem mapExtendXIso_eq (K : HomologicalComplex C c) (e : c.Embedding c') {i' : ι'}
    {i : ι} (h : e.f i = i') :
    mapExtendXIso F K e i' = F.mapIso (K.extendXIso e h) ≪≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).symm := by
  subst h
  unfold mapExtendXIso
  split
  · rename_i j hj
    have := e.injective_f (e.f_eq_of_r_eq_some hj)
    subst this
    rfl
  · rename_i hj
    simp at hj

/-- **Extension by zero commutes with a functor preserving zero morphisms.** -/
noncomputable def mapHomologicalComplexExtendIso (K : HomologicalComplex C c)
    (e : c.Embedding c') :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅ ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (mapExtendXIso F K e) (by
    intro i' j' _
    rcases hi : e.r i' with _ | i
    · apply IsZero.eq_of_src
      exact F.map_isZero (K.isZero_extend_X' e i' hi)
    rcases hj : e.r j' with _ | j
    · apply IsZero.eq_of_tgt
      exact HomologicalComplex.isZero_extend_X' _ e j' hj
    have hi' := e.f_eq_of_r_eq_some hi
    have hj' := e.f_eq_of_r_eq_some hj
    rw [mapExtendXIso_eq F K e hi', mapExtendXIso_eq F K e hj',
      Functor.mapHomologicalComplex_obj_d, K.extend_d_eq e hi' hj',
      HomologicalComplex.extend_d_eq _ e hi' hj']
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
      Functor.mapHomologicalComplex_obj_d, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    simp only [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id])

end ExtendMap

section Transport

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.Frobenius

/-- Isomorphic complexes have isomorphic hypercohomology. -/
noncomputable def hypIsoOfIso {Y T : Scheme.{0}} (h : Y ⟶ T)
    {L L' : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)))} (e : L ≅ L') (j : ℤ) :
    Hc h L j ≅ Hc h L' j := by
  unfold Hc
  exact (ModuleCat.restrictScalars.{0} _).mapIso ((DerivedCategory.homologyFunctor
    (ModuleCat.{0} ((SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)).obj.obj (op ⊤))) j).mapIso
    (DerivedCategory.Plus.ι.mapIso ((SheafOfModules.evaluation.{0}
      (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf))
          (op ⊤)).rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.Q.mapIso e))))

/-- The Frobenius of `𝒪_Y` on the image of a section of `f⁻¹𝒪_{Spec κ}` is the image of its
Frobenius twist. -/
theorem absoluteFrobenius_app_inverseImageStructureMap {Y : Scheme.{0}} {κ : CommRingCat.{0}}
    (f : Y ⟶ Spec κ) (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0) (hpt : ∀ a b : Spec κ, a = b)
    {m : ℕ} (hm : 1 ≤ m) (hκ : ∀ x : κ, x ^ p ^ m = x) (hV : IsInCharacteristic Y p)
    (W : (TopologicalSpace.Opens Y)ᵒᵖ)
    (r : (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf)).obj.obj W) :
    (absoluteFrobenius Y p hV).app W.unop (((inverseImageStructureMap f).hom.app W).hom r) =
      ((inverseImageStructureMap f).hom.app W).hom
        ((frobeniusRingSheafIso f p hp hpt hm hκ).hom.hom.app W r) :=
  (absoluteFrobenius_app_apply Y p hV _ _).trans ((map_pow _ _ _).symm.trans
    (congrArg _ (frobeniusRingSheafIso_hom_app f p hp hpt hm hκ W r).symm))

/-- Reading the Frobenius direct image of an `𝒪_Y`-module over `f⁻¹𝒪_{Spec κ}` is twisting the
scalars of the module read over `f⁻¹𝒪_{Spec κ}` by the Frobenius of `f⁻¹𝒪_{Spec κ}`. -/
noncomputable def frobeniusPushforwardIso {Y : Scheme.{0}} {κ : CommRingCat.{0}}
    (f : Y ⟶ Spec κ) (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0) (hpt : ∀ a b : Spec κ, a = b)
    {m : ℕ} (hm : 1 ≤ m) (hκ : ∀ x : κ, x ^ p ^ m = x) (hV : IsInCharacteristic Y p)
    (M : Y.Modules) :
    (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj
        ((Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj M) ≅
      (_root_.SheafOfModules.restrictScalars.{0}
        (frobeniusRingSheafIso f p hp hpt hm hκ).hom).obj
        ((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj M) where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) fun W r m =>
    congrArg (fun c => (show Y.ringCatSheaf.obj.obj (op W.unop) from c) •
      (show M.val.obj (op W.unop) from m))
      (absoluteFrobenius_app_inverseImageStructureMap f p hp hpt hm hκ hV W r)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) fun W r m =>
    (congrArg (fun c => (show Y.ringCatSheaf.obj.obj (op W.unop) from c) •
      (show M.val.obj (op W.unop) from m))
      (absoluteFrobenius_app_inverseImageStructureMap f p hp hpt hm hκ hV W r)).symm⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The Frobenius direct image of the logarithmic forms, read over `f⁻¹𝒪_{Spec κ}`, is the
Frobenius twist of the scalars of the logarithmic forms. -/
noncomputable def frobeniusLogTermIso (n : ℕ) {Y : Scheme.{0}} {κ : CommRingCat.{0}}
    (f : Y ⟶ Spec κ) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor Y)
    (hD : D.IsRelativeSNC n f) (ε : Bool) (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0)
    (hpt : ∀ a b : Spec κ, a = b) {m : ℕ} (hm : 1 ≤ m) (hκ : ∀ x : κ, x ^ p ^ m = x)
    (hV : IsInCharacteristic Y p) (q : ℕ) :
    (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj
        ((Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj
          (logModule n f D hD (bif ε then D.suppIdeal else ⊤) q)) ≅
      (_root_.SheafOfModules.restrictScalars.{0}
        (frobeniusRingSheafIso f p hp hpt hm hκ).hom).obj ((logCx hD ε).X q) :=
  frobeniusPushforwardIso f p hp hpt hm hκ hV _ ≪≫
    (_root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso f p hp hpt hm hκ).hom).mapIso
      (logSubmoduleIso n f D hD (bif ε then D.suppIdeal else ⊤) q).symm

/-- The complex of Frobenius direct images of the logarithmic forms with a differential `d`
restricting the de Rham differential, read over `f⁻¹𝒪_{Spec κ}`, is the Frobenius twist of the
scalars of the logarithmic de Rham complex. -/
noncomputable def frobeniusLogComplexIso (n : ℕ) {Y : Scheme.{0}} {κ : CommRingCat.{0}}
    (f : Y ⟶ Spec κ) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor Y)
    (hD : D.IsRelativeSNC n f) (ε : Bool) (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0)
    (hpt : ∀ a b : Spec κ, a = b) {m : ℕ} (hm : 1 ≤ m) (hκ : ∀ x : κ, x ^ p ^ m = x)
    (hV : IsInCharacteristic Y p)
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj
        (logModule n f D hD (bif ε then D.suppIdeal else ⊤) q) ⟶
      (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj
        (logModule n f D hD (bif ε then D.suppIdeal else ⊤) (q + 1)))
    (hd : ∀ q, d q ≫ d (q + 1) = 0)
    (hdR : ∀ (q : ℕ) (W : Y.Opens)
      (s : Γ(logModule n f D hD (bif ε then D.suppIdeal else ⊤) q, W)),
      (show ↥((logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) (q + 1)).obj (op W))
        from (d q).app W s).1 =
      ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d q (q + 1)).val.app (op ((LU D).ι ⁻¹ᵁ W))
        (show ↥((logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) q).obj (op W))
          from s).1) :
    ((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).mapHomologicalComplex _).obj
        (CochainComplex.of (fun q => (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj
          (logModule n f D hD (bif ε then D.suppIdeal else ⊤) q)) d hd) ≅
      ((_root_.SheafOfModules.restrictScalars.{0}
        (frobeniusRingSheafIso f p hp hpt hm hκ).hom).mapHomologicalComplex _).obj (logCx hD ε) :=
  HomologicalComplex.Hom.isoOfComponents (frobeniusLogTermIso n f D hD ε p hp hpt hm hκ hV) (by
    rintro i _ rfl
    ext W s
    apply Subtype.ext
    let G : Y.Modules ⥤ SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf)) :=
      pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)
    haveI : G.Additive := inferInstanceAs
      (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).Additive
    let M := fun q : ℕ => logModule n f D hD (bif ε then D.suppIdeal else ⊤) q
    let Cx := CochainComplex.of
      (fun q => (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj (M q)) d hd
    have e1 := subCx_d_val f D (logSubmodule n f D hD (bif ε then D.suppIdeal else ⊤))
      (fun p W ω hω => deRham_mem_relativeLogForms hD ε p W.unop ω hω) i W s
    have e2 := hdR i W.unop s
    change (((logCx hD ε).d i (i + 1)).val.app W s).1 =
      ((((G.mapHomologicalComplex _).obj Cx).d i (i + 1)).val.app W s).1
    have hCx : Cx.d i (i + 1) = d i := CochainComplex.of_d _ d i
    exact e1.trans (e2.symm.trans
      (congrArg (fun φ : (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj (M i) ⟶
          (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj (M (i + 1)) =>
        (show ↥((logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) (i + 1)).obj W)
          from (G.map φ).val.app W s).1) hCx).symm))

/-- **From the decomposition of `F_*Ω^•` to the statement over `f⁻¹𝒪`.** -/
theorem exists_hyp_eq_and_iso_of_frobenius_decomposition (n : ℕ) {Y : Scheme.{0}}
    {κ : CommRingCat.{0}} (f : Y ⟶ Spec κ) [SmoothOfRelativeDimension n f]
    (D : MMP.Mori.Divisor Y) (hD : D.IsRelativeSNC n f) (ε : Bool)
    [HasDerivedCategory.{0} Y.Modules]
    (p : ℕ) [Fact p.Prime] (hp : (p : κ) = 0) (hpt : ∀ a b : Spec κ, a = b) {m : ℕ}
    (hm : 1 ≤ m) (hκ : ∀ x : κ, x ^ p ^ m = x) (hV : IsInCharacteristic Y p)
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj
        (logModule n f D hD (bif ε then D.suppIdeal else ⊤) q) ⟶
      (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj
        (logModule n f D hD (bif ε then D.suppIdeal else ⊤) (q + 1)))
    (hd : ∀ q, d q ≫ d (q + 1) = 0)
    (hdR : ∀ (q : ℕ) (W : Y.Opens)
      (s : Γ(logModule n f D hD (bif ε then D.suppIdeal else ⊤) q, W)),
      (show ↥((logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) (q + 1)).obj (op W))
        from (d q).app W s).1 =
      ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d q (q + 1)).val.app (op ((LU D).ι ⁻¹ᵁ W))
        (show ↥((logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) q).obj (op W))
          from s).1)
    (Φ : (⨁ fun q : Fin (n + 1) => (DerivedCategory.singleFunctor Y.Modules (q : ℤ)).obj
        (logModule n f D hD (bif ε then D.suppIdeal else ⊤) q)) ≅
      DerivedCategory.Q.obj ((CochainComplex.of _ d hd).extend ComplexShape.embeddingUpNat)) :
    let K := relativeLogDeRhamComplex n f D hD (bif ε then D.suppIdeal else ⊤)
    ∃ L : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf))),
      (∀ j : ℤ, Module.finrank Γ(Spec κ, ⊤) (Hc f L j) =
        Module.finrank Γ(Spec κ, ⊤) (Hc f ⟨K.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j)) ∧
      Nonempty (DerivedCategory.Plus.Q.obj L ≅
        ⨁ fun q : Fin (n + 1) => (DerivedCategory.Plus.singleFunctor _ (q : ℤ)).obj (K.X q)) := by
  intro K
  let G : Y.Modules ⥤ SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf)) :=
    pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)
  haveI : G.Additive := inferInstanceAs
    (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).Additive
  haveI : PreservesFiniteLimits G :=
    Stacks.DeRhamDirectImage.preservesFiniteLimits_pushforward_toInverseImageBase f
  haveI : PreservesFiniteColimits G :=
    Stacks.DeRhamDirectImage.preservesFiniteColimits_pushforward_toInverseImageBase f
  let M := fun q : ℕ => logModule n f D hD (bif ε then D.suppIdeal else ⊤) q
  let Cx := CochainComplex.of
    (fun q => (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj (M q)) d hd
  let X : CochainComplex.Plus Y.Modules := ⟨Cx.extend ComplexShape.embeddingUpNat, 0,
    CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩
  let L := G.mapCochainComplexPlus.obj X
  have eK : ∀ q : ℕ, K.X q ≅ G.obj (M q) := fun q =>
    (exists_iso_relativeLogDeRhamComplex_X hD ε q).some
  refine ⟨L, ?_, ⟨plusQMapIsoBiproductOfIso G X (fun q : Fin (n + 1) => M q) Φ.symm ≪≫
    biproduct.mapIso fun q => (DerivedCategory.Plus.singleFunctor _ (q : ℤ)).mapIso
      (eK q).symm⟩⟩
  intro j
  have hK : K = logCx hD ε := relativeLogDeRhamComplex_eq_logCx hD ε
  let E := _root_.SheafOfModules.restrictScalars.{0}
    (frobeniusRingSheafIso f p hp hpt hm hκ).hom
  let ψ : (G.mapHomologicalComplex _).obj Cx ≅ (E.mapHomologicalComplex _).obj (logCx hD ε) :=
    frobeniusLogComplexIso n f D hD ε p hp hpt hm hκ hV d hd hdR
  let eL : L ≅ E.mapCochainComplexPlus.obj ⟨(logCx hD ε).extend ComplexShape.embeddingUpNat, 0,
      CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ :=
    (ObjectProperty.fullyFaithfulι _).preimageIso
      (mapHomologicalComplexExtendIso G Cx ComplexShape.embeddingUpNat ≪≫
        (ComplexShape.embeddingUpNat.extendFunctor _).mapIso ψ ≪≫
        (mapHomologicalComplexExtendIso E (logCx hD ε) ComplexShape.embeddingUpNat).symm)
  rw [hK]
  exact (hypIsoOfIso f eL j).toLinearEquiv.finrank_eq.trans
    (finrank_hyp_frobeniusTwist f p hp hpt hm hκ _ j)

end Transport

open Stacks.Frobenius

/-- A fibre of a scheme over `Spec R` at a point whose residue field has characteristic `p` is a
scheme in characteristic `p`. -/
theorem isInCharacteristic_pullback_fromSpecResidueField {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of R)) (p : ℕ)
    [CharP ((Spec (CommRingCat.of R)).residueField s) p] :
    IsInCharacteristic (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p := by
  have h1 : (p : (Spec (CommRingCat.of R)).residueField s) = 0 := CharP.cast_eq_zero _ p
  have h2 := congrArg ((Scheme.ΓSpecIso _).inv ≫
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).appTop).hom h1
  rwa [map_natCast, map_zero] at h2

open KaehlerDifferential in
/-- `d(b ^ p ξ) = b ^ p dξ` for algebraic forms, when `p` vanishes in `B`. -/
theorem deRhamDifferential_pow_smul_of_natCast_eq_zero {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] (p : ℕ) (hp : (p : B) = 0) (i : ℕ) (b : B) (ξ : ⋀[B]^i (Ω[B⁄A])) :
    deRhamDifferential (A := A) i (b ^ p • ξ) = b ^ p • deRhamDifferential (A := A) i ξ := by
  rw [KaehlerDifferential.deRhamDifferential_smul, Derivation.leibniz_pow,
    ← Nat.cast_smul_eq_nsmul B, hp, zero_smul, exteriorPower.wedgeLeft_zero, LinearMap.zero_apply,
    zero_add]

set_option maxRecDepth 4000 in
/-- The Frobenius linearity of the de Rham differential over an affine open. -/
theorem deRhamComplex_d_pow_smul_affine {k : Type} [Field k] {V : Scheme.{0}}
    (f : V ⟶ Spec (CommRingCat.of k)) (p : ℕ) (hV : IsInCharacteristic V p) (q : ℕ)
    (A : V.affineOpens) (b : Γ(V, A)) (ω : Γ(f.relativeDifferentialForms (q : ℤ), A)) :
    (show Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), A) from
      ((f.deRhamComplex).d q (q + 1)).val.app (op (A : V.Opens)) (b ^ p • ω)) =
      b ^ p • (show Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), A) from
        ((f.deRhamComplex).d q (q + 1)).val.app (op (A : V.Opens)) ω) := by
  letI := MMP.Mori.sectionAlgebra f A
  have hp : (p : Γ(V, A)) = 0 := cast_eq_zero_of_isInCharacteristic hV A
  apply (MMP.DeRham.formsAlgEquiv f (q + 1) A).injective
  have e1 := MMP.DeRham.formsAlgEquiv_d f q A (b ^ p • ω)
  have e2 := MMP.DeRham.formsAlgEquiv_d f q A ω
  have e3 := map_smul (MMP.DeRham.formsAlgEquiv f q A) (b ^ p) ω
  have e4 := map_smul (MMP.DeRham.formsAlgEquiv f (q + 1) A) (b ^ p)
    (show Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), A) from
      ((f.deRhamComplex).d q (q + 1)).val.app (op (A : V.Opens)) ω)
  have e5 := deRhamDifferential_pow_smul_of_natCast_eq_zero (A := k) p hp q b
    (MMP.DeRham.formsAlgEquiv f q A ω)
  exact e1.trans ((congrArg _ e3).trans (e5.trans ((congrArg _ e2.symm).trans e4.symm)))

/-- **The de Rham differential is linear for the Frobenius** on a `k`-scheme in characteristic
`p`: `d (a ^ p ω) = a ^ p dω`. -/
theorem deRhamComplex_d_pow_smul {k : Type} [Field k] {V : Scheme.{0}}
    (f : V ⟶ Spec (CommRingCat.of k)) (p : ℕ) (hV : IsInCharacteristic V p) (q : ℕ)
    (O : V.Opens) (a : Γ(V, O)) (ω : Γ(f.relativeDifferentialForms (q : ℤ), O)) :
    (show Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), O) from
      ((f.deRhamComplex).d q (q + 1)).val.app (op O) (a ^ p • ω)) =
      a ^ p • (show Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), O) from
        ((f.deRhamComplex).d q (q + 1)).val.app (op O) ω) := by
  let Ω₁ := f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)
  let dO : ∀ O' : V.Opens, Γ(f.relativeDifferentialForms (q : ℤ), O') → Γ(Ω₁, O') := fun O' x =>
    ((f.deRhamComplex).d q (q + 1)).val.app (op O') x
  have hnat : ∀ (A : V.affineOpens) (hA : (A : V.Opens) ≤ O)
      (x : Γ(f.relativeDifferentialForms (q : ℤ), O)),
      Ω₁.presheaf.map (homOfLE hA).op (dO O x) =
        dO A ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op x) :=
    fun A hA x => (PresheafOfModules.naturality_apply
      ((f.deRhamComplex).d q (q + 1)).val (homOfLE hA).op x).symm
  have key : dO O (a ^ p • ω) - a ^ p • dO O ω = 0 := by
    refine MMP.DeRham.eq_zero_of_forall_affineOpens_le _ fun A hA => ?_
    have h1 := hnat A hA (a ^ p • ω)
    have h2 := hnat A hA ω
    have h3 := deRhamComplex_d_pow_smul_affine f p hV q A (V.presheaf.map (homOfLE hA).op a)
      ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op ω)
    rw [map_sub, Scheme.Modules.map_smul, h1, h2, Scheme.Modules.map_smul, map_pow]
    exact sub_eq_zero.mpr h3
  exact sub_eq_zero.mp key

/-- **The de Rham differential of the logarithmic forms is linear for the Frobenius.** On a
scheme in characteristic `p`, `d (a ^ p ω) = a ^ p d ω`, so the logarithmic de Rham differential is
a morphism `F_*Ω^q(log D) ⟶ F_*Ω^{q+1}(log D)` of `𝒪`-modules. -/
theorem exists_frobeniusLinear_logDeRham_d (n : ℕ) {Y : Scheme.{0}} {k : Type} [Field k]
    (f : Y ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor Y)
    (hD : D.IsRelativeSNC n f) (ε : Bool) (p : ℕ) [Fact p.Prime]
    (hV : IsInCharacteristic Y p) :
    ∃ (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD (bif ε then D.suppIdeal else ⊤) q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n f D hD (bif ε then D.suppIdeal else ⊤) (q + 1)))
      (hd : ∀ q, d q ≫ d (q + 1) = 0),
      ∀ (q : ℕ) (W : Y.Opens) (x : Γ(G1.logModule n f D hD (bif ε then D.suppIdeal else ⊤) q, W)),
        (show ↥((G1.logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) (q + 1)).obj
          (op W)) from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU D).ι ≫ f)).d q (q + 1)).val.app
          (op ((G1.LU D).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) q).obj (op W))
            from x).1 := by
  have hU : IsInCharacteristic (G1.LU D).toScheme p := by
    have h := congrArg (G1.LU D).ι.appTop.hom hV
    rwa [map_natCast, map_zero] at h
  let dR := fun q : ℕ => (Scheme.Hom.deRhamComplex ((G1.LU D).ι ≫ f)).d q (q + 1)
  let δ : ∀ (q : ℕ) (W : (TopologicalSpace.Opens Y)ᵒᵖ),
      ↥((G1.logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) q).obj W) →+
        ↥((G1.logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) (q + 1)).obj W) :=
    fun q W =>
    { toFun := fun x => ⟨(dR q).val.app (op ((G1.LU D).ι ⁻¹ᵁ W.unop)) x.1,
        G1.deRham_mem_relativeLogForms hD ε q W.unop x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1) }
  let d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
        (G1.logModule n f D hD (bif ε then D.suppIdeal else ⊤) q) ⟶
      (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
        (G1.logModule n f D hD (bif ε then D.suppIdeal else ⊤) (q + 1)) := fun q =>
    ⟨PresheafOfModules.homMk
      { app := fun W => AddCommGrpCat.ofHom (δ q W)
        naturality := fun W W' g => by
          ext x
          apply Subtype.ext
          show ((G1.jStar f (G1.LU D)).map (dR q)).val.app W'
              ((G1.KX f (G1.LU D) q).val.map g x.1) =
            (G1.KX f (G1.LU D) (q + 1)).val.map g
              (((G1.jStar f (G1.LU D)).map (dR q)).val.app W x.1)
          exact PresheafOfModules.naturality_apply
            ((G1.jStar f (G1.LU D)).map (dR q)).val g x.1 }
      fun W r x => Subtype.ext (by
        have e := deRhamComplex_d_pow_smul ((G1.LU D).ι ≫ f) p hU q
          ((G1.LU D).ι ⁻¹ᵁ W.unop) (((G1.LU D).ι.app W.unop).hom r) x.1
        have hr : ((G1.LU D).ι.app W.unop).hom ((absoluteFrobenius Y p hV).app W.unop
            (show Γ(Y, W.unop) from r)) = (((G1.LU D).ι.app W.unop).hom r) ^ p :=
          (congrArg _ (absoluteFrobenius_app_apply Y p hV W.unop _)).trans (map_pow _ _ _)
        change (show Γ(((G1.LU D).ι ≫ f).relativeDifferentialForms ((q + 1 : ℕ) : ℤ),
            (G1.LU D).ι ⁻¹ᵁ W.unop) from (dR q).val.app (op ((G1.LU D).ι ⁻¹ᵁ W.unop))
            ((show Γ((G1.LU D).toScheme, (G1.LU D).ι ⁻¹ᵁ W.unop) from
              ((G1.LU D).ι.app W.unop).hom ((absoluteFrobenius Y p hV).app W.unop r)) •
              (show Γ(((G1.LU D).ι ≫ f).relativeDifferentialForms (q : ℤ),
                (G1.LU D).ι ⁻¹ᵁ W.unop) from x.1))) =
          (show Γ((G1.LU D).toScheme, (G1.LU D).ι ⁻¹ᵁ W.unop) from
              ((G1.LU D).ι.app W.unop).hom ((absoluteFrobenius Y p hV).app W.unop r)) •
            (show Γ(((G1.LU D).ι ≫ f).relativeDifferentialForms ((q + 1 : ℕ) : ℤ),
              (G1.LU D).ι ⁻¹ᵁ W.unop) from (dR q).val.app (op ((G1.LU D).ι ⁻¹ᵁ W.unop)) x.1)
        rw [hr]
        exact e)⟩
  refine ⟨d, fun q => ?_, fun q W x => rfl⟩
  ext W x
  apply Subtype.ext
  exact congrArg (fun φ => φ.val.app (op ((G1.LU D).ι ⁻¹ᵁ W)) x.1)
    ((Scheme.Hom.deRhamComplex ((G1.LU D).ι ≫ f)).d_comp_d q (q + 1) (q + 2))

section CoordQuotient

open TensorProduct KaehlerDifferential

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

/-- The retraction of the conormal map attached to part of a coordinate system. -/
noncomputable def coordRetraction {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (S : Finset (Fin n)) :
    (B ⧸ Ideal.span (t '' S)) ⊗[B] Ω[B⁄R] →ₗ[B]
      (RingHom.ker (algebraMap B (B ⧸ Ideal.span (t '' S)))).Cotangent :=
  let J := RingHom.ker (algebraMap B (B ⧸ Ideal.span (t '' S)))
  have hker : J = Ideal.span (t '' S) := Ideal.mk_ker
  have htJ : ∀ i ∈ S, t i ∈ J := fun i hi => by
    rw [hker]; exact Ideal.subset_span ⟨i, hi, rfl⟩
  have hsmul : ∀ x : B, x ∈ J → ∀ z : J.Cotangent, x • z = 0 := by
    intro x hx z
    obtain ⟨⟨y, hy⟩, rfl⟩ := J.toCotangent_surjective z
    rw [← map_smul, Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul hx hy
  ∑ i ∈ S.attach,
    let g : B →ₗ[B] J.Cotangent :=
      LinearMap.toSpanSingleton B _ (J.toCotangent ⟨t i, htJ i i.2⟩)
    let g' : (B ⧸ Ideal.span (t '' S)) →ₗ[B] J.Cotangent :=
      Submodule.liftQ _ g (fun x hx => by
        rw [LinearMap.mem_ker]
        exact hsmul x (by rwa [hker]) _)
    g' ∘ₗ (TensorProduct.rid B (B ⧸ Ideal.span (t '' S))).toLinearMap ∘ₗ
      LinearMap.lTensor (B ⧸ Ideal.span (t '' S)) (b.coord i)

/-- `coordRetraction t b S` is a left inverse of the conormal map
`kerCotangentToTensor R B (B ⧸ Ideal.span (t '' S))`. -/
theorem coordRetraction_comp {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (S : Finset (Fin n)) :
    coordRetraction t b S ∘ₗ kerCotangentToTensor R B (B ⧸ Ideal.span (t '' S)) =
      LinearMap.id := by
  classical
  set J := RingHom.ker (algebraMap B (B ⧸ Ideal.span (t '' S)))
  have hker : J = Ideal.span (t '' S) := Ideal.mk_ker
  apply LinearMap.ext
  intro z
  obtain ⟨⟨x, hx⟩, rfl⟩ := J.toCotangent_surjective z
  have hxI : x ∈ Ideal.span (t '' S) := by rwa [← hker]
  induction hxI using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    change coordRetraction t b S (1 ⊗ₜ D R B (t i)) = J.toCotangent ⟨t i, hx⟩
    rw [← hb i]
    unfold coordRetraction
    rw [LinearMap.sum_apply, Finset.sum_eq_single ⟨i, hi⟩]
    · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
        Module.Basis.coord_apply, Module.Basis.repr_self, LinearEquiv.coe_coe,
        TensorProduct.rid_tmul, Finsupp.single_eq_same, one_smul]
      exact one_smul B (J.toCotangent ⟨t i, hx⟩)
    · intro k _ hk
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
        Module.Basis.coord_apply, Module.Basis.repr_self, LinearEquiv.coe_coe,
        TensorProduct.rid_tmul]
      rw [Finsupp.single_eq_of_ne (fun h => hk (Subtype.ext h)), zero_smul, map_zero]
    · simp
  | zero =>
    have : (⟨0, hx⟩ : J) = 0 := rfl
    rw [this, map_zero, map_zero, map_zero]
  | add y w hy hw ihy ihw =>
    have hy' : y ∈ J := by rwa [hker]
    have hw' : w ∈ J := by rwa [hker]
    have : (⟨y + w, hx⟩ : J) = ⟨y, hy'⟩ + ⟨w, hw'⟩ := rfl
    rw [this, map_add, map_add, map_add, ihy hy', ihw hw']
  | smul c y hy ih =>
    have hy' : y ∈ J := by rwa [hker]
    have : (⟨c • y, hx⟩ : J) = c • ⟨y, hy'⟩ := rfl
    rw [this, map_smul, LinearMap.comp_apply, map_smul, map_smul, ← LinearMap.comp_apply, ih hy']
    rfl

/-- For `y` in the ideal generated by the coordinates in `S`, the coordinates of `dy` outside `S`
lie in that ideal. -/
theorem coord_D_mem_of_mem_span {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (S : Finset (Fin n)) {k : Fin n} (hk : k ∉ S) {y : B} (hy : y ∈ Ideal.span (t '' S)) :
    b.coord k (D R B y) ∈ Ideal.span (t '' S) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [← hb i, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      if_neg (fun h : i = k => hk (h ▸ hi))]
    exact zero_mem _
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y w _ _ ihy ihw => rw [map_add, map_add]; exact add_mem ihy ihw
  | smul c y hy ih =>
    rw [smul_eq_mul, Derivation.leibniz, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ hy)

/-- The coordinates outside `S` of a form on `B ⧸ (t_S)`. -/
noncomputable def outsideCoords {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (S : Finset (Fin n)) :
    (B ⧸ Ideal.span (t '' S)) ⊗[B] Ω[B⁄R] →ₗ[B ⧸ Ideal.span (t '' S)]
      (↥(Finset.univ \ S) → B ⧸ Ideal.span (t '' S)) :=
  LinearMap.pi fun k => (LinearMap.proj k.1) ∘ₗ
    ((b.baseChange (B ⧸ Ideal.span (t '' S))).equivFun).toLinearMap

/-- A form on `B ⧸ (t_S)` has vanishing coordinates outside `S` if and only if its image in
the Kähler differentials of `B ⧸ (t_S)` vanishes. -/
theorem outsideCoords_eq_zero_iff {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (S : Finset (Fin n)) (x : (B ⧸ Ideal.span (t '' S)) ⊗[B] Ω[B⁄R]) :
    outsideCoords t b S x = 0 ↔
      KaehlerDifferential.mapBaseChange R B (B ⧸ Ideal.span (t '' S)) x = 0 := by
  classical
  set C := B ⧸ Ideal.span (t '' S)
  set J := RingHom.ker (algebraMap B C)
  have hker : J = Ideal.span (t '' S) := Ideal.mk_ker
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R B C
    Ideal.Quotient.mk_surjective
  rw [hex x]
  constructor
  · intro hx
    have hzero : ∀ i ∉ S, (b.baseChange C).repr x i = 0 := fun i hi =>
      congrFun hx ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
    choose y hy using fun i => Ideal.Quotient.mk_surjective ((b.baseChange C).repr x i)
    have htJ : ∀ i ∈ S, t i ∈ J := fun i hi => by
      rw [hker]; exact Ideal.subset_span ⟨i, hi, rfl⟩
    refine ⟨∑ i ∈ S.attach, y i • J.toCotangent ⟨t i, htJ i i.2⟩, ?_⟩
    rw [map_sum]
    conv_rhs => rw [← (b.baseChange C).sum_repr x]
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by rw [hzero i hi, zero_smul]),
      ← Finset.sum_attach S]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    change y i • (1 ⊗ₜ D R B (t i)) = _
    rw [Module.Basis.baseChange_apply, ← hb, ← hy i]
    exact (algebraMap_smul C (y i) _).symm
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := J.toCotangent_surjective z
    funext k
    change ((b.baseChange C).repr (1 ⊗ₜ D R B y)) k.1 = 0
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    have hk : k.1 ∉ S := (Finset.mem_sdiff.mp k.2).2
    have := coord_D_mem_of_mem_span t b hb S hk
      (show y ∈ Ideal.span (t '' S) by rwa [← hker])
    rw [Module.Basis.coord_apply] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this

/-- The map to the coordinates outside `S` is surjective. -/
theorem outsideCoords_surjective {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (S : Finset (Fin n)) :
    Function.Surjective (outsideCoords t b S) := by
  classical
  intro v
  refine ⟨(b.baseChange (B ⧸ Ideal.span (t '' S))).equivFun.symm
    (fun i => if h : i ∈ Finset.univ \ S then v ⟨i, h⟩ else 0), ?_⟩
  funext k
  change (b.baseChange _).equivFun ((b.baseChange _).equivFun.symm _) k.1 = v k
  rw [LinearEquiv.apply_symm_apply, dif_pos k.2]

/-- **The Kähler differentials of the quotient by part of a coordinate system** are free on the
remaining coordinates. -/
noncomputable def kaehlerQuotientCoordEquiv {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (S : Finset (Fin n)) :
    Ω[(B ⧸ Ideal.span (t '' S))⁄R] ≃ₗ[B ⧸ Ideal.span (t '' S)]
      (↥(Finset.univ \ S) → B ⧸ Ideal.span (t '' S)) :=
  (LinearMap.quotKerEquivOfSurjective _ (KaehlerDifferential.mapBaseChange_surjective R B _
      Ideal.Quotient.mk_surjective)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (by
        ext x
        rw [LinearMap.mem_ker, LinearMap.mem_ker, outsideCoords_eq_zero_iff t b hb S x])).trans
      (LinearMap.quotKerEquivOfSurjective _ (outsideCoords_surjective t b S)))

/-- The quotient by part of a coordinate system is formally smooth. -/
theorem formallySmooth_quotient_span_image_coord [Algebra.FormallySmooth R B] {n : ℕ}
    (t : Fin n → B) (b : Module.Basis (Fin n) B Ω[B⁄R])
    (hb : ∀ i, b i = KaehlerDifferential.D R B (t i)) (S : Finset (Fin n)) :
    Algebra.FormallySmooth R (B ⧸ Ideal.span (t '' S)) := by
  rw [Algebra.FormallySmooth.iff_split_injection (P := B) Ideal.Quotient.mk_surjective]
  exact ⟨coordRetraction t b S, coordRetraction_comp t b hb S⟩

/-- **The quotient of a smooth algebra by part of a coordinate system is locally standard smooth
of the complementary relative dimension.** -/
theorem exists_isStandardSmoothOfRelativeDimension_quotient_coord [Algebra.Smooth R B] {n : ℕ}
    (t : Fin n → B) (b : Module.Basis (Fin n) B Ω[B⁄R])
    (hb : ∀ i, b i = KaehlerDifferential.D R B (t i)) (S : Finset (Fin n))
    (𝔮 : Ideal (B ⧸ Ideal.span (t '' S))) [𝔮.IsPrime] :
    ∃ g ∉ 𝔮, Algebra.IsStandardSmoothOfRelativeDimension (n - S.card) R (Localization.Away g) := by
  classical
  set C := B ⧸ Ideal.span (t '' S)
  haveI := formallySmooth_quotient_span_image_coord t b hb S
  haveI : Algebra.FinitePresentation R C :=
    Algebra.FinitePresentation.quotient ⟨(S.image t), by simp⟩
  haveI : Algebra.Smooth R C := ⟨inferInstance, inferInstance⟩
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R 𝔮
  refine ⟨g, hg, ?_⟩
  haveI : Nontrivial (Localization.Away g) := by
    refine OreLocalization.nontrivial_iff.mpr ?_
    rintro ⟨k, hk⟩
    have hk' : g ^ k = 0 := hk
    exact hg (Ideal.IsPrime.mem_of_pow_mem inferInstance k (hk' ▸ 𝔮.zero_mem))
  haveI : Algebra.FormallyEtale C (Localization.Away g) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  let e : Ω[(Localization.Away g)⁄R] ≃ₗ[Localization.Away g]
      (↥(Finset.univ \ S) → Localization.Away g) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R C (Localization.Away g)).symm.trans
      ((LinearEquiv.baseChange C (Localization.Away g) _ _
        (kaehlerQuotientCoordEquiv t b hb S)).trans
        (TensorProduct.piScalarRight C (Localization.Away g) (Localization.Away g) _))
  rw [e.rank_eq, rank_fun', Fintype.card_coe, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, Fintype.card_fin]

end CoordQuotient

/-- **Every component of a relative snc divisor through a point of a chart is a chart
component.** -/
theorem exists_eq_of_mem_support_of_chart {X : Scheme.{0}} (D : MMP.Mori.Divisor X)
    {n : ℕ} {W : X.affineOpens} (t : Fin n → Γ(X, W)) {r : ℕ} (hr : r ≤ n)
    (j : Fin r → MMP.Mori.PrimeDivisor X)
    (hj : ∀ i, (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (hDW : D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)})
    {x : X} (hx : x ∈ (W : X.Opens)) {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ D.support)
    (hxE : x ∈ E.support) : ∃ i, j i = E := by
  set η := AlgebraicGeometry.PrimeDivisor.genericPoint E
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hxE
  have hηW : η ∈ (W : X.Opens) := hηx.mem_open W.1.isOpen hx
  have hηE : η ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hηD : η ∈ D.supp :=
    MMP.Mori.DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE) hηE
  have hηI : η ∈ D.suppIdeal.support :=
    (Scheme.IdealSheafData.gc.l_u_le D.supp) hηD
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hηW, hDW, Scheme.mem_zeroLocus_iff] at hηI
  have hprod := hηI _ (Ideal.mem_span_singleton_self _)
  obtain ⟨i, hi⟩ : ∃ i, η ∉ X.basicOpen (t (Fin.castLE hr i)) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hprod <| Finset.prod_induction _ (fun a => η ∈ X.basicOpen a)
      (fun a b ha hb => by rw [Scheme.basicOpen_mul]; exact ⟨ha, hb⟩)
      (by rw [Scheme.basicOpen_one]; trivial) (fun i _ => hcon i)
  have hηj : η ∈ (j i).support := by
    change η ∈ (j i).idealSheaf.support
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hηW, hj, Scheme.mem_zeroLocus_iff]
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [Scheme.basicOpen_mul]
    exact fun h => hi h.2
  have hsp : AlgebraicGeometry.PrimeDivisor.genericPoint (j i) ⤳ η := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hηj
  refine ⟨i, AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_⟩
  exact eq_of_specializes_of_coheight_eq_one hsp
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint _)
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint _)

/-- In a chart of a relative snc divisor, the components in `T` correspond bijectively to the chart
indices cut out by `T`. -/
theorem card_eq_card_of_chart {X : Scheme.{0}} {D : MMP.Mori.Divisor X} {r : ℕ}
    {j : Fin r → MMP.Mori.PrimeDivisor X} (hjinj : Function.Injective j) (T : Finset D.support)
    (hTj : ∀ E ∈ T, ∃ i, j i = E.1) (Sr : Finset (Fin r))
    (hSr : ∀ i, i ∈ Sr ↔ ∃ E ∈ T, E.1 = j i) : T.card = Sr.card := by
  refine Finset.card_bij (fun E hE => (hTj E hE).choose) (fun E hE => ?_)
    (fun E₁ h₁ E₂ h₂ h => ?_) (fun i hi => ?_)
  · exact (hSr _).2 ⟨E, hE, (hTj E hE).choose_spec.symm⟩
  · exact Subtype.ext ((hTj E₁ h₁).choose_spec.symm.trans
      ((congrArg j h).trans (hTj E₂ h₂).choose_spec))
  · obtain ⟨E, hE, hEi⟩ := (hSr i).1 hi
    exact ⟨E, hE, hjinj ((hTj E hE).choose_spec.trans hEi)⟩

/-- In a chart of a relative snc divisor, the ideal of the intersection of the components in `T`
is generated by the coordinates cutting them out. -/
theorem ideal_iSup_idealSheaf_eq_span_image {X : Scheme.{0}} {D : MMP.Mori.Divisor X} {n : ℕ}
    {W : X.affineOpens} (t : Fin n → Γ(X, W)) {r : ℕ} (hr : r ≤ n)
    (j : Fin r → MMP.Mori.PrimeDivisor X)
    (hj : ∀ i, (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (T : Finset D.support) (hTj : ∀ E ∈ T, ∃ i, j i = E.1) (Sr : Finset (Fin r))
    (hSr : ∀ i, i ∈ Sr ↔ ∃ E ∈ T, E.1 = j i) :
    (⨆ E ∈ T, (E.1 : MMP.Mori.PrimeDivisor X).idealSheaf).ideal W =
      Ideal.span (t '' (Sr.map (Fin.castLEEmb hr) : Finset (Fin n))) := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    refine iSup_le fun E => ?_
    by_cases hE : E ∈ T
    swap
    · rw [iSup_neg hE, Scheme.IdealSheafData.ideal_bot]
      exact bot_le
    rw [iSup_pos hE]
    obtain ⟨i, hi⟩ := hTj E hE
    rw [← hi, hj i]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr
      ⟨Fin.castLE hr i, Finset.mem_map.mpr ⟨i, (hSr i).2 ⟨E, hE, hi.symm⟩, rfl⟩, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨E, hE, hEi⟩ := (hSr i).1 hi
    have hle : (E.1 : MMP.Mori.PrimeDivisor X).idealSheaf ≤
        ⨆ E ∈ T, (E.1 : MMP.Mori.PrimeDivisor X).idealSheaf := le_iSup₂_of_le E hE le_rfl
    refine hle W ?_
    rw [hEi, hj i]
    exact Ideal.mem_span_singleton_self _

/-- **A closed subscheme cut out by part of a coordinate system of a smooth chart is locally
standard smooth** of the complementary relative dimension around each of its points in the
chart. -/
theorem exists_appLE_isStandardSmooth_of_ideal_eq_span {n : ℕ} {X S : Scheme.{0}} (f : X ⟶ S)
    [Smooth f] (K : X.IdealSheafData) {W : X.affineOpens} {V : S.affineOpens}
    (e : (W : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)) (t : Fin n → Γ(X, W))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(S, V)],
        ∀ i, b i = KaehlerDifferential.D Γ(S, V) Γ(X, W) (t i))
    (s : Finset (Fin n)) (hKW : K.ideal W = Ideal.span (t '' s)) (z : K.subscheme)
    (hxW : K.subschemeι z ∈ (W : X.Opens)) :
    ∃ (V' : K.subscheme.affineOpens) (_ : z ∈ V'.1)
      (e' : V'.1 ≤ (K.subschemeι ≫ f) ⁻¹ᵁ (V : S.Opens)),
      RingHom.IsStandardSmoothOfRelativeDimension (n - s.card)
        ((K.subschemeι ≫ f).appLE V V' e').hom := by
  letI : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W e).hom.toAlgebra
  haveI : Algebra.Smooth Γ(S, V) Γ(X, W) := (f.smooth_appLE V.2 W.2 e).toAlgebra
  obtain ⟨b, hb⟩ := hb
  have hV₀ : IsAffineOpen (K.subschemeι ⁻¹ᵁ (W : X.Opens)) := W.2.preimage _
  let φ := (K.subschemeι.app W).hom
  have hkerφ : RingHom.ker φ = Ideal.span (t '' s) :=
    (Scheme.IdealSheafData.ker_subschemeι_app K W).trans hKW
  let θ : (Γ(X, W) ⧸ Ideal.span (t '' s)) ≃+* Γ(K.subscheme, K.subschemeι ⁻¹ᵁ (W : X.Opens)) :=
    (Ideal.quotEquivOfEq hkerφ.symm).trans
      (RingHom.quotientKerEquivOfSurjective (K.subschemeι_app_surjective W))
  have hz : z ∈ K.subschemeι ⁻¹ᵁ (W : X.Opens) := hxW
  set P := hV₀.primeIdealOf ⟨z, hz⟩
  let 𝔮 : Ideal (Γ(X, W) ⧸ Ideal.span (t '' s)) := P.asIdeal.comap θ.toRingHom
  haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨g, hg𝔮, hstd⟩ := exists_isStandardSmoothOfRelativeDimension_quotient_coord t b hb s 𝔮
  set D := K.subscheme.basicOpen (θ g)
  have hD₀ : D ≤ K.subschemeι ⁻¹ᵁ (W : X.Opens) := K.subscheme.basicOpen_le _
  have hzD : z ∈ D := by
    have hzP : hV₀.fromSpec P = z := hV₀.fromSpec_primeIdealOf ⟨z, hz⟩
    rw [← hzP]
    change P ∈ hV₀.fromSpec ⁻¹ᵁ K.subscheme.basicOpen (θ g)
    rw [hV₀.fromSpec_preimage_basicOpen]
    exact hg𝔮
  have e' : D ≤ (K.subschemeι ≫ f) ⁻¹ᵁ (V : S.Opens) := fun y hy => e (hD₀ hy)
  refine ⟨⟨D, hV₀.basicOpen _⟩, hzD, e', ?_⟩
  let ρ := (K.subscheme.presheaf.map (homOfLE hD₀).op).hom
  have hc : (K.subschemeι ≫ f).appLE V D e' =
      f.appLE V W e ≫ K.subschemeι.app W ≫ K.subscheme.presheaf.map (homOfLE hD₀).op := by
    rw [Scheme.Hom.comp_appLE]
    simp only [Scheme.Hom.appLE, Category.assoc]
    rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp]
    rfl
  letI : Algebra (Γ(X, W) ⧸ Ideal.span (t '' s)) Γ(K.subscheme, D) :=
    (ρ.comp θ.toRingHom).toAlgebra
  haveI : IsLocalization.Away g Γ(K.subscheme, D) := by
    haveI h1 := hV₀.isLocalization_basicOpen (θ g)
    have h2 := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers (θ g))
      Γ(K.subscheme, D) θ.symm
    rwa [Submonoid.map_powers, RingEquiv.symm_apply_apply] at h2
  let ψ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
    Γ(K.subscheme, D)
  have hψ : ((K.subschemeι ≫ f).appLE V D e').hom =
      ψ.toRingEquiv.toRingHom.comp (algebraMap Γ(S, V) (Localization.Away g)) := by
    rw [hc, IsScalarTower.algebraMap_eq Γ(S, V) (Γ(X, W) ⧸ Ideal.span (t '' s))
      (Localization.Away g), ← RingHom.comp_assoc]
    ext a
    change ρ (φ ((f.appLE V W e).hom a)) =
      ψ (algebraMap _ (Localization.Away g) (algebraMap Γ(S, V) _ a))
    rw [AlgEquiv.commutes]
    rfl
  rw [hψ]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left _ _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).mpr hstd)

/-- **Each point of an intersection of components of a relative snc divisor** has a standard
smooth affine neighbourhood of the expected relative dimension, which is nonnegative. -/
theorem exists_appLE_isStandardSmooth_iSup_idealSheaf (n : ℕ) {X S : Scheme.{0}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X) (hD : D.IsRelativeSNC n f)
    (T : Finset D.support) (z : (⨆ j ∈ T, (j.1 : MMP.Mori.PrimeDivisor X).idealSheaf).subscheme) :
    T.card ≤ n ∧ ∃ (U : S.affineOpens)
      (V : (⨆ j ∈ T, (j.1 : MMP.Mori.PrimeDivisor X).idealSheaf).subscheme.affineOpens)
      (_ : z ∈ V.1) (e : V.1 ≤
        ((⨆ j ∈ T, (j.1 : MMP.Mori.PrimeDivisor X).idealSheaf).subschemeι ≫ f) ⁻¹ᵁ U.1),
      RingHom.IsStandardSmoothOfRelativeDimension (n - T.card)
        (((⨆ j ∈ T, (j.1 : MMP.Mori.PrimeDivisor X).idealSheaf).subschemeι ≫ f).appLE
          U V e).hom := by
  classical
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  generalize hK : ⨆ j ∈ T, (j.1 : MMP.Mori.PrimeDivisor X).idealSheaf = K at z ⊢
  obtain ⟨W, V, e, t, hxW, hb, r, hr, j, hjinj, hjD, hDW⟩ := hD.2 (K.subschemeι z)
  have hxK : K.subschemeι z ∈ K.support := by
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hTj : ∀ E ∈ T, ∃ i, j i = E.1 := fun E hE =>
    exists_eq_of_mem_support_of_chart D t hr j (fun i => (hjD i).2.2) hDW hxW E.2
      (Scheme.IdealSheafData.support_antitone (hK ▸ le_iSup₂_of_le E hE le_rfl) hxK)
  let Sr : Finset (Fin r) := Finset.univ.filter (fun i => ∃ E ∈ T, E.1 = j i)
  have hSr : ∀ i, i ∈ Sr ↔ ∃ E ∈ T, E.1 = j i := fun i => by simp [Sr]
  have hcardSr := card_eq_card_of_chart hjinj T hTj Sr hSr
  rw [hcardSr]
  refine ⟨(Finset.card_le_univ _).trans (by simpa using hr), ?_⟩
  rw [← Finset.card_map (Fin.castLEEmb hr)]
  exact ⟨V, exists_appLE_isStandardSmooth_of_ideal_eq_span f K e t hb _
    (hK ▸ ideal_iSup_idealSheaf_eq_span_image t hr j (fun i => (hjD i).2.2) T hTj Sr hSr) z hxW⟩

/-- **The intersections of the components of a relative snc divisor are smooth** of the expected
relative dimension, and empty when there are more components than the relative dimension. -/
theorem smoothOfRelativeDimension_iSup_idealSheaf (n : ℕ) {X S : Scheme.{0}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X) (hD : D.IsRelativeSNC n f)
    (T : Finset D.support) :
    SmoothOfRelativeDimension (n - T.card)
        ((⨆ j ∈ T, (j.1 : MMP.Mori.PrimeDivisor X).idealSheaf).subschemeι ≫ f) ∧
      (n < T.card → IsEmpty (⨆ j ∈ T, (j.1 : MMP.Mori.PrimeDivisor X).idealSheaf).subscheme) := by
  have key := exists_appLE_isStandardSmooth_iSup_idealSheaf n f D hD T
  refine ⟨?_, fun hlt => ⟨fun z => absurd (key z).1 (by omega)⟩⟩
  rw [HasRingHomProperty.iff_exists_appLE_locally (P := @SmoothOfRelativeDimension (n - T.card))
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway _).left
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso]
  exact fun z => (key z).2

/-- Pulling ideal sheaves back along a cartesian square preserves the smoothness and the emptiness
of the intersections. -/
theorem smoothOfRelativeDimension_iSup_comap_of_isPullback {X S X' S' : Scheme.{0}}
    {g : X ⟶ S} {g' : X' ⟶ S'} {a : X' ⟶ X} {c : S' ⟶ S} (h : IsPullback a g' g c)
    {ι : Type*} (I : ι → X.IdealSheafData) (T : Finset ι) (m : ℕ) (hm : Prop)
    (hS : SmoothOfRelativeDimension m ((⨆ j ∈ T, I j).subschemeι ≫ g) ∧
      (hm → IsEmpty (⨆ j ∈ T, I j).subscheme)) :
    SmoothOfRelativeDimension m ((⨆ j ∈ T, (I j).comap a).subschemeι ≫ g') ∧
      (hm → IsEmpty (⨆ j ∈ T, (I j).comap a).subscheme) := by
  have hK : (⨆ j ∈ T, (I j).comap a) = (⨆ j ∈ T, I j).comap a :=
    ((Scheme.IdealSheafData.map_gc a).l_iSup₂).symm
  rw [hK]
  set K := ⨆ j ∈ T, I j
  have h₁ : IsPullback (K.comap a).subschemeι
      (Scheme.IdealSheafData.subschemeMap _ K a (Scheme.IdealSheafData.le_map_comap K a)) a
      K.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _
      (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])
  have h₂ := (h₁.paste_horiz h.flip).flip
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange m
  refine ⟨MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension m) h₂ hS.1,
    fun hm' => ?_⟩
  haveI := hS.2 hm'
  exact Function.isEmpty (Scheme.IdealSheafData.subschemeMap _ K a
    (Scheme.IdealSheafData.le_map_comap K a)).base

/-- The support of the intersection of two ideal sheaves is the union of the supports. -/
theorem support_inf_idealSheafData {X : Scheme.{0}} (I J : X.IdealSheafData) :
    (I ⊓ J).support = I.support ⊔ J.support := by
  apply le_antisymm
  · have h : I * J ≤ I ⊓ J := le_inf (mul_le_of_le_one_right bot_le le_top)
      (mul_le_of_le_one_left bot_le le_top)
    exact (Scheme.IdealSheafData.support_antitone h).trans_eq
      (Scheme.IdealSheafData.support_mul I J)
  · exact sup_le (Scheme.IdealSheafData.support_antitone inf_le_left)
      (Scheme.IdealSheafData.support_antitone inf_le_right)

/-- The support of a finite infimum of ideal sheaves is the union of the supports. -/
theorem support_iInf_of_finite {X : Scheme.{0}} {ι : Type*} [Finite ι]
    (I : ι → X.IdealSheafData) : (⨅ j, I j).support = ⨆ j, (I j).support := by
  classical
  haveI := Fintype.ofFinite ι
  rw [← Finset.inf_univ_eq_iInf, ← Finset.sup_univ_eq_iSup]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [Scheme.IdealSheafData.support_top]
  | insert a s ha ih => rw [Finset.inf_insert, Finset.sup_insert, support_inf_idealSheafData, ih]

end MMP.FourfoldProofs.LogDegenerationProof
