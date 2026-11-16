module
public import MMP.Topology.Sheaves.CompactSupport.CSoft
public import MMP.Topology.Sheaves.ClosedEmbeddingUnit

/-!
# Long exact sequences for cohomology with compact supports

Let `X` be a locally compact Hausdorff space and `R` a commutative ring, and write
`H^q_c(X, F)` for compactly supported cohomology of a sheaf `F` of `R`-modules, the cohomology of
the right derived functor of `Γ_c`. For an open `W ⊆ X` write `j_{W!}` for extension by zero
and `ι_W : H^q_c(W, -) ≅ H^q_c(X, j_{W!} -)` for the comparison isomorphisms of
`MMP.Fourfold.compactSupportCohomology_extendByZero`.

*Closed complement.* Let `Z ⊆ X` be closed with inclusion `i` and `U = X \ Z` with inclusion
`j`. The sequence `0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^{-1} F ⟶ 0` gives a natural long exact sequence
`⋯ ⟶ H^q_c(U, F) ⟶ H^q_c(X, F) ⟶ H^q_c(Z, i^{-1} F) ⟶ H^{q+1}_c(U, F) ⟶ ⋯`.
If `X` is compact, every global section has compact support, so `Γ_c = Γ` and
`H^q_c(X, F) ≅ H^q(X, F)`.

*Mayer–Vietoris.* Let `X = U ∪ V` with `U, V` open. The extension maps
`e : H^q_c(U ∩ V, F) ⟶ H^q_c(U, F)` are induced through `ι` by the inclusion
`j_{U∩V!}(F|_{U∩V}) ⟶ j_{U!}(F|_U)`, and `H^q_c(U, F) ⟶ H^q_c(X, F)` by the counit
`j_{U!}(F|_U) ⟶ F`. There are natural connecting maps `δ : H^q_c(X, F) ⟶ H^{q+1}_c(U ∩ V, F)`
making
`⋯ → H^q_c(U ∩ V) --(e, -e)--> H^q_c(U) ⊕ H^q_c(V) --e + e--> H^q_c(X) --δ--> H^{q+1}_c(U ∩ V)`
exact. It comes from the short exact sequence `0 → j_{U∩V!}F → j_{U!}F ⊕ j_{V!}F → F → 0`.

## Main results

* `MMP.Fourfold.compactSupportCohomology_closedComplement`: the closed complement sequence,
  and `H^q_c = H^q` on a compact space.
* `MMP.Fourfold.compactSupportCohomology_mayerVietoris_exact`: the Mayer–Vietoris sequence.

## Implementation notes

The closed subset is a `TopologicalSpace.Closeds X`, its complement the open
`TopologicalSpace.Closeds.compl`, and `i^{-1}` is `TopCat.Sheaf.pullback`. Sheaf cohomology
`H^q(X, F)` is the cohomology of the right derived functor of `F ↦ F(X)`.

Both short exact sequences of sheaves are checked on stalks. For the closed complement: at a
point of `U` the counit `j_! j^* F ⟶ F` is invertible and `i_* i^{-1} F` has zero stalk, at a
point of `Z` the stalk of `j_! j^* F` vanishes and the unit `F ⟶ i_* i^{-1} F` is invertible.
For Mayer–Vietoris, the counit `j_{W!} j_W^* F ⟶ F` is a monomorphism, bijective on stalks at
points of `W`, and at a point of `U ∩ V`, `U \ V` or `V \ U` the stalk sequence splits.

The comparison `H^q_c(X, i_* -) ≅ H^q_c(Z, -)` comes from the universal property of the right
derived functor: `i_*` is exact, carries injective sheaves to injective (hence c-soft) sheaves,
and `Γ_c(X, i_* H) = Γ_c(Z, H)` since a compact subset of `X` meets `Z` in a compact set. The
closed complement sequence is the homology sequence of `Γ_c` applied to the degreewise short
exact sequence `j_! j^* I ⟶ I ⟶ i_* i^{-1} I` of c-soft complexes, for an injective resolution
`I` of `F`; each term computes `H^q_c` by `MMP.Fourfold.compactSupportCohomology_of_isCSoft`, and
the connecting map is natural because morphisms lift to resolutions uniquely up to homotopy.
The Mayer–Vietoris sequence is instead the homology sequence of the distinguished triangle that
the derived functor of `Γ_c` attaches to its short exact sequence, read through `ι`.

The comparison isomorphisms `ι` and the extension maps of the Mayer–Vietoris statement are those
of `MMP.Fourfold.compactSupportCohomology_extendByZero`; the exactness holds for every choice of
`ι`, since changing `ι` only conjugates the middle term by an automorphism. The map
`H^q_c(U, F) ⟶ H^q_c(X, F)` is written through `ι_U` and the counit, since `X` is not the
subspace `⊤` on the nose.

## References

* [Iversen, *Cohomology of sheaves*, III.7]
-/

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace MMP.Fourfold

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction to an open and extension by zero -/

section ExtendByZero

open ZeroObject

variable {R : Type} [CommRing R]

/-- The stalk functor at `x` on sheaves of `R`-modules. -/
private noncomputable abbrev st {Y : TopCat.{0}} (y : Y) :
    TopCat.Sheaf (ModuleCat.{0} R) Y ⥤ ModuleCat.{0} R :=
  TopCat.Sheaf.forget _ Y ⋙ TopCat.Presheaf.stalkFunctor _ y

variable (R) {X : TopCat.{0}} (U : Opens X)

/-- Restriction `j^*`. -/
private noncomputable abbrev resF :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U) :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _

/-- Extension by zero `j_!`. -/
private noncomputable abbrev extF :
    TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj U) ⥤ TopCat.Sheaf (ModuleCat.{0} R) X :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafPullback _ _ _

private noncomputable abbrev adjF : extF R U ⊣ resF R U :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _

variable {R U} in
/-- The stalk of `j^* A` at `x ∈ U` is the stalk of `A` at `x`, naturally in `A`. -/
private lemma stalk_resF_naturality {A B : TopCat.Sheaf (ModuleCat.{0} R) X} (f : A ⟶ B)
    (x : (Opens.toTopCat X).obj U) :
    (st x).map ((resF R U).map f) ≫
        (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, B.presheaf⟩
          U.isOpenEmbedding x).hom =
      (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, A.presheaf⟩
          U.isOpenEmbedding x).hom ≫ (st x.1).map f := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hV => ?_
  ext s
  have e1 := AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply ⟨X, A.presheaf⟩
    U.isOpenEmbedding V x hV s
  have e2 := AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply ⟨X, B.presheaf⟩
    U.isOpenEmbedding V x hV (((TopCat.Sheaf.forget _ X).map f).app _ s)
  have e3 := TopCat.Presheaf.stalkFunctor_map_germ_apply V x hV ((TopCat.Sheaf.forget _ _).map
    ((resF R U).map f)) s
  have e4 := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (U.isOpenEmbedding.functor.obj V) x.1 ⟨x, hV, rfl⟩ ((TopCat.Sheaf.forget _ X).map f) s
  exact (congrArg (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, B.presheaf⟩
    U.isOpenEmbedding x).hom e3).trans (e2.trans (e4.symm.trans (congrArg
      ((TopCat.Presheaf.stalkFunctor _ x.1).map ((TopCat.Sheaf.forget _ X).map f)) e1.symm)))

private lemma additive_resF : (resF R U).Additive := ⟨fun {_ _ _ _} => by apply Sheaf.hom_ext; rfl⟩

private lemma additive_extF : (extF R U).Additive := by
  have := additive_resF R U
  exact (adjF R U).left_adjoint_additive

attribute [local instance] additive_resF additive_extF

variable {R U} in
private lemma isIso_stalk_counit (hunit : ∀ G, IsIso ((adjF R U).unit.app G))
    (G : TopCat.Sheaf (ModuleCat.{0} R) X) (x : (Opens.toTopCat X).obj U) :
    IsIso ((st x.1).map ((adjF R U).counit.app G)) := by
  have : IsIso ((resF R U).map ((adjF R U).counit.app G)) := by
    have := hunit ((resF R U).obj G)
    have : IsIso ((adjF R U).unit.app ((resF R U).obj G) ≫
        (resF R U).map ((adjF R U).counit.app G)) := by
      rw [(adjF R U).right_triangle_components G]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left ((adjF R U).unit.app ((resF R U).obj G)) _
  rw [← (Iso.inv_comp_eq _).mpr (stalk_resF_naturality ((adjF R U).counit.app G) x)]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' inferInstance (Iso.isIso_hom _))

variable {R U} in
private lemma mono_counit (hunit : ∀ G, IsIso ((adjF R U).unit.app G))
    (hzero : ∀ G, ∀ x ∉ U, IsZero (((extF R U).obj G).presheaf.stalk x))
    (G : TopCat.Sheaf (ModuleCat.{0} R) X) : Mono ((adjF R U).counit.app G) := by
  have hS : (ShortComplex.mk (0 : 0 ⟶ (extF R U).obj ((resF R U).obj G))
      ((adjF R U).counit.app G) zero_comp).Exact := by
    rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    intro x
    rw [ShortComplex.exact_iff_mono _ (((st x).map_isZero (isZero_zero _)).eq_of_src _ _)]
    by_cases hx : x ∈ U
    · exact @IsIso.mono_of_iso _ _ _ _ _ (isIso_stalk_counit hunit G ⟨x, hx⟩)
    · exact mono_of_source_iso_zero _ (IsZero.isoZero (hzero _ x hx))
  exact (ShortComplex.exact_iff_mono _ rfl).mp hS

/-- Compactly supported cohomology as a functor. -/
private noncomputable abbrev HcF (Y : TopCat.{0}) (q : ℤ) :
    TopCat.Sheaf (ModuleCat.{0} R) Y ⥤ ModuleCat.{0} R :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (compactSupportSectionsFunctor R (X := Y)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q

end ExtendByZero

attribute [local instance] additive_resF additive_extF

/-! ### The closed complement sequence -/

namespace ClosedComplement

open ZeroObject

variable {R : Type} [CommRing R]

/-! ### Exactness checked on stalks -/

/-- A functor between categories of sheaves whose stalk at every point either vanishes or is a
stalk of its argument preserves exact sequences. -/
private lemma exact_map_of_stalk {Y X : TopCat.{0}}
    (Φ : TopCat.Sheaf (ModuleCat.{0} R) Y ⥤ TopCat.Sheaf (ModuleCat.{0} R) X) [Φ.Additive]
    (h : ∀ x : X, (∀ G, IsZero ((st (R := R) x).obj (Φ.obj G))) ∨
      ∃ y : Y, Nonempty (Φ ⋙ st (R := R) x ≅ st y))
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) Y)) (hS : S.Exact) : (S.map Φ).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rcases h x with h0 | ⟨y, ⟨e⟩⟩
  · exact ShortComplex.exact_of_isZero_X₂ _ (h0 S.X₂)
  · have hy := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS y
    exact (ShortComplex.exact_iff_of_iso (S.mapNatIso e).symm).mp hy

private lemma preservesHomology_of_stalk {Y X : TopCat.{0}}
    (Φ : TopCat.Sheaf (ModuleCat.{0} R) Y ⥤ TopCat.Sheaf (ModuleCat.{0} R) X) [Φ.Additive]
    (h : ∀ x : X, (∀ G, IsZero ((st (R := R) x).obj (Φ.obj G))) ∨
      ∃ y : Y, Nonempty (Φ ⋙ st (R := R) x ≅ st y)) :
    PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ :=
  (Φ.exact_tfae.out 2 4).mp (exact_map_of_stalk Φ h)

/-- A natural transformation that is invertible on the stalks at `x` of every component gives an
isomorphism of the stalk functors at `x`. -/
private noncomputable def stalkIsoOfIsIso {C : Type*} [Category C] {X : TopCat.{0}}
    {Φ Φ' : C ⥤ TopCat.Sheaf (ModuleCat.{0} R) X} (α : Φ ⟶ Φ') (x : X)
    (h : ∀ G, IsIso ((st x).map (α.app G))) : Φ ⋙ st x ≅ Φ' ⋙ st x :=
  haveI : ∀ G, IsIso ((Functor.whiskerRight α (st x)).app G) := h
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerRight α (st x))
  asIso (Functor.whiskerRight α (st x))

/-! ### The stalks of `j_! j^*` -/

section Open

variable (R) {X : TopCat.{0}} (U : Opens X)

/-- `j_! j^*`. -/
private noncomputable abbrev PF :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X :=
  resF R U ⋙ extF R U

variable {R U} in
private lemma stalk_PF (hunit : ∀ G, IsIso ((adjF R U).unit.app G))
    (hzero : ∀ G, ∀ x ∉ U, IsZero (((extF R U).obj G).presheaf.stalk x)) (x : X) :
    (∀ G, IsZero ((st (R := R) x).obj ((PF R U).obj G))) ∨
      ∃ y : X, Nonempty (PF R U ⋙ st (R := R) x ≅ st y) := by
  by_cases hx : x ∈ U
  · exact Or.inr ⟨x, ⟨stalkIsoOfIsIso _ x fun G => isIso_stalk_counit hunit G ⟨x, hx⟩⟩⟩
  · exact Or.inl fun G => hzero _ x hx

end Open

/-! ### Direct and inverse image along a closed embedding -/

section Closed

variable (R)

/-- The stalk of a direct image `f_* A` at `f y` maps to the stalk of `A` at `y`, naturally. -/
private lemma stalkPushforward_naturality {Y X : TopCat.{0}} (f : Y ⟶ X)
    {A B : TopCat.Presheaf (ModuleCat.{0} R) Y} (φ : A ⟶ B) (y : Y) :
    (TopCat.Presheaf.stalkFunctor _ (f y)).map ((TopCat.Presheaf.pushforward _ f).map φ) ≫
        B.stalkPushforward _ f y =
      A.stalkPushforward _ f y ≫ (TopCat.Presheaf.stalkFunctor _ y).map φ := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hV => ?_
  ext s
  have e1 := TopCat.Presheaf.stalkPushforward_germ_apply _ f A V y hV s
  have e2 := TopCat.Presheaf.stalkPushforward_germ_apply _ f B V y hV (φ.app _ s)
  have e3 := TopCat.Presheaf.stalkFunctor_map_germ_apply V (f y) hV
    ((TopCat.Presheaf.pushforward _ f).map φ) s
  have e4 := TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map f).obj V) y hV φ s
  exact (congrArg (B.stalkPushforward _ f y) e3).trans (e2.trans (e4.symm.trans (congrArg
      ((TopCat.Presheaf.stalkFunctor _ y).map φ) e1.symm)))

variable {R} in
/-- For an inducing map `f`, the stalk of `f_* G` at `f y` is the stalk of `G` at `y`. -/
private noncomputable def pushStalkIso {Y X : TopCat.{0}} {f : Y ⟶ X} (hf : IsInducing f)
    (y : Y) : TopCat.Sheaf.pushforward (ModuleCat.{0} R) f ⋙ st (f y) ≅ st y :=
  NatIso.ofComponents (fun G =>
      @asIso _ _ _ _ (G.presheaf.stalkPushforward _ f y)
        (TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          (ModuleCat.{0} R) hf G.presheaf y))
    (fun φ => stalkPushforward_naturality R f φ.hom y)

variable {X : TopCat.{0}} (Z : Closeds X)

/-- The inclusion `i : Z ⟶ X`. -/
private abbrev incl : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

private lemma isClosedEmbedding_incl : IsClosedEmbedding (incl Z) :=
  Z.isClosed.isClosedEmbedding_subtypeVal

/-- `i_*`. -/
private noncomputable abbrev pushF :
    TopCat.Sheaf (ModuleCat.{0} R) (TopCat.of Z) ⥤ TopCat.Sheaf (ModuleCat.{0} R) X :=
  TopCat.Sheaf.pushforward (ModuleCat.{0} R) (incl Z)

/-- `i^{-1}`. -/
private noncomputable abbrev pullF :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) (TopCat.of Z) :=
  TopCat.Sheaf.pullback (ModuleCat.{0} R) (incl Z)

private noncomputable abbrev adjZ : pullF R Z ⊣ pushF R Z :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} R) (incl Z)

private lemma additive_pushF : (pushF R Z).Additive :=
  ⟨fun {_ _ _ _} => by apply Sheaf.hom_ext; rfl⟩

private lemma additive_pullF : (pullF R Z).Additive := by
  have := additive_pushF R Z
  exact (adjZ R Z).left_adjoint_additive

attribute [local instance] additive_pushF additive_pullF

/-- `i_* i^{-1}`. -/
private noncomputable abbrev TF :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X :=
  pullF R Z ⋙ pushF R Z

private lemma isIso_stalk_unit (G : TopCat.Sheaf (ModuleCat.{0} R) X) (z : Z) :
    IsIso ((st (R := R) z.1).map ((adjZ R Z).unit.app G)) :=
  MMP.Topology.isIso_stalkFunctor_map_unit (isClosedEmbedding_incl Z).isInducing G z

private lemma isZero_stalk_pushF (G : TopCat.Sheaf (ModuleCat.{0} R) (TopCat.of Z)) {x : X}
    (hx : x ∉ Z) : IsZero ((st (R := R) x).obj ((pushF R Z).obj G)) :=
  MMP.Topology.isZero_stalk_pushforward_of_notMem_range
    (isClosedEmbedding_incl Z).isClosed_range G
    (by rwa [show Set.range (incl Z) = (Z : Set X) from Subtype.range_val])

private lemma stalk_pushF (x : X) :
    (∀ G, IsZero ((st (R := R) x).obj ((pushF R Z).obj G))) ∨
      ∃ y : TopCat.of Z, Nonempty (pushF R Z ⋙ st (R := R) x ≅ st y) := by
  by_cases hx : x ∈ Z
  · exact Or.inr ⟨⟨x, hx⟩, ⟨pushStalkIso (isClosedEmbedding_incl Z).isInducing ⟨x, hx⟩⟩⟩
  · exact Or.inl fun G => isZero_stalk_pushF R Z G hx

private lemma stalk_pullF (z : TopCat.of Z) :
    (∀ G, IsZero ((st (R := R) z).obj ((pullF R Z).obj G))) ∨
      ∃ y : X, Nonempty (pullF R Z ⋙ st (R := R) z ≅ st y) :=
  Or.inr ⟨z.1, ⟨(Functor.isoWhiskerLeft (pullF R Z)
    (pushStalkIso (isClosedEmbedding_incl Z).isInducing z)).symm ≪≫
      (stalkIsoOfIsIso _ z.1 fun G => isIso_stalk_unit R Z G z).symm⟩⟩

private lemma stalk_TF (x : X) :
    (∀ G, IsZero ((st (R := R) x).obj ((TF R Z).obj G))) ∨
      ∃ y : X, Nonempty (TF R Z ⋙ st (R := R) x ≅ st y) := by
  by_cases hx : x ∈ Z
  · exact Or.inr ⟨x, ⟨(stalkIsoOfIsIso _ x fun G => isIso_stalk_unit R Z G ⟨x, hx⟩).symm⟩⟩
  · exact Or.inl fun G => isZero_stalk_pushF R Z _ hx

end Closed

attribute [local instance] additive_pushF additive_pullF

/-! ### The sequence `0 ⟶ j_! j^* G ⟶ G ⟶ i_* i^{-1} G ⟶ 0` -/

section Sequence

variable {X : TopCat.{0}} {Z : Closeds X}

/-- The hypotheses on extension by zero used below, as provided by
`MMP.Fourfold.compactSupportCohomology_extendByZero`. -/
private structure ExtHyp (R : Type) [CommRing R] {X : TopCat.{0}} (U : Opens X) : Prop where
  unit : ∀ G, IsIso ((adjF R U).unit.app G)
  zero : ∀ G, ∀ x ∉ U, IsZero (((extF R U).obj G).presheaf.stalk x)

private lemma isZero_stalk_PF (h : ExtHyp R Z.compl) (G : TopCat.Sheaf (ModuleCat.{0} R) X)
    {x : X} (hx : x ∈ Z) : IsZero ((st (R := R) x).obj ((PF R Z.compl).obj G)) :=
  h.zero _ x (fun h' => h' hx)

private lemma counit_comp_unit (h : ExtHyp R Z.compl) (G : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (adjF R Z.compl).counit.app G ≫ (adjZ R Z).unit.app G = 0 := by
  apply MMP.Topology.eq_zero_of_stalkFunctor_map_eq_zero
  intro x
  change (st x).map (_ ≫ _) = 0
  rw [Functor.map_comp]
  by_cases hx : x ∈ Z
  · rw [(isZero_stalk_PF h G hx).eq_of_src ((st x).map ((adjF R Z.compl).counit.app G)) 0,
      zero_comp]
  · rw [(isZero_stalk_pushF R Z _ hx).eq_of_tgt ((st x).map ((adjZ R Z).unit.app G)) 0,
      comp_zero]

/-- The short complex `j_! j^* G ⟶ G ⟶ i_* i^{-1} G`. -/
private noncomputable abbrev seq (h : ExtHyp R Z.compl) (G : TopCat.Sheaf (ModuleCat.{0} R) X) :
    ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X) :=
  ShortComplex.mk _ _ (counit_comp_unit h G)

private lemma shortExact_seq (h : ExtHyp R Z.compl) (G : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (seq h G).ShortExact := by
  have := mono_counit h.unit h.zero G
  have := MMP.Topology.epi_unit_of_isClosedEmbedding (isClosedEmbedding_incl Z) G
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  by_cases hx : x ∈ Z
  · rw [ShortComplex.exact_iff_mono _ ((isZero_stalk_PF h G hx).eq_of_src _ _)]
    exact @IsIso.mono_of_iso _ _ _ _ _ (isIso_stalk_unit R Z G ⟨x, hx⟩)
  · rw [ShortComplex.exact_iff_epi _ ((isZero_stalk_pushF R Z _ hx).eq_of_tgt _ _)]
    exact @IsIso.epi_of_iso _ _ _ _ _ (isIso_stalk_counit h.unit G ⟨x, hx⟩)

end Sequence

/-! ### Compactly supported sections of a direct image -/

section GammaPush

variable (R) {X : TopCat.{0}} (Z : Closeds X)

private lemma mem_compactSupportSections_pushF (H : TopCat.Sheaf (ModuleCat.{0} R) (TopCat.of Z))
    (s : H.presheaf.obj (op ⊤)) :
    s ∈ compactSupportSections R ((pushF R Z).obj H) ↔ s ∈ compactSupportSections R H := by
  have hg : ∀ z : TopCat.of Z, ((TopCat.Sheaf.forget _ _).obj ((pushF R Z).obj H)).germ ⊤
      (incl Z z) (Opens.mem_top _) s = 0 ↔
      ((TopCat.Sheaf.forget _ _).obj H).germ ⊤ z (Opens.mem_top _) s = 0 := by
    intro z
    have e := TopCat.Presheaf.stalkPushforward_germ_apply _ (incl Z) H.presheaf ⊤ z
      (Opens.mem_top _) s
    have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (ModuleCat.{0} R) (isClosedEmbedding_incl Z).isInducing H.presheaf z
    have hinj := (ConcreteCategory.bijective_of_isIso
      (H.presheaf.stalkPushforward _ (incl Z) z)).1
    exact ⟨fun h0 => e.symm.trans ((congrArg _ h0).trans (map_zero _)),
      fun h0 => hinj (e.trans (h0.trans (map_zero _).symm))⟩
  constructor
  · rintro ⟨K, hK, hs⟩
    exact ⟨incl Z ⁻¹' K, (isClosedEmbedding_incl Z).isCompact_preimage hK,
      fun z hz => (hg z).mp (hs _ hz)⟩
  · rintro ⟨K, hK, hs⟩
    refine ⟨incl Z '' K, hK.image (incl Z).hom.continuous, fun x hx => ?_⟩
    by_cases hxZ : x ∈ Z
    · exact (hg ⟨x, hxZ⟩).mpr (hs _ fun hz => hx ⟨_, hz, rfl⟩)
    · exact (ModuleCat.isZero_iff_subsingleton.mp (isZero_stalk_pushF R Z H hxZ)).elim _ _

/-- `Γ_c(X, i_* H) = Γ_c(Z, H)` for a closed subspace `Z`. -/
private noncomputable def gammaPushIso :
    pushF R Z ⋙ compactSupportSectionsFunctor R ≅ compactSupportSectionsFunctor R :=
  NatIso.ofComponents (fun H => (LinearEquiv.ofEq _ _ (by
      ext s
      exact mem_compactSupportSections_pushF R Z H s)).toModuleIso)
    (fun _ => rfl)

end GammaPush

/-! ### Comparison of compactly supported cohomology along an exact functor -/

section Derived

variable (R)

/-- c-softness, in the form of `MMP.Fourfold.compactSupportCohomology_of_isCSoft`. -/
private def CSoft {X : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} R) X) : Prop :=
  ∀ K : Set X, IsCompact K → ∀ (W : Opens X), K ⊆ W →
    ∀ s : ((TopCat.Sheaf.forget _ X).obj F).obj (op W),
      ∃ (t : ((TopCat.Sheaf.forget _ X).obj F).obj (op ⊤)) (V : Opens X) (_ : K ⊆ V)
        (hVW : V ≤ W),
        (((TopCat.Sheaf.forget _ X).obj F).map (homOfLE le_top).op).hom t =
          (((TopCat.Sheaf.forget _ X).obj F).map (homOfLE hVW).op).hom s

variable {Y X : TopCat.{0}}
  (E : TopCat.Sheaf (ModuleCat.{0} R) Y ⥤ TopCat.Sheaf (ModuleCat.{0} R) X)
  [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

variable {R E} in
private lemma quasiIso_mapHomotopyCategory
    {K L : HomotopyCategory (TopCat.Sheaf (ModuleCat.{0} R) Y) (ComplexShape.up ℤ)}
    (φ : K ⟶ L) (h : HomotopyCategory.quasiIso _ _ φ) :
    HomotopyCategory.quasiIso _ _ ((E.mapHomotopyCategory _).map φ) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
    ((E.mapHomologicalComplex _).map g)).mpr
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)

/-- An exact functor on bounded below derived categories. -/
private noncomputable def derD :
    DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{0} R) Y) ⥤
      DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{0} R) X) :=
  Localization.lift (W := HomotopyCategory.Plus.quasiIso _)
    (E.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    (fun _ _ f hf => Localization.inverts DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso _) _ (quasiIso_mapHomotopyCategory f.hom hf))
    DerivedCategory.Plus.Qh

private noncomputable def derDFac :
    DerivedCategory.Plus.Qh ⋙ derD R E ≅ E.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  Localization.fac _ _ _

/-- The single functor to `D^+` factors through the bounded below homotopy category. -/
private noncomputable def singleIsoQh (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] :
    DerivedCategory.Plus.singleFunctor C 0 ≅
      HomotopyCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.Qh :=
  ((Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight C).preimageIso
    (DerivedCategory.singleFunctorIsoCompQh C 0)

private noncomputable def singleCompK :
    HomotopyCategory.Plus.singleFunctor _ 0 ⋙ E.mapHomotopyCategoryPlus ≅
      E ⋙ HomotopyCategory.Plus.singleFunctor _ 0 :=
  ((HomotopyCategory.Plus.fullyFaithfulι _).whiskeringRight _).preimageIso
    (by
      refine (?_ : HomotopyCategory.singleFunctor _ 0 ⋙
        E.mapHomotopyCategory (ComplexShape.up ℤ) ≅
          E ⋙ HomotopyCategory.singleFunctor _ 0)
      exact Functor.isoWhiskerRight (HomotopyCategory.singleFunctorPostcompQuotientIso _ 0) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (E.mapHomotopyCategoryFactors _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex E
        (ComplexShape.up ℤ) 0) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (HomotopyCategory.singleFunctorPostcompQuotientIso _ 0).symm)

private noncomputable def singleCompD :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ derD R E ≅
      E ⋙ DerivedCategory.Plus.singleFunctor _ 0 :=
  Functor.isoWhiskerRight (singleIsoQh _) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derDFac R E) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singleCompK R E) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (singleIsoQh _).symm

/-- An exact functor `E` with `Γ_c ∘ E = Γ_c` which carries injective sheaves to c-soft sheaves
induces `H^q_c(Y, -) ≅ H^q_c(X, E -)`. -/
private lemma exists_comparison [LocallyCompactSpace X] [T2Space X]
    (γ : E ⋙ compactSupportSectionsFunctor R ≅ compactSupportSectionsFunctor R)
    (hE : ∀ (J : TopCat.Sheaf (ModuleCat.{0} R) Y) [Injective J], CSoft R (E.obj J)) (q : ℤ) :
    Nonempty (HcF R Y q ≅ E ⋙ HcF R X q) := by
  let ΓY := compactSupportSectionsFunctor R (X := Y)
  let ΓX := compactSupportSectionsFunctor R (X := X)
  let EK := E.mapHomotopyCategoryPlus
  let αY := ΓY.rightDerivedFunctorPlusUnith
  let αX := ΓX.rightDerivedFunctorPlusUnith
  let β : ΓY.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (derD R E ⋙ ΓX.rightDerivedFunctorPlus) :=
    (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryPlusCompIso γ).symm
        DerivedCategory.Plus.Qh).hom ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft EK αX ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (derDFac R E).inv _ ≫
      (Functor.associator _ _ _).hom
  let τ := ΓY.rightDerivedFunctorPlus.rightDerivedDesc αY (HomotopyCategory.Plus.quasiIso _) _ β
  have hβ : ∀ Y' : HomotopyCategory.Plus (InjectiveObject (TopCat.Sheaf (ModuleCat.{0} R) Y)),
      IsIso (β.app ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Y')) := by
    intro Y'
    let K := (InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Y'
    have : IsIso (αX.app (EK.obj K)) :=
      (compactSupportCohomology_of_isCSoft R X).2.2.2.1 ⟨(EK.obj K).obj.as,
        (HomotopyCategory.plus_quotient_obj_iff _).mp (EK.obj K).property⟩
        fun n => hE (K.obj.as.X n)
    simp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  have hτ : IsIso τ := by
    have : ∀ D, IsIso (τ.app D) := by
      intro D
      let Φ := (InjectiveObject.ι (TopCat.Sheaf (ModuleCat.{0} R) Y)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh
      rw [← NatTrans.isIso_app_iff_of_iso τ (Φ.objObjPreimageIso D)]
      have hfac := Functor.rightDerived_fac_app ΓY.rightDerivedFunctorPlus αY
        (HomotopyCategory.Plus.quasiIso _) _ β
        ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj (Φ.objPreimage D))
      have h2 : IsIso (αY.app ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj
          (Φ.objPreimage D)) ≫ τ.app (Φ.obj (Φ.objPreimage D))) := by
        rw [show αY.app ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj (Φ.objPreimage D)) ≫
          τ.app (Φ.obj (Φ.objPreimage D)) = _ from hfac]
        exact hβ _
      exact IsIso.of_isIso_comp_left (αY.app _) (τ.app (Φ.obj (Φ.objPreimage D)))
    exact NatIso.isIso_of_isIso_app _
  exact ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (asIso τ) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singleCompD R E) _ ≪≫ Functor.associator _ _ _⟩

end Derived

/-! ### `H^q_c(X, i_* -) ≅ H^q_c(Z, -)` -/

section Kappa

variable (R) {X : TopCat.{0}} (Z : Closeds X)

private lemma exists_κ [LocallyCompactSpace X] [T2Space X] (q : ℤ) :
    Nonempty (pushF R Z ⋙ HcF R X q ≅ HcF R (TopCat.of Z) q) := by
  obtain ⟨_, _⟩ := preservesHomology_of_stalk _ (stalk_pushF R Z)
  have := (preservesHomology_of_stalk _ (stalk_pullF R Z)).1
  refine ⟨(exists_comparison R (pushF R Z) (gammaPushIso R Z) (fun J _ => ?_) q).some.symm⟩
  have : Injective ((pushF R Z).obj J) := Injective.injective_of_adjoint (adjZ R Z) J
  exact (compactSupportCohomology_of_isCSoft R X).1.2 _ inferInstance

end Kappa

/-! ### Computing `H^q_c` by c-soft complexes -/

section Compute

variable (R) (X : TopCat.{0})

/-- The complex `G[0]` as a bounded below complex. -/
private noncomputable def singlePlus :
    TopCat.Sheaf (ModuleCat.{0} R) X ⥤ CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X) :=
  ObjectProperty.lift _ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
    (fun _ => ⟨0, inferInstance⟩)

/-- `K ↦ H^q(RΓ_c(K))` on bounded below complexes. -/
private noncomputable abbrev Ψ (q : ℤ) :
    CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X) ⥤ ModuleCat.{0} R :=
  HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh ⋙
    (compactSupportSectionsFunctor R (X := X)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q

/-- `K ↦ H^q(Γ_c(K))` on bounded below complexes. -/
private noncomputable abbrev Src (q : ℤ) :
    CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X) ⥤ ModuleCat.{0} R :=
  CochainComplex.Plus.ι _ ⋙ (compactSupportSectionsFunctor R (X := X)).mapHomologicalComplex _ ⋙
    HomologicalComplex.homologyFunctor _ _ q

private noncomputable def singleIsoQuot :
    HomotopyCategory.Plus.singleFunctor (TopCat.Sheaf (ModuleCat.{0} R) X) 0 ≅
      singlePlus R X ⋙ HomotopyCategory.Plus.quotient _ :=
  ((HomotopyCategory.Plus.fullyFaithfulι _).whiskeringRight _).preimageIso
    (HomotopyCategory.Plus.singleFunctorCompιIso _ 0 ≪≫
      HomotopyCategory.singleFunctorPostcompQuotientIso _ 0 ≪≫
      (Functor.isoWhiskerLeft (singlePlus R X) (HomotopyCategory.Plus.quotientCompιIso _)).symm)

/-- `H^q_c(X, G) ≅ H^q(RΓ_c(G[0]))`. -/
private noncomputable def singleIso (q : ℤ) : HcF R X q ≅ singlePlus R X ⋙ Ψ R X q :=
  Functor.isoWhiskerRight (singleIsoQh _ ≪≫
      Functor.isoWhiskerRight (singleIsoQuot R X) DerivedCategory.Plus.Qh) _

private noncomputable def srcIso (q : ℤ) :
    Src R X q ≅ HomotopyCategory.Plus.quotient _ ⋙
      (compactSupportSectionsFunctor R (X := X)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor _ q :=
  Functor.isoWhiskerLeft (CochainComplex.Plus.ι _ ⋙
      (compactSupportSectionsFunctor R (X := X)).mapHomologicalComplex _)
    ((HomotopyCategory.homologyFunctorFactors _ _ q).symm ≪≫
      Functor.isoWhiskerLeft (HomotopyCategory.quotient _ _)
        (DerivedCategory.homologyFunctorFactorsh _ q).symm) ≪≫
  Functor.isoWhiskerLeft (CochainComplex.Plus.ι _)
    (Functor.isoWhiskerRight
      ((compactSupportSectionsFunctor R (X := X)).mapHomotopyCategoryFactors _).symm
      (DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor _ q)) ≪≫
  Iso.refl _

/-- The comparison `H^q(Γ_c(K)) ⟶ H^q(RΓ_c(K))`. -/
private noncomputable def θ (q : ℤ) : Src R X q ⟶ Ψ R X q :=
  (srcIso R X q).hom ≫ Functor.whiskerLeft (HomotopyCategory.Plus.quotient _)
    (Functor.whiskerRight (compactSupportSectionsFunctor R (X := X)).rightDerivedFunctorPlusUnith
      (DerivedCategory.Plus.homologyFunctor _ q))

private lemma isIso_θ_app [LocallyCompactSpace X] [T2Space X] (q : ℤ)
    (K : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)) (hK : ∀ n, CSoft R (K.obj.X n)) :
    IsIso ((θ R X q).app K) := by
  have := (compactSupportCohomology_of_isCSoft R X).2.2.2.1 K hK
  simp only [θ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end Compute

/-! ### Injective resolutions and lifts of morphisms -/

section Resolution

variable (R) {X : TopCat.{0}}

private lemma exists_resolution (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    ∃ (I : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X))
      (e : (singlePlus R X).obj F ⟶ I),
      (∀ n, Injective (I.obj.X n)) ∧ I.obj.IsKInjective ∧ QuasiIso e.hom := by
  have : ((singlePlus R X).obj F).obj.IsStrictlyGE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) 0)
  obtain ⟨L, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective ((singlePlus R X).obj F) 0
  exact ⟨_, i, fun n => (L.obj.X n).property, inferInstanceAs (CochainComplex.IsKInjective
    (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj L.obj)), hi⟩

variable {R} in
private lemma exists_lift {F F' : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ F')
    {I I' : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)}
    (e : (singlePlus R X).obj F ⟶ I) (e' : (singlePlus R X).obj F' ⟶ I')
    [QuasiIso e.hom] [I'.obj.IsKInjective] :
    ∃ f : I ⟶ I', (HomotopyCategory.Plus.quotient _).map (e ≫ f) =
      (HomotopyCategory.Plus.quotient _).map ((singlePlus R X).map φ ≫ e') := by
  let Q := HomotopyCategory.quotient (TopCat.Sheaf (ModuleCat.{0} R) X) (ComplexShape.up ℤ)
  let a := Q.map e.hom
  let b := Q.map (((singlePlus R X).map φ).hom ≫ e'.hom)
  have : IsIso (DerivedCategory.Qh.map a) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) a
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance))
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (Q.obj I.obj) I'.obj).2
    (inv (DerivedCategory.Qh.map a) ≫ DerivedCategory.Qh.map b)
  have hab : a ≫ g = b := (CochainComplex.IsKInjective.Qh_map_bijective
    (Q.obj ((singlePlus R X).obj F).obj) I'.obj).1 (by
      rw [Functor.map_comp, hg, IsIso.hom_inv_id_assoc])
  obtain ⟨f, rfl⟩ := Q.map_surjective g
  refine ⟨ObjectProperty.homMk f, ?_⟩
  ext
  simp only [Q, a, b, Functor.map_comp] at hab
  simp only [HomotopyCategory.Plus.quotient_map_hom, ObjectProperty.FullSubcategory.comp_hom,
    Functor.map_comp]
  exact hab

/-- A chosen injective resolution. -/
private noncomputable def rs (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X) :=
  (exists_resolution R F).choose

variable {R}

private noncomputable def rε (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (singlePlus R X).obj F ⟶ rs R F :=
  (exists_resolution R F).choose_spec.choose

private lemma injective_rs (F : TopCat.Sheaf (ModuleCat.{0} R) X) (n : ℤ) :
    Injective ((rs R F).obj.X n) :=
  (exists_resolution R F).choose_spec.choose_spec.1 n

private lemma isKInjective_rs (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (rs R F).obj.IsKInjective :=
  (exists_resolution R F).choose_spec.choose_spec.2.1

private lemma quasiIso_rε (F : TopCat.Sheaf (ModuleCat.{0} R) X) : QuasiIso (rε F).hom :=
  (exists_resolution R F).choose_spec.choose_spec.2.2

/-- A chosen lift of a morphism to the chosen resolutions. -/
private noncomputable def rl {F F' : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ F') :
    rs R F ⟶ rs R F' :=
  haveI := quasiIso_rε F
  haveI := isKInjective_rs F'
  (exists_lift φ (rε F) (rε F')).choose

private lemma rl_spec {F F' : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ F') :
    (HomotopyCategory.Plus.quotient _).map (rε F ≫ rl φ) =
      (HomotopyCategory.Plus.quotient _).map ((singlePlus R X).map φ ≫ rε F') :=
  haveI := quasiIso_rε F
  haveI := isKInjective_rs F'
  (exists_lift φ (rε F) (rε F')).choose_spec

end Resolution

attribute [local instance] isKInjective_rs quasiIso_rε

/-! ### The comparison with `Γ_c` of a c-soft resolution -/

section Comparison

variable {X : TopCat.{0}}

private lemma isIso_Ψ_map (q : ℤ) {K L : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)}
    (g : K ⟶ L) [QuasiIso g.hom] : IsIso ((Ψ R X q).map g) := by
  have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map g)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
        ((HomologicalComplex.mem_quasiIso_iff _).mpr (show QuasiIso g.hom from inferInstance)))
  simp only [Ψ, Functor.comp_map]
  infer_instance

/-- `H^q_c(X, A) ≅ H^q(Γ_c(K))` for a resolution `A[0] ⟶ K` by c-soft sheaves. -/
private noncomputable def cmp [LocallyCompactSpace X] [T2Space X] (q : ℤ)
    {A : TopCat.Sheaf (ModuleCat.{0} R) X}
    {K : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)}
    (ε : (singlePlus R X).obj A ⟶ K) [QuasiIso ε.hom] (hK : ∀ n, CSoft R (K.obj.X n)) :
    (HcF R X q).obj A ≅ (Src R X q).obj K :=
  (singleIso R X q).app A ≪≫ @asIso _ _ _ _ ((Ψ R X q).map ε) (isIso_Ψ_map q ε) ≪≫
    (@asIso _ _ _ _ ((θ R X q).app K) (isIso_θ_app R X q K hK)).symm

private lemma cmp_naturality [LocallyCompactSpace X] [T2Space X] (q : ℤ)
    {A A' : TopCat.Sheaf (ModuleCat.{0} R) X}
    {K K' : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)}
    (ε : (singlePlus R X).obj A ⟶ K) [QuasiIso ε.hom] (hK : ∀ n, CSoft R (K.obj.X n))
    (ε' : (singlePlus R X).obj A' ⟶ K') [QuasiIso ε'.hom] (hK' : ∀ n, CSoft R (K'.obj.X n))
    (ψ : A ⟶ A') (g : K ⟶ K')
    (h : (HomotopyCategory.Plus.quotient _).map (ε ≫ g) =
      (HomotopyCategory.Plus.quotient _).map ((singlePlus R X).map ψ ≫ ε')) :
    (cmp q ε hK).hom ≫ (Src R X q).map g = (HcF R X q).map ψ ≫ (cmp q ε' hK').hom := by
  have hθ := (θ R X q).naturality g
  have hΨ : (Ψ R X q).map ε ≫ (Ψ R X q).map g =
      (Ψ R X q).map ((singlePlus R X).map ψ) ≫ (Ψ R X q).map ε' := by
    simp only [← Functor.map_comp]
    exact congrArg (fun x => (DerivedCategory.Plus.Qh ⋙
      (compactSupportSectionsFunctor R (X := X)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ q).map x) h
  have hs := (singleIso R X q).hom.naturality ψ
  have := isIso_θ_app R X q K hK
  have := isIso_θ_app R X q K' hK'
  simp only [cmp, Iso.trans_hom, Iso.app_hom, asIso_hom, Iso.symm_hom, asIso_inv,
    Category.assoc]
  have h1 : inv ((θ R X q).app K) ≫ (Src R X q).map g =
      (Ψ R X q).map g ≫ inv ((θ R X q).app K') := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hθ, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [h1, ← Category.assoc ((Ψ R X q).map ε), hΨ, ← Category.assoc ((HcF R X q).map ψ), hs]
  simp only [Functor.comp_map, Category.assoc]

end Comparison

/-! ### Applying an exact functor to a resolution -/

section Apply

variable {X : TopCat.{0}}
  (Φ : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X) [Φ.Additive]

/-- `Φ(A)[0] ≅ Φ(A[0])`. -/
private noncomputable def singlePlusComp :
    Φ ⋙ singlePlus R X ≅ singlePlus R X ⋙ Φ.mapCochainComplexPlus :=
  ((CochainComplex.Plus.fullyFaithfulι _).whiskeringRight _).preimageIso
    (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).symm

private lemma singlePlusComp_hom_app_hom (A : TopCat.Sheaf (ModuleCat.{0} R) X) :
    ((singlePlusComp Φ).hom.app A).hom =
      (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).inv.app A :=
  rfl

/-- The resolution `Φ(A)[0] ⟶ Φ(K)` induced by a resolution `A[0] ⟶ K`. -/
private noncomputable def eΦ {A : TopCat.Sheaf (ModuleCat.{0} R) X}
    {K : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)} (e : (singlePlus R X).obj A ⟶ K) :
    (singlePlus R X).obj (Φ.obj A) ⟶ Φ.mapCochainComplexPlus.obj K :=
  (singlePlusComp Φ).hom.app A ≫ Φ.mapCochainComplexPlus.map e

private lemma quasiIso_eΦ [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    {A : TopCat.Sheaf (ModuleCat.{0} R) X}
    {K : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)} (e : (singlePlus R X).obj A ⟶ K)
    [QuasiIso e.hom] : QuasiIso (eΦ Φ e).hom := by
  have h1 : IsIso ((singlePlusComp Φ).hom.app A).hom :=
    inferInstanceAs (IsIso ((CochainComplex.Plus.ι _).map ((singlePlusComp Φ).hom.app A)))
  have h2 : QuasiIso ((Φ.mapHomologicalComplex _).map e.hom) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology e.hom Φ
  have h3 : QuasiIso ((singlePlusComp Φ).hom.app A).hom := quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h3) (hφ' := h2) _ _

private lemma quotient_map_mapCochainComplexPlus
    {K L : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)} {g g' : K ⟶ L}
    (h : (HomotopyCategory.Plus.quotient _).map g = (HomotopyCategory.Plus.quotient _).map g') :
    (HomotopyCategory.Plus.quotient _).map (Φ.mapCochainComplexPlus.map g) =
      (HomotopyCategory.Plus.quotient _).map (Φ.mapCochainComplexPlus.map g') := by
  have h' : (HomotopyCategory.quotient _ _).map g.hom =
      (HomotopyCategory.quotient _ _).map g'.hom :=
    congrArg (fun x => x.hom) h
  ext
  exact HomotopyCategory.eq_of_homotopy _ _
    (Φ.mapHomotopy (HomotopyCategory.homotopyOfEq _ _ h'))

variable {Φ} in
/-- The morphism `Φ(K) ⟶ Φ'(K)` induced by a natural transformation `Φ ⟶ Φ'`. -/
private noncomputable def νI
    {Φ' : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X}
    [Φ'.Additive] (ν : Φ ⟶ Φ') (K : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)) :
    Φ.mapCochainComplexPlus.obj K ⟶ Φ'.mapCochainComplexPlus.obj K :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex ν _).app K.obj)

private lemma quotient_map_eΦ_lift {F F' : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ F')
    {I I' : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)}
    (e : (singlePlus R X).obj F ⟶ I) (e' : (singlePlus R X).obj F' ⟶ I') (f : I ⟶ I')
    (h : (HomotopyCategory.Plus.quotient _).map (e ≫ f) =
      (HomotopyCategory.Plus.quotient _).map ((singlePlus R X).map φ ≫ e')) :
    (HomotopyCategory.Plus.quotient _).map (eΦ Φ e ≫ Φ.mapCochainComplexPlus.map f) =
      (HomotopyCategory.Plus.quotient _).map ((singlePlus R X).map (Φ.map φ) ≫ eΦ Φ e') := by
  have hn := (singlePlusComp Φ).hom.naturality φ
  simp only [Functor.comp_map] at hn
  have h2 : eΦ Φ e ≫ Φ.mapCochainComplexPlus.map f =
      (singlePlusComp Φ).hom.app F ≫ Φ.mapCochainComplexPlus.map (e ≫ f) := by
    simp [eΦ]
  have h3 : (singlePlus R X).map (Φ.map φ) ≫ eΦ Φ e' =
      (singlePlusComp Φ).hom.app F ≫ Φ.mapCochainComplexPlus.map ((singlePlus R X).map φ ≫ e') := by
    simp only [eΦ, ← Category.assoc, hn, Functor.map_comp]
  rw [h2, h3, Functor.map_comp (HomotopyCategory.Plus.quotient _),
    Functor.map_comp (HomotopyCategory.Plus.quotient _), quotient_map_mapCochainComplexPlus Φ h]

variable {Φ} in
private lemma νI_naturality
    {Φ' : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X}
    [Φ'.Additive] (ν : Φ ⟶ Φ') {K L : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)}
    (g : K ⟶ L) :
    Φ.mapCochainComplexPlus.map g ≫ νI ν L = νI ν K ≫ Φ'.mapCochainComplexPlus.map g := by
  ext1
  exact (NatTrans.mapHomologicalComplex ν _).naturality g.hom

variable {Φ} in
private lemma eΦ_νI {Φ' : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X}
    [Φ'.Additive] (ν : Φ ⟶ Φ') {F : TopCat.Sheaf (ModuleCat.{0} R) X}
    {I : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} R) X)} (e : (singlePlus R X).obj F ⟶ I) :
    eΦ Φ e ≫ νI ν I = (singlePlus R X).map (ν.app F) ≫ eΦ Φ' e := by
  have key : (singlePlusComp Φ).hom.app F ≫ νI ν ((singlePlus R X).obj F) =
      (singlePlus R X).map (ν.app F) ≫ (singlePlusComp Φ').hom.app F := by
    ext1
    apply HomologicalComplex.from_single_hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, singlePlusComp_hom_app_hom, νI]
    erw [HomologicalComplex.comp_f]
  simp only [eΦ, Category.assoc, νI_naturality, reassoc_of% key]

end Apply

/-! ### The long exact sequence -/

section LES

variable {X : TopCat.{0}} [LocallyCompactSpace X] [T2Space X] {Z : Closeds X}

omit [LocallyCompactSpace X] [T2Space X] in
private lemma preservesFiniteLimits_TF : PreservesFiniteLimits (TF R Z) :=
  (preservesHomology_of_stalk _ (stalk_TF R Z)).1

omit [LocallyCompactSpace X] [T2Space X] in
private lemma preservesFiniteColimits_TF : PreservesFiniteColimits (TF R Z) :=
  (preservesHomology_of_stalk _ (stalk_TF R Z)).2

attribute [local instance] preservesFiniteLimits_TF preservesFiniteColimits_TF

/-- The inputs on extension by zero, as provided by
`MMP.Fourfold.compactSupportCohomology_extendByZero`. -/
private structure LesHyp (R : Type) [CommRing R] {X : TopCat.{0}} (Z : Closeds X) : Prop where
  ext : ExtHyp R Z.compl
  csoft : ∀ (J : TopCat.Sheaf (ModuleCat.{0} R) X) [Injective J], CSoft R ((PF R Z.compl).obj J)

omit [LocallyCompactSpace X] [T2Space X] in
private lemma preservesFiniteLimits_PF (H : LesHyp R Z) : PreservesFiniteLimits (PF R Z.compl) :=
  (preservesHomology_of_stalk _ (stalk_PF H.ext.unit H.ext.zero)).1

omit [LocallyCompactSpace X] [T2Space X] in
private lemma preservesFiniteColimits_PF (H : LesHyp R Z) :
    PreservesFiniteColimits (PF R Z.compl) :=
  (preservesHomology_of_stalk _ (stalk_PF H.ext.unit H.ext.zero)).2

private lemma csoft_id (F : TopCat.Sheaf (ModuleCat.{0} R) X) (n : ℤ) :
    CSoft R (((𝟭 _).mapCochainComplexPlus.obj (rs R F)).obj.X n) :=
  (compactSupportCohomology_of_isCSoft R X).1.2 _ (injective_rs F n)

omit [LocallyCompactSpace X] [T2Space X] in
private lemma csoft_P (H : LesHyp R Z) (F : TopCat.Sheaf (ModuleCat.{0} R) X) (n : ℤ) :
    CSoft R (((PF R Z.compl).mapCochainComplexPlus.obj (rs R F)).obj.X n) :=
  haveI := injective_rs F n
  H.csoft ((rs R F).obj.X n)

private lemma csoft_T (H : LesHyp R Z) (F : TopCat.Sheaf (ModuleCat.{0} R) X) (n : ℤ) :
    CSoft R (((TF R Z).mapCochainComplexPlus.obj (rs R F)).obj.X n) :=
  haveI := injective_rs F n
  ((compactSupportCohomology_of_isCSoft R X).2.1 (seq H.ext ((rs R F).obj.X n))
    (shortExact_seq H.ext _) (H.csoft ((rs R F).obj.X n))).2
      ((compactSupportCohomology_of_isCSoft R X).1.2 _ (injective_rs F n))

/-- `0 ⟶ Γ_c(j_! j^* I) ⟶ Γ_c(I) ⟶ Γ_c(i_* i^{-1} I) ⟶ 0` for the chosen resolution `I`. -/
private noncomputable def sesΓ (H : LesHyp R Z) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℤ) :=
  ShortComplex.mk
    (((compactSupportSectionsFunctor R (X := X)).mapHomologicalComplex _).map
      (νI (adjF R Z.compl).counit (rs R F)).hom)
    (((compactSupportSectionsFunctor R (X := X)).mapHomologicalComplex _).map
      (νI (adjZ R Z).unit (rs R F)).hom) (by
      rw [← Functor.map_comp]
      have h0 : (νI (adjF R Z.compl).counit (rs R F)).hom ≫ (νI (adjZ R Z).unit (rs R F)).hom = 0 :=
        HomologicalComplex.hom_ext _ _ fun n => counit_comp_unit H.ext _
      rw [h0, Functor.map_zero])

private lemma shortExact_sesΓ (H : LesHyp R Z) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (sesΓ H F).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    haveI := injective_rs F n
    ((compactSupportCohomology_of_isCSoft R X).2.1 (seq H.ext ((rs R F).obj.X n))
      (shortExact_seq H.ext _) (H.csoft ((rs R F).obj.X n))).1

/-- `H^q_c(X, j_! j^* F) ≅ H^q(Γ_c(j_! j^* I))`. -/
private noncomputable def cP (H : LesHyp R Z) (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (HcF R X q).obj ((PF R Z.compl).obj F) ≅
      (Src R X q).obj ((PF R Z.compl).mapCochainComplexPlus.obj (rs R F)) :=
  haveI := preservesFiniteLimits_PF H
  haveI := preservesFiniteColimits_PF H
  haveI := quasiIso_eΦ (PF R Z.compl) (rε F)
  cmp q (eΦ (PF R Z.compl) (rε F)) (csoft_P H F)

/-- `H^q_c(X, F) ≅ H^q(Γ_c(I))`. -/
private noncomputable def cI (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (HcF R X q).obj ((𝟭 _).obj F) ≅ (Src R X q).obj ((𝟭 _).mapCochainComplexPlus.obj (rs R F)) :=
  haveI := quasiIso_eΦ (𝟭 (TopCat.Sheaf (ModuleCat.{0} R) X)) (rε F)
  cmp q (eΦ (𝟭 _) (rε F)) (csoft_id F)

/-- `H^q_c(X, i_* i^{-1} F) ≅ H^q(Γ_c(i_* i^{-1} I))`. -/
private noncomputable def cT (H : LesHyp R Z) (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (HcF R X q).obj ((TF R Z).obj F) ≅
      (Src R X q).obj ((TF R Z).mapCochainComplexPlus.obj (rs R F)) :=
  haveI := quasiIso_eΦ (TF R Z) (rε F)
  cmp q (eΦ (TF R Z) (rε F)) (csoft_T H F)

private lemma cP_comm (H : LesHyp R Z) (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (cP H q F).hom ≫ (Src R X q).map (νI (adjF R Z.compl).counit (rs R F)) =
      (HcF R X q).map ((adjF R Z.compl).counit.app F) ≫ (cI q F).hom := by
  have := preservesFiniteLimits_PF H
  have := preservesFiniteColimits_PF H
  have := quasiIso_eΦ (PF R Z.compl) (rε F)
  have := quasiIso_eΦ (𝟭 (TopCat.Sheaf (ModuleCat.{0} R) X)) (rε F)
  exact cmp_naturality q _ _ _ _ _ _ (by rw [eΦ_νI])

private lemma cI_comm (H : LesHyp R Z) (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (cI q F).hom ≫ (Src R X q).map (νI (adjZ R Z).unit (rs R F)) =
      (HcF R X q).map ((adjZ R Z).unit.app F) ≫ (cT H q F).hom := by
  have := quasiIso_eΦ (TF R Z) (rε F)
  have := quasiIso_eΦ (𝟭 (TopCat.Sheaf (ModuleCat.{0} R) X)) (rε F)
  exact cmp_naturality q _ _ _ _ _ _ (by rw [eΦ_νI])

/-- The connecting map of `sesΓ`, from `H^q(Γ_c(i_* i^{-1} I))` to `H^{q+1}(Γ_c(j_! j^* I))`. -/
private noncomputable def δΓ (H : LesHyp R Z) (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (Src R X q).obj ((TF R Z).mapCochainComplexPlus.obj (rs R F)) ⟶
      (Src R X (q + 1)).obj ((PF R Z.compl).mapCochainComplexPlus.obj (rs R F)) :=
  (shortExact_sesΓ H F).δ q (q + 1) rfl

/-- The connecting map `H^q_c(X, i_* i^{-1} F) ⟶ H^{q+1}_c(X, j_! j^* F)`. -/
private noncomputable def δF (H : LesHyp R Z) (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (TF R Z ⋙ HcF R X q).obj F ⟶ (PF R Z.compl ⋙ HcF R X (q + 1)).obj F :=
  (cT H q F).hom ≫ δΓ H q F ≫ (cP H (q + 1) F).inv

omit [LocallyCompactSpace X] [T2Space X] in
private lemma sesΓ_comm₁₂ (H : LesHyp R Z) {F F' : TopCat.Sheaf (ModuleCat.{0} R) X}
    (f : rs R F ⟶ rs R F') :
    ((compactSupportSectionsFunctor R (X := X)).mapHomologicalComplex _).map
        ((PF R Z.compl).mapCochainComplexPlus.map f).hom ≫ (sesΓ H F').f =
      (sesΓ H F).f ≫ ((compactSupportSectionsFunctor R (X := X)).mapHomologicalComplex _).map
        ((𝟭 _).mapCochainComplexPlus.map f).hom := by
  dsimp only [sesΓ]
  rw [← Functor.map_comp, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
    ← ObjectProperty.FullSubcategory.comp_hom, νI_naturality]

omit [LocallyCompactSpace X] [T2Space X] in
private lemma sesΓ_comm₂₃ (H : LesHyp R Z) {F F' : TopCat.Sheaf (ModuleCat.{0} R) X}
    (f : rs R F ⟶ rs R F') :
    ((compactSupportSectionsFunctor R (X := X)).mapHomologicalComplex _).map
        ((𝟭 _).mapCochainComplexPlus.map f).hom ≫ (sesΓ H F').g =
      (sesΓ H F).g ≫ ((compactSupportSectionsFunctor R (X := X)).mapHomologicalComplex _).map
        ((TF R Z).mapCochainComplexPlus.map f).hom := by
  dsimp only [sesΓ]
  rw [← Functor.map_comp, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
    ← ObjectProperty.FullSubcategory.comp_hom, νI_naturality]

private lemma δF_naturality (H : LesHyp R Z) (q : ℤ) {F F' : TopCat.Sheaf (ModuleCat.{0} R) X}
    (φ : F ⟶ F') :
    (TF R Z ⋙ HcF R X q).map φ ≫ δF H q F' = δF H q F ≫ (PF R Z.compl ⋙ HcF R X (q + 1)).map φ := by
  have := preservesFiniteLimits_PF H
  have := preservesFiniteColimits_PF H
  have := quasiIso_eΦ (PF R Z.compl) (rε F)
  have := quasiIso_eΦ (PF R Z.compl) (rε F')
  have := quasiIso_eΦ (TF R Z) (rε F)
  have := quasiIso_eΦ (TF R Z) (rε F')
  let f := rl φ
  let Γm := (compactSupportSectionsFunctor R (X := X)).mapHomologicalComplex (ComplexShape.up ℤ)
  let m : sesΓ H F ⟶ sesΓ H F' :=
    { τ₁ := Γm.map ((PF R Z.compl).mapCochainComplexPlus.map f).hom
      τ₂ := Γm.map ((𝟭 _).mapCochainComplexPlus.map f).hom
      τ₃ := Γm.map ((TF R Z).mapCochainComplexPlus.map f).hom
      comm₁₂ := sesΓ_comm₁₂ H f
      comm₂₃ := sesΓ_comm₂₃ H f }
  have hT : (cT H q F).hom ≫ (Src R X q).map ((TF R Z).mapCochainComplexPlus.map f) =
      (HcF R X q).map ((TF R Z).map φ) ≫ (cT H q F').hom :=
    cmp_naturality q _ _ _ _ _ _ (quotient_map_eΦ_lift _ φ _ _ _ (rl_spec φ))
  have hP : (cP H (q + 1) F).hom ≫
      (Src R X (q + 1)).map ((PF R Z.compl).mapCochainComplexPlus.map f) =
      (HcF R X (q + 1)).map ((PF R Z.compl).map φ) ≫ (cP H (q + 1) F').hom :=
    cmp_naturality (q + 1) _ _ _ _ _ _ (quotient_map_eΦ_lift _ φ _ _ _ (rl_spec φ))
  have hP' : (Src R X (q + 1)).map ((PF R Z.compl).mapCochainComplexPlus.map f) ≫
      (cP H (q + 1) F').inv =
        (cP H (q + 1) F).inv ≫ (HcF R X (q + 1)).map ((PF R Z.compl).map φ) := by
    rw [Iso.comp_inv_eq, Category.assoc, ← hP, Iso.inv_hom_id_assoc]
  have hδ' : (Src R X q).map ((TF R Z).mapCochainComplexPlus.map f) ≫ δΓ H q F' =
      δΓ H q F ≫ (Src R X (q + 1)).map ((PF R Z.compl).mapCochainComplexPlus.map f) :=
    (HomologicalComplex.HomologySequence.δ_naturality m (shortExact_sesΓ H F)
      (shortExact_sesΓ H F') q (q + 1) rfl).symm
  change (HcF R X q).map ((TF R Z).map φ) ≫ δF H q F' =
    δF H q F ≫ (HcF R X (q + 1)).map ((PF R Z.compl).map φ)
  simp only [δF, Category.assoc]
  rw [← Category.assoc, ← hT, Category.assoc, ← Category.assoc _ (δΓ H q F'), hδ',
    Category.assoc, hP']

/-- The connecting maps, as a natural transformation. -/
private noncomputable def δN (H : LesHyp R Z) (q : ℤ) :
    TF R Z ⋙ HcF R X q ⟶ PF R Z.compl ⋙ HcF R X (q + 1) where
  app := δF H q
  naturality _ _ φ := δF_naturality H q φ

end LES

/-! ### Exactness transported along isomorphisms -/

private lemma range_eq_ker_of_iso {A B C : ModuleCat.{0} R} (f : A ⟶ B) (g : B ⟶ C)
    (S' : ShortComplex (ModuleCat.{0} R)) (hS' : S'.Exact) (e₁ : A ≅ S'.X₁) (e₂ : B ≅ S'.X₂)
    (e₃ : C ≅ S'.X₃) (h₁ : f ≫ e₂.hom = e₁.hom ≫ S'.f) (h₂ : g ≫ e₃.hom = e₂.hom ≫ S'.g) :
    LinearMap.range f.hom = LinearMap.ker g.hom := by
  have hz : f ≫ g = 0 := by
    have : (f ≫ g) ≫ e₃.hom = 0 ≫ e₃.hom := by
      rw [Category.assoc, h₂, reassoc_of% h₁, S'.zero, comp_zero, zero_comp]
    exact (cancel_mono e₃.hom).mp this
  have hS : (ShortComplex.mk f g hz).Exact :=
    (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁.symm h₂.symm)).mpr hS'
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hS

/-! ### Compact spaces -/

section Compact

variable (R) (X : TopCat.{0}) [CompactSpace X]

private lemma compactSupportSections_eq_top (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    compactSupportSections R F = ⊤ :=
  eq_top_iff.mpr fun _ _ => ⟨Set.univ, isCompact_univ, fun _ hx => (hx trivial).elim⟩

/-- `Γ_c = Γ` on a compact space. -/
private noncomputable def gammaTopIso :
    compactSupportSectionsFunctor R (X := X) ≅
      ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} R)).obj (op ⊤) :
        TopCat.Sheaf (ModuleCat.{0} R) X ⥤ ModuleCat.{0} R) :=
  NatIso.ofComponents
    (fun F => (LinearEquiv.ofTop _ (compactSupportSections_eq_top R X F)).toModuleIso)
    (fun _ => rfl)

/-- Isomorphic additive functors have isomorphic derived functors. -/
private lemma exists_derived_iso {X : TopCat.{0}} (q : ℤ)
    (Γ₀ : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ ModuleCat.{0} R) [Γ₀.Additive]
    (e : compactSupportSectionsFunctor R (X := X) ≅ Γ₀) :
    Nonempty (HcF R X q ≅ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        Γ₀.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor _ q) := by
  let Γc := compactSupportSectionsFunctor R (X := X)
  let τ : Γc.mapHomotopyCategoryPlus ≅ Γ₀.mapHomotopyCategoryPlus :=
    (Functor.mapHomotopyCategoryPlusCompIso (Functor.leftUnitor Γc)).symm ≪≫
      Functor.mapHomotopyCategoryPlusCompIso (Functor.leftUnitor Γc ≪≫ e)
  let e' : Γc.rightDerivedFunctorPlus ≅ Γ₀.rightDerivedFunctorPlus :=
    Functor.rightDerivedNatIso _ _ Γc.rightDerivedFunctorPlusUnith Γ₀.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso _) (Functor.isoWhiskerRight τ DerivedCategory.Plus.Qh)
  exact ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight e' _)⟩

end Compact

/-- Exactness of
`H^q_c(U, F) ⟶ H^q_c(X, F) ⟶ H^q_c(Z, i^{-1} F) ⟶ H^{q+1}_c(U, F) ⟶ H^{q+1}_c(X, F)`,
for any comparison isomorphisms `ι` and `κ`. -/
private lemma les_exact {X : TopCat.{0}} [LocallyCompactSpace X] [T2Space X] {Z : Closeds X}
    (H : LesHyp R Z)
    (ι : ∀ q, HcF R ((Opens.toTopCat X).obj Z.compl) q ≅ extF R Z.compl ⋙ HcF R X q)
    (κ : ∀ q, pushF R Z ⋙ HcF R X q ≅ HcF R (TopCat.of Z) q) (q : ℤ)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    let a := fun q => (ι q).hom.app ((resF R Z.compl).obj F) ≫
      (HcF R X q).map ((adjF R Z.compl).counit.app F)
    let b := (HcF R X q).map ((adjZ R Z).unit.app F) ≫ (κ q).hom.app ((pullF R Z).obj F)
    let d := (κ q).inv.app ((pullF R Z).obj F) ≫ δF H q F ≫
      (ι (q + 1)).inv.app ((resF R Z.compl).obj F)
    LinearMap.range (a q).hom = LinearMap.ker b.hom ∧
      LinearMap.range b.hom = LinearMap.ker d.hom ∧
      LinearMap.range d.hom = LinearMap.ker (a (q + 1)).hom := by
  intro a b d
  have hS := shortExact_sesΓ H F
  have ha : ∀ q, a q ≫ (cI q F).hom = ((ι q).app _ ≪≫ cP H q F).hom ≫
      (Src R X q).map (νI (adjF R Z.compl).counit (rs R F)) := by
    intro q
    simp only [a, Iso.trans_hom, Iso.app_hom, Category.assoc, cP_comm]
  have hb : b ≫ (((κ q).app _).symm ≪≫ cT H q F).hom =
      (cI q F).hom ≫ (Src R X q).map (νI (adjZ R Z).unit (rs R F)) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc,
      Iso.hom_inv_id_app_assoc]
    exact (cI_comm H q F).symm
  have hd : d ≫ ((ι (q + 1)).app _ ≪≫ cP H (q + 1) F).hom =
      (((κ q).app _).symm ≪≫ cT H q F).hom ≫ δΓ H q F := by
    simp only [d, δF, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id, Category.comp_id]
  exact ⟨range_eq_ker_of_iso _ _ _ (hS.homology_exact₂ q) _ _ _ (ha q) hb,
    range_eq_ker_of_iso _ _ _ (hS.homology_exact₃ q (q + 1) rfl) _ _ _ hb hd,
    range_eq_ker_of_iso _ _ _ (hS.homology_exact₁ q (q + 1) rfl) _ _ _ hd (ha (q + 1))⟩

end ClosedComplement

open ClosedComplement in
/-- Let `X` be locally compact Hausdorff, `Z ⊆ X` closed with inclusion `i`, and `U = X \ Z`
with restriction `res = j^*`, extension by zero `ext = j_!` and `adj : j_! ⊣ j^*`. Write
`Hc Y q` for the functor `F ↦ MMP.Fourfold.compactSupportCohomology R q F` on sheaves on `Y`.
There are natural maps `a q : H^q_c(U, j^* F) ⟶ H^q_c(X, F)`, induced through a natural
isomorphism `H^q_c(U, -) ≅ H^q_c(X, j_! -)` by the counit `j_! j^* F ⟶ F`,
`b q : H^q_c(X, F) ⟶ H^q_c(Z, i^{-1} F)`, induced through a natural isomorphism
`H^q_c(X, i_* -) ≅ H^q_c(Z, -)` by the unit `F ⟶ i_* i^{-1} F`, and
`δ q : H^q_c(Z, i^{-1} F) ⟶ H^{q+1}_c(U, j^* F)`, forming a long exact sequence. If moreover
`X` is compact, every global section of `F` has compact support, and `H^q_c(X, F) ≅ H^q(X, F)`
naturally in `F`. -/
@[mmp "lem_mmp_compact_support_closed_complement"]
public theorem compactSupportCohomology_closedComplement
    (R : Type) [CommRing R] (X : TopCat.{0}) [LocallyCompactSpace X] [T2Space X] (Z : Closeds X) :
    let U : Opens X := Z.compl
    let ZT : TopCat.{0} := TopCat.of Z
    let i : ZT ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let UT : TopCat.{0} := (Opens.toTopCat X).obj U
    let res : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) UT :=
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _
    let ext : TopCat.Sheaf (ModuleCat.{0} R) UT ⥤ TopCat.Sheaf (ModuleCat.{0} R) X :=
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafPullback _ _ _
    let adj : ext ⊣ res :=
      haveI := U.isOpenEmbedding.functor_isContinuous
      U.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _
    let Hc : ∀ (Y : TopCat.{0}) (_ : ℤ), TopCat.Sheaf (ModuleCat.{0} R) Y ⥤ ModuleCat.{0} R :=
      fun Y q => DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (compactSupportSectionsFunctor R (X := Y)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q
    let H : ℤ → TopCat.Sheaf (ModuleCat.{0} R) X ⥤ ModuleCat.{0} R :=
      fun q => DerivedCategory.Plus.singleFunctor _ 0 ⋙
        ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} R)).obj
          (op ⊤)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q
    (∃ (ι : ∀ q : ℤ, Hc UT q ≅ ext ⋙ Hc X q)
      (κ : ∀ q : ℤ, TopCat.Sheaf.pushforward (ModuleCat.{0} R) i ⋙ Hc X q ≅ Hc ZT q)
      (a : ∀ q : ℤ, res ⋙ Hc UT q ⟶ Hc X q)
      (b : ∀ q : ℤ, Hc X q ⟶ TopCat.Sheaf.pullback (ModuleCat.{0} R) i ⋙ Hc ZT q)
      (δ : ∀ q : ℤ, TopCat.Sheaf.pullback (ModuleCat.{0} R) i ⋙ Hc ZT q ⟶
        res ⋙ Hc UT (q + 1)),
      (∀ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X),
        (a q).app F = (ι q).hom.app (res.obj F) ≫ (Hc X q).map (adj.counit.app F)) ∧
      (∀ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X),
        (b q).app F = (Hc X q).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} R) i).unit.app F) ≫
          (κ q).hom.app ((TopCat.Sheaf.pullback (ModuleCat.{0} R) i).obj F)) ∧
      ∀ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X),
        LinearMap.range ((a q).app F).hom = LinearMap.ker ((b q).app F).hom ∧
        LinearMap.range ((b q).app F).hom = LinearMap.ker ((δ q).app F).hom ∧
        LinearMap.range ((δ q).app F).hom = LinearMap.ker ((a (q + 1)).app F).hom) ∧
    (CompactSpace X →
      (∀ F : TopCat.Sheaf (ModuleCat.{0} R) X, compactSupportSections R F = ⊤) ∧
      ∀ q : ℤ, Nonempty (Hc X q ≅ H q)) := by
  intro U ZT i UT res ext adj Hc H
  obtain ⟨hU, -, ι', -, -, -, -⟩ := compactSupportCohomology_extendByZero R X
  obtain ⟨hex, hunit, -, hzero, hcs, -⟩ := hU U
  have : LocallyCompactSpace UT := U.isOpen.locallyCompactSpace
  have : T2Space UT := inferInstanceAs (T2Space (U : Set X))
  have hcsP : ∀ (J : TopCat.Sheaf (ModuleCat.{0} R) X) [Injective J],
      CSoft R ((PF R Z.compl).obj J) := by
    intro J _
    have : PreservesFiniteLimits (extF R Z.compl) := hex.1
    have : Injective ((resF R Z.compl).obj J) := Injective.injective_of_adjoint (adjF R Z.compl) J
    have h1 := (compactSupportCohomology_of_isCSoft R UT).1.2 ((resF R Z.compl).obj J)
      inferInstance
    have h2 := hcs ((resF R Z.compl).obj J) (fun K hK W hKW s => by
      obtain ⟨t, V, hKV, hVW, e⟩ := h1 K hK W hKW s
      exact ⟨t, V, hVW, hKV, e.symm⟩)
    intro K hK W hKW s
    obtain ⟨t, V, hVW, hKV, e⟩ := h2 K hK W hKW s
    exact ⟨t, V, hKV, hVW, e.symm⟩
  let H' : LesHyp R Z := ⟨⟨hunit, hzero⟩, hcsP⟩
  let κ := fun q => (exists_κ R Z q).some
  refine ⟨⟨fun q => ι' U q, κ,
    fun q => Functor.whiskerLeft res (ι' U q).hom ≫ Functor.whiskerRight adj.counit (Hc X q),
    fun q => Functor.whiskerRight (adjZ R Z).unit (Hc X q) ≫
      Functor.whiskerLeft (pullF R Z) (κ q).hom,
    fun q => Functor.whiskerLeft (pullF R Z) (κ q).inv ≫ δN H' q ≫
      Functor.whiskerLeft res (ι' U (q + 1)).inv,
    fun q F => rfl, fun q F => rfl, fun q F => les_exact H' (fun q => ι' U q) κ q F⟩,
    fun hc => ?_⟩
  refine ⟨compactSupportSections_eq_top R X, fun q => ?_⟩
  exact @exists_derived_iso R _ X q
    ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} R)).obj (op ⊤))
    (Stacks.Adequate.sheafSections_obj_additive _ _) (gammaTopIso R X)

/-! ### The Mayer–Vietoris sequence -/

namespace MayerVietoris

open Pretriangulated ZeroObject

/-! ### Split exactness of the Mayer–Vietoris short complex after an additive functor -/

section Split

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasZeroObject D] (G : C ⥤ D) [G.Additive]
  {A B B' E : C} (u : A ⟶ B) (v : A ⟶ B') (a : B ⟶ E) (b : B' ⟶ E) (c : A ⟶ E)
  (hu : u ≫ a = c) (hv : v ≫ b = c)

/-- The short complex `A --(u, -v)--> B ⊞ B' --a + b--> E`. -/
private noncomputable abbrev mvSC : ShortComplex C :=
  ShortComplex.mk (biprod.lift u (-v)) (biprod.desc a b) (by simp [hu, hv])

include hu hv in
private lemma shortExact_map_mvSC_of_isIso [IsIso (G.map a)] [IsIso (G.map b)]
    [IsIso (G.map c)] : ((mvSC u v a b c hu hv).map G).ShortExact := by
  have hu' : G.map u ≫ G.map a = G.map c := by rw [← G.map_comp, hu]
  have hv' : G.map v ≫ G.map b = G.map c := by rw [← G.map_comp, hv]
  have : IsIso (G.map u) := by
    have : IsIso (G.map u ≫ G.map a) := by
      rw [hu']
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map a)
  have : IsIso (G.map v) := by
    have : IsIso (G.map v ≫ G.map b) := by
      rw [hv']
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map b)
  have ha : G.map a ≫ inv (G.map c) = inv (G.map u) :=
    IsIso.eq_inv_of_hom_inv_id (by rw [← Category.assoc, hu', IsIso.hom_inv_id])
  have hb' : G.map b ≫ inv (G.map c) = inv (G.map v) :=
    IsIso.eq_inv_of_hom_inv_id (by rw [← Category.assoc, hv', IsIso.hom_inv_id])
  have hb : G.map b ≫ inv (G.map c) ≫ G.map v = 𝟙 _ := by
    rw [← Category.assoc, hb', IsIso.inv_hom_id]
  have f_r : G.map (biprod.lift u (-v)) ≫ G.map biprod.fst ≫ inv (G.map u) = 𝟙 _ := by
    rw [← Category.assoc, ← G.map_comp, biprod.lift_fst, IsIso.hom_inv_id]
  have s_g : (inv (G.map c) ≫ G.map v ≫ G.map biprod.inr) ≫ G.map (biprod.desc a b) = 𝟙 _ := by
    rw [Category.assoc, Category.assoc, ← G.map_comp, biprod.inr_desc, hv', IsIso.inv_hom_id]
  have id : (G.map biprod.fst ≫ inv (G.map u)) ≫ G.map (biprod.lift u (-v)) +
      G.map (biprod.desc a b) ≫ inv (G.map c) ≫ G.map v ≫ G.map biprod.inr = 𝟙 _ := by
    rw [biprod.lift_eq, biprod.desc_eq, ← G.map_id, ← biprod.total]
    simp only [G.map_add, G.map_comp, G.map_neg, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
    rw [reassoc_of% ha, reassoc_of% hb, IsIso.inv_hom_id_assoc]
    abel
  exact ShortComplex.Splitting.shortExact
    { r := G.map biprod.fst ≫ inv (G.map u)
      s := inv (G.map c) ≫ G.map v ≫ G.map biprod.inr
      f_r := f_r
      s_g := s_g
      id := id }

include hu hv in
private lemma shortExact_map_mvSC_of_isZero_left (hA : IsZero (G.obj A)) (hB' : IsZero (G.obj B'))
    [IsIso (G.map a)] : ((mvSC u v a b c hu hv).map G).ShortExact := by
  have s_g : (inv (G.map a) ≫ G.map biprod.inl) ≫ G.map (biprod.desc a b) = 𝟙 _ := by
    rw [Category.assoc, ← G.map_comp, biprod.inl_desc, IsIso.inv_hom_id]
  have id : (0 : G.obj (B ⊞ B') ⟶ G.obj A) ≫ G.map (biprod.lift u (-v)) +
      G.map (biprod.desc a b) ≫ inv (G.map a) ≫ G.map biprod.inl = 𝟙 _ := by
    rw [biprod.desc_eq, ← G.map_id, ← biprod.total]
    simp only [G.map_add, G.map_comp, Preadditive.add_comp, Category.assoc, zero_comp, zero_add,
      IsIso.hom_inv_id_assoc]
    rw [hB'.eq_of_src (G.map b ≫ _) 0, hB'.eq_of_src (G.map biprod.inr) 0]
  exact ShortComplex.Splitting.shortExact
    { r := 0
      s := inv (G.map a) ≫ G.map biprod.inl
      f_r := hA.eq_of_src _ _
      s_g := s_g
      id := id }

include hu hv in
private lemma shortExact_map_mvSC_of_isZero_right (hA : IsZero (G.obj A)) (hB : IsZero (G.obj B))
    [IsIso (G.map b)] : ((mvSC u v a b c hu hv).map G).ShortExact := by
  have s_g : (inv (G.map b) ≫ G.map biprod.inr) ≫ G.map (biprod.desc a b) = 𝟙 _ := by
    rw [Category.assoc, ← G.map_comp, biprod.inr_desc, IsIso.inv_hom_id]
  have id : (0 : G.obj (B ⊞ B') ⟶ G.obj A) ≫ G.map (biprod.lift u (-v)) +
      G.map (biprod.desc a b) ≫ inv (G.map b) ≫ G.map biprod.inr = 𝟙 _ := by
    rw [biprod.desc_eq, ← G.map_id, ← biprod.total]
    simp only [G.map_add, G.map_comp, Preadditive.add_comp, Category.assoc, zero_comp, zero_add,
      IsIso.hom_inv_id_assoc]
    rw [hB.eq_of_src (G.map a ≫ _) 0, hB.eq_of_src (G.map biprod.inl) 0]
  exact ShortComplex.Splitting.shortExact
    { r := 0
      s := inv (G.map b) ≫ G.map biprod.inr
      f_r := hA.eq_of_src _ _
      s_g := s_g
      id := id }

end Split

/-! ### Short exactness of sheaves on stalks -/

section Stalks

variable {R : Type} [CommRing R] {Y : TopCat.{0}}

/-- A short complex of sheaves whose stalk complexes are all short exact is short exact. -/
private lemma shortExact_of_stalks (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) Y))
    (h : ∀ x : Y, (S.map (TopCat.Sheaf.forget (ModuleCat.{0} R) Y ⋙
      TopCat.Presheaf.stalkFunctor _ x)).ShortExact) : S.ShortExact := by
  have := (TopCat.Presheaf.mono_iff_stalk_mono S.f).2 fun x => (h x).mono_f
  have : Epi S.g := (ShortComplex.exact_iff_epi (ShortComplex.mk S.g (0 : S.X₃ ⟶ 0) comp_zero)
    rfl).1 <| (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2 fun x =>
      (ShortComplex.exact_iff_epi _ (by simp; rfl)).2 (h x).epi_g
  exact ⟨(TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).2 fun x => (h x).exact⟩

end Stalks

variable (R : Type) [CommRing R] {X : TopCat.{0}} (U : Opens X)

/-! ### The Mayer–Vietoris short exact sequence of sheaves -/

section ShortExact

variable {R}

/-- A morphism `j_{W'!}(F|_{W'}) ⟶ j_{W!}(F|_W)` over `F`, chosen for every `F`, is natural in
`F`, since the counit of `j_{W!} ⊣ j_W^*` is a monomorphism. -/
private lemma comp_extF_map_eq {W W' : Opens X}
    (hu : ∀ G, IsIso ((adjF R W).unit.app G))
    (hz : ∀ G, ∀ x ∉ W, IsZero (((extF R W).obj G).presheaf.stalk x))
    (m : ∀ F, (extF R W').obj ((resF R W').obj F) ⟶ (extF R W).obj ((resF R W).obj F))
    (hm : ∀ F, m F ≫ (adjF R W).counit.app F = (adjF R W').counit.app F)
    {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ G) :
    m F ≫ (extF R W).map ((resF R W).map φ) = (extF R W').map ((resF R W').map φ) ≫ m G := by
  have := mono_counit hu hz G
  have h₁ : (extF R W).map ((resF R W).map φ) ≫ (adjF R W).counit.app G =
      (adjF R W).counit.app F ≫ φ := (adjF R W).counit_naturality φ
  have h₂ : (extF R W').map ((resF R W').map φ) ≫ (adjF R W').counit.app G =
      (adjF R W').counit.app F ≫ φ := (adjF R W').counit_naturality φ
  rw [← cancel_mono ((adjF R W).counit.app G), Category.assoc, Category.assoc, h₁, hm G,
    reassoc_of% (hm F), h₂]

variable {U} (V : Opens X)
  (mU : ∀ F, (extF R (U ⊓ V)).obj ((resF R (U ⊓ V)).obj F) ⟶ (extF R U).obj ((resF R U).obj F))
  (hmU : ∀ F, mU F ≫ (adjF R U).counit.app F = (adjF R (U ⊓ V)).counit.app F)
  (mV : ∀ F, (extF R (U ⊓ V)).obj ((resF R (U ⊓ V)).obj F) ⟶ (extF R V).obj ((resF R V).obj F))
  (hmV : ∀ F, mV F ≫ (adjF R V).counit.app F = (adjF R (U ⊓ V)).counit.app F)

/-- The Mayer–Vietoris short complex `j_{U∩V!}F → j_{U!}F ⊞ j_{V!}F → F`. -/
private noncomputable abbrev mvShortComplex (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X) :=
  mvSC (mU F) (mV F) ((adjF R U).counit.app F) ((adjF R V).counit.app F)
    ((adjF R (U ⊓ V)).counit.app F) (hmU F) (hmV F)

private lemma mvShortComplex_shortExact
    (hu : ∀ W : Opens X, ∀ G, IsIso ((adjF R W).unit.app G))
    (hz : ∀ W : Opens X, ∀ G, ∀ x ∉ W, IsZero (((extF R W).obj G).presheaf.stalk x))
    (hUV : U ⊔ V = ⊤) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (mvShortComplex V mU hmU mV hmV F).ShortExact := by
  refine shortExact_of_stalks _ fun x => ?_
  by_cases hxU : x ∈ U
  · by_cases hxV : x ∈ V
    · have := isIso_stalk_counit (hu U) F ⟨x, hxU⟩
      have := isIso_stalk_counit (hu V) F ⟨x, hxV⟩
      have := isIso_stalk_counit (hu (U ⊓ V)) F ⟨x, hxU, hxV⟩
      exact shortExact_map_mvSC_of_isIso _ _ _ _ _ _ _ _
    · have := isIso_stalk_counit (hu U) F ⟨x, hxU⟩
      exact shortExact_map_mvSC_of_isZero_left _ _ _ _ _ _ _ _
        (hz (U ⊓ V) _ x fun h => hxV h.2) (hz V _ x hxV)
  · have hxV : x ∈ V := ((hUV ▸ trivial : x ∈ U ⊔ V)).resolve_left hxU
    have := isIso_stalk_counit (hu V) F ⟨x, hxV⟩
    exact shortExact_map_mvSC_of_isZero_right _ _ _ _ _ _ _ _
      (hz (U ⊓ V) _ x fun h => hxU h.1) (hz U _ x hxU)

/-- The morphism of Mayer–Vietoris short complexes induced by a morphism of sheaves. -/
private noncomputable def mvShortComplexMap
    (hu : ∀ W : Opens X, ∀ G, IsIso ((adjF R W).unit.app G))
    (hz : ∀ W : Opens X, ∀ G, ∀ x ∉ W, IsZero (((extF R W).obj G).presheaf.stalk x))
    {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ G) :
    mvShortComplex V mU hmU mV hmV F ⟶ mvShortComplex V mU hmU mV hmV G where
  τ₁ := (extF R (U ⊓ V)).map ((resF R (U ⊓ V)).map φ)
  τ₂ := biprod.map ((extF R U).map ((resF R U).map φ)) ((extF R V).map ((resF R V).map φ))
  τ₃ := φ
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst, biprod.lift_fst_assoc]
      exact (comp_extF_map_eq (hu U) (hz U) mU hmU φ).symm
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd, biprod.lift_snd_assoc,
        Preadditive.neg_comp, Preadditive.comp_neg]
      rw [comp_extF_map_eq (hu V) (hz V) mV hmV φ]
  comm₂₃ := by
    apply biprod.hom_ext' <;> simp [Adjunction.counit_naturality]

end ShortExact

/-! ### Exactness transported along isomorphisms -/

private lemma exact_of_ladder {A₁ A₂ A₃ B₁ B₂ B₃ : ModuleCat.{0} R} {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃}
    {f' : B₁ ⟶ B₂} {g' : B₂ ⟶ B₃} (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (e₃ : A₃ ≅ B₃)
    (h₁ : f ≫ e₂.hom = e₁.hom ≫ f') (h₂ : g ≫ e₃.hom = e₂.hom ≫ g')
    (H : Function.Exact f'.hom g'.hom) : Function.Exact f.hom g.hom := by
  have k₁ : e₁.inv ≫ f = f' ≫ e₂.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h₁]
  have k₂ : e₂.inv ≫ g = g' ≫ e₃.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h₂]
  exact Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := e₁.symm.toLinearEquiv)
    (e₂ := e₂.symm.toLinearEquiv) (e₃ := e₃.symm.toLinearEquiv)
    (LinearMap.ext fun x => ConcreteCategory.congr_hom k₁ x)
    (LinearMap.ext fun x => ConcreteCategory.congr_hom k₂ x) H

/-! ### The long exact sequence -/

section Derived

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  Functor.isTriangulated_rightDerivedFunctorPlus

variable {R} [LocallyCompactSpace X] [T2Space X] {U} (V : Opens X)
  (mU : ∀ F, (extF R (U ⊓ V)).obj ((resF R (U ⊓ V)).obj F) ⟶ (extF R U).obj ((resF R U).obj F))
  (hmU : ∀ F, mU F ≫ (adjF R U).counit.app F = (adjF R (U ⊓ V)).counit.app F)
  (mV : ∀ F, (extF R (U ⊓ V)).obj ((resF R (U ⊓ V)).obj F) ⟶ (extF R V).obj ((resF R V).obj F))
  (hmV : ∀ F, mV F ≫ (adjF R V).counit.app F = (adjF R (U ⊓ V)).counit.app F)
  (hu : ∀ W : Opens X, ∀ G, IsIso ((adjF R W).unit.app G))
  (hz : ∀ W : Opens X, ∀ G, ∀ x ∉ W, IsZero (((extF R W).obj G).presheaf.stalk x))
  (hUV : U ⊔ V = ⊤)

/-- `F ↦ RΓ_c(X, F[0])`, a `δ`-functor. -/
private noncomputable abbrev RΓ : TopCat.Sheaf (ModuleCat.{0} R) X ⥤
    DerivedCategory.Plus (ModuleCat.{0} R) :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (compactSupportSectionsFunctor R (X := X)).rightDerivedFunctorPlus

/-- The distinguished triangle of `RΓ_c(X, -)` attached to the Mayer–Vietoris sequence. -/
private noncomputable abbrev mvTriangle (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Triangle (DerivedCategory.Plus (ModuleCat.{0} R)) :=
  Triangle.mk ((RΓ (R := R) (X := X)).map (mvShortComplex V mU hmU mV hmV F).f)
    ((RΓ (R := R) (X := X)).map (mvShortComplex V mU hmU mV hmV F).g)
    ((Stacks.DerivedIndexing.derivedDeltaFunctorStructure
      (compactSupportSectionsFunctor R (X := X))).δ
      (mvShortComplex_shortExact V mU hmU mV hmV hu hz hUV F))

omit [LocallyCompactSpace X] [T2Space X] in
include hUV in
private lemma mvTriangle_distinguished (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    mvTriangle V mU hmU mV hmV hu hz hUV F ∈ distTriang _ :=
  (Stacks.DerivedIndexing.derivedDeltaFunctorStructure
    (compactSupportSectionsFunctor R (X := X))).distinguished _

/-- The morphism of Mayer–Vietoris triangles induced by a morphism of sheaves. -/
private noncomputable def mvTriangleMap {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ G) :
    mvTriangle V mU hmU mV hmV hu hz hUV F ⟶ mvTriangle V mU hmU mV hmV hu hz hUV G :=
  Triangle.homMk _ _ ((RΓ (R := R) (X := X)).map (mvShortComplexMap V mU hmU mV hmV hu hz φ).τ₁)
    ((RΓ (R := R) (X := X)).map (mvShortComplexMap V mU hmU mV hmV hu hz φ).τ₂)
    ((RΓ (R := R) (X := X)).map φ)
    (by
      dsimp only [Triangle.mk_mor₁]
      rw [← Functor.map_comp, ← Functor.map_comp,
        (mvShortComplexMap V mU hmU mV hmV hu hz φ).comm₁₂])
    (by
      dsimp only [Triangle.mk_mor₂]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ (mvShortComplexMap V mU hmU mV hmV hu hz φ).comm₂₃.symm)
    ((Stacks.DerivedIndexing.derivedDeltaFunctorStructure
      (compactSupportSectionsFunctor R (X := X))).δ_naturality _ _
      (mvShortComplexMap V mU hmU mV hmV hu hz φ))

/-- The connecting morphism `H^q_c(X, F) ⟶ H^{q+1}_c(X, j_{U∩V!}F)`. -/
private noncomputable abbrev mvδ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (HcF R X q).obj F ⟶ (HcF R X (q + 1)).obj ((extF R (U ⊓ V)).obj ((resF R (U ⊓ V)).obj F)) :=
  (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
    (mvTriangle V mU hmU mV hmV hu hz hUV F) q (q + 1) rfl

omit [LocallyCompactSpace X] [T2Space X] in
private lemma mvδ_naturality (q : ℤ) {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (φ : F ⟶ G) :
    (HcF R X q).map φ ≫ mvδ V mU hmU mV hmV hu hz hUV q G =
      mvδ V mU hmU mV hmV hu hz hUV q F ≫
        (HcF R X (q + 1)).map ((extF R (U ⊓ V)).map ((resF R (U ⊓ V)).map φ)) :=
  (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ_naturality
    (mvTriangleMap V mU hmU mV hmV hu hz hUV φ) q (q + 1) rfl

omit [LocallyCompactSpace X] [T2Space X] in
include hu hz hUV in
private lemma exact₂ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Function.Exact ((HcF R X q).map (mvShortComplex V mU hmU mV hmV F).f).hom
      ((HcF R X q).map (mvShortComplex V mU hmU mV hmV F).g).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₂ _
      (mvTriangle_distinguished V mU hmU mV hmV hu hz hUV F) q)

omit [LocallyCompactSpace X] [T2Space X] in
private lemma exact₃ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Function.Exact ((HcF R X q).map (mvShortComplex V mU hmU mV hmV F).g).hom
      (mvδ V mU hmU mV hmV hu hz hUV q F).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₃ _
      (mvTriangle_distinguished V mU hmU mV hmV hu hz hUV F) q (q + 1) rfl)

omit [LocallyCompactSpace X] [T2Space X] in
private lemma exact₁ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Function.Exact (mvδ V mU hmU mV hmV hu hz hUV q F).hom
      ((HcF R X (q + 1)).map (mvShortComplex V mU hmU mV hmV F).f).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₁ _
      (mvTriangle_distinguished V mU hmU mV hmV hu hz hUV F) q (q + 1) rfl)

private lemma additive_HcF (Y : TopCat.{0}) (q : ℤ) : (HcF R Y q).Additive := by
  dsimp only [HcF]
  infer_instance

attribute [local instance] additive_HcF

private lemma preservesBinaryBiproducts_HcF (Y : TopCat.{0}) (q : ℤ) :
    PreservesBinaryBiproducts (HcF R Y q) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

attribute [local instance] preservesBinaryBiproducts_HcF

section Comparison

variable (ι : ∀ (W : Opens X) (q : ℤ), HcF R ((Opens.toTopCat X).obj W) q ≅ extF R W ⋙ HcF R X q)

/-- The map `H^q_c(W, F) ⟶ H^q_c(X, F)` through `ι` and the counit. -/
private noncomputable abbrev eXF (W : Opens X) (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (HcF R ((Opens.toTopCat X).obj W) q).obj ((resF R W).obj F) ⟶ (HcF R X q).obj F :=
  (ι W q).hom.app ((resF R W).obj F) ≫ (HcF R X q).map ((adjF R W).counit.app F)

/-- `H^q_c(U, F) ⊞ H^q_c(V, F) ≅ H^q_c(X, j_{U!}F ⊞ j_{V!}F)`. -/
private noncomputable def biprodIso (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (HcF R ((Opens.toTopCat X).obj U) q).obj ((resF R U).obj F) ⊞
        (HcF R ((Opens.toTopCat X).obj V) q).obj ((resF R V).obj F) ≅
      (HcF R X q).obj ((extF R U).obj ((resF R U).obj F) ⊞ (extF R V).obj ((resF R V).obj F)) :=
  biprod.mapIso ((ι U q).app _) ((ι V q).app _) ≪≫
    ((HcF R X q).mapBiprod ((extF R U).obj ((resF R U).obj F))
      ((extF R V).obj ((resF R V).obj F))).symm

omit [LocallyCompactSpace X] [T2Space X] in
private lemma biprodIso_hom_mapBiprod (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (biprodIso V ι q F).hom ≫ ((HcF R X q).mapBiprod ((extF R U).obj ((resF R U).obj F))
    ((extF R V).obj ((resF R V).obj F))).hom =
      biprod.map ((ι U q).hom.app _) ((ι V q).hom.app _) := by
  simp only [biprodIso, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.app_hom]

omit [LocallyCompactSpace X] [T2Space X] in
private lemma sq₁ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X)
    (eU : (resF R (U ⊓ V) ⋙ HcF R ((Opens.toTopCat X).obj (U ⊓ V)) q).obj F ⟶
      (resF R U ⋙ HcF R ((Opens.toTopCat X).obj U) q).obj F)
    (eV : (resF R (U ⊓ V) ⋙ HcF R ((Opens.toTopCat X).obj (U ⊓ V)) q).obj F ⟶
      (resF R V ⋙ HcF R ((Opens.toTopCat X).obj V) q).obj F)
    (heU : eU = (ι (U ⊓ V) q).hom.app _ ≫ (HcF R X q).map (mU F) ≫ (ι U q).inv.app _)
    (heV : eV = (ι (U ⊓ V) q).hom.app _ ≫ (HcF R X q).map (mV F) ≫ (ι V q).inv.app _) :
    biprod.lift eU (-eV) ≫ (biprodIso V ι q F).hom =
      (ι (U ⊓ V) q).hom.app _ ≫ (HcF R X q).map (mvShortComplex V mU hmU mV hmV F).f := by
  rw [← cancel_mono ((HcF R X q).mapBiprod ((extF R U).obj ((resF R U).obj F))
    ((extF R V).obj ((resF R V).obj F))).hom, Category.assoc, biprodIso_hom_mapBiprod,
    Functor.mapBiprod_hom]
  subst heU heV
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_map, biprod.lift_fst, ← Functor.map_comp]
    simp
  · simp only [Category.assoc, biprod.lift_map, biprod.lift_snd, ← Functor.map_comp]
    simp

omit [LocallyCompactSpace X] [T2Space X] in
private lemma sq₂ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    biprod.desc (eXF ι U q F) (eXF ι V q F) ≫ (Iso.refl _).hom =
      (biprodIso V ι q F).hom ≫ (HcF R X q).map (mvShortComplex V mU hmU mV hmV F).g := by
  apply biprod.hom_ext'
  · simp only [biprodIso, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Category.assoc,
      biprod.inl_map_assoc, Functor.mapBiprod_inv, biprod.inl_desc_assoc, ← Functor.map_comp,
      biprod.inl_desc, Iso.refl_hom, Category.comp_id, eXF, Iso.app_hom]
  · simp only [biprodIso, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Category.assoc,
      biprod.inr_map_assoc, Functor.mapBiprod_inv, biprod.inr_desc_assoc, ← Functor.map_comp,
      biprod.inr_desc, Iso.refl_hom, Category.comp_id, eXF, Iso.app_hom]

end Comparison

include hUV in
private theorem exists_connecting_exact
    (ι : ∀ (W : Opens X) (q : ℤ), HcF R ((Opens.toTopCat X).obj W) q ≅ extF R W ⋙ HcF R X q)
    (eU : ∀ q : ℤ, resF R (U ⊓ V) ⋙ HcF R ((Opens.toTopCat X).obj (U ⊓ V)) q ⟶
      resF R U ⋙ HcF R ((Opens.toTopCat X).obj U) q)
    (eV : ∀ q : ℤ, resF R (U ⊓ V) ⋙ HcF R ((Opens.toTopCat X).obj (U ⊓ V)) q ⟶
      resF R V ⋙ HcF R ((Opens.toTopCat X).obj V) q)
    (heU : ∀ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X)
      (m : (extF R (U ⊓ V)).obj ((resF R (U ⊓ V)).obj F) ⟶ (extF R U).obj ((resF R U).obj F)),
      m ≫ (adjF R U).counit.app F = (adjF R (U ⊓ V)).counit.app F →
        (eU q).app F = (ι (U ⊓ V) q).hom.app _ ≫ (HcF R X q).map m ≫ (ι U q).inv.app _)
    (heV : ∀ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X)
      (m : (extF R (U ⊓ V)).obj ((resF R (U ⊓ V)).obj F) ⟶ (extF R V).obj ((resF R V).obj F)),
      m ≫ (adjF R V).counit.app F = (adjF R (U ⊓ V)).counit.app F →
        (eV q).app F = (ι (U ⊓ V) q).hom.app _ ≫ (HcF R X q).map m ≫ (ι V q).inv.app _) :
    ∃ δ : ∀ q : ℤ, HcF R X q ⟶ resF R (U ⊓ V) ⋙ HcF R ((Opens.toTopCat X).obj (U ⊓ V)) (q + 1),
      ∀ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X),
        Function.Exact (biprod.lift ((eU q).app F) (-(eV q).app F)).hom
            (biprod.desc (eXF ι U q F) (eXF ι V q F)).hom ∧
        Function.Exact (biprod.desc (eXF ι U q F) (eXF ι V q F)).hom ((δ q).app F).hom ∧
        Function.Exact ((δ q).app F).hom
            (biprod.lift ((eU (q + 1)).app F) (-(eV (q + 1)).app F)).hom := by
  obtain ⟨hall, hm, -⟩ := compactSupportCohomology_extendByZero R X
  have hu : ∀ W : Opens X, ∀ G, IsIso ((adjF R W).unit.app G) := fun W => (hall W).2.1
  have hz : ∀ W : Opens X, ∀ G, ∀ x ∉ W, IsZero (((extF R W).obj G).presheaf.stalk x) :=
    fun W => (hall W).2.2.2.1
  choose mU hmU using fun F => (hm F (U ⊓ V) U inf_le_left).exists
  choose mV hmV using fun F => (hm F (U ⊓ V) V inf_le_right).exists
  refine ⟨fun q => { app := fun F => mvδ V mU hmU mV hmV hu hz hUV q F ≫
      (ι (U ⊓ V) (q + 1)).inv.app ((resF R (U ⊓ V)).obj F), naturality := ?_ },
    fun q F => ⟨?_, ?_, ?_⟩⟩
  · intro F G φ
    change (HcF R X q).map φ ≫ (mvδ V mU hmU mV hmV hu hz hUV q G ≫ _) =
      (mvδ V mU hmU mV hmV hu hz hUV q F ≫ _) ≫
        (HcF R ((Opens.toTopCat X).obj (U ⊓ V)) (q + 1)).map ((resF R (U ⊓ V)).map φ)
    rw [← Category.assoc, mvδ_naturality, Category.assoc, Category.assoc]
    exact congrArg _ ((ι (U ⊓ V) (q + 1)).inv.naturality ((resF R (U ⊓ V)).map φ))
  · exact exact_of_ladder R ((ι (U ⊓ V) q).app _) (biprodIso V ι q F) (Iso.refl _)
      (sq₁ V mU hmU mV hmV ι q F _ _ (heU q F _ (hmU F)) (heV q F _ (hmV F)))
      (sq₂ V mU hmU mV hmV ι q F) (exact₂ V mU hmU mV hmV hu hz hUV q F)
  · refine exact_of_ladder R (biprodIso V ι q F) (Iso.refl _) ((ι (U ⊓ V) (q + 1)).app _)
      ?_ ?_ (exact₃ V mU hmU mV hmV hu hz hUV q F)
    · simpa using sq₂ V mU hmU mV hmV ι q F
    · simp
  · refine exact_of_ladder R (Iso.refl _) ((ι (U ⊓ V) (q + 1)).app _) (biprodIso V ι (q + 1) F)
      ?_ (sq₁ V mU hmU mV hmV ι (q + 1) F _ _ (heU (q + 1) F _ (hmU F))
        (heV (q + 1) F _ (hmV F))) (exact₁ V mU hmU mV hmV hu hz hUV q F)
    simp

end Derived

end MayerVietoris

open MayerVietoris in
/-- **Mayer–Vietoris for cohomology with compact supports.** Let `X` be locally compact
Hausdorff and `U, V ⊆ X` open with `U ⊔ V = ⊤`. There are natural comparison isomorphisms
`ι W q : H^q_c(W, -) ≅ H^q_c(X, j_{W!} -)`, extension maps
`e q : H^q_c(W', F|_{W'}) ⟶ H^q_c(W, F|_W)` for opens `W' ≤ W` as in
`MMP.Fourfold.compactSupportCohomology_extendByZero` (functorial in `W' ≤ W` and induced through
`ι` by the morphism `j_{W'!}(F|_{W'}) ⟶ j_{W!}(F|_W)` over `F`), and natural maps
`δ q : H^q_c(X, F) ⟶ H^{q+1}_c(U ⊓ V, F)` such that, with `H^q_c(W, F) ⟶ H^q_c(X, F)`
given by `ι W` and the counit of extension by zero, the sequence
`H^q_c(U ⊓ V) --(e, -e)--> H^q_c(U) ⊞ H^q_c(V) --e + e--> H^q_c(X) --δ q--> H^{q+1}_c(U ⊓ V)`
is exact at every term, for every sheaf `F` and every `q`. Here `Hc Y q` is the functor whose
value on `F` is `MMP.Fourfold.compactSupportCohomology R q F`. -/
@[mmp "lem_mmp_compact_support_mayer_vietoris"]
public theorem compactSupportCohomology_mayerVietoris_exact
    (R : Type) [CommRing R] (X : TopCat.{0}) [LocallyCompactSpace X] [T2Space X]
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    let res : ∀ W : Opens X, TopCat.Sheaf (ModuleCat.{0} R) X ⥤
        TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj W) := fun W =>
      haveI := W.isOpenEmbedding.functor_isContinuous
      W.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _
    let ext : ∀ W : Opens X, TopCat.Sheaf (ModuleCat.{0} R) ((Opens.toTopCat X).obj W) ⥤
        TopCat.Sheaf (ModuleCat.{0} R) X := fun W =>
      haveI := W.isOpenEmbedding.functor_isContinuous
      W.isOpenEmbedding.functor.sheafPullback _ _ _
    let adj : ∀ W : Opens X, ext W ⊣ res W := fun W =>
      haveI := W.isOpenEmbedding.functor_isContinuous
      W.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _
    let Hc : ∀ (Y : TopCat.{0}) (_ : ℤ), TopCat.Sheaf (ModuleCat.{0} R) Y ⥤ ModuleCat.{0} R :=
      fun Y q => DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (compactSupportSectionsFunctor R (X := Y)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q
    ∃ (ι : ∀ (W : Opens X) (q : ℤ), Hc ((Opens.toTopCat X).obj W) q ≅ ext W ⋙ Hc X q)
      (e : ∀ (q : ℤ) {W' W : Opens X}, W' ≤ W →
        (res W' ⋙ Hc ((Opens.toTopCat X).obj W') q ⟶ res W ⋙ Hc ((Opens.toTopCat X).obj W) q))
      (δ : ∀ q : ℤ, Hc X q ⟶ res (U ⊓ V) ⋙ Hc ((Opens.toTopCat X).obj (U ⊓ V)) (q + 1)),
      (∀ (q : ℤ) (W : Opens X), e q (le_refl W) = 𝟙 _) ∧
      (∀ (q : ℤ) (W'' W' W : Opens X) (h₁ : W'' ≤ W') (h₂ : W' ≤ W),
        e q h₁ ≫ e q h₂ = e q (h₁.trans h₂)) ∧
      (∀ (q : ℤ) (W' W : Opens X) (h : W' ≤ W) (F : TopCat.Sheaf (ModuleCat.{0} R) X)
        (m : (ext W').obj ((res W').obj F) ⟶ (ext W).obj ((res W).obj F)),
        m ≫ (adj W).counit.app F = (adj W').counit.app F →
          (e q h).app F = (ι W' q).hom.app _ ≫ (Hc X q).map m ≫ (ι W q).inv.app _) ∧
      ∀ (q : ℤ) (F : TopCat.Sheaf (ModuleCat.{0} R) X),
        let eX : ∀ W : Opens X, (Hc ((Opens.toTopCat X).obj W) q).obj ((res W).obj F) ⟶
            (Hc X q).obj F :=
          fun W => (ι W q).hom.app ((res W).obj F) ≫ (Hc X q).map ((adj W).counit.app F)
        Function.Exact
            (biprod.lift ((e q (inf_le_left : U ⊓ V ≤ U)).app F)
              (-(e q (inf_le_right : U ⊓ V ≤ V)).app F)).hom
            (biprod.desc (eX U) (eX V)).hom ∧
        Function.Exact (biprod.desc (eX U) (eX V)).hom ((δ q).app F).hom ∧
        Function.Exact ((δ q).app F).hom
            (biprod.lift ((e (q + 1) (inf_le_left : U ⊓ V ≤ U)).app F)
              (-(e (q + 1) (inf_le_right : U ⊓ V ≤ V)).app F)).hom := by
  intro res ext adj Hc
  obtain ⟨-, -, ι, e, he₀, he₁, he⟩ := compactSupportCohomology_extendByZero R X
  obtain ⟨δ, hδ⟩ := exists_connecting_exact (U := U) V hUV ι (fun q => e q inf_le_left)
    (fun q => e q inf_le_right) (fun q F m hm => he q _ _ inf_le_left F m hm)
    (fun q F m hm => he q _ _ inf_le_right F m hm)
  exact ⟨ι, e, δ, he₀, he₁, he, hδ⟩

end MMP.Fourfold
