module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksChainBaseChange
public import MMP.AlgebraicTopology.ThomClass.DirectSum
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.CupCompositeGeneric

/-!
# The orientation class of a composite, for Stacks orientation data (Fulton, Lemma 19.2 (b))

Let `X' = X ×_Y Y'` be a fibre square of complex schemes with `i : X → Y`, `i' : X' → Y'` regular
imbeddings of codimension `d` and `f : Y' → Y`, `f' : X' → X` regular imbeddings of codimension
`e`. For orientation data `(ℰ, σ, V, Q)` of `i` and `(ℰ', σ', V', Q')` of `f`
(`MMP.Modules.RegularImbeddingOrientationDatum`), the section `(s̄, s̄')` of `Q ⊕ Q'` over
`V ∩ V'` vanishes exactly on `X'`, the Thom class of `Q ⊕ Q'` is `pr₁^* u_Q ∪ pr₂^* u_{Q'}`
(`MMP.ThomClass.IsThomClass.thomCup`), and naturality of the cup product gives
`(u_i ∪ u_f)|_{V ∩ V'} = (s̄, s̄')^*(u_{Q ⊕ Q'})`.

This file contains the topological half of the argument for Stacks orientation data; the
bundle-agnostic lemmas (`MMP.range_map_comp_eq_inter_of_isPullback`, `MMP.pairPoint`,
`MMP.cohomologyWithSupports.map_cup_eq_map_cup_of_comp`, ...) are those of
`MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.CupCompositeGeneric`.

## Main results

* `MMP.Modules.RegularImbeddingOrientationDatum.isThomClass_thomClassPair`:
  `pr₁^* u_Q ∪ pr₂^* u_{Q'}` is the Thom class of `Q ⊕ Q'`.
* `MMP.Modules.RegularImbeddingOrientationDatum.map_val_eq_map_of_lift`: one factor of the chase.
* `MMP.Modules.RegularImbeddingOrientationDatum.map_val_cup_eq_map_sectionBarPairHom`: the chase
  for two orientation data.
* `MMP.Modules.RegularImbeddingOrientationDatum.excisionRestrict_congrIndex_cup_eq`: the
  orientation equation for the pair.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Lemma 19.2 (b).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology

namespace MMP.Modules

section Assembly

open Bundle ThomClass

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] {i : X ⟶ Y} {f : Y' ⟶ Y} [i.IsOver (Spec (.of ℂ))]
  [f.IsOver (Spec (.of ℂ))] {d e : ℕ}
  (D : RegularImbeddingOrientationDatum i d) (D' : RegularImbeddingOrientationDatum f e)

namespace RegularImbeddingOrientationDatum

/-- The section `(s̄, s̄')` of `Q ⊕ Q'` over `V ∩ V'`. -/
def sectionBarPair (y : ↥(D.nbhd ∩ D'.nbhd)) :
    TotalSpace (D.F × D'.F)
      ((inclLeft D.nbhd D'.nbhd *ᵖ D.Q) ×ᵇ (inclRight D.nbhd D'.nbhd *ᵖ D'.Q)) :=
  pairPoint D.F D.Q D'.F D'.Q y (D.sectionBar (inclLeft _ _ y)) (D.proj_sectionBar _)
    (D'.sectionBar (inclRight _ _ y)) (D'.proj_sectionBar _)

/-- The section `(s̄, s̄')` of `Q ⊕ Q'` over `V ∩ V'` is continuous. -/
lemma continuous_sectionBarPair : Continuous (D.sectionBarPair D') :=
  continuous_pairPoint _ _ continuous_id
    (D.continuous_sectionBar.comp (inclLeft D.nbhd D'.nbhd).continuous)
    (D'.continuous_sectionBar.comp (inclRight D.nbhd D'.nbhd).continuous)

/-- `(s̄, s̄')` as a map of spaces. -/
def sectionBarPairHom : TopCat.of ↥(D.nbhd ∩ D'.nbhd) ⟶
    TopCat.of (TotalSpace (D.F × D'.F)
      ((inclLeft D.nbhd D'.nbhd *ᵖ D.Q) ×ᵇ (inclRight D.nbhd D'.nbhd *ᵖ D'.Q))) :=
  TopCat.ofHom ⟨D.sectionBarPair D', D.continuous_sectionBarPair D'⟩

@[simp]
lemma sectionBarPairHom_apply (y : ↥(D.nbhd ∩ D'.nbhd)) :
    D.sectionBarPairHom D' y = D.sectionBarPair D' y :=
  rfl

variable (R : Type) [CommRing R]

/-- The class `pr₁^* u_Q ∪ pr₂^* u_{Q'}` of `Q ⊕ Q'` over `V ∩ V'`. -/
def thomClassPair
    (uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
      (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ))
    (uQ' : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D'.F D'.Q))
      (range (Bundle.zeroSection D'.F D'.Q)) (2 * Module.finrank ℂ D'.F : ℕ)) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace (D.F × D'.F)
      ((inclLeft D.nbhd D'.nbhd *ᵖ D.Q) ×ᵇ (inclRight D.nbhd D'.nbhd *ᵖ D'.Q))))
      (range (Bundle.zeroSection _ _)) (2 * Module.finrank ℂ (D.F × D'.F) : ℕ) :=
  thomCup D.F (inclLeft D.nbhd D'.nbhd *ᵖ D.Q) D'.F (inclRight D.nbhd D'.nbhd *ᵖ D'.Q)
    ((relativeSingularCohomology.map R (ModuleCat.of R R)
      (pullbackBundleMap D.F D.Q (inclLeft D.nbhd D'.nbhd))
      (pullbackBundleMap_compl_zeroSection D.F D.Q _) _).hom uQ)
    ((relativeSingularCohomology.map R (ModuleCat.of R R)
      (pullbackBundleMap D'.F D'.Q (inclRight D.nbhd D'.nbhd))
      (pullbackBundleMap_compl_zeroSection D'.F D'.Q _) _).hom uQ')

/-- `pr₁^* u_Q ∪ pr₂^* u_{Q'}` is the Thom class of `Q ⊕ Q'`. -/
theorem isThomClass_thomClassPair
    {uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
      (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ)}
    {uQ' : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D'.F D'.Q))
      (range (Bundle.zeroSection D'.F D'.Q)) (2 * Module.finrank ℂ D'.F : ℕ)}
    (hQ : MMP.IsThomClass (R := R) D.F D.Q uQ) (hQ' : MMP.IsThomClass (R := R) D'.F D'.Q uQ') :
    MMP.IsThomClass (R := R) (D.F × D'.F) _ (D.thomClassPair D' R uQ uQ') :=
  MMP.ThomClass.IsThomClass.thomCup (hQ.pullback _ _ _) (hQ'.pullback _ _ _)

end RegularImbeddingOrientationDatum

end Assembly

section Factor

open Bundle ThomClass cohomologyWithSupports

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] {i : X ⟶ Y}
  [i.IsOver (Spec (.of ℂ))] {d : ℕ} (D : RegularImbeddingOrientationDatum i d) (R : Type)
  [CommRing R]

/-- **One factor of the chase.** Let `N ⊆ Y(ℂ)` map into `V` by `incl`, and let `τ : N → incl^* Q`
lift `s̄ ∘ incl`. If `u|_V = s̄^* u_Q`, then `u|_N = τ^* (ĩncl^* u_Q)`. -/
theorem RegularImbeddingOrientationDatum.map_val_eq_map_of_lift
    {N : Set (UnderlyingSpace ℂ Y)} (incl : C(N, D.nbhd))
    (hincl : ∀ y, ((incl y : D.nbhd) : UnderlyingSpace ℂ Y) = y)
    (τ : TopCat.of N ⟶ TopCat.of (TotalSpace D.F (incl *ᵖ D.Q)))
    (hτ : ∀ y, Pullback.lift incl (τ y) = D.sectionBar (incl y)) {S : Set N}
    (hS : Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) i) ⊆ S)
    (hτS : τ ⁻¹' range (Bundle.zeroSection D.F (incl *ᵖ D.Q)) ⊆ S)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) i)) (2 * d : ℕ))
    (uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
      (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ))
    (hu : (RegularImbeddingOrientationDatum.excisionRestrict R _ D.nbhd _).hom u =
      (D.thomPullback R).hom uQ) :
    (relativeSingularCohomology.map R (ModuleCat.of R R)
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(N, UnderlyingSpace ℂ Y)))
        (compl_subset_preimage_compl hS) (2 * d : ℕ)).hom u =
      (relativeSingularCohomology.map R (ModuleCat.of R R) τ
        (compl_subset_preimage_compl hτS) (2 * d : ℕ)).hom
        (congrIndex R _ rfl (by rw [D.finrank_F])
          ((relativeSingularCohomology.map R (ModuleCat.of R R)
            (pullbackBundleMap D.F D.Q incl) (pullbackBundleMap_compl_zeroSection D.F D.Q incl)
            _).hom uQ)) := by
  set inclHom : TopCat.of N ⟶ TopCat.of D.nbhd := TopCat.ofHom incl
  have hS' : (inclHom ⁻¹' ((Subtype.val : D.nbhd → UnderlyingSpace ℂ Y) ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) i))) ⊆ S :=
    fun y hy ↦ hS (by
      change ((incl y : D.nbhd) : UnderlyingSpace ℂ Y) ∈
        range (UnderlyingSpace.map (K := ℂ) i) at hy
      change (y : UnderlyingSpace ℂ Y) ∈ range (UnderlyingSpace.map (K := ℂ) i)
      rwa [hincl] at hy)
  have hS'' : (inclHom ⁻¹' (D.sectionBarHom ⁻¹' range (Bundle.zeroSection D.F D.Q))) ⊆ S :=
    fun y hy ↦ hS' (D.sectionBar_preimage_subset hy)
  have e1 := map_hom_map_hom inclHom
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(D.nbhd, UnderlyingSpace ℂ Y)))
    (A := (range (UnderlyingSpace.map (K := ℂ) i))ᶜ)
    (compl_subset_preimage_compl hS') (fun _ hx ↦ hx) (compl_subset_preimage_compl hS)
    (k := TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(N, UnderlyingSpace ℂ Y)))
    (ConcreteCategory.hom_ext _ _ fun y ↦ hincl y) _ u
  rw [← e1]
  change (relativeSingularCohomology.map R _ inclHom _ _).hom
    ((RegularImbeddingOrientationDatum.excisionRestrict R _ D.nbhd _).hom u) = _
  rw [hu]
  simp only [RegularImbeddingOrientationDatum.thomPullback, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  erw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [LinearMap.comp_apply]
  erw [eqToHom_hom_eq_congrIndex (by rw [D.finrank_F])]
  rw [
    map_congrIndex inclHom rfl rfl _ (compl_subset_preimage_compl hS')
      (compl_subset_preimage_compl hS'),
    map_congrIndex τ rfl rfl _ (compl_subset_preimage_compl hτS)
      (compl_subset_preimage_compl hτS)]
  congr 1
  erw [map_hom_forget_hom_pullback_hom inclHom D.sectionBarHom D.sectionBar_preimage_subset
      (compl_subset_preimage_compl hS') (compl_subset_preimage_compl hS'')]
  rw [map_hom_map_hom τ (pullbackBundleMap D.F D.Q incl) (compl_subset_preimage_compl hτS)
      (pullbackBundleMap_compl_zeroSection D.F D.Q incl) (compl_subset_preimage_compl hS'')
      (k := inclHom ≫ D.sectionBarHom) (ConcreteCategory.hom_ext _ _ fun y ↦ hτ y)]

end Factor

section Pair

open Bundle ThomClass cohomologyWithSupports

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] {i : X ⟶ Y} {f : Y' ⟶ Y} [i.IsOver (Spec (.of ℂ))]
  [f.IsOver (Spec (.of ℂ))] {d e : ℕ}
  (D : RegularImbeddingOrientationDatum i d) (D' : RegularImbeddingOrientationDatum f e)
  (R : Type) [CommRing R]

namespace RegularImbeddingOrientationDatum

/-- The first component of `(s̄, s̄')`, lifted along `V ∩ V' → V`, is `s̄`. -/
lemma lift_sectionBarPair_fst (y : ↥(D.nbhd ∩ D'.nbhd)) :
    Pullback.lift (inclLeft D.nbhd D'.nbhd)
        ((D.sectionBarPairHom D' ≫ prodFstHom D.F _ D'.F _) y) =
      D.sectionBar (inclLeft D.nbhd D'.nbhd y) :=
  lift_pullbackMk (inclLeft D.nbhd D'.nbhd) y _ (D.proj_sectionBar _)

/-- The second component of `(s̄, s̄')`, lifted along `V ∩ V' → V'`, is `s̄'`. -/
lemma lift_sectionBarPair_snd (y : ↥(D.nbhd ∩ D'.nbhd)) :
    Pullback.lift (inclRight D.nbhd D'.nbhd)
        ((D.sectionBarPairHom D' ≫ prodSndHom D.F _ D'.F _) y) =
      D'.sectionBar (inclRight D.nbhd D'.nbhd y) :=
  lift_pullbackMk (inclRight D.nbhd D'.nbhd) y _ (D'.proj_sectionBar _)

/-- The points of `V ∩ V'` where the first component of `(s̄, s̄')` lies on the zero section lie in
`X(ℂ)`. -/
lemma sectionBarPair_fst_preimage_subset :
    (D.sectionBarPairHom D' ≫ prodFstHom D.F _ D'.F _) ⁻¹'
        range (Bundle.zeroSection D.F (inclLeft D.nbhd D'.nbhd *ᵖ D.Q)) ⊆
      Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) i) := by
  rintro y ⟨b, hb⟩
  have h := D.lift_sectionBarPair_fst D' y
  rw [← hb] at h
  exact D.sectionBar_preimage_subset
    (show inclLeft D.nbhd D'.nbhd y ∈ D.sectionBar ⁻¹' range (Bundle.zeroSection D.F D.Q) from
      ⟨_, h⟩)

/-- The points of `V ∩ V'` where the second component of `(s̄, s̄')` lies on the zero section lie
in `Y'(ℂ)`. -/
lemma sectionBarPair_snd_preimage_subset :
    (D.sectionBarPairHom D' ≫ prodSndHom D.F _ D'.F _) ⁻¹'
        range (Bundle.zeroSection D'.F (inclRight D.nbhd D'.nbhd *ᵖ D'.Q)) ⊆
      Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) f) := by
  rintro y ⟨b, hb⟩
  have h := D.lift_sectionBarPair_snd D' y
  rw [← hb] at h
  exact D'.sectionBar_preimage_subset
    (show inclRight D.nbhd D'.nbhd y ∈ D'.sectionBar ⁻¹' range (Bundle.zeroSection D'.F D'.Q) from
      ⟨_, h⟩)

/-- **The chase for two orientation data.** For orientation data `D` of `i` and `D'` of `f` with
`u_i|_V = s̄^* u_Q` and `u_f|_{V'} = s̄'^* u_{Q'}`, on `V ∩ V'`:
`(u_i ∪ u_f)|_{V ∩ V'} = (s̄, s̄')^* (pr₁^* u_Q ∪ pr₂^* u_{Q'})`. -/
theorem map_val_cup_eq_map_sectionBarPairHom
    (hX : IsClosed (range (UnderlyingSpace.map (K := ℂ) i)))
    (hW : IsClosed (range (UnderlyingSpace.map (K := ℂ) f)))
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) i)) (2 * d : ℕ))
    (u' : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * e : ℕ))
    (uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
      (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ))
    (uQ' : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D'.F D'.Q))
      (range (Bundle.zeroSection D'.F D'.Q)) (2 * Module.finrank ℂ D'.F : ℕ))
    (hu : (excisionRestrict R _ D.nbhd _).hom u = (D.thomPullback R).hom uQ)
    (hu' : (excisionRestrict R _ D'.nbhd _).hom u' = (D'.thomPullback R).hom uQ') :
    (relativeSingularCohomology.map R (ModuleCat.of R R)
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(D.nbhd ∩ D'.nbhd), UnderlyingSpace ℂ Y)))
        (compl_subset_preimage_compl (inter_subset_inter subset_rfl subset_rfl))
        ((2 * d : ℕ) + (2 * e : ℕ))).hom (cup R _ hX hW _ _ u u') =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (D.sectionBarPairHom D')
        (compl_subset_preimage_compl (inter_subset_inter
          (D.sectionBarPair_fst_preimage_subset D') (D.sectionBarPair_snd_preimage_subset D')))
        ((2 * d : ℕ) + (2 * e : ℕ))).hom
        (cup R _
          ((ThomClass.isClosed_range_zeroSection _ _).preimage (prodFstHom _ _ _ _).hom.continuous)
          ((ThomClass.isClosed_range_zeroSection _ _).preimage (prodSndHom _ _ _ _).hom.continuous)
          _ _
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prodFstHom D.F _ D'.F _) _ _).hom
            (congrIndex R _ rfl (by rw [D.finrank_F])
              ((relativeSingularCohomology.map R (ModuleCat.of R R)
                (pullbackBundleMap D.F D.Q (inclLeft D.nbhd D'.nbhd))
                (pullbackBundleMap_compl_zeroSection D.F D.Q _) _).hom uQ)))
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prodSndHom D.F _ D'.F _) _ _).hom
            (congrIndex R _ rfl (by rw [D'.finrank_F])
              ((relativeSingularCohomology.map R (ModuleCat.of R R)
                (pullbackBundleMap D'.F D'.Q (inclRight D.nbhd D'.nbhd))
                (pullbackBundleMap_compl_zeroSection D'.F D'.Q _) _).hom uQ')))) :=
  map_cup_eq_map_cup_of_comp _ (D.sectionBarPairHom D') (prodFstHom D.F _ D'.F _)
    (prodSndHom D.F _ D'.F _) hX hW (ThomClass.isClosed_range_zeroSection _ _)
    (ThomClass.isClosed_range_zeroSection _ _) (hX.preimage continuous_subtype_val)
    (hW.preimage continuous_subtype_val) subset_rfl subset_rfl
    (D.sectionBarPair_fst_preimage_subset D') (D.sectionBarPair_snd_preimage_subset D') _ _ u u'
    _ _
    (D.map_val_eq_map_of_lift R (inclLeft D.nbhd D'.nbhd) (fun _ ↦ rfl) _
      (D.lift_sectionBarPair_fst D') subset_rfl (D.sectionBarPair_fst_preimage_subset D') u uQ hu)
    (D'.map_val_eq_map_of_lift R (inclRight D.nbhd D'.nbhd) (fun _ ↦ rfl) _
      (D.lift_sectionBarPair_snd D') subset_rfl (D.sectionBarPair_snd_preimage_subset D') u' uQ'
      hu')

/-- For a fibre square `X' = X ×_Y Y'`, the zero locus of `(s̄, s̄')` on `V ∩ V'` is in `X'(ℂ)`. -/
lemma sectionBarPair_preimage_subset {X' : Scheme.{0}} [X'.Over (Spec (.of ℂ))]
    {f' : X' ⟶ X} {i' : X' ⟶ Y'} [f'.IsOver (Spec (.of ℂ))] [i'.IsOver (Spec (.of ℂ))]
    (sq : IsPullback i' f' f i) :
    D.sectionBarPairHom D' ⁻¹' range (Bundle.zeroSection (D.F × D'.F)
        ((inclLeft D.nbhd D'.nbhd *ᵖ D.Q) ×ᵇ (inclRight D.nbhd D'.nbhd *ᵖ D'.Q))) ⊆
      Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) (f' ≫ i)) := fun y hy ↦ by
  rw [← preimage_prodFstHom_inter_preimage_prodSndHom] at hy
  change (y : UnderlyingSpace ℂ Y) ∈ range (UnderlyingSpace.map (K := ℂ) (f' ≫ i))
  rw [range_map_comp_eq_inter_of_isPullback sq]
  exact ⟨D.sectionBarPair_fst_preimage_subset D' hy.1, D.sectionBarPair_snd_preimage_subset D' hy.2⟩

/-- **The orientation equation for the pair.** `(u_i ∪ u_f)|_{V ∩ V'}`, as a class with supports
in `X'(ℂ) = X(ℂ) ∩ Y'(ℂ)` of degree `2(d + e)`, is `(s̄, s̄')^*` of the Thom class
`pr₁^* u_Q ∪ pr₂^* u_{Q'}` of `Q ⊕ Q'`. -/
theorem excisionRestrict_congrIndex_cup_eq {X' : Scheme.{0}} [X'.Over (Spec (.of ℂ))]
    {f' : X' ⟶ X} {i' : X' ⟶ Y'} [f'.IsOver (Spec (.of ℂ))] [i'.IsOver (Spec (.of ℂ))]
    (sq : IsPullback i' f' f i)
    (hX : IsClosed (range (UnderlyingSpace.map (K := ℂ) i)))
    (hW : IsClosed (range (UnderlyingSpace.map (K := ℂ) f)))
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) i)) (2 * d : ℕ))
    (u' : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * e : ℕ))
    (uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
      (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ))
    (uQ' : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D'.F D'.Q))
      (range (Bundle.zeroSection D'.F D'.Q)) (2 * Module.finrank ℂ D'.F : ℕ))
    (hu : (excisionRestrict R _ D.nbhd _).hom u = (D.thomPullback R).hom uQ)
    (hu' : (excisionRestrict R _ D'.nbhd _).hom u' = (D'.thomPullback R).hom uQ') :
    (excisionRestrict R (range (UnderlyingSpace.map (K := ℂ) (f' ≫ i))) (D.nbhd ∩ D'.nbhd)
        (2 * (d + e) : ℕ)).hom
        (congrIndex R _ (congrArg compl (range_map_comp_eq_inter_of_isPullback sq).symm)
          (by push_cast; ring) (cup R _ hX hW _ _ u u')) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (D.sectionBarPairHom D') _ _ ≫
        cohomologyWithSupports.forget R (ModuleCat.of R R) _
          (D.sectionBarPair_preimage_subset D' sq) _ ≫
        eqToHom (by rw [Module.finrank_prod, D.finrank_F, D'.finrank_F, mul_add])).hom
        (D.thomClassPair D' R uQ uQ') := by
  have hT : ((Subtype.val : ↥(D.nbhd ∩ D'.nbhd) → UnderlyingSpace ℂ Y) ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) i) ∩
      Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) f))ᶜ =
      (Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) (f' ≫ i)))ᶜ := by
    rw [range_map_comp_eq_inter_of_isPullback sq]; rfl
  change (relativeSingularCohomology.map R _ (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
    C(↥(D.nbhd ∩ D'.nbhd), UnderlyingSpace ℂ Y))) (fun _ hx ↦ hx) _).hom _ = _
  rw [map_congrIndex _ (congrArg compl (range_map_comp_eq_inter_of_isPullback sq).symm) hT _
    (compl_subset_preimage_compl (inter_subset_inter subset_rfl subset_rfl)) (fun _ hx ↦ hx),
    map_val_cup_eq_map_sectionBarPairHom D D' R hX hW u u' uQ uQ' hu hu']
  simp only [cohomologyWithSupports.pullback]
  rw [map_congrIndex (prodFstHom _ _ _ _) rfl rfl _ (fun _ hx ↦ hx) (fun _ hx ↦ hx),
    map_congrIndex (prodSndHom _ _ _ _) rfl rfl _ (fun _ hx ↦ hx) (fun _ hx ↦ hx),
    cup_congrIndex,
    map_congrIndex (D.sectionBarPairHom D') rfl rfl _
      (compl_subset_preimage_compl (inter_subset_inter
        (D.sectionBarPair_fst_preimage_subset D') (D.sectionBarPair_snd_preimage_subset D')))
      (compl_subset_preimage_compl (inter_subset_inter
        (D.sectionBarPair_fst_preimage_subset D') (D.sectionBarPair_snd_preimage_subset D'))),
    congrIndex_congrIndex]
  refine Eq.trans ?_ (pullback_comp_forget_comp_eqToHom_hom (D.sectionBarPairHom D')
    (D.sectionBarPair_preimage_subset D' sq)
    (by rw [Module.finrank_prod, D.finrank_F, D'.finrank_F, mul_add])
    _ (compl_subset_preimage_compl (D.sectionBarPair_preimage_subset D' sq)) _).symm
  have hσ' : D.sectionBarPairHom D' ⁻¹'
      (prodFstHom D.F _ D'.F _ ⁻¹' range (Bundle.zeroSection D.F (inclLeft D.nbhd D'.nbhd *ᵖ D.Q)) ∩
        prodSndHom D.F _ D'.F _ ⁻¹'
          range (Bundle.zeroSection D'.F (inclRight D.nbhd D'.nbhd *ᵖ D'.Q))) ⊆
      Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) (f' ≫ i)) := fun y hy ↦
    D.sectionBarPair_preimage_subset D' sq
      (by rw [← preimage_prodFstHom_inter_preimage_prodSndHom]; exact hy)
  refine Eq.trans ?_ (congrArg (congrIndex R _ rfl _) (map_congrIndex (D.sectionBarPairHom D')
    (congrArg compl (preimage_prodFstHom_inter_preimage_prodSndHom D.F _ D'.F _)) rfl
    (two_mul_finrank_add_two_mul_finrank D.F D'.F)
    (compl_subset_preimage_compl hσ')
    (compl_subset_preimage_compl (D.sectionBarPair_preimage_subset D' sq)) _).symm)
  refine (congrIndex_map_hom (D.sectionBarPairHom D') _ _ (compl_subset_preimage_compl hσ') _
    _).trans ?_
  exact (congrIndex_congrIndex R _ rfl rfl _ _ _).symm

end RegularImbeddingOrientationDatum

end Pair

end MMP.Modules
