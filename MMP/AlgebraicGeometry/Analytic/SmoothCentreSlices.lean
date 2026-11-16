module

public import MMP.AlgebraicGeometry.Analytic.SchemeManifoldSlice
public import MMP.AlgebraicGeometry.Analytic.RationalSheafCohomologySingular
public import MMP.AlgebraicGeometry.Analytic.RationalSingularComparison
public import MMP.AlgebraicGeometry.Analytic.ClosedSubschemeOrientation
public import MMP.AlgebraicGeometry.Analytic.BlowupFibre.Euler
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel

/-!
# Analytic slices along smooth centres, and the rational splitting of smooth-centre blowups

This file studies the complex realization near a smooth centre, in two settings.

**Punctured slice germs.** Let `f : Z ⟶ X` be a proper surjective morphism of complex algebraic
schemes which is an isomorphism off a smooth closed subscheme `T ⊆ X`, and let `h : X ⟶ B` be a
morphism to a smooth complex curve such that `T ⟶ B` is finite étale. Suppose that near
`E = (f⁻¹ T)_red` the scheme `Z` is smooth, `E` is a simple normal crossing divisor, and `Z ⟶ B`
and every intersection `⋂_{i ∈ J} E_i` of components of `E` are smooth over `B`. Then for
`b ∈ B(ℂ)` and `x ∈ T(ℂ)` over `b`, the germ of the pair `(X^an, T^an)` at `x` is the product of
the germ of the slice `(X_b^an, {x})` at `x` with the germ `(B^an, b)`, by a homeomorphism over
`B^an` which is the identity on the slice. Consequently restriction to the slice identifies the
stalks at `x` of the higher direct images of the constant sheaf along the punctured inclusions
`j : X^an ∖ T^an ↪ X^an` and `j_b : X_b^an ∖ T_b^an ↪ X_b^an`:
`(R^q j_* ℚ)_x ≅ (R^q j_{b*} ℚ)_x`.

**The splitting of a smooth-centre blowup.** Let `b : V' ⟶ V` be the blowup of a smooth complex
variety `V` along a smooth closed centre `i : T ⟶ V` all of whose components have codimension
`c ≥ 2`. On `V^an` there is an isomorphism in the bounded below derived category of sheaves of
`ℚ`-vector spaces `ℚ_V ⊕ ⨁_{a=1}^{c-1} i_* ℚ_T[-2a] ≅ Rb_* ℚ_{V'}` whose first component is the
structural unit `ℚ_V ⟶ Rb_* ℚ_{V'}`. Consequently, for every Zariski-closed `Q ⊆ V` and every
degree `k`, pullback `H^k(Q; ℚ) ⟶ H^k(b⁻¹(Q); ℚ)` on the sheaf cohomology of the constant sheaf
`ℚ` is a split injection, and so it is for any finite composite of such blowups.

The summand maps come from classes on `V'`. Let `R ⊆ V'` be the exceptional divisor and `ε` the
image in `H²(V'; ℚ)` of its orientation class in `H²(V', V' ∖ R; ℚ)`. Then `ε` vanishes on
`V' ∖ R`, and on a fibre `b⁻¹(t) ≅ ℙ^{c-1}`, `t ∈ T`, it restricts to the Euler class of the
normal bundle of `R`, which is nonzero; so the powers `ε^{a+1}`, `a < c - 1`, are nonzero on the
fibres. Sheaf cohomology computed by an injective resolution `J` of `ℚ_{V'}` is singular
cohomology, naturally in continuous maps; injective sheaves restrict to injective sheaves on open
subsets and are flasque. Hence `ε^{a+1}` is represented by a cocycle of `Γ(V', J)` vanishing on
`b⁻¹(V ∖ T)`, which, read as a map `ℚ_V ⟶ b_* J^{2(a+1)}`, factors through `ℚ_V ⟶ i_* ℚ_T`. The
resulting morphism `i_* ℚ_T[-2(a+1)] ⟶ Rb_* ℚ_{V'}` is nonzero on the stalks of `H^{2(a+1)}` at
the points of `T`. By proper base change and the cohomology of `ℙ^{c-1}`, these stalks are lines
and all other stalks of `H^n(Rb_* ℚ_{V'})` with `n ≠ 0` vanish, so the direct sum of the unit and
these morphisms is an isomorphism on all stalks of all cohomology sheaves, hence in `D⁺`. Its
first projection retracts the unit, and the retraction survives restriction to closed subsets
and composition of blowups.

## Main results

* `MMP.Fourfold.exists_homeomorph_prod_and_stalk_iso_of_relativeSNC`: the product of germs and
  the stalk isomorphism, characterised on germs of classes;
  `MMP.Fourfold.exists_homeomorph_prod_and_stalk_iso_of_isSNC` is the same statement for snc data
  given on all of `Z`.
* `MMP.Mori.smooth_comap_subschemeι`: a closed subscheme smooth over `Y` has smooth trace on
  every open subscheme.
* `MMP.Conductor.exists_biprod_iso_rightDerivedFunctorPlus_blowUpToBase`: the splitting of
  `Rb_* ℚ_{V'}`, together with the split injectivity of pullback on the rational sheaf cohomology
  of closed subsets, for every finite composite of smooth-centre blowups.

## Implementation notes

* The fibre `X_b^an` is the topological fibre `(h^an)⁻¹(b) ⊆ X^an` with the subspace topology,
  and `T^an` is the image of `T(ℂ)` in `X(ℂ)`; `R^q j_* ℚ` is `MMP.Fourfold.higherDirectImage`.
* The stalk isomorphism is characterised on germs: the germ at `x` of a class
  `α ∈ H^q(V ∖ T; ℚ)` goes to the germ of its restriction to `V_b ∖ T_b`. Such germs exhaust
  the stalk, so this pins the isomorphism; its compatibility with restriction of classes from
  resolution neighbourhoods `f⁻¹(V)` and from their fibres is then functoriality of singular
  cohomology.
* The stalk isomorphism is deduced from the product germ. Product neighbourhoods
  `φ⁻¹(A × D')`, with `D'` a contractible neighbourhood of `b`, are cofinal among the
  neighbourhoods of `x`; on such a neighbourhood `P` the inclusion of the punctured slice
  `P_b ∖ T_b = (A ∖ {x}) × {b}` into `P ∖ T = (A ∖ {x}) × D'` is a homotopy equivalence, so
  restriction is an isomorphism on singular cohomology. Restriction of germs is therefore
  bijective on stalks of the presheaves `V ↦ H^q(V ∖ T; ℚ)` and `O ↦ H^q(O ∖ T_b; ℚ)`, which are
  the stalks of their sheafifications.
* In the splitting, the constant sheaf `ℚ_{V'}` is modelled as the inverse image `b^* ℚ_V` and
  `ℚ_T` as `i^* ℚ_V`; both are canonically constant. With this model the structural unit is the
  composite of the adjunction unit `ℚ_V ⟶ b_* b^* ℚ_V`, placed in degree `0`, with the comparison
  `b_* K ⟶ Rb_* K` (`CategoryTheory.Functor.rightDerivedFunctorPlusUnith`).
* Complexes concentrated in one degree are the images under `DerivedCategory.Plus.Qh` of the
  single complexes of `HomotopyCategory.Plus.singleFunctor`; `i_* ℚ_T[-2a]` is `i_* ℚ_T` placed
  in degree `2a`. As `i` is a closed embedding, `i_*` is exact and needs no derivation.
* "The centre has codimension `c`" is that every maximal irreducible closed subset of the
  support of the blown-up ideal has codimension `c`; the centre need not be connected.
* "Variety" is: integral, separated, locally of finite type and quasi-compact over `ℂ`.
* The cohomology `H^k(Z; ℚ)` of a closed subset is the sheaf cohomology
  `Hᵏ(RΓ(Z^an, ℚ_{Z^an}))` of the constant sheaf `ℚ` on the set `Z^an` of `ℂ`-points lying over
  `Z`, with the subspace topology, `Γ` being sections over the whole space; the reduced structure
  on `b⁻¹(Q)` does not change this set. For `g_Q : g⁻¹(Q)^an ⟶ Q^an` the restriction of the
  realized map, pullback `H^k(Q; ℚ) ⟶ H^k(g⁻¹(Q); ℚ)` is `Hᵏ RΓ(Q^an, -)` of the structural
  unit `ℚ_Q ⟶ R(g_Q)_* ℚ_{g⁻¹Q}` (the canonical morphism `ℚ_Q ⟶ (g_Q)_* ℚ_{g⁻¹Q}`, adjoint to the
  unit section, followed by `(g_Q)_* ⟶ R(g_Q)_*`), followed by the identification
  `RΓ(Q^an, R(g_Q)_* -) ≅ RΓ(g⁻¹(Q)^an, -)` of composite derived functors
  (`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`).
* A finite composite of smooth-centre blowups is a morphism in the multiplicative closure
  (`CategoryTheory.MorphismProperty.multiplicativeClosure`) of the class of blowups, over `ℂ`, of
  a smooth variety along a smooth centre of pure codimension at least `2`, the codimension
  allowed to vary from step to step; a single such blowup is the case of length one.
* The orientation class of the exceptional divisor is built from the canonical section of its
  line bundle through `MMP.Topology.divisorOrientationDatum`, so that its restriction to the
  fibres is the Euler class of `MMP.Topology.map_eulerClass_divisorOrientationDatum_ne_zero`; the
  comparison of sheaf and singular cohomology is
  `MMP.Analytic.exists_homology_globalSections_injectiveResolution_iso_relCohomology`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98]
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, §19.2.
* [B. Iversen, *Cohomology of sheaves*], II.5 (pullback on cohomology), VII.1 (proper base
  change).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Topology MMP.Analytic
  MMP.Analytic.ComplexPoints

namespace MMP.Analytic

/-- The complex points of `V` lying over the support of an ideal sheaf `I` are exactly the
image of the realization of the closed immersion `I.subscheme ⟶ V`. -/
theorem range_analyticMap_subschemeι {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (I : V.IdealSheafData) :
    Set.range (analyticMap (sX := I.subschemeι ≫ sV) I.subschemeι rfl) =
      {x : analyticSpace sV | x.toScheme ∈ I.support} := by
  letI : V.Over (Spec (.of ℂ)) := ⟨sV⟩
  letI : I.subscheme.Over (Spec (.of ℂ)) := ⟨I.subschemeι ≫ sV⟩
  haveI : I.subschemeι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have hf : ⇑(analyticMap (sX := I.subschemeι ≫ sV) I.subschemeι rfl) =
      (homeomorphUnderlyingSpace (X := V)).symm ∘
        MMP.UnderlyingSpace.map (K := ℂ) I.subschemeι ∘
          (homeomorphUnderlyingSpace (X := I.subscheme)) := by
    funext x
    apply (homeomorphUnderlyingSpace (X := V)).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    rfl
  have hpre := Set.ext_iff.1
    (MMP.Analytic.ComplexPoints.preimage_homeomorphUnderlyingSpace_range_map I.subschemeι)
  have hs : ∀ v : V, v ∈ I.support ↔ v ∈ Set.range I.subschemeι := fun v => by
    rw [I.range_subschemeι]
    rfl
  ext x
  simp only [Set.mem_setOf_eq, hs]
  constructor
  · rintro ⟨y, rfl⟩
    refine (hpre _).1 ⟨homeomorphUnderlyingSpace (X := I.subscheme) y, ?_⟩
    have h1 := congrFun hf y
    simp only [Function.comp_apply] at h1
    rw [h1]
    exact (Homeomorph.apply_symm_apply (homeomorphUnderlyingSpace (X := V)) _).symm
  · intro hx
    obtain ⟨z, hz⟩ := (hpre x).2 hx
    refine ⟨(homeomorphUnderlyingSpace (X := I.subscheme)).symm z, ?_⟩
    apply (homeomorphUnderlyingSpace (X := V)).injective
    rw [hf]
    simpa using hz

end MMP.Analytic

namespace MMP.Fourfold

/-! ### Restriction to a slice on stalks of punctured direct images -/

section Slice

/-- Homotopic maps induce the same map on rational singular cohomology. -/
private lemma rationalCohomologyMap_eq_of_homotopy {X' X : TopCat.{0}} {f g : X' ⟶ X}
    (H : TopCat.Homotopy f g) (q : ℕ) :
    rationalCohomologyMap f q = rationalCohomologyMap g q :=
  MMP.relativeSingularCohomology.map_eq_of_homotopy ℚ H
    (fun _ hy ↦ absurd (Set.mem_univ _) hy) _ _ q

variable {Y : TopCat.{0}}

/-- The inclusion `Y ∖ τ ↪ Y`. -/
private abbrev jY (τ : Set Y) : TopCat.of ↥τᶜ ⟶ Y :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `F ∖ τ ↪ F` of the punctured slice. -/
private abbrev jF (τ F : Set Y) : TopCat.of ↥((Subtype.val : F → Y) ⁻¹' τ)ᶜ ⟶ TopCat.of F :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The slice `V ∩ F` of an open `V ⊆ Y`, as an open of `F`. -/
private abbrev sliceOpen (F : Set Y) (V : Opens Y) : Opens (TopCat.of F) :=
  ⟨Subtype.val ⁻¹' (V : Set Y), V.isOpen.preimage continuous_subtype_val⟩

/-- The inclusion `(V ∩ F) ∖ τ ↪ V ∖ τ`. -/
private abbrev sliceRes (τ F : Set Y) (V : Opens Y) :
    preimageSpace (jF τ F) (sliceOpen F V) ⟶ preimageSpace (jY τ) V :=
  TopCat.ofHom ⟨fun y ↦ ⟨⟨y.1.1.1, y.1.2⟩, y.2⟩,
    ((continuous_subtype_val.comp (continuous_subtype_val.comp
      continuous_subtype_val)).subtype_mk _).subtype_mk _⟩

/-- If restriction `H^q(P ∖ τ) → H^q((P ∩ F) ∖ τ)` is an isomorphism for a cofinal system of
neighbourhoods `P` of `x ∈ F`, then restriction of germs is an isomorphism
`(R^q j_* ℚ)_x ≅ (R^q j_{F*} ℚ)_x`. -/
private theorem exists_stalk_iso_of_isIso_sliceRes (τ F : Set Y) (x : Y) (hxF : x ∈ F) (q : ℕ)
    (hcof : ∀ V : Opens Y, x ∈ V → ∃ P : Opens Y, x ∈ P ∧ P ≤ V ∧
      IsIso (rationalCohomologyMap (sliceRes τ F P) q)) :
    ∃ e : ((TopCat.Sheaf.forget _ _).obj (higherDirectImage (jY τ) q)).stalk x ≅
        ((TopCat.Sheaf.forget _ _).obj (higherDirectImage (jF τ F) q)).stalk ⟨x, hxF⟩,
      ∀ (V : Opens Y) (hxV : x ∈ V) (α : rationalCohomology (preimageSpace (jY τ) V) q),
        e.hom (higherDirectImageGerm (jY τ) q x hxV α) =
          higherDirectImageGerm (jF τ F) q (V := sliceOpen F V) ⟨x, hxF⟩ hxV
            (rationalCohomologyMap (sliceRes τ F V) q α) := by
  let Pj := directImagePresheaf (jY τ) q
  let Pb := directImagePresheaf (jF τ F) q
  let ι : TopCat.of F ⟶ Y := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let η : Pj ⟶ (TopCat.Presheaf.pushforward _ ι).obj Pb :=
    { app := fun V ↦ rationalCohomologyMap (sliceRes τ F V.unop) q
      naturality := by
        intro V W i
        change rationalCohomologyMap (preimageInclusion _ _) q ≫ _ =
          _ ≫ rationalCohomologyMap (preimageInclusion _ _) q
        rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_comp]
        rfl }
  have hnat : ∀ {V W : Opens Y} (i : W ≤ V) (s : Pj.obj (op V)),
      rationalCohomologyMap (sliceRes τ F W) q (Pj.map (homOfLE i).op s) =
        Pb.map (homOfLE (show sliceOpen F W ≤ sliceOpen F V from fun _ h ↦ i h)).op
          (rationalCohomologyMap (sliceRes τ F V) q s) :=
    fun i s ↦ ConcreteCategory.congr_hom (η.naturality (homOfLE i).op) s
  let ρ : Pj.stalk x ⟶ Pb.stalk ⟨x, hxF⟩ :=
    (TopCat.Presheaf.stalkFunctor _ x).map η ≫ Pb.stalkPushforward _ ι ⟨x, hxF⟩
  have hρ : ∀ (V : Opens Y) (hxV : x ∈ V), Pj.germ V x hxV ≫ ρ =
      rationalCohomologyMap (sliceRes τ F V) q ≫ Pb.germ (sliceOpen F V) ⟨x, hxF⟩ hxV :=
    fun V hxV ↦ (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Pb.stalkPushforward _ ι ⟨x, hxF⟩)
        (TopCat.Presheaf.stalkFunctor_map_germ V x hxV η)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (η.app (op V) ≫ ·) (Pb.stalkPushforward_germ _ ι V ⟨x, hxF⟩ hxV))))
  have hρ' : ∀ (V : Opens Y) (hxV : x ∈ V) (s : Pj.obj (op V)), ρ (Pj.germ V x hxV s) =
      Pb.germ (sliceOpen F V) ⟨x, hxF⟩ hxV (rationalCohomologyMap (sliceRes τ F V) q s) :=
    fun V hxV s ↦ ConcreteCategory.congr_hom (hρ V hxV) s
  -- every open of the slice through `x` is the slice of an open of `Y` through `x`
  have hslice : ∀ O : Opens (TopCat.of F), (⟨x, hxF⟩ : F) ∈ O →
      ∃ V : Opens Y, x ∈ V ∧ sliceOpen F V = O := by
    intro O hO
    obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.mp O.isOpen
    have hO' : (⟨x, hxF⟩ : F) ∈ (O : Set F) := hO
    rw [← hte] at hO'
    exact ⟨⟨t, ht⟩, hO', Opens.ext hte⟩
  have hbij : Function.Bijective ρ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨V, hxV, s, rfl⟩ := Pj.exists_germ_eq t
      have ht' : Pb.germ (sliceOpen F V) ⟨x, hxF⟩ hxV (rationalCohomologyMap (sliceRes τ F V) q s)
          = Pb.germ (sliceOpen F V) ⟨x, hxF⟩ hxV 0 :=
        (hρ' V hxV s).symm.trans (ht.trans (map_zero _).symm)
      obtain ⟨W, hxW, iW, iV, hW⟩ := Pb.germ_eq _ hxV hxV _ _ ht'
      obtain ⟨V'', hxV'', rfl⟩ := hslice W hxW
      obtain ⟨P, hxP, hPV, hiso⟩ := hcof (V ⊓ V'') ⟨hxV, hxV''⟩
      have hPV' : P ≤ V := hPV.trans inf_le_left
      have hPW : sliceOpen F P ≤ sliceOpen F V'' := fun _ h ↦ (hPV h).2
      have h0 : rationalCohomologyMap (sliceRes τ F P) q (Pj.map (homOfLE hPV').op s) = 0 := by
        rw [hnat]
        have : homOfLE (show sliceOpen F P ≤ sliceOpen F V from fun _ h ↦ hPV' h) =
            homOfLE hPW ≫ iW := Subsingleton.elim _ _
        rw [this, op_comp, Functor.map_comp]
        exact (congrArg (Pb.map (homOfLE hPW).op) hW).trans (by simp; rfl)
      have hinj : Function.Injective (rationalCohomologyMap (sliceRes τ F P) q) :=
        ((ConcreteCategory.isIso_iff_bijective _).mp hiso).1
      have h1 : Pj.map (homOfLE hPV').op s = 0 :=
        hinj (h0.trans (map_zero (ConcreteCategory.hom
          (rationalCohomologyMap (sliceRes τ F P) q))).symm)
      rw [← Pj.germ_res_apply (homOfLE hPV') x hxP, h1, map_zero]
    · intro t
      obtain ⟨O, hxO, s, rfl⟩ := Pb.exists_germ_eq t
      obtain ⟨V'', hxV'', rfl⟩ := hslice O hxO
      obtain ⟨P, hxP, hPV, hiso⟩ := hcof V'' hxV''
      have hsurj : Function.Surjective (rationalCohomologyMap (sliceRes τ F P) q) :=
        ((ConcreteCategory.isIso_iff_bijective _).mp hiso).2
      have hPW : sliceOpen F P ≤ sliceOpen F V'' := fun _ h ↦ hPV h
      obtain ⟨α, hα⟩ := hsurj (Pb.map (homOfLE hPW).op s)
      refine ⟨Pj.germ P x hxP α, ?_⟩
      rw [hρ' P hxP α, hα, Pb.germ_res_apply]
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).mpr hbij
  let σj : Pj.stalk x ⟶ ((TopCat.Sheaf.forget _ _).obj (higherDirectImage (jY τ) q)).stalk x :=
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      (toSheafify (Opens.grothendieckTopology Y) Pj)
  let σb : Pb.stalk ⟨x, hxF⟩ ⟶
      ((TopCat.Sheaf.forget _ _).obj (higherDirectImage (jF τ F) q)).stalk ⟨x, hxF⟩ :=
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of F) (ModuleCat.{0} ℚ) ⟨x, hxF⟩).map
      (toSheafify (Opens.grothendieckTopology (TopCat.of F)) Pb)
  have : IsIso σj := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso _ _ _
  have : IsIso σb := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso _ _ _
  refine ⟨(asIso σj).symm ≪≫ asIso ρ ≪≫ asIso σb, fun V hxV α ↦ ?_⟩
  have key : (Pj.germ V x hxV ≫ σj) ≫ (inv σj ≫ ρ ≫ σb) =
      rationalCohomologyMap (sliceRes τ F V) q ≫ Pb.germ (sliceOpen F V) ⟨x, hxF⟩ hxV ≫ σb := by
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [reassoc_of% (hρ V hxV)]
    exact Category.assoc _ _ _
  exact ConcreteCategory.congr_hom key α

/-- Let `φ : U' ≃ₜ U₀ × D` be a product chart at `x` over `g : Y → B` which sends `τ` to the
section through `x` and `g` to the second projection, and suppose `b = g x` has arbitrarily
small contractible open neighbourhoods. Then the neighbourhoods `P` of `x` on which restriction
`H^q(P ∖ τ) → H^q((P ∩ g⁻¹ b) ∖ τ)` is an isomorphism are cofinal. -/
private theorem isIso_sliceRes_of_homeomorph_prod {Bs : TopCat.{0}} (g : Y → Bs) (τ : Set Y)
    (b : Bs) (x : Y) (hxb : g x = b) (q : ℕ)
    {U' : Opens Y} {U₀ : Opens (TopCat.of ↥(g ⁻¹' {b}))} {D : Opens Bs}
    (hxU : x ∈ U') (hx₀ : ⟨x, hxb⟩ ∈ U₀) (hbD : b ∈ D) (φ : U' ≃ₜ U₀ × D)
    (hφx : φ ⟨x, hxU⟩ = (⟨⟨x, hxb⟩, hx₀⟩, ⟨b, hbD⟩))
    (hφg : ∀ y : U', ((φ y).2 : Bs) = g y)
    (hφτ : ∀ y : U', (y : Y) ∈ τ ↔ (φ y).1 = ⟨⟨x, hxb⟩, hx₀⟩)
    (hloc : ∀ N ∈ 𝓝 b, ∃ D' : Set Bs, IsOpen D' ∧ b ∈ D' ∧ D' ⊆ N ∧ ContractibleSpace D') :
    ∀ V : Opens Y, x ∈ V → ∃ P : Opens Y, x ∈ P ∧ P ≤ V ∧
      IsIso (rationalCohomologyMap (sliceRes τ (g ⁻¹' {b}) P) q) := by
  intro V hxV
  -- a product neighbourhood `A × C` of `φ x` inside `φ (V ∩ U')`
  have hS : IsOpen (φ.symm ⁻¹' {y : U' | (y : Y) ∈ V}) :=
    (V.isOpen.preimage continuous_subtype_val).preimage φ.symm.continuous
  have hxS : (⟨⟨x, hxb⟩, hx₀⟩, ⟨b, hbD⟩) ∈ φ.symm ⁻¹' {y : U' | (y : Y) ∈ V} := by
    rw [← hφx]
    simpa using hxV
  obtain ⟨A, C, hA, hC, hx₀A, hbC, hAC⟩ := isOpen_prod_iff.mp hS _ _ hxS
  have hCN : Subtype.val '' C ∈ 𝓝 b :=
    (D.isOpen.isOpenMap_subtype_val C hC).mem_nhds ⟨_, hbC, rfl⟩
  obtain ⟨D', hD'o, hbD', hD'C, hD'c⟩ := hloc _ hCN
  have hD'D : D' ⊆ D := fun z hz ↦ by
    obtain ⟨c, -, rfl⟩ := hD'C hz
    exact c.2
  let D'' : Set D := Subtype.val ⁻¹' D'
  have hD''C : D'' ⊆ C := fun z hz ↦ by
    obtain ⟨c, hc, hcz⟩ := hD'C hz
    rwa [Subtype.ext hcz] at hc
  let Q : Set U' := φ ⁻¹' (A ×ˢ D'')
  have hQ : IsOpen Q := (hA.prod (hD'o.preimage continuous_subtype_val)).preimage φ.continuous
  let P : Opens Y := ⟨Subtype.val '' Q, U'.isOpen.isOpenMap_subtype_val Q hQ⟩
  have hPU : ∀ {y : Y}, y ∈ P → y ∈ U' := fun {y} hy ↦ by
    obtain ⟨u, -, rfl⟩ := hy
    exact u.2
  have hmemP : ∀ (u : U'), (u : Y) ∈ P ↔ φ u ∈ A ×ˢ D'' := fun u ↦
    ⟨fun ⟨u', hu', he⟩ ↦ by rwa [Subtype.ext he] at hu', fun hu ↦ ⟨u, hu, rfl⟩⟩
  have hxP : x ∈ P := (hmemP ⟨x, hxU⟩).2 (by rw [hφx]; exact ⟨hx₀A, hbD'⟩)
  have hPV : P ≤ V := fun y hy ↦ by
    obtain ⟨u, hu, rfl⟩ := hy
    simpa using hAC ⟨hu.1, hD''C hu.2⟩
  refine ⟨P, hxP, hPV, ?_⟩
  -- the contraction of `D'` onto `b`
  obtain ⟨y₀, hy₀⟩ := id_nullhomotopic D'
  obtain ⟨c⟩ := hy₀.trans (ContinuousMap.homotopic_const_iff.mpr
    (PathConnectedSpace.joined y₀ ⟨b, hbD'⟩))
  -- the deformation of `P ∖ τ` onto its slice, along the contraction of the second factor
  let Bp := preimageSpace (jY τ) P
  let Ap := preimageSpace (jF τ (g ⁻¹' {b})) (sliceOpen (g ⁻¹' {b}) P)
  let u : Bp → U' := fun z ↦ ⟨z.1.1, hPU z.2⟩
  have hu : Continuous u := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have huQ : ∀ z, φ (u z) ∈ A ×ˢ D'' := fun z ↦ (hmemP (u z)).1 z.2
  let d : Bp → D' := fun z ↦ ⟨(φ (u z)).2, (huQ z).2⟩
  have hd : Continuous d :=
    (continuous_subtype_val.comp (continuous_snd.comp (φ.continuous.comp hu))).subtype_mk _
  let w : unitInterval × Bp → U' := fun tz ↦
    φ.symm ((φ (u tz.2)).1, ⟨c (tz.1, d tz.2), hD'D (c (tz.1, d tz.2)).2⟩)
  have hw : Continuous w := φ.symm.continuous.comp
    ((continuous_fst.comp (φ.continuous.comp (hu.comp continuous_snd))).prodMk
      ((continuous_subtype_val.comp
        (c.continuous.comp (continuous_fst.prodMk (hd.comp continuous_snd)))).subtype_mk _))
  have hφw : ∀ tz, φ (w tz) = ((φ (u tz.2)).1, ⟨c (tz.1, d tz.2), hD'D (c (tz.1, d tz.2)).2⟩) :=
    fun tz ↦ φ.apply_symm_apply _
  have hwτ : ∀ tz, (w tz : Y) ∉ τ := fun tz h ↦ by
    rw [hφτ, hφw] at h
    exact tz.2.1.2 ((hφτ (u tz.2)).2 h)
  have hwP : ∀ tz, (w tz : Y) ∈ P := fun tz ↦ (hmemP _).2 (by
    rw [hφw]; exact ⟨(huQ tz.2).1, (c (tz.1, d tz.2)).2⟩)
  have hwb : ∀ z, g (w (1, z)) = b := fun z ↦ by
    rw [← hφg, hφw]
    simp
  have hw1 : ∀ z, g (u z) = b → w (1, z) = u z := fun z hz ↦ φ.injective (by
    rw [hφw]
    refine Prod.ext rfl (Subtype.ext ?_)
    change ((c (1, d z) : D') : Bs) = ((φ (u z)).2 : Bs)
    rw [c.apply_one, hφg, hz]
    rfl)
  let p : Bp ⟶ Ap := TopCat.ofHom
    ⟨fun z ↦ ⟨⟨⟨w (1, z), hwb z⟩, hwτ (1, z)⟩, hwP (1, z)⟩,
      (((continuous_subtype_val.comp (hw.comp (continuous_const.prodMk continuous_id))).subtype_mk
        _).subtype_mk _).subtype_mk _⟩
  let r := sliceRes τ (g ⁻¹' {b}) P
  let H : TopCat.Homotopy (𝟙 Bp) (p ≫ r) :=
    { toFun := fun tz ↦ ⟨⟨w tz, hwτ tz⟩, hwP tz⟩
      continuous_toFun := ((continuous_subtype_val.comp hw).subtype_mk _).subtype_mk _
      map_zero_left := fun z ↦ by
        apply Subtype.ext
        apply Subtype.ext
        change ((φ.symm _ : U') : Y) = z.1.1
        rw [c.apply_zero]
        change ((φ.symm (φ (u z)) : U') : Y) = z.1.1
        rw [φ.symm_apply_apply]
      map_one_left := fun z ↦ rfl }
  have hrp : r ≫ p = 𝟙 Ap := by
    ext a
    change ((w (1, r a)) : Y) = a.1.1.1
    rw [hw1 (r a) a.1.1.2]
    rfl
  refine ⟨⟨rationalCohomologyMap p q, ?_, ?_⟩⟩
  · rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_eq_of_homotopy H,
      rationalCohomologyMap_id]
  · rw [← rationalCohomologyMap_comp, hrp, rationalCohomologyMap_id]

end Slice

/-- **Punctured slice germs.** Let `f : Z ⟶ X` be proper and surjective, an isomorphism over
the complement `U` of a smooth closed subscheme `iT : T ⟶ X`, and `h : X ⟶ B` a morphism to a
smooth complex curve with `T ⟶ B` finite étale. Suppose an open `W ⊇ f⁻¹(T)` of `Z` is smooth,
`E ∩ W = (f⁻¹T)_red ∩ W` is the snc divisor `∑_{E_i ∈ s} E_i`, and every intersection
`⋂_{i ∈ J} E_i` (including `W` itself) is smooth over `B`. Then at `x ∈ T(ℂ)` over `b ∈ B(ℂ)`:

* there are neighbourhoods `U'` of `x` in `X^an`, `U₀` of `x` in the slice `X_b^an` and `D` of
  `b` in `B^an`, and a homeomorphism `φ : U' ≃ₜ U₀ × D` over `B^an`, the identity on the slice,
  with `φ x = (x, b)` and `φ (T^an ∩ U') = {x} × D`;
* for every `q`, there is an isomorphism `(R^q j_* ℚ)_x ≅ (R^q j_{b*} ℚ)_x` sending the germ of a
  class `α ∈ H^q(j⁻¹ V; ℚ)` to the germ of its restriction to `j_b⁻¹(V ∩ X_b^an)`. -/
@[mmp "lem_mmp_relative_snc_punctured_slice_germs"]
public theorem exists_homeomorph_prod_and_stalk_iso_of_relativeSNC
    {Z X B T : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [IsSeparated sX] [QuasiCompact sX]
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB]
    [Smooth sB] [SmoothOfRelativeDimension 1 sB]
    (f : Z ⟶ X) [IsProper f] [Surjective f] [IsSeparated (f ≫ sX)] [QuasiCompact (f ≫ sX)]
    (iT : T ⟶ X) [IsClosedImmersion iT] [Smooth (iT ≫ sX)]
    (U : X.Opens) (hU : (U : Set X) = (Set.range iT.base)ᶜ) [IsIso (f ∣_ U)]
    (h : X ⟶ B) (hh : h ≫ sB = sX) [IsFinite (iT ≫ h)] [Etale (iT ≫ h)]
    (hE : ∃ (W : Z.Opens) (s : Finset (Mori.PrimeDivisor W)),
      f.base ⁻¹' Set.range iT.base ⊆ W ∧ Smooth (W.ι ≫ f ≫ sX) ∧
      (⋃ E ∈ s, (E.support : Set W)) = W.ι.base ⁻¹' (f.base ⁻¹' Set.range iT.base) ∧
      Mori.DivisorWithCoeffs.IsSNC (W.ι ≫ f ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)) ∧
      ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ W.ι ≫ f ≫ h))
    (b : ComplexPoints sB) (x : ComplexPoints sX)
    (hxT : x ∈ Set.range (realize iT rfl)) (hxb : realize h hh x = b) :
    let τ : Set (ComplexPoints sX) := Set.range (realize iT rfl)
    let F : Set (ComplexPoints sX) := realize h hh ⁻¹' {b}
    let j : TopCat.of ↥τᶜ ⟶ analyticSpace sX :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let jb : TopCat.of ↥((Subtype.val : F → ComplexPoints sX) ⁻¹' τ)ᶜ ⟶ TopCat.of F :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let slice : Opens (analyticSpace sX) → Opens (TopCat.of F) := fun V ↦
      ⟨Subtype.val ⁻¹' (V : Set (ComplexPoints sX)), V.isOpen.preimage continuous_subtype_val⟩
    let r : ∀ V, preimageSpace jb (slice V) ⟶ preimageSpace j V := fun V ↦
      TopCat.ofHom ⟨fun y ↦ ⟨⟨y.1.1.1, y.1.2⟩, y.2⟩,
        ((continuous_subtype_val.comp (continuous_subtype_val.comp
          continuous_subtype_val)).subtype_mk _).subtype_mk _⟩
    (∃ (U' : Opens (analyticSpace sX)) (U₀ : Opens (TopCat.of F))
        (D : Opens (analyticSpace sB)) (hxU : x ∈ U') (hx₀ : ⟨x, hxb⟩ ∈ U₀) (hbD : b ∈ D)
        (φ : U' ≃ₜ U₀ × D),
      φ ⟨x, hxU⟩ = (⟨⟨x, hxb⟩, hx₀⟩, ⟨b, hbD⟩) ∧
      (∀ y : U', ((φ y).2 : ComplexPoints sB) = realize h hh y) ∧
      (∀ y : U', (y : ComplexPoints sX) ∈ τ ↔ (φ y).1 = ⟨⟨x, hxb⟩, hx₀⟩) ∧
      ∀ (y : U') (hy : realize h hh y = b), ((φ y).1 : F) = ⟨y, hy⟩) ∧
    ∀ q : ℕ, ∃ e : ((TopCat.Sheaf.forget _ _).obj (higherDirectImage j q)).stalk x ≅
        ((TopCat.Sheaf.forget _ _).obj (higherDirectImage jb q)).stalk ⟨x, hxb⟩,
      ∀ (V : Opens (analyticSpace sX)) (hxV : x ∈ V)
        (α : rationalCohomology (preimageSpace j V) q),
        e.hom (higherDirectImageGerm j q x hxV α) =
          higherDirectImageGerm jb q (V := slice V) ⟨x, hxb⟩ hxV
            (rationalCohomologyMap (r V) q α) := by
  intro τ F j jb slice r
  obtain ⟨Δ, hΔo, hbΔ, U', U₀, hU'o, hU₀o, hxU, hx₀, φ, hφ⟩ :=
    exists_homeomorph_prod_of_relativeSNC_of_isProper f iT U hU h hh hE b x hxT hxb
  refine ⟨⟨⟨U', hU'o⟩, ⟨U₀, hU₀o⟩, ⟨Δ, hΔo⟩, hxU, hx₀, hbΔ, φ, hφ⟩, fun q ↦ ?_⟩
  -- `B^an` has a basis of open contractible neighbourhoods (Fulton §19.1)
  have hloc : ∀ N ∈ 𝓝 b, ∃ D' : Set (ComplexPoints sB), IsOpen D' ∧ b ∈ D' ∧ D' ⊆ N ∧
      ContractibleSpace D' := by
    let : B.Over (Spec (.of ℂ)) := ⟨sB⟩
    have : LocallyOfFiniteType (B ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sB›
    have H := (MMP.UnderlyingSpace.hasOpenContractibleBasis B).of_homeomorph
      (homeomorphUnderlyingSpace (X := B)).symm
    intro N hN
    obtain ⟨D', ⟨hD', hbD', hc⟩, hD'N⟩ := (H b).mem_iff.1 hN
    exact ⟨D', hD', hbD', hD'N, hc⟩
  have hcof := isIso_sliceRes_of_homeomorph_prod (Y := analyticSpace sX) (Bs := analyticSpace sB)
    (U' := ⟨U', hU'o⟩) (U₀ := ⟨U₀, hU₀o⟩) (D := ⟨Δ, hΔo⟩) (realize h hh) τ b x hxb q hxU hx₀
    hbΔ φ hφ.1 hφ.2.1 hφ.2.2.1 hloc
  exact exists_stalk_iso_of_isIso_sliceRes (Y := analyticSpace sX) τ F x hxb q hcof

/-! ### Restricting simple normal crossing data to an open subscheme -/

section RestrictOpen

open MMP.Threefold.Mori.OpenRestriction

/-- The support of a prime divisor of an open subscheme `U` is the trace on `U` of the support of
its closure. -/
public theorem _root_.MMP.Mori.PrimeDivisor.preimage_support_primeDivisorMap {X : Scheme}
    (U : X.Opens) (E : Mori.PrimeDivisor U) :
    U.ι.base ⁻¹' (OpenWeilRestriction.primeDivisorMap U.ι E).support = E.support :=
  Set.ext fun v ↦ mem_support_primeDivisorMap_iff U.ι E v

/-- Every prime divisor of `X` is the closure of a prime divisor of the open subscheme `⊤`. -/
public theorem _root_.MMP.Mori.PrimeDivisor.primeDivisorMap_top_surjective (X : Scheme) :
    Function.Surjective (OpenWeilRestriction.primeDivisorMap (⊤ : X.Opens).ι) := fun E ↦
  (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ E).mpr ⟨⟨E.genericPoint, trivial⟩, rfl⟩

/-- If the closed subscheme of `I` is smooth over `Y`, then so is its trace on an open
subscheme. -/
public theorem _root_.MMP.Mori.smooth_comap_subschemeι {V X Y : Scheme} (j : V ⟶ X)
    [IsOpenImmersion j] (g : X ⟶ Y) (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ g)] :
    Smooth ((I.comap j).subschemeι ≫ j ≫ g) := by
  obtain ⟨k, _, hcomm, -⟩ := exists_openImmersion_comap_subscheme j I
  rw [← Category.assoc, hcomm, Category.assoc]
  infer_instance

end RestrictOpen

/-- The support of the reduced divisor `∑_{E ∈ s} E` is `s`. -/
private lemma support_sum_single_one {α : Type*} [DecidableEq α] (s : Finset α) :
    (∑ a ∈ s, Finsupp.single a (1 : ℤ)).support = s := by
  ext a
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- **Punctured slice germs, for snc data on all of `Z`.** The form of
`exists_homeomorph_prod_and_stalk_iso_of_relativeSNC` in which `Z` itself is smooth over `B`,
`E = (f⁻¹T)_red` is the snc divisor `∑_{E_i ∈ s} E_i` on `Z`, and every nonempty intersection
`⋂_{i ∈ J} E_i` is smooth over `B`. -/
public theorem exists_homeomorph_prod_and_stalk_iso_of_isSNC
    {Z X B T : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [IsSeparated sX] [QuasiCompact sX]
    [LocallyOfFiniteType sB] [IsSeparated sB] [QuasiCompact sB]
    [Smooth sB] [SmoothOfRelativeDimension 1 sB]
    (f : Z ⟶ X) [IsProper f] [Surjective f] [IsSeparated (f ≫ sX)] [QuasiCompact (f ≫ sX)]
    (iT : T ⟶ X) [IsClosedImmersion iT] [Smooth (iT ≫ sX)]
    (U : X.Opens) (hU : (U : Set X) = (Set.range iT.base)ᶜ) [IsIso (f ∣_ U)]
    (h : X ⟶ B) (hh : h ≫ sB = sX) [IsFinite (iT ≫ h)] [Etale (iT ≫ h)]
    (hZB : Smooth (f ≫ h)) (s : Finset (Mori.PrimeDivisor Z))
    (hs : (⋃ E ∈ s, (E.support : Set Z)) = f.base ⁻¹' Set.range iT.base)
    (hsnc : Mori.DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, J.Nonempty → Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ f ≫ h))
    (b : ComplexPoints sB) (x : ComplexPoints sX)
    (hxT : x ∈ Set.range (realize iT rfl)) (hxb : realize h hh x = b) :
    let τ : Set (ComplexPoints sX) := Set.range (realize iT rfl)
    let F : Set (ComplexPoints sX) := realize h hh ⁻¹' {b}
    let j : TopCat.of ↥τᶜ ⟶ analyticSpace sX :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let jb : TopCat.of ↥((Subtype.val : F → ComplexPoints sX) ⁻¹' τ)ᶜ ⟶ TopCat.of F :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let slice : Opens (analyticSpace sX) → Opens (TopCat.of F) := fun V ↦
      ⟨Subtype.val ⁻¹' (V : Set (ComplexPoints sX)), V.isOpen.preimage continuous_subtype_val⟩
    let r : ∀ V, preimageSpace jb (slice V) ⟶ preimageSpace j V := fun V ↦
      TopCat.ofHom ⟨fun y ↦ ⟨⟨y.1.1.1, y.1.2⟩, y.2⟩,
        ((continuous_subtype_val.comp (continuous_subtype_val.comp
          continuous_subtype_val)).subtype_mk _).subtype_mk _⟩
    (∃ (U' : Opens (analyticSpace sX)) (U₀ : Opens (TopCat.of F))
        (D : Opens (analyticSpace sB)) (hxU : x ∈ U') (hx₀ : ⟨x, hxb⟩ ∈ U₀) (hbD : b ∈ D)
        (φ : U' ≃ₜ U₀ × D),
      φ ⟨x, hxU⟩ = (⟨⟨x, hxb⟩, hx₀⟩, ⟨b, hbD⟩) ∧
      (∀ y : U', ((φ y).2 : ComplexPoints sB) = realize h hh y) ∧
      (∀ y : U', (y : ComplexPoints sX) ∈ τ ↔ (φ y).1 = ⟨⟨x, hxb⟩, hx₀⟩) ∧
      ∀ (y : U') (hy : realize h hh y = b), ((φ y).1 : F) = ⟨y, hy⟩) ∧
    ∀ q : ℕ, ∃ e : ((TopCat.Sheaf.forget _ _).obj (higherDirectImage j q)).stalk x ≅
        ((TopCat.Sheaf.forget _ _).obj (higherDirectImage jb q)).stalk ⟨x, hxb⟩,
      ∀ (V : Opens (analyticSpace sX)) (hxV : x ∈ V)
        (α : rationalCohomology (preimageSpace j V) q),
        e.hom (higherDirectImageGerm j q x hxV α) =
          higherDirectImageGerm jb q (V := slice V) ⟨x, hxb⟩ hxV
            (rationalCohomologyMap (r V) q α) := by
  classical
  refine exists_homeomorph_prod_and_stalk_iso_of_relativeSNC f iT U hU h hh ?_ b x hxT hxb
  -- transport the data along `⊤ ↪ Z`
  let W : Z.Opens := ⊤
  let p := OpenWeilRestriction.primeDivisorMap W.ι
  have hp : Function.Injective p := OpenWeilRestriction.primeDivisorMap_injective _
  let s' : Finset (Mori.PrimeDivisor W) := s.preimage p hp.injOn
  have hs' : s'.image p = s := by
    ext E
    refine ⟨fun hE ↦ ?_, fun hE ↦ ?_⟩
    · obtain ⟨E', hE', rfl⟩ := Finset.mem_image.mp hE
      exact Finset.mem_preimage.mp hE'
    · obtain ⟨E', rfl⟩ := Mori.PrimeDivisor.primeDivisorMap_top_surjective Z E
      exact Finset.mem_image_of_mem _ (Finset.mem_preimage.mpr hE)
  have : Smooth (f ≫ sX) := by rw [← hh, ← Category.assoc]; infer_instance
  refine ⟨W, s', fun _ _ ↦ trivial, inferInstance, ?_, ?_, fun J' hJ' ↦ ?_⟩
  · rw [← hs, Set.preimage_iUnion₂, ← hs', Finset.set_biUnion_finset_image]
    exact Set.iUnion₂_congr fun E' _ ↦
      (Mori.PrimeDivisor.preimage_support_primeDivisorMap W E').symm
  · refine (Mori.DivisorWithCoeffs.isSNC_iff_of_support_eq ?_).mp (hsnc.restrictOpen W)
    change (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support.preimage p hp.injOn = _
    rw [support_sum_single_one, support_sum_single_one]
  · have hI : (⨆ E' ∈ J', E'.idealSheaf) = (⨆ E ∈ J'.image p, E.idealSheaf).comap W.ι := by
      rw [(Scheme.IdealSheafData.map_gc W.ι).l_iSup₂, Finset.iSup_finset_image]
      exact iSup_congr fun E' ↦ iSup_congr fun _ ↦
        (Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap W.ι E').symm
    rcases J'.eq_empty_or_nonempty with rfl | hne
    · rw [show (⨆ E ∈ (∅ : Finset (Mori.PrimeDivisor W)), E.idealSheaf) = ⊥ by simp]
      infer_instance
    · have := hstr _ (hs' ▸ Finset.image_subset_image hJ') (hne.image p)
      rw [hI]
      exact Mori.smooth_comap_subschemeι W.ι (f ≫ h) _

end MMP.Fourfold

end

/-! ### The rational splitting along a smooth-centre blowup -/

section SmoothBlowupSplitting

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open MMP.Analytic.ComplexPoints MMP.Fourfold

attribute [local instance] HasDerivedCategory.standard

namespace MMP.Conductor

section Helpers

open MMP.Analytic

attribute [local instance] pushforward_additive pushforward_preservesInjectiveObjects

/-- A morphism in `D⁺` of sheaves of `ℚ`-vector spaces is an isomorphism as soon as it induces
isomorphisms on the stalks of all cohomology sheaves. -/
private theorem isIso_of_forall_isIso_stalk_homology {X : TopCat.{0}}
    {K L : DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X)} (f : K ⟶ L)
    (h : ∀ (n : ℤ) (x : X), IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map f).hom)) : IsIso f := by
  have : IsIso (DerivedCategory.Plus.ι.map f) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
        ((DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Plus.ι.map f)).hom) := h n
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      ((DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Plus.ι.map f))
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι f

section SplittingCriterion

variable {X : TopCat.{0}}

private lemma isIso_of_ne_zero {S T : ModuleCat.{0} ℚ} (f : S ⟶ T) (hS : Module.rank ℚ S ≤ 1)
    (hT : Module.rank ℚ T ≤ 1) (hf : f ≠ 0) : IsIso f := by
  obtain ⟨s, hs⟩ : ∃ s, f s ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (by ext s; simpa using h s)
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.1 hS
  obtain ⟨w₀, hw₀⟩ := rank_le_one_iff.1 hT
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨r, rfl⟩ := hv₀ v
    obtain ⟨r', rfl⟩ := hv₀ s
    have h1 : f v₀ ≠ 0 := fun h => hs (by simp [map_smul, h])
    rw [map_smul] at hv
    rcases smul_eq_zero.1 hv with h | h
    · simp [h]
    · exact absurd h h1
  · intro w
    obtain ⟨r, rfl⟩ := hw₀ w
    obtain ⟨r₁, hr₁⟩ := hw₀ (f s)
    have hr₁0 : r₁ ≠ 0 := by rintro rfl; exact hs (by rw [← hr₁, zero_smul])
    refine ⟨(r / r₁) • s, ?_⟩
    rw [map_smul, ← hr₁, smul_smul, div_mul_cancel₀ _ hr₁0]

/-- The stalk at `x` of the `n`-th cohomology sheaf, as a functor on `D⁺`. -/
private noncomputable abbrev stalkH (n : ℤ) (x : X) :
    DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ⥤ ModuleCat.{0} ℚ :=
  DerivedCategory.Plus.homologyFunctor _ n ⋙ TopCat.Sheaf.forget _ X ⋙
    TopCat.Presheaf.stalkFunctor _ x

/-- The `n`-th cohomology of the image in `D⁺` of a single complex. -/
private noncomputable def homologySingleIso (n k : ℤ) (M : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    (DerivedCategory.Plus.homologyFunctor _ n).obj (DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.singleFunctor _ k).obj M)) ≅
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj M).homology n :=
  (DerivedCategory.homologyFunctor _ n).mapIso
      ((DerivedCategory.Plus.QhCompιIsoιCompQh _).app _) ≪≫
    (DerivedCategory.homologyFunctorFactorsh _ n).app _ ≪≫
    (HomotopyCategory.homologyFunctor _ _ n).mapIso
      ((HomotopyCategory.Plus.singleFunctorCompιIso _ k).app M) ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ n).app _

private lemma isZero_stalkH_single {n k : ℤ} (h : n ≠ k) (M : TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    (x : X) : IsZero ((stalkH n x).obj (DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.singleFunctor _ k).obj M))) := by
  have h0 : IsZero ((DerivedCategory.Plus.homologyFunctor _ n).obj (DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.singleFunctor _ k).obj M))) :=
    (HomologicalComplex.isZero_single_obj_homology _ k M n h).of_iso (homologySingleIso n k M)
  exact (TopCat.Presheaf.stalkFunctor _ x).map_isZero ((TopCat.Sheaf.forget _ X).map_isZero h0)

/-- The stalk of the `k`-th cohomology sheaf of a sheaf placed in degree `k`. -/
private noncomputable def stalkHSingleIso (k : ℤ) (M : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (x : X) :
    (stalkH k x).obj (DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.singleFunctor _ k).obj M)) ≅ M.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor _ x).mapIso ((TopCat.Sheaf.forget _ X).mapIso
    (homologySingleIso k k M ≪≫ HomologicalComplex.singleObjHomologySelfIso _ k M))

private lemma rank_stalkH_single (k : ℤ) (M : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (x : X) :
    Module.rank ℚ ((stalkH k x).obj (DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.singleFunctor _ k).obj M))) =
      Module.rank ℚ (M.presheaf.stalk x) :=
  (stalkHSingleIso k M x).toLinearEquiv.rank_eq

/-- A cocycle `z : B ⟶ K^k` composes to zero with every differential out of degree `k`. -/
private lemma comp_d_eq_zero_of_rel {C : Type*} [Category C] [HasZeroMorphisms C]
    {K : CochainComplex C ℤ} {B : C} {k : ℤ} {z : B ⟶ K.X k} (hz : z ≫ K.d k (k + 1) = 0)
    (j : ℤ) (hj : (ComplexShape.up ℤ).Rel k j) : z ≫ K.d k j = 0 := by
  obtain rfl : k + 1 = j := hj
  exact hz

/-- The morphism `B[k] ⟶ C` of the bounded below homotopy category given by a cocycle
`z : B ⟶ C^k`. -/
private noncomputable def singleHomOfCocycle {k : ℤ} {B : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (C : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X))
    (z : B ⟶ C.obj.X k) (hz : z ≫ C.obj.d k (k + 1) = 0) :
    (HomotopyCategory.Plus.singleFunctor _ k).obj B ⟶ (HomotopyCategory.Plus.quotient _).obj C :=
  (HomotopyCategory.Plus.ι _).preimage ((HomotopyCategory.quotient _ _).map
    (HomologicalComplex.mkHomFromSingle z (comp_d_eq_zero_of_rel hz)))

private lemma singleFunctor_map_comp_singleHomOfCocycle {k : ℤ}
    {A B : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (p : A ⟶ B) (C : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X))
    (z : B ⟶ C.obj.X k) (hz : z ≫ C.obj.d k (k + 1) = 0) (hpz : (p ≫ z) ≫ C.obj.d k (k + 1) = 0) :
    (HomotopyCategory.Plus.singleFunctor _ k).map p ≫ singleHomOfCocycle C z hz =
      singleHomOfCocycle C (p ≫ z) hpz := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  rw [Functor.map_comp]
  dsimp only [singleHomOfCocycle]
  erw [Functor.map_preimage, Functor.map_preimage]
  change (HomotopyCategory.quotient _ _).map
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).map p) ≫ _ = _
  refine ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans ?_
  congr 1
  ext
  simp [HomologicalComplex.mkHomFromSingle, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleObjXSelf]

private lemma hom_eq_zero_of_stalk {A B : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (g : A ⟶ B)
    (h : ∀ x : X, (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map g.hom = 0) : g = 0 := by
  apply Sheaf.hom_ext
  ext U s
  refine TopCat.Presheaf.section_ext B U.unop _ _ (fun x hx => ?_)
  have h1 := TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x hx g.hom s
  rw [h x] at h1
  have h3 : (ModuleCat.Hom.hom (NatTrans.app (0 : A.obj ⟶ B.obj) U)) s = 0 := rfl
  refine h1.symm.trans ?_
  change (0 : _) = _
  erw [h3, map_zero]
  rfl

private lemma stalk_map_comp {A B C : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (f : A ⟶ B) (g : B ⟶ C)
    (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map (f ≫ g).hom =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map f.hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map g.hom :=
  (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map_comp f.hom g.hom

private lemma epi_of_stalk {A B : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (p : A ⟶ B) (T : Set X)
    (hpT : ∀ x ∈ T, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map p.hom))
    (hpU : ∀ x ∉ T, Subsingleton (B.presheaf.stalk x)) : Epi p := by
  have h : ∀ x : X, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map p.hom) := by
    intro x
    by_cases hx : x ∈ T
    · have := hpT x hx
      exact ((ConcreteCategory.isIso_iff_bijective _).1 this).2
    · have hs := hpU x hx
      intro y
      exact ⟨0, @Subsingleton.elim _ hs _ _⟩
  have h1 : TopCat.Presheaf.IsLocallySurjective p.hom :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).2 h
  have h2 : Sheaf.IsLocallySurjective p := h1
  exact (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{0} ℚ) p).1 h2

/-- A morphism out of `A` vanishing on the stalks off `T` factors through a morphism `p : A ⟶ B`
which is invertible on the stalks at `T` and lands in a sheaf with zero stalks off `T`. -/
private lemma exists_factor_of_stalk {A B G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (p : A ⟶ B)
    (T : Set X)
    (hpT : ∀ x ∈ T, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map p.hom))
    (hpU : ∀ x ∉ T, Subsingleton (B.presheaf.stalk x)) (f : A ⟶ G)
    (hf : ∀ x ∉ T, (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map f.hom = 0) :
    ∃ f' : B ⟶ G, p ≫ f' = f := by
  have := epi_of_stalk p T hpT hpU
  refine ⟨Abelian.epiDesc p f (hom_eq_zero_of_stalk _ fun x => ?_), Abelian.comp_epiDesc _ _ _⟩
  rw [stalk_map_comp]
  by_cases hx : x ∈ T
  · have := hpT x hx
    have h0 : (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map (kernel.ι p).hom = 0 := by
      rw [← cancel_mono ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map p.hom),
        ← stalk_map_comp, kernel.condition, zero_comp]
      exact (TopCat.Presheaf.stalkFunctor _ x).map_zero _ _
    rw [h0, zero_comp]
  · rw [hf x hx, comp_zero]

section Biprod

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (G : C ⥤ D) [G.Additive] [HasFiniteBiproducts C]

private lemma isZero_map_biproduct {m : ℕ} (B : Fin m → C) (hB : ∀ j, IsZero (G.obj (B j))) :
    IsZero (G.obj (⨁ B)) := by
  rw [IsZero.iff_id_eq_zero, ← G.map_id, ← biproduct.total (f := B), G.map_sum]
  exact Finset.sum_eq_zero fun j _ => by
    rw [G.map_comp, (hB j).eq_of_tgt (G.map (biproduct.π B j)) 0, zero_comp]

private lemma isZero_map_biprod {A W : C} (hA : IsZero (G.obj A)) (hW : IsZero (G.obj W)) :
    IsZero (G.obj (A ⊞ W)) := by
  rw [IsZero.iff_id_eq_zero, ← G.map_id, ← biprod.total (X := A) (Y := W), G.map_add,
    G.map_comp, G.map_comp, hA.eq_of_tgt (G.map biprod.fst) 0, hW.eq_of_tgt (G.map biprod.snd) 0,
    zero_comp, zero_comp, add_zero]

private lemma isIso_map_inl {A W : C} (hW : IsZero (G.obj W)) :
    IsIso (G.map (biprod.inl : A ⟶ A ⊞ W)) := by
  refine ⟨⟨G.map biprod.fst, ?_, ?_⟩⟩
  · rw [← G.map_comp, biprod.inl_fst, G.map_id]
  · rw [← G.map_comp, ← sub_eq_iff_eq_add.2 (biprod.total (X := A) (Y := W)).symm, G.map_sub,
      G.map_id, G.map_comp, hW.eq_of_tgt (G.map biprod.snd) 0, zero_comp, sub_zero]

private lemma isIso_map_ι_inr {m : ℕ} {A : C} (B : Fin m → C) (i : Fin m) (hA : IsZero (G.obj A))
    (hB : ∀ j, j ≠ i → IsZero (G.obj (B j))) :
    IsIso (G.map (biproduct.ι B i ≫ (biprod.inr : ⨁ B ⟶ A ⊞ ⨁ B))) := by
  refine ⟨⟨G.map (biprod.snd ≫ biproduct.π B i), ?_, ?_⟩⟩
  · rw [← G.map_comp]; simp
  · rw [← G.map_comp, ← G.map_id]
    have hsnd : (biprod.snd : A ⊞ ⨁ B ⟶ ⨁ B) ≫ (biprod.inr : ⨁ B ⟶ A ⊞ ⨁ B) =
        ∑ j, (biprod.snd ≫ biproduct.π B j) ≫
          (biproduct.ι B j ≫ (biprod.inr : ⨁ B ⟶ A ⊞ ⨁ B)) := by
      calc (biprod.snd : A ⊞ ⨁ B ⟶ ⨁ B) ≫ (biprod.inr : ⨁ B ⟶ A ⊞ ⨁ B)
          = biprod.snd ≫ 𝟙 _ ≫ biprod.inr := by simp
        _ = biprod.snd ≫ (∑ j, biproduct.π B j ≫ biproduct.ι B j) ≫ biprod.inr := by
          rw [biproduct.total]
        _ = _ := by rw [Preadditive.sum_comp, Preadditive.comp_sum]; simp [Category.assoc]
    rw [← biprod.total (X := A) (Y := ⨁ B), hsnd, G.map_add, G.map_sum, G.map_comp biprod.fst,
      hA.eq_of_tgt (G.map biprod.fst) 0, zero_comp, zero_add, Finset.sum_eq_single i]
    · intro j _ hj
      rw [G.map_comp, (hB j hj).eq_of_tgt (G.map (biprod.snd ≫ biproduct.π B j)) 0, zero_comp]
    · intro h; exact absurd (Finset.mem_univ i) h

private lemma isIso_map_desc_of_inl {m : ℕ} {A K : C} {B : Fin m → C} (u : A ⟶ K) (φ : ∀ j, B j ⟶ K)
    (hB : ∀ j, IsZero (G.obj (B j))) (hu : IsIso (G.map u)) :
    IsIso (G.map (biprod.desc u (biproduct.desc φ))) := by
  have := isIso_map_inl G (A := A) (isZero_map_biproduct G B hB)
  have : IsIso (G.map biprod.inl ≫ G.map (biprod.desc u (biproduct.desc φ))) := by
    rw [← G.map_comp, biprod.inl_desc]; exact hu
  exact IsIso.of_isIso_comp_left (G.map biprod.inl) _

private lemma isIso_map_desc_of_ι {m : ℕ} {A K : C} {B : Fin m → C} (u : A ⟶ K) (φ : ∀ j, B j ⟶ K)
    (i : Fin m) (hA : IsZero (G.obj A)) (hB : ∀ j, j ≠ i → IsZero (G.obj (B j)))
    (hφ : IsIso (G.map (φ i))) :
    IsIso (G.map (biprod.desc u (biproduct.desc φ))) := by
  have := isIso_map_ι_inr G B i hA hB
  have : IsIso (G.map (biproduct.ι B i ≫ (biprod.inr : ⨁ B ⟶ A ⊞ ⨁ B)) ≫
      G.map (biprod.desc u (biproduct.desc φ))) := by
    rw [← G.map_comp, Category.assoc, biprod.inr_desc, biproduct.ι_desc]; exact hφ
  exact IsIso.of_isIso_comp_left (G.map (biproduct.ι B i ≫ (biprod.inr : ⨁ B ⟶ A ⊞ ⨁ B))) _

private lemma isIso_map_desc_of_isZero {m : ℕ} {A K : C} {B : Fin m → C}
    (u : A ⟶ K)
    (φ : ∀ j, B j ⟶ K) (hA : IsZero (G.obj A)) (hB : ∀ j, IsZero (G.obj (B j)))
    (hK : IsZero (G.obj K)) : IsIso (G.map (biprod.desc u (biproduct.desc φ))) :=
  (isZero_map_biprod G hA (isZero_map_biproduct G B hB)).isIso hK _

end Biprod

/-- **A criterion for the splitting.** Let `u : QV[0] ⟶ K` and let `C` be a bounded below
complex modelling `K`. Suppose that the stalks of the cohomology sheaves of `K` have rank at most
one in degree `0` and in the degrees `2(a+1)` at points of `T`, and vanish otherwise; that
`p : QV ⟶ iQ` is invertible on the stalks at `T` and `iQ` has zero stalks off `T`; and that there
are cocycles `ζ a : QV ⟶ C^{2(a+1)}`, zero on the stalks off `T`, whose induced maps are nonzero on
the stalks of cohomology at `T`, as is `u` everywhere in degree `0`. Then the `ζ a` factor through
`p`, and together with `u` they give a morphism which is invertible on all stalks of all
cohomology sheaves. -/
private theorem exists_isIso_stalk_homology_biprod_desc (m : ℕ) (T : Set X)
    (QV iQ : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (p : QV ⟶ iQ)
    (K : DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X))
    (u : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor _ 0).obj QV) ⟶ K)
    (C : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X))
    (M : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj C) ≅ K)
    (hQV : ∀ x, Module.rank ℚ (QV.presheaf.stalk x) ≤ 1)
    (hpT : ∀ x ∈ T, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map p.hom))
    (hpU : ∀ x ∉ T, Subsingleton (iQ.presheaf.stalk x))
    (hK0 : ∀ x, Module.rank ℚ ((stalkH 0 x).obj K) ≤ 1)
    (hKT : ∀ x ∈ T, ∀ a : Fin m, Module.rank ℚ ((stalkH (2 * (a + 1 : ℕ)) x).obj K) ≤ 1)
    (hKz : ∀ (n : ℤ) (x : X), n ≠ 0 → (∀ a : Fin m, x ∈ T → n ≠ 2 * (a + 1 : ℕ)) →
      IsZero ((stalkH n x).obj K))
    (hu : ∀ x, (stalkH 0 x).map u ≠ 0)
    (ζ : ∀ a : Fin m, QV ⟶ C.obj.X (2 * (a + 1 : ℕ)))
    (hζd : ∀ a, ζ a ≫ C.obj.d (2 * (a + 1 : ℕ)) (2 * (a + 1 : ℕ) + 1) = 0)
    (hζU : ∀ a : Fin m, ∀ x ∉ T,
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map (ζ a).hom = 0)
    (hζT : ∀ a : Fin m, ∀ x ∈ T, (stalkH (2 * (a + 1 : ℕ)) x).map
      (DerivedCategory.Plus.Qh.map (singleHomOfCocycle C (ζ a) (hζd a)) ≫ M.hom) ≠ 0) :
    ∃ φ : ∀ a : Fin m, DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor _ (2 * (a + 1 : ℕ))).obj iQ) ⟶ K,
      ∀ (n : ℤ) (x : X), IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          (biprod.desc u (biproduct.desc φ))).hom) := by
  have hepi := epi_of_stalk p T hpT hpU
  choose ζ' hζ' using fun a => exists_factor_of_stalk p T hpT hpU (ζ a) (hζU a)
  have hζ'd : ∀ a, ζ' a ≫ C.obj.d (2 * (a + 1 : ℕ)) (2 * (a + 1 : ℕ) + 1) = 0 := fun a => by
    rw [← cancel_epi p, ← Category.assoc, hζ' a, hζd a, comp_zero]
  let φ : ∀ a : Fin m, DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.singleFunctor _ (2 * (a + 1 : ℕ))).obj iQ) ⟶ K := fun a =>
    DerivedCategory.Plus.Qh.map (singleHomOfCocycle C (ζ' a) (hζ'd a)) ≫ M.hom
  have hφ : ∀ a, DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor _ _).map p) ≫
      φ a = DerivedCategory.Plus.Qh.map (singleHomOfCocycle C (ζ a) (hζd a)) ≫ M.hom := by
    intro a
    have h := singleFunctor_map_comp_singleHomOfCocycle p C (ζ' a) (hζ'd a)
      (by rw [hζ' a]; exact hζd a)
    simp only [φ, ← Category.assoc, ← Functor.map_comp, h]
    congr 3
    exact hζ' a
  refine ⟨φ, fun n x => ?_⟩
  change IsIso ((stalkH n x).map (biprod.desc u (biproduct.desc φ)))
  -- the stalks of the summands
  have hiQ : ∀ x ∈ T, Module.rank ℚ (iQ.presheaf.stalk x) ≤ 1 := fun x hx => by
    have := hpT x hx
    exact ((asIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      p.hom)).toLinearEquiv.rank_eq).symm.le.trans (hQV x)
  have hdeg : ∀ a b : Fin m, (2 * (a + 1 : ℕ) : ℤ) = 2 * (b + 1 : ℕ) → a = b := fun a b h => by
    apply Fin.ext; omega
  by_cases hn0 : n = 0
  · subst hn0
    exact isIso_map_desc_of_inl (stalkH 0 x) u φ
      (fun a => isZero_stalkH_single (by omega) _ _)
      (isIso_of_ne_zero _ ((rank_stalkH_single 0 QV x).le.trans (hQV x)) (hK0 x) (hu x))
  · by_cases hact : ∃ a : Fin m, x ∈ T ∧ n = 2 * (a + 1 : ℕ)
    · obtain ⟨a, hxT, rfl⟩ := hact
      have hφa : (stalkH (2 * (a + 1 : ℕ)) x).map (φ a) ≠ 0 := by
        intro h
        apply hζT a x hxT
        rw [← hφ a, Functor.map_comp, h, comp_zero]
      exact isIso_map_desc_of_ι (stalkH (2 * (a + 1 : ℕ)) x) u φ a
        (isZero_stalkH_single hn0 QV x)
        (fun j hj => isZero_stalkH_single (fun h => hj (hdeg j a h.symm)) _ _)
        (isIso_of_ne_zero _ ((rank_stalkH_single _ iQ x).le.trans (hiQ x hxT)) (hKT x hxT a) hφa)
    · push Not at hact
      refine isIso_map_desc_of_isZero (stalkH n x) u φ (isZero_stalkH_single hn0 QV x)
        (fun a => ?_) (hKz n x hn0 fun a hx => hact a hx)
      by_cases hxT : x ∈ T
      · exact isZero_stalkH_single (hact a hxT) _ _
      · by_cases hna : n = 2 * (a + 1 : ℕ)
        · subst hna
          have := hpU x hxT
          exact (ModuleCat.isZero_of_subsingleton _).of_iso (stalkHSingleIso _ iQ x)
        · exact isZero_stalkH_single hna _ _

end SplittingCriterion

section FibreTest

open Opposite

/-- `cyclesMap φ` sends the cycle `K.cyclesMk x` to the cycle `L.cyclesMk (φ x)`. -/
private lemma cyclesMap_cyclesMk {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{0} ℚ) c} (φ : K ⟶ L) {i : ι}
    (x : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.d i j) x = 0) :
    (forget₂ (ModuleCat.{0} ℚ) Ab).map (HomologicalComplex.cyclesMap φ i) (K.cyclesMk x j hj hx) =
      L.cyclesMk ((forget₂ (ModuleCat.{0} ℚ) Ab).map (φ.f i) x) j hj (by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, φ.comm, Functor.map_comp,
          ConcreteCategory.comp_apply, hx, map_zero]) := by
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback
    ((forget₂ (ModuleCat.{0} ℚ) Ab).map (L.iCycles i)))
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, HomologicalComplex.cyclesMap_i,
    Functor.map_comp, ConcreteCategory.comp_apply, HomologicalComplex.i_cyclesMk,
    HomologicalComplex.i_cyclesMk]

private lemma sectionsTop_additive (Y : TopCat.{0}) :
    (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Y ⋙
      (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

private lemma sectionsTop_additive' {X : TopCat.{0}} (S : Set X) :
    (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (TopCat.of S) ⋙
      (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

attribute [local instance] sectionsTop_additive sectionsTop_additive'

private lemma cyclesMk_congr {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{0} ℚ) c)
    {i : ι} {x y : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X i)} (h : x = y) (j : ι)
    (hj : c.next i = j) (hx : (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.d i j) x = 0)
    (hy : (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.d i j) y = 0) :
    K.cyclesMk x j hj hx = K.cyclesMk y j hj hy := by
  subst h; rfl

variable {X X' : TopCat.{0}} (b : X' ⟶ X) (x : X)

/-- The fibre `b⁻¹(x)` and its inclusion. -/
private abbrev Fib : TopCat.{0} := TopCat.of (b ⁻¹' {x})

private abbrev fibι : Fib b x ⟶ X' := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

private lemma fib_preimage_eq_top (W : Opens X) (hW : x ∈ W) :
    (Opens.map (fibι b x)).obj ((Opens.map b).obj W) = ⊤ := by
  ext ⟨y, hy⟩
  simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Opens.coe_top, Set.mem_univ,
    iff_true]
  change b y ∈ W
  rw [show b y = x from hy]
  exact hW

/-- The restriction of a stalk of `b_* ι_* S` at `x` to the sections of `S` on the fibre. -/
private noncomputable def fibreStalkHom (S : TopCat.Sheaf (ModuleCat.{0} ℚ) (Fib b x)) :
    ((TopCat.Sheaf.pushforward _ b).obj
      ((TopCat.Sheaf.pushforward _ (fibι b x)).obj S)).presheaf.stalk x ⟶
      S.obj.obj (op ⊤) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ ((TopCat.Sheaf.pushforward _ b).obj
      ((TopCat.Sheaf.pushforward _ (fibι b x)).obj S)).presheaf)
    { pt := S.obj.obj (op ⊤)
      ι := {
        app := fun W => S.obj.map (homOfLE (fib_preimage_eq_top b x W.unop.1 W.unop.2).ge).op
        naturality := fun W W' f => by
          dsimp
          rw [Category.comp_id]
          exact (S.obj.map_comp _ _).symm.trans (congrArg _ (Subsingleton.elim _ _)) } }

@[reassoc]
private lemma germ_fibreStalkHom (S : TopCat.Sheaf (ModuleCat.{0} ℚ) (Fib b x)) (W : Opens X)
    (hW : x ∈ W) :
    ((TopCat.Sheaf.pushforward _ b).obj
      ((TopCat.Sheaf.pushforward _ (fibι b x)).obj S)).presheaf.germ
        W x hW ≫ fibreStalkHom b x S =
      S.obj.map (homOfLE (fib_preimage_eq_top b x W hW).ge).op :=
  colimit.ι_desc _ _

/-- `fibreStalkHom` as a natural transformation. -/
private noncomputable def fibreStalkNatTrans :
    TopCat.Sheaf.pushforward _ (fibι b x) ⋙ TopCat.Sheaf.pushforward _ b ⋙
        TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X ⋙ TopCat.Presheaf.stalkFunctor _ x ⟶
      TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (Fib b x) ⋙
        (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤) where
  app S := fibreStalkHom b x S
  naturality S S' φ := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro W hW
    dsimp
    erw [germ_fibreStalkHom_assoc, TopCat.Presheaf.stalkFunctor_map_germ_assoc,
      germ_fibreStalkHom]
    exact (φ.hom.naturality _).symm

/-- The restriction of the stalk complex at `x` of `b_* D` to the sections over the fibre, given a
map of complexes `ρ : D ⟶ ι_* I`. -/
private noncomputable def fibreStalkComplexHom
    {D : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X') ℤ}
    {I : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) (Fib b x)) ℤ}
    (ρ : D ⟶ ((TopCat.Sheaf.pushforward _ (fibι b x)).mapHomologicalComplex _).obj I) :
    ((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X ⋙
      TopCat.Presheaf.stalkFunctor _ x).mapHomologicalComplex _).obj
        (((TopCat.Sheaf.pushforward _ b).mapHomologicalComplex _).obj D) ⟶
      ((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (Fib b x) ⋙
        (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).mapHomologicalComplex _).obj I :=
  ((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X ⋙
    TopCat.Presheaf.stalkFunctor _ x).mapHomologicalComplex _).map
      (((TopCat.Sheaf.pushforward _ b).mapHomologicalComplex _).map ρ) ≫
    (NatTrans.mapHomologicalComplex (fibreStalkNatTrans b x) _).app I

private noncomputable abbrev stalkF (x : X) : TopCat.Sheaf (ModuleCat.{0} ℚ) X ⥤ ModuleCat.{0} ℚ :=
  TopCat.Sheaf.forget _ X ⋙ TopCat.Presheaf.stalkFunctor _ x

variable (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] in
private noncomputable def homologyQhNatIso (k : ℤ) :
    HomotopyCategory.Plus.quotient C ⋙ DerivedCategory.Plus.Qh ⋙
        DerivedCategory.Plus.homologyFunctor C k ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C _ k :=
  Functor.isoWhiskerLeft (HomotopyCategory.Plus.quotient C)
      (Functor.isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh C)
        (DerivedCategory.homologyFunctor C k) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.Plus.quotientCompιIso C) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι C)
      (Functor.isoWhiskerLeft (HomotopyCategory.quotient C _)
        (DerivedCategory.homologyFunctorFactorsh C k) ≪≫
        HomotopyCategory.homologyFunctorFactors C _ k)

/-- A morphism of bounded below complexes whose stalks at `x` are nonzero on `H^k` gives a
morphism in `D⁺` which is nonzero on the stalk at `x` of `H^k`. -/
private lemma stalkH_map_ne_zero_of_homologyMap {k : ℤ} {x : X}
    {E E' : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X)} (f : E ⟶ E')
    (hf : HomologicalComplex.homologyMap (((stalkF x).mapHomologicalComplex _).map f.hom) k ≠ 0) :
    (stalkH k x).map
      (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map f)) ≠ 0 := by
  intro h
  apply hf
  have hn := (homologyQhNatIso (TopCat.Sheaf (ModuleCat.{0} ℚ) X) k).hom.naturality f
  have h1 := congrArg (stalkF x).map hn
  simp only [Functor.map_comp] at h1
  have h2 := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ k).map f.hom) (stalkF x)
  change (stalkF x).map ((DerivedCategory.Plus.homologyFunctor _ k).map
    (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map f))) = 0 at h
  simp only [Functor.comp_map] at h1
  erw [h, zero_comp] at h1
  have h3 : (stalkF x).map (HomologicalComplex.homologyMap f.hom k) = 0 :=
    (((stalkF x).mapIso ((homologyQhNatIso _ k).app E)).cancel_iso_hom_left _ _).1
      (h1.symm.trans (comp_zero).symm)
  have h4 : HomologicalComplex.homologyMap (((stalkF x).mapHomologicalComplex _).map f.hom) k ≫
      ((E'.obj.sc k).mapHomologyIso (stalkF x)).hom = 0 :=
    h2.trans ((congrArg (_ ≫ ·) h3).trans comp_zero)
  exact (((E'.obj.sc k).mapHomologyIso (stalkF x)).cancel_iso_hom_right _ _).1
    (h4.trans zero_comp.symm)

/-- The single complex `A[k]` as a bounded below complex. -/
private noncomputable abbrev singlePlus (k : ℤ) (A : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X) :=
  ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj A, ⟨k, inferInstance⟩⟩

private lemma singleHomOfCocycle_eq {k : ℤ} {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (C : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X))
    (z : A ⟶ C.obj.X k) (hz : z ≫ C.obj.d k (k + 1) = 0) :
    singleHomOfCocycle C z hz = (HomotopyCategory.Plus.quotient _).map
      (ObjectProperty.homMk (HomologicalComplex.mkHomFromSingle z (comp_d_eq_zero_of_rel hz)) :
        singlePlus k A ⟶ C) := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  dsimp only [singleHomOfCocycle]
  erw [Functor.map_preimage]
  rfl

/-- **The fibre test.** Let `ζ : A ⟶ (b_* D)^k` be a cocycle and `ρ : D ⟶ ι_* I` a map of complexes
to a complex on the fibre `b⁻¹(x)`. If, for a global section `s` of `A`, the restriction to the
fibre
of `ζ(s)` has nonzero class in `H^k(Γ(b⁻¹(x), I))`, then the morphism `A[k] ⟶ b_* D` of `D⁺` is
nonzero on the stalk at `x` of `H^k`. -/
private theorem stalkH_map_singleHomOfCocycle_ne_zero
    (D : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) X'))
    {I : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) (Fib b x)) ℤ}
    (ρ : D.obj ⟶ ((TopCat.Sheaf.pushforward _ (fibι b x)).mapHomologicalComplex _).obj I)
    {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X} {k : ℤ}
    (ζ : A ⟶ ((TopCat.Sheaf.pushforward _ b).mapCochainComplexPlus.obj D).obj.X k)
    (hζ : ζ ≫ ((TopCat.Sheaf.pushforward _ b).mapCochainComplexPlus.obj D).obj.d k (k + 1) = 0)
    (s : ToType (A.obj.obj (op ⊤)))
    (hne : ∀ hy, (forget₂ (ModuleCat.{0} ℚ) Ab).map
      ((((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (Fib b x) ⋙
        (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).mapHomologicalComplex _).obj I).homologyπ k)
        (HomologicalComplex.cyclesMk _ ((fibreStalkComplexHom b x ρ).f k
          ((TopCat.Presheaf.stalkFunctor _ x).map ζ.hom (A.presheaf.germ ⊤ x trivial s)))
          (k + 1) (by simp) hy) ≠ 0) :
    (stalkH k x).map (DerivedCategory.Plus.Qh.map (singleHomOfCocycle _ ζ hζ)) ≠ 0 := by
  rw [singleHomOfCocycle_eq]
  apply stalkH_map_ne_zero_of_homologyMap
  intro h0
  let g := ((stalkF x).mapHomologicalComplex _).map
    (ObjectProperty.homMk (HomologicalComplex.mkHomFromSingle ζ (comp_d_eq_zero_of_rel hζ)) :
        singlePlus k A ⟶ (TopCat.Sheaf.pushforward _ b).mapCochainComplexPlus.obj D).hom ≫
      fibreStalkComplexHom b x ρ
  have h1 : HomologicalComplex.homologyMap g k = 0 :=
    (HomologicalComplex.homologyMap_comp _ _ k).trans ((congrArg (· ≫ _) h0).trans zero_comp)
  let K := ((stalkF x).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj A)
  let x₀ : ToType (K.X k) :=
    (stalkF x).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k A).inv
      (A.presheaf.germ ⊤ x trivial s)
  have hx₀ : (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.d k (k + 1)) x₀ = 0 := by
    have : K.d k (k + 1) = 0 := by
      change (stalkF x).map
        (((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj A).d k (k + 1)) = 0
      rw [HomologicalComplex.single_obj_d, Functor.map_zero]
    rw [this, Functor.map_zero]
    rfl
  have hg : g.f k x₀ = (fibreStalkComplexHom b x ρ).f k
      ((TopCat.Presheaf.stalkFunctor _ x).map ζ.hom (A.presheaf.germ ⊤ x trivial s)) := by
    change (fibreStalkComplexHom b x ρ).f k ((stalkF x).map
      ((HomologicalComplex.mkHomFromSingle ζ (comp_d_eq_zero_of_rel hζ)).f k) x₀) = _
    rw [HomologicalComplex.mkHomFromSingle_f]
    congr 1
    change ((stalkF x).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k A).inv ≫
      (stalkF x).map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k A).hom ≫ ζ)) _ = _
    rw [← Functor.map_comp, Iso.inv_hom_id_assoc]
    rfl
  have key := congrArg (fun φ => (forget₂ (ModuleCat.{0} ℚ) Ab).map φ
    (K.cyclesMk x₀ (k + 1) (by simp) hx₀)) (HomologicalComplex.homologyπ_naturality g k)
  simp only [Functor.map_comp, ConcreteCategory.comp_apply, h1, Functor.map_zero] at key
  rw [cyclesMap_cyclesMk] at key
  let L := (((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (Fib b x) ⋙
    (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).mapHomologicalComplex _).obj I)
  have hy0 : (forget₂ (ModuleCat.{0} ℚ) Ab).map (L.d k (k + 1))
      ((forget₂ (ModuleCat.{0} ℚ) Ab).map (g.f k) x₀) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, g.comm, Functor.map_comp,
      ConcreteCategory.comp_apply, hx₀, map_zero]
  have hgy : (forget₂ (ModuleCat.{0} ℚ) Ab).map (g.f k) x₀ = (fibreStalkComplexHom b x ρ).f k
      ((TopCat.Presheaf.stalkFunctor _ x).map ζ.hom (A.presheaf.germ ⊤ x trivial s)) := hg
  have hy := hgy ▸ hy0
  apply hne hy
  have hc := cyclesMk_congr L hgy (k + 1) (by simp) hy0 hy
  refine (congrArg _ hc.symm).trans (key.symm.trans ?_)
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The restriction to the fibre of the germ of a global section. -/
private lemma fibreStalkComplexHom_f_germ
    {D : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X') ℤ}
    {I : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) (Fib b x)) ℤ}
    (ρ : D ⟶ ((TopCat.Sheaf.pushforward _ (fibι b x)).mapHomologicalComplex _).obj I) (k : ℤ)
    (σ : ToType ((D.X k).obj.obj (op ((Opens.map b).obj ⊤)))) :
    (fibreStalkComplexHom b x ρ).f k
        ((((TopCat.Sheaf.pushforward _ b).mapHomologicalComplex _).obj D).X k |>.presheaf.germ ⊤
          x trivial σ) =
      (ρ.f k).hom.app _ σ := by
  change (TopCat.Presheaf.germ _ ⊤ x trivial ≫ (fibreStalkComplexHom b x ρ).f k) σ = _
  simp only [fibreStalkComplexHom, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  erw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    germ_fibreStalkHom, show homOfLE (fib_preimage_eq_top b x ⊤ trivial).ge = 𝟙 _ from
      Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  rfl

end FibreTest

section ExtendComp

/-! ### Extension of `ℕ`-indexed complexes to `ℤ` and cohomology -/

variable {ι : Type*} {c : ComplexShape ι} {A B C : Type*} [Category A] [Category B] [Category C]
  [HasZeroMorphisms A] [HasZeroObject A] [HasZeroMorphisms B] [HasZeroObject B]
  [HasZeroMorphisms C] [HasZeroObject C] (F : A ⥤ B) (G : B ⥤ C)
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- `mapExtendXIsoSymm` for a composite functor. -/
private lemma mapExtendXIsoSymm_comp (K : HomologicalComplex A c) (o : Option ι) :
    G.map (Stacks.DerivedIndexing.mapExtendXIsoSymm F K o).inv ≫
        (Stacks.DerivedIndexing.mapExtendXIsoSymm (F ⋙ G) K o).hom =
      (Stacks.DerivedIndexing.mapExtendXIsoSymm G ((F.mapHomologicalComplex c).obj K) o).hom := by
  cases o with
  | none => exact (HomologicalComplex.extend.isZero_X _ rfl).eq_of_tgt _ _
  | some a =>
    simp only [Stacks.DerivedIndexing.mapExtendXIsoSymm, Iso.refl_inv, Iso.refl_hom]
    exact (Category.comp_id _).trans (G.map_id _)

variable {ι' : Type*} {c' : ComplexShape ι'} (e : c.Embedding c')

/-- `mapExtendIsoSymm` for a composite functor. -/
private lemma mapExtendIsoSymm_comp (K : HomologicalComplex A c) :
    (G.mapHomologicalComplex c').map (Stacks.DerivedIndexing.mapExtendIsoSymm F e K).inv ≫
        (Stacks.DerivedIndexing.mapExtendIsoSymm (F ⋙ G) e K).hom =
      (Stacks.DerivedIndexing.mapExtendIsoSymm G e ((F.mapHomologicalComplex c).obj K)).hom := by
  ext i'
  exact mapExtendXIsoSymm_comp F G K (e.r i')

end ExtendComp

section Psi

variable {A A' D : Type*} [Category A] [Category A'] [Category D] [Abelian A] [Abelian A']
  [Abelian D] (P : A' ⥤ A) (Γ : A ⥤ D) [P.Additive] [Γ.Additive]

/-- The cohomology of the `ℤ`-indexed extension of an `ℕ`-indexed complex, after applying `Γ`,
is the cohomology of the `ℕ`-indexed complex after applying `Γ`. -/
private noncomputable def extendHomologyMapIso (K : CochainComplex A ℕ) (k : ℕ) :
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).homology (ComplexShape.embeddingUpNat.f k) ≅
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology k :=
  HomologicalComplex.homologyMapIso
      (Stacks.DerivedIndexing.mapExtendIsoSymm Γ ComplexShape.embeddingUpNat K)
        (ComplexShape.embeddingUpNat.f k) ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat rfl

/-- The `ℤ`-indexed extension of a map of `ℕ`-indexed complexes `K ⟶ P(K')`. -/
private noncomputable def extendMapPush {K : CochainComplex A ℕ} {K' : CochainComplex A' ℕ}
    (g : K ⟶ (P.mapHomologicalComplex _).obj K') :
    K.extend ComplexShape.embeddingUpNat ⟶
      (P.mapHomologicalComplex _).obj (K'.extend ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap g ComplexShape.embeddingUpNat ≫
    (Stacks.DerivedIndexing.mapExtendIsoSymm P ComplexShape.embeddingUpNat K').inv

/-- `extendHomologyMapIso` is natural in maps `K ⟶ P(K')`. -/
private lemma extendHomologyMapIso_naturality {K : CochainComplex A ℕ} {K' : CochainComplex A' ℕ}
    (g : K ⟶ (P.mapHomologicalComplex _).obj K') (k : ℕ) :
    HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map (extendMapPush P g))
        (ComplexShape.embeddingUpNat.f k) ≫ (extendHomologyMapIso (P ⋙ Γ) K' k).hom =
      (extendHomologyMapIso Γ K k).hom ≫
        HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex _).map g) k := by
  have h1 := mapExtendIsoSymm_comp P Γ ComplexShape.embeddingUpNat K'
  have h2 := Stacks.DerivedIndexing.mapExtendIsoSymm_naturality Γ ComplexShape.embeddingUpNat g
  have h3 := HomologicalComplex.extendHomologyIso_hom_naturality
    ((Γ.mapHomologicalComplex _).map g) ComplexShape.embeddingUpNat (j := k)
    (j' := ComplexShape.embeddingUpNat.f k) rfl
  dsimp only [extendHomologyMapIso, extendMapPush]
  simp only [Iso.trans_hom, HomologicalComplex.homologyMapIso_hom, Functor.map_comp]
  rw [← HomologicalComplex.homologyMap_comp_assoc, Category.assoc, h1, h2,
    HomologicalComplex.homologyMap_comp, Category.assoc, Category.assoc]
  congr 1

end Psi

section StalksAndModel

open Opposite

/-- The stalks of the constant sheaf `ℚ` have rank at most one. -/
private lemma rank_stalk_constantSheaf_le (X : TopCat.{0}) (x : X) :
    Module.rank ℚ (TopCat.Presheaf.stalk (X := X) (C := ModuleCat.{0} ℚ)
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj x) ≤ 1 := by
  let P : TopCat.Presheaf (ModuleCat.{0} ℚ) X := (Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of ℚ ℚ)
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ) P
  have e := (asIso ((TopCat.Presheaf.stalkFunctor _ x).map
    (toSheafify (Opens.grothendieckTopology X) P))).toLinearEquiv
  refine (e.rank_eq).symm.le.trans ?_
  rw [rank_le_one_iff]
  refine ⟨P.germ ⊤ x trivial (1 : ℚ), fun v => ?_⟩
  obtain ⟨U, hxU, q, rfl⟩ := TopCat.Presheaf.germ_exist P (x := x) v
  refine ⟨(show ℚ from q), ?_⟩
  have h1 : P.germ ⊤ x trivial (1 : ℚ) = P.germ U x hxU (1 : ℚ) :=
    (TopCat.Presheaf.germ_res_apply P (homOfLE le_top) x hxU (1 : ℚ)).symm
  rw [h1]
  have h2 : ((show ℚ from q) • (1 : ℚ) : ℚ) = (show ℚ from q) := mul_one _
  exact ((P.germ U x hxU).hom.map_smul (show ℚ from q) (1 : ℚ)).symm.trans (congrArg _ h2)

variable {T X : TopCat.{0}} (i : T ⟶ X)

/-- Along an inducing map, the unit of `i⁻¹ ⊣ i_*` is invertible on the stalks at the image. -/
private lemma isIso_stalk_unit (hi : Topology.IsInducing i) (A : TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    (t : T) :
    IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) (i t)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) i).unit.app A).hom) := by
  have h1 := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    (ModuleCat.{0} ℚ) hi
    ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).obj A).presheaf t
  have h2 : (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) (i t)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) i).unit.app A).hom ≫
        TopCat.Presheaf.stalkPushforward _ i
          ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).obj A).presheaf t =
      Stacks.Topology.ambientStalkHom i A t := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro W hW
    erw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
      TopCat.Presheaf.stalkPushforward_germ]
    ext s
    exact Stacks.Topology.germ_unit_app i A W t hW s
  have : IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) (i t)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) i).unit.app A).hom ≫
        TopCat.Presheaf.stalkPushforward _ i
          ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).obj A).presheaf t) := by
    rw [h2]; exact Stacks.Topology.isIso_ambientStalkHom i A t
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (TopCat.Presheaf.stalkPushforward _ i
    ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).obj A).presheaf t) h1 this

/-- Off the closed image of `i`, the stalks of `i_* G` vanish. -/
private lemma subsingleton_stalk_pushforward (hi : IsClosed (Set.range i))
    (G : TopCat.Sheaf (ModuleCat.{0} ℚ) T) {x : X} (hx : x ∉ Set.range i) :
    Subsingleton (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) i).obj G).presheaf.stalk x) := by
  let W : Opens X := ⟨(Set.range i)ᶜ, hi.isOpen_compl⟩
  have hW : (Opens.map i).obj W = ⊥ := by
    ext y
    simp [W]
  constructor
  intro a b
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist _ (x := x) a
  obtain ⟨U', hxU', s', rfl⟩ := TopCat.Presheaf.germ_exist _ (x := x) b
  have hz : ∀ (V : Opens X) (hxV : x ∈ V) (σ : ToType
      (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) i).obj G).presheaf.obj (op V))),
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) i).obj G).presheaf.germ V x hxV σ = 0 := by
    intro V hxV σ
    have hxVW : x ∈ V ⊓ W := ⟨hxV, hx⟩
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : V ⊓ W ≤ V)) x hxVW]
    have hsub : Subsingleton (ToType (G.presheaf.obj (op ((Opens.map i).obj (V ⊓ W))))) := by
      have hb : (Opens.map i).obj (V ⊓ W) = ⊥ := by
        rw [← le_bot_iff, ← hW]; exact (Opens.map i).monotone inf_le_right
      rw [hb]
      exact (ModuleCat.isZero_iff_subsingleton).1
        (G.isTerminalOfEmpty.isZero)
    rw [@Subsingleton.elim _ hsub
      (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) i).obj G).presheaf.map
      (homOfLE (inf_le_left : V ⊓ W ≤ V)).op σ) 0]
    exact map_zero _
  rw [hz, hz]

end StalksAndModel

section Model

variable {X X' : TopCat.{0}}

/-- The resolution map `A[0] ⟶ J` in the bounded below homotopy category. -/
private noncomputable def resolutionHom {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X'}
    (J : InjectiveResolution A) :
    (HomotopyCategory.Plus.singleFunctor _ 0).obj A ⟶
      (HomotopyCategory.Plus.quotient _).obj J.plusObj :=
  (HomotopyCategory.Plus.ι _).preimage ((HomotopyCategory.quotient _ _).map J.ι')

/-- The resolution map becomes invertible in `D⁺`. -/
private lemma isIso_Qh_map_resolutionHom {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X'}
    (J : InjectiveResolution A) :
    IsIso (DerivedCategory.Plus.Qh.map (resolutionHom J)) := by
  apply Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _)
  change HomotopyCategory.quasiIso _ _ ((HomotopyCategory.Plus.ι _).map (resolutionHom J))
  have h : (HomotopyCategory.Plus.ι _).map (resolutionHom J) =
      (HomotopyCategory.quotient _ _).map J.ι' := Functor.map_preimage _ _
  rw [h]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
    ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)

/-- The model `F(J) ≅ RF(A[0])` of a right derived functor on an injective resolution, for any
choice of derived category of the target. -/
private noncomputable def rightDerivedModelIso {D : Type*} [Category D] [Abelian D]
    {inst : HasDerivedCategory D}
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X' ⥤ D) [F.Additive]
    {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X'} (J : InjectiveResolution A) :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
        (F.mapCochainComplexPlus.obj J.plusObj)) ≅
      F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor _ 0).obj A)) :=
  haveI hU : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient _).obj J.plusObj)) := inferInstance
  haveI := isIso_Qh_map_resolutionHom J
  @asIso _ _ _ _ (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient _).obj J.plusObj)) hU ≪≫
    F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Qh.map (resolutionHom J))).symm

/-- **The injective-resolution model of `RF(A[0])`.** For `η : B ⟶ F A` and an injective resolution
`J` of `A`, there is an isomorphism `F(J) ≅ RF(A[0])` in `D⁺` through which the structural unit
`B[0] ⟶ RF(A[0])` is the map of complexes given by the cocycle `η ≫ F(A ⟶ J⁰)`. -/
private theorem exists_model
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X' ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    [F.Additive] {B : TopCat.Sheaf (ModuleCat.{0} ℚ) X} {A : TopCat.Sheaf (ModuleCat.{0} ℚ) X'}
    (η : B ⟶ F.obj A) (J : InjectiveResolution A) :
    let m : (HomotopyCategory.Plus.singleFunctor _ 0).obj B ⟶
        F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor _ 0).obj A) :=
      (HomotopyCategory.Plus.ι _).preimage ((HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single _ _ 0).map η ≫
          (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app A))
    ∃ (M : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
          (F.mapCochainComplexPlus.obj J.plusObj)) ≅
        F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
          ((HomotopyCategory.Plus.singleFunctor _ 0).obj A)))
      (hζ : (η ≫ F.map J.inclusionZero) ≫
        (F.mapCochainComplexPlus.obj J.plusObj).obj.d 0 (0 + 1) = 0),
      DerivedCategory.Plus.Qh.map (singleHomOfCocycle _ (η ≫ F.map J.inclusionZero) hζ) ≫ M.hom =
        DerivedCategory.Plus.Qh.map m ≫
          F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor _ 0).obj A) := by
  intro m
  have := isIso_Qh_map_resolutionHom J
  have hζ : (η ≫ F.map J.inclusionZero) ≫
      (F.mapCochainComplexPlus.obj J.plusObj).obj.d 0 (0 + 1) = 0 := by
    have h' : (η ≫ F.map J.inclusionZero) ≫ F.map (J.cochainComplex.d 0 1) = 0 := by
      rw [Category.assoc, ← F.map_comp, J.inclusionZero_comp_d, F.map_zero, comp_zero]
    exact h'
  refine ⟨rightDerivedModelIso F J, hζ, ?_⟩
  have key : singleHomOfCocycle (k := 0) (F.mapCochainComplexPlus.obj J.plusObj)
      (η ≫ F.map J.inclusionZero) hζ =
      m ≫ F.mapHomotopyCategoryPlus.map (resolutionHom J) := by
    let ι' := HomotopyCategory.Plus.ι (TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    let Q' := HomotopyCategory.quotient (TopCat.Sheaf (ModuleCat.{0} ℚ) X) (ComplexShape.up ℤ)
    have e1 : ι'.map m = Q'.map ((HomologicalComplex.single _ _ 0).map η ≫
        (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app A) :=
      Functor.map_preimage _ _
    have e2 : ι'.map (F.mapHomotopyCategoryPlus.map (resolutionHom J)) =
        Q'.map ((F.mapHomologicalComplex _).map J.ι') := by
      change (F.mapHomotopyCategory _).map ((HomotopyCategory.Plus.ι _).map (resolutionHom J)) = _
      rw [show (HomotopyCategory.Plus.ι _).map (resolutionHom J) =
        (HomotopyCategory.quotient _ _).map J.ι' from Functor.map_preimage _ _]
      exact Functor.mapHomotopyCategory_map _ _
    have e3 : ι'.map (singleHomOfCocycle (k := 0) (F.mapCochainComplexPlus.obj J.plusObj)
        (η ≫ F.map J.inclusionZero) hζ) =
        Q'.map (HomologicalComplex.mkHomFromSingle (η ≫ F.map J.inclusionZero)
          (comp_d_eq_zero_of_rel hζ)) := Functor.map_preimage _ _
    have hchain : HomologicalComplex.mkHomFromSingle (η ≫ F.map J.inclusionZero)
        (comp_d_eq_zero_of_rel hζ) = ((HomologicalComplex.single _ _ 0).map η ≫
          (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app A) ≫
            (F.mapHomologicalComplex _).map J.ι' := by
      apply HomologicalComplex.from_single_hom_ext
      rw [HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.comp_f,
        HomologicalComplex.comp_f,
        HomologicalComplex.single_map_f_self, Functor.mapHomologicalComplex_map_f,
        J.ι'_f_zero]
      simp [InjectiveResolution.inclusionZero, J.ι'_f_zero]
    apply ι'.map_injective
    refine e3.trans ((congrArg Q'.map hchain).trans ?_)
    refine (Q'.map_comp _ _).trans ?_
    refine Eq.trans ?_ (ι'.map_comp m (F.mapHomotopyCategoryPlus.map (resolutionHom J))).symm
    rw [e1, e2]
    rfl
  have hn := F.rightDerivedFunctorPlusUnith.naturality (resolutionHom J)
  dsimp only [Functor.comp_map] at hn
  rw [key]
  let P := (HomotopyCategory.Plus.quotient (TopCat.Sheaf (ModuleCat.{0} ℚ) X')).obj J.plusObj
  let S := (HomotopyCategory.Plus.singleFunctor (TopCat.Sheaf (ModuleCat.{0} ℚ) X') 0).obj A
  let q := DerivedCategory.Plus.Qh.map (resolutionHom J)
  change DerivedCategory.Plus.Qh.map (m ≫ F.mapHomotopyCategoryPlus.map (resolutionHom J)) ≫
    (F.rightDerivedFunctorPlusUnith.app P ≫ F.rightDerivedFunctorPlus.map (inv q)) = _
  calc DerivedCategory.Plus.Qh.map (m ≫ F.mapHomotopyCategoryPlus.map (resolutionHom J)) ≫
        (F.rightDerivedFunctorPlusUnith.app P ≫ F.rightDerivedFunctorPlus.map (inv q))
      = DerivedCategory.Plus.Qh.map m ≫ ((DerivedCategory.Plus.Qh.map
          (F.mapHomotopyCategoryPlus.map (resolutionHom J)) ≫ F.rightDerivedFunctorPlusUnith.app P) ≫
          F.rightDerivedFunctorPlus.map (inv q)) := by
        simp only [Functor.map_comp, Category.assoc]
    _ = DerivedCategory.Plus.Qh.map m ≫ ((F.rightDerivedFunctorPlusUnith.app S ≫
          F.rightDerivedFunctorPlus.map q) ≫ F.rightDerivedFunctorPlus.map (inv q)) := by
        rw [hn]
    _ = DerivedCategory.Plus.Qh.map m ≫ F.rightDerivedFunctorPlusUnith.app S := by
        rw [Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
        exact congrArg (_ ≫ ·) (Category.comp_id _)

end Model

section FibreCohomology

open Opposite MMP MMP.SingularCochain

section Exact

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B] [EnoughInjectives A]

/-- The single complex `M[0]` after an additive functor, in the bounded below homotopy category. -/
private noncomputable def mapHomotopyCategoryPlusSingleIso (G : A ⥤ B) [G.Additive] (M : A) :
    G.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj M) ≅
      (HomotopyCategory.Plus.singleFunctor B 0).obj (G.obj M) :=
  (HomotopyCategory.Plus.ι B).preimageIso ((HomotopyCategory.quotient B _).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).app M))

/-- An exact functor commutes with the single complex functor on derived categories. -/
private noncomputable def rightDerivedFunctorPlusSingleIso (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (M : A) :
    G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≅
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj (G.obj M)) :=
  ((@asIso _ _ _ _ G.rightDerivedFunctorPlusUnith
      (Stacks.Cohomology.BaseChange.exactUnit_isIso G)).app _).symm ≪≫
    DerivedCategory.Plus.Qh.mapIso (mapHomotopyCategoryPlusSingleIso G M)

end Exact

section Sing

/-- Singular cohomology of a space homeomorphic to `ℙⁿ(ℂ)`. -/
private lemma relCohomology_of_homeomorph {Y : TopCat.{0}} (n : ℕ)
    (e : Y ≃ₜ MMP.Topology.complexProjectiveSpace n) (k : ℕ) :
    Nonempty (relCohomology ℚ ((Set.univ : Set Y)ᶜ) k ≃ₗ[ℚ]
      cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (MMP.Topology.complexProjectiveSpace n)
        Set.univ k) := by
  have hA : (TopCat.isoOfHomeo e).hom ⁻¹'
      ((Set.univ : Set (MMP.Topology.complexProjectiveSpace n))ᶜ) =
      (Set.univ : Set Y)ᶜ := by
    ext; simp
  let iso := MMP.Topology.relativeSingularCohomologyIsoOfIso ℚ (TopCat.isoOfHomeo e)
    ((Set.univ : Set (MMP.Topology.complexProjectiveSpace n))ᶜ) k
  rw [hA] at iso
  exact ⟨(relativeSingularCohomologyEquiv ℚ (Y := Y) _ k).symm.trans iso.symm.toLinearEquiv⟩

/-- The rational Betti numbers of a space homeomorphic to `ℙⁿ(ℂ)`. -/
private lemma rank_relCohomology_le_of_homeomorph {Y : TopCat.{0}} (n : ℕ)
    (e : Y ≃ₜ MMP.Topology.complexProjectiveSpace n) (k : ℕ) :
    (Even k ∧ k ≤ 2 * n → Module.rank ℚ (relCohomology ℚ ((Set.univ : Set Y)ᶜ) k) ≤ 1) ∧
      (¬ (Even k ∧ k ≤ 2 * n) → Subsingleton (relCohomology ℚ ((Set.univ : Set Y)ᶜ) k)) := by
  obtain ⟨E⟩ := relCohomology_of_homeomorph n e k
  have h := MMP.Topology.cohomology_complexProjectiveSpace ℚ n k
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨E'⟩ := h.1 hk
    rw [(E.trans E').rank_eq, Module.rank_self]
  · have := h.2 hk
    exact E.toEquiv.subsingleton

end Sing

/-- Inverse images of sheaves of `ℚ`-vector spaces are left exact. -/
private lemma pullback_preservesFiniteLimits {Y Y' : TopCat.{0}} (k : Y' ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) k) := by
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

/-- The constant sheaf `ℚ` on a space. -/
private noncomputable abbrev ratSheaf (Z : TopCat.{0}) : TopCat.Sheaf (ModuleCat.{0} ℚ) Z :=
  (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- The inverse image of the constant sheaf is the constant sheaf. -/
private noncomputable def constPullbackIso {Z Z' : TopCat.{0}} (f : Z' ⟶ Z) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj (ratSheaf Z) ≅ ratSheaf Z' :=
  haveI := isIso_homEquiv_symm_constUnit f
  asIso (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).homEquiv _ _).symm
    (constUnit f))

/-- The cohomology of derived sections of `A[0]`, for any choice of derived category of
`ℚ`-vector spaces, is the cohomology of the sections of an injective resolution of `A`. -/
private noncomputable def homologyRightDerivedSectionsIso {Z : TopCat.{0}}
    {inst : HasDerivedCategory (ModuleCat.{0} ℚ)} (A : TopCat.Sheaf (ModuleCat.{0} ℚ) Z) (n : ℤ) :
    letI : (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Z ⋙
      (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).Additive := ⟨fun {_ _ _ _} => rfl⟩
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ℚ) n).obj
      ((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Z ⋙
        (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor _ 0).obj A))) ≅
      (((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Z ⋙
        (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).mapHomologicalComplex _).obj
          (injectiveResolution A).cochainComplex).homology n :=
  letI : (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Z ⋙
    (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  (DerivedCategory.Plus.homologyFunctor _ n).mapIso (rightDerivedModelIso _ _).symm ≪≫
    (homologyQhNatIso (ModuleCat.{0} ℚ) n).app _

/-- **The cohomology of the fibres bounds the stalks of `Rb_* ℚ`.** If the fibre of the realized
blowup over `x` is homeomorphic to `ℙᵐ(ℂ)`, the stalk at `x` of `Hⁿ(Rb_* ℚ_{V'})` has rank at most
one when `n` is even with `0 ≤ n ≤ 2m`, and vanishes otherwise. -/
private theorem stalkH_bound_of_homeomorph {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) [IsIntegral V]
    [IsSeparated sV] [LocallyOfFiniteType sV] [QuasiCompact sV] (I : V.IdealSheafData)
    (x : analyticSpace sV) (m : ℕ)
    (e : (analyticMap (blowUpToBase I) rfl ⁻¹' {x} : Set (analyticSpace (blowUpToBase I ≫ sV))) ≃ₜ
      MMP.Topology.complexProjectiveSpace m) (n : ℤ) :
    let bAn := analyticMap (blowUpToBase I) rfl
    let QV := ratSheaf (analyticSpace sV)
    let F := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) bAn
    haveI : F.Additive := Functor.additive_of_preserves_binary_products F
    let QV' := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) bAn).obj QV
    let K := F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.singleFunctor _ 0).obj QV'))
    (Even n ∧ 0 ≤ n ∧ n ≤ 2 * m → Module.rank ℚ ((stalkH n x).obj K) ≤ 1) ∧
      (¬ (Even n ∧ 0 ≤ n ∧ n ≤ 2 * m) → IsZero ((stalkH n x).obj K)) := by
  intro bAn QV F QV' K
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  let Fx := TopCat.of (bAn ⁻¹' {x})
  let ι : Fx ⟶ analyticSpace (blowUpToBase I ≫ sV) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  haveI : (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Fx ⋙
      (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  obtain ⟨φ⟩ := (isIso_baseChange_analyticMap_of_isProper (blowUpToBase I) rfl bAn (𝟙 _) (𝟙 _)
    (IsPullback.id_horiz bAn)).2.2.2 ℚ (DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.singleFunctor _ 0).obj QV')) x n
  haveI : PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) ι) :=
    pullback_preservesFiniteLimits ι
  haveI : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) ι) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  haveI : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) ι).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  let Γ := TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Fx ⋙ (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)
  let ψ2 : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) ι).obj QV' ≅ ratSheaf Fx :=
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) ι).mapIso (constPullbackIso bAn) ≪≫ constPullbackIso ι
  let σ := rightDerivedFunctorPlusSingleIso (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) ι) QV' ≪≫
    DerivedCategory.Plus.Qh.mapIso ((HomotopyCategory.Plus.singleFunctor _ 0).mapIso ψ2)
  let W :=
    ((Γ.mapHomologicalComplex _).obj (injectiveResolution (ratSheaf Fx)).cochainComplex).homology n
  let φ' : (stalkH n x).obj K ≅ W :=
    φ ≪≫ (DerivedCategory.Plus.homologyFunctor _ n).mapIso (Γ.rightDerivedFunctorPlus.mapIso σ) ≪≫
      homologyRightDerivedSectionsIso (ratSheaf Fx) n
  have hmet : MetrizableSpace (analyticSpace (blowUpToBase I ≫ sV)) :=
    (metrizableSpace_and_stronglyLocallyContractibleSpace (blowUpToBase I ≫ sV)).1
  haveI : StronglyLocallyContractibleSpace (MMP.Topology.complexProjectiveSpace m) := by
    letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ m)).Over (Spec (.of ℂ)) :=
      ⟨Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ m⟩
    haveI := Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff ℂ m
    haveI : LocallyOfFiniteType (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ m) ↘ Spec (.of ℂ)) :=
      inferInstanceAs (LocallyOfFiniteType (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ m))
    have h := UnderlyingSpace.hasOpenContractibleBasis
      (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ m))
    have := h.stronglyLocallyContractibleSpace
    exact (MMP.Topology.underlyingSpaceProjectiveSpaceHomeomorph
      m rfl).symm
        |>.isOpenEmbedding.stronglyLocallyContractibleSpace
  haveI : StronglyLocallyContractibleSpace Fx := e.isOpenEmbedding.stronglyLocallyContractibleSpace
  rcases lt_or_ge n 0 with hn | hn
  · have hz : IsZero W := ShortComplex.isZero_homology_of_isZero_X₂ _
      (Γ.map_isZero (CochainComplex.isZero_of_isStrictlyGE _ 0 n hn))
    exact ⟨fun h => absurd h.2.1 (not_le.2 hn), fun _ => hz.of_iso φ'⟩
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    obtain ⟨E, -⟩ := exists_homology_rightDerivedFunctorPlus_globalSections_iso_relCohomology
    let E' : (stalkH (k : ℤ) x).obj K ≅ ModuleCat.of ℚ (relCohomology ℚ ((Set.univ : Set Fx)ᶜ) k) :=
      φ' ≪≫ (homologyRightDerivedSectionsIso (inst := HasDerivedCategory.standard _)
        (ratSheaf Fx) k).symm ≪≫
        E Fx StronglyLocallyContractibleSpace.locallyContractible k
    have hR := rank_relCohomology_le_of_homeomorph (Y := Fx) m e k
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [E'.toLinearEquiv.rank_eq]
      exact hR.1 ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.2⟩
    · have := hR.2 (fun h' => h ⟨by exact_mod_cast h'.1, by omega, by exact_mod_cast h'.2⟩)
      exact (ModuleCat.isZero_of_subsingleton _).of_iso E'

/-- The realization of a closed immersion is a closed embedding. -/
private lemma isClosedEmbedding_analyticMap {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (g : X ⟶ Y)
    [IsClosedImmersion g] : Topology.IsClosedEmbedding (analyticMap (sX := g ≫ sY) g rfl) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : X.Over (Spec (.of ℂ)) := ⟨g ≫ sY⟩
  haveI : g.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have hf : ⇑(analyticMap (sX := g ≫ sY) g rfl) =
      (homeomorphUnderlyingSpace (X := Y)).symm ∘ UnderlyingSpace.map (K := ℂ) g ∘
        (homeomorphUnderlyingSpace (X := X)) := by
    funext x
    apply (homeomorphUnderlyingSpace (X := Y)).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    rfl
  rw [hf]
  exact (homeomorphUnderlyingSpace (X := Y)).symm.isClosedEmbedding.comp
    ((UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion g).comp
      (homeomorphUnderlyingSpace (X := X)).isClosedEmbedding)

/-- Off the centre, the fibres of the realized blowup are points. -/
private lemma nonempty_unique_fibre_of_notMem {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (I : V.IdealSheafData) (x : analyticSpace sV) (hx : x.toScheme ∉ I.support) :
    Nonempty (Unique (analyticMap (blowUpToBase I) rfl ⁻¹' {x} :
      Set (analyticSpace (blowUpToBase I ≫ sV)))) := by
  have h := (isHomeomorph_restrictPreimage_realize_blowUpToBase sV I).bijective
  obtain ⟨⟨y, hyS⟩, hy⟩ := h.2 ⟨x, hx⟩
  have hyx : realize (blowUpToBase I) rfl y = x := congrArg Subtype.val hy
  refine ⟨{ default := ⟨y, hyx⟩, uniq := fun z => ?_ }⟩
  have hz : realize (blowUpToBase I) rfl z.1 = x := z.2
  have hzS : realize (blowUpToBase I) rfl z.1 ∈
      {y : ComplexPoints sV | y.toScheme ∉ (I.support : Set V)} := by
    rw [hz]; exact hx
  have := @h.1 ⟨z.1, hzS⟩ ⟨y, hyS⟩ (Subtype.ext (hz.trans hyx.symm))
  have hzy : z.1 = y := congrArg (fun w => w.1) this
  exact Subtype.ext hzy

/-- The fibres of the realized blowup are complex projective spaces: of dimension `c - 1` over
the centre, and points elsewhere. -/
private lemma exists_fibre_homeomorph {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (I : V.IdealSheafData)
    (hI : MMP.Resolution.IsSmoothBlowup sV I) (c : ℕ) (hc : 2 ≤ c)
    (hcodim : ∀ Z : IrreducibleCloseds V,
      Maximal (fun W : IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z → codimension Z = c)
    (x : analyticSpace sV) :
    ∃ m : ℕ, Nonempty ((analyticMap (blowUpToBase I) rfl ⁻¹' {x} :
        Set (analyticSpace (blowUpToBase I ≫ sV))) ≃ₜ MMP.Topology.complexProjectiveSpace m) ∧
      (x.toScheme ∈ I.support → m = c - 1) ∧ (x.toScheme ∉ I.support → m = 0) := by
  by_cases hx : x.toScheme ∈ I.support
  · exact ⟨c - 1, MMP.Topology.nonempty_homeomorph_preimage_analyticMap_blowUpToBase_of_codimension
      sV I hI c (by omega) hcodim x hx, fun _ => rfl, fun h => absurd hx h⟩
  · obtain ⟨hu⟩ := nonempty_unique_fibre_of_notMem sV I x hx
    exact ⟨0, ⟨Homeomorph.homeomorphOfUnique _ _⟩, fun h => absurd h hx, fun _ => rfl⟩

end FibreCohomology

section ResolutionMaps

open Stacks.DerivedIndexing

/-- An injective resolution of `Z` is one of any object isomorphic to `Z`. -/
private noncomputable def InjectiveResolution.ofIso {C : Type*} [Category C] [Abelian C] {Z Z' : C}
    (e : Z' ≅ Z) (J : InjectiveResolution Z) : InjectiveResolution Z' where
  cocomplex := J.cocomplex
  ι := (CochainComplex.single₀ C).map e.hom ≫ J.ι

set_option backward.isDefEq.respectTransparency false in
/-- A map from an object into the kernel of the first differential of a complex of injectives
extends to a map of complexes out of any injective resolution of the object. -/
private lemma exists_hom_of_injective {C : Type*} [Category* C] [Abelian C] {Z : C}
    (I : InjectiveResolution Z) (K : CochainComplex C ℕ) (hK : ∀ n, Injective (K.X n))
    (φ : Z ⟶ K.X 0) (hφ : φ ≫ K.d 0 1 = 0) :
    ∃ g : I.cocomplex ⟶ K, I.ι.f 0 ≫ g.f 0 = φ := by
  let g0 : I.cocomplex.X 0 ⟶ K.X 0 := Injective.factorThru φ (I.ι.f 0)
  have hg0 : I.ι.f 0 ≫ g0 = φ := Injective.comp_factorThru _ _
  let g1 : I.cocomplex.X 1 ⟶ K.X 1 := I.exact₀.descToInjective (g0 ≫ K.d 0 1) (by
    change I.ι.f 0 ≫ g0 ≫ K.d 0 1 = 0
    rw [reassoc_of% hg0, hφ])
  have hg1 : I.cocomplex.d 0 1 ≫ g1 = g0 ≫ K.d 0 1 := I.exact₀.comp_descToInjective _ _
  refine ⟨CochainComplex.mkHom _ _ g0 g1 hg1.symm fun n ⟨g, g', w⟩ =>
    ⟨(I.exact_succ n).descToInjective (g' ≫ K.d (n + 1) (n + 2))
      (by simp [reassoc_of% w.symm]), ((I.exact_succ n).comp_descToInjective _ _).symm⟩, ?_⟩
  rw [CochainComplex.mkHom_f_0]
  exact hg0

set_option backward.isDefEq.respectTransparency false in
/-- A map `J ⟶ f_* J'` of injective resolutions of the constant sheaves over `constUnit f`. -/
private lemma exists_hom_resolution_pushforward {Y Y' : TopCat.{0}} (f : Y' ⟶ Y)
    (J : InjectiveResolution (ratSheaf Y)) (J' : InjectiveResolution (ratSheaf Y')) :
    ∃ g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex
        _).obj J'.cocomplex,
      J.ι.f 0 ≫ g.f 0 =
        MMP.Analytic.constUnit f ≫
          (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map (J'.ι.f 0) := by
  let P := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f
  exact exists_hom_of_injective J ((P.mapHomologicalComplex _).obj J'.cocomplex)
    (fun k ↦ P.injective_obj (J'.cocomplex.X k)) (MMP.Analytic.constUnit f ≫ P.map (J'.ι.f 0)) (by
      rw [Category.assoc, Functor.mapHomologicalComplex_obj_d, ← CategoryTheory.Functor.map_comp,
        J'.ι_f_zero_comp_complex_d, Functor.map_zero, Limits.comp_zero])

set_option backward.isDefEq.respectTransparency false in
/-- In degree `0`, the extension of a map of resolutions over `constUnit f` is `constUnit f`
between the inclusions of the resolved objects. -/
private lemma inclusionZero_comp_extendMapPush_f_zero {Y Y' : TopCat.{0}} (f : Y' ⟶ Y)
    {A : TopCat.Sheaf (ModuleCat.{0} ℚ) Y} (eQ : A ≅ ratSheaf Y) (J : InjectiveResolution A)
    (I : InjectiveResolution (ratSheaf Y'))
    (g : (InjectiveResolution.ofIso eQ.symm J).cocomplex ⟶
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex _).obj I.cocomplex)
    (hg : (InjectiveResolution.ofIso eQ.symm J).ι.f 0 ≫ g.f 0 =
      constUnit f ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map (I.ι.f 0)) :
    J.inclusionZero ≫ (extendMapPush (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f) g).f 0 =
      eQ.hom ≫ constUnit f ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map I.inclusionZero := by
  have hJ : (InjectiveResolution.ofIso eQ.symm J).ι.f 0 = eQ.inv ≫ J.ι.f 0 := by
    simp [InjectiveResolution.ofIso]
  rw [hJ, Category.assoc] at hg
  have hg' : J.ι.f 0 ≫ g.f 0 = eQ.hom ≫ constUnit f ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map (I.ι.f 0) := by
    rw [← hg, Iso.hom_inv_id_assoc]
  simp only [extendMapPush, HomologicalComplex.comp_f, InjectiveResolution.inclusionZero,
    InjectiveResolution.ι'_f_zero, Category.assoc, Iso.inv_hom_id_assoc]
  have h1 : (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat).f 0 =
      (J.cocomplex.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫ g.f 0 ≫
        ((((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex _).obj
          I.cocomplex).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv :=
    HomologicalComplex.extendMap_f g ComplexShape.embeddingUpNat rfl
  have h2 : (mapExtendIsoSymm (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f)
      ComplexShape.embeddingUpNat I.cocomplex).inv.f 0 =
      ((((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex _).obj
          I.cocomplex).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map
          (I.cocomplex.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv := by
    have h := mapExtendXIsoSymm_hom_of_r_eq_some (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f)
      ComplexShape.embeddingUpNat I.cocomplex (i' := 0) (i := 0)
        (ComplexShape.embeddingUpNat.r_eq_some rfl)
    rw [← cancel_epi (mapExtendXIsoSymm (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f) I.cocomplex
      (ComplexShape.embeddingUpNat.r 0)).hom]
    erw [Iso.hom_inv_id]
    rw [h]
    simp
    rfl
  erw [h1, h2]
  change J.ι.f 0 ≫ (J.cocomplex.extendXIso _ _).inv ≫
    ((J.cocomplex.extendXIso _ _).hom ≫ _ ≫ _) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hg', Functor.map_comp]
  rfl

end ResolutionMaps

section UnitSection

open Opposite

/-- The unit section `1 ∈ Γ(Z, ℚ_Z)` of the constant sheaf. -/
private noncomputable def oneSection (Z : TopCat.{0}) : ToType ((ratSheaf Z).obj.obj (op ⊤)) :=
  (constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ) isTerminalTop).unit.app
    (ModuleCat.of ℚ ℚ) (1 : ℚ)

/-- `constUnit f` carries the unit section to the unit section. -/
private lemma constUnit_app_oneSection {Z Z' : TopCat.{0}} (f : Z' ⟶ Z) :
    (constUnit f).hom.app (op ⊤) (oneSection Z) = oneSection Z' := by
  have h := (Adjunction.homEquiv_unit _ _ _ _).symm.trans (homEquiv_constUnit f)
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom h (1 : ℚ))

/-- Following `constUnit f` by the pushforward of a morphism `φ` out of `ℚ_{Z'}` sends the unit
section to the image of the unit section under `φ`. -/
private lemma constUnit_comp_map_app_oneSection {Z Z' : TopCat.{0}} (f : Z' ⟶ Z)
    {G : TopCat.Sheaf (ModuleCat.{0} ℚ) Z'}
    (φ : (constantSheaf (Opens.grothendieckTopology Z') (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ) ⟶ G) :
    ((constUnit f ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map φ).hom.app (op ⊤))
      (oneSection Z) = φ.hom.app (op ⊤) (oneSection Z') := by
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  erw [constUnit_app_oneSection]
  rfl

/-- On a nonempty space the unit section of the constant sheaf is nonzero. -/
private lemma oneSection_ne_zero (Z : TopCat.{0}) (p : Z) : oneSection Z ≠ 0 := by
  let P : TopCat.Presheaf (ModuleCat.{0} ℚ) Z := (Functor.const (Opens Z)ᵒᵖ).obj (ModuleCat.of ℚ ℚ)
  have hs := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) P
  have hp : p ∈ (⊤ : Opens Z) := trivial
  let ev : P.stalk p ⟶ ModuleCat.of ℚ ℚ := colimit.desc _
    ⟨ModuleCat.of ℚ ℚ, ⟨(fun _ => 𝟙 _),
      (fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm)⟩⟩
  have hev : ev (P.germ ⊤ p hp (1 : ℚ)) = (1 : ℚ) := by
    change (P.germ ⊤ p hp ≫ ev) (1 : ℚ) = (1 : ℚ)
    rw [show P.germ ⊤ p hp ≫ ev = 𝟙 _ from colimit.ι_desc _ _]
    rfl
  have hone : oneSection Z = (toSheafify (Opens.grothendieckTopology Z) P).app (op ⊤) (1 : ℚ) := rfl
  intro h0
  have h1 : (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map
      (toSheafify (Opens.grothendieckTopology Z) P) (P.germ ⊤ p hp (1 : ℚ)) = 0 := by
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rw [← hone, h0]
    exact map_zero _
  have h2 : P.germ ⊤ p hp (1 : ℚ) = 0 := by
    have h3 := congrArg (inv ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map
      (toSheafify (Opens.grothendieckTopology Z) P))) h1
    rw [map_zero] at h3
    refine Eq.trans ?_ h3
    exact ((ConcreteCategory.id_apply _).symm.trans
      (ConcreteCategory.congr_hom (@IsIso.hom_inv_id _ _ _ _ _ hs) _).symm).trans
        (ConcreteCategory.comp_apply _ _ _)
  rw [h2, map_zero] at hev
  exact zero_ne_one hev

end UnitSection

section UnitStalk

open Opposite

set_option backward.isDefEq.respectTransparency false in
/-- **The structural unit is nonzero on the stalks of `H⁰`** at every point with a nonempty
fibre: the restriction to the fibre of the cocycle `ℚ_X ⟶ b_* J⁰` sends `1` to the unit
section of the fibre, whose class in `H⁰` of the fibre is nonzero. -/
private lemma stalkH_unit_ne_zero {X X' : TopCat.{0}} (b : X' ⟶ X) (x : X) (p : Fib b x) :
    let F := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) b
    let QV' := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) b).obj (ratSheaf X)
    let η := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) b).unit.app (ratSheaf X)
    let J := injectiveResolution QV'
    ∀ hζ₀ : (η ≫ F.map J.inclusionZero) ≫
        (F.mapCochainComplexPlus.obj J.plusObj).obj.d 0 (0 + 1) = 0,
      (stalkH 0 x).map (DerivedCategory.Plus.Qh.map
        (singleHomOfCocycle (F.mapCochainComplexPlus.obj J.plusObj) (η ≫ F.map J.inclusionZero)
          hζ₀)) ≠ 0 := by
  intro F QV' η J hζ₀
  let ι := fibι b x
  let eQ : QV' ≅ ratSheaf X' := constPullbackIso b
  let J' := InjectiveResolution.ofIso eQ.symm J
  let Ix := injectiveResolution (ratSheaf (Fib b x))
  obtain ⟨g, hg⟩ := exists_hom_resolution_pushforward ι J' Ix
  refine stalkH_map_singleHomOfCocycle_ne_zero b x J.plusObj
    (extendMapPush (TopCat.Sheaf.pushforward _ ι) g) _ hζ₀ (oneSection X) ?_
  intro hy hπ
  let Γ := TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (Fib b x) ⋙
    (evaluation _ (ModuleCat.{0} ℚ)).obj (op ⊤)
  haveI : Γ.Additive := sectionsTop_additive (Fib b x)
  let L := (Γ.mapHomologicalComplex _).obj Ix.cochainComplex
  have hd : L.d (-1) 0 = 0 :=
    (Γ.map_isZero (CochainComplex.isZero_of_isStrictlyGE Ix.cochainComplex 0 (-1)
      (by omega))).eq_of_src _ _
  have hiso : IsIso (L.homologyπ 0) := L.isIso_homologyπ (-1) 0 (by simp) hd
  have hinj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map (L.homologyπ 0)) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  have hc := hinj (hπ.trans (map_zero _).symm)
  have hy0 := (L.i_cyclesMk _ 1 (by simp) hy).symm.trans
    ((congrArg ((forget₂ (ModuleCat.{0} ℚ) Ab).map (L.iCycles 0)) hc).trans (map_zero _))
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, fibreStalkComplexHom_f_germ] at hy0
  have hP0 := inclusionZero_comp_extendMapPush_f_zero ι eQ J Ix g hg
  have hη : η ≫ F.map eQ.hom = constUnit b :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have key : ((η ≫ F.map (J.inclusionZero ≫ (extendMapPush _ g).f 0)).hom.app (op ⊤))
      (oneSection X) = Ix.inclusionZero.hom.app (op ⊤) (oneSection (Fib b x)) := by
    have hcomp : constUnit b ≫ F.map (constUnit ι) = constUnit (ι ≫ b) :=
      (constUnit_comp b ι).symm
    rw [hP0, Functor.map_comp, ← Category.assoc, hη, Functor.map_comp, ← Category.assoc, hcomp]
    exact constUnit_comp_map_app_oneSection (ι ≫ b) Ix.inclusionZero
  have hmono : Mono Ix.inclusionZero := by
    dsimp only [InjectiveResolution.inclusionZero]
    rw [InjectiveResolution.ι'_f_zero, Iso.inv_hom_id_assoc]
    infer_instance
  have hinj' : Function.Injective (Ix.inclusionZero.hom.app (op ⊤)) := by
    have : Mono (Ix.inclusionZero.hom.app (op ⊤)) := by
      have : Mono ((sheafToPresheaf (Opens.grothendieckTopology (Fib b x)) (ModuleCat.{0} ℚ)).map
          Ix.inclusionZero) := Functor.map_mono _ _
      exact (NatTrans.mono_iff_mono_app _).1 this _
    exact (ModuleCat.mono_iff_injective _).1 this
  apply oneSection_ne_zero (Fib b x) p
  apply hinj'
  rw [map_zero, ← key]
  exact hy0

end UnitStalk

section Elements

/-- In a complex of `ℚ`-vector spaces, a cycle whose class vanishes is a boundary. -/
private lemma exists_d_eq_of_homologyπ_eq_zero {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{0} ℚ) c) {i j : ι} (hij : c.prev j = i)
    (z : ToType (K.cycles j)) (hz : K.homologyπ j z = 0) :
    ∃ y : ToType (K.X i), K.d i j y = K.iCycles j z := by
  have hS : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j)
      (K.toCycles_comp_homologyπ i j)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hij)
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hS z hz
  refine ⟨y, ?_⟩
  rw [← hy, ← ConcreteCategory.comp_apply, K.toCycles_i]

end Elements

section Flasque

/-- **Injective sheaves of `ℚ`-vector spaces are flasque.** -/
private lemma surjective_map_of_injective {Y : TopCat.{0}} (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)
    (hG : Injective G) {U V : Opens Y} (h : U ≤ V) :
    Function.Surjective (G.presheaf.map (homOfLE h).op) := by
  have hG' := @Functor.PreservesInjectiveObjects.injective_obj _ _ _ _
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}))
    (MMP.Topology.preservesInjectiveObjects_sheafCompose_forget₂_rat Y) G hG
  exact @Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective _
    ((sheafCompose _ (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})).obj G) hG' _ _ h

end Flasque

section Restrict

open TopCat.Presheaf TopCat.Presheaf.ExtensionByInitial

variable {Y : TopCat.{0}} (U : Opens Y)

/-- The presheaf-level extension by zero of presheaves of `ℚ`-vector spaces preserves finite
limits. -/
private lemma preservesFiniteLimits_extendByInitialFunctor_rat :
    PreservesFiniteLimits (extendByInitialFunctor (C := ModuleCat.{0} ℚ) U) := by
  apply preservesFiniteLimits_of_evaluation
  intro V
  by_cases hV : V.unop ≤ U
  · let e : (evaluation (Opens (sp U))ᵒᵖ (ModuleCat.{0} ℚ)).obj
            (Opposite.op ((Opens.map U.inclusion').obj V.unop)) ≅
          extendByInitialFunctor (C := ModuleCat.{0} ℚ) U ⋙
            (evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj V :=
      NatIso.ofComponents (fun F =>
        (eqToIso (ExtensionByInitial.obj_of_le U F hV)).symm) (by
          intro F G η; simp [extendByInitialFunctor, extendByInitial, ExtensionByInitial.map,
            ExtensionByInitial.mapNat, ExtensionByInitial.appMap, hV])
    let _ : PreservesFiniteLimits
        ((evaluation (Opens (sp U))ᵒᵖ (ModuleCat.{0} ℚ)).obj
          (Opposite.op ((Opens.map U.inclusion').obj V.unop))) :=
      instPreservesFiniteLimitsFunctorObjEvaluationOfHasFiniteLimits _
    exact preservesFiniteLimits_of_natIso e
  · let e : (Functor.const (TopCat.Presheaf (ModuleCat.{0} ℚ) (sp U))).obj
            (⊥_ (ModuleCat.{0} ℚ)) ≅
          extendByInitialFunctor (C := ModuleCat.{0} ℚ) U ⋙
            (evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj V :=
      NatIso.ofComponents (fun F =>
        (eqToIso (ExtensionByInitial.obj_of_not_le U F hV)).symm) (by
          intro F G η
          simp only [Functor.const_obj_obj, Functor.comp_obj, evaluation_obj_obj,
            Functor.const_obj_map, Iso.symm_hom, eqToIso.inv, Category.id_comp,
            Functor.comp_map, evaluation_obj_map]
          apply (initialIsInitial : IsInitial (⊥_ (ModuleCat.{0} ℚ))).hom_ext)
    let _ : PreservesFiniteLimits
        ((Functor.const (TopCat.Presheaf (ModuleCat.{0} ℚ) (sp U))).obj
          (⊥_ (ModuleCat.{0} ℚ))) :=
      ⟨fun J _ _ =>
        (((Functor.const (TopCat.Presheaf (ModuleCat.{0} ℚ) (sp U))).obj
            (⊥_ (ModuleCat.{0} ℚ))).preservesLimitsOfShape_of_isZero
          (((Functor.const (TopCat.Presheaf (ModuleCat.{0} ℚ) (sp U))).obj
            (⊥_ (ModuleCat.{0} ℚ))).isZero (fun _ => by
              dsimp
              exact (isZero_zero (C := ModuleCat.{0} ℚ)).of_iso
                HasZeroObject.zeroIsoInitial.symm)) J)⟩
    exact preservesFiniteLimits_of_natIso e

/-- Extension by zero of sheaves of `ℚ`-vector spaces preserves monomorphisms. -/
private lemma preservesMonomorphisms_extendByInitialSheaf_rat :
    (extendByInitialSheaf (C := ModuleCat.{0} ℚ) U).PreservesMonomorphisms := by
  have := preservesFiniteLimits_extendByInitialFunctor_rat U
  have : PreservesFiniteLimits
      (presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)) := inferInstance
  have hL : PreservesFiniteLimits (extendByInitialSheaf (C := ModuleCat.{0} ℚ) U) := by
    change PreservesFiniteLimits (sheafToPresheaf _ _ ⋙ (extendByInitialFunctor U ⋙
      presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)))
    infer_instance
  exact @preservesMonomorphisms_of_preservesLimitsOfShape _ _ _ _ _
    (hL.preservesFiniteLimits WalkingCospan)

/-- Restriction to an open subset, as a functor of sheaves of `ℚ`-vector spaces. -/
private noncomputable abbrev resF : TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤
    TopCat.Sheaf (ModuleCat.{0} ℚ) (sp U) :=
  Opens.sheafRestrict (C := ModuleCat.{0} ℚ) U

/-- Restriction to an open subset preserves injective sheaves of `ℚ`-vector spaces. -/
private lemma preservesInjectiveObjects_sheafRestrict : (resF U).PreservesInjectiveObjects :=
  have := preservesMonomorphisms_extendByInitialSheaf_rat U
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (extendByInitialSheafAdjunction U)

/-- `j^{-1} ⊣ j_*` for the inclusion `j` of an open subset. -/
private noncomputable abbrev resAdj :
    resF U ⊣ TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion' :=
  sheafRestrictPushforwardAdjunction U

private lemma preservesFiniteLimits_sheafRestrict : PreservesFiniteLimits (resF U) :=
  haveI : (resF U).IsRightAdjoint := (extendByInitialSheafAdjunction U).isRightAdjoint
  inferInstance

private lemma preservesFiniteColimits_sheafRestrict : PreservesFiniteColimits (resF U) :=
  haveI : (resF U).IsLeftAdjoint := (resAdj U).isLeftAdjoint
  inferInstance

private lemma additive_sheafRestrict : (resF U).Additive :=
  have := preservesFiniteLimits_sheafRestrict U
  Functor.additive_of_preserves_binary_products _

attribute [local instance] preservesInjectiveObjects_sheafRestrict
  preservesFiniteLimits_sheafRestrict
  preservesFiniteColimits_sheafRestrict additive_sheafRestrict

/-- `ℚ_Y|_U ≅ ℚ_U`, through the uniqueness of left adjoints of `j_*`. -/
private noncomputable def restrictConstIso : (resF U).obj (ratSheaf Y) ≅ ratSheaf (sp U) :=
  ((resAdj U).leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) U.inclusion')).app _ ≪≫
    constPullbackIso U.inclusion'

/-- `ℚ_Y ⟶ j_* ℚ_U` is the adjunct of `restrictConstIso`. -/
private lemma unit_comp_map_restrictConstIso_hom :
    (resAdj U).unit.app (ratSheaf Y) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion').map (restrictConstIso U).hom =
      constUnit U.inclusion' := by
  simp only [restrictConstIso, Iso.trans_hom, Iso.app_hom, Functor.map_comp]
  rw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
  change (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) U.inclusion').unit.app _ ≫
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion').map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) U.inclusion').homEquiv
        _ _).symm (constUnit U.inclusion')) = _
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) U.inclusion').homEquiv_unit
    _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The restriction of an injective resolution of `ℚ_Y` to an open subset `U` is an injective
resolution of `ℚ_U`. -/
private noncomputable def restrictResolution (J : InjectiveResolution (ratSheaf Y)) :
    InjectiveResolution (ratSheaf (sp U)) where
  cocomplex := ((resF U).mapHomologicalComplex _).obj J.cocomplex
  injective := ((resF U).mapInjectiveResolution J).injective
  ι := (CochainComplex.single₀ _).map (restrictConstIso U).inv ≫
    ((resF U).mapInjectiveResolution J).ι
  quasiIso := by
    have h1 := ((resF U).mapInjectiveResolution J).quasiIso
    have h2 : QuasiIso ((CochainComplex.single₀ _).map (restrictConstIso U).inv) := inferInstance
    exact @quasiIso_comp _ _ _ _ _ _ _ _ _ _ inferInstance inferInstance inferInstance h2 h1

private lemma restrictResolution_ι_f_zero (J : InjectiveResolution (ratSheaf Y)) :
    (restrictResolution U J).ι.f 0 = (restrictConstIso U).inv ≫ (resF U).map (J.ι.f 0) := by
  change (restrictConstIso U).inv ≫ ((HomologicalComplex.singleMapHomologicalComplex
    (resF U) (ComplexShape.up ℕ) 0).inv.app (ratSheaf Y)).f 0 ≫ (resF U).map (J.ι.f 0) = _
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso.hom, eqToIso.inv, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rfl

/-- The restriction map `J ⟶ j_* (J|_U)` of complexes. -/
private noncomputable def restrictionMap (J : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) Y) ℕ) :
    J ⟶ ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion').mapHomologicalComplex _).obj
      (((resF U).mapHomologicalComplex _).obj J) where
  f n := (resAdj U).unit.app (J.X n)
  comm' i j _ := ((resAdj U).unit.naturality (J.d i j)).symm

private lemma restrictionMap_f_zero (J : InjectiveResolution (ratSheaf Y)) :
    J.ι.f 0 ≫ (restrictionMap U J.cocomplex).f 0 = constUnit U.inclusion' ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion').map
        ((restrictResolution U J).ι.f 0) := by
  rw [restrictResolution_ι_f_zero, ← unit_comp_map_restrictConstIso_hom]
  refine ((resAdj U).unit.naturality (J.ι.f 0)).trans ?_
  have h2 : (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion').map (restrictConstIso U).hom ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion').map
        ((restrictConstIso U).inv ≫ (resF U).map (J.ι.f 0)) =
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion').map ((resF U).map (J.ι.f 0)) :=
    (Functor.map_comp _ _ _).symm.trans (congrArg _ (Iso.hom_inv_id_assoc _ _))
  exact (congrArg ((resAdj U).unit.app (ratSheaf Y) ≫ ·) h2.symm).trans (Category.assoc _ _ _).symm

end Restrict

section Supported

open Opposite

/-- Global sections, as a functor on sheaves of `ℚ`-vector spaces. -/
private noncomputable abbrev secF (Y : TopCat.{0}) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
  (sheafSections (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj (op ⊤)

private lemma secF_additive (Y : TopCat.{0}) : (secF Y).Additive := ⟨fun {_ _ _ _} => rfl⟩

attribute [local instance] secF_additive

variable {Y : TopCat.{0}} (U : Opens Y)

/-- **Supported representatives.** Let `J` be a complex of injective sheaves of `ℚ`-vector spaces
and `U ⊆ Y` open. A class of `H^{k+1}(Γ(Y, J))` restricting to zero on `U` is represented by a
cocycle vanishing on `U`: an injective sheaf is flasque, so a primitive on `U` of the restricted
cocycle extends to `Y`. -/
private lemma exists_cycles_restrict_eq_zero
    (J : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) Y) ℕ) (hJ : ∀ n, Injective (J.X n))
    (k : ℕ) (c : ToType ((((secF Y).mapHomologicalComplex _).obj J).homology (k + 1)))
    (hc : HomologicalComplex.homologyMap (((secF Y).mapHomologicalComplex _).map
      (restrictionMap U J)) (k + 1) c = 0) :
    ∃ z : ToType ((((secF Y).mapHomologicalComplex _).obj J).cycles (k + 1)),
      (((secF Y).mapHomologicalComplex _).obj J).homologyπ (k + 1) z = c ∧
      ((secF Y).map ((resAdj U).unit.app (J.X (k + 1))))
        ((((secF Y).mapHomologicalComplex _).obj J).iCycles (k + 1) z) = 0 := by
  let K := ((secF Y).mapHomologicalComplex _).obj J
  let g := ((secF Y).mapHomologicalComplex _).map (restrictionMap U J)
  obtain ⟨z₀, hz₀⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (k + 1))).1 inferInstance c
  have h1 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality g (k + 1)) z₀
  simp only [ConcreteCategory.comp_apply] at h1
  obtain ⟨y, hy⟩ := exists_d_eq_of_homologyπ_eq_zero _ (i := k)
    (ComplexShape.prev_eq' _ rfl) _ (h1.symm.trans (hz₀ ▸ hc))
  have hy' := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i g (k + 1)) z₀
  simp only [ConcreteCategory.comp_apply] at hy'
  obtain ⟨τ, hτ⟩ := surjective_map_of_injective (J.X k) (hJ k)
    (show U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion').obj ⊤) ≤ ⊤ from
      le_top) y
  have hgτ : g.f k τ = y := by
    change ((resAdj U).unit.app (J.X k)).hom.app (op ⊤) τ = y
    exact hτ
  have hcomm := ConcreteCategory.congr_hom (g.comm k (k + 1)) τ
  simp only [ConcreteCategory.comp_apply] at hcomm
  refine ⟨z₀ - K.toCycles k (k + 1) τ, ?_, ?_⟩
  · rw [map_sub, ← ConcreteCategory.comp_apply, K.toCycles_comp_homologyπ]
    change _ - 0 = _
    rw [sub_zero, hz₀]
  · rw [map_sub, map_sub, ← ConcreteCategory.comp_apply (K.toCycles k (k + 1)), K.toCycles_i]
    change g.f (k + 1) (K.iCycles (k + 1) z₀) - g.f (k + 1) (K.d k (k + 1) τ) = 0
    rw [← hcomm, hgτ, hy, hy', sub_self]

end Supported

section ExtendClass

/-- Under `extendHomologyMapIso`, the class of a cycle of the `ℤ`-indexed extension is the class of
the corresponding cycle of the `ℕ`-indexed complex. -/
private lemma extendHomologyMapIso_hom_homologyπ {A : Type*} [Category A] [Abelian A]
    (Γ : A ⥤ ModuleCat.{0} ℚ) [Γ.Additive] (K : CochainComplex A ℕ) (k : ℕ)
    (z : ToType (((Γ.mapHomologicalComplex _).obj K).cycles k))
    (zℤ : ToType (((Γ.mapHomologicalComplex _).obj
      (K.extend ComplexShape.embeddingUpNat)).cycles (k : ℤ)))
    (hz : ((Γ.mapHomologicalComplex _).obj (K.extend ComplexShape.embeddingUpNat)).iCycles k zℤ =
      Γ.map (K.extendXIso ComplexShape.embeddingUpNat rfl).inv
        (((Γ.mapHomologicalComplex _).obj K).iCycles k z)) :
    (extendHomologyMapIso Γ K k).hom
        (((Γ.mapHomologicalComplex _).obj (K.extend ComplexShape.embeddingUpNat)).homologyπ k zℤ) =
      ((Γ.mapHomologicalComplex _).obj K).homologyπ k z := by
  let φ := (Stacks.DerivedIndexing.mapExtendIsoSymm Γ ComplexShape.embeddingUpNat K).hom
  let L := (Γ.mapHomologicalComplex _).obj K
  change ((L.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom)
    ((HomologicalComplex.homologyMap φ (k : ℤ)) _) = _
  have h1 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ (k : ℤ)) zℤ
  have h2 := ConcreteCategory.congr_hom
    (L.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat (j := k) rfl)
    (HomologicalComplex.cyclesMap φ (k : ℤ) zℤ)
  simp only [ConcreteCategory.comp_apply] at h1 h2
  refine (congrArg (L.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom h1).trans ?_
  refine h2.trans (congrArg (L.homologyπ k) ?_)
  refine (ModuleCat.mono_iff_injective (L.iCycles k)).1 inferInstance ?_
  have h3 := ConcreteCategory.congr_hom
    (L.extendCyclesIso_hom_iCycles ComplexShape.embeddingUpNat (j := k) rfl)
    (HomologicalComplex.cyclesMap φ (k : ℤ) zℤ)
  have h4 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ (k : ℤ)) zℤ
  simp only [ConcreteCategory.comp_apply] at h3 h4
  refine h3.trans ?_
  have h5 : φ.f (k : ℤ) = Γ.map (K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
      (L.extendXIso ComplexShape.embeddingUpNat rfl).inv :=
    Stacks.DerivedIndexing.mapExtendXIsoSymm_hom_of_r_eq_some Γ ComplexShape.embeddingUpNat K
      (ComplexShape.embeddingUpNat.r_eq_some rfl)
  have h6 : (L.extendXIso ComplexShape.embeddingUpNat rfl).hom (φ.f (k : ℤ)
      (Γ.map (K.extendXIso ComplexShape.embeddingUpNat rfl).inv (L.iCycles k z))) =
      L.iCycles k z := by
    rw [h5]
    change ((Γ.map (K.extendXIso ComplexShape.embeddingUpNat rfl).inv ≫
      Γ.map (K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        (L.extendXIso ComplexShape.embeddingUpNat rfl).inv) ≫
          (L.extendXIso ComplexShape.embeddingUpNat rfl).hom) (L.iCycles k z) = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ← Γ.map_comp,
      Iso.inv_hom_id, Γ.map_id]
    rfl
  refine Eq.trans ?_ h6
  exact congrArg (L.extendXIso ComplexShape.embeddingUpNat rfl).hom (h4.trans (congrArg _ hz))

end ExtendClass

section ConstStalk

open Opposite

/-- Every element of a stalk of the constant sheaf `ℚ` is a multiple of the germ of the unit
section. -/
private lemma exists_eq_smul_germ_oneSection (Z : TopCat.{0}) (x : Z)
    (v : ToType ((ratSheaf Z).presheaf.stalk x)) :
    ∃ r : ℚ, v = r • (ratSheaf Z).presheaf.germ ⊤ x trivial (oneSection Z) := by
  let P : TopCat.Presheaf (ModuleCat.{0} ℚ) Z := (Functor.const (Opens Z)ᵒᵖ).obj (ModuleCat.of ℚ ℚ)
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ) P
  let e := (asIso ((TopCat.Presheaf.stalkFunctor _ x).map
    (toSheafify (Opens.grothendieckTopology Z) P))).toLinearEquiv
  obtain ⟨U, hxU, q, hq⟩ := TopCat.Presheaf.germ_exist P (x := x) (e.symm v)
  refine ⟨(show ℚ from q), ?_⟩
  have h1 : P.germ U x hxU q = (show ℚ from q) • P.germ ⊤ x trivial (1 : ℚ) := by
    have h0 : P.germ ⊤ x trivial (1 : ℚ) = P.germ U x hxU (1 : ℚ) :=
      (TopCat.Presheaf.germ_res_apply P (homOfLE le_top) x hxU (1 : ℚ)).symm
    rw [h0]
    have h2 : ((show ℚ from q) • (1 : ℚ) : ℚ) = (show ℚ from q) := mul_one _
    exact (congrArg _ h2.symm).trans ((P.germ U x hxU).hom.map_smul (show ℚ from q) (1 : ℚ))
  have h2 :
      e (P.germ ⊤ x trivial (1 : ℚ)) = (ratSheaf Z).presheaf.germ ⊤ x trivial (oneSection Z) := by
    change ((TopCat.Presheaf.stalkFunctor _ x).map (toSheafify (Opens.grothendieckTopology Z) P))
      (P.germ ⊤ x trivial (1 : ℚ)) = _
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl
  refine (e.apply_symm_apply v).symm.trans ?_
  refine (congrArg e (hq.symm.trans h1)).trans ?_
  exact (e.map_smul _ _).trans (congrArg _ h2)

end ConstStalk

section SupportedCocycle

open Opposite MMP MMP.SingularCochain

attribute [local instance] secF_additive

/-- **The cocycles of the summands.** Let `b : X' ⟶ X` be continuous, `X'` metrizable and locally
contractible, `W ⊆ X` open with `b⁻¹ W` locally contractible, and `γ ∈ H^{k+1}(X'; ℚ)` a class
vanishing on `b⁻¹ W`. Then for the injective resolution `J` of `b^{-1} ℚ_X` there is a cocycle
`ζ : ℚ_X ⟶ b_* J^{k+1}` whose stalks vanish on `W` and whose induced map `ℚ_X[-k-1] ⟶ Rb_* ℚ_{X'}`
is nonzero on the stalk of `H^{k+1}` at every point `x` with locally contractible fibre on which
`γ` restricts to a nonzero class. -/
private theorem exists_cocycle_of_relCohomology {X X' : TopCat.{0}} (b : X' ⟶ X)
    [MetrizableSpace X'] (hX' : LocallyContractibleSpace X') (W : Opens X)
    (hW : LocallyContractibleSpace ((Opens.toTopCat X').obj ((Opens.map b).obj W)))
    (n : ℤ) (m k : ℕ) (hm : m = k + 1) (hn : n = (m : ℤ))
    (γ : relCohomology ℚ ((Set.univ : Set X')ᶜ) m)
    (hγ : relCohomologyMap ℚ ((Opens.map b).obj W).inclusion'
      (MMP.Topology.compl_univ_subset_preimage _) m γ = 0) :
    let F := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) b
    haveI : F.Additive := Functor.additive_of_preserves_binary_products F
    let J := injectiveResolution ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) b).obj (ratSheaf X))
    ∃ (ζ : ratSheaf X ⟶ (F.mapCochainComplexPlus.obj J.plusObj).obj.X n)
      (hζd : ζ ≫ (F.mapCochainComplexPlus.obj J.plusObj).obj.d n (n + 1) = 0),
      (∀ x ∈ W, (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map ζ.hom = 0) ∧
      (∀ x : X, LocallyContractibleSpace (Fib b x) →
        relCohomologyMap ℚ (fibι b x) (MMP.Topology.compl_univ_subset_preimage _) m γ ≠ 0 →
        (stalkH n x).map (DerivedCategory.Plus.Qh.map (singleHomOfCocycle _ ζ hζd)) ≠ 0) := by
  intro F J
  subst hm
  subst hn
  obtain ⟨E, hE⟩ := exists_homology_globalSections_injectiveResolution_iso_relCohomology
  let U := (Opens.map b).obj W
  let eQ : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) b).obj (ratSheaf X) ≅ ratSheaf X' :=
    constPullbackIso b
  let J' : InjectiveResolution (ratSheaf X') := InjectiveResolution.ofIso eQ.symm J
  let JU := restrictResolution U J'
  haveI : MetrizableSpace ((Opens.toTopCat X').obj U) :=
    inferInstanceAs (MetrizableSpace ↥(U : Set X'))
  let c := (E X' hX' J' (k + 1)).inv γ
  have hcγ : (E X' hX' J' (k + 1)).hom c = γ := by
    change ((E X' hX' J' (k + 1)).inv ≫ (E X' hX' J' (k + 1)).hom) γ = γ
    rw [Iso.inv_hom_id]
    rfl
  have hc : HomologicalComplex.homologyMap (((secF X').mapHomologicalComplex _).map
      (restrictionMap U J'.cocomplex)) (k + 1) c = 0 := by
    have hnat := hE X' ((Opens.toTopCat X').obj U) hX' hW U.inclusion' J' JU
      (restrictionMap U J'.cocomplex) (restrictionMap_f_zero U J') (k + 1)
    have h1 := ConcreteCategory.congr_hom hnat c
    simp only [ConcreteCategory.comp_apply] at h1
    apply (ModuleCat.mono_iff_injective (E ((Opens.toTopCat X').obj U) hW JU (k + 1)).hom).1
      inferInstance
    exact h1.trans <| (congrArg (fun t => relCohomologyMap ℚ U.inclusion'
      (MMP.Topology.compl_univ_subset_preimage _) (k + 1) t) hcγ).trans (hγ.trans (map_zero _).symm)
  obtain ⟨z, hzc, hz0⟩ := exists_cycles_restrict_eq_zero U J'.cocomplex J'.injective k c hc
  let K := ((secF X').mapHomologicalComplex _).obj J'.cocomplex
  let σℕ := K.iCycles (k + 1) z
  let xiso := J.cocomplex.extendXIso ComplexShape.embeddingUpNat
    (i' := ((k + 1 : ℕ) : ℤ)) (i := k + 1) rfl
  let σ : ToType ((secF X').obj (J.cochainComplex.X ((k + 1 : ℕ) : ℤ))) := (secF X').map xiso.inv σℕ
  let adj := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) isTerminalTop
  let ζ : ratSheaf X ⟶ F.obj (J.cochainComplex.X ((k + 1 : ℕ) : ℤ)) :=
    (adj.homEquiv _ _).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ σ))
  have hζσ : ζ.hom.app (op ⊤) (oneSection X) = σ := by
    have h := (adj.homEquiv_unit (ModuleCat.of ℚ ℚ) _ ζ).symm.trans (Equiv.apply_symm_apply _ _)
    have h1 := ConcreteCategory.congr_hom h (1 : ℚ)
    refine h1.trans ?_
    change (LinearMap.toSpanSingleton ℚ _ σ) (1 : ℚ) = σ
    rw [LinearMap.toSpanSingleton_apply, one_smul]
  have hd : (secF X').map (J.cochainComplex.d ((k + 1 : ℕ) : ℤ) (((k + 1 : ℕ) : ℤ) + 1)) σ = 0 := by
    have hσℕ : K.d (k + 1) (k + 2) σℕ = 0 := by
      have := ConcreteCategory.congr_hom (K.iCycles_d (k + 1) (k + 2)) z
      exact this
    have e1 := HomologicalComplex.extend_d_eq J.cocomplex ComplexShape.embeddingUpNat
      (i' := ((k + 1 : ℕ) : ℤ)) (j' := ((k + 1 : ℕ) : ℤ) + 1) (i := k + 1) (j := k + 2) rfl
      (by simp; omega)
    change (secF X').map ((J.cocomplex.extend ComplexShape.embeddingUpNat).d _ _)
      ((secF X').map xiso.inv σℕ) = 0
    rw [e1]
    change ((secF X').map xiso.inv ≫ (secF X').map (xiso.hom ≫ _ ≫ _)) σℕ = 0
    rw [← Functor.map_comp, Iso.inv_hom_id_assoc, Functor.map_comp]
    change (secF X').map _ (K.d (k + 1) (k + 2) σℕ) = 0
    exact (congrArg _ hσℕ).trans (map_zero _)
  have hζd : ζ ≫ (F.mapCochainComplexPlus.obj J.plusObj).obj.d ((k + 1 : ℕ) : ℤ)
      (((k + 1 : ℕ) : ℤ) + 1) = 0 := by
    have h0 : ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ σ) ≫
        ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (op ⊤)).map
          ((F.mapCochainComplexPlus.obj J.plusObj).obj.d ((k + 1 : ℕ) : ℤ)
            (((k + 1 : ℕ) : ℤ) + 1)) = 0 := by
      ext1
      apply LinearMap.ext_ring
      change (secF X').map (J.cochainComplex.d ((k + 1 : ℕ) : ℤ) (((k + 1 : ℕ) : ℤ) + 1))
        ((LinearMap.toSpanSingleton ℚ _ σ) (1 : ℚ)) = 0
      rw [LinearMap.toSpanSingleton_apply, one_smul]
      exact hd
    refine (adj.homEquiv_naturality_right_symm _ _).symm.trans ?_
    refine (congrArg (adj.homEquiv _ _).symm h0).trans ?_
    refine (adj.homEquiv_counit _ _ _).trans ?_
    exact (congrArg (· ≫ _) (Functor.map_zero _ _ _)).trans zero_comp
  have hσU : (J.cochainComplex.X ((k + 1 : ℕ) : ℤ)).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op σ = 0 := by
    have hU0 : (J.cocomplex.X (k + 1)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op σℕ = 0 := by
      have hle : U ≤ U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion').obj ⊤) := by
        intro y hy
        exact ⟨⟨y, hy⟩, trivial, rfl⟩
      have h1 : (J.cocomplex.X (k + 1)).presheaf.map (homOfLE (le_top :
          U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion').obj ⊤) ≤ ⊤)).op σℕ =
            0 := hz0
      have h2 : (J.cocomplex.X (k + 1)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op =
          (J.cocomplex.X (k + 1)).presheaf.map (homOfLE (le_top :
            U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion').obj ⊤) ≤ ⊤)).op ≫
          (J.cocomplex.X (k + 1)).presheaf.map (homOfLE hle).op := by
        rw [← Functor.map_comp]
        rfl
      rw [h2]
      exact (congrArg ((J.cocomplex.X (k + 1)).presheaf.map (homOfLE hle).op) h1).trans
        (map_zero _)
    have h3 := ConcreteCategory.congr_hom (xiso.inv.hom.naturality (homOfLE (le_top : U ≤ ⊤)).op)
      σℕ
    exact h3.symm.trans ((congrArg (xiso.inv.hom.app (op U)) hU0).trans (map_zero _))
  refine ⟨ζ, hζd, ?_, ?_⟩
  · intro x hx
    ext v
    obtain ⟨r, rfl⟩ := exists_eq_smul_germ_oneSection X x v
    refine (LinearMap.map_smul _ r _).trans ?_
    refine (congrArg (r • ·) ?_).trans (smul_zero r)
    refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial ζ.hom (oneSection X)).trans ?_
    refine (congrArg _ hζσ).trans ?_
    refine (TopCat.Presheaf.germ_res_apply (F.obj (J.cochainComplex.X ((k + 1 : ℕ) : ℤ))).presheaf
      (homOfLE (le_top : W ≤ ⊤)) x hx σ).symm.trans ?_
    exact (congrArg _ hσU).trans (map_zero _)
  · intro x hFx hγx
    let ι := fibι b x
    let Ix := injectiveResolution (ratSheaf (Fib b x))
    haveI : MetrizableSpace (Fib b x) := inferInstanceAs (MetrizableSpace ↥(b ⁻¹' {x}))
    obtain ⟨g, hg⟩ := exists_hom_resolution_pushforward ι J' Ix
    let ρ := extendMapPush (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) ι) g
    refine stalkH_map_singleHomOfCocycle_ne_zero b x J.plusObj ρ ζ hζd (oneSection X) ?_
    intro hy hπ
    -- the restriction to the fibre of the germ of `ζ(1)`
    have hy' : (fibreStalkComplexHom b x ρ).f _ ((TopCat.Presheaf.stalkFunctor _ x).map ζ.hom
        ((ratSheaf X).presheaf.germ ⊤ x trivial (oneSection X))) = (secF X').map (ρ.f _) σ := by
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hζσ, fibreStalkComplexHom_f_germ]
      rfl
    let Kℤ := ((secF X').mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex
    let φ := ((secF X').mapHomologicalComplex (ComplexShape.up ℤ)).map ρ
    have hdσ : (forget₂ (ModuleCat.{0} ℚ) Ab).map (Kℤ.d ((k + 1 : ℕ) : ℤ) (((k + 1 : ℕ) : ℤ) + 1))
        σ = 0 := hd
    let zℤ := Kℤ.cyclesMk σ (((k + 1 : ℕ) : ℤ) + 1) (by simp) hdσ
    have h1 := cyclesMap_cyclesMk φ σ (((k + 1 : ℕ) : ℤ) + 1) (by simp) hdσ
    have h3 : HomologicalComplex.homologyMap φ ((k + 1 : ℕ) : ℤ)
        (Kℤ.homologyπ ((k + 1 : ℕ) : ℤ) zℤ) = 0 := by
      have e1 := ConcreteCategory.congr_hom
        (HomologicalComplex.homologyπ_naturality φ ((k + 1 : ℕ) : ℤ)) zℤ
      refine e1.trans ?_
      have e2 := h1.trans (cyclesMk_congr _ hy'.symm _ _ _ hy)
      exact (congrArg _ e2).trans hπ
    have hnatF := extendHomologyMapIso_naturality
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) ι) (secF X') g (k + 1)
    have h4 := ConcreteCategory.congr_hom hnatF (Kℤ.homologyπ ((k + 1 : ℕ) : ℤ) zℤ)
    have h5 := extendHomologyMapIso_hom_homologyπ (secF X') J'.cocomplex (k + 1) z zℤ
      (HomologicalComplex.i_cyclesMk Kℤ σ _ _ hdσ)
    have h6 : HomologicalComplex.homologyMap (((secF X').mapHomologicalComplex _).map g) (k + 1)
        c = 0 := by
      rw [← hzc, ← h5]
      exact h4.symm.trans ((congrArg (ConcreteCategory.hom (extendHomologyMapIso
        (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) ι ⋙ secF X') Ix.cocomplex
          (k + 1)).hom) h3).trans
          (map_zero _))
    have h7 := ConcreteCategory.congr_hom (hE X' (Fib b x) hX' hFx ι J' Ix g hg (k + 1)) c
    apply hγx
    refine Eq.trans ?_ (h7.symm.trans ((congrArg (ConcreteCategory.hom
      (E (Fib b x) hFx Ix (k + 1)).hom) h6).trans (map_zero _)))
    exact (congrArg (fun t => relCohomologyMap ℚ ι
      (MMP.Topology.compl_univ_subset_preimage _) (k + 1) t) hcγ).symm

end SupportedCocycle

section SectionBar

open MMP MMP.UnderlyingSpace

/-- The section `σ̄` of an orientation datum vanishes on the subscheme: there the local
coordinates of `σ` vanish, and the quotient map is linear on the fibres. -/
private lemma sectionBar_eq_zeroSection {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] [IsClosedImmersion i] {d : ℕ}
    (D : MMP.Modules.RegularImbeddingOrientationDatum i d) (y : D.nbhd)
    (hy : y.1 ∈ Set.range (UnderlyingSpace.map (K := ℂ) i)) :
    D.sectionBar y = Bundle.zeroSection D.F D.Q y := by
  obtain ⟨c, hc₀⟩ := MMP.Modules.exists_mem_chartBase D.E D.rank y.1
  have hc : ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1 := hc₀
  obtain ⟨L, hL, -, -⟩ := D.fibre c y.1 hc y.2
  have hW : c.1.1 ≤ D.σ ⁻¹ᵁ (MMP.Modules.proj D.E ⁻¹ᵁ c.1.1) :=
    (MMP.Modules.preimage_preimage_proj_of_comp_eq_id D.comp_proj _).ge
  have hsupp : y.1.toHom (IsLocalRing.closedPoint ℂ) ∈ i.ker.support := by
    have hy' : y.1 ∈ Set.range (mapFun (K := ℂ) i) := hy
    rw [range_mapFun_of_isClosedImmersion] at hy'
    have h2 : y.1.toHom (IsLocalRing.closedPoint ℂ) ∈ closure (Set.range i) := subset_closure hy'
    rwa [← Scheme.Hom.support_ker] at h2
  have h0 : MMP.Modules.coord c (mapFun D.σ y.1) = 0 := funext fun a ↦ by
    rw [← MMP.Modules.eval_sectionCoord D.σ c hW y.1 hc a]
    refine MMP.Topology.eval_eq_zero_of_mem_ideal i.ker c.1 y.1 hc hsupp ?_
    rw [← D.zeroLocus_eq, MMP.Modules.ideal_zeroLocus D.σ c c.1 hW]
    exact Ideal.subset_span ⟨a, rfl⟩
  have hs := MMP.Modules.mapFun_eq_chartInv_coord D.comp_proj c y.1 hc
  rw [h0] at hs
  have h1 : D.sectionBar y = D.quot ⟨MMP.Modules.chartInv c y.1 hc 0, by
      rw [MMP.Modules.mapFun_proj_chartInv]; exact y.2⟩ :=
    congrArg D.quot (Subtype.ext hs)
  rw [h1, hL 0, map_zero]
  rfl

end SectionBar

section DivisorClass

open MMP MMP.UnderlyingSpace MMP.Topology Set

/-- **The class of the exceptional divisor.** For a smooth blowup `b : V' ⟶ V` along a centre of
pure codimension `c ≥ 2`, with exceptional divisor `R`, the orientation class of `R` gives a
class `ε ∈ H²(V'(ℂ); ℚ)` which vanishes on every space mapping into `V'(ℂ) ∖ b⁻¹(T)` and
restricts to a nonzero class on every fibre `b⁻¹(t)`, `t ∈ T(ℂ)`: there it is the Euler class of
the normal bundle of `R`. -/
private theorem exists_class_exceptionalDivisor {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    (I : V.IdealSheafData) [(blowUp I).Over (Spec (.of ℂ))]
    [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hI : MMP.Resolution.IsSmoothBlowup (V ↘ Spec (.of ℂ)) I) (c : ℕ) (hc : 2 ≤ c)
    (hcodim : ∀ Z : IrreducibleCloseds V,
      Maximal (fun W : IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z → codimension Z = c) :
    ∃ ε : relativeSingularCohomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (UnderlyingSpace ℂ (blowUp I))) (univ : Set _)ᶜ ((2 * 1 : ℕ) : ℤ),
      (∀ (Z : TopCat.{0}) (g : Z ⟶ TopCat.of (UnderlyingSpace ℂ (blowUp I))),
        (∀ z, (mapFun (blowUpToBase I) (g z)).toHom (IsLocalRing.closedPoint ℂ) ∉ I.support) →
        (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) g (A' := univᶜ)
          (fun x hx ↦ (hx (mem_univ x)).elim) _).hom ε = 0) ∧
      (∀ t : UnderlyingSpace ℂ V, t.toHom (IsLocalRing.closedPoint ℂ) ∈ I.support →
        (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            TopCat.of (mapFun (blowUpToBase I) ⁻¹' {t}) ⟶
              TopCat.of (UnderlyingSpace ℂ (blowUp I)))
          (A' := univᶜ) (fun x hx ↦ (hx (mem_univ x)).elim) _).hom ε ≠ 0) := by
  obtain ⟨D, hDE⟩ : ∃ D, D = exceptionalIdeal I := ⟨_, rfl⟩
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor D := hDE ▸ inferInstance
  letI : D.subscheme.Over (Spec (.of ℂ)) := ⟨D.subschemeι ≫ (blowUp I ↘ Spec (.of ℂ))⟩
  haveI : D.subschemeι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  let Dd := divisorOrientationDatum D
  let Y := TopCat.of (UnderlyingSpace ℂ (blowUp I))
  let R0 : Set Y := range (UnderlyingSpace.map (K := ℂ) D.subschemeι)
  have hR0 : IsClosed R0 :=
    (UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion _).isClosed_range
  have hR0' : ∀ p ∈ R0,
      (mapFun (blowUpToBase I) p).toHom (IsLocalRing.closedPoint ℂ) ∈ I.support := by
    intro p hp
    change p ∈ range (mapFun (K := ℂ) D.subschemeι) at hp
    rw [range_mapFun_of_isClosedImmersion] at hp
    change p.toHom (IsLocalRing.closedPoint ℂ) ∈ range D.subschemeι at hp
    rw [Scheme.IdealSheafData.range_subschemeι, hDE, exceptionalIdeal,
      Scheme.IdealSheafData.support_comap] at hp
    rw [toHom_mapFun]
    exact hp
  let incl : TopCat.of Dd.nbhd ⟶ Y := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hincl : Topology.IsOpenEmbedding incl := Dd.isOpen_nbhd.isOpenEmbedding_subtypeVal
  have hR0W : R0 ⊆ range incl := fun p hp ↦ ⟨⟨p, Dd.range_subset_nbhd hp⟩, rfl⟩
  let m : ℤ := ((2 * Module.finrank ℂ Dd.F : ℕ) : ℤ)
  let iso := openEmbeddingPullbackIso ℚ incl hincl hR0 hR0W m
  let uQ := ThomClass.thomClass ℚ Dd.F Dd.Q
  have hsb : (incl ⁻¹' R0)ᶜ ⊆ Dd.sectionBarHom ⁻¹' (range (Bundle.zeroSection Dd.F Dd.Q))ᶜ :=
    fun y hy hy0 ↦ hy (Dd.sectionBar_preimage_subset hy0)
  let v := (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) Dd.sectionBarHom hsb m).hom uQ
  let v' := iso.inv v
  have he : (univ : Set Y)ᶜ ⊆ (𝟙 Y) ⁻¹' R0ᶜ := fun x hx ↦ (hx (mem_univ x)).elim
  let ε₀ := (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (𝟙 Y) he m).hom v'
  have hF : 2 * Module.finrank ℂ Dd.F = 2 * 1 := congrArg (2 * ·) Dd.finrank_F
  refine ⟨cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology ℚ (ModuleCat.of ℚ ℚ) Y
    (univᶜ) (k : ℤ) : Type)) hF) ε₀, ?_, ?_⟩
  · intro Z g hg
    have hgR : (univ : Set Z) ⊆ g ⁻¹' R0ᶜ := fun z _ hz ↦ hg z (hR0' _ hz)
    refine (cast_map_relativeSingularCohomology g _ hF ε₀).symm.trans ?_
    rw [cast_relativeSingularCohomology_eq_zero_iff hF]
    have hsub := subsingleton_relativeSingularCohomology_univ ℚ Z m
    refine ((relativeSingularCohomology.map_comp_apply' ℚ (g := g) (f := 𝟙 Y) _ he
      (fun x hx ↦ (hx (mem_univ x)).elim) m v').symm).trans ?_
    refine (relativeSingularCohomology.map_congr_apply ℚ
      ((Category.comp_id g).trans (Category.id_comp g).symm) _
      (fun x hx ↦ (hx (mem_univ x)).elim) m v').trans ?_
    refine (relativeSingularCohomology.map_comp_apply' ℚ (g := 𝟙 Z) (f := g) (A' := univ)
      (fun x hx ↦ (hx (mem_univ x)).elim) hgR _ m v').trans ?_
    rw [Subsingleton.elim ((relativeSingularCohomology.map ℚ _ g hgR m).hom v') 0, map_zero]
  · intro t ht h0
    have hsub := preimage_singleton_subset_nbhd_divisorOrientationDatum D hDE ht
    let ι0 : C(↥(mapFun (blowUpToBase I) ⁻¹' {t}), Dd.nbhd) :=
      ⟨fun p ↦ ⟨p.1, hsub p.2⟩, by fun_prop⟩
    have hne := map_eulerClass_divisorOrientationDatum_ne_zero D hI c hc hcodim hDE t ht ι0
      (fun _ ↦ rfl)
    apply hne
    have h1 := (cast_relativeSingularCohomology_eq_zero_iff hF _).1
      ((cast_map_relativeSingularCohomology _ _ hF ε₀).trans h0)
    refine Eq.trans ?_ h1
    have hz : TopCat.ofHom ι0 ≫ Dd.sectionBarHom =
        TopCat.ofHom ι0 ≫ bundleZeroSection Dd.F Dd.Q := by
      refine TopCat.hom_ext (ContinuousMap.ext fun p ↦ ?_)
      exact sectionBar_eq_zeroSection Dd (ι0 p)
        (mem_range_map_subschemeι_of_mapFun_eq D hDE ht p.2)
    have hvi : (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) incl (fun _ hx ↦ hx) m).hom v' =
        v := by
      change (iso.inv ≫ iso.hom) v = v
      rw [Iso.inv_hom_id]
      rfl
    have hE : (univ : Set _)ᶜ ⊆ (TopCat.ofHom ι0) ⁻¹' (incl ⁻¹' R0)ᶜ :=
      fun x hx ↦ (hx (mem_univ x)).elim
    have hE' : (univ : Set (TopCat.of Dd.nbhd))ᶜ ⊆
        (bundleZeroSection Dd.F Dd.Q) ⁻¹' (range (Bundle.zeroSection Dd.F Dd.Q))ᶜ :=
      fun x hx ↦ (hx (mem_univ x)).elim
    change (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom ι0) _ m).hom
      ((relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (bundleZeroSection Dd.F Dd.Q) hE' m).hom
        uQ) = _
    refine ((relativeSingularCohomology.map_comp_apply' ℚ _ hE'
      (fun x hx ↦ (hx (mem_univ x)).elim) m uQ).symm).trans ?_
    refine (relativeSingularCohomology.map_congr_apply ℚ hz.symm _
      (fun x hx ↦ (hx (mem_univ x)).elim) m uQ).trans ?_
    refine (relativeSingularCohomology.map_comp_apply' ℚ hE hsb
      (fun x hx ↦ (hx (mem_univ x)).elim) m uQ).trans ?_
    refine (congrArg _ hvi.symm).trans ?_
    refine ((relativeSingularCohomology.map_comp_apply' ℚ (g := TopCat.ofHom ι0) (f := incl)
      (A := R0ᶜ) hE (fun _ hx ↦ hx) (fun x hx ↦ (hx (mem_univ x)).elim) m v').symm).trans ?_
    refine Eq.trans ?_ (relativeSingularCohomology.map_comp_apply' ℚ
      (fun x hx ↦ (hx (mem_univ x)).elim) he (fun x hx ↦ (hx (mem_univ x)).elim) m v')
    exact relativeSingularCohomology.map_congr_apply ℚ (by rfl) _ _ m v'

end DivisorClass

section CupPowers

open MMP

/-- The cup powers of the zero class vanish. -/
private lemma cupPowSucc_zero_left {Y : TopCat.{0}} (a : ℕ) :
    MMP.Topology.cupPowSucc ℚ
      (0 : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y Set.univ (2 * 1 : ℕ)) a = 0 := by
  cases a with
  | zero => rfl
  | succ a => rw [MMP.Topology.cupPowSucc_succ, map_zero]

end CupPowers

section AnalyticClasses

open MMP MMP.SingularCochain MMP.UnderlyingSpace Set

/-- **The classes of the summands.** For a smooth blowup `b : V' ⟶ V` along a centre `T` of pure
codimension `c ≥ 2`, the powers `ε^{a+1}`, `a < c - 1`, of the class of the exceptional divisor are
classes of `H^{2(a+1)}(V'^an; ℚ)` vanishing on `b⁻¹(V ∖ T)` and nonzero on every fibre over `T`. -/
private theorem exists_relCohomology_classes {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (I : V.IdealSheafData) (hI : MMP.Resolution.IsSmoothBlowup sV I) (c : ℕ) (hc : 2 ≤ c)
    (hcodim : ∀ Z : IrreducibleCloseds V,
      Maximal (fun W : IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z → codimension Z = c)
    (W : Opens (analyticSpace sV)) (hW : ∀ x, x ∈ W ↔ x.toScheme ∉ I.support) :
    let bAn := analyticMap (blowUpToBase I) rfl
    ∃ γ : ∀ a : Fin (c - 1), relCohomology ℚ
        ((univ : Set (analyticSpace (blowUpToBase I ≫ sV)))ᶜ) (2 * ((a : ℕ) + 1)),
      (∀ a, relCohomologyMap ℚ ((Opens.map bAn).obj W).inclusion'
        (MMP.Topology.compl_univ_subset_preimage _) _ (γ a) = 0) ∧
      (∀ a, ∀ x : analyticSpace sV, x.toScheme ∈ I.support →
        relCohomologyMap ℚ (fibι bAn x) (MMP.Topology.compl_univ_subset_preimage _) _
          (γ a) ≠ 0) := by
  intro bAn
  letI : V.Over (Spec (.of ℂ)) := ⟨sV⟩
  letI : (blowUp I).Over (Spec (.of ℂ)) := ⟨blowUpToBase I ≫ sV⟩
  haveI : (blowUpToBase I).IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  obtain ⟨ε, hε0, hεF⟩ := exists_class_exceptionalDivisor I hI c hc hcodim
  let hY := homeomorphUnderlyingSpace (X := blowUp I)
  let hYm : analyticSpace (blowUpToBase I ≫ sV) ⟶ TopCat.of (UnderlyingSpace ℂ (blowUp I)) :=
    TopCat.ofHom ⟨hY, hY.continuous⟩
  let εX := (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) hYm
    (MMP.Topology.compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom ε
  have hpt : ∀ z, mapFun (blowUpToBase I) (hY z) = homeomorphUnderlyingSpace (X := V) (bAn z) :=
    fun z ↦ rfl
  have htoS : ∀ x : analyticSpace sV,
      (homeomorphUnderlyingSpace (X := V) x).toHom (IsLocalRing.closedPoint ℂ) = x.toScheme :=
    fun x ↦ congrArg x.hom (Subsingleton.elim _ _)
  refine ⟨fun a ↦ relativeSingularCohomologyEquiv ℚ _ _ (MMP.Topology.cupPowSucc ℚ εX a), ?_, ?_⟩
  · intro a
    let U := (Opens.map bAn).obj W
    have h1 : (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) U.inclusion'
        (MMP.Topology.compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom εX = 0 := by
      refine (MMP.Topology.relativeSingularCohomology_map_map_apply ℚ U.inclusion' hYm _ _
        (fun x hx ↦ (hx (mem_univ x)).elim) _ ε).trans ?_
      refine hε0 _ (U.inclusion' ≫ hYm) (fun z hz ↦ ?_)
      exact (hW _).1 z.2 (htoS (bAn z.1) ▸ hz)
    refine ((relativeSingularCohomologyEquiv_map U.inclusion' _ _ _).symm).trans ?_
    rw [MMP.Topology.map_cupPowSucc, h1, cupPowSucc_zero_left, map_zero]
  · intro a x hx h0
    obtain ⟨e⟩ := MMP.Topology.nonempty_homeomorph_preimage_analyticMap_blowUpToBase_of_codimension
      sV I hI c (by omega) hcodim x hx
    let t := homeomorphUnderlyingSpace (X := V) x
    have ht : t.toHom (IsLocalRing.closedPoint ℂ) ∈ I.support := (htoS x).symm ▸ hx
    have hne := hεF t ht
    let Ft := TopCat.of (mapFun (blowUpToBase I) ⁻¹' {t})
    let jt : Ft ⟶ TopCat.of (UnderlyingSpace ℂ (blowUp I)) :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let ψ : Fib bAn x ⟶ Ft := TopCat.ofHom ⟨fun p ↦ ⟨hY p.1,
      (hpt p.1).trans (congrArg _ p.2)⟩,
      (hY.continuous.comp continuous_subtype_val).subtype_mk _⟩
    let θ : Ft ⟶ Fib bAn x := TopCat.ofHom ⟨fun q ↦ ⟨hY.symm q.1,
      (homeomorphUnderlyingSpace (X := V)).injective ((hpt _).symm.trans
        ((congrArg (mapFun (blowUpToBase I)) (hY.apply_symm_apply q.1)).trans q.2))⟩,
      (hY.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hθψ : θ ≫ ψ = 𝟙 _ :=
      TopCat.hom_ext (ContinuousMap.ext fun q ↦ Subtype.ext (hY.apply_symm_apply q.1))
    have hjψ : fibι bAn x ≫ hYm = ψ ≫ jt := rfl
    let y := (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (fibι bAn x)
      (MMP.Topology.compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom εX
    have hy : y ≠ 0 := by
      intro hy0
      apply hne
      have h2 : (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) ψ
          (MMP.Topology.compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom
          ((relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) jt
            (MMP.Topology.compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom ε) = 0 :=
        (MMP.Topology.relativeSingularCohomology_map_map_apply ℚ ψ jt
          (MMP.Topology.compl_univ_subset_preimage _) (MMP.Topology.compl_univ_subset_preimage _)
          (MMP.Topology.compl_univ_subset_preimage _) _ ε).trans
          ((relativeSingularCohomology.map_congr_apply ℚ hjψ.symm
            (MMP.Topology.compl_univ_subset_preimage _) (MMP.Topology.compl_univ_subset_preimage _)
            _ ε).trans
            ((MMP.Topology.relativeSingularCohomology_map_map_apply ℚ (fibι bAn x) hYm
              (MMP.Topology.compl_univ_subset_preimage _)
              (MMP.Topology.compl_univ_subset_preimage _)
              (MMP.Topology.compl_univ_subset_preimage _) _ ε).symm.trans hy0))
      refine (MMP.Topology.relativeSingularCohomology_map_map_apply_of_comp_eq_id ℚ θ ψ hθψ
        (MMP.Topology.compl_univ_subset_preimage _) (MMP.Topology.compl_univ_subset_preimage _) _
        ((relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) jt
          (MMP.Topology.compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom ε)).symm.trans ?_
      exact (congrArg _ h2).trans (map_zero _)
    have h3 : (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (fibι bAn x)
        (MMP.Topology.compl_univ_subset_preimage _) (2 * ((a : ℕ) + 1) : ℕ)).hom
        (MMP.Topology.cupPowSucc ℚ εX a) = 0 := by
      apply (relativeSingularCohomologyEquiv ℚ _ _).injective
      rw [relativeSingularCohomologyEquiv_map, map_zero]
      exact h0
    rw [MMP.Topology.map_cupPowSucc] at h3
    let φ : MMP.Topology.complexProjectiveSpace (c - 1) ⟶ Fib bAn x :=
      TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
    let θ' : Fib bAn x ⟶ MMP.Topology.complexProjectiveSpace (c - 1) :=
      TopCat.ofHom ⟨e, e.continuous⟩
    have hθφ : θ' ≫ φ = 𝟙 _ :=
      TopCat.hom_ext (ContinuousMap.ext fun p ↦ e.symm_apply_apply p)
    have hφ : (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) φ
        (MMP.Topology.compl_univ_subset_preimage _) (2 * 1 : ℕ)).hom y ≠ 0 := fun h ↦
      hy ((MMP.Topology.relativeSingularCohomology_map_map_apply_of_comp_eq_id ℚ θ' φ hθφ
        (MMP.Topology.compl_univ_subset_preimage _) (MMP.Topology.compl_univ_subset_preimage _) _
          y).symm.trans ((congrArg _ h).trans (map_zero _)))
    refine MMP.Topology.cupPowSucc_ne_zero ℚ a.2 _ hφ ?_
    rw [← MMP.Topology.map_cupPowSucc]
    exact (congrArg _ h3).trans (map_zero _)

end AnalyticClasses

/-- A functor kills `f` once it kills `f` followed by an isomorphism. -/
private lemma map_eq_zero_of_map_comp_iso {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    [Limits.HasZeroMorphisms 𝒟] (G : 𝒞 ⥤ 𝒟) {A B B' : 𝒞} (f : A ⟶ B) (e : B ≅ B')
    (h : G.map (f ≫ e.hom) = 0) : G.map f = 0 := by
  have : G.map f = G.map (f ≫ e.hom) ≫ G.map e.inv := by
    rw [← G.map_comp, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [this, h, Limits.zero_comp]

/-- The input of `exists_isIso_stalk_homology_biprod_desc` for a smooth-centre blowup: the
locus `T` of the centre, a model `C` of `Rb_* ℚ_{V'}` by a bounded below complex, the stalk
ranks of the cohomology sheaves of `Rb_* ℚ_{V'}` (those of `ℙ^{c-1}` at points of `T`, of a
point elsewhere), and cocycles `ζ a : ℚ_V ⟶ C^{2(a+1)}`, zero off `T`, representing the powers
`ε^{a+1}` on the fibres. -/
private theorem exists_splitting_data {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) [IsIntegral V] [IsSeparated sV] [LocallyOfFiniteType sV]
    [QuasiCompact sV]
    (I : V.IdealSheafData) (hI : MMP.Resolution.IsSmoothBlowup sV I)
    (c : ℕ) (hc : 2 ≤ c)
    (hcodim : ∀ Z : IrreducibleCloseds V,
      Maximal (fun W : IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z → codimension Z = c) :
    let bAn := analyticMap (blowUpToBase I) rfl
    let iAn := analyticMap I.subschemeι rfl
    let QV : TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sV) :=
      (constantSheaf (Opens.grothendieckTopology (analyticSpace sV)) (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ ℚ)
    (let F := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) bAn
    haveI : F.Additive := Functor.additive_of_preserves_binary_products F
    let QV' := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) bAn).obj QV
    let η := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) bAn).unit.app QV
    let S := HomotopyCategory.Plus.singleFunctor (TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sV))
    let S' := HomotopyCategory.Plus.singleFunctor
      (TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace (blowUpToBase I ≫ sV)))
    let m : (S 0).obj QV ⟶ F.mapHomotopyCategoryPlus.obj ((S' 0).obj QV') :=
      (HomotopyCategory.Plus.ι _).preimage ((HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single _ _ 0).map η ≫
          (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app QV'))
    let unit := DerivedCategory.Plus.Qh.map m ≫ F.rightDerivedFunctorPlusUnith.app ((S' 0).obj QV')
    let iQ : TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sV) :=
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) iAn).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) iAn).obj QV)
    let p : QV ⟶ iQ :=
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) iAn).unit.app QV
    let K := F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj ((S' 0).obj QV'))
    ∃ (T : Set (analyticSpace sV))
      (C : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sV)))
      (M : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj C) ≅ K)
      (ζ : ∀ a : Fin (c - 1), QV ⟶ C.obj.X (2 * (a + 1 : ℕ)))
      (hζd : ∀ a, ζ a ≫ C.obj.d (2 * (a + 1 : ℕ)) (2 * (a + 1 : ℕ) + 1) = 0),
      (∀ x, Module.rank ℚ (QV.presheaf.stalk x) ≤ 1) ∧
      (∀ x ∈ T, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map p.hom)) ∧
      (∀ x ∉ T, Subsingleton (iQ.presheaf.stalk x)) ∧
      (∀ x, Module.rank ℚ ((stalkH 0 x).obj K) ≤ 1) ∧
      (∀ x ∈ T, ∀ a : Fin (c - 1), Module.rank ℚ ((stalkH (2 * (a + 1 : ℕ)) x).obj K) ≤ 1) ∧
      (∀ (n : ℤ) (x : analyticSpace sV), n ≠ 0 →
        (∀ a : Fin (c - 1), x ∈ T → n ≠ 2 * (a + 1 : ℕ)) → IsZero ((stalkH n x).obj K)) ∧
      (∀ x, (stalkH 0 x).map unit ≠ 0) ∧
      (∀ a : Fin (c - 1), ∀ x ∉ T,
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map (ζ a).hom = 0) ∧
      (∀ a : Fin (c - 1), ∀ x ∈ T, (stalkH (2 * (a + 1 : ℕ)) x).map
        (DerivedCategory.Plus.Qh.map (singleHomOfCocycle C (ζ a) (hζd a)) ≫ M.hom) ≠ 0)) := by
  intro bAn iAn QV F QV' η S S' m unit iQ p K
  let T : Set (analyticSpace sV) := Set.range iAn
  have hT : ∀ x, x ∈ T ↔ x.toScheme ∈ I.support := fun x => by
    rw [show T = _ from range_analyticMap_subschemeι sV I]; rfl
  have hiAn := isClosedEmbedding_analyticMap sV I.subschemeι
  let J := injectiveResolution QV'
  obtain ⟨M, hζ₀, hu₀⟩ := exists_model F η J
  let C := F.mapCochainComplexPlus.obj J.plusObj
  obtain ⟨ζ, hζd, hζU, hζT⟩ : ∃ (ζ : ∀ a : Fin (c - 1), QV ⟶ C.obj.X (2 * (a + 1 : ℕ)))
      (hζd : ∀ a, ζ a ≫ C.obj.d (2 * (a + 1 : ℕ)) (2 * (a + 1 : ℕ) + 1) = 0),
      (∀ a : Fin (c - 1), ∀ x ∉ T,
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map (ζ a).hom = 0) ∧
      (∀ a : Fin (c - 1), ∀ x ∈ T, (stalkH (2 * (a + 1 : ℕ)) x).map
        (DerivedCategory.Plus.Qh.map (singleHomOfCocycle C (ζ a) (hζd a)) ≫ M.hom) ≠ 0) := by
    let W : Opens (analyticSpace sV) := ⟨Tᶜ, hiAn.isClosed_range.isOpen_compl⟩
    have hWT : ∀ x, x ∈ W ↔ x.toScheme ∉ I.support := fun x ↦ (hT x).not
    obtain ⟨γ, hγ0, hγF⟩ := exists_relCohomology_classes sV I hI c hc hcodim W hWT
    have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
    have hmet := metrizableSpace_and_stronglyLocallyContractibleSpace (blowUpToBase I ≫ sV)
    haveI : MetrizableSpace (analyticSpace (blowUpToBase I ≫ sV)) := hmet.1
    haveI : StronglyLocallyContractibleSpace (analyticSpace (blowUpToBase I ≫ sV)) := hmet.2
    have hX' : LocallyContractibleSpace (analyticSpace (blowUpToBase I ≫ sV)) :=
      StronglyLocallyContractibleSpace.locallyContractible
    have hWl : LocallyContractibleSpace ((Opens.toTopCat _).obj ((Opens.map bAn).obj W)) := by
      haveI : StronglyLocallyContractibleSpace ((Opens.toTopCat _).obj ((Opens.map bAn).obj W)) :=
        ((Opens.map bAn).obj W).2.isOpenEmbedding_subtypeVal.stronglyLocallyContractibleSpace
      exact StronglyLocallyContractibleSpace.locallyContractible
    haveI : StronglyLocallyContractibleSpace (MMP.Topology.complexProjectiveSpace (c - 1)) := by
      letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ (c - 1))).Over (Spec (.of ℂ)) :=
        ⟨Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ (c - 1)⟩
      haveI := Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff ℂ (c - 1)
      haveI : LocallyOfFiniteType (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ (c - 1)) ↘ Spec (.of ℂ)) :=
        inferInstanceAs (LocallyOfFiniteType (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ (c - 1)))
      have h := MMP.UnderlyingSpace.hasOpenContractibleBasis
        (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ (c - 1)))
      have := h.stronglyLocallyContractibleSpace
      exact (MMP.Topology.underlyingSpaceProjectiveSpaceHomeomorph
        (c - 1) rfl).symm
          |>.isOpenEmbedding.stronglyLocallyContractibleSpace
    have key : ∀ a : Fin (c - 1), ∃ (ζ : QV ⟶ C.obj.X (2 * (a + 1 : ℕ)))
        (hζd : ζ ≫ C.obj.d (2 * (a + 1 : ℕ)) (2 * (a + 1 : ℕ) + 1) = 0),
        (∀ x ∉ T, (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map ζ.hom = 0) ∧
        (∀ x ∈ T, (stalkH (2 * (a + 1 : ℕ)) x).map
          (DerivedCategory.Plus.Qh.map (singleHomOfCocycle C ζ hζd) ≫ M.hom) ≠ 0) := by
      intro a
      obtain ⟨ζ, hζd, hU, hF⟩ := exists_cocycle_of_relCohomology bAn hX' W hWl
        (2 * (a + 1 : ℕ)) (2 * ((a : ℕ) + 1)) (2 * (a : ℕ) + 1) (by ring) (by push_cast; ring)
        (γ a) (hγ0 a)
      refine ⟨ζ, hζd, fun x hx ↦ hU x hx, fun x hx ↦ ?_⟩
      obtain ⟨e⟩ :=
        MMP.Topology.nonempty_homeomorph_preimage_analyticMap_blowUpToBase_of_codimension
          sV I hI c (by omega) hcodim x ((hT x).1 hx)
      haveI : StronglyLocallyContractibleSpace (Fib bAn x) :=
        e.isOpenEmbedding.stronglyLocallyContractibleSpace
      have h := hF x StronglyLocallyContractibleSpace.locallyContractible (hγF a x ((hT x).1 hx))
      intro h0
      exact h (map_eq_zero_of_map_comp_iso _ _ M h0)
    choose ζ hζd hζU hζT using key
    exact ⟨ζ, hζd, hζU, hζT⟩
  have hbound : ∀ (x : analyticSpace sV) (n : ℤ), ∃ m : ℕ,
      ((x.toScheme ∈ I.support → m = c - 1) ∧ (x.toScheme ∉ I.support → m = 0)) ∧
      ((Even n ∧ 0 ≤ n ∧ n ≤ 2 * m → Module.rank ℚ ((stalkH n x).obj K) ≤ 1) ∧
        (¬ (Even n ∧ 0 ≤ n ∧ n ≤ 2 * m) → IsZero ((stalkH n x).obj K))) := by
    intro x n
    obtain ⟨m, ⟨e⟩, h1, h2⟩ := exists_fibre_homeomorph sV I hI c hc hcodim x
    exact ⟨m, ⟨h1, h2⟩, stalkH_bound_of_homeomorph sV I x m e n⟩
  refine ⟨T, C, M, ζ, hζd, fun x => rank_stalk_constantSheaf_le _ x, ?_, ?_, ?_, ?_, ?_, ?_,
    hζU, hζT⟩
  · rintro x ⟨t, rfl⟩
    exact isIso_stalk_unit iAn hiAn.isInducing QV t
  · intro x hx
    exact subsingleton_stalk_pushforward iAn hiAn.isClosed_range _ hx
  · intro x
    obtain ⟨m, -, h⟩ := hbound x 0
    exact h.1 ⟨Even.zero, le_rfl, by omega⟩
  · intro x hx a
    obtain ⟨m, ⟨hm, -⟩, h⟩ := hbound x (2 * (a + 1 : ℕ))
    have := hm ((hT x).1 hx)
    subst this
    exact h.1 ⟨⟨(a + 1 : ℕ), by push_cast; ring⟩, by positivity, by have := a.2; omega⟩
  · intro n x hn0 hna
    obtain ⟨m, ⟨hm1, hm0⟩, h⟩ := hbound x n
    apply h.2
    rintro ⟨⟨r, hr⟩, h0, h2⟩
    by_cases hx : x ∈ T
    · have := hm1 ((hT x).1 hx)
      subst this
      obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
      refine hna ⟨r' - 1, by omega⟩ hx ?_
      push_cast
      omega
    · have := hm0 (fun h' => hx ((hT x).2 h'))
      subst this
      omega
  · intro x
    obtain ⟨m', ⟨e⟩, -, -⟩ := exists_fibre_homeomorph sV I hI c hc hcodim x
    have hpt : Nonempty (MMP.Topology.complexProjectiveSpace m') := by
      cases m' with
      | zero => exact ⟨default⟩
      | succ k => exact ⟨MMP.Topology.projectiveSpaceBasePoint k⟩
    let p : Fib bAn x := e.symm hpt.some
    have h := stalkH_unit_ne_zero bAn x p hζ₀
    intro hzero
    apply h
    have h2 : (stalkH 0 x).map (DerivedCategory.Plus.Qh.map
        (singleHomOfCocycle C (η ≫ F.map J.inclusionZero) hζ₀) ≫ M.hom) = 0 := by
      rw [hu₀]
      exact hzero
    exact map_eq_zero_of_map_comp_iso _ _ M h2

/-- The derived splitting `ℚ_V ⊞ ⨁ i_* ℚ_T[-2a] ≅ Rb_* ℚ_{V'}` with first component the unit. -/
private theorem exists_biprod_iso_rightDerivedFunctorPlus_of_isSmoothBlowup {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) [IsIntegral V] [IsSeparated sV] [LocallyOfFiniteType sV]
    [QuasiCompact sV]
    (I : V.IdealSheafData) (hI : MMP.Resolution.IsSmoothBlowup sV I)
    (c : ℕ) (hc : 2 ≤ c)
    (hcodim : ∀ Z : IrreducibleCloseds V,
      Maximal (fun W : IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z → codimension Z = c) :
    let bAn := analyticMap (blowUpToBase I) rfl
    let iAn := analyticMap I.subschemeι rfl
    let QV := (constantSheaf (Opens.grothendieckTopology (analyticSpace sV)) (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)
    (let F := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) bAn
    haveI : F.Additive := Functor.additive_of_preserves_binary_products F
    let QV' := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) bAn).obj QV
    let η := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) bAn).unit.app QV
    let S := HomotopyCategory.Plus.singleFunctor (TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sV))
    let S' := HomotopyCategory.Plus.singleFunctor
      (TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace (blowUpToBase I ≫ sV)))
    let m : (S 0).obj QV ⟶ F.mapHomotopyCategoryPlus.obj ((S' 0).obj QV') :=
      (HomotopyCategory.Plus.ι _).preimage ((HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single _ _ 0).map η ≫
          (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app QV'))
    let unit := DerivedCategory.Plus.Qh.map m ≫ F.rightDerivedFunctorPlusUnith.app ((S' 0).obj QV')
    let iQ := (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) iAn).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) iAn).obj QV)
    ∃ e : DerivedCategory.Plus.Qh.obj ((S 0).obj QV) ⊞
        (⨁ fun a : Fin (c - 1) ↦ DerivedCategory.Plus.Qh.obj ((S (2 * (a + 1 : ℕ))).obj iQ)) ≅
        F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj ((S' 0).obj QV')),
      biprod.inl ≫ e.hom = unit)
    := by
  intro bAn iAn QV F QV' η S S' m unit iQ
  obtain ⟨φ, hφ⟩ : ∃ φ : ∀ a : Fin (c - 1),
      DerivedCategory.Plus.Qh.obj ((S (2 * (a + 1 : ℕ))).obj iQ) ⟶
        F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj ((S' 0).obj QV')),
      ∀ (n : ℤ) (x : analyticSpace sV),
        IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
          ((DerivedCategory.Plus.homologyFunctor _ n).map
            (biprod.desc unit (biproduct.desc φ))).hom) := by
    obtain ⟨T, C, M, ζ, hζd, hQV, hpT, hpU, hK0, hKT, hKz, hu, hζU, hζT⟩ :=
      exists_splitting_data sV I hI c hc hcodim
    exact exists_isIso_stalk_homology_biprod_desc (c - 1) T QV iQ _ _ unit C M hQV hpT hpU hK0
      hKT hKz hu ζ hζd hζU hζT
  exact ⟨@asIso _ _ _ _ _ (isIso_of_forall_isIso_stalk_homology _ hφ), biprod.inl_desc _ _⟩

/-- Over every set `Q` of points of the target, the structural unit of the restriction of `g` has
a retraction. -/
private def HasRestrictedUnitRetraction {W Y : Over (Spec (.of ℂ))} (g : W ⟶ Y) : Prop :=
      ∀ Q : Set Y.left,
        let gAn := analyticMap g.left (Over.w g)
        let Qan : Set (analyticSpace Y.hom) := {x | toScheme x ∈ Q}
        let gQ : TopCat.of (gAn ⁻¹' Qan) ⟶ TopCat.of Qan :=
          TopCat.ofHom ⟨Qan.restrictPreimage gAn, gAn.hom.continuous.restrictPreimage⟩
        HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) gQ) (constUnit gQ)

private lemma hasRestrictedUnitRetraction_id (Y : Over (Spec (.of ℂ))) :
    HasRestrictedUnitRetraction (𝟙 Y) := by
  intro Q
  dsimp only
  have heq : (TopCat.ofHom ⟨{x : analyticSpace Y.hom | toScheme x ∈ Q}.restrictPreimage
      (analyticMap (Over.Hom.left (𝟙 Y)) (Over.w (𝟙 Y))),
      (analyticMap (Over.Hom.left (𝟙 Y)) (Over.w (𝟙 Y))).hom.continuous.restrictPreimage⟩ :
        TopCat.of (analyticMap (Over.Hom.left (𝟙 Y)) (Over.w (𝟙 Y)) ⁻¹'
          {x : analyticSpace Y.hom | toScheme x ∈ Q}) ⟶
        TopCat.of {x : analyticSpace Y.hom | toScheme x ∈ Q}) = 𝟙 _ := by
    ext x
    exact Category.comp_id _
  exact (hasUnitRetraction_constUnit_congr heq).mpr (hasUnitRetraction_constUnit_id _)

private lemma hasRestrictedUnitRetraction_comp {W Y Z : Over (Spec (.of ℂ))} (g : W ⟶ Y)
    (h : Y ⟶ Z) (hg : HasRestrictedUnitRetraction g) (hh : HasRestrictedUnitRetraction h) :
    HasRestrictedUnitRetraction (g ≫ h) := by
  intro Q
  have h₁ := hh Q
  have h₂ := hg (h.left.base ⁻¹' Q)
  dsimp only at h₁ h₂ ⊢
  set gAn := analyticMap g.left (Over.w g)
  set hAn := analyticMap h.left (Over.w h)
  set fAn := analyticMap (g ≫ h).left (Over.w (g ≫ h))
  set Qan : Set (analyticSpace Z.hom) := {x | toScheme x ∈ Q}
  set Qan' : Set (analyticSpace Y.hom) := {x | toScheme x ∈ h.left.base ⁻¹' Q}
  have heq : (TopCat.ofHom ⟨Qan.restrictPreimage fAn, fAn.hom.continuous.restrictPreimage⟩ :
      TopCat.of (fAn ⁻¹' Qan) ⟶ TopCat.of Qan) =
      (TopCat.ofHom ⟨Qan'.restrictPreimage gAn, gAn.hom.continuous.restrictPreimage⟩ :
        TopCat.of (gAn ⁻¹' Qan') ⟶ TopCat.of Qan') ≫
      (TopCat.ofHom ⟨Qan.restrictPreimage hAn, hAn.hom.continuous.restrictPreimage⟩ :
        TopCat.of (hAn ⁻¹' Qan) ⟶ TopCat.of Qan) := by
    ext x
    exact (Category.assoc _ _ _).symm
  exact (hasUnitRetraction_constUnit_congr heq).mpr (hasUnitRetraction_constUnit_comp h₁ h₂)

/-- Along a single smooth-centre blowup the structural unit, restricted over any set
`Q` of points of the base, has a retraction: the projection to the first summand of the derived
splitting retracts the unit, and proper base change restricts the retraction to `Q`. -/
private theorem hasRestrictedUnitRetraction_of_isSmoothBlowup :
    let P : MorphismProperty (Over (Spec (.of ℂ))) := fun X Y g ↦
      IsIntegral Y.left ∧ IsSeparated Y.hom ∧ LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
        ∃ (J : Y.left.IdealSheafData) (e : blowUp J ≅ X.left),
          e.hom ≫ g.left = blowUpToBase J ∧ MMP.Resolution.IsSmoothBlowup Y.hom J ∧
          ∃ d : ℕ, 2 ≤ d ∧ ∀ Z : IrreducibleCloseds Y.left,
            Maximal (fun W : IrreducibleCloseds Y.left ↦ (W : Set Y.left) ⊆ J.support) Z →
              codimension Z = d
    ∀ {W Y : Over (Spec (.of ℂ))} (g : W ⟶ Y), P g → HasRestrictedUnitRetraction g := by
  intro P W Y g ⟨_, _, _, _, J, e, he, hJ, d, hd, hcodim⟩
  obtain ⟨E, hE⟩ := exists_biprod_iso_rightDerivedFunctorPlus_of_isSmoothBlowup Y.hom J hJ d hd
    hcodim
  let bAn := analyticMap (sY := Y.hom) (blowUpToBase J) rfl
  have hU : HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) bAn)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) bAn).unit.app
        ((constantSheaf (Opens.grothendieckTopology (analyticSpace Y.hom)) (ModuleCat.{0} ℚ)).obj
          (ModuleCat.of ℚ ℚ))) :=
    ⟨E.inv ≫ biprod.fst, (congrArg (· ≫ E.inv ≫ biprod.fst) hE).symm.trans
      (by simp : (biprod.inl ≫ E.hom) ≫ E.inv ≫ biprod.fst = 𝟙 _)⟩
  have hU' := hasUnitRetraction_constUnit_of_unit bAn hU
  have hw : e.hom ≫ W.hom = blowUpToBase J ≫ Y.hom := by
    rw [← Over.w g, ← Category.assoc, he]
  have hb : bAn = analyticMap e.hom hw ≫ analyticMap g.left (Over.w g) := by
    change analyticMap (blowUpToBase J) _ = _
    rw [analyticMap_comp]
    congr 1
    exact he.symm
  have hUg := hasUnitRetraction_constUnit_of_comp ((hasUnitRetraction_constUnit_congr hb).mp hU')
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hgl : g.left = e.inv ≫ blowUpToBase J := by rw [← he, Iso.inv_hom_id_assoc]
  have : IsProper g.left := by rw [hgl]; infer_instance
  have : LocallyOfFiniteType W.hom := by rw [← Over.w g]; infer_instance
  have : QuasiCompact W.hom := by rw [← Over.w g]; infer_instance
  intro Q
  exact hasUnitRetraction_constUnit_restrictPreimage g.left (Over.w g) hUg Q

/-- Along any finite composite of smooth-centre blowups the restricted structural units have
retractions. -/
private theorem hasRestrictedUnitRetraction_of_multiplicativeClosure :
    let P : MorphismProperty (Over (Spec (.of ℂ))) := fun X Y g ↦
      IsIntegral Y.left ∧ IsSeparated Y.hom ∧ LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
        ∃ (J : Y.left.IdealSheafData) (e : blowUp J ≅ X.left),
          e.hom ≫ g.left = blowUpToBase J ∧ MMP.Resolution.IsSmoothBlowup Y.hom J ∧
          ∃ d : ℕ, 2 ≤ d ∧ ∀ Z : IrreducibleCloseds Y.left,
            Maximal (fun W : IrreducibleCloseds Y.left ↦ (W : Set Y.left) ⊆ J.support) Z →
              codimension Z = d
    ∀ {W Y : Over (Spec (.of ℂ))} (g : W ⟶ Y), P.multiplicativeClosure g →
      HasRestrictedUnitRetraction g := by
  intro P W Y g hg
  induction hg with
  | of g hg => exact hasRestrictedUnitRetraction_of_isSmoothBlowup g hg
  | id Y => exact hasRestrictedUnitRetraction_id Y
  | comp_of g h _ hh ih =>
    exact hasRestrictedUnitRetraction_comp g h ih
      (hasRestrictedUnitRetraction_of_isSmoothBlowup h hh)

/-- Pullback on the rational sheaf cohomology of closed subsets is split injective along any
finite composite of smooth-centre blowups. -/
private theorem exists_retraction_sheafCohomology_of_multiplicativeClosure :
    let P : MorphismProperty (Over (Spec (.of ℂ))) := fun X Y g ↦
      IsIntegral Y.left ∧ IsSeparated Y.hom ∧ LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
        ∃ (J : Y.left.IdealSheafData) (e : blowUp J ≅ X.left),
          e.hom ≫ g.left = blowUpToBase J ∧ MMP.Resolution.IsSmoothBlowup Y.hom J ∧
          ∃ d : ℕ, 2 ≤ d ∧ ∀ Z : IrreducibleCloseds Y.left,
            Maximal (fun W : IrreducibleCloseds Y.left ↦ (W : Set Y.left) ⊆ J.support) Z →
              codimension Z = d
    ∀ {W Y : Over (Spec (.of ℂ))} (g : W ⟶ Y), P.multiplicativeClosure g →
      ∀ Q : Set Y.left, IsClosed Q → ∀ k : ℕ,
        let gAn := analyticMap g.left (Over.w g)
        let Qan : Set (analyticSpace Y.hom) := {x | toScheme x ∈ Q}
        let gQ : TopCat.of (gAn ⁻¹' Qan) ⟶ TopCat.of Qan :=
          TopCat.ofHom ⟨Qan.restrictPreimage gAn, gAn.hom.continuous.restrictPreimage⟩
        let G := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) gQ
        haveI : G.Additive := Functor.additive_of_preserves_binary_products G
        haveI : G.PreservesInjectiveObjects :=
          haveI : PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) gQ) :=
            (fun {A B : TopCat.{0}} (k : A ⟶ B) =>
              (by apply Functor.sheafPullbackConstruction.preservesFiniteLimits :
                PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) k))) gQ
          Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
            (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) gQ)
        let QQ : TopCat.Sheaf (ModuleCat.{0} ℚ) (TopCat.of Qan) :=
          (constantSheaf (Opens.grothendieckTopology (TopCat.of Qan)) (ModuleCat.{0} ℚ)).obj
            (ModuleCat.of ℚ ℚ)
        let QQ' : TopCat.Sheaf (ModuleCat.{0} ℚ) (TopCat.of (gAn ⁻¹' Qan)) :=
          (constantSheaf (Opens.grothendieckTopology (TopCat.of (gAn ⁻¹' Qan)))
            (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
        let c : QQ ⟶ G.obj QQ' :=
          ((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).homEquiv _ _).symm
            ((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).unit.app _)
        let T := HomotopyCategory.Plus.singleFunctor
          (TopCat.Sheaf (ModuleCat.{0} ℚ) (TopCat.of Qan))
        let T' := HomotopyCategory.Plus.singleFunctor
          (TopCat.Sheaf (ModuleCat.{0} ℚ) (TopCat.of (gAn ⁻¹' Qan)))
        let m : (T 0).obj QQ ⟶ G.mapHomotopyCategoryPlus.obj ((T' 0).obj QQ') :=
          (HomotopyCategory.Plus.ι _).preimage ((HomotopyCategory.quotient _ _).map
            ((HomologicalComplex.single _ _ 0).map c ≫
              (HomologicalComplex.singleMapHomologicalComplex G _ 0).inv.app QQ'))
        let u := DerivedCategory.Plus.Qh.map m ≫ G.rightDerivedFunctorPlusUnith.app ((T' 0).obj QQ')
        let Γ := TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (TopCat.of Qan) ⋙
          (evaluation _ (ModuleCat.{0} ℚ)).obj (Opposite.op ⊤)
        let Γ' := TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (TopCat.of (gAn ⁻¹' Qan)) ⋙
          (evaluation _ (ModuleCat.{0} ℚ)).obj (Opposite.op ⊤)
        haveI : Γ.Additive := ⟨fun {_ _ _ _} => rfl⟩
        haveI : Γ'.Additive := ⟨fun {_ _ _ _} => rfl⟩
        let e : Γ'.rightDerivedFunctorPlus ≅
            G.rightDerivedFunctorPlus ⋙ Γ.rightDerivedFunctorPlus :=
          Functor.rightDerivedFunctorPlusCompIso G Γ
        ∃ r, (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ℚ) k).map
          (Γ.rightDerivedFunctorPlus.map u ≫ e.inv.app _) ≫ r = 𝟙 _
    := by
  intro P W Y g hg Q _ k gAn Qan gQ G QQ QQ' c T T' m u Γ Γ' e
  have h : HasUnitRetraction G c := hasRestrictedUnitRetraction_of_multiplicativeClosure g hg Q
  have : Γ.Additive := ⟨fun {_ _ _ _} => rfl⟩
  exact exists_retraction_homology_of_hasUnitRetraction G Γ h (k : ℤ)

end Helpers

/-- **The rational structural unit splits for a smooth-centre blowup.** Let `b : V' ⟶ V` be the
blowup of a smooth complex variety along a smooth closed centre `T` (the closed subscheme of `I`)
of pure codimension `c ≥ 2`. Then there is an isomorphism
`ℚ_V ⊞ ⨁_{a=1}^{c-1} i_* ℚ_T[-2a] ≅ Rb_* ℚ_{V'}` in the bounded below derived category of sheaves
of `ℚ`-vector spaces on `V^an` whose first component is the structural unit. Moreover, for every
finite composite `g` of smooth-centre blowups over `ℂ`, every Zariski-closed `Q` in its target
and every `k`, pullback `H^k(Q^an; ℚ) ⟶ H^k(g^{-1}(Q)^an; ℚ)` on the sheaf cohomology of the
constant sheaf `ℚ` has a left inverse. -/
@[mmp "thm_mmp_conductor_smooth_blowup_betti_splitting"]
public theorem exists_biprod_iso_rightDerivedFunctorPlus_blowUpToBase {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) [IsIntegral V] [IsSeparated sV] [LocallyOfFiniteType sV]
    [QuasiCompact sV]
    (I : V.IdealSheafData) (hI : MMP.Resolution.IsSmoothBlowup sV I)
    (c : ℕ) (hc : 2 ≤ c)
    (hcodim : ∀ Z : IrreducibleCloseds V,
      Maximal (fun W : IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z → codimension Z = c) :
    let bAn := analyticMap (blowUpToBase I) rfl
    let iAn := analyticMap I.subschemeι rfl
    let QV := (constantSheaf (Opens.grothendieckTopology (analyticSpace sV)) (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)
    (let F := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) bAn
    haveI : F.Additive := Functor.additive_of_preserves_binary_products F
    let QV' := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) bAn).obj QV
    let η := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) bAn).unit.app QV
    let S := HomotopyCategory.Plus.singleFunctor (TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sV))
    let S' := HomotopyCategory.Plus.singleFunctor
      (TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace (blowUpToBase I ≫ sV)))
    let m : (S 0).obj QV ⟶ F.mapHomotopyCategoryPlus.obj ((S' 0).obj QV') :=
      (HomotopyCategory.Plus.ι _).preimage ((HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single _ _ 0).map η ≫
          (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app QV'))
    let unit := DerivedCategory.Plus.Qh.map m ≫ F.rightDerivedFunctorPlusUnith.app ((S' 0).obj QV')
    let iQ := (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) iAn).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) iAn).obj QV)
    ∃ e : DerivedCategory.Plus.Qh.obj ((S 0).obj QV) ⊞
        (⨁ fun a : Fin (c - 1) ↦ DerivedCategory.Plus.Qh.obj ((S (2 * (a + 1 : ℕ))).obj iQ)) ≅
        F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj ((S' 0).obj QV')),
      biprod.inl ≫ e.hom = unit) ∧
    let P : MorphismProperty (Over (Spec (.of ℂ))) := fun X Y g ↦
      IsIntegral Y.left ∧ IsSeparated Y.hom ∧ LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
        ∃ (J : Y.left.IdealSheafData) (e : blowUp J ≅ X.left),
          e.hom ≫ g.left = blowUpToBase J ∧ MMP.Resolution.IsSmoothBlowup Y.hom J ∧
          ∃ d : ℕ, 2 ≤ d ∧ ∀ Z : IrreducibleCloseds Y.left,
            Maximal (fun W : IrreducibleCloseds Y.left ↦ (W : Set Y.left) ⊆ J.support) Z →
              codimension Z = d
    ∀ {W Y : Over (Spec (.of ℂ))} (g : W ⟶ Y), P.multiplicativeClosure g →
      ∀ Q : Set Y.left, IsClosed Q → ∀ k : ℕ,
        let gAn := analyticMap g.left (Over.w g)
        let Qan : Set (analyticSpace Y.hom) := {x | toScheme x ∈ Q}
        let gQ : TopCat.of (gAn ⁻¹' Qan) ⟶ TopCat.of Qan :=
          TopCat.ofHom ⟨Qan.restrictPreimage gAn, gAn.hom.continuous.restrictPreimage⟩
        let G := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) gQ
        haveI : G.Additive := Functor.additive_of_preserves_binary_products G
        haveI : G.PreservesInjectiveObjects :=
          haveI : PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) gQ) :=
            (fun {A B : TopCat.{0}} (k : A ⟶ B) =>
              (by apply Functor.sheafPullbackConstruction.preservesFiniteLimits :
                PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) k))) gQ
          Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
            (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) gQ)
        let QQ : TopCat.Sheaf (ModuleCat.{0} ℚ) (TopCat.of Qan) :=
          (constantSheaf (Opens.grothendieckTopology (TopCat.of Qan)) (ModuleCat.{0} ℚ)).obj
            (ModuleCat.of ℚ ℚ)
        let QQ' : TopCat.Sheaf (ModuleCat.{0} ℚ) (TopCat.of (gAn ⁻¹' Qan)) :=
          (constantSheaf (Opens.grothendieckTopology (TopCat.of (gAn ⁻¹' Qan)))
            (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
        let c : QQ ⟶ G.obj QQ' :=
          ((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).homEquiv _ _).symm
            ((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).unit.app _)
        let T := HomotopyCategory.Plus.singleFunctor
          (TopCat.Sheaf (ModuleCat.{0} ℚ) (TopCat.of Qan))
        let T' := HomotopyCategory.Plus.singleFunctor
          (TopCat.Sheaf (ModuleCat.{0} ℚ) (TopCat.of (gAn ⁻¹' Qan)))
        let m : (T 0).obj QQ ⟶ G.mapHomotopyCategoryPlus.obj ((T' 0).obj QQ') :=
          (HomotopyCategory.Plus.ι _).preimage ((HomotopyCategory.quotient _ _).map
            ((HomologicalComplex.single _ _ 0).map c ≫
              (HomologicalComplex.singleMapHomologicalComplex G _ 0).inv.app QQ'))
        let u := DerivedCategory.Plus.Qh.map m ≫ G.rightDerivedFunctorPlusUnith.app ((T' 0).obj QQ')
        let Γ := TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (TopCat.of Qan) ⋙
          (evaluation _ (ModuleCat.{0} ℚ)).obj (Opposite.op ⊤)
        let Γ' := TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (TopCat.of (gAn ⁻¹' Qan)) ⋙
          (evaluation _ (ModuleCat.{0} ℚ)).obj (Opposite.op ⊤)
        haveI : Γ.Additive := ⟨fun {_ _ _ _} => rfl⟩
        haveI : Γ'.Additive := ⟨fun {_ _ _ _} => rfl⟩
        let e : Γ'.rightDerivedFunctorPlus ≅
            G.rightDerivedFunctorPlus ⋙ Γ.rightDerivedFunctorPlus :=
          Functor.rightDerivedFunctorPlusCompIso G Γ
        ∃ r, (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ℚ) k).map
          (Γ.rightDerivedFunctorPlus.map u ≫ e.inv.app _) ≫ r = 𝟙 _ :=
  ⟨exists_biprod_iso_rightDerivedFunctorPlus_of_isSmoothBlowup sV I hI c hc hcodim,
    exists_retraction_sheafCohomology_of_multiplicativeClosure⟩

end MMP.Conductor

end SmoothBlowupSplitting
