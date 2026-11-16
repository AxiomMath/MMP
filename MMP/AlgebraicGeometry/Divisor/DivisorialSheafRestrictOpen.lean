module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Restrict.RationalFunction

/-!
# Divisorial sections on an open subscheme

Let `U` be an open of a scheme `X`. The irreducible components `Z'` of `U` correspond to the
irreducible components `Z` of `X` meeting `U`, by `Z ↦ Z ∩ U`, and the generic point of `Z'` is
the generic point of `Z`; the open immersion `U ⟶ X` identifies the local rings at these points.
Hence for an open `O ⊆ U` the sections of the sheaf of rational functions `𝒦_X` over `O` are
identified with the sections of `𝒦_U` over `O`, compatibly with restriction and with the germs of
regular functions. For a locally Noetherian normal `X` the identification preserves the orders of
vanishing along prime divisors, so it carries the sections of `𝒪_X(D)` over `O` to the sections
of `𝒪_U(D|_U)` over `O`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.componentStalkIso`: `𝒪_{X,η_Z} ≅ 𝒪_{U,η_{Z'}}` for a
  component `Z'` of `U` whose generic point lies on the component `Z` of `X`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.rationalFunctionsToOpens`: `𝒦_X(O) → 𝒦_U(O)`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.componentGenericPoint_eq_ι`: the generic point of a
  component of `X` through the image of the generic point of a component of `U` is that image.
* `MMP.FourfoldProofs.FractionalLogComplexProof.rationalFunctionsToOpens_bijective`: for `O ⊆ U` the
  map `𝒦_X(O) → 𝒦_U(O)` is bijective.
* `MMP.FourfoldProofs.FractionalLogComplexProof.isDivisorialSection_rationalFunctionsToOpens_iff`:
  it carries the sections of `𝒪_X(D)` to those of `𝒪_U(D|_U)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_divisorialSubmodule_restrictDivisor_iff`: a
  regular function on `O ∩ U'` extends to a section of `𝒪_X(-M)` over `O` exactly when its
  restriction to `U` extends to a section of `𝒪_U(-M|_U)` over `O`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open MMP.Mori

universe u

variable {X : Scheme.{u}} (U : X.Opens)

/-! ### Irreducible components of an open subscheme -/

/-- If the image of the generic point of a component `Z'` of `U` lies on a component `Z` of `X`,
it is the generic point of `Z`. -/
theorem componentGenericPoint_eq_ι {Z' : irreducibleComponents U.toScheme}
    {Z : irreducibleComponents X} (h : U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1) :
    componentGenericPoint X Z = U.ι (componentGenericPoint U.toScheme Z') := by
  have sp : componentGenericPoint X Z ⤳ U.ι (componentGenericPoint U.toScheme Z') :=
    (isGenericPoint_componentGenericPoint X Z).specializes h
  obtain ⟨y, hy⟩ : componentGenericPoint X Z ∈ Set.range U.ι.base :=
    sp.mem_open U.ι.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  have sp' : y ⤳ componentGenericPoint U.toScheme Z' := by
    rwa [← U.ι.isOpenEmbedding.isInducing.specializes_iff, hy]
  have hZ' := isGenericPoint_componentGenericPoint U.toScheme Z'
  have hsub : Z'.1 ⊆ closure {y} := by
    rw [← hZ'.def]
    exact sp'.closure_subset
  have heq : closure {y} = Z'.1 :=
    (Z'.2.2 isIrreducible_singleton.closure hsub).antisymm hsub
  rw [← hy, (show IsGenericPoint y Z'.1 from heq).eq hZ']

/-- A component of `X` whose generic point lies in `U` contains the image of the generic point of
a component of `U`. -/
theorem exists_ι_componentGenericPoint_mem {Z : irreducibleComponents X}
    (hZ : componentGenericPoint X Z ∈ U) :
    ∃ Z' : irreducibleComponents U.toScheme, U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1 := by
  have hne : (Z.1 ∩ Set.range U.ι.base).Nonempty :=
    ⟨_, (isGenericPoint_componentGenericPoint X Z).mem, by rwa [Scheme.Opens.range_ι]⟩
  let Z' : irreducibleComponents U.toScheme :=
    ⟨U.ι.base ⁻¹' Z.1, preimage_mem_irreducibleComponents Z.2 U.ι.isOpenEmbedding hne⟩
  exact ⟨Z', (isGenericPoint_componentGenericPoint U.toScheme Z').mem⟩

/-- The image of the generic point of a component of `U` lies on at most one component of `X`. -/
theorem irreducibleComponents_eq_of_ι_mem {Z' : irreducibleComponents U.toScheme}
    {Z W : irreducibleComponents X} (hZ : U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1)
    (hW : U.ι (componentGenericPoint U.toScheme Z') ∈ W.1) : Z = W := by
  apply Subtype.ext
  rw [← (isGenericPoint_componentGenericPoint X Z).def,
    ← (isGenericPoint_componentGenericPoint X W).def, componentGenericPoint_eq_ι U hZ,
    componentGenericPoint_eq_ι U hW]

/-- Two components of `U` the images of whose generic points lie on the same component of `X` are
equal. -/
theorem irreducibleComponents_opens_eq_of_ι_mem {Z' Z'' : irreducibleComponents U.toScheme}
    {Z : irreducibleComponents X} (h' : U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1)
    (h'' : U.ι (componentGenericPoint U.toScheme Z'') ∈ Z.1) : Z' = Z'' := by
  have h : componentGenericPoint U.toScheme Z' = componentGenericPoint U.toScheme Z'' :=
    U.ι.isOpenEmbedding.injective
      ((componentGenericPoint_eq_ι U h').symm.trans (componentGenericPoint_eq_ι U h''))
  apply Subtype.ext
  rw [← (isGenericPoint_componentGenericPoint U.toScheme Z').def,
    ← (isGenericPoint_componentGenericPoint U.toScheme Z'').def, h]

/-! ### Rational functions on an open subscheme -/

/-- The local ring of `X` at the generic point of a component `Z` is the local ring of `U` at the
generic point of a component `Z'` of `U` whose generic point lies on `Z`. -/
noncomputable def componentStalkIso {Z' : irreducibleComponents U.toScheme}
    {Z : irreducibleComponents X} (h : U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1) :
    X.presheaf.stalk (componentGenericPoint X Z) ≅
      U.toScheme.presheaf.stalk (componentGenericPoint U.toScheme Z') :=
  X.presheaf.stalkCongr (Inseparable.of_eq (componentGenericPoint_eq_ι U h)) ≪≫
    @asIso _ _ _ _ (U.ι.stalkMap _) (IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι _)

/-- The forward map of `componentStalkIso` is injective. -/
theorem componentStalkIso_hom_injective {Z' : irreducibleComponents U.toScheme}
    {Z : irreducibleComponents X} (h : U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1) :
    Function.Injective (componentStalkIso U h).hom.hom :=
  (componentStalkIso U h).commRingCatIsoToRingEquiv.injective

/-- The forward map of `componentStalkIso` is the specialization map of stalks of `X` followed by
the stalk map of the open immersion `U ⟶ X`. -/
theorem componentStalkIso_hom {Z' : irreducibleComponents U.toScheme}
    {Z : irreducibleComponents X} (h : U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1) :
    (componentStalkIso U h).hom = X.presheaf.stalkSpecializes
      (Inseparable.of_eq (componentGenericPoint_eq_ι U h)).specializes' ≫ U.ι.stalkMap _ :=
  rfl

/-- `componentStalkIso` carries the germ of a regular function `g` on an open `W` of `X` to the
germ of the restriction of `g` to `U⁻¹(W)`. -/
theorem componentStalkIso_hom_germ {Z' : irreducibleComponents U.toScheme}
    {Z : irreducibleComponents X} (h : U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1)
    (W : X.Opens) (hW : componentGenericPoint X Z ∈ W) (g : Γ(X, W)) :
    (componentStalkIso U h).hom.hom ((X.presheaf.germ W _ hW).hom g) =
      (U.toScheme.presheaf.germ (U.ι ⁻¹ᵁ W) (componentGenericPoint U.toScheme Z')
        (by change U.ι _ ∈ W; rwa [← componentGenericPoint_eq_ι U h])).hom
        ((U.ι.app W).hom g) := by
  rw [componentStalkIso_hom, CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- For `U⁻¹(O) = O'`, if the generic point of a component `Z'` of `U` lies in `O'` and its image
lies on a component `Z` of `X`, then the generic point of `Z` lies in `O`. -/
theorem componentGenericPoint_mem_of_ι_mem {O : X.Opens} {O' : U.toScheme.Opens}
    (hO' : U.ι ⁻¹ᵁ O = O') {Z' : irreducibleComponents U.toScheme}
    (hZ' : componentGenericPoint U.toScheme Z' ∈ O') {Z : irreducibleComponents X}
    (h : U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1) : componentGenericPoint X Z ∈ O := by
  subst hO'
  rw [componentGenericPoint_eq_ι U h]
  exact hZ'

/-- For `U⁻¹(O) = O'`, if the generic point of a component `Z` of `X` lies in `O` and the image of
the generic point of a component `Z'` of `U` lies on `Z`, then the generic point of `Z'` lies in
`O'`. -/
theorem componentGenericPoint_opens_mem_of_ι_mem {O : X.Opens} {O' : U.toScheme.Opens}
    (hO' : U.ι ⁻¹ᵁ O = O') {Z' : irreducibleComponents U.toScheme} {Z : irreducibleComponents X}
    (hZ : componentGenericPoint X Z ∈ O) (h : U.ι (componentGenericPoint U.toScheme Z') ∈ Z.1) :
    componentGenericPoint U.toScheme Z' ∈ O' := by
  rw [← hO']
  change U.ι _ ∈ O
  rwa [← componentGenericPoint_eq_ι U h]

/-- **Rational functions on an open subscheme**: for `U⁻¹(O) = O'`, the map `𝒦_X(O) → 𝒦_U(O')`
whose component on a component `Z'` of `U` is the component on the component of `X` through
`η_{Z'}`, read in `𝒪_{U,η_{Z'}}`. -/
noncomputable def rationalFunctionsToOpens {O : X.Opens} {O' : U.toScheme.Opens}
    (hO' : U.ι ⁻¹ᵁ O = O') (φ : ToType ((rationalFunctionsPresheaf X).obj (op O))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op O')) :=
  fun Z' => (componentStalkIso U
    (mem_pointComponent (U.ι (componentGenericPoint U.toScheme Z'.1)))).hom.hom
      (φ ⟨pointComponent (U.ι (componentGenericPoint U.toScheme Z'.1)),
        componentGenericPoint_mem_of_ι_mem U hO' Z'.2 (mem_pointComponent _)⟩)

/-- The component of `rationalFunctionsToOpens U hO' φ` on `Z'` is the image under
`componentStalkIso` of the component of `φ` on any component `Z` of `X` through `η_{Z'}`. -/
theorem rationalFunctionsToOpens_apply {O : X.Opens} {O' : U.toScheme.Opens}
    (hO' : U.ι ⁻¹ᵁ O = O') (φ : ToType ((rationalFunctionsPresheaf X).obj (op O)))
    (Z' : {Z' : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z' ∈ O'})
    (Z : irreducibleComponents X) (h : U.ι (componentGenericPoint U.toScheme Z'.1) ∈ Z.1)
    (hZ : componentGenericPoint X Z ∈ O) :
    rationalFunctionsToOpens U hO' φ Z' = (componentStalkIso U h).hom.hom (φ ⟨Z, hZ⟩) := by
  obtain rfl := irreducibleComponents_eq_of_ι_mem U h (mem_pointComponent _)
  rfl

/-- For components `Z'` and `Z''` of `U` meeting `O'` whose generic points both lie on a component
`Z` of `X`, the forward map of `componentStalkIso` for `Z'` sends the inverse image under the one
for `Z''` of the component of `ψ` on `Z''` to the component of `ψ` on `Z'`. -/
theorem componentStalkIso_hom_inv_apply {O' : U.toScheme.Opens}
    (ψ : ToType ((rationalFunctionsPresheaf U.toScheme).obj (op O')))
    (Z' Z'' : {Z' : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z' ∈ O'})
    {Z : irreducibleComponents X} (h' : U.ι (componentGenericPoint U.toScheme Z'.1) ∈ Z.1)
    (h'' : U.ι (componentGenericPoint U.toScheme Z''.1) ∈ Z.1) :
    (componentStalkIso U h').hom.hom ((componentStalkIso U h'').inv.hom (ψ Z'')) = ψ Z' := by
  obtain rfl : Z'' = Z' := Subtype.ext (irreducibleComponents_opens_eq_of_ι_mem U h'' h')
  exact Iso.inv_hom_id_apply (componentStalkIso U h') _

/-- The inverse of `rationalFunctionsToOpens` for `O ⊆ U`. -/
noncomputable def rationalFunctionsOfOpens {O : X.Opens} {O' : U.toScheme.Opens} (hO : O ≤ U)
    (hO' : U.ι ⁻¹ᵁ O = O') (ψ : ToType ((rationalFunctionsPresheaf U.toScheme).obj (op O'))) :
    ToType ((rationalFunctionsPresheaf X).obj (op O)) :=
  fun Z => (componentStalkIso U
    (exists_ι_componentGenericPoint_mem U (hO Z.2)).choose_spec).inv.hom
      (ψ ⟨_, componentGenericPoint_opens_mem_of_ι_mem U hO' Z.2
        (exists_ι_componentGenericPoint_mem U (hO Z.2)).choose_spec⟩)

/-- For `O ⊆ U`, `𝒦_X(O) → 𝒦_U(U⁻¹(O))` is bijective. -/
theorem rationalFunctionsToOpens_bijective {O : X.Opens} {O' : U.toScheme.Opens} (hO : O ≤ U)
    (hO' : U.ι ⁻¹ᵁ O = O') : Function.Bijective (rationalFunctionsToOpens U hO') := by
  refine ⟨fun φ ψ hφψ => funext fun Z => ?_, fun ψ => ⟨rationalFunctionsOfOpens U hO hO' ψ,
    funext fun Z' => ?_⟩⟩
  · obtain ⟨Z', h⟩ := exists_ι_componentGenericPoint_mem U (hO Z.2)
    have := congrFun hφψ ⟨Z', componentGenericPoint_opens_mem_of_ι_mem U hO' Z.2 h⟩
    rw [rationalFunctionsToOpens_apply U hO' φ _ Z.1 h Z.2,
      rationalFunctionsToOpens_apply U hO' ψ _ Z.1 h Z.2] at this
    exact componentStalkIso_hom_injective U h this
  · have hZc : componentGenericPoint X
        (pointComponent (U.ι (componentGenericPoint U.toScheme Z'.1))) ∈ O :=
      componentGenericPoint_mem_of_ι_mem U hO' Z'.2 (mem_pointComponent _)
    refine (rationalFunctionsToOpens_apply U hO' _ Z' _ (mem_pointComponent _) hZc).trans ?_
    exact componentStalkIso_hom_inv_apply U ψ Z'
      ⟨_, componentGenericPoint_opens_mem_of_ι_mem U hO' hZc
        (exists_ι_componentGenericPoint_mem U (hO hZc)).choose_spec⟩
      (mem_pointComponent _) (exists_ι_componentGenericPoint_mem U (hO hZc)).choose_spec

/-- `rationalFunctionsToOpens` commutes with restriction of rational functions. -/
theorem rationalFunctionsToOpens_map {O₁ O₂ : X.Opens} {O₁' O₂' : U.toScheme.Opens}
    (h₁ : U.ι ⁻¹ᵁ O₁ = O₁') (h₂ : U.ι ⁻¹ᵁ O₂ = O₂') (i : O₂ ⟶ O₁) (i' : O₂' ⟶ O₁')
    (φ : ToType ((rationalFunctionsPresheaf X).obj (op O₁))) :
    rationalFunctionsToOpens U h₂ ((rationalFunctionsPresheaf X).map i.op φ) =
      (rationalFunctionsPresheaf U.toScheme).map i'.op (rationalFunctionsToOpens U h₁ φ) :=
  rfl

/-- `rationalFunctionsToOpens` carries the rational function of a regular function `g` on `W` to
the rational function of the restriction of `g` to `W'`. -/
theorem rationalFunctionsToOpens_toRationalFunctionsPresheaf {W : X.Opens}
    {W' : U.toScheme.Opens} (hW : U.ι ⁻¹ᵁ W = W') (i : W' ⟶ U.ι ⁻¹ᵁ W) (g : Γ(X, W)) :
    rationalFunctionsToOpens U hW ((toRationalFunctionsPresheaf X).app (op W) g) =
      (toRationalFunctionsPresheaf U.toScheme).app (op W')
        (U.toScheme.presheaf.map i.op ((U.ι.app W).hom g)) := by
  funext Z'
  change (componentStalkIso U _).hom.hom ((X.presheaf.germ W _ _).hom g) =
    (U.toScheme.presheaf.germ W' _ Z'.2).hom (U.toScheme.presheaf.map i.op ((U.ι.app W).hom g))
  rw [componentStalkIso_hom_germ, TopCat.Presheaf.germ_res_apply]

/-- Restriction of divisors to `U` commutes with negation: `(-D)|_U = -(D|_U)`. -/
@[simp]
theorem restrictDivisor_neg (D : Divisor X) : restrictDivisor U (-D) = -restrictDivisor U D :=
  Finsupp.ext fun E => by simp [restrictDivisor_apply]

/-! ### Orders of vanishing -/

variable [IsLocallyNoetherian X] [IsNormal X]

omit [IsLocallyNoetherian X] in
/-- The square `𝒪_{X,P} ⟶ 𝒪_{X,η} ≅ 𝒪_{U,η'}`, `𝒪_{X,P} ≅ 𝒪_{U,E} ⟶ 𝒪_{U,η'}` commutes, for a prime
divisor `E` of `U` and the prime divisor `P` of `X` with the same generic point. -/
theorem toComponent_comp_componentStalkIso_hom (E : Mori.PrimeDivisor U.toScheme) :
    (primeDivisorOfOpens U E).toComponent ≫
        (componentStalkIso U (ι_componentGenericPoint_mem_component U E)).hom =
      X.presheaf.stalkSpecializes
          (Inseparable.of_eq (genericPoint_primeDivisorOfOpens U E)).specializes' ≫
        U.ι.stalkMap E.genericPoint ≫ E.toComponent := by
  simp only [PrimeDivisor.toComponent, stalkToRationalFunctions, componentStalkIso_hom]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap, TopCat.Presheaf.stalkSpecializes_comp_assoc,
    TopCat.Presheaf.stalkSpecializes_comp_assoc]

/-- **Orders of vanishing on an open subscheme**: `v_E` on `K(U)` is `v_P` on `K(X)`, for a prime
divisor `E` of `U` and the prime divisor `P` of `X` with the same generic point. -/
theorem valuation_componentStalkIso (E : Mori.PrimeDivisor U.toScheme)
    (f : X.presheaf.stalk (componentGenericPoint X (primeDivisorOfOpens U E).component)) :
    E.valuation ((componentStalkIso U (ι_componentGenericPoint_mem_component U E)).hom.hom f) =
      (primeDivisorOfOpens U E).valuation f := by
  let gIso : (primeDivisorOfOpens U E).localRing ≅ E.localRing :=
    X.presheaf.stalkCongr (Inseparable.of_eq (genericPoint_primeDivisorOfOpens U E)) ≪≫
      @asIso _ _ _ _ (U.ι.stalkMap E.genericPoint)
        (IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι _)
  have hcomm : ∀ b, (componentStalkIso U (ι_componentGenericPoint_mem_component U E)).hom.hom
      ((primeDivisorOfOpens U E).toComponent.hom b) = E.toComponent.hom (gIso.hom.hom b) :=
    fun b => by
    rw [← CommRingCat.comp_apply, toComponent_comp_componentStalkIso_hom]
    rfl
  have hv : ∀ b : (primeDivisorOfOpens U E).localRing,
      E.valuation (E.toComponent.hom (gIso.hom.hom b)) =
        (primeDivisorOfOpens U E).valuation ((primeDivisorOfOpens U E).toComponent.hom b) := by
    intro b
    rcases eq_or_ne b 0 with rfl | hb
    · simp only [map_zero]
    · exact MMP.Positivity.valuation_toComponent_ringEquiv E (primeDivisorOfOpens U E)
        gIso.commRingCatIsoToRingEquiv hb
  let := (primeDivisorOfOpens U E).toComponent.hom.toAlgebra
  have :=
    isFractionRing_stalkToRationalFunctions (primeDivisorOfOpens U E).genericPoint_mem_component
  obtain ⟨⟨r, s⟩, hrs⟩ :=
    IsLocalization.surj (nonZeroDivisors (primeDivisorOfOpens U E).localRing) f
  change f * (primeDivisorOfOpens U E).toComponent.hom s =
    (primeDivisorOfOpens U E).toComponent.hom r at hrs
  have hs : (s : (primeDivisorOfOpens U E).localRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have h1 := congrArg (primeDivisorOfOpens U E).valuation hrs
  have h2 := congrArg (fun x => E.valuation
    ((componentStalkIso U (ι_componentGenericPoint_mem_component U E)).hom.hom x)) hrs
  simp only [map_mul, hcomm] at h1 h2
  rw [hv s, hv r] at h2
  exact mul_right_cancel₀
    (MMP.Positivity.valuation_toComponent_ne_zero (primeDivisorOfOpens U E) hs)
    (h2.trans h1.symm)

/-- For a prime divisor `E` of `U` and the prime divisor `P` of `X` with the same generic point,
`v_E(f) ≥ n` on the image of `f` under `componentStalkIso` exactly when `v_P(f) ≥ n`. -/
theorem ordGE_componentStalkIso_iff (E : Mori.PrimeDivisor U.toScheme) (n : ℤ)
    (f : X.presheaf.stalk (componentGenericPoint X (primeDivisorOfOpens U E).component)) :
    E.OrdGE n ((componentStalkIso U (ι_componentGenericPoint_mem_component U E)).hom.hom f) ↔
      (primeDivisorOfOpens U E).OrdGE n f := by
  unfold PrimeDivisor.OrdGE
  rw [valuation_componentStalkIso,
    map_eq_zero_iff _ (componentStalkIso_hom_injective U _)]

/-- **Divisorial sections on an open subscheme**: for `O ⊆ U`, `𝒦_X(O) → 𝒦_U(O)` carries the
sections of `𝒪_X(D)` exactly onto those of `𝒪_U(D|_U)`. -/
theorem isDivisorialSection_rationalFunctionsToOpens_iff (D : Divisor X) {O : X.Opens}
    {O' : U.toScheme.Opens} (hO : O ≤ U) (hO' : U.ι ⁻¹ᵁ O = O')
    (φ : ToType ((rationalFunctionsPresheaf X).obj (op O))) :
    Divisor.IsDivisorialSection (restrictDivisor U D) O' (rationalFunctionsToOpens U hO' φ) ↔
      D.IsDivisorialSection O φ := by
  subst hO'
  have key : ∀ (E : Mori.PrimeDivisor U.toScheme) (hE : (E.support ∩ U.ι ⁻¹ᵁ O).Nonempty)
      (hP : ((primeDivisorOfOpens U E).support ∩ O).Nonempty),
      E.OrdGE (-DivisorWithCoeffs.coeff (restrictDivisor U D) E) (rationalFunctionsToOpens U rfl φ
        ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) ↔
      (primeDivisorOfOpens U E).OrdGE (-D.coeff (primeDivisorOfOpens U E))
        (φ ⟨_, (primeDivisorOfOpens U E).componentGenericPoint_mem_of_nonempty hP⟩) := by
    intro E hE hP
    have hc : DivisorWithCoeffs.coeff (restrictDivisor U D) E = D.coeff (primeDivisorOfOpens U E) :=
      restrictDivisor_apply U D E
    rw [hc, rationalFunctionsToOpens_apply U rfl φ
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ (primeDivisorOfOpens U E).component
      (ι_componentGenericPoint_mem_component U E)
      ((primeDivisorOfOpens U E).componentGenericPoint_mem_of_nonempty hP)]
    exact ordGE_componentStalkIso_iff U E _ _
  constructor
  · rintro h E ⟨x, hxE, hxO⟩
    obtain ⟨y, rfl⟩ : x ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hO hxO
    obtain ⟨E', rfl⟩ := exists_primeDivisorOfOpens_eq U E hxE
    have hE' : (E'.support ∩ U.ι ⁻¹ᵁ O).Nonempty :=
      ⟨y, (mem_support_primeDivisorOfOpens_iff U E' y).1 hxE, hxO⟩
    exact (key E' hE' ⟨_, hxE, hxO⟩).1 (h E' hE')
  · rintro h E ⟨y, hyE, hyO⟩
    have hP : ((primeDivisorOfOpens U E).support ∩ O).Nonempty :=
      ⟨U.ι y, (mem_support_primeDivisorOfOpens_iff U E y).2 hyE, hyO⟩
    exact (key E ⟨y, hyE, hyO⟩ hP).2 (h _ hP)

/-- **Extending a regular function to a divisorial section, on an open piece.** For opens
`O ⊆ U` of `V` and `U' = V ∖ (D ∪ Supp M)`, a regular function `g` on `O ∩ U'` is the restriction
of a section of `𝒪_V(-M)` over `O` exactly when its restriction to `U` is the restriction of a
section of `𝒪_U(-M|_U)` over `O`. -/
theorem exists_divisorialSubmodule_restrictDivisor_iff {V : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] (U : V.Opens) (D M : MMP.Mori.Divisor V) (O : V.Opens) (hO : O ≤ U)
    (g : Γ(V, O ⊓ cU' D M)) :
    (∃ a ∈ (-M).divisorialSubmodule O,
      (MMP.Mori.rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a =
        (MMP.Mori.toRationalFunctionsPresheaf V).app (op (O ⊓ cU' D M)) g) ↔
    (∃ a ∈ MMP.Mori.Divisor.divisorialSubmodule (-(restrictDivisor U M)) (U.ι ⁻¹ᵁ O),
      (MMP.Mori.rationalFunctionsPresheaf U.toScheme).map (homOfLE inf_le_left).op a =
        (MMP.Mori.toRationalFunctionsPresheaf U.toScheme).app
          (op (U.ι ⁻¹ᵁ O ⊓ cU' (restrictDivisor U D) (restrictDivisor U M)))
          (U.toScheme.presheaf.map (eqToHom (show U.ι ⁻¹ᵁ O ⊓
              cU' (restrictDivisor U D) (restrictDivisor U M) = U.ι ⁻¹ᵁ (O ⊓ cU' D M) by
            rw [cU'_restrictDivisor]; rfl)).op ((U.ι.app (O ⊓ cU' D M)).hom g))) := by
  have hW : U.ι ⁻¹ᵁ (O ⊓ cU' D M) =
      U.ι ⁻¹ᵁ O ⊓ cU' (restrictDivisor U D) (restrictDivisor U M) := by
    rw [cU'_restrictDivisor]
    rfl
  constructor
  · rintro ⟨a, ha, hag⟩
    refine ⟨rationalFunctionsToOpens U rfl a, ?_, ?_⟩
    · rw [← restrictDivisor_neg]
      exact (isDivisorialSection_rationalFunctionsToOpens_iff U (-M) hO rfl a).2 ha
    · rw [← rationalFunctionsToOpens_map U rfl hW (homOfLE inf_le_left) (homOfLE inf_le_left),
        hag]
      exact rationalFunctionsToOpens_toRationalFunctionsPresheaf U hW _ g
  · rintro ⟨a', ha', hag'⟩
    obtain ⟨a, rfl⟩ := (rationalFunctionsToOpens_bijective U hO rfl).2 a'
    refine ⟨a, (isDivisorialSection_rationalFunctionsToOpens_iff U (-M) hO rfl a).1 ?_, ?_⟩
    · rw [restrictDivisor_neg]
      exact ha'
    · apply (rationalFunctionsToOpens_bijective U (inf_le_left.trans hO) hW).1
      rw [rationalFunctionsToOpens_map U rfl hW (homOfLE inf_le_left) (homOfLE inf_le_left), hag',
        rationalFunctionsToOpens_toRationalFunctionsPresheaf U hW _ g]

end MMP.FourfoldProofs.FractionalLogComplexProof
