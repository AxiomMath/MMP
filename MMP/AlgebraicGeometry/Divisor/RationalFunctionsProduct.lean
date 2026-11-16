module

public import MMP.AlgebraicGeometry.Divisor.Principal

/-!
# Rational functions of a Noetherian normal scheme as a product of function fields

Let `X` be a Noetherian normal scheme. Every point of `X` lies on exactly one irreducible
component, and there are finitely many, so each irreducible component `Z` is the complement of
the finite union of the others: it is open and closed. Being irreducible it is connected, so the
irreducible components of `X` are exactly its connected components.

The open subscheme `X_Z` on such a component is irreducible and reduced, hence integral, and its
generic point is the generic point `η_Z` of `Z`; so its function field is the stalk of `X_Z` at
`η_Z`, which is the stalk `𝒪_{X,η_Z}`. Hence the ring of rational functions
`K(X) = ∏_Z 𝒪_{X,η_Z}` is the product `∏_Z K(X_Z)` of the function fields of the connected
components, and for `x ∈ Z` the generization map `𝒪_{X,x} → 𝒪_{X,η_Z}` is the inclusion of
`𝒪_{X_Z,x} = 𝒪_{X,x}` into its fraction field `K(X_Z)`.

## Main definitions

* `MMP.Mori.componentOpens`: an irreducible component of a Noetherian normal scheme, as an open.
* `MMP.Mori.irreducibleComponentsEquivConnectedComponents`: the irreducible components are the
  connected components.
* `MMP.Mori.componentFunctionFieldIso`: `K(X_Z) ≅ 𝒪_{X,η_Z}`.
* `MMP.Mori.stalkToComponentFunctionField`: `𝒪_{X,x} → K(X_Z)` for `x ∈ Z`.
* `MMP.Mori.rationalFunctionsEquivPiFunctionField`: `K(X) ≃+* ∏_Z K(X_Z)`.

## Main results

* `MMP.Mori.isClopen_of_mem_irreducibleComponents`: irreducible components are open and closed
  (Stacks 033N, 0357).
* `MMP.Mori.connectedComponent_eq_irreducibleComponent`: connected and irreducible components
  agree.
* `MMP.Mori.isIntegral_componentOpens`: the open subscheme on a component is integral.
* `MMP.Mori.genericPoint_componentOpens`: its generic point is `η_Z`.
* `MMP.Mori.stalkToRationalFunctions_comp_inv_componentFunctionFieldIso`: the generization map
  `𝒪_{X,x} → 𝒪_{X,η_Z}` is the inclusion `𝒪_{X_Z,x} → K(X_Z)`
  (`MMP.Mori.stalkToComponentFunctionField_apply`,
  `MMP.Mori.rationalFunctionsEquivPiFunctionField_apply_stalkToRationalFunctions`), and
  `MMP.Mori.stalkToComponentFunctionField_injective`: that inclusion is injective.

## Implementation notes

The hypothesis that `X` is Noetherian is stated as `IsLocallyNoetherian X` and `CompactSpace X`,
as in the theory of principal divisors. It is used only to know that `X` has finitely many
irreducible components.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
* [Stacks Project, Tag 033N](https://stacks.math.columbia.edu/tag/033N)
* [Stacks Project, Tag 0357](https://stacks.math.columbia.edu/tag/0357)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X]

/-! ### Irreducible and connected components -/

section Components

/-- On a Noetherian normal scheme every irreducible component is open and closed. -/
theorem isClopen_of_mem_irreducibleComponents {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    IsClopen Z := by
  have : IsNoetherian X := ⟨⟩
  refine ⟨isClosed_of_mem_irreducibleComponents Z hZ, ?_⟩
  have hcompl : Zᶜ = ⋃ Z' ∈ irreducibleComponents X \ {Z}, Z' := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff,
      exists_prop]
    refine ⟨fun hx => ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x,
      fun h => hx (h ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩, ?_⟩
    rintro ⟨Z', ⟨hZ', hne⟩, hx⟩ hxZ
    exact hne (congrArg Subtype.val
      (eq_of_mem_irreducibleComponents (Z := ⟨Z', hZ'⟩) (Z' := ⟨Z, hZ⟩) hx hxZ))
  rw [← isClosed_compl_iff, hcompl]
  exact ((NoetherianSpace.finite_irreducibleComponents (α := X)).subset
    Set.sdiff_subset).isClosed_biUnion
    fun Z' hZ' => isClosed_of_mem_irreducibleComponents Z' hZ'.1

/-- On a Noetherian normal scheme an irreducible component is the connected component of each of
its points. -/
theorem connectedComponent_eq_of_mem_irreducibleComponents {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) {x : X} (hx : x ∈ Z) : connectedComponent x = Z :=
  ((isClopen_of_mem_irreducibleComponents hZ).connectedComponent_subset hx).antisymm
    (hZ.1.isConnected.subset_connectedComponent hx)

/-- On a Noetherian normal scheme the connected component of a point is its irreducible
component. -/
theorem connectedComponent_eq_irreducibleComponent (x : X) :
    connectedComponent x = irreducibleComponent x :=
  connectedComponent_eq_of_mem_irreducibleComponents
    (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent

/-- On a Noetherian normal scheme the connected component of a point is an irreducible
component. -/
theorem connectedComponent_mem_irreducibleComponents (x : X) :
    connectedComponent x ∈ irreducibleComponents X :=
  connectedComponent_eq_irreducibleComponent x ▸ irreducibleComponent_mem_irreducibleComponents x

/-- On a Noetherian normal scheme the irreducible components are the connected components. -/
theorem mem_irreducibleComponents_iff_exists_eq_connectedComponent {Z : Set X} :
    Z ∈ irreducibleComponents X ↔ ∃ x, connectedComponent x = Z := by
  refine ⟨fun hZ => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hZ.1.nonempty
    exact ⟨x, connectedComponent_eq_of_mem_irreducibleComponents hZ hx⟩
  · rintro ⟨x, rfl⟩
    exact connectedComponent_mem_irreducibleComponents x

variable (X) in
/-- On a Noetherian normal scheme the irreducible components are the connected components: an
irreducible component goes to the connected component of any of its points. -/
def irreducibleComponentsEquivConnectedComponents :
    irreducibleComponents X ≃ ConnectedComponents X where
  toFun Z := ConnectedComponents.mk (componentGenericPoint X Z)
  invFun := Quotient.lift
    (fun x => (⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩ :
      irreducibleComponents X))
    (fun x y h => Subtype.ext <| (connectedComponent_eq_irreducibleComponent x).symm.trans <|
      (ConnectedComponents.coe_eq_coe.mp (Quotient.sound h)).trans
        (connectedComponent_eq_irreducibleComponent y))
  left_inv Z := Subtype.ext <| (connectedComponent_eq_irreducibleComponent _).symm.trans <|
    connectedComponent_eq_of_mem_irreducibleComponents Z.2
      (isGenericPoint_componentGenericPoint X Z).mem
  right_inv := by
    rintro ⟨x⟩
    change ConnectedComponents.mk (componentGenericPoint X _) = ConnectedComponents.mk x
    rw [ConnectedComponents.coe_eq_coe', connectedComponent_eq_irreducibleComponent]
    exact (isGenericPoint_componentGenericPoint X
      ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩).mem

/-- An irreducible component goes to the connected component of its generic point. -/
@[simp]
theorem irreducibleComponentsEquivConnectedComponents_apply (Z : irreducibleComponents X) :
    irreducibleComponentsEquivConnectedComponents X Z =
      ConnectedComponents.mk (componentGenericPoint X Z) :=
  rfl

/-- The irreducible component corresponding to the connected component of `x` is
`connectedComponent x`. -/
@[simp]
theorem coe_irreducibleComponentsEquivConnectedComponents_symm (x : X) :
    ((irreducibleComponentsEquivConnectedComponents X).symm (ConnectedComponents.mk x)).1 =
      connectedComponent x :=
  (connectedComponent_eq_irreducibleComponent x).symm

end Components

/-! ### The open subscheme on a component -/

section ComponentOpens

/-- An irreducible component `Z` of a Noetherian normal scheme `X`, as an open of `X`; it is a
connected component of `X`. -/
def componentOpens (Z : irreducibleComponents X) : X.Opens :=
  ⟨Z.1, (isClopen_of_mem_irreducibleComponents Z.2).isOpen⟩

/-- The underlying set of `componentOpens Z` is `Z`. -/
@[simp]
theorem coe_componentOpens (Z : irreducibleComponents X) : (componentOpens Z : Set X) = Z.1 :=
  rfl

/-- A point lies in `componentOpens Z` if and only if it lies in `Z`. -/
@[simp]
theorem mem_componentOpens {Z : irreducibleComponents X} {x : X} :
    x ∈ componentOpens Z ↔ x ∈ Z.1 :=
  Iff.rfl

/-- The open subscheme on an irreducible component is irreducible. -/
instance irreducibleSpace_componentOpens (Z : irreducibleComponents X) :
    IrreducibleSpace (componentOpens Z).toScheme :=
  Subtype.irreducibleSpace Z.2.1

/-- The open subscheme on an irreducible component of a Noetherian normal scheme is integral. -/
instance isIntegral_componentOpens (Z : irreducibleComponents X) :
    IsIntegral (componentOpens Z).toScheme :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The generic point `η_Z`, as a point of the open subscheme on `Z`. -/
def componentOpensGenericPoint (Z : irreducibleComponents X) : componentOpens Z :=
  ⟨componentGenericPoint X Z, (isGenericPoint_componentGenericPoint X Z).mem⟩

/-- The underlying point of `componentOpensGenericPoint Z` is the generic point `η_Z`. -/
@[simp]
theorem coe_componentOpensGenericPoint (Z : irreducibleComponents X) :
    (componentOpensGenericPoint Z : X) = componentGenericPoint X Z :=
  rfl

/-- The generic point of the open subscheme on `Z` is the generic point `η_Z` of `Z`. -/
theorem genericPoint_componentOpens (Z : irreducibleComponents X) :
    genericPoint (componentOpens Z).toScheme = componentOpensGenericPoint Z := by
  refine (genericPoint_spec (componentOpens Z).toScheme).eq ?_
  change closure {componentOpensGenericPoint Z} = Set.univ
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
  change Subtype.val ⁻¹' closure {componentGenericPoint X Z} = _
  rw [(isGenericPoint_componentGenericPoint X Z).def]
  exact Subtype.coe_preimage_self _

/-- The function field of the open subscheme on `Z` is the local ring `𝒪_{X,η_Z}`, the `Z`-th
factor of the ring of rational functions. -/
def componentFunctionFieldIso (Z : irreducibleComponents X) :
    (componentOpens Z).toScheme.functionField ≅ X.presheaf.stalk (componentGenericPoint X Z) :=
  (componentOpens Z).toScheme.presheaf.stalkCongr
      (.of_eq (genericPoint_componentOpens Z)) ≪≫
    (componentOpens Z).stalkIso (componentOpensGenericPoint Z)

/-- The inverse of `componentFunctionFieldIso Z` is the stalk map of the inclusion of the open
subscheme on `Z` at `η_Z`, followed by the identification of that stalk with the function field. -/
theorem componentFunctionFieldIso_inv (Z : irreducibleComponents X) :
    (componentFunctionFieldIso Z).inv =
      (componentOpens Z).ι.stalkMap (componentOpensGenericPoint Z) ≫
        (componentOpens Z).toScheme.presheaf.stalkSpecializes
          (genericPoint_componentOpens Z ▸ specializes_rfl) := by
  rw [← Scheme.Opens.stalkIso_inv]
  rfl

/-- For `x ∈ Z`, the generization map `𝒪_{X,x} → 𝒪_{X,η_Z}` is the inclusion of
`𝒪_{X_Z,x} = 𝒪_{X,x}` into the function field of the open subscheme `X_Z` on `Z`. -/
theorem stalkToRationalFunctions_comp_inv_componentFunctionFieldIso
    {Z : irreducibleComponents X} {x : X} (hx : x ∈ Z.1) :
    stalkToRationalFunctions X hx ≫ (componentFunctionFieldIso Z).inv =
      ((componentOpens Z).stalkIso ⟨x, hx⟩).inv ≫
        (componentOpens Z).toScheme.presheaf.stalkSpecializes
          ((genericPoint_spec (componentOpens Z).toScheme).specializes trivial) := by
  have h : componentOpensGenericPoint Z ⤳ (⟨x, hx⟩ : componentOpens Z) :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp
      ((isGenericPoint_componentGenericPoint X Z).specializes hx)
  have e := Scheme.Hom.stalkSpecializes_stalkMap (componentOpens Z).ι _ _ h
  rw [componentFunctionFieldIso_inv, Scheme.Opens.stalkIso_inv, stalkToRationalFunctions]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)
  exact (Category.assoc _ _ _).trans (congrArg _ (TopCat.Presheaf.stalkSpecializes_comp _ _ _))

/-- A point `x` of an irreducible component `Z`, as a point of the open subscheme on `Z`. -/
abbrev componentOpensPoint {Z : irreducibleComponents X} {x : X} (hx : x ∈ Z.1) :
    (componentOpens Z).toScheme :=
  ⟨x, hx⟩

/-- For `x ∈ Z`, the map `𝒪_{X,x} → K(X_Z)` from the local ring at `x` to the function field of the
open subscheme on the component through `x`: the generization map `𝒪_{X,x} → 𝒪_{X,η_Z}` followed
by `𝒪_{X,η_Z} ≅ K(X_Z)`. -/
def stalkToComponentFunctionField {Z : irreducibleComponents X} {x : X} (hx : x ∈ Z.1) :
    X.presheaf.stalk x ⟶ (componentOpens Z).toScheme.functionField :=
  stalkToRationalFunctions X hx ≫ (componentFunctionFieldIso Z).inv

/-- The map `𝒪_{X,x} → K(X_Z)` is the inclusion of the local ring `𝒪_{X_Z,x} = 𝒪_{X,x}` of the
integral scheme `X_Z` into its function field. -/
theorem stalkToComponentFunctionField_apply {Z : irreducibleComponents X} {x : X} (hx : x ∈ Z.1)
    (s : X.presheaf.stalk x) :
    stalkToComponentFunctionField hx s =
      algebraMap ((componentOpens Z).toScheme.presheaf.stalk (componentOpensPoint hx))
        (componentOpens Z).toScheme.functionField
        (((componentOpens Z).stalkIso (componentOpensPoint hx)).inv s) :=
  congr($(stalkToRationalFunctions_comp_inv_componentFunctionFieldIso hx).hom s)

/-- On a Noetherian normal scheme the map `𝒪_{X,x} → K(X_Z)` is injective. -/
theorem stalkToComponentFunctionField_injective {Z : irreducibleComponents X} {x : X}
    (hx : x ∈ Z.1) : Function.Injective (stalkToComponentFunctionField hx) :=
  (componentFunctionFieldIso Z).commRingCatIsoToRingEquiv.symm.injective.comp
    (stalkToRationalFunctions_injective hx)

end ComponentOpens

/-! ### The ring of rational functions as a product of function fields -/

section ProductOfFunctionFields

variable (X) in
/-- On a Noetherian normal scheme the ring of rational functions `K(X) = ∏_Z 𝒪_{X,η_Z}` is the
product `∏_Z K(X_Z)` of the function fields of the open subschemes on its irreducible components,
which are its connected components. -/
def rationalFunctionsEquivPiFunctionField :
    RationalFunctions X ≃+*
      ∀ Z : irreducibleComponents X, (componentOpens Z).toScheme.functionField :=
  RingEquiv.piCongrRight fun Z => (componentFunctionFieldIso Z).commRingCatIsoToRingEquiv.symm

/-- The `Z`-th factor of the image of `φ` in `∏_Z K(X_Z)` is the `Z`-th component of `φ`, carried
to `K(X_Z)` by `componentFunctionFieldIso Z`. -/
@[simp]
theorem rationalFunctionsEquivPiFunctionField_apply (φ : RationalFunctions X)
    (Z : irreducibleComponents X) :
    rationalFunctionsEquivPiFunctionField X φ Z =
      (componentFunctionFieldIso Z).inv (RationalFunctions.component X Z φ) :=
  rfl

/-- The `Z`-th component of the rational function corresponding to `f ∈ ∏_Z K(X_Z)` is `f Z`,
carried to `𝒪_{X,η_Z}` by `componentFunctionFieldIso Z`. -/
@[simp]
theorem component_rationalFunctionsEquivPiFunctionField_symm
    (f : ∀ Z : irreducibleComponents X, (componentOpens Z).toScheme.functionField)
    (Z : irreducibleComponents X) :
    RationalFunctions.component X Z ((rationalFunctionsEquivPiFunctionField X).symm f) =
      (componentFunctionFieldIso Z).hom (f Z) :=
  rfl

/-- The projection of `∏_Z K(X_Z)` to its `Z`-th factor corresponds to the projection
`RationalFunctions.component` of `K(X)`. -/
theorem evalRingHom_comp_rationalFunctionsEquivPiFunctionField (Z : irreducibleComponents X) :
    (Pi.evalRingHom _ Z).comp (rationalFunctionsEquivPiFunctionField X).toRingHom =
      (componentFunctionFieldIso Z).inv.hom.comp (RationalFunctions.component X Z) :=
  rfl

/-- Under `K(X) ≃+* ∏_Z K(X_Z)`, the generization map `𝒪_{X,x} → 𝒪_{X,η_Z}` into the factor of
the component `Z` through `x` is the inclusion `𝒪_{X_Z,x} → K(X_Z)`. -/
theorem rationalFunctionsEquivPiFunctionField_apply_stalkToRationalFunctions
    {Z : irreducibleComponents X} {x : X} (hx : x ∈ Z.1) (φ : RationalFunctions X)
    (s : X.presheaf.stalk x)
    (hφ : RationalFunctions.component X Z φ = stalkToRationalFunctions X hx s) :
    rationalFunctionsEquivPiFunctionField X φ Z =
      algebraMap ((componentOpens Z).toScheme.presheaf.stalk (componentOpensPoint hx))
        (componentOpens Z).toScheme.functionField
        (((componentOpens Z).stalkIso (componentOpensPoint hx)).inv s) := by
  rw [rationalFunctionsEquivPiFunctionField_apply, hφ, ← stalkToComponentFunctionField_apply]
  rfl

end ProductOfFunctionFields

end MMP.Mori
