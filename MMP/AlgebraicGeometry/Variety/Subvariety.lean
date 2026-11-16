module

public import MMP.AlgebraicGeometry.Variety.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight

/-!
# Subvarieties: the closed subscheme, the order, generic points and dimension

API for `MMP.Intersection.Scheme.Subvariety` (Fulton B.1.2), an integral closed subscheme of a
scheme given by its ideal sheaf.

* A subvariety `V` is a scheme `V.toScheme` with a closed immersion `V.ι` into `X`; over a base
  `S` of `X` it is a scheme over `S`, and it is of finite type over a field when `X` is.
* Subvarieties are ordered by inclusion of closed subschemes. A subvariety is the reduced induced
  structure on its support (`ideal_eq_vanishingIdeal`), so the order is an order isomorphism with
  the irreducible closed subsets of `X` (`orderIsoIrreducibleCloseds`), and subvarieties
  correspond to points through their generic points (`equivPoints`).
* The dimension `V.dim` of a subvariety is the Krull dimension of its underlying space, equal to
  that of its support (`dim_eq_topologicalKrullDim_support`) and to its height among the
  subvarieties of `X` (`dim_eq_height`). `HasDim T k` says that a space has dimension the
  integer `k`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.1–B.2
-/

@[expose] public noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MMP.Intersection

/-! ### Spaces of a given integer dimension -/

/-- A topological space `T` *has dimension* the integer `k` (Fulton B.1.3) if `k` is a natural
number `n` and the Krull dimension of `T` is `n`. -/
def HasDim (T : Type v) [TopologicalSpace T] (k : ℤ) : Prop :=
  ∃ n : ℕ, (n : ℤ) = k ∧ topologicalKrullDim T = n

/-- A space of dimension `k` has `0 ≤ k`. -/
theorem HasDim.nonneg {T : Type v} [TopologicalSpace T] {k : ℤ} (h : HasDim T k) : 0 ≤ k := by
  obtain ⟨n, rfl, -⟩ := h
  exact Int.natCast_nonneg n

/-- A space has dimension the natural number `n` iff its Krull dimension is `n`. -/
@[simp]
theorem hasDim_natCast_iff {T : Type v} [TopologicalSpace T] (n : ℕ) :
    HasDim T n ↔ topologicalKrullDim T = n := by
  constructor
  · rintro ⟨m, hm, h⟩
    rw [← Int.ofNat_inj.mp hm]
    exact h
  · exact fun h ↦ ⟨n, rfl, h⟩

namespace Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ### The reduced induced closed subscheme structure -/

namespace IdealSheafData

/-- The closed subscheme of `I` is homeomorphic to the support of `I`. -/
def subschemeHomeomorphSupport (I : X.IdealSheafData) : I.subscheme ≃ₜ I.support :=
  I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr I.range_subschemeι)

/-- The closed subscheme of `I` is irreducible iff its support is. -/
theorem irreducibleSpace_subscheme_iff (I : X.IdealSheafData) :
    IrreducibleSpace I.subscheme ↔ IsIrreducible (I.support : Set X) := by
  rw [(subschemeHomeomorphSupport I).irreducibleSpace_iff, isIrreducible_iff_irreducibleSpace]
  exact Iff.rfl

end IdealSheafData

namespace Subvariety

/-! ### The closed subscheme -/

/-- Subvarieties with the same ideal sheaf are equal. -/
@[ext]
theorem ext {V W : Subvariety X} (h : V.ideal = W.ideal) : V = W := by
  cases V; cases W; cases h; rfl

/-- A subvariety is determined by its ideal sheaf. -/
theorem ideal_injective : Function.Injective (ideal : Subvariety X → X.IdealSheafData) :=
  fun _ _ h ↦ ext h

/-- The subvariety `V` as a scheme: the closed subscheme of `X` it is. -/
abbrev toScheme (V : Subvariety X) : AlgebraicGeometry.Scheme.{u} := V.ideal.subscheme

/-- The scheme of a subvariety is integral. -/
instance (V : Subvariety X) : IsIntegral V.toScheme := V.isIntegral

/-- The closed immersion of the subvariety `V` into `X`. -/
abbrev ι (V : Subvariety X) : V.toScheme ⟶ X := V.ideal.subschemeι

/-- The generic point of `V` is the image under `V.ι` of the generic point of `V.toScheme`. -/
theorem genericPoint_eq (V : Subvariety X) :
    V.genericPoint = V.ι (_root_.genericPoint V.toScheme) := rfl

/-- The support of `V` is the support of its ideal sheaf. -/
theorem support_eq (V : Subvariety X) : V.support = (V.ideal.support : Set X) := rfl

/-- Over a base `S` of `X`, a subvariety of `X` is a scheme over `S` through `X`. -/
instance instOverToScheme {S : AlgebraicGeometry.Scheme.{u}} [X.Over S] (V : Subvariety X) :
    V.toScheme.Over S :=
  ⟨V.ι ≫ X ↘ S⟩

/-- The closed immersion `V.ι` is a morphism over `S`. -/
instance isOver_ι {S : AlgebraicGeometry.Scheme.{u}} [X.Over S] (V : Subvariety X) :
    V.ι.IsOver S :=
  ⟨rfl⟩

/-- A subvariety of a scheme locally of finite type over a field `K` is locally of finite type
over `K`. -/
instance locallyOfFiniteType_toScheme (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (V : Subvariety X) :
    LocallyOfFiniteType (V.toScheme ↘ Spec (.of K)) :=
  inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X ↘ Spec (.of K)))

/-- A subvariety of a scheme quasi-compact over a field `K` is quasi-compact over `K`. -/
instance quasiCompact_toScheme (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))] (V : Subvariety X) :
    QuasiCompact (V.toScheme ↘ Spec (.of K)) :=
  inferInstanceAs (QuasiCompact (V.ι ≫ X ↘ Spec (.of K)))

/-! ### The order -/

/-- Subvarieties are ordered by inclusion of closed subschemes: `V ≤ W` iff the ideal of `W` is
contained in the ideal of `V`. -/
instance : PartialOrder (Subvariety X) :=
  PartialOrder.lift (fun V ↦ OrderDual.toDual V.ideal) fun _ _ h ↦
    ext (OrderDual.toDual.injective h)

/-- `V ≤ W` iff the ideal sheaf of `W` is contained in that of `V`. -/
theorem le_iff {V W : Subvariety X} : V ≤ W ↔ W.ideal ≤ V.ideal := Iff.rfl

/-- A subvariety is the reduced induced closed subscheme structure on its support. -/
theorem ideal_eq_vanishingIdeal (V : Subvariety X) :
    V.ideal = .vanishingIdeal V.ideal.support :=
  AlgebraicGeometry.Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
    V.ideal V.ideal.support rfl

/-- The ideal sheaf of a subvariety is radical. -/
theorem radical_ideal (V : Subvariety X) : V.ideal.radical = V.ideal :=
  AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support.symm.trans
    V.ideal_eq_vanishingIdeal.symm

/-- The irreducible closed subset of `V` is its support. -/
@[simp]
theorem coe_toIrreducibleCloseds (V : Subvariety X) :
    (V.toIrreducibleCloseds : Set X) = V.support := rfl

/-- The subvariety with support an irreducible closed subset `Z` of `X`: the reduced induced
closed subscheme structure on `Z`. -/
def ofIrreducibleCloseds (Z : IrreducibleCloseds X) : Subvariety X :=
  ofIsIrreducible ⟨Z, Z.isClosed⟩ Z.isIrreducible

/-- The ideal sheaf of `ofIrreducibleCloseds Z` is the vanishing ideal of `Z`. -/
@[simp]
theorem ideal_ofIrreducibleCloseds (Z : IrreducibleCloseds X) :
    (ofIrreducibleCloseds Z).ideal = .vanishingIdeal (⟨Z, Z.isClosed⟩ : Closeds X) := rfl

/-- The support of `ofIrreducibleCloseds Z` is `Z`. -/
@[simp]
theorem support_ofIrreducibleCloseds (Z : IrreducibleCloseds X) :
    (ofIrreducibleCloseds Z).support = Z :=
  AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- The support of the ideal sheaf of `ofIrreducibleCloseds Z` is `Z`. -/
@[simp]
theorem ideal_support_ofIrreducibleCloseds (Z : IrreducibleCloseds X) :
    (ofIrreducibleCloseds Z).ideal.support = (⟨Z, Z.isClosed⟩ : Closeds X) :=
  Closeds.ext (support_ofIrreducibleCloseds Z)

/-- The irreducible closed subset of `ofIrreducibleCloseds Z` is `Z`. -/
@[simp]
theorem toIrreducibleCloseds_ofIrreducibleCloseds (Z : IrreducibleCloseds X) :
    (ofIrreducibleCloseds Z).toIrreducibleCloseds = Z :=
  IrreducibleCloseds.ext (support_ofIrreducibleCloseds Z)

/-- A subvariety is the reduced induced structure on its support. -/
@[simp]
theorem ofIrreducibleCloseds_toIrreducibleCloseds (V : Subvariety X) :
    ofIrreducibleCloseds V.toIrreducibleCloseds = V :=
  ext (V.ideal_eq_vanishingIdeal.symm : _)

/-- `V ≤ W` iff the support of `V` is contained in the support of `W`. -/
theorem le_iff_support_le {V W : Subvariety X} : V ≤ W ↔ V.support ⊆ W.support := by
  rw [le_iff, V.ideal_eq_vanishingIdeal,
    ← AlgebraicGeometry.Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  rfl

/-- A subvariety is determined by its support. -/
theorem support_injective : Function.Injective (support : Subvariety X → Set X) :=
  fun _ _ h ↦ le_antisymm (le_iff_support_le.mpr h.le) (le_iff_support_le.mpr h.ge)

/-- Subvarieties of `X`, ordered by inclusion, correspond to irreducible closed subsets of `X`:
a subvariety goes to its support, an irreducible closed subset to its reduced induced closed
subscheme structure. -/
def orderIsoIrreducibleCloseds : Subvariety X ≃o IrreducibleCloseds X where
  toFun := toIrreducibleCloseds
  invFun := ofIrreducibleCloseds
  left_inv := ofIrreducibleCloseds_toIrreducibleCloseds
  right_inv := toIrreducibleCloseds_ofIrreducibleCloseds
  map_rel_iff' := le_iff_support_le.symm

/-- `orderIsoIrreducibleCloseds` sends `V` to `V.toIrreducibleCloseds`. -/
@[simp]
theorem orderIsoIrreducibleCloseds_apply (V : Subvariety X) :
    orderIsoIrreducibleCloseds V = V.toIrreducibleCloseds := rfl

/-- The inverse of `orderIsoIrreducibleCloseds` sends `Z` to `ofIrreducibleCloseds Z`. -/
@[simp]
theorem orderIsoIrreducibleCloseds_symm_apply (Z : IrreducibleCloseds X) :
    orderIsoIrreducibleCloseds.symm Z = ofIrreducibleCloseds Z := rfl

/-! ### Generic points -/

/-- The closure of the generic point of `V` is the support of `V`. -/
theorem closure_genericPoint (V : Subvariety X) : closure {V.genericPoint} = V.support :=
  V.isGenericPoint_genericPoint.def

/-- The subvariety whose generic point is `x`: the reduced induced closed subscheme structure on
the closure of `{x}`. -/
def ofPoint (x : X) : Subvariety X :=
  ofIrreducibleCloseds ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- The support of `ofPoint x` is the closure of `{x}`. -/
@[simp]
theorem support_ofPoint (x : X) : (ofPoint x).support = closure {x} :=
  support_ofIrreducibleCloseds _

/-- The generic point of `ofPoint x` is `x`. -/
@[simp]
theorem genericPoint_ofPoint (x : X) : (ofPoint x).genericPoint = x := by
  refine (ofPoint x).isGenericPoint_genericPoint.eq ?_
  rw [support_ofPoint]
  exact isGenericPoint_closure

/-- The subvariety with generic point `V.genericPoint` is `V`. -/
@[simp]
theorem ofPoint_genericPoint (V : Subvariety X) : ofPoint V.genericPoint = V :=
  support_injective (by rw [support_ofPoint, closure_genericPoint])

/-- Subvarieties of `X` correspond to points of `X`, through their generic points. -/
def equivPoints : Subvariety X ≃ X where
  toFun := genericPoint
  invFun := ofPoint
  left_inv := ofPoint_genericPoint
  right_inv := genericPoint_ofPoint

/-- `equivPoints` sends `V` to its generic point. -/
@[simp]
theorem equivPoints_apply (V : Subvariety X) : equivPoints V = V.genericPoint := rfl

/-- The inverse of `equivPoints` sends `x` to `ofPoint x`. -/
@[simp]
theorem equivPoints_symm_apply (x : X) : equivPoints.symm x = ofPoint x := rfl

/-- `V ≤ W` iff the generic point of `W` specializes to the generic point of `V`. -/
theorem le_iff_specializes {V W : Subvariety X} :
    V ≤ W ↔ W.genericPoint ⤳ V.genericPoint := by
  rw [le_iff_support_le, specializes_iff_closure_subset, closure_genericPoint,
    closure_genericPoint]

/-- A subvariety is determined by its generic point. -/
theorem genericPoint_injective : Function.Injective (genericPoint : Subvariety X → X) :=
  equivPoints.injective

/-- Subvarieties of `X`, ordered by inclusion, are the points of `X` in the specialization order:
`V ≤ W` iff the generic point of `W` specializes to that of `V`. -/
def orderIsoPoints : Subvariety X ≃o X where
  toEquiv := equivPoints
  map_rel_iff' {V W} := by
    simp only [equivPoints_apply]
    rw [AlgebraicGeometry.Scheme.le_iff_specializes, ← le_iff_specializes]

/-- `orderIsoPoints` sends `V` to its generic point. -/
@[simp]
theorem orderIsoPoints_apply (V : Subvariety X) : orderIsoPoints V = V.genericPoint := rfl

end Subvariety

/-! ### Dimension -/

/-- **Fulton's definition of dimension** (B.1.3): the dimension of `X` is the supremum of the
lengths of chains of subvarieties of `X`. -/
theorem dimension_eq_krullDim_subvariety (X : AlgebraicGeometry.Scheme.{u}) :
    dimension X = Order.krullDim (Subvariety X) :=
  (Order.krullDim_eq_of_orderIso Subvariety.orderIsoIrreducibleCloseds).symm

/-- The irreducible closed subsets contained in an irreducible closed subset `Z` are the
irreducible closed subsets of the subspace `Z`. -/
def irreducibleClosedsIicOrderIso {α : Type*} [TopologicalSpace α] (Z : IrreducibleCloseds α) :
    Set.Iic Z ≃o IrreducibleCloseds (Z : Set α) where
  toFun T := ⟨Subtype.val ⁻¹' (T.1 : Set α), by
      have := Subtype.irreducibleSpace T.1.isIrreducible
      rw [show Subtype.val ⁻¹' (T.1 : Set α) = Set.range (Set.inclusion T.2) from
        (Set.range_inclusion T.2).symm, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (continuous_inclusion T.2).continuousOn,
    T.1.isClosed.preimage continuous_subtype_val⟩
  invFun S := ⟨⟨Subtype.val '' (S : Set (Z : Set α)),
      S.isIrreducible.image _ continuous_subtype_val.continuousOn,
      Z.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ S.isClosed⟩,
    by
      change Subtype.val '' (S : Set (Z : Set α)) ⊆ (Z : Set α)
      exact Subtype.coe_image_subset _ _⟩
  left_inv T := by
    ext1
    refine IrreducibleCloseds.ext ?_
    change Subtype.val '' (Subtype.val ⁻¹' (T.1 : Set α)) = _
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr T.2]
  right_inv S := IrreducibleCloseds.ext (Set.preimage_image_eq _ Subtype.val_injective)
  map_rel_iff' {T T'} := by
    change Subtype.val ⁻¹' (T.1 : Set α) ⊆ Subtype.val ⁻¹' (T'.1 : Set α) ↔ (T.1 : Set α) ⊆ T'.1
    constructor
    · intro h x hx
      exact h (show (⟨x, T.2 hx⟩ : (Z : Set α)) ∈ Subtype.val ⁻¹' (T.1 : Set α) from hx)
    · exact fun h ↦ Set.preimage_mono h

namespace Subvariety

/-- The *dimension* of a subvariety (Fulton B.1.3): the Krull dimension of its underlying
space. -/
abbrev dim (V : Subvariety X) : WithBot ℕ∞ := dimension V.toScheme

/-- A subvariety `V` *has dimension* the integer `k`. -/
abbrev HasDim (V : Subvariety X) (k : ℤ) : Prop := MMP.Intersection.HasDim V.toScheme k

/-- The dimension of a subvariety `V` is the Krull dimension of its support. -/
theorem dim_eq_topologicalKrullDim_support (V : Subvariety X) :
    V.dim = topologicalKrullDim V.support :=
  (IdealSheafData.subschemeHomeomorphSupport V.ideal).isHomeomorph.topologicalKrullDim_eq

/-- The dimension of a subvariety `V` is its height in the poset of subvarieties of `X`: the
supremum of the lengths of chains of subvarieties `V₀ ⊊ V₁ ⊊ ⋯ ⊊ Vₙ = V`. -/
theorem dim_eq_height (V : Subvariety X) : V.dim = Order.height V := by
  rw [dim_eq_topologicalKrullDim_support, ← Order.height_orderIso orderIsoIrreducibleCloseds V,
    Order.height_eq_krullDim_Iic,
    Order.krullDim_eq_of_orderIso (irreducibleClosedsIicOrderIso _)]
  rfl

/-- The dimension of a subvariety is the height of its generic point. -/
theorem dim_eq_height_genericPoint (V : Subvariety X) :
    V.dim = Order.height V.genericPoint := by
  rw [dim_eq_height, ← orderIsoPoints_apply, Order.height_orderIso]

/-- Two subvarieties `V ≤ W` of the same finite dimension are equal. -/
theorem eq_of_le_of_dim_eq {V W : Subvariety X} (hle : V ≤ W) (hdim : V.dim = W.dim)
    (hfin : V.dim ≠ ⊤) : V = W := by
  by_contra hne
  have hlt : V < W := lt_of_le_of_ne hle hne
  rw [dim_eq_height, dim_eq_height] at hdim
  rw [dim_eq_height] at hfin
  have hfin' : Order.height V < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h ↦ hfin ?_
    rw [h]
    rfl
  have := Order.height_strictMono hlt hfin'
  rw [WithBot.coe_inj.mp hdim] at this
  exact lt_irrefl _ this

/-- The codimension of a subvariety is the coheight of its generic point. -/
theorem codim_eq_coheight_genericPoint (V : Subvariety X) :
    V.codim = Order.coheight V.genericPoint := by
  rw [codim, codimension_eq_coheight, ← orderIsoIrreducibleCloseds_apply,
    Order.coheight_orderIso, ← orderIsoPoints_apply, Order.coheight_orderIso]

/-- **Fulton, §1.1.** For a subvariety `V` of an integral scheme `X` locally of finite type over
a field, `dim V + codim(V, X) = dim X`. -/
theorem dim_add_codim (K : Type u) [Field K] [X.Over (Spec (.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (V : Subvariety X) :
    V.dim + (V.codim : WithBot ℕ∞) = dimension X := by
  rw [dim_eq_height_genericPoint, codim_eq_coheight_genericPoint, ← WithBot.coe_add,
    MMP.height_add_coheight_eq_krullDim K V.genericPoint, dimension_eq_krullDim_subvariety,
    Order.krullDim_eq_of_orderIso orderIsoPoints]

/-- The support of the subvariety with generic point the generic point of `X` is all of `X`. -/
theorem support_ofPoint_genericPoint [IrreducibleSpace X] :
    (ofPoint (_root_.genericPoint X)).support = Set.univ := by
  rw [support_ofPoint, genericPoint_closure]

/-- On a reduced irreducible scheme `X`, the closed immersion of the subvariety with generic
point the generic point of `X` is an isomorphism: this subvariety is `X` itself. -/
instance isIso_ι_ofPoint_genericPoint [IrreducibleSpace X] [IsReduced X] :
    IsIso (ofPoint (_root_.genericPoint X)).ι :=
  have : Surjective (ofPoint (_root_.genericPoint X)).ι := ⟨Set.range_eq_univ.1 (by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
    exact support_ofPoint_genericPoint)⟩
  isIso_of_isClosedImmersion_of_surjective _

/-- If an integral scheme `X` has dimension `n`, so does the subvariety `X` itself. -/
theorem hasDim_ofPoint_genericPoint [IsIntegral X] {n : ℤ} (hX : MMP.Intersection.HasDim X n) :
    (ofPoint (_root_.genericPoint X)).HasDim n := by
  obtain ⟨m, hm, hd⟩ := hX
  refine ⟨m, hm, ?_⟩
  rw [← hd]
  exact (ofPoint (_root_.genericPoint X)).ι.homeomorph.isHomeomorph.topologicalKrullDim_eq

end Subvariety

end Scheme

end MMP.Intersection
