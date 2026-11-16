module

public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.Basic
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.LocalIsomorphism
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Regular functions and proper birational morphisms in codimension one

On a normal integral locally Noetherian scheme, a non-zero rational function is regular on a
non-empty open set if and only if its order of vanishing along every prime divisor meeting that
open set is non-negative. A universally closed birational morphism of integral schemes onto a
normal scheme is a local isomorphism over every point of codimension one.

## Main results

* `exists_germToFunctionField_eq_iff_forall_zero_le_ord`: a non-zero rational function on a
  normal integral locally Noetherian scheme is regular on a non-empty open `V` if and only if
  `ord_P(φ) ≥ 0` for every prime divisor `P` meeting `V`.
* `exists_isIso_stalkMap_of_valuationRing`: for a universally closed dominant morphism of
  integral schemes inducing an isomorphism of function fields, over a point whose local ring is
  a valuation ring there is a point at which the morphism induces an isomorphism of local rings.
* `exists_preimage_of_coheight_eq_one`: over every point of codimension one of a normal target,
  such a morphism has a point of codimension one outside its exceptional locus.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry Order

namespace MMP.Intersection

open MMP.Mori (Divisor)

variable {X : Scheme.{u}}

/-! ### Regular functions on a normal scheme -/

/-- A prime divisor meeting an open set has its generic point in that open set. -/
theorem genericPoint_mem_of_support_inter_nonempty (P : MMP.Mori.PrimeDivisor X) {V : X.Opens}
    (h : (P.support ∩ V).Nonempty) : P.genericPoint ∈ V := by
  obtain ⟨z, hzP, hzV⟩ := h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hzP
  exact (specializes_iff_mem_closure.mpr hzP).mem_open V.isOpen hzV

/-- A prime divisor meets every open set containing its generic point. -/
theorem support_inter_nonempty_of_genericPoint_mem (P : MMP.Mori.PrimeDivisor X) {V : X.Opens}
    (h : P.genericPoint ∈ V) : (P.support ∩ V).Nonempty := by
  refine ⟨P.genericPoint, ?_, h⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- On an integral scheme, the generic point lies in every non-empty open set. -/
theorem genericPoint_mem_opens [IsIntegral X] (V : X.Opens) [h : Nonempty V] :
    genericPoint X ∈ V :=
  ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using h)

/-- On an integral scheme, the image of a section in the function field is unchanged by
restriction to a smaller non-empty open set. -/
theorem germToFunctionField_map [IsIntegral X] {U V : X.Opens} (i : U ⟶ V) [Nonempty U]
    (s : Γ(X, V)) :
    haveI : Nonempty V := ⟨⟨_, i.le (genericPoint_mem_opens U)⟩⟩
    X.germToFunctionField U (X.presheaf.map i.op s) = X.germToFunctionField V s :=
  X.presheaf.germ_res_apply i _ _ s

/-- On an integral scheme, a rational function lying in the local ring at every point of an open
set `V` is a regular function on `V`. -/
theorem exists_germToFunctionField_eq_of_forall_mem_range_stalk [IsIntegral X] (V : X.Opens)
    [Nonempty V] {z : X.functionField}
    (h : ∀ x ∈ V, z ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ r : Γ(X, V), X.germToFunctionField V r = z := by
  classical
  choose c hc using fun x : V => h x.1 x.2
  choose W hxW r hr using fun x : V => X.presheaf.germ_exist (x := x.1) (c x)
  let W' : V → X.Opens := fun x => W x ⊓ V
  have hxW' (x : V) : x.1 ∈ W' x := ⟨hxW x, x.2⟩
  have hne (x : V) : Nonempty (W' x) := ⟨⟨x.1, hxW' x⟩⟩
  let r' : (x : V) → Γ(X, W' x) := fun x => X.presheaf.map (homOfLE inf_le_left).op (r x)
  have hs (x : V) : X.germToFunctionField (W' x) (r' x) = z := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (hxW' x), ← hc x, ← hr x]
    congr 1
    exact X.presheaf.germ_res_apply _ _ _ _
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W' r' := by
    intro x y
    have : Nonempty (W' x ⊓ W' y : X.Opens) :=
      ⟨⟨genericPoint X, genericPoint_mem_opens _, genericPoint_mem_opens _⟩⟩
    apply X.germToFunctionField_injective (W' x ⊓ W' y : X.Opens)
    exact (germToFunctionField_map _ (r' x)).trans
      ((hs x).trans ((hs y).symm.trans (germToFunctionField_map _ (r' y)).symm))
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W' V (fun x => homOfLE inf_le_right)
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW' ⟨x, hx⟩⟩) r' hcompat
  refine ⟨t, ?_⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  have := hne x
  have hres : X.presheaf.map (homOfLE inf_le_right : W' x ⟶ V).op t = r' x := ht x
  rw [← hs x, ← hres]
  exact (germToFunctionField_map (homOfLE inf_le_right : W' x ⟶ V) t).symm

/-- **Regularity on a normal scheme is tested at prime divisors.** On a normal integral locally
Noetherian scheme `X`, a non-zero rational function `φ` is regular on a non-empty open `V` if and
only if `ord_P(φ) ≥ 0` for every prime divisor `P` meeting `V`. -/
@[mmp "lem_mmp_foundation_laz_rational_function_regular_criterion"]
theorem exists_germToFunctionField_eq_iff_forall_zero_le_ord [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (V : X.Opens) [Nonempty V] {φ : X.functionField}
    (hφ : φ ≠ 0) :
    (∃ r : Γ(X, V), X.germToFunctionField V r = φ) ↔
      ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ V).Nonempty →
        0 ≤ Scheme.ord φ P.genericPoint := by
  constructor
  · rintro ⟨r, rfl⟩ P hP
    rw [← Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P) hφ]
    exact ⟨_, Scheme.algebraMap_germ_eq_germToFunctionField (X := X)
      (genericPoint_mem_of_support_inter_nonempty P hP) r⟩
  · intro h
    refine exists_germToFunctionField_eq_of_forall_mem_range_stalk V fun x hx => ?_
    refine Scheme.mem_range_algebraMap_stalk_of_forall_zero_le_ord x hφ fun y hy hyx => ?_
    simpa using h (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy)
      (support_inter_nonempty_of_genericPoint_mem _ (by simpa using hyx.mem_open V.isOpen hx))

/-! ### Proper birational morphisms in codimension one -/

section CodimOne

variable {X' : Scheme.{u}}

/-- The inclusions of the local rings into the function field are compatible with the
identification of the local rings at two equal points. -/
theorem algebraMap_stalkCongr [IsIntegral X] {y z : X} (h : y = z) (b : X.presheaf.stalk y) :
    algebraMap (X.presheaf.stalk z) X.functionField
        ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom b) =
      algebraMap (X.presheaf.stalk y) X.functionField b := by
  subst h
  simp

/-- A morphism of integral schemes inducing an isomorphism of function fields induces an
isomorphism of local rings at `x'` as soon as the local ring at `x'` maps into the one at `μ x'`
compatibly with the inclusions into the function fields. -/
theorem isIso_stalkMap_of_functionFieldMap_comp_eq [IsIntegral X] [IsIntegral X'] (μ : X' ⟶ X)
    [IsDominant μ] (hμ : Function.Bijective (functionFieldMap μ)) {x' : X'} {y : X}
    (hx' : μ x' = y) (φ : X'.presheaf.stalk x' ⟶ X.presheaf.stalk y)
    (hφ : ∀ a, functionFieldMap μ (algebraMap (X.presheaf.stalk y) X.functionField (φ.hom a)) =
      algebraMap (X'.presheaf.stalk x') X'.functionField a) :
    IsIso (μ.stalkMap x') := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => ?_, fun a' => ?_⟩
  · have h1 := MMP.Mori.functionFieldMap_algebraMap_stalk μ x' a
    have h2 := MMP.Mori.functionFieldMap_algebraMap_stalk μ x' b
    change (μ.stalkMap x').hom a = (μ.stalkMap x').hom b at hab
    rw [hab, ← h2] at h1
    exact IsFractionRing.injective (X.presheaf.stalk (μ x')) X.functionField (hμ.1 h1)
  · refine ⟨(X.presheaf.stalkCongr (Inseparable.of_eq hx'.symm)).hom.hom (φ.hom a'),
      IsFractionRing.injective (X'.presheaf.stalk x') X'.functionField ?_⟩
    change algebraMap _ _ ((μ.stalkMap x').hom _) = _
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, algebraMap_stalkCongr hx'.symm]
    exact hφ a'

/-- **The valuative criterion at a point with valuation-ring stalk.** Let `μ : X' ⟶ X` be a
universally closed dominant morphism of integral schemes inducing an isomorphism of function
fields. If the local ring of `X` at `y` is a valuation ring, there is a point `x'` over `y` at
which `μ` induces an isomorphism of local rings. -/
theorem exists_isIso_stalkMap_of_valuationRing [IsIntegral X] [IsIntegral X'] (μ : X' ⟶ X)
    [IsDominant μ] [UniversallyClosed μ] (hμ : Function.Bijective (functionFieldMap μ)) (y : X)
    [ValuationRing (X.presheaf.stalk y)] :
    ∃ x' : X', μ x' = y ∧ IsIso (μ.stalkMap x') := by
  letI alg : Algebra (X.presheaf.stalk y) X'.functionField :=
    ((functionFieldMap μ).comp (algebraMap (X.presheaf.stalk y) X.functionField)).toAlgebra
  let e : X.functionField ≃ₐ[X.presheaf.stalk y] X'.functionField :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (functionFieldMap μ) hμ) (fun _ => rfl)
  haveI : IsFractionRing (X.presheaf.stalk y) X'.functionField :=
    IsLocalization.isLocalization_of_algEquiv _ e
  have hex : ValuativeCriterion.Existence μ :=
    (UniversallyClosed.eq_valuativeCriterion.le _ _ μ inferInstance).1
  have hy : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
  have halg : CommRingCat.ofHom (algebraMap (X.presheaf.stalk y) X'.functionField) =
      X.presheaf.stalkSpecializes hy ≫ CommRingCat.ofHom (functionFieldMap μ) := by
    ext a
    rfl
  have hsq : X'.fromSpecStalk (genericPoint X') ≫ μ =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk y) X'.functionField)) ≫
        X.fromSpecStalk y := by
    rw [← functionFieldMap_fromSpecStalk, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hy,
      halg]
    exact (Spec.map_comp_assoc (X.presheaf.stalkSpecializes hy)
      (CommRingCat.ofHom (functionFieldMap μ)) _).symm
  let S : ValuativeCommSq μ :=
    { R := X.presheaf.stalk y
      domain := inferInstance
      K := X'.functionField
      i₁ := X'.fromSpecStalk (genericPoint X')
      i₂ := X.fromSpecStalk y
      commSq := ⟨hsq⟩ }
  obtain ⟨l', hl₁', hl₂'⟩ := (hex S).exists_lift
  let l : Spec (X.presheaf.stalk y) ⟶ X' := l'
  have hl₁ : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk y) X'.functionField)) ≫ l =
      X'.fromSpecStalk (genericPoint X') := hl₁'
  have hl₂ : l ≫ μ = X.fromSpecStalk y := hl₂'
  clear_value l
  have hx' : μ (l (IsLocalRing.closedPoint (X.presheaf.stalk y))) = y :=
    (congrArg (fun f : Spec _ ⟶ X => f (IsLocalRing.closedPoint _)) hl₂).trans
      Scheme.fromSpecStalk_closedPoint
  refine ⟨_, hx', ?_⟩
  set x' := l (IsLocalRing.closedPoint (X.presheaf.stalk y))
  let φ := Scheme.stalkClosedPointTo l
  have hφ : ∀ a, algebraMap (X.presheaf.stalk y) X'.functionField (φ.hom a) =
      algebraMap (X'.presheaf.stalk x') X'.functionField a := by
    intro a
    have hl : Spec.map φ ≫ X'.fromSpecStalk x' = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
    have key : Spec.map (φ ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk y)
        X'.functionField)) ≫ X'.fromSpecStalk x' =
        Spec.map (X'.presheaf.stalkSpecializes (genericPoint_specializes x')) ≫
          X'.fromSpecStalk x' := by
      rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact (Spec.map_comp_assoc φ _ _).trans (by rw [hl]; exact hl₁)
    exact congrArg (fun g => g.hom a) (Spec.map_injective ((cancel_mono _).1 key))
  exact isIso_stalkMap_of_functionFieldMap_comp_eq μ hμ hx' φ hφ

/-- **A proper birational morphism to a normal scheme is an isomorphism over the points of
codimension one.** Let `μ : X' ⟶ X` be a universally closed, locally of finite type, dominant
morphism of integral schemes inducing an isomorphism of function fields, with `X` normal and
locally Noetherian. Over every point `y` of codimension one of `X` there is a point `x'` of
codimension one of `X'` outside the exceptional locus of `μ`, such that a rational function on
`X` lies in `𝒪_{X,y}` as soon as its pull-back lies in `𝒪_{X',x'}`. -/
theorem exists_preimage_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] (μ : X' ⟶ X) [IsDominant μ] [UniversallyClosed μ] [LocallyOfFiniteType μ]
    (hμ : Function.Bijective (functionFieldMap μ)) {y : X} (hy : coheight y = 1) :
    ∃ x' : X', μ x' = y ∧ coheight x' = 1 ∧ x' ∉ exceptionalLocus μ ∧
      ∀ g : X.functionField,
        functionFieldMap μ g ∈ (algebraMap (X'.presheaf.stalk x') X'.functionField).range →
          g ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range := by
  haveI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hy
  obtain ⟨x', hx', hiso⟩ := exists_isIso_stalkMap_of_valuationRing μ hμ y
  refine ⟨x', hx', ?_, ?_, ?_⟩
  · have h1 : ringKrullDim (X'.presheaf.stalk x') = ringKrullDim (X.presheaf.stalk (μ x')) :=
      (ringKrullDim_eq_of_ringEquiv (asIso (μ.stalkMap x')).commRingCatIsoToRingEquiv).symm
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx', hy] at h1
    exact_mod_cast h1
  · intro hx'E
    have hfin : (irreducibleComponents X).Finite := by
      rw [irreducibleComponents_eq_singleton]
      exact Set.finite_singleton _
    obtain ⟨U, hxU, hU⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap μ x' hfin hiso
    exact (mem_exceptionalLocus_iff.mp hx'E) U hxU hU
  · rintro g ⟨a', ha'⟩
    obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso (μ.stalkMap x')).2 a'
    refine ⟨(X.presheaf.stalkCongr (Inseparable.of_eq hx')).hom.hom b, ?_⟩
    rw [algebraMap_stalkCongr hx']
    apply hμ.1
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, ← ha']
    exact congrArg _ hb

end CodimOne

end MMP.Intersection
