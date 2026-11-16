module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Extending maps from the function field, and proper maps of curves

* `MMP.NormalCompleteCurve.exists_hom_of_fromFunctionField`: for an integral `S`-scheme `X` all of
  whose local rings are valuation rings and a separated `Y` proper over the separated `S`, every
  `S`-morphism `Spec R(X) ⟶ Y` extends to an `S`-morphism `X ⟶ Y` (valuative criterion).
* `MMP.NormalCompleteCurve.isFinite_and_surjective`: a proper morphism from an irreducible
  Noetherian scheme of dimension at most one to an irreducible scheme with more than one point,
  sending generic point to generic point, is finite and surjective.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], I.6.8, II.6.8.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP.NormalCompleteCurve

/-- The map `Spec 𝒪_{X,y} ⟶ U` for a generization `y` of `x ∈ U` factors through
`Spec 𝒪_{X,x} ⟶ U`. -/
theorem SpecMap_stalkSpecializes_fromSpecStalkOfMem {X : Scheme.{u}} (U : X.Opens) {x y : X}
    (h : y ⤳ x) (hx : x ∈ U) (hy : y ∈ U) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem y hy := by
  rw [← cancel_mono U.ι]
  simp

/-- The restriction of a partial map to `Spec R(X)` factors through `Spec 𝒪_{X,x}` for every
point `x` of its domain. -/
theorem fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X.PartialMap Y)
    {x : X} (hx : x ∈ f.domain) :
    f.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫
        f.fromSpecStalkOfMem hx := by
  simp only [Scheme.PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc, SpecMap_stalkSpecializes_fromSpecStalkOfMem]

/-- A point of an irreducible scheme of dimension at most one other than the generic point is
closed. -/
theorem isClosed_singleton_of_ne_genericPoint {X : Scheme.{u}} [IrreducibleSpace X]
    (h : Order.krullDim X ≤ 1) {x : X} (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  by_contra hwx
  have hxw : x ⤳ w := specializes_iff_mem_closure.mpr hw
  have h1 : w < x := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxw)
    fun h' ↦ hwx (hxw.antisymm (Scheme.le_iff_specializes.mp h')).eq.symm
  have hηx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have h2 : x < genericPoint X := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hηx)
    fun h' ↦ hx (hηx.antisymm (Scheme.le_iff_specializes.mp h')).eq.symm
  rcases Order.krullDim_le_one_iff.mp h x with hmin | hmax
  · exact hmin.not_lt h1
  · exact hmax.not_lt h2

/-- In an irreducible Noetherian scheme of dimension at most one, every closed subset not
containing the generic point is finite. -/
theorem finite_of_isClosed_of_genericPoint_notMem {X : Scheme.{u}} [IrreducibleSpace X]
    [TopologicalSpace.NoetherianSpace X] (h : Order.krullDim X ≤ 1) {Z : Set X}
    (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨z, hz⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
  rw [← hz.def, (isClosed_singleton_of_ne_genericPoint h
    fun e ↦ hη ⟨t, ht, e ▸ hz.mem⟩).closure_eq]
  exact Set.finite_singleton z

set_option backward.isDefEq.respectTransparency false in
/-- A rational map from an integral scheme `X` to a scheme `Y` proper over the base `S`, given
by an `S`-morphism `Spec R(X) ⟶ Y`, is defined at every point of `X` whose local ring is a
valuation ring. -/
theorem mem_domain_ofFunctionField {X Y S : Scheme.{u}} [IsIntegral X] (sX : X ⟶ S)
    (sY : Y ⟶ S) [IsProper sY] (ψ : Spec X.functionField ⟶ Y)
    (hψ : ψ ≫ sY = X.fromSpecStalk _ ≫ sX) {x : X} [ValuationRing (X.presheaf.stalk x)] :
    x ∈ (Scheme.RationalMap.ofFunctionField sX sY ψ hψ).domain := by
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) =
      Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) := rfl
  let 𝒮 : ValuativeCommSq sY :=
    { R := X.presheaf.stalk x
      K := X.functionField
      i₁ := ψ
      i₂ := X.fromSpecStalk x ≫ sX
      commSq := ⟨by rw [hspec, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, hψ]⟩ }
  have hE : ValuativeCriterion.Existence sY := by
    have h : UniversallyClosed sY := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hE 𝒮).exists_lift
  let g := Scheme.PartialMap.ofFromSpecStalk sX sY l hl₂
  have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂
  refine Scheme.RationalMap.mem_domain.mpr ⟨g, hxg, ?_⟩
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_ofFunctionField, fromFunctionField_eq g hxg,
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk, ← hspec]
  exact hl₁

set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be an integral `S`-scheme all of whose local rings are valuation rings, and `Y` a
separated scheme proper over the separated scheme `S`. Then every `S`-morphism
`Spec R(X) ⟶ Y` extends to an `S`-morphism `X ⟶ Y`. -/
theorem exists_hom_of_fromFunctionField {X Y S : Scheme.{u}} [X.Over S] [Y.Over S] [IsIntegral X]
    [S.IsSeparated] [Y.IsSeparated] [IsProper (Y ↘ S)]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (ψ : Spec X.functionField ⟶ Y)
    [ψ.IsOver S] :
    ∃ g : X ⟶ Y, g.IsOver S ∧ X.fromSpecStalk (genericPoint X) ≫ g = ψ := by
  have hψ : ψ ≫ Y ↘ S = X.fromSpecStalk _ ≫ X ↘ S := by
    rw [comp_over ψ S]
    rfl
  let F := Scheme.RationalMap.equivFunctionFieldOver (S := S) ⟨ψ, inferInstance⟩
  let f : X ⤏ Y := F.1
  haveI : f.IsOver S := F.2
  have hf : f = Scheme.RationalMap.ofFunctionField (X ↘ S) (Y ↘ S) ψ hψ := rfl
  have htop : f.domain = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    haveI := hX x
    rw [hf]
    exact mem_domain_ofFunctionField (X ↘ S) (Y ↘ S) ψ hψ
  let p := f.toPartialMap
  have hpd : p.domain = f.domain := rfl
  have hp : p.hom ≫ Y ↘ S = p.domain.ι ≫ X ↘ S := comp_over p.hom S
  let g : X ⟶ Y := X.topIso.inv ≫ (X.isoOfEq (htop.symm.trans hpd.symm)).hom ≫ p.hom
  refine ⟨g, ⟨?_⟩, ?_⟩
  · simp only [g, Category.assoc, hp]
    rw [Scheme.isoOfEq_hom_ι_assoc, Scheme.toIso_inv_ι_assoc]
  · have hη : genericPoint X ∈ p.domain := by
      rw [hpd, htop]
      trivial
    have h1 : X.fromSpecStalk (genericPoint X) ≫ X.topIso.inv ≫
        (X.isoOfEq (htop.symm.trans hpd.symm)).hom =
          p.domain.fromSpecStalkOfMem (genericPoint X) hη := by
      rw [← cancel_mono p.domain.ι]
      simp only [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι, Category.comp_id]
    have h2 : p.fromFunctionField = ψ := by
      rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
        Scheme.RationalMap.toRationalMap_toPartialMap, hf,
        Scheme.RationalMap.fromFunctionField_ofFunctionField]
    rw [← h2]
    simp only [g, ← Category.assoc, h1]
    rfl

/-- A proper morphism from an irreducible Noetherian scheme of dimension at most one to an
irreducible scheme with more than one point, sending generic point to generic point, is finite
and surjective. -/
theorem isFinite_and_surjective {X Y : Scheme.{u}} [IrreducibleSpace X]
    [TopologicalSpace.NoetherianSpace X] (hX : Order.krullDim X ≤ 1) [IrreducibleSpace Y]
    [Nontrivial Y] (g : X ⟶ Y) [IsProper g] (hg : g (genericPoint X) = genericPoint Y) :
    IsFinite g ∧ Function.Surjective g := by
  have hcl : IsClosedMap g := g.isClosedMap
  have hξ : ¬IsClosed ({genericPoint Y} : Set Y) := fun h ↦ by
    have huniv : ({genericPoint Y} : Set Y) = Set.univ := by
      rw [← h.closure_eq, (genericPoint_spec Y).def]
    exact not_subsingleton Y (Set.subsingleton_univ_iff.mp (huniv ▸ Set.subsingleton_singleton))
  have hfib : ∀ y : Y, (g ⁻¹' {y}).Finite := by
    intro y
    by_cases hy : y = genericPoint Y
    · subst hy
      refine (Set.finite_singleton (genericPoint X)).subset fun x hx ↦ ?_
      by_contra hne
      have := hcl _ (isClosed_singleton_of_ne_genericPoint hX hne)
      rw [Set.image_singleton, show g x = genericPoint Y from hx] at this
      exact hξ this
    · refine (finite_of_isClosed_of_genericPoint_notMem hX
        (isClosed_closure.preimage g.continuous) fun hmem ↦ ?_).subset
        (Set.preimage_mono subset_closure)
      exact hy ((specializes_iff_mem_closure.mpr (hg ▸ hmem)).antisymm
        ((genericPoint_spec Y).specializes trivial)).eq
  have : LocallyQuasiFinite g := LocallyQuasiFinite.of_finite_preimage_singleton g hfib
  refine ⟨IsFinite.of_isProper_of_locallyQuasiFinite g, fun y ↦ ?_⟩
  exact closure_minimal (Set.singleton_subset_iff.mpr (hg ▸ Set.mem_range_self _))
    hcl.isClosed_range ((genericPoint_spec Y).def ▸ Set.mem_univ y)

end MMP.NormalCompleteCurve
