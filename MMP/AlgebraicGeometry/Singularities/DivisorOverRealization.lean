module
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.RingTheory.RegularLocalRing.QuotientRegularIff

/-!
# Divisors over a variety are realized over any proper birational model

Let `g : X₁ ⟶ X` be a proper birational morphism of varieties over a field `k` and `(Y, f, E)` a
divisor over `X`. Then the valuation `ord_E` of `k(X)` is realized by a divisor `(Z, h, F)` over
`X₁`: under the isomorphism `k(X) ≅ k(X₁)` induced by `g`, `ord_F = ord_E`. Moreover the composite
`(Z, h ≫ g, F)` is a divisor over `X` with the same valuation `ord_E`.

## Main results

* `MMP.Flips.ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq`

## References

* [Kollár et al., *Flips and abundance for algebraic threefolds*][FA], §1.6;
  [Kollár–Mori, *Birational geometry of algebraic varieties*][KM98], Lemma 2.22.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

open scoped WithZero

namespace MMP.Flips.ProperDivisorOver

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by
      rw [Scheme.topIso_hom]
      exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have hle₁ : U ≤ U₁ := inf_le_left
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE hle₁ ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by
      rw [this]
      infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U (U.2.dense hne)

/-- **A divisor over `X` is realized over any proper birational model.** Let `g : X₁ ⟶ X` be a
proper birational morphism of varieties over `k` (`X₁` with structure morphism `g ≫ s_X`) and `D`
a divisor `(Y, f, E)` over `X`. Then there is a divisor `D₁ = (Z, h, F)` over `X₁` with
`ord_F = ord_E` under the identification `k(X) → k(X₁)` given by `g`, and `(Z, h ≫ g, F)` is a
divisor over `X` with valuation `ord_E`. -/
@[mmp "lem_fa1a_divisor_realized_over_model"]
public theorem exists_comap_functionFieldMap_valuation_eq {k : Type u} [Field k]
    {X X₁ : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : Mori.IsVariety k sX) (g : X₁ ⟶ X)
    (hX₁ : Mori.IsVariety k (g ≫ sX)) [IsProper g] (hg : IsBirationalMorphism g)
    (D : ProperDivisorOver k sX) :
    haveI : IsIntegral X := hX.toIsIntegral
    haveI : IsIntegral X₁ := hX₁.toIsIntegral
    haveI : IsDominant g := hg.isDominant
    ∃ D₁ : ProperDivisorOver k (g ≫ sX),
      D₁.valuation.comap (functionFieldMap g) = D.valuation ∧
      ∃ (hn : IsNormalVariety k ((D₁.f ≫ g) ≫ sX)) (hb : IsBirationalMorphism (D₁.f ≫ g))
        (hp : IsProper (D₁.f ≫ g)),
        ProperDivisorOver.valuation
          (⟨⟨D₁.Y, D₁.f ≫ g, hn, hb, D₁.E⟩, hp⟩ : ProperDivisorOver k sX) = D.valuation := by
  haveI : IsIntegral X := hX.toIsIntegral
  haveI : IsIntegral X₁ := hX₁.toIsIntegral
  haveI : IsDominant g := hg.isDominant
  haveI := D.isIntegral
  haveI := D.isDominant
  set v := D.valuation
  -- the field isomorphism `g^* : k(X) ≃ k(X₁)`
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  let e : X.functionField ≃ₐ[k] X₁.functionField := AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom k X.functionField X₁.functionField) hg.functionFieldMap_bijective
  let v₁ : Valuation X₁.functionField ℤᵐ⁰ :=
    v.comap (e.symm : X₁.functionField →+* X.functionField)
  have hv₁ : ∀ t, v₁ (functionFieldMap g t) = v t := fun t ↦ by
    change v (e.symm (e t)) = v t
    rw [e.symm_apply_apply]
  -- `𝒪_{X,x}` is dominated by `v`, for `x = f(η_E)`
  set x := D.f D.E.genericPoint
  have hle := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver x rfl
  -- the valuative criterion of properness
  let R := v₁.valuationSubring
  have hequiv := v₁.isEquiv_valuation_valuationSubring
  have hkR : ∀ c : k, algebraMap k X₁.functionField c ∈ R := fun c ↦ by
    letI := stalkAlgebra sX x
    have := isScalarTower_stalk_functionField sX x
    rw [Valuation.mem_valuationSubring_iff, IsScalarTower.algebraMap_apply k X.functionField,
      IsScalarTower.algebraMap_apply k (X.presheaf.stalk x) X.functionField]
    change v₁ (functionFieldMap g _) ≤ 1
    rw [hv₁]
    exact hle _
  obtain ⟨x₁, -, hle₁, hlt₁⟩ := exists_map_eq_and_dominates_of_isProper hX g hX₁ R hkR x
    (fun a ↦ by
      rw [← hequiv.le_one_iff_le_one, hv₁]
      exact hle a)
    (fun a ha ↦ by
      rw [← hequiv.lt_one_iff_lt_one, hv₁]
      exact MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D.toDivisorOver x rfl a ha)
  -- `v₁` is a divisor of `k(X₁)`
  have hdiv : IsDivisorOfFunctionField k (g ≫ sX) v₁ := by
    let := functionFieldAlgebra (D.f ≫ sX)
    let := functionFieldMapAlgebra D.f
    have := isScalarTower_functionFieldMap sX D.f
    let eD : X.functionField ≃ₐ[k] D.Y.functionField := AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom k X.functionField D.Y.functionField)
      D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, e.symm.trans eD, ?_⟩
    ext t
    rfl
  haveI : AlgebraicGeometry.IsVariety k (g ≫ sX) := hX₁
  obtain ⟨D₁, -, hD₁, -⟩ := exists_properDivisorOver_isProjective_of_dominates (g ≫ sX) hdiv x₁
    (fun a ↦ hequiv.le_one_iff_le_one.2 (hle₁ a))
    (fun a ha ↦ hequiv.lt_one_iff_lt_one.2 (hlt₁ a ha))
  haveI := D₁.isIntegral
  haveI := D₁.isDominant
  have hcomp : D₁.valuation.comap (functionFieldMap g) = D.valuation := by
    ext t
    rw [Valuation.comap_apply, hD₁, hv₁]
  refine ⟨D₁, hcomp, ?_, isBirationalMorphism_comp D₁.isBirationalMorphism hg, ?_, ?_⟩
  · rw [Category.assoc]
    exact D₁.isNormalVariety
  · haveI := D₁.isProper
    infer_instance
  · refine Eq.trans ?_ hcomp
    ext t
    exact congrArg _ (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply
      D₁.f g t).symm

end MMP.Flips.ProperDivisorOver

end
