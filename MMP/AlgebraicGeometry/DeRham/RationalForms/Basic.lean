module

public import MMP.AlgebraicGeometry.DeRham.FormsSectionsAlgebra

/-!
# Rational differential forms of an integral scheme

Let `X` be an integral scheme over a field `k` with function field `K = k(X)`. A relative
differential `q`-form over an affine open `W ≠ ∅` is an element of `⋀^q Ω_{Γ(X, W)/k}`
(`MMP.DeRham.formsAlgEquiv`), and its pull-back along `Γ(X, W) → K` is a *rational* `q`-form, an
element of `⋀^q_K Ω_{K/k}`. These rational forms do not change under restriction to a smaller
affine open, they commute with the de Rham differential, and on an affine open where `Ω` is free
a form is determined by its rational form, since `Ω^q_{K/k}` is the localization of
`Ω^q_{Γ(X, W)/k}`. Rational forms are how the forms of `X` over different opens, and of a finite
cover of `X`, are compared in the proof that the fractional logarithmic complex degenerates at
`E₁`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.ratForm`: the rational form of a section of
  `Ω^q_{X/k}` over a non-empty affine open.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.mapExteriorPower_comp`: the pull-back of forms along
  a tower `A → B → C` is the composite of the pull-backs.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratForm_restrict`: rational forms are unchanged by
  restriction.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratForm_d`: rational forms commute with `d`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratForm_injective`: on an affine open where
  `Ω_{X/k}` is free, a form is determined by its rational form.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section Tower

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A B] [Algebra B C] [Algebra A C]
  [IsScalarTower R A B] [IsScalarTower R B C] [IsScalarTower R A C] [IsScalarTower A B C]

/-- The pull-back of `1`-forms along a tower `A → B → C` is the composite of the pull-backs. -/
theorem map_map_eq (ω : Ω[A⁄R]) :
    KaehlerDifferential.map R R B C (KaehlerDifferential.map R R A B ω) =
      KaehlerDifferential.map R R A C ω := by
  have h : ((KaehlerDifferential.map R R B C).restrictScalars A).comp
      (KaehlerDifferential.map R R A B) = KaehlerDifferential.map R R A C := by
    ext a
    change KaehlerDifferential.map R R B C (KaehlerDifferential.map R R A B (D R A a)) =
      KaehlerDifferential.map R R A C (D R A a)
    rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D, KaehlerDifferential.map_D,
      ← IsScalarTower.algebraMap_apply]
  exact congrArg (fun φ => φ ω) h

/-- **The pull-back of forms is functorial**: along a tower `A → B → C` of `R`-algebras, the
pull-back `Ω^q_{A/R} → Ω^q_{C/R}` is the composite of the pull-backs through `B`. -/
theorem mapExteriorPower_comp (q : ℕ) (ω : ⋀[A]^q (Ω[A⁄R])) :
    mapExteriorPower R B C q (mapExteriorPower R A B q ω) = mapExteriorPower R A C q ω := by
  have h : ((mapExteriorPower R B C q).restrictScalars A).comp (mapExteriorPower R A B q) =
      mapExteriorPower R A C q := by
    refine exteriorPower.linearMap_ext ?_
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, mapExteriorPower_ιMulti]
    congr 2
    funext i
    exact map_map_eq R A B C (v i)
  exact congrArg (fun φ => φ ω) h

end Tower

section RationalForms

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k))

/-- **The rational form** of a section of `Ω^q_{X/k}` over a non-empty affine open `W`: its
pull-back along `Γ(X, W) → k(X)`, an element of `⋀^q_{k(X)} Ω_{k(X)/k}`. -/
noncomputable def ratForm (q : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)] :
    letI := MMP.Mori.functionFieldAlgebra sX
    Γ(sX.relativeDifferentialForms (q : ℤ), W) →+ ⋀[X.functionField]^q Ω[X.functionField⁄k] :=
  letI := MMP.Mori.sectionAlgebra sX W
  letI := MMP.Mori.functionFieldAlgebra sX
  haveI := MMP.Mori.isScalarTower_section_functionField sX W
  (mapExteriorPower k Γ(X, W) X.functionField q).toAddMonoidHom.comp
    (MMP.DeRham.formsAlgEquiv sX q W).toLinearMap.toAddMonoidHom

/-- The rational form of `ω` is the pull-back along `Γ(X, W) → k(X)` of its image under
`MMP.DeRham.formsAlgEquiv`. -/
theorem ratForm_apply (q : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (ω : Γ(sX.relativeDifferentialForms (q : ℤ), W)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.functionFieldAlgebra sX
    haveI := MMP.Mori.isScalarTower_section_functionField sX W
    ratForm sX q W ω = mapExteriorPower k Γ(X, W) X.functionField q
      (MMP.DeRham.formsAlgEquiv sX q W ω) := rfl

/-- The germ maps to the function field are compatible with restriction. -/
theorem isScalarTower_section_res_functionField {W W' : X.Opens} (h : W' ≤ W) [Nonempty W]
    [Nonempty W'] :
    letI : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    IsScalarTower Γ(X, W) Γ(X, W') X.functionField := by
  let : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  change (X.germToFunctionField W).hom =
    ((X.presheaf.map (homOfLE h).op) ≫ X.germToFunctionField W').hom
  rw [Scheme.germToFunctionField, Scheme.germToFunctionField, TopCat.Presheaf.germ_res]

/-- **Rational forms are unchanged by restriction** to a smaller non-empty affine open. -/
theorem ratForm_restrict (q : ℕ) {W W' : X.affineOpens} (h : (W' : X.Opens) ≤ W)
    [Nonempty (W : X.Opens)] [Nonempty (W' : X.Opens)]
    (ω : Γ(sX.relativeDifferentialForms (q : ℤ), W)) :
    ratForm sX q W' ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op ω) =
      ratForm sX q W ω := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX W'
  let := MMP.Mori.functionFieldAlgebra sX
  let : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res sX h
  have := MMP.Mori.isScalarTower_section_functionField sX W
  have := MMP.Mori.isScalarTower_section_functionField sX W'
  have := isScalarTower_section_res_functionField h
  rw [ratForm_apply, ratForm_apply, MMP.DeRham.formsAlgEquiv_restrict]
  exact mapExteriorPower_comp k Γ(X, W) Γ(X, W') X.functionField q _

/-- **Rational forms commute with the de Rham differential.** -/
theorem ratForm_d (q : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (ω : Γ(sX.relativeDifferentialForms (q : ℤ), W)) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratForm sX (q + 1) W (((sX.deRhamComplex).d q (q + 1)).val.app (op (W : X.Opens)) ω) =
      deRhamDifferential (A := k) q (ratForm sX q W ω) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.functionFieldAlgebra sX
  have := MMP.Mori.isScalarTower_section_functionField sX W
  exact (congrArg (mapExteriorPower k Γ(X, W) X.functionField (q + 1))
    (MMP.DeRham.formsAlgEquiv_d sX q W ω)).trans
    (KaehlerDifferential.mapExteriorPower_deRhamDifferential k Γ(X, W) X.functionField q _)

/-- **Forms are determined by their rational forms** on an affine open where `Ω_{X/k}` is
free. -/
theorem ratForm_injective (q : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (hfree : letI := MMP.Mori.sectionAlgebra sX W; Module.Free Γ(X, W) Ω[Γ(X, W)⁄k]) :
    Function.Injective (ratForm sX q W) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.functionFieldAlgebra sX
  have := MMP.Mori.isScalarTower_section_functionField sX W
  have := functionField_isFractionRing_of_isAffineOpen X (W : X.Opens) W.2
  intro ω ω' hω
  rw [ratForm_apply, ratForm_apply] at hω
  refine (MMP.DeRham.formsAlgEquiv sX q W).injective ?_
  -- `Ω^q_{K/k}` is the localization of `Ω^q_{Γ(X, W)/k}`
  have : Algebra.FormallyEtale Γ(X, W) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(X, W))
  have hbc : IsBaseChange X.functionField (mapExteriorPower k Γ(X, W) X.functionField q) :=
    DeRhamBaseChange.isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, W) X.functionField) _
      (fun v => mapExteriorPower_ιMulti k Γ(X, W) X.functionField q v)
  have hloc := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors Γ(X, W)) X.functionField
    (mapExteriorPower k Γ(X, W) X.functionField q)).2 hbc
  have := hfree
  rw [← sub_eq_zero, ← map_sub] at hω
  rw [← sub_eq_zero]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors Γ(X, W))
    (mapExteriorPower k Γ(X, W) X.functionField q)).1 hω
  exact (smul_eq_zero.1 hc).resolve_left (nonZeroDivisors.ne_zero c.2)

end RationalForms

end MMP.FourfoldProofs.FractionalLogComplexProof
