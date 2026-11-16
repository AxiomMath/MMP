module

public import MMP.AlgebraicGeometry.DeRham.RationalForms.Basic

/-!
# Rational forms of the total ring of differential forms

Let `X` be an integral scheme over a field `k` with function field `K`, and `W ≠ ∅` an affine
open. The sections over `W` of the total ring `Ω^•_{X/k}` (the direct sum of the sections of the
`Ω^q_{X/k}`) map additively to the exterior algebra `⋀ Ω_{K/k}`, each homogeneous form going to
its rational form (`MMP.FourfoldProofs.FractionalLogComplexProof.ratForm`), negative degrees to `0`.
This map is multiplicative on homogeneous forms of non-negative degrees, sends a function to its
germ and the exact form `d a` to `d a`. It is the dictionary between identities among forms on
the schemes involved in the proof that the fractional logarithmic complex degenerates at `E₁` and
identities in the exterior algebra of the function field.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal`: the map to `⋀ Ω_{K/k}`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.mapExteriorPower_wedgeMul`: the pull-back of forms is
  multiplicative.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal_incl`: on a homogeneous form of degree
  `q ≥ 0`, the rational form.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal_incl_mul_incl`: `ratTotal` is multiplicative
  on homogeneous forms of non-negative degrees.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal_structureMap_mul_incl`: multiplication by a
  function becomes multiplication by its germ.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal_incl_exactOne`: `d a` goes to `d a`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal_totalRestrict`: `ratTotal` is unchanged by
  restriction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

section Multiplicative

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- **The pull-back of forms is multiplicative**: `f^*(α ∧ β) = f^*α ∧ f^*β`. -/
theorem mapExteriorPower_wedgeMul {p q : ℕ} (α : ⋀[A]^p (Ω[A⁄R])) (β : ⋀[A]^q (Ω[A⁄R])) :
    mapExteriorPower R A B (p + q) (exteriorPower.wedgeMul p q α β) =
      exteriorPower.wedgeMul p q (mapExteriorPower R A B p α) (mapExteriorPower R A B q β) := by
  have key : ∀ (u : Fin p → Ω[A⁄R]) (v : Fin q → Ω[A⁄R]),
      mapExteriorPower R A B (p + q)
          (exteriorPower.wedgeMul p q (exteriorPower.ιMulti A p u) (exteriorPower.ιMulti A q v)) =
        exteriorPower.wedgeMul p q (mapExteriorPower R A B p (exteriorPower.ιMulti A p u))
          (mapExteriorPower R A B q (exteriorPower.ιMulti A q v)) := by
    intro u v
    simp only [exteriorPower.wedgeMul_ιMulti, mapExteriorPower_ιMulti]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  have hα : α ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A p)) := by
    simp [exteriorPower.ιMulti_span]
  have hβ : β ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A q)) := by
    simp [exteriorPower.ιMulti_span]
  induction hα using Submodule.span_induction generalizing β with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    induction hβ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact key u v
    | zero => simp
    | add y y' _ _ hy hy' => simp only [map_add, hy, hy']
    | smul a y _ hy => simp only [map_smul, LinearMap.map_smul_of_tower, hy]
  | zero => simp
  | add x x' _ _ hx hx' => simp only [map_add, LinearMap.add_apply, hx β hβ, hx' β hβ]
  | smul a x _ hx =>
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smul_of_tower, hx β hβ]

end Multiplicative

section Total

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k))

omit [IsIntegral X] in
/-- The exact form `d a` of the de Rham algebras is the generator applied to `d a`. -/
theorem exactOne_eq_exteriorGenerator (W : X.Opens) (a : Γ(X, W)) :
    _root_.AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX) (op W) a =
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
        (op W) ((Scheme.Hom.universalRelativeDerivation sX).d (X := op W) a) := rfl

omit [IsIntegral X] in
/-- The algebraic form of an exact `1`-form `d a` is `d a`. -/
theorem formsAlgEquiv_exactOne (W : X.affineOpens) (a : Γ(X, W)) :
    letI := MMP.Mori.sectionAlgebra sX W
    MMP.DeRham.formsAlgEquiv sX 1 W
        ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
          (op (W : X.Opens))
          ((Scheme.Hom.universalRelativeDerivation sX).d (X := op (W : X.Opens)) a)) =
      exteriorPower.ιMulti Γ(X, W) 1 (fun _ => D k Γ(X, W) a) := by
  let := MMP.Mori.sectionAlgebra sX W
  have h := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_exactOne sX W.2
    (isAffineOpen_top _) (by simp) a
  rw [exactOne_eq_exteriorGenerator] at h
  refine (MMP.DeRham.formsAlgEquiv_apply sX 1 W _).trans ?_
  refine (congrArg (exteriorPower.map 1 (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap) h).trans ?_
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact MMP.DeRham.kaehlerBaseEquiv_d _ _ _ a

/-- The rational form of an exact `1`-form `d a` is `d a`. -/
theorem ratForm_exactOne (W : X.affineOpens) [Nonempty (W : X.Opens)] (a : Γ(X, W)) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratForm sX 1 W ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
        (op (W : X.Opens))
          ((Scheme.Hom.universalRelativeDerivation sX).d (X := op (W : X.Opens)) a)) =
      exteriorPower.ιMulti X.functionField 1
          (fun _ => D k X.functionField (X.germToFunctionField W a)) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.functionFieldAlgebra sX
  have := MMP.Mori.isScalarTower_section_functionField sX W
  refine (congrArg (mapExteriorPower k Γ(X, W) X.functionField 1)
    (formsAlgEquiv_exactOne sX W a)).trans ?_
  rw [mapExteriorPower_ιMulti]
  congr 1
  funext i
  rw [KaehlerDifferential.map_D]
  rfl

/-- The pieces of the map to the exterior algebra of rational forms: the rational form in
non-negative degrees, `0` in negative degrees. -/
noncomputable def ratPiece (W : X.affineOpens) [Nonempty (W : X.Opens)] : (i : ℤ) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece i).val.obj (op (W : X.Opens)) →+
      (letI := MMP.Mori.functionFieldAlgebra sX
       ExteriorAlgebra X.functionField Ω[X.functionField⁄k])
  | (q : ℕ) =>
    letI := MMP.Mori.functionFieldAlgebra sX
    (⋀[X.functionField]^q (Ω[X.functionField⁄k])).subtype.toAddMonoidHom.comp (ratForm sX q W)
  | Int.negSucc _ => 0

/-- **The rational forms of the total ring of forms** over a non-empty affine open. -/
noncomputable def ratTotal (W : X.affineOpens) [Nonempty (W : X.Opens)] :
    (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
        (op (W : X.Opens)) →+
      (letI := MMP.Mori.functionFieldAlgebra sX
       ExteriorAlgebra X.functionField Ω[X.functionField⁄k]) :=
  DirectSum.toAddMonoid (ratPiece sX W)

/-- On a homogeneous form of degree `q ≥ 0`, `ratTotal` is the rational form. -/
theorem ratTotal_incl (W : X.affineOpens) [Nonempty (W : X.Opens)] (q : ℕ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.obj
      (op (W : X.Opens))) :
    ratTotal sX W ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl
      (q : ℤ) x) = (ratForm sX q W x : _) :=
  DirectSum.toAddMonoid_of _ _ _

/-- **`ratTotal` is multiplicative** on homogeneous forms of non-negative degrees. -/
theorem ratTotal_incl_mul_incl (W : X.affineOpens) [Nonempty (W : X.Opens)] (p q : ℕ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (p : ℤ)).val.obj
      (op (W : X.Opens)))
    (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.obj
      (op (W : X.Opens))) :
    ratTotal sX W ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl
        (p : ℤ) x *
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl (q : ℤ) y) =
      ratTotal sX W ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl
        (p : ℤ) x) *
      ratTotal sX W ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl
        (q : ℤ) y) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.functionFieldAlgebra sX
  have := MMP.Mori.isScalarTower_section_functionField sX W
  let m : Γ(sX.relativeDifferentialForms ((p + q : ℕ) : ℤ), W) :=
    ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.mul (p : ℤ) q).app
      (op (W : X.Opens)) x y
  have h2 : MMP.DeRham.formsAlgEquiv sX (p + q) W m =
      exteriorPower.wedgeMul p q (MMP.DeRham.formsAlgEquiv sX p W x)
        (MMP.DeRham.formsAlgEquiv sX q W y) := by
    refine Eq.trans ?_ (MMP.DeRham.formsAlgEquiv_mul sX p q W x y)
    congr 1
  have h1 : ratTotal sX W
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl (p : ℤ) x *
        (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl (q : ℤ) y) =
      (ratForm sX (p + q) W m : _) := by
    rw [Stacks.GradedAlgebra.incl_mul_incl]
    exact ratTotal_incl sX W (p + q) m
  rw [h1, ratForm_apply, h2, mapExteriorPower_wedgeMul, exteriorPower.wedgeMul_apply_coe,
    ratTotal_incl, ratTotal_incl]
  rfl

omit [IsIntegral X] in
/-- The two spellings of the action of the functions on forms agree. -/
theorem structureRingSheaf_smul_eq (W : X.Opens) (q : ℕ) (a : Γ(X, W))
    (x : Γ(sX.relativeDifferentialForms (q : ℤ), W)) :
    @HSMul.hSMul ((Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj (op W))
      (((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.obj (op W)) _ _
      (show (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj (op W) from a) x =
      a • x := rfl

/-- Rational forms are linear over the functions, acting through their germs. -/
theorem ratForm_smul (W : X.affineOpens) [Nonempty (W : X.Opens)] (q : ℕ) (a : Γ(X, W))
    (ω : Γ(sX.relativeDifferentialForms (q : ℤ), W)) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratForm sX q W (a • ω) = X.germToFunctionField W a • ratForm sX q W ω := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.functionFieldAlgebra sX
  have := MMP.Mori.isScalarTower_section_functionField sX W
  rw [ratForm_apply, ratForm_apply, map_smul, map_smul]
  exact algebra_compatible_smul X.functionField a _

/-- `ratTotal` turns multiplication by a function into multiplication by its germ. -/
theorem ratTotal_structureMap_mul_incl (W : X.affineOpens) [Nonempty (W : X.Opens)] (q : ℕ)
    (a : Γ(X, W))
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.obj
      (op (W : X.Opens))) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratTotal sX W
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
        (op (W : X.Opens)) a *
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl (q : ℤ) x) =
      algebraMap X.functionField (ExteriorAlgebra X.functionField Ω[X.functionField⁄k])
          (X.germToFunctionField W a) *
        ratTotal sX W ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl
          (q : ℤ) x) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.functionFieldAlgebra sX
  have := MMP.Mori.isScalarTower_section_functionField sX W
  let a' : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj (op (W : X.Opens)) := a
  have e : (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
        (op (W : X.Opens)) a *
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl (q : ℤ) x =
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl (q : ℤ)
        (a' • x) := by
    change a' • (1 : (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
      (op (W : X.Opens))) * _ = _
    rw [Stacks.GradedAlgebra.smul_mul_eq, one_mul, Stacks.GradedAlgebra.incl_smul]
  rw [e, ratTotal_incl, ratTotal_incl, structureRingSheaf_smul_eq sX W q a x]
  refine (congrArg Subtype.val (ratForm_smul sX W q a x)).trans ?_
  rw [Submodule.coe_smul_of_tower, Algebra.smul_def]

/-- `ratTotal` sends the exact `1`-form `d a` to `d a`. -/
theorem ratTotal_incl_exactOne (W : X.affineOpens) [Nonempty (W : X.Opens)] (a : Γ(X, W)) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratTotal sX W ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl 1
      ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
        (op (W : X.Opens))
          ((Scheme.Hom.universalRelativeDerivation sX).d (X := op (W : X.Opens)) a))) =
      ExteriorAlgebra.ι X.functionField (D k X.functionField (X.germToFunctionField W a)) := by
  let := MMP.Mori.functionFieldAlgebra sX
  refine (ratTotal_incl sX W 1 _).trans ?_
  rw [ratForm_exactOne, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp

omit [IsIntegral X] in
/-- The two spellings of the restriction of forms agree. -/
theorem piece_map_eq_presheaf_map {W W' : X.Opens} (h : W' ≤ W) (q : ℕ)
    (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.obj (op W)) :
    (((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.map (homOfLE h).op y :
      Γ(sX.relativeDifferentialForms (q : ℤ), W')) =
      (sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op y := rfl

/-- Rational forms are unchanged by restriction along the pieces of the algebra of forms. -/
theorem ratForm_piece_map {W W' : X.affineOpens} (h : (W' : X.Opens) ≤ W)
    [Nonempty (W : X.Opens)] [Nonempty (W' : X.Opens)] (q : ℕ)
    (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.obj
      (op (W : X.Opens))) :
    ratForm sX q W'
      (((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.map (homOfLE h).op y) =
      ratForm sX q W y := by
  rw [piece_map_eq_presheaf_map sX h q y]
  exact ratForm_restrict sX q h y

/-- `ratTotal` is unchanged by restriction, on a homogeneous form of degree `q ≥ 0`. -/
theorem ratTotal_totalRestrict_incl {W W' : X.affineOpens} (h : (W' : X.Opens) ≤ W)
    [Nonempty (W : X.Opens)] [Nonempty (W' : X.Opens)] (q : ℕ)
    (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.obj
      (op (W : X.Opens))) :
    ratTotal sX W'
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
      (homOfLE h).op
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl (q : ℤ) y)) =
      ratTotal sX W
        ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl
          (q : ℤ) y) := by
  rw [Stacks.GradedAlgebra.totalRestrict_incl, Stacks.sectionRestrict_apply]
  exact (ratTotal_incl sX W' q _).trans ((congrArg Subtype.val (ratForm_piece_map sX h q y)).trans
    (ratTotal_incl sX W q y).symm)

/-- **`ratTotal` is unchanged by restriction** to a smaller non-empty affine open. -/
theorem ratTotal_totalRestrict {W W' : X.affineOpens} (h : (W' : X.Opens) ≤ W)
    [Nonempty (W : X.Opens)] [Nonempty (W' : X.Opens)]
    (z : (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
      (op (W : X.Opens))) :
    ratTotal sX W'
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.totalRestrict
      (homOfLE h).op z) = ratTotal sX W z := by
  induction z using Stacks.GradedAlgebra.incl_induction with
  | zero => simp
  | incl i y =>
    cases i with
    | ofNat q => exact ratTotal_totalRestrict_incl sX h q y
    | negSucc m =>
      rw [Stacks.GradedAlgebra.totalRestrict_incl]
      exact (DirectSum.toAddMonoid_of _ _ _).trans (DirectSum.toAddMonoid_of _ _ _).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end Total

end MMP.FourfoldProofs.FractionalLogComplexProof
