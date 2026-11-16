module

public import MMP.AlgebraicGeometry.DeRham.RationalForms.Separation
public import MMP.AlgebraicGeometry.DeRham.RationalForms.TotalRing

/-!
# Rational forms on an integral scheme, independently of the affine open

On an integral scheme `X` over `k` any two non-empty open subsets meet, so the rational forms of
the restrictions of a form on an open `O` to two non-empty affine opens inside `O` agree: both
equal the rational form on a non-empty affine open inside their intersection. This makes the
rational form of a section over any non-empty open well defined.

The map `ratTotal` to the exterior algebra of rational forms is multiplicative on the sums of
homogeneous forms of non-negative degree, which contain `1` and the functions and are closed under
products; in particular it carries a product of functions and exact `1`-forms to the
corresponding product of rational functions and exact rational `1`-forms.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.nonnegForms`: the sums of homogeneous forms of
  non-negative degree.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.ratForm_eq_of_le`: independence of the affine open.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratTotal_mul`: multiplicativity on `nonnegForms`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- On an integral scheme, the rational forms of the restrictions of a form on `O` to any two
non-empty affine opens contained in `O` agree. -/
theorem ratForm_eq_of_le [IsIntegral X] (q : ℕ) {O : X.Opens}
    (θ : Γ(sX.relativeDifferentialForms (q : ℤ), O)) {W₁ W₂ : X.affineOpens}
    (h₁ : (W₁ : X.Opens) ≤ O) (h₂ : (W₂ : X.Opens) ≤ O) [Nonempty (W₁ : X.Opens)]
    [Nonempty (W₂ : X.Opens)] :
    ratForm sX q W₁ ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h₁).op θ) =
      ratForm sX q W₂ ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h₂).op θ) := by
  obtain ⟨⟨x₁, hx₁⟩⟩ := ‹Nonempty (W₁ : X.Opens)›
  obtain ⟨⟨x₂, hx₂⟩⟩ := ‹Nonempty (W₂ : X.Opens)›
  obtain ⟨x, hx₁', hx₂'⟩ := nonempty_preirreducible_inter (W₁ : X.Opens).isOpen
    (W₂ : X.Opens).isOpen ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
  obtain ⟨_, ⟨W₃, hW₃, rfl⟩, hxW₃, hW₃le⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ ((W₁ : X.Opens) ⊓ W₂ : X.Opens)
      from ⟨hx₁', hx₂'⟩) ((W₁ : X.Opens) ⊓ W₂).isOpen
  let W : X.affineOpens := ⟨W₃, hW₃⟩
  have hW1 : (W : X.Opens) ≤ W₁ := fun y hy => (hW₃le hy).1
  have hW2 : (W : X.Opens) ≤ W₂ := fun y hy => (hW₃le hy).2
  have : Nonempty (W : X.Opens) := ⟨⟨x, hxW₃⟩⟩
  rw [← ratForm_restrict sX q hW1, ← ratForm_restrict sX q hW2]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

/-- The sums of homogeneous forms of non-negative degree in the total ring of forms over `O`. -/
noncomputable def nonnegForms (O : X.Opens) :
    AddSubgroup ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
      (op O)) :=
  AddSubgroup.closure {z | ∃ (q : ℕ) (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece
    (q : ℤ)).val.obj (op O)),
      z = (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl (q : ℤ) x}

/-- A homogeneous form of non-negative degree lies in `nonnegForms`. -/
theorem incl_mem_nonnegForms (O : X.Opens) (q : ℕ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece (q : ℤ)).val.obj (op O)) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl (q : ℤ) x ∈
      nonnegForms sX O :=
  AddSubgroup.subset_closure ⟨q, x, rfl⟩

/-- On an integral scheme, `ratTotal` is multiplicative on `nonnegForms`. -/
theorem ratTotal_mul [IsIntegral X] (W : X.affineOpens) [Nonempty (W : X.Opens)]
    {z w : (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
      (op (W : X.Opens))} (hz : z ∈ nonnegForms sX W) (hw : w ∈ nonnegForms sX W) :
    ratTotal sX W (z * w) = ratTotal sX W z * ratTotal sX W w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨p, x, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨q, y, rfl⟩ := hw
      exact ratTotal_incl_mul_incl sX W p q x y
    | zero => simp
    | add w w' _ _ h h' => rw [mul_add, map_add, h, h', map_add, mul_add]
    | neg w _ h => rw [mul_neg, map_neg, h, map_neg, mul_neg]
  | zero => simp
  | add z z' _ _ h h' => rw [add_mul, map_add, h, h', map_add, add_mul]
  | neg z _ h => rw [neg_mul, map_neg, h, map_neg, neg_mul]

/-- The forms of non-negative degree are closed under products. -/
theorem mul_mem_nonnegForms (O : X.Opens)
    {z w : (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total (op O)}
    (hz : z ∈ nonnegForms sX O) (hw : w ∈ nonnegForms sX O) : z * w ∈ nonnegForms sX O := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨p, x, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨q, y, rfl⟩ := hw
      rw [Stacks.GradedAlgebra.incl_mul_incl]
      exact incl_mem_nonnegForms sX O (p + q) _
    | zero => simp
    | add w w' _ _ h h' => simpa only [mul_add] using add_mem h h'
    | neg w _ h => simpa only [mul_neg] using neg_mem h
  | zero => simp
  | add z z' _ _ h h' => simpa only [add_mul] using add_mem h h'
  | neg z _ h => simpa only [neg_mul] using neg_mem h

/-- The unit of the total ring of forms lies in `nonnegForms`. -/
theorem one_mem_nonnegForms (O : X.Opens) :
    (1 : (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total (op O)) ∈
      nonnegForms sX O := by
  rw [Stacks.GradedAlgebra.one_eq_incl]
  exact incl_mem_nonnegForms sX O 0 _

/-- The image of a function under the structure map lies in `nonnegForms`. -/
theorem structureMap_mem_nonnegForms (O : X.Opens) (a : Γ(X, O)) :
    (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap (op O)
      a ∈ nonnegForms sX O := by
  let a' : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj (op O) := a
  change a' • (1 : (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
    (op O)) ∈ _
  rw [Stacks.GradedAlgebra.one_eq_incl, ← Stacks.GradedAlgebra.incl_smul]
  exact incl_mem_nonnegForms sX O 0 _

/-- The unit of the de Rham algebras is the unit of the algebra of forms. -/
theorem deRhamAlgebras_one_eq (W : X.Opens) :
    (Scheme.Hom.deRhamAlgebras sX).exterior.one.eval (op W) =
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.one.eval (op W) :=
  rfl

/-- The algebraic form of the unit section is `1`. -/
theorem formsAlgEquiv_one (W : X.affineOpens) :
    letI := MMP.Mori.sectionAlgebra sX W
    MMP.DeRham.formsAlgEquiv sX 0 W
        ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.one.eval
          (op (W : X.Opens))) = exteriorPower.ιMulti Γ(X, W) 0 Fin.elim0 := by
  let := MMP.Mori.sectionAlgebra sX W
  have h := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_one sX W.2
    (isAffineOpen_top _) (by simp)
  rw [deRhamAlgebras_one_eq] at h
  refine (MMP.DeRham.formsAlgEquiv_apply sX 0 W _).trans ?_
  refine (congrArg (exteriorPower.map 0 (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap) h).trans ?_
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact i.elim0

/-- `ratTotal` of the unit is `1`. -/
theorem ratTotal_incl_one [IsIntegral X] (W : X.affineOpens) [Nonempty (W : X.Opens)] :
    ratTotal sX W ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl
      ((0 : ℕ) : ℤ)
        ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.one.eval
          (op (W : X.Opens)))) = 1 := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.functionFieldAlgebra sX
  have := MMP.Mori.isScalarTower_section_functionField sX W
  refine (ratTotal_incl sX W 0 _).trans ?_
  refine (congrArg Subtype.val ((congrArg (mapExteriorPower k Γ(X, W) X.functionField 0)
    (formsAlgEquiv_one sX W)).trans (mapExteriorPower_ιMulti _ _ _ _ _))).trans ?_
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp

/-- `ratTotal` of a function is its germ. -/
theorem ratTotal_structureMap [IsIntegral X] (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (a : Γ(X, W)) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratTotal sX W
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
        (op (W : X.Opens)) a) =
      algebraMap X.functionField (ExteriorAlgebra X.functionField Ω[X.functionField⁄k])
        (X.germToFunctionField W a) := by
  let := MMP.Mori.functionFieldAlgebra sX
  have h := ratTotal_structureMap_mul_incl sX W 0 a
    ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.one.eval
      (op (W : X.Opens)))
  rw [ratTotal_incl_one, mul_one] at h
  refine Eq.trans ?_ h
  congr 1
  exact (mul_one _).symm

/-- The product of a list of elements of `nonnegForms` lies in `nonnegForms`. -/
theorem list_prod_mem_nonnegForms (O : X.Opens)
    (l : List ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
      (op O))) (hl : ∀ z ∈ l, z ∈ nonnegForms sX O) : l.prod ∈ nonnegForms sX O := by
  induction l with
  | nil => exact one_mem_nonnegForms sX O
  | cons z l ih =>
    rw [List.prod_cons]
    exact mul_mem_nonnegForms sX O (hl z List.mem_cons_self)
      (ih fun w hw => hl w (List.mem_cons_of_mem z hw))

/-- `ratTotal` of a product of forms of non-negative degree. -/
theorem ratTotal_list_prod [IsIntegral X] (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (l : List ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.Total
      (op (W : X.Opens)))) (hl : ∀ z ∈ l, z ∈ nonnegForms sX W) :
    ratTotal sX W l.prod = (l.map (ratTotal sX W)).prod := by
  induction l with
  | nil =>
    rw [List.prod_nil, List.map_nil, List.prod_nil, Stacks.GradedAlgebra.one_eq_incl]
    exact ratTotal_incl_one sX W
  | cons z l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      ratTotal_mul sX W (hl z List.mem_cons_self)
        (list_prod_mem_nonnegForms sX W l fun w hw => hl w (List.mem_cons_of_mem z hw)),
      ih fun w hw => hl w (List.mem_cons_of_mem z hw)]

/-- The exact `1`-form `d a` commutes with restriction. -/
theorem exactOne_restrict {O O' : X.Opens} (h : O' ≤ O) (a : Γ(X, O)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).piece 1).val.map (homOfLE h).op
        ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app (op O)
          ((Scheme.Hom.universalRelativeDerivation sX).d (X := op O) a)) =
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app (op O')
        ((Scheme.Hom.universalRelativeDerivation sX).d (X := op O')
          (X.presheaf.map (homOfLE h).op a)) :=
  (PresheafOfModules.naturality_apply
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val
        (homOfLE h).op _).symm.trans (congrArg _
      ((Scheme.Hom.universalRelativeDerivation sX).d_map (homOfLE h).op a).symm)

/-- `ratTotal` of `s · d a`. -/
theorem ratTotal_structureMap_mul_exactOne [IsIntegral X] (W : X.affineOpens)
    [Nonempty (W : X.Opens)] (s a : Γ(X, W)) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ratTotal sX W
      ((Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.structureMap
        (op (W : X.Opens)) s *
      (Scheme.Hom.relativeDifferentialFormsAlgebra sX).toPresheafGradedAlgebra.incl 1
        ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials sX)).val.app
          (op (W : X.Opens))
          ((Scheme.Hom.universalRelativeDerivation sX).d (X := op (W : X.Opens)) a))) =
      algebraMap X.functionField (ExteriorAlgebra X.functionField Ω[X.functionField⁄k])
          (X.germToFunctionField W s) *
        ExteriorAlgebra.ι X.functionField (D k X.functionField (X.germToFunctionField W a)) :=
  (ratTotal_structureMap_mul_incl sX W 1 s _).trans
    (congrArg (_ * ·) (ratTotal_incl_exactOne sX W a))

end MMP.FourfoldProofs.FractionalLogComplexProof
