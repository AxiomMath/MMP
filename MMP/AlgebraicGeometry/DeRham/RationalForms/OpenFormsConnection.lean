module

public import MMP.AlgebraicGeometry.DeRham.RationalForms.OpenSubscheme
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.ChartForms

/-!
# Rational forms of the forms on a non-empty open

Let `Y` be an integral scheme over a field `k` and `U ⊆ Y` a non-empty open. A form on an open
of `U` has, on every non-empty affine open `O ⊆ U`, a rational form in `⋀^q Ω_{k(U)/k}`, which we
move to `⋀^q Ω_{k(Y)/k}` along `k(U) ≅ k(Y)`
(`MMP.FourfoldProofs.FractionalLogComplexProof.openRatForm`). These rational forms are additive,
unchanged by restriction, commute with `d`, turn multiplication by a function into
multiplication by its germ, and determine the form when `U` is smooth over `k`.

The connection `∇ = d - N⁻¹ (du/u) ∧` of the fractional logarithmic complex is written, on
sections, as the identity `N u ∇β = N u dβ - du ∧ β` in the total ring of forms. Its rational
forms satisfy the same identity in the exterior algebra of `Ω_{k(Y)/k}`, with `u` replaced by its
germ, and this identity is carried along every tower of `k`-algebras by the pull-back of forms.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.exteriorWedgeLeft`: `β ↦ x ∧ β`,
  `⋀^q M → ⋀^{q+1} M`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.openRatForm`: the rational form, in `k(Y)`, of a form
  over a non-empty affine open of `U`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.nabla_mapExteriorPower`: the identity
  `N ψ β' = N ψ dβ - dψ ∧ β` is carried along the pull-back of forms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.eq_of_openRatForm_eq`: forms are determined by their
  rational forms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.openRatForm_nabla`: the rational forms of an identity
  `N u β' = N u dβ - du ∧ β` of forms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

/-! ### Left multiplication in the exterior algebra -/

section Wedge

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Left multiplication by `x ∈ M` in the exterior algebra, `⋀^q M → ⋀^{q+1} M`. -/
noncomputable def exteriorWedgeLeft (x : M) (q : ℕ) : ⋀[R]^q M →ₗ[R] ⋀[R]^(q + 1) M where
  toFun β := ⟨ExteriorAlgebra.ι R x * β, by
    rw [ExteriorAlgebra.exteriorPower, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) β.2⟩
  map_add' β γ := Subtype.ext (by simp [mul_add])
  map_smul' c β := Subtype.ext (by simp)

/-- The underlying element of `x ∧ β` in the exterior algebra is the product `ι x * β`. -/
@[simp]
theorem coe_exteriorWedgeLeft (x : M) (q : ℕ) (β : ⋀[R]^q M) :
    (exteriorWedgeLeft x q β : ExteriorAlgebra R M) = ExteriorAlgebra.ι R x * β := rfl

/-- Left multiplication by `x` sends `v₀ ∧ ⋯ ∧ v_{q-1}` to `x ∧ v₀ ∧ ⋯ ∧ v_{q-1}`. -/
@[simp]
theorem exteriorWedgeLeft_ιMulti (x : M) (q : ℕ) (v : Fin q → M) :
    exteriorWedgeLeft x q (exteriorPower.ιMulti R q v) =
      exteriorPower.ιMulti R (q + 1) (Fin.cons x v) := by
  apply Subtype.ext
  rw [coe_exteriorWedgeLeft, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply]
  simp [Matrix.vecTail]

end Wedge

section Tower

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- **The pull-back of forms commutes with `x ∧ -`.** -/
theorem mapExteriorPower_exteriorWedgeLeft (x : Ω[A⁄R]) (q : ℕ) (β : ⋀[A]^q (Ω[A⁄R])) :
    mapExteriorPower R A B (q + 1) (exteriorWedgeLeft x q β) =
      exteriorWedgeLeft (KaehlerDifferential.map R R A B x) q (mapExteriorPower R A B q β) := by
  have h : (mapExteriorPower R A B (q + 1)).comp (exteriorWedgeLeft x q) =
      ((exteriorWedgeLeft (KaehlerDifferential.map R R A B x) q).restrictScalars A).comp
        (mapExteriorPower R A B q) := by
    refine exteriorPower.linearMap_ext ?_
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, exteriorWedgeLeft_ιMulti, mapExteriorPower_ιMulti]
    exact congrArg (fun w => ((exteriorPower.ιMulti B (q + 1) w : ⋀[B]^(q + 1) (Ω[B⁄R])) :
      ExteriorAlgebra B Ω[B⁄R])) (funext fun i => Fin.cases rfl (fun j => rfl) i)
  exact congrArg (fun φ => φ β) h

/-- **The identity `N ψ β' = N ψ dβ - dψ ∧ β` is carried along the pull-back of forms**, in the
exterior algebras of `Ω_{A/R}` and `Ω_{B/R}`. -/
theorem nabla_mapExteriorPower (q N : ℕ) (ψ : A) (β : ⋀[A]^q (Ω[A⁄R]))
    (β' δβ : ⋀[A]^(q + 1) (Ω[A⁄R]))
    (h : N • (algebraMap A (ExteriorAlgebra A Ω[A⁄R]) ψ * (β' : ExteriorAlgebra A Ω[A⁄R])) =
      N • (algebraMap A (ExteriorAlgebra A Ω[A⁄R]) ψ * (δβ : ExteriorAlgebra A Ω[A⁄R])) -
        ExteriorAlgebra.ι A (KaehlerDifferential.D R A ψ) * (β : ExteriorAlgebra A Ω[A⁄R])) :
    N • (algebraMap A B ψ • (mapExteriorPower R A B (q + 1) β' : ExteriorAlgebra B Ω[B⁄R])) =
      N • (algebraMap A B ψ •
          (mapExteriorPower R A B (q + 1) δβ : ExteriorAlgebra B Ω[B⁄R])) -
        ExteriorAlgebra.ι B (KaehlerDifferential.D R B (algebraMap A B ψ)) *
          (mapExteriorPower R A B q β : ExteriorAlgebra B Ω[B⁄R]) := by
  have h' : N • (ψ • β') = N • (ψ • δβ) - exteriorWedgeLeft (KaehlerDifferential.D R A ψ) q β :=
    Subtype.ext (by
      simp only [Submodule.coe_sub, AddSubmonoidClass.coe_nsmul, Submodule.coe_smul,
        coe_exteriorWedgeLeft]
      rw [Algebra.smul_def ψ, Algebra.smul_def ψ]
      exact h)
  have h2 := congrArg (fun γ => (mapExteriorPower R A B (q + 1) γ : ExteriorAlgebra B Ω[B⁄R])) h'
  simp only [map_sub, map_nsmul, LinearMap.map_smul, mapExteriorPower_exteriorWedgeLeft,
    KaehlerDifferential.map_D] at h2
  rw [← algebraMap_smul B ψ (mapExteriorPower R A B (q + 1) β'),
    ← algebraMap_smul B ψ (mapExteriorPower R A B (q + 1) δβ)] at h2
  simpa only [Submodule.coe_sub, AddSubmonoidClass.coe_nsmul, Submodule.coe_smul,
    coe_exteriorWedgeLeft] using h2

end Tower

/-! ### Rational forms of the forms on a non-empty open -/

section OpenRatForm

variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y] (U : Y.Opens) [Nonempty U]
  (sY : Y ⟶ Spec (.of k))

/-- **The rational form**, in `k(Y)`, of a form over a non-empty affine open `O` of `U`: its
rational form in `k(U)`, moved to `k(Y)` along `k(U) ≅ k(Y)`. -/
noncomputable abbrev openRatForm (q : ℕ) (O : U.toScheme.affineOpens)
    [Nonempty (O : U.toScheme.Opens)]
    (θ : Γ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ), O)) :
    letI := MMP.Mori.functionFieldAlgebra sY
    ⋀[Y.functionField]^q Ω[Y.functionField⁄k] :=
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  openFormsMap U sY q (ratForm (U.ι ≫ sY) q O θ)

/-- The rational form in `k(Y)` is the image of the rational form in `k(U)` under
`openFormsMap`. -/
theorem openRatForm_apply (q : ℕ) (O : U.toScheme.affineOpens) [Nonempty (O : U.toScheme.Opens)]
    (θ : Γ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ), O)) :
    openRatForm U sY q O θ = openFormsMap U sY q (ratForm (U.ι ≫ sY) q O θ) := rfl

/-- Rational forms are additive. -/
theorem openRatForm_add (q : ℕ) (O : U.toScheme.affineOpens) [Nonempty (O : U.toScheme.Opens)]
    (θ θ' : Γ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ), O)) :
    openRatForm U sY q O (θ + θ') = openRatForm U sY q O θ + openRatForm U sY q O θ' := by
  rw [openRatForm_apply, openRatForm_apply, openRatForm_apply, map_add, map_add]

/-- Rational forms are unchanged by restriction. -/
theorem openRatForm_restrict (q : ℕ) {O O' : U.toScheme.affineOpens}
    (h : (O' : U.toScheme.Opens) ≤ O) [Nonempty (O : U.toScheme.Opens)]
    [Nonempty (O' : U.toScheme.Opens)] (θ : Γ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ), O)) :
    openRatForm U sY q O' (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE h).op θ) = openRatForm U sY q O θ := by
  rw [openRatForm_apply, openRatForm_apply, ratForm_restrict]

/-- **Forms over an open of `U` are determined by their rational forms**, when `U` is smooth over
`k`. -/
theorem eq_of_openRatForm_eq {m : ℕ} [SmoothOfRelativeDimension m (U.ι ≫ sY)] (q : ℕ)
    {Ω : U.toScheme.Opens} (θ θ' : Γ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ), Ω))
    (h : ∀ (O : U.toScheme.affineOpens) (hO : (O : U.toScheme.Opens) ≤ Ω)
      [Nonempty (O : U.toScheme.Opens)],
      openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE hO).op θ) =
        openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE hO).op θ')) :
    θ = θ' :=
  eq_of_ratForm_eq (U.ι ≫ sY) (m := m) q θ θ' fun O hO _ =>
    (openFormsMap_bijective U sY q).1 (h O hO)

/-- `eq_of_openRatForm_eq` for sections of the pieces of the algebra of forms. -/
theorem eq_of_openRatForm_eq_piece {m : ℕ} [SmoothOfRelativeDimension m (U.ι ≫ sY)] (q : ℕ)
    {Ω : U.toScheme.Opens}
    (θ θ' : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω))
    (h : ∀ (O : U.toScheme.affineOpens) (hO : (O : U.toScheme.Opens) ≤ Ω)
      [Nonempty (O : U.toScheme.Opens)],
      openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE hO).op θ) =
        openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE hO).op θ')) :
    θ = θ' :=
  eq_of_openRatForm_eq U sY (m := m) q θ θ' h

/-- **Rational forms commute with `d`.** -/
theorem openRatForm_d (q : ℕ) (O : U.toScheme.affineOpens) [Nonempty (O : U.toScheme.Opens)]
    (θ : Γ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ), O)) :
    letI := MMP.Mori.functionFieldAlgebra sY
    openRatForm U sY (q + 1) O
        ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op (O : U.toScheme.Opens)) θ) =
      deRhamDifferential (A := k) q (openRatForm U sY q O θ) := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  let := openFunctionFieldAlgebra U
  have := isScalarTower_openFunctionField U sY
  refine (congrArg (openFormsMap U sY (q + 1)) (ratForm_d (U.ι ≫ sY) q O θ)).trans ?_
  exact KaehlerDifferential.mapExteriorPower_deRhamDifferential k U.toScheme.functionField
    Y.functionField q _

/-- **Rational forms turn multiplication by a function into multiplication by its germ.** -/
theorem openRatForm_smul (q : ℕ) (O : U.toScheme.affineOpens) [Nonempty (O : U.toScheme.Opens)]
    (a : Γ(U.toScheme, O)) (θ : Γ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ), O)) :
    letI := MMP.Mori.functionFieldAlgebra sY
    openRatForm U sY q O (a • θ) =
      openFunctionFieldEquiv U (U.toScheme.germToFunctionField O a) • openRatForm U sY q O θ := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  rw [openRatForm_apply, openRatForm_apply, ratForm_smul, openFormsMap_smul]

/-- The germ in `k(Y)` of the restriction to an open `O` of `U` of a function on an open `W` of
`Y` is its germ. -/
theorem openFunctionFieldEquiv_germ_restrict {W : Y.Opens} [Nonempty W] {O : U.toScheme.Opens}
    [Nonempty O] (h : O ≤ U.ι ⁻¹ᵁ W) (a : Γ(Y, W)) :
    openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
      (U.toScheme.presheaf.map (homOfLE h).op (U.ι.app W a))) = Y.germToFunctionField W a := by
  have : Nonempty (U.ι ⁻¹ᵁ W) := let ⟨x⟩ := ‹Nonempty O›; ⟨⟨x.1, h x.2⟩⟩
  rw [germToFunctionField_map h, openFunctionFieldEquiv_germ]

/-- The rational forms in `k(U)` of an identity `N u β' = N u dβ - du ∧ β` of forms over a
non-empty affine open `O` of `U`. -/
theorem ratForm_nabla (q N : ℕ) (O : U.toScheme.affineOpens) [Nonempty (O : U.toScheme.Opens)]
    (a : Γ(U.toScheme, O)) (b : Γ((U.ι ≫ sY).relativeDifferentialForms (q : ℤ), O))
    (b' : Γ((U.ι ≫ sY).relativeDifferentialForms ((q + 1 : ℕ) : ℤ), O))
    (h : N • ((TB (U.ι ≫ sY)).structureMap (op (O : U.toScheme.Opens)) a *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ) b') =
      N • ((TB (U.ι ≫ sY)).structureMap (op (O : U.toScheme.Opens)) a *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ)
          ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op (O : U.toScheme.Opens)) b)) -
      δ (U.ι ≫ sY) O a * (TB (U.ι ≫ sY)).incl (q : ℤ) b) :
    letI := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
    N • (algebraMap U.toScheme.functionField
          (ExteriorAlgebra U.toScheme.functionField Ω[U.toScheme.functionField⁄k])
          (U.toScheme.germToFunctionField O a) * (ratForm (U.ι ≫ sY) (q + 1) O b' : _)) =
      N • (algebraMap U.toScheme.functionField
          (ExteriorAlgebra U.toScheme.functionField Ω[U.toScheme.functionField⁄k])
          (U.toScheme.germToFunctionField O a) *
            (deRhamDifferential (A := k) q (ratForm (U.ι ≫ sY) q O b) : _)) -
        ExteriorAlgebra.ι U.toScheme.functionField (KaehlerDifferential.D k
          U.toScheme.functionField (U.toScheme.germToFunctionField O a)) *
          (ratForm (U.ι ≫ sY) q O b : _) := by
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  have e1 := (ratTotal_structureMap_mul_incl (U.ι ≫ sY) O (q + 1) a b').trans
    (congrArg (_ * ·) (ratTotal_incl (U.ι ≫ sY) O (q + 1) b'))
  have e2 := (ratTotal_structureMap_mul_incl (U.ι ≫ sY) O (q + 1) a
    ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op (O : U.toScheme.Opens)) b)).trans
    (congrArg (_ * ·) ((ratTotal_incl (U.ι ≫ sY) O (q + 1) _).trans
      (congrArg Subtype.val (ratForm_d (U.ι ≫ sY) q O b))))
  have e3 := (ratTotal_incl_mul_incl (U.ι ≫ sY) O 1 q _ b).trans (congrArg₂ (· * ·)
    (ratTotal_incl_exactOne (U.ι ≫ sY) O a) (ratTotal_incl (U.ι ≫ sY) O q b))
  have := congrArg (ratTotal (U.ι ≫ sY) O) h
  rw [map_sub, map_nsmul, map_nsmul] at this
  refine ((congrArg (N • ·) e1).symm.trans this).trans ?_
  exact congrArg₂ (fun x y => N • x - y) e2 e3

omit [IsIntegral Y] [Nonempty U] in
/-- An identity `N u β' = N u dβ - du ∧ β` of forms over an open `Ω` restricts to every smaller
open. -/
theorem nabla_restrict (q N : ℕ) {Ω Ω' : U.toScheme.Opens} (hΩ : Ω' ≤ Ω) (a : Γ(U.toScheme, Ω))
    (β : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj (op Ω))
    (β' : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece
      ((q + 1 : ℕ) : ℤ)).val.obj (op Ω))
    (h : N • ((TB (U.ι ≫ sY)).structureMap (op Ω) a *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ) β') =
      N • ((TB (U.ι ≫ sY)).structureMap (op Ω) a *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ)
          ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω) β)) -
      (TB (U.ι ≫ sY)).incl 1
          ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials (U.ι ≫ sY))).val.app
            (op Ω) ((Scheme.Hom.universalRelativeDerivation (U.ι ≫ sY)).d (X := op Ω) a)) *
        (TB (U.ι ≫ sY)).incl (q : ℤ) β) :
    N • ((TB (U.ι ≫ sY)).structureMap (op Ω') (U.toScheme.presheaf.map (homOfLE hΩ).op a) *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ)
          (((U.ι ≫ sY).relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
            (homOfLE hΩ).op β')) =
      N • ((TB (U.ι ≫ sY)).structureMap (op Ω') (U.toScheme.presheaf.map (homOfLE hΩ).op a) *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ)
          ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω')
            (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hΩ).op β))) -
      δ (U.ι ≫ sY) Ω' (U.toScheme.presheaf.map (homOfLE hΩ).op a) *
        (TB (U.ι ≫ sY)).incl (q : ℤ)
          (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hΩ).op β) := by
  have r1 : ∀ (i : ℤ) (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece
      i).val.obj (op Ω)), (TB (U.ι ≫ sY)).totalRestrict (homOfLE hΩ).op
        ((TB (U.ι ≫ sY)).structureMap (op Ω) a * (TB (U.ι ≫ sY)).incl i x) =
      (TB (U.ι ≫ sY)).structureMap (op Ω') (U.toScheme.presheaf.map (homOfLE hΩ).op a) *
        (TB (U.ι ≫ sY)).incl i (Stacks.sectionRestrict
          ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece i).val
            (homOfLE hΩ).op x) := by
    intro i x
    rw [Stacks.GradedAlgebra.totalRestrict_mul, Stacks.GradedAlgebra.totalRestrict_incl]
    exact congrArg (· * _) (totalRestrict_sm (g := U.ι ≫ sY) (homOfLE hΩ).op a)
  have hd : Stacks.sectionRestrict ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece
      ((q + 1 : ℕ) : ℤ)).val (homOfLE hΩ).op
        ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω) β) =
      (((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω')
        (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hΩ).op β) :=
    (PresheafOfModules.naturality_apply (((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val
      (homOfLE hΩ).op β).symm
  have e2 : (TB (U.ι ≫ sY)).totalRestrict (homOfLE hΩ).op
      ((TB (U.ι ≫ sY)).structureMap (op Ω) a * (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ)
        ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω) β)) =
      (TB (U.ι ≫ sY)).structureMap (op Ω') (U.toScheme.presheaf.map (homOfLE hΩ).op a) *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ)
          ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω')
            (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hΩ).op β)) :=
    (r1 _ _).trans (congrArg (fun x => _ * (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ) x) hd)
  have e3 : (TB (U.ι ≫ sY)).totalRestrict (homOfLE hΩ).op ((TB (U.ι ≫ sY)).incl 1
        ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials (U.ι ≫ sY))).val.app
          (op Ω) ((Scheme.Hom.universalRelativeDerivation (U.ι ≫ sY)).d (X := op Ω) a)) *
      (TB (U.ι ≫ sY)).incl (q : ℤ) β) =
      δ (U.ι ≫ sY) Ω' (U.toScheme.presheaf.map (homOfLE hΩ).op a) *
        (TB (U.ι ≫ sY)).incl (q : ℤ)
          (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hΩ).op β) := by
    rw [Stacks.GradedAlgebra.totalRestrict_mul, Stacks.GradedAlgebra.totalRestrict_incl]
    exact congrArg (· * _) (totalRestrict_δ (g := U.ι ≫ sY) (homOfLE hΩ).op a)
  have := congrArg ((TB (U.ι ≫ sY)).totalRestrict (homOfLE hΩ).op) h
  rw [map_sub, map_nsmul, map_nsmul, r1 _ β', e2, e3] at this
  exact this

/-- **The rational forms of an identity `N u β' = N u dβ - du ∧ β`** of forms over an open `Ω` of
`U`: on every non-empty affine open `O ⊆ Ω`, with `ψ` the germ of `u` in `k(Y)`, the rational
forms satisfy `N ψ β' = N ψ dβ - dψ ∧ β` in the exterior algebra of `Ω_{k(Y)/k}`. -/
theorem openRatForm_nabla (q N : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)] (a : Γ(U.toScheme, Ω))
    (β : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj (op Ω))
    (β' : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece
      ((q + 1 : ℕ) : ℤ)).val.obj (op Ω))
    (h : N • ((TB (U.ι ≫ sY)).structureMap (op Ω) a *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ) β') =
      N • ((TB (U.ι ≫ sY)).structureMap (op Ω) a *
        (TB (U.ι ≫ sY)).incl ((q + 1 : ℕ) : ℤ)
          ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω) β)) -
      (TB (U.ι ≫ sY)).incl 1
          ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials (U.ι ≫ sY))).val.app
            (op Ω) ((Scheme.Hom.universalRelativeDerivation (U.ι ≫ sY)).d (X := op Ω) a)) *
        (TB (U.ι ≫ sY)).incl (q : ℤ) β) :
    letI := MMP.Mori.functionFieldAlgebra sY
    N • (openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
          (U.toScheme.presheaf.map (homOfLE hO).op a)) •
        (openRatForm U sY (q + 1) O (((U.ι ≫ sY).relativeDifferentialForms
          ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hO).op β') :
            ExteriorAlgebra Y.functionField Ω[Y.functionField⁄k])) =
      N • (openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
          (U.toScheme.presheaf.map (homOfLE hO).op a)) •
        (deRhamDifferential (A := k) q (openRatForm U sY q O
          (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hO).op β)) :
            ExteriorAlgebra Y.functionField Ω[Y.functionField⁄k])) -
        ExteriorAlgebra.ι Y.functionField (KaehlerDifferential.D k Y.functionField
          (openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
            (U.toScheme.presheaf.map (homOfLE hO).op a)))) *
          (openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
            (homOfLE hO).op β) : ExteriorAlgebra Y.functionField Ω[Y.functionField⁄k]) := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  let := openFunctionFieldAlgebra U
  have := isScalarTower_openFunctionField U sY
  have h3 := nabla_mapExteriorPower k U.toScheme.functionField Y.functionField q N _ _ _ _
    (ratForm_nabla U sY q N O _ _ _ (nabla_restrict U sY q N hO a β β' h))
  refine h3.trans ?_
  rw [KaehlerDifferential.mapExteriorPower_deRhamDifferential]
  rfl

/-- **The rational forms of an identity `β₂ = c β`** of forms over an open `Ω` of `U`: on every
non-empty affine open `O ⊆ Ω`, the rational form of `β₂` is the germ of `c` times that of `β`. -/
theorem openRatForm_eq_smul_of_incl_eq (q : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)] (c : Γ(U.toScheme, Ω))
    (β β₂ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω))
    (h : (TB (U.ι ≫ sY)).incl (q : ℤ) β₂ =
      (TB (U.ι ≫ sY)).structureMap (op Ω) c * (TB (U.ι ≫ sY)).incl (q : ℤ) β) :
    letI := MMP.Mori.functionFieldAlgebra sY
    openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE hO).op β₂) =
      openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
          (U.toScheme.presheaf.map (homOfLE hO).op c)) •
        openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE hO).op β) := by
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  have h1 : (TB (U.ι ≫ sY)).incl (q : ℤ)
      (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hO).op β₂) =
      (TB (U.ι ≫ sY)).structureMap (op (O : U.toScheme.Opens))
        (U.toScheme.presheaf.map (homOfLE hO).op c) * (TB (U.ι ≫ sY)).incl (q : ℤ)
          (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hO).op β) := by
    refine ((TB (U.ι ≫ sY)).totalRestrict_incl (homOfLE hO).op (q : ℤ) β₂).symm.trans ?_
    refine (congrArg ((TB (U.ι ≫ sY)).totalRestrict (homOfLE hO).op) h).trans ?_
    rw [Stacks.GradedAlgebra.totalRestrict_mul, Stacks.GradedAlgebra.totalRestrict_incl]
    exact congrArg (· * _) (totalRestrict_sm (g := U.ι ≫ sY) (homOfLE hO).op c)
  have h2 := congrArg (ratTotal (U.ι ≫ sY) O) h1
  have h3 : (ratForm (U.ι ≫ sY) q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE hO).op β₂) : ExteriorAlgebra U.toScheme.functionField
          Ω[U.toScheme.functionField⁄k]) =
      ((U.toScheme.germToFunctionField O (U.toScheme.presheaf.map (homOfLE hO).op c) •
        ratForm (U.ι ≫ sY) q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE hO).op β) : ⋀[U.toScheme.functionField]^q (Ω[U.toScheme.functionField⁄k])) :
          ExteriorAlgebra U.toScheme.functionField Ω[U.toScheme.functionField⁄k]) := by
    rw [Submodule.coe_smul, Algebra.smul_def]
    exact (ratTotal_incl (U.ι ≫ sY) O q _).symm.trans (h2.trans
      ((ratTotal_structureMap_mul_incl (U.ι ≫ sY) O q _ _).trans
        (congrArg (_ * ·) (ratTotal_incl (U.ι ≫ sY) O q _))))
  rw [openRatForm_apply, openRatForm_apply, Subtype.ext h3, openFormsMap_smul]

/-- The rational form on `O` of a form restricted first to `Ω'` equals that of the form restricted
directly to `O`. -/
theorem openRatForm_map_map (q : ℕ) {Ω Ω' : U.toScheme.Opens} (h : Ω' ≤ Ω)
    (O : U.toScheme.affineOpens) (hO : (O : U.toScheme.Opens) ≤ Ω')
    [Nonempty (O : U.toScheme.Opens)]
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE hO).op
        (((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.map
          (homOfLE h).op θ)) =
      openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (hO.trans h)).op θ) :=
  congrArg (openRatForm U sY q O) (piece_map_map _ _ _ _ θ)

/-- The rational forms of a form over an open of `U` on an affine open `O` and on a smaller affine
open `O'` agree. -/
theorem openRatForm_mono (q : ℕ) {Ω : U.toScheme.Opens} {O O' : U.toScheme.affineOpens}
    (hO : (O : U.toScheme.Opens) ≤ Ω) (h : (O' : U.toScheme.Opens) ≤ O)
    [Nonempty (O : U.toScheme.Opens)] [Nonempty (O' : U.toScheme.Opens)]
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    openRatForm U sY q O' (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (h.trans hO)).op θ) =
      openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE hO).op θ) := by
  rw [← openRatForm_restrict U sY q h]
  exact congrArg (openRatForm U sY q O') (piece_map_map _ (homOfLE hO).op (homOfLE h).op
    (homOfLE (h.trans hO)).op θ).symm

/-- **Rational forms commute with `d`**, for forms over an open of `U`. -/
theorem openRatForm_map_d (q : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)]
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    letI := MMP.Mori.functionFieldAlgebra sY
    openRatForm U sY (q + 1) O
      (((U.ι ≫ sY).relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hO).op
        ((((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val.app (op Ω) θ)) =
      deRhamDifferential (A := k) q (openRatForm U sY q O
        (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hO).op θ)) := by
  rw [← openRatForm_d]
  exact congrArg (openRatForm U sY (q + 1) O)
    (PresheafOfModules.naturality_apply (((U.ι ≫ sY).deRhamComplex).d q (q + 1)).val
      (homOfLE hO).op θ).symm

/-- Rational forms turn multiplication by a function into multiplication by its germ, for forms
over an open of `U`. -/
theorem openRatForm_map_smul (q : ℕ) {Ω : U.toScheme.Opens} (O : U.toScheme.affineOpens)
    (hO : (O : U.toScheme.Opens) ≤ Ω) [Nonempty (O : U.toScheme.Opens)]
    (c : (Stacks.RingedSpace.structureRingSheaf U.toScheme.toRingedSpace).obj.obj (op Ω))
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ sY)).piece (q : ℤ)).val.obj
      (op Ω)) :
    letI := MMP.Mori.functionFieldAlgebra sY
    openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE hO).op (c • θ)) =
      openFunctionFieldEquiv U (U.toScheme.germToFunctionField O
          (U.toScheme.presheaf.map (homOfLE hO).op c)) •
        openRatForm U sY q O (((U.ι ≫ sY).relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE hO).op θ) :=
  openRatForm_eq_smul_of_incl_eq U sY q O hO c θ (c • θ) (sm_mul_incl (g := U.ι ≫ sY) c q θ).symm

end OpenRatForm

end MMP.FourfoldProofs.FractionalLogComplexProof
