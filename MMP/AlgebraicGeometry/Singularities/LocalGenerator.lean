module

public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Jacobian

/-!
# Local generators and discrepancies exist (KM 2.25)

* For a pair `(X, Δ)` and `m > 0` with `m(K_X + Δ)` Cartier, `mΔ` is a divisor and every point
  has a neighbourhood on which a form generates `𝒪_X(m(K_X + Δ))`.
* Hence every divisor `(Y, f, E)` over `X` has a discrepancy `a(E, X, Δ)`.

## Main results

* `MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus`: if the generic
  point of every prime divisor is a smooth point, a canonical divisor is the divisor `div(ω)` of a
  nonzero rational top form; `MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq` over a perfect
  field.
* `MMP.Positivity.IsPair.exists_generatesOn`
* `MMP.Positivity.IsPair.exists_isDiscrepancy`

## Implementation notes

`MMP.Positivity.IsPair.exists_generatesOn` and `MMP.Positivity.IsPair.exists_isDiscrepancy` rest
on `MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq`.

What that needs of the base field is that the generic point of every prime divisor be a smooth
point; this holds over a perfect field (KM work over an algebraically closed field), where
`𝒪_{X,Γ}` is a discrete valuation ring, hence formally smooth. Over an imperfect field it can fail,
and then both statements fail: for `k = 𝔽_p(t)` and `X = 𝔸¹_{k(t^{1/p})}` seen over `k`,
`Ω_{X/k}` has rank 2 at every point, so every rational form has order 0 along every prime divisor
and no form generates `𝒪_X(m(K_X + Δ))` when `Δ ≠ 0`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Mori

/-! ### Orders of rational functions -/

/-- The order of vanishing does not depend on the fraction field: if `e : K₁ → K₂` is a map of
fraction fields of `R` over `R`, then `ord_R(e x) = ord_R(x)`. -/
theorem ordFrac_map_of_comp {R K₁ K₂ : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field K₁] [Field K₂] [Algebra R K₁] [Algebra R K₂]
    [IsFractionRing R K₁] [IsFractionRing R K₂] (e : K₁ →+* K₂)
    (he : ∀ r : R, e (algebraMap R K₁ r) = algebraMap R K₂ r) (x : K₁) :
    Ring.ordFrac R (e x) = Ring.ordFrac R x := by
  have h : ∀ r : R, Ring.ordFrac R (algebraMap R K₂ r) = Ring.ordFrac R (algebraMap R K₁ r) := by
    intro r
    by_cases hr : r = 0
    · simp [hr]
    · rw [Ring.ordFrac_eq_ord R hr, Ring.ordFrac_eq_ord R hr]
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, he, he, map_div₀, map_div₀, h a, h s]

/-- An integral scheme has exactly one irreducible component. -/
theorem subsingleton_irreducibleComponents (X : Scheme.{u}) [IsIntegral X] :
    Subsingleton (irreducibleComponents X) := by
  rw [irreducibleComponents_eq_singleton]
  infer_instance

section RationalFunctions

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The generization `𝒪_{X,η_Z} → k(X)` from the factor of `K(X)` on a component `Z` of an
integral scheme to its function field. -/
abbrev componentToFunctionField (Z : irreducibleComponents X) :
    X.presheaf.stalk (componentGenericPoint X Z) ⟶ X.presheaf.stalk (genericPoint X) :=
  X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The specialization `k(X) → 𝒪_{X,η_Z}` from the function field of an integral scheme to the
factor of `K(X)` on a component `Z`. -/
def functionFieldToComponent (Z : irreducibleComponents X) :
    X.functionField →+* X.presheaf.stalk (componentGenericPoint X Z) :=
  (X.presheaf.stalkSpecializes ((isGenericPoint_componentGenericPoint X Z).specializes
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _) trivial))).hom

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- `functionFieldToComponent` is a section of `componentToFunctionField`. -/
theorem componentToFunctionField_functionFieldToComponent (Z : irreducibleComponents X)
    (a : X.functionField) :
    (componentToFunctionField Z).hom (functionFieldToComponent Z a) = a := by
  change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom a = a
  rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- On an integral scheme, the images in `k(X)` of a unit of `K(X)` and of its inverse, taken on
any two components, multiply to `1`. -/
theorem componentToFunctionField_mul_inv (φ : (RationalFunctions X)ˣ)
    (Z Z' : irreducibleComponents X) :
    (componentToFunctionField Z).hom ((φ : RationalFunctions X) Z) *
      (componentToFunctionField Z').hom
        (((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z') = 1 := by
  have := subsingleton_irreducibleComponents X
  obtain rfl := Subsingleton.elim Z Z'
  rw [← map_mul, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Pi.one_apply, map_one]

/-- On an integral scheme the order `v_Γ(φ)` of a unit of `K(X)` is the order of vanishing
`AlgebraicGeometry.Scheme.ord` of its image in the function field. -/
theorem ord_eq_ord_componentToFunctionField (Γ : Mori.PrimeDivisor X)
    (φ : (RationalFunctions X)ˣ) :
    Γ.ord φ = X.ord ((componentToFunctionField Γ.component).hom (φ.val Γ.component))
      Γ.genericPoint := by
  set y := φ.val Γ.component
  have hy : IsUnit y := φ.isUnit.map (Pi.evalRingHom _ Γ.component)
  have hz := Γ.coheight_genericPoint
  have hne : (componentToFunctionField Γ.component).hom y ≠ 0 := (hy.map _).ne_zero
  rw [eq_comm, Scheme.ord_eq_iff hz hne]
  have h1 : (Γ.valuation y : WithZero (Multiplicative ℤ)) =
      ((Γ.ordHom φ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    simp [Mori.PrimeDivisor.ordHom, y, RationalFunctions.component]
  rw [show Multiplicative.ofAdd (Γ.ord φ) = Γ.ordHom φ from rfl, ← h1]
  let := Γ.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions Γ.genericPoint_mem_component
  have : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le hz.le
  let ψ := IsLocalization.algEquiv (nonZeroDivisors Γ.localRing)
    (X.presheaf.stalk (componentGenericPoint X Γ.component)) (FractionRing Γ.localRing)
  change Ring.ordFrac (X.presheaf.stalk Γ.genericPoint) _ = Ring.ordFrac Γ.localRing (ψ y)
  have key := ordFrac_map_of_comp (R := Γ.localRing) (K₁ := FractionRing Γ.localRing)
    (K₂ := X.functionField)
    ((componentToFunctionField Γ.component).hom.comp (ψ.symm : _ →+* _)) ?_ (ψ y)
  · simpa using key
  · intro r
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.commutes]
    change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom r =
      (X.presheaf.stalkSpecializes _).hom r
    rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- On an integral scheme every unit of `K(X)` has the orders of a nonzero rational function. -/
theorem exists_ord_eq_of_units (φ : (RationalFunctions X)ˣ) :
    ∃ g : X.functionField, g ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor X, Γ.ord φ = X.ord g Γ.genericPoint := by
  have := subsingleton_irreducibleComponents X
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨Z₀, -⟩ := exists_mem_irreducibleComponents x
  refine ⟨(componentToFunctionField Z₀).hom (φ.val Z₀),
    ((φ.isUnit.map (Pi.evalRingHom _ Z₀)).map _).ne_zero, fun Γ => ?_⟩
  rw [ord_eq_ord_componentToFunctionField Γ φ, Subsingleton.elim Γ.component Z₀]

/-- On an integral scheme every nonzero rational function has the orders of a unit of `K(X)`. -/
theorem exists_units_of_ne_zero {g : X.functionField} (hg : g ≠ 0) :
    ∃ φ : (RationalFunctions X)ˣ,
      ∀ Γ : Mori.PrimeDivisor X, Γ.ord φ = X.ord g Γ.genericPoint := by
  refine ⟨Units.map (RingHom.pi functionFieldToComponent).toMonoidHom (Units.mk0 g hg),
    fun Γ => ?_⟩
  rw [ord_eq_ord_componentToFunctionField Γ]
  exact congrArg (X.ord · _) (componentToFunctionField_functionFieldToComponent _ g)

end RationalFunctions

open Stacks.RelativeDifferentialStalkMap

section Algebra

variable {k Λ A B : Type*} [CommRing k] [CommRing Λ] [CommRing A] [CommRing B]
  [Algebra k Λ] [Algebra Λ A] [Algebra k A] [IsScalarTower k Λ A]
  [Algebra A B] [Algebra k B] [IsScalarTower k A B]

/-- If `k → Λ` is surjective, `Ω_{A/k} → Ω_{A/Λ}` is bijective. -/
theorem bijective_kaehlerDifferential_map_of_surjective
    (h : Function.Surjective (algebraMap k Λ)) :
    Function.Bijective (KaehlerDifferential.map k Λ A A) := by
  refine ⟨?_, KaehlerDifferential.map_surjective k Λ A⟩
  have : Subsingleton Ω[Λ⁄k] := KaehlerDifferential.subsingleton_of_surjective k Λ h
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map k Λ A x).mp hx
  have hy : y = 0 := by
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => rfl
    | tmul a w => rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [hy, map_zero]

variable (k Λ A B) in
/-- The map `Ω^n_{A/Λ} → Ω^n_{B/k}` induced by `A → B`, for `k → Λ` surjective. -/
def formsBaseChange (h : Function.Surjective (algebraMap k Λ)) (n : ℕ) :
    ⋀[A]^n Ω[A⁄Λ] →ₗ[A] ⋀[B]^n Ω[B⁄k] :=
  (topFormsMap k A B n).comp
    (extCongr n (LinearEquiv.ofBijective _
      (bijective_kaehlerDifferential_map_of_surjective (A := A) h)).symm).toLinearMap

/-- `formsBaseChange` sends `da₁ ∧ ⋯ ∧ daₙ` to `d(a₁) ∧ ⋯ ∧ d(aₙ)`, with the `aᵢ` mapped to `B`. -/
theorem formsBaseChange_ιMulti (h : Function.Surjective (algebraMap k Λ)) {n : ℕ}
    (a : Fin n → A) :
    formsBaseChange k Λ A B h n
        (exteriorPower.ιMulti A n fun i => KaehlerDifferential.D Λ A (a i)) =
      exteriorPower.ιMulti B n fun i => KaehlerDifferential.D k B (algebraMap A B (a i)) := by
  have hD : ∀ x : A, (LinearEquiv.ofBijective _
      (bijective_kaehlerDifferential_map_of_surjective (A := A) h)).symm
        (KaehlerDifferential.D Λ A x) = KaehlerDifferential.D k A x := by
    intro x
    rw [LinearEquiv.symm_apply_eq]
    simp
  simp only [formsBaseChange, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    MMP.Intersection.extCongr_ιMulti, hD, topFormsMap_ιMulti, KaehlerDifferential.map_D]

end Algebra

section FormsStalk

variable {S Y : Scheme.{u}} (q : Y ⟶ S) (n : ℕ) (y : Y)

/-- **Induction on the stalk of `Ω^n_{Y/S}`**: the stalk is generated, as a module over `𝒪_{Y,y}`,
by the germs of the forms `dg₁ ∧ ⋯ ∧ dgₙ`. -/
theorem formsStalk_induction
    {P : ↑(TopCat.Presheaf.stalk (C := Ab)
      ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece (n : ℤ)).val.presheaf y) → Prop}
    (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (V : Y.Opens) (hy : y ∈ V) (r : Γ(Y, V))
      (ω : Γ(Scheme.Hom.relativeDifferentialForms q (n : ℤ), V)),
      P (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf V y hy ω) →
      P (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf V y hy (r • ω)))
    (hgen : ∀ (V : Y.Opens) (hy : y ∈ V) (g : Fin n → Γ(Y, V)),
      P (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf V y hy (Stacks.DeRham.FormsGenerators.gen q V g)))
    (m : ↑(TopCat.Presheaf.stalk (C := Ab)
      ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece (n : ℤ)).val.presheaf y)) :
    P m := by
  let := algebraStalkMap q y
  suffices h : ∀ t, P ((formsStalkEquiv q n y).symm t) by simpa using h (formsStalkEquiv q n y m)
  intro t
  have ht := Submodule.mem_top (R := ToType (Y.sheaf.presheaf.stalk y)) (x := t)
  rw [← exteriorPower.ιMulti_span_of_span _ n (hs := KaehlerDifferential.span_range_derivation
    (ToType (S.presheaf.stalk (q y))) (ToType (Y.sheaf.presheaf.stalk y)))] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    choose w hw using fun i => ha (Set.mem_range_self i)
    obtain ⟨V, hy, g, hg⟩ := MMP.Intersection.exists_germ_eq_of_fin y w
    convert hgen V hy g using 1
    rw [LinearEquiv.symm_apply_eq, MMP.Intersection.formsStalkEquiv_germ_gen q hy g]
    congr 1
    funext i
    rw [hg i, hw i]
  | zero => simpa using h0
  | add x x' _ _ hx hx' =>
    rw [map_add]
    exact hadd _ _ hx hx'
  | smul a x _ hx =>
    obtain ⟨V₂, hy₂, r, hr⟩ : ∃ (V : Y.Opens) (hy : y ∈ V) (r : Γ(Y, V)),
        Y.sheaf.presheaf.germ V y hy r = a := TopCat.Presheaf.exists_germ_eq _ a
    obtain ⟨V₁, hV, hy₁, ω, hω⟩ : ∃ V ≤ V₂, ∃ (hy : y ∈ V)
        (ω : Γ(Scheme.Hom.relativeDifferentialForms q (n : ℤ), V)),
        TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V y hy ω = (formsStalkEquiv q n y).symm x :=
      TopCat.Presheaf.exists_le_germ_eq _ ((formsStalkEquiv q n y).symm x) hy₂
    have h2 : Y.sheaf.presheaf.germ V₁ y hy₁ (Y.presheaf.map (homOfLE hV).op r) = a :=
      (TopCat.Presheaf.germ_res_apply Y.presheaf _ _ _ _).trans hr
    have h4 : formsStalkEquiv q n y (TopCat.Presheaf.germ
        ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece (n : ℤ)).val.presheaf
          V₁ y hy₁ ω) = x :=
      (congrArg (formsStalkEquiv q n y) hω).trans (LinearEquiv.apply_symm_apply _ _)
    have h3 : (formsStalkEquiv q n y).symm (a • x) = TopCat.Presheaf.germ
        ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece (n : ℤ)).val.presheaf
          V₁ y hy₁ (Y.presheaf.map (homOfLE hV).op r • ω) :=
      (LinearEquiv.symm_apply_eq _).mpr
        ((MMP.Intersection.formsStalkEquiv_germ_smul q hy₁ n _ ω).trans
          (congrArg₂ (· • ·) h2 h4)).symm
    exact (congrArg P h3).mpr (hsmul _ _ _ _ ((congrArg P hω).mpr hx))

/-- Restricting a function and a form to a smaller open does not change their germs. -/
theorem exists_res_forms {V W : Y.Opens} (h : W ≤ V) (r : Γ(Y, V))
    (τ : Γ(Scheme.Hom.relativeDifferentialForms q (n : ℤ), V)) :
    ∃ (r' : Γ(Y, W)) (τ' : Γ(Scheme.Hom.relativeDifferentialForms q (n : ℤ), W)),
      (∀ z (hz : z ∈ W), Y.presheaf.germ W z hz r' = Y.presheaf.germ V z (h hz) r) ∧
      (∀ z (hz : z ∈ W), TopCat.Presheaf.germ
          ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf W z hz τ' =
        TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V z (h hz) τ) ∧
      (∀ z (hz : z ∈ W), TopCat.Presheaf.germ
          ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf W z hz (r' • τ') =
        TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V z (h hz) (r • τ)) := by
  refine ⟨Y.presheaf.map (homOfLE h).op r,
    (Scheme.Hom.relativeDifferentialForms q (n : ℤ)).presheaf.map (homOfLE h).op τ,
    fun z hz => TopCat.Presheaf.germ_res_apply _ _ _ _ _,
    fun z hz => TopCat.Presheaf.germ_res_apply _ _ _ _ _, fun z hz => ?_⟩
  rw [← Scheme.Modules.map_smul]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- Two forms with the same germ at `y` have the same germs near `y`. -/
theorem exists_forall_germ_eq_of_germ_eq {V W : Y.Opens} (hV : y ∈ V) (hW : y ∈ W)
    (τ : Γ(Scheme.Hom.relativeDifferentialForms q (n : ℤ), V))
    (τ' : Γ(Scheme.Hom.relativeDifferentialForms q (n : ℤ), W))
    (h : (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf) V y hV τ = (TopCat.Presheaf.germ
            ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
            (n : ℤ)).val.presheaf) W y hW τ') :
    ∃ (W' : Y.Opens) (_ : y ∈ W') (hV' : W' ≤ V) (hW' : W' ≤ W),
      ∀ z (hz : z ∈ W'), (TopCat.Presheaf.germ
          ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf) V z (hV' hz) τ = (TopCat.Presheaf.germ
              ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
              (n : ℤ)).val.presheaf) W z (hW' hz) τ' := by
  obtain ⟨W', hyW', iV, iW, heq⟩ := TopCat.Presheaf.germ_eq _ y hV hW τ τ' h
  refine ⟨W', hyW', iV.le, iW.le, fun z hz => ?_⟩
  exact (TopCat.Presheaf.germ_res_apply _ iV z hz τ).symm.trans
    ((congrArg ((TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials q).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf) W' z hz) heq).trans (TopCat.Presheaf.germ_res_apply _ iW z hz τ'))

end FormsStalk

section OpenForms

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (U : X.Opens)

/-- The `k`-algebra structure of a stalk of `Spec k`. -/
@[instance_reducible]
def specStalkAlgebra (p : Spec (.of k)) : Algebra k (ToType ((Spec (.of k)).presheaf.stalk p)) :=
  StructureSheaf.stalkAlgebra k p

/-- The map from `k` to a stalk of `Spec k` is surjective. -/
theorem surjective_algebraMap_stalk_Spec (p : Spec (.of k)) :
    letI := specStalkAlgebra p
    Function.Surjective (algebraMap k (ToType ((Spec (.of k)).presheaf.stalk p))) :=
  fieldBaseStalkAlgebraMap_surjective (Subsingleton.elim _ _)

/-- The `k`-algebra structure on `𝒪_{U,y}` through `𝒪_{Spec k, ·}`. -/
@[instance_reducible]
def opensStalkAlgebra (y : U.toScheme) : Algebra k (ToType (U.toScheme.sheaf.presheaf.stalk y)) :=
  (((U.ι ≫ sX).stalkMap y).hom.comp (StructureSheaf.toStalk k ((U.ι ≫ sX) y)).hom).toAlgebra

/-- The algebra structure `𝒪_{U,y} → 𝒪_{X,y}` of the stalk isomorphism. -/
@[instance_reducible]
def opensStalkIsoAlgebra (y : U.toScheme) :
    Algebra (ToType (U.toScheme.sheaf.presheaf.stalk y)) (X.presheaf.stalk y.1) :=
  (U.stalkIso y).hom.hom.toAlgebra

/-- The stalk map of `U.ι ≫ sX` at `y`, followed by `𝒪_{U,y} ≅ 𝒪_{X,y}`, is the stalk map of
`sX` at `y`. -/
theorem stalkIso_hom_stalkMap_comp (y : U.toScheme) :
    (U.ι ≫ sX).stalkMap y ≫ (U.stalkIso y).hom = sX.stalkMap y.1 := by
  erw [Scheme.Hom.stalkMap_comp U.ι sX y, Category.assoc, ← Scheme.Opens.stalkIso_inv U y,
    Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The scalar tower `k → 𝒪_{U,y} → 𝒪_{X,y}`. -/
theorem isScalarTower_opensStalk (y : U.toScheme) :
    letI := opensStalkAlgebra sX U y
    letI := opensStalkIsoAlgebra U y
    letI := stalkAlgebra sX y.1
    IsScalarTower k (ToType (U.toScheme.sheaf.presheaf.stalk y)) (X.presheaf.stalk y.1) := by
  let := opensStalkAlgebra sX U y
  let := opensStalkIsoAlgebra U y
  let := stalkAlgebra sX y.1
  refine IsScalarTower.of_algebraMap_eq' ?_
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ y.1 (Opens.mem_top _) =
      (StructureSheaf.toStalk k ((U.ι ≫ sX) y) ≫ (U.ι ≫ sX).stalkMap y) ≫ (U.stalkIso y).hom := by
    erw [Category.assoc, stalkIso_hom_stalkMap_comp sX U y]
    change _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ _ trivial) ≫ _
    erw [Category.assoc, Scheme.Hom.germ_stalkMap sX ⊤ y.1 trivial]
    rfl
  exact congrArg CommRingCat.Hom.hom h

/-- The scalar tower `k → 𝒪_{Spec k, ·} → 𝒪_{U,y}`. -/
theorem isScalarTower_opensStalk_base (y : U.toScheme) :
    letI := algebraStalkMap (U.ι ≫ sX) y
    letI := specStalkAlgebra ((U.ι ≫ sX) y)
    letI := opensStalkAlgebra sX U y
    IsScalarTower k (ToType ((Spec (.of k)).presheaf.stalk ((U.ι ≫ sX) y)))
      (ToType (U.toScheme.sheaf.presheaf.stalk y)) := by
  let := algebraStalkMap (U.ι ≫ sX) y
  let := specStalkAlgebra ((U.ι ≫ sX) y)
  let := opensStalkAlgebra sX U y
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The germ map `(Ω^n_{U/k})_y → Ω^n_{𝒪_{X,y}/k}` of the top forms of an open `U` of a scheme over
`k`: the stalk of `Ω^n_{U/k}` is `⋀ⁿ Ω_{𝒪_{U,y}/𝒪_{Spec k}}`, and `𝒪_{U,y} = 𝒪_{X,y}`,
`𝒪_{Spec k, ·} = k`. -/
def formsGerm (n : ℕ) (y : U.toScheme) :
    letI := stalkAlgebra sX y.1
    ↑(TopCat.Presheaf.stalk (C := Ab)
        ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf y) →+
      ⋀[X.presheaf.stalk y.1]^n Ω[X.presheaf.stalk y.1⁄k] :=
  letI := algebraStalkMap (U.ι ≫ sX) y
  letI := specStalkAlgebra ((U.ι ≫ sX) y)
  letI := opensStalkAlgebra sX U y
  letI := opensStalkIsoAlgebra U y
  letI := stalkAlgebra sX y.1
  haveI := isScalarTower_opensStalk_base sX U y
  haveI := isScalarTower_opensStalk sX U y
  (formsBaseChange k (ToType ((Spec (.of k)).presheaf.stalk ((U.ι ≫ sX) y)))
    (ToType (U.toScheme.sheaf.presheaf.stalk y)) (X.presheaf.stalk y.1)
    (surjective_algebraMap_stalk_Spec _) n).toAddMonoidHom.comp
      (formsStalkEquiv (U.ι ≫ sX) n y).toAddEquiv.toAddMonoidHom

/-- `formsGerm` is `formsStalkEquiv` followed by `formsBaseChange`. -/
theorem formsGerm_apply (n : ℕ) (y : U.toScheme)
    (m : ↑(TopCat.Presheaf.stalk (C := Ab)
        ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf y)) :
    letI := algebraStalkMap (U.ι ≫ sX) y
    letI := specStalkAlgebra ((U.ι ≫ sX) y)
    letI := opensStalkAlgebra sX U y
    letI := opensStalkIsoAlgebra U y
    letI := stalkAlgebra sX y.1
    haveI := isScalarTower_opensStalk_base sX U y
    haveI := isScalarTower_opensStalk sX U y
    formsGerm sX U n y m =
      formsBaseChange k (ToType ((Spec (.of k)).presheaf.stalk ((U.ι ≫ sX) y)))
        (ToType (U.toScheme.sheaf.presheaf.stalk y)) (X.presheaf.stalk y.1)
        (surjective_algebraMap_stalk_Spec _) n (formsStalkEquiv (U.ι ≫ sX) n y m) :=
  rfl

/-- `formsGerm` is semilinear along the germ map: the germ of `r • ω` goes to the germ of `r` in
`𝒪_{X,y}` times the image of the germ of `ω`. -/
theorem formsGerm_germ_smul (n : ℕ) {V : U.toScheme.Opens} {y : U.toScheme} (hy : y ∈ V)
    (r : Γ(U.toScheme, V)) (ω : Γ(Scheme.Hom.relativeDifferentialForms (U.ι ≫ sX) (n : ℤ), V)) :
    letI := stalkAlgebra sX y.1
    formsGerm sX U n y
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V y hy (r • ω)) =
      (U.stalkIso y).hom (U.toScheme.presheaf.germ V y hy r) • formsGerm sX U n y
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V y hy ω) := by
  let := algebraStalkMap (U.ι ≫ sX) y
  let := specStalkAlgebra ((U.ι ≫ sX) y)
  let := opensStalkAlgebra sX U y
  let := opensStalkIsoAlgebra U y
  let := stalkAlgebra sX y.1
  have := isScalarTower_opensStalk_base sX U y
  have := isScalarTower_opensStalk sX U y
  rw [formsGerm_apply, formsGerm_apply, MMP.Intersection.formsStalkEquiv_germ_smul,
    LinearMap.map_smul]
  exact (algebraMap_smul (X.presheaf.stalk y.1) _ _).symm

/-- `formsGerm` sends the germ of `dg₁ ∧ ⋯ ∧ dgₙ` to `d(g₁)_y ∧ ⋯ ∧ d(gₙ)_y` in
`Ω^n_{𝒪_{X,y}/k}`. -/
theorem formsGerm_germ_gen (n : ℕ) {V : U.toScheme.Opens} {y : U.toScheme} (hy : y ∈ V)
    (g : Fin n → Γ(U.toScheme, V)) :
    letI := stalkAlgebra sX y.1
    formsGerm sX U n y
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V y hy (Stacks.DeRham.FormsGenerators.gen (U.ι ≫ sX) V g)) =
      exteriorPower.ιMulti _ n fun i => KaehlerDifferential.D k (X.presheaf.stalk y.1)
        ((U.stalkIso y).hom (U.toScheme.presheaf.germ V y hy (g i))) := by
  let := algebraStalkMap (U.ι ≫ sX) y
  let := specStalkAlgebra ((U.ι ≫ sX) y)
  let := opensStalkAlgebra sX U y
  let := opensStalkIsoAlgebra U y
  let := stalkAlgebra sX y.1
  have := isScalarTower_opensStalk_base sX U y
  have := isScalarTower_opensStalk sX U y
  rw [formsGerm_apply, MMP.Intersection.formsStalkEquiv_germ_gen]
  exact formsBaseChange_ιMulti _ _

section FunctionField

variable [IsIntegral X]

/-- The image in `k(X)` of the germ in `𝒪_{X,y}` of a section `r` over `V ⊆ U` is
`X.germToFunctionField (U.ι ''ᵁ V) r`. -/
theorem algebraMap_stalkIso_germ {V : U.toScheme.Opens} {y : U.toScheme} (hy : y ∈ V)
    (r : Γ(U.toScheme, V)) :
    haveI : Nonempty (U.ι ''ᵁ V) := ⟨⟨y.1, y, hy, rfl⟩⟩
    algebraMap (X.presheaf.stalk y.1) X.functionField
        ((U.stalkIso y).hom (U.toScheme.presheaf.germ V y hy r)) =
      X.germToFunctionField (U.ι ''ᵁ V) r := by
  have : Nonempty (U.ι ''ᵁ V) := ⟨⟨y.1, y, hy, rfl⟩⟩
  have h' : (U.stalkIso y).hom (U.toScheme.presheaf.germ V y hy r) =
      X.presheaf.germ (U.ι ''ᵁ V) y.1 ⟨y, hy, rfl⟩ r := by
    rw [← U.germ_stalkIso_hom y hy]
    rfl
  rw [h']
  exact Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U.ι ''ᵁ V) _ r

/-- The germ `(Ω^n_{U/k})_y → Ω^n_{k(X)/k}`, through `Ω^n_{𝒪_{X,y}/k}`. -/
def formsGermFF (n : ℕ) (y : U.toScheme) :
    letI := functionFieldAlgebra sX
    ↑(TopCat.Presheaf.stalk (C := Ab)
        ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf y) →+
      ⋀[X.functionField]^n Ω[X.functionField⁄k] :=
  letI := stalkAlgebra sX y.1
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX y.1
  (topFormsMap k (X.presheaf.stalk y.1) X.functionField n).toAddMonoidHom.comp
    (formsGerm sX U n y)

/-- `formsGermFF` is `formsGerm` followed by `topFormsMap` to `k(X)`. -/
theorem formsGermFF_apply (n : ℕ) (y : U.toScheme)
    (m : ↑(TopCat.Presheaf.stalk (C := Ab)
        ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf y)) :
    letI := stalkAlgebra sX y.1
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX y.1
    formsGermFF sX U n y m =
      topFormsMap k (X.presheaf.stalk y.1) X.functionField n (formsGerm sX U n y m) :=
  rfl

/-- `formsGermFF` sends the germ of `r • ω` to the image of `r` in `k(X)` times the image of the
germ of `ω`. -/
theorem formsGermFF_germ_smul (n : ℕ) {V : U.toScheme.Opens} {y : U.toScheme} (hy : y ∈ V)
    (r : Γ(U.toScheme, V)) (ω : Γ(Scheme.Hom.relativeDifferentialForms (U.ι ≫ sX) (n : ℤ), V)) :
    haveI : Nonempty (U.ι ''ᵁ V) := ⟨⟨y.1, y, hy, rfl⟩⟩
    letI := functionFieldAlgebra sX
    formsGermFF sX U n y
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V y hy (r • ω)) =
      X.germToFunctionField (U.ι ''ᵁ V) r • formsGermFF sX U n y
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V y hy ω) := by
  let := stalkAlgebra sX y.1
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX y.1
  rw [formsGermFF_apply, formsGermFF_apply, formsGerm_germ_smul, LinearMap.map_smul,
    ← algebraMap_smul X.functionField, algebraMap_stalkIso_germ]

/-- `formsGermFF` sends the germ of `dg₁ ∧ ⋯ ∧ dgₙ` to `dg₁ ∧ ⋯ ∧ dgₙ` in `Ω^n_{k(X)/k}`, with the
`gᵢ` taken in `k(X)`. -/
theorem formsGermFF_germ_gen (n : ℕ) {V : U.toScheme.Opens} {y : U.toScheme} (hy : y ∈ V)
    (g : Fin n → Γ(U.toScheme, V)) :
    haveI : Nonempty (U.ι ''ᵁ V) := ⟨⟨y.1, y, hy, rfl⟩⟩
    letI := functionFieldAlgebra sX
    formsGermFF sX U n y
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V y hy (Stacks.DeRham.FormsGenerators.gen (U.ι ≫ sX) V g)) =
      exteriorPower.ιMulti _ n fun i =>
        KaehlerDifferential.D k X.functionField (X.germToFunctionField (U.ι ''ᵁ V) (g i)) := by
  let := stalkAlgebra sX y.1
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX y.1
  rw [formsGermFF_apply, formsGerm_germ_gen, topFormsMap_ιMulti]
  congr 1
  funext i
  rw [KaehlerDifferential.map_D, algebraMap_stalkIso_germ]

/-- **The image of a form in `Ω^n_{k(X)/k}` is locally constant**: for a section `τ` of
`Ω^n_{U/k}` over `V` and `y ∈ V`, the images of the germs of `τ` at the points near `y` agree. -/
theorem formsGermFF_eventually_eq (n : ℕ) {V : U.toScheme.Opens}
    (τ : Γ(Scheme.Hom.relativeDifferentialForms (U.ι ≫ sX) (n : ℤ), V)) {y : U.toScheme}
    (hy : y ∈ V) :
    ∃ (W : U.toScheme.Opens) (_ : y ∈ W) (hW : W ≤ V), ∀ z (hz : z ∈ W),
      formsGermFF sX U n z ((TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
          (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf) V z (hW hz) τ) = formsGermFF sX U n y ((TopCat.Presheaf.germ
              ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
              (n : ℤ)).val.presheaf) V y hy τ) := by
  let P : ↑(TopCat.Presheaf.stalk (C := Ab)
      ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
        (n : ℤ)).val.presheaf y) → Prop := fun m =>
    ∃ (W : U.toScheme.Opens) (hyW : y ∈ W)
      (τ' : Γ(Scheme.Hom.relativeDifferentialForms (U.ι ≫ sX) (n : ℤ), W)),
      (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf) W y hyW τ' = m ∧ ∀ z (hz : z ∈ W), formsGermFF sX U n z
              ((TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
              (U.ι ≫ sX)).exteriorAlgebra.piece
              (n : ℤ)).val.presheaf) W z hz τ') =
        formsGermFF sX U n y m
  have hP : ∀ m, P m := by
    refine formsStalk_induction (U.ι ≫ sX) n y ?_ ?_ ?_ ?_
    · refine ⟨⊤, trivial, 0, map_zero _, fun z hz => ?_⟩
      exact ((congrArg (formsGermFF sX U n z) (map_zero _)).trans (map_zero _)).trans
        (map_zero _).symm
    · rintro a b ⟨W₁, h₁, τ₁, e₁, c₁⟩ ⟨W₂, h₂, τ₂, e₂, c₂⟩
      obtain ⟨-, τ₁', -, g₁, -⟩ := exists_res_forms (U.ι ≫ sX) n (inf_le_left : W₁ ⊓ W₂ ≤ W₁) 0 τ₁
      obtain ⟨-, τ₂', -, g₂, -⟩ := exists_res_forms (U.ι ≫ sX) n (inf_le_right : W₁ ⊓ W₂ ≤ W₂) 0 τ₂
      refine ⟨W₁ ⊓ W₂, ⟨h₁, h₂⟩, τ₁' + τ₂', ?_, fun z hz => ?_⟩
      · exact (map_add _ _ _).trans (congrArg₂ (· + ·) ((g₁ y _).trans e₁) ((g₂ y _).trans e₂))
      · refine ((congrArg (formsGermFF sX U n z) (map_add _ _ _)).trans (map_add _ _ _)).trans ?_
        refine Eq.trans ?_ (map_add _ _ _).symm
        exact congrArg₂ (· + ·) ((congrArg _ (g₁ z hz)).trans (c₁ z _))
          ((congrArg _ (g₂ z hz)).trans (c₂ z _))
    · rintro V₀ hy₀ r ω ⟨W₁, h₁, τ₁, e₁, c₁⟩
      obtain ⟨W₂, hy₂, hW₂₁, hW₂₀, hagree⟩ :=
        exists_forall_germ_eq_of_germ_eq (U.ι ≫ sX) n y h₁ hy₀ τ₁ ω e₁
      obtain ⟨r', ω', hr', hω', hrω'⟩ := exists_res_forms (U.ι ≫ sX) n hW₂₀ r ω
      refine ⟨W₂, hy₂, r' • ω', hrω' y hy₂, fun z hz => ?_⟩
      have : Nonempty (U.ι ''ᵁ W₂) := ⟨⟨y.1, y, hy₂, rfl⟩⟩
      have : Nonempty (U.ι ''ᵁ V₀) := ⟨⟨y.1, y, hy₀, rfl⟩⟩
      have hff : X.germToFunctionField (U.ι ''ᵁ W₂) r' = X.germToFunctionField (U.ι ''ᵁ V₀) r := by
        rw [← algebraMap_stalkIso_germ U hy₂ r', ← algebraMap_stalkIso_germ U hy₀ r]
        exact congrArg _ (congrArg _ (hr' y hy₂))
      rw [formsGermFF_germ_smul sX U n hz, formsGermFF_germ_smul sX U n hy₀, hff]
      congr 1
      exact (congrArg _ ((hω' z hz).trans (hagree z hz).symm)).trans (c₁ z _)
    · intro V₀ hy₀ g
      refine ⟨V₀, hy₀, _, rfl, fun z hz => ?_⟩
      rw [formsGermFF_germ_gen sX U n hz, formsGermFF_germ_gen sX U n hy₀]
  obtain ⟨W, hyW, τ', hτ', hW⟩ := hP ((TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
      (U.ι ≫ sX)).exteriorAlgebra.piece
      (n : ℤ)).val.presheaf) V y hy τ)
  obtain ⟨W', hyW', hW'V, hW'W, hagree⟩ :=
    exists_forall_germ_eq_of_germ_eq (U.ι ≫ sX) n y hy hyW τ τ' hτ'.symm
  exact ⟨W', hyW', hW'V, fun z hz => (congrArg _ (hagree z hz)).trans (hW z _)⟩

/-- The image of a form in `Ω^n_{k(X)/k}` does not depend on the point. -/
theorem formsGermFF_eq_of_mem (n : ℕ) {V : U.toScheme.Opens}
    (τ : Γ(Scheme.Hom.relativeDifferentialForms (U.ι ≫ sX) (n : ℤ), V)) {y y' : U.toScheme}
    (hy : y ∈ V) (hy' : y' ∈ V) :
    formsGermFF sX U n y
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V y hy τ) =
      formsGermFF sX U n y'
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials (U.ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V y' hy' τ) := by
  have : Nonempty U := ⟨⟨y.1, y.2⟩⟩
  obtain ⟨W₁, h₁, hW₁, c₁⟩ := formsGermFF_eventually_eq sX U n τ hy
  obtain ⟨W₂, h₂, hW₂, c₂⟩ := formsGermFF_eventually_eq sX U n τ hy'
  obtain ⟨z, hz₁, hz₂⟩ := nonempty_preirreducible_inter W₁.isOpen W₂.isOpen ⟨y, h₁⟩ ⟨y', h₂⟩
  exact (c₁ z hz₁).symm.trans (c₂ z hz₂)

end FunctionField

end OpenForms

/-! ### Prime divisors lie in the smooth locus -/

section SmoothLocus

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- **Smoothness along a prime divisor.** For `X` locally of finite type over `k`, the generic
point of a prime divisor `Γ` is a smooth point exactly when `𝒪_{X,Γ}` is formally smooth over
`k`. -/
theorem PrimeDivisor.genericPoint_mem_smoothLocus_iff [LocallyOfFiniteType sX]
    (Γ : Mori.PrimeDivisor X) :
    Γ.genericPoint ∈ smoothLocus sX ↔
      letI := stalkAlgebra sX Γ.genericPoint
      Algebra.FormallySmooth k Γ.localRing := by
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [smoothLocus_eq_smoothLocus, Scheme.Hom.mem_smoothLocus]
  let f : CommRingCat.of k ⟶ (Spec (.of k)).presheaf.stalk (sX Γ.genericPoint) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ _ (Opens.mem_top _)
  have hiso : IsIso f := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨RingHom.injective _, surjective_algebraMap_stalk_Spec _⟩
  have hcomp : f ≫ sX.stalkMap Γ.genericPoint =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ Γ.genericPoint (Opens.mem_top _) := by
    erw [Category.assoc, Scheme.Hom.germ_stalkMap sX ⊤ Γ.genericPoint (Opens.mem_top _)]
    rfl
  rw [← RingHom.FormallySmooth.respectsIso.cancel_left_isIso f, ← CommRingCat.hom_comp, hcomp]
  rfl

/-- **The generic point of a prime divisor is a smooth point.** On a normal variety over a perfect
field, `𝒪_{X,Γ}` is a discrete valuation ring, hence regular, hence formally smooth over `k`. -/
@[mmp "lem_mmp_foundation_normal_prime_divisor_smooth_generic_point"]
theorem PrimeDivisor.genericPoint_mem_smoothLocus [PerfectField k] (hX : IsNormalVariety k sX)
    (Γ : Mori.PrimeDivisor X) : Γ.genericPoint ∈ smoothLocus sX := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNormal X := hX.2
  exact (PrimeDivisor.genericPoint_mem_smoothLocus_iff Γ).mpr
    (Γ.formallySmooth_localRing (sX := sX)).1

end SmoothLocus

/-! ### Sections of the divisorial sheaf near a prime divisor -/

section Divisorial

open Opposite

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The generic point of a prime divisor lies in its support. -/
theorem PrimeDivisor.genericPoint_mem_support' (Γ : Mori.PrimeDivisor X) :
    Γ.genericPoint ∈ Γ.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure (Set.mem_singleton _)

/-- For a local equation `ψ` of `D` on `W`, the section `ψ⁻¹` of `𝒪_X(D)` over `W`. -/
def Divisor.invSectionOfLocalEquation {D : Divisor X} {W : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (h : D.IsLocalEquation W ψ) : D.divisorialSubmodule W :=
  ⟨fun Z => ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1, fun E hE =>
    Or.inr (by rw [E.valuation_component, PrimeDivisor.ord_inv, h E hE])⟩

/-- **Sections of `𝒪_X(D)` near a prime divisor.** If `ψ` is a local equation of `D` on `W ∋ η_Γ`,
every section `h` of `𝒪_X(D)` near `η_Γ` is `a · ψ⁻¹` near `η_Γ`, for a regular function `a`:
`h ψ` has order `≥ 0` along `Γ`, hence lies in `𝒪_{X,Γ}`. -/
theorem Divisor.exists_eq_smul_invSection [IsIntegral X] {D : Divisor X} {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ) (Γ : Mori.PrimeDivisor X)
    (hΓ : Γ.genericPoint ∈ W) {W₀ : X.Opens} (hΓ₀ : Γ.genericPoint ∈ W₀)
    (h : D.divisorialSubmodule W₀) :
    ∃ (W' : X.Opens) (_ : Γ.genericPoint ∈ W') (hW'₀ : W' ≤ W₀) (_ : W' ≤ W) (a : Γ(X, W')),
      ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W'},
        h.1 ⟨Z.1, hW'₀ Z.2⟩ = X.presheaf.germ W' _ Z.2 a *
          ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 := by
  have := subsingleton_irreducibleComponents X
  have hne : (Γ.support ∩ (W₀ : Set X)).Nonempty :=
    ⟨Γ.genericPoint, PrimeDivisor.genericPoint_mem_support' Γ, hΓ₀⟩
  have hZ₀ : componentGenericPoint X Γ.component ∈ W₀ := Γ.componentGenericPoint_mem_of_nonempty hne
  set f := h.1 ⟨Γ.component, hZ₀⟩ with hf
  have h1 : Γ.OrdGE (-D.coeff Γ) f := h.2 Γ hne
  have h2 : Γ.OrdGE (D.coeff Γ) ((ψ : RationalFunctions X) Γ.component) :=
    Or.inr (by
      rw [Γ.valuation_component, hψ Γ
          ⟨Γ.genericPoint, PrimeDivisor.genericPoint_mem_support' Γ, hΓ⟩])
  have h3 : Γ.OrdGE 0 (f * (ψ : RationalFunctions X) Γ.component) := by
    simpa only [neg_add_cancel] using h1.mul h2
  obtain ⟨b, hb⟩ : ∃ b : Γ.localRing, Γ.toComponent.hom b = f *
      (ψ : RationalFunctions X) Γ.component := by
    rcases h3 with h0 | h3
    · exact ⟨0, by rw [map_zero, h0]⟩
    · exact Γ.exists_toComponent_eq_of_one_le_valuation (by simpa using h3)
  obtain ⟨W', hW', hΓW', a, ha⟩ := X.presheaf.exists_le_germ_eq b (V := W₀ ⊓ W) ⟨hΓ₀, hΓ⟩
  refine ⟨W', hΓW', hW'.trans inf_le_left, hW'.trans inf_le_right, a, ?_⟩
  rintro ⟨Z, hZ⟩
  obtain rfl : Z = Γ.component := Subsingleton.elim _ _
  have hga : X.presheaf.germ W' _ hZ a = f * (ψ : RationalFunctions X) Γ.component := by
    rw [← hb, ← ha]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hΓW' _ a).symm
  rw [hga, mul_assoc, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Pi.one_apply, mul_one]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Two prime divisors whose generic points specialize to one another are equal. -/
theorem PrimeDivisor.eq_of_genericPoint_specializes {E Γ : Mori.PrimeDivisor X}
    (h : E.genericPoint ⤳ Γ.genericPoint) : E = Γ := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  by_contra hne
  by_cases h' : Γ.genericPoint ⤳ E.genericPoint
  · exact hne (h.antisymm h').eq
  have hlt : Γ.genericPoint < E.genericPoint := lt_of_le_not_ge h h'
  have := Order.coheight_strictAnti hlt (by rw [E.coheight_genericPoint]; decide)
  rw [E.coheight_genericPoint, Γ.coheight_genericPoint] at this
  exact lt_irrefl _ this

/-- Along a prime divisor `Γ` of an integral normal scheme there is a unit of `K(X)` of order
one. -/
theorem PrimeDivisor.exists_ord_eq_one [IsIntegral X] (Γ : Mori.PrimeDivisor X) :
    ∃ φ : (RationalFunctions X)ˣ, Γ.ord φ = 1 := by
  have := Γ.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Γ.localRing
  set g := algebraMap Γ.localRing X.functionField ϖ
  have hg : g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Γ.localRing X.functionField)).mpr hϖ.ne_zero
  refine ⟨Units.map (RingHom.pi functionFieldToComponent).toMonoidHom (Units.mk0 g hg), ?_⟩
  refine Γ.ord_eq_one_of_irreducible hϖ ?_
  change _ = (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom ϖ
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- **Divisors are Cartier at codimension-one points.** On a quasi-compact integral normal
scheme, a divisor `D` has a local equation on an open neighbourhood of the generic point of any
prime divisor `Γ`: a power `ψ` of a uniformizer along `Γ`, on the complement of the finitely many
other prime divisors along which `D` and `div(ψ)` differ. -/
theorem Divisor.exists_isLocalEquation [IsIntegral X] [CompactSpace X] (D : Divisor X)
    (Γ : Mori.PrimeDivisor X) :
    ∃ (W : X.Opens) (ψ : (RationalFunctions X)ˣ), Γ.genericPoint ∈ W ∧ D.IsLocalEquation W ψ := by
  classical
  obtain ⟨φ, hφ⟩ := PrimeDivisor.exists_ord_eq_one Γ
  set ψ := φ ^ D.coeff Γ
  have hψΓ : Γ.ord ψ = D.coeff Γ := by
    rw [PrimeDivisor.ord_zpow, hφ, smul_eq_mul, mul_one]
  set B : Set (Mori.PrimeDivisor X) := {E | D.coeff E ≠ E.ord ψ}
  have hB : B.Finite := by
    refine ((D.support.finite_toSet).union (finite_ord_ne_zero ψ)).subset fun E hE => ?_
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not,
      Set.mem_ofPred_eq] at h
    exact hE (by rw [DivisorWithCoeffs.coeff_apply, h.1, h.2])
  let B' := {E ∈ B | E ≠ Γ}
  have hB' : B'.Finite := hB.subset fun E hE => hE.1
  have hclosed : IsClosed (⋃ E ∈ B', E.support) :=
    hB'.isClosed_biUnion fun E _ => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isClosed_closure
  refine ⟨⟨(⋃ E ∈ B', E.support)ᶜ, hclosed.isOpen_compl⟩, ψ, ?_, ?_⟩
  · simp only [TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro E hE hΓE
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hΓE
    exact hE.2 (PrimeDivisor.eq_of_genericPoint_specializes hΓE)
  · rintro E ⟨x, hxE, hx⟩
    by_cases hEΓ : E = Γ
    · rw [hEΓ, hψΓ]
    by_contra hne
    exact hx (Set.mem_iUnion₂.mpr ⟨E, ⟨hne, hEΓ⟩, hxE⟩)

/-- The section `ψ⁻¹` of `𝒪_X(D)|_U` over `U ∩ W`, for a local equation `ψ` of `D` on `W`. -/
def Divisor.restrictInvSection {D : Divisor X} {W : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (h : D.IsLocalEquation W ψ) (U : X.Opens) : Γ(D.divisorialSheaf.restrict U.ι, U.ι ⁻¹ᵁ W) :=
  Divisor.invSectionOfLocalEquation (h.mono (Scheme.Hom.image_preimage_le U.ι W))

/-- `Divisor.exists_eq_smul_invSection` on an open `U`. -/
theorem Divisor.exists_restrict_eq_smul [IsIntegral X] {D : Divisor X} {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ) (U : X.Opens)
    (Γ : Mori.PrimeDivisor X) (hsm : Γ.genericPoint ∈ U) (hΓW : Γ.genericPoint ∈ W)
    {V₀ : U.toScheme.Opens} (hy₀ : (⟨Γ.genericPoint, hsm⟩ : U.toScheme) ∈ V₀)
    (h : Γ(D.divisorialSheaf.restrict U.ι, V₀)) :
    ∃ (V' : U.toScheme.Opens) (_ : (⟨Γ.genericPoint, hsm⟩ : U.toScheme) ∈ V') (h₀ : V' ≤ V₀)
      (hW : V' ≤ U.ι ⁻¹ᵁ W) (a : Γ(U.toScheme, V')),
      (D.divisorialSheaf.restrict U.ι).presheaf.map (homOfLE h₀).op h =
        a • (D.divisorialSheaf.restrict U.ι).presheaf.map (homOfLE hW).op
          (Divisor.restrictInvSection hψ U) := by
  obtain ⟨W', hΓW', hW'₀, hW'W, a', ha'⟩ := Divisor.exists_eq_smul_invSection hψ Γ hΓW
    (W₀ := U.ι ''ᵁ V₀) ⟨_, hy₀, rfl⟩ h
  refine ⟨U.ι ⁻¹ᵁ W', hΓW', ?_, fun z hz => hW'W hz,
    X.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le U.ι W')).op a', ?_⟩
  · exact (Scheme.Hom.image_le_image_iff U.ι _ _).mp
      ((Scheme.Hom.image_preimage_le U.ι W').trans hW'₀)
  · apply Subtype.ext
    funext Z
    have hZ : componentGenericPoint X Z.1 ∈ W' := Scheme.Hom.image_preimage_le U.ι W' Z.2
    refine (ha' ⟨Z.1, hZ⟩).trans ?_
    refine (congrArg (· * _) (TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE (Scheme.Hom.image_preimage_le U.ι W')) _ Z.2 a').symm).trans ?_
    have hsm' := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι D.divisorialSheaf
      (U.ι ⁻¹ᵁ W') (X.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le U.ι W')).op a')
      ((D.divisorialSheaf.restrict U.ι).presheaf.map (homOfLE (fun z hz => hW'W hz)).op
        (Divisor.restrictInvSection hψ U))
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv] at hsm'
    refine Eq.trans ?_ (congrArg (fun s : Γ(D.divisorialSheaf, U.ι ''ᵁ U.ι ⁻¹ᵁ W') =>
      (s : D.divisorialSubmodule _).1 Z) hsm').symm
    rfl

/-- Two local equations `ψ, ψ'` of `D` differ by a regular function `c` on a nonempty open `V`
of `U`: `ψ'⁻¹ = c ψ⁻¹` on `V`, and `c = ψ/ψ'` in `k(X)`. -/
theorem Divisor.exists_restrict_invSection_eq_smul [IsIntegral X] {D : Divisor X}
    {W W' : X.Opens} {ψ ψ' : (RationalFunctions X)ˣ} (hψ : D.IsLocalEquation W ψ)
    (hψ' : D.IsLocalEquation W' ψ') (U : X.Opens) (hne : ((U ⊓ W ⊓ W' : X.Opens) : Set X).Nonempty)
    (Z₀ : irreducibleComponents X) :
    ∃ (V : U.toScheme.Opens) (y : U.toScheme) (hy : y ∈ V) (h₁ : V ≤ U.ι ⁻¹ᵁ W)
      (h₂ : V ≤ U.ι ⁻¹ᵁ W') (c : Γ(U.toScheme, V)),
      (D.divisorialSheaf.restrict U.ι).presheaf.map (homOfLE h₂).op
          (Divisor.restrictInvSection hψ' U) =
        c • (D.divisorialSheaf.restrict U.ι).presheaf.map (homOfLE h₁).op
          (Divisor.restrictInvSection hψ U) ∧
      haveI : Nonempty (U.ι ''ᵁ V) := ⟨⟨y.1, y, hy, rfl⟩⟩
      X.germToFunctionField (U.ι ''ᵁ V) c = (componentToFunctionField Z₀).hom
        (((ψ * ψ'⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z₀) := by
  have := subsingleton_irreducibleComponents X
  have huniv : (Z₀.1 : Set X) = Set.univ :=
    (irreducibleComponents_eq_singleton (X := X) ▸ Z₀.2 : Z₀.1 ∈ ({Set.univ} : Set (Set X)))
  obtain ⟨Wc, hWc, c', hc'⟩ := X.presheaf.exists_germ_eq
    (((ψ * ψ'⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z₀)
  have hmem : ∀ O : X.Opens, (O : Set X).Nonempty → componentGenericPoint X Z₀ ∈ O := fun O hO =>
    (genericPoint_mem_iff Z₀ O).mpr (by rw [huniv, Set.inter_univ]; exact hO)
  have hp : componentGenericPoint X Z₀ ∈ U ⊓ W ⊓ W' := hmem _ hne
  set y : U.toScheme := ⟨componentGenericPoint X Z₀, hp.1.1⟩
  let V : U.toScheme.Opens := U.ι ⁻¹ᵁ (W ⊓ W' ⊓ Wc)
  have hyV : y ∈ V := ⟨⟨hp.1.2, hp.2⟩, hWc⟩
  have hVc : U.ι ''ᵁ V ≤ Wc := (Scheme.Hom.image_preimage_le U.ι _).trans inf_le_right
  refine ⟨V, y, hyV, fun z hz => hz.1.1, fun z hz => hz.1.2,
    X.presheaf.map (homOfLE hVc).op c', ?_, ?_⟩
  · apply Subtype.ext
    funext Z
    obtain ⟨Z, hZ⟩ := Z
    obtain rfl : Z = Z₀ := Subsingleton.elim _ _
    have hsm' := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι D.divisorialSheaf V
      (X.presheaf.map (homOfLE hVc).op c')
      ((D.divisorialSheaf.restrict U.ι).presheaf.map (homOfLE
          (fun z hz => hz.1.1 : V ≤ U.ι ⁻¹ᵁ W)).op
        (Divisor.restrictInvSection hψ U))
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv] at hsm'
    refine Eq.trans ?_ (congrArg (fun s : Γ(D.divisorialSheaf, U.ι ''ᵁ V) =>
      (s : D.divisorialSubmodule _).1 ⟨Z, hZ⟩) hsm').symm
    change ((ψ'⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z =
      X.presheaf.germ (U.ι ''ᵁ V) _ hZ (X.presheaf.map (homOfLE hVc).op c') *
        ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z
    rw [TopCat.Presheaf.germ_res_apply, hc', ← Pi.mul_apply, ← Units.val_mul, mul_comm ψ,
      mul_assoc, mul_inv_cancel, mul_one]
  · have : Nonempty (U.ι ''ᵁ V) := ⟨⟨y.1, y, hyV, rfl⟩⟩
    rw [← hc']
    change X.presheaf.germ _ _ _ (X.presheaf.map (homOfLE hVc).op c') =
      (X.presheaf.germ Wc _ hWc ≫ X.presheaf.stalkSpecializes _).hom c'
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_stalkSpecializes]

end Divisorial

/-! ### The generator of `ω_X` along a prime divisor -/

section Generator

/-- A morphism of `𝒪_Y`-modules commutes with restriction of sections. -/
theorem modulesHom_app_map {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) {V W : Y.Opens}
    (h : W ≤ V) (x : Γ(M, V)) :
    φ.app W (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app V x) := by
  have := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x
  simpa only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] using this

/-- For an isomorphism `e` of `𝒪_Y`-modules, `e.hom.app V (e.inv.app V x) = x`. -/
theorem modulesIso_hom_app_inv_app {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N) (V : Y.Opens)
    (x : Γ(N, V)) : e.hom.app V (e.inv.app V x) = x := by
  have := congrArg (fun f => (Scheme.Modules.Hom.app f V).hom x) e.inv_hom_id
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply] at this
  exact this.trans rfl

/-- If `e⁻¹ t` restricts to `c • s` on `V'`, then `t` restricts to `c • e s` on `V'`. -/
theorem modulesIso_map_eq_smul {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    {V₀ V₁ V' : Y.Opens} (h₀ : V' ≤ V₀) (h₁ : V' ≤ V₁) (t : Γ(N, V₀)) (s : Γ(M, V₁))
    (c : Γ(Y, V'))
    (hc : M.presheaf.map (homOfLE h₀).op (e.inv.app V₀ t) = c • M.presheaf.map (homOfLE h₁).op s) :
    N.presheaf.map (homOfLE h₀).op t = c • N.presheaf.map (homOfLE h₁).op (e.hom.app V₁ s) := by
  have e2 := congrArg (e.hom.app V') hc
  rwa [modulesHom_app_map, modulesIso_hom_app_inv_app, Scheme.Modules.Hom.app_smul,
    modulesHom_app_map] at e2

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- **The image of the local generator generates `Ω^n` at `Γ`.** For a canonical divisor `K` with
local equation `ψ` on `W ∋ η_Γ`, the form corresponding to the section `ψ⁻¹` of `𝒪_X(K)` under
`𝒪_X(K)|_{X_sm} ≅ ω_{X_sm}` generates `Ω^n_{𝒪_{X,Γ}/k}`. -/
theorem span_formsGerm_invSection_eq_top {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {W : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : K.IsLocalEquation W ψ) (Γ : Mori.PrimeDivisor X) (hsm : Γ.genericPoint ∈ smoothLocus sX)
    (hΓW : Γ.genericPoint ∈ W) :
    letI := stalkAlgebra sX Γ.genericPoint
    Submodule.span Γ.localRing {(formsGerm sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm⟩
      (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
          ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf ((smoothLocus sX).ι ⁻¹ᵁ W) ⟨Γ.genericPoint, hsm⟩ hΓW
        (hK.iso.hom.app ((smoothLocus sX).ι ⁻¹ᵁ W)
          (Divisor.restrictInvSection hψ (smoothLocus sX)))))} = ⊤ := by
  let := stalkAlgebra sX Γ.genericPoint
  rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span _ n
    (hs := KaehlerDifferential.span_range_derivation k Γ.localRing), Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  choose b hb using fun i => ha (Set.mem_range_self i)
  obtain ⟨V₀, hy₀, g, hg⟩ := MMP.Intersection.exists_germ_eq_of_fin
    (Y := (smoothLocus sX).toScheme) ⟨Γ.genericPoint, hsm⟩
    (fun i => ((smoothLocus sX).stalkIso ⟨Γ.genericPoint, hsm⟩).inv (b i))
  have e1 : exteriorPower.ιMulti _ n a = formsGerm sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm⟩
      (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
          ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V₀ ⟨Γ.genericPoint, hsm⟩ hy₀
        (Stacks.DeRham.FormsGenerators.gen ((smoothLocus sX).ι ≫ sX) V₀ g)) := by
    refine Eq.trans ?_ (formsGerm_germ_gen sX (smoothLocus sX) n hy₀ g).symm
    refine congrArg (exteriorPower.ιMulti _ n) (funext fun i => ?_)
    exact (hb i).symm.trans (congrArg (KaehlerDifferential.D k _)
      ((Iso.inv_hom_id_apply _ _).symm.trans (congrArg _ (hg i).symm)))
  obtain ⟨V', hy', h₀, hW, c, hc⟩ := Divisor.exists_restrict_eq_smul hψ (smoothLocus sX) Γ hsm hΓW
    hy₀ (hK.iso.inv.app V₀ (Stacks.DeRham.FormsGenerators.gen ((smoothLocus sX).ι ≫ sX) V₀ g))
  have e3 := modulesIso_map_eq_smul hK.iso h₀ hW
    (Stacks.DeRham.FormsGenerators.gen ((smoothLocus sX).ι ≫ sX) V₀ g) _ c hc
  have e4 : formsGerm sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm⟩
      (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
          ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf V₀ ⟨Γ.genericPoint, hsm⟩ hy₀
        (Stacks.DeRham.FormsGenerators.gen ((smoothLocus sX).ι ≫ sX) V₀ g)) =
      ((smoothLocus sX).stalkIso ⟨Γ.genericPoint, hsm⟩).hom
          ((smoothLocus sX).toScheme.presheaf.germ V' ⟨Γ.genericPoint, hsm⟩ hy' c) •
        formsGerm sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm⟩
          (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
              ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
              (n : ℤ)).val.presheaf ((smoothLocus sX).ι ⁻¹ᵁ W) ⟨Γ.genericPoint, hsm⟩ hΓW
            (hK.iso.hom.app ((smoothLocus sX).ι ⁻¹ᵁ W)
              (Divisor.restrictInvSection hψ (smoothLocus sX)))) := by
    refine (congrArg (formsGerm sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm⟩)
      ((TopCat.Presheaf.germ_res_apply _ (homOfLE h₀) _ hy' _).symm.trans
        (congrArg (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
            ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
            (n : ℤ)).val.presheaf V' ⟨Γ.genericPoint, hsm⟩ hy') e3))).trans ?_
    refine (formsGerm_germ_smul sX (smoothLocus sX) n hy' c _).trans ?_
    exact congrArg (_ • ·) (congrArg (formsGerm sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm⟩)
      (TopCat.Presheaf.germ_res_apply _ (homOfLE hW) _ hy' _))
  exact Submodule.mem_span_singleton.mpr ⟨_, e4.symm.trans e1.symm⟩

/-- **Comparing the generators along two prime divisors.** For local equations `ψ, ψ'` of a
canonical divisor at `Γ, Γ'`, the images in `Ω^n_{k(X)/k}` of the forms corresponding to `ψ⁻¹` and
`ψ'⁻¹` differ by the factor `ψ/ψ'`. -/
theorem formsGermFF_invSection_eq_smul {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {W W' : X.Opens} {ψ ψ' : (RationalFunctions X)ˣ}
    (hψ : K.IsLocalEquation W ψ) (hψ' : K.IsLocalEquation W' ψ') (Γ Γ' : Mori.PrimeDivisor X)
    (hsm : Γ.genericPoint ∈ smoothLocus sX) (hsm' : Γ'.genericPoint ∈ smoothLocus sX)
    (hΓW : Γ.genericPoint ∈ W) (hΓW' : Γ'.genericPoint ∈ W') :
    letI := functionFieldAlgebra sX
    formsGermFF sX (smoothLocus sX) n ⟨Γ'.genericPoint, hsm'⟩
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
            ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
            (n : ℤ)).val.presheaf ((smoothLocus sX).ι ⁻¹ᵁ W') ⟨Γ'.genericPoint, hsm'⟩ hΓW'
          (hK.iso.hom.app ((smoothLocus sX).ι ⁻¹ᵁ W')
            (Divisor.restrictInvSection hψ' (smoothLocus sX)))) =
      (componentToFunctionField Γ.component).hom
          (((ψ * ψ'⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Γ.component) •
        formsGermFF sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm⟩
          (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
              ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
              (n : ℤ)).val.presheaf ((smoothLocus sX).ι ⁻¹ᵁ W) ⟨Γ.genericPoint, hsm⟩ hΓW
            (hK.iso.hom.app ((smoothLocus sX).ι ⁻¹ᵁ W)
              (Divisor.restrictInvSection hψ (smoothLocus sX)))) := by
  let := functionFieldAlgebra sX
  have hgen : ∀ {x : X} (O : X.Opens), x ∈ O → genericPoint X ∈ O := fun O h =>
    ((genericPoint_spec X).specializes trivial).mem_open O.isOpen h
  have hne : (((smoothLocus sX) ⊓ W ⊓ W' : X.Opens) : Set X).Nonempty :=
    ⟨genericPoint X, ⟨hgen _ hsm, hgen _ hΓW⟩, hgen _ hΓW'⟩
  obtain ⟨V, y, hy, h₁, h₂, c, hc, hcval⟩ :=
    Divisor.exists_restrict_invSection_eq_smul hψ hψ' (smoothLocus sX) hne Γ.component
  have e3 := modulesIso_map_eq_smul hK.iso h₂ h₁
    (hK.iso.hom.app ((smoothLocus sX).ι ⁻¹ᵁ W') (Divisor.restrictInvSection hψ' (smoothLocus sX)))
    (Divisor.restrictInvSection hψ (smoothLocus sX)) c
    (Eq.trans (congrArg _ (modulesIso_hom_app_inv_app hK.iso.symm _ _)) hc)
  have : Nonempty ((smoothLocus sX).ι ''ᵁ V) := ⟨⟨y.1, y, hy, rfl⟩⟩
  refine (formsGermFF_eq_of_mem sX (smoothLocus sX) n _ hΓW' (h₂ hy)).trans ?_
  refine (congrArg (formsGermFF sX (smoothLocus sX) n y)
      ((TopCat.Presheaf.germ_res_apply _ (homOfLE h₂) _ hy _).symm.trans
        (congrArg (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
            ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
            (n : ℤ)).val.presheaf V y hy) e3))).trans ?_
  refine (formsGermFF_germ_smul sX (smoothLocus sX) n hy c _).trans ?_
  refine congrArg₂ (· • ·) hcval ?_
  refine (congrArg (formsGermFF sX (smoothLocus sX) n y)
      (TopCat.Presheaf.germ_res_apply _ (homOfLE h₁) _ hy _)).trans ?_
  exact formsGermFF_eq_of_mem sX (smoothLocus sX) n _ (h₁ hy) hΓW

end Generator

/-! ### Canonical divisors are divisors of forms -/

section SmoothInCodimOne

/-- In a preorder of finite Krull dimension `n ≠ 0` some element has coheight one. -/
private theorem exists_coheight_eq_one_of_krullDim_eq {α : Type*} [Preorder α] {n : ℕ}
    (hn : Order.krullDim α = n) (h : n ≠ 0) : ∃ x : α, Order.coheight x = 1 := by
  have hfin : ∀ x : α, Order.coheight x < ⊤ := fun x => by
    have := Order.coheight_le_krullDim x
    rw [hn] at this
    exact lt_of_le_of_lt (WithBot.coe_le_coe.mp this) (ENat.natCast_lt_top n)
  -- descend from a point of coheight `m + 1` along a chain until the coheight is one
  have H : ∀ m : ℕ, ∀ x : α, Order.coheight x = m + 1 → ∃ y : α, Order.coheight y = 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hx
      rcases m with _ | m
      · exact ⟨x, by simpa using hx⟩
      obtain ⟨p, rfl, hpl⟩ := Order.exists_series_of_le_coheight x (n := 2)
        (by rw [hx]; exact_mod_cast (by omega : 2 ≤ m + 1 + 1))
      set a := p ⟨1, by omega⟩
      have h01 : p.head < a := p.strictMono (show (0 : ℕ) < 1 by omega)
      have h12 : a < p ⟨2, by omega⟩ := p.strictMono (show (1 : ℕ) < 2 by omega)
      have hlt := Order.coheight_strictAnti h01 (hfin _)
      have hpos : Order.coheight a ≠ 0 := by
        rw [Ne, Order.coheight_eq_zero]
        exact fun hmax => hmax.not_lt h12
      obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (hfin a).ne
      obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact hpos hc.symm)
      rw [hx, ← hc] at hlt
      have : c + 1 < m + 1 + 1 := by exact_mod_cast hlt
      exact ih c (by omega) a (by rw [← hc]; push_cast; rfl)
  obtain ⟨x, hx⟩ : ∃ x : α, Order.coheight x ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    have : Order.krullDim α ≤ 0 := by
      rw [Order.krullDim_eq_iSup_coheight]
      exact iSup_le fun x => by simp [hc x]
    rw [hn] at this
    exact h (by exact_mod_cast this.antisymm (by positivity))
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (hfin x).ne
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact hx hc.symm)
  exact H c x (by rw [← hc]; push_cast; rfl)

/-- A scheme of dimension `n ≠ 0` has a prime divisor: a point of coheight one. -/
theorem nonempty_primeDivisor_of_topologicalKrullDim_eq {X : Scheme.{u}} {n : ℕ}
    (hn : topologicalKrullDim X = n) (h : n ≠ 0) : Nonempty (Mori.PrimeDivisor X) := by
  let _ : PartialOrder X := specializationOrder X
  have hn' : Order.krullDim X = n := by
    rw [← hn]
    exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm
  obtain ⟨x, hx⟩ := exists_coheight_eq_one_of_krullDim_eq hn' h
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- If `b' = c • b` and `g' c = g`, then `g' • b'^{⊗1} = g • b^{⊗1}`. -/
theorem ZTensorPower.smul_basis_one_eq_of_eq_smul {K L : Type*} [Field K] [AddCommGroup L]
    [Module K L] {b b' : Module.Basis Unit K L} {c g g' : K} (h : b' () = c • b ())
    (hc : g' * c = g) :
    g' • ZTensorPower.basis b' 1 () = g • ZTensorPower.basis b 1 () := by
  rw [ZTensorPower.basis_apply_of_eq_smul h, zpow_one, smul_smul, hc]

omit [IsLocallyNoetherian X] in
/-- **The line of top forms.** On a normal variety `X` of dimension `n` over `k` whose prime
divisors have smooth generic points, `Ω^n_{k(X)/k}` is a line: if `n ≠ 0` there is a prime divisor
`Γ`, so `k(X)`, a localization of the formally smooth `𝒪_{X,Γ}`, is formally smooth over `k`,
`H₁(L_{k(X)/k}) = 0` and `dim Ω_{k(X)/k} = trdeg_k k(X) = n`. -/
theorem finrank_topForms_functionField_eq_one (hX : IsNormalVariety k sX)
    (hsm : ∀ Γ : Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) :
    letI := functionFieldAlgebra sX
    Module.finrank X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]) = 1 := by
  let := functionFieldAlgebra sX
  rcases eq_or_ne n 0 with rfl | h0
  · exact ((exteriorPower.zeroEquiv _ _).finrank_eq).trans (Module.finrank_self _)
  obtain ⟨Γ⟩ := nonempty_primeDivisor_of_topologicalKrullDim_eq hn h0
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  let := stalkAlgebra sX Γ.genericPoint
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have := (PrimeDivisor.genericPoint_mem_smoothLocus_iff Γ).mp (hsm Γ)
  have : Algebra.FormallySmooth Γ.localRing X.functionField :=
    .of_isLocalization (nonZeroDivisors Γ.localRing)
  have : Algebra.FormallySmooth k X.functionField := .comp k Γ.localRing X.functionField
  have := essFiniteType_functionField (sX := sX)
  have h := trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k X.functionField
  have : FiniteDimensional X.functionField Ω[X.functionField⁄k] := h.1
  have hK : Module.finrank X.functionField Ω[X.functionField⁄k] = n := by
    have h2 := h.2.2
    rw [Module.finrank_zero_of_subsingleton (M := Algebra.H1Cotangent k X.functionField),
      Nat.cast_zero, sub_zero] at h2
    rw [← toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn]
    exact_mod_cast h2.symm
  rw [exteriorPower.finrank_eq, hK, Nat.choose_self]

/-- **A canonical divisor is the divisor of a rational top form.** On a normal variety `X` of
dimension `n` over `k` whose prime divisors have their generic points in the smooth locus, a
canonical divisor `K` (`𝒪_X(K)|_{X_sm} ≅ ω_{X_sm}`) is `div(ω)` for a nonzero rational `n`-form
`ω`: `ord_Γ(ω) = coeff_Γ(K)` for every prime divisor `Γ`. Along `Γ`, let `ψ_Γ` be a local
equation of `K` and `b_Γ ∈ Ω^n_{k(X)/k}` the image of the form corresponding to the section
`ψ_Γ⁻¹` of `𝒪_X(K)`; it comes from a generator of `Ω^n_{𝒪_{X,Γ}/k}`, so `ω_Γ = ψ_Γ b_Γ` has
`ord_Γ(ω_Γ) = v_Γ(ψ_Γ) = coeff_Γ(K)`. Comparing on the smooth locus, `b_{Γ'} = (ψ_Γ/ψ_{Γ'}) b_Γ`,
so `ω_Γ` does not depend on `Γ`. -/
theorem IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus (hX : IsNormalVariety k sX)
    (hsm : ∀ Γ : Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ := by
  classical
  have hn := hK.topologicalKrullDim_eq
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : CompactSpace X := by
    have := hX.1
    exact QuasiCompact.compactSpace_of_compactSpace sX
  let := functionFieldAlgebra sX
  have h1 := finrank_topForms_functionField_eq_one hX hsm hn
  have : Nontrivial (⋀[X.functionField]^n Ω[X.functionField⁄k]) :=
    Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  -- local data along each prime divisor
  choose W ψ hΓW hψ using fun Γ : Mori.PrimeDivisor X => Divisor.exists_isLocalEquation K Γ
  -- the image `b Γ` in `Ω^n_{k(X)/k}` of the form corresponding to `ψ_Γ⁻¹`
  let b : Mori.PrimeDivisor X → ⋀[X.functionField]^n Ω[X.functionField⁄k] := fun Γ =>
    formsGermFF sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm Γ⟩
      (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
          ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf ((smoothLocus sX).ι ⁻¹ᵁ W Γ) ⟨Γ.genericPoint, hsm Γ⟩ (hΓW Γ)
        (hK.iso.hom.app ((smoothLocus sX).ι ⁻¹ᵁ W Γ)
          (Divisor.restrictInvSection (hψ Γ) (smoothLocus sX))))
  let g : Mori.PrimeDivisor X → X.functionField := fun Γ =>
    (componentToFunctionField Γ.component).hom (((ψ Γ : (RationalFunctions X)ˣ) :
      RationalFunctions X) Γ.component)
  have hg0 : ∀ Γ, g Γ ≠ 0 := fun Γ =>
    left_ne_zero_of_mul_eq_one (componentToFunctionField_mul_inv (ψ Γ) Γ.component Γ.component)
  -- the generators
  have hσ : ∀ Γ : Mori.PrimeDivisor X,
      letI := stalkAlgebra sX Γ.genericPoint
      Submodule.span Γ.localRing {(formsGerm sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm Γ⟩
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
            ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
            (n : ℤ)).val.presheaf ((smoothLocus sX).ι ⁻¹ᵁ W Γ) ⟨Γ.genericPoint, hsm Γ⟩ (hΓW Γ)
          (hK.iso.hom.app ((smoothLocus sX).ι ⁻¹ᵁ W Γ)
            (Divisor.restrictInvSection (hψ Γ) (smoothLocus sX)))))} = ⊤ := fun Γ =>
    span_formsGerm_invSection_eq_top hK (hψ Γ) Γ (hsm Γ) (hΓW Γ)
  have h0 : ∀ Γ : Mori.PrimeDivisor X,
      letI := stalkAlgebra sX Γ.genericPoint
      haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
      topFormsMap k Γ.localRing X.functionField n
        (formsGerm sX (smoothLocus sX) n ⟨Γ.genericPoint, hsm Γ⟩
          (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials
              ((smoothLocus sX).ι ≫ sX)).exteriorAlgebra.piece
              (n : ℤ)).val.presheaf ((smoothLocus sX).ι ⁻¹ᵁ W Γ) ⟨Γ.genericPoint, hsm Γ⟩ (hΓW Γ)
            (hK.iso.hom.app ((smoothLocus sX).ι ⁻¹ᵁ W Γ)
              (Divisor.restrictInvSection (hψ Γ) (smoothLocus sX))))) ≠ 0 := fun Γ => by
    let := stalkAlgebra sX Γ.genericPoint
    have := isScalarTower_stalk_functionField sX Γ.genericPoint
    exact topFormsMap_ne_zero_of_span_eq_top (hσ Γ)
  -- the form `ω_Γ = g_Γ · b_Γ`
  let ω : Mori.PrimeDivisor X → RationalPluriForms sX n 1 := fun Γ =>
    letI := stalkAlgebra sX Γ.genericPoint
    haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
    g Γ • ZTensorPower.basis (topFormsBasis Γ.localRing (hσ Γ) (h0 Γ)) 1 ()
  have hord : ∀ Γ : Mori.PrimeDivisor X, Γ.ordForm (ω Γ) = K.coeff Γ := by
    intro Γ
    let := stalkAlgebra sX Γ.genericPoint
    have := isScalarTower_stalk_functionField sX Γ.genericPoint
    rw [PrimeDivisor.ordForm_eq Γ (ω Γ) (hσ Γ) (h0 Γ)]
    have hc : formCoeff (k := k) Γ.localRing (hσ Γ) (h0 Γ)
        (g Γ • ZTensorPower.basis (topFormsBasis Γ.localRing (hσ Γ) (h0 Γ)) 1 ()) = g Γ := by
      rw [formCoeff_smul]
      simp [formCoeff]
    refine (congrArg (fun x => X.ord x Γ.genericPoint) hc).trans ?_
    rw [← ord_eq_ord_componentToFunctionField Γ (ψ Γ)]
    exact (hψ Γ Γ ⟨Γ.genericPoint, PrimeDivisor.genericPoint_mem_support' Γ, hΓW Γ⟩).symm
  have hbΓ : ∀ Γ : Mori.PrimeDivisor X,
      (letI := stalkAlgebra sX Γ.genericPoint
      haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
      topFormsBasis Γ.localRing (hσ Γ) (h0 Γ) ()) = b Γ := fun Γ => by
    let := stalkAlgebra sX Γ.genericPoint
    have := isScalarTower_stalk_functionField sX Γ.genericPoint
    exact topFormsBasis_apply _ _ _
  have heq : ∀ Γ Γ' : Mori.PrimeDivisor X, ω Γ' = ω Γ := by
    intro Γ Γ'
    have hbb := formsGermFF_invSection_eq_smul hK (hψ Γ) (hψ Γ') Γ Γ' (hsm Γ) (hsm Γ') (hΓW Γ)
      (hΓW Γ')
    set c := (componentToFunctionField Γ.component).hom
      (((ψ Γ * (ψ Γ')⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Γ.component) with hcdef
    have hc : g Γ' * c = g Γ := by
      rw [hcdef, Units.val_mul, Pi.mul_apply, map_mul, mul_left_comm,
        componentToFunctionField_mul_inv (ψ Γ'), mul_one]
    exact ZTensorPower.smul_basis_one_eq_of_eq_smul
      ((hbΓ Γ').trans (hbb.trans (congrArg (c • ·) (hbΓ Γ).symm))) hc
  by_cases hne : Nonempty (Mori.PrimeDivisor X)
  · obtain ⟨Γ₀⟩ := hne
    refine ⟨ω Γ₀, ?_, fun Γ => (congrArg _ (heq Γ Γ₀)).trans (hord Γ)⟩
    let := stalkAlgebra sX Γ₀.genericPoint
    have := isScalarTower_stalk_functionField sX Γ₀.genericPoint
    exact smul_ne_zero (hg0 Γ₀) ((ZTensorPower.basis _ 1).ne_zero ())
  · let bb := Module.basisUnique Unit h1
    exact ⟨ZTensorPower.basis bb 1 (), (ZTensorPower.basis bb 1).ne_zero (),
      fun Γ => (hne ⟨Γ⟩).elim⟩

end SmoothInCodimOne

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- On a variety of dimension `n` over a perfect field the line `Ω^n_{k(X)/k}` has a basis. -/
theorem exists_basis_topForms (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) :
    letI := functionFieldAlgebra sX
    Nonempty (Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k])) := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have := essFiniteType_functionField (sX := sX)
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hK : Module.finrank X.functionField Ω[X.functionField⁄k] = n :=
    (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans hd
  have : FiniteDimensional X.functionField Ω[X.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k X.functionField).1
  have h1 : Module.finrank X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]) = 1 := by
    rw [exteriorPower.finrank_eq, hK, Nat.choose_self]
  exact ⟨Module.basisUnique Unit h1⟩

/-- **A canonical divisor is the divisor of a rational top form**, over a perfect field: there the
generic point of every prime divisor is a smooth point
(`MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus`). -/
theorem IsCanonicalDivisor.exists_ordForm_eq (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ :=
  IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hX
    (fun Γ => PrimeDivisor.genericPoint_mem_smoothLocus hX Γ) hK

/-- **KM Def. 2.25, local generators exist.** Let `(X, Δ)` be a pair, `K` a canonical divisor of
`X` of dimension `n`, `m > 0` an integer such that `m(K + Δ)` is a Cartier divisor, and `x ∈ X`.
Then `mΔ` is a divisor, and there are an open `U ∋ x` and a form `τ` generating
`𝒪_X(m(K + Δ))` on `U`. (`m > 0` is not needed.) -/
@[mmp "lem_km2b_local_generator_exists"]
theorem IsPair.exists_generatesOn {Δ : QDivisor X} (hP : IsPair sX Δ) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {m : ℕ}
    (hmC : ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor) (x : X) :
    (∃ D : Divisor X, Divisor.toQDivisor D = (m : ℤ) • Δ) ∧
      ∃ U : X.Opens, x ∈ U ∧ ∃ τ : RationalPluriForms sX n m, GeneratesOn Δ m U τ := by
  obtain ⟨C, hC, hCart⟩ := hmC
  refine ⟨⟨C - (m : ℤ) • K, ?_⟩, ?_⟩
  · rw [map_sub, map_zsmul, hC, smul_add]
    abel
  have hX := hP.isNormalVariety
  have hn := hK.topologicalKrullDim_eq
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := exists_basis_topForms hX hn
  obtain ⟨ω, hω0, hω⟩ := IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨U, hxU, φ, hφ⟩ := hCart x
  obtain ⟨g, hg0, hg⟩ := exists_ord_eq_of_units φ
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hcg : c ^ (m : ℤ) * g⁻¹ ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg0)
  let τ : RationalPluriForms sX n m := (c ^ (m : ℤ) * g⁻¹) • ZTensorPower.basis b m ()
  have hrepr : (ZTensorPower.basis b m).repr τ () = c ^ (m : ℤ) * g⁻¹ := by
    simp [τ]
  have hτ : τ ≠ 0 := smul_ne_zero hcg ((ZTensorPower.basis b m).ne_zero ())
  refine ⟨U, hxU, τ, hτ, fun Γ hΓ => ?_⟩
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω0
  have e2 := hN m τ hτ
  rw [hrepr, Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg0), ord_zpow _ hc,
    ← zpow_neg_one, ord_zpow _ hg0] at e2
  rw [← hc_def, hω Γ] at e1
  have hCΓ : (C.coeff Γ : ℚ) = m * (K.coeff Γ + Δ.coeff Γ) := by
    have := congrArg (fun D : QDivisor X => D.coeff Γ) hC
    rw [mul_add]
    simpa [zsmul_eq_mul] using this
  have hgΓ : C.coeff Γ = X.ord g Γ.genericPoint := (hφ Γ hΓ).trans (hg Γ)
  have e1' : (K.coeff Γ : ℚ) = X.ord c Γ.genericPoint + N := by exact_mod_cast (by omega : _)
  have e2' : (Γ.ordForm τ : ℚ) =
      m * X.ord c Γ.genericPoint + -1 * X.ord g Γ.genericPoint + m * N := by
    exact_mod_cast e2
  have hgΓ' : (C.coeff Γ : ℚ) = X.ord g Γ.genericPoint := by exact_mod_cast hgΓ
  linear_combination e2' - (m : ℚ) * e1' + hgΓ' - hCΓ

/-- **KM Def. 2.25, "thus there are rational numbers `a(Eᵢ, X, Δ)`".** Let `(X, Δ)` be a pair
with canonical divisor `K` of dimension `n`, and `(Y, f, E)` a divisor over `X`. Then a rational
number `a` with the property of the discrepancy `a(E, X, Δ)` exists. -/
@[mmp "lem_km2b_discrepancy_exists"]
theorem IsPair.exists_isDiscrepancy {Δ : QDivisor X} (hP : IsPair sX Δ) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (D : DivisorOver k sX) :
    ∃ a : ℚ, IsDiscrepancy sX n K Δ D a := by
  obtain ⟨hX, n', K', hK', hQ⟩ := hP
  obtain rfl : n' = n := by
    exact_mod_cast hK'.topologicalKrullDim_eq.symm.trans hK.topologicalKrullDim_eq
  have hn := hK.topologicalKrullDim_eq
  have : CompactSpace X := by
    have := hX.1
    exact QuasiCompact.compactSpace_of_compactSpace sX
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := exists_basis_topForms hX hn
  obtain ⟨ω, hω0, hω⟩ := IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨ω', hω0', hω'⟩ := IsCanonicalDivisor.exists_ordForm_eq hX hK'
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set c' := (ZTensorPower.basis b 1).repr ω' () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hω0'
  obtain ⟨φ, hφ⟩ := exists_units_of_ne_zero (mul_ne_zero hc' (inv_ne_zero hc))
  have hlin : K'.LinearlyEquivalent K := by
    refine ⟨φ, ?_⟩
    ext Γ
    obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hN 1 ω hω0
    have e2 := hN 1 ω' hω0'
    rw [← hc_def, hω Γ] at e1
    rw [← hc'_def, hω' Γ] at e2
    rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
      Scheme.ord_mul hc' (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc]
    omega
  have hQK := hQ.add_of_linearlyEquivalent hlin
  obtain ⟨m, hm, hmC⟩ := hQK.exists_pos
  obtain ⟨-, U, hxU, τ, hτ⟩ :=
    IsPair.exists_generatesOn ⟨hX, n', K', hK', hQ⟩ hK hmC (D.f D.E.genericPoint)
  refine ⟨D.ordPullback τ / m, hX, hK, m, hm, hmC, U, hxU, τ, hτ, ?_⟩
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

end MMP.Positivity
