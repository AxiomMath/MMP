module

public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics

/-!
# Push-forward along a proper birational morphism (KM §2.a)

Let `f : X → Y` be a proper birational morphism of normal varieties over `k`.

* For `φ ∈ k(Y)^× = k(X)^×`, `f_* div_X(φ) = div_Y(φ)`.
* For a `ℚ`-Cartier `ℚ`-divisor `B` on `Y`, `f_* f^* B = B`.

Here `f_*` is the birational transform of divisors along `f`
(`MMP.Mori.RationalMap.transformDivisor`), `φ` is seen on `X` through
`MMP.Mori.pullbackRationalFunction`, and `f^*B` is `MMP.Mori.QDivisor.IsPullback`.

## Main results

* `MMP.Positivity.transformDivisor_principalDivisor_pullback`
* `MMP.Positivity.transformDivisor_of_isPullback`

## Implementation notes

The hypotheses `hφ` and `hB`, that `f` maps no generic point of `X` into `Supp div(φ)`,
resp. `Supp B`, are what `MMP.Mori.pullbackRationalFunction` and `MMP.Mori.QDivisor.IsPullback`
require; they hold for every dominant `f` of integral schemes.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Mori

section Helpers

variable {X Y : Scheme.{u}}

/-- If `ψ : 𝒪_{X,x} ⟶ R` is compatible with the maps to the function field `K` of an integral
scheme `X`, then `Spec K ⟶ Spec R ⟶ Spec 𝒪_{X,x} ⟶ X` is the generic point of `X`. -/
theorem SpecMap_algebraMap_SpecMap_fromSpecStalk [IsIntegral X] {R : CommRingCat}
    [Algebra R X.functionField] {x : X} (ψ : X.presheaf.stalk x ⟶ R)
    (hψ : ∀ b, algebraMap R X.functionField (ψ.hom b) =
      algebraMap (X.presheaf.stalk x) X.functionField b) :
    Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ Spec.map ψ ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) := by
  have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have : ψ ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
      X.presheaf.stalkSpecializes hgen := by
    ext b; exact hψ b
  rw [← Spec.map_comp_assoc, this]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen

/-- A local homomorphism `𝒪_{X,x} ⟶ R` sends the closed point of `Spec R` to `x`. -/
theorem SpecMap_fromSpecStalk_closedPoint {x : X} {R : CommRingCat} [IsLocalRing R]
    (ψ : X.presheaf.stalk x ⟶ R) [IsLocalHom ψ.hom] :
    (Spec.map ψ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by
  change X.fromSpecStalk x (Spec.map ψ (IsLocalRing.closedPoint _)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- **Valuative criterion of separatedness at a valuation-ring stalk.** Let `f : X → Y` be a
separated dominant morphism of integral schemes inducing an isomorphism of function fields, and
`x₁, x₂` points over the same point of `Y`, whose local ring is a valuation ring, at which `f`
induces isomorphisms of local rings. Then `x₁ = x₂`: both give lifts
`Spec 𝒪_{Y,f(x₁)} ⟶ X` of the same valuative square. -/
theorem eq_of_isIso_stalkMap [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsSeparated f]
    [IsDominant f] (hμ : Function.Bijective (functionFieldMap f)) {x₁ x₂ : X}
    (h : f x₂ = f x₁) [ValuationRing (Y.presheaf.stalk (f x₁))] [IsIso (f.stalkMap x₁)]
    [IsIso (f.stalkMap x₂)] : x₁ = x₂ := by
  let alg : Algebra (Y.presheaf.stalk (f x₁)) X.functionField :=
    ((functionFieldMap f).comp (algebraMap (Y.presheaf.stalk (f x₁)) Y.functionField)).toAlgebra
  let e : Y.functionField ≃ₐ[Y.presheaf.stalk (f x₁)] X.functionField :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (functionFieldMap f) hμ) (fun _ => rfl)
  have : IsFractionRing (Y.presheaf.stalk (f x₁)) X.functionField :=
    IsLocalization.isLocalization_of_algEquiv _ e
  let c := (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom
  let ψ₁ : X.presheaf.stalk x₁ ⟶ Y.presheaf.stalk (f x₁) := inv (f.stalkMap x₁)
  let ψ₂ : X.presheaf.stalk x₂ ⟶ Y.presheaf.stalk (f x₁) := inv (f.stalkMap x₂) ≫ c
  have ht₁ := SpecMap_algebraMap_SpecMap_fromSpecStalk ψ₁ fun b => by
    change functionFieldMap f (algebraMap _ Y.functionField (ψ₁.hom b)) = _
    rw [functionFieldMap_algebraMap_stalk]
    congr 1
    change (ψ₁ ≫ f.stalkMap x₁).hom b = b
    simp [ψ₁]
  have ht₂ := SpecMap_algebraMap_SpecMap_fromSpecStalk ψ₂ fun b => by
    change functionFieldMap f (algebraMap _ Y.functionField
      (c.hom ((inv (f.stalkMap x₂)).hom b))) = _
    rw [MMP.Intersection.algebraMap_stalkCongr h, functionFieldMap_algebraMap_stalk]
    congr 1
    change (inv (f.stalkMap x₂) ≫ f.stalkMap x₂).hom b = b
    simp
  have hb₁ : (Spec.map ψ₁ ≫ X.fromSpecStalk x₁) ≫ f = Y.fromSpecStalk (f x₁) := by
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
    simp [ψ₁]
  have hb₂ : (Spec.map ψ₂ ≫ X.fromSpecStalk x₂) ≫ f = Y.fromSpecStalk (f x₁) := by
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
    simp only [ψ₂, IsIso.hom_inv_id_assoc]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_eq h).ge
  have hsq : X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x₁)) X.functionField)) ≫
        Y.fromSpecStalk (f x₁) := by
    rw [← ht₁, ← hb₁]
    simp only [Category.assoc]
  let S : ValuativeCommSq f :=
    { R := Y.presheaf.stalk (f x₁)
      domain := inferInstance
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Y.fromSpecStalk (f x₁)
      commSq := ⟨hsq⟩ }
  have hS := IsSeparated.valuativeCriterion f S
  let L₁ : S.commSq.LiftStruct := ⟨Spec.map ψ₁ ≫ X.fromSpecStalk x₁, ht₁, hb₁⟩
  let L₂ : S.commSq.LiftStruct := ⟨Spec.map ψ₂ ≫ X.fromSpecStalk x₂, ht₂, hb₂⟩
  have hL : (Spec.map ψ₁ ≫ X.fromSpecStalk x₁) (IsLocalRing.closedPoint _) =
      (Spec.map ψ₂ ≫ X.fromSpecStalk x₂) (IsLocalRing.closedPoint _) :=
    congrArg (fun L : S.commSq.LiftStruct => L.l (IsLocalRing.closedPoint _))
      (Subsingleton.elim L₁ L₂)
  rwa [SpecMap_fromSpecStalk_closedPoint, SpecMap_fromSpecStalk_closedPoint] at hL

/-- **A valuation ring is maximal for domination.** Let `f : X → Y` be a dominant morphism of
integral schemes inducing an isomorphism of function fields. At a point `x` whose image has a
valuation ring as local ring, `f^♯ : 𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` is an isomorphism. -/
theorem isIso_stalkMap_of_valuationRing [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (hμ : Function.Bijective (functionFieldMap f)) (x : X)
    [ValuationRing (Y.presheaf.stalk (f x))] : IsIso (f.stalkMap x) := by
  have key : ∀ a, algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom a) =
      functionFieldMap f (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a) :=
    fun a => (functionFieldMap_algebraMap_stalk f x a).symm
  have hinjX : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    IsFractionRing.injective _ _
  have hinjY : Function.Injective (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) :=
    IsFractionRing.injective _ _
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => hinjY (hμ.1 ?_), fun b => ?_⟩
  · rw [← key, ← key]
    exact congrArg _ hab
  obtain ⟨c, hc⟩ := hμ.2 (algebraMap (X.presheaf.stalk x) X.functionField b)
  suffices ∃ a, algebraMap (Y.presheaf.stalk (f x)) Y.functionField a = c by
    obtain ⟨a, ha⟩ := this
    exact ⟨a, hinjX (by rw [key, ha, hc])⟩
  rcases ValuationRing.isInteger_or_isInteger (Y.presheaf.stalk (f x)) c with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, ha⟩
  by_cases hu : IsUnit a
  · refine ⟨(hu.unit⁻¹ : (Y.presheaf.stalk (f x))ˣ), ?_⟩
    rw [map_units_inv, IsUnit.unit_spec, ha, inv_inv]
  by_cases hc0 : c = 0
  · exact ⟨0, by simp [hc0]⟩
  exfalso
  apply hu
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField (b * (f.stalkMap x).hom a) = 1 := by
    rw [map_mul, key, ha, ← hc, ← map_mul, mul_inv_cancel₀ hc0, map_one]
  exact (isUnit_map_iff (f.stalkMap x).hom a).mp
    (IsUnit.of_mul_eq_one b ((mul_comm _ _).trans (hinjX (h1.trans (map_one _).symm))))

section Valuation

variable [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]

/-- `v_P` does not vanish on the image of a nonzero element of `𝒪_{Y,P}`. -/
theorem valuation_toComponent_ne_zero (P : MMP.Mori.PrimeDivisor Y) {b : P.localRing}
    (hb : b ≠ 0) : P.valuation (P.toComponent.hom b) ≠ 0 := by
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  rw [map_mul, map_pow, map_mul, map_pow, P.valuation_toComponent_of_isUnit u.isUnit,
    P.valuation_toComponent_of_irreducible hϖ, one_mul]
  exact pow_ne_zero _ WithZero.exp_ne_zero

/-- A ring isomorphism `𝒪_{Y,P} ≅ 𝒪_{X,E}` of the local rings along two prime divisors carries
`v_P` to `v_E`. -/
theorem valuation_toComponent_ringEquiv (E : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor Y)
    (g : P.localRing ≃+* E.localRing) {b : P.localRing} (hb : b ≠ 0) :
    E.valuation (E.toComponent.hom (g b)) = P.valuation (P.toComponent.hom b) := by
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hϖ' : Irreducible (g ϖ) := (MulEquiv.irreducible_iff g.toMulEquiv).mpr hϖ
  simp only [map_mul, map_pow]
  rw [E.valuation_toComponent_of_isUnit (u.isUnit.map g),
    E.valuation_toComponent_of_irreducible hϖ',
    P.valuation_toComponent_of_isUnit u.isUnit, P.valuation_toComponent_of_irreducible hϖ]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- On the stalk at the generic point of a prime divisor `P`, the map to the function field of
the component of `P` through `𝒪_{Y,P}` is the canonical one. -/
theorem toComponent_stalkCongr_apply (P : MMP.Mori.PrimeDivisor Y) {y : Y}
    (h : y = P.genericPoint) (hy : y ∈ P.component.1) (b : Y.presheaf.stalk y) :
    P.toComponent.hom ((Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom b) =
      (stalkToRationalFunctions Y hy).hom b := by
  change (Y.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes' ≫
    Y.presheaf.stalkSpecializes ((isGenericPoint_componentGenericPoint Y P.component).specializes
      P.genericPoint_mem_component)).hom b = (Y.presheaf.stalkSpecializes
        ((isGenericPoint_componentGenericPoint Y P.component).specializes hy)).hom b
  rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- `v_P` does not vanish on the image of a nonzero element of the stalk at `η_P`. -/
theorem valuation_stalkToRationalFunctions_ne_zero (P : MMP.Mori.PrimeDivisor Y) {y : Y}
    (h : y = P.genericPoint) (hy : y ∈ P.component.1) {b : Y.presheaf.stalk y} (hb : b ≠ 0) :
    P.valuation ((stalkToRationalFunctions Y hy).hom b) ≠ 0 := by
  rw [← toComponent_stalkCongr_apply P h hy]
  exact valuation_toComponent_ne_zero P fun h0 => hb (by
    simpa using congrArg (inv (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom).hom h0)

/-- Let `E ⊆ X`, `P ⊆ Y` be prime divisors with `f(η_E) = η_P` and `f^♯ : 𝒪_{Y,P} ⟶ 𝒪_{X,E}` an
isomorphism. Then `v_E(f^♯ b) = v_P(b)` for every nonzero `b ∈ 𝒪_{Y,f(η_E)}`. -/
theorem valuation_toComponent_stalkMap {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] (hfx : f E.genericPoint ∈ P.component.1)
    {b : Y.presheaf.stalk (f E.genericPoint)} (hb : b ≠ 0) :
    E.valuation (E.toComponent.hom ((f.stalkMap E.genericPoint).hom b)) =
      P.valuation ((stalkToRationalFunctions Y hfx).hom b) := by
  let t := (Y.presheaf.stalkCongr (Inseparable.of_eq heq)).hom
  let g : P.localRing ≃+* E.localRing :=
    ((Y.presheaf.stalkCongr (Inseparable.of_eq heq)).symm ≪≫
      asIso (f.stalkMap E.genericPoint)).commRingCatIsoToRingEquiv
  have hg : g (t.hom b) = (f.stalkMap E.genericPoint).hom b := by
    change ((Y.presheaf.stalkCongr (Inseparable.of_eq heq)).hom ≫
      (Y.presheaf.stalkCongr (Inseparable.of_eq heq)).inv ≫ f.stalkMap E.genericPoint).hom b = _
    rw [Iso.hom_inv_id_assoc]
  have hts : t.hom b ≠ 0 := fun h0 => hb (by simpa using congrArg (inv t).hom h0)
  rw [← hg, valuation_toComponent_ringEquiv E P g hts]
  exact congrArg P.valuation (toComponent_stalkCongr_apply P heq hfx b)

/-- **The order of vanishing along a strict transform.** Let `E ⊆ X`, `P ⊆ Y` be prime divisors
with `f(η_E) = η_P` and `f^♯ : 𝒪_{Y,P} ⟶ 𝒪_{X,E}` an isomorphism. If `a` is a unit of
`𝒪_{Y,f(η_i)}` (`η_i` the generic point of the component of `E`) with image `φ_j` in the function
field of the component of `P`, then `v_E(f^♯ a) = v_P(φ)`. -/
theorem ordUnit_stalkMap_eq_ord {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] (φ : (RationalFunctions Y)ˣ)
    (hW : f (componentGenericPoint X E.component) ∈ P.component.1)
    (a : (Y.presheaf.stalk (f (componentGenericPoint X E.component)))ˣ)
    (ha : (stalkToRationalFunctions Y hW).hom a = (φ : RationalFunctions Y) P.component) :
    E.ordUnit (Units.map (f.stalkMap (componentGenericPoint X E.component)).hom.toMonoidHom a) =
      P.ord φ := by
  have sp : componentGenericPoint X E.component ⤳ E.genericPoint := E.specializes_genericPoint
  have sp' := f.base.hom.map_specializes sp
  have hfx : f E.genericPoint ∈ P.component.1 := heq ▸ P.genericPoint_mem_component
  have hι' : ∀ b, (stalkToRationalFunctions Y hW).hom ((Y.presheaf.stalkSpecializes sp').hom b) =
      (stalkToRationalFunctions Y hfx).hom b := by
    intro b
    change (Y.presheaf.stalkSpecializes _ ≫ Y.presheaf.stalkSpecializes _).hom b =
      (Y.presheaf.stalkSpecializes _).hom b
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  have hE : ∀ b, (f.stalkMap (componentGenericPoint X E.component)).hom
      ((Y.presheaf.stalkSpecializes sp').hom b) =
        E.toComponent.hom ((f.stalkMap E.genericPoint).hom b) :=
    fun b => Scheme.Hom.stalkSpecializes_stalkMap_apply f _ _ sp b
  let := (stalkToRationalFunctions Y hfx).hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions hfx
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective
    (nonZeroDivisors (Y.presheaf.stalk (f E.genericPoint))) ((φ : RationalFunctions Y) P.component)
  have hspec := IsLocalization.mk'_spec
    (Y.presheaf.stalk (componentGenericPoint Y P.component)) r s
  change IsLocalization.mk' _ r s = _ at hrs
  rw [hrs] at hspec
  change (φ : RationalFunctions Y) P.component * (stalkToRationalFunctions Y hfx).hom s =
    (stalkToRationalFunctions Y hfx).hom r at hspec
  have hs : (s : Y.presheaf.stalk (f E.genericPoint)) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hr : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hspec
    have h0 : (stalkToRationalFunctions Y hfx).hom s = 0 := by
      have := congrArg (fun z => ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y)
        P.component * z) hspec
      simp only [mul_zero, ← mul_assoc] at this
      rwa [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply,
        one_mul] at this
    exact hs (stalkToRationalFunctions_injective hfx (h0.trans (map_zero _).symm))
  have h1 : (a : Y.presheaf.stalk _) * (Y.presheaf.stalkSpecializes sp').hom s =
      (Y.presheaf.stalkSpecializes sp').hom r := by
    apply stalkToRationalFunctions_injective hW
    rw [map_mul, ha, hι', hι', hspec]
  have h2 := congrArg (fun z => E.valuation ((f.stalkMap _).hom z)) h1
  simp only [map_mul, hE] at h2
  rw [valuation_toComponent_stalkMap E P heq hfx hs,
    valuation_toComponent_stalkMap E P heq hfx hr] at h2
  have h3 := congrArg P.valuation hspec
  rw [map_mul] at h3
  have h4 := mul_right_cancel₀ (valuation_stalkToRationalFunctions_ne_zero P heq hfx hs)
    (h2.trans h3.symm)
  rw [P.valuation_component] at h4
  exact WithZero.exp_injective ((E.valuation_eq_exp_ordUnit _).symm.trans h4)

end Valuation

/-! ### Transforms of prime divisors under a morphism -/

/-- The coefficient of `P` in the linear extension of a partial map `φ` on prime divisors, when `E`
is the only prime divisor sent to `P`, is the coefficient of `E`. -/
theorem mapPrimeDivisors_apply_of_forall_eq {R : Type*} [AddCommMonoid R]
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)} {E : MMP.Mori.PrimeDivisor X}
    {P : MMP.Mori.PrimeDivisor Y} (hE : φ E = some P) (h : ∀ E', φ E' = some P → E' = E)
    (D : DivisorWithCoeffs R X) : DivisorWithCoeffs.mapPrimeDivisors φ D P = D E := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hD, hD']
  | single E' r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hφ : φ E' with _ | Q
    · have : E' ≠ E := fun h' => by rw [h', hE] at hφ; cases hφ
      simp [this]
    · by_cases hQ : Q = P
      · subst hQ
        obtain rfl := h E' hφ
        simp
      · have : E' ≠ E := fun h' => by rw [h', hE] at hφ; exact hQ (Option.some.inj hφ).symm
        simp [hQ, this]

/-- A closed subscheme which is reduced is cut out by the vanishing ideal of its support (as in
`Stacks.Intersection.ExteriorProductProjections.vanishingIdeal_support_of_isReduced`). -/
theorem vanishingIdeal_support_of_isReduced {Z : Scheme.{u}} (I : Z.IdealSheafData)
    [IsReduced I.subscheme] : Scheme.IdealSheafData.vanishingIdeal I.support = I := by
  have h : Closeds.closure (I.subschemeι.base '' ((⊤ : Closeds I.subscheme) : Set I.subscheme)) =
      I.support := by
    apply SetLike.coe_injective
    simp only [Closeds.coe_closure, Closeds.coe_top, Set.image_univ]
    rw [show Set.range I.subschemeι.base = (I.support : Set Z) from I.range_subschemeι]
    exact I.support.isClosed.closure_eq
  rw [← h, ← Scheme.IdealSheafData.map_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_subschemeι]

/-- The transform of a prime divisor `E` under a morphism `f` from a reduced scheme to a separated
scheme is the prime divisor `P` exactly when `f(η_E) = η_P`. -/
theorem transformPrimeDivisor_toRationalMap_eq_some_iff [IsReduced X]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] (f : X ⟶ Y) (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) :
    RationalMap.transformPrimeDivisor (X := X) f.toRationalMap E = some P ↔
      f E.genericPoint = P.genericPoint := by
  have hdef : RationalMap.DefinedAt (X := X) f.toRationalMap E.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have htr := closure_image_eq_transform f.toPartialMap rfl E.idealSheaf.support (by
    change closure ((E.idealSheaf.support : Set X) ∩ ((⊤ : X.Opens) : Set X)) = _
    rw [TopologicalSpace.Opens.coe_top, Set.inter_univ, E.idealSheaf.support.isClosed.closure_eq])
  have htr' : (RationalMap.transform (X := X) f.toRationalMap E.idealSheaf.support : Set Y) =
      closure {f E.genericPoint} := by
    rw [← htr, image_toPartialMap_hom, Closeds.coe_closure]
    change closure (f '' E.support) = _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, closure_image_closure f.continuous,
      Set.image_singleton]
  constructor
  · intro h
    have h1 := RationalMap.support_transformPrimeDivisor h
    rw [htr', AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
    exact ((specializes_iff_closure_subset.mpr h1.le).antisymm
      (specializes_iff_closure_subset.mpr h1.ge)).eq
  · intro h
    refine RationalMap.transformPrimeDivisor_eq_some_iff.mpr ⟨hdef, ?_⟩
    have hP : RationalMap.transform (X := X) f.toRationalMap E.idealSheaf.support =
        P.idealSheaf.support := by
      apply SetLike.coe_injective
      rw [htr', h]
      exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure P).symm
    have := P.integral
    rw [RationalMap.transformIdeal, hP, vanishingIdeal_support_of_isReduced]

end Helpers

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
  [CompactSpace X] [CompactSpace Y]

omit [IsLocallyNoetherian X] [CompactSpace X] [CompactSpace Y] in
/-- **The strict transform of a prime divisor.** Let `f : X → Y` be a proper birational morphism
of normal varieties and `P ⊆ Y` a prime divisor. There is a prime divisor `E ⊆ X` with
`f(η_E) = η_P` at which `f` induces an isomorphism `𝒪_{Y,P} ≅ 𝒪_{X,E}`, and it is the only prime
divisor whose transform is `P`: the coefficient of `P` in `f_* D` is the coefficient of `E` in
`D`. -/
theorem exists_isIso_stalkMap_forall_transformDivisor_apply (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f)
    (P : MMP.Mori.PrimeDivisor Y) :
    ∃ E : MMP.Mori.PrimeDivisor X, f E.genericPoint = P.genericPoint ∧
      IsIso (f.stalkMap E.genericPoint) ∧ ∀ {R : Type*} [AddCommMonoid R]
        (D : DivisorWithCoeffs R X), RationalMap.transformDivisor (X := X) f.toRationalMap D P =
          D E := by
  have := hY.1
  have := hX.1
  have : IsSeparated f := IsSeparated.of_comp f sY
  have : IsSeparated (Y ↘ Limits.terminal Scheme) := by
    rw [show (Y ↘ Limits.terminal Scheme) = sY ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨x, hx, hiso⟩ := MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hbij
    P.genericPoint
  have hco : Order.coheight x = 1 := by
    have h1 : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) :=
      (ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      P.coheight_genericPoint] at h1
    exact_mod_cast h1
  set E := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  have hEP : f E.genericPoint = P.genericPoint := by rw [hE, hx]
  have hisoE : IsIso (f.stalkMap E.genericPoint) := hE ▸ hiso
  refine ⟨E, hEP, hisoE, fun D => ?_⟩
  refine mapPrimeDivisors_apply_of_forall_eq
    ((transformPrimeDivisor_toRationalMap_eq_some_iff f E P).mpr hEP) (fun E' hE' => ?_) D
  have hE'P := (transformPrimeDivisor_toRationalMap_eq_some_iff f E' P).mp hE'
  have : ValuationRing (Y.presheaf.stalk (f E'.genericPoint)) := by rw [hE'P]; infer_instance
  have : ValuationRing (Y.presheaf.stalk (f E.genericPoint)) := by rw [hEP]; infer_instance
  have := isIso_stalkMap_of_valuationRing f hbij E'.genericPoint
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_isIso_stalkMap f hbij (x₁ := E.genericPoint) (x₂ := E'.genericPoint)
      (hE'P.trans hEP.symm)).symm

omit [CompactSpace X] [CompactSpace Y] in
/-- Let `E ⊆ X` and `P ⊆ Y` be prime divisors with `f(η_E) = η_P` and `𝒪_{Y,P} ≅ 𝒪_{X,E}`. If `D'`
is the pull-back of a Cartier divisor `D` on `Y`, the coefficient of `E` in `D'` is the
coefficient of `P` in `D`. -/
theorem coeff_eq_of_isPullback {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] {D : Divisor Y} (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    {D' : Divisor X} (h : D.IsPullback f hB D') : D'.coeff E = D.coeff P := by
  obtain ⟨U, hU, φ, hφ⟩ := hDc P.genericPoint
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty :=
    (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp (show f E.genericPoint ∈ U from heq ▸ hU)
  have hPU : (P.support ∩ U).Nonempty := (P.genericPoint_mem_iff U).mp hU
  rw [h U φ hφ E hEU, hφ P hPU]
  have hsp : f (componentGenericPoint X E.component) ⤳ P.genericPoint :=
    heq ▸ f.base.hom.map_specializes E.specializes_genericPoint
  have hWP : pointComponent (f (componentGenericPoint X E.component)) = P.component :=
    eq_of_mem_irreducibleComponents
      (hsp.mem_closed (isClosed_of_mem_irreducibleComponents _ (pointComponent _).2)
        (mem_pointComponent _)) P.genericPoint_mem_component
  have hW : f (componentGenericPoint X E.component) ∈ P.component.1 :=
    hWP ▸ mem_pointComponent _
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk (E.map_componentGenericPoint_mem f hEU) (hB _) hW
  rw [pullbackComponent_eq hB hφ _ hW a ha]
  exact ordUnit_stalkMap_eq_ord E P heq φ hW a ha

omit [CompactSpace X] [CompactSpace Y] in
/-- **KM §2.a.** Let `f : X → Y` be a proper birational morphism of normal varieties and `D` a
Cartier divisor on `Y`. Then `f_* f^* D = D`. -/
theorem transformDivisor_of_isPullback_divisor (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f)
    {D : Divisor Y} (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    {D' : Divisor X} (h : D.IsPullback f hB D') :
    RationalMap.transformDivisor (X := X) f.toRationalMap D' = D := by
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, heq, hiso, htr⟩ := exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hf P
  exact (htr _).trans (coeff_eq_of_isPullback E P heq hDc h)

/-- **KM §2.a.** Let `f : X → Y` be a proper birational morphism of normal varieties and
`φ ∈ k(X)^× = k(Y)^×`. Then `f_* div_X(φ) = div_Y(φ)`. -/
@[mmp "lem_km2a_birational_pushforward_principal"]
theorem transformDivisor_principalDivisor_pullback (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f)
    (φ : (RationalFunctions Y)ˣ)
    (hφ : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (principalDivisor φ).supp) :
    RationalMap.transformDivisor (X := X) f.toRationalMap
        (principalDivisor (pullbackRationalFunction f φ hφ)) = principalDivisor φ :=
  transformDivisor_of_isPullback_divisor hY hX hf (Divisor.isCartier_principalDivisor φ)
    (Divisor.isPullback_principalDivisor φ hφ)

omit [CompactSpace X] [CompactSpace Y] in
/-- **KM §2.a.** Let `f : X → Y` be a proper birational morphism of normal varieties and `B` a
`ℚ`-Cartier `ℚ`-divisor on `Y`. Then `f_* f^* B = B`. -/
@[mmp "lem_km2a_birational_pushforward_pullback"]
theorem transformDivisor_of_isPullback (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f)
    {B : QDivisor Y} (hBq : B.IsQCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp)
    {B' : QDivisor X} (hB' : B.IsPullback f hB B') :
    RationalMap.transformDivisor (X := X) f.toRationalMap B' = B := by
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, heq, hiso, htr⟩ := exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hf P
  rw [htr]
  have hm := QDivisor.cartierIndex_pos hBq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hBq
  obtain ⟨D', hD', hp⟩ := hB' _ hm D₀ hD₀ hD₀c
  have hc := coeff_eq_of_isPullback E P heq hD₀c hp
  have h1 := congrArg (fun G : QDivisor X => G E) hD'
  have h2 := congrArg (fun G : QDivisor Y => G P) hD₀
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1 h2
  have hm' : (B.cartierIndex hBq : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  exact mul_left_cancel₀ hm' (h1.symm.trans ((congrArg (fun z : ℤ => (z : ℚ)) hc).trans h2))

end MMP.Positivity
