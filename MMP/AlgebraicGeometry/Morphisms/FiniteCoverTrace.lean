module
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent

/-!
# Contractions, traces, sections along birational morphisms, flips and normal divisors

Results from Kollár–Mori, *Birational geometry of algebraic varieties*, chapters 2, 3 and 5:

* the target of a contraction `f_* 𝒪_X = 𝒪_Y` from a normal variety is normal;
* over a normal base the trace of a finite cover maps regular functions to regular functions, and
  `deg⁻¹ · Tr` splits `𝒪_X ⟶ f_* 𝒪_Y` when the degree is invertible;
* along a proper birational morphism `f : Y ⟶ X` of normal varieties, global sections of
  `𝒪_Y(B_Y)` push forward to `𝒪_X(B)`, and `𝒪_X(B) ≅ f_* 𝒪_Y(f^*B + E)` for an effective
  `f`-exceptional `E`;
* a small projective model on which `K + D` becomes ample is a flip;
* a reduced divisor with normal support has pairwise disjoint components.

## Main results

* `MMP.Mori.isNormal_of_isIso_c`
* `MMP.Mori.exists_germToFunctionField_eq_fieldTrace`
* `MMP.Mori.exists_unitToPushforwardObjUnit_comp_eq_id`
* `MMP.Mori.Divisor.exists_functionFieldMap_eq_of_isBirationalMorphism`
* `MMP.Mori.Divisor.exists_addEquiv_divisorialSubmodule_add_of_isExceptional`
* `MMP.Mori.Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional`
* `MMP.Mori.DivisorWithCoeffs.mapPrimeDivisors_toQDivisor`, `MMP.Mori.flipTransform_toQDivisor`:
  mapping prime divisors, and the birational transform `g⁻¹_* f_*`, commute with `toQDivisor`
* `MMP.Mori.isFlip_of_isProjectiveMorphism`
* `MMP.Mori.DivisorWithCoeffs.pairwise_disjoint_support_of_isNormal_suppScheme`

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

/-!
## The target of a contraction from a normal variety is normal

Let `f : X ⟶ Y` be a dominant morphism of varieties over a field `k` with `X` normal and
`f_* 𝒪_X = 𝒪_Y`. Then `Y` is normal: for a nonempty affine open `V ⊆ Y` the comorphism identifies
`𝒪(V)` with `𝒪(f⁻¹ V)`, the ring of global sections of the integral normal open subscheme
`f⁻¹ V` of `X` (nonempty by dominance), which is an integrally closed domain.

### Main results

* `MMP.Mori.isNormal_of_isIso_c`: the target of a dominant morphism of varieties `f` with
  `X` normal and `𝒪_Y ⟶ f_* 𝒪_X` an isomorphism is normal.

### Implementation notes

The condition `f_* 𝒪_X = 𝒪_Y` is the canonical one: the comorphism `f.c : 𝒪_Y ⟶ f_* 𝒪_X` of `f`
is an isomorphism.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 2.5
-/

section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **The target of a contraction from a normal variety is normal.** Let `f : X ⟶ Y` be a
dominant morphism of varieties over `k` with `X` normal and `𝒪_Y ⟶ f_* 𝒪_X` an isomorphism.
Then `Y` is normal. -/
@[mmp "lem_km2a_contraction_target_normal"]
public theorem isNormal_of_isIso_c {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (f : X ⟶ Y) (hY : IsVariety k sY) (hX : IsVariety k (f ≫ sY))
    [IsDominant f] [IsNormal X] [IsIso f.c] :
    IsNormal Y := by
  have := hX.toIsIntegral
  have := hY.toIsIntegral
  rw [isNormal_iff_forall_affineOpen_normal]
  intro V hV
  obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open V.1.isOpen ⟨hV.some.1, hV.some.2⟩
  have : Nonempty (f ⁻¹ᵁ V.1) := ⟨⟨x, hx⟩⟩
  have : IsIso (f.app V.1) := NatIso.isIso_app_of_isIso f.c (Opposite.op V.1)
  exact (normal_globalSections (f ⁻¹ᵁ V.1).toScheme).of_equiv
    ((asIso (f.app V.1)) ≪≫ (f ⁻¹ᵁ V.1).topIso.symm).commRingCatIsoToRingEquiv.symm

end MMP.Mori

end

/-!
## The trace of a regular function over a normal base is regular

Let `f : Y ⟶ X` be an integral (for instance finite) dominant morphism of integral schemes with
`X` normal, and let `Tr_{Y/X} : K(Y) → K(X)` be the field trace `MMP.Mori.fieldTrace f`. For every
nonempty open `U ⊆ X` and every section `s ∈ 𝒪_Y(f⁻¹U)`, the trace of the rational function `s`
is the rational function of a section of `𝒪_X(U)`: the trace maps `𝒪_Y(f⁻¹U)` into `𝒪_X(U)`.

### Main results

* `MMP.Mori.exists_germToFunctionField_eq_fieldTrace`

### Implementation notes

Sections of `𝒪_X(U)` are compared with elements of `K(X)` through the injective map
`AlgebraicGeometry.Scheme.germToFunctionField`, which is defined only for nonempty `U`; for
`U = ∅` the statement is empty. The source's hypothesis that `f` be finite and surjective is
weakened to `f` integral and dominant: this is what makes `𝒪_Y(f⁻¹U)` integral over `𝒪_X(U)`
on affine `U` and gives the extension `K(Y)/K(X)`. When `K(Y)/K(X)` is infinite the trace is `0`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 2.64
-/

section

universe u

open CategoryTheory AlgebraicGeometry
open MMP.Mori (fieldTrace functionFieldMapAlgebra)

namespace MMP.Proofs.lem_km2c_trace_regular

/-- The rational function of a restricted section is the rational function of the section. -/
private theorem germToFunctionField_map {X : Scheme.{u}} [IsIntegral X] {U V : X.Opens}
    (i : V ⟶ U) [Nonempty U] [Nonempty V] (s : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map i.op s) = X.germToFunctionField U s :=
  X.presheaf.germ_res_apply i _ _ s

/-- `g^*` of the germ of `a` at the generic point is the germ of `g^♯ a`. -/
private theorem functionFieldMap_germ {X Y : Scheme.{u}} (g : Y ⟶ X) [IsIntegral X]
    [IsIntegral Y] [IsDominant g] (U : X.Opens) (a : Γ(X, U)) (hx : genericPoint X ∈ U)
    (hy : genericPoint Y ∈ g ⁻¹ᵁ U) :
    functionFieldMap g (X.presheaf.germ U (genericPoint X) hx a) =
      Y.presheaf.germ (g ⁻¹ᵁ U) (genericPoint Y) hy (g.app U a) := by
  have key : X.presheaf.germ U (genericPoint X) hx ≫
      (X.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant g).symm)).hom ≫
        g.stalkMap (genericPoint Y) = g.app U ≫ Y.presheaf.germ (g ⁻¹ᵁ U) (genericPoint Y) hy := by
    simp only [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc (F := X.presheaf) (x := g (genericPoint Y))]
    exact Scheme.Hom.germ_stalkMap g U _ hy
  exact congrArg (fun f => f.hom a) key

/-- The extension of function fields of a dominant morphism is compatible with pulling back
sections: `f^*` of the rational function of `a ∈ 𝒪_X(U)` is the rational function of `f^♯ a`. -/
private theorem functionFieldMap_germToFunctionField {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] (U : X.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (a : Γ(X, U)) :
    functionFieldMap f (X.germToFunctionField U a) =
      Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) := by
  obtain ⟨y⟩ := ‹Nonempty (f ⁻¹ᵁ U)›
  exact functionFieldMap_germ f U a _
    (((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr ⟨y.1, trivial, y.2⟩)

/-- The affine case: over an affine open `U` of a normal `X`, the trace of a section of `𝒪_Y`
over `f⁻¹U` is the rational function of a section of `𝒪_X` over `U`. -/
private theorem exists_germToFunctionField_eq_fieldTrace_of_isAffineOpen {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIntegralHom f] [IsNormal X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (s : Γ(Y, f ⁻¹ᵁ U)) :
    ∃ t : Γ(X, U), X.germToFunctionField U t =
      fieldTrace f (Y.germToFunctionField (f ⁻¹ᵁ U) s) := by
  letI := functionFieldMapAlgebra f
  letI : Algebra Γ(X, U) Y.functionField :=
    ((functionFieldMap f).comp (X.germToFunctionField U).hom).toAlgebra
  haveI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  haveI : IsIntegrallyClosed Γ(X, U) :=
    (isNormal_iff_forall_affineOpen_normal X).mp ‹IsNormal X› ⟨U, hU⟩ ‹Nonempty U›
  have hint : _root_.IsIntegral Γ(X, U) (Y.germToFunctionField (f ⁻¹ᵁ U) s) := by
    obtain ⟨p, hp, hps⟩ := IsIntegralHom.isIntegral_app f U hU s
    refine ⟨p, hp, ?_⟩
    have h := congrArg (Y.germToFunctionField (f ⁻¹ᵁ U)).hom hps
    rw [Polynomial.hom_eval₂, map_zero] at h
    have heq : algebraMap Γ(X, U) Y.functionField =
        (Y.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom :=
      RingHom.ext fun a => functionFieldMap_germToFunctionField f U a
    rw [← heq] at h
    exact h
  change ∃ t, algebraMap Γ(X, U) X.functionField t =
    Algebra.trace X.functionField Y.functionField _
  by_cases hfd : FiniteDimensional X.functionField Y.functionField
  · exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hint)
  · refine ⟨0, ?_⟩
    rw [Algebra.trace_eq_zero_of_not_exists_basis, map_zero, LinearMap.zero_apply]
    rintro ⟨b, ⟨e⟩⟩
    exact hfd (Module.Finite.of_basis e)

/-- Regularity of a rational function is local: if `φ ∈ K(X)` is, near every point of `U`, the
rational function of a section, then it is the rational function of a section over `U`. -/
private theorem exists_germToFunctionField_eq_of_local {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (φ : X.functionField)
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hxV : x ∈ V), V ≤ U ∧
      ∃ t : Γ(X, V), X.germToFunctionField (h := ⟨⟨x, hxV⟩⟩) V t = φ) :
    ∃ t : Γ(X, U), X.germToFunctionField U t = φ := by
  choose V hxV hVU t htx using fun x : U => h x.1 x.2
  have hgen : ∀ x : U, genericPoint X ∈ V x := fun x =>
    ((genericPoint_spec X).mem_open_set_iff (V x).isOpen).mpr ⟨x.1, trivial, hxV x⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.obj V t := by
    intro i j
    have : Nonempty (V i ⊓ V j : X.Opens) := ⟨⟨genericPoint X, hgen i, hgen j⟩⟩
    exact X.germToFunctionField_injective (V i ⊓ V j) <|
      (@germToFunctionField_map X _ _ _ (TopologicalSpace.Opens.infLELeft _ _)
      ⟨⟨i.1, hxV i⟩⟩ this (t i)).trans ((htx i).trans ((htx j).symm.trans
      (@germToFunctionField_map X _ _ _ (TopologicalSpace.Opens.infLERight _ _)
        ⟨⟨j.1, hxV j⟩⟩ this (t j)).symm))
  obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' V U (fun x => homOfLE (hVU x))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV _⟩) t hcomp
  obtain ⟨x⟩ := ‹Nonempty U›
  refine ⟨g, ?_⟩
  rw [← htx x, ← hg x]
  exact (@germToFunctionField_map X _ _ _ (homOfLE (hVU x)) _ ⟨⟨x.1, hxV x⟩⟩ g).symm

end MMP.Proofs.lem_km2c_trace_regular

namespace MMP.Mori

open MMP.Proofs.lem_km2c_trace_regular in
/-- Over a normal integral base, the field trace of an integral dominant morphism `f : Y ⟶ X` of
integral schemes sends the rational function of a section of `𝒪_Y` over `f⁻¹U` to the rational
function of a section of `𝒪_X` over `U`. -/
@[mmp "lem_km2c_trace_regular"]
public theorem exists_germToFunctionField_eq_fieldTrace {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIntegralHom f] [IsNormal X]
    (U : X.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, f ⁻¹ᵁ U)) :
    ∃ t : Γ(X, U), X.germToFunctionField U t =
      fieldTrace f (Y.germToFunctionField (f ⁻¹ᵁ U) s) := by
  refine exists_germToFunctionField_eq_of_local U _ fun x hx => ?_
  obtain ⟨V, hVa, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨genericPoint Y, show f (genericPoint Y) ∈ V by
    rw [map_genericPoint_of_isDominant f]
    exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩⟩⟩
  obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_fieldTrace_of_isAffineOpen f V hVa
    (Y.presheaf.map (homOfLE (f.preimage_mono hVU)).op s)
  exact ⟨V, hxV, hVU, t, ht.trans (by rw [germToFunctionField_map])⟩

end MMP.Mori

end

/-!
## The trace splits the structure map of a finite cover of a normal variety

Let `k` be a field of characteristic `0` and `f : Y ⟶ X` a finite surjective morphism of
varieties over `k` with `X` normal. Then the structure map `f^# : 𝒪_X ⟶ f_* 𝒪_Y` of sheaves of
`𝒪_X`-modules is a split monomorphism: there is an `𝒪_X`-linear `τ : f_* 𝒪_Y ⟶ 𝒪_X` with
`τ ∘ f^# = id`. One may take `τ = d⁻¹ · Tr_{Y/X}`, where `d = [K(Y) : K(X)]`
(`MMP.Mori.finiteDegree f`) and `Tr_{Y/X}` is the trace `MMP.Mori.fieldTrace f`.

## Main results

* `MMP.Mori.exists_unitToPushforwardObjUnit_comp_eq_id`: the splitting.

## Implementation notes

The extension `K(Y)/K(X)` is finite since `f` is finite, so `d ≥ 1`, and `d` is a unit of
`k ⊆ 𝒪_X(X)` since `k` has characteristic `0`. Over a normal `X` the trace of a section of
`𝒪_Y` over `f⁻¹ U` is a section of `𝒪_X` over `U`
(`MMP.Mori.exists_germToFunctionField_eq_fieldTrace`), and `d⁻¹ · Tr` is then `𝒪_X`-linear and
restricts to the identity on `𝒪_X`. The characteristic assumption cannot be dropped: for a
variety in characteristic `p` that is not F-split the Frobenius is a counterexample. The
structure map `f^#` is `SheafOfModules.unitToPushforwardObjUnit` for the morphism of sheaves of
rings underlying `f`, and `𝒪_X` is `SheafOfModules.unit X.ringCatSheaf`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 2.64,
  Step 1, and 5.7(2)
-/

section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Proofs.lem_km2c_finite_trace_splitting

open MMP.Proofs.lem_km2c_trace_regular

private theorem nonempty_preimage {X Y : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    (U : X.Opens) [h : Nonempty U] : Nonempty (f ⁻¹ᵁ U) :=
  let ⟨x, hx⟩ := f.denseRange.exists_mem_open U.isOpen ⟨_, h.some.2⟩
  ⟨⟨x, hx⟩⟩

/-- Sections over an open `U` are determined by their rational functions: over a nonempty `U`
this is the injectivity of `germToFunctionField`, and over the empty open sections are zero. -/
private theorem eq_of_germToFunctionField_eq {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    {a b : Γ(X, U)} (h : ∀ [Nonempty U], X.germToFunctionField U a = X.germToFunctionField U b) :
    a = b := by
  by_cases hU : Nonempty U
  · exact X.germToFunctionField_injective U h
  · obtain rfl : U = ⊥ := le_bot_iff.mp fun x hx => (hU ⟨⟨x, hx⟩⟩).elim
    exact Subsingleton.elim _ _

private theorem fieldTrace_functionFieldMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] (a : X.functionField) :
    fieldTrace f (functionFieldMap f a) = (finiteDegree f : X.functionField) * a := by
  let := functionFieldMapAlgebra f
  exact (Algebra.trace_algebraMap a).trans (nsmul_eq_mul _ _)

private theorem fieldTrace_functionFieldMap_mul {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] (a : X.functionField) (b : Y.functionField) :
    fieldTrace f (functionFieldMap f a * b) = a * fieldTrace f b := by
  let := functionFieldMapAlgebra f
  exact (Algebra.trace X.functionField Y.functionField).map_smul a b

private theorem fieldTrace_add {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] (a b : Y.functionField) :
    fieldTrace f (a + b) = fieldTrace f a + fieldTrace f b := by
  let := functionFieldMapAlgebra f
  exact (Algebra.trace X.functionField Y.functionField).map_add a b

attribute [local instance] nonempty_preimage

/-- A finite dominant morphism of integral schemes induces a finite extension of function
fields. -/
private theorem finite_functionField {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsFinite f] :
    letI := functionFieldMapAlgebra f
    Module.Finite X.functionField Y.functionField := by
  let := functionFieldMapAlgebra f
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  let A := Γ(X, U)
  let B := Γ(Y, f ⁻¹ᵁ U)
  have : IsDomain A := IsIntegral.component_integral U
  have : IsDomain B := IsIntegral.component_integral (f ⁻¹ᵁ U)
  let : Algebra A B := (f.app U).hom.toAlgebra
  have : Module.Finite A B := f.finite_app U hU
  have hcompat : ∀ a : A, functionFieldMap f (X.germToFunctionField U a) =
      Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) :=
    functionFieldMap_germToFunctionField f U
  have hmap : Function.Injective (f.app U).hom := by
    intro a b hab
    apply X.germToFunctionField_injective U
    apply (functionFieldMap f).injective
    rw [hcompat a, hcompat b]
    exact congrArg _ hab
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hmap
  let : Algebra A Y.functionField :=
    ((functionFieldMap f).comp (X.germToFunctionField U).hom).toAlgebra
  have : IsScalarTower A X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B Y.functionField :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext hcompat)
  have : IsFractionRing A X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsFractionRing B Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y (f ⁻¹ᵁ U) (hU.preimage f)
  apply Module.rank_lt_aleph0_iff.mp
  rw [Algebra.IsAlgebraic.rank_of_isFractionRing A X.functionField B Y.functionField]
  exact Module.rank_lt_aleph0 A B

/-- For a finite surjective morphism of varieties over a field of characteristic `0`, the degree
`deg f` is invertible on `X`: it is a positive integer, hence a unit of `k ⊆ Γ(X, ⊤)`. -/
private theorem isUnit_finiteDegree {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsFinite f] :
    IsUnit (finiteDegree f : Γ(X, ⊤)) := by
  have hpos : 0 < finiteDegree f := by
    let := functionFieldMapAlgebra f
    have := finite_functionField f
    exact Module.finrank_pos
  let φ : k →+* Γ(X, ⊤) := sX.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hk : IsUnit (finiteDegree f : k) := (Nat.cast_ne_zero.mpr hpos.ne').isUnit
  simpa only [map_natCast] using hk.map φ

section

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsDominant f]
  [IsIntegralHom f] [IsNormal X] (hdeg : IsUnit (finiteDegree f : Γ(X, ⊤)))

omit [IsIntegralHom f] [IsNormal X] in
include hdeg in
private theorem natCast_finiteDegree_ne_zero : (finiteDegree f : X.functionField) ≠ 0 := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  simpa using (hdeg.map (X.germToFunctionField ⊤).hom).ne_zero

include hdeg in
/-- When `d = deg f` is a unit on `X`, `d⁻¹ · Tr_{Y/X}` sends regular functions on `f⁻¹ U` to
regular functions on `U`. -/
private theorem exists_germToFunctionField_eq_inv_mul_fieldTrace (U : X.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, f ⁻¹ᵁ U)) :
    ∃ t : Γ(X, U), X.germToFunctionField U t =
      (finiteDegree f : X.functionField)⁻¹ * fieldTrace f (Y.germToFunctionField (f ⁻¹ᵁ U) s) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_fieldTrace f U s
  refine ⟨X.presheaf.map (homOfLE le_top).op ↑hdeg.unit⁻¹ * t, ?_⟩
  rw [map_mul, germToFunctionField_map, ht, map_units_inv, IsUnit.unit_spec, map_natCast]

open Classical in
/-- The section `d⁻¹ · Tr_{Y/X}(s)` of `𝒪_X` over `U`, for `s` a section of `𝒪_Y` over `f⁻¹ U`. -/
private noncomputable def traceSection (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)) : Γ(X, U) :=
  if _ : Nonempty U then
    (exists_germToFunctionField_eq_inv_mul_fieldTrace f hdeg U s).choose
  else 0

private theorem germToFunctionField_traceSection (U : X.Opens) [Nonempty U] (s : Γ(Y, f ⁻¹ᵁ U)) :
    X.germToFunctionField U (traceSection f hdeg U s) =
      (finiteDegree f : X.functionField)⁻¹ * fieldTrace f (Y.germToFunctionField (f ⁻¹ᵁ U) s) := by
  simp only [traceSection, ‹Nonempty U›, dite_true]
  exact (exists_germToFunctionField_eq_inv_mul_fieldTrace f hdeg U s).choose_spec

private theorem traceSection_add (U : X.Opens) (a b : Γ(Y, f ⁻¹ᵁ U)) :
    traceSection f hdeg U (a + b) = traceSection f hdeg U a + traceSection f hdeg U b :=
  eq_of_germToFunctionField_eq <| by
    intro
    simp only [map_add, germToFunctionField_traceSection, fieldTrace_add, mul_add]

private theorem traceSection_mul (U : X.Opens) (r : Γ(X, U)) (a : Γ(Y, f ⁻¹ᵁ U)) :
    traceSection f hdeg U (f.app U r * a) = r * traceSection f hdeg U a :=
  eq_of_germToFunctionField_eq <| by
    intro
    rw [map_mul, germToFunctionField_traceSection, germToFunctionField_traceSection, map_mul,
      ← functionFieldMap_germToFunctionField, fieldTrace_functionFieldMap_mul, mul_left_comm]

private theorem traceSection_app (U : X.Opens) (r : Γ(X, U)) :
    traceSection f hdeg U (f.app U r) = r :=
  eq_of_germToFunctionField_eq <| by
    intro
    rw [germToFunctionField_traceSection, ← functionFieldMap_germToFunctionField,
      fieldTrace_functionFieldMap,
      inv_mul_cancel_left₀ (natCast_finiteDegree_ne_zero f hdeg)]

private theorem traceSection_map {U V : X.Opens} (i : V ⟶ U) (a : Γ(Y, f ⁻¹ᵁ U)) :
    traceSection f hdeg V (Y.presheaf.map (homOfLE (f.preimage_mono i.le)).op a) =
      X.presheaf.map i.op (traceSection f hdeg U a) :=
  eq_of_germToFunctionField_eq <| by
    intro
    have : Nonempty U := ⟨⟨_, i.le (Classical.arbitrary V).2⟩⟩
    rw [germToFunctionField_traceSection, germToFunctionField_map, germToFunctionField_map,
      germToFunctionField_traceSection]

end

/-- The general splitting: for `deg f` invertible on `X`, `d⁻¹ · Tr_{Y/X}` is an `𝒪_X`-linear
left inverse of `f^#`. -/
private theorem exists_comp_eq_id_of_isUnit {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIntegralHom f] [IsNormal X]
    (hdeg : IsUnit (finiteDegree f : Γ(X, ⊤))) :
    ∃ τ : (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
        SheafOfModules.unit X.ringCatSheaf,
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ τ = 𝟙 _ := by
  refine ⟨⟨{ app U := ConcreteCategory.ofHom
              { toFun := traceSection f hdeg U.unop
                map_add' := traceSection_add f hdeg U.unop
                map_smul' := traceSection_mul f hdeg U.unop }
             naturality := fun i => by ext a; exact traceSection_map f hdeg i.unop a }⟩, ?_⟩
  ext U : 3
  exact LinearMap.ext (traceSection_app f hdeg U.unop)

end MMP.Proofs.lem_km2c_finite_trace_splitting

attribute [local instance] MMP.Proofs.lem_km2c_finite_trace_splitting.nonempty_preimage

namespace MMP.Mori

open MMP.Proofs.lem_km2c_finite_trace_splitting in
/-- **The trace splits `f^#`.** For a finite surjective morphism `f : Y ⟶ X` of varieties over a
field of characteristic `0` with `X` normal, the structure map `𝒪_X ⟶ f_* 𝒪_Y` has an
`𝒪_X`-linear left inverse, namely `d⁻¹ · Tr_{Y/X}` with `d = deg f`. -/
@[mmp "lem_km2c_finite_trace_splitting"]
public theorem exists_unitToPushforwardObjUnit_comp_eq_id {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsVariety k sX] [IsVariety k sY] (f : Y ⟶ X) (_hf : f ≫ sX = sY)
    [IsFinite f] [Surjective f] [IsNormal X] :
    ∃ τ : (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
        SheafOfModules.unit X.ringCatSheaf,
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ τ = 𝟙 _ :=
  exists_comp_eq_id_of_isUnit f (isUnit_finiteDegree sX f)

end MMP.Mori

end

/-!
## Sections of divisorial sheaves along a proper birational morphism

Let `f : Y ⟶ X` be a proper birational morphism of normal varieties over a field `k`, and identify
`K(Y) = K(X)` through `f^* : K(X) ≃ K(Y)`. If `B_Y` is a divisor on `Y` and `B` a divisor on `X`
such that, for every prime divisor `P` of `X`, the coefficient of its birational transform
`f⁻¹_* P` in `B_Y` is at most the coefficient of `P` in `B`, then `H⁰(Y, B_Y) ⊆ H⁰(X, B)` inside
the common function field.

### Main results

* `MMP.Mori.Divisor.exists_functionFieldMap_eq_of_isBirationalMorphism`: every global section of
  `𝒪_Y(B_Y)` is the pull-back `f^*φ` of a global section `φ` of `𝒪_X(B)`.

### Implementation notes

The inclusion `H⁰(Y, B_Y) ⊆ H⁰(X, B)` under `K(Y) = K(X)` is stated as: for every
`σ ∈ H⁰(Y, 𝒪_Y(B_Y))` there is `τ ∈ H⁰(X, 𝒪_X(B))` with `f^* τ = σ` in `K(Y)`, the sections
read as rational functions (`MMP.Mori.Divisor.sectionToRationalFunctions`) and these as elements
of the function fields (`MMP.Mori.rationalFunctionsEquivFunctionField`); `f^*` is
`AlgebraicGeometry.functionFieldMap f`, which is bijective for a birational morphism.

The birational transform `f⁻¹_* P` is `MMP.Mori.inverseTransformPrimeDivisor f P`, which is `none`
when `P` does not meet the locus over which `f` is an isomorphism; for such `P` the hypothesis
asks nothing. For `f` proper and `X` normal there is no such `P`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.5
-/

section

universe u

open CategoryTheory Opposite MMP.Mori MMP.Mori.Divisor
open AlgebraicGeometry hiding IsVariety PrimeDivisor

namespace MMP.Proofs.lem_km3a_sections_push_forward

section Generic

variable {W : Scheme.{u}} [IsIntegral W]

private theorem irreducibleComponent_eq_univ (Z : irreducibleComponents W) :
    (Z.1 : Set W) = Set.univ :=
  (irreducibleComponents_eq_singleton (X := W) ▸ Z.2 : Z.1 ∈ ({Set.univ} : Set (Set W)))

private theorem irreducibleComponents_ext (Z Z' : irreducibleComponents W) : Z = Z' :=
  Subtype.ext ((irreducibleComponent_eq_univ Z).trans (irreducibleComponent_eq_univ Z').symm)

private theorem nonempty_irreducibleComponents : Nonempty (irreducibleComponents W) := by
  rw [irreducibleComponents_eq_singleton]; exact ⟨⟨_, rfl⟩⟩

/-- Reading a component of a rational function at the generic point is bijective. -/
private theorem stalkSpecializes_bijective (Z : irreducibleComponents W) :
    Function.Bijective (W.presheaf.stalkSpecializes
      (genericPoint_specializes (componentGenericPoint W Z))).hom := by
  have key : ∀ (p : W) (hp : p = genericPoint W),
      Function.Bijective (W.presheaf.stalkSpecializes (genericPoint_specializes p)).hom := by
    rintro p rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact Function.bijective_id
  exact key _ (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z)

/-- The identification `K(W) ≃ k(W)` reads a rational function at the generic point. -/
private theorem rationalFunctionsEquivFunctionField_apply (r : RationalFunctions W)
    (Z : irreducibleComponents W) :
    rationalFunctionsEquivFunctionField W r =
      W.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint W Z)) (r Z) := by
  haveI : Finite (irreducibleComponents W) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  obtain ⟨U, hU, s, hs⟩ := W.presheaf.exists_germ_eq (r Z)
  have hd : Dense (U : Set W) := U.isOpen.dense ⟨_, hU⟩
  have hg : genericPoint W ∈ U := (genericPoint_specializes _).mem_open U.isOpen hU
  have h1 : (rationalFunctionsEquivStalks W).symm r = Stacks.Chow.ofSection W ⟨U, hd⟩ s := by
    rw [RingEquiv.symm_apply_eq]
    funext Z'
    obtain rfl := irreducibleComponents_ext Z Z'
    rw [rationalFunctionsEquivStalks, (Stacks.Chow.rationalFunctionsEquivStalks W).2 ⟨U, hd⟩ s Z hU]
    exact hs.symm
  change (Stacks.Chow.rationalFunctionsEquivFunctionField W).1
    ((rationalFunctionsEquivStalks W).symm r) = _
  rw [h1]
  refine ((Stacks.Chow.rationalFunctionsEquivFunctionField W).2 ⟨U, hd⟩ s hg).trans ?_
  rw [← hs, TopCat.Presheaf.germ_stalkSpecializes_apply]

end Generic

section Valuation

variable {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- Reading the generization `𝒪_{W,P} → 𝒪_{W,η}` in the function field is the algebra map. -/
private theorem stalkSpecializes_toComponent (P : MMP.Mori.PrimeDivisor W) (b : P.localRing) :
    W.presheaf.stalkSpecializes (genericPoint_specializes _) (P.toComponent.hom b) =
      algebraMap (W.presheaf.stalk P.genericPoint) W.functionField b := by
  change (P.toComponent ≫ W.presheaf.stalkSpecializes _).hom b = _
  rw [MMP.Mori.PrimeDivisor.toComponent, MMP.Mori.stalkToRationalFunctions,
    TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- `v_P(u ϖⁿ) = n` for a unit `u` and a uniformizer `ϖ` of `𝒪_{W,P}`. -/
private theorem valuation_toComponent_unit_mul_pow (P : MMP.Mori.PrimeDivisor W)
    (u : P.localRingˣ) {ϖ : P.localRing} (hϖ : Irreducible ϖ) (n : ℕ) :
    P.valuation (P.toComponent.hom ((u : P.localRing) * ϖ ^ n)) = WithZero.exp 1 ^ n := by
  rw [map_mul, map_pow, map_mul, map_pow, P.valuation_toComponent_of_isUnit u.isUnit,
    P.valuation_toComponent_of_irreducible hϖ, one_mul]

end Valuation

section Transfer

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] (g : Y ⟶ X) [IsDominant g]

/-- `g^*` on function fields extends `𝒪_{X,x} → 𝒪_{Y,y}` for `g y = x`. -/
private theorem functionFieldMap_algebraMap_of_eq {y : Y} {x : X} (hxy : g y = x)
    (a : X.presheaf.stalk x) :
    functionFieldMap g (algebraMap _ X.functionField a) =
      algebraMap _ Y.functionField
        ((g.stalkMap y).hom ((X.presheaf.stalkCongr (Inseparable.of_eq hxy.symm)).hom.hom a)) := by
  subst hxy
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  exact functionFieldMap_algebraMap_stalk g y a

/-- **Valuations agree along an isomorphism of local rings.** If `g` maps the generic point of
`P'` to that of `P` and induces an isomorphism `𝒪_{X,P} ≅ 𝒪_{Y,P'}`, then `v_{P'}(g^* x) = v_P(x)`
for every `x ∈ K(X)`. -/
private theorem valuation_eq_of_isIso_stalkMap (P : MMP.Mori.PrimeDivisor X)
    (P' : MMP.Mori.PrimeDivisor Y) (hη : g P'.genericPoint = P.genericPoint)
    [IsIso (g.stalkMap P'.genericPoint)]
    (x : X.presheaf.stalk (componentGenericPoint X P.component))
    (y : Y.presheaf.stalk (componentGenericPoint Y P'.component))
    (h : Y.presheaf.stalkSpecializes (genericPoint_specializes _) y =
      functionFieldMap g (X.presheaf.stalkSpecializes (genericPoint_specializes _) x)) :
    P'.valuation y = P.valuation x := by
  let e : P.localRing ≃+* P'.localRing :=
    (X.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).commRingCatIsoToRingEquiv.trans
      (asIso (g.stalkMap P'.genericPoint)).commRingCatIsoToRingEquiv
  have he : ∀ a : P.localRing, functionFieldMap g (algebraMap _ X.functionField a) =
      algebraMap _ Y.functionField (e a) := fun a => functionFieldMap_algebraMap_of_eq g hη a
  -- `v_{P'} ∘ e = v_P` on `𝒪_{X,P}`
  have := P.isDiscreteValuationRing_localRing
  have := P'.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  have hϖ' : Irreducible (e ϖ) := (MulEquiv.irreducible_iff e.toMulEquiv).mpr hϖ
  have hv : ∀ c : P.localRing,
      P'.valuation (P'.toComponent.hom (e c)) = P.valuation (P.toComponent.hom c) := by
    intro c
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    rw [valuation_toComponent_unit_mul_pow P v hϖ n,
      ← valuation_toComponent_unit_mul_pow P' (Units.map e.toMonoidHom v) hϖ' n, map_mul, map_pow]
    rfl
  -- write `x` as a fraction `a / s`
  letI := P.toComponent.hom.toAlgebra
  haveI := isFractionRing_stalkToRationalFunctions P.genericPoint_mem_component
  obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors P.localRing) x
  simp only [RingHom.algebraMap_toAlgebra] at hx
  have hs0 : P.valuation (P.toComponent.hom s) ≠ 0 := by
    obtain ⟨n, v, hsv⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.coe_ne_zero s) hϖ
    rw [hsv, valuation_toComponent_unit_mul_pow P v hϖ n]
    exact pow_ne_zero _ WithZero.exp_ne_zero
  have hy : y * P'.toComponent.hom (e s) = P'.toComponent.hom (e a) := by
    apply (stalkSpecializes_bijective P'.component).1
    rw [map_mul, h, stalkSpecializes_toComponent, stalkSpecializes_toComponent, ← he, ← he,
      ← stalkSpecializes_toComponent, ← stalkSpecializes_toComponent, ← map_mul, ← map_mul, hx]
  have h1 := congrArg P'.valuation hy
  rw [map_mul, hv, hv, ← hx, map_mul] at h1
  exact mul_right_cancel₀ hs0 h1

/-- Orders `≥ -b'` along `P'` transfer to orders `≥ -b` along `P` for `b' ≤ b`, through the
identification of `v_{P'}` with `v_P`. -/
private theorem ordGE_of_isIso_stalkMap (P : MMP.Mori.PrimeDivisor X)
    (P' : MMP.Mori.PrimeDivisor Y) (hη : g P'.genericPoint = P.genericPoint)
    [IsIso (g.stalkMap P'.genericPoint)] {b b' : ℤ} (hb : b' ≤ b)
    (x : X.presheaf.stalk (componentGenericPoint X P.component))
    (y : Y.presheaf.stalk (componentGenericPoint Y P'.component))
    (h : Y.presheaf.stalkSpecializes (genericPoint_specializes _) y =
      functionFieldMap g (X.presheaf.stalkSpecializes (genericPoint_specializes _) x))
    (hy : P'.OrdGE (-b') y) : P.OrdGE (-b) x := by
  rcases hy with hy | hy
  · left
    rw [hy, map_zero, eq_comm, map_eq_zero_iff _ (functionFieldMap g).injective] at h
    exact (stalkSpecializes_bijective P.component).1 (h.trans (map_zero _).symm)
  · right
    rw [← valuation_eq_of_isIso_stalkMap g P P' hη x y h]
    exact (WithZero.exp_le_exp.mpr (neg_le_neg hb)).trans hy

end Transfer

section Divisor

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (sX : X ⟶ Spec (.of k))
  (g : Y ⟶ X) (hX : MMP.Mori.IsVariety k sX) (hY : MMP.Mori.IsVariety k (g ≫ sX)) [IsProper g]
  (hg : IsBirationalMorphism g)

include hX hY hg in
/-- The generic point of every prime divisor of `X` lies in the biregular locus of `g`. -/
private theorem genericPoint_mem_biregularLocus (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∈ biregularLocus g := by
  obtain ⟨V, hV2, hVi⟩ := exists_isIso_morphismRestrict_two_le_closedsCodimension k sX (g ≫ sX)
    ⟨hX, ‹IsNormal X›⟩ hY g rfl hg
  refine le_biregularLocus hVi ?_
  by_contra hP
  have hsub : ((TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint :
      TopologicalSpace.IrreducibleCloseds X) : Set X) ⊆ (V.compl : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hP) V.compl.isClosed
  have h4 := le_closedsCodimension_iff.mp hV2 _ hsub
  rw [codimension_eq_coheight, show TopologicalSpace.IrreducibleCloseds.closureSingleton
      P.genericPoint = (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
    Order.coheight_orderIso, P.coheight_genericPoint] at h4
  exact absurd h4 (by decide)

include hX hY hg in
/-- Every prime divisor `P` of `X` has a birational transform `P' = g⁻¹_* P`, whose generic point
lies over that of `P`, with `g` an isomorphism of local rings `𝒪_{X,P} ≅ 𝒪_{Y,P'}`. -/
private theorem exists_inverseTransformPrimeDivisor_eq_some (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor Y, inverseTransformPrimeDivisor g P = some P' ∧
      g P'.genericPoint = P.genericPoint ∧ IsIso (g.stalkMap P'.genericPoint) := by
  have hP := genericPoint_mem_biregularLocus sX g hX hY hg P
  haveI := hg.isDominant
  obtain ⟨y, hy⟩ := g.surjective P.genericPoint
  have hco : Order.coheight y = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g (hy ▸ hP), hy]
    exact P.coheight_genericPoint
  let P' : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco
  have hgen : P'.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hco
  have hη : g P'.genericPoint = P.genericPoint := by rw [hgen, hy]
  have hV : g P'.genericPoint ∈ biregularLocus g := hη ▸ hP
  exact ⟨P',
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη hV,
    hη, MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus g hV⟩

end Divisor

end MMP.Proofs.lem_km3a_sections_push_forward

namespace MMP.Mori.Divisor

open MMP.Proofs.lem_km3a_sections_push_forward in
/-- **Sections push forward along a proper birational morphism.** Let `f : Y ⟶ X` be a proper
birational morphism of normal varieties over `k`, `B_Y` a divisor on `Y` and `B` a divisor on `X`
such that the coefficient in `B_Y` of the birational transform `f⁻¹_* P` of every prime divisor
`P` of `X` is at most the coefficient of `P` in `B`. Then every global section `σ` of
`𝒪_Y(B_Y)` is, in `K(Y) = K(X)`, a global section of `𝒪_X(B)`: `σ = f^* τ` for some `τ`. -/
@[mmp "lem_km3a_sections_push_forward"]
public theorem exists_functionFieldMap_eq_of_isBirationalMorphism {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) (hX : IsVariety k sX) (hY : IsVariety k (f ≫ sX))
    [IsProper f] (hf : IsBirationalMorphism f) (BY : Divisor Y) (B : Divisor X)
    (hB : ∀ (P : PrimeDivisor X) (P' : PrimeDivisor Y),
      inverseTransformPrimeDivisor f P = some P' → BY.coeff P' ≤ B.coeff P)
    (σ : BY.divisorialSubmodule ⊤) :
    haveI := hf.isDominant
    ∃ τ : B.divisorialSubmodule ⊤,
      functionFieldMap f (rationalFunctionsEquivFunctionField X (sectionToRationalFunctions τ)) =
        rationalFunctionsEquivFunctionField Y (sectionToRationalFunctions σ) := by
  haveI := hf.isDominant
  obtain ⟨s, hs⟩ := hf.functionFieldMap_bijective.2
    (rationalFunctionsEquivFunctionField Y (sectionToRationalFunctions σ))
  let φ : ToType ((rationalFunctionsPresheaf X).obj (op ⊤)) := fun Z =>
    (RingEquiv.ofBijective _ (stalkSpecializes_bijective Z.1)).symm s
  have hφ : ∀ Z, X.presheaf.stalkSpecializes (genericPoint_specializes _) (φ Z) = s := fun Z =>
    (RingEquiv.ofBijective _ (stalkSpecializes_bijective Z.1)).apply_symm_apply s
  have hsec : B.IsDivisorialSection ⊤ φ := by
    intro P hP
    obtain ⟨P', hT, hη, hiso⟩ := exists_inverseTransformPrimeDivisor_eq_some sX f hX hY hf P
    have hyP' : P'.genericPoint ∈ P'.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have hP'top : (P'.support ∩ ((⊤ : Y.Opens) : Set Y)).Nonempty := ⟨_, hyP', trivial⟩
    refine ordGE_of_isIso_stalkMap f P P' hη (hB P P' hT) _ _ ?_ (σ.2 P' hP'top)
    erw [hφ ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩]
    rw [hs, rationalFunctionsEquivFunctionField_apply _ P'.component]
    rfl
  refine ⟨⟨φ, hsec⟩, ?_⟩
  obtain ⟨ZX⟩ := nonempty_irreducibleComponents (W := X)
  rw [rationalFunctionsEquivFunctionField_apply _ ZX]
  exact (congrArg (functionFieldMap f) (hφ ⟨ZX, trivial⟩)).trans hs

end MMP.Mori.Divisor

end

/-!
## Sections of `f^*D + A` for an effective exceptional divisor `A`

Let `f : Y ⟶ X` be a proper birational morphism of normal varieties over a field `k`, and
identify `K(Y) = K(X)` through `f^* : K(X) ≃ K(Y)`. Let `D` be a Cartier divisor on `X` and `A`
an effective Cartier divisor on `Y` all of whose components are `f`-exceptional. Then for every
open `U ⊆ X` the identity of rational functions `φ ↦ f^*φ` is an isomorphism
`H⁰(U, D) ≃ H⁰(f⁻¹U, f^*D + A)`. In terms of sections it is `σ ↦ f^*σ · s_A`, where
`f^*σ ∈ H⁰(f⁻¹U, f^*D)` and `s_A` is the canonical section of `𝒪_Y(A)`.

### Main results

* `MMP.Mori.Divisor.exists_addEquiv_divisorialSubmodule_add_of_isExceptional`: the isomorphism
  `H⁰(U, D) ≃ H⁰(f⁻¹U, f^*D + A)`, characterised by `f^*φ = φ` in `K(Y) = K(X)`, together with
  its factorisation through `H⁰(f⁻¹U, f^*D)`.

### Implementation notes

A section of `𝒪_X(D)` over `U` is an element of `𝒦_X(U) = ∏_{η_Z ∈ U} 𝒪_{X,η_Z}`
(`MMP.Mori.Divisor.divisorialSubmodule`); for integral `X` its component at the generic point is
read in the function field through `TopCat.Presheaf.stalkSpecializes` along the specialization
of the generic point, and `f^*` on function fields is `AlgebraicGeometry.functionFieldMap f`.
The pull-back `f^*D` is any divisor `D_Y` with `D.IsPullback f hD D_Y`, where `hD` is the
condition that `f` maps the generic point of `Y` outside `Supp D` (automatic for a dominant `f`).
The canonical section `s_A` of `𝒪_Y(A)` is the constant function `1`, so multiplication by `s_A`
is the inclusion `𝒪_Y(f^*D) ⊆ 𝒪_Y(f^*D + A)` (`Submodule.inclusion`), and the section form of
the statement is that `e σ` is the image of the section `f^*σ` of `𝒪_Y(f^*D)` under this
inclusion. The statement is over an arbitrary open `U`, the source's global statement being the
case `U = ⊤`; the argument is local on `X`. The isomorphism is stated as an additive
equivalence; since it is the identity on rational functions, it is linear over `Γ(X, U)` acting
through `f`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.9
-/

section

universe u

open CategoryTheory Opposite MMP.Mori MMP.Mori.Divisor
open AlgebraicGeometry hiding IsVariety PrimeDivisor

namespace MMP.Proofs.lem_km3a_sections_exceptional_pullback

open MMP.Proofs.lem_km3a_sections_push_forward MMP.Proofs.lem_km2c_trace_regular

section Generic

variable {W : Scheme.{u}} [IsIntegral W]

/-- Two sections of `𝒦_W` over `V` with the same rational functions are equal. -/
private theorem rationalFunctions_ext {V : W.Opens}
    {φ ψ : ToType ((rationalFunctionsPresheaf W).obj (op V))}
    (h : ∀ (Z : irreducibleComponents W) (hZ : componentGenericPoint W Z ∈ V),
      W.presheaf.stalkSpecializes (genericPoint_specializes _) (φ ⟨Z, hZ⟩) =
        W.presheaf.stalkSpecializes (genericPoint_specializes _) (ψ ⟨Z, hZ⟩)) :
    φ = ψ :=
  funext fun Z => (stalkSpecializes_bijective Z.1).1 (h Z.1 Z.2)

end Generic

section Order

/-- If `v * u = 1`, `v` has order `≥ n` along `E` and `u * x` is regular along `E`, then `x` has
order `≥ n` along `E`. -/
private theorem ordGE_of_mul_left {W : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W]
    {E : MMP.Mori.PrimeDivisor W} {n : ℤ}
    {u v x : W.presheaf.stalk (componentGenericPoint W E.component)} (huv : v * u = 1)
    (hv : E.OrdGE n v) (h : E.OrdGE 0 (u * x)) : E.OrdGE n x := by
  simpa [← mul_assoc, huv] using hv.mul h

end Order

section Sections

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (sX : X ⟶ Spec (.of k))
  (g : Y ⟶ X) (hX : MMP.Mori.IsVariety k sX) (hY : MMP.Mori.IsVariety k (g ≫ sX)) [IsProper g]
  (hg : IsBirationalMorphism g) (B : Divisor X) (hBc : B.IsCartier)
  (hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ B.supp) (BY : Divisor Y)
  (hBY : B.IsPullback g hB BY) (E : Divisor Y) (hEc : E.IsCartier) (hE : 0 ≤ E)
  (hEexc : ∀ P : MMP.Mori.PrimeDivisor Y, E.coeff P ≠ 0 →
    RationalMap.IsExceptional g.toRationalMap P)

/-- `τ` over `g⁻¹U` has the rational function `g^*φ`, where `φ` is that of `σ` over `U`. -/
private def IsPullbackSection {M : Divisor X} {N : Divisor Y} [IsDominant g] {U : X.Opens}
    (σ : M.divisorialSubmodule U) (τ : N.divisorialSubmodule (g ⁻¹ᵁ U)) : Prop :=
  ∀ (ZX : irreducibleComponents X) (hZX : componentGenericPoint X ZX ∈ U)
    (ZY : irreducibleComponents Y) (hZY : componentGenericPoint Y ZY ∈ g ⁻¹ᵁ U),
    Y.presheaf.stalkSpecializes (genericPoint_specializes _) (τ.1 ⟨ZY, hZY⟩) =
      functionFieldMap g (X.presheaf.stalkSpecializes (genericPoint_specializes _) (σ.1 ⟨ZX, hZX⟩))

/-- The generic point of a scheme dominating `X` through `g` lies over every nonempty open. -/
private theorem componentGenericPoint_mem_of_mem_preimage [IsDominant g] {U : X.Opens}
    (ZX : irreducibleComponents X) {ZY : irreducibleComponents Y}
    (hZY : componentGenericPoint Y ZY ∈ g ⁻¹ᵁ U) : componentGenericPoint X ZX ∈ U := by
  have h : g (componentGenericPoint Y ZY) ∈ U := hZY
  rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant,
    ← MMP.Fourfold.componentGenericPoint_eq_genericPoint ZX] at h

private theorem componentGenericPoint_mem_preimage [IsDominant g] {U : X.Opens}
    {ZX : irreducibleComponents X} (ZY : irreducibleComponents Y)
    (hZX : componentGenericPoint X ZX ∈ U) : componentGenericPoint Y ZY ∈ g ⁻¹ᵁ U := by
  change g _ ∈ U
  rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant,
    ← MMP.Fourfold.componentGenericPoint_eq_genericPoint ZX]

/-- Reading `fieldMap g` at the generic points is `g^*` on function fields. -/
private theorem stalkSpecializes_fieldMap [IsDominant g] (ZX : irreducibleComponents X)
    (ZY : irreducibleComponents Y) (a : X.presheaf.stalk (componentGenericPoint X ZX)) :
    Y.presheaf.stalkSpecializes (genericPoint_specializes _) (MMP.Fourfold.fieldMap g ZX ZY a) =
      functionFieldMap g (X.presheaf.stalkSpecializes (genericPoint_specializes _) a) := by
  obtain ⟨V, hV, b, rfl⟩ := X.presheaf.exists_germ_eq a
  rw [MMP.Fourfold.fieldMap_germ]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ]

section Assembly

variable [IsDominant g] {M : Divisor X} {N N' : Divisor Y}

private theorem IsPullbackSection.eq_right {U : X.Opens} {σ : M.divisorialSubmodule U}
    {τ τ' : N.divisorialSubmodule (g ⁻¹ᵁ U)} (h : IsPullbackSection g σ τ)
    (h' : IsPullbackSection g σ τ') : τ = τ' := by
  obtain ⟨ZX⟩ := nonempty_irreducibleComponents (W := X)
  exact Subtype.ext (rationalFunctions_ext fun ZY hZY =>
    (h ZX (componentGenericPoint_mem_of_mem_preimage g ZX hZY) ZY hZY).trans
      (h' ZX (componentGenericPoint_mem_of_mem_preimage g ZX hZY) ZY hZY).symm)

private theorem IsPullbackSection.eq_left {U : X.Opens} {σ σ' : M.divisorialSubmodule U}
    {τ : N.divisorialSubmodule (g ⁻¹ᵁ U)} (h : IsPullbackSection g σ τ)
    (h' : IsPullbackSection g σ' τ) : σ = σ' := by
  obtain ⟨ZY⟩ := nonempty_irreducibleComponents (W := Y)
  exact Subtype.ext (rationalFunctions_ext fun ZX hZX =>
    (functionFieldMap g).injective
      ((h ZX hZX ZY (componentGenericPoint_mem_preimage g ZY hZX)).symm.trans
        (h' ZX hZX ZY (componentGenericPoint_mem_preimage g ZY hZX))))

private theorem IsPullbackSection.add {U : X.Opens} {σ σ' : M.divisorialSubmodule U}
    {τ τ' : N.divisorialSubmodule (g ⁻¹ᵁ U)} (h : IsPullbackSection g σ τ)
    (h' : IsPullbackSection g σ' τ') : IsPullbackSection g (σ + σ') (τ + τ') := by
  intro ZX hZX ZY hZY
  change Y.presheaf.stalkSpecializes _ (τ.1 ⟨ZY, hZY⟩ + τ'.1 ⟨ZY, hZY⟩) =
    functionFieldMap g (X.presheaf.stalkSpecializes _ (σ.1 ⟨ZX, hZX⟩ + σ'.1 ⟨ZX, hZX⟩))
  rw [map_add, map_add, map_add, h ZX hZX ZY hZY, h' ZX hZX ZY hZY]

end Assembly

include hX hY hg hBc hBY in
/-- The pull-back `g^*σ` of a section `σ` of `𝒪_X(B)` over `U` is a section of `𝒪_Y(g^*B)` over
`g⁻¹U`. -/
private theorem exists_isPullbackSection [IsDominant g] (U : X.Opens)
    (σ : B.divisorialSubmodule U) :
    ∃ τ : BY.divisorialSubmodule (g ⁻¹ᵁ U), IsPullbackSection g σ τ := by
  obtain ⟨ZX⟩ := nonempty_irreducibleComponents (W := X)
  let τ : ToType ((rationalFunctionsPresheaf Y).obj (op (g ⁻¹ᵁ U))) := fun Z =>
    MMP.Fourfold.fieldMap g ZX Z.1 (σ.1 ⟨ZX, componentGenericPoint_mem_of_mem_preimage g ZX Z.2⟩)
  have hτ : BY.IsDivisorialSection (g ⁻¹ᵁ U) τ := by
    intro E hE
    obtain ⟨y, hyE, hyU⟩ := hE
    obtain ⟨V, hyV, φ, hφ⟩ := hBc (g y)
    have hφW : B.IsLocalEquation (V ⊓ U) φ := hφ.mono inf_le_left
    have hE' : (E.support ∩ g ⁻¹ᵁ (V ⊓ U)).Nonempty := ⟨y, hyE, hyV, hyU⟩
    have hZXW : componentGenericPoint X ZX ∈ V ⊓ U :=
      componentGenericPoint_mem_of_mem_preimage g ZX (E.componentGenericPoint_mem_of_nonempty hE')
    -- `φ · σ` is regular on `V ∩ U`, by algebraic Hartogs
    have hsec : (0 : Divisor X).IsDivisorialSection (V ⊓ U)
        (fun Z => (φ : RationalFunctions X) Z.1 * σ.1 ⟨Z.1, inf_le_right (a := V) Z.2⟩) := by
      intro P hP
      have h1 : P.OrdGE (B.coeff P) ((φ : RationalFunctions X) P.component) :=
        Or.inr (le_of_eq (by rw [P.valuation_component, hφW P hP]))
      have h2 := h1.mul (σ.2 P (hP.mono (Set.inter_subset_inter_right _ inf_le_right)))
      rw [add_neg_cancel] at h2
      rw [DivisorWithCoeffs.coeff_zero, neg_zero]
      exact h2
    obtain ⟨b, hb⟩ := hsec.exists_eq
    have hbZ := congrFun hb ⟨ZX, hZXW⟩
    rw [toRationalFunctionsPresheaf_app_apply] at hbZ
    -- its pull-back is regular, so has order `≥ 0` along `E`
    have h0 : E.OrdGE 0 (MMP.Fourfold.fieldMap g ZX E.component
        ((φ : RationalFunctions X) ZX * σ.1 ⟨ZX, inf_le_right (a := V) hZXW⟩)) := by
      rw [← hbZ, MMP.Fourfold.fieldMap_germ]
      have := isDivisorialSection_algebraMap (le_refl (0 : Divisor Y)) (g.app (V ⊓ U) b) E hE'
      rw [DivisorWithCoeffs.coeff_zero, neg_zero] at this
      exact this
    -- `g^*φ⁻¹` has order `-BY_E` along `E`
    have hinv : E.OrdGE (-BY.coeff E) (MMP.Fourfold.fieldMap g ZX E.component
        (((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ZX)) := by
      refine Or.inr (le_of_eq ?_)
      have hv := MMP.Fourfold.valuation_fieldMap_of_isPullback g hBY hφW E hE' ZX
      have h1 : ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ZX *
          (φ : RationalFunctions X) ZX = 1 := congrFun (Units.inv_mul φ) ZX
      have h2 := congrArg (fun a => E.valuation (MMP.Fourfold.fieldMap g ZX E.component a)) h1
      simp only [map_mul, map_one, hv] at h2
      refine mul_right_cancel₀ (WithZero.exp_ne_zero (a := BY.coeff E)) ?_
      rw [h2, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    rw [map_mul] at h0
    exact ordGE_of_mul_left (by
      rw [← map_mul]; exact (congrArg _ (congrFun (Units.inv_mul φ) ZX)).trans (map_one _)) hinv h0
  refine ⟨⟨τ, hτ⟩, fun ZX' hZX' ZY hZY => ?_⟩
  obtain rfl := irreducibleComponents_ext ZX ZX'
  exact stalkSpecializes_fieldMap g ZX ZY _

include hX hg in
/-- Every prime divisor `P` of `X` is the image of a prime divisor `P'` of `Y` which is not
`g`-exceptional, with `g` an isomorphism of local rings `𝒪_{X,P} ≅ 𝒪_{Y,P'}`: since `𝒪_{X,P}` is a
valuation ring of `K(X) = K(Y)`, the stalk map at any point over the generic point of `P` is an
isomorphism. -/
private theorem exists_primeDivisor_map_genericPoint [IsDominant g] (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor Y, g P'.genericPoint = P.genericPoint ∧
      IsIso (g.stalkMap P'.genericPoint) ∧ ¬ RationalMap.IsExceptional g.toRationalMap P' := by
  have : IsSeparated sX := hX.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  obtain ⟨y, hy⟩ := g.surjective P.genericPoint
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (g y)) := by rw [hy]; infer_instance
  have hiso := MMP.Positivity.isIso_stalkMap_of_valuationRing g hg.functionFieldMap_bijective y
  have hco : Order.coheight y = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight y
    have h2 := ringKrullDim_stalk_eq_coheight (g y)
    rw [← ringKrullDim_eq_of_ringEquiv (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv, h2, hy,
      P.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco, ?_, ?_, ?_⟩
  · show g (AlgebraicGeometry.PrimeDivisor.genericPoint _) = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hy]
  · show IsIso (g.stalkMap (AlgebraicGeometry.PrimeDivisor.genericPoint _))
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]; exact hiso
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : TopologicalSpace.Closeds.closure
      (g '' ((AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco).idealSheaf.support : Set Y)) =
      ⟨closure {P.genericPoint}, isClosed_closure⟩ := by
    ext1
    change closure (g '' (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco).support) = _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
      closure_image_closure g.continuous, Set.image_singleton, hy]
    rfl
  have h3 : codimension
      (TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint) = 1 := by
    rw [codimension_eq_coheight, show TopologicalSpace.IrreducibleCloseds.closureSingleton
        P.genericPoint = (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint]
  rw [hcl]
  have h4 := MMP.Mori.closedsCodimension_coe
    (TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint)
  intro h
  exact absurd (h3 ▸ h4 ▸ h : (2 : ℕ∞) ≤ 1) (by decide)

/-- Over a point where `g` is an isomorphism of local rings, every element of `𝒪_{Y,y}` is the
pull-back of an element of `𝒪_{X,g y}`, read in the function fields. -/
private theorem exists_functionFieldMap_algebraMap_eq [IsDominant g] {y : Y} {x : X}
    (hxy : g y = x) [IsIso (g.stalkMap y)] (b : Y.presheaf.stalk y) :
    ∃ a : X.presheaf.stalk x, functionFieldMap g (algebraMap _ X.functionField a) =
      algebraMap _ Y.functionField b := by
  subst hxy
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (g.stalkMap y)).2 b
  exact ⟨a, functionFieldMap_algebraMap_stalk g y a⟩

/-- The hard step of the descent: if `g` is an isomorphism of local rings `𝒪_{X,P} ≅ 𝒪_{Y,P'}`
over the generic point of `P`, a rational function `x` on `X` whose pull-back is regular along
`P'` is regular along `P`. -/
private theorem ordGE_zero_of_ordGE_zero_fieldMap [IsDominant g] {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor Y} (hP : g P'.genericPoint = P.genericPoint)
    [IsIso (g.stalkMap P'.genericPoint)]
    {x : X.presheaf.stalk (componentGenericPoint X P.component)}
    (h : P'.OrdGE 0 (MMP.Fourfold.fieldMap g P.component P'.component x)) : P.OrdGE 0 x := by
  obtain ⟨b, hb⟩ : ∃ b : P'.localRing,
      P'.toComponent.hom b = MMP.Fourfold.fieldMap g P.component P'.component x := by
    rcases h with h | h
    · exact ⟨0, by rw [map_zero, h]⟩
    · exact P'.exists_toComponent_eq_of_one_le_valuation (by rwa [WithZero.exp_zero] at h)
  obtain ⟨a, ha⟩ := exists_functionFieldMap_algebraMap_eq g hP b
  obtain rfl : x = P.toComponent.hom a := (stalkSpecializes_bijective _).1 <|
    (functionFieldMap g).injective <| by
      rw [stalkSpecializes_toComponent, ha, ← stalkSpecializes_toComponent, hb,
        stalkSpecializes_fieldMap]
  by_cases ha0 : a = 0
  · exact Or.inl (by rw [ha0, map_zero])
  · exact Or.inr (by rw [WithZero.exp_zero]; exact P.one_le_valuation_toComponent ha0)

include hX hg hBc hBY hEexc in
/-- A family `φ` of rational functions on the components of `X` over `U`, all specializing to
`s`, is a section of `𝒪_X(B)` over `U` once `g^*s` is the rational function of a section `τ` of
`𝒪_Y(g^*B + E)` over `g⁻¹U`. -/
private theorem isDivisorialSection_of_stalkSpecializes_eq [IsDominant g] {U : X.Opens}
    (τ : (BY + E).divisorialSubmodule (g ⁻¹ᵁ U)) {s : X.functionField} {t : Y.functionField}
    (hs : functionFieldMap g s = t)
    (ht : ∀ (ZY : irreducibleComponents Y) (hZY : componentGenericPoint Y ZY ∈ g ⁻¹ᵁ U),
      Y.presheaf.stalkSpecializes (genericPoint_specializes _) (τ.1 ⟨ZY, hZY⟩) = t)
    {φ : ToType ((rationalFunctionsPresheaf X).obj (op U))}
    (hφ : ∀ Z, X.presheaf.stalkSpecializes (genericPoint_specializes _) (φ Z) = s) :
    B.IsDivisorialSection U φ := by
  intro P hP
  have hxU : P.genericPoint ∈ U := P.genericPoint_mem_of_nonempty hP
  obtain ⟨V, hxV, f, hf⟩ := hBc P.genericPoint
  have hfW : B.IsLocalEquation (V ⊓ U) f := hf.mono inf_le_left
  have hxP : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hPW : (P.support ∩ (V ⊓ U : X.Opens)).Nonempty := ⟨_, hxP, hxV, hxU⟩
  obtain ⟨P', hP'x, hiso, hnexc⟩ := exists_primeDivisor_map_genericPoint sX g hX hg P
  have hE0 : E.coeff P' = 0 := of_not_not fun h => hnexc (hEexc P' h)
  have hyP' : P'.genericPoint ∈ P'.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hP'W : (P'.support ∩ g ⁻¹ᵁ (V ⊓ U)).Nonempty :=
    ⟨_, hyP', show g P'.genericPoint ∈ V ⊓ U by rw [hP'x]; exact ⟨hxV, hxU⟩⟩
  have hP'U : (P'.support ∩ g ⁻¹ᵁ U).Nonempty :=
    hP'W.mono (Set.inter_subset_inter_right _ (g.preimage_mono inf_le_right))
  have hτP := τ.2 P' hP'U
  have hfP : P'.OrdGE (BY.coeff P') (MMP.Fourfold.fieldMap g P.component P'.component
      ((f : RationalFunctions X) P.component)) :=
    Or.inr (le_of_eq
      (MMP.Fourfold.valuation_fieldMap_of_isPullback g hBY hfW P' hP'W P.component).symm)
  have h0 := hfP.mul hτP
  rw [DivisorWithCoeffs.coeff_add, hE0, add_zero, add_neg_cancel] at h0
  have hτφ : τ.1 ⟨P'.component, P'.componentGenericPoint_mem_of_nonempty hP'U⟩ =
      MMP.Fourfold.fieldMap g P.component P'.component
        (φ ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩) :=
    (stalkSpecializes_bijective _).1 <| by
      rw [stalkSpecializes_fieldMap, ht]
      erw [hφ ⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩]
      exact hs.symm
  rw [hτφ, ← map_mul] at h0
  haveI := hiso
  have hd0 := ordGE_zero_of_ordGE_zero_fieldMap g hP'x h0
  have hinv : P.OrdGE (-B.coeff P)
      (((f⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) P.component) :=
    Or.inr (le_of_eq (by rw [P.valuation_component, MMP.Mori.PrimeDivisor.ord_inv, hfW P hPW]))
  exact ordGE_of_mul_left (congrFun (Units.inv_mul f) P.component) hinv hd0

include hX hY hg hBc hBY hEc hE hEexc in
/-- Every section of `𝒪_Y(g^*B + E)` over `g⁻¹U` is the pull-back of a section of `𝒪_X(B)` over
`U`. -/
private theorem exists_isPullbackSection_of_add [IsDominant g] (U : X.Opens)
    (τ : (BY + E).divisorialSubmodule (g ⁻¹ᵁ U)) :
    ∃ σ : B.divisorialSubmodule U, IsPullbackSection g σ τ := by
  classical
  have hbij := hg.functionFieldMap_bijective
  obtain ⟨ZX0⟩ := nonempty_irreducibleComponents (W := X)
  obtain ⟨ZY0⟩ := nonempty_irreducibleComponents (W := Y)
  by_cases hU : componentGenericPoint X ZX0 ∈ U
  swap
  · refine ⟨0, fun ZX hZX => ?_⟩
    obtain rfl := irreducibleComponents_ext ZX0 ZX
    exact absurd hZX hU
  have hY0 : componentGenericPoint Y ZY0 ∈ g ⁻¹ᵁ U := componentGenericPoint_mem_preimage g ZY0 hU
  set t := Y.presheaf.stalkSpecializes (genericPoint_specializes _) (τ.1 ⟨ZY0, hY0⟩) with ht_def
  obtain ⟨s, hs⟩ := hbij.2 t
  have ht : ∀ (ZY : irreducibleComponents Y) (hZY : componentGenericPoint Y ZY ∈ g ⁻¹ᵁ U),
      Y.presheaf.stalkSpecializes (genericPoint_specializes _) (τ.1 ⟨ZY, hZY⟩) = t := by
    intro ZY hZY
    obtain rfl := irreducibleComponents_ext ZY0 ZY
    rfl
  let φ : ToType ((rationalFunctionsPresheaf X).obj (op U)) := fun Z =>
    (RingEquiv.ofBijective _ (stalkSpecializes_bijective Z.1)).symm s
  have hφ : ∀ Z, X.presheaf.stalkSpecializes (genericPoint_specializes _) (φ Z) = s := fun Z =>
    (RingEquiv.ofBijective _ (stalkSpecializes_bijective Z.1)).apply_symm_apply s
  have hφsec : B.IsDivisorialSection U φ :=
    isDivisorialSection_of_stalkSpecializes_eq sX g hX hg B hBc hB BY hBY E hEexc τ hs ht hφ
  refine ⟨⟨φ, hφsec⟩, fun ZX hZX ZY hZY => ?_⟩
  change _ = functionFieldMap g (X.presheaf.stalkSpecializes _ (φ ⟨ZX, hZX⟩))
  rw [ht, hφ, hs]

end Sections

/-- Sections over `U` determined by their rational functions, with `g^*` mapping the sections of
`𝒪_X(M)` into those of `𝒪_Y(N)` and every section of `𝒪_Y(N')`, `N ≤ N'`, in the image, give the
additive equivalence `H⁰(U, M) ≃ H⁰(g⁻¹U, N')`. -/
private theorem exists_addEquiv_of_isPullbackSection {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (g : Y ⟶ X) [IsProper g] [IsDominant g] {M : Divisor X} {N N' : Divisor Y} (hN : N ≤ N')
    (U : X.Opens)
    (hA : ∀ σ : M.divisorialSubmodule U,
      ∃ τ : N.divisorialSubmodule (g ⁻¹ᵁ U), IsPullbackSection g σ τ)
    (hB : ∀ τ : N'.divisorialSubmodule (g ⁻¹ᵁ U),
      ∃ σ : M.divisorialSubmodule U, IsPullbackSection g σ τ) :
    ∃ e : M.divisorialSubmodule U ≃+ N'.divisorialSubmodule (g ⁻¹ᵁ U),
      ∀ σ : M.divisorialSubmodule U, IsPullbackSection g σ (e σ) ∧
        ∃ τ : N.divisorialSubmodule (g ⁻¹ᵁ U), IsPullbackSection g σ τ ∧
          e σ = Submodule.inclusion (divisorialSubmodule_mono hN _) τ := by
  choose fA hfA using hA
  choose fB hfB using hB
  let fwd : M.divisorialSubmodule U → N'.divisorialSubmodule (g ⁻¹ᵁ U) :=
    fun σ => Submodule.inclusion (divisorialSubmodule_mono hN _) (fA σ)
  have hfwd : ∀ σ, IsPullbackSection g σ (fwd σ) := hfA
  refine ⟨{ toFun := fwd, invFun := fB
            left_inv := fun σ => (hfB (fwd σ)).eq_left g (hfwd σ)
            right_inv := fun τ => (hfwd (fB τ)).eq_right g (hfB τ)
            map_add' := fun a b => (hfwd (a + b)).eq_right g ((hfwd a).add g (hfwd b)) },
    fun σ => ⟨hfwd σ, fA σ, hfA σ, rfl⟩⟩

end MMP.Proofs.lem_km3a_sections_exceptional_pullback

namespace MMP.Mori.Divisor

open MMP.Proofs.lem_km3a_sections_exceptional_pullback in
/-- **Sections of `f^*D + A`, `A` effective exceptional.** Let `f : Y ⟶ X` be a proper
birational morphism of normal varieties over `k`, `D` a Cartier divisor on `X` with pull-back
`D_Y = f^*D`, and `A` an effective Cartier divisor on `Y` all of whose components are
`f`-exceptional. Then for every open `U ⊆ X`, `φ ↦ f^*φ` is an isomorphism
`e : H⁰(U, D) ≃ H⁰(f⁻¹U, D_Y + A)`, and for every section `σ`, `e σ = f^*σ · s_A` with
`f^*σ ∈ H⁰(f⁻¹U, D_Y)`. -/
@[mmp "lem_km3a_sections_exceptional_pullback"]
public theorem exists_addEquiv_divisorialSubmodule_add_of_isExceptional {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) (hX : IsVariety k sX) (hY : IsVariety k (f ≫ sX))
    [IsProper f] (hf : IsBirationalMorphism f) (D : Divisor X) (hDc : D.IsCartier)
    (hD : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    (DY : Divisor Y) (hDY : D.IsPullback f hD DY)
    (A : Divisor Y) (hAc : A.IsCartier) (hA : 0 ≤ A)
    (hAexc : ∀ E : PrimeDivisor Y, A.coeff E ≠ 0 → RationalMap.IsExceptional f.toRationalMap E)
    (U : X.Opens) :
    haveI := hf.isDominant
    ∃ e : D.divisorialSubmodule U ≃+ (DY + A).divisorialSubmodule (f ⁻¹ᵁ U),
      ∀ σ : D.divisorialSubmodule U,
        (∀ (ZX : irreducibleComponents X) (hZX : componentGenericPoint X ZX ∈ U)
          (ZY : irreducibleComponents Y) (hZY : componentGenericPoint Y ZY ∈ f ⁻¹ᵁ U),
          Y.presheaf.stalkSpecializes (genericPoint_specializes _) ((e σ).1 ⟨ZY, hZY⟩) =
            functionFieldMap f
              (X.presheaf.stalkSpecializes (genericPoint_specializes _) (σ.1 ⟨ZX, hZX⟩))) ∧
          ∃ τ : DY.divisorialSubmodule (f ⁻¹ᵁ U),
            (∀ (ZX : irreducibleComponents X) (hZX : componentGenericPoint X ZX ∈ U)
              (ZY : irreducibleComponents Y) (hZY : componentGenericPoint Y ZY ∈ f ⁻¹ᵁ U),
              Y.presheaf.stalkSpecializes (genericPoint_specializes _) (τ.1 ⟨ZY, hZY⟩) =
                functionFieldMap f
                  (X.presheaf.stalkSpecializes (genericPoint_specializes _) (σ.1 ⟨ZX, hZX⟩))) ∧
              e σ = Submodule.inclusion
                (divisorialSubmodule_mono (le_add_of_nonneg_right hA) (f ⁻¹ᵁ U)) τ := by
  haveI := hf.isDominant
  exact exists_addEquiv_of_isPullbackSection f (le_add_of_nonneg_right hA) U
    (exists_isPullbackSection sX f hX hY hf D hDc hD DY hDY U)
    (exists_isPullbackSection_of_add sX f hX hY hf D hDc hD DY hDY A hAc hA hAexc U)

end MMP.Mori.Divisor

end

/-!
## Push-forward of `𝒪_Y(g^*B + E)` for an effective exceptional divisor `E`

Let `g : Y ⟶ X` be a proper birational morphism of normal varieties over a field `k`, `B` a
Cartier divisor on `X` and `E` an effective Cartier divisor on `Y` all of whose components are
`g`-exceptional, with canonical section `s_E`. Then for every open `U ⊆ X` the map
`σ ↦ g^*σ · s_E` is an isomorphism `H⁰(U, 𝒪_X(B)) ≃ H⁰(g⁻¹U, 𝒪_Y(g^*B + E))`; these maps commute
with restriction and are `𝒪_X`-linear, so they form an isomorphism of `𝒪_X`-modules
`𝒪_X(B) ≅ g_*𝒪_Y(g^*B + E)`.

### Main results

* `MMP.Mori.Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional`: the isomorphism
  `𝒪_X(B) ≅ g_*𝒪_Y(g^*B + E)`, characterised on sections over every open `U` by `g^*φ = φ` in
  `K(Y) = K(X)`, together with its factorisation through `H⁰(g⁻¹U, 𝒪_Y(g^*B))`.

### Implementation notes

A section of `𝒪_X(B)` over `U` is an element of `𝒦_X(U) = ∏_{η_Z ∈ U} 𝒪_{X,η_Z}`
(`MMP.Mori.Divisor.divisorialSubmodule`); for integral `X` its component at the generic point of
`X` is read in the function field through `TopCat.Presheaf.stalkSpecializes` along the
specialization of the generic point. The push-forward is
`AlgebraicGeometry.Scheme.Modules.pushforward`,
whose sections over `U` are the sections over `g ⁻¹ᵁ U`. The pull-back `g^*B` is any divisor
`B_Y` with `B.IsPullback g hB B_Y`. The canonical section `s_E` is the constant function `1`, so
multiplication by `s_E` is the inclusion `𝒪_Y(g^*B) ⊆ 𝒪_Y(g^*B + E)` (`Submodule.inclusion`).

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4, 3.5
-/

section

universe u

open CategoryTheory Opposite MMP.Mori MMP.Mori.Divisor
open AlgebraicGeometry hiding IsVariety PrimeDivisor

namespace MMP.Proofs.lem_km3a_sections_exceptional_twist

open MMP.Proofs.lem_km3a_sections_push_forward MMP.Proofs.lem_km3a_sections_exceptional_pullback
open MMP.Proofs.lem_km2c_trace_regular

section Generic

variable {W : Scheme.{u}} [IsIntegral W]

/-- The rational function of `r • φ` is the rational function of `r` times that of `φ`. -/
private theorem stalkSpecializes_smul {V : W.Opens} (r : Γ(W, V))
    (φ : ToType ((rationalFunctionsPresheaf W).obj (op V)))
    (Z : irreducibleComponents W) (hZ : componentGenericPoint W Z ∈ V) :
    W.presheaf.stalkSpecializes (genericPoint_specializes _) ((r • φ) ⟨Z, hZ⟩) =
      W.presheaf.germ V (genericPoint W) ((genericPoint_specializes _).mem_open V.isOpen hZ) r *
        W.presheaf.stalkSpecializes (genericPoint_specializes _) (φ ⟨Z, hZ⟩) := by
  rw [rationalFunctions_smul_apply, map_mul]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes_apply W.presheaf hZ _ r

end Generic

section Sections

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (g : Y ⟶ X) [IsProper g]

section Assembly

variable [IsDominant g] {M : Divisor X} {N N' : Divisor Y}

private theorem _root_.MMP.Proofs.lem_km3a_sections_exceptional_pullback.IsPullbackSection.smul
    {U : X.Opens} {σ : M.divisorialSubmodule U}
    {τ : N.divisorialSubmodule (g ⁻¹ᵁ U)} (h : IsPullbackSection g σ τ) (r : Γ(X, U)) :
    IsPullbackSection g (r • σ) (g.app U r • τ) := by
  intro ZX hZX ZY hZY
  change Y.presheaf.stalkSpecializes _ ((g.app U r • τ.1) ⟨ZY, hZY⟩) =
    functionFieldMap g (X.presheaf.stalkSpecializes _ ((r • σ.1) ⟨ZX, hZX⟩))
  rw [stalkSpecializes_smul, stalkSpecializes_smul, map_mul, h ZX hZX ZY hZY,
    functionFieldMap_germ]

private theorem _root_.MMP.Proofs.lem_km3a_sections_exceptional_pullback.IsPullbackSection.restrict
    {U V : X.Opens} (i : V ⟶ U)
    {σ : M.divisorialSubmodule U} {τ : N.divisorialSubmodule (g ⁻¹ᵁ U)}
    (h : IsPullbackSection g σ τ) :
    IsPullbackSection g (M.divisorialRestrict i σ)
      (N.divisorialRestrict (homOfLE (g.preimage_mono i.le)) τ) :=
  fun ZX hZX ZY hZY => h ZX (i.le hZX) ZY (g.preimage_mono i.le hZY)

/-- Sections over every open determined by their rational functions, with `g^*` mapping the
sections of `𝒪_X(M)` into those of `𝒪_Y(N)` and every section of `𝒪_Y(N')` with `N ≤ N'` in the
image, give the isomorphism `𝒪_X(M) ≅ g_*𝒪_Y(N')`. -/
private theorem exists_iso_of_isPullbackSection (hN : N ≤ N')
    (hA : ∀ (U : X.Opens) (σ : M.divisorialSubmodule U),
      ∃ τ : N.divisorialSubmodule (g ⁻¹ᵁ U), IsPullbackSection g σ τ)
    (hB : ∀ (U : X.Opens) (τ : N'.divisorialSubmodule (g ⁻¹ᵁ U)),
      ∃ σ : M.divisorialSubmodule U, IsPullbackSection g σ τ) :
    ∃ e : M.divisorialSheaf ≅ (Scheme.Modules.pushforward g).obj N'.divisorialSheaf,
      ∀ (U : X.Opens) (σ : M.divisorialSubmodule U),
        IsPullbackSection g σ (e.hom.app U σ : N'.divisorialSubmodule (g ⁻¹ᵁ U)) ∧
        ∃ τ : N.divisorialSubmodule (g ⁻¹ᵁ U), IsPullbackSection g σ τ ∧
          (e.hom.app U σ : N'.divisorialSubmodule (g ⁻¹ᵁ U)) =
            Submodule.inclusion (divisorialSubmodule_mono hN _) τ := by
  choose fA hfA using hA
  choose fB hfB using hB
  let fwd : ∀ U : X.Opens, M.divisorialSubmodule U → N'.divisorialSubmodule (g ⁻¹ᵁ U) :=
    fun U σ => Submodule.inclusion (divisorialSubmodule_mono hN _) (fA U σ)
  have hfwd : ∀ U σ, IsPullbackSection g σ (fwd U σ) := fun U σ => hfA U σ
  let hom : M.divisorialSheaf ⟶ (Scheme.Modules.pushforward g).obj N'.divisorialSheaf :=
    ⟨{ app U := ConcreteCategory.ofHom
        { toFun := fwd U.unop
          map_add' := fun a b => (hfwd _ (a + b)).eq_right g ((hfwd _ a).add g (hfwd _ b))
          map_smul' := fun r a => (hfwd _ (r • a)).eq_right g ((hfwd _ a).smul g r) }
       naturality := fun i => by
        ext a
        exact (hfwd _ _).eq_right g ((hfwd _ a).restrict g i.unop) }⟩
  let inv : (Scheme.Modules.pushforward g).obj N'.divisorialSheaf ⟶ M.divisorialSheaf :=
    ⟨{ app U := ConcreteCategory.ofHom
        { toFun := fB U.unop
          map_add' := fun a b => (hfB _ (a + b)).eq_left g ((hfB _ a).add g (hfB _ b))
          map_smul' := fun r a => (hfB _ (r • a)).eq_left g ((hfB _ a).smul g r) }
       naturality := fun i => by
        ext a
        exact (hfB _ _).eq_left g ((hfB _ a).restrict g i.unop) }⟩
  refine ⟨{ hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }, ?_⟩
  · refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext a
    exact (hfB U (fwd U a)).eq_left g (hfwd U a)
  · refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext a
    exact (hfwd U (fB U a)).eq_right g (hfB U a)
  · exact fun U σ => ⟨hfwd U σ, fA U σ, hfA U σ, rfl⟩

end Assembly

end Sections

end MMP.Proofs.lem_km3a_sections_exceptional_twist

namespace MMP.Mori.Divisor

open MMP.Proofs.lem_km3a_sections_exceptional_pullback
  MMP.Proofs.lem_km3a_sections_exceptional_twist in
/-- **Push-forward of `𝒪_Y(g^*B + E)`, `E` effective exceptional.** Let `g : Y ⟶ X` be a proper
birational morphism of normal varieties over `k`, `B` a Cartier divisor on `X` with pull-back
`B_Y = g^*B`, and `E` an effective Cartier divisor on `Y` all of whose components are
`g`-exceptional. Then there is an isomorphism of `𝒪_X`-modules
`e : 𝒪_X(B) ≅ g_*𝒪_Y(B_Y + E)` which, over every open `U`, sends a section `σ` to
`g^*σ · s_E`: the rational function of `e σ` is `g^*` of that of `σ`, and `e σ` is the image of a
section of `𝒪_Y(B_Y)` over `g⁻¹U` with the same rational function. -/
@[mmp "lem_km3a_sections_exceptional_twist"]
public theorem exists_iso_pushforward_divisorialSheaf_add_of_isExceptional {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) (hX : IsVariety k sX) (hY : IsVariety k (g ≫ sX))
    [IsProper g] (hg : IsBirationalMorphism g) (B : Divisor X) (hBc : B.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ B.supp)
    (BY : Divisor Y) (hBY : B.IsPullback g hB BY)
    (E : Divisor Y) (hEc : E.IsCartier) (hE : 0 ≤ E)
    (hEexc : ∀ P : PrimeDivisor Y, E.coeff P ≠ 0 → RationalMap.IsExceptional g.toRationalMap P) :
    haveI := hg.isDominant
    ∃ e : B.divisorialSheaf ≅ (Scheme.Modules.pushforward g).obj (BY + E).divisorialSheaf,
      ∀ (U : X.Opens) (σ : B.divisorialSubmodule U)
        (ZX : irreducibleComponents X) (hZX : componentGenericPoint X ZX ∈ U)
        (ZY : irreducibleComponents Y) (hZY : componentGenericPoint Y ZY ∈ g ⁻¹ᵁ U),
        Y.presheaf.stalkSpecializes (genericPoint_specializes _)
            ((e.hom.app U σ : (BY + E).divisorialSubmodule (g ⁻¹ᵁ U)).1 ⟨ZY, hZY⟩) =
          functionFieldMap g
            (X.presheaf.stalkSpecializes (genericPoint_specializes _) (σ.1 ⟨ZX, hZX⟩)) ∧
        ∃ τ : BY.divisorialSubmodule (g ⁻¹ᵁ U),
          Y.presheaf.stalkSpecializes (genericPoint_specializes _) (τ.1 ⟨ZY, hZY⟩) =
              functionFieldMap g
                (X.presheaf.stalkSpecializes (genericPoint_specializes _) (σ.1 ⟨ZX, hZX⟩)) ∧
            (e.hom.app U σ : (BY + E).divisorialSubmodule (g ⁻¹ᵁ U)) =
              Submodule.inclusion (divisorialSubmodule_mono (le_add_of_nonneg_right hE) _) τ := by
  haveI := hg.isDominant
  obtain ⟨e, he⟩ := exists_iso_of_isPullbackSection g (le_add_of_nonneg_right hE)
    (exists_isPullbackSection sX g hX hY hg B hBc hB BY hBY)
    (exists_isPullbackSection_of_add sX g hX hY hg B hBc hB BY hBY E hEc hE hEexc)
  refine ⟨e, fun U σ ZX hZX ZY hZY => ?_⟩
  obtain ⟨h₁, τ, h₂, h₃⟩ := he U σ
  exact ⟨h₁ ZX hZX ZY hZY, τ, h₂ ZX hZX ZY hZY, h₃⟩

end MMP.Mori.Divisor

end

/-!
## A small ample model of a flipping contraction is its flip

Let `f : X ⟶ Y` be a `(K + D)`-flipping contraction of normal varieties over a field `k`, and let
`r > 0` be an integer with `r D` integral. Suppose `g : Z ⟶ Y` is a projective birational
morphism over `k` from a normal variety `Z` whose exceptional set has codimension at least two,
and such that the birational transform `g⁻¹_* f_* (r K_X + r D)` is `ℚ`-Cartier and `g`-ample.
Then `g` is a `(K + D)`-flip of `f`: with `K_Z = g⁻¹_* f_* K_X` and `D⁺ = g⁻¹_* f_* D` one has
`r (K_Z + D⁺) = g⁻¹_* f_* (r K_X + r D)`, so `K_Z + D⁺` is `ℚ`-Cartier and `g`-ample.

### Main results

* `MMP.Mori.isFlip_of_isProjectiveMorphism`: a projective birational morphism `g : Z ⟶ Y` from a
  normal variety, small, on which `g⁻¹_* f_* (r K_X + r D)` is `ℚ`-Cartier and `g`-ample, is a
  `(K + D)`-flip of the flipping contraction `f`.

### Implementation notes

The birational transform `g⁻¹_* f_*` is `MMP.Mori.flipTransform f g`, applied here to the
`ℚ`-divisor `r • (K_X + D)`; integrality of `r D` is recorded as the existence of an integral
divisor `B` with `B = r • D` as `ℚ`-divisors.

### References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, proof of 6.4(2) via
  6.2.2.
-/

section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP MMP.Mori

namespace MMP.Mori

/-- Mapping prime divisors commutes with regarding a divisor as a `ℚ`-divisor. -/
public theorem DivisorWithCoeffs.mapPrimeDivisors_toQDivisor {X Y : Scheme.{u}}
    (φ : PrimeDivisor X → Option (PrimeDivisor Y)) (D : Divisor X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toQDivisor D) =
      Divisor.toQDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add A B hA hB => simp only [map_add, hA, hB]
  | single P n =>
    rw [Threefold.Resolution.toQDivisor_single, DivisorWithCoeffs.mapPrimeDivisors_single,
      DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ P with
    | none => simp
    | some E => exact (Threefold.Resolution.toQDivisor_single E n).symm

/-- The birational transform `g⁻¹_* f_*` commutes with regarding a divisor as a `ℚ`-divisor. -/
public theorem flipTransform_toQDivisor {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (D : Divisor X) :
    flipTransform f g (Divisor.toQDivisor D) = Divisor.toQDivisor (flipTransform f g D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, RationalMap.transformDivisor,
    inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors_toQDivisor]

end MMP.Mori

namespace MMP.Proofs.lem_km3c_small_ample_model_is_flip

/-- A `ℚ`-divisor is `ℚ`-Cartier as soon as a positive integral multiple of it is. -/
private theorem isQCartier_of_natCast_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {E : QDivisor X} {r : ℕ} (hr : 0 < r) (h : ((r : ℤ) • E).IsQCartier) : E.IsQCartier := by
  obtain ⟨m, hm, h⟩ := h
  exact ⟨m * r, mul_ne_zero hm (by exact_mod_cast hr.ne'), by rwa [mul_smul]⟩

/-- A `ℚ`-divisor is `g`-ample as soon as a positive integral multiple of it is. -/
private theorem hasRelativelyAmpleMultiple_of_natCast_smul {X Y : Scheme.{u}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {E : QDivisor X} {g : X ⟶ Y} {r : ℕ} (hr : 0 < r)
    (h : ((r : ℤ) • E).HasRelativelyAmpleMultiple g) : E.HasRelativelyAmpleMultiple g := by
  obtain ⟨m, hm, L, hL, hLe, hamp⟩ := h
  refine ⟨m * r, Nat.mul_pos hm hr, L, hL, ?_, hamp⟩
  rw [hLe, ← mul_smul]; push_cast; rfl

end MMP.Proofs.lem_km3c_small_ample_model_is_flip

namespace MMP.Mori

open MMP.Proofs.lem_km3c_small_ample_model_is_flip in
/-- A projective birational morphism `g : Z ⟶ Y` over `k` from a normal variety, with exceptional
set of codimension at least two, on which the birational transform `g⁻¹_* f_* (r K_X + r D)`
(for an integer `r > 0` with `r D` integral) is `ℚ`-Cartier and `g`-ample, is a `(K + D)`-flip
of the `(K + D)`-flipping contraction `f : X ⟶ Y`. -/
@[mmp "lem_km3c_small_ample_model_is_flip"]
public theorem isFlip_of_isProjectiveMorphism {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {K : Divisor X} {D : QDivisor X} {f : X ⟶ Y} {g : Z ⟶ Y}
    (hf : IsFlippingContraction sX sY K D f)
    {r : ℕ} (hr : 0 < r) (hrD : ∃ B : Divisor X, Divisor.toQDivisor B = (r : ℤ) • D)
    (hZ : IsNormalVariety k sZ) (hgY : g ≫ sY = sZ)
    (hgproj : IsProjectiveMorphism g) (hgbir : IsBirationalMorphism g)
    (hcodim : 2 ≤ closedsCodimension (exceptionalSet g))
    (hQC : QDivisor.IsQCartier (flipTransform f g ((r : ℤ) • (Divisor.toQDivisor K + D))))
    (hample : QDivisor.HasRelativelyAmpleMultiple
      (flipTransform f g ((r : ℤ) • (Divisor.toQDivisor K + D))) g) :
    IsFlip sX sY sZ K D f g := by
  rw [map_zsmul, map_add, flipTransform_toQDivisor] at hQC hample
  exact ⟨hf, hZ, hgY, isProper_of_isProjectiveMorphism g hgproj, hgbir,
    isQCartier_of_natCast_smul hr hQC, hasRelativelyAmpleMultiple_of_natCast_smul hr hample, hcodim⟩

end MMP.Mori

end

/-!
## A normal reduced divisor has pairwise disjoint components

Let `X` be a normal variety over a field `k` and `D = D₁ + ⋯ + D_s` a reduced divisor on `X`.
If the support of `D`, with its reduced closed subscheme structure, is a normal scheme, then the
components `Dᵢ` are pairwise disjoint: at a point `y` on two components the local ring
`𝒪_{D,y}` has two minimal primes, so it is not a domain, whereas every local ring of a normal
scheme is a normal domain.

### Main results

* `MMP.Mori.DivisorWithCoeffs.pairwise_disjoint_support_of_isNormal_suppScheme`: the prime
  divisors occurring in a reduced divisor with normal support are pairwise disjoint.

### Implementation notes

The scheme `D` is `MMP.Mori.DivisorWithCoeffs.suppScheme D`, the reduced closed subscheme of
`X` on `Supp D`; for a reduced divisor this is the scheme `D`. Its irreducible components are
the prime divisors `Dᵢ` with nonzero coefficient, so the conclusion is stated for those prime
divisors, in the form `MMP.Mori.PairOnNormalDivisor` records it.

### References

* [Kollár–Mori, *Birational geometry of algebraic varieties*, Prop. 5.51]
-/

section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Proofs.lem_km5b_normal_floor_disjoint_components

/-- The generic point of a prime divisor specializes to every point of its support. -/
private theorem genericPoint_specializes {X : Scheme.{u}} (E : MMP.Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ E.support) : E.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
  exact specializes_iff_mem_closure.mpr hx

/-- In a scheme whose stalk at `z` is a domain, any two generizations of `z` have a common
generization: the image of the generic point of `Spec 𝒪_{Z,z}`. -/
private theorem exists_common_generization {Z : Scheme.{u}} {z a a' : Z}
    (hz : IsDomain (Z.presheaf.stalk z)) (ha : a ⤳ z) (ha' : a' ⤳ z) :
    ∃ b : Z, b ⤳ a ∧ b ⤳ a' := by
  obtain ⟨p, rfl⟩ : a ∈ Set.range (Z.fromSpecStalk z) := by rwa [Scheme.range_fromSpecStalk]
  obtain ⟨p', rfl⟩ : a' ∈ Set.range (Z.fromSpecStalk z) := by rwa [Scheme.range_fromSpecStalk]
  let q : PrimeSpectrum (Z.presheaf.stalk z) := ⟨⊥, Ideal.isPrime_bot⟩
  exact ⟨Z.fromSpecStalk z q,
    ((PrimeSpectrum.le_iff_specializes q p).mp bot_le).map (Z.fromSpecStalk z).continuous,
    ((PrimeSpectrum.le_iff_specializes q p').mp bot_le).map (Z.fromSpecStalk z).continuous⟩

/-- Two prime divisors whose generic points have a common generization in `Supp D` are equal:
that generization lies on a component `F` of `D`, and the generic point of `F` then
specializes to both generic points, which forces both prime divisors to be `F`. -/
private theorem eq_of_common_generization_mem_supp {X : Scheme.{u}} {D : MMP.Mori.Divisor X}
    {E E' : MMP.Mori.PrimeDivisor X} {b : X} (hb : b ∈ D.supp) (hE : b ⤳ E.genericPoint)
    (hE' : b ⤳ E'.genericPoint) : E = E' := by
  obtain ⟨F, -, hbF⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mp hb
  have hF := genericPoint_specializes F hbF
  exact (MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes (hF.trans hE)).symm.trans
    (MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes (hF.trans hE'))

end MMP.Proofs.lem_km5b_normal_floor_disjoint_components

namespace MMP.Mori.DivisorWithCoeffs

open MMP.Proofs.lem_km5b_normal_floor_disjoint_components in
/-- **A normal reduced divisor has pairwise disjoint components** (Kollár–Mori 5.51). If `D` is
a reduced divisor on a normal variety `X` whose support `D.suppScheme` is a normal scheme, then
the prime divisors occurring in `D` are pairwise disjoint. -/
@[mmp "lem_km5b_normal_floor_disjoint_components"]
public theorem pairwise_disjoint_support_of_isNormal_suppScheme {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (D : Divisor X) (hD : MMP.Intersection.IsReducedEffective D)
    [IsNormal D.suppScheme] :
    (D.support : Set (PrimeDivisor X)).Pairwise
      fun E E' => Disjoint E.support E'.support := by
  intro E hE E' hE' hne
  refine Set.disjoint_left.mpr fun y hy hy' => hne ?_
  set ι := D.suppIdeal.subschemeι
  have hrange : Set.range ι = (D.supp : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, MMP.Mori.DivisorWithCoeffs.coe_support_suppIdeal]
  have hmem {F : MMP.Mori.PrimeDivisor X} (hF : F ∈ D.support) {x : X} (hx : x ∈ F.support) :
      x ∈ Set.range ι :=
    hrange ▸ MMP.Mori.DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hF) hx
  have hind : Topology.IsInducing ι := ι.isClosedEmbedding.isInducing
  obtain ⟨z, rfl⟩ := hmem hE hy
  obtain ⟨a, ha⟩ := hmem hE (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E)
  obtain ⟨a', ha'⟩ := hmem hE' (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E')
  obtain ⟨b, hb, hb'⟩ := exists_common_generization (‹IsNormal D.suppScheme›.stalk_isDomain z)
    (hind.specializes_iff.mp (ha ▸ genericPoint_specializes E hy))
    (hind.specializes_iff.mp (ha' ▸ genericPoint_specializes E' hy'))
  exact eq_of_common_generization_mem_supp (D := D) (hrange.subset ⟨b, rfl⟩)
    (ha ▸ hb.map ι.continuous) (ha' ▸ hb'.map ι.continuous)

end MMP.Mori.DivisorWithCoeffs

end
