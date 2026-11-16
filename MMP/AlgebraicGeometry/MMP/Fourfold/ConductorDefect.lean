module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ComplexSchemeSubscheme
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Chow.RationalCycleClass

/-!
# The algebraic defect of an exceptional model

Let `r : Z ⟶ Y` be a projective birational morphism of complex varieties, `Z` a smooth projective
fourfold, whose full exceptional locus is an snc divisor `F = ⋃ᵢ Fᵢ`, with inclusions
`ιᵢ : Fᵢ ⟶ Z`. Let `Cᵢ ⊆ H_4(Fᵢ, ℚ)` be the span of the classes of the prime divisors of `Fᵢ`, and
put
`K(r) = ker (⨁ᵢ Cᵢ → H_4(Z, ℚ))`, `(xᵢ)ᵢ ↦ ∑ᵢ (ιᵢ)_* xᵢ`,
`B(r) = {([Zᵢ(a)])ᵢ : a an oriented double-surface system}`,
where `Zᵢ(a)` is the divisor of `a` on `Fᵢ` (`MMP.Fourfold.surfaceCoefficientDivisor`). The
*algebraic defect* is `K(r)/B(r)`. When `Y` is a normal projective `ℚ`-factorial terminal
fourfold, `r` is an isomorphism over `Y_reg` with `F` the reduced inverse image of `Sing Y`,
`-D` is `r`-ample for some `D = ∑ mᵢ Fᵢ` with `mᵢ > 0` and every `Fᵢ` maps to a curve or a point,
`r` is a *curve-and-point exceptional model*.

The vertical versions only allow representatives killed by `r`: `Cᵢ^v ⊆ H_4(Fᵢ, ℚ)` is the space
of classes of rational surface cycles `Lᵢ` on `Fᵢ` with `r_* Lᵢ = 0` as a cycle on `Y`,
`K_v(r) = ker (⨁ᵢ Cᵢ^v → H_4(Z, ℚ))`, `B_v(r)` is spanned by the classes of the oriented
double-surface systems supported on surfaces whose image in `Y` has dimension at most one, and
`D_v(r) = K_v(r)/B_v(r)`. For a closed `Q ⊆ Y`, `D_{v,Q}(r) ⊆ D_v(r)` consists of the classes with
such representatives all of whose surfaces map into `Q`. *Property `A(r)`* says that every
family `(Lᵢ)ᵢ` of rational surface cycles with `r_* Lᵢ = 0` and `∑ᵢ (ιᵢ)_* [Lᵢ] = 0` has
`[Lᵢ] = [Zᵢ(a)]` for one vertical oriented system `a`; the vertical condition is imposed on the
cycles `Lᵢ`, not on their classes.

## Main definitions

* `MMP.Fourfold.RationalHomology`, `MMP.Fourfold.RationalCycles`,
  `MMP.Fourfold.rationalCycleClass`: `H_n(X, ℚ)`, rational `k`-cycles and their classes in
  `H_{2k}(X, ℚ)`.
* `MMP.Fourfold.rationalPushforward`: the push-forward `f_*` of rational cycles.
* `MMP.Fourfold.divisorClass`, `MMP.Fourfold.divisorClasses`: the class of a `ℚ`-divisor and the
  span `C` of the classes of prime divisors.
* `MMP.Fourfold.componentHomologyMap`, `MMP.Fourfold.componentHomologySum`: `(ιᵢ)_*` and
  `⨁ᵢ H_4(Fᵢ, ℚ) → H_4(Z, ℚ)`; `MMP.Fourfold.exceptionalKernel`: the kernel of its restriction to
  `⨁ᵢ Cᵢ` for subspaces `Cᵢ`.
* `MMP.Fourfold.IsCurvePointExceptionalModel`: curve-and-point exceptional models.
* `MMP.Fourfold.algebraicKernel`, `MMP.Fourfold.orientedSurfaceClasses`,
  `MMP.Fourfold.AlgebraicDefect`: `K(r)`, `B(r)` and `K(r)/B(r)`.
* `MMP.Fourfold.verticalDivisorClasses`, `MMP.Fourfold.verticalKernel`,
  `MMP.Fourfold.verticalSurfaceCoefficients`, `MMP.Fourfold.verticalSurfaceClasses`,
  `MMP.Fourfold.VerticalDefect`, `MMP.Fourfold.verticalDefectOver`: `Cᵢ^v`, `K_v(r)`, the
  vertical oriented systems, `B_v(r)`, `D_v(r)` and `D_{v,Q}(r)`.
* `MMP.Fourfold.HasVerticalAlgebraicKernel`: property `A(r)`.

## Main results

* `MMP.Fourfold.isCycleClass_rationalCycleClass_single`: the class of a subvariety is its cycle
  class, the push-forward of its fundamental class.
* `MMP.Fourfold.rationalCycleClass_mapRange`, `MMP.Fourfold.rationalPushforward_mapRange`: on
  integral cycles, the class is the cycle map and the push-forward is that of cycles.
* `MMP.Fourfold.mem_exceptionalKernel`, `MMP.Fourfold.mem_orientedSurfaceClasses`: membership in
  the kernels and in `B(r)`.
* `MMP.Fourfold.verticalKernelOver_le`: the classes with representatives over `Q` lie in
  `K_v(r)`.

## Implementation notes

* `H_n(X, ℚ)` is the Borel–Moore homology with rational coefficients of the complex points
  `X(ℂ)` in the classical topology (`MMP.borelMooreHomology`). For `X` proper
  over `ℂ`, as for `Z` and the `Fᵢ`, `X(ℂ)` is compact and this is singular homology. The class
  of a rational `k`-cycle is the `ℚ`-linear extension of the cycle map of Fulton, §19.1
  (`MMP.Chow.rationalCycleClass`, on Stacks cycles), which sends a subvariety to the push-forward
  of its fundamental class; the class of a `ℚ`-divisor is the class of its cycle. The class of a
  prime divisor that is not a surface is taken to be `0`; on the threefolds `Fᵢ` every prime
  divisor is a surface.
* The components `Fᵢ` are the prime divisors in the support of `F`, with their reduced structure
  (`E.idealSheaf.subscheme`), and `⨁ᵢ` is the finite product over them. A rational surface cycle
  on `Fᵢ` is a rational `2`-cycle; on the threefold `Fᵢ` it is a `ℚ`-divisor.
* `r_* Lᵢ` is the push-forward along `r ∘ ιᵢ` of rational cycles. The image in `Y` of a surface
  `S` is `r(S)`, and its dimension is the Krull dimension of `r(S)`.
* The definitions of the defect spaces only use `Z`, the components of `F` and `r`; the
  hypotheses on `r`, `Z` and `Y` are the setting in which they are used, recorded for the
  curve-and-point case by `MMP.Fourfold.IsCurvePointExceptionalModel`. In it, `Z` is a complex
  scheme by way of `r` and the structure morphism of `Y`. Projectivity of `Z` and smoothness
  are the clauses of `MMP.Intersection.IsResolution`; "`F` is the full exceptional divisor and
  the reduced inverse image of `Sing Y`" is that `F` is reduced with support `Ex(r)` and
  `r⁻¹(Sing Y)`.
* The quotients `K(r)/B(r)` and `K_v(r)/B_v(r)` are taken by the intersections `B(r) ∩ K(r)` and
  `B_v(r) ∩ K_v(r)`, which are `B(r)` and `B_v(r)` once these lie in the kernels.
* `B(r)` is the image of the oriented systems under the linear map `a ↦ ([Zᵢ(a)])ᵢ`
  (`MMP.Fourfold.surfaceCoefficientClasses`); `a ↦ Zᵢ(a)` is linear since `Z` is Noetherian
  (`MMP.Fourfold.noetherianSpace_of_isComplexScheme`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open scoped MMP.SubschemeOver

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Rational homology -/

section Homology

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]

/-- The rational homology `H_n(X, ℚ)` of the complex points `X(ℂ)` of a complex scheme, in the
classical topology: Borel–Moore homology with coefficients in `ℚ`, which is singular homology
when `X(ℂ)` is compact, for instance when `X` is projective. -/
abbrev RationalHomology (n : ℕ) : Type :=
  borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ X)) (n : ℕ)

variable {X} [IsComplexScheme X]

/-- An algebraic scheme over `ℂ` is a Noetherian topological space. -/
theorem noetherianSpace_of_isComplexScheme : NoetherianSpace X := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of ℂ))).mp inferInstance
  have : IsNoetherian X := (isNoetherian_iff X).mpr ⟨inferInstance, inferInstance⟩
  infer_instance

end Homology

/-! ### Rational cycles mapping into a subset -/

section Pushforward

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- The rational `k`-cycles on `X` all of whose prime cycles `[x]` have closure mapping into
`Q ⊆ Y` under `f`. -/
def cyclesMappingInto (f : X ⟶ Y) (k : ℕ) (Q : Set Y) :
    Submodule ℚ (Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ)
      (X ↘ Spec (.of ℂ)) k) where
  carrier := {L | ∀ x : X, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ)
      (X ↘ Spec (.of ℂ)) k x L ≠ 0 → f.base '' closure {x} ⊆ Q}
  add_mem' {L L'} hL hL' x hx := by
    rw [map_add] at hx
    by_cases h : Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x L = 0
    · exact hL' x fun h' => hx (by rw [h, h', add_zero])
    · exact hL x h
  zero_mem' x hx := absurd (map_zero _) hx
  smul_mem' c L hL x hx := hL x fun h => hx (by rw [map_smul, h, smul_zero])

end Pushforward

/-! ### Divisor classes -/

section DivisorClass

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- The span `C ⊆ H_4(X, ℚ)` of the classes of the prime divisors of `X`. -/
@[mmp "def_mmp_conductor_curve_point_defect"]
def divisorClasses : Submodule ℚ (RationalHomology X 4) :=
  LinearMap.range (Chow.divisorClass X)

/-- `C` is the span of the classes of the prime divisors of `X`. -/
theorem divisorClasses_eq_span :
    divisorClasses X =
      Submodule.span ℚ (Set.range fun P => Chow.divisorClass X (Finsupp.single P 1)) := by
  rw [divisorClasses, Chow.divisorClass, Chow.divisorCycle, LinearMap.range_comp,
    Finsupp.range_linearCombination, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext x
  simp [Finsupp.linearCombination_single]

end DivisorClass

/-! ### Linearity of the divisors of coefficient systems -/

section Linear

variable {Z : Scheme.{u}} (F : Divisor Z)

/-- The coefficient of `P` in `Zᵢ(a)` is additive in `a`. -/
theorem surfaceCoefficientCoeff_add (a b : DoubleSurface F → ℚ) (E : Mori.PrimeDivisor Z)
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) :
    surfaceCoefficientCoeff (a + b) E P = surfaceCoefficientCoeff a E P +
      surfaceCoefficientCoeff b E P := by
  have := finite_doubleSurfaces_eq (B := F) E P
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

/-- The coefficient of `P` in `Zᵢ(a)` is homogeneous in `a`. -/
theorem surfaceCoefficientCoeff_smul (c : ℚ) (a : DoubleSurface F → ℚ) (E : Mori.PrimeDivisor Z)
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) :
    surfaceCoefficientCoeff (c • a) E P = c • surfaceCoefficientCoeff a E P :=
  (smul_finsum c _).symm

end Linear

/-! ### The components of the exceptional divisor and the exceptional kernel -/

section Kernel

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]

/-- The push-forward `(ιᵢ)_* : H_n(Fᵢ, ℚ) → H_n(Z, ℚ)` along the inclusion `ιᵢ : Fᵢ ⟶ Z` of a
prime divisor `Fᵢ`. -/
def componentHomologyMap (E : Mori.PrimeDivisor Z) (n : ℕ) :
    RationalHomology E.idealSheaf.subscheme n →ₗ[ℚ] RationalHomology Z n :=
  (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) E.idealSheaf.subschemeι))
    (UnderlyingSpace.isProperMap_map (K := ℂ) _) n).hom

variable (F : Divisor Z)

/-- The direct sum `⨁ᵢ H_4(Fᵢ, ℚ)` over the components `Fᵢ` of `F`. -/
abbrev ComponentHomology : Type :=
  ∀ E : F.support, RationalHomology E.1.idealSheaf.subscheme 4

/-- The sum of push-forwards `⨁ᵢ H_4(Fᵢ, ℚ) → H_4(Z, ℚ)`, `(xᵢ)ᵢ ↦ ∑ᵢ (ιᵢ)_* xᵢ`. -/
def componentHomologySum : ComponentHomology F →ₗ[ℚ] RationalHomology Z 4 :=
  ∑ E : F.support, componentHomologyMap E.1 4 ∘ₗ LinearMap.proj E

/-- `(xᵢ)ᵢ ↦ ∑ᵢ (ιᵢ)_* xᵢ` on an element. -/
theorem componentHomologySum_apply (x : ComponentHomology F) :
    componentHomologySum F x = ∑ E : F.support, componentHomologyMap E.1 4 (x E) := by
  simp [componentHomologySum]

/-- The kernel of `⨁ᵢ Cᵢ → H_4(Z, ℚ)` for subspaces `Cᵢ ⊆ H_4(Fᵢ, ℚ)`, as a subspace of
`⨁ᵢ H_4(Fᵢ, ℚ)`. -/
def exceptionalKernel
    (C : ∀ E : F.support, Submodule ℚ (RationalHomology E.1.idealSheaf.subscheme 4)) :
    Submodule ℚ (ComponentHomology F) :=
  Submodule.pi Set.univ C ⊓ LinearMap.ker (componentHomologySum F)

/-- `x` lies in the kernel of `⨁ᵢ Cᵢ → H_4(Z, ℚ)` if and only if every `xᵢ` lies in `Cᵢ` and
`∑ᵢ (ιᵢ)_* xᵢ = 0`. -/
theorem mem_exceptionalKernel
    {C : ∀ E : F.support, Submodule ℚ (RationalHomology E.1.idealSheaf.subscheme 4)}
    {x : ComponentHomology F} :
    x ∈ exceptionalKernel F C ↔
      (∀ E, x E ∈ C E) ∧ ∑ E : F.support, componentHomologyMap E.1 4 (x E) = 0 := by
  simp [exceptionalKernel, componentHomologySum_apply]

/-- The kernel of `⨁ᵢ Cᵢ → H_4(Z, ℚ)` is monotone in the subspaces `Cᵢ`. -/
theorem exceptionalKernel_mono
    {C C' : ∀ E : F.support, Submodule ℚ (RationalHomology E.1.idealSheaf.subscheme 4)}
    (h : ∀ E, C E ≤ C' E) : exceptionalKernel F C ≤ exceptionalKernel F C' :=
  inf_le_inf_right _ (Submodule.pi_mono fun E _ => h E)

/-- `K(r) = ker(⨁ᵢ Cᵢ → H_4(Z, ℚ))`, with `Cᵢ ⊆ H_4(Fᵢ, ℚ)` the span of the classes of the prime
divisors of `Fᵢ`. -/
@[mmp "def_mmp_conductor_curve_point_defect"]
def algebraicKernel : Submodule ℚ (ComponentHomology F) :=
  exceptionalKernel F fun E => divisorClasses E.1.idealSheaf.subscheme

/-! ### The classes of the divisors of oriented coefficient systems -/

/-- `a ↦ Zᵢ(a)` is `ℚ`-linear. -/
def surfaceCoefficientDivisorLinearMap (E : Mori.PrimeDivisor Z) :
    (DoubleSurface F → ℚ) →ₗ[ℚ] QDivisor E.idealSheaf.subscheme where
  toFun a := surfaceCoefficientDivisor a E
  map_add' a b := by
    have := noetherianSpace_of_isComplexScheme (X := Z)
    refine Finsupp.ext fun P => ?_
    change (surfaceCoefficientDivisor (a + b) E).coeff P =
      (surfaceCoefficientDivisor a E).coeff P + (surfaceCoefficientDivisor b E).coeff P
    rw [coeff_surfaceCoefficientDivisor, coeff_surfaceCoefficientDivisor,
      coeff_surfaceCoefficientDivisor, surfaceCoefficientCoeff_add]
  map_smul' c a := by
    have := noetherianSpace_of_isComplexScheme (X := Z)
    refine Finsupp.ext fun P => ?_
    change (surfaceCoefficientDivisor (c • a) E).coeff P =
      c • (surfaceCoefficientDivisor a E).coeff P
    rw [coeff_surfaceCoefficientDivisor, coeff_surfaceCoefficientDivisor,
      surfaceCoefficientCoeff_smul]

/-- The map `a ↦ ([Zᵢ(a)])ᵢ` from surface coefficient systems of `F` to `⨁ᵢ H_4(Fᵢ, ℚ)`. -/
def surfaceCoefficientClasses : (DoubleSurface F → ℚ) →ₗ[ℚ] ComponentHomology F :=
  LinearMap.pi fun E => Chow.divisorClass E.1.idealSheaf.subscheme ∘ₗ
    surfaceCoefficientDivisorLinearMap F E.1

/-- The `i`-th component of `([Zᵢ(a)])ᵢ` is the class of `Zᵢ(a)`. -/
theorem surfaceCoefficientClasses_apply (a : DoubleSurface F → ℚ) (E : F.support) :
    surfaceCoefficientClasses F a E =
      Chow.divisorClass E.1.idealSheaf.subscheme (surfaceCoefficientDivisor a E.1) :=
  rfl

/-- `B(r) = {([Zᵢ(a)])ᵢ : a an oriented double-surface system}`. -/
@[mmp "def_mmp_conductor_curve_point_defect"]
def orientedSurfaceClasses : Submodule ℚ (ComponentHomology F) :=
  (orientedSurfaceCoefficients F).map (surfaceCoefficientClasses F)

/-- `x` lies in `B(r)` if and only if `xᵢ = [Zᵢ(a)]` for every `i`, for some oriented
double-surface system `a`. -/
theorem mem_orientedSurfaceClasses {x : ComponentHomology F} :
    x ∈ orientedSurfaceClasses F ↔ ∃ a ∈ orientedSurfaceCoefficients F,
      ∀ E : F.support, x E = Chow.divisorClass E.1.idealSheaf.subscheme
        (surfaceCoefficientDivisor a E.1) := by
  simp only [orientedSurfaceClasses, Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, fun E => rfl⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, funext fun E => (h E).symm⟩

/-- The *algebraic defect* `K(r)/B(r)`. The quotient is by `B(r) ∩ K(r)`, which is `B(r)` once
`B(r) ⊆ K(r)`. -/
@[mmp "def_mmp_conductor_curve_point_defect"]
abbrev AlgebraicDefect : Type :=
  algebraicKernel F ⧸ (orientedSurfaceClasses F).comap (algebraicKernel F).subtype

end Kernel

/-! ### Vertical representatives -/

section VerticalCoefficients

variable {Z Y : Scheme.{u}} (r : Z ⟶ Y) (F : Divisor Z)

/-- The surface coefficient systems of `F` supported on surfaces mapping into dimension at most
one under `r`, that is, `a_{ij,S} = 0` unless `dim r(S) ≤ 1`. -/
def verticalSurfaceCoefficientsSupport : Submodule ℚ (DoubleSurface F → ℚ) where
  carrier := {a | ∀ σ, a σ ≠ 0 → topologicalKrullDim (r.base '' σ.carrier) ≤ 1}
  add_mem' {a b} ha hb σ h := by
    by_cases h' : a σ = 0
    · exact hb σ fun hb' => h (by simp [h', hb'])
    · exact ha σ h'
  zero_mem' σ h := absurd rfl h
  smul_mem' c a ha σ h := ha σ fun h' => h (by simp [h'])

/-- The oriented double-surface systems of `F` supported on surfaces mapping into dimension at
most one in `Y`. -/
@[mmp "def_mmp_conductor_vertical_defect_space"]
def verticalSurfaceCoefficients : Submodule ℚ (DoubleSurface F → ℚ) :=
  orientedSurfaceCoefficients F ⊓ verticalSurfaceCoefficientsSupport r F

/-- `a` is a vertical oriented system if and only if it is oriented and `a_σ ≠ 0` implies that
`r(σ)` has dimension at most one. -/
theorem mem_verticalSurfaceCoefficients {a : DoubleSurface F → ℚ} :
    a ∈ verticalSurfaceCoefficients r F ↔ a ∈ orientedSurfaceCoefficients F ∧
      ∀ σ, a σ ≠ 0 → topologicalKrullDim (r.base '' σ.carrier) ≤ 1 :=
  Iff.rfl

end VerticalCoefficients

section Vertical

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [Y.Over (Spec (.of ℂ))]
  [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] [IsProper r]
  (F : Divisor Z)

omit [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] [r.IsOver (Spec (.of ℂ))]
  [IsProper r] in
variable (Z) in
/-- The rational `k`-cycles `Z_k(Fᵢ)_ℚ` on a component `Fᵢ` of `F`. -/
abbrev ComponentCycles (E : Mori.PrimeDivisor Z) (k : ℕ) : Type :=
  Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ)
    (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) k

/-- The push-forward `(r ∘ ιᵢ)_*` of rational `k`-cycles from a component `Fᵢ` of `F` to `Y`. -/
def componentPushforward (E : Mori.PrimeDivisor Z) (k : ℕ) :
    ComponentCycles Z E k →ₗ[ℚ]
      Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) k :=
  Chow.rationalProperPushforward _ _ _ k (E.idealSheaf.subschemeι ≫ r) (comp_over _ _)

/-- `Cᵢ^v ⊆ H_4(Fᵢ, ℚ)`: the classes of the rational surface cycles `Lᵢ` on `Fᵢ` with
`r_* Lᵢ = 0` as a cycle on `Y`. -/
@[mmp "def_mmp_conductor_vertical_defect_space"]
def verticalDivisorClasses (E : Mori.PrimeDivisor Z) :
    Submodule ℚ (RationalHomology E.idealSheaf.subscheme 4) :=
  (LinearMap.ker (componentPushforward r E 2)).map
    (Chow.rationalCycleClass E.idealSheaf.subscheme 2)

/-- The classes of the rational surface cycles `Lᵢ` on `Fᵢ` with `r_* Lᵢ = 0` all of whose
surfaces map into `Q ⊆ Y`. -/
def verticalDivisorClassesOver (E : Mori.PrimeDivisor Z) (Q : Set Y) :
    Submodule ℚ (RationalHomology E.idealSheaf.subscheme 4) :=
  (LinearMap.ker (componentPushforward r E 2) ⊓
      cyclesMappingInto (E.idealSheaf.subschemeι ≫ r) 2 Q).map
    (Chow.rationalCycleClass E.idealSheaf.subscheme 2)

/-- The classes with representatives over `Q` lie in `Cᵢ^v`. -/
theorem verticalDivisorClassesOver_le (E : Mori.PrimeDivisor Z) (Q : Set Y) :
    verticalDivisorClassesOver r E Q ≤ verticalDivisorClasses r E :=
  Submodule.map_mono inf_le_left

/-- `K_v(r) = ker(⨁ᵢ Cᵢ^v → H_4(Z, ℚ))`. -/
@[mmp "def_mmp_conductor_vertical_defect_space"]
def verticalKernel : Submodule ℚ (ComponentHomology F) :=
  exceptionalKernel F fun E => verticalDivisorClasses r E.1

/-- `B_v(r)`: the classes `([Zᵢ(a)])ᵢ` of the oriented double-surface systems `a` supported on
surfaces mapping into dimension at most one in `Y`. -/
@[mmp "def_mmp_conductor_vertical_defect_space"]
def verticalSurfaceClasses : Submodule ℚ (ComponentHomology F) :=
  (verticalSurfaceCoefficients r F).map (surfaceCoefficientClasses F)

/-- The *vertical algebraic defect* `D_v(r) = K_v(r)/B_v(r)`. The quotient is by
`B_v(r) ∩ K_v(r)`, which is `B_v(r)` once `B_v(r) ⊆ K_v(r)`. -/
@[mmp "def_mmp_conductor_vertical_defect_space"]
abbrev VerticalDefect : Type :=
  verticalKernel r F ⧸ (verticalSurfaceClasses r F).comap (verticalKernel r F).subtype

/-- The elements of `K_v(r)` whose components have vertical representatives all of whose
surfaces map into `Q ⊆ Y`. -/
def verticalKernelOver (Q : Set Y) : Submodule ℚ (ComponentHomology F) :=
  exceptionalKernel F fun E => verticalDivisorClassesOver r E.1 Q

/-- The elements with representatives over `Q` lie in `K_v(r)`. -/
theorem verticalKernelOver_le (Q : Set Y) : verticalKernelOver r F Q ≤ verticalKernel r F :=
  exceptionalKernel_mono F fun E => verticalDivisorClassesOver_le r E.1 Q

/-- `D_{v,Q}(r) ⊆ D_v(r)`: the classes admitting representatives `(Lᵢ)ᵢ`, `r_* Lᵢ = 0`, with
every surface of every `Lᵢ` mapping into `Q`. -/
@[mmp "def_mmp_conductor_vertical_defect_space"]
def verticalDefectOver (Q : Set Y) : Submodule ℚ (VerticalDefect r F) :=
  ((verticalKernelOver r F Q).comap (verticalKernel r F).subtype).map (Submodule.mkQ _)

/-- **Property `A(r)`**: whenever rational surface cycles `Lᵢ` on the components `Fᵢ` of `F`
satisfy `r_* Lᵢ = 0` on `Y` for every `i` and `∑ᵢ (ιᵢ)_* [Lᵢ] = 0` in `H_4(Z, ℚ)`, there is an
oriented double-surface system `a`, supported on surfaces whose image in `Y` has dimension at
most one, with `[Lᵢ] = [Zᵢ(a)]` in `H_4(Fᵢ, ℚ)` for every `i`. -/
@[mmp "def_mmp_conductor_vertical_algebraic_kernel"]
def HasVerticalAlgebraicKernel : Prop :=
  ∀ L : ∀ E : F.support, ComponentCycles Z E.1 2,
    (∀ E : F.support, componentPushforward r E.1 2 (L E) = 0) →
    ∑ E : F.support, componentHomologyMap E.1 4 (Chow.rationalCycleClass _ 2 (L E)) = 0 →
    ∃ a ∈ verticalSurfaceCoefficients r F, ∀ E : F.support,
      Chow.rationalCycleClass _ 2 (L E) = Chow.divisorClass _ (surfaceCoefficientDivisor a E.1)

end Vertical

/-! ### Curve-and-point exceptional models -/

section Model

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z] [IsLocallyNoetherian Z]
  [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- A *curve-and-point exceptional model* `(r, F, D)` of `Y`: `Y` is a normal projective
`ℚ`-factorial terminal complex fourfold, `r : Z ⟶ Y` is a projective resolution by a smooth
variety which is an isomorphism over `Y_reg`, the full exceptional divisor `F = ∑ Fᵢ` of `r` is
a reduced snc divisor whose support is `r⁻¹(Sing Y)`, `D = ∑ mᵢ Fᵢ` with every `mᵢ > 0` and
`-D` relatively ample over `Y`, and every `Fᵢ` maps to a curve or a point. -/
@[mmp "def_mmp_conductor_curve_point_defect"]
structure IsCurvePointExceptionalModel (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (F D : Divisor Z) :
    Prop where
  /-- `Z` is a complex scheme by way of `r`. -/
  comp_eq : r ≫ sY = Z ↘ Spec (.of ℂ)
  /-- `Y` is projective. -/
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sY
  /-- `Y` is `ℚ`-factorial (in particular a normal variety). -/
  isQFactorial : IsQFactorial sY
  /-- `Y` is a fourfold. -/
  topologicalKrullDim_eq : topologicalKrullDim Y = 4
  /-- `Y` is terminal. -/
  isTerminalVariety : IsTerminalVariety sY
  /-- `r` is a projective resolution: `Z` is a smooth variety and `r` is projective and
  birational. -/
  isResolution : MMP.Intersection.IsResolution sY r
  /-- `r` is an isomorphism over `Y_reg`. -/
  isBiregular : IsBiregular r (smoothLocus sY)
  /-- `F` is reduced. -/
  isReducedEffective : MMP.Intersection.IsReducedEffective F
  /-- `F` is snc. -/
  isSNC : DivisorWithCoeffs.IsSNC (r ≫ sY) F
  /-- `F` is the full exceptional divisor of `r`. -/
  supp_eq_exceptionalSet : (F.supp : Set Z) = exceptionalSet r
  /-- `F` is the reduced inverse image of `Sing Y`. -/
  supp_eq_preimage_singularLocus : (F.supp : Set Z) = r.base ⁻¹' (singularLocus sY : Set Y)
  /-- `D = ∑ mᵢ Fᵢ` with `mᵢ > 0`. -/
  coeff_pos : ∀ P ∈ F.support, 0 < D.coeff P
  /-- `D` is supported on `F`. -/
  coeff_eq_zero : ∀ P ∉ F.support, D.coeff P = 0
  /-- `-D` is `r`-ample. -/
  isRelativelyAmple_neg : ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple r h
  /-- Every `Fᵢ` maps to a curve or a point. -/
  topologicalKrullDim_image_le : ∀ P ∈ F.support, topologicalKrullDim (r.base '' P.support) ≤ 1

end Model

end MMP.Fourfold
