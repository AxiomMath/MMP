module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import StacksFrontier.AlgebraicGeometry.CurveTensorEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Relative cones of curves, relative bigness and contractions

Let `f : X ⟶ Y` be a morphism of `k`-schemes. A curve `C ⊆ X` is *contracted* by `f` if `f(C)` is a
point. The real vector space `Z₁(X/Y)_ℝ` of *relative 1-cycles* consists of the formal sums
`∑ aᵢ Cᵢ` of contracted curves, and `N₁(X/Y)` is its quotient by the cycles `Z` with `(Z · D) = 0`
for every Cartier divisor `D` on `X`. The *relative cone of curves* `NE(X/Y) ⊆ N₁(X/Y)` is the
convex cone spanned by the classes of contracted curves, `NE̅(X/Y)` is its closure for the
coarsest topology making every `z ↦ (z · D)` continuous, and `ρ(X/Y) = dim_ℝ N₁(X/Y)` is the
*relative Picard number*. Every relative 1-cycle is a 1-cycle, which gives the natural map
`N₁(X/Y) → N₁(X)`.

A Cartier divisor `D` on `X` is *`f`-free* if `f^* f_* 𝒪_X(D) → 𝒪_X(D)` is surjective, and
*`f`-big* if the rank of `f_* 𝒪_X(kD)` at the generic point of `f(X)` grows at least like
`c kⁿ`, `n = dim X - dim f(X)`.

For an extremal face `F` of the closed cone of curves `NE̅(X)` of a projective variety `X`, a
*contraction of `F`* is a morphism `φ : X ⟶ Z` to a projective variety with `φ_* 𝒪_X = 𝒪_Z`
which contracts exactly the curves whose class lies in `F`; the relative version over `Y` uses
`NE̅(X/Y)`. The contraction of an extremal ray of a normal projective variety is *of fiber type*,
*divisorial* or *small* according to the dimension of the target and the exceptional set.

## Main definitions

* `MMP.Mori.ProperCurve.IsContractedBy`: `f(C)` is a point.
* `MMP.Mori.relativeOneCycles`, `MMP.Mori.RelativeNumericalCurveClasses`,
  `MMP.Mori.relativeNumericalClass`: `Z₁(X/Y)_ℝ`, `N₁(X/Y)` and the class `[Z]`.
* `MMP.Mori.RelativeNumericalCurveClasses.intersectionNumber`,
  `MMP.Mori.RelativeNumericalCurveClasses.IntersectionNumberEq`: the pairing `(z · D) = r`.
* `MMP.Mori.relativeConeOfCurves`, `MMP.Mori.relativeClosedConeOfCurves`: `NE(X/Y)` and
  `NE̅(X/Y)`.
* `MMP.Mori.relativePicardNumber`: `ρ(X/Y)`.
* `MMP.Mori.relativeToAbsolute`, `MMP.Mori.IsNaturalRelativeMap`: the natural map
  `N₁(X/Y) → N₁(X)`.
* `MMP.Mori.IsProjectiveSetting`, `MMP.Mori.IsProperSetting`: the settings (3.21.0) and (3.21.1).
* `MMP.Mori.IsRelativelyBigCartier`, `MMP.Mori.Divisor.IsRelativelyBig`,
  `MMP.Mori.QDivisor.IsRelativelyBig`: `f`-big divisors.
* `MMP.Mori.IsRelativelyFreeCartier`: `f`-free Cartier divisors.
* `MMP.Mori.IsContractionOfFace`, `MMP.Mori.IsRelativeContractionOfFace`: contractions of
  extremal faces, absolute and over `Y`.
* `MMP.Mori.IsFiberTypeContraction`, `MMP.Mori.IsDivisorialContraction`,
  `MMP.Mori.IsSmallContraction`: the three types of contractions of an extremal ray.

## Main results

* `MMP.Mori.RelativeNumericalCurveClasses.intersectionNumberEq_iff`: `(z · D) = r` holds exactly
  for the value at `z` of the linear form `z ↦ (z · D)`, which is well defined on `N₁(X/Y)`.
* `MMP.Mori.isNaturalRelativeMap_relativeToAbsolute`, `MMP.Mori.IsNaturalRelativeMap.unique`:
  the natural map exists and is unique.

## Implementation notes

Curves are the proper curves of `MMP.Mori.ProperCurve`, irreducible reduced closed subschemes of
dimension one which are proper over `k`. When `f` is proper and `X`, `Y` are of finite type over
`k`, the image of a curve `C` is closed, so a contracted curve lies in the fibre over a closed
point `y`, whose residue field is finite over `k`; hence `C` is proper over `k`, and the
contracted curves of the source are exactly the contracted proper curves.

Numerical triviality is tested, as for `N₁(X)` (`MMP.Mori.OneCycle.numericallyTrivial`), against
all invertible sheaves `L` on `X`, the invertible sheaves `𝒪_X(D)` of the Cartier divisors `D` of
the source; on an integral scheme, in particular on a variety, every invertible sheaf is of
that form. The same holds for the topology on `N₁(X/Y)`. The intersection number `(Z · D)` with
an `ℝ`-Cartier divisor is `MMP.Mori.OneCycle.intersectionNumber`.

The constructions of `N₁(X/Y)`, `NE(X/Y)`, `ρ(X/Y)`, the pairing, the natural map, `f`-freeness,
`f`-bigness and contractions are made for an arbitrary morphism `f`, without the properness,
projectivity or variety hypotheses under which the source states them.

The rank of `f_* 𝒪_X(kD)` at the generic point `η` of `f(X)` is the dimension over `κ(η)` of
the fibre `κ(η) ⊗ (f_* 𝒪_X(kD))_η` (`AlgebraicGeometry.Scheme.Modules.fiberRank`). For `X`
irreducible with generic point `ξ`, `η = f(ξ)` is the generic point of the closure of `f(X)`.
Since `f_* 𝒪_X(kD)` is a module over `f_* 𝒪_X`, it is killed by the ideal of the
scheme-theoretic image, which is integral with local ring `κ(η)` at `η`; so the fibre is the
stalk, and its dimension is the rank of `f_* 𝒪_X(kD)` as a sheaf on `f(X)`. The dimension of
`f(X)` is that of its closure.

The condition `φ_* 𝒪_X = 𝒪_Z` says that the map `𝒪_Z → φ_* 𝒪_X` of `φ` is an isomorphism,
that is, `Γ(Z, U) → Γ(X, φ⁻¹ U)` is bijective for every open `U ⊆ Z`. A projective morphism
is `AlgebraicGeometry.IsProjectiveMorphism`, a closed immersion into some `ℙⁿ` over the base.
Surjectivity of a map of sheaves of modules is `Epi` in the abelian category `X.Modules`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.25, 2.5,
  2.16, 3.21, 3.22, 3.25, 3.27
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-! ### Relative 1-cycles and `N₁(X/Y)` -/

section RelativeCycles

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y)

/-- A proper curve `C ⊆ X` is *contracted* by a morphism `f : X ⟶ Y` if `f(C)` is a point:
`f` is constant on the closure of the generic point of `C`. -/
def ProperCurve.IsContractedBy {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (f : X ⟶ Y) :
    Prop :=
  ∀ x ∈ closure ({C.point} : Set X), f x = f C.point

/-- The real vector space `Z₁(X/Y)_ℝ` of *relative 1-cycles* for `f : X ⟶ Y`: the formal finite
sums `∑ aᵢ Cᵢ`, `aᵢ ∈ ℝ`, of curves `Cᵢ ⊆ X` with `f(Cᵢ)` a point, as a subspace of the real
1-cycles on `X`. -/
@[mmp "def_km1b_relative_numerical_curve_space"]
def relativeOneCycles : Submodule ℝ (OneCycle ℝ sX) :=
  Finsupp.supported ℝ ℝ {C : ProperCurve sX | C.IsContractedBy f}

/-- The relative 1-cycles `Z` which are numerically trivial: `(Z · D) = 0` for every Cartier
divisor `D` on `X`, through its invertible sheaf `𝒪_X(D)`. -/
def relativeNumericallyTrivial : Submodule ℝ (relativeOneCycles sX f) :=
  (OneCycle.numericallyTrivial sX).comap (relativeOneCycles sX f).subtype

variable {sX f} in
/-- A relative 1-cycle is numerically trivial if and only if it is numerically trivial as a
1-cycle on `X`. -/
theorem mem_relativeNumericallyTrivial {Z : relativeOneCycles sX f} :
    Z ∈ relativeNumericallyTrivial sX f ↔ (Z : OneCycle ℝ sX) ∈ OneCycle.numericallyTrivial sX :=
  Iff.rfl

/-- The real vector space `N₁(X/Y) = Z₁(X/Y)_ℝ / {Z : (Z · D) = 0 for every Cartier divisor D}`
of *relative 1-cycle classes* of `f : X ⟶ Y`. -/
@[mmp "def_km1b_relative_numerical_curve_space"]
abbrev RelativeNumericalCurveClasses : Type _ :=
  relativeOneCycles sX f ⧸ relativeNumericallyTrivial sX f

/-- The class `[Z] ∈ N₁(X/Y)` of a relative 1-cycle `Z`. -/
@[mmp "def_km1b_relative_numerical_curve_space"]
def relativeNumericalClass : relativeOneCycles sX f →ₗ[ℝ] RelativeNumericalCurveClasses sX f :=
  (relativeNumericallyTrivial sX f).mkQ

/-- Every class in `N₁(X/Y)` is the class of a relative 1-cycle. -/
theorem relativeNumericalClass_surjective :
    Function.Surjective (relativeNumericalClass sX f) :=
  Submodule.mkQ_surjective _

variable {sX f} in
/-- The cycle `1 · C` of a contracted curve is a relative 1-cycle. -/
theorem ProperCurve.cycle_mem_relativeOneCycles {C : ProperCurve sX} (hC : C.IsContractedBy f) :
    C.cycle ℝ ∈ relativeOneCycles sX f :=
  Finsupp.single_mem_supported ℝ 1 hC

variable {sX} in
/-- The class `[C] ∈ N₁(X/Y)` of a curve `C` contracted by `f`. -/
def ProperCurve.relativeClass (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    RelativeNumericalCurveClasses sX f :=
  relativeNumericalClass sX f ⟨C.cycle ℝ, C.cycle_mem_relativeOneCycles hC⟩

/-- The degree `(z · L)` of an invertible sheaf `L` on a relative class `z ∈ N₁(X/Y)`. -/
def RelativeNumericalCurveClasses.degree (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ :=
  (relativeNumericallyTrivial sX f).liftQ
    ((OneCycle.degree ℝ sX L).comp (relativeOneCycles sX f).subtype) fun _ hZ =>
      LinearMap.mem_ker.mpr (OneCycle.mem_numericallyTrivial.mp hZ L)

/-- The degree of `L` on the class `[Z]` of a relative 1-cycle is the degree `(Z · L)`. -/
theorem RelativeNumericalCurveClasses.degree_relativeNumericalClass (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (Z : relativeOneCycles sX f) :
    RelativeNumericalCurveClasses.degree sX f L (relativeNumericalClass sX f Z) =
      OneCycle.degree ℝ sX L Z :=
  rfl

/-! ### The pairing with `ℝ`-Cartier divisors -/

variable {sX f}

/-- The intersection number `(z · D)` of a relative class `z ∈ N₁(X/Y)` with an `ℝ`-Cartier
divisor `D`: the common value of `(Z · D)` over the relative 1-cycles `Z` with `[Z] = z`. -/
@[mmp "def_km1b_relative_class_pairing"]
def RelativeNumericalCurveClasses.intersectionNumber (D : KCartierDivisor ℝ X) :
    RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ :=
  (relativeNumericallyTrivial sX f).liftQ
    ((OneCycle.intersectionPairing D).comp (relativeOneCycles sX f).subtype) fun _ hZ =>
      LinearMap.mem_ker.mpr (OneCycle.intersectionNumber_eq_zero_of_mem hZ D)

/-- The intersection number of the class `[Z]` of a relative 1-cycle with `D` is `(Z · D)`. -/
theorem RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass
    (D : KCartierDivisor ℝ X) (Z : relativeOneCycles sX f) :
    RelativeNumericalCurveClasses.intersectionNumber D (relativeNumericalClass sX f Z) =
      (Z : OneCycle ℝ sX).intersectionNumber D :=
  rfl

/-- For a relative class `z ∈ N₁(X/Y)`, an `ℝ`-Cartier divisor `D = ∑ⱼ cⱼ Dⱼ` and `r ∈ ℝ`,
`(z · D) = r` means that `∑ⱼ cⱼ (Z · Dⱼ) = (Z · D) = r` for every relative 1-cycle `Z` with
`[Z] = z`. -/
@[mmp "def_km1b_relative_class_pairing"]
def RelativeNumericalCurveClasses.IntersectionNumberEq (z : RelativeNumericalCurveClasses sX f)
    (D : KCartierDivisor ℝ X) (r : ℝ) : Prop :=
  ∀ Z : relativeOneCycles sX f, relativeNumericalClass sX f Z = z →
    (Z : OneCycle ℝ sX).intersectionNumber D = r

/-- `(z · D) = r` holds exactly for the value `r` at `z` of the linear form
`MMP.Mori.RelativeNumericalCurveClasses.intersectionNumber D`. -/
theorem RelativeNumericalCurveClasses.intersectionNumberEq_iff
    (z : RelativeNumericalCurveClasses sX f) (D : KCartierDivisor ℝ X) (r : ℝ) :
    z.IntersectionNumberEq D r ↔ RelativeNumericalCurveClasses.intersectionNumber D z = r := by
  refine ⟨fun h => ?_, fun h Z hZ => ?_⟩
  · obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
    exact h Z rfl
  · rw [← h, ← hZ, RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass]

variable (sX f)

/-! ### The topology, the relative cone of curves and the relative Picard number -/

/-- The topology on `N₁(X/Y)`: the coarsest topology for which every linear form
`z ↦ (z · L)`, `L = 𝒪_X(D)` the invertible sheaf of a Cartier divisor `D` (more generally any
invertible sheaf), is continuous. -/
@[mmp "def_km1b_relative_cone"]
instance RelativeNumericalCurveClasses.instTopologicalSpace :
    TopologicalSpace (RelativeNumericalCurveClasses sX f) :=
  ⨅ (L : X.Modules) (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
    haveI := h
    TopologicalSpace.induced (RelativeNumericalCurveClasses.degree sX f L) inferInstance

/-- For every invertible sheaf `L` on `X`, the degree `z ↦ (z · L)` is continuous on `N₁(X/Y)`. -/
theorem RelativeNumericalCurveClasses.continuous_degree (L : X.Modules)
    [h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Continuous (RelativeNumericalCurveClasses.degree sX f L) :=
  continuous_iff_le_induced.mpr (iInf₂_le L h)

/-- Addition on `N₁(X/Y)` is continuous. -/
instance RelativeNumericalCurveClasses.instContinuousAdd :
    ContinuousAdd (RelativeNumericalCurveClasses sX f) :=
  ⟨continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => continuous_induced_rng.2 <| by
    have := h
    have hc := RelativeNumericalCurveClasses.continuous_degree sX f L
    change Continuous fun p : RelativeNumericalCurveClasses sX f ×
        RelativeNumericalCurveClasses sX f =>
      RelativeNumericalCurveClasses.degree sX f L (p.1 + p.2)
    simp only [map_add]
    exact (hc.comp continuous_fst).add (hc.comp continuous_snd)⟩

/-- Scalar multiplication by a real number on `N₁(X/Y)` is continuous. -/
instance RelativeNumericalCurveClasses.instContinuousConstSMul :
    ContinuousConstSMul ℝ (RelativeNumericalCurveClasses sX f) :=
  ⟨fun c => continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h =>
    continuous_induced_rng.2 <| by
      have := h
      have hc := RelativeNumericalCurveClasses.continuous_degree sX f L
      change Continuous fun z : RelativeNumericalCurveClasses sX f =>
        RelativeNumericalCurveClasses.degree sX f L (c • z)
      simp only [map_smul, smul_eq_mul]
      exact continuous_const.mul hc⟩

/-- The *relative cone of curves* `NE(X/Y) ⊆ N₁(X/Y)`: the convex cone of the classes
`∑ aᵢ [Cᵢ]`, `aᵢ ≥ 0`, of the curves `Cᵢ ⊆ X` with `f(Cᵢ)` a point. -/
@[mmp "def_km1b_relative_curve_classes"]
def relativeConeOfCurves : PointedCone ℝ (RelativeNumericalCurveClasses sX f) :=
  PointedCone.hull ℝ
    (Set.range fun C : {C : ProperCurve sX // C.IsContractedBy f} => C.1.relativeClass f C.2)

/-- The *closed relative cone of curves* `NE̅(X/Y)`: the closure of `NE(X/Y)` in `N₁(X/Y)` for
the coarsest topology making every `z ↦ (z · D)` continuous. -/
@[mmp "def_km1b_relative_cone"]
def relativeClosedConeOfCurves : PointedCone ℝ (RelativeNumericalCurveClasses sX f) :=
  (relativeConeOfCurves sX f).closure

/-- The underlying set of `NE̅(X/Y)` is the closure of `NE(X/Y)`. -/
theorem coe_relativeClosedConeOfCurves :
    (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) =
      closure (relativeConeOfCurves sX f) :=
  rfl

variable {sX f} in
/-- The class of a contracted curve lies in `NE(X/Y)`. -/
theorem relativeClass_mem_relativeConeOfCurves {C : ProperCurve sX} (hC : C.IsContractedBy f) :
    C.relativeClass f hC ∈ relativeConeOfCurves sX f :=
  Submodule.subset_span ⟨⟨C, hC⟩, rfl⟩

/-- The *relative Picard number* `ρ(X/Y) = dim_ℝ N₁(X/Y) ∈ ℕ ∪ {∞}`. -/
@[mmp "def_km1b_relative_picard_number"]
def relativePicardNumber : ℕ∞ :=
  (Module.rank ℝ (RelativeNumericalCurveClasses sX f)).toENat

/-! ### The natural map `N₁(X/Y) → N₁(X)` -/

/-- The natural map `N₁(X/Y) → N₁(X)`, `[Z] ↦ [Z]`, induced by the inclusion of relative
1-cycles into 1-cycles. -/
def relativeToAbsolute :
    RelativeNumericalCurveClasses sX f →ₗ[ℝ] NumericalCurveClasses sX :=
  (relativeNumericallyTrivial sX f).mapQ (OneCycle.numericallyTrivial sX)
    (relativeOneCycles sX f).subtype le_rfl

/-- A linear map `ι : N₁(X/Y) → N₁(X)` is *the natural map* if it sends the class in `N₁(X/Y)` of
every relative 1-cycle `∑ aᵢ Cᵢ` (the `Cᵢ` contracted by `f`) to its class in `N₁(X)`. -/
@[mmp "def_km3b_relative_curve_space_map"]
def IsNaturalRelativeMap
    (ι : RelativeNumericalCurveClasses sX f →ₗ[ℝ] NumericalCurveClasses sX) : Prop :=
  ∀ Z : relativeOneCycles sX f,
    ι (relativeNumericalClass sX f Z) = OneCycle.numericalClass sX (Z : OneCycle ℝ sX)

/-- The map `MMP.Mori.relativeToAbsolute` is the natural map `N₁(X/Y) → N₁(X)`. -/
theorem isNaturalRelativeMap_relativeToAbsolute :
    IsNaturalRelativeMap sX f (relativeToAbsolute sX f) :=
  fun _ => rfl

variable {sX f} in
/-- The natural map is unique. -/
theorem IsNaturalRelativeMap.unique
    {ι ι' : RelativeNumericalCurveClasses sX f →ₗ[ℝ] NumericalCurveClasses sX}
    (h : IsNaturalRelativeMap sX f ι) (h' : IsNaturalRelativeMap sX f ι') : ι = ι' := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [h Z, h' Z]

end RelativeCycles

/-! ### The settings of the relative cone theorem -/

section Settings

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k)) (f : X ⟶ Y)

/-- A morphism `f : X ⟶ Y` of `k`-schemes is *in setting (3.21.0)* if `X` and `Y` are projective
varieties over an algebraically closed field `k` of characteristic `0` and `f` is a morphism over
`k`. -/
@[mmp "def_km3b_relative_setting_projective"]
structure IsProjectiveSetting : Prop where
  isAlgClosed : IsAlgClosed k
  /-- The field `k` has characteristic `0`. -/
  charZero : CharZero k
  isProjectiveVariety_source : IsProjectiveVariety k sX
  isProjectiveVariety_target : IsProjectiveVariety k sY
  comp_eq : f ≫ sY = sX

/-- A morphism `f : X ⟶ Y` of `k`-schemes is *in setting (3.21.1)* if it is a proper morphism of
varieties over an algebraically closed field `k` of characteristic `0`. -/
@[mmp "def_km3b_relative_setting_proper"]
structure IsProperSetting : Prop where
  isAlgClosed : IsAlgClosed k
  /-- The field `k` has characteristic `0`. -/
  charZero : CharZero k
  isVariety_source : IsVariety k sX
  isVariety_target : IsVariety k sY
  comp_eq : f ≫ sY = sX
  isProper : IsProper f

end Settings

/-! ### `f`-big and `f`-free divisors -/

section RelativelyBig

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]

/-- The rank at the generic point `η = f(ξ_X)` of `f(X)` of the push-forward `f_* F` of a sheaf
of modules `F` on an irreducible scheme `X`: the dimension over `κ(η)` of the fibre
`κ(η) ⊗ (f_* F)_η`. -/
def relativeGenericRank (F : X.Modules) : ℕ :=
  Scheme.Modules.fiberRank ((Scheme.Modules.pushforward f).obj F) (f (genericPoint X))

/-- A Cartier divisor `D` on an irreducible scheme `X` is *`f`-big* for a morphism `f : X ⟶ Y`
if, with `n = dim X - dim f(X)`, there are `c > 0` and `k₀` such that for every integer
`k ≥ k₀` the rank of `f_* 𝒪_X(kD)` at the generic point of `f(X)` exceeds `c kⁿ`. The
definition is made for an arbitrary morphism, so it covers the algebraic settings (3.21.0) and
(3.21.1); the complex-analytic setting (3.21.2) is not treated here. -/
@[mmp "def_km3b_relatively_big"]
def IsRelativelyBigCartier (D : X.CartierDivisor) : Prop :=
  ∃ a b : ℕ, topologicalKrullDim X = a ∧ topologicalKrullDim (closure (Set.range f.base)) = b ∧
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ, ∀ m : ℤ, k₀ ≤ m →
      c * (m : ℝ) ^ (a - b) <
        (relativeGenericRank f (MMP.CartierDivisor.sheaf (m • D)) : ℝ)

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor `D` on an irreducible normal scheme `X` is *`f`-big* for `f : X ⟶ Y` if, with
`n = dim X - dim f(X)`, there are `c > 0` and `k₀` such that for every integer `k ≥ k₀` the
rank of `f_* 𝒪_X(kD)` at the generic point of `f(X)` exceeds `c kⁿ`; for `D` Cartier this is
the `f`-bigness of the Cartier divisor `D`. As for Cartier divisors, the algebraic settings
(3.21.0) and (3.21.1) are covered and the complex-analytic setting (3.21.2) is not treated
here. -/
@[mmp "def_km3b_relatively_big"]
def Divisor.IsRelativelyBig (D : Divisor X) : Prop :=
  ∃ a b : ℕ, topologicalKrullDim X = a ∧ topologicalKrullDim (closure (Set.range f.base)) = b ∧
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ, ∀ m : ℤ, k₀ ≤ m →
      c * (m : ℝ) ^ (a - b) < (relativeGenericRank f (m • D).divisorialSheaf : ℝ)

/-- A `ℚ`-Cartier `ℚ`-divisor `M` is *`f`-big* if some positive multiple `mM` is a Cartier
divisor which is `f`-big. The definition is made for an arbitrary morphism, so it covers the
algebraic settings (3.21.0) and (3.21.1); the complex-analytic setting (3.21.2) is not treated
here. -/
@[mmp "def_km3b_relatively_big"]
def QDivisor.IsRelativelyBig (M : QDivisor X) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor X, Divisor.toQDivisor D = (m : ℚ) • M ∧ D.IsCartier ∧
    D.IsRelativelyBig f

end RelativelyBig

section RelativelyFree

variable {X Y : Scheme.{u}}

/-- A Cartier divisor `D` on `X` is *`f`-free* for `f : X ⟶ Y` if the natural map
`f^* f_* 𝒪_X(D) → 𝒪_X(D)`, the counit of the adjunction `f^* ⊣ f_*`, is surjective (an
epimorphism of sheaves of modules). -/
@[mmp "def_km3b_relatively_free"]
def IsRelativelyFreeCartier (f : X ⟶ Y) (D : X.CartierDivisor) : Prop :=
  Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app
    (MMP.CartierDivisor.sheaf D))

end RelativelyFree

/-! ### Contractions of extremal faces -/

section Contractions

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A morphism `φ : X ⟶ Z` of `k`-schemes is a *contraction of `F`*, for a subset `F ⊆ N₁(X)`,
if `X` and `Z` are projective varieties, `F` is an extremal face of `NE̅(X)`, `φ` maps a curve
`C ⊆ X` to a point if and only if `[C] ∈ F`, and `φ_* 𝒪_X = 𝒪_Z`. -/
@[mmp "def_km1b_contraction_of_extremal_face"]
structure IsContractionOfFace (sZ : Z ⟶ Spec (.of k)) (F : Set (NumericalCurveClasses sX))
    (φ : X ⟶ Z) : Prop where
  isProjectiveVariety_source : IsProjectiveVariety k sX
  isProjectiveVariety_target : IsProjectiveVariety k sZ
  comp_eq : φ ≫ sZ = sX
  isExtremalFace : IsExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) F
  isContractedBy_iff : ∀ C : ProperCurve sX,
    C.IsContractedBy φ ↔ OneCycle.numericalClass sX (C.cycle ℝ) ∈ F
  /-- `φ_* 𝒪_X = 𝒪_Z`: the map `𝒪_Z(U) → 𝒪_X(φ⁻¹ U)` is an isomorphism for every open `U`. -/
  isIso_app : ∀ U : Z.Opens, IsIso (φ.app U)

variable {k sX}

/-- A pair `(ψ, g)` of morphisms `ψ : X ⟶ Z`, `g : Z ⟶ Y` is a *contraction of `F` over `Y`*,
for `f : X ⟶ Y` and a subset `F ⊆ N₁(X/Y)`, if `F` is an extremal face of `NE̅(X/Y)`, `g` is
projective, `f = g ∘ ψ`, `ψ_* 𝒪_X = 𝒪_Z`, and a curve `C ⊆ X` with `f(C)` a point is mapped to
a point by `ψ` if and only if its class `[C] ∈ N₁(X/Y)` lies in `F`. No hypothesis is placed on
`f`, so this covers the algebraic settings (3.21.0) and (3.21.1), and every morphism of schemes;
the complex-analytic setting (3.21.2) is outside the scope of this library (it has no complex
analytic spaces), as for `f`-bigness (`MMP.Mori.IsRelativelyBigCartier`). -/
@[mmp "def_km3b_relative_contraction"]
structure IsRelativeContractionOfFace (f : X ⟶ Y)
    (F : Set (RelativeNumericalCurveClasses sX f)) (ψ : X ⟶ Z) (g : Z ⟶ Y) : Prop where
  isExtremalFace : IsExtremalFace ℝ
    (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) F
  isProjectiveMorphism : IsProjectiveMorphism g
  comp_eq : ψ ≫ g = f
  /-- `ψ_* 𝒪_X = 𝒪_Z`: the map `𝒪_Z(U) → 𝒪_X(ψ⁻¹ U)` is an isomorphism for every open `U`. -/
  isIso_app : ∀ U : Z.Opens, IsIso (ψ.app U)
  isContractedBy_iff : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f),
    C.IsContractedBy ψ ↔ C.relativeClass f hC ∈ F

variable (k sX)

/-- A contraction `f : X ⟶ Y` of an extremal ray `R` of `NE̅(X)`, for `X` a normal projective
variety, is *of fiber type* if `dim Y < dim X`. -/
@[mmp "def_km2a_fiber_type_contraction"]
structure IsFiberTypeContraction (sY : Y ⟶ Spec (.of k)) (R : Set (NumericalCurveClasses sX))
    (f : X ⟶ Y) : Prop where
  isNormalVariety : IsNormalVariety k sX
  isExtremalRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R
  isContractionOfFace : IsContractionOfFace k sX sY R f
  dim_lt : topologicalKrullDim Y < topologicalKrullDim X

/-- A contraction `f : X ⟶ Y` of an extremal ray `R` of `NE̅(X)`, for `X` a normal projective
variety, is *divisorial* if `f` is birational and its exceptional set `Ex(f)` is a prime divisor
of `X`. -/
@[mmp "def_km2a_divisorial_contraction"]
structure IsDivisorialContraction (sY : Y ⟶ Spec (.of k)) (R : Set (NumericalCurveClasses sX))
    (f : X ⟶ Y) : Prop where
  isNormalVariety : IsNormalVariety k sX
  isExtremalRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R
  isContractionOfFace : IsContractionOfFace k sX sY R f
  isBirationalMorphism : IsBirationalMorphism f
  exists_primeDivisor : ∃ E : PrimeDivisor X, (exceptionalSet f : Set X) = E.support

/-- A contraction `f : X ⟶ Y` of an extremal ray `R` of `NE̅(X)`, for `X` a normal projective
variety, is *small* if `f` is birational and `Ex(f)` has codimension at least two in `X`; this
includes the case `Ex(f) = ∅`, whose codimension is `⊤`. -/
@[mmp "def_km2a_small_contraction"]
structure IsSmallContraction (sY : Y ⟶ Spec (.of k)) (R : Set (NumericalCurveClasses sX))
    (f : X ⟶ Y) : Prop where
  isNormalVariety : IsNormalVariety k sX
  isExtremalRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R
  isContractionOfFace : IsContractionOfFace k sX sY R f
  isBirationalMorphism : IsBirationalMorphism f
  two_le_codimension : 2 ≤ closedsCodimension (exceptionalSet f)

end Contractions

/-! ### Relatively nef divisors -/

section RelativelyNef

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y)

/-- An `ℝ`-Cartier divisor `L = ∑ⱼ cⱼ Lⱼ` on `X` is *`f`-nef* for `f : X ⟶ Y` if
`(C · L) = ∑ⱼ cⱼ deg_C 𝒪_X(Lⱼ) ≥ 0` for every curve `C ⊆ X` (proper over `k`) such that `f(C)` is
a point. No hypothesis is placed on `f`; for `f` proper and `X`, `Y` of finite type over `k`
the curves contracted by `f` are proper over `k`. -/
@[mmp "def_km1b_relatively_nef"]
def KCartierDivisor.IsRelativelyNef (L : KCartierDivisor ℝ X) : Prop :=
  ∀ C : ProperCurve sX, C.IsContractedBy f → 0 ≤ (C.cycle ℝ).intersectionNumber L

/-- A `ℚ`-Cartier `ℚ`-divisor `D` on a normal scheme `X` is *`f`-nef* if its associated
`ℚ`-Cartier divisor `⟨D⟩ = ∑ⱼ cⱼ Dⱼ` (`MMP.Mori.QDivisor.associatedCartier`) is: for every curve
`C ⊆ X` (proper over `k`) with `f(C)` a point, `∑ⱼ cⱼ deg_C 𝒪_X(Dⱼ) ≥ 0`. -/
@[mmp "def_km1b_relatively_nef"]
def QDivisor.IsRelativelyNef [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (D : QDivisor X) : Prop :=
  ∃ h : D.IsQCartier, ∀ C : ProperCurve sX, C.IsContractedBy f →
    0 ≤ (D.associatedCartier h).sum fun E c =>
      (c : ℝ) * ((E : Divisor X).degreeOn k sX C.ι C.dim_le E.2 : ℝ)

end RelativelyNef

end MMP.Mori
