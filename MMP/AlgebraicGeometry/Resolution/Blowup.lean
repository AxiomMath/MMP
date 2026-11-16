module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
public import MMP.AlgebraicGeometry.Resolution.Surface.CurveMultiplicity
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSheafData
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic

/-!
# Blow-ups, exceptional curves, resolutions and normalizations (Kollár, *Resolution*, 2.1–2.22)

This file collects the notions Kollár's second chapter uses without definition, around the
blow-up `π : B_Z X = Proj_X ⨁_{n ≥ 0} Iⁿ ⟶ X` of a Noetherian scheme along a closed subscheme.

* An *`f`-exceptional curve* of a morphism `f : X ⟶ Y` of `k`-schemes is an integral closed
  subscheme `C ⊆ X` of dimension one, projective over `k`, with `f(C)` a point.
* The *intersection number* `(L · C) = deg_C(L|_C)` of a line bundle with such a curve, with the
  degree of Kollár 1.20 (`MMP.Resolution.degree`); `(D · C) = (𝒪_X(D) · C)` for a Cartier
  divisor `D`, extended bilinearly to `ℝ`-Cartier divisors and real 1-cycles.
* An `ℝ`-Cartier divisor `L` is *`f`-nef* if `(L · C) ≥ 0` for every `f`-exceptional curve.
* A Cartier divisor is *`f`-ample* if `𝒪_X(D)` is.
* A *resolution* of a surface `Y` is a projective birational morphism `X ⟶ Y` from a smooth
  surface; it is *minimal* if `K_X` is `f`-nef.
* On a normal variety `S` the divisor `div_S(η)` of a rational top form only records the prime
  divisors meeting the smooth locus.
* A divisor `∑ aᵢ Dᵢ` is *`f`-exceptional* if `dim f(Dᵢ) < dim Dᵢ` for every `i`.
* A *normalization of `Y` in a finite extension `L ⊇ k(Y)`* is a dominant affine morphism
  `g : X ⟶ Y` with `k(X) ≅ L` carrying `𝒪(g⁻¹ Y₀)` onto the integral closure of `𝒪(Y₀)` in `L`.

## Main definitions

* `MMP.Resolution.IsContractedProjectiveCurve`: `f`-exceptional curves.
* `MMP.Resolution.lineBundleCurveIntersection`, `MMP.Resolution.cartierCurveIntersection`,
  `MMP.Resolution.curveIntersectionPairing`: `(L · C)`, `(D · C)` and the bilinear pairing.
* `MMP.Resolution.IsNefOnContractedCurves`: `f`-nef `ℝ`-Cartier divisors.
* `MMP.Resolution.IsRelativelyAmpleCartier`: `f`-ample Cartier divisors.
* `MMP.Resolution.IsProjectiveSurfaceResolution`, `MMP.Resolution.IsMinimalSurfaceResolution`:
  resolutions of surfaces and minimal ones.
* `MMP.Resolution.divisorOfFormOnSmoothLocus`: `div_S(η)` on a normal variety.
* `MMP.Resolution.IsExceptionalDivisorFor`, `MMP.Resolution.IsExceptionalCartierFor`:
  `f`-exceptional divisors.
* `MMP.Resolution.IsNormalizationInExtension`: normalizations of a variety in a finite extension
  of its function field.

## Implementation notes

Several of the notions are already in the library and are registered here, not restated:

* the blow-up `B_I X = Proj_X ⨁ Iⁿ` and `π_{Z,X}` are StacksDraft's `Stacks.Blowup.blowUp` and
  `Stacks.Blowup.blowUpToBase` (Stacks 01OG);
* the birational transform `g_*(Z)` of an irreducible closed subset and its reduced structure are
  `MMP.Mori.RationalMap.transform` and `MMP.Mori.RationalMap.transformIdeal`: the closure of the
  union of the images of `Z ∩ U` over the representatives `(U, g_U)` of `g` is the closure of
  `g(Z ∩ X⁰)` for the largest domain `X⁰`;
* the birational transform of a divisor is `MMP.Mori.RationalMap.transformDivisor`, which drops
  the components whose transform is not a prime divisor of `Y` (for varieties: not of dimension
  `dim Y - 1`) and those not meeting `X⁰`, outside the source's domain;
* `f`-ampleness of a line bundle is `MMP.Mori.IsRelativelyAmple`.

The curves are `MMP.Mori.ProperCurve`s: integral closed subschemes of dimension one, recorded by
their generic point, proper over `k`. An `f`-exceptional curve is in addition projective over
`k` (`AlgebraicGeometry.IsProjectiveMorphism`, H-projective), as in the source. The
intersection number is defined for all proper curves, a domain larger than the source's.

The degree of the source's intersection number is Kollár's `deg_C` of 1.20
(`MMP.Resolution.degree`), computed by multiplicities of a rational section. The library's
`MMP.Mori.ProperCurve.degree` is `χ(C, L|_C) - χ(C, 𝒪_C)`; by Riemann–Roch the two agree on
invertible sheaves, a comparison not proved here.

The order of a top form along a prime divisor meeting the smooth locus is
`MMP.Mori.PrimeDivisor.ordForm`, which there is the coefficient of `div_{S_sm}(η)`: the local
ring is that of the smooth locus, where `Ω^n` is free of rank one. Off the smooth locus the
source's coefficient is `0`, so `div_S(η)` is `MMP.Mori.divisorOfForm` restricted to the prime
divisors meeting the smooth locus.

A *surface* is a variety of dimension two over `k`, a *smooth surface* a scheme of dimension two
smooth over `k`. The canonical divisor `K_X` of a smooth surface is a Cartier divisor whose Weil
divisor (`AlgebraicGeometry.cartierWeilDivisor`) is `div_X(ω)` for a nonzero rational `2`-form
`ω`; minimality asks it to be `f`-nef for every such `ω`.

Hypotheses of the source that only restrict the domain are dropped where the definition makes
sense without them: the noetherian and finite type hypotheses of `f`-ampleness, generic
finiteness of `f` and normality of `X` for exceptional divisors, and finiteness of `L ⊇ k(Y)`
for normalizations.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 2.1–2.22]
* [R. Hartshorne, *Algebraic geometry*, II.7]
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

/-! ### Notions recorded from the library -/

attribute [mmp "def_kr2a_birational_transform_subvariety"] MMP.Mori.RationalMap.transform
  MMP.Mori.RationalMap.transformIdeal
attribute [mmp "def_kr2a_birational_transform_divisor"] MMP.Mori.RationalMap.transformDivisor
  MMP.Mori.RationalMap.transformDivisorₗ
attribute [mmp "def_kr2a_relatively_ample"] MMP.Mori.IsRelativelyAmple

namespace MMP.Resolution

/-! ### Exceptional curves and intersection numbers -/

section Curves

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y)

/-- An *`f`-exceptional curve* of a morphism `f : X ⟶ Y` of `k`-schemes: an integral closed
subscheme `C ⊆ X` of dimension one (a `MMP.Mori.ProperCurve`) which is projective over `k` and
such that `f(C)` is a single point. -/
@[mmp "def_kr2a_exceptional_curve"]
def IsContractedProjectiveCurve (C : ProperCurve sX) : Prop :=
  IsProjectiveMorphism (C.ι ≫ sX) ∧ C.IsContractedBy f

variable {sX}

/-- A proper curve, the reduced closed subscheme on the closure of a point, is integral. -/
instance isIntegral_properCurve_scheme (C : ProperCurve sX) : IsIntegral C.scheme :=
  StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
    isIrreducible_singleton.closure

/-- The *intersection number* `(L · C) = deg_C(L|_C)` of a sheaf of modules `L` on `X` (a line
bundle in the source) with a proper curve `C ⊆ X`, the degree being Kollár's `deg_C` of 1.20
(`MMP.Resolution.degree`) of the pull-back of `L` to `C`. -/
@[mmp "def_kr2a_intersection_number_proper_curve"]
def lineBundleCurveIntersection (L : X.Modules) (C : ProperCurve sX) : ℤ :=
  degree (C.ι ≫ sX) ((Scheme.Modules.pullback C.ι).obj L)

/-- The *intersection number* `(D · C) = (𝒪_X(D) · C)` of a Cartier divisor `D` with a proper
curve `C ⊆ X`. -/
@[mmp "def_kr2a_intersection_number_proper_curve"]
def cartierCurveIntersection (D : X.CartierDivisor) (C : ProperCurve sX) : ℤ :=
  lineBundleCurveIntersection (MMP.CartierDivisor.sheaf D) C

variable (sX) in
/-- The bilinear extension `(∑ⱼ rⱼ Dⱼ · ∑ᵢ cᵢ Cᵢ) = ∑ᵢ,ⱼ rⱼ cᵢ (Dⱼ · Cᵢ)` of the intersection
number to `ℝ`-Cartier divisors and finite real combinations of proper curves. -/
@[mmp "def_kr2a_intersection_number_proper_curve"]
def curveIntersectionPairing : KCartierDivisor ℝ X →ₗ[ℝ] OneCycle ℝ sX →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ fun D =>
    Finsupp.linearCombination ℝ fun C => (cartierCurveIntersection D C : ℝ)

@[simp]
theorem curveIntersectionPairing_ofCartier_cycle (D : X.CartierDivisor) (C : ProperCurve sX) :
    curveIntersectionPairing sX (KCartierDivisor.ofCartier ℝ D) (C.cycle ℝ) =
      cartierCurveIntersection D C := by
  simp only [curveIntersectionPairing, KCartierDivisor.ofCartier, ProperCurve.cycle,
    Finsupp.linearCombination_single, LinearMap.smul_apply, one_smul]

variable (sX) in
/-- An `ℝ`-linear combination `L` of Cartier divisors on `X` is *`f`-nef* for a morphism
`f : X ⟶ Y` of `k`-schemes if `(L · C) ≥ 0` for every `f`-exceptional curve `C ⊆ X`. -/
@[mmp "def_kr2a_relatively_nef"]
def IsNefOnContractedCurves (L : KCartierDivisor ℝ X) : Prop :=
  ∀ C : ProperCurve sX, IsContractedProjectiveCurve sX f C →
    0 ≤ curveIntersectionPairing sX L (C.cycle ℝ)

end Curves

/-! ### Relatively ample Cartier divisors -/

/-- A Cartier divisor `D` on `X` is *`f`-ample* for `f : X ⟶ Y` if the line bundle `𝒪_X(D)` is:
every point of `Y` has an affine open neighbourhood `V` such that `𝒪_X(D)|_{f⁻¹(V)}` is ample. -/
@[mmp "def_kr2a_relatively_ample"]
def IsRelativelyAmpleCartier {X Y : Scheme.{u}} (f : X ⟶ Y) (D : X.CartierDivisor) : Prop :=
  IsRelativelyAmple f (MMP.CartierDivisor.sheaf D)

/-! ### The divisor of a rational top form on a normal variety -/

section Forms

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ}

open Classical in
/-- The divisor `div_S(η) = ∑_P c_P P` of a rational `n`-form `η` on a normal variety `S`: the
sum over the prime divisors `P` meeting the smooth locus `S_sm`, with `c_P` the coefficient of
`P ∩ S_sm` in `div_{S_sm}(η)`, which is the order `ord_P(η)`. -/
@[mmp "def_kr2a_divisor_of_form_normal_variety"]
def divisorOfFormOnSmoothLocus (η : RationalPluriForms sX n 1) : Divisor X :=
  (divisorOfForm η).filter fun P => (P.support ∩ (smoothLocus sX : Set X)).Nonempty

end Forms

/-! ### Resolutions of surfaces -/

section Resolution

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))

/-- A *resolution* of a surface `Y` over `k` (a variety of dimension two) is a projective
birational morphism `f : X ⟶ Y` from a smooth surface `X`: `X` is smooth over `k` (for the
structure morphism `f ≫ s_Y`) and of dimension two. -/
@[mmp "def_kr2a_resolution"]
structure IsProjectiveSurfaceResolution (f : X ⟶ Y) : Prop where
  isVariety : AlgebraicGeometry.IsVariety k sY
  dim_eq : topologicalKrullDim Y = 2
  isProjectiveMorphism : IsProjectiveMorphism f
  isBirationalMorphism : IsBirationalMorphism f
  isSmoothScheme : IsSmoothScheme (f ≫ sY)
  dim_source_eq : topologicalKrullDim X = 2

/-- A resolution `f : X ⟶ Y` of a surface is *minimal* if `div_X(ω)` is `f`-nef for every
nonzero rational `2`-form `ω` on `X`, that is, `K_X` is `f`-nef: there is a Cartier divisor whose
Weil divisor is `div_X(ω)` and which is `f`-nef. -/
@[mmp "def_kr2a_minimal_resolution"]
def IsMinimalSurfaceResolution [IsIntegral X] [IsNoetherian X] (f : X ⟶ Y)
    [LocallyOfFiniteType (f ≫ sY)] : Prop :=
  IsProjectiveSurfaceResolution sY f ∧
    ∀ ω : RationalPluriForms (f ≫ sY) 2 1, ω ≠ 0 →
      ∃ K : X.CartierDivisor,
        (∀ P : AlgebraicGeometry.PrimeDivisor X,
          (cartierWeilDivisor K).1 P = (divisorOfFormOnSmoothLocus ω) P) ∧
        IsNefOnContractedCurves (f ≫ sY) f (KCartierDivisor.ofCartier ℝ K)

end Resolution

/-! ### Exceptional divisors -/

section Exceptional

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A divisor `D = ∑ᵢ aᵢ Dᵢ` with coefficients in `R` (Weil, `ℚ`- or `ℝ`-divisor) is
*`f`-exceptional* for a (generically finite) morphism `f : X ⟶ Y` if `dim f(Dᵢ) < dim Dᵢ` for
every prime divisor `Dᵢ` with `aᵢ ≠ 0`. -/
@[mmp "def_kr2a_exceptional_divisor"]
def IsExceptionalDivisorFor {R : Type*} [Zero R] (D : DivisorWithCoeffs R X) : Prop :=
  ∀ P ∈ D.support,
    topologicalKrullDim (closure (f.base '' P.support)) < topologicalKrullDim P.support

/-- A Cartier divisor on a (normal) scheme `X` is *`f`-exceptional* if its Weil divisor is: every
prime divisor with nonzero coefficient satisfies `dim f(P) < dim P`. -/
@[mmp "def_kr2a_exceptional_divisor"]
def IsExceptionalCartierFor [IsNoetherian X] [IsIntegral X] (D : X.CartierDivisor) : Prop :=
  ∀ P : AlgebraicGeometry.PrimeDivisor X, (cartierWeilDivisor D).1 P ≠ 0 →
    topologicalKrullDim (closure (f.base '' P.support)) < topologicalKrullDim P.support

end Exceptional

/-! ### Normalization in a finite extension of the function field -/

section Normalization

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (L : Type u) [Field L]
  [Algebra Y.functionField L]

/-- The integral closure of `𝒪(Y₀)` in an extension `L` of `k(Y)`, for a nonempty open `Y₀`
(containing the generic point), along `𝒪(Y₀) ⟶ k(Y) ⟶ L`. -/
def integralClosureInExtension (Y₀ : Y.Opens) (hY₀ : genericPoint Y ∈ Y₀) : Subring L :=
  letI : Algebra Γ(Y, Y₀) L :=
    ((algebraMap Y.functionField L).comp (Y.presheaf.germ Y₀ (genericPoint Y) hY₀).hom).toAlgebra
  (integralClosure Γ(Y, Y₀) L).toSubring

/-- A *normalization of a `k`-variety `Y` in a (finite) field extension `L ⊇ k(Y)`*: a dominant
affine morphism of `k`-varieties `g : X ⟶ Y` with a field isomorphism `ι : k(X) ≅ L` such that
`ι ∘ g^*` is the inclusion `k(Y) ⊆ L` and, for every affine open `Y₀ ⊆ Y`, `ι` maps
`𝒪(g⁻¹ Y₀) ⊆ k(X)` onto the integral closure of `𝒪(Y₀)` in `L`. Both conditions are stated on
germs at the generic points; an empty `Y₀` imposes nothing. -/
@[mmp "def_kr2b_normalization_in_extension"]
structure IsNormalizationInExtension (g : X ⟶ Y) (ι : X.functionField ≃+* L) : Prop where
  isVariety_source : AlgebraicGeometry.IsVariety k sX
  isVariety_target : AlgebraicGeometry.IsVariety k sY
  comp_eq : g ≫ sY = sX
  isDominant : IsDominant g
  isAffineHom : IsAffineHom g
  map_germ : ∀ (Y₀ : Y.Opens) (hY₀ : genericPoint Y ∈ Y₀) (hX : genericPoint X ∈ g ⁻¹ᵁ Y₀)
    (s : Γ(Y, Y₀)),
    ι (X.presheaf.germ (g ⁻¹ᵁ Y₀) (genericPoint X) hX (g.app Y₀ s)) =
      algebraMap Y.functionField L (Y.presheaf.germ Y₀ (genericPoint Y) hY₀ s)
  range_germ : ∀ (Y₀ : Y.Opens), IsAffineOpen Y₀ → ∀ (hY₀ : genericPoint Y ∈ Y₀)
    (hX : genericPoint X ∈ g ⁻¹ᵁ Y₀),
    Set.range (fun s : Γ(X, g ⁻¹ᵁ Y₀) => ι (X.presheaf.germ (g ⁻¹ᵁ Y₀) (genericPoint X) hX s)) =
      (integralClosureInExtension L Y₀ hY₀ : Set L)

end Normalization

end MMP.Resolution
