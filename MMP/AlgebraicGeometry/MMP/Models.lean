module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic

/-!
# Resolutions, flips, rational curves and surface germs

This file sets up the language of resolutions and of flips used throughout Kollár–Mori, and the
numerical language of resolutions of surface germs of Kollár–Mori, Chapter 4.

Let `X` be a scheme of finite type over a field `k`. A *resolution* of `X` is a proper birational
morphism `g : Y ⟶ X` with `Y` smooth over `k`. A closed subset `S` of a smooth `k`-scheme is an
*snc divisor* if it is empty, or it is the union of finitely many prime divisors whose sum is an
snc divisor. A *log resolution* of a pair `(X, D)` is a resolution `g` such that `Ex(g)` is empty
or of pure codimension one and `Ex(g) ∪ g⁻¹(Supp D)` is an snc divisor.

Let `X` be a normal variety, `K_X` a canonical divisor and `D` a `ℚ`-divisor with `K_X + D`
`ℚ`-Cartier. A *`(K + D)`-flipping contraction* is a proper birational morphism `f : X ⟶ Y` onto a
normal variety with `Ex(f)` of codimension at least two and `-(K_X + D)` `f`-ample. A
*`(K + D)`-flip* of `f` is a proper birational morphism `f⁺ : X⁺ ⟶ Y` from a normal variety such
that, with `D⁺ = (f⁺)⁻¹_* f_* D` and `K_{X⁺} = (f⁺)⁻¹_* f_* K_X`, the divisor `K_{X⁺} + D⁺` is
`ℚ`-Cartier and `f⁺`-ample and `Ex(f⁺)` has codimension at least two; the birational map
`φ = (f⁺)⁻¹ ∘ f : X ⤏ X⁺` is then also called a flip. A *flipped curve* is an irreducible curve
in `Ex(f⁺)`. A birational map is an *isomorphism in codimension one* if neither it nor its inverse
has an exceptional divisor.

A *rational curve* on `X` is a proper integral closed subscheme `C` of dimension one with a finite
birational morphism `ℙ¹ ⟶ C`; it is *smooth* if `C ≅ ℙ¹`. For a proper morphism `f : Y ⟶ X`, an
*`f`-exceptional curve* is a curve `C ⊆ Y` with `f(C)` a point. A *`(-1)`-curve* on a smooth
surface is a curve `C ≅ ℙ¹` with `(C · C) = -1`, and a resolution of a normal surface is *minimal*
if no exceptional curve is a smooth rational curve of self-intersection `-1`. The *arithmetic
genus* of a proper curve is `p_a(C) = 1 - χ(C, 𝒪_C)`.

For a resolution `f : Y ⟶ X` of a surface with exceptional curves `E₁, …, E_r` and a `ℚ`-divisor
`Δ` on `X`, a vector `(a₁, …, a_r)` *solves the numerical pull-back equations* if
`∑ᵢ aᵢ (Eᵢ · Eⱼ) = ((K_Y + f⁻¹_* Δ) · Eⱼ)` for all `j`; `aᵢ` is then the *numerical discrepancy*
of `Eᵢ`, and `Θ = f⁻¹_* Δ - ∑ᵢ aᵢ Eᵢ` is the *log pull-back*. For effective divisors `C`, `C'` on
a smooth surface without common component through a closed point `q`, with local equations `g`,
`g'`, the *local intersection number* is `i_q(C, C') = dim_k 𝒪_{Y,q} / (g, g')`.

A *germ* of a space `X` around a subset `Z` is a small open neighbourhood of `Z`, shrunk at will:
a property holds on the germ if it holds on some open neighbourhood of `Z`. A *surface germ*
`(0 ∈ X)` is a normal surface with a closed point `0` such that `X ∖ {0}` is smooth.

## Main definitions

* `MMP.Mori.IsSmoothResolution`: resolutions.
* `MMP.Mori.IsSNCSubset`: closed subsets which are snc divisors.
* `MMP.Mori.IsLogResolution`: log resolutions.
* `MMP.Mori.IsFlippingContraction`, `MMP.Mori.IsFlip`, `MMP.Mori.IsFlipRationalMap`,
  `MMP.Mori.IsFlippedCurve`: flipping contractions, flips and flipped curves.
* `MMP.Mori.RationalMap.IsIsomorphismInCodimOne`: isomorphisms in codimension one.
* `MMP.Mori.IsRationalCurve`, `MMP.Mori.IsSmoothRationalCurve`: (smooth) rational curves.
* `MMP.Mori.IsExceptionalCurve`: exceptional curves of a morphism.
* `MMP.Mori.IsMinusOneCurve`: `(-1)`-curves.
* `MMP.Mori.IsMinimalSurfaceResolution`: minimal resolutions of normal surfaces.
* `MMP.Mori.arithmeticGenus`: the arithmetic genus of a proper curve.
* `MMP.Mori.localIntersectionNumber`, `MMP.Mori.QDivisor.localIntersectionNumber`: local
  intersection numbers.
* `MMP.Mori.IsNumericalPullbackSolution`, `MMP.Mori.IsNumericalDiscrepancy`,
  `MMP.Mori.logPullback`: the numerical pull-back of a `ℚ`-divisor to a resolution of a surface.
* `MMP.Mori.HoldsOnGerm`: properties of germs of a space around a subset.
* `MMP.Mori.IsSurfaceGerm`, `MMP.Mori.germExceptionalLocus`: surface germs and the exceptional
  curves of a resolution over the distinguished point.

## Main results

* `MMP.Mori.IsSNCSubset.bot`: the empty set is an snc divisor.
* `MMP.Mori.IsLogResolution.isSmoothResolution`: a log resolution is a resolution.
* `MMP.Mori.localIntersectionNumber_eq_of_span`: with local equations `g`, `g'` of `C`, `C'`
  at `q`, `i_q(C, C') = dim_k 𝒪_{Y,q} / (g, g')`.
* `MMP.Mori.IsIntersectionNumber.unique`: an intersection number, when defined, is unique.

## Implementation notes

A morphism `g : Y ⟶ X` of `k`-schemes is given by `g` and the structure morphism `s_X` of `X`;
`Y` carries the structure morphism `g ≫ s_X`. The standing hypotheses of the source (finite type
over `k`, varieties, dimension two) are not part of the definitions unless they enter their
statements; they are the setting in which the definitions are used.

Curves and closed subschemes are presented by ideal sheaves, through
`AlgebraicGeometry.Scheme.IdealSheafData`; a curve is an integral closed subscheme of dimension
one. On a surface, irreducible curves are prime divisors, which carry both the curve (their
integral closed subscheme) and the divisor (with coefficient one).

The closed subset `S` is an snc divisor exactly when it is empty or the union of finitely many
prime divisors `S₁, …, S_r` with `S₁ + ⋯ + S_r` snc. Distinct prime divisors are incomparable,
so these are the irreducible components of `S`, all of codimension one; conversely, on a
Noetherian scheme the components of `S` are finite in number, and those of codimension one
are prime divisors. This is the formulation of the source.

The intersection number `(D · C)` of a `ℚ`-divisor with a curve is
`MMP.Mori.QDivisor.intersectionNumber`, which requires `D` to be `ℚ`-Cartier and `C` proper of
dimension at most one. The statement "`(D · C)` is defined and equals `n`" is
`MMP.Mori.IsIntersectionNumber`. On a smooth variety every divisor is Cartier, and an exceptional
curve of a proper morphism to a scheme of finite type over `k`, or a curve isomorphic to `ℙ¹`, is
proper, so in the setting of the source the intersection numbers asked for are always defined.
The numerical pull-back equations ask, for each `j`, for values of the intersection numbers
`(Eᵢ · Eⱼ)` and `((K_Y + f⁻¹_* Δ) · Eⱼ)` satisfying the equation; values are unique when they
exist (`MMP.Mori.IsIntersectionNumber.unique`). The vector `(a₁, …, a_r)` indexed by the
exceptional curves is the `ℚ`-divisor `∑ aᵢ Eᵢ`, supported on exceptional curves.

`f`-ampleness of a `ℚ`-divisor `D` is ampleness relative to `f` of the invertible sheaf of a
positive multiple `mD` which is a Cartier divisor (`MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`).

The flip `φ = (f⁺)⁻¹ ∘ f` is characterised as a rational map `X ⤏ X⁺` with `f⁺ ∘ φ = f`: if `h`
is the inverse of the birational morphism `f⁺`, then `h ∘ f` is such a map, and any such map
agrees with `h ∘ f` on a dense open of the integral scheme `X`.

The projective line `ℙ¹_k` is `AlgebraicGeometry.projectiveLine k`, glued from two affine lines,
with its structure morphism to `Spec k`; isomorphisms and morphisms from `ℙ¹_k` are over `k`.

The local intersection number of effective divisors `C`, `C'` at `q` is the dimension over `k` of
`𝒪_{Y,q} / (I_{C,q} + I_{C',q})`, where `I_{C,q} = ∏_E I_{E,q}^{c_E}` is the ideal of
`C = ∑ c_E E` in `𝒪_{Y,q}`. On a smooth surface it is principal, generated by a local equation
`g` of `C`, and `I_{C,q} + I_{C',q} = (g, g')`
(`MMP.Mori.localIntersectionNumber_eq_of_span`). The dimension is `Module.finrank`, which is `0`
on an infinite-dimensional quotient; with no common component through `q` the quotient is
finite-dimensional. The bilinear extension to `ℚ`-divisors is computed on prime divisors.

*Germs.* Kollár–Mori, Notation 0.4(13), works with complex analytic spaces, for which Mathlib has
no counterpart. What the notation fixes is a convention about neighbourhoods: a statement about
the germ of `X` around `Z` is a statement about some open neighbourhood `U ⊇ Z`, which may be
shrunk. This is `MMP.Mori.HoldsOnGerm`, stated for an arbitrary topological space; for a scheme it
is the Zariski germ, which is the germ used for algebraic surface germs `(0 ∈ X)`
(`MMP.Mori.IsSurfaceGerm`). The renaming of meromorphic and bimeromorphic maps to maps and
birational maps has no content apart from analytic spaces.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4,
  1.2, Definition 3.33, 3.37, 3.49, Notation 4.1, 4.4–4.18
* [R. Hartshorne, *Algebraic geometry*][Har77], V.1
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-! ### Resolutions -/

section Resolution

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A *resolution* of a `k`-scheme `X` (structure morphism `s_X`) is a proper birational morphism
`g : Y ⟶ X` with `Y` smooth over `k`, for the structure morphism `g ≫ s_X`. -/
@[mmp "def_km0_resolution"]
structure IsSmoothResolution (g : Y ⟶ X) : Prop where
  isProper : IsProper g
  isBirationalMorphism : IsBirationalMorphism g
  isSmoothScheme : IsSmoothScheme (g ≫ sX)

/-- A closed subset `S` of a scheme `X` smooth over `k` (structure morphism `s_X`) is an *snc
divisor* if it is empty, or it is the union of finitely many prime divisors `S₁, …, S_r` (its
irreducible components, all of codimension one) such that `S₁ + ⋯ + S_r` is an snc divisor. -/
@[mmp "def_km0_snc_subset"]
def IsSNCSubset (S : Closeds X) : Prop :=
  S = ⊥ ∨ ∃ s : Finset (PrimeDivisor X), (⋃ E ∈ s, E.support) = (S : Set X) ∧
    DivisorWithCoeffs.IsSNC sX (∑ E ∈ s, Finsupp.single E (1 : ℤ))

variable {sX} in
/-- The empty set is an snc divisor. -/
theorem IsSNCSubset.bot : IsSNCSubset sX (⊥ : Closeds X) := Or.inl rfl

/-- A closed subset `S` of `X` is *of pure codimension one* if every irreducible closed subset of
`X` maximal among those contained in `S` (an irreducible component of `S`) has codimension one.
The empty set is of pure codimension one. -/
def IsPureCodimOne {T : Type*} [TopologicalSpace T] (S : Closeds T) : Prop :=
  ∀ W : IrreducibleCloseds T, Maximal (fun W' : IrreducibleCloseds T ↦ (W' : Set T) ⊆ S) W →
    codimension W = 1

/-- A *log resolution* of a pair `(X, D)`, `D` an `ℝ`-divisor on the `k`-scheme `X`, is a proper
birational morphism `g : Y ⟶ X` with `Y` smooth over `k` such that `Ex(g)` is empty or of pure
codimension one and `Ex(g) ∪ g⁻¹(Supp D)` is an snc divisor. -/
@[mmp "def_km0_log_resolution"]
structure IsLogResolution (D : RDivisor X) (g : Y ⟶ X) : Prop extends
    IsSmoothResolution sX g where
  isPureCodimOne_exceptionalSet : IsPureCodimOne (exceptionalSet g)
  isSNCSubset : IsSNCSubset (g ≫ sX) (exceptionalSet g ⊔ D.supp.preimage g.continuous)

end Resolution

/-! ### Flipping contractions and flips -/

section Flip

variable {k : Type u} [Field k] {X Y X' : Scheme.{u}}

/-- A `ℚ`-divisor `D` on `X` is *`f`-ample* for `f : X ⟶ Y` if some positive multiple `mD` is a
Cartier divisor whose invertible sheaf is `f`-ample. -/
def QDivisor.HasRelativelyAmpleMultiple [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (D : QDivisor X) (f : X ⟶ Y) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ (L : Divisor X) (hL : L.IsCartier),
    Divisor.toQDivisor L = (m : ℤ) • D ∧ L.IsRelativelyAmple f hL

variable (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A *`(K + D)`-flipping contraction*: for a normal variety `X` over `k` with canonical divisor
`K` and a `ℚ`-divisor `D` such that `K + D` is `ℚ`-Cartier, a proper birational morphism
`f : X ⟶ Y` over `k` onto a normal variety `Y` such that `Ex(f)` has codimension at least two in
`X` and `-(K + D)` is `f`-ample. -/
@[mmp "def_km3c_flipping_contraction"]
structure IsFlippingContraction (K : Divisor X) (D : QDivisor X) (f : X ⟶ Y) : Prop where
  isNormalVariety_source : IsNormalVariety k sX
  isNormalVariety_target : IsNormalVariety k sY
  comp_eq : f ≫ sY = sX
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sX n
  /-- The divisor `K + D` is `ℚ`-Cartier. -/
  isQCartier : (Divisor.toQDivisor K + D).IsQCartier
  isProper : IsProper f
  isBirationalMorphism : IsBirationalMorphism f
  two_le_codimension : 2 ≤ closedsCodimension (exceptionalSet f)
  /-- The divisor `-(K + D)` is `f`-ample. -/
  hasRelativelyAmpleMultiple : (-(Divisor.toQDivisor K + D)).HasRelativelyAmpleMultiple f

/-- The birational transform `(f⁺)⁻¹_* f_* D` on `X⁺` of a divisor `D` on `X`, for morphisms
`f : X ⟶ Y` and `f⁺ : X⁺ ⟶ Y`. -/
def flipTransform {R : Type*} [AddCommMonoid R] (f : X ⟶ Y) (fp : X' ⟶ Y) :
    DivisorWithCoeffs R X →+ DivisorWithCoeffs R X' :=
  (inverseTransformDivisor fp).comp (RationalMap.transformDivisor (X := X) f.toRationalMap)

variable (sX' : X' ⟶ Spec (.of k)) [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- A *`(K + D)`-flip* of a `(K + D)`-flipping contraction `f : X ⟶ Y`: a normal variety `X⁺`
over `k` with a proper birational morphism `f⁺ : X⁺ ⟶ Y` over `k` such that, with
`D⁺ = (f⁺)⁻¹_* f_* D` and `K_{X⁺} = (f⁺)⁻¹_* f_* K`, `K_{X⁺} + D⁺` is `ℚ`-Cartier and `f⁺`-ample
and `Ex(f⁺)` has codimension at least two in `X⁺`. -/
@[mmp "def_km3c_flip"]
structure IsFlip (K : Divisor X) (D : QDivisor X) (f : X ⟶ Y) (fp : X' ⟶ Y) : Prop where
  isFlippingContraction : IsFlippingContraction sX sY K D f
  isNormalVariety : IsNormalVariety k sX'
  comp_eq : fp ≫ sY = sX'
  isProper : IsProper fp
  isBirationalMorphism : IsBirationalMorphism fp
  /-- The divisor `K_{X⁺} + D⁺` is `ℚ`-Cartier. -/
  isQCartier : (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp D).IsQCartier
  /-- The divisor `K_{X⁺} + D⁺` is `f⁺`-ample. -/
  hasRelativelyAmpleMultiple :
    (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp D).HasRelativelyAmpleMultiple fp
  two_le_codimension : 2 ≤ closedsCodimension (exceptionalSet fp)

/-- By abuse of terminology, the birational map `φ = (f⁺)⁻¹ ∘ f : X ⤏ X⁺` of a `(K + D)`-flip
`f⁺ : X⁺ ⟶ Y` of `f : X ⟶ Y` is also called a *`(K + D)`-flip*: `φ` is a rational map with
`f⁺ ∘ φ = f`. -/
@[mmp "not_km3c_flip_rational_map"]
def IsFlipRationalMap (K : Divisor X) (D : QDivisor X) (f : X ⟶ Y) (fp : X' ⟶ Y)
    (φ : RationalMap X X') : Prop :=
  IsFlip sX sY sX' K D f fp ∧ φ.compHom fp = f.toRationalMap

/-- A *curve* in `X`: an integral closed subscheme of dimension one, presented by its ideal
sheaf. -/
def IsCurveIn {Z : Scheme.{u}} (C : Z.IdealSheafData) : Prop :=
  IsIntegral C.subscheme ∧ topologicalKrullDim C.subscheme = 1

/-- A *flipped curve* of a `(K + D)`-flip `f⁺ : X⁺ ⟶ Y` of `f`: an irreducible curve
`C⁺ ⊆ Ex(f⁺)`. -/
@[mmp "def_km3c_flipped_curve"]
def IsFlippedCurve (K : Divisor X) (D : QDivisor X) (f : X ⟶ Y) (fp : X' ⟶ Y)
    (C : X'.IdealSheafData) : Prop :=
  IsFlip sX sY sX' K D f fp ∧ IsCurveIn C ∧ (C.support : Set X') ⊆ (exceptionalSet fp : Set X')

end Flip

namespace RationalMap

variable {X X' : Scheme.{u}}

/-- A birational map `φ : X ⤏ X'` is an *isomorphism in codimension one* if neither `φ` nor its
inverse has an exceptional divisor. -/
@[mmp "def_km3c_isomorphism_in_codimension_one"]
def IsIsomorphismInCodimOne (φ : RationalMap X X') : Prop :=
  IsBirational φ ∧ (∀ E : PrimeDivisor X, ¬ φ.IsExceptional E) ∧
    ∀ ψ : RationalMap X' X, φ.IsInverse ψ → ∀ E : PrimeDivisor X', ¬ ψ.IsExceptional E

end RationalMap

/-! ### Curves -/

section Curves

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A *rational curve* on a `k`-scheme `X`: a closed subscheme `C ⊆ X` which is a proper curve
(integral, of dimension one) admitting a finite birational morphism `ℙ¹_k ⟶ C` over `k`. -/
@[mmp "def_km1a_rational_curve"]
def IsRationalCurve (C : X.IdealSheafData) : Prop :=
  IsCurveIn C ∧ IsProper (C.subschemeι ≫ sX) ∧
    ∃ ν : projectiveLine k ⟶ C.subscheme, ν ≫ C.subschemeι ≫ sX = projectiveLine k ↘ Spec (.of k) ∧
      IsFinite ν ∧ IsBirationalMorphism ν

/-- A *smooth rational curve* on a `k`-scheme `X`: a rational curve `C ⊆ X` with `C ≅ ℙ¹_k` over
`k`. -/
@[mmp "def_km1a_rational_curve"]
def IsSmoothRationalCurve (C : X.IdealSheafData) : Prop :=
  IsRationalCurve sX C ∧
    ∃ e : projectiveLine k ≅ C.subscheme,
      e.hom ≫ C.subschemeι ≫ sX = projectiveLine k ↘ Spec (.of k)

/-- An *`f`-exceptional curve* of a morphism `f : Y ⟶ X`: a curve `C ⊆ Y` such that `f(C)` is a
point. -/
@[mmp "def_km4a_exceptional_curve"]
def IsExceptionalCurve (f : Y ⟶ X) (C : Y.IdealSheafData) : Prop :=
  IsCurveIn C ∧ ∃ x : X, f.base '' (C.support : Set Y) = {x}

/-- The *arithmetic genus* `p_a(C) = 1 - χ(C, 𝒪_C)` of a proper curve `C` over `k`. -/
@[mmp "def_km4a_arithmetic_genus"]
def arithmeticGenus {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) [IsProper sC]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] : ℤ :=
  1 - eulerCharacteristic k sC (SheafOfModules.unit C.ringCatSheaf)

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- The intersection number `(D · C)` of a `ℚ`-divisor `D` on a normal `k`-scheme `X` with a closed
subscheme `C ⊆ X` *is defined and equals `n`*: `C` is proper over `k` of dimension at most one,
`D` is `ℚ`-Cartier, and `(D · C) = n`. -/
def IsIntersectionNumber (D : QDivisor X) (C : X.IdealSheafData) (n : ℚ) : Prop :=
  ∃ (_ : IsProper (C.subschemeι ≫ sX)) (hdim : topologicalKrullDim C.subscheme ≤ 1)
    (hD : D.IsQCartier), D.intersectionNumber k sX C.subschemeι hdim hD = n

variable {sX} in
/-- An intersection number, when defined, is unique. -/
theorem IsIntersectionNumber.unique {D : QDivisor X} {C : X.IdealSheafData} {n n' : ℚ}
    (h : IsIntersectionNumber sX D C n) (h' : IsIntersectionNumber sX D C n') : n = n' := by
  obtain ⟨_, _, _, rfl⟩ := h
  obtain ⟨_, _, _, rfl⟩ := h'
  rfl

/-- A *`(-1)`-curve* on a smooth surface `X` over `k`: a proper curve `C ⊆ X`, a prime divisor,
with `C ≅ ℙ¹_k` and `(C · C) = -1`. -/
@[mmp "def_km4a_minus_one_curve"]
def IsMinusOneCurve (C : PrimeDivisor X) : Prop :=
  IsProper (C.idealSheaf.subschemeι ≫ sX) ∧
    (∃ e : projectiveLine k ≅ C.idealSheaf.subscheme,
      e.hom ≫ C.idealSheaf.subschemeι ≫ sX = projectiveLine k ↘ Spec (.of k)) ∧
    IsIntersectionNumber sX (Finsupp.single C 1) C.idealSheaf (-1)

end Curves

section MinimalResolution

variable {k : Type u} [Field k] {S S' : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (f : S' ⟶ S)
  [QuasiCompact (f ≫ sS)] [IsLocallyNoetherian S'] [IsNormal S']

/-- A resolution `f : S' ⟶ S` of a normal surface `S` is *minimal* if no irreducible curve
`E ⊆ Ex(f)` is a smooth rational curve with `(E²) = -1`. On the smooth surface `S'` the
irreducible curves are the prime divisors. -/
@[mmp "def_km3c_minimal_resolution_surface"]
def IsMinimalSurfaceResolution : Prop :=
  IsSmoothResolution sS f ∧
    ¬ ∃ E : PrimeDivisor S', E.support ⊆ (exceptionalSet f : Set S') ∧
      IsSmoothRationalCurve (f ≫ sS) E.idealSheaf ∧
      IsIntersectionNumber (f ≫ sS) (Finsupp.single E 1) E.idealSheaf (-1)

end MinimalResolution

/-! ### Local intersection numbers -/

section LocalIntersection

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))

/-- The ideal `I_{C,q} = ∏_E I_{E,q}^{c_E}` in `𝒪_{Y,q}` of an effective divisor `C = ∑ c_E E`,
`I_{E,q}` the ideal of the prime divisor `E` at `q`. -/
def localIdeal (q : Y) (C : Divisor Y) : Ideal (Y.presheaf.stalk q) :=
  ∏ E ∈ C.support, IdealSheafData.stalk E.idealSheaf q ^ (C E).toNat

/-- The *local intersection number* `i_q(C, C') = dim_k 𝒪_{Y,q} / (g, g')` of effective divisors
`C`, `C'` on a smooth surface `Y` over `k` at a closed point `q`, where `g`, `g'` are local
equations of `C`, `C'` at `q`: the dimension of `𝒪_{Y,q} / (I_{C,q} + I_{C',q})`. -/
@[mmp "def_km4a_local_intersection_number"]
def localIntersectionNumber (q : Y) (C C' : Divisor Y) : ℕ :=
  letI := stalkAlgebra sY q
  Module.finrank k (Y.presheaf.stalk q ⧸ (localIdeal q C ⊔ localIdeal q C'))

/-- With local equations `g`, `g'` of `C`, `C'` at `q`, `i_q(C, C') = dim_k 𝒪_{Y,q} / (g, g')`. -/
theorem localIntersectionNumber_eq_of_span (q : Y) {C C' : Divisor Y}
    {g g' : Y.presheaf.stalk q} (hg : localIdeal q C = Ideal.span {g})
    (hg' : localIdeal q C' = Ideal.span {g'}) :
    localIntersectionNumber sY q C C' =
      letI := stalkAlgebra sY q
      Module.finrank k (Y.presheaf.stalk q ⧸ Ideal.span {g, g'}) := by
  rw [localIntersectionNumber, hg, hg', Ideal.span_insert]

/-- The *local intersection number* `i_q(D, D')` of `ℚ`-divisors without common components through
`q`, extended bilinearly: `i_q(∑ d_E E, ∑ d'_{E'} E') = ∑ d_E d'_{E'} i_q(E, E')`. -/
@[mmp "def_km4a_local_intersection_number"]
def QDivisor.localIntersectionNumber (q : Y) (D D' : QDivisor Y) : ℚ :=
  ∑ E ∈ D.support, ∑ E' ∈ D'.support,
    D E * D' E' * (Mori.localIntersectionNumber sY q (Finsupp.single E 1) (Finsupp.single E' 1))

end LocalIntersection

/-! ### Numerical pull-back on resolutions of surfaces -/

section NumericalPullback

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
  [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]

/-- For a resolution `f : Y ⟶ X` of a surface with exceptional curves `E₁, …, E_r`, a canonical
divisor `K_Y` and a `ℚ`-divisor `Δ` on `X`, the vector `(a₁, …, a_r)`, given as the `ℚ`-divisor
`a = ∑ aᵢ Eᵢ` supported on the `f`-exceptional curves, *solves the numerical pull-back equations*
of `(X, Δ)` on `f` if `∑ᵢ aᵢ (Eᵢ · Eⱼ) = ((K_Y + f⁻¹_* Δ) · Eⱼ)` for every `f`-exceptional curve
`Eⱼ`. -/
@[mmp "def_km4a_numerical_pullback_coefficients"]
def IsNumericalPullbackSolution (K : Divisor Y) (Δ : QDivisor X) (a : QDivisor Y) : Prop :=
  IsSmoothResolution sX f ∧ (∃ n : ℕ, K.IsCanonicalDivisor (f ≫ sX) n) ∧
    (∀ E ∈ a.support, IsExceptionalCurve f E.idealSheaf) ∧
    ∀ Ej : PrimeDivisor Y, IsExceptionalCurve f Ej.idealSheaf →
      ∃ (c : PrimeDivisor Y → ℚ) (b : ℚ),
        (∀ Ei ∈ a.support,
          IsIntersectionNumber (f ≫ sX) (Finsupp.single Ei 1) Ej.idealSheaf (c Ei)) ∧
        IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor K + inverseTransformDivisor f Δ)
          Ej.idealSheaf b ∧
        ∑ Ei ∈ a.support, a Ei * c Ei = b

/-- In the setting of `MMP.Mori.IsNumericalPullbackSolution`, `q ∈ ℚ` is the *(numerical)
discrepancy* `a(E, X, Δ)` of the `f`-exceptional curve `E` computed on `f` if `q = a_E` for a
vector `a` solving the numerical pull-back equations. -/
@[mmp "def_km4a_numerical_discrepancy"]
def IsNumericalDiscrepancy (K : Divisor Y) (Δ : QDivisor X) (E : PrimeDivisor Y) (q : ℚ) : Prop :=
  IsExceptionalCurve f E.idealSheaf ∧
    ∃ a : QDivisor Y, IsNumericalPullbackSolution sX f K Δ a ∧ a E = q

end NumericalPullback

/-- The *log pull-back* `Θ_{f,a} = f⁻¹_* Δ - ∑ᵢ aᵢ Eᵢ` of a `ℚ`-divisor `Δ` on `X` to `Y` along a
resolution `f : Y ⟶ X`, for a vector `a`, given as the `ℚ`-divisor `∑ᵢ aᵢ Eᵢ` on the exceptional
curves. -/
@[mmp "def_km4a_log_pullback"]
def logPullback {X Y : Scheme.{u}} (f : Y ⟶ X) (Δ : QDivisor X) (a : QDivisor Y) : QDivisor Y :=
  inverseTransformDivisor f Δ - a

/-! ### Germs -/

/-- A property `P` of open subsets of a space `T` *holds on the germ of `T` around `Z`* if it
holds on some open neighbourhood `U ⊇ Z`: statements about the germ are understood after
replacing `T` by a suitably small open neighbourhood of `Z`, which may be shrunk. -/
@[mmp "not_km0_analytic_germ"]
def HoldsOnGerm {T : Type*} [TopologicalSpace T] (Z : Set T) (P : Opens T → Prop) : Prop :=
  ∃ U : Opens T, Z ⊆ U ∧ P U

section SurfaceGerm

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A *(normal) surface germ* `(0 ∈ X)`: a normal surface `X` over `k` with a closed point `0`
such that `X ∖ {0}` is smooth. A property of the germ *holds near `0`* if it holds on some open
neighbourhood of `0` (`MMP.Mori.HoldsOnGerm` with `Z = {0}`). -/
@[mmp "not_km4a_surface_germ"]
def IsSurfaceGerm (x : X) : Prop :=
  IsNormalVariety k sX ∧ topologicalKrullDim X = 2 ∧ IsClosed ({x} : Set X) ∧
    ∀ y : X, y ≠ x → y ∈ smoothLocus sX

/-- For a resolution `f : Y ⟶ X` of a surface germ `(0 ∈ X)`, the union `E = ⋃ᵢ Eᵢ` of the
`f`-exceptional curves `Eᵢ` with `f(Eᵢ) = 0`. -/
@[mmp "not_km4a_surface_germ"]
def germExceptionalLocus (f : Y ⟶ X) (x : X) : Set Y :=
  ⋃ (C : Y.IdealSheafData) (_ : IsExceptionalCurve f C ∧ f.base '' (C.support : Set Y) = {x}),
    (C.support : Set Y)

end SurfaceGerm

end MMP.Mori
