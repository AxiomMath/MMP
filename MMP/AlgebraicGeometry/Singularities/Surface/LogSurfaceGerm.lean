/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Basic
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.Combinatorics.WeightedGraph.Basic
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive

/-!
# Log surface germs, their resolutions and weighted dual graphs

The geometric set-up of Chapter 3 of Kollár et al., *Flips and abundance for algebraic
threefolds* (FA): surface germs with boundary `(X, P; B)`, their resolutions and minimal
resolutions, the weighted dual graph `Γ(g)` and the extended dual graph `Γ^*(g)` of a
resolution `g`, the numbers `c_j` and `d_j`, log discrepancy vectors, rational singularities and
Du Val graphs and singularities.

FA works over `ℂ`. Here the base is an arbitrary field `k`, a variety being a `k`-scheme with
structure morphism `s_X : X ⟶ Spec k`; the weighted dual graph (and the notions built on it)
asks `k` to be algebraically closed, see the implementation notes.

## Main definitions

* `MMP.Flips.IsSurfaceGermWithBoundary`, `MMP.Flips.IsReducedBoundary`: the setting
  `(X, P; B)` of FA 3.0.0.
* `MMP.Flips.IsGermResolution`: resolutions of `(X, P)`;
  `MMP.Flips.IsGermExceptionalCurve`, `MMP.Flips.IsExceptionalCurveEnumeration`: their
  exceptional curves `E_1, …, E_n`.
* `MMP.Flips.IsMinimalGermResolution`: minimal resolutions.
* `MMP.Flips.IsWeightedDualGraph`: `Γ` is the weighted dual graph `Γ(g)`;
  `MMP.Flips.IsMinimalWeightedDualGraph`: `Γ = Γ(f)` for the minimal resolution `f`.
* `MMP.Flips.ExtendedWeightedGraph`, `MMP.Flips.IsGermBoundaryPoint`,
  `MMP.Flips.IsExtendedDualGraph`: boundary points and the extended dual graph `Γ^*(g)`.
* `MMP.Flips.IsGermC`, `MMP.Flips.IsGermD`: the numbers `c_j` and `d_j` of a resolution.
* `MMP.Flips.IsGermLogDiscrepancyVector`: log discrepancy vectors of `(X, P; B)` on `g`.
* `MMP.Flips.IsRationalSurfaceSingularity`: rational singularities.
* `MMP.Flips.WeightedGraph.IsDuVal`, `MMP.Flips.IsDuValSingularity`: Du Val graphs and Du Val
  singularities.

## Main results

* `MMP.Flips.IsSurfaceGermWithBoundary.isLogVariety`: `(X, B)` is a log variety.
* `MMP.Flips.IsGermExceptionalCurve.isProper`: exceptional curves are proper curves.
* `MMP.Flips.IsWeightedDualGraph.isGermD_iff`: `d_j = d_j(Γ(g))`.
* `MMP.Flips.isGermLogDiscrepancyVector_of_isEmpty`: for `n = 0` the empty vector is the log
  discrepancy vector.
* `MMP.Flips.isIntersectionNumber_add_iff_of_linearlyEquivalent`: `((K + Δ) · C)` is invariant
  under linear equivalence of `K`.
* `MMP.Flips.isGermLogDiscrepancyVector_iff_of_forall_linearlyEquivalent`: the log discrepancy
  condition may be checked on one canonical divisor when all are linearly equivalent.
* `MMP.Flips.isGermLogDiscrepancyVector_iff_of_isCanonicalDivisor`: the log discrepancy condition
  does not depend on the choice of the canonical divisor `K_Y` (FA 3.0.2).
* `MMP.Flips.isGermLogDiscrepancyVector_iff_exists_numericalPullback`: the equivalent form
  `K_Y + g⁻¹_* B + ∑ E_j ≡ g^*(K_X + B) + ∑ a_j E_j` with Mumford's numerical pull-back
  (FA 3.0.2).
* `MMP.Flips.IsGermResolution.isIntegral`: the source of a resolution of a germ is integral.
* `MMP.Flips.isIntersectionNumber_add`: intersection numbers are additive.
* `MMP.Flips.WeightedGraph.isDuVal_of_isEmpty`: the empty graph is a Du Val graph.

## Implementation notes

*Exceptional curves.* The exceptional curves of a resolution `g : Y ⟶ X` are the
one-dimensional irreducible components of `g⁻¹(P)`. They are recorded as prime divisors `E` of
the smooth surface `Y` whose support is an irreducible component of `g⁻¹(P)` of dimension one;
on a smooth surface an irreducible closed subset of dimension one has codimension one, so these
are all of them. An irreducible component of `g⁻¹(P)` is a maximal irreducible subset of it.
The list `E_1, …, E_n` is an injective `E : Fin n → MMP.Mori.PrimeDivisor Y` whose range is the
set of exceptional curves (`MMP.Flips.IsExceptionalCurveEnumeration`).

*Intersection numbers.* The intersection numbers `(D · E_j)` are Kollár–Mori's
`MMP.Mori.IsIntersectionNumber` on `Y` with structure morphism `g ≫ s_X`: "`(D · E_j)` is
defined and equals `x`". They are unique when defined (`MMP.Mori.IsIntersectionNumber.unique`),
so the data defined through them (the weighted dual graph, `c_j`, `d_j`) are stated as
relations "`Γ` is `Γ(g)`", "`c` is `c_j`", which determine the data. Likewise the arithmetic
genus `p_a(E_j) = 1 - χ(𝒪_{E_j})` is `MMP.Mori.arithmeticGenus`, defined for a proper curve with
coherent structure sheaf; `MMP.Flips.IsArithmeticGenusOf` says it is defined and has the given
value.

*The weighted dual graph.* `Γ(g)` is a `MMP.Flips.WeightedGraph (Fin n)`, vertex `j` standing
for `E_j`. A weighted graph has genus `p_j ∈ ℤ_{≥ 0}`; the arithmetic genus of an integral
proper curve is nonnegative over an algebraically closed field (FA's `ℂ`), which is why
`MMP.Flips.IsWeightedDualGraph` asks `k` to be algebraically closed. The facts `m_{jk} ≥ 0` and
`β_j ≥ 0` (curves without common components, `g⁻¹_* B` effective with no exceptional component)
are not needed: a graph with these data is a weighted graph.

*The extended dual graph.* FA gives no weights to the "`•`" vertices; `Γ^*(g)` is recorded as
`Γ(g)` together with the edge weights between "`∘`" and "`•`" vertices
(`MMP.Flips.ExtendedWeightedGraph`), "no edge" being edge weight `0` as in a weighted graph.

*The minimal resolution.* "The" minimal resolution `f` (unique up to isomorphism over `X`) is
used existentially: `Γ(f)`, rationality and the Du Val condition are asked of some minimal
resolution.

*Canonical divisors.* The log discrepancy condition is asked for every canonical divisor `K_Y`
of `Y`; FA asks it for one, noting that it does not depend on the choice. The intersection number
`((K_Y + Δ) · E_i)` is invariant under linear equivalence of `K_Y`
(`MMP.Flips.isIntersectionNumber_add_iff_of_linearlyEquivalent`), and on the smooth integral
surface `Y` (`MMP.Flips.IsGermResolution.isIntegral`) all canonical divisors are linearly
equivalent, since `𝒪_Y(K) ≅ ω_Y ≅ 𝒪_Y(K')` forces `K ∼ K'`
(`MMP.Flips.linearlyEquivalent_of_isCanonicalDivisor`). So the condition for every `K_Y` is the
condition for any one canonical divisor
(`MMP.Flips.isGermLogDiscrepancyVector_iff_of_isCanonicalDivisor`). With no canonical divisor
the condition holds vacuously; the existence of `K_Y` is not used.

*Numerical pull-back.* Mumford's numerical pull-back `g^*(K_X + B)` is a `ℚ`-divisor
`N = K_Y + g⁻¹_* B + ∑_j c_j E_j` with `(N · E_i) = 0` for every `i` (the numerical pull-back of
`K_X + B` for the canonical divisor `K_X = g_* K_Y`), and `≡` is numerical equivalence over `X`:
the difference of the two sides has intersection number `0` with every `E_i`. The form
`K_Y + g⁻¹_* B + ∑ E_j ≡ g^*(K_X + B) + ∑ a_j E_j` is
`MMP.Flips.isGermLogDiscrepancyVector_iff_exists_numericalPullback`; uniqueness of `N` (negative
definiteness of `(E_i · E_j)`) is not needed for the equivalence.

*Rational singularities.* `R¹f_*𝒪_Y` is the first right derived functor of
`AlgebraicGeometry.Scheme.Modules.pushforward f` applied to `𝒪_Y`, and its stalk at `P` is the
stalk of the underlying presheaf of abelian groups.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.0.0),
  (3.0.2), (3.1.1), (3.1.2), (3.1.10), (3.1.14), (3.3.4), (3.4.1)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

open MMP.Mori

/-! ### Intersection numbers and linear equivalence -/

section IntersectionNumbers

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The intersection number `(D · C)` depends only on the `ℚ`-divisor `D`, not on the proof that
it is `ℚ`-Cartier. -/
theorem QDivisor.intersectionNumber_congr {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {D D' : QDivisor X} (h : D = D') (hD : D.IsQCartier)
    (hD' : D'.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D'.intersectionNumber k sX i hdim hD' := by
  subst h
  rfl

variable {sX} in
/-- Intersection numbers are additive: if `(D · C) = x` and `(D' · C) = y`, then
`((D + D') · C) = x + y`. -/
theorem isIntersectionNumber_add {D D' : QDivisor X} {C : X.IdealSheafData} {x y : ℚ}
    (h : IsIntersectionNumber sX D C x) (h' : IsIntersectionNumber sX D' C y) :
    IsIntersectionNumber sX (D + D') C (x + y) := by
  obtain ⟨hp, hdim, hD, rfl⟩ := h
  obtain ⟨-, -, hD', rfl⟩ := h'
  exact ⟨hp, hdim, hD.add hD', QDivisor.intersectionNumber_add' k sX _ hdim _ _ hD hD' _⟩

variable {sX} in
/-- If some intersection number `(D · C)` is defined, then `(0 · C) = 0`. -/
theorem isIntersectionNumber_zero {D : QDivisor X} {C : X.IdealSheafData} {x : ℚ}
    (h : IsIntersectionNumber sX D C x) : IsIntersectionNumber sX 0 C 0 := by
  obtain ⟨hp, hdim, -, -⟩ := h
  have h0 : IsIntersectionNumber sX (Divisor.toQDivisor 0) C 0 :=
    ⟨hp, hdim, QDivisor.isQCartier_toQDivisor Divisor.isCartier_zero, by
      rw [QDivisor.intersectionNumber_toQDivisor k sX _ hdim _ Divisor.isCartier_zero,
        Divisor.degreeOn_zero' k sX _ hdim, Int.cast_zero]⟩
  rwa [map_zero] at h0

variable [CompactSpace X]

/-- A Cartier divisor linearly equivalent to `0` has degree `0` along every proper curve. -/
theorem Divisor.degreeOn_eq_zero_of_linearlyEquivalent {C : Scheme.{u}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {D : Divisor X}
    (hD : D.IsCartier) (h : D.LinearlyEquivalent 0) : D.degreeOn k sX i hdim hD = 0 := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
  rw [← Divisor.degreeOn_zero' k sX i hdim]
  exact degreeOn_eq_of_iso k sX i hdim h.divisorialSheafIso

variable {sX} in
/-- **Invariance under linear equivalence.** If `K ∼ K'`, then `((K + Δ) · C) = x` implies
`((K' + Δ) · C) = x`. -/
theorem isIntersectionNumber_add_of_linearlyEquivalent {K K' : Divisor X} {Δ : QDivisor X}
    {C : X.IdealSheafData} {x : ℚ} (hK : K.LinearlyEquivalent K')
    (h : IsIntersectionNumber sX (Divisor.toQDivisor K + Δ) C x) :
    IsIntersectionNumber sX (Divisor.toQDivisor K' + Δ) C x := by
  obtain ⟨hp, hdim, hD, rfl⟩ := h
  have h0 : (K' - K).LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := hK.symm
    exact ⟨φ, by rw [sub_zero, hφ]⟩
  have hc : (K' - K).IsCartier := Divisor.IsCartier.of_linearlyEquivalent h0 Divisor.isCartier_zero
  have hc' := QDivisor.isQCartier_toQDivisor hc
  refine ⟨hp, hdim, hD.add_of_linearlyEquivalent hK, ?_⟩
  rw [QDivisor.intersectionNumber_congr sX _ hdim (show Divisor.toQDivisor K' + Δ =
      (Divisor.toQDivisor K + Δ) + Divisor.toQDivisor (K' - K) by rw [map_sub]; abel) _
      (hD.add hc'),
    QDivisor.intersectionNumber_add' k sX _ hdim _ _ hD hc',
    QDivisor.intersectionNumber_toQDivisor k sX _ hdim _ hc,
    Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX _ hdim hc h0, Int.cast_zero, add_zero]

variable {sX} in
/-- For `K ∼ K'`, `((K + Δ) · C) = x` if and only if `((K' + Δ) · C) = x`. -/
theorem isIntersectionNumber_add_iff_of_linearlyEquivalent {K K' : Divisor X} {Δ : QDivisor X}
    {C : X.IdealSheafData} {x : ℚ} (hK : K.LinearlyEquivalent K') :
    IsIntersectionNumber sX (Divisor.toQDivisor K + Δ) C x ↔
      IsIntersectionNumber sX (Divisor.toQDivisor K' + Δ) C x :=
  ⟨isIntersectionNumber_add_of_linearlyEquivalent hK,
    isIntersectionNumber_add_of_linearlyEquivalent hK.symm⟩

end IntersectionNumbers

/-! ### Surface germs with boundary -/

section Germ

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A *surface germ with boundary* `(X, P; B)` (FA 3.0.0): a normal surface `X` over `k`, a
closed point `P ∈ X` with `X ∖ {P}` smooth (`MMP.Mori.IsSurfaceGerm`), and a `ℚ`-divisor
`B = ∑ bᵢ Bᵢ` whose components `Bᵢ` are curves through `P`, with `0 ≤ bᵢ ≤ 1`. A property of
`(X, B)` holds *near `P`* if it holds on an open neighbourhood of `P`
(`MMP.Mori.HoldsOnGerm`). -/
def IsSurfaceGermWithBoundary (P : X) (B : QDivisor X) : Prop :=
  IsSurfaceGerm sX P ∧ (∀ C ∈ B.support, P ∈ C.support) ∧ ∀ C, 0 ≤ B C ∧ B C ≤ 1

/-- For a surface germ with boundary `(X, P; B)`, `B` is a boundary and `(X, B)` a log variety
(FA 3.0.0). -/
theorem IsSurfaceGermWithBoundary.isLogVariety {P : X} {B : QDivisor X}
    (h : IsSurfaceGermWithBoundary sX P B) : IsLogVariety k sX (QDivisor.toRDivisor B) :=
  ⟨h.1.1, fun C => by
    rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff]
    exact ⟨by exact_mod_cast (h.2.2 C).1, by exact_mod_cast (h.2.2 C).2⟩⟩

/-- The boundary `B` is *reduced* (FA 3.0.0): `bᵢ = 1` for every component (`B = 0` allowed). -/
def IsReducedBoundary (B : QDivisor X) : Prop := ∀ C ∈ B.support, B C = 1

end Germ

/-! ### Resolutions and their exceptional curves -/

section Resolution

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A *resolution of `(X, P)`* (FA 3.0.2), for a surface germ `(X, P)`: a proper birational
morphism `g : Y ⟶ X` from a smooth surface `Y` which is an isomorphism over `X ∖ {P}`. -/
@[mmp "def_fa3_resolution_of_germ"]
structure IsGermResolution (P : X) (g : Y ⟶ X) : Prop where
  /-- `(X, P)` is a surface germ. -/
  isSurfaceGerm : IsSurfaceGerm sX P
  /-- `g` is proper and birational and `Y` is smooth over `k`. -/
  isSmoothResolution : IsSmoothResolution sX g
  /-- `Y` is a surface. -/
  topologicalKrullDim_eq : topologicalKrullDim Y = 2
  /-- `g` is an isomorphism over `X ∖ {P}`. -/
  isIso_away : ∃ U : X.Opens, (U : Set X) = {P}ᶜ ∧ IsIso (g ∣_ U)

/-- An *exceptional curve* of a resolution `g : Y ⟶ X` of `(X, P)` (FA 3.0.2): a
one-dimensional irreducible component of `g⁻¹(P)` (a maximal irreducible subset of `g⁻¹(P)`),
here a prime divisor `E` of `Y` whose support is such a component and which is a curve
(integral of dimension one). -/
@[mmp "def_fa3_resolution_of_germ"]
def IsGermExceptionalCurve (g : Y ⟶ X) (P : X) (E : Mori.PrimeDivisor Y) : Prop :=
  Maximal (fun Z : Set Y => IsIrreducible Z ∧ Z ⊆ g.base ⁻¹' {P}) E.support ∧
    IsCurveIn E.idealSheaf

/-- The exceptional curves of a resolution `g` of `(X, P)` are proper curves on `Y`
(FA 3.0.2). -/
@[mmp "def_fa3_resolution_of_germ"]
theorem IsGermExceptionalCurve.isProper {P : X} {g : Y ⟶ X} (hg : IsGermResolution sX P g)
    {E : Mori.PrimeDivisor Y} (hE : IsGermExceptionalCurve g P E) :
    IsCurveIn E.idealSheaf ∧ IsProper (E.idealSheaf.subschemeι ≫ g ≫ sX) := by
  refine ⟨hE.2, ?_⟩
  have : IsProper g := hg.isSmoothResolution.isProper
  have hX := hg.isSurfaceGerm.1.1
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsClosedImmersion (X.fromSpecResidueField P) :=
    isClosed_singleton_iff_isClosedImmersion.mp hg.isSurfaceGerm.2.2.1
  have : IsIntegral E.idealSheaf.subscheme := E.integral
  set h := E.idealSheaf.subschemeι ≫ g with hh
  -- `h` has image `{P}` and reduced source, so it factors through `Spec κ(P) ⟶ X`
  have H : (X.fromSpecResidueField P).ker ≤ h.ker := by
    have h1 : h.ker = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (h.base '' (⊤ : Closeds E.idealSheaf.subscheme))) := by
      rw [← Scheme.IdealSheafData.map_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_top,
        Scheme.nilradical_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [h1, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, Closeds.closure_le]
    rintro _ ⟨z, -, rfl⟩
    refine (X.fromSpecResidueField P).range_subset_ker_support ?_
    rw [Scheme.range_fromSpecResidueField]
    have hz : E.idealSheaf.subschemeι z ∈ E.support := by
      rw [PrimeDivisor.support, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    exact hE.1.prop.2 hz
  let l := IsClosedImmersion.lift (X.fromSpecResidueField P) h H
  have hl : l ≫ X.fromSpecResidueField P = h := IsClosedImmersion.lift_fac _ _ H
  have : IsProper (l ≫ X.fromSpecResidueField P) := hl ▸ inferInstance
  have : IsProper l := IsProper.of_comp l (X.fromSpecResidueField P)
  -- `Spec κ(P) ⟶ Spec k` is of finite type, hence finite
  have : IsFinite (X.fromSpecResidueField P ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [← Category.assoc, ← hh, ← hl, Category.assoc]
  infer_instance

/-- `E_1, …, E_n` (`n ≥ 0`) are *the exceptional curves* of `g` (FA 3.0.2):
`E : Fin n → Mori.PrimeDivisor Y` lists every exceptional curve exactly once. -/
@[mmp "def_fa3_resolution_of_germ"]
structure IsExceptionalCurveEnumeration (g : Y ⟶ X) (P : X) {n : ℕ}
    (E : Fin n → Mori.PrimeDivisor Y) : Prop where
  /-- No exceptional curve is listed twice. -/
  injective : Function.Injective E
  /-- Every `E_j` is an exceptional curve. -/
  isGermExceptionalCurve : ∀ j, IsGermExceptionalCurve g P (E j)
  /-- Every exceptional curve is listed. -/
  exists_eq : ∀ C, IsGermExceptionalCurve g P C → ∃ j, E j = C

/-- The source of a resolution of `(X, P)` is integral. -/
theorem IsGermResolution.isIntegral {P : X} {g : Y ⟶ X} [IsNormal Y]
    (hg : IsGermResolution sX P g) : IsIntegral Y := by
  have : IsIntegral X := hg.isSurfaceGerm.1.1.toIsIntegral
  have : IsReduced Y := isReduced_of_isNormal Y
  obtain ⟨e, -⟩ := hg.isSmoothResolution.isBirationalMorphism
  have : Nonempty e.target := e.dense_target.nonempty.to_subtype
  have : IsIntegral e.source.toScheme := IsIntegral.of_isIso e.iso.inv
  have hirr : IsIrreducible (e.source : Set Y) :=
    isIrreducible_iff_irreducibleSpace.mpr (inferInstanceAs (IrreducibleSpace e.source.toScheme))
  have : IrreducibleSpace Y := (irreducibleSpace_def Y).mpr (by
    rw [Set.top_eq_univ, ← e.dense_source.closure_eq]
    exact hirr.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- A resolution `f : Y ⟶ X` of `(X, P)` is *minimal* (FA 3.0.2) if none of its exceptional
curves `E` is a smooth rational curve with `(E · E) = -1`. -/
@[mmp "def_fa3_minimal_resolution"]
def IsMinimalGermResolution (P : X) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] : Prop :=
  IsGermResolution sX P f ∧
    ¬ ∃ E : Mori.PrimeDivisor Y, IsGermExceptionalCurve f P E ∧
      IsSmoothRationalCurve (f ≫ sX) E.idealSheaf ∧
      IsIntersectionNumber (f ≫ sX) (Finsupp.single E 1) E.idealSheaf (-1)

end Resolution

/-! ### The arithmetic genus of a curve -/

section Genus

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))

/-- The arithmetic genus `p_a(E) = 1 - χ(𝒪_E)` of the curve `E ⊆ Y` is defined and equals `p`:
`E` is proper over `k` with coherent structure sheaf and `MMP.Mori.arithmeticGenus` of `E` is
`p`. -/
def IsArithmeticGenusOf (E : Mori.PrimeDivisor Y) (p : ℤ) : Prop :=
  ∃ (_ : IsProper (E.idealSheaf.subschemeι ≫ sY))
    (_ : (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf).IsCoherent),
    p = arithmeticGenus (E.idealSheaf.subschemeι ≫ sY)

variable {sY} in
/-- The arithmetic genus, when defined, is unique. -/
theorem IsArithmeticGenusOf.unique {E : Mori.PrimeDivisor Y} {p p' : ℤ}
    (h : IsArithmeticGenusOf sY E p) (h' : IsArithmeticGenusOf sY E p') : p = p' := by
  obtain ⟨_, _, rfl⟩ := h
  obtain ⟨_, _, rfl⟩ := h'
  rfl

end Genus

/-! ### Weighted dual graphs -/

/-- An *extended weighted graph*: a weighted graph `Γ` on the vertices `V` ("`∘`") together with
further vertices `W` ("`•`"), carrying no data of their own, and an edge weight
`m_{jl} ∈ ℤ_{≥ 0}` between each `∘`-vertex `v_j` and each `•`-vertex `w_l` (`0` for no edge).
This is the shape of the extended dual graph of FA 3.1.14. -/
@[mmp "def_fa3_extended_dual_graph"]
structure ExtendedWeightedGraph (V W : Type*) [Fintype V] where
  /-- The weighted graph on the `∘`-vertices. -/
  toWeightedGraph : WeightedGraph V
  /-- The edge weight between `v_j` and the `•`-vertex `w_l`. -/
  boundaryEdgeWeight : V → W → ℕ

section DualGraph

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `Γ` is the *weighted dual graph* `Γ(g)` (FA 3.1.1) of a resolution `g` of `(X, P)`, with
exceptional curves `E_1, …, E_n`, of the surface germ with boundary `(X, P; B)`: it has
vertices `v_1, …, v_n` (`v_j` for `E_j`) and `n_j = -(E_j · E_j)`, `p_j = p_a(E_j)`,
`β_j = (g⁻¹_* B · E_j)` and `m_{jk} = (E_j · E_k)` for `j ≠ k`. Here `k` is algebraically
closed, as FA's `ℂ`. -/
@[mmp "def_fa3_weighted_dual_graph"]
structure IsWeightedDualGraph [IsAlgClosed k] (P : X) (B : QDivisor X) (g : Y ⟶ X)
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    (E : Fin n → Mori.PrimeDivisor Y) (Γ : WeightedGraph (Fin n)) : Prop where
  /-- `(X, P; B)` is a surface germ with boundary. -/
  isSurfaceGermWithBoundary : IsSurfaceGermWithBoundary sX P B
  /-- `g` is a resolution of `(X, P)`. -/
  isGermResolution : IsGermResolution sX P g
  /-- `E_1, …, E_n` are the exceptional curves of `g`. -/
  isExceptionalCurveEnumeration : IsExceptionalCurveEnumeration g P E
  /-- `(E_j · E_j) = -n_j`. -/
  weight : ∀ j, IsIntersectionNumber (g ≫ sX) (Finsupp.single (E j) 1) (E j).idealSheaf
    (-(Γ.weight j : ℚ))
  /-- `p_j = p_a(E_j)`. -/
  genus : ∀ j, IsArithmeticGenusOf (g ≫ sX) (E j) (Γ.genus j)
  /-- `β_j = (g⁻¹_* B · E_j)`. -/
  boundary : ∀ j, IsIntersectionNumber (g ≫ sX) (inverseTransformDivisor g B) (E j).idealSheaf
    (Γ.boundary j)
  /-- `m_{jk} = (E_j · E_k)` for `j ≠ k`. -/
  edgeWeight : ∀ j l, j ≠ l → IsIntersectionNumber (g ≫ sX) (Finsupp.single (E j) 1)
    (E l).idealSheaf (Γ.edgeWeight j l)

/-- `Γ = Γ(f)` (FA 3.1.1): `Γ` is the weighted dual graph of the minimal resolution `f` of
`(X, P)`, for an enumeration of its exceptional curves. -/
@[mmp "def_fa3_weighted_dual_graph"]
def IsMinimalWeightedDualGraph [IsAlgClosed k] (P : X) (B : QDivisor X) {n : ℕ}
    (Γ : WeightedGraph (Fin n)) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : QuasiCompact (f ≫ sX)) (_ : IsLocallyNoetherian Y)
    (_ : IsNormal Y) (E : Fin n → Mori.PrimeDivisor Y),
    IsMinimalGermResolution sX P f ∧ IsWeightedDualGraph sX P B f E Γ

/-- A *boundary point* `(C, y)` of a resolution `g` of `(X, P)` (FA 3.1.14): `C` is an
irreducible component of `g⁻¹_* B` and `y ∈ C ∩ g⁻¹(P)`. -/
@[mmp "def_fa3_extended_dual_graph"]
def IsGermBoundaryPoint (g : Y ⟶ X) (P : X) (B : QDivisor X) (C : Mori.PrimeDivisor Y)
    (y : Y) : Prop :=
  inverseTransformDivisor g B C ≠ 0 ∧ y ∈ C.support ∧ g.base y = P

/-- `Γ^*` is the *extended dual graph* `Γ^*(g)` (FA 3.1.14, 3.1.10) of a resolution `g` of
`(X, P)`, `B` reduced, with exceptional curves `E_1, …, E_n` and boundary points
`(C_1, y_1), …, (C_m, y_m)` (each listed exactly once): its `∘`-vertices form `Γ(g)`, it has a
`•`-vertex `w_l` for each boundary point `(C_l, y_l)`, and `w_l` is joined to `v_j` by an edge
of weight `(C_l · E_j)_{y_l}` if `y_l ∈ E_j`, with no edge (weight `0`) if `y_l ∉ E_j`. -/
@[mmp "def_fa3_extended_dual_graph"]
structure IsExtendedDualGraph [IsAlgClosed k] (P : X) (B : QDivisor X) (g : Y ⟶ X)
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n m : ℕ}
    (E : Fin n → Mori.PrimeDivisor Y) (pt : Fin m → Mori.PrimeDivisor Y × Y)
    (Γ : ExtendedWeightedGraph (Fin n) (Fin m)) : Prop where
  /-- `B` is reduced. -/
  isReducedBoundary : IsReducedBoundary B
  /-- The `∘`-vertices form the weighted dual graph `Γ(g)`. -/
  isWeightedDualGraph : IsWeightedDualGraph sX P B g E Γ.toWeightedGraph
  /-- No boundary point is listed twice. -/
  injective : Function.Injective pt
  /-- Every `(C_l, y_l)` is a boundary point. -/
  isGermBoundaryPoint : ∀ l, IsGermBoundaryPoint g P B (pt l).1 (pt l).2
  /-- Every boundary point is listed. -/
  exists_eq : ∀ C y, IsGermBoundaryPoint g P B C y → ∃ l, pt l = (C, y)
  /-- The edge weight between `v_j` and `w_l` is `(C_l · E_j)_{y_l}` if `y_l ∈ E_j`, else `0`. -/
  boundaryEdgeWeight_eq : ∀ j l, Γ.boundaryEdgeWeight j l =
    haveI := Classical.propDecidable ((pt l).2 ∈ (E j).support)
    if (pt l).2 ∈ (E j).support then
      localIntersectionNumber (g ≫ sX) (pt l).2 (Finsupp.single (pt l).1 1)
        (Finsupp.single (E j) 1)
    else 0

end DualGraph

/-! ### The numbers `c_j`, `d_j` and log discrepancy vectors -/

section Numbers

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (P : X)
  (B : QDivisor X) (g : Y ⟶ X) [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
  {n : ℕ} (E : Fin n → Mori.PrimeDivisor Y)

/-- `c ∈ ℚ` is the number `c_j := 2 - 2p_a(E_j) - ((g⁻¹_* B + ∑_{k ≠ j} E_k) · E_j)` (FA 3.0.2,
after `(*)`) of a resolution `g` of `(X, P)` with exceptional curves `E_1, …, E_n`, where
`p_a(E_j) = 1 - χ(𝒪_{E_j})`. -/
@[mmp "def_fa3_cj"]
def IsGermC (j : Fin n) (c : ℚ) : Prop :=
  IsSurfaceGermWithBoundary sX P B ∧ IsGermResolution sX P g ∧
    IsExceptionalCurveEnumeration g P E ∧
    ∃ (p : ℤ) (x : ℚ), IsArithmeticGenusOf (g ≫ sX) (E j) p ∧
      IsIntersectionNumber (g ≫ sX)
        (inverseTransformDivisor g B + ∑ l ∈ Finset.univ.erase j, Finsupp.single (E l) 1)
        (E j).idealSheaf x ∧
      c = 2 - 2 * p - x

/-- `d ∈ ℚ` is the number `d_j := 2 - 2p_a(E_j) + (E_j · E_j) - (g⁻¹_* B · E_j)` (FA 3.0.2,
after `(**)`) of a resolution `g` of `(X, P)` with exceptional curves `E_1, …, E_n`. -/
@[mmp "def_fa3_dj"]
def IsGermD (j : Fin n) (d : ℚ) : Prop :=
  IsSurfaceGermWithBoundary sX P B ∧ IsGermResolution sX P g ∧
    IsExceptionalCurveEnumeration g P E ∧
    ∃ (p : ℤ) (y b : ℚ), IsArithmeticGenusOf (g ≫ sX) (E j) p ∧
      IsIntersectionNumber (g ≫ sX) (Finsupp.single (E j) 1) (E j).idealSheaf y ∧
      IsIntersectionNumber (g ≫ sX) (inverseTransformDivisor g B) (E j).idealSheaf b ∧
      d = 2 - 2 * p + y - b

variable {sX P B g E} in
/-- The geometric `d_j` is the number `d_j(Γ(g))` of the weighted dual graph (FA 3.0.2). -/
@[mmp "def_fa3_dj"]
theorem IsWeightedDualGraph.isGermD_iff [IsAlgClosed k] {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B g E Γ) (j : Fin n) (d : ℚ) :
    IsGermD sX P B g E j d ↔ d = Γ.d j := by
  constructor
  · rintro ⟨-, -, -, p, y, b, hp, hy, hb, rfl⟩
    rw [WeightedGraph.d, hp.unique (hΓ.genus j), hy.unique (hΓ.weight j),
      hb.unique (hΓ.boundary j)]
    push_cast
    ring
  · rintro rfl
    refine ⟨hΓ.isSurfaceGermWithBoundary, hΓ.isGermResolution,
      hΓ.isExceptionalCurveEnumeration, Γ.genus j, -(Γ.weight j : ℚ), Γ.boundary j,
      hΓ.genus j, hΓ.weight j, hΓ.boundary j, ?_⟩
    rw [WeightedGraph.d]
    push_cast
    ring

/-- `a ∈ ℚ^n` is a *log discrepancy vector of `(X, P; B)` on `g`* (FA 3.0.2), for a resolution
`g` of `(X, P)` with exceptional curves `E_1, …, E_n`, if
`((K_Y + g⁻¹_* B + ∑_j (1 - a_j) E_j) · E_i) = 0` for every `i`, for a canonical divisor `K_Y` of
`Y` (the condition is asked of every canonical divisor; FA notes it does not depend on the
choice, `MMP.Flips.isGermLogDiscrepancyVector_iff_of_isCanonicalDivisor`). For `n = 0` the empty
vector is the log discrepancy vector (`MMP.Flips.isGermLogDiscrepancyVector_of_isEmpty`).
Equivalently `K_Y + g⁻¹_* B + ∑_j E_j ≡ g^*(K_X + B) + ∑_j a_j E_j` with `g^*` Mumford's numerical
pull-back (`MMP.Flips.isGermLogDiscrepancyVector_iff_exists_numericalPullback`). -/
@[mmp "def_fa3_log_discrepancy_vector"]
def IsGermLogDiscrepancyVector (a : Fin n → ℚ) : Prop :=
  IsSurfaceGermWithBoundary sX P B ∧ IsGermResolution sX P g ∧
    IsExceptionalCurveEnumeration g P E ∧
    ∀ K : Divisor Y, K.IsCanonicalDivisor (g ≫ sX) 2 → ∀ i,
      IsIntersectionNumber (g ≫ sX)
        (Divisor.toQDivisor K + inverseTransformDivisor g B +
          ∑ j, Finsupp.single (E j) (1 - a j))
        (E i).idealSheaf 0

variable {sX P B g E} in
/-- `a` is a log discrepancy vector iff the condition holds for one canonical divisor `K₀` of
`Y`, provided every canonical divisor of `Y` is linearly equivalent to `K₀`. -/
theorem isGermLogDiscrepancyVector_iff_of_forall_linearlyEquivalent [CompactSpace Y]
    {K₀ : Divisor Y} (hK₀ : K₀.IsCanonicalDivisor (g ≫ sX) 2)
    (hK : ∀ K : Divisor Y, K.IsCanonicalDivisor (g ≫ sX) 2 → K.LinearlyEquivalent K₀)
    (a : Fin n → ℚ) :
    IsGermLogDiscrepancyVector sX P B g E a ↔
      IsSurfaceGermWithBoundary sX P B ∧ IsGermResolution sX P g ∧
        IsExceptionalCurveEnumeration g P E ∧ ∀ i,
          IsIntersectionNumber (g ≫ sX)
            (Divisor.toQDivisor K₀ + inverseTransformDivisor g B +
              ∑ j, Finsupp.single (E j) (1 - a j))
            (E i).idealSheaf 0 := by
  refine ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4 K₀ hK₀⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, fun K hKc i => ?_⟩⟩
  simp only [add_assoc] at h4 ⊢
  exact isIntersectionNumber_add_of_linearlyEquivalent (hK K hKc).symm (h4 i)

variable {sX P B g E} in
/-- **Independence of the canonical divisor** (FA 3.0.2): the log discrepancy condition may be
checked on any one canonical divisor `K₀` of `Y`. -/
@[mmp "def_fa3_log_discrepancy_vector"]
theorem isGermLogDiscrepancyVector_iff_of_isCanonicalDivisor {K₀ : Divisor Y}
    (hK₀ : K₀.IsCanonicalDivisor (g ≫ sX) 2) (a : Fin n → ℚ) :
    IsGermLogDiscrepancyVector sX P B g E a ↔
      IsSurfaceGermWithBoundary sX P B ∧ IsGermResolution sX P g ∧
        IsExceptionalCurveEnumeration g P E ∧ ∀ i,
          IsIntersectionNumber (g ≫ sX)
            (Divisor.toQDivisor K₀ + inverseTransformDivisor g B +
              ∑ j, Finsupp.single (E j) (1 - a j))
            (E i).idealSheaf 0 := by
  refine ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4 K₀ hK₀⟩, fun h => ?_⟩
  have := h.2.1.isIntegral sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  exact (isGermLogDiscrepancyVector_iff_of_forall_linearlyEquivalent hK₀ (fun K hK =>
    linearlyEquivalent_of_isCanonicalDivisor h.2.1.isSmoothResolution.isSmoothScheme hK hK₀)
    a).mpr h

variable {sX P B g E} in
/-- **The numerical pull-back form** (FA 3.0.2): `a` is a log discrepancy vector if and only if,
for every canonical divisor `K_Y`, there is a `ℚ`-divisor `N = K_Y + g⁻¹_* B + ∑_j c_j E_j` with
`(N · E_i) = 0` for every `i` (Mumford's numerical pull-back `g^*(K_X + B)`, for the canonical
divisor `K_X = g_* K_Y`) such that `K_Y + g⁻¹_* B + ∑_j E_j ≡ N + ∑_j a_j E_j` numerically over
`X`: the difference has intersection number `0` with every exceptional curve `E_i`. -/
@[mmp "def_fa3_log_discrepancy_vector"]
theorem isGermLogDiscrepancyVector_iff_exists_numericalPullback (a : Fin n → ℚ) :
    IsGermLogDiscrepancyVector sX P B g E a ↔
      IsSurfaceGermWithBoundary sX P B ∧ IsGermResolution sX P g ∧
        IsExceptionalCurveEnumeration g P E ∧
        ∀ K : Divisor Y, K.IsCanonicalDivisor (g ≫ sX) 2 → ∃ c : Fin n → ℚ,
          (∀ i, IsIntersectionNumber (g ≫ sX)
            (Divisor.toQDivisor K + inverseTransformDivisor g B +
              ∑ j, Finsupp.single (E j) (c j))
            (E i).idealSheaf 0) ∧
          ∀ i, IsIntersectionNumber (g ≫ sX)
            ((Divisor.toQDivisor K + inverseTransformDivisor g B +
                ∑ j, Finsupp.single (E j) 1) -
              ((Divisor.toQDivisor K + inverseTransformDivisor g B +
                  ∑ j, Finsupp.single (E j) (c j)) + ∑ j, Finsupp.single (E j) (a j)))
            (E i).idealSheaf 0 := by
  have hs : ∀ c : Fin n → ℚ, ∑ j, Finsupp.single (E j) (c j) +
      ∑ j, Finsupp.single (E j) (1 - c j) = ∑ j, Finsupp.single (E j) (1 : ℚ) := fun c => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [← Finsupp.single_add, add_sub_cancel]
  refine ⟨fun ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, h3, fun K hK => ⟨fun j => 1 - a j, h4 K hK, fun i => ?_⟩⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, fun K hK i => ?_⟩⟩
  · have hz : (Divisor.toQDivisor K + inverseTransformDivisor g B +
          ∑ j, Finsupp.single (E j) 1) -
        ((Divisor.toQDivisor K + inverseTransformDivisor g B +
            ∑ j, Finsupp.single (E j) (1 - a j)) + ∑ j, Finsupp.single (E j) (a j)) = 0 := by
      rw [add_assoc (Divisor.toQDivisor K + inverseTransformDivisor g B), add_comm (∑ j, _),
        hs a, sub_self]
    rw [hz]
    exact isIntersectionNumber_zero (h4 K hK i)
  · obtain ⟨c, hN, hD⟩ := h4 K hK
    have heq : Divisor.toQDivisor K + inverseTransformDivisor g B +
        ∑ j, Finsupp.single (E j) (1 - a j) =
        (Divisor.toQDivisor K + inverseTransformDivisor g B + ∑ j, Finsupp.single (E j) (c j)) +
          ((Divisor.toQDivisor K + inverseTransformDivisor g B + ∑ j, Finsupp.single (E j) 1) -
            ((Divisor.toQDivisor K + inverseTransformDivisor g B +
              ∑ j, Finsupp.single (E j) (c j)) + ∑ j, Finsupp.single (E j) (a j))) := by
      rw [← hs a]
      abel
    rw [heq, ← add_zero (0 : ℚ)]
    exact isIntersectionNumber_add (hN i) (hD i)

variable {sX P B g} in
/-- For `n = 0` the empty vector is the log discrepancy vector (FA 3.0.2). -/
theorem isGermLogDiscrepancyVector_of_isEmpty (hB : IsSurfaceGermWithBoundary sX P B)
    (hg : IsGermResolution sX P g) (E : Fin 0 → Mori.PrimeDivisor Y)
    (hE : IsExceptionalCurveEnumeration g P E) (a : Fin 0 → ℚ) :
    IsGermLogDiscrepancyVector sX P B g E a :=
  ⟨hB, hg, hE, fun _ _ i => i.elim0⟩

end Numbers

/-! ### Rational singularities -/

section Rational

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `(X, P)` is a *rational singularity* (FA 3.3.4, 3.4.1; Artin 1966) if
`(R¹f_*𝒪_Y)_P = 0` for the minimal resolution `f : Y ⟶ X` of `(X, P)`. -/
@[mmp "def_fa3_rational_singularity"]
def IsRationalSurfaceSingularity (P : X) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : QuasiCompact (f ≫ sX)) (_ : IsLocallyNoetherian Y)
    (_ : IsNormal Y), IsMinimalGermResolution sX P f ∧
    Subsingleton ((((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)).presheaf.stalk P)

end Rational

/-! ### Du Val graphs and singularities -/

namespace WeightedGraph

variable {V : Type*} [Fintype V] (Γ : WeightedGraph V)

/-- `Γ` is a *Du Val graph* (FA 3.1.2): `p_j = 0`, `n_j = 2` and `β_j = 0` for every vertex
`v_j`. -/
@[mmp "def_fa3_du_val"]
def IsDuVal : Prop := ∀ j, Γ.genus j = 0 ∧ Γ.weight j = 2 ∧ Γ.boundary j = 0

/-- The empty graph is a Du Val graph (FA 3.1.2). -/
@[mmp "def_fa3_du_val"]
theorem isDuVal_of_isEmpty [IsEmpty V] : Γ.IsDuVal := isEmptyElim

end WeightedGraph

section DuVal

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `(X, P; B)` is a *Du Val singularity* (FA 3.1.2) if the weighted dual graph `Γ(f)` of the
minimal resolution `f` is a Du Val graph. -/
@[mmp "def_fa3_du_val"]
def IsDuValSingularity (P : X) (B : QDivisor X) : Prop :=
  ∃ (n : ℕ) (Γ : WeightedGraph (Fin n)), IsMinimalWeightedDualGraph sX P B Γ ∧ Γ.IsDuVal

end DuVal

end MMP.Flips
