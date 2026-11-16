module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
public import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.CohenMacaulay.SerreDuality
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenSubscheme
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenImmersionRange
public import MMP.AlgebraicTopology.BorelMoore.Restriction
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
import MMP.AlgebraicGeometry.Chow.CycleClassTopDegree
import MMP.AlgebraicGeometry.CycleMap.Stacks.OpenRestriction
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreLongExact
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AffinePointsLevelSet
import MMP.AlgebraicTopology.BorelMoore.FiniteChains
import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
import MMP.AlgebraicTopology.BorelMoore.TopHomologyRestriction
import MMP.AlgebraicTopology.PoincareDuality.Homotopy
import MMP.AlgebraicTopology.PoincareDuality.Localize
import MMP.AlgebraicTopology.PoincareDuality.Punctured
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPointEuclideanChart
import MMP.AlgebraicGeometry.Semialgebraic.Operations
import MMP.AlgebraicGeometry.Semialgebraic.TriangulationProof
import MMP.AlgebraicTopology.Triangulation.StdTriangulation
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ProjectiveSpace
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionTerminal
public import MMP.Topology.KrullDimensionProperClosed
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Cycle spans under restriction to an open subscheme, and connectedness of ample divisors

Let `P` be a projective complex variety, `A ⊆ P` a closed subset and `U = P ∖ A`. Restriction of
Borel–Moore homology `H^BM_{2r}(P, ℚ) → H^BM_{2r}(U, ℚ)` maps the cycle span `Cyc_r(P)` onto
`Cyc_r(U)`: the class of an `r`-dimensional subvariety `V ⊆ P` restricts to the class of
`V ∩ U` (or to `0` if `V ∩ U = ∅`), and every `r`-dimensional subvariety of `U` is `V ∩ U` for
its closure `V`. If `dim A ≤ r`, the kernel of this restriction on `Cyc_r(P)` is spanned by the
classes of the `r`-dimensional irreducible components of `A`: by the localization sequence
`H_{2r}(A, ℚ) → H_{2r}(P, ℚ) → H^BM_{2r}(U, ℚ)` a class in the kernel comes from `H_{2r}(A, ℚ)`,
which has a basis of such classes. Consequently the cycle rank `ρ_r = dim_ℚ Cyc_r` is unchanged
by removing a closed subset of dimension `< r`, and strictly drops when `A` has an
`r`-dimensional component; the latter uses that `Cyc_r(P)` is finite-dimensional, which holds
because `P(ℂ)` is homeomorphic to a finite polyhedron.

The same localization argument shows that for a projective birational morphism `h : M → N`
from a smooth projective threefold to a normal projective variety, the strict transform of a
homologically trivial `ℚ`-divisor on `N` becomes homologically trivial after adding a
combination of prime divisors of `M` with images of dimension at most one.

Finally, on a normal projective variety of dimension at least two, an effective divisor `A`
with `𝒪_X(A)` ample has connected support: normality gives Serre's condition `S₂`, hence depth
at least two at every closed point, which is what `MMP.Mori.isConnected_support_of_two_le_depth`
requires.

## Main results

* `MMP.Analytic.map_restrict_cycleSpan_compl`: restriction maps `Cyc_r(P)` onto `Cyc_r(P ∖ A)`.
* `MMP.Analytic.cycleSpan_inf_ker_restrict_eq_span_fundamentalClass`: for `dim A ≤ r`, the
  kernel of `Cyc_r(V) → H^BM_{2r}(V ∖ A, ℚ)` is spanned by the classes of the `r`-dimensional
  subvarieties contained in `A`.
* `MMP.Analytic.cycleRank_eq_of_topologicalKrullDim_lt`: `ρ_r(V ∖ A) = ρ_r(V)` if `dim A < r`.
* `MMP.Analytic.cycleRank_opens_lt_of_mem_irreducibleComponents`: `ρ_r(V ∖ A) < ρ_r(V)` if
  `dim A ≤ r` and `A` has an `r`-dimensional irreducible component.
* `MMP.Analytic.cycleRank_eq_cycleRank_compl_add_finrank_span`: for `dim A ≤ r`,
  `ρ_r(V) = ρ_r(V ∖ A) + dim_ℚ ⟨[Z] : Z ⊆ A, dim Z = r⟩`.
* `MMP.Analytic.finiteDimensional_cycleSpan`: `Cyc_r(V)` is finite-dimensional for `V`
  projective.
* `MMP.Fourfold.exists_divisorClass_inverseTransformDivisor_add_eq_zero`: the correction of the
  strict transform of a homologically trivial divisor by divisors over curves and points.
* `MMP.Mori.isConnected_support_of_isAmple_divisorSheaf_of_isNormal`: an effective ample
  divisor on a normal projective variety of dimension at least two is connected.

## Implementation notes

* The restriction `H^BM_{2r}(P, ℚ) → H^BM_{2r}(U, ℚ)` of `map_restrict_cycleSpan_compl` is the
  composite of `MMP.borelMooreHomology.restrict` to the open subset `U(ℂ) ⊆ P(ℂ)`
  of Fulton's underlying space (`MMP.UnderlyingSpace.opensRangeMap U.ι`), read on
  `U(ℂ)` through `MMP.UnderlyingSpace.homeomorphOpensRangeMap`, with the
  identifications `MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace` of the complex
  realizations with the underlying spaces, in which `MMP.Analytic.fundamentalClass` is defined.
* The open subscheme `P ∖ A` is an open `U : P.Opens` with underlying set `Aᶜ`; its structure
  over `ℂ` is any one making the inclusion a morphism over `ℂ` (there is exactly one).
* In `cycleSpan_inf_ker_restrict_eq_span_fundamentalClass` the restriction is to the open subset
  `{x | x.toScheme ∈ Aᶜ}` of `V^an`, homeomorphic to the realization of `V ∖ A`; the kernel does
  not depend on this choice. It is written `Cyc_r(V) ⊓ ker` as a submodule of `H_{2r}(V, ℚ)`.
  Since `dim A ≤ r`, the `r`-dimensional subvarieties contained in `A` are exactly its
  `r`-dimensional irreducible components.
* Finite-dimensionality of `Cyc_r(V)`: embed `V ⊆ ℙᴺ` and send a point to the real coordinates
  of the matrix of the orthogonal projection onto its line. On each standard chart this is a
  rational function of the coordinates, so the image of `V(ℂ)` is a compact semialgebraic set,
  homeomorphic to the polyhedron `|Δ|` of a finite simplicial complex by the triangulation
  theorem. The open vertex stars cover `|Δ|` and their nonempty intersections are star-shaped,
  so Mayer–Vietoris for finite singular chains, by induction on the number of stars, makes
  `H_*(|Δ|, ℚ)` finite-dimensional; on a compact space locally finite chains are finite.
* `H_4(-, ℚ)` in the threefold statement is `MMP.Fourfold.RationalHomology`, the class of a
  `ℚ`-divisor is `MMP.Chow.divisorClass` (Stacks cycles) and the strict transform is
  `MMP.Mori.inverseTransformDivisor h`. Each prime component `E` of the correction satisfies
  `dim h(E) ≤ 1`; as `N` is a threefold, every such `E` is exceptional.
* The connectedness of ample divisors is stated over an arbitrary field `k`; the source's case
  is `k = ℂ`. The divisor is an ideal sheaf with `Stacks.Divisors.IsEffectiveCartierDivisor`,
  its invertible sheaf is `Stacks.Divisors.divisorSheaf A`, and `Supp A` is `A.support`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998].
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 15.
* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], Theorem 9.2.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1.
-/

@[expose] public section

namespace MMP.Analytic

/-! ### Restriction of cycle spans to an open subscheme -/

section CycleSpanRestriction

open CategoryTheory AlgebraicGeometry MMP MMP.UnderlyingSpace

section

variable (P : Scheme.{0}) [P.Over (Spec (.of ℂ))] [IsComplexScheme P] (U : P.Opens)
  [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] (r : ℕ)

/-- The restriction `H^BM_{2r}(P, ℚ) → H^BM_{2r}(U, ℚ)` to an open subscheme `U`. -/
private noncomputable def restrictionMap :
    borelMooreHomology (P ↘ Spec (.of ℂ)) (2 * r) ⟶
      borelMooreHomology (U.toScheme ↘ Spec (.of ℂ)) (2 * r) :=
  borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := P)).continuous⟩)
      (ComplexPoints.homeomorphUnderlyingSpace (X := P)).isProperMap (2 * r : ℕ) ≫
    borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
      (Y := TopCat.of (UnderlyingSpace ℂ P)) (opensRangeMap U.ι) (2 * r : ℕ) ≫
    borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_, (homeomorphOpensRangeMap U.ι).symm.continuous⟩)
      (homeomorphOpensRangeMap U.ι).symm.isProperMap (2 * r : ℕ) ≫
    borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_,
        (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm.continuous⟩)
      (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm.isProperMap
      (2 * r : ℕ)

/-- Push-forward along a homeomorphism after push-forward along its inverse is the identity. -/
private lemma pushforward_pushforward_symm {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (j : ℤ) (a : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of B) j) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom ⟨_, e.continuous⟩)
        e.isProperMap j).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ⟨_, e.symm.continuous⟩) e.symm.isProperMap j).hom a) = a :=
  borelMooreHomology.pushforward_symm_pushforward_homeomorph ℚ _ e.symm j a

/-- `restrictionMap` applied to a class, as the four maps applied in turn. -/
private lemma restrictionMap_apply
    (x : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints (P ↘ Spec (.of ℂ)))) (2 * r : ℕ)) :
    (restrictionMap P U r).hom x =
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ⟨_,
          (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm.continuous⟩)
        (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm.isProperMap
        (2 * r : ℕ)).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ⟨_, (homeomorphOpensRangeMap U.ι).symm.continuous⟩)
        (homeomorphOpensRangeMap U.ι).symm.isProperMap (2 * r : ℕ)).hom
      ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
        (Y := TopCat.of (UnderlyingSpace ℂ P)) (opensRangeMap U.ι) (2 * r : ℕ)).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ⟨_,
          (ComplexPoints.homeomorphUnderlyingSpace (X := P)).continuous⟩)
        (ComplexPoints.homeomorphUnderlyingSpace (X := P)).isProperMap
        (2 * r : ℕ)).hom x))) :=
  rfl

/-- The class of a point `x = U.ι z` of `U` restricts to the class of `z`: the class of
`closure {x}` restricts to the class of `closure {x} ∩ U`. -/
private lemma restrictionMap_fundamentalClass_of_mem (z : U.toScheme)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (P ↘ Spec (.of ℂ)) (U.ι.base z) = r)
    (hz : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (U.toScheme ↘ Spec (.of ℂ)) z = r) :
    (restrictionMap P U r).hom (fundamentalClass (U.ι.base z) hx) = fundamentalClass z hz := by
  rw [fundamentalClass_eq, fundamentalClass_eq, restrictionMap_apply, pushforward_pushforward_symm,
    MMP.Chow.restrict_pointCycleClass_eq_pushforward ℚ U.ι z hx hz]
  exact congrArg _ (borelMooreHomology.pushforward_symm_pushforward_homeomorph ℚ _
    (homeomorphOpensRangeMap U.ι) _ _)

/-- The class of a point off `U` restricts to `0`: its closure misses `U`. -/
private lemma restrictionMap_fundamentalClass_of_notMem (x : P)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (P ↘ Spec (.of ℂ)) x = r) (hxU : x ∉ U) :
    (restrictionMap P U r).hom (fundamentalClass x hx) = 0 := by
  rw [fundamentalClass_eq, restrictionMap_apply, pushforward_pushforward_symm]
  rw [MMP.Chow.restrict_pointCycleClass_eq_zero_of_notMem ℚ U.ι x hx
    (by rwa [Scheme.Opens.range_ι])]
  rw [map_zero, map_zero]
  rfl

end

/-- **Restriction of cycle spans.** Let `P` be a projective complex scheme and `A ⊆ P` a closed
subset. For every `r`, the restriction `H^BM_{2r}(P, ℚ) → H^BM_{2r}(P ∖ A, ℚ)` to the open
subscheme `P ∖ A` maps the cycle span `Cyc_r(P)` onto `Cyc_r(P ∖ A)`. -/
@[mmp "lem_mmp_bm_projective_cycle_restriction"]
public theorem map_restrict_cycleSpan_compl (P : Scheme.{0}) [P.Over (Spec (.of ℂ))]
    (hP : IsProjectiveMorphism (P ↘ Spec (.of ℂ))) [IsComplexScheme P]
    (A : TopologicalSpace.Closeds P) (U : P.Opens) (hU : (U : Set P) = (A : Set P)ᶜ)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] (r : ℕ) :
    Submodule.map
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := P)).continuous⟩)
          (ComplexPoints.homeomorphUnderlyingSpace (X := P)).isProperMap (2 * r : ℕ) ≫
        borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
          (Y := TopCat.of (UnderlyingSpace ℂ P)) (opensRangeMap U.ι) (2 * r : ℕ) ≫
        borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_, (homeomorphOpensRangeMap U.ι).symm.continuous⟩)
          (homeomorphOpensRangeMap U.ι).symm.isProperMap (2 * r : ℕ) ≫
        borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_,
            (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm.continuous⟩)
          (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm.isProperMap
          (2 * r : ℕ)).hom)
      (cycleSpan P r) = cycleSpan U.toScheme r := by
  change Submodule.map (restrictionMap P U r).hom (cycleSpan P r) = _
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap, cycleSpan_le_iff]
    intro x hx
    rw [Submodule.mem_comap]
    by_cases hxU : x ∈ U
    · obtain ⟨z, rfl⟩ : ∃ z : U.toScheme, U.ι.base z = x := ⟨⟨x, hxU⟩, rfl⟩
      rw [restrictionMap_fundamentalClass_of_mem P U r z hx
        ((MMP.Chow.relativeDimension_eq_of_isOver U.ι z).trans hx)]
      exact fundamentalClass_mem_cycleSpan _ _
    · rw [restrictionMap_fundamentalClass_of_notMem P U r x hx hxU]
      exact Submodule.zero_mem _
  · rw [cycleSpan_le_iff]
    intro z hz
    have hx := (MMP.Chow.relativeDimension_eq_of_isOver U.ι z).symm.trans hz
    exact ⟨_, fundamentalClass_mem_cycleSpan _ hx,
      restrictionMap_fundamentalClass_of_mem P U r z hx hz⟩

end CycleSpanRestriction

/-! ### Cycle classes of points (Stacks cycles) -/

section PointClasses

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open MMP.UnderlyingSpace MMP.borelMooreHomology Stacks.Chow
open scoped MMP.SubschemeOver

/-- Over `ℂ`, the delta-dimension of a point is the dimension of its closure. -/
private lemma relativeDimension_eq_natCast_iff {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (x : X) (n : ℕ) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n ↔
      topologicalKrullDim (closure ({x} : Set X)) = n := by
  rw [topologicalKrullDim_closure_singleton_eq ℂ (X ↘ Spec (.of ℂ)) x]
  have h0 := relativeDimension_fieldChowSituation_nonneg ℂ (X ↘ Spec (.of ℂ)) x
  constructor
  · intro h
    rw [h, Int.toNat_natCast]
  · intro h
    have h' : (relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) x).toNat = n := by exact_mod_cast h
    omega

/-- **Top-degree homology is spanned by the components** (Fulton, Lemma 19.1.1): on a complex
scheme of dimension at most `n`, `H_{2n}(X, ℚ)` is spanned by the cycle classes of the generic
points of the irreducible components (`0` for a component of smaller dimension). -/
private theorem mem_span_pointCycleClassOrZero_of_dimension_le {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] {n : ℕ} (hX : topologicalKrullDim X ≤ n)
    (z : Chow.BMHomology ℚ X (2 * n)) :
    z ∈ Submodule.span ℚ (Set.range fun j : irreducibleComponents X ↦
      Chow.pointCycleClassOrZero ℚ n (Chow.componentGenericPoint j)) := by
  have hz : z ∈ (⊤ : Submodule ℚ (Chow.BMHomology ℚ X (2 * n))) := Submodule.mem_top
  rw [← (Chow.linearIndependent_and_span_eq_top_pointCycleClass ℚ hX).2] at hz
  refine Submodule.span_mono ?_ hz
  rintro _ ⟨j, rfl⟩
  exact ⟨j.1, by dsimp only; rw [Chow.pointCycleClassOrZero, dif_pos j.2]⟩

/-- **Localization in top degree.** Let `X` be a complex scheme and `U ⊆ X` an open subscheme
whose complement has dimension at most `n`. A class of `H_{2n}(X, ℚ)` restricting to zero on
`U(ℂ)` is a combination of the cycle classes of points of `X` off `U`. -/
theorem mem_span_pointCycleClassOrZero_of_restrict_eq_zero {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (U : X.Opens)
    (O : Opens (TopCat.of (UnderlyingSpace ℂ X)))
    (hO : ∀ p : UnderlyingSpace ℂ X, p ∈ O ↔ p.toHom (IsLocalRing.closedPoint ℂ) ∈ U)
    {n : ℕ} (hdim : topologicalKrullDim ↥((U : Set X)ᶜ) ≤ n) (x : Chow.BMHomology ℚ X (2 * n))
    (hx : restrict ℚ (ModuleCat.of ℚ ℚ) (Y := TopCat.of (UnderlyingSpace ℂ X)) O (2 * n : ℕ) x =
      0) :
    x ∈ Submodule.span ℚ (Chow.pointCycleClassOrZero ℚ n '' {y | y ∉ U}) := by
  classical
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X) with hI
  have hrange : Set.range I.subschemeι = (U : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  haveI : IsComplexScheme I.subscheme := IsComplexScheme.of_isClosedImmersion I.subschemeι
  obtain ⟨δ, -, h2, -⟩ :=
    IsComplexScheme.exists_borelMooreHomology_longExact ℚ (ModuleCat.of ℚ ℚ) X I.subschemeι
  have hO' : complOpens (Y := TopCat.of (UnderlyingSpace ℂ X))
      (isClosed_range_map_of_isClosedImmersion I.subschemeι) = O := by
    ext p
    change p ∉ Set.range (mapFun (K := ℂ) I.subschemeι) ↔ _
    rw [range_mapFun_of_isClosedImmersion, Set.mem_setOf_eq, hrange, SetLike.mem_coe, hO]
    exact not_not
  obtain ⟨z, rfl⟩ := (h2 (2 * n : ℕ) x).mp (by rwa [hO'])
  have hZ : topologicalKrullDim I.subscheme ≤ n := by
    have hmem : ∀ z, I.subschemeι.base z ∈ (U : Set X)ᶜ := fun z ↦ by
      rw [← hrange]; exact Set.mem_range_self z
    exact ((I.subschemeι.isClosedEmbedding.isInducing.codRestrict
      hmem).topologicalKrullDim_le).trans hdim
  have hz' := Submodule.mem_map_of_mem (f := (borelMooreHomology.pushforward ℚ
    (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) I.subschemeι))
    (isProperMap_map (K := ℂ) I.subschemeι) (2 * n : ℕ)).hom)
    (mem_span_pointCycleClassOrZero_of_dimension_le hZ z)
  rw [Submodule.map_span] at hz'
  refine Submodule.span_le.2 ?_ hz'
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  by_cases hj : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (I.subscheme ↘ Spec (.of ℂ)) (Chow.componentGenericPoint j) = n
  · change (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) I.subschemeι)) (isProperMap_map (K := ℂ) I.subschemeι)
      (2 * n : ℕ)).hom (Chow.pointCycleClassOrZero ℚ n (Chow.componentGenericPoint j)) ∈ _
    rw [Chow.pointCycleClassOrZero, dif_pos hj]
    change borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) I.subschemeι)) (isProperMap_map (K := ℂ) I.subschemeι)
      (2 * n : ℕ) (Chow.pointCycleClass ℚ _ hj) ∈ _
    rw [Chow.pushforward_pointCycleClass, residueDegree_eq_one_of_isClosedImmersion,
      Nat.cast_one, one_smul]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    change _ ∈ (U : Set X)ᶜ
    rw [← hrange]
    exact Set.mem_range_self _
  · change (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) I.subschemeι)) (isProperMap_map (K := ℂ) I.subschemeι)
      (2 * n : ℕ)).hom (Chow.pointCycleClassOrZero ℚ n (Chow.componentGenericPoint j)) ∈ _
    rw [Chow.pointCycleClassOrZero, dif_neg hj, map_zero]
    exact Submodule.zero_mem _

end PointClasses

/-! ### The kernel of restriction to the complement of a closed subset -/

section CycleSpanKernel

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MMP (UnderlyingSpace)
open MMP.UnderlyingSpace MMP.borelMooreHomology
open scoped MMP.SubschemeOver

section Transport

variable {X Y : TopCat.{0}} [T2Space X] [T2Space Y] (f : X ⟶ Y) (hf : IsProperMap f)
  {U : Opens Y} {n : ℤ}

/-- If `f⁻¹(U) = W` and `a|_W = 0`, then `(f_* a)|_U = 0`: restriction commutes with proper
push-forward. -/
private lemma restrict_pushforward_eq_zero_of_comap_eq {W : Opens X}
    (hUW : Opens.comap f.hom U = W)
    {a : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) X n}
    (ha : (restrict ℚ (ModuleCat.of ℚ ℚ) W n).hom a = 0) :
    (restrict ℚ (ModuleCat.of ℚ ℚ) U n).hom
      ((pushforward ℚ (ModuleCat.of ℚ ℚ) f hf n).hom a) = 0 := by
  subst hUW
  rw [restrict_pushforward_apply, ha, map_zero]

end Transport

section Underlying

variable (V : Scheme.{0}) [V.Over (Spec (.of ℂ))] [MMP.IsComplexScheme V]
  {A : Set V} (hA : IsClosed A)

set_option hygiene false in
/-- The reduced closed subscheme structure on `A`. -/
local notation "ιA" => (Scheme.IdealSheafData.vanishingIdeal (⟨A, hA⟩ : Closeds V)).subschemeι

set_option hygiene false in
/-- The open complement of `A(ℂ)` in Fulton's underlying space `V(ℂ)`. -/
local notation "UA" => complOpens (Y := TopCat.of (UnderlyingSpace ℂ V))
  (isClosed_range_map_of_isClosedImmersion ιA)

/-- The reduced closed subscheme on `A` has image `A`. -/
private lemma range_subschemeι : Set.range ιA = A := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- A point of `V(ℂ)` lies off `A(ℂ)` iff its closed point lies off `A`. -/
private lemma mem_complOpens_iff (p : UnderlyingSpace ℂ V) :
    p ∈ UA ↔ p.toHom (IsLocalRing.closedPoint ℂ) ∉ A := by
  change p ∉ Set.range (mapFun (K := ℂ) ιA) ↔ _
  rw [range_mapFun_of_isClosedImmersion, Set.mem_setOf_eq, range_subschemeι]

/-- The class of a point of `A` vanishes on `V(ℂ) ∖ A`: the closure of the point lies in `A`. -/
private lemma restrict_pointCycleClass_eq_zero_of_mem {r : ℕ} {y : V} (hyA : y ∈ A)
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (V ↘ Spec (.of ℂ)) y = r) :
    (restrict ℚ (ModuleCat.of ℚ ℚ) UA ((2 * r : ℕ) : ℤ)).hom
      (MMP.Chow.pointCycleClass ℚ y hy) = 0 := by
  refine MMP.Chow.restrict_pointCycleClass_eq_zero ℚ y hy UA
    (Set.disjoint_left.2 fun p hp hp' ↦ ?_)
  rw [range_mapFun_of_isClosedImmersion, Set.mem_setOf_eq,
    Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt] at hp'
  exact (mem_complOpens_iff V hA p).1 hp
    (closure_minimal (Set.singleton_subset_iff.2 hyA) hA hp')

/-- The scheme point of `p ∈ V(ℂ)`, read through `V^an ≃ V(ℂ)`. -/
private lemma toScheme_homeomorphUnderlyingSpace_symm (p : UnderlyingSpace ℂ V) :
    (ComplexPoints.homeomorphUnderlyingSpace.symm p).toScheme =
      p.toHom (IsLocalRing.closedPoint ℂ) :=
  congrArg p.toHom (Subsingleton.elim _ _)

/-- Under `V^an ≃ V(ℂ)`, the complement of `A(ℂ)` corresponds to the complement of `A^an`. -/
private lemma comap_homeomorphUnderlyingSpace_complOpens :
    Opens.comap (TopCat.ofHom (ComplexPoints.homeomorphUnderlyingSpace (X := V) :
      C(ComplexPoints (V ↘ Spec (.of ℂ)), UnderlyingSpace ℂ V))).hom UA =
      ⟨{x | x.toScheme ∈ Aᶜ},
        ComplexPoints.isOpen_setOf_toScheme_mem hA.isOpen_compl⟩ := by
  ext x
  change ComplexPoints.homeomorphUnderlyingSpace x ∈ UA ↔ x.toScheme ∈ Aᶜ
  rw [mem_complOpens_iff V hA, ← toScheme_homeomorphUnderlyingSpace_symm,
    Homeomorph.symm_apply_apply]
  rfl

/-- Under `V(ℂ) ≃ V^an`, the complement of `A^an` corresponds to the complement of `A(ℂ)`. -/
private lemma comap_homeomorphUnderlyingSpace_symm :
    Opens.comap (TopCat.ofHom
      ((ComplexPoints.homeomorphUnderlyingSpace (X := V)).symm :
      C(UnderlyingSpace ℂ V, ComplexPoints (V ↘ Spec (.of ℂ))))).hom
      ⟨{x | x.toScheme ∈ Aᶜ},
        ComplexPoints.isOpen_setOf_toScheme_mem hA.isOpen_compl⟩ = UA := by
  ext p
  change (ComplexPoints.homeomorphUnderlyingSpace.symm p).toScheme ∈ Aᶜ ↔ p ∈ UA
  rw [mem_complOpens_iff V hA, toScheme_homeomorphUnderlyingSpace_symm]
  rfl

end Underlying

/-- Let `V` be a projective complex variety and `A ⊆ V` a closed subset of dimension at most
`r`. The kernel of the restriction `Cyc_r(V) → H^BM_{2r}(V ∖ A, ℚ)` is the `ℚ`-span of the
fundamental classes `[Z] ∈ H_{2r}(V, ℚ)` of the `r`-dimensional irreducible closed subvarieties
`Z ⊆ A`, i.e. of the `r`-dimensional irreducible components of `A`. -/
@[mmp "lem_oai4_cycle_rank"]
public theorem cycleSpan_inf_ker_restrict_eq_span_fundamentalClass
    (V : Scheme.{0}) [V.Over (Spec (.of ℂ))] [MMP.IsComplexScheme V]
    (hV : MMP.Mori.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))) {A : Set V} (hA : IsClosed A)
    {r : ℕ} (hdim : topologicalKrullDim A ≤ r) :
    haveI : T2Space (ComplexPoints (V ↘ Spec (.of ℂ))) :=
      ComplexPoints.homeomorphUnderlyingSpace.isEmbedding.t2Space
    cycleSpan V r ⊓ LinearMap.ker
        (MMP.borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
          (Y := TopCat.of (ComplexPoints (V ↘ Spec (.of ℂ))))
          ⟨{x | x.toScheme ∈ Aᶜ}, ComplexPoints.isOpen_setOf_toScheme_mem hA.isOpen_compl⟩
          ((2 * r : ℕ) : ℤ)).hom =
      Submodule.span ℚ (Set.range fun y : {y : V // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (V ↘ Spec (.of ℂ)) y = r ∧ y ∈ A} ↦
          fundamentalClass y.1 y.2.1) := by
  haveI : T2Space (ComplexPoints (V ↘ Spec (.of ℂ))) :=
    ComplexPoints.homeomorphUnderlyingSpace.isEmbedding.t2Space
  set e := ComplexPoints.homeomorphUnderlyingSpace (X := V)
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro x ⟨-, hx⟩
    rw [← pushforward_symm_pushforward_homeomorph ℚ _ e _ x]
    let W : V.Opens := ⟨Aᶜ, hA.isOpen_compl⟩
    have hdim' : topologicalKrullDim ((W : Set V)ᶜ : Set V) ≤ r := by
      change topologicalKrullDim ((Aᶜ)ᶜ : Set V) ≤ r
      rwa [compl_compl]
    refine (Submodule.map_span_le _ _ _).2 ?_ ⟨_, mem_span_pointCycleClassOrZero_of_restrict_eq_zero
      W _ (fun p ↦ mem_complOpens_iff V hA p) hdim' _
      (restrict_pushforward_eq_zero_of_comap_eq _ e.isProperMap
        (comap_homeomorphUnderlyingSpace_complOpens V hA) hx), rfl⟩
    rintro _ ⟨y, hyW, rfl⟩
    rw [MMP.Chow.pointCycleClassOrZero]
    split_ifs with hy
    · refine Submodule.subset_span ⟨⟨y, hy, ?_⟩, rfl⟩
      by_contra hyA
      exact hyW hyA
    · convert Submodule.zero_mem _ using 1
      exact map_zero _
  · rintro _ ⟨⟨y, hy, hyA⟩, rfl⟩
    exact ⟨fundamentalClass_mem_cycleSpan y hy,
      restrict_pushforward_eq_zero_of_comap_eq _ e.symm.isProperMap
        (comap_homeomorphUnderlyingSpace_symm V hA)
        (restrict_pointCycleClass_eq_zero_of_mem V hA hyA hy)⟩

/-! ### Removing a closed subset of dimension `< r` -/

/-- A point of delta-dimension `r` does not lie in a closed subset of dimension `< r`: its
closure, of dimension `r`, would lie in it. -/
private lemma notMem_of_topologicalKrullDim_lt {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] {A : Set V} (hA : IsClosed A) {r : ℕ}
    (hdim : topologicalKrullDim A < r) (y : V)
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (V ↘ Spec (.of ℂ)) y = r) : y ∉ A := by
  intro hyA
  have h1 := (relativeDimension_eq_natCast_iff y r).1 hy
  have hle : topologicalKrullDim (closure ({y} : Set V)) ≤ topologicalKrullDim A :=
    (Topology.IsInducing.subtypeVal.codRestrict fun z : closure ({y} : Set V) ↦
      closure_minimal (Set.singleton_subset_iff.2 hyA) hA z.2).topologicalKrullDim_le
  exact absurd (h1 ▸ hle) (not_le.2 hdim)

/-- A linear map injective on `S` maps it onto a submodule of the same rank. -/
private lemma finrank_eq_of_map_eq {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N]
    [Module ℚ N] (f : M →ₗ[ℚ] N) (S : Submodule ℚ M) (T : Submodule ℚ N)
    (h : S.map f = T) (hinj : ∀ x ∈ S, f x = 0 → x = 0) :
    Module.finrank ℚ T = Module.finrank ℚ S := by
  subst h
  rw [← LinearMap.range_domRestrict]
  refine LinearMap.finrank_range_of_inj ?_
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨x, hx⟩ h0
  exact Subtype.ext (hinj x hx h0)

/-- Push-forward along a homeomorphism is injective. -/
private lemma pushforward_homeomorph_injective {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (j : ℤ) :
    Function.Injective (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom ⟨_, e.continuous⟩)
      e.isProperMap j).hom :=
  Function.LeftInverse.injective (pushforward_symm_pushforward_homeomorph ℚ _ e j)

/-- The restriction `Cyc_r(V) → Cyc_r(U)` of `MMP.Analytic.map_restrict_cycleSpan_compl`, read on
`V(ℂ)`: a class it kills restricts to zero on `V(ℂ) ∖ A`. -/
private lemma restrict_compl_eq_zero {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [MMP.IsComplexScheme V] {A : Set V} (hA : IsClosed A)
    (U : V.Opens) (hU : (U : Set V) = Aᶜ)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] (n : ℤ)
    [T2Space (ComplexPoints (V ↘ Spec (.of ℂ)))]
    {x : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints (V ↘ Spec (.of ℂ)))) n}
    (h0 : (pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := V)).continuous⟩)
          (ComplexPoints.homeomorphUnderlyingSpace (X := V)).isProperMap n ≫
        restrict ℚ (ModuleCat.of ℚ ℚ)
          (Y := TopCat.of (UnderlyingSpace ℂ V)) (opensRangeMap U.ι) n ≫
        pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_, (homeomorphOpensRangeMap U.ι).symm.continuous⟩)
          (homeomorphOpensRangeMap U.ι).symm.isProperMap n ≫
        pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_,
            (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm.continuous⟩)
          (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm.isProperMap
          n).hom x = 0) :
    (restrict ℚ (ModuleCat.of ℚ ℚ) (Y := TopCat.of (ComplexPoints (V ↘ Spec (.of ℂ))))
      ⟨{x | x.toScheme ∈ Aᶜ}, ComplexPoints.isOpen_setOf_toScheme_mem hA.isOpen_compl⟩
      n).hom x = 0 := by
  set e := ComplexPoints.homeomorphUnderlyingSpace (X := V)
  have hcomap : Opens.comap (TopCat.ofHom (e.symm : C(UnderlyingSpace ℂ V,
      ComplexPoints (V ↘ Spec (.of ℂ))))).hom
      ⟨{x | x.toScheme ∈ Aᶜ},
        ComplexPoints.isOpen_setOf_toScheme_mem hA.isOpen_compl⟩ =
      opensRangeMap U.ι := by
    ext p
    change (e.symm p).toScheme ∈ Aᶜ ↔ p ∈ opensRangeMap U.ι
    rw [mem_opensRangeMap_ι_iff, toScheme_homeomorphUnderlyingSpace_symm, ← hU]
    rfl
  have h1 : (restrict ℚ (ModuleCat.of ℚ ℚ) (opensRangeMap U.ι) n).hom
      ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom ⟨_, e.continuous⟩) e.isProperMap n).hom
        x) = 0 := by
    apply pushforward_homeomorph_injective (homeomorphOpensRangeMap U.ι).symm
    apply pushforward_homeomorph_injective
      (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm
    simpa using h0
  have h2 := restrict_pushforward_eq_zero_of_comap_eq _ e.symm.isProperMap hcomap h1
  rwa [pushforward_symm_pushforward_homeomorph ℚ _ e n x] at h2

/-- **Removing a small closed subset keeps the cycle rank.** Let `V` be a projective complex
variety and `A ⊆ V` a closed subset with `dim A < r`, and let `U = V ∖ A` be the complementary
open subscheme. Then `ρ_r(U) = ρ_r(V)`. -/
@[mmp "lem_oai4_cycle_rank_i"]
public theorem cycleRank_eq_of_topologicalKrullDim_lt
    (V : Scheme.{0}) [V.Over (Spec (.of ℂ))] [MMP.IsComplexScheme V]
    (hV : MMP.Mori.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))) {A : Set V} (hA : IsClosed A)
    {r : ℕ} (hdim : topologicalKrullDim A < r)
    (U : V.Opens) (hU : (U : Set V) = Aᶜ)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] :
    cycleRank U.toScheme r = cycleRank V r := by
  haveI : T2Space (ComplexPoints (V ↘ Spec (.of ℂ))) :=
    ComplexPoints.homeomorphUnderlyingSpace.isEmbedding.t2Space
  have hker := cycleSpan_inf_ker_restrict_eq_span_fundamentalClass V hV hA hdim.le
  haveI : IsEmpty {y : V // Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (V ↘ Spec (.of ℂ)) y = r ∧ y ∈ A} :=
    ⟨fun y ↦ notMem_of_topologicalKrullDim_lt hA hdim y.1 y.2.1 y.2.2⟩
  rw [Set.range_eq_empty, Submodule.span_empty] at hker
  refine finrank_eq_of_map_eq _ _ _
    (map_restrict_cycleSpan_compl V hV.isProjective ⟨A, hA⟩ U hU r)
    fun x hx h0 ↦ hker.le ⟨hx, LinearMap.mem_ker.2 (restrict_compl_eq_zero hA U hU _ h0)⟩

end CycleSpanKernel

/-! ### Finite-dimensionality of the cycle span of a projective variety -/

noncomputable section CycleRankDrop

section Homology

open MMP MMP.SingularChain Set

section HFin

variable {Y : Type*} [TopologicalSpace Y]

/-- The `k`-cycles lying in `A`. -/
private def cyc (A : Set Y) : (k : ℕ) → Submodule ℚ (Chain ℚ Y k)
  | 0 => inside ℚ 0 A
  | k + 1 => inside ℚ (k + 1) A ⊓ LinearMap.ker (bd ℚ k)

/-- The `k`-boundaries of chains lying in `A`. -/
private def bnd (A : Set Y) (k : ℕ) : Submodule ℚ (Chain ℚ Y k) :=
  (inside ℚ (k + 1) A).map (bd ℚ k)

/-- Finite-dimensionality of `H_*(A; ℚ)`, computed with chains of `Y` lying in `A`. -/
private def HFin (A : Set Y) : Prop :=
  ∀ k, ∃ F : Set (Chain ℚ Y k), F.Finite ∧ cyc A k ≤ Submodule.span ℚ F ⊔ bnd A k

private lemma cyc_le_inside (A : Set Y) : ∀ k, cyc A k ≤ inside ℚ k A
  | 0 => le_rfl
  | _ + 1 => inf_le_left

private lemma bnd_le_cyc (A : Set Y) : ∀ k, bnd A k ≤ cyc A k
  | 0 => by
    rintro _ ⟨w, hw, rfl⟩
    exact bd_mem_inside hw
  | k + 1 => by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨bd_mem_inside hw, by simp [bd_bd]⟩

/-- A submodule contained in a finitely generated one modulo `B` is finitely generated modulo
`B` by finitely many of its own elements. -/
private lemma exists_finite_subset_le_span_sup {M : Type*} [AddCommGroup M] [Module ℚ M]
    {J B : Submodule ℚ M} {F : Set M} (hF : F.Finite) (hJ : J ≤ Submodule.span ℚ F ⊔ B) :
    ∃ G : Set M, G.Finite ∧ G ⊆ J ∧ J ≤ Submodule.span ℚ G ⊔ B := by
  classical
  set π := B.mkQ
  have hle : J.map π ≤ Submodule.span ℚ (π '' F) := by
    rw [Submodule.span_image]
    refine (Submodule.map_mono hJ).trans ?_
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  haveI : FiniteDimensional ℚ (Submodule.span ℚ (π '' F)) :=
    FiniteDimensional.span_of_finite ℚ (hF.image _)
  haveI : FiniteDimensional ℚ (J.map π) := Submodule.finiteDimensional_of_le hle
  obtain ⟨G₀, hG₀⟩ := (Submodule.fg_iff_finiteDimensional _).2 this
  have hlift : ∀ y ∈ (G₀ : Set (M ⧸ B)), ∃ x ∈ J, π x = y := fun y hy ↦ by
    have : y ∈ J.map π := hG₀ ▸ Submodule.subset_span hy
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, hx, rfl⟩
  choose! g hgJ hg using hlift
  refine ⟨g '' G₀, G₀.finite_toSet.image _, fun _ ⟨y, hy, hxy⟩ ↦ hxy ▸ hgJ y hy, ?_⟩
  intro x hx
  have hπx : π x ∈ Submodule.span ℚ (π '' (g '' G₀)) := by
    have : π '' (g '' (G₀ : Set (M ⧸ B))) = G₀ := by
      rw [Set.image_image]
      exact (Set.image_congr fun y hy ↦ hg y hy).trans (Set.image_id _)
    rw [this, hG₀]
    exact ⟨x, hx, rfl⟩
  rw [Submodule.span_image] at hπx
  obtain ⟨y, hy, hxy⟩ := hπx
  have : x - y ∈ B := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    exact sub_eq_zero.2 hxy.symm
  rw [show x = y + (x - y) by abel]
  exact Submodule.add_mem_sup hy this

private lemma bd_mem_cyc {A : Set Y} {k : ℕ} {w : Chain ℚ Y (k + 1)}
    (hw : bd ℚ k w ∈ inside ℚ k A) :
    bd ℚ k w ∈ cyc A k := by
  cases k with
  | zero => exact hw
  | succ k => exact ⟨hw, by simp [bd_bd]⟩

private lemma bnd_mono {A B : Set Y} (h : A ⊆ B) (k : ℕ) : bnd A k ≤ bnd B k :=
  Submodule.map_mono (inside_mono _ h)

private lemma le_span_sup_of_le {A B : Set Y} {k : ℕ} {F F' : Set (Chain ℚ Y k)} (hFF' : F ⊆ F')
    (hAB : A ⊆ B) (h : cyc A k ≤ Submodule.span ℚ F ⊔ bnd A k) :
    cyc A k ≤ Submodule.span ℚ F' ⊔ bnd B k :=
  h.trans (sup_le_sup (Submodule.span_mono hFF') (bnd_mono hAB k))

/-- A cycle of `U ∪ V` splits, up to a boundary, as a sum of chains of `U` and `V` whose
boundaries cancel. -/
private lemma exists_eq_add_add_bd_of_mem_cyc {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    {k : ℕ} {z : Chain ℚ Y (k + 1)} (hz : z ∈ cyc (U ∪ V) (k + 1)) :
    ∃ a ∈ inside ℚ (k + 1) U, ∃ b ∈ inside ℚ (k + 1) V, ∃ D ∈ inside ℚ (k + 2) (U ∪ V),
      bd ℚ k a + bd ℚ k b = 0 ∧ z = a + b + bd ℚ (k + 1) D := by
  set 𝒰 : Set (Set Y) := {U, V}
  have h𝒰 : ∀ W ∈ 𝒰, IsOpen W := by
    rintro W (rfl | rfl)
    · exact hU
    · exact hV
  have hsU : ⋃₀ 𝒰 = U ∪ V := by simp [𝒰]
  obtain ⟨hzi, hzb⟩ := hz
  have hzb : bd ℚ k z = 0 := hzb
  have hz' : z ∈ inside ℚ (k + 1) (⋃₀ 𝒰) := hsU ▸ hzi
  obtain ⟨a, ha, b, hb, hsplit⟩ :=
    exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 (k + 1) hz')
  have hρ : smallChainMap ℚ 𝒰 (k + 1) z = z - bd ℚ (k + 1) (smallHomotopy ℚ 𝒰 (k + 1) z) := by
    rw [smallChainMap_succ, hzb, map_zero, sub_zero]
  refine ⟨a, ha, b, hb, _, smallHomotopy_mem_inside_of_mem 𝒰 hzi, ?_,
    (eq_sub_iff_add_eq.1 (hsplit.symm.trans hρ)).symm⟩
  rw [← map_add, ← hsplit, bd_smallChainMap, hzb, map_zero]

/-- Chosen lifts `a g ∈ U`, `b g ∈ V` of the generators `g ∈ G`, with `∂ a g = g` and
`∂ b g = -g`, extend linearly to every `s ∈ span G`. -/
private lemma exists_lift_of_mem_span {U V : Set Y} {k : ℕ} {G : Set (Chain ℚ Y k)}
    {aG bG : Chain ℚ Y k → Chain ℚ Y (k + 1)} (haG : ∀ g ∈ G, aG g ∈ inside ℚ (k + 1) U)
    (hbG : ∀ g ∈ G, bG g ∈ inside ℚ (k + 1) V) (haGg : ∀ g ∈ G, bd ℚ k (aG g) = g)
    (hbGg : ∀ g ∈ G, bd ℚ k (bG g) = -g) {s : Chain ℚ Y k} (hs : s ∈ Submodule.span ℚ G) :
    ∃ A ∈ inside ℚ (k + 1) U, ∃ B ∈ inside ℚ (k + 1) V, bd ℚ k A = s ∧ bd ℚ k B = -s ∧
      A + B ∈ Submodule.span ℚ ((fun g ↦ aG g + bG g) '' G) := by
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hs
  refine ⟨∑ i, c i • aG (g i), Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (haG _ (g i).2), ∑ i, c i • bG (g i), Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (hbG _ (g i).2), ?_, ?_, ?_⟩
  · simp only [map_sum, map_smul, haGg _ (g _).2]
  · simp only [map_sum, map_smul, hbGg _ (g _).2, smul_neg, Finset.sum_neg_distrib]
  · rw [← Finset.sum_add_distrib]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [← smul_add]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g i, (g i).2, rfl⟩)

/-- The degree-`k + 1` case of `HFin.union`. -/
private lemma HFin.union_succ {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V) (h₁ : HFin U)
    (h₂ : HFin V) (h₁₂ : HFin (U ∩ V)) (k : ℕ) :
    ∃ F : Set (Chain ℚ Y (k + 1)), F.Finite ∧
      cyc (U ∪ V) (k + 1) ≤ Submodule.span ℚ F ⊔ bnd (U ∪ V) (k + 1) := by
  classical
  obtain ⟨FU, hFU, hUk⟩ := h₁ (k + 1)
  obtain ⟨FV, hFV, hVk⟩ := h₂ (k + 1)
  obtain ⟨F₁₂, hF₁₂, h₁₂k⟩ := h₁₂ k
  set J : Submodule ℚ (Chain ℚ Y k) := cyc (U ∩ V) k ⊓ (inside ℚ (k + 1) U).map (bd ℚ k) ⊓
    (inside ℚ (k + 1) V).map (bd ℚ k)
  obtain ⟨G, hG, hGJ, hJG⟩ := exists_finite_subset_le_span_sup hF₁₂
    ((inf_le_left.trans inf_le_left : J ≤ cyc (U ∩ V) k).trans h₁₂k)
  have hlift : ∀ g ∈ G, ∃ a ∈ inside ℚ (k + 1) U, ∃ b ∈ inside ℚ (k + 1) V,
      bd ℚ k a = g ∧ bd ℚ k b = -g := by
    intro g hg
    obtain ⟨⟨-, a, ha, rfl⟩, b, hb, hbg⟩ := hGJ hg
    exact ⟨a, ha, -b, Submodule.neg_mem _ hb, rfl, by rw [map_neg, hbg]⟩
  choose! aG haG bG hbG haGg hbGg using hlift
  refine ⟨FU ∪ FV ∪ (fun g ↦ aG g + bG g) '' G, (hFU.union hFV).union (hG.image _),
    fun z hz ↦ ?_⟩
  obtain ⟨a, ha, b, hb, D, hD, hab, rfl⟩ := exists_eq_add_add_bd_of_mem_cyc hU hV hz
  have hy : bd ℚ k a ∈ J := by
    refine ⟨⟨bd_mem_cyc ?_, a, ha, rfl⟩, -b, Submodule.neg_mem _ hb, ?_⟩
    · rw [inside_inter]
      refine ⟨bd_mem_inside ha, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hab]
      exact Submodule.neg_mem _ (bd_mem_inside hb)
    · rw [map_neg, eq_neg_of_add_eq_zero_left hab]
  obtain ⟨s, hs, t, ⟨e, he, rfl⟩, hst⟩ := Submodule.mem_sup.1 (hJG hy)
  obtain ⟨A, hA, B, hB, hbA, hbB, hW⟩ := exists_lift_of_mem_span haG hbG haGg hbGg hs
  have ha1 : a - A - e ∈ cyc U (k + 1) := by
    refine ⟨Submodule.sub_mem _ (Submodule.sub_mem _ ha hA)
      (inside_mono _ inter_subset_left he), ?_⟩
    change bd ℚ k _ = 0
    rw [map_sub, map_sub, hbA, ← hst]
    abel
  have hb1 : b - B + e ∈ cyc V (k + 1) := by
    refine ⟨Submodule.add_mem _ (Submodule.sub_mem _ hb hB)
      (inside_mono _ inter_subset_right he), ?_⟩
    change bd ℚ k _ = 0
    rw [map_add, map_sub, hbB, eq_neg_of_add_eq_zero_right hab, ← hst]
    abel
  rw [show a + b + bd ℚ (k + 1) D = (a - A - e) + (b - B + e) + (A + B) + bd ℚ (k + 1) D by
    abel]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
    (Submodule.mem_sup_left (Submodule.span_mono subset_union_right hW)))
    (Submodule.mem_sup_right ⟨_, hD, rfl⟩)
  · exact le_span_sup_of_le (subset_union_left.trans subset_union_left) subset_union_left
      hUk ha1
  · exact le_span_sup_of_le (subset_union_right.trans subset_union_left) subset_union_right
      hVk hb1

/-- **Mayer–Vietoris for finite-dimensionality.** For `U`, `V` open, if `H_*(U)`, `H_*(V)` and
`H_*(U ∩ V)` are finite-dimensional, so is `H_*(U ∪ V)`. -/
private lemma HFin.union {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V) (h₁ : HFin U) (h₂ : HFin V)
    (h₁₂ : HFin (U ∩ V)) : HFin (U ∪ V) := by
  classical
  set 𝒰 : Set (Set Y) := {U, V}
  have h𝒰 : ∀ W ∈ 𝒰, IsOpen W := by
    rintro W (rfl | rfl)
    · exact hU
    · exact hV
  have hsU : ⋃₀ 𝒰 = U ∪ V := by simp [𝒰]
  intro k
  cases k with
  | zero =>
    obtain ⟨FU, hFU, hU0⟩ := h₁ 0
    obtain ⟨FV, hFV, hV0⟩ := h₂ 0
    refine ⟨FU ∪ FV, hFU.union hFV, fun z hz ↦ ?_⟩
    have hz' : z ∈ inside ℚ 0 (⋃₀ 𝒰) := hsU ▸ hz
    obtain ⟨a, ha, b, hb, hsplit⟩ :=
      exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 0 hz')
    rw [smallChainMap_zero] at hsplit
    have hD : smallHomotopy ℚ 𝒰 0 z ∈ inside ℚ 1 (U ∪ V) :=
      smallHomotopy_mem_inside_of_mem 𝒰 hz
    rw [show z = a + b + bd ℚ 0 (smallHomotopy ℚ 𝒰 0 z) by rw [← hsplit]; abel]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.mem_sup_right ⟨_, hD, rfl⟩)
    · exact le_span_sup_of_le subset_union_left subset_union_left hU0 ha
    · exact le_span_sup_of_le subset_union_right subset_union_right hV0 hb
  | succ k => exact HFin.union_succ hU hV h₁ h₂ h₁₂ k

private lemma hFin_empty : HFin (∅ : Set Y) := by
  intro k
  refine ⟨∅, finite_empty, fun c hc ↦ ?_⟩
  have := eq_zero_of_mem_inside_empty (cyc_le_inside _ k hc)
  rw [this]
  exact Submodule.zero_mem _

end HFin

section StarConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {K : Set E}

/-- A boundary in `E` of a chain lying in `val '' A` is a boundary of a chain of `K` lying in
`A`. -/
private lemma mem_bnd_of_bd_eq {A : Set K} {k : ℕ} {c : Chain ℚ K k} {w : Chain ℚ E (k + 1)}
    (hw : w ∈ inside ℚ (k + 1) (Subtype.val '' A))
    (hwc : bd ℚ k w = postcomp ℚ (ContinuousMap.subtypeVal K) k c) : c ∈ bnd A k := by
  obtain ⟨w', hw'⟩ := exists_postcomp_subtypeVal_eq
    (inside_mono _ (Subtype.coe_image_subset K A) hw)
  have hw'A : w' ∈ inside ℚ (k + 1) A := by
    have := mem_inside_preimage_of_postcomp_mem_inside Subtype.val_injective (hw'.symm ▸ hw)
    change w' ∈ inside ℚ (k + 1) (Subtype.val ⁻¹' (Subtype.val '' A)) at this
    rwa [Subtype.val_injective.preimage_image] at this
  refine ⟨w', hw'A, postcomp_injective (f := ContinuousMap.subtypeVal K) Subtype.val_injective k ?_⟩
  rw [postcomp_bd, hw', hwc]

/-- A subset of `K` whose image is star-shaped has the homology of a point. -/
private lemma hFin_of_starConvex {A : Set K} {p : K} (hp : p ∈ A)
    (hA : StarConvex ℝ (p : E) (Subtype.val '' A)) : HFin A := by
  intro k
  cases k with
  | zero =>
    refine ⟨{Finsupp.single (ContinuousMap.const _ p) 1}, finite_singleton _, fun c hc ↦ ?_⟩
    have hc' : c - aug ℚ 0 c • Finsupp.single (ContinuousMap.const _ p) 1 ∈ inside ℚ 0 A :=
      Submodule.sub_mem _ hc (Submodule.smul_mem _ _ (single_const_mem_inside hp 1))
    have hE := postcomp_mem_inside (ContinuousMap.subtypeVal K)
      (mapsTo_image Subtype.val A) hc'
    have haug : aug ℚ 0 (postcomp ℚ (ContinuousMap.subtypeVal K) 0
        (c - aug ℚ 0 c • Finsupp.single (ContinuousMap.const _ p) 1)) = 0 := by
      rw [aug_postcomp, map_sub, map_smul, aug_single, smul_eq_mul, mul_one, sub_self]
    obtain ⟨w, hw, hwc⟩ := exists_bd_eq_of_starConvex_zero hA hE haug
    have hb := mem_bnd_of_bd_eq hw hwc
    rw [show c = aug ℚ 0 c • Finsupp.single (ContinuousMap.const _ p) 1 +
      (c - aug ℚ 0 c • Finsupp.single (ContinuousMap.const _ p) 1) by abel]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
      (Submodule.subset_span rfl))) (Submodule.mem_sup_right hb)
  | succ k =>
    refine ⟨∅, finite_empty, fun c hc ↦ Submodule.mem_sup_right ?_⟩
    obtain ⟨hci, hcb⟩ := hc
    have hcb : bd ℚ k c = 0 := hcb
    have hE := postcomp_mem_inside (ContinuousMap.subtypeVal K)
      (mapsTo_image Subtype.val A) hci
    have hbE : bd ℚ k (postcomp ℚ (ContinuousMap.subtypeVal K) (k + 1) c) = 0 := by
      rw [← postcomp_bd, hcb, map_zero]
    obtain ⟨w, hw, hwc⟩ := exists_bd_eq_of_starConvex hA hE hbE
    exact mem_bnd_of_bd_eq hw hwc

/-- A finite open cover of a union all of whose nonempty intersections have star-shaped image
gives finite-dimensional homology. -/
private lemma hFin_biUnion {ι : Type*} [DecidableEq ι] (T : Finset ι) : ∀ (O : ι → Set K),
    (∀ i, IsOpen (O i)) →
    (∀ S ⊆ T, S.Nonempty → (⋂ i ∈ S, O i) = ∅ ∨
      ∃ p ∈ ⋂ i ∈ S, O i, StarConvex ℝ (p : E) (Subtype.val '' ⋂ i ∈ S, O i)) →
    HFin (⋃ i ∈ T, O i) := by
  induction T using Finset.induction_on with
  | empty =>
    intro O _ _
    simpa using (hFin_empty : HFin (∅ : Set K))
  | @insert j T hj IH =>
    intro O hO hgood
    have hU : IsOpen (⋃ i ∈ T, O i) := isOpen_biUnion fun i _ ↦ hO i
    have h₁ : HFin (⋃ i ∈ T, O i) :=
      IH O hO fun S hS hne ↦ hgood S (hS.trans (Finset.subset_insert _ _)) hne
    have h₂ : HFin (O j) := by
      rcases hgood {j} (by simp) (by simp) with h | ⟨p, hp, hpc⟩
      · simp only [Finset.mem_singleton, iInter_iInter_eq_left] at h
        rw [h]; exact hFin_empty
      · simp only [Finset.mem_singleton, iInter_iInter_eq_left] at hp hpc
        exact hFin_of_starConvex hp hpc
    have h₁₂ : HFin ((⋃ i ∈ T, O i) ∩ O j) := by
      have heq : (⋃ i ∈ T, O i) ∩ O j = ⋃ i ∈ T, (O i ∩ O j) := by
        rw [iUnion₂_inter]
      rw [heq]
      refine IH (fun i ↦ O i ∩ O j) (fun i ↦ (hO i).inter (hO j)) fun S hS hne ↦ ?_
      have hI : (⋂ i ∈ S, (O i ∩ O j)) = ⋂ i ∈ insert j S, O i := by
        ext x
        simp only [mem_iInter, mem_inter_iff, Finset.mem_insert, forall_eq_or_imp]
        obtain ⟨i₀, hi₀⟩ := hne
        exact ⟨fun h ↦ ⟨(h i₀ hi₀).2, fun i hi ↦ (h i hi).1⟩,
          fun h i hi ↦ ⟨h.2 i hi, h.1⟩⟩
      rw [hI]
      exact hgood (insert j S) (Finset.insert_subset_insert _ hS) (Finset.insert_nonempty _ _)
    rw [Finset.set_biUnion_insert, union_comm]
    exact HFin.union hU (hO j) h₁ h₂ h₁₂

end StarConvex

section Polyhedron

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

private lemma mem_stdSpace_iff {Δ : Set (Finset ν)} {x : ν → ℝ} :
    x ∈ stdSpace Δ ↔ ∃ s ∈ Δ, (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1 ∧ ∀ v ∉ s, x v = 0 := by
  simp only [stdSpace, mem_iUnion, mem_convexHull_stdVertex_iff, exists_prop]

/-- The intersection of the open stars of the vertices in `S`, if nonempty, is star-shaped
about the barycentre of `S`. -/
private lemma starConvex_openStar {Δ : Set (Finset ν)}
    (hdown : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ) {S : Finset ν} (hS : S.Nonempty)
    {x₀ : ν → ℝ} (hx₀ : x₀ ∈ stdSpace Δ) (hx₀S : ∀ v ∈ S, 0 < x₀ v) :
    ∃ p ∈ {x ∈ stdSpace Δ | ∀ v ∈ S, 0 < x v},
      StarConvex ℝ p {x ∈ stdSpace Δ | ∀ v ∈ S, 0 < x v} := by
  classical
  have hsub : ∀ {x : ν → ℝ} {s : Finset ν}, (∀ v ∉ s, x v = 0) → (∀ v ∈ S, 0 < x v) → S ⊆ s :=
    fun {x s} hxs hxS v hv ↦ by
      by_contra h
      exact (hxS v hv).ne' (hxs v h)
  obtain ⟨s₀, hs₀, -, -, hx₀s⟩ := mem_stdSpace_iff.1 hx₀
  have hSΔ : S ∈ Δ := hdown s₀ hs₀ S (hsub hx₀s hx₀S) hS
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  set p : ν → ℝ := fun v ↦ if v ∈ S then (S.card : ℝ)⁻¹ else 0
  have hp0 : ∀ v, 0 ≤ p v := fun v ↦ by
    simp only [p]; split_ifs <;> positivity
  have hp1 : ∑ v, p v = 1 := by
    simp only [p]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ hcard.ne']
  have hpS : ∀ v ∈ S, 0 < p v := fun v hv ↦ by simp only [p, if_pos hv]; positivity
  have hpoff : ∀ v ∉ S, p v = 0 := fun v hv ↦ by simp only [p, if_neg hv]
  refine ⟨p, ⟨mem_stdSpace_iff.2 ⟨S, hSΔ, hp0, hp1, hpoff⟩, hpS⟩, ?_⟩
  rintro x ⟨hx, hxS⟩ a b ha hb hab
  obtain ⟨s, hs, hx0, hx1, hxs⟩ := mem_stdSpace_iff.1 hx
  have hSs := hsub hxs hxS
  refine ⟨mem_stdSpace_iff.2 ⟨s, hs, fun v ↦ ?_, ?_, fun v hv ↦ ?_⟩, fun v hv ↦ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp0 v)) (mul_nonneg hb (hx0 v))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hx1, mul_one, hab]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxs v hv,
      hpoff v (fun h ↦ hv (hSs h)), mul_zero, add_zero]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      rw [hab, zero_mul, zero_add, one_mul]
      exact hxS v hv
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hpS v hv)) (mul_nonneg hb (hx0 v))

/-- **The polyhedron of a finite simplicial complex has finite-dimensional rational
homology**, by Mayer–Vietoris over the cover by open vertex stars. -/
private lemma hFin_univ_stdSpace {Δ : Set (Finset ν)}
    (hdown : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ) : HFin (univ : Set (stdSpace Δ)) := by
  classical
  set O : ν → Set (stdSpace Δ) := fun v ↦ {x | 0 < (x : ν → ℝ) v}
  have hO : ∀ v, IsOpen (O v) := fun v ↦
    isOpen_lt continuous_const ((continuous_apply v).comp continuous_subtype_val)
  have hcov : (⋃ v ∈ (Finset.univ : Finset ν), O v) = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    obtain ⟨s, -, hx0, hx1, -⟩ := mem_stdSpace_iff.1 x.2
    by_contra h
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion, not_exists, O, mem_setOf_eq,
      not_lt] at h
    have : ∑ v, (x : ν → ℝ) v ≤ 0 := Finset.sum_nonpos fun v _ ↦ h v
    linarith
  rw [← hcov]
  refine hFin_biUnion _ O hO fun S _ hS ↦ ?_
  rcases eq_empty_or_nonempty (⋂ v ∈ S, O v) with h | ⟨x₀, hx₀⟩
  · exact Or.inl h
  · right
    have hI : Subtype.val '' (⋂ v ∈ S, O v) = {x ∈ stdSpace Δ | ∀ v ∈ S, 0 < x v} := by
      ext x
      simp only [mem_image, mem_iInter, O, mem_setOf_eq]
      exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ ⟨y.2, hy⟩, fun ⟨hx, hxS⟩ ↦ ⟨⟨x, hx⟩, hxS, rfl⟩⟩
    have hx₀S : ∀ v ∈ S, 0 < (x₀ : ν → ℝ) v := by
      simpa only [mem_iInter, O, mem_setOf_eq] using hx₀
    obtain ⟨p, ⟨hpK, hpS⟩, hpc⟩ := starConvex_openStar hdown hS x₀.2 hx₀S
    refine ⟨⟨p, hpK⟩, ?_, ?_⟩
    · simpa only [mem_iInter, O, mem_setOf_eq] using hpS
    · rwa [hI]

end Polyhedron

section BorelMoore

open CategoryTheory borelMooreHomology

variable (X : TopCat.{0})

private lemma bijective_ofFinsupp [CompactSpace X] (n : ℕ) :
    Function.Bijective (ofFinsupp (R := ℚ) (X := X) (n := n)) := by
  refine ⟨fun f g h ↦ ?_, fun c ↦ ?_⟩
  · ext τ
    have := congrFun (congrArg Subtype.val h) ((SingularCochain.simplexEquiv X _).symm τ)
    simpa [ofFinsupp_apply] using this
  · have hc : (Function.support c.1).Finite := by
      refine (c.2.finite_inter_compact isCompact_univ).subset fun σ hσ ↦ ⟨hσ, ?_⟩
      obtain ⟨x, hx⟩ := nonempty_singularSimplexImage σ
      exact ⟨x, hx, trivial⟩
    exact ⟨toFinsupp c hc, ofFinsupp_toFinsupp c hc⟩

/-- `ofFinsupp` as a linear map. -/
private def ofFinsuppₗ (n : ℕ) :
    Chain ℚ X n →ₗ[ℚ] (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) X).X n where
  toFun := ofFinsupp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma finite_homology_sc' [CompactSpace X] (h : HFin (univ : Set X)) (n k : ℕ)
    (hk : ∀ c : Chain ℚ X n, c ∈ cyc univ n ↔
      ((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) X).d n k).hom (ofFinsupp c) = 0) :
    Module.Finite ℚ ((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) X).sc' (n + 1) n k).homology := by
  set C := borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) X
  set S := C.sc' (n + 1) n k
  suffices h' : Module.Finite ℚ (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) by
    haveI : Module.Finite ℚ S.moduleCatLeftHomologyData.H := h'
    exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv
  obtain ⟨F₀, hF₀, hle₀⟩ := h n
  obtain ⟨F, hF, hFc, hle⟩ := exists_finite_subset_le_span_sup hF₀ hle₀
  have hcyc : ∀ c ∈ cyc (univ : Set X) n, ofFinsuppₗ X n c ∈ LinearMap.ker S.g.hom :=
    fun c hc ↦ (hk c).1 hc
  let Φ : cyc (univ : Set X) n →ₗ[ℚ]
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    (LinearMap.range S.moduleCatToCycles).mkQ ∘ₗ
      ((ofFinsuppₗ X n).restrict (p := cyc univ n) (q := LinearMap.ker S.g.hom) hcyc)
  have hΦsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨c, rfl⟩ := (bijective_ofFinsupp X n).2 x
    exact ⟨⟨c, (hk c).2 hx⟩, rfl⟩
  have hΦb : ∀ c (hc : c ∈ cyc (univ : Set X) n), c ∈ bnd (univ : Set X) n → Φ ⟨c, hc⟩ = 0 := by
    rintro _ hc ⟨e, -, rfl⟩
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨ofFinsupp e, Subtype.ext ?_⟩
    exact d_ofFinsupp e
  have hFle : Submodule.span ℚ F ≤ cyc univ n := Submodule.span_le.2 hFc
  have hsurj : Function.Surjective (Φ ∘ₗ Submodule.inclusion hFle) := by
    intro q
    obtain ⟨⟨c, hc⟩, rfl⟩ := hΦsurj q
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hle hc)
    refine ⟨⟨a, ha⟩, ?_⟩
    have hb' : b ∈ cyc (univ : Set X) n := bnd_le_cyc _ _ hb
    have : (⟨a + b, hc⟩ : cyc (univ : Set X) n) = ⟨a, hFle ha⟩ + ⟨b, hb'⟩ := rfl
    rw [this, map_add, hΦb b hb' hb, add_zero]
    rfl
  haveI : Module.Finite ℚ (Submodule.span ℚ F) := FiniteDimensional.span_of_finite ℚ hF
  exact Module.Finite.of_surjective _ hsurj

/-- **Rational Borel–Moore homology of a compact space with finite-dimensional finite-chain
homology is finite-dimensional.** -/
private lemma finite_borelMooreHomology [CompactSpace X] (h : HFin (univ : Set X)) (n : ℕ) :
    Module.Finite ℚ (MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) X n) := by
  set C := borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) X
  suffices Module.Finite ℚ (C.homology n) from
    Module.Finite.equiv (borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) X n).symm.toLinearEquiv
  cases n with
  | zero =>
    haveI := finite_homology_sc' X h 0 0 fun c ↦ by
      rw [C.shape 0 0 (by simp)]
      exact ⟨fun _ ↦ rfl, fun _ ↦ mem_inside_univ c⟩
    exact Module.Finite.equiv (C.homologyIsoSc' 1 0 0 (by simp) (by simp)).symm.toLinearEquiv
  | succ m =>
    haveI := finite_homology_sc' X h (m + 1) m fun c ↦ by
      rw [d_ofFinsupp]
      constructor
      · rintro ⟨-, hc⟩
        rw [show bd ℚ m c = 0 from hc]
        rfl
      · intro hc
        refine ⟨mem_inside_univ c, ?_⟩
        change bd ℚ m c = 0
        exact (bijective_ofFinsupp X m).1 (hc.trans rfl)
    exact Module.Finite.equiv
      (C.homologyIsoSc' (m + 2) (m + 1) m (by simp) (by simp)).symm.toLinearEquiv

end BorelMoore

end Homology

section Polyhedral

open MMP MvPolynomial Set ComplexConjugate AlgebraicGeometry CategoryTheory

/-- The real coordinates of an `(n + 1) × (n + 1)` complex matrix. -/
private abbrev MatIdx (n : ℕ) : Type := (Fin (n + 1) × Fin (n + 1)) × Fin 2

/-- The real coordinates of a complex matrix. -/
private def matReal {ι : Type*} (M : ι → ι → ℂ) : (ι × ι) × Fin 2 → ℝ :=
  complexToReal fun ij ↦ M ij.1 ij.2

private lemma matReal_injective {ι : Type*} : Function.Injective (matReal (ι := ι)) := by
  intro M M' h
  have := congrArg realToComplex h
  simp only [matReal, realToComplex_complexToReal] at this
  funext i j
  exact congrFun this (i, j)

private lemma continuous_matReal {ι : Type*} : Continuous (matReal (ι := ι)) := by
  refine continuous_pi fun ⟨⟨i, j⟩, e⟩ ↦ ?_
  simp only [matReal, complexToReal]
  split_ifs
  · exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))
  · exact Complex.continuous_im.comp ((continuous_apply j).comp (continuous_apply i))

/-- The real coordinates of the projection onto the line of `u`, scaled by `∑ |u l|²`. -/
private lemma matReal_lineProjection_mul_sum_normSq {n : ℕ} (u : Fin (n + 1) → ℂ)
    (e : MatIdx n) (hu0 : u ≠ 0) :
    matReal (MMP.Topology.lineProjection u) e * (∑ l, Complex.normSq (u l)) =
      if e.2 = 0 then (u e.1.1).re * (u e.1.2).re + (u e.1.1).im * (u e.1.2).im
      else (u e.1.1).im * (u e.1.2).re - (u e.1.1).re * (u e.1.2).im := by
  obtain ⟨⟨j, k⟩, e⟩ := e
  have hs := MMP.Topology.sum_mul_conj_ne_zero hu0
  rw [MMP.Topology.sum_mul_conj_eq_ofReal, Complex.ofReal_ne_zero] at hs
  simp only [matReal, complexToReal, MMP.Topology.lineProjection,
    MMP.Topology.sum_mul_conj_eq_ofReal]
  split_ifs with he
  · rw [Complex.div_ofReal_re, div_mul_cancel₀ _ hs, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring
  · rw [Complex.div_ofReal_im, div_mul_cancel₀ _ hs, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring

/-- The image of a complex algebraic set under `v ↦ lineProjection (q v)`, `q` polynomial and
nonvanishing on it, is semialgebraic in real coordinates. -/
private lemma isSemialgebraic_image_lineProjection {m n r : ℕ} (f : Fin r → MvPolynomial (Fin m) ℂ)
    (q : Fin (n + 1) → MvPolynomial (Fin m) ℂ)
    (hq : ∀ v : Fin m → ℂ, (∀ j, eval v (f j) = 0) → (fun l ↦ eval v (q l)) ≠ 0) :
    IsSemialgebraic ((fun v ↦ matReal (MMP.Topology.lineProjection fun l ↦ eval v (q l))) ''
      {v | ∀ j, eval v (f j) = 0}) := by
  classical
  obtain ⟨g, hg⟩ := exists_complexZeroLocus_eq f
  choose a b hab using fun l ↦ exists_eval_eq_re_add_im (q l)
  let A : Fin (n + 1) → MvPolynomial (MatIdx n ⊕ (Fin m × Fin 2)) ℝ := fun l ↦ rename Sum.inr (a l)
  let B : Fin (n + 1) → MvPolynomial (MatIdx n ⊕ (Fin m × Fin 2)) ℝ := fun l ↦ rename Sum.inr (b l)
  let N : MvPolynomial (MatIdx n ⊕ (Fin m × Fin 2)) ℝ := ∑ l, (A l * A l + B l * B l)
  let E : MatIdx n → MvPolynomial (MatIdx n ⊕ (Fin m × Fin 2)) ℝ := fun e ↦ X (Sum.inl e) * N -
    if e.2 = 0 then A e.1.1 * A e.1.2 + B e.1.1 * B e.1.2
    else B e.1.1 * A e.1.2 - A e.1.1 * B e.1.2
  let G : Set (MatIdx n ⊕ (Fin m × Fin 2) → ℝ) := {z | ∀ j, eval z (rename Sum.inr (g j)) = 0} ∩
    {z | ∀ e, eval z (E e) = 0}
  have hG : IsSemialgebraic G :=
    (isSemialgebraic_zeroLocus _).inter (isSemialgebraic_zeroLocus _)
  convert IsSemialgebraic.exists_sumElim hG using 1
  have hu : ∀ (y : Fin m × Fin 2 → ℝ) (l : Fin (n + 1)), eval (realToComplex y) (q l) =
      ⟨eval y (a l), eval y (b l)⟩ := fun y l ↦ by
    rw [hab l, complexToReal_realToComplex]
  have hev : ∀ (x : MatIdx n → ℝ) (y : Fin m × Fin 2 → ℝ) (p : MvPolynomial (Fin m × Fin 2) ℝ),
      eval (Sum.elim x y) (rename Sum.inr p) = eval y p := fun x y p ↦ by
    rw [eval_rename]; rfl
  have hN : ∀ (x : MatIdx n → ℝ) (y : Fin m × Fin 2 → ℝ), eval (Sum.elim x y) N =
      ∑ l, Complex.normSq (eval (realToComplex y) (q l)) := fun x y ↦ by
    simp only [N, A, B, map_sum, map_add, map_mul, hev, hu, Complex.normSq_apply]
  have hNpos : ∀ (x : MatIdx n → ℝ) (y : Fin m × Fin 2 → ℝ),
      (fun l ↦ eval (realToComplex y) (q l)) ≠ 0 →
      0 < eval (Sum.elim x y) N := fun x y hy ↦ by
    rw [hN]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    exact Finset.sum_pos' (fun k _ ↦ Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have hE : ∀ (x : MatIdx n → ℝ) (y : Fin m × Fin 2 → ℝ) (e : MatIdx n), eval (Sum.elim x y) (E e) =
      x e * eval (Sum.elim x y) N -
        if e.2 = 0 then
          (eval (realToComplex y) (q e.1.1)).re * (eval (realToComplex y) (q e.1.2)).re +
          (eval (realToComplex y) (q e.1.1)).im * (eval (realToComplex y) (q e.1.2)).im
        else (eval (realToComplex y) (q e.1.1)).im * (eval (realToComplex y) (q e.1.2)).re -
          (eval (realToComplex y) (q e.1.1)).re * (eval (realToComplex y) (q e.1.2)).im := by
    intro x y e
    simp only [E, map_sub, map_mul, eval_X, Sum.elim_inl]
    split_ifs <;> simp [A, B, hev, hu]
  ext x
  simp only [mem_image, mem_setOf_eq, G, mem_inter_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨complexToReal v, fun j ↦ ?_, fun e ↦ ?_⟩
    · rw [hev]
      have : complexToReal v ∈ realToComplex ⁻¹' {z : Fin m → ℂ | ∀ j, eval z (f j) = 0} := by
        simpa using hv
      rw [hg] at this
      exact this j
    · rw [hE, hN, realToComplex_complexToReal,
        matReal_lineProjection_mul_sum_normSq _ _ (hq v hv), sub_self]
  · rintro ⟨y, hy₁, hy₂⟩
    have hv : ∀ j, eval (realToComplex y) (f j) = 0 := by
      have : y ∈ {x | ∀ j, eval x (g j) = 0} := fun j ↦ by simpa [hev] using hy₁ j
      rwa [← hg] at this
    refine ⟨realToComplex y, hv, funext fun e ↦ ?_⟩
    have hpos := hNpos x y (hq _ hv)
    have h1 := hE x y e
    rw [hy₂ e, hN] at h1
    rw [hN] at hpos
    have h2 := matReal_lineProjection_mul_sum_normSq _ e (hq _ hv)
    refine mul_right_cancel₀ hpos.ne' ?_
    rw [h2]
    linarith

/-- On an affine open `U` of a scheme of finite type over `ℂ`, the values at the points of
`U(ℂ)` of finitely many sections over `U` form the image of a complex algebraic set under a
polynomial map. -/
private lemma exists_image_zeroLocus_eq_eval (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (U : X.Opens) (hU : IsAffineOpen U) {n : ℕ}
    (c : Fin n → Γ(X, U)) :
    ∃ (m r : ℕ) (f : Fin r → MvPolynomial (Fin m) ℂ) (q : Fin n → MvPolynomial (Fin m) ℂ),
      (fun v l ↦ eval v (q l)) '' {v | ∀ j, eval v (f j) = 0} =
        {w | ∃ (p : UnderlyingSpace ℂ X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U),
          (fun l ↦ UnderlyingSpace.eval p hp (c l)) = w} := by
  letI : U.toScheme.Over (Spec (.of ℂ)) := ⟨U.ι ≫ X ↘ Spec (.of ℂ)⟩
  haveI : U.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsAffine U := hU
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  letI : Algebra ℂ Γ(U.toScheme, ⊤) := (UnderlyingSpace.structureRingHom ℂ U.toScheme).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(U.toScheme, ⊤) := UnderlyingSpace.finiteType_structureRingHom
  haveI : Algebra.FinitePresentation ℂ Γ(U.toScheme, ⊤) :=
    Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation ℂ Γ(U.toScheme, ⊤)
  let d : Fin n → Γ(U.toScheme, ⊤) := fun l ↦ U.ι.appLE U ⊤ U.ι_preimage_self.ge (c l)
  choose q hq using fun l ↦ P.aeval_val_surjective (d l)
  refine ⟨_, _, P.relation, q, ?_⟩
  have hval : ∀ (p' : UnderlyingSpace ℂ U.toScheme)
      (hp : ⊤ ≤ (UnderlyingSpace.mapFun U.ι p').toHom ⁻¹ᵁ U)
      (l : Fin n), UnderlyingSpace.eval (UnderlyingSpace.mapFun U.ι p') hp (c l) =
        eval (UnderlyingSpace.evalFamily P.val p') (q l) := fun p' hp l ↦ by
    refine (UnderlyingSpace.eval_mapFun_ι U p' hp (c l)).trans ?_
    rw [← UnderlyingSpace.evalTop_aeval rfl, hq l]
    rfl
  rw [← UnderlyingSpace.range_evalFamily_val rfl P]
  ext w
  constructor
  · rintro ⟨_, ⟨p', rfl⟩, rfl⟩
    have hp : ⊤ ≤ (UnderlyingSpace.mapFun U.ι p').toHom ⁻¹ᵁ U := by
      rw [UnderlyingSpace.toHom_mapFun, Scheme.Hom.comp_preimage, U.ι_preimage_self,
        Scheme.Hom.preimage_top]
    exact ⟨_, hp, funext fun l ↦ hval p' hp l⟩
  · rintro ⟨p, hp, rfl⟩
    have : p ∈ Set.range (UnderlyingSpace.mapFun (K := ℂ) U.ι) := by
      rw [UnderlyingSpace.range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
      exact hp
    obtain ⟨p', rfl⟩ := this
    exact ⟨_, ⟨p', rfl⟩, funext fun l ↦ (hval p' hp l).symm⟩

/-- The polyhedron of a finite simplicial complex is compact. -/
private lemma compactSpace_stdSpace {ν : Type*} [Fintype ν] [DecidableEq ν]
    (Δ : Set (Finset ν)) : CompactSpace (stdSpace Δ) := by
  refine isCompact_iff_compactSpace.1 ?_
  unfold stdSpace
  exact (Set.toFinite Δ).isCompact_biUnion fun s _ ↦
    (Finset.finite_toSet (s.map (stdVertex ν))).isCompact_convexHull (𝕜 := ℝ)

section Projective

variable (V : Scheme.{0}) [V.Over (Spec (.of ℂ))] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))]
  {N : ℕ} [(AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)).Over (Spec (.of ℂ))]
  (hP : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)) ↘ Spec (.of ℂ) = Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ N)
  (ι : V ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)) [ι.IsOver (Spec (.of ℂ))] [IsClosedImmersion ι]

/-- The points of `V`, embedded through `V → ℙᴺ` into the real coordinates of the matrices of
orthogonal projections onto the lines of `ℂᴺ⁺¹`. -/
private def projEmb (p : UnderlyingSpace ℂ V) : (Fin (N + 1) × Fin (N + 1)) × Fin 2 → ℝ :=
  matReal (MMP.Topology.toLineProjection (UnderlyingSpace.mapFun ι p))

private lemma continuous_projEmb : Continuous (projEmb V ι) :=
  continuous_matReal.comp (MMP.Topology.continuous_toLineProjection.comp
    (UnderlyingSpace.continuous_mapFun ι))

include hP in
private lemma injective_projEmb : Function.Injective (projEmb V ι) :=
  matReal_injective.comp ((MMP.Topology.injective_toLineProjection
    hP).comp
    (UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion ι).injective)

/-- The points of `V` lying over the `i`-th standard chart of `ℙᴺ` have semialgebraic image. -/
private lemma isSemialgebraic_projEmb_chart (i : Fin (N + 1)) :
    IsSemialgebraic {x | ∃ (p : UnderlyingSpace ℂ V)
      (_ : ⊤ ≤ (UnderlyingSpace.mapFun ι p).toHom ⁻¹ᵁ
        UnderlyingSpace.projectiveSpaceStdChart ℂ N i), projEmb V ι p = x} := by
  classical
  set Ui := UnderlyingSpace.projectiveSpaceStdChart ℂ N i
  have hW : IsAffineOpen (ι ⁻¹ᵁ Ui) :=
    (show IsAffineOpen Ui from MMP.Topology.isAffine_projectiveSpaceStdChart i).preimage ι
  set c : Fin (N + 1) → Γ(V, ι ⁻¹ᵁ Ui) :=
    fun l ↦ ι.app Ui (UnderlyingSpace.projectiveSpaceStdCoord ℂ N i l)
  obtain ⟨m, r, f, q, himg⟩ := exists_image_zeroLocus_eq_eval V (ι ⁻¹ᵁ Ui) hW c
  have hc : ∀ (p : UnderlyingSpace ℂ V)
      (hp : ⊤ ≤ (UnderlyingSpace.mapFun ι p).toHom ⁻¹ᵁ Ui) (l : Fin (N + 1)),
      UnderlyingSpace.eval (U := ι ⁻¹ᵁ Ui) p hp (c l) =
        UnderlyingSpace.eval (UnderlyingSpace.mapFun ι p) hp
          (UnderlyingSpace.projectiveSpaceStdCoord ℂ N i l) := fun p hp l ↦
    (UnderlyingSpace.eval_mapFun ι p hp _).symm
  have hF : ∀ (p : UnderlyingSpace ℂ V)
      (hp : ⊤ ≤ (UnderlyingSpace.mapFun ι p).toHom ⁻¹ᵁ Ui),
      projEmb V ι p = matReal (MMP.Topology.lineProjection
        fun l ↦ UnderlyingSpace.eval (U := ι ⁻¹ᵁ Ui) p hp (c l)) := fun p hp ↦ by
    rw [projEmb, MMP.Topology.toLineProjection_eq hp]
    simp only [hc]
  have hne : ∀ v : Fin m → ℂ, (∀ j, eval v (f j) = 0) → (fun l ↦ eval v (q l)) ≠ 0 :=
    fun v hv ↦ by
    obtain ⟨p, hp, hpv⟩ := (Set.ext_iff.1 himg _).1 ⟨v, hv, rfl⟩
    have hpv' : (fun l ↦ eval v (q l)) =
        fun l ↦ UnderlyingSpace.eval (U := ι ⁻¹ᵁ Ui) p hp (c l) :=
      hpv.symm
    rw [hpv']
    intro h
    apply MMP.Topology.projectiveSpaceStdCoord_vector_ne_zero (p := UnderlyingSpace.mapFun ι p)
      (i := i) hp
    funext l
    rw [← hc p hp l]
    exact congrFun h l
  convert isSemialgebraic_image_lineProjection f q hne using 1
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨v, hv, hvp⟩ := (Set.ext_iff.1 himg _).2 ⟨p, hp, rfl⟩
    exact ⟨v, hv, by rw [hF p hp, ← hvp]⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨p, hp, hpv⟩ := (Set.ext_iff.1 himg _).1 ⟨v, hv, rfl⟩
    exact ⟨p, hp, by rw [hF p hp, hpv]⟩

private lemma isSemialgebraic_range_projEmb : IsSemialgebraic (Set.range (projEmb V ι)) := by
  have : Set.range (projEmb V ι) = ⋃ i, {x | ∃ (p : UnderlyingSpace ℂ V)
      (_ : ⊤ ≤ (UnderlyingSpace.mapFun ι p).toHom ⁻¹ᵁ
        UnderlyingSpace.projectiveSpaceStdChart ℂ N i), projEmb V ι p = x} := by
    ext x
    simp only [mem_range, mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨i, hi⟩ := MMP.Topology.exists_top_le_preimage_projectiveSpaceStdChart
        (UnderlyingSpace.mapFun ι p)
      exact ⟨i, p, hi, rfl⟩
    · rintro ⟨i, p, -, rfl⟩
      exact ⟨p, rfl⟩
  rw [this]
  exact IsSemialgebraic.iUnion (isSemialgebraic_projEmb_chart V ι)

include hP ι in
/-- **The complex points of a projective scheme form a finite polyhedron.** -/
private theorem exists_homeomorph_stdSpace :
    ∃ (ν : Type) (_ : Fintype ν) (_ : DecidableEq ν) (Δ : Set (Finset ν)),
      (∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ) ∧
        Nonempty (stdSpace Δ ≃ₜ UnderlyingSpace ℂ V) := by
  haveI := UnderlyingSpace.compactSpace_projectiveSpace (K := ℂ) N
    hP
  haveI : CompactSpace (UnderlyingSpace ℂ V) :=
    (UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion ι).compactSpace
  set S := Set.range (projEmb V ι)
  have hSc : IsCompact S := isCompact_range (continuous_projEmb V ι)
  obtain ⟨ν, _, _, Δ, h, hT, -⟩ := stdTriangulable _ S PEmpty PEmpty.elim hSc
    (isSemialgebraic_range_projEmb V ι) (fun j ↦ j.elim) (fun j ↦ j.elim)
  refine ⟨ν, inferInstance, inferInstance, Δ, hT.down_closed, ⟨?_⟩⟩
  have e₁ : UnderlyingSpace ℂ V ≃ₜ S :=
    ((continuous_projEmb V ι).isClosedEmbedding (injective_projEmb V hP ι)).isEmbedding.toHomeomorph
  haveI : CompactSpace (stdSpace Δ) := compactSpace_stdSpace Δ
  have hcont : Continuous ((stdSpace Δ).restrict h) := hT.continuousOn.restrict
  have hinj : Function.Injective ((stdSpace Δ).restrict h) := fun x y hxy ↦
    Subtype.ext (hT.injOn x.2 y.2 hxy)
  have hrange : Set.range ((stdSpace Δ).restrict h) = S :=
    (Set.range_restrict h _).trans hT.image_eq
  have e₂ : stdSpace Δ ≃ₜ S :=
    (hcont.isClosedEmbedding hinj).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  exact e₂.trans e₁.symm

end Projective

end Polyhedral

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MMP MMP.UnderlyingSpace

/-- Rational Borel–Moore homology of a space homeomorphic to a finite polyhedron is
finite-dimensional. -/
private lemma finite_borelMooreHomology_of_homeomorph {ν : Type} [Fintype ν] [DecidableEq ν]
    {Δ : Set (Finset ν)} (hdown : ∀ s ∈ Δ, ∀ t ⊆ s, t.Nonempty → t ∈ Δ) {Y : Type}
    [TopologicalSpace Y] (e : stdSpace Δ ≃ₜ Y) (n : ℕ) :
    Module.Finite ℚ
      (MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of Y) n) := by
  haveI : CompactSpace (stdSpace Δ) := compactSpace_stdSpace Δ
  haveI : Module.Finite ℚ
      (MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (stdSpace Δ)) n) :=
    finite_borelMooreHomology (TopCat.of (stdSpace Δ)) (hFin_univ_stdSpace hdown) n
  have hsurj : Function.Surjective (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (e.symm.symm : C(stdSpace Δ, Y))) e.symm.symm.isProperMap (n : ℤ)).hom :=
    fun y ↦ ⟨_, borelMooreHomology.pushforward_symm_pushforward_homeomorph ℚ _ e.symm _ y⟩
  exact Module.Finite.of_surjective _ hsurj

/-- The cycle span of a projective complex variety is finite-dimensional. -/
public lemma finiteDimensional_cycleSpan (V : Scheme.{0}) [V.Over (Spec (.of ℂ))]
    [MMP.IsComplexScheme V]
    (hV : MMP.Mori.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))) (r : ℕ) :
    FiniteDimensional ℚ (cycleSpan V r) := by
  haveI : LocallyOfFiniteType (V ↘ Spec (.of ℂ)) := hV.toIsVariety.toLocallyOfFiniteType
  obtain ⟨N, i', hi', hcomm⟩ := hV.isProjective
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)).Over (Spec (.of ℂ)) :=
    ⟨Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ N⟩
  let ι : V ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) :=
    i' ≫ (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison ℂ N).iso.hom
  haveI : IsClosedImmersion ι := inferInstance
  haveI : ι.IsOver (Spec (.of ℂ)) := ⟨by
    change (i' ≫ _) ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ N = _
    rw [Category.assoc,
      Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff, ← hcomm]
    rfl⟩
  obtain ⟨ν, _, _, Δ, hdown, ⟨e⟩⟩ := exists_homeomorph_stdSpace V rfl ι
  haveI : Module.Finite ℚ (borelMooreHomology (V ↘ Spec (.of ℂ)) (2 * r)) :=
    finite_borelMooreHomology_of_homeomorph hdown
      (e.trans ComplexPoints.homeomorphUnderlyingSpace.symm) (2 * r)
  infer_instance

/-- A linear map lowers the rank of a finite-dimensional subspace containing a nonzero vector
of its kernel. -/
private lemma finrank_map_lt_of_mem_ker {K M N : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K N] (L : M →ₗ[K] N) (S : Submodule K M)
    (hS : FiniteDimensional K S) {x : M} (hx : x ∈ S) (hx0 : x ≠ 0) (hLx : L x = 0) :
    Module.finrank K (S.map L) < Module.finrank K S :=
  lt_of_le_of_ne (Submodule.finrank_map_le L S) fun h ↦
    hx0 (Submodule.disjoint_def.1 (Submodule.disjoint_ker_of_finrank_le L h.ge) x hx hLx)

/-- The generic point of an `r`-dimensional irreducible component of a closed subset `A ⊆ V`
is a point of `A` of delta-dimension `r`. -/
private lemma exists_point_of_mem_irreducibleComponents {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] {A : Set V}
    (hA : IsClosed A) {r : ℕ} {Z : Set A} (hZ : Z ∈ irreducibleComponents A)
    (hZdim : topologicalKrullDim Z = r) :
    ∃ y : V, Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (V ↘ Spec (.of ℂ)) y = r ∧ y ∈ A := by
  have hZc : IsClosed (Subtype.val '' Z : Set V) :=
    hA.isClosedMap_subtype_val _ (isClosed_of_mem_irreducibleComponents Z hZ)
  have hirr : IsIrreducible (Subtype.val '' Z : Set V) :=
    hZ.1.image _ continuous_subtype_val.continuousOn
  have hcl : closure ({hirr.genericPoint} : Set V) = Subtype.val '' Z := by
    rw [hirr.isGenericPoint_genericPoint_closure.def, hZc.closure_eq]
  have hemb : Topology.IsEmbedding (fun z : Z ↦ (z : A).1) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have h2 : Set.range (fun z : Z ↦ (z : A).1) = (Subtype.val '' Z : Set V) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  refine ⟨hirr.genericPoint, (relativeDimension_eq_natCast_iff _ r).2 ?_, ?_⟩
  · rw [hcl, ← h2, ← hemb.toHomeomorph.isHomeomorph.topologicalKrullDim_eq, hZdim]
  · have hmem : hirr.genericPoint ∈ closure ({hirr.genericPoint} : Set V) :=
      subset_closure rfl
    rw [hcl] at hmem
    obtain ⟨a, -, ha⟩ := hmem
    exact ha ▸ a.2

/-- A class on `V(ℂ)` vanishing on `V(ℂ) ∖ A` is killed by the restriction
`H^BM(V(ℂ)) → H^BM(U(ℂ))` of `MMP.Analytic.map_restrict_cycleSpan_compl`, for `U = V ∖ A`. -/
private lemma restrict_comp_eq_zero_of_restrict_compl_eq_zero {V : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [MMP.IsComplexScheme V] {A : Set V} (hA : IsClosed A)
    (U : V.Opens) (hU : (U : Set V) = Aᶜ)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] (n : ℤ)
    [T2Space (ComplexPoints (V ↘ Spec (.of ℂ)))]
    {x : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints (V ↘ Spec (.of ℂ)))) n}
    (hx : (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
      (Y := TopCat.of (ComplexPoints (V ↘ Spec (.of ℂ))))
      ⟨{x | x.toScheme ∈ Aᶜ}, ComplexPoints.isOpen_setOf_toScheme_mem hA.isOpen_compl⟩
      n).hom x = 0) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_,
            (ComplexPoints.homeomorphUnderlyingSpace (X := V)).continuous⟩)
          (ComplexPoints.homeomorphUnderlyingSpace (X := V)).isProperMap n ≫
        borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
          (Y := TopCat.of (UnderlyingSpace ℂ V)) (opensRangeMap U.ι) n ≫
        borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_, (homeomorphOpensRangeMap U.ι).symm.continuous⟩)
          (homeomorphOpensRangeMap U.ι).symm.isProperMap n ≫
        borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_,
            (ComplexPoints.homeomorphUnderlyingSpace
              (X := U.toScheme)).symm.continuous⟩)
          (ComplexPoints.homeomorphUnderlyingSpace (X := U.toScheme)).symm.isProperMap
          n).hom x = 0 := by
  have hcomap : Opens.comap (TopCat.ofHom ⟨_,
      (ComplexPoints.homeomorphUnderlyingSpace (X := V)).continuous⟩).hom
        (opensRangeMap U.ι) =
      ⟨{x | x.toScheme ∈ Aᶜ},
        ComplexPoints.isOpen_setOf_toScheme_mem hA.isOpen_compl⟩ := by
    ext x
    change ComplexPoints.homeomorphUnderlyingSpace x ∈ opensRangeMap U.ι ↔
      x.toScheme ∈ Aᶜ
    rw [mem_opensRangeMap_ι_iff, ← hU, ComplexPoints.homeomorphUnderlyingSpace_apply,
      Subsingleton.elim (IsLocalRing.closedPoint ℂ) default]
    exact (congrArg (· ∈ U) (congrArg x.hom (Subsingleton.elim _ _))).to_iff
  simp only [ModuleCat.comp_apply, restrict_pushforward_eq_zero_of_comap_eq _
    (ComplexPoints.homeomorphUnderlyingSpace (X := V)).isProperMap hcomap hx,
    map_zero]

/-- **Removing an `r`-dimensional component lowers the cycle rank.** Let `V` be a projective
complex variety and `A ⊆ V` a closed subset of dimension at most `r` having an irreducible
component of dimension `r`. Then the cycle rank of the open subscheme `U = V ∖ A` in dimension
`r` is strictly smaller than that of `V`: `ρ_r(V ∖ A) < ρ_r(V)`. -/
@[mmp "lem_oai4_cycle_rank_ii"]
public theorem cycleRank_opens_lt_of_mem_irreducibleComponents
    (V : Scheme.{0}) [V.Over (Spec (.of ℂ))] [MMP.IsComplexScheme V]
    (hV : MMP.Mori.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))) {A : Set V} (hA : IsClosed A)
    {r : ℕ} (hdim : topologicalKrullDim A ≤ r)
    {Z : Set A} (hZ : Z ∈ irreducibleComponents A) (hZdim : topologicalKrullDim Z = r)
    (U : V.Opens) (hU : (U : Set V) = Aᶜ)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] :
    cycleRank U.toScheme r < cycleRank V r := by
  haveI : T2Space (ComplexPoints (V ↘ Spec (.of ℂ))) :=
    ComplexPoints.homeomorphUnderlyingSpace.isEmbedding.t2Space
  obtain ⟨y, hy, hyA⟩ := exists_point_of_mem_irreducibleComponents hA hZ hZdim
  have hW := (cycleSpan_inf_ker_restrict_eq_span_fundamentalClass V hV hA hdim).ge
    (Submodule.subset_span ⟨⟨y, hy, hyA⟩, rfl⟩)
  unfold cycleRank
  rw [← map_restrict_cycleSpan_compl V hV.isProjective ⟨A, hA⟩ U hU r]
  exact finrank_map_lt_of_mem_ker _ _ (finiteDimensional_cycleSpan V hV r) hW.1
    (fundamentalClass_ne_zero hV y hy)
    (restrict_comp_eq_zero_of_restrict_compl_eq_zero hA U hU _ hW.2)

/-- Rank–nullity for the restriction of a linear map to a finite-dimensional subspace. -/
private lemma finrank_map_add_finrank_inf_ker {K M N : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (p : Submodule K M)
    [FiniteDimensional K p] :
    Module.finrank K (p.map f) + Module.finrank K ↥(p ⊓ LinearMap.ker f) =
      Module.finrank K p := by
  rw [← LinearMap.finrank_range_add_finrank_ker (f.domRestrict p), LinearMap.range_domRestrict,
    LinearMap.ker_domRestrict, ← (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq,
    Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]

/-- **Cycle rank and removal of a closed subset.** Let `V` be a projective complex variety,
`A ⊆ V` a closed subset of dimension at most `r` and `U = V ∖ A`. Then
`ρ_r(V) = ρ_r(U) + dim_ℚ ⟨[Z] : Z ⊆ A, dim Z = r⟩`. -/
public theorem cycleRank_eq_cycleRank_compl_add_finrank_span
    (V : Scheme.{0}) [V.Over (Spec (.of ℂ))] [MMP.IsComplexScheme V]
    (hV : MMP.Mori.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))) {A : Set V} (hA : IsClosed A)
    {r : ℕ} (hdim : topologicalKrullDim A ≤ r)
    (U : V.Opens) (hU : (U : Set V) = Aᶜ)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] :
    cycleRank V r = cycleRank U.toScheme r +
      Module.finrank ℚ (Submodule.span ℚ (Set.range fun y : {y : V // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (V ↘ Spec (.of ℂ)) y = r ∧ y ∈ A} ↦
          fundamentalClass y.1 y.2.1)) := by
  haveI : T2Space (ComplexPoints (V ↘ Spec (.of ℂ))) :=
    ComplexPoints.homeomorphUnderlyingSpace.isEmbedding.t2Space
  haveI := finiteDimensional_cycleSpan V hV r
  rw [← cycleSpan_inf_ker_restrict_eq_span_fundamentalClass V hV hA hdim]
  have hmap : (cycleSpan V r).map (restrictionMap V U r).hom = cycleSpan U.toScheme r :=
    map_restrict_cycleSpan_compl V hV.isProjective ⟨A, hA⟩ U hU r
  have hker : cycleSpan V r ⊓ LinearMap.ker (restrictionMap V U r).hom =
      cycleSpan V r ⊓ LinearMap.ker (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
        (Y := TopCat.of (ComplexPoints (V ↘ Spec (.of ℂ))))
        ⟨{x | x.toScheme ∈ Aᶜ}, ComplexPoints.isOpen_setOf_toScheme_mem hA.isOpen_compl⟩
        ((2 * r : ℕ) : ℤ)).hom := by
    ext x
    simp only [Submodule.mem_inf, LinearMap.mem_ker]
    exact and_congr_right fun _ ↦ ⟨restrict_compl_eq_zero hA U hU _,
      restrict_comp_eq_zero_of_restrict_compl_eq_zero hA U hU _⟩
  unfold cycleRank
  rw [← finrank_map_add_finrank_inf_ker (restrictionMap V U r).hom, hmap, hker]

end CycleRankDrop

end MMP.Analytic

namespace MMP.Fourfold

/-! ### Strict-transform lifts of a homologically trivial divisor -/

open CategoryTheory AlgebraicGeometry MMP TopologicalSpace
open MMP.Mori
open MMP.UnderlyingSpace MMP.borelMooreHomology
open scoped MMP.SubschemeOver

/-! ### Dimension arithmetic -/

/-- In `WithBot ℕ∞`, `m + a = n` forces `a = n - m`. -/
private lemma eq_natCast_sub_of_natCast_add_eq {m n : ℕ} {a : ℕ∞}
    (h : (m : WithBot ℕ∞) + a = n) :
    a = (n - m : ℕ) := by
  have h' : (m : ℕ∞) + a = n := by exact_mod_cast h
  induction a using ENat.recTopCoe with
  | top => simp at h'
  | coe a =>
    have : m + a = n := by exact_mod_cast h'
    norm_cast
    omega

/-- In `WithBot ℕ∞`, `d + c = n` with `k ≤ c` gives `d ≤ n - k`. -/
private lemma le_natCast_sub_of_add_eq {d : WithBot ℕ∞} {c : ℕ∞} {n k : ℕ} (h : d + c = n)
    (hc : (k : ℕ∞) ≤ c) : d ≤ (n - k : ℕ) := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    have h' : d + c = n := by exact_mod_cast h
    induction d using ENat.recTopCoe with
    | top => simp at h'
    | coe d =>
      induction c using ENat.recTopCoe with
      | top => simp at h'
      | coe c =>
        have : d + c = n := by exact_mod_cast h'
        have : k ≤ c := by exact_mod_cast hc
        have h2 : d ≤ n - k := by omega
        show ((d : ℕ∞) : WithBot ℕ∞) ≤ (((n - k : ℕ) : ℕ∞) : WithBot ℕ∞)
        exact WithBot.coe_le_coe.mpr (Nat.cast_le.mpr h2)

/-- In `WithBot ℕ∞`, `x < n + 1` gives `x ≤ n`. -/
private lemma le_of_lt_natCast_succ {x : WithBot ℕ∞} {n : ℕ} (h : x < (n + 1 : ℕ)) :
    x ≤ n := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe x =>
    induction x using ENat.recTopCoe with
    | top => simp at h
    | coe x =>
      have : x < n + 1 := by exact_mod_cast h
      exact_mod_cast (show x ≤ n by omega)

/-! ### Prime divisors over the biregular locus -/

section Biregular

variable {X Y : Scheme.{0}}

/-- Over the biregular locus, a morphism reflects specialization. -/
private theorem specializes_of_map_specializes {f : X ⟶ Y} {x y : X}
    (hx : f x ∈ biregularLocus f) (hy : f y ∈ biregularLocus f) (h : f x ⤳ f y) : x ⤳ y := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  let p : (f ⁻¹ᵁ biregularLocus f).toScheme := ⟨x, hx⟩
  let q : (f ⁻¹ᵁ biregularLocus f).toScheme := ⟨y, hy⟩
  have hp : ((f ∣_ biregularLocus f) ≫ (biregularLocus f).ι) p = f x := by
    rw [morphismRestrict_ι]
    rfl
  have hq : ((f ∣_ biregularLocus f) ≫ (biregularLocus f).ι) q = f y := by
    rw [morphismRestrict_ι]
    rfl
  have hpq : p ⤳ q := by
    rwa [← ((f ∣_ biregularLocus f) ≫
      (biregularLocus f).ι).isOpenEmbedding.isInducing.specializes_iff, hp, hq]
  exact hpq.map (f ⁻¹ᵁ biregularLocus f).ι.continuous

private theorem mem_support_iff_specializes (D : Mori.PrimeDivisor X) (x : X) :
    x ∈ D.support ↔ D.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, specializes_iff_mem_closure]

/-- If `f` sends `η_P` to `η_Q` and is biregular over `η_Q`, then `P` is the inverse transform
of `Q`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_map_genericPoint {f : X ⟶ Y}
    (P : Mori.PrimeDivisor X) (Q : Mori.PrimeDivisor Y)
    (hPQ : f P.genericPoint = Q.genericPoint) (hV : Q.genericPoint ∈ biregularLocus f) :
    inverseTransformPrimeDivisor f Q = some P := by
  have hset : (inverseTransform f Q.idealSheaf.support : Set X) = P.support := by
    rw [inverseTransform, Closeds.coe_closure]
    refine le_antisymm (closure_minimal ?_ ?_) ?_
    · rintro y ⟨hyQ, hyV⟩
      have h1 : f P.genericPoint ⤳ f y := hPQ ▸ (mem_support_iff_specializes Q _).mp hyQ
      exact (mem_support_iff_specializes P y).mpr
        (specializes_of_map_specializes (hPQ ▸ hV) hyV h1)
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isClosed_closure
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal (Set.singleton_subset_iff.mpr (subset_closure ?_)) isClosed_closure
      refine ⟨?_, ?_⟩
      · change f P.genericPoint ∈ Q.support
        rw [hPQ]
        exact (mem_support_iff_specializes Q _).mpr specializes_rfl
      · change f P.genericPoint ∈ biregularLocus f
        rwa [hPQ]
  refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨⟨Q.genericPoint,
    (mem_support_iff_specializes Q _).mpr specializes_rfl, hV⟩, ?_⟩
  have := P.integral
  rw [inverseTransformIdeal,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme P.idealSheaf _ rfl]
  congr 1
  ext1
  exact hset.symm

end Biregular

/-- Push-forward along a map with a left inverse is injective. -/
private lemma injective_pushforward_of_comp_eq_id {A B : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ A)
    (hf : IsProperMap f) (hg : IsProperMap g) (hgf : f ≫ g = 𝟙 A) (j : ℤ) :
    Function.Injective (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf j).hom := by
  have hb := borelMooreHomology.bijective_pushforward_of_eq_id ℚ (ModuleCat.of ℚ ℚ) (f ≫ g)
    (hg.comp hf) hgf j
  rw [borelMooreHomology.pushforward_comp ℚ (ModuleCat.of ℚ ℚ) f g hf hg j] at hb
  intro a b hab
  exact hb.1 (by rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, hab])

/-! ### Points of delta-dimension two -/

section PointClasses

open Stacks.Chow

/-- In `WithBot ℕ∞`, `d + 1 = 3` forces `d = 2`. -/
private lemma eq_two_of_add_one_eq_three {d : WithBot ℕ∞}
    (h : d + ((1 : ℕ∞) : WithBot ℕ∞) = 3) : d = 2 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    have h' : d + 1 = 3 := by
      rwa [← WithBot.coe_add, WithBot.coe_eq_ofNat] at h
    induction d using ENat.recTopCoe with
    | top => simp at h'
    | coe d =>
      have : d + 1 = 3 := by exact_mod_cast h'
      obtain rfl : d = 2 := by omega
      rfl

/-- On an integral threefold over `ℂ`, the points of delta-dimension `2` are the points of
coheight one, the generic points of the prime divisors. -/
private lemma relativeDimension_eq_two_iff {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (hX : topologicalKrullDim X = 3)
    (x : X) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = 2 ↔
      Order.coheight x = 1 := by
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (X ↘ Spec (.of ℂ)) x
  rw [hX] at h1
  have e := MMP.Analytic.relativeDimension_eq_natCast_iff x 2
  push_cast at e
  rw [e]
  constructor
  · intro h
    rw [h] at h1
    simpa using eq_natCast_sub_of_natCast_add_eq (m := 2) (n := 3) (by exact_mod_cast h1)
  · intro h
    rw [h] at h1
    exact eq_two_of_add_one_eq_three h1

end PointClasses

/-! ### Push-forward along a map which is an isomorphism over an open -/

section IsoOver

/-- A point of `X(ℂ)` whose closed point lies in an open `U` factors through `U`. -/
private theorem exists_lift_of_mem {X : Scheme.{0}} (U : X.Opens) (a : Spec (.of ℂ) ⟶ X)
    (h : a (IsLocalRing.closedPoint ℂ) ∈ U) : ∃ a' : Spec (.of ℂ) ⟶ U, a' ≫ U.ι = a := by
  refine ⟨IsOpenImmersion.lift U.ι a ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι, Subsingleton.elim y (IsLocalRing.closedPoint ℂ)]
  exact h

variable {W S : Scheme.{0}} [W.Over (Spec (.of ℂ))] [S.Over (Spec (.of ℂ))]

/-- A morphism which is an isomorphism over `V` is bijective on `ℂ`-points over `V`. -/
private theorem bijective_restrictPreimage_opensRangeMap (r : W ⟶ S) [r.IsOver (Spec (.of ℂ))]
    (V : S.Opens) [IsIso (r ∣_ V)] :
    Function.Bijective (borelMooreHomology.restrictPreimage
      (TopCat.ofHom (map (K := ℂ) r)) (opensRangeMap V.ι)) := by
  have hmem : ∀ p : UnderlyingSpace ℂ W,
      p ∈ Opens.comap (TopCat.ofHom (map (K := ℂ) r)).hom (opensRangeMap V.ι) ↔
        (p.toHom ≫ r) (IsLocalRing.closedPoint ℂ) ∈ V := fun p ↦ by
    change map (K := ℂ) r p ∈ opensRangeMap V.ι ↔ _
    rw [mem_opensRangeMap_ι_iff, toHom_map]
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : a.toHom ≫ r = b.toHom ≫ r := congrArg (fun z => (Subtype.val z).toHom) hab
    obtain ⟨a', ha'⟩ := exists_lift_of_mem (r ⁻¹ᵁ V) a.toHom ((hmem a).1 ha)
    obtain ⟨b', hb'⟩ := exists_lift_of_mem (r ⁻¹ᵁ V) b.toHom ((hmem b).1 hb)
    have key : a' ≫ (r ∣_ V) ≫ V.ι = b' ≫ (r ∣_ V) ≫ V.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, ha', ← Category.assoc, hb', hab']
    have : a' = b' := by
      rwa [← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono] at key
    apply Subtype.ext
    apply UnderlyingSpace.ext
    rw [← ha', ← hb', this]
  · rintro ⟨q, hq⟩
    have hq' : q.toHom (IsLocalRing.closedPoint ℂ) ∈ V := (mem_opensRangeMap_ι_iff V q).1 hq
    obtain ⟨q', hq''⟩ := exists_lift_of_mem V q.toHom hq'
    let p : Spec (.of ℂ) ⟶ W := q' ≫ inv (r ∣_ V) ≫ (r ⁻¹ᵁ V).ι
    have hpr : p ≫ r = q.toHom := by
      simp only [p, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hq'']
    have hpo : p ≫ W ↘ Spec (.of ℂ) = 𝟙 _ := by
      rw [← comp_over r (Spec (.of ℂ)), ← Category.assoc, hpr, q.toHom_comp_over]
    refine ⟨⟨⟨p, hpo⟩, (hmem _).2 ?_⟩, ?_⟩
    · change (p ≫ r) (IsLocalRing.closedPoint ℂ) ∈ V
      rwa [hpr]
    · exact Subtype.ext (UnderlyingSpace.ext hpr)

/-- If `r` is an isomorphism over `V` and `r_* x = 0`, then `x` restricts to zero on
`r⁻¹(V)(ℂ)`. -/
private theorem restrict_comap_eq_zero_of_pushforward_eq_zero [IsComplexScheme W]
    [IsComplexScheme S] (r : W ⟶ S) [r.IsOver (Spec (.of ℂ))] [IsProper r] (V : S.Opens)
    [IsIso (r ∣_ V)] (k : ℤ)
    (x : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W)) k)
    (hx : (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) r))
      (isProperMap_map (K := ℂ) r) k).hom x = 0) :
    (restrict ℚ (ModuleCat.of ℚ ℚ)
      (Opens.comap (TopCat.ofHom (map (K := ℂ) r)).hom (opensRangeMap V.ι)) k).hom x = 0 := by
  have hp := isProperMap_map (K := ℂ) r
  have h := restrict_pushforward_apply ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (map (K := ℂ) r)) hp (opensRangeMap V.ι) k x
  rw [hx, map_zero] at h
  have hb := bijective_restrictPreimage_opensRangeMap r V
  have hpp := isProperMap_restrictPreimage (TopCat.ofHom (map (K := ℂ) r)) (opensRangeMap V.ι) hp
  have hemb : Topology.IsClosedEmbedding (borelMooreHomology.restrictPreimage
      (TopCat.ofHom (map (K := ℂ) r)) (opensRangeMap V.ι)) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (borelMooreHomology.restrictPreimage _ _).hom.continuous hb.1 hpp.isClosedMap
  let Φ := hemb.isEmbedding.toHomeomorphOfSurjective hb.2
  refine injective_pushforward_of_comp_eq_id _ (TopCat.ofHom ⟨Φ.symm, Φ.symm.continuous⟩) hpp
    Φ.symm.isProperMap (ConcreteCategory.hom_ext _ _ fun a ↦ Φ.symm_apply_apply a) k ?_
  rw [map_zero]
  exact h.symm

end IsoOver

/-- A morphism which is an isomorphism over `U` has residue degree one at the points over `U`. -/
private theorem residueDegree_eq_one_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f ∣_ U)] (x : X) (hx : f x ∈ U) : f.residueDegree x = 1 := by
  obtain ⟨x', rfl⟩ : ∃ x' : (f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).ι x' = x := ⟨⟨x, hx⟩, rfl⟩
  have h1 : IsIso (((f ⁻¹ᵁ U).ι ≫ f).residueFieldMap x') := by
    rw [← morphismRestrict_ι, Scheme.residueFieldMap_comp]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_ <;>
      exact Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion _ _
  rw [Scheme.residueFieldMap_comp] at h1
  have h3 : IsIso ((f ⁻¹ᵁ U).ι.residueFieldMap x') :=
    Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion _ _
  have h2 : IsIso (f.residueFieldMap ((f ⁻¹ᵁ U).ι x')) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (f.residueFieldMap ((f ⁻¹ᵁ U).ι x'))
      ((f ⁻¹ᵁ U).ι.residueFieldMap x') h3 h1
  have hb : Function.Bijective (f.residueFieldMap ((f ⁻¹ᵁ U).ι x')).hom :=
    ConcreteCategory.bijective_of_isIso (f.residueFieldMap ((f ⁻¹ᵁ U).ι x'))
  unfold Scheme.Hom.residueDegree
  letI := (f.residueFieldMap ((f ⁻¹ᵁ U).ι x')).hom.toAlgebra
  let e := AlgEquiv.ofBijective (Algebra.ofId (Y.residueField (f ((f ⁻¹ᵁ U).ι x')))
    (X.residueField ((f ⁻¹ᵁ U).ι x'))) hb
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- **The strict transform pushes forward to the divisor.** If `h : M ⟶ N` is proper, its
biregular locus has complement of codimension at least two, and all prime divisors of `M` and
`N` are surfaces, then `h_*[h⁻¹_* L] = [L]` in `H_4(N, ℚ)`. -/
private theorem pushforward_divisorClass_inverseTransformDivisor {M N : Scheme.{0}}
    [M.Over (Spec (.of ℂ))] [N.Over (Spec (.of ℂ))] [IsComplexScheme M] [IsComplexScheme N]
    (h : M ⟶ N) [h.IsOver (Spec (.of ℂ))] [IsProper h]
    (hcodim : 2 ≤ closedsCodimension (biregularLocus h).compl)
    (hM : ∀ E : Mori.PrimeDivisor M, Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (M ↘ Spec (.of ℂ)) E.genericPoint = 2)
    (hN : ∀ D : Mori.PrimeDivisor N, Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (N ↘ Spec (.of ℂ)) D.genericPoint = 2)
    (L : QDivisor N) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) h))
      (isProperMap_map (K := ℂ) h) (2 * 2 : ℕ)).hom
        (Chow.divisorClass M (inverseTransformDivisor h L)) = Chow.divisorClass N L := by
  classical
  haveI : IsIso (h ∣_ biregularLocus h) := isBiregular_biregularLocus h
  have key : ∀ D : Mori.PrimeDivisor N,
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) h))
        (isProperMap_map (K := ℂ) h) (2 * 2 : ℕ)).hom
        (Chow.divisorClass M (inverseTransformDivisor h (Finsupp.single D 1))) =
      Chow.divisorClass N (Finsupp.single D 1) := by
    intro D
    -- `η_D` lies in the biregular locus, and `h` maps a point `ξ` to it
    have hη : D.genericPoint ∈ biregularLocus h := by
      by_contra hη
      have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hcodim _ hη
      rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
      exact absurd this (by decide)
    obtain ⟨p, hp0⟩ := (h ∣_ biregularLocus h).homeomorph.surjective ⟨D.genericPoint, hη⟩
    have hp : (h ∣_ biregularLocus h) p = ⟨D.genericPoint, hη⟩ := hp0
    have hξ : h p.1 = D.genericPoint := by
      have := congrArg Subtype.val hp
      rwa [morphismRestrict_base_coe] at this
    have hcoh : Order.coheight p.1 = 1 := by
      have h1 : Order.coheight (((h ∣_ biregularLocus h) ≫ (biregularLocus h).ι) p) =
          Order.coheight p := Topology.IsOpenEmbedding.coheight_eq _
        ((h ∣_ biregularLocus h) ≫ (biregularLocus h).ι).isOpenEmbedding
      have h2 : Order.coheight ((h ⁻¹ᵁ biregularLocus h).ι p) = Order.coheight p :=
        Topology.IsOpenEmbedding.coheight_eq _ (h ⁻¹ᵁ biregularLocus h).ι.isOpenEmbedding
      have h3 : ((h ∣_ biregularLocus h) ≫ (biregularLocus h).ι) p = D.genericPoint := by
        rwa [morphismRestrict_ι]
      rw [h3, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
      exact h2.trans h1.symm
    -- the strict transform of `D` is the prime divisor `E` through `ξ`
    let E : Mori.PrimeDivisor M := AlgebraicGeometry.PrimeDivisor.ofCoheightOne p.1 hcoh
    have hEg : E.genericPoint = p.1 := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have hEt : inverseTransformPrimeDivisor h D = some E :=
      inverseTransformPrimeDivisor_eq_some_of_map_genericPoint E D (by rwa [hEg]) hη
    have hx : h E.genericPoint = D.genericPoint := by rwa [hEg]
    rw [inverseTransformDivisor_single_of_eq_some hEt, Chow.divisorClass_single (hM E),
      Chow.divisorClass_single (hN D)]
    change borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) h))
      (isProperMap_map (K := ℂ) h) (2 * 2 : ℕ) (Chow.pointCycleClass ℚ E.genericPoint (hM E)) = _
    rw [Chow.pushforward_pointCycleClass,
      residueDegree_eq_one_of_isIso h (biregularLocus h) _ (by rwa [hx]),
      Nat.cast_one, one_smul, hx, Chow.pointCycleClassOrZero,
      dif_pos (show _ = ((2 : ℕ) : ℤ) from hN D)]
  have hlin : (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) h)) (isProperMap_map (K := ℂ) h) (2 * 2 : ℕ)).hom ∘ₗ
      Chow.divisorClass M ∘ₗ inverseTransformDivisorₗ ℚ h = Chow.divisorClass N :=
    Finsupp.lhom_ext' fun D ↦ LinearMap.ext_ring (by simpa using key D)
  exact LinearMap.congr_fun hlin L

/-- **Strict-transform lifts of a homologically trivial divisor.** Let `h : M ⟶ N` be a
projective birational morphism over `ℂ`, with `M` a smooth projective threefold and `N` a normal
projective variety, and let `L` be a `ℚ`-divisor on `N` with `[L] = 0` in `H_4(N, ℚ)`. Then there
is a `ℚ`-divisor `c` on `M`, each of whose prime components maps under `h` to a subset of `N` of
dimension at most one, with `[h⁻¹_* L + c] = 0` in `H_4(M, ℚ)`. -/
@[mmp "lem_mmp_conductor_strict_divisor_lift"]
public theorem exists_divisorClass_inverseTransformDivisor_add_eq_zero {M N : Scheme.{0}}
    [M.Over (Spec (.of ℂ))] [N.Over (Spec (.of ℂ))] [IsComplexScheme M] [IsComplexScheme N]
    (hM : Mori.IsProjectiveVariety ℂ (M ↘ Spec (.of ℂ)))
    (hMs : Mori.IsSmoothScheme (M ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim M = 3)
    (hN : Mori.IsProjectiveVariety ℂ (N ↘ Spec (.of ℂ))) [IsNormal N]
    (h : M ⟶ N) [h.IsOver (Spec (.of ℂ))] (hproj : IsProjectiveMorphism h)
    (hbir : Mori.IsBirationalMorphism h)
    (L : QDivisor N) (hL : Chow.divisorClass N L = 0) :
    ∃ c : QDivisor M, (∀ E ∈ c.support, topologicalKrullDim (h.base '' E.support) ≤ 1) ∧
      Chow.divisorClass M (inverseTransformDivisor h L + c) = 0 := by
  classical
  obtain ⟨hMv, -⟩ := (Mori.isProjectiveVariety_iff ℂ _).mp hM
  obtain ⟨hNv, -⟩ := (Mori.isProjectiveVariety_iff ℂ _).mp hN
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hproj
  haveI : IsIntegral M := hMv.toIsIntegral
  haveI : IsIntegral N := hNv.toIsIntegral
  haveI : LocallyOfFiniteType (M ↘ Spec (.of ℂ)) := hMv.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (N ↘ Spec (.of ℂ)) := hNv.toLocallyOfFiniteType
  have hcodim : 2 ≤ closedsCodimension (biregularLocus h).compl :=
    two_le_closedsCodimension_compl_biregularLocus (N ↘ Spec (.of ℂ)) h (hY := hNv)
      (hX := by rwa [CategoryTheory.comp_over]) hbir
  have hdimN : topologicalKrullDim N = 3 := by
    haveI := hMv
    haveI := hNv
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (N ↘ Spec (.of ℂ))
      (M ↘ Spec (.of ℂ)) hbir, hdim]
  -- points off the biregular locus have closures of dimension at most one
  have hdimcl : ∀ y : N, y ∉ biregularLocus h → topologicalKrullDim (closure {y} : Set N) ≤ 1 := by
    intro y hy
    have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (N ↘ Spec (.of ℂ)) y
    rw [hdimN] at h1
    have := le_natCast_sub_of_add_eq (n := 3) (k := 2) (by exact_mod_cast h1)
      (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hcodim y hy)
    simpa using this
  -- the open `U = h⁻¹ V` is nonempty
  have hUne : ((h ⁻¹ᵁ biregularLocus h : M.Opens) : Set M).Nonempty := by
    have hη : genericPoint N ∈ biregularLocus h := by
      by_contra hη
      have h1 := hdimcl _ hη
      rw [(genericPoint_spec N).def, IsHomeomorph.topologicalKrullDim_eq _
        (Homeomorph.Set.univ N).isHomeomorph, hdimN] at h1
      exact absurd h1 (by decide)
    haveI : IsIso (h ∣_ biregularLocus h) := isBiregular_biregularLocus h
    obtain ⟨p, -⟩ := (h ∣_ biregularLocus h).surjective ⟨genericPoint N, hη⟩
    exact ⟨p.1, p.2⟩
  -- its complement has dimension at most two
  have hdimA : topologicalKrullDim ↥((h ⁻¹ᵁ biregularLocus h : M.Opens) : Set M)ᶜ ≤ (2 : ℕ) := by
    have hle : topologicalKrullDim ↥(((h ⁻¹ᵁ biregularLocus h : M.Opens) : Set M)ᶜ) ≤ 3 :=
      (topologicalKrullDim_subspace_le _ _).trans hdim.le
    have hlt := MMP.topologicalKrullDim_lt_of_isClosed_of_ne_univ
      (h ⁻¹ᵁ biregularLocus h).isOpen.isClosed_compl
      (fun he ↦ by
        obtain ⟨x, hx⟩ := hUne
        exact (Set.eq_univ_iff_forall.mp he x) hx)
      (fun ht ↦ by rw [ht] at hle; exact absurd hle (by decide))
    rw [hdim] at hlt
    exact le_of_lt_natCast_succ (n := 2) hlt
  -- the class of the strict transform pushes forward to `[L] = 0`, so it vanishes over `V`
  haveI : IsIso (h ∣_ biregularLocus h) := isBiregular_biregularLocus h
  have hpush := pushforward_divisorClass_inverseTransformDivisor h hcodim
    (fun E ↦ (relativeDimension_eq_two_iff hdim _).2 E.coheight_genericPoint)
    (fun D ↦ (relativeDimension_eq_two_iff hdimN _).2 D.coheight_genericPoint) L
  rw [hL] at hpush
  have hy0 := restrict_comap_eq_zero_of_pushforward_eq_zero h (biregularLocus h) _ _ hpush
  have hspan := MMP.Analytic.mem_span_pointCycleClassOrZero_of_restrict_eq_zero (n := 2)
    (h ⁻¹ᵁ biregularLocus h) _ (fun p ↦ by
      change map (K := ℂ) h p ∈ opensRangeMap (biregularLocus h).ι ↔ _
      rw [mem_opensRangeMap_ι_iff, toHom_map]
      rfl) hdimA _ hy0
  obtain ⟨l, hlS, hl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℚ).mp hspan
  -- the surfaces of `M` are prime divisors
  let d : M → QDivisor M := fun x ↦
    if hx : Order.coheight x = 1 then
      Finsupp.single (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx : Mori.PrimeDivisor M) 1
    else 0
  have hd : ∀ x, Chow.divisorClass M (d x) = Chow.pointCycleClassOrZero ℚ 2 x := by
    intro x
    by_cases hx : Order.coheight x = 1
    · let E : Mori.PrimeDivisor M := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx
      have hEg : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have hE2 := (relativeDimension_eq_two_iff hdim E.genericPoint).2 E.coheight_genericPoint
      change Chow.divisorClass M (if hx : Order.coheight x = 1 then
        Finsupp.single (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx : Mori.PrimeDivisor M) 1
        else 0) = _
      rw [dif_pos hx]
      change Chow.divisorClass M (Finsupp.single E 1) = _
      rw [Chow.divisorClass_single hE2]
      conv_rhs => rw [← hEg]
      rw [Chow.pointCycleClassOrZero, dif_pos (show _ = ((2 : ℕ) : ℤ) from hE2)]
    · change Chow.divisorClass M (if hx : Order.coheight x = 1 then
        Finsupp.single (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx : Mori.PrimeDivisor M) 1
        else 0) = _
      rw [dif_neg hx, map_zero, Chow.pointCycleClassOrZero,
        dif_neg fun h2 : _ = ((2 : ℕ) : ℤ) ↦ hx ((relativeDimension_eq_two_iff hdim x).1 h2)]
  refine ⟨-Finsupp.linearCombination ℚ d l, ?_, ?_⟩
  · intro E hE
    rw [Finsupp.support_neg, Finsupp.linearCombination_apply, Finsupp.sum] at hE
    obtain ⟨x, hxl, hEx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hE)
    have hEx' := Finsupp.support_smul hEx
    have hxU : x ∉ h ⁻¹ᵁ biregularLocus h := (Finsupp.mem_supported ℚ l).1 hlS hxl
    by_cases hx : Order.coheight x = 1
    · have hdx : d x = Finsupp.single
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx : Mori.PrimeDivisor M) 1 :=
        dif_pos hx
      rw [hdx, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hEx'
      subst hEx'
      have hEgen : AlgebraicGeometry.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx) = x :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hEgen,
        ← h.isClosedMap.closure_image_eq_of_continuous h.continuous, Set.image_singleton]
      exact hdimcl _ hxU
    · have hdx : d x = 0 := dif_neg hx
      rw [hdx, Finsupp.support_zero] at hEx'
      exact absurd hEx' (Finset.notMem_empty _)
  · rw [map_add, map_neg, Finsupp.apply_linearCombination,
      show Chow.divisorClass M ∘ d = Chow.pointCycleClassOrZero ℚ 2 from funext hd, hl,
      add_neg_cancel]

end MMP.Fourfold

namespace MMP.Mori

/-! ### Connectedness of ample divisors on normal varieties -/

open CategoryTheory AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **An effective ample divisor on a normal projective variety is connected.** Let `X` be an
integral normal scheme, projective over a field `k`, of dimension at least two, and let `A` be an
effective Cartier divisor on `X` with `𝒪_X(A)` ample. Then `Supp A` is connected (in particular
nonempty). -/
@[mmp "lem_mmp_fa15_ample_divisor_connected"]
public theorem isConnected_support_of_isAmple_divisorSheaf_of_isNormal (hproj : IsProjective f)
    [IsIntegral X] [IsNormal X] (hdim : 2 ≤ topologicalKrullDim X)
    (A : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor A]
    (hA : haveI := Stacks.Divisors.isInvertible_divisorSheaf A
      Stacks.Ample.IsAmple X (Stacks.Divisors.divisorSheaf A)) :
    _root_.IsConnected (A.support : Set X) := by
  have : IsProper f := hproj.isProper
  have := LocallyOfFiniteType.isLocallyNoetherian f
  refine isConnected_support_of_two_le_depth f (fun x hx ↦ ?_) A hA
  refine VectorBundleCodimensionOne.two_le_depth_stalk_of_isNormal x ?_
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f x hx,
    topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k X f
      (.of_preirreducibleSpace X) x]
  exact_mod_cast hdim

end MMP.Mori

end
