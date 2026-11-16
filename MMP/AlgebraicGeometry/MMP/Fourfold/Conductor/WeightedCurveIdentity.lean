module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureAssociatedPoints
import StacksFrontier.AlgebraicGeometry.RegularImmersion.StalkDimension
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothPermanence
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.NoetherianRegularKoszul
import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
import MMP.AlgebraicGeometry.Variety.StalkDimensionClosedPoint
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceCurves
import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwist
import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
import MMP.AlgebraicTopology.BorelMoore.TopHomologyRestriction
import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
import MMP.AlgebraicTopology.PoincareDuality.AlexanderGeneral
import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Iterate
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreLongExact
import MMP.AlgebraicTopology.CapProduct.SupportLemmas
import MMP.AlgebraicTopology.CapProduct.SupportRetraction
import MMP.AlgebraicTopology.FundamentalClass.Exists
import MMP.AlgebraicTopology.PoincareDuality.AlexanderCocycleDuality
import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.Intersection.Nef
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Resolution.Basic
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.DualityAntiampleFibre
import MMP.AlgebraicGeometry.Analytic.SupportedDuality
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import MMP.AlgebraicGeometry.IdealSheafSubscheme
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import MMP.AlgebraicGeometry.SubschemeOver
import MMP.AlgebraicGeometry.Chow.CycleClassDegree
import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase

/-!
# The weighted curve identity on an antiample snc surface fibre

Let `W` be a smooth complex threefold, `E = ⋃ᵢ Eᵢ` an snc divisor with proper components and
`D = ∑ᵢ mᵢ Eᵢ`, all `mᵢ > 0`, such that `-D` is Cartier and ample on every `Eᵢ`. Let
`a = (a_{ij,C})` be an oriented coefficient system on the double curves of `E` (a double curve `C`
of the pair `(Eᵢ, Eⱼ)` is a connected component of `Eᵢ ∩ Eⱼ`, and `a_{ji,C} = -a_{ij,C}`), let
`Zᵢ = ∑_{j, C} a_{ij,C} C` be its divisor on the surface `Eᵢ` and `b_{ij,C} = a_{ij,C}/(mᵢ mⱼ)`.
Then
`∑_{i<j, C} mᵢ mⱼ b_{ij,C}² (D · C)`
`  = ∑ᵢ Zᵢ²/mᵢ + ∑_{i<j<k, p} mᵢ mⱼ mₖ (b_{ij,p} - b_{ik,p} + b_{jk,p})²`,
the last sum running over the triple points `p ∈ Eᵢ ∩ Eⱼ ∩ Eₖ`. Since `(D · C) < 0` for every
double curve, the left side is nonpositive and vanishes only for `a = 0`; if every class `[Zᵢ]`
vanishes in `H_2(Eᵢ, ℚ)`, then `Zᵢ² = 0`, so both sides vanish and `a = 0`.

The intersection numbers are computed locally. On `Eᵢ`, a double curve `C` is a prime divisor;
distinct double curves on `Eᵢ` meet transversally at the triple points and are disjoint when they
lie on the same pair of components. The restriction of `Eⱼ` to `Eᵢ` is the sum of the double curves
of `(Eᵢ, Eⱼ)`, so `(D · C)` splits into the two self-intersections of `C` on its two components
and the triple-point counts. The identity is then the algebraic identity
`u² + v² + w² - 2 (uv - uw + vw) = (u - v + w)²` at each triple point, summed.

For the second part, the class of `Zᵢ` vanishing in `H₂(Eᵢ, ℚ)` forces `(Zᵢ · C) = 0` for every
curve `C ⊆ Eᵢ`. This is duality on the smooth projective surface `Eᵢ` (projective because
`-D|_{Eᵢ}` is ample), together with Fulton's Theorem 19.2 for the classes of Cartier divisors.
Ampleness of `-D` makes every `(D · C)` negative, so the left side of the identity is at most zero
and the right side at least zero, and every coefficient vanishes.

## Main results

* `MMP.Threefold.sum_doubleCurve_intersectionNumber_eq_and_eq_zero_of_cycleClass_eq_zero`: the
  weighted curve identity, and the vanishing of an oriented system whose divisors `Zᵢ` all have
  zero class in `H_2(Eᵢ, ℚ)`.

## Implementation notes

* The components `Eᵢ` are the prime divisors in the support of `D`, with their reduced structure,
  and `mᵢ` is the coefficient of `D` at `Eᵢ`; double curves and oriented systems are
  `MMP.Fourfold.DoubleSurface D` and `MMP.Fourfold.orientedSurfaceCoefficients D`, and
  `Zᵢ = MMP.Fourfold.surfaceCoefficientDivisor a Eᵢ`. The coefficient `b_{ij,p}` at a triple
  point is `MMP.Fourfold.coeffAlong` along `{p}` divided by `mᵢ mⱼ`.
* A double curve `C ⊆ Eᵢ ∩ Eⱼ` is the reduced closed subscheme of `Eᵢ` on the preimage of `C`,
  embedded in `W` through `Eᵢ`. `(D · C)` and the intersection numbers on `Eᵢ` are
  `MMP.Mori.QDivisor.intersectionNumber`. The self-intersection is expanded by linearity in the
  curve: `Zᵢ² = ∑_{j, C} a_{ij,C} (Zᵢ · C)_{Eᵢ}`.
* The sums over `i < j` and `i < j < k` are written as sums over ordered pairs (all double curves
  `σ`, each unordered curve counted twice) and ordered triples of distinct components, divided by
  `2` and `6`; their summands are invariant under reordering, since `a` is oriented.
* "`E` projective" is properness of every `Eᵢ` over `ℂ`; a proper surface carrying the ample
  `-D|_{Eᵢ}` is projective. "`A = -D` ample on `Eᵢ`" is ampleness of the pull-back of `𝒪_W(-D)`
  to `Eᵢ`.
* The class `[Zᵢ] ∈ H_2(Eᵢ, ℚ)` is the cycle class (`MMP.Chow.rationalCycleClass`) of the
  rational `1`-cycle `∑_P (Zᵢ)_P [P]` on the surface `Eᵢ`.
* The normality of the `Eᵢ`, the `ℚ`-Cartier property of `D` and of the `Zᵢ` and the dimension
  of the double curves, needed to form the intersection numbers, follow from smoothness and the
  snc condition; they are asserted in the conclusion.
* The combinatorics is proved for an abstract configuration of components, double curves and
  triple points, and then specialized. The comparison of the class in `H₂` with intersection
  numbers follows the proof for threefolds in
  `MMP.Threefold.isNumericallyTrivial_of_divisorClass_eq_zero`, here on a surface.
* The auxiliary lemmas of the proof live in the namespace
  `Proof_lem_mmp_conductor_threefold_weighted_curve_identity`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Theorem 19.2
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open scoped MMP.SubschemeOver

namespace Proof_lem_mmp_conductor_threefold_weighted_curve_identity

open MMP.Mori MMP.Fourfold

/-! ### Connected components with unique local generizations -/

/-- In a Noetherian quasi-sober space, let `S` be a closed set every point `y` of which has a
generalization `ζ ∈ S` from which every generalization of `y` lying in `S` specializes. Then the
connected component of `S` through `x` is the closure of such a `ζ` for `x`. -/
private theorem connectedComponentIn_eq_closure_of_forall {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {S : Set X} (hS : IsClosed S)
    (hloc : ∀ y ∈ S, ∃ ζ ∈ S, ζ ⤳ y ∧ ∀ ξ ∈ S, ξ ⤳ y → ζ ⤳ ξ) {x : X} (hx : x ∈ S)
    {ζ : X} (hζS : ζ ∈ S) (hζx : ζ ⤳ x) (hζ : ∀ ξ ∈ S, ξ ⤳ x → ζ ⤳ ξ) :
    connectedComponentIn S x = closure {ζ} := by
  classical
  set K := connectedComponentIn S x with hKdef
  have hKS : K ⊆ S := connectedComponentIn_subset S x
  have hxK : x ∈ K := mem_connectedComponentIn hx
  have hKc : IsPreconnected K := isPreconnected_connectedComponentIn
  have hKcl : IsClosed K := by
    refine closure_subset_iff_isClosed.mp ?_
    exact hKc.closure.subset_connectedComponentIn (subset_closure hxK)
      (closure_minimal hKS hS)
  have : Nonempty X := ⟨x⟩
  choose! g hgS hgy hgmax using hloc
  -- closures of the `g y` lie in `K`
  have hsubK : ∀ y ∈ K, closure {g y} ⊆ K := by
    intro y hy
    have hyS := hKS hy
    have h1 : closure {g y} ⊆ connectedComponentIn S y :=
      (isIrreducible_singleton (x := g y)).closure.isConnected.isPreconnected.subset_connectedComponentIn
        (specializes_iff_mem_closure.mp (hgy y hyS)) (closure_minimal
          (Set.singleton_subset_iff.mpr (hgS y hyS)) hS)
    rwa [← connectedComponentIn_eq hy] at h1
  -- two such closures meeting are equal
  have hmax : ∀ y ∈ S, ∀ w ∈ S, (closure {g y} ∩ closure {g w}).Nonempty →
      closure {g y} = closure {g w} := by
    have key : ∀ y ∈ S, ∀ v ∈ S, g y ⤳ v → closure {g y} = closure {g v} := by
      intro y hy v hv hyv
      have h1 : g v ⤳ g y := hgmax v hv (g y) (hgS y hy) hyv
      have h2 : g y ⤳ g v := hgmax y hy (g v) (hgS v hv) (h1.trans (hgy y hy))
      exact subset_antisymm (specializes_iff_closure_subset.mp h1)
        (specializes_iff_closure_subset.mp h2)
    rintro y hy w hw ⟨v, hvy, hvw⟩
    have hvS : v ∈ S := closure_minimal (Set.singleton_subset_iff.mpr (hgS y hy)) hS hvy
    rw [key y hy v hvS (specializes_iff_mem_closure.mpr hvy),
      key w hw v hvS (specializes_iff_mem_closure.mpr hvw)]
  -- a finite cover of `K` by irreducible closed sets
  obtain ⟨T, hT, hTc, hTi, hKT⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hKcl
  have hgen : ∀ t ∈ T, ∃ e, IsGenericPoint e t := fun t ht =>
    QuasiSober.sober (hTi t ht) (hTc t ht)
  choose! e he using hgen
  have heK : ∀ t ∈ T, e t ∈ K := fun t ht => by
    rw [hKT]; exact Set.mem_sUnion_of_mem (he t ht).mem ht
  have htsub : ∀ t ∈ T, t ⊆ closure {g (e t)} := by
    intro t ht
    have h := (he t ht).def
    conv_lhs => rw [← h]
    exact specializes_iff_closure_subset.mp (hgy _ (hKS (heK t ht)))
  set A := closure {g x}
  have hxA : x ∈ A := specializes_iff_mem_closure.mp (hgy x hx)
  set T' := {t ∈ T | closure {g (e t)} ≠ A}
  set B := ⋃ t ∈ T', closure {g (e t)}
  have hBc : IsClosed B :=
    (hT.subset (Set.sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure
  have hKAB : K ⊆ A ∪ B := by
    intro y hy
    rw [hKT] at hy
    obtain ⟨t, ht, hyt⟩ := Set.mem_sUnion.mp hy
    by_cases h : closure {g (e t)} = A
    · exact Or.inl (h ▸ htsub t ht hyt)
    · exact Or.inr (Set.mem_biUnion (x := t) ⟨ht, h⟩ (htsub t ht hyt))
  have hdisj : K ∩ (A ∩ B) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨-, hyA, hyB⟩
    obtain ⟨t, ⟨ht, hne⟩, hyt⟩ := Set.mem_iUnion₂.mp hyB
    exact hne (hmax _ (hKS (heK t ht)) x hx ⟨y, hyt, hyA⟩)
  have hKA : K ⊆ A := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hKc) A B isClosed_closure hBc hKAB
      hdisj with h | h
    · exact h
    · exfalso
      obtain ⟨t, ⟨ht, hne⟩, hxt⟩ := Set.mem_iUnion₂.mp (h hxK)
      exact hne (hmax _ (hKS (heK t ht)) x hx ⟨x, hxt, hxA⟩)
  have hAK : A ⊆ K := hsubK x hxK
  have hAeq : A = closure {ζ} := by
    have h1 : g x ⤳ ζ := hgmax x hx ζ hζS hζx
    have h2 : ζ ⤳ g x := hζ (g x) (hgS x hx) (hgy x hx)
    exact subset_antisymm (specializes_iff_closure_subset.mp h2)
      (specializes_iff_closure_subset.mp h1)
  rw [← hAeq]
  exact subset_antisymm hKA hAK

/-- In a Noetherian quasi-sober space, a closed set all of whose points are closed is finite. -/
private theorem finite_of_isClosed_of_forall_isClosed_singleton {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {S : Set X} (hS : IsClosed S)
    (h : ∀ x ∈ S, IsClosed ({x} : Set X)) : S.Finite := by
  haveI : QuasiSober S := hS.isClosedEmbedding_subtypeVal.quasiSober
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := S)
  have hsub : ∀ Z ∈ irreducibleComponents S, ∃ x : S, Z = {x} := by
    intro Z hZ
    obtain ⟨x, hx⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
    refine ⟨x, ?_⟩
    rw [← hx.def]
    have : IsClosed ({x} : Set S) := by
      have := (h x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ S)))
      convert this using 1
      ext y
      simp [Subtype.ext_iff]
    exact this.closure_eq
  have hcov : (Set.univ : Set S) ⊆ ⋃ Z ∈ irreducibleComponents S, Z := by
    intro y _
    obtain ⟨Z, hZ, hy⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
    exact Set.mem_biUnion hZ (hy rfl)
  have hU : (Set.univ : Set S).Finite :=
    (hfin.biUnion fun Z hZ => by
      obtain ⟨x, rfl⟩ := hsub Z hZ
      exact Set.finite_singleton x).subset hcov
  simpa using hU.image (Subtype.val : S → X)

/-! ### Two components of a simple normal crossing divisor -/

section SNC

variable {W Y : Scheme.{0}} [IsLocallyNoetherian W] {f : W ⟶ Y} {D : Divisor W}

/-- At a point `y` of two distinct components `E`, `E'` of an snc divisor, the ideals of `E` and
`E'` in `𝒪_{W,y}` are generated by two distinct members of one regular system of parameters. -/
private theorem exists_pair_of_isSNC (hD : DivisorWithCoeffs.IsSNC f D)
    {E E' : MMP.Mori.PrimeDivisor W} (hE : E ∈ D.support) (hE' : E' ∈ D.support) (hne : E ≠ E')
    {y : W} (hyE : y ∈ E.support) (hyE' : y ∈ E'.support) :
    ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk y) (a b : Fin n),
      IsRegularSystemOfParameters z ∧ a ≠ b ∧
      IdealSheafData.stalk E.idealSheaf y = Ideal.span {z a} ∧
      IdealSheafData.stalk E'.idealSheaf y = Ideal.span {z b} := by
  obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2 y
  have hab : j ⟨E, hE, hyE⟩ ≠ j ⟨E', hE', hyE'⟩ := by
    intro h
    have h' := hj h
    rw [Subtype.mk.injEq] at h'
    exact hne h'
  exact ⟨n, z, j ⟨E, hE, hyE⟩, j ⟨E', hE', hyE'⟩, hz, hab, hI ⟨E, hE, hyE⟩, hI ⟨E', hE', hyE'⟩⟩

/-- The sum of the ideals of two distinct members of a regular system of parameters is the span
of the two members, a prime ideal. -/
private theorem isPrime_span_pair {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} {z : Fin n → R} (hz : IsRegularSystemOfParameters z) (a b : Fin n) :
    (Ideal.span {z a} ⊔ Ideal.span {z b}).IsPrime := by
  classical
  have h := MMP.Resolution.span_image_isPrime_of_isRegularSystemOfParameters hz {a, b}
  rwa [Finset.coe_pair, Set.image_pair, Ideal.span_insert] at h

/-- **Local generic point of a double intersection.** At a point `y` of `E ∩ E'`, for distinct
components `E`, `E'` of an snc divisor, the prime `I_{E,y} + I_{E',y}` of `𝒪_{W,y}` is the
prime of a generization `ζ ∈ E ∩ E'` of `y`, from which every generization of `y` in `E ∩ E'`
specializes. -/
private theorem exists_generization_of_isSNC (hD : DivisorWithCoeffs.IsSNC f D)
    {E E' : MMP.Mori.PrimeDivisor W} (hE : E ∈ D.support) (hE' : E' ∈ D.support) (hne : E ≠ E')
    {y : W} (hy : y ∈ E.support ∩ E'.support) :
    ∃ ζ ∈ E.support ∩ E'.support, ∃ h : ζ ⤳ y,
      MMP.Intersection.primeOfSpecializes h =
        IdealSheafData.stalk E.idealSheaf y ⊔ IdealSheafData.stalk E'.idealSheaf y ∧
      ∀ ξ ∈ E.support ∩ E'.support, ξ ⤳ y → ζ ⤳ ξ := by
  obtain ⟨n, z, a, b, hz, -, ha, hb⟩ := exists_pair_of_isSNC hD hE hE' hne hy.1 hy.2
  set 𝔭 := IdealSheafData.stalk E.idealSheaf y ⊔ IdealSheafData.stalk E'.idealSheaf y with h𝔭
  have hprime : 𝔭.IsPrime := by
    rw [h𝔭, ha, hb]; exact isPrime_span_pair hz a b
  have hζy := MMP.Resolution.specializes_fromSpecStalk y ⟨𝔭, hprime⟩
  have hpζ := MMP.Resolution.primeOfSpecializes_fromSpecStalk y ⟨𝔭, hprime⟩ hζy
  refine ⟨W.fromSpecStalk y ⟨𝔭, hprime⟩, ⟨?_, ?_⟩, hζy, hpζ, fun ξ hξ hξy => ?_⟩
  · change _ ∈ E.idealSheaf.support
    rw [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hζy, hpζ]
    exact le_sup_left
  · change _ ∈ E'.idealSheaf.support
    rw [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hζy, hpζ]
    exact le_sup_right
  refine MMP.Intersection.specializes_of_primeOfSpecializes_le hζy hξy ?_
  rw [hpζ]
  exact sup_le ((MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hξy).1 hξ.1)
    ((MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hξy).1 hξ.2)

/-- **Double surfaces are irreducible.** On a Noetherian scheme, the carrier of a double
surface `σ` of an snc divisor is the closure of a point `ζ` whose prime in `𝒪_{W,y}`, at every
point `y` of the carrier, is `I_{Eᵢ,y} + I_{Eⱼ,y}`. -/
private theorem exists_isGenericPoint_carrier [NoetherianSpace W]
    (hD : DivisorWithCoeffs.IsSNC f D) (σ : DoubleSurface D) :
    ∃ ζ, IsGenericPoint ζ σ.carrier ∧ ∀ y ∈ σ.carrier, ∀ h : ζ ⤳ y,
      MMP.Intersection.primeOfSpecializes h =
        IdealSheafData.stalk σ.fst.idealSheaf y ⊔ IdealSheafData.stalk σ.snd.idealSheaf y := by
  set S : Set W := σ.fst.support ∩ σ.snd.support with hSdef
  have hS : IsClosed S := σ.fst.idealSheaf.support.isClosed.inter σ.snd.idealSheaf.support.isClosed
  have hloc : ∀ y ∈ S, ∃ ζ ∈ S, ζ ⤳ y ∧ ∀ ξ ∈ S, ξ ⤳ y → ζ ⤳ ξ := by
    intro y hy
    obtain ⟨ζ, hζS, hζy, -, hmax⟩ :=
      exists_generization_of_isSNC hD σ.fst_mem σ.snd_mem σ.fst_ne_snd hy
    exact ⟨ζ, hζS, hζy, hmax⟩
  have key : ∀ y ∈ σ.carrier, ∃ ζ, IsGenericPoint ζ σ.carrier ∧ ∃ h : ζ ⤳ y,
      MMP.Intersection.primeOfSpecializes h =
        IdealSheafData.stalk σ.fst.idealSheaf y ⊔ IdealSheafData.stalk σ.snd.idealSheaf y := by
    intro y hy
    obtain ⟨ζ, hζS, hζy, hp, hmax⟩ :=
      exists_generization_of_isSNC hD σ.fst_mem σ.snd_mem σ.fst_ne_snd (σ.carrier_subset hy)
    refine ⟨ζ, ?_, hζy, hp⟩
    change closure {ζ} = σ.carrier
    rw [σ.carrier_eq_connectedComponentIn hy]
    exact (connectedComponentIn_eq_closure_of_forall hS hloc (σ.carrier_subset hy) hζS hζy
      hmax).symm
  obtain ⟨y₀, hy₀⟩ := σ.carrier_nonempty
  obtain ⟨ζ, hζ, -⟩ := key y₀ hy₀
  refine ⟨ζ, hζ, fun y hy h => ?_⟩
  obtain ⟨ζ', hζ', h', hp'⟩ := key y hy
  obtain rfl : ζ' = ζ := hζ'.eq hζ
  exact hp'

/-- The prime of the trivial generization `x ⤳ x` is the maximal ideal. -/
private theorem primeOfSpecializes_refl {X : Scheme.{0}} (x : X) :
    MMP.Intersection.primeOfSpecializes (specializes_refl x) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  change Ideal.comap (X.presheaf.stalkSpecializes (specializes_refl x)).hom _ = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Ideal.comap_id _

/-- If the maximal ideal of a Noetherian local ring is generated by two distinct members `z_a`,
`z_b` of a regular system of parameters `z`, then `z` has length two. -/
private theorem eq_two_of_maximalIdeal_eq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {n : ℕ} {z : Fin n → R} (hz : IsRegularSystemOfParameters z)
    {a b : Fin n} (hab : a ≠ b)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {z a} ⊔ Ideal.span {z b}) : n = 2 := by
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hrank := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hz.2] at hrank
  have hn : (IsLocalRing.maximalIdeal R).spanFinrank = n := by exact_mod_cast hrank
  rw [hm, ← Ideal.span_insert] at hn
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R)
    (Set.toFinite ({z a, z b} : Set R))
  have hcard : ({z a, z b} : Set R).ncard ≤ 2 := by
    have := Set.ncard_insert_le (z a) ({z b} : Set R)
    rwa [Set.ncard_singleton] at this
  have hsp : (Ideal.span {z a, z b}).spanFinrank =
      (Submodule.span R ({z a, z b} : Set R)).spanFinrank := rfl
  have ha := a.isLt
  have hb := b.isLt
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  change (Ideal.span {z a, z b}).spanFinrank = n at hn
  omega

/-- The local ring of a closed subscheme is the quotient of the local ring of the ambient scheme by
the stalk of the ideal. -/
private noncomputable def stalkSubschemeEquiv {X : Scheme.{0}} (I : X.IdealSheafData)
    (x : I.subscheme) :
    (X.presheaf.stalk (I.subschemeι x) ⧸ IdealSheafData.stalk I (I.subschemeι x)) ≃+*
      I.subscheme.presheaf.stalk x :=
  (Ideal.quotEquivOfEq (Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk I x).symm).trans
    (RingHom.quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective x))

/-- If the ideal of a closed subscheme at a point is generated by a member of a regular system of
parameters of length `n`, the local ring of the subscheme there has dimension `n - 1`. -/
private theorem ringKrullDim_stalk_subscheme_eq {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : I.subscheme) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (I.subschemeι x)} (hz : IsRegularSystemOfParameters z)
    (a : Fin n) (ha : IdealSheafData.stalk I (I.subschemeι x) = Ideal.span {z a}) :
    ringKrullDim (I.subscheme.presheaf.stalk x) = (n - 1 : ℕ) := by
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  rw [← ringKrullDim_eq_of_ringEquiv (stalkSubschemeEquiv I x), ha]
  exact MMP.Resolution.ringKrullDim_quotient_span_singleton_of_isRegularSystemOfParameters hz a

end SNC

/-! ### Dimensions of local rings -/

section Dimension

/-- At a closed point of a complex scheme smooth of relative dimension `d` over `ℂ`, the local
ring has dimension `d`. -/
private theorem ringKrullDim_stalk_eq_of_isClosed {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    (d : ℕ) [SmoothOfRelativeDimension d (W ↘ Spec (.of ℂ))] (x : W)
    (hx : IsClosed ({x} : Set W)) : ringKrullDim (W.presheaf.stalk x) = d := by
  haveI : Smooth (W ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth d (W ↘ Spec (.of ℂ))
  rw [← topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point (W ↘ Spec (.of ℂ)) x hx]
  exact topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field d (W ↘ Spec (.of ℂ)) x

/-- The local ring at a `ℂ`-point of a complex scheme smooth of relative dimension `d` over `ℂ`
has dimension `d`. -/
private theorem ringKrullDim_stalk_eq_of_smoothOfRelativeDimension {U : Scheme.{0}}
    [U.Over (Spec (.of ℂ))] (d : ℕ) [SmoothOfRelativeDimension d (U ↘ Spec (.of ℂ))]
    (p : UnderlyingSpace ℂ U) :
    ringKrullDim (U.presheaf.stalk (p.toHom (IsLocalRing.closedPoint ℂ))) = d := by
  haveI : Smooth (U ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth d (U ↘ Spec (.of ℂ))
  exact ringKrullDim_stalk_eq_of_isClosed d _ (UnderlyingSpace.equivClosedPoints U p).2

end Dimension

/-! ### Components and triple points of an snc divisor on a smooth threefold -/

section Threefold

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] [QuasiCompact (W ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 3 (W ↘ Spec (.of ℂ))] {D : Divisor W}

/-- On a smooth threefold, a point whose local ring has dimension at least three is closed. -/
private theorem isClosed_singleton_of_three_le (x : W)
    (h : (3 : WithBot ℕ∞) ≤ ringKrullDim (W.presheaf.stalk x)) : IsClosed ({x} : Set W) := by
  haveI : CompactSpace W :=
    (quasiCompact_iff_compactSpace (W ↘ Spec (.of ℂ))).mp inferInstance
  by_contra hx
  obtain ⟨y, hyx, hy⟩ := isClosed_closure.exists_closed_singleton
    (⟨x, subset_closure rfl⟩ : (closure ({x} : Set W)).Nonempty)
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hyx
  have hne : y ≠ x := fun e => hx (e ▸ hy)
  have hlt : y < x := MMP.Intersection.lt_of_specializes_of_ne hxy hne
  have h3 := ringKrullDim_stalk_eq_of_isClosed 3 y hy
  rw [ringKrullDim_stalk_eq_coheight] at h3 h
  have h3' : Order.coheight y = 3 := WithBot.coe_inj.mp (h3.trans rfl)
  have h' : (3 : ℕ∞) ≤ Order.coheight x := WithBot.coe_le_coe.mp (le_trans (le_of_eq rfl) h)
  have h1 : Order.coheight x + 1 ≤ 3 := h3' ▸ Order.coheight_add_one_le hlt
  have : (3 : ℕ∞) + 1 ≤ 3 := (add_le_add h' le_rfl).trans h1
  exact absurd this (by norm_num)

variable [IsLocallyNoetherian W]

/-- **Triple points are closed.** A point lying on three distinct components of an snc divisor
on a smooth threefold is a closed point. -/
private theorem isClosed_singleton_of_mem_three (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D)
    {E₁ E₂ E₃ : MMP.Mori.PrimeDivisor W} (h₁ : E₁ ∈ D.support) (h₂ : E₂ ∈ D.support)
    (h₃ : E₃ ∈ D.support) (h₁₂ : E₁ ≠ E₂) (h₁₃ : E₁ ≠ E₃) (h₂₃ : E₂ ≠ E₃) {x : W}
    (hx : x ∈ E₁.support ∩ E₂.support ∩ E₃.support) : IsClosed ({x} : Set W) := by
  obtain ⟨n, z, j, hz, hj, -⟩ := hD.2 x
  let g : Fin 3 → {E : MMP.Mori.PrimeDivisor W // E ∈ D.support ∧ x ∈ E.support} :=
    ![⟨E₁, h₁, hx.1.1⟩, ⟨E₂, h₂, hx.1.2⟩, ⟨E₃, h₃, hx.2⟩]
  have hg : Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [g, Subtype.ext_iff]
  have hn : 3 ≤ n := by
    simpa using Fintype.card_le_of_injective _ (hj.comp hg)
  refine isClosed_singleton_of_three_le x ?_
  rw [hz.2]
  exact_mod_cast hn

/-- **Triple points are finite.** Three distinct components of an snc divisor on a smooth
complex threefold meet in finitely many points. -/
private theorem finite_inter_inter (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D)
    [NoetherianSpace W] {E₁ E₂ E₃ : MMP.Mori.PrimeDivisor W} (h₁ : E₁ ∈ D.support)
    (h₂ : E₂ ∈ D.support) (h₃ : E₃ ∈ D.support) (h₁₂ : E₁ ≠ E₂) (h₁₃ : E₁ ≠ E₃)
    (h₂₃ : E₂ ≠ E₃) : (E₁.support ∩ E₂.support ∩ E₃.support : Set W).Finite :=
  finite_of_isClosed_of_forall_isClosed_singleton
    (((E₁.idealSheaf.support.isClosed).inter E₂.idealSheaf.support.isClosed).inter
      E₃.idealSheaf.support.isClosed)
    fun _ hx => isClosed_singleton_of_mem_three hD h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hx

/-- **The components are surfaces.** Every component of an snc divisor on a smooth complex
threefold has dimension two. -/
private theorem topologicalKrullDim_component (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D)
    {E : MMP.Mori.PrimeDivisor W} (hE : E ∈ D.support) :
    topologicalKrullDim E.idealSheaf.subscheme = 2 := by
  haveI := E.integral
  haveI : CompactSpace W :=
    (quasiCompact_iff_compactSpace (W ↘ Spec (.of ℂ))).mp inferInstance
  set ι := E.idealSheaf.subschemeι
  haveI : CompactSpace E.idealSheaf.subscheme := ι.isClosedEmbedding.compactSpace
  obtain ⟨x', -, hx'⟩ := isClosed_univ.exists_closed_singleton
    (Set.univ_nonempty : (Set.univ : Set E.idealSheaf.subscheme).Nonempty)
  have hx : IsClosed ({ι x'} : Set W) := by
    have := ι.isClosedEmbedding.isClosedMap _ hx'
    rwa [Set.image_singleton] at this
  have hxE : ι x' ∈ E.support := by
    change _ ∈ (E.idealSheaf.support : Set W)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x', rfl⟩
  obtain ⟨n, z, j, hz, -, hI⟩ := hD.2 (ι x')
  have h3 := ringKrullDim_stalk_eq_of_isClosed 3 (ι x') hx
  rw [hz.2] at h3
  have hn : n = 3 := by exact_mod_cast h3
  have h2 := ringKrullDim_stalk_subscheme_eq E.idealSheaf x' hz (j ⟨E, hE, hxE⟩) (hI ⟨E, hE, hxE⟩)
  rw [hn] at h2
  rw [Stacks.Chow.topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed
    (Stacks.Chow.fieldChowSituation ℂ) (fun _ _ ↦ rfl) (W ↘ Spec (.of ℂ)) ι x' hx', h2]
  rfl

end Threefold

/-! ### Primes of generizations -/

section Generization

/-- The stalk at `x` of the reduced ideal of the closure of a generization `ξ` of `x` is the prime
of `ξ` in `𝒪_{X,x}`. -/
private theorem stalk_vanishingIdeal_closure {X : Scheme.{0}} {ξ x : X} (h : ξ ⤳ x) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ξ})) x =
      MMP.Intersection.primeOfSpecializes h := by
  have e := MMP.Intersection.fromSpecStalk_primeOfSpecializes h
  have := Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk x
    ⟨MMP.Intersection.primeOfSpecializes h, inferInstance⟩
  rw [e] at this
  exact this

/-- Along a closed immersion `ι`, the prime of a generization `ξ ⤳ x` is the image of the prime of
`ι ξ ⤳ ι x`. -/
private theorem primeOfSpecializes_eq_map {Z X : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι]
    {ξ x : Z} (h : ξ ⤳ x) :
    MMP.Intersection.primeOfSpecializes h = Ideal.map (ι.stalkMap x).hom
      (MMP.Intersection.primeOfSpecializes (h.map ι.continuous)) := by
  have hcomap : Ideal.comap (ι.stalkMap x).hom (MMP.Intersection.primeOfSpecializes h) =
      MMP.Intersection.primeOfSpecializes (h.map ι.continuous) := by
    ext t
    simp only [Ideal.mem_comap, MMP.Intersection.primeOfSpecializes]
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, IsLocalRing.mem_maximalIdeal,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff (ι.stalkMap ξ).hom]
  rw [← hcomap, Ideal.map_comap_of_surjective _ (ι.stalkMap_surjective x)]

end Generization

/-! ### Double curves as prime divisors of the components -/

section DoubleCurve

variable {W Y : Scheme.{0}} [IsLocallyNoetherian W] [NoetherianSpace W] {f : W ⟶ Y}
  {D : Divisor W}

/-- **The double curve `σ ⊆ Eᵢ ∩ Eⱼ` is a prime divisor of `Eᵢ`.** Its ideal sheaf on `Eᵢ` is the
vanishing ideal of the preimage of the carrier, and the image of its generic point is the generic
point of the carrier. -/
private theorem exists_primeDivisor_doubleSurface (hD : DivisorWithCoeffs.IsSNC f D)
    (σ : DoubleSurface D) :
    ∃ P : MMP.Mori.PrimeDivisor σ.fst.idealSheaf.subscheme,
      P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier)) ∧
      IsGenericPoint (σ.fst.idealSheaf.subschemeι P.genericPoint) σ.carrier ∧
      P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {P.genericPoint}) := by
  obtain ⟨ζ, hζ, hst⟩ := exists_isGenericPoint_carrier hD σ
  set ι := σ.fst.idealSheaf.subschemeι with hι
  have hζE : ζ ∈ Set.range ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact (σ.carrier_subset hζ.mem).1
  obtain ⟨ζ', rfl⟩ := hζE
  obtain ⟨n, z, a, b, hz, hab, ha, hb⟩ := exists_pair_of_isSNC hD σ.fst_mem σ.snd_mem
    σ.fst_ne_snd (σ.carrier_subset hζ.mem).1 (σ.carrier_subset hζ.mem).2
  have hm := hst _ hζ.mem (specializes_refl _)
  rw [primeOfSpecializes_refl, ha, hb] at hm
  have hn := eq_two_of_maximalIdeal_eq hz hab hm
  have hdim := ringKrullDim_stalk_subscheme_eq σ.fst.idealSheaf ζ' hz a ha
  rw [hn, ringKrullDim_stalk_eq_coheight] at hdim
  have hco : Order.coheight ζ' = 1 := by exact_mod_cast hdim
  have hgen : MMP.Mori.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne ζ' hco) = ζ' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne ζ' hco
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne ζ' hco, ?_, ?_, ?_⟩
  · change Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ζ'}) = _
    congr 1
    ext1
    simp only [Closeds.coe_closure]
    rw [← hζ.def, ← Set.image_singleton,
      ← ι.isClosedEmbedding.isInducing.closure_eq_preimage_closure_image, closure_closure]
  · change IsGenericPoint (ι (AlgebraicGeometry.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne ζ' hco))) _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hζ
  · rw [hgen]; rfl

/-- The double curve `τ ⊆ E ∩ Eⱼ`, `E` its first component, as a prime divisor of `E`. -/
private noncomputable def curveOn (hD : DivisorWithCoeffs.IsSNC f D) (E : MMP.Mori.PrimeDivisor W)
    (τ : DoubleSurface D) (h : τ.fst = E) : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme :=
  h ▸ (exists_primeDivisor_doubleSurface hD τ).choose

private theorem curveOn_spec (hD : DivisorWithCoeffs.IsSNC f D) (E : MMP.Mori.PrimeDivisor W)
    (τ : DoubleSurface D) (h : τ.fst = E) :
    (curveOn hD E τ h).idealSheaf = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (E.idealSheaf.subschemeι.base ⁻¹' τ.carrier)) ∧
      IsGenericPoint (E.idealSheaf.subschemeι (curveOn hD E τ h).genericPoint) τ.carrier ∧
      (curveOn hD E τ h).idealSheaf = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure {(curveOn hD E τ h).genericPoint}) := by
  subst h
  exact (exists_primeDivisor_doubleSurface hD τ).choose_spec

private theorem curveOn_idealSheaf (hD : DivisorWithCoeffs.IsSNC f D) (E : MMP.Mori.PrimeDivisor W)
    (τ : DoubleSurface D) (h : τ.fst = E) :
    (curveOn hD E τ h).idealSheaf = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (E.idealSheaf.subschemeι.base ⁻¹' τ.carrier)) :=
  (curveOn_spec hD E τ h).1

private theorem isGenericPoint_curveOn (hD : DivisorWithCoeffs.IsSNC f D)
    (E : MMP.Mori.PrimeDivisor W) (τ : DoubleSurface D) (h : τ.fst = E) :
    IsGenericPoint (E.idealSheaf.subschemeι (curveOn hD E τ h).genericPoint) τ.carrier :=
  (curveOn_spec hD E τ h).2.1

/-- A point of `E` lies on the double curve `τ` exactly when its image lies on the carrier. -/
private theorem mem_support_curveOn_iff (hD : DivisorWithCoeffs.IsSNC f D)
    (E : MMP.Mori.PrimeDivisor W) (τ : DoubleSurface D) (h : τ.fst = E)
    (y : E.idealSheaf.subscheme) :
    y ∈ (curveOn hD E τ h).support ↔ E.idealSheaf.subschemeι y ∈ τ.carrier := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure,
    ← (isGenericPoint_curveOn hD E τ h).specializes_iff_mem,
    E.idealSheaf.subschemeι.isClosedEmbedding.isInducing.specializes_iff]

/-- At a point `y` of the double curve `τ ⊆ E ∩ E'`, the ideal of `τ` in `𝒪_{E,y}` is the image of
the ideal of `E'` in `𝒪_{W,y}`. -/
private theorem stalk_curveOn (hD : DivisorWithCoeffs.IsSNC f D) (E : MMP.Mori.PrimeDivisor W)
    (τ : DoubleSurface D) (h : τ.fst = E) {y : E.idealSheaf.subscheme}
    (hy : E.idealSheaf.subschemeι y ∈ τ.carrier) :
    IdealSheafData.stalk (curveOn hD E τ h).idealSheaf y =
      Ideal.map (E.idealSheaf.subschemeι.stalkMap y).hom
        (IdealSheafData.stalk τ.snd.idealSheaf (E.idealSheaf.subschemeι y)) := by
  set ι := E.idealSheaf.subschemeι
  have hgen := isGenericPoint_curveOn hD E τ h
  have hspW : ι (curveOn hD E τ h).genericPoint ⤳ ι y := hgen.specializes hy
  have hsp : (curveOn hD E τ h).genericPoint ⤳ y :=
    ι.isClosedEmbedding.isInducing.specializes_iff.mp hspW
  obtain ⟨ζ, hζ, hst⟩ := exists_isGenericPoint_carrier hD τ
  obtain rfl : ζ = ι (curveOn hD E τ h).genericPoint := hζ.eq hgen
  rw [(curveOn_spec hD E τ h).2.2, stalk_vanishingIdeal_closure hsp,
    primeOfSpecializes_eq_map ι hsp, hst _ hy, Ideal.map_sup]
  have hker : Ideal.map (ι.stalkMap y).hom (IdealSheafData.stalk τ.fst.idealSheaf (ι y)) = ⊥ := by
    subst h
    rw [Ideal.map_eq_bot_iff_le_ker, Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk]
  rw [hker, bot_sup_eq]

/-- On a Noetherian scheme a divisor has finitely many double surfaces. -/
private theorem finite_doubleSurface (D : Divisor W) : Finite (DoubleSurface D) := by
  classical
  set S : Set (Set W) := ⋃ E ∈ (D.support : Set (MMP.Mori.PrimeDivisor W)),
    ⋃ F ∈ (D.support : Set (MMP.Mori.PrimeDivisor W)),
      {S : Set W | ∃ σ : DoubleSurface D, σ.fst = E ∧ σ.snd = F ∧ σ.carrier = S}
  have hS : S.Finite := D.support.finite_toSet.biUnion fun E _ =>
    D.support.finite_toSet.biUnion fun F _ => DoubleSurface.finite_setOf_carrier E F
  have : Finite S := hS.to_subtype
  refine Finite.of_injective (β := D.support × D.support × S)
    (fun σ => (⟨σ.fst, σ.fst_mem⟩, ⟨σ.snd, σ.snd_mem⟩, ⟨σ.carrier, Set.mem_biUnion σ.fst_mem
      (Set.mem_biUnion σ.snd_mem ⟨σ, rfl, rfl, rfl⟩)⟩)) ?_
  intro σ τ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact DoubleSurface.ext h.1 h.2.1 h.2.2

/-- If at a point `y` of `E ∩ F` the maximal ideal is generated by the ideals of `E` and `F`, then
`y` is the generic point of the double surface of `(E, F)` through `y`. -/
private theorem isGenericPoint_connectedComponentIn (hD : DivisorWithCoeffs.IsSNC f D)
    {E F : MMP.Mori.PrimeDivisor W} (hE : E ∈ D.support) (hF : F ∈ D.support) (hne : E ≠ F)
    {y : W} (hy : y ∈ E.support ∩ F.support)
    (hm : IsLocalRing.maximalIdeal (W.presheaf.stalk y) =
      IdealSheafData.stalk E.idealSheaf y ⊔ IdealSheafData.stalk F.idealSheaf y) :
    IsGenericPoint y (connectedComponentIn (E.support ∩ F.support) y) := by
  obtain ⟨ζ, hζS, hζy, hp, hmax⟩ := exists_generization_of_isSNC hD hE hF hne hy
  have hζ : ζ = y := by
    have e := MMP.Intersection.fromSpecStalk_primeOfSpecializes hζy
    have e2 : (⟨MMP.Intersection.primeOfSpecializes hζy, inferInstance⟩ :
        PrimeSpectrum (W.presheaf.stalk y)) = IsLocalRing.closedPoint (W.presheaf.stalk y) :=
      PrimeSpectrum.ext (hp.trans hm.symm)
    rw [e2, Scheme.fromSpecStalk_closedPoint] at e
    exact e.symm
  subst hζ
  have hS : IsClosed (E.support ∩ F.support) :=
    E.idealSheaf.support.isClosed.inter F.idealSheaf.support.isClosed
  have hloc : ∀ y ∈ E.support ∩ F.support, ∃ ζ ∈ E.support ∩ F.support, ζ ⤳ y ∧
      ∀ ξ ∈ E.support ∩ F.support, ξ ⤳ y → ζ ⤳ ξ := by
    intro y hy
    obtain ⟨ζ, hζS, hζy, -, hmax⟩ := exists_generization_of_isSNC hD hE hF hne hy
    exact ⟨ζ, hζS, hζy, hmax⟩
  exact (connectedComponentIn_eq_closure_of_forall hS hloc hy hζS hζy hmax).symm

end DoubleCurve

/-! ### Transversality of double curves at triple points -/

section Transversal

/-- At a closed point of a scheme locally of finite type over `ℂ`, the residue field is `ℂ`. -/
private theorem finrank_quotient_maximalIdeal {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := MMP.Mori.stalkAlgebra sX x
    Module.finrank ℂ (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) = 1 := by
  letI := MMP.Mori.stalkAlgebra sX x
  haveI : Module.Finite ℂ (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX x hx
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)
    (K := IsLocalRing.ResidueField (X.presheaf.stalk x))
  exact Module.finrank_of_bijective_algebraMap hb

/-- The ideal `I_{C,q}` of the divisor `1 · C` is the stalk of the ideal sheaf of `C`. -/
private theorem localIdeal_single_one {Y : Scheme.{0}} (C : MMP.Mori.PrimeDivisor Y) (q : Y) :
    localIdeal q (Finsupp.single C 1) = IdealSheafData.stalk C.idealSheaf q := by
  rw [localIdeal, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.prod_singleton,
    Finsupp.single_eq_same]
  simp

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] [QuasiCompact (W ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 3 (W ↘ Spec (.of ℂ))] [IsLocallyNoetherian W] [NoetherianSpace W]
  {D : Divisor W}

/-- **Transversality.** At a triple point `y` of `E ∩ Eⱼ ∩ Eₖ`, the ideals of the double curves
`τ ⊆ E ∩ Eⱼ` and `τ' ⊆ E ∩ Eₖ` generate the maximal ideal of `𝒪_{E,y}`. -/
private theorem stalk_curveOn_sup_eq_maximalIdeal
    (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D) {E : MMP.Mori.PrimeDivisor W}
    (hE : E ∈ D.support) {τ τ' : DoubleSurface D} (h : τ.fst = E) (h' : τ'.fst = E)
    (hne : τ.snd ≠ τ'.snd) {y : E.idealSheaf.subscheme}
    (hy : E.idealSheaf.subschemeι y ∈ τ.carrier) (hy' : E.idealSheaf.subschemeι y ∈ τ'.carrier) :
    IdealSheafData.stalk (curveOn hD E τ h).idealSheaf y ⊔
        IdealSheafData.stalk (curveOn hD E τ' h').idealSheaf y =
      IsLocalRing.maximalIdeal (E.idealSheaf.subscheme.presheaf.stalk y) := by
  classical
  set ι := E.idealSheaf.subschemeι
  set x := ι y
  have hxE : x ∈ E.support := by
    change _ ∈ (E.idealSheaf.support : Set W)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  have hxj : x ∈ τ.snd.support := (τ.carrier_subset hy).2
  have hxk : x ∈ τ'.snd.support := (τ'.carrier_subset hy').2
  have hEj : E ≠ τ.snd := h ▸ τ.fst_ne_snd
  have hEk : E ≠ τ'.snd := h' ▸ τ'.fst_ne_snd
  have hcl := isClosed_singleton_of_mem_three hD hE τ.snd_mem τ'.snd_mem hEj hEk hne
    ⟨⟨hxE, hxj⟩, hxk⟩
  obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2 x
  set a := j ⟨E, hE, hxE⟩
  set b := j ⟨τ.snd, τ.snd_mem, hxj⟩
  set c := j ⟨τ'.snd, τ'.snd_mem, hxk⟩
  have hab : a ≠ b := fun e => hEj (congrArg Subtype.val (hj e))
  have hac : a ≠ c := fun e => hEk (congrArg Subtype.val (hj e))
  have hbc : b ≠ c := fun e => hne (congrArg Subtype.val (hj e))
  have h3 := ringKrullDim_stalk_eq_of_isClosed 3 x hcl
  rw [hz.2] at h3
  have hn : n = 3 := by exact_mod_cast h3
  have huniv : (Finset.univ : Finset (Fin n)) = {a, b, c} := by
    refine (Finset.eq_univ_of_card _ ?_).symm
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton, Fintype.card_fin, hn]
  have hrange : Set.range z = {z a, z b, z c} := by
    rw [← Set.image_univ, ← Finset.coe_univ, huniv]
    simp [Set.image_insert_eq]
  have hmW : IsLocalRing.maximalIdeal (W.presheaf.stalk x) =
      Ideal.span {z a} ⊔ Ideal.span {z b} ⊔ Ideal.span {z c} := by
    rw [← hz.1, hrange, Ideal.span_insert, Ideal.span_insert, sup_assoc]
  have hker : Ideal.map (ι.stalkMap y).hom (Ideal.span {z a}) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk]
    exact (hI ⟨E, hE, hxE⟩).ge
  rw [stalk_curveOn hD E τ h hy, stalk_curveOn hD E τ' h' hy', hI ⟨τ.snd, τ.snd_mem, hxj⟩,
    hI ⟨τ'.snd, τ'.snd_mem, hxk⟩,
    ← IsLocalRing.map_maximalIdeal_of_surjective _ (ι.stalkMap_surjective y), hmW,
    Ideal.map_sup, Ideal.map_sup, hker, bot_sup_eq]

/-- **The local intersection number at a triple point is one.** -/
private theorem localIntersectionNumber_curveOn_eq_one
    (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D) {E : MMP.Mori.PrimeDivisor W}
    (hE : E ∈ D.support) {τ τ' : DoubleSurface D} (h : τ.fst = E) (h' : τ'.fst = E)
    (hne : τ.snd ≠ τ'.snd) {y : E.idealSheaf.subscheme}
    (hy : E.idealSheaf.subschemeι y ∈ τ.carrier) (hy' : E.idealSheaf.subschemeι y ∈ τ'.carrier) :
    localIntersectionNumber (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)) y
      (Finsupp.single (curveOn hD E τ h) 1) (Finsupp.single (curveOn hD E τ' h') 1) = 1 := by
  have hEj : E ≠ τ.snd := h ▸ τ.fst_ne_snd
  have hEk : E ≠ τ'.snd := h' ▸ τ'.fst_ne_snd
  have hcl := isClosed_singleton_of_mem_three hD hE τ.snd_mem τ'.snd_mem hEj hEk hne
    ⟨⟨by
      change _ ∈ (E.idealSheaf.support : Set W)
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, rfl⟩, (τ.carrier_subset hy).2⟩,
      (τ'.carrier_subset hy').2⟩
  have hcly : IsClosed ({y} : Set E.idealSheaf.subscheme) := by
    have := hcl.preimage E.idealSheaf.subschemeι.continuous
    have e : E.idealSheaf.subschemeι ⁻¹' {E.idealSheaf.subschemeι y} = {y} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hw => E.idealSheaf.subschemeι.isClosedEmbedding.injective hw,
        fun hw => hw ▸ rfl⟩
    rwa [e] at this
  delta localIntersectionNumber
  rw [localIdeal_single_one, localIdeal_single_one,
    stalk_curveOn_sup_eq_maximalIdeal hD hE h h' hne hy hy']
  exact finrank_quotient_maximalIdeal _ y hcly

end Transversal

/-! ### Local equations of a prime divisor at a point -/

section LocalEquation

variable {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]

/-- On a normal scheme the image of a nonzero germ in a factor of `K(X)` is nonzero. -/
private theorem stalkToRationalFunctions_ne_zero' {x : X} {Z : irreducibleComponents X}
    (hx : x ∈ Z.1) {t : X.presheaf.stalk x} (ht : t ≠ 0) :
    (stalkToRationalFunctions X hx).hom t ≠ 0 :=
  fun h => ht (stalkToRationalFunctions_injective hx (h.trans (map_zero _).symm))

/-- The unit of `K(X)` which is a nonzero germ `t ∈ 𝒪_{X,x}` on the component `Z ∋ x` and `1` on
the other components. -/
private noncomputable def componentUnit {x : X} {Z : irreducibleComponents X} (hx : x ∈ Z.1)
    (t : X.presheaf.stalk x) (ht : t ≠ 0) : (RationalFunctions X)ˣ := by
  classical
  exact (RationalFunctions.unitsEquiv X).symm (Pi.mulSingle Z (Units.mkOfMulEqOne _ _
    (Classical.choose_spec ((RationalFunctions.isField_stalk X Z).mul_inv_cancel
      (stalkToRationalFunctions_ne_zero' hx ht)))))

private theorem componentUnit_apply_self {x : X} {Z : irreducibleComponents X} (hx : x ∈ Z.1)
    (t : X.presheaf.stalk x) (ht : t ≠ 0) :
    (componentUnit hx t ht : RationalFunctions X) Z = (stalkToRationalFunctions X hx).hom t := by
  classical
  unfold componentUnit
  rw [show ∀ (f : ∀ Z' : irreducibleComponents X, (X.presheaf.stalk (componentGenericPoint X Z'))ˣ),
      (((RationalFunctions.unitsEquiv X).symm f : (RationalFunctions X)ˣ) : RationalFunctions X) Z =
        ((f Z : (X.presheaf.stalk (componentGenericPoint X Z))ˣ) :
          X.presheaf.stalk (componentGenericPoint X Z)) from fun f => rfl]
  rw [Pi.mulSingle_eq_same]
  rfl

/-- The specialization of a germ to the generic point of a prime divisor through `x` is nonzero
on a normal scheme. -/
private theorem stalkSpecializes_ne_zero' {y x : X} (h : y ⤳ x) {t : X.presheaf.stalk x}
    (ht : t ≠ 0) : (X.presheaf.stalkSpecializes h).hom t ≠ 0 := by
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have := MMP.Intersection.isLocalization_stalkSpecializes h
  have hinj := IsLocalization.injective (M := ((IsLocalRing.maximalIdeal
    (X.presheaf.stalk y)).comap (X.presheaf.stalkSpecializes h).hom).primeCompl)
    (X.presheaf.stalk y) (Ideal.primeCompl_le_nonZeroDivisors _)
  rw [Ne, ← map_zero (X.presheaf.stalkSpecializes h).hom]
  exact fun e => ht (hinj e)

/-- If `t ∈ 𝒪_{X,x}` generates the prime of a prime divisor `G` through `x`, then `t`, as a unit of
`K(X)` on the component through `x`, has order one along `G`. -/
private theorem ord_componentUnit_eq_one {x : X} {Z : irreducibleComponents X} (hx : x ∈ Z.1)
    {t : X.presheaf.stalk x} (ht : t ≠ 0) (G : MMP.Mori.PrimeDivisor X)
    (hsp : G.genericPoint ⤳ x)
    (hq : Ideal.span {t} = MMP.Intersection.primeOfSpecializes hsp) :
    G.ord (componentUnit hx t ht) = 1 := by
  have hxG : x ∈ G.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hsp
  obtain rfl : G.component = Z :=
    eq_of_mem_irreducibleComponents (G.support_subset_component hxG) hx
  have := G.isDiscreteValuationRing_localRing
  let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have := MMP.Intersection.isLocalization_stalkSpecializes hsp
  have hmax : IsLocalRing.maximalIdeal G.localRing =
      Ideal.span {(X.presheaf.stalkSpecializes hsp).hom t} := by
    have h := IsLocalization.AtPrime.map_eq_maximalIdeal
      (MMP.Intersection.primeOfSpecializes hsp) G.localRing
    rw [← hq, Ideal.map_span, Set.image_singleton] at h
    exact h.symm
  refine G.ord_eq_one_of_irreducible
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (stalkSpecializes_ne_zero' hsp ht) hmax) ?_
  rw [G.toComponent_stalkSpecializes hsp hx, componentUnit_apply_self]

/-- If `t ∈ 𝒪_{X,x}` lies outside the prime of a prime divisor `G` through `x`, then `t`, as a unit
of `K(X)` on the component through `x`, has order zero along `G`. -/
private theorem ord_componentUnit_eq_zero {x : X} {Z : irreducibleComponents X} (hx : x ∈ Z.1)
    {t : X.presheaf.stalk x} (ht : t ≠ 0) (G : MMP.Mori.PrimeDivisor X)
    (hsp : G.genericPoint ⤳ x) (htq : t ∉ MMP.Intersection.primeOfSpecializes hsp) :
    G.ord (componentUnit hx t ht) = 0 := by
  have hxG : x ∈ G.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hsp
  obtain rfl : G.component = Z :=
    eq_of_mem_irreducibleComponents (G.support_subset_component hxG) hx
  have hu : IsUnit ((X.presheaf.stalkSpecializes hsp).hom t) := by
    by_contra h
    exact htq ((IsLocalRing.mem_maximalIdeal _).mpr h)
  refine G.ord_eq_zero_of_isUnit hu ?_
  rw [G.toComponent_stalkSpecializes hsp hx, componentUnit_apply_self]

/-- The stalk at `y` of the ideal of a prime divisor `F` through `y` is the prime of the generic
point of `F` in `𝒪_{X,y}`. -/
private theorem stalk_primeDivisor (F : MMP.Mori.PrimeDivisor X) {y : X}
    (hsp : F.genericPoint ⤳ y) :
    IdealSheafData.stalk F.idealSheaf y = MMP.Intersection.primeOfSpecializes hsp := by
  haveI := F.integral
  have hT : F.idealSheaf.support = Closeds.closure {F.genericPoint} := Closeds.ext (by
    rw [Closeds.coe_closure]; exact AlgebraicGeometry.PrimeDivisor.support_eq_closure F)
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme F.idealSheaf _ hT]
  exact stalk_vanishingIdeal_closure hsp

/-- **A local equation of a prime divisor near a point.** If `φ` is a local equation of `F` on
`U ∋ y` and `t ∈ 𝒪_{X,y}` generates the prime of `F`, then the component of `φ` through `y` is
`u t` for a unit `u` of `𝒪_{X,y}`. -/
private theorem exists_unit_mul_eq_of_isLocalEquation {F : MMP.Mori.PrimeDivisor X}
    {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : MMP.Mori.Divisor.IsLocalEquation (Finsupp.single F 1 : Divisor X) U φ) {y : X} (hyU : y ∈ U)
    (hsp : F.genericPoint ⤳ y) {t : X.presheaf.stalk y}
    (hq : Ideal.span {t} = MMP.Intersection.primeOfSpecializes hsp) :
    ∃ u : (X.presheaf.stalk y)ˣ,
      (stalkToRationalFunctions X (mem_pointComponent y)).hom (u * t) =
        (φ : RationalFunctions X) (pointComponent y) := by
  classical
  set Z := pointComponent y
  have hyZ : y ∈ Z.1 := mem_pointComponent y
  have ht : t ≠ 0 := by
    rintro rfl
    have hbot : MMP.Intersection.primeOfSpecializes hsp = ⊥ := by
      rw [← hq, Ideal.span_singleton_eq_bot]
    have e1 := MMP.Intersection.fromSpecStalk_primeOfSpecializes hsp
    have e2 : X.fromSpecStalk y ⟨MMP.Intersection.primeOfSpecializes hsp, inferInstance⟩ =
        X.fromSpecStalk y ⟨⊥, Ideal.isPrime_bot⟩ := congrArg _ (PrimeSpectrum.ext hbot)
    rw [e2, ← componentGenericPoint_eq_fromSpecStalk hyZ] at e1
    have hf : IsField (X.presheaf.stalk F.genericPoint) :=
      e1 ▸ RationalFunctions.isField_stalk X Z
    have h0 := ringKrullDim_eq_zero_of_isField hf
    rw [ringKrullDim_stalk_eq_coheight, F.coheight_genericPoint] at h0
    exact absurd h0 (by decide)
  set τ := componentUnit hyZ t ht
  have hψ : ∀ G : MMP.Mori.PrimeDivisor X, y ∈ G.support → G.ord (φ * τ⁻¹) = 0 := by
    intro G hyG
    have hspG : G.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hyG
    rw [MMP.Mori.PrimeDivisor.ord_mul, MMP.Mori.PrimeDivisor.ord_inv, ← hφ G ⟨y, hyG, hyU⟩]
    by_cases hGF : G = F
    · subst hGF
      rw [DivisorWithCoeffs.coeff_single_self, ord_componentUnit_eq_one hyZ ht G hspG hq]
      simp
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hGF),
        ord_componentUnit_eq_zero hyZ ht G hspG ?_]
      · simp
      intro htG
      have hle : MMP.Intersection.primeOfSpecializes hsp ≤
          MMP.Intersection.primeOfSpecializes hspG := by
        rw [← hq, Ideal.span_le, Set.singleton_subset_iff]; exact htG
      have h1 := MMP.Intersection.specializes_of_primeOfSpecializes_le hsp hspG hle
      have hmem : G.genericPoint ∈ F.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact specializes_iff_mem_closure.mp h1
      exact hGF (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support F G hmem).symm
  obtain ⟨u, hu⟩ := exists_unit_stalk_of_forall_ord_eq_zero hyZ (φ * τ⁻¹) hψ
  refine ⟨u, ?_⟩
  rw [map_mul, hu, ← componentUnit_apply_self hyZ t ht]
  change ((φ * τ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z *
    (τ : RationalFunctions X) Z = _
  rw [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel_right]

/-- The image of the generic point of the component of a prime divisor `P` of a closed subscheme
lies on the irreducible component of the ambient scheme through the image of the generic point of
`P`. -/
private theorem map_componentGenericPoint_mem_pointComponent (I : X.IdealSheafData)
    (P : MMP.Mori.PrimeDivisor I.subscheme) :
    I.subschemeι (componentGenericPoint I.subscheme P.component) ∈
      (pointComponent (I.subschemeι P.genericPoint)).1 := by
  have h1 := (P.specializes_genericPoint.map I.subschemeι.continuous).mem_closed
    (isClosed_of_mem_irreducibleComponents _ (pointComponent _).2) (mem_pointComponent _)
  exact eq_of_mem_irreducibleComponents h1 (mem_pointComponent _) ▸ mem_pointComponent _

/-- **The order of a pulled-back local equation along a transversal prime divisor.** Let
`ι : V ⟶ X` be a closed subscheme, `P` a prime divisor of `V` whose generic point maps to
`y ∈ F`, and `t ∈ 𝒪_{X,y}` a generator of the prime of `F` restricting to a uniformizer of
`𝒪_{V,P}`. Then the pull-back of a local equation of `F` has order one along `P`. -/
private theorem ordUnit_pullbackComponent_eq_one (I : X.IdealSheafData)
    [IsLocallyNoetherian I.subscheme] [IsNormal I.subscheme] {F : MMP.Mori.PrimeDivisor X}
    (hB : ∀ Z : irreducibleComponents I.subscheme,
      I.subschemeι (componentGenericPoint I.subscheme Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single F 1 : Divisor X))
    {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : MMP.Mori.Divisor.IsLocalEquation (Finsupp.single F 1 : Divisor X) U φ)
    (P : MMP.Mori.PrimeDivisor I.subscheme) (hP : (P.support ∩ I.subschemeι ⁻¹ᵁ U).Nonempty)
    (hsp : F.genericPoint ⤳ I.subschemeι P.genericPoint)
    {t : X.presheaf.stalk (I.subschemeι P.genericPoint)}
    (hq : Ideal.span {t} = MMP.Intersection.primeOfSpecializes hsp)
    (hirr : Irreducible ((I.subschemeι.stalkMap P.genericPoint).hom t)) :
    P.ordUnit (pullbackComponent I.subschemeι hB hφ P.component
      (P.map_componentGenericPoint_mem I.subschemeι hP)) = 1 := by
  have hyU : I.subschemeι P.genericPoint ∈ U := (P.genericPoint_mem_iff (I.subschemeι ⁻¹ᵁ U)).mpr hP
  obtain ⟨u, hu⟩ := exists_unit_mul_eq_of_isLocalEquation hφ hyU hsp hq
  have hy₀ : I.subschemeι (componentGenericPoint I.subscheme P.component) ⤳
      I.subschemeι P.genericPoint := P.specializes_genericPoint.map I.subschemeι.continuous
  have hW' := map_componentGenericPoint_mem_pointComponent I P
  have ht' : IsUnit ((X.presheaf.stalkSpecializes hy₀).hom t) := by
    by_contra hnu
    have htq : t ∈ MMP.Intersection.primeOfSpecializes hy₀ :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hle : MMP.Intersection.primeOfSpecializes hsp ≤
        MMP.Intersection.primeOfSpecializes hy₀ := by
      rw [← hq, Ideal.span_le, Set.singleton_subset_iff]; exact htq
    have h1 := MMP.Intersection.specializes_of_primeOfSpecializes_le hsp hy₀ hle
    have hmem : I.subschemeι (componentGenericPoint I.subscheme P.component) ∈ F.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact specializes_iff_mem_closure.mp h1
    refine hB P.component (DivisorWithCoeffs.support_subset_supp ?_ hmem)
    rw [DivisorWithCoeffs.coeff_single_self]; exact one_ne_zero
  set a := ((u.isUnit.map (X.presheaf.stalkSpecializes hy₀).hom).mul ht').unit with ha_def
  have ha : (stalkToRationalFunctions X hW').hom a =
      (φ : RationalFunctions X) (pointComponent (I.subschemeι P.genericPoint)) := by
    rw [← hu]
    change (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes hy₀).hom u *
      (X.presheaf.stalkSpecializes hy₀).hom t) =
        (X.presheaf.stalkSpecializes _).hom ((u : X.presheaf.stalk _) * t)
    rw [← map_mul, ← ConcreteCategory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  rw [pullbackComponent_eq hB hφ _ hW' a ha]
  have hv := P.valuation_eq_exp_ordUnit
    (Units.map (I.subschemeι.stalkMap (componentGenericPoint I.subscheme P.component)).hom.toMonoidHom a)
  have hval : ((Units.map (I.subschemeι.stalkMap
      (componentGenericPoint I.subscheme P.component)).hom.toMonoidHom a :
        (I.subscheme.presheaf.stalk (componentGenericPoint I.subscheme P.component))ˣ) :
      I.subscheme.presheaf.stalk (componentGenericPoint I.subscheme P.component)) =
      P.toComponent.hom ((I.subschemeι.stalkMap P.genericPoint).hom u *
        (I.subschemeι.stalkMap P.genericPoint).hom t) := by
    change (I.subschemeι.stalkMap _).hom ((X.presheaf.stalkSpecializes hy₀).hom u *
      (X.presheaf.stalkSpecializes hy₀).hom t) = _
    rw [← map_mul, ← map_mul, I.subschemeι.stalkSpecializes_stalkMap_apply]
    rfl
  rw [hval, map_mul, map_mul, P.valuation_toComponent_of_isUnit (u.isUnit.map _),
    P.valuation_toComponent_of_irreducible hirr, one_mul] at hv
  exact (WithZero.exp_injective hv).symm

/-- **The order of a pulled-back local equation off the divisor.** If the generic point of a prime
divisor `P` of a closed subscheme maps outside `F`, the pull-back of a local equation of `F` has
order zero along `P`. -/
private theorem ordUnit_pullbackComponent_eq_zero (I : X.IdealSheafData)
    [IsLocallyNoetherian I.subscheme] [IsNormal I.subscheme] {F : MMP.Mori.PrimeDivisor X}
    (hB : ∀ Z : irreducibleComponents I.subscheme,
      I.subschemeι (componentGenericPoint I.subscheme Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single F 1 : Divisor X))
    {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : MMP.Mori.Divisor.IsLocalEquation (Finsupp.single F 1 : Divisor X) U φ)
    (P : MMP.Mori.PrimeDivisor I.subscheme) (hP : (P.support ∩ I.subschemeι ⁻¹ᵁ U).Nonempty)
    (hyF : I.subschemeι P.genericPoint ∉ DivisorWithCoeffs.supp (Finsupp.single F 1 : Divisor X)) :
    P.ordUnit (pullbackComponent I.subschemeι hB hφ P.component
      (P.map_componentGenericPoint_mem I.subschemeι hP)) = 0 := by
  have hyU : I.subschemeι P.genericPoint ∈ U := (P.genericPoint_mem_iff (I.subschemeι ⁻¹ᵁ U)).mpr hP
  obtain ⟨u, hu⟩ := hφ.exists_unit_stalk hyU hyF (mem_pointComponent _)
  have hy₀ : I.subschemeι (componentGenericPoint I.subscheme P.component) ⤳
      I.subschemeι P.genericPoint := P.specializes_genericPoint.map I.subschemeι.continuous
  have hW' := map_componentGenericPoint_mem_pointComponent I P
  set a := (u.isUnit.map (X.presheaf.stalkSpecializes hy₀).hom).unit with ha_def
  have ha : (stalkToRationalFunctions X hW').hom a =
      (φ : RationalFunctions X) (pointComponent (I.subschemeι P.genericPoint)) := by
    rw [← hu]
    change (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes hy₀).hom u) =
      (X.presheaf.stalkSpecializes _).hom
        (u : X.presheaf.stalk (I.subschemeι P.genericPoint))
    rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  rw [pullbackComponent_eq hB hφ _ hW' a ha]
  refine P.ordUnit_eq_zero_of_isUnit (a := (I.subschemeι.stalkMap P.genericPoint).hom
    (u : X.presheaf.stalk (I.subschemeι P.genericPoint))) (u.isUnit.map _) ?_
  change _ = (I.subschemeι.stalkMap _).hom ((X.presheaf.stalkSpecializes hy₀).hom
    (u : X.presheaf.stalk (I.subschemeι P.genericPoint)))
  rw [I.subschemeι.stalkSpecializes_stalkMap_apply]
  rfl

end LocalEquation

/-! ### Restriction of a component to another component -/

section Restriction

variable {W Y : Scheme.{0}} [IsLocallyNoetherian W] [NoetherianSpace W] [IsNormal W]
  {f : W ⟶ Y} {D : Divisor W}

/-- The generic point of a component `E` lies on no other component `F`. -/
private theorem forall_notMem_supp_single {E F : MMP.Mori.PrimeDivisor W} (hne : E ≠ F) :
    ∀ Z : irreducibleComponents E.idealSheaf.subscheme,
      E.idealSheaf.subschemeι (componentGenericPoint E.idealSheaf.subscheme Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single F 1 : Divisor W) := by
  haveI := E.integral
  intro Z hZ
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint Z] at hZ
  exact hne (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support F E
    (DivisorWithCoeffs.supp_single_le F 1 hZ)).symm

open Classical in
/-- **The restriction of a component to another one.** For distinct components `E`, `F` of an snc
divisor, the pull-back of `F` to `E` is the sum of the double curves of `(E, F)`, each with
coefficient one. -/
private theorem isPullback_single_component (hD : DivisorWithCoeffs.IsSNC f D)
    [Fintype (DoubleSurface D)] {E F : MMP.Mori.PrimeDivisor W} (hE : E ∈ D.support)
    (hF : F ∈ D.support) (hne : E ≠ F) [IsLocallyNoetherian E.idealSheaf.subscheme]
    [IsNormal E.idealSheaf.subscheme] (hFc : MMP.Mori.Divisor.IsCartier (Finsupp.single F 1 : Divisor W)) :
    MMP.Mori.Divisor.IsPullback E.idealSheaf.subschemeι (Finsupp.single F 1 : Divisor W)
      (forall_notMem_supp_single hne)
      (∑ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = F},
        Finsupp.single (curveOn hD E τ.1 τ.2.1) 1) := by
  haveI := E.integral
  refine MMP.Mori.Divisor.IsPullback.of_forall_exists fun P => ?_
  obtain ⟨U, hyU, φ, hφ⟩ := hFc (E.idealSheaf.subschemeι P.genericPoint)
  have hηP : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hP : (P.support ∩ E.idealSheaf.subschemeι ⁻¹ᵁ U).Nonempty := ⟨P.genericPoint, hηP, hyU⟩
  refine ⟨U, φ, hφ, hP, ?_⟩
  have hcoeff : DivisorWithCoeffs.coeff (∑ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = F},
      Finsupp.single (curveOn hD E τ.1 τ.2.1) (1 : ℤ)) P =
      ∑ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = F},
        if curveOn hD E τ.1 τ.2.1 = P then 1 else 0 := by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    exact Finset.sum_congr rfl fun τ _ => Finsupp.single_apply
  rw [hcoeff]
  have hyE : E.idealSheaf.subschemeι P.genericPoint ∈ E.support := by
    change _ ∈ (E.idealSheaf.support : Set W)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩
  -- a double curve equal to `P` has generic point `ι η_P`
  have hgen : ∀ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = F},
      curveOn hD E τ.1 τ.2.1 = P →
        IsGenericPoint (E.idealSheaf.subschemeι P.genericPoint) τ.1.carrier := by
    rintro τ rfl
    exact isGenericPoint_curveOn hD E τ.1 τ.2.1
  by_cases hyF : E.idealSheaf.subschemeι P.genericPoint ∈ F.support
  · -- `P` is a double curve of `(E, F)`
    obtain ⟨n, z, a, b, hz, hab, ha, hb⟩ := exists_pair_of_isSNC hD hE hF hne hyE hyF
    have h1 := ringKrullDim_stalk_subscheme_eq E.idealSheaf P.genericPoint hz a ha
    rw [ringKrullDim_stalk_eq_coheight, P.coheight_genericPoint] at h1
    have hn1 : n - 1 = 1 := by
      have h2 : (((n - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := h1.symm
      exact_mod_cast WithBot.coe_inj.mp h2
    have hn : n = 2 := by
      have := a.isLt; have := b.isLt
      have : a.val ≠ b.val := fun e => hab (Fin.ext e)
      omega
    have huniv : (Finset.univ : Finset (Fin n)) = {a, b} := by
      refine (Finset.eq_univ_of_card _ ?_).symm
      rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton, Fintype.card_fin,
        hn]
    have hrange : Set.range z = {z a, z b} := by
      rw [← Set.image_univ, ← Finset.coe_univ, huniv]
      simp [Set.image_insert_eq]
    have hm : IsLocalRing.maximalIdeal (W.presheaf.stalk (E.idealSheaf.subschemeι P.genericPoint)) =
        IdealSheafData.stalk E.idealSheaf (E.idealSheaf.subschemeι P.genericPoint) ⊔
          IdealSheafData.stalk F.idealSheaf (E.idealSheaf.subschemeι P.genericPoint) := by
      rw [← hz.1, hrange, ha, hb, Ideal.span_insert]
    have hspF : F.genericPoint ⤳ E.idealSheaf.subschemeι P.genericPoint := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hyF
    have hq : Ideal.span {z b} = MMP.Intersection.primeOfSpecializes hspF :=
      hb.symm.trans (stalk_primeDivisor F hspF)
    -- the restriction of `z_b` is a uniformizer along `P`
    have hirr : Irreducible ((E.idealSheaf.subschemeι.stalkMap P.genericPoint).hom (z b)) := by
      have := P.isDiscreteValuationRing_localRing
      have hker : Ideal.map (E.idealSheaf.subschemeι.stalkMap P.genericPoint).hom
          (Ideal.span {z a}) = ⊥ := by
        rw [Ideal.map_eq_bot_iff_le_ker, Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk]
        exact ha.ge
      have hmax : IsLocalRing.maximalIdeal P.localRing =
          Ideal.span {(E.idealSheaf.subschemeι.stalkMap P.genericPoint).hom (z b)} := by
        rw [← IsLocalRing.map_maximalIdeal_of_surjective _
          (E.idealSheaf.subschemeι.stalkMap_surjective P.genericPoint), hm, ha, hb,
          Ideal.map_sup, hker, bot_sup_eq, Ideal.map_span, Set.image_singleton]
      have hne0 : (E.idealSheaf.subschemeι.stalkMap P.genericPoint).hom (z b) ≠ 0 := by
        intro h0
        rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hmax
        have hfield : IsField P.localRing := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax
        have h0' := ringKrullDim_eq_zero_of_isField hfield
        rw [ringKrullDim_stalk_eq_coheight, P.coheight_genericPoint] at h0'
        exact absurd h0' (by decide)
      exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne0 hmax
    rw [ordUnit_pullbackComponent_eq_one E.idealSheaf (forall_notMem_supp_single hne) hφ P hP
      hspF hq hirr]
    -- the unique double curve of `(E, F)` equal to `P`
    have hyEF : E.idealSheaf.subschemeι P.genericPoint ∈ E.support ∩ F.support := ⟨hyE, hyF⟩
    set τ₀ := DoubleSurface.through hE hF hne (Set.singleton_nonempty _)
      (Set.singleton_subset_iff.mpr hyEF)
    have hτ₀ : IsGenericPoint (E.idealSheaf.subschemeι P.genericPoint) τ₀.carrier := by
      have hsome : (Set.singleton_nonempty (E.idealSheaf.subschemeι P.genericPoint)).some =
          E.idealSheaf.subschemeι P.genericPoint :=
        (Set.singleton_nonempty _).some_mem
      change IsGenericPoint _ (connectedComponentIn (E.support ∩ F.support) _)
      rw [hsome]
      exact isGenericPoint_connectedComponentIn hD hE hF hne hyEF hm
    have hP₀ : curveOn hD E τ₀ rfl = P := by
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      exact E.idealSheaf.subschemeι.isClosedEmbedding.injective
        ((isGenericPoint_curveOn hD E τ₀ rfl).eq hτ₀)
    rw [Finset.sum_eq_single ⟨τ₀, rfl, rfl⟩, if_pos hP₀]
    · intro τ _ hτ
      rw [if_neg]
      intro hτP
      apply hτ
      apply Subtype.ext
      refine DoubleSurface.eq_through hE hF hne (Set.singleton_nonempty _)
        (Set.singleton_subset_iff.mpr hyEF) isPreconnected_singleton τ.1 τ.2.1 τ.2.2 ?_
      exact ⟨_, (hgen τ hτP).mem, rfl⟩
    · exact fun h => absurd (Finset.mem_univ _) h
  · -- `P` is not a double curve of `(E, F)`
    have hyF' : E.idealSheaf.subschemeι P.genericPoint ∉
        DivisorWithCoeffs.supp (Finsupp.single F 1 : Divisor W) :=
      fun h => hyF (DivisorWithCoeffs.supp_single_le F 1 h)
    rw [ordUnit_pullbackComponent_eq_zero E.idealSheaf (forall_notMem_supp_single hne) hφ P hP hyF']
    refine Finset.sum_eq_zero fun τ _ => if_neg fun hτP => hyF ?_
    exact (τ.1.carrier_subset (hgen τ hτP).mem).2 |> fun h => τ.2.2 ▸ h

end Restriction

/-! ### Degrees and intersection numbers of sums -/

section Degrees

variable {k : Type} [Field k] {X C : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] (i : C ⟶ X) [IsProper (i ≫ sX)]
  (hdim : topologicalKrullDim C ≤ 1)

/-- The degree along a curve of `∑_{j ∈ s} Lⱼ` is `∑_{j ∈ s} deg_C Lⱼ`. -/
private theorem degreeOn_finset_sum {ι : Type*} (s : Finset ι) (L : ι → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (h : (∑ j ∈ s, L j).IsCartier) :
    (∑ j ∈ s, L j).degreeOn k sX i hdim h = ∑ j ∈ s, (L j).degreeOn k sX i hdim (hL j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Divisor.degreeOn_congr Finset.sum_empty h Divisor.isCartier_zero, Divisor.degreeOn_zero',
      Finset.sum_empty]
  | insert a s ha ih =>
    have hs : (∑ j ∈ s, L j).IsCartier :=
      Finset.sum_induction _ Divisor.IsCartier (fun _ _ h h' ↦ h.add h')
        Divisor.isCartier_zero fun j _ ↦ hL j
    rw [Divisor.degreeOn_congr (Finset.sum_insert ha) h ((hL a).add hs),
      Divisor.degreeOn_add k sX i hdim _ _ (hL a) hs, ih hs, Finset.sum_insert ha]

/-- On a scheme on which every `ℚ`-divisor is `ℚ`-Cartier, the intersection number of
`∑ⱼ qⱼ Lⱼ`, the `Lⱼ` Cartier, is `∑ⱼ qⱼ deg_C Lⱼ`. -/
private theorem intersectionNumber_finset_sum_smul (hQ : ∀ G : QDivisor X, G.IsQCartier)
    {ι : Type*} (s : Finset ι) (q : ι → ℚ) (L : ι → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (h : (∑ j ∈ s, q j • Divisor.toQDivisor (L j)).IsQCartier) :
    (∑ j ∈ s, q j • Divisor.toQDivisor (L j)).intersectionNumber k sX i hdim h =
      ∑ j ∈ s, q j * (L j).degreeOn k sX i hdim (hL j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ (QDivisor.isQCartier_toQDivisor
      Divisor.isCartier_zero) (by simp), QDivisor.intersectionNumber_toQDivisor k sX i hdim _
      Divisor.isCartier_zero, Divisor.degreeOn_zero']
    simp
  | insert a s ha ih =>
    rw [MMP.Fourfold.intersectionNumber_congr sX i hdim h ((hQ _).add (hQ _))
        (Finset.sum_insert ha),
      QDivisor.intersectionNumber_add' k sX i hdim _ _ (hQ _) (hQ _), ih (hQ _),
      MMP.Fourfold.intersectionNumber_smul sX i hdim _ (QDivisor.isQCartier_toQDivisor (hL a))
        (q a) (hQ _),
      QDivisor.intersectionNumber_toQDivisor k sX i hdim _ (hL a), Finset.sum_insert ha]

/-- **Degrees along curves with the same image.** Two closed immersions of reduced schemes with the
same image in `X` give the same degree to every invertible sheaf on `X`. -/
private theorem degreeOn_eq_of_range_eq {k : Type} [Field k] {X C C' : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) (i' : C' ⟶ X) [IsClosedImmersion i]
    [IsClosedImmersion i'] [IsReduced C] [IsReduced C'] [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)]
    (h : Set.range i = Set.range i') (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    MMP.Mori.degreeOn k sX i hdim L = MMP.Mori.degreeOn k sX i' hdim' L := by
  have hker : i'.ker = i.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      h]
  haveI := IsClosedImmersion.isIso_lift i' i hker
  exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim'
    (asIso (IsClosedImmersion.lift i' i hker.le)) (IsClosedImmersion.lift_fac _ _ _) L

end Degrees

/-! ### Degrees of components along double curves -/

section ComponentDegrees

variable {W Y : Scheme.{0}} [IsLocallyNoetherian W] [NoetherianSpace W] [IsNormal W]
  {f : W ⟶ Y} {D : Divisor W}

open Classical in
/-- **The degree of a component along a curve on another component.** For distinct components
`E`, `F` and a curve `C ⟶ E`, `deg_C 𝒪_W(F) = ∑_{τ ⊆ E ∩ F} deg_C 𝒪_E(τ)`. -/
private theorem degreeOn_single_eq_sum_curveOn (hD : DivisorWithCoeffs.IsSNC f D)
    [Fintype (DoubleSurface D)] {k : Type} [Field k] (sW : W ⟶ Spec (.of k)) [QuasiCompact sW]
    {E F : MMP.Mori.PrimeDivisor W} (hE : E ∈ D.support) (hF : F ∈ D.support) (hne : E ≠ F)
    [IsLocallyNoetherian E.idealSheaf.subscheme] [IsNormal E.idealSheaf.subscheme]
    [QuasiCompact (E.idealSheaf.subschemeι ≫ sW)]
    (hFc : MMP.Mori.Divisor.IsCartier (Finsupp.single F 1 : Divisor W))
    (hc : ∀ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = F},
      MMP.Mori.Divisor.IsCartier (Finsupp.single (curveOn hD E τ.1 τ.2.1) 1 :
        Divisor E.idealSheaf.subscheme))
    {C : Scheme.{0}} (i : C ⟶ E.idealSheaf.subscheme) [IsProper ((i ≫ E.idealSheaf.subschemeι) ≫ sW)]
    [IsProper (i ≫ E.idealSheaf.subschemeι ≫ sW)] (hdim : topologicalKrullDim C ≤ 1) :
    MMP.Mori.Divisor.degreeOn k sW (i ≫ E.idealSheaf.subschemeι) hdim
        (Finsupp.single F 1 : Divisor W) hFc =
      ∑ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = F},
        MMP.Mori.Divisor.degreeOn k (E.idealSheaf.subschemeι ≫ sW) i hdim
          (Finsupp.single (curveOn hD E τ.1 τ.2.1) 1) (hc τ) := by
  haveI := E.integral
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : CompactSpace E.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (E.idealSheaf.subschemeι ≫ sW)
  have hP := isPullback_single_component hD hE hF hne hFc
  have hB'c : MMP.Mori.Divisor.IsCartier (∑ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = F},
      (Finsupp.single (curveOn hD E τ.1 τ.2.1) 1 : Divisor E.idealSheaf.subscheme)) :=
    Finset.sum_induction _ MMP.Mori.Divisor.IsCartier (fun _ _ h h' ↦ h.add h')
      MMP.Mori.Divisor.isCartier_zero fun τ _ ↦ hc τ
  rw [← degreeOn_finset_sum (E.idealSheaf.subschemeι ≫ sW) i hdim Finset.univ _ hc hB'c]
  haveI := hFc.isInvertibleModule_divisorialSheaf
  haveI := hB'c.isInvertibleModule_divisorialSheaf
  change MMP.Mori.degreeOn k sW (i ≫ E.idealSheaf.subschemeι) hdim
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single F 1 : Divisor W)) =
    MMP.Mori.degreeOn k (E.idealSheaf.subschemeι ≫ sW) i hdim
      (MMP.Mori.Divisor.divisorialSheaf (∑ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = F},
        (Finsupp.single (curveOn hD E τ.1 τ.2.1) 1 : Divisor E.idealSheaf.subscheme)))
  rw [MMP.Threefold.Resolution.degreeOn_comp k sW E.idealSheaf.subschemeι i hdim]
  exact (MMP.Mori.degreeOn_eq_of_iso k (E.idealSheaf.subschemeι ≫ sW) i hdim
    (MMP.Mori.Divisor.IsPullback.divisorialSheafIso (hBc := hFc) hP)).symm

end ComponentDegrees

/-! ### Double curves on a component, and the divisor `Zᵢ` -/

section CurveDivisor

variable {W Y : Scheme.{0}} [IsLocallyNoetherian W] [NoetherianSpace W] {f : W ⟶ Y}
  {D : Divisor W}

open Classical in
/-- The double curve `τ` as a divisor on the component `E`, zero unless `E` is the first component
of `τ`. -/
private noncomputable def curveDivisor (hD : DivisorWithCoeffs.IsSNC f D)
    (E : MMP.Mori.PrimeDivisor W) (τ : DoubleSurface D) : Divisor E.idealSheaf.subscheme :=
  if h : τ.fst = E then Finsupp.single (curveOn hD E τ h) 1 else 0

open Classical in
private theorem curveDivisor_of_fst_eq (hD : DivisorWithCoeffs.IsSNC f D)
    {E : MMP.Mori.PrimeDivisor W} {τ : DoubleSurface D} (h : τ.fst = E) :
    curveDivisor hD E τ = Finsupp.single (curveOn hD E τ h) 1 := by
  rw [curveDivisor, dif_pos h]

/-- A double curve `τ` of `E` is the prime divisor `P` of `E` exactly when its carrier is the
closure of the image of the generic point of `P`. -/
private theorem carrier_eq_closure_iff (hD : DivisorWithCoeffs.IsSNC f D)
    {E : MMP.Mori.PrimeDivisor W} {τ : DoubleSurface D} (h : τ.fst = E)
    (P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme) :
    τ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint} ↔ curveOn hD E τ h = P := by
  constructor
  · intro hc
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    exact E.idealSheaf.subschemeι.isClosedEmbedding.injective
      ((isGenericPoint_curveOn hD E τ h).eq hc.symm)
  · rintro rfl
    exact (isGenericPoint_curveOn hD E τ h).def.symm

open Classical in
/-- **The divisor `Zᵢ` of an oriented system** is `∑_τ a_τ τ` over the double curves `τ` of
`Eᵢ`. -/
private theorem surfaceCoefficientDivisor_eq_sum (hD : DivisorWithCoeffs.IsSNC f D)
    [Fintype (DoubleSurface D)] (a : DoubleSurface D → ℚ) (E : MMP.Mori.PrimeDivisor W) :
    surfaceCoefficientDivisor a E = ∑ τ, a τ • Divisor.toQDivisor (curveDivisor hD E τ) := by
  ext P
  change (surfaceCoefficientDivisor a E).coeff P = _
  rw [coeff_surfaceCoefficientDivisor, surfaceCoefficientCoeff,
    finsum_subtype_eq_finsum_cond]
  simp_rw [finsum_eq_if]
  rw [finsum_eq_sum_of_fintype, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  change _ = a τ * ((curveDivisor hD E τ P : ℤ) : ℚ)
  by_cases h : τ.fst = E
  · rw [curveDivisor_of_fst_eq hD h, Finsupp.single_apply]
    by_cases hP : curveOn hD E τ h = P
    · rw [if_pos ⟨h, (carrier_eq_closure_iff hD h P).mpr hP⟩, if_pos hP]
      simp
    · rw [if_neg fun h' => hP ((carrier_eq_closure_iff hD h P).mp h'.2), if_neg hP]
      simp
  · rw [if_neg fun h' => h h'.1, curveDivisor, dif_neg h]
    simp

/-- The image in `W` of the double curve `σ`, embedded through its first component, is its
carrier. -/
private theorem range_doubleCurve (hD : DivisorWithCoeffs.IsSNC f D) (σ : DoubleSurface D) :
    Set.range ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι ≫
      σ.fst.idealSheaf.subschemeι) = σ.carrier := by
  obtain ⟨ζ, hζ, -⟩ := exists_isGenericPoint_carrier hD σ
  have hcl : IsClosed σ.carrier := hζ.def ▸ isClosed_closure
  have hpre : IsClosed (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier) :=
    hcl.preimage σ.fst.idealSheaf.subschemeι.continuous
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, hpre.closure_eq,
    Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι]
  exact Set.inter_eq_left.mpr fun x hx => (σ.carrier_subset hx).1

end CurveDivisor

/-! ### Intersection numbers of double curves on a component -/

section CurveIntersections

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] [QuasiCompact (W ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 3 (W ↘ Spec (.of ℂ))] [IsLocallyNoetherian W] [NoetherianSpace W]
  {D : Divisor W}

/-- The generic point of a double curve is not a triple point: its local ring on the component
has dimension one, whereas that at a closed point has dimension two. -/
private theorem curveOn_injective (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D)
    {E : MMP.Mori.PrimeDivisor W} (hE : E ∈ D.support) {σ τ : DoubleSurface D}
    (hσ : σ.fst = E) (hτ : τ.fst = E) (hne : τ ≠ σ) :
    curveOn hD E σ hσ ≠ curveOn hD E τ hτ := by
  intro h
  have hgσ := isGenericPoint_curveOn hD E σ hσ
  have hgτ := isGenericPoint_curveOn hD E τ hτ
  rw [← h] at hgτ
  have hcar : σ.carrier = τ.carrier := hgσ.def.symm.trans hgτ.def
  by_cases hs : τ.snd = σ.snd
  · exact hne (DoubleSurface.ext (hτ.trans hσ.symm) hs hcar.symm)
  · set η := (curveOn hD E σ hσ).genericPoint
    have hxσ : E.idealSheaf.subschemeι η ∈ σ.carrier := hgσ.mem
    have hxτ : E.idealSheaf.subschemeι η ∈ τ.carrier := hcar ▸ hxσ
    have hxE : E.idealSheaf.subschemeι η ∈ E.support := hσ ▸ (σ.carrier_subset hxσ).1
    have hEσ : E ≠ σ.snd := hσ ▸ σ.fst_ne_snd
    have hEτ : E ≠ τ.snd := hτ ▸ τ.fst_ne_snd
    have hcl := isClosed_singleton_of_mem_three hD hE σ.snd_mem τ.snd_mem hEσ hEτ (Ne.symm hs)
      ⟨⟨hxE, (σ.carrier_subset hxσ).2⟩, (τ.carrier_subset hxτ).2⟩
    obtain ⟨n, z, j, hz, -, hI⟩ := hD.2 (E.idealSheaf.subschemeι η)
    have h3 := ringKrullDim_stalk_eq_of_isClosed 3 _ hcl
    rw [hz.2] at h3
    have hn : n = 3 := by exact_mod_cast h3
    have h2 := ringKrullDim_stalk_subscheme_eq E.idealSheaf η hz (j ⟨E, hE, hxE⟩)
      (hI ⟨E, hE, hxE⟩)
    rw [hn, ringKrullDim_stalk_eq_coheight, (curveOn hD E σ hσ).coheight_genericPoint] at h2
    exact absurd h2 (by decide)

/-- **Intersections of distinct double curves on a component.** For distinct double curves `σ`,
`τ` of the component `E`, `(τ · σ)_E` is the number of points of `σ ∩ τ`. -/
private theorem degreeOn_curveDivisor_eq_finsum
    (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D) {E : MMP.Mori.PrimeDivisor W}
    (hE : E ∈ D.support) [IsLocallyNoetherian E.idealSheaf.subscheme]
    [IsNormal E.idealSheaf.subscheme] [QuasiCompact (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    (hvar : MMP.Mori.IsVariety ℂ (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
    (hsmE : IsSmoothScheme (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
    (hdimE : topologicalKrullDim E.idealSheaf.subscheme = 2) {σ τ : DoubleSurface D}
    (hσ : σ.fst = E) (hτ : τ.fst = E) (hne : τ ≠ σ)
    [IsProper ((curveOn hD E σ hσ).idealSheaf.subschemeι ≫
      E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    (hdim : topologicalKrullDim (curveOn hD E σ hσ).idealSheaf.subscheme ≤ 1)
    (hc : MMP.Mori.Divisor.IsCartier (curveDivisor hD E τ)) :
    (MMP.Mori.Divisor.degreeOn ℂ (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))
      (curveOn hD E σ hσ).idealSheaf.subschemeι hdim (curveDivisor hD E τ) hc : ℚ) =
      ∑ᶠ x ∈ σ.carrier ∩ τ.carrier, (1 : ℚ) := by
  set sE := E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)
  set C := curveOn hD E σ hσ
  set C' := curveOn hD E τ hτ
  have hCD : C ≠ C' := curveOn_injective hD hE hσ hτ hne
  have hc' : MMP.Mori.Divisor.IsCartier (Finsupp.single C' 1 : Divisor E.idealSheaf.subscheme) :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsmE _
  obtain ⟨-, hIN, -⟩ := MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne sE hvar
    hsmE hdimE hCD inferInstance
  obtain ⟨_, hdim1, hQ, heq⟩ := hIN
  rw [MMP.Mori.Divisor.degreeOn_congr (curveDivisor_of_fst_eq hD hτ) hc hc']
  have e : (MMP.Mori.Divisor.degreeOn ℂ sE C.idealSheaf.subschemeι hdim
      (Finsupp.single C' 1 : Divisor E.idealSheaf.subscheme) hc' : ℚ) =
      MMP.Mori.QDivisor.intersectionNumber ℂ sE C.idealSheaf.subschemeι hdim1
        (Finsupp.single C' 1 : QDivisor E.idealSheaf.subscheme) hQ := by
    have hDeq : Divisor.toQDivisor (Finsupp.single C' 1 : Divisor E.idealSheaf.subscheme) =
        (Finsupp.single C' 1 : QDivisor E.idealSheaf.subscheme) := by
      rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]
    rw [← QDivisor.intersectionNumber_toQDivisor ℂ sE _ hdim _ hc'
      (QDivisor.isQCartier_toQDivisor hc')]
    exact MMP.Fourfold.intersectionNumber_congr sE _ hdim (QDivisor.isQCartier_toQDivisor hc') hQ
      hDeq
  rw [e, heq]
  have himage : E.idealSheaf.subschemeι.base '' (C.support ∩ C'.support) = σ.carrier ∩ τ.carrier := by
    ext x
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨(mem_support_curveOn_iff hD E σ hσ y).mp h1, (mem_support_curveOn_iff hD E τ hτ y).mp h2⟩
    · rintro ⟨h1, h2⟩
      have hxE : x ∈ Set.range E.idealSheaf.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hσ ▸ (σ.carrier_subset h1).1
      obtain ⟨y, rfl⟩ := hxE
      exact ⟨y, ⟨(mem_support_curveOn_iff hD E σ hσ y).mpr h1,
        (mem_support_curveOn_iff hD E τ hτ y).mpr h2⟩, rfl⟩
  rw [← himage, finsum_mem_image E.idealSheaf.subschemeι.isClosedEmbedding.injective.injOn]
  by_cases hs : σ.snd = τ.snd
  · have hempty : C.support ∩ C'.support = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨h1, h2⟩
      have := DoubleSurface.disjoint_carrier (hσ.trans hτ.symm) hs (Ne.symm hne)
      exact Set.disjoint_left.mp this ((mem_support_curveOn_iff hD E σ hσ y).mp h1)
        ((mem_support_curveOn_iff hD E τ hτ y).mp h2)
    rw [hempty, finsum_mem_empty, finsum_mem_empty]
  · refine finsum_mem_congr rfl fun y hy => ?_
    rw [localIntersectionNumber_curveOn_eq_one hD hE hσ hτ hs
      ((mem_support_curveOn_iff hD E σ hσ y).mp hy.1) ((mem_support_curveOn_iff hD E τ hτ y).mp hy.2)]
    simp

end CurveIntersections

/-! ### The two sides of the identity along one double curve -/

section PerCurve

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] [QuasiCompact (W ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 3 (W ↘ Spec (.of ℂ))] [IsLocallyNoetherian W] [NoetherianSpace W]
  [IsNormal W] {D : Divisor W} [Fintype (DoubleSurface D)]

open Classical in
/-- **The right side along `σ`.** `(Zᵢ · σ)_{Eᵢ} = a_σ (σ · σ)_{Eᵢ} + ∑_τ a_τ #(σ ∩ τ)` over the
other double curves `τ` of `Eᵢ`. -/
private theorem intersectionNumber_surfaceCoefficientDivisor_eq
    (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D) (a : DoubleSurface D → ℚ)
    (σ : DoubleSurface D) [IsLocallyNoetherian σ.fst.idealSheaf.subscheme]
    [IsNormal σ.fst.idealSheaf.subscheme]
    [QuasiCompact (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    (hvar : MMP.Mori.IsVariety ℂ (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
    (hsmE : IsSmoothScheme (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
    (hdimE : topologicalKrullDim σ.fst.idealSheaf.subscheme = 2)
    (J : σ.fst.idealSheaf.subscheme.IdealSheafData)
    (hJ : J = (curveOn hD σ.fst σ rfl).idealSheaf)
    [IsProper (J.subschemeι ≫ σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    (hdim : topologicalKrullDim J.subscheme ≤ 1)
    (hZ : (surfaceCoefficientDivisor a σ.fst).IsQCartier) :
    (surfaceCoefficientDivisor a σ.fst).intersectionNumber ℂ
        (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)) J.subschemeι hdim hZ =
      a σ * (MMP.Mori.Divisor.degreeOn ℂ (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))
          J.subschemeι hdim (curveDivisor hD σ.fst σ)
          (MMP.Fourfold.isCartier_of_isSmoothScheme hsmE _) : ℚ) +
        ∑ τ ∈ Finset.univ.filter (fun τ => τ.fst = σ.fst ∧ τ ≠ σ),
          a τ * ∑ᶠ x ∈ σ.carrier ∩ τ.carrier, (1 : ℚ) := by
  subst hJ
  set sE := σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)
  have hc : ∀ τ, MMP.Mori.Divisor.IsCartier (curveDivisor hD σ.fst τ) := fun τ =>
    MMP.Fourfold.isCartier_of_isSmoothScheme hsmE _
  have hQ := MMP.Fourfold.isQCartier_of_isSmoothScheme hsmE
  rw [MMP.Fourfold.intersectionNumber_congr sE _ hdim hZ (hQ _)
      (surfaceCoefficientDivisor_eq_sum hD a σ.fst),
    intersectionNumber_finset_sum_smul sE _ hdim hQ Finset.univ a (curveDivisor hD σ.fst) hc,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ σ)]
  congr 1
  rw [← Finset.sum_subset (s₁ := Finset.univ.filter (fun τ => τ.fst = σ.fst ∧ τ ≠ σ))
    (fun τ hτ => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hτ).2.2, Finset.mem_univ _⟩)
    (fun τ hτ hτ' => ?_)]
  · refine Finset.sum_congr rfl fun τ hτ => ?_
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hτ
    rw [degreeOn_curveDivisor_eq_finsum hD σ.fst_mem hvar hsmE hdimE rfl h1 h2]
  · have h1 : τ.fst ≠ σ.fst := fun h =>
      hτ' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, (Finset.mem_erase.mp hτ).1⟩)
    rw [MMP.Mori.Divisor.degreeOn_congr (by rw [curveDivisor, dif_neg h1]) (hc τ)
      MMP.Mori.Divisor.isCartier_zero, MMP.Mori.Divisor.degreeOn_zero']
    simp

open Classical in
/-- A sum over the double curves of `(E, G)` read through `curveDivisor`. -/
private theorem sum_subtype_degreeOn_eq (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D)
    {E G : MMP.Mori.PrimeDivisor W} [IsLocallyNoetherian E.idealSheaf.subscheme]
    [IsNormal E.idealSheaf.subscheme]
    [QuasiCompact (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))] {C : Scheme.{0}}
    (i : C ⟶ E.idealSheaf.subscheme) [IsProper (i ≫ E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    (hdim : topologicalKrullDim C ≤ 1)
    (hc : ∀ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = G},
      MMP.Mori.Divisor.IsCartier (Finsupp.single (curveOn hD E τ.1 τ.2.1) 1 :
        Divisor E.idealSheaf.subscheme))
    (hc' : ∀ τ, MMP.Mori.Divisor.IsCartier (curveDivisor hD E τ)) :
    ∑ τ : {τ : DoubleSurface D // τ.fst = E ∧ τ.snd = G},
        (MMP.Mori.Divisor.degreeOn ℂ (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)) i hdim
          (Finsupp.single (curveOn hD E τ.1 τ.2.1) 1) (hc τ) : ℚ) =
      ∑ τ ∈ Finset.univ.filter (fun τ : DoubleSurface D => τ.fst = E ∧ τ.snd = G),
        (MMP.Mori.Divisor.degreeOn ℂ (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)) i hdim
          (curveDivisor hD E τ) (hc' τ) : ℚ) := by
  rw [Finset.sum_subtype (p := fun τ : DoubleSurface D => τ.fst = E ∧ τ.snd = G)
    (Finset.univ.filter fun τ : DoubleSurface D => τ.fst = E ∧ τ.snd = G) (fun τ => by simp)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [MMP.Mori.Divisor.degreeOn_congr (curveDivisor_of_fst_eq hD τ.2.1) (hc' τ.1) (hc τ)]

open Classical in
/-- **The left side along `σ ⊆ Eᵢ ∩ Eⱼ`.** `(D · σ) = mⱼ (σ · σ)_{Eᵢ} + mᵢ (σ · σ)_{Eⱼ} +
∑_τ m_{k(τ)} #(σ ∩ τ)` over the other double curves `τ ⊆ Eᵢ ∩ E_{k(τ)}`. -/
private theorem intersectionNumber_divisor_eq
    (hD : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D)
    (hsmW : IsSmoothScheme (W ↘ Spec (.of ℂ))) (σ : DoubleSurface D)
    [IsLocallyNoetherian σ.fst.idealSheaf.subscheme] [IsNormal σ.fst.idealSheaf.subscheme]
    [QuasiCompact (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    [IsLocallyNoetherian σ.snd.idealSheaf.subscheme] [IsNormal σ.snd.idealSheaf.subscheme]
    [QuasiCompact (σ.snd.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    (hvar : MMP.Mori.IsVariety ℂ (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
    (hsmE : IsSmoothScheme (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
    (hdimE : topologicalKrullDim σ.fst.idealSheaf.subscheme = 2)
    (hvar' : MMP.Mori.IsVariety ℂ (σ.snd.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
    (hsmF : IsSmoothScheme (σ.snd.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
    (hdimF : topologicalKrullDim σ.snd.idealSheaf.subscheme = 2)
    (J : σ.fst.idealSheaf.subscheme.IdealSheafData)
    (hJ : J = (curveOn hD σ.fst σ rfl).idealSheaf)
    (J' : σ.snd.idealSheaf.subscheme.IdealSheafData)
    (hJ' : J' = (curveOn hD σ.snd σ.swap rfl).idealSheaf)
    [IsProper (J.subschemeι ≫ σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    [IsProper ((J.subschemeι ≫ σ.fst.idealSheaf.subschemeι) ≫ W ↘ Spec (.of ℂ))]
    [IsProper (J'.subschemeι ≫ σ.snd.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    [IsProper ((J'.subschemeι ≫ σ.snd.idealSheaf.subschemeι) ≫ W ↘ Spec (.of ℂ))]
    (hdim : topologicalKrullDim J.subscheme ≤ 1) (hdim' : topologicalKrullDim J'.subscheme ≤ 1)
    (hDq : (Divisor.toQDivisor D).IsQCartier) :
    (Divisor.toQDivisor D).intersectionNumber ℂ (W ↘ Spec (.of ℂ))
        (J.subschemeι ≫ σ.fst.idealSheaf.subschemeι) hdim hDq =
      (D.coeff σ.snd : ℚ) * (MMP.Mori.Divisor.degreeOn ℂ
          (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)) J.subschemeι hdim
          (curveDivisor hD σ.fst σ) (MMP.Fourfold.isCartier_of_isSmoothScheme hsmE _) : ℚ) +
        (D.coeff σ.fst : ℚ) * (MMP.Mori.Divisor.degreeOn ℂ
          (σ.snd.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)) J'.subschemeι hdim'
          (curveDivisor hD σ.snd σ.swap) (MMP.Fourfold.isCartier_of_isSmoothScheme hsmF _) : ℚ) +
        ∑ τ ∈ Finset.univ.filter (fun τ => τ.fst = σ.fst ∧ τ ≠ σ),
          (D.coeff τ.snd : ℚ) * ∑ᶠ x ∈ σ.carrier ∩ τ.carrier, (1 : ℚ) := by
  subst hJ hJ'
  have hcW : ∀ G : Divisor W, MMP.Mori.Divisor.IsCartier G :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsmW
  have hcE : ∀ G : Divisor σ.fst.idealSheaf.subscheme, MMP.Mori.Divisor.IsCartier G :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsmE
  have hcF : ∀ G : Divisor σ.snd.idealSheaf.subscheme, MMP.Mori.Divisor.IsCartier G :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsmF
  rw [QDivisor.intersectionNumber_toQDivisor ℂ (W ↘ Spec (.of ℂ)) _ hdim D (hcW D) hDq]
  -- expand `D` along its components
  have hDsum : D = ∑ G ∈ D.support, D G • (Finsupp.single G 1 : Divisor W) := by
    conv_lhs => rw [← Finsupp.sum_single D]
    simp only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [MMP.Mori.Divisor.degreeOn_congr hDsum (hcW D) (hcW _),
    degreeOn_finset_sum (W ↘ Spec (.of ℂ)) _ hdim D.support _ (fun G => hcW _) (hcW _)]
  have hterm : ∀ G ∈ D.support, MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
      ((curveOn hD σ.fst σ rfl).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι) hdim
      (D G • (Finsupp.single G 1 : Divisor W)) (hcW _) =
      D G * MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
        ((curveOn hD σ.fst σ rfl).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι) hdim
        (Finsupp.single G 1 : Divisor W) (hcW _) := fun G _ =>
    MMP.Fourfold.degreeOn_zsmul (W ↘ Spec (.of ℂ)) _ hdim _ (hcW _) (D G)
  rw [Finset.sum_congr rfl hterm, ← Finset.add_sum_erase _ _ σ.fst_mem]
  push_cast
  -- the component `Eᵢ` itself: the curve identity and the restriction to `Eⱼ`
  have hEterm : (MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
      ((curveOn hD σ.fst σ rfl).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι) hdim
      (Finsupp.single σ.fst 1 : Divisor W) (hcW _) : ℚ) =
      (MMP.Mori.Divisor.degreeOn ℂ (σ.snd.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ)))
        (curveOn hD σ.snd σ.swap rfl).idealSheaf.subschemeι hdim'
        (curveDivisor hD σ.snd σ.swap) (hcF _) : ℚ) := by
    have hrange : Set.range ((curveOn hD σ.fst σ rfl).idealSheaf.subschemeι ≫
        σ.fst.idealSheaf.subschemeι) = Set.range ((curveOn hD σ.snd σ.swap rfl).idealSheaf.subschemeι ≫
        σ.snd.idealSheaf.subschemeι) := by
      have h1 := range_doubleCurve hD σ
      have h2 := range_doubleCurve hD σ.swap
      rw [← curveOn_idealSheaf hD σ.fst σ rfl] at h1
      rw [← curveOn_idealSheaf hD σ.swap.fst σ.swap rfl] at h2
      exact h1.trans h2.symm
    have e1 : MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
        ((curveOn hD σ.fst σ rfl).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι) hdim
        (Finsupp.single σ.fst 1 : Divisor W) (hcW _) =
        MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
        ((curveOn hD σ.snd σ.swap rfl).idealSheaf.subschemeι ≫ σ.snd.idealSheaf.subschemeι) hdim'
        (Finsupp.single σ.fst 1 : Divisor W) (hcW _) := by
      haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
      haveI := (curveOn hD σ.fst σ rfl).integral
      haveI := (curveOn hD σ.snd σ.swap rfl).integral
      haveI := (hcW (Finsupp.single σ.fst 1 : Divisor W)).isInvertibleModule_divisorialSheaf
      exact degreeOn_eq_of_range_eq (W ↘ Spec (.of ℂ)) _ _ hrange hdim hdim' _
    rw [e1, degreeOn_single_eq_sum_curveOn hD (W ↘ Spec (.of ℂ)) σ.snd_mem σ.fst_mem (Ne.symm σ.fst_ne_snd)
      (hcW _) (fun τ => hcF _) _ hdim']
    push_cast
    rw [sum_subtype_degreeOn_eq hD _ hdim' (fun τ => hcF _) (fun τ => hcF _),
      Finset.sum_eq_single σ.swap]
    · intro τ hτ hne
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hτ
      rw [degreeOn_curveDivisor_eq_finsum hD σ.snd_mem hvar' hsmF hdimF rfl h1 hne]
      have hdisj := DoubleSurface.disjoint_carrier (σ := σ.swap) (τ := τ) h1.symm h2.symm
        (Ne.symm hne)
      rw [Set.disjoint_iff_inter_eq_empty.mp hdisj, finsum_mem_empty]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩) h
  -- the other components
  have hrest : ∑ G ∈ D.support.erase σ.fst, (D G : ℚ) *
      (MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
        ((curveOn hD σ.fst σ rfl).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι) hdim
        (Finsupp.single G 1 : Divisor W) (hcW _) : ℚ) =
      ∑ τ ∈ Finset.univ.filter (fun τ : DoubleSurface D => τ.fst = σ.fst),
        (D τ.snd : ℚ) * (MMP.Mori.Divisor.degreeOn ℂ (σ.fst.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ)))
          (curveOn hD σ.fst σ rfl).idealSheaf.subschemeι hdim (curveDivisor hD σ.fst τ)
          (hcE _) : ℚ) := by
    have hG : ∀ G ∈ D.support.erase σ.fst, (D G : ℚ) *
        (MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
          ((curveOn hD σ.fst σ rfl).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι) hdim
          (Finsupp.single G 1 : Divisor W) (hcW _) : ℚ) =
        ∑ τ ∈ (Finset.univ.filter (fun τ : DoubleSurface D => τ.fst = σ.fst)).filter
          (fun τ => τ.snd = G),
          (D τ.snd : ℚ) * (MMP.Mori.Divisor.degreeOn ℂ (σ.fst.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ)))
            (curveOn hD σ.fst σ rfl).idealSheaf.subschemeι hdim (curveDivisor hD σ.fst τ)
            (hcE _) : ℚ) := by
      intro G hG
      obtain ⟨hGE, hGD⟩ := Finset.mem_erase.mp hG
      rw [degreeOn_single_eq_sum_curveOn hD (W ↘ Spec (.of ℂ)) σ.fst_mem hGD (Ne.symm hGE) (hcW _)
        (fun τ => hcE _) _ hdim]
      push_cast
      rw [sum_subtype_degreeOn_eq hD _ hdim (fun τ => hcE _) (fun τ => hcE _), Finset.mul_sum,
        Finset.filter_filter]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [(Finset.mem_filter.mp hτ).2.2]
    rw [Finset.sum_congr rfl hG]
    refine Finset.sum_fiberwise_of_maps_to (fun τ hτ => ?_) _
    obtain ⟨-, h1⟩ := Finset.mem_filter.mp hτ
    exact Finset.mem_erase.mpr ⟨fun h => τ.fst_ne_snd (h1.trans h.symm), τ.snd_mem⟩
  have hσmem : σ ∈ Finset.univ.filter fun τ : DoubleSurface D => τ.fst = σ.fst := by simp
  rw [hEterm, hrest, ← Finset.add_sum_erase _ _ hσmem]
  have hfilt : (Finset.univ.filter (fun τ : DoubleSurface D => τ.fst = σ.fst)).erase σ =
      Finset.univ.filter (fun τ => τ.fst = σ.fst ∧ τ ≠ σ) := by
    ext τ
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hfilt]
  have hsum : ∑ τ ∈ Finset.univ.filter (fun τ : DoubleSurface D => τ.fst = σ.fst ∧ τ ≠ σ),
      (D τ.snd : ℚ) * (MMP.Mori.Divisor.degreeOn ℂ (σ.fst.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ)))
        (curveOn hD σ.fst σ rfl).idealSheaf.subschemeι hdim (curveDivisor hD σ.fst τ)
        (hcE _) : ℚ) =
      ∑ τ ∈ Finset.univ.filter (fun τ => τ.fst = σ.fst ∧ τ ≠ σ),
        (D.coeff τ.snd : ℚ) * ∑ᶠ x ∈ σ.carrier ∩ τ.carrier, (1 : ℚ) := by
    refine Finset.sum_congr rfl fun τ hτ => ?_
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hτ
    rw [degreeOn_curveDivisor_eq_finsum hD σ.fst_mem hvar hsmE hdimE rfl h1 h2]
    rfl
  rw [hsum]
  change (D σ.fst : ℚ) * _ + ((D σ.snd : ℚ) * _ + _) = (D σ.snd : ℚ) * _ + (D σ.fst : ℚ) * _ + _
  ring

end PerCurve

/-! ### The combinatorial identity -/

section Combinatorics

open Finset

variable {ι S P : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]

open Classical in
/-- A finite sum over the points of a finite set `T` containing `S` of the indicator of `S`
computes the finite sum over `S`. -/
private theorem finsum_mem_eq_sum_ite {S' : Set P} {T : Finset P} (h : S' ⊆ T) (g : P → ℚ) :
    ∑ᶠ x ∈ S', g x = ∑ x ∈ T, if x ∈ S' then g x else 0 := by
  classical
  have hfin : S'.Finite := T.finite_toSet.subset h
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_filter]
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
  exact ⟨fun hx => ⟨h hx, hx⟩, fun hx => hx.2⟩

/-- The data of a simple normal crossing configuration of curves on surfaces: double curves `σ`
with an ordered pair of components, their carriers, and the triple points. -/
private structure SNCConfig (ι S P : Type*) where
  fst : S → ι
  snd : S → ι
  swap : S → S
  swap_swap : ∀ σ, swap (swap σ) = σ
  fst_swap : ∀ σ, fst (swap σ) = snd σ
  snd_swap : ∀ σ, snd (swap σ) = fst σ
  fst_ne_snd : ∀ σ, fst σ ≠ snd σ
  car : S → Set P
  car_swap : ∀ σ, car (swap σ) = car σ
  comp : ι → Set P
  car_subset : ∀ σ, car σ ⊆ comp (fst σ) ∩ comp (snd σ)
  exists_car : ∀ i j, i ≠ j → ∀ x ∈ comp i ∩ comp j, ∃ σ, fst σ = i ∧ snd σ = j ∧ x ∈ car σ
  eq_of_mem : ∀ σ τ, fst σ = fst τ → snd σ = snd τ → ∀ x ∈ car σ, x ∈ car τ → σ = τ
  finite : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → (comp i ∩ comp j ∩ comp k).Finite

namespace SNCConfig

/-- The finite set of triple points of `(i, j, k)`, empty unless the three are distinct. -/
private noncomputable def tri (c : SNCConfig ι S P) (i j k : ι) : Finset P := by
  classical
  exact if h : i ≠ j ∧ i ≠ k ∧ j ≠ k then (c.finite i j k h.1 h.2.1 h.2.2).toFinset else ∅

private theorem mem_tri (c : SNCConfig ι S P) {i j k : ι} {x : P} :
    x ∈ tri c i j k ↔ (i ≠ j ∧ i ≠ k ∧ j ≠ k) ∧ x ∈ c.comp i ∩ c.comp j ∩ c.comp k := by
  classical
  unfold tri
  split_ifs with h
  · simp [h]
  · simp [h]

private theorem tri_swap₁₂ (c : SNCConfig ι S P) (i j k : ι) : tri c j i k = tri c i j k := by
  ext x
  rw [mem_tri c, mem_tri c]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, ⟨hj, hi⟩, hk⟩; exact ⟨⟨Ne.symm h1, h3, h2⟩, ⟨hi, hj⟩, hk⟩
  · rintro ⟨⟨h1, h2, h3⟩, ⟨hi, hj⟩, hk⟩; exact ⟨⟨Ne.symm h1, h3, h2⟩, ⟨hj, hi⟩, hk⟩

private theorem tri_swap₂₃ (c : SNCConfig ι S P) (i j k : ι) : tri c i k j = tri c i j k := by
  ext x
  rw [mem_tri c, mem_tri c]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, ⟨hi, hk⟩, hj⟩; exact ⟨⟨h2, h1, Ne.symm h3⟩, ⟨hi, hj⟩, hk⟩
  · rintro ⟨⟨h1, h2, h3⟩, ⟨hi, hj⟩, hk⟩; exact ⟨⟨h2, h1, Ne.symm h3⟩, ⟨hi, hk⟩, hj⟩

/-- The sum over ordered triples of distinct components and their triple points. -/
private noncomputable def triSum (c : SNCConfig ι S P) (F : ι → ι → ι → P → ℚ) : ℚ :=
  ∑ i, ∑ j, ∑ k, ∑ x ∈ tri c i j k, F i j k x

private theorem triSum_mul (c : SNCConfig ι S P) (r : ℚ) (F : ι → ι → ι → P → ℚ) :
    triSum c (fun i j k x => r * F i j k x) = r * triSum c F := by
  simp only [triSum, Finset.mul_sum]

private theorem triSum_congr (c : SNCConfig ι S P) {F G : ι → ι → ι → P → ℚ}
    (h : ∀ i j k, ∀ x ∈ tri c i j k, F i j k x = G i j k x) : triSum c F = triSum c G := by
  unfold triSum
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x hx => h i j k x hx

private theorem triSum_swap₁₂ (c : SNCConfig ι S P) (F : ι → ι → ι → P → ℚ) :
    triSum c (fun i j k x => F j i k x) = triSum c F := by
  unfold triSum
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => by rw [tri_swap₁₂ c]

private theorem triSum_swap₂₃ (c : SNCConfig ι S P) (F : ι → ι → ι → P → ℚ) :
    triSum c (fun i j k x => F i k j x) = triSum c F := by
  unfold triSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [tri_swap₂₃ c]

/-- **The identity at the triple points.** For an antisymmetric family `A i j x`, with
`b_{ij} = A_{ij}/(m_i m_j)`, summing over ordered triples of distinct components and their triple
points, `½ ∑ m_i m_j m_k b_{ij}² = ∑ m_i m_j m_k b_{ij} b_{ik} + ⅙ ∑ m_i m_j m_k
(b_{ij} - b_{ik} + b_{jk})²`. -/
private theorem triSum_identity (c : SNCConfig ι S P) (m : ι → ℚ) (hm : ∀ i, m i ≠ 0)
    (A : ι → ι → P → ℚ)
    (hA : ∀ i j, i ≠ j → ∀ x ∈ c.comp i ∩ c.comp j, A j i x = -A i j x) :
    (1 / 2) * triSum c (fun i j k x => A i j x ^ 2 / (m i * m j) * m k) =
      triSum c (fun i j k x => A i j x * A i k x / m i) +
      (1 / 6) * triSum c (fun i j k x => m i * m j * m k *
        (A i j x / (m i * m j) - A i k x / (m i * m k) + A j k x / (m j * m k)) ^ 2) := by
  set B : ι → ι → P → ℚ := fun i j x => A i j x / (m i * m j) with hBdef
  have hB : ∀ i j k, ∀ x ∈ tri c i j k,
      B j i x = -B i j x ∧ B k i x = -B i k x ∧ B k j x = -B j k x := by
    intro i j k x hx
    obtain ⟨⟨hij, hik, hjk⟩, ⟨hi, hj⟩, hk⟩ := (mem_tri c).mp hx
    simp only [hBdef]
    refine ⟨?_, ?_, ?_⟩
    · rw [hA i j hij x ⟨hi, hj⟩, mul_comm (m j)]; ring
    · rw [hA i k hik x ⟨hi, hk⟩, mul_comm (m k)]; ring
    · rw [hA j k hjk x ⟨hj, hk⟩, mul_comm (m k)]; ring
  set F1 : ι → ι → ι → P → ℚ := fun i j k x => m i * m j * m k * B i j x ^ 2
  set X0 : ι → ι → ι → P → ℚ := fun i j k x => m i * m j * m k * (B i j x * B i k x)
  have h1 : triSum c (fun i j k x => A i j x ^ 2 / (m i * m j) * m k) = triSum c F1 :=
    triSum_congr c fun i j k x _ => by
      simp only [F1, hBdef]
      field_simp [hm i, hm j]
  have h2 : triSum c (fun i j k x => A i j x * A i k x / m i) = triSum c X0 :=
    triSum_congr c fun i j k x _ => by
      simp only [X0, hBdef]
      field_simp [hm i, hm j, hm k]
  have h3 : triSum c (fun i j k x => m i * m j * m k *
      (A i j x / (m i * m j) - A i k x / (m i * m k) + A j k x / (m j * m k)) ^ 2) =
      triSum c F1 + triSum c (fun i j k x => m i * m j * m k * B i k x ^ 2) +
        triSum c (fun i j k x => m i * m j * m k * B j k x ^ 2) - 2 * triSum c X0 +
        2 * triSum c (fun i j k x => m i * m j * m k * (B i j x * B j k x)) -
        2 * triSum c (fun i j k x => m i * m j * m k * (B i k x * B j k x)) := by
    simp only [triSum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x _ => ?_
    simp only [F1, X0, hBdef]
    ring
  have hF2 : triSum c (fun i j k x => m i * m j * m k * B i k x ^ 2) = triSum c F1 :=
    calc triSum c (fun i j k x => m i * m j * m k * B i k x ^ 2)
        = triSum c (fun i j k x => F1 i k j x) :=
          triSum_congr c fun i j k x _ => by simp only [F1]; ring
      _ = triSum c F1 := triSum_swap₂₃ c F1
  have hF3 : triSum c (fun i j k x => m i * m j * m k * B j k x ^ 2) = triSum c F1 :=
    calc triSum c (fun i j k x => m i * m j * m k * B j k x ^ 2)
        = triSum c (fun i j k x => F1 j k i x) :=
          triSum_congr c fun i j k x _ => by simp only [F1]; ring
      _ = triSum c (fun i j k x => F1 i k j x) := triSum_swap₁₂ c (fun i j k x => F1 i k j x)
      _ = triSum c F1 := triSum_swap₂₃ c F1
  have hF5 : triSum c (fun i j k x => m i * m j * m k * (B i j x * B j k x)) = -triSum c X0 :=
    calc triSum c (fun i j k x => m i * m j * m k * (B i j x * B j k x))
        = triSum c (fun i j k x => m j * m i * m k * (B j i x * B i k x)) :=
          (triSum_swap₁₂ c (fun i j k x => m i * m j * m k * (B i j x * B j k x))).symm
      _ = triSum c (fun i j k x => -1 * X0 i j k x) :=
          triSum_congr c fun i j k x hx => by
            simp only [X0]
            rw [(hB i j k x hx).1]
            ring
      _ = -triSum c X0 := by rw [triSum_mul]; ring
  have hF6 : triSum c (fun i j k x => m i * m j * m k * (B i k x * B j k x)) = triSum c X0 :=
    calc triSum c (fun i j k x => m i * m j * m k * (B i k x * B j k x))
        = triSum c (fun i j k x => X0 k i j x) :=
          triSum_congr c fun i j k x hx => by
            simp only [X0]
            rw [(hB i j k x hx).2.1, (hB i j k x hx).2.2]
            ring
      _ = triSum c (fun i j k x => X0 j i k x) := triSum_swap₂₃ c (fun i j k x => X0 j i k x)
      _ = triSum c X0 := triSum_swap₁₂ c X0
  rw [h1, h2, h3, hF2, hF3, hF5, hF6]
  ring

open Classical in
/-- **Reindexing intersections of double curves by triple points.** Summing over pairs of distinct
double curves `σ`, `τ` with the same first component and over their common points is summing over
ordered triples of distinct components and their triple points. -/
private theorem sum_sum_finsum_eq_triSum (c : SNCConfig ι S P) (Ψ : ι → ι → ι → P → ℚ) :
    ∑ σ, ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
      ∑ᶠ x ∈ c.car σ ∩ c.car τ, Ψ (c.fst σ) (c.snd σ) (c.snd τ) x = triSum c Ψ := by
  set U : Finset P := univ.biUnion (fun q : ι × ι × ι => tri c q.1 q.2.1 q.2.2) with hU
  have htriU : ∀ i j k, tri c i j k ⊆ U := fun i j k x hx =>
    Finset.mem_biUnion.mpr ⟨(i, j, k), Finset.mem_univ _, hx⟩
  have hsub : ∀ σ τ, c.fst τ = c.fst σ → τ ≠ σ →
      c.car σ ∩ c.car τ ⊆ ↑(tri c (c.fst σ) (c.snd σ) (c.snd τ)) := by
    rintro σ τ h1 h2 x ⟨hxσ, hxτ⟩
    by_cases h3 : c.snd τ = c.snd σ
    · exact absurd (c.eq_of_mem τ σ h1 h3 x hxτ hxσ) h2
    · rw [Finset.mem_coe, mem_tri c]
      refine ⟨⟨c.fst_ne_snd σ, h1 ▸ c.fst_ne_snd τ, Ne.symm h3⟩,
        ⟨(c.car_subset σ hxσ).1, (c.car_subset σ hxσ).2⟩, ?_⟩
      exact (c.car_subset τ hxτ).2
  -- pointwise in the triple point: a bijection of index sets
  have hpt : ∀ x : P, (∑ σ, ∑ τ, if (c.fst τ = c.fst σ ∧ τ ≠ σ) ∧ x ∈ c.car σ ∩ c.car τ then
      Ψ (c.fst σ) (c.snd σ) (c.snd τ) x else 0) =
      ∑ i, ∑ j, ∑ k, if x ∈ tri c i j k then Ψ i j k x else 0 := by
    intro x
    rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
    rw [show (∑ i, ∑ j, ∑ k, if x ∈ tri c i j k then Ψ i j k x else 0) =
        ∑ q : ι × ι × ι, if x ∈ tri c q.1 q.2.1 q.2.2 then Ψ q.1 q.2.1 q.2.2 x else 0 by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => by rw [Fintype.sum_prod_type],
      ← Finset.sum_filter]
    refine Finset.sum_bij (fun p _ => (c.fst p.1, c.snd p.1, c.snd p.2)) ?_ ?_ ?_ ?_
    · rintro ⟨σ, τ⟩ hp
      obtain ⟨-, ⟨h1, h2⟩, hx⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub σ τ h1 h2 hx⟩
    · rintro ⟨σ, τ⟩ hp ⟨σ', τ'⟩ hp' he
      obtain ⟨-, ⟨h1, -⟩, hxσ, hxτ⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, ⟨h1', -⟩, hxσ', hxτ'⟩ := Finset.mem_filter.mp hp'
      simp only [Prod.mk.injEq] at he
      obtain ⟨he1, he2, he3⟩ := he
      have hσ : σ = σ' := c.eq_of_mem σ σ' he1 he2 x hxσ hxσ'
      subst hσ
      have hτ : τ = τ' := c.eq_of_mem τ τ' (h1.trans h1'.symm) he3 x hxτ hxτ'
      subst hτ
      rfl
    · rintro ⟨i, j, k⟩ hq
      obtain ⟨-, hq⟩ := Finset.mem_filter.mp hq
      obtain ⟨⟨hij, hik, hjk⟩, ⟨hi, hj⟩, hk⟩ := (mem_tri c).mp hq
      obtain ⟨σ, hσ1, hσ2, hxσ⟩ := c.exists_car i j hij x ⟨hi, hj⟩
      obtain ⟨τ, hτ1, hτ2, hxτ⟩ := c.exists_car i k hik x ⟨hi, hk⟩
      refine ⟨(σ, τ), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨hτ1.trans hσ1.symm, fun h => hjk (by
          have h' : τ = σ := h
          rw [← hσ2, ← hτ2, h'])⟩, hxσ, hxτ⟩, ?_⟩
      simp only [hσ1, hσ2, hτ2]
    · intro p _
      rfl
  -- both sides as sums over the triple points
  have hLHS : ∀ σ, ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
      ∑ᶠ x ∈ c.car σ ∩ c.car τ, Ψ (c.fst σ) (c.snd σ) (c.snd τ) x =
      ∑ τ, ∑ x ∈ U, if (c.fst τ = c.fst σ ∧ τ ≠ σ) ∧ x ∈ c.car σ ∩ c.car τ then
        Ψ (c.fst σ) (c.snd σ) (c.snd τ) x else 0 := by
    intro σ
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs with h
    · rw [finsum_mem_eq_sum_ite ((hsub σ τ h.1 h.2).trans (by
        intro x hx; exact Finset.mem_coe.mpr (htriU _ _ _ (Finset.mem_coe.mp hx)))) _]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ c.car σ ∩ c.car τ
      · rw [if_pos hx, if_pos ⟨h, hx⟩]
      · rw [if_neg hx, if_neg fun h' => hx h'.2]
    · refine (Finset.sum_eq_zero fun x _ => ?_).symm
      rw [if_neg fun h' => h h'.1]
  have hRHS : triSum c Ψ = ∑ i, ∑ j, ∑ k, ∑ x ∈ U, if x ∈ tri c i j k then Ψ i j k x else 0 := by
    unfold triSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (htriU i j k)]
  rw [Finset.sum_congr rfl fun σ _ => hLHS σ, hRHS]
  calc ∑ σ, ∑ τ, ∑ x ∈ U, (if (c.fst τ = c.fst σ ∧ τ ≠ σ) ∧ x ∈ c.car σ ∩ c.car τ then
          Ψ (c.fst σ) (c.snd σ) (c.snd τ) x else 0)
      = ∑ x ∈ U, ∑ σ, ∑ τ, (if (c.fst τ = c.fst σ ∧ τ ≠ σ) ∧ x ∈ c.car σ ∩ c.car τ then
          Ψ (c.fst σ) (c.snd σ) (c.snd τ) x else 0) := by
        rw [Finset.sum_congr rfl fun σ _ => Finset.sum_comm]
        exact Finset.sum_comm
    _ = ∑ x ∈ U, ∑ i, ∑ j, ∑ k, (if x ∈ tri c i j k then Ψ i j k x else 0) :=
        Finset.sum_congr rfl fun x _ => hpt x
    _ = ∑ i, ∑ j, ∑ k, ∑ x ∈ U, (if x ∈ tri c i j k then Ψ i j k x else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]

open Classical in
/-- **The weighted curve identity, combinatorial form.** For an oriented system `a` on the double
curves, weights `m`, self-intersections `s` and the coefficients `A i j x` of `a` along the double
curve of `(i, j)` through `x`,
`½ ∑_σ m_i m_j b_σ² (m_j s_σ + m_i s_{σ'} + ∑_τ m_{k(τ)} #(σ ∩ τ))`
`= ∑_σ a_σ (a_σ s_σ + ∑_τ a_τ #(σ ∩ τ)) / m_i`
`+ ⅙ ∑_{i,j,k,x} m_i m_j m_k (b_{ij} - b_{ik} + b_{jk})²`,
the inner sums over the double curves `τ ≠ σ` with the same first component. -/
private theorem weighted_identity (c : SNCConfig ι S P) (a : S → ℚ)
    (ha : ∀ σ, a (c.swap σ) = -a σ) (m : ι → ℚ) (hm : ∀ i, m i ≠ 0) (s : S → ℚ)
    (A : ι → ι → P → ℚ) (hA : ∀ σ, ∀ x ∈ c.car σ, A (c.fst σ) (c.snd σ) x = a σ) :
    (1 / 2) * ∑ σ, m (c.fst σ) * m (c.snd σ) * (a σ / (m (c.fst σ) * m (c.snd σ))) ^ 2 *
        (m (c.snd σ) * s σ + m (c.fst σ) * s (c.swap σ) +
          ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
            m (c.snd τ) * ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ)) =
      ∑ σ, a σ * (a σ * s σ + ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
            a τ * ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ)) / m (c.fst σ) +
      (1 / 6) * triSum c (fun i j k x => m i * m j * m k *
        (A i j x / (m i * m j) - A i k x / (m i * m k) + A j k x / (m j * m k)) ^ 2) := by
  -- antisymmetry of the coefficients
  have hA' : ∀ i j, i ≠ j → ∀ x ∈ c.comp i ∩ c.comp j, A j i x = -A i j x := by
    intro i j hij x hx
    obtain ⟨σ, h1, h2, hxσ⟩ := c.exists_car i j hij x hx
    have e1 := hA σ x hxσ
    have e2 := hA (c.swap σ) x (by rw [c.car_swap]; exact hxσ)
    rw [c.fst_swap, c.snd_swap, ha, h1, h2] at e2
    rw [h1, h2] at e1
    rw [e2, e1]
  have hId := triSum_identity c m hm A hA'
  -- the cross terms
  have hX1 : ∑ σ, ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
      a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) * m (c.snd τ) * ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ) =
      triSum c (fun i j k x => A i j x ^ 2 / (m i * m j) * m k) := by
    rw [← sum_sum_finsum_eq_triSum c]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ hτ => ?_
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hτ
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun x hx => ?_
    rw [hA σ x hx.1, mul_one]
  have hX2 : ∑ σ, ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
      a σ * a τ / m (c.fst σ) * ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ) =
      triSum c (fun i j k x => A i j x * A i k x / m i) := by
    rw [← sum_sum_finsum_eq_triSum c]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ hτ => ?_
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hτ
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun x hx => ?_
    rw [hA σ x hx.1, ← h1, hA τ x hx.2, mul_one]
  -- the self-intersection terms
  have hswap : ∀ f : S → ℚ, ∑ σ, f (c.swap σ) = ∑ σ, f σ := fun f =>
    Fintype.sum_bijective c.swap (Function.Involutive.bijective c.swap_swap) _ _ fun _ => rfl
  have hself : ∑ σ, a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) * (m (c.fst σ) * s (c.swap σ)) =
      ∑ σ, a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) * (m (c.snd σ) * s σ) := by
    rw [← hswap (fun σ => a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) * (m (c.snd σ) * s σ))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ha, c.fst_swap, c.snd_swap]
    ring
  have hL : ∀ σ, m (c.fst σ) * m (c.snd σ) * (a σ / (m (c.fst σ) * m (c.snd σ))) ^ 2 =
      a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) := fun σ => by
    field_simp [hm (c.fst σ), hm (c.snd σ)]
  simp_rw [hL]
  have e1 : ∑ σ, a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) *
      (m (c.snd σ) * s σ + m (c.fst σ) * s (c.swap σ) +
        ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
          m (c.snd τ) * ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ)) =
      ∑ σ, a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) * (m (c.snd σ) * s σ) +
      ∑ σ, a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) * (m (c.fst σ) * s (c.swap σ)) +
      ∑ σ, ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
        a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) * m (c.snd τ) *
          ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_add, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have e2 : ∑ σ, a σ * (a σ * s σ + ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
        a τ * ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ)) / m (c.fst σ) =
      ∑ σ, a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) * (m (c.snd σ) * s σ) +
      ∑ σ, ∑ τ ∈ univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
        a σ * a τ / m (c.fst σ) * ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hs : a σ ^ 2 / (m (c.fst σ) * m (c.snd σ)) * (m (c.snd σ) * s σ) =
        a σ * (a σ * s σ) / m (c.fst σ) := by
      field_simp [hm (c.fst σ), hm (c.snd σ)]
    rw [mul_add, add_div, hs, Finset.mul_sum, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  rw [e1, e2, hself, hX1, hX2]
  linarith

/-- **No relation among the double curves.** If the weighted identity holds with the left
weights `X σ` negative and the self-intersections `Y σ` zero, then all coefficients vanish. -/
private theorem eq_zero_of_weighted (c : SNCConfig ι S P) (a : S → ℚ) (m : ι → ℚ)
    (hm : ∀ i, 0 < m i) (X Y : S → ℚ) (hX : ∀ σ, X σ < 0) (hY : ∀ σ, Y σ = 0)
    (A : ι → ι → P → ℚ)
    (h : (1 / 2) * ∑ σ, m (c.fst σ) * m (c.snd σ) * (a σ / (m (c.fst σ) * m (c.snd σ))) ^ 2 *
        X σ =
      ∑ σ, a σ * Y σ / m (c.fst σ) +
        (1 / 6) * triSum c (fun i j k x => m i * m j * m k *
          (A i j x / (m i * m j) - A i k x / (m i * m k) + A j k x / (m j * m k)) ^ 2)) :
    a = 0 := by
  have hT : 0 ≤ triSum c (fun i j k x => m i * m j * m k *
      (A i j x / (m i * m j) - A i k x / (m i * m k) + A j k x / (m j * m k)) ^ 2) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun x _ => ?_
    have := hm i
    have := hm j
    have := hm k
    positivity
  have hR : ∑ σ, a σ * Y σ / m (c.fst σ) = 0 :=
    Finset.sum_eq_zero fun σ _ => by rw [hY σ]; ring
  have hterm : ∀ σ, m (c.fst σ) * m (c.snd σ) * (a σ / (m (c.fst σ) * m (c.snd σ))) ^ 2 *
      X σ ≤ 0 := fun σ => by
    have := hm (c.fst σ)
    have := hm (c.snd σ)
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hX σ).le
  have hle : ∑ σ, m (c.fst σ) * m (c.snd σ) * (a σ / (m (c.fst σ) * m (c.snd σ))) ^ 2 *
      X σ ≤ 0 := Finset.sum_nonpos fun σ _ => hterm σ
  have hsum : ∑ σ, m (c.fst σ) * m (c.snd σ) * (a σ / (m (c.fst σ) * m (c.snd σ))) ^ 2 *
      X σ = 0 := by
    rw [hR, zero_add] at h
    linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonpos fun σ _ => hterm σ).mp hsum
  funext σ
  have h0 := hall σ (Finset.mem_univ σ)
  have h1 := hm (c.fst σ)
  have h2 := hm (c.snd σ)
  have hb : (a σ / (m (c.fst σ) * m (c.snd σ))) ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < (a σ / (m (c.fst σ) * m (c.snd σ))) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    have : m (c.fst σ) * m (c.snd σ) * (a σ / (m (c.fst σ) * m (c.snd σ))) ^ 2 * X σ < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (hX σ)
    linarith
  have hb' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb
  rcases div_eq_zero_iff.mp hb' with h3 | h3
  · exact h3
  · exact absurd h3 (by positivity)

end SNCConfig

end Combinatorics

/-! ### Classes of curve combinations on a smooth projective surface -/

section ClassDegree

open Classical in
/-- The class `[F] ∈ H_2(X, ℚ)` of a `ℚ`-divisor `F` on a complex scheme: the class of the
rational curve cycle `∑ fᵢ [Fᵢ]`, a component that is not a curve contributing `0`. -/
private noncomputable def curveDivisorClass (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [MMP.IsComplexScheme X] : QDivisor X →ₗ[ℚ] RationalHomology X (2 * 1) :=
  MMP.Chow.rationalCycleClass X 1 ∘ₗ Finsupp.linearCombination ℚ
    (fun Q : MMP.Mori.PrimeDivisor X =>
      if h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (X ↘ Spec (.of ℂ)) Q.genericPoint = 1 then
        MMP.Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) 1
          Q.genericPoint h else 0)

section Main

/-- **A curve combination with vanishing homology class has degree zero on curves.** Let `W` be a
smooth projective complex surface and `F` a `ℚ`-divisor on `W` with Cartier components. If the
class of `F` in `H_2(W, ℚ)` vanishes, then `(F · C) = 0` for every integral closed curve
`C ⊆ W`. -/
private theorem intersectionNumber_eq_zero_of_curveDivisorClass_eq_zero
    {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W]
    [IsLocallyNoetherian W] [IsNormal W]
    (hv : MMP.Mori.IsVariety ℂ (W ↘ Spec (.of ℂ)))
    (hWp : AlgebraicGeometry.IsProjective (W ↘ Spec (.of ℂ)))
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 2)
    (F : QDivisor W) (hQ : F.IsQCartier)
    (hFc : ∀ S ∈ F.support, Divisor.IsCartier (Finsupp.single S 1 : Divisor W))
    (hF : curveDivisorClass W F = 0)
    (C : Scheme.{0}) (i : C ⟶ W) [IsClosedImmersion i] [IsIntegral C]
    [IsProper (i ≫ W ↘ Spec (.of ℂ))] (hC : topologicalKrullDim C = 1) :
    F.intersectionNumber ℂ (W ↘ Spec (.of ℂ)) i hC.le hQ = 0 := by
  classical
  haveI : IsIntegral W := hv.toIsIntegral
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  have hX : MMP.Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).2
      ⟨hv, isProjectiveMorphism_of_isProjective_of_isAffine _ hWp⟩
  -- an integral multiple `G = N F`
  obtain ⟨N, hN, G, hG⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor F
  have hGC : G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm G
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ _ i hC.le F hQ hN G hGC hG]
  suffices h0 : G.degreeOn ℂ (W ↘ Spec (.of ℂ)) i hC.le hGC = 0 by rw [h0]; simp
  haveI hGi : Stacks.Ample.IsInvertibleModule W G.divisorialSheaf :=
    hGC.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 G.divisorialSheaf := hGi
  -- the dictionary: `[F] = 0` iff `c₁(𝒪_W(G)) = 0`
  have hdimX : topologicalKrullDim W = ((1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]; rfl
  have hgen : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (W ↘ Spec (.of ℂ))
      (_root_.genericPoint W) = ((1 + 1 : ℕ) : ℤ) := by
    refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
      ℂ _ _ (1 + 1) ?_
    rw [(genericPoint_spec W).def, ← hdimX]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ W).isHomeomorph
  have hc := ((MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback hX hsm hdimX F hN G hG
    (_root_.genericPoint W) hgen).2).1 hF
  have hL := MMP.Chow.firstChernClassTop_eq_zero_of_mapCoeff_eq_zero G.divisorialSheaf hc
  -- the degree along `C` of a line bundle with vanishing `c₁ᵗᵒᵖ`
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hX
  haveI : Stacks.Ample.IsInvertibleModule W H := hH
  exact MMP.Chow.degreeOn_eq_zero_of_firstChernClassTop_eq_zero H
    ((Stacks.AmpleBridge.isAmple_iff_isAmple W H).mpr hHa) _ hL i hC.le

end Main

end ClassDegree

/-! ### Antiample divisors are negative on curves of the components -/

section Antiample

/-- A prime divisor of an integral surface of finite type over a field, of dimension at most one,
is a curve: it has dimension exactly one. -/
private theorem topologicalKrullDim_primeDivisor_eq_one {k : Type} [Field k] {E : Scheme.{0}}
    [E.Over (Spec (.of k))] [IsIntegral E] [LocallyOfFiniteType (E ↘ Spec (.of k))]
    (hdimE : topologicalKrullDim E = 2) (C : MMP.Mori.PrimeDivisor E)
    (hle : topologicalKrullDim C.idealSheaf.subscheme ≤ 1) :
    topologicalKrullDim C.idealSheaf.subscheme = 1 := by
  refine le_antisymm hle ?_
  haveI := C.integral
  have h := MMP.height_add_coheight_eq_krullDim k C.genericPoint
  rw [C.coheight_genericPoint,
    Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim, hdimE] at h
  have hmin : ¬ IsMin C.genericPoint := by
    intro hm
    rw [Order.height_eq_zero.mpr hm, zero_add] at h
    exact absurd h (by decide)
  obtain ⟨y, hy⟩ := not_isMin_iff.mp hmin
  have hyC : y ∈ Set.range C.idealSheaf.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    change y ∈ C.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hy.le
  obtain ⟨y', rfl⟩ := hyC
  have hind : Topology.IsInducing C.idealSheaf.subschemeι :=
    C.idealSheaf.subschemeι.isClosedEmbedding.isInducing
  have hlt : y' < genericPoint C.idealSheaf.subscheme := by
    refine lt_of_le_not_ge ?_ fun h' => hy.not_ge ?_
    · exact hind.specializes_iff.mp hy.le
    · exact hind.specializes_iff.mpr h'
  have hpos : 0 < Order.krullDim C.idealSheaf.subscheme := Order.krullDim_pos_iff.mpr ⟨_, _, hlt⟩
  rw [Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim] at hpos
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hpos.ne_bot
  rw [← hn] at hpos ⊢
  have hn0 : (0 : ℕ∞) < n := by exact_mod_cast hpos
  have h1 : (1 : ℕ∞) ≤ n := by
    by_contra hlt1
    exact (ENat.lt_one_iff_eq_zero.mp (not_le.mp hlt1) ▸ hn0).false
  exact_mod_cast h1

/-- **An antiample divisor is negative on curves.** If `-D` is Cartier and ample on a surface
`E ⊆ W` proper over `ℂ`, then `deg_C 𝒪_W(D) < 0` for every prime divisor `C` of `E`. -/
private theorem degreeOn_neg_of_isAmple {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsLocallyNoetherian W] [IsNormal W] [QuasiCompact (W ↘ Spec (.of ℂ))]
    (E : MMP.Mori.PrimeDivisor W) [IsProper (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))]
    (hdimE : topologicalKrullDim E.idealSheaf.subscheme = 2)
    (C : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme) (J : E.idealSheaf.subscheme.IdealSheafData)
    (hJ : J = C.idealSheaf) (hdim : topologicalKrullDim J.subscheme ≤ 1)
    [IsProper ((J.subschemeι ≫ E.idealSheaf.subschemeι) ≫ W ↘ Spec (.of ℂ))]
    (D : Divisor W) (hDc : MMP.Mori.Divisor.IsCartier D) (hD : MMP.Mori.Divisor.IsCartier (-D))
    (hamp : haveI : CompactSpace W :=
        (quasiCompact_iff_compactSpace (W ↘ Spec (.of ℂ))).mp inferInstance
      haveI := hD.isInvertibleModule_divisorialSheaf
      haveI := Stacks.InvertiblePullback.isInvertibleModule_pullback E.idealSheaf.subschemeι
        (MMP.Mori.Divisor.divisorialSheaf (-D))
      Stacks.Ample.IsAmple E.idealSheaf.subscheme
        ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
          (MMP.Mori.Divisor.divisorialSheaf (-D)))) :
    MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
      (J.subschemeι ≫ E.idealSheaf.subschemeι) hdim D hDc < 0 := by
  subst hJ
  haveI : CompactSpace W := (quasiCompact_iff_compactSpace (W ↘ Spec (.of ℂ))).mp inferInstance
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := E.integral
  haveI := C.integral
  have hneg := MMP.Mori.Divisor.degreeOn_neg' ℂ (W ↘ Spec (.of ℂ))
    (C.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι) hdim D hDc
  suffices h : 0 < MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ))
      (C.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι) hdim (-D) hDc.neg by
    omega
  change 0 < MMP.Mori.degreeOn ℂ (W ↘ Spec (.of ℂ))
      (C.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι) hdim
      (MMP.Mori.Divisor.divisorialSheaf (-D))
  rw [MMP.Threefold.Resolution.degreeOn_comp ℂ (W ↘ Spec (.of ℂ)) E.idealSheaf.subschemeι
    C.idealSheaf.subschemeι hdim, MMP.Mori.degreeOn_eq_invertibleCurveDegree]
  letI : E.idealSheaf.subscheme.Over (Spec (.of ℂ)) :=
    ⟨E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)⟩
  haveI : LocallyOfFiniteType (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
  have hdim1 : topologicalKrullDim C.idealSheaf.subscheme = 1 :=
    topologicalKrullDim_primeDivisor_eq_one (k := ℂ) hdimE C hdim
  haveI : AlgebraicGeometry.IsCurve ℂ
      (C.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := hdim1 }
  haveI := MMP.Mori.isInvertible_pullback_obj E.idealSheaf.subschemeι
    (MMP.Mori.Divisor.divisorialSheaf (-D))
  have h1 := (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hamp
  have h2 := isAmple_pullback_of_isFinite C.idealSheaf.subschemeι _ h1
  exact invertibleCurveDegree_pos_of_isAmple_of_isCurve ℂ _ hdim _ h2

end Antiample

/-! ### The coefficient of a surface coefficient system at a point -/

section PointCoeff

/-- The coefficient `a_{ij,x}` of a surface coefficient system at a point `x ∈ Eᵢ ∩ Eⱼ`,
`i ≠ j`, and `0` otherwise. -/
private noncomputable def pointCoeff {W : Scheme.{0}} {D : Divisor W} (a : DoubleSurface D → ℚ)
    (i j : {P : MMP.Mori.PrimeDivisor W // P ∈ D.support}) (x : W) : ℚ := by
  classical
  exact if h : i ≠ j ∧ x ∈ (i.1.support ∩ j.1.support : Set W) then
    coeffAlong a i.2 j.2 (fun e => h.1 (Subtype.ext e)) (Set.singleton_nonempty x)
      (Set.singleton_subset_iff.mpr h.2)
  else 0

private theorem pointCoeff_of_mem {W : Scheme.{0}} {D : Divisor W} (a : DoubleSurface D → ℚ)
    {i j : {P : MMP.Mori.PrimeDivisor W // P ∈ D.support}} {x : W}
    (h : i ≠ j ∧ x ∈ (i.1.support ∩ j.1.support : Set W)) :
    pointCoeff a i j x = coeffAlong a i.2 j.2 (fun e => h.1 (Subtype.ext e))
      (Set.singleton_nonempty x) (Set.singleton_subset_iff.mpr h.2) := by
  rw [pointCoeff, dif_pos h]

private theorem pointCoeff_eq {W : Scheme.{0}} {D : Divisor W} (a : DoubleSurface D → ℚ)
    (σ : DoubleSurface D) {x : W} (hx : x ∈ σ.carrier) :
    pointCoeff a ⟨σ.fst, σ.fst_mem⟩ ⟨σ.snd, σ.snd_mem⟩ x = a σ := by
  rw [pointCoeff_of_mem a ⟨fun e => σ.fst_ne_snd (congrArg Subtype.val e), σ.carrier_subset hx⟩]
  exact coeffAlong_eq a _ _ _ _ _ isPreconnected_singleton σ rfl rfl ⟨x, hx, rfl⟩

end PointCoeff

end Proof_lem_mmp_conductor_threefold_weighted_curve_identity

namespace MMP.Threefold

open MMP.Mori MMP.Fourfold
open Proof_lem_mmp_conductor_threefold_weighted_curve_identity

open Classical in
/-- **The weighted curve identity.** Let `W` be a smooth complex threefold, `D = ∑ᵢ mᵢ Eᵢ` a
divisor with all `mᵢ > 0` whose support is an snc divisor with proper components `Eᵢ`, such that
`-D` is Cartier with ample restriction to every `Eᵢ`, and let `a` be an oriented coefficient
system on the double curves of `D`, with divisors `Zᵢ = surfaceCoefficientDivisor a Eᵢ` and
`b_{ij,C} = a_{ij,C}/(mᵢ mⱼ)`. Then
`∑_{i<j, C} mᵢ mⱼ b_{ij,C}² (D · C)`
`  = ∑ᵢ Zᵢ²/mᵢ + ∑_{i<j<k, p} mᵢ mⱼ mₖ (b_{ij,p} - b_{ik,p} + b_{jk,p})²`,
where `C` runs over the double curves and `p` over the triple points; and if every `Zᵢ` has zero
class in `H_2(Eᵢ, ℚ)`, then `a = 0`. -/
@[mmp "lem_mmp_conductor_threefold_weighted_curve_identity"]
public theorem sum_doubleCurve_intersectionNumber_eq_and_eq_zero_of_cycleClass_eq_zero
    {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsLocallyNoetherian W]
    [IsNormal W]
    (hsm : SmoothOfRelativeDimension 3 (W ↘ Spec (.of ℂ)))
    (D : Divisor W) (hsnc : DivisorWithCoeffs.IsSNC (W ↘ Spec (.of ℂ)) D)
    (hDpos : ∀ P ∈ D.support, 0 < D.coeff P)
    (hproj : ∀ P ∈ D.support,
      IsProper (P.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ))))
    (hA : ∃ hD : (-D).IsCartier, ∀ P ∈ D.support,
      haveI : CompactSpace W := (quasiCompact_iff_compactSpace (W ↘ Spec (.of ℂ))).mp inferInstance
      haveI := hD.isInvertibleModule_divisorialSheaf
      haveI := Stacks.InvertiblePullback.isInvertibleModule_pullback P.idealSheaf.subschemeι
        (-D).divisorialSheaf
      Stacks.Ample.IsAmple P.idealSheaf.subscheme
        ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf))
    (a : DoubleSurface D → ℚ) (ha : a ∈ orientedSurfaceCoefficients D) :
    (∃ (hDq : (Divisor.toQDivisor D).IsQCartier)
      (hN : ∀ P ∈ D.support, IsNormal P.idealSheaf.subscheme)
      (hdim : ∀ σ : DoubleSurface D, topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subscheme ≤ 1)
      (hZ : ∀ P (hP : P ∈ D.support), haveI := hN P hP;
        (surfaceCoefficientDivisor a P).IsQCartier),
      (1 / 2 : ℚ) * (∑ᶠ σ : DoubleSurface D,
          haveI : IsProper (σ.fst.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ))) :=
            hproj σ.fst σ.fst_mem
          haveI : IsProper (((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι ≫
              σ.fst.idealSheaf.subschemeι) ≫ (W ↘ Spec (.of ℂ))) :=
            (by rw [Category.assoc]; infer_instance)
          (D.coeff σ.fst : ℚ) * D.coeff σ.snd *
            (a σ / (D.coeff σ.fst * D.coeff σ.snd)) ^ 2 *
            (Divisor.toQDivisor D).intersectionNumber ℂ (W ↘ Spec (.of ℂ))
              ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι ≫
                σ.fst.idealSheaf.subschemeι) (hdim σ) hDq) =
        (∑ᶠ σ : DoubleSurface D,
          haveI := hN σ.fst σ.fst_mem
          haveI : IsProper (σ.fst.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ))) :=
            hproj σ.fst σ.fst_mem
          a σ * (surfaceCoefficientDivisor a σ.fst).intersectionNumber ℂ
              (σ.fst.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ)))
              (Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι
              (hdim σ) (hZ σ.fst σ.fst_mem) / D.coeff σ.fst) +
        (1 / 6 : ℚ) * ∑ i : D.support, ∑ j : D.support, ∑ k : D.support,
          if h : i ≠ j ∧ i ≠ k ∧ j ≠ k then
            ∑ᶠ p : {p : W // p ∈ i.1.support ∩ j.1.support ∩ k.1.support},
              (D.coeff i : ℚ) * D.coeff j * D.coeff k *
                (coeffAlong a i.2 j.2 (fun e => h.1 (Subtype.ext e)) (Set.singleton_nonempty p.1)
                    (Set.singleton_subset_iff.mpr ⟨p.2.1.1, p.2.1.2⟩) / (D.coeff i * D.coeff j) -
                  coeffAlong a i.2 k.2 (fun e => h.2.1 (Subtype.ext e))
                    (Set.singleton_nonempty p.1)
                    (Set.singleton_subset_iff.mpr ⟨p.2.1.1, p.2.2⟩) / (D.coeff i * D.coeff k) +
                  coeffAlong a j.2 k.2 (fun e => h.2.2 (Subtype.ext e))
                    (Set.singleton_nonempty p.1)
                    (Set.singleton_subset_iff.mpr ⟨p.2.1.2, p.2.2⟩) / (D.coeff j * D.coeff k)) ^ 2
          else 0) ∧
    ((∀ P ∈ D.support, Chow.rationalCycleClass P.idealSheaf.subscheme 1
        (Finsupp.linearCombination ℚ
          (fun Q : Mori.PrimeDivisor P.idealSheaf.subscheme =>
            if h : Stacks.Chow.relativeDimension
                (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (P.idealSheaf.subscheme ↘ Spec (.of ℂ)) Q.genericPoint = 1 then
              Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
                (P.idealSheaf.subscheme ↘ Spec (.of ℂ)) 1 Q.genericPoint h else 0)
          (surfaceCoefficientDivisor a P)) = 0) → a = 0) := by
  classical
  haveI := hsm
  haveI : TopologicalSpace.NoetherianSpace W := MMP.Fourfold.noetherianSpace_of_isComplexScheme
  haveI : Fintype (DoubleSurface D) := @Fintype.ofFinite _ (finite_doubleSurface D)
  have hsmW : IsSmoothScheme (W ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isSmoothScheme_iff _).mpr (SmoothOfRelativeDimension.smooth 3 _)
  have hcomp : ∀ P ∈ D.support,
      MMP.Mori.IsVariety ℂ (P.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ))) ∧
        IsNormal P.idealSheaf.subscheme := by
    intro P hP
    haveI := hproj P hP
    haveI := P.integral
    exact ⟨{}, isNormal_of_isRegular _
      (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme (hsnc.1 P hP))⟩
  have hN : ∀ P ∈ D.support, IsNormal P.idealSheaf.subscheme := fun P hP => (hcomp P hP).2
  have hDq : (Divisor.toQDivisor D).IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsmW _
  have hdim : ∀ σ : DoubleSurface D, topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subscheme ≤ 1 := by
    intro σ
    haveI := hN σ.fst σ.fst_mem
    rw [← curveOn_idealSheaf hsnc σ.fst σ rfl]
    haveI := (curveOn hsnc σ.fst σ rfl).integral
    exact Stacks.ResolutionOfSurfaces.topologicalKrullDim_subscheme_le_one
      (topologicalKrullDim_component hsnc σ.fst_mem) _
      (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme
        (hsnc.1 _ σ.fst_mem) _)
  have hZ : ∀ P (hP : P ∈ D.support), haveI := hN P hP;
      (surfaceCoefficientDivisor a P).IsQCartier := fun P hP =>
    haveI := hN P hP
    MMP.Fourfold.isQCartier_of_isSmoothScheme (hsnc.1 P hP) _
  -- the combinatorial configuration of the double curves
  let c : SNCConfig {P : MMP.Mori.PrimeDivisor W // P ∈ D.support} (DoubleSurface D) W :=
    { fst := fun σ => ⟨σ.fst, σ.fst_mem⟩
      snd := fun σ => ⟨σ.snd, σ.snd_mem⟩
      swap := DoubleSurface.swap
      swap_swap := DoubleSurface.swap_swap
      fst_swap := fun _ => rfl
      snd_swap := fun _ => rfl
      fst_ne_snd := fun σ h => σ.fst_ne_snd (congrArg Subtype.val h)
      car := DoubleSurface.carrier
      car_swap := fun _ => rfl
      comp := fun i => (i.1.support : Set W)
      car_subset := fun σ => σ.carrier_subset
      exists_car := fun i j hij x hx =>
        ⟨DoubleSurface.through i.2 j.2 (fun e => hij (Subtype.ext e))
          (Set.singleton_nonempty x) (Set.singleton_subset_iff.mpr hx), rfl, rfl,
          DoubleSurface.subset_through _ _ _ _ _ isPreconnected_singleton rfl⟩
      eq_of_mem := fun σ τ h1 h2 x hσ hτ => by
        by_contra hne
        exact Set.disjoint_left.mp (DoubleSurface.disjoint_carrier (congrArg Subtype.val h1)
          (congrArg Subtype.val h2) hne) hσ hτ
      finite := fun i j k hij hik hjk => finite_inter_inter hsnc i.2 j.2 k.2
        (fun e => hij (Subtype.ext e)) (fun e => hik (Subtype.ext e))
        (fun e => hjk (Subtype.ext e)) }
  let m : {P : MMP.Mori.PrimeDivisor W // P ∈ D.support} → ℚ := fun i => (D.coeff i.1 : ℚ)
  have hm : ∀ i, m i ≠ 0 := fun i => by
    have := hDpos i.1 i.2
    simp only [m]
    exact_mod_cast this.ne'
  -- the self-intersections of the double curves on their components
  let s : DoubleSurface D → ℚ := fun τ =>
    haveI := hN τ.fst τ.fst_mem
    haveI := hproj τ.fst τ.fst_mem
    (MMP.Mori.Divisor.degreeOn ℂ (τ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (τ.fst.idealSheaf.subschemeι.base ⁻¹' τ.carrier))).subschemeι
      (hdim τ) (curveDivisor hsnc τ.fst τ)
      (MMP.Fourfold.isCartier_of_isSmoothScheme (hsnc.1 _ τ.fst_mem) _) : ℚ)
  have hfilt : ∀ σ : DoubleSurface D,
      Finset.univ.filter (fun τ : DoubleSurface D => τ.fst = σ.fst ∧ τ ≠ σ) =
        Finset.univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ) := fun σ =>
    Finset.filter_congr fun τ _ => by
      change _ ↔ (⟨τ.fst, τ.fst_mem⟩ : {P // P ∈ D.support}) = ⟨σ.fst, σ.fst_mem⟩ ∧ _
      rw [Subtype.mk.injEq]
  have hI : ∀ σ : DoubleSurface D,
      haveI : IsProper (σ.fst.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ))) :=
        hproj σ.fst σ.fst_mem
      haveI : IsProper (((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι ≫
          σ.fst.idealSheaf.subschemeι) ≫ (W ↘ Spec (.of ℂ))) :=
        (by rw [Category.assoc]; infer_instance)
      (Divisor.toQDivisor D).intersectionNumber ℂ (W ↘ Spec (.of ℂ))
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι ≫
          σ.fst.idealSheaf.subschemeι) (hdim σ) hDq =
      m (c.snd σ) * s σ + m (c.fst σ) * s (c.swap σ) +
        ∑ τ ∈ Finset.univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
          m (c.snd τ) * ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ) := by
    intro σ
    haveI := hN σ.fst σ.fst_mem
    haveI := hN σ.snd σ.snd_mem
    haveI := hproj σ.fst σ.fst_mem
    haveI := hproj σ.snd σ.snd_mem
    haveI : IsProper (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι ≫
        σ.fst.idealSheaf.subschemeι) ≫ W ↘ Spec (.of ℂ)) := by
      rw [Category.assoc]; infer_instance
    haveI : IsProper (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (σ.snd.idealSheaf.subschemeι.base ⁻¹' σ.swap.carrier))).subschemeι ≫
        σ.snd.idealSheaf.subschemeι) ≫ W ↘ Spec (.of ℂ)) := by
      rw [Category.assoc]; infer_instance
    rw [← hfilt σ]
    exact intersectionNumber_divisor_eq hsnc hsmW σ (hcomp _ σ.fst_mem).1 (hsnc.1 _ σ.fst_mem)
      (topologicalKrullDim_component hsnc σ.fst_mem) (hcomp _ σ.snd_mem).1
      (hsnc.1 _ σ.snd_mem) (topologicalKrullDim_component hsnc σ.snd_mem) _
      (curveOn_idealSheaf hsnc σ.fst σ rfl).symm _
      (curveOn_idealSheaf hsnc σ.snd σ.swap rfl).symm (hdim σ) (hdim σ.swap) hDq
  have hZσ : ∀ σ : DoubleSurface D,
      haveI := hN σ.fst σ.fst_mem
      haveI : IsProper (σ.fst.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ))) :=
        hproj σ.fst σ.fst_mem
      (surfaceCoefficientDivisor a σ.fst).intersectionNumber ℂ
          (σ.fst.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ)))
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι
          (hdim σ) (hZ σ.fst σ.fst_mem) =
        a σ * s σ + ∑ τ ∈ Finset.univ.filter (fun τ => c.fst τ = c.fst σ ∧ τ ≠ σ),
          a τ * ∑ᶠ x ∈ c.car σ ∩ c.car τ, (1 : ℚ) := by
    intro σ
    haveI := hN σ.fst σ.fst_mem
    haveI := hproj σ.fst σ.fst_mem
    rw [← hfilt σ]
    exact intersectionNumber_surfaceCoefficientDivisor_eq hsnc a σ (hcomp _ σ.fst_mem).1
      (hsnc.1 _ σ.fst_mem) (topologicalKrullDim_component hsnc σ.fst_mem) _
      (curveOn_idealSheaf hsnc σ.fst σ rfl).symm (hdim σ) (hZ σ.fst σ.fst_mem)
  have key := c.weighted_identity a ha m hm s (pointCoeff a)
    (fun σ x hx => pointCoeff_eq a σ hx)
  refine ⟨⟨hDq, hN, hdim, hZ, ?identity⟩, ?part2⟩
  case identity =>
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    convert key using 2
    · refine Finset.sum_congr rfl fun σ _ => ?_
      rw [hI σ]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      rw [hZσ σ]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => ?_
      by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k
      · rw [dif_pos h, SNCConfig.tri, dif_pos h, ← finsum_mem_eq_finite_toFinset_sum,
          ← finsum_set_coe_eq_finsum_mem]
        refine finsum_congr fun p => ?_
        dsimp only
        rw [pointCoeff_of_mem a ⟨h.1, p.2.1.1, p.2.1.2⟩,
          pointCoeff_of_mem a ⟨h.2.1, p.2.1.1, p.2.2⟩,
          pointCoeff_of_mem a ⟨h.2.2, p.2.1.2, p.2.2⟩]
      · rw [dif_neg h, SNCConfig.tri, dif_neg h, Finset.sum_empty]
  case part2 =>
    intro hcl
    obtain ⟨hDneg, hamp⟩ := hA
    have hDc : MMP.Mori.Divisor.IsCartier D := MMP.Fourfold.isCartier_of_isSmoothScheme hsmW D
    have hmpos : ∀ i, 0 < m i := fun i => by
      have := hDpos i.1 i.2
      simp only [m]
      exact_mod_cast this
    refine c.eq_zero_of_weighted a m hmpos _ _ ?hX ?hY (pointCoeff a) key
    case hX =>
      intro σ
      rw [← hI σ]
      haveI := hN σ.fst σ.fst_mem
      haveI := hproj σ.fst σ.fst_mem
      haveI : IsProper (((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι ≫
          σ.fst.idealSheaf.subschemeι) ≫ W ↘ Spec (.of ℂ)) := by
        rw [Category.assoc]; infer_instance
      rw [QDivisor.intersectionNumber_toQDivisor ℂ (W ↘ Spec (.of ℂ)) _ (hdim σ) D hDc hDq]
      exact_mod_cast degreeOn_neg_of_isAmple σ.fst (topologicalKrullDim_component hsnc σ.fst_mem)
        (curveOn hsnc σ.fst σ rfl) _ (curveOn_idealSheaf hsnc σ.fst σ rfl).symm (hdim σ) D hDc
        hDneg (hamp σ.fst σ.fst_mem)
    case hY =>
      intro σ
      rw [← hZσ σ]
      haveI := hN σ.fst σ.fst_mem
      haveI := hproj σ.fst σ.fst_mem
      haveI := σ.fst.integral
      have hsmE := hsnc.1 _ σ.fst_mem
      have hdimE := topologicalKrullDim_component hsnc σ.fst_mem
      haveI : CompactSpace W :=
        (quasiCompact_iff_compactSpace (W ↘ Spec (.of ℂ))).mp inferInstance
      haveI := hDneg.isInvertibleModule_divisorialSheaf
      haveI := Stacks.InvertiblePullback.isInvertibleModule_pullback σ.fst.idealSheaf.subschemeι
        (MMP.Mori.Divisor.divisorialSheaf (-D))
      haveI : IsProper (σ.fst.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
        inferInstanceAs (IsProper (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
      haveI : LocallyOfFiniteType (σ.fst.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
        inferInstanceAs (LocallyOfFiniteType (σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
      have hWp : AlgebraicGeometry.IsProjective (σ.fst.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
        MMP.isProjective_of_isProper_of_isRelativelyAmple _ _
          (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple _ _ (hamp σ.fst σ.fst_mem))
      have hJeq := curveOn_idealSheaf hsnc σ.fst σ rfl
      haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subscheme := by
        rw [← hJeq]; exact (curveOn hsnc σ.fst σ rfl).integral
      have hC1 : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subscheme = 1 := by
        have h1 := hdim σ
        rw [← hJeq] at h1 ⊢
        exact topologicalKrullDim_primeDivisor_eq_one (k := ℂ) hdimE _ h1
      haveI : IsProper ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι ≫
          σ.fst.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
        inferInstanceAs (IsProper ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (σ.fst.idealSheaf.subschemeι.base ⁻¹' σ.carrier))).subschemeι ≫
          σ.fst.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ)))
      exact intersectionNumber_eq_zero_of_curveDivisorClass_eq_zero (hcomp _ σ.fst_mem).1 hWp
        hsmE hdimE _ (hZ σ.fst σ.fst_mem)
        (fun S _ => MMP.Fourfold.isCartier_of_isSmoothScheme hsmE _) (hcl σ.fst σ.fst_mem) _ _ hC1

end MMP.Threefold
