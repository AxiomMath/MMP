module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyRestrictOpen
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ExceptionalValuations
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorBranchCounts
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.Properties.DimensionFunctionClosure
import MMP.AlgebraicGeometry.Normalization.IntegralScheme

/-!
# Branches, weights and unit drops across a small fourfold step

Let `Y⁻ → Z ← Y⁺` (by `f^±`) be a fourfold step diagram over `ℂ` in which both `f⁻` and `f⁺` are
small, with common biregular locus `U ⊆ Z`, base bad locus `Σ = Z ∖ U` and full bad loci
`W^± = (f^±)⁻¹(Σ)`. This file collects four facts about such a step, used to compare the
difficulty of the two sides of a flip in the termination argument for lc fourfolds.

**Normalizations of a divisor and of its strict transform.** Let `S⁻` be a prime divisor of
`Y⁻`, `S⁺` its strict transform on `Y⁺`, `ν^± : (S^±)^ν ⟶ S^± ⊆ Y^±` the normalizations and
`τ : T ⟶ Z` the normalization of the prime divisor `V = f⁻(S⁻)`. For each sign there is a
projective birational morphism `σ^± : (S^±)^ν ⟶ T` with `τ ∘ σ^± = f^± ∘ ν^±`: the composite
`(S^±)^ν ⟶ S^± ⟶ V` is a surjection from a normal integral scheme, so it lifts through `T`; it
is projective because `(S^±)^ν` is; and it is birational because `f^±` is an isomorphism near the
generic point of `S^±` (for `S⁻` because the exceptional set of `f⁻` has codimension two, for
`S⁺` by construction of the strict transform).

**Exceptional branches.** For any such `σ` and a prime divisor `P` of `(S^ε)^ν`,
`dim σ(P) ≤ 1` exactly when `ν^ε(P) ⊆ W^ε`; so the bad branches counted by
`MMP.Fourfold.badBranchCount` are the `σ`-exceptional prime divisors. The proof compares
heights of points, ordered by specialization. Let `η` be the generic point of `P`, `y = ν(η)`,
`z = f(y)` and `ζ = σ(η)`; as `σ` is universally closed, `dim σ(P) = height ζ`. Every point of `Σ`
has coheight at least three, since the fibre of `f^±` over it is infinite and so contains a
specialization starting in the exceptional set. If `z ∈ Σ` then `height ζ ≤ height z ≤ 1`, `τ`
being integral; otherwise `f` is an isomorphism over `z` and `height ζ ≥ height z = height y ≥
height η = 2`, `τ` being closed and `ν` integral.

**Weights outside the weighted bad set.** Let `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` be a small terminal flip of
a bridge of a prepared chain, with weighted bad set `𝒜₀`. A normalized divisorial valuation `v`
of `ℂ(Y⁻)` exceptional over `Y⁻` and not in `𝒜₀` gives the valuation `v⁺` of `ℂ(Y⁺)` with the
same restriction to `ℂ(Z)`; it is exceptional over `Y⁺`, as both maps are small, and
`w_v(Y⁻, Θ⁻) = w_v(Y⁺, Θ⁺)`. If the centre of `v` meets `(f⁻)⁻¹(U)`, the two pairs are isomorphic
over `U` and log discrepancies are local at the centre, so they agree; if it lies in `W⁻`, both
weights vanish because `v ∉ 𝒜₀`.

**The unit drop.** In a stabilized small klt tail `(X_i, B_i)` with a terminal chain and an
admissible scale `N`, let `w(u) = ⌈N max{u, 0}⌉` and let `v` be the generic blowup valuation of
an irreducible surface `V ⊆ W_i⁺ ⊆ X_{i+1}` along which `X_{i+1}` is smooth. Then
`w(2 - a(v; X_i, B_i)) ≥ w(2 - a(v; X_{i+1}, B_{i+1})) + 1`. Indeed
`a(v; X_{i+1}, B_{i+1}) = 2 - mult_{η_V} B_{i+1}` is `N`-integral, the coefficients of `B_{i+1}`
being sums of coefficients of `B_0`, and `a(v; X_i, B_i) < a(v; X_{i+1}, B_{i+1})` because the
centre of `v` lies in `W_i⁺`. The strict inequality is the strictness of the discrepancy
comparison along a step diagram, proved through the normalized graph `(G, u, v)` and its graph
divisor `H = u^*(K⁻ + B⁻) - v^*(K⁺ + B⁺)`: `a(ξ; Y⁺) - a(ξ; Y⁻) = ξ(H)`, `-H` is relatively ample
over `Z` and `H` vanishes over `U`, so by the negativity lemma `H ≥ 0` and `Supp H` contains the
preimage of `Σ`.

## Main results

* `MMP.Mori.isBirationalMorphism_of_bijective_functionFieldMap`: a surjective morphism of
  integral schemes, locally of finite type and inducing an isomorphism of function fields, is a
  birational morphism.
* `MMP.Fourfold.IsFourfoldStepDiagram.exists_normalization_comp_eq`: the morphisms `σ^±`.
* `MMP.Fourfold.IsFourfoldStepDiagram.topologicalKrullDim_image_le_one_iff`: for both signs,
  `dim σ(P) ≤ 1` if and only if `ν(P) ⊆ W`.
* `PreparedChain.isValuationWeight_target_iff_of_notMem_flipBadSet`, in the namespace
  `MMP.Fourfold.StabilizedSmallKltTail`: the weights of `v⁺` on `(Y⁺, Θ⁺)` are exactly the
  weight of `v` on `(Y⁻, Θ⁻)`.
* `MMP.Fourfold.StabilizedSmallKltTail.difficultyWeight_add_one_le_of_subset_badLocusPlusAt`:
  the unit drop.

## Implementation notes

* The normalizations are `MMP.Fourfold.primeDivisorNormalization`, composed with the closed
  immersion into the ambient scheme, so `τ ∘ σ = f ∘ ν` is an equality of morphisms to `Z`. The
  strict transform `S⁺` is a prime divisor `S'` with
  `MMP.Fourfold.flipTransformPrimeDivisor f⁻ f⁺ S = some S'`, and `f⁻(S⁻)` a prime divisor `V`
  of `Z` with support `f⁻(S⁻)`. The two signs are the two conjuncts of each statement.
* For the exceptional branches, the source shows that `σ` is an isomorphism near the generic
  point of `P` when `ν(P) ⊄ W`; only the consequence `dim σ(P) = 2` is proved here.
* Weights are the predicate `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`,
  which contains exceptionality over the model; the comparison of the weights says that those
  of `v⁺` are exactly the weight `w` of `v`. Of the source's graph comparison
  `a(v; Y⁺, Θ⁺) - a(v; Y⁻, Θ⁻) = v(H)` only the equality off `W⁻` is used there, and it is proved
  directly over `U`. When the flip ends a bridge its target is the next junction, identified
  with the last model of the bridge by an isomorphism, and the comparison goes through it.
* In the unit drop the valuation `v` of `k(X_{i+1})` is read on `X_i` as the valuation of
  `k(X_i)` with the same restriction to `k(Z_i)`
  (`MMP.Fourfold.StepSequence.IsTransportedValuation`); log discrepancies are the predicate
  `MMP.Fourfold.StepSequence.IsLogDiscrepancyAt`, and the inequality holds for every pair of
  values it admits. Smoothness at `η_V` is the regularity of `𝒪_{X_{i+1}, η_V}`, part of
  `MMP.Fourfold.IsSurfaceGenericBlowupValuation`.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][oai4]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.38, 3.39
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-- A surjective morphism, locally of finite type, of integral schemes inducing an isomorphism of
function fields is a birational morphism. -/
theorem isBirationalMorphism_of_bijective_functionFieldMap {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] (μ : X ⟶ T) [Surjective μ] [LocallyOfFiniteType μ]
    (hbij : Function.Bijective (functionFieldMap μ)) : IsBirationalMorphism μ := by
  let e := T.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant μ).symm)
  haveI : IsIso (e.hom ≫ μ.stalkMap (genericPoint X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI : IsIso (μ.stalkMap (genericPoint X)) := IsIso.of_isIso_comp_left e.hom _
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents T) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational μ
    (isBirational_of_isIso_stalkMap_genericPoint μ) (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE μ U V hU.nonempty hV.nonempty hUV hiso

end MMP.Mori

/-! ## The morphisms of normalizations -/

namespace MMP.Fourfold.BranchNormalization

open MMP.Mori MMP.Fourfold

/-- A morphism from a reduced scheme whose image lies in the support of an ideal sheaf `I`
kills `I`. -/
private theorem le_ker_of_range_subset {X Y : Scheme.{u}} [IsReduced X] (I : Y.IdealSheafData)
    (f : X ⟶ Y) (h : Set.range f ⊆ I.support) : I ≤ f.ker := by
  have hk : f.ker = Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range f)) := by
    rw [← Category.id_comp f, Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot_of_isIso,
      ← Scheme.nilradical_eq_bot, ← Scheme.IdealSheafData.vanishingIdeal_top,
      Scheme.IdealSheafData.map_vanishingIdeal]
    simp [Set.image_univ]
  rw [hk, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    TopologicalSpace.Closeds.closure_le]
  exact h

/-- A surjective morphism of integral schemes carries generic points to generic points. -/
private theorem mem_genericPoints_of_surjective {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (f : Z ⟶ X) [Surjective f] : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X := by
  rintro ⟨η, hη⟩
  have : η = genericPoint Z := by rwa [genericPoints_eq_singleton] at hη
  subst this
  change f (genericPoint Z) ∈ genericPoints X
  rw [genericPoint_eq_of_isDominant f, genericPoints_eq_singleton]; rfl

/-- If the stalk map of `f` at `x` is surjective, so is the residue field map. -/
private theorem surjective_residueFieldMap_of_surjective_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (h : Function.Surjective (f.stalkMap x).hom) :
    Function.Surjective (f.residueFieldMap x).hom := by
  intro z
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, rfl⟩ := h s
  refine ⟨Y.residue (f x) t, ?_⟩
  have := congrArg (fun φ => φ.hom t) (Scheme.residue_residueFieldMap f x)
  simpa using this

/-- **Birationality along a divisor.** Let `ιP : P ⟶ X` and `ιQ : Q ⟶ Y` be morphisms from
integral schemes with `ιP` surjective on stalks, and `r : P ⟶ Q` a dominant morphism over
`f : X ⟶ Y`. If `f` is an isomorphism of stalks at the image of the generic point of `P`, then
`r` induces an isomorphism of function fields. -/
private theorem bijective_functionFieldMap_of_isIso_stalkMap {P Q X Y : Scheme.{u}}
    [IsIntegral P] [IsIntegral Q] (ιP : P ⟶ X) (ιQ : Q ⟶ Y) [SurjectiveOnStalks ιP]
    (f : X ⟶ Y) (r : P ⟶ Q) [IsDominant r] (hr : r ≫ ιQ = ιP ≫ f)
    (hf : IsIso (f.stalkMap (ιP (genericPoint P)))) :
    Function.Bijective (functionFieldMap r) := by
  have hι := surjective_residueFieldMap_of_surjective_stalkMap ιP (genericPoint P)
    (SurjectiveOnStalks.stalkMap_surjective ιP _)
  have hfs := surjective_residueFieldMap_of_surjective_stalkMap f (ιP (genericPoint P))
    (ConcreteCategory.bijective_of_isIso (f.stalkMap _)).2
  have hres : Function.Surjective ((r ≫ ιQ).residueFieldMap (genericPoint P)).hom := by
    rw [hr, Scheme.residueFieldMap_comp]
    exact hι.comp hfs
  rw [Scheme.residueFieldMap_comp] at hres
  have h := congrArg DFunLike.coe (residueFieldMap_comp_genericResidueEquivOfDominant r)
  simp only [RingHom.coe_comp] at h
  have hbij : Function.Bijective (r.residueFieldMap (genericPoint P)).hom :=
    ⟨RingHom.injective _, Function.Surjective.of_comp (g := (ιQ.residueFieldMap _).hom) hres⟩
  exact (Function.Bijective.of_comp_iff' (genericResidueEquiv P).bijective _).mp
    (h ▸ hbij.comp (genericResidueEquivOfDominant r).bijective)

/-- In a commutative square `σ ≫ nQ = nP ≫ r` of dominant morphisms of integral schemes in which
`nP`, `nQ` and `r` induce isomorphisms of function fields, so does `σ`. -/
private theorem bijective_functionFieldMap_of_comp_eq {A B C D : Scheme.{u}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] [IsIntegral D] {σ : A ⟶ B} {nQ : B ⟶ D} {nP : A ⟶ C}
    {r : C ⟶ D} [IsDominant σ] [IsDominant nQ] [IsDominant nP] [IsDominant r]
    (h : σ ≫ nQ = nP ≫ r) (hP : Function.Bijective (functionFieldMap nP))
    (hQ : Function.Bijective (functionFieldMap nQ))
    (hr : Function.Bijective (functionFieldMap r)) :
    Function.Bijective (functionFieldMap σ) := by
  have hcomp : functionFieldMap σ ∘ functionFieldMap nQ =
      functionFieldMap nP ∘ functionFieldMap r := by
    ext t
    simp only [Function.comp_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr h]
  exact (Function.Bijective.of_comp_iff _ hQ).mp (hcomp ▸ hP.comp hr)

/-- The stalk map of `f` is an isomorphism at a point over the biregular locus of `f`. -/
private theorem isIso_stalkMap_of_mem_biregularLocus {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    (hx : x ∈ f ⁻¹ᵁ biregularLocus f) : IsIso (f.stalkMap x) := by
  haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  haveI : IsOpenImmersion (f ∣_ biregularLocus f) := inferInstance
  have h1 : IsIso ((f ∣_ biregularLocus f).stalkMap ⟨x, hx⟩) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap (f ∣_ biregularLocus f) ⟨x, hx⟩
  exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
    (morphismRestrictStalkMap f (biregularLocus f) ⟨x, hx⟩)).mp h1

/-- **The morphism of normalizations induced by a morphism birational along a prime divisor.**
Let `f : X ⟶ Y` be a morphism of varieties over `k` with `X` projective, `P` a prime divisor of
`X` whose generic point maps into the biregular locus of `f`, and `Q` a prime divisor of `Y` with
support `f(P)`. Then there is a projective birational morphism `σ : P^ν ⟶ Q^ν` with
`ν_Q ∘ σ = f ∘ ν_P`. -/
private theorem exists_normalization_comp_eq_of_mem_biregularLocus {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : AlgebraicGeometry.IsProjectiveVariety k sX) (hY : AlgebraicGeometry.IsVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hQ : (Q.support : Set Y) = f '' P.support)
    (hP : P.genericPoint ∈ f ⁻¹ᵁ biregularLocus f) :
    ∃ σ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme Q,
      IsProjectiveMorphism σ ∧ IsBirationalMorphism σ ∧
        σ ≫ primeDivisorNormalization Q = primeDivisorNormalization P ≫ f := by
  haveI := hX.toIsVariety
  haveI := P.integral
  haveI := Q.integral
  set IP := P.idealSheaf
  set IQ := Q.idealSheaf
  haveI hvP : AlgebraicGeometry.IsVariety k (IP.subschemeι ≫ sX) :=
    (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  haveI hvQ : AlgebraicGeometry.IsVariety k (IQ.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hspecP := MMP.Threefold.normalization_spec (IP.subschemeι ≫ sX)
  have hspecQ := MMP.Threefold.normalization_spec (IQ.subschemeι ≫ sY)
  set hXP := MMP.finite_irreducibleComponents_of_isIntegral
    IP.subscheme
  set hXQ := MMP.finite_irreducibleComponents_of_isIntegral
    IQ.subscheme
  set nP := IP.subscheme.normalization hXP
  set nQ := IQ.subscheme.normalization hXQ
  obtain ⟨⟨hvνP, hnormP, -, hsurjP, hbirP⟩, -, -, -, hprojP⟩ := hspecP
  obtain ⟨⟨hvνQ, hnormQ, -, hsurjQ, hbirQ⟩, ⟨UQ, hUQ, hisoQ⟩, -, -, -⟩ := hspecQ
  haveI : IsIntegral (IP.subscheme.normalizationScheme hXP) :=
    AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := nP ≫ IP.subschemeι ≫ sX)
  haveI : IsIntegral (IQ.subscheme.normalizationScheme hXQ) :=
    AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := nQ ≫ IQ.subschemeι ≫ sY)
  -- the morphism `r : P ⟶ Q` induced by `f`
  have hrange : Set.range (IP.subschemeι ≫ f) = (Q.support : Set Y) := by
    rw [hQ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι]
  let r := IQ.subschemeLift (IP.subschemeι ≫ f)
    (le_ker_of_range_subset IQ _ hrange.le)
  have hr : r ≫ IQ.subschemeι = IP.subschemeι ≫ f :=
    Scheme.IdealSheafData.subschemeLift_subschemeι _ _
  haveI : Surjective r := ⟨fun y => by
    obtain ⟨x, hx⟩ : IQ.subschemeι y ∈ Set.range (IP.subschemeι ≫ f) := by
      have hy : IQ.subschemeι y ∈ Set.range IQ.subschemeι := ⟨y, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι] at hy
      rw [hrange]; exact hy
    refine ⟨x, IQ.subschemeι.isClosedEmbedding.injective ?_⟩
    rw [← hx, ← hr]; rfl⟩
  -- the lift `σ`
  let q := nP ≫ r
  haveI : Surjective q := inferInstance
  obtain ⟨σ, hσ, -⟩ := Scheme.existsUnique_lift_normalization hXQ q
    (mem_genericPoints_of_surjective q)
  have hcomm' : σ ≫ nQ ≫ IQ.subschemeι = nP ≫ IP.subschemeι ≫ f := by
    rw [← Category.assoc, hσ]
    simp only [q, Category.assoc, hr]
  have hcomm : σ ≫ primeDivisorNormalization Q = primeDivisorNormalization P ≫ f := hcomm'
  -- projectivity
  haveI : AlgebraicGeometry.IsProjectiveVariety k (IP.subschemeι ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr
      ⟨inferInstance, (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp
        hX.isProjective⟩
  have hcompS : σ ≫ nQ ≫ IQ.subschemeι ≫ sY = nP ≫ IP.subschemeι ≫ sX := by
    rw [← hf]
    simpa only [Category.assoc] using congrArg (· ≫ sY) hcomm'
  have hproj : IsProjectiveMorphism σ := by
    refine IsProjectiveMorphism.of_comp σ (nQ ≫ IQ.subschemeι ≫ sY) ?_
    rw [hcompS]
    exact (hprojP inferInstance).isProjective
  refine ⟨σ, hproj, ?_, hcomm⟩
  -- birationality: `σ` maps the generic point to the generic point
  have hηQ : genericPoint IQ.subscheme ∈ UQ := by
    show genericPoint IQ.subscheme ∈ (UQ : Set IQ.subscheme)
    rw [hUQ]
    exact Field.instIsIntegrallyClosed IQ.subscheme.functionField
  have hinj : ∀ a b, nQ a ∈ UQ → nQ b ∈ UQ → nQ a = nQ b → a = b := by
    intro a b ha hb hab
    have := (nQ ∣_ UQ).isOpenEmbedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩)
      (Subtype.ext ((morphismRestrict_base_coe nQ UQ ⟨a, ha⟩).trans
        (hab.trans (morphismRestrict_base_coe nQ UQ ⟨b, hb⟩).symm)))
    exact congrArg Subtype.val this
  have hσgen : σ (genericPoint _) = genericPoint _ := by
    have h1 : nQ (σ (genericPoint _)) = genericPoint IQ.subscheme := by
      rw [← Scheme.Hom.comp_apply, hσ]
      exact genericPoint_eq_of_isDominant q
    have h2 : nQ (genericPoint _) = genericPoint IQ.subscheme := genericPoint_eq_of_isDominant nQ
    exact hinj _ _ (h1 ▸ hηQ) (h2 ▸ hηQ) (h1.trans h2.symm)
  haveI : IsDominant σ := ((tfae_isDominant_of_isIntegral σ).out 1 2).mpr hσgen
  haveI : IsProper σ := isProper_of_isProjectiveMorphism σ hproj
  haveI : Surjective σ := ⟨by
    have h := σ.denseRange.closure_range
    rw [σ.isClosedMap.isClosed_range.closure_eq] at h
    exact Set.range_eq_univ.mp h⟩
  haveI : LocallyOfFiniteType σ := by
    have : LocallyOfFiniteType (σ ≫ nQ ≫ IQ.subschemeι ≫ sY) := by
      rw [hcompS]; infer_instance
    exact LocallyOfFiniteType.of_comp this
  exact isBirationalMorphism_of_bijective_functionFieldMap σ
    (bijective_functionFieldMap_of_comp_eq (hσ.trans rfl) hbirP.functionFieldMap_bijective
      hbirQ.functionFieldMap_bijective
      (bijective_functionFieldMap_of_isIso_stalkMap IP.subschemeι IQ.subschemeι f r hr
        (isIso_stalkMap_of_mem_biregularLocus f hP)))

/-- The generic point of a prime divisor `P` of `X` is the generic point of its support. -/
private theorem isGenericPoint_genericPoint {X : Scheme.{u}} (P : MMP.Mori.PrimeDivisor X) :
    IsGenericPoint P.genericPoint (P.support : Set X) :=
  (AlgebraicGeometry.PrimeDivisor.support_eq_closure P).symm

/-- If the exceptional set of `f` has codimension at least two, the generic point of every prime
divisor lies over the biregular locus of `f`. -/
private theorem genericPoint_mem_preimage_biregularLocus {X Y : Scheme.{u}} {f : X ⟶ Y}
    (h : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∈ f ⁻¹ᵁ biregularLocus f := by
  by_contra hn
  have hmem : P.genericPoint ∈ (exceptionalSet f : Set X) := hn
  have hsub : ((IrreducibleCloseds.closureSingleton P.genericPoint : IrreducibleCloseds X) :
      Set X) ⊆ exceptionalSet f :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) (exceptionalSet f).isClosed
  have h2 := le_closedsCodimension_iff.mp h _ hsub
  rw [AlgebraicGeometry.PrimeDivisor.codimension_closureSingleton_genericPoint] at h2
  exact absurd h2 (by decide)

/-- A prime divisor whose support lies in the support of another prime divisor has the same
support: both have codimension one. -/
private theorem support_eq_of_support_subset {X : Scheme.{u}} {A B : MMP.Mori.PrimeDivisor X}
    (h : (A.support : Set X) ⊆ B.support) : (A.support : Set X) = B.support := by
  have hle : IrreducibleCloseds.closureSingleton A.genericPoint ≤
      IrreducibleCloseds.closureSingleton B.genericPoint := by
    change closure {A.genericPoint} ⊆ closure {B.genericPoint}
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact h
  rcases hle.lt_or_eq with hlt | heq
  · have hA := A.codimension_closureSingleton_genericPoint
    have hB := B.codimension_closureSingleton_genericPoint
    rw [codimension_eq_coheight] at hA hB
    have := Order.coheight_strictAnti hlt (by rw [hB]; decide)
    rw [hA, hB] at this
    exact absurd this (lt_irrefl _)
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact congrArg (fun T : IrreducibleCloseds X => (T : Set X)) heq

/-- The strict transform `S⁺` of a prime divisor `S` under `f⁻ : X⁻ ⟶ Z ← X⁺ : f⁺`, with `f⁺`
proper, maps onto the prime divisor `V = f⁻(S)` of `Z`, and its generic point lies over the
biregular locus of `f⁺`. -/
private theorem image_flipTransformPrimeDivisor {Xm Xp Z : Scheme.{u}} {fm : Xm ⟶ Z}
    {fp : Xp ⟶ Z} [IsProper fp] {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S')
    {V : MMP.Mori.PrimeDivisor Z} (hV : (V.support : Set Z) = fm '' S.support) :
    (V.support : Set Z) = fp '' S'.support ∧ S'.genericPoint ∈ fp ⁻¹ᵁ biregularLocus fp := by
  unfold flipTransformPrimeDivisor at hS'
  obtain ⟨E, hE, hE'⟩ := Option.bind_eq_some_iff.mp hS'
  -- `V = E`
  have hES : fm '' S.support ⊆ E.support := by
    rw [MMP.Mori.RationalMap.support_transformPrimeDivisor hE]
    refine subset_trans ?_ (MMP.Mori.RationalMap.image_subset_transform fm.toPartialMap rfl
      S.idealSheaf.support)
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, trivial⟩, hx, ?_⟩
    simp only [Scheme.Hom.toPartialMap]
    rfl
  have hVE : (V.support : Set Z) = E.support := support_eq_of_support_subset (hV ▸ hES)
  -- the strict transform on `X⁺`
  obtain ⟨hne, -⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp hE'
  have hS'supp : (S'.support : Set Xp) =
      closure (fp ⁻¹' ((E.support : Set Z) ∩ biregularLocus fp)) := by
    rw [support_inverseTransformPrimeDivisor hE']
    rfl
  have hηE : E.genericPoint ∈ (E.support : Set Z) ∩ biregularLocus fp :=
    ⟨(isGenericPoint_genericPoint E).mem,
      ((isGenericPoint_genericPoint E).mem_open_set_iff (biregularLocus fp).isOpen).mpr hne⟩
  haveI : IsIso (fp ∣_ biregularLocus fp) := isBiregular_biregularLocus fp
  obtain ⟨w, hw⟩ := (fp ∣_ biregularLocus fp).surjective ⟨E.genericPoint, hηE.2⟩
  have hfw : fp w.1 = E.genericPoint := by
    rw [← morphismRestrict_base_coe, hw]
  have hwS' : w.1 ∈ (S'.support : Set Xp) := by
    rw [hS'supp]
    exact subset_closure (show fp w.1 ∈ _ by rw [hfw]; exact hηE)
  refine ⟨?_, ?_⟩
  · rw [hVE]
    refine le_antisymm ?_ ?_
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal ?_ (fp.isClosedMap _ S'.idealSheaf.support.isClosed)
      rw [Set.singleton_subset_iff]
      exact ⟨w.1, hwS', hfw⟩
    · rw [hS'supp]
      refine (image_closure_subset_closure_image fp.continuous).trans
        (closure_minimal ?_ E.idealSheaf.support.isClosed)
      rintro _ ⟨x, hx, rfl⟩
      exact hx.1
  · exact ((isGenericPoint_genericPoint S').mem_open_set_iff (fp ⁻¹ᵁ biregularLocus fp).isOpen).mpr
      ⟨w.1, hwS', w.2⟩

end MMP.Fourfold.BranchNormalization

/-! ## Exceptional branches -/

namespace MMP.Fourfold.BadBranches

open Order MMP.Mori MMP.Fourfold

open MMP.Mori MMP.Fourfold

/-! ### Specialization and integral or closed morphisms -/

/-- **Incomparability.** Over an integral ring map, two comparable primes with the same
contraction are equal. -/
private theorem eq_of_le_of_comap_eq_of_isIntegral {R S : Type*} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) {P Q : Ideal S} [P.IsPrime] (hPQ : P ≤ Q)
    (h : P.comap φ = Q.comap φ) : P = Q := by
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hφ⟩
  by_contra hne
  exact (Ideal.IsIntegral.comap_lt_comap (R := R) (lt_of_le_of_ne hPQ hne)).ne h

/-- Incomparability on spectra. -/
private theorem eq_of_specializes_of_isIntegral_specMap {R S : CommRingCat} (φ : R ⟶ S)
    (hφ : φ.hom.IsIntegral) (p q : PrimeSpectrum S) (hpq : p ⤳ q)
    (hc : Spec.map φ p = Spec.map φ q) : p = q := by
  rw [← PrimeSpectrum.le_iff_specializes] at hpq
  exact PrimeSpectrum.ext (eq_of_le_of_comap_eq_of_isIntegral _ hφ hpq
    (congrArg PrimeSpectrum.asIdeal hc))

/-- Incomparability for an integral morphism of affine schemes. -/
private theorem eq_of_specializes_of_isIntegralHom_of_isAffine {X Z : Scheme.{u}} [IsAffine X]
    [IsAffine Z] (f : X ⟶ Z) [IsIntegralHom f] {t t' : X} (h : t ⤳ t') (he : f t = f t') :
    t = t' := by
  have hg : (f.appTop).hom.IsIntegral := f.isIntegral_app ⊤ (isAffineOpen_top Z)
  have hc : (Spec.map f.appTop) (X.isoSpec.hom t) = (Spec.map f.appTop) (X.isoSpec.hom t') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, he]
  have heq := congrArg X.isoSpec.inv (eq_of_specializes_of_isIntegral_specMap _ hg _ _
    (h.map X.isoSpec.hom.continuous) hc)
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at heq

/-- **Incomparability.** The fibres of an integral morphism carry no nontrivial
specializations. -/
private theorem eq_of_specializes_of_isIntegralHom {X Z : Scheme.{u}} (f : X ⟶ Z)
    [IsIntegralHom f] {t t' : X} (h : t ⤳ t') (he : f t = f t') : t = t' := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f t')) isOpen_univ
  have ht' : t' ∈ f ⁻¹ᵁ U := hmem
  have ht : t ∈ f ⁻¹ᵁ U := h.mem_open (f ⁻¹ᵁ U).isOpen ht'
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hU.preimage f
  let a : (f ⁻¹ᵁ U).toScheme := ⟨t, ht⟩
  let b : (f ⁻¹ᵁ U).toScheme := ⟨t', ht'⟩
  have hab : a ⤳ b := subtype_specializes_iff _ _ |>.2 h
  have hfab : (f ∣_ U) a = (f ∣_ U) b := Subtype.ext
    ((morphismRestrict_base_coe f U a).trans (he.trans (morphismRestrict_base_coe f U b).symm))
  exact congrArg Subtype.val (eq_of_specializes_of_isIntegralHom_of_isAffine (f ∣_ U) hab hfab)

/-- An integral morphism is strictly monotone for the specialization orders. -/
private theorem strictMono_of_isIntegralHom {X Z : Scheme.{u}} (f : X ⟶ Z) [IsIntegralHom f] :
    StrictMono f := by
  intro a b hab
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab ⊢
  refine ⟨hab.1.map f.continuous, fun h => hab.2 ?_⟩
  rw [eq_of_specializes_of_isIntegralHom f hab.1 ((hab.1.map f.continuous).antisymm h).eq]

/-- An integral morphism does not decrease heights: a chain of specializations of `x` maps to a
chain of specializations of `f x`. -/
private theorem height_le_height_map_of_isIntegralHom {X Z : Scheme.{u}} (f : X ⟶ Z)
    [IsIntegralHom f] (x : X) : height x ≤ height (f x) :=
  height_le_height_apply_of_strictMono _ (strictMono_of_isIntegralHom f) x

/-- A closed morphism does not increase heights: a chain of specializations of `f x` lifts to a
chain of specializations of `x`. -/
private theorem height_map_le_of_isClosedMap {X Z : Scheme.{u}} (f : X ⟶ Z)
    (hf : IsClosedMap f) (x : X) : height (f x) ≤ height x := by
  have hsp : SpecializingMap f := hf.specializingMap
  suffices H : ∀ n : ℕ, ∀ x : X, (n : ℕ∞) ≤ height (f x) → (n : ℕ∞) ≤ height x from
    ENat.forall_natCast_le_iff_le.mp fun n hn => H n x hn
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro x hx
    obtain ⟨p, hp, hlen⟩ := Order.exists_series_of_le_height (f x) hx
    have hlen0 : p.length ≠ 0 := by omega
    have hb : p.eraseLast.last < f x := hp ▸ p.eraseLast_last_rel_last hlen0
    have hnb : (n : ℕ∞) ≤ height p.eraseLast.last := by
      have := Order.length_le_height_last (p := p.eraseLast)
      rwa [RelSeries.eraseLast_length, hlen, Nat.add_sub_cancel] at this
    obtain ⟨x', hxx', hfx'⟩ := hsp (Scheme.le_iff_specializes.mp hb.le)
    have hlt : x' < x := by
      refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxx') fun h => hb.ne ?_
      rw [← hfx', (hxx'.antisymm (Scheme.le_iff_specializes.mp h)).eq]
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ height x' + 1 := by gcongr; exact ih x' (hfx' ▸ hnb)
      _ ≤ height x := Order.height_add_one_le hlt

/-- Two elements of `ℕ∞` with finite sum are finite. -/
private theorem exists_eq_natCast_of_add_eq {a b : ℕ∞} {n : ℕ} (h : a + b = n) :
    ∃ a' b' : ℕ, a = a' ∧ b = b' ∧ a' + b' = n := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h
    | coe b => exact ⟨a, b, rfl, rfl, by exact_mod_cast h⟩

/-! ### Heights, coheights and dimensions -/

/-- On an integral scheme locally of finite type over a field, the height and the coheight of a
point add up to the dimension. -/
private theorem height_add_coheight_eq {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (y : Y) :
    ((height y : ℕ∞) : WithBot ℕ∞) + coheight y = topologicalKrullDim Y := by
  rw [← AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height]
  exact MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY y

/-- On an integral scheme locally of finite type over a field, the height of any point is at most
the height plus the coheight of any other point, both sums being the dimension. -/
private theorem height_le_height_add_coheight {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (x y : Y) :
    height x ≤ height y + coheight y := by
  have h := height_add_coheight_eq sY x
  rw [← height_add_coheight_eq sY y] at h
  exact le_self_add.trans_eq (by exact_mod_cast h)

/-- `height_add_coheight_eq` on a scheme of known finite dimension, as an equation in `ℕ`. -/
private theorem exists_height_coheight_eq {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {n : ℕ}
    (hn : topologicalKrullDim Y = n) (y : Y) :
    ∃ a b : ℕ, height y = a ∧ coheight y = b ∧ a + b = n := by
  have h := height_add_coheight_eq sY y
  rw [hn] at h
  exact exists_eq_natCast_of_add_eq (by exact_mod_cast h)

/-- On two schemes of the same finite dimension, points of equal coheight have equal height. -/
private theorem height_eq_of_coheight_eq {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sY' : Y' ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    [IsIntegral Y'] [LocallyOfFiniteType sY'] {n : ℕ} (hY : topologicalKrullDim Y = n)
    (hY' : topologicalKrullDim Y' = n) {y : Y} {y' : Y'} (h : coheight y = coheight y') :
    height y = height y' := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq sY hY y
  obtain ⟨a', b', ha', hb', hab'⟩ := exists_height_coheight_eq sY' hY' y'
  rw [h, hb'] at hb
  have : b = b' := by exact_mod_cast hb.symm
  rw [ha, ha']
  norm_cast
  omega

/-- On a scheme of dimension four, a point of coheight at least three has height at most one. -/
private theorem height_le_one_of_three_le_coheight {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hY : topologicalKrullDim Y = 4) {y : Y} (hy : 3 ≤ coheight y) : height y ≤ 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq sY (n := 4) hY y
  rw [hb] at hy
  have : 3 ≤ b := by exact_mod_cast hy
  rw [ha]
  exact_mod_cast (by omega : a ≤ 1)

/-! ### Points of the base bad locus -/

/-- If a small morphism `f : X ⟶ Z` of varieties of the same dimension is not an isomorphism over
any neighbourhood of `z`, then `z` has coheight at least three. -/
private theorem three_le_coheight_of_notMem_biregularLocus {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    (hdim : topologicalKrullDim X = topologicalKrullDim Z) {z : Z}
    (hz : z ∉ biregularLocus f) : 3 ≤ coheight z := by
  have hX := hf.isNormalVariety_source.1
  have hZ := hf.isNormalVariety_target.1
  haveI := hf.isNormalVariety_target.2
  haveI := hX.toIsIntegral
  haveI := hZ.toIsIntegral
  haveI := hf.isProper
  have hb : IsBirational f :=
    MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf.isBirationalMorphism
  -- the fibre over `z` is infinite, hence positive-dimensional
  have hinf : ¬ (f ⁻¹' {z}).Finite := by
    intro hfin
    obtain ⟨hO, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1
      inferInstance
    exact hz (le_biregularLocus (V := ⟨_, hO⟩) hiso hfin)
  have hpos : ¬ topologicalKrullDim (f.fiber z) ≤ 0 := by
    intro h0
    refine hinf (MMP.Resolution.Bridges.finite_preimage_singleton_of_topologicalKrullDim_le f z ?_)
    rwa [← IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo z).isHomeomorph]
  -- a proper specialization `x ⤳ x'` inside the fibre
  rw [show topologicalKrullDim (f.fiber z) = krullDim (f.fiber z) from
    Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints] at hpos
  obtain ⟨a, b, hab⟩ : ∃ a b : f.fiber z, a < b := by
    by_contra! hne
    exact hpos (Order.krullDim_nonpos_iff_forall_isMax.mpr fun a c hac =>
      not_not.mp fun h => hne a c (lt_of_le_not_ge hac h))
  set e := f.fiberHomeo z
  set x : X := (e b : X)
  set x' : X := (e a : X)
  have hfx : f x = z := (e b).2
  have hfx' : f x' = z := (e a).2
  have hsp : x ⤳ x' := by
    have h1 : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
    exact (subtype_specializes_iff _ _).mp (h1.map e.continuous)
  have hne : x' ≠ x := fun h => hab.ne (e.injective (Subtype.ext h))
  have hlt : x' < x := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp) fun h =>
    hne (hsp.antisymm (Scheme.le_iff_specializes.mp h)).eq.symm
  -- `x` lies in the exceptional set, of codimension at least two
  have hxex : x ∈ exceptionalSet f := fun hmem => hz (hfx ▸ hmem)
  have h2 : 2 ≤ coheight x :=
    MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hf.two_le_codimension hxex
  have h4 : coheight x' ≤ coheight (f x') :=
    MMP.Flips.coheight_le_coheight_map sZ sX hZ hX f hf.comp_eq hdim x'
  rw [hfx'] at h4
  calc (3 : ℕ∞) = 2 + 1 := by norm_num
    _ ≤ coheight x + 1 := by gcongr
    _ ≤ coheight z := (Order.coheight_add_one_le hlt).trans h4

/-! ### One sign -/

/-- On a variety `X` of dimension four, the generic point of a prime divisor of the normalization
of a prime divisor of `X` has height at least two. -/
private theorem two_le_height_genericPoint_primeDivisorNormalization {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsVariety ℂ sX) (hdimX : topologicalKrullDim X = 4)
    (S : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S)) :
    2 ≤ height P.genericPoint := by
  have := hX
  have := hX.toIsIntegral
  have := hX.toLocallyOfFiniteType
  have := S.integral
  set ν := primeDivisorNormalization S
  set IS := S.idealSheaf
  have hvS : AlgebraicGeometry.IsVariety ℂ (IS.subschemeι ≫ sX) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨hvN, -, -, hsurjN, -⟩, -, -, -, -⟩ :=
    MMP.Threefold.normalization_spec (IS.subschemeι ≫ sX)
  set sN : primeDivisorNormalizationScheme S ⟶ Spec (.of ℂ) := ν ≫ sX
  have hvN' : AlgebraicGeometry.IsVariety ℂ sN := hvN
  have : IsIntegral (primeDivisorNormalizationScheme S) := hvN'.toIsIntegral
  have : LocallyOfFiniteType sN := hvN'.toLocallyOfFiniteType
  obtain ⟨g', hg'⟩ : ∃ g', ν g' = S.genericPoint := by
    obtain ⟨s, hs⟩ : S.genericPoint ∈ Set.range IS.subschemeι := by
      rw [IS.range_subschemeι]
      exact (show S.genericPoint ∈ (S.support : Set X) from
        (AlgebraicGeometry.PrimeDivisor.support_eq_closure S).symm ▸ subset_closure rfl)
    obtain ⟨g', rfl⟩ := hsurjN.surj s
    exact ⟨g', hs⟩
  have hhg : height S.genericPoint = 3 := by
    obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq sX (n := 4) hdimX S.genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint S] at hb
    have : b = 1 := by exact_mod_cast hb.symm
    rw [ha]
    norm_cast
    omega
  have hg'3 : 3 ≤ height g' := hhg ▸ hg' ▸ height_map_le_of_isClosedMap ν ν.isClosedMap g'
  have h := hg'3.trans (height_le_height_add_coheight sN g' P.genericPoint)
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P] at h
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h

/-- For a small morphism `f : X ⟶ Z` of varieties of dimension four, an open `U ⊆ Z` over which
`f` is an isomorphism and whose complement consists of points of coheight at least three, a
prime divisor `S` of `X`, a prime divisor `V` of `Z` and a morphism `σ` of normalizations over
`f`, a prime divisor `P` of `S^ν` has `dim σ(P) ≤ 1` exactly when `ν(P) ⊆ f⁻¹(Z ∖ U)`. -/
private theorem topologicalKrullDim_image_le_one_iff_of_isSmallMorphism {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    (hdimX : topologicalKrullDim X = 4) (hdimZ : topologicalKrullDim Z = 4) (U : Z.Opens)
    (hU : U ≤ biregularLocus f) (hbad : ∀ z : Z, z ∉ U → 3 ≤ coheight z)
    (S : MMP.Mori.PrimeDivisor X) (V : MMP.Mori.PrimeDivisor Z)
    (σ : primeDivisorNormalizationScheme S ⟶ primeDivisorNormalizationScheme V)
    (hσ : σ ≫ primeDivisorNormalization V = primeDivisorNormalization S ≫ f)
    (P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S)) :
    topologicalKrullDim (σ.base '' P.support) ≤ 1 ↔
      primeDivisorNormalization S '' P.support ⊆ f ⁻¹' (U : Set Z)ᶜ := by
  have hX := hf.isNormalVariety_source.1
  have hZ := hf.isNormalVariety_target.1
  have := hX
  have := hX.toIsIntegral
  have := hZ.toIsIntegral
  have := hX.toLocallyOfFiniteType
  have := hZ.toLocallyOfFiniteType
  have := hf.isProper
  have := S.integral
  set ν := primeDivisorNormalization S with hν
  set τ := primeDivisorNormalization V with hτ
  set η := P.genericPoint
  have hPsupp : (P.support : Set _) = closure {η} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure P
  set ζ := σ η
  have hτζ : τ ζ = f (ν η) := by
    rw [← Scheme.Hom.comp_apply, hσ, Scheme.Hom.comp_apply]
  have : UniversallyClosed (σ ≫ τ) := by rw [hσ]; infer_instance
  have : UniversallyClosed σ := UniversallyClosed.of_comp_of_isSeparated σ τ
  have himage : σ.base '' P.support = closure {ζ} := by
    rw [hPsupp, ← σ.isClosedMap.closure_image_eq_of_continuous σ.continuous, Set.image_singleton]
  have hdimσ : topologicalKrullDim (σ.base '' P.support) = height ζ := by
    rw [himage]
    exact AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height ζ
  have hW : ν '' P.support ⊆ f ⁻¹' (U : Set Z)ᶜ ↔ f (ν η) ∉ U := by
    constructor
    · intro h
      exact h ⟨η, by rw [hPsupp]; exact subset_closure rfl, rfl⟩
    · rintro h _ ⟨a, ha, rfl⟩ hfa
      rw [hPsupp] at ha
      have hsp : η ⤳ a := specializes_iff_mem_closure.mpr ha
      exact h (((hsp.map ν.continuous).map f.continuous).mem_open U.isOpen hfa)
  rw [hdimσ, hW]
  constructor
  · intro hle hU'
    apply not_lt.mpr hle
    have hfνη : height (f (ν η)) = height (ν η) := height_eq_of_coheight_eq sZ sX (n := 4)
      hdimZ hdimX (MMP.Positivity.coheight_map_of_mem_biregularLocus f (hU hU'))
    have hζ : height (f (ν η)) ≤ height ζ := hτζ ▸ height_map_le_of_isClosedMap τ τ.isClosedMap ζ
    have : (2 : ℕ∞) ≤ height ζ :=
      (two_le_height_genericPoint_primeDivisorNormalization hX hdimX S P).trans
        ((height_le_height_map_of_isIntegralHom ν η).trans (hfνη ▸ hζ))
    calc ((1 : ℕ∞) : WithBot ℕ∞) < ((2 : ℕ∞) : WithBot ℕ∞) := by norm_cast
      _ ≤ (height ζ : WithBot ℕ∞) := by exact_mod_cast this
  · intro hnot
    have hζ : height ζ ≤ height (f (ν η)) := hτζ ▸ height_le_height_map_of_isIntegralHom τ ζ
    have : height ζ ≤ 1 := hζ.trans (height_le_one_of_three_le_coheight sZ hdimZ (hbad _ hnot))
    exact_mod_cast this

end MMP.Fourfold.BadBranches

namespace MMP.Fourfold

open MMP.Mori

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

open BranchNormalization in
/-- In a fourfold step diagram `Y⁻ → Z ← Y⁺` in which both `f⁻` and `f⁺` are small, let `S` be a
prime divisor of `Y⁻`, `S'` its strict transform on `Y⁺` and `V` the prime divisor `f⁻(S)` of
`Z`. Then the normalizations `S^ν`, `S'^ν` both map to the normalization `T` of `V` by projective
birational morphisms `σ^±` with `τ ∘ σ⁻ = f⁻ ∘ ν⁻` and `τ ∘ σ⁺ = f⁺ ∘ ν⁺`. -/
@[mmp "lem_oai4_c3_label_normalization_morphism"]
public theorem IsFourfoldStepDiagram.exists_normalization_comp_eq
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm)
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S')
    {V : MMP.Mori.PrimeDivisor Z} (hV : (V.support : Set Z) = fm '' S.support) :
    (∃ σ : primeDivisorNormalizationScheme S ⟶ primeDivisorNormalizationScheme V,
      IsProjectiveMorphism σ ∧ IsBirationalMorphism σ ∧
        σ ≫ primeDivisorNormalization V = primeDivisorNormalization S ≫ fm) ∧
    (∃ σ : primeDivisorNormalizationScheme S' ⟶ primeDivisorNormalizationScheme V,
      IsProjectiveMorphism σ ∧ IsBirationalMorphism σ ∧
        σ ≫ primeDivisorNormalization V = primeDivisorNormalization S' ≫ fp) := by
  have hZ : AlgebraicGeometry.IsVariety ℂ sZ := h.isProjectiveVariety_target.toIsVariety
  haveI : IsProper fp := h.isProper_plus
  obtain ⟨hV', hP'⟩ := image_flipTransformPrimeDivisor hS' hV
  exact ⟨exists_normalization_comp_eq_of_mem_biregularLocus h.isProjectiveVariety_minus hZ
      h.comp_eq_minus hV (genericPoint_mem_preimage_biregularLocus hm.two_le_codimension S),
    exists_normalization_comp_eq_of_mem_biregularLocus h.isProjectiveVariety_plus hZ
      h.comp_eq_plus hV' hP'⟩

open Order BadBranches in
/-- In a fourfold step diagram `Y⁻ → Z ← Y⁺` in which both `f⁻` and `f⁺` are small, let `S` be a
prime divisor of `Y⁻`, `S'` its strict transform on `Y⁺` and `V` the prime divisor `f⁻(S)` of
`Z`. For any morphism `σ` from the normalization of `S` (resp. `S'`) to the normalization of `V`
over `f⁻` (resp. `f⁺`), a prime divisor `P` of the source has image `σ(P)` of dimension at most
one if and only if its image in `Y⁻` (resp. `Y⁺`) lies in the bad locus `W⁻` (resp. `W⁺`). -/
@[mmp "lem_oai4_c3_bad_branches_exceptional"]
public theorem IsFourfoldStepDiagram.topologicalKrullDim_image_le_one_iff
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm)
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S')
    {V : MMP.Mori.PrimeDivisor Z} (hV : (V.support : Set Z) = fm '' S.support) :
    (∀ σ : primeDivisorNormalizationScheme S ⟶ primeDivisorNormalizationScheme V,
      σ ≫ primeDivisorNormalization V = primeDivisorNormalization S ≫ fm →
      ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S),
        topologicalKrullDim (σ.base '' P.support) ≤ 1 ↔
          primeDivisorNormalization S '' P.support ⊆ badLocusMinus fm fp) ∧
    (∀ σ : primeDivisorNormalizationScheme S' ⟶ primeDivisorNormalizationScheme V,
      σ ≫ primeDivisorNormalization V = primeDivisorNormalization S' ≫ fp →
      ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S'),
        topologicalKrullDim (σ.base '' P.support) ≤ 1 ↔
          primeDivisorNormalization S' '' P.support ⊆ badLocusPlus fm fp) := by
  have hp := h.isSmallMorphism_plus
  have hdimZ : topologicalKrullDim Z = 4 := by
    haveI : MMP.Mori.IsVariety ℂ sZ := hm.isNormalVariety_target.1
    haveI : MMP.Mori.IsVariety ℂ sXm := hm.isNormalVariety_source.1
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sXm
      hm.isBirationalMorphism]
    exact h.dim_minus
  have hbad : ∀ z : Z, z ∉ commonBiregularLocus fm fp → 3 ≤ coheight z := by
    intro z hz
    by_cases hzm : z ∈ biregularLocus fm
    · have hzp : z ∉ biregularLocus fp := fun hzp => hz ⟨hzm, hzp⟩
      exact three_le_coheight_of_notMem_biregularLocus hp (h.dim_plus.trans hdimZ.symm) hzp
    · exact three_le_coheight_of_notMem_biregularLocus hm (h.dim_minus.trans hdimZ.symm) hzm
  exact ⟨fun σ hσ P => topologicalKrullDim_image_le_one_iff_of_isSmallMorphism hm h.dim_minus
      hdimZ _ inf_le_left hbad S V σ hσ P,
    fun σ hσ P => topologicalKrullDim_image_le_one_iff_of_isSmallMorphism hp h.dim_plus
      hdimZ _ inf_le_right hbad S' V σ hσ P⟩

end MMP.Fourfold

/-! ## Weights across a flip -/

namespace MMP.Fourfold.FlipWeights

open MMP.Mori MMP.Fourfold

/-! ### Divisors over a variety seen over a birational model -/

section CompProper

variable {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- A divisor `(W, h, E)` over `X`, with `h` proper, seen over `X'` through a proper birational
morphism `g : X ⟶ X'` over `ℂ`: the divisor `(W, g ∘ h, E)`. -/
private noncomputable def compProper {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) : DivisorOver ℂ sX' where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by
    rw [Category.assoc, hs]
    exact D.isNormalVariety
  isBirationalMorphism := by
    haveI := D.isIntegral
    haveI := hD
    exact isBirationalMorphism_comp_of_isBirational g D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  E := D.E

/-- The divisor `(W, g ∘ h, E)` has the valuation `ord_E` read on `k(X')` through `g`. -/
private theorem valuation_compProper {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) :
    haveI := hg.isDominant
    (compProper g hg hs D hD).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := hg.isDominant
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ g) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

end CompProper

/-! ### Transport of log discrepancies along an isomorphism -/

section Iso

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- Under an isomorphism `f : Y ⟶ X`, every prime divisor `Γ` of `X` is the image of a prime
divisor `P` of `Y`: `f(η_P) = η_Γ`. -/
private theorem exists_primeDivisor_map_genericPoint_eq (f : Y ⟶ X) [IsIso f]
    (Γ : MMP.Mori.PrimeDivisor X) :
    ∃ P : MMP.Mori.PrimeDivisor Y, f P.genericPoint = Γ.genericPoint := by
  set x : Y := (inv f) Γ.genericPoint
  have hx : f x = Γ.genericPoint := by
    simp only [x]
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Γ.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx⟩

/-- **Rational top forms descend along a birational morphism.** If `f : X ⟶ Z` induces an
isomorphism of function fields, every rational top form on `X` is the pull-back `f^* τ` of a
rational top form `τ` on `Z`. -/
private theorem exists_pullbackRationalPluriForms_eq {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sZ] (f : X ⟶ Z) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {n : ℕ}
    (hd : letI := functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
    (ω : RationalPluriForms (f ≫ sZ) n 1) :
    ∃ τ : RationalPluriForms sZ n 1, pullbackRationalPluriForms sZ f τ = ω := by
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sZ f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1).repr ω ())
  refine ⟨g • ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1 (), ?_⟩
  change pullbackForms (K := Z.functionField) (K' := X.functionField) 1 _ = ω
  rw [pullbackForms_eq hω₀, pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  change functionFieldMap f g • _ = ω
  rw [hg]
  exact basis_unit_repr_smul _ ω

/-- **Log discrepancies are preserved by isomorphisms of pairs.** Let `f : Y ⟶ X` be an
isomorphism carrying the boundary `B_Y` of `Y` to the boundary `B` of `X`, and let `X` have a
canonical divisor of dimension `n`. Then a log discrepancy `a` of a proper divisor `(W, g, E)`
over `(Y, B_Y)` is the log discrepancy of `(W, f ∘ g, E)` over `(X, B)`. -/
private theorem isLogDiscrepancy_compIso [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    (f : Y ⟶ X) [IsIso f] {n : ℕ} {K₀ : Divisor X} (hK₀ : K₀.IsCanonicalDivisor sX n)
    {B : QDivisor X} {BY : QDivisor Y}
    (hB : ∀ (P : MMP.Mori.PrimeDivisor Y) (Γ : MMP.Mori.PrimeDivisor X),
      f P.genericPoint = Γ.genericPoint → BY.coeff P = B.coeff Γ)
    {D : DivisorOver ℂ (f ≫ sX)} (hD : IsProper D.f) {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy (f ≫ sX) n (QDivisor.toRDivisor BY) D a) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      (compProper f (isBirationalMorphism_of_isIso f) rfl D hD) a := by
  obtain ⟨hYv, -, ω, hω0, -, m, r, C, C', hCc, hsum, hpb, rfl⟩ := h
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := hD
  have hs : inv f ≫ f ≫ sX = sX := by simp
  have hXv : IsNormalVariety ℂ sX := by
    refine ⟨(isVariety_iff ℂ sX).2 ⟨inferInstance, ?_, ?_, ?_⟩, inferInstance⟩
    · haveI := hYv.1.toIsSeparated
      rw [← hs]
      infer_instance
    · haveI := hYv.1.toLocallyOfFiniteType
      rw [← hs]
      infer_instance
    · haveI := hYv.1.toQuasiCompact
      rw [← hs]
      infer_instance
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have hn : topologicalKrullDim X = n := hK₀.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := (isBirationalMorphism_of_isIso f).functionFieldMap_bijective
  obtain ⟨τ, rfl⟩ := exists_pullbackRationalPluriForms_eq f hbij hd ω
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    apply hω0
    let := functionFieldAlgebra sX
    let := functionFieldAlgebra (f ≫ sX)
    let := functionFieldMapAlgebra f
    have := isScalarTower_functionFieldMap sX f
    obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
    rw [pullbackForms_eq hω₀, pullbackFormsAlong, LinearEquiv.map_zero]
    simp
  have hKτ : (divisorOfForm τ).IsCanonicalDivisor sX n := by
    refine hK₀.of_linearlyEquivalent ?_
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hK₀ hτ0
    rwa [one_smul] at this
  have hL : ∀ i, ∃ L : Divisor X, L.IsCartier ∧
      L.IsPullback f (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f L) (C i) := by
    intro i
    obtain ⟨L, hLpb⟩ := (hCc i).exists_isPullback (f := inv f)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (inv f) (C i))
    have hLc : L.IsCartier := hLpb.isCartier (hCc i)
    obtain ⟨L₂, hL₂⟩ := hLc.exists_isPullback (f := f)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f L)
    refine ⟨L, hLc, ?_⟩
    convert hL₂ using 1
    refine Finsupp.ext fun P => ?_
    obtain ⟨Γ, hΓ⟩ := exists_primeDivisor_map_genericPoint_eq (inv f) P
    have hP : f P.genericPoint = Γ.genericPoint := by
      rw [← hΓ, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    have h1 := MMP.Positivity.coeff_eq_of_isPullback P Γ hP hLc hL₂
    have h2 := MMP.Positivity.coeff_eq_of_isPullback Γ P hΓ (hCc i) hLpb
    exact (h2.symm.trans h1.symm)
  choose L hLc hLpb using hL
  refine ⟨hXv, (inferInstance : IsProper (D.f ≫ f)), τ, hτ0,
    ⟨_, hKτ, fun Γ => coeff_divisorOfForm τ Γ⟩, m, r, L, C',
    hLc, fun Γ => ?_, fun i => ?_, ?_⟩
  · obtain ⟨P, hP⟩ := exists_primeDivisor_map_genericPoint_eq f Γ
    have hord := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hbij hd P Γ hP τ
    have hc : ∀ i, (C i).coeff P = (L i).coeff Γ := fun i =>
      MMP.Positivity.coeff_eq_of_isPullback P Γ hP (hLc i) (hLpb i)
    have := hsum P
    simp only [QDivisor.coeff_toRDivisor, hord, hB P Γ hP, hc] at this ⊢
    exact this
  · obtain ⟨hC, hCpb⟩ := hpb i
    exact ⟨_, Oai4C1.TwoEnds.divisor_isPullback_comp (hLpb i) hCpb
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ f) (L i))⟩
  · have hcomp := MMP.Flips.pullbackRationalPluriForms_comp f D.f hbij
      D.isBirationalMorphism.functionFieldMap_bijective hd τ
    change 1 + (D.E.ordForm (pullbackRationalPluriForms (f ≫ sX) D.f
        (pullbackRationalPluriForms sX f τ)) : ℝ) - _ =
      1 + (D.E.ordForm (pullbackRationalPluriForms sX (D.f ≫ f) τ) : ℝ) - _
    rw [hcomp]
    rfl

end Iso

/-! ### Points and prime divisors over a biregular open -/

section Biregular

variable {X Y : Scheme.{0}}

/-- A morphism is injective over an open `V` over which it is an isomorphism. -/
private theorem eq_of_map_eq_of_isBiregular {f : X ⟶ Y} {V : Y.Opens} (hV : IsBiregular f V)
    {x y : X} (hx : f x ∈ V) (hxy : f x = f y) : x = y := by
  have : IsIso (f ∣_ V) := hV
  have hy : f y ∈ V := hxy ▸ hx
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let q : (f ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have hp : ((f ∣_ V) ≫ V.ι) p = f x := by rw [morphismRestrict_ι]; rfl
  have hq : ((f ∣_ V) ≫ V.ι) q = f y := by rw [morphismRestrict_ι]; rfl
  exact congrArg Subtype.val
    (((f ∣_ V) ≫ V.ι).isOpenEmbedding.injective (hp.trans (hxy.trans hq.symm)) : p = q)

/-- The image of the generic point of a prime divisor `P` under a morphism which is an
isomorphism over an open `V ∋ f(η_P)` is the generic point of a prime divisor. -/
private theorem exists_primeDivisor_genericPoint_eq_map {f : X ⟶ Y} {V : Y.Opens}
    (hV : IsBiregular f V) {P : MMP.Mori.PrimeDivisor X} (hP : f P.genericPoint ∈ V) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, f P.genericPoint = Q.genericPoint := by
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f (le_biregularLocus hV hP),
      P.coheight_genericPoint]
  exact ⟨_, (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩

/-- The coefficient of `f_* B` at `Q` is that of `B` at `P` when `P` is the only prime divisor
with `f(η_P) = η_Q`. -/
private theorem transformDivisor_apply_of_map_genericPoint [IsReduced X]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {R : Type*} [AddCommMonoid R] {f : X ⟶ Y}
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hPQ : f P.genericPoint = Q.genericPoint)
    (hinj : ∀ E : MMP.Mori.PrimeDivisor X, f E.genericPoint = Q.genericPoint → E = P)
    (B : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (X := X) f.toRationalMap B Q = B P :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hPQ)
    (fun E hE => hinj E ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E Q).mp
      hE)) B

/-- Over the common biregular locus `U` of `f⁻ : X⁻ ⟶ Z ⟵ X⁺ : f⁺`, the strict transform
`(f⁺)⁻¹_* f⁻_* D` has at `P⁺` the coefficient of `D` at `P⁻`, when `f⁻(η_{P⁻}) = f⁺(η_{P⁺}) ∈ U`.
-/
private theorem flipTransform_apply_of_mem_commonBiregularLocus {Xm Xp Z : Scheme.{0}}
    [IsReduced Xm] [IsSeparated (Z ↘ Limits.terminal Scheme)] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    {Pm : MMP.Mori.PrimeDivisor Xm} {Pp : MMP.Mori.PrimeDivisor Xp}
    (h : fm Pm.genericPoint = fp Pp.genericPoint)
    (hU : fp Pp.genericPoint ∈ commonBiregularLocus fm fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Xm) : flipTransform fm fp D Pp = D Pm := by
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_genericPoint_eq_map
    (isBiregular_commonBiregularLocus_right fm fp) hU
  change inverseTransformDivisor fp (RationalMap.transformDivisor (X := Xm) fm.toRationalMap D) Pp
    = D Pm
  rw [Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint hQ
    (le_biregularLocus (isBiregular_commonBiregularLocus_right fm fp) (hQ ▸ hU))]
  refine transformDivisor_apply_of_map_genericPoint (h.trans hQ) (fun E hE => ?_) D
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  refine eq_of_map_eq_of_isBiregular (isBiregular_commonBiregularLocus_left fm fp) ?_
    (hE.trans (h.trans hQ).symm)
  rw [hE, ← hQ]
  exact hU

/-- The coefficient of the restriction `B|_U = ι⁻¹_* B` at a prime divisor `W` of `U` is that of
`B` at the prime divisor of `X` with the same generic point. -/
private theorem inverseTransformDivisor_ι_apply {R : Type*} [AddCommMonoid R] (U : X.Opens)
    (B : DivisorWithCoeffs R X) {W : MMP.Mori.PrimeDivisor U.toScheme} {Q : MMP.Mori.PrimeDivisor X}
    (hWQ : U.ι W.genericPoint = Q.genericPoint) : inverseTransformDivisor U.ι B W = B Q := by
  have hiso : IsIso (U.ι ∣_ U) := by
    have : Surjective (U.ι ∣_ U) := by
      constructor
      intro y
      let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
      refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
      have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
      rw [morphismRestrict_ι] at this
      exact this.symm
    exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)
  exact Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint hWQ
    (le_biregularLocus hiso (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨_, hWQ⟩)) B

/-- Every prime divisor `W` of an open subscheme `U ⊆ X` has the generic point of a prime
divisor of `X`. -/
private theorem exists_primeDivisor_ι_genericPoint (U : X.Opens)
    (W : MMP.Mori.PrimeDivisor U.toScheme) :
    ∃ Q : MMP.Mori.PrimeDivisor X, U.ι W.genericPoint = Q.genericPoint := by
  have hco : Order.coheight (U.ι W.genericPoint) = 1 := by
    rw [Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding, W.coheight_genericPoint]
  exact ⟨_, (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩

end Biregular

/-! ### Valuations of function fields -/

section Valuations

/-- Pulling a valuation back along a composite: `ξ ∘ (a ≫ b)^* = (ξ ∘ a^*) ∘ b^*`. -/
private theorem comap_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)]
    (ξ : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    ξ.comap (functionFieldMap (a ≫ b)) =
      (ξ.comap (functionFieldMap a)).comap (functionFieldMap b) := by
  ext t
  simp only [Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The map of function fields only depends on the morphism. -/
private theorem functionFieldMap_congr {A B : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    {g g' : A ⟶ B} [IsDominant g] [IsDominant g'] (h : g = g') :
    functionFieldMap g = functionFieldMap g' := by
  subst h
  rfl

/-- Every valuation of `k(X)` is read on `k(U) = k(X)` for a nonempty open `U ⊆ X`. -/
private theorem exists_comap_functionFieldMap_ι_eq {X : Scheme.{0}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))) :
    haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
    ∃ ξU : Valuation U.toScheme.functionField (WithZero (Multiplicative ℤ)),
      ξU.comap (functionFieldMap U.ι) = ξ := by
  haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
  have hbij := functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
    ⟨_, Set.mem_univ (Classical.arbitrary U)⟩
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) hbij
  refine ⟨ξ.comap e.symm.toRingHom, ?_⟩
  ext t
  simp only [Valuation.comap_apply]
  change ξ (e.symm (e t)) = ξ t
  rw [RingEquiv.symm_apply_apply]

end Valuations

/-! ### Comparison of log discrepancies over the common biregular locus -/

section Comparison

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
  [CompactSpace Xm] [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [CompactSpace Xp]
  [IsIntegral Z]

/-- **Log discrepancies over the common biregular locus.** Let `f⁻ : X⁻ ⟶ Z ⟵ X⁺ : f⁺` be proper
birational morphisms over `ℂ` to a normal variety, with common biregular locus `U`, and let
`(X^±, B^±)` be pairs such that `B⁺` and `B⁻` have the same coefficient at prime divisors with
the same generic point over `U`. If the centre of a normal divisorial valuation `v` of `k(X⁻)` is
not contained in the bad locus `W⁻ = X⁻ ∖ (f⁻)⁻¹(U)`, and `v⁺` is the valuation of `k(X⁺)` with
the same restriction to `k(Z)`, then `a(v; X⁻, B⁻) = a(v⁺; X⁺, B⁺)`. -/
private theorem eq_of_isValuationLogDiscrepancy {sXm : Xm ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ)
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsProper fm] [IsProper fp]
    (hbm : IsBirationalMorphism fm) (hbp : IsBirationalMorphism fp)
    (hm : fm ≫ sZ = sXm) (hp : fp ≫ sZ = sXp)
    {Bm : QDivisor Xm} {Bp : QDivisor Xp} (hBm : MMP.Fourfold.IsPair sXm Bm)
    (hBp : MMP.Fourfold.IsPair sXp Bp)
    (hB : ∀ (Pm : MMP.Mori.PrimeDivisor Xm) (Pp : MMP.Mori.PrimeDivisor Xp),
      fm Pm.genericPoint = fp Pp.genericPoint →
        fp Pp.genericPoint ∈ commonBiregularLocus fm fp → Bp.coeff Pp = Bm.coeff Pm)
    {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hv' : haveI := hbm.isDominant
      haveI := hbp.isDominant
      v'.comap (functionFieldMap fp) = v.comap (functionFieldMap fm))
    {Zc : IrreducibleCloseds Xm} (hZc : MMP.Intersection.IsCentre ℂ sXm v Zc)
    (hZU : ¬ (Zc : Set Xm) ⊆ badLocusMinus fm fp)
    {a a' : ℝ} (ha : IsValuationLogDiscrepancy sXm Bm v a)
    (ha' : IsValuationLogDiscrepancy sXp Bp v' a') : a = a' := by
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hXm := hBm.isPair.1
  set Uc := commonBiregularLocus fm fp with hUc
  obtain ⟨n, D, hDp, hDv, hl⟩ := ha
  obtain ⟨n', D', hD'p, hD'v, hl'⟩ := ha'
  -- the centre of `v` meets `(f⁻)⁻¹(U)`, so `f⁻` maps the generic point of the centre into `U`
  have hη : fm (D.f D.E.genericPoint) ∈ Uc := by
    obtain ⟨D₀, -, hv₀, rfl⟩ := hZc
    have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXm (hDv.trans hv₀)
    rw [Set.not_subset] at hZU
    obtain ⟨y, hy, hyW⟩ := hZU
    have hyU : y ∈ fm ⁻¹ᵁ Uc := by simpa [badLocusMinus] using hyW
    rw [D₀.center_eq_closure_genericPoint, ← hc] at hy
    exact (specializes_iff_mem_closure.mpr hy).mem_open (fm ⁻¹ᵁ Uc).isOpen hyU
  -- the centres of `v` and `v⁺` lie over the same point of `Z`
  have hη' : fp (D'.f D'.E.genericPoint) = fm (D.f D.E.genericPoint) :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hZ
      (D := compProper fp hbp hp D' hD'p) (D' := compProper fm hbm hm D hDp) (by
        rw [valuation_compProper, valuation_compProper, hDv, hD'v, hv'])
  have hη'U : fp (D'.f D'.E.genericPoint) ∈ Uc := hη' ▸ hη
  set Um : Xm.Opens := fm ⁻¹ᵁ Uc with hUm_def
  set Up : Xp.Opens := fp ⁻¹ᵁ Uc with hUp_def
  haveI : Nonempty Um := ⟨⟨_, hη⟩⟩
  haveI : Nonempty Up := ⟨⟨_, hη'U⟩⟩
  haveI := Opens.isDominant_ι (Um.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty Um›))
  haveI := Opens.isDominant_ι (Up.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty Up›))
  haveI : IsNoetherian Xp := {}
  haveI : CompactSpace Up := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  obtain ⟨vU, hvU⟩ := exists_comap_functionFieldMap_ι_eq Um v
  obtain ⟨vU', hvU'⟩ := exists_comap_functionFieldMap_ι_eq Up v'
  have hmemc : D.f D.E.genericPoint ∈ (D.center : Set Xm) := by
    rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl
  have hmemc' : D'.f D'.E.genericPoint ∈ (D'.center : Set Xp) := by
    rw [D'.center_eq_closure_genericPoint]; exact subset_closure rfl
  have hUm := (isValuationLogDiscrepancy_restrict_iff sXm hBm ⟨D, hDp, hDv.symm⟩
    ⟨D, hDp, hDv.symm, rfl⟩ Um ⟨_, hη, hmemc⟩ hvU a).2 ⟨n, D, hDp, hDv, hl⟩
  have hUp := (isValuationLogDiscrepancy_restrict_iff sXp hBp ⟨D', hD'p, hD'v.symm⟩
    ⟨D', hD'p, hD'v.symm, rfl⟩ Up ⟨_, hη'U, hmemc'⟩ hvU' a').2 ⟨n', D', hD'p, hD'v, hl'⟩
  -- the isomorphism `φ : U⁻ ≅ U⁺` over `U`
  haveI : IsIso (fm ∣_ Uc) := isBiregular_commonBiregularLocus_left fm fp
  haveI : IsIso (fp ∣_ Uc) := isBiregular_commonBiregularLocus_right fm fp
  let φ : Um.toScheme ⟶ Up.toScheme := (fm ∣_ Uc) ≫ inv (fp ∣_ Uc)
  have hφ : φ ≫ (fp ∣_ Uc) = fm ∣_ Uc := by simp [φ]
  have hφι : φ ≫ Up.ι ≫ fp = Um.ι ≫ fm := by
    rw [← morphismRestrict_ι fp Uc, ← Category.assoc, hφ, morphismRestrict_ι]
  have hs : φ ≫ Up.ι ≫ sXp = Um.ι ≫ sXm := by
    rw [← hp, ← hm, ← Category.assoc Up.ι, ← Category.assoc φ, ← Category.assoc Um.ι, hφι]
  rw [← hs] at hUm
  obtain ⟨nU, DU, hDUp, hDUv, hlU⟩ := hUm
  obtain ⟨np, Dp, -, hDpv, hlp⟩ := hUp
  obtain ⟨-, -, -, -, ⟨Kp, hKp, -⟩, -⟩ := id hlp
  have hn : np = nU := by
    have h1 := hKp.topologicalKrullDim_eq
    have h2 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hlU
    rw [← IsHomeomorph.topologicalKrullDim_eq _ φ.homeomorph.isHomeomorph, h2] at h1
    exact_mod_cast h1.symm
  subst hn
  have hBφ : ∀ (P : MMP.Mori.PrimeDivisor Um.toScheme) (Γ : MMP.Mori.PrimeDivisor Up.toScheme),
      φ P.genericPoint = Γ.genericPoint →
        (inverseTransformDivisor Um.ι Bm).coeff P = (inverseTransformDivisor Up.ι Bp).coeff Γ := by
    intro P Γ hPΓ
    obtain ⟨Pm, hPm⟩ := exists_primeDivisor_ι_genericPoint Um P
    obtain ⟨Pp, hPp⟩ := exists_primeDivisor_ι_genericPoint Up Γ
    change inverseTransformDivisor Um.ι Bm P = inverseTransformDivisor Up.ι Bp Γ
    rw [inverseTransformDivisor_ι_apply Um Bm hPm, inverseTransformDivisor_ι_apply Up Bp hPp]
    have heq : fm Pm.genericPoint = fp Pp.genericPoint := by
      rw [← hPm, ← hPp, ← hPΓ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        ← Scheme.Hom.comp_apply, ← hφι]
    have hmem : fp Pp.genericPoint ∈ Uc := by
      rw [← hPp]
      exact Γ.genericPoint.2
    exact (hB Pm Pp heq hmem).symm
  have hiso := isLogDiscrepancy_compIso φ hKp hBφ hDUp hlU
  refine MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hiso hlp ?_
  rw [valuation_compProper, hDUv, hDpv]
  have hsurj : Function.Surjective (functionFieldMap (Up.ι ≫ fp)) := by
    intro t
    obtain ⟨s, rfl⟩ := (functionFieldMap_bijective_of_isOpenImmersion Up.ι ⊤
      ⟨_, Set.mem_univ (Classical.arbitrary Up)⟩).2 t
    obtain ⟨r, rfl⟩ := hbp.functionFieldMap_bijective.2 s
    exact ⟨r, (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply Up.ι fp r).symm⟩
  apply Oai4C1.valuation_eq_of_comap_eq hsurj
  change (vU.comap (functionFieldMap φ)).comap (functionFieldMap (Up.ι ≫ fp)) =
    vU'.comap (functionFieldMap (Up.ι ≫ fp))
  rw [← comap_functionFieldMap_comp φ (Up.ι ≫ fp), comap_functionFieldMap_comp Up.ι fp, hvU', hv',
    functionFieldMap_congr hφι, comap_functionFieldMap_comp Um.ι fm, hvU]

end Comparison

/-! ### Biregular loci of morphisms precomposed with an isomorphism -/

section IsoComp

/-- Precomposing with an isomorphism does not shrink the biregular locus. -/
private theorem biregularLocus_le_biregularLocus_comp {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus f ≤ biregularLocus (φ ≫ f) :=
  sSup_le fun V hV => le_biregularLocus (by
    have : IsIso (f ∣_ V) := hV
    change IsIso ((φ ≫ f) ∣_ V)
    rw [morphismRestrict_comp]
    have h2 : IsIso (φ ∣_ (f ⁻¹ᵁ V)) := by infer_instance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 this)

/-- Precomposing with an isomorphism does not change the biregular locus. -/
private theorem biregularLocus_comp_of_isIso {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus (φ ≫ f) = biregularLocus f := by
  refine le_antisymm ?_ (biregularLocus_le_biregularLocus_comp φ f)
  have := biregularLocus_le_biregularLocus_comp (inv φ) (φ ≫ f)
  rwa [IsIso.inv_hom_id_assoc] at this

end IsoComp

/-! ### The valuation of the target of a flip -/

section Target

/-- **Exceptionality is transported along an isomorphism.** If `ψ : A ≅ X` is an isomorphism over
`ℂ` and the valuation `v ∘ ψ^*` of `ℂ(X)` is exceptional over `X`, then `v` is exceptional over
`A`. -/
private theorem isExceptionalValuation_of_isIso {A X : Scheme.{0}} [IsIntegral A]
    [IsLocallyNoetherian A] [IsNormal A] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sA : A ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)} (ψ : A ≅ X) (hψ : ψ.hom ≫ sX = sA)
    {v : Valuation A.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Intersection.IsExceptionalValuation ℂ sX (v.comap (functionFieldMap ψ.hom))) :
    MMP.Intersection.IsExceptionalValuation ℂ sA v := by
  obtain ⟨D, hDp, hDv, hcod⟩ := h
  have hs : ψ.inv ≫ sA = sX := by rw [← hψ, Iso.inv_hom_id_assoc]
  haveI := hDp
  refine ⟨compProper ψ.inv (isBirationalMorphism_of_isIso _) hs D hDp,
    (inferInstance : IsProper (D.f ≫ ψ.inv)), ?_, ?_⟩
  · rw [valuation_compProper, ← hDv, ← comap_functionFieldMap_comp,
      functionFieldMap_congr ψ.hom_inv_id]
    ext t
    rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_id_apply]
  · rw [MMP.Positivity.DivisorOver.codimension_center] at hcod ⊢
    change 2 ≤ Order.coheight ((D.f ≫ ψ.inv) D.E.genericPoint)
    rw [Scheme.Hom.comp_apply, Topology.IsOpenEmbedding.coheight_eq _ ψ.inv.isOpenEmbedding]
    exact hcod

variable {Xm Xp A Z : Scheme.{0}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
  [CompactSpace Xm] [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [CompactSpace Xp]
  [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A] [CompactSpace A] [IsIntegral Z]

/-- **Weights across a small flip.** Let `f⁻ : X⁻ ⟶ Z ⟵ X⁺ : f⁺` be small morphisms to a normal
variety, let `ψ : A ≅ X⁺` be an isomorphism over `ℂ` and `f_A = f⁺ ∘ ψ`, and let `(X⁻, B⁻)` and
`(A, B_A)` be pairs with `B_A` the transport along `ψ` of the strict transform
`(f⁺)⁻¹_* f⁻_* B⁻`. Let `v` be exceptional over `X⁻` and let `v'` be the valuation of `ℂ(A)` with
the same restriction to `ℂ(Z)`. Then `v'` is exceptional over `A`, it has a log discrepancy over
`(A, B_A)`, any two of its log discrepancies agree, and if the centre of `v` is not contained in
the bad locus `W⁻` of `(f⁻, f_A)`, the log discrepancies of `v` and `v'` agree. -/
private theorem isValuationLogDiscrepancy_target {sXm : Xm ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {sA : A ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : IsNormalVariety ℂ sZ) {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {fA : A ⟶ Z} [IsDominant fm]
    [IsDominant fA] (hsm : IsSmallMorphism sXm sZ fm) (hsp : IsSmallMorphism sXp sZ fp)
    (ψ : A ≅ Xp) (hψ : ψ.hom ≫ sXp = sA) (hfA : fA = ψ.hom ≫ fp) {Bm : QDivisor Xm}
    {BA : QDivisor A} (hBm : MMP.Fourfold.IsPair sXm Bm) (hBA : MMP.Fourfold.IsPair sA BA)
    (hB : ∀ (PA : MMP.Mori.PrimeDivisor A) (Γ : MMP.Mori.PrimeDivisor Xp),
      ψ.hom PA.genericPoint = Γ.genericPoint → BA.coeff PA = (flipTransform fm fp Bm).coeff Γ)
    {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation A.functionField (WithZero (Multiplicative ℤ))}
    (hv' : v'.comap (functionFieldMap fA) = v.comap (functionFieldMap fm))
    (hexc : MMP.Intersection.IsExceptionalValuation ℂ sXm v) :
    MMP.Intersection.IsExceptionalValuation ℂ sA v' ∧
      (∃ a', IsValuationLogDiscrepancy sA BA v' a') ∧
      (∀ a₁ a₂, IsValuationLogDiscrepancy sA BA v' a₁ → IsValuationLogDiscrepancy sA BA v' a₂ →
        a₁ = a₂) ∧
      ∀ Zc : IrreducibleCloseds Xm, MMP.Intersection.IsCentre ℂ sXm v Zc →
        ¬ (Zc : Set Xm) ⊆ badLocusMinus fm fA → ∀ a a',
          IsValuationLogDiscrepancy sXm Bm v a → IsValuationLogDiscrepancy sA BA v' a' →
            a = a' := by
  subst hfA
  haveI : IsDominant fp := hsp.isBirationalMorphism.isDominant
  haveI : IsProper fm := hsm.isProper
  haveI : IsProper fp := hsp.isProper
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hZ
  -- `v'` is exceptional over `A`
  have hv'' : (v'.comap (functionFieldMap ψ.hom)).comap (functionFieldMap fp) =
      v.comap (functionFieldMap fm) := by
    rw [← comap_functionFieldMap_comp]
    exact hv'
  have hexc'' : MMP.Intersection.IsExceptionalValuation ℂ sXp
      (v'.comap (functionFieldMap ψ.hom)) :=
    (hsm.isExceptionalValuation_iff hsp hv''.symm).1 hexc
  have hexc' := isExceptionalValuation_of_isIso ψ hψ hexc''
  refine ⟨hexc', ?_, ?_, ?_⟩
  · -- a log discrepancy of `v'` exists, since `(A, B_A)` is a pair
    obtain ⟨D, hDp, hDv, -⟩ := hexc'
    obtain ⟨-, n, K, hK, -⟩ := id hBA.isPair
    obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBA.isPair hK D
    exact ⟨_, n, D, hDp, hDv.symm,
      MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb hDp⟩
  · -- log discrepancies only depend on the valuation
    rintro a₁ a₂ ⟨n₁, D₁, -, hv₁, h₁⟩ ⟨n₂, D₂, -, hv₂, h₂⟩
    exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h₁ h₂ (hv₁.trans hv₂.symm)
  · -- off the bad locus, the comparison over the common biregular locus
    intro Zc hZc hZU a a' ha ha'
    have hbA : IsBirationalMorphism (ψ.hom ≫ fp) :=
      isBirationalMorphism_comp_of_isBirational fp ψ.hom
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hsp.isBirationalMorphism)
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          (isBirationalMorphism_of_isIso ψ.hom))
    have hU : commonBiregularLocus fm (ψ.hom ≫ fp) = commonBiregularLocus fm fp := by
      simp only [commonBiregularLocus, biregularLocus_comp_of_isIso]
    refine eq_of_isValuationLogDiscrepancy hZ hsm.isBirationalMorphism hbA hsm.comp_eq
      (by rw [Category.assoc, hsp.comp_eq, hψ]) hBm hBA (fun Pm PA h hPA => ?_) hv' hZc hZU
      ha ha'
    obtain ⟨Γ, hΓ⟩ := exists_primeDivisor_map_genericPoint_eq ψ.inv PA
    have hΓ' : ψ.hom PA.genericPoint = Γ.genericPoint := by
      rw [← hΓ, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have hfp : (ψ.hom ≫ fp) PA.genericPoint = fp Γ.genericPoint := by
      rw [Scheme.Hom.comp_apply, hΓ']
    rw [hB PA Γ hΓ']
    exact flipTransform_apply_of_mem_commonBiregularLocus (h.trans hfp)
      (by rw [← hfp, ← hU]; exact hPA) Bm

end Target

/-! ### The target of a flip of a bridge -/

section Chain

open StabilizedSmallKltTail

/-- Along an equality `a = b` of indices, the identification `V_a = V_b` of models of a programme
is compatible with their structure morphisms. -/
private theorem eqToHom_comp_modelStr {V : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (sY : ∀ k, Y k ⟶ Spec (.of ℂ)) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (modelSeq V Y) h) ≫ modelStr sV sY b = modelStr sV sY a := by
  subst h; simp

/-- At the end `V_M ≅ W` of a programme, identified with `V_{k+1}`, the boundary `Θ_{k+1}`
corresponds to the boundary `B` of `W` when `Θ_M = e⁻¹_* B`. -/
private theorem coeff_eq_of_boundary_eq {V W : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    {Θ : QDivisor V} {ΘY : ∀ k, QDivisor (Y k)} (B : QDivisor W) {M k : ℕ} (hM : M = k + 1)
    (e : modelSeq V Y M ≅ W) (hb : divisorSeq Θ ΘY M = inverseTransformDivisor e.hom B)
    (P : MMP.Mori.PrimeDivisor W) (Γ : MMP.Mori.PrimeDivisor (Y k))
    (h : (e.inv ≫ eqToHom (congrArg (modelSeq V Y) hM)) P.genericPoint = Γ.genericPoint) :
    B.coeff P = (ΘY k).coeff Γ := by
  subst hM
  simp only [eqToHom_refl, Category.comp_id] at h
  have hΓ : e.hom Γ.genericPoint = P.genericPoint := by
    rw [← h, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  change _ = divisorSeq Θ ΘY (k + 1) Γ
  rw [hb, Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint hΓ
    (le_biregularLocus (V := ⊤) (inferInstance : IsIso (e.hom ∣_ ⊤)) trivial)]
  rfl

/-- The model reached by the `k`-th flip of the `i`-th bridge of a terminal chain is `V_{k+1}` up
to an isomorphism `ψ` over `ℂ` (the identity, or the inverse of the identification
`e : V_{m_i} ≅ Y_{i+1}` of the end of the bridge), through which the morphism to `T_k` is `g_k⁺`
and the boundary is `Θ_{k+1}`. -/
private theorem exists_iso_flipTargetOf {T : StabilizedSmallKltTail} (C : TerminalChain T) (i : ℕ)
    (k : Fin (C.bridge i).P.m) (d : Decidable (k.1 + 1 < (C.bridge i).P.m)) :
    ∃ ψ : C.model (C.flipTargetOf i k d) ≅ (C.bridge i).P.Y k,
      ψ.hom ≫ (C.bridge i).P.sY k = C.modelStructure (C.flipTargetOf i k d) ∧
      C.flipTargetMapOf i k d = ψ.hom ≫ (C.bridge i).P.gp k ∧
      ∀ (PA : MMP.Mori.PrimeDivisor (C.model (C.flipTargetOf i k d)))
        (Γ : MMP.Mori.PrimeDivisor ((C.bridge i).P.Y k)),
        ψ.hom PA.genericPoint = Γ.genericPoint →
          (C.modelBoundary (C.flipTargetOf i k d)).coeff PA = ((C.bridge i).P.ΘY k).coeff Γ := by
  cases d with
  | isTrue h =>
    refine ⟨Iso.refl _, Category.id_comp _, (Category.id_comp _).symm, fun PA Γ hPA => ?_⟩
    obtain rfl : PA = Γ := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hPA
    rfl
  | isFalse h =>
    have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
    refine ⟨(C.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk), ?_,
      (Category.assoc _ _ _).symm, fun PA Γ hPA => ?_⟩
    · change ((C.bridge i).e.inv ≫
        eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)) ≫
          modelStr (C.junction i).sY (C.bridge i).P.sY (k.1 + 1) = (C.junction (i + 1)).sY
      rw [Category.assoc, eqToHom_comp_modelStr _ _ hmk]
      exact (Iso.inv_comp_eq _).2 (C.bridge i).comp_sY.symm
    · exact coeff_eq_of_boundary_eq _ hmk (C.bridge i).e (C.bridge i).endBoundary_eq PA Γ hPA

end Chain

end MMP.Fourfold.FlipWeights

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail} {Q : PreparedChain T}

open MMP.Mori FlipWeights in
/-- **Weights outside the weighted bad set are unchanged by a flip.** Let `μ` be a small
terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a bridge of a prepared chain `Q`, with step diagram
`Y⁻ → Z ← Y⁺` and weighted bad set `𝒜₀ = Q.flipBadSet μ`. Let `v` be a normalized divisorial
valuation of `ℂ(Y⁻)` exceptional over `Y⁻`, with weight `w = w_v(Y⁻, Θ⁻)`, and `v ∉ 𝒜₀`, and let
`v'` be the valuation of `ℂ(Y⁺)` with the same restriction to `ℂ(Z)`. Then the weights of `v'`
on `(Y⁺, Θ⁺)` are exactly `w`: `v'` is exceptional over `Y⁺` and `w_v(Y⁺, Θ⁺) = w_v(Y⁻, Θ⁻)`. -/
@[mmp "lem_oai4_c3_flip_weights_outside_bad_set"]
public theorem isValuationWeight_target_iff_of_notMem_flipBadSet (μ : Q.FlipMove)
    {v : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ))}
    (hv : v ∉ Q.flipBadSet μ)
    (hvv' : v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap))
    {w : ℕ} (hw : Q.chain.IsValuationWeight Q.scale μ.source.1 v w) (w' : ℕ) :
    Q.chain.IsValuationWeight Q.scale μ.target.1 v' w' ↔ w' = w := by
  have hD := (Q.chain.bridge μ.1.1).P.isFourfoldStepDiagram μ.1.2 μ.1.2.2
  obtain ⟨ψ, hψ, hfA, hB⟩ := exists_iso_flipTargetOf Q.chain μ.1.1 μ.1.2 inferInstance
  have hpair : ∀ x, MMP.Fourfold.IsPair (Q.chain.modelStructure x) (Q.chain.modelBoundary x) :=
    fun x => (TerminalChain.isKltTerminalPair_modelBoundary Q.chain x).1.1.1
  obtain ⟨hexc', ⟨a', ha'⟩, huniq, hcomp⟩ := isValuationLogDiscrepancy_target
    (fm := μ.sourceMap) (fA := μ.targetMap) hD.isNormalVariety_target
    (Q.chain.isSmallMorphism_flipSourceMap μ.1.1 μ.1.2) hD.isSmallMorphism_plus ψ hψ hfA
    (hpair μ.source.1) (hpair μ.target.1)
    (fun PA Γ h => (hB PA Γ h).trans (congrArg (fun B => DivisorWithCoeffs.coeff B Γ)
      ((Q.chain.bridge μ.1.1).P.ΘY_eq μ.1.2 μ.1.2.2))) hvv' hw.1
  obtain ⟨a, ha, rfl⟩ := hw.2
  have hw' : Q.chain.IsValuationWeight Q.scale μ.target.1 v' (difficultyWeight Q.scale (2 - a')) :=
    ⟨hexc', a', ha', rfl⟩
  have heq : difficultyWeight Q.scale (2 - a') = difficultyWeight Q.scale (2 - a) := by
    by_cases hc : ∃ Z : IrreducibleCloseds (Q.chain.model μ.source.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure μ.source.1) v Z ∧
          (Z : Set (Q.chain.model μ.source.1)) ⊆ μ.badLocusSource
    · -- the centre lies in `W⁻`: both weights vanish, as `v` is not in the weighted bad set
      have : ¬ 0 < difficultyWeight Q.scale (2 - a) + difficultyWeight Q.scale (2 - a') :=
        fun h => hv ⟨hc, v', hvv', _, _, hw, hw', h⟩
      omega
    · -- the centre is not in `W⁻`: the log discrepancies agree
      obtain ⟨Dv, hDvp, hDvv, -⟩ := hw.1
      have hZc : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure μ.source.1) v Dv.center :=
        ⟨Dv, hDvp, hDvv, rfl⟩
      rw [hcomp Dv.center hZc (fun h => hc ⟨_, hZc, h⟩) a a' ha ha']
  constructor
  · rintro ⟨-, b, hb, rfl⟩
    rw [huniq b a' hb ha', heq]
  · rintro rfl
    exact heq ▸ hw'

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

/-! ## The unit drop -/

namespace MMP.Fourfold.UnitDrop

open Limits

open MMP.Mori MMP.Fourfold

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-! ### Residue fields and stalks at generic points -/

section Residue

/-- The residue map of a point whose local ring is a field is bijective. -/
private theorem residue_bijective_of_isField {X : Scheme.{0}} (x : X)
    (hx : IsField (X.presheaf.stalk x)) : Function.Bijective (X.residue x) := by
  letI := hx.toField
  exact ⟨(X.residue x).hom.injective, IsLocalRing.residue_surjective⟩

/-- The local ring of an integral scheme at its generic point is a field. -/
private theorem isField_stalk_of_eq_genericPoint {X : Scheme.{0}} [IsIntegral X] {x : X}
    (hx : x = genericPoint X) : IsField (X.presheaf.stalk x) := by
  subst hx
  exact Field.toIsField X.functionField

/-- A morphism of integral schemes sending generic point to generic point and inducing an
isomorphism of residue fields there is an isomorphism on local rings there. -/
private theorem isIso_stalkMap_of_isIso_residueFieldMap {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y)
    [IsIso (f.residueFieldMap (genericPoint X))] : IsIso (f.stalkMap (genericPoint X)) := by
  have h1 := residue_bijective_of_isField (genericPoint X) (isField_stalk_of_eq_genericPoint rfl)
  have h2 := residue_bijective_of_isField (f (genericPoint X))
    (isField_stalk_of_eq_genericPoint hf)
  have h3 : Function.Bijective (f.residueFieldMap (genericPoint X)) :=
    ConcreteCategory.bijective_of_isIso _
  have hc := congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    (Scheme.residue_residueFieldMap f (genericPoint X))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hc
  have hb : Function.Bijective ((X.residue (genericPoint X)) ∘
      (f.stalkMap (genericPoint X))) := by
    rw [← hc]; exact h3.comp h2
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => hb.1 (by simp [hab]), fun c => ?_⟩
  obtain ⟨a, ha⟩ := hb.2 (X.residue _ c)
  exact ⟨a, h1.1 ha⟩

/-- A morphism of integral schemes sending generic point to generic point and inducing an
isomorphism of residue fields there is birational. -/
private theorem isBirational_of_isIso_residueFieldMap_genericPoint {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y)
    [IsIso (f.residueFieldMap (genericPoint X))] : IsBirational f := by
  haveI := isIso_stalkMap_of_isIso_residueFieldMap f hf
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ?_ fun x hx => ?_
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
    exact hf
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    infer_instance

/-- A birational morphism of integral schemes induces an isomorphism of residue fields at the
generic point. -/
private theorem isIso_residueFieldMap_genericPoint {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {f : X ⟶ Y} (hf : IsBirational f) :
    IsIso (f.residueFieldMap (genericPoint X)) := by
  haveI := hf.isIso_stalkMap (genericPoint X) (by rw [genericPoints_eq_singleton]; rfl)
  exact isIso_residueFieldMap_of_isIso_stalkMap _ _

/-- If the residue field map of `g` at `T.y` is an isomorphism, then so is the canonical map
`κ(T.x) ⟶ κ(T.x) ⊗_{κ(T.s)} κ(T.y)`, being a pushout of an isomorphism. -/
private theorem isIso_tensorInl {X Z S : Scheme.{0}} {f : X ⟶ S} {g : Z ⟶ S}
    (T : Scheme.Pullback.Triplet f g) (hres : IsIso (g.residueFieldMap T.y)) :
    IsIso T.tensorInl := by
  have : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) := inferInstance
  change IsIso (pushout.inl ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
  infer_instance

/-- If the residue field map of `g : Z ⟶ S` at `z` is an isomorphism, a point of `X ×_S Z` is
determined by its two projections when the second one is `z` ([Stacks, Tag 01JT]). -/
private theorem eq_of_fst_eq_of_snd_eq {X Z S : Scheme.{0}} (f : X ⟶ S) (g : Z ⟶ S)
    {w w' : ↥(pullback f g)} (hres : IsIso (g.residueFieldMap (pullback.snd f g w)))
    (h₁ : pullback.fst f g w' = pullback.fst f g w)
    (h₂ : pullback.snd f g w' = pullback.snd f g w) : w' = w := by
  have : Subsingleton ↥(Spec (Scheme.Pullback.carrierEquiv w).fst.tensor) := by
    have hinl := isIso_tensorInl (Scheme.Pullback.carrierEquiv w).fst hres
    exact (PrimeSpectrum.comap_injective_of_surjective
      (Scheme.Pullback.carrierEquiv w).fst.tensorInl.hom
      (ConcreteCategory.bijective_of_isIso _).2).subsingleton
  refine Scheme.Pullback.carrierEquiv.injective
    (Scheme.Pullback.carrierEquiv_eq_iff.mpr ?_)
  exact ⟨Scheme.Pullback.Triplet.ext h₁ h₂, Subsingleton.elim _ _⟩

/-- At a point `w` of `X ×_S Z` over `x` and `z`, if the residue field map of `g : Z ⟶ S` at `z`
is an isomorphism then so is that of the first projection at `w`
([Stacks, Tag 01JT]). -/
private theorem isIso_residueFieldMap_fst {X Z S : Scheme.{0}} (f : X ⟶ S) (g : Z ⟶ S)
    (z : Z) [hres : IsIso (g.residueFieldMap z)] (w : ↥(pullback f g))
    (hw₂ : pullback.snd f g w = z) : IsIso ((pullback.fst f g).residueFieldMap w) := by
  subst hw₂
  have hinl := isIso_tensorInl (Scheme.Pullback.Triplet.ofPoint w) hres
  obtain ⟨ι, -, hι⟩ := hinl.out
  have hfac : (Scheme.Pullback.Triplet.ofPoint w).tensorInl ≫ Scheme.Pullback.ofPointTensor w =
      (pullback.fst f g).residueFieldMap w :=
    pushout.inl_desc _ _ (Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoint w)
  have htri : Spec.map ((Scheme.Pullback.Triplet.ofPoint w).tensorInl ≫
      Scheme.Pullback.ofPointTensor w) ≫
      Spec.map ι ≫ (Scheme.Pullback.Triplet.ofPoint w).SpecTensorTo =
      (pullback f g).fromSpecResidueField w := by
    rw [Spec.map_comp, Category.assoc,
      ← Category.assoc (Spec.map (Scheme.Pullback.Triplet.ofPoint w).tensorInl), ← Spec.map_comp,
      hι, Spec.map_id, Category.id_comp, Scheme.Pullback.ofPointTensor_SpecTensorTo]
  have key : ∀ {K : Type} [Field K] (ψ : CommRingCat.of K ⟶ (pullback f g).residueField w)
      (a : Spec (CommRingCat.of K) ⟶ pullback f g),
      Spec.map ψ ≫ a = (pullback f g).fromSpecResidueField w → IsIso ψ := by
    intro K _ ψ a h
    obtain ⟨⟨y, k⟩, rfl⟩ := (Scheme.SpecToEquivOfField K (pullback f g)).symm.surjective a
    simp only [Scheme.SpecToEquivOfField_symm_apply] at h
    have hy : y = w := by
      have h₁ : (pullback f g).fromSpecResidueField y (Spec.map k (Spec.map ψ default)) =
          (pullback f g).fromSpecResidueField w default :=
        congrArg (fun m : Spec ((pullback f g).residueField w) ⟶ pullback f g ↦ m default) h
      simpa using h₁
    subst y
    have : Mono ψ := ConcreteCategory.mono_of_injective ψ ψ.hom.injective
    have : IsSplitEpi ψ := ⟨⟨k, by
      simpa only [← Spec.map_inj, Spec.map_comp, Spec.map_id,
        ← cancel_mono ((pullback f g).fromSpecResidueField w), Category.assoc,
        Category.id_comp] using h⟩⟩
    exact isIso_of_mono_of_isSplitEpi ψ
  exact key _ _ (.trans (congrArg
    (fun u ↦ Spec.map u ≫ Spec.map ι ≫ (Scheme.Pullback.Triplet.ofPoint w).SpecTensorTo)
    hfac.symm) htri)

/-- Residue field maps that are isomorphisms compose. -/
private theorem isIso_residueFieldMap_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [IsIso (f.residueFieldMap x)] [IsIso (g.residueFieldMap (f x))] :
    IsIso ((f ≫ g).residueFieldMap x) := by
  rw [Scheme.residueFieldMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›

/-- At a point `w` of `X ×_S Z` over `x` and `z`, if the residue field map of `f : X ⟶ S` at `x`
is an isomorphism then so is that of the second projection at `w`. -/
private theorem isIso_residueFieldMap_snd {X Z S : Scheme.{0}} (f : X ⟶ S) (g : Z ⟶ S)
    (x : X) [IsIso (f.residueFieldMap x)] (w : ↥(pullback f g))
    (hw₁ : pullback.fst f g w = x) : IsIso ((pullback.snd f g).residueFieldMap w) := by
  haveI := isIso_residueFieldMap_fst g f x ((pullbackSymmetry f g).hom w)
    (by rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd, hw₁])
  rw [← pullbackSymmetry_hom_comp_fst]
  exact isIso_residueFieldMap_comp _ _ w

/-- A morphism surjective on stalks induces isomorphisms of residue fields. -/
private theorem isIso_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, fun c => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  obtain ⟨b, rfl⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have hc := congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    (Scheme.residue_residueFieldMap f x)
  exact congrFun hc b

end Residue

/-! ### The normalized graph -/

/-- The data of a normalized graph of a step diagram, together with the finiteness facts used
below. -/
private structure GraphData {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (_h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) where
  G : Scheme.{0}
  u : G ⟶ Xm
  v : G ⟶ Xp
  isNormalizedGraph : IsNormalizedGraph fm fp u v
  isNormal : IsNormal G
  isLocallyNoetherian : IsLocallyNoetherian G
  compactSpace : CompactSpace G
  locallyOfFiniteType : LocallyOfFiniteType (u ≫ sXm)
  isProper_u : IsProper u
  isProper_v : IsProper v

/-- The source of a normalized graph is integral. -/
private theorem GraphData.isIntegral {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    {h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp} (D : GraphData h) : IsIntegral D.G :=
  D.isNormalizedGraph.isIntegral

attribute [local instance] GraphData.isIntegral GraphData.isNormal GraphData.isLocallyNoetherian
  GraphData.compactSpace GraphData.locallyOfFiniteType GraphData.isProper_u GraphData.isProper_v

/-- **The normalized graph exists**: the normalization `G` of the closure `Γ ⊆ X⁻ ×_Z X⁺` of the
point over the two generic points, with its two projections. -/
private theorem exists_graphData {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) : Nonempty (GraphData h) := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sXm := h.isNormalVariety_minus.1.toLocallyOfFiniteType
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hbm := h.isBirationalMorphism_minus
  have hbp := h.isBirationalMorphism_plus
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  have hbm' := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbm
  have hbp' := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbp
  have hηm : fm (genericPoint Xm) = genericPoint Z := map_genericPoint_of_isDominant fm
  have hηp : fp (genericPoint Xp) = genericPoint Z := map_genericPoint_of_isDominant fp
  -- the generic point `t` of the graph
  obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := fm) (g := fp)
    (genericPoint Xm) (genericPoint Xp) (hηm.trans hηp.symm)
  set Γ := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({t} : Set ↥(pullback fm fp))))
  haveI : IsIntegral Γ.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  set ι := Γ.subschemeι
  have hιγ : ι (genericPoint Γ.subscheme) = t := by
    have h1 := (genericPoint_spec Γ.subscheme).image ι.continuous
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at h1
    have h2 : IsGenericPoint t (closure (closure ({t} : Set ↥(pullback fm fp)))) := by
      rw [closure_closure]; exact isGenericPoint_closure
    exact h1.eq h2
  set γ := genericPoint Γ.subscheme
  have hΓfin : ∀ U : Γ.subscheme.Opens, IsCompact (U : Set Γ.subscheme) →
      (irreducibleComponents (U : Set Γ.subscheme)).Finite :=
    fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U
  set G := Γ.subscheme.normalizationScheme hΓfin
  set ν := Γ.subscheme.normalization hΓfin
  haveI : IsFinite ν := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field ℂ (ι ≫ pullback.fst fm fp ≫ sXm)) hΓfin
  haveI : IsIntegral G := Scheme.isIntegral_normalizationScheme _ _
  haveI : IsNormal G := Scheme.isNormal_normalizationScheme _ _
  have hν : IsBirational ν := Scheme.isBirational_normalization _ _
  -- residue fields at the generic point of the graph
  haveI := isIso_residueFieldMap_genericPoint hbm'
  haveI := isIso_residueFieldMap_genericPoint hbp'
  haveI := isIso_residueFieldMap_of_surjectiveOnStalks ι γ
  have hgen1 : (ι ≫ pullback.fst fm fp) γ = genericPoint Xm := by
    rw [Scheme.Hom.comp_apply, hιγ, ht₁]
  have hgen2 : (ι ≫ pullback.snd fm fp) γ = genericPoint Xp := by
    rw [Scheme.Hom.comp_apply, hιγ, ht₂]
  haveI := isIso_residueFieldMap_fst fm fp _ (ι γ) (by rw [hιγ, ht₂])
  haveI := isIso_residueFieldMap_snd fm fp _ (ι γ) (by rw [hιγ, ht₁])
  haveI := isIso_residueFieldMap_comp ι (pullback.fst fm fp) γ
  haveI := isIso_residueFieldMap_comp ι (pullback.snd fm fp) γ
  have hb1 := isBirational_of_isIso_residueFieldMap_genericPoint _ hgen1
  have hb2 := isBirational_of_isIso_residueFieldMap_genericPoint _ hgen2
  set u : G ⟶ Xm := ν ≫ ι ≫ pullback.fst fm fp with hudef
  set v : G ⟶ Xp := ν ≫ ι ≫ pullback.snd fm fp with hvdef
  haveI : IsProper u := by rw [hudef]; infer_instance
  haveI : IsProper v := by rw [hvdef]; infer_instance
  haveI : LocallyOfFiniteType (u ≫ sXm) := by rw [hudef]; infer_instance
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (u ≫ sXm)
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace u
  have hbu : IsBirationalMorphism u :=
    Oai4C1.CommonModel.isBirationalMorphism_of_isBirational u (hν.comp hb1)
  have hbv : IsBirationalMorphism v :=
    Oai4C1.CommonModel.isBirationalMorphism_of_isBirational v (hν.comp hb2)
  have hcomp : u ≫ fm = v ≫ fp := by
    simp only [hudef, hvdef, Category.assoc, pullback.condition]
  have hlift : pullback.lift u v hcomp = ν ≫ ι := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc]
  have hG : IsNormalizedGraph fm fp u v :=
    { isIntegral := inferInstance, isNormal := inferInstance, comp_eq := hcomp,
      isFinite := by rw [hlift]; infer_instance, isBirationalMorphism_minus := hbu,
      isBirationalMorphism_plus := hbv }
  exact ⟨⟨G, u, v, hG, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance⟩⟩

/-! ### Fibres and biregular loci -/

/-- A proper birational morphism of complex varieties onto a normal variety is an isomorphism
over a neighbourhood of every point with finite fibre. -/
private theorem mem_biregularLocus_of_finite {U R : Scheme.{0}} {sU : U ⟶ Spec (.of ℂ)}
    {sR : R ⟶ Spec (.of ℂ)} (hU : AlgebraicGeometry.IsVariety ℂ sU)
    (hR : AlgebraicGeometry.IsVariety ℂ sR) [IsNormal R] (f : U ⟶ R) (hf : f ≫ sR = sU)
    [IsProper f] (hb : IsBirational f) {z : R} (hz : (f ⁻¹' {z}).Finite) :
    z ∈ biregularLocus f := by
  obtain ⟨⟨hO, hiso⟩, -, -⟩ :=
    MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq ℂ hU hR f hf hb
  exact le_biregularLocus (V := ⟨_, hO⟩) hiso hz

variable {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- The structure map `g = u ≫ f⁻` of the normalized graph has finite fibres over the open where
both `f^±` are isomorphisms: there a fibre of `X⁻ ×_Z X⁺` is one point, and `(u, v)` is finite. -/
private theorem finite_preimage_of_mem_commonBiregularLocus
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (D : GraphData h) {z : Z}
    (hz : z ∈ commonBiregularLocus fm fp) : ((D.u ≫ fm) ⁻¹' {z}).Finite := by
  have hG := D.isNormalizedGraph
  haveI := hG.isFinite
  haveI : IsIso (fm ∣_ biregularLocus fm) := isBiregular_biregularLocus fm
  haveI : IsIso (fp ∣_ biregularLocus fp) := isBiregular_biregularLocus fp
  have sm := MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict fm _ hz.1
  have sp := MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict fp _ hz.2
  rcases ((D.u ≫ fm) ⁻¹' {z}).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · rw [he]; exact Set.finite_empty
  set L := pullback.lift D.u D.v hG.comp_eq
  refine (L.finite_preimage_singleton (L x₀)).subset fun x hx => ?_
  have hx' : fm (D.u x) = z := hx
  have hx₀' : fm (D.u x₀) = z := hx₀
  have hvx : fp (D.v x) = z := by
    rw [← Scheme.Hom.comp_apply, ← hG.comp_eq]; exact hx
  have hvx₀ : fp (D.v x₀) = z := by
    rw [← Scheme.Hom.comp_apply, ← hG.comp_eq]; exact hx₀
  have hres : IsIso (fp.residueFieldMap (pullback.snd fm fp (L x₀))) := by
    have hsnd : pullback.snd fm fp (L x₀) = D.v x₀ := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    have hmem : fp (pullback.snd fm fp (L x₀)) ∈ biregularLocus fp := by
      rw [hsnd, hvx₀]; exact hz.2
    haveI := MMP.isIso_stalkMap_of_mem_biregularLocus fp hmem
    exact isIso_residueFieldMap_of_isIso_stalkMap _ _
  refine eq_of_fst_eq_of_snd_eq fm fp hres ?_ ?_
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact sm hx' hx₀'
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    exact sp hvx hvx₀

/-- The source of the normalized graph is a complex variety through `u ≫ s⁻`. -/
private theorem isVariety_graph (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : AlgebraicGeometry.IsVariety ℂ (D.u ≫ sXm) := by
  have := h.isNormalVariety_minus.1
  exact (isVariety_iff ℂ (D.u ≫ sXm)).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The structure map `g = u ≫ f⁻` of the normalized graph is birational. -/
private theorem isBirational_graph (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : IsBirational (D.u ≫ fm) := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  exact IsBirational.comp
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      D.isNormalizedGraph.isBirationalMorphism_minus)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_minus)

/-- The source of the normalized graph is a normal complex variety through `u ≫ s⁻`. -/
private theorem isNormalVariety_graph (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : IsNormalVariety ℂ (D.u ≫ sXm) :=
  ⟨isVariety_graph h D, inferInstance⟩

/-- The structure map `g = u ≫ f⁻` of the normalized graph is a birational morphism. -/
private theorem isBirationalMorphism_graph (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : IsBirationalMorphism (D.u ≫ fm) := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  exact MMP.Mori.isBirationalMorphism_comp_of_isBirational fm D.u
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_minus)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      D.isNormalizedGraph.isBirationalMorphism_minus)

/-- The source of the normalized graph is a normal complex variety through `v ≫ s⁺`. -/
private theorem isNormalVariety_graph_plus (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : IsNormalVariety ℂ (D.v ≫ sXp) := by
  have := h.isNormalVariety_plus.1
  exact ⟨(isVariety_iff ℂ (D.v ≫ sXp)).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

/-- **The graph divisor vanishes over `U = Z ∖ Σ`.** If the generic point of a prime divisor `E`
of `G` lies over the open where both `f^±` are isomorphisms, then `g` is an isomorphism there,
so `v(η_E)` is the generic point of a prime divisor `P` of `X⁺` over which `E` is the only prime
divisor; the coefficient of `E` in `H` is that of `P` in `v_* H = 0`. -/
private theorem coeff_eq_zero_of_mem_commonBiregularLocus
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (D : GraphData h) {H : QDivisor D.G}
    (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H) (E : MMP.Mori.PrimeDivisor D.G)
    (hE : (D.u ≫ fm) E.genericPoint ∈ commonBiregularLocus fm fp) : H E = 0 := by
  have hG := D.isNormalizedGraph
  have hZ := h.isNormalVariety_target
  haveI : IsNormal Z := hZ.2
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hgz : (D.u ≫ fm) E.genericPoint ∈ biregularLocus (D.u ≫ fm) :=
    mem_biregularLocus_of_finite (isVariety_graph h D) hZ.1 (D.u ≫ fm)
      (by rw [Category.assoc, h.comp_eq_minus]) (isBirational_graph h D)
      (finite_preimage_of_mem_commonBiregularLocus h D hE)
  have hvx : fp (D.v E.genericPoint) ∈ biregularLocus fp := by
    rw [← Scheme.Hom.comp_apply, ← hG.comp_eq]; exact hE.2
  have hco : Order.coheight (D.v E.genericPoint) = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hvx, ← Scheme.Hom.comp_apply,
      ← hG.comp_eq, MMP.Positivity.coheight_map_of_mem_biregularLocus _ hgz,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hP : P.genericPoint = D.v E.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  obtain ⟨E', hE'P, -, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    h.isNormalVariety_plus (isNormalVariety_graph_plus h D) hG.isBirationalMorphism_plus P
  have hEE' : E' = E := by
    haveI : IsIso ((D.u ≫ fm) ∣_ biregularLocus (D.u ≫ fm)) :=
      isBiregular_biregularLocus (D.u ≫ fm)
    refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict _ _ hgz ?_ rfl)
    change (D.u ≫ fm) E'.genericPoint = (D.u ≫ fm) E.genericPoint
    rw [hG.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hE'P]
    exact congrArg fp hP
  have h0 := hH.transformDivisor_eq_zero
  have := htr H
  rw [h0, hEE'] at this
  exact this.symm

/-- A step diagram with a normalized graph has a graph divisor: the pull-backs of the
`ℚ`-Cartier divisors `D^±` exist, the generic point of `G` mapping to the generic points of
`X^±`. -/
private theorem exists_isGraphDivisor (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : ∃ H : QDivisor D.G, IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H := by
  haveI := D.isNormalizedGraph.isBirationalMorphism_minus.isDominant
  haveI := D.isNormalizedGraph.isBirationalMorphism_plus.isDominant
  have hm := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' D.u
    (Divisor.toQDivisor K + B)
  have hp := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' D.v
    (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B)
  exact ⟨_, h, D.isNormalizedGraph, _, _, hm, hp,
    QDivisor.isPullback_pullback h.isQCartier_minus hm,
    QDivisor.isPullback_pullback h.isQCartier_plus hp, rfl⟩

/-! ### A model over the graph realizing the valuation -/

/-- The birational map `(f')⁻¹ ∘ f : X ⤏ X'` of two birational morphisms to a separated
scheme is a birational map over `Y`. -/
private theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{0}} [IsReduced X]
    [IsReduced X'] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : MMP.Mori.RationalMap X X', MMP.Mori.RationalMap.IsBirational φ ∧
      φ.compHom f' = f.toRationalMap := by
  obtain ⟨em, hem⟩ := hf
  obtain ⟨ep, hep⟩ := hf'
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 Y) hem
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep f' (𝟙 Y) hep
  set e := em.trans ep.symm with he
  have H : e.IsOver (f ≫ 𝟙 Y) (f' ≫ 𝟙 Y) := h1.trans h2.symm
  have H' : e.iso.hom ≫ e.target.ι ≫ f' = e.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using H
  refine ⟨e.toRationalMap, MMP.Mori.RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, H']
  simp

/-- **A model over the graph.** For a divisor `D₀` over `X⁻` there are a normal variety `W` with a
proper birational morphism `w : W ⟶ G` and a prime divisor `E` of `W` such that the divisor
`(W, w ≫ u, E)` over `X⁻` has the valuation of `D₀`. -/
private theorem exists_model (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (D : GraphData h)
    (D₀ : DivisorOver ℂ sXm) :
    ∃ (W : Scheme.{0}) (w : W ⟶ D.G) (hW : IsNormalVariety ℂ ((w ≫ D.u) ≫ sXm))
      (hb : IsBirationalMorphism (w ≫ D.u)), IsProper w ∧ IsBirationalMorphism w ∧
      ∃ E : MMP.Mori.PrimeDivisor W,
        (⟨W, w ≫ D.u, hW, hb, E⟩ : DivisorOver ℂ sXm).valuation = D₀.valuation := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hG := D.isNormalizedGraph
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper (D.u ≫ fm) := inferInstance
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq h.isBirationalMorphism_minus
    (isBirationalMorphism_graph h D)
  obtain ⟨W, g₁, w, hW₁, hg₁, hg₁p, hwp, hw, -, hcomm, E, hE⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq
      h.isNormalVariety_minus (isNormalVariety_graph h D) fm (D.u ≫ fm) φ hφ hφS D₀
  have e : (w ≫ D.u) ≫ sXm = g₁ ≫ sXm := calc
    (w ≫ D.u) ≫ sXm = (w ≫ D.u) ≫ fm ≫ sZ := by rw [h.comp_eq_minus]
    _ = g₁ ≫ fm ≫ sZ := by rw [← Category.assoc g₁, hcomm]; simp only [Category.assoc]
    _ = g₁ ≫ sXm := by rw [h.comp_eq_minus]
  have hW : IsNormalVariety ℂ ((w ≫ D.u) ≫ sXm) := by rw [e]; exact hW₁
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian ((w ≫ D.u) ≫ sXm)
  haveI : IsDominant w := hw.isDominant
  have hb : IsBirationalMorphism (w ≫ D.u) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational D.u w
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hG.isBirationalMorphism_minus)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hw)
  refine ⟨W, w, hW, hb, hwp, hw, E, ?_⟩
  rw [← hE]
  haveI := hg₁.isDominant
  haveI := hb.isDominant
  haveI := h.isBirationalMorphism_minus.isDominant
  ext x
  obtain ⟨t, rfl⟩ := h.isBirationalMorphism_minus.functionFieldMap_bijective.2 x
  change E.divisorialValuation (functionFieldMap (w ≫ D.u) (functionFieldMap fm t)) =
    E.divisorialValuation (functionFieldMap g₁ (functionFieldMap fm t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  simp only [Category.assoc, hcomm]

/-! ### Log discrepancies through local equations -/

/-- **Log discrepancies through a local equation.** Let `ω` be a nonzero rational top form on
the normal variety `X` of dimension `n`, `B` a `ℚ`-divisor and `φ` a rational function with
`v_Γ(φ) = M (ord_Γ ω + coeff_Γ B)` along every prime divisor `Γ` through the image `x` of the
generic point of `E`, for a divisor `(Y, f, E)` over `X` of valuation `ξ` (so `φ` is a local
equation of `M (div ω + B)` near `x`). Then `M (a(ξ; X, B) - 1) = M ord_E(f^*ω) - v_E(f^*φ)`. -/
private theorem mul_sub_one_eq_of_isValuationLogDiscrepancy {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    {n : ℕ} (hn : topologicalKrullDim X = n) {Δ : QDivisor X}
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a : ℝ}
    (ha : IsValuationLogDiscrepancy sX Δ ξ a) (D' : DivisorOver ℂ sX) (hD' : D'.valuation = ξ)
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0) {M : ℕ} (hM : 0 < M)
    {φ : X.functionField} (hφ : φ ≠ 0)
    (hφΓ : ∀ Γ : MMP.Mori.PrimeDivisor X, D'.f D'.E.genericPoint ∈ Γ.support →
      (X.ord φ Γ.genericPoint : ℝ) = M * ((Γ.ordForm ω : ℝ) + (Δ.coeff Γ : ℝ))) :
    haveI := D'.isIntegral
    haveI := D'.isLocallyNoetherian
    haveI := D'.isDominant
    (M : ℝ) * (a - 1) =
      M * D'.ordPullback ω - D'.Y.ord (functionFieldMap D'.f φ) D'.E.genericPoint := by
  classical
  obtain ⟨n', D, -, hDv, hl⟩ := ha
  have hn' : n' = n := by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hl
    rw [hn] at this
    exact_mod_cast this.symm
  subst hn'
  have hv : D.valuation = D'.valuation := hDv.trans hD'.symm
  have hx : D.f D.E.genericPoint = D'.f D'.E.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hv
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have := D'.isDominant
  have e1 : D'.ordPullback ω = D.ordPullback ω :=
    (MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv ω).symm
  have e2 : D'.Y.ord (functionFieldMap D'.f φ) D'.E.genericPoint =
      D.Y.ord (functionFieldMap D.f φ) D.E.genericPoint :=
    MMP.Threefold.Bridges.ord_functionFieldMap_eq_of_valuationOver_eq D.E D'.E hv hφ
  rw [e1, e2]
  rw [← hx] at hφΓ
  obtain ⟨-, -, ω', hω'0, -, m', r, C, C', hCc, hsum, hpb, rfl⟩ := hl
  let := MMP.Mori.functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨β, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set x := D.f D.E.genericPoint with hxdef
  choose V hV ψ hψ using fun i => hCc i x
  let Z0 := MMP.Mori.pointComponent x
  let g : Fin m' → X.functionField := fun i =>
    MMP.Threefold.Mori.Helpers.evalFF Z0 ((ψ i : MMP.Mori.RationalFunctions X))
  have hg : ∀ i, g i ≠ 0 := fun i => ((ψ i).isUnit.map _).ne_zero
  set cω' := (MMP.Mori.ZTensorPower.basis β 1).repr ω' () with hcω'
  set cω := (MMP.Mori.ZTensorPower.basis β 1).repr ω () with hcω
  have hcω'0 : cω' ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hω'0
  have hcω0 : cω ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hω
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  let G : Option (Option (Option (Fin m'))) → X.functionField := fun j =>
    Option.elim j cω' fun j => Option.elim j cω fun j => Option.elim j φ g
  let wt : Option (Option (Option (Fin m'))) → ℝ := fun j =>
    Option.elim j 1 fun j => Option.elim j (-1) fun j => Option.elim j (1 / (M : ℝ)) fun i => -r i
  have hG : ∀ j, G j ≠ 0 := by
    rintro (_ | _ | _ | i)
    exacts [hcω'0, hcω0, hφ, hg i]
  have hgΓ : ∀ (Γ : MMP.Mori.PrimeDivisor X) (i : Fin m'), x ∈ Γ.support →
      X.ord (g i) Γ.genericPoint = (C i).coeff Γ := by
    intro Γ i hΓ
    have hZ : Γ.component = Z0 := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    rw [hψ i Γ ⟨x, hΓ, hV i⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E G hG wt
    fun Γ hΓ => by
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd β
    have f1 : (Γ.ordForm ω' : ℝ) = X.ord cω' Γ.genericPoint + NΓ := by
      exact_mod_cast (by simpa using hNΓ 1 ω' hω'0)
    have f2 : (Γ.ordForm ω : ℝ) = X.ord cω Γ.genericPoint + NΓ := by
      exact_mod_cast (by simpa using hNΓ 1 ω hω)
    have f3 := hφΓ Γ hΓ
    have f4 := hsum Γ
    rw [QDivisor.coeff_toRDivisor] at f4
    simp only [Fintype.sum_option, G, wt, Option.elim]
    simp_rw [hgΓ Γ _ hΓ]
    have f5 : ∑ i, ((C i).coeff Γ : ℝ) * -r i = -∑ i, r i * ((C i).coeff Γ : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [f5, f3]
    field_simp
    linear_combination -f1 + f2 + f4
  have hcoeff : ∀ i, ((C' i).coeff D.E : ℝ) =
      D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint := by
    intro i
    obtain ⟨hC, hCp⟩ := hpb i
    exact_mod_cast MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hCp (hψ i) D.E (hV i) Z0
  have h1 : (D.ordPullback ω' : ℝ) =
      D.Y.ord (functionFieldMap D.f cω') D.E.genericPoint + N := by
    exact_mod_cast (by simpa using hN 1 ω' hω'0)
  have h2 : (D.ordPullback ω : ℝ) =
      D.Y.ord (functionFieldMap D.f cω) D.E.genericPoint + N := by
    exact_mod_cast (by simpa using hN 1 ω hω)
  simp only [Fintype.sum_option, G, wt, Option.elim] at key
  simp_rw [hcoeff]
  have f5 : ∑ i, (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) * -r i =
      -∑ i, r i * (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [f5] at key
  field_simp at key
  linear_combination (M : ℝ) * h1 - (M : ℝ) * h2 + key

/-! ### Pull-backs of forms -/

section Forms

variable {k : Type} [Field k] [PerfectField k]

/-- Along a morphism `f` inducing an isomorphism of function fields, every rational pluri-form
is a pull-back: `τ = f^*σ`, with `σ ≠ 0` when `τ ≠ 0`. -/
private theorem exists_pullbackRationalPluriForms_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms (f ≫ sY) d m) :
    ∃ σ : RationalPluriForms sY d m, pullbackRationalPluriForms sY f σ = τ ∧
      (τ ≠ 0 → σ ≠ 0) := by
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY f hf hd
  set bY := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m with hbY
  set bX := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m with hbX
  obtain ⟨c, hc⟩ := hf.2 (bX.repr τ ())
  have hpull : pullbackRationalPluriForms sY f (c • bY ()) = τ := by
    change pullbackForms m (c • bY ()) = τ
    rw [pullbackForms_eq hω m]
    apply bX.ext_elem
    intro i
    obtain rfl : i = () := rfl
    rw [repr_pullbackFormsAlong hω m]
    simp only [bY, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    exact hc
  refine ⟨c • bY (), hpull, fun hτ hσ => hτ ?_⟩
  rw [← hpull, hσ]
  change pullbackForms m 0 = 0
  rw [pullbackForms_eq hω m]
  simp [pullbackFormsAlong]

/-- Along a morphism inducing an isomorphism of function fields, the pull-back of a nonzero
rational pluri-form is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d) {m : ℤ}
    {σ : RationalPluriForms sY d m} (hσ : σ ≠ 0) : pullbackRationalPluriForms sY f σ ≠ 0 := by
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY f hf hd
  rw [show pullbackRationalPluriForms sY f σ = pullbackFormsAlong hω m σ from
    pullbackForms_eq hω m σ]
  intro h0
  have h1 := repr_pullbackFormsAlong hω m σ
  rw [h0] at h1
  have h2 : algebraMap Y.functionField X.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr σ ()) = 0 := by
    rw [← h1]
    exact (DFunLike.congr_fun (LinearEquiv.map_zero _) ()).trans Finsupp.zero_apply
  exact repr_ne_zero_of_ne_zero _ hσ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h2)

/-- **Orders of pulled-back forms along a composite.** For `g : W ⟶ X` and a birational
`f : X ⟶ Y`, the order along `(W, g, F)` over `X` of `f^*σ` is the order along
`(W, g ≫ f, F)` over `Y` of `σ`. -/
private theorem ordPullback_pullbackRationalPluriForms {X Y W : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    [LocallyOfFiniteType (f ≫ sY)] (hf : IsBirationalMorphism f) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d)
    {g : W ⟶ X} (hW : IsNormalVariety k (g ≫ f ≫ sY)) (hg : IsBirationalMorphism g)
    (hgf : IsBirationalMorphism (g ≫ f)) (F : MMP.Mori.PrimeDivisor W) {m : ℤ}
    (σ : RationalPluriForms sY d m) :
    (⟨W, g, hW, hg, F⟩ : DivisorOver k (f ≫ sY)).ordPullback
        (pullbackRationalPluriForms sY f σ) =
      (⟨W, g ≫ f, hW, hgf, F⟩ : DivisorOver k sY).ordPullback σ := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsDominant g := hg.isDominant
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ f ≫ sY)
  change F.ordForm (pullbackRationalPluriForms (f ≫ sY) g (pullbackRationalPluriForms sY f σ)) =
    F.ordForm (pullbackRationalPluriForms sY (g ≫ f) σ)
  rw [MMP.Flips.pullbackRationalPluriForms_comp f g hf.functionFieldMap_bijective
    hg.functionFieldMap_bijective hd σ]
  rfl

/-- The order of the pull-back of a form along equal morphisms is the same. -/
private theorem ordForm_pullbackRationalPluriForms_congr {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)} {f₁ f₂ : Y ⟶ X}
    [IsDominant f₁] [IsDominant f₂] (hf : f₁ = f₂) (E : MMP.Mori.PrimeDivisor Y) {d : ℕ}
    {m : ℤ} (σ : RationalPluriForms sX d m) :
    E.ordForm (pullbackRationalPluriForms sX f₁ σ) =
      E.ordForm (pullbackRationalPluriForms sX f₂ σ) := by
  subst hf
  rfl

end Forms

/-- The order along `Γ` of the rational function of a local equation of a divisor `L` on an open
`U` is the coefficient of `Γ` in `L`, for every prime divisor `Γ` through a point `x ∈ U`. -/
private theorem ord_evalFF_eq_coeff {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {L : Divisor X} {U : X.Opens} {ψ : (MMP.Mori.RationalFunctions X)ˣ}
    (hψ : L.IsLocalEquation U ψ) {x : X} (hx : x ∈ U) (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : x ∈ Γ.support) :
    X.ord (MMP.Threefold.Mori.Helpers.evalFF (MMP.Mori.pointComponent x)
      (ψ : MMP.Mori.RationalFunctions X)) Γ.genericPoint = L Γ := by
  have hZ : Γ.component = MMP.Mori.pointComponent x := Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  change _ = L.coeff Γ
  rw [hψ Γ ⟨x, hΓ, hx⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]

/-- **The common differential.** Let `σ` be a rational top form on `Z` whose pull-back to `X⁻`
cuts out the canonical divisor `K⁻`. Then its pull-back to `X⁺` cuts out
`K⁺ = (f⁺)⁻¹_* f⁻_* K⁻`: at a prime divisor `P` of `X⁺`, take the prime divisor `E` of the
normalized graph over `P` and the prime divisor `P⁻ = u(E)` of `X⁻`; all the maps are local
isomorphisms at these generic points. -/
private theorem ordForm_pullbackRationalPluriForms_eq_flipTransform
    [IsIntegral Z] [IsDominant fm] [IsDominant fp]
    (h : IsFourfoldStepDiagram (fm ≫ sZ) sZ (fp ≫ sZ) K B fm fp) (D : GraphData h) {n : ℕ}
    (hnZ : topologicalKrullDim Z = n) (σ : RationalPluriForms sZ n 1)
    (hσ : ∀ Γ : MMP.Mori.PrimeDivisor Xm,
      Γ.ordForm (pullbackRationalPluriForms sZ fm σ) = K Γ)
    (P : MMP.Mori.PrimeDivisor Xp) :
    P.ordForm (pullbackRationalPluriForms sZ fp σ) = flipTransform fm fp K P := by
  have hG := D.isNormalizedGraph
  have hZ := h.isNormalVariety_target
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  haveI : LocallyOfFiniteType (fm ≫ sZ) := hXm.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hXp.1.toLocallyOfFiniteType
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  have hbm := h.isBirationalMorphism_minus
  have hbp := h.isBirationalMorphism_plus
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  haveI : MMP.Mori.IsVariety ℂ (fm ≫ sZ) := hXm.1
  haveI : MMP.Mori.IsVariety ℂ (fp ≫ sZ) := hXp.1
  have hdZ := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  have hdm := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := fm ≫ sZ)
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fm ≫ sZ)
      hbm).symm.trans hnZ)
  have hdp := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := fp ≫ sZ)
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fp ≫ sZ)
      hbp).symm.trans hnZ)
  obtain ⟨E, hvE, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
      hXp (isNormalVariety_graph_plus h D) hG.isBirationalMorphism_plus P
  obtain ⟨Pm, huE, hfl⟩ := exists_eq_genericPoint_flipTransform_apply hbm
    h.isSmallMorphism_plus P (D.u E.genericPoint)
    (by rw [← Scheme.Hom.comp_apply, hG.comp_eq, Scheme.Hom.comp_apply, hvE])
  haveI := isIso_stalkMap_of_map_eq_genericPoint hG.isBirationalMorphism_minus huE
  haveI := hiso
  rw [hfl K, ← hσ Pm,
    ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso D.v
      hG.isBirationalMorphism_plus.functionFieldMap_bijective hdp E P hvE,
    ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso D.u
      hG.isBirationalMorphism_minus.functionFieldMap_bijective hdm E Pm huE,
    MMP.Flips.pullbackRationalPluriForms_comp fp D.v hbp.functionFieldMap_bijective
      hG.isBirationalMorphism_plus.functionFieldMap_bijective hdZ σ,
    MMP.Flips.pullbackRationalPluriForms_comp fm D.u hbm.functionFieldMap_bijective
      hG.isBirationalMorphism_minus.functionFieldMap_bijective hdZ σ]
  exact ordForm_pullbackRationalPluriForms_congr hG.comp_eq.symm E σ

/-- The order of a quotient of nonzero rational functions is the difference of the orders. -/
private theorem ord_mul_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {a b : X.functionField} (ha : a ≠ 0) (hb : b ≠ 0) (x : X) :
    X.ord (a * b⁻¹) x = X.ord a x - X.ord b x := by
  have hinv : X.ord b⁻¹ x = -X.ord b x := by
    have := MMP.Mori.ord_zpow x hb (-1)
    rwa [zpow_neg, zpow_one, neg_one_mul] at this
  rw [Scheme.ord_mul ha (inv_ne_zero hb), hinv]
  ring

/-! ### The discrepancy comparison through the graph divisor -/

/-- **The comparison of discrepancies is the graph divisor** (the formula
`a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = ξ(H)`). For a model `w : W ⟶ G` and a prime divisor `E` of `W`,
there are `M > 0` and a local equation `φ` of `M H` near `w(η_E)` with
`M (a(E; X⁺, B⁺) - a(E; X⁻, B⁻)) = v_E(w^*φ)`. -/
private theorem exists_ord_eq_mul_sub (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {w : W ⟶ D.G}
    [IsDominant w] [IsProper w] (hW : IsNormalVariety ℂ ((w ≫ D.u) ≫ sXm))
    (hW' : IsNormalVariety ℂ ((w ≫ D.v) ≫ sXp)) (hb : IsBirationalMorphism (w ≫ D.u))
    (hb' : IsBirationalMorphism (w ≫ D.v)) (E : MMP.Mori.PrimeDivisor W)
    {ξ : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : (⟨W, w ≫ D.u, hW, hb, E⟩ : DivisorOver ℂ sXm).valuation = ξ)
    (hξp : (⟨W, w ≫ D.v, hW', hb', E⟩ : DivisorOver ℂ sXp).valuation = ξp)
    {am ap : ℝ} (ham : IsValuationLogDiscrepancy sXm B ξ am)
    (hap : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) ξp ap) :
    ∃ (M : ℕ) (φ : D.G.functionField), 0 < M ∧ φ ≠ 0 ∧
      (∀ Γ : MMP.Mori.PrimeDivisor D.G, w E.genericPoint ∈ Γ.support →
        (D.G.ord φ Γ.genericPoint : ℚ) = M * H Γ) ∧
      (M : ℝ) * (ap - am) = W.ord (functionFieldMap w φ) E.genericPoint := by
  classical
  have hG := D.isNormalizedGraph
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hbm := h.isBirationalMorphism_minus
  have hbp := h.isBirationalMorphism_plus
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  haveI := hb.isDominant
  haveI := hb'.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  obtain ⟨n, hK⟩ := h.isCanonicalDivisor
  have hnm : topologicalKrullDim Xm = n := hK.topologicalKrullDim_eq
  obtain rfl := h.comp_eq_minus
  obtain rfl := h.comp_eq_plus
  haveI : LocallyOfFiniteType (fm ≫ sZ) := hXm.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hXp.1.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  haveI : MMP.Mori.IsVariety ℂ (fm ≫ sZ) := hXm.1
  haveI : MMP.Mori.IsVariety ℂ (fp ≫ sZ) := hXp.1
  have hnZ : topologicalKrullDim Z = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fm ≫ sZ)
      hbm).trans hnm
  have hnp : topologicalKrullDim Xp = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fp ≫ sZ)
      hbp).symm.trans hnZ
  have hdZ := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  -- the common differential
  obtain ⟨ω₀, hω₀, hω₀K⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXm hK
  obtain ⟨σ, rfl, hσ⟩ :=
    exists_pullbackRationalPluriForms_eq fm hbm.functionFieldMap_bijective hdZ ω₀
  have hσ0 := hσ hω₀
  have hωp0 := pullbackRationalPluriForms_ne_zero fp hbp.functionFieldMap_bijective hdZ hσ0
  have hωpK := ordForm_pullbackRationalPluriForms_eq_flipTransform h D hnZ σ hω₀K
  -- Cartier multiples of `D^±`
  obtain ⟨m₁, hm₁, L₁₀, hL₁₀, hL₁₀c⟩ := h.isQCartier_minus.exists_pos
  obtain ⟨m₂, hm₂, L₂₀, hL₂₀, hL₂₀c⟩ := h.isQCartier_plus.exists_pos
  set M := m₁ * m₂ with hMdef
  have hM : 0 < M := Nat.mul_pos hm₁ hm₂
  set L₁ : Divisor Xm := (m₂ : ℤ) • L₁₀ with hL₁def
  set L₂ : Divisor Xp := (m₁ : ℤ) • L₂₀ with hL₂def
  have hL₁ : Divisor.toQDivisor L₁ = (M : ℤ) • (Divisor.toQDivisor K + B) := by
    rw [hL₁def, map_zsmul, hL₁₀, smul_smul, hMdef]
    push_cast
    rw [mul_comm]
  have hL₂ : Divisor.toQDivisor L₂ = (M : ℤ) •
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B) := by
    rw [hL₂def, map_zsmul, hL₂₀, smul_smul, hMdef]
    push_cast
    rfl
  have hL₁c : L₁.IsCartier := hL₁₀c.zsmul _
  have hL₂c : L₂.IsCartier := hL₂₀c.zsmul _
  have cL₁ : ∀ Γ, (L₁ Γ : ℚ) = M * ((K Γ : ℚ) + B Γ) := fun Γ => by
    have := congrArg (fun G : QDivisor Xm => G Γ) hL₁
    simp only [Finsupp.smul_apply, Finsupp.add_apply, zsmul_eq_mul, Int.cast_natCast] at this
    exact this
  have cL₂ : ∀ Γ, (L₂ Γ : ℚ) =
      M * ((flipTransform fm fp K Γ : ℚ) + flipTransform fm fp B Γ) := fun Γ => by
    have := congrArg (fun G : QDivisor Xp => G Γ) hL₂
    simp only [Finsupp.smul_apply, Finsupp.add_apply, zsmul_eq_mul, Int.cast_natCast] at this
    exact this
  -- local equations near the centres
  set xm := (w ≫ D.u) E.genericPoint with hxm
  set xp := (w ≫ D.v) E.genericPoint with hxp
  obtain ⟨U₁, hxU₁, ψ₁, hψ₁⟩ := hL₁c xm
  obtain ⟨U₂, hxU₂, ψ₂, hψ₂⟩ := hL₂c xp
  set φ₁ := MMP.Threefold.Mori.Helpers.evalFF (MMP.Mori.pointComponent xm)
    (ψ₁ : MMP.Mori.RationalFunctions Xm) with hφ₁def
  set φ₂ := MMP.Threefold.Mori.Helpers.evalFF (MMP.Mori.pointComponent xp)
    (ψ₂ : MMP.Mori.RationalFunctions Xp) with hφ₂def
  have hφ₁ : φ₁ ≠ 0 := (ψ₁.isUnit.map _).ne_zero
  have hφ₂ : φ₂ ≠ 0 := (ψ₂.isUnit.map _).ne_zero
  -- the two log discrepancies
  have em := mul_sub_one_eq_of_isValuationLogDiscrepancy hXm hnm ham _ hξ hω₀ hM hφ₁
    fun Γ hΓ => by
      rw [ord_evalFF_eq_coeff hψ₁ hxU₁ Γ hΓ, hω₀K Γ]
      exact_mod_cast cL₁ Γ
  have ep := mul_sub_one_eq_of_isValuationLogDiscrepancy hXp hnp hap _ hξp hωp0 hM hφ₂
    fun Γ hΓ => by
      rw [ord_evalFF_eq_coeff hψ₂ hxU₂ Γ hΓ, hωpK Γ]
      exact_mod_cast cL₂ Γ
  -- the common form along `E`
  have hgf : IsBirationalMorphism ((w ≫ D.u) ≫ fm) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fm (w ≫ D.u)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbm)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
  have hgf' : IsBirationalMorphism ((w ≫ D.v) ≫ fp) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fp (w ≫ D.v)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbp)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb')
  have e1 := ordPullback_pullbackRationalPluriForms fm hbm hdZ hW hb hgf E σ
  have e2 := ordPullback_pullbackRationalPluriForms fp hbp hdZ hW' hb' hgf' E σ
  haveI := hgf.isDominant
  haveI := hgf'.isDominant
  have hv : (⟨W, (w ≫ D.v) ≫ fp, hW', hgf', E⟩ : DivisorOver ℂ sZ).valuation =
      (⟨W, (w ≫ D.u) ≫ fm, hW, hgf, E⟩ : DivisorOver ℂ sZ).valuation := by
    change E.valuationOver ((w ≫ D.v) ≫ fp) = E.valuationOver ((w ≫ D.u) ≫ fm)
    simp only [Category.assoc, hG.comp_eq]
  have e3 := MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hZ hnZ hv σ
  -- the rational function on `G`
  set φ := functionFieldMap D.u φ₁ * (functionFieldMap D.v φ₂)⁻¹ with hφdef
  have hu₁ : functionFieldMap D.u φ₁ ≠ 0 := (map_ne_zero _).mpr hφ₁
  have hv₂ : functionFieldMap D.v φ₂ ≠ 0 := (map_ne_zero _).mpr hφ₂
  refine ⟨M, φ, hM, mul_ne_zero hu₁ (inv_ne_zero hv₂), fun Γ hΓ => ?_, ?_⟩
  · obtain ⟨Hm, Hp, hm, hp, hHm, hHp, hHeq⟩ := hH.exists_pullback
    obtain ⟨L₁', hL₁', hpb₁⟩ := hHm M hM L₁ hL₁ hL₁c
    obtain ⟨L₂', hL₂', hpb₂⟩ := hHp M hM L₂ hL₂ hL₂c
    have hsp : Γ.genericPoint ⤳ w E.genericPoint := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hΓ
    have hU₁ : D.u Γ.genericPoint ∈ U₁ := (hsp.map D.u.continuous).mem_open U₁.2 hxU₁
    have hU₂ : D.v Γ.genericPoint ∈ U₂ := (hsp.map D.v.continuous).mem_open U₂.2 hxU₂
    have c1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hpb₁ hψ₁ Γ hU₁
      (MMP.Mori.pointComponent xm)
    have c2 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hpb₂ hψ₂ Γ hU₂
      (MMP.Mori.pointComponent xp)
    have d1 := congrArg (fun G : QDivisor D.G => G Γ) hL₁'
    have d2 := congrArg (fun G : QDivisor D.G => G Γ) hL₂'
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at d1 d2
    change (L₁' Γ : ℚ) = M * Hm Γ at d1
    change (L₂' Γ : ℚ) = M * Hp Γ at d2
    rw [ord_mul_inv hu₁ hv₂, hHeq, Finsupp.sub_apply]
    change (L₁'.coeff Γ : ℚ) = _ at d1
    rw [c1] at d1
    change (L₂'.coeff Γ : ℚ) = _ at d2
    rw [c2] at d2
    push_cast
    rw [d1, d2]
    ring
  · rw [map_mul, map_inv₀, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      ord_mul_inv ((map_ne_zero _).mpr hφ₁) ((map_ne_zero _).mpr hφ₂)]
    have e4 : (⟨W, w ≫ D.u, hW, hb, E⟩ : DivisorOver ℂ (fm ≫ sZ)).ordPullback
        (pullbackRationalPluriForms sZ fm σ) =
        (⟨W, w ≫ D.v, hW', hb', E⟩ : DivisorOver ℂ (fp ≫ sZ)).ordPullback
          (pullbackRationalPluriForms sZ fp σ) := by
      rw [e1, e2, e3]
    change (M : ℝ) * (am - 1) = M * _ - _ at em
    change (M : ℝ) * (ap - 1) = M * _ - _ at ep
    rw [e4] at em
    push_cast
    linear_combination ep - em

/-! ### Proper curves and intersection numbers -/

section Curves

open MMP.Flips

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

end Intersection

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve contracted by `f` that meets `S` without lying
in it. -/
private theorem exists_properCurve_isContractedBy (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : MMP.Mori.ProperCurve sY, C.IsContractedBy f ∧ ¬ Set.range C.ι ⊆ S ∧
      (Set.range C.ι ∩ S).Nonempty := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  have key : ∀ {F S : Set Y}, IsClosed F → _root_.IsConnected F → IsClosed S →
      (F ∩ S).Nonempty → ¬ F ⊆ S → ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
    intro F S hF hFc hS hmeet hsub
    set T := F \ S
    have hTF : closure T ⊆ F := closure_minimal Set.diff_subset hF
    by_cases hdis : (closure T ∩ S).Nonempty
    · obtain ⟨s, hsT, hsS⟩ := hdis
      obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
        TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
          (isClosed_closure : IsClosed (closure T))
      have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
        refine closure_minimal (fun y hy => ?_) ?_
        · have : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
          obtain ⟨z, hz, hyz⟩ := this
          exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
        · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
      obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
      obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
      have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
      exact ⟨ζ, hTF (hzT hζ.mem), fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS),
        s, hsS, hζ.specializes hsz⟩
    · obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
      obtain ⟨w, -, hwT, hwS⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
        isClosed_closure hS (fun a ha => by
          by_cases haS : a ∈ S
          · exact Or.inr haS
          · exact Or.inl (subset_closure (show a ∈ T from ⟨ha, haS⟩)))
        ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
      exact (hdis ⟨w, hwT, hwS⟩).elim
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ := key hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  -- the scheme-theoretic fibre, proper over `k`
  let ι := f.fiberι x
  let sF := ι ≫ sY
  haveI : IsProper sF := by
    have h : sF = f.fiberToSpecResidueField x ≫ (X.fromSpecResidueField x ≫ sX) := by
      simp only [sF, ι, ← hf, Scheme.Hom.fiber_fac_assoc]
    rw [h]
    haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
    haveI : LocallyOfFiniteType (X.fromSpecResidueField x) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp hx
    haveI : IsFinite (X.fromSpecResidueField x ≫ sX) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
    haveI : IsProper (f.fiberToSpecResidueField x) :=
      inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
    haveI : IsProper (X.fromSpecResidueField x ≫ sX) := inferInstance
    infer_instance
  haveI : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {x} := f.range_fiberι x
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηF
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpF
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by
    rw [← hemb.isInducing.specializes_iff, hη', hp']; exact hηp
  have hp'c : IsClosed ({p'} : Set (f.fiber x)) := by
    have : ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} := by
      ext z; simp [← hp', hemb.injective.eq_iff]
    rw [this]; exact (mem_closedPoints_iff.mp hpc).preimage ι.continuous
  obtain ⟨y', -, hy'p', hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  let C' : MMP.Mori.ProperCurve sF := ⟨y', hy'⟩
  -- its image in `Y` is a proper curve of `Y`
  have hφsY : (C'.ι ≫ ι) ≫ sY = C'.ι ≫ sF := Category.assoc _ _ _
  haveI : AlgebraicGeometry.IsCurve k ((C'.ι ≫ ι) ≫ sY) := hφsY ▸ C'.isCurve
  haveI : IsProper ((C'.ι ≫ ι) ≫ sY) := by rw [hφsY]; infer_instance
  have hrange : Set.range (C'.ι ≫ ι) = closure {ι y'} := C'.range_comp ι rfl
  have hinj : Function.Injective (C'.ι ≫ ι) := fun a b h =>
    C'.ι.isEmbedding.injective (hemb.injective (by simpa using h))
  have hnc : ¬ ∃ z, Set.range (C'.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    have : Subsingleton C'.scheme := ⟨fun a b => hinj (by
      have ha : (C'.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
      have hb : (C'.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
      exact ha.trans hb.symm)⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C'.scheme
    rw [C'.dim_eq] at h0
    exact absurd h0 (by decide)
  have hcurve := MMP.Mori.isCurve_imageι_comp sY (C'.ι ≫ ι) hnc
  have hker := C'.ker_comp ι
  have hdim : topologicalKrullDim (curveSubschemeAt (ι y')) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim (C'.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (ι y') ≫ sY) := by
    have h1 : IsProper ((C'.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C'.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1
  let C : MMP.Mori.ProperCurve sY := ⟨ι y', ⟨hdim, hprop⟩⟩
  have hrC : Set.range C.ι = closure {ι y'} := C.range_ι
  have hclF : closure {ι y'} ⊆ f.base ⁻¹' {x} := by
    rw [← hrange, ← hrι]
    rintro _ ⟨w, rfl⟩
    exact ⟨C'.ι w, by simp⟩
  have hCf : C.IsContractedBy f := fun z hz => by
    have h1 := hclF hz
    have h2 := hclF (subset_closure rfl : ι y' ∈ closure {ι y'})
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  refine ⟨C, hCf, ?_, ?_⟩
  · rw [hrC]
    intro h
    exact hy'S (h (subset_closure rfl))
  · refine ⟨p, ?_, hpS⟩
    rw [hrC, ← hp']
    exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

/-- **A contracted curve through a point with positive-dimensional fibre.** If `f : Y ⟶ X` is a
proper birational morphism of normal varieties and `z` a closed point of `Y` mapped outside the
biregular locus of `f`, then some proper curve contracted by `f` passes through `z`. -/
private theorem exists_properCurve_specializes (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsNormal X] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (z : Y) (hz : IsClosed ({z} : Set Y)) (hzf : f z ∉ biregularLocus f) :
    ∃ C : MMP.Mori.ProperCurve sY, C.IsContractedBy f ∧ C.point ⤳ z := by
  have := hX.1.toIsIntegral
  have := hY.1.toIsIntegral
  have hx : IsClosed ({f z} : Set X) := by
    simpa [Set.image_singleton] using f.isClosedMap _ hz
  have hsub : ¬ f.base ⁻¹' {f z} ⊆ {z} := by
    intro h
    obtain ⟨-, hEx, -⟩ := MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k
      hY.1 hX.1 f hf (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
    have hzE : z ∈ (MMP.Mori.exceptionalSet f : Set Y) := hzf
    rw [hEx] at hzE
    have hss : (f.base ⁻¹' {f z}).Subsingleton := Set.subsingleton_singleton.anti h
    haveI : Subsingleton (f.base ⁻¹' {f z}) := hss.coe_sort
    exact absurd (topologicalKrullDim_zero_of_discreteTopology _) (not_le.mpr hzE)
  obtain ⟨C, hCf, -, w, hw, hwz⟩ := exists_properCurve_isContractedBy k sX sY hX hY f hf hfb
    (f z) hx hz ⟨z, rfl, rfl⟩ hsub
  refine ⟨C, hCf, ?_⟩
  rw [Set.mem_singleton_iff.mp hwz, C.range_ι] at hw
  exact specializes_iff_mem_closure.mpr hw

end Curves

/-! ### Effectivity and support of the graph divisor -/

/-- **`-H` is positive on contracted curves.** The graph divisor is `H = -(1/m) L` for a Cartier
divisor `L = -mH`, `m > 0`, ample relative to `g = u ≫ f⁻`; so `L` has positive degree on every
proper curve contracted by `g`. -/
private theorem exists_eq_smul_degreeOn_pos (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H) :
    ∃ (m : ℕ) (L : Divisor D.G) (hL : L.IsCartier), 0 < m ∧
      QDivisor.toRDivisor H = (-1 / (m : ℝ)) • Divisor.toRDivisor L ∧
      ∀ C : MMP.Mori.ProperCurve (D.u ≫ sXm), C.IsContractedBy (D.u ≫ fm) →
        0 < L.degreeOn ℂ (D.u ≫ sXm) C.ι C.dim_le hL := by
  obtain ⟨m, hm, L, hL, hLq, hamp⟩ := hH.hasRelativelyAmpleMultiple_neg
  refine ⟨m, L, hL, hm, ?_, fun C hC => ?_⟩
  · ext P
    have h1 := congrArg (fun G : QDivisor D.G => G P) hLq
    simp only [Finsupp.smul_apply, Finsupp.neg_apply, zsmul_eq_mul, Int.cast_natCast] at h1
    change ((L P : ℤ) : ℚ) = _ at h1
    change ((H P : ℚ) : ℝ) = (-1 / (m : ℝ)) * ((L P : ℤ) : ℝ)
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have h2 : ((L P : ℤ) : ℝ) = m * (-((H P : ℚ) : ℝ)) := by exact_mod_cast h1
    rw [h2]
    field_simp
  · haveI := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
      (D.u ≫ fm) L.divisorialSheaf hamp C hC

/-- The graph divisor, as an `ℝ`-divisor, is a combination of Cartier divisors. -/
private theorem isCartierCombination_toRDivisor_of_eq_smul {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {H : QDivisor X} {L : Divisor X} (hL : L.IsCartier)
    {c : ℝ} (hHL : QDivisor.toRDivisor H = c • Divisor.toRDivisor L) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor H) :=
  ⟨1, ![c], ![L], fun j => by rw [Fin.fin_one_eq_zero j]; exact hL, by
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]; exact hHL⟩

/-- **`-H` is `g`-nef.** -/
private theorem isRelativelyNef_neg_toRDivisor (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H) :
    MMP.Flips.IsRelativelyNef ℂ (D.u ≫ sXm) (D.u ≫ fm) (-QDivisor.toRDivisor H) := by
  haveI : QuasiCompact (D.u ≫ sXm) := (isVariety_graph h D).toQuasiCompact
  obtain ⟨m, L, hL, hm, hHL, hpos⟩ := exists_eq_smul_degreeOn_pos h D hH
  refine ⟨1, ![1 / (m : ℝ)], ![L], fun j => by rw [Fin.fin_one_eq_zero j]; exact hL, ?_,
    fun C hC x hx => ?_⟩
  · rw [hHL, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero, ← neg_smul]
    congr 1
    ring
  · obtain ⟨hL', d, -, hd, hxd⟩ := hx
    have h0 := Oai4C1.Negativity.eq_degreeOn_of_isCartierIntersectionNumber (hd 0)
    have hp := hpos C hC
    rw [hxd]
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rw [h0]
    have : (0 : ℝ) < (L.degreeOn ℂ (D.u ≫ sXm) C.ι C.dim_le hL : ℝ) := by exact_mod_cast hp
    exact mul_nonneg (by positivity) this.le

/-- **The graph divisor is effective**, by the negativity lemma: `-H` is `g`-nef, and `H`
vanishes along every prime divisor of `G` that is not exceptional over `Z`, since such a divisor
lies over a point of codimension one of `Z`, where both `f^±` are isomorphisms. -/
private theorem coeff_nonneg_of_isGraphDivisor (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H)
    (Γ : MMP.Mori.PrimeDivisor D.G) : 0 ≤ H Γ := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hGv := isNormalVariety_graph h D
  haveI : QuasiCompact (D.u ≫ sXm) := (isVariety_graph h D).toQuasiCompact
  have hbg := isBirationalMorphism_graph h D
  have hf : (D.u ≫ fm) ≫ sZ = D.u ≫ sXm := by rw [Category.assoc, h.comp_eq_minus]
  obtain ⟨m, L, hL, hm, hHL, -⟩ := exists_eq_smul_degreeOn_pos h D hH
  have hB := isCartierCombination_toRDivisor_of_eq_smul hL hHL
  have hnef := isRelativelyNef_neg_toRDivisor h D hH
  have hM : MMP.Flips.IsCartierCombination (-QDivisor.toRDivisor H) := by
    obtain ⟨n, r, Ls, hLs, hpres⟩ := hB
    exact ⟨n, -r, Ls, hLs, by rw [hpres]; simp [Finset.sum_neg_distrib, neg_smul]⟩
  have h0Z : MMP.Flips.IsCartierCombination (0 : RDivisor Z) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have h0G : MMP.Flips.IsCartierCombination (0 : RDivisor D.G) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have hpb0 : MMP.Flips.IsRCartierPullback (D.u ≫ fm) (0 : RDivisor Z) 0 :=
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hnum : MMP.Flips.IsNumericallyEquivalentOver ℂ (D.u ≫ sXm) (D.u ≫ fm) 0
      (-QDivisor.toRDivisor H + QDivisor.toRDivisor H) := by
    rw [neg_add_cancel]
    exact ⟨h0G, h0G, fun C _ m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ =>
      (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ (D.u ≫ sXm) C).1 0 r₁ L₁ r₂ L₂ x₁ x₂ h₁ h₂⟩
  obtain ⟨n, hn⟩ := Oai4C1.Negativity.exists_topologicalKrullDim_eq_natCast sZ
  have heff := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback ℂ sZ (D.u ≫ sXm)
    hZ hGv (D.u ≫ fm) hf hbg h0Z hpb0 hM hnef hB (fun P hP => by
      have hco : Order.coheight ((D.u ≫ fm) P.genericPoint) ≤ 1 := by
        by_contra hc
        rw [not_le] at hc
        apply hP
        refine ⟨by rw [hf]; exact hGv, hbg, inferInstance, ?_⟩
        unfold MMP.Flips.ProperDivisorOver.IsExceptional
        rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
          DivisorOver.center_eq_closure_genericPoint, hn]
        have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sZ
          ((D.u ≫ fm) P.genericPoint)
        rw [hn] at hd
        exact (Oai4C1.Negativity.withBot_add_two_le_iff hd).mpr (Order.add_one_le_of_lt hc)
      have hx : ringKrullDim (Z.presheaf.stalk ((D.u ≫ fm) P.genericPoint)) ≤ 1 := by
        rw [ringKrullDim_stalk_eq_coheight]
        exact_mod_cast hco
      have hzm := MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hZ fm
        (by rw [h.comp_eq_minus]; exact h.isNormalVariety_minus.1) h.isBirationalMorphism_minus hx
      have hzp := MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hZ fp
        (by rw [h.comp_eq_plus]; exact h.isNormalVariety_plus.1) h.isBirationalMorphism_plus hx
      rw [QDivisor.coeff_toRDivisor]
      have := coeff_eq_zero_of_mem_commonBiregularLocus h D hH P ⟨hzm, hzp⟩
      change (0 : ℝ) ≤ ((H P : ℚ) : ℝ)
      rw [this]
      simp) hnum
  have := heff Γ
  rw [QDivisor.coeff_toRDivisor] at this
  exact_mod_cast this

/-- A point of the bad locus of the base lies outside the biregular locus of the structure map
`g = u ≫ f⁻` of the normalized graph: over the biregular locus the fibres of `g`, hence those of
`f^±`, are single points. -/
private theorem notMem_biregularLocus_of_mem_badLocusBase
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (D : GraphData h) {z : Z}
    (hz : z ∈ badLocusBase fm fp) : z ∉ biregularLocus (D.u ≫ fm) := by
  intro hzg
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hG := D.isNormalizedGraph
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  haveI : IsIso ((D.u ≫ fm) ∣_ biregularLocus (D.u ≫ fm)) :=
    isBiregular_biregularLocus (D.u ≫ fm)
  have hs := MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict
    (D.u ≫ fm) _ hzg
  refine hz ⟨?_, ?_⟩
  · refine mem_biregularLocus_of_finite h.isNormalVariety_minus.1 hZ.1 fm h.comp_eq_minus
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_minus)
      ((hs.finite.image D.u).subset fun a ha => ?_)
    obtain ⟨x, rfl⟩ := D.u.surjective a
    exact ⟨x, ha, rfl⟩
  · refine mem_biregularLocus_of_finite h.isNormalVariety_plus.1 hZ.1 fp h.comp_eq_plus
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_plus)
      ((hs.finite.image D.v).subset fun a ha => ?_)
    obtain ⟨x, rfl⟩ := D.v.surjective a
    refine ⟨x, ?_, rfl⟩
    change (D.u ≫ fm) x = z
    rw [hG.comp_eq]; exact ha

/-- **The support of the graph divisor contains `g⁻¹(Σ)`.** By the negativity lemma over a point,
the fibre of `g` over `g(y)` lies in `Supp H` or misses it. In the second case `H = 0` near a
closed point `y₀ ∈ cl{y}`, which lies over `Σ`, so off the biregular locus of `g`; a proper curve
contracted by `g` through `y₀` then misses `Supp H`, so `H · C ≥ 0`, while `-H` is `g`-ample. -/
private theorem exists_mem_support_coeff_ne_zero (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H)
    {y : D.G} (hy : (D.u ≫ fm) y ∈ badLocusBase fm fp) :
    ∃ Γ : MMP.Mori.PrimeDivisor D.G, y ∈ Γ.support ∧ H Γ ≠ 0 := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  have hGv := isNormalVariety_graph h D
  haveI : QuasiCompact (D.u ≫ sXm) := (isVariety_graph h D).toQuasiCompact
  haveI : LocallyOfFiniteType (D.u ≫ sXm) := (isVariety_graph h D).toLocallyOfFiniteType
  haveI : JacobsonSpace D.G := LocallyOfFiniteType.jacobsonSpace (D.u ≫ sXm)
  have hbg := isBirationalMorphism_graph h D
  have hf : (D.u ≫ fm) ≫ sZ = D.u ≫ sXm := by rw [Category.assoc, h.comp_eq_minus]
  obtain ⟨m, L, hL, hm, hHL, hpos⟩ := exists_eq_smul_degreeOn_pos h D hH
  have hB := isCartierCombination_toRDivisor_of_eq_smul hL hHL
  have hnef := isRelativelyNef_neg_toRDivisor h D hH
  have hBeff : (QDivisor.toRDivisor H).IsEffective := fun P => by
    rw [QDivisor.coeff_toRDivisor]
    exact_mod_cast coeff_nonneg_of_isGraphDivisor h D hH P
  set S := (QDivisor.toRDivisor H).supp with hS
  rcases MMP.Flips.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg ℂ sZ
    (D.u ≫ sXm) hZ hGv (D.u ≫ fm) hf hbg hB hBeff hnef ((D.u ≫ fm) y) with hsub | hdis
  · obtain ⟨Γ, hΓ, hyΓ⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mp (hsub rfl)
    refine ⟨Γ, hyΓ, fun h0 => hΓ ?_⟩
    rw [QDivisor.coeff_toRDivisor]
    change ((H Γ : ℚ) : ℝ) = 0
    rw [h0]
    simp
  · exfalso
    set g := D.u ≫ fm with hg
    have hSc : IsClosed (g '' (S : Set D.G)) := g.isClosedMap _ S.isClosed
    have hyV : y ∈ g ⁻¹' (g '' (S : Set D.G))ᶜ := by
      rintro ⟨s, hs, hgs⟩
      exact Set.disjoint_left.mp hdis (show s ∈ g.base ⁻¹' {g y} from hgs) hs
    have hT : IsLocallyClosed (closure {y} ∩ g ⁻¹' (g '' (S : Set D.G))ᶜ) :=
      isClosed_closure.isLocallyClosed.inter
        (hSc.isOpen_compl.preimage g.continuous).isLocallyClosed
    have hne : (closure {y} ∩ g ⁻¹' (g '' (S : Set D.G))ᶜ).Nonempty :=
      ⟨y, subset_closure rfl, hyV⟩
    obtain ⟨y₀, ⟨hy₀y, hy₀V⟩, hy₀c⟩ := nonempty_inter_closedPoints hne hT
    have hz₀ : g y₀ ∈ badLocusBase fm fp :=
      ((specializes_iff_mem_closure.mpr hy₀y).map g.continuous).mem_closed
        (badLocusBase fm fp).isClosed hy
    obtain ⟨C, hCf, hCy₀⟩ := exists_properCurve_specializes ℂ sZ (D.u ≫ sXm) hZ hGv g hf hbg
      y₀ (mem_closedPoints_iff.mp hy₀c) (notMem_biregularLocus_of_mem_badLocusBase h D hz₀)
    have hgC : g C.point = g y₀ := (hCf y₀ (specializes_iff_mem_closure.mp hCy₀)).symm
    have hCS : C.point ∉ S := fun hCS => hy₀V ⟨C.point, hCS, hgC⟩
    have hx := isRIntersectionNumber_sum_degreeOn ℂ (D.u ≫ sXm) C ![-1 / (m : ℝ)] ![L]
      (fun j => by rw [Fin.fin_one_eq_zero j]; exact hL)
    rw [show ∑ j, ![-1 / (m : ℝ)] j • Divisor.toRDivisor (![L] j) = QDivisor.toRDivisor H by
      rw [hHL, Fin.sum_univ_one]; rfl] at hx
    have hnn := MMP.Flips.IsRIntersectionNumber.nonneg_of_isEffective ℂ (D.u ≫ sXm) hGv _ hB
      hBeff C hCS _ _ hx
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at hnn
    have hp : (0 : ℝ) < (L.degreeOn ℂ (D.u ≫ sXm) C.ι C.dim_le hL : ℝ) := by
      exact_mod_cast hpos C hCf
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have : -1 / (m : ℝ) * (L.degreeOn ℂ (D.u ≫ sXm) C.ι C.dim_le hL : ℝ) < 0 :=
      mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) hm') hp
    linarith

/-! ### Orders of pull-backs at the centre -/

/-- A rational function with order zero along every prime divisor through `f(η_E)` has
order zero along `E` after pull-back. -/
private theorem ord_functionFieldMap_eq_zero {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (E : MMP.Mori.PrimeDivisor Y) {φ : X.functionField} (hφ : φ ≠ 0)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, f E.genericPoint ∈ Γ.support →
      X.ord φ Γ.genericPoint = 0) :
    Y.ord (functionFieldMap f φ) E.genericPoint = 0 := by
  have := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := f) E (fun _ : Unit => φ)
    (fun _ => hφ) (fun _ => 1) fun Γ hΓ => by simp [h Γ hΓ]
  simpa using this

/-- A rational function with nonnegative order along every prime divisor through `f(η_E)`, and
positive order along one of them, has positive order along `E` after pull-back. -/
private theorem ord_functionFieldMap_pos {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (E : MMP.Mori.PrimeDivisor Y) {φ : X.functionField} (hφ : φ ≠ 0)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, f E.genericPoint ∈ Γ.support →
      0 ≤ X.ord φ Γ.genericPoint)
    (h' : ∃ Γ : MMP.Mori.PrimeDivisor X, f E.genericPoint ∈ Γ.support ∧
      0 < X.ord φ Γ.genericPoint) :
    0 < Y.ord (functionFieldMap f φ) E.genericPoint := by
  obtain ⟨Γ₀, hΓ₀, hpos⟩ := h'
  obtain ⟨r, hr⟩ :=
    MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hφ h
  have hrm : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (f E.genericPoint)) := by
    by_contra hru
    have hu : IsUnit r := by
      by_contra hu'
      exact hru ((IsLocalRing.mem_maximalIdeal _).mpr hu')
    have hsp : Γ₀.genericPoint ⤳ f E.genericPoint := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hΓ₀
    have hr' : algebraMap Γ₀.localRing X.functionField
        ((X.presheaf.stalkSpecializes hsp).hom r) = φ := by
      rw [MMP.Mori.algebraMap_stalkSpecializes, hr]
    have hlt := (Γ₀.divisorialValuation_algebraMap_lt_one_iff
      ((X.presheaf.stalkSpecializes hsp).hom r)).mp (by
        rw [hr', Γ₀.divisorialValuation_eq_exp_neg_ord hφ, ← WithZero.exp_zero,
          WithZero.exp_lt_exp]
        omega)
    exact (IsLocalRing.mem_maximalIdeal _).mp hlt (hu.map _)
  have hs : (f.stalkMap E.genericPoint).hom r ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk E.genericPoint) := by
    rw [IsLocalRing.mem_maximalIdeal] at hrm ⊢
    exact (map_mem_nonunits_iff _ _).mpr hrm
  have hfφ : functionFieldMap f φ =
      algebraMap E.localRing Y.functionField ((f.stalkMap E.genericPoint).hom r) := by
    rw [← hr, MMP.Mori.functionFieldMap_algebraMap_stalk]
  have hlt := (E.divisorialValuation_algebraMap_lt_one_iff _).mpr hs
  rw [← hfφ, E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hφ), ← WithZero.exp_zero,
    WithZero.exp_lt_exp] at hlt
  omega

/-- **The graph divisor detects the bad locus at the centre.** Let `w : W ⟶ G` be a model,
`E` a prime divisor of `W`, and `φ` a rational function on `G` with `v_Γ(φ) = M coeff_Γ(H)`,
`M > 0`, along every prime divisor `Γ` through `y = w(η_E)`. Then `v_E(w^*φ) > 0` exactly when
`g(y) ∈ Σ`: over `Z ∖ Σ` the divisor `H` vanishes near `y`, while over `Σ` it is effective and
nonzero along some prime divisor through `y`. -/
private theorem ord_functionFieldMap_pos_iff (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (w : W ⟶ D.G)
    [IsDominant w] (E : MMP.Mori.PrimeDivisor W) {M : ℕ} (hM : 0 < M) {φ : D.G.functionField}
    (hφ : φ ≠ 0) (hφΓ : ∀ Γ : MMP.Mori.PrimeDivisor D.G, w E.genericPoint ∈ Γ.support →
      (D.G.ord φ Γ.genericPoint : ℚ) = M * H Γ) :
    0 < W.ord (functionFieldMap w φ) E.genericPoint ↔
      (D.u ≫ fm) (w E.genericPoint) ∈ badLocusBase fm fp := by
  constructor
  · intro hpos
    by_contra hnm
    have hU : (D.u ≫ fm) (w E.genericPoint) ∈ commonBiregularLocus fm fp := by
      by_contra hU
      exact hnm (by rw [← SetLike.mem_coe, coe_badLocusBase]; exact hU)
    have h0 := ord_functionFieldMap_eq_zero w E hφ fun Γ hΓ => by
      have hsp : Γ.genericPoint ⤳ w E.genericPoint := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hΓ
      have := hφΓ Γ hΓ
      rw [coeff_eq_zero_of_mem_commonBiregularLocus h D hH Γ
        ((hsp.map (D.u ≫ fm).continuous).mem_open (commonBiregularLocus fm fp).2 hU),
        mul_zero] at this
      exact_mod_cast this
    exact hpos.ne' h0
  · intro hmem
    obtain ⟨Γ₀, hΓ₀, hΓ₀H⟩ := exists_mem_support_coeff_ne_zero h D hH hmem
    refine ord_functionFieldMap_pos w E hφ (fun Γ hΓ => ?_) ⟨Γ₀, hΓ₀, ?_⟩
    · have : (0 : ℚ) ≤ D.G.ord φ Γ.genericPoint := by
        rw [hφΓ Γ hΓ]
        have := coeff_nonneg_of_isGraphDivisor h D hH Γ
        positivity
      exact_mod_cast this
    · have : (0 : ℚ) < D.G.ord φ Γ₀.genericPoint := by
        rw [hφΓ Γ₀ hΓ₀]
        exact mul_pos (by exact_mod_cast hM)
          ((coeff_nonneg_of_isGraphDivisor h D hH Γ₀).lt_of_ne hΓ₀H.symm)
      exact_mod_cast this

/-! ### Centres -/

/-- The centre of a normalized divisorial valuation `ξ = ord_E`, for a divisor `(W, g, E)`
over `X`, is the closure of `g(η_E)`. -/
private theorem coe_eq_closure_of_isCentre {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {C : IrreducibleCloseds X}
    (hC : MMP.Intersection.IsCentre ℂ sX ξ C) (D : DivisorOver ℂ sX) (hD : D.valuation = ξ) :
    (C : Set X) = closure {D.f D.E.genericPoint} := by
  obtain ⟨D₀, -, hv₀, rfl⟩ := hC
  rw [D₀.center_eq_closure_genericPoint,
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX (hv₀.symm.trans hD.symm)]

/-- The closure of a point lies in the preimage `f⁻¹(S)` of the closed set `S` exactly when the
image of the point lies in `S`. -/
private theorem closure_subset_preimage_iff {X Y : Scheme.{0}} (f : X ⟶ Y) (S : Closeds Y)
    (x : X) : closure {x} ⊆ f ⁻¹' (S : Set Y) ↔ f x ∈ S :=
  ⟨fun hs => hs (subset_closure rfl),
    fun hx => closure_minimal (Set.singleton_subset_iff.mpr hx) (S.isClosed.preimage f.continuous)⟩

/-- `ξ⁺`, the valuation of `k(X⁺)` corresponding to `ξ = ord_E`, is `ord_E` for `(W, g', E)`. -/
private theorem valuation_eq_of_comap_eq {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsIntegral Z]
    [IsDominant fm] [IsDominant fp] (hfp : IsBirationalMorphism fp) {W : Scheme.{0}}
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {g : W ⟶ Xm} {g' : W ⟶ Xp}
    (hW : IsNormalVariety ℂ (g ≫ sXm)) (hW' : IsNormalVariety ℂ (g' ≫ sXp))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ fm = g' ≫ fp)
    (E : MMP.Mori.PrimeDivisor W) {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : ξp.comap (functionFieldMap fp) =
      (⟨W, g, hW, hg, E⟩ : DivisorOver ℂ sXm).valuation.comap (functionFieldMap fm)) :
    (⟨W, g', hW', hg', E⟩ : DivisorOver ℂ sXp).valuation = ξp := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ sXm)
  haveI : IsDominant g := hg.isDominant
  haveI : IsDominant g' := hg'.isDominant
  have hinj : Function.Injective
      (Valuation.comap (Γ₀ := WithZero (Multiplicative ℤ)) (functionFieldMap fp)) := by
    intro v w hvw
    ext x
    obtain ⟨y, rfl⟩ := hfp.functionFieldMap_bijective.2 x
    exact congrArg (fun v => v y) hvw
  apply hinj
  rw [hξ]
  ext x
  simp only [Valuation.comap_apply]
  change E.divisorialValuation (functionFieldMap g' (functionFieldMap fp x)) =
    E.divisorialValuation (functionFieldMap g (functionFieldMap fm x))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  simp only [hcomm]

/-- **Strictness of the comparison.** In a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` of fourfolds,
for a normalized divisorial valuation `ξ` of `k(X⁻)` and the corresponding valuation `ξ⁺` of
`k(X⁺)`, the following are equivalent: `a(ξ; X⁻, B⁻) < a(ξ⁺; X⁺, B⁺)`; `c_{X⁻}(ξ) ⊆ W⁻`;
`c_{X⁺}(ξ⁺) ⊆ W⁺`. -/
private theorem tfae_lt_and_centre_subset_badLocus :
    ∀ {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    {ξ : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isBirationalMorphism_plus.isDominant
      ξp.comap (functionFieldMap fp) = ξ.comap (functionFieldMap fm))
    {am ap : ℝ} (ham : IsValuationLogDiscrepancy sXm B ξ am)
    (hap : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) ξp ap)
    {Cm : IrreducibleCloseds Xm} {Cp : IrreducibleCloseds Xp}
    (hCm : MMP.Intersection.IsCentre ℂ sXm ξ Cm) (hCp : MMP.Intersection.IsCentre ℂ sXp ξp Cp),
    List.TFAE [am < ap, (Cm : Set Xm) ⊆ badLocusMinus fm fp,
      (Cp : Set Xp) ⊆ badLocusPlus fm fp] := by
  intro Xm Xp Z _ _ _ _ _ _ _ _ sXm sZ sXp K B fm fp h ξ ξp hξ am ap ham hap Cm Cp hCm hCp
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isBirationalMorphism_plus.isDominant
  obtain ⟨D⟩ := exists_graphData h
  obtain ⟨H, hH⟩ := exists_isGraphDivisor h D
  have hG := D.isNormalizedGraph
  have hCm' := hCm
  obtain ⟨D₀, -, rfl, -⟩ := hCm'
  obtain ⟨W, w, hW, hb, hwp, hw, E, hE⟩ := exists_model h D D₀
  haveI := hwp
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian ((w ≫ D.u) ≫ sXm)
  haveI : IsDominant w := hw.isDominant
  have hcomm : (w ≫ D.u) ≫ fm = (w ≫ D.v) ≫ fp := by
    rw [Category.assoc, Category.assoc, hG.comp_eq]
  have hW' : IsNormalVariety ℂ ((w ≫ D.v) ≫ sXp) := by
    have e : (w ≫ D.v) ≫ sXp = (w ≫ D.u) ≫ sXm := calc
      (w ≫ D.v) ≫ sXp = (w ≫ D.v) ≫ fp ≫ sZ := by rw [h.comp_eq_plus]
      _ = (w ≫ D.u) ≫ fm ≫ sZ := by rw [← Category.assoc, ← hcomm, Category.assoc]
      _ = (w ≫ D.u) ≫ sXm := by rw [h.comp_eq_minus]
    rw [e]; exact hW
  have hb' : IsBirationalMorphism (w ≫ D.v) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational D.v w
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hG.isBirationalMorphism_plus)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hw)
  set Dm : DivisorOver ℂ sXm := ⟨W, w ≫ D.u, hW, hb, E⟩ with hDm
  set Dp : DivisorOver ℂ sXp := ⟨W, w ≫ D.v, hW', hb', E⟩ with hDp
  have hDpv : Dp.valuation = ξp :=
    valuation_eq_of_comap_eq h.isBirationalMorphism_plus hW hW' hb hb' hcomm E
      (by rw [hE]; exact hξ)
  -- the centres
  set z := (D.u ≫ fm) (w E.genericPoint) with hz
  have hCmc : (Cm : Set Xm) = closure {(w ≫ D.u) E.genericPoint} :=
    coe_eq_closure_of_isCentre h.isNormalVariety_minus hCm Dm hE
  have hCpc : (Cp : Set Xp) = closure {(w ≫ D.v) E.genericPoint} :=
    coe_eq_closure_of_isCentre h.isNormalVariety_plus hCp Dp hDpv
  have h2 : (Cm : Set Xm) ⊆ badLocusMinus fm fp ↔ z ∈ badLocusBase fm fp := by
    rw [hCmc, coe_badLocusMinus, closure_subset_preimage_iff fm]
    rfl
  have h3 : (Cp : Set Xp) ⊆ badLocusPlus fm fp ↔ z ∈ badLocusBase fm fp := by
    rw [hCpc, coe_badLocusPlus, closure_subset_preimage_iff fp, ← Scheme.Hom.comp_apply,
      ← hcomm, hz]
    rfl
  -- the discrepancies
  obtain ⟨M, φ, hM, hφ, hφΓ, hkey⟩ :=
    exists_ord_eq_mul_sub h D hH hW hW' hb hb' E hE hDpv ham hap
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : am < ap ↔ z ∈ badLocusBase fm fp := by
    rw [← sub_pos, ← mul_pos_iff_of_pos_left hM', hkey, Int.cast_pos]
    exact ord_functionFieldMap_pos_iff h D hH w E hM hφ hφΓ
  tfae_have 1 ↔ 2 := h1.trans h2.symm
  tfae_have 2 ↔ 3 := h2.trans h3.symm
  tfae_finish

/-! ### The unit drop -/

section UnitDrop

open MMP.Mori.DivisorWithCoeffs in
/-- A transform of divisors along a correspondence of prime divisors keeps coefficients
`N`-integral: if `N d_P ∈ ℤ` for every coefficient `d_P` of `D`, the same holds for
`mapPrimeDivisors φ D`. -/
private theorem exists_intCast_eq_coeff_mapPrimeDivisors {X Y : Scheme.{0}} (N : ℕ)
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) {D : QDivisor X}
    (hD : ∀ P, ∃ z : ℤ, (N : ℚ) * D.coeff P = z) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ z : ℤ, (N : ℚ) * (mapPrimeDivisors φ D).coeff Q = z := by
  classical
  let S : AddSubmonoid (QDivisor Y) :=
    { carrier := {D' | ∀ Q, ∃ z : ℤ, (N : ℚ) * D'.coeff Q = z}
      zero_mem' := fun Q => ⟨0, by simp [MMP.Mori.DivisorWithCoeffs.coeff]⟩
      add_mem' := fun {D₁ D₂} h₁ h₂ Q => by
        obtain ⟨z₁, hz₁⟩ := h₁ Q
        obtain ⟨z₂, hz₂⟩ := h₂ Q
        refine ⟨z₁ + z₂, ?_⟩
        simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.add_apply] at hz₁ hz₂ ⊢
        push_cast
        rw [mul_add, hz₁, hz₂] }
  have hmem : mapPrimeDivisors φ D ∈ S := by
    rw [← Finsupp.sum_single D, map_finsuppSum]
    refine AddSubmonoidClass.finsuppSum_mem S _ _ fun P _ => ?_
    rw [mapPrimeDivisors_single]
    rcases φ P with _ | Q'
    · exact S.zero_mem
    · intro Q
      obtain ⟨z, hz⟩ := hD P
      simp only [Option.elim_some, MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.single_apply]
      split_ifs
      · exact ⟨z, hz⟩
      · exact ⟨0, by simp⟩
  exact hmem Q

/-- If `N d_P ∈ ℤ` for every coefficient `d_P` of a `ℚ`-divisor `D = ∑ d_P P`, then
`N mult_x D = N ∑ d_P mult_x P ∈ ℤ`. -/
private theorem exists_intCast_eq_multiplicityAt {X : Scheme.{0}} (N : ℕ) {D : QDivisor X}
    (hD : ∀ P, ∃ z : ℤ, (N : ℚ) * D.coeff P = z) (x : X) :
    ∃ z : ℤ, (N : ℚ) * D.multiplicityAt x = z := by
  choose z hz using hD
  refine ⟨∑ P ∈ D.support, ((P.multiplicityAt x).toNat : ℤ) * z P, ?_⟩
  rw [MMP.Mori.DivisorWithCoeffs.multiplicityAt, Finsupp.sum, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [nsmul_eq_mul, ← hz P, MMP.Mori.DivisorWithCoeffs.coeff]
  ring

/-- The multiplicity of an effective `ℚ`-divisor at a point is nonnegative. -/
private theorem multiplicityAt_nonneg {X : Scheme.{0}} {D : QDivisor X} (hD : ∀ P, 0 ≤ D.coeff P)
    (x : X) : 0 ≤ D.multiplicityAt x :=
  Finset.sum_nonneg fun P _ => nsmul_nonneg (hD P) _

open MMP.Fourfold.StabilizedSmallKltTail in
/-- Every coefficient of every boundary `B_j` of a stabilized small klt tail is `N`-integral for
an admissible scale `N`: `B_{j+1}` is a birational transform of `B_j`. -/
private theorem exists_intCast_eq_coeff_B {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {N : ℕ} (hN : C.IsAdmissibleScale N) :
    ∀ (j : ℕ) (P : MMP.Mori.PrimeDivisor (T.X j)), ∃ z : ℤ, (N : ℚ) * (T.B j).coeff P = z
  | 0, P => hN.exists_intCast_eq_coeff P
  | j + 1, P => by
    rw [T.B_eq j]
    unfold flipTransform inverseTransformDivisor MMP.Mori.RationalMap.transformDivisor
    exact exists_intCast_eq_coeff_mapPrimeDivisors N _
      (exists_intCast_eq_coeff_mapPrimeDivisors N _ (exists_intCast_eq_coeff_B hN j)) P

/-- **The weight drops by a unit past an `N`-integral value.** If `0 ≤ u'` with `N u' ∈ ℤ`
and `u' < u`, then `w(u') = N u'` and `w(u') + 1 ≤ w(u)`. -/
private theorem difficultyWeight_add_one_le_of_lt {N : ℕ} (hN : 0 < N) {u u' : ℝ} (hu' : 0 ≤ u')
    (hz : ∃ z : ℤ, (N : ℝ) * u' = z) (hlt : u' < u) :
    difficultyWeight N u' + 1 ≤ difficultyWeight N u := by
  obtain ⟨z, hz⟩ := hz
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  lift z to ℕ using by exact_mod_cast hz ▸ mul_nonneg hN'.le hu'
  rw [difficultyWeight, max_eq_left hu', hz, Int.cast_natCast, Nat.ceil_natCast,
    Nat.add_one_le_iff, difficultyWeight, Nat.lt_ceil, ← Int.cast_natCast, ← hz]
  exact (mul_lt_mul_of_pos_left hlt hN').trans_le
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hN'.le)

end UnitDrop

end MMP.Fourfold.UnitDrop

namespace MMP.Fourfold.StabilizedSmallKltTail

open MMP.Mori UnitDrop in
/-- **Unit drop of the weight at a positive-side bad surface.** Let `T` be a stabilized small
klt tail with a terminal chain `C` and admissible scale `N`. Let `V` be an irreducible surface
contained in the positive-side bad locus `W_i⁺ ⊆ X_{i+1}` of the `i`-th step, and `v` the
generic blowup valuation of `V` on `X_{i+1}`, read on `X_i` as `η` (same restriction to
`k(Z_i)`). If `a = a(η; X_i, B_i)` and `a' = a(v; X_{i+1}, B_{i+1})`, then
`w(2 - a') + 1 ≤ w(2 - a)` for the weight `w = MMP.Fourfold.difficultyWeight N`. -/
@[mmp "lem_oai4_c3_unit_drop"]
public theorem difficultyWeight_add_one_le_of_subset_badLocusPlusAt (T : StabilizedSmallKltTail)
    (C : TerminalChain T) {N : ℕ} (hN : C.IsAdmissibleScale N) (i : ℕ)
    (V : IrreducibleCloseds (T.X (i + 1)))
    (hV : (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i)
    {v : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hv : IsSurfaceGenericBlowupValuation (T.sX (i + 1)) V v)
    {η : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    (hη : T.IsTransportedValuation i η v)
    {a a' : ℝ} (ha : T.IsLogDiscrepancyAt i η a) (ha' : T.IsLogDiscrepancyAt (i + 1) v a') :
    difficultyWeight N (2 - a') + 1 ≤ difficultyWeight N (2 - a) := by
  -- `a' = 2 - mult_{η_V} B_{i+1}`
  have hpair : MMP.Mori.IsPair (T.sX (i + 1)) (T.B (i + 1)) :=
    (T.isStabilizedSmallKltTail.isKlt (i + 1)).1.isPair
  obtain ⟨n, E, hEp, hEv, hE⟩ := ha'
  have ha'eq := (hv.isLogDiscrepancy_two_sub_multiplicityAt hpair E hEp hEv).2 n a' hE
  -- `a < a'`, since the centre `V` of `v` lies in `W_i⁺`
  obtain ⟨n₀, D₀, hD₀p, hD₀v, hD₀⟩ := ha
  have hCm : MMP.Intersection.IsCentre ℂ (T.sX i) η D₀.center := ⟨D₀, hD₀p, hD₀v.symm, rfl⟩
  have hap : IsValuationLogDiscrepancy (T.sX (i + 1))
      (flipTransform (T.f i) (T.fp i) (T.B i)) v a' := by
    rw [← T.B_eq i]
    exact ⟨n, E, hEp, hEv, hE⟩
  have hlt : a < a' :=
    ((tfae_lt_and_centre_subset_badLocus (T.isFourfoldStepDiagram i) hη
      ⟨n₀, D₀, hD₀p, hD₀v, hD₀⟩ hap hCm hv.2.2.2.2.1).out 1 3).2 hV
  -- `2 - a' = mult_{η_V} B_{i+1}` is nonnegative and `N`-integral
  obtain ⟨z, hz⟩ := exists_intCast_eq_multiplicityAt N (exists_intCast_eq_coeff_B hN (i + 1))
    V.isIrreducible.genericPoint
  subst ha'eq
  rw [sub_sub_cancel]
  refine difficultyWeight_add_one_le_of_lt hN.pos ?_ ⟨z, by exact_mod_cast hz⟩ (by linarith)
  exact_mod_cast multiplicityAt_nonneg (T.isFourfoldStepDiagram (i + 1)).nonneg _

end MMP.Fourfold.StabilizedSmallKltTail

end
