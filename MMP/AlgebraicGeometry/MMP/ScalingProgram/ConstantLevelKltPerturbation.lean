module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.AmpleFloorLowering
import MMP.AlgebraicGeometry.MMP.Flip.NumericalClassTransport
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Positivity.Kleiman.RhoOneCurveTest
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTransform
import MMP.AlgebraicGeometry.MMP.Flip.RealCanonicalRationalWitness
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Surface.ContractionChainBound
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.MMP.Flip.DivisorNormalizationLift
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction

/-!
# A constant scaling level can be made klt

Let `π : X ⟶ Z` be a morphism of complex projective varieties, `X` normal and `ℚ`-factorial, and
let `B, C ≥ 0` be real divisors with `(X, B + C)` dlt, such that `B` contains an effective ample
`ℚ`-divisor `A` none of whose components lies in `⌊B + C⌋`. Consider a sequence of
`(K_X + B)`-flips over `Z` with scaling of `C` in which every threshold is one: at each stage
`K_{X_i} + B_i + C_i` is nef over `Z`, `K_{X_i} + B_i + t C_i` is not nef over `Z` for `t < 1`,
and the flipping contraction `X_i ⟶ Z_i` is `(K_{X_i} + B_i + C_i)`-trivial. Then there are
effective real divisors `B̃, C̃` with `(X, B̃ + C̃)` klt and `B̃` containing an effective ample
`ℚ`-divisor, such that the same diagrams form a sequence of `(K_X + B̃)`-flips with scaling of
`C̃`, again with every threshold one, along which the upper pairs `(X_i, B̃_i + C̃_i)` stay klt.
One may take `B̃ = B + εC - A - δ⌊B + C⌋ + A'` and `C̃ = (1 - ε) C` for a general
`A' ∼_ℚ A + δ⌊B + C⌋`.

## Main results

* `MMP.Fourfold.IsRealDltPair.exists_isRealKltPair_isRealFlipStep_scaling_threshold_one`.

## Implementation notes

The models are indexed as in `MMP.Fourfold.RealFlipSequence`: `X₀ = X`, `X_{i+1} = Y i`, with
`n ∈ ℕ ∪ {∞}` steps; the `i`-th step is the diagram `X_i ⟶ Z_i ⟵ X_{i+1}` given by `f i`,
`fp i`, lying over `Z` through `g i : Z_i ⟶ Z`, and is an `MMP.Fourfold.IsRealFlipStep` for the
lower adjoint `K_{X_i} + B_i`. The scaling divisors `C_{i+1}` are the strict transforms
`MMP.Mori.flipTransform` of `C_i`. The threshold of the `i`-th step is the least `t ≥ 0` with
`K_{X_i} + B_i + t C_i` nef over `Z`; that it equals one is `IsLeast … 1`. No dimension is fixed.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

universe u

/- ### The flip as a birational map -/

section Points

variable {X Y : Scheme.{u}}

/-- The restriction `f ∣_ V` followed by `V ⊆ Y` is `f` on `f⁻¹(V)`. -/
private theorem apply_ι_morphismRestrict (f : X ⟶ Y) (V : Y.Opens) (p : (f ⁻¹ᵁ V).toScheme) :
    V.ι ((f ∣_ V) p) = f ((f ⁻¹ᵁ V).ι p) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, `f` is injective. -/
private theorem eq_of_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {x₁ x₂ : X}
    (h₁ : f x₁ ∈ V) (h₂ : f x₂ ∈ V) (h : f x₁ = f x₂) : x₁ = x₂ := by
  let p₁ : (f ⁻¹ᵁ V).toScheme := ⟨x₁, h₁⟩
  let p₂ : (f ⁻¹ᵁ V).toScheme := ⟨x₂, h₂⟩
  have : (f ∣_ V) p₁ = (f ∣_ V) p₂ :=
    V.ι.isOpenEmbedding.injective ((apply_ι_morphismRestrict f V p₁).trans
      (h.trans (apply_ι_morphismRestrict f V p₂).symm))
  exact congrArg Subtype.val ((f ∣_ V).isOpenEmbedding.injective this)

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, every point of `V` is in the image
of `f`. -/
private theorem exists_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {y : Y}
    (hy : y ∈ V) : ∃ x, f x = y := by
  let q : V.toScheme := ⟨y, hy⟩
  refine ⟨(f ⁻¹ᵁ V).ι (inv (f ∣_ V) q), ?_⟩
  rw [← apply_ι_morphismRestrict, ← Scheme.Hom.comp_apply (inv (f ∣_ V)) (f ∣_ V), IsIso.inv_hom_id]
  rfl

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, `f` preserves coheights. -/
private theorem coheight_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {x : X}
    (hx : f x ∈ V) : Order.coheight (f x) = Order.coheight x :=
  MMP.Positivity.coheight_map_of_mem_biregularLocus f
    ((isBiregular_iff_le_biregularLocus.mp ‹IsIso (f ∣_ V)›) hx)

/-- Prime divisors correspond over `V`: if `f` and `f⁺` are isomorphisms over `V`, every prime
divisor `P⁺` of `X⁺` lying over `V` has a prime divisor `P` of `X` over the same point of `Y`. -/
private theorem exists_primeDivisor_genericPoint_eq {X' : Scheme.{u}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (P' : MMP.Mori.PrimeDivisor X')
    (hP' : fp P'.genericPoint ∈ V) :
    ∃ P : MMP.Mori.PrimeDivisor X, f P.genericPoint = fp P'.genericPoint := by
  obtain ⟨x, hx⟩ := exists_apply_eq f V hP'
  have hxV : f x ∈ V := hx ▸ hP'
  have hco : Order.coheight x = 1 := by
    rw [← coheight_apply_eq f V hxV, hx, coheight_apply_eq fp V hP',
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco,
    (congrArg f (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco)).trans hx⟩

end Points

section Small

variable {X Z : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- **A small contraction is an isomorphism off codimension two.** For a small birational
contraction `f : X ⟶ Z` there are closed subsets `V ⊆ X` and `W ⊆ Z` of points of coheight at
least two, with `X ∖ V ⊆ f⁻¹(Z ∖ W)`, such that `f` is an isomorphism over `Z ∖ W`: the section of
the separated `f⁻¹(Z ∖ W) ⟶ Z ∖ W` given by `X ∖ V` is a closed immersion, so `X ∖ V` is
open and closed in the irreducible `f⁻¹(Z ∖ W)`. -/
private theorem exists_closeds_isIso_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f) :
    ∃ (V : Closeds X) (W : Closeds Z), (∀ x ∈ (V : Set X), 2 ≤ Order.coheight x) ∧
      (∀ z ∈ (W : Set Z), 2 ≤ Order.coheight z) ∧ V.compl ≤ f ⁻¹ᵁ W.compl ∧
      IsIso (f ∣_ W.compl) := by
  obtain ⟨V, W, hV, hW, h, hiso⟩ := hf.exists_isIso
  have hV' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV
  refine ⟨V, W, hV', MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW, h, ?_⟩
  haveI : IsProper f := hf.isProper
  set U := f ⁻¹ᵁ W.compl
  set g := f ∣_ W.compl
  set j := X.homOfLE h
  have hjg : j ≫ g = f.resLE W.compl V.compl h := rfl
  set s := inv (f.resLE W.compl V.compl h) ≫ j
  have hs : s ≫ g = 𝟙 _ := by simp [s, hjg]
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s g
  have hj : j = f.resLE W.compl V.compl h ≫ s := by simp [s]
  haveI : IsClosedImmersion j := by rw [hj]; infer_instance
  -- `X ∖ V` is nonempty: it contains the generic point
  have hgen : genericPoint X ∈ (V.compl : Set X) := by
    intro hgV
    have := hV' (genericPoint X) hgV
    rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at this
    exact absurd this (by decide)
  haveI : Nonempty U := ⟨⟨_, h hgen⟩⟩
  have hclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range j).Nonempty := ⟨_, ⟨⟨_, hgen⟩, rfl⟩⟩
  have hrange : Set.range j = Set.univ := (isClopen_iff.mp hclopen).resolve_left hne.ne_empty
  haveI : Surjective j := ⟨Set.range_eq_univ.mp hrange⟩
  haveI : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  have hg : g = inv j ≫ f.resLE W.compl V.compl h := by rw [← hjg]; simp
  change IsIso g
  rw [hg]
  infer_instance

variable [IsLocallyNoetherian X] [IsNormal X]

/-- Points of coheight at most one of the base lie in the biregular locus of a small
contraction. -/
private theorem mem_biregularLocus_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    {z : Z} (hz : Order.coheight z ≤ 1) : z ∈ biregularLocus f := by
  obtain ⟨V, W, -, hW, -, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hzW : z ∈ (W.compl : Set Z) := fun h => absurd ((hW z h).trans hz) (by decide)
  exact le_biregularLocus hiso hzW

/-- A small contraction maps the generic point of a prime divisor to a point of coheight one,
in its biregular locus. -/
private theorem coheight_map_genericPoint_of_isSmall {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight (f P.genericPoint) = 1 ∧ f P.genericPoint ∈ biregularLocus f := by
  obtain ⟨V, W, hV, -, h, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hPV : P.genericPoint ∈ (V.compl : Set X) := fun hP =>
    absurd (hV _ hP) (by rw [P.coheight_genericPoint]; decide)
  have hb : f P.genericPoint ∈ biregularLocus f := le_biregularLocus hiso (h hPV)
  exact ⟨by rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb,
    P.coheight_genericPoint], hb⟩

/-- Two prime divisors with the same image under a small contraction coincide. -/
private theorem primeDivisor_eq_of_map_eq_of_isSmall {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) {P Q : MMP.Mori.PrimeDivisor X}
    (hPQ : f P.genericPoint = f Q.genericPoint) : P = Q := by
  haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_iff_le_biregularLocus.mpr le_rfl
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective <| eq_of_apply_eq f _
    (coheight_map_genericPoint_of_isSmall hf P).2 (coheight_map_genericPoint_of_isSmall hf Q).2 hPQ

end Small

section SmallPair

variable {X X' Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- Every prime divisor of `X` corresponds, through `Z`, to a prime divisor of `X⁺`. -/
private theorem exists_primeDivisor_map_eq_of_isSmall {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor X', fp P'.genericPoint = f P.genericPoint := by
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  have hb := mem_biregularLocus_of_isSmall hfp hz.le
  obtain ⟨x', hx'⟩ :=
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj (f P.genericPoint)
  have hc : Order.coheight x' = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hx' ▸ hb), hx', hz]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (congrArg fp (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hc)).trans hx'⟩

/-- The strict transform `(f⁺)⁻¹_* f_* D` across two small contractions has, at the prime divisor
`P⁺` corresponding to `P`, the coefficient of `D` at `P`. -/
private theorem flipTransform_apply_of_isSmall [IsIntegral Z] (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'}
    (hPP' : fp P'.genericPoint = f P.genericPoint) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsProper f := hf.isProper
  haveI := hfb.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hz
  have hQ : f P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hz).symm
  have := Q.isDiscreteValuationRing_localRing
  exact flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj hQ (hPP'.trans hQ)
    (mem_biregularLocus_of_isSmall hfp (hQ ▸ hz).le) D

/-- The strict transform commutes with real multiples of integral divisors. -/
private theorem flipTransform_smul_toRDivisor [IsIntegral Z] (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f) (c : ℝ)
    (G : Divisor X) :
    flipTransform f fp (c • Divisor.toRDivisor G) =
      c • Divisor.toRDivisor (flipTransform f fp G) := by
  ext P'
  obtain ⟨P, hP⟩ := exists_primeDivisor_map_eq_of_isSmall hfp hf P'
  have h1 := flipTransform_apply_of_isSmall hZ hf hfp hfb hP.symm (c • Divisor.toRDivisor G)
  have h2 := flipTransform_apply_of_isSmall hZ hf hfp hfb hP.symm G
  simp only [DivisorWithCoeffs.coeff_apply] at h1 ⊢
  rw [h1]
  change c * (Divisor.toRDivisor G).coeff P =
    c * (Divisor.toRDivisor (flipTransform f fp G)).coeff P'
  rw [Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
    DivisorWithCoeffs.coeff_apply, h2]

end SmallPair

/- ### The two transforms of divisors -/

section Transforms

/-- The coefficients of `(f⁺)⁻¹_* f_* D`: if `f` and `f⁺` are isomorphisms over `V`, over which
lie the points of codimension one of `X`, the coefficient of `P⁺` is that of the prime divisor `P`
of `X` over the same point of `Y`. -/
private theorem flipTransform_apply {k : Type u} [Field k] {X X' Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {fp : X' ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) [IsProper f]
    (hf : IsBirationalMorphism f) (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} (hPP : f P.genericPoint = fp P'.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hV : f P.genericPoint ∈ V :=
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  have hV' : fp P'.genericPoint ∈ V := hPP ▸ hV
  have hco : Order.coheight (fp P'.genericPoint) = 1 := by
    rw [coheight_apply_eq fp V hV', AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : Q.genericPoint = fp P'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hbir : fp P'.genericPoint ∈ biregularLocus fp :=
    (isBiregular_iff_le_biregularLocus.mp ‹IsIso (fp ∣_ V)›) hV'
  have huniq : ∀ Q₁ : MMP.Mori.PrimeDivisor Y,
      inverseTransformPrimeDivisor fp Q₁ = some P' → Q₁ = Q := by
    intro Q₁ hQ₁
    obtain ⟨h1, -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ₁
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h1.symm.trans hQ.symm)
  have h1 : inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := X)
      f.toRationalMap D) P' = MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D Q :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        hQ.symm hbir) huniq _
  obtain ⟨E, hEQ, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hf Q
  change inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := X)
    f.toRationalMap D) P' = _
  rw [h1, htr]
  have hE : f E.genericPoint = f P.genericPoint := hEQ.trans (hQ.trans hPP.symm)
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq f V (hE ▸ hV) hV hE)]

/-- If `f⁺` is an isomorphism over `U`, two morphisms into `(f⁺)⁻¹(U)` which agree after
composing with `f⁺` are equal. -/
private theorem eq_of_comp_eq {T X' Y : Scheme.{u}} (fp : X' ⟶ Y) (U : Y.Opens)
    [IsIso (fp ∣_ U)] (a b : T ⟶ X') (ha : Set.range a ⊆ (fp ⁻¹ᵁ U : Set X'))
    (hb : Set.range b ⊆ (fp ⁻¹ᵁ U : Set X')) (h : a ≫ fp = b ≫ fp) : a = b := by
  have ha' : Set.range a ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  have hb' : Set.range b ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  rw [← IsOpenImmersion.lift_fac _ _ ha', ← IsOpenImmersion.lift_fac _ _ hb']
  congr 1
  rw [← cancel_mono (fp ∣_ U), ← cancel_mono U.ι, Category.assoc, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
    IsOpenImmersion.lift_fac, h]

/-- A morphism `a : T ⟶ X'` with `a ≫ f⁺ = c ≫ f` for some `c` landing in `f⁻¹(U)` lands in
`(f⁺)⁻¹(U)`. -/
private theorem range_subset_of_comp_eq {T X X' Y : Scheme.{u}} {f : X ⟶ Y} {fp : X' ⟶ Y}
    {U : Y.Opens} (a : T ⟶ X') (c : T ⟶ X) (hc : ∀ t, c t ∈ f ⁻¹ᵁ U) (h : a ≫ fp = c ≫ f) :
    Set.range a ⊆ (fp ⁻¹ᵁ U : Set X') := by
  rintro _ ⟨t, rfl⟩
  change fp (a t) ∈ U
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact hc t

/-- Let `f⁺` be an isomorphism over `U`. A partial map `p : X ⇀ X'` defined inside `f⁻¹(U)` with
`f⁺ ∘ p = f` represents every rational map `g` with `f⁺ ∘ g = f`. -/
private theorem toRationalMap_eq_of_comp_eq {X X' Y : Scheme.{u}} {f : X ⟶ Y} (fp : X' ⟶ Y)
    (U : Y.Opens) [IsIso (fp ∣_ U)] (p : X.PartialMap X') (hpU : p.domain ≤ f ⁻¹ᵁ U)
    (hp : p.hom ≫ fp = p.domain.ι ≫ f) (g : X.PartialMap X')
    (hg : g.toRationalMap.compHom fp = f.toPartialMap.toRationalMap) :
    p.toRationalMap = g.toRationalMap := by
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at hg
  obtain ⟨W, hWd, hWl, _, hWe⟩ := hg
  replace hWl : W ≤ g.domain := hWl
  have h2 : W ⊓ p.domain ≤ g.domain := inf_le_left.trans hWl
  have hc : ∀ t, (W ⊓ p.domain).ι t ∈ f ⁻¹ᵁ U := fun t ↦ hpU t.2.2
  have ha : (X.homOfLE (inf_le_right : W ⊓ p.domain ≤ _) ≫ p.hom) ≫ fp =
      (W ⊓ p.domain).ι ≫ f := by
    rw [Category.assoc, hp, Scheme.homOfLE_ι_assoc]
  have hb : (X.homOfLE h2 ≫ g.hom) ≫ fp = (W ⊓ p.domain).ι ≫ f := by
    have hWe' : X.homOfLE hWl ≫ g.hom ≫ fp = X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom ≫ f := hWe
    rw [Category.assoc, ← X.homOfLE_homOfLE (inf_le_left : W ⊓ p.domain ≤ W) hWl,
      Category.assoc, hWe', Scheme.topIso_hom, ← Category.assoc, ← Category.assoc,
      Scheme.homOfLE_homOfLE, Scheme.homOfLE_ι]
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  exact ⟨_, hWd.inter_of_isOpen_left p.dense_domain W.isOpen, inf_le_right, h2,
    eq_of_comp_eq fp U _ _ (range_subset_of_comp_eq _ _ hc ha)
      (range_subset_of_comp_eq _ _ hc hb) (ha.trans hb.symm)⟩

/-- A rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`, where `f` and `f⁺` are isomorphisms over a
`V` whose preimage in `X` is dense, is represented on `f⁻¹(V)` by `(f⁺)⁻¹ ∘ f`. -/
private theorem exists_partialMap {X X' Y : Scheme.{u}} {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hd : Dense (f ⁻¹ᵁ V : Set X))
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) :
    ∃ g : X.PartialMap X', g.domain = f ⁻¹ᵁ V ∧ g.toRationalMap = φ ∧
      g.hom ≫ fp = g.domain.ι ≫ f ∧ ∀ t, fp (g.hom t) ∈ V := by
  let g : X.PartialMap X' := ⟨f ⁻¹ᵁ V, hd, (f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι⟩
  have hg : g.hom ≫ fp = g.domain.ι ≫ f := by
    change ((f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι) ≫ fp = (f ⁻¹ᵁ V).ι ≫ f
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι]
  refine ⟨g, rfl, ?_, hg, fun t => ?_⟩
  · obtain ⟨g₀, rfl⟩ := Quotient.exists_rep φ
    exact toRationalMap_eq_of_comp_eq fp V g le_rfl hg g₀ hφ
  · change fp ((fp ⁻¹ᵁ V).ι ((inv (fp ∣_ V)) ((f ∣_ V) t))) ∈ V
    exact ((inv (fp ∣_ V)) ((f ∣_ V) t)).2

/-- If `f` and `f⁺` are isomorphisms over `V`, over which lie the points of codimension at most
one of `X`, a rational map `φ` with `f⁺ ∘ φ = f` is represented by a partial map defined at the
generic point of every prime divisor `Q` of `X`, sending it to the point of `X⁺` over
`f(η_Q) ∈ V`. -/
private theorem exists_partialMap_primeDivisor {X X' Y : Scheme.{u}} [IsIntegral X] {f : X ⟶ Y}
    (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V) {φ : X.RationalMap X'}
    (hφ : φ.compHom fp = f.toRationalMap) :
    ∃ g : X.PartialMap X', g.toRationalMap = φ ∧
      ∃ hmem : ∀ Q : MMP.Mori.PrimeDivisor X, Q.genericPoint ∈ g.domain,
        ∀ Q, fp (g.hom ⟨Q.genericPoint, hmem Q⟩) = f Q.genericPoint ∧
          fp (g.hom ⟨Q.genericPoint, hmem Q⟩) ∈ V := by
  have hgen : Order.coheight (genericPoint X) ≤ 1 :=
    (Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z).trans_le zero_le_one
  obtain ⟨g, hgd, hgφ, hgc, hgV⟩ :=
    exists_partialMap fp V ((f ⁻¹ᵁ V).isOpen.dense ⟨_, hXV _ hgen⟩) hφ
  have hmem : ∀ Q : MMP.Mori.PrimeDivisor X, Q.genericPoint ∈ g.domain := fun Q => by
    rw [hgd]; exact hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le
  exact ⟨g, hgφ, hmem, fun Q => ⟨congrArg (fun h => h.base ⟨Q.genericPoint, hmem Q⟩) hgc, hgV _⟩⟩

/-- If `f`, `f⁺` are isomorphisms over `V`, over which lie the points of codimension at most one
of `X`, a rational map `φ` with `f⁺ ∘ φ = f` carries a prime divisor `P` to the prime divisor
`P⁺` over the same point of `Y`. -/
private theorem transformPrimeDivisor_eq_some_of_map_eq {X X' Y : Scheme.{u}} [IsIntegral X]
    [IsSeparated (X' ↘ ⊤_ Scheme)] {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)]
    [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} (hPP : f P.genericPoint = fp P'.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some P' := by
  obtain ⟨g, hgφ, hmem, hval⟩ := exists_partialMap_primeDivisor fp V hXV hφ
  have hPV : f P.genericPoint ∈ V :=
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  exact MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g hgφ (hmem P)
    (eq_of_apply_eq fp V (hPP ▸ hPV) (hval P).2 (hPP.symm.trans (hval P).1.symm))

/-- The coefficients of `φ_* D` for a rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`, when `f` and
`f⁺` are isomorphisms over `V`, over which lie the points of codimension at most one of `X`: the
coefficient of `P⁺` is that of the prime divisor `P` of `X` over the same point of `Y`. -/
private theorem transformDivisor_apply {X X' Y : Scheme.{u}} [IsIntegral X]
    [IsSeparated (X' ↘ ⊤_ Scheme)] {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)]
    [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} (hPP : f P.genericPoint = fp P'.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ D P' = D P := by
  obtain ⟨g, hgφ, hmem, hval⟩ := exists_partialMap_primeDivisor fp V hXV hφ
  have hPV : ∀ Q : MMP.Mori.PrimeDivisor X, f Q.genericPoint ∈ V := fun Q =>
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_eq_some_of_map_eq fp V hXV hφ hPP) (fun P₁ hP₁ => ?_) D
  have h1 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP₁ g hgφ (hmem P₁)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq f V (hPV P₁) (hPV P) (by rw [← (hval P₁).1, ← h1, ← hPP]))

/-- **The flip transforms divisors as `(f⁺)⁻¹_* f_*`.** If `f` and `f⁺` are isomorphisms over `V`,
over which lie the points of codimension at most one of `X` and of `X⁺`, then
`φ_* D = (f⁺)⁻¹_* f_* D` for every rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`. -/
private theorem transformDivisor_eq_flipTransform {k : Type u} [Field k] {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsSeparated (X' ↘ ⊤_ Scheme)]
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hX : IsNormalVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f) (V : Y.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {φ : X.RationalMap X'}
    (hφ : φ.compHom fp = f.toRationalMap) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ D = flipTransform f fp D := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, hP⟩ := exists_primeDivisor_genericPoint_eq f fp V P'
    (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le)
  rw [transformDivisor_apply fp V hXV hφ hP, flipTransform_apply hY hX hf V hXV hP]

end Transforms

/- ### `ℚ`-factorial varieties and presentations -/

/-- An `ℝ`-divisor is the sum of its prime components with their coefficients. -/
private theorem eq_sum_coeff_smul_single {W : Scheme.{0}} (G : RDivisor W) :
    G = ∑ j : Fin G.support.card, G.coeff (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) •
      Divisor.toRDivisor
        (Finsupp.single (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) 1) := by
  classical
  have hsumFin : ∀ F : MMP.Mori.PrimeDivisor W → ℝ,
      ∑ j, F (G.support.equivFin.symm j) = ∑ Q ∈ G.support, F Q := fun F => by
    rw [← Finset.sum_coe_sort G.support]
    exact Equiv.sum_comp G.support.equivFin.symm (fun Q => F Q)
  refine DivisorWithCoeffs.ext' fun Q => ?_
  simp only [MMP.Flips.coeff_sum_smul_toRDivisor]
  have key : ∀ R : MMP.Mori.PrimeDivisor W,
      ((DivisorWithCoeffs.coeff (R := ℤ) (Finsupp.single R 1) Q : ℤ) : ℝ) =
        if R = Q then 1 else 0 := fun R => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp
  simp only [key, mul_ite, mul_one, mul_zero]
  rw [hsumFin (fun R => if R = Q then G.coeff R else 0), Finset.sum_ite_eq']
  by_cases hQ : Q ∈ G.support
  · simp [hQ]
  · simp only [hQ, if_false]
    rw [DivisorWithCoeffs.coeff_apply]
    exact Finsupp.notMem_support_iff.mp hQ

section QFactorial

open MMP.Flips

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- Dividing the coefficient by `m` undoes the multiple `m D`:
`(c / m) • (m D) = c • D` for `m > 0`. -/
private theorem div_smul_toRDivisor_zsmul {X : Scheme.{u}} (c : ℝ) {m : ℕ} (hm : 0 < m)
    (D : Divisor X) :
    (c / m) • Divisor.toRDivisor ((m : ℤ) • D) = c • Divisor.toRDivisor D := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast,
    div_mul_cancel₀ c (by exact_mod_cast hm.ne')]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor `G = ∑ g_P P` is the combination
`∑ (g_P / m_P) (m_P P)` of Cartier divisors, where `m_P P` is Cartier. -/
private theorem exists_presentation_of_isQFactorial (hq : IsQFactorial sX) (G : RDivisor X) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
      G = ∑ j, r j • Divisor.toRDivisor (L j) := by
  classical
  choose mq hmq hmqC using fun P : MMP.Mori.PrimeDivisor X => hq.2 (Finsupp.single P 1)
  set Pj : Fin G.support.card → MMP.Mori.PrimeDivisor X :=
    fun j => (G.support.equivFin.symm j : _)
  refine ⟨G.support.card, fun j => G.coeff (Pj j) / (mq (Pj j) : ℝ),
    fun j => (mq (Pj j) : ℤ) • Finsupp.single (Pj j) 1, fun j => hmqC _, ?_⟩
  conv_lhs => rw [eq_sum_coeff_smul_single G]
  exact Finset.sum_congr rfl fun j _ => (div_smul_toRDivisor_zsmul _ (hmq _) _).symm

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isQFactorial (hq : IsQFactorial sX) (G : RDivisor X) :
    IsCartierCombination G := by
  obtain ⟨m, r, L, hL, hG⟩ := exists_presentation_of_isQFactorial hq G
  exact ⟨m, r, L, hL, by rw [hG]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

end QFactorial

section FlipMap

variable {X Z X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- The points of codimension at most one of `X` lie over the open of `Z` over which both small
contractions are isomorphisms. -/
private theorem mem_biregularLocus_inf_of_isSmall (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) {x : X} (hx : Order.coheight x ≤ 1) :
    f x ∈ biregularLocus f ⊓ biregularLocus fp := by
  obtain ⟨V, W, hV, -, hVW, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hxV : x ∈ (V.compl : Set X) := fun h => absurd ((hV x h).trans hx) (by decide)
  have hb : f x ∈ biregularLocus f := le_biregularLocus hiso (hVW hxV)
  refine ⟨hb, mem_biregularLocus_of_isSmall hfp ?_⟩
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb]
  exact hx

/-- **The flip as a birational map.** For small contractions `f : X ⟶ Z ⟵ X⁺ : f⁺` of normal
varieties there is a birational map `g = (f⁺)⁻¹ ∘ f : X ⤏ X⁺` over `Z`, which transforms divisors
as the strict transform `(f⁺)⁻¹_* f_*` and every prime divisor of `X⁺` is a transform. -/
private theorem exists_flipMap (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX')
    (hZ : IsNormalVariety ℂ sZ) (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    (hfpb : IsBirationalMorphism fp) :
    ∃ g : X.RationalMap X', MMP.Mori.RationalMap.IsBirational g ∧
      MMP.Flips.RationalMap.IsOver f fp g ∧
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor g D = flipTransform f fp D) ∧
      ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
        MMP.Mori.RationalMap.transformPrimeDivisor g P = some P' := by
  obtain ⟨g, hg, hgo⟩ := MMP.Mori.exists_isBirational_compHom_eq hfb hfpb
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal_of_isNormalVariety hX'
  haveI : IsIso (f ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
    isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI : IsIso (fp ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
    isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ biregularLocus f ⊓ biregularLocus fp :=
    fun x hx => mem_biregularLocus_inf_of_isSmall hf hfp hx
  have hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ biregularLocus f ⊓ biregularLocus fp :=
    fun x hx => by
      have := mem_biregularLocus_inf_of_isSmall hfp hf hx
      exact ⟨this.2, this.1⟩
  haveI : IsProper f := hf.isProper
  have hXn : IsNormalVariety ℂ (f ≫ sZ) := by rw [hf.comp_eq]; exact hX
  refine ⟨g, hg, hgo, fun D => transformDivisor_eq_flipTransform hZ hXn hfb _ hXV hX'V hgo D,
    fun P' => ?_⟩
  obtain ⟨P, hP⟩ := exists_primeDivisor_genericPoint_eq f fp _ P'
    (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le)
  exact ⟨P, transformPrimeDivisor_eq_some_of_map_eq fp _ hXV hgo hP⟩

end FlipMap

section CurveNormalization

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  have : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        have : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        have : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_sum_degreeOn (D : RDivisor X) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (MMP.Flips.degreeOn_normalization C hν hdim _).symm

end CurveNormalization

/- ### Numerical triviality over the base -/

section Numerical

open MMP.Flips

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X]

/-- The empty presentation computes `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber ℂ sX 0 (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- Every presentation of an `ℝ`-Cartier divisor computes some value of `D · C`. -/
private theorem exists_isRIntersectionNumber {D : RDivisor X} (hD : IsCartierCombination D)
    (C : ProperCurve sX) : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX D r L C x := by
  obtain ⟨m, r, L, hL, hDeq⟩ := hD
  refine ⟨m, r, L, ∑ j, r j * (L j).degreeOn ℂ sX C.ι C.dim_le (hL j),
    isRIntersectionNumber_sum_degreeOn D r L hL ?_ C⟩
  rw [hDeq]
  simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]

/-- `ℝ`-Cartier divisors form a real vector space. -/
private theorem isCartierCombination_add_smul {D N : RDivisor X} (hD : IsCartierCombination D)
    (hN : IsCartierCombination N) (c : ℝ) : IsCartierCombination (D + c • N) := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  obtain ⟨m', r', L', hL', rfl⟩ := hN
  refine ⟨m + m', Fin.append r (c • r'), Fin.append L L', fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hL j
    · simpa using hL' j
  · rw [Fin.sum_univ_add, Finset.smul_sum]
    simp [smul_smul]

/-- A numerically trivial divisor computes `0` on every contracted curve. -/
private theorem eq_zero_of_isNumericallyTrivialOver {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver ℂ sX f N) {C : ProperCurve sX} (hC : C.IsContractedBy f)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber ℂ sX N r L C x) : x = 0 :=
  hN.2.2 C hC m r L x 0 Fin.elim0 Fin.elim0 0 hx (isRIntersectionNumber_zero C)

/-- Adding a multiple of a numerically trivial divisor does not change numerical classes. -/
private theorem isNumericallyEquivalentOver_add_smul {f : X ⟶ Y} {D N : RDivisor X}
    (hD : IsCartierCombination D) (hN : IsNumericallyTrivialOver ℂ sX f N) (c : ℝ) :
    IsNumericallyEquivalentOver ℂ sX f (D + c • N) D := by
  refine ⟨isCartierCombination_add_smul hD hN.1 c, hD,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  obtain ⟨m₃, r₃, L₃, x₃, h₃⟩ := exists_isRIntersectionNumber hN.1 C
  have h0 := eq_zero_of_isNumericallyTrivialOver hN hC h₃
  have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 D N r₂ L₂ r₃ L₃ x₂ x₃ 1 c h₂ h₃
  rw [one_smul] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ hsum, h0]
  ring

/-- A Cartier divisor linearly equivalent to `0` is numerically trivial over any base. -/
private theorem isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent [CompactSpace X]
    (f : X ⟶ Y) {D : Divisor X} (hD : D.IsCartier) (h : D.LinearlyEquivalent 0) :
    IsNumericallyTrivialOver ℂ sX f (Divisor.toRDivisor D) := by
  have hDc : IsCartierCombination (Divisor.toRDivisor D) :=
    ⟨1, fun _ => 1, fun _ => D, fun _ => hD, by simp [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  refine ⟨hDc, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have h₃ := isRIntersectionNumber_sum_degreeOn (Divisor.toRDivisor D) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => D) (fun _ => hD) (by simp) C
  have hdeg : D.degreeOn ℂ sX C.ι C.dim_le hD = 0 :=
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hD h
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ h₃,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₂ L₂ _ _ x₂ _ h₂
      (isRIntersectionNumber_zero C)]
  simp [hdeg]

end Numerical

/-- **Numerically equivalent divisors are ample together** over a projective morphism of normal
varieties (FA 2.16.3). -/
private theorem isRelativelyAmple_of_isNumericallyEquivalentOver {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : IsNormalVariety ℂ sX) (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z}
    (hf : IsProjectiveMorphism f) (hfs : f ≫ sZ = sX) {D A : RDivisor X}
    (hDA : haveI : QuasiCompact sX := hX.1.toQuasiCompact
      MMP.Flips.IsNumericallyEquivalentOver ℂ sX f D A)
    (hA : MMP.Flips.IsRelativelyAmple f A) : MMP.Flips.IsRelativelyAmple f D := by
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf
  exact (MMP.Flips.relativelyAmple_basics sX sZ hX hZ f hfs).2.2.2.2.2
    (IsProjectiveMorphism.isProjective hf) D A hDA hA

section Sign

open MMP.Flips

variable {X Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}

/-- The sum of numerically trivial divisors is numerically trivial. -/
private theorem isNumericallyTrivialOver_add_smul {Y : Scheme.{0}} {f : X ⟶ Y} {T N : RDivisor X}
    (hT : IsNumericallyTrivialOver ℂ sX f T) (hN : IsNumericallyTrivialOver ℂ sX f N) (c : ℝ) :
    IsNumericallyTrivialOver ℂ sX f (T + c • N) := by
  refine ⟨isCartierCombination_add_smul hT.1 hN.1 c, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0,
    by simp⟩, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  obtain ⟨_, rT, LT, xT, hxT⟩ := exists_isRIntersectionNumber hT.1 C
  obtain ⟨_, rN, LN, xN, hxN⟩ := exists_isRIntersectionNumber hN.1 C
  have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 T N rT LT rN LN xT xN 1 c hxT hxN
  rw [one_smul] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ hsum,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₂ L₂ _ _ x₂ _ h₂
      (isRIntersectionNumber_zero C), eq_zero_of_isNumericallyTrivialOver hT hC hxT,
    eq_zero_of_isNumericallyTrivialOver hN hC hxN]
  ring

end Sign

/- ### Linear algebra of strict transforms and of numerical classes -/

section Linear

/-- The strict transform `(f⁺)⁻¹_* f_*` is `ℝ`-linear. -/
private theorem flipTransform_smul {X X' Y : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y) (c : ℝ)
    (D : RDivisor X) : flipTransform f fp (c • D) = c • flipTransform f fp D := by
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply,
    RationalMap.transformDivisor, inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors_smul]

open MMP.Flips

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

/-- An `ℝ`-Cartier divisor numerically equivalent over `Y` to an `f`-nef one is `f`-nef. -/
private theorem isRelativelyNef_of_isNumericallyEquivalentOver {f : X ⟶ Y} {D D' : RDivisor X}
    (h : IsNumericallyEquivalentOver ℂ sX f D' D) (hD : IsRelativelyNef ℂ sX f D) :
    IsRelativelyNef ℂ sX f D' := by
  obtain ⟨m, r, L, hL, hDeq, hnef⟩ := hD
  obtain ⟨m', r', L', hL', hD'eq⟩ := h.1
  refine ⟨m', r', L', hL', by rw [hD'eq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs],
    fun C hC x hx => ?_⟩
  have hy := isRIntersectionNumber_sum_degreeOn D r L hL hDeq C
  rw [h.2.2 C hC m' r' L' x m r L _ hx hy]
  exact hnef C hC _ hy

/-- Adding a multiple of a numerically trivial divisor preserves relative nefness. -/
private theorem isRelativelyNef_add_smul {f : X ⟶ Y} {D N : RDivisor X}
    (hD : IsRelativelyNef ℂ sX f D) (hN : IsNumericallyTrivialOver ℂ sX f N) (c : ℝ) :
    IsRelativelyNef ℂ sX f (D + c • N) :=
  isRelativelyNef_of_isNumericallyEquivalentOver
    (isNumericallyEquivalentOver_add_smul
      (MMP.Fourfold.Oai4C1.Negativity.isCartierCombination_of_isRelativelyNef hD) hN c) hD

/-- A divisor `D` with `D + c N` relatively nef, `N` numerically trivial, is relatively nef. -/
private theorem isRelativelyNef_of_add_smul {f : X ⟶ Y} {D N : RDivisor X} {c : ℝ}
    (hD : IsRelativelyNef ℂ sX f (D + c • N)) (hN : IsNumericallyTrivialOver ℂ sX f N) :
    IsRelativelyNef ℂ sX f D := by
  have := isRelativelyNef_add_smul hD hN (-c)
  rwa [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at this

/-- A numerically trivial divisor is relatively nef. -/
private theorem isRelativelyNef_of_isNumericallyTrivialOver {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver ℂ sX f N) : IsRelativelyNef ℂ sX f N := by
  obtain ⟨m, r, L, hL, hNeq⟩ := hN.1
  refine ⟨m, r, L, hL, by rw [hNeq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs],
    fun C hC x hx => (eq_zero_of_isNumericallyTrivialOver hN hC hx).ge⟩

/-- The negative of a numerically trivial divisor is numerically trivial. -/
private theorem isNumericallyTrivialOver_neg {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver ℂ sX f N) : IsNumericallyTrivialOver ℂ sX f (-N) := by
  have := isNumericallyTrivialOver_add_smul hN hN (-2)
  convert this using 1
  module

/-- A multiple of a numerically trivial divisor is numerically trivial. -/
private theorem isNumericallyTrivialOver_smul {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver ℂ sX f N) (a : ℝ) : IsNumericallyTrivialOver ℂ sX f (a • N) := by
  have := isNumericallyTrivialOver_add_smul hN hN (a - 1)
  convert this using 1
  module

/-- Adding a numerically trivial divisor does not change numerical classes. -/
private theorem isNumericallyEquivalentOver_add {f : X ⟶ Y} {D N : RDivisor X}
    (hD : IsCartierCombination D) (hN : IsNumericallyTrivialOver ℂ sX f N) :
    IsNumericallyEquivalentOver ℂ sX f (D + N) D := by
  simpa only [one_smul] using isNumericallyEquivalentOver_add_smul hD hN 1

/-- A positive multiple of a relatively ample divisor is relatively ample. -/
private theorem isRelativelyAmple_smul {X Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Z} {A : RDivisor X} (hA : IsRelativelyAmple f A) {t : ℝ}
    (ht : 0 < t) : IsRelativelyAmple f (t • A) := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hA
  refine ⟨m, t • r, L, hm, fun j => mul_pos ht (hr j), hL, ?_⟩
  rw [Finset.smul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, smul_smul]

end Linear

/- ### One step of the sequence -/

section Step

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- **The strict transform of a canonical divisor across a flip is canonical.** If `K` is a
canonical divisor of `X`, then `(f⁺)⁻¹_* f_* K` is a canonical divisor of `X⁺`: `f_* K` is a
canonical divisor of `Z`, which is `f⁺_* K⁺` for a canonical divisor `K⁺` of `X⁺`, and the small
`f⁺` identifies the prime divisors of `X⁺` and `Z`. -/
private theorem isCanonicalDivisor_flipTransform (hX : IsNormalVariety ℂ sX)
    (hX' : IsNormalVariety ℂ sX') (hZ : IsNormalVariety ℂ sZ) (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    (hfpb : IsBirationalMorphism fp) {n : ℕ} (hK : K.IsCanonicalDivisor sX n) :
    Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K) := by
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper f := hf.isProper
  haveI : IsProper fp := hfp.isProper
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  have hdimZ : topologicalKrullDim Z = n := by rw [← hf.dim_eq]; exact hK.1
  have hdimX' : topologicalKrullDim X' = n := by rw [hfp.dim_eq]; exact hdimZ
  obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor sZ hZ hdimZ
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sX' hX' hdimX'
  have hXn : IsNormalVariety ℂ (f ≫ sZ) := by rw [hf.comp_eq]; exact hX
  have hX'n : IsNormalVariety ℂ (fp ≫ sZ) := by rw [hfp.comp_eq]; exact hX'
  haveI : LocallyOfFiniteType (f ≫ sZ) := hXn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hX'n.1.toLocallyOfFiniteType
  have hK1 : K.IsCanonicalDivisor (f ≫ sZ) n := by rw [hf.comp_eq]; exact hK
  have hK₀' : K₀.IsCanonicalDivisor (fp ≫ sZ) n := by rw [hfp.comp_eq]; exact hK₀
  have h1 := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hZ hXn hfb hKZ hK1
  obtain ⟨KY, hKY, hKYeq⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hZ hX'n hfpb h1 hK₀'
  have heq : flipTransform f fp K = flipTransform fp fp KY := by
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply, hKYeq]
  have hid : flipTransform fp fp KY = KY := by
    ext P
    simp only [DivisorWithCoeffs.coeff_apply]
    exact flipTransform_apply_of_isSmall hZ hfp hfp hfpb rfl KY
  rw [heq, hid]
  rw [hfp.comp_eq] at hKY
  exact hKY

/-- A principal divisor is numerically trivial over any base. -/
private theorem isNumericallyTrivialOver_principalDivisor [QuasiCompact sX] {Y : Scheme.{0}}
    (g : X ⟶ Y) (ψ : (RationalFunctions X)ˣ) :
    MMP.Flips.IsNumericallyTrivialOver ℂ sX g (Divisor.toRDivisor (principalDivisor ψ)) :=
  isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent g (Divisor.isCartier_principalDivisor ψ)
    (Divisor.linearlyEquivalent_principalDivisor_zero ψ)

/-- **Strict transforms of principal divisors across a flip are principal.** Every rational
function on `X` is the pull-back of one, `φ`, on `Z`; then `f_* div φ = div φ = f⁺_* div φ`, and
the small `f⁺` identifies the prime divisors of `X⁺` and `Z`. -/
private theorem exists_flipTransform_principalDivisor_eq
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) (ψ : (RationalFunctions X)ˣ) :
    ∃ ψ' : (RationalFunctions X')ˣ,
      flipTransform f fp (principalDivisor ψ) = principalDivisor ψ' := by
  have hE := h.isNegativeExtremalContraction
  have hX := hE.isNormalVariety_source
  have hZ := hE.isNormalVariety_target
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper f := h.isSmall.isProper
  haveI : IsProper fp := h.isSmall_flip.isProper
  haveI : IsDominant fp := h.isBirationalMorphism_flip.isDominant
  have hXn : IsNormalVariety ℂ (f ≫ sZ) := by rw [h.isSmall.comp_eq]; exact hX
  have hX'n : IsNormalVariety ℂ (fp ≫ sZ) := by rw [h.isSmall_flip.comp_eq]; exact hX'
  obtain ⟨φ, hφ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq h.isBirationalMorphism ψ
  have hφ' : ∀ Z' : irreducibleComponents X',
      fp (componentGenericPoint X' Z') ∉ (principalDivisor φ).supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant fp _
  have h1 := MMP.Positivity.transformDivisor_principalDivisor_pullback hZ hXn
    h.isBirationalMorphism φ hφ
  have h2 := MMP.Positivity.transformDivisor_principalDivisor_pullback hZ hX'n
    h.isBirationalMorphism_flip φ hφ'
  refine ⟨pullbackRationalFunction fp φ hφ', ?_⟩
  have h3 : flipTransform f fp (principalDivisor (pullbackRationalFunction f φ hφ)) =
      flipTransform fp fp (principalDivisor (pullbackRationalFunction fp φ hφ')) := by
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply, h1, h2]
  rw [h3]
  ext P
  simp only [DivisorWithCoeffs.coeff_apply]
  exact flipTransform_apply_of_isSmall hZ h.isSmall_flip h.isSmall_flip
    h.isBirationalMorphism_flip rfl _

/-- **Numerical triviality crosses the flip.** If `K + D ≡_Z 0` on `X`, then
`K⁺ + D⁺ ≡_Z 0` on `X⁺` for the strict transform `D⁺`: by FA 18 the push-forward along the flip
`(f⁺)⁻¹ ∘ f` of `K + D` is numerically trivial, and it differs from `K⁺ + D⁺` by a principal
divisor. -/
private theorem isNumericallyTrivialOver_logCanonicalDivisor_flipTransform
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    [QuasiCompact sX] [QuasiCompact sX'] (hQ' : IsQFactorial sX') {D : RDivisor X}
    (hD : MMP.Flips.IsNumericallyTrivialOver ℂ sX f (MMP.Flips.logCanonicalDivisor K D)) :
    MMP.Flips.IsNumericallyTrivialOver ℂ sX' fp
      (MMP.Flips.logCanonicalDivisor K' (flipTransform f fp D)) := by
  have hE := h.isNegativeExtremalContraction
  have hX := hE.isNormalVariety_source
  have hZ := hE.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsProper f := h.isSmall.isProper
  haveI : IsProper fp := h.isSmall_flip.isProper
  obtain ⟨g, -, hgo, htr, hsurj⟩ := exists_flipMap hX hX' hZ h.isSmall h.isSmall_flip
    h.isBirationalMorphism h.isBirationalMorphism_flip
  obtain ⟨m, hKm⟩ := hK
  obtain ⟨m', hK'm⟩ := h.isCanonicalDivisor_flip
  have hK'' := isCanonicalDivisor_flipTransform hX hX' hZ h.isSmall h.isSmall_flip
    h.isBirationalMorphism h.isBirationalMorphism_flip hKm
  obtain ⟨φ, hφ⟩ :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX' hK'' hK'm
  have hTK : flipTransform f fp (Divisor.toRDivisor K) =
      Divisor.toRDivisor (flipTransform f fp K) := by
    have := flipTransform_smul_toRDivisor hZ h.isSmall h.isSmall_flip h.isBirationalMorphism 1 K
    simpa only [one_smul] using this
  have hT := (MMP.Flips.IsNumericallyTrivialOver.transformDivisor_of_isOver sZ hX hQ'
    h.isSmall.comp_eq h.isSmall_flip.comp_eq h.isBirationalMorphism h.isBirationalMorphism_flip
    hgo hsurj hD.1 hD).2
  rw [htr] at hT
  have heq : MMP.Flips.logCanonicalDivisor K' (flipTransform f fp D) =
      flipTransform f fp (MMP.Flips.logCanonicalDivisor K D) +
        (-1 : ℝ) • Divisor.toRDivisor (principalDivisor φ) := by
    rw [MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, map_add, hTK, ← hφ, map_sub]
    module
  rw [heq]
  exact isNumericallyTrivialOver_add_smul hT (isNumericallyTrivialOver_principalDivisor fp φ) _

/-- **Changing the boundary by numerically trivial divisors keeps a flip.** Let
`X ⟶ Z ⟵ X⁺` be a step of an extremal real flip sequence for `K + B` with `K + B + C ≡_Z 0`, and
let `div ψ⁺` be the strict transform of a principal divisor `div ψ`. For `0 < ε < 1` the same
diagram is a step for `K + B + εC + c div ψ`: on `X` its negative is numerically
`(1 - ε)(-(K + B))`, and on `X⁺`, where `K⁺ + B⁺ + C⁺ ≡_Z 0` as well, the transformed adjoint is
numerically `(1 - ε)(K⁺ + B⁺)`. -/
private theorem isRealFlipStep_add_smul (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX')
    [QuasiCompact sX] [QuasiCompact sX'] {C : RDivisor X}
    (hnull : MMP.Flips.IsNumericallyTrivialOver ℂ sX f (MMP.Flips.logCanonicalDivisor K (B + C)))
    (ψ : (RationalFunctions X)ˣ) (ψ' : (RationalFunctions X')ˣ)
    (hψ : flipTransform f fp (principalDivisor ψ) = principalDivisor ψ')
    {ε : ℝ} (hε1 : ε < 1) (c : ℝ) :
    IsRealFlipStep sX sZ sX' K (B + ε • C + c • Divisor.toRDivisor (principalDivisor ψ)) K'
      (B' + ε • flipTransform f fp C + c • Divisor.toRDivisor (principalDivisor ψ')) f fp := by
  have hE := h.isNegativeExtremalContraction
  have hX := hE.isNormalVariety_source
  have hZ := hE.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  have hnull' := isNumericallyTrivialOver_logCanonicalDivisor_flipTransform h hK hQ' hnull
  rw [map_add, ← h.eq_flipTransform] at hnull'
  have hG := isNumericallyTrivialOver_principalDivisor (sX := sX) f ψ
  have hG' := isNumericallyTrivialOver_principalDivisor (sX := sX') fp ψ'
  have hT := isNumericallyTrivialOver_add_smul (isNumericallyTrivialOver_smul hnull (-ε)) hG (-c)
  have hT' := isNumericallyTrivialOver_add_smul (isNumericallyTrivialOver_smul hnull' ε) hG' c
  have hnKB :
      -MMP.Flips.logCanonicalDivisor K (B + ε • C + c • Divisor.toRDivisor (principalDivisor ψ)) =
      (1 - ε) • (-MMP.Flips.logCanonicalDivisor K B) +
        ((-ε) • MMP.Flips.logCanonicalDivisor K (B + C) +
          (-c) • Divisor.toRDivisor (principalDivisor ψ)) := by
    simp only [MMP.Flips.logCanonicalDivisor]; module
  have hKB' : MMP.Flips.logCanonicalDivisor K'
      (B' + ε • flipTransform f fp C + c • Divisor.toRDivisor (principalDivisor ψ')) =
      (1 - ε) • MMP.Flips.logCanonicalDivisor K' B' +
        (ε • MMP.Flips.logCanonicalDivisor K' (B' + flipTransform f fp C) +
          c • Divisor.toRDivisor (principalDivisor ψ')) := by
    simp only [MMP.Flips.logCanonicalDivisor]; module
  have h1ε : 0 < 1 - ε := by linarith
  exact
    { isQuasiProjectiveVariety_target := h.isQuasiProjectiveVariety_target
      isNegativeExtremalContraction :=
        { isNormalVariety_source := hX
          isNormalVariety_target := hZ
          isCartierCombination := isCartierCombination_of_isQFactorial hQ _
          isContraction := hE.isContraction
          isRelativelyAntiAmple := by
            change MMP.Flips.IsRelativelyAmple f _
            rw [hnKB]
            exact isRelativelyAmple_of_isNumericallyEquivalentOver hX hZ h.isProjectiveMorphism
              hE.isContraction.comp_eq
              (isNumericallyEquivalentOver_add (isCartierCombination_of_isQFactorial hQ _) hT)
              (isRelativelyAmple_smul hE.isRelativelyAntiAmple h1ε)
          relativePicardNumber_eq_one := hE.relativePicardNumber_eq_one }
      isSmall := h.isSmall
      isBirationalMorphism := h.isBirationalMorphism
      isProjectiveMorphism := h.isProjectiveMorphism
      not_isIso := h.not_isIso
      isCanonicalDivisor_flip := h.isCanonicalDivisor_flip
      isSmall_flip := h.isSmall_flip
      isBirationalMorphism_flip := h.isBirationalMorphism_flip
      isProjectiveMorphism_flip := h.isProjectiveMorphism_flip
      not_isIso_flip := h.not_isIso_flip
      relativePicardNumber_flip := h.relativePicardNumber_flip
      isRelativelyAmple_flip := by
        rw [hKB']
        exact isRelativelyAmple_of_isNumericallyEquivalentOver hX' hZ
          h.isProjectiveMorphism_flip h.isSmall_flip.comp_eq
          (isNumericallyEquivalentOver_add (isCartierCombination_of_isQFactorial hQ' _) hT')
          (isRelativelyAmple_smul h.isRelativelyAmple_flip h1ε)
      eq_flipTransform := by
        rw [map_add, map_add, flipTransform_smul, ← h.eq_flipTransform,
          flipTransform_smul_toRDivisor hZ h.isSmall h.isSmall_flip h.isBirationalMorphism, hψ] }

/-- **The threshold stays one.** If `1` is the least `t ≥ 0` with `K + B + tC` nef over `g`,
then it is also the least `t ≥ 0` with `K + (B + εC + c div ψ) + t(1 - ε)C` nef over `g`, since
that divisor is `K + B + (ε + t(1 - ε))C` up to the principal `c div ψ`. -/
private theorem isLeast_add_smul [QuasiCompact sX] {Y : Scheme.{0}} {g : X ⟶ Y}
    {C : RDivisor X} (ψ : (RationalFunctions X)ˣ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ)
    (hthr : IsLeast {t : ℝ | 0 ≤ t ∧ MMP.Flips.IsRelativelyNef ℂ sX g
      (MMP.Flips.logCanonicalDivisor K (B + t • C))} 1) :
    IsLeast {t : ℝ | 0 ≤ t ∧ MMP.Flips.IsRelativelyNef ℂ sX g
      (MMP.Flips.logCanonicalDivisor K
        (B + ε • C + c • Divisor.toRDivisor (principalDivisor ψ) + t • ((1 - ε) • C)))} 1 := by
  have hG := isNumericallyTrivialOver_principalDivisor (sX := sX) g ψ
  have key : ∀ t : ℝ, MMP.Flips.logCanonicalDivisor K
      (B + ε • C + c • Divisor.toRDivisor (principalDivisor ψ) + t • ((1 - ε) • C)) =
      MMP.Flips.logCanonicalDivisor K (B + (ε + t * (1 - ε)) • C) +
        c • Divisor.toRDivisor (principalDivisor ψ) := fun t => by
    simp only [MMP.Flips.logCanonicalDivisor]; module
  refine ⟨⟨zero_le_one, ?_⟩, fun t ⟨ht0, ht⟩ => ?_⟩
  · rw [key, show ε + 1 * (1 - ε) = 1 by ring]
    exact isRelativelyNef_add_smul hthr.1.2 hG c
  · rw [key] at ht
    have hs := hthr.2 ⟨by nlinarith, isRelativelyNef_of_add_smul ht hG⟩
    nlinarith

/-- **One step of the perturbation.** Let `X ⟶ Z ⟵ X⁺` be a `(K + B)`-flip with scaling of `C`
at threshold one over `g`, with `K + B + C ≡_Z 0` and `C⁺` the strict transform of `C`, and let
`div ψ⁺` be the strict transform of `div ψ`. For `0 < ε < 1` the same diagram is a
`(K + B + εC + c div ψ)`-flip with scaling of `(1 - ε)C`, whose strict transform is `(1 - ε)C⁺`,
again with `K + B + C + c div ψ ≡_Z 0` and threshold one. -/
private theorem isRealFlipStep_perturb (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX')
    [QuasiCompact sX] [QuasiCompact sX'] {Y : Scheme.{0}} {g : X ⟶ Y} {C : RDivisor X}
    {C' : RDivisor X'} (hC' : C' = flipTransform f fp C)
    (hnull : MMP.Flips.IsNumericallyTrivialOver ℂ sX f (MMP.Flips.logCanonicalDivisor K (B + C)))
    (hthr : IsLeast {t : ℝ | 0 ≤ t ∧ MMP.Flips.IsRelativelyNef ℂ sX g
      (MMP.Flips.logCanonicalDivisor K (B + t • C))} 1)
    (ψ : (RationalFunctions X)ˣ) (ψ' : (RationalFunctions X')ˣ)
    (hψ : flipTransform f fp (principalDivisor ψ) = principalDivisor ψ')
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) :
    IsRealFlipStep sX sZ sX' K (B + ε • C + c • Divisor.toRDivisor (principalDivisor ψ)) K'
        (B' + ε • C' + c • Divisor.toRDivisor (principalDivisor ψ')) f fp ∧
      (1 - ε) • C' = flipTransform f fp ((1 - ε) • C) ∧
      MMP.Flips.IsNumericallyTrivialOver ℂ sX f (MMP.Flips.logCanonicalDivisor K
        (B + ε • C + c • Divisor.toRDivisor (principalDivisor ψ) + (1 - ε) • C)) ∧
      IsLeast {t : ℝ | 0 ≤ t ∧ MMP.Flips.IsRelativelyNef ℂ sX g
        (MMP.Flips.logCanonicalDivisor K
          (B + ε • C + c • Divisor.toRDivisor (principalDivisor ψ) + t • ((1 - ε) • C)))} 1 := by
  subst hC'
  refine ⟨isRealFlipStep_add_smul h hK hQ hQ' hnull ψ ψ' hψ hε1 c, (flipTransform_smul ..).symm,
    ?_, isLeast_add_smul ψ hε0 hε1 c hthr⟩
  have heq : MMP.Flips.logCanonicalDivisor K
      (B + ε • C + c • Divisor.toRDivisor (principalDivisor ψ) + (1 - ε) • C) =
      MMP.Flips.logCanonicalDivisor K (B + C) + c • Divisor.toRDivisor (principalDivisor ψ) := by
    simp only [MMP.Flips.logCanonicalDivisor]; module
  rw [heq]
  exact isNumericallyTrivialOver_add_smul hnull (isNumericallyTrivialOver_principalDivisor f ψ) c

end Step

/- ### The dictionary between the two log discrepancies -/

section Bridge

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]

/-- With a presentation of `div(ω) + D` by Cartier divisors, every divisor over `X` (with proper
model) has a discrepancy computed with these choices. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety ℂ sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : MMP.Flips.ProperDivisorOver ℂ sX) : ∃ b, MMP.Flips.IsDiscrepancyWith sX n D ω r L E b := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hX, hn, hω, hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : MMP.Flips.ProperDivisorOver ℂ sX) :
    MMP.Flips.HasNonemptyCenter ℂ sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-- A log discrepancy is a discrepancy, computed with the form inside it, plus one. -/
private theorem isDiscrepancyWith_of_isLogDiscrepancy {n : ℕ} {B : RDivisor X}
    {D : DivisorOver ℂ sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) :
    ∃ (ω : RationalPluriForms sX n 1) (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      MMP.Flips.IsDiscrepancyWith sX n B ω r L ⟨D, h.2.1⟩ (a - 1) := by
  obtain ⟨hX, hp, ω, hω, ⟨K, hK, hKc⟩, m, r, C, C', hC, hrel, hpb, ha⟩ := h
  refine ⟨ω, m, r, C, hX, hK.topologicalKrullDim_eq, hω, hC, ?_, C', hpb, ?_⟩
  · refine DivisorWithCoeffs.ext' fun Γ => ?_
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
      MMP.Flips.coeff_sum_smul_toRDivisor]
    exact hrel Γ
  · exact (by linear_combination ha :
      a - 1 = (D.ordPullback ω : ℝ) - ∑ j, r j * ((C' j).coeff D.E : ℝ))

/-- A log discrepancy, against a presentation of `div(ω) + B`, gives the discrepancy `a - 1` of
the valuation in the sense of *Flips and abundance*. -/
private theorem isDiscrepancy_of_isLogDiscrepancy {n : ℕ} {B : RDivisor X}
    {D : DivisorOver ℂ sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B)) :
    MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) B D.valuation (a - 1) := by
  obtain ⟨ω', m', r', L', hw'⟩ := isDiscrepancyWith_of_isLogDiscrepancy h
  obtain ⟨m, r, L, hLc, hsum⟩ := hKB
  have hsum' : Divisor.toRDivisor (divisorOfForm ω) + B =
      ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hsum
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith h.1 hK.topologicalKrullDim_eq hω hLc hsum'
    ⟨D, h.2.1⟩
  have hab := hb.eq hw' rfl
  refine ⟨hK, ⟨m, r, L, hLc, hsum⟩, hasNonemptyCenter_valuation ⟨D, h.2.1⟩, ⟨D, h.2.1⟩, ω, m, r,
    L, rfl, rfl, ?_⟩
  rwa [hab] at hb

end Bridge

section FormDivisors

/-- A divisor canonical in some dimension is canonical in the dimension of the variety. -/
private theorem isCanonicalDivisor_of_topologicalKrullDim_eq {k : Type u} [Field k]
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {K : Divisor X} (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) {n : ℕ}
    (hn : topologicalKrullDim X = n) : K.IsCanonicalDivisor sX n := by
  obtain ⟨m, hm⟩ := hK
  obtain rfl : m = n := by exact_mod_cast hm.topologicalKrullDim_eq.symm.trans hn
  exact hm

end FormDivisors

section Forms

open MMP.Flips

/-- The pull-back of rational forms along an isomorphism of function fields is surjective. -/
private theorem pullbackForms_surjective {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    (hbij : Function.Bijective (algebraMap K K')) {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : IsPullbackGenerator K' ω) (m : ℤ) :
    Function.Surjective (pullbackForms (k := k) (K := K) (K' := K') (d := d) m) := by
  intro σ
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  obtain ⟨c, hc⟩ := hbij.2 (b'.repr σ ())
  refine ⟨c • b (), ?_⟩
  have h1 : b.repr (c • b ()) () = c := by
    simp [Module.Basis.repr_self]
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  change algebraMap K K' (b.repr (c • b ()) ()) • b' () = σ
  rw [h1, hc]
  exact basis_unit_repr_smul b' σ

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)}

/-- Every rational top form on a birational model is a pull-back. -/
private theorem exists_pullbackRationalPluriForms_eq [LocallyOfFiniteType sX] (g : Y ⟶ X)
    [IsDominant g] (hg : Function.Bijective (functionFieldMap g)) {n : ℕ}
    (hn : topologicalKrullDim X = n) (σ : RationalPluriForms (g ≫ sX) n 1) :
    ∃ ω : RationalPluriForms sX n 1, pullbackRationalPluriForms sX g ω = σ := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hg hd
  exact pullbackForms_surjective hg hω 1 σ

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero (g : Y ⟶ X) [IsDominant g] {n : ℕ} :
    pullbackRationalPluriForms sX g (0 : RationalPluriForms sX n 1) = 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  have h := pullbackForms_smul (K' := Y.functionField) (k := ℂ) (d := n) (m := 1)
    (0 : X.functionField) (0 : RationalPluriForms sX n 1)
  simp only [zero_smul, map_zero] at h
  exact h

/-- On a normal variety with a canonical divisor, the divisor of every nonzero rational top form
is canonical. -/
private theorem isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {τ : RationalPluriForms sX n 1}
    (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n :=
  hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ

end Forms

section KltStep

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- Across two small birational contractions `f : X ⟶ Z ⟵ X⁺ : g`, the inverse transform
`g⁻¹_* f_* Γ` along `g` is the strict transform `(g)⁻¹_* f_* Γ`. -/
private theorem birationalInverseTransform_transformDivisor [IsIntegral Z]
    (hZ : IsNormalVariety ℂ sZ) {g : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hg : MMP.Flips.IsSmall ℂ sZ sX' g) (hfb : IsBirationalMorphism f)
    (hgb : IsBirationalMorphism g) (Γ : RDivisor X) :
    MMP.Flips.birationalInverseTransform g hgb
      (RationalMap.transformDivisor (X := X) f.toRationalMap Γ) = flipTransform f g Γ := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsProper g := hg.isProper
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, hP⟩ := exists_primeDivisor_map_eq_of_isSmall hg hf P'
  obtain ⟨hco, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  have hQ : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco).genericPoint = f P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hgY : MMP.Mori.IsVariety ℂ (g ≫ sZ) := by rw [hg.comp_eq]; exact hg.isVariety_source
  rw [MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hZ g hgY hgb _
      (hP.symm.trans hQ.symm),
    flipTransform_apply_of_isSmall hZ hf hg hfb hP.symm Γ]
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P _).mpr hQ.symm)
    (fun P₁ hP₁ => primeDivisor_eq_of_map_eq_of_isSmall hf
      (((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P₁ _).mp hP₁).trans
        hQ)) Γ

/-- **Log discrepancies across a crepant flip diagram** (FA 2.28 over the base). If
`K + Γ ≡_Z 0` on `X`, every log discrepancy `a'` over `X⁺` of the strict transform `Γ⁺` is at
least a log discrepancy over `X` of `Γ`: both `-(K + Γ)` and `K⁺ + Γ⁺` are nef over `Z`, and the
divisor of `k(X⁺)` is realized over `X` by the same valuation of `k(Z)`. -/
private theorem exists_isLogDiscrepancy_le (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX')
    [QuasiCompact sX] [QuasiCompact sX'] {Γ : RDivisor X}
    (hΓ : MMP.Flips.IsNumericallyTrivialOver ℂ sX f (MMP.Flips.logCanonicalDivisor K Γ))
    {n : ℕ} {E' : DivisorOver ℂ sX'} {a' : ℝ}
    (ha' : MMP.Intersection.IsLogDiscrepancy sX' n (flipTransform f fp Γ) E' a') :
    ∃ (E : DivisorOver ℂ sX) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX n Γ E a ∧ a ≤ a' := by
  classical
  have hΓ' := isNumericallyTrivialOver_logCanonicalDivisor_flipTransform h hK hQ' hΓ
  have hE := h.isNegativeExtremalContraction
  have hX := hE.isNormalVariety_source
  have hZ := hE.isNormalVariety_target
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  have hfb := h.isBirationalMorphism
  have hfpb := h.isBirationalMorphism_flip
  have hsm := h.isSmall
  have hsm' := h.isSmall_flip
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  haveI : IsProper f := hsm.isProper
  haveI : IsProper fp := hsm'.isProper
  haveI := hfb.isDominant
  haveI := hfpb.isDominant
  -- dimensions and canonical divisors in dimension `n`
  have hdX' : topologicalKrullDim X' = n :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha'
  have hdZ : topologicalKrullDim Z = n := by rw [← hsm'.dim_eq]; exact hdX'
  have hdX : topologicalKrullDim X = n := by rw [hsm.dim_eq]; exact hdZ
  have hKn := isCanonicalDivisor_of_topologicalKrullDim_eq hK hdX
  have hK'n := isCanonicalDivisor_of_topologicalKrullDim_eq h.isCanonicalDivisor_flip hdX'
  -- the structure morphisms through `Z`
  have hfs : f ≫ sZ = sX := hsm.comp_eq
  have hfps : fp ≫ sZ = sX' := hsm'.comp_eq
  subst hfs hfps
  -- a top form on `Z` computing `K`
  obtain ⟨ωX, hωX0, hωXK⟩ := exists_divisorOfForm_eq hX hKn
  obtain ⟨ω, hω⟩ := exists_pullbackRationalPluriForms_eq f hfb.functionFieldMap_bijective hdZ ωX
  have hω0 : ω ≠ 0 := by
    rintro rfl
    exact hωX0 (hω ▸ pullbackRationalPluriForms_zero f)
  have hωY0 : pullbackRationalPluriForms sZ fp ω ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' fp
      hfpb.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdZ) hω0
  have hKY : (divisorOfForm (pullbackRationalPluriForms sZ fp ω)).IsCanonicalDivisor
      (fp ≫ sZ) n := isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor hX' hK'n hωY0
  obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (fp ≫ sZ) hX'
    hKY hK'n
  -- the boundaries are strict transforms of `f_* Γ`
  have hBX : MMP.Flips.birationalInverseTransform f hfb
      (RationalMap.transformDivisor (X := X) f.toRationalMap Γ) = Γ := by
    rw [birationalInverseTransform_transformDivisor hZ hsm hsm hfb hfb Γ]
    ext P
    simp only [DivisorWithCoeffs.coeff_apply]
    exact flipTransform_apply_of_isSmall hZ hsm hsm hfb rfl Γ
  have hBY : MMP.Flips.birationalInverseTransform fp hfpb
      (RationalMap.transformDivisor (X := X) f.toRationalMap Γ) = flipTransform f fp Γ :=
    birationalInverseTransform_transformDivisor hZ hsm hsm' hfb hfpb Γ
  -- the valuation over `Z` and its realization over `X`
  have hE'p : IsProper E'.f := ha'.2.1
  have hv : MMP.Flips.HasNonemptyCenter ℂ sZ (E'.valuation.comap (functionFieldMap fp)) := by
    haveI := hE'p
    have hp : IsProper (MMP.Mori.compDivisorOver fp hX' hfpb E').f :=
      (inferInstance : IsProper (E'.f ≫ fp))
    have := hasNonemptyCenter_valuation (sX := sZ) ⟨MMP.Mori.compDivisorOver fp hX' hfpb E', hp⟩
    rwa [show (⟨MMP.Mori.compDivisorOver fp hX' hfpb E', hp⟩ :
      MMP.Flips.ProperDivisorOver ℂ sZ).valuation = E'.valuation.comap (functionFieldMap fp) from
        MMP.Mori.valuation_compDivisorOver fp hX' hfpb E'] at this
  set ef := RingEquiv.ofBijective (functionFieldMap f) hfb.functionFieldMap_bijective with hef
  have hvX : ((E'.valuation.comap (functionFieldMap fp)).comap
      (ef.symm : X.functionField →+* Z.functionField)).comap (functionFieldMap f) =
      E'.valuation.comap (functionFieldMap fp) := by
    ext t
    simp only [Valuation.comap_apply]
    exact congrArg (fun x => E'.valuation (functionFieldMap fp x)) (ef.symm_apply_apply t)
  -- the comparison over `Z`
  obtain ⟨hcX, -, hcmp⟩ := MMP.Flips.isDiscrepancy_le_of_isRelativelyNef
    (D := RationalMap.transformDivisor (X := X) f.toRationalMap Γ) (E_X := 0) (E_Y := 0)
    (K_X := K) (K_Y := divisorOfForm (pullbackRationalPluriForms sZ fp ω)) hZ hX hX' hfb hfpb
    (by rw [hω, hωXK]) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      rw [add_zero, hBX]
      exact isRelativelyNef_of_isNumericallyTrivialOver (isNumericallyTrivialOver_neg hΓ))
    (by
      rw [add_zero, hBY]
      have heq : MMP.Flips.logCanonicalDivisor (divisorOfForm (pullbackRationalPluriForms sZ fp ω))
          (flipTransform f fp Γ) = MMP.Flips.logCanonicalDivisor K' (flipTransform f fp Γ) +
            (1 : ℝ) • Divisor.toRDivisor (principalDivisor φ) := by
        rw [MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, ← hφ, map_sub]
        module
      rw [heq]
      exact isRelativelyNef_of_isNumericallyTrivialOver (isNumericallyTrivialOver_add_smul hΓ'
        (isNumericallyTrivialOver_principalDivisor fp φ) 1))
    hv hvX rfl
  obtain ⟨-, E, hEv⟩ := hcX
  have hKω : (divisorOfForm ωX).IsCanonicalDivisor (f ≫ sZ) n := hωXK ▸ hKn
  have hcart : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωX) + Γ) := by
    rw [hωXK]; exact isCartierCombination_of_isQFactorial hQ _
  obtain ⟨a, ha⟩ := exists_isLogDiscrepancy hX hωX0 hKω hcart E.toDivisorOver E.isProper
  refine ⟨E.toDivisorOver, a, ha, ?_⟩
  have h1 := isDiscrepancy_of_isLogDiscrepancy ha hωX0 hKω hcart
  rw [hωXK] at h1
  have h2 := isDiscrepancy_of_isLogDiscrepancy ha' hωY0 hKY
    (isCartierCombination_of_isQFactorial hQ' _)
  have := hcmp (a - 1) (a' - 1) (by rw [add_zero, hBX, ← hEv]; exact h1)
    (by rw [add_zero, hBY]; exact h2)
  linarith

/-- **Klt crosses a crepant flip diagram.** If `X ⟶ Z ⟵ X⁺` is a step of an extremal real flip
sequence, `(X, Γ)` is klt and `K + Γ ≡_Z 0`, then `(X⁺, Γ⁺)` is klt for the strict transform
`Γ⁺`: its coefficients are those of `Γ`, it is `ℝ`-Cartier on the `ℚ`-factorial `X⁺`, and every
log discrepancy over `X⁺` is bounded below by one over `X`. -/
private theorem isRealKltPair_flipTransform (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX')
    [QuasiCompact sX] [QuasiCompact sX'] {Γ : RDivisor X}
    (hΓ : MMP.Flips.IsNumericallyTrivialOver ℂ sX f (MMP.Flips.logCanonicalDivisor K Γ))
    (hklt : IsRealKltPair sX Γ) : IsRealKltPair sX' (flipTransform f fp Γ) := by
  have hZ := h.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  refine ⟨hX', fun P' => ?_, ?_, fun n E' a' ha' => ?_⟩
  · obtain ⟨P, hP⟩ := exists_primeDivisor_map_eq_of_isSmall h.isSmall_flip h.isSmall P'
    have h1 : (flipTransform f fp Γ).coeff P' = Γ.coeff P := by
      simpa only [DivisorWithCoeffs.coeff_apply] using
        flipTransform_apply_of_isSmall hZ h.isSmall h.isSmall_flip h.isBirationalMorphism hP.symm Γ
    rw [h1]
    exact hklt.2.1 P
  · obtain ⟨m', hK'm⟩ := h.isCanonicalDivisor_flip
    refine ⟨m', K', hK'm, ?_⟩
    obtain ⟨m, r, L, hL, heq⟩ := exists_presentation_of_isQFactorial hQ'
      (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K' + flipTransform f fp Γ)
    exact ⟨m, r, L, hL, fun Γ₀ => by rw [heq, MMP.Flips.coeff_sum_smul_toRDivisor]⟩
  · obtain ⟨E, a, ha, hle⟩ := exists_isLogDiscrepancy_le h hK hQ hQ' hΓ ha'
    exact (hklt.2.2.2 n E a ha).trans_le hle

end KltStep

/-- The strict transforms `D_i` of a divisor `D` on the models of a sequence of diagrams
`X_i ⟶ W_i ⟵ X_{i+1}`: `D_0 = D` and `D_{i+1} = (f_i⁺)⁻¹_* (f_i)_* D_i`. -/
private noncomputable def transformSeq {R : Type*} [AddCommMonoid R] {X : Scheme.{0}}
    {Y W : ℕ → Scheme.{0}} (f : ∀ i, modelSeq X Y i ⟶ W i) (fp : ∀ i, Y i ⟶ W i)
    (D : DivisorWithCoeffs R X) : ∀ i, DivisorWithCoeffs R (modelSeq X Y i)
  | 0 => D
  | i + 1 => flipTransform (f i) (fp i) (transformSeq f fp D i)

/-- **The perturbed boundary on `X`.** Let `(X, B + C)` be dlt on a `ℚ`-factorial projective
variety, with `B ≥ A ≥ 0` for an ample `ℚ`-divisor `A` having no component in `⌊B + C⌋`. Floor
lowering applied to `A/2` gives `A' ∼_ℚ A/2 + δ⌊B + C⌋`, that is `A' - A/2 - δ⌊B + C⌋ = c div ψ`,
with `(X, B + C - A/2 - δ⌊B + C⌋ + A')` klt. Then `B̃ = B + C/2 + c div ψ` is effective and
contains the ample `A/2`, and `(X, B̃ + C/2)` is klt. -/
private theorem exists_isRealKltPair_add_smul_principalDivisor {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX) {B C : RDivisor X}
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P) (hdlt : IsRealDltPair sX (B + C))
    {A : QDivisor X} (hA0 : ∀ P, 0 ≤ A.coeff P) (hA : A.IsAmple)
    (hAB : ∀ P, (A.coeff P : ℝ) ≤ B.coeff P) (hAfloor : ∀ P, A.coeff P ≠ 0 → (B + C).coeff P < 1) :
    ∃ (ψ : (RationalFunctions X)ˣ) (c : ℝ),
      (∀ P, 0 ≤ (B + (1 / 2 : ℝ) • C + c • Divisor.toRDivisor (principalDivisor ψ)).coeff P) ∧
      IsRealKltPair sX
        (B + (1 / 2 : ℝ) • C + c • Divisor.toRDivisor (principalDivisor ψ) + (1 - 1 / 2 : ℝ) • C) ∧
      ∃ A' : QDivisor X, (∀ P, 0 ≤ A'.coeff P) ∧ A'.IsAmple ∧ ∀ P,
        (A'.coeff P : ℝ) ≤
          (B + (1 / 2 : ℝ) • C + c • Divisor.toRDivisor (principalDivisor ψ)).coeff P := by
  classical
  set ε : ℝ := 1 / 2 with hεdef
  -- the floor of `B + C` and the floor-lowering divisor `A'`
  set Γ : RDivisor X := B + C with hΓdef
  have hΓ0 : ∀ P, 0 ≤ Γ.coeff P := hdlt.1.2.1
  have hΓ1 : ∀ P, Γ.coeff P ≤ 1 := hdlt.2.1
  set T : Divisor X := DivisorWithCoeffs.roundDown Γ with hTdef
  have hTc : ∀ P, (T.coeff P : ℝ) = if Γ.coeff P = 1 then 1 else 0 := fun P => by
    rw [hTdef, DivisorWithCoeffs.coeff_roundDown]
    split_ifs with h
    · rw [h, Int.floor_one]; simp
    · rw [Int.floor_eq_zero_iff.mpr ⟨hΓ0 P, lt_of_le_of_ne (hΓ1 P) h⟩]; simp
  have hAΓ : ∀ P, Γ.coeff P = 1 → A.coeff P = 0 := fun P h => by
    by_contra hA'
    have := hAfloor P hA'
    rw [h] at this
    exact lt_irrefl _ this
  set A₂ : QDivisor X := (1 / 2 : ℚ) • A with hA₂def
  have hA₂c : ∀ P, ((A₂.coeff P : ℚ) : ℝ) = (A.coeff P : ℝ) / 2 := fun P => by
    rw [hA₂def, DivisorWithCoeffs.coeff_smul, smul_eq_mul]; push_cast; ring
  have hA₂amp : A₂.IsAmple := by
    obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hA
    refine ⟨2 * m, by omega, D, ?_, hDc, hDa⟩
    rw [hD, hA₂def, smul_smul]
    congr 1
    push_cast
    ring
  have hA₂0 : ∀ P, 0 ≤ A₂.coeff P := fun P => by
    rw [hA₂def, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    exact mul_nonneg (by norm_num) (hA0 P)
  have hA₂Γ : ∀ P, (A₂.coeff P : ℝ) ≤ Γ.coeff P := fun P => by
    rw [hA₂c, hΓdef, DivisorWithCoeffs.coeff_add]
    have := hAB P
    have := hC P
    have : (0 : ℝ) ≤ A.coeff P := by exact_mod_cast hA0 P
    linarith
  have hA₂T : ∀ P, A₂.coeff P ≠ 0 → T.coeff P = 0 := fun P hP => by
    have hAP : A.coeff P ≠ 0 := by
      intro h0; apply hP; rw [hA₂def, DivisorWithCoeffs.coeff_smul, h0, smul_zero]
    have h1 := hAfloor P hAP
    have h2 := hTc P
    rw [if_neg h1.ne] at h2
    exact_mod_cast h2
  obtain ⟨δ₀, hδ₀, hfl⟩ := IsRealDltPair.exists_isRealKltPair_sub_add_of_isAmple hXq hX hdlt
    hA₂amp hA₂0 hA₂Γ hA₂T
  set δ : ℚ := min δ₀ (1 / 2) / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ₀' : δ < δ₀ := by
    have := min_le_left δ₀ (1 / 2); rw [hδdef]; linarith
  have hδ4 : δ ≤ 1 / 4 := by
    have := min_le_right δ₀ (1 / 2); rw [hδdef]; linarith
  obtain ⟨A', hA'0, -, -, hA'eq, -, hklt0⟩ :=
    hfl δ hδ0 hδ₀' 1 one_pos ∅ Set.finite_empty (by simp)
  obtain ⟨m, hm, ψ, hψ⟩ := hA'eq
  set c : ℝ := 1 / (m : ℝ) with hcdef
  refine ⟨ψ, c, ?_⟩
  set G : Divisor X := principalDivisor ψ with hGdef
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hGc : ∀ P, c * (G.coeff P : ℝ) =
      (A'.coeff P : ℝ) - ((A.coeff P : ℝ) / 2 + (δ : ℝ) * (T.coeff P : ℝ)) := fun P => by
    have h1 := congrArg (fun D : QDivisor X => D.coeff P) hψ
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, zsmul_eq_mul, Int.cast_natCast,
      smul_eq_mul] at h1
    have h2 : ((G.coeff P : ℤ) : ℝ) = (m : ℝ) * ((A'.coeff P : ℝ) - ((A₂.coeff P : ℝ) +
        (δ : ℝ) * ((T.coeff P : ℤ) : ℝ))) := by
      rw [hGdef]; exact_mod_cast h1.symm
    rw [h2, hA₂c, hcdef]
    field_simp
  have hP : QDivisor.toRDivisor A' - QDivisor.toRDivisor (A₂ + δ • Divisor.toQDivisor T) =
      c • Divisor.toRDivisor G := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, hGc P]
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, smul_eq_mul, hA₂def]
    push_cast
    ring
  set B' : RDivisor X := B + ε • C + c • Divisor.toRDivisor G with hB'def
  set C' : RDivisor X := (1 - ε) • C with hC'def
  have hB'c : ∀ P, B'.coeff P = B.coeff P + ε * C.coeff P - (A.coeff P : ℝ) / 2 -
      (δ : ℝ) * (T.coeff P : ℝ) + (A'.coeff P : ℝ) := fun P => by
    rw [hB'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul,
      Divisor.coeff_toRDivisor, hGc P]
    ring
  have hB'A : ∀ P, (A₂.coeff P : ℝ) ≤ B'.coeff P := fun P => by
    rw [hA₂c, hB'c]
    have hA'P : (0 : ℝ) ≤ A'.coeff P := by exact_mod_cast hA'0 P
    have hAP : (0 : ℝ) ≤ A.coeff P := by exact_mod_cast hA0 P
    have hCP := hC P
    have hBP := hB P
    have hABP := hAB P
    have hTP := hTc P
    have hδR : (δ : ℝ) ≤ 1 / 4 := by
      have := (Rat.cast_le (K := ℝ)).mpr hδ4
      push_cast at this
      linarith
    split_ifs at hTP with hΓP
    · have hA0' : (A.coeff P : ℝ) = 0 := by rw [hAΓ P hΓP]; simp
      have hΓP' : B.coeff P + C.coeff P = 1 := by
        rw [← DivisorWithCoeffs.coeff_add]; exact hΓP
      rw [hTP, hA0', hεdef]
      nlinarith
    · rw [hTP]
      nlinarith
  have hB'0 : ∀ P, 0 ≤ B'.coeff P := fun P => by
    refine le_trans ?_ (hB'A P)
    rw [hA₂c]
    have : (0 : ℝ) ≤ A.coeff P := by exact_mod_cast hA0 P
    linarith
  have hBC' : B' + C' = Γ - QDivisor.toRDivisor (A₂ + δ • Divisor.toQDivisor T) +
      QDivisor.toRDivisor A' := by
    rw [show QDivisor.toRDivisor A' = QDivisor.toRDivisor (A₂ + δ • Divisor.toQDivisor T) +
      c • Divisor.toRDivisor G from by rw [← hP]; abel, hB'def, hC'def, hΓdef]
    module
  exact ⟨hB'0, by rw [hBC']; exact hklt0, A₂, hA₂0, hA₂amp, hB'A⟩

/-- The strict transforms of a principal divisor along a sequence of flips are principal. -/
private theorem exists_transformSeq_principalDivisor_eq {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ∞}
    {Y W : ℕ → Scheme.{0}} {sY : ∀ i, Y i ⟶ Spec (.of ℂ)} [∀ i, IsIntegral (Y i)]
    [∀ i, CompactSpace (Y i)] [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    {sW : ∀ i, W i ⟶ Spec (.of ℂ)} {f : ∀ i, modelSeq X Y i ⟶ W i} {fp : ∀ i, Y i ⟶ W i}
    {K : Divisor X} {KY : ∀ i, Divisor (Y i)} {B : RDivisor X} {BY : ∀ i, RDivisor (Y i)}
    (hstep : ∀ i : ℕ, (i : ℕ∞) < n →
      IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
        (KY i) (BY i) (f i) (fp i))
    (ψ : (RationalFunctions X)ˣ) :
    ∀ i : ℕ, (i : ℕ∞) ≤ n → ∃ φ, transformSeq f fp (principalDivisor ψ) i = principalDivisor φ := by
  intro i
  induction i with
  | zero => intro _; exact ⟨ψ, rfl⟩
  | succ i ih =>
    intro hi
    have hi' : (i : ℕ∞) < n := (ENat.coe_lt_coe.mpr (Nat.lt_succ_self i)).trans_le hi
    obtain ⟨φ, hφ⟩ := ih hi'.le
    obtain ⟨φ', hφ'⟩ := exists_flipTransform_principalDivisor_eq (hstep i hi') φ
    exact ⟨φ', (congrArg (flipTransform (f i) (fp i)) hφ).trans hφ'⟩

/-- **A constant scaling level can be made klt.** Let `π : X ⟶ Z` be a morphism of complex
projective varieties with `X` normal and `ℚ`-factorial, `K` a canonical divisor of `X`, and
`B, C ≥ 0` real divisors with `(X, B + C)` dlt, such that `B ≥ A` for an effective ample
`ℚ`-divisor `A` having no component in `⌊B + C⌋`. Let `X_i ⟶ Z_i ⟵ X_{i+1}` (`i < n`) be a
sequence of `(K_{X_i} + B_i)`-flips over `Z` with scaling of `C` at level one: each step is an
`IsRealFlipStep` for `B_i`, `C_{i+1}` is the strict transform of `C_i`,
`K_{X_i} + B_i + C_i` is numerically trivial over `Z_i`, and `1` is the least `t ≥ 0` for which
`K_{X_i} + B_i + t C_i` is nef over `Z`. Then there are effective `B̃, C̃` with `(X, B̃ + C̃)` klt
and `B̃ ≥ A'` for an effective ample `ℚ`-divisor `A'`, whose strict transforms `B̃_i, C̃_i` make
the same diagrams a sequence of `(K_{X_i} + B̃_i)`-flips over `Z` with scaling of `C̃` at level
one, with every `(X_i, B̃_i + C̃_i)`, `i ≤ n`, klt. -/
@[mmp "lem_fourfold_constant_dlt_level_klt_perturbation"]
public theorem IsRealDltPair.exists_isRealKltPair_isRealFlipStep_scaling_threshold_one
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {π : X ⟶ Z} (hπ : π ≫ sZ = sX)
    (hXq : IsQFactorial sX) {d : ℕ} (hd : topologicalKrullDim X = d) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX d)
    {B C : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hdlt : IsRealDltPair sX (B + C))
    {A : QDivisor X} (hA0 : ∀ P, 0 ≤ A.coeff P) (hA : A.IsAmple)
    (hAB : ∀ P, (A.coeff P : ℝ) ≤ B.coeff P) (hAfloor : ∀ P, A.coeff P ≠ 0 → (B + C).coeff P < 1)
    -- the sequence of flips
    {n : ℕ∞} {Y : ℕ → Scheme.{0}} {sY : ∀ i, Y i ⟶ Spec (.of ℂ)} [∀ i, IsIntegral (Y i)]
    [∀ i, CompactSpace (Y i)] [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    {πY : ∀ i, Y i ⟶ Z} {KY : ∀ i, Divisor (Y i)} {BY CY : ∀ i, RDivisor (Y i)}
    {W : ℕ → Scheme.{0}} {sW : ∀ i, W i ⟶ Spec (.of ℂ)} {f : ∀ i, modelSeq X Y i ⟶ W i}
    {fp : ∀ i, Y i ⟶ W i} {g : ∀ i, W i ⟶ Z}
    (hπY : ∀ i, πY i ≫ sZ = sY i)
    (hfg : ∀ i : ℕ, (i : ℕ∞) < n → f i ≫ g i = modelMap π πY i)
    (hfpg : ∀ i : ℕ, (i : ℕ∞) < n → fp i ≫ g i = πY i)
    (hYq : ∀ i : ℕ, (i : ℕ∞) ≤ n → IsQFactorial (modelStr sX sY i))
    (hstep : ∀ i : ℕ, (i : ℕ∞) < n →
      IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
        (KY i) (BY i) (f i) (fp i))
    (hCY : ∀ i : ℕ, (i : ℕ∞) < n → CY i = flipTransform (f i) (fp i) (divisorSeq C CY i))
    (hnull : ∀ i : ℕ, (i : ℕ∞) < n →
      MMP.Flips.IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
        (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + divisorSeq C CY i)))
    (hthr : ∀ i : ℕ, (i : ℕ∞) < n →
      IsLeast {t : ℝ | 0 ≤ t ∧ MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
        (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
          (divisorSeq B BY i + t • divisorSeq C CY i))} 1) :
    ∃ B' C' : RDivisor X, (∀ P, 0 ≤ B'.coeff P) ∧ (∀ P, 0 ≤ C'.coeff P) ∧
      IsRealKltPair sX (B' + C') ∧
      (∃ A' : QDivisor X, (∀ P, 0 ≤ A'.coeff P) ∧ A'.IsAmple ∧
        ∀ P, (A'.coeff P : ℝ) ≤ B'.coeff P) ∧
      ∃ BY' CY' : ∀ i, RDivisor (Y i),
        (∀ i : ℕ, (i : ℕ∞) < n →
          IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i)
            (divisorSeq B' BY' i) (KY i) (BY' i) (f i) (fp i) ∧
          CY' i = flipTransform (f i) (fp i) (divisorSeq C' CY' i) ∧
          MMP.Flips.IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
            (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
              (divisorSeq B' BY' i + divisorSeq C' CY' i)) ∧
          IsLeast {t : ℝ | 0 ≤ t ∧ MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY i)
            (modelMap π πY i) (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
              (divisorSeq B' BY' i + t • divisorSeq C' CY' i))} 1) ∧
        ∀ i : ℕ, (i : ℕ∞) ≤ n →
          IsRealKltPair (modelStr sX sY i) (divisorSeq B' BY' i + divisorSeq C' CY' i) := by
  classical
  have hXn : IsNormalVariety ℂ sX := hXq.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  have hlt_succ : ∀ i : ℕ, (i : ℕ∞) < n → ((i + 1 : ℕ) : ℕ∞) ≤ n := fun i hi =>
    Order.add_one_le_of_lt hi
  have hKs : ∀ i : ℕ, (i : ℕ∞) ≤ n →
      ∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i) := by
    intro i hi
    cases i with
    | zero => exact ⟨d, hK⟩
    | succ j =>
      exact (hstep j ((ENat.coe_lt_coe.mpr (Nat.lt_succ_self j)).trans_le
        hi)).isCanonicalDivisor_flip
  obtain ⟨ψ, c, hB'0, hklt0, hA'⟩ :=
    exists_isRealKltPair_add_smul_principalDivisor hX hXq hB hC hdlt hA0 hA hAB hAfloor
  have hprinc := exists_transformSeq_principalDivisor_eq hstep ψ
  set ε : ℝ := 1 / 2 with hεdef
  have hε0 : 0 < ε := by norm_num [hεdef]
  have hε1 : ε < 1 := by norm_num [hεdef]
  set G : Divisor X := principalDivisor ψ
  set B' : RDivisor X := B + ε • C + c • Divisor.toRDivisor G
  set C' : RDivisor X := (1 - ε) • C with hC'def
  have hC'0 : ∀ P, 0 ≤ C'.coeff P := fun P => by
    rw [hC'def, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    exact mul_nonneg (by linarith) (hC P)
  -- the strict transforms of `div ψ` are principal on every model
  set Gs := transformSeq f fp G
  have hGs : ∀ i, Gs (i + 1) = flipTransform (f i) (fp i) (Gs i) := fun i => rfl
  set BY' : ∀ i, RDivisor (Y i) := fun i =>
    BY i + ε • CY i + c • Divisor.toRDivisor (X := Y i) (Gs (i + 1))
  set CY' : ∀ i, RDivisor (Y i) := fun i => (1 - ε) • CY i
  have hBs : ∀ i, divisorSeq B' BY' i =
      divisorSeq B BY i + ε • divisorSeq C CY i + c • Divisor.toRDivisor (Gs i) := by
    intro i; cases i <;> rfl
  have hCs : ∀ i, divisorSeq C' CY' i = (1 - ε) • divisorSeq C CY i := by
    intro i; cases i <;> rfl
  -- every diagram is again a flip with scaling at level one
  have hnew : ∀ i : ℕ, (i : ℕ∞) < n →
      IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i)
        (divisorSeq B' BY' i) (KY i) (BY' i) (f i) (fp i) ∧
      CY' i = flipTransform (f i) (fp i) (divisorSeq C' CY' i) ∧
      MMP.Flips.IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
        (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
          (divisorSeq B' BY' i + divisorSeq C' CY' i)) ∧
      IsLeast {t : ℝ | 0 ≤ t ∧ MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY i)
        (modelMap π πY i) (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
          (divisorSeq B' BY' i + t • divisorSeq C' CY' i))} 1 := by
    intro i hi
    obtain ⟨φ, hφ⟩ := hprinc i hi.le
    obtain ⟨φ', hφ'⟩ : ∃ φ' : (RationalFunctions (Y i))ˣ, Gs (i + 1) = principalDivisor φ' :=
      hprinc (i + 1) (hlt_succ i hi)
    have hBYi : BY' i = BY i + ε • CY i + c • Divisor.toRDivisor (principalDivisor φ') := by
      change BY i + ε • CY i + c • Divisor.toRDivisor (X := Y i) (Gs (i + 1)) = _
      rw [← hφ']
    rw [hBs i, hCs i, hφ, hBYi]
    exact isRealFlipStep_perturb (hstep i hi) (hKs i hi.le) (hYq i hi.le)
      (hYq (i + 1) (hlt_succ i hi)) (hCY i hi) (hnull i hi) (hthr i hi) φ φ'
      (by rw [← hφ, ← hφ', hGs]) hε0 hε1 c
  refine ⟨B', C', hB'0, hC'0, hklt0, hA', BY', CY', hnew, ?_⟩
  intro i
  induction i with
  | zero =>
    intro _
    exact hklt0
  | succ i ih =>
    intro hi
    have hi' : (i : ℕ∞) < n := (ENat.coe_lt_coe.mpr (Nat.lt_succ_self i)).trans_le hi
    obtain ⟨h1, h2, h3, -⟩ := hnew i hi'
    have hk := isRealKltPair_flipTransform h1 (hKs i hi'.le) (hYq i hi'.le) (hYq (i + 1) hi) h3
      (ih hi'.le)
    rw [map_add, ← h1.eq_flipTransform, ← h2] at hk
    exact hk

