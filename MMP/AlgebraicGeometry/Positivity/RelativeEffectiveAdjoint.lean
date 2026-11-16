module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import StacksFrontier.Topology.Sober.Generization
import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GraphLineProjectionFlat
import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Positivity.FreePencilCrepant
import MMP.AlgebraicGeometry.Intersection.ThreefoldEffectiveIntersection
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector

/-!
# Effective adjoints and an ample component over a birational base

Let `f : X ⟶ Z` be a projective birational morphism of normal projective complex varieties, with
`X` `ℚ`-factorial, and let `(X, B)` be a klt pair with `B` an effective `ℝ`-divisor. Then
`K_X + B` is numerically equivalent over `Z` to an effective `ℝ`-divisor `M`, and after adding an
effective `ℚ`-divisor `T_X ∼_ℚ f^*T`, pulled back from a `ℚ`-Cartier divisor `T` on `Z`, the
boundary `B + T_X` is still klt, still has `K_X + B + T_X ≡_Z M`, and contains an effective ample
`ℚ`-divisor `A` none of whose components lies in `Supp M`. The divisor `A` may be chosen general
with respect to any given log resolution of `(X, B + M)`: that resolution is still a log
resolution of `(X, B + M + A)`.

Since `f` is birational, every prime divisor of `X` maps to a non-generic point of `Z`, so the
pull-back `w₁` of a suitable effective Cartier divisor of `Z` is positive along every component
of `K_X + B`; `M = K_X + B + N w₁` is then effective and `M ≡_f K_X + B`, a pull-back having
degree zero on every curve contracted by `f`. The zero divisor is `f`-big, so relative Kodaira
decomposes `0 ∼_ℚ H + G - c f^*T₀` with `H` ample and `G ≥ 0`. Given a log resolution `π` of
`(X, B + M)`, a general member `H'` of a free multiple of `H` keeps `π` a log resolution and has
no component in `Supp (B + M)`; for `ε = 1/N` small, `(X, B + ε(H' + G))` is klt (Kollár–Mori
2.35, for a real boundary), and `T_X = ε(H' + G)`, `A = εH'` satisfy the assertions.

## Main results

* `MMP.Fourfold.exists_isRealKltPair_add_pullback_isAmple_le_of_isBirationalMorphism`.
* `MMP.Fourfold.isBirationalMorphism_toImage`: a birational morphism of integral schemes is
  birational onto its scheme-theoretic image.
* `MMP.Fourfold.isNumericallyEquivalentOver_add` and
  `MMP.Fourfold.isNumericallyTrivialOver_of_qLinearlyEquivalent_smul_weilDivisor`: a `ℚ`-divisor
  `ℚ`-linearly equivalent to a multiple of a pull-back from `Z` is numerically trivial over `f`.
* `MMP.Fourfold.isPullback_of_isWeilDivisorOfCartier`: the Weil divisor of a pulled-back Cartier
  divisor is the pull-back of its Weil divisor, and
  `MMP.Fourfold.eq_zero_of_isCartierIntersectionNumber_of_isPullback`: it has degree zero on every
  curve contracted by `f`.

## Implementation notes

The `ℚ`-Cartier divisor `T` on `Z` is written `c • T₀` with `c ∈ ℚ` and `T₀` a Cartier divisor on
`Z`, and `f^*T` is `c` times the Weil divisor of the Cartier pull-back of `T₀`
(`MMP.Intersection.IsPullback`, `MMP.Intersection.IsWeilDivisorOfCartier`), as in
`MMP.Mori.QDivisor.IsRelativelyBig.exists_qLinearlyEquivalent_add_sub_pullback`. The canonical
divisor `K_X` is a given Weil divisor `K` with `K.IsCanonicalDivisor sX n`. The condition
`A ⊄ Supp M` is stated componentwise: no prime component of `A` is a component of `M`. The
genericity of `A` on a log resolution `π` of `(X, B + M)` is stated as `π` being a log resolution
of `(X, B + M + A)` as well (`MMP.Mori.IsLogResolution`); the plain existence statement is given
separately so that it does not rest on the existence of log resolutions.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.35
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Divisor arithmetic -/

/-- A log resolution depends on the divisor only through its support. -/
private theorem isLogResolution_of_supp_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {D D' : RDivisor X} {g : Y ⟶ X} (h : MMP.Mori.IsLogResolution sX D g)
    (hDD' : D.supp = D'.supp) : MMP.Mori.IsLogResolution sX D' g :=
  ⟨h.toIsSmoothResolution, h.isPureCodimOne_exceptionalSet, hDD' ▸ h.isSNCSubset⟩

/-- Divisors with the same nonzero coefficients have the same support. -/
private theorem supp_congr {R : Type*} [Zero R] {X : Scheme.{u}} {D D' : DivisorWithCoeffs R X}
    (h : ∀ P, D.coeff P ≠ 0 ↔ D'.coeff P ≠ 0) : D.supp = D'.supp := by
  have : D.support = D'.support := by
    ext P
    simp only [Finsupp.mem_support_iff]
    exact h P
  unfold DivisorWithCoeffs.supp
  rw [this]

/-- Scaling a nonnegative summand by a positive factor does not change whether a sum of
nonnegative reals vanishes. -/
private theorem add_mul_ne_zero_iff {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    a + ε * b ≠ 0 ↔ a + b ≠ 0 := by
  rw [Ne, Ne, add_eq_zero_iff_of_nonneg ha (by positivity), add_eq_zero_iff_of_nonneg ha hb,
    mul_eq_zero, or_iff_right hε.ne']

section LogResolution

open TopologicalSpace MMP.Resolution

/-! ### Snc closed subsets are snc divisors -/

/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : MMP.Mori.PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rw [hPs]
        exact hxW
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-! ### Existence of log resolutions -/

/-- **Log resolutions exist** in characteristic zero: the snc-preserving log resolution of the
reduced divisor `Supp D` is a log resolution of `(X, D)`. -/
private theorem exists_isLogResolution_of_charZero {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (D : RDivisor X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), MMP.Mori.IsLogResolution sX D g := by
  obtain ⟨Y, f, hres, hpure, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX D.support
  have hYv : AlgebraicGeometry.IsVariety k (f ≫ sX) := hres.isVariety_source
  have : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (f ≫ sX) := hYv.toQuasiCompact
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : AlgebraicGeometry.IsNoetherian Y := {}
  have hsupp_eq : (D.supp : Set X) = D.support.sup fun E => (E.idealSheaf.support : Set X) := by
    rw [DivisorWithCoeffs.supp, Closeds.coe_finset_sup]
    rfl
  rw [← hsupp_eq] at hS
  refine ⟨Y, f, ⟨⟨hres.isProjective.isProper, hres.isBirationalMorphism, hres.isSmoothScheme⟩,
    hpure, isSNCSubset_of_isSNCClosedSubset _ ?_⟩⟩
  simpa using hS

end LogResolution

/-! ### Birationality onto the scheme-theoretic image -/

/-- A birational morphism of integral schemes, locally of finite type and quasi-compact, is
birational onto its scheme-theoretic image. -/
theorem isBirationalMorphism_toImage {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [LocallyOfFiniteType f] [QuasiCompact f] (hfb : IsBirationalMorphism f) :
    IsBirationalMorphism f.toImage := by
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Z) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hb (Or.inl ⟨inferInstance, inferInstance⟩)
  have hUV' : U ≤ f.toImage ⁻¹ᵁ (f.imageι ⁻¹ᵁ V) := by
    intro x hx
    change (f.toImage ≫ f.imageι) x ∈ V
    rw [Scheme.Hom.toImage_imageι]
    exact hUV hx
  have hcomp : f.toImage.resLE (f.imageι ⁻¹ᵁ V) U hUV' ≫
      f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl = f.resLE V U hUV := by
    rw [Scheme.Hom.resLE_comp_resLE]
    simp only [Scheme.Hom.toImage_imageι]
  have hmono : Mono (f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl) := inferInstance
  have hsplit : IsSplitEpi (f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl) :=
    ⟨⟨⟨inv (f.resLE V U hUV) ≫ f.toImage.resLE (f.imageι ⁻¹ᵁ V) U hUV', by
      rw [Category.assoc, hcomp, IsIso.inv_hom_id]⟩⟩⟩
  have hiso₂ : IsIso (f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl) := isIso_of_mono_of_isSplitEpi _
  have hiso₁ : IsIso (f.toImage.resLE (f.imageι ⁻¹ᵁ V) U hUV') := by
    have : IsIso (f.toImage.resLE (f.imageι ⁻¹ᵁ V) U hUV' ≫
        f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl) := by rw [hcomp]; exact hiso
    exact IsIso.of_isIso_comp_right _ (f.imageι.resLE V (f.imageι ⁻¹ᵁ V) le_rfl)
  obtain ⟨x, hx⟩ := hU.nonempty
  haveI : IrreducibleSpace f.image := by
    have h1 : IsIrreducible (Set.range f.toImage) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
    have h2 := h1.closure
    rw [f.toImage.denseRange.closure_range] at h2
    exact (irreducibleSpace_def _).mpr h2
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f.toImage U (f.imageι ⁻¹ᵁ V) ⟨x, hx⟩
    ⟨f.toImage x, hUV' hx⟩ hUV' hiso₁

section PositivePullback

/-- `weilDivisorEquivFinsupp (cartierWeilDivisor D)` is the Weil divisor of the Cartier divisor
`D`. -/
private lemma isWeilDivisorOfCartier_cartierWeilDivisor {S : Scheme.{u}} [IsIntegral S]
    [IsNoetherian S] (D : S.CartierDivisor) :
    MMP.Intersection.IsWeilDivisorOfCartier D (weilDivisorEquivFinsupp (cartierWeilDivisor D)) := by
  intro P
  have hcoh : Order.coheight (MMP.Mori.PrimeDivisor.genericPoint P) = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  haveI : Ring.KrullDimLE 1
      (S.presheaf.stalk (MMP.Intersection.primeDivisorSubvariety P).genericPoint) :=
    krullDimLE_of_coheight_le hcoh.le
  obtain ⟨N, hN⟩ :=
    MMP.Intersection.exists_isOrderAlong D (MMP.Intersection.primeDivisorSubvariety P)
  convert hN using 1
  have hN' := hN
  unfold MMP.Intersection.IsOrderAlong at hN'
  dsimp only [MMP.Intersection.primeDivisorSubvariety_genericPoint] at hN'
  obtain ⟨a, b, ha, hb, ⟨g, hg, hgab⟩, la, lb, hla, hlb, rfl⟩ := hN'
  change cartierMultiplicity D (MMP.Mori.PrimeDivisor.genericPoint P) = _
  rw [MMP.Intersection.cartierMultiplicity_eq_ord_of_isLocalEquationAt hg]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (S.presheaf.stalk _) S.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : totalQuotientStalkToFunctionField _ g *
      algebraMap (S.presheaf.stalk _) S.functionField b =
      algebraMap (S.presheaf.stalk _) S.functionField a := by
    have := congrArg (totalQuotientStalkToFunctionField _) hgab.2
    rw [map_mul, MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    rw [mul_comm]
    exact this
  have hTg := MMP.Intersection.totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg
  have hord := S.ord_mul (x := MMP.Mori.PrimeDivisor.genericPoint P) hTg hbK
  rw [key, ord_algebraMap_stalk _ hcoh a ha0, ord_algebraMap_stalk _ hcoh b hb0] at hord
  erw [hla, hlb, ENat.toNat_coe, ENat.toNat_coe] at hord
  omega

/-- Key local computation: for an effective `T₀` and a pull-back `T₀'`, the order of `T₀'` along
a prime divisor is a natural number, positive when the image of its generic point lies in
`Supp T₀`. -/
private lemma exists_order_of_isPullback {Y S : Scheme.{u}} [IsIntegral Y]
    {f : Y ⟶ S} {T₀ : S.CartierDivisor} {T₀' : Y.CartierDivisor}
    (hT₀ : MMP.Intersection.IsEffective T₀) (hpb : MMP.Intersection.IsPullback f T₀ T₀')
    (P : MMP.Mori.PrimeDivisor Y) {N : ℤ}
    (hN : MMP.Intersection.IsOrderAlong T₀' (MMP.Intersection.primeDivisorSubvariety P) N) :
    ∃ n : ℕ, N = n ∧ (f P.genericPoint ∈ MMP.Intersection.cartierSupport T₀ → 1 ≤ n) := by
  set y := P.genericPoint with hy
  obtain ⟨U, hvU, s, hs, hsD⟩ := hT₀ (f y)
  set a : S.presheaf.stalk (f y) := S.presheaf.germ U (f y) hvU s with ha
  have hg : MMP.Intersection.IsLocalEquationAt T₀ (f y)
      (MMP.Intersection.stalkToTotalQuotient _ a) :=
    ⟨U, hvU, hs.unit, hsD, MMP.Intersection.germ_toTotalQuotient hvU s⟩
  have hab : MMP.Intersection.IsFraction (MMP.Intersection.stalkToTotalQuotient _ a) a 1 :=
    ⟨by rw [map_one]; exact isUnit_one, by rw [map_one, one_mul]⟩
  have h' : MMP.Intersection.IsFraction
      (MMP.Intersection.stalkToTotalQuotient y (f.stalkMap y a)) (f.stalkMap y a)
      (f.stalkMap y 1) :=
    ⟨by rw [map_one, map_one]; exact isUnit_one, by rw [map_one, map_one, one_mul]⟩
  have hloc := hpb.isLocalEquationAt hg hab h'
  obtain ⟨n, hn, rfl⟩ := hN.eq_length (V := MMP.Intersection.primeDivisorSubvariety P) hloc
  refine ⟨n, rfl, fun hsupp => ?_⟩
  have hna : ¬ IsUnit a := by
    intro hu
    apply MMP.Intersection.notMem_cartierSupport_of_isLocalEquationAt_one _ hsupp
    have h1 := hg.mul_units hu.unit⁻¹
    have e : MMP.Intersection.stalkToTotalQuotient _ a *
        MMP.Intersection.stalkToTotalQuotient _ ((hu.unit⁻¹ : (S.presheaf.stalk (f y))ˣ) :
          S.presheaf.stalk (f y)) = 1 := by
      rw [← map_mul]
      have : a * ((hu.unit⁻¹ : (S.presheaf.stalk (f y))ˣ) : S.presheaf.stalk (f y)) = 1 := by
        simp
      rw [this, map_one]
    rwa [e] at h1
  have hnu : ¬ IsUnit (f.stalkMap y a) := fun hu => hna (isUnit_of_map_unit (f.stalkMap y).hom a hu)
  by_contra hlt
  have h0 : n = 0 := by omega
  subst h0
  apply hnu
  have hsub := Module.length_eq_zero_iff.1 (by exact_mod_cast hn)
  exact (Ideal.span_singleton_eq_top).1 (Ideal.Quotient.subsingleton_iff.1 hsub)

/-- Pole-clearing step: for finitely many prime divisors of `Y` that are vertical over `S`,
there is a Cartier divisor `T₀` on `S` with a pull-back `T₀'` whose Weil divisor is effective and
positive along each of them. -/
private theorem exists_weilPullback_pos_of_vertical
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {Y S : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sS]
    [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (f : Y ⟶ S)
    (s : Finset (MMP.Mori.PrimeDivisor Y))
    (hs : ∀ P ∈ s, f P.genericPoint ≠ f (genericPoint Y)) :
    ∃ (T₀ : S.CartierDivisor) (T₀' : Y.CartierDivisor) (w : Divisor Y),
      MMP.Intersection.IsPullback f T₀ T₀' ∧ MMP.Intersection.IsWeilDivisorOfCartier T₀' w ∧
      w.IsEffective ∧ ∀ P ∈ s, 0 < w.coeff P := by
  letI : IsNoetherian Y := ⟨⟩
  haveI hSln : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian sS
  have hSv : MMP.Mori.IsVariety k sS := inferInstance
  have hSq : Stacks.HProjective.IsHQuasiProjective sS :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sS).isProjective.isHQuasiProjective
  set T : Set S := ⋃ P ∈ s, closure {f P.genericPoint} with hT
  have hTc : IsClosed T := s.finite_toSet.isClosed_biUnion fun P _ => isClosed_closure
  have hy₀ : f (genericPoint Y) ∈ Tᶜ := by
    intro h
    obtain ⟨P, hP, hmem⟩ := Set.mem_iUnion₂.1 h
    apply hs P hP
    have h1 : f P.genericPoint ⤳ f (genericPoint Y) := specializes_iff_mem_closure.2 hmem
    have h2 : f (genericPoint Y) ⤳ f P.genericPoint :=
      ((genericPoint_specializes P.genericPoint)).map f.continuous
    exact (h1.antisymm h2).eq
  obtain ⟨T₀, hT₀e, hTs, hy₀s⟩ :=
    MMP.Threefold.Resolution.exists_isEffective_subset_cartierSupport_of_notMem hSv hSq hTc hy₀
  have hpc : MMP.Intersection.PullbackCondition f T₀ := by
    intro η hη
    have hass : Stacks.Divisors.schemeAssociatedPoints Y = {genericPoint Y} :=
      calc Stacks.Divisors.schemeAssociatedPoints Y
          = Stacks.Divisors.schemeWeaklyAssociatedPoints Y :=
            AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints Y _
        _ = genericPoints Y := AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints Y
        _ = {genericPoint Y} := genericPoints_eq_singleton
    rw [hass] at hη
    rw [Set.mem_singleton_iff.1 hη]
    exact hy₀s
  obtain ⟨T₀', hpb⟩ := MMP.Intersection.exists_isPullback hpc
  have hw := isWeilDivisorOfCartier_cartierWeilDivisor T₀'
  refine ⟨T₀, T₀', _, hpb, hw, fun P => ?_, fun P hP => ?_⟩
  · obtain ⟨n, hn, -⟩ := exists_order_of_isPullback hT₀e hpb P (hw P)
    show 0 ≤ _
    rw [hn]; exact Int.natCast_nonneg n
  · obtain ⟨n, hn, h1⟩ := exists_order_of_isPullback hT₀e hpb P (hw P)
    have hmem : f P.genericPoint ∈ MMP.Intersection.cartierSupport T₀ :=
      hTs (Set.mem_iUnion₂.2 ⟨P, hP, subset_closure rfl⟩)
    have := h1 hmem
    show 0 < _
    rw [hn]; exact_mod_cast this

end PositivePullback

section Numerics

open MMP.Intersection

/-- The images in `K(X)` of the germs of a section of `𝓜_X` agree at all points. -/
private theorem totalQuotientStalkToFunctionField_germ {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {U : X.Opens} (s : X.totalQuotientSheaf.obj.obj (Opposite.op U))
    {x : X} (hx : x ∈ U) :
    totalQuotientStalkToFunctionField x (X.totalQuotientSheaf.presheaf.germ U x hx s) =
      totalQuotientStalkToFunctionField (genericPoint X)
        (X.totalQuotientSheaf.presheaf.germ U (genericPoint X)
          (((genericPoint_spec X).specializes trivial : genericPoint X ⤳ x).mem_open U.isOpen hx)
          s) := by
  have h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  rw [← totalQuotientStalkToFunctionField_stalkSpecializes h]
  congr 1
  exact ConcreteCategory.congr_hom
    (TopCat.Presheaf.germ_stalkSpecializes X.totalQuotientSheaf.presheaf hx h) s

/-- The order along a prime divisor `E` of `Y` of the pull-back `f^*_i φ` of a local equation
`φ` is the order of `f^*φ ∈ k(Y)` at the generic point of `E`. -/
private theorem ordUnit_pullbackComponent_eq_ord {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} [IsDominant f] {C : Divisor X}
    (hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp) {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : C.IsLocalEquation U φ) (E : MMP.Mori.PrimeDivisor Y)
    (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty) (Z : irreducibleComponents X) :
    E.ordUnit (pullbackComponent f hC hφ E.component (E.map_componentGenericPoint_mem f hE)) =
      Y.ord (functionFieldMap f
        (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))) E.genericPoint := by
  classical
  have hZp := E.map_componentGenericPoint_mem f hE
  have hW := mem_pointComponent (f (componentGenericPoint Y E.component))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZp (hC _) hW
  rw [pullbackComponent_eq hC hφ hZp hW a ha]
  set u := Units.map (f.stalkMap (componentGenericPoint Y E.component)).hom.toMonoidHom a
  let ψ : (RationalFunctions Y)ˣ :=
    (RationalFunctions.unitsEquiv Y).symm (Function.update 1 E.component u)
  have hψZ : (ψ : RationalFunctions Y) E.component = u := by
    simp [ψ, RationalFunctions.unitsEquiv]
  have h1 : E.ordUnit u = E.ord ψ := by
    rw [PrimeDivisor.ord_eq_ordUnit]
    congr 1
    exact (Units.ext hψZ).symm
  rw [h1, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  congr 1
  obtain rfl : Z = pointComponent (f (componentGenericPoint Y E.component)) :=
    Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
  change (Y.presheaf.stalkSpecializes _).hom ((ψ : RationalFunctions Y) E.component) =
    functionFieldMap f ((X.presheaf.stalkSpecializes _).hom
      ((φ : RationalFunctions X) _))
  rw [hψZ, ← ha]
  change _ = functionFieldMap f ((stalkToRationalFunctions X hW ≫
    X.presheaf.stalkSpecializes _).hom a)
  rw [stalkToRationalFunctions, TopCat.Presheaf.stalkSpecializes_comp]
  exact (functionFieldMap_algebraMap_stalk f (componentGenericPoint Y E.component) a.val).symm

/-- **The Weil divisor of a pulled-back Cartier divisor is the pull-back of the Weil divisor.**
If `w₀ = [T₀]` on a normal integral `Z` and `w = [T₀']` for a pull-back `T₀'` of `T₀` along a
dominant `f : X ⟶ Z` from a normal integral `X`, then `w = f^*w₀`. -/
theorem isPullback_of_isWeilDivisorOfCartier {X Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (f : X ⟶ Z) [IsDominant f] {T₀ : Z.CartierDivisor} {T₀' : X.CartierDivisor}
    {w₀ : Divisor Z} {w : Divisor X} (hw₀ : IsWeilDivisorOfCartier T₀ w₀)
    (hT : IsPullback f T₀ T₀') (hw : IsWeilDivisorOfCartier T₀' w)
    (hB : ∀ Z' : irreducibleComponents X, f (componentGenericPoint X Z') ∉ w₀.supp) :
    w₀.IsPullback f hB w := by
  classical
  refine Divisor.IsPullback.of_forall_exists fun E => ?_
  set y := E.genericPoint with hy
  obtain ⟨a, b, ⟨g, hg, hab⟩, ha', hb', g', hg', hab'⟩ := hT.2 y
  obtain ⟨U₁, hz, g₁, hloc, hgerm⟩ := hg
  have hĝ0 : totalQuotientStalkToFunctionField (f y) g ≠ 0 :=
    totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt ⟨U₁, hz, g₁, hloc, hgerm⟩
  set ĝ := totalQuotientStalkToFunctionField (f y) g with hĝ
  set φ : (RationalFunctions Z)ˣ := Units.map functionFieldToRationalFunctions.toMonoidHom
    (Units.mk0 ĝ hĝ0) with hφdef
  have hevalφ : ∀ Z' : irreducibleComponents Z,
      MMP.Threefold.Mori.Helpers.evalFF Z' (φ : RationalFunctions Z) = ĝ := fun Z' => by
    simp [hφdef]
  have hφ : w₀.IsLocalEquation U₁ φ := by
    intro P hP
    have hηP : P.genericPoint ∈ U₁ := (P.genericPoint_mem_iff U₁).mpr hP
    have hlocP : IsLocalEquationAt T₀ P.genericPoint
        (Z.totalQuotientSheaf.presheaf.germ U₁ P.genericPoint hηP (g₁ : _)) :=
      ⟨U₁, hηP, g₁, hloc, rfl⟩
    rw [← ord_eq_coeff_of_isLocalEquationAt hw₀ P rfl hlocP,
      MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hevalφ, hĝ, ← hgerm,
      totalQuotientStalkToFunctionField_germ (g₁ : _) hηP,
      totalQuotientStalkToFunctionField_germ (g₁ : _) hz]
  have hE : (E.support ∩ f ⁻¹ᵁ U₁).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U₁)).mp hz
  refine ⟨U₁, φ, hφ, hE, ?_⟩
  have Z₀ : irreducibleComponents Z := ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩
  rw [ordUnit_pullbackComponent_eq_ord hB hφ E hE Z₀, hevalφ,
    ← ord_eq_coeff_of_isLocalEquationAt hw E rfl hg']
  congr 1
  -- `f^*ĝ` is the image of the local equation `f^♯a / f^♯b` of `T₀'` at `y`
  have h1 : ĝ * algebraMap (Z.presheaf.stalk (f y)) Z.functionField b =
      algebraMap (Z.presheaf.stalk (f y)) Z.functionField a := by
    have := congrArg (totalQuotientStalkToFunctionField (f y)) hab.2
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    rw [mul_comm]; exact this
  have h2 : totalQuotientStalkToFunctionField y g' *
      algebraMap (X.presheaf.stalk y) X.functionField ((f.stalkMap y).hom b) =
      algebraMap (X.presheaf.stalk y) X.functionField ((f.stalkMap y).hom a) := by
    have := congrArg (totalQuotientStalkToFunctionField y) hab'.2
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    rw [mul_comm]; exact this
  have hb0 : algebraMap (X.presheaf.stalk y) X.functionField ((f.stalkMap y).hom b) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb'
  have h3 := congrArg (functionFieldMap f) h1
  rw [map_mul, functionFieldMap_algebraMap_stalk, functionFieldMap_algebraMap_stalk] at h3
  rw [← h2] at h3
  exact (mul_right_cancel₀ hb0 h3).symm

section Degree

open MMP.Flips

variable {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem ProperCurve.not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem ProperCurve.isCurve_comp (C : ProperCurve sX) {C' : Scheme} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine ProperCurve.not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := ProperCurve.isCurve_comp C hν hdim
  have hc2 := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (ProperCurve.not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- A principal divisor has intersection number zero with every proper curve. -/
private theorem IsCartierIntersectionNumber.eq_zero_of_principalDivisor [IsIntegral X]
    [CompactSpace X] {C : ProperCurve sX} (φ : (RationalFunctions X)ˣ)
    {h : (MMP.Mori.principalDivisor φ).IsCartier}
    {d : ℤ} (hd : IsCartierIntersectionNumber k sX C (MMP.Mori.principalDivisor φ) h d) :
    d = 0 := by
  rw [eq_degreeOn_of_isCartierIntersectionNumber hd]
  exact Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le h
    ⟨φ, by rw [sub_zero]⟩

end Degree

section DegreePullback

open MMP.Flips

/-- The Weil divisor of the pull-back of a Cartier divisor of a normal variety `Z` has degree
zero on every curve contracted by `f`. -/
theorem eq_zero_of_isCartierIntersectionNumber_of_isPullback {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sX]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsSeparated sZ]
    [LocallyOfFiniteType sZ] [QuasiCompact sZ] [IsIntegral Z] [IsNormal Z]
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) [IsDominant f]
    {T₀ : Z.CartierDivisor} {T₀' : X.CartierDivisor} {w₀ : Divisor Z} {w : Divisor X}
    (hw₀ : IsWeilDivisorOfCartier T₀ w₀) (hT : IsPullback f T₀ T₀')
    (hw : IsWeilDivisorOfCartier T₀' w) (hwc : w.IsCartier)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) {d : ℤ}
    (hd : IsCartierIntersectionNumber k sX C w hwc d) : d = 0 := by
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hw₀c : w₀.IsCartier := hw₀.isCartier
  have hB : ∀ Z' : irreducibleComponents X, f (componentGenericPoint X Z') ∉ w₀.supp :=
    MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f w₀
  have hpb := isPullback_of_isWeilDivisorOfCartier f hw₀ hT hw hB
  obtain rfl := hpb.pullback_eq hw₀c
  rw [eq_degreeOn_of_isCartierIntersectionNumber hd]
  exact Divisor.degreeOn_pullback_eq_zero_of_isContractedBy f hf hw₀c hB C hC

end DegreePullback

open MMP.Flips in
/-- A real divisor on a scheme on which every Weil divisor has a Cartier multiple is a real
combination of Cartier divisors. -/
private theorem isCartierCombination_of_forall {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier)
    (D : RDivisor X) : IsCartierCombination D := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  | add D₁ D₂ h₁ h₂ =>
    obtain ⟨m₁, r₁, L₁, hL₁, rfl⟩ := h₁
    obtain ⟨m₂, r₂, L₂, hL₂, rfl⟩ := h₂
    refine ⟨m₁ + m₂, Fin.append r₁ r₂, Fin.append L₁ L₂, fun j => ?_, ?_⟩
    · refine Fin.addCases (motive := fun j => (Fin.append L₁ L₂ j).IsCartier)
        (fun i => by simpa using hL₁ i) (fun i => by simpa using hL₂ i) j
    · rw [Fin.sum_univ_add]
      simp
  | single P r =>
    obtain ⟨m, hm, hmc⟩ := hQ (Finsupp.single P 1)
    refine ⟨1, fun _ => r / m, fun _ => (m : ℤ) • Finsupp.single P 1, fun _ => hmc, ?_⟩
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    ext Q
    simp only [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    change (Finsupp.single P r) Q = r / m * ((((m : ℤ) • Finsupp.single P (1 : ℤ)) Q : ℤ) : ℝ)
    by_cases hPQ : P = Q
    · subst hPQ
      simp [Finsupp.single_apply]
      field_simp
    · simp [Finsupp.single_apply, hPQ]

open MMP.Flips in
/-- `N₁ ≡_f N₂` when `N₁ - N₂` is a real combination of Cartier divisors of degree zero on the
curves contracted by `f`. -/
private theorem isNumericallyEquivalentOver_of_eq_add_sum {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] (f : X ⟶ Y) {N₁ N₂ : RDivisor X} (h₁ : IsCartierCombination N₁)
    (h₂ : IsCartierCombination N₂) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier)
    (h0 : ∀ j, ∀ C : ProperCurve sX, C.IsContractedBy f → ∀ d : ℤ,
      IsCartierIntersectionNumber k sX C (L j) (hL j) d → d = 0)
    (h : N₁ = N₂ + ∑ j, r j • Divisor.toRDivisor (L j)) :
    IsNumericallyEquivalentOver k sX f N₁ N₂ := by
  refine ⟨h₁, h₂, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ hx₁ hx₂ => ?_⟩
  -- a normalization of `C`, read off from one of the two presentations
  by_cases hm : m₁ = 0 ∧ m₂ = 0
  · obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨-, -, -, -, rfl⟩ := hx₁
    obtain ⟨-, -, -, -, rfl⟩ := hx₂
    simp
  have hν : ∃ (C' : Scheme.{u}) (ν : C' ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim C' ≤ 1 := by
    rcases not_and_or.mp hm with h1 | h2
    · obtain ⟨_, _, _, hd, _⟩ := hx₁
      obtain ⟨C', ν, hν, hdim, -⟩ := hd ⟨0, Nat.pos_of_ne_zero h1⟩
      exact ⟨C', ν, hν, hdim⟩
    · obtain ⟨_, _, _, hd, _⟩ := hx₂
      obtain ⟨C', ν, hν, hdim, -⟩ := hd ⟨0, Nat.pos_of_ne_zero h2⟩
      exact ⟨C', ν, hν, hdim⟩
  obtain ⟨C', ν, hν', hdim⟩ := hν
  have := hν'.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have hICN : ∀ j, IsCartierIntersectionNumber k sX C (L j) (hL j)
      ((L j).degreeOn k sX (ν ≫ C.ι) hdim (hL j)) := fun j => ⟨C', ν, hν', hdim, rfl⟩
  have hT : IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C 0 :=
    ⟨hL, fun j => (L j).degreeOn k sX (ν ≫ C.ι) hdim (hL j), rfl, hICN, by
      simp [h0 _ C hC _ (hICN _)]⟩
  have hsum := (IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ 1 1 hx₂ hT
  rw [one_smul, one_smul, ← h, one_mul, one_mul, add_zero] at hsum
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx₁ hsum

end Numerics

section RealKlt

section Aff

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **Log discrepancies are affine in the boundary.** If every Weil divisor on `X` has a Cartier
multiple, then for a log discrepancy `a = a(E, X, B)` and a finite set `S` of prime divisors there
are numbers `μ_P ≥ 0` (the coefficients along `E` of the pull-backs of `P`) such that
`a(E, X, B + ∑_{P ∈ S} β_P P) = a - ∑_{P ∈ S} β_P μ_P` for all real `β`. -/
private theorem exists_isLogDiscrepancy_add_sum
    (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier) {n : ℕ} {B : RDivisor X}
    {E : DivisorOver k sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B E a)
    (S : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ μ : MMP.Mori.PrimeDivisor X → ℝ, (∀ P, 0 ≤ μ P) ∧ ∀ β : MMP.Mori.PrimeDivisor X → ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n (B + ∑ P ∈ S, Finsupp.single P (β P)) E
        (a - ∑ P ∈ S, β P * μ P) := by
  classical
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isIntegral
  have := E.isBirationalMorphism.isDominant
  have : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨hnv, hprop, ω, hω0, hK, m, r, C, C', hC, hrel, hpb, ha⟩ := h
  choose mP hmP hmPc using fun P : MMP.Mori.PrimeDivisor X => hQ (Finsupp.single P 1)
  choose CP hCP using fun P : MMP.Mori.PrimeDivisor X =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hmPc P)
  have hnn : ∀ P, 0 ≤ (CP P).coeff E.E := fun P => by
    refine MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) (hmPc P)
      (fun P' _ => ?_) (hCP P) E.E ((E.E.genericPoint_mem_iff _).mp trivial)
    change (0 : ℤ) ≤ ((mP P : ℤ) • Finsupp.single P (1 : ℤ)) P'
    rw [Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> simp
  refine ⟨fun P => ((CP P).coeff E.E : ℝ) / mP P, fun P => div_nonneg (by exact_mod_cast hnn P)
    (by positivity), fun β => ?_⟩
  set e := S.equivFin
  refine ⟨hnv, hprop, ω, hω0, hK, m + S.card,
    Fin.append r (fun j => β (e.symm j) / mP (e.symm j)),
    Fin.append C (fun j => (mP (e.symm j) : ℤ) • Finsupp.single (e.symm j).1 1),
    Fin.append C' (fun j => CP (e.symm j)), ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (motive := fun i => (Fin.append C _ i).IsCartier) (fun i => ?_)
      (fun i => ?_) i
    · simpa using hC i
    · simpa using hmPc (e.symm i)
  · intro Γ
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [DivisorWithCoeffs.coeff_add, ← add_assoc, hrel Γ]
    congr 1
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, ← Finset.sum_coe_sort S]
    refine Fintype.sum_equiv e
      (fun P : S => (Finsupp.single P.1 (β P)) Γ)
      (fun x => β (e.symm x) / mP (e.symm x) *
        ((DivisorWithCoeffs.coeff ((mP (e.symm x) : ℤ) • Finsupp.single (e.symm x).1 (1 : ℤ))
          Γ : ℤ) : ℝ)) (fun P => ?_)
    · simp only [Equiv.symm_apply_apply]
      have hm : (mP P : ℝ) ≠ 0 := by exact_mod_cast (hmP P).ne'
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply,
        Finsupp.single_apply, Finsupp.single_apply]
      split_ifs
      · simp only [smul_eq_mul, mul_one]
        push_cast; field_simp
      · simp
  · intro i
    refine Fin.addCases (motive := fun i => ∃ hC, (Fin.append C _ i).IsPullback E.f hC
      (Fin.append C' _ i)) (fun i => ?_) (fun i => ?_) i
    · simpa using hpb i
    · simp only [Fin.append_right]
      exact ⟨MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E.f _, hCP (e.symm i)⟩
  · rw [Fin.sum_univ_add, ha]
    simp only [Fin.append_left, Fin.append_right]
    have hre : ∑ x : Fin S.card, β (e.symm x) / mP (e.symm x) *
        ((DivisorWithCoeffs.coeff (CP (e.symm x)) E.E : ℤ) : ℝ) =
        ∑ P ∈ S, β P * (((CP P).coeff E.E : ℝ) / mP P) := by
      rw [← Finset.sum_coe_sort S]
      refine (Fintype.sum_equiv e _ _ fun P => ?_).symm
      simp only [Equiv.symm_apply_apply]
      ring
    rw [hre]
    ring

end Aff

section KLT

open TopologicalSpace

/-- A positive rational below the values of `g` on `s`, when those values are positive. -/
private theorem exists_pos_forall_le {α : Type*} (s : Finset α) (g : α → ℚ)
    (h : ∀ x ∈ s, 0 < g x) : ∃ ε : ℚ, 0 < ε ∧ ∀ x ∈ s, ε ≤ g x := by
  classical
  refine ⟨(insert 1 (s.image g)).min' (Finset.insert_nonempty _ _), ?_,
    fun x hx => Finset.min'_le _ _ (by simpa using Or.inr ⟨x, hx, rfl⟩)⟩
  simpa [Finset.lt_min'_iff] using h

/-- The existence of log discrepancies: if `K + B` is `ℝ`-Cartier, every divisor over `X` with a
proper model has a log discrepancy. -/
private theorem exists_isLogDiscrepancy {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : MMP.Fourfold.RDivisor.IsRCartier
      (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + B))
    (E : DivisorOver k sX) (hE : IsProper E.f) :
    ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n B E a := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hrel⟩ := hKB
  choose C' hC' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hC j)
  refine ⟨_, hX, hE, ω, hω0, ⟨K, hK, fun Γ => (hωK Γ).symm⟩, m, r, C, C', hC, fun Γ => ?_,
    fun j => ⟨_, hC' j⟩, rfl⟩
  rw [← hrel Γ, DivisorWithCoeffs.coeff_add, hωK Γ]
  rfl

open Classical in
/-- **Klt from one log resolution.** Let `(X, Δ)` be a pair with every coefficient `< 1`, and
`g : Y ⟶ X` a log resolution of an `ℝ`-divisor `R` whose support contains that of `Δ`. If every
prime divisor of `Y` has discrepancy `> -1`, then `(X, Δ)` is klt. -/
private theorem isKltPair_of_isLogResolution {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hP : IsPairWith sX n K Δ)
    (hΔ : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P < 1) {R : RDivisor X}
    (hR : ∀ P, Δ.coeff P ≠ 0 → R.coeff P ≠ 0) {Y : Scheme.{u}} {g : Y ⟶ X}
    (hg : MMP.Mori.IsLogResolution sX R g)
    (h : ∀ (hY : IsNormalVariety k (g ≫ sX)) (G : MMP.Mori.PrimeDivisor Y) (a : ℚ),
      IsDiscrepancy sX n K Δ ⟨Y, g, hY, hg.isBirationalMorphism, G⟩ a → -1 < a) :
    MMP.Mori.IsKltPair sX n K Δ := by
  have hX : IsNormalVariety k sX := hP.1
  obtain ⟨hY, hdimY, -⟩ := hg.toIsSmoothResolution.isNormalVariety hX
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType (g ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  have : IsNormal Y := hY.2
  have : IsProper g := hg.isProper
  have : MMP.Mori.IsVariety k sX := hX.1
  have : MMP.Mori.IsVariety k (g ≫ sX) := hY.1
  have : IsDominant g := hg.isBirationalMorphism.isDominant
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  set hgb := hg.isBirationalMorphism
  let DG : MMP.Mori.PrimeDivisor Y → DivisorOver k sX := fun G => ⟨Y, g, hY, hgb, G⟩
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (g ≫ sX) hg.isSmoothScheme
    (hdimY.trans hP.2.1.topologicalKrullDim_eq)
  obtain ⟨⟨Θ, hΘ, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP.isPair hP.2.1 g hY hgb
  have hθ : ∀ G, Θ.coeff G < 1 := fun G => by
    have := h hY G _ (hΘ G)
    linarith
  obtain ⟨S, hsncS, hmemS⟩ := MMP.Mori.exists_finset_isSNC hg.isSmoothScheme hg.isSNCSubset
  have hexcS : ∀ G : MMP.Mori.PrimeDivisor Y, (DG G).IsExceptional → G ∈ S := fun G hG =>
    hmemS G (Or.inl (MMP.Positivity.support_subset_exceptionalSet G hG
      (MMP.Flips.primeDivisor_genericPoint_mem_support G)))
  have hsuppS : ∀ G, Θ.coeff G ≠ 0 → G ∈ S := by
    intro G hG0
    by_cases hG : (DG G).IsExceptional
    · exact hexcS G hG
    obtain ⟨P, hc, hη, -⟩ := MMP.Mori.exists_coeff_eq_of_not_isExceptional hP hY hgb hΘ hG
    have hRP : R.coeff P ≠ 0 := hR P (hc ▸ hG0)
    refine hmemS G (Or.inr ?_)
    change g G.genericPoint ∈ R.supp
    rw [hη]
    exact DivisorWithCoeffs.support_subset_supp hRP
      (MMP.Flips.primeDivisor_genericPoint_mem_support P)
  have hsuppΘ : Θ.support ⊆ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support := by
    intro G hG
    have hGS := hsuppS G (Finsupp.mem_support_iff.mp hG)
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hGS]
  have hYklt := isKltPair_of_isSNC (g ≫ sX) hY hg.isSmoothScheme hKY
    (hsncS.of_support_subset hsuppΘ) hθ
  -- a uniform bound on the exceptional discrepancies
  obtain ⟨δ, hδ, hδS⟩ := exists_pos_forall_le S (fun G => 1 - Θ.coeff G)
    (fun G _ => by linarith [hθ G])
  refine ⟨hP, ?_, roundDown_nonpos_iff.mpr hΔ⟩
  rw [IsCrepantBoundary.discrep_eq_min hP.isPair hP.2.1 hKY hΘ]
  refine lt_min hYklt.2.1 (lt_of_lt_of_le (b := (((-1 + δ : ℚ) : ℝ) : EReal)) ?_ ?_)
  · have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
    have : ((-1 : ℝ) : EReal) < (((-1 + δ : ℚ) : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr (by push_cast; linarith)
    simpa using this
  · refine le_sInf ?_
    rintro _ ⟨E, a, hE, ha, rfl⟩
    have haE : a = -Θ.coeff E := ha.eq (hΘ E)
    have := hδS E (hexcS E hE)
    exact EReal.coe_le_coe_iff.mpr (by exact_mod_cast (show (-1 + δ : ℚ) ≤ a by rw [haE]; linarith))

/-- A rational number below finitely many positive reals. -/
private theorem exists_rat_pos_lt {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ i ∈ s, (δ : ℝ) < f i := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨i₀, hi₀, hmin⟩ := s.exists_min_image f hs
  obtain ⟨δ, h1, h2⟩ := exists_rat_btwn (hf i₀ hi₀)
  exact ⟨δ, by exact_mod_cast h1, fun i hi => h2.trans_le (hmin i hi)⟩

open Classical in
/-- The coefficients of `∑_{P ∈ S} single P (β P)`. -/
private theorem coeff_sum_single {R : Type*} [AddCommMonoid R] {X : Scheme.{u}}
    (S : Finset (MMP.Mori.PrimeDivisor X)) (β : MMP.Mori.PrimeDivisor X → R)
    (P : MMP.Mori.PrimeDivisor X) :
    DivisorWithCoeffs.coeff (∑ Q ∈ S, Finsupp.single Q (β Q) : DivisorWithCoeffs R X) P =
      if P ∈ S then β P else 0 := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

open Classical in
/-- **Kollár–Mori 2.35 for a real boundary.** If `(X, B)` is a real klt pair on a `ℚ`-factorial
variety and `D ≥ 0`, then `(X, B + D/N)` is klt for some `N > 0`. -/
private theorem exists_isRealKltPair_add_inv_smul_of {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hXQ : MMP.Fourfold.IsQFactorial sX)
    (hlr : ∀ D : RDivisor X, ∃ (Y : Scheme.{u}) (g : Y ⟶ X), MMP.Mori.IsLogResolution sX D g)
    (hRC : ∀ D : RDivisor X, MMP.Fourfold.RDivisor.IsRCartier D)
    {B : RDivisor X} (hB : B.IsEffective) (hBk : MMP.Fourfold.IsRealKltPair sX B)
    {D : QDivisor X} (hD : D.IsEffective) :
    ∃ N : ℕ, 0 < N ∧ MMP.Fourfold.IsRealKltPair sX (B + QDivisor.toRDivisor (((N : ℚ)⁻¹) • D)) := by
  have hX : IsNormalVariety k sX := hXQ.1
  have hQ := hXQ.2
  obtain ⟨-, hB1, ⟨n, K, hK, hKB⟩, hpos⟩ := hBk
  set SX : Finset (MMP.Mori.PrimeDivisor X) := B.support ∪ D.support with hSX
  set R : RDivisor X := ∑ P ∈ SX, Finsupp.single P (1 : ℝ) with hRdef
  obtain ⟨Y, g, hg⟩ := hlr R
  obtain ⟨hY, -, -⟩ := hg.toIsSmoothResolution.isNormalVariety hX
  have : LocallyOfFiniteType (g ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  obtain ⟨S, -, hmemS⟩ := MMP.Mori.exists_finset_isSNC hg.isSmoothScheme hg.isSNCSubset
  let DG : MMP.Mori.PrimeDivisor Y → DivisorOver k sX := fun G =>
    ⟨Y, g, hY, hg.isBirationalMorphism, G⟩
  choose aG haG using fun G => exists_isLogDiscrepancy hX hK hKB (DG G) hg.isProper
  choose μ hμ0 hμ using fun G => exists_isLogDiscrepancy_add_sum hQ (haG G) SX
  have haGpos : ∀ G, 0 < aG G := fun G => hpos n (DG G) _ (haG G)
  set c : MMP.Mori.PrimeDivisor Y → ℝ := fun G => ∑ P ∈ SX, (1 + (D.coeff P : ℝ)) * μ G P
  have hc0 : ∀ G, 0 ≤ c G := fun G => Finset.sum_nonneg fun P _ =>
    mul_nonneg (by have := hD P; positivity) (hμ0 G P)
  have hD0 : ∀ P, (0 : ℝ) ≤ D.coeff P := fun P => by exact_mod_cast hD P
  -- the radius `δ`
  obtain ⟨δ₁, hδ₁, hδ₁S⟩ := exists_rat_pos_lt S (fun G => aG G / (1 + c G))
    (fun G _ => div_pos (haGpos G) (by linarith [hc0 G]))
  obtain ⟨δ₂, hδ₂, hδ₂S⟩ := exists_rat_pos_lt SX (fun P => (1 - B.coeff P) / (1 + D.coeff P))
    (fun P _ => div_pos (by linarith [hB1 P]) (by linarith [hD0 P]))
  set δ : ℚ := min δ₁ δ₂ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hδG : ∀ G ∈ S, (δ : ℝ) * c G < aG G := by
    intro G hG
    have h1 := hδ₁S G hG
    have h2 : (δ : ℝ) ≤ δ₁ := by exact_mod_cast min_le_left _ _
    rw [lt_div_iff₀ (by linarith [hc0 G])] at h1
    nlinarith [hc0 G]
  have hδP : ∀ P ∈ SX, B.coeff P + δ * (1 + D.coeff P) < 1 := by
    intro P hP
    have h1 := hδ₂S P hP
    have h2 : (δ : ℝ) ≤ δ₂ := by exact_mod_cast min_le_right _ _
    rw [lt_div_iff₀ (by linarith [hD0 P])] at h1
    nlinarith [hD0 P]
  -- `ε = 1/N < δ`, and rational coefficients `q_P ∈ (B_P, B_P + δ)`
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℚ) < N := (one_div_pos.mpr hδ).trans hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  set ε : ℚ := (N : ℚ)⁻¹ with hεdef
  have hε0 : 0 < ε := inv_pos.mpr hNpos
  have hεδ : ε < δ := by
    rw [hεdef, inv_lt_comm₀ hNpos hδ, ← one_div]
    exact hN
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε0
  have hεδ' : (ε : ℝ) < δ := by exact_mod_cast hεδ
  choose q hq1 hq2 using fun P => exists_rat_btwn (show B.coeff P < B.coeff P + δ by linarith)
  set Ω' : QDivisor X := (∑ P ∈ SX, Finsupp.single P (q P)) + ε • D with hΩ'
  have hDSX : ∀ P, P ∉ SX → D.coeff P = 0 := fun P hP => by
    rw [DivisorWithCoeffs.coeff_apply]
    exact Finsupp.notMem_support_iff.mp fun h => hP (Finset.mem_union_right _ h)
  have hBSX : ∀ P, P ∉ SX → B.coeff P = 0 := fun P hP => by
    rw [DivisorWithCoeffs.coeff_apply]
    exact Finsupp.notMem_support_iff.mp fun h => hP (Finset.mem_union_left _ h)
  have hΩ'coeff : ∀ P, (Ω'.coeff P : ℝ) = if P ∈ SX then (q P : ℝ) + ε * D.coeff P else 0 := by
    intro P
    rw [hΩ', DivisorWithCoeffs.coeff_add, coeff_sum_single, DivisorWithCoeffs.coeff_smul]
    split_ifs with hP
    · rw [smul_eq_mul, Rat.cast_add, Rat.cast_mul]
    · rw [hDSX P hP]; simp
  have hΩ'lt : ∀ P, Ω'.coeff P < 1 := by
    intro P
    have h := hΩ'coeff P
    split_ifs at h with hP
    · have h1 := hq2 P
      have h2 := hδP P hP
      have h3 := hD0 P
      have : ((Ω'.coeff P : ℚ) : ℝ) < 1 := by
        rw [h]; nlinarith
      exact_mod_cast this
    · have : ((Ω'.coeff P : ℚ) : ℝ) < 1 := by rw [h]; norm_num
      exact_mod_cast this
  have hΩ'ge : ∀ P, B.coeff P + ε * D.coeff P ≤ Ω'.coeff P := by
    intro P
    rw [hΩ'coeff P]
    split_ifs with hP
    · linarith [hq1 P]
    · rw [hBSX P hP, hDSX P hP]; simp
  have hΩ'e : Ω'.IsEffective := fun P => by
    have := hΩ'ge P
    have h1 := hB P
    have : (0 : ℝ) ≤ Ω'.coeff P := by nlinarith [hD0 P]
    exact_mod_cast this
  -- `Ω'` is klt
  have hQc : (Divisor.toQDivisor K + Ω').IsQCartier :=
    MMP.Fourfold.isQCartier_of_isQFactorial sX hXQ _
  have hpairW : IsPairWith sX n K Ω' := ⟨hX, hK, hQc⟩
  -- the boundary `B + ∑ β_P P = Ω'`
  have hβ : B + ∑ P ∈ SX, Finsupp.single P ((Ω'.coeff P : ℝ) - B.coeff P) =
      QDivisor.toRDivisor Ω' := by
    ext P
    rw [DivisorWithCoeffs.coeff_add, coeff_sum_single, QDivisor.coeff_toRDivisor]
    split_ifs with hP
    · ring
    · rw [hBSX P hP, add_zero, hΩ'coeff P, if_neg hP]
  have hMori : MMP.Mori.IsKltPair sX n K Ω' := by
    refine isKltPair_of_isLogResolution hpairW hΩ'lt (R := R) (fun P hP => ?_) hg ?_
    · have hPS : P ∈ SX := by
        by_contra hP'
        apply hP
        exact_mod_cast (show ((Ω'.coeff P : ℚ) : ℝ) = 0 by rw [hΩ'coeff P, if_neg hP'])
      rw [hRdef, coeff_sum_single, if_pos hPS]
      exact one_ne_zero
    · intro hY' G a ha
      by_cases hG : (DG G).IsExceptional
      · have hGS : G ∈ S := hmemS G (Or.inl (MMP.Positivity.support_subset_exceptionalSet G hG
          (MMP.Flips.primeDivisor_genericPoint_mem_support G)))
        have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha
          hg.isProper
        have h2 := hμ G (fun P => (Ω'.coeff P : ℝ) - B.coeff P)
        rw [hβ] at h2
        have h3 := MMP.Threefold.Bridges.IsLogDiscrepancy.unique h1 h2
        have hsum : ∑ P ∈ SX, ((Ω'.coeff P : ℝ) - B.coeff P) * μ G P ≤ δ * c G := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun P hP => ?_
          have h4 : (Ω'.coeff P : ℝ) - B.coeff P ≤ δ * (1 + D.coeff P) := by
            rw [hΩ'coeff P, if_pos hP]
            nlinarith [hq2 P, hD0 P]
          have := hμ0 G P
          nlinarith
        have := hδG G hGS
        have h5 : (0 : ℝ) < 1 + (a : ℝ) := by linarith
        have : (-1 : ℝ) < a := by linarith
        exact_mod_cast this
      · obtain ⟨P, -, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hpairW _ hG
        have := ha.eq hd
        have h1 := hΩ'lt P
        rw [this]
        linarith
  have hpair : MMP.Fourfold.IsPair sX Ω' :=
    ⟨inferInstance, inferInstance, hpairW.isPair, hΩ'e⟩
  have hklt := (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK hpair).2 hMori
  refine ⟨N, hN0, hX, fun P => ?_, ⟨n, K, hK, hRC _⟩, fun n' E a h => ?_⟩
  · rw [DivisorWithCoeffs.coeff_add, QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul,
      smul_eq_mul]
    have := hΩ'ge P
    have h2 : ((Ω'.coeff P : ℚ) : ℝ) < 1 := by exact_mod_cast hΩ'lt P
    rw [Rat.cast_mul]
    linarith
  · obtain ⟨μ', hμ'0, hμ'⟩ := exists_isLogDiscrepancy_add_sum hQ h SX
    have h2 := hμ' (fun P => (Ω'.coeff P : ℝ) - (B.coeff P + ε * D.coeff P))
    have hβ' : B + QDivisor.toRDivisor (ε • D) + ∑ P ∈ SX,
        Finsupp.single P ((Ω'.coeff P : ℝ) - (B.coeff P + ε * D.coeff P)) =
        QDivisor.toRDivisor Ω' := by
      ext P
      rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, coeff_sum_single,
        QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul,
        smul_eq_mul]
      split_ifs with hP
      · push_cast; ring
      · rw [hBSX P hP, hDSX P hP, hΩ'coeff P, if_neg hP]; simp
    rw [hβ'] at h2
    have h3 := hklt.2 n' E _ h2
    have h4 : 0 ≤ ∑ P ∈ SX, ((Ω'.coeff P : ℝ) - (B.coeff P + ε * D.coeff P)) * μ' P :=
      Finset.sum_nonneg fun P _ => mul_nonneg (by linarith [hΩ'ge P]) (hμ'0 P)
    linarith

end KLT

end RealKlt

section Bertini

open TopologicalSpace

/-- The support of the reduced divisor `∑_{F ∈ S} F` is `S`. -/
private theorem support_sum_single {Y : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ F ∈ S, Finsupp.single F (1 : ℤ)).support = S := by
  classical
  ext F; simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- A general linear combination of finitely many sections, one of them nonzero, is nonzero:
the coefficient vectors `c` with `∑ cᵢ sᵢ = 0` form a proper subspace of `kⁱ`, contained in the
kernel of a linear form `ℓ` with `ℓ(e_j) ≠ 0`. -/
private theorem exists_polynomial_sum_smul_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤) (j : ι)
    (hj : s j ≠ 0) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0 := by
  classical
  let p : Submodule k (ι → k) :=
    { carrier := {c | ∑ i, scalarsToGlobalSections k sX (c i) • s i = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Pi.add_apply, map_add, add_smul,
          Finset.sum_add_distrib] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at *
        rw [← Finset.smul_sum, hc, smul_zero] }
  have hjp : (Pi.single j 1 : ι → k) ∉ p := by
    intro h
    apply hj
    have : ∑ i, scalarsToGlobalSections k sX ((Pi.single j 1 : ι → k) i) • s i = 0 := h
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp),
      Pi.single_eq_same, map_one, one_smul] at this
  obtain ⟨ℓ, hℓ, hp⟩ := Submodule.exists_le_ker_of_notMem hjp
  let Q : MvPolynomial ι k :=
    ∑ i, MvPolynomial.C (ℓ (fun j => if i = j then 1 else 0)) * MvPolynomial.X i
  have heval : ∀ c, MvPolynomial.eval c Q = ℓ c := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ ℓ c]
    simp [Q, MvPolynomial.eval_sum, mul_comm]
  refine ⟨Q, fun h => hℓ (by rw [← heval, h, map_zero]), fun c hc h0 => hc ?_⟩
  rw [heval]
  exact hp (show c ∈ p from h0)

section AmpleMultiples

variable {X : Scheme.{u}}

open Stacks.Ample Stacks.RelativeVeryAmple in
/-- `𝒪_X(E)^{⊗ n} ≅ 𝒪_X(n E)` for a Cartier divisor `E`. -/
private noncomputable def tensorPowDivisorialIso [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (E : Divisor X) (hE : E.IsCartier)
    [IsInvertibleModule X E.divisorialSheaf] :
    (n : ℕ) → tensorPowModule X E.divisorialSheaf (n : ℤ) ≅ (n • E).divisorialSheaf
  | 0 => tensorPowModuleZeroIso X E.divisorialSheaf ≪≫
      (eqToIso rfl : unitModule X ≅ MMP.Mori.structureSheafModule X) ≪≫
      (Divisor.divisorialSheafZeroIso (X := X)).symm ≪≫
      eqToIso (by rw [zero_nsmul])
  | (n + 1) =>
      tensorPowModuleCongr X E.divisorialSheaf
          (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring) ≪≫
        (tensorPowModuleAddIso X E.divisorialSheaf (n : ℤ) 1).symm ≪≫
        tensorModulesMapIso X (tensorPowDivisorialIso E hE n)
          (tensorPowModuleOneIso X E.divisorialSheaf) ≪≫
        (hE.nsmul n).divisorialSheafTensorIso hE ≪≫
        eqToIso (by rw [succ_nsmul])

open Stacks.Ample Stacks.RelativeVeryAmple Stacks.AmplePositivePower in
/-- If `m E = m' D` with `m, m' > 0` and `𝒪_X(D)` ample, then `𝒪_X(E)` is ample. -/
private theorem isAmple_divisorialSheaf_of_nsmul_eq [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (E D : Divisor X) (hE : E.IsCartier) (hD : D.IsCartier)
    [IsInvertibleModule X E.divisorialSheaf] [IsInvertibleModule X D.divisorialSheaf]
    (hDa : Stacks.Ample.IsAmple X D.divisorialSheaf) {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (h : m • E = m' • D) : Stacks.Ample.IsAmple X E.divisorialSheaf := by
  have e : tensorPowModule X D.divisorialSheaf (m' : ℤ) ≅
      tensorPowModule X E.divisorialSheaf (m : ℤ) :=
    tensorPowDivisorialIso D hD m' ≪≫ eqToIso (by rw [← h]) ≪≫
      (tensorPowDivisorialIso E hE m).symm
  exact isAmple_of_isAmple_tensorPowModule _ m hm
    ((isAmple_congr _ _ e).1 (isAmple_tensorPowModule_of_isAmple _ m' hm' hDa))

/-- The sheaf of a Cartier multiple of an ample `ℚ`-divisor is ample. -/
private theorem isAmple_divisorialSheaf_of_isAmple [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] {H : QDivisor X} (hH : H.IsAmple) (E : Divisor X) (hE : E.IsCartier) {m₂ : ℕ}
    (hm₂ : 0 < m₂) (h : Divisor.toQDivisor E = (m₂ : ℚ) • H) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Scheme.Modules.IsAmple X E.divisorialSheaf := by
  obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hH
  haveI := hE.isInvertibleModule_divisorialSheaf
  haveI := hDc.isInvertibleModule_divisorialSheaf
  refine (Stacks.AmpleBridge.isAmple_iff_isAmple X _).1 ?_
  refine isAmple_divisorialSheaf_of_nsmul_eq E D hE hDc hDa hm hm₂ ?_
  apply Divisor.toQDivisor_injective
  rw [map_nsmul, map_nsmul, h, hD, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
    smul_smul, smul_smul, mul_comm]

end AmpleMultiples

section ZeroDivisor

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- A nonzero section `σ` of `𝒪_X(M)` is the rational function `φ` with `div φ + M = (σ)₀`;
multiplication by `φ⁻¹` carries it to the section `1` of `𝒪_X((σ)₀)`. -/
private theorem divisorialSheafMulIso_app_eq_oneSection {M : Divisor X}
    (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    ((Divisor.divisorialSheafMulIso (D := M) (D' := M.zeroDivisor σ hσ)
        (Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ fun E => by
          rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
            PrimeDivisor.ord_inv]; ring).hom.app ⊤ σ) =
      MMP.Threefold.Mori.oneSection (M.zeroDivisor_nonneg σ hσ) := by
  refine Subtype.ext (funext fun Z => ?_)
  change ((Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ : (RationalFunctions X)ˣ).1 Z.1 *
      σ.1 Z = ((Divisor.structureSheafToDivisorialSheaf _).app ⊤ (1 : Γ(X, ⊤))).1 Z
  rw [Divisor.coe_structureSheafToDivisorialSheaf_app, map_one]
  have h1 : σ.1 Z = ((Divisor.isUnit_sectionToRationalFunctions hσ).unit :
      RationalFunctions X) Z.1 := rfl
  rw [h1, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rfl

/-- **The nonvanishing locus of a section is the complement of its divisor of zeros**, for a
Cartier divisor `M`. -/
private theorem nonvanishingLocus_eq_compl_supp_zeroDivisor {M : Divisor X} (hM : M.IsCartier)
    (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    haveI := hM.isInvertibleModule_divisorialSheaf
    Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ = ((M.zeroDivisor σ hσ).supp : Set X)ᶜ := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  have hZc : (M.zeroDivisor σ hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hM
  haveI := hZc.isInvertibleModule_divisorialSheaf
  rw [← Stacks.CokernelSupport.nonvanishingLocus_iso_app (Divisor.divisorialSheafMulIso (D := M)
    (D' := M.zeroDivisor σ hσ) (Divisor.isUnit_sectionToRationalFunctions hσ).unit⁻¹ fun E => by
      rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
        PrimeDivisor.ord_inv]; ring) σ]
  rw [divisorialSheafMulIso_app_eq_oneSection σ hσ]
  exact MMP.Threefold.Mori.nonvanishingLocus_oneSection _ hZc

/-- If the nonvanishing loci of sections `s i` of `𝒪_X(M)` cover `X`, every point lies off the
divisor of zeros of some nonzero `s i`. -/
theorem exists_ne_zero_notMem_supp_zeroDivisor {M : Divisor X} (hM : M.IsCartier) {ι : Type*}
    (s : ι → M.divisorialSubmodule ⊤)
    (hs : haveI := hM.isInvertibleModule_divisorialSheaf
      ∀ x : X, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf (s i)) (x : X) :
    ∃ (i : ι) (hi : s i ≠ 0), x ∉ (M.zeroDivisor (s i) hi).supp := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  obtain ⟨i, hi⟩ := hs x
  have hne : s i ≠ 0 := by
    intro h0
    let σ : Γ(M.divisorialSheaf, ⊤) := s i
    have hσ : x ∈ Stacks.Ample.nonvanishingLocus M.divisorialSheaf σ := hi
    have h0' : σ = 0 := h0
    rw [h0', Stacks.Ample.nonvanishingLocus_zero] at hσ
    exact hσ
  refine ⟨i, hne, fun hx => ?_⟩
  rw [nonvanishingLocus_eq_compl_supp_zeroDivisor hM (s i) hne] at hi
  exact hi hx

end ZeroDivisor

section GlobalGeneration

open Stacks.Ample Stacks.RelativeVeryAmple

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- `𝒪_X(n H + F) ≅ 𝒪_X(F) ⊗ 𝒪_X(H)^{⊗ n}` for Cartier divisors `H` and `F`. -/
private theorem nonempty_divisorialSheaf_nsmul_add_iso {H F : Divisor X} (hH : H.IsCartier)
    (hF : F.IsCartier) (n : ℕ) :
    haveI := hH.isInvertibleModule_divisorialSheaf
    Nonempty ((n • H + F).divisorialSheaf ≅
      tensorModules X F.divisorialSheaf (tensorPowModule X H.divisorialSheaf (n : ℤ))) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  induction n with
  | zero =>
    exact ⟨eqToIso (by rw [zero_smul, zero_add]) ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor X _).symm ≪≫
      tensorModulesMapIso X (Iso.refl _) (tensorPowModuleZeroIso X _).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [succ_nsmul, add_right_comm]) ≪≫
      (((hH.nsmul n).add hF).divisorialSheafTensorIso hH).symm ≪≫
      tensorModulesMapIso X e (tensorPowModuleOneIso X _).symm ≪≫
      Stacks.TensorSheafSpellingIso.tensorModulesAssociator X _ _ _ ≪≫
      tensorModulesMapIso X (Iso.refl _)
        (tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫ tensorPowModuleCongr X _ (by push_cast; ring))⟩

/-- **Serre generation for `𝒪_X(n H + F)`.** If `𝒪_X(H)` is ample and `F` is Cartier, then for
some `n` finitely many global sections `s₀, …, s_N` of `𝒪_X(n H + F)` have nonvanishing opens
covering `X`. -/
private theorem exists_forall_mem_nonvanishingOpen [IsIntegral X] {H F : Divisor X}
    (hH : H.IsCartier) (hF : F.IsCartier)
    (hamp : haveI := hH.isInvertibleModule_divisorialSheaf
      Stacks.Ample.IsAmple X H.divisorialSheaf) :
    ∃ (n N : ℕ) (s : Fin (N + 1) → Γ((n • H + F).divisorialSheaf, ⊤)),
      haveI := ((hH.nsmul n).add hF).isInvertibleModule_divisorialSheaf
      ∀ x : X, ∃ i, x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X (n • H + F).divisorialSheaf
        (s i) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  haveI := hF.isInvertibleModule_divisorialSheaf
  have : SheafOfModules.IsFiniteType.{u, u, u} F.divisorialSheaf :=
    Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hamp).2 F.divisorialSheaf inferInstance inferInstance
  set n : ℕ := n₀.toNat
  obtain ⟨σ, hσ⟩ := hn₀ (n : ℤ) (by omega)
  haveI := ((hH.nsmul n).add hF).isInvertibleModule_divisorialSheaf
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory X
  let i := Stacks.TensorSheafSpellingIso.monoidalTensorIso X F.divisorialSheaf
    (tensorPowModule X H.divisorialSheaf (n : ℤ))
  obtain ⟨e⟩ := nonempty_divisorialSheaf_nsmul_add_iso hH hF n
  let p := i.hom ≫ e.inv
  haveI : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ p :=
    @IsIso.epi_of_iso _ _ _ _ p inferInstance
  let σ' := σ.ofEpi p
  haveI : Finite σ'.I := hσ
  haveI : Fintype σ'.I := Fintype.ofFinite _
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨i₀, -⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing _ σ' x₀
  have hcard : 0 < Fintype.card σ'.I := Fintype.card_pos_iff.mpr ⟨i₀⟩
  let eI : σ'.I ≃ Fin (Fintype.card σ'.I - 1 + 1) :=
    Fintype.equivFinOfCardEq (by omega)
  refine ⟨n, Fintype.card σ'.I - 1, fun j => (σ'.s (eI.symm j)).eval (Opposite.op ⊤),
    fun x => ?_⟩
  obtain ⟨j, hj⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing _ σ' x
  refine ⟨eI j, ?_⟩
  have hx : x ∈ (Stacks.SheafOfModules.nonvanishingOpen _ (σ'.s j) : Set X) := hj
  rw [Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X _ (σ'.s j)] at hx
  simp only [Equiv.symm_apply_apply]
  exact hx

end GlobalGeneration

section General

/-- A prime divisor whose generic point lies on a finite union of prime divisors is one of them. -/
theorem mem_of_genericPoint_mem_biUnion_support {W : Scheme.{u}} [IsLocallyNoetherian W]
    [IsNormal W] {F : Finset (MMP.Mori.PrimeDivisor W)} {P : MMP.Mori.PrimeDivisor W}
    (h : P.genericPoint ∈ ⋃ E ∈ F, (E.support : Set W)) : P ∈ F := by
  obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp h
  rwa [← MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPE]

/-- On a smooth scheme, an snc subset is the union of the components of an snc divisor. -/
theorem exists_finset_isSNC_of_isSNCSubset {k : Type u} [Field k] {W : Scheme.{u}}
    {f : W ⟶ Spec (.of k)} [LocallyOfFiniteType f] {C : Closeds W}
    (hC : MMP.Mori.IsSNCSubset f C) (hf : IsSmoothScheme f) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor W), (⋃ E ∈ S, (E.support : Set W)) = (C : Set W) ∧
      DivisorWithCoeffs.IsSNC f (∑ E ∈ S, Finsupp.single E (1 : ℤ)) := by
  rcases hC with h0 | hS
  · refine ⟨∅, by simp [h0], ?_⟩
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hf
  · exact hS

/-- Adding a nonzero multiple of a divisor `Z` with no component in `Supp R` to `R` gives support
`Supp R ∪ Supp Z`. -/
theorem supp_add_toRDivisor_smul_toQDivisor {X : Scheme.{u}} {R : RDivisor X} {Z : Divisor X}
    {c : ℚ} (hc : c ≠ 0) (hcomp : ∀ P, Z.coeff P ≠ 0 → R.coeff P = 0) :
    ((R + QDivisor.toRDivisor (c • Divisor.toQDivisor Z)).supp : Set X) =
      (R.supp : Set X) ∪ Z.supp := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_union, DivisorWithCoeffs.mem_supp_iff,
    DivisorWithCoeffs.coeff_add, QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul,
    Divisor.coeff_toQDivisor, smul_eq_mul]
  constructor
  · rintro ⟨E, hE, hxE⟩
    by_cases hZE : Z.coeff E = 0
    · exact Or.inl ⟨E, by simpa [hZE] using hE, hxE⟩
    · exact Or.inr ⟨E, hZE, hxE⟩
  · rintro (⟨E, hE, hxE⟩ | ⟨E, hE, hxE⟩)
    · refine ⟨E, ?_, hxE⟩
      by_cases hZE : Z.coeff E = 0
      · simpa [hZE] using hE
      · exact absurd (hcomp E hZE) hE
    · refine ⟨E, ?_, hxE⟩
      rw [hcomp E hE, zero_add]
      have : c * (Z.coeff E : ℚ) ≠ 0 := mul_ne_zero hc (by exact_mod_cast hE)
      exact_mod_cast this

/-- If `π⁻¹ Supp Z` and `Exc(π) ∪ π⁻¹ Supp R` are the unions of the disjoint families of prime
divisors `T` and `S`, then no component of `Z` is a component of `R`. -/
theorem coeff_eq_zero_of_coeff_ne_zero_of_disjoint {X W : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {π : W ⟶ X} [IsProper π] [IsDominant π] (hπ : IsBirationalMorphism π) {R : RDivisor X}
    {Z : Divisor X} {S T : Finset (MMP.Mori.PrimeDivisor W)} (hTS : Disjoint T S)
    (hSU : (⋃ E ∈ S, (E.support : Set W)) =
      ((exceptionalSet π ⊔ R.supp.preimage π.continuous : Closeds W) : Set W))
    (hZT : π ⁻¹' (Z.supp : Set X) = ⋃ E ∈ T, (E.support : Set W)) (P : MMP.Mori.PrimeDivisor X)
    (hZP : Z.coeff P ≠ 0) : R.coeff P = 0 := by
  by_contra hRP
  obtain ⟨x', hx', hc', -, -⟩ := MMP.Intersection.exists_preimage_of_coheight_eq_one π
    hπ.functionFieldMap_bijective (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)
  set P' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hc' with hP'
  have hη : MMP.Mori.PrimeDivisor.genericPoint P' = x' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hPS : P' ∈ S := by
    have hmem : x' ∈ ((exceptionalSet π ⊔ R.supp.preimage π.continuous : Closeds W) :
        Set W) := Or.inr (show π x' ∈ R.supp by
      rw [hx']
      exact DivisorWithCoeffs.support_subset_supp hRP
        (MMP.Flips.primeDivisor_genericPoint_mem_support P))
    rw [← hSU] at hmem
    exact mem_of_genericPoint_mem_biUnion_support (by rwa [hη])
  have hPT : P' ∈ T := by
    have hmem : x' ∈ π ⁻¹' (Z.supp : Set X) := by
      rw [Set.mem_preimage, hx']
      exact DivisorWithCoeffs.support_subset_supp hZP
        (MMP.Flips.primeDivisor_genericPoint_mem_support P)
    rw [hZT] at hmem
    exact mem_of_genericPoint_mem_biUnion_support (by rwa [hη])
  exact Finset.disjoint_left.mp hTS hPT hPS

/-- If `D₀ = m • H` as `ℚ`-divisors, then `n • D₀ + D₀ = ((n + 1) * m) • H` coefficientwise. -/
theorem coeff_nsmul_add_self_eq_of_toQDivisor_eq {X : Scheme.{u}} {H : QDivisor X} {m : ℕ}
    {D₀ : Divisor X} (hD₀ : Divisor.toQDivisor D₀ = (m : ℚ) • H) (n : ℕ)
    (E : MMP.Mori.PrimeDivisor X) :
    (((n • D₀ + D₀).coeff E : ℤ) : ℚ) = (((n + 1) * m : ℕ) : ℚ) * H.coeff E := by
  have h1 := congrArg (fun G : QDivisor X => G.coeff E) hD₀
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h1
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul]
  push_cast
  rw [nsmul_eq_mul]
  push_cast
  rw [h1]
  ring

/-- If the pull-back of a Cartier divisor `Z` along a birational morphism of normal varieties is a
reduced sum of prime divisors, then every coefficient of `Z` is at most `1`. -/
theorem coeff_le_one_of_isPullback_eq_sum_single {k : Type u} [Field k] {X W : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of k)} (hXn : IsNormalVariety k sX) {π : W ⟶ X}
    (hWn : IsNormalVariety k (π ≫ sX)) [IsProper π] (hπ : IsBirationalMorphism π)
    {Z : Divisor X} (hZc : Z.IsCartier)
    {hB : ∀ Z' : irreducibleComponents W, π (componentGenericPoint W Z') ∉ Z.supp}
    {H : Divisor W} (hH : Z.IsPullback π hB H) {T : Finset (MMP.Mori.PrimeDivisor W)}
    (hT : H = ∑ E ∈ T, Finsupp.single E (1 : ℤ)) (P : MMP.Mori.PrimeDivisor X) :
    Z.coeff P ≤ 1 := by
  classical
  obtain ⟨E, heq, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hWn hπ P
  rw [← MMP.Positivity.coeff_eq_of_isPullback E P heq hZc hH, hT,
    DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', apply_ite]
  split_ifs <;> simp

/-- If `Z = L + div φ` for a Cartier divisor `L` with `L = M • H`, `M > 0` and `H` ample, then
`Z` is ample. -/
theorem isAmple_of_coeff_eq_ord_add {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {H : QDivisor X} (hH : H.IsAmple) {L Z : Divisor X}
    (hLc : L.IsCartier) (hZc : Z.IsCartier) {M : ℕ} (hM : 0 < M)
    (hLQ : ∀ E, ((L.coeff E : ℤ) : ℚ) = M * H.coeff E) (φ : (RationalFunctions X)ˣ)
    (hZφ : ∀ E, Z.coeff E = E.ord φ + L.coeff E) : Z.IsAmple hZc := by
  haveI := hLc.isInvertibleModule_divisorialSheaf
  haveI := hZc.isInvertibleModule_divisorialSheaf
  have hLQ' : Divisor.toQDivisor L = (M : ℚ) • H := by
    ext E
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul, hLQ E]
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ (Divisor.divisorialSheafMulIso
    (D := L) (D' := Z) φ⁻¹ fun E => by rw [hZφ E, PrimeDivisor.ord_inv]; ring)).1
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X _).2
      (isAmple_divisorialSheaf_of_isAmple hH L hLc hM hLQ'))

open Classical in
/-- **A general ample divisor on a log resolution.** Given a log resolution `π : W ⟶ X` of an
`ℝ`-divisor `R` and an ample `ℚ`-divisor `H`, there is an effective ample `H' ∼_ℚ H` with no
component in `Supp R` such that `π` is also a log resolution of `R + H'`: a general member of a
free multiple of `H`. Moreover `H' = Z / N` for a reduced effective Weil divisor `Z`. -/
theorem _root_.MMP.Mori.IsLogResolution.exists_isAmple_qLinearlyEquivalent_add
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X W : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hXv : AlgebraicGeometry.IsVariety k sX) {R : RDivisor X} {π : W ⟶ X}
    (hπ : MMP.Mori.IsLogResolution sX R π) {H : QDivisor X} (hH : H.IsAmple) :
    ∃ H' : QDivisor X, H'.IsEffective ∧ H'.IsAmple ∧ H'.QLinearlyEquivalent H ∧
      (∀ P, H'.coeff P ≠ 0 → R.coeff P = 0) ∧
      MMP.Mori.IsLogResolution sX (R + QDivisor.toRDivisor H') π ∧
      ∃ (N : ℕ) (Z : Divisor X), 0 < N ∧ 0 ≤ Z ∧ (∀ P, Z.coeff P ≤ 1) ∧
        H' = (N : ℚ)⁻¹ • Divisor.toQDivisor Z := by
  have hπs := hπ.toIsSmoothResolution
  have hXn : IsNormalVariety k sX := ⟨hXv, inferInstance⟩
  obtain ⟨hWn, -, -⟩ := hπs.isNormalVariety hXn
  haveI : IsIntegral W := hπs.isIntegral
  haveI : LocallyOfFiniteType (π ≫ sX) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : IsNormal W := hWn.2
  haveI : IsProper π := hπs.isProper
  haveI : IsDominant π := hπs.isBirationalMorphism.isDominant
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace π
  obtain ⟨m, hm, D₀, hD₀, hD₀c, hD₀a⟩ := id hH
  haveI := hD₀c.isInvertibleModule_divisorialSheaf
  obtain ⟨n, N, s, hs⟩ := exists_forall_mem_nonvanishingOpen hD₀c hD₀c hD₀a
  have hLc : (n • D₀ + D₀).IsCartier := (hD₀c.nsmul n).add hD₀c
  haveI := hLc.isInvertibleModule_divisorialSheaf
  let t : Fin (N + 1) → (n • D₀ + D₀).divisorialSubmodule ⊤ := s
  have ht : ∀ x : X, ∃ (i : Fin (N + 1)) (hi : t i ≠ 0),
      x ∉ ((n • D₀ + D₀).zeroDivisor (t i) hi).supp :=
    exists_ne_zero_notMem_supp_zeroDivisor hLc t hs
  obtain ⟨S, hSU, hSsnc⟩ := exists_finset_isSNC_of_isSNCSubset hπ.isSNCSubset hπs.isSmoothScheme
  obtain ⟨Q, hQ0, hQ⟩ :=
    MMP.Mori.exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC hXv hπs t ht S hSsnc
  obtain ⟨j, hj, -⟩ := ht (Nonempty.some inferInstance)
  obtain ⟨Q₁, hQ₁, hσ⟩ := exists_polynomial_sum_smul_ne_zero sX t j hj
  obtain ⟨c, hc⟩ : ∃ c : Fin (N + 1) → k, MvPolynomial.eval c (Q₁ * Q) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hQ₁ hQ0 (MvPolynomial.funext fun c => by rw [h c, map_zero])
  rw [map_mul] at hc
  have hσ0 := hσ c (left_ne_zero_of_mul hc)
  set Z : Divisor X := (n • D₀ + D₀).zeroDivisor _ hσ0 with hZdef
  have hZc : Z.IsCartier := by
    rw [hZdef, Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hLc
  have hZe : 0 ≤ Z := Divisor.zeroDivisor_nonneg _ _ hσ0
  have hBZ : ∀ Z' : irreducibleComponents W, π (componentGenericPoint W Z') ∉ Z.supp :=
    MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant π _
  obtain ⟨H'', hH''⟩ := hZc.exists_isPullback hBZ
  obtain ⟨T, hT, hTS, hTsnc, -⟩ := hQ c (right_ne_zero_of_mul hc) hσ0 hBZ H'' hH''
  have hsuppH'' : (H''.supp : Set W) = π ⁻¹' (Z.supp : Set X) :=
    MMP.Flips.supp_eq_preimage_supp_of_isPullback hZc
      (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hZe) hH''
  have hsuppT : (H''.supp : Set W) = ⋃ E ∈ T, (E.support : Set W) := by
    rw [hT, DivisorWithCoeffs.coe_supp, support_sum_single]
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ0).unit with hφ
  have hZφ : ∀ E, Z.coeff E = E.ord φ + (n • D₀ + D₀).coeff E := fun E => by
    rw [hZdef, Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  set M : ℕ := (n + 1) * m
  have hM : 0 < M := Nat.mul_pos (Nat.succ_pos n) hm
  have hLQ : ∀ E, (((n • D₀ + D₀).coeff E : ℤ) : ℚ) = M * H.coeff E :=
    coeff_nsmul_add_self_eq_of_toQDivisor_eq hD₀ n
  have hcomp : ∀ P, Z.coeff P ≠ 0 → R.coeff P = 0 :=
    coeff_eq_zero_of_coeff_ne_zero_of_disjoint hπs.isBirationalMorphism hTS hSU
      (hsuppH''.symm.trans hsuppT)
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨(M : ℚ)⁻¹ • Divisor.toQDivisor Z, fun P => ?_,
    ⟨M, hM, Z, ?_, hZc, isAmple_of_coeff_eq_ord_add hH hLc hZc hM hLQ φ hZφ⟩,
    ⟨M, hM, φ, ?_⟩, fun P hP => hcomp P ?_, ⟨hπs, hπ.isPureCodimOne_exceptionalSet,
      Or.inr ⟨T ∪ S, ?_, hTsnc⟩⟩, M, Z, hM, hZe,
    coeff_le_one_of_isPullback_eq_sum_single hXn hWn hπs.isBirationalMorphism hZc hH'' hT, rfl⟩
  · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
    have : (0 : ℚ) ≤ (Z.coeff P : ℚ) := by exact_mod_cast hZe P
    positivity
  · rw [smul_smul, mul_inv_cancel₀ hM', one_smul]
  · ext E
    rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor, coeff_principalDivisor, hZφ E]
    push_cast
    rw [hLQ E]
    simp only [zsmul_eq_mul, smul_eq_mul, Int.cast_natCast]
    field_simp
    ring
  · intro h0
    apply hP
    rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, h0]
    simp
  · rw [Finset.set_biUnion_union, ← hsuppT, hsuppH'', hSU]
    ext x
    simp only [Closeds.coe_sup, Set.mem_union, Closeds.coe_preimage, Set.mem_preimage,
      supp_add_toRDivisor_smul_toQDivisor (inv_ne_zero hM') hcomp]
    tauto

end General

end Bertini

/-! ### The steps of the proof -/

/-- **Relative Kodaira for the zero divisor.** Over a birational base, `0` is `f`-big, so
`0 ∼_ℚ H + G - c • f^*T₀` with `H` ample and effective and `G` effective. -/
private theorem exists_qLinearlyEquivalent_zero_add_sub_pullback {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : MMP.Mori.IsNormalVariety ℂ sZ)
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (hfb : IsBirationalMorphism f) :
    ∃ H G : QDivisor X, H.IsAmple ∧ H.IsEffective ∧ G.IsEffective ∧
      ∃ (c : ℚ) (T₀ : Z.CartierDivisor) (T₀' : X.CartierDivisor) (w : Divisor X),
        MMP.Intersection.IsPullback f T₀ T₀' ∧ MMP.Intersection.IsWeilDivisorOfCartier T₀' w ∧
        (0 : QDivisor X).QLinearlyEquivalent (H + G - c • Divisor.toQDivisor w) := by
  haveI := hX
  haveI := hZ
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sZ) := by rw [hf]; infer_instance
    exact LocallyOfFiniteType.of_comp this
  have : QuasiCompact f := by
    have : QuasiCompact (f ≫ sZ) := by rw [hf]; infer_instance
    exact QuasiCompact.of_comp f sZ
  haveI : IsIntegral Z := hZ.toIsIntegral
  have hbig := (isRelativelyPseudoEffective_and_isRelativelyBig_zero_of_isBirationalMorphism_toImage
    sX sZ f hX hXQ hZ hZn hf (isBirationalMorphism_toImage f hfb)).2
  exact MMP.Mori.QDivisor.IsRelativelyBig.exists_qLinearlyEquivalent_add_sub_pullback (k := ℂ)
    sX sZ hXQ f hf hbig

/-- Every `ℝ`-divisor `D` becomes effective after adding a multiple of the Weil divisor `w₁` of
the pull-back of a Cartier divisor of `Z`: every prime divisor of `X` is vertical over `Z`. -/
private theorem exists_isEffective_add_smul {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hfb : IsBirationalMorphism f) (D : RDivisor X) :
    ∃ (N : ℝ) (T₁ : Z.CartierDivisor) (T₁' : X.CartierDivisor) (w₁ : Divisor X),
      MMP.Intersection.IsPullback f T₁ T₁' ∧ MMP.Intersection.IsWeilDivisorOfCartier T₁' w₁ ∧
      (D + N • Divisor.toRDivisor w₁).IsEffective := by
  classical
  haveI := hX
  haveI := hZ
  haveI : IsIntegral Z := hZ.toIsIntegral
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sZ) := by rw [hf]; infer_instance
    exact LocallyOfFiniteType.of_comp this
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb
  have hpre := preimage_genericPoint f hb
  have hs : ∀ P ∈ D.support, f P.genericPoint ≠ f (genericPoint X) := by
    intro P _ h
    have hmem : P.genericPoint ∈ f ⁻¹' {genericPoint Z} := by
      show f P.genericPoint = genericPoint Z
      rw [h]
      exact IsBirational.genericPoint_eq f hb
    rw [hpre] at hmem
    have h1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
    have hmax : IsMax (genericPoint X) := fun z _ => genericPoint_specializes z
    have h0 : Order.coheight (genericPoint X) = 0 := Order.coheight_eq_zero.mpr hmax
    rw [show AlgebraicGeometry.PrimeDivisor.genericPoint P = genericPoint X from hmem, h0] at h1
    exact zero_ne_one h1
  obtain ⟨T₁, T₁', w₁, hT, hw, hwe, hwpos⟩ :=
    exists_weilPullback_pos_of_vertical (k := ℂ) sX sZ f D.support hs
  refine ⟨∑ P ∈ D.support, |D P|, T₁, T₁', w₁, hT, hw, fun P => ?_⟩
  have hN : ∀ Q ∈ D.support, |D Q| ≤ ∑ P ∈ D.support, |D P| := fun Q hQ =>
    Finset.single_le_sum (f := fun P => |D P|) (fun _ _ => abs_nonneg _) hQ
  have hN0 : 0 ≤ ∑ P ∈ D.support, |D P| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hwP : (0 : ℝ) ≤ (w₁.coeff P : ℝ) := by exact_mod_cast hwe P
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  by_cases hP : P ∈ D.support
  · have h1 : (1 : ℝ) ≤ (w₁.coeff P : ℝ) := by exact_mod_cast hwpos P hP
    have h2 := hN P hP
    have h3 := neg_abs_le (D P)
    rw [DivisorWithCoeffs.coeff_apply]
    nlinarith
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hP, zero_add]
    exact mul_nonneg hN0 hwP

/-- Adding `T_X ∼_ℚ c • f^*T₀` or a real multiple of a pull-back `w₁` does not change the
numerical class over `f`: `D + T_X ≡_f D + r • w₁`. -/
theorem isNumericallyEquivalentOver_add {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : MMP.Mori.IsNormalVariety ℂ sZ)
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (hfb : IsBirationalMorphism f)
    {T₀ T₁ : Z.CartierDivisor} {T₀' T₁' : X.CartierDivisor} {w w₁ : Divisor X}
    (hT : MMP.Intersection.IsPullback f T₀ T₀') (hw : MMP.Intersection.IsWeilDivisorOfCartier T₀' w)
    (hT₁ : MMP.Intersection.IsPullback f T₁ T₁')
    (hw₁ : MMP.Intersection.IsWeilDivisorOfCartier T₁' w₁)
    {TX : QDivisor X} {c : ℚ} (hTX : TX.QLinearlyEquivalent (c • Divisor.toQDivisor w))
    (D : RDivisor X) (r : ℝ) :
    MMP.Flips.IsNumericallyEquivalentOver ℂ sX f (D + QDivisor.toRDivisor TX)
      (D + r • Divisor.toRDivisor w₁) := by
  classical
  haveI := hX
  haveI := hZ
  haveI : IsIntegral Z := hZ.toIsIntegral
  haveI : IsNormal Z := hZn.2
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : AlgebraicGeometry.IsNoetherian Z := {}
  haveI : IsDominant f := hfb.isDominant
  obtain ⟨m, hm, φ, hφ⟩ := hTX
  have hw₀ := isWeilDivisorOfCartier_cartierWeilDivisor T₀
  have hw₀₁ := isWeilDivisorOfCartier_cartierWeilDivisor T₁
  let L : Fin 3 → Divisor X := ![MMP.Mori.principalDivisor φ, w, w₁]
  have hL : ∀ j, (L j).IsCartier := by
    intro j
    fin_cases j
    · exact Divisor.isCartier_principalDivisor φ
    · exact hw.isCartier
    · exact hw₁.isCartier
  refine isNumericallyEquivalentOver_of_eq_add_sum sX f
    (isCartierCombination_of_forall hXQ.2 _) (isCartierCombination_of_forall hXQ.2 _)
    ![((m : ℝ))⁻¹, (c : ℝ), -r] L hL ?_ ?_
  · intro j C hC d hd
    fin_cases j
    · exact IsCartierIntersectionNumber.eq_zero_of_principalDivisor φ hd
    · exact eq_zero_of_isCartierIntersectionNumber_of_isPullback f hf hw₀ hT hw _ C hC hd
    · exact eq_zero_of_isCartierIntersectionNumber_of_isPullback f hf hw₀₁ hT₁ hw₁ _ C hC hd
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    ext P
    have h1 := congrArg (fun F : QDivisor X => F.coeff P) hφ
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      Divisor.coeff_toQDivisor, zsmul_eq_mul] at h1
    simp only [L, Fin.sum_univ_three, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      smul_eq_mul]
    have h2 : ((TX.coeff P : ℚ) : ℝ) = ((MMP.Mori.principalDivisor φ).coeff P : ℝ) / m +
        (c : ℝ) * (w.coeff P : ℝ) := by
      have h3 : (TX.coeff P : ℚ) = ((MMP.Mori.principalDivisor φ).coeff P : ℚ) / m +
          c * (w.coeff P : ℚ) := by
        have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
        field_simp
        simp only [smul_eq_mul] at h1
        linear_combination h1
      rw [h3]
      push_cast
      ring
    rw [h2]
    field_simp
    ring

/-- A `ℚ`-divisor `T_X ∼_ℚ c • f^*T₀`, pulled back from a Cartier divisor on the base, is
numerically trivial over `f`. -/
theorem isNumericallyTrivialOver_of_qLinearlyEquivalent_smul_weilDivisor {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : MMP.Mori.IsNormalVariety ℂ sZ)
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (hfb : IsBirationalMorphism f)
    {T₀ : Z.CartierDivisor} {T₀' : X.CartierDivisor} {w : Divisor X}
    (hT : MMP.Intersection.IsPullback f T₀ T₀') (hw : MMP.Intersection.IsWeilDivisorOfCartier T₀' w)
    {TX : QDivisor X} {c : ℚ} (hTX : TX.QLinearlyEquivalent (c • Divisor.toQDivisor w)) :
    MMP.Flips.IsNumericallyTrivialOver ℂ sX f (QDivisor.toRDivisor TX) := by
  unfold MMP.Flips.IsNumericallyTrivialOver
  simpa using isNumericallyEquivalentOver_add sX sZ hX hXQ hZ hZn f hf hfb hT hw hT hw hTX 0 0

/-- Kollár–Mori 2.35 on a `ℚ`-factorial complex variety: `(X, B + D/N)` is klt for some
`N > 0`. -/
private theorem exists_isRealKltPair_add_inv_smul {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ))
    (hXQ : IsQFactorial sX) {B : RDivisor X} (hB : B.IsEffective) (hBk : IsRealKltPair sX B)
    {D : QDivisor X} (hD : D.IsEffective) :
    ∃ N : ℕ, 0 < N ∧ IsRealKltPair sX (B + QDivisor.toRDivisor (((N : ℚ)⁻¹) • D)) := by
  refine exists_isRealKltPair_add_inv_smul_of hXQ
    (fun D => exists_isLogResolution_of_charZero sX hXQ.1 D) (fun D' => ?_) hB hBk hD
  obtain ⟨m, r, L, hL, h⟩ := isCartierCombination_of_forall hXQ.2 D'
  refine ⟨m, r, L, hL, fun Γ => ?_⟩
  rw [h, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  rfl

/-- If `0 ∼_ℚ H + G - c • W` and `H' ∼_ℚ H`, then `ε • (H' + G) ∼_ℚ (ε c) • W`. -/
private theorem qLinearlyEquivalent_smul_add {X : Scheme.{0}} [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] {H H' G W : QDivisor X} {c : ℚ}
    (h0 : (0 : QDivisor X).QLinearlyEquivalent (H + G - c • W))
    (h : H'.QLinearlyEquivalent H) (ε : ℚ) :
    (ε • (H' + G)).QLinearlyEquivalent ((ε * c) • W) := by
  obtain ⟨m, hm, φ, hφ⟩ := h0
  obtain ⟨n, hn, ψ, hψ⟩ := h
  refine ⟨ε.den * m * n, by positivity, ψ ^ (ε.num * m) * φ ^ (-(ε.num * n)), ?_⟩
  ext E
  have h1 := congrArg (fun D => DivisorWithCoeffs.coeff D E) hφ
  have h2 := congrArg (fun D => DivisorWithCoeffs.coeff D E) hψ
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
    DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_zero, Divisor.coeff_toQDivisor,
    coeff_principalDivisor, zsmul_eq_mul, smul_eq_mul] at h1 h2 ⊢
  rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow, PrimeDivisor.ord_zpow, smul_eq_mul,
    smul_eq_mul]
  push_cast
  rw [← h1, ← h2]
  have hε : ε * ε.den = ε.num := Rat.mul_den_eq_num ε
  linear_combination ((m : ℚ) * n * (H'.coeff E + G.coeff E - c * W.coeff E)) * hε

/-- A positive rational multiple `H / N` of an ample `ℚ`-divisor is ample. -/
private theorem isAmple_inv_natCast_smul {X : Scheme.{0}} [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] {H : QDivisor X} (hH : H.IsAmple) {N : ℕ} (hN : 0 < N) :
    (((N : ℚ)⁻¹) • H).IsAmple := by
  obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hH
  refine ⟨m * N, Nat.mul_pos hm hN, D, ?_, hDc, hDa⟩
  rw [hD, smul_smul]
  congr 1
  have : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

/-- Let `f : X ⟶ Z` be a projective birational morphism of normal projective complex varieties
with `X` `ℚ`-factorial, `K` a canonical divisor of `X`, and `B` an effective `ℝ`-divisor with
`(X, B)` klt. There is an effective `ℝ`-divisor `M` such that, for some effective `ℚ`-divisor
`T_X ∼_ℚ c • f^*T₀` (`T₀` Cartier on `Z`, `c ∈ ℚ`) and some effective ample `ℚ`-divisor
`A ≤ B + T_X`, the pair `(X, B + T_X)` is klt, `K + B + T_X ≡_f M`, and no component of `A` is a
component of `M`. Moreover, for every log resolution `π` of `(X, B + M)`, such `T_X` and `A` can be
chosen so that `π` is also a log resolution of `(X, B + M + A)`. -/
@[mmp "lem_fourfold_birational_effective_ample_translation"]
theorem exists_isRealKltPair_add_pullback_isAmple_le_of_isBirationalMorphism
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : MMP.Mori.IsNormalVariety ℂ sZ)
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f)
    {n : ℕ} (K : Divisor X) (hK : K.IsCanonicalDivisor sX n)
    (B : RDivisor X) (hB : B.IsEffective) (hBk : IsRealKltPair sX B) :
    ∃ M : RDivisor X, M.IsEffective ∧
      (∃ (TX A : QDivisor X) (c : ℚ) (T₀ : Z.CartierDivisor) (T₀' : X.CartierDivisor)
          (w : Divisor X),
        MMP.Intersection.IsPullback f T₀ T₀' ∧ MMP.Intersection.IsWeilDivisorOfCartier T₀' w ∧
        TX.IsEffective ∧ TX.QLinearlyEquivalent (c • Divisor.toQDivisor w) ∧
        A.IsEffective ∧ A.IsAmple ∧ QDivisor.toRDivisor A ≤ B + QDivisor.toRDivisor TX ∧
        IsRealKltPair sX (B + QDivisor.toRDivisor TX) ∧
        MMP.Flips.IsNumericallyEquivalentOver ℂ sX f
          (Divisor.toRDivisor K + B + QDivisor.toRDivisor TX) M ∧
        ∀ P, A.coeff P ≠ 0 → M.coeff P = 0) ∧
      ∀ (W : Scheme.{0}) (π : W ⟶ X), MMP.Mori.IsLogResolution sX (B + M) π →
        ∃ (TX A : QDivisor X) (c : ℚ) (T₀ : Z.CartierDivisor) (T₀' : X.CartierDivisor)
          (w : Divisor X),
          MMP.Intersection.IsPullback f T₀ T₀' ∧ MMP.Intersection.IsWeilDivisorOfCartier T₀' w ∧
          TX.IsEffective ∧ TX.QLinearlyEquivalent (c • Divisor.toQDivisor w) ∧
          A.IsEffective ∧ A.IsAmple ∧ QDivisor.toRDivisor A ≤ B + QDivisor.toRDivisor TX ∧
          IsRealKltPair sX (B + QDivisor.toRDivisor TX) ∧
          MMP.Flips.IsNumericallyEquivalentOver ℂ sX f
            (Divisor.toRDivisor K + B + QDivisor.toRDivisor TX) M ∧
          (∀ P, A.coeff P ≠ 0 → M.coeff P = 0) ∧
          MMP.Mori.IsLogResolution sX (B + M + QDivisor.toRDivisor A) π := by
  obtain ⟨H, G, hHa, hHe, hGe, c, T₀, T₀', w, hT, hw, hlin⟩ :=
    exists_qLinearlyEquivalent_zero_add_sub_pullback sX sZ hX hXQ hZ hZn f hf hfb
  obtain ⟨NM, T₁, T₁', w₁, hT₁, hw₁, hMe⟩ :=
    exists_isEffective_add_smul sX sZ hX hZ f hf hfb (Divisor.toRDivisor K + B)
  set M : RDivisor X := Divisor.toRDivisor K + B + NM • Divisor.toRDivisor w₁ with hM
  have key : ∀ (W : Scheme.{0}) (π : W ⟶ X), MMP.Mori.IsLogResolution sX (B + M) π →
      ∃ (TX A : QDivisor X) (c : ℚ) (T₀ : Z.CartierDivisor) (T₀' : X.CartierDivisor)
        (w : Divisor X),
        MMP.Intersection.IsPullback f T₀ T₀' ∧ MMP.Intersection.IsWeilDivisorOfCartier T₀' w ∧
        TX.IsEffective ∧ TX.QLinearlyEquivalent (c • Divisor.toQDivisor w) ∧
        A.IsEffective ∧ A.IsAmple ∧ QDivisor.toRDivisor A ≤ B + QDivisor.toRDivisor TX ∧
        IsRealKltPair sX (B + QDivisor.toRDivisor TX) ∧
        MMP.Flips.IsNumericallyEquivalentOver ℂ sX f
          (Divisor.toRDivisor K + B + QDivisor.toRDivisor TX) M ∧
        (∀ P, A.coeff P ≠ 0 → M.coeff P = 0) ∧
        MMP.Mori.IsLogResolution sX (B + M + QDivisor.toRDivisor A) π := by
    intro W π hπ
    obtain ⟨H', hH'e, hH'a, hH'lin, hH'R, hπ', -⟩ :=
      hπ.exists_isAmple_qLinearlyEquivalent_add ((MMP.Mori.isProjectiveVariety_iff ℂ sX).mp hX).1
        hHa
    obtain ⟨N, hN, hklt⟩ := exists_isRealKltPair_add_inv_smul sX hXQ hB hBk (hH'e.add hGe)
    set ε : ℚ := (N : ℚ)⁻¹ with hε
    have hε0 : 0 < ε := inv_pos.mpr (by exact_mod_cast hN)
    have hTXlin := qLinearlyEquivalent_smul_add hlin hH'lin ε
    refine ⟨ε • (H' + G), ε • H', ε * c, T₀, T₀', w, hT, hw, fun P => ?_, hTXlin, fun P => ?_,
      isAmple_inv_natCast_smul hH'a hN, fun P => ?_, hklt,
      isNumericallyEquivalentOver_add sX sZ hX hXQ hZ hZn f hf hfb hT hw hT₁ hw₁ hTXlin _ NM,
      fun P hP => ?_, ?_⟩
    · simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_smul, Finsupp.coe_add, Pi.smul_apply,
        Pi.add_apply, smul_eq_mul]
      exact mul_nonneg hε0.le (add_nonneg (hH'e P) (hGe P))
    · simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hε0.le (hH'e P)
    · show (QDivisor.toRDivisor (ε • H')).coeff P ≤
        (B + QDivisor.toRDivisor (ε • (H' + G))).coeff P
      simp only [DivisorWithCoeffs.coeff_add, QDivisor.coeff_toRDivisor,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul, mul_add, Rat.cast_add]
      have : (0 : ℝ) ≤ ((ε * G.coeff P : ℚ) : ℝ) := by exact_mod_cast mul_nonneg hε0.le (hGe P)
      linarith [hB P]
    · have hHP : H'.coeff P ≠ 0 := fun h0 => hP (by simp [h0])
      have h := hH'R P hHP
      rw [DivisorWithCoeffs.coeff_add] at h
      exact ((add_eq_zero_iff_of_nonneg (hB P) (hMe P)).1 h).2
    · refine isLogResolution_of_supp_eq hπ' (supp_congr fun P => ?_)
      simp only [DivisorWithCoeffs.coeff_add, QDivisor.coeff_toRDivisor,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul, Rat.cast_mul]
      exact (add_mul_ne_zero_iff (add_nonneg (hB P) (hMe P))
        (b := (H'.coeff P : ℝ)) (by exact_mod_cast hH'e P) (ε := (ε : ℝ))
        (by exact_mod_cast hε0)).symm
  refine ⟨M, hMe, ?_, key⟩
  obtain ⟨W, π, hπ⟩ := exists_isLogResolution_of_charZero sX hXQ.1 (B + M)
  obtain ⟨TX, A, c, T₀, T₀', w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := key W π hπ
  exact ⟨TX, A, c, T₀, T₀', w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end MMP.Fourfold

end
