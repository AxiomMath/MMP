module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Dimension.KrullPrincipalIdeal
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Divisor.RationalFunctionsProduct
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.Surface.CanonicalMinimalResolutionCrepant
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC
import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberLogResolution
import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberDiscrepancy
import MMP.AlgebraicGeometry.Divisor.GeneralMemberAdjunction
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolution
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.Positivity.AmpleTwistRealPerturbation
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# General hyperplane sections of pairs, and terminal varieties in codimension two

Let `(X, Δ)` be a pair over an algebraically closed field `k` of characteristic zero with
`dim X ≥ 2`, and `|V|` a free linear system on `X`, spanned by finitely many sections `sᵢ` of
`𝒪_X(H)` without common zero. For a general member `H_g = (∑ cᵢ sᵢ)₀` of `|V|` and every connected
component `H⁰` of `H_g`, the scheme `H⁰` is a normal variety and
`discrep(X, Δ) ≤ discrep(H⁰, Δ|_{H⁰})`, where `Δ|_{H⁰}` is the restriction by components
`MMP.Mori.DivisorWithCoeffs.restrictComponents` (Kollár–Mori 5.17(1)).

To prove it, choose a log resolution `f : Y ⟶ X` of `(X, Δ)` whose boundary transform
`∑ⱼ f⁻¹_* Dⱼ` is smooth. For a general member, the base change `f⁰ : Y ×_X H⁰ ⟶ H⁰` is a log
resolution of `(H⁰, Δ|_{H⁰})` with smooth boundary transform, whose exceptional prime divisors are
the components of the `Eᵢ ∩ (Y ×_X H⁰)` and have the discrepancies of the `Eᵢ`. Both
discrepancies are then minima over these log resolutions, and every term of the minimum for
`H⁰` bounds `discrep(X, Δ)` from above.

As a consequence, a terminal variety is smooth in codimension two (Kollár–Mori 5.18): every point
of the singular locus of `X` has codimension at least three when `(X, 0)` is terminal. The proof
is by induction on `dim X`. In dimension two, a singular point would give an exceptional curve of
the minimal resolution with discrepancy `0`. In higher dimension, a connected component of a
general member of a pencil through a singular point `x` of codimension at most two is again
terminal, by the first result, and has a singular point of codimension at most two.

## Main results

* `MMP.Mori.IsPair.exists_polynomial_discrep_le_discrep_restrict_connectedComponent`: the
  discrepancy does not drop on a connected component of a general member of a free linear system.
* `MMP.Mori.IsTerminalPair.three_le_coheight_of_mem_singularLocus`: terminal varieties are smooth
  in codimension two.

## Implementation notes

"General" means `Q(c) ≠ 0` for a nonzero polynomial `Q` in the coefficients of `σ = ∑ cᵢ sᵢ`, and
`H⁰` is a connected component `Z` of `Supp (σ)₀` with its reduced structure, the setting of
`MMP.Mori.IsLogResolution.exists_polynomial_isLogResolution_restrict_connectedComponent`. That
`H⁰` is a normal variety, which `MMP.Mori.discrep` requires, is part of the conclusion. The
inequality is stated for every canonical divisor `K` of `X` and every divisor `K'` on `H⁰`: when
`K'` is not canonical, no divisor over `H⁰` has a discrepancy and the right-hand side is `⊤`.

The log resolution with smooth boundary transform (Kollár–Mori 2.32(2)) is built from any log
resolution by repeatedly blowing up an irreducible component of the intersection of the
transforms of two distinct components of `Δ`. The generic points of the components of these
pairwise intersections decrease strictly in number, so finitely many blow-ups make the transforms
pairwise disjoint. A component of `Δ|_{H⁰}` lies on a single component of `Δ`: its generic point
lies over the biregular locus of `f`, where the transforms of the components of `Δ` are disjoint.

The codimension of `Sing X` is stated pointwise, through `Order.coheight` for the specialization
order. The source cuts by `n - 2` general hyperplane sections of an affine chart at once. Here one
hyperplane is cut at a time, by induction on the dimension, and the member is taken in the pencil
spanned by `1` and one regular function `a` that is non-constant on the closure `W` of `x`. Then
`a` takes infinitely many values on the closed points of `W`, so a general member of the pencil
through a closed point of `W` exists, and no projective closure is needed. That `K_S` is
`ℚ`-Cartier on the hyperplane section `S`, which the source reads off adjunction, is read here
off a discrepancy: an exceptional divisor of the base change of a log resolution of `X` lies over
the singular point of `S`, and its discrepancy over `S` equals a discrepancy over `X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 5.17(1),
  Corollary 5.18
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry hiding PrimeDivisor

universe u

namespace MMP.Mori

/-- A variety is a Noetherian scheme. -/
private theorem isNoetherian_of_isVariety {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)}
    (h : AlgebraicGeometry.IsVariety k sY) : IsNoetherian Y := by
  have : LocallyOfFiniteType sY := h.toLocallyOfFiniteType
  have : QuasiCompact sY := h.toQuasiCompact
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  exact ⟨⟩

/-! ### Log resolutions and their exceptional divisors -/

section ComponentsOf

open MMP.Resolution

variable {Y : Scheme.{u}}

/-- A component of a closed subset of pure codimension one is the closure of a point of
codimension one. -/
private theorem exists_coheight_eq_one_of_mem_componentsOf {S : Set Y} (hSc : IsClosed S)
    (hS : MMP.Mori.IsPureCodimOne (⟨S, hSc⟩ : Closeds Y)) {V : Set Y}
    (hV : V ∈ componentsOf S) : ∃ ξ : Y, V = closure {ξ} ∧ Order.coheight ξ = 1 := by
  obtain ⟨ξ, -, hξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hSc hV
  refine ⟨ξ, hξ, ?_⟩
  rw [← MMP.Flips.codimension_closureSingleton]
  apply hS
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {ξ} ⊆ S
    rw [← hξ]
    exact hV.1.2
  · have : (W' : Set Y) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rwa [hξ])
    change (W' : Set Y) ⊆ closure {ξ}
    rw [← hξ]
    exact this

end ComponentsOf

section LogResolution

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A prime divisor whose generic point lies on finitely many prime divisors is one of them. -/
private theorem mem_of_genericPoint_mem_iUnion {Y : Scheme.{u}}
    {s : Finset (MMP.Mori.PrimeDivisor Y)} {C : Set Y}
    (hs : (⋃ E ∈ s, (E.support : Set Y)) = C) {F : MMP.Mori.PrimeDivisor Y}
    (hF : F.genericPoint ∈ C) : F ∈ s := by
  rw [← hs] at hF
  obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hF
  rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE

/-- Prime divisors with the same inverse transform are equal. -/
private theorem eq_of_inverseTransformPrimeDivisor_eq_some {Y : Scheme.{u}} {f : Y ⟶ X}
    {P Q : MMP.Mori.PrimeDivisor X} {G : MMP.Mori.PrimeDivisor Y}
    (hP : inverseTransformPrimeDivisor f P = some G)
    (hQ : inverseTransformPrimeDivisor f Q = some G) : P = Q :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hP).1.symm.trans
        (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ).1

/-- The generic point of the inverse transform of a component of `Δ` lies in
`Ex(f) ∪ f⁻¹(Supp Δ)`. -/
private theorem genericPoint_mem_of_inverseTransformPrimeDivisor_eq_some {Y : Scheme.{u}}
    {Δ : QDivisor X} {f : Y ⟶ X} {P : MMP.Mori.PrimeDivisor X} (hP : P ∈ Δ.support)
    {G : MMP.Mori.PrimeDivisor Y} (hG : inverseTransformPrimeDivisor f P = some G) :
    G.genericPoint ∈ ((exceptionalSet f ⊔
      (QDivisor.toRDivisor Δ).supp.preimage f.continuous : Closeds Y) : Set Y) := by
  right
  change f G.genericPoint ∈ (QDivisor.toRDivisor Δ).supp
  rw [QDivisor.supp_toRDivisor,
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hG).1]
  exact DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hP)
    (MMP.Flips.primeDivisor_genericPoint_mem_support P)

/-- The exceptional prime divisors of a log resolution are finitely many. -/
private theorem exists_finset_isExceptional [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} {Y : Scheme.{u}} {f : Y ⟶ X}
    (hf : IsLogResolution sX D f) :
    ∃ Ex : Finset (MMP.Mori.PrimeDivisor Y),
      ∀ F : MMP.Mori.PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F := by
  classical
  have hmem : ∀ F : MMP.Mori.PrimeDivisor Y, RationalMap.IsExceptional f.toRationalMap F →
      F.genericPoint ∈ ((exceptionalSet f ⊔ D.supp.preimage f.continuous : Closeds Y) : Set Y) :=
    fun F hF => Or.inl (MMP.Positivity.support_subset_exceptionalSet F hF
      (MMP.Flips.primeDivisor_genericPoint_mem_support F))
  rcases hf.isSNCSubset with h0 | ⟨s, hs, -⟩
  · refine ⟨∅, fun F => ⟨fun h => absurd h (Finset.notMem_empty _), fun hF => ?_⟩⟩
    have := hmem F hF
    rw [h0] at this
    exact absurd this (by simp)
  · refine ⟨s.filter (fun F => RationalMap.IsExceptional f.toRationalMap F), fun F => ?_⟩
    rw [Finset.mem_filter]
    refine ⟨fun h => h.2, fun hF => ⟨?_, hF⟩⟩
    exact mem_of_genericPoint_mem_iUnion hs (hmem F hF)

/-- The coefficient of `G` in `∑_{E ∈ s} E` is nonzero exactly for `G ∈ s`. -/
private theorem mem_support_sum_single {Y : Scheme.{u}} (s : Finset (MMP.Mori.PrimeDivisor Y))
    {G : MMP.Mori.PrimeDivisor Y} (hG : G ∈ s) :
    G ∈ (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply, hG]

/-- A component of a transformed divisor is the transform of a component. -/
private theorem exists_of_mem_support_mapPrimeDivisors {Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (D : DivisorWithCoeffs R X) (F : MMP.Mori.PrimeDivisor Y)
    (hF : F ∈ (DivisorWithCoeffs.mapPrimeDivisors φ D).support) :
    ∃ D' ∈ D.support, φ D' = some F := by
  classical
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum] at hF
  obtain ⟨D', hD', hF'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hF)
  refine ⟨D', hD', ?_⟩
  cases h : φ D' with
  | none => simp [h] at hF'
  | some G =>
    simp only [h, Option.elim_some, Finsupp.singleAddHom_apply] at hF'
    have := Finsupp.support_single_subset hF'
    simp only [Finset.mem_singleton] at this
    rw [this]

/-- The inverse transform of a component of `Δ` is a component of the inverse transform of `Δ`. -/
private theorem mem_support_inverseTransformDivisor {Y : Scheme.{u}} (h : Y ⟶ X) {R : Type*}
    [AddCommMonoid R] (Δ : DivisorWithCoeffs R X) {E : MMP.Mori.PrimeDivisor X}
    (hE : E ∈ Δ.support) {F : MMP.Mori.PrimeDivisor Y}
    (hF : inverseTransformPrimeDivisor h E = some F) :
    F ∈ (inverseTransformDivisor h Δ).support := by
  classical
  rw [Finsupp.mem_support_iff]
  change (DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor h) Δ) F ≠ 0
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finset.sum_eq_single E]
  · rw [hF]
    simpa using Finsupp.mem_support_iff.mp hE
  · intro D _ hDE
    cases hD : inverseTransformPrimeDivisor h D with
    | none => simp
    | some F' =>
      simp only [Option.elim_some, Finsupp.singleAddHom_apply]
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hDE (eq_of_inverseTransformPrimeDivisor_eq_some hD hF)
  · exact fun hE' => absurd hE hE'

/-- Distinct components of an snc divisor whose union is smooth are disjoint. -/
private theorem disjoint_of_isSmoothScheme_iInf {R : Type*} [Zero R]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY) {T : Finset (MMP.Mori.PrimeDivisor Y)}
    (hT : T ⊆ D.support)
    (hsm : IsSmoothScheme ((⨅ F ∈ T, F.idealSheaf).subschemeι ≫ sY)) :
    ∀ F ∈ T, ∀ F' ∈ T, F ≠ F' → Disjoint F.support F'.support := by
  classical
  intro F hF F' hF' hne
  rw [Set.disjoint_left]
  intro y hyF hyF'
  set K : Y.IdealSheafData := ⨅ F ∈ T, F.idealSheaf with hKdef
  have hKinf : K = T.inf fun G => G.idealSheaf := by rw [Finset.inf_eq_iInf]
  have hKF : K ≤ F.idealSheaf := iInf₂_le F hF
  have hyK : y ∈ K.support := Scheme.IdealSheafData.support_antitone hKF hyF
  obtain ⟨z, rfl⟩ : ∃ z, K.subschemeι z = y := by
    rwa [← SetLike.mem_coe, ← K.range_subschemeι] at hyK
  have : LocallyOfFinitePresentation (K.subschemeι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := K.subschemeι ≫ sY)).mpr
      inferInstance
  have : Smooth (K.subschemeι ≫ sY) := (isSmoothScheme_iff _).mp hsm
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field (K.subschemeι ≫ sY) z
  have : IsDomain (K.subscheme.presheaf.stalk z) := IsRegularLocalRing.isDomain _
  have hdom : IsDomain (Y.presheaf.stalk (K.subschemeι z) ⧸
      IdealSheafData.stalk K (K.subschemeι z)) :=
    (IdealSheafData.subschemeStalkQuotEquiv K z).toMulEquiv.isDomain
  have hprime : (IdealSheafData.stalk K (K.subschemeι z)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  set y := K.subschemeι z
  have hKs : IdealSheafData.stalk K y = T.inf fun G => IdealSheafData.stalk G.idealSheaf y := by
    rw [hKinf, MMP.Intersection.stalk_finsetInf]
  obtain ⟨G, hG, hGK⟩ := (Ideal.IsPrime.inf_le' (s := T)
    (f := fun G : MMP.Mori.PrimeDivisor Y => IdealSheafData.stalk G.idealSheaf y) hprime).mp
      hKs.symm.le
  have hyG : y ∈ G.support := by
    by_contra hyG
    rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support G hyG, top_le_iff] at hGK
    exact hprime.ne_top hGK
  obtain ⟨n, w, j, hw, hj, hI⟩ := hD.2 y
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have key : ∀ (P : MMP.Mori.PrimeDivisor Y) (hP : P ∈ T) (hyP : y ∈ P.support),
      j ⟨G, hT hG, hyG⟩ = j ⟨P, hT hP, hyP⟩ := by
    intro P hP hyP
    by_contra hjne
    have h1 : IdealSheafData.stalk G.idealSheaf y ≤ IdealSheafData.stalk P.idealSheaf y :=
      hGK.trans (hKs.le.trans (Finset.inf_le (f := fun G : MMP.Mori.PrimeDivisor Y =>
        IdealSheafData.stalk G.idealSheaf y) hP))
    rw [hI ⟨G, hT hG, hyG⟩, hI ⟨P, hT hP, hyP⟩, Ideal.span_singleton_le_iff_mem] at h1
    exact MMP.Resolution.notMem_span_singleton_of_isRegularSystemOfParameters hw hjne h1
  have h12 := (key F hF hyF).symm.trans (key F' hF' hyF')
  exact hne (congrArg Subtype.val (hj h12))

/-- If the reduced divisor on the components of the boundary transform of a log resolution is
smooth, the transforms of the components of the boundary are smooth and pairwise disjoint. -/
private theorem smooth_and_disjoint_of_isSmoothScheme [LocallyOfFiniteType sX] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y]
    {Δ : QDivisor X} {f : Y ⟶ X} (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (hsm : IsSmoothScheme
      ((⨅ F ∈ (inverseTransformDivisor f Δ).support, F.idealSheaf).subschemeι ≫ f ≫ sX)) :
    (∀ P ∈ Δ.support, ∀ E : MMP.Mori.PrimeDivisor Y, inverseTransformPrimeDivisor f P = some E →
      IsSmoothScheme (E.idealSheaf.subschemeι ≫ f ≫ sX)) ∧
    (∀ P ∈ Δ.support, ∀ Q ∈ Δ.support, P ≠ Q → ∀ E E' : MMP.Mori.PrimeDivisor Y,
      inverseTransformPrimeDivisor f P = some E → inverseTransformPrimeDivisor f Q = some E' →
        Disjoint (E.support : Set Y) E'.support) := by
  classical
  have : IsProper f := hf.isProper
  rcases hf.isSNCSubset with h0 | ⟨S, hS, hsnc⟩
  · refine ⟨fun P hP E hE => ?_, fun P hP _ _ _ E _ hE _ => ?_⟩ <;>
    · have h := genericPoint_mem_of_inverseTransformPrimeDivisor_eq_some hP hE
      rw [h0] at h
      simp at h
  have hmemS : ∀ P ∈ Δ.support, ∀ E : MMP.Mori.PrimeDivisor Y,
      inverseTransformPrimeDivisor f P = some E → E ∈ S := fun P hP E hE =>
    mem_of_genericPoint_mem_iUnion hS
      (genericPoint_mem_of_inverseTransformPrimeDivisor_eq_some hP hE)
  refine ⟨fun P hP E hE => hsnc.1 E (mem_support_sum_single S (hmemS P hP E hE)), ?_⟩
  intro P hP Q hQ hPQ E E' hE hE'
  have hT : (inverseTransformDivisor f Δ).support ⊆
      (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support := by
    intro G hG
    obtain ⟨P', hP', hG'⟩ := exists_of_mem_support_mapPrimeDivisors
      (inverseTransformPrimeDivisor f) Δ G hG
    exact mem_support_sum_single S (hmemS P' hP' G hG')
  exact disjoint_of_isSmoothScheme_iInf (f ≫ sX) hsnc hT hsm E
    (mem_support_inverseTransformDivisor f Δ hP hE) E'
    (mem_support_inverseTransformDivisor f Δ hQ hE')
    (by rintro rfl; exact hPQ (eq_of_inverseTransformPrimeDivisor_eq_some hE hE'))

end LogResolution

/-! ### Fibres over the biregular locus -/

section Fibres

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A proper birational morphism is surjective. -/
private theorem surjective_of_isBirationalMorphism {Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (hf : IsBirationalMorphism f) : Function.Surjective f := by
  have := hf.isDominant
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have hd : Dense (Set.range f) := f.denseRange
  intro x
  change x ∈ Set.range f
  rw [← hcl.closure_eq, hd.closure_eq]
  trivial

/-- Over a point outside the biregular locus of a proper birational morphism onto a normal variety,
the fibre has more than one point. -/
private theorem not_subsingleton_fiber_of_notMem_biregularLocus {Y : Scheme.{u}}
    (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {x : X}
    (hx : x ∉ biregularLocus f) : ¬ (f ⁻¹' {x}).Subsingleton := by
  have := hX.2
  have := hY.toIsIntegral
  have := hX.1.toIsIntegral
  obtain ⟨u, rfl⟩ := surjective_of_isBirationalMorphism f hf x
  have hu : u ∈ exceptionalSet f := hx
  have key := (MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k hY hX.1 f
    rfl (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)).2.1
  have hu' : u ∈ (exceptionalSet f : Set Y) := hu
  rw [key] at hu'
  intro hsub
  have : Subsingleton (f ⁻¹' {f u}) := hsub.coe_sort
  have : DiscreteTopology (f ⁻¹' {f u}) := ⟨Subsingleton.elim _ _⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology (f ⁻¹' {f u})
  have hu'' : 0 < topologicalKrullDim (f ⁻¹' {f u}) := hu'
  exact absurd (lt_of_lt_of_le hu'' h0) (lt_irrefl _)

/-- Being an isomorphism over an open is stable under base change. -/
private theorem isIso_pullback_snd_morphismRestrict {Y Z : Scheme.{u}} (f : Y ⟶ X) (ι : Z ⟶ X)
    (V : X.Opens) [IsIso (f ∣_ V)] :
    IsIso (pullback.snd f ι ∣_ (ι ⁻¹ᵁ V)) := by
  have hC := (isPullback_morphismRestrict (pullback.snd f ι) (ι ⁻¹ᵁ V)).flip
  have hB := IsPullback.of_hasPullback f ι
  have hs := hC.paste_horiz hB
  rw [← morphismRestrict_ι ι V] at hs
  have hD := IsPullback.of_right' hs (isPullback_morphismRestrict f V).flip
  exact hD.isIso_snd_of_isIso

/-- A morphism is injective over its biregular locus. -/
private theorem injOn_preimage_biregularLocus {Y : Scheme.{u}} (f : Y ⟶ X) :
    Set.InjOn f.base (f ⁻¹ᵁ biregularLocus f : Set Y) := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  have hinj : Function.Injective ((f ⁻¹ᵁ biregularLocus f).ι ≫ f).base := by
    rw [← morphismRestrict_ι]
    exact ((f ∣_ biregularLocus f) ≫ (biregularLocus f).ι).isOpenEmbedding.injective
  exact fun a ha b hb hab ↦ congrArg Subtype.val (@hinj ⟨a, ha⟩ ⟨b, hb⟩ hab)

/-- The fibre of a morphism over a point of its biregular locus has at most one point. -/
private theorem subsingleton_fiber_of_mem_biregularLocus {Y Z : Scheme.{u}} (f : Y ⟶ Z) {z : Z}
    (hz : z ∈ biregularLocus f) : (f ⁻¹' {z}).Subsingleton := by
  intro a ha b hb
  exact injOn_preimage_biregularLocus f (show f a ∈ biregularLocus f by rwa [ha])
    (show f b ∈ biregularLocus f by rwa [hb]) (ha.trans hb.symm)

/-- The biregular locus of the base change is the preimage of the biregular locus of `f`, when the
fibres of `f` over the other points have several points. -/
private theorem mem_biregularLocus_pullback_snd_iff {Y Z : Scheme.{u}} (f : Y ⟶ X) (ι : Z ⟶ X)
    (hA : ∀ x, x ∉ biregularLocus f → ¬ (f ⁻¹' {x}).Subsingleton) (z : Z) :
    z ∈ biregularLocus (pullback.snd f ι) ↔ ι z ∈ biregularLocus f := by
  constructor
  · intro hz
    by_contra hx
    apply hA _ hx
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨w₁, hw₁, hw₁'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ι) y₁ z hy₁
    obtain ⟨w₂, hw₂, hw₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ι) y₂ z hy₂
    rw [← hw₁, ← hw₂, subsingleton_fiber_of_mem_biregularLocus _ hz hw₁' hw₂']
  · intro hz
    have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
    have : IsIso (pullback.snd f ι ∣_ (ι ⁻¹ᵁ biregularLocus f)) :=
      isIso_pullback_snd_morphismRestrict f ι _
    exact le_biregularLocus (V := ι ⁻¹ᵁ biregularLocus f) this hz

/-- A point of codimension at most one of a normal variety lies in the biregular locus of a proper
birational morphism from a variety. -/
private theorem mem_biregularLocus_of_coheight_le_one {Y : Scheme.{u}}
    (hX : IsNormalVariety k sX) (f : Y ⟶ X) (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) {x : X} (hx : Order.coheight x ≤ 1) :
    x ∈ biregularLocus f := by
  have := hX.1.toIsIntegral
  refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hX f hY hf ?_
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast hx

end Fibres

section Disjoining

/-! ### Separating the transforms of the components of the boundary

Starting from a log resolution `g` of `(X, Δ)`, blow up an irreducible component `W` of the
intersection `g⁻¹_* P ∩ g⁻¹_* Q` of the transforms of two distinct components of `Δ`
(`MMP.Resolution.blowUp_snc_stratum`). The composite is again a log resolution, and the generic
points of the components of the pairwise intersections of the new transforms map injectively to
those of the old ones other than the generic point of `W`. After finitely many steps the
transforms are pairwise disjoint, and then the reduced divisor on them is smooth. -/

open MMP.Resolution

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The codimension of the closure of a point is its coheight. -/
private theorem closedsCodimension_closure_closure_singleton {Y : Scheme.{u}} (y : Y) :
    MMP.Mori.closedsCodimension (Closeds.closure (closure {y} : Set Y)) = Order.coheight y := by
  have : Closeds.closure (closure {y} : Set Y) =
      ⟨(IrreducibleCloseds.closureSingleton y : Set Y),
        (IrreducibleCloseds.closureSingleton y).isClosed⟩ :=
    Closeds.ext (by rw [Closeds.coe_closure, closure_closure]; rfl)
  rw [this, closedsCodimension_coe, MMP.Flips.codimension_closureSingleton]

section Strata

variable {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} {Λ : Type*} [Fintype Λ]
  {Sf : Λ → MMP.Mori.PrimeDivisor Y}

/-- The generic point of an irreducible component of `⋂_{j ∈ J} S_j`, for an snc family `S`
on a smooth variety, has codimension `|J|`. -/
private theorem coheight_eq_card_of_mem_componentsOf [PerfectField k]
    (hY : MMP.Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) (hS : Function.Injective Sf)
    (hSNC : DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (Sf j) (1 : ℤ)))
    (J : Finset Λ) (hJ : 2 ≤ J.card) {y : Y}
    (hy : closure {y} ∈ componentsOf (⋂ j ∈ J, ((Sf j).support : Set Y))) :
    Order.coheight y = J.card := by
  have h := (blowUp_snc_stratum sY hY hsm Sf hS hSNC J hJ ⟨_, hy⟩).2.1
  rwa [closedsCodimension_closure_closure_singleton] at h

/-- Every point of `⋂_{j ∈ J} S_j`, for an snc family `S` on a smooth variety, has codimension
at least `|J|`. -/
private theorem card_le_coheight_of_mem_iInter [PerfectField k]
    (hY : MMP.Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) (hS : Function.Injective Sf)
    (hSNC : DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (Sf j) (1 : ℤ)))
    (J : Finset Λ) (hJ : 2 ≤ J.card) {y : Y} (hy : y ∈ ⋂ j ∈ J, ((Sf j).support : Set Y)) :
    (J.card : ℕ∞) ≤ Order.coheight y := by
  have : IsNoetherian Y := isNoetherian_of_isVariety hY
  have hcl : IsClosed (⋂ j ∈ J, ((Sf j).support : Set Y)) :=
    isClosed_biInter fun j _ => (Sf j).idealSheaf.support.isClosed
  obtain ⟨W, hW, hyW⟩ := (Aux.finite_and_cover_componentsOf hcl).2 hy
  obtain ⟨ξ, -, hWξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hcl hW
  have hξ := coheight_eq_card_of_mem_componentsOf hY hsm hS hSNC J hJ (hWξ ▸ hW)
  rw [← hξ]
  rw [hWξ] at hyW
  exact Order.coheight_anti (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hyW))

/-- A point of `⋂_{j ∈ J} S_j` of codimension at most `|J|` is the generic point of an
irreducible component. -/
private theorem closure_singleton_mem_componentsOf [PerfectField k]
    (hY : MMP.Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) (hS : Function.Injective Sf)
    (hSNC : DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (Sf j) (1 : ℤ)))
    (J : Finset Λ) (hJ : 2 ≤ J.card) {y : Y} (hy : y ∈ ⋂ j ∈ J, ((Sf j).support : Set Y))
    (hcoh : Order.coheight y ≤ J.card) :
    closure {y} ∈ componentsOf (⋂ j ∈ J, ((Sf j).support : Set Y)) := by
  have : IsNoetherian Y := isNoetherian_of_isVariety hY
  have hcl : IsClosed (⋂ j ∈ J, ((Sf j).support : Set Y)) :=
    isClosed_biInter fun j _ => (Sf j).idealSheaf.support.isClosed
  refine ⟨⟨isIrreducible_singleton.closure, closure_minimal (Set.singleton_subset_iff.mpr hy)
    hcl⟩, fun T hT hle => ?_⟩
  -- the component through the generic point of `T` is the closure of `y`
  have hTc : closure T ⊆ ⋂ j ∈ J, ((Sf j).support : Set Y) := closure_minimal hT.2 hcl
  set ξ := hT.1.genericPoint
  have hξ : IsGenericPoint ξ (closure T) := hT.1.isGenericPoint_genericPoint_closure
  obtain ⟨W, hW, hξW⟩ := (Aux.finite_and_cover_componentsOf hcl).2 (hTc hξ.mem)
  obtain ⟨ξ₁, -, hWξ₁⟩ := Aux.exists_eq_closure_of_mem_componentsOf hcl hW
  have hξ₁ := coheight_eq_card_of_mem_componentsOf hY hsm hS hSNC J hJ (hWξ₁ ▸ hW)
  have hTW : closure T ⊆ closure {ξ₁} := by
    rw [← hξ.def, ← hWξ₁]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξW)
      (Aux.isClosed_of_mem_componentsOf hcl hW)
  have hyT : y ∈ closure {ξ₁} := hTW (subset_closure (hle (subset_closure rfl)))
  have hsp : ξ₁ ⤳ y := specializes_iff_mem_closure.mpr hyT
  have hξ₁y : ξ₁ = y := by
    by_contra hne
    have hlt : y < ξ₁ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
      fun h => hne (hsp.antisymm (Scheme.le_iff_specializes.mp h)).eq
    have := Order.coheight_strictAnti hlt
    rw [hξ₁] at this
    exact absurd (this (by simp)) (not_lt.mpr hcoh)
  rw [← hξ₁y]
  exact subset_closure.trans hTW

/-- The intersection over a pair. -/
private theorem iInter_pair {j₁ j₂ : Λ} [DecidableEq Λ] :
    (⋂ j ∈ ({j₁, j₂} : Finset Λ), ((Sf j).support : Set Y)) =
      ((Sf j₁).support : Set Y) ∩ (Sf j₂).support := by
  ext y
  simp

end Strata

/-- **The exceptional set of a composite.** For proper birational morphisms `p : Y' ⟶ Y` and
`g : Y ⟶ X` of varieties with `X` and `Y` normal, `Ex(g ∘ p) = p⁻¹(Ex(g)) ∪ Ex(p)`: by Zariski's
main theorem a point lies off the biregular locus exactly when its fibre has several points. -/
private theorem coe_exceptionalSet_comp {Y Y' : Scheme.{u}} (hX : IsNormalVariety k sX)
    {g : Y ⟶ X} {p : Y' ⟶ Y} (hY : IsNormalVariety k (g ≫ sX))
    (hY' : MMP.Mori.IsVariety k ((p ≫ g) ≫ sX)) [IsProper g] [IsProper p]
    (hg : IsBirationalMorphism g) (hp : IsBirationalMorphism p)
    (hgp : IsBirationalMorphism (p ≫ g)) :
    (exceptionalSet (p ≫ g) : Set Y') =
      p ⁻¹' (exceptionalSet g : Set Y) ∪ (exceptionalSet p : Set Y') := by
  have hY'' : MMP.Mori.IsVariety k (p ≫ g ≫ sX) := by rwa [← Category.assoc]
  ext y'
  simp only [Set.mem_union, Set.mem_preimage, SetLike.mem_coe, mem_exceptionalSet,
    Scheme.Hom.comp_apply]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨hgV, hpV⟩ := hcon
    apply h
    by_contra hx
    apply not_subsingleton_fiber_of_notMem_biregularLocus hX (p ≫ g) hY' hgp hx
    intro z₁ hz₁ z₂ hz₂
    have h₁ : p z₁ = p y' := subsingleton_fiber_of_mem_biregularLocus g hgV hz₁ rfl
    have h₂ : p z₂ = p y' := subsingleton_fiber_of_mem_biregularLocus g hgV hz₂ rfl
    exact subsingleton_fiber_of_mem_biregularLocus p hpV h₁ h₂
  · rintro (h | h) hx
    · apply not_subsingleton_fiber_of_notMem_biregularLocus hX g hY.1 hg h
      intro a ha b hb
      obtain ⟨a', rfl⟩ := surjective_of_isBirationalMorphism p hp a
      obtain ⟨b', rfl⟩ := surjective_of_isBirationalMorphism p hp b
      have := subsingleton_fiber_of_mem_biregularLocus (p ≫ g) hx
        (show (p ≫ g) a' = g (p y') from ha) (show (p ≫ g) b' = g (p y') from hb)
      rw [this]
    · apply not_subsingleton_fiber_of_notMem_biregularLocus hY p hY'' hp h
      intro a ha b hb
      have ha' : p a = p y' := ha
      have hb' : p b = p y' := hb
      exact subsingleton_fiber_of_mem_biregularLocus (p ≫ g) hx
        (show (p ≫ g) a = g (p y') by rw [Scheme.Hom.comp_apply, ha'])
        (show (p ≫ g) b = g (p y') by rw [Scheme.Hom.comp_apply, hb'])

/-- A closed subset which is a finite union of prime divisors is of pure codimension one. -/
private theorem isPureCodimOne_of_eq_iUnion {Y : Scheme.{u}} {C : Closeds Y}
    (s : Finset (MMP.Mori.PrimeDivisor Y)) (hC : (C : Set Y) = ⋃ F ∈ s, (F.support : Set Y)) :
    MMP.Mori.IsPureCodimOne C := by
  classical
  intro W hW
  have hWC : (W : Set Y) ⊆ ⋃₀ ((s.image fun F => (F.support : Set Y) : Finset (Set Y)) :
      Set (Set Y)) := by
    intro y hy
    have := hC ▸ hW.prop hy
    obtain ⟨F, hF, hyF⟩ := Set.mem_iUnion₂.mp this
    exact ⟨F.support, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨F, hF, rfl⟩), hyF⟩
  obtain ⟨Z, hZ, hWZ⟩ := isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible _
    (fun Z hZ => by
      obtain ⟨F, -, rfl⟩ := Finset.mem_image.mp hZ
      exact F.idealSheaf.support.isClosed) hWC
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hZ
  have hFs : ((IrreducibleCloseds.closureSingleton F.genericPoint : IrreducibleCloseds Y) :
      Set Y) = F.support := by
    change closure {F.genericPoint} = _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have hle : W ≤ IrreducibleCloseds.closureSingleton F.genericPoint := by
    change (W : Set Y) ⊆ _
    rwa [hFs]
  have hP : ((IrreducibleCloseds.closureSingleton F.genericPoint : IrreducibleCloseds Y) :
      Set Y) ⊆ C := by
    rw [hFs, hC]
    exact Set.subset_biUnion_of_mem (u := fun F => (F.support : Set Y)) hF
  have heq : W = IrreducibleCloseds.closureSingleton F.genericPoint :=
    le_antisymm hle (hW.2 hP hle)
  rw [heq, MMP.Flips.codimension_closureSingleton, F.coheight_genericPoint]

/-- The generic points of the irreducible components of the pairwise intersections of the
transforms `g⁻¹_* P`, `g⁻¹_* Q` of distinct components `P ≠ Q` of `Δ`. -/
private def badSet (Δ : QDivisor X) {Y : Scheme.{u}} (g : Y ⟶ X) : Set Y :=
  {y | ∃ P ∈ Δ.support, ∃ Q ∈ Δ.support, P ≠ Q ∧ ∃ G G' : MMP.Mori.PrimeDivisor Y,
    inverseTransformPrimeDivisor g P = some G ∧ inverseTransformPrimeDivisor g Q = some G' ∧
    closure {y} ∈ componentsOf ((G.support : Set Y) ∩ G'.support)}

/-- On a Noetherian scheme the set `badSet Δ g` is finite. -/
private theorem finite_badSet (Δ : QDivisor X) {Y : Scheme.{u}} [NoetherianSpace Y]
    (g : Y ⟶ X) : (badSet Δ g).Finite := by
  classical
  have hfin : ∀ P Q : MMP.Mori.PrimeDivisor X, {y : Y | ∃ G G' : MMP.Mori.PrimeDivisor Y,
      inverseTransformPrimeDivisor g P = some G ∧ inverseTransformPrimeDivisor g Q = some G' ∧
      closure {y} ∈ componentsOf ((G.support : Set Y) ∩ G'.support)}.Finite := by
    intro P Q
    rcases hP : inverseTransformPrimeDivisor g P with _ | G
    · refine Set.finite_empty.subset ?_
      rintro y ⟨G, G', hG, -, -⟩
      cases hG
    rcases hQ : inverseTransformPrimeDivisor g Q with _ | G'
    · refine Set.finite_empty.subset ?_
      rintro y ⟨G₁, G₁', -, hG', -⟩
      cases hG'
    have hcl : IsClosed ((G.support : Set Y) ∩ G'.support) :=
      G.idealSheaf.support.isClosed.inter G'.idealSheaf.support.isClosed
    refine Set.Finite.of_finite_image ((Aux.finite_and_cover_componentsOf hcl).1.subset ?_)
      fun y _ y' _ h => (inseparable_iff_closure_eq.2 h).eq
    rintro _ ⟨y, ⟨G₁, G₁', h₁, h₁', hy⟩, rfl⟩
    cases h₁
    cases h₁'
    exact hy
  refine ((Δ.support.finite_toSet.biUnion fun P _ =>
    Δ.support.finite_toSet.biUnion fun Q _ => hfin P Q)).subset ?_
  rintro y ⟨P, hP, Q, hQ, -, G, G', hG, hG', hy⟩
  exact Set.mem_iUnion₂.mpr ⟨P, hP, Set.mem_iUnion₂.mpr ⟨Q, hQ, G, G', hG, hG', hy⟩⟩

/-- When `badSet Δ g` is empty, the transforms of distinct components of `Δ` are disjoint. -/
private theorem disjoint_of_badSet_eq_empty {Δ : QDivisor X} {Y : Scheme.{u}}
    [NoetherianSpace Y] {g : Y ⟶ X} (h : badSet Δ g = ∅) :
    ∀ P ∈ Δ.support, ∀ Q ∈ Δ.support, P ≠ Q → ∀ G G' : MMP.Mori.PrimeDivisor Y,
      inverseTransformPrimeDivisor g P = some G → inverseTransformPrimeDivisor g Q = some G' →
        Disjoint (G.support : Set Y) G'.support := by
  intro P hP Q hQ hPQ G G' hG hG'
  rw [Set.disjoint_iff]
  intro y hy
  have hcl : IsClosed ((G.support : Set Y) ∩ G'.support) :=
    G.idealSheaf.support.isClosed.inter G'.idealSheaf.support.isClosed
  obtain ⟨W, hW, -⟩ := (Aux.finite_and_cover_componentsOf hcl).2 hy
  obtain ⟨ξ, -, hWξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hcl hW
  have : ξ ∈ badSet Δ g := ⟨P, hP, Q, hQ, hPQ, G, G', hG, hG', hWξ ▸ hW⟩
  rw [h] at this
  exact this

/-- If the transforms of distinct components of `Δ` under a log resolution `f` are disjoint, the
reduced divisor `∑ⱼ f⁻¹_* Dⱼ` is smooth. -/
private theorem isSmoothScheme_of_disjoint [PerfectField k] {Δ : QDivisor X} {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] {f : Y ⟶ X} [LocallyOfFiniteType (f ≫ sX)]
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (hdisj : ∀ P ∈ Δ.support, ∀ Q ∈ Δ.support, P ≠ Q → ∀ G G' : MMP.Mori.PrimeDivisor Y,
      inverseTransformPrimeDivisor f P = some G → inverseTransformPrimeDivisor f Q = some G' →
        Disjoint (G.support : Set Y) G'.support) :
    IsSmoothScheme
      ((⨅ F ∈ (inverseTransformDivisor f Δ).support, F.idealSheaf).subschemeι ≫ f ≫ sX) := by
  classical
  set T := (inverseTransformDivisor f Δ).support with hT
  -- every member of `T` is the transform of a component of `Δ`
  have hTP : ∀ F ∈ T, ∃ P ∈ Δ.support, inverseTransformPrimeDivisor f P = some F :=
    fun F hF => exists_of_mem_support_mapPrimeDivisors (inverseTransformPrimeDivisor f) Δ F hF
  have honly : ∀ F ∈ T, ∀ F' ∈ T, ∀ w, w ∈ F.support → w ∈ F'.support → F = F' := by
    intro F hF F' hF' w hw hw'
    by_contra hne
    obtain ⟨P, hP, hPF⟩ := hTP F hF
    obtain ⟨Q, hQ, hQF⟩ := hTP F' hF'
    have hPQ : P ≠ Q := by
      rintro rfl
      exact hne (Option.some.inj (hPF.symm.trans hQF))
    exact Set.disjoint_left.mp (hdisj P hP Q hQ hPQ F F' hPF hQF) hw hw'
  -- the snc divisor containing the members of `T`
  have hmem : ∀ F ∈ T, F.genericPoint ∈ ((exceptionalSet f ⊔
      (QDivisor.toRDivisor Δ).supp.preimage f.continuous : Closeds Y) : Set Y) := fun F hF =>
    have ⟨_, hP, hPF⟩ := hTP F hF
    genericPoint_mem_of_inverseTransformPrimeDivisor_eq_some hP hPF
  have hKinf : (⨅ F ∈ T, F.idealSheaf) = T.inf fun F => F.idealSheaf := by
    rw [Finset.inf_eq_iInf]
  refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ fun w hw => ?_
  have hstK : IdealSheafData.stalk (⨅ F ∈ T, F.idealSheaf) w =
      T.inf fun F => IdealSheafData.stalk F.idealSheaf w := by
    rw [hKinf, MMP.Intersection.stalk_finsetInf]
  obtain ⟨F, hF, hwF⟩ : ∃ F ∈ T, w ∈ F.support := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    have htop : IdealSheafData.stalk (⨅ F ∈ T, F.idealSheaf) w = ⊤ := by
      rw [hstK, Finset.inf_eq_top_iff]
      intro F hF
      exact MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support F (hno F hF)
    exact ((IdealSheafData.stalk_eq_top_iff_notMem_support _ w).mp htop) hw
  have hstF : IdealSheafData.stalk (⨅ F ∈ T, F.idealSheaf) w =
      IdealSheafData.stalk F.idealSheaf w := by
    rw [hstK]
    refine le_antisymm (Finset.inf_le hF) (Finset.le_inf fun F' hF' => ?_)
    by_cases hwF' : w ∈ F'.support
    · rw [honly F hF F' hF' w hwF hwF']
    · rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support F' hwF']; exact le_top
  rcases hf.isSNCSubset with h0 | ⟨S, hS, hsnc⟩
  · have h := hmem F hF
    rw [h0] at h
    simp at h
  have hFS : F ∈ S := mem_of_genericPoint_mem_iUnion hS (hmem F hF)
  obtain ⟨n, z, j, hz, -, hI⟩ := hsnc.2 w
  exact ⟨n, z, j ⟨F, mem_support_sum_single S hFS, hwF⟩, hz,
    hstF.trans (hI ⟨F, mem_support_sum_single S hFS, hwF⟩)⟩

/-- If `A = p⁻¹ S ∪ E` and the sets `T i` cover `S ∪ D`, with `T' i ⊆ p⁻¹ (T i) ⊆ T' i ∪ E`,
then `A ∪ p⁻¹ D = E ∪ ⋃ i, T' i`. -/
theorem union_preimage_eq_of_cover {α β ι : Type*} (p : α → β) {A E : Set α} {S D : Set β}
    {T : ι → Set β} {T' : ι → Set α} (hA : A = p ⁻¹' S ∪ E) (hT : ⋃ i, T i = S ∪ D)
    (hsub : ∀ i, T' i ⊆ p ⁻¹' T i) (hsup : ∀ i, p ⁻¹' T i ⊆ T' i ∪ E) :
    A ∪ p ⁻¹' D = E ∪ ⋃ i, T' i := by
  subst hA
  have key : ∀ w, p w ∈ S ∪ D → w ∈ E ∪ ⋃ i, T' i := fun w hw => by
    rw [← hT] at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    rcases hsup i hi with h | h
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, h⟩)
    · exact Or.inl h
  refine Set.Subset.antisymm ?_ ?_
  · rintro w ((hw | hw) | hw)
    · exact key w (Or.inl hw)
    · exact Or.inl hw
    · exact key w (Or.inr hw)
  · rintro w (hw | hw)
    · exact Or.inl (Or.inr hw)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
      have h : p w ∈ S ∪ D := hT ▸ Set.mem_iUnion.mpr ⟨i, hsub i hi⟩
      rcases h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

/-- **One blow-up step.** If `badSet Δ g` is nonempty, blowing up the component of the
intersection of two transforms through one of its points gives a log resolution with a smaller
`badSet`. -/
private theorem exists_step [CharZero k] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (Δ : QDivisor X) {Y : Scheme.{u}} {g : Y ⟶ X}
    (hg : IsLogResolution sX (QDivisor.toRDivisor Δ) g) {y₀ : Y} (hy₀ : y₀ ∈ badSet Δ g) :
    ∃ (Y' : Scheme.{u}) (g' : Y' ⟶ X), IsLogResolution sX (QDivisor.toRDivisor Δ) g' ∧
      (badSet Δ g').ncard < (badSet Δ g).ncard := by
  classical
  have : PerfectField k := PerfectField.ofCharZero
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsProper g := hg.isProper
  have hgb := hg.isBirationalMorphism
  obtain ⟨hYv, -, hgB⟩ := hg.toIsSmoothResolution.isNormalVariety hX
  have : IsIntegral Y := hYv.1.toIsIntegral
  have : IsNormal Y := hYv.2
  have : LocallyOfFiniteType (g ≫ sX) := hYv.1.toLocallyOfFiniteType
  have : IsNoetherian Y := isNoetherian_of_isVariety hYv.1
  have hsmY : IsSmoothScheme (g ≫ sX) := hg.isSmoothScheme
  obtain ⟨P₀, hP₀, Q₀, hQ₀, hPQ₀, G₀, G₀', hG₀, hG₀', hW₀⟩ := id hy₀
  rcases hg.isSNCSubset with h0 | ⟨S, hS, hsnc⟩
  · have h := genericPoint_mem_of_inverseTransformPrimeDivisor_eq_some hP₀ hG₀
    rw [h0] at h
    simp at h
  -- the snc family of the components of `Ex(g) ∪ g⁻¹(Supp Δ)`
  let Sf : S → MMP.Mori.PrimeDivisor Y := Subtype.val
  have hSNC : DivisorWithCoeffs.IsSNC (g ≫ sX) (∑ j, Finsupp.single (Sf j) (1 : ℤ)) := by
    rwa [Finset.sum_coe_sort S (fun E => Finsupp.single E (1 : ℤ))]
  have hidx : ∀ P ∈ Δ.support, ∀ G, inverseTransformPrimeDivisor g P = some G → G ∈ S :=
    fun P hP G hG => mem_of_genericPoint_mem_iUnion hS
      (genericPoint_mem_of_inverseTransformPrimeDivisor_eq_some hP hG)
  have hne₀ : G₀ ≠ G₀' := by
    rintro rfl
    exact hPQ₀ (eq_of_inverseTransformPrimeDivisor_eq_some hG₀ hG₀')
  set a : S := ⟨G₀, hidx P₀ hP₀ G₀ hG₀⟩ with ha
  set b : S := ⟨G₀', hidx Q₀ hQ₀ G₀' hG₀'⟩ with hb
  have hab : a ≠ b := fun h => hne₀ (congrArg Subtype.val h)
  have hJ : 2 ≤ ({a, b} : Finset S).card := by rw [Finset.card_pair hab]
  have hWc : closure {y₀} ∈
      componentsOf (⋂ j ∈ ({a, b} : Finset S), ((Sf j).support : Set Y)) := by
    rwa [iInter_pair]
  have hst := blowUp_snc_stratum (g ≫ sX) hYv.1 hsmY Sf Subtype.val_injective hSNC {a, b} hJ
    ⟨closure {y₀}, hWc⟩
  have hTcl : IsClosed (⋂ j ∈ ({a, b} : Finset S), ((Sf j).support : Set Y)) :=
    isClosed_biInter fun j _ => (Sf j).idealSheaf.support.isClosed
  have hIs := coe_support_componentsFamily hTcl ⟨closure {y₀}, hWc⟩
  generalize componentsFamily (⋂ j ∈ ({a, b} : Finset S), ((Sf j).support : Set Y))
    ⟨closure {y₀}, hWc⟩ = I at hst hIs
  obtain ⟨-, -, hsm', hiso, E, S', hEI, -, hS'tr, hS'inj, hS'E, hsnc', -, -⟩ := hst
  change (I.support : Set Y) = closure {y₀} at hIs
  -- the centre `W = closure {y₀}` has codimension two
  have hcoh₀ : Order.coheight y₀ = 2 := by
    rw [coheight_eq_card_of_mem_componentsOf hYv.1 hsmY Subtype.val_injective hSNC {a, b} hJ hWc,
      Finset.card_pair hab]
    rfl
  have hWT : closure {y₀} ⊆ (G₀.support : Set Y) := fun y hy => (hW₀.1.2 hy).1
  have hnuniv : ∃ y : Y, y ∉ closure {y₀} := by
    by_contra h
    push Not at h
    have hmax : IsMax y₀ := fun z _ =>
      Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr (h z))
    have := Order.coheight_eq_zero.mpr hmax
    rw [hcoh₀] at this
    exact absurd this (by norm_num)
  have hI0 : I ≠ ⊥ := by
    intro h
    obtain ⟨y, hy⟩ := hnuniv
    apply hy
    rw [← hIs, h, Scheme.IdealSheafData.support_bot]
    trivial
  -- the blow-up
  haveI := hYv.1
  obtain ⟨hY'v, hpproj, hpB⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational (g ≫ sX) I hI0
  set p := blowUpToBase I with hpdef
  have : IsProper p := hpproj.isProper
  have : IsIntegral (blowUp I) := hY'v.toIsIntegral
  have : LocallyOfFiniteType (p ≫ g ≫ sX) := hY'v.toLocallyOfFiniteType
  have : IsNoetherian (blowUp I) := isNoetherian_of_isVariety hY'v
  have : IsNormal (blowUp I) :=
    (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm').2
  have hY''v : MMP.Mori.IsVariety k ((p ≫ g) ≫ sX) := by rwa [Category.assoc]
  have hsm'' : IsSmoothScheme ((p ≫ g) ≫ sX) := by rwa [Category.assoc]
  have hVp : I.support.compl ≤ biregularLocus p := le_biregularLocus hiso
  have hpV : ∀ y, y ∉ closure {y₀} → y ∈ biregularLocus p := fun y hy =>
    hVp (show y ∉ (I.support : Set Y) by rwa [hIs])
  have hpb : IsBirationalMorphism p := by
    obtain ⟨y, hy⟩ := hnuniv
    have hyV : y ∈ I.support.compl := show y ∉ (I.support : Set Y) by rwa [hIs]
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE p (p ⁻¹ᵁ I.support.compl)
      I.support.compl ⟨_, ((inv (p ∣_ I.support.compl)) ⟨y, hyV⟩).2⟩ ⟨y, hyV⟩ le_rfl ?_
    simpa [Scheme.Hom.resLE] using hiso
  have hg'b : IsBirationalMorphism (p ≫ g) := isBirationalMorphism_comp_of_isBirational g p hgB hpB
  have hEsupp : (E.support : Set (blowUp I)) = p ⁻¹' closure {y₀} := by
    change ((E.idealSheaf.support : Set (blowUp I))) = _
    rw [hEI, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hIs]
  -- no point of the centre lies in the biregular locus of `p`
  have hWnotV : ∀ w ∈ closure {y₀}, w ∉ biregularLocus p := by
    intro w hw hwV
    have hy₀V : y₀ ∈ biregularLocus p :=
      (specializes_iff_mem_closure.mpr hw).mem_open (biregularLocus p).isOpen hwV
    obtain ⟨e, he⟩ := surjective_of_isBirationalMorphism p hpb y₀
    have heE : e ∈ E.support := by
      rw [hEsupp]; show p e ∈ closure {y₀}; rw [he]; exact subset_closure rfl
    have hsp : E.genericPoint ⤳ e := specializes_iff_mem_closure.mpr (by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact heE)
    have hηV : p E.genericPoint ∈ biregularLocus p :=
      (hsp.map p.continuous).mem_open (biregularLocus p).isOpen (he ▸ hy₀V)
    have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus p hηV
    rw [E.coheight_genericPoint] at h1
    have hηW : p E.genericPoint ∈ closure {y₀} := by
      have : E.genericPoint ∈ (E.support : Set (blowUp I)) :=
        MMP.Flips.primeDivisor_genericPoint_mem_support E
      rwa [hEsupp] at this
    have h2 : Order.coheight y₀ ≤ Order.coheight (p E.genericPoint) :=
      Order.coheight_anti (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hηW))
    rw [h1, hcoh₀] at h2
    exact absurd h2 (by norm_num)
  have hExp : (exceptionalSet p : Set (blowUp I)) = E.support := by
    rw [hEsupp]
    ext w
    simp only [SetLike.mem_coe, mem_exceptionalSet, Set.mem_preimage]
    exact ⟨fun h => by_contra fun h' => h (hpV _ h'), fun h => hWnotV _ h⟩
  have hExg' : (exceptionalSet (p ≫ g) : Set (blowUp I)) =
      p ⁻¹' (exceptionalSet g : Set Y) ∪ E.support := by
    rw [coe_exceptionalSet_comp hX hYv hY''v hgb hpb hg'b, hExp]
  -- the transforms under `g ∘ p`
  have hexP : ∀ P ∈ Δ.support, ∃ G, inverseTransformPrimeDivisor g P = some G := by
    intro P hP
    obtain ⟨G, hG, -⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P
      (mem_biregularLocus_of_coheight_le_one hX g hYv.1 hgb (by rw [P.coheight_genericPoint]))
    exact ⟨G, hG⟩
  have htr' : ∀ P (hP : P ∈ Δ.support) G (hG : inverseTransformPrimeDivisor g P = some G),
      inverseTransformPrimeDivisor (p ≫ g) P = some (S' ⟨G, hidx P hP G hG⟩) := by
    intro P hP G hG
    have h1 := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      (hS'tr ⟨G, hidx P hP G hG⟩)).1
    have h2 := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hG).1
    have h3 : (p ≫ g) (S' ⟨G, hidx P hP G hG⟩).genericPoint = P.genericPoint := by
      rw [Scheme.Hom.comp_apply]
      exact (congrArg g h1).trans h2
    refine MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint h3 ?_
    rw [h3]
    exact mem_biregularLocus_of_coheight_le_one hX (p ≫ g) hY''v hg'b
      (by rw [P.coheight_genericPoint])
  -- supports of the transforms
  have hS'sub : ∀ j, ((S' j).support : Set (blowUp I)) ⊆ p ⁻¹' (Sf j).support := by
    intro j w hw
    rw [support_inverseTransformPrimeDivisor (hS'tr j)] at hw
    exact closure_minimal (fun w hw => hw.1)
      ((Sf j).idealSheaf.support.isClosed.preimage p.continuous) hw
  have hS'sup : ∀ j, p ⁻¹' (Sf j).support ⊆ ((S' j).support : Set (blowUp I)) ∪ E.support := by
    intro j w hw
    by_cases hwE : w ∈ (E.support : Set (blowUp I))
    · exact Or.inr hwE
    · left
      have hpw : p w ∉ closure {y₀} := by rwa [hEsupp] at hwE
      rw [support_inverseTransformPrimeDivisor (hS'tr j)]
      exact subset_closure ⟨hw, hpV _ hpw⟩
  have hT' : ((exceptionalSet (p ≫ g) ⊔
      (QDivisor.toRDivisor Δ).supp.preimage (p ≫ g).continuous : Closeds (blowUp I)) :
        Set (blowUp I)) = (E.support : Set (blowUp I)) ∪ ⋃ j, ((S' j).support : Set _) :=
    union_preimage_eq_of_cover p
      (D := ((QDivisor.toRDivisor Δ).supp.preimage g.continuous : Set Y)) hExg'
      ((Set.iUnion_subtype _ _).trans hS) hS'sub hS'sup
  have hEimg : E ∉ Finset.univ.image S' := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun j h => hS'E j h
  have hsum : ∑ F ∈ insert E (Finset.univ.image S'), Finsupp.single F (1 : ℤ) =
      Finsupp.single E 1 + ∑ j, Finsupp.single (S' j) 1 := by
    rw [Finset.sum_insert hEimg, Finset.sum_image (fun i _ j _ h => hS'inj h)]
  have hsncsub : IsSNCSubset ((p ≫ g) ≫ sX) (exceptionalSet (p ≫ g) ⊔
      (QDivisor.toRDivisor Δ).supp.preimage (p ≫ g).continuous) := by
    refine Or.inr ⟨insert E (Finset.univ.image S'), ?_, ?_⟩
    · rw [hT', Finset.set_biUnion_insert, Finset.set_biUnion_finset_image]
      simp
    · rwa [hsum, Category.assoc]
  -- `Ex(g ∘ p)` is of pure codimension one
  have hpure : IsPureCodimOne (exceptionalSet (p ≫ g)) := by
    let s'' := (insert E (Finset.univ.image S')).filter
      (fun F => (F.support : Set (blowUp I)) ⊆ exceptionalSet (p ≫ g))
    have hS'Ex : ∀ G (hG : G ∈ S), (G.support : Set Y) ⊆ exceptionalSet g →
        ((S' ⟨G, hG⟩).support : Set (blowUp I)) ⊆ exceptionalSet (p ≫ g) := by
      intro G hG hGEx v hv
      show v ∈ (exceptionalSet (p ≫ g) : Set (blowUp I))
      rw [hExg']
      exact Or.inl (hGEx (hS'sub ⟨G, hG⟩ hv))
    have hEEx : (E.support : Set (blowUp I)) ⊆ exceptionalSet (p ≫ g) := by
      intro v hv
      show v ∈ (exceptionalSet (p ≫ g) : Set (blowUp I))
      rw [hExg']
      exact Or.inr hv
    refine isPureCodimOne_of_eq_iUnion s'' ?_
    apply subset_antisymm
    · intro w hw
      have hw' : w ∈ (exceptionalSet (p ≫ g) : Set (blowUp I)) := hw
      rw [hExg'] at hw'
      by_cases hwE : w ∈ (E.support : Set (blowUp I))
      · exact Set.mem_iUnion₂.mpr ⟨E, Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hEEx⟩,
          hwE⟩
      rcases hw' with hw' | hw'
      · have hExcl : IsClosed (exceptionalSet g : Set Y) := (exceptionalSet g).isClosed
        obtain ⟨W, hW, hpwW⟩ := (Aux.finite_and_cover_componentsOf hExcl).2 hw'
        obtain ⟨ξ, hWξ, hξ1⟩ :=
          exists_coheight_eq_one_of_mem_componentsOf hExcl hg.isPureCodimOne_exceptionalSet hW
        set G := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξ1 with hGdef
        have hGs : (G.support : Set Y) = W := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
            AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hWξ]
        have hGS : G ∈ S := by
          refine mem_of_genericPoint_mem_iUnion hS (Or.inl ?_)
          have hξEx : ξ ∈ (exceptionalSet g : Set Y) := hW.1.2 (hWξ ▸ subset_closure rfl)
          convert hξEx using 1
          exact AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne ξ hξ1
        have hpwG : p w ∈ ((Sf ⟨G, hGS⟩).support : Set Y) := hGs ▸ hpwW
        rcases hS'sup ⟨G, hGS⟩ hpwG with h | h
        · exact Set.mem_iUnion₂.mpr ⟨S' ⟨G, hGS⟩, Finset.mem_filter.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)),
              hS'Ex G hGS (hGs ▸ hW.1.2)⟩, h⟩
        · exact absurd h hwE
      · exact absurd hw' hwE
    · exact Set.iUnion₂_subset fun F hF => (Finset.mem_filter.mp hF).2
  have hlog' : IsLogResolution sX (QDivisor.toRDivisor Δ) (p ≫ g) :=
    ⟨⟨inferInstance, hg'b, hsm''⟩, hpure, hsncsub⟩
  refine ⟨blowUp I, p ≫ g, hlog', ?_⟩
  -- the snc family on the blow-up
  let Sf' : Option S → MMP.Mori.PrimeDivisor (blowUp I) := fun o => o.elim E S'
  have hinj' : Function.Injective Sf' := by
    rintro (_ | i) (_ | j) h
    · rfl
    · exact absurd h.symm (hS'E j)
    · exact absurd h (hS'E i)
    · exact congrArg some (hS'inj h)
  have hSNC' : DivisorWithCoeffs.IsSNC ((p ≫ g) ≫ sX) (∑ o, Finsupp.single (Sf' o) (1 : ℤ)) := by
    rwa [Fintype.sum_option, Category.assoc]
  -- the points of `badSet` of `g ∘ p` lie off `E` and map to those of `g` other than `y₀`
  have key : ∀ y' ∈ badSet Δ (p ≫ g),
      p y' ∈ biregularLocus p ∧ p y' ∈ badSet Δ g ∧ p y' ≠ y₀ := by
    rintro y' ⟨P, hP, Q, hQ, hPQ, G₁, G₂, hG₁, hG₂, hy'⟩
    obtain ⟨H₁, hH₁⟩ := hexP P hP
    obtain ⟨H₂, hH₂⟩ := hexP Q hQ
    set j₁ : S := ⟨H₁, hidx P hP H₁ hH₁⟩ with hj₁
    set j₂ : S := ⟨H₂, hidx Q hQ H₂ hH₂⟩ with hj₂
    have e₁ : G₁ = S' j₁ := Option.some.inj (hG₁.symm.trans (htr' P hP H₁ hH₁))
    have e₂ : G₂ = S' j₂ := Option.some.inj (hG₂.symm.trans (htr' Q hQ H₂ hH₂))
    have hj : j₁ ≠ j₂ := by
      intro h
      have h' : H₁ = H₂ := congrArg Subtype.val h
      subst h'
      exact hPQ (eq_of_inverseTransformPrimeDivisor_eq_some hH₁ hH₂)
    have hoj : (some j₁ : Option S) ≠ some j₂ := fun h => hj (Option.some.inj h)
    have hJ' : 2 ≤ ({some j₁, some j₂} : Finset (Option S)).card := by
      rw [Finset.card_pair hoj]
    rw [e₁, e₂] at hy'
    have hy'c : closure {y'} ∈ componentsOf
        (⋂ o ∈ ({some j₁, some j₂} : Finset (Option S)), ((Sf' o).support : Set _)) := by
      rwa [iInter_pair]
    have hcoh' := coheight_eq_card_of_mem_componentsOf hY''v hsm'' hinj' hSNC' _ hJ' hy'c
    rw [Finset.card_pair hoj] at hcoh'
    have hy'G : y' ∈ ((S' j₁).support : Set _) ∩ (S' j₂).support := hy'.1.2 (subset_closure rfl)
    have hy'E : y' ∉ (E.support : Set (blowUp I)) := by
      intro h
      have hnone : (none : Option S) ∉ ({some j₁, some j₂} : Finset (Option S)) := by simp
      have hJ3 : 2 ≤ (insert none {some j₁, some j₂} : Finset (Option S)).card := by
        rw [Finset.card_insert_of_notMem hnone, Finset.card_pair hoj]
        norm_num
      have hmem3 : y' ∈ ⋂ o ∈ (insert none {some j₁, some j₂} : Finset (Option S)),
          ((Sf' o).support : Set _) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_iInter]
        rintro o (rfl | rfl | rfl)
        · exact h
        · exact hy'G.1
        · exact hy'G.2
      have := card_le_coheight_of_mem_iInter hY''v hsm'' hinj' hSNC' _ hJ3 hmem3
      rw [Finset.card_insert_of_notMem hnone, Finset.card_pair hoj, hcoh'] at this
      exact absurd this (by norm_num)
    have hpy : p y' ∉ closure {y₀} := by rwa [hEsupp] at hy'E
    have hpyV := hpV _ hpy
    have hcohp : Order.coheight (p y') = 2 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus p hpyV, hcoh']
      rfl
    have hpyH : p y' ∈ ⋂ j ∈ ({j₁, j₂} : Finset S), ((Sf j).support : Set Y) := by
      rw [iInter_pair]; exact ⟨hS'sub j₁ hy'G.1, hS'sub j₂ hy'G.2⟩
    have hJ2 : 2 ≤ ({j₁, j₂} : Finset S).card := by rw [Finset.card_pair hj]
    have hcomp := closure_singleton_mem_componentsOf hYv.1 hsmY Subtype.val_injective hSNC _ hJ2
      hpyH (by rw [hcohp, Finset.card_pair hj]; rfl)
    rw [iInter_pair] at hcomp
    exact ⟨hpyV, ⟨P, hP, Q, hQ, hPQ, H₁, H₂, hH₁, hH₂, hcomp⟩,
      fun h => hpy (h ▸ subset_closure rfl)⟩
  have hsub : p '' badSet Δ (p ≫ g) ⊆ badSet Δ g \ {y₀} := by
    rintro _ ⟨y', hy', rfl⟩
    obtain ⟨-, h1, h2⟩ := key y' hy'
    exact ⟨h1, h2⟩
  have hinjOn : Set.InjOn p (badSet Δ (p ≫ g)) := fun y₁ h₁ y₂ h₂ h =>
    injOn_preimage_biregularLocus p (show y₁ ∈ (p ⁻¹ᵁ biregularLocus p : Set _) from (key y₁ h₁).1)
      (show y₂ ∈ (p ⁻¹ᵁ biregularLocus p : Set _) from (key y₂ h₂).1) h
  calc (badSet Δ (p ≫ g)).ncard = (p '' badSet Δ (p ≫ g)).ncard :=
        hinjOn.ncard_image.symm
    _ ≤ (badSet Δ g \ {y₀}).ncard :=
        Set.ncard_le_ncard hsub ((finite_badSet Δ g).subset Set.diff_subset)
    _ < (badSet Δ g).ncard := Set.ncard_sdiff_singleton_lt_of_mem hy₀ (finite_badSet Δ g)

/-- **A log resolution with smooth boundary transform** (Kollár–Mori 2.32(2)). -/
private theorem exists_isLogResolution_isSmoothScheme [CharZero k] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) (Δ : QDivisor X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsLogResolution sX (QDivisor.toRDivisor Δ) f ∧
      IsSmoothScheme
        ((⨅ F ∈ (inverseTransformDivisor f Δ).support, F.idealSheaf).subschemeι ≫ f ≫ sX) := by
  have : PerfectField k := PerfectField.ofCharZero
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  suffices H : ∀ (N : ℕ) (Y : Scheme.{u}) (g : Y ⟶ X),
      IsLogResolution sX (QDivisor.toRDivisor Δ) g → (badSet Δ g).ncard ≤ N →
      ∃ (Y' : Scheme.{u}) (f : Y' ⟶ X), IsLogResolution sX (QDivisor.toRDivisor Δ) f ∧
        IsSmoothScheme
          ((⨅ F ∈ (inverseTransformDivisor f Δ).support, F.idealSheaf).subschemeι ≫ f ≫ sX) by
    obtain ⟨Y, g, hg⟩ := exists_isLogResolution sX hX (QDivisor.toRDivisor Δ)
    exact H _ Y g hg le_rfl
  intro N
  induction N with
  | zero =>
    intro Y g hg hN
    have : IsProper g := hg.isProper
    have hYv := (hg.toIsSmoothResolution.isNormalVariety hX).1
    have : LocallyOfFiniteType (g ≫ sX) := hYv.1.toLocallyOfFiniteType
    have : IsNoetherian Y := isNoetherian_of_isVariety hYv.1
    have : IsLocallyNoetherian Y := this.toIsLocallyNoetherian
    have h0 : badSet Δ g = ∅ :=
      (Set.ncard_eq_zero (finite_badSet Δ g)).mp (Nat.le_zero.mp hN)
    exact ⟨Y, g, hg, isSmoothScheme_of_disjoint hg (disjoint_of_badSet_eq_empty h0)⟩
  | succ N ih =>
    intro Y g hg hN
    rcases (badSet Δ g).eq_empty_or_nonempty with h0 | ⟨y₀, hy₀⟩
    · exact ih Y g hg (by
        rw [h0, Set.ncard_empty]; exact Nat.zero_le _)
    · obtain ⟨Y', g', hg', hlt⟩ := exists_step hX Δ hg hy₀
      exact ih Y' g' hg' (by omega)

end Disjoining

/-! ### Comparing the coefficients and discrepancies on a general member -/

section Main

/-- Comparison of rationals through `EReal`. -/
private theorem rat_le_of_coe_le {a b : ℚ} (h : (((a : ℚ) : ℝ) : EReal) ≤ ((b : ℝ) : EReal)) :
    a ≤ b := by
  exact_mod_cast EReal.coe_le_coe_iff.mp h

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A divisor over a normal variety is exceptional if and only if its center has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- A variety of dimension `n` with an exceptional divisor over it has `n ≥ 2`. -/
private theorem two_le_of_isExceptional [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {D : DivisorOver k sX} (hD : D.IsExceptional) : 2 ≤ n := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (D.f D.E.genericPoint)
  rw [hn] at h
  have h0 : 0 ≤ topologicalKrullDim (closure {D.f D.E.genericPoint} : Set X) :=
    Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨_, subset_closure rfl⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : ((Order.coheight (D.f D.E.genericPoint) : ℕ∞) : WithBot ℕ∞) ≤ n :=
    h ▸ le_add_of_nonneg_left h0
  exact_mod_cast ((isExceptional_iff_two_le_coheight hX D).mp hD).trans
    (WithBot.coe_le_coe.mp this)

/-- On a connected component `H⁰` of a general member, each component of `Δ|_{H⁰}` has the
coefficient of a component of `Δ`: the generic point of a prime divisor `C` of `H⁰` lies over
the biregular locus of `f`, so it lies on at most one component of `Δ`, the transforms of the
components of `Δ` being disjoint. -/
private theorem coeff_restrictComponents_eq [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {Δ : QDivisor X} {Y : Scheme.{u}} {f : Y ⟶ X}
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f) (hY : IsNormalVariety k (f ≫ sX))
    (hdisj : ∀ P ∈ Δ.support, ∀ Q ∈ Δ.support, P ≠ Q → ∀ E E' : MMP.Mori.PrimeDivisor Y,
      inverseTransformPrimeDivisor f P = some E → inverseTransformPrimeDivisor f Q = some E' →
        Disjoint (E.support : Set Y) E'.support)
    (Z : Closeds X)
    (hH : IsNormalVariety k ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX))
    (hY' : IsNormalVariety k
      (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX))
    (hbir : IsBirationalMorphism
      (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι))
    (C : MMP.Mori.PrimeDivisor (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)
    (hC : (Δ.restrictComponents (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).coeff C ≠ 0) :
    ∃ P ∈ Δ.support,
      (Δ.restrictComponents (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).coeff C =
        Δ.coeff P := by
  classical
  set ι := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι with hι
  have : IsProper f := hf.isProper
  have := hH.1.toIsIntegral
  have := hH.2
  have hfb := hf.isBirationalMorphism
  -- the generic point of `C` lies over the biregular locus of `f`
  have hηC : C.genericPoint ∈ biregularLocus (pullback.snd f ι) :=
    mem_biregularLocus_of_coheight_le_one hH _ hY'.1 hbir (by rw [C.coheight_genericPoint])
  have hx : ι C.genericPoint ∈ biregularLocus f :=
    (mem_biregularLocus_pullback_snd_iff f ι
      (fun x hx => not_subsingleton_fiber_of_notMem_biregularLocus hX f hY.1 hfb hx) _).mp hηC
  obtain ⟨y, hy⟩ := surjective_of_isBirationalMorphism f hfb (ι C.genericPoint)
  -- the generic point of `C` lies on at most one component of `Δ`
  have huniq : ∀ P ∈ Δ.support, ∀ Q ∈ Δ.support, ι C.genericPoint ∈ P.support →
      ι C.genericPoint ∈ Q.support → P = Q := by
    have htr : ∀ P : MMP.Mori.PrimeDivisor X, ι C.genericPoint ∈ P.support →
        ∃ G : MMP.Mori.PrimeDivisor Y, inverseTransformPrimeDivisor f P = some G ∧
          y ∈ G.support := by
      intro P hP
      obtain ⟨G, hG, -⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P
        (mem_biregularLocus_of_coheight_le_one hX f hY.1 hfb (by rw [P.coheight_genericPoint]))
      refine ⟨G, hG, ?_⟩
      rw [support_inverseTransformPrimeDivisor hG]
      exact subset_closure (show f y ∈ (P.idealSheaf.support : Set X) ∩ biregularLocus f by
        rw [hy]; exact ⟨hP, hx⟩)
    intro P hP Q hQ hxP hxQ
    by_contra hPQ
    obtain ⟨G, hG, hyG⟩ := htr P hxP
    obtain ⟨G', hG', hyG'⟩ := htr Q hxQ
    exact Set.disjoint_left.mp (hdisj P hP Q hQ hPQ G G' hG hG') hyG hyG'
  by_cases hfin : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff ι Δ)).Finite
  · rw [DivisorWithCoeffs.coeff_restrictComponents ι hfin C, Finsupp.sum] at hC ⊢
    obtain ⟨P, hP, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hC
    have hxP : ι C.genericPoint ∈ P.support := by
      by_contra hn
      exact hne (if_neg hn)
    refine ⟨P, hP, ?_⟩
    rw [Finset.sum_eq_single P, if_pos hxP]
    · rfl
    · intro Q hQ hQP
      rw [if_neg]
      exact fun hxQ => hQP (huniq Q hQ P hP hxQ hxP)
    · exact fun h => absurd hP h
  · exfalso
    apply hC
    rw [DivisorWithCoeffs.restrictComponents, dif_neg hfin]
    rfl

end Main

section GeneralHyperplane

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- **The discrepancy does not drop on a general member** (Kollár–Mori 5.17(1)). Let `(X, Δ)` be
a pair over an algebraically closed field `k` of characteristic zero with `dim X ≥ 2`, and
`s : ι → H⁰(X, 𝒪_X(H))` finitely many sections without common zero. There is a nonzero
polynomial `Q` such that for every `c` with `Q(c) ≠ 0` the section `σ = ∑ cᵢ sᵢ` is nonzero and,
for every connected component `Z` of `Supp (σ)₀` with its reduced structure `ι_Z : H⁰ ⟶ X`, the
scheme `H⁰` is a normal variety over `k` and `discrep(X, Δ) ≤ discrep(H⁰, Δ|_{H⁰})` for every
canonical divisor `K` of `X` and every divisor `K'` of `H⁰`. -/
@[mmp "lem_km5d_discrep_le_general_hyperplane"]
public theorem IsPair.exists_polynomial_discrep_le_discrep_restrict_connectedComponent
    [IsAlgClosed k] [CharZero k] (hdim : 2 ≤ topologicalKrullDim X)
    {Δ : QDivisor X} (hΔ : IsPair sX Δ)
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∃ hσ : (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0,
        ∀ (Z : Closeds X),
          ∀ x ∈ (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp,
          connectedComponentIn
            ((H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp : Set X) x =
            (Z : Set X) →
          ∃ hH : IsNormalVariety k ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX),
            haveI := hH.1.toIsIntegral
            haveI := hH.2
            haveI := hH.1.toLocallyOfFiniteType
            haveI := LocallyOfFiniteType.isLocallyNoetherian
              ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
            ∀ (n n' : ℕ) (K : Divisor X)
              (K' : Divisor (Scheme.IdealSheafData.vanishingIdeal Z).subscheme),
              K.IsCanonicalDivisor sX n →
              discrep sX n K Δ ≤
                discrep ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) n' K'
                  (Δ.restrictComponents (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) := by
  classical
  have hX : IsNormalVariety k sX := hΔ.isNormalVariety
  have : PerfectField k := PerfectField.ofCharZero
  obtain ⟨Y, f, hf, hsm⟩ := exists_isLogResolution_isSmoothScheme hX Δ
  obtain ⟨hYln, hYn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hf.isSmoothScheme
  obtain ⟨Ex, hEx⟩ := exists_finset_isExceptional hf
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨hsmX, hdisjX⟩ := smooth_and_disjoint_of_isSmoothScheme hf hsm
  obtain ⟨Q₁, hQ₁, h₁⟩ :=
    IsLogResolution.exists_polynomial_isLogResolution_restrict_connectedComponent hdim hΔ hf Ex
      hEx hsm s hs
  obtain ⟨hY, Q₂, hQ₂, h₂⟩ :=
    IsLogResolution.exists_polynomial_isDiscrepancy_restrict_connectedComponent_iff hdim hΔ hf Ex
      hEx hsm s hs
  refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, fun c hc => ?_⟩
  rw [map_mul] at hc
  obtain ⟨hσ, h₁c⟩ := h₁ c (left_ne_zero_of_mul hc)
  obtain ⟨hσ₂, h₂c⟩ := h₂ c (right_ne_zero_of_mul hc)
  refine ⟨hσ, fun Z x hx hZ => ?_⟩
  obtain ⟨hlog, hexc, -, hsm'⟩ := h₁c Z x hx hZ
  obtain ⟨hH, hY', hbir, hdisc⟩ := h₂c Z x hx hZ
  refine ⟨hH, ?_⟩
  set I := Scheme.IdealSheafData.vanishingIdeal Z with hI
  have := hH.1.toIsIntegral
  have := hH.2
  have := hH.1.toLocallyOfFiniteType
  have := LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ sX)
  intro n n' K K' hK
  set Δ' := Δ.restrictComponents I.subschemeι with hΔ'
  -- if `discrep(X, Δ) = -∞` there is nothing to prove
  rcases eq_or_ne (discrep sX n K Δ) ⊥ with hbot | hbot
  · rw [hbot]; exact bot_le
  -- if no exceptional divisor over `H⁰` has a discrepancy, the right side is `+∞`
  by_cases hnone : ∀ (D : DivisorOver k (I.subschemeι ≫ sX)) (b : ℚ), D.IsExceptional →
      ¬ IsDiscrepancy (I.subschemeι ≫ sX) n' K' Δ' D b
  · rw [discrep_eq_top hnone]; exact le_top
  push Not at hnone
  obtain ⟨D₀, b₀, hD₀, hb₀⟩ := hnone
  have hK' : K'.IsCanonicalDivisor (I.subschemeι ≫ sX) n' := hb₀.2.1
  have hP' : IsPairWith (I.subschemeι ≫ sX) n' K' Δ' := by
    obtain ⟨hH0, hK0, m, hm, hC, -⟩ := hb₀
    exact ⟨hH0, hK0, m, by exact_mod_cast hm.ne', hC⟩
  have hn' : 2 ≤ n' := two_le_of_isExceptional hH hK'.topologicalKrullDim_eq hD₀
  -- the pair `(X, Δ)` with the canonical divisor `K`
  have hn : 2 ≤ n := by
    have h := hK.topologicalKrullDim_eq
    rw [h] at hdim
    exact_mod_cast hdim
  have hP : IsPairWith sX n K Δ := by
    obtain ⟨-, n₀, K₀, hK₀, hQ⟩ := hΔ
    exact ⟨hX, hK, hQ.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK₀ hK)⟩
  -- the total discrepancy of `(X, Δ)` is at least `-1`
  have htot : -1 ≤ totalDiscrep sX n K Δ := by
    by_contra h
    exact hbot (discrep_eq_bot_of_totalDiscrep_lt_neg_one hP hn (lt_of_not_ge h))
  have hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P ≤ 1 := by
    intro P
    have h := htot.trans (totalDiscrep_le_neg_coeff hX
      (MMP.Positivity.IsPair.exists_isDiscrepancy hΔ hK (DivisorOver.ofPrimeDivisor k hX P)))
    have h'' : (-1 : ℚ) ≤ -Δ.coeff P :=
      rat_le_of_coe_le (by rwa [show (((-1 : ℚ) : ℝ) : EReal) = -1 by simp])
    linarith
  have hge : ∀ (D : DivisorOver k sX) (a : ℚ), D.IsExceptional →
      IsDiscrepancy sX n K Δ D a → -1 ≤ a := by
    intro D a hD ha
    have h := htot.trans (totalDiscrep_le_discrep.trans (discrep_le hD ha))
    exact rat_le_of_coe_le (by simpa using h)
  -- `discrep(X, Δ)` from the log resolution `f`
  have hYv : IsNormalVariety k (f ≫ sX) := hY
  choose aX haX using fun E : MMP.Mori.PrimeDivisor Y =>
    MMP.Positivity.IsPair.exists_isDiscrepancy hΔ hK
      (⟨Y, f, hYv, hf.isBirationalMorphism, E⟩ : DivisorOver k sX)
  have hformX := discrep_eq_min_of_isLogResolution hP hn hcoeff hf hYv hsmX hdisjX aX
    (fun E _ => haX E) (fun E hE => hge _ _ hE (haX E))
  -- `discrep(H⁰, Δ|_{H⁰})` from the log resolution `f⁰`
  obtain ⟨hsmH, hdisjH⟩ := smooth_and_disjoint_of_isSmoothScheme hlog hsm'
  have hcoeff' : ∀ C : MMP.Mori.PrimeDivisor I.subscheme, Δ'.coeff C ≤ 1 := by
    intro C
    by_cases hC : Δ'.coeff C = 0
    · rw [hC]; exact zero_le_one
    obtain ⟨P, -, hPC⟩ := coeff_restrictComponents_eq hX hf hYv hdisjX Z hH hY' hbir C hC
    rw [hPC]; exact hcoeff P
  choose aH haH using fun F : MMP.Mori.PrimeDivisor (pullback f I.subschemeι) =>
    MMP.Positivity.IsPair.exists_isDiscrepancy hP'.isPair hK'
      (⟨_, pullback.snd f I.subschemeι, hY', hlog.isBirationalMorphism, F⟩ :
        DivisorOver k (I.subschemeι ≫ sX))
  -- an exceptional prime divisor of `Y ×_X H⁰` has the discrepancy of some `Eᵢ`
  have hFE : ∀ F : MMP.Mori.PrimeDivisor (pullback f I.subschemeι),
      (⟨_, pullback.snd f I.subschemeι, hY', hlog.isBirationalMorphism, F⟩ :
        DivisorOver k (I.subschemeι ≫ sX)).IsExceptional →
      ∃ E ∈ Ex, IsDiscrepancy sX n K Δ ⟨Y, f, hYv, hf.isBirationalMorphism, E⟩ (aH F) := by
    intro F hF
    obtain ⟨E, hE, hmax⟩ := (hexc F).mp hF
    exact ⟨E, hE, ((hdisc E hE F hmax n n' K K' hK hK' (aH F)).mpr (haH F))⟩
  have hformH := discrep_eq_min_of_isLogResolution hP' hn' hcoeff' hlog hY' hsmH hdisjH aH
    (fun F _ => haH F) (fun F hF => by
      obtain ⟨E, hE, hd⟩ := hFE F hF
      exact hge ⟨Y, f, hYv, hf.isBirationalMorphism, E⟩ _ ((hEx E).mp hE) hd)
  rw [hformH]
  refine le_min (le_iInf₂ fun F hF => ?_) (le_min (le_iInf₂ fun C hC => ?_) ?_)
  · obtain ⟨E, hE, hd⟩ := hFE F hF
    exact discrep_le (D := ⟨Y, f, hYv, hf.isBirationalMorphism, E⟩) ((hEx E).mp hE) hd
  · obtain ⟨P, hP, hPC⟩ := coeff_restrictComponents_eq hX hf hYv hdisjX Z hH hY' hbir C
      (Finsupp.mem_support_iff.mp hC)
    rw [hPC, hformX]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (iInf₂_le P hP))
  · rw [hformX]
    exact (min_le_right _ _).trans (min_le_right _ _)

end GeneralHyperplane

/-! ### Points of codimension at most one -/

section CodimOne

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A point of codimension at most one of a normal variety over a perfect field is smooth. -/
private theorem mem_smoothLocus_of_coheight_le_one [PerfectField k] (hX : IsNormalVariety k sX)
    {x : X} (hx : Order.coheight x ≤ 1) : x ∈ smoothLocus sX := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rcases eq_or_ne (Order.coheight x) 1 with h1 | h1
  · have := MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hX
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1)
    have hg : MMP.Mori.PrimeDivisor.genericPoint
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1) = x :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    rwa [hg] at this
  · have h0 : Order.coheight x = 0 := Order.lt_one_iff.mp (lt_of_le_of_ne hx h1)
    have hle : x ≤ genericPoint X := by
      rw [Scheme.le_iff_specializes]; exact genericPoint_specializes x
    have hge := Order.coheight_eq_zero.mp h0 hle
    rw [Scheme.le_iff_specializes] at hge
    rw [(hge.antisymm (genericPoint_specializes x)).eq, smoothLocus_eq_smoothLocus]
    exact sX.genericPoint_mem_smoothLocus_of_perfectField

end CodimOne

/-! ### Two algebraic facts -/

section Algebra

open IsLocalRing

/-- **A local ring whose quotient by a nonzerodivisor is regular is regular.** If `g ∈ 𝔪` is a
nonzerodivisor of a Noetherian local ring `R` and `R/(g)` is regular, then `𝔪` is generated by
`g` and lifts of generators of `𝔪/(g)`, so `μ(𝔪) ≤ dim R/(g) + 1 = dim R`. -/
private theorem isRegularLocalRing_of_isRegularLocalRing_quotient {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {g : R} (hg : g ∈ nonZeroDivisors R)
    (hgm : g ∈ maximalIdeal R) (h : IsRegularLocalRing (R ⧸ Ideal.span {g})) :
    IsRegularLocalRing R := by
  classical
  set R' := R ⧸ Ideal.span {g}
  have hd := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    hg hgm
  have hsfr : ((maximalIdeal R').spanFinrank : WithBot ℕ∞) = ringKrullDim R' :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  obtain ⟨S, hcard, hS⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R')).exists_span_finset_card_eq_spanFinrank
  have hmk : Function.Surjective (Ideal.Quotient.mk (Ideal.span {g})) :=
    Ideal.Quotient.mk_surjective
  choose lift hlift using hmk
  set T : Finset R := S.image lift ∪ {g}
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {g})) = maximalIdeal R' :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hT : Ideal.span (T : Set R) = maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le]
      intro a ha
      simp only [T, Finset.coe_union, Finset.coe_image, Finset.coe_singleton, Set.mem_union,
        Set.mem_image, Finset.mem_coe, Set.mem_singleton_iff] at ha
      rcases ha with ⟨s, hs, rfl⟩ | rfl
      · by_contra hna
        have hu : IsUnit (lift s) := (IsLocalRing.notMem_maximalIdeal).mp hna
        have hs' : s ∈ maximalIdeal R' := by
          rw [← hS]; exact Submodule.subset_span hs
        rw [← hlift s] at hs'
        exact (IsLocalRing.notMem_maximalIdeal.mpr (hu.map _)) hs'
      · exact hgm
    · intro a ha
      have ha' : Ideal.Quotient.mk (Ideal.span {g}) a ∈
          (Ideal.span ((S.image lift : Finset R) : Set R)).map
            (Ideal.Quotient.mk (Ideal.span {g})) := by
        rw [Ideal.map_span, Finset.coe_image, ← Set.image_comp]
        have : ⇑(Ideal.Quotient.mk (Ideal.span {g})) ∘ lift = id := funext hlift
        rw [this, Set.image_id]
        change _ ∈ Submodule.span R' (S : Set R')
        rw [hS, ← hmap]
        exact Ideal.mem_map_of_mem _ ha
      obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
        ha'
      have hdiff : a - b ∈ Ideal.span {g} := by
        rw [← Ideal.Quotient.eq]; exact hab.symm
      have : a = b + (a - b) := by ring
      rw [this]
      refine Ideal.add_mem _ (Ideal.span_mono ?_ hb) (Ideal.span_mono ?_ hdiff)
      · intro y hy; simp only [T, Finset.coe_union]; exact Or.inl hy
      · intro y hy; simp only [T, Finset.coe_union, Finset.coe_singleton]; exact Or.inr hy
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← hT, ← hd, ← hsfr]
  have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (T.finite_toSet)
  have h2 : (T : Set R).ncard ≤ S.card + 1 := by
    rw [Set.ncard_coe_finset]
    calc T.card ≤ (S.image lift).card + ({g} : Finset R).card := Finset.card_union_le _ _
      _ ≤ S.card + 1 := by
        rw [Finset.card_singleton]
        exact Nat.add_le_add_right Finset.card_image_le 1
  rw [hcard] at h2
  exact_mod_cast h1.trans h2

/-- **A general member of a pencil through a general value.** For a nonzero polynomial `Q` in two
variables over an infinite field and an infinite set `T`, there are `μ ≠ 0` and `t ∈ T` with
`Q(-μt, μ) ≠ 0`: the polynomial `Q · X₁` does not vanish identically, which gives `μ` with
`t ↦ Q(-μt, μ)` a nonzero polynomial, and it has finitely many roots. -/
private theorem exists_eval_ne_zero_of_infinite {k : Type*} [Field k] [Infinite k]
    {Q : MvPolynomial (Fin 2) k} (hQ : Q ≠ 0) {T : Set k} (hT : T.Infinite) :
    ∃ μ : k, μ ≠ 0 ∧ ∃ t ∈ T, MvPolynomial.eval ![-(μ * t), μ] Q ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 2 → k, MvPolynomial.eval c (Q * MvPolynomial.X 1) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hQ (MvPolynomial.X_ne_zero 1)
      (MvPolynomial.funext fun c => by simpa using h c)
  rw [map_mul, MvPolynomial.eval_X] at hc
  set μ := c 1
  have hμ : μ ≠ 0 := right_ne_zero_of_mul hc
  have hQc : MvPolynomial.eval c Q ≠ 0 := left_ne_zero_of_mul hc
  let v : Fin 2 → Polynomial k := ![-(Polynomial.C μ * Polynomial.X), Polynomial.C μ]
  set p : Polynomial k := MvPolynomial.aeval v Q
  have hp : ∀ t : k, p.eval t = MvPolynomial.eval ![-(μ * t), μ] Q := by
    intro t
    rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, MvPolynomial.comp_aeval,
      ← MvPolynomial.coe_aeval_eq_eval]
    have hv : (fun i => Polynomial.aeval t (v i)) = ![-(μ * t), μ] := by
      funext i; fin_cases i <;> simp [v]
    rw [hv]
    rfl
  have hp0 : p ≠ 0 := by
    intro h0
    apply hQc
    have := hp (-(c 0) / μ)
    rw [h0, Polynomial.eval_zero] at this
    have hc' : ![-(μ * (-(c 0) / μ)), μ] = c := by
      funext i
      fin_cases i
      · simp; field_simp
      · rfl
    rw [hc'] at this
    exact this.symm
  obtain ⟨t, htT, ht⟩ := (hT.sdiff (Polynomial.finite_setOfPred_isRoot hp0)).nonempty
  exact ⟨μ, hμ, t, htT, by rwa [← hp]⟩

end Algebra

/-! ### Restriction to open subschemes -/

section OpenRestriction

open MMP.Mori Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

/-- On an integral scheme the generic point of every irreducible component is the generic
point. -/
private theorem componentGenericPoint_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z = genericPoint Y := by
  have h1 := isGenericPoint_componentGenericPoint Y Z
  rw [eq_univ_of_irreducibleComponents Z] at h1
  exact h1.eq (genericPoint_spec Y)

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint Y Z.1))).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective
      (Y.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint Y Z))).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes
        (genericPoint_specializes (componentGenericPoint Y E.component))).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes
          (genericPoint_specializes (componentGenericPoint Y E.component))).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes
            (genericPoint_specializes (componentGenericPoint Y E.component))).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

omit [IsLocallyNoetherian X] [IsNormal X] [IsDominant U.ι] in
private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

omit [IsLocallyNoetherian X] [IsNormal X] [IsDominant U.ι] in
private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The unique irreducible component `Y` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rwa [componentGenericPoint_eq_genericPoint]⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨x, hx, hxe⟩
      rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- The smooth locus of an open subscheme `U ⊆ X` lies in the smooth locus of `X`. -/
private theorem range_smoothLocus_subset (U : X.Opens) :
    Set.range ((smoothLocus (U.ι ≫ sX)).ι ≫ U.ι) ⊆ Set.range (smoothLocus sX).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 x.2
  let V := (W.ι ≫ U.ι).opensRange
  have e : (W.ι ≫ U.ι).isoOpensRange.inv ≫ (W.ι ≫ U.ι) = V.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hV : Smooth (V.ι ≫ sX) := by
    rw [← e, Category.assoc, Category.assoc]
    infer_instance
  refine le_smoothLocus sX hV ⟨⟨x.1, hxW⟩, rfl⟩

/-- On the smooth locus of a nonempty open subscheme `U`, the divisorial sheaf of `K|_U` is the
canonical sheaf when that of `K` is on the smooth locus of `X`. -/
private theorem nonempty_restrict_smoothLocus_iso {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U] [IsDominant U.ι] :
    Nonempty ((Divisor.divisorialSheaf (K.restrictOpen U)).restrict (smoothLocus (U.ι ≫ sX)).ι ≅
      canonicalSheaf (U.ι ≫ sX) n) := by
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso K U
  let T := smoothLocus (U.ι ≫ sX)
  let S := smoothLocus sX
  let ψ : T.toScheme ⟶ S := IsOpenImmersion.lift S.ι (T.ι ≫ U.ι) (range_smoothLocus_subset U)
  have hψ : ψ ≫ S.ι = T.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso ψ (S.ι ≫ sX)
    (T.ι ≫ U.ι ≫ sX) (by rw [← Category.assoc, hψ, Category.assoc]) n
  exact ⟨(Scheme.Modules.restrictFunctor T.ι).mapIso e₀ ≪≫
    (Scheme.Modules.restrictFunctorComp T.ι U.ι).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorCongr hψ.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp ψ S.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor ψ).mapIso hK.iso ≪≫ e₁⟩

/-- The restriction of a canonical divisor to a nonempty open subscheme is canonical. -/
private theorem isCanonicalDivisor_restrictOpen {n : ℕ} {K : Divisor X}
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] :
    Divisor.IsCanonicalDivisor (U.ι ≫ sX) n (K.restrictOpen U) :=
  ⟨(topologicalKrullDim_opens_eq hX U).trans hK.1, nonempty_restrict_smoothLocus_iso hK U⟩

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- The closure in `X` of a prime divisor of `U` meeting `U ∩ V` meets `V`. -/
private theorem primeDivisorMap_support_inter_nonempty (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] {V : X.Opens} (W : MMP.Mori.PrimeDivisor U.toScheme)
    (hW : (W.support ∩ U.ι ⁻¹ᵁ V).Nonempty) :
    ((OpenWeilRestriction.primeDivisorMap U.ι W).support ∩ V).Nonempty := by
  rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff]
  exact (congrArg (· ∈ V) (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W)).mpr
    ((W.genericPoint_mem_iff _).2 hW)

/-- The restriction of a Cartier divisor to a dense open subscheme is Cartier: a local equation
`φ` of `D` on `V` gives the local equation `φ|_U` of `D|_U` on `U ∩ V`, since the closure in `X`
of a prime divisor of `U` has the same local ring. -/
private theorem isCartier_restrictOpen {D : Divisor X} (h : D.IsCartier) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : Divisor.IsCartier (D.restrictOpen U) := by
  intro x
  obtain ⟨V, hxV, φ, hφ⟩ := h (U.ι x)
  obtain ⟨g, hg, hφg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  obtain ⟨φ', hφ'⟩ := MMP.Positivity.exists_units_of_ne_zero
    ((map_ne_zero (functionFieldMap U.ι)).2 hg)
  refine ⟨U.ι ⁻¹ᵁ V, hxV, φ', fun W hW => ?_⟩
  have hP := primeDivisorMap_support_inter_nonempty U W hW
  rw [DivisorWithCoeffs.coeff_restrictOpen, hφ _ hP, hφg, hφ',
    MMP.Positivity.ord_functionFieldMap_of_isIso U.ι W _
      (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- The restriction of a Cartier `ℚ`-divisor of the form `m(K + Δ)` is Cartier. -/
private theorem isCartierDivisor_smul_restrictOpen {K : Divisor X} {Δ : QDivisor X} {m : ℕ}
    (h : ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] :
    ((m : ℤ) • (Divisor.toQDivisor (K.restrictOpen U) + Δ.restrictOpen U)).IsCartierDivisor := by
  obtain ⟨D', hD', hC⟩ := h
  refine ⟨D'.restrictOpen U, ?_, isCartier_restrictOpen hC U⟩
  ext W
  have := congrArg
    (fun E => DivisorWithCoeffs.coeff E (OpenWeilRestriction.primeDivisorMap U.ι W)) hD'
  simpa using this

end OpenRestriction

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm` (nonempty, as it contains the generic point) the canonical sheaf is `𝒪_T(K_T)` for a
divisor `K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  have : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  have : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  have : IsDominant T.ι := isDominant_opens_ι T
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  have : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  have : IsIntegral T := inferInstance
  have : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso KS T
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

/-! ### Open subsets of terminal varieties -/

section TerminalOpen

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A point of an open subscheme has the same coheight in the open subscheme and in `X`. -/
private theorem coheight_ι (U : X.Opens) (y : U.toScheme) :
    Order.coheight (U.ι y) = Order.coheight y := by
  have h := ringKrullDim_eq_of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h.symm

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A point of an open subscheme is smooth exactly when it is a smooth point of `X`. -/
private theorem mem_smoothLocus_ι_iff [LocallyOfFiniteType sX] (U : X.Opens) (y : U.toScheme) :
    y ∈ smoothLocus (U.ι ≫ sX) ↔ U.ι y ∈ smoothLocus sX := by
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [smoothLocus_eq_smoothLocus, smoothLocus_eq_smoothLocus,
    ← Scheme.Hom.preimage_smoothLocus_eq]
  rfl

/-- **Open subsets of terminal varieties are terminal.** A divisor `(Y, f, E)` exceptional over
a nonempty open `U ⊆ X` is the divisor `(Y, ι ∘ f, E)` exceptional over `X`, with the same
discrepancy (`MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff`). -/
private theorem isTerminalPair_restrictOpen [IsAlgClosed k] [CharZero k] {n : ℕ}
    {K : Divisor X} (h : IsTerminalPair sX n K 0) (U : X.Opens) [Nonempty U] :
    IsTerminalPair (U.ι ≫ sX) n (K.restrictOpen U) 0 := by
  have : PerfectField k := PerfectField.ofCharZero
  have hX : IsNormalVariety k sX := h.1.1
  have := isDominant_opens_ι U
  have h0 : (0 : QDivisor X).restrictOpen U = 0 := by
    ext W; simp
  have hP : IsPairWith (U.ι ≫ sX) n (K.restrictOpen U) 0 := by
    refine ⟨isNormalVariety_ι hX U, isCanonicalDivisor_restrictOpen hX h.1.2.1 U, ?_⟩
    obtain ⟨m, hm, hC⟩ := h.1.2.2.exists_pos
    have := isCartierDivisor_smul_restrictOpen hC U
    rw [h0] at this
    exact ⟨m, by exact_mod_cast hm.ne', this⟩
  refine ⟨hP, lt_of_lt_of_le h.2 ?_⟩
  rw [le_discrep_iff]
  intro D' a hD' ha
  have := D'.isIntegral
  have := D'.isNormal
  have := D'.isLocallyNoetherian
  have hD'dom : IsDominant D'.f := D'.isBirationalMorphism.isDominant
  have hdom : IsDominant (D'.f ≫ U.ι) := inferInstance
  obtain ⟨W, hW, hWo⟩ := exists_isOpenImmersion_of_isBirationalMorphism D'.isBirationalMorphism
  have : IsOpenImmersion (W.ι ≫ D'.f ≫ U.ι) := by
    rw [← Category.assoc]; infer_instance
  let D : DivisorOver k sX :=
    { Y := D'.Y
      f := D'.f ≫ U.ι
      isNormalVariety := by rw [Category.assoc]; exact D'.isNormalVariety
      isBirationalMorphism := isBirationalMorphism_of_isOpenImmersion (D'.f ≫ U.ι) W hW
      E := D'.E }
  have hD : D.IsExceptional := by
    rw [isExceptional_iff_two_le_coheight hX]
    rw [isExceptional_iff_two_le_coheight hP.1] at hD'
    change 2 ≤ Order.coheight (U.ι (D'.f D'.E.genericPoint))
    rwa [coheight_ι]
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨D.f D.E.genericPoint,
      subset_closure ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support D'.E, rfl⟩,
      (D'.f D'.E.genericPoint).2⟩
  obtain ⟨a₀, ha₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1 D
  obtain ⟨hY'', hf'', E'', -, hval, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff h.1 D U hcen
  have ha₀' := (hiff a₀).1 ha₀
  rw [h0] at ha₀'
  have hvalD : D.valuation = D'.valuation.comap (functionFieldMap U.ι) := by
    ext t
    change D'.E.divisorialValuation (functionFieldMap (D'.f ≫ U.ι) t) =
      D'.E.divisorialValuation (functionFieldMap D'.f (functionFieldMap U.ι t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hv : D'.valuation = (DivisorOver.valuation (⟨_, D.f ∣_ U, hY'', hf'', E''⟩ :
      DivisorOver k (U.ι ≫ sX))) := by
    rw [hvalD] at hval
    obtain ⟨e, he⟩ : ∃ e : X.functionField ≃+* U.toScheme.functionField,
        ⇑e = functionFieldMap U.ι :=
      ⟨RingEquiv.ofBijective _ (functionFieldMap_opens_ι_bijective U), rfl⟩
    ext t
    have := congrArg
      (fun v : Valuation X.functionField (WithZero (Multiplicative ℤ)) => v (e.symm t)) hval
    simp only [Valuation.comap_apply] at this
    rwa [← he, RingEquiv.apply_symm_apply] at this
  have hae : a = a₀ := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hv ha ha₀'
  rw [hae]
  exact discrep_le hD ha₀

end TerminalOpen

/-! ### Points of Noetherian schemes -/

/-- The dimension of a scheme is the Krull dimension of its points under specialization. -/
private theorem topologicalKrullDim_eq_krullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- A closed subset of a Noetherian quasi-sober space all of whose points are closed is finite. -/
private theorem finite_of_forall_isClosed_singleton {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] {S : Set T} (hS : IsClosed S)
    (hpt : ∀ y ∈ S, IsClosed ({y} : Set T)) : S.Finite := by
  classical
  obtain ⟨F, hF, hSF⟩ := NoetherianSpace.exists_finset_irreducible ⟨S, hS⟩
  have hsub : S ⊆ ⋃ C ∈ F, (C : Set T) := by
    intro y hy
    have : y ∈ ((F.sup id : Closeds T) : Set T) := by rwa [← hSF]
    rw [Closeds.coe_finset_sup] at this
    simpa using this
  refine Set.Finite.subset (Set.Finite.biUnion F.finite_toSet fun C hC => ?_) hsub
  have hirr : IsIrreducible (C : Set T) := hF ⟨C, hC⟩
  have hCS : (C : Set T) ⊆ S := by
    intro y hy
    have : y ∈ ((F.sup id : Closeds T) : Set T) := by
      rw [Closeds.coe_finset_sup]
      exact Finset.le_sup (f := SetLike.coe ∘ id) hC hy
    rwa [← hSF] at this
  have hg := hirr.isGenericPoint_genericPoint_closure
  rw [C.isClosed.closure_eq] at hg
  have hgC : hirr.genericPoint ∈ (C : Set T) := hg.mem
  have hcl := hpt _ (hCS hgC)
  rw [← hg.def, hcl.closure_eq]
  exact Set.finite_singleton _

/-- On a variety of dimension `n`, every point has codimension at most `n`. -/
private theorem coheight_le_of_topologicalKrullDim_eq {X : Scheme.{u}} {n : ℕ}
    (hn : topologicalKrullDim X = n) (x : X) : Order.coheight x ≤ n := by
  have h1 := Order.coheight_le_krullDim x
  rw [← topologicalKrullDim_eq_krullDim, hn] at h1
  have h2 : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h1
  exact WithBot.coe_le_coe.mp h2

/-- In a Noetherian space, a point of a closed set `S` lies on a closed irreducible subset of `S`
that is maximal among the irreducible subsets of `S`. -/
private theorem exists_maximal_isIrreducible_subset {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] {S : Set T} (hS : IsClosed S) {p : T} (hp : p ∈ S) :
    ∃ C : Closeds T, IsIrreducible (C : Set T) ∧ p ∈ C ∧ (C : Set T) ⊆ S ∧
      ∀ Z : Set T, IsIrreducible Z → Z ⊆ S → (C : Set T) ⊆ Z → Z ⊆ C := by
  classical
  obtain ⟨F, hF, hSF⟩ := NoetherianSpace.exists_finset_irreducible (⟨S, hS⟩ : Closeds T)
  have hcov : ∀ y ∈ S, ∃ C ∈ F, y ∈ (C : Set T) := by
    intro y hy
    have : y ∈ ((F.sup id : Closeds T) : Set T) := by rwa [← hSF]
    rw [Closeds.coe_finset_sup] at this
    simpa using this
  have hsubS : ∀ C ∈ F, (C : Set T) ⊆ S := by
    intro C hC y hy
    have : y ∈ ((F.sup id : Closeds T) : Set T) := by
      rw [Closeds.coe_finset_sup]
      exact Finset.le_sup (f := SetLike.coe ∘ id) hC hy
    rwa [← hSF] at this
  obtain ⟨C₀, hC₀F, hpC₀⟩ := hcov p hp
  obtain ⟨C, hCmax⟩ := Finset.exists_maximal (s := F.filter fun C : Closeds T => p ∈ C)
    ⟨C₀, Finset.mem_filter.mpr ⟨hC₀F, hpC₀⟩⟩
  have hC := Finset.mem_filter.mp hCmax.1
  refine ⟨C, hF ⟨C, hC.1⟩, hC.2, hsubS C hC.1, fun Z hZ hZS hCZ => ?_⟩
  obtain ⟨z, hz, hZz⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ
    (F.image fun C : Closeds T => (C : Set T))
    (fun z hz => by
      obtain ⟨C', -, rfl⟩ := Finset.mem_image.mp hz
      exact C'.isClosed)
    (fun y hy => by
      obtain ⟨C', hC', hyC'⟩ := hcov y (hZS hy)
      exact Set.mem_sUnion.mpr ⟨_, Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨C', hC', rfl⟩), hyC'⟩)
  obtain ⟨C', hC'F, rfl⟩ := Finset.mem_image.mp hz
  have hCC' : C ≤ C' := fun y hy => hZz (hCZ hy)
  have hC'mem : C' ∈ F.filter fun C : Closeds T => p ∈ C :=
    Finset.mem_filter.mpr ⟨hC'F, hCC' hC.2⟩
  exact fun y hy => hCmax.2 hC'mem hCC' (hZz hy)

/-! ### Terminal surfaces -/

section Surface

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A curve on an integral surface of finite type over `k` is a prime divisor. -/
private theorem exists_primeDivisor_of_isCurveIn {Y : Scheme.{u}}
    (s : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [LocallyOfFiniteType s] [IsLocallyNoetherian Y] [IsNormal Y] (hYd : topologicalKrullDim Y = 2)
    {C : Y.IdealSheafData}
    (hC : IsCurveIn C) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, Q.idealSheaf = C ∧
      closure ({Q.genericPoint} : Set Y) = C.support := by
  have : IsIntegral C.subscheme := hC.1
  obtain ⟨c, hcC, -⟩ := hC.exists_isGenericPoint
  have hcoh : Order.coheight c = 1 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s c
    rw [hcC, ← topologicalKrullDim_subscheme_eq, hC.2, hYd] at h
    generalize Order.coheight c = d at h ⊢
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have : 1 + d = 2 := Nat.cast_injective (R := WithBot ℕ∞) (by push_cast; exact h)
      obtain rfl : d = 1 := by omega
      rfl
  let Q : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne c hcoh
  have hQξ : Q.genericPoint = c := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨Q, ?_, by rw [hQξ, hcC]⟩
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf, hQξ,
    ← vanishingIdeal_support_eq_self C]
  exact congrArg _ (TopologicalSpace.Closeds.ext hcC)

/-- **Terminal surfaces are smooth** (Kollár–Mori 4.5(1), `Δ = 0`). On a terminal surface the
singular points are closed and finitely many; on the neighbourhood of a singular point `x` where it
is the only one, the minimal resolution of the germ `(x ∈ X)` has an exceptional curve `E`, and
`a(E, X, 0) = 0` since a terminal pair is canonical, contradicting `discrep(X, 0) > 0`. -/
private theorem notMem_singularLocus_of_isTerminalPair_two [IsAlgClosed k] [CharZero k]
    {K : Divisor X} (h : IsTerminalPair sX 2 K 0) (x : X) : x ∉ singularLocus sX := by
  intro hx
  have : PerfectField k := PerfectField.ofCharZero
  have hX : IsNormalVariety k sX := h.1.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have hdim : topologicalKrullDim X = 2 := by exact_mod_cast h.1.2.1.1
  -- singular points have coheight two and are closed
  have hcoh_le : ∀ y : X, Order.coheight y ≤ 2 :=
    coheight_le_of_topologicalKrullDim_eq h.1.2.1.1
  have hsing : ∀ y ∈ (singularLocus sX : Set X), Order.coheight y = 2 := by
    intro y hy
    refine le_antisymm (hcoh_le y) ?_
    by_contra hlt
    push Not at hlt
    exact hy (mem_smoothLocus_of_coheight_le_one hX (Order.le_of_lt_add_one hlt))
  have hclosed : ∀ y ∈ (singularLocus sX : Set X), IsClosed ({y} : Set X) := by
    intro y hy
    rw [← closure_subset_iff_isClosed]
    intro y' hy'
    rw [Set.mem_singleton_iff]
    by_contra hne
    have hlt : y' < y := lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr hy'),
      fun h' => hne ((Scheme.le_iff_specializes.mp h').antisymm
        (specializes_iff_mem_closure.mpr hy')).eq⟩
    have h1 := Order.coheight_add_one_le hlt
    rw [hsing y hy] at h1
    exact absurd (h1.trans (hcoh_le y')) (by decide)
  have hfin := finite_of_forall_isClosed_singleton (singularLocus sX).isClosed hclosed
  -- the open neighbourhood of `x` on which `x` is the only singular point
  have hcl : IsClosed ((singularLocus sX : Set X) \ {x}) := by
    have := (hfin.sdiff (t := {x})).isClosed_biUnion fun y hy => hclosed y hy.1
    rwa [Set.biUnion_of_singleton] at this
  let U : X.Opens := ⟨_, hcl.isOpen_compl⟩
  have hxU : x ∈ U := fun h => h.2 rfl
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hU := isTerminalPair_restrictOpen h U
  set x' : U.toScheme := ⟨x, hxU⟩
  have hUv : IsNormalVariety k (U.ι ≫ sX) := hU.1.1
  have hUdim : topologicalKrullDim U.toScheme = 2 := by exact_mod_cast hU.1.2.1.1
  have hgerm : IsSurfaceGerm (U.ι ≫ sX) x' := by
    refine ⟨hUv, hUdim, ?_, fun y hy => ?_⟩
    · have := (hclosed x hx).preimage U.ι.continuous
      convert this using 1
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
    · rw [mem_smoothLocus_ι_iff]
      by_contra hns
      exact y.2 ⟨hns, fun h => hy (Subtype.ext h)⟩
  have hx'sing : x' ∉ smoothLocus (U.ι ≫ sX) := by
    rwa [mem_smoothLocus_ι_iff]
  obtain ⟨Y, f, hYv, hYd, ⟨hqc, hln, hn, hmin⟩, hiso⟩ :=
    MMP.Mori.exists_isMinimalSurfaceResolution (U.ι ≫ sX) hUv hUdim
  obtain ⟨C, hC⟩ : ∃ C : Y.IdealSheafData, IsExceptionalCurve f C := by
    by_contra hnone
    push Not at hnone
    exact hx'sing ((MMP.Mori.mem_smoothLocus_iff_forall_not_isExceptionalCurve (U.ι ≫ sX) hgerm f
      hmin).mpr hnone)
  have : IsIntegral Y := hYv.toIsIntegral
  have : LocallyOfFiniteType (f ≫ U.ι ≫ sX) := hYv.toLocallyOfFiniteType
  obtain ⟨E, hEC, hEcl⟩ := exists_primeDivisor_of_isCurveIn (f ≫ U.ι ≫ sX) hYd hC.1
  have hdisc := MMP.Mori.IsCanonicalPair.isDiscrepancy_zero_of_isMinimalSurfaceResolution hgerm
    (Δ := 0) (fun _ => le_rfl) hU.isCanonicalPair hmin (E := E) (hEC ▸ hC)
  -- `E` is exceptional: its image is the closed point `x'`
  obtain ⟨p, hp⟩ := hC.2
  have hηC : E.genericPoint ∈ (C.support : Set Y) := by
    rw [← hEcl]; exact subset_closure rfl
  have hfη : f E.genericPoint = p := by
    have : f E.genericPoint ∈ f.base '' (C.support : Set Y) := ⟨_, hηC, rfl⟩
    rwa [hp] at this
  have hpU : p = x' := by
    by_contra hne
    have hpsm : p ∈ smoothLocus (U.ι ≫ sX) := hgerm.2.2.2 p hne
    have hfC : ∀ a ∈ (C.support : Set Y), f a = p := fun a ha =>
      Set.mem_singleton_iff.mp (hp ▸ Set.mem_image_of_mem f.base ha)
    exact hC.1.not_subsingleton fun a ha b hb => Stacks.Models.eq_of_isIso_morphismRestrict f
      (smoothLocus (U.ι ≫ sX)) (hfC a ha ▸ hpsm) ((hfC a ha).trans (hfC b hb).symm)
  have hexc : (⟨Y, f, (hmin.1.isNormalVariety hgerm.1).1, hmin.1.isBirationalMorphism, E⟩ :
      DivisorOver k (U.ι ≫ sX)).IsExceptional := by
    rw [isExceptional_iff_two_le_coheight hUv]
    change 2 ≤ Order.coheight (f E.genericPoint)
    rw [hfη, hpU, ← coheight_ι]
    exact (hsing x hx).ge
  have h0 := lt_of_lt_of_le hU.2 (discrep_le hexc hdisc)
  exact absurd h0 (by norm_num)

end Surface

/-! ### Zero schemes of sections of divisorial sheaves -/

section ZeroSchemeBridge

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- A divisor `H` admitting finitely many sections of `𝒪_X(H)` without common zero is Cartier:
off `Supp (sᵢ)₀ = Supp (div uᵢ + H)` the divisor `H` has the local equation `uᵢ⁻¹`. -/
private theorem isCartier_of_forall_exists_notMem_supp {H : Divisor X} {ι : Type*}
    (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    H.IsCartier := by
  intro x
  obtain ⟨i, hi, hx⟩ := hs x
  refine ⟨(H.zeroDivisor (s i) hi).supp.compl, hx, ?_⟩
  set u := (Divisor.isUnit_sectionToRationalFunctions hi).unit
  refine ⟨u⁻¹, fun E ⟨y, hyE, hyU⟩ => ?_⟩
  have h0 : (H.zeroDivisor (s i) hi).coeff E = 0 := by
    by_contra hne
    exact hyU (DivisorWithCoeffs.support_subset_supp hne hyE)
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at h0
  rw [PrimeDivisor.ord_inv]
  exact eq_neg_of_add_eq_zero_right h0

attribute [local instance] isInvertible_of_isInvertibleModule

section ZeroSchemeLocal

/-- The support of the zero scheme of `t` is the support of the divisor of zeros `(t)₀`. -/
private theorem mem_supportSet_zeroScheme_iff {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (y : Y) :
    y ∈ (AlgebraicGeometry.zeroScheme Y D.divisorialSheaf t).supportSet ↔
      y ∈ (D.zeroDivisor t ht).supp := by
  obtain ⟨V, hyV, a, ha, hI, hc⟩ := exists_affine_zeroScheme_ideal_eq_span D hD t ht y
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hyV, hI, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe, Y.mem_basicOpen a y hyV]
  constructor
  · intro hna
    by_contra hy
    apply hna
    obtain ⟨c, hc'⟩ := exists_unit_stalk_of_forall_ord_eq_zero (mem_pointComponent y)
      (MMP.Threefold.Resolution.sectionUnit a ha) fun E hE => by
        have hEV : E.genericPoint ∈ (V : Y.Opens) := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
          exact (specializes_iff_mem_closure.mpr hE).mem_open (V : Y.Opens).isOpen hyV
        rw [← hc E hEV]
        by_contra hne
        exact hy (DivisorWithCoeffs.support_subset_supp hne hE)
    have hZ : componentGenericPoint Y (pointComponent y) ∈ (V : Y.Opens) :=
      ((isGenericPoint_componentGenericPoint Y _).specializes
        (mem_pointComponent y)).mem_open (V : Y.Opens).isOpen hyV
    have heq : (Y.presheaf.germ V y hyV).hom a = c := by
      apply stalkToRationalFunctions_injective (mem_pointComponent y)
      rw [hc', MMP.Threefold.Resolution.sectionUnit_apply a ha _ hZ]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    exact heq ▸ c.isUnit
  · intro hy hu
    obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
    have hηE : E.genericPoint ⤳ y := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hEV : E.genericPoint ∈ (V : Y.Opens) := hηE.mem_open (V : Y.Opens).isOpen hyV
    have hyB : y ∈ Y.basicOpen a := (Y.mem_basicOpen a y hyV).mpr hu
    have hEB : E.genericPoint ∈ Y.basicOpen a := hηE.mem_open (Y.basicOpen a).isOpen hyB
    exact hE ((hc E hEV).trans (MMP.Threefold.Resolution.ord_sectionUnit_eq_zero a ha E hEV
      ((Y.mem_basicOpen a _ hEV).mp hEB)))

end ZeroSchemeLocal

/-! ### Normality of a connected component -/

/-- The points of `Supp D` off a connected component `Z` of it form a closed set. -/
private theorem isClosed_supp_diff_connectedComponentIn {Y : Scheme.{u}} (D : Divisor Y)
    {Z : Closeds Y} {x₀ : Y} (hZ : connectedComponentIn (D.supp : Set Y) x₀ = (Z : Set Y)) :
    IsClosed ((D.supp : Set Y) \ Z) := by
  classical
  have heq : (D.supp : Set Y) \ Z =
      ⋃ E ∈ D.support.filter (fun E => Disjoint E.support (Z : Set Y)), E.support := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨hy, hyZ⟩
      obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
      refine ⟨E, ⟨Finsupp.mem_support_iff.mpr hE, ?_⟩, hyE⟩
      rw [Set.disjoint_left]
      intro y' hy'E hy'Z
      have hirr : _root_.IsPreconnected E.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isPreconnected_singleton.closure
      have hsub : E.support ⊆ (D.supp : Set Y) := fun z hz =>
        DivisorWithCoeffs.support_subset_supp hE hz
      have hcc : connectedComponentIn (D.supp : Set Y) y' = Z := by
        rw [← hZ]; exact (connectedComponentIn_eq (hZ ▸ hy'Z)).symm
      have := hirr.subset_connectedComponentIn hy'E hsub hyE
      rw [hcc] at this
      exact hyZ this
    · rintro ⟨E, ⟨hE, hdisj⟩, hyE⟩
      exact ⟨DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE) hyE,
        Set.disjoint_left.mp hdisj hyE⟩
  rw [heq]
  exact (Finset.finite_toSet _).isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **A component of a normal member is locally principal.** If the zero scheme of a nonzero
section `t` of `𝒪_X(D)` is normal and `Z` is a connected component of `Supp (t)₀`, the ideal of
`Z` at a point `x ∈ Z` is generated by a nonzero non-unit `g`: near `Z` the zero scheme is
reduced, hence equal to `Z` with its reduced structure, and it is cut out by one equation. -/
private theorem exists_stalk_vanishingIdeal_eq_span (D : Divisor X) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule X D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0)
    (hnorm : IsNormal (AlgebraicGeometry.zeroScheme X D.divisorialSheaf t).subscheme)
    (Z : Closeds X) (x₀ : X)
    (hZ : connectedComponentIn ((D.zeroDivisor t ht).supp : Set X) x₀ = (Z : Set X))
    {x : X} (hxZ : x ∈ (Z : Set X)) :
    ∃ g : X.presheaf.stalk x, g ≠ 0 ∧ g ∈ IsLocalRing.maximalIdeal _ ∧
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z) x = Ideal.span {g} := by
  classical
  set zs := AlgebraicGeometry.zeroScheme X D.divisorialSheaf t with hzs_def
  have : IsReduced zs.subscheme := @isReduced_of_isNormal _ hnorm
  have hsupp : zs.support = (D.zeroDivisor t ht).supp := by
    ext y
    exact mem_supportSet_zeroScheme_iff D hD t ht y
  have hzs : zs = Scheme.IdealSheafData.vanishingIdeal (D.zeroDivisor t ht).supp :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme zs _ hsupp
  have hZD : (Z : Set X) ⊆ (D.zeroDivisor t ht).supp := hZ ▸ connectedComponentIn_subset _ _
  have hcl := isClosed_supp_diff_connectedComponentIn (D.zeroDivisor t ht) hZ
  -- near `Z`, the ideals of the zero scheme and of `Z` agree
  have hstalk : IdealSheafData.stalk zs x =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z) x := by
    rw [hzs]
    refine MMP.Mori.stalk_vanishingIdeal_eq_of_inter_eq _ _
      (U := ⟨_, hcl.isOpen_compl⟩) (fun h => h.2 hxZ) ?_
    ext y
    simp only [Set.mem_inter_iff, Opens.coe_mk, Set.mem_compl_iff, Set.mem_sdiff, not_and,
      not_not]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₂ h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨hZD h₁, h₂⟩⟩
  obtain ⟨V, hxV, a, ha, hIa, -⟩ := exists_affine_zeroScheme_ideal_eq_span D hD t ht x
  have hst : IdealSheafData.stalk zs x = Ideal.span {(X.presheaf.germ V x hxV).hom a} :=
    IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span hxV hIa
  refine ⟨(X.presheaf.germ V x hxV).hom a, ?_, ?_, hstalk ▸ hst⟩
  · intro h0
    let Z₀ : irreducibleComponents X := pointComponent x
    have hsp := (isGenericPoint_componentGenericPoint X Z₀).specializes (mem_pointComponent x)
    apply ha Z₀ (hsp.mem_open (V : X.Opens).isOpen hxV)
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxV hsp, h0, map_zero]
  · have hxs : x ∈ zs.support := by rw [hsupp]; exact hZD hxZ
    have hne := (IdealSheafData.stalk_eq_top_iff_notMem_support zs x).not.mpr (not_not.mpr hxs)
    rw [hst] at hne
    by_contra hm
    exact hne ((Ideal.span_singleton_eq_top).mpr ((IsLocalRing.notMem_maximalIdeal).mp hm))

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **The local ring of a component of a normal member.** In the situation of
`exists_stalk_vanishingIdeal_eq_span`, the local ring of `Z` at a point `z` is `𝒪_{X,z}/(g)` for
a nonzero non-unit `g`. -/
private theorem exists_ringEquiv_stalk_quotient (D : Divisor X) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule X D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0)
    (hnorm : IsNormal (AlgebraicGeometry.zeroScheme X D.divisorialSheaf t).subscheme)
    (Z : Closeds X) (x₀ : X)
    (hZ : connectedComponentIn ((D.zeroDivisor t ht).supp : Set X) x₀ = (Z : Set X))
    (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :
    ∃ g : X.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι z),
      g ≠ 0 ∧ g ∈ IsLocalRing.maximalIdeal _ ∧
      Nonempty ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme.presheaf.stalk z ≃+*
        X.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι z) ⧸
          Ideal.span {g}) := by
  have hxZ : (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι z ∈ (Z : Set X) := by
    rw [← Scheme.IdealSheafData.coe_support_vanishingIdeal,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  obtain ⟨g, hg0, hgm, hst⟩ := exists_stalk_vanishingIdeal_eq_span D hD t ht hnorm Z x₀ hZ hxZ
  refine ⟨g, hg0, hgm, ⟨(RingHom.quotientKerEquivOfSurjective
    ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.stalkMap_surjective z)).symm.trans
      (Ideal.quotEquivOfEq ?_)⟩⟩
  rw [IdealSheafData.ker_stalkMap_subschemeι, hst]

section Bertini

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **Bertini: the general member is normal.** For a general member `(σ)₀` of a free linear
system on a normal variety of dimension at least two over an algebraically closed field of
characteristic zero, the zero scheme of `σ` is normal. -/
private theorem exists_polynomial_isNormal_zeroScheme [IsAlgClosed k] [CharZero k]
    (hdim : 2 ≤ topologicalKrullDim X) (hX : IsNormalVariety k sX)
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    haveI := (isCartier_of_forall_exists_notMem_supp s hs).isInvertibleModule_divisorialSheaf
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0 →
      IsNormal (AlgebraicGeometry.zeroScheme X H.divisorialSheaf
        (∑ i, scalarsToGlobalSections k sX (c i) • s i)).subscheme := by
  classical
  let : X.Over (Spec (.of k)) := ⟨sX⟩
  have : AlgebraicGeometry.IsVariety k (X ↘ Spec (.of k)) := hX.1
  have hHc := isCartier_of_forall_exists_notMem_supp s hs
  have hL := hHc.isInvertibleModule_divisorialSheaf
  obtain ⟨i₀, -, -⟩ := hs (Nonempty.some inferInstance)
  set N := Fintype.card ι - 1
  have hcard : Fintype.card ι = N + 1 := by
    have := Fintype.card_pos_iff.mpr ⟨i₀⟩
    omega
  let e : ι ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  let s' : Fin (N + 1) → Γ(H.divisorialSheaf, ⊤) := fun j => s (e.symm j)
  have hsys : ∀ c : ι → k, MMP.Threefold.Bridges.systemSection (k := k) s' (c ∘ e.symm) =
      ∑ i, scalarsToGlobalSections k sX (c i) • s i := by
    intro c
    rw [MMP.Threefold.Bridges.systemSection_apply]
    exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)
  have hs' : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen X H.divisorialSheaf
      (MMP.Threefold.Bridges.systemSection s' c) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨i, hi, hy⟩ := hs y
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single (e i) 1, ?_⟩
    have h1 : MMP.Threefold.Bridges.systemSection (k := k) s' (Pi.single (e i) 1) = s i := by
      rw [MMP.Threefold.Bridges.systemSection_apply,
        Finset.sum_eq_single (e i) (fun j _ hj => by simp [hj]) (by simp)]
      simp only [s', Equiv.symm_apply_apply, Pi.single_eq_same]
      exact one_smul k _
    rw [h1]
    exact mem_nonvanishingOpen_of_notMem_supp H hHc (s i) hi y hy
  obtain ⟨U, hU, hUc⟩ :=
    MMP.Threefold.Bridges.exists_dense_open_isNormal_zeroScheme_of_two_le_topologicalKrullDim
      hdim s' hs'
  obtain ⟨Q', hQ'0, hQ'⟩ := exists_polynomial_dualPoint_mem U hU
  refine ⟨MvPolynomial.rename e.symm Q', fun h => hQ'0
    (MvPolynomial.rename_injective _ e.symm.injective (h.trans (map_zero _).symm)),
    fun c hc hσ => ?_⟩
  rw [MvPolynomial.eval_rename] at hc
  have hc0 : c ∘ e.symm ≠ 0 := by
    intro h0
    apply hσ
    rw [← hsys, h0, map_zero]
    rfl
  have hnorm := hUc (c ∘ e.symm) hc0 (hQ' _ hc0 hc)
  rw [hsys] at hnorm
  exact hnorm

end Bertini

end ZeroSchemeBridge

/-! ### Values of regular functions at closed points -/

section ClosedPoints

open IsLocalRing

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The germ of the image of a scalar is its image under the stalk algebra structure. -/
private theorem germ_scalarsToGlobalSections (w : X) (t : k) :
    letI := MMP.Mori.stalkAlgebra sX w
    (X.presheaf.germ ⊤ w trivial).hom (scalarsToGlobalSections k sX t) =
      algebraMap k (X.presheaf.stalk w) t :=
  rfl

/-- If `b - t` vanishes at `w` and `t ≠ t'`, then `b - t'` does not vanish at `w`. -/
private theorem mem_basicOpen_sub_of_ne {w : X} {b : Γ(X, ⊤)} {t t' : k}
    (h : w ∉ X.basicOpen (b - scalarsToGlobalSections k sX t)) (hne : t ≠ t') :
    w ∈ X.basicOpen (b - scalarsToGlobalSections k sX t') := by
  rw [Scheme.mem_basicOpen_top] at h ⊢
  by_contra h'
  have h1 := (mem_maximalIdeal _).mpr h
  have h2 := (mem_maximalIdeal _).mpr h'
  have h3 : (X.presheaf.germ ⊤ w trivial).hom (b - scalarsToGlobalSections k sX t') -
      (X.presheaf.germ ⊤ w trivial).hom (b - scalarsToGlobalSections k sX t) ∈
        maximalIdeal (X.presheaf.stalk w) := Ideal.sub_mem _ h2 h1
  rw [← map_sub, show b - scalarsToGlobalSections k sX t' - (b - scalarsToGlobalSections k sX t)
    = scalarsToGlobalSections k sX (t - t') by rw [map_sub]; ring] at h3
  have hu : IsUnit (scalarsToGlobalSections k sX (t - t')) :=
    (Ne.isUnit (sub_ne_zero.mpr hne)).map _
  exact (mem_maximalIdeal _).mp h3 (hu.map _)

/-- **Closed points have values in `k`.** At a closed point `w` of a scheme locally of finite type
over an algebraically closed field `k`, every regular function `b` takes a value `t ∈ k`: `b - t`
vanishes at `w`, since the residue field at `w` is finite over `k`, hence `k`. -/
private theorem exists_notMem_basicOpen_sub [IsAlgClosed k] [LocallyOfFiniteType sX] {w : X}
    (hw : IsClosed ({w} : Set X)) (b : Γ(X, ⊤)) :
    ∃ t : k, w ∉ X.basicOpen (b - scalarsToGlobalSections k sX t) := by
  let := MMP.Mori.stalkAlgebra sX w
  have hfin := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX w hw
  have hsurj : Function.Surjective (algebraMap k (ResidueField (X.presheaf.stalk w))) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
  obtain ⟨t, ht⟩ := hsurj (residue _ ((X.presheaf.germ ⊤ w trivial).hom b))
  refine ⟨t, ?_⟩
  rw [Scheme.mem_basicOpen_top, map_sub, germ_scalarsToGlobalSections]
  intro hu
  have h0 : residue _ ((X.presheaf.germ ⊤ w trivial).hom b - algebraMap k _ t) = 0 := by
    rw [map_sub, ← ht, IsScalarTower.algebraMap_apply k (X.presheaf.stalk w)
      (ResidueField (X.presheaf.stalk w)), ResidueField.algebraMap_eq, sub_self]
  rw [residue_eq_zero_iff] at h0
  exact (mem_maximalIdeal _).mp h0 hu

/-- **Two closed points with different values.** On an affine scheme of finite type over an
algebraically closed field, the closure of a non-closed point contains two closed points `w₁, w₂`
at which some regular function `a` takes different values `t₁ ≠ t₂`. -/
private theorem exists_closedPoints_values_ne [IsAlgClosed k] [LocallyOfFiniteType sX]
    [IsAffine X] {x : X} (hx : ¬ IsClosed ({x} : Set X)) :
    ∃ (a : Γ(X, ⊤)) (w₁ w₂ : X) (t₁ t₂ : k), x ⤳ w₁ ∧ x ⤳ w₂ ∧ IsClosed ({w₁} : Set X) ∧
      IsClosed ({w₂} : Set X) ∧ w₁ ∉ X.basicOpen (a - scalarsToGlobalSections k sX t₁) ∧
      w₂ ∉ X.basicOpen (a - scalarsToGlobalSections k sX t₂) ∧ t₁ ≠ t₂ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hW : IsLocallyClosed (closure ({x} : Set X)) := isClosed_closure.isLocallyClosed
  obtain ⟨w₁, hw₁W, hw₁⟩ := nonempty_inter_closedPoints
    (⟨x, subset_closure (Set.mem_singleton x)⟩ : (closure ({x} : Set X)).Nonempty) hW
  -- a second closed point
  obtain ⟨w₂, hw₂W, hw₂, hne⟩ : ∃ w₂ ∈ closure ({x} : Set X), IsClosed ({w₂} : Set X) ∧
      w₂ ≠ w₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : closure ({x} : Set X) ∩ closedPoints X ⊆ {w₁} := fun w hw =>
      hcon w hw.1 hw.2
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure hW
    rw [closure_closure] at this
    have hx1 : x ∈ ({w₁} : Set X) := by
      have := closure_mono hsub
      rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hW, closure_closure,
        (show IsClosed ({w₁} : Set X) from hw₁).closure_eq] at this
      exact this (subset_closure rfl)
    rw [Set.mem_singleton_iff.mp hx1] at hx
    exact hx hw₁
  -- a function vanishing at `w₁` but not at `w₂`
  obtain ⟨a, hale, haw₂⟩ := (isAffineOpen_top X).exists_basicOpen_le
    (V := ⟨_, (show IsClosed ({w₁} : Set X) from hw₁).isOpen_compl⟩)
    ⟨w₂, hne⟩ trivial
  have haw₁ : w₁ ∉ X.basicOpen a := fun h => hale h rfl
  obtain ⟨t₂, ht₂⟩ := exists_notMem_basicOpen_sub (sX := sX) hw₂ a
  refine ⟨a, w₁, w₂, 0, t₂, specializes_iff_mem_closure.mpr hw₁W,
    specializes_iff_mem_closure.mpr hw₂W, hw₁, hw₂, by simpa using haw₁, ht₂, ?_⟩
  rintro rfl
  exact ht₂ (by simpa using haw₂)

/-- **A regular function non-constant on an irreducible closed set takes infinitely many values
there.** If `a` takes different values at two closed points of `W = closure {x}`, the set of
values of `a` at closed points of `W` is infinite: otherwise the closed points of `W`, which are
dense, would lie in the finite union of the closed sets `{a = t}`, and `W` in one of them. -/
private theorem infinite_setOf_values [LocallyOfFiniteType sX] [IsAlgClosed k] {x : X}
    {a : Γ(X, ⊤)} {w₁ w₂ : X} {t₁ t₂ : k} (h₁ : x ⤳ w₁) (h₂ : x ⤳ w₂)
    (hw₁ : w₁ ∉ X.basicOpen (a - scalarsToGlobalSections k sX t₁))
    (hw₂ : w₂ ∉ X.basicOpen (a - scalarsToGlobalSections k sX t₂)) (hne : t₁ ≠ t₂) :
    {t : k | ∃ w : X, x ⤳ w ∧ IsClosed ({w} : Set X) ∧
      w ∉ X.basicOpen (a - scalarsToGlobalSections k sX t)}.Infinite := by
  intro hfin
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  set T := {t : k | ∃ w : X, x ⤳ w ∧ IsClosed ({w} : Set X) ∧
      w ∉ X.basicOpen (a - scalarsToGlobalSections k sX t)}
  have hW : IsLocallyClosed (closure ({x} : Set X)) := isClosed_closure.isLocallyClosed
  have hsub : closure ({x} : Set X) ⊆
      ⋃ t ∈ T, X.zeroLocus {a - scalarsToGlobalSections k sX t} := by
    rw [← closure_closure (s := ({x} : Set X)),
      ← JacobsonSpace.closure_inter_closedPoints_eq_closure hW]
    refine closure_minimal ?_ (hfin.isClosed_biUnion fun t _ => X.zeroLocus_isClosed _)
    rintro w ⟨hwW, hwc⟩
    obtain ⟨t, ht⟩ := exists_notMem_basicOpen_sub (sX := sX) hwc a
    refine Set.mem_iUnion₂.mpr ⟨t, ⟨w, specializes_iff_mem_closure.mpr hwW, hwc, ht⟩, ?_⟩
    rw [Scheme.zeroLocus_singleton]
    exact ht
  classical
  obtain ⟨z, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp isIrreducible_singleton.closure
    (hfin.toFinset.image fun t => X.zeroLocus {a - scalarsToGlobalSections k sX t})
    (fun z hz => by
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hz
      exact X.zeroLocus_isClosed _)
    (by
      refine hsub.trans fun w hw => ?_
      obtain ⟨t, ht, hwt⟩ := Set.mem_iUnion₂.mp hw
      exact Set.mem_sUnion.mpr ⟨_, Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨t, hfin.mem_toFinset.mpr ht, rfl⟩), hwt⟩)
  obtain ⟨t₀, -, rfl⟩ := Finset.mem_image.mp hz
  have hval : ∀ {w : X} {t : k}, x ⤳ w →
      w ∉ X.basicOpen (a - scalarsToGlobalSections k sX t) → t = t₀ := by
    intro w t hw hwt
    by_contra hne
    have := hWz (specializes_iff_mem_closure.mp hw)
    rw [Scheme.zeroLocus_singleton] at this
    exact this (mem_basicOpen_sub_of_ne hwt hne)
  exact hne ((hval h₁ hw₁).trans (hval h₂ hw₂).symm)

end ClosedPoints

/-! ### Krull's principal ideal theorem on the closure of a point -/

section PrincipalIdeal

/-- If `a + c = N` in `WithBot ℕ∞` with `N` a natural number, then `a` and `c` are natural
numbers. -/
private theorem exists_nat_of_add_eq {a : WithBot ℕ∞} {c : ℕ∞} {N : ℕ}
    (h : a + (c : WithBot ℕ∞) = N) : ∃ d e : ℕ, a = d ∧ c = e ∧ d + e = N := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (((⊤ : ℕ∞) + c : ℕ∞) : WithBot ℕ∞) = ((N : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]; exact_mod_cast h
      have h'' := WithBot.coe_injective h'
      simp at h''
    | coe d =>
      induction c using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((d : ℕ∞) + ⊤ : ℕ∞) = (N : ℕ∞) := by exact_mod_cast h
        simp at this
      | coe e =>
        refine ⟨d, e, rfl, rfl, ?_⟩
        have : ((d + e : ℕ) : WithBot ℕ∞) = (N : WithBot ℕ∞) := by exact_mod_cast h
        exact_mod_cast this

variable {k : Type u} [Field k]

/-- **Codimension of a hypersurface section of the closure of a point.** Let `X` be an affine
integral scheme of finite type over `k` of dimension `N`, `r` a regular function not vanishing at
`x` and vanishing at a specialization `w` of `x`. Then some specialization `x'` of `x` at which `r`
vanishes has codimension at most one more than `x`: take `x'` the generic point of an irreducible
component through `w` of `V(r) ∩ closure {x}`, which has dimension `dim closure {x} - 1` by Krull's
principal ideal theorem (`MMP.hasDim_of_maximal_isIrreducible_zeroLocus`). -/
private theorem exists_specializes_notMem_basicOpen_coheight_le {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsAffine X] [LocallyOfFiniteType sX] {N : ℕ}
    (hN : topologicalKrullDim X = N) {x w : X} (hxw : x ⤳ w) {r : Γ(X, ⊤)}
    (hx : x ∈ X.basicOpen r) (hw : w ∉ X.basicOpen r) :
    ∃ x' : X, x ⤳ x' ∧ x' ∉ X.basicOpen r ∧ Order.coheight x' ≤ Order.coheight x + 1 := by
  classical
  let W : Closeds X := ⟨closure {x}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal W
  have hrange : Set.range I.subschemeι = closure {x} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨xt, hxt⟩ : x ∈ Set.range I.subschemeι := hrange ▸ subset_closure rfl
  obtain ⟨wt, hwt⟩ : w ∈ Set.range I.subschemeι :=
    hrange ▸ specializes_iff_mem_closure.mp hxw
  have hemb := I.subschemeι.isClosedEmbedding
  have hcl : closure ({xt} : Set I.subscheme) = Set.univ := by
    rw [hemb.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hxt, ← hrange,
      Set.preimage_range]
  have : IrreducibleSpace I.subscheme := (irreducibleSpace_def _).mpr (by
    have := (isIrreducible_singleton (x := xt)).closure
    rwa [hcl, ← Set.top_eq_univ] at this)
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ sX⟩
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ sX))
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ sX)
  have : IsNoetherian I.subscheme := {}
  -- dimensions
  have hdimX := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  rw [hN] at hdimX
  obtain ⟨d, e, hd, he, hde⟩ := exists_nat_of_add_eq hdimX
  have hdimW : MMP.Intersection.HasDim I.subscheme d := by
    refine ⟨d, rfl, ?_⟩
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hd
  -- the function `r` on `closure {x}`
  set a : Γ(I.subscheme, ⊤) := I.subschemeι.appTop r with ha_def
  have hbo : ∀ y : I.subscheme, y ∈ I.subscheme.basicOpen a ↔ I.subschemeι y ∈ X.basicOpen r := by
    intro y
    change y ∈ I.subscheme.basicOpen ((I.subschemeι.app ⊤).hom r) ↔ _
    rw [← Scheme.preimage_basicOpen]
    rfl
  have ha0 : a ≠ 0 := by
    intro h0
    have := (hbo xt).mpr (hxt ▸ hx)
    rw [h0, Scheme.basicOpen_zero] at this
    exact this
  have hwtS : wt ∈ I.subscheme.zeroLocus {a} := by
    rw [Scheme.zeroLocus_singleton]
    exact fun h => hw (hwt ▸ (hbo wt).mp h)
  -- an irreducible component of `V(a)` through `wt`
  obtain ⟨C, hCirr, -, hCS, hCmax⟩ :=
    exists_maximal_isIrreducible_subset (I.subscheme.zeroLocus_isClosed {a}) hwtS
  have hmax : Maximal (fun Z : Set I.subscheme => IsIrreducible Z ∧
      Z ⊆ I.subscheme.zeroLocus {a} ∩ ↑(⊤ : I.subscheme.Opens)) (C : Set I.subscheme) :=
    ⟨⟨hCirr, fun y hy => ⟨hCS hy, trivial⟩⟩,
      fun Z hZ hCZ => hCmax Z hZ.1 (fun y hy => (hZ.2 hy).1) hCZ⟩
  have hdimC := MMP.hasDim_of_maximal_isIrreducible_zeroLocus k hdimW
    (isAffineOpen_top I.subscheme) ha0 hmax
  obtain ⟨m, hm, hmC⟩ := hdimC
  -- the generic point of the component
  set t := hCirr.genericPoint
  have ht : closure ({t} : Set I.subscheme) = C := by
    have := hCirr.isGenericPoint_genericPoint_closure
    rw [C.isClosed.closure_eq] at this
    exact this
  refine ⟨I.subschemeι t, ?_, ?_, ?_⟩
  · have : I.subschemeι t ∈ Set.range I.subschemeι := ⟨t, rfl⟩
    rw [hrange] at this
    exact specializes_iff_mem_closure.mpr this
  · have htS : t ∈ I.subscheme.zeroLocus {a} := hCS (ht ▸ subset_closure rfl)
    rw [Scheme.zeroLocus_singleton] at htS
    exact fun h => htS ((hbo t).mpr h)
  · have hcl' : closure ({I.subschemeι t} : Set X) = I.subschemeι '' C := by
      rw [← Set.image_singleton, hemb.closure_image_eq, ht]
    have hdimx' := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
      (I.subschemeι t)
    rw [hN, hcl', ← (hemb.isEmbedding.homeomorphImage
      (C : Set I.subscheme)).isHomeomorph.topologicalKrullDim_eq, hmC] at hdimx'
    obtain ⟨m', e', hm', he', hme'⟩ := exists_nat_of_add_eq hdimx'
    have hmm' : m = m' := by exact_mod_cast hm'
    rw [he', he]
    have : e' = e + 1 := by omega
    rw [this]
    push_cast
    exact le_rfl

end PrincipalIdeal

/-! ### Divisors of zeros of regular functions -/

section RegularSection

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- The support of the divisor of zeros of a regular function `r`, read as a section of
`𝒪_X(0)`, is the zero locus of `r`: a point lies on a prime divisor along which `r` vanishes
exactly when `r` is not a unit at it (`X` is normal). -/
private theorem mem_supp_zeroDivisor_algebraMap_iff (r : Γ(X, ⊤))
    (hr : (⟨algebraMap Γ(X, ⊤) _ r, Divisor.isDivisorialSection_algebraMap le_rfl r⟩ :
      (0 : Divisor X).divisorialSubmodule ⊤) ≠ 0)
    (y : X) :
    y ∈ ((0 : Divisor X).zeroDivisor _ hr).supp ↔ y ∉ X.basicOpen r := by
  classical
  set u := (Divisor.isUnit_sectionToRationalFunctions hr).unit
  have hval : ∀ Z : irreducibleComponents X, (u : RationalFunctions X) Z =
      (X.presheaf.germ ⊤ (componentGenericPoint X Z) trivial).hom r := fun Z => rfl
  have ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ (⊤ : X.Opens)),
      (X.presheaf.germ ⊤ _ hZ).hom r ≠ 0 := by
    intro Z hZ h0
    have hu := (Pi.isUnit_iff.mp u.isUnit) Z
    rw [hval Z, h0] at hu
    exact not_isUnit_zero hu
  have hsu : u = MMP.Threefold.Resolution.sectionUnit r ha := by
    ext Z
    rw [hval Z, MMP.Threefold.Resolution.sectionUnit_apply r ha Z trivial]
  have hc : ∀ E : MMP.Mori.PrimeDivisor X, ((0 : Divisor X).zeroDivisor _ hr).coeff E =
      E.ord (MMP.Threefold.Resolution.sectionUnit r ha) := by
    intro E
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
      DivisorWithCoeffs.coeff_zero, add_zero, ← hsu]
  constructor
  · intro hy hyB
    obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
    have hηE : E.genericPoint ⤳ y := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hEB : E.genericPoint ∈ X.basicOpen r := hηE.mem_open (X.basicOpen r).isOpen hyB
    exact hE ((hc E).trans (MMP.Threefold.Resolution.ord_sectionUnit_eq_zero r ha E trivial
      ((X.mem_basicOpen_top r _).mp hEB)))
  · intro hy
    by_contra hns
    apply hy
    obtain ⟨c, hc'⟩ := exists_unit_stalk_of_forall_ord_eq_zero (mem_pointComponent y)
      (MMP.Threefold.Resolution.sectionUnit r ha) fun E hE => by
        rw [← hc E]
        by_contra hne
        exact hns (DivisorWithCoeffs.support_subset_supp hne hE)
    have heq : (X.presheaf.germ ⊤ y trivial).hom r = c := by
      apply stalkToRationalFunctions_injective (mem_pointComponent y)
      rw [hc', MMP.Threefold.Resolution.sectionUnit_apply r ha _ trivial]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [X.mem_basicOpen_top]
    exact heq ▸ c.isUnit

end RegularSection

/-! ### Exceptional divisors over singular points -/

section ExceptionalOverSingular

variable {k : Type u} [Field k]

/-- The biregular locus of a morphism from a smooth scheme lies in the smooth locus. -/
private theorem biregularLocus_le_smoothLocus {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType (f ≫ sX)]
    (hY : IsSmoothScheme (f ≫ sX)) : biregularLocus f ≤ smoothLocus sX := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
  have : Smooth (f ≫ sX) := (isSmoothScheme_iff _).1 hY
  have h : Smooth ((f ∣_ V) ≫ V.ι ≫ sX) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have e : V.ι ≫ sX = inv (f ∣_ V) ≫ ((f ∣_ V) ≫ V.ι ≫ sX) := by simp
  refine le_smoothLocus _ ?_
  rw [e]
  infer_instance

/-- **A log resolution has an exceptional divisor over every singular point.** Let `g : P ⟶ Z`
be a log resolution of a normal variety `Z` and `z` a singular point of `Z`. Then `g` is not an
isomorphism over `z` (`P` is smooth), so the exceptional set, of pure codimension one, contains a
prime divisor `F`; its image is not in the biregular locus, so it has codimension at least two
(a codimension-one point of the normal `Z` is in the biregular locus), and `F` is
`g`-exceptional. -/
private theorem exists_isExceptional_of_notMem_smoothLocus {Z P : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : IsNormalVariety k sZ) {D : RDivisor Z} {g : P ⟶ Z} (hg : IsLogResolution sZ D g)
    {z : Z} (hz : z ∉ smoothLocus sZ) :
    ∃ F : MMP.Mori.PrimeDivisor P, RationalMap.IsExceptional g.toRationalMap F := by
  have hP : IsNormalVariety k (g ≫ sZ) := (hg.toIsSmoothResolution.isNormalVariety hZ).1
  have : IsIntegral P := hP.1.toIsIntegral
  have : IsNormal P := hP.2
  have : LocallyOfFiniteType (g ≫ sZ) := hP.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sZ)
  have : QuasiCompact (g ≫ sZ) := hP.1.toQuasiCompact
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (g ≫ sZ)
  have : IsNoetherian P := {}
  have := hg.isProper
  have hbir := hg.isBirationalMorphism
  -- `z` is not in the biregular locus, so the fibre over it lies in the exceptional set
  have hzb : z ∉ biregularLocus g := fun h =>
    hz (biregularLocus_le_smoothLocus sZ g hg.isSmoothScheme h)
  obtain ⟨p, rfl⟩ := surjective_of_isBirationalMorphism g hbir z
  have hpE : p ∈ (exceptionalSet g : Set P) := hzb
  obtain ⟨C, hCirr, hpC, hCS, hCmax⟩ :=
    exists_maximal_isIrreducible_subset (exceptionalSet g).isClosed hpE
  let W : IrreducibleCloseds P := ⟨C, hCirr, C.isClosed⟩
  have hW : codimension W = 1 := by
    refine hg.isPureCodimOne_exceptionalSet W ⟨hCS, fun W' hW' hle => ?_⟩
    exact hCmax W' W'.isIrreducible hW' hle
  -- the generic point of `W`
  set ξ := hCirr.genericPoint
  have hξ : closure ({ξ} : Set P) = C := by
    have := hCirr.isGenericPoint_genericPoint_closure
    rwa [C.isClosed.closure_eq] at this
  have hWξ : W = IrreducibleCloseds.closureSingleton ξ := by
    ext y
    change y ∈ (C : Set P) ↔ y ∈ closure {ξ}
    rw [hξ]
  have hξ1 : Order.coheight ξ = 1 := by
    rw [← MMP.Flips.codimension_closureSingleton, ← hWξ, hW]
  let F : MMP.Mori.PrimeDivisor P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξ1
  have hFξ : F.genericPoint = ξ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hξS : ξ ∈ (exceptionalSet g : Set P) := hCS (hξ ▸ subset_closure rfl)
  refine ⟨F, ?_⟩
  let DF : DivisorOver k sZ := ⟨P, g, hP, hbir, F⟩
  have : DF.IsExceptional := by
    rw [isExceptional_iff_two_le_coheight hZ]
    change 2 ≤ Order.coheight (g F.genericPoint)
    rw [hFξ]
    by_contra hlt
    push Not at hlt
    have hle : ringKrullDim (Z.presheaf.stalk (g ξ)) ≤ 1 := by
      rw [ringKrullDim_stalk_eq_coheight]
      exact_mod_cast Order.le_of_lt_add_one hlt
    exact hξS (MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hZ g hP.1 hbir hle)
  exact this

end ExceptionalOverSingular

/-! ### Restricting the zero divisor -/

/-- The restriction by components of the zero divisor is zero. -/
private theorem restrictComponents_zero {R : Type*} [AddCommMonoid R] {X S : Scheme.{u}}
    (f : S ⟶ X) : (0 : DivisorWithCoeffs R X).restrictComponents f = 0 := by
  classical
  unfold DivisorWithCoeffs.restrictComponents
  split_ifs with h
  · ext C
    change DivisorWithCoeffs.restrictComponentsCoeff f 0 C = 0
    simp [DivisorWithCoeffs.restrictComponentsCoeff]
  · rfl

/-! ### Cutting by a general hyperplane -/

section Hyperplane

variable {k : Type u} [Field k]

/-- With no boundary, the boundary subscheme `⋂ f⁻¹_* Δ` of a log resolution is empty, hence
smooth. -/
private theorem isSmoothScheme_inverseTransformDivisor_zero {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (f : Y ⟶ X) : IsSmoothScheme
      ((⨅ F ∈ (inverseTransformDivisor f (0 : QDivisor X)).support, F.idealSheaf).subschemeι ≫
        f ≫ sX) := by
  have h0 : (inverseTransformDivisor f (0 : QDivisor X)).support = ∅ := by
    rw [map_zero]; rfl
  have hempty : IsEmpty
      (⨅ F ∈ (inverseTransformDivisor f (0 : QDivisor X)).support, F.idealSheaf).subscheme := by
    rw [h0]
    simp only [Finset.notMem_empty, iInf_of_empty, iInf_top]
    refine ⟨fun y => ?_⟩
    have : (⊤ : Y.IdealSheafData).subschemeι y ∈ Set.range (⊤ : Y.IdealSheafData).subschemeι :=
      ⟨y, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_top] at this
    exact this
  exact top_le_iff.mp fun y _ => (hempty.false y).elim

/-- If the local ring of `z` is `𝒪_{X,x}/(g)` for a nonzerodivisor `g ∈ 𝔪_x`, then `z` has
codimension one less than `x`. -/
private theorem coheight_add_one_eq_of_ringEquiv {Z X : Scheme.{u}} [IsLocallyNoetherian X]
    {z : Z} {x : X} {g : X.presheaf.stalk x} (hg : g ∈ nonZeroDivisors _)
    (hgm : g ∈ IsLocalRing.maximalIdeal _)
    (e : Z.presheaf.stalk z ≃+* X.presheaf.stalk x ⧸ Ideal.span {g}) :
    Order.coheight z + 1 = Order.coheight x := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    hg hgm
  rw [← ringKrullDim_eq_of_ringEquiv e, ringKrullDim_stalk_eq_coheight,
    ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- **The hyperplane step.** On an affine terminal variety of dimension `n + 1 ≥ 3`, a singular
point of codimension at most two gives a terminal variety of dimension `n` with a singular point
of codimension at most two: a connected component of a general hyperplane section through it. -/
private theorem exists_isTerminalPair_singular_of_isAffine [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsAffine X] {n : ℕ} {K : Divisor X} (h : IsTerminalPair sX (n + 1) K 0) (hn : 2 ≤ n)
    {x : X} (hx : x ∈ singularLocus sX) (hcx : Order.coheight x ≤ 2) :
    ∃ (Z : Scheme.{u}) (sZ : Z ⟶ Spec (.of k)) (_ : IsIntegral Z) (_ : IsLocallyNoetherian Z)
      (_ : IsNormal Z) (K' : Divisor Z), IsTerminalPair sZ n K' 0 ∧
        ∃ z ∈ singularLocus sZ, Order.coheight z ≤ 2 := by
  classical
  have : PerfectField k := PerfectField.ofCharZero
  have hX : IsNormalVariety k sX := h.1.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hdimX : topologicalKrullDim X = ((n + 1 : ℕ) : WithBot ℕ∞) := h.1.2.1.1
  have hdim2 : 2 ≤ topologicalKrullDim X := by
    rw [hdimX]; exact_mod_cast (by omega : 2 ≤ n + 1)
  -- `x` is not a closed point
  have hxnc : ¬ IsClosed ({x} : Set X) := by
    intro hcl
    have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
    rw [hcl.closure_eq, hdimX] at h1
    obtain ⟨d, e, hd, he, hde⟩ := exists_nat_of_add_eq h1
    have h0 : topologicalKrullDim ({x} : Set X) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [hd] at h0
    have hd0 : d = 0 := by exact_mod_cast le_antisymm h0 (by positivity)
    rw [he] at hcx
    have : e ≤ 2 := by exact_mod_cast hcx
    omega
  -- a regular function with two different values on `closure {x}`
  obtain ⟨a, w₁, w₂, t₁, t₂, h₁, h₂, -, -, hv₁, hv₂, ht⟩ :=
    exists_closedPoints_values_ne (sX := sX) hxnc
  have hT := infinite_setOf_values h₁ h₂ hv₁ hv₂ ht
  -- the pencil spanned by `1` and `a`
  let sec : Γ(X, ⊤) → (0 : Divisor X).divisorialSubmodule ⊤ := fun b =>
    ⟨algebraMap Γ(X, ⊤) _ b, Divisor.isDivisorialSection_algebraMap le_rfl b⟩
  have hsec_ne : ∀ b : Γ(X, ⊤), b ≠ 0 → sec b ≠ 0 := by
    intro b hb h0
    apply hb
    let Z₀ : irreducibleComponents X := pointComponent x
    have h1 := congrArg (fun φ : (0 : Divisor X).divisorialSubmodule ⊤ => φ.1 ⟨Z₀, trivial⟩) h0
    have h2 : (X.presheaf.germ ⊤ (componentGenericPoint X Z₀) trivial).hom b =
        (X.presheaf.germ ⊤ (componentGenericPoint X Z₀) trivial).hom 0 := by
      rwa [map_zero]
    exact germ_injective_of_isIntegral X (U := ⊤) _ (Opens.mem_top _) h2
  let s : Fin 2 → (0 : Divisor X).divisorialSubmodule ⊤ := ![sec 1, sec a]
  have hs : ∀ y : X, ∃ (i : Fin 2) (hi : s i ≠ 0),
      y ∉ ((0 : Divisor X).zeroDivisor (s i) hi).supp := by
    intro y
    refine ⟨0, hsec_ne 1 one_ne_zero, ?_⟩
    refine (mem_supp_zeroDivisor_algebraMap_iff (1 : Γ(X, ⊤)) (hsec_ne 1 one_ne_zero) y).not.mpr ?_
    rw [not_not, Scheme.basicOpen_one]
    trivial
  -- a log resolution of `X`
  obtain ⟨Y, f, hf⟩ := exists_isLogResolution sX hX (QDivisor.toRDivisor (0 : QDivisor X))
  have hYv : IsNormalVariety k (f ≫ sX) := (hf.toIsSmoothResolution.isNormalVariety hX).1
  have : IsNormal Y := hYv.2
  have : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  obtain ⟨Ex, hEx⟩ := exists_finset_isExceptional hf
  have hsm := isSmoothScheme_inverseTransformDivisor_zero (sX := sX) f
  -- the general member
  obtain ⟨Q₁, hQ₁, h₁c⟩ :=
    IsPair.exists_polynomial_discrep_le_discrep_restrict_connectedComponent hdim2 h.1.isPair s hs
  obtain ⟨Q₂, hQ₂, h₂c⟩ :=
    IsLogResolution.exists_polynomial_isLogResolution_restrict_connectedComponent hdim2
      h.1.isPair hf Ex hEx hsm s hs
  obtain ⟨hY, Q₃, hQ₃, h₃c⟩ :=
    IsLogResolution.exists_polynomial_isDiscrepancy_restrict_connectedComponent_iff hdim2
      h.1.isPair hf Ex hEx hsm s hs
  obtain ⟨Q₄, hQ₄, h₄c⟩ := exists_polynomial_isNormal_zeroScheme hdim2 hX s hs
  have hQ : Q₁ * Q₂ * Q₃ * Q₄ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hQ₁ hQ₂) hQ₃) hQ₄
  obtain ⟨μ, hμ, t, ⟨w, hxw, -, hwt⟩, hQc⟩ := exists_eval_ne_zero_of_infinite hQ hT
  set c : Fin 2 → k := ![-(μ * t), μ] with hc_def
  simp only [map_mul] at hQc
  have hc₄ := right_ne_zero_of_mul hQc
  have hc₃ := right_ne_zero_of_mul (left_ne_zero_of_mul hQc)
  have hc₂ := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hQc))
  have hc₁ := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hQc))
  -- the section `σ = μ (a - t)`
  set r : Γ(X, ⊤) := scalarsToGlobalSections k sX μ * (a - scalarsToGlobalSections k sX t)
    with hr_def
  have hσr : (∑ i, scalarsToGlobalSections k sX (c i) • s i) = sec r := by
    apply Subtype.ext
    funext Z
    simp only [Fin.sum_univ_two, s, sec, c, Matrix.cons_val_zero, Matrix.cons_val_one,
      Submodule.coe_add, Submodule.coe_smul]
    rw [Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul, ← map_add]
    have : scalarsToGlobalSections k sX (-(μ * t)) * 1 +
        scalarsToGlobalSections k sX μ * a = r := by
      rw [hr_def, map_neg, map_mul]; ring
    rw [this]
  have hsuppr : ∀ (hσ : (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0) (y : X),
      y ∈ ((0 : Divisor X).zeroDivisor _ hσ).supp ↔ y ∉ X.basicOpen r := by
    intro hσ y
    have hr' : sec r ≠ 0 := hσr ▸ hσ
    have key : ∀ (σ₁ σ₂ : (0 : Divisor X).divisorialSubmodule ⊤) (_ : σ₁ = σ₂) (h₁ : σ₁ ≠ 0)
        (h₂ : σ₂ ≠ 0), (0 : Divisor X).zeroDivisor σ₁ h₁ = (0 : Divisor X).zeroDivisor σ₂ h₂ := by
      rintro _ _ rfl _ _; rfl
    rw [key _ _ hσr hσ hr']
    exact mem_supp_zeroDivisor_algebraMap_iff r hr' y
  -- `σ` vanishes at `w` but not at `x`
  have hμu : X.basicOpen (scalarsToGlobalSections k sX μ) = ⊤ :=
    Scheme.basicOpen_of_isUnit _ ((Ne.isUnit hμ).map _)
  have hwr : w ∉ X.basicOpen r := by
    rw [hr_def, Scheme.basicOpen_mul, hμu, top_inf_eq]
    exact hwt
  have hxr : x ∈ X.basicOpen r := by
    obtain ⟨w', hxw', hw'⟩ : ∃ w', x ⤳ w' ∧
        w' ∈ X.basicOpen (a - scalarsToGlobalSections k sX t) := by
      by_cases ht₁ : t₁ = t
      · exact ⟨w₂, h₂, mem_basicOpen_sub_of_ne hv₂ (fun h => ht (ht₁.trans h.symm))⟩
      · exact ⟨w₁, h₁, mem_basicOpen_sub_of_ne hv₁ ht₁⟩
    have : w' ∈ X.basicOpen r := by
      rwa [hr_def, Scheme.basicOpen_mul, hμu, top_inf_eq]
    exact hxw'.mem_open (X.basicOpen r).isOpen this
  -- a point `x'` of `closure {x} ∩ V(σ)` of codimension at most `3`
  obtain ⟨x', hxx', hx'r, hcx'⟩ :=
    exists_specializes_notMem_basicOpen_coheight_le (sX := sX) hdimX hxw hxr hwr
  have hx'sing : x' ∈ singularLocus sX := hxx'.mem_closed (singularLocus sX).isClosed hx
  -- the connected component `Z` of `V(σ)` through `x'`
  obtain ⟨hσ, h₁Z⟩ := h₁c c hc₁
  have hx'supp : x' ∈ ((0 : Divisor X).zeroDivisor _ hσ).supp := (hsuppr hσ x').mpr hx'r
  have hZc : IsClosed (connectedComponentIn
      (((0 : Divisor X).zeroDivisor _ hσ).supp : Set X) x') := by
    rw [connectedComponentIn_eq_image hx'supp]
    exact ((((0 : Divisor X).zeroDivisor _ hσ).supp.isClosed).isClosedEmbedding_subtypeVal
      ).isClosedMap _ isClosed_connectedComponent
  let Z : Closeds X := ⟨_, hZc⟩
  obtain ⟨hH, hdisc⟩ := h₁Z Z x' hx'supp rfl
  obtain ⟨hσ₂, h₂Z⟩ := h₂c c hc₂
  obtain ⟨hlog, hexc, -, -⟩ := h₂Z Z x' hx'supp rfl
  obtain ⟨hσ₃, h₃Z⟩ := h₃c c hc₃
  obtain ⟨hH₃, hY', hbir, hiff⟩ := h₃Z Z x' hx'supp rfl
  have hnorm := h₄c c hc₄ hσ
  -- the component `Z` as a normal variety
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := hH.1.toIsIntegral
  have : IsNormal (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := hH.2
  have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) :=
    hH.1.toLocallyOfFiniteType
  have : QuasiCompact ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) :=
    hH.1.toQuasiCompact
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
  have : CompactSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace
      ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
  have hrangeZ : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hx'Z : x' ∈ (Z : Set X) := mem_connectedComponentIn hx'supp
  obtain ⟨z, hz⟩ : x' ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
    hrangeZ ▸ hx'Z
  -- the local ring of `Z` at `z` is `𝒪_{X,x'}/(g)`
  have hHc := isCartier_of_forall_exists_notMem_supp s hs
  have := hHc.isInvertibleModule_divisorialSheaf
  obtain ⟨g, hg0, hgm, ⟨e⟩⟩ :=
    exists_ringEquiv_stalk_quotient (0 : Divisor X) hHc _ hσ hnorm Z x' rfl z
  have hgreg : g ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero hg0
  -- `z` is a singular point of `Z`
  have hzsing : z ∈ singularLocus ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) := by
    intro hzsm
    have hreg := (mem_smoothLocus_iff_isRegularLocalRing _ z).mp hzsm
    have hreg' := IsRegularLocalRing.of_ringEquiv e
    have hregX := isRegularLocalRing_of_isRegularLocalRing_quotient hgreg hgm hreg'
    have hsm := (mem_smoothLocus_iff_isRegularLocalRing sX _).mpr hregX
    rw [hz] at hsm
    exact hx'sing hsm
  -- `z` has codimension at most two in `Z`
  have hcz : Order.coheight z ≤ 2 := by
    have h4 : Order.coheight z + 1 ≤ 2 + 1 := by
      rw [coheight_add_one_eq_of_ringEquiv hgreg hgm e, hz]
      exact hcx'.trans (add_le_add_left hcx 1)
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h4
  -- `Z` has dimension `n`, by Krull's principal ideal theorem
  have hrne : r ≠ 0 := fun h0 => by
    rwa [h0, Scheme.basicOpen_zero] at hxr
  let : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sX)
  have hdimZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = n := by
    have hirr : IsIrreducible (Z : Set X) := by
      have := isIrreducible_support_of_isIntegral (Scheme.IdealSheafData.vanishingIdeal Z)
      rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    have hmaxZ : Maximal (fun T : Set X => IsIrreducible T ∧
        T ⊆ X.zeroLocus {r} ∩ ↑(⊤ : X.Opens)) (Z : Set X) := by
      refine ⟨⟨hirr, fun y hy => ⟨?_, trivial⟩⟩, fun T hT hZT => ?_⟩
      · rw [Scheme.zeroLocus_singleton]
        exact (hsuppr hσ y).mp (connectedComponentIn_subset _ _ hy)
      · have hTs : T ⊆ ((0 : Divisor X).zeroDivisor _ hσ).supp := fun y hy =>
          (hsuppr hσ y).mpr (by
            have := (hT.2 hy).1
            rwa [Scheme.zeroLocus_singleton] at this)
        exact (IsIrreducible.isConnected hT.1).isPreconnected.subset_connectedComponentIn
          (hZT hx'Z) hTs
    have hX' : MMP.Intersection.HasDim X ((n + 1 : ℕ) : ℤ) := ⟨n + 1, rfl, hdimX⟩
    obtain ⟨m, hm, hmZ⟩ := MMP.hasDim_of_maximal_isIrreducible_zeroLocus k hX'
      (isAffineOpen_top X) hrne hmaxZ
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    obtain rfl : m = n := by omega
    exact hmZ
  -- a canonical divisor of `Z`
  obtain ⟨K', hK'⟩ := exists_isCanonicalDivisor
    ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) hH hdimZ
  have hres0 : (0 : QDivisor X).restrictComponents
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = 0 := restrictComponents_zero _
  -- `K_Z` is `ℚ`-Cartier: an exceptional divisor of the base change of `f` over the singular
  -- point `z` has a discrepancy over `Z`
  obtain ⟨F, hFexc⟩ := exists_isExceptional_of_notMem_smoothLocus hH hlog hzsing
  obtain ⟨E, hE, hEF⟩ := (hexc F).mp hFexc
  obtain ⟨a₀, ha₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1
    (⟨Y, f, hY, hf.toIsSmoothResolution.isBirationalMorphism, E⟩ : DivisorOver k sX)
  obtain ⟨-, -, m, hm, hmC, -⟩ := (hiff E hE F hEF (n + 1) n K K' h.1.2.1 hK' a₀).mp ha₀
  rw [hres0] at hmC
  have hQC : (Divisor.toQDivisor K' + 0).IsQCartier := ⟨m, by exact_mod_cast hm.ne', hmC⟩
  -- `(Z, 0)` is terminal
  refine ⟨_, (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX, inferInstance,
    inferInstance, inferInstance, K', ⟨⟨hH, hK', hQC⟩, ?_⟩, z, hzsing, hcz⟩
  have hd := hdisc (n + 1) n K K' h.1.2.1
  rw [hres0] at hd
  exact lt_of_lt_of_le h.2 hd

end Hyperplane

/-! ### The main induction -/

/-- The inductive statement: a terminal normal variety of dimension `n` has no singular point of
codimension at most two. -/
private theorem not_exists_singular_coheight_le_two (n : ℕ) :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
      {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
      {K : Divisor X}, IsTerminalPair sX n K 0 → ∀ x ∈ singularLocus sX,
        Order.coheight x ≤ 2 → False := by
  induction n with
  | zero =>
    intro k _ _ _ X sX _ _ _ K h x hx _
    have : PerfectField k := PerfectField.ofCharZero
    have hc := coheight_le_of_topologicalKrullDim_eq h.1.2.1.1 x
    exact hx (mem_smoothLocus_of_coheight_le_one h.1.1 (hc.trans (by norm_num)))
  | succ n ih =>
    intro k _ _ _ X sX _ _ _ K h x hx hcx
    have : PerfectField k := PerfectField.ofCharZero
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · have hc := coheight_le_of_topologicalKrullDim_eq h.1.2.1.1 x
        exact hx (mem_smoothLocus_of_coheight_le_one h.1.1 (by exact_mod_cast hc))
      · exact notMem_singularLocus_of_isTerminalPair_two h x hx
    · -- pass to an affine open neighbourhood of `x`
      obtain ⟨_, ⟨U₀, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      let U : X.Opens := U₀
      have : Nonempty U := ⟨⟨x, hxU⟩⟩
      have : IsAffine U.toScheme := hU
      have hUt := isTerminalPair_restrictOpen h U
      have hX : IsNormalVariety k sX := h.1.1
      have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
      set x' : U.toScheme := ⟨x, hxU⟩
      have hx' : x' ∈ singularLocus (U.ι ≫ sX) := by
        change x' ∉ smoothLocus (U.ι ≫ sX)
        rw [mem_smoothLocus_ι_iff]
        exact hx
      have hcx' : Order.coheight x' ≤ 2 := by
        rwa [← coheight_ι]
      obtain ⟨Z, sZ, _, _, _, K', hZ, z, hz, hcz⟩ :=
        exists_isTerminalPair_singular_of_isAffine hUt hn hx' hcx'
      exact ih hZ z hz hcz

section TerminalCodimTwo

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **Terminal varieties are smooth in codimension two** (Kollár–Mori 5.18). Let `X` be a normal
variety over an algebraically closed field `k` of characteristic zero, `K` a canonical divisor of
`X` of dimension `n`, and suppose `(X, 0)` is terminal. Then every point of the singular locus of
`X` has codimension at least `3`. -/
@[mmp "lem_km5d_terminal_smooth_codim_two"]
public theorem IsTerminalPair.three_le_coheight_of_mem_singularLocus [IsAlgClosed k] [CharZero k]
    {n : ℕ} {K : Divisor X} (h : IsTerminalPair sX n K 0) {x : X}
    (hx : x ∈ singularLocus sX) : 3 ≤ Order.coheight x :=
  not_lt.mp fun hlt => not_exists_singular_coheight_le_two n h x hx (Order.le_of_lt_add_one hlt)

end TerminalCodimTwo

end MMP.Mori

end
