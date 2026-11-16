module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.Cycles
import MMP.AlgebraicGeometry.ProjectiveSpace.Hyperplane
import MMP.AlgebraicGeometry.Dimension.EffectiveCartierPureDimension
import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
import MMP.AlgebraicGeometry.ProjectiveSpace.HyperplaneEffectiveCartier
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingIdeal
import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.RingTheory.GradedAlgebra.KrullDimension
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SplitQuotientComplementAffineSpace
import StacksFrontier.AlgebraicGeometry.HigherDirectImageBaseChange.Basic
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import MMP.AlgebraicGeometry.Singularities.Semismooth.SingularLocus
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.RingTheory.Serre.FinitePointsDepthDimension
import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedConeDepthDimension
import MMP.AlgebraicGeometry.SpreadingOut.GenericFibreDimension
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.Topology.KrullDimensionProperClosed
public import MMP.AlgebraicGeometry.IdealSheafComap
public import MMP.AlgebraicGeometry.Dimension.PureDimensional
import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsRestrict
import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion
import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion

/-!
# Bertini theorems and generic fibres in characteristic zero

This file collects the generic-member and generic-fibre statements used throughout Mori's
program over a field of characteristic zero.

Let `k` be algebraically closed of characteristic zero. If `X` is a normal variety over `k` and
`s₀, …, s_N` are global sections generating an invertible sheaf `L`, then the zero scheme of
`∑ᵢ cᵢ sᵢ` is normal for a general coefficient vector `c`. The proof checks Serre's criterion
`(R₁) + (S₂)` on the zero scheme: for general `c` the section avoids a finite set of points of
`X` (the generic point, the generic points of the singular locus in codimension two, and the
finitely many points of depth two and dimension greater than two), and its trace on the smooth
locus is smooth by Bertini's theorem for smoothness.

Applied to the pulled-back coordinates of a `k`-morphism `φ : Z ⟶ ℙᴺ_k` from a normal variety,
this gives Bertini for general hyperplane pullbacks `Z_H = φ⁻¹(H)`: `Z_H` is a normal variety of
dimension `dim Z - 1` when `dim φ(Z) ≥ 2`; for closed subvarieties `F_j ⊆ Z`, the cut
`F_j ∩ Z_H` is empty when `φ(F_j)` is a point, and otherwise non-empty, reduced, of pure
dimension `dim F_j - 1`, and irreducible when `dim φ(F_j) ≥ 2`; and a `ℚ`-Cartier divisor
`B = ∑ bᵢ Bᵢ` with components among the `F_j` restricts to `∑ bᵢ [Bᵢ ∩ Z_H]`.

Over a base, let `k₀` be a field of characteristic zero, `R` a domain of finite type over `k₀`
and `f : Y ⟶ Spec R` a morphism of finite type. If `Y` is reduced, the fibres of `f` over a
dense principal open `D(r)` are geometrically reduced; if the generic fibre of `f` is normal,
the fibres over some `D(r)` are geometrically normal, and pure of dimension `d` whenever the
generic fibre is.

## Main results

* `MMP.Threefold.Bridges.exists_dense_open_isNormal_zeroScheme`: general members of a free
  linear system on a normal variety are normal.
* `MMP.Threefold.Bridges.exists_dense_open_hyperplaneSection_restrictComponents`: Bertini for
  general hyperplane pullbacks, with reduced cuts and restriction of divisors.
* `MMP.exists_ne_zero_forall_geometricallyReduced_fiberToSpecResidueField`: reduced schemes have
  geometrically reduced fibres over a dense open.
* `MMP.exists_ne_zero_forall_geometrically_isNormal_fiber`: normal generic fibres spread out.

## Implementation notes

A linear system `V` is presented by sections `s₀, …, s_N` spanning it, a member by its coefficient
vector `c` (`MMP.Threefold.Bridges.systemSection s c = ∑ᵢ cᵢ sᵢ`), a dense open of `V` by one of
`MMP.Threefold.Bridges.coefficientSpace k N` and a dense open of `ℙ(V)` by one of
`AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)`, the nonzero `c`
giving the point `MMP.Threefold.Bridges.dualPoint c`. A hyperplane is `V(∑ᵢ cᵢ Tᵢ)`, and `Z_H` is
the subscheme of `MMP.Threefold.Bridges.hyperplaneSection φ c`; the pull-back of `ℚ`-divisors is
only defined between normal schemes, so the restriction formula is stated whenever `Z_H` is normal.

The spreading-out results are proved on affine charts `Spec A → Spec R`. Instead of passing
through the normalization and the `Ext`-supports of a presentation, they use the ideal `J` of the
non-smooth locus of `R → A`: one nonzerodivisor in `J` (for reducedness), or one regular sequence
of length two in `J` (for normality, by Serre's criterion), is chosen on the generic fibre and
spread to all fibres over `D(r)` by generic flatness of `A` and its quotients. A fibre is
geometrically reduced or normal when every base change of it to a field is.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 3.39
* [Stacks Project, Tag 0ECN](https://stacks.math.columbia.edu/tag/0ECN)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S) (Serre's criterion)
* [Stacks Project, Tag 051Z](https://stacks.math.columbia.edu/tag/051Z) (generic flatness)
* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV) (smoothness and
  regularity over a field)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule baseRingHom)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u w

namespace MMP.Threefold.Bridges

/-- `ℙᴺ_k = Proj k[T₀, …, T_N]` over `Spec k` through Stacks' structure morphism
`projToSpecCoeff k N`. -/
@[reducible] private noncomputable def projectiveSpaceOver (k : Type u) [Field k] (N : ℕ) :
    (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Over
      (Spec (.of k)) :=
  ⟨Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k N⟩

attribute [local instance high] projectiveSpaceOver

/-- `ℙᴺ_k` is proper over `k`. -/
private local instance isProper_projectiveSpaceOver (k : Type u) [Field k] (N : ℕ) :
    IsProper (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) ↘
      Spec (.of k)) :=
  Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k N

/-! ### Dividing a local ring by a nonzerodivisor -/

section LocalAlgebra

open scoped Pointwise

/-- Dividing a Noetherian local ring by a nonzerodivisor of its maximal ideal lowers its depth
and its Krull dimension by exactly one. -/
private theorem depth_and_ringKrullDim_quotient_add_one {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {f : R} (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hfreg : f ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {f})] :
    Module.depth (R ⧸ Ideal.span {f}) (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {f}))
        (R ⧸ Ideal.span {f}) + 1 =
      Module.depth R (IsLocalRing.maximalIdeal R) R ∧
    ringKrullDim (R ⧸ Ideal.span {f}) + 1 = ringKrullDim R := by
  set Q := R ⧸ Ideal.span {f}
  have hspan : (f • (⊤ : Submodule R R) : Submodule R R) = Ideal.span {f} := by
    rw [← Submodule.ideal_span_singleton_smul]
    simp
  let e : QuotSMulTop f R ≃ₗ[R] Q := Submodule.quotEquivOfEq _ _ hspan
  have hdrop := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (IsLocalRing.maximalIdeal R) R).1 f hf
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hfreg)
  rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal R) e] at hdrop
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R Q) = IsLocalRing.maximalIdeal Q := by
    simpa only [Q, Ideal.Quotient.algebraMap_eq] using
      (IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective)
  refine ⟨?_, ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    hfreg hf⟩
  rw [← hdrop, Module.depth_eq_depth_map_algebraMap (A := R) (B := Q) Ideal.Quotient.mk_surjective
    _ Q, hmax]

/-- The depth and the Krull dimension of a local ring only depend on it up to isomorphism. -/
private theorem depth_and_ringKrullDim_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Module.depth A (IsLocalRing.maximalIdeal A) A = Module.depth B (IsLocalRing.maximalIdeal B) B ∧
      ringKrullDim A = ringKrullDim B :=
  ⟨Module.depth_self_eq_of_ringEquiv e, ringKrullDim_eq_of_ringEquiv e⟩

end LocalAlgebra

/-! ### Local rings of an effective Cartier divisor -/

section CartierStalk

/-- The localization at a prime `q` of `A ⧸ J` is the quotient of the localization of `A` at the
preimage of `q` by the image of `J`. -/
private noncomputable def localizationAtPrimeQuotientEquiv {A : Type*} [CommRing A]
    (J : Ideal A) (q : Ideal (A ⧸ J)) [q.IsPrime] :
    (Localization.AtPrime (q.comap (Ideal.Quotient.mk J))) ⧸
        J.map (algebraMap A (Localization.AtPrime (q.comap (Ideal.Quotient.mk J)))) ≃+*
      Localization.AtPrime q := by
  let p := q.comap (Ideal.Quotient.mk J)
  have hsub : Submonoid.map (Ideal.Quotient.mk J) p.primeCompl = q.primeCompl := by
    change Submonoid.map (Ideal.Quotient.mk J)
      (Submonoid.comap (Ideal.Quotient.mk J) q.primeCompl) = q.primeCompl
    exact Submonoid.map_comap_eq_of_surjective Ideal.Quotient.mk_surjective q.primeCompl
  let _ : IsLocalization (Submonoid.map (Ideal.Quotient.mk J) p.primeCompl)
      (Localization.AtPrime q) := by
    rw [hsub]
    infer_instance
  let ψ : Localization.AtPrime p →+* Localization.AtPrime q :=
    IsLocalization.map (M := p.primeCompl) (Localization.AtPrime q)
      (Ideal.Quotient.mk J) (Submonoid.le_comap_map _)
  have hsurj : Function.Surjective ψ :=
    IsLocalization.map_surjective_of_surjective p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q) (g := Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hker : RingHom.ker ψ = J.map (algebraMap A (Localization.AtPrime p)) := by
    change RingHom.ker (IsLocalization.map (Localization.AtPrime q)
      (Ideal.Quotient.mk J) (Submonoid.le_comap_map _)) = _
    rw [IsLocalization.ker_map (Localization.AtPrime q) (Ideal.Quotient.mk J) rfl]
    simp [Ideal.mk_ker]
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

/-- **The local rings of an effective Cartier divisor.** At a point `y` of an effective Cartier
divisor `D` of a locally Noetherian scheme `X`, the depth and the dimension of `𝒪_{D,y}` are those
of `𝒪_{X,y}` minus one: `𝒪_{D,y}` is the quotient of `𝒪_{X,y}` by a nonzerodivisor of its
maximal ideal. -/
private theorem depth_and_ringKrullDim_stalk_subscheme_add_one {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (y : I.subscheme) :
    Module.depth (I.subscheme.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (I.subscheme.presheaf.stalk y))
        (I.subscheme.presheaf.stalk y) + 1 =
      Module.depth (X.presheaf.stalk (I.subschemeι y))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι y)))
        (X.presheaf.stalk (I.subschemeι y)) ∧
    ringKrullDim (I.subscheme.presheaf.stalk y) + 1 =
      ringKrullDim (X.presheaf.stalk (I.subschemeι y)) := by
  have hxSupport : I.subschemeι y ∈ I.supportSet := by
    rw [I.mem_supportSet_iff_mem_support]
    change I.subschemeι y ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact ⟨y, rfl⟩
  obtain ⟨U, hU, hxU, f, hf, e, he⟩ :=
    (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal I).mp hI _ hxSupport
  let A := Γ(X, U)
  let mk : A →+* A ⧸ Ideal.span {f} := Ideal.Quotient.mk _
  let P := pullback I.subschemeι U.ι
  have hyRange : y ∈ Set.range (pullback.fst I.subschemeι U.ι).base := by
    rw [IsOpenImmersion.range_pullbackFst]
    show I.subschemeι y ∈ U.ι.opensRange
    rwa [Scheme.Opens.opensRange_ι]
  obtain ⟨z, hz⟩ := Set.mem_range.mp hyRange
  subst hz
  let u : U := (pullback.snd I.subschemeι U.ι).base z
  have hu : (u : X) = I.subschemeι ((pullback.fst I.subschemeι U.ι).base z) := by
    have hh : (pullback.fst I.subschemeι U.ι ≫ I.subschemeι) z =
        (pullback.snd I.subschemeι U.ι ≫ U.ι) z := by rw [pullback.condition]
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hh
    exact hh.symm
  let qpt : PrimeSpectrum (A ⧸ Ideal.span {f}) := e.hom z
  have hspec : hU.primeIdealOf u = qpt.comap mk := by
    have hh : (pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom) z =
        (e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) z := by
      rw [he]
    simp only [Scheme.Hom.comp_apply] at hh
    exact hh
  let p : Ideal A := qpt.asIdeal.comap mk
  let _ : p.IsPrime := (qpt.comap mk).2
  let _ : IsNoetherianRing A :=
    (inferInstance : IsLocallyNoetherian X).component_noetherian ⟨U, hU⟩
  let _ : Algebra A (X.presheaf.stalk (u : X)) :=
    X.presheaf.algebra_section_stalk ⟨(u : X), u.2⟩
  let _ : IsLocalization.AtPrime (X.presheaf.stalk (u : X)) p := by
    change IsLocalization.AtPrime (X.presheaf.stalk (u : X)) (qpt.comap mk).asIdeal
    simpa only [← hspec] using hU.isLocalization_stalk u
  let R := Localization.AtPrime p
  let eX := IsLocalization.algEquiv p.primeCompl R (X.presheaf.stalk (u : X))
  let fR : R := algebraMap A R f
  have hfmax : fR ∈ IsLocalRing.maximalIdeal R := by
    have hfp : f ∈ p := by
      change mk f ∈ qpt.asIdeal
      simp [mk]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R p f).2 hfp
  have hfreg : fR ∈ nonZeroDivisors R :=
    IsLocalization.map_nonZeroDivisors_le p.primeCompl R
      (Submonoid.mem_map.mpr ⟨f, isRegular_iff_mem_nonZeroDivisors.mp hf, rfl⟩)
  let Q := R ⧸ Ideal.span {fR}
  let _ : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (ne_of_lt (lt_of_le_of_lt (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hfmax))
      (IsLocalRing.maximalIdeal.isMaximal R).lt_top))
  let _ : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {fR})) Ideal.Quotient.mk_surjective
  let eQ : Q ≃+* Localization.AtPrime qpt.asIdeal := by
    have hspan : (Ideal.span {f}).map (algebraMap A R) = Ideal.span {fR} := by
      simp [Ideal.map_span, fR]
    exact (Ideal.quotEquivOfEq hspan.symm).trans
      (localizationAtPrimeQuotientEquiv (Ideal.span {f}) qpt.asIdeal)
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap (pullback.fst I.subschemeι U.ι) z
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap e.hom z
  let eZ : I.subscheme.presheaf.stalk ((pullback.fst I.subschemeι U.ι).base z) ≃+* Q :=
    (asIso ((pullback.fst I.subschemeι U.ι).stalkMap z)).commRingCatIsoToRingEquiv.trans <|
      (asIso (e.hom.stalkMap z)).commRingCatIsoToRingEquiv.symm.trans <|
        (Spec.stalkIso (.of (A ⧸ Ideal.span {f})) qpt).commRingCatIsoToRingEquiv.trans eQ.symm
  obtain ⟨hd, hk⟩ := depth_and_ringKrullDim_quotient_add_one hfmax hfreg
  obtain ⟨hdZ, hkZ⟩ := depth_and_ringKrullDim_eq_of_ringEquiv eZ
  obtain ⟨hdX, hkX⟩ := depth_and_ringKrullDim_eq_of_ringEquiv eX.toRingEquiv
  rw [← hu, hdZ, hkZ, ← hdX, ← hkX]
  exact ⟨hd, hk⟩

end CartierStalk

/-! ### Points of exceptional depth -/

section DepthPoints

attribute [local instance] HasDerivedCategory.standard

/-- The localization of a ring at a prime, as a module over itself through `LocalizedModule`, has
the depth and the support dimension of the local ring. -/
private theorem depth_and_supportDim_localizedModule_self {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] :
    Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal _)
        (LocalizedModule.AtPrime p R) =
      Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal _)
        (Localization.AtPrime p) ∧
    Module.supportDim (Localization.AtPrime p) (LocalizedModule.AtPrime p R) =
      ringKrullDim (Localization.AtPrime p) := by
  let e := IsLocalizedModule.iso p.primeCompl (Algebra.linearMap R (Localization.AtPrime p))
  let e' := e.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
  refine ⟨Module.depth_eq_depth_of_linearEquiv _ e', ?_⟩
  haveI : Module.Finite (Localization.AtPrime p) (LocalizedModule.AtPrime p R) :=
    Module.Finite.equiv e'.symm
  have hann : Module.annihilator (Localization.AtPrime p) (LocalizedModule.AtPrime p R) = ⊥ := by
    rw [e'.annihilator_eq]
    exact Module.annihilator_eq_bot.mpr inferInstance
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, hann]
  exact ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)

/-- **Finiteness of the points of exceptional depth** ([Stacks, Tag 0ECN] for the structure
sheaf). Let `X` be a quasi-compact scheme locally of finite type over a field satisfying Serre's
condition `(Sₙ)`. Then there are only finitely many points `x ∈ X` at which `𝒪_{X,x}` has depth
`n` and dimension greater than `n`. -/
private theorem finite_setOf_depth_eq_and_lt_ringKrullDim {k : Type u} [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] [CompactSpace X]
    [IsLocallyNoetherian X] (n : ℕ) (hS : HasPropertySk X n) :
    {x : X | Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) = n ∧
          (n : WithBot ℕ∞) < ringKrullDim (X.presheaf.stalk x)}.Finite := by
  classical
  set E := {x : X | Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) = n ∧ (n : WithBot ℕ∞) < ringKrullDim (X.presheaf.stalk x)}
  have hloc : ∀ U : X.Opens, IsAffineOpen U → (E ∩ (U : Set X)).Finite := by
    intro U hU
    let R := Γ(X, U)
    let _ : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hft : (g.appLE ⊤ U (by simp)).hom.FiniteType :=
      g.finiteType_appLE (isAffineOpen_top _) hU (by simp)
    let _ : Algebra k R :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ U (by simp)).hom.toAlgebra
    have hftA : RingHom.FiniteType (algebraMap k R) := by
      change (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ U (by simp)).hom).FiniteType
      exact hft.comp (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
    let _ : Algebra.FiniteType k R := RingHom.finiteType_algebraMap.mp hftA
    obtain ⟨ω, hω⟩ := Stacks.Algebraization.exists_isDualizingComplex_of_finiteType_field k R
    let eq : ∀ q : Spec R,
        X.presheaf.stalk (hU.fromSpec q) ≃+* Localization.AtPrime q.asIdeal := fun q =>
      have := IsOpenImmersion.instIsIsoCommRingCatStalkMap hU.fromSpec q
      (asIso (hU.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv.trans
        (Spec.stalkIso R q).commRingCatIsoToRingEquiv
    have htr : ∀ q : Spec R,
        Module.depth (Localization.AtPrime q.asIdeal) (IsLocalRing.maximalIdeal _)
            (LocalizedModule.AtPrime q.asIdeal R) =
          Module.depth (X.presheaf.stalk (hU.fromSpec q))
            (IsLocalRing.maximalIdeal (X.presheaf.stalk (hU.fromSpec q)))
            (X.presheaf.stalk (hU.fromSpec q)) ∧
        Module.supportDim (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal R) =
          ringKrullDim (X.presheaf.stalk (hU.fromSpec q)) := by
      intro q
      obtain ⟨h1, h2⟩ := depth_and_supportDim_localizedModule_self q.asIdeal
      obtain ⟨h3, h4⟩ := depth_and_ringKrullDim_eq_of_ringEquiv (eq q)
      exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
    have hfin := Module.finite_setOf_depth_eq_and_lt_supportDim_localization ω hω n R
      (fun q => by rw [(htr q).1, (htr q).2]; exact hS (hU.fromSpec q))
    refine (hfin.image hU.fromSpec).subset ?_
    rintro x ⟨hxE, hxU⟩
    have hfx : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
    refine ⟨hU.primeIdealOf ⟨x, hxU⟩, ?_, hfx⟩
    obtain ⟨h1, h2⟩ := htr (hU.primeIdealOf ⟨x, hxU⟩)
    rw [hfx] at h1 h2
    exact ⟨h1.trans hxE.1, lt_of_lt_of_eq hxE.2 h2.symm⟩
  obtain ⟨Us, hUs, hUs_finite, hUs_sup⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := (⊤ : X.Opens))
      (by simpa using isCompact_univ (X := X))
  have : Fintype Us := hUs_finite.fintype
  refine (Set.finite_iUnion fun i : Us => hloc i.1 (hUs i.2)).subset fun x hx => ?_
  have hxtop : x ∈ ((⊤ : X.Opens) : Set X) := trivial
  rw [hUs_sup, sSup_eq_iSup] at hxtop
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxtop
  obtain ⟨hiUs, hxi⟩ := Opens.mem_iSup.mp hi
  exact Set.mem_iUnion.mpr ⟨⟨i, hiUs⟩, ⟨hx, hxi⟩⟩

end DepthPoints

/-! ### Points of small dimension on a closed subset -/

section SmallDimension

/-- The dimension of the local ring drops strictly at a proper generization. -/
private theorem ringKrullDim_stalk_lt_of_specializes {X : Scheme.{u}} [IsLocallyNoetherian X]
    {x x' : X} (h : x' ⤳ x) (hne : x' ≠ x) :
    ringKrullDim (X.presheaf.stalk x') < ringKrullDim (X.presheaf.stalk x) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  apply WithBot.coe_lt_coe.mpr
  apply Order.coheight_strictAnti
  · exact lt_of_le_not_ge (show x ≤ x' from h) (fun h' ↦ hne (h.antisymm h').eq)
  · apply WithBot.coe_lt_coe.mp
    simpa only [WithBot.coe_top, ← ringKrullDim_stalk_eq_coheight] using
      (ringKrullDim_lt_top (R := X.presheaf.stalk x'))

/-- If every point of a closed subset `T` of a Noetherian scheme has a local ring of dimension
at least `d`, only finitely many points of `T` have a local ring of dimension at most `d`: they are
generic points of irreducible components of `T`. -/
private theorem finite_setOf_mem_and_ringKrullDim_le {X : Scheme.{u}} [IsLocallyNoetherian X]
    [NoetherianSpace X] {T : Set X} (hT : IsClosed T) (d : WithBot ℕ∞)
    (hd : ∀ x ∈ T, d ≤ ringKrullDim (X.presheaf.stalk x)) :
    {x | x ∈ T ∧ ringKrullDim (X.presheaf.stalk x) ≤ d}.Finite := by
  classical
  obtain ⟨hfin, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hT
  have hgen : ∀ W : MMP.Resolution.componentsOf T, ∃ ξ : X, ξ ∈ T ∧ (W : Set X) = closure {ξ} :=
    fun W => MMP.Resolution.Aux.exists_eq_closure_of_mem_componentsOf hT W.2
  choose ξ hξT hξ using hgen
  have : Finite (MMP.Resolution.componentsOf T) := hfin.to_subtype
  refine (Set.finite_range ξ).subset fun x ⟨hxT, hxd⟩ => ?_
  obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp (hcov hxT)
  refine ⟨⟨W, hW⟩, ?_⟩
  have hspec : ξ ⟨W, hW⟩ ⤳ x := by
    rwa [specializes_iff_mem_closure, ← hξ ⟨W, hW⟩]
  by_contra hne
  exact not_le.mpr ((ringKrullDim_stalk_lt_of_specializes hspec hne).trans_le hxd)
    (hd _ (hξT ⟨W, hW⟩))

end SmallDimension

/-! ### Serre's criterion on an effective Cartier divisor -/

section SerreCriterion

/-- The arithmetic of `(S₂)` on a divisor: if `min(2, e + 1) ≤ d + 1` and not both `d + 1 = 2`
and `e + 1 > 2`, then `min(2, e) ≤ d`. Applied with `d`, `e` the depth and dimension of
`𝒪_{D,y}`, whose successors are those of `𝒪_{X,x}`. -/
private theorem min_two_le_of_add_one {d e : ℕ∞} (h2 : min 2 (e + 1) ≤ d + 1)
    (hne : ¬ (d + 1 = 2 ∧ 2 < e + 1)) : min 2 e ≤ d := by
  induction e using ENat.recTopCoe <;> induction d using ENat.recTopCoe <;>
    simp_all [min_le_iff] <;> norm_cast at * <;> omega

/-- `min (2, a) ≤ b` reads the same in `ℕ∞` and in `WithBot ℕ∞`. -/
private theorem min_two_coe_le_coe_iff (a b : ℕ∞) :
    min ((2 : ℕ) : WithBot ℕ∞) (a : WithBot ℕ∞) ≤ (b : WithBot ℕ∞) ↔ min 2 a ≤ b := by
  rw [show ((2 : ℕ) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) by norm_cast, ← WithBot.coe_min,
    WithBot.coe_le_coe]

/-- **Normality of an effective Cartier divisor of a normal scheme**, read off Serre's criterion.
Let `D` be an effective Cartier divisor of a locally Noetherian normal scheme `X`. Suppose that the
local ring of `D` is regular at every point at which the local ring of `X` has dimension at most
two, and that at no point of `D` does the local ring of `X` have depth two and dimension greater
than two. Then `D` is normal. -/
private theorem isNormal_subscheme_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hreg : ∀ y : I.subscheme, ringKrullDim (X.presheaf.stalk (I.subschemeι y)) ≤ 2 →
      IsRegularLocalRing (I.subscheme.presheaf.stalk y))
    (hdepth : ∀ y : I.subscheme,
      ¬ (Module.depth (X.presheaf.stalk (I.subschemeι y))
          (IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι y)))
          (X.presheaf.stalk (I.subschemeι y)) = 2 ∧
        (2 : WithBot ℕ∞) < ringKrullDim (X.presheaf.stalk (I.subschemeι y)))) :
    IsNormal I.subscheme := by
  haveI : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have hX := (isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one X).mp inferInstance
  refine (isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one _).mpr ⟨fun y => ?_,
    fun y hy => ?_⟩
  · obtain ⟨hd, hk⟩ := depth_and_ringKrullDim_stalk_subscheme_add_one I hI y
    have hS := hX.1 (I.subschemeι y)
    have hne := hdepth y
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at hk
    rw [ringKrullDim_stalk_eq_coheight] at hS hne ⊢
    rw [min_two_coe_le_coe_iff] at hS ⊢
    have hk' : Order.coheight y + 1 = Order.coheight (I.subschemeι y) := by exact_mod_cast hk
    rw [← hd, ← hk'] at hS hne
    exact min_two_le_of_add_one hS fun h => hne ⟨h.1, WithBot.coe_lt_coe.mpr h.2⟩
  · refine hreg y ?_
    obtain ⟨-, hk⟩ := depth_and_ringKrullDim_stalk_subscheme_add_one I hI y
    rw [← hk]
    calc ringKrullDim (I.subscheme.presheaf.stalk y) + 1 ≤ ((1 : ℕ) : WithBot ℕ∞) + 1 := by
          gcongr
      _ = 2 := by norm_num

end SerreCriterion

/-! ### Local rings of a trace on an open subscheme -/

section Trace

/-- **A smooth trace on an open subscheme has regular local rings.** Let `I` be an ideal sheaf on a
scheme `X` over a perfect field `k` and `S ⊆ X` an open subscheme such that `V(I) ∩ S` is smooth
over `k`. Then the local ring of `V(I)` at any point lying over `S` is regular: `V(I) ∩ S` is an
open subscheme of `V(I)`, with the same local rings. -/
private theorem isRegularLocalRing_stalk_of_smooth_comap {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (S : X.Opens)
    (hsm : Smooth ((I.comap S.ι).subschemeι ≫ S.ι ≫ g)) (y : I.subscheme)
    (hy : I.subschemeι y ∈ S) : IsRegularLocalRing (I.subscheme.presheaf.stalk y) := by
  have hpb := Scheme.IdealSheafData.isPullback_comap I S.ι
  set m := (I.comap S.ι).subschemeMap I S.ι (I.le_map_comap S.ι)
  haveI : IsOpenImmersion m :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb inferInstance
  have hrange : y ∈ Set.range m := by
    have hsnd : y ∈ Set.range (pullback.snd S.ι I.subschemeι) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      show I.subschemeι y ∈ S.ι.opensRange
      rwa [Scheme.Opens.opensRange_ι]
    obtain ⟨w, rfl⟩ := hsnd
    refine ⟨hpb.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd]
  obtain ⟨y', rfl⟩ := hrange
  haveI : LocallyOfFinitePresentation ((I.comap S.ι).subschemeι ≫ S.ι ≫ g) :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth _
  haveI : LocallyOfFiniteType ((I.comap S.ι).subschemeι ≫ S.ι ≫ g) := inferInstance
  have hreg := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk
    ((I.comap S.ι).subschemeι ≫ S.ι ≫ g)).mp hsm y'
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap m y'
  exact IsRegularLocalRing.of_ringEquiv (asIso (m.stalkMap y')).commRingCatIsoToRingEquiv.symm

end Trace

/-! ### General members avoid a point -/

section Avoid

attribute [local instance] globalSectionsModule

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **The members of a generating system vanishing at a point lie on a hyperplane.** The
coefficient vectors `c` with `∑ᵢ cᵢ sᵢ` vanishing at `x` form a `k`-subspace of `kᴺ⁺¹`, which is
proper because the system generates `L` at `x`; so they lie in the zero set of a nonzero linear
polynomial. -/
private theorem exists_polynomial_mem_nonvanishingOpen (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) (x : X) :
    ∃ P : MvPolynomial (Fin (N + 1)) k, P ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c P ≠ 0 → x ∈ nonvanishingOpen X L (systemSection s c) := by
  classical
  have hmem : ∀ c : Fin (N + 1) → k, x ∉ nonvanishingOpen X L (systemSection s c) ↔
      (L.presheaf.Γgerm x).hom (systemSection s c) ∈ Stacks.ModuleStalk.maximalSmul L x := by
    intro c
    rw [Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff, not_not]
  let K : Submodule k (Fin (N + 1) → k) :=
    { carrier := {c | x ∉ nonvanishingOpen X L (systemSection s c)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, hmem, map_add] at ha hb ⊢
        exact Submodule.add_mem _ ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, hmem, map_zero]
        exact Submodule.zero_mem _
      smul_mem' := fun t a ha => by
        simp only [Set.mem_setOf_eq, hmem, map_smul] at ha ⊢
        change (L.presheaf.Γgerm x).hom
          ((Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k X t) •
            systemSection s a) ∈ _
        rw [Stacks.ModuleStalk.Γgerm_smul]
        exact Submodule.smul_mem _ _ ha }
  have hKtop : K ≠ ⊤ := by
    intro h
    have hx : x ∈ ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) := by
      rw [hs]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have : c ∈ K := h ▸ Submodule.mem_top
    exact this hc
  obtain ⟨φ, hφ0, hφK⟩ := Submodule.exists_le_ker_of_lt_top K (lt_top_iff_ne_top.mpr hKtop)
  set P : MvPolynomial (Fin (N + 1)) k :=
    ∑ i, MvPolynomial.C (φ (fun j => if i = j then 1 else 0)) * MvPolynomial.X i
  have heval : ∀ c, MvPolynomial.eval c P = φ c := fun c => by
    rw [LinearMap.pi_apply_eq_sum_univ φ c]
    simp [P, mul_comm]
  refine ⟨P, fun h0 => hφ0 (LinearMap.ext fun c => by simp [← heval, h0]), fun c hc => ?_⟩
  rw [heval] at hc
  by_contra hx
  exact hc (hφK hx)

end Avoid

/-! ### General members of a free system on a normal variety -/

section GeneralMembers

attribute [local instance] globalSectionsModule

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-- A dense open of the spectrum of a domain contains the basic open of a nonzero element. -/
private theorem exists_ne_zero_basicOpen_le {R : Type*} [CommRing R] [IsDomain R]
    (U : Opens (PrimeSpectrum R)) (hU : Dense (U : Set (PrimeSpectrum R))) :
    ∃ f : R, f ≠ 0 ∧ PrimeSpectrum.basicOpen f ≤ U := by
  obtain ⟨x, hx⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨f, fun h => ?_, hfU⟩
  subst h
  exact hxf (by simp)

/-- **The general members of a free system on a normal variety are normal**, in polynomial form:
there is a nonzero polynomial `Q` in the coefficients such that `Z(∑ᵢ cᵢ sᵢ)` is normal as soon as
`Q(c) ≠ 0`. -/
private theorem exists_polynomial_isNormal_zeroScheme [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))] [IsNormal X] (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 →
        IsNormal (Stacks.Divisors.zeroScheme X L (systemSection s c)).subscheme := by
  classical
  set g := X ↘ Spec (.of k)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  haveI : IsNoetherian X := ⟨⟩
  haveI : PerfectField k := PerfectField.ofCharZero
  set S := g.smoothLocus
  have hSreg := (MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField g).1
  haveI : Smooth (S.ι ≫ g) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp [S]
  obtain ⟨⟨U₁, hU₁, hc₁⟩, -⟩ :=
    exists_dense_open_smooth_zeroScheme (k := k) s hs (I := PUnit.{u + 1}) (fun _ => S.ι)
  obtain ⟨G, hG0, hGU⟩ := exists_ne_zero_basicOpen_le U₁ hU₁
  have hX := (isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one X).mp inferInstance
  set Fb : Set X := {x | x ∈ (S : Set X)ᶜ ∧ ringKrullDim (X.presheaf.stalk x) ≤ 2}
  have hFb : Fb.Finite := by
    refine finite_setOf_mem_and_ringKrullDim_le S.isOpen.isClosed_compl 2 fun x hx => ?_
    have hlt : ((1 : ℕ) : WithBot ℕ∞) < ringKrullDim (X.presheaf.stalk x) :=
      lt_of_not_ge fun h => hx ((hSreg x).mpr (hX.2 x h))
    rw [ringKrullDim_stalk_eq_coheight] at hlt ⊢
    exact WithBot.coe_le_coe.mpr (Order.add_one_le_of_lt (by exact_mod_cast hlt :
      (1 : ℕ∞) < Order.coheight x))
  set Fc : Set X := {x | Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) = ((2 : ℕ) : ℕ∞) ∧
      ((2 : ℕ) : WithBot ℕ∞) < ringKrullDim (X.presheaf.stalk x)}
  have hFc : Fc.Finite := finite_setOf_depth_eq_and_lt_ringKrullDim g 2 hX.1
  set F : Set X := insert (genericPoint X) (Fb ∪ Fc)
  have hF : F.Finite := (hFb.union hFc).insert _
  choose P hP0 hP using exists_polynomial_mem_nonvanishingOpen (k := k) s hs
  haveI := hF.fintype
  refine ⟨G * ∏ x : F, P x, mul_ne_zero hG0 (Finset.prod_ne_zero_iff.mpr fun x _ => hP0 x),
    fun c hc => ?_⟩
  rw [map_mul, map_prod] at hc
  have hcG : coefficientPoint c ∈ U₁ := by
    apply hGU
    change G ∉ RingHom.ker (MvPolynomial.eval c)
    exact fun h => left_ne_zero_of_mul hc ((RingHom.mem_ker).mp h)
  have hsm := (hc₁ c hcG).2 PUnit.unit
  have hnv : ∀ x ∈ F, x ∈ nonvanishingOpen X L (systemSection s c) := fun x hx =>
    hP x c ((Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hc)) ⟨x, hx⟩ (Finset.mem_univ _))
  set σ := systemSection s c
  have hσ : σ ≠ 0 := by
    intro h0
    have h := hnv (genericPoint X) (Set.mem_insert _ _)
    rw [Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff, h0, map_zero] at h
    exact h (Submodule.zero_mem _)
  set Z := Stacks.Divisors.zeroScheme X L σ
  have hI := isEffectiveCartierDivisor_zeroScheme_of_ne_zero L σ hσ
  have hZ : ∀ y : Z.subscheme, Z.subschemeι y ∉ F := by
    intro y hyF
    refine notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen L σ (hnv _ hyF) ?_
    rw [Z.mem_supportSet_iff_mem_support]
    change Z.subschemeι y ∈ (Z.support : Set X)
    rw [← Z.range_subschemeι]
    exact ⟨y, rfl⟩
  refine isNormal_subscheme_of_isEffectiveCartierDivisor Z hI (fun y hy => ?_)
    (fun y h => hZ y (Or.inr (Or.inr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩)))
  have hyS : Z.subschemeι y ∈ S := by
    by_contra h
    exact hZ y (Or.inr (Or.inl ⟨h, hy⟩))
  exact isRegularLocalRing_stalk_of_smooth_comap g Z S hsm y hyS

/-- **Normality of general members of a free system.** Let `k` be algebraically closed of
characteristic zero, `X` a normal variety over `k`, `L` an invertible sheaf on `X` and
`V ⊆ H⁰(X, L)` the finite-dimensional system spanned by `s₀, …, s_N`, generating `L`. There are a
dense open of `V` and a dense open of `ℙ(V)` such that the sections `∑ᵢ cᵢ sᵢ` with coefficient
vector `c` in the first, and with `c ≠ 0` and `[c]` in the second, have normal zero scheme
(possibly empty or disconnected). -/
@[mmp "lem_mmp_foundation_free_system_normal_bertini"]
public theorem exists_dense_open_isNormal_zeroScheme [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))] [IsNormal X]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) :
    (∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U →
        IsNormal (Stacks.Divisors.zeroScheme X L (systemSection s c)).subscheme) ∧
    (∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        IsNormal (Stacks.Divisors.zeroScheme X L (systemSection s c)).subscheme) := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_isNormal_zeroScheme s hs
  refine ⟨⟨PrimeSpectrum.basicOpen Q, dense_basicOpen_of_ne_zero hQ0, fun c hc => hQ c ?_⟩, ?_⟩
  · intro h0
    change Q ∉ RingHom.ker (MvPolynomial.eval c) at hc
    exact hc ((RingHom.mem_ker).mpr h0)
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d Q ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ0
    rw [← MvPolynomial.sum_homogeneousComponent Q]
    exact Finset.sum_eq_zero fun i _ => h i
  refine ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      (MvPolynomial.homogeneousComponent d Q), dense_projectiveSpace_basicOpen hd,
    fun c hc hmem => ?_⟩
  have hhc : MvPolynomial.eval c (MvPolynomial.homogeneousComponent d Q) ≠ 0 := by
    intro h0
    change MvPolynomial.homogeneousComponent d Q ∉
      (RingHom.ker (MvPolynomial.eval c)).homogeneousCore
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) at hmem
    exact hmem <| Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨d, MvPolynomial.homogeneousComponent_isHomogeneous d Q⟩ ((RingHom.mem_ker).mpr h0)
  obtain ⟨t, ht, htQ⟩ := exists_ne_zero_eval_smul_ne_zero Q c hhc
  convert hQ (t • c) htQ using 2
  exact (zeroScheme_systemSection_smul s c ht).symm

end GeneralMembers

/-! ### General hyperplane sections -/

section HyperplaneSections

attribute [local instance] MvPolynomial.gradedAlgebra globalSectionsModule

/-! ### The coordinate sections of `𝒪(1)` -/

section Coordinates

variable {k : Type u} [Field k] {N : ℕ}

variable (k N) in
/-- The twisting sheaf `𝒪(1)` on `ℙᴺ_k`, in the spelling of the hyperplanes. -/
private noncomputable abbrev twistOne : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Modules :=
  ProjectiveSpectrum.Proj.twistingSheafModule
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) ((1 : ℕ) : ℤ)

/-- The global section of `𝒪(1)` of a linear form. -/
private noncomputable def formSection (a : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1) :
    Γ(twistOne k N, ⊤) :=
  ProjectiveSpectrum.Proj.degreeSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) 1 a

/-- The coordinate `Tᵢ` as a global section of `𝒪(1)`. -/
private noncomputable def coordSection (i : Fin (N + 1)) : Γ(twistOne k N, ⊤) :=
  formSection ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩

/-- The section of a degree-one form is `k`-linear in the form. -/
private theorem smul_formSection (r : k)
    (a : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1) :
    r • formSection a = formSection (r • a) := by
  refine Subtype.ext (funext fun x => ?_)
  show HomogeneousLocalization.val ((baseRingHom k (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) r).1 x) •
      LocalizedModule.mk (a : MvPolynomial (Fin (N + 1)) k)
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    = LocalizedModule.mk
        ((r • a : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1) :
          MvPolynomial (Fin (N + 1)) k)
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  have hval : HomogeneousLocalization.val ((baseRingHom k (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) r).1 x)
      = Localization.mk (MvPolynomial.C r)
          (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
    unfold baseRingHom
    exact (Stacks.AlgebraicGeometry.ProjEulerSequence.projToSpecCoeff_appTop_val k N r x.1).trans
      (Localization.mk_one_eq_algebraMap (MvPolynomial.C r)).symm
  rw [hval, LocalizedModule.mk_smul_mk, one_mul, Submodule.coe_smul,
    MvPolynomial.smul_eq_C_mul, smul_eq_mul]

/-- `∑ᵢ cᵢ Tᵢ` is the section of the linear form of `c`. -/
private theorem sum_smul_coordSection (c : Fin (N + 1) → k) :
    ∑ i, c i • coordSection (k := k) (N := N) i =
      formSection (linearForm c) := by
  rw [linearForm, formSection, ← ProjectiveSpectrum.Proj.degreeSectionHom_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => smul_formSection (c i) _

end Coordinates

/-! ### The support of a zero scheme -/

section ZeroSchemeSupport

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
private local instance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-- **The support of the zero scheme of a section is the complement of its nonvanishing open.**
On an affine open inside a trivializing open of `L`, the ideal of `Z(s)` is generated by the
trivializing function of `s`, and the nonvanishing locus is where that function is a unit. -/
private theorem mem_supportSet_zeroScheme_iff_notMem (s : Γ(L, ⊤)) (y : X) :
    y ∈ (zeroScheme X L s).supportSet ↔ y ∉ nonvanishingOpen X L s := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 L
  obtain ⟨z, hz⟩ : ∃ z : X, y ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top y)
  obtain ⟨t⟩ := htriv z
  obtain ⟨W, hW, hyW, hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hz
  let t' := t.comp (homOfLE hWV)
  let e : Γ(L, W) ≃ₗ[Γ(X, W)] Γ(X, W) := t'.θ W (𝟙 W)
  set a : Γ(X, W) := e (L.presheaf.map (homOfLE le_top).op s) with ha
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨W, hW⟩) hyW,
    zeroScheme_ideal_of_trivialization X L s ⟨W, hW⟩ e a rfl,
    Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_iff_not]
  exact ((X.mem_basicOpen a y hyW).trans
    (Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit t' s hyW).symm)

end ZeroSchemeSupport

/-! ### Hyperplane sections as zero schemes of a free system -/

section Pullback

variable {k : Type u} [Field k] {N : ℕ} {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
  (ψ : Z ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))

/-- The pullback `ψ^* 𝒪(1)` of the twisting sheaf. -/
private noncomputable abbrev pullTwist : Z.Modules :=
  (Scheme.Modules.pullback ψ).obj (twistOne k N)

private local instance : Stacks.Ample.IsInvertibleModule Z (pullTwist ψ) :=
  Stacks.AlgebraicGeometry.ProjChartRatioPullback.isInvertibleModule_schemeModulesPullback ψ _

private local instance :
    SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property (pullTwist ψ) :=
  (inferInstance : Stacks.Ample.IsInvertibleModule Z (pullTwist ψ))

/-- The pulled-back coordinates `ψ^* T₀, …, ψ^* T_N`. -/
private noncomputable def pullSystem : Fin (N + 1) → Γ(pullTwist ψ, ⊤) :=
  fun i => pullbackGlobalSections ψ (twistOne k N) (coordSection i)

/-- `∑ᵢ cᵢ ψ^* Tᵢ = ψ^* (∑ᵢ cᵢ Tᵢ)`. -/
private theorem systemSection_pullSystem [ψ.IsOver (Spec (.of k))] (c : Fin (N + 1) → k) :
    systemSection (pullSystem ψ) c =
      pullbackGlobalSections ψ (twistOne k N) (formSection (linearForm c)) := by
  rw [systemSection_apply, ← sum_smul_coordSection, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackGlobalSections_smul_scalar
    k ψ _ (by simp) (c i) _).symm

/-- **The zero scheme of `∑ᵢ cᵢ ψ^* Tᵢ` is the hyperplane section `ψ⁻¹(V(∑ᵢ cᵢ Tᵢ))`.** -/
private theorem zeroScheme_pullSystem [ψ.IsOver (Spec (.of k))] (c : Fin (N + 1) → k) :
    zeroScheme Z (pullTwist ψ) (systemSection (pullSystem ψ) c) = hyperplaneSection ψ c := by
  rw [systemSection_pullSystem]
  exact Stacks.Divisors.zeroScheme_pullback ψ (twistOne k N) (formSection (linearForm c))

omit [Z.Over (Spec (.of k))] in
/-- A point lies on the hyperplane section of `c` iff the homogeneous prime of its image contains
the linear form of `c`. -/
private theorem mem_support_hyperplaneSection_iff (c : Fin (N + 1) → k) (z : Z) :
    z ∈ (hyperplaneSection ψ c).support ↔
      (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈ (ψ z).asHomogeneousIdeal := by
  rw [hyperplaneSection, Scheme.IdealSheafData.support_comap]
  exact MMP.ProjectiveSpace.mem_support_hyperplane_iff _ _

/-- The linear form of a standard basis vector is the coordinate. -/
private theorem coe_linearForm_single (i : Fin (N + 1)) :
    (linearForm (Pi.single i 1 : Fin (N + 1) → k) : MvPolynomial (Fin (N + 1)) k) =
      MvPolynomial.X i := by
  classical
  simp [linearForm, Pi.single_apply]

/-- **The pulled-back coordinates generate `ψ^* 𝒪(1)`.** -/
private theorem iSup_nonvanishingOpen_pullSystem [ψ.IsOver (Spec (.of k))] :
    ⨆ c : Fin (N + 1) → k, nonvanishingOpen Z (pullTwist ψ) (systemSection (pullSystem ψ) c) =
      ⊤ := by
  refine eq_top_iff.mpr fun z _ => Opens.mem_iSup.mpr ?_
  obtain ⟨i, hi⟩ := MMP.ProjectiveSpace.exists_X_notMem (ψ z)
  refine ⟨Pi.single i 1, not_not.mp fun h => hi ?_⟩
  rw [← coe_linearForm_single (k := k), ← mem_support_hyperplaneSection_iff, ←
    zeroScheme_pullSystem]
  exact (mem_supportSet_zeroScheme_iff_notMem _ _ _).mpr h

end Pullback

/-! ### A general hyperplane misses finitely many given points -/

section Avoid

variable {k : Type u} [Field k] {N : ℕ}

/-- `∑ᵢ cᵢ Tᵢ`, as a polynomial, is linear in `c`. -/
private theorem coe_linearForm (c : Fin (N + 1) → k) :
    (linearForm c : MvPolynomial (Fin (N + 1)) k) =
      Fintype.linearCombination k (fun i => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k))
        c := by
  simp [linearForm, Fintype.linearCombination_apply]

/-- **The hyperplanes through a point form a proper linear subspace** of the dual space: there is
a nonzero linear polynomial `Q` in the coefficients such that `∑ᵢ cᵢ Tᵢ` does not vanish at `p`
as soon as `Q(c) ≠ 0`. -/
private theorem exists_isHomogeneous_notMem (p : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q.IsHomogeneous 1 ∧ Q ≠ 0 ∧
      ∀ c : Fin (N + 1) → k, MvPolynomial.eval c Q ≠ 0 →
        (linearForm c : MvPolynomial (Fin (N + 1)) k) ∉ p.asHomogeneousIdeal := by
  classical
  set ℓ := Fintype.linearCombination k
    (fun i => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) with hℓ
  set K : Submodule k (Fin (N + 1) → k) :=
    (p.asHomogeneousIdeal.toIdeal.restrictScalars k).comap ℓ with hK
  obtain ⟨i, hi⟩ := MMP.ProjectiveSpace.exists_X_notMem p
  have hKtop : K < ⊤ := lt_top_iff_ne_top.mpr fun h => hi <| by
    have hmem : (Pi.single i 1 : Fin (N + 1) → k) ∈ K := h ▸ Submodule.mem_top
    rwa [hK, Submodule.mem_comap, hℓ, ← coe_linearForm, coe_linearForm_single] at hmem
  obtain ⟨g, hg0, hKg⟩ := Submodule.exists_le_ker_of_lt_top K hKtop
  set Q : MvPolynomial (Fin (N + 1)) k :=
    ∑ j, MvPolynomial.C (g (Pi.single j 1)) * MvPolynomial.X j with hQ
  have heval : ∀ c, MvPolynomial.eval c Q = g c := by
    intro c
    conv_rhs => rw [← Finset.univ_sum_single c]
    simp only [hQ, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  refine ⟨Q, ?_, ?_, ?_⟩
  · exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
      (MvPolynomial.isHomogeneous_C_mul_X _ j)
  · intro h0
    apply hg0
    refine LinearMap.ext fun c => ?_
    rw [← heval, h0, map_zero, LinearMap.zero_apply]
  · intro c hc hmem
    apply hc
    have hcK : c ∈ K := by
      change ℓ c ∈ p.asHomogeneousIdeal.toIdeal
      rwa [← coe_linearForm]
    rw [heval]
    exact hKg hcK

/-- **A general hyperplane misses finitely many given points**: there is a dense open of the dual
projective space such that the hyperplane `[c]` of each of its points passes through none of
them. -/
private theorem exists_dense_open_forall_notMem (P : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) (hP : P.Finite) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U → ∀ p ∈ P,
        (linearForm c : MvPolynomial (Fin (N + 1)) k) ∉ p.asHomogeneousIdeal := by
  classical
  choose Q hQh hQ0 hQ using fun p : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) => exists_isHomogeneous_notMem p
  set R := ∏ p ∈ hP.toFinset, Q p with hR
  have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hQ0 p
  have hRh : R.IsHomogeneous (∑ p ∈ hP.toFinset, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun p _ => hQh p
  refine ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) R,
    dense_projectiveSpace_basicOpen hR0, fun c hc hmem p hp => hQ p c ?_⟩
  have hRc : MvPolynomial.eval c R ≠ 0 := by
    intro h0
    change R ∉ (RingHom.ker (MvPolynomial.eval c)).homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) at hmem
    exact hmem (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨_, hRh⟩
      ((RingHom.mem_ker).mpr h0))
  rw [hR, map_prod] at hRc
  exact Finset.prod_ne_zero_iff.mp hRc p (hP.mem_toFinset.mpr hp)

end Avoid

/-! ### Homeomorphisms -/

/-- A nonempty subset of finite dimension has dimension a natural number. -/
private theorem exists_natCast_eq_topologicalKrullDim {Y : Type*} [TopologicalSpace Y]
    {S : Set Y} (hne : S.Nonempty) (hfin : topologicalKrullDim S ≠ ⊤) :
    ∃ n : ℕ, topologicalKrullDim S = n := by
  have hbot : topologicalKrullDim S ≠ ⊥ := by
    obtain ⟨s, hs⟩ := hne
    have : Nonempty (IrreducibleCloseds S) :=
      ⟨⟨closure {⟨s, hs⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_ne_bot_iff.mpr this
  induction h : topologicalKrullDim S with
  | bot => exact absurd h hbot
  | coe m =>
    induction m with
    | top => exact absurd h hfin
    | coe m => exact ⟨m, rfl⟩

/-- A subset of dimension at least a natural number is nonempty. -/
private theorem nonempty_of_natCast_le_topologicalKrullDim {Y : Type*} [TopologicalSpace Y]
    {S : Set Y} {n : ℕ} (h : (n : WithBot ℕ∞) ≤ topologicalKrullDim S) : S.Nonempty := by
  by_contra hS
  rw [Set.not_nonempty_iff_eq_empty] at hS
  subst hS
  have : IsEmpty (IrreducibleCloseds (∅ : Set Y)) :=
    ⟨fun Z => by
      obtain ⟨⟨x, hx⟩, -⟩ := Z.isIrreducible.nonempty
      exact hx⟩
  have h0 : topologicalKrullDim (∅ : Set Y) = ⊥ := Order.krullDim_eq_bot
  rw [h0] at h
  exact absurd (le_bot_iff.mp h) (by simp)

/-- If `a + 1 = N` in `WithBot ℕ∞` with `N ≥ 1`, then `a = N - 1`. -/
private theorem eq_natCast_sub_one_of_add_one_eq {a : WithBot ℕ∞} {N : ℕ}
    (h : a + 1 = (N : WithBot ℕ∞)) (hN : 1 ≤ N) : a = ((N - 1 : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [this] at h
      exact ENat.top_ne_natCast N (WithBot.coe_injective h)
    | coe a =>
      have : ((a + 1 : ℕ) : WithBot ℕ∞) = (N : WithBot ℕ∞) := by exact_mod_cast h
      have : a + 1 = N := by exact_mod_cast this
      subst this
      simp

/-- A homeomorphism carries irreducible components to irreducible components. -/
private theorem image_mem_irreducibleComponents {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) {C : Set A} (hC : C ∈ irreducibleComponents A) :
    e '' C ∈ irreducibleComponents B := by
  have h := preimage_mem_irreducibleComponents hC e.symm.isOpenEmbedding
    (by rw [e.symm.range_coe, Set.inter_univ]; exact hC.1.nonempty)
  rwa [e.preimage_symm] at h

/-- A homeomorphism preserves the dimension of a subset. -/
private theorem topologicalKrullDim_image_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (C : Set A) :
    topologicalKrullDim (e '' C) = topologicalKrullDim C :=
  (e.image C).isHomeomorph.topologicalKrullDim_eq.symm

/-! ### Dense opens of the dual projective space -/

section DenseOpens

variable {k : Type u} [Field k] {N : ℕ}

/-- The intersection of two dense opens is a dense open. -/
private theorem dense_coe_inf {Y : Type*} [TopologicalSpace Y] {U V : Opens Y}
    (hU : Dense (U : Set Y)) (hV : Dense (V : Set Y)) : Dense ((U ⊓ V : Opens Y) : Set Y) := by
  rw [Opens.coe_inf]
  exact hU.inter_of_isOpen_left hV U.isOpen

/-- Two properties holding on dense opens of the dual projective space hold together on one. -/
private theorem exists_dense_open_and {P Q : ∀ c : Fin (N + 1) → k, c ≠ 0 → Prop}
    (hP : ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ c hc, dualPoint c hc ∈ U → P c hc)
    (hQ : ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ c hc, dualPoint c hc ∈ U → Q c hc) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ c hc, dualPoint c hc ∈ U → P c hc ∧ Q c hc := by
  obtain ⟨U, hU, hUP⟩ := hP
  obtain ⟨V, hV, hVQ⟩ := hQ
  exact ⟨U ⊓ V, dense_coe_inf hU hV, fun c hc h => ⟨hUP c hc h.1, hVQ c hc h.2⟩⟩

/-- Finitely many properties holding on dense opens of the dual projective space hold together on
one. -/
private theorem exists_dense_open_forall {ι : Type*} [Finite ι]
    {P : ι → ∀ c : Fin (N + 1) → k, c ≠ 0 → Prop}
    (h : ∀ i, ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ c hc, dualPoint c hc ∈ U → P i c hc) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ c hc, dualPoint c hc ∈ U → ∀ i, P i c hc := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
        ∀ c hc, dualPoint c hc ∈ U → ∀ i ∈ s, P i c hc by
    obtain ⟨U, hU, h'⟩ := H Finset.univ
    exact ⟨U, hU, fun c hc hm i => h' c hc hm i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨⊤, by simpa using dense_univ, fun _ _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨U, hU, hUP⟩ := exists_dense_open_and (h a) ih
    refine ⟨U, hU, fun c hc hm i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (hUP c hc hm).1
    · exact (hUP c hc hm).2 i hi

end DenseOpens

/-! ### Incidence with hyperplanes -/

section Incidence

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (ψ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))

/-- A point lies on the hyperplane section of `c` iff the section `∑ᵢ cᵢ ψ^* Tᵢ` vanishes there. -/
private theorem mem_support_hyperplaneSection_iff_notMem [ψ.IsOver (Spec (.of k))]
    (c : Fin (N + 1) → k) (x : X) :
    x ∈ (hyperplaneSection ψ c).support ↔
      x ∉ nonvanishingOpen X (pullTwist ψ) (systemSection (pullSystem ψ) c) := by
  rw [← zeroScheme_pullSystem ψ c]
  exact mem_supportSet_zeroScheme_iff_notMem _ _ x

end Incidence

/-! ### Closed points of projective space -/

section ClosedPoints

variable {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ}

/-- **A closed point of `ℙᴺ_k` is a `k`-point `(a₀ : ⋯ : a_N)`**, `k` algebraically closed: its
homogeneous prime lies in a maximal ideal `ker (eval a)` other than the irrelevant one, as
`k[T₀, …, T_N]` is a Jacobson ring. -/
private theorem exists_eq_point_of_isClosed (p : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    (hp : IsClosed ({p} : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)))) :
    ∃ (a : Fin (N + 1) → k) (ha : a ≠ 0), p = dualPoint a ha := by
  classical
  set I := p.asHomogeneousIdeal.toIdeal with hI
  have hIp : I.IsPrime := p.isPrime
  set m₀ : Ideal (MvPolynomial (Fin (N + 1)) k) := RingHom.ker (MvPolynomial.eval 0) with hm₀
  -- the irrelevant ideal lies in the kernel of evaluation at `0`
  have hirr : (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal ≤ m₀ := by
    intro f hf
    change f ∈ HomogeneousIdeal.irrelevant _ at hf
    rw [HomogeneousIdeal.mem_irrelevant_iff] at hf
    rw [GradedRing.proj_apply] at hf
    have h0 : MvPolynomial.homogeneousComponent 0 f = 0 :=
      (MvPolynomial.decomposition.decompose'_apply f 0).symm.trans hf
    rw [hm₀, RingHom.mem_ker, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
    have := congrArg (fun p : MvPolynomial _ _ => p.coeff 0) h0
    simpa [MvPolynomial.coeff_homogeneousComponent] using this
  -- a maximal ideal containing `I` other than `ker (eval 0)`
  obtain ⟨m, hm, hIm, hm0⟩ : ∃ m : Ideal (MvPolynomial (Fin (N + 1)) k), m.IsMaximal ∧ I ≤ m ∧
      m ≠ m₀ := by
    by_contra hcon
    push Not at hcon
    have hjac : I.jacobson = I := IsJacobsonRing.out inferInstance hIp.isRadical
    have hle : m₀ ≤ I.jacobson := by
      refine le_sInf fun J hJ => ?_
      rw [hcon J hJ.2 hJ.1]
    exact p.not_irrelevant_le (hirr.trans (hle.trans hjac.le))
  obtain ⟨a, rfl⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hm
  have hker : ∀ f, f ∈ MvPolynomial.vanishingIdeal k {a} ↔ MvPolynomial.eval a f = 0 := by
    intro f
    simp [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  have ha : a ≠ 0 := by
    rintro rfl
    exact hm0 (Ideal.ext fun f => by rw [hker, hm₀, RingHom.mem_ker])
  refine ⟨a, ha, ?_⟩
  have hle : p.asHomogeneousIdeal ≤
      (dualPoint a ha).asHomogeneousIdeal := by
    have hIa : p.asHomogeneousIdeal.toIdeal ≤ RingHom.ker (MvPolynomial.eval a) := fun f hf =>
      (RingHom.mem_ker).mpr ((hker f).mp (hIm hf))
    exact (Ideal.homogeneousCore.gc _).le_iff_le.mp hIa
  have hmem := (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp hle
  exact (Set.mem_singleton_iff.mp (hp.closure_subset hmem)).symm

/-- **Closed points of `ℙᴺ_k` are separated by hyperplanes.** -/
private theorem eq_of_isClosed_of_forall_linearForm_mem_iff {p q : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)}
    (hp : IsClosed ({p} : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))))
    (hq : IsClosed ({q} : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))))
    (h : ∀ c : Fin (N + 1) → k, (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈
      p.asHomogeneousIdeal ↔ (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈
        q.asHomogeneousIdeal) : p = q := by
  classical
  obtain ⟨a, ha, rfl⟩ := exists_eq_point_of_isClosed p hp
  obtain ⟨b, hb, rfl⟩ := exists_eq_point_of_isClosed q hq
  have hlin : ∀ (a : Fin (N + 1) → k) (ha : a ≠ 0) (c : Fin (N + 1) → k),
      (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈
        (dualPoint a ha).asHomogeneousIdeal ↔
        Fintype.linearCombination k a c = 0 := by
    intro a ha c
    rw [mem_dualPoint_iff a ha
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp (linearForm c).2), coe_linearForm,
      Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
    simp [mul_comm]
  set fa := Fintype.linearCombination k a with hfa
  set fb := Fintype.linearCombination k b with hfb
  have hab : ∀ c, fa c = 0 ↔ fb c = 0 := fun c => (hlin a ha c).symm.trans ((h c).trans
    (hlin b hb c))
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (funext hcon)
  have hfa_single : ∀ j, fa (Pi.single j 1) = a j := fun j => by
    rw [hfa, Fintype.linearCombination_apply_single, one_smul]
  have hfb_single : ∀ j, fb (Pi.single j 1) = b j := fun j => by
    rw [hfb, Fintype.linearCombination_apply_single, one_smul]
  set c₀ : Fin (N + 1) → k := Pi.single i 1
  have hc₀ : fa c₀ ≠ 0 := by rwa [hfa_single]
  set t := fb c₀ / fa c₀
  have hprop : ∀ c, fb c = t * fa c := by
    intro c
    have hd : fa (c - (fa c / fa c₀) • c₀) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hc₀, sub_self]
    have hd' := (hab _).mp hd
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hd'
    rw [hd']
    simp only [t]
    field_simp
  have hbt : b = t • a := funext fun j => by
    rw [← hfb_single, hprop, hfa_single, Pi.smul_apply, smul_eq_mul]
  have ht : t ≠ 0 := by
    rintro ht
    rw [ht, zero_smul] at hbt
    exact hb hbt
  have key : ∀ (b' : Fin (N + 1) → k) (hb' : b' ≠ 0), b' = t • a →
      dualPoint a ha =
        dualPoint b' hb' := by
    rintro _ _ rfl
    exact (dualPoint_smul a ha ht).symm
  exact key b hb hbt

/-- Two continuous maps out of a Jacobson space which agree on closed points satisfy
`g x ⤳ f x` at every point. -/
private theorem specializes_of_forall_isClosed_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [JacobsonSpace X] {f g : X → Y} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ y, IsClosed ({y} : Set X) → f y = g y) (x : X) :
    g x ⤳ f x := by
  rw [specializes_iff_mem_closure]
  have hC : closure (closure {x} ∩ closedPoints X) = closure {x} :=
    JacobsonSpace.closure_inter_closedPoints isClosed_closure
  have h1 : f x ∈ closure (f '' (closure {x} ∩ closedPoints X)) := by
    have hx : x ∈ closure (closure {x} ∩ closedPoints X) := by
      rw [hC]
      exact subset_closure rfl
    exact image_closure_subset_closure_image hf ⟨x, hx, rfl⟩
  have h2 : f '' (closure {x} ∩ closedPoints X) ⊆ g '' closure {x} := by
    rintro _ ⟨y, ⟨hy, hyc⟩, rfl⟩
    exact ⟨y, hy, (h y hyc).symm⟩
  have h3 : g '' closure {x} ⊆ closure {g x} := by
    have := image_closure_subset_closure_image hg (s := {x})
    rwa [Set.image_singleton] at this
  exact closure_minimal (h2.trans h3) isClosed_closure h1

/-- **Two morphisms to `ℙᴺ_k` with the same hyperplane sections agree on points.** They agree on
closed points, which separate hyperplanes, and closed points are dense in every closed subset of
a scheme locally of finite type over `k`. -/
private theorem apply_eq_of_forall_linearForm_mem_iff {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (f g : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (h : ∀ (x : X) (c : Fin (N + 1) → k), (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈
      (f x).asHomogeneousIdeal ↔ (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈
        (g x).asHomogeneousIdeal) (x : X) : f x = g x := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  have : JacobsonSpace (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) :=
    LocallyOfFiniteType.jacobsonSpace (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) ↘ Spec (.of k))
  have hcl : ∀ y : X, IsClosed ({y} : Set X) → f y = g y := fun y hy =>
    eq_of_isClosed_of_forall_linearForm_mem_iff
      (f.closePoints_subset_preimage_closedPoints hy)
      (g.closePoints_subset_preimage_closedPoints hy) (h y)
  exact (specializes_of_forall_isClosed_eq g.continuous f.continuous
    (fun y hy => (hcl y hy).symm) x).antisymm
    (specializes_of_forall_isClosed_eq f.continuous g.continuous hcl x) |>.eq

end ClosedPoints

/-! ### The morphism of a generating system on points -/

section PointValue

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
  Stacks.AlgebraicGeometry.ProjDegreeOneRepresents

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {V : Type u} [AddCommGroup V]
  [Module k V]

/-- The preimage of the standard open `D₊(v)` under the morphism of a generating system is the
nonvanishing open of the section of `v`. -/
private theorem preimage_basicOpen_morphismOfGeneratingSections'
    (ψ : V →ₗ[k] Γ(L, ⊤)) (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (v : V) :
    morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V v) =
      nonvanishingOpen X L (ψ v) := by
  refine ((classifies_classifyingPair k V L ψ hψ).1 (degreeOneElement k V v)).trans ?_
  change nonvanishingOpen X (Stacks.TensorPowers.natTensorPow L 1)
      ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V v).2 1) = _
  rw [pow_degreeOneElement, nonvanishingOpen_twistOneSection]

end PointValue

/-! ### Finiteness -/

/-- A morphism whose composite with some `g` is locally of finite type is locally of finite
type. -/
private theorem locallyOfFiniteType_of_comp_eq {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    {h : X ⟶ S} [LocallyOfFiniteType h] (e : f ≫ g = h) : LocallyOfFiniteType f := by
  subst e
  exact locallyOfFiniteType_of_comp f g

/-- `ℙᴺ_k` is Noetherian. -/
private theorem isNoetherian_projectiveSpace {k : Type u} [Field k] {N : ℕ} :
    IsNoetherian (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) :=
  { __ := LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) ↘ Spec (.of k)),
    __ := QuasiCompact.compactSpace_of_compactSpace (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) ↘ Spec (.of k)) }

/-! ### The dimension of the image -/

section ImageDimension

variable {k : Type u} [Field k] {N : ℕ}

/-- In a Noetherian sober space, a constructible set `C` containing a point `η` contains every
specialization of `η` lying in a suitable open neighbourhood of `η`: the specializations of `η`
outside `C` form a constructible set whose closure misses `η`. -/
private theorem exists_isOpen_forall_specializes_mem_of_isConstructible {A : Type*}
    [TopologicalSpace A] [NoetherianSpace A] [QuasiSober A] [T0Space A] {C : Set A}
    (hC : Topology.IsConstructible C) {η : A} (hη : η ∈ C) :
    ∃ O : Set A, IsOpen O ∧ η ∈ O ∧ ∀ t ∈ O, η ⤳ t → t ∈ C := by
  have := SpectralSpace.of_noetherianSpace A
  have hcl : Topology.IsConstructible (closure ({η} : Set A)) :=
    Topology.isConstructible_compl.mp
      ((NoetherianSpace.isCompact _).isConstructible isClosed_closure.isOpen_compl)
  have hD : Topology.IsConstructible (closure ({η} : Set A) ∩ Cᶜ) := hcl.inter hC.compl
  refine ⟨(closure (closure ({η} : Set A) ∩ Cᶜ))ᶜ, isClosed_closure.isOpen_compl, fun hηD ↦ ?_,
    fun t ht hηt ↦ ?_⟩
  · obtain ⟨z, hz, hzη⟩ := hD.exists_mem_specializes_of_mem_closure hηD
    have hz' : z = η := (hzη.antisymm (specializes_iff_mem_closure.mpr hz.1)).eq
    exact hz.2 (hz' ▸ hη)
  · by_contra htC
    exact ht (subset_closure ⟨specializes_iff_mem_closure.mp hηt, htC⟩)

/-- **Chevalley.** For `f : X ⟶ S` locally of finite type with `S` locally Noetherian and `a ∈ X`,
every specialization of `f a` in a suitable open neighbourhood of `f a` is the image of a
specialization of `a`: the image of the closure of `a` in an affine chart is constructible. -/
private theorem exists_isOpen_forall_specializes_exists_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (a : X) :
    ∃ O : Set S, IsOpen O ∧ f a ∈ O ∧ ∀ t ∈ O, f a ⤳ t → ∃ b : X, a ⤳ b ∧ f b = t := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hV, hfaV, -⟩ := (Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show f a ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨W, hW, haW, hWV⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show a ∈ f ⁻¹ᵁ V from hfaV)
  have : IsAffine (V : Scheme.{u}) := hV
  have : IsAffine (W : Scheme.{u}) := hW
  have : IsNoetherian (V : Scheme.{u}) := {}
  have : IsNoetherian (W : Scheme.{u}) := {}
  let g : (W : Scheme.{u}) ⟶ V := f.resLE V W hWV
  have hg : ∀ w, ((Scheme.Opens.ι V) (g w) : S) = f ((Scheme.Opens.ι W) w) := fun w ↦ by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
  have : QuasiCompact g := inferInstance
  let a' : (W : Scheme.{u}) := ⟨a, haW⟩
  let η' : (V : Scheme.{u}) := ⟨f a, hfaV⟩
  have hcl : Topology.IsConstructible (closure ({a'} : Set (W : Scheme.{u}))) :=
    Topology.isConstructible_compl.mp
      ((NoetherianSpace.isCompact _).isConstructible isClosed_closure.isOpen_compl)
  have hC := g.isConstructible_image hcl
  have hη' : η' ∈ g '' closure ({a'} : Set (W : Scheme.{u})) := by
    refine ⟨a', subset_closure rfl, (Scheme.Opens.ι V).isOpenEmbedding.injective ?_⟩
    rw [hg]
    rfl
  obtain ⟨O, hO, hηO, hOC⟩ := exists_isOpen_forall_specializes_mem_of_isConstructible hC hη'
  refine ⟨(Scheme.Opens.ι V) '' O, (Scheme.Opens.ι V).isOpenEmbedding.isOpenMap _ hO,
    ⟨η', hηO, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩ hηt
  have hηt' : η' ⤳ t := (Scheme.Opens.ι V).isOpenEmbedding.isInducing.specializes_iff.mp hηt
  obtain ⟨w, hw, hwt⟩ := hOC t ht hηt'
  refine ⟨(Scheme.Opens.ι W) w,
    (specializes_iff_mem_closure.mpr hw).map (Scheme.Opens.ι W).continuous, ?_⟩
  rw [← hg, hwt]

/-- **Chevalley.** The image of a morphism locally of finite type from an irreducible scheme to a
locally Noetherian scheme contains an open neighbourhood of the image of the generic point in the
closure of the image. -/
private theorem exists_isOpen_closure_range_inter_subset {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    ∃ O : Set Y, IsOpen O ∧ f (genericPoint X) ∈ O ∧
      closure (Set.range f.base) ∩ O ⊆ Set.range f.base := by
  obtain ⟨O, hO, haO, hOt⟩ := exists_isOpen_forall_specializes_exists_specializes f
    (genericPoint X)
  refine ⟨O, hO, haO, fun t ⟨ht, htO⟩ => ?_⟩
  have hcl : closure (Set.range f.base) ⊆ closure {f (genericPoint X)} := by
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨x, rfl⟩
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes x).map f.continuous)
  obtain ⟨b, -, rfl⟩ := hOt t htO (specializes_iff_mem_closure.mpr (hcl ht))
  exact ⟨b, rfl⟩

/-- The image of a morphism of finite type `k`-schemes from an irreducible scheme has the
dimension of its closure. -/
private theorem topologicalKrullDim_closure_range_le {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [IrreducibleSpace X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [IsLocallyNoetherian Y] [NoetherianSpace Y] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    topologicalKrullDim (closure (Set.range f.base)) ≤ topologicalKrullDim (Set.range f.base) := by
  classical
  have := locallyOfFiniteType_of_comp_eq f _ (comp_over f (Spec (.of k)))
  obtain ⟨O, hO, hηO, hsub⟩ := exists_isOpen_closure_range_inter_subset f
  set W : Closeds Y := ⟨closure (Set.range f.base), isClosed_closure⟩
  set J := Scheme.IdealSheafData.vanishingIdeal W
  have hrange : Set.range J.subschemeι = closure (Set.range f.base) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  letI : J.subscheme.Over (Spec (.of k)) := ⟨J.subschemeι ≫ Y ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (J.subscheme ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (J.subschemeι ≫ Y ↘ Spec (.of k))
    infer_instance
  have : NoetherianSpace J.subscheme :=
    J.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let e₁ : J.subscheme ≃ₜ closure (Set.range f.base) :=
    J.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hirr : IsIrreducible (closure (Set.range f.base)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ X).image _ f.continuous.continuousOn).closure
  have : IrreducibleSpace J.subscheme := by
    have : IrreducibleSpace (closure (Set.range f.base)) := Subtype.irreducibleSpace hirr
    have h := (IrreducibleSpace.isIrreducible_univ (closure (Set.range f.base))).image e₁.symm
      e₁.symm.continuous.continuousOn
    rw [Set.image_univ, e₁.symm.surjective.range_eq] at h
    exact (irreducibleSpace_def _).mpr h
  let O' : J.subscheme.Opens := J.subschemeι ⁻¹ᵁ ⟨O, hO⟩
  have hO'ne : (O' : Set J.subscheme).Nonempty := by
    obtain ⟨y, hy⟩ : f (genericPoint X) ∈ Set.range J.subschemeι :=
      hrange ▸ subset_closure ⟨_, rfl⟩
    exact ⟨y, show J.subschemeι y ∈ O from hy ▸ hηO⟩
  have hdense : Dense (Set.range O'.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact O'.isOpen.dense hO'ne
  have h1 := Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion k
    O'.ι (O'.ι ≫ (J.subscheme ↘ Spec (.of k))) (J.subscheme ↘ Spec (.of k)) rfl hdense
  have h2 : topologicalKrullDim O'.toScheme =
      topologicalKrullDim (Set.range (O'.ι ≫ J.subschemeι).base) :=
    (O'.ι ≫ J.subschemeι).isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  have h3 : Set.range (O'.ι ≫ J.subschemeι).base ⊆ Set.range f.base := by
    rintro _ ⟨x, rfl⟩
    refine hsub ⟨hrange ▸ ⟨_, rfl⟩, ?_⟩
    exact x.2
  calc topologicalKrullDim (closure (Set.range f.base))
      = topologicalKrullDim J.subscheme := e₁.isHomeomorph.topologicalKrullDim_eq.symm
    _ ≤ topologicalKrullDim O'.toScheme := h1
    _ = _ := h2
    _ ≤ _ := topologicalKrullDim_le_of_subset h3

open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare in
/-- The image of the morphism `X ⟶ ℙ(V^*)` of the pulled-back coordinates has the dimension of the
closure of the image of `ψ`. -/
private theorem le_topologicalKrullDim_range_morphismOfGeneratingSections [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsVariety k (X ↘ Spec (.of k))]
    (ψ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [ψ.IsOver (Spec (.of k))] :
    topologicalKrullDim (closure (Set.range ψ.base)) ≤ topologicalKrullDim (Set.range
      (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections k
        (Fin (N + 1) → k) (pullTwist ψ) (systemSection (pullSystem ψ))
        (iSup_nonvanishingOpen_pullSystem ψ)).base) := by
  classical
  set g := Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections k
    (Fin (N + 1) → k) (pullTwist ψ) (systemSection (pullSystem ψ))
    (iSup_nonvanishingOpen_pullSystem ψ) with hg
  set b := Pi.basisFun k (Fin (N + 1))
  set e := projectiveSpaceOfModuleIsoProjMvPolynomial b
  have hgo : g ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k) = X ↘ Spec (.of k) :=
    morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec _ _
  have := locallyOfFiniteType_of_comp_eq g _ hgo
  have := locallyOfFiniteType_of_comp_eq ψ _ (comp_over ψ (Spec (.of k)))
  have hφℓ : ∀ c : Fin (N + 1) → k, (SymPow.gradedMvPolynomialInv b)
      (linearForm c : MvPolynomial (Fin (N + 1)) k) =
        SymmetricAlgebra.ι k (Fin (N + 1) → k) c := by
    intro c
    rw [SymPow.gradedMvPolynomialInv_apply, AlgEquiv.symm_apply_eq,
      Stacks.SymmetricFree.equivMvPolynomial_ι, coe_linearForm]
    simp [b, Module.Basis.constr_apply, Fintype.linearCombination_apply, Finsupp.sum_fintype]
  have hpt : ∀ x, (g ≫ e.hom) x = ψ x := by
    refine apply_eq_of_forall_linearForm_mem_iff (g ≫ e.hom) ψ fun x c => ?_
    have h1 : (g ≫ e.hom) x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        (linearForm c : MvPolynomial (Fin (N + 1)) k) ↔
        x ∈ nonvanishingOpen X (pullTwist ψ) (systemSection (pullSystem ψ) c) := by
      change x ∈ (g ≫ e.hom) ⁻¹ᵁ (Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        (linearForm c : MvPolynomial (Fin (N + 1)) k)) ↔ _
      rw [Scheme.Hom.comp_preimage, projectiveSpaceOfModuleIsoProjMvPolynomial_hom,
        Proj.map_preimage_basicOpen, hφℓ, hg, preimage_basicOpen_morphismOfGeneratingSections']
    rw [Proj.mem_basicOpen] at h1
    rw [← mem_support_hyperplaneSection_iff ψ c x, mem_support_hyperplaneSection_iff_notMem, ← h1,
      not_not]
  have hrange : Set.range ψ.base = e.hom.homeomorph '' Set.range g.base := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun x => (hpt x).symm)
  have := isNoetherian_projectiveSpace (k := k) (N := N)
  calc topologicalKrullDim (closure (Set.range ψ.base))
      ≤ topologicalKrullDim (Set.range ψ.base) := topologicalKrullDim_closure_range_le (k := k) ψ
    _ = _ := by rw [hrange, topologicalKrullDim_image_homeomorph]

end ImageDimension

/-! ### The hyperplane section is a Cartier divisor -/

section Cartier

variable {k : Type u} [Field k] {N : ℕ}

/-- **A hyperplane section is an effective Cartier divisor** when the hyperplane misses the
image of the generic point of the integral scheme `X`. -/
private theorem isEffectiveCartierDivisor_hyperplaneSection {X : Scheme.{u}}
    [IsIntegral X] (ψ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) (c : Fin (N + 1) → k) (hc : c ≠ 0)
    (hgen : (linearForm c : MvPolynomial (Fin (N + 1)) k) ∉
      (ψ (genericPoint X)).asHomogeneousIdeal) :
    Stacks.Divisors.IsEffectiveCartierDivisor (hyperplaneSection ψ c) := by
  have hp0 : (linearForm c : MvPolynomial (Fin (N + 1)) k) ≠ 0 := by
    intro h0
    apply hc
    funext i
    simpa [coe_linearForm, Fintype.linearCombination_apply, Pi.single_apply] using
      congrArg (MvPolynomial.eval (Pi.single i 1)) h0
  set H := Stacks.ProjectiveSpace.hyperplane (linearForm c)
  have hH := MMP.ProjectiveSpace.isEffectiveCartierDivisor_hyperplane hp0
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun y => ?_
  obtain ⟨W₀, hW₀, hyW, s, -, hsW⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor H hH (ψ y)
  set W : (AlgebraicGeometry.Proj
    (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).affineOpens := ⟨W₀, hW₀⟩
  have hy : y ∈ ψ ⁻¹ᵁ W.1 := hyW
  have hξ : genericPoint X ∈ ψ ⁻¹ᵁ W.1 :=
    ((genericPoint_spec X).mem_open_set_iff (ψ ⁻¹ᵁ W.1).isOpen).mpr ⟨y, trivial, hy⟩
  suffices hs0 : X.presheaf.germ _ (genericPoint X) hξ (ψ.app W.1 s) ≠ 0 by
    obtain ⟨U, hyU, g, hg, hU⟩ := MMP.exists_localEquation_comap H ψ W hsW hξ hs0 hy
    exact ⟨U.1, U.2, hyU, g, isRegular_iff_mem_nonZeroDivisors.mpr hg, hU⟩
  intro hzero
  have hmem : ψ (genericPoint X) ∈ (Stacks.ProjectiveSpace.hyperplane (linearForm c)).support := by
    by_contra hns
    have hnz : ψ (genericPoint X) ∉ (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).zeroLocus {s} := by
      intro hz
      apply hns
      have : ψ (genericPoint X) ∈ (H.support : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∩ W.1 := by
        rw [Scheme.IdealSheafData.coe_support_inter, hsW, Scheme.zeroLocus_span]
        exact ⟨hz, hξ⟩
      exact this.1
    rw [Scheme.zeroLocus_singleton, Set.notMem_compl_iff, SetLike.mem_coe,
      Scheme.mem_basicOpen _ _ _
        (show ψ (genericPoint X) ∈ (W : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens) from hξ)] at hnz
    apply (hnz.map (ψ.stalkMap (genericPoint X)).hom).ne_zero
    rwa [Scheme.Hom.germ_stalkMap_apply]
  exact hgen ((MMP.ProjectiveSpace.mem_support_hyperplane_iff _ _).mp hmem)

/-- A variety has finite dimension. -/
private theorem topologicalKrullDim_eq_natCast_of_isVariety (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsVariety k (X ↘ Spec (.of k))] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h := Stacks.Chow.topologicalKrullDim_closure_singleton_eq k (X ↘ Spec (.of k))
    (genericPoint X)
  rw [(genericPoint_spec X).def,
    (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq] at h
  exact ⟨_, h⟩

/-- **Every component of a hyperplane section has codimension one** when the hyperplane misses
the image of the generic point of the variety `X`. -/
private theorem topologicalKrullDim_add_one_of_mem_irreducibleComponents {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsVariety k (X ↘ Spec (.of k))] (ψ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    (c : Fin (N + 1) → k) (hc : c ≠ 0)
    (hgen : (linearForm c : MvPolynomial (Fin (N + 1)) k) ∉
      (ψ (genericPoint X)).asHomogeneousIdeal)
    {C : Set (hyperplaneSection ψ c).subscheme}
    (hC : C ∈ irreducibleComponents (hyperplaneSection ψ c).subscheme) :
    topologicalKrullDim C + 1 = topologicalKrullDim X := by
  have hI := isEffectiveCartierDivisor_hyperplaneSection ψ c hc hgen
  obtain ⟨n, hn⟩ := topologicalKrullDim_eq_natCast_of_isVariety (k := k) X
  obtain ⟨ζ, -⟩ := hC.1.1
  have hx : (hyperplaneSection ψ c).subschemeι ζ ∈ (hyperplaneSection ψ c).support := by
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨ζ, rfl⟩
  have hne : (hyperplaneSection ψ c).subschemeι ζ ≠ genericPoint X := fun h =>
    hgen (h ▸ (mem_support_hyperplaneSection_iff ψ c _).mp hx)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => ?_)
    have hpos : 0 < topologicalKrullDim X := by
      refine Order.krullDim_pos_iff.mpr
        ⟨⟨closure {(hyperplaneSection ψ c).subschemeι ζ}, isIrreducible_singleton.closure,
          isClosed_closure⟩, ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩,
          SetLike.coe_ssubset_coe.mp ((Set.subset_univ _).ssubset_of_ne fun h => hne ?_)⟩
      exact (show IsGenericPoint ((hyperplaneSection ψ c).subschemeι ζ) Set.univ from h).eq
        (genericPoint_spec X)
    simp [hn, h0] at hpos
  obtain ⟨m', hm', hd⟩ :=
    MMP.hasDim_of_mem_irreducibleComponents_of_isEffectiveCartierDivisor k hn.symm hI hC
  obtain rfl : m' = m := by exact_mod_cast hm'
  rw [hd, hn]
  norm_cast

end Cartier

/-! ### Nonemptiness of general hyperplane sections -/

section Nonempty

variable {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ}

omit [IsAlgClosed k] in
/-- `ℙᴺ_k` is a variety. -/
private theorem isVariety_projectiveSpace : IsVariety k (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) ↘ Spec (.of k)) := by
  have : IsSeparated (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) ↘ Spec (.of k)) := inferInstance
  exact { toIsIntegral := inferInstance }

omit [IsAlgClosed k] in
/-- A point `(a₀ : ⋯ : a_N)` lies on the hyperplane of `c` iff `∑ᵢ cᵢ aᵢ = 0`. -/
private theorem linearForm_mem_point_iff (a : Fin (N + 1) → k) (ha : a ≠ 0)
    (c : Fin (N + 1) → k) :
    (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈
      (dualPoint a ha).asHomogeneousIdeal ↔
      ∑ i, c i * a i = 0 := by
  rw [mem_dualPoint_iff a ha
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp (linearForm c).2), coe_linearForm,
    Fintype.linearCombination_apply, map_sum]
  simp

omit [IsAlgClosed k] in
/-- The generic point of `ℙᴺ_k` lies on no hyperplane. -/
private theorem linearForm_notMem_genericPoint (c : Fin (N + 1) → k) (hc : c ≠ 0) :
    (linearForm c : MvPolynomial (Fin (N + 1)) k) ∉
      (genericPoint (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))).asHomogeneousIdeal := by
  intro h
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (funext hcon)
  have ha : (Pi.single i 1 : Fin (N + 1) → k) ≠ 0 := by
    simp [funext_iff, Pi.single_apply]
  have hle : (genericPoint (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))).asHomogeneousIdeal ≤
      (dualPoint _ ha).asHomogeneousIdeal :=
    (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mpr
      ((genericPoint_spec (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))).specializes (Set.mem_univ _)).mem_closure
  have := (linearForm_mem_point_iff _ ha c).mp (hle h)
  simp [Pi.single_apply] at this
  exact hi this

omit [IsAlgClosed k] in
/-- A hyperplane of `ℙᴺ_k`, `N ≥ 1`, has a point. -/
private theorem exists_mem_support_hyperplane (c : Fin (N + 1) → k) (hc : c ≠ 0) (hN : 1 ≤ N) :
    ∃ p : AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N),
      (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈ p.asHomogeneousIdeal := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (funext hcon)
  obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), j ≠ i := ⟨if i = 0 then 1 else 0, by
    split_ifs with h
    · rw [h]; exact Fin.ne_of_val_ne (by simp; omega)
    · exact Ne.symm h⟩
  set a : Fin (N + 1) → k := c j • Pi.single i 1 - c i • Pi.single j 1
  have ha : a ≠ 0 := by
    intro h
    have := congrFun h j
    simp [a, Pi.single_apply, hj] at this
    exact hi this
  refine ⟨dualPoint a ha, (linearForm_mem_point_iff a ha c).mpr ?_⟩
  simp [a, Pi.single_apply, mul_sub, Finset.sum_sub_distrib, hj.symm, mul_comm]

omit [IsAlgClosed k] in
/-- `ℙᴺ_k` has dimension `N`. -/
private theorem topologicalKrullDim_projectiveSpace :
    topologicalKrullDim (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) = N :=
  (Stacks.ProjectiveSpace.topologicalKrullDim_proj k (Fin (N + 1))).trans (by simp)

/-- A hyperplane of `ℙᴺ_k`, `N ≥ 1`, has dimension `N - 1`. -/
private theorem topologicalKrullDim_support_hyperplane (c : Fin (N + 1) → k) (hc : c ≠ 0)
    (hN : 1 ≤ N) :
    topologicalKrullDim ((Stacks.ProjectiveSpace.hyperplane (linearForm c)).support :
      Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) = ((N - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  have := isVariety_projectiveSpace (k := k) (N := N)
  have hP := topologicalKrullDim_projectiveSpace (k := k) (N := N)
  set J := hyperplaneSection (𝟙 (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) c
  have hJ : ((Stacks.ProjectiveSpace.hyperplane (linearForm c)).support :
      Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) = J.support := by
    ext p
    rw [SetLike.mem_coe, SetLike.mem_coe, mem_support_hyperplaneSection_iff (𝟙 _) c p,
      MMP.ProjectiveSpace.mem_support_hyperplane_iff]
    rfl
  have hpure : MMP.IsPureDimensional J.subscheme ((N - 1 : ℕ) : ℤ) := by
    intro C hC
    have h := (topologicalKrullDim_add_one_of_mem_irreducibleComponents (𝟙 _) c hc
      (linearForm_notMem_genericPoint c hc) hC).trans hP
    exact ⟨N - 1, rfl, eq_natCast_sub_one_of_add_one_eq h hN⟩
  obtain ⟨p, hp⟩ := exists_mem_support_hyperplane c hc hN
  have hne : Nonempty J.subscheme := by
    have hpJ : p ∈ (J.support : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) := by
      rwa [SetLike.mem_coe, mem_support_hyperplaneSection_iff (𝟙 _) c p]
    rw [← Scheme.IdealSheafData.range_subschemeι] at hpJ
    obtain ⟨y, -⟩ := hpJ
    exact ⟨y⟩
  obtain ⟨n, hn, hdn⟩ := hpure.hasDim_of_nonempty
  have hnN : n = N - 1 := by exact_mod_cast hn
  rw [hJ, ← Scheme.IdealSheafData.range_subschemeι,
    ← J.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    hdn, hnN]

/-- **Stacks 0B2R in `ℙᴺ_k`.** Nonempty closed subsets of dimensions `r` and `s` with
`N ≤ r + s` meet in dimension at least `r + s - N`. -/
private theorem le_topologicalKrullDim_inter (W H : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) (hWc : IsClosed W)
    (hHc : IsClosed H) (hWne : W.Nonempty) (hHne : H.Nonempty) {r s : ℕ}
    (hWd : topologicalKrullDim W = r) (hHd : topologicalKrullDim H = s) (hrs : N ≤ r + s) :
    ((r + s - N : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (W ∩ H : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) := by
  set e :=
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k N).iso.hom.homeomorph.symm
  have h := AlgebraicGeometry.le_topologicalKrullDim_inter_projectiveSpaceOverRing k N r s
    (e '' W) (e '' H) (e.isClosed_image.mpr hWc) (e.isClosed_image.mpr hHc) (hWne.image e)
    (hHne.image e) (by rwa [topologicalKrullDim_image_homeomorph])
    (by rwa [topologicalKrullDim_image_homeomorph]) hrs
  rwa [← Set.image_inter e.injective, topologicalKrullDim_image_homeomorph] at h

omit [Field k] [IsAlgClosed k] in
/-- Finitely many points of a closed subset `D` of a Noetherian sober space generalize to every
point of `D` inside `D`: the generic points of the irreducible components of `D`. -/
private theorem exists_finite_forall_specializes {Y : Type*} [TopologicalSpace Y]
    [NoetherianSpace Y] [QuasiSober Y] [T0Space Y] {D : Set Y} (hD : IsClosed D) :
    ∃ G : Set Y, G.Finite ∧ ∀ x ∈ D, ∃ η ∈ G, η ∈ D ∧ η ⤳ x := by
  refine ⟨⋃ C ∈ irreducibleComponents D, {e | IsGenericPoint e (closure (((↑) : D → Y) '' C))},
    NoetherianSpace.finite_irreducibleComponents.biUnion fun C _ =>
      Set.Subsingleton.finite fun a ha b hb => IsGenericPoint.eq ha hb, fun x hx => ?_⟩
  have hC := irreducibleComponent_mem_irreducibleComponents (⟨x, hx⟩ : D)
  have hirr : IsIrreducible (closure (((↑) : D → Y) '' irreducibleComponent (⟨x, hx⟩ : D))) :=
    (hC.1.image _ continuous_subtype_val.continuousOn).closure
  obtain ⟨η, hη⟩ := QuasiSober.sober hirr isClosed_closure
  refine ⟨η, Set.mem_biUnion hC hη, ?_, ?_⟩
  · refine closure_minimal ?_ hD hη.mem
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  · exact hη.specializes (subset_closure ⟨⟨x, hx⟩, mem_irreducibleComponent, rfl⟩)

/-- **A general hyperplane meets the image of a variety whose image is not a point.** -/
private theorem exists_dense_open_support_nonempty {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsVariety k (X ↘ Spec (.of k))] (ψ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)) [ψ.IsOver (Spec (.of k))]
    (hψ : ¬ (Set.range ψ.base).Subsingleton) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        ((hyperplaneSection ψ c).support : Set X).Nonempty := by
  classical
  have := isNoetherian_projectiveSpace (k := k) (N := N)
  have := locallyOfFiniteType_of_comp_eq ψ _ (comp_over ψ (Spec (.of k)))
  have hP := topologicalKrullDim_projectiveSpace (k := k) (N := N)
  obtain ⟨O, hO, hηO, hsub⟩ := exists_isOpen_closure_range_inter_subset ψ
  set W := closure (Set.range ψ.base) with hW
  have hWc : IsClosed W := isClosed_closure
  have hWirr : IsIrreducible W := by
    rw [hW, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ X).image _ ψ.continuous.continuousOn).closure
  have hWfin : topologicalKrullDim W ≠ ⊤ :=
    ne_top_of_le_ne_top (by
        rw [hP]
        intro h
        have : ((N : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := h
        exact ENat.coe_ne_top N (WithBot.coe_injective this))
      ((topologicalKrullDim_le_of_subset (Set.subset_univ W)).trans
        (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq.le)
  -- `W` has dimension `r ≥ 1`
  have hWdim : ∃ r : ℕ, 1 ≤ r ∧ topologicalKrullDim W = r := by
    obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ : ∃ y₁ ∈ W, ∃ y₂ ∈ W, y₁ ≠ y₂ := by
      by_contra hcon
      push Not at hcon
      exact hψ fun a ha b hb => hcon a (subset_closure ha) b (subset_closure hb)
    obtain ⟨w, hw⟩ := QuasiSober.sober hWirr hWc
    obtain ⟨y, hyW, hyw⟩ : ∃ y ∈ W, y ≠ w := by
      by_cases h : y₁ = w
      · exact ⟨y₂, hy₂, fun h' => hy (h.trans h'.symm)⟩
      · exact ⟨y₁, hy₁, h⟩
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hWirr isClosed_closure
      (closure_minimal (Set.singleton_subset_iff.mpr hyW) hWc)
      (fun h => hyw ((show IsGenericPoint y W from h).eq hw)) hWfin
    obtain ⟨r, hr⟩ := exists_natCast_eq_topologicalKrullDim ⟨y, hyW⟩ hWfin
    obtain ⟨d, hd⟩ := exists_natCast_eq_topologicalKrullDim (S := closure {y})
      ⟨y, subset_closure rfl⟩ (ne_top_of_lt hlt)
    rw [hr, hd] at hlt
    exact ⟨r, by exact_mod_cast (Nat.zero_lt_of_lt (by exact_mod_cast hlt : d < r)), hr⟩
  obtain ⟨r, hr1, hWr⟩ := hWdim
  have hrN : r ≤ N := by
    have := (topologicalKrullDim_le_of_subset (Set.subset_univ W)).trans
      (Homeomorph.Set.univ (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))).isHomeomorph.topologicalKrullDim_eq.le
    rw [hWr, hP] at this
    exact_mod_cast this
  have hN : 1 ≤ N := hr1.trans hrN
  -- the complement `D` of the open part of the image
  set D := W ∩ Oᶜ with hD
  have hDc : IsClosed D := hWc.inter hO.isClosed_compl
  have hηD : ψ (genericPoint X) ∉ D := fun h => h.2 hηO
  obtain ⟨G, hGfin, hG⟩ := exists_finite_forall_specializes hDc
  obtain ⟨U, hU, hUG⟩ := exists_dense_open_forall_notMem G hGfin
  refine ⟨U, hU, fun c hc hm => ?_⟩
  set H := ((Stacks.ProjectiveSpace.hyperplane (linearForm c)).support : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)))
    with hH
  have hHc : IsClosed H := (Stacks.ProjectiveSpace.hyperplane (linearForm c)).support.isClosed
  have hHd := topologicalKrullDim_support_hyperplane c hc hN
  have hmemH : ∀ p, p ∈ H ↔ (linearForm c : MvPolynomial (Fin (N + 1)) k) ∈ p.asHomogeneousIdeal :=
    fun p => MMP.ProjectiveSpace.mem_support_hyperplane_iff _ _
  have hHne : H.Nonempty := by
    obtain ⟨p, hp⟩ := exists_mem_support_hyperplane c hc hN
    exact ⟨p, (hmemH p).mpr hp⟩
  have h1 := le_topologicalKrullDim_inter W H hWc hHc ⟨_, subset_closure ⟨genericPoint X, rfl⟩⟩
    hHne hWr hHd (by omega)
  have hr' : r + (N - 1) - N = r - 1 := by omega
  rw [hr'] at h1
  have hnot : ¬ (W ∩ H ⊆ D) := by
    intro hWH
    have hWHD : W ∩ H ⊆ D ∩ H := fun y hy => ⟨hWH hy, hy.2⟩
    have hWHne : (W ∩ H).Nonempty := nonempty_of_natCast_le_topologicalKrullDim h1
    have hDH : (D ∩ H).Nonempty := hWHne.mono hWHD
    have hDlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hWirr hDc
      Set.inter_subset_left (fun h => hηD (h ▸ subset_closure ⟨genericPoint X, rfl⟩)) hWfin
    rw [hWr] at hDlt
    obtain ⟨d, hd⟩ := exists_natCast_eq_topologicalKrullDim (hDH.mono Set.inter_subset_left)
      (ne_top_of_lt hDlt)
    rw [hd] at hDlt
    have hdr : d < r := by exact_mod_cast hDlt
    obtain ⟨hd1, hDH'⟩ := MMP.topologicalKrullDim_inter_le_pred_of_forall_exists_specializes hDc
      hHc hd.le (fun x hx => by
        obtain ⟨η, hηG, hηD, hηx⟩ := hG x hx.1
        exact ⟨η, hηD, hηx, fun h => hUG c hc hm η hηG ((hmemH η).mp h)⟩) hDH
    have := h1.trans ((topologicalKrullDim_le_of_subset hWHD).trans hDH')
    have : r - 1 ≤ d - 1 := by exact_mod_cast this
    omega
  obtain ⟨y, ⟨hyW, hyH⟩, hyD⟩ := Set.not_subset.mp hnot
  have hyO : y ∈ O := by
    by_contra h
    exact hyD ⟨hyW, h⟩
  obtain ⟨x, rfl⟩ := hsub ⟨hyW, hyO⟩
  exact ⟨x, (mem_support_hyperplaneSection_iff ψ c x).mpr ((hmemH _).mp hyH)⟩

end Nonempty

/-! ### General hyperplane sections of a variety -/

section Variety

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {N : ℕ}

/-- **General hyperplane sections of a variety.** For a `k`-morphism `ψ : X ⟶ ℙᴺ_k` from a variety
and a general hyperplane `H`: `H` misses the image of the generic point of `X`; `ψ⁻¹(H)` is
non-empty if the image of `ψ` is not a point; `ψ⁻¹(H)` is reduced, all its components have
dimension `dim X - 1`, it is integral if the image of `ψ` has dimension at least two, and normal
if `X` is. -/
private theorem exists_dense_open_hyperplaneSection_variety {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsVariety k (X ↘ Spec (.of k))] (ψ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    [ψ.IsOver (Spec (.of k))] :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        (linearForm c : MvPolynomial (Fin (N + 1)) k) ∉
          (ψ (genericPoint X)).asHomogeneousIdeal ∧
        (¬ (Set.range ψ.base).Subsingleton → ((hyperplaneSection ψ c).support : Set X).Nonempty) ∧
        IsReduced (hyperplaneSection ψ c).subscheme ∧
        (∀ C ∈ irreducibleComponents (hyperplaneSection ψ c).subscheme,
          topologicalKrullDim C + 1 = topologicalKrullDim X) ∧
        (2 ≤ topologicalKrullDim (closure (Set.range ψ.base)) →
          IsIntegral (hyperplaneSection ψ c).subscheme) ∧
        (IsNormal X → IsNormal (hyperplaneSection ψ c).subscheme) := by
  classical
  have : Infinite k := IsAlgClosed.instInfinite
  obtain ⟨U₁, hU₁, h₁⟩ := exists_dense_open_forall_notMem {ψ (genericPoint X)}
    (Set.finite_singleton _)
  obtain ⟨U₂, hU₂, h₂⟩ : ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧ ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0),
        dualPoint c hc ∈ U → ¬ (Set.range ψ.base).Subsingleton →
          ((hyperplaneSection ψ c).support : Set X).Nonempty := by
    by_cases hψ : (Set.range ψ.base).Subsingleton
    · exact ⟨⊤, by simpa using dense_univ, fun _ _ _ h => absurd hψ h⟩
    · obtain ⟨U, hU, h⟩ := exists_dense_open_support_nonempty ψ hψ
      exact ⟨U, hU, fun c hc hm _ => h c hc hm⟩
  obtain ⟨U₃, hU₃, h₃⟩ := (exists_dense_open_isReduced_zeroScheme (k := k) (X := X)
    (pullSystem ψ) (iSup_nonvanishingOpen_pullSystem ψ)).2
  obtain ⟨U₄, hU₄, h₄⟩ : ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧ ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0),
        dualPoint c hc ∈ U → 2 ≤ topologicalKrullDim (closure (Set.range ψ.base)) →
          IsIntegral (hyperplaneSection ψ c).subscheme := by
    by_cases h2 : 2 ≤ topologicalKrullDim (closure (Set.range ψ.base))
    · obtain ⟨-, U, hU, h⟩ := exists_dense_open_geometricallyIrreducible_zeroScheme
        (pullSystem ψ) (iSup_nonvanishingOpen_pullSystem ψ)
        (h2.trans (le_topologicalKrullDim_range_morphismOfGeneratingSections ψ))
      exact ⟨U, hU, fun c hc hm _ => zeroScheme_pullSystem ψ c ▸ (h c hc hm).2.2⟩
    · exact ⟨⊤, by simpa using dense_univ, fun _ _ _ h => absurd h h2⟩
  obtain ⟨U₅, hU₅, h₅⟩ : ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧ ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0),
        dualPoint c hc ∈ U → IsNormal X → IsNormal (hyperplaneSection ψ c).subscheme := by
    by_cases hX : IsNormal X
    · obtain ⟨U, hU, h⟩ := (exists_dense_open_isNormal_zeroScheme (k := k) (X := X)
        (pullSystem ψ) (iSup_nonvanishingOpen_pullSystem ψ)).2
      exact ⟨U, hU, fun c hc hm _ => (zeroScheme_pullSystem ψ c :
        Stacks.Divisors.zeroScheme _ _ _ = _) ▸ h c hc hm⟩
    · exact ⟨⊤, by simpa using dense_univ, fun _ _ _ h => absurd h hX⟩
  refine ⟨U₁ ⊓ U₂ ⊓ U₃ ⊓ U₄ ⊓ U₅,
    dense_coe_inf (dense_coe_inf (dense_coe_inf (dense_coe_inf hU₁ hU₂) hU₃) hU₄) hU₅,
    fun c hc hm => ?_⟩
  obtain ⟨⟨⟨⟨m₁, m₂⟩, m₃⟩, m₄⟩, m₅⟩ := hm
  have hgen : (linearForm c : MvPolynomial (Fin (N + 1)) k) ∉
      (ψ (genericPoint X)).asHomogeneousIdeal := h₁ c hc m₁ _ rfl
  refine ⟨hgen, h₂ c hc m₂, ?_, fun C hC =>
    topologicalKrullDim_add_one_of_mem_irreducibleComponents ψ c hc hgen hC, h₄ c hc m₄,
    h₅ c hc m₅⟩
  have := h₃ c hc m₃
  rwa [zeroScheme_pullSystem] at this

end Variety

/-! ### General hyperplane sections of a closed subvariety -/

section Subvariety

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {N : ℕ}

/-- **An integral closed subscheme of a variety is a variety.** -/
private theorem isVariety_subschemeι_comp {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [IsVariety k (Z ↘ Spec (.of k))] (I : Z.IdealSheafData) [IsIntegral I.subscheme] :
    IsVariety k (I.subschemeι ≫ Z ↘ Spec (.of k)) := by
  have : IsSeparated I.subschemeι := inferInstance
  have : IsSeparated (Z ↘ Spec (.of k)) := inferInstance
  have : IsSeparated (I.subschemeι ≫ Z ↘ Spec (.of k)) := inferInstance
  have : LocallyOfFiniteType (I.subschemeι ≫ Z ↘ Spec (.of k)) := inferInstance
  have : QuasiCompact (I.subschemeι ≫ Z ↘ Spec (.of k)) := inferInstance
  exact { toIsIntegral := inferInstance }

/-- **A closed irreducible subset of a variety, with its reduced structure, is a variety.** -/
private theorem isVariety_vanishingIdeal {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [IsVariety k (Z ↘ Spec (.of k))] (F : Closeds Z) (hF : IsIrreducible (F : Set Z)) :
    IsVariety k ((Scheme.IdealSheafData.vanishingIdeal F).subschemeι ≫ Z ↘ Spec (.of k)) := by
  set I := Scheme.IdealSheafData.vanishingIdeal F
  have : IsReduced I.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal F
  have hrange : Set.range I.subschemeι = (F : Set Z) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have : IrreducibleSpace I.subscheme := by
    have e : I.subscheme ≃ₜ (F : Set Z) :=
      I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
    have : IrreducibleSpace (F : Set Z) := Subtype.irreducibleSpace hF
    have h := (IrreducibleSpace.isIrreducible_univ (F : Set Z)).image e.symm
      e.symm.continuous.continuousOn
    rw [Set.image_univ, e.symm.surjective.range_eq] at h
    exact (irreducibleSpace_def _).mpr h
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  exact isVariety_subschemeι_comp I

/-- **General hyperplane sections of a closed subvariety `F` of `Z`**, read as the
scheme-theoretic intersections `F ∩ φ⁻¹(H)`. -/
private theorem exists_dense_open_hyperplaneSection_closeds {Z : Scheme.{u}}
    [Z.Over (Spec (.of k))] [IsVariety k (Z ↘ Spec (.of k))] (φ : Z ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    [φ.IsOver (Spec (.of k))] (F : Closeds Z) (hF : IsIrreducible (F : Set Z)) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        (∀ η : Z, IsGenericPoint η (F : Set Z) → η ∉ (hyperplaneSection φ c).support) ∧
        ((φ.base '' F).Subsingleton → (F : Set Z) ∩ (hyperplaneSection φ c).support = ∅) ∧
        (¬ (φ.base '' F).Subsingleton →
          ((F : Set Z) ∩ (hyperplaneSection φ c).support).Nonempty ∧
          IsReduced (Scheme.IdealSheafData.vanishingIdeal F ⊔ hyperplaneSection φ c).subscheme ∧
          (∀ C ∈ irreducibleComponents (Scheme.IdealSheafData.vanishingIdeal F ⊔
              hyperplaneSection φ c).subscheme,
            topologicalKrullDim C + 1 = topologicalKrullDim F) ∧
          (2 ≤ topologicalKrullDim (closure (φ.base '' F)) →
            IsIrreducible ((F : Set Z) ∩ (hyperplaneSection φ c).support))) := by
  classical
  set I := Scheme.IdealSheafData.vanishingIdeal F with hIdef
  letI : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ Z ↘ Spec (.of k)⟩
  have : IsVariety k (I.subscheme ↘ Spec (.of k)) := isVariety_vanishingIdeal F hF
  let ψ : I.subscheme ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N) := I.subschemeι ≫ φ
  have : ψ.IsOver (Spec (.of k)) := ⟨by
    change (I.subschemeι ≫ φ) ≫ _ = I.subschemeι ≫ Z ↘ Spec (.of k)
    rw [Category.assoc, comp_over φ (Spec (.of k))]⟩
  obtain ⟨U, hU, hgood⟩ := exists_dense_open_hyperplaneSection_variety ψ
  refine ⟨U, hU, fun c hc hm => ?_⟩
  obtain ⟨hgen, hne, hred, hdim, hint, -⟩ := hgood c hc hm
  have hrange : Set.range I.subschemeι = (F : Set Z) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hrangeψ : Set.range ψ.base = φ.base '' F := by
    rw [← hrange, ← Set.range_comp]
    rfl
  have hcomp : hyperplaneSection ψ c = (hyperplaneSection φ c).comap I.subschemeι := by
    simp only [ψ, hyperplaneSection, Scheme.IdealSheafData.comap_comp]
  have hsupp : (F : Set Z) ∩ (hyperplaneSection φ c).support =
      I.subschemeι '' ((hyperplaneSection ψ c).support) := by
    ext z
    constructor
    · rintro ⟨hzF, hz⟩
      obtain ⟨y, rfl⟩ : z ∈ Set.range I.subschemeι := hrange ▸ hzF
      exact ⟨y, (mem_support_hyperplaneSection_iff ψ c y).mpr
        ((mem_support_hyperplaneSection_iff φ c _).mp hz), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hrange ▸ ⟨y, rfl⟩, (mem_support_hyperplaneSection_iff φ c _).mpr
        ((mem_support_hyperplaneSection_iff ψ c y).mp hy)⟩
  have hη : IsGenericPoint (I.subschemeι (genericPoint I.subscheme)) (F : Set Z) := by
    have h := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
    rwa [Set.image_univ, hrange, (F.isClosed).closure_eq] at h
  have hFmem : I.subschemeι (genericPoint I.subscheme) ∈ (F : Set Z) := hη.mem
  refine ⟨fun η hη' h => hgen ((mem_support_hyperplaneSection_iff φ c _).mp
    (hη'.eq hη ▸ h)), fun hsub => ?_, fun hnsub => ?_⟩
  · refine Set.eq_empty_iff_forall_notMem.mpr fun x ⟨hxF, hx⟩ => hgen ?_
    have hφx : φ x = φ (I.subschemeι (genericPoint I.subscheme)) :=
      hsub ⟨x, hxF, rfl⟩ ⟨_, hFmem, rfl⟩
    have := (mem_support_hyperplaneSection_iff φ c x).mp hx
    rwa [hφx] at this
  have hnsub' : ¬ (Set.range ψ.base).Subsingleton := hrangeψ ▸ hnsub
  rw [hcomp] at hred hdim hint
  let e := Scheme.IdealSheafData.supComapSubschemeIso I (hyperplaneSection φ c)
  have heF : topologicalKrullDim I.subscheme = topologicalKrullDim F :=
    (I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)).isHomeomorph.topologicalKrullDim_eq
  refine ⟨?_, isReduced_of_isOpenImmersion e.hom, fun C hC => ?_, fun h2 => ?_⟩
  · rw [hsupp]
    exact (hne hnsub').image _
  · rw [← topologicalKrullDim_image_homeomorph e.hom.homeomorph C, ← heF]
    exact hdim _ (image_mem_irreducibleComponents e.hom.homeomorph hC)
  · have : IsIntegral ((hyperplaneSection φ c).comap I.subschemeι).subscheme :=
      hint (hrangeψ ▸ h2)
    rw [hsupp, hcomp, ← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ, ← Set.image_comp]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (Scheme.Hom.continuous _ |>.comp (Scheme.Hom.continuous _)).continuousOn

end Subvariety

/-! ### Restriction of divisors -/

section Restriction

open MMP.Mori MMP.Intersection

section Local

variable {Z : Scheme.{u}}

/-- The ideal `I_x ⊆ 𝒪_{Z,x}` of the stalk of an ideal sheaf, in the two spellings of the
library. -/
private theorem stalk_eq_stalkIdeal (I : Z.IdealSheafData) (x : Z) :
    IdealSheafData.stalk I x = I.stalkIdeal x := by
  unfold IdealSheafData.stalk Scheme.IdealSheafData.stalkIdeal
  exact iSup_subtype'

/-- The stalk of `I ⊔ J` is the sum of the stalks. -/
private theorem stalkIdeal_sup (I J : Z.IdealSheafData) (x : Z) :
    (I ⊔ J).stalkIdeal x = I.stalkIdeal x ⊔ J.stalkIdeal x := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Z) (x := x) (U := ⊤) (by simp)
  simp only [← stalk_eq_stalkIdeal]
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ J x ⟨U, hU⟩ hxU, Scheme.IdealSheafData.ideal_sup]
  exact Ideal.map_sup _ _ _

/-- The height of the prime of a generization `y ⤳ x` in `𝒪_{Z,x}` is the codimension of `y`. -/
private theorem height_primeOfSpecializes [IsLocallyNoetherian Z] {y x : Z} (h : y ⤳ x) :
    (primeOfSpecializes h).height = Order.coheight y := by
  let := (Z.presheaf.stalkSpecializes h).hom.toAlgebra
  have := isLocalization_stalkSpecializes h
  have e := IsLocalization.AtPrime.ringKrullDim_eq_height (primeOfSpecializes h)
    (Z.presheaf.stalk y)
  rw [ringKrullDim_stalk_eq_coheight] at e
  exact_mod_cast e.symm

/-- **A local equation at a point of the support of a locally principal ideal**: the stalk is
generated by a nonzero element of the maximal ideal. -/
private theorem exists_stalkIdeal_eq_span [IsIntegral Z] {I : Z.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) {y : Z}
    (hy : y ∈ I.support) :
    ∃ h : Z.presheaf.stalk y, h ≠ 0 ∧ h ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk y) ∧
      I.stalkIdeal y = Ideal.span {h} := by
  obtain ⟨U, hU, hyU, f, hf, hIU⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI y
  have hspan : I.stalkIdeal y = Ideal.span {Z.presheaf.germ U y hyU f} := by
    rw [← stalk_eq_stalkIdeal, IdealSheafData.stalk_eq_map_germ I y ⟨U, hU⟩ hyU, hIU,
      Ideal.map_span, Set.image_singleton]
  refine ⟨_, ?_, ?_, hspan⟩
  · have : Nonempty U := ⟨⟨y, hyU⟩⟩
    intro h0
    apply nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp hf)
    exact germ_injective_of_isIntegral Z y hyU (h0.trans (map_zero _).symm)
  · have h := (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support I y).mpr hy
    rw [stalk_eq_stalkIdeal, hspan] at h
    exact h (Ideal.mem_span_singleton_self _)

/-- **The codimension of a point of a Cartier divisor drops by one in the divisor.** -/
private theorem coheight_subschemeι [IsIntegral Z] [IsLocallyNoetherian Z] {I : Z.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (v : I.subscheme) : Order.coheight (I.subschemeι v) = Order.coheight v + 1 := by
  have hyI : I.subschemeι v ∈ I.support := by
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨v, rfl⟩
  obtain ⟨h, h0, hm, hspan⟩ := exists_stalkIdeal_eq_span hI hyI
  have hnzd : h ∈ nonZeroDivisors (Z.presheaf.stalk (I.subschemeι v)) :=
    mem_nonZeroDivisors_of_ne_zero h0
  have e : (Z.presheaf.stalk (I.subschemeι v) ⧸ Ideal.span {h}) ≃+*
      I.subscheme.presheaf.stalk v :=
    (Ideal.quotEquivOfEq (by rw [Scheme.IdealSheafData.ker_stalkMap_subschemeι, hspan])).trans
      (RingHom.quotientKerEquivOfSurjective
        (SurjectiveOnStalks.stalkMap_surjective I.subschemeι v))
  have hd := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    hnzd hm
  rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_stalk_eq_coheight,
    ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd.symm

/-- The generic point of an irreducible component has codimension zero. -/
private theorem coheight_componentGenericPoint {X : Scheme.{u}} (W : irreducibleComponents X) :
    Order.coheight (componentGenericPoint X W) = 0 := by
  refine Order.coheight_eq_zero.2 fun η hη => ?_
  rw [Scheme.le_iff_specializes] at hη ⊢
  have hW := isGenericPoint_componentGenericPoint X W
  have hsub : W.1 ⊆ closure {η} := by
    rw [← hW.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hη))
      isClosed_closure
  have heq : closure {η} ⊆ W.1 := W.2.2 isIrreducible_singleton.closure hsub
  rw [specializes_iff_mem_closure, hW.def]
  exact heq (subset_closure rfl)

/-- **A point of codimension zero of the divisor `V(I)` lies on no prescribed prime divisor**
whose generic point is off `V(I)`: it would be that generic point. -/
private theorem notMem_support_of_coheight_eq_zero [IsIntegral Z] [IsLocallyNoetherian Z]
    {I : Z.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (E : MMP.Mori.PrimeDivisor Z) (hE : E.genericPoint ∉ I.support) {s : I.subscheme}
    (hs : Order.coheight s = 0) : I.subschemeι s ∉ E.support := by
  intro hmem
  have h1 : Order.coheight (I.subschemeι s) = 1 := by
    rw [coheight_subschemeι hI, hs, zero_add]
  have hsp : E.genericPoint ⤳ I.subschemeι s := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have heq : I.subschemeι s = E.genericPoint := by
    by_contra hne
    have hlt : I.subschemeι s < E.genericPoint :=
      lt_of_le_not_ge (Scheme.le_iff_specializes.2 hsp)
        (fun h => hne ((Scheme.le_iff_specializes.1 h).antisymm hsp).eq)
    have := Order.coheight_add_one_le hlt
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, h1] at this
    exact absurd this (by decide)
  apply hE
  rw [← heq, ← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨s, rfl⟩

/-- Every point of an irreducible scheme lies on its only irreducible component. -/
private theorem mem_irreducibleComponents_of_irreducibleSpace [IrreducibleSpace Z]
    (W : irreducibleComponents Z) (y : Z) : y ∈ W.1 := by
  obtain ⟨W, hW⟩ := W
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hW
  subst hW
  trivial

/-- The image of a nonzero element of a local ring of an integral scheme in a factor of `K(Z)` is
nonzero. -/
private theorem stalkToRationalFunctions_ne_zero [IsIntegral Z] {y : Z} {t : Z.presheaf.stalk y}
    (ht : t ≠ 0) (W : irreducibleComponents Z) :
    (stalkToRationalFunctions Z (mem_irreducibleComponents_of_irreducibleSpace W y)).hom t ≠ 0 :=
  stalkSpecializes_ne_zero _ ht

/-- The unit of `K(Z)` of a nonzero element of a local ring of the integral scheme `Z`. -/
private noncomputable def stalkUnit [IsIntegral Z] {y : Z} (t : Z.presheaf.stalk y)
    (ht : t ≠ 0) : (RationalFunctions Z)ˣ :=
  (RationalFunctions.unitsEquiv Z).symm fun W =>
    Units.mkOfMulEqOne _ _ (Classical.choose_spec
      ((RationalFunctions.isField_stalk Z W).mul_inv_cancel
        (stalkToRationalFunctions_ne_zero ht W)))

private theorem stalkUnit_apply [IsIntegral Z] {y : Z} (t : Z.presheaf.stalk y) (ht : t ≠ 0)
    (W : irreducibleComponents Z) :
    (stalkUnit t ht : RationalFunctions Z) W =
      (stalkToRationalFunctions Z (mem_irreducibleComponents_of_irreducibleSpace W y)).hom t :=
  rfl

variable [IsLocallyNoetherian Z] [IsNormal Z]

/-- `v_G(∏ fᵢ) = ∑ v_G(fᵢ)`. -/
private theorem ord_prod (G : MMP.Mori.PrimeDivisor Z) {α : Type*} (s : Finset α)
    (f : α → (RationalFunctions Z)ˣ) : G.ord (∏ i ∈ s, f i) = ∑ i ∈ s, G.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PrimeDivisor.ord_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, PrimeDivisor.ord_mul, ih, Finset.sum_insert ha]

/-- The order of a unit of the function field of a component is additive on finite products. -/
private theorem ordUnit_prod {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (P : MMP.Mori.PrimeDivisor X) {α : Type*} (s : Finset α)
    (f : α → (X.presheaf.stalk (componentGenericPoint X P.component))ˣ) :
    P.ordUnit (∏ i ∈ s, f i) = ∑ i ∈ s, P.ordUnit (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, PrimeDivisor.ordUnit_mul, ih, Finset.sum_insert ha]

variable [IsIntegral Z]

/-- If `t ∈ 𝒪_{Z,y}` generates the prime of a prime divisor `G` through `y`, then `v_G(t) = 1`. -/
private theorem ord_stalkUnit_eq_one {y : Z} {t : Z.presheaf.stalk y} (ht : t ≠ 0)
    (G : MMP.Mori.PrimeDivisor Z) (hsp : G.genericPoint ⤳ y)
    (hq : Ideal.span {t} = primeOfSpecializes hsp) : G.ord (stalkUnit t ht) = 1 := by
  have := G.isDiscreteValuationRing_localRing
  let := (Z.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have := isLocalization_stalkSpecializes hsp
  have hmax : IsLocalRing.maximalIdeal G.localRing =
      Ideal.span {(Z.presheaf.stalkSpecializes hsp).hom t} := by
    have h := IsLocalization.AtPrime.map_eq_maximalIdeal (primeOfSpecializes hsp) G.localRing
    rw [← hq, Ideal.map_span, Set.image_singleton] at h
    exact h.symm
  have hne : (Z.presheaf.stalkSpecializes hsp).hom t ≠ 0 := stalkSpecializes_ne_zero hsp ht
  refine G.ord_eq_one_of_irreducible
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hmax) ?_
  rw [G.toComponent_stalkSpecializes hsp
    (mem_irreducibleComponents_of_irreducibleSpace G.component y), stalkUnit_apply]

/-- If `t ∈ 𝒪_{Z,y}` lies outside the prime of a prime divisor `G` through `y`, then
`v_G(t) = 0`. -/
private theorem ord_stalkUnit_eq_zero {y : Z} {t : Z.presheaf.stalk y} (ht : t ≠ 0)
    (G : MMP.Mori.PrimeDivisor Z) (hsp : G.genericPoint ⤳ y)
    (htq : t ∉ primeOfSpecializes hsp) : G.ord (stalkUnit t ht) = 0 := by
  have hu : IsUnit ((Z.presheaf.stalkSpecializes hsp).hom t) := by
    by_contra h
    exact htq ((IsLocalRing.mem_maximalIdeal _).mpr h)
  refine G.ord_eq_zero_of_isUnit hu ?_
  rw [G.toComponent_stalkSpecializes hsp
    (mem_irreducibleComponents_of_irreducibleSpace G.component y), stalkUnit_apply]

/-- **The ideal of a transversal prime divisor at a point of codimension one of a Cartier
divisor.** Let `V = V(I)` be normal, `P` a prime divisor of `V` with generic point mapping to
`y ∈ Z`, and `E` a prime divisor of `Z` through `y` whose generic point is off `V`, with
`E ∩ V` reduced. As `𝒪_{V,P} = 𝒪_{Z,y}/(h)` is a discrete valuation ring and `𝒪_{E ∩ V, y}` is
reduced of dimension zero, `𝔪_y = 𝔭_E + (h)`; a lift `t ∈ 𝔭_E` of a uniformizer of `𝒪_{V,P}`
then gives `𝔪_y = (t, h)`, so `𝒪_{Z,y}/(t)` is regular of dimension one and `𝔭_E = (t)`. -/
private theorem exists_span_eq_primeOfSpecializes {I : Z.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    [IsLocallyNoetherian I.subscheme] [IsNormal I.subscheme]
    (P : MMP.Mori.PrimeDivisor I.subscheme) (E : MMP.Mori.PrimeDivisor Z)
    (hsp : E.genericPoint ⤳ I.subschemeι P.genericPoint) (hE : E.genericPoint ∉ I.support)
    (hred : IsReduced (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure {E.genericPoint}) ⊔ I).subscheme) :
    ∃ t : Z.presheaf.stalk (I.subschemeι P.genericPoint),
      Irreducible ((I.subschemeι.stalkMap P.genericPoint).hom t) ∧
      Ideal.span {t} = primeOfSpecializes hsp := by
  classical
  set v := P.genericPoint
  set y := I.subschemeι v with hy
  set R := Z.presheaf.stalk y
  set π := (I.subschemeι.stalkMap v).hom with hπdef
  set q := primeOfSpecializes hsp with hqdef
  have hyI : y ∈ I.support := by
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨v, rfl⟩
  obtain ⟨h, h0, hm, hspan⟩ := exists_stalkIdeal_eq_span hI hyI
  have hπ : Function.Surjective π := SurjectiveOnStalks.stalkMap_surjective _ v
  have hker : RingHom.ker π = Ideal.span {h} := by
    rw [hπdef, Scheme.IdealSheafData.ker_stalkMap_subschemeι, hspan]
  have hπh : π h = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self h
  have hdimR : ringKrullDim R = 2 := by
    rw [ringKrullDim_stalk_eq_coheight, hy, coheight_subschemeι hI,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    rfl
  have hq1 : q.height = 1 := by
    rw [height_primeOfSpecializes, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  have hm2 : (IsLocalRing.maximalIdeal R).height = 2 := by
    have : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
      rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdimR]
      rfl
    exact WithBot.coe_injective this
  have hhq : h ∉ q := by
    intro hhq
    apply hE
    rwa [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes I hsp, stalk_eq_stalkIdeal,
      hspan, Ideal.span_le, Set.singleton_subset_iff]
  set K := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {E.genericPoint}) ⊔ I with hK
  have hKy : K.stalkIdeal y = q ⊔ Ideal.span {h} := by
    rw [stalkIdeal_sup, hspan]
    congr 1
    have h1 := Stacks.Chow.stalkIdeal_vanishingIdeal_closure_fromSpecStalk y ⟨q, inferInstance⟩
    rwa [fromSpecStalk_primeOfSpecializes] at h1
  have hyK : y ∈ K.support := by
    rw [hK, Scheme.IdealSheafData.support_sup]
    refine ⟨?_, hyI⟩
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
    exact specializes_iff_mem_closure.mp hsp
  obtain ⟨w, hw⟩ : y ∈ Set.range K.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have hrad : (q ⊔ Ideal.span {h}).IsRadical := by
    have hr' : ∀ z : K.subscheme, (K.stalkIdeal (K.subschemeι z)).IsRadical := by
      intro z
      have e : (Z.presheaf.stalk (K.subschemeι z) ⧸ K.stalkIdeal (K.subschemeι z)) ≃+*
          K.subscheme.presheaf.stalk z :=
        (Ideal.quotEquivOfEq (Scheme.IdealSheafData.ker_stalkMap_subschemeι K z).symm).trans
          (RingHom.quotientKerEquivOfSurjective
            (SurjectiveOnStalks.stalkMap_surjective K.subschemeι z))
      have : _root_.IsReduced
          (Z.presheaf.stalk (K.subschemeι z) ⧸ K.stalkIdeal (K.subschemeι z)) :=
        isReduced_of_injective e.toRingHom e.injective
      exact (Ideal.isRadical_iff_quotient_reduced _).mpr this
    have hr : (K.stalkIdeal y).IsRadical := hw ▸ hr' w
    rwa [hKy] at hr
  have hle_m : q ⊔ Ideal.span {h} ≤ IsLocalRing.maximalIdeal R :=
    sup_le (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
      (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  have hmax : ∀ Q : Ideal R, Q.IsPrime → q ⊔ Ideal.span {h} ≤ Q →
      Q = IsLocalRing.maximalIdeal R := by
    intro Q hQ hle
    by_contra hne
    have hqQ : q < Q := lt_of_le_of_ne (le_sup_left.trans hle) fun e =>
      hhq (e ▸ hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h)))
    have hQm : Q < IsLocalRing.maximalIdeal R :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top) hne
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hqQ
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQm
    rw [hq1] at h1
    rw [hm2] at h2
    have h3 : (1 : ℕ∞) + 1 + 1 ≤ 2 := (add_le_add h1 le_rfl).trans h2
    exact absurd h3 (by decide)
  have hJm : q ⊔ Ideal.span {h} = IsLocalRing.maximalIdeal R := by
    rw [← hrad.radical, Ideal.radical_eq_sInf]
    exact le_antisymm (sInf_le ⟨hle_m, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩)
      (le_sInf fun Q ⟨hle, hQ⟩ => (hmax Q hQ hle).ge)
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  have hπm : Ideal.map π (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal P.localRing := by
    have : IsLocalHom π := IsLocalHom.of_surjective π hπ
    exact IsLocalRing.map_maximalIdeal_of_surjective π hπ
  have hπq : Ideal.map π q = IsLocalRing.maximalIdeal P.localRing := by
    rw [← hπm, ← hJm, Ideal.map_sup, Ideal.map_span, Set.image_singleton, hπh,
      Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq]
  have hϖm : ϖ ∈ Ideal.map π q := by
    rw [hπq]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  obtain ⟨t, htq, htϖ⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp hϖm
  refine ⟨t, htϖ ▸ hϖ, ?_⟩
  have hϖspan : IsLocalRing.maximalIdeal P.localRing = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hqm : q ≤ IsLocalRing.maximalIdeal R := le_sup_left.trans hle_m
  have hmth : Ideal.span (Set.range ![t, h]) = IsLocalRing.maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hqm htq
      · exact hm
    · rw [← hJm]
      refine sup_le (fun x hx => ?_) (Ideal.span_mono ?_)
      · have hx' : π x ∈ Ideal.span {ϖ} := by
          rw [← hϖspan, ← hπq]
          exact Ideal.mem_map_of_mem π hx
        obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hx'
        obtain ⟨s', rfl⟩ := hπ s
        have hdiff : x - s' * t ∈ Ideal.span {h} := by
          rw [← hker, RingHom.mem_ker, map_sub, map_mul, htϖ, hs, sub_self]
        have hx : x = s' * t + (x - s' * t) := by ring
        rw [hx]
        refine add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩))
          (Ideal.span_mono ?_ hdiff)
        rintro _ rfl
        exact ⟨1, rfl⟩
      · rintro _ rfl
        exact ⟨1, rfl⟩
  have hpair : Set.range ![t, h] = {t, h} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun h' => h'.imp Eq.symm Eq.symm, fun h' => h'.imp Eq.symm Eq.symm⟩
  have hmth' : Ideal.span {t, h} = IsLocalRing.maximalIdeal R := hpair ▸ hmth
  haveI : IsRegularLocalRing R := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le R ?_
    rw [← hmth', hdimR]
    have hle : (Ideal.span {t, h}).spanFinrank ≤ 2 :=
      (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
        ((Set.ncard_insert_le t {h}).trans (by rw [Set.ncard_singleton]))
    exact_mod_cast hle
  have hlist : Ideal.ofList [t, h] = IsLocalRing.maximalIdeal R := by
    rw [← hmth', Ideal.ofList]
    congr 1
    ext x
    simp
  have hfr : (IsLocalRing.maximalIdeal R).spanFinrank = 2 := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdimR] at this
    exact_mod_cast this
  -- [Stacks, Tag 00NQ]: a regular local ring modulo part of a minimal generating list of its
  -- maximal ideal is regular.
  haveI hreg : IsRegularLocalRing (R ⧸ Ideal.span {t}) := by
    have := (((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      R).1 [t, h] hlist (by simp [hfr])).2 1 (by simp)).1
    have hset : {r : R | r ∈ [t, h].take 1} = {t} := by
      ext x
      simp
    rwa [Ideal.ofList, hset] at this
  have hprime : (Ideal.span {t}).IsPrime := by
    have : IsDomain (R ⧸ Ideal.span {t}) := IsRegularLocalRing.isDomain _
    exact (Ideal.Quotient.isDomain_iff_prime _).1 this
  have hle : Ideal.span {t} ≤ q := by
    rwa [Ideal.span_le, Set.singleton_subset_iff]
  by_contra hne
  have hlt : Ideal.span {t} < q := lt_of_le_of_ne hle hne
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at htϖ
    exact hϖ.ne_zero htϖ.symm
  have hbot : (⊥ : Ideal R) < Ideal.span {t} := by
    rw [bot_lt_iff_ne_bot]
    exact Ideal.span_singleton_eq_bot.not.mpr ht0
  have : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hq1] at h2
  have h3 : (0 : ℕ∞) + 1 + 1 ≤ 1 :=
    (add_le_add ((add_le_add zero_le le_rfl).trans h1) le_rfl).trans h2
  exact absurd h3 (by decide)

/-- **The coefficient of the restriction of a Cartier divisor along a prime divisor of the
cut.** Let `D` be a Cartier divisor on `Z` whose components have generic points off the normal
Cartier divisor `V = V(I)` and meet `V` in reduced subschemes. At the generic point of a prime
divisor `P` of `V`, with image `y`, a local equation `φ` of `D` is a unit times `∏ t_E^{d_E}`
over the components `E ∋ y`, `t_E` generating the prime of `E` in `𝒪_{Z,y}`
(`exists_span_eq_primeOfSpecializes`) and restricting to a uniformizer of `𝒪_{V,P}`; so the
order of the restriction of `φ` along `P` is `∑_{E ∋ y} d_E`. -/
private theorem exists_coeff_restrictComponents_eq_ordUnit [CompactSpace Z]
    {I : Z.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    [IsLocallyNoetherian I.subscheme] [IsNormal I.subscheme]
    (D : MMP.Mori.Divisor Z) (hDc : D.IsCartier)
    (hDgen : ∀ E ∈ D.support, E.genericPoint ∉ I.support)
    (hDred : ∀ E ∈ D.support, ((E.support : Set Z) ∩ I.support).Nonempty →
      IsReduced (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure {E.genericPoint}) ⊔ I).subscheme)
    (hB : ∀ Z' : irreducibleComponents I.subscheme,
      I.subschemeι (componentGenericPoint I.subscheme Z') ∉ D.supp)
    (P : MMP.Mori.PrimeDivisor I.subscheme) :
    ∃ (U : Z.Opens) (φ : (RationalFunctions Z)ˣ) (hφ : D.IsLocalEquation U φ)
      (hP : (P.support ∩ I.subschemeι ⁻¹ᵁ U).Nonempty),
      (D.restrictComponents I.subschemeι).coeff P =
        P.ordUnit (pullbackComponent I.subschemeι hB hφ P.component
          (P.map_componentGenericPoint_mem _ hP)) := by
  classical
  set ι := I.subschemeι with hι
  set v := P.genericPoint
  set y := ι v with hydef
  have : IsNoetherian Z := {}
  have : NoetherianSpace I.subscheme := ι.isClosedEmbedding.isInducing.noetherianSpace
  have hyI : y ∈ I.support := by
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨v, rfl⟩
  -- the coefficient of the restriction
  have hfin : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff ι D)).Finite :=
    DivisorWithCoeffs.finite_support_restrictComponentsCoeff ι D fun E hE s hs =>
      notMem_support_of_coheight_eq_zero hI E (hDgen E hE) hs
  rw [DivisorWithCoeffs.coeff_restrictComponents ι hfin P]
  -- a local equation near `y`
  obtain ⟨U, hyU, φ, hφ⟩ := hDc y
  have hvP : v ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hP : (P.support ∩ ι ⁻¹ᵁ U).Nonempty := ⟨v, hvP, hyU⟩
  refine ⟨U, φ, hφ, hP, ?_⟩
  set T := D.support.filter (fun E => y ∈ E.support) with hT
  -- generators `t_E` of the primes of the components through `y`
  have hTt : ∀ E : MMP.Mori.PrimeDivisor Z, ∃ t : Z.presheaf.stalk y, E ∈ T →
      Irreducible ((ι.stalkMap v).hom t) ∧
        ∃ hsp : E.genericPoint ⤳ y, Ideal.span {t} = primeOfSpecializes hsp := by
    intro E
    by_cases hE : E ∈ T
    · obtain ⟨hED, hyE⟩ := Finset.mem_filter.mp hE
      have hsp : E.genericPoint ⤳ y := by
        rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      obtain ⟨t, ht1, ht2⟩ := exists_span_eq_primeOfSpecializes hI P E hsp (hDgen E hED)
        (hDred E hED ⟨y, hyE, hyI⟩)
      exact ⟨t, fun _ => ⟨ht1, hsp, ht2⟩⟩
    · exact ⟨1, fun h => absurd h hE⟩
  choose t ht using hTt
  have ht0 : ∀ E ∈ T, t E ≠ 0 := fun E hE h0 =>
    (ht E hE).1.ne_zero (by rw [h0, map_zero])
  let τ : MMP.Mori.PrimeDivisor Z → (RationalFunctions Z)ˣ := fun E =>
    if hE : E ∈ T then stalkUnit (t E) (ht0 E hE) else 1
  have hτ : ∀ E (hE : E ∈ T), τ E = stalkUnit (t E) (ht0 E hE) := fun E hE => dif_pos hE
  -- orders of the `t_E` along the prime divisors through `y`
  have hordτ : ∀ E ∈ T, ∀ G : MMP.Mori.PrimeDivisor Z, y ∈ G.support →
      G.ord (τ E) = if G = E then 1 else 0 := by
    intro E hE G hyG
    obtain ⟨-, hspE, hqE⟩ := ht E hE
    have hspG : G.genericPoint ⤳ y := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [hτ E hE]
    split_ifs with hGE
    · subst hGE
      exact ord_stalkUnit_eq_one (ht0 _ hE) G hspG hqE
    · refine ord_stalkUnit_eq_zero (ht0 E hE) G hspG fun htG => hGE ?_
      have hle : primeOfSpecializes hspE ≤ primeOfSpecializes hspG := by
        rwa [← hqE, Ideal.span_le, Set.singleton_subset_iff]
      have heq : primeOfSpecializes hspE = primeOfSpecializes hspG := by
        by_contra hne
        have := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
        rw [height_primeOfSpecializes, height_primeOfSpecializes,
          AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
          AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
        exact absurd this (by decide)
      have h1 := specializes_of_primeOfSpecializes_le hspE hspG heq.le
      have h2 := specializes_of_primeOfSpecializes_le hspG hspE heq.ge
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h2.antisymm h1).eq
  -- dividing the local equation by `∏ t_E ^ d_E` leaves a unit at `y`
  set ψ := φ * ∏ E ∈ T, τ E ^ (-(D.coeff E)) with hψ
  have hψord : ∀ G : MMP.Mori.PrimeDivisor Z, y ∈ G.support → G.ord ψ = 0 := by
    intro G hyG
    rw [hψ, PrimeDivisor.ord_mul, ord_prod, ← hφ G ⟨y, hyG, hyU⟩]
    have hsum : ∑ E ∈ T, G.ord (τ E ^ (-(D.coeff E))) =
        ∑ E ∈ T, if G = E then -(D.coeff E) else 0 := by
      refine Finset.sum_congr rfl fun E hE => ?_
      rw [PrimeDivisor.ord_zpow, hordτ E hE G hyG]
      split_ifs <;> simp
    rw [hsum, Finset.sum_ite_eq]
    split_ifs with hGT
    · ring
    · have : G ∉ D.support := fun hGD => hGT (Finset.mem_filter.mpr ⟨hGD, hyG⟩)
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp this, add_zero]
  set x₀ := componentGenericPoint I.subscheme P.component
  set y₀ := ι x₀
  have hx₀v : x₀ ⤳ v := P.specializes_genericPoint
  have hy₀y : y₀ ⤳ y := ι.base.hom.map_specializes hx₀v
  have hy₀U : y₀ ∈ U := P.map_componentGenericPoint_mem ι hP
  set W := pointComponent y₀
  have hy₀W : y₀ ∈ W.1 := mem_pointComponent y₀
  have hyW : y ∈ W.1 := mem_irreducibleComponents_of_irreducibleSpace W y
  obtain ⟨a, ha⟩ := exists_unit_stalk_of_forall_ord_eq_zero hyW ψ hψord
  -- the `t_E` are units at `y₀`
  have hu : ∀ E ∈ T, IsUnit ((Z.presheaf.stalkSpecializes hy₀y).hom (t E)) := by
    intro E hE
    obtain ⟨-, hspE, hqE⟩ := ht E hE
    by_contra hnu
    have htq0 : t E ∈ primeOfSpecializes hy₀y := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hle : primeOfSpecializes hspE ≤ primeOfSpecializes hy₀y := by
      rwa [← hqE, Ideal.span_le, Set.singleton_subset_iff]
    have hy₀E : y₀ ∈ E.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact specializes_iff_mem_closure.mp (specializes_of_primeOfSpecializes_le hspE hy₀y hle)
    exact hB P.component (DivisorWithCoeffs.mem_supp_iff.mpr
      ⟨E, Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hE).1, hy₀E⟩)
  let u : MMP.Mori.PrimeDivisor Z → (Z.presheaf.stalk y₀)ˣ := fun E =>
    if hE : E ∈ T then (hu E hE).unit else 1
  have huval : ∀ E (hE : E ∈ T), (u E : Z.presheaf.stalk y₀) =
      (Z.presheaf.stalkSpecializes hy₀y).hom (t E) := fun E hE => by
    simp only [u, dif_pos hE, IsUnit.unit_spec]
  set b := Units.map (Z.presheaf.stalkSpecializes hy₀y).hom.toMonoidHom a *
    ∏ E ∈ T, u E ^ D.coeff E with hbdef
  have hb : (stalkToRationalFunctions Z hy₀W).hom b = (φ : RationalFunctions Z) W := by
    have key : Units.map (stalkToRationalFunctions Z hy₀W).hom.toMonoidHom b =
        Units.map (RationalFunctions.component Z W).toMonoidHom φ := by
      have hφψ : φ = ψ * ∏ E ∈ T, τ E ^ (D.coeff E) := by
        rw [hψ, mul_assoc, ← Finset.prod_mul_distrib]
        simp [← zpow_add]
      rw [hφψ, hbdef, map_mul, map_mul, map_prod, map_prod]
      congr 1
      · ext
        change (stalkToRationalFunctions Z hy₀W).hom
          ((Z.presheaf.stalkSpecializes hy₀y).hom (a : Z.presheaf.stalk y)) =
          (ψ : RationalFunctions Z) W
        rw [← ha]
        change (Z.presheaf.stalkSpecializes hy₀y ≫ Z.presheaf.stalkSpecializes _).hom
          (a : Z.presheaf.stalk y) = (Z.presheaf.stalkSpecializes _).hom (a : Z.presheaf.stalk y)
        rw [TopCat.Presheaf.stalkSpecializes_comp]
      · refine Finset.prod_congr rfl fun E hE => ?_
        rw [map_zpow, map_zpow]
        congr 1
        ext
        change (stalkToRationalFunctions Z hy₀W).hom (u E : Z.presheaf.stalk y₀) =
          (τ E : RationalFunctions Z) W
        rw [huval E hE, hτ E hE, stalkUnit_apply]
        change (Z.presheaf.stalkSpecializes hy₀y ≫ Z.presheaf.stalkSpecializes _).hom (t E) =
          (Z.presheaf.stalkSpecializes _).hom (t E)
        rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact congrArg Units.val key
  rw [pullbackComponent_eq hB hφ hy₀U hy₀W b hb]
  rw [hbdef, map_mul, map_prod, PrimeDivisor.ordUnit_mul, ordUnit_prod]
  have h1 : P.ordUnit (Units.map (ι.stalkMap x₀).hom.toMonoidHom
      (Units.map (Z.presheaf.stalkSpecializes hy₀y).hom.toMonoidHom a)) = 0 := by
    refine P.ordUnit_eq_zero_of_isUnit (a.isUnit.map (ι.stalkMap v).hom) ?_
    change (I.subscheme.presheaf.stalkSpecializes _).hom
      ((ι.stalkMap v).hom (a : Z.presheaf.stalk y)) =
      (ι.stalkMap x₀).hom ((Z.presheaf.stalkSpecializes hy₀y).hom (a : Z.presheaf.stalk y))
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]
  have h2 : ∀ E ∈ T, P.ordUnit (Units.map (ι.stalkMap x₀).hom.toMonoidHom (u E ^ D.coeff E)) =
      D.coeff E := by
    intro E hE
    rw [map_zpow, PrimeDivisor.ordUnit_zpow]
    have hv := P.valuation_eq_exp_ordUnit (Units.map (ι.stalkMap x₀).hom.toMonoidHom (u E))
    have hval : ((Units.map (ι.stalkMap x₀).hom.toMonoidHom (u E) :
        (I.subscheme.presheaf.stalk x₀)ˣ) : I.subscheme.presheaf.stalk x₀) =
        P.toComponent.hom ((ι.stalkMap v).hom (t E)) := by
      change (ι.stalkMap x₀).hom (u E : Z.presheaf.stalk y₀) = _
      rw [huval E hE, Scheme.Hom.stalkSpecializes_stalkMap_apply]
      rfl
    rw [hval, P.valuation_toComponent_of_irreducible (ht E hE).1] at hv
    rw [← WithZero.exp_injective hv, mul_one]
  rw [h1, zero_add, Finset.sum_congr rfl h2, Finsupp.sum, hT, Finset.sum_filter]
  rfl

end Local

/-- **The restriction formula for divisors with transversal components.** Let `Z` be a normal
integral locally Noetherian scheme and `I` an ideal sheaf locally generated by a non-zero-divisor
whose subscheme `V` is normal, containing the generic point of none of the closed sets `F j`, and
meeting each `F j` in a reduced subscheme. Then every `ℚ`-Cartier `ℚ`-divisor `B` whose components
are among the `F j` pulls back to `V` as `∑ bᵢ [Bᵢ ∩ V]`. -/
private theorem exists_isPullback_restrictComponents {Z : Scheme.{u}} [IsIntegral Z] [IsNormal Z]
    [IsLocallyNoetherian Z] [CompactSpace Z] (I : Z.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    [IsLocallyNoetherian I.subscheme] [IsNormal I.subscheme]
    {J : Type*} (F : J → Closeds Z)
    (hFgen : ∀ j, ∀ η : Z, IsGenericPoint η (F j : Set Z) → η ∉ I.support)
    (hFred : ∀ j, ((F j : Set Z) ∩ I.support).Nonempty →
      IsReduced (Scheme.IdealSheafData.vanishingIdeal (F j) ⊔ I).subscheme)
    (B : QDivisor Z) (hBq : B.IsQCartier) (hBF : ∀ E ∈ B.support, ∃ j, (E.support : Set Z) = F j) :
    ∃ hB, B.IsPullback I.subschemeι hB (B.restrictComponents I.subschemeι) := by
  classical
  set ι := I.subschemeι with hι
  have hgen : ∀ E : MMP.Mori.PrimeDivisor Z, (∃ j, (E.support : Set Z) = F j) →
      E.genericPoint ∉ I.support := by
    rintro E ⟨j, hj⟩
    refine hFgen j E.genericPoint ?_
    rw [← hj, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rfl
  have hred : ∀ E : MMP.Mori.PrimeDivisor Z, (∃ j, (E.support : Set Z) = F j) →
      ((E.support : Set Z) ∩ I.support).Nonempty →
      IsReduced (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure {E.genericPoint}) ⊔ I).subscheme := by
    rintro E ⟨j, hj⟩ hne
    have hFj : F j = Closeds.closure {E.genericPoint} := Closeds.ext (by
      rw [Closeds.coe_closure, ← hj, AlgebraicGeometry.PrimeDivisor.support_eq_closure])
    rw [← hFj]
    exact hFred j (hj ▸ hne)
  have hB : ∀ Z' : irreducibleComponents I.subscheme,
      ι (componentGenericPoint I.subscheme Z') ∉ B.supp := by
    intro Z' hmem
    obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    exact notMem_support_of_coheight_eq_zero hI E
      (hgen E (hBF E (Finsupp.mem_support_iff.mpr hE))) (coheight_componentGenericPoint Z') hyE
  refine ⟨hB, fun m hm D hD hDc => ?_⟩
  have hDcoeff : ∀ E, ((D.coeff E : ℤ) : ℚ) = m * B.coeff E := by
    intro E
    have := congrArg (fun G : MMP.Mori.QDivisor Z => G.coeff E) hD
    simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul] using this
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hDsupp : D.support = B.support := by
    ext E
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    have h := hDcoeff E
    constructor
    · intro hD0 hB0
      apply hD0
      rw [← DivisorWithCoeffs.coeff_apply] at hB0 ⊢
      rw [hB0, mul_zero] at h
      exact_mod_cast h
    · intro hB0 hD0
      apply hB0
      rw [← DivisorWithCoeffs.coeff_apply] at hD0 ⊢
      rw [hD0, Int.cast_zero, eq_comm, mul_eq_zero] at h
      exact h.resolve_left hmq
  have hDF : ∀ E ∈ D.support, ∃ j, (E.support : Set Z) = F j := fun E hE =>
    hBF E (hDsupp ▸ hE)
  have : IsNoetherian Z := {}
  have : NoetherianSpace I.subscheme := ι.isClosedEmbedding.isInducing.noetherianSpace
  have hfinD : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff ι D)).Finite :=
    DivisorWithCoeffs.finite_support_restrictComponentsCoeff ι D fun E hE s hs =>
      notMem_support_of_coheight_eq_zero hI E (hgen E (hDF E hE)) hs
  have hfinB : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff ι B)).Finite :=
    DivisorWithCoeffs.finite_support_restrictComponentsCoeff ι B fun E hE s hs =>
      notMem_support_of_coheight_eq_zero hI E (hgen E (hBF E hE)) hs
  refine ⟨D.restrictComponents ι, ?_, ?_⟩
  · refine DivisorWithCoeffs.ext' fun P => ?_
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_restrictComponents ι hfinD,
      DivisorWithCoeffs.coeff_restrictComponents ι hfinB, Finsupp.sum, Finsupp.sum, hDsupp,
      Int.cast_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs
    · rw [zsmul_eq_mul]
      exact_mod_cast hDcoeff E
    · simp
  · refine MMP.Mori.Divisor.IsPullback.of_forall_exists fun P => ?_
    exact exists_coeff_restrictComponents_eq_ordUnit hI D hDc (fun E hE => hgen E (hDF E hE))
      (fun E hE => hred E (hDF E hE)) _ P

end Restriction

/-- **Bertini for general hyperplane pullbacks.** Let `k` be algebraically closed of
characteristic zero, `Z` a normal variety over `k`, `φ : Z ⟶ ℙᴺ_k` a `k`-morphism and `F j`
(`j ∈ J`, `J` finite) irreducible closed subsets of `Z`. There is a dense open `U` of the dual
projective space such that for every hyperplane `[c] ∈ U`, with `Z_H = hyperplaneSection φ c`:
(a) if `dim φ(Z) ≥ 2`, `Z_H` is a normal variety with `dim Z_H + 1 = dim Z`;
(b) for each `j`, if `φ(F j)` is a point then `F j ∩ Z_H = ∅`, and otherwise `F j ∩ Z_H` is
non-empty, its scheme structure `vanishingIdeal (F j) ⊔ Z_H` is reduced, every irreducible
component of it has dimension `dim F j - 1`, and it is irreducible when `dim φ(F j) ≥ 2`;
(c) `Z_H` is normal, and for every `ℚ`-Cartier `ℚ`-divisor `B` whose prime components are
among the `F j`, no component of `Z_H` maps into `Supp B` and the pull-back of `B` to `Z_H` is
`B.restrictComponents`, the divisor `∑ bᵢ [Bᵢ ∩ Z_H]`. -/
@[mmp "lem_mmp_foundation_km2a_hyperplane_bertini"]
public theorem exists_dense_open_hyperplaneSection_restrictComponents {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {N : ℕ} {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [IsVariety k (Z ↘ Spec (.of k))] [IsNormal Z] [IsLocallyNoetherian Z]
    (φ : Z ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))
    (hφ : φ ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k N = Z ↘ Spec (.of k))
    {J : Type*} [Finite J] (F : J → Closeds Z) (hF : ∀ j, IsIrreducible (F j : Set Z)) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        (2 ≤ topologicalKrullDim (closure (Set.range φ.base)) →
          IsVariety k ((hyperplaneSection φ c).subschemeι ≫ Z ↘ Spec (.of k)) ∧
          IsNormal (hyperplaneSection φ c).subscheme ∧
          topologicalKrullDim (hyperplaneSection φ c).subscheme + 1 = topologicalKrullDim Z) ∧
        (∀ j, ((φ.base '' F j).Subsingleton →
            (F j : Set Z) ∩ (hyperplaneSection φ c).support = ∅) ∧
          (¬ (φ.base '' F j).Subsingleton →
            ((F j : Set Z) ∩ (hyperplaneSection φ c).support).Nonempty ∧
            IsReduced (Scheme.IdealSheafData.vanishingIdeal (F j) ⊔
              hyperplaneSection φ c).subscheme ∧
            (∀ C ∈ irreducibleComponents (Scheme.IdealSheafData.vanishingIdeal (F j) ⊔
                hyperplaneSection φ c).subscheme,
              topologicalKrullDim C + 1 = topologicalKrullDim (F j)) ∧
            (2 ≤ topologicalKrullDim (closure (φ.base '' F j)) →
              IsIrreducible ((F j : Set Z) ∩ (hyperplaneSection φ c).support)))) ∧
        ∃ (_ : IsLocallyNoetherian (hyperplaneSection φ c).subscheme)
          (_ : IsNormal (hyperplaneSection φ c).subscheme), ∀ (B : MMP.Mori.QDivisor Z),
          B.IsQCartier → (∀ E ∈ B.support, ∃ j, (E.support : Set Z) = F j) →
          ∃ hB, B.IsPullback (hyperplaneSection φ c).subschemeι hB
            (B.restrictComponents (hyperplaneSection φ c).subschemeι) := by
  classical
  haveI : φ.IsOver (Spec (.of k)) := ⟨hφ⟩
  obtain ⟨U₀, hU₀, h₀⟩ := exists_dense_open_hyperplaneSection_variety φ
  obtain ⟨U₁, hU₁, h₁⟩ := exists_dense_open_forall
    (fun j => exists_dense_open_hyperplaneSection_closeds φ (F j) (hF j))
  refine ⟨U₀ ⊓ U₁, dense_coe_inf hU₀ hU₁, fun c hc hm => ?_⟩
  obtain ⟨hgen, -, -, hdim, hint, hnorm⟩ := h₀ c hc hm.1
  have hj := h₁ c hc hm.2
  haveI : IsLocallyNoetherian (hyperplaneSection φ c).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (hyperplaneSection φ c).subschemeι
  haveI : IsNormal (hyperplaneSection φ c).subscheme := hnorm inferInstance
  refine ⟨fun h2 => ?_, fun j => (hj j).2, inferInstance, inferInstance, ?_⟩
  · have : IsIntegral (hyperplaneSection φ c).subscheme := hint h2
    refine ⟨isVariety_subschemeι_comp _, inferInstance, ?_⟩
    have huniv : (Set.univ : Set (hyperplaneSection φ c).subscheme) ∈
        irreducibleComponents (hyperplaneSection φ c).subscheme := by
      rw [irreducibleComponents_eq_singleton]
      rfl
    rw [← (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq]
    exact hdim _ huniv
  · intro B hBq hBF
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
    refine exists_isPullback_restrictComponents _
      (isEffectiveCartierDivisor_hyperplaneSection φ c hc hgen) F (fun j => (hj j).1)
      (fun j hne => ?_) B hBq hBF
    by_cases hsub : (φ.base '' F j).Subsingleton
    · rw [(hj j).2.1 hsub] at hne
      exact absurd hne Set.not_nonempty_empty
    · exact ((hj j).2.2 hsub).2.1

end HyperplaneSections

end MMP.Threefold.Bridges

namespace MMP

open TensorProduct

/-! ### Reducedness detected by a nonzerodivisor -/

section Reduced

variable {C : Type*} [CommRing C]

/-- In a reduced ring, an element outside every minimal prime is a nonzerodivisor. -/
private theorem eq_zero_of_mul_eq_zero_of_forall_notMem_minimalPrimes [IsReduced C] {x : C}
    (hx : ∀ p ∈ minimalPrimes C, x ∉ p) {z : C} (hz : x * z = 0) : z = 0 := by
  have hmem : z ∈ sInf (minimalPrimes C) := by
    refine Submodule.mem_sInf.mpr fun p hp => ?_
    have := hp.1.1
    exact (this.mem_or_mem (hz ▸ p.zero_mem)).resolve_left (hx p hp)
  rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero z ⟨n, by simpa using hn⟩

/-- A ring with a nonzerodivisor `x` whose local rings at the primes not containing `x` are
reduced is reduced. -/
private theorem isReduced_of_forall_isReduced_localization {x : C}
    (hx : ∀ z : C, x * z = 0 → z = 0)
    (hloc : ∀ (P : Ideal C) [P.IsPrime], x ∉ P → IsReduced (Localization.AtPrime P)) :
    IsReduced C := by
  refine ⟨fun n hn => ?_⟩
  let I : Ideal C := LinearMap.ker (LinearMap.mulRight C n)
  have hI : ∀ t, t ∈ I ↔ t * n = 0 := fun t => by simp [I]
  have hxI : x ∈ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.mpr fun (P : Ideal C) ⟨hIP, hP⟩ => ?_
    by_contra hxP
    have := hloc P hxP
    have h0 : algebraMap C (Localization.AtPrime P) n = 0 :=
      IsNilpotent.eq_zero (hn.map _)
    obtain ⟨⟨m, hm⟩, hmn⟩ := (IsLocalization.map_eq_zero_iff (Ideal.primeCompl P) _ n).mp h0
    exact hm (hIP ((hI m).mpr hmn))
  obtain ⟨k, hk⟩ := hxI
  rw [hI] at hk
  clear hI
  induction k with
  | zero => simpa using hk
  | succ k ih => exact ih (hx _ (by rwa [← mul_assoc, ← pow_succ']))

end Reduced

/-! ### Nonzerodivisors under base change -/

section FlatSpreading

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra B C]

/-- Exactness of `C →(x·) C → C/(x)`. -/
private theorem exact_mulLeft_mk (x : C) :
    Function.Exact (LinearMap.mulLeft B x)
      (Ideal.Quotient.mkₐ B (Ideal.span {x})).toLinearMap := by
  intro c
  simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton', Set.mem_range, LinearMap.mulLeft_apply]
  exact ⟨fun ⟨d, hd⟩ => ⟨d, by rwa [mul_comm]⟩,
    fun ⟨d, hd⟩ => ⟨d, by rwa [mul_comm]⟩⟩

/-- Multiplication by `1 ⊗ x` on `Q ⊗ C` is the base change of multiplication by `x`. -/
private theorem one_tmul_mul_eq_lTensor (Q : Type*) [CommRing Q] [Algebra B Q] (x : C)
    (z : Q ⊗[B] C) : (1 ⊗ₜ[B] x) * z = (LinearMap.mulLeft B x).lTensor Q z := by
  induction z with
  | tmul q c => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add z w hz hw => rw [mul_add, map_add, hz, hw]

/-- **Nonzerodivisors survive base change when the quotient is flat.** If `x` is a nonzerodivisor
on `C` and `C/(x)` is flat over `B`, then `1 ⊗ x` is a nonzerodivisor on `Q ⊗_B C` for every
`B`-algebra `Q`. -/
private theorem one_tmul_mul_eq_zero (Q : Type*) [CommRing Q] [Algebra B Q] {x : C}
    [Module.Flat B (C ⧸ Ideal.span {x})] (hx : ∀ z : C, x * z = 0 → z = 0) :
    ∀ z : Q ⊗[B] C, (1 ⊗ₜ x) * z = 0 → z = 0 := by
  have hinjx : Function.Injective (LinearMap.mulLeft B x) := fun a b h => by
    have := hx (a - b) (by rw [mul_sub]; exact sub_eq_zero.mpr h)
    exact sub_eq_zero.mp this
  have h1 := LinearMap.lTensor_injective_of_exact_of_flat _
    (Ideal.Quotient.mkₐ_surjective B (Ideal.span {x})) _ hinjx (exact_mulLeft_mk x) Q
  exact fun z hz => h1 (by rw [map_zero, ← one_tmul_mul_eq_lTensor, hz])

/-- For a flat `B`-module `N` and an injective `B → K`, the map `N → K ⊗ N` is injective. -/
private theorem one_tmul_injective (K : Type*) [CommRing K] [Algebra B K]
    (hK : Function.Injective (algebraMap B K)) (N : Type*) [AddCommGroup N] [Module B N]
    [Module.Flat B N] : Function.Injective (fun n : N => (1 : K) ⊗ₜ[B] n) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := N) (Algebra.linearMap B K) hK
  intro a b hab
  apply (TensorProduct.lid B N).symm.injective
  apply h
  simpa using hab

/-- **A nonzerodivisor on a flat algebra is detected generically.** If `B → K` is injective, `C`
is flat over `B` and `1 ⊗ x` is a nonzerodivisor on `K ⊗_B C`, then `x` is one on `C`. -/
private theorem mul_eq_zero_of_tensor (K : Type*) [CommRing K] [Algebra B K]
    (hK : Function.Injective (algebraMap B K)) {x : C} [Module.Flat B C]
    (hx : ∀ z : K ⊗[B] C, (1 ⊗ₜ x) * z = 0 → z = 0) : ∀ z : C, x * z = 0 → z = 0 := by
  have hC := one_tmul_injective K hK C
  refine fun z hz => hC ?_
  simp only [tmul_zero]
  exact hx _ (by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hz, tmul_zero])

/-- Exactness of `C/(x) →(y·) C/(x) → C/(x, y)`. -/
private theorem exact_mulLeft_factor (x y : C) :
    Function.Exact (LinearMap.mulLeft B (Ideal.Quotient.mk (Ideal.span {x}) y))
      (Ideal.Quotient.factorₐ B (Ideal.span_mono (by simp) :
        Ideal.span {x} ≤ Ideal.span {x, y})).toLinearMap := by
  intro c
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_pair, Set.mem_range, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨Ideal.Quotient.mk _ b, ?_⟩
    rw [← map_mul, Ideal.Quotient.eq, ← h]
    exact Ideal.mem_span_singleton'.mpr ⟨-a, by ring⟩
  · rintro ⟨d, hd⟩
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [← map_mul, Ideal.Quotient.eq] at hd
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hd
    exact ⟨-a, d, by linear_combination -ha⟩

/-- **Regular pairs survive base change when the quotients are flat.** If `x, y` is a regular
sequence on `C` and `C/(x)`, `C/(x, y)` are flat over `B`, then `1 ⊗ x, 1 ⊗ y` is a regular
sequence on `Q ⊗_B C` for every `B`-algebra `Q`. -/
private theorem regular_pair_tensor (Q : Type*) [CommRing Q] [Algebra B Q] {x y : C}
    [Module.Flat B (C ⧸ Ideal.span {x})] [Module.Flat B (C ⧸ Ideal.span {x, y})]
    (hx : ∀ z : C, x * z = 0 → z = 0)
    (hy : ∀ z : C, y * z ∈ Ideal.span {x} → z ∈ Ideal.span {x}) :
    (∀ z : Q ⊗[B] C, (1 ⊗ₜ x) * z = 0 → z = 0) ∧
      ∀ z : Q ⊗[B] C, (1 ⊗ₜ y) * z ∈ Ideal.span {1 ⊗ₜ x} → z ∈ Ideal.span {1 ⊗ₜ x} := by
  have hinjx : Function.Injective (LinearMap.mulLeft B x) := fun a b h => by
    have := hx (a - b) (by rw [mul_sub]; exact sub_eq_zero.mpr h)
    exact sub_eq_zero.mp this
  have hinjy : Function.Injective (LinearMap.mulLeft B (Ideal.Quotient.mk (Ideal.span {x}) y)) :=
    fun a b h => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      simp only [LinearMap.mulLeft_apply, ← map_mul, Ideal.Quotient.eq] at h ⊢
      exact hy _ (by rwa [mul_sub])
  have h1 := LinearMap.lTensor_injective_of_exact_of_flat _
    (Ideal.Quotient.mkₐ_surjective B (Ideal.span {x})) _ hinjx (exact_mulLeft_mk x) Q
  have h2 := LinearMap.lTensor_injective_of_exact_of_flat _
    (fun c => by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨Ideal.Quotient.mk _ c, rfl⟩) _ hinjy (exact_mulLeft_factor x y) Q
  have hex := lTensor_exact Q (exact_mulLeft_mk (B := B) x)
    (Ideal.Quotient.mkₐ_surjective B (Ideal.span {x}))
  refine ⟨fun z hz => h1 (by rw [map_zero, ← one_tmul_mul_eq_lTensor, hz]), fun z hz => ?_⟩
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hz
  have hπ : ((Ideal.Quotient.mkₐ B (Ideal.span {x})).toLinearMap.lTensor Q) ((1 ⊗ₜ y) * z) = 0 :=
    (hex _).mpr ⟨w, by rw [← one_tmul_mul_eq_lTensor, mul_comm, hw]⟩
  have hnat : ∀ t : Q ⊗[B] C,
      ((Ideal.Quotient.mkₐ B (Ideal.span {x})).toLinearMap.lTensor Q) ((1 ⊗ₜ y) * t) =
        (LinearMap.mulLeft B (Ideal.Quotient.mk (Ideal.span {x}) y)).lTensor Q
          (((Ideal.Quotient.mkₐ B (Ideal.span {x})).toLinearMap.lTensor Q) t) := by
    intro t
    induction t with
    | tmul q c => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add t₁ t₂ h₁ h₂ => rw [mul_add, map_add, map_add, map_add, h₁, h₂]
  rw [hnat] at hπ
  have h3 : ((Ideal.Quotient.mkₐ B (Ideal.span {x})).toLinearMap.lTensor Q) z = 0 :=
    h2 (by rw [hπ, map_zero])
  obtain ⟨w', hw'⟩ := (hex z).mp h3
  rw [← one_tmul_mul_eq_lTensor] at hw'
  exact Ideal.mem_span_singleton'.mpr ⟨w', by rwa [mul_comm]⟩

/-- **A regular pair on a flat algebra is detected generically.** If `B → K` is injective, `C`
and `C/(x)` are flat over `B`, and `1 ⊗ x, 1 ⊗ y` is regular on `K ⊗_B C`, then `x, y` is regular
on `C`. -/
private theorem regular_pair_of_tensor (K : Type*) [CommRing K] [Algebra B K]
    (hK : Function.Injective (algebraMap B K)) {x y : C} [Module.Flat B C]
    [Module.Flat B (C ⧸ Ideal.span {x})]
    (hx : ∀ z : K ⊗[B] C, (1 ⊗ₜ x) * z = 0 → z = 0)
    (hy : ∀ z : K ⊗[B] C, (1 ⊗ₜ y) * z ∈ Ideal.span {1 ⊗ₜ x} → z ∈ Ideal.span {1 ⊗ₜ x}) :
    (∀ z : C, x * z = 0 → z = 0) ∧ ∀ z : C, y * z ∈ Ideal.span {x} → z ∈ Ideal.span {x} := by
  have hC := one_tmul_injective K hK C
  have hCx := one_tmul_injective K hK (C ⧸ Ideal.span {x})
  have hex := lTensor_exact K (exact_mulLeft_mk (B := B) x)
    (Ideal.Quotient.mkₐ_surjective B (Ideal.span {x}))
  refine ⟨fun z hz => hC ?_, fun z hz => ?_⟩
  · simp only [tmul_zero]
    exact hx _ (by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hz, tmul_zero])
  · obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hz
    have h1 : (1 ⊗ₜ y) * ((1 : K) ⊗ₜ[B] z) ∈ Ideal.span {(1 : K) ⊗ₜ[B] x} :=
      Ideal.mem_span_singleton'.mpr ⟨1 ⊗ₜ w, by
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          hw]⟩
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (hy _ h1)
    have h2 : ((Ideal.Quotient.mkₐ B (Ideal.span {x})).toLinearMap.lTensor K) ((1 : K) ⊗ₜ z) = 0 :=
      (hex _).mpr ⟨v, by rw [← one_tmul_mul_eq_lTensor, mul_comm, hv]⟩
    rw [LinearMap.lTensor_tmul] at h2
    have h3 : Ideal.Quotient.mk (Ideal.span {x}) z = 0 := hCx (by simpa using h2)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3

end FlatSpreading

/-! ### Smoothness and regularity -/

section Smooth

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- If `D(g)` lies in the smooth locus of `R → A`, then over any field `k` the fibre ring
`k ⊗_R A` has regular local rings at the primes not containing `1 ⊗ g`. -/
private theorem isRegularLocalRing_of_basicOpen_subset_smoothLocus
    [Algebra.FinitePresentation R A] (k : Type*) [Field k] [Algebra R k] {g : A}
    (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆ Algebra.smoothLocus R A)
    (P : Ideal (k ⊗[R] A)) [P.IsPrime] (hgP : (1 : k) ⊗ₜ[R] g ∉ P) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  have := Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp hg
  have : IsRegularRing (k ⊗[R] Localization.Away g) := Algebra.isRegularRing_of_smooth k _
  let e := IsLocalization.Away.tensorProductEquivTMulRight R k g (Localization.Away g)
  have : IsRegularRing (Localization.Away ((1 : k) ⊗ₜ[R] g)) :=
    IsRegularRing.of_ringEquiv e.toRingEquiv
  have hdisj : Disjoint (Submonoid.powers ((1 : k) ⊗ₜ[R] g) : Set (k ⊗[R] A)) P :=
    (Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)).mpr hgP
  let P' : Ideal (Localization.Away ((1 : k) ⊗ₜ[R] g)) :=
    P.map (algebraMap _ (Localization.Away ((1 : k) ⊗ₜ[R] g)))
  have hP' : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers _) _ P ‹_› hdisj
  have hcomap : P'.comap (algebraMap _ _) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers _) _ ‹_› hdisj
  have := IsRegularRing.isRegularLocalRing_localization P'
  have key : ∀ (Q : Ideal (k ⊗[R] A)) [Q.IsPrime], Q = P →
      IsRegularLocalRing (Localization.AtPrime Q) →
        IsRegularLocalRing (Localization.AtPrime P) := by
    rintro Q _ rfl h
    exact h
  exact key _ hcomap (IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (Submonoid.powers _)
      P').symm.toRingEquiv)

/-- Over a field of characteristic zero, a finite type algebra is formally smooth at every prime
with regular local ring. -/
private theorem formallySmooth_localization_of_isRegularLocalRing {k S : Type*} [Field k]
    [CharZero k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    Algebra.FormallySmooth k (Localization.AtPrime q) := by
  have := Algebra.isSeparableExtension_of_perfectField k q.ResidueField
  exact (Algebra.isSmoothAt_iff_isRegularLocalRing q (Localization.AtPrime q)).mpr hq

/-- **Regular points of the generic fibre are smooth.** Let `R` be a domain with fraction field
`K = κ(⊥)` of characteristic zero and `A` an `R`-algebra of finite type. At a prime `P` of
`K ⊗_R A` with regular local ring, the contraction of `P` to `A` lies in the smooth locus of
`R → A`. -/
private theorem comap_mem_smoothLocus_of_isRegularLocalRing [IsDomain R] [Algebra.FiniteType R A]
    [CharZero (⊥ : Ideal R).ResidueField]
    (P : Ideal ((⊥ : Ideal R).ResidueField ⊗[R] A)) [P.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime P)) :
    (⟨P.comap (Algebra.TensorProduct.includeRight (R := R)
        (A := (⊥ : Ideal R).ResidueField) (B := A)).toRingHom, Ideal.comap_isPrime _ _⟩ :
      PrimeSpectrum A) ∈ Algebra.smoothLocus R A := by
  set K := (⊥ : Ideal R).ResidueField
  have hsm : Algebra.FormallySmooth K (Localization.AtPrime P) :=
    formallySmooth_localization_of_isRegularLocalRing P hreg
  have : Algebra.FormallySmooth R K := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors R)
  have : Algebra.FormallySmooth R (Localization.AtPrime P) := Algebra.FormallySmooth.comp R K _
  let : Algebra A (K ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (K ⊗[R] A) :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  have : IsLocalization.AtPrime (Localization.AtPrime P) (P.comap (algebraMap A (K ⊗[R] A))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (Localization.AtPrime P) P
  let e := IsLocalization.algEquiv (P.comap (algebraMap A (K ⊗[R] A))).primeCompl
    (Localization.AtPrime (P.comap (algebraMap A (K ⊗[R] A)))) (Localization.AtPrime P)
  exact Algebra.FormallySmooth.of_equiv (e.symm.restrictScalars R)

/-- **On a normal generic fibre, the non-smooth locus has codimension at least two.** Let `R` be
a domain with fraction field `K = κ(⊥)` of characteristic zero and `A` an `R`-algebra of finite
type with `K ⊗_R A` normal. At a prime `P` of `K ⊗_R A` of height at most one the local ring is
regular, hence formally smooth over `K`, and so the contraction of `P` to `A` lies in the smooth
locus of `R → A`. -/
private theorem comap_mem_smoothLocus_of_height_le_one [IsDomain R] [Algebra.FiniteType R A]
    [CharZero (⊥ : Ideal R).ResidueField]
    (hN : IsNormalRing ((⊥ : Ideal R).ResidueField ⊗[R] A))
    (P : Ideal ((⊥ : Ideal R).ResidueField ⊗[R] A)) [P.IsPrime] (hP : P.height ≤ 1) :
    (⟨P.comap (Algebra.TensorProduct.includeRight (R := R)
        (A := (⊥ : Ideal R).ResidueField) (B := A)).toRingHom, Ideal.comap_isPrime _ _⟩ :
      PrimeSpectrum A) ∈ Algebra.smoothLocus R A := by
  have : IsNoetherianRing ((⊥ : Ideal R).ResidueField ⊗[R] A) :=
    Algebra.FiniteType.isNoetherianRing (⊥ : Ideal R).ResidueField _
  exact comap_mem_smoothLocus_of_isRegularLocalRing P
    (((isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth
      (R := (⊥ : Ideal R).ResidueField ⊗[R] A)).mp hN).1 P hP)

end Smooth

/-! ### Localizing the base -/

section LocalizeBase

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- For an algebra `Q` over `R_f`, the base change of `A_f` along `R_f → Q` is the base change of
`A` along `R → Q`. -/
private theorem exists_tensor_localization_algEquiv (f : R) (Q : Type*) [CommRing Q]
    [Algebra R Q] [Algebra (Localization.Away f) Q] [IsScalarTower R (Localization.Away f) Q] :
    ∃ e : Q ⊗[Localization.Away f] Localization (Algebra.algebraMapSubmonoid A
        (Submonoid.powers f)) ≃ₐ[Q] Q ⊗[R] A,
      ∀ a : A, e (1 ⊗ₜ algebraMap A _ a) = 1 ⊗ₜ a := by
  set R' := Localization.Away f
  set Sf := Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))
  let : Algebra A (R' ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers f)) (R' ⊗[R] A) :=
    IsLocalization.tensorRight R' (Submonoid.powers f)
  let e1 : Sf ≃ₐ[A] R' ⊗[R] A :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid A (Submonoid.powers f)) Sf (R' ⊗[R] A)
  have hcomm : ∀ r : R', e1 (algebraMap R' Sf r) = algebraMap R' (R' ⊗[R] A) r := by
    have : (e1 : Sf →+* R' ⊗[R] A).comp (algebraMap R' Sf) = algebraMap R' (R' ⊗[R] A) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f)
      ext r
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A Sf,
        AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
      simp [Algebra.algebraMap_eq_smul_one]
    exact fun r => congrArg (fun φ : R' →+* R' ⊗[R] A => φ r) this
  let e2 : Sf ≃ₐ[R'] R' ⊗[R] A := AlgEquiv.ofRingEquiv (f := e1.toRingEquiv) hcomm
  refine ⟨(Algebra.TensorProduct.congr AlgEquiv.refl e2).trans
    (Algebra.TensorProduct.cancelBaseChange R R' Q Q A), fun a => ?_⟩
  have : e2 (algebraMap A Sf a) = 1 ⊗ₜ a := by
    change e1 (algebraMap A Sf a) = 1 ⊗ₜ a
    rw [AlgEquiv.commutes]
    rfl
  change (Algebra.TensorProduct.cancelBaseChange R R' Q Q A) (1 ⊗ₜ e2 (algebraMap A Sf a)) = _
  rw [this, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

/-- **Generic flatness for an algebra and two of its quotients.** For a domain `R`, a finite type
`R`-algebra `A` and ideals `I₁, I₂ ⊆ A`, there is `f ≠ 0` in `R` such that `A_f`, `A_f / I₁ A_f`
and `A_f / I₂ A_f` are flat over `R_f`. -/
private theorem exists_ne_zero_flat_localization [IsDomain R] [Algebra.FiniteType R A]
    (I₁ I₂ : Ideal A) :
    ∃ f : R, f ≠ 0 ∧
      Module.Flat (Localization.Away f)
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))) ∧
      Module.Flat (Localization.Away f)
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f)) ⧸
          I₁.map (algebraMap A
            (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))))) ∧
      Module.Flat (Localization.Away f)
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f)) ⧸
          I₂.map (algebraMap A
            (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))))) := by
  obtain ⟨U, hUo, hUd, hU⟩ :=
    Algebra.exists_isOpen_dense_isFinitePresentationFreeAway (R := R) (S := A)
      (M := (A ⧸ I₁) × (A ⧸ I₂))
  have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ U := by
    rw [(MMP.Threefold.Bridges.isGenericPoint_bot_primeSpectrum (R := R)).mem_open_set_iff hUo,
      Set.univ_inter]
    exact hUd.nonempty
  obtain ⟨f, hf, -, -, -, h3, h4⟩ := hU _ hη
  set R' := Localization.Away f
  set Sf := Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))
  refine ⟨f, fun h => hf (by simp [h]), inferInstance, ?_⟩
  have hflat : Module.Flat R' (Sf ⊗[A] ((A ⧸ I₁) × (A ⧸ I₂))) := Module.Flat.of_free
  have hprod : Module.Flat R' ((Sf ⊗[A] (A ⧸ I₁)) × (Sf ⊗[A] (A ⧸ I₂))) :=
    Module.Flat.of_linearEquiv
      ((TensorProduct.prodRight A Sf Sf (A ⧸ I₁) (A ⧸ I₂)).restrictScalars R').symm
  have h1 : Module.Flat R' (Sf ⊗[A] (A ⧸ I₁)) :=
    Module.Flat.of_retract (LinearMap.inl R' (Sf ⊗[A] (A ⧸ I₁)) (Sf ⊗[A] (A ⧸ I₂)))
      (LinearMap.fst R' _ _) (by ext; simp)
  have h2 : Module.Flat R' (Sf ⊗[A] (A ⧸ I₂)) :=
    Module.Flat.of_retract (LinearMap.inr R' (Sf ⊗[A] (A ⧸ I₁)) (Sf ⊗[A] (A ⧸ I₂)))
      (LinearMap.snd R' _ _) (by ext; simp)
  exact ⟨Module.Flat.of_linearEquiv
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot Sf I₁).toLinearEquiv.restrictScalars R'),
    Module.Flat.of_linearEquiv
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot Sf I₂).toLinearEquiv.restrictScalars R')⟩

/-- An `R_f`-algebra structure on a field into which `R` embeds is injective on `R_f`. -/
private theorem injective_algebraMap_localizationAway (f : R) (K : Type*) [Field K] [Algebra R K]
    [Algebra (Localization.Away f) K] [IsScalarTower R (Localization.Away f) K]
    (hK : Function.Injective (algebraMap R K)) :
    Function.Injective (algebraMap (Localization.Away f) K) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) z
  have h1 : algebraMap R K a = 0 := by
    rw [IsScalarTower.algebraMap_apply R (Localization.Away f) K, ← hs, map_mul, hz, zero_mul]
  have ha : a = 0 := hK (by rw [h1, map_zero])
  have hsu := IsLocalization.map_units (Localization.Away f) s
  simp only [ha, map_zero] at hs
  exact (hsu.mul_left_eq_zero).mp hs

/-- Over a prime `p` not containing `f`, the residue field `κ(p)` is an `R_f`-algebra. -/
private theorem exists_algebra_localizationAway_residueField {f : R} (p : Ideal R) [p.IsPrime]
    (hf : f ∉ p) : ∃ _ : Algebra (Localization.Away f) p.ResidueField,
      IsScalarTower R (Localization.Away f) p.ResidueField := by
  have hu : IsUnit (algebraMap R p.ResidueField f) := by
    rwa [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
  let : Algebra (Localization.Away f) p.ResidueField :=
    (IsLocalization.Away.lift f hu).toAlgebra
  exact ⟨this, IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq f hu r).symm⟩

end LocalizeBase

/-! ### Spreading reducedness on an affine chart -/

section KeyLemma

variable {R A : Type w} [CommRing R] [CommRing A] [Algebra R A]

/-- **A generic nonzerodivisor inside the smooth locus.** Let `R` be a Noetherian domain whose
fraction field `K` has characteristic zero and `A` a reduced `R`-algebra of finite type. Then
there is `a : A` with `D(a)` contained in the smooth locus of `R → A` such that `1 ⊗ a` is a
nonzerodivisor on the generic fibre `K ⊗_R A`. -/
private theorem exists_basicOpen_subset_smoothLocus_forall_mul_eq_zero [IsDomain R]
    [IsNoetherianRing R] [Algebra.FiniteType R A] [IsReduced A]
    [CharZero (⊥ : Ideal R).ResidueField] :
    ∃ a : A, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆ Algebra.smoothLocus R A ∧
      ∀ z : (⊥ : Ideal R).ResidueField ⊗[R] A, (1 ⊗ₜ a) * z = 0 → z = 0 := by
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  set K := (⊥ : Ideal R).ResidueField
  -- the ideal of the non-smooth locus
  set J := PrimeSpectrum.vanishingIdeal (Algebra.smoothLocus R A)ᶜ
  have hJ : ∀ q : PrimeSpectrum A, J ≤ q.asIdeal ↔ q ∉ Algebra.smoothLocus R A := by
    intro q
    have h := PrimeSpectrum.mem_zeroLocus q (J : Set A)
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      Algebra.isOpen_smoothLocus.isClosed_compl.closure_eq] at h
    exact h.symm
  -- the generic fibre is a reduced localization of `A`
  have : IsNoetherianRing (K ⊗[R] A) := Algebra.FiniteType.isNoetherianRing K _
  let : Algebra A (K ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (K ⊗[R] A) :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  have : IsReduced (K ⊗[R] A) := isReduced_localizationPreserves
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (K ⊗[R] A) inferInstance
  -- `J` lies in no minimal prime of the generic fibre, whose local rings are fields
  have hmin : ∀ P ∈ minimalPrimes (K ⊗[R] A), ¬ J.map (algebraMap A (K ⊗[R] A)) ≤ P := by
    intro P hP hle
    have := hP.1.1
    have : Ring.KrullDimLE 0 (Localization.AtPrime P) := .of_isLocalization _ hP _
    let : Field (Localization.AtPrime P) := Ring.KrullDimLE.isField_of_isReduced.toField
    exact (hJ _).mp (Ideal.map_le_iff_le_comap.mp hle)
      (comap_mem_smoothLocus_of_isRegularLocalRing P inferInstance)
  -- prime avoidance: a nonzerodivisor in `J`
  have hns : ¬ ((J.map (algebraMap A (K ⊗[R] A)) : Set (K ⊗[R] A)) ⊆
      ⋃ P ∈ minimalPrimes (K ⊗[R] A), (P : Set (K ⊗[R] A))) := fun hsub => by
    obtain ⟨P, hP, hle⟩ := ((J.map (algebraMap A (K ⊗[R] A))).subset_union_prime_finite
      (minimalPrimes.finite_of_isNoetherianRing _) (f := id) 0 0
      fun P hP _ _ => hP.1.1).1 (by simpa only [id] using hsub)
    exact hmin P hP hle
  obtain ⟨x, hxJ, hx⟩ := Set.not_subset.mp hns
  simp only [Set.mem_iUnion, not_exists, SetLike.mem_coe] at hx
  obtain ⟨⟨⟨a, haJ⟩, s⟩, hxa⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (K ⊗[R] A)).mp hxJ
  refine ⟨a, fun q hq => by_contra fun hsm => hq ((hJ q).mpr hsm haJ), fun z hz => ?_⟩
  refine (IsLocalization.map_units (K ⊗[R] A) s).mul_right_eq_zero.mp
    (eq_zero_of_mul_eq_zero_of_forall_notMem_minimalPrimes hx ?_)
  rwa [← mul_assoc, hxa]

/-- **Spreading out a generic nonzerodivisor.** Let `R` be a domain with fraction field `K`, `A` a
finite type `R`-algebra and `a : A` such that `1 ⊗ a` is a nonzerodivisor on `K ⊗_R A`. Then for
some `r ≠ 0`, `1 ⊗ a` is a nonzerodivisor on `L ⊗_R A` for every field `L` over `R` in which `r`
is nonzero. -/
private theorem exists_ne_zero_forall_mul_eq_zero [IsDomain R] [Algebra.FiniteType R A] (a : A)
    (ha : ∀ z : (⊥ : Ideal R).ResidueField ⊗[R] A, (1 ⊗ₜ a) * z = 0 → z = 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type w) [Field L] [Algebra R L], algebraMap R L r ≠ 0 →
      ∀ z : L ⊗[R] A, (1 ⊗ₜ a) * z = 0 → z = 0 := by
  set K := (⊥ : Ideal R).ResidueField
  -- generic flatness of `A` and `A/(a)`
  obtain ⟨f, hf0, hC, hC1, -⟩ := exists_ne_zero_flat_localization (R := R) (A := A)
    (Ideal.span {a}) (Ideal.span {a})
  set R' := Localization.Away f
  set Sf := Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))
  rw [Ideal.map_span, Set.image_singleton] at hC1
  -- `a` is a nonzerodivisor on `A_f`, detected on the generic fibre
  have hfK : IsUnit (algebraMap R K f) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
    simpa using hf0
  let : Algebra R' K := (IsLocalization.Away.lift f hfK).toAlgebra
  have : IsScalarTower R R' K :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq f hfK r).symm
  obtain ⟨eK, heK⟩ := exists_tensor_localization_algEquiv (A := A) f K
  have hSreg := mul_eq_zero_of_tensor K
    (injective_algebraMap_localizationAway f K (IsFractionRing.injective R K)) fun z hz =>
      eK.injective <| by rw [map_zero]; exact ha _ (by rw [← heK, ← map_mul, hz, map_zero])
  -- and stays one on every fibre over `D(f)`, by flatness of `A_f/(a)`
  refine ⟨f, hf0, fun L _ _ hL z hz => ?_⟩
  have hfL : IsUnit (algebraMap R L f) := hL.isUnit
  let : Algebra R' L := (IsLocalization.Away.lift f hfL).toAlgebra
  have : IsScalarTower R R' L :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq f hfL r).symm
  obtain ⟨eL, heL⟩ := exists_tensor_localization_algEquiv (A := A) f L
  apply eL.symm.injective
  rw [map_zero]
  refine one_tmul_mul_eq_zero (B := R') (C := Sf) L hSreg _ (eL.injective ?_)
  rw [map_mul, heL, AlgEquiv.apply_symm_apply, hz, map_zero]

/-- **Spreading out reducedness on an affine chart.** Let `R` be a Noetherian domain whose
fraction field has characteristic zero and `A` a reduced `R`-algebra of finite type. Then for
some `r ≠ 0` the ring `L ⊗_R A` is reduced for every field `L` over `R` in which `r` is
nonzero. -/
private theorem exists_ne_zero_forall_isReduced_tensor [IsDomain R] [IsNoetherianRing R]
    [Algebra.FiniteType R A] [IsReduced A] [CharZero (⊥ : Ideal R).ResidueField] :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type w) [Field L] [Algebra R L], algebraMap R L r ≠ 0 →
      IsReduced (L ⊗[R] A) := by
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨a, hsub, ha⟩ := exists_basicOpen_subset_smoothLocus_forall_mul_eq_zero (R := R) (A := A)
  obtain ⟨r, hr, hL⟩ := exists_ne_zero_forall_mul_eq_zero a ha
  refine ⟨r, hr, fun L _ _ hrL =>
    isReduced_of_forall_isReduced_localization (hL L hrL) fun P _ hP => ?_⟩
  have := isRegularLocalRing_of_basicOpen_subset_smoothLocus L hsub P hP
  have := IsRegularLocalRing.isDomain (Localization.AtPrime P)
  infer_instance

end KeyLemma

/-! ### Base changes of affine charts -/

section Charts

/-- An affine open `U` of a scheme of finite type over `Spec R` is the spectrum of a finite type
`R`-algebra, compatibly with the structure morphism. -/
private theorem exists_algebra_fromSpec {R : Type*} [CommRing R] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ _ : Algebra R Γ(X, U), Algebra.FiniteType R Γ(X, U) ∧
      hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  let : Algebra R Γ(X, U) := φ.hom.toAlgebra
  have hφ : Spec.map φ = hU.fromSpec ≫ f := Spec.map_preimage _
  have hft : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  exact ⟨this, HasRingHomProperty.Spec_iff.mp hft, hφ.symm⟩

/-- The base change along `g : T ⟶ S` of an affine chart `Spec Γ(X, U) → X → S` is an open
subscheme of the base change of `X`, containing every point lying over `U`. -/
private theorem exists_isOpenImmersion_chart_pullback {S X T : Scheme} (f : X ⟶ S) {U : X.Opens}
    (hU : IsAffineOpen U) (g : T ⟶ S) :
    ∃ j : pullback (hU.fromSpec ≫ f) g ⟶ pullback f g, IsOpenImmersion j ∧
      ∀ y : ↥(pullback f g), pullback.fst f g y ∈ U → ∃ y', j y' = y := by
  let e : pullback hU.fromSpec (pullback.fst f g) ≅ pullback (hU.fromSpec ≫ f) g :=
    pullbackRightPullbackFstIso f g hU.fromSpec
  let j : pullback (hU.fromSpec ≫ f) g ⟶ pullback f g := e.inv ≫ pullback.snd _ _
  have : IsOpenImmersion j := IsOpenImmersion.comp _ _
  refine ⟨j, this, fun y hy => ?_⟩
  obtain ⟨u, hu⟩ : pullback.fst f g y ∈ Set.range hU.fromSpec := by
    rwa [hU.range_fromSpec]
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := hU.fromSpec)
    (g := pullback.fst f g) u y hu
  refine ⟨e.hom z, ?_⟩
  change (e.hom ≫ e.inv ≫ pullback.snd hU.fromSpec (pullback.fst f g)) z = y
  rwa [Iso.hom_inv_id_assoc]

/-- **Reduced base changes over a principal open.** Let `R` be a Noetherian domain whose fraction
field has characteristic zero and `f : X ⟶ Spec R` quasi-compact and locally of finite type with
`X` reduced. Then for some `r ≠ 0` the base change of `f` to every field `L` over `R` in which
`r` is nonzero is reduced. -/
private theorem exists_ne_zero_forall_isReduced_pullback {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [CharZero (⊥ : Ideal R).ResidueField] {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] [Algebra R L], algebraMap R L r ≠ 0 →
      IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R L)))) := by
  have hchart : ∀ U : X.affineOpens, ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] [Algebra R L],
      algebraMap R L r ≠ 0 →
        IsReduced
          (pullback (U.2.fromSpec ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R L)))) := by
    rintro ⟨U, hU⟩
    obtain ⟨_, hft, hφ⟩ := exists_algebra_fromSpec f hU
    obtain ⟨r, hr, hr'⟩ := exists_ne_zero_forall_isReduced_tensor (R := R) (A := Γ(X, U))
    refine ⟨r, hr, fun L _ _ hL => ?_⟩
    change IsReduced (pullback (hU.fromSpec ≫ f) _)
    rw [hφ]
    have := hr' L hL
    have : _root_.IsReduced (Γ(X, U) ⊗[R] L) :=
      isReduced_of_injective (Algebra.TensorProduct.comm R Γ(X, U) L).toRingHom
        (Algebra.TensorProduct.comm R Γ(X, U) L).injective
    exact isReduced_of_isOpenImmersion (pullbackSpecIso R Γ(X, U) L).hom
  choose rU hrU0 hrU using hchart
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨W, hW, hxW, -⟩ :=
        exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)
  refine ⟨∏ U ∈ t, rU U, Finset.prod_ne_zero_iff.mpr fun U _ => hrU0 U, fun L _ _ hL => ?_⟩
  set g := Spec.map (CommRingCat.ofHom (algebraMap R L))
  have : ∀ y : ↥(pullback f g), _root_.IsReduced ((pullback f g).presheaf.stalk y) := by
    intro y
    obtain ⟨U, hUt, hyU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (pullback.fst f g y)))
    have hLU : algebraMap R L (rU U) ≠ 0 := fun h => hL (by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem rU hUt
      rw [hc, map_mul, h, zero_mul])
    have := hrU U L hLU
    obtain ⟨j, hj, hjy⟩ := exists_isOpenImmersion_chart_pullback f U.2 g
    obtain ⟨y', rfl⟩ := hjy y hyU
    have := IsOpenImmersion.instIsIsoCommRingCatStalkMap j y'
    let e := (asIso (j.stalkMap y')).commRingCatIsoToRingEquiv
    exact isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isReduced_stalk _

end Charts

/-- **Reduced fibres spread in characteristic zero.** Let `f : Y ⟶ Spec R` be of finite type,
where `Y` is reduced and `R` is a domain of finite type over a field `k` of characteristic zero.
Then there is a nonzero `r : R` such that every fibre of `f` over `D(r)` is geometrically
reduced. -/
@[mmp "lem_mmp_foundation_reduced_generic_fibres_spread_char_zero"]
public theorem exists_ne_zero_forall_geometricallyReduced_fiberToSpecResidueField
    (k : Type u) [Field k] [CharZero k]
    {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    {Y : Scheme.{u}} [IsReduced Y] (f : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ r : R, r ≠ 0 ∧ ∀ s : Spec (CommRingCat.of R), r ∉ s.asIdeal →
      GeometricallyReduced (f.fiberToSpecResidueField s) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : CharZero (⊥ : Ideal R).ResidueField := charZero_of_injective_ringHom
    (f := (algebraMap R (⊥ : Ideal R).ResidueField).comp (algebraMap k R)) (RingHom.injective _)
  obtain ⟨r, hr, hred⟩ := exists_ne_zero_forall_isReduced_pullback f
  refine ⟨r, hr, fun s hs => GeometricallyReduced.mk ?_⟩
  intro K _ y Z fst snd hpb
  set g := y ≫ (Spec (CommRingCat.of R)).fromSpecResidueField s
  have hpb' : IsPullback (fst ≫ f.fiberι s) snd f g :=
    hpb.paste_horiz (IsPullback.of_hasPullback _ _)
  let : Algebra R K := (Spec.preimage g).hom.toAlgebra
  have hg : Spec.map (CommRingCat.ofHom (algebraMap R K)) = g := Spec.map_preimage g
  have hK : algebraMap R K r ≠ 0 := by
    intro h0
    apply hs
    obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
    have hx : g x = s := by
      simp only [g, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rw [← hx, ← hg]
    exact (show algebraMap R K r ∈ x.asIdeal by rw [h0]; exact zero_mem _)
  have := hred K hK
  rw [← hg] at hpb'
  exact isReduced_of_isOpenImmersion hpb'.isoPullback.hom

section NormalFibres

open RingTheory.Sequence Pointwise

/-! ### Regular sequences of length two -/

section RegularPair

/-- Prime avoidance for associated primes: an ideal contained in no associated prime of a finite
module over a Noetherian ring contains a nonzerodivisor on it. -/
private theorem exists_mem_isSMulRegular_of_forall_not_le {B M : Type*} [CommRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M] {I : Ideal B}
    (h : ∀ q ∈ associatedPrimes B M, ¬ I ≤ q) : ∃ x ∈ I, IsSMulRegular M x := by
  have hns : ¬ ((I : Set B) ⊆ ⋃ q ∈ associatedPrimes B M, (q : Set B)) := fun hsub => by
    obtain ⟨q, hq, hle⟩ := (I.subset_union_prime_finite (associatedPrimes.finite B M) (f := id)
      0 0 fun _ hq _ _ ↦ hq.isPrime).1 (by simpa only [id] using hsub)
    exact h q hq hle
  rw [biUnion_associatedPrimes_eq_compl_regular] at hns
  obtain ⟨x, hxI, hx⟩ := Set.not_subset.mp hns
  exact ⟨x, hxI, by simpa using hx⟩

/-- The localization of `xN ⊆ N` is `x N_T ⊆ N_T`. -/
private theorem localized'_smul_top {S : Type*} [CommRing S] (T : Submonoid S) (Sₘ : Type*)
    [CommRing Sₘ] [Algebra S Sₘ] [IsLocalization T Sₘ] {N : Type*} [AddCommGroup N] [Module S N]
    {Nₘ : Type*} [AddCommGroup Nₘ] [Module S Nₘ] [Module Sₘ Nₘ] [IsScalarTower S Sₘ Nₘ]
    (g : N →ₗ[S] Nₘ) [IsLocalizedModule T g] (x : S) :
    Submodule.localized' Sₘ T g (x • (⊤ : Submodule S N))
      = (algebraMap S Sₘ x) • (⊤ : Submodule Sₘ Nₘ) := by
  rw [← Submodule.ideal_span_singleton_smul, Submodule.localized'_smul, Submodule.localized'_top,
    ← Submodule.ideal_span_singleton_smul (algebraMap S Sₘ x) ⊤]
  congr 1
  rw [Ideal.span, Submodule.localized'_span]
  simp

/-- Localization commutes with dividing by an element: `(N/xN)_T` is `N_T / x N_T`. -/
private theorem exists_isLocalizedModule_quotSMulTop {S : Type*} [CommRing S] (T : Submonoid S)
    (Sₘ : Type*) [CommRing Sₘ] [Algebra S Sₘ] [IsLocalization T Sₘ] {N : Type*} [AddCommGroup N]
    [Module S N] {Nₘ : Type*} [AddCommGroup Nₘ] [Module S Nₘ] [Module Sₘ Nₘ]
    [IsScalarTower S Sₘ Nₘ] (g : N →ₗ[S] Nₘ) [IsLocalizedModule T g] (x : S) :
    ∃ h : QuotSMulTop x N →ₗ[S] QuotSMulTop (algebraMap S Sₘ x) Nₘ, IsLocalizedModule T h :=
  ⟨((Submodule.quotEquivOfEq _ _ (localized'_smul_top T Sₘ g x)).restrictScalars S).toLinearMap ∘ₗ
      Submodule.toLocalizedQuotient' Sₘ T g (x • (⊤ : Submodule S N)),
    IsLocalizedModule.of_linearEquiv T _
      ((Submodule.quotEquivOfEq _ _ (localized'_smul_top T Sₘ g x)).restrictScalars S)⟩

/-- A regular sequence `a, b` on a ring, read elementwise. -/
private theorem isWeaklyRegular_pair_iff {B : Type*} [CommRing B] (a b : B) :
    IsWeaklyRegular B [a, b] ↔ (∀ z : B, a * z = 0 → z = 0) ∧
      ∀ z : B, b * z ∈ Ideal.span {a} → z ∈ Ideal.span {a} := by
  have hspan : (a • ⊤ : Submodule B B) = Ideal.span {a} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff]
  simp only [IsWeaklyRegular.nil, and_true]
  refine and_congr ⟨fun h z hz => h (by simpa using hz), fun h u v huv => ?_⟩
    ⟨fun h z hz => ?_, fun h u v huv => ?_⟩
  · have := h (u - v) (by simpa [mul_sub, sub_eq_zero] using huv)
    exact sub_eq_zero.mp this
  · have h0 : b • (Submodule.Quotient.mk z : QuotSMulTop a B) = b • 0 := by
      rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hspan]
      simpa using hz
    have := h h0
    rwa [Submodule.Quotient.mk_eq_zero, hspan] at this
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp only [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hspan] at huv ⊢
    exact h _ (by simpa [mul_sub] using huv)

/-- An elementwise regular pair is transported along a ring isomorphism. -/
private theorem regular_pair_map {B B' : Type*} [CommRing B] [CommRing B'] (e : B ≃+* B')
    {a b : B} (h : (∀ z : B, a * z = 0 → z = 0) ∧
      ∀ z : B, b * z ∈ Ideal.span {a} → z ∈ Ideal.span {a}) :
    (∀ z : B', e a * z = 0 → z = 0) ∧
      ∀ z : B', e b * z ∈ Ideal.span {e a} → z ∈ Ideal.span {e a} := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have := h.1 (e.symm z) (by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, hz, map_zero])
    simpa using congrArg e this
  · obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hz
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (h.2 (e.symm z)
      (Ideal.mem_span_singleton'.mpr ⟨e.symm w, by
        apply e.injective
        rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply, hw]⟩))
    exact Ideal.mem_span_singleton'.mpr ⟨e v, by rw [← map_mul, hv, e.apply_symm_apply]⟩

/-- Multiplying the two terms of an elementwise regular pair by units keeps it regular. -/
private theorem regular_pair_unit_mul {B : Type*} [CommRing B] {a b : B} (u v : Bˣ)
    (h : (∀ z : B, a * z = 0 → z = 0) ∧
      ∀ z : B, b * z ∈ Ideal.span {a} → z ∈ Ideal.span {a}) :
    (∀ z : B, (u * a) * z = 0 → z = 0) ∧
      ∀ z : B, (v * b) * z ∈ Ideal.span {u * a} → z ∈ Ideal.span {u * a} := by
  have hspan : Ideal.span {(u : B) * a} = Ideal.span {a} :=
    Ideal.span_singleton_mul_left_unit u.isUnit a
  refine ⟨fun z hz => h.1 z ?_, fun z hz => ?_⟩
  · have : (u : B) * (a * z) = 0 := by rw [← mul_assoc, hz]
    simpa using this
  · rw [hspan] at hz ⊢
    refine h.2 z ?_
    have : (↑v⁻¹ : B) * ((v * b) * z) ∈ Ideal.span {a} := Ideal.mul_mem_left _ _ hz
    simpa [← mul_assoc] using this

/-- At an associated prime `q` of a finite module `N` over a Noetherian ring, every model `N_q`
of the localization has depth zero over `B_q`. -/
private theorem depth_eq_zero_of_mem_associatedPrimes {B N Nq : Type*} [CommRing B]
    [IsNoetherianRing B] [AddCommGroup N] [Module B N] [Module.Finite B N] {q : Ideal B}
    [q.IsPrime] (hq : q ∈ associatedPrimes B N) [AddCommGroup Nq] [Module B Nq]
    [Module (Localization.AtPrime q) Nq] [IsScalarTower B (Localization.AtPrime q) Nq]
    (g : N →ₗ[B] Nq) [IsLocalizedModule q.primeCompl g] :
    Module.depth (Localization.AtPrime q) (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      Nq = 0 := by
  have hm := Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hq
  have h0 := Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes hm
  rw [ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
    inferInstance)] at h0
  rw [← Module.depth_eq_depth_of_linearEquiv _
    ((IsLocalizedModule.iso q.primeCompl g).extendScalarsOfIsLocalization q.primeCompl _)]
  exact le_antisymm (by exact_mod_cast h0) (zero_le)

/-- In a Noetherian normal ring, an ideal all of whose primes have height at least two contains a
regular sequence of length two. -/
private theorem exists_isWeaklyRegular_pair {B : Type*} [CommRing B] [IsNoetherianRing B]
    (hB : IsNormalRing B) (I : Ideal B)
    (hI : ∀ P : Ideal B, P.IsPrime → I ≤ P → 2 ≤ P.height) :
    ∃ a ∈ I, ∃ b ∈ I, IsWeaklyRegular B [a, b] := by
  have hS2 := ((isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth
    (R := B)).mp hB).2
  have hdep : ∀ (q : Ideal B) [q.IsPrime], I ≤ q → (2 : ℕ∞) ≤ Module.depth
      (Localization.AtPrime q) (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) := by
    intro q _ hq
    have h := hS2 q
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q] at h
    have h2 : (2 : WithBot ℕ∞) ≤ (q.height : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr (hI q ‹_› hq)
    rw [min_eq_left h2] at h
    exact WithBot.coe_le_coe.mp h
  obtain ⟨a, haI, ha⟩ : ∃ a ∈ I, IsSMulRegular B a := by
    refine exists_mem_isSMulRegular_of_forall_not_le fun q hq hIq => ?_
    have := hq.isPrime
    have h0 := depth_eq_zero_of_mem_associatedPrimes hq
      (Algebra.linearMap B (Localization.AtPrime q))
    have h2 := hdep q hIq
    rw [h0] at h2
    norm_num at h2
  obtain ⟨b, hbI, hb⟩ : ∃ b ∈ I, IsSMulRegular (QuotSMulTop a B) b := by
    refine exists_mem_isSMulRegular_of_forall_not_le fun q hq hIq => ?_
    have := hq.isPrime
    obtain ⟨h, _⟩ := exists_isLocalizedModule_quotSMulTop q.primeCompl (Localization.AtPrime q)
      (Algebra.linearMap B (Localization.AtPrime q)) a
    have h0 := depth_eq_zero_of_mem_associatedPrimes hq h
    have hreg : IsSMulRegular (Localization.AtPrime q) (algebraMap B _ a) :=
      IsSMulRegular.of_isLocalizedModule (Localization.AtPrime q) q.primeCompl
        (Algebra.linearMap B (Localization.AtPrime q)) ha
    have hmem : algebraMap B (Localization.AtPrime q) a ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mpr (hIq haI)
    have h1 := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append _
      (Localization.AtPrime q)).1 _ hmem hreg
    rw [h0, zero_add] at h1
    have h2 := hdep q hIq
    rw [← h1] at h2
    norm_num at h2
  refine ⟨a, haI, b, hbI, ?_⟩
  rw [isWeaklyRegular_cons_iff]
  exact ⟨ha, (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hb, IsWeaklyRegular.nil _ _⟩⟩

/-- A regular sequence `a, b` inside a prime `P` makes the depth of `B_P` at least two. -/
private theorem two_le_depth_localization_atPrime {B : Type*} [CommRing B] {a b : B}
    (hab : IsWeaklyRegular B [a, b]) (P : Ideal B) [P.IsPrime] (ha : a ∈ P) (hb : b ∈ P) :
    (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) := by
  have h := hab.of_isLocalizedModule (Localization.AtPrime P) P.primeCompl
    (Algebra.linearMap B (Localization.AtPrime P))
  have hmem : ∀ r ∈ [a, b].map (algebraMap B (Localization.AtPrime P)),
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr ha
    · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr hb
  simpa using Stacks.Depth.ModNonzerodivisor.length_le_depth_of_isWeaklyRegular _ hmem h

/-- **Serre's criterion with a regular pair.** Let `B` be Noetherian and `J` an ideal containing a
regular sequence `a, b`. If `B_P` is regular for every prime `P` not containing `J`, then `B` is
a normal ring. -/
private theorem isNormalRing_of_isWeaklyRegular_pair {B : Type*} [CommRing B] [IsNoetherianRing B]
    (J : Ideal B) {a b : B} (ha : a ∈ J) (hb : b ∈ J) (hab : IsWeaklyRegular B [a, b])
    (hreg : ∀ P : Ideal B, [P.IsPrime] → ¬ J ≤ P → IsRegularLocalRing (Localization.AtPrime P)) :
    IsNormalRing B := by
  have key : ∀ (P : Ideal B) [P.IsPrime], J ≤ P → (2 : ℕ∞) ≤ Module.depth
      (Localization.AtPrime P) (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P) := fun P _ h =>
    two_le_depth_localization_atPrime hab P (h ha) (h hb)
  refine (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth
    (R := B)).mpr ⟨fun P _ hP => ?_, fun P _ => ?_⟩
  · by_cases hJ : J ≤ P
    · exfalso
      have h2 := Module.depth_le_ringKrullDim (Localization.AtPrime P)
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P] at h2
      have h3 : (2 : ℕ∞) ≤ P.height := (key P hJ).trans (WithBot.coe_le_coe.mp h2)
      have h4 := h3.trans hP
      norm_num at h4
    · exact hreg P hJ
  · by_cases hJ : J ≤ P
    · exact (min_le_left _ _).trans (WithBot.coe_le_coe.mpr (key P hJ))
    · have := hreg P hJ
      rw [depth_eq_ringKrullDim_of_isRegularLocalRing]
      exact min_le_right _ _

end RegularPair

/-! ### Spreading normality on an affine chart -/

section KeyLemma

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Spreading out normality on an affine chart.** Let `R` be a Noetherian domain all of whose
residue fields have characteristic zero and `A` a finite type `R`-algebra whose generic fibre
`κ(⊥) ⊗_R A` is normal. Then for some `r ≠ 0` every fibre `κ(p) ⊗_R A`, `r ∉ p`, is normal. -/
private theorem exists_ne_zero_forall_isNormalRing_fiber [IsDomain R] [IsNoetherianRing R]
    [Algebra.FiniteType R A] (hchar : ∀ (p : Ideal R) [p.IsPrime], CharZero p.ResidueField)
    (hN : IsNormalRing ((⊥ : Ideal R).ResidueField ⊗[R] A)) :
    ∃ r : R, r ≠ 0 ∧ ∀ (p : Ideal R) [p.IsPrime], r ∉ p →
      IsNormalRing (p.ResidueField ⊗[R] A) := by
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  set K := (⊥ : Ideal R).ResidueField
  have := hchar ⊥
  -- the ideal of the non-smooth locus
  set J := PrimeSpectrum.vanishingIdeal (Algebra.smoothLocus R A)ᶜ
  have hJ : ∀ q : PrimeSpectrum A, J ≤ q.asIdeal ↔ q ∉ Algebra.smoothLocus R A := by
    intro q
    have h := PrimeSpectrum.mem_zeroLocus q (J : Set A)
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      Algebra.isOpen_smoothLocus.isClosed_compl.closure_eq] at h
    exact h.symm
  -- a regular pair in `J` on the generic fibre
  have : IsNoetherianRing (K ⊗[R] A) := Algebra.FiniteType.isNoetherianRing K _
  let : Algebra A (K ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (K ⊗[R] A) :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  have hI : ∀ P : Ideal (K ⊗[R] A), P.IsPrime → J.map (algebraMap A (K ⊗[R] A)) ≤ P →
      2 ≤ P.height := by
    intro P _ hP
    by_contra hlt
    have h1 : P.height ≤ 1 := Order.le_of_lt_succ (lt_of_not_ge hlt)
    exact (hJ _).mp (Ideal.map_le_iff_le_comap.mp hP)
      (comap_mem_smoothLocus_of_height_le_one hN P h1)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_isWeaklyRegular_pair hN _ hI
  rw [isWeaklyRegular_pair_iff] at hab
  obtain ⟨⟨x, s⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (K ⊗[R] A)).mp ha
  obtain ⟨⟨y, t⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (K ⊗[R] A)).mp hb
  have hu := IsLocalization.map_units (K ⊗[R] A) s
  have hv := IsLocalization.map_units (K ⊗[R] A) t
  have hgen := regular_pair_unit_mul hu.unit hv.unit hab
  rw [IsUnit.unit_spec, mul_comm, hx, IsUnit.unit_spec, mul_comm, hy] at hgen
  -- `hgen` is the regular pair `1 ⊗ x, 1 ⊗ y` on the generic fibre; spread it by generic flatness
  obtain ⟨f, hf0, hC, hC1, hC2⟩ := exists_ne_zero_flat_localization (R := R) (A := A)
    (Ideal.span {(x : A)}) (Ideal.span {(x : A), (y : A)})
  set R' := Localization.Away f
  set Sf := Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers f))
  rw [Ideal.map_span, Set.image_singleton] at hC1
  rw [Ideal.map_span, Set.image_pair] at hC2
  obtain ⟨instK, hK⟩ := exists_algebra_localizationAway_residueField (f := f) (⊥ : Ideal R)
    (by simpa using hf0)
  let := instK
  have hKinj : Function.Injective (algebraMap R' K) :=
    injective_algebraMap_localizationAway f K
      (IsFractionRing.injective R K)
  obtain ⟨eK, heK⟩ := exists_tensor_localization_algEquiv (A := A) f K
  have hgen' := regular_pair_map eK.symm.toRingEquiv hgen
  have hsymm : ∀ z : A, eK.symm.toRingEquiv (algebraMap A (K ⊗[R] A) z) =
      1 ⊗ₜ algebraMap A Sf z := fun z => by
    change eK.symm (1 ⊗ₜ z) = _
    rw [AlgEquiv.symm_apply_eq, heK]
  rw [hsymm, hsymm] at hgen'
  have hCreg := regular_pair_of_tensor K hKinj hgen'.1 hgen'.2
  refine ⟨f, hf0, fun p _ hfp => ?_⟩
  obtain ⟨instp, hp⟩ := exists_algebra_localizationAway_residueField p hfp
  let := instp
  have hfib := regular_pair_tensor (B := R') (C := Sf) p.ResidueField hCreg.1 hCreg.2
  obtain ⟨ep, hep⟩ := exists_tensor_localization_algEquiv (A := A) f p.ResidueField
  have hfib' := regular_pair_map ep.toRingEquiv hfib
  rw [show ep.toRingEquiv (1 ⊗ₜ algebraMap A Sf x) = 1 ⊗ₜ (x : A) from hep x,
    show ep.toRingEquiv (1 ⊗ₜ algebraMap A Sf y) = 1 ⊗ₜ (y : A) from hep y] at hfib'
  have : IsNoetherianRing (p.ResidueField ⊗[R] A) :=
    Algebra.FiniteType.isNoetherianRing p.ResidueField _
  let ι := (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) (B := A)).toRingHom
  refine isNormalRing_of_isWeaklyRegular_pair (J.map ι) (Ideal.mem_map_of_mem ι x.2)
    (Ideal.mem_map_of_mem ι y.2) ((isWeaklyRegular_pair_iff _ _).mpr hfib') ?_
  intro P _ hP
  have hnot : ¬ J ≤ P.comap ι := fun h => hP (Ideal.map_le_iff_le_comap.mpr h)
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.mp hnot
  refine isRegularLocalRing_of_basicOpen_subset_smoothLocus _ ?_ P hgP
  intro q hq
  by_contra hsm
  exact hq ((hJ q).mpr hsm hgJ)

end KeyLemma

/-! ### Fibres of affine charts -/

section Charts

/-- The fibre of `Spec B → Spec R` over `s` is normal exactly when the fibre ring `κ(s) ⊗_R B`
is a normal ring. -/
private theorem isNormal_fiber_spec_iff (R B : Type w) [CommRing R] [CommRing B] [Algebra R B]
    (s : PrimeSpectrum R) :
    IsNormal ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiber s) ↔
      IsNormalRing (s.asIdeal.Fiber B) := by
  let e : (Spec.map (CommRingCat.ofHom (algebraMap R B))).fiber s ≅
      Spec (CommRingCat.of (s.asIdeal.Fiber B)) :=
    Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R B s)
  constructor
  · intro h
    have : IsNormal (Spec (CommRingCat.of (s.asIdeal.Fiber B))) := isNormal_of_isOpenImmersion e.inv
    exact isNormalRing_of_isNormal_spec this
  · intro h
    have := isNormal_spec_of_isNormalRing h
    exact isNormal_of_isOpenImmersion e.hom

/-- The fibre of an affine chart `Spec Γ(X, U) → X → S` over `s` is an open subscheme of the
fibre of `X` over `s`, containing every point of that fibre which lies in `U`. -/
private theorem exists_isOpenImmersion_chart_fiber {S X : Scheme} (f : X ⟶ S) {U : X.Opens}
    (hU : IsAffineOpen U) (s : S) :
    ∃ j : (hU.fromSpec ≫ f).fiber s ⟶ f.fiber s, IsOpenImmersion j ∧
      ∀ y : f.fiber s, f.fiberι s y ∈ U → ∃ y', j y' = y :=
  exists_isOpenImmersion_chart_pullback f hU (S.fromSpecResidueField s)

/-- **Normal fibres over a principal open.** Let `R` be a Noetherian domain whose residue fields
have characteristic zero and `f : X ⟶ Spec R` quasi-compact and locally of finite type with normal
generic fibre. Then for some `r ≠ 0` every fibre of `f` over `D(r)` is normal. -/
private theorem exists_ne_zero_forall_isNormal_fiber {R : Type w} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (hchar : ∀ (p : Ideal R) [p.IsPrime], CharZero p.ResidueField)
    {X : Scheme.{w}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hF : IsNormal (f.fiber ⟨⊥, Ideal.isPrime_bot⟩)) :
    ∃ r : R, r ≠ 0 ∧ ∀ s : Spec (CommRingCat.of R), r ∉ s.asIdeal → IsNormal (f.fiber s) := by
  have hchart : ∀ U : X.affineOpens, ∃ r : R, r ≠ 0 ∧ ∀ s : Spec (CommRingCat.of R),
      r ∉ s.asIdeal → IsNormal ((U.2.fromSpec ≫ f).fiber s) := by
    rintro ⟨U, hU⟩
    obtain ⟨_, hft, hφ⟩ := exists_algebra_fromSpec f hU
    obtain ⟨j, hj, -⟩ := exists_isOpenImmersion_chart_fiber f hU ⟨⊥, Ideal.isPrime_bot⟩
    have hgen : IsNormal ((hU.fromSpec ≫ f).fiber ⟨⊥, Ideal.isPrime_bot⟩) :=
      isNormal_of_isOpenImmersion j
    change ∃ r : R, r ≠ 0 ∧ ∀ s : Spec (CommRingCat.of R),
      r ∉ s.asIdeal → IsNormal ((hU.fromSpec ≫ f).fiber s)
    rw [hφ] at hgen ⊢
    have hN := (isNormal_fiber_spec_iff R Γ(X, U) ⟨⊥, Ideal.isPrime_bot⟩).mp hgen
    obtain ⟨r, hr, hr'⟩ := exists_ne_zero_forall_isNormalRing_fiber hchar hN
    exact ⟨r, hr, fun s hs => (isNormal_fiber_spec_iff R Γ(X, U) s).mpr
      (@hr' s.asIdeal s.isPrime hs)⟩
  choose rU hrU0 hrU using hchart
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨W, hW, hxW, -⟩ :=
        exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)
  refine ⟨∏ U ∈ t, rU U, Finset.prod_ne_zero_iff.mpr fun U _ => hrU0 U, fun s hs => ?_⟩
  refine (isNormal_iff_stalk_isNormalRing _).mpr fun y => ?_
  obtain ⟨U, hUt, hyU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (f.fiberι s y)))
  have hsU : rU U ∉ s.asIdeal := fun h => hs (by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem rU hUt
    rw [hc]
    exact Ideal.mul_mem_right _ _ h)
  have := hrU U s hsU
  obtain ⟨j, hj, hjy⟩ := exists_isOpenImmersion_chart_fiber f U.2 s
  obtain ⟨y', rfl⟩ := hjy y hyU
  have := hj
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap j y'
  have h := (isNormal_iff_stalk_isNormalRing _).mp ‹_› y'
  exact IsNormalRing.congr (asIso (j.stalkMap y')).commRingCatIsoToRingEquiv.symm h

end Charts

/-! ### Purity of the fibres -/

section Purity

/-- On a scheme locally of finite type over a field and pure of dimension `d`, the local
dimension at every point is `d`. -/
private theorem topologicalKrullDimAt_eq_of_isPureDimensional {k : Type w} [Field k]
    {T : Scheme.{w}} (g : T ⟶ Spec (CommRingCat.of k)) (hg : LocallyOfFiniteType g) {d : ℕ}
    (hT : MMP.Intersection.IsPureDimensional T d) (t : T) :
    topologicalKrullDimAt T t = d := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k T g t]
  obtain ⟨C, hC, htC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {t} isIrreducible_singleton
  exact le_antisymm (iSup₂_le fun Z hZ => (hT Z hZ.1).le)
    (le_iSup₂_of_le C ⟨hC, htC rfl⟩ (hT C hC).ge)

/-- On a scheme locally of finite type over a field, the local dimension at the generic point of
an irreducible component is the dimension of that component, no other component containing it. -/
private theorem topologicalKrullDimAt_genericPoint_eq {k : Type w} [Field k] {T : Scheme.{w}}
    (g : T ⟶ Spec (CommRingCat.of k)) (hg : LocallyOfFiniteType g) {W : Set T}
    (hW : W ∈ irreducibleComponents T) :
    topologicalKrullDimAt T hW.1.genericPoint = topologicalKrullDim W := by
  have hηW : IsGenericPoint hW.1.genericPoint W :=
    hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  have honly : ∀ V ∈ irreducibleComponents T, hW.1.genericPoint ∈ V → V = W := by
    intro V hV hηV
    have hWV : W ⊆ V := hηW ▸ closure_minimal (Set.singleton_subset_iff.mpr hηV)
      (isClosed_of_mem_irreducibleComponents V hV)
    exact (hWV.antisymm (hW.2 hV.1 hWV)).symm
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k T g hW.1.genericPoint]
  refine le_antisymm (iSup_le fun V ↦ iSup_le fun hV ↦ by rw [honly V hV.1 hV.2]) ?_
  exact le_iSup_of_le W (le_iSup_of_le ⟨hW, hηW.mem⟩ le_rfl)

/-- An irreducible component of a scheme over `Spec R`, `R` a domain, either dominates `Spec R`
or lies over `V(r)` for some `r ≠ 0`. -/
private theorem exists_ne_zero_map_genericPoint_eq {R : Type w} [CommRing R] [IsDomain R]
    {X : Scheme.{w}} (f : X ⟶ Spec (CommRingCat.of R)) {C : Set X}
    (hC : C ∈ irreducibleComponents X) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ C, r ∉ (f x).asIdeal →
      f hC.1.genericPoint = ⟨⊥, Ideal.isPrime_bot⟩ := by
  by_cases h : f hC.1.genericPoint = ⟨⊥, Ideal.isPrime_bot⟩
  · exact ⟨1, one_ne_zero, fun _ _ _ => h⟩
  · have hne : (f hC.1.genericPoint).asIdeal ≠ ⊥ := fun h' => h (PrimeSpectrum.ext h')
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨r, hr0, fun x hx hrx => absurd ?_ hrx⟩
    have hsp : hC.1.genericPoint ⤳ x :=
      (hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)).specializes hx
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr (hsp.map f.continuous) hr

/-- A point of the fibre over `s` maps to `s`. -/
private theorem apply_fiberι_eq {X Y : Scheme} (f : X ⟶ Y) (s : Y) (y : f.fiber s) :
    f (f.fiberι s y) = s := by
  have : f.fiberι s y ∈ f ⁻¹' {s} := by rw [← Scheme.Hom.range_fiberι]; exact ⟨y, rfl⟩
  exact this

/-- **Pure fibres over a principal open.** For `f : X ⟶ Spec R` quasi-compact and locally of
finite type over a Noetherian domain there is `r ≠ 0` such that, whenever the generic fibre is
pure of dimension `d`, so is every nonempty fibre over `D(r)`. -/
private theorem exists_ne_zero_forall_isPureDimensional_fiber {R : Type w} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] {X : Scheme.{w}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ r : R, r ≠ 0 ∧ ∀ s : Spec (CommRingCat.of R), r ∉ s.asIdeal → ∀ d : ℕ,
      MMP.Intersection.IsPureDimensional (f.fiber ⟨⊥, Ideal.isPrime_bot⟩) d →
        Nonempty (f.fiber s) → MMP.Intersection.IsPureDimensional (f.fiber s) d := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  by_cases hE : IsEmpty (f.fiber ⟨⊥, Ideal.isPrime_bot⟩)
  · have hηr : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∉ Set.range f := by
      rintro ⟨x, hx⟩
      obtain ⟨y, -⟩ : x ∈ Set.range (f.fiberι ⟨⊥, Ideal.isPrime_bot⟩) :=
        (Set.ext_iff.mp (Scheme.Hom.range_fiberι f _) x).mpr hx
      exact hE.false y
    obtain ⟨r, hr, hr'⟩ := MMP.Threefold.Bridges.exists_ne_zero_forall_mem_of_not_mem_range f hηr
    refine ⟨r, hr, fun s hs d _ ⟨y⟩ => absurd ?_ hs⟩
    have := hr' (f.fiberι s y)
    rwa [apply_fiberι_eq] at this
  rw [not_isEmpty_iff] at hE
  obtain ⟨w₀⟩ := hE
  have hlη := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f ⟨⊥, Ideal.isPrime_bot⟩
  have hcompfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  choose! rC hrC0 hrC using fun (C : Set X) (hC : C ∈ irreducibleComponents X) =>
    exists_ne_zero_map_genericPoint_eq f hC
  have hrcomp0 : ∏ C ∈ hcompfin.toFinset, rC C ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun C hC => hrC0 C (hcompfin.mem_toFinset.mp hC)
  have hdim : ∃ rd : R, rd ≠ 0 ∧ ∀ d : ℕ,
      MMP.Intersection.IsPureDimensional (f.fiber ⟨⊥, Ideal.isPrime_bot⟩) d →
        ∀ s : Spec (CommRingCat.of R), rd ∉ s.asIdeal → f.fiberDimension s ≤ d := by
    by_cases hP : ∃ d : ℕ, MMP.Intersection.IsPureDimensional (f.fiber ⟨⊥, Ideal.isPrime_bot⟩) d
    · obtain ⟨d₀, hd₀⟩ := hP
      have hloc := topologicalKrullDimAt_eq_of_isPureDimensional
        (f.fiberToSpecResidueField ⟨⊥, Ideal.isPrime_bot⟩) hlη hd₀
      have hle : topologicalKrullDim (Limits.pullback (C := Scheme.{w}) f
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) ≤ d₀ := by
        rw [MMP.Threefold.Bridges.topologicalKrullDim_pullback_eq_fiberDimension]
        change topologicalKrullDim (f.fiber ⟨⊥, Ideal.isPrime_bot⟩) ≤ _
        rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
        exact iSup_le fun t => by
          rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hloc t]
      obtain ⟨rd, hrd, hrd'⟩ :=
        MMP.Threefold.Bridges.exists_forall_fiberDimension_le_of_genericFibre (FractionRing R) f
          d₀ hle
      refine ⟨rd, hrd, fun d hd s hs => ?_⟩
      have : (d : WithBot ℕ∞) = d₀ := by
        rw [← topologicalKrullDimAt_eq_of_isPureDimensional
          (f.fiberToSpecResidueField ⟨⊥, Ideal.isPrime_bot⟩) hlη hd w₀, hloc w₀]
      rw [this]
      exact hrd' s hs
    · exact ⟨1, one_ne_zero, fun d hd => absurd ⟨d, hd⟩ hP⟩
  obtain ⟨rd, hrd0, hrd⟩ := hdim
  refine ⟨(∏ C ∈ hcompfin.toFinset, rC C) * rd, mul_ne_zero hrcomp0 hrd0,
    fun s hs d hd _ => ?_⟩
  have hs1 : ∏ C ∈ hcompfin.toFinset, rC C ∉ s.asIdeal := fun h => hs (Ideal.mul_mem_right _ _ h)
  have hs2 : rd ∉ s.asIdeal := fun h => hs (Ideal.mul_mem_left _ _ h)
  have hls := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f s
  intro Z hZ
  rw [← topologicalKrullDimAt_genericPoint_eq (f.fiberToSpecResidueField s) hls hZ]
  refine le_antisymm
    ((_root_.topologicalKrullDimAt_le_topologicalKrullDim hZ.1.genericPoint).trans
      (hrd d hd s hs2)) ?_
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    {f.fiberι s hZ.1.genericPoint} isIrreducible_singleton
  have hdom : f hC.1.genericPoint = ⟨⊥, Ideal.isPrime_bot⟩ :=
    hrC C hC _ (hxC rfl) (by
      rw [apply_fiberι_eq]
      intro h
      apply hs1
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem rC (hcompfin.mem_toFinset.mpr hC)
      rw [hc]
      exact Ideal.mul_mem_right _ _ h)
  have hsp : hC.1.genericPoint ⤳ f.fiberι s hZ.1.genericPoint :=
    (hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)).specializes
      (hxC rfl)
  have key := AlgebraicGeometry.fiberDimensionAt_le_of_specializes f hsp
  rw [Scheme.Hom.topologicalKrullDimAt_fiber_fiberι f s] at key
  obtain ⟨w, hw⟩ : hC.1.genericPoint ∈ Set.range (f.fiberι ⟨⊥, Ideal.isPrime_bot⟩) :=
    (Set.ext_iff.mp (Scheme.Hom.range_fiberι f _) _).mpr hdom
  rw [← hw, Scheme.Hom.topologicalKrullDimAt_fiber_fiberι f _ w,
    topologicalKrullDimAt_eq_of_isPureDimensional
      (f.fiberToSpecResidueField ⟨⊥, Ideal.isPrime_bot⟩) hlη hd w] at key
  exact key

end Purity

/-! ### Geometric normality and the theorem -/

section Main

/-- Over a perfect field, a normal scheme is geometrically normal: every base change to a field
extension is normal. -/
private theorem geometrically_isNormal_of_isNormal {k : Type w} [Field k] [PerfectField k]
    {Y : Scheme.{w}} (g : Y ⟶ Spec (CommRingCat.of k)) [IsNormal Y] :
    geometrically IsNormal g := by
  intro K _ y Z fst snd hpb
  let : Algebra k K := (Spec.preimage y).hom.toAlgebra
  have hy : Spec.map (CommRingCat.ofHom (algebraMap k K)) = y := Spec.map_preimage y
  rw [← hy] at hpb
  have : IsNormal (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    (isNormal_iff_stalk_isNormalRing _).mpr fun x' =>
      isGeometricallyNormal_of_isNormal_of_perfectField k g
        (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) x') K x' rfl
  exact isNormal_of_isOpenImmersion hpb.isoPullback.hom

end Main

/-- **Normal generic fibres spread in characteristic zero.** Let `f : X ⟶ Spec R` be of finite
type, where `R` is a domain of finite type over a field `k₀` of characteristic zero. If the
generic fibre of `f` is normal, there is a nonzero `r : R` such that over `D(r)` every fibre of
`f` is geometrically normal, and, if the generic fibre is pure of dimension `d`, every
nonempty such fibre is pure of dimension `d`. -/
@[mmp "thm_mmp_generic_normal_fibres"]
public theorem exists_ne_zero_forall_geometrically_isNormal_fiber
    (k₀ : Type u) [Field k₀] [CharZero k₀]
    {R : Type u} [CommRing R] [IsDomain R] [Algebra k₀ R] [Algebra.FiniteType k₀ R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hF : IsNormal (f.fiber (genericPoint (Spec (CommRingCat.of R))))) :
    ∃ r : R, r ≠ 0 ∧ ∀ s : Spec (CommRingCat.of R), r ∉ s.asIdeal →
      geometrically IsNormal (f.fiberToSpecResidueField s) ∧
      ∀ d : ℕ, MMP.Intersection.IsPureDimensional
          (f.fiber (genericPoint (Spec (CommRingCat.of R)))) d →
        Nonempty (f.fiber s) → MMP.Intersection.IsPureDimensional (f.fiber s) d := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k₀ R
  rw [genericPoint_eq_bot_of_affine (CommRingCat.of R)] at hF ⊢
  have hchar : ∀ (p : Ideal R) [p.IsPrime], CharZero p.ResidueField := fun p _ =>
    charZero_of_injective_ringHom
      (f := (algebraMap R p.ResidueField).comp (algebraMap k₀ R)) (RingHom.injective _)
  obtain ⟨r₁, hr₁, hN⟩ := exists_ne_zero_forall_isNormal_fiber hchar f hF
  obtain ⟨r₂, hr₂, hP⟩ := exists_ne_zero_forall_isPureDimensional_fiber f
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun s hs =>
    ⟨?_, hP s (fun h => hs (Ideal.mul_mem_left _ _ h))⟩⟩
  have := hN s (fun h => hs (Ideal.mul_mem_right _ _ h))
  have := s.isPrime
  have : CharZero ((Spec (CommRingCat.of R)).residueField s) :=
    charZero_of_injective_ringHom
      (f := (Scheme.Spec.residueFieldIso (CommRingCat.of R) s).inv.hom.comp
        ((algebraMap R s.asIdeal.ResidueField).comp (algebraMap k₀ R))) (RingHom.injective _)
  have : PerfectField ((Spec (CommRingCat.of R)).residueField s) := PerfectField.ofCharZero
  exact geometrically_isNormal_of_isNormal (k := (Spec (CommRingCat.of R)).residueField s)
    (f.fiberToSpecResidueField s)

end NormalFibres

end MMP

end
