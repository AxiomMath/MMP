module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.MMP.Steps
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Positivity.RelativelyAmplePullbackIso
import MMP.AlgebraicGeometry.Cohomology.Duality.AdjunctionSequence
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Divisor.Principal
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve

/-!
# Flips are isomorphisms off the flipping locus

Let `φ : X ⟶ Z` be a small contraction of normal varieties, `E` a `ℚ`-Cartier `ℚ`-divisor on `X`
with `-E` `φ`-ample, and `φ⁺ : X⁺ ⟶ Z` a flip of `φ` with respect to `E`, with birational map
`g : X ⤏ X⁺` over `Z`. Over an open `U ⊆ Z` disjoint from `φ(Ex φ)` the contraction `φ` is an
isomorphism. The flip `g` maps the prime divisors of `X` bijectively onto those of `X⁺`,
compatibly with the valuations of `K(Z)`, so local equations of a Cartier multiple `C = mE` read
in `K(Z)` are local equations of `g_* C`; clearing denominators, a `φ⁺`-ample Cartier divisor is
principal over small affine opens of `U`, so `φ⁺ ∣_ U` is affine, hence finite, hence an
isomorphism. Hence `φ⁺` is an isomorphism over `Z ∖ φ(Ex φ)`, and if `φ` is not an
isomorphism then `φ⁺` has a flipped curve.

For a morphism `f` write `Ex(f)` for the points of the source lying on a positive-dimensional
irreducible component of their fibre. For a proper birational morphism onto a normal variety,
`Ex(f)` is closed and a union of fibres, and `f` is an isomorphism off `f(Ex f)`. In a sequence
of log flips, the contraction `φ_i : X_i ⟶ Z_i` and its flip `φ_i⁺` satisfy
`φ_i⁺(Ex φ_i⁺) = φ_i(Ex φ_i)`, and the flip map `θ_i` restricts to an isomorphism
`X_i ∖ Ex φ_i ≅ X_{i+1} ∖ Ex φ_i⁺` over `Z_i ∖ φ_i(Ex φ_i)`.

## Main results

* `MMP.Flips.IsFlip.isIso_morphismRestrict_of_disjoint_image_exceptionalSet`
* `MMP.Flips.IsFlip.exists_isFlippedCurveOf_of_not_isIso`
* `MMP.Mori.isClosed_and_preimage_image_exceptionalLocus_eq`
* `MMP.Mori.isIso_morphismRestrict_compl_image_exceptionalLocus`: a proper birational morphism
  onto a normal variety is an isomorphism off the image of its exceptional locus.
* `MMP.Flips.SequenceOfLogFlips.image_exceptionalLocus_flip_eq`
* `MMP.Flips.SequenceOfLogFlips.exists_iso_compl_exceptionalLocus_flipMap`

## Implementation notes

The fibre `f⁻¹(f y)` is the subspace `f ⁻¹' {f y}` of the source, homeomorphic to the
underlying space of the scheme-theoretic fibre, and the dimension of an irreducible component is
its topological Krull dimension. A point lies on no positive-dimensional component of its fibre
exactly when `f` is quasi-finite at it, whose locus is open.

The source proves `φ(Ex φ) ⊆ φ⁺(Ex φ⁺)` by numerical triviality of `K + B` over
`Z ∖ φ⁺(Ex φ⁺)`; here the finiteness criterion used for the flip itself is applied with the roles
of `φ` and `φ⁺` exchanged, writing `g_* E` as an `ℝ`-combination of Cartier divisors.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (4.13), 4.15,
  7.1, Exercise 4.9.1
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

namespace MMP.Flips

open MMP.Mori

/-! ### Small contractions over opens of the base -/

/-- A scheme separated over a field is separated over the terminal scheme. -/
public theorem isSeparated_terminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- A contraction `φ` is an isomorphism over every open `U` disjoint from `φ(Ex φ)`: there `φ` is
proper and locally an open immersion, hence finite, and `𝒪_U ≅ φ_* 𝒪` makes it an isomorphism. -/
private theorem isIso_morphismRestrict_source_of_disjoint
    {k : Type u} [Field k] {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {φ : X ⟶ Z} (hc : IsContraction k sZ sX φ) (U : Z.Opens)
    (hU : Disjoint (U : Set Z) (φ '' MMP.Flips.exceptionalSet φ)) : IsIso (φ ∣_ U) := by
  haveI := hc.isProper
  have hV : ∀ x : φ ⁻¹ᵁ U, ∃ V : X.Opens, x.1 ∈ V ∧ IsOpenImmersion (V.ι ≫ φ) := fun x =>
    not_not.mp fun h => Set.disjoint_left.mp hU x.2 ⟨x.1, h, rfl⟩
  choose V hxV hVι using hV
  haveI : IsZariskiLocalAtSource (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  haveI : LocallyQuasiFinite (φ ∣_ U) := by
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyQuasiFinite)
      (fun x => (φ ⁻¹ᵁ U).ι ⁻¹ᵁ V x) ?_ fun x => ?_
    · exact top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ⟨y, hxV y⟩
    · haveI := hVι x
      set W := (φ ⁻¹ᵁ U).ι ⁻¹ᵁ V x
      have hr : Set.range (W.ι ≫ (φ ⁻¹ᵁ U).ι) ⊆ Set.range (V x).ι := by
        rintro _ ⟨y, rfl⟩
        exact ⟨⟨_, y.2⟩, rfl⟩
      let l := IsOpenImmersion.lift (V x).ι (W.ι ≫ (φ ⁻¹ᵁ U).ι) hr
      have hl : l ≫ (V x).ι = W.ι ≫ (φ ⁻¹ᵁ U).ι := IsOpenImmersion.lift_fac _ _ _
      haveI : LocallyQuasiFinite (l ≫ (V x).ι) := by
        rw [hl]
        infer_instance
      haveI : LocallyQuasiFinite l := LocallyQuasiFinite.of_comp l (V x).ι
      haveI : LocallyQuasiFinite ((W.ι ≫ φ ∣_ U) ≫ U.ι) := by
        rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, ← hl, Category.assoc]
        infer_instance
      exact LocallyQuasiFinite.of_comp _ U.ι
  haveI : IsFinite (φ ∣_ U) := IsFinite.of_isProper_of_locallyQuasiFinite _
  refine (IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun W : U.toScheme.affineOpens => (W : U.toScheme.Opens))
    (iSup_affineOpens_eq_top _) fun W => ?_)
  refine (isIso_morphismRestrict_iff_isIso_app (φ ∣_ U) W.2).mpr ?_
  rw [morphismRestrict_app, eqToHom_op, eqToHom_map]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hc.isIso_app _) (instIsIsoEqToHom _)

/-- A small contraction `f` is surjective, so `f⁻¹ U` is nonempty over a nonempty open `U`. -/
private theorem nonempty_preimage
    {k : Type u} [Field k] {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {f : Y ⟶ Z}
    (hs : IsSmall k sZ sY f) (U : Z.Opens) [hU : Nonempty U] :
    Nonempty (f ⁻¹ᵁ U) := by
  obtain ⟨z⟩ := hU
  obtain ⟨x, hx⟩ :=
    (hs.toIsBirationalContraction.surjective_and_isBirational).1.surj z.1
  exact ⟨⟨x, show f x ∈ U by rw [hx]; exact z.2⟩⟩

/-- Over a nonempty open `U`, the restriction `f ∣_ U` of a small contraction onto a normal
variety is a birational morphism. -/
private theorem isBirationalMorphism_morphismRestrict_of_isSmall
    {k : Type u} [Field k] {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ Z}
    (hs : IsSmall k sZ sY f) (hZ : IsNormalVariety k sZ) (U : Z.Opens) [Nonempty U] :
    IsBirationalMorphism (f ∣_ U) := by
  haveI := hZ.1.toIsIntegral
  haveI := hs.isVariety_source.toIsIntegral
  haveI := nonempty_preimage hs U
  exact MMP.Mori.isBirationalMorphism_morphismRestrict (hs.isBirationalMorphism _ _) U

/-! ### Finiteness from quasi-affine preimages -/

/-- A quasi-affine scheme which is universally closed over an affine scheme is affine. -/
private theorem isAffine_of_isQuasiAffine_of_universallyClosed {X Y : Scheme.{u}} (g : X ⟶ Y)
    [X.IsQuasiAffine] [IsAffine Y] [UniversallyClosed g] : IsAffine X := by
  have hfac : X.toSpecΓ ≫ (Spec.map g.appTop ≫ Y.isoSpec.inv) = g := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have : UniversallyClosed (X.toSpecΓ ≫ (Spec.map g.appTop ≫ Y.isoSpec.inv)) := by
    rw [hfac]; infer_instance
  have : UniversallyClosed X.toSpecΓ :=
    UniversallyClosed.of_comp_of_isSeparated _ (Spec.map g.appTop ≫ Y.isoSpec.inv)
  have : IsClosedImmersion X.toSpecΓ :=
    IsClosedImmersion.of_isPreimmersion _ X.toSpecΓ.isClosedMap.isClosed_range
  exact isAffine_of_isAffineHom X.toSpecΓ

/-- A proper small contraction `f` onto a normal variety is an isomorphism over a nonempty open `U`
covered by affine opens `W ⊆ U` with affine preimages `f⁻¹ W`. -/
private theorem isIso_morphismRestrict_of_forall_isAffineOpen_preimage
    {k : Type u} [Field k] {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [IsNormal Y] [IsNormal Z] {f : Y ⟶ Z}
    [IsProper f] (hs : IsSmall k sZ sY f) (hZ : IsNormalVariety k sZ) (U : Z.Opens) [Nonempty U]
    (hqa : ∀ v ∈ U, ∃ W : Z.Opens, v ∈ W ∧ W ≤ U ∧ IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W)) :
    IsIso (f ∣_ U) := by
  haveI := hZ.1.toIsIntegral
  haveI := hs.isVariety_source.toIsIntegral
  haveI : IsAffineHom (f ∣_ U) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    obtain ⟨W, hyW, hWU, hW, hpW⟩ := hqa y.1 y.2
    refine ⟨U.ι ⁻¹ᵁ W, hyW, hW.preimage_of_isOpenImmersion U.ι (by
      rwa [Scheme.Opens.opensRange_ι]), ?_⟩
    rw [← (f ⁻¹ᵁ U).ι.isAffineOpen_iff_of_isOpenImmersion, image_morphismRestrict_preimage,
      U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWU]
    exact hpW
  haveI : IsIntegralHom (f ∣_ U) :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  haveI : IsFinite (f ∣_ U) :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩
  haveI := nonempty_preimage hs U
  exact (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso (f ∣_ U)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      (isBirationalMorphism_morphismRestrict_of_isSmall hs hZ U))).2 inferInstance

/-! ### Relatively ample Cartier divisors -/

open CategoryTheory.Limits in
/-- On a scheme separated over an affine scheme, a tensor product of two ample invertible modules
is ample: it is the pull-back of the external tensor product along the diagonal, which is a closed
immersion. -/
private theorem isAmple_tensorModules {X S : Scheme.{u}} [IsAffine S] (t : X ⟶ S) [IsSeparated t]
    (L M : X.Modules) [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X M]
    [Stacks.Ample.IsInvertibleModule X (Stacks.RelativeVeryAmple.tensorModules X L M)]
    (hL : Stacks.Ample.IsAmple X L) (hM : Stacks.Ample.IsAmple X M) :
    Stacks.Ample.IsAmple X (Stacks.RelativeVeryAmple.tensorModules X L M) := by
  have h1 := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    (pullback.diagonal t) (pullback.fst t t ≫ t) _
    (Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor t t L M
      ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple t L).mpr hL)
      ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple t M).mpr hM))
  have e := Stacks.AmpleExternalTensor.pullbackExternalTensorIso t t (pullback.diagonal t) L M
  simp only [pullback.diagonal_fst, pullback.diagonal_snd] at e
  have eid : ∀ N : X.Modules,
      (RingedSpaceModuleAdjunction.modulePullback (Scheme.Hom.toLRSHom (𝟙 X)).toShHom).obj N ≅
        N := fun N =>
    (Adjunction.leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        (Scheme.Hom.toLRSHom (𝟙 X)).toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))).app N ≪≫
      (Scheme.Modules.pullbackId X).app N
  have e2 := e ≪≫ Stacks.RelativeVeryAmple.tensorModulesMapIso X (eid L) (eid M)
  rw [pullback.diagonal_fst_assoc] at h1
  rw [← Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple t]
  exact (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e2).mp h1

/-- The sum of two `f`-ample Cartier divisors is `f`-ample. -/
private theorem isRelativelyAmpleCartier_add' {Y V : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ V) [IsSeparated f]
    {A B : Divisor Y}
    (hA : IsRelativelyAmpleCartier f A) (hB : IsRelativelyAmpleCartier f B) :
    IsRelativelyAmpleCartier f (A + B) := by
  obtain ⟨hAc, hAa⟩ := hA
  obtain ⟨hBc, hBa⟩ := hB
  have := hAc.isInvertibleModule_divisorialSheaf
  have := hBc.isInvertibleModule_divisorialSheaf
  have := (hAc.add hBc).isInvertibleModule_divisorialSheaf
  refine ⟨hAc.add hBc, fun U hU => ?_⟩
  have : IsAffine U.toScheme := hU
  have e := (RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).mapIso
      (hAc.divisorialSheafTensorIso hBc).symm ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorModulesIso (f ⁻¹ᵁ U).ι _ _
  have := Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules (f ⁻¹ᵁ U).toScheme
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
      A.divisorialSheaf)
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
      B.divisorialSheaf)
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (isAmple_tensorModules (f ∣_ U) _ _ (hAa U hU) (hBa U hU))

/-- A positive multiple of an `f`-ample Cartier divisor is `f`-ample. -/
private theorem isRelativelyAmpleCartier_nsmul' {Y V : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ V) [IsSeparated f]
    {A : Divisor Y}
    (hA : IsRelativelyAmpleCartier f A) {n : ℕ} (hn : 1 ≤ n) :
    IsRelativelyAmpleCartier f (n • A) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using hA
  | succ n _ ih => rw [succ_nsmul]; exact isRelativelyAmpleCartier_add' f ih hA

/-- A positive integer combination of `f`-ample Cartier divisors is `f`-ample. -/
private theorem isRelativelyAmpleCartier_sum' {Y V : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ V) [IsSeparated f] {m : ℕ}
    (hm : 1 ≤ m)
    {A : Fin m → Divisor Y} (hA : ∀ i, IsRelativelyAmpleCartier f (A i)) {n : Fin m → ℤ}
    (hn : ∀ i, 0 < n i) : IsRelativelyAmpleCartier f (∑ i, n i • A i) := by
  refine Finset.sum_induction_nonempty _ (IsRelativelyAmpleCartier f)
    (fun _ _ => isRelativelyAmpleCartier_add' f) ⟨⟨0, hm⟩, Finset.mem_univ _⟩ fun i _ => ?_
  have : n i • A i = (n i).toNat • A i := by
    rw [← natCast_zsmul, Int.toNat_of_nonneg (hn i).le]
  rw [this]
  exact isRelativelyAmpleCartier_nsmul' f (hA i) (by have := hn i; omega)

/-- If an `f`-ample Cartier divisor `A` has a local equation on `f⁻¹(U)` for an affine open `U`,
then `f⁻¹(U)` is quasi-affine: the trivial bundle is ample on it. -/
private theorem isQuasiAffine_preimage_of_isLocalEquation' {Y V : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral Y] [IsNoetherian Y] [IsNormal Y]
    (f : Y ⟶ V) {A : Divisor Y} (hA : IsRelativelyAmpleCartier f A) {U : V.Opens}
    (hU : IsAffineOpen U) {φ : (RationalFunctions Y)ˣ} (hφ : A.IsLocalEquation (f ⁻¹ᵁ U) φ) :
    (f ⁻¹ᵁ U).toScheme.IsQuasiAffine := by
  obtain ⟨hAc, hamp⟩ := hA
  have := hAc.isInvertibleModule_divisorialSheaf
  have e := MMP.Threefold.Resolution.modulePullbackIsoRestrict' (f ⁻¹ᵁ U) A.divisorialSheaf ≪≫
    hφ.restrictDivisorialSheafIso
  exact (Stacks.RelativeVeryAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule _ _ e).mpr
    (hamp U hU)

/-! ### Clearing denominators -/

/-- Finitely many rationals have a common positive denominator. -/
private theorem exists_pos_nat_mul_eq_int {ι : Type*} [Finite ι] (x : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ z : ℤ, (N : ℚ) * x i = z := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨∏ l, (x l).den, Finset.prod_pos fun l _ => (x l).den_pos, fun i => ?_⟩
  refine ⟨(∏ l ∈ Finset.univ.erase i, ((x l).den : ℤ)) * (x i).num, ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  push_cast
  rw [mul_comm ((x i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]

/-- A positive real combination of the integer vectors `a i` equal to a real combination of the
integer vectors `b j` yields a positive rational such relation. -/
private theorem exists_pos_rat_relation {P : Type*} {m k : ℕ} (s : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) (r : Fin k → ℝ) (a : Fin m → P → ℤ) (b : Fin k → P → ℤ)
    (h : ∀ p, ∑ i, s i * a i p = ∑ j, r j * b j p) :
    ∃ α : Fin m → ℚ, (∀ i, 0 < α i) ∧ ∃ β : Fin k → ℚ,
      ∀ p, ∑ i, α i * a i p = ∑ j, β j * b j p := by
  classical
  let W : Submodule ℚ ℝ := Submodule.span ℚ (Set.range s ∪ Set.range r)
  have : FiniteDimensional ℚ W :=
    FiniteDimensional.span_of_finite ℚ ((Set.finite_range s).union (Set.finite_range r))
  let sW : Fin m → W := fun i => ⟨s i, Submodule.subset_span (Or.inl ⟨i, rfl⟩)⟩
  let rW : Fin k → W := fun j => ⟨r j, Submodule.subset_span (Or.inr ⟨j, rfl⟩)⟩
  let bW := Module.finBasis ℚ W
  let cs : Fin m → _ := fun i => bW.repr (sW i)
  let cr : Fin k → _ := fun j => bW.repr (rW j)
  have key : ∀ p, ∑ i, (a i p : ℚ) • cs i = ∑ j, (b j p : ℚ) • cr j := by
    intro p
    have hw : ∑ i, (a i p : ℚ) • sW i = ∑ j, (b j p : ℚ) • rW j := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, sW, rW, Rat.cast_intCast,
        Rat.smul_def]
      simpa [mul_comm] using h p
    simpa [map_sum, cs, cr] using congrArg bW.repr hw
  have hexp : ∀ i, s i = ∑ t, (cs i t : ℝ) * (bW t : ℝ) := by
    intro i
    have := congrArg Subtype.val (bW.sum_repr (sW i))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def] at this
    exact this.symm
  let O : Set (Fin _ → ℝ) := {x | ∀ i, 0 < ∑ t, (cs i t : ℝ) * x t}
  have hO : IsOpen O := by
    simp only [O, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)
  have hOne : O.Nonempty := ⟨fun t => (bW t : ℝ), fun i => by rw [← hexp]; exact hs i⟩
  obtain ⟨q, hq⟩ := (DenseRange.piMap fun _ => Rat.denseRange_cast).exists_mem_open hO hOne
  let α : Fin m → ℚ := fun i => ∑ t, cs i t * q t
  let β : Fin k → ℚ := fun j => ∑ t, cr j t * q t
  have hα : ∀ i, 0 < α i := fun i => by
    have := hq i
    simp only [Pi.map_apply] at this
    exact_mod_cast this
  have hrel : ∀ p, ∑ i, α i * a i p = ∑ j, β j * b j p := by
    intro p
    have := fun t => congrArg (fun g => g t * q t) (key p)
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul] at this
    calc ∑ i, α i * a i p = ∑ t, ∑ i, (a i p : ℚ) * cs i t * q t := by
          simp only [α, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ t, ∑ j, (b j p : ℚ) * cr j t * q t := Finset.sum_congr rfl fun t _ => this t
      _ = ∑ j, β j * b j p := by
          simp only [β, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by ring
  exact ⟨α, hα, β, hrel⟩

/-- **Clearing denominators in a real relation with integer coefficients.** If a positive real
combination of the integer vectors `a i` equals a real combination of the integer vectors `b j`,
then a positive integer combination of the `a i` equals an integer combination of the `b j`. -/
private theorem exists_pos_int_relation {P : Type*} {m k : ℕ} (s : Fin m → ℝ)
    (hs : ∀ i, 0 < s i) (r : Fin k → ℝ) (a : Fin m → P → ℤ) (b : Fin k → P → ℤ)
    (h : ∀ p, ∑ i, s i * a i p = ∑ j, r j * b j p) :
    ∃ n : Fin m → ℤ, (∀ i, 0 < n i) ∧ ∃ c : Fin k → ℤ,
      ∀ p, ∑ i, n i * a i p = ∑ j, c j * b j p := by
  classical
  obtain ⟨α, hα, β, hrel⟩ := exists_pos_rat_relation s hs r a b h
  obtain ⟨N, hN, hz⟩ := exists_pos_nat_mul_eq_int (Sum.elim α β)
  choose z hz using hz
  refine ⟨fun i => z (Sum.inl i), fun i => ?_, fun j => z (Sum.inr j), fun p => ?_⟩
  · have h1 := hz (Sum.inl i)
    simp only [Sum.elim_inl] at h1
    have : (0 : ℚ) < z (Sum.inl i) := h1 ▸ mul_pos (by exact_mod_cast hN) (hα i)
    exact_mod_cast this
  · have h2 : ((∑ i, z (Sum.inl i) * a i p : ℤ) : ℚ) = ((∑ j, z (Sum.inr j) * b j p : ℤ) : ℚ) := by
      push_cast
      simp only [← hz, Sum.elim_inl, Sum.elim_inr, mul_assoc, ← Finset.mul_sum, hrel p]
    exact_mod_cast h2

/-! ### Transforms of prime divisors under a flip -/

/-- The linear extension of a partial map on prime divisors which is a bijection `e` takes the
coefficient of `P` to the coefficient of `e P`. -/
private theorem mapPrimeDivisors_apply_of_eq_some {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    (e : MMP.Mori.PrimeDivisor X ≃ MMP.Mori.PrimeDivisor Y) (he : ∀ P, φ P = some (e P))
    (D : DivisorWithCoeffs R X) (P : MMP.Mori.PrimeDivisor X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D (e P) = D P := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, h, h']
  | single Q r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_some (he Q)]
    simp only [Finsupp.single_apply, e.injective.eq_iff]

/-- If `g` sends the prime divisor `Q` to `P` and `g` is a map over `Z`, then
`φ⁺(η_P) = φ(η_Q)`. -/
private theorem map_genericPoint_eq_of_transformPrimeDivisor_eq_some {X X' Z : Scheme.{u}}
    [IsReduced X] [IsSeparated (X' ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)]
    {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'} (hg : MMP.Flips.RationalMap.IsOver φ φp g)
    {Q : MMP.Mori.PrimeDivisor X} {P : MMP.Mori.PrimeDivisor X'}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor g Q = some P) :
    φp P.genericPoint = φ Q.genericPoint := by
  obtain ⟨g', hQ, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  have hP : P.genericPoint = g'.hom ⟨Q.genericPoint, hQ⟩ := by
    have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
    rw [coe_transform_eq_closure_singleton g' hg' Q hQ,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
    exact (inseparable_iff_closure_eq.2 h1).eq
  rw [hP]
  have h1 : (g'.compHom φp).toRationalMap = φ.toPartialMap.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg']
    exact hg
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom φp) (g' := φ.toPartialMap) h1 hQ trivial
  change (g'.hom ≫ φp) ⟨Q.genericPoint, hQ⟩ = (X.topIso.hom ≫ φ) ⟨Q.genericPoint, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Scheme.topIso_hom]
  rfl

/-- **Descent of local equations.** Over an open `U ⊆ Z` over which `φ` is an isomorphism, the
transform `g_* C` of a Cartier divisor `C` on `X` has a local equation on `φ⁺⁻¹(W)` for a
neighbourhood `W ⊆ U` of every point of `U`: a local equation of `C` near the point of `X` over
`v`, read in `K(Z) = K(X) = K(X⁺)`, has the same orders along corresponding prime divisors. -/
private theorem exists_isLocalEquation_of_coeff_eq {X X' Z : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [AlgebraicGeometry.IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [AlgebraicGeometry.IsIntegral Z]
    [IsSeparated (X' ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)]
    {φ : X ⟶ Z} {φp : X' ⟶ Z} [IsDominant φ] [IsDominant φp] [UniversallyClosed φ]
    (hφb : IsBirationalMorphism φ)
    (e : MMP.Mori.PrimeDivisor X ≃ MMP.Mori.PrimeDivisor X')
    (hgen : ∀ Q : MMP.Mori.PrimeDivisor X, φp (e Q).genericPoint = φ Q.genericPoint)
    (hval : ∀ P : MMP.Mori.PrimeDivisor X,
      (e P).divisorialValuation.comap (functionFieldMap φp) =
        P.divisorialValuation.comap (functionFieldMap φ))
    (U : Z.Opens) [IsIso (φ ∣_ U)] [Surjective φ] {C : Divisor X} (hC : C.IsCartier)
    {C' : Divisor X'} (hC' : ∀ Q, C'.coeff (e Q) = C.coeff Q) (v : Z) (hv : v ∈ U) :
    ∃ W : Z.Opens, v ∈ W ∧ W ≤ U ∧ ∃ ψ : (RationalFunctions X')ˣ,
      Divisor.IsLocalEquation C' (φp ⁻¹ᵁ W) ψ := by
  -- `φ` is injective over `U`, and `v` has a preimage
  have hinj : ∀ a b : X, φ a ∈ U → φ b ∈ U → φ a = φ b → a = b := by
    intro a b ha hb hab
    have : (φ ∣_ U) ⟨a, ha⟩ = (φ ∣_ U) ⟨b, hb⟩ :=
      Subtype.ext ((morphismRestrict_base_coe φ U ⟨a, ha⟩).trans
        (hab.trans (morphismRestrict_base_coe φ U ⟨b, hb⟩).symm))
    exact congrArg Subtype.val ((φ ∣_ U).isOpenEmbedding.injective this)
  obtain ⟨x, hφx⟩ := φ.surjective v
  obtain ⟨N, hxN, φ₀, hφ₀⟩ := hC x
  -- the neighbourhood `W` of `v`: the points of `U` whose fibre lies in `N`
  have hcl : IsClosed (φ '' (Nᶜ : Set X)) := φ.isClosedMap _ N.isOpen.isClosed_compl
  let W : Z.Opens := U ⊓ ⟨(φ '' (Nᶜ : Set X))ᶜ, hcl.isOpen_compl⟩
  have hvW : v ∈ W := by
    refine ⟨hv, ?_⟩
    rintro ⟨b, hbN, hb⟩
    have hbU : φ b ∈ U := hb ▸ hv
    exact hbN (hinj b x hbU (hφx ▸ hv) (hb.trans hφx.symm) ▸ hxN)
  have hWN : ∀ a : X, φ a ∈ W → a ∈ N := fun a ha => by
    by_contra h
    exact ha.2 ⟨a, h, rfl⟩
  -- the local equation, through the function field of `Z`
  obtain ⟨g₀, hg₀, hord₀⟩ := MMP.Positivity.exists_ord_eq_of_units φ₀
  obtain ⟨θ, hθ⟩ := hφb.functionFieldMap_bijective.2 g₀
  have hθ0 : θ ≠ 0 := by rintro rfl; exact hg₀ (by rw [← hθ, map_zero])
  have hψ0 : functionFieldMap φp θ ≠ 0 := (map_ne_zero _).mpr hθ0
  obtain ⟨ψ, hψ⟩ := MMP.Positivity.exists_units_of_ne_zero hψ0
  refine ⟨W, hvW, inf_le_left, ψ, fun P hP => ?_⟩
  obtain ⟨Q, rfl⟩ := e.surjective P
  have hgen' : φp (e Q).genericPoint ∈ W := ((e Q).genericPoint_mem_iff (φp ⁻¹ᵁ W)).2 hP
  rw [hgen Q] at hgen'
  have hQN : (Q.support ∩ N).Nonempty := (Q.genericPoint_mem_iff N).1 (hWN _ hgen')
  rw [hC' Q, hφ₀ Q hQN, hord₀, hψ, ← hθ]
  have hv := congrArg (fun w => w θ) (hval Q)
  simp only [Valuation.comap_apply] at hv
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hψ0,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr hθ0)] at hv
  exact (neg_inj.mp (WithZero.exp_injective hv)).symm

/-- **A `φ⁺`-ample Cartier multiple of `E⁺`.** For a flip `φ⁺` of a `ℚ`-Cartier divisor `E` whose
transform `g` maps the prime divisors of `X` bijectively onto those of `X⁺`, there are a Cartier
divisor `C` on `X` and a `φ⁺`-ample Cartier divisor on `X⁺` which is an integral multiple of
`g_* C`: take `C = mE`, write `E⁺ = ∑ sᵢ Aᵢ` with `Aᵢ` `φ⁺`-ample and clear denominators. -/
private theorem exists_isRelativelyAmpleCartier_eq_zsmul_transformDivisor
    {k : Type u} [Field k] {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {E : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hE : E.IsQCartier) (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g)
    (e : MMP.Mori.PrimeDivisor X ≃ MMP.Mori.PrimeDivisor X')
    (he : ∀ P, MMP.Mori.RationalMap.transformPrimeDivisor g P = some (e P)) :
    ∃ C : Divisor X, C.IsCartier ∧ ∃ A : Divisor X', IsRelativelyAmpleCartier φp A ∧
      ∃ d : ℤ, A = d • MMP.Mori.RationalMap.transformDivisor g C := by
  haveI := hflip.isProper
  obtain ⟨m, hm, C, hCE, hC⟩ := hE.exists_pos
  obtain ⟨n, s, A, hn1, hs, hA, hAE⟩ := hflip.isRelativelyAmple_transform
  set Cp := MMP.Mori.RationalMap.transformDivisor g C
  have hcoeff : ∀ p, ∑ i, s i * (A i p : ℝ) = ∑ _j : Fin 1, (1 / (m : ℝ)) * (Cp p : ℝ) := by
    intro p
    obtain ⟨Q, rfl⟩ := e.surjective p
    have h1 := congrArg (fun D : RDivisor X' => D (e Q)) hAE
    have h4 := congrArg (fun D : QDivisor X => D Q) hCE
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at h1
    simp only [Finsupp.smul_apply, smul_eq_mul, Int.cast_natCast, zsmul_eq_mul] at h4
    have h1' : ∑ i, s i * ((A i (e Q) : ℤ) : ℝ) = QDivisor.toRDivisor E Q :=
      h1.symm.trans (mapPrimeDivisors_apply_of_eq_some e he _ Q)
    have h3 : Cp (e Q) = C Q := mapPrimeDivisors_apply_of_eq_some e he C Q
    rw [h1', h3, Fin.sum_univ_one]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have h5 : ((C Q : ℤ) : ℝ) = (m : ℝ) * ((E Q : ℚ) : ℝ) := by exact_mod_cast h4
    rw [h5]
    change ((E Q : ℚ) : ℝ) = _
    field_simp
  obtain ⟨c, hc, d, hrel⟩ := exists_pos_int_relation s hs (fun _ => 1 / (m : ℝ))
    (fun i p => A i p) (fun _ p => Cp p) hcoeff
  refine ⟨C, hC, ∑ i, c i • A i, isRelativelyAmpleCartier_sum' φp hn1 hA hc, d 0,
    Finsupp.ext fun p => ?_⟩
  simpa [Finsupp.finsetSum_apply] using hrel p

/-! ### A flip is an isomorphism away from the flipping locus -/

/-- Let `φ : X ⟶ Z` be a small contraction of normal varieties, `E` a `ℚ`-Cartier `ℚ`-divisor on
`X` with `-E` `φ`-ample, and `φ⁺ : X⁺ ⟶ Z` a flip of `φ` with respect to `E` (with birational map
`g : X ⤏ X⁺`). Then `φ⁺` restricts to an isomorphism `φ⁺⁻¹(U) ⟶ U` over every open `U ⊆ Z`
disjoint from the image `φ(Ex φ)` of the exceptional set of `φ`. -/
@[mmp "lem_fa4_flip_iso_off_flipping_locus"]
public theorem IsFlip.isIso_morphismRestrict_of_disjoint_image_exceptionalSet
    {k : Type u} [Field k] {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {E : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hE : E.IsQCartier) (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g)
    (U : Z.Opens) (hU : Disjoint (U : Set Z) (φ '' exceptionalSet φ)) :
    IsIso (φp ∣_ U) := by
  haveI := hflip.isNormalVariety_target.isLocallyNoetherian
  haveI : IsNormal Z := hflip.isNormalVariety_target.2
  haveI := hflip.isProper
  haveI := hflip.isContraction.isProper
  haveI := hflip.isNormalVariety_source.1.toIsIntegral
  haveI := hflip.isNormalVariety_target.1.toIsIntegral
  haveI := hflip.isNormalVariety_flip.1.toIsIntegral
  rcases isEmpty_or_nonempty U with hUe | hUne
  · haveI : IsEmpty (φp ⁻¹ᵁ U) := ⟨fun x => hUe.false ⟨_, x.2⟩⟩
    exact isIso_of_isEmpty _
  haveI : IsIso (φ ∣_ U) := isIso_morphismRestrict_source_of_disjoint hflip.isContraction U hU
  -- separatedness
  have : IsSeparated sZ := hflip.isNormalVariety_target.1.toIsSeparated
  have := isSeparated_terminal sZ
  have : IsSeparated sX' := hflip.isNormalVariety_flip.1.toIsSeparated
  have := isSeparated_terminal sX'
  -- dominance and birationality
  haveI hφs := hflip.isSmall_source.toIsBirationalContraction.surjective_and_isBirational.1
  haveI hφps := hflip.isSmall.toIsBirationalContraction.surjective_and_isBirational.1
  have hφb : IsBirationalMorphism φ := hflip.isSmall_source.isBirationalMorphism _ _
  have he := (MMP.Flips.exceptional_hasNonemptyCenter_iff_of_isSmall sX sX' sZ φ φp
    hflip.isSmall_source hflip.isSmall).2 g hflip.isModificationOf
  set e := MMP.Flips.primeDivisorEquivOfModification
    hflip.isSmall_source hflip.isSmall hflip.isModificationOf
  -- a `φ⁺`-ample Cartier divisor `A = d • g_* C` with `C` Cartier
  obtain ⟨C, hC, A, hA', d, hAd⟩ :=
    exists_isRelativelyAmpleCartier_eq_zsmul_transformDivisor hE hflip e fun P => (he P).1
  -- affine neighbourhoods with affine preimages
  haveI : IsNoetherian X' := {}
  have hqa : ∀ v ∈ U, ∃ W : Z.Opens, v ∈ W ∧ W ≤ U ∧ IsAffineOpen W ∧
      IsAffineOpen (φp ⁻¹ᵁ W) := by
    intro v hv
    obtain ⟨W, hvW, hWU, ψ, hψ⟩ := exists_isLocalEquation_of_coeff_eq hφb e
      (fun Q => map_genericPoint_eq_of_transformPrimeDivisor_eq_some hflip.isModificationOf.2
        (he Q).1) (fun P => (he P).2) U hC
      (mapPrimeDivisors_apply_of_eq_some e (fun P => (he P).1) C) v hv
    obtain ⟨W', hW', hvW', hW'W⟩ := exists_isAffineOpen_mem_and_subset hvW
    have hloc : A.IsLocalEquation (φp ⁻¹ᵁ W') (ψ ^ d) := by
      rw [hAd]
      exact (hψ.zsmul d).mono (φp.preimage_mono hW'W)
    have := isQuasiAffine_preimage_of_isLocalEquation' φp hA' hW' hloc
    haveI : IsAffine W'.toScheme := hW'
    exact ⟨W', hvW', hW'W.trans hWU, hW', isAffine_of_isQuasiAffine_of_universallyClosed (φp ∣_ W')⟩
  exact isIso_morphismRestrict_of_forall_isAffineOpen_preimage hflip.isSmall
    hflip.isNormalVariety_target U hqa

/-! ### A nontrivial flip has a flipped curve -/

/-- A subset containing two distinct points `a ⤳ b` of a `T₀` space has positive topological
Krull dimension. -/
private theorem topologicalKrullDim_pos_of_specializes {α : Type*} [TopologicalSpace α]
    [T0Space α] {T : Set α} {a b : α} (ha : a ∈ T) (hb : b ∈ T) (hab : a ⤳ b) (hne : a ≠ b) :
    0 < topologicalKrullDim T := by
  let A : IrreducibleCloseds T :=
    ⟨closure {⟨a, ha⟩}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds T :=
    ⟨closure {⟨b, hb⟩}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hsp : (⟨a, ha⟩ : T) ⤳ ⟨b, hb⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  have hBA : B < A := by
    refine lt_of_le_of_ne ?_ fun h => hne ?_
    · change closure {(⟨b, hb⟩ : T)} ⊆ closure {⟨a, ha⟩}
      exact closure_minimal (Set.singleton_subset_iff.mpr hsp.mem_closure) isClosed_closure
    · have hmem : (⟨a, ha⟩ : T) ∈ closure {(⟨b, hb⟩ : T)} := by
        change (⟨a, ha⟩ : T) ∈ (B : Set T)
        rw [h]; exact subset_closure rfl
      have hba : (⟨b, hb⟩ : T) ⤳ ⟨a, ha⟩ := specializes_iff_mem_closure.mpr hmem
      exact congrArg Subtype.val (hsp.antisymm hba).eq
  exact Order.krullDim_pos_iff.mpr ⟨B, A, hBA⟩

/-- A birational contraction onto a normal variety without flipping curves is an isomorphism:
an infinite fibre over a closed point has an infinite irreducible component, which has positive
dimension; so every fibre over a closed point is finite, the open finite-fibre locus contains every
closed point and is everything, and the morphism is an isomorphism over it. -/
private theorem isIso_of_forall_not_isFlippingCurve {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : Y ⟶ Z} [IsNormal Z]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    (hf : IsBirationalContraction k sZ sY f) (h : ∀ C, ¬ IsFlippingCurve k sY sZ f C) :
    IsIso f := by
  have := hf.isVariety_target.toIsIntegral
  have := hf.isVariety_source.toIsIntegral
  have : IsNoetherian Y := ⟨⟩
  have hfp := hf.isProper
  have hb : IsBirational f := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    hf.surjective_and_isBirational.2
  obtain ⟨hU, hI⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1 hfp
  have hall : MMP.Resolution.Bridges.finiteFibreLocus f = Set.univ := by
    by_contra hne
    have : CompactSpace Z :=
      hf.surjective_and_isBirational.1.surj.compactSpace f.continuous
    obtain ⟨z, hz, hzc⟩ := hU.isClosed_compl.exists_closed_singleton
      (Set.nonempty_compl.mpr hne)
    have hinf : (f ⁻¹' {z}).Infinite := hz
    have hFc : IsClosed (f ⁻¹' {z}) := hzc.preimage f.continuous
    obtain ⟨S, hSf, hScl, hSirr, hFS⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
    obtain ⟨t, htS, htinf⟩ : ∃ t ∈ S, t.Infinite := by
      by_contra! hfin
      exact hinf (hFS ▸ hSf.sUnion fun t ht => hfin t ht)
    obtain ⟨t', htt', ht'max⟩ := hSf.exists_le_maximal htS
    have ht'S : t' ∈ S := ht'max.prop
    have ha := (hScl t' ht'S).closure_eq ▸ (hSirr t' ht'S).isGenericPoint_genericPoint_closure
    obtain ⟨c, hct, hca⟩ :=
      (htinf.diff (Set.finite_singleton (hSirr t' ht'S).genericPoint)).nonempty
    have ht'F : t' ⊆ f ⁻¹' {z} := hFS ▸ Set.subset_sUnion_of_mem ht'S
    refine h t' ⟨hf.isVariety_source, hf.isVariety_target, hf.comp_eq, hfp, z, hzc,
      ⟨⟨hSirr t' ht'S, ht'F⟩, ?_⟩,
      topologicalKrullDim_pos_of_specializes ha.mem (htt' hct) (ha.specializes (htt' hct))
        fun h => hca h.symm⟩
    rintro U ⟨hUirr, hUF⟩ htU
    obtain ⟨s, hs, hUs⟩ := (isIrreducible_iff_sUnion_isClosed.mp hUirr) hSf.toFinset
      (fun s hs => hScl s (hSf.mem_toFinset.mp hs))
      (by rw [Set.Finite.coe_toFinset, ← hFS]; exact hUF)
    exact hUs.trans (ht'max.2 (hSf.mem_toFinset.mp hs) (htU.trans hUs))
  have hI' : IsIso (f ∣_ ⊤) := (show (⟨_, hU⟩ : Z.Opens) = ⊤ from Opens.ext hall) ▸ hI
  exact (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun _ : Unit => (⊤ : Z.Opens)) (by simp)).mpr fun _ => hI'

/-- Relative ampleness is preserved under composing with the inverse of an isomorphism of the
target: an affine open of the new target is the preimage of an affine open of the old one. -/
private theorem isRelativelyAmple_comp_inv {Y W Z : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (φ : Y ⟶ Z) (ψ : W ⟶ Z) [IsIso ψ] {A : RDivisor Y}
    (h : MMP.Flips.IsRelativelyAmple φ A) : MMP.Flips.IsRelativelyAmple (φ ≫ inv ψ) A := by
  obtain ⟨m, r, L, hm, hr, hL, hA⟩ := h
  refine ⟨m, r, L, hm, hr, fun j => ?_, hA⟩
  obtain ⟨hc, ha⟩ := hL j
  exact ⟨hc, fun U hU => ha _ (hU.preimage (inv ψ))⟩

/-- The negative of a pull-back of an `ℝ`-Cartier divisor is a pull-back of its negative. -/
private theorem isRCartierPullback_neg {Y W : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian W] [IsNormal W] {f : Y ⟶ W} {D : RDivisor W} {G : RDivisor Y}
    (h : IsRCartierPullback f D G) : IsRCartierPullback f (-D) (-G) := by
  obtain ⟨m, r, L, L', hc, hD, hpb, hG⟩ := h
  exact ⟨m, -r, L, L', hc, by simp [hD, Finset.sum_neg_distrib, neg_smul], hpb,
    by simp [hG, Finset.sum_neg_distrib, neg_smul]⟩

/-- A rational map over an isomorphism `ψ` is the morphism `f ≫ ψ⁻¹`. -/
private theorem eq_toRationalMap_of_compHom_eq {X Y Z : Scheme.{u}} (g : X.RationalMap Y)
    (f : X ⟶ Z) (ψ : Y ⟶ Z) [IsIso ψ] (h : g.compHom ψ = f.toRationalMap) :
    g = (f ≫ inv ψ).toRationalMap := by
  have h1 : (g.compHom ψ).compHom (inv ψ) = g := by
    induction g using Quotient.inductionOn with
    | h g' =>
      change ((g'.compHom ψ).compHom (inv ψ)).toRationalMap = g'.toRationalMap
      congr 1
      ext1
      · rfl
      · simp [Scheme.PartialMap.compHom]
  rw [← h1, h]
  rfl

/-- A universally closed birational morphism `h` whose transform of prime divisors is a bijection
`e` is a local isomorphism at the generic point of every prime divisor `P`: the valuation ring
`𝒪_{e P}` is dominated by the stalk of some `x` over it with an isomorphism of local rings, `x`
then has coheight one, so it is the generic point of a prime divisor `P'` with `e P' = e P`. -/
private theorem isIso_stalkMap_genericPoint_of_transformPrimeDivisor {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (h : X ⟶ Y) [UniversallyClosed h]
    (hhb : IsBirationalMorphism h) (e : MMP.Mori.PrimeDivisor X ≃ MMP.Mori.PrimeDivisor Y)
    (he : ∀ P, MMP.Mori.RationalMap.transformPrimeDivisor (X := X) h.toRationalMap P = some (e P))
    (P : MMP.Mori.PrimeDivisor X) : IsIso (h.stalkMap P.genericPoint) := by
  have : IsDominant h := hhb.isDominant
  have := (e P).isDiscreteValuationRing_localRing
  obtain ⟨x, hx, hiso⟩ := MMP.Intersection.exists_isIso_stalkMap_of_valuationRing h
    hhb.functionFieldMap_bijective (e P).genericPoint
  have hco : Order.coheight x = 1 := by
    have h' := ringKrullDim_eq_of_ringEquiv (asIso (h.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      (e P).coheight_genericPoint] at h'
    exact_mod_cast h'.symm
  let P' : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hP' : P'.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  have heP : e P' = e P := by
    have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff h P' (e P)).mpr
      (hP' ▸ hx)
    rw [he] at h1
    exact Option.some_injective _ h1
  rw [← e.injective heP, hP']
  exact hiso

/-- If the flip `φ⁺` is an isomorphism, `E` is the pull-back of `E⁺ = g_* E` along `φ ≫ φ⁺⁻¹`:
`h = φ ≫ φ⁺⁻¹` is the morphism underlying `g`, so it maps the generic point of each prime divisor
`P` to that of its transform `e P`, with an isomorphism of local rings there, and the coefficient
of `P` in `h^* E⁺` is that of `e P` in `E⁺`, which is that of `P` in `E`. -/
private theorem isRCartierPullback_transformDivisor_of_isIso
    {k : Type u} [Field k] {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {E : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g)
    [IsIso φp] :
    IsRCartierPullback (φ ≫ inv φp)
      (MMP.Mori.RationalMap.transformDivisor g (QDivisor.toRDivisor E))
      (QDivisor.toRDivisor E) := by
  have := hflip.isNormalVariety_source.1.toIsIntegral
  have := hflip.isNormalVariety_flip.1.toIsIntegral
  have := hflip.isNormalVariety_target.1.toIsIntegral
  have := hflip.isContraction.isProper
  have : IsSeparated sX' := hflip.isNormalVariety_flip.1.toIsSeparated
  have := isSeparated_terminal sX'
  have : IsNormal Z := hflip.isNormalVariety_target.2
  have : IsLocallyNoetherian Z := hflip.isNormalVariety_target.isLocallyNoetherian
  have : Surjective φ :=
    hflip.isSmall_source.toIsBirationalContraction.surjective_and_isBirational.1
  have : Surjective φp := hflip.isSmall.toIsBirationalContraction.surjective_and_isBirational.1
  set h := φ ≫ inv φp
  have hb : IsBirational φ := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    hflip.isSmall_source.surjective_and_isBirational.2
  have hbi : IsBirational (inv φp) := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    (isBirationalMorphism_of_isIso _)
  have hhb : IsBirationalMorphism h := isBirationalMorphism_comp_of_isBirational (inv φp) φ hbi hb
  have : IsDominant h := hhb.isDominant
  have hgh : g = h.toRationalMap :=
    eq_toRationalMap_of_compHom_eq g φ φp hflip.isModificationOf.2
  have he := (MMP.Flips.exceptional_hasNonemptyCenter_iff_of_isSmall sX sX' sZ φ φp
    hflip.isSmall_source hflip.isSmall).2 g hflip.isModificationOf
  set e := MMP.Flips.primeDivisorEquivOfModification
    hflip.isSmall_source hflip.isSmall hflip.isModificationOf
  have hgen : ∀ P, h P.genericPoint = (e P).genericPoint := fun P =>
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff h P (e P)).mp
      (hgh ▸ (he P).1)
  obtain ⟨m, r, L, hL, hEp⟩ := hflip.isCartierCombination_transform
  have hB : ∀ j (Zc : irreducibleComponents X), h (componentGenericPoint X Zc) ∉ (L j).supp :=
    fun j Zc => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant h (L j) Zc
  choose L' hL' using fun j => (hL j).exists_isPullback (hB j)
  have hpull : IsRCartierPullback h
      (MMP.Mori.RationalMap.transformDivisor g (QDivisor.toRDivisor E))
      (∑ j, r j • Divisor.toRDivisor (L' j)) :=
    ⟨m, r, L, L', hL, hEp, fun j => ⟨hB j, hL' j⟩, rfl⟩
  have hG : ∑ j, r j • Divisor.toRDivisor (L' j) = QDivisor.toRDivisor E := by
    ext P
    have := isIso_stalkMap_genericPoint_of_transformPrimeDivisor h hhb e
      (fun P => hgh ▸ (he P).1) P
    exact (MMP.Fourfold.coeff_eq_of_isRCartierPullback P (e P) (hgen P) hpull).trans
      (mapPrimeDivisors_apply_of_eq_some e (fun P => (he P).1) _ P)
  exact hG ▸ hpull

/-- Let `φ : X ⟶ Z` be a small contraction of normal varieties which is not an isomorphism, `E` a
`ℚ`-Cartier `ℚ`-divisor on `X` with `-E` `φ`-ample, and `φ⁺ : X⁺ ⟶ Z` a flip of `φ` with
respect to `E` (with birational map `g : X ⤏ X⁺`). Then `φ⁺` has a flipped curve. -/
@[mmp "lem_fa4_nontrivial_flip_has_flipped_curve"]
public theorem IsFlip.exists_isFlippedCurveOf_of_not_isIso
    {k : Type u} [Field k] {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {E : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hE : E.IsQCartier) (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g)
    (hφ : ¬ IsIso φ) :
    ∃ C : Set X', IsFlippedCurveOf k sX sZ sX' (QDivisor.toRDivisor E) φ φp g C := by
  have := hflip.isNormalVariety_source.1.toIsIntegral
  have := hflip.isNormalVariety_flip.1.toIsIntegral
  have := hflip.isNormalVariety_target.1.toIsIntegral
  have : IsNormal Z := hflip.isNormalVariety_target.2
  have : IsLocallyNoetherian Z := hflip.isNormalVariety_target.isLocallyNoetherian
  have : IsNoetherian X := ⟨⟩
  by_contra hno
  have : IsIso φp := isIso_of_forall_not_isFlippingCurve hflip.isSmall.toIsBirationalContraction
    fun C hC => hno ⟨C, hflip, hC⟩
  have := hflip.isContraction.isProper
  have hb : IsBirational φ := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    hflip.isSmall_source.surjective_and_isBirational.2
  have hbi : IsBirational (inv φp) := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    (isBirationalMorphism_of_isIso _)
  have hh : IsIso (φ ≫ inv φp) := isIso_of_isRelativelyAmple_of_isRCartierPullback (φ ≫ inv φp)
    (isBirationalMorphism_comp_of_isBirational (inv φp) φ hbi hb)
    (isRCartierPullback_neg (isRCartierPullback_transformDivisor_of_isIso hflip))
    (isRelativelyAmple_comp_inv φ φp hflip.isRelativelyAntiAmple)
  exact hφ (by simpa using (inferInstance : IsIso ((φ ≫ inv φp) ≫ φp)))

end MMP.Flips

namespace MMP.Mori

/-! ### The exceptional locus of a proper birational morphism -/

/-- In a Noetherian `T₀` space, a point is clopen exactly when every irreducible component
through it has dimension `≤ 0`. -/
private lemma isClopen_singleton_iff_topologicalKrullDim_le_zero {F : Type*} [TopologicalSpace F]
    [T0Space F]
    [TopologicalSpace.NoetherianSpace F] (p : F) :
    IsClopen {p} ↔ ∀ C ∈ irreducibleComponents F, p ∈ C → topologicalKrullDim C ≤ 0 := by
  constructor
  · intro hp C hC hpC
    have hsub : C ⊆ {p} :=
      (IsIrreducible.isConnected hC.1).isPreconnected.subset_isClopen hp
        ⟨p, hpC, rfl⟩
    have : Subsingleton C := (Set.subsingleton_singleton.anti hsub).coe_sort
    exact topologicalKrullDim_zero_of_discreteTopology C
  · intro H
    -- every component through `p` is `{p}`
    have hcomp : ∀ C ∈ irreducibleComponents F, p ∈ C → C = {p} := by
      intro C hC hpC
      have hdim := H C hC hpC
      have huniv : ∀ q : C, closure {q} = Set.univ := by
        intro q
        by_contra hne
        have : IrreducibleSpace C := Subtype.irreducibleSpace hC.1
        have hlt : (⟨closure {q}, isIrreducible_singleton.closure, isClosed_closure⟩ :
            TopologicalSpace.IrreducibleCloseds C) <
            ⟨Set.univ, IrreducibleSpace.isIrreducible_univ C, isClosed_univ⟩ :=
          lt_of_le_of_ne (Set.subset_univ _) (fun h ↦ hne (congrArg (·.1) h))
        exact absurd hdim (not_le.mpr (Order.krullDim_pos_iff.mpr ⟨_, _, hlt⟩))
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hpC, fun q hq ↦ ?_⟩
      have h1 : (⟨p, hpC⟩ : C) ∈ closure {(⟨q, hq⟩ : C)} := by rw [huniv]; trivial
      have h2 : (⟨q, hq⟩ : C) ∈ closure {(⟨p, hpC⟩ : C)} := by rw [huniv]; trivial
      have := (inseparable_iff_closure_eq.mpr
        (subset_antisymm (closure_minimal (by simpa using h2) isClosed_closure)
          (closure_minimal (by simpa using h1) isClosed_closure))).eq
      exact congrArg Subtype.val this
    have hclosed : IsClosed {p} := by
      rw [← hcomp _ (irreducibleComponent_mem_irreducibleComponents p) (mem_irreducibleComponent)]
      exact isClosed_of_mem_irreducibleComponents _
        (irreducibleComponent_mem_irreducibleComponents p)
    refine ⟨hclosed, ?_⟩
    have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := F)
    have heq : ({p} : Set F)ᶜ = ⋃ C ∈ {C ∈ irreducibleComponents F | p ∉ C}, C := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_setOf_eq,
        exists_prop]
      constructor
      · intro hx
        refine ⟨irreducibleComponent x,
          ⟨irreducibleComponent_mem_irreducibleComponents x, fun hp ↦ hx ?_⟩,
          mem_irreducibleComponent⟩
        simpa [hcomp _ (irreducibleComponent_mem_irreducibleComponents x) hp] using
          (mem_irreducibleComponent : x ∈ irreducibleComponent x)
      · rintro ⟨C, ⟨-, hpC⟩, hxC⟩ rfl
        exact hpC hxC
    rw [← isClosed_compl_iff, heq]
    exact (hfin.subset fun C hC ↦ hC.1).isClosed_biUnion fun C hC ↦
      isClosed_of_mem_irreducibleComponents C hC.1

/-- A point of a scheme is clopen in its fibre exactly when the morphism is quasi-finite at it. -/
private lemma isClopen_singleton_fiber_iff_quasiFiniteAt {X S : Scheme} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    IsClopen {(⟨x, rfl⟩ : f ⁻¹' {f x})} ↔ f.QuasiFiniteAt x := by
  have hx : f.fiberHomeo (f x) (f.asFiber x) = ⟨x, rfl⟩ :=
    (f.fiberHomeo (f x)).apply_symm_apply _
  rw [← hx, ← Set.image_singleton (f := ⇑(f.fiberHomeo (f x))), IsClopen,
    (f.fiberHomeo (f x)).isClosed_image,
    (f.fiberHomeo (f x)).isOpen_image, Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  exact ⟨And.right, fun h ↦ ⟨(Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
    h).isClopen_singleton_asFiber.1, h⟩⟩

/-- For a morphism of finite type from a Noetherian scheme, the points lying on a
positive-dimensional irreducible component of their fibre are exactly the points at which the
morphism is not quasi-finite. -/
private lemma setOf_zero_lt_topologicalKrullDim_eq {X S : Scheme} (f : X ⟶ S)
    [LocallyOfFiniteType f] [TopologicalSpace.NoetherianSpace X] :
    {x | ∃ C ∈ irreducibleComponents (f ⁻¹' {f x}),
      (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ C ∧ 0 < topologicalKrullDim C} = {x | f.QuasiFiniteAt x}ᶜ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  rw [← isClopen_singleton_fiber_iff_quasiFiniteAt,
    isClopen_singleton_iff_topologicalKrullDim_le_zero]
  simp only [not_forall, not_le, exists_prop]

/-- If the fibres of `f` are connected, the non-quasi-finite locus of `f` is a union of fibres:
a fibre with a point clopen in it is that single point. -/
private lemma preimage_image_compl_setOf_quasiFiniteAt {X S : Scheme} (f : X ⟶ S)
    [LocallyOfFiniteType f] (hf : ∀ s, _root_.IsConnected (f ⁻¹' {s})) :
    f ⁻¹' (f '' {x | f.QuasiFiniteAt x}ᶜ) = {x | f.QuasiFiniteAt x}ᶜ := by
  refine subset_antisymm ?_ (Set.subset_preimage_image f _)
  rintro y ⟨e, he, hey⟩ hy
  have := isConnected_iff_connectedSpace.mp (hf (f y))
  have hmem := ((isClopen_singleton_fiber_iff_quasiFiniteAt f y).mpr hy).eq_univ
    ⟨_, rfl⟩ ▸ Set.mem_univ (⟨e, hey⟩ : f ⁻¹' {f y})
  obtain rfl : e = y := congrArg Subtype.val hmem
  exact he hy

/-- Let `f : Y ⟶ Z` be a proper birational morphism of varieties over `k` with `Z` normal, and
let `E ⊆ Y` be its exceptional locus: the points lying on an irreducible component of positive
dimension of their fibre. Then `E` is closed and `f⁻¹(f(E)) = E`. -/
@[mmp "lem_fa7_exceptional_locus_saturated"]
public theorem isClosed_and_preimage_image_exceptionalLocus_eq {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (hY : IsVariety k sY) (hZ : IsNormalVariety k sZ) (f : Y ⟶ Z) (hf : f ≫ sZ = sY)
    [IsProper f] (hb : IsBirationalMorphism f) :
    let E : Set Y := {y | ∃ C ∈ irreducibleComponents (f ⁻¹' {f y}),
      (⟨y, rfl⟩ : f ⁻¹' {f y}) ∈ C ∧ 0 < topologicalKrullDim C}
    IsClosed E ∧ f ⁻¹' (f '' E) = E := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := ⟨⟩
  rw [setOf_zero_lt_topologicalKrullDim_eq f]
  exact ⟨f.isOpen_quasiFiniteAt.isClosed_compl, preimage_image_compl_setOf_quasiFiniteAt f
    (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      sY sZ hY hZ f hb).2⟩

/-- The preimage, under the inclusion of `C`, of an irreducible set contained in `C` is
irreducible. -/
private lemma isIrreducible_preimage_val {T : Type*} [TopologicalSpace T] {C s : Set T}
    (hs : IsIrreducible s) (hsC : s ⊆ C) : IsIrreducible (Subtype.val ⁻¹' s : Set C) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hs.nonempty
    exact ⟨⟨x, hsC hx⟩, hx⟩
  · rintro u v hu hv ⟨a, has, hau⟩ ⟨b, hbs, hbv⟩
    obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
    obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
    obtain ⟨z, hzs, hzu, hzv⟩ := hs.2 u' v' hu' hv' ⟨a, has, hau⟩ ⟨b, hbs, hbv⟩
    exact ⟨⟨z, hsC hzs⟩, hzs, hzu, hzv⟩

/-- A space all of whose irreducible components have dimension at most `0` has dimension at
most `0`. -/
private lemma topologicalKrullDim_nonpos_of_forall_mem_irreducibleComponents {T : Type*}
    [TopologicalSpace T] (h : ∀ C ∈ irreducibleComponents T, topologicalKrullDim C ≤ 0) :
    topologicalKrullDim T ≤ 0 := by
  refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun Z W hZW x hx => ?_
  obtain ⟨C, hC, hWC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ W.isIrreducible
  let pull : (s : IrreducibleCloseds T) → (s : Set T) ⊆ C → IrreducibleCloseds C :=
    fun s hs => ⟨Subtype.val ⁻¹' s, isIrreducible_preimage_val s.isIrreducible hs,
      s.isClosed.preimage continuous_subtype_val⟩
  have hle : pull Z (fun _ hy => hWC (hZW hy)) ≤ pull W hWC := fun _ hy => hZW hy
  have hmax : pull W hWC ≤ pull Z (fun _ hy => hWC (hZW hy)) :=
    Order.krullDim_nonpos_iff_forall_isMax.mp (h C hC) _ hle
  exact hmax (show (⟨x, hWC hx⟩ : C) ∈ Subtype.val ⁻¹' (W : Set T) from hx)

/-- Off the image of the exceptional locus every fibre is finite: such a fibre has no
positive-dimensional irreducible component, so it has dimension `0`. -/
private lemma compl_image_subset_finiteFibreLocus {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    (f '' {y | ∃ C ∈ irreducibleComponents (f ⁻¹' {f y}),
      (⟨y, rfl⟩ : f ⁻¹' {f y}) ∈ C ∧ 0 < topologicalKrullDim C})ᶜ ⊆
      MMP.Resolution.Bridges.finiteFibreLocus f := by
  intro z hz
  refine MMP.Resolution.Bridges.finite_preimage_singleton_of_topologicalKrullDim_le f z
    (topologicalKrullDim_nonpos_of_forall_mem_irreducibleComponents fun C hC =>
      not_lt.mp fun hlt => ?_)
  obtain ⟨⟨x, hx⟩, hxC⟩ := hC.1.nonempty
  obtain rfl : f x = z := hx
  exact hz ⟨x, ⟨C, hC, hxC, hlt⟩, rfl⟩

/-- Let `f : Y ⟶ Z` be a proper birational morphism of varieties over `k` with `Z` normal, and
let `E ⊆ Y` be its exceptional locus: the points lying on an irreducible component of positive
dimension of their fibre. Then `V = Z ∖ f(E)` is open, `f⁻¹(V) = Y ∖ E`, and `f ∣_ V` is an
isomorphism. -/
@[mmp "lem_fa7_iso_off_exceptional_locus"]
public theorem isIso_morphismRestrict_compl_image_exceptionalLocus {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (hY : IsVariety k sY) (hZ : IsNormalVariety k sZ) (f : Y ⟶ Z) (hf : f ≫ sZ = sY)
    [IsProper f] (hb : IsBirationalMorphism f) :
    let E : Set Y := {y | ∃ C ∈ irreducibleComponents (f ⁻¹' {f y}),
      (⟨y, rfl⟩ : f ⁻¹' {f y}) ∈ C ∧ 0 < topologicalKrullDim C}
    ∃ hV : IsOpen (f '' E)ᶜ, f ⁻¹' (f '' E)ᶜ = Eᶜ ∧ IsIso (f ∣_ ⟨(f '' E)ᶜ, hV⟩) := by
  intro E
  obtain ⟨hEc, hsat⟩ :=
    MMP.Mori.isClosed_and_preimage_image_exceptionalLocus_eq sY sZ hY hZ f hf hb
  have : IsIntegral Y := hY.toIsIntegral
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  subst hf
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sZ
  obtain ⟨_, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).1 inferInstance
  refine ⟨(f.isClosedMap _ hEc).isOpen_compl, by rw [Set.preimage_compl, hsat], ?_⟩
  exact MMP.Mori.isBiregular_iff_le_biregularLocus.mpr <|
    (compl_image_subset_finiteFibreLocus f).trans
      (MMP.Mori.isBiregular_iff_le_biregularLocus.mp hiso)

end MMP.Mori

namespace MMP.Flips

open MMP.Mori

/-! ### The exceptional loci of a log flip have the same image -/

/-- Over an open `U` on which `f` restricts to an isomorphism, no point lies on a
positive-dimensional irreducible component of its fibre. -/
private theorem image_notMem_of_isIso_morphismRestrict {Y Z : Scheme} (f : Y ⟶ Z) (U : Z.Opens)
    [IsIso (f ∣_ U)] {y : Y}
    (hy : ∃ C ∈ irreducibleComponents (f ⁻¹' {f y}),
      (⟨y, rfl⟩ : f ⁻¹' {f y}) ∈ C ∧ 0 < topologicalKrullDim C) : f y ∉ U := by
  intro hyU
  obtain ⟨C, -, -, hC⟩ := hy
  haveI : Subsingleton (f ⁻¹' {f y}) := by
    refine ⟨fun a b => ?_⟩
    have ha : a.1 ∈ f ⁻¹ᵁ U := show f a.1 ∈ U by rwa [a.2]
    have hb : b.1 ∈ f ⁻¹ᵁ U := show f b.1 ∈ U by rwa [b.2]
    let p : (f ⁻¹ᵁ U).toScheme := ⟨a.1, ha⟩
    let q : (f ⁻¹ᵁ U).toScheme := ⟨b.1, hb⟩
    have hU : ∀ r : (f ⁻¹ᵁ U).toScheme, U.ι ((f ∣_ U) r) = f ((f ⁻¹ᵁ U).ι r) := fun r => by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    have hpq : p = q := (f ∣_ U).isOpenEmbedding.injective (U.ι.isOpenEmbedding.injective (by
      rw [hU, hU]
      exact a.2.trans b.2.symm))
    exact Subtype.ext (congrArg (fun r => (f ⁻¹ᵁ U).ι r) hpq)
  haveI : Subsingleton C := ⟨fun c d => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : DiscreteTopology C := Subsingleton.discreteTopology
  exact hC.not_ge (topologicalKrullDim_zero_of_discreteTopology C)

/-- For a flip `φ⁺` of a small contraction `φ` with respect to a `ℚ`-Cartier divisor, the image
of the exceptional locus of `φ⁺` lies in the image of the exceptional locus of `φ`. -/
private theorem image_exceptionalLocus_flip_subset
    {k : Type u} [Field k] {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {E : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hE : E.IsQCartier) (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g) :
    φp '' {y | ∃ C ∈ irreducibleComponents (φp ⁻¹' {φp y}),
        (⟨y, rfl⟩ : φp ⁻¹' {φp y}) ∈ C ∧ 0 < topologicalKrullDim C} ⊆
      φ '' {y | ∃ C ∈ irreducibleComponents (φ ⁻¹' {φ y}),
        (⟨y, rfl⟩ : φ ⁻¹' {φ y}) ∈ C ∧ 0 < topologicalKrullDim C} := by
  haveI := hflip.isContraction.isProper
  obtain ⟨hV, hpre, hiso⟩ := isIso_morphismRestrict_compl_image_exceptionalLocus sX sZ
    hflip.isContraction.isVariety_source hflip.isNormalVariety_target φ
    hflip.isContraction.comp_eq (hflip.isSmall_source.isBirationalMorphism _ _)
  set V : Z.Opens := ⟨_, hV⟩
  have hdisj : Disjoint (V : Set Z) (φ '' MMP.Flips.exceptionalSet φ) := by
    rw [Set.disjoint_left]
    rintro _ hzV ⟨y, hy, rfl⟩
    have hyV : y ∈ φ ⁻¹ᵁ V := hzV
    refine hy ⟨φ ⁻¹ᵁ V, hyV, ?_⟩
    rw [← morphismRestrict_ι]
    exact inferInstance
  haveI : IsIso (φp ∣_ V) :=
    hflip.isIso_morphismRestrict_of_disjoint_image_exceptionalSet hE V hdisj
  rintro _ ⟨x, hx, rfl⟩
  by_contra h
  exact image_notMem_of_isIso_morphismRestrict φp V hx h

/-- If `A = ∑ dⱼ Dⱼ` is `f`-ample Cartier and each `Dⱼ` has local equations on preimages of
neighbourhoods inside `U`, then every point of `U` has an affine neighbourhood in `U` with affine
preimage under the proper morphism `f`. -/
private theorem exists_isAffineOpen_preimage_of_isLocalEquation {Y V : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral Y] [IsNoetherian Y] [IsNormal Y] (f : Y ⟶ V) [IsProper f]
    {m : ℕ} {A : Divisor Y} (hA : IsRelativelyAmpleCartier f A) (d : Fin m → ℤ)
    (D : Fin m → Divisor Y) (hAD : A = ∑ j, d j • D j) (U : V.Opens)
    (hD : ∀ v ∈ U, ∀ j, ∃ W : V.Opens, v ∈ W ∧ W ≤ U ∧ ∃ ψ : (RationalFunctions Y)ˣ,
      Divisor.IsLocalEquation (D j) (f ⁻¹ᵁ W) ψ) :
    ∀ v ∈ U, ∃ W : V.Opens, v ∈ W ∧ W ≤ U ∧ IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) := by
  intro v hv
  choose W hvW hWU ψ hψ using hD v hv
  let W₀ : V.Opens := U ⊓ (Finset.univ : Finset (Fin m)).inf W
  have hvW₀ : v ∈ W₀ := ⟨hv, Finset.inf_induction (p := fun U : V.Opens => v ∈ U) trivial
    (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) fun j _ => hvW j⟩
  have hW₀ : ∀ j, W₀ ≤ W j := fun j =>
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ j))
  have hloc₀ : ∀ t : Finset (Fin m), Divisor.IsLocalEquation (∑ j ∈ t, d j • D j)
      (f ⁻¹ᵁ W₀) (∏ j ∈ t, ψ j ^ d j) := by
    intro t
    induction t using Finset.cons_induction with
    | empty => simpa using Divisor.isLocalEquation_zero (f ⁻¹ᵁ W₀)
    | cons j t hj ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      exact (((hψ j).mono (f.preimage_mono (hW₀ j))).zsmul (d j)).add ih
  obtain ⟨W', hW', hvW', hW'W⟩ := exists_isAffineOpen_mem_and_subset hvW₀
  have hloc : Divisor.IsLocalEquation A (f ⁻¹ᵁ W') (∏ j, ψ j ^ d j) := by
    rw [hAD]
    exact (hloc₀ Finset.univ).mono (f.preimage_mono hW'W)
  have := isQuasiAffine_preimage_of_isLocalEquation' f hA hW' hloc
  haveI : IsAffine W'.toScheme := hW'
  exact ⟨W', hvW', hW'W.trans inf_le_left, hW',
    isAffine_of_isQuasiAffine_of_universallyClosed (f ∣_ W')⟩

/-- Over an open `V ⊆ Z` on which the flip `φ⁺` is an isomorphism, the contraction `φ` is an
isomorphism too. Write `-E = ∑ sᵢ Aᵢ` with `Aᵢ` `φ`-ample Cartier and `g_* E = ∑ rⱼ Dⱼ` with `Dⱼ`
Cartier on `X⁺`. Since `g` matches the prime divisors of `X` and `X⁺` compatibly with the
valuations of `K(Z)`, local equations of `Dⱼ` over `V ≅ φ⁺⁻¹(V)`, read in `K(X)`, are local
equations of the corresponding divisors `Dⱼ'` on `X` near the fibres of `φ` over `V`. Clearing
denominators, a positive integer combination of the `Aᵢ` is an integer combination of the `Dⱼ'`,
so a `φ`-ample Cartier divisor is principal over small affine opens of `V`; hence `φ ∣_ V` is
affine, so finite, and a finite birational morphism onto a normal scheme is an isomorphism. -/
private theorem isIso_morphismRestrict_of_isIso_morphismRestrict_flip
    {k : Type u} [Field k] {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {E : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g)
    (V : Z.Opens) [IsIso (φp ∣_ V)] : IsIso (φ ∣_ V) := by
  haveI := hflip.isNormalVariety_target.isLocallyNoetherian
  haveI : IsNormal Z := hflip.isNormalVariety_target.2
  haveI := hflip.isProper
  haveI := hflip.isContraction.isProper
  haveI := hflip.isNormalVariety_source.1.toIsIntegral
  haveI := hflip.isNormalVariety_target.1.toIsIntegral
  haveI := hflip.isNormalVariety_flip.1.toIsIntegral
  rcases isEmpty_or_nonempty V with hVe | hVne
  · haveI : IsEmpty (φ ⁻¹ᵁ V) := ⟨fun x => hVe.false ⟨_, x.2⟩⟩
    exact isIso_of_isEmpty _
  have : IsSeparated sZ := hflip.isNormalVariety_target.1.toIsSeparated
  have := isSeparated_terminal sZ
  have : IsSeparated sX := hflip.isNormalVariety_source.1.toIsSeparated
  have := isSeparated_terminal sX
  have : IsSeparated sX' := hflip.isNormalVariety_flip.1.toIsSeparated
  have := isSeparated_terminal sX'
  haveI hφs := hflip.isSmall_source.toIsBirationalContraction.surjective_and_isBirational.1
  haveI hφps := hflip.isSmall.toIsBirationalContraction.surjective_and_isBirational.1
  have hφpb : IsBirationalMorphism φp := hflip.isSmall.isBirationalMorphism _ _
  have he := (MMP.Flips.exceptional_hasNonemptyCenter_iff_of_isSmall sX sX' sZ φ φp
    hflip.isSmall_source hflip.isSmall).2 g hflip.isModificationOf
  set e := MMP.Flips.primeDivisorEquivOfModification
    hflip.isSmall_source hflip.isSmall hflip.isModificationOf
  have hgen : ∀ Q : MMP.Mori.PrimeDivisor X',
      φ (e.symm Q).genericPoint = φp Q.genericPoint := fun Q => by
    simpa only [e.apply_symm_apply] using
      (map_genericPoint_eq_of_transformPrimeDivisor_eq_some hflip.isModificationOf.2
        (he (e.symm Q)).1).symm
  have hval : ∀ P : MMP.Mori.PrimeDivisor X',
      (e.symm P).divisorialValuation.comap (functionFieldMap φ) =
        P.divisorialValuation.comap (functionFieldMap φp) := fun P => by
    simpa only [e.apply_symm_apply] using (he (e.symm P)).2.symm
  obtain ⟨n, s, A, hn1, hs, hA, hAE⟩ := hflip.isRelativelyAntiAmple
  obtain ⟨m, r, D, hD, hDE⟩ := hflip.isCartierCombination_transform
  let D' : Fin m → Divisor X := fun j => Finsupp.equivMapDomain e.symm (D j)
  have hD' : ∀ j Q, (D' j).coeff (e.symm Q) = (D j).coeff Q := fun j Q => by
    change Finsupp.equivMapDomain e.symm (D j) (e.symm Q) = D j Q
    simp
  have hcoeff : ∀ p, ∑ i, s i * (A i p : ℝ) = ∑ j, (-r j) * (D' j p : ℝ) := by
    intro p
    have h1 := congrArg (fun F : RDivisor X => F p) hAE
    have h2 := congrArg (fun F : RDivisor X' => F (e p)) hDE
    have h3 : MMP.Mori.RationalMap.transformDivisor g (QDivisor.toRDivisor E) (e p) =
        QDivisor.toRDivisor E p := mapPrimeDivisors_apply_of_eq_some e (fun P => (he P).1) _ p
    have h4 : ∀ j, D' j p = D j (e p) := fun j => by
      change Finsupp.equivMapDomain e.symm (D j) p = _
      simp
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.neg_apply]
      at h1 h2
    simp only [h4, neg_mul, Finset.sum_neg_distrib]
    exact h1.symm.trans (congrArg Neg.neg (h3.symm.trans h2))
  obtain ⟨c, hc, d, hrel⟩ := exists_pos_int_relation s hs (fun j => -r j)
    (fun i p => A i p) (fun j p => D' j p) hcoeff
  have hA' : IsRelativelyAmpleCartier φ (∑ i, c i • A i) :=
    isRelativelyAmpleCartier_sum' φ hn1 hA hc
  have hA'eq : ∑ i, c i • A i = ∑ j, d j • D' j :=
    Finsupp.ext fun p => by simpa [Finsupp.finsetSum_apply] using hrel p
  haveI : IsNoetherian X := {}
  exact isIso_morphismRestrict_of_forall_isAffineOpen_preimage hflip.isSmall_source
    hflip.isNormalVariety_target V <| exists_isAffineOpen_preimage_of_isLocalEquation φ hA' d D'
      hA'eq V fun v hv j =>
        exists_isLocalEquation_of_coeff_eq hφpb e.symm hgen hval V (hD j) (hD' j) v hv

/-- For a flip `φ⁺` of a small contraction `φ` with respect to a `ℚ`-Cartier divisor, the image
of the exceptional locus of `φ` lies in the image of the exceptional locus of `φ⁺`. -/
private theorem image_exceptionalLocus_subset_image_flip
    {k : Type u} [Field k] {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {E : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g) :
    φ '' {y | ∃ C ∈ irreducibleComponents (φ ⁻¹' {φ y}),
        (⟨y, rfl⟩ : φ ⁻¹' {φ y}) ∈ C ∧ 0 < topologicalKrullDim C} ⊆
      φp '' {y | ∃ C ∈ irreducibleComponents (φp ⁻¹' {φp y}),
        (⟨y, rfl⟩ : φp ⁻¹' {φp y}) ∈ C ∧ 0 < topologicalKrullDim C} := by
  haveI := hflip.isProper
  obtain ⟨hV, -, hiso⟩ := isIso_morphismRestrict_compl_image_exceptionalLocus sX' sZ
    hflip.isSmall.isVariety_source hflip.isNormalVariety_target φp
    hflip.isSmall.comp_eq (hflip.isSmall.isBirationalMorphism _ _)
  haveI : IsIso (φ ∣_ ⟨_, hV⟩) := isIso_morphismRestrict_of_isIso_morphismRestrict_flip hflip _
  rintro _ ⟨x, hx, rfl⟩
  by_contra h
  exact image_notMem_of_isIso_morphismRestrict φ ⟨_, hV⟩ hx h

/-- In a sequence of log flips `S` starting from `(X₀, B₀)`, for every `i` with `i + 1 < L` the
flip `φ_i⁺ = S.flip i` and the contraction `φ_i = S.contraction i` have the same image of their
exceptional loci in `Z_i`: `φ_i⁺(Ex(φ_i⁺)) = φ_i(Ex(φ_i))`, where `Ex(f)` is the set of points of
the source lying on an irreducible component of positive dimension of their fibre. -/
@[mmp "lem_fa7_flip_exceptional_images_agree"]
public theorem SequenceOfLogFlips.image_exceptionalLocus_flip_eq {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    let Ex : ∀ {Y Z : Scheme.{u}}, (Y ⟶ Z) → Set Y := fun {_ _} f =>
      {y | ∃ C ∈ irreducibleComponents (f ⁻¹' {f y}),
        (⟨y, rfl⟩ : f ⁻¹' {f y}) ∈ C ∧ 0 < topologicalKrullDim C}
    S.flip i '' Ex (S.flip i) = S.contraction i '' Ex (S.contraction i) := by
  intro Ex
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.compactSpace_model i
  haveI := S.isLocallyNoetherian_model (i + 1)
  haveI := S.isNormal_model (i + 1)
  haveI := S.compactSpace_model (i + 1)
  haveI := S.isLocallyNoetherian_base i
  haveI := S.isNormal_base i
  have hE := (S.isExtremalRayContraction i hi).isQCartier
  have heq : QDivisor.toRDivisor (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2) =
      logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2) := by
    unfold logCanonicalDivisor
    rw [map_add]
    congr 1
    ext
    simp [QDivisor.toRDivisor, Divisor.toQDivisor, Divisor.toRDivisor]
  have hflip := S.isFlip i hi
  rw [← heq] at hflip
  exact Set.Subset.antisymm (image_exceptionalLocus_flip_subset hE hflip)
    (image_exceptionalLocus_subset_image_flip hflip)

/-! ### A log flip is an isomorphism off the exceptional loci -/

/-- If `q` is an isomorphism over the open `V`, two maps into the source of `q` which agree
after `q` and land over `V` are equal. -/
public lemma eq_of_comp_eq_of_isIso_morphismRestrict {T Y Z : Scheme.{u}} (q : Y ⟶ Z)
    (V : Z.Opens) [IsIso (q ∣_ V)] {a₁ a₂ : T ⟶ Y} (c : T ⟶ V) (h₁ : a₁ ≫ q = c ≫ V.ι)
    (h₂ : a₂ ≫ q = c ≫ V.ι) : a₁ = a₂ := by
  have hP := isPullback_morphismRestrict q V
  have key : ∀ a : T ⟶ Y, a ≫ q = c ≫ V.ι → a = (c ≫ inv (q ∣_ V)) ≫ (q ⁻¹ᵁ V).ι := by
    intro a ha
    rw [← hP.lift_snd c a ha.symm]
    congr 1
    rw [← cancel_mono (q ∣_ V)]
    simp
  exact (key a₁ h₁).trans (key a₂ h₂).symm

/-- A birational morphism locally of finite type from a nonempty scheme has a point lying on no
positive-dimensional irreducible component of its fibre. -/
private lemma exists_notMem_exceptionalLocus {Y Z : Scheme.{u}} [Nonempty Y] (f : Y ⟶ Z)
    [LocallyOfFiniteType f] (hf : IsBirationalMorphism f) :
    ∃ y, y ∉ {y | ∃ C ∈ irreducibleComponents (f ⁻¹' {f y}),
      (⟨y, rfl⟩ : f ⁻¹' {f y}) ∈ C ∧ 0 < topologicalKrullDim C} := by
  obtain ⟨W, ⟨x, hx⟩, hW⟩ := hf.exists_isOpenImmersion
  have hq : f.QuasiFiniteAt x :=
    Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion (f := W.ι) (x := ⟨x, hx⟩) |>.mp
      ((W.ι ≫ f).quasiFiniteAt _)
  have hclopen := (isClopen_singleton_fiber_iff_quasiFiniteAt f x).mpr hq
  refine ⟨x, ?_⟩
  rintro ⟨C, hC, hxC, hdim⟩
  have hsub : C ⊆ {(⟨x, rfl⟩ : f ⁻¹' {f x})} :=
    (IsIrreducible.isConnected hC.1).isPreconnected.subset_isClopen hclopen
      ⟨_, hxC, Set.mem_singleton _⟩
  have : Subsingleton C := (Set.subsingleton_singleton.anti hsub).coe_sort
  have : DiscreteTopology C := Subsingleton.discreteTopology
  exact hdim.not_ge (topologicalKrullDim_zero_of_discreteTopology C)

/-- **A rational map over `Z` is determined where `q` is an isomorphism.** Let `X` be
integral, `θ : X ⤏ Y` a rational map with `q ∘ θ = p`, and `V ⊆ Z` an open over which `q` is an
isomorphism and whose preimage under `p` is dense. Then any `f : p⁻¹(V) ⟶ q⁻¹(V)` over `V`
represents `θ`: both agree after `q` at the generic point of `X`, which lies over `V`. -/
public lemma toRationalMap_eq_of_comp_morphismRestrict_eq {X Y Z : Scheme.{u}} [IsIntegral X]
    {p : X ⟶ Z} {q : Y ⟶ Z} {V : Z.Opens} [IsIso (q ∣_ V)] (hd : Dense (p ⁻¹ᵁ V : Set X))
    {f : (p ⁻¹ᵁ V).toScheme ⟶ q ⁻¹ᵁ V} (hf : f ≫ q ∣_ V = p ∣_ V) {θ : X.RationalMap Y}
    (hθ : θ.compHom q = p.toRationalMap) :
    (Scheme.PartialMap.mk (p ⁻¹ᵁ V) hd (f ≫ (q ⁻¹ᵁ V).ι)).toRationalMap = θ := by
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  have hη : genericPoint X ∈ p ⁻¹ᵁ V :=
    (genericPoint_specializes _).mem_open (p ⁻¹ᵁ V).2 hd.nonempty.choose_spec
  refine eq_of_comp_eq_of_isIso_morphismRestrict q V
    (((p ⁻¹ᵁ V).fromSpecStalkOfMem _ hη) ≫ p ∣_ V) ?_ ?_
  · rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
    simp only [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem,
      Category.assoc, ← morphismRestrict_ι, reassoc_of% hf]
  · rw [← MMP.Flips.RationalMap.fromFunctionField_compHom, hθ,
      MMP.Flips.RationalMap.fromFunctionField_hom, Category.assoc, morphismRestrict_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι_assoc]

/-- In a sequence of log flips `S`, for every `i` with `i + 1 < L`, let `φ_i = S.contraction i`,
`φ_i⁺ = S.flip i`, `θ_i = S.flipMap i`, and let `V = Z_i ∖ φ_i(Ex φ_i)`, where `Ex(f)` is the set
of points of the source lying on an irreducible component of positive dimension of their fibre.
Then `V` is open, `φ_i⁻¹(V) = X_i ∖ Ex(φ_i)`, `φ_i⁺⁻¹(V) = X_{i+1} ∖ Ex(φ_i⁺)`, and there is an
isomorphism `e : φ_i⁻¹(V) ≅ φ_i⁺⁻¹(V)` over `V` which is the restriction of `θ_i`. -/
@[mmp "lem_fa7_flip_iso_off_exceptional_loci"]
public theorem SequenceOfLogFlips.exists_iso_compl_exceptionalLocus_flipMap {k : Type u}
    [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    let Ex : ∀ {Y Z : Scheme.{u}}, (Y ⟶ Z) → Set Y := fun {_ _} f =>
      {y | ∃ C ∈ irreducibleComponents (f ⁻¹' {f y}),
        (⟨y, rfl⟩ : f ⁻¹' {f y}) ∈ C ∧ 0 < topologicalKrullDim C}
    ∃ hV : IsOpen (S.contraction i '' Ex (S.contraction i))ᶜ,
      S.contraction i ⁻¹' (S.contraction i '' Ex (S.contraction i))ᶜ = (Ex (S.contraction i))ᶜ ∧
      S.flip i ⁻¹' (S.contraction i '' Ex (S.contraction i))ᶜ = (Ex (S.flip i))ᶜ ∧
      ∃ (hd : Dense ((S.contraction i ⁻¹ᵁ ⟨_, hV⟩ : (S.model i).1.Opens) : Set (S.model i).1))
        (e : (S.contraction i ⁻¹ᵁ ⟨_, hV⟩).toScheme ≅ (S.flip i ⁻¹ᵁ ⟨_, hV⟩).toScheme),
        e.hom ≫ (S.flip i ∣_ ⟨_, hV⟩) = S.contraction i ∣_ ⟨_, hV⟩ ∧
        (Scheme.PartialMap.mk (S.contraction i ⁻¹ᵁ ⟨_, hV⟩) hd
          (e.hom ≫ (S.flip i ⁻¹ᵁ ⟨_, hV⟩).ι)).toRationalMap = S.flipMap i := by
  intro Ex
  have hfC : MMP.Flips.IsSmall k (S.baseStr i) (S.model i).2.1 (S.contraction i) := S.isSmall i hi
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have hF := S.isFlip i hi
  have hG := hF.isSmall
  have hZ := hF.isNormalVariety_target
  have : IsProper (S.contraction i) := hfC.isProper
  have : IsProper (S.flip i) := hG.isProper
  have : IsIntegral (S.model i).1 := hfC.isVariety_source.toIsIntegral
  obtain ⟨hV, h1, h2⟩ := isIso_morphismRestrict_compl_image_exceptionalLocus _ _
    hfC.isVariety_source hZ (S.contraction i) hfC.comp_eq hfC.isBirationalMorphism
  obtain ⟨hV', h1', h2'⟩ := isIso_morphismRestrict_compl_image_exceptionalLocus _ _
    hG.isVariety_source hZ (S.flip i) hG.comp_eq hG.isBirationalMorphism
  have hagree : (S.flip i) '' Ex (S.flip i) = (S.contraction i) '' Ex (S.contraction i) :=
    S.image_exceptionalLocus_flip_eq i hi
  set V : (S.base i).Opens := ⟨_, hV⟩
  have hVV : (⟨_, hV'⟩ : (S.base i).Opens) = V := TopologicalSpace.Opens.ext (by
    change ((S.flip i) '' Ex (S.flip i))ᶜ = ((S.contraction i) '' Ex (S.contraction i))ᶜ
    rw [hagree])
  rw [hVV] at h2'
  refine ⟨hV, h1, ?_, ?_⟩
  · rwa [← hagree]
  obtain ⟨y, hy⟩ := exists_notMem_exceptionalLocus (S.contraction i) hfC.isBirationalMorphism
  have hd : Dense (((S.contraction i) ⁻¹ᵁ V : (S.model i).1.Opens) : Set (S.model i).1) :=
    ((S.contraction i) ⁻¹ᵁ V).isOpen.dense ⟨y, by
      change y ∈ (S.contraction i) ⁻¹' ((S.contraction i) '' Ex (S.contraction i))ᶜ
      rwa [h1]⟩
  let e := asIso ((S.contraction i) ∣_ V) ≪≫ (asIso ((S.flip i) ∣_ V)).symm
  have he : e.hom ≫ ((S.flip i) ∣_ V) = (S.contraction i) ∣_ V := by simp [e]
  exact ⟨hd, e, he, toRationalMap_eq_of_comp_morphismRestrict_eq hd he hF.isModificationOf.2⟩

end MMP.Flips

end
