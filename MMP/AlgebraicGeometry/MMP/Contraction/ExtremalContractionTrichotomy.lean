module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.ExceptionalSetPrimeDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Exceptional sets of extremal contractions

Two results on contractions with one-dimensional relative Néron–Severi space.

If `φ : V ⟶ W` is a projective birational contraction of a `ℚ`-factorial variety onto a normal
variety with relative Picard number `ρ(V/W) = 1` and `φ` is not small, then its exceptional set
`Ex(φ)` is a prime divisor `F` (Kollár et al., FA 6.5): `F` is an exceptional prime divisor inside
`Ex(φ)`, it is negative on some contracted curve, hence (as `N¹(V/W)` is a line) on every one, so
every contracted curve lies in `F`, and contracted curves sweep out `Ex(φ)`.

The contraction `f : X ⟶ Y` of an extremal ray of a normal projective `ℚ`-factorial variety is
exactly one of: of fiber type, divisorial, or small (Kollár–Mori 2.5). If `dim Y = dim X`, generic
finiteness of fibres and `f_* 𝒪_X = 𝒪_Y` make `f` birational; then either `Ex(f)` has codimension
at least two, or it contains a prime divisor, which is all of `Ex(f)` by `ℚ`-factoriality.

## Main results

* `MMP.Flips.exists_primeDivisor_exceptionalSet_eq_support_of_not_isSmall`: the exceptional set of
  a non-small divisorial extremal contraction is a prime divisor.
* `MMP.Mori.IsContractionOfFace.trichotomy_of_isExtremalRay`: the trichotomy of extremal
  contractions.

## Implementation notes

The relative Picard number is `MMP.Flips.relativePicardNumber`; FA 6.5 is stated over any field
rather than `ℂ`. "Exactly one of three" is the disjunction of the three cases together with the
three pairwise exclusions. Each result's auxiliary lemmas live in a namespace `Proof_<tag>`,
opened only for that result.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 6.5
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Proposition 2.5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_fa6_extremal_birational_contraction_divisor

open MMP.Mori MMP.Flips

/-- The exceptional set `Ex(f)` (points with no neighbourhood on which `f` is an open immersion)
is contained in the complement of the preimage of the biregular locus of `f`. -/
private theorem exceptionalSet_subset {X Y : Scheme.{u}} (f : Y ⟶ X) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set Y) := by
  intro y hy
  by_contra hyM
  apply hy
  have : IsIso (f ∣_ biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  refine ⟨f ⁻¹ᵁ biregularLocus f, ?_, ?_⟩
  · by_contra h
    exact hyM (MMP.Mori.mem_exceptionalSet.mpr h)
  · rw [← morphismRestrict_ι]
    infer_instance

/-- In a Noetherian quasi-sober space, a closed connected set `F` that meets a closed set `S`
without lying in it contains a point outside `S` specializing to a point of `S`. -/
private theorem exists_specializes_of_isConnected {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] {F S : Set Y} (hF : IsClosed F)
    (hFc : IsConnected F) (hS : IsClosed S) (hmeet : (F ∩ S).Nonempty) (hsub : ¬ F ⊆ S) :
    ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
  set T := F \ S
  obtain ⟨s, hsT, hsS⟩ : (closure T ∩ S).Nonempty := by
    obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
    obtain ⟨w, -, hw⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
      isClosed_closure hS (fun a ha => (em (a ∈ S)).symm.imp
        (fun haS => subset_closure (show a ∈ T from ⟨ha, haS⟩)) id)
      ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
    exact ⟨w, hw⟩
  obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure : IsClosed (closure T))
  have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
    refine closure_minimal (fun y hy => ?_) ?_
    · obtain ⟨z, hz, hyz⟩ : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
      exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
    · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
  obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
  have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
  exact ⟨ζ, closure_minimal Set.sdiff_subset hF (hzT hζ.mem),
    fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS), s, hsS, hζ.specializes hsz⟩

/-- The fibre of a proper morphism `f` of `k`-schemes of finite type over a closed point is proper
over `k`. -/
private theorem isProper_fiberι_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsProper f] (hX : IsNormalVariety k sX) (x : X)
    (hx : IsClosed ({x} : Set X)) : IsProper (f.fiberι x ≫ f ≫ sX) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  rw [Scheme.Hom.fiber_fac_assoc]
  infer_instance

/-- An injective morphism `ι : W ⟶ Y` to a separated `k`-scheme of finite type maps a proper curve
of `W` onto a proper curve of `Y`. -/
private theorem isProperCurve_of_injective {k : Type u} [Field k] {W Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] (ι : W ⟶ Y)
    (hι : Function.Injective ι) (C : ProperCurve (ι ≫ sY)) : IsProperCurve sY (ι C.point) := by
  have hφsY : (C.ι ≫ ι) ≫ sY = C.ι ≫ ι ≫ sY := Category.assoc _ _ _
  have : AlgebraicGeometry.IsCurve k ((C.ι ≫ ι) ≫ sY) := hφsY ▸ C.isCurve
  have : IsProper ((C.ι ≫ ι) ≫ sY) := by
    rw [hφsY]
    infer_instance
  have hnc : ¬ ∃ z, Set.range (C.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    have : Subsingleton C.scheme := ⟨fun a b => C.ι.isEmbedding.injective (hι (by
      have ha : (C.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
      have hb : (C.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
      simpa using ha.trans hb.symm))⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
    rw [C.dim_eq] at h0
    exact absurd h0 (by decide)
  have hker := C.ker_comp ι
  constructor
  · have h1 := (MMP.Mori.isCurve_imageι_comp sY (C.ι ≫ ι) hnc).topologicalKrullDim_eq_one
    change topologicalKrullDim (C.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  · have h1 : IsProper ((C.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve contracted by `f` that meets `S`. -/
private theorem exists_properCurve_isContractedBy {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : ProperCurve sY, C.IsContractedBy f ∧ (Set.range C.ι ∩ S).Nonempty := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsSeparated sY := hY.1.toIsSeparated
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ := exists_specializes_of_isConnected hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  let ι := f.fiberι x
  let sF := ι ≫ sY
  have : IsProper sF := by simpa [sF, ι, hf] using isProper_fiberι_comp sX f hX x hx
  have : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {x} := f.range_fiberι x
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηF
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpF
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by
    rwa [← hemb.isInducing.specializes_iff, hη', hp']
  have hp'c : IsClosed ({p'} : Set (f.fiber x)) := by
    have : ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} := by
      ext z
      simp [← hp', hemb.injective.eq_iff]
    rw [this]
    exact (mem_closedPoints_iff.mp hpc).preimage ι.continuous
  obtain ⟨y', -, hy'p', hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  let C' : ProperCurve sF := ⟨y', hy'⟩
  have hrange : Set.range (C'.ι ≫ ι) = closure {ι y'} := C'.range_comp ι rfl
  let C : ProperCurve sY := ⟨ι y', isProperCurve_of_injective sY ι ι.isEmbedding.injective C'⟩
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
  refine ⟨C, hCf, p, ?_, hpS⟩
  rw [hrC, ← hp']
  exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

/-- **Every closed point of the exceptional set lies on a contracted curve.** For a proper
birational morphism `f : Y ⟶ X` of normal varieties with `f_* 𝒪_Y = 𝒪_X`, every closed point
`y ∈ Ex(f)` lies on a proper curve contracted by `f`. -/
private theorem exists_properCurve_mem_closure {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (hO : ∀ U : X.Opens, IsIso (f.app U)) {y : Y} (hyc : IsClosed ({y} : Set Y))
    (hy : y ∈ MMP.Mori.exceptionalSet f) :
    ∃ C : ProperCurve sY, C.IsContractedBy f ∧ y ∈ closure {C.point} := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨C₀, -, -, hdim, hyC₀, w, hw⟩ :=
    exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hY.1 hX.1 f hf hfb hO
      hyc hy
  obtain rfl : w = f y := ((Set.eq_singleton_iff_unique_mem.mp hw).2 _ ⟨y, hyC₀, rfl⟩).symm
  have hC₀F : C₀ ⊆ f.base ⁻¹' {f y} := fun z hz => hw ▸ ⟨z, hz, rfl⟩
  have hsub : ¬ f.base ⁻¹' {f y} ⊆ {y} := by
    intro h
    obtain rfl : C₀ = {y} := (hC₀F.trans h).antisymm (Set.singleton_subset_iff.mpr hyC₀)
    have : Subsingleton ({y} : Set Y) := Set.subsingleton_singleton.coe_sort
    have : DiscreteTopology ({y} : Set Y) := ⟨Subsingleton.elim _ _⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({y} : Set Y)
    rw [hdim] at h0
    exact absurd h0 (by decide)
  have hxc : IsClosed ({f y} : Set X) := Set.image_singleton (f := f) ▸ f.isClosedMap _ hyc
  obtain ⟨C, hC, z, hz, rfl⟩ := exists_properCurve_isContractedBy sX sY hX hY f hf hfb (f y) hxc
    hyc ⟨y, rfl, rfl⟩ hsub
  exact ⟨C, hC, C.range_ι ▸ hz⟩

/-- **A relatively ample divisor from a projective morphism.** If `f : X ⟶ Y` is projective and
`X` integral, some Cartier divisor `A` on `X` has positive degree on every proper curve contracted
by `f`. -/
private theorem exists_cartierDivisor_intersectionNumber_pos {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] (f : X ⟶ Y)
    (hf : IsProjectiveMorphism f) :
    ∃ A : X.CartierDivisor, ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 < (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ A) := by
  obtain ⟨⟨L, hL, hamp, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple (IsProjectiveMorphism.isProjective hf)
  obtain ⟨A, ⟨e⟩⟩ := hA inferInstance
  refine ⟨A, fun C hC => ?_⟩
  have hrel : MMP.Mori.IsRelativelyAmple f L := fun y => by
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨U, hU, hyU, hamp.2 U hU⟩
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f L
    hrel C hC
  rw [ProperCurve.degree, degreeOn_eq_of_iso k sX C.ι C.dim_le e]
  exact_mod_cast hpos

/-- **Negativity spreads along a ray.** Let `f : X ⟶ Y` be projective with `N¹(X/Y)` a line. If
an effective `ℚ`-Cartier `ℚ`-divisor `G` is negative on one contracted curve, it is numerically a
negative multiple of an `f`-ample divisor, hence negative on every contracted curve, so every
contracted curve lies in `Supp G`. -/
private theorem mem_supp_of_finrank_eq_one {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    [IsIntegral X] (f : X ⟶ Y) (hf : IsProjectiveMorphism f)
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1) {G : QDivisor X}
    (hG : G.IsQCartier) (hG0 : 0 ≤ G) {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (hneg : G.intersectionNumber k sX C₀.ι C₀.dim_le hG < 0) {C : ProperCurve sX}
    (hC : C.IsContractedBy f) : C.point ∈ G.supp := by
  obtain ⟨A, hA⟩ := exists_cartierDivisor_intersectionNumber_pos sX f hf
  obtain ⟨δ, hδ⟩ := exists_kCartierDivisor_intersectionNumber_eq sX G hG
  obtain ⟨c, hc⟩ := exists_intersectionNumber_eq_mul_of_finrank_eq_one f hfin _ δ hC₀
    (hA C₀ hC₀).ne'
  have key : ∀ C : ProperCurve sX, C.IsContractedBy f →
      (G.intersectionNumber k sX C.ι C.dim_le hG : ℝ) =
        c * (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ A) :=
    fun C hC => (hδ C).symm.trans (hc C hC)
  have hc0 : c < 0 := neg_of_mul_neg_left (key C₀ hC₀ ▸ by exact_mod_cast hneg) (hA C₀ hC₀).le
  by_contra hCG
  have h := (MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sX G hG hG0 C hCG).1
  have : (G.intersectionNumber k sX C.ι C.dim_le hG : ℝ) < 0 :=
    key C hC ▸ mul_neg_of_neg_of_pos hc0 (hA C hC)
  exact this.not_ge (by exact_mod_cast h)

/-- **A non-small birational contraction has an exceptional divisor in its exceptional set.** If
`φ : V ⟶ W` is a birational contraction of normal varieties that is not small, some prime divisor
`F` of `V` with `F ⊆ Ex(φ)` is exceptional over `W`. -/
private theorem exists_isExceptionalPrimeDivisor_support_subset {k : Type u} [Field k]
    {V W : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k)) [IsLocallyNoetherian V]
    [IsNormal V] (hVn : IsNormalVariety k sV) (hW : IsNormalVariety k sW) (φ : V ⟶ W)
    (hφ : IsBirationalContraction k sW sV φ) (hs : ¬ IsSmall k sW sV φ) :
    ∃ F : MMP.Mori.PrimeDivisor V, F.support ⊆ MMP.Flips.exceptionalSet φ ∧
      IsExceptionalPrimeDivisor sW φ F := by
  have : IsIntegral V := hVn.1.toIsIntegral
  have : IsIntegral W := hW.1.toIsIntegral
  have : IsNormal W := hW.2
  have : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  have hφs : φ ≫ sW = sV := hφ.comp_eq
  have := hφ.isProper
  obtain ⟨hsurj, hbir⟩ := hφ.surjective_and_isBirational
  obtain ⟨-, V', hV', hV'b⟩ := isIso_app_and_exists_isBiregular_of_isBirationalMorphism hW φ
    (hφs ▸ hVn.1) hbir
  have hEx : ∀ y ∈ MMP.Flips.exceptionalSet φ, 2 ≤ Order.coheight (φ y) := fun y hy => by
    by_contra h
    exact MMP.Mori.mem_exceptionalSet.mp (exceptionalSet_subset φ hy) (le_biregularLocus hV'b
      (by_contra fun hw => h (le_closedsCodimension_iff_le_coheight.mp hV' _ hw)))
  have hns : ¬ 2 ≤ closedsCodimension (exceptionalCloseds φ) := fun h =>
    hs ((isSmall_iff_two_le_closedsCodimension_exceptionalSet hφ).mpr h)
  rw [le_closedsCodimension_iff_le_coheight] at hns
  push Not at hns
  obtain ⟨y, hyEx, hy2⟩ := hns
  have hy0 : Order.coheight y ≠ 0 := by
    intro h0
    have hgEx : genericPoint V ∈ MMP.Flips.exceptionalSet φ :=
      (Order.coheight_eq_zero.mp h0 (genericPoint_specializes y)).mem_closed
        (MMP.Flips.isClosed_exceptionalSet φ) hyEx
    obtain ⟨z, hz⟩ := hsurj.surj (genericPoint W)
    have h2 := hEx z ((genericPoint_specializes z).mem_closed
      (MMP.Flips.isClosed_exceptionalSet φ) hgEx)
    rw [hz, Order.coheight_eq_zero.mpr fun b _ => genericPoint_specializes b] at h2
    exact absurd h2 (by decide)
  have hy1 : Order.coheight y = 1 := by
    generalize Order.coheight y = n at hy0 hy2 ⊢
    lift n to ℕ using hy2.ne_top
    norm_cast at hy0 hy2 ⊢
    omega
  have hFgen := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy1
  refine ⟨.ofCoheightOne y hy1, ?_, ⟨hφs ▸ hVn, hbir, inferInstance, ?_⟩⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hFgen]
    exact closure_minimal (Set.singleton_subset_iff.mpr hyEx) (MMP.Flips.isClosed_exceptionalSet φ)
  · by_contra hne
    exact ProperDivisorOver.not_two_le_coheight_of_not_isExceptional _ hne
      (by simpa [hFgen] using hEx y hyEx)

/-- **An exceptional prime divisor is not relatively nef.** If `F` is a `ℚ`-Cartier prime divisor
exceptional over `W`, then `F · C₀ < 0` for some curve `C₀` contracted by `φ`. -/
private theorem exists_intersectionNumber_single_neg {k : Type u} [Field k] {V W : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k)) [QuasiCompact sV] [IsLocallyNoetherian V]
    [IsNormal V] (hVn : IsNormalVariety k sV) (hW : IsNormalVariety k sW) (φ : V ⟶ W)
    (hφs : φ ≫ sW = sV) [IsProper φ] (hbir : IsBirationalMorphism φ)
    {F : MMP.Mori.PrimeDivisor V} (hF : IsExceptionalPrimeDivisor sW φ F)
    (hG : (show QDivisor V from Finsupp.single F 1).IsQCartier) :
    ∃ C₀ : ProperCurve sV, C₀.IsContractedBy φ ∧
      (show QDivisor V from Finsupp.single F 1).intersectionNumber k sV C₀.ι C₀.dim_le hG < 0 := by
  by_contra h
  push Not at h
  have h0 := QDivisor.eq_zero_of_isEffective_of_isRelativelyNef k sW sV hW hVn φ hφs hbir hG
    (fun P hP => Finsupp.single_eq_of_ne fun h => hP (h ▸ hF))
    (DivisorWithCoeffs.isEffective_iff_nonneg.mpr (Finsupp.single_nonneg.mpr zero_le_one))
    (MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV hG h)
  simpa using congrArg (fun D : QDivisor V => D F) h0

/-- **The exceptional set is swept out by contracted curves.** If a closed set `Z` contains every
proper curve contracted by `f`, then `Ex(f) ⊆ Z`. -/
private theorem exceptionalSet_subset_of_forall_isContractedBy {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
    [IsLocallyNoetherian Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (hO : ∀ U : X.Opens, IsIso (f.app U)) {Z : Set Y} (hZ : IsClosed Z)
    (hCZ : ∀ C : ProperCurve sY, C.IsContractedBy f → C.point ∈ Z) :
    MMP.Flips.exceptionalSet f ⊆ Z := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  rw [← closure_inter_closedPoints (MMP.Flips.isClosed_exceptionalSet f)]
  refine closure_minimal (fun y ⟨hyEx, hyc⟩ => ?_) hZ
  obtain ⟨C, hC, hyC⟩ := exists_properCurve_mem_closure sX sY hX hY f hf hfb hO
    (mem_closedPoints_iff.mp hyc) (exceptionalSet_subset f hyEx)
  exact closure_minimal (Set.singleton_subset_iff.mpr (hCZ C hC)) hZ hyC

end Proof_lem_fa6_extremal_birational_contraction_divisor

namespace MMP.Flips

open Proof_lem_fa6_extremal_birational_contraction_divisor

/-- **The exceptional locus of a divisorial extremal contraction** (FA 6.5). Let `V` be a
`ℚ`-factorial variety over `k` and `φ : V ⟶ W` a projective birational contraction onto a normal
variety with `ρ(V/W) = 1`. If `φ` is not small, then `Ex(φ)` is a prime divisor of `V`. -/
@[mmp "lem_fa6_extremal_birational_contraction_divisor"]
public theorem exists_primeDivisor_exceptionalSet_eq_support_of_not_isSmall
    {k : Type u} [Field k] {V W : Scheme.{u}} (sV : V ⟶ Spec (.of k))
    (sW : W ⟶ Spec (.of k)) [IsLocallyNoetherian V] [IsNormal V]
    (hV : MMP.Fourfold.IsQFactorial sV) (hW : Mori.IsNormalVariety k sW) (φ : V ⟶ W)
    (hφ : IsBirationalContraction k sW sV φ) (hφp : IsProjectiveMorphism φ)
    (hρ : relativePicardNumber sV φ = 1) (hs : ¬ IsSmall k sW sV φ) :
    ∃ F : Mori.PrimeDivisor V, exceptionalSet φ = F.support := by
  open MMP.Mori in
  have : IsIntegral V := hV.1.1.toIsIntegral
  have : QuasiCompact sV := hV.1.1.toQuasiCompact
  have := hφ.isProper
  have hbir := hφ.surjective_and_isBirational.2
  obtain ⟨F, hFsub, hFexc⟩ :=
    exists_isExceptionalPrimeDivisor_support_subset sV sW hV.1 hW φ hφ hs
  have hG := MMP.Fourfold.isQCartier_of_isQFactorial sV hV (Finsupp.single F (1 : ℚ))
  obtain ⟨C₀, hC₀, hneg⟩ :=
    exists_intersectionNumber_single_neg sV sW hV.1 hW φ hφ.comp_eq hbir hFexc hG
  have hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sV φ) = 1 :=
    Module.finrank_eq_of_rank_eq (by rw [Cardinal.toENat_eq_one.mp hρ]; rfl)
  have hO := (isIso_app_and_exists_isBiregular_of_isBirationalMorphism hW φ
    (hφ.comp_eq ▸ hV.1.1) hbir).1
  refine ⟨F, (exceptionalSet_subset_of_forall_isContractedBy sW sV hW hV.1 φ hφ.comp_eq hbir hO
    (F.support_eq_closure ▸ isClosed_closure) fun C hC => ?_).antisymm hFsub⟩
  exact DivisorWithCoeffs.supp_single_le F (1 : ℚ) (mem_supp_of_finrank_eq_one sV φ hφp hfin hG
    (Finsupp.single_nonneg.mpr zero_le_one) hC₀ hneg hC)

end MMP.Flips

namespace Proof_prop_km2a_extremal_contraction_trichotomy

open MMP.Mori TopologicalSpace

/-- A quasi-sober space all of whose irreducible components have dimension at most `0` has
dimension at most `0`: a strict inclusion `B ⊊ C` of irreducible closed subsets would give, inside
an irreducible component `Z ⊇ C`, the strict inclusion of the closures of their generic points. -/
private theorem topologicalKrullDim_le_zero_of_forall_mem_irreducibleComponents
    {T : Type*} [TopologicalSpace T] [QuasiSober T]
    (h : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z ≤ 0) :
    topologicalKrullDim T ≤ 0 := by
  rw [topologicalKrullDim, Order.krullDim_nonpos_iff_forall_isMax]
  intro B C hBC
  by_contra hCB
  obtain ⟨Z, hZ, hCZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ C.isIrreducible
  have hc := C.isIrreducible.isGenericPoint_genericPoint_closure
  have hb := B.isIrreducible.isGenericPoint_genericPoint_closure
  rw [C.isClosed.closure_eq] at hc
  rw [B.isClosed.closure_eq] at hb
  set c := C.isIrreducible.genericPoint
  set b := B.isIrreducible.genericPoint
  have hbC : b ∈ (C : Set T) := hBC hb.mem
  have hcb : c ⤳ b := hc.specializes hbC
  have hbc : ¬ b ⤳ c := fun h => hCB fun z hz => by
    have hcB : c ∈ (B : Set T) := hb.specializes_iff_mem.mp h
    exact (B.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hcB))
      (hc.def ▸ hz)
  let b' : Z := ⟨b, hCZ hbC⟩
  let c' : Z := ⟨c, hCZ hc.mem⟩
  have hc'b' : c' ⤳ b' := Topology.IsInducing.subtypeVal.specializes_iff.mp hcb
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp (h Z hZ)
    (IrreducibleCloseds.closureSingleton b')
  have hle : IrreducibleCloseds.closureSingleton b' ≤ IrreducibleCloseds.closureSingleton c' := by
    change closure {b'} ⊆ closure {c'}
    exact specializes_iff_closure_subset.mp hc'b'
  exact hbc (Topology.IsInducing.subtypeVal.specializes_iff.mpr
    (specializes_iff_mem_closure.mpr (hmax hle (subset_closure rfl))))

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` is an isomorphism on sections over every open and finite over an open `V`, then every
point of `V` lies in the biregular locus of `f`. -/
private theorem mem_biregularLocus_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hO : ∀ U : Y.Opens, IsIso (f.app U)) {V : Y.Opens} (hV : IsFinite (f ∣_ V)) {y : Y}
    (hy : y ∈ V) : y ∈ biregularLocus f := by
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := V) hy
  have e := morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr (show U ≤ V from hUV)] at e
  have hfin : IsFinite (f ∣_ U) :=
    (MorphismProperty.arrow_mk_iso_iff @IsFinite e).mp inferInstance
  have : IsAffine U := hU
  have hbir : IsBiregular f U := by
    change MorphismProperty.isomorphisms Scheme (f ∣_ U)
    rw [HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)]
    refine ⟨isAffine_of_isAffineHom (f ∣_ U), ?_⟩
    rw [morphismRestrict_appTop]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hO _)
      (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U ⊤)).op).isIso_hom
  exact le_biregularLocus hbir hyU

/-- If `a + b = c` with `c ≤ b` and `c` neither `⊥` nor `⊤`, then `a ≤ 0`. -/
private theorem nonpos_of_add_eq_of_le {a b c : WithBot ℕ∞} (hc : c ≠ ⊤) (hc' : c ≠ ⊥)
    (h : a + b = c) (hcb : c ≤ b) : a ≤ 0 := by
  lift c to ℕ∞ using hc'
  lift c to ℕ using by simpa using hc
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
  induction b using WithBot.recBotCoe with
  | bot => simp at hcb
  | coe b =>
  norm_cast at h hcb ⊢
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe a =>
  induction b using ENat.recTopCoe with
  | top => simp at h
  | coe b =>
  norm_cast at h hcb ⊢
  omega

/-- **Generic finiteness of fibres.** A dominant morphism `f : X ⟶ Y` of varieties over `k` with
`dim X ≤ dim Y` has a finite fibre: over a dense open of `Y` every component of a fibre has
dimension `dim X - dim Y ≤ 0`. -/
private theorem exists_finite_preimage_singleton {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sX]
    [AlgebraicGeometry.IsVariety k sY]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f] [QuasiCompact f] (hf : f ≫ sY = sX)
    (hdim : topologicalKrullDim X ≤ topologicalKrullDim Y) : ∃ y : Y, (f ⁻¹' {y}).Finite := by
  have : IsIntegral X := AlgebraicGeometry.IsVariety.toIsIntegral (f := sX)
  have : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (f := sY)
  obtain ⟨-, ⟨W, hWd, hW⟩, -⟩ := MMP.topologicalKrullDim_fiber_of_isDominant k sX sY f hf
  obtain ⟨y, hyW⟩ := hWd.nonempty
  refine ⟨y, MMP.Resolution.Bridges.finite_preimage_singleton_of_topologicalKrullDim_le f y ?_⟩
  rw [← IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph]
  exact topologicalKrullDim_le_zero_of_forall_mem_irreducibleComponents fun Z hZ =>
    nonpos_of_add_eq_of_le (topologicalKrullDim_lt_top_of_isIntegral k sX (𝟙 X)).ne
      (Order.krullDim_ne_bot_iff.mpr
        ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩)
      (hW y hyW Z hZ) hdim

/-- A morphism of irreducible schemes whose biregular locus meets its image is birational. -/
private theorem isBirationalMorphism_of_mem_biregularLocus {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) {x : X} (hx : f x ∈ biregularLocus f) :
    IsBirationalMorphism f := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f _ _ ⟨x, hx⟩ ⟨f x, hx⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- The support of a prime divisor has codimension one. -/
private theorem closedsCodimension_eq_one {X : Scheme.{u}} {Z : Closeds X}
    (E : MMP.Mori.PrimeDivisor X) (hZ : (Z : Set X) = E.support) : closedsCodimension Z = 1 := by
  have : Z = ⟨_, (IrreducibleCloseds.closureSingleton E.genericPoint).isClosed⟩ := by
    ext1
    rw [hZ, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rfl
  rw [this, closedsCodimension_coe]
  exact E.codimension_closure_genericPoint

/-- On an irreducible scheme, a proper closed subset of codimension `< 2` contains a prime
divisor: a point of it of coheight `< 2` is not the generic point, so has coheight one. -/
private theorem exists_primeDivisor_support_subset {X : Scheme.{u}} [IrreducibleSpace X]
    {Z : Closeds X} {x : X} (hx : x ∉ Z) (hZ : closedsCodimension Z < 2) :
    ∃ E : MMP.Mori.PrimeDivisor X, E.support ⊆ (Z : Set X) := by
  obtain ⟨z, hzZ, hz⟩ : ∃ z ∈ (Z : Set X), Order.coheight z < 2 := by
    simpa using mt MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr hZ.not_ge
  have hz0 : Order.coheight z ≠ 0 := fun h0 => hx <| by
    have h1 : z ⤳ genericPoint X := Order.coheight_eq_zero.mp h0
      ((genericPoint_spec X).specializes (Set.mem_univ z))
    exact (h1.trans ((genericPoint_spec X).specializes (Set.mem_univ x))).mem_closed Z.isClosed hzZ
  have h1 : Order.coheight z = 1 := by
    generalize Order.coheight z = d at *
    lift d to ℕ using hz.ne_top
    norm_cast at hz hz0 ⊢
    omega
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne z h1, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hzZ)

end Proof_prop_km2a_extremal_contraction_trichotomy

namespace MMP.Mori

open Proof_prop_km2a_extremal_contraction_trichotomy

/-- **Trichotomy of extremal contractions.** Let `X` be a normal projective `ℚ`-factorial variety
over `k` and `f : X ⟶ Y` a contraction of an extremal ray `R ⊆ NE̅(X)`. Then exactly one of the
following holds: `f` is of fiber type (`MMP.Mori.IsFiberTypeContraction`), `f` is a divisorial
contraction (`MMP.Mori.IsDivisorialContraction`), `f` is a small contraction
(`MMP.Mori.IsSmallContraction`). -/
@[mmp "prop_km2a_extremal_contraction_trichotomy"]
public theorem IsContractionOfFace.trichotomy_of_isExtremalRay
    {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Fourfold.IsQFactorial sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {f : X ⟶ Y} (hf : IsContractionOfFace k sX sY R f) :
    (IsFiberTypeContraction k sX sY R f ∨ IsDivisorialContraction k sX sY R f ∨
        IsSmallContraction k sX sY R f) ∧
      ¬ (IsFiberTypeContraction k sX sY R f ∧ IsDivisorialContraction k sX sY R f) ∧
      ¬ (IsFiberTypeContraction k sX sY R f ∧ IsSmallContraction k sX sY R f) ∧
      ¬ (IsDivisorialContraction k sX sY R f ∧ IsSmallContraction k sX sY R f) := by
  have hpX := hf.isProjectiveVariety_source
  have hpY := hf.isProjectiveVariety_target
  have : AlgebraicGeometry.IsVariety k sX := hpX.toIsVariety
  have : AlgebraicGeometry.IsVariety k sY := hpY.toIsVariety
  have : IsIntegral X := hpX.toIsVariety.toIsIntegral
  have : IsIntegral Y := hpY.toIsVariety.toIsIntegral
  have hNV : IsNormalVariety k sX := ⟨hpX.toIsVariety, inferInstance⟩
  have : IsProper (f ≫ sY) := hf.comp_eq ▸ inferInstance
  have : IsProper f := IsProper.of_comp f sY
  have : Surjective f := Scheme.Hom.surjective_of_isIso_app f hf.isIso_app
  have hdim (hb : IsBirationalMorphism f) : topologicalKrullDim Y = topologicalKrullDim X :=
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY sX hb
  refine ⟨?_, fun ⟨h1, h2⟩ => (hdim h2.isBirationalMorphism ▸ h1.dim_lt).false,
    fun ⟨h1, h2⟩ => (hdim h2.isBirationalMorphism ▸ h1.dim_lt).false, fun ⟨h1, h2⟩ => by
      obtain ⟨E, hE⟩ := h1.exists_primeDivisor
      have := h2.two_le_codimension
      rw [closedsCodimension_eq_one E hE] at this
      exact absurd this (by decide)⟩
  by_cases hlt : topologicalKrullDim Y < topologicalKrullDim X
  · exact .inl ⟨hNV, hR, hf, hlt⟩
  obtain ⟨y, hy⟩ := exists_finite_preimage_singleton f hf.comp_eq (not_lt.mp hlt)
  obtain ⟨x, rfl⟩ := f.surjective y
  obtain ⟨_, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f _ hy
  have hx := mem_biregularLocus_of_isFinite f hf.isIso_app hV hyV
  have hbir := isBirationalMorphism_of_mem_biregularLocus f hx
  by_cases h2 : 2 ≤ closedsCodimension (exceptionalSet f)
  · exact .inr (.inr ⟨hNV, hR, hf, hbir, h2⟩)
  obtain ⟨E, hE⟩ := exists_primeDivisor_support_subset (not_not.mpr hx) (not_le.mp h2)
  exact .inr (.inl ⟨hNV, hR, hf, hbir, E,
    (support_eq_exceptionalSet_of_isContractionOfFace hX hR hf hbir E hE).symm⟩)

end MMP.Mori

end
