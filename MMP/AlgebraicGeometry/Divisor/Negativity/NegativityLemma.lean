module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.AntiAmpleExceptional
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyQuasiAffineHom
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupEtaleChartTransfer
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import MMP.AlgebraicGeometry.Intersection.ProperCurveDegree
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Chow.FieldSituation
import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.Descent

/-!
# The negativity lemma and nonnegativity of exceptional coefficients

Let `f : Y ⟶ X` be a proper birational morphism of normal varieties over a field `k`. The
negativity lemma says that an `ℝ`-Cartier divisor `B` on `Y` with `-B` `f`-nef and `f_*B`
effective is itself effective, when `f` is projective. As a consequence, if `f^*L ≡_f M + B` with
`M` `f`-nef and the coefficients of `B` along the non-exceptional prime divisors nonnegative, then
`B` is effective. Both proofs work over an affine open of `X`, with an effective Cartier divisor
`W` such that `-W` is relatively ample (Kollár 2.9), and the largest `t` with `B|_V + tW`
effective; the second first reduces to `f` projective by the Chow lemma.

## Main results

* `MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback`: the exceptional coefficients
  in a relative numerical equivalence `f^*L ≡_f M + B` are nonnegative.
* `MMP.Flips.isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor`: the negativity
  lemma.

## Implementation notes

The auxiliary lemmas of each proof live in the namespace `Proof_<tag>` named after its label. The
first proof carries its own form of the negativity lemma over an arbitrary field (with `f`
projective in the sense of `IsProjective`), as its statement has no characteristic hypothesis;
the push-forward `f_*B` is `MMP.Mori.RationalMap.transformDivisor` of `B` along
`f.toRationalMap`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.19, 2.19.1
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], 3.39
* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 2.9
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_fa2_negativity_coefficients_nonneg

section Helpers

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
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
private theorem isCurve_comp_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) [IsDominant f] [LocallyOfFiniteType f]
    (hf : IsBirationalMorphism f) : degreeOver f = 1 := by
  let := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
  have hc2 : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := C.isCurve
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
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

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  have : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
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
      isBirationalMorphism := isBirationalMorphism_of_isBirational _
        (Scheme.isBirational_normalization C.scheme hX) }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  have : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

/-- An effective `ℝ`-divisor `D = ∑ s_j M_j + t N`, presented by Cartier divisors, has `D · C ≥ 0`
on every proper curve `C` not contained in `Supp D`. -/
private theorem sum_degreeOn_add_nonneg (hX : IsNormalVariety k sX) (C : ProperCurve sX) {n : ℕ}
    (s : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ j, (M j).IsCartier) (t : ℝ) (N : Divisor X)
    (hN : N.IsCartier)
    (hD : (∑ j, s j • Divisor.toRDivisor (M j) + t • Divisor.toRDivisor N).IsEffective)
    (hC : C.point ∉ (∑ j, s j • Divisor.toRDivisor (M j) + t • Divisor.toRDivisor N).supp) :
    0 ≤ ∑ j, s j * ((M j).degreeOn k sX C.ι C.dim_le (hM j) : ℝ) +
      t * (N.degreeOn k sX C.ι C.dim_le hN : ℝ) := by
  let s' : Fin (n + 1) → ℝ := Fin.snoc s t
  let M' : Fin (n + 1) → Divisor X := Fin.snoc M N
  have hM' : ∀ j, (M' j).IsCartier :=
    Fin.lastCases (by simpa [M'] using hN) fun j => by simpa [M'] using hM j
  have hDM : ∑ j, s j • Divisor.toRDivisor (M j) + t • Divisor.toRDivisor N =
      ∑ j, s' j • Divisor.toRDivisor (M' j) := by
    simp [Fin.sum_univ_castSucc, s', M']
  rw [hDM] at hD hC
  have h := IsRIntersectionNumber.nonneg_of_isEffective k sX hX _ ⟨_, s', M', hM', rfl⟩ hD C hC s'
    M' (isRIntersectionNumber_sum_degreeOn k sX C s' M' hM')
  simpa [Fin.sum_univ_castSucc, s', M'] using h

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
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsSeparated sY := hY.1.toIsSeparated
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  have key : ∀ {F S : Set Y}, IsClosed F → _root_.IsConnected F → IsClosed S →
      (F ∩ S).Nonempty → ¬ F ⊆ S → ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
    intro F S hF hFc hS hmeet hsub
    set T := F \ S
    have hTF : closure T ⊆ F := closure_minimal Set.sdiff_subset hF
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
  have : IsProper sF := by
    have h : sF = f.fiberToSpecResidueField x ≫ (X.fromSpecResidueField x ≫ sX) := by
      simp only [sF, ι, ← hf, Scheme.Hom.fiber_fac_assoc]
    rw [h]
    have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
    have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp hx
    have : IsFinite (X.fromSpecResidueField x ≫ sX) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
    have : IsProper (f.fiberToSpecResidueField x) :=
      inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
    have : IsProper (X.fromSpecResidueField x ≫ sX) := inferInstance
    infer_instance
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
  let C' : MMP.Mori.ProperCurve sF := ⟨y', hy'⟩
  -- its image in `Y` is a proper curve of `Y`
  have hφsY : (C'.ι ≫ ι) ≫ sY = C'.ι ≫ sF := Category.assoc _ _ _
  have : AlgebraicGeometry.IsCurve k ((C'.ι ≫ ι) ≫ sY) := hφsY ▸ C'.isCurve
  have : IsProper ((C'.ι ≫ ι) ≫ sY) := by rw [hφsY]; infer_instance
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
    have : Subsingleton (f.base ⁻¹' {f z}) := hss.coe_sort
    exact absurd (topologicalKrullDim_zero_of_discreteTopology _) (not_le.mpr hzE)
  obtain ⟨C, hCf, -, w, hw, hwz⟩ := exists_properCurve_isContractedBy k sX sY hX hY f hf hfb
    (f z) hx hz ⟨z, rfl, rfl⟩ hsub
  refine ⟨C, hCf, ?_⟩
  rw [Set.mem_singleton_iff.mp hwz, C.range_ι] at hw
  exact specializes_iff_mem_closure.mpr hw

/-- **Negative coefficients lie over the exceptional locus.** Let `f : Y ⟶ X` be a proper
birational morphism of normal varieties and `B` an `ℝ`-divisor on `Y` with `f_* B` effective.
If `B` has a negative coefficient along the prime divisor `P`, then `f` maps the generic point of
`P` outside the biregular locus of `f`: over the biregular locus `f(P)` would be a prime divisor
of `X` whose coefficient in `f_* B` is that of `P` in `B`. -/
private theorem map_genericPoint_notMem_biregularLocus {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) [IsProper f] (hfb : IsBirationalMorphism f)
    {B : RDivisor Y}
    (hpush : (MMP.Mori.RationalMap.transformDivisor f.toRationalMap B).IsEffective)
    {P : MMP.Mori.PrimeDivisor Y} (hP : B.coeff P < 0) :
    f P.genericPoint ∉ biregularLocus f := by
  intro hmem
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hmem]
    exact P.coheight_genericPoint
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : MMP.Mori.PrimeDivisor.genericPoint Q = f P.genericPoint :=
    PrimeDivisor.genericPoint_ofCoheightOne _ hco
  obtain ⟨E, hE, -, hcoeff⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hfb Q
  have hEQ : f E.genericPoint = f P.genericPoint := hE.trans hQ
  have hEP : E = P := by
    have h1 : f E.genericPoint ∈ biregularLocus f := by rwa [hEQ]
    apply PrimeDivisor.genericPoint_injective
    exact (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f h1 hmem
      (by rw [hEQ])).antisymm
      (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f hmem h1 (by rw [hEQ])) |>.eq
  have h := hpush Q
  rw [DivisorWithCoeffs.coeff_apply, hcoeff B, hEP] at h
  exact absurd h (not_le.mpr hP)

/-- **Degrees can be computed on an open subscheme.** Let `V ⊆ Y` be an integral open subscheme,
`L` a Cartier divisor on `Y` and `C` a proper curve of `Y` lying in `V`, which is the proper curve
`C_V` of `V`. Then the degree of the restriction `L|_V` (the pull-back along `V ⟶ Y`) along `C_V`
is the degree of `L` along `C`. -/
private theorem degreeOn_pullback_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (V : Y.Opens) [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {L : Divisor Y} (hL : L.IsCartier)
    (hB : ∀ Z : irreducibleComponents V, V.ι (componentGenericPoint V Z) ∉ L.supp)
    (C : ProperCurve sY) (CV : ProperCurve (V.ι ≫ sY)) (hC : V.ι CV.point = C.point)
    (hCV : closure ({C.point} : Set Y) ⊆ V) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    (L.pullback hL hB).degreeOn k (V.ι ≫ sY) CV.ι CV.dim_le (hL.isCartier_pullback V.ι hB) =
      L.degreeOn k sY C.ι C.dim_le hL := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hL.isInvertibleModule_divisorialSheaf
  have hLV := hL.isCartier_pullback V.ι hB
  have := hLV.isInvertibleModule_divisorialSheaf
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso V.ι CV.point hC (by
    rwa [Scheme.Opens.range_ι])
  have : IsProper ((CV.ι ≫ V.ι) ≫ sY) := by rw [Category.assoc]; infer_instance
  have h1 := MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sY C.ι (CV.ι ≫ V.ι) C.dim_le
    CV.dim_le e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact he.symm) L.divisorialSheaf
  have h2 := MMP.Threefold.Resolution.degreeOn_comp k sY V.ι CV.ι CV.dim_le L.divisorialSheaf
  obtain ⟨e₂⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hL V.ι hB
  have h3 := MMP.Mori.degreeOn_eq_of_iso k (V.ι ≫ sY) CV.ι CV.dim_le e₂
  exact (h1.trans (h2.trans h3.symm)).symm

/-- **An effective Cartier divisor negative on the contracted curves over an affine open.** Let
`f : Y ⟶ X` be a projective birational morphism of normal varieties and `U ⊆ X` an affine open
with `V = f⁻¹(U)` nonempty. There is an effective Cartier divisor `W` on `V` with `W · C < 0` for
every proper curve `C ⊆ V` contracted by `f`: as `U` is quasi-projective, Kollár 2.9 gives `W`
with `-W` relatively ample over `U`. -/
private theorem exists_isCartier_degreeOn_neg (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian X]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (f : Y ⟶ X)
    [IsProper f] (hfb : IsBirationalMorphism f) (U : X.Opens) (hU : IsAffineOpen U)
    (hproj : IsProjectiveMorphism (f ∣_ U)) [Nonempty (f ⁻¹ᵁ U)] [IsLocallyNoetherian (f ⁻¹ᵁ U)]
    [IsNormal (f ⁻¹ᵁ U)] [CompactSpace (f ⁻¹ᵁ U)] [QuasiCompact ((f ⁻¹ᵁ U).ι ≫ sY)] :
    ∃ W : Divisor (f ⁻¹ᵁ U), 0 ≤ W ∧ ∃ hW : W.IsCartier,
      ∀ C : ProperCurve ((f ⁻¹ᵁ U).ι ≫ sY), C.IsContractedBy (f ∣_ U) →
        W.degreeOn k ((f ⁻¹ᵁ U).ι ≫ sY) C.ι C.dim_le hW < 0 := by
  set V := f ⁻¹ᵁ U
  set f' : V.toScheme ⟶ U.toScheme := f ∣_ U
  have hι : ∀ y, U.ι (f' y) = f (V.ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  obtain ⟨y₀⟩ := ‹Nonempty V›
  have : Nonempty U := ⟨f' y₀⟩
  have := hX.1
  have := hY.1
  have hYV := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sY V
  have hXU := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sX U
  have : IsAffine U := hU
  have : LocallyOfFiniteType (U.ι ≫ sX) := hXU.toLocallyOfFiniteType
  have hXqp : Stacks.HProjective.IsHQuasiProjective (U.ι ≫ sX) := by
    open Stacks.HQuasiProjectiveDimensionOne in exact isHQuasiProjective_of_isAffine_toSpec _
  -- `f'` is finite over a neighbourhood of the generic point
  have hgf : ∃ W : U.toScheme.Opens, ((W : Set U) ∩ Set.range f'.base).Nonempty ∧
      IsFinite (f' ∣_ W) := by
    have : IsIntegral V.toScheme := hYV.toIsIntegral
    have : IsIntegral U.toScheme := hXU.toIsIntegral
    have : IsIntegral X := hX.1.toIsIntegral
    have : IsIntegral Y := hY.1.toIsIntegral
    have hpre := preimage_genericPoint f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
    have hηU : U.ι (genericPoint U) = genericPoint X :=
      Stacks.Intersection.RationalEquivalenceProduct.genericPoint_image_of_isOpenImmersion U.ι
    have hηV : V.ι (genericPoint V) = genericPoint Y :=
      Stacks.Intersection.RationalEquivalenceProduct.genericPoint_image_of_isOpenImmersion V.ι
    have hfη : f (genericPoint Y) = genericPoint X := by
      have : genericPoint Y ∈ f.base ⁻¹' {genericPoint X} := by rw [hpre]; rfl
      exact this
    have hmem : ∀ y : V.toScheme, f' y = genericPoint U → V.ι y = genericPoint Y := by
      intro y hy
      have h : V.ι y ∈ f.base ⁻¹' {genericPoint X} := by
        change f (V.ι y) = genericPoint X
        rw [← hι, hy, hηU]
      rw [hpre] at h
      exact h
    have hfin : (f'.base ⁻¹' {genericPoint U}).Finite := by
      refine Set.Subsingleton.finite fun y₁ hy₁ y₂ hy₂ => V.ι.isOpenEmbedding.injective ?_
      exact (hmem y₁ hy₁).trans (hmem y₂ hy₂).symm
    obtain ⟨W, hW, hfinW⟩ : ∃ W : U.toScheme.Opens, genericPoint U ∈ W ∧ IsFinite (f' ∣_ W) := by
      open MMP.Threefold.Mori MMP.Threefold.Resolution in
      exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton f' _ hfin
    refine ⟨W, ⟨genericPoint U, hW, genericPoint V, ?_⟩, hfinW⟩
    apply U.ι.isOpenEmbedding.injective
    rw [hι, hηV, hfη, hηU]
  obtain ⟨W, hW0, hWc, hamp⟩ :=
    MMP.Threefold.Resolution.exists_isCartier_isRelativelyAmple_neg_of_isProjectiveMorphism
      hYV hXU hXqp hproj hgf
  refine ⟨W, hW0, hWc, fun C hC => ?_⟩
  have := hWc.neg.isInvertibleModule_divisorialSheaf
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hYV f'
    (-W).divisorialSheaf hamp C hC
  have hneg := Divisor.degreeOn_neg' k (V.ι ≫ sY) C.ι C.dim_le W hWc
  change 0 < (-W).degreeOn k (V.ι ≫ sY) C.ι C.dim_le hWc.neg at hpos
  rw [hneg] at hpos
  change W.degreeOn k (V.ι ≫ sY) C.ι C.dim_le hWc < 0
  omega

/-- The generic point of a prime divisor `E` lies outside the support of every divisor in which
`E` has coefficient zero. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {D : DivisorWithCoeffs R Y}
    {E : MMP.Mori.PrimeDivisor Y} (hDE : D.coeff E = 0) : E.genericPoint ∉ D.supp := by
  intro h
  obtain ⟨E', hE', hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E hmem] at hE'
  exact hE' hDE

/-- If `W ≥ 0` is positive along every prime divisor where the `ℝ`-divisor `B` is negative, and
`B` is negative somewhere, then there is `t > 0` (take `t` maximal) with `B + t W` effective and
a prime divisor along which `B` is negative but `B + t W` has coefficient zero. -/
private theorem exists_isEffective_add_smul_coeff_eq_zero {Y : Scheme.{u}} (B : RDivisor Y)
    {W : Divisor Y} (hW0 : 0 ≤ W) (hW : ∀ E, B.coeff E < 0 → 0 < W.coeff E)
    {E₀ : MMP.Mori.PrimeDivisor Y} (hE₀ : B.coeff E₀ < 0) :
    ∃ t : ℝ, 0 < t ∧ (B + t • Divisor.toRDivisor W).IsEffective ∧
      ∃ E, B.coeff E < 0 ∧ (B + t • Divisor.toRDivisor W).coeff E = 0 := by
  classical
  have hS : ∀ E, E ∈ B.support.filter (B.coeff · < 0) ↔ B.coeff E < 0 := fun E => by
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  obtain ⟨E₁, hE₁, hmax⟩ := (B.support.filter (B.coeff · < 0)).exists_max_image
    (fun E => -B.coeff E / (W.coeff E : ℝ)) ⟨E₀, (hS E₀).2 hE₀⟩
  rw [hS] at hE₁
  have hW₁ : (0 : ℝ) < W.coeff E₁ := by exact_mod_cast hW E₁ hE₁
  have ht : 0 < -B.coeff E₁ / W.coeff E₁ := div_pos (neg_pos.mpr hE₁) hW₁
  have hcoeff : ∀ (t : ℝ) E,
      (B + t • Divisor.toRDivisor W).coeff E = B.coeff E + t * W.coeff E := fun t E => by
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
  refine ⟨_, ht, fun E => ?_, E₁, hE₁, ?_⟩
  · rw [hcoeff]
    by_cases h : B.coeff E < 0
    · have hWE : (0 : ℝ) < W.coeff E := by exact_mod_cast hW E h
      linarith [(div_le_iff₀ hWE).mp (hmax E ((hS E).2 h))]
    · have : (0 : ℝ) ≤ W.coeff E := by exact_mod_cast hW0 E
      nlinarith [not_lt.mp h]
  · rw [hcoeff]
    field_simp
    ring

/-- **A contracted curve meets every neighbourhood of a negative component.** Let `f : Y ⟶ X` be
a proper birational morphism of normal varieties and `B` an `ℝ`-divisor on `Y` with `f_* B`
effective. If `B` has a negative coefficient along `P`, then every open set `O` meeting `P`
contains a closed point lying on a proper curve contracted by `f`. -/
private theorem exists_properCurve_specializes_of_coeff_neg (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    [IsProper f] (hfb : IsBirationalMorphism f) {B : RDivisor Y}
    (hpush : (MMP.Mori.RationalMap.transformDivisor f.toRationalMap B).IsEffective)
    {P : MMP.Mori.PrimeDivisor Y} (hP : B.coeff P < 0) {O : Set Y} (hO : IsOpen O)
    (hPO : P.genericPoint ∈ O) :
    ∃ C : ProperCurve sY, C.IsContractedBy f ∧ ∃ z ∈ O, C.point ⤳ z := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have hA := map_genericPoint_notMem_biregularLocus hX (hf ▸ hY) hfb hpush hP
  obtain ⟨z, ⟨hzP, hzO⟩, hzc⟩ := nonempty_inter_closedPoints
    (show (closure {P.genericPoint} ∩ O).Nonempty from ⟨_, subset_closure rfl, hPO⟩)
    (isClosed_closure.isLocallyClosed.inter hO.isLocallyClosed)
  have hzf : f z ∉ biregularLocus f := fun h => hA
    (((specializes_iff_mem_closure.mpr hzP).map f.continuous).mem_open (biregularLocus f).isOpen h)
  obtain ⟨C, hCf, hCz⟩ :=
    exists_properCurve_specializes k sX sY hX hY f hf hfb z (mem_closedPoints_iff.mp hzc) hzf
  exact ⟨C, hCf, z, hzO, hCz⟩

end Helpers

section Reduction

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- A prime divisor `F` of `Y` whose image `g(η_F)` has coheight one in the normal variety `X`
is not exceptional over `X`. -/
private theorem not_isExceptionalPrimeDivisor_of_coheight_eq_one {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (F : MMP.Mori.PrimeDivisor Y) (hF : Order.coheight (g F.genericPoint) = 1) :
    ¬ IsExceptionalPrimeDivisor sX g F := by
  rintro ⟨hY, hg, hp, hexc⟩
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  unfold ProperDivisorOver.IsExceptional at hexc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hn] at hexc
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  have h2 := (withBot_add_two_le_iff hd).mp hexc
  change 2 ≤ Order.coheight (g F.genericPoint) at h2
  rw [hF] at h2
  exact absurd h2 (by decide)

/-- The pull-back `f^*L` of a Cartier divisor has degree zero on every curve contracted by `f`. -/
private theorem degreeOn_eq_zero_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sY] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) (hf : f ≫ sX = sY)
    {L₀ : Divisor X} (hL₀ : L₀.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L₀.supp}
    {L₁ : Divisor Y} (hp : L₀.IsPullback f hB L₁) (hc : L₁.IsCartier) (C : ProperCurve sY)
    (hC : C.IsContractedBy f) : L₁.degreeOn k sY C.ι C.dim_le hc = 0 := by
  obtain rfl := Divisor.IsPullback.pullback_eq hL₀ hp
  exact Divisor.degreeOn_pullback_eq_zero_of_isContractedBy f hf hL₀ hB C hC

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_left (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero_of_not_isProperCurve {k : Type u} [Field k]
    {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_right hc, map_zero]

/-- **`B · C ≤ 0` on contracted curves.** If `f^*L ≡_f M + B` with `M` `f`-nef, then
`B · C = f^*L · C - M · C = -M · C ≤ 0` on every proper curve `C` contracted by `f`, computed from
any presentation `B = ∑ s_j N_j` by Cartier divisors. -/
private theorem sum_degreeOn_nonpos_of_isNumericallyEquivalentOver {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sX]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [QuasiCompact sY] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} (hf : f ≫ sX = sY) {L : RDivisor X} {L' : RDivisor Y}
    (hL' : IsRCartierPullback f L L') {M : RDivisor Y} (hMnef : IsRelativelyNef k sY f M)
    {B : RDivisor Y} (hnum : IsNumericallyEquivalentOver k sY f L' (M + B)) {m : ℕ}
    (s : Fin m → ℝ) (N : Fin m → Divisor Y) (hN : ∀ j, (N j).IsCartier)
    (hB : B = ∑ j, s j • Divisor.toRDivisor (N j)) (C : ProperCurve sY)
    (hC : C.IsContractedBy f) :
    ∑ j, s j * ((N j).degreeOn k sY C.ι C.dim_le (hN j) : ℝ) ≤ 0 := by
  obtain ⟨mL, rL, L₀, L₁, hL₀, -, hpb, rfl⟩ := hL'
  have hL₁c : ∀ j, (L₁ j).IsCartier := fun j => by
    obtain ⟨hBj, hj⟩ := hpb j
    rw [← Divisor.IsPullback.pullback_eq (hL₀ j) hj]
    exact (hL₀ j).isCartier_pullback f hBj
  have hLx : IsRIntersectionNumber k sY (∑ j, rL j • Divisor.toRDivisor (L₁ j)) rL L₁ C 0 := by
    convert isRIntersectionNumber_sum_degreeOn k sY C rL L₁ hL₁c using 1
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [degreeOn_eq_zero_of_isPullback f hf (hL₀ j) (hpb j).2 (hL₁c j) C hC, Int.cast_zero,
      mul_zero]
  obtain ⟨mM, rM, LM, hLM, rfl, hMall⟩ := hMnef
  have hMx := isRIntersectionNumber_sum_degreeOn k sY C rM LM hLM
  have hBx := isRIntersectionNumber_sum_degreeOn k sY C s N hN
  rw [← hB] at hBx
  have hMB := (IsRIntersectionNumber.eq_and_linear k sY C).2 _ B rM LM s N _ _ 1 1 hMx hBx
  rw [one_smul, one_smul] at hMB
  linarith [hnum.2.2 C hC _ rL L₁ 0 _ _ _ _ hLx hMB, hMall C hC _ hMx]

/-- **Pulling back a divisor nonpositive on contracted curves.** Let `h : Y' ⟶ Y` be proper and
`B = ∑ s_j N_j` a combination of Cartier divisors with `B · C ≤ 0` on every curve contracted by
`f : Y ⟶ X`. Then `-h^*B = -∑ s_j h^*N_j` is `(h ≫ f)`-nef: by the projection formula a curve
`C'` contracted by `h ≫ f` has `h^*B · C' = [k(C') : k(h C')] (B · h C')` if `h(C')` is a curve,
which is then contracted by `f`, and `h^*B · C' = 0` if `h(C')` is a point. -/
private theorem isRelativelyNef_neg_sum_pullback {k : Type u} [Field k] {X Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [IsProper h] [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y']
    (f : Y ⟶ X) {m : ℕ} (s : Fin m → ℝ) (N : Fin m → Divisor Y) (hN : ∀ j, (N j).IsCartier)
    (hNB : ∀ j, ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ (N j).supp)
    (hBC : ∀ C : ProperCurve sY, C.IsContractedBy f →
      ∑ j, s j * ((N j).degreeOn k sY C.ι C.dim_le (hN j) : ℝ) ≤ 0) :
    IsRelativelyNef k (h ≫ sY) (h ≫ f)
      (-∑ j, s j • Divisor.toRDivisor ((N j).pullback (hN j) (hNB j))) := by
  have hN'c : ∀ j, ((N j).pullback (hN j) (hNB j)).IsCartier := fun j =>
    (hN j).isCartier_pullback h (hNB j)
  refine ⟨m, fun j => -s j, _, hN'c, by simp [← Finset.sum_neg_distrib], fun C' hC' x hx => ?_⟩
  have hx0 := isRIntersectionNumber_sum_degreeOn k (h ≫ sY) C' (fun j => -s j) _ hN'c
  rw [(IsRIntersectionNumber.eq_and_linear k (h ≫ sY) C').1 _ _ _ _ _ _ _ hx
    (by simpa [← Finset.sum_neg_distrib] using hx0)]
  by_cases hc : IsProperCurve sY (h C'.point)
  · -- `h(C')` is a curve `C`, contracted by `f`
    let C : ProperCurve sY := ⟨_, hc⟩
    have hCf : C.IsContractedBy f := by
      intro y hy
      have hsub : closure ({h C'.point} : Set Y) ⊆ h '' closure ({C'.point} : Set Y') :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
          (h.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      simpa only [Scheme.Hom.comp_apply] using hC' z hz
    simp only [degreeOn_pullback_eq_mul h (hN _) (hNB _) C' C rfl, Int.cast_mul, Int.cast_natCast,
      Finset.sum_neg_distrib, mul_left_comm (s _), ← Finset.mul_sum, neg_nonneg]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hBC C hCf)
  · -- `h(C')` is a point
    simp [degreeOn_pullback_eq_zero_of_not_isProperCurve h (hN _) (hNB _) C' hc]

/-- **The push-forward of a pull-back.** Let `h : Y' ⟶ Y` and `f : Y ⟶ X` be birational
morphisms of normal varieties with `f` and `h ≫ f` proper, and `B'` the pull-back of `B` along
`h`. If `B` is nonnegative along every prime divisor of `Y` not exceptional over `X`, then
`(h ≫ f)_* B'` is effective. For a prime divisor `Q` of `X` with strict transform `E` on `Y'`,
the stalks of `X` at `η_Q` and of `Y` at `h(η_E)` are isomorphic, so `h(η_E)` is the generic point
of a prime divisor `P` of `Y` mapping onto `Q`, and `B'(E) = B(P) ≥ 0`. -/
private theorem isEffective_transformDivisor_comp_of_isRCartierPullback {k : Type u} [Field k]
    {X Y Y' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y']
    (hX : IsNormalVariety k sX) (h : Y' ⟶ Y) (f : Y ⟶ X)
    (hY' : IsNormalVariety k ((h ≫ f) ≫ sX)) [IsProper (h ≫ f)] (hfb : IsBirationalMorphism f)
    (hhb : IsBirationalMorphism h) (hf'b : IsBirationalMorphism (h ≫ f)) {B : RDivisor Y}
    {B' : RDivisor Y'} (hB' : IsRCartierPullback h B B')
    (hBG : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ IsExceptionalPrimeDivisor sX f P → 0 ≤ B.coeff P) :
    (MMP.Mori.RationalMap.transformDivisor (h ≫ f).toRationalMap B').IsEffective := by
  have := hfb.isDominant
  have := hhb.isDominant
  intro Q
  obtain ⟨E, hE, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hY' hf'b Q
  rw [DivisorWithCoeffs.coeff_apply, htr]
  have hfy : f (h E.genericPoint) = Q.genericPoint := by rwa [← Scheme.Hom.comp_apply]
  have := Q.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f (h E.genericPoint))) := by rw [hfy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hfb.functionFieldMap_bijective
    (h E.genericPoint)
  have hco : Order.coheight (h E.genericPoint) = 1 := by
    have h1 := ringKrullDim_eq_of_ringEquiv
      (asIso (f.stalkMap (h E.genericPoint))).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hfy,
      Q.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  set P : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hP : P.genericPoint = h E.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (h E.genericPoint)) := by rw [← hP]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing h hhb.functionFieldMap_bijective
    E.genericPoint
  rw [← DivisorWithCoeffs.coeff_apply, MMP.Fourfold.coeff_eq_of_isRCartierPullback E P hP.symm hB']
  refine hBG P (not_isExceptionalPrimeDivisor_of_coheight_eq_one hX f P ?_)
  rw [hP, hfy]
  exact Q.coheight_genericPoint

end Reduction

section Negativity

/-- **Negativity lemma** over an arbitrary field. Let `f : Y ⟶ X` be a projective birational
morphism of normal varieties over `k` and `B` an `ℝ`-Cartier divisor on `Y` with `-B` `f`-nef and
`f_*B` effective. Then `B` is effective. -/
private theorem isEffective_of_isRelativelyNef_neg_of_forall_isProjectiveMorphism
    (k : Type u) [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f]
    (hproj : ∀ U : X.Opens, IsAffineOpen U → IsProjectiveMorphism (f ∣_ U))
    (hfb : IsBirationalMorphism f)
    {B : RDivisor Y} (hnef : IsRelativelyNef k sY f (-B))
    (hpush : (MMP.Mori.RationalMap.transformDivisor f.toRationalMap B).IsEffective) :
    B.IsEffective := by
  classical
  have := hY.1
  have : IsIntegral Y := hY.1.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨m, r, L, hL, hpres, hall⟩ := hnef
  -- `-B` is `f`-nef: `∑ r_j (L_j · C) ≥ 0` on every contracted curve
  have hN : ∀ C : ProperCurve sY, C.IsContractedBy f →
      0 ≤ ∑ j, r j * ((L j).degreeOn k sY C.ι C.dim_le (hL j) : ℝ) := fun C hC =>
    hall C hC _ (by rw [hpres]; exact isRIntersectionNumber_sum_degreeOn k sY C r L hL)
  have hBpres : B = ∑ j, (-r j) • Divisor.toRDivisor (L j) := by
    rw [← neg_neg B, hpres]
    simp [neg_smul, Finset.sum_neg_distrib]
  intro P₀
  by_contra! hP₀
  -- localize over an affine open `U` meeting `f(P₀)`
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show f P₀.genericPoint ∈ (⊤ : X.Opens) from trivial)
  set V := f ⁻¹ᵁ U
  set f' : V.toScheme ⟶ U.toScheme := f ∣_ U
  have hι : ∀ y, U.ι (f' y) = f (V.ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have : Nonempty V := ⟨⟨P₀.genericPoint, hxU⟩⟩
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨_, hxU⟩)
  have hYV := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sY V
  have : IsIntegral V := hYV.toIsIntegral
  have : IsNormal V := isNormal_of_isOpenImmersion V.ι
  have : IsAffine U := hU
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiCompact (V.ι ≫ sY) := quasiCompact_of_compactSpace _
  have hYVn : IsNormalVariety k (V.ι ≫ sY) := ⟨hYV, inferInstance⟩
  obtain ⟨W, hW0, hWc, hWneg⟩ := exists_isCartier_degreeOn_neg k sX sY hX hY f hfb U hU
    (hproj U hU)
  -- the restriction `B|_V = ∑ (-r_j) L_j|_V`
  have hBj : ∀ j, ∀ Z : irreducibleComponents V, V.ι (componentGenericPoint V Z) ∉ (L j).supp :=
    fun j => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' V.ι (L j)
  let L' : Fin m → Divisor V := fun j => (L j).pullback (hL j) (hBj j)
  have hL' : ∀ j, (L' j).IsCartier := fun j => (hL j).isCartier_pullback V.ι (hBj j)
  set BV : RDivisor V := ∑ j, (-r j) • Divisor.toRDivisor (L' j) with hBVdef
  have hBV : ∀ E, BV.coeff E = B.coeff (OpenWeilRestriction.primeDivisorMap V.ι E) := by
    intro E
    rw [hBVdef, hBpres]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := MMP.Positivity.coeff_eq_of_isPullback E _
      (OpenWeilRestriction.genericPoint_primeDivisorMap V.ι E).symm (hL j)
      (Divisor.isPullback_pullback (hL j) (hBj j))
    simp only [DivisorWithCoeffs.coeff_apply] at this
    change -r j * ((L' j E : ℤ) : ℝ) = -r j * ((L j _ : ℤ) : ℝ)
    rw [this]
  -- a contracted curve through a closed point of a negative component, off a closed set
  have hcurve : ∀ (E : MMP.Mori.PrimeDivisor V) (T : TopologicalSpace.Closeds V),
      BV.coeff E < 0 → E.genericPoint ∉ T →
      ∃ (C : ProperCurve sY) (CV : ProperCurve (V.ι ≫ sY)), C.IsContractedBy f ∧
        CV.IsContractedBy f' ∧ V.ι CV.point = C.point ∧ closure ({C.point} : Set Y) ⊆ V ∧
        CV.point ∉ T := by
    intro E T hE hET
    obtain ⟨C, hCf, _, ⟨z', hz'T, rfl⟩, hCz⟩ :=
      exists_properCurve_specializes_of_coeff_neg k sX sY hX hY f hf hfb hpush
        (P := OpenWeilRestriction.primeDivisorMap V.ι E) (by rwa [← hBV])
        (V.ι.isOpenEmbedding.isOpenMap _ T.isClosed.isOpen_compl)
        ⟨E.genericPoint, hET, (OpenWeilRestriction.genericPoint_primeDivisorMap V.ι E).symm⟩
    -- the curve lies in `V`
    have hfz : f C.point = f (V.ι z') := (hCf _ (specializes_iff_mem_closure.mp hCz)).symm
    have hsub : closure ({C.point} : Set Y) ⊆ V := fun w hw => by
      change f w ∈ U
      rw [hCf w hw, hfz, ← hι]
      exact (f' z').2
    obtain ⟨CV, hCV⟩ := MMP.Threefold.Resolution.exists_properCurve_of_closure_subset k V C hsub
    refine ⟨C, CV, hCf, fun y hy => ?_, hCV, hsub, fun hCT => ?_⟩
    · apply U.ι.isOpenEmbedding.injective
      rw [hι, hι, hCV]
      refine hCf _ (map_mem_closure V.ι.continuous hy fun w hw => ?_)
      rw [Set.mem_singleton_iff.1 hw, hCV]
      rfl
    · have hsp : CV.point ⤳ z' := by
        rwa [← V.ι.isOpenEmbedding.isInducing.specializes_iff, hCV]
      exact hz'T (hsp.mem_closed T.isClosed hCT)
  -- every prime divisor with negative coefficient in `B|_V` is a component of `W`
  have hWpos : ∀ E, BV.coeff E < 0 → 0 < W.coeff E := by
    intro E hE
    by_contra! hW
    obtain ⟨C, CV, -, hCVf, -, -, hCVT⟩ := hcurve E _ hE
      (genericPoint_notMem_supp_of_coeff_eq_zero (le_antisymm hW (hW0 E)))
    exact (hWneg CV hCVf).not_ge (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff (V.ι ≫ sY)
      CV.ι CV.dim_le W hWc hW0 ⟨_, by rwa [CV.ι_genericPoint]⟩).1
  -- for the largest `t` with `D = B|_V + t W` effective, `D · C ≥ 0` for a contracted curve `C`
  obtain ⟨E₀, hE₀⟩ := MMP.Threefold.Resolution.exists_primeDivisorMap_eq V P₀ hxU
  obtain ⟨t, ht, hDeff, E₁, hE₁, hD₁⟩ :=
    exists_isEffective_add_smul_coeff_eq_zero BV hW0 hWpos (E₀ := E₀) (by rwa [hBV, hE₀])
  obtain ⟨C, CV, hCf, hCVf, hCV, hsub, hCVT⟩ :=
    hcurve E₁ _ hE₁ (genericPoint_notMem_supp_of_coeff_eq_zero hD₁)
  have h := sum_degreeOn_add_nonneg k (V.ι ≫ sY) hYVn CV (fun j => -r j) L' hL' t W hWc hDeff hCVT
  have hdeg : ∀ j, ((L' j).degreeOn k (V.ι ≫ sY) CV.ι CV.dim_le (hL' j) : ℝ) =
      (L j).degreeOn k sY C.ι C.dim_le (hL j) := fun j => by
    exact_mod_cast degreeOn_pullback_ι V (hL j) (hBj j) C CV hCV hsub
  simp only [hdeg, neg_mul, Finset.sum_neg_distrib] at h
  -- but `D · C = B · C + t (W · C) < 0`
  have hWC : (W.degreeOn k (V.ι ≫ sY) CV.ι CV.dim_le hWc : ℝ) < 0 := by
    exact_mod_cast hWneg CV hCVf
  nlinarith [hN C hCf]

end Negativity

end Proof_lem_fa2_negativity_coefficients_nonneg

namespace MMP.Flips

open Proof_lem_fa2_negativity_coefficients_nonneg

/-- **Exceptional coefficients are nonnegative** (a form of the negativity lemma). Let
`f : Y ⟶ X` be a proper birational morphism of normal varieties over `k`, `L` an `ℝ`-Cartier
divisor on `X` with pull-back `L' = f^*L`, `M` an `f`-nef `ℝ`-Cartier divisor on `Y`, and `B` an
`ℝ`-Cartier divisor on `Y` with nonnegative coefficients along every prime divisor that is not
exceptional over `X`. If `f^*L ≡_f M + B`, then `B` is effective. -/
@[mmp "lem_fa2_negativity_coefficients_nonneg"]
public theorem isEffective_of_isNumericallyEquivalentOver_pullback
    (k : Type u) [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    {L : RDivisor X} (_hL : IsCartierCombination L) {L' : RDivisor Y}
    (hL' : IsRCartierPullback f L L')
    {M : RDivisor Y} (_hM : IsCartierCombination M) (hMnef : IsRelativelyNef k sY f M)
    {B : RDivisor Y} (hB : IsCartierCombination B)
    (hBG : ∀ P : Mori.PrimeDivisor Y, ¬ IsExceptionalPrimeDivisor sX f P → 0 ≤ B.coeff P)
    (hnum : IsNumericallyEquivalentOver k sY f L' (M + B)) :
    B.IsEffective := by
  have := hY.1
  have := hX.1
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsIntegral X := hX.1.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨m, s, N, hN, hBeq⟩ := hB
  have hBeq' : B = ∑ j, s j • Divisor.toRDivisor (N j) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hBeq
  -- the Chow lemma: `h : Y' ⟶ Y` projective birational, `Y'` normal, `h ≫ f` projective
  obtain ⟨Y', h, hY'v, hY'n, hhp, hhb, hfp'⟩ :=
    MMP.Resolution.Bridges.exists_isProjective_isBirational_isNormal_chowModification k hY.1 hX.1
      f hf ‹_› (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
  have : IsProper h := IsProjective.isProper hhp
  have : IsIntegral Y' := hY'v.toIsIntegral
  have : QuasiCompact (h ≫ sY) := hY'v.toQuasiCompact
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sY)
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace (h ≫ sY)
  have hY' : IsNormalVariety k (h ≫ sY) := ⟨hY'v, hY'n⟩
  have hhB : IsBirationalMorphism h := isBirationalMorphism_of_isBirational h hhb
  have hf'b : IsBirationalMorphism (h ≫ f) := isBirationalMorphism_of_isBirational (h ≫ f)
    (hhb.comp (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb))
  have hf' : (h ≫ f) ≫ sX = h ≫ sY := by rw [Category.assoc, hf]
  have : IsDominant h := hhB.isDominant
  -- the pull-back `B' = h^*B = ∑ s_j h^*N_j`, with `-B'` `(h ≫ f)`-nef and `(h ≫ f)_* B' ≥ 0`
  have hNB j : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ (N j).supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant h (N j)
  have hB' : IsRCartierPullback h B _ := ⟨m, s, N, _, hN, hBeq',
    fun j => ⟨hNB j, Divisor.isPullback_pullback (hN j) (hNB j)⟩, rfl⟩
  have : IsProper (h ≫ f) := IsProjective.isProper hfp'
  have hB'eff := isEffective_of_isRelativelyNef_neg_of_forall_isProjectiveMorphism k sX (h ≫ sY)
    hX hY' (h ≫ f) hf' (fun U hU => haveI : IsAffine U := hU
      isProjectiveMorphism_of_isProjective_of_isAffine _
        (IsProjective.of_isPullback (isPullback_morphismRestrict (h ≫ f) U) hfp')) hf'b
    (isRelativelyNef_neg_sum_pullback h f s N hN hNB
      (sum_degreeOn_nonpos_of_isNumericallyEquivalentOver hf hL' hMnef hnum s N hN hBeq'))
    (isEffective_transformDivisor_comp_of_isRCartierPullback hX h f (hf' ▸ hY') hfb hhB hf'b hB'
      hBG)
  intro P
  obtain ⟨E, hE, _, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY hY' hhB P
  rw [← MMP.Fourfold.coeff_eq_of_isRCartierPullback E P hE hB']
  exact hB'eff E

/-- **Negativity lemma.** Let `f : Y ⟶ X` be a projective birational morphism of normal varieties
over a field `k` of characteristic zero and `B` an `ℝ`-Cartier divisor on `Y` such that `-B` is
`f`-nef. If the push-forward `f_*B` is effective, then `B` is effective. -/
@[mmp "thm_fa2_negativity_lemma"]
public theorem isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor
    (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (hfp : IsProjectiveMorphism f)
    (hfb : IsBirationalMorphism f)
    {B : RDivisor Y} (_hB : IsCartierCombination B) (hnef : IsRelativelyNef k sY f (-B))
    (hpush : (Mori.RationalMap.transformDivisor f.toRationalMap B).IsEffective) :
    B.IsEffective := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hfp
  exact isEffective_of_isRelativelyNef_neg_of_forall_isProjectiveMorphism k sX sY hX hY f hf
    (fun U _ => hfp.restrict U) hfb hnef hpush

end MMP.Flips
