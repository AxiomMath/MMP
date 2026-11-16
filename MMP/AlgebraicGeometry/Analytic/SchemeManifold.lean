module

public import MMP.AlgebraicGeometry.Analytic.PluriformDensity
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
import MMP.Analysis.Complex.CauchyOsgoodLaurent
import MMP.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinateCharts
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.StandardSmooth
import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsRank
import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCoverSmooth
import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison

/-!
# The complex manifold `X^an` of a smooth complex scheme

Let `X` be a scheme smooth of relative dimension `n` over `ℂ`, with complex realization
`X^an = MMP.Analytic.ComplexPoints sX`. Étale coordinates `z = (z_1, …, z_n)` on a Zariski open
`U ⊆ X`, restricted to an open `W ⊆ U(ℂ)` of `X^an` on which `y ↦ (z_i(y))_i` is an open
embedding into `ℂⁿ`, are charts of `X^an`; every point lies in one, and since every regular
function is holomorphic in étale coordinates the transition maps are holomorphic. So `X^an` is a
complex (analytic) manifold of dimension `n`. It is Hausdorff when `X` is separated over `ℂ`, and
second countable when `X` is quasi-compact. Integrality is not needed: every point has affine open
neighbourhoods which are smooth complex varieties, and the atlas is local.

## Main definitions

* `MMP.Analytic.ComplexPoints.EtaleCoordinateChart`: étale coordinates `z` on `U` together with
  an open `W ⊆ U(ℂ)` on which `z` is an open embedding.
* `MMP.Analytic.ComplexPoints.EtaleCoordinateChart.toOpenPartialHomeomorph`: the chart
  `W → ℂⁿ` it defines; `MMP.Analytic.ComplexPoints.EtaleCoordinateChart.restrict`, its
  restriction to an open subset.
* `MMP.Analytic.ComplexPoints.etaleChartedSpaceOf`: the étale coordinate charts, read in a model
  space `E` through a linear isomorphism `ℂⁿ ≃ E`, with a prescribed preferred chart at every
  point; `MMP.Analytic.ComplexPoints.etaleChartedSpace` with an arbitrary preferred chart.
* `MMP.Analytic.ComplexPoints.curveChart`: the preferred chart of a smooth complex curve at a
  point, an étale coordinate chart whose coordinate has nonzero differential there.

## Main results

* `MMP.Analytic.ComplexPoints.etaleCoordinate_atlas_of_smooth`: the étale coordinate atlas of a
  scheme smooth of relative dimension `n` over `ℂ`, deduced from the variety case on the affine
  variety neighbourhoods `MMP.Analytic.ComplexPoints.exists_isAffineOpen_isVariety`;
  `MMP.Analytic.ComplexPoints.exists_etale_coordinates_extending_of_mem`: sections with
  independent differentials at a point of an open smooth of relative dimension `n` are among
  étale coordinates there.
* `MMP.Analytic.ComplexPoints.EtaleCoordinateChart.exists_analyticOnNhd`: every regular function
  is an analytic function of étale coordinates.
* `MMP.Analytic.ComplexPoints.isManifold_etaleChartedSpaceOf`: the étale charts form an analytic
  atlas; the instances `instChartedSpaceEuclideanSpace`, `instIsManifoldEuclideanSpace` (model
  `EuclideanSpace ℂ (Fin n)`) and, for curves, `instChartedSpaceComplex`,
  `instIsManifoldComplex` (model `ℂ`).
* `MMP.Analytic.ComplexPoints.t2Space`, `MMP.Analytic.ComplexPoints.secondCountableTopology`:
  `X^an` is Hausdorff for `X` separated, and second countable.
* `MMP.Analytic.ComplexPoints.contMDiff_realize`: realized morphisms of smooth varieties are
  holomorphic.
* `MMP.Analytic.ComplexPoints.exists_mem_maximalAtlas_image_eq_hyperplane`: an étale chart in
  which a family of subsets are the zero loci of coordinates is a simultaneous coordinate chart
  of the maximal atlas.
* `MMP.Analytic.ComplexPoints.hasMFDerivAt_realize_of_adapted`,
  `MMP.Analytic.ComplexPoints.surjective_mfderiv_realize_of_adapted`,
  `MMP.Analytic.ComplexPoints.exists_mem_tangentConeAt_mfderiv_realize_ne_zero`: in a preferred
  chart one of whose coordinates is the pull-back of the coordinate of a curve `B`, the
  differential of `X^an → B^an` is a coordinate projection, so it is surjective, also along
  every stratum whose equations are the other coordinates.
* `MMP.Analytic.ComplexPoints.exists_etale_coordinates_extending`: sections whose differentials
  are independent at a point are among a system of étale coordinates there;
  `MMP.Analytic.ComplexPoints.tmul_D_germ_app_ne_zero`: pull-back along a smooth morphism keeps
  nonzero differentials.
* `MMP.Analytic.ComplexPoints.exists_etale_coordinates_adapted`: for `g : X ⟶ B` smooth at a
  point, étale coordinates one of which is the pull-back of the coordinate of `B`; hence
  `MMP.Analytic.ComplexPoints.exists_pick_surjective_mfderiv_realize`: smooth morphisms to a
  curve are holomorphic submersions.
* `MMP.Analytic.ComplexPoints.exists_pick_relativeSNC`: étale coordinates adapted at every point
  to a morphism to a curve and to a family of subsets give holomorphy, simultaneous coordinate
  charts and submersivity along all strata, the hypotheses of the product germ theorem
  `MMP.Analytic.exists_homeomorph_prod_of_relativeSNC`.
* `MMP.Analytic.ComplexPoints.exists_mem_support_iff_notMem_basicOpen`: near a point where the
  stalk of an ideal sheaf is principal, its support is the zero locus of a generator;
  `MMP.Analytic.ComplexPoints.tmul_D_germ_app_notMem_span`: along a closed subscheme smooth over
  a curve, the pull-back of a coordinate of the curve has differential independent of those of
  the equations of the subscheme.
* `MMP.Analytic.ComplexPoints.exists_etale_coordinates_adapted_of_isSNC`: for a simple normal
  crossing divisor all of whose strata are smooth over `B`, étale coordinates adapted at every
  point to the morphism and to the components; hence
  `MMP.Analytic.ComplexPoints.exists_pick_relativeSNC_of_isSNC`, the manifold hypotheses of the
  product germ theorem for such a divisor;
  `MMP.Analytic.ComplexPoints.exists_pick_relativeSNC_relativeDimensionLocus`, the same on each
  relative dimension locus `MMP.Analytic.ComplexPoints.relativeDimensionLocus` of a scheme smooth
  over `ℂ`, which is open and closed (`MMP.Analytic.ComplexPoints.isClosed_relativeDimensionLocus`).
* `MMP.Analytic.ComplexPoints.isProperMap_restrict_realize_preimage_range`: the preimage of a
  centre proper over `B` is proper over `B^an`.

## Implementation notes

* The atlas of `MMP.Analytic.ComplexPoints.etaleChartedSpaceOf` is the set of all étale
  coordinate charts, whatever the preferred charts; so all these structures have the same
  maximal atlas, and the manifold is the same. The preferred chart matters only where a
  statement is read in it (`mfderiv`, `extChartAt`), and choosing it adapted to a morphism to
  a curve and to a divisor computes the differential there.
* The atlas is compatible for every smoothness order, in particular `ω` and `∞`: regular
  functions are holomorphic in étale coordinates, hence analytic by Osgood's lemma.
* For a relative snc divisor `∑_{E ∈ s} E`, the coordinates at `x` are the pull-back `g^* w` of
  the coordinate of `B` together with the members `t_E` of the regular system of parameters
  generating the components through `x`. Their differentials are independent: the `dt_E` are
  part of a basis, and `d(g^* w)` survives on the stratum `⋂_{x ∈ E} E`, which is smooth over
  `B` and on which every `t_E` vanishes. Points off the divisor are the case of no component
  through `x`: the chart is taken inside the complement of the components.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*]
* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

open CategoryTheory AlgebraicGeometry Topology Manifold
open scoped ContDiff

namespace MMP.Analytic.ComplexPoints

section VarietyNeighbourhoods

/-- In a reduced Noetherian ring, for a prime `p` there is `f ∉ p` killing every element that is
killed by some element outside `p`. -/
public theorem exists_notMem_forall_mul_eq_zero {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsReduced A] (p : Ideal A) [hp : p.IsPrime] :
    ∃ f ∉ p, ∀ x : A, (∃ s ∉ p, s * x = 0) → f * x = 0 := by
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hc : ∀ q ∈ minimalPrimes A, ¬ q ≤ p → ∃ a ∈ q, a ∉ p := fun _ _ h ↦
    SetLike.not_le_iff_exists.1 h
  choose! a ha hap using hc
  let S := hfin.toFinset.filter (fun q ↦ ¬ q ≤ p)
  have hS : ∀ q ∈ S, q ∈ minimalPrimes A ∧ ¬ q ≤ p := fun q hq ↦ by
    simpa only [S, Finset.mem_filter, Set.Finite.mem_toFinset] using hq
  refine ⟨∏ q ∈ S, a q, ?_, ?_⟩
  · intro h
    obtain ⟨q, hq, hqp⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hap q (hS q hq).1 (hS q hq).2 hqp
  · rintro x ⟨s, hs, hsx⟩
    have hmem : (∏ q ∈ S, a q) * x ∈ (⊥ : Ideal A).radical := by
      rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro q hq
      have hqprime : q.IsPrime := hq.1.1
      by_cases hqp : q ≤ p
      · refine q.mul_mem_left _ ?_
        have : s * x ∈ q := by simp [hsx]
        exact (hqprime.mem_or_mem this).resolve_left fun h ↦ hs (hqp h)
      · have hqS : q ∈ S := Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hq, hqp⟩
        refine q.mul_mem_right _ ?_
        obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem a hqS
        rw [hu]
        exact q.mul_mem_right _ (ha q hq hqp)
    obtain ⟨k, hk⟩ := hmem
    exact IsReduced.eq_zero _ ⟨k, Ideal.mem_bot.1 hk⟩

/-- **Integral affine neighbourhoods.** On a reduced locally Noetherian scheme, a point whose local
ring is a domain has arbitrarily small affine open neighbourhoods that are integral. -/
public theorem exists_isAffineOpen_isIntegral {X : Scheme.{0}} [IsLocallyNoetherian X] [IsReduced X]
    (p : X) [IsDomain (X.presheaf.stalk p)] (V : X.Opens) (hpV : p ∈ V) :
    ∃ W : X.Opens, p ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧ IsIntegral W := by
  obtain ⟨V', hV', hpV', hV'V⟩ := exists_isAffineOpen_mem_and_subset hpV
  have : IsNoetherianRing Γ(X, V') := IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  let _ : Algebra Γ(X, V') (X.presheaf.stalk p) := X.presheaf.algebra_section_stalk ⟨p, hpV'⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk p) (hV'.primeIdealOf ⟨p, hpV'⟩).asIdeal :=
    hV'.isLocalization_stalk ⟨p, hpV'⟩
  obtain ⟨f, hf, hfx⟩ := exists_notMem_forall_mul_eq_zero (hV'.primeIdealOf ⟨p, hpV'⟩).asIdeal
  have hpW : p ∈ X.basicOpen f := by
    rw [X.mem_basicOpen f p hpV']
    exact IsLocalization.map_units (X.presheaf.stalk p)
      (⟨f, hf⟩ : (hV'.primeIdealOf ⟨p, hpV'⟩).asIdeal.primeCompl)
  have hW : IsAffineOpen (X.basicOpen f) := hV'.basicOpen f
  have hWV : X.basicOpen f ≤ V' := X.basicOpen_le f
  let _ : Algebra Γ(X, V') Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE hWV).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hV'.isLocalization_basicOpen f
  have hinj : Function.Injective (X.presheaf.germ (X.basicOpen f) p hpW).hom := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨⟨c, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) u
    have hgc : (X.presheaf.germ V' p hpV').hom c = 0 := by
      have h2 := congrArg (X.presheaf.germ (X.basicOpen f) p hpW).hom
        (IsLocalization.mk'_spec (Γ(X, X.basicOpen f)) c (⟨f ^ k, k, rfl⟩ : Submonoid.powers f))
      rw [map_mul, hu, zero_mul] at h2
      rw [← X.presheaf.germ_res_apply (homOfLE hWV) p hpW c]
      exact h2.symm
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
      (hV'.primeIdealOf ⟨p, hpV'⟩).asIdeal.primeCompl _ c).1 hgc
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨f, 1, pow_one f⟩, hfx c ⟨s, s.2, hs⟩⟩
  have : Nontrivial Γ(X, X.basicOpen f) := (X.presheaf.germ _ p hpW).hom.domain_nontrivial
  have : IsDomain Γ(X, X.basicOpen f) := hinj.isDomain _
  refine ⟨X.basicOpen f, hpW, hWV.trans hV'V, hW, ?_⟩
  have : IsAffine (X.basicOpen f) := hW
  have : Nonempty (X.basicOpen f) := ⟨⟨p, hpW⟩⟩
  have : IsDomain Γ((X.basicOpen f : Scheme), ⊤) :=
    ((X.basicOpen f).topIso.commRingCatIsoToRingEquiv.injective).isDomain
      (X.basicOpen f).topIso.commRingCatIsoToRingEquiv.toRingHom
  exact isIntegral_of_isAffine_of_isDomain _

/-- **Variety neighbourhoods.** On a scheme smooth of relative dimension `n` over `ℂ`, every
point has arbitrarily small affine open neighbourhoods `W` which are smooth complex varieties of
dimension `n`. -/
public theorem exists_isAffineOpen_isVariety {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [SmoothOfRelativeDimension n sX] (p : X) (V : X.Opens) (hpV : p ∈ V) :
    ∃ W : X.Opens, p ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧ AlgebraicGeometry.IsVariety ℂ (W.ι ≫ sX) ∧
      SmoothOfRelativeDimension n (W.ι ≫ sX) := by
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hdom : ∀ q : X, IsDomain (X.presheaf.stalk q) := fun q ↦
    have := isRegularLocalRing_stalk_of_smooth_over_field sX q
    IsRegularLocalRing.isDomain _
  have hred : ∀ q : X, _root_.IsReduced (X.presheaf.stalk q) := fun q ↦ by
    have := hdom q
    exact isReduced_of_noZeroDivisors
  have : AlgebraicGeometry.IsReduced X := @isReduced_of_isReduced_stalk X hred
  have := hdom p
  obtain ⟨W, hpW, hWV, hW, hWi⟩ := exists_isAffineOpen_isIntegral p V hpV
  have : IsAffine W := hW
  let : ∀ m, IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} m) := fun m ↦
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} m)
  refine ⟨W, hpW, hWV, hW, ⟨⟩, IsZariskiLocalAtSource.comp ‹_› _⟩

end VarietyNeighbourhoods

section LocalRank

open IsLocalRing TensorProduct KaehlerDifferential

/-- The differentials `dr ⊗ 1` span `κ(T) ⊗ Ω[T⁄R]`. -/
private theorem span_tmul_D {R T : Type*} [CommRing R] [CommRing T] [IsLocalRing T]
    [Algebra R T] :
    ⊤ ≤ Submodule.span (ResidueField T)
      (Set.range fun r : T ↦ (1 : ResidueField T) ⊗ₜ[T] D R T r) := by
  have key : ∀ v : ResidueField T ⊗[T] Ω[T⁄R], v ∈ Submodule.span (ResidueField T)
      (Set.range fun r : T ↦ (1 : ResidueField T) ⊗ₜ[T] D R T r) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul c x =>
      have hx : x ∈ Submodule.span T (Set.range (D R T)) := by
        rw [span_range_derivation]; trivial
      have h1 : (1 : ResidueField T) ⊗ₜ[T] x ∈ Submodule.span (ResidueField T)
          (Set.range fun r : T ↦ (1 : ResidueField T) ⊗ₜ[T] D R T r) := by
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨r, rfl⟩ := hy
          exact Submodule.subset_span ⟨r, rfl⟩
        | zero => simp
        | add y y' _ _ hy hy' => rw [tmul_add]; exact add_mem hy hy'
        | smul a y _ hy =>
          rw [tmul_smul, ← algebraMap_smul (ResidueField T) a]
          exact Submodule.smul_mem _ _ hy
      rw [show c ⊗ₜ[T] x = c • ((1 : ResidueField T) ⊗ₜ[T] x) by
        rw [smul_tmul', smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ h1
    | add x y hx hy => exact add_mem hx hy
  exact fun v _ ↦ key v

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}

open Stacks.RelativeDifferentialStalkMap in
/-- At a point `p` of an open `V` of a smooth complex scheme on which `V ⟶ Spec ℂ` is smooth of
relative dimension `n`, the stalk of `Ω_{X/ℂ}` has rank `n`. -/
public theorem finrank_kaehlerDifferential_stalk_of_mem [Smooth sX] (V : X.Opens)
    [SmoothOfRelativeDimension n (V.ι ≫ sX)] (p : X) (hp : p ∈ V) :
    letI := (sX.stalkMap p).hom.toAlgebra
    Module.finrank (X.presheaf.stalk p)
      Ω[X.presheaf.stalk p ⁄ (Spec (.of ℂ)).presheaf.stalk (sX p)] = n := by
  classical
  letI := algebraStalkMap sX p
  have hrank := AlgebraicGeometry.finrank_stalk_relativeDifferentials_eq_fiberDimensionAt sX p
  have h2 := AlgebraicGeometry.fiberDimensionAt_eq_of_smoothOfRelativeDimension (V.ι ≫ sX) n
    ⟨p, hp⟩
  rw [AlgebraicGeometry.fiberDimensionAt_comp_openImmersion V.ι sX ⟨p, hp⟩] at h2
  rw [(relativeDifferentialsStalkKaehlerEquiv sX p).finrank_eq] at hrank
  exact_mod_cast hrank.trans h2

/-- **Completing differentials to étale coordinates.** Let `X` be smooth over `ℂ`, `V₀ ⊆ X` an
open smooth of relative dimension `n` over `ℂ`, `p ∈ V₀` and `a_1, …, a_k` sections over an open
`V ∋ p` whose differentials are linearly independent in the fibre `κ(p) ⊗ Ω_{X/ℂ,p}`. Then the
`a_i` are among a system of
étale coordinates `z_1, …, z_n` on an open `U ∋ p` inside `V`: `a_i = z_{c i}` for an injection
`c : Fin k ↪ Fin n`. -/
public theorem exists_etale_coordinates_extending_of_mem [Smooth sX] (V₀ : X.Opens)
    [SmoothOfRelativeDimension n (V₀.ι ≫ sX)] (p : X) (hp₀ : p ∈ V₀) (V : X.Opens) (hpV : p ∈ V)
    {k : ℕ} (a : Fin k → Γ(X, V))
    (ha : letI := (sX.stalkMap p).hom.toAlgebra
      LinearIndependent (ResidueField (X.presheaf.stalk p)) fun i ↦
        (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
          D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
            (X.presheaf.germ V p hpV (a i))) :
    ∃ (U : X.Opens) (_ : p ∈ U) (hUV : U ≤ V) (z : Fin n → Γ(X, U)) (c : Fin k ↪ Fin n),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) ∧
      ∀ i, z (c i) = X.presheaf.map (homOfLE hUV).op (a i) := by
  classical
  letI := (sX.stalkMap p).hom.toAlgebra
  obtain ⟨hfree, hfin⟩ := MMP.Flips.ResolutionInputs.free_finite_kaehlerDifferential_stalk sX p
  have hdim : Module.finrank (ResidueField (X.presheaf.stalk p))
      (ResidueField (X.presheaf.stalk p) ⊗[X.presheaf.stalk p]
        Ω[X.presheaf.stalk p ⁄ (Spec (.of ℂ)).presheaf.stalk (sX p)]) = n := by
    rw [Module.finrank_baseChange]
    exact finrank_kaehlerDifferential_stalk_of_mem V₀ p hp₀
  let w : Fin k →
      ResidueField (X.presheaf.stalk p) ⊗[X.presheaf.stalk p]
        Ω[X.presheaf.stalk p ⁄ (Spec (.of ℂ)).presheaf.stalk (sX p)] :=
    fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
      D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p) (X.presheaf.germ V p hpV (a i))
  obtain ⟨e, v, hvS, hli, hsp⟩ := MMP.Flips.ResolutionInputs.exists_sumElim_basis w ha _
    (span_tmul_D (R := (Spec (.of ℂ)).presheaf.stalk (sX p)) (T := X.presheaf.stalk p))
  choose r hr using hvS
  have hcard : k + e = n := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [hdim, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at this
    exact this.symm
  obtain ⟨V₁, -, hpV₁, b, hb⟩ := MMP.Flips.ResolutionInputs.exists_affineOpen_germ_eq p r
  have hpV' : p ∈ V ⊓ V₁ := ⟨hpV, hpV₁⟩
  let g' : Fin k ⊕ Fin e → Γ(X, V ⊓ V₁) := Sum.elim
    (fun i ↦ X.presheaf.map (homOfLE inf_le_left).op (a i))
    (fun j ↦ X.presheaf.map (homOfLE inf_le_right).op (b j))
  let σ : Fin n ≃ Fin k ⊕ Fin e := (finSumFinEquiv.trans (finCongr hcard)).symm
  have hv : ∀ l : Fin k ⊕ Fin e, (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
      D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
        (X.presheaf.germ (V ⊓ V₁) p hpV' (g' l)) = Sum.elim w v l := by
    rintro (j | j)
    · simp only [g', Sum.elim_inl, w]
      rw [X.presheaf.germ_res_apply]
    · simp only [g', Sum.elim_inr]
      rw [X.presheaf.germ_res_apply, hb j]
      exact hr j
  obtain ⟨U, -, hpU, hUV', het⟩ :=
    MMP.Flips.ResolutionInputs.exists_isAffineOpen_etale_homOfVector sX p (V ⊓ V₁) hpV'
      (g' ∘ σ) (by
        simp only [Function.comp_apply, hv]
        refine ⟨hli.comp σ σ.injective, ?_⟩
        rw [show (fun i ↦ Sum.elim w v (σ i)) = Sum.elim w v ∘ σ from rfl, Set.range_comp,
          σ.range_eq_univ, Set.image_univ]
        exact top_le_iff.1 hsp)
  refine ⟨U, hpU, hUV'.trans inf_le_left, fun i ↦ X.presheaf.map (homOfLE hUV').op (g' (σ i)),
    Function.Embedding.inl.trans σ.symm.toEmbedding, het, fun i ↦ ?_⟩
  change X.presheaf.map (homOfLE hUV').op (g' (σ (σ.symm (Sum.inl i)))) = _
  simp only [Equiv.apply_symm_apply, g', Sum.elim_inl]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end LocalRank

section Atlas

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ}

/-- A point lies in the chart of a preimage open iff its realization lies in the chart. -/
public lemma mem_chart_preimage_iff (g : X ⟶ Y) (hg : g ≫ sY = sX) (U : Y.Opens)
    (y : ComplexPoints sX) : y ∈ chart (g ⁻¹ᵁ U) ↔ realize g hg y ∈ chart U := by
  rw [mem_chart_iff, mem_chart_iff]
  rfl

private lemma eval_app_realize (g : X ⟶ Y) (hg : g ≫ sY = sX) (U : Y.Opens) (a : Γ(Y, U))
    (y : ComplexPoints sX) (hy : y ∈ chart (g ⁻¹ᵁ U)) :
    eval (g ⁻¹ᵁ U) (g.app U a) ⟨y, hy⟩ =
      eval U a ⟨realize g hg y, (mem_chart_preimage_iff g hg U y).1 hy⟩ := by
  simp only [ComplexPoints.eval]
  congr 1

/-- The realization of the inclusion of an open subscheme is an open embedding. -/
private theorem isOpenEmbedding_realize_ι' (W : X.Opens) :
    IsOpenEmbedding (realize (sX := W.ι ≫ sX) W.ι rfl) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : (W : Scheme).Over (Spec (.of ℂ)) := ⟨W.ι ≫ sX⟩
  haveI : W.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have h : realize (sX := W.ι ≫ sX) W.ι rfl = (homeomorphUnderlyingSpace (X := X)).symm ∘
      MMP.UnderlyingSpace.map (K := ℂ) W.ι ∘
        homeomorphUnderlyingSpace (X := (W : Scheme)) :=
    rfl
  rw [h]
  exact (homeomorphUnderlyingSpace (X := X)).symm.isOpenEmbedding.comp
    ((MMP.UnderlyingSpace.isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) W.ι).comp
      (homeomorphUnderlyingSpace (X := (W : Scheme))).isOpenEmbedding)

/-- A `ℂ`-point of `X` lying in an open `W` comes from a `ℂ`-point of `W`. -/
private theorem exists_realize_ι_eq (W : X.Opens) (x : ComplexPoints sX)
    (hx : toScheme x ∈ W) : ∃ x' : ComplexPoints (W.ι ≫ sX), realize W.ι rfl x' = x := by
  have H : Set.range x.hom ⊆ Set.range W.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p default, Scheme.Opens.range_ι]
    exact hx
  refine ⟨⟨IsOpenImmersion.lift W.ι x.hom H, ?_⟩, ?_⟩
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, x.hom_comp_structure]
  · ext1
    exact IsOpenImmersion.lift_fac W.ι x.hom H

/-- Étale coordinates restrict to étale coordinates on an open subscheme. -/
private lemma etale_homOfVector_ι (W U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)))) :
    Etale (AffineSpace.homOfVector ((W.ι ⁻¹ᵁ U).ι ≫ W.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ (W.ι ⁻¹ᵁ U).topIso.inv (W.ι.app U (z i.down)))) := by
  have e : AffineSpace.homOfVector ((W.ι ⁻¹ᵁ U).ι ≫ W.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ (W.ι ⁻¹ᵁ U).topIso.inv (W.ι.app U (z i.down))) =
      W.ι.resLE U (W.ι ⁻¹ᵁ U) le_rfl ≫ AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)) := by
    rw [AffineSpace.comp_homOfVector, Scheme.Hom.resLE_comp_ι_assoc]
    congr 1
    funext i
    change _ = (W.ι.resLE U (W.ι ⁻¹ᵁ U) le_rfl).app ⊤ (U.topIso.inv (z i.down))
    rw [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
    exact (congrArg (fun φ : Γ(X, U) ⟶ Γ(W.ι ⁻¹ᵁ U, ⊤) ↦ φ (z i.down))
      (Iso.inv_hom_id_assoc U.topIso (W.ι.app U ≫ (W.ι ⁻¹ᵁ U).topIso.inv))).symm
  have : IsOpenImmersion (W.ι.resLE U (W.ι ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  rw [e]
  infer_instance

variable (sX) in
/-- The `ℂ`-points lying over an open subscheme form an open set. -/
public lemma isOpen_chart (U : X.Opens) : IsOpen (chart (sX := sX) U) := by
  have : chart (sX := sX) U = toScheme ⁻¹' (U : Set X) := by
    ext x
    exact mem_chart_iff
  rw [this]
  exact U.isOpen.preimage continuous_toScheme

/-- **Étale coordinates form a holomorphic atlas on a smooth complex scheme.** The conclusions of
`MMP.Analytic.ComplexPoints.etaleCoordinate_atlas` hold for every scheme `X` smooth of relative
dimension `n` over `ℂ`, integral or not:

1. every point of `X^an` lies in `U(ℂ)` for some Zariski open `U` carrying étale coordinates
   `z : Fin n → Γ(X, U)`;
2. for étale coordinates `z` on `U` and `x ∈ U(ℂ)`, there is an open neighbourhood `W ⊆ U(ℂ)`
   of `x` in `X^an` on which `y ↦ (z_i(y))_i` is an open embedding into `ℂⁿ`;
3. on such a chart `W`, every regular function `f` on an open `U'` is, on `W ∩ U'(ℂ)`, a
   holomorphic function of the coordinates `z`. -/
public theorem etaleCoordinate_atlas_of_smooth (sX : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension n sX] :
    (∀ x : ComplexPoints sX, ∃ (U : X.Opens) (z : Fin n → Γ(X, U)),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) ∧ x ∈ chart U) ∧
    (∀ (U : X.Opens) (z : Fin n → Γ(X, U)),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) →
      ∀ x ∈ chart (sX := sX) U, ∃ (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U),
        IsOpen W ∧ x ∈ W ∧
          IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)) ∧
    (∀ (U : X.Opens) (z : Fin n → Γ(X, U)),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) →
      ∀ (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U), IsOpen W →
        IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩) →
        ∀ (U' : X.Opens) (f : Γ(X, U')), ∃ G : (Fin n → ℂ) → ℂ,
          DifferentiableOn ℂ G
            ((fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩) '' {y | y.1 ∈ chart U'}) ∧
          ∀ (y : W) (hy : y.1 ∈ chart U'),
            eval U' f ⟨y.1, hy⟩ = G (fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)) := by
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  refine ⟨fun x ↦ ?_, fun U z hz x hx ↦ ?_, fun U z hz W hW hWo hemb U' f ↦ ?_⟩
  · obtain ⟨V₀, hxV₀, -, -, -, hV₀s⟩ :=
      exists_isAffineOpen_isVariety sX (n := n) (toScheme x) ⊤ trivial
    haveI := hV₀s
    obtain ⟨U, hpU, -, z, -, hz, -⟩ :=
      exists_etale_coordinates_extending_of_mem (sX := sX) (n := n) V₀
      (toScheme x) hxV₀ ⊤ trivial (fun i : Fin 0 ↦ i.elim0) linearIndependent_empty_type
    exact ⟨U, z, hz, mem_chart_iff.2 hpU⟩
  · obtain ⟨V, hxV, -, -, hVv, hVs⟩ :=
      exists_isAffineOpen_isVariety sX (n := n) (toScheme x) U (mem_chart_iff.1 hx)
    haveI := hVv
    haveI := hVs
    obtain ⟨x', rfl⟩ := exists_realize_ι_eq V x hxV
    have hz' := etale_homOfVector_ι V U z hz
    have hx'U : x' ∈ chart (V.ι ⁻¹ᵁ U) := (mem_chart_preimage_iff V.ι rfl U x').2 hx
    obtain ⟨WY, hWY, hWYo, hx'W, hembY⟩ := (etaleCoordinate_atlas (V.ι ≫ sX) (n := n)).2.1 _
      (fun i ↦ V.ι.app U (z i)) hz' x' hx'U
    have hρ := isOpenEmbedding_realize_ι' (sX := sX) V
    have hσ : IsOpenEmbedding (fun y : WY ↦ realize (sX := V.ι ≫ sX) V.ι rfl y) :=
      hρ.comp hWYo.isOpenEmbedding_subtypeVal
    have hsub : Set.range (fun y : WY ↦ realize (sX := V.ι ≫ sX) V.ι rfl y) ⊆ chart U := by
      rintro _ ⟨y, rfl⟩
      exact (mem_chart_preimage_iff V.ι rfl U y.1).1 (hWY y.2)
    refine ⟨Set.range (fun y : WY ↦ realize (sX := V.ι ≫ sX) V.ι rfl y), hsub, hσ.isOpen_range,
      Set.mem_range.2 ⟨⟨x', hx'W⟩, rfl⟩, ?_⟩
    let e : WY ≃ₜ Set.range (fun y : WY ↦ realize (sX := V.ι ≫ sX) V.ι rfl y) :=
      hσ.isEmbedding.toHomeomorph
    have hfe : (fun y : Set.range (fun y : WY ↦ realize (sX := V.ι ≫ sX) V.ι rfl y) ↦
        fun i ↦ eval U (z i) ⟨y.1, hsub y.2⟩) =
        (fun y : WY ↦ fun i ↦ eval (V.ι ⁻¹ᵁ U) (V.ι.app U (z i)) ⟨y.1, hWY y.2⟩) ∘ e.symm := by
      funext y i
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [Function.comp_apply, e.symm_apply_apply, eval_app_realize V.ι rfl U]
      rfl
    rw [hfe]
    exact hembY.comp e.symm.isOpenEmbedding
  · classical
    set c : W → (Fin n → ℂ) := fun y i ↦ eval U (z i) ⟨y.1, hW y.2⟩ with hc
    let G : (Fin n → ℂ) → ℂ := fun v ↦
      if h : ∃ y : W, y.1 ∈ chart U' ∧ c y = v then eval U' f ⟨h.choose.1, h.choose_spec.1⟩
      else 0
    have hG : ∀ (y : W) (hy : y.1 ∈ chart U'), G (c y) = eval U' f ⟨y.1, hy⟩ := by
      intro y hy
      have h : ∃ y' : W, y'.1 ∈ chart U' ∧ c y' = c y := ⟨y, hy, rfl⟩
      have hy' : h.choose = y := hemb.injective h.choose_spec.2
      simp only [G, dif_pos h]
      have hv : (⟨h.choose.1, h.choose_spec.1⟩ : chart (sX := sX) U') = ⟨y.1, hy⟩ :=
        Subtype.ext (congrArg (fun w : W ↦ (w : ComplexPoints sX)) hy')
      exact congrArg (eval U' f) hv
    refine ⟨G, ?_, fun y hy ↦ (hG y hy).symm⟩
    rintro _ ⟨y₀, hy₀, rfl⟩
    refine DifferentiableAt.differentiableWithinAt ?_
    obtain ⟨V, hxV, hVUU', -, hVv, hVs⟩ := exists_isAffineOpen_isVariety sX (n := n)
      (toScheme y₀.1) (U ⊓ U') ⟨mem_chart_iff.1 (hW y₀.2), mem_chart_iff.1 hy₀⟩
    haveI := hVv
    haveI := hVs
    have hρ := isOpenEmbedding_realize_ι' (sX := sX) V
    obtain ⟨y₀', hy₀'⟩ := exists_realize_ι_eq V y₀.1 hxV
    have hz' := etale_homOfVector_ι V U z hz
    set ρ := realize (sX := V.ι ≫ sX) V.ι rfl with hρdef
    set WY : Set (ComplexPoints (V.ι ≫ sX)) := ρ ⁻¹' W with hWYdef
    have hWY : WY ⊆ chart (V.ι ⁻¹ᵁ U) := fun y hy ↦
      (mem_chart_preimage_iff V.ι rfl U y).2 (hW hy)
    have hWYo : IsOpen WY := hWo.preimage hρ.continuous
    set cY : WY → (Fin n → ℂ) := fun y i ↦ eval (V.ι ⁻¹ᵁ U) (V.ι.app U (z i)) ⟨y.1, hWY y.2⟩
      with hcYdef
    have hcY : cY = c ∘ W.restrictPreimage ρ := by
      funext y i
      simp only [cY, c, Function.comp_apply]
      rw [eval_app_realize V.ι rfl U]
      rfl
    have hembY : IsOpenEmbedding cY := by
      rw [hcY]
      exact hemb.comp (hρ.restrictPreimage W)
    obtain ⟨GY, hGYd, hGYe⟩ := (etaleCoordinate_atlas (V.ι ≫ sX) (n := n)).2.2 _
      (fun i ↦ V.ι.app U (z i)) hz' WY hWY hWYo hembY (V.ι ⁻¹ᵁ U') (V.ι.app U' f)
    have hSo : IsOpen (cY '' {y | y.1 ∈ chart (V.ι ⁻¹ᵁ U')}) :=
      hembY.isOpenMap _ ((isOpen_chart _ _).preimage continuous_subtype_val)
    have hy₀W : y₀' ∈ WY := by
      change ρ y₀' ∈ W
      rw [hy₀']
      exact y₀.2
    have hmemS : cY ⟨y₀', hy₀W⟩ = c y₀ := by
      rw [hcY]
      exact congrArg c (Subtype.ext hy₀')
    have hy₀U' : y₀' ∈ chart (V.ι ⁻¹ᵁ U') :=
      (mem_chart_preimage_iff V.ι rfl U' y₀').2 (by rw [← hρdef, hy₀']; exact hy₀)
    have hvS : c y₀ ∈ cY '' {y | y.1 ∈ chart (V.ι ⁻¹ᵁ U')} := ⟨⟨y₀', hy₀W⟩, hy₀U', hmemS⟩
    have heq : G =ᶠ[𝓝 (c y₀)] GY := by
      filter_upwards [hSo.mem_nhds hvS] with v hv
      obtain ⟨y, hy, rfl⟩ := hv
      have hyU' : (W.restrictPreimage ρ y).1 ∈ chart U' :=
        (mem_chart_preimage_iff V.ι rfl U' y.1).1 hy
      calc G (cY y) = G (c (W.restrictPreimage ρ y)) := by rw [hcY]; rfl
        _ = eval U' f ⟨_, hyU'⟩ := hG _ hyU'
        _ = eval (V.ι ⁻¹ᵁ U') (V.ι.app U' f) ⟨y.1, hy⟩ :=
          (eval_app_realize V.ι rfl U' f y.1 hy).symm
        _ = GY (cY y) := hGYe y hy
    exact (hGYd.differentiableAt (hSo.mem_nhds hvS)).congr_of_eventuallyEq heq

end Atlas

section Charts

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (n : ℕ)

/-- An *étale coordinate chart* of `X^an`: étale coordinates `z_1, …, z_n` on a Zariski open
`U ⊆ X`, together with a nonempty open subset `W ⊆ U(ℂ)` of `X^an` on which the coordinate map
`y ↦ (z_i(y))_i` is an open embedding into `ℂⁿ`. -/
public structure EtaleCoordinateChart where
  /-- The Zariski open carrying the coordinates. -/
  U : X.Opens
  /-- The coordinates. -/
  z : Fin n → Γ(X, U)
  /-- The coordinates are étale. -/
  etale : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
    (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)))
  /-- The domain of the chart, an open subset of `U(ℂ)`. -/
  W : Set (ComplexPoints sX)
  /-- `W` lies in `U(ℂ)`. -/
  subset : W ⊆ chart U
  /-- `W` is open. -/
  isOpen : IsOpen W
  /-- `W` is nonempty. -/
  nonempty : W.Nonempty
  /-- The coordinate map is an open embedding on `W`. -/
  isOpenEmbedding : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, subset y.2⟩)

namespace EtaleCoordinateChart

variable {sX n}

/-- The coordinate map `W → ℂⁿ` of an étale coordinate chart. -/
@[expose] public noncomputable def coord (c : EtaleCoordinateChart sX n) : c.W → (Fin n → ℂ) :=
  fun y i ↦ eval c.U (c.z i) ⟨y.1, c.subset y.2⟩

/-- The chart `W → ℂⁿ` of an étale coordinate chart, as an open partial homeomorphism of
`X^an` into `ℂⁿ` with source `W`. -/
@[expose] public noncomputable def toOpenPartialHomeomorph (c : EtaleCoordinateChart sX n) :
    OpenPartialHomeomorph (ComplexPoints sX) (Fin n → ℂ) :=
  haveI : Nonempty c.W := c.nonempty.to_subtype
  (c.isOpenEmbedding.toOpenPartialHomeomorph _).lift_openEmbedding
    c.isOpen.isOpenEmbedding_subtypeVal

@[simp]
public lemma source_toOpenPartialHomeomorph (c : EtaleCoordinateChart sX n) :
    c.toOpenPartialHomeomorph.source = c.W := by
  simp [toOpenPartialHomeomorph, OpenPartialHomeomorph.lift_openEmbedding_source]

/-- On `W`, the chart is given by the values of the coordinates `z_i`. -/
public lemma toOpenPartialHomeomorph_apply (c : EtaleCoordinateChart sX n) {y : ComplexPoints sX}
    (hy : y ∈ c.W) (i : Fin n) :
    c.toOpenPartialHomeomorph y i = eval c.U (c.z i) ⟨y, c.subset hy⟩ := by
  have : Nonempty c.W := c.nonempty.to_subtype
  exact congrFun (OpenPartialHomeomorph.lift_openEmbedding_apply
    (c.isOpenEmbedding.toOpenPartialHomeomorph _) c.isOpen.isOpenEmbedding_subtypeVal
    (x := ⟨y, hy⟩)) i

/-- The inverse of the chart maps its target into the domain `W`. -/
public lemma toOpenPartialHomeomorph_symm_mem (c : EtaleCoordinateChart sX n) {v : Fin n → ℂ}
    (hv : v ∈ c.toOpenPartialHomeomorph.target) :
    c.toOpenPartialHomeomorph.symm v ∈ c.W := by
  have := c.toOpenPartialHomeomorph.map_target hv
  rwa [source_toOpenPartialHomeomorph] at this

/-- The chart inverts its inverse on its target. -/
public lemma toOpenPartialHomeomorph_apply_symm (c : EtaleCoordinateChart sX n)
    {v : Fin n → ℂ} (hv : v ∈ c.toOpenPartialHomeomorph.target) :
    c.toOpenPartialHomeomorph (c.toOpenPartialHomeomorph.symm v) = v :=
  c.toOpenPartialHomeomorph.right_inv hv

/-- **Regular functions are analytic in étale coordinates.** On an étale coordinate chart `W`,
every regular function `f` on a Zariski open `U'` is, on `W ∩ U'(ℂ)`, an analytic function of
the coordinates. -/
public theorem exists_analyticOnNhd
    [SmoothOfRelativeDimension n sX] (c : EtaleCoordinateChart sX n) (U' : X.Opens)
    (f : Γ(X, U')) :
    ∃ G : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ G (c.toOpenPartialHomeomorph.target ∩
        c.toOpenPartialHomeomorph.symm ⁻¹' chart U') ∧
      ∀ (y : ComplexPoints sX) (_hy : y ∈ c.W) (hy' : y ∈ chart U'),
        eval U' f ⟨y, hy'⟩ = G (c.toOpenPartialHomeomorph y) := by
  obtain ⟨G, hGd, hG⟩ := (etaleCoordinate_atlas_of_smooth sX).2.2 c.U c.z c.etale c.W c.subset
    c.isOpen c.isOpenEmbedding U' f
  set S := c.toOpenPartialHomeomorph.target ∩ c.toOpenPartialHomeomorph.symm ⁻¹' chart U'
  have hSo : IsOpen S := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm (isOpen_chart sX U')
  have hSsub : S ⊆ (fun y : c.W ↦ fun i ↦ eval c.U (c.z i) ⟨y.1, c.subset y.2⟩) ''
      {y | y.1 ∈ chart U'} := by
    intro v hv
    refine ⟨⟨_, c.toOpenPartialHomeomorph_symm_mem hv.1⟩, hv.2, ?_⟩
    funext i
    have := c.toOpenPartialHomeomorph_apply (c.toOpenPartialHomeomorph_symm_mem hv.1) i
    rw [c.toOpenPartialHomeomorph_apply_symm hv.1] at this
    exact this.symm
  have hd : DifferentiableOn ℂ G S := hGd.mono hSsub
  have hosg := ((MMP.SeveralComplex.cauchy_osgood_laurent.{0, 0} ℂ).2.2.1 n S G hSo
    hd.continuousOn (fun ζ hζ j ↦ by
      have h1 : DifferentiableAt ℂ G (Function.update ζ j (ζ j)) := by
        rw [Function.update_eq_self]; exact hd.differentiableAt (hSo.mem_nhds hζ)
      have hu : DifferentiableAt ℂ (fun w : ℂ ↦ Function.update ζ j w) (ζ j) := by
        rw [differentiableAt_pi]
        intro i
        by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      exact h1.comp (ζ j) hu)).2.1
  refine ⟨G, hosg, fun y hy hy' ↦ ?_⟩
  rw [hG ⟨y, hy⟩ hy']
  congr 1
  funext i
  exact (c.toOpenPartialHomeomorph_apply hy i).symm

/-- Every point of `X^an` lies in an étale coordinate chart. -/
public theorem exists_mem_W [SmoothOfRelativeDimension n sX]
    (x : ComplexPoints sX) : ∃ c : EtaleCoordinateChart sX n, x ∈ c.W := by
  obtain ⟨U, z, hz, hx⟩ := (etaleCoordinate_atlas_of_smooth sX (n := n)).1 x
  obtain ⟨W, hW, hWo, hxW, hemb⟩ := (etaleCoordinate_atlas_of_smooth sX).2.1 U z hz x hx
  exact ⟨⟨U, z, hz, W, hW, hWo, ⟨x, hxW⟩, hemb⟩, hxW⟩

/-- **Holomorphic transition maps.** The transition map between two étale coordinate charts is
analytic on its domain. -/
public theorem analyticOnNhd_transition
    [SmoothOfRelativeDimension n sX] (c c' : EtaleCoordinateChart sX n) :
    AnalyticOnNhd ℂ (c.toOpenPartialHomeomorph.symm.trans c'.toOpenPartialHomeomorph)
      (c.toOpenPartialHomeomorph.symm.trans c'.toOpenPartialHomeomorph).source := by
  set e := c.toOpenPartialHomeomorph
  set e' := c'.toOpenPartialHomeomorph
  have hS : (e.symm.trans e').source = e.target ∩ e.symm ⁻¹' c'.W := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      source_toOpenPartialHomeomorph]
  have hG := fun j ↦ c.exists_analyticOnNhd c'.U (c'.z j)
  choose G hGa hGe using hG
  have hsub : (e.symm.trans e').source ⊆ e.target ∩ e.symm ⁻¹' chart c'.U := by
    rw [hS]
    exact fun v hv ↦ ⟨hv.1, c'.subset hv.2⟩
  have hpi : AnalyticOnNhd ℂ (fun v j ↦ G j v) (e.symm.trans e').source := fun v hv ↦
    AnalyticAt.pi fun j ↦ hGa j v (hsub hv)
  refine hpi.congr (e.symm.trans e').open_source fun v hv ↦ ?_
  rw [hS] at hv
  funext j
  have hW := c.toOpenPartialHomeomorph_symm_mem hv.1
  change G j v = e' (e.symm v) j
  rw [c'.toOpenPartialHomeomorph_apply hv.2 j, hGe j _ hW (c'.subset hv.2),
    c.toOpenPartialHomeomorph_apply_symm hv.1]

/-- The restriction of an étale coordinate chart to an open subset `O` meeting its domain. -/
@[expose] public noncomputable def restrict (c : EtaleCoordinateChart sX n)
    (O : Set (ComplexPoints sX)) (hO : IsOpen O) (hne : (c.W ∩ O).Nonempty) :
    EtaleCoordinateChart sX n where
  U := c.U
  z := c.z
  etale := c.etale
  W := c.W ∩ O
  subset := Set.inter_subset_left.trans c.subset
  isOpen := c.isOpen.inter hO
  nonempty := hne
  isOpenEmbedding := by
    have h := c.isOpenEmbedding.comp (IsOpenEmbedding.inclusion
      (Set.inter_subset_left : c.W ∩ O ⊆ c.W)
      ((c.isOpen.inter hO).preimage continuous_subtype_val))
    exact h

@[simp]
public lemma W_restrict (c : EtaleCoordinateChart sX n) (O : Set (ComplexPoints sX))
    (hO : IsOpen O) (hne : (c.W ∩ O).Nonempty) : (c.restrict O hO hne).W = c.W ∩ O :=
  rfl

end EtaleCoordinateChart

end Charts

section Manifold

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (n : ℕ)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {sX n} in
/-- An étale coordinate chart read in a model space `E` through a linear isomorphism
`L : ℂⁿ ≃ E`. -/
@[expose] public noncomputable def EtaleCoordinateChart.toChart (L : (Fin n → ℂ) ≃L[ℂ] E)
    (c : EtaleCoordinateChart sX n) : OpenPartialHomeomorph (ComplexPoints sX) E :=
  c.toOpenPartialHomeomorph.transHomeomorph L.toHomeomorph

variable {sX n} in
@[simp]
public lemma EtaleCoordinateChart.source_toChart (L : (Fin n → ℂ) ≃L[ℂ] E)
    (c : EtaleCoordinateChart sX n) : (c.toChart L).source = c.W := by
  simp [EtaleCoordinateChart.toChart]

variable {sX n} in
public lemma EtaleCoordinateChart.toChart_apply (L : (Fin n → ℂ) ≃L[ℂ] E)
    (c : EtaleCoordinateChart sX n) (y : ComplexPoints sX) :
    c.toChart L y = L (c.toOpenPartialHomeomorph y) := rfl

/-- The étale coordinate charts of `X^an`, read in a model space `E` through a linear isomorphism
`L : ℂⁿ ≃ E`, with a prescribed preferred chart `pick x ∋ x` at every point `x`: the atlas is
the set of all étale coordinate charts. -/
@[expose, instance_reducible]
public noncomputable def etaleChartedSpaceOf (L : (Fin n → ℂ) ≃L[ℂ] E)
    (pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W}) :
    ChartedSpace E (ComplexPoints sX) where
  atlas := Set.range (fun c : EtaleCoordinateChart sX n ↦ c.toChart L)
  chartAt x := (pick x).1.toChart L
  mem_chart_source x := by
    rw [EtaleCoordinateChart.source_toChart]
    exact (pick x).2
  chart_mem_atlas x := ⟨_, rfl⟩

public lemma chartAt_etaleChartedSpaceOf (L : (Fin n → ℂ) ≃L[ℂ] E)
    (pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
    (x : ComplexPoints sX) :
    letI := etaleChartedSpaceOf sX n L pick
    chartAt E x = (pick x).1.toChart L :=
  rfl

public lemma mem_atlas_etaleChartedSpaceOf (L : (Fin n → ℂ) ≃L[ℂ] E)
    (pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
    (c : EtaleCoordinateChart sX n) :
    letI := etaleChartedSpaceOf sX n L pick
    c.toChart L ∈ atlas E (ComplexPoints sX) :=
  ⟨c, rfl⟩

variable [SmoothOfRelativeDimension n sX]

/-- **`X^an` is a complex manifold.** The étale coordinate charts form an analytic atlas: its
transition maps are `C^N` for every `N`, including `ω`. -/
public theorem isManifold_etaleChartedSpaceOf (L : (Fin n → ℂ) ≃L[ℂ] E)
    (pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
    (N : WithTop ℕ∞) :
    letI := etaleChartedSpaceOf sX n L pick
    IsManifold 𝓘(ℂ, E) N (ComplexPoints sX) := by
  let := etaleChartedSpaceOf sX n L pick
  refine isManifold_of_contDiffOn _ _ _ ?_
  intro e e' he he'
  obtain ⟨c, rfl⟩ : e ∈ Set.range (fun c : EtaleCoordinateChart sX n ↦ c.toChart L) := he
  obtain ⟨c', rfl⟩ : e' ∈ Set.range (fun c : EtaleCoordinateChart sX n ↦ c.toChart L) := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.range_id, Set.inter_univ, Set.preimage_id_eq]
  set T := c.toOpenPartialHomeomorph.symm.trans c'.toOpenPartialHomeomorph
  have hT := c.analyticOnNhd_transition c'
  have hTc : ContDiffOn ℂ N T T.source := hT.contDiffOn T.open_source.uniqueDiffOn
  have hsrc : ((c.toChart L).symm.trans (c'.toChart L)).source = L.symm ⁻¹' T.source := by
    ext v
    simp [EtaleCoordinateChart.toChart, T]
  have hfun : ∀ v ∈ ((c.toChart L).symm.trans (c'.toChart L)).source,
      ((c.toChart L).symm.trans (c'.toChart L)) v = L (T (L.symm v)) := by
    intro v _
    simp [EtaleCoordinateChart.toChart, T]
  rw [hsrc] at hfun ⊢
  refine ContDiffOn.congr ?_ hfun
  exact L.contDiff.comp_contDiffOn (hTc.comp L.symm.contDiff.contDiffOn fun v hv ↦ hv)

/-- The étale coordinate charts of a scheme `X` smooth of relative dimension `n` over `ℂ`, read in a
model space `E` through a linear isomorphism `L : ℂⁿ ≃ E`, with some étale coordinate chart
containing `x` as preferred chart at `x`. -/
@[expose, instance_reducible]
public noncomputable def etaleChartedSpace (L : (Fin n → ℂ) ≃L[ℂ] E) :
    ChartedSpace E (ComplexPoints sX) :=
  etaleChartedSpaceOf sX n L fun x ↦
    ⟨(EtaleCoordinateChart.exists_mem_W (n := n) x).choose,
      (EtaleCoordinateChart.exists_mem_W (n := n) x).choose_spec⟩

/-- Every étale coordinate chart is in the atlas. -/
public lemma mem_atlas_etaleChartedSpace (L : (Fin n → ℂ) ≃L[ℂ] E)
    (c : EtaleCoordinateChart sX n) :
    letI := etaleChartedSpace sX n L
    c.toChart L ∈ atlas E (ComplexPoints sX) :=
  ⟨c, rfl⟩

/-- The étale coordinate charts of a scheme smooth over `ℂ` form an analytic atlas. -/
public theorem isManifold_etaleChartedSpace (L : (Fin n → ℂ) ≃L[ℂ] E) (N : WithTop ℕ∞) :
    letI := etaleChartedSpace sX n L
    IsManifold 𝓘(ℂ, E) N (ComplexPoints sX) :=
  isManifold_etaleChartedSpaceOf sX n L _ N

variable {sX n} in
/-- The étale coordinate charts of a scheme smooth of relative dimension `n` over `ℂ`, modelled on
`EuclideanSpace ℂ (Fin n)`. -/
public noncomputable instance instChartedSpaceEuclideanSpace :
    ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX) :=
  etaleChartedSpace sX n (EuclideanSpace.equiv (Fin n) ℂ).symm

variable {sX n} in
/-- A scheme smooth of relative dimension `n` over `ℂ` is a complex manifold of dimension `n`. -/
public instance instIsManifoldEuclideanSpace {N : WithTop ℕ∞} :
    IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) N (ComplexPoints sX) :=
  isManifold_etaleChartedSpace sX n _ N

/-- The étale coordinate charts are in the maximal atlas of `X^an`, for every smoothness
order. -/
public theorem toChart_mem_maximalAtlas (c : EtaleCoordinateChart sX n) (N : WithTop ℕ∞) :
    c.toChart (EuclideanSpace.equiv (Fin n) ℂ).symm ∈
      IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) N (ComplexPoints sX) :=
  StructureGroupoid.subset_maximalAtlas _ (mem_atlas_etaleChartedSpace sX n _ c)

end Manifold

section Topology

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- `X^an` is Hausdorff for `X` separated over `ℂ`. -/
public instance t2Space [IsSeparated sX] : T2Space (ComplexPoints sX) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  have : IsSeparated (X ↘ Spec (.of ℂ)) := ‹IsSeparated sX›
  have := MMP.UnderlyingSpace.t2Space_of_isSeparated (K := ℂ) X
  exact (homeomorphUnderlyingSpace (X := X)).isEmbedding.t2Space

/-- A function pulled back from the base `Spec ℂ` evaluates to the corresponding constant. -/
private lemma eval_appLE (V : X.Opens) (e : V ≤ sX ⁻¹ᵁ ⊤) (a : Γ(Spec (.of ℂ), ⊤))
    (y : chart (sX := sX) V) :
    ComplexPoints.eval V (sX.appLE ⊤ V e a) y = (Scheme.ΓSpecIso (.of ℂ)).hom a := by
  have h2 : y.1.hom ≫ sX = 𝟙 _ := y.1.2
  have key : sX.appLE ⊤ V e ≫ y.1.hom.appLE V ⊤ y.2.ge = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have aux : ∀ (f : Spec (.of ℂ) ⟶ Spec (.of ℂ)), f = 𝟙 _ → ∀ e, f.appLE ⊤ ⊤ e = 𝟙 _ := by
      rintro _ rfl e
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      exact (Spec (.of ℂ)).presheaf.map_id _
    exact aux _ h2 _
  exact congrArg (fun φ => (Scheme.ΓSpecIso (.of ℂ)).hom.hom (φ.hom a)) key

/-- The `ℂ`-points of an affine open are Lindelöf: their topology is coarser than the one
induced by the values of finitely many algebra generators, which embeds them in some `ℂ^N`. -/
private lemma isLindelof_chart [LocallyOfFiniteType sX] (U : X.affineOpens) :
    @IsLindelof _ (chartTopology (sX := sX) (U : X.Opens)) Set.univ := by
  have e : (U : X.Opens) ≤ sX ⁻¹ᵁ ⊤ := by simp
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType sX ‹_›
    ⟨⊤, isAffineOpen_top (Spec (.of ℂ))⟩ U e
  let := (sX.appLE ⊤ (U : X.Opens) e).hom.toAlgebra
  obtain ⟨t, ht⟩ := (hft : Algebra.FiniteType _ _).out
  let Φ : chart (sX := sX) (U : X.Opens) → (t → ℂ) := fun y i ↦ ComplexPoints.eval _ i.1 y
  let T : TopologicalSpace (chart (sX := sX) (U : X.Opens)) := TopologicalSpace.induced Φ
      inferInstance
  have hT : ∀ f, Continuous (ComplexPoints.eval (sX := sX) (U : X.Opens) f) := by
    intro f
    have hf : f ∈ (⊤ : Subalgebra Γ(Spec (.of ℂ), ⊤) Γ(X, (U : X.Opens))) := trivial
    rw [← ht] at hf
    induction hf using Algebra.adjoin_induction with
    | mem x hx =>
      exact (continuous_apply (A := fun _ : t ↦ ℂ) (⟨x, hx⟩ : t)).comp
        (continuous_induced_dom (f := Φ))
    | algebraMap a =>
      have : ComplexPoints.eval (sX := sX) (U : X.Opens) (algebraMap _ _ a) =
          fun _ ↦ (Scheme.ΓSpecIso (.of ℂ)).hom a := funext (eval_appLE _ e a)
      exact this ▸ continuous_const
    | add x y _ _ hx hy =>
      have : ComplexPoints.eval (sX := sX) (U : X.Opens) (x + y) =
          fun p ↦ ComplexPoints.eval _ x p + ComplexPoints.eval _ y p :=
        funext fun p ↦ map_add (evalHom _ p) x y
      exact this ▸ hx.add hy
    | mul x y _ _ hx hy =>
      have : ComplexPoints.eval (sX := sX) (U : X.Opens) (x * y) =
          fun p ↦ ComplexPoints.eval _ x p * ComplexPoints.eval _ y p :=
        funext fun p ↦ map_mul (evalHom _ p) x y
      exact this ▸ hx.mul hy
  have hle : T ≤ chartTopology (sX := sX) (U : X.Opens) :=
    le_iInf fun f ↦ continuous_iff_le_induced.1 (hT f)
  have : SecondCountableTopology (chart (sX := sX) (U : X.Opens)) :=
    Topology.IsInducing.secondCountableTopology (f := Φ) ⟨rfl⟩
  have := @IsLindelof.image _ _ T (chartTopology (sX := sX) (U : X.Opens)) _ _
    isLindelof_univ (continuous_id_of_le hle)
  rwa [Set.image_id] at this

/-- `X^an` is Lindelöf for `X` quasi-compact and locally of finite type over `ℂ`. -/
public theorem isLindelof_univ [LocallyOfFiniteType sX] [QuasiCompact sX] :
    IsLindelof (Set.univ : Set (ComplexPoints sX)) := by
  have hX : IsCompact (Set.univ : Set X) := by
    simpa using QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U : Set X) := fun x _ ↦ by
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hxW⟩
  obtain ⟨s, hs⟩ := hX.elim_finite_subcover _ (fun U : X.affineOpens ↦ U.1.isOpen) hcov
  have hsub : (Set.univ : Set (ComplexPoints sX)) ⊆
      ⋃ U ∈ (s : Set X.affineOpens), Subtype.val '' (Set.univ : Set (chart (sX := sX) (U :
          X.Opens))) := by
    intro y _
    obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y.toScheme))
    exact Set.mem_iUnion₂.2 ⟨U, hU, ⟨y, mem_chart_iff.2 hyU⟩, trivial, rfl⟩
  refine IsLindelof.of_isClosed_subset ?_ isClosed_univ hsub
  refine s.finite_toSet.isLindelof_biUnion fun U _ ↦ ?_
  exact @IsLindelof.image _ _ (chartTopology (sX := sX) (U : X.Opens)) _ _ _
    (isLindelof_chart U) (continuous_chart_val U)

/-- `X^an` is second countable for `X` quasi-compact and smooth of relative dimension `n`
over `ℂ`. -/
public theorem secondCountableTopology (n : ℕ) [QuasiCompact sX]
    [SmoothOfRelativeDimension n sX] : SecondCountableTopology (ComplexPoints sX) := by
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  obtain ⟨r, hr, hcov⟩ := (isLindelof_univ (sX := sX)).elim_countable_subcover
    (fun x : ComplexPoints sX ↦ (chartAt (EuclideanSpace ℂ (Fin n)) x).source)
    (fun x ↦ (chartAt (EuclideanSpace ℂ (Fin n)) x).open_source)
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, mem_chart_source _ x⟩)
  exact ChartedSpace.secondCountable_of_countable_cover (EuclideanSpace ℂ (Fin n))
    (Set.eq_univ_of_univ_subset hcov) hr

end Topology

section Realize

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {n m : ℕ}

/-- **Realized morphisms are holomorphic in étale coordinates.** For a morphism `g : X ⟶ Y` of
smooth complex varieties over `ℂ`, read in étale coordinate charts `c` around `x` and `c'`
around `g(x)`, the realized map `y ↦ c'(g(c⁻¹ y))` is analytic at `c(x)`. -/
public theorem EtaleCoordinateChart.analyticAt_realize
    [SmoothOfRelativeDimension n sX] (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (c : EtaleCoordinateChart sX n) (c' : EtaleCoordinateChart sY m) {x : ComplexPoints sX}
    (hx : x ∈ c.W) (hgx : realize g hg x ∈ c'.W) :
    AnalyticAt ℂ
      (fun v ↦ c'.toOpenPartialHomeomorph (realize g hg (c.toOpenPartialHomeomorph.symm v)))
      (c.toOpenPartialHomeomorph x) := by
  set e := c.toOpenPartialHomeomorph
  set e' := c'.toOpenPartialHomeomorph
  have hG := fun j ↦ c.exists_analyticOnNhd (g ⁻¹ᵁ c'.U) (g.app c'.U (c'.z j))
  choose G hGa hGe using hG
  have hxs : x ∈ e.source := by rwa [c.source_toOpenPartialHomeomorph]
  have hN : e.target ∩ e.symm ⁻¹' (realize g hg ⁻¹' c'.W) ∈ 𝓝 (e x) :=
    (e.isOpen_inter_preimage_symm (c'.isOpen.preimage (continuous_realize g hg))).mem_nhds
      ⟨e.map_source hxs, by rwa [Set.mem_preimage, e.left_inv hxs]⟩
  have hsub : ∀ v ∈ e.target ∩ e.symm ⁻¹' (realize g hg ⁻¹' c'.W),
      v ∈ e.target ∩ e.symm ⁻¹' chart (g ⁻¹ᵁ c'.U) := fun v hv ↦
    ⟨hv.1, (mem_chart_preimage_iff g hg c'.U _).2 (c'.subset hv.2)⟩
  have hpi : AnalyticAt ℂ (fun v j ↦ G j v) (e x) :=
    AnalyticAt.pi fun j ↦ hGa j _ (hsub _ (mem_of_mem_nhds hN))
  refine hpi.congr ?_
  filter_upwards [hN] with v hv
  funext j
  have hW := c.toOpenPartialHomeomorph_symm_mem hv.1
  have hy := (mem_chart_preimage_iff g hg c'.U _).2 (c'.subset hv.2)
  rw [c'.toOpenPartialHomeomorph_apply hv.2 j, ← eval_app_realize g hg c'.U _ _ hy,
    hGe j _ hW hy, c.toOpenPartialHomeomorph_apply_symm hv.1]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- **Realized morphisms are holomorphic.** For a morphism `g : X ⟶ Y` of smooth complex
varieties over `ℂ`, the realized map `X^an → Y^an` is `C^N` for every `N` (including `ω`) in
the étale coordinate charts, read in any model spaces and with any preferred charts. -/
public theorem contMDiff_realize_etaleChartedSpaceOf
    [SmoothOfRelativeDimension n sX]
    [SmoothOfRelativeDimension m sY] (L : (Fin n → ℂ) ≃L[ℂ] E) (L' : (Fin m → ℂ) ≃L[ℂ] F)
    (pickX : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
    (pickY : ∀ y : ComplexPoints sY, {c : EtaleCoordinateChart sY m // y ∈ c.W})
    (N : WithTop ℕ∞) (g : X ⟶ Y) (hg : g ≫ sY = sX) :
    letI := etaleChartedSpaceOf sX n L pickX
    letI := etaleChartedSpaceOf sY m L' pickY
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) N (realize g hg) := by
  let := etaleChartedSpaceOf sX n L pickX
  let := etaleChartedSpaceOf sY m L' pickY
  have := isManifold_etaleChartedSpaceOf sX n L pickX N
  have := isManifold_etaleChartedSpaceOf sY m L' pickY N
  have : FiniteDimensional ℂ F := L'.toLinearEquiv.finiteDimensional
  have := FiniteDimensional.complete ℂ F
  intro x
  rw [contMDiffAt_iff_of_mem_source (x := x) (y := realize g hg x) (mem_chart_source _ x)
    (mem_chart_source _ _)]
  refine ⟨(continuous_realize g hg).continuousAt, ?_⟩
  set c := (pickX x).1
  set c' := (pickY (realize g hg x)).1
  have ha := c.analyticAt_realize g hg c' (pickX x).2 (pickY (realize g hg x)).2
  have hA : AnalyticAt ℂ (fun w ↦ L' (c'.toOpenPartialHomeomorph
      (realize g hg (c.toOpenPartialHomeomorph.symm (L.symm w)))))
      (L (c.toOpenPartialHomeomorph x)) := by
    refine L'.analyticAt _ |>.comp ?_
    refine AnalyticAt.comp (g := fun v ↦ c'.toOpenPartialHomeomorph
      (realize g hg (c.toOpenPartialHomeomorph.symm v))) ?_ (L.symm.analyticAt _)
    simpa using ha
  simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl,
    OpenPartialHomeomorph.toFun_eq_coe, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
    modelWithCornersSelf_coe, Set.range_id]
  exact (hA.contDiffAt).contDiffWithinAt

/-- Realized morphisms of smooth complex varieties are holomorphic in the étale coordinate
charts, read in any model spaces. -/
public theorem contMDiff_realize_etaleChartedSpace
    [SmoothOfRelativeDimension n sX]
    [SmoothOfRelativeDimension m sY] (L : (Fin n → ℂ) ≃L[ℂ] E) (L' : (Fin m → ℂ) ≃L[ℂ] F)
    (N : WithTop ℕ∞) (g : X ⟶ Y) (hg : g ≫ sY = sX) :
    letI := etaleChartedSpace sX n L
    letI := etaleChartedSpace sY m L'
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) N (realize g hg) :=
  contMDiff_realize_etaleChartedSpaceOf L L' _ _ N g hg

/-- For smooth complex varieties `X`, `Y` of dimensions `n`, `m`, realized morphisms are
holomorphic maps of complex manifolds. -/
public theorem contMDiff_realize
    [SmoothOfRelativeDimension n sX]
    [SmoothOfRelativeDimension m sY] (N : WithTop ℕ∞) (g : X ⟶ Y) (hg : g ≫ sY = sX) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin m)) N
      (realize g hg) :=
  contMDiff_realize_etaleChartedSpace _ _ N g hg

end Realize

section RelativeCoordinates

open IsLocalRing TensorProduct KaehlerDifferential

/-- Let `R → S → T` with `S → T` formally smooth, `S`, `T` local and `Ω[S⁄R]` free. If
`ds ⊗ 1 ≠ 0` in `κ(S) ⊗ Ω[S⁄R]`, then `d(s|_T) ⊗ 1 ≠ 0` in `κ(T) ⊗ Ω[T⁄R]`: the differential of
a smooth map is injective on fibres. -/
private theorem tmul_D_algebraMap_ne_zero {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [IsLocalRing S] [IsLocalRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra.FormallySmooth S T] [Module.Free S Ω[S⁄R]] (s : S)
    (hs : (1 : ResidueField S) ⊗ₜ[S] D R S s ≠ 0) :
    (1 : ResidueField T) ⊗ₜ[T] D R T (algebraMap S T s) ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis S Ω[S⁄R]
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (b.repr (D R S s) i) := by
    by_contra! h
    apply hs
    rw [← b.linearCombination_repr (D R S s), Finsupp.linearCombination_apply, Finsupp.sum,
      tmul_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [tmul_smul, ← algebraMap_smul (ResidueField S), IsLocalRing.ResidueField.algebraMap_eq,
      (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 (h j)), zero_smul]
  let ψ : Ω[S⁄R] →ₗ[S] T := (Algebra.linearMap S T) ∘ₗ b.coord i
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hinj : Function.Injective (mapBaseChange R S T) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
    have : Subsingleton (Algebra.H1Cotangent S T) := ((Algebra.formallySmooth_iff S T).1 ‹_›).2
    rw [Subsingleton.elim y 0, map_zero]
  have hsurj : Function.Surjective (map R S T T) := map_surjective R S T
  obtain ⟨l₀, hl₀⟩ := Module.projective_lifting_property (map R S T T) LinearMap.id hsurj
  have htf := (hex.split_tfae hinj hsurj).out 1 2
  obtain ⟨l, hl⟩ := htf.1 ⟨l₀, hl₀⟩
  let Φ : Ω[T⁄R] →ₗ[T] T := ψ.liftBaseChange T ∘ₗ l
  have hΦ : Φ (D R T (algebraMap S T s)) = algebraMap S T (b.repr (D R S s) i) := by
    have : D R T (algebraMap S T s) = mapBaseChange R S T (1 ⊗ₜ D R S s) := by
      rw [mapBaseChange_tmul, one_smul, map_D]
    simp only [Φ, LinearMap.comp_apply, this]
    rw [← LinearMap.comp_apply l, hl, LinearMap.id_apply, LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  intro h0
  have h1 := congrArg (TensorProduct.rid T (ResidueField T) ∘ (Φ.baseChange (ResidueField T))) h0
  simp only [Function.comp_apply, LinearMap.baseChange_tmul, map_zero, hΦ,
    TensorProduct.rid_tmul, Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq] at h1
  exact ((hi.map (algebraMap S T)).map (residue T)).ne_zero h1

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}

/-- The restriction of `sX` to the open `⊤` is smooth of relative dimension `n` when `sX` is. -/
private theorem smoothOfRelativeDimension_top_ι [SmoothOfRelativeDimension n sX] :
    SmoothOfRelativeDimension n ((⊤ : X.Opens).ι ≫ sX) :=
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} n)
  IsZariskiLocalAtSource.comp ‹_› _

/-- On a scheme smooth of relative dimension `n` over `ℂ`, the stalk of `Ω_{X/ℂ}` at every
point has rank `n`. -/
private theorem finrank_kaehlerDifferential_stalk (sX : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension n sX] (p : X) :
    letI := (sX.stalkMap p).hom.toAlgebra
    Module.finrank (X.presheaf.stalk p)
      Ω[X.presheaf.stalk p ⁄ (Spec (.of ℂ)).presheaf.stalk (sX p)] = n := by
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have := smoothOfRelativeDimension_top_ι (n := n) (sX := sX)
  exact finrank_kaehlerDifferential_stalk_of_mem ⊤ p trivial

/-- **Completing differentials to étale coordinates.** Let `X` be smooth of relative dimension
`n` over `ℂ`, `p ∈ X` and `a_1, …, a_k` sections over an open `V ∋ p` whose differentials are
linearly independent in the fibre `κ(p) ⊗ Ω_{X/ℂ,p}`. Then the `a_i` are among a system of
étale coordinates `z_1, …, z_n` on an open `U ∋ p` inside `V`: `a_i = z_{c i}` for an injection
`c : Fin k ↪ Fin n`. -/
public theorem exists_etale_coordinates_extending [SmoothOfRelativeDimension n sX]
    (p : X) (V : X.Opens) (hpV : p ∈ V) {k : ℕ} (a : Fin k → Γ(X, V))
    (ha : letI := (sX.stalkMap p).hom.toAlgebra
      LinearIndependent (ResidueField (X.presheaf.stalk p)) fun i ↦
        (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
          D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
            (X.presheaf.germ V p hpV (a i))) :
    ∃ (U : X.Opens) (_ : p ∈ U) (hUV : U ≤ V) (z : Fin n → Γ(X, U)) (c : Fin k ↪ Fin n),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) ∧
      ∀ i, z (c i) = X.presheaf.map (homOfLE hUV).op (a i) := by
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have := smoothOfRelativeDimension_top_ι (n := n) (sX := sX)
  exact exists_etale_coordinates_extending_of_mem ⊤ p trivial V hpV a ha

/-- **Completing a differential to étale coordinates.** Let `X` be smooth of relative dimension
`n` over `ℂ`, `p ∈ X` and `a` a section over an open `V ∋ p` whose differential is nonzero in
the fibre `κ(p) ⊗ Ω_{X/ℂ,p}`. Then `a` is one of a system of étale coordinates `z_1, …, z_n` on
an open `U ∋ p` inside `V`. -/
public theorem exists_etale_coordinates_eq_of_tmul_D_ne_zero [SmoothOfRelativeDimension n sX]
    (p : X) (V : X.Opens) (hpV : p ∈ V) (a : Γ(X, V))
    (ha : letI := (sX.stalkMap p).hom.toAlgebra
      (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (X.presheaf.germ V p hpV a) ≠ 0) :
    ∃ (U : X.Opens) (_ : p ∈ U) (hUV : U ≤ V) (z : Fin n → Γ(X, U)) (j₀ : Fin n),
      Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))) ∧
      z j₀ = X.presheaf.map (homOfLE hUV).op a := by
  letI := (sX.stalkMap p).hom.toAlgebra
  obtain ⟨U, hpU, hUV, z, c, hz, hzc⟩ := exists_etale_coordinates_extending (n := n) p V hpV
    (fun _ : Fin 1 ↦ a) (by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      rw [Fin.eq_zero i]
      simp only [Fin.sum_univ_one] at hc
      by_contra h0
      apply ha
      have := congrArg ((c 0)⁻¹ • ·) hc
      simp only [smul_zero, smul_smul, inv_mul_cancel₀ h0, one_smul] at this
      exact this)
  exact ⟨U, hpU, hUV, z, c 0, hz, hzc 0⟩

/-- **Pull-backs along a smooth morphism keep nonzero differentials.** Let `g : X ⟶ B` be a
morphism over `ℂ`, smooth at `p`, with `B` smooth over `ℂ`. If a section `w` of `𝒪_B` near
`g(p)` has nonzero differential in `κ(g p) ⊗ Ω_{B/ℂ, g p}`, then `g^* w` has nonzero differential
in `κ(p) ⊗ Ω_{X/ℂ, p}`. -/
public theorem tmul_D_germ_app_ne_zero {B : Scheme.{0}} {sB : B ⟶ Spec (.of ℂ)} [Smooth sB]
    (g : X ⟶ B) (hg : g ≫ sB = sX) (p : X) (hgp : (g.stalkMap p).hom.FormallySmooth)
    (V : B.Opens) (hpV : g p ∈ V) (w : Γ(B, V))
    (hw : letI := (sB.stalkMap (g p)).hom.toAlgebra
      (1 : ResidueField (B.presheaf.stalk (g p))) ⊗ₜ[B.presheaf.stalk (g p)]
        D ((Spec (.of ℂ)).presheaf.stalk (sB (g p))) (B.presheaf.stalk (g p))
          (B.presheaf.germ V (g p) hpV w) ≠ 0) :
    letI := (sX.stalkMap p).hom.toAlgebra
    (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
      D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
        (X.presheaf.germ (g ⁻¹ᵁ V) p hpV (g.app V w)) ≠ 0 := by
  subst hg
  letI : Algebra ((Spec (.of ℂ)).presheaf.stalk (sB (g p))) (B.presheaf.stalk (g p)) :=
    (sB.stalkMap (g p)).hom.toAlgebra
  letI : Algebra (B.presheaf.stalk (g p)) (X.presheaf.stalk p) := (g.stalkMap p).hom.toAlgebra
  letI : Algebra ((Spec (.of ℂ)).presheaf.stalk (sB (g p))) (X.presheaf.stalk p) :=
    ((g ≫ sB).stalkMap p).hom.toAlgebra
  have : IsScalarTower ((Spec (.of ℂ)).presheaf.stalk (sB (g p))) (B.presheaf.stalk (g p))
      (X.presheaf.stalk p) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((g ≫ sB).stalkMap p).hom = _
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have : Algebra.FormallySmooth (B.presheaf.stalk (g p)) (X.presheaf.stalk p) := hgp
  obtain ⟨hfree, -⟩ := MMP.Flips.ResolutionInputs.free_finite_kaehlerDifferential_stalk sB (g p)
  have := tmul_D_algebraMap_ne_zero (R := (Spec (.of ℂ)).presheaf.stalk (sB (g p)))
    (T := X.presheaf.stalk p) (B.presheaf.germ V (g p) hpV w) hw
  rwa [show algebraMap (B.presheaf.stalk (g p)) (X.presheaf.stalk p)
    (B.presheaf.germ V (g p) hpV w) = X.presheaf.germ (g ⁻¹ᵁ V) p hpV (g.app V w) from
      Scheme.Hom.germ_stalkMap_apply g V p hpV w] at this

end RelativeCoordinates

section Curves

variable {B : Scheme.{0}} {sB : B ⟶ Spec (.of ℂ)}
  [SmoothOfRelativeDimension 1 sB]

open IsLocalRing TensorProduct KaehlerDifferential in
/-- Every point `b` of a smooth complex curve lies in an étale coordinate chart whose coordinate
has nonzero differential at `b`. -/
public theorem exists_curveChart (b : ComplexPoints sB) :
    ∃ c : EtaleCoordinateChart sB 1, b ∈ c.W ∧ ∀ hb : (toScheme b) ∈ c.U,
      letI := (sB.stalkMap (toScheme b)).hom.toAlgebra
      (1 : ResidueField (B.presheaf.stalk (toScheme b))) ⊗ₜ[B.presheaf.stalk (toScheme b)]
        D ((Spec (.of ℂ)).presheaf.stalk (sB (toScheme b))) (B.presheaf.stalk (toScheme b))
          (B.presheaf.germ c.U (toScheme b) hb (c.z 0)) ≠ 0 := by
  classical
  have : Smooth sB := SmoothOfRelativeDimension.smooth 1 sB
  letI := (sB.stalkMap (toScheme b)).hom.toAlgebra
  obtain ⟨hfree, hfin⟩ :=
    MMP.Flips.ResolutionInputs.free_finite_kaehlerDifferential_stalk sB (toScheme b)
  have hdim : Module.finrank (ResidueField (B.presheaf.stalk (toScheme b)))
      (ResidueField (B.presheaf.stalk (toScheme b)) ⊗[B.presheaf.stalk (toScheme b)]
        Ω[B.presheaf.stalk (toScheme b) ⁄
          (Spec (.of ℂ)).presheaf.stalk (sB (toScheme b))]) = 1 := by
    rw [Module.finrank_baseChange]
    exact finrank_kaehlerDifferential_stalk sB (toScheme b)
  obtain ⟨r, hr⟩ : ∃ r : B.presheaf.stalk (toScheme b),
      (1 : ResidueField (B.presheaf.stalk (toScheme b))) ⊗ₜ[B.presheaf.stalk (toScheme b)]
        D ((Spec (.of ℂ)).presheaf.stalk (sB (toScheme b))) (B.presheaf.stalk (toScheme b))
          r ≠ 0 := by
    by_contra! h
    have hsp := span_tmul_D (R := (Spec (.of ℂ)).presheaf.stalk (sB (toScheme b)))
      (T := B.presheaf.stalk (toScheme b))
    rw [(Submodule.span_eq_bot.2 (by rintro _ ⟨r, rfl⟩; exact h r)), top_le_iff] at hsp
    rw [← finrank_top, ← hsp, finrank_bot] at hdim
    exact zero_ne_one hdim
  obtain ⟨V, hpV, a, rfl⟩ := B.presheaf.exists_germ_eq r
  obtain ⟨U, hpU, hUV, z, j₀, hz, hzj⟩ :=
    exists_etale_coordinates_eq_of_tmul_D_ne_zero (sX := sB) (n := 1) (toScheme b) V hpV a hr
  obtain rfl : j₀ = 0 := Subsingleton.elim _ _
  obtain ⟨W, hW, hWo, hbW, hemb⟩ :=
    (etaleCoordinate_atlas_of_smooth sB).2.1 U z hz b (mem_chart_iff.2 hpU)
  refine ⟨⟨U, z, hz, W, hW, hWo, ⟨b, hbW⟩, hemb⟩, hbW, fun hb ↦ ?_⟩
  change (1 : ResidueField (B.presheaf.stalk (toScheme b))) ⊗ₜ[B.presheaf.stalk (toScheme b)]
    D ((Spec (.of ℂ)).presheaf.stalk (sB (toScheme b))) (B.presheaf.stalk (toScheme b))
      (B.presheaf.germ U (toScheme b) hb (z 0)) ≠ 0
  rw [hzj, B.presheaf.germ_res_apply]
  exact hr

/-- The preferred étale coordinate chart of a smooth complex curve `B` at `b`, from which the
chart `chartAt ℂ b` of `instChartedSpaceComplex` is read: its coordinate has nonzero
differential at `b`. -/
public noncomputable def curveChart (b : ComplexPoints sB) : EtaleCoordinateChart sB 1 :=
  (exists_curveChart b).choose

public lemma mem_curveChart_W (b : ComplexPoints sB) : b ∈ (curveChart b).W :=
  (exists_curveChart b).choose_spec.1

open IsLocalRing TensorProduct KaehlerDifferential in
/-- The coordinate of the preferred chart of a smooth complex curve at `b` has nonzero
differential at `b`. -/
public lemma tmul_D_germ_curveChart_ne_zero (b : ComplexPoints sB)
    (hb : toScheme b ∈ (curveChart b).U) :
    letI := (sB.stalkMap (toScheme b)).hom.toAlgebra
    (1 : ResidueField (B.presheaf.stalk (toScheme b))) ⊗ₜ[B.presheaf.stalk (toScheme b)]
      D ((Spec (.of ℂ)).presheaf.stalk (sB (toScheme b))) (B.presheaf.stalk (toScheme b))
        (B.presheaf.germ (curveChart b).U (toScheme b) hb ((curveChart b).z 0)) ≠ 0 :=
  (exists_curveChart b).choose_spec.2 hb

/-- The étale coordinate charts of a smooth complex curve, modelled on `ℂ`, with preferred
charts `MMP.Analytic.ComplexPoints.curveChart`. -/
public noncomputable instance instChartedSpaceComplex : ChartedSpace ℂ (ComplexPoints sB) :=
  etaleChartedSpaceOf sB 1 (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ)
    fun b ↦ ⟨curveChart b, mem_curveChart_W b⟩

/-- A smooth complex curve is a Riemann surface. -/
public instance instIsManifoldComplex {N : WithTop ℕ∞} : IsManifold 𝓘(ℂ) N (ComplexPoints sB) :=
  isManifold_etaleChartedSpaceOf sB 1 _ _ N

public lemma source_chartAt_complex (b : ComplexPoints sB) :
    (chartAt ℂ b).source = (curveChart b).W :=
  (curveChart b).source_toChart _

/-- For `X` smooth of relative dimension `n` over `ℂ` and a smooth complex curve `B`, realized
morphisms are holomorphic maps from a complex manifold to a Riemann surface. -/
public theorem contMDiff_realize_curve {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}
    [SmoothOfRelativeDimension n sX] (N : WithTop ℕ∞)
    (g : X ⟶ B) (hg : g ≫ sB = sX) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) N (realize g hg) :=
  contMDiff_realize_etaleChartedSpaceOf _ _ _ _ N g hg

end Curves

section Adapted

variable {X B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)} {n : ℕ}

/-- **Coordinate hyperplanes.** If, on an étale coordinate chart `W`, a set `D ⊆ X^an` is the
zero locus of the coordinate `z_j`, then the chart carries `D ∩ W` onto the trace of the
hyperplane `{v_j = 0}` on its image. -/
public theorem EtaleCoordinateChart.image_toChart_inter_eq (c : EtaleCoordinateChart sX n)
    (D : Set (ComplexPoints sX)) (j : Fin n)
    (hD : ∀ (y : ComplexPoints sX) (hy : y ∈ c.W),
      y ∈ D ↔ eval c.U (c.z j) ⟨y, c.subset hy⟩ = 0) :
    c.toChart (EuclideanSpace.equiv (Fin n) ℂ).symm ''
        (D ∩ (c.toChart (EuclideanSpace.equiv (Fin n) ℂ).symm).source) =
      (c.toChart (EuclideanSpace.equiv (Fin n) ℂ).symm).target ∩ {v | v j = 0} := by
  set e := c.toChart (EuclideanSpace.equiv (Fin n) ℂ).symm
  have hsrc : e.source = c.W := c.source_toChart _
  have happ : ∀ y (hy : y ∈ c.W), e y j = eval c.U (c.z j) ⟨y, c.subset hy⟩ := fun y hy ↦
    c.toOpenPartialHomeomorph_apply hy j
  ext v
  constructor
  · rintro ⟨y, ⟨hyD, hys⟩, rfl⟩
    rw [hsrc] at hys
    refine ⟨e.map_source (by rwa [hsrc]), ?_⟩
    change e y j = 0
    rw [happ y hys]
    exact (hD y hys).1 hyD
  · rintro ⟨hv, hv0⟩
    have hs := e.map_target hv
    have hyW : e.symm v ∈ c.W := by rwa [hsrc] at hs
    refine ⟨e.symm v, ⟨(hD _ hyW).2 ?_, hs⟩, e.right_inv hv⟩
    rw [← happ _ hyW, e.right_inv hv]
    exact hv0

/-- **Simple normal crossing charts.** Let `D : ι → Set X^an` be a family of subsets, `x` a
point of an étale coordinate chart `W`, `s` a finite set of indices and `j : s ↪ Fin n` such
that `D i` misses `W` for `i ∉ s` and, on `W`, `D i` is the zero locus of the coordinate
`z_{j i}` for `i ∈ s`. Then the chart is in the maximal atlas of `X^an` and carries each `D i`
onto a coordinate hyperplane: the simultaneous coordinate charts of an snc divisor. -/
public theorem exists_mem_maximalAtlas_image_eq_hyperplane
    [SmoothOfRelativeDimension n sX]
    (pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
    (N : WithTop ℕ∞) {ι : Type*} (D : ι → Set (ComplexPoints sX)) (x : ComplexPoints sX)
    (c : EtaleCoordinateChart sX n) (hx : x ∈ c.W) (s : Finset ι) (j : s ↪ Fin n)
    (hout : ∀ i ∉ s, D i ∩ c.W = ∅)
    (hin : ∀ (i : s) (y : ComplexPoints sX) (hy : y ∈ c.W),
      y ∈ D i ↔ eval c.U (c.z (j i)) ⟨y, c.subset hy⟩ = 0) :
    letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
    ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) N (ComplexPoints sX),
      x ∈ φ.source ∧ ∃ (s : Finset ι) (c : s ↪ Fin n),
        (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
        ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0} := by
  let := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
  have := isManifold_etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick N
  refine ⟨c.toChart (EuclideanSpace.equiv (Fin n) ℂ).symm,
    StructureGroupoid.subset_maximalAtlas _ (mem_atlas_etaleChartedSpaceOf sX n _ pick c),
    by rwa [c.source_toChart], s, j, fun i hi ↦ by rw [c.source_toChart]; exact hout i hi,
    fun i ↦ c.image_toChart_inter_eq (D i) (j i) (hin i)⟩

variable [SmoothOfRelativeDimension 1 sB]

/-- **Realized morphisms in adapted coordinates.** Let `g : X ⟶ B` be a morphism to a smooth
complex curve, and suppose that the preferred chart at `x` has `g^*w` as its `j₀`-th
coordinate, where `w` is the coordinate of the preferred chart of `B` at `g(x)`. Then the
differential of `g^an` at `x` is the `j₀`-th coordinate projection. -/
public theorem hasMFDerivAt_realize_of_adapted
    (pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
    (g : X ⟶ B) (hg : g ≫ sB = sX) (x : ComplexPoints sX) (j₀ : Fin n)
    (hadapt : ∀ y ∈ (pick x).1.W, realize g hg y ∈ (chartAt ℂ (realize g hg x)).source ∧
      chartAt ℂ (realize g hg x) (realize g hg y) = (pick x).1.toOpenPartialHomeomorph y j₀) :
    letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
    HasMFDerivAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (realize g hg) x
      (EuclideanSpace.proj j₀ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) := by
  let := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
  refine ⟨(continuous_realize g hg).continuousAt, ?_⟩
  set c := (pick x).1
  set e := c.toChart (EuclideanSpace.equiv (Fin n) ℂ).symm
  have he : chartAt (EuclideanSpace ℂ (Fin n)) x = e := rfl
  have hxs : x ∈ e.source := by rw [c.source_toChart]; exact (pick x).2
  have hev : writtenInExtChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) x (realize g hg)
      =ᶠ[𝓝 (e x)] fun v ↦ (EuclideanSpace.proj j₀ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) v := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hxs)] with v hv
    have hW : e.symm v ∈ c.W := by
      have := e.map_target hv
      rwa [c.source_toChart] at this
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, he,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
    rw [(hadapt _ hW).2]
    have h1 : e (e.symm v) = v := e.right_inv hv
    change (EuclideanSpace.equiv (Fin n) ℂ).symm (c.toOpenPartialHomeomorph (e.symm v)) = v at h1
    have h2 := congrArg (fun w : EuclideanSpace ℂ (Fin n) ↦ w j₀) h1
    simp only at h2
    rw [show (EuclideanSpace.proj j₀ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) v = v j₀ by simp, ← h2]
    rfl
  have hd := ((EuclideanSpace.proj j₀ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasFDerivAt
    (x := e x)).congr_of_eventuallyEq hev
  simp only [extChartAt_coe, he, modelWithCornersSelf_coe, Function.comp_apply, id_eq,
    Set.range_id]
  exact hd.hasFDerivWithinAt

/-- **Adapted coordinates give a submersion.** Under the hypotheses of
`MMP.Analytic.ComplexPoints.hasMFDerivAt_realize_of_adapted`, the differential of `g^an` at `x`
is surjective. -/
public theorem surjective_mfderiv_realize_of_adapted
    (pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
    (g : X ⟶ B) (hg : g ≫ sB = sX) (x : ComplexPoints sX) (j₀ : Fin n)
    (hadapt : ∀ y ∈ (pick x).1.W, realize g hg y ∈ (chartAt ℂ (realize g hg x)).source ∧
      chartAt ℂ (realize g hg x) (realize g hg y) = (pick x).1.toOpenPartialHomeomorph y j₀) :
    letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
    Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (realize g hg) x) := by
  let := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
  rw [(hasMFDerivAt_realize_of_adapted pick g hg x j₀ hadapt).mfderiv]
  intro (a : ℂ)
  refine ⟨EuclideanSpace.single j₀ a, ?_⟩
  change EuclideanSpace.proj j₀ (EuclideanSpace.single j₀ a) = a
  simp

/-- **Adapted coordinates give a submersion on strata.** Under the hypotheses of
`MMP.Analytic.ComplexPoints.hasMFDerivAt_realize_of_adapted`, let `S ⊆ X^an` contain every
point of the preferred chart at `x` whose coordinates indexed by `J` are those of `x`, where
`j₀ ∉ J`. Then `dg_x` is nonzero on the tangent cone of `S` at `x`. -/
public theorem exists_mem_tangentConeAt_mfderiv_realize_ne_zero
    (pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W})
    (g : X ⟶ B) (hg : g ≫ sB = sX) (x : ComplexPoints sX) (j₀ : Fin n)
    (hadapt : ∀ y ∈ (pick x).1.W, realize g hg y ∈ (chartAt ℂ (realize g hg x)).source ∧
      chartAt ℂ (realize g hg x) (realize g hg y) = (pick x).1.toOpenPartialHomeomorph y j₀)
    (S : Set (ComplexPoints sX)) (J : Set (Fin n)) (hj₀ : j₀ ∉ J)
    (hS : letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
      ∀ v ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).target,
        (∀ i ∈ J, v i = chartAt (EuclideanSpace ℂ (Fin n)) x x i) →
          (chartAt (EuclideanSpace ℂ (Fin n)) x).symm v ∈ S) :
    letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
    ∃ v ∈ tangentConeAt ℂ
        ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).target ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).symm ⁻¹' S)
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x),
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (realize g hg) x v ≠ 0 := by
  let := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
  rw [(hasMFDerivAt_realize_of_adapted pick g hg x j₀ hadapt).mfderiv]
  set e := chartAt (EuclideanSpace ℂ (Fin n)) x
  set u : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j₀ 1
  refine ⟨u, ?_, ?_⟩
  swap
  · change EuclideanSpace.proj j₀ u ≠ 0
    simp [u]
  simp only [extChartAt_target, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Set.range_id, Set.inter_univ, Set.preimage_id_eq,
    Function.comp_apply, id_eq]
  refine mem_tangentConeAt_of_add_smul_mem (l := 𝓝[≠] (0 : ℂ)) (c := id) Filter.tendsto_id ?_
  have hxs : x ∈ e.source := mem_chart_source _ x
  have hT : ∀ᶠ t : ℂ in 𝓝 0, e x + t • u ∈ e.target := by
    have hc : Continuous fun t : ℂ ↦ e x + t • u := by fun_prop
    have := hc.continuousAt (x := 0) |>.preimage_mem_nhds
      (e.open_target.mem_nhds (by simpa using e.map_source hxs))
    exact this
  filter_upwards [nhdsWithin_le_nhds hT] with t ht
  refine ⟨ht, hS _ ht fun i hi ↦ ?_⟩
  have hne : i ≠ j₀ := fun h ↦ hj₀ (h ▸ hi)
  simp [u, hne]
  rfl

end Adapted

section AdaptedCharts

variable {X B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)} {n : ℕ}

private lemma eval_res {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : ComplexPoints sX)
    (hy : y ∈ chart V) :
    eval V (X.presheaf.map (homOfLE h).op f) ⟨y, hy⟩ = eval U f ⟨y, chart_mono h hy⟩ :=
  (evalHom_res h ⟨y, hy⟩ f).symm

/-- **Étale coordinates give charts.** Étale coordinates `z` on a Zariski open `U` give an étale
coordinate chart around any `x ∈ U(ℂ)` inside any given neighbourhood `O` of `x`, whose
coordinates are the values of `z`. -/
public theorem EtaleCoordinateChart.exists_of_etale
    [SmoothOfRelativeDimension n sX] (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    {x : ComplexPoints sX} (hx : x ∈ chart U) {O : Set (ComplexPoints sX)} (hO : IsOpen O)
    (hxO : x ∈ O) :
    ∃ c : EtaleCoordinateChart sX n, x ∈ c.W ∧ c.W ⊆ O ∧ c.W ⊆ chart U ∧
      ∀ (y : ComplexPoints sX) (_ : y ∈ c.W) (hy' : y ∈ chart U) (j : Fin n),
        c.toOpenPartialHomeomorph y j = eval U (z j) ⟨y, hy'⟩ := by
  obtain ⟨W, hW, hWo, hxW, hemb⟩ := (etaleCoordinate_atlas_of_smooth sX).2.1 U z hz x hx
  let c₀ : EtaleCoordinateChart sX n := ⟨U, z, hz, W, hW, hWo, ⟨x, hxW⟩, hemb⟩
  exact ⟨c₀.restrict O hO ⟨x, hxW, hxO⟩, ⟨hxW, hxO⟩, fun _ h ↦ h.2, fun _ h ↦ hW h.1,
    fun y hy _ j ↦ (c₀.restrict O hO _).toOpenPartialHomeomorph_apply hy j⟩

variable [SmoothOfRelativeDimension 1 sB]

/-- The preferred chart of a smooth complex curve at `b` is the value of the coordinate of
`MMP.Analytic.ComplexPoints.curveChart`. -/
public lemma chartAt_complex_apply (b : ComplexPoints sB) {y : ComplexPoints sB}
    (hy : y ∈ (curveChart b).W) :
    chartAt ℂ b y = eval (curveChart b).U ((curveChart b).z 0) ⟨y, (curveChart b).subset hy⟩ :=
  (curveChart b).toOpenPartialHomeomorph_apply hy 0

/-- **Charts adapted to a morphism to a curve.** Let `g : X ⟶ B` be a morphism to a smooth
complex curve and `z` étale coordinates on `U ∋ x` whose `j₀`-th coordinate is the pull-back of
the coordinate `w` of the preferred chart of `B` at `g(x)`. Then inside any neighbourhood `O` of
`x` there is an étale coordinate chart around `x` with coordinates `z` in which `g^an` reads
`y ↦ y_{j₀}` in the preferred chart of `B`: the hypothesis of
`MMP.Analytic.ComplexPoints.hasMFDerivAt_realize_of_adapted`. -/
public theorem EtaleCoordinateChart.exists_adapted
    [SmoothOfRelativeDimension n sX] (g : X ⟶ B) (hg : g ≫ sB = sX) (x : ComplexPoints sX)
    (U : X.Opens) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (hx : x ∈ chart U) (j₀ : Fin n) (hU : U ≤ g ⁻¹ᵁ (curveChart (realize g hg x)).U)
    (hzj₀ : z j₀ = X.presheaf.map (homOfLE hU).op
      (g.app _ ((curveChart (realize g hg x)).z 0)))
    {O : Set (ComplexPoints sX)} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ c : EtaleCoordinateChart sX n, x ∈ c.W ∧ c.W ⊆ O ∧ c.W ⊆ chart U ∧
      (∀ (y : ComplexPoints sX) (_ : y ∈ c.W) (hy' : y ∈ chart U) (j : Fin n),
        c.toOpenPartialHomeomorph y j = eval U (z j) ⟨y, hy'⟩) ∧
      ∀ y ∈ c.W, realize g hg y ∈ (chartAt ℂ (realize g hg x)).source ∧
        chartAt ℂ (realize g hg x) (realize g hg y) = c.toOpenPartialHomeomorph y j₀ := by
  set cB := curveChart (realize g hg x)
  have hO' : IsOpen (O ∩ realize g hg ⁻¹' cB.W) :=
    hO.inter (cB.isOpen.preimage (continuous_realize g hg))
  obtain ⟨c, hxc, hcO, hcU, hcz⟩ := EtaleCoordinateChart.exists_of_etale U z hz hx hO'
    ⟨hxO, mem_curveChart_W _⟩
  refine ⟨c, hxc, fun y hy ↦ (hcO hy).1, hcU, hcz, fun y hy ↦ ?_⟩
  have hyB : realize g hg y ∈ cB.W := (hcO hy).2
  refine ⟨by rw [source_chartAt_complex]; exact hyB, ?_⟩
  rw [chartAt_complex_apply _ hyB, hcz y hy (hcU hy) j₀]
  have hy' : y ∈ chart (g ⁻¹ᵁ cB.U) := chart_mono hU (hcU hy)
  simp only [hzj₀]
  rw [eval_res hU _ y (hcU hy), eval_app_realize g hg cB.U _ y hy']

end AdaptedCharts

section RelativeSNC

variable {X B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)} {n : ℕ}
  [SmoothOfRelativeDimension n sX] [SmoothOfRelativeDimension 1 sB]

/-- **Manifold data of a relative simple normal crossing family.** Let `g : X ⟶ B` be a
morphism from a smooth complex variety of dimension `n` to a smooth complex curve and
`D : ι → Set X^an` a family of subsets. Suppose that around every `x ∈ X^an` there are étale
coordinates `z` on a Zariski open `U ∋ x` such that `z_{j₀}` is the pull-back of the coordinate
of the preferred chart of `B` at `g(x)`, and, for a finite set `s` of indices and an injection
`c : s ↪ Fin n` avoiding `j₀`, `D i` misses `U(ℂ)` for `i ∉ s` and is the zero locus of
`z_{c i}` on `U(ℂ)` for `i ∈ s`. Then for a choice of preferred charts of `X^an`:

* `g^an` is holomorphic;
* the `D i` have simultaneous coordinate charts in the maximal atlas;
* `g^an` is a submersion;
* at every `x`, `dg^an_x` is nonzero on the tangent cone of the stratum `⋂_{x ∈ D i} D i`.

These are the hypotheses on `g` and `D` of
`MMP.Analytic.exists_homeomorph_prod_of_relativeSNC`. -/
public theorem exists_pick_relativeSNC (g : X ⟶ B) (hg : g ≫ sB = sX) {ι : Type*}
    (D : ι → Set (ComplexPoints sX))
    (had : ∀ x : ComplexPoints sX, ∃ (U : X.Opens) (z : Fin n → Γ(X, U))
      (_ : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (_ : x ∈ chart U) (j₀ : Fin n) (hU : U ≤ g ⁻¹ᵁ (curveChart (realize g hg x)).U)
      (_ : z j₀ = X.presheaf.map (homOfLE hU).op
        (g.app _ ((curveChart (realize g hg x)).z 0)))
      (s : Finset ι) (c : s ↪ Fin n), (∀ i, c i ≠ j₀) ∧ (∀ i ∉ s, D i ∩ chart U = ∅) ∧
        ∀ (i : s) (y : ComplexPoints sX) (hy : y ∈ chart U),
          y ∈ D i ↔ eval U (z (c i)) ⟨y, hy⟩ = 0) :
    ∃ pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W},
      letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
      (∀ N : WithTop ℕ∞, ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) N (realize g hg)) ∧
      (∀ (N : WithTop ℕ∞) (x : ComplexPoints sX),
        ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) N (ComplexPoints sX),
          x ∈ φ.source ∧ ∃ (s : Finset ι) (c : s ↪ Fin n),
            (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
            ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0}) ∧
      (∀ x : ComplexPoints sX,
        Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (realize g hg) x)) ∧
      ∀ x : ComplexPoints sX, ∃ v ∈ tangentConeAt ℂ
          ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).target ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).symm ⁻¹' ⋂ (i) (_ : x ∈ D i), D i)
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x),
        mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (realize g hg) x v ≠ 0 := by
  have key : ∀ x : ComplexPoints sX, ∃ (c : EtaleCoordinateChart sX n) (j₀ : Fin n)
      (s : Finset ι) (cc : s ↪ Fin n), x ∈ c.W ∧ (∀ i, cc i ≠ j₀) ∧
      (∀ i ∉ s, D i ∩ c.W = ∅) ∧
      (∀ (i : s) (y : ComplexPoints sX) (_ : y ∈ c.W),
        y ∈ D i ↔ c.toOpenPartialHomeomorph y (cc i) = 0) ∧
      ∀ y ∈ c.W, realize g hg y ∈ (chartAt ℂ (realize g hg x)).source ∧
        chartAt ℂ (realize g hg x) (realize g hg y) = c.toOpenPartialHomeomorph y j₀ := by
    intro x
    obtain ⟨U, z, hz, hx, j₀, hU, hzj, s, cc, hne, hout, hin⟩ := had x
    obtain ⟨c, hxc, -, hcU, hcz, hadapt⟩ :=
      EtaleCoordinateChart.exists_adapted g hg x U z hz hx j₀ hU hzj isOpen_univ trivial
    refine ⟨c, j₀, s, cc, hxc, hne, fun i hi ↦ ?_, fun i y hy ↦ ?_, hadapt⟩
    · refine Set.eq_empty_of_forall_notMem fun y hy ↦ ?_
      have : y ∈ D i ∩ chart U := ⟨hy.1, hcU hy.2⟩
      rw [hout i hi] at this
      exact this
    · rw [hcz y hy (hcU hy)]
      exact hin i y (hcU hy)
  choose C j₀ s cc hC using key
  let pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W} :=
    fun x ↦ ⟨C x, (hC x).1⟩
  refine ⟨pick, fun N ↦ contMDiff_realize_etaleChartedSpaceOf _ _ pick _ N g hg,
    fun N x ↦ ?_, fun x ↦ surjective_mfderiv_realize_of_adapted pick g hg x (j₀ x)
      (hC x).2.2.2.2, fun x ↦ ?_⟩
  · refine exists_mem_maximalAtlas_image_eq_hyperplane pick N D x (C x) (hC x).1 (s x) (cc x)
      (hC x).2.2.1 fun i y hy ↦ ?_
    rw [(hC x).2.2.2.1 i y hy, (C x).toOpenPartialHomeomorph_apply hy]
  · refine exists_mem_tangentConeAt_mfderiv_realize_ne_zero pick g hg x (j₀ x) (hC x).2.2.2.2 _
      (Set.range fun i ↦ cc x i) (by rintro ⟨i, hi⟩; exact (hC x).2.1 i hi) ?_
    letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
    intro v hv hJ
    set e := chartAt (EuclideanSpace ℂ (Fin n)) x
    have he : e = (C x).toChart (EuclideanSpace.equiv (Fin n) ℂ).symm := rfl
    have hW : e.symm v ∈ (C x).W := by
      have := e.map_target hv
      rwa [he, (C x).source_toChart] at this
    have hval : ∀ j, (C x).toOpenPartialHomeomorph (e.symm v) j = v j := fun j ↦
      congrArg (fun w : EuclideanSpace ℂ (Fin n) ↦ w j) (e.right_inv hv)
    have hx : ∀ j, (C x).toOpenPartialHomeomorph x j = e x j := fun _ ↦ rfl
    simp only [Set.mem_iInter]
    intro i hxi
    have his : i ∈ s x := by
      by_contra h
      have : x ∈ D i ∩ (C x).W := ⟨hxi, (hC x).1⟩
      rw [(hC x).2.2.1 i h] at this
      exact this
    rw [(hC x).2.2.2.1 ⟨i, his⟩ _ hW, hval, hJ _ ⟨⟨i, his⟩, rfl⟩, ← hx]
    exact ((hC x).2.2.2.1 ⟨i, his⟩ x (hC x).1).1 hxi

/-- **Étale coordinates adapted to a smooth morphism to a curve.** Let `g : X ⟶ B` be a
morphism from a smooth complex variety of dimension `n` to a smooth complex curve, smooth at the
point under `x ∈ X^an`, and `O ∋ x` a Zariski open. Then there are étale coordinates `z` on a
Zariski open `U ⊆ O` with `x ∈ U(ℂ)`, one of which, `z_{j₀}`, is the pull-back `g^* w` of the
coordinate `w` of the preferred chart of `B` at `g(x)`. -/
public theorem exists_etale_coordinates_adapted (g : X ⟶ B) (hg : g ≫ sB = sX)
    (x : ComplexPoints sX) (hgx : (g.stalkMap (toScheme x)).hom.FormallySmooth) (O : X.Opens)
    (hxO : toScheme x ∈ O) :
    ∃ (U : X.Opens) (z : Fin n → Γ(X, U))
      (_ : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (_ : x ∈ chart U) (_ : U ≤ O) (j₀ : Fin n)
      (hU : U ≤ g ⁻¹ᵁ (curveChart (realize g hg x)).U),
      z j₀ = X.presheaf.map (homOfLE hU).op (g.app _ ((curveChart (realize g hg x)).z 0)) := by
  have : Smooth sB := SmoothOfRelativeDimension.smooth 1 sB
  set cB := curveChart (realize g hg x)
  have hb : toScheme (realize g hg x) ∈ cB.U := mem_chart_iff.1 (cB.subset (mem_curveChart_W _))
  have hgp : g (toScheme x) ∈ cB.U := hb
  have hX := tmul_D_germ_app_ne_zero g hg (toScheme x) hgx cB.U hgp (cB.z 0)
    (tmul_D_germ_curveChart_ne_zero (realize g hg x) hb)
  have hpV : toScheme x ∈ g ⁻¹ᵁ cB.U ⊓ O := ⟨hgp, hxO⟩
  obtain ⟨U, hpU, hUV, z, j₀, hz, hzj⟩ := exists_etale_coordinates_eq_of_tmul_D_ne_zero (n := n)
    (toScheme x) (g ⁻¹ᵁ cB.U ⊓ O) hpV
    (X.presheaf.map (homOfLE inf_le_left).op (g.app cB.U (cB.z 0)))
    (by rw [X.presheaf.germ_res_apply]; exact hX)
  refine ⟨U, z, hz, mem_chart_iff.2 hpU, hUV.trans inf_le_right, j₀, hUV.trans inf_le_left, ?_⟩
  rw [hzj, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **Smooth morphisms to a curve are submersions.** For a morphism `g : X ⟶ B` from a smooth
complex variety of dimension `n` to a smooth complex curve, smooth at every point, there is a
choice of preferred étale charts of `X^an` in which `g^an` is holomorphic with surjective
differential everywhere. -/
public theorem exists_pick_surjective_mfderiv_realize (g : X ⟶ B) (hg : g ≫ sB = sX)
    [Smooth g] :
    ∃ pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W},
      letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
      (∀ N : WithTop ℕ∞, ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) N (realize g hg)) ∧
      ∀ x : ComplexPoints sX,
        Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (realize g hg) x) := by
  obtain ⟨pick, h1, -, h3, -⟩ := exists_pick_relativeSNC g hg (fun i : Empty ↦ i.elim) fun x ↦ by
    have hgx : (g.stalkMap (toScheme x)).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.1 (by rw [g.smoothLocus_eq_top]; trivial)
    obtain ⟨U, z, hz, hx, -, j₀, hU, hzj⟩ :=
      exists_etale_coordinates_adapted (n := n) g hg x hgx ⊤ trivial
    exact ⟨U, z, hz, hx, j₀, hU, hzj, ∅, ⟨fun i ↦ i.1.elim, fun i ↦ i.1.elim⟩,
      fun i ↦ i.1.elim, fun i ↦ i.elim, fun i ↦ i.1.elim⟩
  exact ⟨pick, h1, h3⟩

end RelativeSNC

section RelativeSNCDivisor

open IsLocalRing TensorProduct KaehlerDifferential

/-- The point of `X` under a `ℂ`-point is closed: a section of `X → Spec ℂ` is a closed
immersion. -/
private theorem isClosed_singleton_toScheme {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (x : ComplexPoints sX) : IsClosed ({x.toScheme} : Set X) := by
  have : IsClosedImmersion x.hom := isClosedImmersion_of_comp_eq_id sX x.hom x.2
  convert x.hom.isClosedEmbedding.isClosed_range using 1
  ext y
  constructor
  · rintro rfl; exact ⟨default, rfl⟩
  · rintro ⟨q, rfl⟩; rw [Subsingleton.elim q default]; rfl

/-- Over a base change `R → R₀` with bijective structure map, differentials forming a basis of
`κ(B) ⊗ Ω[B⁄R]` also form a basis of `κ(B) ⊗ Ω[B⁄R₀]`. -/
private theorem isBasis_D_of_bijective_algebraMap {R R₀ B : Type*} [CommRing R] [CommRing R₀]
    [CommRing B] [IsLocalRing B] [Algebra R R₀] [Algebra R₀ B] [Algebra R B]
    [IsScalarTower R R₀ B] (hR : Function.Bijective (algebraMap R R₀)) {ι : Type*} (b : ι → B)
    (hli : LinearIndependent (ResidueField B)
      (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (b i)))
    (hsp : Submodule.span (ResidueField B)
      (Set.range (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (b i))) = ⊤) :
    LinearIndependent (ResidueField B)
      (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R₀ B (b i)) ∧
    Submodule.span (ResidueField B)
      (Set.range (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R₀ B (b i))) = ⊤ := by
  have : Algebra.FormallyEtale R R₀ :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R R₀) hR)
  have : Subsingleton Ω[R₀⁄R] := (Algebra.formallyUnramified_iff R R₀).mp inferInstance
  have hbij : Function.Bijective (KaehlerDifferential.map R R₀ B B) := by
    refine ⟨?_, KaehlerDifferential.map_surjective R R₀ B⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (KaehlerDifferential.exact_mapBaseChange_map R R₀ B x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]
  let e : Ω[B⁄R] ≃ₗ[B] Ω[B⁄R₀] := LinearEquiv.ofBijective (KaehlerDifferential.map R R₀ B B) hbij
  let e' := e.baseChange B (ResidueField B)
  have hcomp : (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R₀ B (b i)) =
      e' ∘ (fun i ↦ (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D R B (b i)) := by
    funext i
    change _ = (1 : ResidueField B) ⊗ₜ[B]
      KaehlerDifferential.map R R₀ B B (KaehlerDifferential.D R B (b i))
    rw [KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply]
  rw [hcomp]
  refine ⟨hli.map' e'.toLinearMap (LinearEquiv.ker e'), ?_⟩
  rw [Set.range_comp, ← LinearEquiv.coe_coe, ← Submodule.map_span, hsp, Submodule.map_top,
    LinearEquiv.range]

/-- At a closed point of a smooth complex scheme, the differentials of a regular system of
parameters form a basis of the fibre `κ(p) ⊗ Ω_{𝒪_{X,p}/ℂ}`. -/
private theorem isBasis_D_stalk_of_isRegularSystemOfParameters {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [Smooth sX] (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ}
    (t : Fin n → X.presheaf.stalk p) (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    let := MMP.Mori.stalkAlgebra sX p
    LinearIndependent (ResidueField (X.presheaf.stalk p))
      (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ℂ (X.presheaf.stalk p) (t i)) ∧
    Submodule.span (ResidueField (X.presheaf.stalk p))
      (Set.range (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ℂ (X.presheaf.stalk p) (t i))) = ⊤ := by
  classical
  let := MMP.Mori.stalkAlgebra sX p
  obtain ⟨h1, h2, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts sX p
  have := h1
  have := h2
  have := h3
  have : Module.Finite ℂ (ResidueField (X.presheaf.stalk p)) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX p hp
  have : Algebra.FormallyUnramified ℂ (ResidueField (X.presheaf.stalk p)) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  obtain ⟨ht0, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular t ht.1 ht.2
  exact ⟨MMP.Flips.ResolutionInputs.linearIndependent_tmul_D ℂ t ht0 hli,
    top_le_iff.mp (MMP.Flips.ResolutionInputs.span_tmul_D ℂ t ht.1)⟩

/-- The structure map from `ℂ` to the stalk of `Spec ℂ` at its point is bijective. -/
private theorem bijective_germ_comp_ΓSpecIso_inv (q : Spec (.of ℂ)) :
    Function.Bijective ((Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec (.of ℂ)).presheaf.germ ⊤ q trivial).hom := by
  refine ⟨RingHom.injective _, ?_⟩
  have hloc := (isAffineOpen_top (Spec (.of ℂ))).isLocalization_stalk ⟨q, trivial⟩
  have hu : ∀ y : ((isAffineOpen_top (Spec (.of ℂ))).primeIdealOf ⟨q, trivial⟩).asIdeal.primeCompl,
      IsUnit (y : Γ(Spec (.of ℂ), ⊤)) := by
    intro y
    have hy0 : (y : Γ(Spec (.of ℂ), ⊤)) ≠ 0 := fun h0 ↦ y.2 (h0 ▸ Ideal.zero_mem _)
    have : (Scheme.ΓSpecIso (.of ℂ)).hom (y : Γ(Spec (.of ℂ), ⊤)) ≠ 0 := by
      intro h; apply hy0
      rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of ℂ)) (y : Γ(Spec (.of ℂ), ⊤)), h, map_zero]
    have hU := (IsUnit.mk0 _ this).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom
    rwa [Iso.hom_inv_id_apply] at hU
  let := TopCat.Presheaf.algebra_section_stalk (Spec (.of ℂ)).presheaf (U := ⊤) ⟨q, trivial⟩
  have hs := (IsLocalization.atUnits Γ(Spec (.of ℂ), ⊤) _ (S := (Spec (.of ℂ)).presheaf.stalk q)
    (fun y hy ↦ hu ⟨y, hy⟩)).surjective
  intro r
  obtain ⟨a, ha⟩ := hs r
  refine ⟨(Scheme.ΓSpecIso (.of ℂ)).hom a, ?_⟩
  rw [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply]
  exact ha

/-- At a closed point `p` of a smooth complex scheme, the differentials of a regular system of
parameters form a basis of `κ(p) ⊗ Ω[𝒪_{X,p} ⁄ 𝒪_{Spec ℂ, sX p}]`. -/
private theorem isBasis_D_stalk_base_of_isRegularSystemOfParameters {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [Smooth sX] (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ}
    (t : Fin n → X.presheaf.stalk p) (ht : MMP.Mori.IsRegularSystemOfParameters t) :
    let := (sX.stalkMap p).hom.toAlgebra
    LinearIndependent (ResidueField (X.presheaf.stalk p))
      (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (t i)) ∧
    Submodule.span (ResidueField (X.presheaf.stalk p))
      (Set.range (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        KaehlerDifferential.D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (t i))) = ⊤ := by
  let := MMP.Mori.stalkAlgebra sX p
  let := (sX.stalkMap p).hom.toAlgebra
  let : Algebra ℂ ((Spec (.of ℂ)).presheaf.stalk (sX p)) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec (.of ℂ)).presheaf.germ ⊤ (sX p) trivial).hom.toAlgebra
  have : IsScalarTower ℂ ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom =
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec (.of ℂ)).presheaf.germ ⊤ (sX p)
        (TopologicalSpace.Opens.mem_top _) ≫ sX.stalkMap p).hom
    rw [Scheme.Hom.germ_stalkMap]
    rfl
  obtain ⟨hli, hsp⟩ := isBasis_D_stalk_of_isRegularSystemOfParameters sX p hp t ht
  exact isBasis_D_of_bijective_algebraMap (bijective_germ_comp_ΓSpecIso_inv (sX p)) t hli hsp

/-- If an ideal `I` of `A` is finitely generated and its image in a localization `S` of `A` lies
in that of `J`, then some `s` in the localizing submonoid has `s I ⊆ J`. -/
private theorem exists_mul_mem_of_map_le {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (I J : Ideal A) (hI : I.FG)
    (h : I.map (algebraMap A S) ≤ J.map (algebraMap A S)) :
    ∃ s ∈ M, ∀ a ∈ I, s * a ∈ J := by
  classical
  obtain ⟨t, rfl⟩ := hI
  have hc : ∀ a ∈ (t : Set A), ∃ c : M, (c : A) * a ∈ J := by
    intro a ha
    have h1 : algebraMap A S a ∈ J.map (algebraMap A S) :=
      h (Ideal.mem_map_of_mem _ (Ideal.subset_span ha))
    obtain ⟨⟨⟨j, hj⟩, m⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp h1
    simp only at hx
    rw [← map_mul, IsLocalization.eq_iff_exists M S] at hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨c * m, ?_⟩
    have : (↑(c * m) : A) * a = ↑c * j := by
      rw [Submonoid.coe_mul]
      calc (c : A) * m * a = c * (a * m) := by ring
        _ = c * j := hc
    rw [this]; exact J.mul_mem_left _ hj
  choose! c hc using hc
  refine ⟨∏ a ∈ t, (c a : A), Submonoid.prod_mem _ fun a _ ↦ (c a).2, fun a ha ↦ ?_⟩
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun a ↦ (c a : A)) (show x ∈ t from hx)
    rw [hu, mul_comm (c x : A) u, mul_assoc]
    exact J.mul_mem_left _ (hc x hx)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact J.mul_mem_left _ hx

/-- **A principal stalk cuts out the support near the point.** Let `Z` be an ideal sheaf on a
locally Noetherian scheme whose stalk at `p` is principal, generated by `t`. Then near `p`, on an
open `V`, `t` is the germ of a section `τ` whose zero locus is the support of `Z`. -/
public theorem exists_mem_support_iff_notMem_basicOpen {X : Scheme.{0}} [IsLocallyNoetherian X]
    (Z : X.IdealSheafData) (p : X) (t : X.presheaf.stalk p)
    (ht : IdealSheafData.stalk Z p = Ideal.span {t}) :
    ∃ (V : X.Opens) (hpV : p ∈ V) (τ : Γ(X, V)), X.presheaf.germ V p hpV τ = t ∧
      ∀ q ∈ V, q ∈ Z.support ↔ q ∉ X.basicOpen τ := by
  obtain ⟨V, hV, hpV, a, ha⟩ :=
    MMP.Flips.ResolutionInputs.exists_affineOpen_germ_eq p (fun _ : Unit ↦ t)
  let _ : Algebra Γ(X, V) (X.presheaf.stalk p) := X.presheaf.algebra_section_stalk ⟨p, hpV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk p) (hV.primeIdealOf ⟨p, hpV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨p, hpV⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  set τ := a ()
  set I : Ideal Γ(X, V) := Z.ideal ⟨V, hV⟩
  set J : Ideal Γ(X, V) := Ideal.span {τ}
  have hmap : I.map (algebraMap Γ(X, V) (X.presheaf.stalk p)) =
      J.map (algebraMap Γ(X, V) (X.presheaf.stalk p)) := by
    have e1 := IdealSheafData.stalk_eq_map_germ Z p ⟨V, hV⟩ hpV
    rw [ht] at e1
    rw [Ideal.map_span, Set.image_singleton]
    change _ = Ideal.span {(X.presheaf.germ V p hpV).hom τ}
    rw [ha ()]
    exact e1.symm
  obtain ⟨s1, hs1, h1⟩ := exists_mul_mem_of_map_le (S := X.presheaf.stalk p)
    (hV.primeIdealOf ⟨p, hpV⟩).asIdeal.primeCompl I J (IsNoetherian.noetherian I) hmap.le
  obtain ⟨s2, hs2, h2⟩ := exists_mul_mem_of_map_le (S := X.presheaf.stalk p)
    (hV.primeIdealOf ⟨p, hpV⟩).asIdeal.primeCompl J I (IsNoetherian.noetherian J) hmap.ge
  have hp : ∀ s ∈ (hV.primeIdealOf ⟨p, hpV⟩).asIdeal.primeCompl, p ∈ X.basicOpen s := by
    intro s hs
    rw [X.mem_basicOpen s p hpV]
    exact IsLocalization.map_units (X.presheaf.stalk p)
      (⟨s, hs⟩ : (hV.primeIdealOf ⟨p, hpV⟩).asIdeal.primeCompl)
  have hWV : X.basicOpen s1 ⊓ X.basicOpen s2 ≤ V := inf_le_left.trans (X.basicOpen_le s1)
  have hpW : p ∈ X.basicOpen s1 ⊓ X.basicOpen s2 := ⟨hp s1 hs1, hp s2 hs2⟩
  refine ⟨X.basicOpen s1 ⊓ X.basicOpen s2, hpW,
    X.presheaf.map (homOfLE hWV).op τ, ?_, fun q hq ↦ ?_⟩
  · rw [X.presheaf.germ_res_apply]
    exact ha ()
  rw [Scheme.basicOpen_res, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) (hWV hq),
    Scheme.mem_zeroLocus_iff]
  constructor
  · intro h hq'
    refine h _ (h2 τ (Ideal.mem_span_singleton_self τ)) ?_
    rw [Scheme.basicOpen_mul]
    exact ⟨hq.2, hq'.2⟩
  · intro h f hf hqf
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h1 f hf)
    have : q ∈ X.basicOpen (s1 * f) := by rw [Scheme.basicOpen_mul]; exact ⟨hq.1, hqf⟩
    rw [← hc, Scheme.basicOpen_mul] at this
    exact h ⟨hq, this.2⟩

/-- In a local ring `A`, `1 ⊗ x` vanishes in `κ(A) ⊗ M` exactly when `x ∈ 𝔪 M`. -/
private theorem one_tmul_eq_zero_iff {A M : Type*} [CommRing A] [IsLocalRing A] [AddCommGroup M]
    [Module A M] (x : M) :
    (1 : ResidueField A) ⊗ₜ[A] x = 0 ↔ x ∈ maximalIdeal A • (⊤ : Submodule A M) := by
  rw [← Submodule.Quotient.mk_eq_zero, ← quotTensorEquivQuotSMul_mk_one_tmul (maximalIdeal A) x,
    LinearEquiv.map_eq_zero_iff]
  rfl

/-- The maps on stalks of a smooth morphism are formally smooth. -/
private theorem formallySmooth_stalkMap_of_smooth {Y Y' : Scheme.{0}} (φ : Y ⟶ Y') (hφ : Smooth φ)
    (y : Y) : (φ.stalkMap y).hom.FormallySmooth :=
  Scheme.Hom.mem_smoothLocus.1 (by rw [φ.smoothLocus_eq_top]; trivial)

variable {X B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)} {n : ℕ}

/-- **Differentials along a smooth stratum.** Let `g : X ⟶ B` be a morphism over `ℂ` with `B`
smooth, `Z ⊆ X` a closed subscheme smooth over `B` and `p ∈ Z`. If a section `w` of `𝒪_B` near
`g(p)` has nonzero differential at `g(p)`, then `d(g^* w)` is not in the span of the differentials
at `p` of elements of the ideal of `Z`. -/
public theorem tmul_D_germ_app_notMem_span [Smooth sB] (g : X ⟶ B) (hg : g ≫ sB = sX)
    (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ g)) (p : X) (hp : p ∈ Z.support)
    (V : B.Opens) (hpV : g p ∈ V) (w : Γ(B, V))
    (hw : letI := (sB.stalkMap (g p)).hom.toAlgebra
      (1 : ResidueField (B.presheaf.stalk (g p))) ⊗ₜ[B.presheaf.stalk (g p)]
        D ((Spec (.of ℂ)).presheaf.stalk (sB (g p))) (B.presheaf.stalk (g p))
          (B.presheaf.germ V (g p) hpV w) ≠ 0)
    {k : ℕ} (t : Fin k → X.presheaf.stalk p) (ht : ∀ i, t i ∈ IdealSheafData.stalk Z p) :
    letI := (sX.stalkMap p).hom.toAlgebra
    (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (X.presheaf.germ (g ⁻¹ᵁ V) p hpV (g.app V w)) ∉
      Submodule.span (ResidueField (X.presheaf.stalk p)) (Set.range fun i ↦
        (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
          D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p) (t i)) := by
  classical
  subst hg
  obtain ⟨d, rfl⟩ : p ∈ Set.range Z.subschemeι := by rw [Z.range_subschemeι]; exact hp
  letI : Algebra ((Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
      (B.presheaf.stalk (g (Z.subschemeι d))) :=
    (sB.stalkMap (g (Z.subschemeι d))).hom.toAlgebra
  letI : Algebra ((Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
      (X.presheaf.stalk (Z.subschemeι d)) :=
    ((g ≫ sB).stalkMap (Z.subschemeι d)).hom.toAlgebra
  letI : Algebra (X.presheaf.stalk (Z.subschemeι d)) (Z.subscheme.presheaf.stalk d) :=
    (Z.subschemeι.stalkMap d).hom.toAlgebra
  letI : Algebra (B.presheaf.stalk (g (Z.subschemeι d))) (Z.subscheme.presheaf.stalk d) :=
    ((Z.subschemeι ≫ g).stalkMap d).hom.toAlgebra
  letI : Algebra ((Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
      (Z.subscheme.presheaf.stalk d) :=
    ((Z.subschemeι ≫ g ≫ sB).stalkMap d).hom.toAlgebra
  have : IsScalarTower ((Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
      (X.presheaf.stalk (Z.subschemeι d))
      (Z.subscheme.presheaf.stalk d) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Z.subschemeι ≫ g ≫ sB).stalkMap d).hom = _
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have : IsScalarTower ((Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
      (B.presheaf.stalk (g (Z.subschemeι d)))
      (Z.subscheme.presheaf.stalk d) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change (((Z.subschemeι ≫ g) ≫ sB).stalkMap d).hom = _
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hfs : ((Z.subschemeι ≫ g).stalkMap d).hom.FormallySmooth :=
    formallySmooth_stalkMap_of_smooth (Z.subschemeι ≫ g) hZ d
  have : Algebra.FormallySmooth (B.presheaf.stalk (g (Z.subschemeι d)))
      (Z.subscheme.presheaf.stalk d) := hfs
  obtain ⟨hfree, -⟩ :=
    MMP.Flips.ResolutionInputs.free_finite_kaehlerDifferential_stalk sB (g (Z.subschemeι d))
  have hT :=
    tmul_D_algebraMap_ne_zero (R := (Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
    (T := Z.subscheme.presheaf.stalk d) (B.presheaf.germ V (g (Z.subschemeι d)) hpV w) hw
  have hgw : algebraMap (B.presheaf.stalk (g (Z.subschemeι d))) (Z.subscheme.presheaf.stalk d)
      (B.presheaf.germ V (g (Z.subschemeι d)) hpV w) =
        algebraMap (X.presheaf.stalk (Z.subschemeι d)) (Z.subscheme.presheaf.stalk d)
          (X.presheaf.germ (g ⁻¹ᵁ V) (Z.subschemeι d) hpV (g.app V w)) := by
    change ((Z.subschemeι ≫ g).stalkMap d).hom _ = (Z.subschemeι.stalkMap d).hom _
    rw [Scheme.Hom.stalkMap_comp]
    change (Z.subschemeι.stalkMap d).hom ((g.stalkMap (Z.subschemeι d)).hom _) = _
    rw [Scheme.Hom.germ_stalkMap_apply]
  have hker : ∀ i,
      algebraMap (X.presheaf.stalk (Z.subschemeι d)) (Z.subscheme.presheaf.stalk d) (t i) = 0 := by
    intro i
    have h2 := IdealSheafData.stalk_ker_of_isClosedImmersion Z.subschemeι d
    rw [Z.ker_subschemeι] at h2
    have := ht i
    rw [h2] at this
    exact RingHom.mem_ker.1 this
  intro hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  choose a ha using fun i ↦ IsLocalRing.residue_surjective (c i)
  set x := D ((Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
        (X.presheaf.stalk (Z.subschemeι d))
        (X.presheaf.germ (g ⁻¹ᵁ V) (Z.subschemeι d) hpV (g.app V w)) -
    ∑ i, a i • D ((Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
      (X.presheaf.stalk (Z.subschemeι d)) (t i)
  have hx :
      (1 : ResidueField (X.presheaf.stalk (Z.subschemeι d))) ⊗ₜ[X.presheaf.stalk (Z.subschemeι d)]
        x = 0 := by
    rw [tmul_sub, tmul_sum, sub_eq_zero]
    refine hc.symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [tmul_smul, ← ha i, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
    rfl
  rw [one_tmul_eq_zero_iff] at hx
  have hμ : ∀ y ∈ maximalIdeal (X.presheaf.stalk (Z.subschemeι d)) •
      (⊤ : Submodule (X.presheaf.stalk (Z.subschemeι d))
        Ω[X.presheaf.stalk (Z.subschemeι d) ⁄
          (Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d)))]),
      map ((Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
        ((Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d))))
        (X.presheaf.stalk (Z.subschemeι d))
        (Z.subscheme.presheaf.stalk d) y ∈ maximalIdeal (Z.subscheme.presheaf.stalk d) •
          (⊤ : Submodule (Z.subscheme.presheaf.stalk d)
            Ω[Z.subscheme.presheaf.stalk d ⁄
              (Spec (.of ℂ)).presheaf.stalk (sB (g (Z.subschemeι d)))]) := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun r hr y _ ↦ ?_) (fun y y' hy hy' ↦ ?_)
    · have hr' : algebraMap (X.presheaf.stalk (Z.subschemeι d)) (Z.subscheme.presheaf.stalk d) r ∈
          maximalIdeal (Z.subscheme.presheaf.stalk d) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
        exact fun hu ↦ hr (isUnit_of_map_unit (Z.subschemeι.stalkMap d).hom _ hu)
      rw [LinearMap.map_smul, ← algebraMap_smul (Z.subscheme.presheaf.stalk d) r
        (map _ _ (X.presheaf.stalk (Z.subschemeι d)) (Z.subscheme.presheaf.stalk d) y)]
      exact Submodule.smul_mem_smul hr' Submodule.mem_top
    · rw [map_add]; exact add_mem hy hy'
  have h1 := hμ x hx
  simp only [x, map_sub, map_sum, LinearMap.map_smul, map_D, hker, map_zero, smul_zero,
    Finset.sum_const_zero, sub_zero] at h1
  apply hT
  rwa [hgw, one_tmul_eq_zero_iff]

variable [SmoothOfRelativeDimension 1 sB]

/-- **Étale coordinates adapted to a relative simple normal crossing divisor.** Let `g : X ⟶ B`
be a morphism from a scheme smooth over `ℂ` to a smooth complex curve, `V_d ⊆ X` an open smooth of
relative dimension `n` over `ℂ`, and `E = ∑_{E_i ∈ s} E_i` a simple normal crossing divisor on `X`
every intersection `⋂_{i ∈ J} E_i` of whose components (including `X` itself, for `J = ∅`) is
smooth over `B`. Then
around every `x ∈ V_d(ℂ)` there are étale coordinates `z` on a Zariski open `x ∈ U ⊆ V_d` such that
`z_{j₀}` is the pull-back of the coordinate of the preferred chart of `B` at `g(x)`, the
components through `x` are the zero loci on `U(ℂ)` of other coordinates `z_{c i}`, and the
other components miss `U(ℂ)`. -/
public theorem exists_etale_coordinates_adapted_of_isSNC [Smooth sX] (Vd : X.Opens)
    [SmoothOfRelativeDimension n (Vd.ι ≫ sX)] (g : X ⟶ B) (hg : g ≫ sB = sX)
    (s : Finset (Mori.PrimeDivisor X))
    (hs : Mori.DivisorWithCoeffs.IsSNC sX (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ g)) (x : ComplexPoints sX)
    (hxd : toScheme x ∈ Vd) :
    ∃ (U : X.Opens) (z : Fin n → Γ(X, U))
      (_ : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
      (_ : x ∈ chart U) (_ : U ≤ Vd) (j₀ : Fin n) (hU : U ≤ g ⁻¹ᵁ (curveChart (realize g hg x)).U)
      (_ : z j₀ = X.presheaf.map (homOfLE hU).op
        (g.app _ ((curveChart (realize g hg x)).z 0)))
      (s' : Finset s) (c : s' ↪ Fin n), (∀ i, c i ≠ j₀) ∧
        (∀ i ∉ s', {y : ComplexPoints sX | toScheme y ∈ i.1.support} ∩ chart U = ∅) ∧
        ∀ (i : s') (y : ComplexPoints sX) (hy : y ∈ chart U),
          toScheme y ∈ i.1.1.support ↔ eval U (z (c i)) ⟨y, hy⟩ = 0 := by
  classical
  have : Smooth sB := SmoothOfRelativeDimension.smooth 1 sB
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set p := toScheme x with hp
  set cB := curveChart (realize g hg x)
  have hb : toScheme (realize g hg x) ∈ cB.U := mem_chart_iff.1 (cB.subset (mem_curveChart_W _))
  have hgp : g p ∈ cB.U := hb
  have hsupp : ∀ E, E ∈ (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support ↔ E ∈ s := by
    intro E
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    by_cases hE : E ∈ s
    · rw [Finset.sum_eq_single E (fun b _ hb ↦ by rw [Finsupp.single_apply, if_neg hb])
        (fun h ↦ (h hE).elim), Finsupp.single_eq_same]
      exact ⟨fun _ ↦ hE, fun _ ↦ one_ne_zero⟩
    · rw [Finset.sum_eq_zero fun b hb ↦ by
        rw [Finsupp.single_apply, if_neg (fun h : b = E ↦ hE (h ▸ hb))]]
      exact ⟨fun h ↦ (h rfl).elim, fun h ↦ (hE h).elim⟩
  obtain ⟨m, t, j, ht, hj, hI⟩ := hs.2 p
  -- the components through `p`
  let s' : Finset s := s.attach.filter fun E ↦ p ∈ E.1.support
  have hs' : ∀ E : s, E ∈ s' ↔ p ∈ E.1.support := fun E ↦ by simp [s']
  let k := s'.card
  obtain ⟨e⟩ : Nonempty (Fin k ≃ s') := ⟨s'.equivFin.symm⟩
  let jE : s' → Fin m := fun E ↦ j ⟨E.1.1, (hsupp _).2 E.1.2, (hs' _).1 E.2⟩
  have hjE : Function.Injective jE := by
    intro E E' h
    have := hj h
    simp only [Subtype.mk.injEq] at this
    exact Subtype.ext (Subtype.ext this)
  -- each component through `p` is cut out by a section near `p`
  have hI' : ∀ E : s', IdealSheafData.stalk E.1.1.idealSheaf p = Ideal.span {t (jE E)} :=
    fun E ↦ hI ⟨E.1.1, (hsupp _).2 E.1.2, (hs' _).1 E.2⟩
  choose V hpV τ hτ hτV using fun l : Fin k ↦
    exists_mem_support_iff_notMem_basicOpen (e l).1.1.idealSheaf p (t (jE (e l))) (hI' (e l))
  -- a common neighbourhood
  have hev : ∀ᶠ q in 𝓝 p, (∀ l, q ∈ V l) ∧ q ∈ g ⁻¹ᵁ cB.U ∧
      (∀ E ∈ s, p ∉ E.support → q ∉ E.support) ∧ q ∈ Vd := by
    refine (Filter.eventually_all.2 fun l ↦ (V l).isOpen.mem_nhds (hpV l)).and
      (Filter.Eventually.and (show ∀ᶠ q in 𝓝 p, q ∈ g ⁻¹ᵁ cB.U from
        (g ⁻¹ᵁ cB.U).isOpen.mem_nhds hgp) (Filter.Eventually.and ?_
          (show ∀ᶠ q in 𝓝 p, q ∈ Vd from Vd.isOpen.mem_nhds hxd)))
    refine (Filter.eventually_all_finset s).2 fun E _ ↦ ?_
    by_cases hE : p ∈ E.support
    · exact Filter.Eventually.of_forall fun q h ↦ (h hE).elim
    · filter_upwards [E.idealSheaf.support.isClosed.isOpen_compl.mem_nhds hE] with q hq _
      exact hq
  obtain ⟨O, hOsub, hOo, hpO⟩ := mem_nhds_iff.1 hev
  let V₀ : X.Opens := ⟨O, hOo⟩
  have hV₀l : ∀ l, V₀ ≤ V l := fun l q hq ↦ (hOsub hq).1 l
  have hV₀B : V₀ ≤ g ⁻¹ᵁ cB.U := fun q hq ↦ (hOsub hq).2.1
  have hpV₀ : p ∈ V₀ := hpO
  let a : Fin (k + 1) → Γ(X, V₀) :=
    Fin.cons (X.presheaf.map (homOfLE hV₀B).op (g.app cB.U (cB.z 0)))
      fun l ↦ X.presheaf.map (homOfLE (hV₀l l)).op (τ l)
  letI := (sX.stalkMap p).hom.toAlgebra
  have hgerm : (fun i ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
      D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
        (X.presheaf.germ V₀ p hpV₀ (a i))) =
      Fin.cons ((1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (X.presheaf.germ (g ⁻¹ᵁ cB.U) p hgp (g.app cB.U (cB.z 0))))
        fun l ↦ (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
          D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p) (t (jE (e l))) := by
    funext i
    refine Fin.cases ?_ (fun l ↦ ?_) i
    · simp only [a, Fin.cons_zero]
      rw [X.presheaf.germ_res_apply]
    · simp only [a, Fin.cons_succ]
      rw [X.presheaf.germ_res_apply, hτ l]
  have hli : LinearIndependent (ResidueField (X.presheaf.stalk p)) fun i ↦
      (1 : ResidueField (X.presheaf.stalk p)) ⊗ₜ[X.presheaf.stalk p]
        D ((Spec (.of ℂ)).presheaf.stalk (sX p)) (X.presheaf.stalk p)
          (X.presheaf.germ V₀ p hpV₀ (a i)) := by
    rw [hgerm, linearIndependent_fin_cons]
    refine ⟨?_, ?_⟩
    · exact (isBasis_D_stalk_base_of_isRegularSystemOfParameters sX p
        (isClosed_singleton_toScheme x) t ht).1.comp _ (hjE.comp e.injective)
    · let J : Finset (Mori.PrimeDivisor X) := s.filter fun E ↦ p ∈ E.support
      have hJ : J ⊆ s := Finset.filter_subset _ _
      have hle : ∀ E ∈ J, E.idealSheaf ≤ ⨆ E ∈ J, E.idealSheaf := fun E hE ↦
        le_iSup₂ (f := fun E (_ : E ∈ J) ↦ E.idealSheaf) E hE
      have hpZ : p ∈ (⨆ E ∈ J, E.idealSheaf).support := by
        rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_iSup,
          TopologicalSpace.Closeds.coe_iInf, Set.mem_iInter]
        intro E
        rw [Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf, Set.mem_iInter]
        intro hE
        exact (Finset.mem_filter.1 hE).2
      refine tmul_D_germ_app_notMem_span g hg _ (hstr J hJ) p hpZ cB.U hgp (cB.z 0)
        (tmul_D_germ_curveChart_ne_zero (realize g hg x) hb) _ fun l ↦ ?_
      have hEJ : (e l).1.1 ∈ J :=
        Finset.mem_filter.2 ⟨(e l).1.2, (hs' _).1 (e l).2⟩
      refine IdealSheafData.stalk_mono (hle _ hEJ) p ?_
      rw [hI' (e l)]
      exact Ideal.mem_span_singleton_self _
  obtain ⟨U, hpU, hUV, z, cc, hz, hzc⟩ :=
    exists_etale_coordinates_extending_of_mem (sX := sX) (n := n) Vd p hxd V₀ hpV₀ a hli
  refine ⟨U, z, hz, mem_chart_iff.2 hpU, fun q hq ↦ (hOsub (hUV hq)).2.2.2, cc 0, hUV.trans hV₀B,
    ?_, s',
    ⟨fun E ↦ cc (Fin.succ (e.symm E)), fun E E' h ↦
      e.symm.injective (Fin.succ_injective _ (cc.injective h))⟩,
    fun E ↦ cc.injective.ne (Fin.succ_ne_zero _), fun E hE ↦ ?_, fun E y hy ↦ ?_⟩
  · rw [hzc 0]
    simp only [a, Fin.cons_zero]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  · refine Set.eq_empty_of_forall_notMem fun y hy ↦ ?_
    have hyO : toScheme y ∈ O := hUV (mem_chart_iff.1 hy.2)
    exact (hOsub hyO).2.2.1 E.1 E.2 (fun h ↦ hE ((hs' E).2 h)) hy.1
  · change toScheme y ∈ (E : s).1.support ↔ _
    have hyU : toScheme y ∈ U := mem_chart_iff.1 hy
    have hkey := toScheme_mem_basicOpen_iff (sX := sX) ⟨y, hy⟩ (z (cc (Fin.succ (e.symm E))))
    rw [evalHom_apply] at hkey
    change _ ↔ eval U (z (cc (Fin.succ (e.symm E)))) ⟨y, hy⟩ = 0
    rw [← not_iff_not, ← ne_eq, ← hkey, hzc, Scheme.basicOpen_res]
    simp only [a, Fin.cons_succ]
    rw [Scheme.basicOpen_res]
    have h1 := hτV (e.symm E) (toScheme y) (hV₀l _ (hUV hyU))
    rw [e.apply_symm_apply] at h1
    rw [show toScheme y ∈ U ⊓ (V₀ ⊓ X.basicOpen (τ (e.symm E))) ↔
        toScheme y ∈ X.basicOpen (τ (e.symm E)) from ⟨fun h ↦ h.2.2, fun h ↦ ⟨hyU, hUV hyU, h⟩⟩]
    exact ⟨fun h ↦ by_contra fun hb ↦ h (h1.2 hb), fun hb ha ↦ h1.1 ha hb⟩

/-- **A relative simple normal crossing divisor gives manifold data.** Let `g : X ⟶ B` be a
morphism from a smooth complex variety of dimension `n` to a smooth complex curve and
`E = ∑_{E_i ∈ s} E_i` a simple normal crossing divisor on `X` every intersection of whose
components (including `X` itself) is smooth over `B`. Then for a choice of preferred charts of
`X^an`, `g^an` is holomorphic, the components `E_i^an` have simultaneous coordinate charts in the
maximal atlas, `g^an` is a submersion, and at every `x`, `dg^an_x` is nonzero on the tangent cone
of the stratum `⋂_{x ∈ E_i} E_i^an`: the hypotheses on `g` and the `E_i^an` of
`MMP.Analytic.exists_homeomorph_prod_of_relativeSNC`. -/
public theorem exists_pick_relativeSNC_of_isSNC [SmoothOfRelativeDimension n sX] (g : X ⟶ B)
    (hg : g ≫ sB = sX) (s : Finset (Mori.PrimeDivisor X))
    (hs : Mori.DivisorWithCoeffs.IsSNC sX (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ g)) :
    let D : s → Set (ComplexPoints sX) := fun E ↦ {y | toScheme y ∈ E.1.support}
    ∃ pick : ∀ x : ComplexPoints sX, {c : EtaleCoordinateChart sX n // x ∈ c.W},
      letI := etaleChartedSpaceOf sX n (EuclideanSpace.equiv (Fin n) ℂ).symm pick
      (∀ N : WithTop ℕ∞, ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) N (realize g hg)) ∧
      (∀ (N : WithTop ℕ∞) (x : ComplexPoints sX),
        ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) N (ComplexPoints sX),
          x ∈ φ.source ∧ ∃ (s : Finset s) (c : s ↪ Fin n),
            (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
            ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0}) ∧
      (∀ x : ComplexPoints sX,
        Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (realize g hg) x)) ∧
      ∀ x : ComplexPoints sX, ∃ v ∈ tangentConeAt ℂ
          ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).target ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).symm ⁻¹' ⋂ (i) (_ : x ∈ D i), D i)
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x),
        mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (realize g hg) x v ≠ 0 :=
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have := smoothOfRelativeDimension_top_ι (n := n) (sX := sX)
  exists_pick_relativeSNC g hg _ fun x ↦ by
    obtain ⟨U, z, hz, hx, -, j₀, hU, hzj, s', c, h⟩ :=
      exists_etale_coordinates_adapted_of_isSNC (sX := sX) (n := n) ⊤ g hg s hs hstr x trivial
    exact ⟨U, z, hz, hx, j₀, hU, hzj, s', c, h⟩

end RelativeSNCDivisor

section RelativeDimensionLocus

variable {X B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}

variable (sX) in
/-- The open locus of `X` on which `X ⟶ Spec ℂ` is smooth of relative dimension `d`: the union
of the opens `V` with `V ⟶ Spec ℂ` smooth of relative dimension `d`. -/
@[expose] public noncomputable def relativeDimensionLocus (d : ℕ) : X.Opens :=
  ⨆ (V : X.Opens) (_ : SmoothOfRelativeDimension d (V.ι ≫ sX)), V

public lemma mem_relativeDimensionLocus_iff {d : ℕ} {p : X} :
    p ∈ relativeDimensionLocus sX d ↔
      ∃ V : X.Opens, SmoothOfRelativeDimension d (V.ι ≫ sX) ∧ p ∈ V := by
  simp only [relativeDimensionLocus, TopologicalSpace.Opens.mem_iSup, exists_prop]

/-- On its relative dimension locus, `X ⟶ Spec ℂ` is smooth of relative dimension `d`. -/
public instance smoothOfRelativeDimension_relativeDimensionLocus (d : ℕ) :
    SmoothOfRelativeDimension d ((relativeDimensionLocus sX d).ι ≫ sX) := by
  let : ∀ m, IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} m) := fun m ↦
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} m)
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun V : {V : X.Opens // SmoothOfRelativeDimension d (V.ι ≫ sX)} ↦
      (relativeDimensionLocus sX d).ι ⁻¹ᵁ V.1) ?_ fun V ↦ ?_
  · refine eq_top_iff.2 fun q _ ↦ ?_
    obtain ⟨V, hV, hqV⟩ := mem_relativeDimensionLocus_iff.1 q.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hqV⟩
  · have H : Set.range (((relativeDimensionLocus sX d).ι ⁻¹ᵁ V.1).ι ≫
        (relativeDimensionLocus sX d).ι) ⊆ Set.range V.1.ι := by
      rintro _ ⟨r, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact r.2
    have hfac := IsOpenImmersion.lift_fac V.1.ι
      (((relativeDimensionLocus sX d).ι ⁻¹ᵁ V.1).ι ≫ (relativeDimensionLocus sX d).ι) H
    rw [← Category.assoc, ← hfac, Category.assoc]
    haveI := V.2
    exact IsZariskiLocalAtSource.comp ‹_› _

/-- The relative dimension at a point is unique. -/
public lemma eq_of_mem_relativeDimensionLocus [Smooth sX] {d d' : ℕ} {p : X}
    (h : p ∈ relativeDimensionLocus sX d) (h' : p ∈ relativeDimensionLocus sX d') : d = d' := by
  obtain ⟨V, hV, hpV⟩ := mem_relativeDimensionLocus_iff.1 h
  obtain ⟨V', hV', hpV'⟩ := mem_relativeDimensionLocus_iff.1 h'
  haveI := hV
  haveI := hV'
  have h1 := finrank_kaehlerDifferential_stalk_of_mem (sX := sX) (n := d) V p hpV
  have h2 := finrank_kaehlerDifferential_stalk_of_mem (sX := sX) (n := d') V' p hpV'
  exact h1.symm.trans h2

/-- Every point of a smooth complex scheme lies in a relative dimension locus. -/
public lemma exists_mem_relativeDimensionLocus [Smooth sX] (p : X) :
    ∃ d, p ∈ relativeDimensionLocus sX d := by
  obtain ⟨V, hpV, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_nbhd sX p
  exact ⟨d, mem_relativeDimensionLocus_iff.2 ⟨V, hd, hpV⟩⟩

/-- The relative dimension loci are closed (they are open by definition). -/
public lemma isClosed_relativeDimensionLocus [Smooth sX] (d : ℕ) :
    IsClosed (relativeDimensionLocus sX d : Set X) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨d', hd'⟩ := exists_mem_relativeDimensionLocus (sX := sX) p
  refine ⟨relativeDimensionLocus sX d', fun q hq hqd ↦ ?_, (relativeDimensionLocus sX d').isOpen,
    hd'⟩
  have := eq_of_mem_relativeDimensionLocus hqd hq
  subst this
  exact hp hd'

variable [SmoothOfRelativeDimension 1 sB]

/-- **Manifold data on a relative dimension locus.** Let `g : X ⟶ B` be a morphism from a
scheme smooth over `ℂ` to a smooth complex curve and `E = ∑_{E_i ∈ s} E_i` a simple normal
crossing divisor on `X` every intersection of whose components (including `X` itself) is smooth
over `B`. Then on the locus `Y ⊆ X` of relative dimension `d`, for a choice of preferred charts
of `Y^an`, `g^an` is holomorphic, the traces `E_i^an ∩ Y^an` have simultaneous coordinate charts,
`g^an` is a submersion, and `dg^an` is nonzero on the tangent cone of every stratum. -/
public theorem exists_pick_relativeSNC_relativeDimensionLocus [Smooth sX] (d : ℕ) (g : X ⟶ B)
    (hg : g ≫ sB = sX) (s : Finset (Mori.PrimeDivisor X))
    (hs : Mori.DivisorWithCoeffs.IsSNC sX (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (hstr : ∀ J ⊆ s, Smooth ((⨆ E ∈ J, E.idealSheaf).subschemeι ≫ g)) :
    let D : s → Set (ComplexPoints ((relativeDimensionLocus sX d).ι ≫ sX)) := fun E ↦
      {y | (relativeDimensionLocus sX d).ι (toScheme y) ∈ E.1.support}
    let gY := realize (sX := (relativeDimensionLocus sX d).ι ≫ sX) (sY := sB)
      ((relativeDimensionLocus sX d).ι ≫ g) (by rw [Category.assoc, hg])
    ∃ pick : ∀ x : ComplexPoints ((relativeDimensionLocus sX d).ι ≫ sX),
        {c : EtaleCoordinateChart ((relativeDimensionLocus sX d).ι ≫ sX) d // x ∈ c.W},
      letI := etaleChartedSpaceOf ((relativeDimensionLocus sX d).ι ≫ sX) d
        (EuclideanSpace.equiv (Fin d) ℂ).symm pick
      (∀ N : WithTop ℕ∞, ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) 𝓘(ℂ) N (gY)) ∧
      (∀ (N : WithTop ℕ∞) (x : ComplexPoints ((relativeDimensionLocus sX d).ι ≫ sX)),
        ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) N
            (ComplexPoints ((relativeDimensionLocus sX d).ι ≫ sX)),
          x ∈ φ.source ∧ ∃ (s : Finset s) (c : s ↪ Fin d),
            (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
            ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0}) ∧
      (∀ x : ComplexPoints ((relativeDimensionLocus sX d).ι ≫ sX),
        Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) 𝓘(ℂ) (gY) x)) ∧
      ∀ x : ComplexPoints ((relativeDimensionLocus sX d).ι ≫ sX), ∃ v ∈ tangentConeAt ℂ
          ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) x).target ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) x).symm ⁻¹' ⋂ (i) (_ : x ∈ D i), D i)
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) x x),
        mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) 𝓘(ℂ) (gY) x v ≠ 0 := by
  intro D gY
  refine exists_pick_relativeSNC _ (by rw [Category.assoc, hg]) D fun y ↦ ?_
  have hxY : toScheme (realize (sX := (relativeDimensionLocus sX d).ι ≫ sX)
      (relativeDimensionLocus sX d).ι rfl y) ∈ (relativeDimensionLocus sX d) := (toScheme y).2
  obtain ⟨U, z, hz, hx, hUY, j₀, hU, hzj, s', c, hne, hout, hin⟩ :=
    exists_etale_coordinates_adapted_of_isSNC (n := d) (relativeDimensionLocus sX d) g hg s hs hstr
      (realize (sX := (relativeDimensionLocus sX d).ι ≫ sX) (relativeDimensionLocus sX d).ι rfl y)
      hxY
  have hpt : realize (sX := (relativeDimensionLocus sX d).ι ≫ sX)
        ((relativeDimensionLocus sX d).ι ≫ g) (by rw [Category.assoc, hg]) y =
      realize g hg (realize (sX := (relativeDimensionLocus sX d).ι ≫ sX)
        (relativeDimensionLocus sX d).ι rfl y) :=
    congrFun (realize_comp (relativeDimensionLocus sX d).ι rfl g hg) y
  rw [hpt]
  refine ⟨(relativeDimensionLocus sX d).ι ⁻¹ᵁ U,
    fun i ↦ (relativeDimensionLocus sX d).ι.app U (z i),
    etale_homOfVector_ι (relativeDimensionLocus sX d) U z hz,
    (mem_chart_preimage_iff (relativeDimensionLocus sX d).ι rfl U y).2 hx, j₀, fun q hq ↦ hU hq, ?_,
    s', c, hne,
    fun i hi ↦ ?_, fun i y' hy' ↦ ?_⟩
  · dsimp only
    rw [hzj, ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply,
      Scheme.Hom.comp_app]
    rfl
  · refine Set.eq_empty_of_forall_notMem fun y' hy' ↦ ?_
    exact (Set.eq_empty_iff_forall_notMem.1 (hout i hi))
      (realize (relativeDimensionLocus sX d).ι rfl y')
      ⟨hy'.1, (mem_chart_preimage_iff (relativeDimensionLocus sX d).ι rfl U y').1 hy'.2⟩
  · rw [eval_app_realize (relativeDimensionLocus sX d).ι rfl U]
    exact hin i (realize (sX := (relativeDimensionLocus sX d).ι ≫ sX)
      (relativeDimensionLocus sX d).ι rfl y') _

end RelativeDimensionLocus

section ProperExceptional

variable {Z X T B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}

/-- **The preimage of a centre proper over the base is proper over the base.** Let `f : Z ⟶ X`
be proper, `iT : T ⟶ X` a closed immersion and `h : X ⟶ B` a morphism of schemes of finite type
over `ℂ` with `T ⟶ B` proper (for instance finite). Then `f^an` restricted to the preimage of
`T^an` is a proper map to `B^an` after composing with `h^an`. -/
public theorem isProperMap_restrict_realize_preimage_range [LocallyOfFiniteType sX]
    [QuasiCompact sX] [LocallyOfFiniteType sB] [QuasiCompact sB] (f : Z ⟶ X) [IsProper f]
    [QuasiCompact (f ≫ sX)] (iT : T ⟶ X) [IsClosedImmersion iT] (h : X ⟶ B) (hh : h ≫ sB = sX)
    [IsProper (iT ≫ h)] :
    IsProperMap ((realize f rfl ⁻¹' Set.range (realize iT rfl)).domRestrict
      (realize (sX := f ≫ sX) (sY := sB) (f ≫ h) (by rw [Category.assoc, hh]))) := by
  have hfp := (isSeparatedMap_and_isProperMap_realize (sX := f ≫ sX) (sS := sX) f rfl).2
  have hTB := (isSeparatedMap_and_isProperMap_realize (sX := iT ≫ sX) (sS := sB) (iT ≫ h)
    (by rw [Category.assoc, hh])).2
  have hTp := (isSeparatedMap_and_isProperMap_realize (sX := iT ≫ sX) (sS := sX) iT rfl).2
  have hinj : Function.Injective (realize iT rfl) := fun t t' htt ↦
    ComplexPoints.ext ((cancel_mono iT).1 (congrArg (fun y : ComplexPoints sX ↦ y.hom) htt))
  have hTe : IsClosedEmbedding (realize iT rfl) :=
    IsClosedEmbedding.of_continuous_injective_isClosedMap hTp.continuous hinj hTp.isClosedMap
  let e := hTe.isEmbedding.toHomeomorph
  have key : (realize f rfl ⁻¹' Set.range (realize iT rfl)).domRestrict
      (realize (sX := f ≫ sX) (sY := sB) (f ≫ h) (by rw [Category.assoc, hh])) =
      realize (sX := iT ≫ sX) (sY := sB) (iT ≫ h) (by rw [Category.assoc, hh]) ∘ e.symm ∘
        (Set.range (realize iT rfl)).restrictPreimage (realize f rfl) := by
    funext z
    obtain ⟨t, ht⟩ := z.2
    have he : e.symm ((Set.range (realize iT rfl)).restrictPreimage (realize f rfl) z) = t :=
      e.symm_apply_eq.2 (Subtype.ext ht.symm)
    simp only [Function.comp_apply, he]
    rw [realize_comp iT rfl h hh, realize_comp f rfl h hh]
    simp only [Function.comp_apply, ht]
    rfl
  rw [key]
  exact hTB.comp (e.symm.isProperMap.comp (hfp.restrictPreimage _))

end ProperExceptional

end MMP.Analytic.ComplexPoints
