module

public import MMP.AlgebraicGeometry.Variety.ParameterPoint
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ParameterPointFibre
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ComplexSchemeSubscheme
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Finite
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksHomotopyInfra
public import MMP.AlgebraicGeometry.RegularImmersion.CodimOne
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalization
public import MMP.AlgebraicGeometry.CycleMap.Stacks.AlgebraicEquivalence.PointSection
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.HomotopyPointGeneric
public import MMP.AlgebraicTopology.BorelMoore.Suspension
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AgreesSubmanifoldRank
public import MMP.AlgebraicGeometry.Analytic.DivisorOrientationDatum
public import MMP.AlgebraicGeometry.CycleMap.OrientationClass.HomotopyGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.CupCompositeGeneric
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionNormalize
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple
import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Fulton's Lemma 19.1.3 at a fibre, on Stacks cycles

Let `f : V → B` be a dominant morphism from a complex variety of dimension `n + 1` to a smooth
complex curve, and `t ∈ B` a parameter point. The fibre `V_t = f⁻¹(t)` is the zero scheme of the
pull-back `f^* σ` of a section `σ` of a line bundle on `B` cutting out the reduced point `t`, so
Fulton's Lemma 19.1.3 for the section `f^* σ` gives the specialization formula
`f^*(u_{t,B}) ∩ cl(V) = cl_{V_t}([V_t]_n)` (Fulton, proof of Lemma 19.1.3: "apply [the lemma for
line bundles] to `X`, `f^* L`, `f^* s_t`").

## Main results

* `MMP.Modules.properPushforward_zeroLocusSubschemeMap_of_zeroLocus_eq`: `ν_{D*}[D']_k = [D]_k`
  for a section `σ` whose zero scheme is the zero scheme of a non-zero section of an invertible
  module.
* `MMP.Modules.localizedFirstChernFormula_of_zeroLocus_eq`: Fulton's Lemma 19.1.3 for such a
  section `σ`.
* `MMP.ParameterPoint.pushforward_cycleClass_fibre_eq_capProductSupportPullback`: **the
  specialization formula** `f^*(u_{t,B}) ∩ cl(V) = cl_{V_t}([V_t]_n)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Stacks.Chow
open MMP.UnderlyingSpace
open scoped MMP.SubschemeOver

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

namespace MMP.Modules

open MMP AlgebraicGeometry.SheafOfModules

section Cycle

/-- Proper push-forward of cycles depends only on the morphism. -/
private lemma properPushforward_congr_hom' (C : ChowSituation.{0}) {A B : Scheme.{0}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    {f f' : A ⟶ B} [IsProper f] [IsProper f'] (h : f = f') (hf : f ≫ sB = sA) (k : ℤ)
    (c : CycleGroup C sA k) :
    properPushforward C sA sB f hf k c = properPushforward C sA sB f' (h ▸ hf) k c := by
  subst h
  rfl

variable {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsIntegral X]
  [X'.Over (Spec (.of ℂ))] [IsComplexScheme X'] [IsIntegral X']
  (ν : X' ⟶ X) [ν.IsOver (Spec (.of ℂ))] [IsProper ν]

/-- **`ν_{D*}[D']_k = [D]_k`** (Stacks Tag 02ST, for degree one). Let `ν : X' → X` be a proper
surjective morphism of complex varieties of dimension `k + 1` with residue degree one at the
generic point, and `σ` a section of `𝐕(ℰ)` whose zero scheme `D = Z(σ)` is the zero scheme
`Z(s)` of a non-zero global section `s` of an invertible module `ℒ`. With `D' = Z(ν^*σ)`, the
restriction `ν_D : D' → D` pushes `[D']_k` to `[D]_k`. -/
theorem properPushforward_zeroLocusSubschemeMap_of_zeroLocus_eq {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X)
    (hn' : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X') (hν : Function.Surjective ν)
    (hdeg : ν.residueDegree (genericPoint X') = 1) {E : X.Modules} [E.IsQuasicoherent]
    {σ : X ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 X) (L : X.Modules)
    [IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (hD : zeroLocus E σ = Stacks.Divisors.zeroScheme X L s) :
    properPushforward (fieldChowSituation ℂ) (_ ↘ Spec (.of ℂ)) (_ ↘ Spec (.of ℂ))
        (zeroLocusSubschemeMap ν hσ) (comp_over _ _) k
        (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (_ ↘ Spec (.of ℂ)) (𝟙 _) k) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k := by
  have : IsDominant ν := ⟨hν.denseRange⟩
  have hD' : zeroLocus _ (pullbackSectionMap ν hσ) =
      Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback ν).obj L)
        (pullbackGlobalSections ν L s) := by
    rw [zeroLocus_pullbackSectionMap, hD, Stacks.Divisors.zeroScheme_pullback]
  have hX := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (X ↘ Spec (.of ℂ)) hn.symm
  have hX' := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (X' ↘ Spec (.of ℂ)) hn'.symm
  have key := properPushforward_cycleAssociatedToZeroScheme (fieldChowSituation ℂ) _ _ hX hX' ν
    (comp_over ν _) L s hs
  rw [finrank_functionField_eq_residueDegree ν, hdeg, Nat.cast_one, one_smul,
    show ((k + 1 : ℕ) : ℤ) - 1 = k by push_cast; ring] at key
  apply properPushforward_injective_of_isClosedImmersion (fieldChowSituation ℂ) _
    (X ↘ Spec (.of ℂ)) (zeroLocus E σ).subschemeι (comp_over _ _) k
  rw [properPushforward_properPushforward,
    properPushforward_congr_hom' _ _ _ (zeroLocusSubschemeMap_subschemeι ν hσ),
    ← properPushforward_properPushforward _ _ (X' ↘ Spec (.of ℂ)) _ _ ν (comp_over _ _)
      (comp_over _ _),
    properPushforward_cycleAssociatedToClosedSubscheme_id,
    properPushforward_cycleAssociatedToClosedSubscheme_id, hD, hD']
  exact key

end Cycle

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- **Fulton's Lemma 19.1.3 for a section cutting out the zero scheme of a section of an
invertible module** (Fulton, §19.1). Let `X` be a complex variety of dimension `k + 1`, `ℰ`
locally free of rank one and `σ ≠ 0` a section of `𝐕(ℰ)` whose zero scheme `D = Z(σ)` is the zero
scheme `Z(s)` of a non-zero global section `s` of an invertible module `ℒ`. Then
`σ^*(u_ℰ) ∩ cl(X) = cl_D([D]_k)` in `H_{2k} D` for every fundamental class `cl(X)`. The proof is
that of `MMP.Modules.localizedFirstChernFormula`: pass to the normalization. -/
theorem localizedFirstChernFormula_of_zeroLocus_eq [IsIntegral X] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X) {E : X.Modules} [E.IsQuasicoherent]
    [IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1] {σ : X ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))]
    (hσ : σ ≫ proj E = 𝟙 X) (h0 : σ ≠ zeroSection E) (L : X.Modules)
    [IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (hD : zeroLocus E σ = Stacks.Divisors.zeroScheme X L s) :
    LocalizedFirstChernFormula R hn E σ := by
  have hX := MMP.finite_irreducibleComponents_of_isIntegral X
  have : IsFinite (X.normalization hX) :=
    normalization_isFinite X (isJapaneseScheme_of_isNagataScheme X
      (isNagataScheme_of_locallyOfFiniteType_over_field ℂ (X ↘ Spec (.of ℂ))))
  have hn' : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim (X.normalizationScheme hX) :=
    (topologicalKrullDim_normalizationSchemeOverField (X ↘ Spec (.of ℂ)) hn.symm).symm
  have := Scheme.isNormal_normalizationScheme X hX
  have hsurj := (X.normalization hX).surjective
  have hdeg := residueDegree_genericPoint_eq_one_of_isBirational (X.normalization hX)
    (Scheme.isBirational_normalization X hX)
  exact LocalizedFirstChernFormula.of_proper_birational R hn' hσ _ hsurj hdeg
    (properPushforward_zeroLocusSubschemeMap_of_zeroLocus_eq _ hn hn' hsurj hdeg hσ L s hs hD)
    (LocalizedFirstChernFormula.of_isNormal R hn' (pullbackSectionMap_proj _ hσ)
      (pullbackSectionMap_ne_zeroSection _ hσ h0 hsurj))

end MMP.Modules

/-! ### The specialization formula -/

namespace MMP.ParameterPoint

open MMP MMP.Modules AlgebraicGeometry.SheafOfModules

/-- Closed immersions of reduced schemes with the same image have the same kernel. -/
private lemma ker_eq_ker_of_range_eq {X X' Y : Scheme.{0}} [IsReduced X] [IsReduced X']
    (f : X ⟶ Y) (g : X' ⟶ Y) [IsClosedImmersion f] [IsClosedImmersion g]
    (h : range f = range g) : f.ker = g.ker := by
  have hf : IsReduced f.ker.subscheme := isReduced_of_isOpenImmersion (inv f.toImage)
  have hg : IsReduced g.ker.subscheme := isReduced_of_isOpenImmersion (inv g.toImage)
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme f.ker _ rfl,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme g.ker _ rfl]
  congr 1
  ext1
  rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker, h]

variable {B : Scheme.{0}} [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))]

/-- The complex point of a parameter point `t` cuts out the same closed subscheme of `B` as `t`. -/
private lemma ker_toHom_complexPoint (t : ParameterPoint B) :
    t.complexPoint.toHom.ker = t.ι.ker := by
  refine ker_eq_ker_of_range_eq _ _ ?_
  rw [range_ι]
  ext x
  simp only [mem_range, mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint ℂ), complexPoint_toHom_closedPoint]
  · rintro rfl
    exact ⟨_, complexPoint_toHom_closedPoint t⟩

/-- Pull-back commutes with enlarging the support. -/
private lemma pullback_hom_forget_hom (R : Type) [CommRing R] {Y' Y : TopCat.{0}} (f : Y' ⟶ Y)
    {X X' : Set Y} (h : X ⊆ X') (j : ℤ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y X j) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) f X' j).hom
        ((cohomologyWithSupports.forget R (ModuleCat.of R R) Y h j).hom x) =
      (cohomologyWithSupports.forget R (ModuleCat.of R R) Y' (preimage_mono h) j).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f X j).hom x) := by
  rw [cohomologyWithSupports.forget_hom_pullback_hom f (preimage_mono h)
    (fun _ hy hx ↦ hy (h hx)) j x]
  unfold cohomologyWithSupports.forget cohomologyWithSupports.pullback
  rw [cohomologyWithSupports.map_hom_map_hom f (𝟙 Y) (A'' := (f ⁻¹' X')ᶜ) (A' := X'ᶜ)
    (A := Xᶜ) (fun _ hy ↦ hy) (compl_subset_compl.mpr h) (fun _ hy hx ↦ hy (h hx))
    (Category.comp_id f)]

/-- `j = j'` transports commute with push-forward. -/
private lemma pushforward_congrDegree (R : Type) [CommRing R] {Y Z : TopCat.{0}} (g : Y ⟶ Z)
    (hg : IsProperMap g) {j j' : ℤ} (h : j = j')
    (x : borelMooreHomology R (ModuleCat.of R R) Y j) :
    (borelMooreHomology.pushforward R (ModuleCat.of R R) g hg j').hom
        (BorelMooreCross.congrDegree R Y h x) =
      BorelMooreCross.congrDegree R Z h
        ((borelMooreHomology.pushforward R (ModuleCat.of R R) g hg j).hom x) := by
  subst h
  rfl

/-- The fibre of a dominant morphism to a smooth curve over a parameter point is not all of the
source: its ideal sheaf is not `⊥`. -/
theorem ker_fibreι_ne_bot (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))) {V : Scheme.{0}}
    (f : V ⟶ B) [IsDominant f] (t : ParameterPoint B) : (fibreι f t).ker ≠ ⊥ := by
  intro hbot
  have hsupp := Scheme.Hom.support_ker (fibreι f t)
  rw [hbot, Scheme.IdealSheafData.support_bot, range_fibreι,
    ((isClosed_point t).preimage f.continuous).closure_eq] at hsupp
  have hrange : range f ⊆ {t.point} := range_subset_iff.2 fun x ↦ by
    rw [← mem_preimage, ← hsupp]
    trivial
  have huniv : ({t.point} : Set B) = univ := by
    have := closure_mono hrange
    rw [f.denseRange.closure_range, (isClosed_point t).closure_eq] at this
    exact univ_subset_iff.mp this
  have : Subsingleton B := by
    rw [← subsingleton_univ_iff, ← huniv]
    exact subsingleton_singleton
  have : Nonempty B := ⟨t.point⟩
  have : DiscreteTopology B := ⟨Subsingleton.elim _ _⟩
  have h1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := ℂ) (X := B) 1
  rw [topologicalKrullDim_eq_zero_of_discreteTopology_nonempty] at h1
  exact absurd h1 (by norm_num)

/-- The ideal of the fibre `V_t` is the pull-back of the ideal of the point `t`. -/
theorem ker_fibreι_eq_comap {V : Scheme.{0}} (f : V ⟶ B) (t : ParameterPoint B) :
    (fibreι f t).ker = t.ι.ker.comap f := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (isPullback_fibre f t).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- A closed subscheme `Z` of `V` with the ideal sheaf of the fibre `V_t` is isomorphic to `V_t`
over `ℂ`, compatibly with the closed immersions into `V`, and the isomorphism pushes `[Z]_n` to
`[V_t]_n`. -/
theorem exists_isIso_fibre_of_eq_ker {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] (f : V ⟶ B) (t : ParameterPoint B) (I : V.IdealSheafData)
    (hI : I = (fibreι f t).ker) (n : ℕ) :
    ∃ (φ : I.subscheme ⟶ fibre f t) (_ : IsIso φ) (_ : φ.IsOver (Spec (.of ℂ))),
      φ ≫ fibreι f t = I.subschemeι ∧
      properPushforward (fieldChowSituation ℂ) _ (fibre f t ↘ Spec (.of ℂ)) φ
        (comp_over φ _) n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (I.subscheme ↘ Spec (.of ℂ)) (𝟙 _) n) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (fibre f t ↘ Spec (.of ℂ))
        (𝟙 _) n := by
  let φ : I.subscheme ⟶ fibre f t :=
    Scheme.IdealSheafData.inclusion hI.ge ≫ inv (fibreι f t).toImage
  have hφι : φ ≫ fibreι f t = I.subschemeι := by
    have e : inv (fibreι f t).toImage ≫ fibreι f t = (fibreι f t).imageι := by
      rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
    simp only [φ, Category.assoc, e]
    exact Scheme.IdealSheafData.inclusion_subschemeι _
  have : IsIso φ := by
    have := Stacks.Chow.TensorZeroScheme.isIso_inclusion_of_eq hI.symm
    infer_instance
  have : φ.IsOver (Spec (.of ℂ)) := ⟨by
    change φ ≫ fibreι f t ≫ V ↘ Spec (.of ℂ) = I.subschemeι ≫ V ↘ Spec (.of ℂ)
    rw [← Category.assoc, hφι]⟩
  refine ⟨φ, inferInstance, inferInstance, hφι, ?_⟩
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  exact cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso φ) (by simp) _

variable (R : Type) [CommRing R]

/-- **Fulton's Lemma 19.1.3 at a fibre, on Stacks cycles** (Fulton, §19.1). Let `f : V → B` be a
dominant morphism from a complex variety of dimension `n + 1` to a smooth complex curve, `t ∈ B` a
parameter point and `u_{t,B} ∈ H²(B, B - t)` the local orientation class of `B(ℂ)` at `t`. Then
`f^*(u_{t,B}) ∩ cl(V) = cl_{V_t}([V_t]_n)` in `H_{2n}(f⁻¹ t)`, for every fundamental class
`cl(V)`, where `[V_t]_n` is Stacks' cycle of the scheme-theoretic fibre and `H_* V_t` is mapped to
`H_*(f⁻¹ t)` along `V_t(ℂ) ≅ f⁻¹(t) ⊆ V(ℂ)`.

The fibre is the zero scheme of `f^* σ_t`, for the canonical section `σ_t` of `𝒪_B(t)`, whose
pull-back `σ_t^* u` of the Thom class is `u_{t,B}`; so this is Fulton's Lemma 19.1.3 for `f^* σ_t`
(`MMP.Modules.localizedFirstChernFormula_of_zeroLocus_eq`). -/
theorem pushforward_cycleClass_fibre_eq_capProductSupportPullback
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))) {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] [IsIntegral V] (f : V ⟶ B)
    [f.IsOver (Spec (.of ℂ))] [IsDominant f]
    {n : ℕ} (hn : ((n + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V) (t : ParameterPoint B)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {t.complexPoint} (2 * 1 : ℕ)}
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis t.complexPoint u)
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V))
      (2 * (n + 1) : ℕ)}
    (hμ : IsVarietyFundamentalClass R hn μ) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) (fibreComplexPointsHom f t)
        (isProperMap_fibreComplexPointsHom f t) (2 * n : ℕ)
        (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (fibre f t ↘ Spec (.of ℂ)) (𝟙 _) n)) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        (borelMooreHomology.capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) f))
          isClosed_singleton (hasProperNeighbourhoodDeformations_preimage_singleton f _)
          (2 * 1 : ℕ) (2 * (n + 1) : ℕ) u μ) := by
  -- the canonical section `σ_B` of `𝒪_B(t)` cuts out the point `t`
  have hDt := ker_toHom_complexPoint t
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor t.ι.ker :=
    hDt ▸ isEffectiveCartierDivisor_ker_of_isRegularClosedImmersionOfCodim_one _
      (UnderlyingSpace.isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hB t.complexPoint)
  set D := t.ι.ker
  set L := Stacks.Divisors.divisorSheaf D
  set sD := Stacks.Divisors.divisorSheafGlobalSection D
  set EB := MMP.Topology.divisorDualSheaf D
  set σB := MMP.Topology.canonicalSectionMap D
  have hσB : σB ≫ proj EB = 𝟙 B := MMP.Topology.canonicalSectionMap_proj D
  have hzB : zeroLocus EB σB = t.complexPoint.toHom.ker :=
    (MMP.Topology.zeroLocus_canonicalSectionMap D).trans hDt.symm
  have hu' := IsLocalOrientationClass.eq (by norm_num) hu
    (Modules.isLocalOrientationClass_forget_pullback_thomClass t.complexPoint R hB hσB hzB)
  -- its pull-back `σ = f^* σ_B` cuts out the fibre
  set E := (Scheme.Modules.pullback f).obj EB
  set σ := pullbackSectionMap f hσB
  have hσ : σ ≫ proj E = 𝟙 V := pullbackSectionMap_proj f hσB
  have hzV : zeroLocus E σ = (fibreι f t).ker := by
    rw [zeroLocus_pullbackSectionMap, MMP.Topology.zeroLocus_canonicalSectionMap,
      ker_fibreι_eq_comap]
  haveI : IsInvertible V.sheaf.obj V.ringCatSheaf.property ((Scheme.Modules.pullback f).obj L) :=
    Stacks.WeilCohomology.isInvertible_pullback_obj f L inferInstance
  have hzV' : zeroLocus E σ = Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback f).obj L)
      (pullbackGlobalSections f L sD) := by
    have h1 : zeroLocus EB σB = Stacks.Divisors.zeroScheme B L sD := zeroLocus_globalSectionMap L sD
    rw [zeroLocus_pullbackSectionMap, Stacks.Divisors.zeroScheme_pullback, h1]
  have hne : zeroLocus E σ ≠ ⊥ := hzV ▸ ker_fibreι_ne_bot hB f t
  have h0 : σ ≠ zeroSection E := fun h ↦ hne (h ▸ zeroLocus_zeroSection E)
  have hs : pullbackGlobalSections f L sD ≠ 0 := by
    refine fun h ↦ hne (hzV'.trans ?_)
    rw [h]
    exact AlgebraicGeometry.zeroScheme_zero _ _
  have hform := localizedFirstChernFormula_of_zeroLocus_eq R hn hσ h0 _ _ hs hzV' μ hμ
  -- `f^*(u) = σ^*(u_ℰ)` in `H²(V, V - f⁻¹(t))`
  have hπ := baseChangeMap_proj f EB
  have hF := isFibrewiseIso_baseChangeMap f EB 1
  have hσσ := pullbackSectionMap_baseChangeMap f hσB
  have hSP : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) =
      (TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {t.complexPoint} := by
    rw [preimage_zeroLocus_of_comp σB σ hπ hF hσσ]
    congr 1
    exact preimage_mapFun_range_zeroSection_eq_singleton σB t.complexPoint hzB
  have hS : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) :=
    isClosed_range_zeroSection.preimage (continuous_mapFun σ)
  have hpull : (cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (TopCat.ofHom (map (K := ℂ) f)) {t.complexPoint} (2 * 1 : ℕ)).hom u =
      (cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V))
        hSP.le (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
          (thomClass R E 1)) := by
    rw [hu', pullback_hom_forget_hom, ← forget_pullback_thomClass_of_comp R σB σ hπ hF hσσ,
      ← ModuleCat.comp_apply, ← cohomologyWithSupports.forget_trans]
  -- the zero scheme `Z(σ)` is the fibre
  obtain ⟨φ, _, _, hφι, hcyc⟩ := exists_isIso_fibre_of_eq_ker f t (zeroLocus E σ) hzV n
  have hmap : TopCat.ofHom (map (K := ℂ) φ) ≫ fibreComplexPointsHom f t =
      zeroLocusHom σ ≫ borelMooreHomology.subsetInclusionOfSubset hSP.le := by
    refine ConcreteCategory.hom_ext _ _ fun p ↦ Subtype.ext ?_
    change map (K := ℂ) (fibreι f t) (map (K := ℂ) φ p) =
      map (K := ℂ) (zeroLocus E σ).subschemeι p
    refine UnderlyingSpace.ext ?_
    simp only [toHom_map, Category.assoc, hφι]
  rw [← hcyc, Chow.cycleClass_properPushforward, borelMooreHomology.pushforward_pushforward_eq_comp,
    borelMooreHomology.pushforward_apply_eq_of_hom_eq R (ModuleCat.of R R) hmap _
      ((borelMooreHomology.isProperMap_subsetInclusionOfSubset hS hSP.le).comp
        (isProperMap_zeroLocusHom σ)),
    ← borelMooreHomology.pushforward_pushforward_eq_comp R (ModuleCat.of R R) _ _
      (isProperMap_zeroLocusHom σ)
      (borelMooreHomology.isProperMap_subsetInclusionOfSubset hS hSP.le)]
  erw [hform]
  rw [pushforward_congrDegree]
  congr 1
  rw [localizedTopChernCap, borelMooreHomology.capProductSupportPullback_apply,
    borelMooreHomology.capProductSupportPullback_apply, hpull,
    borelMooreHomology.capProductSupport_forget_of_eq R _ hSP hS]

end MMP.ParameterPoint
