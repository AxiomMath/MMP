module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalization
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.HomotopyPointGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.CupCompositeGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksHomotopyInfra
public import MMP.AlgebraicGeometry.CycleMap.Stacks.AlgebraicEquivalence.PointSection
public import MMP.AlgebraicGeometry.RegularImmersion.CodimOne
public import MMP.AlgebraicGeometry.Variety.ParameterPoint
public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import MMP.AlgebraicGeometry.Analytic.DivisorOrientationDatum
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PointsOver
public import MMP.AlgebraicTopology.BorelMoore.Suspension
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionNormalize
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple

/-!
# Fulton's Lemma 19.1.3 at a fibre, for the cycle class of a point

Let `g : G → B` be a morphism from a complex scheme to a smooth complex curve, `x ∈ G` a point
of delta-dimension `n + 1` whose closure `V = closure {x}` dominates `B`, and `s ∈ B` a parameter
point, with complex point `p ∈ B(ℂ)` and local orientation class `u ∈ H²(B, B - p)`. Then

  `g^* u ∩ cl_G(x) = cl([V_s]_n)`  in `H_{2n}(g⁻¹ p)`,

where `cl_G(x)` is the cycle class of `x` (`MMP.Chow.pointCycleClass`), `[V_s]_n` Stacks' cycle of
the scheme-theoretic fibre `V_s` (Tag 02QU) and `cl` the cycle class map on Stacks cycles
(`MMP.Chow.cycleClass`), read in `g⁻¹ p` along `V_s(ℂ) → g⁻¹(p)`
(`MMP.Chow.pushforward_cycleClass_fibre_eq_capProductSupportPullback_pointCycleClass`).

The fibre `V_s` is the zero scheme of the pull-back `f^* σ` along `f : V → B` of the canonical
section `σ` of `𝒪_B(s)`, a section of a line bundle cutting out the reduced point `s`; so Fulton's
Lemma 19.1.3 for the section `f^* σ` on Stacks bundles and cycles
(`MMP.Modules.LocalizedFirstChernFormula.of_proper_birational`,
`MMP.Modules.LocalizedFirstChernFormula.of_isNormal`) gives the formula on `V` (Fulton, proof of
Lemma 19.1.3: "apply [the lemma for line bundles] to `X`, `f^* L`, `f^* s_t`"), and the projection
formula carries it to `G`.

## Main results

* `MMP.Chow.pushforward_cycleClass_fibre_eq_capProductSupportPullback_pointCycleClass`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Stacks.Chow
open MMP.UnderlyingSpace

section SubschemeOverScope

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
private theorem properPushforward_zeroLocusSubschemeMap_of_zeroLocus_eq {k : ℕ}
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
private theorem localizedFirstChernFormula_of_zeroLocus_eq [IsIntegral X] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X) {E : X.Modules}
    [E.IsQuasicoherent]
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

/-! ### The specialization formula at a fibre -/

namespace MMP.Chow

open MMP MMP.Modules MMP.ParameterPoint AlgebraicGeometry.SheafOfModules

/-- The scheme-theoretic fibre of a morphism from a complex scheme is a complex scheme. -/
private instance isComplexScheme_fibre' {V T : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] (f : V ⟶ T) (t : ParameterPoint T) : IsComplexScheme (fibre f t) :=
  IsComplexScheme.of_isClosedImmersion (fibreι f t)

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

/-- A complex point `p` lying over a parameter point `t` cuts out the same closed subscheme of
`B` as `t`. -/
private lemma ker_toHom_of_toHom_closedPoint_eq (t : ParameterPoint B) (p : UnderlyingSpace ℂ B)
    (hp : p.toHom (IsLocalRing.closedPoint ℂ) = t.point) : p.toHom.ker = t.ι.ker := by
  refine ker_eq_ker_of_range_eq _ _ ?_
  rw [range_ι]
  ext x
  simp only [mem_range, mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint ℂ), hp]
  · rintro rfl
    exact ⟨_, hp⟩

/-- The fibre of `f(ℂ) : V(ℂ) → B(ℂ)` over a complex point `p` is the set of complex points of
`V` over the scheme-theoretic fibre `f⁻¹(p)`. -/
private lemma preimage_map_singleton' {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] (f : V ⟶ B)
    [f.IsOver (Spec (.of ℂ))] (p : UnderlyingSpace ℂ B) :
    map (K := ℂ) f ⁻¹' {p} = pointsOver (f.base ⁻¹' {p.toHom (IsLocalRing.closedPoint ℂ)}) := by
  ext q
  simp only [mem_preimage, mem_singleton_iff, mem_pointsOver]
  rw [← (equivClosedPoints (K := ℂ) B).injective.eq_iff, ← Subtype.coe_inj,
    equivClosedPoints_apply, equivClosedPoints_apply]
  rfl

/-- `f⁻¹(p) ⊆ V(ℂ)` has arbitrarily small proper neighbourhood deformations. -/
private lemma hasProperNeighbourhoodDeformations_preimage_singleton' {V : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [IsComplexScheme V] (f : V ⟶ B) [f.IsOver (Spec (.of ℂ))]
    (p : UnderlyingSpace ℂ B) :
    HasProperNeighbourhoodDeformations ((TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {p}) := by
  change HasProperNeighbourhoodDeformations (map (K := ℂ) f ⁻¹' {p})
  rw [preimage_map_singleton']
  exact hasProperNeighbourhoodDeformations_pointsOver V
    ⟨_, (equivClosedPoints (K := ℂ) B p).2.preimage f.base.hom.continuous⟩

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

/-- **Changing the support to an equal set.** For `Z = Z'`, the cap product with
`c ∈ H^j(Y, Y - Z)` viewed in `H^j(Y, Y - Z')` is the cap product with `c` transported along
`Z ⊆ Z'`. -/
private lemma capProductSupport_forget_of_eq' (R : Type) [CommRing R] (Y : TopCat.{0})
    {Z Z' : Set Y} (h : Z = Z') (hZ : IsClosed Z) (hZ' : IsClosed Z')
    (hZd : HasProperNeighbourhoodDeformations Z)
    (hZ'd : HasProperNeighbourhoodDeformations Z') (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y Z j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    borelMooreHomology.capProductSupport R Y hZ' hZ'd j k
        ((cohomologyWithSupports.forget R (ModuleCat.of R R) Y h.le j).hom c) a =
      (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (borelMooreHomology.subsetInclusionOfSubset h.le)
        (borelMooreHomology.isProperMap_subsetInclusionOfSubset hZ h.le) (k - j)).hom
        (borelMooreHomology.capProductSupport R Y hZ hZd j k c a) := by
  subst h
  have e : borelMooreHomology.subsetInclusionOfSubset (le_refl Z) = 𝟙 (TopCat.of Z) := rfl
  rw [show cohomologyWithSupports.forget R (ModuleCat.of R R) Y (le_refl Z) j = 𝟙 _ from
      cohomologyWithSupports.forget_refl R _ Y Z j,
    borelMooreHomology.pushforward_congr' R e _ (by simpa using isProperMap_id),
    borelMooreHomology.pushforward_id]
  rfl

/-- `j = j'` transports commute with push-forward. -/
private lemma pushforward_congrDegree' (R : Type) [CommRing R] {Y Z : TopCat.{0}} (g : Y ⟶ Z)
    (hg : IsProperMap g) {j j' : ℤ} (h : j = j')
    (x : borelMooreHomology R (ModuleCat.of R R) Y j) :
    (borelMooreHomology.pushforward R (ModuleCat.of R R) g hg j').hom
        (BorelMooreCross.congrDegree R Y h x) =
      BorelMooreCross.congrDegree R Z h
        ((borelMooreHomology.pushforward R (ModuleCat.of R R) g hg j).hom x) := by
  subst h
  rfl

/-- **Projection formula along a composite**, for any map `ρ : F⁻¹ Z → g⁻¹ Z` restricting a
proper `ι` with `ι ≫ g = F`: `ρ_*(F^* c ∩ a) = g^* c ∩ ι_* a`. -/
private lemma pushforward_capProductSupportPullback_of_comp_eq' (R : Type) [CommRing R]
    {C N' N : TopCat.{0}} (ι : C ⟶ N') (hι : IsProperMap ι) (g : N' ⟶ N) (F : C ⟶ N)
    (hF : ι ≫ g = F) {Z : Set N} (hZ : IsClosed Z)
    (hd : HasProperNeighbourhoodDeformations (g ⁻¹' Z))
    (hd' : HasProperNeighbourhoodDeformations (F ⁻¹' Z))
    (ρ : TopCat.of (F ⁻¹' Z) ⟶ TopCat.of (g ⁻¹' Z)) (hρ : ∀ x, (ρ x).1 = ι x.1)
    (hρp : IsProperMap ρ) (j k : ℤ) (c : cohomologyWithSupports R (ModuleCat.of R R) N Z j)
    (a : borelMooreHomology R (ModuleCat.of R R) C k) :
    (borelMooreHomology.pushforward R (ModuleCat.of R R) ρ hρp (k - j)).hom
        (borelMooreHomology.capProductSupportPullback R F hZ hd' j k c a) =
      borelMooreHomology.capProductSupportPullback R g hZ hd j k c
        ((borelMooreHomology.pushforward R (ModuleCat.of R R) ι hι k).hom a) := by
  subst hF
  obtain rfl : ρ = TopCat.ofHom (ι.hom.restrictPreimage (g ⁻¹' Z)) := by
    ext q
    exact hρ q
  rw [borelMooreHomology.capProductSupportPullback_apply R (ι ≫ g),
    cohomologyWithSupports.pullback_comp]
  exact borelMooreHomology.pushforward_restrictPreimage_capProductSupportPullback R ι hι
    (hZ.preimage g.hom.continuous) hd hd' j k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g Z j).hom c) a

/-- The fibre of a dominant morphism to a smooth curve over a parameter point is not all of the
source: its ideal sheaf is not `⊥`. -/
private lemma ker_fibreι_ne_bot (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ)))
    {V : Scheme.{0}} (f : V ⟶ B) [IsDominant f] (t : ParameterPoint B) :
    (fibreι f t).ker ≠ ⊥ := by
  intro hbot
  have hsupp := Scheme.Hom.support_ker (fibreι f t)
  rw [hbot, Scheme.IdealSheafData.support_bot, range_fibreι,
    ((isClosed_point t).preimage f.continuous).closure_eq] at hsupp
  have hrange : range f ⊆ {t.point} := by
    rintro _ ⟨x, rfl⟩
    change x ∈ f ⁻¹' {t.point}
    rw [← hsupp]
    trivial
  have huniv : ({t.point} : Set B) = univ := by
    have := closure_mono hrange
    rw [f.denseRange.closure_range, (isClosed_point t).closure_eq] at this
    exact univ_subset_iff.mp this
  haveI : Subsingleton B := ⟨fun a b ↦ by
    have ha : a ∈ ({t.point} : Set B) := huniv ▸ mem_univ a
    have hb : b ∈ ({t.point} : Set B) := huniv ▸ mem_univ b
    rw [mem_singleton_iff] at ha hb
    rw [ha, hb]⟩
  haveI : Nonempty B := ⟨t.point⟩
  have h1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := ℂ) (X := B) 1
  rw [topologicalKrullDim_eq_zero_of_discreteTopology_nonempty] at h1
  exact absurd h1 (by norm_num)

/-- The ideal of the fibre `V_t` is the pull-back of the ideal of the point `t`. -/
private lemma ker_fibreι_eq_comap {V : Scheme.{0}} (f : V ⟶ B) (t : ParameterPoint B) :
    (fibreι f t).ker = t.ι.ker.comap f := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (isPullback_fibre f t).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

variable (R : Type) [CommRing R]

/-- Fulton's Lemma 19.1.3 at a fibre, from a section `σ` of a line bundle on `V` cutting out the
fibre `V_t`, with `σ⁻¹(0) = f⁻¹ p`, `f^* u = σ^*(u_ℰ)` and the localized first Chern formula
for `σ`: then `f^* u ∩ cl(V) = cl([V_t]_n)` in `H_{2n}(f⁻¹ p)`. -/
private theorem pushforward_cycleClass_fibre_eq_of_zeroLocus_eq {V : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V] (f : V ⟶ B)
    [f.IsOver (Spec (.of ℂ))]
    {n : ℕ} (hn : ((n + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V) (t : ParameterPoint B)
    (p : UnderlyingSpace ℂ B)
    (hd : HasProperNeighbourhoodDeformations ((TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {p}))
    (ψ : TopCat.of (UnderlyingSpace ℂ (fibre f t)) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {p}))
    (hψ : ∀ q, (ψ q).1 = map (K := ℂ) (fibreι f t) q) (hψp : IsProperMap ψ)
    {E : V.Modules} [E.IsQuasicoherent] [IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    {σ : V ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))] (hzV : zeroLocus E σ = (fibreι f t).ker)
    (hSP : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) =
      (TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {p})
    (hform : LocalizedFirstChernFormula R hn E σ)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {p} (2 * 1 : ℕ)}
    (hpull : (cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (TopCat.ofHom (map (K := ℂ) f)) {p} (2 * 1 : ℕ)).hom u =
      (cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V))
        hSP.le (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
          (thomClass R E 1)))
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V))
      (2 * (n + 1) : ℕ)}
    (hμ : IsVarietyFundamentalClass R hn μ) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) ψ hψp (2 * n : ℕ)
        (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (fibre f t ↘ Spec (.of ℂ)) (𝟙 _) n)) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        (borelMooreHomology.capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) f))
          isClosed_singleton hd (2 * 1 : ℕ) (2 * (n + 1) : ℕ) u μ) := by
  have hS : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) :=
    isClosed_range_zeroSection.preimage (continuous_mapFun σ)
  let φ : (zeroLocus E σ).subscheme ⟶ fibre f t :=
    Scheme.IdealSheafData.inclusion hzV.ge ≫ inv (fibreι f t).toImage
  have hφι : φ ≫ fibreι f t = (zeroLocus E σ).subschemeι := by
    have e : inv (fibreι f t).toImage ≫ fibreι f t = (fibreι f t).imageι := by
      rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
    simp only [φ, Category.assoc, e]
    exact Scheme.IdealSheafData.inclusion_subschemeι _
  haveI : IsIso φ := by
    haveI := Stacks.Chow.TensorZeroScheme.isIso_inclusion_of_eq hzV.symm
    infer_instance
  haveI : φ.IsOver (Spec (.of ℂ)) := ⟨by
    change φ ≫ fibreι f t ≫ V ↘ Spec (.of ℂ) =
      (zeroLocus E σ).subschemeι ≫ V ↘ Spec (.of ℂ)
    rw [← Category.assoc, hφι]⟩
  have hcyc : properPushforward (fieldChowSituation ℂ) _ (fibre f t ↘ Spec (.of ℂ)) φ
      (comp_over φ _) n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) n) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (fibre f t ↘ Spec (.of ℂ))
        (𝟙 _) n := by
    rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
    exact cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso φ) (by simp) _
  have hmap : TopCat.ofHom (map (K := ℂ) φ) ≫ ψ =
      zeroLocusHom σ ≫ borelMooreHomology.subsetInclusionOfSubset hSP.le := by
    refine ConcreteCategory.hom_ext _ _ fun q ↦ Subtype.ext ?_
    change (ψ (map (K := ℂ) φ q)).1 = map (K := ℂ) (zeroLocus E σ).subschemeι q
    rw [hψ]
    refine UnderlyingSpace.ext ?_
    simp only [toHom_map, Category.assoc, hφι]
  rw [← hcyc, Chow.cycleClass_properPushforward,
    borelMooreHomology.pushforward_pushforward_eq_comp,
    borelMooreHomology.pushforward_apply_eq_of_hom_eq R (ModuleCat.of R R) hmap _
      ((borelMooreHomology.isProperMap_subsetInclusionOfSubset hS hSP.le).comp
        (isProperMap_zeroLocusHom σ)),
    ← borelMooreHomology.pushforward_pushforward_eq_comp R (ModuleCat.of R R) _ _
      (isProperMap_zeroLocusHom σ)
      (borelMooreHomology.isProperMap_subsetInclusionOfSubset hS hSP.le)]
  erw [hform μ hμ]
  rw [pushforward_congrDegree']
  congr 1
  rw [localizedTopChernCap, borelMooreHomology.capProductSupportPullback_apply,
    borelMooreHomology.capProductSupportPullback_apply, hpull,
    capProductSupport_forget_of_eq' R _ hSP hS]

/-- **Fulton's Lemma 19.1.3 at a fibre, on a variety.** For a dominant `f : V → B` from a complex
variety of dimension `n + 1`, a parameter point `t` with complex point `p` and the local
orientation class `u` of `B(ℂ)` at `p`: `f^* u ∩ cl(V) = cl([V_t]_n)` in `H_{2n}(f⁻¹ p)`, for
every fundamental class `cl(V)` and every map `ψ : V_t(ℂ) → f⁻¹(p)` restricting `V_t → V`. -/
private theorem pushforward_cycleClass_fibre_eq_capProductSupportPullback_aux
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))) {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] [IsIntegral V] (f : V ⟶ B)
    [f.IsOver (Spec (.of ℂ))] [IsDominant f]
    {n : ℕ} (hn : ((n + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V) (t : ParameterPoint B)
    (p : UnderlyingSpace ℂ B) (hp : p.toHom (IsLocalRing.closedPoint ℂ) = t.point)
    (hd : HasProperNeighbourhoodDeformations ((TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {p}))
    (ψ : TopCat.of (UnderlyingSpace ℂ (fibre f t)) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {p}))
    (hψ : ∀ q, (ψ q).1 = map (K := ℂ) (fibreι f t) q) (hψp : IsProperMap ψ)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {p} (2 * 1 : ℕ)}
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis p u)
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V))
      (2 * (n + 1) : ℕ)}
    (hμ : IsVarietyFundamentalClass R hn μ) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) ψ hψp (2 * n : ℕ)
        (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (fibre f t ↘ Spec (.of ℂ)) (𝟙 _) n)) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        (borelMooreHomology.capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) f))
          isClosed_singleton hd (2 * 1 : ℕ) (2 * (n + 1) : ℕ) u μ) := by
  have hDt := ker_toHom_of_toHom_closedPoint_eq t p hp
  haveI hD : Stacks.Divisors.IsEffectiveCartierDivisor t.ι.ker :=
    hDt ▸ isEffectiveCartierDivisor_ker_of_isRegularClosedImmersionOfCodim_one _
      (UnderlyingSpace.isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hB p)
  set D := t.ι.ker
  set L := Stacks.Divisors.divisorSheaf D
  set sD := Stacks.Divisors.divisorSheafGlobalSection D
  set EB := MMP.Topology.divisorDualSheaf D
  set σB := MMP.Topology.canonicalSectionMap D
  have hσB : σB ≫ proj EB = 𝟙 B := MMP.Topology.canonicalSectionMap_proj D
  have hzB : zeroLocus EB σB = p.toHom.ker :=
    (MMP.Topology.zeroLocus_canonicalSectionMap D).trans hDt.symm
  have hu' := IsLocalOrientationClass.eq (by norm_num) hu
    (Modules.isLocalOrientationClass_forget_pullback_thomClass p R hB hσB hzB)
  set E := (Scheme.Modules.pullback f).obj EB
  set σ := pullbackSectionMap f hσB
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
  have hs : pullbackGlobalSections f L sD ≠ 0 := fun h ↦ hne (hzV'.trans (by
    rw [h, Stacks.Divisors.zeroScheme_zero_eq_bot]))
  have hπ := baseChangeMap_proj f EB
  have hF := isFibrewiseIso_baseChangeMap f EB 1
  have hσσ := pullbackSectionMap_baseChangeMap f hσB
  refine pushforward_cycleClass_fibre_eq_of_zeroLocus_eq R f hn t p hd ψ hψ hψp hzV ?_
    (Modules.localizedFirstChernFormula_of_zeroLocus_eq R hn (pullbackSectionMap_proj f hσB) h0
      _ _ hs hzV') ?_ hμ
  · rw [preimage_zeroLocus_of_comp σB σ hπ hF hσσ]
    congr 1
    exact Modules.preimage_mapFun_range_zeroSection_eq_singleton σB p hzB
  · rw [hu', pullback_hom_forget_hom, ← forget_pullback_thomClass_of_comp R σB σ hπ hF hσσ,
      ← ModuleCat.comp_apply, ← cohomologyWithSupports.forget_trans]

end MMP.Chow

end SubschemeOverScope

namespace MMP.Chow

open MMP MMP.ParameterPoint

variable {B : Scheme.{0}} [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))]
  (R : Type) [CommRing R]
variable {G : Scheme.{0}} [G.Over (Spec (.of ℂ))] [IsComplexScheme G]

/-- Fulton's Lemma 19.1.3 at a fibre, for a complex variety `V` with a closed immersion
`ι : V → G`: `g^* u ∩ ι_* cl(V) = cl([V_s]_n)` in `H_{2n}(g⁻¹ p)`. -/
private theorem pushforward_cycleClass_fibre_eq_capProductSupportPullback_pushforward
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))) {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] [IsIntegral V] (ι : V ⟶ G)
    [IsClosedImmersion ι]
    [ι.IsOver (Spec (.of ℂ))] (g : G ⟶ B) [g.IsOver (Spec (.of ℂ))] [IsDominant (ι ≫ g)]
    {n : ℕ} (hn : ((n + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V) (s : ParameterPoint B)
    (p : UnderlyingSpace ℂ B) (hp : p.toHom (IsLocalRing.closedPoint ℂ) = s.point)
    (hd : HasProperNeighbourhoodDeformations ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {p}))
    (φ : TopCat.of (UnderlyingSpace ℂ (fibre (ι ≫ g) s)) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {p}))
    (hφ : ∀ q, (φ q).1 = map (K := ℂ) ι (map (K := ℂ) (fibreι (ι ≫ g) s) q))
    (hφp : IsProperMap φ)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {p} (2 * 1 : ℕ)}
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis p u)
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V))
      (2 * (n + 1) : ℕ)}
    (hμ : IsVarietyFundamentalClass R hn μ) :
    (borelMooreHomology.pushforward R (ModuleCat.of R R) φ hφp (2 * n : ℕ)).hom
        (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (fibre (ι ≫ g) s ↘ Spec (.of ℂ)) (𝟙 _) n)) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        (borelMooreHomology.capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) g))
          isClosed_singleton hd (2 * 1 : ℕ) (2 * (n + 1) : ℕ) u
          ((borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) ι))
            (isProperMap_map (K := ℂ) ι) (2 * (n + 1) : ℕ)).hom μ)) := by
  have hF : TopCat.ofHom (map (K := ℂ) ι) ≫ TopCat.ofHom (map (K := ℂ) g) =
      TopCat.ofHom (map (K := ℂ) (ι ≫ g)) :=
    ConcreteCategory.hom_ext _ _ fun q ↦ UnderlyingSpace.ext (Category.assoc _ _ _)
  have hmemψ : ∀ q : UnderlyingSpace ℂ (fibre (ι ≫ g) s),
      map (K := ℂ) (fibreι (ι ≫ g) s) q ∈
        (TopCat.ofHom (map (K := ℂ) (ι ≫ g))).hom ⁻¹' {p} := fun q ↦ by
    have h : map (K := ℂ) g (φ q).1 = p := (φ q).2
    rw [hφ q] at h
    change map (K := ℂ) (ι ≫ g) (map (K := ℂ) (fibreι (ι ≫ g) s) q) = p
    rw [← h]
    exact DFunLike.congr_fun (map_comp ι g) _
  let ψ : TopCat.of (UnderlyingSpace ℂ (fibre (ι ≫ g) s)) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) (ι ≫ g))).hom ⁻¹' {p}) :=
    TopCat.ofHom ⟨fun q ↦ ⟨map (K := ℂ) (fibreι (ι ≫ g) s) q, hmemψ q⟩,
      (map (K := ℂ) (fibreι (ι ≫ g) s)).continuous.subtype_mk _⟩
  have hψp : IsProperMap ψ :=
    (Topology.IsClosedEmbedding.of_comp (f := ψ) Topology.IsEmbedding.subtypeVal
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (fibreι (ι ≫ g) s))).isProperMap
  have hmemρ : ∀ r : (TopCat.ofHom (map (K := ℂ) (ι ≫ g))).hom ⁻¹' {p},
      map (K := ℂ) ι r.1 ∈ (TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {p} := fun r ↦ by
    have h : map (K := ℂ) (ι ≫ g) r.1 = p := r.2
    rw [DFunLike.congr_fun (map_comp ι g) r.1] at h
    exact h
  let ρ : TopCat.of ((TopCat.ofHom (map (K := ℂ) (ι ≫ g))).hom ⁻¹' {p}) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {p}) :=
    TopCat.ofHom ⟨fun r ↦ ⟨map (K := ℂ) ι r.1, hmemρ r⟩,
      ((map (K := ℂ) ι).continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hρp : IsProperMap ρ :=
    (Topology.IsClosedEmbedding.of_comp (f := ρ) Topology.IsEmbedding.subtypeVal
      ((isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) ι).comp
        (Topology.IsClosedEmbedding.subtypeVal
          (isClosed_singleton.preimage (map (K := ℂ) (ι ≫ g)).continuous)))).isProperMap
  have hφψ : φ = ψ ≫ ρ :=
    ConcreteCategory.hom_ext _ _ fun q ↦ Subtype.ext (hφ q)
  have h₁ := pushforward_cycleClass_fibre_eq_capProductSupportPullback_aux R hB (ι ≫ g) hn s p
    hp (hasProperNeighbourhoodDeformations_preimage_singleton' (ι ≫ g) p) ψ (fun _ ↦ rfl) hψp
    hu hμ
  rw [borelMooreHomology.pushforward_apply_eq_of_hom_eq R (ModuleCat.of R R) hφψ hφp
      (hρp.comp hψp),
    ← borelMooreHomology.pushforward_pushforward_eq_comp R (ModuleCat.of R R) _ _ hψp hρp]
  erw [h₁]
  rw [pushforward_congrDegree']
  congr 1
  exact pushforward_capProductSupportPullback_of_comp_eq' R _ (isProperMap_map (K := ℂ) ι) _ _
    hF isClosed_singleton hd _ ρ (fun _ ↦ rfl) hρp _ _ u _

/-- **Fulton's Lemma 19.1.3 at a fibre, for the cycle class of a point** (Fulton, §19.1). Let
`g : G → B` be a morphism from a complex scheme to a smooth complex curve, `x ∈ G` a point of
delta-dimension `n + 1` whose closure `V = closure {x}` dominates `B`, `s ∈ B` a parameter point
lying under the complex point `p ∈ B(ℂ)`, and `u ∈ H²(B, B - p)` the local orientation class of
`B(ℂ)` at `p`. Then the class of Stacks' cycle `[V_s]_n` of the scheme-theoretic fibre `V_s`,
read in `g⁻¹(p) ⊆ G(ℂ)` along any map `φ : V_s(ℂ) → g⁻¹(p)` restricting `V_s → G`, is
`g^* u ∩ cl_G(x)`. -/
theorem pushforward_cycleClass_fibre_eq_capProductSupportPullback_pointCycleClass
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))) (g : G ⟶ B) [g.IsOver (Spec (.of ℂ))]
    {n : ℕ} (x : G)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (G ↘ Spec (.of ℂ)) x =
      ((n + 1 : ℕ) : ℤ))
    [IsDominant ((integralComponentAt x).subschemeι ≫ g)] (s : ParameterPoint B)
    [IsComplexScheme (fibre ((integralComponentAt x).subschemeι ≫ g) s)]
    (p : UnderlyingSpace ℂ B) (hp : p.toHom (IsLocalRing.closedPoint ℂ) = s.point)
    (hd : HasProperNeighbourhoodDeformations ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {p}))
    (φ : TopCat.of (UnderlyingSpace ℂ (fibre ((integralComponentAt x).subschemeι ≫ g) s)) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {p}))
    (hφ : ∀ q, (φ q).1 = map (K := ℂ) (integralComponentAt x).subschemeι
      (map (K := ℂ) (fibreι ((integralComponentAt x).subschemeι ≫ g) s) q))
    (hφp : IsProperMap φ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ B))
      {p} (2 * 1 : ℕ))
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) R
      curveOrientationBasis p u) :
    (borelMooreHomology.pushforward R (ModuleCat.of R R) φ hφp (2 * n : ℕ)).hom
        (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (fibre ((integralComponentAt x).subschemeι ≫ g) s ↘ Spec (.of ℂ)) (𝟙 _) n)) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring)
        (borelMooreHomology.capProductSupportPullback R (TopCat.ofHom (map (K := ℂ) g))
          isClosed_singleton hd (2 * 1 : ℕ) (2 * (n + 1) : ℕ) u (Chow.pointCycleClass R x hx)) :=
  pushforward_cycleClass_fibre_eq_capProductSupportPullback_pushforward R hB _ g
    (natCast_eq_dimension_integralComponentAt x hx) s p hp hd φ hφ hφp hu
    (existsUnique_isVarietyFundamentalClass R
      (natCast_eq_dimension_integralComponentAt x hx)).choose_spec.1

end MMP.Chow
