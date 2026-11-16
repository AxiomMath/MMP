module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksAssembly
public import MMP.AlgebraicGeometry.Chow.CycleClassDescent
public import MMP.AlgebraicGeometry.Chow.CycleClassFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowPrimeCycleTransverse
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.SubvarietyProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksChainZeroSection

/-!
# Fulton's Lemma 19.2(d) on Stacks cycles: `u_ℰ ∩ cl(π^* β) = cl_X(β)`

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X` (`MMP.Modules.totalSpace`, `MMP.Modules.proj`), zero
section `0 : X ⟶ 𝐕(ℰ)` and Thom class `u_ℰ` (`MMP.Modules.thomClass`). For every cycle `β` of
delta-dimension `m` on `X` (Stacks' cycles over `fieldChowSituation ℂ`), the cap product
`u_ℰ ∩ cl(π^* β)` of the Thom class with the cycle class of the flat pull-back `π^* β`
(Stacks 02RB), read in `H_{2m} X` through `0(X(ℂ)) ≅ X(ℂ)`, is `cl_X(β)`.

By linearity it is enough to treat the prime cycle `[x]` of a point of delta-dimension `m`. Its
flat pull-back is the cycle of the inverse image `π⁻¹(closure {x})` (Stacks 02RB), an integral
closed subscheme of dimension `m + r`, so its cycle class is the cycle class of that subvariety
(`MMP.Chow.cycleClass_cycleAssociatedToClosedSubscheme`); and the topological statement
`u_ℰ ∩ cl(E|_V) = cl_X(V)` for the subvariety `V = closure {x}` is
`MMP.Modules.zeroSectionCapFormula`.

## Main results

* `MMP.Chow.flatPullback_proj_pointCycle`: `π^*[x]_m = [π⁻¹(closure {x})]_{m+r}`.
* `MMP.Chow.thomCap_cycleClass_flatPullback_proj`: `u_ℰ ∩ cl(π^* β) = cl_X(β)` on cycles.
* `MMP.Chow.thomCap_chowCycleClass_flatPullbackChow_proj`: the same on Chow groups.
* `MMP.Chow.orientationCap_chowCycleClass_flatPullbackChow_proj`: the same for any orientation
  class of the zero section.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, Lemma 19.2(d).
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Stacks.Chow MMP.UnderlyingSpace MMP.Modules

namespace MMP.Chow

open MMP.Intersection.Scheme
open MMP.Intersection (hasDim_natCast_iff)

/-! ### Cycle classes of integral closed subschemes as cycle classes of subvarieties -/

section Subvariety

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]

open Stacks.Intersection.ReductionToDiagonal in
/-- The delta-dimension over `fieldChowSituation ℂ` of an integral closed subscheme of
dimension `n` is `n`. -/
theorem schemeDeltaDimension_subschemeι_of_natCast_eq_dimension (W : Z.IdealSheafData)
    (hW : IsIntegral W.subscheme) {n : ℕ} (hn : (n : WithBot ℕ∞) = dimension W.subscheme) :
    schemeDeltaDimension (fieldChowSituation ℂ) (W.subschemeι ≫ Z ↘ Spec (.of ℂ)) =
      ((n : ℤ) : EInt) := by
  have h := schemeDeltaDimension_integralComponentAt_eq_of_topologicalKrullDim_eq ℂ
    (Z ↘ Spec (.of ℂ)) (genericPointOf W hW) n (by
      rw [← support_eq_closure_genericPointOf W hW, ← Scheme.IdealSheafData.range_subschemeι,
        hn]
      exact (IsHomeomorph.topologicalKrullDim_eq _ (IsClosedImmersion.isClosedEmbedding
        W.subschemeι).isEmbedding.toHomeomorph.isHomeomorph).symm)
  rwa [integralComponentAt_genericPointOf W hW] at h

/-- The prime cycle of a point of delta-dimension `k` is the fundamental cycle of its closure. -/
theorem pointCycle_eq_cycleAssociatedToClosedSubscheme {k : ℤ} (x : Z)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) x = k) :
    pointCycle (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) k x hx =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ))
        (integralComponentAt x).subschemeι k := by
  rw [cycleAssociatedToClosedSubscheme_eq_pointCycle (integralComponentAt x)
    (isIntegral_integralComponentAt x)
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ _ x hx)]
  congr 1
  exact (genericPointOf_integralComponentAt x).symm

variable (R : Type) [CommRing R]

/-- The cycle class of a point `y` of delta-dimension `k` is the cycle class of any subvariety
whose ideal sheaf is the reduced closure of `y`. -/
theorem isCycleClassOf_pointCycleClass_of_integralComponentAt_eq {k : ℕ} (y : Z)
    (hy : relativeDimension (fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) y = k)
    {V : Subvariety Z} (h : integralComponentAt y = V.ideal)
    (hk : (k : WithBot ℕ∞) = dimension V.toScheme) :
    IsCycleClassOf R V.ι hk (pointCycleClass R y hy) := by
  obtain ⟨W, hW⟩ := V
  dsimp only at h
  subst h
  exact isCycleClassOf_pointCycleClass R y hy

/-- The cycle class of the fundamental cycle `[W]_k` of an integral closed subscheme of
dimension `k` is the cycle class of `W`, as a subvariety. -/
theorem isCycleClassOf_cycleClass_cycleAssociatedToClosedSubscheme (V : Subvariety Z) {k : ℕ}
    (hk : (k : WithBot ℕ∞) = dimension V.toScheme) :
    IsCycleClassOf R V.ι hk (cycleClass R k
      (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ))
        V.ideal.subschemeι k)) := by
  rw [cycleClass_cycleAssociatedToClosedSubscheme R V.ideal V.isIntegral
    (schemeDeltaDimension_subschemeι_of_natCast_eq_dimension V.ideal V.isIntegral hk)]
  exact isCycleClassOf_pointCycleClass_of_integralComponentAt_eq R _ _
    (integralComponentAt_genericPointOf V.ideal V.isIntegral) hk

/-- The cycle class is unique: two cycle classes of one subvariety agree. -/
theorem eq_of_isCycleClassOf_ι {V : Subvariety Z} {k : ℕ}
    {hk : (k : WithBot ℕ∞) = dimension V.toScheme}
    {a b : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Z)) (2 * k : ℕ)}
    (ha : IsCycleClassOf R V.ι hk a) (hb : IsCycleClassOf R V.ι hk b) : a = b :=
  IsCycleClassOf.eq (fun c c' hc hc' ↦ by
    obtain ⟨_, -, huniq, -⟩ := existsUnique_isVarietyFundamentalClass R hk
    rw [huniq c hc, huniq c' hc']) ha hb

end Subvariety

/-! ### The flat pull-back of a prime cycle to a vector bundle -/

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (E : X.Modules)
  [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

omit [X.Over (Spec (.of ℂ))] [IsComplexScheme X] in
/-- The projection of a vector bundle of rank `r` has relative dimension `r`. -/
theorem relativeDimension_proj :
    haveI := locallyOfFiniteType_proj E r
    AlgebraicGeometry.RelativeDimension (MMP.Modules.proj E) r :=
  haveI := locallyOfFiniteType_proj E r
  Stacks.Chow.relativeDimension_of_isAffineSpaceBundle (MMP.Modules.proj E) r
    (isAffineSpaceBundle_proj E r)

variable [IsComplexScheme (totalSpace E)]

variable (R : Type) [CommRing R]

/-- **Stacks 02RB for a vector bundle and a prime cycle.** The flat pull-back along
`π : 𝐕(ℰ) ⟶ X` of the prime cycle `[x]_m` of a point of delta-dimension `m` is the fundamental
cycle `[π⁻¹(closure {x})]_{m+r}` of its inverse image. -/
theorem flatPullback_proj_pointCycle {m : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = m) :
    haveI := locallyOfFiniteType_proj E r
    haveI := flat_proj E r
    flatPullback (fieldChowSituation ℂ) (totalSpace E ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))
        (MMP.Modules.proj E) rfl r (relativeDimension_proj E r) m
        (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) m x hx) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (totalSpace E ↘ Spec (.of ℂ))
        ((integralComponentAt x).comap (MMP.Modules.proj E)).subschemeι (m + r) := by
  have := locallyOfFiniteType_proj E r
  have := flat_proj E r
  rw [pointCycle_eq_cycleAssociatedToClosedSubscheme x hx]
  exact flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le _ _ _ _ _ _ _ _ _
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ _ x hx).le

omit [IsComplexScheme (totalSpace E)] in
/-- The dimension of `π⁻¹(closure {x})` for a point `x` of delta-dimension `m` is `m + r`. -/
theorem natCast_add_eq_dimension_preimageSubvariety {m : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = m) :
    ((m + r : ℕ) : WithBot ℕ∞) =
      dimension (preimageSubvariety E r (Subvariety.ofPoint x)).toScheme := by
  have hV : (Subvariety.ofPoint x).HasDim (((m + r : ℕ) : ℤ) - r) := by
    rw [show ((m + r : ℕ) : ℤ) - r = ((m : ℕ) : ℤ) by push_cast; ring]
    exact (hasDim_natCast_iff m).2 (natCast_eq_dimension_integralComponentAt x hx).symm
  exact ((hasDim_natCast_iff _).1 (hasDim_preimageSubvariety ℂ hV)).symm

/-- **Fulton's Lemma 19.2(d) for a prime cycle.** For a point `x` of delta-dimension `m`,
`u_ℰ ∩ cl(π^*[x]) = cl_X([x])` in `H_{2m} X`, read through `0(X(ℂ)) ≅ X(ℂ)`. -/
theorem thomCap_cycleClass_flatPullback_proj_pointCycle {m : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = m) :
    haveI := locallyOfFiniteType_proj E r
    haveI := flat_proj E r
    BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m r)
        (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroSectionInvHom E)
          (isProperMap_zeroSectionInvHom E) _
          (borelMooreHomology.capProductSupport R _ isClosed_range_zeroSection
            (hasProperNeighbourhoodDeformations_range_zeroSection E)
            ((2 * r : ℕ) : ℤ) ((2 * (m + r) : ℕ) : ℤ) (thomClass R E r)
            (cycleClass R (m + r)
              (flatPullback (fieldChowSituation ℂ) (totalSpace E ↘ Spec (.of ℂ))
                (X ↘ Spec (.of ℂ)) (MMP.Modules.proj E) rfl r (relativeDimension_proj E r) m
                (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) m x hx))))) =
      cycleClass R m (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) m x hx) := by
  have := locallyOfFiniteType_proj E r
  have := flat_proj E r
  have hV : (m : WithBot ℕ∞) = dimension (Subvariety.ofPoint x).toScheme :=
    natCast_eq_dimension_integralComponentAt x hx
  have hW := natCast_add_eq_dimension_preimageSubvariety E r x hx
  have hcl : IsCycleClassOf R (preimageSubvariety E r (Subvariety.ofPoint x)).ι hW
      (cycleClass R (m + r) (flatPullback (fieldChowSituation ℂ) (totalSpace E ↘ Spec (.of ℂ))
        (X ↘ Spec (.of ℂ)) (MMP.Modules.proj E) rfl r (relativeDimension_proj E r) m
        (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) m x hx))) := by
    rw [flatPullback_proj_pointCycle E r x hx]
    exact isCycleClassOf_cycleClass_cycleAssociatedToClosedSubscheme R _ hW
  refine eq_of_isCycleClassOf_ι R
    (isCycleClass_pushforward_capProductSupport_of_zeroSectionCapFormula E R r _
      (zeroSectionCapFormula E r _ R hV hW) hcl) ?_
  rw [cycleClass_pointCycle]
  exact isCycleClassOf_pointCycleClass_of_integralComponentAt_eq R x hx rfl hV

/-- **Fulton's Lemma 19.2(d) on Stacks cycles.** Let `ℰ` be finite locally free of rank `r` on
a complex scheme `X`, with vector bundle `π : 𝐕(ℰ) ⟶ X` and Thom class `u_ℰ`. For every cycle
`β` of delta-dimension `m` on `X`, the cap product `u_ℰ ∩ cl(π^* β) ∈ H_{2m}(0(X(ℂ)))`, read in
`H_{2m} X` through `0(X(ℂ)) ≅ X(ℂ)`, is `cl_X(β)`; `π^*` is Stacks' flat pull-back of cycles
(Stacks 02RB). -/
theorem thomCap_cycleClass_flatPullback_proj {m : ℕ}
    (β : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) m) :
    haveI := locallyOfFiniteType_proj E r
    haveI := flat_proj E r
    BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m r)
        (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroSectionInvHom E)
          (isProperMap_zeroSectionInvHom E) _
          (borelMooreHomology.capProductSupport R _ isClosed_range_zeroSection
            (hasProperNeighbourhoodDeformations_range_zeroSection E)
            ((2 * r : ℕ) : ℤ) ((2 * (m + r) : ℕ) : ℤ) (thomClass R E r)
            (cycleClass R (m + r)
              (flatPullback (fieldChowSituation ℂ) (totalSpace E ↘ Spec (.of ℂ))
                (X ↘ Spec (.of ℂ)) (MMP.Modules.proj E) rfl r (relativeDimension_proj E r) m
                β)))) =
      cycleClass R m β := by
  have := locallyOfFiniteType_proj E r
  have := flat_proj E r
  conv_lhs => rw [eq_sum_pointCycleOrZero β]
  conv_rhs => rw [eq_sum_pointCycleOrZero β]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hxm : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x =
      m :=
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation ℂ) _ m β.1).mp β.2 x
      ((finite_support_cycle β).mem_toFinset.mp hx)
  rw [pointCycleOrZero, dif_pos hxm, thomCap_cycleClass_flatPullback_proj_pointCycle E r R x hxm]

/-- **Fulton's Lemma 19.2(d) on Stacks' Chow groups.** For every class `a ∈ A_m(X)`,
`u_ℰ ∩ cl(π^* a) = cl_X(a)` in `H_{2m} X`, read through `0(X(ℂ)) ≅ X(ℂ)`; `π^*` is Stacks' flat
pull-back on Chow groups (Stacks 0FVK), with Stacks 02S1 discharged
(`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`). -/
theorem thomCap_chowCycleClass_flatPullbackChow_proj {m : ℕ}
    (a : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) m) :
    haveI := locallyOfFiniteType_proj E r
    haveI := flat_proj E r
    BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m r)
        (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroSectionInvHom E)
          (isProperMap_zeroSectionInvHom E) _
          (borelMooreHomology.capProductSupport R _ isClosed_range_zeroSection
            (hasProperNeighbourhoodDeformations_range_zeroSection E)
            ((2 * r : ℕ) : ℤ) ((2 * (m + r) : ℕ) : ℤ) (thomClass R E r)
            (chowCycleClass R (m + r)
              (flatPullbackChow (fieldChowSituation ℂ) (totalSpace E ↘ Spec (.of ℂ))
                (X ↘ Spec (.of ℂ)) (MMP.Modules.proj E) rfl r (relativeDimension_proj E r) m
                (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) a)))) =
      chowCycleClass R m a := by
  induction a using QuotientAddGroup.induction_on with
  | H β => exact thomCap_cycleClass_flatPullback_proj E r R β

/-- **Fulton's Lemma 19.2(d) on Stacks' Chow groups, for an orientation class of the zero
section.** If `u ∈ H^{2r}(𝐕(ℰ), 𝐕(ℰ) - 0(X))` is an orientation class of the zero section
`0 : X → 𝐕(ℰ)` (Fulton §19.2), then `u ∩ cl(π^* a) = cl_X(a)` for every `a ∈ A_m(X)`. -/
theorem orientationCap_chowCycleClass_flatPullbackChow_proj {m : ℕ}
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
      (range (UnderlyingSpace.map (zeroSection E))) (2 * r : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R (zeroSection E) r u)
    (a : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) m) :
    haveI := locallyOfFiniteType_proj E r
    haveI := flat_proj E r
    BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m r)
        (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroSectionInvHom E)
          (isProperMap_zeroSectionInvHom E) _
          (borelMooreHomology.capProductSupport R _ isClosed_range_zeroSection
            (hasProperNeighbourhoodDeformations_range_zeroSection E)
            ((2 * r : ℕ) : ℤ) ((2 * (m + r) : ℕ) : ℤ) u
            (chowCycleClass R (m + r)
              (flatPullbackChow (fieldChowSituation ℂ) (totalSpace E ↘ Spec (.of ℂ))
                (X ↘ Spec (.of ℂ)) (MMP.Modules.proj E) rfl r (relativeDimension_proj E r) m
                (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) a)))) =
      chowCycleClass R m a := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  obtain rfl := MMP.Modules.eq_thomClass_of_isRegularImbeddingOrientationClass E r R hu
  exact thomCap_chowCycleClass_flatPullbackChow_proj E r R a

end MMP.Chow
