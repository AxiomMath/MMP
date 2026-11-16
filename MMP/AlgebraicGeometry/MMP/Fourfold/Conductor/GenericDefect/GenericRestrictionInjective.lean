module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreCycle

/-!
# Injectivity of the generic restriction of the algebraic defect

Let `r : Z ⟶ Y` be a curve-and-point exceptional model with exceptional divisor `F = ∑ Fᵢ`, and
let `Φ : K(r)/B(r) → ⨁_T (𝒱_T^*)^{π₁(T°)}` be the map of generic restrictions: `Φ [x]` pairs a
germ of `𝒲_t` with the sum `w_T(t)` of the fundamental classes of the curves `Lᵢ ∩ F_t`, for a
divisor representative `(Lᵢ)` of `x` and a general point `t` of `T°`.

If `Φ [x] = 0`, then `w_T(t)` pairs to zero with every class restricted to `F_t` from a
neighbourhood of `F_t`. Such restrictions detect `H₂(F_t, ℚ)` (proper base change and the
universal coefficient theorem), so `w_T(t) = 0` for all but finitely many `t`; the fibre cycle
`∑ᵢ ∑_P cₚ [P ×_Y t]` then has zero class on a dense open of each curve `T`. The kernel step
(the Hodge index argument on the components) puts the class tuple of `(Lᵢ)` in `B(r)`, that is
`[x] = 0`.

## Main results

* `MMP.Fourfold.IsCurvePointExceptionalModel.injective_curveLocalSystemDual`: `Φ` is injective.

## Implementation notes

* The target of `Φ` is any submodule `M` of the families of forms on the stalks of `𝒱_T`; only
  the pairing property of `Φ` is used, so `M` may be the space of monodromy-invariant forms of
  `MMP.Fourfold.IsCurvePointExceptionalModel.exists_linearMap_curveLocalSystemDual`.
* The kernel step enters as the hypothesis `hkernel`. Two topological inputs enter as the
  hypotheses `hdetect` (classes restricted from neighbourhoods of `F_t` detect `H₂(F_t, ℚ)`)
  and `hcycle` (for general `t`, the class of the fibre cycle of `(Lᵢ)` over `t` is the sum of
  the fundamental classes of the components of the curves `Lᵢ ∩ F_t`, so it vanishes on a dense
  open of `T` once these sums vanish at all but finitely many `t`).

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MMP
open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open scoped MMP.SubschemeOver TensorProduct

namespace MMP.Fourfold

/-- The push-forward of Borel–Moore homology along the homeomorphism `X^an ≃ X(ℂ)` is injective. -/
private theorem pushforward_homeomorphUnderlyingSpace_injective {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] (n : ℕ) :
    Function.Injective (MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace (X := X).symm.continuous⟩)
      ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap n).hom := by
  intro a b hab
  let e := ComplexPoints.homeomorphUnderlyingSpace (X := X)
  let g : TopCat.of (ComplexPoints (X ↘ Spec (.of ℂ))) ⟶ TopCat.of (UnderlyingSpace ℂ X) :=
    TopCat.ofHom ⟨e, e.continuous⟩
  have hab' := congrArg (MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
    g e.isProperMap n).hom hab
  have hid : (TopCat.ofHom ⟨_, e.symm.continuous⟩ ≫ g) = 𝟙 _ :=
    TopCat.ext e.apply_symm_apply
  rwa [MMP.borelMooreHomology.pushforward_comp_apply ℚ _ g _ _
      (hid ▸ isProperMap_id),
    MMP.borelMooreHomology.pushforward_comp_apply ℚ _ g _ _
      (hid ▸ isProperMap_id),
    MMP.borelMooreHomology.pushforward_id_apply' ℚ _ _ hid,
    MMP.borelMooreHomology.pushforward_id_apply' ℚ _ _ hid] at hab'

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **The generic restriction of the algebraic defect is injective.** Let `Φ` be a linear map
from `K(r)/B(r)` to families of forms on the stalks of the punctured local systems `𝒱_T` over
adapted opens `T₀`, pairing `r_t α` with the sum of the fundamental curve classes of a divisor
representative `(Lᵢ)` on general fibres `F_t`. Given the kernel step `hkernel`, the detection
of `H₂(F_t, ℚ)` by restricted classes `hdetect` and the generic identification `hcycle` of the
fibre cycle classes, `Φ` is injective. -/
public theorem IsCurvePointExceptionalModel.injective_curveLocalSystemDual
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D)
    (T₀ : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens)
    (M : Submodule ℚ (∀ T, ∀ t : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY),
      Module.Dual ℚ (curveLocalSystemFibre sY (T₀ T) t)))
    (Φ : AlgebraicDefect F →ₗ[ℚ] M)
    (hΦval : ∀ T (x : algebraicKernel F) (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme),
      (∀ E, Chow.divisorClass E.1.idealSheaf.subscheme (L E) = x.1 E) →
      ∀ᶠ t : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY) in Filter.cofinite,
      ∃ _ : IsComplexScheme (pointFibre sY r (T₀ T) t),
      ∀ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY (T₀ T) t ∈ V)
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
        (p : pointFibre sY r (T₀ T) t)
        (hp : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) p = (0 : ℕ)),
        borelMooreHomology.capProduct ℚ
            (analyticSpace (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ))) Set.univ 2 2
            ((rationalCohomologyMap (pointFibreInclusion sY r (T₀ T) t hV) 2).hom α)
            (∑ E : F.support, (L E).sum fun P c ↦ c •
              ∑ᶠ (C : {x : pointFibre sY r (T₀ T) t // Stacks.Chow.relativeDimension
                  (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                  (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
                (_ : Maximal (fun A : Set (pointFibre sY r (T₀ T) t) ↦ IsIrreducible A ∧
                  A ⊆ (pointFibreFst sY r (T₀ T) t).base ⁻¹'
                    (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
                  (closure {C.1})),
                fundamentalClass C.1 C.2) =
          (Φ (Submodule.Quotient.mk x)).1 T t
              ((localSystemRestrictionFibre sY hr.isBiregular (T₀ T) t).hom
                ((stalkToPullbackStalk (curveOpenInclusion sY (T₀ T))
                  (resolutionHigherDirectImage sY r 2) t).hom
                  ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α))) •
            fundamentalClass p hp)
    (hkernel : ∀ L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme,
      ∑ E : F.support, componentHomologyMap E.1 4 (Chow.divisorClass _ (L E)) = 0 →
      (∀ T : IrreducibleCloseds Y, (T : Set Y) ⊆ (singularLocus sY : Set Y) →
          topologicalKrullDim (T : Set Y) = 1 →
        ∃ U : (curveScheme T).Opens, Dense (U : Set (curveScheme T)) ∧
          ∀ (t : ComplexPoints (U.ι ≫ curveι T ≫ sY))
            [IsComplexScheme (pointFibre sY r U t)],
            Chow.rationalCycleClass (pointFibre sY r U t) 1
              (∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
                (1 : ℚ) ⊗ₜ[ℤ] @Stacks.Chow.cycleAssociatedToClosedSubscheme
                  (Stacks.Chow.fieldChowSituation ℂ) _ _ (pointFibre sY r U t ↘ Spec (.of ℂ)) _
                  (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r)
                    (t.hom ≫ U.ι ≫ curveι T) r (t.hom ≫ U.ι ≫ curveι T)
                    (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
                    ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
                    ((Category.comp_id _).trans (Category.id_comp _).symm))
                  (isClosedImmersion_pullback_map_of_comp_eq
                    (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _)
                    (t.hom ≫ U.ι ≫ curveι T)) ((1 : ℕ) : ℤ)) = 0) →
      (fun E => Chow.divisorClass E.1.idealSheaf.subscheme (L E) : ComponentHomology F) ∈
        orientedSurfaceClasses F)
    (hdetect : ∀ T (t : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY))
      [IsComplexScheme (pointFibre sY r (T₀ T) t)]
      (w : MMP.Analytic.borelMooreHomology (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) (2 * 1)),
      (∀ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY (T₀ T) t ∈ V)
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
        (_p : pointFibre sY r (T₀ T) t)
        (_hp : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) _p = (0 : ℕ)),
        borelMooreHomology.capProduct ℚ
            (analyticSpace (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ))) Set.univ 2 2
            ((rationalCohomologyMap (pointFibreInclusion sY r (T₀ T) t hV) 2).hom α) w = 0) →
      w = 0)
    (hcycle : ∀ T (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme),
      (∀ᶠ t : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY) in Filter.cofinite,
        ∃ _ : IsComplexScheme (pointFibre sY r (T₀ T) t),
          (∑ E : F.support, (L E).sum fun P c ↦ c •
            ∑ᶠ (x : {x : pointFibre sY r (T₀ T) t // Stacks.Chow.relativeDimension
                (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
              (_ : Maximal (fun A : Set (pointFibre sY r (T₀ T) t) ↦ IsIrreducible A ∧
                A ⊆ (pointFibreFst sY r (T₀ T) t).base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
                (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) = 0) →
      ∃ U : (curveScheme T.1).Opens, Dense (U : Set (curveScheme T.1)) ∧
        ∀ (t : ComplexPoints (U.ι ≫ curveι T.1 ≫ sY))
          [IsComplexScheme (pointFibre sY r U t)],
          Chow.rationalCycleClass (pointFibre sY r U t) 1
            (∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
              (1 : ℚ) ⊗ₜ[ℤ] @Stacks.Chow.cycleAssociatedToClosedSubscheme
                (Stacks.Chow.fieldChowSituation ℂ) _ _ (pointFibre sY r U t ↘ Spec (.of ℂ)) _
                (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r)
                  (t.hom ≫ U.ι ≫ curveι T.1) r (t.hom ≫ U.ι ≫ curveι T.1)
                  (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
                  ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
                  ((Category.comp_id _).trans (Category.id_comp _).symm))
                (isClosedImmersion_pullback_map_of_comp_eq
                  (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _)
                  (t.hom ≫ U.ι ≫ curveι T.1)) ((1 : ℕ) : ℤ)) = 0) :
    Function.Injective Φ := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H x =>
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  have hx : (x : ComponentHomology F) ∈
      exceptionalKernel F fun E => divisorClasses E.1.idealSheaf.subscheme := x.2
  rw [mem_exceptionalKernel] at hx
  choose L hL using fun E => LinearMap.mem_range.1 (hx.1 E)
  have hsum : ∑ E : F.support, componentHomologyMap E.1 4 (Chow.divisorClass _ (L E)) = 0 := by
    simpa only [hL] using hx.2
  have hmem := hkernel L hsum fun T hTs hTd => hcycle ⟨T, hTs, hTd⟩ L <|
    (hΦval ⟨T, hTs, hTd⟩ x L hL).mono fun t ⟨hc, h⟩ => ⟨hc, by
      classical
      have hw := hdetect _ t _ fun V hV α p hp => by
        refine (h V hV α p hp).trans ?_
        rw [hq]
        simp
        rfl
      refine pushforward_homeomorphUnderlyingSpace_injective (2 * 1) ?_
      rw [map_zero]
      refine Eq.trans ?_ hw
      rw [map_sum]
      refine Finset.sum_congr rfl fun E _ => ?_
      simp only [Finsupp.sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [map_smul]
      congr 1
      refine ((LinearMap.toAddMonoidHom _).map_finsum_of_injective
        (pushforward_homeomorphUnderlyingSpace_injective
          (X := pointFibre sY r (T₀ ⟨T, hTs, hTd⟩) t) (2 * 1))
        _).trans (finsum_congr fun C => ?_)
      rw [finsum_eq_if, finsum_eq_if]
      split_ifs
      · rfl
      · exact map_zero _⟩
  convert hmem using 1
  exact funext fun E => (hL E).symm

end MMP.Fourfold
