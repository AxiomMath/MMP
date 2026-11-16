module
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.Morphisms.SmoothStalkDimension
public import MMP.AlgebraicGeometry.Analytic.BlowupFibre.Euler
public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.Transport
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicTopology.PoincareDuality.DualClassSupport
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksFormula
public import StacksFrontier.AlgebraicGeometry.Properties.DimensionFunctionClosure
public import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksLineBundleChern
public import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import MMP.AlgebraicGeometry.Chow.CycleClassGenericPoint
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationProof
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.DivisorTransversal
public import MMP.AlgebraicGeometry.CycleMap.RingDiagonalSwap
public import MMP.AlgebraicGeometry.CycleMap.RefinedIntersection
public import MMP.AlgebraicTopology.CapProduct.SupportRetraction
public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionStructureSheaf
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PoincareDualityVariety

/-!
# The Cartier divisor dictionary on a smooth projective variety

Let `X` be a smooth projective complex variety of dimension `n = d + 1`, with fundamental class
`[X] ∈ H_{2n}(X, ℚ)`, and let `L` be a `ℚ`-divisor on `X`; since `X` is smooth, `L` is
`ℚ`-Cartier, and for any `m > 0` with `mL = M` an integral divisor, `𝒪_X(M)` is invertible. The
first Chern class of `L` with rational coefficients is `c₁(𝒪_X(L)) = (1/m) c₁(𝒪_X(M)) ∈
H²(X^an; ℚ)`. The dictionary says that the fundamental class `[L] = ∑ᵢ aᵢ [Pᵢ] ∈ H_{2d}(X, ℚ)` of
`L = ∑ᵢ aᵢ Pᵢ` is `c₁(𝒪_X(L)) ∩ [X]`. As capping with `[X]` is Poincaré duality
`H²(X; ℚ) ≅ H_{2n-2}(X, ℚ)` on the compact complex manifold `X^an`, `[L] = 0` if and only if
`c₁(𝒪_X(L)) = 0` rationally.

Both sides are additive in the divisor (`c₁(𝒪(N + N')) = c₁(𝒪(N)) + c₁(𝒪(N'))`, since
`𝒪(N) ⊗ 𝒪(N') ≅ 𝒪(N + N')` for Cartier divisors), so it suffices to treat a prime divisor `S`.
On the smooth `X` it is an effective Cartier divisor, so Stacks' invertible sheaf `𝒪_X(S)`
(Tag 01WS) carries its canonical section `1`, whose Stacks zero scheme (Tag 02OQ) is `S`, and
`𝒪_X(S)` is the divisorial sheaf of `S`. By Fulton's Lemma 19.1.3 and Proposition 19.2 on Stacks
cycles (`MMP.Chow.cycleClass_zeroScheme_eq_firstChernClassTopCap`), the cycle class of `[S]` is
`c₁ᵗᵒᵖ(𝒪_X(S)) ∩ [X]`, where `c₁ᵗᵒᵖ` is the zero-section pull-back of the Thom class of the line
bundle `𝐕(𝒪_X(S)^∨)`; and `c₁ᵗᵒᵖ(𝓛)` is the first Chern class of `𝓛` pulled back along
`X(ℂ) ≅ X^an` (`MMP.Modules.topFirstChernClass_dual`: the Euler class of a complex line bundle is
its first Chern class, Milnor–Stasheff, Thm. 12.5). Finally, capping with `[X]` is injective on
`H²(X^an; ℚ)` by Poincaré duality, which gives the equivalence of the two vanishings.

## Main results

* `MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback`: `m [L] = c₁(𝒪_X(mL)) ∩ [X]` in
  `H_{2d}(X, ℚ)`, and `[L] = 0` if and only if `c₁(𝒪_X(mL)) = 0` in `H²(X^an; ℚ)`.
* `MMP.Fourfold.pushforward_refinedGysin_eq_capProductSupportPullback_smul_rationalCycleClass`:
  for a regular closed immersion `f : S → X` with orientation class `u`,
  `u ∩ m [L] = cl(f^! (mL))` and `u ∩ m [L] = f^* c₁(𝒪_X(mL)) ∩ [S]` in `H_{2k}(f(S(ℂ)), ℚ)`, by
  Fulton's Theorem 19.2 on Stacks' Chow groups (`MMP.Chow.chowCycleMapRefinedGysinFormulaAt`).

## Implementation notes

* `H_k(X, ℚ)` is `MMP.Fourfold.RationalHomology`, the Borel–Moore homology of Fulton's
  underlying space `X(ℂ)`, which is singular homology as `X` is projective. The cycle of `L` is
  the Stacks rational cycle `∑ᵢ aᵢ [Pᵢ]` (`MMP.Chow.RationalCycleGroup`), with `[Pᵢ]` the prime
  cycle of the generic point of `Pᵢ` (every prime divisor of `X` has delta-dimension `d`), and
  `[L]` is its image under `MMP.Chow.rationalCycleClass`; for `d = 2` this is
  `MMP.Chow.divisorClass`. `[X]` is the class of the prime cycle of a point of delta-dimension
  `n`, which is the generic point of `X`. The Chern class
  `MMP.Analytic.algebraicFirstChernClass` lives on the analytic space `X^an`, and the cap product
  is taken after pulling it back along the homeomorphism `X(ℂ) ≅ X^an`
  (`MMP.borelMooreHomology.capProductPullback`); its degree `2n - 2` is identified
  with `2d` by `MMP.BorelMooreCross.congrDegree`.
* The source proves the identity by removing from `X` the singular loci of the components of `L`
  and their pairwise intersections, a closed set `C` of codimension at least two, comparing the two
  classes on `X ∖ C` through the Thom classes of the normal disks, and using the injectivity of
  `H_{2d}(X) → H^BM_{2d}(X ∖ C)`. Here that localization is the proof of Fulton's Lemma 19.1.3
  for the canonical section of `𝒪_X(S)`; the comparison of the Thom class of the normal disk with
  the line-bundle Chern class is `c₁ᵗᵒᵖ(𝒪_X(S)) = c₁(𝒪_X(S))`.
* A `ℚ`-Cartier divisor is represented by `L` together with an integral divisor `M` and `m > 0`
  with `M = mL`; the identity is stated for `m [L]` and `c₁(𝒪_X(M))`, which is the identity for
  `[L]` and `(1/m) c₁(𝒪_X(M))`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Lemma 19.1.3 and Proposition 19.1.2;
  §19.2, Theorem 19.2.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], Thm. 12.5 and §14.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MMP

namespace MMP.Fourfold

open MMP.Analytic
open scoped MMP.SubschemeOver
open Stacks.Intersection.ExteriorProductProjections
  (relativeDimension_eq_of_topologicalKrullDim_closure)

/-! ### Smooth projective varieties are smooth of relative dimension their dimension -/

/-- A smooth projective complex variety of dimension `n` is smooth of relative dimension `n`. -/
private theorem smoothOfRelativeDimension_of_isSmoothScheme {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))]
    (hW : MMP.Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (W ↘ Spec (.of ℂ))) {n : ℕ} (hdim : topologicalKrullDim W = n) :
    SmoothOfRelativeDimension n (W ↘ Spec (.of ℂ)) := by
  haveI := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hW).1
  haveI : Smooth (W ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  exact MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ n hdim

/-! ### Poincaré duality -/

section Duality

open borelMooreHomology Set

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

variable (X) in
/-- The homeomorphism `X(ℂ) ≅ X^an`, as a morphism of spaces. -/
private abbrev anHom : TopCat.of (UnderlyingSpace ℂ X) ⟶ Analytification.space (X ↘ Spec (.of ℂ)) :=
  TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩

variable (X) in
/-- The inverse homeomorphism `X^an ≅ X(ℂ)`. -/
private abbrev anInv : Analytification.space (X ↘ Spec (.of ℂ)) ⟶ TopCat.of (UnderlyingSpace ℂ X) :=
  TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.continuous⟩

/-- `X^an → X(ℂ) → X^an` is the identity. -/
private theorem anInv_anHom : anInv X ≫ anHom X = 𝟙 _ := by
  refine TopCat.hom_ext (ContinuousMap.ext fun x ↦ ?_)
  exact ComplexPoints.homeomorphUnderlyingSpace.symm_apply_apply x

/-- Pulling back along a map equal to the identity is the identity. -/
private theorem pullback_apply_of_eq_id {Y : TopCat.{0}} {φ : Y ⟶ Y} (hφ : φ = 𝟙 Y) (j : ℤ)
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ j) :
    (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) φ univ j).hom c = c := by
  subst hφ
  rw [cohomologyWithSupports.pullback_id]
  rfl

/-- Pulling back along the homeomorphism `X(ℂ) ≅ X^an` is injective. -/
private theorem injective_pullback_anHom (j : ℤ) :
    Function.Injective
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (anHom X) univ j).hom := by
  have key : ∀ c, (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (anInv X)
      (anHom X ⁻¹' univ) j).hom
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (anHom X) univ j).hom c) = c := by
    intro c
    rw [← ModuleCat.comp_apply, ← cohomologyWithSupports.pullback_comp]
    exact pullback_apply_of_eq_id anInv_anHom j c
  exact Function.LeftInverse.injective key

/-- On an integral complex scheme smooth of relative dimension `d + 1`, the class of the prime cycle
of a point of delta-dimension `d + 1` (which is the generic point) is a fundamental class of `X`. -/
private theorem isVarietyFundamentalClass_rationalCycleClass [IsIntegral X] {d : ℕ}
    [SmoothOfRelativeDimension (d + 1) (X ↘ Spec (.of ℂ))]
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = ((d + 1 : ℕ) : ℤ)) :
    IsVarietyFundamentalClass ℚ
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := X) (d + 1))
      (Chow.rationalCycleClass X (d + 1)
        (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          ((d + 1 : ℕ) : ℤ) x hx)) := by
  rw [Chow.rationalCycleClass_rationalPointCycle]
  have hbot : Stacks.Chow.integralComponentAt x = ⊥ := by
    have hcl : TopologicalSpace.Closeds.closure ({x} : Set X) = ⊤ :=
      TopologicalSpace.Closeds.ext (Chow.closure_eq_univ_of_relativeDimension_eq ℂ hdim x hx)
    rw [Stacks.Chow.integralComponentAt, hcl, Scheme.IdealSheafData.vanishingIdeal_top,
      Scheme.nilradical_eq_bot]
  haveI : IsIso (Stacks.Chow.integralComponentAt x).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 hbot
  exact IsVarietyFundamentalClass.pushforward_of_isIso _ _
    (existsUnique_isVarietyFundamentalClass ℚ
      (Chow.natCast_eq_dimension_integralComponentAt x hx)).choose_spec.1

/-- **Poincaré duality on a smooth projective variety**: capping with `[X]` is injective on
`H²(X^an; ℚ)`. -/
private theorem injective_capProductPullback (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) {d : ℕ}
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = ((d + 1 : ℕ) : ℤ)) :
    Function.Injective fun c ↦ capProductPullback ℚ (anHom X) univ 2 ((2 * (d + 1) : ℕ) : ℤ) c
      (Chow.rationalCycleClass X (d + 1)
        (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          ((d + 1 : ℕ) : ℤ) x hx)) := by
  haveI : IsIntegral X := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hX).1.toIsIntegral
  haveI : SmoothOfRelativeDimension (d + 1) (X ↘ Spec (.of ℂ)) :=
    smoothOfRelativeDimension_of_isSmoothScheme hX hsm hdim
  have hb := bijective_capProduct_univ_of_isVarietyFundamentalClass
    (isVarietyFundamentalClass_rationalCycleClass hdim x hx) 2
  exact fun _ _ h ↦ injective_pullback_anHom 2 (hb.1 h)

end Duality

/-! ### Reduction to a prime divisor -/

section Assembly

open borelMooreHomology Set

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

variable (X) in
/-- The rational `d`-cycle `∑ aᵢ [Pᵢ]` of a `ℚ`-divisor `∑ aᵢ Pᵢ`, a prime divisor counting (by
the prime cycle of its generic point) when it has delta-dimension `d`. -/
private def qCycle (d : ℕ) :
    Mori.QDivisor X →ₗ[ℚ] Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ)
      (X ↘ Spec (.of ℂ)) d :=
  Finsupp.linearCombination ℚ fun P : Mori.PrimeDivisor X =>
    if h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) P.genericPoint = d then
      Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) d
        P.genericPoint h
    else 0

variable (X) in
/-- Capping with a class `μ ∈ H_{2d+2}(X, ℚ)`, `c ↦ c ∩ μ ∈ H_{2d}(X, ℚ)`, for
`c ∈ H²(X^an; ℚ)`. -/
private def capWith (d : ℕ) (μ : RationalHomology X (2 * (d + 1))) :
    singularCohomology ℚ (Analytification.space (X ↘ Spec (.of ℂ))) 2 →ₗ[ℚ]
      RationalHomology X (2 * d) :=
  (BorelMooreCross.congrDegree ℚ (TopCat.of (UnderlyingSpace ℂ X))
      (by push_cast; ring : ((2 * (d + 1) : ℕ) : ℤ) - 2 = ((2 * d : ℕ) : ℤ))).toLinearMap ∘ₗ
    (capProductPullback ℚ (anHom X) univ 2 ((2 * (d + 1) : ℕ) : ℤ)).flip μ

/-- `c ∩ μ` is the cap product with `c` pulled back to `X(ℂ)`. -/
private theorem capWith_apply (d : ℕ) (μ : RationalHomology X (2 * (d + 1)))
    (c : singularCohomology ℚ (Analytification.space (X ↘ Spec (.of ℂ))) 2) :
    capWith X d μ c = BorelMooreCross.congrDegree ℚ (TopCat.of (UnderlyingSpace ℂ X))
      (by push_cast; ring : ((2 * (d + 1) : ℕ) : ℤ) - 2 = ((2 * d : ℕ) : ℤ))
      (capProductPullback ℚ (anHom X) univ 2 ((2 * (d + 1) : ℕ) : ℤ) c μ) :=
  rfl

/-- The rational first Chern class `c₁(L) ∈ H²(X^an; ℚ)` of an invertible module. -/
private abbrev ratChern (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    singularCohomology ℚ (Analytification.space (X ↘ Spec (.of ℂ))) 2 :=
  singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)

omit [X.Over (Spec (.of ℂ))] [IsComplexScheme X] in
/-- The `ℚ`-divisor of the prime divisor `P` is `P`. -/
private theorem toQDivisor_single_one (P : Mori.PrimeDivisor X) :
    Mori.Divisor.toQDivisor (Finsupp.single P (1 : ℤ)) = Finsupp.single P (1 : ℚ) := by
  ext E
  change ((Finsupp.single P (1 : ℤ) E : ℤ) : ℚ) = _
  by_cases h : P = E <;> simp [Finsupp.single_apply, h, Mori.DivisorWithCoeffs.coeff_apply]

variable [IsLocallyNoetherian X] [IsNormal X]

/-- On a smooth projective variety the divisorial sheaf of every divisor is invertible. -/
private theorem isInvertible_divisorialSheaf (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) (N : Mori.Divisor X) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N.divisorialSheaf := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  haveI : IsIntegral X := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hX).1.toIsIntegral
  exact (MMP.Fourfold.isCartier_of_isSmoothScheme hsm N).isInvertibleModule_divisorialSheaf

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- In a variety of dimension `d + 1` over `ℂ`, the generic point of a prime divisor has
delta-dimension `d`. -/
private theorem relativeDimension_primeDivisor_genericPoint_eq [IsIntegral X] {d : ℕ}
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) (S : Mori.PrimeDivisor X) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) S.genericPoint = d := by
  refine relativeDimension_eq_of_topologicalKrullDim_closure ℂ _ _ d ?_
  rw [AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height]
  have h1 := MMP.height_add_coheight_eq_krullDim ℂ S.genericPoint
  rw [show Order.krullDim X = ((d + 1 : ℕ) : WithBot ℕ∞) by
      rwa [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))],
    MMP.Mori.PrimeDivisor.coheight_genericPoint S] at h1
  have h2 : Order.height S.genericPoint + 1 = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
  have h3 : Order.height S.genericPoint = (d : ℕ∞) := by
    generalize Order.height S.genericPoint = c at h2 ⊢
    induction c with
    | top => exact absurd h2 (by rw [top_add]; exact ENat.top_ne_natCast _)
    | coe n => norm_cast at h2 ⊢; omega
  rw [h3]
  rfl

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The ideal sheaf of a prime divisor of an integral scheme is not zero. -/
private theorem primeDivisor_idealSheaf_ne_bot [IsIntegral X] (S : Mori.PrimeDivisor X) :
    S.idealSheaf ≠ ⊥ := by
  intro hS
  have hcl : closure ({S.genericPoint} : Set X) = Set.univ := by
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support, hS, Scheme.IdealSheafData.support_bot]
    rfl
  have hmax : IsMax S.genericPoint := fun y _ ↦ by
    change S.genericPoint ⤳ y
    rw [specializes_iff_mem_closure, hcl]
    exact Set.mem_univ _
  have h1 := MMP.Mori.PrimeDivisor.coheight_genericPoint S
  rw [Order.coheight_eq_zero.2 hmax] at h1
  exact zero_ne_one h1

/-- **Stacks 02QU.** The fundamental cycle `[Z]_k` of an integral scheme `Z` of delta-dimension `k`
is the prime cycle of its generic point. -/
private theorem cycleAssociatedToClosedSubscheme_id_eq_pointCycle {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] [IsIntegral Z] {k : ℤ}
    (hk : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Z ↘ Spec (.of ℂ)) (_root_.genericPoint Z) = k) :
    Stacks.Chow.cycleAssociatedToClosedSubscheme (Stacks.Chow.fieldChowSituation ℂ)
        (Z ↘ Spec (.of ℂ)) (𝟙 Z) k =
      Stacks.Chow.pointCycle (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) k
        (_root_.genericPoint Z) hk := by
  refine Subtype.ext ?_
  ext y
  rw [Stacks.Chow.pointCycle_apply]
  by_cases hy : y = _root_.genericPoint Z
  · subst hy
    rw [if_pos rfl]
    exact Stacks.Chow.cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint _ _ (𝟙 Z) k hk
  · rw [if_neg hy]
    exact Stacks.Chow.cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne _ _ (𝟙 Z) k hy

/-- The push-forward to `X` of the cycle class of the fundamental `d`-cycle of the subscheme `S`
of a prime divisor is the class of the rational `d`-cycle of `S`. -/
private theorem pushforward_cycleClass_cycleAssociatedToClosedSubscheme_eq [IsIntegral X] {d : ℕ}
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) (S : Mori.PrimeDivisor X)
    {I : X.IdealSheafData} (hI : I = S.idealSheaf) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) I.subschemeι))
        (UnderlyingSpace.isProperMap_map (K := ℂ) _) ((2 * d : ℕ) : ℤ)).hom
        (Chow.cycleClass ℚ d (Stacks.Chow.cycleAssociatedToClosedSubscheme
          (Stacks.Chow.fieldChowSituation ℂ) (I.subscheme ↘ Spec (.of ℂ)) (𝟙 _) d)) =
      Chow.rationalCycleClass X d (qCycle X d (Mori.Divisor.toQDivisor (Finsupp.single S 1))) := by
  classical
  subst hI
  haveI : IsIntegral S.idealSheaf.subscheme := S.integral
  have hS := relativeDimension_primeDivisor_genericPoint_eq hdim S
  have hgen : S.idealSheaf.subschemeι (_root_.genericPoint S.idealSheaf.subscheme) =
      S.genericPoint := rfl
  have hZ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
    (S.idealSheaf.subscheme ↘ Spec (.of ℂ))
      (_root_.genericPoint S.idealSheaf.subscheme) = d := by
    rw [show S.idealSheaf.subscheme ↘ Spec (.of ℂ) =
      S.idealSheaf.subschemeι ≫ X ↘ Spec (.of ℂ) from rfl,
      Stacks.Chow.relativeDimension_comp_closedImmersion, hgen, hS]
  rw [cycleAssociatedToClosedSubscheme_id_eq_pointCycle hZ, Chow.cycleClass_pointCycle]
  erw [Chow.pushforward_pointCycleClass]
  rw [Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion, hgen, Chow.pointCycleClassOrZero,
    dif_pos hS, toQDivisor_single_one S, qCycle, Finsupp.linearCombination_single, one_smul,
    dif_pos hS, Chow.rationalCycleClass_rationalPointCycle]
  simp

/-- The cycle class of the fundamental `d`-cycle of the subscheme `S` of a prime divisor, read in
`X`, is the class of the rational `d`-cycle of `S`. -/
private theorem cycleClass_cycleAssociatedToClosedSubscheme_eq [IsIntegral X] {d : ℕ}
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) (S : Mori.PrimeDivisor X)
    {I : X.IdealSheafData} (hI : I = S.idealSheaf) :
    Chow.cycleClass ℚ d (Stacks.Chow.cycleAssociatedToClosedSubscheme
        (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) I.subschemeι d) =
      Chow.rationalCycleClass X d (qCycle X d (Mori.Divisor.toQDivisor (Finsupp.single S 1))) := by
  have e := Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
    (Stacks.Chow.fieldChowSituation ℂ) (I.subscheme ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))
    I.subschemeι (comp_over _ _) (𝟙 _) d
  rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_congr (Stacks.Chow.fieldChowSituation ℂ)
    (X ↘ Spec (.of ℂ)) _ _ (Category.id_comp I.subschemeι)] at e
  rw [← e, Chow.cycleClass_properPushforward]
  exact pushforward_cycleClass_cycleAssociatedToClosedSubscheme_eq hdim S hI

/-- `c₁(L) ∩ μ`, with `c₁(L)` the first Chern class of `L` on `X^an` pulled back to `X(ℂ)`, is
`c₁ᵗᵒᵖ(L) ∩ μ`, with `c₁ᵗᵒᵖ(L)` the zero-section pull-back of the Thom class of `𝐕(L^∨)`. -/
private theorem capWith_ratChern_eq_firstChernClassTopCap (d : ℕ)
    (μ : RationalHomology X (2 * (d + 1))) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    capWith X d μ (ratChern L) = Chow.firstChernClassTopCap ℚ L d μ := by
  rw [capWith_apply, capProductPullback_apply, Chow.firstChernClassTopCap, Chow.firstChernClassTop,
    MMP.Modules.topFirstChernClass_dual ℚ L]
  rfl

/-- **The dictionary for a prime divisor.** -/
private theorem rationalCycleClass_qCycle_single_eq
    (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) {d : ℕ}
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = ((d + 1 : ℕ) : ℤ))
    (S : Mori.PrimeDivisor X)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Mori.Divisor.divisorialSheaf (Finsupp.single S (1 : ℤ)))] :
    Chow.rationalCycleClass X d (qCycle X d (Mori.Divisor.toQDivisor (Finsupp.single S 1))) =
      capWith X d (Chow.rationalCycleClass X (d + 1)
        (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          ((d + 1 : ℕ) : ℤ) x hx))
        (ratChern (Mori.Divisor.divisorialSheaf (Finsupp.single S (1 : ℤ)))) := by
  haveI : IsIntegral X := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hX).1.toIsIntegral
  haveI : SmoothOfRelativeDimension (d + 1) (X ↘ Spec (.of ℂ)) :=
    smoothOfRelativeDimension_of_isSmoothScheme hX hsm hdim
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  have hn : ((d + 1 : ℕ) : WithBot ℕ∞) = MMP.Intersection.Scheme.dimension X := hdim.symm
  set μ := Chow.rationalCycleClass X (d + 1)
      (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
        ((d + 1 : ℕ) : ℤ) x hx)
  have hμ : IsVarietyFundamentalClass ℚ hn μ :=
    isVarietyFundamentalClass_rationalCycleClass hdim x hx
  -- `𝒪_X(S)` is the Stacks sheaf `𝒪_X(D)` of the effective Cartier divisor `D = S`, whose
  -- canonical section `1_D` has zero scheme `D`
  haveI hcart : Stacks.Divisors.IsEffectiveCartierDivisor S.idealSheaf :=
    MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm S
  obtain ⟨e⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' S
    hcart (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _)
  let L : X.Modules := Stacks.Divisors.modulesInvertibleSheaf S.idealSheaf
  let e' : Mori.Divisor.divisorialSheaf (Finsupp.single S (1 : ℤ)) ≅ L := e
  haveI hL : Stacks.Ample.IsInvertibleModule X L :=
    Stacks.Divisors.isInvertible_invertibleSheaf S.idealSheaf
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL
  let t : Γ(L, ⊤) := Stacks.Divisors.canonicalSection S.idealSheaf
  have hZ : Stacks.Divisors.zeroScheme X L t = S.idealSheaf :=
    Stacks.Divisors.zeroScheme_canonicalSection' S.idealSheaf
  have ht : t ≠ 0 := by
    intro h0
    refine primeDivisor_idealSheaf_ne_bot S (hZ.symm.trans ?_)
    rw [h0]
    refine le_antisymm (fun U => ?_) bot_le
    refine le_trans (Scheme.IdealSheafData.ideal_ofIdeals_le _ U) ?_
    show Ideal.span _ ≤ (⊥ : Ideal Γ(X, U.1))
    rw [Ideal.span_le]
    rintro a ⟨φ, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_bot, map_zero, map_zero]
  -- Fulton 19.1.3 / 19.2 for the section `t`: `cl([Z(t)]_d) = c₁ᵗᵒᵖ(L) ∩ μ`
  have key : Chow.cycleClass ℚ d (Stacks.Chow.cycleAssociatedToClosedSubscheme
      (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
        (Stacks.Divisors.zeroScheme X L t).subschemeι d) =
      Chow.firstChernClassTopCap ℚ L d μ :=
    Chow.cycleClass_zeroScheme_eq_firstChernClassTopCap ℚ L hn t ht hμ
  rw [cycleClass_cycleAssociatedToClosedSubscheme_eq hdim S hZ] at key
  rw [key, ← capWith_ratChern_eq_firstChernClassTopCap]
  exact congrArg (fun c ↦ capWith X d μ (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c))
    (algebraicFirstChernClass_eq_of_iso e').symm

/-- Additivity of the rational first Chern class of divisorial sheaves on a smooth projective
variety: `c₁(𝒪(N + N')) = c₁(𝒪(N)) + c₁(𝒪(N'))`. -/
private theorem ratChern_add (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) (N N' : Mori.Divisor X) :
    @ratChern X _ (N + N').divisorialSheaf (isInvertible_divisorialSheaf hX hsm (N + N')) =
      @ratChern X _ N.divisorialSheaf (isInvertible_divisorialSheaf hX hsm N) +
        @ratChern X _ N'.divisorialSheaf (isInvertible_divisorialSheaf hX hsm N') := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  haveI : IsIntegral X := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hX).1.toIsIntegral
  have hN := MMP.Fourfold.isCartier_of_isSmoothScheme hsm N
  have hN' := MMP.Fourfold.isCartier_of_isSmoothScheme hsm N'
  haveI := isInvertible_divisorialSheaf hX hsm N
  haveI := isInvertible_divisorialSheaf hX hsm N'
  haveI := isInvertible_divisorialSheaf hX hsm (N + N')
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
        N.divisorialSheaf).obj N'.divisorialSheaf) :=
    hN.isInvertibleModule_tensorSheaf hN'
  have e := algebraicFirstChernClass_eq_of_iso (hN.divisorialSheafTensorIso hN')
  rw [algebraicFirstChernClass_sheafTensor] at e
  simp only [ratChern, ← e, map_add]

variable (X) in
/-- The class `N ↦ c₁(𝒪(N)) ∩ [X]`, an additive map on divisors. -/
private def capChernHom (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) (d : ℕ)
    (μ : RationalHomology X (2 * (d + 1))) : Mori.Divisor X →+ RationalHomology X (2 * d) :=
  AddMonoidHom.mk'
    (fun N ↦ capWith X d μ
      (@ratChern X _ N.divisorialSheaf (isInvertible_divisorialSheaf hX hsm N)))
    fun N N' ↦ by
      change capWith X d μ _ = capWith X d μ _ + capWith X d μ _
      rw [ratChern_add hX hsm N N', map_add]

/-- **The dictionary for a divisor.** -/
private theorem rationalCycleClass_qCycle_eq
    (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) {d : ℕ}
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = ((d + 1 : ℕ) : ℤ))
    (N : Mori.Divisor X)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N.divisorialSheaf] :
    Chow.rationalCycleClass X d (qCycle X d (Mori.Divisor.toQDivisor N)) =
      capWith X d (Chow.rationalCycleClass X (d + 1)
        (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          ((d + 1 : ℕ) : ℤ) x hx))
        (ratChern N.divisorialSheaf) := by
  let A : Mori.Divisor X →+ RationalHomology X (2 * d) :=
    ((Chow.rationalCycleClass X d ∘ₗ qCycle X d).toAddMonoidHom).comp Mori.Divisor.toQDivisor
  have hAB : A = capChernHom X hX hsm d (Chow.rationalCycleClass X (d + 1)
          (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
            ((d + 1 : ℕ) : ℤ) x hx)) := by
    refine Finsupp.addHom_ext fun S n ↦ ?_
    have hs : (Finsupp.single S n : Mori.Divisor X) = n • Finsupp.single S 1 :=
      (Finsupp.smul_single_one _ _).symm
    rw [hs, map_zsmul, map_zsmul]
    congr 1
    haveI := isInvertible_divisorialSheaf hX hsm (Finsupp.single S 1)
    exact rationalCycleClass_qCycle_single_eq hX hsm hdim x hx S
  exact DFunLike.congr_fun hAB N

end Assembly

/-! ### The dictionary -/

/-- **The Cartier divisor dictionary on a smooth projective variety.** Let `X` be a smooth
projective complex variety of dimension `d + 1`, `L` a `ℚ`-divisor on `X` and `M = mL` an integral
divisor with `m > 0`. Then `m [L] = c₁(𝒪_X(M)) ∩ [X]` in `H_{2d}(X, ℚ)`, where `[L]` is the class
of the rational `d`-cycle `∑ᵢ aᵢ [Pᵢ]` of `L = ∑ᵢ aᵢ Pᵢ` (`[Pᵢ]` the prime cycle of the generic
point of `Pᵢ`) and `[X]` is the class of the prime cycle of a point `x` of delta-dimension
`d + 1`, which is the generic point of `X`; and `[L] = 0` if and only if `c₁(𝒪_X(M)) = 0` in
`H²(X^an; ℚ)`. -/
@[mmp "lem_mmp_conductor_smooth_cartier_dictionary"]
public theorem smul_rationalCycleClass_eq_capProductPullback {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) {d : ℕ}
    (hdim : topologicalKrullDim X = (d + 1 : ℕ))
    (L : Mori.QDivisor X) {m : ℕ} (hm : 0 < m) (M : Mori.Divisor X)
    (hM : Mori.Divisor.toQDivisor M = (m : ℤ) • L)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M.divisorialSheaf]
    (x : X) (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = ((d + 1 : ℕ) : ℤ)) :
    (m : ℚ) • Chow.rationalCycleClass X d
        (Finsupp.linearCombination ℚ (fun P : Mori.PrimeDivisor X =>
          if h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (X ↘ Spec (.of ℂ))
              P.genericPoint = d then
            Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) d
              P.genericPoint h
          else 0) L) =
        BorelMooreCross.congrDegree ℚ (TopCat.of (UnderlyingSpace ℂ X))
          (by push_cast; ring : ((2 * (d + 1) : ℕ) : ℤ) - 2 = ((2 * d : ℕ) : ℤ))
          (borelMooreHomology.capProductPullback ℚ
            (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
              TopCat.of (UnderlyingSpace ℂ X) ⟶ Analytification.space (X ↘ Spec (.of ℂ)))
            Set.univ 2 ((2 * (d + 1) : ℕ) : ℤ)
            (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
              (algebraicFirstChernClass M.divisorialSheaf))
            (Chow.rationalCycleClass X (d + 1)
              (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
                ((d + 1 : ℕ) : ℤ) x hx))) ∧
      (Chow.rationalCycleClass X d
          (Finsupp.linearCombination ℚ (fun P : Mori.PrimeDivisor X =>
            if h : Stacks.Chow.relativeDimension
                (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
                P.genericPoint = d then
              Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) d
                P.genericPoint h
            else 0) L) = 0 ↔
        singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (algebraicFirstChernClass M.divisorialSheaf) = 0) := by
  have hq : (m : ℚ) • qCycle X d L = qCycle X d (Mori.Divisor.toQDivisor M) := by
    rw [hM, ← map_smul]
    congr 1
  have h1 : (m : ℚ) • Chow.rationalCycleClass X d (qCycle X d L) =
      capWith X d (Chow.rationalCycleClass X (d + 1)
        (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          ((d + 1 : ℕ) : ℤ) x hx))
        (ratChern M.divisorialSheaf) := by
    rw [← map_smul, hq, rationalCycleClass_qCycle_eq hX hsm hdim x hx M]
  have hinj : Function.Injective
      (capWith X d (Chow.rationalCycleClass X (d + 1)
        (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          ((d + 1 : ℕ) : ℤ) x hx))) := fun c c' h ↦
    injective_capProductPullback hX hsm hdim x hx ((LinearEquiv.injective _) h)
  refine ⟨h1, ?_⟩
  change Chow.rationalCycleClass X d (qCycle X d L) = 0 ↔ ratChern M.divisorialSheaf = 0
  rw [← smul_eq_zero_iff_right (Nat.cast_ne_zero.2 hm.ne' : (m : ℚ) ≠ 0), h1,
    map_eq_zero_iff _ hinj]

/-! ### Compatibility with Gysin restriction -/

section Gysin

open borelMooreHomology Set UnderlyingSpace Stacks.Chow CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

attribute [local instance] Chow.fibreProductOver Chow.isOver_fibreProduct_fst
  Chow.isOver_fibreProduct_snd Chow.isComplexScheme_fibreProduct

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

variable (X) in
/-- The integral `n`-cycle `∑ aᵢ [Pᵢ]` of a divisor `∑ aᵢ Pᵢ`, a prime divisor counting (by the
prime cycle of its generic point) when it has delta-dimension `n`. -/
private def zCycle (n : ℕ) :
    Mori.Divisor X →ₗ[ℤ] CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n :=
  Finsupp.linearCombination ℤ fun P : Mori.PrimeDivisor X =>
    if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
      P.genericPoint = n then
      pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n P.genericPoint h
    else 0

/-- The class of the integral cycle of a divisor `M` is the class of the rational cycle of `M`. -/
private theorem cycleClass_zCycle (n : ℕ) (M : Mori.Divisor X) :
    Chow.cycleClass ℚ n (zCycle X n M) =
      Chow.rationalCycleClass X n (qCycle X n (Mori.Divisor.toQDivisor M)) := by
  induction M using Finsupp.induction_linear with
  | zero => simp
  | add M N hM hN => simp only [map_add, hM, hN]
  | single P a =>
    have hs : (Finsupp.single P a : Mori.Divisor X) = a • Finsupp.single P 1 :=
      (Finsupp.smul_single_one _ _).symm
    rw [hs]
    simp only [map_zsmul, toQDivisor_single_one]
    congr 1
    rw [zCycle, Finsupp.linearCombination_single, one_smul, qCycle,
      Finsupp.linearCombination_single, one_smul]
    split_ifs with h
    · rw [Chow.cycleClass_pointCycle, Chow.rationalCycleClass_rationalPointCycle]
    · simp

/-- The class of the fundamental cycle of an integral `X` is that of the prime cycle of its generic
point. -/
private theorem cycleClass_fundamentalCycle_eq [IsIntegral X] {n : ℕ}
    (hgen : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
      (_root_.genericPoint X) = (n : ℤ)) :
    Chow.cycleClass ℚ n
        (Stacks.Chow.fundamentalCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n) =
      Chow.rationalCycleClass X n
        (Chow.rationalPointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (n : ℤ)
          (_root_.genericPoint X) hgen) := by
  rw [Chow.rationalCycleClass_rationalPointCycle, Stacks.Chow.fundamentalCycle,
    cycleAssociatedToClosedSubscheme_id_eq_pointCycle hgen, Chow.cycleClass_pointCycle]

variable {S : Scheme.{0}} [S.Over (Spec (.of ℂ))] [IsComplexScheme S] (f : S ⟶ X)
  [f.IsOver (Spec (.of ℂ))] [IsClosedImmersion f]

/-- `S ×_X X`, read in `X(ℂ)`, is `S(ℂ)` through the first projection. -/
private theorem fibreSquarePointsHom_flip_eq :
    fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 X)).flip =
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst f (𝟙 X))) ≫
        fibreSquarePointsHom (IsPullback.id_vert f) := by
  ext p
  change p.toHom ≫ pullback.snd f (𝟙 X) = (p.toHom ≫ pullback.fst f (𝟙 X)) ≫ f
  rw [Category.assoc, pullback.condition, Category.comp_id]

/-- The class of the fundamental cycle of `S ×_X X`, pushed forward to `X(ℂ)`, is that of `S`. -/
private theorem pushforward_cycleClass_fundamentalCycle_fibreProduct (n : ℕ) :
    borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 X)).flip)
        (isProperMap_fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 X)).flip) (2 * n : ℕ)
        (Chow.cycleClass (X := pullback f (𝟙 X)) ℚ n
          (Stacks.Chow.fundamentalCycle (fieldChowSituation ℂ)
            (pullback f (𝟙 X) ↘ Spec (.of ℂ)) n)) =
      borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreSquarePointsHom (IsPullback.id_vert f))
        (isProperMap_fibreSquarePointsHom (IsPullback.id_vert f)) (2 * n : ℕ)
        (Chow.cycleClass ℚ n
          (Stacks.Chow.fundamentalCycle (fieldChowSituation ℂ) (S ↘ Spec (.of ℂ)) n)) := by
  have key : ∀ (φ ψ : TopCat.of (UnderlyingSpace ℂ (pullback f (𝟙 X))) ⟶
      TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f))) (hφ : IsProperMap φ) (hψ : IsProperMap ψ),
      φ = ψ → borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) φ hφ (2 * n : ℕ) =
        borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) ψ hψ (2 * n : ℕ) := by
    rintro φ ψ hφ hψ rfl
    rfl
  rw [key _ _ _ ((isProperMap_fibreSquarePointsHom (IsPullback.id_vert f)).comp
      (isProperMap_map (K := ℂ) (pullback.fst f (𝟙 X)))) (fibreSquarePointsHom_flip_eq f),
    borelMooreHomology.pushforward_comp ℚ (ModuleCat.of ℚ ℚ) _ _ (isProperMap_map (K := ℂ) _)
      (isProperMap_fibreSquarePointsHom _), ModuleCat.comp_apply,
    ← Chow.cycleClass_properPushforward]
  congr 2
  rw [Stacks.Chow.fundamentalCycle,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    Stacks.Chow.fundamentalCycle]
  exact cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso (pullback.fst f (𝟙 X)))
    (by simp) _

variable {f} in
/-- **Fulton's `u ∩ cl[X] = cl[S]`** for a regular closed immersion `f : S ⟶ X` of codimension
`e` with orientation class `u`, when `dim_δ X ≤ N`: Theorem 19.2 at `α = [X]_N`, with
`f^![X]_N = [S ×_X X]_{N-e}` (Stacks 0FBM at vanishing excess). -/
private theorem capProductSupportPullback_cycleClass_fundamentalCycle_eq {k e : ℕ}
    (hf : IsRegularClosedImmersionOfCodim f e) (N : ℕ) (hN : k + 1 + e = N)
    (hX : schemeDeltaDimension (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ≤ ((N : ℤ) : EInt))
    {u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ X))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * e : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass ℚ f e u) :
    capProductSupportPullback ℚ (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X)))
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
        (hasProperNeighbourhoodDeformations_preimage_range_map f (𝟙 X))
        ((2 * e : ℕ) : ℤ) ((2 * N : ℕ) : ℤ) u
        (Chow.cycleClass ℚ N
          (Stacks.Chow.fundamentalCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) N)) =
      BorelMooreCross.congrDegree ℚ _ (by rw [← hN]; push_cast; ring)
        ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
          (fibreSquarePointsHom (IsPullback.id_vert f))
          (isProperMap_fibreSquarePointsHom (IsPullback.id_vert f)) (2 * (k + 1) : ℕ)).hom
          (Chow.cycleClass ℚ (k + 1)
            (Stacks.Chow.fundamentalCycle (fieldChowSituation ℂ) (S ↘ Spec (.of ℂ))
              (k + 1 : ℕ)))) := by
  subst hN
  have h := Chow.chowCycleMapRefinedGysinFormulaAt f (𝟙 X) ℚ hf hu (k + 1)
    (fundamentalChowClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (k + 1 + e : ℕ))
  unfold Chow.ChowCycleMapRefinedGysinFormulaAt at h
  rw [chowGroupCongr_fundamentalChowClass,
    regularNormalGysinClass_cap_fundamentalChowClass _ _ _ _ _ hf _ hX,
    Chow.chowGroupCongrDegree_fundamentalChowClass] at h
  erw [pushforward_cycleClass_fundamentalCycle_fibreProduct] at h
  rw [← Chow.chowCycleClass_fundamentalChowClass]
  erw [h]
  rw [congrDegree_congrDegree]
  rfl

/-- A set containing every point has proper neighbourhood deformations. -/
private theorem hasProperNeighbourhoodDeformations_of_forall_mem {Z : Type*} [TopologicalSpace Z]
    {A : Set Z} (hA : ∀ y, y ∈ A) : HasProperNeighbourhoodDeformations A := by
  rw [eq_univ_of_forall hA]
  exact hasProperNeighbourhoodDeformations_univ _

/-- The Gysin restriction of `m [L] = c₁(𝒪_X(M)) ∩ [X]` along a regular closed immersion
`f : S ⟶ X` is `f^* c₁(𝒪_X(M)) ∩ [S]`. -/
private theorem pushforward_congrDegree_capProductPullback_eq
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsLocallyNoetherian X]
    [IsNormal X] (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) {k e : ℕ}
    (hdim : topologicalKrullDim X = (k + e + 1 : ℕ))
    (L : Mori.QDivisor X) {m : ℕ} (hm : 0 < m) (M : Mori.Divisor X)
    (hM : Mori.Divisor.toQDivisor M = (m : ℤ) • L)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M.divisorialSheaf]
    {S : Scheme.{0}} [S.Over (Spec (.of ℂ))] [IsComplexScheme S] {f : S ⟶ X}
    [f.IsOver (Spec (.of ℂ))] [IsClosedImmersion f]
    (hf : IsRegularClosedImmersionOfCodim f e)
    {u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ X))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * e : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass ℚ f e u) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreSquarePointsHom (IsPullback.id_vert f))
        (isProperMap_fibreSquarePointsHom (IsPullback.id_vert f)) (2 * k : ℕ)).hom
        (BorelMooreCross.congrDegree ℚ (TopCat.of (UnderlyingSpace ℂ S))
          (by push_cast; ring : ((2 * (k + 1) : ℕ) : ℤ) - 2 = ((2 * k : ℕ) : ℤ))
          (borelMooreHomology.capProductPullback ℚ
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f) ≫
              TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
              TopCat.of (UnderlyingSpace ℂ S) ⟶ Analytification.space (X ↘ Spec (.of ℂ)))
            Set.univ 2 ((2 * (k + 1) : ℕ) : ℤ)
            (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
              (algebraicFirstChernClass M.divisorialSheaf))
            (Chow.cycleClass ℚ (k + 1)
              (Stacks.Chow.fundamentalCycle (fieldChowSituation ℂ) (S ↘ Spec (.of ℂ))
                (k + 1 : ℕ))))) =
      BorelMooreCross.congrDegree ℚ _ (two_mul_add_sub_two_mul_eq k e)
        (borelMooreHomology.capProductSupportPullback ℚ
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X)))
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
          (hasProperNeighbourhoodDeformations_preimage_range_map f (𝟙 X))
          ((2 * e : ℕ) : ℤ) ((2 * (k + e) : ℕ) : ℤ) u
          ((m : ℚ) • Chow.rationalCycleClass X (k + e)
            (Finsupp.linearCombination ℚ (fun P : Mori.PrimeDivisor X =>
              if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction
                  (X ↘ Spec (.of ℂ)) P.genericPoint = (k + e : ℕ) then
                Chow.rationalPointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (k + e : ℕ)
                  P.genericPoint h
              else 0) L))) := by
  haveI : IsIntegral X := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hX).1.toIsIntegral
  have hx := Chow.relativeDimension_genericPoint_eq ℂ (X ↘ Spec (.of ℂ)) hdim
  have hXd : schemeDeltaDimension (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ≤
      (((k + e + 1 : ℕ) : ℤ) : EInt) :=
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
      (X ↘ Spec (.of ℂ)) hdim).le
  have hF := capProductSupportPullback_cycleClass_fundamentalCycle_eq (k := k) hf (k + e + 1)
    (by omega) hXd hu
  rw [cycleClass_fundamentalCycle_eq hx] at hF
  have h1 := (smul_rationalCycleClass_eq_capProductPullback hX hsm hdim L hm M hM
    (_root_.genericPoint X) hx).1
  have hD : IsClosed (range (UnderlyingSpace.map (K := ℂ) f)) :=
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
  have hDd := hasProperNeighbourhoodDeformations_preimage_range_map f (𝟙 X)
  have hD' : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X))).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) f)) :=
    hD.preimage (UnderlyingSpace.map (K := ℂ) (𝟙 X)).continuous
  have hS : IsClosed ((anHom X).hom ⁻¹' univ) := isClosed_univ.preimage (anHom X).hom.continuous
  have hSall : ∀ y, y ∈ (anHom X).hom ⁻¹' univ := fun _ ↦ trivial
  have hDSd : HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f) ∩ (anHom X).hom ⁻¹' univ) := by
    rwa [inter_eq_left.2 fun x _ ↦ hSall x]
  have hSDd : HasProperNeighbourhoodDeformations ((anHom X).hom ⁻¹' univ ∩
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f)) := by
    rwa [inter_eq_right.2 fun x _ ↦ hSall x]
  have hSD' : HasProperNeighbourhoodDeformations (subsetInclusion ((anHom X).hom ⁻¹' univ) ⁻¹'
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f))) :=
    hDd.preimage_homeomorph
      ((Homeomorph.setCongr (eq_univ_of_forall hSall)).trans (Homeomorph.Set.univ _))
  have hDS'c : IsClosed (subsetInclusion
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f)) ⁻¹' ((anHom X).hom ⁻¹' univ)) :=
    hS.preimage (subsetInclusion _).hom.continuous
  have hs : (-1 : ℚˣ) ^ (((2 * e : ℕ) : ℤ) * 2) = 1 := (even_two.mul_left _).neg_one_zpow
  have hhq : (fibreSquarePointsHom (IsPullback.id_vert f) ≫ subsetInclusion _) ≫ anHom X =
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f) ≫ anHom X := rfl
  rw [h1, capProductSupportPullback_congrDegree_apply, capProductPullback_apply ℚ (anHom X),
    capProductSupportPullback_apply, capProductSupport_capProduct_eq ℚ _ hD' hS hDd
      (hasProperNeighbourhoodDeformations_of_forall_mem hSall) hDSd hSDd hSD'
      (hasProperNeighbourhoodDeformations_of_forall_mem fun _ ↦ trivial) _ hs,
    ← capProductSupportPullback_apply ℚ _ hD, hF, capProduct_congrDegree,
    ← pushforward_capProduct_pullback ℚ _ (isProperMap_fibreSquarePointsHom _) hDS'c
      (hasProperNeighbourhoodDeformations_of_forall_mem fun _ ↦ trivial)
      (hasProperNeighbourhoodDeformations_of_forall_mem fun _ ↦ trivial),
    capProduct_pullback_pullback, capProduct_pullback_pullback, capProduct_pullback_congr ℚ hhq,
    pushforward_congrDegree, capProductPullback_apply]
  simp only [congrDegree_congrDegree ℚ]

/-- **Compatibility of the Cartier divisor dictionary with Gysin restriction.** Let `X` be a smooth
projective complex variety of dimension `k + e + 1`, `L` a `ℚ`-divisor on `X` and `M = mL` an
integral divisor with `m > 0`, and let `f : S → X` be a regular closed immersion of codimension `e`
(a transverse smooth slice, or for `e = 1` a divisor of the smooth ambient `X`), with orientation
class `u ∈ H^{2e}(X, X - S)` and Gysin map `u ∩ - : H_{2k+2e}(X, ℚ) → H_{2k}(S, ℚ)`. Then:
* the Gysin restriction of `m [L]` to `S` is the class of the restricted divisor,
  `u ∩ m [L] = cl(f^! M)`, `f^! M = c(S ⟶ X, 𝒩) ∩ [M]` the refined Gysin image of the class of
  the cycle of `M` (the cycle of `M|_S` for a transverse slice);
* the Gysin restriction of `m [L] = c₁(𝒪_X(M)) ∩ [X]` is the restricted Chern class capped with
  the fundamental class of `S`: `u ∩ m [L] = f^* c₁(𝒪_X(M)) ∩ [S]`.
Both sides are read in `H_{2k}(f(S(ℂ)))`, through `S(ℂ) ≅ f(S(ℂ))` and `(S ×_X X)(ℂ) ≅ f(S(ℂ))`. -/
@[mmp "lem_mmp_conductor_smooth_cartier_dictionary"]
public theorem pushforward_refinedGysin_eq_capProductSupportPullback_smul_rationalCycleClass
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsLocallyNoetherian X]
    [IsNormal X] (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) {k e : ℕ}
    (hdim : topologicalKrullDim X = (k + e + 1 : ℕ))
    (L : Mori.QDivisor X) {m : ℕ} (hm : 0 < m) (M : Mori.Divisor X)
    (hM : Mori.Divisor.toQDivisor M = (m : ℤ) • L)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M.divisorialSheaf]
    {S : Scheme.{0}} [S.Over (Spec (.of ℂ))] [IsComplexScheme S] {f : S ⟶ X}
    [f.IsOver (Spec (.of ℂ))] [IsClosedImmersion f]
    (hf : IsRegularClosedImmersionOfCodim f e)
    {u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ X))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * e : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass ℚ f e u) :
    borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 X)).flip)
        (isProperMap_fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 X)).flip) (2 * k : ℕ)
        (Chow.chowCycleClass (X := pullback f (𝟙 X)) ℚ k
          (chowGroupCongrDegree (fieldChowSituation ℂ) (pullback.fst f (𝟙 X) ≫ S ↘ Spec (.of ℂ))
            (natCast_add_sub_natCast k e)
            ((regularNormalGysinClass (fieldChowSituation ℂ) (S ↘ Spec (.of ℂ))
                (X ↘ Spec (.of ℂ)) f (comp_over f _) hf).cap (𝟙 X) ((k + e : ℕ) : ℤ)
              (chowGroupCongr (fieldChowSituation ℂ) (q := X ↘ Spec (.of ℂ))
                (q' := 𝟙 X ≫ X ↘ Spec (.of ℂ)) (comp_over (𝟙 X) _).symm ((k + e : ℕ) : ℤ)
                (QuotientAddGroup.mk
                  (Finsupp.linearCombination ℤ (fun P : Mori.PrimeDivisor X =>
                    if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction
                        (X ↘ Spec (.of ℂ)) P.genericPoint = (k + e : ℕ) then
                      pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (k + e : ℕ)
                        P.genericPoint h
                    else 0) M) :
                  chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((k + e : ℕ) : ℤ)))))) =
      BorelMooreCross.congrDegree ℚ _ (two_mul_add_sub_two_mul_eq k e)
        (borelMooreHomology.capProductSupportPullback ℚ
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X)))
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
          (hasProperNeighbourhoodDeformations_preimage_range_map f (𝟙 X))
          ((2 * e : ℕ) : ℤ) ((2 * (k + e) : ℕ) : ℤ) u
          ((m : ℚ) • Chow.rationalCycleClass X (k + e)
            (Finsupp.linearCombination ℚ (fun P : Mori.PrimeDivisor X =>
              if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction
                  (X ↘ Spec (.of ℂ)) P.genericPoint = (k + e : ℕ) then
                Chow.rationalPointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (k + e : ℕ)
                  P.genericPoint h
              else 0) L))) ∧
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreSquarePointsHom (IsPullback.id_vert f))
        (isProperMap_fibreSquarePointsHom (IsPullback.id_vert f)) (2 * k : ℕ)).hom
        (BorelMooreCross.congrDegree ℚ (TopCat.of (UnderlyingSpace ℂ S))
          (by push_cast; ring : ((2 * (k + 1) : ℕ) : ℤ) - 2 = ((2 * k : ℕ) : ℤ))
          (borelMooreHomology.capProductPullback ℚ
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f) ≫
              TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
              TopCat.of (UnderlyingSpace ℂ S) ⟶ Analytification.space (X ↘ Spec (.of ℂ)))
            Set.univ 2 ((2 * (k + 1) : ℕ) : ℤ)
            (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
              (algebraicFirstChernClass M.divisorialSheaf))
            (Chow.cycleClass ℚ (k + 1)
              (Stacks.Chow.fundamentalCycle (fieldChowSituation ℂ) (S ↘ Spec (.of ℂ))
                (k + 1 : ℕ))))) =
      BorelMooreCross.congrDegree ℚ _ (two_mul_add_sub_two_mul_eq k e)
        (borelMooreHomology.capProductSupportPullback ℚ
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X)))
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
          (hasProperNeighbourhoodDeformations_preimage_range_map f (𝟙 X))
          ((2 * e : ℕ) : ℤ) ((2 * (k + e) : ℕ) : ℤ) u
          ((m : ℚ) • Chow.rationalCycleClass X (k + e)
            (Finsupp.linearCombination ℚ (fun P : Mori.PrimeDivisor X =>
              if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction
                  (X ↘ Spec (.of ℂ)) P.genericPoint = (k + e : ℕ) then
                Chow.rationalPointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (k + e : ℕ)
                  P.genericPoint h
              else 0) L))) := by
  have hq : (m : ℚ) • qCycle X (k + e) L = qCycle X (k + e) (Mori.Divisor.toQDivisor M) := by
    rw [hM, ← map_smul]
    congr 1
  refine ⟨?_, pushforward_congrDegree_capProductPullback_eq hX hsm hdim L hm M hM hf hu⟩
  have h := Chow.chowCycleMapRefinedGysinFormulaAt f (𝟙 X) ℚ hf hu k
    (QuotientAddGroup.mk (zCycle X (k + e) M) :
      chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((k + e : ℕ) : ℤ))
  unfold Chow.ChowCycleMapRefinedGysinFormulaAt at h
  rwa [Chow.chowCycleClass_mk, cycleClass_zCycle, ← hq, map_smul] at h

end Gysin

end MMP.Fourfold
