module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.SncFibreHomologyThree
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFibreGeneric
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafInvertible
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothModelOverPerfectField

/-!
# Degrees on the curves of the general fibres of a curve-image component

An invertible sheaf `N` on a complex scheme whose first Chern class vanishes in `H²(X^an; ℚ)` has
degree zero on every proper curve `C ⊆ X`, singular or not: the degree is computed on the
normalization `C̃` of `C`, a smooth projective curve birational onto `C`, where `c₁` is natural
under pull-back and the degree is `c₁ ∩ [C̃]`. On a smooth projective variety the Cartier divisor
dictionary `[W] = c₁(𝒪(W)) ∩ [X]` turns a divisor with homologically trivial cycle into one with
rationally trivial `c₁`.

Let `r : Z ⟶ Y` be a curve-and-point exceptional model, `E` a component of the exceptional divisor
whose image is a curve, and `M = ∑ c_P P` a `ℚ`-divisor on `E`. Over a general closed point `y` of
`r(E)`, every proper curve `C ⊆ E` over `y` lies in a component `G` of the fibre `E_y`. When `G`
is a smooth projective surface and the restriction of `𝒪_E(P)` to `G` is the sheaf of a Cartier
divisor whose Weil divisor has class `∑_{C' ⊆ G ∩ P} [C']`, the vanishing of
`∑ c_P ∑_{C'} [C']` in `H_2(G, ℚ)` gives `∑ c_P deg_C 𝒪_E(P) = 0`.

## Main results

* `invertibleCurveDegree_eq_zero_of_isIntegral_of_mapCoeff_algebraicFirstChernClass_eq_zero`,
  `MMP.Fourfold.degreeOn_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero`,
  `MMP.Mori.ProperCurve.degree_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero`: a
  rationally trivial `c₁` has degree zero on every integral proper curve.
* `MMP.Fourfold.degreeOn_divisorialSheaf_eq_zero_of_rationalCycleClass_eq_zero`: on a smooth
  projective variety, a divisor with homologically trivial cycle has degree zero on every curve.
* `MMP.Fourfold.degreeOn_sum_zsmul`: the degree of an integral combination of Cartier divisors.
* `MMP.Mori.ProperCurve.sum_degree_eq_zero_of_factor_smooth_surface`: on a smooth projective
  surface through which a curve factors, homologically trivial combinations of the restricted
  divisors have vanishing total degree.
* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_opens_sum_degree_eq_zero_of_fibre_of_restrict`:
  the fibre degrees vanish, given the restriction of the divisors to the general fibre
  components.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MMP
open MMP.Intersection.Scheme (Subvariety)
open MMP.Intersection (hasDim_natCast_iff)
open MMP.Mori MMP.Analytic TopologicalSpace

namespace MMP.Fourfold

section Normalization

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Rationally trivial `c₁` has degree zero on an integral proper curve.** Let `C` be an
integral complex curve, proper over `ℂ`, and `N` an invertible sheaf on `C` whose first Chern
class vanishes in `H²(C^an; ℚ)`. Then `deg N = 0`. -/
theorem invertibleCurveDegree_eq_zero_of_isIntegral_of_mapCoeff_algebraicFirstChernClass_eq_zero
    {C : Scheme.{0}} [C.Over (Spec (.of ℂ))] [IsIntegral C] [IsProper (C ↘ Spec (.of ℂ))]
    (hdim : topologicalKrullDim C = 1)
    (N : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N]
    (hN : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N) = 0) :
    invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim.le N = 0 := by
  let p := C ↘ Spec (.of ℂ)
  have hp : IsProper p := ‹_›
  have : AlgebraicGeometry.IsVariety ℂ p :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  have : AlgebraicGeometry.IsCurve ℂ p := ⟨hdim⟩
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType ℂ p
  have hvar : AlgebraicGeometry.IsVariety ℂ (normalizationOverField ℂ p ≫ p) :=
    isVariety_normalizationOverField ℂ p
  have : IsIntegral (normalizationSchemeOverField ℂ p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField ℂ p) := isFinite_normalizationOverField ℂ p
  have : IsDominant (normalizationOverField ℂ p) := isDominant_normalizationOverField ℂ p
  have hbir : MMP.Mori.IsBirationalMorphism (normalizationOverField ℂ p) :=
    Oai4C1.CommonModel.isBirationalMorphism_of_isBirational _
      (Scheme.isBirational_normalization C hX)
  have hdim' : topologicalKrullDim (normalizationSchemeOverField ℂ p) = 1 :=
    (normalizationModel' ℂ p).isCurve.topologicalKrullDim_eq_one
  have : AlgebraicGeometry.IsCurve ℂ (normalizationOverField ℂ p ≫ p) := ⟨hdim'⟩
  have hP : IsProper (normalizationOverField ℂ p ≫ p) := inferInstance
  have hnc : ¬ ∃ y : C, ∀ x : normalizationSchemeOverField ℂ p,
      (normalizationOverField ℂ p).base x = y := by
    rintro ⟨y, hy⟩
    have huniv : Set.range (normalizationOverField ℂ p) = Set.univ := by
      rw [← (normalizationOverField ℂ p).isClosedMap.isClosed_range.closure_eq,
        (normalizationOverField ℂ p).denseRange.closure_range]
    have : Subsingleton C := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
      obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
      exact (hy x).trans (hy x').symm⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C
    rw [hdim] at h0
    exact absurd h0 (by decide)
  have key := curveDegree_pullback_eq_degreeOver_mul ℂ (normalizationOverField ℂ p ≫ p) p
    (normalizationOverField ℂ p) rfl hnc N 1
  rw [Oai4C1.Negativity.degreeOver_eq_one _ hbir, Nat.cast_one, one_mul] at key
  rw [invertibleCurveDegree_eq_curveDegree_one, ← key,
    ← invertibleCurveDegree_eq_curveDegree_one]
  let : (normalizationSchemeOverField ℂ p).Over (Spec (.of ℂ)) :=
    ⟨normalizationOverField ℂ p ≫ p⟩
  have hproj : MMP.Mori.IsProjectiveVariety ℂ
      (normalizationSchemeOverField ℂ p ↘ Spec (.of ℂ)) :=
    (normalizationModel' ℂ p).isProjectiveVariety
  have : IsComplexScheme (normalizationSchemeOverField ℂ p) :=
    isComplexScheme_of_isProjectiveVariety _ hproj
  have : Smooth (normalizationSchemeOverField ℂ p ↘ Spec (.of ℂ)) :=
    (normalizationModel' ℂ p).smooth_structureMap
  have : IsProper (normalizationSchemeOverField ℂ p ↘ Spec (.of ℂ)) := hP
  have hsm : IsSmoothScheme (normalizationSchemeOverField ℂ p ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isSmoothScheme_iff _).2 inferInstance
  refine invertibleCurveDegree_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero hsm hdim'
    hproj ((Scheme.Modules.pullback (normalizationOverField ℂ p)).obj N) ?_
  rw [MMP.Analytic.algebraicFirstChernClass_pullback (normalizationOverField ℂ p)
    (MMP.Analytic.ComplexPoints.analyticMap (normalizationOverField ℂ p) rfl)
    (fun _ => rfl) N]
  refine (MMP.Analytic.singularCohomology.mapCoeff_relativeSingularCohomology_map
    (Int.castRingHom ℚ) _ _ 2 _).trans ?_
  rw [hN, map_zero]

/-- **Rationally trivial `c₁` has degree zero along every integral proper curve.** Let `X` be a
scheme over `ℂ`, `N` an invertible sheaf on `X` whose first Chern class vanishes in
`H²(X^an; ℚ)`, and `i : C ⟶ X` a morphism from an integral curve `C` proper over `ℂ`. Then
`deg_C i^* N = 0`. -/
theorem degreeOn_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero
    {X C : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsIntegral C] (i : C ⟶ X)
    [IsProper (i ≫ (X ↘ Spec (.of ℂ)))] (hdim : topologicalKrullDim C = 1)
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hN : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N) = 0) :
    degreeOn ℂ (X ↘ Spec (.of ℂ)) i hdim.le N = 0 := by
  let : C.Over (Spec (.of ℂ)) := ⟨i ≫ (X ↘ Spec (.of ℂ))⟩
  have : i.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : IsProper (C ↘ Spec (.of ℂ)) := ‹IsProper (i ≫ (X ↘ Spec (.of ℂ)))›
  refine invertibleCurveDegree_eq_zero_of_isIntegral_of_mapCoeff_algebraicFirstChernClass_eq_zero
    hdim _ ?_
  rw [MMP.Analytic.algebraicFirstChernClass_pullback i
    (MMP.Analytic.ComplexPoints.analyticMap i rfl) (fun _ => rfl) N]
  refine (MMP.Analytic.singularCohomology.mapCoeff_relativeSingularCohomology_map
    (Int.castRingHom ℚ) _ _ 2 _).trans ?_
  rw [hN, map_zero]

/-- **Rationally trivial `c₁` has degree zero on every proper curve.** Let `X` be a scheme over
`ℂ` and `N` an invertible sheaf on `X` whose first Chern class vanishes in `H²(X^an; ℚ)`. Then
`deg_C N = 0` for every proper curve `C ⊆ X`, singular or not. -/
theorem _root_.MMP.Mori.ProperCurve.degree_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (C : ProperCurve (X ↘ Spec (.of ℂ)))
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hN : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N) = 0) :
    C.degree ℂ N = 0 :=
  MMP.Fourfold.degreeOn_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero C.ι C.dim_eq N hN

open Classical in
/-- **A homologically trivial divisor on a smooth projective variety has degree zero on every
curve.** Let `X` be a smooth projective complex variety of dimension `d + 1` and `W` a divisor on
`X` whose `d`-cycle `∑ᵢ aᵢ [Pᵢ]` has zero class in `H_{2d}(X, ℚ)`. Then `deg_C i^* 𝒪_X(W) = 0`
for every integral proper curve `i : C ⟶ X`. -/
theorem degreeOn_divisorialSheaf_eq_zero_of_rationalCycleClass_eq_zero {X C : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) {d : ℕ}
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) (W : MMP.Mori.Divisor X)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 W.divisorialSheaf]
    (hW : Chow.rationalCycleClass X d
        (Finsupp.linearCombination ℚ (fun P : MMP.Mori.PrimeDivisor X =>
          if h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
              (X ↘ Spec (.of ℂ)) P.genericPoint = d then
            Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) d
              P.genericPoint h
          else 0) (MMP.Mori.Divisor.toQDivisor W)) = 0)
    [IsIntegral C] (i : C ⟶ X) [IsProper (i ≫ (X ↘ Spec (.of ℂ)))]
    (hdimC : topologicalKrullDim C = 1) :
    degreeOn ℂ (X ↘ Spec (.of ℂ)) i hdimC.le W.divisorialSheaf = 0 := by
  have : IsIntegral X := hX.toIsVariety.toIsIntegral
  have hξ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) (genericPoint X) = ((d + 1 : ℕ) : ℤ) :=
    MMP.Chow.relativeDimension_genericPoint_eq ℂ _ hdim
  exact degreeOn_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero i hdimC _
    ((smul_rationalCycleClass_eq_capProductPullback hX hsm hdim
      (MMP.Mori.Divisor.toQDivisor W) one_pos W (by simp) (genericPoint X) hξ).2.1 hW)

end Normalization

section DegreeSum

variable {k : Type} [Field k] {X C : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (i : C ⟶ X)
  [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- **The degree of an integral combination of Cartier divisors** along a curve is the
combination of the degrees: `deg_C 𝒪_X(∑ nᵢ Wᵢ) = ∑ nᵢ deg_C 𝒪_X(Wᵢ)`. -/
theorem degreeOn_sum_zsmul {ι : Type*} (s : Finset ι) (n : ι → ℤ) (W : ι → Divisor X)
    (hW : ∀ j, (W j).IsCartier) (h : (∑ j ∈ s, n j • W j).IsCartier) :
    (∑ j ∈ s, n j • W j).degreeOn k sX i hdim h =
      ∑ j ∈ s, n j * (W j).degreeOn k sX i hdim (hW j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Divisor.degreeOn_congr Finset.sum_empty h Divisor.isCartier_zero,
      Divisor.degreeOn_zero', Finset.sum_empty]
  | insert a s ha ih =>
    have hs : (∑ j ∈ s, n j • W j).IsCartier :=
      Finset.sum_induction _ Divisor.IsCartier (fun _ _ h₁ h₂ ↦ h₁.add h₂)
        Divisor.isCartier_zero fun j _ ↦ (hW j).zsmul (n j)
    rw [Divisor.degreeOn_congr (Finset.sum_insert ha) h
      (((hW a).zsmul (n a)).add hs), Divisor.degreeOn_add k sX i hdim _ _ ((hW a).zsmul (n a)) hs,
      degreeOn_zsmul sX i hdim (W a) (hW a) (n a), ih hs, Finset.sum_insert ha]

end DegreeSum

section Fibre

open scoped MMP.SubschemeOver

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat
  MMP.CartierDivisor.isInvertible_sheaf

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

open Classical in
/-- **The cycle class of an integral combination of divisors** vanishes when the classes `vᵢ` of
the `Wᵢ` satisfy `∑ cᵢ vᵢ = 0` and the coefficients are `nᵢ = N cᵢ`. -/
theorem rationalCycleClass_sum_zsmul_eq_zero {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] {d : ℕ} {ι : Type*} (s : Finset ι) (n : ι → ℤ) (W : ι → Divisor X)
    {c : ι → ℚ} {v : ι → Chow.BMHomology ℚ X (2 * d)} {N : ℚ}
    (hW : ∀ i, Chow.rationalCycleClass X d
      (Finsupp.linearCombination ℚ (fun Q : MMP.Mori.PrimeDivisor X =>
        if h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (X ↘ Spec (.of ℂ)) Q.genericPoint = (d : ℤ) then
          Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
            (d : ℤ) Q.genericPoint h
        else 0) (MMP.Mori.Divisor.toQDivisor (W i))) = v i)
    (hn : ∀ i, (n i : ℚ) = N * c i) (hv : ∑ i ∈ s, c i • v i = 0) :
    Chow.rationalCycleClass X d
      (Finsupp.linearCombination ℚ (fun Q : MMP.Mori.PrimeDivisor X =>
        if h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (X ↘ Spec (.of ℂ)) Q.genericPoint = (d : ℤ) then
          Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
            (d : ℤ) Q.genericPoint h
        else 0) (MMP.Mori.Divisor.toQDivisor (∑ i ∈ s, n i • W i))) = 0 := by
  rw [map_sum, map_sum, map_sum, Finset.sum_congr rfl fun i _ ↦ by
    rw [map_zsmul, map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, hW, hn, mul_smul],
    ← Finset.smul_sum, hv, smul_zero]

/-- **The degree along a curve that factors through a morphism.** If a proper curve `C ⊆ X` factors
as `j ≫ g` through `g : G ⟶ X`, and `g^* L ≅ 𝒪_G(D')` for a Cartier divisor `D'` with Weil divisor
`W`, then `deg_C L = deg_C 𝒪_G(W)`. -/
theorem _root_.MMP.Mori.ProperCurve.degree_eq_degreeOn_of_factor {k : Type} [Field k]
    {X G : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (g : G ⟶ X)
    (j : C.scheme ⟶ G) (hj : j ≫ g = C.ι) {sG : G ⟶ Spec (.of k)} (hsG : g ≫ sX = sG)
    [IsProper (j ≫ sG)] [QuasiCompact sG] [IsIntegral G]
    [IsLocallyNoetherian G] [IsNormal G] {L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (D' : G.CartierDivisor)
    (W : Divisor G) (hW : W.IsCartier)
    (e : (Scheme.Modules.pullback g).obj L ≅ MMP.CartierDivisor.sheaf D')
    (hDW : MMP.Intersection.IsWeilDivisorOfCartier D' W) :
    C.degree k L = W.degreeOn k sG j C.dim_le hW := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sG
  have : IsProper ((j ≫ g) ≫ sX) := by
    rw [hj]
    infer_instance
  have h1 := degreeOn_pullback_eq_degreeOn_comp sG sX g j hsG C.dim_le L
  have h2 : ∀ (i' : C.scheme ⟶ X) (h : i' = C.ι) [IsProper (i' ≫ sX)],
      degreeOn k sX i' C.dim_le L = C.degree k L := by
    rintro _ rfl _
    rfl
  have := hW.isInvertibleModule_divisorialSheaf
  rw [← h2 _ hj, ← h1, degreeOn_eq_of_iso k _ j C.dim_le e,
    degreeOn_eq_of_iso k _ j C.dim_le hDW.sheafIsoDivisorialSheaf]
  rfl

open Classical in
/-- **Degrees along a curve through a smooth projective surface.** If a proper curve `C ⊆ X`
factors through `g : G ⟶ X` with `G` a smooth projective surface, and for `P` in the support of a
`ℚ`-divisor `M = ∑ c_P P` the sheaf `g^* 𝒪(π P)` is that of a Cartier divisor whose Weil divisor
has class `v P` in `H_2(G, ℚ)`, then `∑ c_P v P = 0` gives `∑ c_P deg_C 𝒪(π P) = 0`. -/
theorem _root_.MMP.Mori.ProperCurve.sum_degree_eq_zero_of_factor_smooth_surface {X G : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [G.Over (Spec (.of ℂ))] (C : ProperCurve sX) (g : G ⟶ X)
    (j : C.scheme ⟶ G) (hj : j ≫ g = C.ι) (hsG : g ≫ sX = G ↘ Spec (.of ℂ)) [IsComplexScheme G]
    (hproj : MMP.Mori.IsProjectiveVariety ℂ (G ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (G ↘ Spec (.of ℂ)))
    (hdimG : topologicalKrullDim G = ((1 + 1 : ℕ) : WithBot ℕ∞))
    (π : MMP.Mori.PrimeDivisor X → X.CartierDivisor) (M : QDivisor X)
    (v : MMP.Mori.PrimeDivisor X → Chow.BMHomology ℚ G (2 * 1))
    (hW : ∀ P ∈ M.support, ∃ (D' : G.CartierDivisor) (W : Divisor G),
      Nonempty ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf (π P)) ≅
        MMP.CartierDivisor.sheaf D') ∧
      MMP.Intersection.IsWeilDivisorOfCartier D' W ∧
      Chow.rationalCycleClass G 1
          (Finsupp.linearCombination ℚ (fun Q : MMP.Mori.PrimeDivisor G =>
            if h : Stacks.Chow.relativeDimension
                (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (G ↘ Spec (.of ℂ)) Q.genericPoint = ((1 : ℕ) : ℤ) then
              Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
                (G ↘ Spec (.of ℂ)) ((1 : ℕ) : ℤ) Q.genericPoint h
            else 0) (MMP.Mori.Divisor.toQDivisor W)) = v P)
    (hv : M.sum (fun P c ↦ c • v P) = 0) :
    (M.sum fun P a ↦ a * (C.degree ℂ (MMP.CartierDivisor.sheaf (π P)) : ℚ)) = 0 := by
  have : IsProper (j ≫ (G ↘ Spec (.of ℂ))) := by
    rw [← hsG, ← Category.assoc, hj]
    infer_instance
  have : IsIntegral G := hproj.toIsVariety.toIsIntegral
  have : QuasiCompact (G ↘ Spec (.of ℂ)) := hproj.toIsVariety.toQuasiCompact
  have : Smooth (G ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have : IsNormal G := isNormal_of_smooth_over_field (G ↘ Spec (.of ℂ))
  have : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (G ↘ Spec (.of ℂ))
  have : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace (G ↘ Spec (.of ℂ))
  have hcart : ∀ W : Divisor G, W.IsCartier := isCartier_of_isSmoothScheme hsm
  choose D' W he hDW hcl using hW
  obtain ⟨N, hN, M', hM'⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor M
  have hcoef : ∀ P, (M' P : ℚ) = N * M P := fun P => by
    simpa [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffs, zsmul_eq_mul] using
      congrArg (fun L : QDivisor X => L P) hM'
  set MG : Divisor G := ∑ P ∈ M.support.attach, M' P.1 • W P.1 P.2
  have hclass := MMP.Fourfold.rationalCycleClass_sum_zsmul_eq_zero M.support.attach (fun P ↦ M' P.1)
    (fun P ↦ W P.1 P.2) (fun P ↦ hcl P.1 P.2) (fun P ↦ hcoef P.1)
    (by rwa [Finsupp.sum, ← Finset.sum_attach] at hv)
  have := (hcart MG).isInvertibleModule_divisorialSheaf
  have h0 := MMP.Fourfold.degreeOn_divisorialSheaf_eq_zero_of_rationalCycleClass_eq_zero hproj hsm
    hdimG MG hclass j C.dim_eq
  have hsum := MMP.Fourfold.degreeOn_sum_zsmul (k := ℂ) (G ↘ Spec (.of ℂ)) j C.dim_le
    M.support.attach (fun P ↦ M' P.1) (fun P ↦ W P.1 P.2) (fun P ↦ hcart _) (hcart MG)
  change MG.degreeOn ℂ _ j C.dim_le (hcart MG) = 0 at h0
  rw [h0] at hsum
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine (mul_eq_zero.1 ?_).resolve_left hN'
  rw [Finsupp.sum, Finset.mul_sum, ← Finset.sum_attach M.support]
  have := congrArg (fun z : ℤ ↦ (z : ℚ)) hsum
  push_cast at this
  rw [this]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  rw [C.degree_eq_degreeOn_of_factor g j hj hsG (D' P.1 P.2) (W P.1 P.2)
    (hcart _) (he P.1 P.2).some (hDW P.1 P.2), hcoef]
  ring

/-- The image of the support of a prime divisor under a universally closed morphism is
irreducible and closed. -/
theorem isIrreducible_and_isClosed_image_support {X S : Scheme.{0}} (f : X ⟶ S)
    [UniversallyClosed f] (P : AlgebraicGeometry.PrimeDivisor X) :
    IsIrreducible (f.base '' (P.support : Set X)) ∧ IsClosed (f.base '' (P.support : Set X)) := by
  refine ⟨?_, f.isClosedMap _ P.idealSheaf.support.isClosed⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact isIrreducible_singleton.closure.image _ f.continuous.continuousOn

open Classical in
/-- **Fibre degrees from the restriction to the general fibre components.** Let `r : Z ⟶ Y` be a
curve-and-point exceptional model, `E` a component of `F` mapping onto a curve, `π P` a Cartier
divisor on `E` for each prime divisor `P` of `E`, and `M = ∑ c_P P` a `ℚ`-divisor on `E`. Suppose
that over the closed points `y` of an open `U₁` meeting `r(E)` every component `G` of the fibre
`E_y` is a smooth projective surface on which, for `P` in the support of `M`, `𝒪_E(π P)|_G` is the
sheaf of a Cartier divisor whose Weil divisor `W` has class `∑_{C' ⊆ G ∩ P} [C']` in `H_2(G, ℚ)`
(`C'` running over the maximal irreducible subsets of `G ∩ P`). If `∑ c_P ∑_{C'} [C'] = 0` in
`H_2(G, ℚ)` for every such `G` over the closed points of an open `U₀` meeting `r(E)`, then over an
open `U` meeting `r(E)`, `∑ c_P deg_C 𝒪_E(π P) = 0` for every proper curve `C ⊆ E` over a closed
point of `U`. -/
theorem IsCurvePointExceptionalModel.exists_opens_sum_degree_eq_zero_of_fibre_of_restrict
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support)
    (hE : topologicalKrullDim (r.base '' (E.1.support : Set Z)) = 1)
    (π : MMP.Mori.PrimeDivisor E.1.idealSheaf.subscheme → E.1.idealSheaf.subscheme.CartierDivisor)
    (M : QDivisor E.1.idealSheaf.subscheme)
    (hgen : ∃ U : Y.Opens, ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty ∧
      ∀ y ∈ (U : Set Y) ∩ r.base '' (E.1.support : Set Z), IsClosed {y} →
        ∀ G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          MMP.Mori.IsProjectiveVariety ℂ (G.1.toScheme ↘ Spec (.of ℂ)) ∧
          MMP.Mori.IsSmoothScheme (G.1.toScheme ↘ Spec (.of ℂ)) ∧
          ∀ P ∈ M.support, ∃ (D' : G.1.toScheme.CartierDivisor) (W : Divisor G.1.toScheme),
            Nonempty ((Scheme.Modules.pullback G.1.ι).obj (MMP.CartierDivisor.sheaf (π P)) ≅
              MMP.CartierDivisor.sheaf D') ∧
            MMP.Intersection.IsWeilDivisorOfCartier D' W ∧
            Chow.rationalCycleClass G.1.toScheme 1
                (Finsupp.linearCombination ℚ (fun Q : MMP.Mori.PrimeDivisor G.1.toScheme =>
                  if h : Stacks.Chow.relativeDimension
                      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                      (G.1.toScheme ↘ Spec (.of ℂ)) Q.genericPoint = ((1 : ℕ) : ℤ) then
                    Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
                      (G.1.toScheme ↘ Spec (.of ℂ)) ((1 : ℕ) : ℤ) Q.genericPoint h
                  else 0) (MMP.Mori.Divisor.toQDivisor W)) =
              ∑ᶠ (x : {x : G.1.toScheme //
                Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                  (G.1.toScheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
                (_ : Maximal (fun A ↦ IsIrreducible A ∧
                    A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
                Chow.pointCycleClass ℚ x.1 x.2)
    (hvan : ∃ U : Y.Opens, ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty ∧
      ∀ y ∈ (U : Set Y) ∩ r.base '' (E.1.support : Set Z), IsClosed {y} →
        ∀ G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          M.sum (fun P c ↦ c •
            ∑ᶠ (x : {x : G.1.toScheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (G.1.toScheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
              (_ : Maximal (fun A ↦ IsIrreducible A ∧
                  A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) = 0) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty ∧
      ∀ C : ProperCurve (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)),
        (E.1.idealSheaf.subschemeι ≫ r).base C.point ∈ U →
        IsClosed {(E.1.idealSheaf.subschemeι ≫ r).base C.point} →
        (M.sum fun P a ↦ a * (C.degree ℂ (MMP.CartierDivisor.sheaf (π P)) : ℚ)) = 0 := by
  classical
  have : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  obtain ⟨U₀, hU₀, hvan⟩ := hvan
  obtain ⟨U₁, hU₁, hgen⟩ := hgen
  set ι := E.1.idealSheaf.subschemeι
  obtain ⟨hKirr, hKcl⟩ := isIrreducible_and_isClosed_image_support r E.1
  let T : IrreducibleCloseds Y := ⟨_, hKirr, hKcl⟩
  obtain ⟨U₂, hU₂, hdisj⟩ := exists_disjoint_maximal_fibre_of_mem hr T hE E
  refine ⟨U₀ ⊓ U₁ ⊓ U₂, inter_inter_nonempty_of_irreducibleCloseds T
    (inter_inter_nonempty_of_irreducibleCloseds T hU₀ hU₁) hU₂, ?_⟩
  intro C hCU hCcl
  set y := (ι ≫ r).base C.point
  have hyK : y ∈ r.base '' (E.1.support : Set Z) := by
    refine ⟨ι.base C.point, ?_, rfl⟩
    have : ι.base C.point ∈ Set.range ι.base := ⟨_, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at this
  have hFcl : IsClosed ((ι ≫ r).base ⁻¹' {y}) := hCcl.preimage (ι ≫ r).base.hom.continuous
  have hs : closure {C.point} ⊆ (ι ≫ r).base ⁻¹' {y} :=
    closure_minimal (Set.singleton_subset_iff.2 rfl) hFcl
  obtain ⟨A, hsA, hA⟩ :=
    exists_subset_maximal_of_isIrreducible isIrreducible_singleton.closure hs
  have hAcl : IsClosed A := isClosed_of_maximal hFcl hA
  let G₀ : Subvariety E.1.idealSheaf.subscheme :=
    Subvariety.ofIrreducibleCloseds ⟨A, hA.1.1, hAcl⟩
  have hG₀ : (G₀.support : Set _) = A :=
    Subvariety.support_ofIrreducibleCloseds _
  have hdimA := (hdisj y ⟨hCU.2, hyK⟩).2 A hA
  let G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} := ⟨G₀, by
    have h := Subvariety.dim_eq_topologicalKrullDim_support G₀
    rw [hG₀] at h
    exact (hasDim_natCast_iff 2).2 (h.trans hdimA)⟩
  have hGA : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (ι ≫ r).base ⁻¹' {y})
      (G.1.support : Set _) := hG₀ ▸ hA
  obtain ⟨hproj, hsm, hW⟩ := hgen y ⟨hCU.1.2, hyK⟩ hCcl G hGA
  have hv := hvan y ⟨hCU.1.1, hyK⟩ hCcl G hGA
  have hker : G.1.ι.ker ≤ C.ι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    change closure {C.point} ⊆ (G.1.support : Set _)
    rw [show (G.1.support : Set _) = A from hG₀]
    exact hsA
  let j : C.scheme ⟶ G.1.toScheme := IsClosedImmersion.lift G.1.ι C.ι hker
  have hj : j ≫ G.1.ι = C.ι := IsClosedImmersion.lift_fac _ _ _
  exact C.sum_degree_eq_zero_of_factor_smooth_surface G.1.ι j hj rfl hproj hsm
    ((hasDim_natCast_iff 2).1 G.2) π M _ hW hv

end Fibre

end MMP.Fourfold
