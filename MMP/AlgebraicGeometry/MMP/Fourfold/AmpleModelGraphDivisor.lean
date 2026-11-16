module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelAdjointAmple
import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelBirational
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorBranchCounts
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# The ample model of a birational contraction of an lc fourfold

Let `(X, B)` be a projective lc fourfold pair over `ℂ` with rational boundary and canonical
divisor `K_X`, `D = K_X + B`, `f : X ⟶ Z` a birational contraction onto a normal projective
variety with `-D` `f`-ample, and `(M, B_M, q, V, B_V)` an ample-model datum for `f`, with
structure morphism `p : V ⟶ Z`. Let `K_V` be the canonical divisor of `V` compatible with `K_X`,
`(G, u, v)` the normalization of the graph of the birational map `X ⤏ V` over `Z`, and
`H = u^* D - v^*(K_V + B_V)` the graph divisor, with `g = u ≫ f : G ⟶ Z`.

The divisor `-H` is the pull-back of the `Z`-ample divisor `pr₁^*(-D) + pr₂^*(K_V + B_V)` along
the finite morphism `(u, v) : G ⟶ X ×_Z V`, so it is ample over `Z`. Its push-forward to `Z`
vanishes: a prime divisor of `Z` has strict transforms on `X`, `V` and `M`, at which the
coefficients of `K + B`, `K_V + B_V` and `K_M + B_M` agree. The negativity lemma then gives
`H ≥ 0`. A prime divisor of `V` has a strict transform `E` on `G`; log canonicity of `(X, B)`
bounds the coefficient of `E` in `H` from above by `0`, so `v_* H = 0`. Through a closed point
of a fibre of `g` over a point outside the biregular loci of `f` and `p` passes a curve
contracted by `g`, on which `-H` has positive degree; so the whole fibre lies in `Supp H`.
Finally `q : M ⟶ V` is crepant for `K_M + B_M = q^*(K_V + B_V)`, so every log discrepancy of
`(V, B_V)` is one of the dlt pair `(M, B_M)`, and `(V, B_V)` is lc.

## Main results

* `MMP.Fourfold.IsAmpleModelDatum.transformDivisor_pullback_sub_pullback_eq_zero`:
  `v_*(u^* D - v^*(K_V + B_V)) = 0`.
* `MMP.Fourfold.IsAmpleModelDatum.isEffective_pullback_sub_pullback`: the graph divisor is
  effective.
* `MMP.Fourfold.IsAmpleModelDatum.preimage_singleton_subset_supp_pullback_sub_pullback`: the
  fibre of `G ⟶ Z` over a point outside the common biregular locus of `f` and `p` lies in the
  support of the graph divisor.
* `MMP.Fourfold.IsAmpleModelDatum.isLogCanonicalPair_ampleModel`: `(V, B_V)` is lc.

## Implementation notes

* The birational map `X ⤏ V` is `p⁻¹ ∘ f`, so the normalization of its graph is a normalized
  graph of `f` and `p` (`MMP.Fourfold.IsNormalizedGraph`): a normal integral `G` with birational
  `u`, `v`, `f ∘ u = p ∘ v` and `(u, v) : G ⟶ X ×_Z V` finite.
* The graph divisor depends on the canonical divisors, not only on their linear equivalence
  classes: `K_X` and `K_V` must be cut out by the same rational top form. This is expressed as
  `p_* K_V = f_* K_X` on `Z`, which determines `K_V` among the canonical divisors of `V`.
* The pull-backs are `MMP.Mori.QDivisor.pullback` of `ℚ`-Cartier `ℚ`-divisors; that `D` and
  `K_V + B_V` are `ℚ`-Cartier, and that `u` and `v` send the generic point of `G` outside their
  supports, are part of each conclusion.
* The push-forward `v_*` is the birational transform `MMP.Mori.RationalMap.transformDivisor`
  along `v.toRationalMap`.
* `z` is an arbitrary scheme point of `Z`, and the fibre is the set-theoretic preimage
  `(u ≫ f) ⁻¹' {z}`; for closed points this is the source's statement, and the general case
  follows since the support is closed and closed points are dense in closed subsets of `G`.
* The source passes to a smooth projective model `W` of `G` and compares there with the log
  minimal model `M`. Here every comparison is made on `G` itself, and log canonicity of
  `(V, B_V)` is compared with `(M, B_M)` directly along `q`; every divisor over `V` is realized
  over `M` by the valuative criterion of properness.
* `V` is a variety over `ℂ` through `p ≫ s_Z`; to form divisors on `V` and `G` the schemes are
  assumed normal and locally Noetherian, as holds for the relative ample model and the
  normalized graph of projective varieties.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4]
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

section Helpers

variable {X Y T : Scheme.{u}}

/-- Let `E ⊆ X`, `P ⊆ Y` be prime divisors with `f(η_E) = η_P` and `f^♯ : 𝒪_{Y,P} ≅ 𝒪_{X,E}`.
The coefficient of `E` in the pull-back of a `ℚ`-Cartier `ℚ`-divisor `B` is that of `P` in
`B`. -/
private theorem coeff_pullback_eq_of_isIso [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = P.genericPoint) [IsIso (f.stalkMap E.genericPoint)]
    {B : QDivisor Y} (hBq : B.IsQCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp) :
    B.pullback hBq hB E = B P := by
  have hB' := QDivisor.isPullback_pullback hBq hB
  have hm := QDivisor.cartierIndex_pos hBq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hBq
  obtain ⟨D', hD', hp⟩ := hB' _ hm D₀ hD₀ hD₀c
  have hc := MMP.Positivity.coeff_eq_of_isPullback E P heq hD₀c hp
  have h1 := congrArg (fun G : QDivisor X => G E) hD'
  have h2 := congrArg (fun G : QDivisor Y => G P) hD₀
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1 h2
  refine mul_left_cancel₀ (by exact_mod_cast hm.ne') (h1.symm.trans (Eq.trans ?_ h2))
  exact congrArg (fun z : ℤ => (z : ℚ)) hc

/-- Functoriality of the pull-back of rational functions along dominant morphisms. -/
private theorem functionFieldMap_comp_apply [IsIntegral X] [IsIntegral Y] [IsIntegral T]
    (a : X ⟶ Y) (b : Y ⟶ T) [IsDominant a] [IsDominant b] {c : X ⟶ T} [IsDominant c]
    (hc : a ≫ b = c) (t : T.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap c t := by
  subst hc
  obtain ⟨s, rfl⟩ := MMP.Positivity.DivisorOver.algebraMap_stalk_surjective_of_eq_genericPoint
    ((a ≫ b) (genericPoint X)) (map_genericPoint_of_isDominant (a ≫ b)) t
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk (a ≫ b) (genericPoint X) s]
  erw [MMP.Mori.functionFieldMap_algebraMap_stalk b (a (genericPoint X)) s,
    MMP.Mori.functionFieldMap_algebraMap_stalk a (genericPoint X)]
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- If `h(η_E) = η_P` and `h^♯ : 𝒪_{Y,P} ≅ 𝒪_{X,E}`, then `E` and `P` define the same valuation
of `k(T)` for any dominant `t : Y ⟶ T`. -/
private theorem valuationOver_eq_of_isIso [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] (h : X ⟶ Y) (t : Y ⟶ T)
    {c : X ⟶ T} [IsDominant h] [IsDominant t] [IsDominant c] (hc : h ≫ t = c)
    (E : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor Y)
    (heq : h E.genericPoint = P.genericPoint)
    [IsIso (h.stalkMap E.genericPoint)] :
    E.valuationOver c = P.valuationOver t := by
  refine Valuation.ext fun g => ?_
  rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply,
    ← functionFieldMap_comp_apply h t hc]
  by_cases hg : functionFieldMap t g = 0
  · rw [hg, map_zero, map_zero, map_zero]
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr hg),
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Positivity.ord_functionFieldMap_of_isIso h E P heq]

/-- A dominant morphism inducing `k(Y) ≅ k(X)`, onto a normal scheme, is a local isomorphism at
every point over the generic point of a prime divisor, since `𝒪_{Y,P}` is a discrete valuation
ring. -/
private theorem isIso_stalkMap_of_map_eq_genericPoint [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {x : X} {P : MMP.Mori.PrimeDivisor Y}
    (hx : f x = P.genericPoint) : IsIso (f.stalkMap x) := by
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x

/-- A separated dominant morphism inducing `k(Y) ≅ k(X)`, onto a normal scheme, has at most one
point over the generic point of a prime divisor. -/
private theorem eq_of_map_eq_genericPoint [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {f : X ⟶ Y} [IsSeparated f] [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {x₁ x₂ : X} {P : MMP.Mori.PrimeDivisor Y}
    (h₁ : f x₁ = P.genericPoint) (h₂ : f x₂ = P.genericPoint) : x₁ = x₂ := by
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (f x₁)) := by rw [h₁]; infer_instance
  have := isIso_stalkMap_of_map_eq_genericPoint hf h₁
  have := isIso_stalkMap_of_map_eq_genericPoint hf h₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf (h₂.trans h₁.symm)

/-- The birational transform of a `ℚ`-divisor with nonnegative coefficients has nonnegative
coefficients. -/
private theorem transformDivisor_apply_nonneg (φ : X.RationalMap Y) {D : QDivisor X}
    (hD : ∀ E, 0 ≤ D E) (P : MMP.Mori.PrimeDivisor Y) :
    0 ≤ RationalMap.transformDivisor φ D P := by
  classical
  rw [← Finsupp.sum_single D, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_nonneg fun E _ => ?_
  rw [RationalMap.transformDivisor, DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases RationalMap.transformPrimeDivisor φ E with _ | Q
  · simp
  · simp only [Option.elim_some, Finsupp.single_apply]
    split_ifs
    · exact hD E
    · exact le_rfl

/-- A morphism of integral schemes sending the generic point to the generic point is dominant. -/
private theorem isDominant_of_map_genericPoint [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (h : f (genericPoint X) = genericPoint Y) : IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have : y ∈ closure {genericPoint Y} := by rw [genericPoint_spec Y]; trivial
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range.mpr ⟨_, h⟩)) this

/-- The birational transform of a prime divisor `P` under a rational map with a representative
`g` defined at `η_P` is the closure of `g(η_P)`. -/
private theorem coe_transform_eq_closure_singleton [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g : X.PartialMap Y)
    (hg : g.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g.domain) :
    (RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g hg _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g.domain.ι q := by
      have : g.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If the transform of `P` under `φ` is the prime divisor `E`, then a representative of `φ`
defined at `η_P` sends `η_P` to `η_E`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : RationalMap.transformPrimeDivisor φ P = some E)
    (g : X.PartialMap Y) (hg : g.toRationalMap = φ) (hP : P.genericPoint ∈ g.domain) :
    E.genericPoint = g.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g hg P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

private theorem hom_comp_eq_of_compHom_eq [IsReduced X] [IsSeparated (T ↘ ⊤_ Scheme)]
    {f : X ⟶ T} {π : Y ⟶ T} {φ : X.RationalMap Y} {g : X.PartialMap Y}
    (hg : g.toRationalMap = φ) (hφ : φ.compHom π = f.toRationalMap) :
    g.hom ≫ π = g.domain.ι ≫ f := by
  have h1 : (g.compHom π).toRationalMap = f.toPartialMap.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg, hφ]
  exact (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)

/-- A point of `Y` over the generic point of `T`, along a dominant `π : Y ⟶ T` inducing
`k(T) ≅ k(Y)`, is the generic point of `Y`. -/
private theorem eq_genericPoint_of_map_eq_genericPoint [IsIntegral Y] [IsIntegral T]
    {π : Y ⟶ T} [IsDominant π] [IsSeparated π] (hbπ : Function.Bijective (functionFieldMap π))
    {y : Y}
    (hy : π y = genericPoint T) : y = genericPoint Y := by
  have hy' : π (genericPoint Y) = genericPoint T := map_genericPoint_of_isDominant π
  have : ValuationRing (T.presheaf.stalk (π (genericPoint Y))) := by
    rw [hy']
    exact inferInstanceAs (ValuationRing T.functionField)
  have : ValuationRing (T.presheaf.stalk (π y)) := by
    rw [hy]
    exact inferInstanceAs (ValuationRing T.functionField)
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing π hbπ y
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing π hbπ (genericPoint Y)
  exact (MMP.Positivity.eq_of_isIso_stalkMap π hbπ (x₁ := genericPoint Y) (x₂ := y)
    (hy.trans hy'.symm)).symm

/-- Let `φ : X ⤏ Y` be a rational map over `T` (along `f : X ⟶ T` and `π : Y ⟶ T`, with `f` and
`π` birational) and `E` the transform of a prime divisor `P` of `X`. Then `P` and `E` define the
same valuation of `k(T)`. -/
private theorem valuationOver_eq_of_transformPrimeDivisor_eq_some [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral T] [IsSeparated (T ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {f : X ⟶ T} {π : Y ⟶ T} [IsDominant f] [IsDominant π] [IsSeparated π]
    (hbf : Function.Bijective (functionFieldMap f)) (hbπ : Function.Bijective (functionFieldMap π))
    {φ : X.RationalMap Y} (hφ : φ.compHom π = f.toRationalMap)
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (hP : RationalMap.transformPrimeDivisor φ P = some E) :
    P.valuationOver f = E.valuationOver π := by
  obtain ⟨hdef, -⟩ := RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
  obtain ⟨g, hgP, hg⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have hE := genericPoint_eq_of_transformPrimeDivisor_eq_some hP g hg hgP
  have hcomm := hom_comp_eq_of_compHom_eq hg hφ
  set U := g.domain
  have : Nonempty U := ⟨⟨_, hgP⟩⟩
  let x : U.toScheme := ⟨P.genericPoint, hgP⟩
  have hco : Order.coheight x = 1 := by
    rw [← Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding]
    exact P.coheight_genericPoint
  let PU : MMP.Mori.PrimeDivisor U.toScheme := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hPU : PU.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  have : IsDominant U.ι := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U.isOpen.dense (by simpa using ‹Nonempty U›)
  -- `g` is dominant: it sends the generic point of `U` over the generic point of `T`
  have hgen : g.hom (genericPoint U) = genericPoint Y := by
    refine eq_genericPoint_of_map_eq_genericPoint hbπ ?_
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply,
      map_genericPoint_of_isDominant U.ι, map_genericPoint_of_isDominant f]
  have : IsDominant g.hom := isDominant_of_map_genericPoint _ hgen
  have hbg : Function.Bijective (functionFieldMap g.hom) := by
    refine ⟨(functionFieldMap g.hom).injective, fun s => ?_⟩
    have hι : Function.Bijective (functionFieldMap U.ι) :=
      MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨x, trivial⟩
    obtain ⟨t, ht⟩ := (Function.Bijective.comp hι hbf).2 s
    refine ⟨functionFieldMap π t, ?_⟩
    rw [functionFieldMap_comp_apply g.hom π hcomm, ← ht, Function.comp_apply,
      functionFieldMap_comp_apply U.ι f rfl]
  have h1 : PU.valuationOver (U.ι ≫ f) = P.valuationOver f :=
    valuationOver_eq_of_isIso U.ι f rfl PU P (by rw [hPU]; rfl)
  have hgx : g.hom PU.genericPoint = E.genericPoint := by rw [hPU, hE]
  have : IsIso (g.hom.stalkMap PU.genericPoint) := by
    have := E.isDiscreteValuationRing_localRing
    have : ValuationRing (Y.presheaf.stalk (g.hom PU.genericPoint)) := by
      rw [hgx]
      infer_instance
    exact MMP.Positivity.isIso_stalkMap_of_valuationRing _ hbg _
  have h2 : PU.valuationOver (U.ι ≫ f) = E.valuationOver π :=
    valuationOver_eq_of_isIso g.hom π hcomm PU E hgx
  rw [← h1, h2]

/-- **Algebraic Hartogs along a birational morphism.** Let `g : X ⟶ Y` be a dominant morphism of
normal integral schemes with `g^* : k(Y) ≅ k(X)`, and `c` a rational function on `X` whose order
vanishes along some prime divisor of `X` over each prime divisor of `Y` at which `g` is a local
isomorphism. Then `c` comes from a rational function on `Y` without zeros or poles, a unit of
`Γ(Y, 𝒪_Y)`, so the order of `c` vanishes along every prime divisor of `X`. -/
private theorem ord_eq_zero_of_forall_isIso_stalkMap [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (g : X ⟶ Y) [IsDominant g]
    (hbg : Function.Bijective (functionFieldMap g)) {c : X.functionField} (hc : c ≠ 0)
    (hex : ∀ Q : MMP.Mori.PrimeDivisor Y, ∃ E : MMP.Mori.PrimeDivisor X,
      g E.genericPoint = Q.genericPoint ∧ IsIso (g.stalkMap E.genericPoint) ∧
        X.ord c E.genericPoint = 0)
    (E : MMP.Mori.PrimeDivisor X) : X.ord c E.genericPoint = 0 := by
  obtain ⟨c', rfl⟩ := hbg.2 c
  have hc' : c' ≠ 0 := by rintro rfl; exact hc (map_zero _)
  have h0 : ∀ y : Y, Order.coheight y = 1 → Y.ord c' y = 0 := by
    intro y hy
    let Q : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy
    have hQ : Q.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy
    obtain ⟨E', hE', hiso, hord⟩ := hex Q
    rw [← hQ, ← MMP.Positivity.ord_functionFieldMap_of_isIso g E' Q hE' c', hord]
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalUnit_of_forall_ord_eq_zero
      (Units.mk0 c' hc') h0
  have h1 : c' = algebraMap (Y.presheaf.stalk (g E.genericPoint)) Y.functionField
      (Y.presheaf.germ ⊤ (g E.genericPoint) (TopologicalSpace.Opens.mem_top _)
        (s : Γ(Y, ⊤))) := by
    have hsp : genericPoint Y ⤳ g E.genericPoint := (genericPoint_spec Y).specializes trivial
    change c' = (Y.presheaf.stalkSpecializes hsp).hom
      (Y.presheaf.germ ⊤ (g E.genericPoint) (TopologicalSpace.Opens.mem_top _) (s : Γ(Y, ⊤)))
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    exact hs.symm
  rw [h1, MMP.Mori.functionFieldMap_algebraMap_stalk]
  exact E.ord_algebraMap_of_isUnit (((s.isUnit).map _).map _)

/-- The transcendence degree of the function field does not see a rewriting of the structure
morphism. -/
private theorem trdeg_functionField_congr {k : Type u} [Field k] [IsIntegral X]
    {s s' : X ⟶ Spec (.of k)} (h : s = s') :
    (letI := functionFieldAlgebra s; Algebra.trdeg k X.functionField) =
      (letI := functionFieldAlgebra s'; Algebra.trdeg k X.functionField) := by
  subst h
  rfl

/-- A form whose rewriting along an equality of structure morphisms vanishes is zero. -/
private theorem eq_zero_of_cast_eq_zero {k : Type u} [Field k] [IsIntegral X]
    {s s' : X ⟶ Spec (.of k)} (h : s = s') {d : ℕ} {m : ℤ} (τ : RationalPluriForms s d m)
    (h0 : (h ▸ τ : RationalPluriForms s' d m) = 0) : τ = 0 := by
  subst h
  exact h0

/-- The order of a form does not see a rewriting of the structure morphism. -/
private theorem ordForm_cast {k : Type u} [Field k] [IsIntegral X] [IsLocallyNoetherian X]
    {s s' : X ⟶ Spec (.of k)} (h : s = s') {d : ℕ} {m : ℤ} (τ : RationalPluriForms s d m)
    (E : MMP.Mori.PrimeDivisor X) :
    E.ordForm (h ▸ τ : RationalPluriForms s' d m) = E.ordForm τ := by
  subst h
  rfl

/-- Along a dominant `f : Y ⟶ X` with `f^* : k(X) ≅ k(Y)`, over a perfect field, the pull-back of
a nonzero rational `m`-canonical form is nonzero, and every rational `m`-canonical form on `Y` is
a multiple of it. -/
private theorem pullbackRationalPluriForms_ne_zero_and_exists_eq_smul {k : Type u} [Field k]
    [PerfectField k] [IsIntegral X] [IsIntegral Y] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) (σ : RationalPluriForms (f ≫ sX) d m) :
    pullbackRationalPluriForms sX f τ ≠ 0 ∧
      ∃ c : Y.functionField, σ = c • pullbackRationalPluriForms sX f τ := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let e := ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) m
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω₀ m τ :=
    pullbackForms_eq hω₀ m τ
  have hr0 : e.repr (pullbackFormsAlong hω₀ m τ) () ≠ 0 := by
    change (ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) m).repr
      (pullbackFormsAlong hω₀ m τ) () ≠ 0
    rw [repr_pullbackFormsAlong hω₀ m τ]
    exact (map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ)
  have hne : pullbackFormsAlong hω₀ m τ ≠ 0 := fun h0 => hr0 (by rw [h0]; simp)
  rw [hpull]
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    ((Module.finrank_eq_card_basis e).trans Fintype.card_unit) hne σ
  exact ⟨hne, c, hc.symm⟩

/-- Let `φ : X ⤏ Y` be a rational map over `T` (along `f : X ⟶ T` and a proper `π : Y ⟶ T` with
`π^* : k(T) ≅ k(Y)`), `X` normal. If prime divisors `P` of `X` and `E` of `Y` lie over the same
prime divisor `Q` of `T`, then `φ_* P = E`: `φ` is defined at `η_P`, and `φ(η_P)` and `η_E` are
two points over `η_Q`, at which `π` is a local isomorphism. -/
private theorem transformPrimeDivisor_eq_some_of_map_eq [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (T ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {f : X ⟶ T} {π : Y ⟶ T} [IsProper π] [IsDominant π]
    (hbπ : Function.Bijective (functionFieldMap π))
    {φ : X.RationalMap Y} (hφ : φ.compHom π = f.toRationalMap)
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y} {Q : MMP.Mori.PrimeDivisor T}
    (hP : f P.genericPoint = Q.genericPoint) (hE : π E.genericPoint = Q.genericPoint) :
    RationalMap.transformPrimeDivisor φ P = some E := by
  obtain ⟨g, hgP, hg⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one f π φ hφ P.coheight_genericPoint.le)
  have hcomm := hom_comp_eq_of_compHom_eq hg hφ
  have h1 : π (g.hom ⟨P.genericPoint, hgP⟩) = Q.genericPoint := by
    change (g.hom ≫ π) ⟨P.genericPoint, hgP⟩ = _
    rw [hcomm]
    exact hP
  refine RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g, hgP, hg⟩, ?_⟩
  have hE' : E.genericPoint = g.hom ⟨P.genericPoint, hgP⟩ := eq_of_map_eq_genericPoint hbπ hE h1
  have h2 : RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g hg P hgP, ← hE']
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [RationalMap.transformIdeal, h2, MMP.Positivity.vanishingIdeal_support_of_isReduced]

end Helpers

section Negativity

open CategoryTheory.Limits MMP.Flips

/-- The second projection `v : G ⟶ X⁺` of a normalized graph of two projective morphisms
`f⁻ : X⁻ ⟶ Z`, `f⁺ : X⁺ ⟶ Z` over a projective `Z ⟶ Spec k` is projective: it is the finite
morphism `(u, v) : G ⟶ X⁻ ×_Z X⁺`, into a scheme projective over `k`, followed by the base change
of `f⁻`. -/
private theorem isProjectiveMorphism_snd {k : Type} [Field k] {Xm Xp Z G : Scheme.{0}}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp} {sZ : Z ⟶ Spec (.of k)}
    (hfm : IsProjectiveMorphism fm) (hfp : IsProjectiveMorphism fp)
    (hZ : IsProjectiveMorphism sZ) (hG : IsNormalizedGraph fm fp u v) :
    IsProjectiveMorphism v := by
  have hsnd : IsProjectiveMorphism (pullback.snd fm fp) := hfm.baseChange fp
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isProjectiveMorphism
    (pullback.snd fm fp ≫ fp ≫ sZ) (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _) (hsnd.comp (hfp.comp hZ))
  have := hG.isFinite
  have hlift := isProjectiveMorphism_of_isFinite (pullback.lift u v hG.comp_eq) L hLa
  have := hlift.comp hsnd
  rwa [pullback.lift_snd] at this

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_exists_forall_base_eq_of_isCurveNormalization (C : ProperCurve sX)
    {C' : Scheme.{u}} {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
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
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_exists_forall_base_eq_of_isCurveNormalization C hν
    ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem isCurve_ι (C : ProperCurve sX) : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
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
private theorem degreeOn_comp_eq_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have := isCurve_comp C hν hdim
  have := isCurve_ι (k := k) C
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_exists_forall_base_eq_of_isCurveNormalization C hν)
    ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- A `ℚ`-divisor `E` on `X` which is ample over `Z` for `g : X ⟶ Z` is nef over `Y` for every
`w : X ⟶ Y` all of whose contracted curves are contracted by `g`: a positive multiple `N E` is a
`g`-ample Cartier divisor, of positive degree on every curve contracted by `g`. -/
private theorem isRelativelyNef_toRDivisor_of_hasRelativelyAmpleMultiple
    [CompactSpace X] {Y Z : Scheme.{u}} {g : X ⟶ Z} {w : X ⟶ Y}
    (hwg : ∀ C : ProperCurve sX, C.IsContractedBy w → C.IsContractedBy g)
    {E : QDivisor X} (hE : E.HasRelativelyAmpleMultiple g) :
    IsRelativelyNef k sX w (QDivisor.toRDivisor E) := by
  obtain ⟨N, hN, L, hL, hLq, hLa⟩ := hE
  refine ⟨1, fun _ => (N : ℝ)⁻¹, fun _ => L, fun _ => hL, ?_, ?_⟩
  · rw [Fin.sum_univ_one, ← QDivisor.toRDivisor_toQDivisor, hLq, map_zsmul,
      ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast,
      inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]
  · intro C hC x hx
    obtain ⟨hL', d, -, hd, hxd⟩ := hx
    obtain ⟨C', ν, hν, hdim, hd0⟩ := hd 0
    have := hν.isFinite
    have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    have := hL.isInvertibleModule_divisorialSheaf
    have hpos : 0 < d 0 := by
      rw [hd0]
      change 0 < MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim L.divisorialSheaf
      rw [degreeOn_comp_eq_of_isCurveNormalization C hν hdim]
      exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy g _ hLa
        C (hwg C hC)
    rw [hxd, Fin.sum_univ_one]
    have : (0 : ℝ) < d 0 := by exact_mod_cast hpos
    positivity

end Curve

section Ample

open RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple

/-- If `φ = (a, b) : W ⟶ X ×_S Y` is affine, `L` is `f`-ample and `N` is `g`-ample, then
`a^* L ⊗ b^* N` is ample relative to `a ≫ f`. -/
private theorem isRelativelyAmple_tensorModules_of_isAffineHom {S X Y W : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} {a : W ⟶ X} {b : W ⟶ Y} (h : a ≫ f = b ≫ g)
    [IsAffineHom (pullback.lift a b h)] (L : X.Modules) (N : Y.Modules)
    [IsInvertibleModule X L] [IsInvertibleModule Y N]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hN : Stacks.RelativeAmple.IsRelativelyAmple g N) :
    Stacks.RelativeAmple.IsRelativelyAmple (a ≫ f)
      (tensorModules W ((modulePullback a.toLRSHom.toShHom).obj L)
        ((modulePullback b.toLRSHom.toShHom).obj N)) := by
  have h1 := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    (pullback.lift a b h) (pullback.fst f g ≫ f) _
    (Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor f g L N hL hN)
  have e := Stacks.AmpleExternalTensor.pullbackExternalTensorIso f g (pullback.lift a b h) L N
  simp only [pullback.lift_fst, pullback.lift_snd] at e
  rw [← Category.assoc, pullback.lift_fst] at h1
  exact (isRelativelyAmple_congr _ _ _ e).mp h1

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private def modulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj F ≅ (Scheme.Modules.pullback f).obj F :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app F

/-- For a quasi-compact morphism, `f`-ampleness gives ampleness over every affine open. -/
private theorem isRelativelyAmple_stacks_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] (L : X.Modules) [IsInvertibleModule X L]
    (hL : MMP.Mori.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L inferInstance hL

/-- If `(a, b) : W ⟶ X ×_S Y` is affine, `A` is an `f`-ample and `B` a `g`-ample Cartier divisor,
then `a^* A + b^* B` is ample relative to `a ≫ f`. -/
private theorem isRelativelyAmple_add_of_isPullback {S X Y W : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W]
    {f : X ⟶ S} {g : Y ⟶ S} [QuasiCompact f] [QuasiCompact g] {a : W ⟶ X} {b : W ⟶ Y}
    (h : a ≫ f = b ≫ g) [IsAffineHom (pullback.lift a b h)]
    {A : Divisor X} (hA : A.IsCartier) (hAf : A.IsRelativelyAmple f hA)
    {B : Divisor Y} (hB : B.IsCartier) (hBg : B.IsRelativelyAmple g hB)
    {A' B' : Divisor W} {ha : ∀ Z : irreducibleComponents W, a (componentGenericPoint W Z) ∉ A.supp}
    {hb : ∀ Z : irreducibleComponents W, b (componentGenericPoint W Z) ∉ B.supp}
    (hpa : A.IsPullback a ha A') (hpb : B.IsPullback b hb B') :
    (A' + B').IsRelativelyAmple (a ≫ f) ((hpa.isCartier hA).add (hpb.isCartier hB)) := by
  have hA' := hpa.isCartier hA
  have hB' := hpb.isCartier hB
  have := hA.isInvertibleModule_divisorialSheaf
  have := hB.isInvertibleModule_divisorialSheaf
  have := hA'.isInvertibleModule_divisorialSheaf
  have := hB'.isInvertibleModule_divisorialSheaf
  have := (hA'.add hB').isInvertibleModule_divisorialSheaf
  have h1 := isRelativelyAmple_tensorModules_of_isAffineHom h _ _
    (isRelativelyAmple_stacks_of_isRelativelyAmple f _ hAf)
    (isRelativelyAmple_stacks_of_isRelativelyAmple g _ hBg)
  have e : tensorModules W ((modulePullback a.toLRSHom.toShHom).obj A.divisorialSheaf)
      ((modulePullback b.toLRSHom.toShHom).obj B.divisorialSheaf) ≅ (A' + B').divisorialSheaf :=
    tensorModulesMapIso W (modulePullbackIso a _ ≪≫ (hpa.divisorialSheafIso (hBc := hA)).symm)
      (modulePullbackIso b _ ≪≫ (hpb.divisorialSheafIso (hBc := hB)).symm) ≪≫
      hA'.divisorialSheafTensorIso hB'
  exact MMP.Mori.IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ e).mp h1)

/-- For a quasi-compact separated morphism `f`, the sum of two `f`-ample Cartier divisors is
`f`-ample. -/
private theorem isRelativelyAmple_add {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {A B : Divisor X} (hA : A.IsCartier) (hAf : A.IsRelativelyAmple f hA)
    (hB : B.IsCartier) (hBf : B.IsRelativelyAmple f hB) :
    (A + B).IsRelativelyAmple f (hA.add hB) := by
  have := hA.isInvertibleModule_divisorialSheaf
  have := hB.isInvertibleModule_divisorialSheaf
  have := (hA.add hB).isInvertibleModule_divisorialSheaf
  have : IsAffineHom (pullback.lift (𝟙 X) (𝟙 X) (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f)) :=
    show IsAffineHom (pullback.diagonal f) from inferInstance
  have h := isRelativelyAmple_tensorModules_of_isAffineHom (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f) _ _
    (isRelativelyAmple_stacks_of_isRelativelyAmple f _ hAf)
    (isRelativelyAmple_stacks_of_isRelativelyAmple f _ hBf)
  rw [Category.id_comp] at h
  refine MMP.Mori.IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ ?_).mp h)
  exact tensorModulesMapIso X (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _)
    (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _) ≪≫
    hA.divisorialSheafTensorIso hB

/-- For a quasi-compact separated morphism `f`, every positive multiple of an `f`-ample Cartier
divisor is `f`-ample. -/
private theorem isRelativelyAmple_zsmul {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL)
    (n : ℕ) : (((n : ℤ) + 1) • L).IsRelativelyAmple f (hL.zsmul _) := by
  induction n with
  | zero => simpa using hLf
  | succ n ih =>
    convert isRelativelyAmple_add _ ih _ hLf using 2
    push_cast
    rw [add_smul, one_smul]

/-- For a normalized graph `(G, u, v)` of proper morphisms `f⁻ : X⁻ ⟶ Z`, `f⁺ : X⁺ ⟶ Z`, and
`ℚ`-Cartier divisors `D⁻` on `X⁻`, `D⁺` on `X⁺` with `-D⁻` `f⁻`-ample and `D⁺` `f⁺`-ample, the
divisor `-(u^* D⁻ - v^* D⁺)` is ample over `Z`: it is the pull-back of the `Z`-ample divisor
`pr₁^*(-D⁻) + pr₂^* D⁺` along the finite morphism `(u, v) : G ⟶ X⁻ ×_Z X⁺`. -/
private theorem hasRelativelyAmpleMultiple_neg_pullback_sub_pullback {Xm Xp Z G : Scheme.{u}}
    [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
    [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [CompactSpace G] [IsLocallyNoetherian G] [IsNormal G]
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsProper fm] [IsProper fp] {u : G ⟶ Xm} {v : G ⟶ Xp}
    (hG : IsNormalizedGraph fm fp u v) {Dm : QDivisor Xm} {Dp : QDivisor Xp}
    (hDm : Dm.IsQCartier) (hDp : Dp.IsQCartier)
    (hu : ∀ T : irreducibleComponents G, u (componentGenericPoint G T) ∉ Dm.supp)
    (hv : ∀ T : irreducibleComponents G, v (componentGenericPoint G T) ∉ Dp.supp)
    (hm : (-Dm).HasRelativelyAmpleMultiple fm) (hp : Dp.HasRelativelyAmpleMultiple fp) :
    (-(Dm.pullback hDm hu - Dp.pullback hDp hv)).HasRelativelyAmpleMultiple (u ≫ fm) := by
  have : IsIntegral G := hG.isIntegral
  have := hG.isFinite
  have hHm := QDivisor.isPullback_pullback hDm hu
  have hHp := QDivisor.isPullback_pullback hDp hv
  obtain ⟨m₁, hm₁, L₁, hL₁, hL₁q, hL₁a⟩ := hm
  obtain ⟨m₂, hm₂, L₂, hL₂, hL₂q, hL₂a⟩ := hp
  obtain ⟨k₁, rfl⟩ : ∃ k, m₁ = k + 1 := ⟨m₁ - 1, by omega⟩
  obtain ⟨k₂, rfl⟩ : ∃ k, m₂ = k + 1 := ⟨m₂ - 1, by omega⟩
  set N : ℕ := (k₁ + 1) * (k₂ + 1)
  have hNpos : 0 < N := by positivity
  set A₁ : Divisor Xm := ((k₂ : ℤ) + 1) • L₁
  set A₂ : Divisor Xp := ((k₁ : ℤ) + 1) • L₂
  have hqA₁ : Divisor.toQDivisor A₁ = (-(N : ℤ)) • Dm := by
    simp only [A₁, map_zsmul, hL₁q, smul_smul, smul_neg, ← neg_smul]
    congr 1; push_cast [N]; ring
  have hq₁ : Divisor.toQDivisor ((-1 : ℤ) • A₁) = (N : ℤ) • Dm := by
    rw [map_zsmul, hqA₁, smul_smul]; simp
  have hq₂ : Divisor.toQDivisor A₂ = (N : ℤ) • Dp := by
    simp only [A₂, map_zsmul, hL₂q, smul_smul]
    congr 1
  obtain ⟨A₁', hA₁'q, hpa⟩ := hHm N hNpos _ hq₁ ((hL₁.zsmul _).zsmul _)
  obtain ⟨A₂', hA₂'q, hpb⟩ := hHp N hNpos _ hq₂ (hL₂.zsmul _)
  have ha : ∀ T : irreducibleComponents G, u (componentGenericPoint G T) ∉ A₁.supp := by
    rw [QDivisor.supp_eq_of_toQDivisor_eq (by simp [hNpos.ne']) hqA₁]
    exact hu
  have hpa' : A₁.IsPullback u ha ((-1 : ℤ) • A₁') :=
    (hpa.zsmul ((hL₁.zsmul _).zsmul _) (-1) (by simpa using ha)).of_eq (by simp; rfl)
  have hamp := isRelativelyAmple_add_of_isPullback hG.comp_eq (hL₁.zsmul _)
    (isRelativelyAmple_zsmul hL₁ hL₁a k₂) (hL₂.zsmul _) (isRelativelyAmple_zsmul hL₂ hL₂a k₁)
    hpa' hpb
  refine ⟨N, hNpos, _, _, ?_, hamp⟩
  rw [map_add, map_zsmul, hA₁'q, hA₂'q, smul_smul, smul_neg, smul_sub]
  module

end Ample

/-- The birational transform of divisors commutes with regarding a `ℚ`-divisor as an
`ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {X Y : Scheme.{u}} (φ : X.RationalMap Y)
    (D : QDivisor X) :
    RationalMap.transformDivisor φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (RationalMap.transformDivisor φ D) := by
  classical
  have hs : ∀ {Z : Scheme.{u}} (Q : MMP.Mori.PrimeDivisor Z) (r : ℚ),
      QDivisor.toRDivisor (Finsupp.single Q r) = Finsupp.single Q (r : ℝ) :=
    fun Q r => Finsupp.mapRange_single (hf := map_zero (Rat.castHom ℝ).toAddMonoidHom)
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    rw [hs, RationalMap.transformDivisor_single, RationalMap.transformDivisor_single]
    cases RationalMap.transformPrimeDivisor φ P with
    | none => exact (map_zero _).symm
    | some E => exact (hs E r).symm

/-- **Negativity lemma, ample form.** Let `v : G ⟶ V` be a projective birational morphism of
normal varieties and `g : G ⟶ Z` a morphism factoring through `v`. If `-H` is ample over `Z` for
`g` and `v_* H = 0`, then `H ≥ 0`: every curve contracted by `v` is contracted by `g`, so `-H` is
`v`-nef, and the negativity lemma applies. -/
private theorem isEffective_of_hasRelativelyAmpleMultiple_neg (k : Type u) [Field k] [CharZero k]
    {G V Z : Scheme.{u}} [CompactSpace G] [IsLocallyNoetherian G] [IsNormal G]
    [IsLocallyNoetherian V] [IsNormal V] {sG : G ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [QuasiCompact sG] (hG : IsNormalVariety k sG) (hV : IsNormalVariety k sV) {v : G ⟶ V}
    (hv : v ≫ sV = sG) (hvp : IsProjectiveMorphism v) (hvb : IsBirationalMorphism v)
    {g : G ⟶ Z} {w : V ⟶ Z} (hg : g = v ≫ w) {H : QDivisor G}
    (hH : (-H).HasRelativelyAmpleMultiple g)
    (hpush : RationalMap.transformDivisor v.toRationalMap H = 0) : H.IsEffective := by
  subst hg
  have hnef : IsRelativelyNef k sG v (-QDivisor.toRDivisor H) := by
    rw [← map_neg]
    exact isRelativelyNef_toRDivisor_of_hasRelativelyAmpleMultiple k sG
      (fun C hC x hx => by simp only [Scheme.Hom.comp_apply, hC x hx]) hH
  have hcomb : IsCartierCombination (QDivisor.toRDivisor H) := by
    obtain ⟨m, r, L, hL, hD, -⟩ := hnef
    refine ⟨m, -r, L, hL, ?_⟩
    rw [← neg_neg (QDivisor.toRDivisor H), hD]
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rfl
  have hR := isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor k sV sG hV hG v
    hv hvp hvb hcomb hnef
    (by rw [transformDivisor_toRDivisor, hpush, map_zero]; exact fun _ => le_rfl)
  exact fun E => Rat.cast_nonneg.mp (hR E)

end Negativity

section Graph

open MMP.Intersection

/-- Let `u : G ⟶ X` and `v : G ⟶ V` be birational with `u ≫ f = v ≫ p` for proper birational
morphisms `f : X ⟶ Z`, `p : V ⟶ Z` of normal varieties, and `E` a prime divisor of `G` over a
prime divisor `Q` of `Z`. Then `u`, `v` send `η_E` to the generic points of the strict transforms
`Q_X`, `Q_V` of `Q`, and are local isomorphisms there; divisors `A` on `X` and `A'` on `V` with
`p_* A' = f_* A` have the same coefficient along `Q_V` and `Q_X`. -/
private theorem exists_strictTransforms_of_map_eq_genericPoint {k : Type u} [Field k]
    {X V Z G : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian V]
    [IsNormal V] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral G] {sZ : Z ⟶ Spec (.of k)}
    (hZ : IsNormalVariety k sZ) {f : X ⟶ Z} {p : V ⟶ Z} [IsProper f] [IsProper p]
    (hX : IsNormalVariety k (f ≫ sZ)) (hV : IsNormalVariety k (p ≫ sZ))
    (hf : IsBirationalMorphism f) (hp : IsBirationalMorphism p) {u : G ⟶ X} {v : G ⟶ V}
    (hu : IsBirationalMorphism u) (hv : IsBirationalMorphism v) (huv : u ≫ f = v ≫ p)
    {Q : MMP.Mori.PrimeDivisor Z} {E : MMP.Mori.PrimeDivisor G}
    (hE : (u ≫ f) E.genericPoint = Q.genericPoint) :
    ∃ (QX : MMP.Mori.PrimeDivisor X) (QV : MMP.Mori.PrimeDivisor V),
      u E.genericPoint = QX.genericPoint ∧ v E.genericPoint = QV.genericPoint ∧
      IsIso (u.stalkMap E.genericPoint) ∧ IsIso (v.stalkMap E.genericPoint) ∧
      f QX.genericPoint = Q.genericPoint ∧ p QV.genericPoint = Q.genericPoint ∧
      ∀ (A : Divisor X) (A' : Divisor V), RationalMap.transformDivisor (X := V) p.toRationalMap A' =
        RationalMap.transformDivisor (X := X) f.toRationalMap A → A' QV = A QX := by
  have := hX.1.toIsIntegral
  have := hV.1.toIsIntegral
  have := hZ.1.toIsIntegral
  have := hf.isDominant
  have := hp.isDominant
  have := hu.isDominant
  have := hv.isDominant
  obtain ⟨QX, hfQ, -, htrf⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hX hf Q
  obtain ⟨QV, hpQ, -, htrp⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hV hp Q
  have hu' : f (u E.genericPoint) = Q.genericPoint := hE
  have hv' : p (v E.genericPoint) = Q.genericPoint := by
    rwa [← Scheme.Hom.comp_apply, ← huv]
  have huE := eq_of_map_eq_genericPoint hf.functionFieldMap_bijective hu' hfQ
  have hvE := eq_of_map_eq_genericPoint hp.functionFieldMap_bijective hv' hpQ
  refine ⟨QX, QV, huE, hvE, isIso_stalkMap_of_map_eq_genericPoint hu.functionFieldMap_bijective huE,
    isIso_stalkMap_of_map_eq_genericPoint hv.functionFieldMap_bijective hvE, hfQ, hpQ,
    fun A A' h => ?_⟩
  rw [← htrp A', ← htrf A, h]

/-- **Canonical divisors on the graph.** In the setting of
`exists_strictTransforms_of_map_eq_genericPoint`, let `K_X = div ω` and `K_V` be canonical
divisors with `p_* K_V = f_* K_X`. If `v` is a local isomorphism at `η_E` over `η_P`, then
`coeff_P(K_V) = ord_E(u^* ω)`. Indeed `v^* ω_V = c · u^* ω` for a rational function `c` on `G`
whose order vanishes along every prime divisor of `G` over a prime divisor of `Z`, so `c` is a
unit by algebraic Hartogs on `Z`. -/
private theorem coeff_eq_ordForm_pullback_of_isCanonicalDivisor {k : Type u} [Field k]
    [PerfectField k] {X V Z G : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral G]
    [IsLocallyNoetherian G] [IsNormal G] {sZ : Z ⟶ Spec (.of k)} (hZ : IsNormalVariety k sZ)
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z} {p : V ⟶ Z} [IsProper f] [IsProper p]
    (hfs : f ≫ sZ = sX) (hX : IsNormalVariety k sX) (hV : IsNormalVariety k (p ≫ sZ))
    (hf : IsBirationalMorphism f) (hp : IsBirationalMorphism p) {u : G ⟶ X} {v : G ⟶ V}
    [IsProper u] [IsDominant u] (hG : IsNormalVariety k (u ≫ sX)) (hu : IsBirationalMorphism u)
    (hv : IsBirationalMorphism v) (huv : u ≫ f = v ≫ p) {K : Divisor X} {nX : ℕ}
    (hK : K.IsCanonicalDivisor sX nX) {KV : Divisor V} {n : ℕ}
    (hKV : KV.IsCanonicalDivisor (p ≫ sZ) n)
    (hKVK : RationalMap.transformDivisor (X := V) p.toRationalMap KV =
      RationalMap.transformDivisor (X := X) f.toRationalMap K)
    {ω : RationalPluriForms sX nX 1} (hω0 : ω ≠ 0)
    (hω : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = DivisorWithCoeffs.coeff K Γ)
    {E : MMP.Mori.PrimeDivisor G} {P : MMP.Mori.PrimeDivisor V}
    (hvE : v E.genericPoint = P.genericPoint) [IsIso (v.stalkMap E.genericPoint)] :
    KV P = E.ordForm (pullbackRationalPluriForms sX u ω) := by
  have := hV.1.toIsIntegral
  have := hZ.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sZ) := hV.1.toLocallyOfFiniteType
  have := hf.isDominant
  have := hv.isDominant
  have hbu := hu.functionFieldMap_bijective
  have hbv := hv.functionFieldMap_bijective
  have hXf : IsNormalVariety k (f ≫ sZ) := hfs ▸ hX
  have hsG : v ≫ p ≫ sZ = u ≫ sX := by rw [← Category.assoc, ← huv, Category.assoc, hfs]
  have hgbir : IsBirationalMorphism (u ≫ f) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational f u
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hu)
  have hGf : IsNormalVariety k ((u ≫ f) ≫ sZ) := by rwa [Category.assoc, hfs]
  obtain ⟨ωV, hωV0, hωV⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hV hKV
  have hdX := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hK.topologicalKrullDim_eq
  have hdV := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := p ≫ sZ)
    hKV.topologicalKrullDim_eq
  have e1 := MMP.Mori.trdeg_functionField_eq_of_bijective sX u hbu
  have e2 := MMP.Mori.trdeg_functionField_eq_of_bijective (p ≫ sZ) v hbv
  have hn : n = nX := by
    rw [← hdX, ← hdV]
    exact congrArg Cardinal.toNat
      ((e2.trans (trdeg_functionField_congr (k := k) hsG)).trans e1.symm)
  subst hn
  have hdG : letI := functionFieldAlgebra (u ≫ sX)
      (Algebra.trdeg k G.functionField).toNat = n := by
    rw [← hdX]; exact congrArg Cardinal.toNat e1.symm
  change DivisorWithCoeffs.coeff KV P = _
  rw [← hωV P, ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso v hbv hdV E P hvE ωV,
    ← ordForm_cast hsG]
  set α := pullbackRationalPluriForms sX u ω with hα
  set β : RationalPluriForms (u ≫ sX) n 1 :=
    hsG ▸ pullbackRationalPluriForms (p ≫ sZ) v ωV with hβ
  obtain ⟨hα0, c, hcα⟩ :=
    pullbackRationalPluriForms_ne_zero_and_exists_eq_smul sX u hbu hdX hω0 β
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcα
    exact (pullbackRationalPluriForms_ne_zero_and_exists_eq_smul (p ≫ sZ) v hbv hdV hωV0 0).1
      (eq_zero_of_cast_eq_zero hsG _ hcα)
  have hord : ∀ E' : MMP.Mori.PrimeDivisor G,
      E'.ordForm β = G.ord c E'.genericPoint + E'.ordForm α := fun E' => by
    rw [hcα]; exact E'.ordForm_smul hdG hc0 hα0
  have hex : ∀ Q : MMP.Mori.PrimeDivisor Z, ∃ E' : MMP.Mori.PrimeDivisor G,
      (u ≫ f) E'.genericPoint = Q.genericPoint ∧ IsIso ((u ≫ f).stalkMap E'.genericPoint) ∧
        G.ord c E'.genericPoint = 0 := by
    intro Q
    obtain ⟨E', hgE, hgiso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hZ hGf hgbir Q
    obtain ⟨QX, QV, huE', hvE', hui, hvi, -, -, hK'⟩ :=
      exists_strictTransforms_of_map_eq_genericPoint hZ hXf hV hf hp hu hv huv hgE
    refine ⟨E', hgE, hgiso, ?_⟩
    have h1 := hord E'
    rw [hβ, ordForm_cast hsG,
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso v hbv hdV E' QV hvE' ωV,
      hα, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso u hbu hdX E' QX huE' ω,
      hωV, hω] at h1
    have h2 : DivisorWithCoeffs.coeff KV QV = DivisorWithCoeffs.coeff K QX := hK' K KV hKVK
    omega
  rw [hord, ord_eq_zero_of_forall_isIso_stalkMap (u ≫ f) hgbir.functionFieldMap_bijective hc0 hex E,
    zero_add]

/-- **Log canonicity on a model.** Let `(X, B)` be an lc pair over `k` with `K_X = div ω`, and
`u : G ⟶ X` a proper birational morphism from a normal variety. For every prime divisor `E` of
`G`, the log discrepancy `1 + ord_E(u^* ω) - coeff_E(u^*(K_X + B))` of `E` over `(X, B)` is
nonnegative. -/
private theorem pullback_apply_le_one_add_ordForm {k : Type u} [Field k] {X G : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral G]
    [CompactSpace G] [IsLocallyNoetherian G] [IsNormal G] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {K : Divisor X} {B : QDivisor X} {n : ℕ}
    (hK : K.IsCanonicalDivisor sX n) (hB : IsLogCanonicalPair sX B)
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hω : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = DivisorWithCoeffs.coeff K Γ)
    {u : G ⟶ X} [IsProper u] [IsDominant u] (hG : IsNormalVariety k (u ≫ sX))
    (hu : IsBirationalMorphism u) (hD : (Divisor.toQDivisor K + B).IsQCartier)
    (huD : ∀ T : irreducibleComponents G,
      u (componentGenericPoint G T) ∉ (Divisor.toQDivisor K + B).supp)
    (E : MMP.Mori.PrimeDivisor G) :
    (Divisor.toQDivisor K + B).pullback hD huD E ≤
      1 + E.ordForm (pullbackRationalPluriForms sX u ω) := by
  obtain ⟨N, hN, C, hC, hCc⟩ := hD.exists_pos
  obtain ⟨C', hC', hpull⟩ := QDivisor.isPullback_pullback hD huD N hN C hC hCc
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hCE := congrArg (fun F : QDivisor G => F E) hC'
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at hCE
  replace hCE : ((C' E : ℤ) : ℚ) = N * (Divisor.toQDivisor K + B).pullback hD huD E := hCE
  have hla := hB.2.2 n ⟨G, u, hG, hu, E⟩
    (1 + (E.ordForm (pullbackRationalPluriForms sX u ω) : ℝ) - (N : ℝ)⁻¹ * (C' E : ℝ))
    ⟨hX, ‹IsProper u›, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, 1, fun _ => (N : ℝ)⁻¹,
      fun _ => C, fun _ => C', fun _ => hCc, fun Γ => ?_, fun _ => ⟨_, hpull⟩, ?_⟩
  · have hE : ((Divisor.toQDivisor K + B).pullback hD huD E : ℝ) = (N : ℝ)⁻¹ * (C' E : ℝ) := by
      rw [show (Divisor.toQDivisor K + B).pullback hD huD E = (N : ℚ)⁻¹ * (C' E : ℚ) by
        rw [hCE, inv_mul_cancel_left₀ hNQ]]
      push_cast; ring
    exact_mod_cast (show ((Divisor.toQDivisor K + B).pullback hD huD E : ℝ) ≤
      1 + (E.ordForm (pullbackRationalPluriForms sX u ω) : ℝ) by rw [hE]; linarith)
  · have hCΓ := congrArg (fun F : QDivisor X => F Γ) hC
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast, Finsupp.add_apply] at hCΓ
    replace hCΓ : ((C Γ : ℤ) : ℚ) = N * (((K Γ : ℤ) : ℚ) + B Γ) := hCΓ
    change ((Γ.ordForm ω : ℤ) : ℝ) + ((B Γ : ℚ) : ℝ) = ∑ _i : Fin 1, (N : ℝ)⁻¹ * ((C Γ : ℤ) : ℝ)
    rw [Fin.sum_univ_one, hω Γ, ← Rat.cast_intCast (C Γ), hCΓ]
    push_cast
    field_simp
    rfl
  · rw [Fin.sum_univ_one]
    rfl

end Graph

section Fibres

open CategoryTheory.Limits

/-- In a Noetherian quasi-sober space, a closed point `x` of a preconnected closed set `F ≠ {x}`
has a generization `η ≠ x` in `F`. -/
private theorem exists_specializes_ne_of_isPreconnected {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] [QuasiSober α] {F : Set α} (hF : IsClosed F)
    (hconn : IsPreconnected F) {x : α} (hx : x ∈ F) (hxc : IsClosed ({x} : Set α))
    (hne : F ≠ {x}) : ∃ η ∈ F, η ⤳ x ∧ η ≠ x := by
  classical
  by_contra hcon
  push Not at hcon
  set A := F \ {x}
  obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure : IsClosed (closure A))
  set S' := {t ∈ S | t ≠ {x}}
  have hsub : A ⊆ ⋃₀ S' := fun a ha => by
    obtain ⟨t, ht, hat⟩ : a ∈ ⋃₀ S := hS ▸ subset_closure ha
    exact ⟨t, ⟨ht, fun h => ha.2 (h ▸ hat)⟩, hat⟩
  have hS'c : IsClosed (⋃₀ S') :=
    (hSf.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hSc t ht.1
  have hxA : x ∉ closure A := by
    intro hx'
    obtain ⟨t, ⟨ht, htx⟩, hxt⟩ := closure_minimal hsub hS'c hx'
    have htA : t ⊆ closure A := hS ▸ Set.subset_sUnion_of_mem ht
    obtain ⟨ξ, hξ⟩ : ∃ ξ, closure {ξ} = t :=
      ⟨_, (hSi t ht).closure_genericPoint (hSc t ht)⟩
    have hξx : ξ ⤳ x := specializes_iff_mem_closure.mpr (by rw [hξ]; exact hxt)
    have hξF : ξ ∈ F :=
      closure_minimal Set.diff_subset hF (htA (by rw [← hξ]; exact subset_closure rfl))
    apply htx
    rw [← hξ, hcon _ hξF hξx, hxc.closure_eq]
  have hAc : IsClosed A := isClosed_of_closure_subset fun a ha =>
    ⟨closure_minimal Set.diff_subset hF ha, fun h => hxA ((Set.mem_singleton_iff.mp h) ▸ ha)⟩
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn {x} A hxc hAc
    (fun a ha => if hax : a = x then Or.inl hax else Or.inr ⟨ha, hax⟩) (by ext a; simp [A])
    with h | h
  · exact hne (Set.Subset.antisymm h (Set.singleton_subset_iff.mpr hx))
  · exact (h hx).2 rfl

/-- Let `H` be an effective `ℚ`-divisor on a normal scheme `G` proper over a field, with `-H`
ample relative to `g : G ⟶ Z`. A closed point `x` over a closed point of `Z` whose fibre
`g⁻¹(g x)` is connected and not `{x}` lies in `Supp H`: otherwise a proper curve through `x` in
that fibre, not contained in `Supp H`, has `deg (-H) > 0` because it is contracted by `g`, and
`deg H ≥ 0` because `H` is effective. -/
private theorem mem_supp_of_isPreconnected_fibre {k : Type u} [Field k] {G Z : Scheme.{u}}
    (sG : G ⟶ Spec (.of k)) [IsProper sG] [IsNoetherian G] [IsNormal G]
    {g : G ⟶ Z} {H : QDivisor G} (heff : H.IsEffective)
    (hamp : (-H).HasRelativelyAmpleMultiple g) {x : G} (hx : IsClosed ({x} : Set G))
    (hgx : IsClosed ({g x} : Set Z)) (hconn : _root_.IsPreconnected (g ⁻¹' {g x}))
    (hne : g ⁻¹' {g x} ≠ {x}) : x ∈ H.supp := by
  obtain ⟨η, hg, hηx, hne⟩ := exists_specializes_ne_of_isPreconnected
    (hgx.preimage g.continuous) hconn rfl hx hne
  by_contra hxH
  obtain ⟨N, hN, L, hL, hLq, hLa⟩ := hamp
  have hηH : η ∉ (H.supp : Set G) := fun h => hxH (hηx.mem_closed H.supp.isClosed h)
  obtain ⟨y, hηy, hyx, hyZ, hy⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sG hηx hx
    (H.supp.isClosed.union hx) (Or.inr rfl) fun h => h.elim hηH hne
  let C : ProperCurve sG := ⟨y, hy⟩
  have hgy : g y = g x :=
    ((hyx.map g.continuous).antisymm ((hg : g η = g x) ▸ hηy.map g.continuous)).eq
  have hC : C.IsContractedBy g := fun w hw => by
    have hyw : g y ⤳ g w := (specializes_iff_mem_closure.mpr hw).map g.continuous
    rw [hgy] at hyw ⊢
    exact hyw.mem_closed hgx rfl
  have := hL.isInvertibleModule_divisorialSheaf
  have hpos : 0 < MMP.Mori.degreeOn k sG C.ι C.dim_le L.divisorialSheaf :=
    MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy g _ hLa C hC
  have hq : Divisor.toQDivisor (-L) = (N : ℤ) • H := by
    rw [map_neg, hLq, smul_neg, neg_neg]
  have heffL : 0 ≤ -L := by
    rw [← DivisorWithCoeffs.isEffective_iff_nonneg]
    intro E
    have hE : ((-L).coeff E : ℚ) = (N : ℤ) • H.coeff E := by
      simpa using congrArg (fun D => D.coeff E) hq
    exact_mod_cast hE ▸ smul_nonneg (by positivity) (heff E)
  have hnn := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sG C.ι C.dim_le (-L) hL.neg
    heffL ⟨genericPoint C.scheme, by
      rw [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hN.ne') hq,
        ProperCurve.ι_genericPoint]
      exact fun h => hyZ (Or.inl h)⟩).1
  rw [MMP.Mori.Divisor.degreeOn_neg' k sG C.ι C.dim_le L hL] at hnn
  change 0 ≤ -MMP.Mori.degreeOn k sG C.ι C.dim_le L.divisorialSheaf at hnn
  omega

/-- Let `u : G ⟶ X`, `v : G ⟶ V` be surjective with `u ≫ f = v ≫ p`, where `f` and `p` are proper
birational onto `Z`. If the fibre of `g = u ≫ f` through `x` is `{x}`, then `g x` lies in the
biregular loci of both `f` and `p`: their fibres over it are the images of `{x}`, hence finite. -/
private theorem mem_biregularLocus_of_preimage_eq_singleton {G X V Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral V] [IsIntegral Z] [IsNormal Z] {f : X ⟶ Z} {p : V ⟶ Z}
    [IsProper f] [IsProper p]
    (hf : IsBirationalMorphism f) (hp : IsBirationalMorphism p) {u : G ⟶ X} {v : G ⟶ V}
    [Surjective u] [Surjective v] (huv : u ≫ f = v ≫ p) {x : G}
    (hx : (u ≫ f) ⁻¹' {(u ≫ f) x} = {x}) :
    (u ≫ f) x ∈ biregularLocus f ⊓ biregularLocus p := by
  have hfin : ∀ {Y : Scheme.{u}} [IsIntegral Y] (a : Y ⟶ Z) [IsProper a],
      IsBirationalMorphism a → ∀ (b : G ⟶ Y) [Surjective b], b ≫ a = u ≫ f →
      (u ≫ f) x ∈ biregularLocus a := by
    intro Y _ a _ ha b _ hb
    obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso a
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism ha)).1 inferInstance
    refine le_biregularLocus (V := ⟨_, hU⟩) hiso (?_ : (a ⁻¹' _).Finite)
    rw [← Set.image_preimage_eq (a ⁻¹' _) b.surjective, ← Set.preimage_comp]
    change (b '' (b ≫ a) ⁻¹' _).Finite
    rw [hb, hx]
    exact Set.finite_singleton _ |>.image _
  exact ⟨hfin f hf u rfl, hfin p hp v huv.symm⟩

/-- In a Jacobson space, a closed set containing every closed point `x` with `g x ∉ U`, for an
open `U`, contains all of `g⁻¹(Uᶜ)`. -/
private theorem preimage_compl_subset_of_isClosed {α β : Type*} [TopologicalSpace α]
    [JacobsonSpace α] [TopologicalSpace β] {g : α → β} (hg : Continuous g) {U : Set β}
    (hU : IsOpen U) {S : Set α} (hS : IsClosed S)
    (h : ∀ x, IsClosed ({x} : Set α) → g x ∉ U → x ∈ S) : g ⁻¹' Uᶜ ⊆ S := by
  intro w hw
  suffices closure {w} ⊆ S from this (subset_closure rfl)
  rw [← JacobsonSpace.closure_inter_closedPoints isClosed_closure]
  exact closure_minimal (fun x ⟨hxw, hxc⟩ => h x hxc fun hU' =>
    hw (((specializes_iff_mem_closure.mpr hxw).map hg).mem_open hU hU')) hS

end Fibres

section LogCanonical

open MMP.Flips
open scoped WithZero

/-! ### Discrepancies computed with choices -/

section DiscrepancyChoices

open TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A discrepancy computed with a form whose divisor is canonical gives the log discrepancy
`1 + a`. -/
private theorem isLogDiscrepancy_of_isDiscrepancyWith {n : ℕ} {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {b : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n D ω r L E b) :
    MMP.Intersection.IsLogDiscrepancy sX n D E.toDivisorOver (1 + b) := by
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω, ⟨divisorOfForm ω, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r,
    L, L', hLc, fun Γ => ?_, hpb, by ring⟩
  have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    MMP.Fourfold.coeff_sum_smul_toRDivisor] using this

/-- With a presentation of `div(ω) + D` by Cartier divisors, every divisor over `X` (with proper
model) has a discrepancy computed with these choices. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ b, IsDiscrepancyWith sX n D ω r L E b := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hX, hn, hω, hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

end DiscrepancyChoices

section Lift

variable {k : Type u} [Field k] {M W : Scheme.{u}} [IsIntegral M] [IsIntegral W]
  {sM : M ⟶ Spec (.of k)}

/-- **The centre on a proper model.** If `q : W ⟶ M` is proper and dominant and `ξ` is a
valuation of `k(W)` restricting to the valuation of a divisor `D` over `M`, then `ξ` dominates the
local ring of some point of `W` (valuative criterion of properness). -/
private theorem exists_dominated_point (q : W ⟶ M) [IsDominant q] [IsProper q]
    (D : DivisorOver k sM) (ξ : Valuation W.functionField ℤᵐ⁰)
    (h : ξ.comap (functionFieldMap q) = D.valuation) :
    ∃ x : W, (∀ a : W.presheaf.stalk x, ξ (algebraMap _ W.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        ξ (algebraMap _ W.functionField a) < 1 := by
  set z := D.f D.E.genericPoint
  have hw : ∀ b : M.presheaf.stalk z,
      ξ (functionFieldMap q (algebraMap _ M.functionField b)) =
        D.valuation (algebraMap _ M.functionField b) := fun b => by
    rw [← h]; rfl
  let R := ξ.valuationSubring
  let φ : M.presheaf.stalk z →+* R :=
    ((functionFieldMap q).comp (algebraMap (M.presheaf.stalk z) M.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _)
  have hgen : genericPoint M ⤳ z := (genericPoint_spec M).specializes trivial
  have hex : ValuativeCriterion.Existence q := by
    have h : @IsProper _ _ q := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq q :=
    { R := R
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ M.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk q,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫ l =
      W.fromSpecStalk (genericPoint W) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
      W.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : W.presheaf.stalk x,
      algebraMap _ W.functionField a = ((f.hom a : R) : W.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]
    exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

variable [IsLocallyNoetherian M] [IsNormal M] [IsLocallyNoetherian W] [IsNormal W]

/-- **Lifting a divisor over `M` along a proper birational morphism.** Every divisor `D` over `M`
with proper model has the valuation `ord_E ∘ q^*` of a divisor `E` over `W`, for `q : W ⟶ M`
proper birational with `W` a variety. -/
private theorem exists_properDivisorOver_comap_eq (q : W ⟶ M) [IsProper q]
    (hq : IsBirationalMorphism q) [AlgebraicGeometry.IsVariety k (q ≫ sM)]
    (D : ProperDivisorOver k sM) :
    haveI := hq.isDominant
    ∃ E : ProperDivisorOver k (q ≫ sM),
      E.valuation.comap (functionFieldMap q) = D.valuation := by
  have := hq.isDominant
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hbq := hq.functionFieldMap_bijective
  let eq := RingEquiv.ofBijective (functionFieldMap q) hbq
  let ξ : Valuation W.functionField ℤᵐ⁰ := D.valuation.comap eq.symm.toRingHom
  have hξ : ξ.comap (functionFieldMap q) = D.valuation := by
    ext a
    change D.valuation (eq.symm (functionFieldMap q a)) = D.valuation a
    rw [show functionFieldMap q a = eq a from rfl, RingEquiv.symm_apply_apply]
  obtain ⟨x, hle, hlt⟩ := exists_dominated_point q D.toDivisorOver ξ hξ
  have hdiv : IsDivisorOfFunctionField k (q ≫ sM) ξ := by
    refine ⟨D.Y, D.f ≫ sM, D.isNormalVariety, D.E, ?_⟩
    letI := functionFieldAlgebra sM
    letI := functionFieldAlgebra (q ≫ sM)
    letI := functionFieldAlgebra (D.f ≫ sM)
    let eP := functionFieldAlgEquiv sM q hbq
    let eY := functionFieldAlgEquiv sM D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbq.2 t
    change D.valuation (eq.symm (functionFieldMap q s)) =
      D.E.divisorialValuation (eY (eP.symm (functionFieldMap q s)))
    rw [show eP.symm (functionFieldMap q s) = s from eP.symm_apply_apply s,
      show functionFieldMap q s = eq s from rfl, RingEquiv.symm_apply_apply]
    rfl
  obtain ⟨E, -, hv, -⟩ := exists_properDivisorOver_isProjective_of_dominates (q ≫ sM) hdiv x hle hlt
  exact ⟨E, by rw [hv, hξ]⟩

end Lift

/-! ### Compatible forms -/

section Forms

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

open MMP.Positivity in
/-- For a proper birational morphism `f : Y → X` of normal varieties of dimension `n` and a
canonical divisor `K_Y` of `Y`, there is a nonzero rational top form `ω` on `X` with
`div_Y(f^*ω) = K_Y` and `div_X(ω) = f_* K_Y`. -/
private theorem exists_divisorOfForm_eq_transformDivisor (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} (hn : topologicalKrullDim X = n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧
      divisorOfForm ω = RationalMap.transformDivisor (X := Y) f.toRationalMap KY ∧
      divisorOfForm (pullbackRationalPluriForms sX f ω) = KY := by
  have hbij := hf.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω₁, hω₁0, hω₁⟩ := IsCanonicalDivisor.exists_ordForm_eq hY hKY
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sX n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sX f τ = ω₁ := by
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 τ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  refine ⟨τ, fun h0 => hω₁0 ?_, Finsupp.ext fun P => ?_, Finsupp.ext fun Γ => ?_⟩
  · rw [← hpull, h0]
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp
  · obtain ⟨E, heq, hiso, htr⟩ := exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
    rw [htr]
    change P.ordForm τ = KY.coeff E
    rw [← ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq τ, hpull, hω₁]
  · change Γ.ordForm _ = KY.coeff Γ
    rw [hpull, hω₁]

end Forms

/-! ### Log discrepancies along a crepant morphism -/

section CrepantDescent

variable {k : Type u} [Field k] [PerfectField k] {V M : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [LocallyOfFiniteType sV]
  [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]

/-- **Log discrepancies descend along a crepant proper birational morphism.** Let `q : M ⟶ V` be
proper birational, `ω` a nonzero rational top form on `V` with `K_V = div(ω)` and
`K_M = div(q^*ω)`, and `K_V + B_V` an `ℝ`-Cartier combination whose pull-back is `K_M + B_M`.
If every log discrepancy of `(M, B_M)` is nonnegative, so is every log discrepancy of
`(V, B_V)`: each is the log discrepancy of `(M, B_M)` along the same valuation. -/
private theorem nonneg_of_isLogDiscrepancy_of_isRCartierPullback (hV : IsNormalVariety k sV)
    (q : M ⟶ V) [IsProper q] [IsDominant q] [LocallyOfFiniteType (q ≫ sV)]
    (hM : IsNormalVariety k (q ≫ sV)) (hq : IsBirationalMorphism q) {n : ℕ}
    {ω : RationalPluriForms sV n 1} (hω : ω ≠ 0) (hKV : (divisorOfForm ω).IsCanonicalDivisor sV n)
    (hKM : (divisorOfForm (pullbackRationalPluriForms sV q ω)).IsCanonicalDivisor (q ≫ sV) n)
    {BV : RDivisor V} {BM : RDivisor M} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor V}
    (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + BV = ∑ j, r j • Divisor.toRDivisor (L j))
    (hDY : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ω) + BV)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sV q ω)) + BM))
    (hlc : ∀ (E : DivisorOver k (q ≫ sV)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (q ≫ sV) n BM E a → 0 ≤ a)
    {E : DivisorOver k sV} {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sV n BV E a) :
    0 ≤ a := by
  have := hM.1
  let EP : ProperDivisorOver k sV := ⟨E, ha.2.1⟩
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith hV hKV.topologicalKrullDim_eq hω hLc hsum EP
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
    (isLogDiscrepancy_of_isDiscrepancyWith hKV hb)]
  obtain ⟨E', hE'⟩ := exists_properDivisorOver_comap_eq q hq EP
  have hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + BV) :=
    ⟨m, r, L, hLc, by rw [hsum]; simp only [toRDivisor_eq_mapCoeffs]⟩
  obtain ⟨-, -, -, E₀, _, _, _, _, -, hdiv₀, hw₀⟩ :=
    (isDiscrepancy_comap_functionFieldMap_iff hV hω hKV hKD q hM hq hDY hKM E' b).mp
      (hE' ▸ ⟨hKV, hKD, hasNonemptyCenter_valuation EP, EP, ω, m, r, L, rfl, rfl, hb⟩)
  exact hlc E₀.toDivisorOver _ (isLogDiscrepancy_of_isDiscrepancyWith (hdiv₀ ▸ hKM) hw₀)

end CrepantDescent

end LogCanonical

section AmpleModelGraph

variable {X Z M V G : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
  [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  [CompactSpace G] [IsLocallyNoetherian G] [IsNormal G]

/-- Let `φ : X ⤏ M` be a birational map over `Z`, `q : M ⟶ V` and `p : V ⟶ Z` with
`q ≫ p = π_M`, and `(G, u, v)` a graph of `X ⤏ V` over `Z`. If `v` sends `η_E` to `η_P`, `q`
sends `η_{P_M}` to `η_P`, both local isomorphisms there, and `φ_* Q = P_M`, then `u(η_E) = η_Q`. -/
private theorem map_genericPoint_eq_of_transformPrimeDivisor_eq_some [IsIntegral Z] [IsIntegral V]
    [IsIntegral G] [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (M ↘ ⊤_ Scheme)]
    {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {u : G ⟶ X}
    {v : G ⟶ V} {φ : X.RationalMap M} [IsDominant f] [IsDominant πM] [IsSeparated πM]
    [IsDominant q] [IsDominant p] [IsDominant u] [IsDominant v]
    (hbf : Function.Bijective (functionFieldMap f))
    (hbπ : Function.Bijective (functionFieldMap πM)) (hφ : MMP.Flips.RationalMap.IsOver f πM φ)
    (hqp : q ≫ p = πM) (hc : u ≫ f = v ≫ p) (hXnv : IsNormalVariety ℂ sX)
    (hGu : IsNormalVariety ℂ (u ≫ sX)) (hu : IsBirationalMorphism u)
    (E : MMP.Mori.PrimeDivisor G) (P : MMP.Mori.PrimeDivisor V) (PM : MMP.Mori.PrimeDivisor M)
    (hvE : v E.genericPoint = P.genericPoint) (_ : IsIso (v.stalkMap E.genericPoint))
    (hqPM : q PM.genericPoint = P.genericPoint) (_ : IsIso (q.stalkMap PM.genericPoint))
    (Q : MMP.Mori.PrimeDivisor X) (hQ : RationalMap.transformPrimeDivisor φ Q = some PM) :
    u E.genericPoint = Q.genericPoint := by
  have h3 := valuationOver_eq_of_transformPrimeDivisor_eq_some hbf hbπ hφ hQ
  have h2 := valuationOver_eq_of_isIso q p hqp PM P hqPM
  have h1 := valuationOver_eq_of_isIso v p (c := u ≫ f) hc.symm E P hvE
  have hval : E.valuationOver u = Q.valuationOver (𝟙 X) := by
    refine Valuation.ext fun t => ?_
    obtain ⟨c, rfl⟩ := hbf.2 t
    have := congrArg (fun w : Valuation Z.functionField _ => w c)
      (h1.trans (h2.symm.trans h3.symm))
    simp only [PrimeDivisor.valuationOver_apply] at this ⊢
    rw [functionFieldMap_comp_apply u f rfl, this, MMP.Mori.functionFieldMap_id_apply]
  let DE : DivisorOver ℂ sX := ⟨G, u, hGu, hu, E⟩
  have hDE : DE.valuation = (DivisorOver.ofPrimeDivisor ℂ hXnv Q).valuation := hval
  exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXnv.1 hDE

/-- In the situation of `map_genericPoint_eq_of_transformPrimeDivisor_eq_some`, the coefficient
of `φ_* B` along `P_M` is the coefficient of `B` along `Q`. -/
private theorem transformDivisor_apply_eq_of_transformPrimeDivisor_eq_some [IsIntegral Z]
    [IsIntegral V] [IsIntegral G] [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (M ↘ ⊤_ Scheme)]
    {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {u : G ⟶ X}
    {v : G ⟶ V} {φ : X.RationalMap M} [IsDominant f] [IsDominant πM] [IsSeparated πM]
    [IsDominant q] [IsDominant p] [IsDominant u] [IsDominant v] {B : QDivisor X}
    (hbf : Function.Bijective (functionFieldMap f))
    (hbπ : Function.Bijective (functionFieldMap πM)) (hφ : MMP.Flips.RationalMap.IsOver f πM φ)
    (hqp : q ≫ p = πM) (hc : u ≫ f = v ≫ p) (hXnv : IsNormalVariety ℂ sX)
    (hGu : IsNormalVariety ℂ (u ≫ sX)) (hu : IsBirationalMorphism u)
    (E : MMP.Mori.PrimeDivisor G) (P : MMP.Mori.PrimeDivisor V) (PM : MMP.Mori.PrimeDivisor M)
    (hvE : v E.genericPoint = P.genericPoint) (hvi : IsIso (v.stalkMap E.genericPoint))
    (hqPM : q PM.genericPoint = P.genericPoint) (hqi : IsIso (q.stalkMap PM.genericPoint))
    (Q : MMP.Mori.PrimeDivisor X) (hQ : RationalMap.transformPrimeDivisor φ Q = some PM) :
    (RationalMap.transformDivisor φ B) PM = B Q :=
  have hmatch := map_genericPoint_eq_of_transformPrimeDivisor_eq_some hbf hbπ hφ hqp hc hXnv
    hGu hu E P PM hvE hvi hqPM hqi
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hQ (fun Q' hQ' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((hmatch Q' hQ').symm.trans
      (hmatch Q hQ))) B

/-- For an ample-model datum `(M, B_M, q, V, B_V)` of a birational contraction `f : X ⟶ Z`, with
structure morphism `p : V ⟶ Z`, a canonical divisor `K_V` of `V` compatible with `K_X`
(`p_* K_V = f_* K_X`), and a normalized graph `(G, u, v)` of the birational map `X ⤏ V` over `Z`,
the `ℚ`-divisors `K_X + B` and `K_V + B_V` are `ℚ`-Cartier, their pull-backs to `G` are defined,
and `v_*(u^*(K_X + B) - v^*(K_V + B_V)) = 0`. -/
@[mmp "lem_oai4_c3_ample_model_graph_pushforward"]
public theorem IsAmpleModelDatum.transformDivisor_pullback_sub_pullback_eq_zero
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV)
    {KV : Divisor V} {n : ℕ} (hKV : KV.IsCanonicalDivisor (p ≫ sZ) n)
    (hKVK : RationalMap.transformDivisor (X := V) p.toRationalMap KV =
      RationalMap.transformDivisor (X := X) f.toRationalMap K)
    {u : G ⟶ X} {v : G ⟶ V} (hG : IsNormalizedGraph f p u v) :
    ∃ (hD : (Divisor.toQDivisor K + B).IsQCartier)
      (hDV : (Divisor.toQDivisor KV + BV).IsQCartier)
      (hu : ∀ T : irreducibleComponents G,
        u (componentGenericPoint G T) ∉ (Divisor.toQDivisor K + B).supp)
      (hv : ∀ T : irreducibleComponents G,
        v (componentGenericPoint G T) ∉ (Divisor.toQDivisor KV + BV).supp),
      RationalMap.transformDivisor (X := G) v.toRationalMap
        ((Divisor.toQDivisor K + B).pullback hD hu -
          (Divisor.toQDivisor KV + BV).pullback hDV hv) = 0 := by
  obtain ⟨hqp, hVint, hVnv, hMnv, hqprop, hqbir⟩ := h.isProper_and_isBirationalMorphism
  obtain ⟨hpproj, hpbir⟩ := h.isProjectiveMorphism_and_isBirationalMorphism
  have hc := h.isContraction
  have hXnv : IsNormalVariety ℂ sX := hc.isNormalVariety_source
  have hZnv : IsNormalVariety ℂ sZ := hc.isNormalVariety_target
  have hXnv' : IsNormalVariety ℂ (f ≫ sZ) := hc.comp_eq ▸ hXnv
  have := hG.isIntegral
  have := hG.isFinite
  have : IsIntegral Z := hZnv.1.toIsIntegral
  have : IsNormal Z := hZnv.2
  have : LocallyOfFiniteType sZ := hZnv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : LocallyOfFiniteType sX := hXnv.1.toLocallyOfFiniteType
  have : IsProper f := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  have : IsProper p := isProper_of_isProjectiveMorphism _ hpproj
  have : IsProper v := by rw [← Limits.pullback.lift_snd u v hG.comp_eq]; infer_instance
  have : IsProper u := by rw [← Limits.pullback.lift_fst u v hG.comp_eq]; infer_instance
  have hGv : IsNormalVariety ℂ (v ≫ p ≫ sZ) := by
    refine ⟨?_, inferInstance⟩
    have := hVnv.1
    exact (isVariety_iff ℂ (v ≫ p ≫ sZ)).mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hsG : v ≫ p ≫ sZ = u ≫ sX := by
    rw [← Category.assoc, ← hG.comp_eq, Category.assoc, hc.comp_eq]
  have hGu : IsNormalVariety ℂ (u ≫ sX) := hsG ▸ hGv
  have hGf : IsNormalVariety ℂ ((u ≫ f) ≫ sZ) := by rwa [Category.assoc, hc.comp_eq]
  have := hG.isBirationalMorphism_minus.isDominant
  have := hG.isBirationalMorphism_plus.isDominant
  have := hqbir.isDominant
  have := hpbir.isDominant
  have := h.isBirationalMorphism.isDominant
  have hbu := hG.isBirationalMorphism_minus.functionFieldMap_bijective
  have hbf := h.isBirationalMorphism.functionFieldMap_bijective
  -- the `ℚ`-Cartier divisors and their pull-backs
  obtain ⟨hDV, hDVa⟩ := h.isQCartier_and_hasRelativelyAmpleMultiple hKV
  have hD : (Divisor.toQDivisor K + B).IsQCartier := by
    obtain ⟨N, hN, L, hL, hLq, -⟩ := h.hasRelativelyAmpleMultiple
    refine ⟨-(N : ℤ), by exact_mod_cast (neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hN.ne')), L,
      ?_, hL⟩
    rw [hLq, neg_smul, smul_neg]
  have hu : ∀ T : irreducibleComponents G,
      u (componentGenericPoint G T) ∉ (Divisor.toQDivisor K + B).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' u _
  have hv : ∀ T : irreducibleComponents G,
      v (componentGenericPoint G T) ∉ (Divisor.toQDivisor KV + BV).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' v _
  refine ⟨hD, hDV, hu, hv, ?_⟩
  -- separatedness and birationality of the structure maps over `Z`
  have : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    have := hZnv.1
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (M ↘ Limits.terminal Scheme) := by
    have := hMnv.1
    rw [show (M ↘ Limits.terminal Scheme) =
        (q ≫ p ≫ sZ) ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsDominant πM := by rw [← hqp]; infer_instance
  have : IsProper πM := by rw [← hqp]; infer_instance
  have hbπ : Function.Bijective (functionFieldMap πM) := by
    have : (functionFieldMap q) ∘ (functionFieldMap p) = functionFieldMap πM :=
      funext fun t => functionFieldMap_comp_apply q p hqp t
    rw [← this]
    exact hqbir.functionFieldMap_bijective.comp hpbir.functionFieldMap_bijective
  have hmatch := map_genericPoint_eq_of_transformPrimeDivisor_eq_some hbf hbπ
    h.isGoodLogMinimalModel.isOver hqp hG.comp_eq hXnv hGu hG.isBirationalMorphism_minus
  have hφB := transformDivisor_apply_eq_of_transformPrimeDivisor_eq_some (B := B) hbf hbπ
    h.isGoodLogMinimalModel.isOver hqp hG.comp_eq hXnv hGu hG.isBirationalMorphism_minus
  -- `g_* H = 0` for `g = u ≫ f : G ⟶ Z`
  have hgbir : IsBirationalMorphism (u ≫ f) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational f u
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hG.isBirationalMorphism_minus)
  have hpush : RationalMap.transformDivisor (u ≫ f).toRationalMap
      ((Divisor.toQDivisor K + B).pullback hD hu -
        (Divisor.toQDivisor KV + BV).pullback hDV hv) = 0 := by
    refine Finsupp.ext fun Q => ?_
    obtain ⟨E, hgE, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZnv hGf hgbir Q
    rw [htr, Finsupp.coe_zero, Pi.zero_apply]
    obtain ⟨QX, QV, huE, hvE, hui, hvi, hfQ, hpQ, hK'⟩ :=
      exists_strictTransforms_of_map_eq_genericPoint hZnv hXnv' hVnv h.isBirationalMorphism hpbir
        hG.isBirationalMorphism_minus hG.isBirationalMorphism_plus hG.comp_eq hgE
    obtain ⟨PM, hqPM, hPMiso, htrq⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hVnv hMnv hqbir QV
    have hφQ : RationalMap.transformPrimeDivisor φ QX = some PM :=
      transformPrimeDivisor_eq_some_of_map_eq hbπ h.isGoodLogMinimalModel.isOver hfQ
        (by rw [← hqp, Scheme.Hom.comp_apply, hqPM, hpQ])
    have hnex : ¬ MMP.Flips.RationalMap.IsInverseExceptional φ PM := by
      simpa [MMP.Flips.RationalMap.IsInverseExceptional] using ⟨QX, hφQ⟩
    have hBM := h.isGoodLogMinimalModel.coeff_boundary PM
    simp only [DivisorWithCoeffs.coeff] at hBM
    rw [ite_eq_right hnex, hφB E QV PM hvE hvi hqPM hPMiso QX hφQ] at hBM
    rw [Finsupp.sub_apply, coeff_pullback_eq_of_isIso E QX huE hD hu,
      coeff_pullback_eq_of_isIso E QV hvE hDV hv]
    change ((K QX : ℤ) : ℚ) + B QX - (((KV QV : ℤ) : ℚ) + BV QV) = 0
    rw [h.boundary_eq, htrq, hBM, hK' K KV hKVK]
    ring
  -- the graph divisor is effective, by the negativity lemma for `g`
  have hgproj : IsProjectiveMorphism (u ≫ f) := by
    rw [hG.comp_eq]
    exact (isProjectiveMorphism_snd hc.isProjectiveMorphism hpproj
      h.isProjectiveVariety_target.isProjective hG).comp hpproj
  have heff := isEffective_of_hasRelativelyAmpleMultiple_neg ℂ hGf hZnv (v := u ≫ f) rfl hgproj
    hgbir (g := u ≫ f) (w := 𝟙 Z) (Category.comp_id _).symm
    (hasRelativelyAmpleMultiple_neg_pullback_sub_pullback hG hD hDV hu hv
      h.hasRelativelyAmpleMultiple hDVa) hpush
  -- the coefficient along the strict transform `E` of a prime divisor `P` of `V`
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, hvE, hEiso, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    hVnv hGv hG.isBirationalMorphism_plus P
  rw [map_sub, Finsupp.sub_apply, htr, htr, Finsupp.coe_zero, Pi.zero_apply]
  have h0 := heff E
  simp only [DivisorWithCoeffs.coeff, Finsupp.sub_apply, sub_nonneg] at h0
  rw [coeff_pullback_eq_of_isIso E P hvE hDV hv] at h0 ⊢
  obtain ⟨nX, hK⟩ := h.isCanonicalDivisor
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXnv hK
  have hlc := pullback_apply_le_one_add_ordForm hXnv hK h.isLogCanonicalPair hω0 hω hGu
    hG.isBirationalMorphism_minus hD hu E
  obtain ⟨PM, hqPM, hPMiso, htrq⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hVnv hMnv hqbir P
  have hBM := h.isGoodLogMinimalModel.coeff_boundary PM
  simp only [DivisorWithCoeffs.coeff] at hBM
  change ((KV P : ℤ) : ℚ) + BV P ≤ _ at h0
  change _ - (((KV P : ℤ) : ℚ) + BV P) = 0
  rw [coeff_eq_ordForm_pullback_of_isCanonicalDivisor hZnv hc.comp_eq hXnv hVnv
      h.isBirationalMorphism hpbir hGu hG.isBirationalMorphism_minus hG.isBirationalMorphism_plus
      hG.comp_eq hK hKV hKVK hω0 hω hvE, h.boundary_eq, htrq, hBM] at h0 ⊢
  by_cases hex : MMP.Flips.RationalMap.IsInverseExceptional φ PM
  · have := transformDivisor_apply_nonneg φ h.isLogCanonicalPair.2.1 PM
    rw [ite_eq_left hex] at h0 ⊢
    linarith
  · obtain ⟨Q, hQ⟩ : ∃ Q, RationalMap.transformPrimeDivisor φ Q = some PM := by
      simpa [MMP.Flips.RationalMap.IsInverseExceptional] using hex
    rw [ite_eq_right hex]
    have huE := hmatch E P PM hvE hEiso hqPM hPMiso Q hQ
    have := isIso_stalkMap_of_map_eq_genericPoint hbu huE
    rw [coeff_pullback_eq_of_isIso E Q huE hD hu,
      MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso u hbu
        (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hK.topologicalKrullDim_eq)
        E Q huE ω,
      hω Q, hφB E P PM hvE hEiso hqPM hPMiso Q hQ]
    change ((K Q : ℤ) : ℚ) + B Q - (((K Q : ℤ) : ℚ) + (B Q + 0)) = 0
    ring

open CategoryTheory.Limits MMP.Flips in
/-- For an ample-model datum `(M, B_M, q, V, B_V)` of a birational contraction `f : X ⟶ Z`, with
structure morphism `p : V ⟶ Z`, a canonical divisor `K_V` of `V` compatible with `K_X`
(`p_* K_V = f_* K_X`), and a normalized graph `(G, u, v)` of the birational map `X ⤏ V` over `Z`,
the `ℚ`-divisors `K_X + B` and `K_V + B_V` are `ℚ`-Cartier, their pull-backs to `G` are defined,
and `u^*(K_X + B) - v^*(K_V + B_V)` is effective. -/
@[mmp "lem_oai4_c3_ample_model_graph_divisor"]
public theorem IsAmpleModelDatum.isEffective_pullback_sub_pullback
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV)
    {KV : Divisor V} {n : ℕ} (hKV : KV.IsCanonicalDivisor (p ≫ sZ) n)
    (hKVK : RationalMap.transformDivisor (X := V) p.toRationalMap KV =
      RationalMap.transformDivisor (X := X) f.toRationalMap K)
    {u : G ⟶ X} {v : G ⟶ V} (hG : IsNormalizedGraph f p u v) :
    ∃ (hD : (Divisor.toQDivisor K + B).IsQCartier)
      (hDV : (Divisor.toQDivisor KV + BV).IsQCartier)
      (hu : ∀ T : irreducibleComponents G,
        u (componentGenericPoint G T) ∉ (Divisor.toQDivisor K + B).supp)
      (hv : ∀ T : irreducibleComponents G,
        v (componentGenericPoint G T) ∉ (Divisor.toQDivisor KV + BV).supp),
      ((Divisor.toQDivisor K + B).pullback hD hu -
        (Divisor.toQDivisor KV + BV).pullback hDV hv).IsEffective := by
  obtain ⟨hD, hDV, hu, hv, hzero⟩ := h.transformDivisor_pullback_sub_pullback_eq_zero hKV hKVK hG
  refine ⟨hD, hDV, hu, hv, ?_⟩
  have : IsIntegral G := hG.isIntegral
  obtain ⟨hpproj, -⟩ := h.isProjectiveMorphism_and_isBirationalMorphism
  obtain ⟨-, _, hVvar, -, -, -⟩ := h.isProper_and_isBirationalMorphism
  have hfproj := h.isContraction.isProjectiveMorphism
  have hZproj : IsProjectiveMorphism sZ := h.isProjectiveVariety_target.isProjective
  have hvproj := isProjectiveMorphism_snd hfproj hpproj hZproj hG
  have := isProper_of_isProjectiveMorphism f hfproj
  have := isProper_of_isProjectiveMorphism p hpproj
  have := isProper_of_isProjectiveMorphism v hvproj
  have := isProper_of_isProjectiveMorphism sZ hZproj
  have hGv : AlgebraicGeometry.IsVariety ℂ (v ≫ p ≫ sZ) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  exact isEffective_of_hasRelativelyAmpleMultiple_neg ℂ ⟨hGv, inferInstance⟩ hVvar rfl hvproj
    hG.isBirationalMorphism_plus hG.comp_eq
    (hasRelativelyAmpleMultiple_neg_pullback_sub_pullback hG hD hDV hu hv
      h.hasRelativelyAmpleMultiple (h.isQCartier_and_hasRelativelyAmpleMultiple hKV).2) hzero

open CategoryTheory.Limits in
/-- For an ample-model datum `(M, B_M, q, V, B_V)` of a birational contraction `f : X ⟶ Z`, with
structure morphism `p : V ⟶ Z`, a canonical divisor `K_V` of `V` compatible with `K_X`, a
normalized graph `(G, u, v)` of `X ⤏ V` over `Z`, and a point `z` of `Z` outside the biregular
locus of `f` or of `p`, the `ℚ`-divisors `K_X + B` and `K_V + B_V` are `ℚ`-Cartier, their
pull-backs to `G` are defined, and the fibre of `G ⟶ Z` over `z` is contained in the support of
`u^*(K_X + B) - v^*(K_V + B_V)`. -/
@[mmp "lem_oai4_c3_ample_model_graph_support"]
public theorem IsAmpleModelDatum.preimage_singleton_subset_supp_pullback_sub_pullback
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV)
    {KV : Divisor V} {n : ℕ} (hKV : KV.IsCanonicalDivisor (p ≫ sZ) n)
    (hKVK : RationalMap.transformDivisor (X := V) p.toRationalMap KV =
      RationalMap.transformDivisor (X := X) f.toRationalMap K)
    {u : G ⟶ X} {v : G ⟶ V} (hG : IsNormalizedGraph f p u v)
    {z : Z} (hz : z ∉ biregularLocus f ⊓ biregularLocus p) :
    ∃ (hD : (Divisor.toQDivisor K + B).IsQCartier)
      (hDV : (Divisor.toQDivisor KV + BV).IsQCartier)
      (hu : ∀ T : irreducibleComponents G,
        u (componentGenericPoint G T) ∉ (Divisor.toQDivisor K + B).supp)
      (hv : ∀ T : irreducibleComponents G,
        v (componentGenericPoint G T) ∉ (Divisor.toQDivisor KV + BV).supp),
      (u ≫ f) ⁻¹' {z} ⊆ ((Divisor.toQDivisor K + B).pullback hD hu -
        (Divisor.toQDivisor KV + BV).pullback hDV hv).supp := by
  obtain ⟨hD, hDV, hu, hv, heff⟩ := h.isEffective_pullback_sub_pullback hKV hKVK hG
  refine ⟨hD, hDV, hu, hv, ?_⟩
  have : IsIntegral G := hG.isIntegral
  have : IsNoetherian G := {}
  obtain ⟨hpproj, hpbir⟩ := h.isProjectiveMorphism_and_isBirationalMorphism
  obtain ⟨-, _, -, -, -, -⟩ := h.isProper_and_isBirationalMorphism
  have hZn : IsNormalVariety ℂ sZ := h.isContraction.isNormalVariety_target
  have : IsIntegral Z := hZn.1.toIsIntegral
  have : IsNormal Z := hZn.2
  have : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := isProper_of_isProjectiveMorphism f h.isContraction.isProjectiveMorphism
  have := isProper_of_isProjectiveMorphism p hpproj
  have := isProper_of_isProjectiveMorphism sZ h.isProjectiveVariety_target.isProjective
  have := hG.isFinite
  have : IsProper u := by rw [← pullback.lift_fst u v hG.comp_eq]; infer_instance
  have : IsProper v := by rw [← pullback.lift_snd u v hG.comp_eq]; infer_instance
  have := hG.isBirationalMorphism_minus.isDominant
  have := hG.isBirationalMorphism_plus.isDominant
  have : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace (u ≫ f ≫ sZ)
  have hgb : IsBirationalMorphism (u ≫ f) := MMP.Mori.isBirationalMorphism_comp_of_isBirational f u
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hG.isBirationalMorphism_minus)
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    (u ≫ f ≫ sZ) sZ
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance } hZn (u ≫ f) hgb).2
  refine (Set.preimage_mono (Set.singleton_subset_iff.mpr hz)).trans
    (preimage_compl_subset_of_isClosed (u ≫ f).continuous
      (biregularLocus f ⊓ biregularLocus p).isOpen
      (TopologicalSpace.Closeds.isClosed _) fun x hx hgx => ?_)
  exact mem_supp_of_isPreconnected_fibre (u ≫ f ≫ sZ) heff
    (hasRelativelyAmpleMultiple_neg_pullback_sub_pullback hG hD hDV hu hv
      h.hasRelativelyAmpleMultiple (h.isQCartier_and_hasRelativelyAmpleMultiple hKV).2)
    hx (by simpa using (u ≫ f).isClosedMap _ hx) (hconn _).isPreconnected
    fun h1 => hgx (mem_biregularLocus_of_preimage_eq_singleton h.isBirationalMorphism hpbir
      hG.comp_eq h1)

end AmpleModelGraph

section AmpleModelLC

open MMP.Flips

variable {X Z M V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
  [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]

/-- For an ample-model datum `(M, B_M, q, V, B_V)` of a birational contraction `f : X ⟶ Z`, with
structure morphism `p : V ⟶ Z`, the pair `(V, B_V)` is log canonical. -/
@[mmp "lem_oai4_c3_ample_model_lc"]
public theorem IsAmpleModelDatum.isLogCanonicalPair_ampleModel
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV) :
    MMP.Intersection.IsLogCanonicalPair (p ≫ sZ) BV := by
  classical
  obtain ⟨hqp, -, hV, hM, hqprop, hqb⟩ := h.isProper_and_isBirationalMorphism
  have hlm := h.isGoodLogMinimalModel
  have hsM : sM = q ≫ p ≫ sZ := by rw [← hlm.comp_eq_model, ← hqp, Category.assoc]
  subst hsM
  have : IsDominant q := hqb.isDominant
  have := hV.1
  have := hM.1
  have : LocallyOfFiniteType (p ≫ sZ) := hV.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (q ≫ p ≫ sZ) := hM.1.toLocallyOfFiniteType
  have : QuasiCompact (p ≫ sZ) := hV.1.toQuasiCompact
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p ≫ sZ)
  have hBMlc : MMP.Intersection.IsLogCanonicalPair (q ≫ p ≫ sZ) BM := hlm.isDltPair.1
  -- dimensions and canonical divisors, cut out by one rational top form
  obtain ⟨n, hKM⟩ := hlm.isCanonicalDivisor
  have hnV : topologicalKrullDim V = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (p ≫ sZ) (q ≫ p ≫ sZ)
      hqb).trans hKM.topologicalKrullDim_eq
  obtain ⟨ω, hω0, hωV, hωM⟩ := exists_divisorOfForm_eq_transformDivisor hV hM hqb hnV hKM
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (p ≫ sZ) hV hnV
  have hKVc : (divisorOfForm ω).IsCanonicalDivisor (p ≫ sZ) n :=
    hK₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hV hK₀ hω0)
  have hKMc : (divisorOfForm (pullbackRationalPluriForms (p ≫ sZ) q ω)).IsCanonicalDivisor
      (q ≫ p ≫ sZ) n := hωM ▸ hKM
  -- `K_V + B_V` is `ℚ`-Cartier
  have hQ := (h.isQCartier_and_hasRelativelyAmpleMultiple hKVc).1
  -- `K_M + B_M = q^*(K_V + B_V)`
  obtain ⟨k, hk, D, hD, hDC, hfree, A, e, he, hind⟩ := h.isRelativeAmpleModel
  obtain ⟨d, hd, H, hH, -, ⟨eH⟩⟩ :=
    DivisorialSectionAlgebra.exists_isRelativelyAmple_pullback_iso h.isProjectiveVariety_target
      hlm.isProjectiveMorphism_model hDC hfree A e he hind
  obtain ⟨hTc, hB, hTp⟩ := isPullback_transformDivisor_of_iso hV hM hqb H eH
  set T : Divisor V := RationalMap.transformDivisor (X := M) q.toRationalMap ((d : ℤ) • D)
  set r : Fin 1 → ℝ := fun _ => ((d : ℝ) * k)⁻¹
  have hdk : ((d : ℝ) * k) ≠ 0 := by positivity
  have hcoeff : ∀ E : MMP.Mori.PrimeDivisor M, ((KM.coeff E : ℤ) : ℝ) + ((BM.coeff E : ℚ) : ℝ) =
      ((d : ℝ) * k)⁻¹ * ((((d : ℤ) • D).coeff E : ℤ) : ℝ) := by
    intro E
    have hDE := congrArg (fun G : QDivisor M => G.coeff E) hD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hDE
    have hDE' : ((D.coeff E : ℤ) : ℝ) =
        (k : ℝ) * (((KM.coeff E : ℤ) : ℝ) + ((BM.coeff E : ℚ) : ℝ)) := by
      exact_mod_cast congrArg (fun t : ℚ => (t : ℝ)) hDE
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul, Int.cast_mul, hDE']
    field_simp
    push_cast
    ring
  have hpresV : Divisor.toRDivisor (divisorOfForm ω) + QDivisor.toRDivisor BV =
      ∑ j, r j • Divisor.toRDivisor ((fun _ : Fin 1 => T) j) := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    obtain ⟨E, -, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hV hM hqb P
    rw [MMP.Fourfold.coeff_sum_smul_toRDivisor, Fin.sum_univ_one, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, hωV, h.boundary_eq]
    change ((RationalMap.transformDivisor (X := M) q.toRationalMap KM P : ℤ) : ℝ) +
      ((RationalMap.transformDivisor (X := M) q.toRationalMap BM P : ℚ) : ℝ) =
        r 0 * ((RationalMap.transformDivisor (X := M) q.toRationalMap ((d : ℤ) • D) P : ℤ) : ℝ)
    rw [htr, htr, htr]
    exact hcoeff E
  have hpresM : Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms (p ≫ sZ) q ω)) +
      QDivisor.toRDivisor BM =
        ∑ j, r j • Divisor.toRDivisor ((fun _ : Fin 1 => (d : ℤ) • D) j) := by
    refine DivisorWithCoeffs.ext' fun E => ?_
    rw [MMP.Fourfold.coeff_sum_smul_toRDivisor, Fin.sum_univ_one, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, hωM]
    exact hcoeff E
  have hDY : IsRCartierPullback q
      (Divisor.toRDivisor (divisorOfForm ω) + QDivisor.toRDivisor BV)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms (p ≫ sZ) q ω)) +
        QDivisor.toRDivisor BM) :=
    ⟨1, r, fun _ => T, fun _ => (d : ℤ) • D, fun _ => hTc, hpresV, fun _ => ⟨hB, hTp⟩, hpresM⟩
  refine ⟨⟨hV, n, divisorOfForm ω, hKVc, hQ⟩, fun P => ?_, ?_⟩
  · -- the boundary `B_V = q_* B_M` is effective
    obtain ⟨E, -, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hV hM hqb P
    rw [h.boundary_eq]
    change 0 ≤ RationalMap.transformDivisor (X := M) q.toRationalMap BM P
    rw [htr]
    exact hBMlc.2.1 E
  · -- every log discrepancy of `(V, B_V)` is one of `(M, B_M)`
    intro n' E a ha
    obtain rfl : n' = n := by
      exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
        hnV
    exact nonneg_of_isLogDiscrepancy_of_isRCartierPullback hV q hM hqb hω0 hKVc hKMc
      (fun _ => hTc) hpresV hDY (hBMlc.2.2 _) ha

end AmpleModelLC

end MMP.Fourfold
