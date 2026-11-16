module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Strict increase of discrepancies off the domain of a log canonical model

Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a log canonical model of `f : (X, D_X) ⟶ Z` with respect to `𝓕`,
through the modification `φ : X ⤏ Y`. If `B` is a divisor of `k(X) = k(Y)` with nonempty center
on `X` and `φ` is not defined at the generic point `x` of `Center_X(B)`, then
`a(B, D_{𝓕,Y}) > a(B, D_X)`.

`B` is realized as a prime divisor `E` of a model `h : W' ⟶ W` of the given common model
`(W, p, q)`, and `(W', h ≫ p, h ≫ q)` is again a common model, with `(h ≫ p)(η_E) = x`. On a common
model the `ℝ`-divisor `Δ = p^*(K_X + D_X) - q^*(K_Y + D_{𝓕,Y}) + (div_W(q^*ω_Y) - div_W(p^*ω_X))`
has coefficient `a(P, D_{𝓕,Y}) - a(P, D_X)` along every prime divisor `P` of `W`
(FA (2.23.4)); it is effective by the negativity lemma, and `-Δ` is `p`-nef, since pull-backs from
`X` are trivial on the curves contracted by `p`.

If `Δ` had coefficient `0` along `E`, the negativity lemma over a point would make `p⁻¹(x)`
disjoint from `Supp Δ`, so `p⁻¹(y)` misses `Supp Δ` for a closed point `y` of `closure {x}`
outside the closed set `p(Supp Δ)`. Since `φ` is not defined at `x`, it is not defined at `y`.
If `q` were constant on `p⁻¹(y)`, with value in an affine open `V`, then over an open `U ∋ y`
with `p⁻¹(U) ⊆ q⁻¹(V)` the ring map `Γ(V, 𝒪_Y) ⟶ Γ(p⁻¹ U, 𝒪_W) ≅ Γ(U, 𝒪_X)` (by `p_* 𝒪_W = 𝒪_X`)
would define `φ` on `U`. So the connected fibre `p⁻¹(y)` contains a proper curve `C` not
contracted by `q`, and `q(C)` is a curve contracted by `g`. Then `Δ · C ≥ 0`, as `C ⊄ Supp Δ`,
while `Δ · C = -q^*(K_Y + D_{𝓕,Y}) · C = -[k(C) : k(q C)] (K_Y + D_{𝓕,Y}) · q(C) < 0` because
`K_Y + D_{𝓕,Y}` is `g`-ample: a contradiction.

## Main results

* `MMP.Flips.IsLogCanonicalModelOf.isDiscrepancy_lt`.

## Implementation notes

As in `MMP.Flips.IsWeakLogCanonicalModelOf.isDiscrepancy_le`, the function fields `k(X)` and
`k(Y)` are identified through `φ` by a common model `(W, p, q)` of `φ`
(`MMP.Flips.IsCommonModel`): `B` is a valuation `v` of `k(X)` together with the valuation `v'`
of `k(Y)`, both induced by one valuation `w` of `k(W)`. The center of `B` on `X` is
`Center_X(B) = h(E)` for a divisor `(V, h, E)` over `X` with `ord_E = v`; its generic point is
`h(η_E)`. The center does not depend on the divisor chosen, so it suffices to ask that `φ` be
undefined at `h(η_E)` for one such divisor.

The discrepancies are computed with forms `ω_X`, `ω_Y` with `div ω_X = K_X`, `div ω_Y = K_Y`; the
correction `div_W(q^*ω_Y) - div_W(p^*ω_X)` is principal, so it is Cartier and of degree zero on
every proper curve. The source's step through the closure `Γ ⊆ X ×_Z Y` of the graph of `φ` and
Zariski's main theorem is replaced by the rigidity argument above, which shows directly that `q`
is not constant on `p⁻¹(y)`; the curve `C` is then found in the fibre itself rather than lifted
from `q(p⁻¹(y))`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.23.3
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori
open scoped WithZero

universe u

namespace MMP.Flips

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
    {ν : C' ⟶ C.scheme}
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
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
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
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by
    rw [← Category.assoc]
    infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
  have hc2 := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
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

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]
    infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_comp_eq_of_isCurveNormalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

end Intersection

/-- **Projection formula** for a pull-back `L₁ = h^*D` of a Cartier divisor `D` along
`h : Y' ⟶ Y`: on a proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`L₁ · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_eq_mul_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- A divisor `L₁` given as a pull-back along `h` has degree zero on a proper curve whose image is
not a proper curve. -/
private theorem degreeOn_eq_zero_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (hnc : ¬ IsProperCurve sY (h C'.point)) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc = 0 := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hnc, map_zero]

/-- The pull-back of a Cartier divisor is Cartier. -/
private theorem isCartier_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} {L : Divisor X} (hL : L.IsCartier) {L' : Divisor Y}
    (h : ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp,
      L.IsPullback f hB L') : L'.IsCartier := by
  obtain ⟨hB, hp⟩ := h
  rw [← Divisor.IsPullback.pullback_eq hL hp]
  exact hL.isCartier_pullback f hB

/-- A pull-back of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {N : RDivisor X} {G : RDivisor Y} (h : IsRCartierPullback f N G) : IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  exact ⟨m, r, L', fun j => isCartier_of_isPullback (hL j) (hpb j),
    by simp only [toRDivisor_eq_mapCoeffs]⟩

/-- The difference of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_sub {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D - D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r (fun j => -r' j), Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The sum of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_add {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D + D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r r', Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add]

/-- A Cartier divisor `L₀` linearly equivalent to `0` has intersection number `0` with every proper
curve, for every presentation. -/
private theorem eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {L₀ : Divisor X} (hc : L₀.IsCartier) (h : L₀.LinearlyEquivalent 0)
    (C : ProperCurve sX) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX (Divisor.toRDivisor L₀) r L C x) : x = 0 := by
  have h1 := isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 1 => (1 : ℝ)) (fun _ => L₀)
    (fun _ => hc)
  rw [show ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor L₀ = Divisor.toRDivisor L₀ by simp] at h1
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx h1]
  simp [MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hc h]

/-- Two nonzero rational top forms on a normal variety of dimension `n` over a perfect field have
linearly equivalent divisors. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ τ' : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (divisorOfForm τ).LinearlyEquivalent (divisorOfForm τ') := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr τ' () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ'
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 τ' hτ'
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ, Scheme.ord_mul he (inv_ne_zero hc),
    ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm, coeff_divisorOfForm, e1, e2]
  ring

/-- The divisors of two nonzero rational top forms on a normal variety `X`, for two equal
structure morphisms, are linearly equivalent. -/
private theorem linearlyEquivalent_divisorOfForm_of_eq {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {s₁ s₂ : X ⟶ Spec (.of k)} (e : s₁ = s₂) [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    (hX : IsNormalVariety k s₂) {n : ℕ} (hn : topologicalKrullDim X = n)
    {τ : RationalPluriForms s₁ n 1} {τ' : RationalPluriForms s₂ n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (divisorOfForm τ).LinearlyEquivalent (divisorOfForm τ') := by
  subst e
  exact linearlyEquivalent_divisorOfForm hX hn hτ hτ'

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- The valuation of `E` over `C` through `a ≫ b` is that over `B` through `a`, restricted along
`b^*`. -/
private theorem comap_valuationOver {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] [IsLocallyNoetherian A] [IsNormal A] (E : MMP.Mori.PrimeDivisor A) (a : A ⟶ B)
    (b : B ⟶ C)
    [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    (E.valuationOver a).comap (functionFieldMap b) = E.valuationOver (a ≫ b) := by
  ext t
  change E.divisorialValuation (functionFieldMap a (functionFieldMap b t)) =
    E.divisorialValuation (functionFieldMap (a ≫ b) t)
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- A valuation of `k(Y)` is determined by its restriction to `k(Z)` along a birational
morphism `g : Y ⟶ Z`. -/
private theorem valuation_eq_of_comap_eq {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    {g : Y ⟶ Z} (hg : IsBirationalMorphism g) [IsDominant g]
    {v w : Valuation Y.functionField ℤᵐ⁰}
    (h : v.comap (functionFieldMap g) = w.comap (functionFieldMap g)) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hg.functionFieldMap_bijective.2 t
    exact congrArg (fun u => u s) h

section CommonModel

/-- The generic point of an irreducible scheme lies in every dense open. -/
private theorem genericPoint_mem_of_dense {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : Dense (U : Set X)) : genericPoint X ∈ U := by
  haveI : Nonempty X := IrreducibleSpace.toNonempty
  exact (_root_.genericPoint_specializes _).mem_open U.2 hU.nonempty.choose_spec

/-- The composite `p⁻¹(dom φ₀) ⟶ dom φ₀ ⟶ Y` is, at the generic point, `Spec k(W) ⟶ Spec k(X)`
followed by `φ₀`. -/
private theorem fromFunctionField_resLE_comp {W X Y : Scheme.{u}} [IsIntegral W] [IsIntegral X]
    (p : W ⟶ X) [IsDominant p] (φ₀ : X.PartialMap Y)
    (hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W)) :
    (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
      (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).fromFunctionField =
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ₀.fromFunctionField := by
  have hx : genericPoint X ∈ φ₀.domain := genericPoint_mem_of_dense φ₀.dense_domain
  have hW : genericPoint W ∈ p ⁻¹ᵁ φ₀.domain := genericPoint_mem_of_dense hd
  change (p ⁻¹ᵁ φ₀.domain).fromSpecStalkOfMem (genericPoint W) hW ≫
      p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom =
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
      φ₀.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ φ₀.hom
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono φ₀.domain.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (functionFieldMap_fromSpecStalk p).symm

/-- **A common model, at the generic point.** If `q = φ ∘ p` as maps for a dominant `p`, then
`Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_fromFunctionField_eq_of_comp_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] (q : W ⟶ Y)
    (H : ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  obtain ⟨φ₀, rfl, hd, heq⟩ := H
  have h1 := congrArg Scheme.RationalMap.fromFunctionField heq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap, fromFunctionField_resLE_comp,
    MMP.Flips.RationalMap.fromFunctionField_hom] at h1
  exact h1

/-- Conversely, if `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`, then
`q = φ ∘ p` as maps. -/
private theorem comp_eq_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap := by
  obtain ⟨φ₀, rfl⟩ := φ.exists_rep
  have hx := genericPoint_mem_of_dense φ₀.dense_domain
  have hW : genericPoint W ∈ p ⁻¹ᵁ φ₀.domain := by
    change p (genericPoint W) ∈ φ₀.domain
    rw [map_genericPoint_of_isDominant]
    exact hx
  have hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W) := (p ⁻¹ᵁ φ₀.domain).isOpen.dense ⟨_, hW⟩
  refine ⟨φ₀, rfl, hd, Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap, fromFunctionField_resLE_comp,
    MMP.Flips.RationalMap.fromFunctionField_hom]
  exact H

/-- The generic-point form of `q = φ ∘ p` is stable under precomposition with a dominant
`h : W' ⟶ W`. -/
private theorem specMap_fromFunctionField_comp {W' W X Y : Scheme.{u}} [IsIntegral W']
    [IsIntegral W] [IsIntegral X] (φ : X.RationalMap Y) (h : W' ⟶ W) (p : W ⟶ X) (q : W ⟶ Y)
    [IsDominant h] [IsDominant p]
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    Spec.map (CommRingCat.ofHom (functionFieldMap (h ≫ p))) ≫ φ.fromFunctionField =
      W'.fromSpecStalk (genericPoint W') ≫ h ≫ q := by
  have e : functionFieldMap (h ≫ p) = (functionFieldMap h).comp (functionFieldMap p) :=
    RingHom.ext fun t =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply h p t).symm
  rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, H, ← Category.assoc,
    functionFieldMap_fromSpecStalk h, Category.assoc]

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- **A common model lies over the base.** If `q = φ ∘ p` at the generic point of `W` and
`g ∘ φ = f`, then `p ≫ f = q ≫ g`, for `W` reduced and `Z` separated. -/
private theorem comp_eq_comp_of_specMap_fromFunctionField_eq {W X Y Z : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [Z.IsSeparated] {φ : X.RationalMap Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hφ : φ.compHom g = f.toRationalMap) (p : W ⟶ X) [IsDominant p]
    (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    p ≫ f = q ≫ g := by
  have h1 : (p ≫ f).toRationalMap = (q ≫ g).toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom,
      ← Category.assoc, ← functionFieldMap_fromSpecStalk p, Category.assoc,
      ← MMP.Flips.RationalMap.fromFunctionField_hom f, ← hφ,
      MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc, H, Category.assoc]
  obtain ⟨U, hU, hUl, hUr, e⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp h1
  have : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι hU
  refine ext_of_isDominant (ι := U.ι) ?_
  simp only [Scheme.PartialMap.restrict_hom, Scheme.Hom.toPartialMap_hom, Scheme.topIso_hom,
    Category.assoc] at e
  exact (Scheme.homOfLE_ι_assoc W hUl _).symm.trans (e.trans (Scheme.homOfLE_ι_assoc W hUr _))

end CommonModel

/-- **Composing a common model with a model of it.** If `(W, p, q)` is a common model of `φ` and
`h : W' ⟶ W` is a proper birational morphism from a normal variety, then `(W', h ≫ p, h ≫ q)` is a
common model of `φ`. -/
private theorem isCommonModel_comp {k : Type u} [Field k] {X Y Z W W' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q) (h : W' ⟶ W)
    [IsProper h] (hh : IsBirationalMorphism h) (hW' : IsNormalVariety k (h ≫ sW)) :
    IsCommonModel k sX sY sZ (h ≫ sW) f g φ (h ≫ p) (h ≫ q) := by
  have hWn := hW.isNormalVariety
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsIntegral W' := hW'.1.toIsIntegral
  haveI := hW.isProper_p
  haveI := hW.isProper_q
  haveI : IsDominant p := hW.isBirationalMorphism_p.isDominant
  haveI : IsDominant h := hh.isDominant
  have hhB := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hh
  have KF := specMap_fromFunctionField_eq_of_comp_eq φ p q hW.comp_eq
  exact
    { isVariety_X := hW.isVariety_X
      isVariety_Y := hW.isVariety_Y
      isVariety_Z := hW.isVariety_Z
      comp_f := hW.comp_f
      comp_g := hW.comp_g
      isProper_f := hW.isProper_f
      isProper_g := hW.isProper_g
      isModificationOf := hW.isModificationOf
      isNormalVariety := hW'
      comp_p := by rw [Category.assoc, hW.comp_p]
      comp_q := by rw [Category.assoc, hW.comp_q]
      isProper_p := inferInstance
      isProper_q := inferInstance
      isBirationalMorphism_p := isBirationalMorphism_comp_of_isBirational p h
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          hW.isBirationalMorphism_p) hhB
      isBirationalMorphism_q := isBirationalMorphism_comp_of_isBirational q h
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          hW.isBirationalMorphism_q) hhB
      comp_eq := comp_eq_of_specMap_fromFunctionField_eq φ (h ≫ p) (h ≫ q)
        (specMap_fromFunctionField_comp φ h p q KF) }

/-- Numerical equivalence over a base is reflexive on `ℝ`-Cartier divisors. -/
private theorem isNumericallyEquivalentOver_self {k : Type u} [Field k] {W X : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    {p : W ⟶ X} {D : RDivisor W} (hD : IsCartierCombination D) :
    IsNumericallyEquivalentOver k sW p D D :=
  ⟨hD, hD, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ hx₁ hx₂ =>
    (IsRIntersectionNumber.eq_and_linear k _ C).1 _ r₁ L₁ r₂ L₂ x₁ x₂ hx₁ hx₂⟩

/-! ### Intersection numbers of negatives, pull-backs and lifted curves -/

section Curves

variable {k : Type u} [Field k]

/-- An `ℝ`-Cartier divisor has an intersection number with every proper curve. -/
private theorem exists_isRIntersectionNumber {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D : RDivisor X}
    (hD : IsCartierCombination D) (C : ProperCurve sX) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX D r L C x := by
  obtain ⟨m, r, L, hL, hpres⟩ := hD
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  subst hpres
  exact ⟨m, r, L, _, isRIntersectionNumber_sum_degreeOn k sX C r L hL⟩

/-- If `q ≫ g` contracts `C'`, then `g` contracts the image curve `C = q(C')`. -/
private theorem isContractedBy_of_isContractedBy_comp {W Y Z : Scheme.{u}} {sW : W ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} (q : W ⟶ Y) [IsProper q] (g : Y ⟶ Z) (C' : ProperCurve sW)
    (C : ProperCurve sY) (hC : C.point = q C'.point) (hC' : C'.IsContractedBy (q ≫ g)) :
    C.IsContractedBy g := by
  intro y hy
  rw [hC] at hy
  have hsub : closure ({q C'.point} : Set Y) ⊆ q '' closure ({C'.point} : Set W) :=
    closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
      (q.isClosedMap _ isClosed_closure)
  obtain ⟨z, hz, rfl⟩ := hsub hy
  rw [hC]
  simpa only [Scheme.Hom.comp_apply] using hC' z hz

/-- The generic point of a proper curve specializes to a point other than itself. -/
private theorem exists_specializes_ne_of_isProperCurve {G : Scheme.{u}} {sG : G ⟶ Spec (.of k)}
    {p : G} (h : IsProperCurve sG p) : ∃ w, p ⤳ w ∧ w ≠ p := by
  by_contra hcon
  push Not at hcon
  have hsub : Subsingleton (closure ({p} : Set G)) := ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => Subtype.ext
    ((hcon a (specializes_iff_mem_closure.mpr ha)).trans
      (hcon b (specializes_iff_mem_closure.mpr hb)).symm)⟩
  have h1 := h.dim_eq
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq] at h1
  have h2 := @topologicalKrullDim_zero_of_discreteTopology (closure ({p} : Set G)) _
    (@Subsingleton.discreteTopology _ _ hsub)
  rw [h1] at h2
  exact absurd h2 (by decide)

variable {V T : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} [IsSeparated sT]
  [LocallyOfFiniteType sT]

/-- A proper curve which is not contracted by `u` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (u : V ⟶ T) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : ¬ ∃ t : T, Set.range (Γ.ι ≫ u) = {t} := by
  rintro ⟨t, ht⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨y, rfl⟩ := hx
  have h1 : (Γ.ι ≫ u) y ∈ Set.range (Γ.ι ≫ u) := ⟨y, rfl⟩
  have h2 : (Γ.ι ≫ u) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ u) := ⟨_, rfl⟩
  rw [ht] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- A morphism non-constant on a proper curve has positive residue degree at its generic
point. -/
private theorem residueFieldDegree_pos_of_not_isContractedBy (u : V ⟶ T) (hu : u ≫ sT = sV)
    (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : 0 < residueFieldDegree u Γ.point := by
  have hnc := not_exists_range_eq_singleton u Γ h
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have hP : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hc : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hnc
  have : IsIntegral φ.image := hc.toIsIntegral
  have hLφ : LocallyOfFiniteType φ := hP.toLocallyOfFiniteType
  have : QuasiCompact φ := instQuasiCompactOfUniversallyClosed φ
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι) := by
      rwa [Scheme.Hom.toImage_imageι]
    exact locallyOfFiniteType_of_comp _ φ.imageι
  have : IsDominant φ.toImage := Scheme.instIsDominantToImageOfQuasiCompact φ
  have hdeg : residueFieldDegree u Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι u (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sT φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

/-- The image of a proper curve not contracted by `u` is a proper curve. -/
private theorem isProperCurve_of_not_isContractedBy (u : V ⟶ T) (hu : u ≫ sT = sV)
    (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : IsProperCurve sT (u Γ.point) := by
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hpt := not_exists_range_eq_singleton u Γ h
  have hcurve := isCurve_imageι_comp sT φ hpt
  have hker := Γ.ker_comp u
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (u Γ.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (u Γ.point) ≫ sT) := by
    have h1 : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    change IsProper (φ.ker.subschemeι ≫ sT) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

end Curves

/-- **Projection formula** for a pull-back `G = q^*N` of an `ℝ`-Cartier divisor: on a proper
curve `C' ⊆ W` whose image is the proper curve `C`, `G · C' = [k(C') : k(C)] (N · C)`, for all
presentations of `G` and `N`. -/
private theorem isRIntersectionNumber_pullback_eq_mul {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) (hq : q ≫ sY = sW) {N : RDivisor Y} {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (C : ProperCurve sY)
    (hC : C.point = q C'.point) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x' : ℝ}
    (hx' : IsRIntersectionNumber k sW G r L C' x') {m' : ℕ} {r' : Fin m' → ℝ}
    {L' : Fin m' → Divisor Y} {x : ℝ} (hx : IsRIntersectionNumber k sY N r' L' C x) :
    x' = residueFieldDegree q C'.point * x := by
  subst hq
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, hNpres, hpb, rfl⟩ := hG
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => isCartier_of_isPullback (hL₀ j) (hpb j)
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sY) C' r₀ L₁ hL₁
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sY) C').1 _ _ _ _ _ _ _ hx' hx0]
  have hy0 := isRIntersectionNumber_sum_degreeOn k sY C r₀ L₀ hL₀
  rw [← hNpres] at hy0
  rw [(IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx hy0]
  have hdeg : ∀ j, ((L₁ j).degreeOn k (q ≫ sY) C'.ι C'.dim_le (hL₁ j) : ℝ) =
      (residueFieldDegree q C'.point : ℝ) * (L₀ j).degreeOn k sY C.ι C.dim_le (hL₀ j) :=
    fun j => by
      rw [degreeOn_eq_mul_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' C hC]
      push_cast
      ring
  simp only [hdeg, mul_left_comm (r₀ _), ← Finset.mul_sum]

/-- A pull-back `G = q^*N` of an `ℝ`-Cartier divisor has intersection number `0` with a proper
curve `C' ⊆ W` whose image is not a proper curve. -/
private theorem isRIntersectionNumber_pullback_eq_zero {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) (hq : q ≫ sY = sW) {N : RDivisor Y} {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (hnc : ¬ IsProperCurve sY (q C'.point))
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x' : ℝ}
    (hx' : IsRIntersectionNumber k sW G r L C' x') : x' = 0 := by
  subst hq
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, -, hpb, rfl⟩ := hG
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => isCartier_of_isPullback (hL₀ j) (hpb j)
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sY) C' r₀ L₁ hL₁
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sY) C').1 _ _ _ _ _ _ _ hx' hx0]
  simp [fun j => degreeOn_eq_zero_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' hnc]

/-- A curve contracted by `p` is contracted by `p ≫ f`. -/
private theorem isContractedBy_comp {k : Type u} [Field k] {W X Z : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} {p : W ⟶ X} (f : X ⟶ Z) {C : ProperCurve sW}
    (hC : C.IsContractedBy p) : C.IsContractedBy (p ≫ f) :=
  fun z hz => by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC z hz]

/-- A `(p ≫ f)`-nef divisor is `p`-nef. -/
private theorem isRelativelyNef_of_comp {k : Type u} [Field k] {W X Z : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {p : W ⟶ X} (f : X ⟶ Z) {D : RDivisor W}
    (hD : IsRelativelyNef k sW (p ≫ f) D) : IsRelativelyNef k sW p D :=
  let ⟨m, r, L, hL, hpres, hall⟩ := hD
  ⟨m, r, L, hL, hpres, fun C hC => hall C (isContractedBy_comp f hC)⟩

/-- **Pull-backs of relatively nef divisors.** Let `q : W ⟶ Y` be proper and `N` a `g`-nef
`ℝ`-Cartier divisor on `Y`. Then `q^*N` is `(q ≫ g)`-nef: on a proper curve `C' ⊆ W` contracted
by `q ≫ g`, the projection formula gives `q^*N · C' = [k(C') : k(q C')] (N · q C')` when `q(C')`
is a curve, which is contracted by `g`, and `q^*N · C' = 0` when `q(C')` is a point. -/
private theorem isRelativelyNef_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (g : Y ⟶ Z) {N : RDivisor Y}
    (hN : IsRelativelyNef k sY g N) {G : RDivisor W} (hG : IsRCartierPullback q N G) :
    IsRelativelyNef k sW (q ≫ g) G := by
  obtain ⟨m, r, L, hL, hpres⟩ := isCartierCombination_of_isRCartierPullback hG
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C' hC' x hx => ?_⟩
  by_cases hc : IsProperCurve sY (q C'.point)
  · let C : ProperCurve sY := ⟨_, hc⟩
    obtain ⟨m', r', L', hL', hNpres, hall⟩ := hN
    have hy := isRIntersectionNumber_sum_degreeOn k sY C r' L' hL'
    rw [← hNpres] at hy
    rw [isRIntersectionNumber_pullback_eq_mul q hq hG C' C rfl hx hy]
    exact mul_nonneg (Nat.cast_nonneg _)
      (hall C (isContractedBy_of_isContractedBy_comp q g C' C rfl hC') _ hy)
  · exact (isRIntersectionNumber_pullback_eq_zero q hq hG C' hc hx).ge

/-- The generic point of a prime divisor `E` lies outside the support of every divisor in which
`E` has coefficient zero. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {D : DivisorWithCoeffs R Y}
    {E : MMP.Mori.PrimeDivisor Y} (hDE : D.coeff E = 0) : E.genericPoint ∉ D.supp := by
  intro h
  obtain ⟨E', hE', hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E hmem] at hE'
  exact hE' hDE

/-- If `L` is numerically trivial on the proper curve `C`, then
`(G - G' + L) · C = G · C - G' · C`. -/
private theorem isRIntersectionNumber_sub_add_eq {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {G G' L : RDivisor W} (hLc : IsCartierCombination L) (C : ProperCurve sW)
    (hL0 : ∀ {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW L r L' C x → x = 0)
    {m₁ : ℕ} {r₁ : Fin m₁ → ℝ} {L₁ : Fin m₁ → Divisor W} {x₁ : ℝ}
    {m₂ : ℕ} {r₂ : Fin m₂ → ℝ} {L₂ : Fin m₂ → Divisor W} {x₂ : ℝ}
    {m₃ : ℕ} {r₃ : Fin m₃ → ℝ} {L₃ : Fin m₃ → Divisor W} {x₃ : ℝ}
    (hx₁ : IsRIntersectionNumber k sW G r₁ L₁ C x₁)
    (hx₂ : IsRIntersectionNumber k sW G' r₂ L₂ C x₂)
    (hx₃ : IsRIntersectionNumber k sW (G - G' + L) r₃ L₃ C x₃) : x₃ = x₁ - x₂ := by
  obtain ⟨_, _, _, x₄, hx₄⟩ := exists_isRIntersectionNumber (k := k) hLc C
  have hlin := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hx₁ hx₂
  have hlin' := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 1 hlin hx₄
  rw [show (1 : ℝ) • ((1 : ℝ) • G + (-1 : ℝ) • G') + (1 : ℝ) • L = G - G' + L by
    module] at hlin'
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx₃ hlin', hL0 hx₄]
  ring

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D)
    (hDc : D.IsCartier) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  haveI := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

section FibreCurves

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- In a Noetherian quasi-sober space, a connected closed set `F` meeting a closed set `S`
without lying in it contains a point outside `S` specializing to a point of `S`. -/
private theorem exists_specializes_of_isConnected_of_inter_nonempty {Y : Type*}
    [TopologicalSpace Y] [NoetherianSpace Y] [QuasiSober Y] {F S : Set Y} (hF : IsClosed F)
    (hFc : _root_.IsConnected F) (hS : IsClosed S) (hmeet : (F ∩ S).Nonempty) (hsub : ¬ F ⊆ S) :
    ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
  set T := F \ S
  have hTF : closure T ⊆ F := closure_minimal Set.diff_subset hF
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

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve contracted by `f` that meets `S` without lying
in it. -/
private theorem exists_properCurve_isContractedBy {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : MMP.Mori.ProperCurve sY, C.IsContractedBy f ∧ ¬ Set.range C.ι ⊆ S ∧
      (Set.range C.ι ∩ S).Nonempty := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ :=
    exists_specializes_of_isConnected_of_inter_nonempty hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  let ι := f.fiberι x
  let sF := ι ≫ sY
  haveI : IsProper sF := by
    have h : sF = f.fiberToSpecResidueField x ≫ (X.fromSpecResidueField x ≫ sX) := by
      simp only [sF, ι, ← hf, Scheme.Hom.fiber_fac_assoc]
    rw [h]
    haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
    haveI : LocallyOfFiniteType (X.fromSpecResidueField x) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp hx
    haveI : IsFinite (X.fromSpecResidueField x ≫ sX) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
    haveI : IsProper (f.fiberToSpecResidueField x) :=
      inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
    haveI : IsProper (X.fromSpecResidueField x ≫ sX) := inferInstance
    infer_instance
  haveI : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
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
  have hCι : ¬ C'.IsContractedBy ι := fun h => by
    obtain ⟨w, hw, hne⟩ := exists_specializes_ne_of_isProperCurve hy'
    exact hne (hemb.injective (h w (specializes_iff_mem_closure.mp hw)))
  let C : MMP.Mori.ProperCurve sY := ⟨ι y', isProperCurve_of_not_isContractedBy ι rfl C' hCι⟩
  have hrange : Set.range (C'.ι ≫ ι) = closure {ι y'} := C'.range_comp ι rfl
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
    exact fun h => hy'S (h (subset_closure rfl))
  · refine ⟨p, ?_, hpS⟩
    rw [hrC, ← hp']
    exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

end FibreCurves

/-! ### A rational map is defined where a common model has a constant second projection -/

/-- **Rigidity at a point.** Let `p : W ⟶ X` be a proper dominant morphism of integral schemes
with `p_* 𝒪_W = 𝒪_X`, inducing an isomorphism of function fields, and let `q : W ⟶ Y` agree with
the rational map `φ : X ⤏ Y` through `p` at the generic point. If `q` maps the fibre `p⁻¹(y)` to
a single point `c`, then `φ` is defined at `y`: for an affine open `V ∋ c` there is an open
`U ∋ y` with `p⁻¹(U) ⊆ q⁻¹(V)`, and the map `Γ(V, 𝒪_Y) ⟶ Γ(p⁻¹ U, 𝒪_W) ≅ Γ(U, 𝒪_X)` is a
morphism `U ⟶ V` representing `φ`. -/
private theorem mem_domain_of_forall_eq {X Y W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] [IsProper p] (q : W ⟶ Y)
    (hbij : Function.Bijective (functionFieldMap p)) (hiso : ∀ U : X.Opens, IsIso (p.app U))
    (KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {y : X} {c : Y} (hc : ∀ w, p w = y → q w = c) : y ∈ φ.domain := by
  obtain ⟨V, hV, hcV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ c)
  have hK : IsClosed (p '' ((q ⁻¹ᵁ V : W.Opens) : Set W)ᶜ) :=
    p.isClosedMap _ (q ⁻¹ᵁ V).isOpen.isClosed_compl
  let U : X.Opens := ⟨_, hK.isOpen_compl⟩
  have hyU : y ∈ U := by
    rintro ⟨w, hw, rfl⟩
    exact hw (show q w ∈ V by rwa [hc w rfl])
  have hUV : p ⁻¹ᵁ U ≤ q ⁻¹ᵁ V := fun w hw => by
    by_contra h
    exact hw ⟨w, h, rfl⟩
  haveI : IsAffine V.toScheme := hV
  let h' : (p ⁻¹ᵁ U).toScheme ⟶ V.toScheme := W.homOfLE hUV ≫ (q ∣_ V)
  haveI : IsIso (p ∣_ U).appTop := by
    rw [morphismRestrict_appTop]
    have h2 : IsIso (W.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤)).op) :=
      inferInstance
    exact IsIso.comp_isIso' (hiso (U.ι ''ᵁ ⊤)) h2
  let ψV : U.toScheme ⟶ V.toScheme :=
    U.toScheme.toSpecΓ ≫ Spec.map (h'.appTop ≫ inv (p ∣_ U).appTop) ≫ V.toScheme.isoSpec.inv
  have hψ : (p ∣_ U) ≫ ψV = h' := by
    simp only [ψV]
    rw [reassoc_of% (Scheme.toSpecΓ_naturality (p ∣_ U)), ← Spec.map_comp_assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, ← reassoc_of% (Scheme.toSpecΓ_naturality h')]
    change h' ≫ V.toScheme.isoSpec.hom ≫ V.toScheme.isoSpec.inv = h'
    rw [Iso.hom_inv_id, Category.comp_id]
  have hψ' : (p ∣_ U) ≫ ψV ≫ V.ι = (p ⁻¹ᵁ U).ι ≫ q := by
    rw [← Category.assoc, hψ]
    simp only [h', Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  let g : X.PartialMap Y := ⟨U, U.isOpen.dense ⟨y, hyU⟩, ψV ≫ V.ι⟩
  refine Scheme.RationalMap.mem_domain.mpr ⟨g, hyU, ?_⟩
  have hηX : genericPoint X ∈ U := (genericPoint_specializes y).mem_open U.isOpen hyU
  have hηW : genericPoint W ∈ p ⁻¹ᵁ U := by
    change p (genericPoint W) ∈ U
    rw [map_genericPoint_of_isDominant]
    exact hηX
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
  haveI : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), KF]
  have key : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
      U.fromSpecStalkOfMem (genericPoint X) hηX =
      (p ⁻¹ᵁ U).fromSpecStalkOfMem (genericPoint W) hηW ≫ (p ∣_ U) := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk p
  change Spec.map _ ≫ U.fromSpecStalkOfMem (genericPoint X) hηX ≫ ψV ≫ V.ι = _
  rw [reassoc_of% key, hψ', ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]

/-! ### Intersection numbers on curves contracted over the source -/

/-- A pull-back `G = q^*N` has intersection number `0` with every proper curve contracted by
`q`: its image is a closed point, not a curve. -/
private theorem isRIntersectionNumber_pullback_eq_zero_of_isContractedBy {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) {N : RDivisor Y}
    {G : RDivisor W} (hG : IsRCartierPullback q N G) (C : ProperCurve sW)
    (hC : C.IsContractedBy q) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ}
    (hx : IsRIntersectionNumber k sW G r L C x) : x = 0 := by
  refine isRIntersectionNumber_pullback_eq_zero q hq hG C (fun hc => ?_) hx
  obtain ⟨w, hspec, hne⟩ := exists_specializes_ne_of_isProperCurve hc
  have hcl : IsClosed ({q C.point} : Set Y) := by
    have h1 : q '' closure ({C.point} : Set W) = {q C.point} := by
      ext z
      constructor
      · rintro ⟨w', hw', rfl⟩
        exact hC w' hw'
      · rintro rfl
        exact ⟨C.point, subset_closure rfl, rfl⟩
    rw [← h1]
    exact q.isClosedMap _ isClosed_closure
  exact hne (hspec.mem_closed hcl rfl)

/-- If `M` is `p`-nef and the `ℝ`-Cartier divisor `N` is numerically trivial on the curves
contracted by `p`, then `M - N` is `p`-nef. -/
private theorem isRelativelyNef_sub_of_eq_zero {k : Type u} [Field k] {W X : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {p : W ⟶ X} {M N : RDivisor W} (hM : IsRelativelyNef k sW p M)
    (hNc : IsCartierCombination N)
    (hN0 : ∀ C : ProperCurve sW, C.IsContractedBy p → ∀ {m : ℕ} {r : Fin m → ℝ}
      {L : Fin m → Divisor W} {x : ℝ}, IsRIntersectionNumber k sW N r L C x → x = 0) :
    IsRelativelyNef k sW p (M - N) := by
  have hMc : IsCartierCombination M := let ⟨m, r, L, hL, hD, _⟩ := hM; ⟨m, r, L, hL, hD⟩
  obtain ⟨m, r, L, hL, hpres⟩ := isCartierCombination_sub hMc hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C hC x hx => ?_⟩
  obtain ⟨mM, rM, LM, hLM, hMpres, hall⟩ := hM
  obtain ⟨_, _, _, xN, hxN⟩ := exists_isRIntersectionNumber (k := k) hNc C
  have hxM := isRIntersectionNumber_sum_degreeOn k sW C rM LM hLM
  rw [← hMpres] at hxM
  have hsum := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hxM hxN
  rw [show (1 : ℝ) • M + (-1 : ℝ) • N = M - N by module]
    at hsum
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx hsum, hN0 C hC hxN]
  have := hall C hC _ hxM
  linarith

/-- An `f`-ample `ℝ`-Cartier divisor is positive on every proper curve contracted by `f`. -/
private theorem isRIntersectionNumber_pos_of_isRelativelyAmple {k : Type u} [Field k]
    {Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {g : Y ⟶ Z} {A : RDivisor Y} (hA : IsRelativelyAmple g A)
    (C : ProperCurve sY) (hC : C.IsContractedBy g) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor Y} {x : ℝ} (hx : IsRIntersectionNumber k sY A r L C x) : 0 < x := by
  obtain ⟨m', r', L', hm, hr, hL, rfl⟩ := hA
  have hLc : ∀ j, (L' j).IsCartier := fun j => (hL j).1
  rw [(IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx
    (isRIntersectionNumber_sum_degreeOn k sY C r' L' hLc)]
  refine Finset.sum_pos (fun j _ => mul_pos (hr j) ?_) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier g (hL j) (hLc j) C hC

/-- In a Jacobson space, a point outside a closed set `T` specializes to a closed point outside
`T`. -/
private theorem exists_isClosed_singleton_notMem {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {T : Set X} (hT : IsClosed T) {x : X} (hx : x ∉ T) :
    ∃ y ∈ closure {x}, IsClosed ({y} : Set X) ∧ y ∉ T := by
  obtain ⟨y, ⟨hyx, hyT⟩, hyc⟩ := nonempty_inter_closedPoints
    (⟨x, subset_closure rfl, hx⟩ : (closure {x} ∩ Tᶜ).Nonempty)
    (isClosed_closure.isLocallyClosed.inter hT.isOpen_compl.isLocallyClosed)
  exact ⟨y, hyx, mem_closedPoints_iff.mp hyc, hyT⟩

/-- If the rational map `φ` is not defined at the closed point `y`, then the fibre `p⁻¹(y)` of a
model `(W, p, q)` of `φ` contains a proper curve contracted by `p` but not by `q`. -/
private theorem exists_properCurve_not_isContractedBy {k : Type u} [Field k]
    {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X]
    [IsIntegral W] [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    (hXn : IsNormalVariety k sX) (hWn : IsNormalVariety k sW) {φ : X.RationalMap Y}
    {p : W ⟶ X} [IsDominant p] [IsProper p] {q : W ⟶ Y} [IsProper q] (hp : p ≫ sX = sW)
    (hpb : IsBirationalMorphism p)
    (KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {y : X} (hyc : IsClosed ({y} : Set X)) (hyφ : y ∉ φ.domain) :
    ∃ C : ProperCurve sW, C.IsContractedBy p ∧ ¬ C.IsContractedBy q ∧ p C.point = y := by
  have hiso : ∀ U : X.Opens, IsIso (p.app U) :=
    (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sW sX hWn.1 hXn p
      hpb).1
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
  have hFcl : IsClosed (p.base ⁻¹' {y}) := hyc.preimage p.continuous
  haveI : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  obtain ⟨w', hw'⟩ := Surjective.surj (f := p) y
  obtain ⟨w₀, hw₀F, hw₀c⟩ := nonempty_inter_closedPoints
    (⟨w', hw'⟩ : (p.base ⁻¹' {y}).Nonempty) hFcl.isLocallyClosed
  obtain ⟨w₁, hw₁, hqw₁⟩ : ∃ w₁, p w₁ = y ∧ q w₁ ≠ q w₀ := by
    by_contra h
    push Not at h
    exact hyφ (mem_domain_of_forall_eq φ p q hpb.functionFieldMap_bijective hiso KF h)
  have hqcl : IsClosed ({q w₀} : Set Y) := by
    rw [← Set.image_singleton]
    exact q.isClosedMap _ (mem_closedPoints_iff.mp hw₀c)
  obtain ⟨C, hCp, hCS, c₀, hc₀R, hc₀S⟩ := exists_properCurve_isContractedBy hXn hWn p
    hp hpb y hyc (hFcl.inter (hqcl.preimage q.continuous)) ⟨w₀, hw₀F, hw₀F, rfl⟩
    fun h => hqw₁ (h (show w₁ ∈ p.base ⁻¹' {y} from hw₁)).2
  rw [C.range_ι] at hCS hc₀R
  have hpC : p C.point = y := (hCp c₀ hc₀R).symm.trans hc₀S.1
  exact ⟨C, hCp, fun hq' => hCS fun z hz =>
    ⟨(hCp z hz).trans hpC, (hq' z hz).trans ((hq' c₀ hc₀R).symm.trans hc₀S.2)⟩, hpC⟩

/-- On a common model `(W, p, q)`, let `Δ = p^*N_X - q^*N_Y + L₁` be effective with `L₁ ~ 0`,
`N_Y` relatively ample over `Z` and `q^*N_Y - L₁` `p`-nef. If `φ` is not defined at `p(η_P)`,
then `Δ` has nonzero coefficient along `P`. -/
private theorem coeff_ne_zero_of_notMem_domain {k : Type u} [Field k] {X Y Z W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsSeparated sX] [QuasiCompact sX] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] [IsSeparated sY] [QuasiCompact sY] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] [QuasiCompact sW]
    (hXn : IsNormalVariety k sX) (hWn : IsNormalVariety k sW) {φ : X.RationalMap Y}
    {p : W ⟶ X} [IsDominant p] [IsProper p] {q : W ⟶ Y} [IsProper q] (hp : p ≫ sX = sW)
    (hq : q ≫ sY = sW) (hpb : IsBirationalMorphism p)
    (KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {f : X ⟶ Z} {g : Y ⟶ Z} (hcomm : p ≫ f = q ≫ g) {N_X : RDivisor X} {N_Y : RDivisor Y}
    (hNY : IsCartierCombination N_Y) (hamp : IsRelativelyAmple g N_Y) {G_X G_Y : RDivisor W}
    (hGX : IsRCartierPullback p N_X G_X) (hGY : IsRCartierPullback q N_Y G_Y) {L₁ : Divisor W}
    (hL₁c : L₁.IsCartier) (hL₁ : L₁.LinearlyEquivalent 0)
    (hL₁r : IsCartierCombination (Divisor.toRDivisor L₁))
    (hΔc : IsCartierCombination (G_X - G_Y + Divisor.toRDivisor L₁))
    (hΔ : (G_X - G_Y + Divisor.toRDivisor L₁).IsEffective)
    (hMnef : IsRelativelyNef k sW p (G_Y - Divisor.toRDivisor L₁)) {P₀ : Mori.PrimeDivisor W}
    (hx : p P₀.genericPoint ∉ φ.domain) : (G_X - G_Y + Divisor.toRDivisor L₁).coeff P₀ ≠ 0 := by
  intro hc0
  have hnegnef : IsRelativelyNef k sW p (-(G_X - G_Y + Divisor.toRDivisor L₁)) := by
    rw [show -(G_X - G_Y + Divisor.toRDivisor L₁) = (G_Y - Divisor.toRDivisor L₁) - G_X by abel]
    exact isRelativelyNef_sub_of_eq_zero hMnef (isCartierCombination_of_isRCartierPullback hGX)
      fun C hC _ _ _ _ hx' =>
        isRIntersectionNumber_pullback_eq_zero_of_isContractedBy p hp hGX C hC hx'
  have hdisj : Disjoint (p.base ⁻¹' {p P₀.genericPoint})
      ((G_X - G_Y + Divisor.toRDivisor L₁).supp : Set W) :=
    (preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg k sX sW hXn hWn p
      hp hpb hΔc hΔ hnegnef (p P₀.genericPoint)).resolve_left
      fun hsub => genericPoint_notMem_supp_of_coeff_eq_zero hc0 (hsub rfl)
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  obtain ⟨y, hyT, hyc, hyS⟩ := exists_isClosed_singleton_notMem
    (p.isClosedMap _ (G_X - G_Y + Divisor.toRDivisor L₁).supp.isClosed)
    (x := p P₀.genericPoint) fun ⟨w, hw, hwx⟩ =>
      Set.disjoint_left.mp hdisj (show p w ∈ ({p P₀.genericPoint} : Set X) from hwx) hw
  obtain ⟨C, hCp, hCq, hpC⟩ := exists_properCurve_not_isContractedBy hXn hWn hp hpb KF hyc
    fun hy => hx ((specializes_iff_mem_closure.mpr hyT).mem_open φ.domain.2 hy)
  have hCpg : C.IsContractedBy (q ≫ g) := hcomm ▸ isContractedBy_comp f hCp
  let C' : ProperCurve sY := ⟨q C.point, isProperCurve_of_not_isContractedBy q hq C hCq⟩
  obtain ⟨_, _, _, x₁, hx₁⟩ :=
    exists_isRIntersectionNumber (k := k) (isCartierCombination_of_isRCartierPullback hGX) C
  obtain ⟨_, _, _, x₂, hx₂⟩ :=
    exists_isRIntersectionNumber (k := k) (isCartierCombination_of_isRCartierPullback hGY) C
  obtain ⟨_, _, _, x₃, hx₃⟩ := exists_isRIntersectionNumber (k := k) hΔc C
  obtain ⟨_, _, _, y₂, hy₂⟩ := exists_isRIntersectionNumber (k := k) hNY C'
  have e₁ : x₁ = 0 := isRIntersectionNumber_pullback_eq_zero_of_isContractedBy p hp hGX C hCp hx₁
  have e₂ : x₂ = residueFieldDegree q C.point * y₂ :=
    isRIntersectionNumber_pullback_eq_mul q hq hGY C C' rfl hx₂ hy₂
  have hy₂pos : 0 < y₂ :=
    isRIntersectionNumber_pos_of_isRelativelyAmple hamp C'
      (isContractedBy_of_isContractedBy_comp q g C C' rfl hCpg) hy₂
  have hdeg : (0 : ℝ) < residueFieldDegree q C.point :=
    Nat.cast_pos.mpr (residueFieldDegree_pos_of_not_isContractedBy q hq C hCq)
  have e₃ : x₃ = x₁ - x₂ := isRIntersectionNumber_sub_add_eq hL₁r C
    (fun hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₁c hL₁ C hx) hx₁ hx₂ hx₃
  have h₃ : 0 ≤ x₃ := IsRIntersectionNumber.nonneg_of_isEffective k sW hWn _ hΔc hΔ C
    (fun hC => hyS ⟨C.point, hC, hpC⟩) _ _ hx₃
  nlinarith [mul_pos hdeg hy₂pos]

/-- **FA 2.23.3, strict form, on a common model.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a log canonical
model of `f : (X, D_X) ⟶ Z`, `(W, p, q)` a common model of `φ` and `P` a prime divisor of `W`
such that `φ` is not defined at `p(η_P)`. Then `a(ord_P, D_{𝓕,Y}) > a(ord_P, D_X)`.

On `W`, `Δ = p^*(K_X + D_X) - q^*(K_Y + D_{𝓕,Y}) + (div_W(q^*ω_Y) - div_W(p^*ω_X))` is effective,
`-Δ` is `p`-nef, and its coefficient along `P` is the difference of the discrepancies. If that
coefficient vanished, the fibre `p⁻¹(p(η_P))` would miss `Supp Δ` (negativity lemma over a point),
and so would `p⁻¹(y)` for a closed point `y` of `closure {p(η_P)}` outside `p(Supp Δ)`. As `φ` is
not defined at `y`, `q` is not constant on `p⁻¹(y)`, which therefore contains a proper curve `C`
not contracted by `q`. Then `Δ · C ≥ 0` as `C ⊄ Supp Δ`, while
`Δ · C = -q^*(K_Y + D_{𝓕,Y}) · C < 0` by the projection formula and relative ampleness. -/
private theorem isDiscrepancy_lt_of_isCommonModel {k : Type u}
    [Field k] [PerfectField k] {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q)
    (P₀ : Mori.PrimeDivisor W) (hx : p P₀.genericPoint ∉ φ.domain) :
    let EX : ProperDivisorOver k sX :=
      { Y := W, f := p, isNormalVariety := hW.comp_p ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_p, E := P₀, isProper := hW.isProper_p }
    let EY : ProperDivisorOver k sY :=
      { Y := W, f := q, isNormalVariety := hW.comp_q ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_q, E := P₀, isProper := hW.isProper_q }
    ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G EY.valuation a →
      IsDiscrepancy sX n K_X D_X EX.valuation a' → a' < a := by
  intro EX EY a a' ha ha'
  obtain ⟨-, -, -, ⟨hXn, hYn, -⟩, -, ⟨-, -, hAY⟩, -⟩ := id hM.1
  obtain ⟨-, -, hamp⟩ := hM.2
  have hWn := hW.isNormalVariety
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sW := hWn.1.toQuasiCompact
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hpb := hW.isBirationalMorphism_p
  have hqb := hW.isBirationalMorphism_q
  haveI := hW.isProper_p
  haveI := hW.isProper_q
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  haveI := hYn.1.toQuasiCompact
  haveI := hW.isVariety_Z.toIsSeparated
  haveI : Z.IsSeparated := ⟨isSeparated_toTerminal sZ⟩
  have hWp : IsNormalVariety k (p ≫ sX) := hW.comp_p ▸ hWn
  have hWq : IsNormalVariety k (q ≫ sY) := hW.comp_q ▸ hWn
  have KF := specMap_fromFunctionField_eq_of_comp_eq φ p q hW.comp_eq
  have hcomm : p ≫ f = q ≫ g :=
    comp_eq_comp_of_specMap_fromFunctionField_eq hW.isModificationOf.2 p q KF
  obtain ⟨hKXc, hBXc, -, _EX, ωX, _mX, _rX, _LX, -, hωXK, hwX⟩ := id ha'
  obtain ⟨hKYc, hBYc, -, _EY, ωY, _mY, _rY, _LY, -, hωYK, hwY⟩ := id ha
  subst hωXK hωYK
  have hn : topologicalKrullDim X = n := hKXc.topologicalKrullDim_eq
  have htrX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have htrY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY)
    hKYc.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = n := by
    rw [← toENat_trdeg_functionField (sX := p ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX p hpb.functionFieldMap_bijective,
      toENat_trdeg_functionField (sX := sX), hn]
  have hpω := pullbackRationalPluriForms_ne_zero p hpb.functionFieldMap_bijective htrX hwX.2.2.1
  have hqω := pullbackRationalPluriForms_ne_zero q hqb.functionFieldMap_bijective htrY hwY.2.2.1
  obtain ⟨L₁, hL₁_def⟩ : ∃ L₁ : Divisor W,
      L₁ = divisorOfForm (pullbackRationalPluriForms sY q ωY) -
        divisorOfForm (pullbackRationalPluriForms sX p ωX) := ⟨_, rfl⟩
  have hL₁ : L₁.LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm_of_eq
      (hW.comp_q.trans hW.comp_p.symm) hWp hnW hqω hpω
    exact ⟨φ, by rwa [sub_zero, hL₁_def]⟩
  have hL₁c : L₁.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hL₁ Divisor.isCartier_zero
  obtain ⟨G_X, hGX, -⟩ := existsUnique_isRCartierPullback p hBXc
  obtain ⟨G_Y, hGY, -⟩ := existsUnique_isRCartierPullback q hBYc
  set dX := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX))
  set dY := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sY q ωY))
  have haX : ∀ P, IsDiscrepancy sX n (divisorOfForm ωX) D_X
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance).valuation
      (dX.coeff P - G_X.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hXn ωX hwX.2.2.1 hKXc hBXc p hWp hpb hGX P
  have haY : ∀ P, IsDiscrepancy sY n (divisorOfForm ωY) G
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance).valuation
      (dY.coeff P - G_Y.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hYn ωY hwY.2.2.1 hKYc hBYc q hWq hqb hGY P
  have hcoeff : ∀ P, (G_X - G_Y + Divisor.toRDivisor L₁).coeff P =
      (dY.coeff P - G_Y.coeff P) - (dX.coeff P - G_X.coeff P) := by
    intro P
    rw [hL₁_def, map_sub]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  have hL₁r : IsCartierCombination (Divisor.toRDivisor L₁) :=
    ⟨1, fun _ => 1, fun _ => L₁, fun _ => hL₁c, by simp [← toRDivisor_eq_mapCoeffs]⟩
  have hYnef : IsRelativelyNef k sW (p ≫ f) G_Y := by
    rw [hcomm]
    exact isRelativelyNef_of_isRCartierPullback q hW.comp_q g hAY hGY
  have hMnef : IsRelativelyNef k sW p (G_Y - Divisor.toRDivisor L₁) :=
    isRelativelyNef_sub_of_eq_zero (isRelativelyNef_of_comp f hYnef) hL₁r
      fun C _ _ _ _ _ hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₁c hL₁ C hx
  have hBG : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sX p P →
      0 ≤ (G_X - G_Y + Divisor.toRDivisor L₁).coeff P := by
    intro P hP
    rw [hcoeff P, sub_nonneg]
    exact hM.1.isDiscrepancy_le_of_not_isExceptional hW P
      (fun h => hP ⟨hWp, hpb, inferInstance, h⟩) _ _ (haY P) (haX P)
  have hMc := isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hGY) hL₁r
  have hBc := isCartierCombination_add (isCartierCombination_sub
    (isCartierCombination_of_isRCartierPullback hGX)
    (isCartierCombination_of_isRCartierPullback hGY)) hL₁r
  have hnum : IsNumericallyEquivalentOver k sW p G_X
      ((G_Y - Divisor.toRDivisor L₁) + (G_X - G_Y + Divisor.toRDivisor L₁)) := by
    rw [sub_add_add_cancel, add_sub_cancel]
    exact isNumericallyEquivalentOver_self (isCartierCombination_of_isRCartierPullback hGX)
  have hΔeff := isEffective_of_isNumericallyEquivalentOver_pullback k sX sW hXn hWn p hW.comp_p
    hpb hBXc hGX hMc hMnef hBc hBG hnum
  have haP : a = dY.coeff P₀ - G_Y.coeff P₀ := ha.eq (haY P₀)
  have ha'P : a' = dX.coeff P₀ - G_X.coeff P₀ := ha'.eq (haX P₀)
  have hle : a' ≤ a := by
    have h0 := hΔeff P₀
    rw [hcoeff P₀] at h0
    linarith
  refine lt_of_le_of_ne hle fun heq => coeff_ne_zero_of_notMem_domain hXn hWn hW.comp_p hW.comp_q
    hpb KF hcomm hBYc hamp hGX hGY hL₁c hL₁ hL₁r hBc hΔeff hMnef hx ?_
  rw [hcoeff P₀]
  linarith

/-- **FA 2.23.3, strict inequality.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a log canonical model of
`f : (X, D_X) ⟶ Z` with respect to `𝓕` (`MMP.Flips.IsLogCanonicalModelOf`, with
`G = D_{𝓕,Y}`), through the modification `φ : X ⤏ Y`, over a field of characteristic zero. Let
`B` be a divisor of `k(X) = k(Y)` with nonempty center on `X`: a valuation `v` of `k(X)` and a
valuation `v'` of `k(Y)` induced by one valuation `w` of `k(W)` on a common model `(W, p, q)`
of `φ`. Let `(V, h, E)` be a divisor over `X` with `ord_E = v`, so that `h(η_E)` is the generic
point of `Center_X(B)`, and suppose `φ` is not defined at `h(η_E)`. Then
`a(B, D_{𝓕,Y}) > a(B, D_X)`. -/
@[mmp "thm_fa2_lc_model_discrepancy_strict"]
public theorem IsLogCanonicalModelOf.isDiscrepancy_lt {k : Type u} [Field k] [CharZero k]
    {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY] [QuasiCompact sY] {n : ℕ}
    {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X} {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q)
    {v : Valuation X.functionField ℤᵐ⁰} (hv : HasNonemptyCenter k sX v)
    (D : ProperDivisorOver k sX) (hD : D.valuation = v)
    (hx : D.f D.E.genericPoint ∉ φ.domain)
    {v' : Valuation Y.functionField ℤᵐ⁰} :
    haveI : IsIntegral W := hW.isNormalVariety.1.toIsIntegral
    haveI : IsDominant p := hW.isBirationalMorphism_p.isDominant
    haveI : IsDominant q := hW.isBirationalMorphism_q.isDominant
    ∀ w : Valuation W.functionField ℤᵐ⁰, w.comap (functionFieldMap p) = v →
      w.comap (functionFieldMap q) = v' →
        ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G v' a → IsDiscrepancy sX n K_X D_X v a' → a' < a := by
  have hWn := hW.isNormalVariety
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have hpb := hW.isBirationalMorphism_p
  haveI := hW.isProper_p
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hW.isBirationalMorphism_q.isDominant
  intro w hwp hwq
  subst hD
  obtain ⟨D₁, hD₁, -⟩ := ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq
    hW.isVariety_X p (hW.comp_p ▸ hWn.1) hpb D
  have hw : D₁.valuation = w := valuation_eq_of_comap_eq hpb (hD₁.trans hwp.symm)
  haveI := D₁.isIntegral
  haveI := D₁.isNormal
  haveI := D₁.isLocallyNoetherian
  haveI := D₁.isDominant
  haveI := D₁.isProper
  have hW'n : IsNormalVariety k (D₁.f ≫ sW) := by
    rw [← hW.comp_p]
    exact D₁.isNormalVariety
  have hW' := isCommonModel_comp hW D₁.f D₁.isBirationalMorphism hW'n
  have hEX : (D₁.E.valuationOver (D₁.f ≫ p)) = D.valuation := by
    rwa [← comap_valuationOver]
  have hEY : (D₁.E.valuationOver (D₁.f ≫ q)) = v' := by
    rw [← comap_valuationOver, ← hwq]
    exact congrArg (fun u => u.comap (functionFieldMap q)) hw
  let EX : ProperDivisorOver k sX :=
    { Y := D₁.Y, f := D₁.f ≫ p, isNormalVariety := hW'.comp_p ▸ hW'.isNormalVariety,
      isBirationalMorphism := hW'.isBirationalMorphism_p, E := D₁.E,
      isProper := hW'.isProper_p }
  have hpt : (D₁.f ≫ p) D₁.E.genericPoint = D.f D.E.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hW.isVariety_X
      (D := EX.toDivisorOver) (D' := D.toDivisorOver) hEX
  intro a a' ha ha'
  exact isDiscrepancy_lt_of_isCommonModel hM hW' D₁.E (by rwa [hpt]) a a'
    (by rwa [← hEY] at ha) (by rwa [← hEX] at ha')

end MMP.Flips
