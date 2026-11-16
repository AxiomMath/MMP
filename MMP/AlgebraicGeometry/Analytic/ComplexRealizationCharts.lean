module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.Analytic.ComplexRealization
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Positivity.VeryAmpleAffineBase
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap
import MMP.AlgebraicGeometry.Analytic.BorelMoore
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle

/-!
# Graph divisors, persistent labels, the default weight, and complex realizations

This file collects four groups of results used in the termination argument for fourfold flips
and in the comparison of algebraic and analytic topology.

**Graph divisors.** Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` (by `f^±`) be a threefold step diagram with
normalized graph `(G, u, v)` and graph divisor `H = u^* D⁻ - v^* D⁺` on `G`, where
`D^± = K_{X^±} + B^±`. Every prime divisor `P` of `X⁺` has its valuation centred on a prime
divisor `P⁻` of `X⁻`, with both `f^±` isomorphisms over the generic point of `f⁺(P)`; so `u` and
`v` induce isomorphisms of local rings at every prime divisor `E` of `G` over `P`, and the
coefficients of `E` in `u^* D⁻` and `v^* D⁺` agree, since `D⁺` is the strict transform of `D⁻`.
Hence `v_* H = 0`, and when `f⁻` is small the same argument gives `u_* H = 0`.

**Labels along a terminal chain.** Along a terminal chain `(p_i, Θ_i)_{i ≥ 0}` over a stabilized
tail, every flip of a bridge has small contraction, so its strict transform is a bijection of
prime divisors preserving valuations and boundary coefficients. Composing these along the moves
gives, for every model `M` of the chain, a bijection from the prime divisors of `Y_0` onto those
of `M`, pinned by equality of valuations; and the centre of `s ∈ I_∞` on `Y_i` is the
exceptional divisor `E_{i,s}` of the `i`-th junction.

**The default weight.** For `b ∈ [0, 1)` the default `d(b) = ∑_{j ≥ 1} w(1 - j(1 - b))` is the
finite sum over `1 ≤ j < ⌈1 / (1 - b)⌉`, since `1 - j(1 - b) ≤ 0` beyond; `d(0) = 0`, and `d` is
monotone on `[0, 1)`.

**Complex realizations.** For an affine chart `U` of a scheme over `ℂ`, `U(ℂ)` is open in `X^an`
and the coordinate map identifies it with the zero locus of the relations. The realization of a
closed immersion is a closed embedding, the realization of a fibre product is the topological
fibre product, and the realization of a morphism admitting a closed immersion into `ℙᴺ_S` over
`S` has compact inverse images of compact sets.

## Main results

* `MMP.Fourfold.IsThreefoldGraphDivisor.transformDivisor_eq_zero`: `v_* H = 0`, and `u_* H = 0`
  when `f⁻` is small.
* `MMP.Fourfold.StabilizedTail.TerminalChain.exists_equiv_primeDivisor`: prime divisors and
  labels persist along a terminal chain.
* `MMP.Fourfold.defaultWeight_finite`, `MMP.Fourfold.monotoneOn_defaultWeight`.
* `MMP.Analytic.Chart.isOpen_chart_and_isEmbedding_coords`: affine charts of `X^an`.
* `MMP.Analytic.ComplexPoints.isClosedEmbedding_realize`: closed immersions realize as closed
  embeddings.
* `MMP.Analytic.ComplexPoints.isEmbedding_realize_pullback`: `(X ×_S Y)^an ≃ₜ X^an ×_{S^an} Y^an`.
* `MMP.Analytic.ComplexPoints.isCompact_preimage_realize_of_exists_isClosedImmersion`: projective
  morphisms realize with compact inverse images of compact sets.

## Implementation notes

The push-forward of a `ℚ`-divisor along the birational morphism `v : G ⟶ X⁺` is its birational
transform `MMP.Mori.RationalMap.transformDivisor` under `v` regarded as a rational map; for a
proper birational morphism this is the push-forward of cycles.

In `exists_equiv_primeDivisor`, the valuation `ord_P` of a prime divisor `P` of `Y_0` is regarded
as a valuation of `k(X_0)` through `p_0` and carried to `k(X_i)` by
`MMP.Fourfold.StabilizedTail.IsTransportedValuationFrom`; for the model `V_k` of the `i`-th
bridge it is compared in `k(Z_i)` through `π_k : V_k ⟶ Z_i`. The models of a bridge are taken
for all `k ≤ m_i`, including the end `V_{m_i} ≅ Y_{i+1}`.

The complex realization `X^an` is homeomorphic to the underlying space `X(ℂ)` with the classical
topology (`MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace`), compatibly with induced maps;
the results on closed immersions, fibre products and proper maps are transported from there. The
homeomorphism onto the topological fibre product is stated as an embedding into `X^an × Y^an`
together with the description of its range.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
* [Serre, *Géométrie algébrique et géométrie analytique*]
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

/-! ### The graph divisor pushes forward to zero -/

namespace MMP.Fourfold

section GraphDivisor

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The coefficient of `P` in the linear extension of a partial map `φ` on prime divisors
vanishes when `D` has coefficient `0` at every prime divisor sent to `P`. -/
private theorem mapPrimeDivisors_apply_eq_zero {X Y : Scheme.{u}} {R : Type*} [AddCommMonoid R]
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {P : MMP.Mori.PrimeDivisor Y} (D : DivisorWithCoeffs R X)
    (h : ∀ E, φ E = some P → D E = 0) :
    DivisorWithCoeffs.mapPrimeDivisors φ D P = 0 := by
  classical
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun E _ => ?_
  rcases hφ : φ E with _ | Q
  · simp [hφ]
  · by_cases hQ : Q = P
    · subst hQ
      simp [hφ, h E hφ]
    · simp [hφ, Finsupp.single_apply, hQ]

private theorem genericPoint_mem_support {X : Scheme.{u}} (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∈ (P.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- If `f(P) = Q` for prime divisors `P`, `Q`, then `f(η_P) = η_Q`. -/
private theorem map_genericPoint_eq_of_image_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (h : f '' (P.support : Set X) = Q.support) : f P.genericPoint = Q.genericPoint := by
  have hQ := genericPoint_mem_support Q
  have h1 : f P.genericPoint ∈ (Q.support : Set Y) := h ▸ ⟨_, genericPoint_mem_support P, rfl⟩
  rw [← h] at hQ
  obtain ⟨x, hx, hxQ⟩ := hQ
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hx h1
  have h2 : f P.genericPoint ⤳ Q.genericPoint := hxQ ▸ hx.map f.continuous
  exact (h2.antisymm h1).eq

/-- A birational morphism induces an isomorphism of local rings at a point over the generic point
of a prime divisor. -/
private theorem isIso_stalkMap_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (P : MMP.Mori.PrimeDivisor Y) {x : X}
    (hx : f x = P.genericPoint) : IsIso (f.stalkMap x) := by
  have := P.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (f x)) := by
    rw [hx]
    infer_instance
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x

/-- Two points of `X` over the generic point of a prime divisor `Q` of the normal scheme `Y` are
equal, for `f : X ⟶ Y` separated, dominant and birational. -/
private theorem eq_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f] [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (Q : MMP.Mori.PrimeDivisor Y) {x₁ x₂ : X}
    (h₁ : f x₁ = Q.genericPoint) (h₂ : f x₂ = Q.genericPoint) : x₁ = x₂ := by
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (f x₁)) := by
    rw [h₁]
    infer_instance
  haveI := isIso_stalkMap_of_map_eq_genericPoint f hf Q h₁
  haveI := isIso_stalkMap_of_map_eq_genericPoint f hf Q h₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf (h₂.trans h₁.symm)

/-- **The inverse transform over the biregular locus.** If `f(η_P) = η_Q` lies in the biregular
locus of `f`, then `f⁻¹_* Q = P`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus {X Y : Scheme.{u}}
    {f : X ⟶ Y} (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (he : f P.genericPoint = Q.genericPoint) (hQ : Q.genericPoint ∈ biregularLocus f) :
    inverseTransformPrimeDivisor f Q = some P := by
  have hQmem := genericPoint_mem_support Q
  rw [inverseTransformPrimeDivisor_eq_some_iff]
  refine ⟨⟨Q.genericPoint, hQmem, hQ⟩, ?_⟩
  have := P.integral
  rw [inverseTransformIdeal]
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  ext1
  change (P.support : Set X) = closure (f ⁻¹' ((Q.support : Set Y) ∩ biregularLocus f))
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine le_antisymm (closure_mono ?_) (closure_minimal ?_ isClosed_closure)
  · rintro _ rfl
    exact ⟨he ▸ hQmem, he ▸ hQ⟩
  · rintro x ⟨hxQ, hxV⟩
    have hPV : f P.genericPoint ∈ V := he ▸ hQ
    let x' : (f ⁻¹ᵁ V).toScheme := ⟨x, hxV⟩
    let p' : (f ⁻¹ᵁ V).toScheme := ⟨P.genericPoint, hPV⟩
    have hι : ∀ z : (f ⁻¹ᵁ V).toScheme, V.ι ((f ∣_ V) z) = f z.1 := fun z => by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
      rfl
    have h1 : V.ι ((f ∣_ V) p') ⤳ V.ι ((f ∣_ V) x') := by
      rw [hι, hι]
      change f P.genericPoint ⤳ f x
      rw [he, specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hxQ
    rw [V.ι.isOpenEmbedding.isInducing.specializes_iff,
      (f ∣_ V).isOpenEmbedding.isInducing.specializes_iff] at h1
    rw [← specializes_iff_mem_closure]
    exact h1.map (f ⁻¹ᵁ V).ι.continuous

/-- Only `Q` has inverse transform `P`, when `f(η_P) = η_Q`. -/
private theorem eq_of_inverseTransformPrimeDivisor_eq_some {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : MMP.Mori.PrimeDivisor X) (Q Q' : MMP.Mori.PrimeDivisor Y)
    (he : f P.genericPoint = Q.genericPoint) (h : inverseTransformPrimeDivisor f Q' = some P) :
    Q' = Q := by
  have hs := support_inverseTransformPrimeDivisor h
  have hP := genericPoint_mem_support P
  rw [hs] at hP
  have hcl : IsClosed (f ⁻¹' (Q'.support : Set Y)) :=
    (Q'.idealSheaf.support.isClosed).preimage f.continuous
  have hsub : (inverseTransform f Q'.idealSheaf.support : Set X) ⊆ f ⁻¹' (Q'.support : Set Y) :=
    closure_minimal (fun z hz => hz.1) hcl
  have hQ' : Q.genericPoint ∈ (Q'.support : Set Y) := he ▸ hsub hP
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (Q'.eq_genericPoint_of_mem_support hQ' Q.coheight_genericPoint).symm

/-- **Coefficients of the strict transform.** If `f(η_{P⁻}) = f⁺(η_P) = η_Q` with `f⁺` an
isomorphism over `η_Q`, the coefficient of `P` in `(f⁺)⁻¹_* f_* D` is that of `P⁻` in `D`. -/
private theorem flipTransform_apply_eq {Xm Xp Z : Scheme.{u}} [IsIntegral Xm] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsSeparated fm]
    [IsDominant fm] (hfm : Function.Bijective (functionFieldMap fm))
    (Pm : MMP.Mori.PrimeDivisor Xm) (P : MMP.Mori.PrimeDivisor Xp) (Q : MMP.Mori.PrimeDivisor Z)
    (hm : fm Pm.genericPoint = Q.genericPoint) (hp : fp P.genericPoint = Q.genericPoint)
    (hQ : Q.genericPoint ∈ biregularLocus fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Xm) : flipTransform fm fp D P = D Pm := by
  change inverseTransformDivisor fp (RationalMap.transformDivisor (X := Xm) fm.toRationalMap D) P
    = D Pm
  rw [inverseTransformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus P Q hp hQ)
      (fun Q' hQ' => eq_of_inverseTransformPrimeDivisor_eq_some P Q Q' hp hQ'),
    RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm Q).mpr hm)]
  intro Pm' h'
  have h'' := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm' Q).mp h'
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_map_eq_genericPoint fm hfm Q h'' hm)

/-- Let `E ⊆ X` and `P ⊆ Y` be prime divisors with `f(η_E) = η_P` and `𝒪_{Y,P} ≅ 𝒪_{X,E}`. If `B'`
is the pull-back of a `ℚ`-Cartier `ℚ`-divisor `B` on `Y`, the coefficient of `E` in `B'` is the
coefficient of `P` in `B`. -/
private theorem coeff_eq_of_isPullback_qDivisor {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] {B : QDivisor Y} (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} (hB' : B.IsPullback f hB B') : B' E = B P := by
  have hm := QDivisor.cartierIndex_pos hBq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hBq
  obtain ⟨D', hD', hp⟩ := hB' _ hm D₀ hD₀ hD₀c
  have hc := MMP.Positivity.coeff_eq_of_isPullback E P heq hD₀c hp
  have h1 := congrArg (fun G : QDivisor X => G E) hD'
  have h2 := congrArg (fun G : QDivisor Y => G P) hD₀
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1 h2
  have hm' : (B.cartierIndex hBq : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine mul_left_cancel₀ hm' (h1.symm.trans (Eq.trans ?_ h2))
  exact congrArg (fun z : ℤ => (z : ℚ)) hc

/-- **The graph divisor vanishes over a common prime divisor.** If a prime divisor `E` of `G` lies
over prime divisors `P⁻` of `X⁻` and `P` of `X⁺`, both over the prime divisor `Q` of `Z`, and `f⁺`
is an isomorphism over `η_Q`, then the coefficient of `E` in the graph divisor `H` is `0`. -/
private theorem IsThreefoldGraphDivisor.apply_eq_zero
    {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsLocallyNoetherian G] [IsNormal G] [IsIntegral G]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsSeparated (Z ↘ Limits.terminal Scheme)]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    [IsSeparated fm] [IsDominant fm] [IsDominant u] [IsDominant v]
    {H : QDivisor G} (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H)
    (hfm : Function.Bijective (functionFieldMap fm)) (hu : Function.Bijective (functionFieldMap u))
    (hv : Function.Bijective (functionFieldMap v)) (E : MMP.Mori.PrimeDivisor G)
    (Pm : MMP.Mori.PrimeDivisor Xm) (P : MMP.Mori.PrimeDivisor Xp) (Q : MMP.Mori.PrimeDivisor Z)
    (huE : u E.genericPoint = Pm.genericPoint) (hvE : v E.genericPoint = P.genericPoint)
    (hm : fm Pm.genericPoint = Q.genericPoint) (hp : fp P.genericPoint = Q.genericPoint)
    (hQ : Q.genericPoint ∈ biregularLocus fp) : H E = 0 := by
  have hD := h.isThreefoldStepDiagram
  haveI := isIso_stalkMap_of_map_eq_genericPoint u hu Pm huE
  haveI := isIso_stalkMap_of_map_eq_genericPoint v hv P hvE
  obtain ⟨Hm, Hp, hm', hp', hHm, hHp, rfl⟩ := h.exists_pullback
  rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor E Pm huE hD.isQCartier_minus hHm,
    coeff_eq_of_isPullback_qDivisor E P hvE hD.isQCartier_plus hHp, Finsupp.add_apply,
    Finsupp.add_apply, flipTransform_apply_eq hfm Pm P Q hm hp hQ,
    ← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply (Divisor.toQDivisor _),
    Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_apply,
    DivisorWithCoeffs.coeff_apply, flipTransform_apply_eq hfm Pm P Q hm hp hQ, sub_self]

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]

/-- **The graph divisor is exceptional over both sides.** For a threefold step diagram
`X⁻ → Z ← X⁺` (by `f^±`) with normalized graph `(G, u, v)` and graph divisor `H`, the push-forward
`v_* H` vanishes; if moreover `f⁻` is small, then `u_* H` vanishes too. -/
@[mmp "lem_mmp_indexc_graph_pushforward_zero"]
public theorem IsThreefoldGraphDivisor.transformDivisor_eq_zero
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H) :
    RationalMap.transformDivisor v.toRationalMap H = 0 ∧
      (IsSmallMorphism sXm sZ fm → RationalMap.transformDivisor u.toRationalMap H = 0) := by
  have hD := h.isThreefoldStepDiagram
  have hG := h.isNormalizedGraph
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z :=
    haveI := hZ.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsIntegral G := hG.isIntegral
  haveI := hD.isBirationalMorphism_minus.isDominant
  haveI := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isSmallMorphism_plus.isProper
  have hfm := hD.isBirationalMorphism_minus.functionFieldMap_bijective
  have hfp := hD.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective
  have hu := hG.isBirationalMorphism_minus.functionFieldMap_bijective
  have hv := hG.isBirationalMorphism_plus.functionFieldMap_bijective
  haveI := hZ.1
  haveI := hD.isNormalVariety_minus.1
  haveI := hD.isNormalVariety_plus.1
  have hsep : ∀ {Y : Scheme.{0}} (s : Y ⟶ Spec (.of ℂ)) [IsSeparated s],
      IsSeparated (Y ↘ Limits.terminal Scheme) := by
    intro Y s _
    rw [show (Y ↘ Limits.terminal Scheme) = s ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  haveI := hsep sZ
  haveI := hsep sXm
  haveI := hsep sXp
  have hcomp : ∀ x : G, fm (u x) = fp (v x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hG.comp_eq, Scheme.Hom.comp_apply]
  refine ⟨?_, fun hsmall => ?_⟩
  · refine Finsupp.ext fun P => ?_
    rw [Finsupp.zero_apply, RationalMap.transformDivisor]
    refine mapPrimeDivisors_apply_eq_zero H fun E hE => ?_
    have hvE := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff v E P).mp hE
    obtain ⟨Pm, Q, -, hQm, hQp, hQ, -, -⟩ := hD.exists_primeDivisor_valuationOver_eq P
    have hm := map_genericPoint_eq_of_image_eq fm Pm Q hQm
    have hp := map_genericPoint_eq_of_image_eq fp P Q hQp
    exact h.apply_eq_zero hfm hu hv E Pm P Q
      (eq_of_map_eq_genericPoint fm hfm Q (by rw [hcomp, hvE, hp]) hm) hvE hm hp hQ.2
  · refine Finsupp.ext fun Pm => ?_
    rw [Finsupp.zero_apply, RationalMap.transformDivisor]
    refine mapPrimeDivisors_apply_eq_zero H fun E hE => ?_
    have huE := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff u E Pm).mp hE
    obtain ⟨-, e, he⟩ := hD.isExceptionalValuation_iff_of_isSmallMorphism hsmall
    obtain ⟨hPm, -, -⟩ := he Pm
    obtain ⟨Q, hQ, hQP⟩ := Option.bind_eq_some_iff.mp hPm
    have hm := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm Q).mp hQ
    have hQV : Q.genericPoint ∈ biregularLocus fp :=
      MMP.Positivity.mem_biregularLocus_of_coheight_le_one fp hfp
        hD.isSmallMorphism_plus.two_le_codimension Q.coheight_genericPoint.le
    obtain ⟨P', hP', -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZ
        (by rw [hD.comp_eq_plus]; exact hD.isNormalVariety_plus)
        hD.isSmallMorphism_plus.isBirationalMorphism Q
    have hPP' : e Pm = P' := Option.some.inj
      (hQP.symm.trans (inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus P' Q hP' hQV))
    subst hPP'
    exact h.apply_eq_zero hfm hu hv E Pm (e Pm) Q huE
      (eq_of_map_eq_genericPoint fp hfp Q (by rw [← hcomp, huE, hm]) hP') hm hP' hQV

end GraphDivisor

end MMP.Fourfold

/-! ### Prime divisors persist along a terminal chain -/

namespace MMP.Fourfold.StabilizedTail.TerminalChain

section Labels

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The extension of function fields of a composite of dominant morphisms is the composite. -/
private theorem functionFieldMap_comp {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] [IsDominant a] [IsDominant b] :
    functionFieldMap (a ≫ b) = (functionFieldMap a).comp (functionFieldMap b) := by
  suffices h : CommRingCat.ofHom (functionFieldMap (a ≫ b)) =
      CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) from
    congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  apply (cancel_mono (Z.fromSpecStalk (genericPoint Z))).mp
  rw [functionFieldMap_fromSpecStalk (a ≫ b)]
  have h1 := functionFieldMap_fromSpecStalk a
  have h2 := functionFieldMap_fromSpecStalk b
  have hof : CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) =
      CommRingCat.ofHom (functionFieldMap b) ≫ CommRingCat.ofHom (functionFieldMap a) := rfl
  rw [hof, Spec.map_comp, Category.assoc, h2,
    ← Category.assoc (Spec.map (CommRingCat.ofHom (functionFieldMap a))), h1]
  exact (Category.assoc _ _ _).symm

/-- `ord_Q` regarded through a composite is `ord_Q` regarded through the first map, then
restricted along the second. -/
private theorem valuationOver_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (Q : MMP.Mori.PrimeDivisor X) (a : X ⟶ Y)
    (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    Q.valuationOver (a ≫ b) = (Q.valuationOver a).comap (functionFieldMap b) := by
  simp only [PrimeDivisor.valuationOver]
  rw [← Valuation.comap_comp, functionFieldMap_comp a b]

private theorem valuationOver_def {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] (Q : MMP.Mori.PrimeDivisor X) (a : X ⟶ Y) [IsDominant a] :
    Q.valuationOver a = Q.divisorialValuation.comap (functionFieldMap a) := rfl

/-- Two prime divisors whose valuations agree over `Y` have equal valuations over `Z`, for any
`Y ⟶ Z`. -/
private theorem valuationOver_comp_eq_of_comap_eq {X X' Y Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Y] [IsIntegral Z] (Q : MMP.Mori.PrimeDivisor X) (Q' : MMP.Mori.PrimeDivisor X')
    (a : X ⟶ Y) (a' : X' ⟶ Y) (b : Y ⟶ Z) [ha : IsDominant a] [ha' : IsDominant a']
    [hb : IsDominant b] [hab : IsDominant (a ≫ b)] [hab' : IsDominant (a' ≫ b)]
    (h : Q'.divisorialValuation.comap (functionFieldMap a') =
      Q.divisorialValuation.comap (functionFieldMap a)) :
    Q'.valuationOver (a' ≫ b) = Q.valuationOver (a ≫ b) := by
  rw [valuationOver_comp, valuationOver_comp, valuationOver_def, valuationOver_def, h]

/-- `valuationOver` only depends on the morphism. -/
private theorem valuationOver_congr {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] (Q : MMP.Mori.PrimeDivisor X) {a b : X ⟶ Y} [ha : IsDominant a]
    [hb : IsDominant b] (h : a = b) :
    Q.valuationOver a = Q.valuationOver b := by
  subst h; rfl

/-- The image of a prime divisor under an isomorphism. -/
private noncomputable def mapOfIso {V W : Scheme.{0}} (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor W :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (e.hom Q.genericPoint) (by
    rw [coheight_eq_of_isOpenImmersion e.hom]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)

private theorem genericPoint_mapOfIso {V W : Scheme.{0}} (e : V ≅ W)
    (Q : MMP.Mori.PrimeDivisor V) : (mapOfIso e Q).genericPoint = e.hom Q.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- Transport of prime divisors along an isomorphism. -/
private noncomputable def primeDivisorEquivOfIso {V W : Scheme.{0}} (e : V ≅ W) :
    MMP.Mori.PrimeDivisor V ≃ MMP.Mori.PrimeDivisor W where
  toFun := mapOfIso e
  invFun := mapOfIso e.symm
  left_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (mapOfIso e.symm (mapOfIso e Q)).genericPoint = _
    rw [genericPoint_mapOfIso, genericPoint_mapOfIso, ← Scheme.Hom.comp_apply]
    simp
  right_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (mapOfIso e (mapOfIso e.symm Q)).genericPoint = _
    rw [genericPoint_mapOfIso, genericPoint_mapOfIso, ← Scheme.Hom.comp_apply]
    simp

/-- Transport along an isomorphism preserves the divisorial valuation. -/
private theorem divisorialValuation_primeDivisorEquivOfIso {V W : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (e : V ≅ W) [IsDominant e.hom] (Q : MMP.Mori.PrimeDivisor V) :
    Q.divisorialValuation.comap (functionFieldMap e.hom) =
      (primeDivisorEquivOfIso e Q).divisorialValuation := by
  ext g
  rw [Valuation.comap_apply]
  by_cases hg : g = 0
  · simp [hg]
  have hg' : functionFieldMap e.hom g ≠ 0 := (map_ne_zero _).mpr hg
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Positivity.ord_functionFieldMap_of_isIso e.hom Q (primeDivisorEquivOfIso e Q)
      (genericPoint_mapOfIso e Q).symm]

/-- Equivalences composed along a finite sequence of moves. -/
private noncomputable def seqEquiv {α : Type*} {β : ℕ → Type*} (m : ℕ) (e₀ : α ≃ β 0)
    (F : ∀ k < m, β k ≃ β (k + 1)) : ∀ k ≤ m, α ≃ β k
  | 0, _ => e₀
  | k + 1, h => (seqEquiv m e₀ F k (Nat.le_of_succ_le h)).trans (F k h)

/-- `ord_Q` regarded through `e ≫ b`, for an isomorphism `e`, is `ord` of the transported prime
divisor regarded through `b`. -/
private theorem valuationOver_iso_comp {V W Z : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral Z] (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) (b : W ⟶ Z) [IsDominant b]
    [IsDominant e.hom] [IsDominant (e.hom ≫ b)] :
    Q.valuationOver (e.hom ≫ b) = (primeDivisorEquivOfIso e Q).valuationOver b := by
  rw [valuationOver_comp, valuationOver_def Q e.hom, divisorialValuation_primeDivisorEquivOfIso]
  rfl

section Chain

variable {T : StabilizedTail} (C : TerminalChain T)

/-- Every flip of a bridge is a bijection of prime divisors preserving the valuations over the
base of the flip and the boundary coefficients. -/
private theorem exists_flipEquiv (i k : ℕ) (hk : k < (C.bridge i).P.m) :
    haveI := ((C.bridge i).P.isThreefoldStepDiagram k hk).isNormalVariety_target.1.toIsIntegral
    haveI := ((C.bridge i).P.isThreefoldStepDiagram k hk).isBirationalMorphism_minus.isDominant
    haveI := ((C.bridge i).P.isThreefoldStepDiagram k hk).isSmallMorphism_plus
      |>.isBirationalMorphism.isDominant
    ∃ F : MMP.Mori.PrimeDivisor (modelSeq (C.junction i).Y (C.bridge i).P.Y k) ≃
        MMP.Mori.PrimeDivisor (modelSeq (C.junction i).Y (C.bridge i).P.Y (k + 1)),
      ∀ Q, (F Q).divisorialValuation.comap (functionFieldMap ((C.bridge i).P.gp k)) =
          Q.divisorialValuation.comap (functionFieldMap ((C.bridge i).P.g k)) ∧
        ((C.bridge i).P.boundary (k + 1)).coeff (F Q) = ((C.bridge i).P.boundary k).coeff Q := by
  have hD := (C.bridge i).P.isThreefoldStepDiagram k hk
  obtain ⟨-, e, he⟩ :=
    hD.isExceptionalValuation_iff_of_isSmallMorphism ((C.bridge i).isSmallMorphism k hk)
  refine ⟨e, fun Q => ⟨(he Q).2.1, ?_⟩⟩
  rw [RelativeThreefoldProgram.boundary_succ_eq_flipTransform _ hk]
  exact (he Q).2.2

/-- The bijections onto the models of the `i`-th bridge, composed from one onto its first
model `Y_i`. -/
private theorem exists_bridgeEquiv (i : ℕ)
    (e₀ : haveI := (C.junction 0).isBirationalMorphism.isDominant
      MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.junction i).Y)
    (he₀ : haveI := (C.junction 0).isBirationalMorphism.isDominant
      haveI := (C.junction i).isBirationalMorphism.isDominant
      ∀ P, ∃ w, T.IsTransportedValuationFrom i (P.valuationOver (C.junction 0).p) w ∧
        (e₀ P).valuationOver (C.junction i).p = w) :
    haveI := (C.junction 0).isBirationalMorphism.isDominant
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    ∃ e : ∀ k ≤ (C.bridge i).P.m, MMP.Mori.PrimeDivisor (C.junction 0).Y ≃
        MMP.Mori.PrimeDivisor (modelSeq (C.junction i).Y (C.bridge i).P.Y k),
      (∀ (k : ℕ) (hk : k ≤ (C.bridge i).P.m) (P : MMP.Mori.PrimeDivisor (C.junction 0).Y),
        ∃ w, T.IsTransportedValuationFrom i (P.valuationOver (C.junction 0).p) w ∧
          ∃ _ : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k),
            (e k hk P).valuationOver
                (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) =
              w.comap (functionFieldMap (T.f i))) ∧
      ∀ (k : ℕ) (hk : k < (C.bridge i).P.m) (P : MMP.Mori.PrimeDivisor (C.junction 0).Y),
        ((C.bridge i).P.boundary (k + 1)).coeff (e (k + 1) hk P) =
          ((C.bridge i).P.boundary k).coeff (e k hk.le P) := by
  haveI := (C.junction 0).isBirationalMorphism.isDominant
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  choose F hF using exists_flipEquiv C i
  refine ⟨seqEquiv (β := fun k => MMP.Mori.PrimeDivisor
    (modelSeq (C.junction i).Y (C.bridge i).P.Y k)) _ e₀ F, ?_, ?_⟩
  · intro k hk P
    obtain ⟨w, hw, hw'⟩ := he₀ P
    refine ⟨w, hw, ?_⟩
    induction k with
    | zero =>
      refine ⟨(inferInstance : IsDominant ((C.junction i).p ≫ T.f i)), ?_⟩
      change (e₀ P).valuationOver ((C.junction i).p ≫ T.f i) = _
      rw [valuationOver_comp, hw']
    | succ k ih =>
      have hk' : k < (C.bridge i).P.m := hk
      obtain ⟨hdom, hval⟩ := ih hk'.le
      have hD := (C.bridge i).P.isThreefoldStepDiagram k hk'
      haveI := hD.isNormalVariety_target.1.toIsIntegral
      haveI := hD.isBirationalMorphism_minus.isDominant
      have h1 := (C.bridge i).P.modelMap_eq k hk'
      have h2 := (C.bridge i).P.modelMap_succ_eq hk'
      haveI hgh' : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := h1 ▸ hdom
      haveI hh := IsDominant.of_comp ((C.bridge i).P.g k) ((C.bridge i).P.h k)
      haveI hgp : @IsDominant (modelSeq (C.junction i).Y (C.bridge i).P.Y (k + 1)) _
          ((C.bridge i).P.gp k) := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
      haveI hgh : @IsDominant (modelSeq (C.junction i).Y (C.bridge i).P.Y (k + 1)) _
          ((C.bridge i).P.gp k ≫ (C.bridge i).P.h k) :=
        ⟨hh.denseRange.comp hgp.denseRange ((C.bridge i).P.h k).continuous⟩
      haveI hdom' : IsDominant
          (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY (k + 1)) := h2 ▸ hgh
      refine ⟨hdom', ?_⟩
      change (F k hk' (seqEquiv _ e₀ F k hk'.le P)).valuationOver _ = _
      rw [valuationOver_congr _ h2 (ha := hdom') (hb := hgh),
        valuationOver_comp_eq_of_comap_eq _ _ _ _ _ (ha' := hgp) (hab' := hgh) (hab := hgh')
          (hF k hk' _).1,
        ← valuationOver_congr _ h1, hval]
  · intro k hk P
    exact (hF k hk _).2

/-- The bijection onto the prime divisors of the next junction `Y_{i+1}`, the end of the `i`-th
bridge. -/
private theorem exists_junctionEquiv_succ (i : ℕ)
    (e₀ : haveI := (C.junction 0).isBirationalMorphism.isDominant
      MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.junction i).Y)
    (he₀ : haveI := (C.junction 0).isBirationalMorphism.isDominant
      haveI := (C.junction i).isBirationalMorphism.isDominant
      ∀ P, ∃ w, T.IsTransportedValuationFrom i (P.valuationOver (C.junction 0).p) w ∧
        (e₀ P).valuationOver (C.junction i).p = w) :
    haveI := (C.junction 0).isBirationalMorphism.isDominant
    haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
    ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.junction (i + 1)).Y,
      ∀ P, ∃ w, T.IsTransportedValuationFrom (i + 1) (P.valuationOver (C.junction 0).p) w ∧
        (e P).valuationOver (C.junction (i + 1)).p = w := by
  haveI := (C.junction 0).isBirationalMorphism.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
  obtain ⟨E, hE, -⟩ := exists_bridgeEquiv C i e₀ he₀
  refine ⟨(E _ le_rfl).trans (primeDivisorEquivOfIso (C.bridge i).e), fun P => ?_⟩
  obtain ⟨w, hw, hdom, hval⟩ := hE _ le_rfl P
  refine ⟨_, ⟨w, hw, ?_⟩, rfl⟩
  change ((primeDivisorEquivOfIso (C.bridge i).e (E _ le_rfl P)).valuationOver
    (C.junction (i + 1)).p).comap (functionFieldMap (T.fp i)) = w.comap (functionFieldMap (T.f i))
  rw [← valuationOver_comp, ← hval, valuationOver_congr _ (C.bridge i).modelMap_eq,
    valuationOver_iso_comp]

/-- Part (a): the bijections onto every junction `Y_i`, by induction along the chain. -/
private theorem exists_junctionEquiv (i : ℕ) :
    haveI := (C.junction 0).isBirationalMorphism.isDominant
    haveI := (C.junction i).isBirationalMorphism.isDominant
    ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.junction i).Y,
      ∀ P, ∃ w, T.IsTransportedValuationFrom i (P.valuationOver (C.junction 0).p) w ∧
        (e P).valuationOver (C.junction i).p = w := by
  haveI := (C.junction 0).isBirationalMorphism.isDominant
  induction i with
  | zero => exact ⟨Equiv.refl _, fun P => ⟨_, rfl, rfl⟩⟩
  | succ i ih =>
    obtain ⟨e, he⟩ := ih
    exact exists_junctionEquiv_succ C i e he

/-- The stabilization `I(X_i, B_i) ≅ I(X_{i+1}, B_{i+1})` carries a label `u ∈ I_i` to a label
of `I_{i+1}` whose valuation is the transport of `u`. -/
private theorem exists_label_succ (i : ℕ) (u : C.I i) :
    ∃ s : C.I (i + 1), T.IsTransportedValuation i u.1 s.1 := by
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hu : u.1 ∈ lowDiscrepancySet (T.sX i) (T.B i) := C.coe_I i ▸ u.2
  obtain ⟨s, hs, heq⟩ : u.1.comap (functionFieldMap (T.f i)) ∈
      valuationsOver (T.fp i) (lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1))) :=
    T.lowDiscrepancySet_eq i ▸ ⟨u.1, hu, rfl⟩
  exact ⟨⟨s, by rw [← Finset.mem_coe, C.coe_I]; exact hs⟩, heq⟩

end Chain

variable {T : StabilizedTail}

/-- For a terminal chain over a stabilized tail:
* for every junction `Y_i` there is a bijection `e` from the prime divisors of `Y_0` onto those
  of `Y_i` with `ord_{e P}` corresponding to `ord_P`;
* for every bridge `i` there are bijections `e k` from the prime divisors of `Y_0` onto those of
  each model `V_k`, `k ≤ m_i`, with `ord_{e k P}` corresponding to `ord_P`, and under which the
  boundary coefficients are unchanged by every flip `V_k → T_k ← V_{k+1}`;
* for every `i` and `s ∈ I_∞`, the valuation `s'` of `k(X_i)` corresponding to `s` lies in the
  set `I_i` extracted by the `i`-th junction, and `ord_{E_{i,s'}} = s'`. -/
@[mmp "lem_mmp_indexc_labels_persist"]
public theorem exists_equiv_primeDivisor (C : TerminalChain T) :
    (∀ i : ℕ,
      haveI := (C.junction 0).isBirationalMorphism.isDominant
      haveI := (C.junction i).isBirationalMorphism.isDominant
      ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.junction i).Y,
        ∀ P, ∃ w, T.IsTransportedValuationFrom i (P.valuationOver (C.junction 0).p) w ∧
          (e P).valuationOver (C.junction i).p = w) ∧
    (∀ i : ℕ,
      haveI := (C.junction 0).isBirationalMorphism.isDominant
      haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
      haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
      ∃ e : ∀ k ≤ (C.bridge i).P.m, MMP.Mori.PrimeDivisor (C.junction 0).Y ≃
          MMP.Mori.PrimeDivisor (modelSeq (C.junction i).Y (C.bridge i).P.Y k),
        (∀ (k : ℕ) (hk : k ≤ (C.bridge i).P.m) (P : MMP.Mori.PrimeDivisor (C.junction 0).Y),
          ∃ w, T.IsTransportedValuationFrom i (P.valuationOver (C.junction 0).p) w ∧
            ∃ _ : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k),
              (e k hk P).valuationOver
                  (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) =
                w.comap (functionFieldMap (T.f i))) ∧
        ∀ (k : ℕ) (hk : k < (C.bridge i).P.m) (P : MMP.Mori.PrimeDivisor (C.junction 0).Y),
          ((C.bridge i).P.boundary (k + 1)).coeff (e (k + 1) hk P) =
            ((C.bridge i).P.boundary k).coeff (e k hk.le P)) ∧
    ∀ (i : ℕ) (s : C.I 0), ∃ s' : C.I i, T.IsTransportedValuationFrom i s.1 s'.1 ∧
      haveI := (C.junction i).isBirationalMorphism.isDominant
      ((C.junction i).E s').valuationOver (C.junction i).p = s'.1 := by
  refine ⟨exists_junctionEquiv C, fun i => ?_, fun i s => ?_⟩
  · obtain ⟨e, he⟩ := exists_junctionEquiv C i
    exact exists_bridgeEquiv C i e he
  · induction i with
    | zero => exact ⟨s, rfl, (C.junction 0).valuation_eq s⟩
    | succ i ih =>
      obtain ⟨u, hu, -⟩ := ih
      obtain ⟨s', hs'⟩ := exists_label_succ C i u
      exact ⟨s', ⟨u.1, hu, hs'⟩, (C.junction (i + 1)).valuation_eq _⟩

end Labels

end MMP.Fourfold.StabilizedTail.TerminalChain

/-! ### The default weight -/

namespace MMP.Fourfold

/-- A term `w(1 - j(1 - b))` vanishes once `1 / (1 - b) ≤ j`. -/
private theorem difficultyWeight_eq_zero_of_le (N : ℕ) {b : ℝ} (hb1 : b < 1) {j : ℕ}
    (hj : 1 / (1 - b) ≤ (j : ℝ)) : difficultyWeight N (1 - j * (1 - b)) = 0 := by
  apply difficultyWeight_of_nonpos
  have hpos : 0 < 1 - b := by linarith
  rw [div_le_iff₀ hpos] at hj
  linarith

/-- For `b < 1`, the default weight `d(b)` is the finite sum over `1 ≤ j < ⌈1 / (1 - b)⌉`. -/
private theorem defaultWeight_eq_sum_Ico (N : ℕ) {b : ℝ} (hb1 : b < 1) :
    defaultWeight N b =
      ∑ j ∈ Finset.Ico 1 ⌈1 / (1 - b)⌉₊, difficultyWeight N (1 - j * (1 - b)) := by
  rw [defaultWeight, ← finsum_mem_coe_finset]
  refine finsum_congr fun j => ?_
  simp only [Finset.coe_Ico, Set.mem_Ico]
  by_cases hj : j < ⌈1 / (1 - b)⌉₊
  · rw [and_iff_left hj]
  · simp [hj, difficultyWeight_eq_zero_of_le N hb1 (Nat.ceil_le.mp (not_lt.mp hj))]

/-- For `0 ≤ b < 1`: every `j ≥ 1` with `w(1 - j(1 - b)) ≠ 0` satisfies `j < 1 / (1 - b)`; hence
the default `d(b)` is the finite sum of `w(1 - j(1 - b))` over `1 ≤ j < ⌈1 / (1 - b)⌉`; and
`d(0) = 0`. -/
@[mmp "lem_mmp_indexd_default_finite"]
public theorem defaultWeight_finite (N : ℕ) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (∀ j : ℕ, 1 ≤ j → difficultyWeight N (1 - j * (1 - b)) ≠ 0 → (j : ℝ) < 1 / (1 - b)) ∧
    defaultWeight N b =
      ∑ j ∈ Finset.Ico 1 ⌈1 / (1 - b)⌉₊, difficultyWeight N (1 - j * (1 - b)) ∧
    defaultWeight N 0 = 0 := by
  refine ⟨fun j _ hne => not_le.mp fun h => hne (difficultyWeight_eq_zero_of_le N hb1 h),
    defaultWeight_eq_sum_Ico N hb1, ?_⟩
  rw [defaultWeight_eq_sum_Ico N zero_lt_one]
  norm_num

/-- The default `d(b) = ∑_{j ≥ 1} w(1 - j(1 - b))` is monotone on `[0, 1)`: for
`0 ≤ b' ≤ b < 1`, `d(b') ≤ d(b)`. -/
@[mmp "lem_mmp_indexd_default_monotone"]
public theorem monotoneOn_defaultWeight (N : ℕ) : MonotoneOn (defaultWeight N) (Set.Ico 0 1) := by
  rintro b' ⟨-, hb'1⟩ b ⟨-, hb1⟩ hle
  rw [defaultWeight_eq_sum_Ico N hb'1, defaultWeight_eq_sum_Ico N hb1]
  calc ∑ j ∈ Finset.Ico 1 ⌈1 / (1 - b')⌉₊, difficultyWeight N (1 - j * (1 - b'))
      ≤ ∑ j ∈ Finset.Ico 1 ⌈1 / (1 - b)⌉₊, difficultyWeight N (1 - j * (1 - b')) :=
        Finset.sum_le_sum_of_subset <| Finset.Ico_subset_Ico le_rfl <|
          Nat.ceil_mono <| one_div_le_one_div_of_le (by linarith) (by linarith)
    _ ≤ ∑ j ∈ Finset.Ico 1 ⌈1 / (1 - b)⌉₊, difficultyWeight N (1 - j * (1 - b)) :=
        Finset.sum_le_sum fun j _ => difficultyWeight_mono N <|
          sub_le_sub_left (mul_le_mul_of_nonneg_left (by linarith) j.cast_nonneg) 1

end MMP.Fourfold

/-! ### Affine charts of the complex realization -/

namespace MMP.Analytic

section Charts

open CategoryTheory AlgebraicGeometry Topology ComplexPoints

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

private lemma mem_chart_basicOpen_iff {U : X.Opens} (y : chart (sX := sX) U) (a : Γ(X, U)) :
    y.1 ∈ chart (sX := sX) (X.basicOpen a) ↔ ComplexPoints.eval U a y ≠ 0 := by
  rw [mem_chart_iff]
  have h := Scheme.basicOpen_appLE y.1.hom ⊤ U y.2.ge a
  have e : y.1.hom.appLE U ⊤ y.2.ge a =
      (Scheme.ΓSpecIso (.of ℂ)).inv (ComplexPoints.eval U a y) := by
    simp only [ComplexPoints.eval]
    exact (Iso.hom_inv_id_apply _ _).symm
  rw [e, basicOpen_eq_of_affine, top_inf_eq] at h
  change (default : Spec (.of ℂ)) ∈ y.1.hom ⁻¹ᵁ X.basicOpen a ↔ _
  rw [← h]
  generalize (default : ↥(Spec (CommRingCat.of ℂ))) = p
  have hp := Ideal.eq_bot_of_prime (show PrimeSpectrum ℂ from p).asIdeal
  refine (PrimeSpectrum.mem_basicOpen (x := (show PrimeSpectrum ℂ from p)) _).trans ?_
  rw [hp]
  simp

private lemma eval_inclusion {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : chart (sX := sX) V) :
    ComplexPoints.eval U f (Set.inclusion (chart_mono h) y) =
      ComplexPoints.eval V (X.presheaf.map (homOfLE h).op f) y :=
  evalHom_res h y f

private lemma continuous_inclusion {U V : X.Opens} (h : V ≤ U) :
    Continuous[chartTopology V, chartTopology U] (Set.inclusion (chart_mono (sX := sX) h)) := by
  refine continuous_iInf_rng.2 fun f => continuous_induced_rng.2 ?_
  have : ComplexPoints.eval U f ∘ Set.inclusion (chart_mono (sX := sX) h) =
      ComplexPoints.eval V (X.presheaf.map (homOfLE h).op f) := funext (eval_inclusion h f)
  rw [this]
  exact continuous_eval V _

private lemma isOpenEmbedding_inclusion_basicOpen {V : X.Opens} (hV : IsAffineOpen V)
    (a : Γ(X, V)) :
    @IsOpenEmbedding _ _ (chartTopology (X.basicOpen a)) (chartTopology V)
      (Set.inclusion (chart_mono (sX := sX) (X.basicOpen_le a))) := by
  set ι := Set.inclusion (chart_mono (sX := sX) (X.basicOpen_le a))
  have hne : ∀ y, ComplexPoints.eval V a (ι y) ≠ 0 := fun y =>
    (mem_chart_basicOpen_iff (ι y) a).1 y.2
  have hind : chartTopology (X.basicOpen a) = TopologicalSpace.induced ι (chartTopology V) := by
    refine le_antisymm (continuous_iff_le_induced.1 (continuous_inclusion (X.basicOpen_le a))) ?_
    refine le_iInf fun g => continuous_iff_le_induced.1 ?_
    letI := hV.isLocalization_basicOpen a
    obtain ⟨⟨r, _, n, rfl⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers a) g
    have key : ComplexPoints.eval (X.basicOpen a) g =
        fun y => ComplexPoints.eval V r (ι y) / ComplexPoints.eval V a (ι y) ^ n := by
      funext y
      rw [eq_div_iff (pow_ne_zero _ (hne y))]
      have := congrArg (evalHom (X.basicOpen a) y) hrs
      simp only [map_mul, map_pow] at this
      rw [evalHom_apply, evalHom_apply, evalHom_apply] at this
      rw [eval_inclusion (X.basicOpen_le a) r y, eval_inclusion (X.basicOpen_le a) a y]
      exact this
    rw [key]
    letI : TopologicalSpace (chart (sX := sX) V) := chartTopology V
    letI : TopologicalSpace (chart (sX := sX) (X.basicOpen a)) :=
      TopologicalSpace.induced ι (chartTopology V)
    have hι : Continuous ι := continuous_induced_dom
    exact (((continuous_eval V r).comp hι).div
      (((continuous_eval V a).comp hι).pow n)
      fun y => pow_ne_zero _ (hne y))
  refine @IsOpenEmbedding.mk _ _ (chartTopology (X.basicOpen a)) (chartTopology V) ι
    (@IsEmbedding.mk _ _ (chartTopology (X.basicOpen a)) (chartTopology V) ι
      (@IsInducing.mk _ _ (chartTopology (X.basicOpen a)) (chartTopology V) ι hind)
      (Set.inclusion_injective _)) ?_
  have : Set.range ι = ComplexPoints.eval V a ⁻¹' {0}ᶜ := by
    ext y
    refine ⟨?_, fun hy => ⟨⟨y.1, (mem_chart_basicOpen_iff y a).2 hy⟩, rfl⟩⟩
    rintro ⟨z, rfl⟩
    exact hne z
  rw [this]
  exact @Continuous.isOpen_preimage _ _ (chartTopology V) _ _ (continuous_eval V a) _
    isClosed_singleton.isOpen_compl

private lemma isOpen_trace_image (U V : X.affineOpens) (O : Set (chart (sX := sX) (U : X.Opens)))
    (hO : IsOpen[chartTopology (U : X.Opens)] O) :
    IsOpen[chartTopology (V : X.Opens)]
      {y : chart (sX := sX) (V : X.Opens) | y.1 ∈ Subtype.val '' O} := by
  rw [@isOpen_iff_forall_mem_open _ (chartTopology (V : X.Opens))]
  rintro y ⟨o, ho, hoy⟩
  have hx : y.1.toScheme ∈ (U : X.Opens) ⊓ V :=
    ⟨hoy ▸ mem_chart_iff.1 o.2, mem_chart_iff.1 y.2⟩
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 _ hx
  have hDU : X.basicOpen g ≤ U := hfg ▸ X.basicOpen_le f
  have hemb := isOpenEmbedding_inclusion_basicOpen (sX := sX) V.2 g
  refine ⟨Set.inclusion (chart_mono (sX := sX) (X.basicOpen_le g)) ''
      (Set.inclusion (chart_mono (sX := sX) hDU) ⁻¹' O), ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, hz, rfl⟩
  · exact @IsOpenEmbedding.isOpenMap _ _ _ (chartTopology (X.basicOpen g))
      (chartTopology (V : X.Opens)) hemb _
      (@Continuous.isOpen_preimage _ _ (chartTopology (X.basicOpen g))
        (chartTopology (U : X.Opens)) _
        (continuous_inclusion hDU) _ hO)
  · refine ⟨⟨y.1, mem_chart_iff.2 (hfg ▸ hxf)⟩, ?_, rfl⟩
    have : Set.inclusion (chart_mono (sX := sX) hDU) ⟨y.1, mem_chart_iff.2 (hfg ▸ hxf)⟩ = o :=
      Subtype.ext hoy.symm
    rw [Set.mem_preimage, this]
    exact ho

private lemma isOpen_image_val (U : X.affineOpens) (O : Set (chart (sX := sX) (U : X.Opens)))
    (hO : IsOpen[chartTopology (U : X.Opens)] O) : IsOpen (Subtype.val '' O) :=
  (isOpen_iff _).2 fun V => isOpen_trace_image U V O hO

private lemma isOpen_chart (U : X.affineOpens) : IsOpen (chart (sX := sX) (U : X.Opens)) := by
  simpa using isOpen_image_val U Set.univ (@isOpen_univ _ (chartTopology _))

private lemma instTopologicalSpace_eq_chartTopology (U : X.affineOpens) :
    (inferInstance : TopologicalSpace (chart (sX := sX) (U : X.Opens))) =
      chartTopology (U : X.Opens) := by
  refine le_antisymm (TopologicalSpace.le_def.2 fun O hO => ?_)
    (continuous_iff_le_induced.1 (continuous_chart_val U))
  exact isOpen_induced_iff.2
    ⟨_, isOpen_image_val U O hO, Set.preimage_image_eq _ Subtype.val_injective⟩

private lemma isIso_fromSpec_top : IsIso (isAffineOpen_top (Spec (.of ℂ))).fromSpec := by
  rw [IsAffineOpen.fromSpec_top]
  infer_instance

private lemma pres_apply (c : Chart sX) (q : MvPolynomial (Fin c.n) ℂ) :
    MvPolynomial.eval₂Hom (baseRingHom sX c.U) c.gen q = c.pres q :=
  rfl

private lemma coords_injective (c : Chart sX) : Function.Injective c.coords := by
  intro y y' h
  have hev : evalHom c.U y = evalHom c.U y' := by
    ext f
    obtain ⟨q, rfl⟩ := c.surjective f
    rw [pres_apply, c.evalHom_pres, c.evalHom_pres, h]
  have happ : y.1.hom.appLE c.U ⊤ y.2.ge = y'.1.hom.appLE c.U ⊤ y'.2.ge := by
    refine (cancel_mono (Scheme.ΓSpecIso (.of ℂ)).hom).1 ?_
    ext1
    exact hev
  haveI := isIso_fromSpec_top
  refine Subtype.ext (ComplexPoints.ext ((cancel_epi (isAffineOpen_top _).fromSpec).1 ?_))
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec _ c.isAffineOpen (isAffineOpen_top _) y.2.ge,
    ← IsAffineOpen.SpecMap_appLE_fromSpec _ c.isAffineOpen (isAffineOpen_top _) y'.2.ge, happ]

private lemma isEmbedding_coords (c : Chart sX) :
    @IsEmbedding _ _ (chartTopology c.U) _ c.coords := by
  refine @IsEmbedding.mk _ _ (chartTopology c.U) _ _
    (@IsInducing.mk _ _ (chartTopology c.U) _ _ ?_) (coords_injective c)
  refine le_antisymm (continuous_iff_le_induced.1
    (@continuous_pi _ _ _ (chartTopology c.U) _ _ fun i => continuous_eval c.U (c.gen i))) ?_
  refine le_iInf fun f => continuous_iff_le_induced.1 ?_
  obtain ⟨q, rfl⟩ := c.surjective f
  have e : ComplexPoints.eval c.U (MvPolynomial.eval₂Hom (baseRingHom sX c.U) c.gen q) =
      fun y => MvPolynomial.eval (c.coords y) q :=
    funext fun y => c.evalHom_pres y q
  rw [e]
  letI : TopologicalSpace (chart (sX := sX) c.U) :=
    TopologicalSpace.induced c.coords inferInstance
  exact (MvPolynomial.continuous_eval q).comp continuous_induced_dom

private lemma exists_coords_eq_of_mem_zeroLocus (c : Chart sX) {p : Fin c.n → ℂ}
    (hp : p ∈ MvPolynomial.zeroLocus ℂ c.ideal) : ∃ y, c.coords y = p := by
  let φ : Γ(X, c.U) →+* ℂ := RingHom.liftOfSurjective c.pres c.surjective
    ⟨MvPolynomial.eval p, fun q hq => by simpa [MvPolynomial.coe_aeval_eq_eval] using hp q hq⟩
  have hφ : ∀ q, φ (c.pres q) = MvPolynomial.eval p q := fun q =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ q
  have hU := c.isAffineOpen
  haveI := isIso_fromSpec_top
  let x : Spec (.of ℂ) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hmem : x ⁻¹ᵁ c.U = ⊤ := by
    refine eq_top_iff.2 fun t _ => ?_
    change x t ∈ c.U
    rw [Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  have htop : (isAffineOpen_top (Spec (.of ℂ))).fromSpec =
      Spec.map (Scheme.ΓSpecIso (.of ℂ)).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
    rfl
  have hsec : x ≫ sX = 𝟙 _ := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec sX (isAffineOpen_top _) hU (by simp)
    rw [Category.assoc, ← h, htop, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id,
      Spec.map_inj]
    ext a
    have : (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sX.appLE ⊤ c.U (by simp) =
        CommRingCat.ofHom (baseRingHom sX c.U) := rfl
    rw [this]
    change φ (baseRingHom sX c.U a) = a
    rw [← MvPolynomial.eval₂Hom_C (baseRingHom sX c.U) c.gen a, pres_apply, hφ,
      MvPolynomial.eval_C]
  let y : chart (sX := sX) c.U := ⟨⟨x, hsec⟩, hmem⟩
  have happ : x.appLE c.U ⊤ hmem.ge = CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of ℂ)).inv := by
    rw [← Spec.map_inj, Spec.map_comp, ← htop]
    refine (cancel_mono hU.fromSpec).1 ?_
    rw [IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) hmem.ge, Category.assoc]
  refine ⟨y, funext fun i => ?_⟩
  change (Scheme.ΓSpecIso (.of ℂ)).hom (x.appLE c.U ⊤ hmem.ge (c.gen i)) = p i
  rw [happ]
  change (Scheme.ΓSpecIso (.of ℂ)).hom ((Scheme.ΓSpecIso (.of ℂ)).inv (φ (c.gen i))) = p i
  rw [Iso.inv_hom_id_apply, ← MvPolynomial.eval₂Hom_X' (baseRingHom sX c.U) c.gen i,
    pres_apply, hφ, MvPolynomial.eval_X]

private lemma range_coords (c : Chart sX) :
    Set.range c.coords = MvPolynomial.zeroLocus ℂ c.ideal := by
  ext p
  refine ⟨?_, exists_coords_eq_of_mem_zeroLocus c⟩
  rintro ⟨y, rfl⟩ q hq
  change MvPolynomial.eval (c.coords y) q = 0
  rw [← c.evalHom_pres, (RingHom.mem_ker).1 hq, map_zero]

/-- For an affine chart `c` of a scheme over `ℂ`, the `ℂ`-points of `c.U` form an open subset of
the complex realization; the subspace topology on it is `ComplexPoints.chartTopology c.U`; and the
coordinate map `c.coords` is a topological embedding of it into `ℂⁿ` with image the zero locus of
the ideal of relations `c.ideal`. -/
@[mmp "lem_mmp_realization_affine_charts"]
public theorem Chart.isOpen_chart_and_isEmbedding_coords (c : Chart sX) :
    IsOpen (ComplexPoints.chart (sX := sX) c.U) ∧
      (inferInstance : TopologicalSpace (ComplexPoints.chart (sX := sX) c.U)) =
        ComplexPoints.chartTopology c.U ∧
      IsEmbedding c.coords ∧
      Set.range c.coords = MvPolynomial.zeroLocus ℂ c.ideal := by
  have hb := instTopologicalSpace_eq_chartTopology (sX := sX) ⟨c.U, c.isAffineOpen⟩
  refine ⟨isOpen_chart ⟨c.U, c.isAffineOpen⟩, hb, ?_, range_coords c⟩
  change @IsEmbedding _ _ (inferInstance : TopologicalSpace (chart (sX := sX) c.U)) _ c.coords
  rw [hb]
  exact isEmbedding_coords c

end Charts

/-! ### Closed immersions, fibre products and projective morphisms -/

namespace ComplexPoints

open CategoryTheory AlgebraicGeometry Topology

section ClosedImmersion

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}

/-- The realized map `X^an → Y^an` of a closed immersion `f : X ⟶ Y` of schemes of finite type
over `ℂ` is a closed embedding. -/
@[mmp "lem_mmp_realization_closed_immersion"]
public theorem isClosedEmbedding_realize [LocallyOfFiniteType sX] [QuasiCompact sX]
    [LocallyOfFiniteType sY] [QuasiCompact sY] (f : X ⟶ Y) [IsClosedImmersion f]
    (hf : f ≫ sY = sX) : IsClosedEmbedding (realize f hf) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  have : f.IsOver (Spec (.of ℂ)) := ⟨hf⟩
  exact (homeomorphUnderlyingSpace (X := Y)).symm.isClosedEmbedding.comp
    ((MMP.UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion
      (K := ℂ) f).comp (homeomorphUnderlyingSpace (X := X)).isClosedEmbedding)

end ClosedImmersion

section FibreProduct

open Limits

variable {X Y S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
  {sS : S ⟶ Spec (.of ℂ)}

/-- For schemes `X`, `Y`, `S` of finite type over `ℂ` and morphisms `f : X ⟶ S`, `g : Y ⟶ S`
over `ℂ`, the natural map `(X ×_S Y)^an → X^an × Y^an` given by realizing the two projections
is a topological embedding with image the topological fibre product
`{(x, y) | realize f x = realize g y}`; that is, `(X ×_S Y)^an ≃ₜ X^an ×_{S^an} Y^an`. -/
@[mmp "lem_mmp_realization_fibre_products"]
public theorem isEmbedding_realize_pullback
    [LocallyOfFiniteType sX] [QuasiCompact sX] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [LocallyOfFiniteType sS] [QuasiCompact sS]
    (f : X ⟶ S) (g : Y ⟶ S) (hf : f ≫ sS = sX) (hg : g ≫ sS = sY) :
    IsEmbedding (fun z : ComplexPoints (pullback.fst f g ≫ sX) =>
        (realize (pullback.fst f g) rfl z,
          realize (sY := sY) (pullback.snd f g)
            (by rw [← hg, ← Category.assoc, ← pullback.condition, Category.assoc, hf]) z)) ∧
      Set.range (fun z : ComplexPoints (pullback.fst f g ≫ sX) =>
        (realize (pullback.fst f g) rfl z,
          realize (sY := sY) (pullback.snd f g)
            (by rw [← hg, ← Category.assoc, ← pullback.condition, Category.assoc, hf]) z)) =
        {p | realize f hf p.1 = realize g hg p.2} := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  let : S.Over (Spec (.of ℂ)) := ⟨sS⟩
  let : (pullback f g).Over (Spec (.of ℂ)) := ⟨pullback.fst f g ≫ sX⟩
  have hsnd : pullback.snd f g ≫ sY = pullback.fst f g ≫ sX := by
    rw [← hg, ← Category.assoc, ← pullback.condition, Category.assoc, hf]
  have : (pullback.fst f g).IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : (pullback.snd f g).IsOver (Spec (.of ℂ)) := ⟨hsnd⟩
  have : f.IsOver (Spec (.of ℂ)) := ⟨hf⟩
  have : g.IsOver (Spec (.of ℂ)) := ⟨hg⟩
  have H := IsPullback.of_hasPullback f g
  let eX := homeomorphUnderlyingSpace (X := X)
  let eY := homeomorphUnderlyingSpace (X := Y)
  let φ := (eX.symm.prodCongr eY.symm) ∘
    MMP.UnderlyingSpace.prodMap (K := ℂ) (pullback.fst f g) (pullback.snd f g) ∘
      homeomorphUnderlyingSpace
  have hrange : Set.range φ = {p | realize f hf p.1 = realize g hg p.2} := by
    rw [Set.range_comp, Set.range_comp, Homeomorph.range_coe, Set.image_univ,
      MMP.UnderlyingSpace.range_prodMap_of_isPullback (K := ℂ) H,
      Homeomorph.image_eq_preimage_symm]
    ext ⟨x, y⟩
    exact homeomorphUnderlyingSpace.injective.eq_iff.symm
  exact ⟨(eX.symm.prodCongr eY.symm).isEmbedding.comp
    ((MMP.UnderlyingSpace.isEmbedding_prodMap_of_isPullback (K := ℂ) H).comp
      homeomorphUnderlyingSpace.isEmbedding), hrange⟩

end FibreProduct

section Projective

variable {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}

/-- The realization of a proper morphism of schemes locally of finite type over `ℂ` is a proper
map. -/
private lemma isProperMap_realize [X.Over (Spec (.of ℂ))]
    [S.Over (Spec (.of ℂ))] [LocallyOfFiniteType (S ↘ Spec (.of ℂ))]
    (f : X ⟶ S) [f.IsOver (Spec (.of ℂ))] [IsProper f]
    (hf : f ≫ S ↘ Spec (.of ℂ) = X ↘ Spec (.of ℂ)) : IsProperMap (realize f hf) := by
  have : realize f hf =
      homeomorphUnderlyingSpace.symm ∘ MMP.UnderlyingSpace.map (K := ℂ) f ∘
        homeomorphUnderlyingSpace := by
    funext x
    exact homeomorphUnderlyingSpace.eq_symm_apply.mpr (MMP.UnderlyingSpace.ext rfl)
  rw [this]
  exact homeomorphUnderlyingSpace.symm.isProperMap.comp
    ((MMP.UnderlyingSpace.isProperMap_map f).comp
      homeomorphUnderlyingSpace.isProperMap)

/-- Let `f : X ⟶ S` be a morphism of schemes of finite type over `ℂ` admitting a closed immersion
`X ⟶ ℙᴺ_S` over `S`. Then the inverse image under the realized map `X^an → S^an` of every compact
subset of `S^an` is compact. -/
@[mmp "lem_mmp_projective_realization_compact_preimage"]
public theorem isCompact_preimage_realize_of_exists_isClosedImmersion
    [LocallyOfFiniteType sX] [QuasiCompact sX] [LocallyOfFiniteType sS] [QuasiCompact sS]
    (f : X ⟶ S) (hf : f ≫ sS = sX)
    (hproj : ∃ (N : ℕ) (i : X ⟶ projectiveSpaceOver N S),
      IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver N S ↘ S) = f)
    {C : Set (ComplexPoints sS)} (hC : IsCompact C) :
    IsCompact (realize f hf ⁻¹' C) := by
  obtain ⟨N, i, _, hif⟩ := hproj
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : S.Over (Spec (.of ℂ)) := ⟨sS⟩
  have : f.IsOver (Spec (.of ℂ)) := ⟨hf⟩
  have := isProper_projectiveSpaceOver N S
  have : IsProper f := hif ▸ inferInstance
  have : LocallyOfFiniteType (S ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sS›
  exact (isProperMap_realize f hf).isCompact_preimage hC

end Projective

end ComplexPoints

end MMP.Analytic

end
