module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Analytic.ComplexRealizationCharts
import MMP.RingTheory.RegularLocalRing.CompletionStrictHenselization
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper

/-!
# Threefold step diagrams: the graph divisor and finite chains

Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a threefold step diagram with normalized graph `(G, u, v)` and
graph divisor `H = u^* D⁻ - v^* D⁺`, `D^± = K_{X^±} + B^±`. Then `H ≥ 0`, by the negativity
lemma for `v : G ⟶ X⁺`: `-H` is ample over `Z`, hence `v`-nef, and `v_* H = 0`. For a finite
chain `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `k < m`, of threefold step diagrams and compatible
birational morphisms `q_k : W ⟶ V_k` from a smooth projective variety, the comparison divisor
`q_0^*(K_{V_0} + Θ_0) - q_m^*(K_{V_m} + Θ_m)` is effective: it is the telescoping sum of the
divisors `q_k^* D_k - q_{k+1}^* D_{k+1}`, each effective by the same negativity argument run on
`W`.

## Main results

* `MMP.Fourfold.IsThreefoldGraphDivisor.nonneg`: the graph divisor is effective.
* `MMP.Fourfold.pullback_sub_pullback_nonneg_of_isThreefoldStepDiagram`: the comparison divisor
  of a finite chain of threefold step diagrams is effective.

## Implementation notes

Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened only for that result. The source lifts `(q_k, q_{k+1})` to the normalized graph `G_k` of
the `k`-th step and pulls back the graph divisor `H_k ≥ 0`; the proof here runs the negativity
argument proving `H_k ≥ 0` on `W` itself, which yields `q_k^* D_k - q_{k+1}^* D_{k+1} ≥ 0`
without constructing `G_k`. In a chain the canonical divisor and boundary of `V_{k+1}` are the
strict transforms `MMP.Mori.flipTransform (g k) (gp k)`, the convention of
`MMP.Fourfold.IsThreefoldStepDiagram`, and pull-backs are `MMP.Mori.QDivisor.pullback`. The base
field is `ℂ`.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4], the threefold index chain
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_mmp_indexc_graph_h_effective

open MMP.Mori MMP.Fourfold

/-- A `ℚ`-divisor with a `g`-ample multiple is `v`-nef for every `v` whose contracted curves are
contracted by `g`. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple {X Y W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] {g : X ⟶ W} {v : X ⟶ Y} {D : QDivisor X}
    (hD : D.HasRelativelyAmpleMultiple g)
    (hvg : ∀ C : ProperCurve sX, C.IsContractedBy v → C.IsContractedBy g) :
    D.IsRelativelyNef sX v := by
  obtain ⟨m, hm, L, hLc, hL, hamp⟩ := hD
  have hDq : D.IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hL, hLc⟩
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hDq fun C hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX C.ι C.dim_le D hDq hm L hLc hL]
  haveI := hLc.isInvertibleModule_divisorialSheaf
  have := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
    g _ hamp C (hvg C hC)
  exact (div_pos (Int.cast_pos.mpr this) (Nat.cast_pos.mpr hm)).le

/-- The `ℚ`-Cartier property passes from `-D` to `D`. -/
private theorem isQCartier_of_isQCartier_neg {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : QDivisor X} (h : (-D).IsQCartier) : D.IsQCartier := by
  obtain ⟨n, hn, E, hE, hEc⟩ := h
  exact ⟨-n, neg_ne_zero.mpr hn, E, by rw [hE, smul_neg, neg_smul], hEc⟩

end Proof_lem_mmp_indexc_graph_h_effective

namespace MMP.Fourfold

open Proof_lem_mmp_indexc_graph_h_effective

open MMP.Mori

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]

/-- **The graph divisor is effective.** For a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`
with normalized graph `(G, u, v)` and graph divisor `H = u^* D⁻ - v^* D⁺`, we have `0 ≤ H`. -/
@[mmp "lem_mmp_indexc_graph_h_effective"]
public theorem IsThreefoldGraphDivisor.nonneg
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H) : 0 ≤ H := by
  have hD := h.isThreefoldStepDiagram
  have hG := h.isNormalizedGraph
  haveI := hG.isIntegral
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_plus
  haveI : IsFinite (Limits.pullback.lift u v hG.comp_eq) := hG.isFinite
  haveI : IsProper v := by
    rw [← Limits.pullback.lift_snd u v hG.comp_eq]
    infer_instance
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace v
  haveI := hD.isNormalVariety_plus.1
  have hnef : (-H).IsRelativelyNef (v ≫ sXp) v :=
    isRelativelyNef_of_hasRelativelyAmpleMultiple _ h.hasRelativelyAmpleMultiple_neg
      fun C hC x hx => by
        rw [hG.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  exact DivisorWithCoeffs.isEffective_iff_nonneg.mp <|
    QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg ℂ sXp (v ≫ sXp)
      hD.isNormalVariety_plus ⟨⟨⟩, inferInstance⟩ v rfl hG.isBirationalMorphism_plus
      (isQCartier_of_isQCartier_neg hnef.1) hnef
      (by rw [h.transformDivisor_eq_zero.1]; exact DivisorWithCoeffs.isEffective_zero)

end MMP.Fourfold

namespace Proof_lem_mmp_indexc_finite_program_comparison

open MMP.Mori MMP.Fourfold

/-! ### Push-forward of the comparison divisor of one step -/

section Pushforward

universe u

private theorem genericPoint_mem_support {X : Scheme.{u}} (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∈ (P.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

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

/-- Two points of `X` over the generic point of a prime divisor `Q` of the normal scheme `Y` are
equal, for `f : X ⟶ Y` separated, dominant and birational. -/
private theorem eq_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f] [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (Q : MMP.Mori.PrimeDivisor Y) {x₁ x₂ : X}
    (h₁ : f x₁ = Q.genericPoint) (h₂ : f x₂ = Q.genericPoint) : x₁ = x₂ := by
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (f x₁)) := by rw [h₁]; infer_instance
  haveI : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h₂]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf (h₂.trans h₁.symm)

/-- A birational morphism induces an isomorphism of local rings at a point over the generic point
of a prime divisor. -/
private theorem isIso_stalkMap_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (P : MMP.Mori.PrimeDivisor Y) {x : X}
    (hx : f x = P.genericPoint) : IsIso (f.stalkMap x) := by
  have := P.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x

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
  have hP := genericPoint_mem_support P
  rw [support_inverseTransformPrimeDivisor h] at hP
  have hsub : (inverseTransform f Q'.idealSheaf.support : Set X) ⊆ f ⁻¹' (Q'.support : Set Y) :=
    closure_minimal (fun z hz => hz.1) (Q'.idealSheaf.support.isClosed.preimage f.continuous)
  have hQ' : Q.genericPoint ∈ (Q'.support : Set Y) := he ▸ hsub hP
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (Q'.eq_genericPoint_of_mem_support hQ' Q.coheight_genericPoint).symm

/-- **Coefficients of the strict transform.** If `f(η_{P⁻}) = f⁺(η_P) = η_Q` with `f⁺` an
isomorphism over `η_Q`, the coefficient of `P` in `(f⁺)⁻¹_* (f⁻)_* D` is that of `P⁻` in `D`. -/
private theorem flipTransform_apply_eq {Xm Xp Z : Scheme.{u}} [IsIntegral Xm]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
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
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (eq_of_map_eq_genericPoint fm hfm Q
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm' Q).mp h') hm)

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

/-- **The comparison divisor vanishes over a common prime divisor.** If a prime divisor `E` of `W`
lies over prime divisors `P⁻` of `X⁻` and `P` of `X⁺`, both over the prime divisor `Q` of `Z`, and
`f⁺` is an isomorphism over `η_Q`, then the coefficient of `E` in `q^* D⁻ - p^* D⁺` is `0`. -/
private theorem apply_sub_eq_zero
    {Xm Xp Z W : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsSeparated (Z ↘ Limits.terminal Scheme)]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hD : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) [IsSeparated fm] [IsDominant fm]
    {q : W ⟶ Xm} {p : W ⟶ Xp} [IsDominant q] [IsDominant p]
    (hfm : Function.Bijective (functionFieldMap fm)) (hu : Function.Bijective (functionFieldMap q))
    (hv : Function.Bijective (functionFieldMap p)) {Em Ep : QDivisor W}
    {hm : ∀ T : irreducibleComponents W,
      q (componentGenericPoint W T) ∉ (Divisor.toQDivisor K + B).supp}
    {hp' : ∀ T : irreducibleComponents W, p (componentGenericPoint W T) ∉
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).supp}
    (hEm : (Divisor.toQDivisor K + B).IsPullback q hm Em)
    (hEp : (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).IsPullback p hp'
      Ep) (E : MMP.Mori.PrimeDivisor W)
    (Pm : MMP.Mori.PrimeDivisor Xm) (P : MMP.Mori.PrimeDivisor Xp) (Q : MMP.Mori.PrimeDivisor Z)
    (huE : q E.genericPoint = Pm.genericPoint) (hvE : p E.genericPoint = P.genericPoint)
    (hmQ : fm Pm.genericPoint = Q.genericPoint) (hpQ : fp P.genericPoint = Q.genericPoint)
    (hQ : Q.genericPoint ∈ biregularLocus fp) : (Em - Ep) E = 0 := by
  haveI := isIso_stalkMap_of_map_eq_genericPoint q hu Pm huE
  haveI := isIso_stalkMap_of_map_eq_genericPoint p hv P hvE
  rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor E Pm huE hD.isQCartier_minus hEm,
    coeff_eq_of_isPullback_qDivisor E P hvE hD.isQCartier_plus hEp, Finsupp.add_apply,
    Finsupp.add_apply, flipTransform_apply_eq hfm Pm P Q hmQ hpQ hQ,
    ← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply (Divisor.toQDivisor _),
    Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_apply,
    DivisorWithCoeffs.coeff_apply, flipTransform_apply_eq hfm Pm P Q hmQ hpQ hQ, sub_self]

/-- **The comparison divisor of one step pushes forward to zero**: `p_*(q^* D⁻ - p^* D⁺) = 0`. -/
private theorem transformDivisor_sub_eq_zero
    {Xm Xp Z W : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hD : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    {q : W ⟶ Xm} {p : W ⟶ Xp} (hqb : IsBirationalMorphism q) (hpb : IsBirationalMorphism p)
    (hcomp : q ≫ fm = p ≫ fp) {Em Ep : QDivisor W}
    {hm : ∀ T : irreducibleComponents W,
      q (componentGenericPoint W T) ∉ (Divisor.toQDivisor K + B).supp}
    {hp' : ∀ T : irreducibleComponents W, p (componentGenericPoint W T) ∉
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).supp}
    (hEm : (Divisor.toQDivisor K + B).IsPullback q hm Em)
    (hEp : (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).IsPullback p hp'
      Ep) :
    RationalMap.transformDivisor p.toRationalMap (Em - Ep) = 0 := by
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z :=
    haveI := hZ.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hD.isBirationalMorphism_minus.isDominant
  haveI := hqb.isDominant
  haveI := hpb.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm hD.isProjectiveMorphism_minus
  have hfm := hD.isBirationalMorphism_minus.functionFieldMap_bijective
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
  have hc : ∀ x : W, fm (q x) = fp (p x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
  refine Finsupp.ext fun P => ?_
  rw [Finsupp.zero_apply, RationalMap.transformDivisor]
  refine mapPrimeDivisors_apply_eq_zero (Em - Ep) fun E hE => ?_
  have hvE := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p E P).mp hE
  obtain ⟨Pm, Q, -, hQm, hQp, hQ, -, -⟩ := hD.exists_primeDivisor_valuationOver_eq P
  have hmQ := map_genericPoint_eq_of_image_eq fm Pm Q hQm
  have hpQ := map_genericPoint_eq_of_image_eq fp P Q hQp
  exact apply_sub_eq_zero hD hfm hqb.functionFieldMap_bijective
    hpb.functionFieldMap_bijective hEm hEp E Pm P Q
    (eq_of_map_eq_genericPoint fm hfm Q (by rw [hc, hvE, hpQ]) hmQ) hvE hmQ hpQ hQ.2

end Pushforward

/-! ### Relative nefness of the comparison divisor of one step -/

section Nef

/-- Pull-back commutes with negation. -/
private theorem isPullback_neg {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : QDivisor Y}
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} (h : B.IsPullback f hB B')
    (hBn : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (-B).supp) :
    (-B).IsPullback f hBn (-B') := by
  intro m hm D hD hDc
  have hD2 : Divisor.toQDivisor (-D) = (m : ℤ) • B := by rw [map_neg, hD, smul_neg, neg_neg]
  obtain ⟨D', hD', hp⟩ := h m hm (-D) hD2 hDc.neg
  refine ⟨-D', by rw [map_neg, hD', smul_neg], ?_⟩
  have hsupp : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ ((-1 : ℤ) • -D).supp :=
    fun Z hZ => hBn Z (by
      rwa [neg_one_smul, neg_neg, ← Divisor.supp_toQDivisor, hD,
        QDivisor.supp_zsmul (by exact_mod_cast hm.ne')] at hZ)
  have := hp.zsmul hDc.neg (-1) hsupp
  rw [show (-1 : ℤ) • D' = -D' from neg_one_smul ℤ D'] at this
  exact Divisor.IsPullback.of_eq (by rw [neg_one_smul, neg_neg]) this

/-- **The projection formula for a pulled-back `ℚ`-divisor.** If `A'` is the pull-back of `A` along
`f : W ⟶ Y` and `L = mA` is a Cartier divisor, then `m (A' · C)` is the degree of `𝒪_Y(L)` on the
push-forward `f_*[C]`. -/
private theorem intersectionNumber_mul_eq_degree_cyclePushforwardOfPoint {W Y : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (sW : W ⟶ Spec (.of ℂ)) [QuasiCompact sW]
    (sY : Y ⟶ Spec (.of ℂ)) [IsSeparated sY] [LocallyOfFiniteType sY] (f : W ⟶ Y) (hf : f ≫ sY = sW)
    {A : QDivisor Y}
    {hA : ∀ Z : irreducibleComponents W, f (componentGenericPoint W Z) ∉ A.supp}
    {A' : QDivisor W} (h : A.IsPullback f hA A') (hA'q : A'.IsQCartier) {m : ℕ} (hm : 0 < m)
    (L : Divisor Y) (hL : L.IsCartier) (hLA : Divisor.toQDivisor L = (m : ℤ) • A)
    (C : ProperCurve sW) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    ((A'.intersectionNumber ℂ sW C.ι C.dim_le hA'q : ℚ) : ℝ) * m =
      OneCycle.degree ℝ sY L.divisorialSheaf (cyclePushforwardOfPoint ℝ sY f C.point) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  obtain ⟨D', hD', hp⟩ := h m hm L hLA hL
  have hD'c := hp.isCartier hL
  haveI := hD'c.isInvertibleModule_divisorialSheaf
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sW C.ι C.dim_le A' hA'q hm D' hD'c hD',
    C.degree_pushforward_eq_degree_pullback f hf, ProperCurve.degree, Divisor.degreeOn,
    degreeOn_eq_of_iso ℂ sW C.ι C.dim_le (hp.divisorialSheafIso (hBc := hL))]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/-- A curve contracted by `f` pushes forward to `0`. -/
private theorem cyclePushforwardOfPoint_eq_zero_of_isContractedBy {W Y : Scheme.{0}}
    {sW : W ⟶ Spec (.of ℂ)} (sY : Y ⟶ Spec (.of ℂ)) [IsSeparated sY] [LocallyOfFiniteType sY]
    (f : W ⟶ Y) (hf : f ≫ sY = sW) (C : ProperCurve sW) (hC : C.IsContractedBy f) :
    cyclePushforwardOfPoint ℝ sY f C.point = 0 := by
  rw [cyclePushforwardOfPoint, dif_neg]
  intro h
  have hr : ∀ t, curveSubschemeAtι (f C.point) t = f C.point := fun t => by
    have ht : curveSubschemeAtι (f C.point) t ∈ closure {f C.point} :=
      range_curveSubschemeAtι (f C.point) ▸ ⟨t, rfl⟩
    rw [← C.range_comp f hf] at ht
    obtain ⟨c, hc⟩ := ht
    rw [← hc, Scheme.Hom.comp_apply]
    exact hC (C.ι c) (by rw [← C.range_ι]; exact ⟨c, rfl⟩)
  have : Subsingleton (curveSubschemeAt (f C.point)) :=
    ⟨fun a b => (curveSubschemeAtι (f C.point)).isEmbedding.injective ((hr a).trans (hr b).symm)⟩
  have h0 : topologicalKrullDim (curveSubschemeAt (f C.point)) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  rw [h.dim_eq] at h0
  norm_num at h0

/-- An invertible sheaf `L` ample over `Z` has nonnegative degree on the push-forward along `q` of
a curve whose image in `Z` is a point. -/
private theorem degree_cyclePushforwardOfPoint_nonneg {W X Z : Scheme.{0}}
    {sW : W ⟶ Spec (.of ℂ)} (sX : X ⟶ Spec (.of ℂ)) [IsSeparated sX] [LocallyOfFiniteType sX]
    (q : W ⟶ X) (hq : q ≫ sX = sW) (fm : X ⟶ Z) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hamp : MMP.Mori.IsRelativelyAmple fm L) (C : ProperCurve sW)
    (hC : C.IsContractedBy (q ≫ fm)) :
    0 ≤ OneCycle.degree ℝ sX L (cyclePushforwardOfPoint ℝ sX q C.point) := by
  rw [cyclePushforwardOfPoint]
  split_ifs with h
  · rw [OneCycle.degree_apply, Finsupp.sum_single_index (by simp)]
    refine mul_nonneg (by positivity) ?_
    have hC' : ProperCurve.IsContractedBy ⟨q C.point, h⟩ fm := by
      intro x hx
      change x ∈ closure {q C.point} at hx
      rw [← C.range_comp q hq] at hx
      obtain ⟨c, rfl⟩ := hx
      simpa only [Scheme.Hom.comp_apply] using hC (C.ι c) (by rw [← C.range_ι]; exact ⟨c, rfl⟩)
    exact_mod_cast (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
      fm L hamp _ hC').le
  · simp

end Nef

/-- **Relative nefness of the comparison divisor of one step.** For a threefold step diagram
`(X⁻, B⁻) → Z ← (X⁺, B⁺)` and morphisms `q : W ⟶ X⁻`, `p : W ⟶ X⁺` with `f⁻ ∘ q = f⁺ ∘ p`, the
divisor `-(q^* D⁻ - p^* D⁺)` is `p`-nef. -/
private theorem isRelativelyNef_neg_sub
    {Xm Xp Z W : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hD : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (sW : W ⟶ Spec (.of ℂ)) [QuasiCompact sW] (q : W ⟶ Xm) (p : W ⟶ Xp) (hq : q ≫ sXm = sW)
    (hp : p ≫ sXp = sW) (hcomp : q ≫ fm = p ≫ fp) {Em Ep : QDivisor W}
    {hm : ∀ T : irreducibleComponents W,
      q (componentGenericPoint W T) ∉ (Divisor.toQDivisor K + B).supp}
    {hp' : ∀ T : irreducibleComponents W, p (componentGenericPoint W T) ∉
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).supp}
    (hEm : (Divisor.toQDivisor K + B).IsPullback q hm Em)
    (hEp : (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).IsPullback p hp'
      Ep) :
    (-(Em - Ep)).IsRelativelyNef sW p := by
  haveI := hD.isNormalVariety_plus.1.toIsSeparated
  haveI := hD.isNormalVariety_plus.1.toLocallyOfFiniteType
  haveI := hD.isNormalVariety_minus.1.toIsSeparated
  haveI := hD.isNormalVariety_minus.1.toLocallyOfFiniteType
  obtain ⟨m₁, hm₁, L₁, hL₁c, hL₁, hL₁a⟩ := hD.hasRelativelyAmpleMultiple_minus
  obtain ⟨m₂, hm₂, L₂, hL₂c, hL₂, -⟩ := hD.hasRelativelyAmpleMultiple_plus
  haveI := hL₁c.isInvertibleModule_divisorialSheaf
  have hEpq := hEp.isQCartier hD.isQCartier_plus
  have hnEm := isPullback_neg hEm (fun T hT => hm T (by rwa [DivisorWithCoeffs.supp_neg] at hT))
  have hnEmq := hnEm.isQCartier ⟨m₁, by exact_mod_cast hm₁.ne', L₁, hL₁, hL₁c⟩
  have hsum := hEpq.add hnEmq
  have e : -(Em - Ep) = Ep + -Em := by abel
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sW (e ▸ hsum) fun C hC => ?_
  rw [intersectionNumber_congr sW C.ι C.dim_le _ hsum e,
    QDivisor.intersectionNumber_add' ℂ sW C.ι C.dim_le _ _ hEpq hnEmq]
  have h1 := intersectionNumber_mul_eq_degree_cyclePushforwardOfPoint sW sXp p hp hEp hEpq hm₂
    L₂ hL₂c hL₂ C
  rw [cyclePushforwardOfPoint_eq_zero_of_isContractedBy sXp p hp C hC, map_zero] at h1
  have h2 := degree_cyclePushforwardOfPoint_nonneg sXm q hq fm L₁.divisorialSheaf hL₁a C
    fun x hx => by rw [hcomp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  rw [← intersectionNumber_mul_eq_degree_cyclePushforwardOfPoint sW sXm q hq hnEm hnEmq hm₁
    L₁ hL₁c hL₁ C] at h2
  have hm₂' : (m₂ : ℝ) ≠ 0 := by exact_mod_cast hm₂.ne'
  rw [mul_eq_zero, or_iff_left hm₂', Rat.cast_eq_zero] at h1
  rw [h1, zero_add]
  exact_mod_cast (mul_nonneg_iff_of_pos_right (by positivity)).mp h2

/-- **One threefold step.** For a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` and birational
morphisms `q : W ⟶ X⁻`, `p : W ⟶ X⁺` from a projective normal variety with `f⁻ ∘ q = f⁺ ∘ p`,
`q^* D⁻ - p^* D⁺ ≥ 0`. -/
private theorem nonneg_sub_of_isThreefoldStepDiagram
    {Xm Xp Z W : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hD : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (sW : W ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWn : IsNormalVariety ℂ sW) (q : W ⟶ Xm) (p : W ⟶ Xp) (hq : q ≫ sXm = sW)
    (hp : p ≫ sXp = sW) (hqb : IsBirationalMorphism q) (hpb : IsBirationalMorphism p)
    (hcomp : q ≫ fm = p ≫ fp) {Em Ep : QDivisor W}
    {hm : ∀ T : irreducibleComponents W,
      q (componentGenericPoint W T) ∉ (Divisor.toQDivisor K + B).supp}
    {hp' : ∀ T : irreducibleComponents W, p (componentGenericPoint W T) ∉
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).supp}
    (hEm : (Divisor.toQDivisor K + B).IsPullback q hm Em)
    (hEp : (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).IsPullback p hp'
      Ep) :
    0 ≤ Em - Ep := by
  haveI := hW.toIsVariety.toQuasiCompact
  haveI : IsProper sW := isProper_of_isProjectiveMorphism sW hW.isProjective
  haveI := hD.isNormalVariety_plus.1.toIsSeparated
  haveI : IsProper (p ≫ sXp) := hp ▸ inferInstance
  haveI : IsProper p := IsProper.of_comp p sXp
  have hnef := isRelativelyNef_neg_sub hD sW q p hq hp hcomp hEm hEp
  have heff : (RationalMap.transformDivisor (X := W) p.toRationalMap (Em - Ep)).IsEffective := by
    rw [transformDivisor_sub_eq_zero hD hqb hpb hcomp hEm hEp]
    exact DivisorWithCoeffs.isEffective_zero
  exact DivisorWithCoeffs.isEffective_iff_nonneg.mp
    (QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg ℂ sXp sW
      hD.isNormalVariety_plus hWn p hp hpb
      (Proof_lem_mmp_indexc_graph_h_effective.isQCartier_of_isQCartier_neg hnef.1) hnef heff)

/-- A birational morphism of integral schemes maps the generic point of every component of the
source off the support of every divisor of the target. -/
private theorem map_componentGenericPoint_notMem_supp {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) (hf : IsBirationalMorphism f) {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R Y) (T : irreducibleComponents X) :
    f (componentGenericPoint X T) ∉ D.supp := by
  haveI := hf.isDominant
  rw [componentGenericPoint_eq_genericPoint, MMP.Positivity.map_genericPoint_eq_of_isDominant]
  exact genericPoint_notMem_supp D

/-- `B'` is a pull-back of `B₂` along `f` if it is one of `B₁` and `B₁ = B₂`. -/
private theorem isPullback_of_eq_left {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B₁ B₂ : QDivisor Y}
    (e : B₁ = B₂) {hB₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₂.supp}
    {B' : QDivisor X} (h : B₁.IsPullback f hB₁ B') : B₂.IsPullback f hB₂ B' := by
  subst e
  exact h

end Proof_lem_mmp_indexc_finite_program_comparison

namespace MMP.Fourfold

open Proof_lem_mmp_indexc_finite_program_comparison

open MMP.Mori

/-- **The comparison divisor of a finite chain of threefold steps is effective.** For threefold
step diagrams `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `k < m`, with transported canonical
divisors `K_{k+1} = (g_k⁺)⁻¹_* (g_k)_* K_k` and boundaries `Θ_{k+1} = (g_k⁺)⁻¹_* (g_k)_* Θ_k`, and
birational morphisms `q_k : W ⟶ V_k`, `k ≤ m`, over `ℂ` from a smooth projective variety `W` with
`q_k ≫ g_k = q_{k+1} ≫ g_k⁺`, the `ℚ`-divisor `q_0^*(K_0 + Θ_0) - q_m^*(K_m + Θ_m)` is
effective. -/
@[mmp "lem_mmp_indexc_finite_program_comparison"]
public theorem pullback_sub_pullback_nonneg_of_isThreefoldStepDiagram (m : ℕ)
    {V : ℕ → Scheme.{0}} (sV : ∀ k, V k ⟶ Spec (.of ℂ)) [∀ k, IsIntegral (V k)]
    [∀ k, CompactSpace (V k)] [∀ k, IsLocallyNoetherian (V k)] [∀ k, IsNormal (V k)]
    (K : ∀ k, Divisor (V k)) (Θ : ∀ k, QDivisor (V k))
    {T : ℕ → Scheme.{0}} (sT : ∀ k, T k ⟶ Spec (.of ℂ))
    (g : ∀ k, V k ⟶ T k) (gp : ∀ k, V (k + 1) ⟶ T k)
    (hstep : ∀ k < m,
      IsThreefoldStepDiagram (sV k) (sT k) (sV (k + 1)) (K k) (Θ k) (g k) (gp k))
    (hK : ∀ k < m, K (k + 1) = flipTransform (g k) (gp k) (K k))
    (hΘ : ∀ k < m, Θ (k + 1) = flipTransform (g k) (gp k) (Θ k))
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (sW : W ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWn : IsNormalVariety ℂ sW) (hWs : IsSmoothScheme sW)
    (q : ∀ k, W ⟶ V k) (hqs : ∀ k ≤ m, q k ≫ sV k = sW)
    (hq : ∀ k ≤ m, IsBirationalMorphism (q k))
    (hcomp : ∀ k < m, q k ≫ g k = q (k + 1) ≫ gp k)
    (hD₀ : (Divisor.toQDivisor (K 0) + Θ 0).IsQCartier)
    (hDₘ : (Divisor.toQDivisor (K m) + Θ m).IsQCartier)
    (h₀ : ∀ Z : irreducibleComponents W,
      q 0 (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K 0) + Θ 0).supp)
    (hₘ : ∀ Z : irreducibleComponents W,
      q m (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K m) + Θ m).supp) :
    0 ≤ (Divisor.toQDivisor (K 0) + Θ 0).pullback hD₀ h₀ -
      (Divisor.toQDivisor (K m) + Θ m).pullback hDₘ hₘ := by
  have key : ∀ j ≤ m, ∀ (hj : (Divisor.toQDivisor (K j) + Θ j).IsQCartier)
      (hgj : ∀ Z : irreducibleComponents W,
        q j (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K j) + Θ j).supp),
      0 ≤ (Divisor.toQDivisor (K 0) + Θ 0).pullback hD₀ h₀ -
        (Divisor.toQDivisor (K j) + Θ j).pullback hj hgj := by
    intro j
    induction j with
    | zero =>
      intro _ _ _
      simp
    | succ j ih =>
      intro hj1 hj hgj
      have hjm : j < m := hj1
      have hS := hstep j hjm
      have hgj' : ∀ Z : irreducibleComponents W,
          q j (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K j) + Θ j).supp :=
        map_componentGenericPoint_notMem_supp (q j) (hq j hjm.le) _
      have h2 := nonneg_sub_of_isThreefoldStepDiagram hS sW hW hWn (q j) (q (j + 1))
        (hqs j hjm.le) (hqs (j + 1) hj1) (hq j hjm.le) (hq (j + 1) hj1) (hcomp j hjm)
        (QDivisor.isPullback_pullback hS.isQCartier_minus hgj')
        (isPullback_of_eq_left (by rw [hK j hjm, hΘ j hjm])
          (QDivisor.isPullback_pullback hj hgj)
          (hB₂ := map_componentGenericPoint_notMem_supp (q (j + 1)) (hq (j + 1) hj1) _))
      simpa only [sub_add_sub_cancel] using add_nonneg (ih hjm.le hS.isQCartier_minus hgj') h2
  exact key m le_rfl hDₘ hₘ

end MMP.Fourfold

end
