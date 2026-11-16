module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Fourfold singularities: canonical boundaries, lc complements and reduced snc pairs

This file collects five results on singularities of pairs used for fourfolds.

*Sections above a canonical boundary.* Let `g : T ⟶ S` be a projective birational morphism of
smooth varieties over a field `k`, `(S, Ω)` a canonical pair, `Ψ_T ≥ 0` a `ℚ`-divisor on `T` and
`Ψ = g_* Ψ_T ≤ Ω`. If `m(K_S + Ψ)` and `m(K_T + Ψ_T)` are integral Cartier divisors, then pulling
back rational `m`-canonical forms along `g^* : k(S) ≅ k(T)` identifies
`H⁰(S, 𝒪_S(m(K_S + Ψ)))` with `H⁰(T, 𝒪_T(m(K_T + Ψ_T)))`. Along a non-exceptional prime `E` of
`T`, `g` is an isomorphism of local rings, so orders and coefficients agree; along an
exceptional `E`, the canonical condition `a(E, S, Ω) ≥ 1` and algebraic Hartogs at the centre
give `ord_E(g^*τ) ≥ 0`, while `Ψ_T ≥ 0`.

*Transport of an lc complement.* Let `(X, B)` and `(M, B_M)` be lc pairs, projective over `Z`,
with a common resolution `p : W ⟶ X`, `q : W ⟶ M` over `Z` on which
`p^*(K_X + B) = q^*(K_M + B_M) + F`, `F ≥ 0` `q`-exceptional. If `A ≥ 0` is `ℚ`-Cartier with
`(X, B + A)` lc and `K_X + B + A ∼_ℚ f^*H`, then `A_M = q_* p^* A` is effective `ℚ`-Cartier,
`K_M + B_M + A_M ∼_ℚ g^*H` with the same rational function, `q^*(K_M + B_M + A_M) =
p^*(K_X + B + A)`, `q^*A_M = p^*A + F`, `(M, B_M + A_M)` is lc (crepant invariance of log
discrepancies along `p` and `q`), and `A_M` has order zero along every lc place of `(M, B_M)`.

*Reduced snc pairs.* On a smooth variety `W` over an algebraically closed field of
characteristic zero with a reduced snc divisor `T`, every log discrepancy `a(F, W, T)` is a
nonnegative integer: integral because `K_W + T` is Cartier, nonnegative by the snc formula for
discrepancies. Consequently the reduced snc discrepancy `e_T(ξ)` of a divisorial valuation `ξ`
is a nonnegative integer, and if the centre of `ξ` has codimension `c` and lies on the components
`J(ξ)` of `T`, then `e_T(ξ) ≥ c - |J(ξ)|`: in a regular system of parameters at the centre
containing the local equations of the components of `T`, a wedge of logarithmic forms has at
most a simple pole along the divisor realizing `ξ`.

## Main results

* `MMP.Fourfold.bijOn_pullbackRationalPluriForms_logPluricanonicalSections`: the pull-back
  `MMP.Mori.pullbackRationalPluriForms` is a bijection between the two spaces
  `MMP.Fourfold.logPluricanonicalSections`.
* `MMP.Fourfold.IsLogComparisonResolution.transport_lcComplement`: transport of an effective lc
  complement along a common resolution.
* `MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC`: `a(F, W, T) ∈ ℤ_{≥ 0}`.
* `MMP.Fourfold.IsReducedSNCDiscrepancy.exists_eq_natCast`: `e_T(ξ) ∈ ℤ_{≥ 0}`.
* `MMP.Fourfold.IsReducedSNCDiscrepancy.sub_card_sncIndexSet_le`: `c - |J(ξ)| ≤ e_T(ξ)`.

## Implementation notes

* Spaces of sections are spaces of rational `m`-canonical forms, so the identification of
  sections above a canonical boundary is the pull-back of forms, with compatible canonical
  divisors built in. Smoothness of `S` and `T` replaces perfectness of `k`: it gives local
  generators of the top forms, makes every divisor Cartier and every canonical divisor the
  divisor of a rational top form.
* The common resolution is `MMP.Fourfold.IsLogComparisonResolution` applied to rational
  boundaries regarded as real ones; its comparison divisor `G_X - G_Y` is `F`. Pull-backs are
  `MMP.Flips.IsRCartierPullback`, and "`q^*D' = p^*D`" says every pull-back of `D` along `p` is
  one of `D'` along `q`. `D ∼_ℚ f^*H` reads `n • D = n • f^*H + div(u)` with `n > 0`.
* The reduced snc discrepancy is the relation `MMP.Fourfold.IsReducedSNCDiscrepancy`, which
  records that `W` is smooth, `T` reduced snc and that `ξ` has a centre. The source writes
  `e_T(ξ)` as `a(ξ; W', ∑_{J(ξ)} Tⱼ + ∑_ℓ L_ℓ) + ∑_ℓ ξ(t_ℓ)`; the codimension bound here runs the
  same comparison directly at the centre, without introducing the divisors `L_ℓ`.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 2.31
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold

/-! ## Sections of adjoint divisors above a canonical boundary -/

section CanonicalBoundary

open MMP MMP.Mori

/-! ### Pull-back of forms along a birational morphism of smooth varieties -/

section PullbackGenerator

variable {k : Type u} [Field k] {S T : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (g : T ⟶ S)
  [IsIntegral S] [IsIntegral T] [IsDominant g]

/-- On a smooth integral `k`-scheme of dimension `n`, `Ω_{k(S)/k}` is finite-dimensional of
rank `n`. -/
private theorem finrank_kaehler_functionField [Smooth sS] {n : ℕ}
    (hn : topologicalKrullDim S = n) :
    letI := functionFieldAlgebra sS
    FiniteDimensional S.functionField Ω[S.functionField⁄k] ∧
      Module.finrank S.functionField Ω[S.functionField⁄k] = n := by
  let := functionFieldAlgebra sS
  obtain ⟨n', ⟨b⟩, hn'⟩ := MMP.Threefold.Resolution.exists_basis_kaehler_stalk sS (genericPoint S)
  have hnd : n' = n := by
    have := (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k S sS
      (genericPoint S)).trans hn'
    rw [hn] at this
    exact_mod_cast this.symm
  exact ⟨Module.Finite.of_basis b, by rw [Module.finrank_eq_card_basis b, Fintype.card_fin, hnd]⟩

/-- Along a birational morphism to a smooth variety of dimension `n`, `Ω^n_{k(S)/k}` has a
generator pulling back to a generator of `Ω^n_{k(T)/k}`. -/
private theorem exists_isPullbackGenerator [Smooth sS]
    (hbij : Function.Bijective (functionFieldMap g)) {n : ℕ} (hn : topologicalKrullDim S = n) :
    letI := functionFieldAlgebra sS
    letI := functionFieldAlgebra (g ≫ sS)
    letI := functionFieldMapAlgebra g
    haveI := isScalarTower_functionFieldMap sS g
    ∃ ω : ⋀[S.functionField]^n Ω[S.functionField⁄k], IsPullbackGenerator T.functionField ω := by
  let := functionFieldAlgebra sS
  let := functionFieldAlgebra (g ≫ sS)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sS g
  have : Algebra.FormallyEtale S.functionField T.functionField :=
    Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId S.functionField T.functionField) hbij)
  obtain ⟨_, h⟩ := finrank_kaehler_functionField sS hn
  exact exists_isPullbackGenerator_of_formallyEtale h

/-- The pull-back of rational `m`-canonical forms along a birational morphism to a smooth
variety of dimension `n` is bijective. -/
private theorem pullbackRationalPluriForms_bijective [Smooth sS]
    (hbij : Function.Bijective (functionFieldMap g)) {n : ℕ} (hn : topologicalKrullDim S = n)
    (m : ℤ) : Function.Bijective (pullbackRationalPluriForms sS g (d := n) (m := m)) := by
  let := functionFieldAlgebra sS
  let := functionFieldAlgebra (g ≫ sS)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sS g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator sS g hbij hn
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  have hpb : ∀ τ : RationalPluriForms sS n m, pullbackRationalPluriForms sS g τ =
      functionFieldMap g (b.repr τ ()) • b' () := fun τ =>
    pullbackForms_eq (K' := T.functionField) hω m τ
  refine ⟨fun τ₁ τ₂ h => ?_, fun τ' => ?_⟩
  · rw [hpb, hpb] at h
    have h1 := congrArg (fun x => b'.repr x ()) h
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] at h1
    rw [← basis_unit_repr_smul b τ₁, ← basis_unit_repr_smul b τ₂, hbij.1 h1]
  · obtain ⟨c, hc⟩ := hbij.2 (b'.repr τ' ())
    refine ⟨(c • b () : PluriForms k S.functionField n m), (hpb _).trans ?_⟩
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    rw [hc]
    exact basis_unit_repr_smul b' τ'

/-- **The order of a pulled-back form along a strict transform**, for a birational morphism to a
smooth variety: if `g(η_E) = η_P` and `g^♯ : 𝒪_{S,P} ⟶ 𝒪_{T,E}` is an isomorphism, then
`ord_E(g^*τ) = ord_P(τ)`. -/
private theorem ordForm_pullback_of_isIso [IsLocallyNoetherian S] [IsNormal S]
    [IsLocallyNoetherian T] [IsNormal T] [Smooth sS]
    (hbij : Function.Bijective (functionFieldMap g)) {n : ℕ} (hn : topologicalKrullDim S = n)
    (E : Mori.PrimeDivisor T) (P : Mori.PrimeDivisor S) (heq : g E.genericPoint = P.genericPoint)
    [IsIso (g.stalkMap E.genericPoint)] {m : ℤ} (τ : RationalPluriForms sS n m) :
    E.ordForm (pullbackRationalPluriForms sS g τ) = P.ordForm τ := by
  let := functionFieldAlgebra sS
  let := functionFieldAlgebra (g ≫ sS)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sS g
  let := stalkAlgebra sS P.genericPoint
  have := isScalarTower_stalk_functionField sS P.genericPoint
  let := stalkAlgebra (g ≫ sS) E.genericPoint
  have := isScalarTower_stalk_functionField (g ≫ sS) E.genericPoint
  have hsp : g E.genericPoint ⤳ P.genericPoint := heq ▸ specializes_rfl
  let φ : S.presheaf.stalk P.genericPoint ⟶ T.presheaf.stalk E.genericPoint :=
    S.presheaf.stalkSpecializes hsp ≫ g.stalkMap E.genericPoint
  have : IsIso (S.presheaf.stalkSpecializes hsp) := by
    rw [show S.presheaf.stalkSpecializes hsp =
      (S.presheaf.stalkCongr (Inseparable.of_eq heq)).inv from rfl]
    infer_instance
  have hφ : IsIso φ := by infer_instance
  let : Algebra P.localRing E.localRing := φ.hom.toAlgebra
  let : Algebra P.localRing T.functionField :=
    ((algebraMap S.functionField T.functionField).comp
      (algebraMap P.localRing S.functionField)).toAlgebra
  have : IsScalarTower P.localRing S.functionField T.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hφK : ∀ r : P.localRing, algebraMap P.localRing T.functionField r =
      algebraMap E.localRing T.functionField (φ.hom r) := fun r => by
    change functionFieldMap g _ = algebraMap _ T.functionField ((g.stalkMap E.genericPoint).hom
        ((S.presheaf.stalkSpecializes hsp).hom r))
    rw [← functionFieldMap_algebraMap_stalk, algebraMap_stalkSpecializes]
  have : IsScalarTower P.localRing E.localRing T.functionField :=
    IsScalarTower.of_algebraMap_eq hφK
  have : IsScalarTower k P.localRing E.localRing := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ sS).appTop ≫
          T.presheaf.germ ⊤ E.genericPoint (TopologicalSpace.Opens.mem_top _) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sS.appTop ≫
          S.presheaf.germ ⊤ P.genericPoint (TopologicalSpace.Opens.mem_top _)) ≫ φ := by
      simp only [φ, Scheme.Hom.comp_appTop, Category.assoc,
        TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
      rfl
    exact congrArg CommRingCat.Hom.hom h
  have : IsScalarTower k P.localRing T.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [IsScalarTower.algebraMap_apply k S.functionField T.functionField,
      IsScalarTower.algebraMap_apply k P.localRing S.functionField]
    rfl
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨σ, hσ, h0⟩ :=
    MMP.Threefold.Resolution.exists_topForms_generator_stalk sS hn P.genericPoint
  have hspan : Submodule.span S.functionField {topFormsMap k P.localRing S.functionField n σ} =
      ⊤ := span_singleton_topFormsMap (nonZeroDivisors P.localRing) hσ
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator sS g hbij hn
  have hgen := MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω hspan h0
  have hbijA : Function.Bijective (algebraMap P.localRing E.localRing) :=
    (ConcreteCategory.isIso_iff_bijective φ).mp hφ
  exact MMP.Threefold.Mori.Helpers.ordAt_pullbackForms_eq (k := k) hbijA
    P.ord_mul_of_ne_zero (fun _ ha => P.ord_algebraMap_of_isUnit ha)
    E.ord_mul_of_ne_zero (fun _ ha => E.ord_algebraMap_of_isUnit ha)
    (fun x => MMP.Positivity.ord_functionFieldMap_of_isIso g E P heq x) hσ hgen τ

/-- **Orders of pulled-back forms at a prime divisor.** For a birational morphism `g : T ⟶ S` of
smooth varieties of dimension `n` and a prime divisor `E ⊆ T` with centre `x = g(η_E)`, write
rational `m`-canonical forms on `S` as `τ = c(τ) σ^{⊗m}` for a generator `σ` of the top forms at
`x`. There is an integer `N` (the order along `E` of the Jacobian of `g` with respect to
generators at `x` and at `η_E`) with `ord_E(g^*τ) = v_E(g^*c(τ)) + mN`, while
`ord_Γ(τ) = v_Γ(c(τ))` for every prime divisor `Γ` through `x`. -/
private theorem exists_ordForm_pullback_eq [Smooth sS] [Smooth (g ≫ sS)]
    [IsLocallyNoetherian S] [IsLocallyNoetherian T]
    (hbij : Function.Bijective (functionFieldMap g)) {n : ℕ} (hn : topologicalKrullDim S = n)
    (hnT : topologicalKrullDim T = n) (E : Mori.PrimeDivisor T) :
    ∃ (N : ℤ) (c : ∀ m : ℤ, RationalPluriForms sS n m → S.functionField),
      (∀ (m : ℤ) (τ : RationalPluriForms sS n m), τ ≠ 0 → c m τ ≠ 0) ∧
      (∀ (m : ℤ) (τ : RationalPluriForms sS n m), τ ≠ 0 →
        E.ordForm (pullbackRationalPluriForms sS g τ) =
          T.ord (functionFieldMap g (c m τ)) E.genericPoint + m * N) ∧
      (∀ (m : ℤ) (τ : RationalPluriForms sS n m) (Γ : Mori.PrimeDivisor S),
        g E.genericPoint ∈ Γ.support → Γ.ordForm τ = S.ord (c m τ) Γ.genericPoint) := by
  let := functionFieldAlgebra sS
  let := functionFieldAlgebra (g ≫ sS)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sS g
  let := stalkAlgebra sS (g E.genericPoint)
  have := isScalarTower_stalk_functionField sS (g E.genericPoint)
  let := stalkAlgebra (g ≫ sS) E.genericPoint
  have := isScalarTower_stalk_functionField (g ≫ sS) E.genericPoint
  let := (g.stalkMap E.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sS g E.genericPoint
  obtain ⟨σA, hσA, h0A⟩ :=
    MMP.Threefold.Resolution.exists_topForms_generator_stalk sS hn (g E.genericPoint)
  obtain ⟨σB, hσB, h0B⟩ :=
    MMP.Threefold.Resolution.exists_topForms_generator_stalk (g ≫ sS) hnT E.genericPoint
  obtain ⟨h, hrel⟩ := Submodule.mem_span_singleton.mp
    (hσB ▸ Submodule.mem_top : topFormsMap k (S.presheaf.stalk (g E.genericPoint)) E.localRing n σA
      ∈ Submodule.span E.localRing {σB})
  -- the Jacobian `h` is nonzero
  let : Algebra (S.presheaf.stalk (g E.genericPoint)) T.functionField :=
    ((algebraMap S.functionField T.functionField).comp
      (algebraMap (S.presheaf.stalk (g E.genericPoint)) S.functionField)).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (g E.genericPoint)) S.functionField T.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (g E.genericPoint)) E.localRing T.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      functionFieldMap_algebraMap_stalk g E.genericPoint a
  have : IsScalarTower k (S.presheaf.stalk (g E.genericPoint)) T.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k S.functionField T.functionField,
        IsScalarTower.algebraMap_apply k (S.presheaf.stalk (g E.genericPoint)) S.functionField]
      rfl
  have hh : algebraMap E.localRing T.functionField h ≠ 0 := by
    intro h0
    have hz : h = 0 := IsFractionRing.injective E.localRing T.functionField (by rw [h0, map_zero])
    obtain ⟨ω, hω⟩ := exists_isPullbackGenerator sS g hbij hn
    have hspan : Submodule.span S.functionField
        {topFormsMap k (S.presheaf.stalk (g E.genericPoint)) S.functionField n σA} = ⊤ :=
      span_singleton_topFormsMap (nonZeroDivisors (S.presheaf.stalk (g E.genericPoint))) hσA
    have hgen := MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω hspan h0A
    apply hgen.2.2
    rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp, ← MMP.Threefold.Mori.Helpers.topFormsMap_comp
      (B := E.localRing), ← hrel, hz, zero_smul, map_zero]
  refine ⟨T.ord (algebraMap E.localRing T.functionField h) E.genericPoint,
    fun m τ => formCoeff (k := k) (S.presheaf.stalk (g E.genericPoint)) hσA h0A τ,
    fun m τ hτ h0 => hτ ((formCoeff_eq_zero_iff hσA h0A τ).mp h0),
    fun m τ hτ => ?_, fun m τ Γ hΓ => ?_⟩
  · exact MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq sS g E hσA h0A hσB h0B h
      hrel.symm hh hτ
  · exact MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sS (g E.genericPoint) Γ hΓ hσA h0A τ

end PullbackGenerator

/-! ### Membership in `H⁰(X, m(K_X + B))` -/

section Membership

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A rational `m`-canonical form lies in `H⁰(X, m(K_X + B))` if and only if
`ord_Γ(τ) + ⌊m b_Γ⌋ ≥ 0` along every prime divisor `Γ`, when `τ ≠ 0`. -/
private theorem mem_logPluricanonicalSections_iff {d m : ℕ} {B : QDivisor X}
    {τ : RationalPluriForms sX d m} :
    τ ∈ logPluricanonicalSections sX d m B ↔
      ∀ Γ : Mori.PrimeDivisor X, τ ≠ 0 → 0 ≤ Γ.ordForm τ + ⌊(m : ℚ) * B.coeff Γ⌋ := by
  have hU : (⊤ : X.Opens) ≠ ⊥ := fun h => by
    have := congrArg (fun U : X.Opens => genericPoint X ∈ U) h
    simp at this
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot hU]
  refine forall_congr' fun Γ => ?_
  have hΓ : (Γ.support ∩ (⊤ : X.Opens)).Nonempty :=
    (Γ.genericPoint_mem_iff ⊤).mp trivial
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast]
  exact ⟨fun h => h hΓ, fun h _ => h⟩

end Membership

private theorem pullbackRationalPluriForms_zero {k : Type u} [Field k] {S T : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) (g : T ⟶ S) [IsIntegral S] [IsIntegral T] [IsDominant g] {d : ℕ}
    {m : ℤ} : pullbackRationalPluriForms sS g (0 : RationalPluriForms sS d m) = 0 := by
  let := functionFieldAlgebra sS
  let := functionFieldAlgebra (g ≫ sS)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sS g
  have h := pullbackForms_add (k := k) (K := S.functionField) (K' := T.functionField) (d := d)
    (m := m) 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-! ### Strict transforms of prime divisors -/

section StrictTransform

variable {k : Type u} [Field k] {S T : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {g : T ⟶ S}
  [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsDominant g] [IsProper g]

/-- If `g(η_E) = η_P` for a proper birational morphism of normal varieties, then `g` induces an
isomorphism `𝒪_{S,P} ≅ 𝒪_{T,E}` and the coefficient of `P` in the push-forward of a divisor is
the coefficient of `E`. -/
private theorem isIso_and_transformDivisor_apply_of_genericPoint_eq
    (hS : IsNormalVariety k sS) (hT : IsNormalVariety k (g ≫ sS)) (hg : IsBirationalMorphism g)
    {E : Mori.PrimeDivisor T} {P : Mori.PrimeDivisor S} (heq : g E.genericPoint = P.genericPoint) :
    IsIso (g.stalkMap E.genericPoint) ∧ ∀ {R : Type*} [AddCommMonoid R]
      (D : DivisorWithCoeffs R T), RationalMap.transformDivisor (X := T) g.toRationalMap D P =
        D E := by
  have := hS.1
  have := hT.1
  have : IsSeparated g := IsSeparated.of_comp g sS
  have hbij := hg.functionFieldMap_bijective
  obtain ⟨E', heq', hiso', htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hS hT hg P
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (S.presheaf.stalk (g E'.genericPoint)) := by rw [heq']; infer_instance
  have : ValuationRing (S.presheaf.stalk (g E.genericPoint)) := by rw [heq]; infer_instance
  have hiso := MMP.Positivity.isIso_stalkMap_of_valuationRing g hbij E.genericPoint
  have hEE : E' = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.eq_of_isIso_stalkMap g hbij (heq.trans heq'.symm))
  subst hEE
  exact ⟨hiso, htr⟩

end StrictTransform

/-! ### Orders of pulled-back rational functions at a centre -/

section Local

variable {S T : Scheme.{u}} (g : T ⟶ S) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsDominant g]

/-- If a rational function `u` has nonnegative order along every prime divisor through
`g(η_E)`, then `g^*u` has nonnegative order along `E` (algebraic Hartogs). -/
private theorem ord_functionFieldMap_nonneg (E : Mori.PrimeDivisor T) {u : S.functionField}
    (hu : u ≠ 0)
    (h : ∀ Γ : Mori.PrimeDivisor S, g E.genericPoint ∈ Γ.support → 0 ≤ S.ord u Γ.genericPoint) :
    0 ≤ T.ord (functionFieldMap g u) E.genericPoint := by
  obtain ⟨r, hr⟩ :=
    MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hu h
  have hne : functionFieldMap g u ≠ 0 := (map_ne_zero _).mpr hu
  have h1 : E.divisorialValuation (functionFieldMap g u) ≤ 1 := by
    rw [E.divisorialValuation_le_one_iff]
    refine ⟨(g.stalkMap E.genericPoint).hom r, ?_⟩
    rw [← hr, functionFieldMap_algebraMap_stalk]
  rw [E.divisorialValuation_eq_exp_neg_ord hne, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

/-- Two rational functions with the same orders along the prime divisors through `g(η_E)` pull
back to functions with the same order along `E`. -/
private theorem ord_functionFieldMap_eq (E : Mori.PrimeDivisor T) {u u' : S.functionField}
    (hu : u ≠ 0) (hu' : u' ≠ 0)
    (h : ∀ Γ : Mori.PrimeDivisor S, g E.genericPoint ∈ Γ.support →
      S.ord u Γ.genericPoint = S.ord u' Γ.genericPoint) :
    T.ord (functionFieldMap g u) E.genericPoint = T.ord (functionFieldMap g u') E.genericPoint := by
  have key : ∀ a b : S.functionField, a ≠ 0 → b ≠ 0 →
      (∀ Γ : Mori.PrimeDivisor S, g E.genericPoint ∈ Γ.support →
        S.ord a Γ.genericPoint = S.ord b Γ.genericPoint) →
      T.ord (functionFieldMap g b) E.genericPoint ≤
        T.ord (functionFieldMap g a) E.genericPoint := by
    intro a b ha hb hab
    have hab' : a * b⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hb)
    have h0 := ord_functionFieldMap_nonneg g E hab' fun Γ hΓ => by
      rw [Scheme.ord_mul ha (inv_ne_zero hb), ← zpow_neg_one, MMP.Mori.ord_zpow _ hb, hab Γ hΓ]
      omega
    have hgb : functionFieldMap g b ≠ 0 := (map_ne_zero _).mpr hb
    rw [map_mul, map_inv₀, Scheme.ord_mul ((map_ne_zero _).mpr ha) (inv_ne_zero hgb),
      ← zpow_neg_one, MMP.Mori.ord_zpow _ hgb] at h0
    omega
  exact le_antisymm (key u' u hu' hu fun Γ hΓ => (h Γ hΓ).symm) (key u u' hu hu' h)

/-- A local equation `φ` of a divisor `B` on `U ∋ x` has, along every prime divisor through `x`,
the order prescribed by `B`. -/
private theorem ord_evalFF_eq_coeff {B : Divisor S} {U : S.Opens} {φ : (RationalFunctions S)ˣ}
    (hφ : B.IsLocalEquation U φ) {x : S} (hxU : x ∈ U) (Γ : Mori.PrimeDivisor S)
    (hΓ : x ∈ Γ.support) :
    S.ord (MMP.Threefold.Mori.Helpers.evalFF (pointComponent x) (φ : RationalFunctions S))
      Γ.genericPoint = B.coeff Γ := by
  have e2 := hφ Γ ⟨x, hΓ, hxU⟩
  rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at e2
  have hZ : Γ.component = pointComponent x := Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := S)) _ _
  rw [hZ] at e2
  exact e2.symm

/-- A Cartier divisor has, at each point `x`, a rational function whose orders along the prime
divisors through `x` are its coefficients. -/
private theorem exists_ord_eq_coeff {B : Divisor S} (hB : B.IsCartier) (x : S) :
    ∃ r : S.functionField, r ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor S, x ∈ Γ.support → S.ord r Γ.genericPoint = B.coeff Γ := by
  obtain ⟨U, hxU, φ, hφ⟩ := hB x
  exact ⟨_, (φ.isUnit.map _).ne_zero, ord_evalFF_eq_coeff hφ hxU⟩

/-- **The coefficient of a pull-back.** If `r` has, along the prime divisors through `g(η_E)`,
the orders prescribed by a Cartier divisor `B`, then the coefficient of `E` in `g^*B` is the
order of `g^*r` along `E`. -/
private theorem coeff_isPullback_eq_ord {B : Divisor S} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents T, g (componentGenericPoint T Z) ∉ B.supp}
    {B' : Divisor T} (h : B.IsPullback g hB B') (E : Mori.PrimeDivisor T) {r : S.functionField}
    (hr : r ≠ 0) (hrB : ∀ Γ : Mori.PrimeDivisor S, g E.genericPoint ∈ Γ.support →
      S.ord r Γ.genericPoint = B.coeff Γ) :
    B'.coeff E = T.ord (functionFieldMap g r) E.genericPoint := by
  obtain ⟨U, hxU, φ, hφ⟩ := hBc (g E.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ E hxU
    (pointComponent (g E.genericPoint))]
  exact ord_functionFieldMap_eq g E (φ.isUnit.map _).ne_zero hr fun Γ hΓ => by
    rw [ord_evalFF_eq_coeff hφ hxU Γ hΓ, hrB Γ hΓ]

end Local

/-- Sums over the enumeration `Fin s.card ≃ s` of a finite set are sums over `s`. -/
private theorem sum_equivFin {α M : Type*} [AddCommMonoid M] (s : Finset α) (F : α → M) :
    ∑ j : Fin s.card, F (s.equivFin.symm j) = ∑ p ∈ s, F p := by
  rw [← Finset.sum_coe_sort s F]
  exact Equiv.sum_comp s.equivFin.symm (fun p : s => F p)

/-- The final inequality of the exceptional case: if `q_j ≤ m w_j`, `e_j ≥ 0`,
`∑ w_j e_j ≤ N` and `v + ∑ q_j e_j ≥ 0`, then `v + m N ≥ 0`. -/
private theorem add_mul_nonneg_of_le_mul {ι : Type*} [Fintype ι] {v N : ℤ} {m : ℕ}
    {w : ι → ℝ} {q e : ι → ℤ} (hq : ∀ j, (q j : ℝ) ≤ m * w j) (he : ∀ j, 0 ≤ e j)
    (hN : ∑ j, w j * e j ≤ N) (hv : 0 ≤ v + ∑ j, q j * e j) : 0 ≤ v + m * N := by
  have h1 : ∑ j, (q j : ℝ) * e j ≤ m * N :=
    calc ∑ j, (q j : ℝ) * e j ≤ ∑ j, (m : ℝ) * w j * e j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hq j) (by exact_mod_cast he j)
      _ = m * ∑ j, w j * e j := by simp only [Finset.mul_sum, mul_assoc]
      _ ≤ m * N := mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg _)
  have h2 : (0 : ℝ) ≤ v + ∑ j, (q j : ℝ) * e j := by exact_mod_cast hv
  exact_mod_cast (by linarith : (0 : ℝ) ≤ v + m * N)

/-- **Sections do not acquire poles along exceptional divisors.** Let `g : T ⟶ S` be a proper
birational morphism of smooth varieties of dimension `n`, `(S, Ω)` a real canonical pair and
`Ψ ≤ Ω`. If `E ⊆ T` is a prime divisor whose centre `g(η_E)` is not the generic point of a prime
divisor, then `ord_E(g^*τ) ≥ 0` for every nonzero `τ ∈ H⁰(S, m(K_S + Ψ))`.

Writing `τ = c σ^{⊗m}` near the centre `x`, with Jacobian order `N` of `g` along `E`, the log
discrepancy of `E` for `(S, Ω)` is `1 + N - coeff_E(g^*Ω)`, which is at least `1` since `E` is
exceptional; and `c ∏ φ_P^{⌊m ψ_P⌋}` is regular at `x` (Hartogs), for local equations `φ_P` of
the components `P` of `Ω`, so `v_E(g^*c) ≥ -∑ ⌊m ψ_P⌋ coeff_E(g^*P) ≥ -m coeff_E(g^*Ω)`. -/
private theorem ordForm_pullback_nonneg_of_forall_ne
    {k : Type u} [Field k] {S T : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (g : T ⟶ S)
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsDominant g] [IsProper g]
    [Smooth sS] [Smooth (g ≫ sS)]
    (hS : Mori.IsVariety k sS) (hT : Mori.IsVariety k (g ≫ sS)) (hg : IsBirationalMorphism g)
    {n m : ℕ} {KS : Divisor S} (hKS : KS.IsCanonicalDivisor sS n)
    (hdT : topologicalKrullDim T = n) {Ω : QDivisor S}
    (hcan : IsRealCanonicalPair sS (QDivisor.toRDivisor Ω)) {Ψ : QDivisor S} (hΨΩ : Ψ ≤ Ω)
    (E : Mori.PrimeDivisor T) (hE : ∀ P : Mori.PrimeDivisor S, g E.genericPoint ≠ P.genericPoint)
    {τ : RationalPluriForms sS n m} (hτ : τ ∈ logPluricanonicalSections sS n m Ψ)
    (hτ0 : τ ≠ 0) : 0 ≤ E.ordForm (pullbackRationalPluriForms sS g τ) := by
  classical
  have hdS : topologicalKrullDim S = n := hKS.topologicalKrullDim_eq
  have : CompactSpace S := by
    have := hS
    exact QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace T := by
    have := hT
    exact QuasiCompact.compactSpace_of_compactSpace (g ≫ sS)
  have hSn : IsNormalVariety k sS := ⟨hS, inferInstance⟩
  have hTn : IsNormalVariety k (g ≫ sS) := ⟨hT, inferInstance⟩
  have hbij := hg.functionFieldMap_bijective
  have hsmS : IsSmoothScheme sS := (isSmoothScheme_iff sS).mpr inferInstance
  -- `E` is exceptional over `S`
  set D : DivisorOver k sS := ⟨T, g, hTn, hg, E⟩ with hD
  have hDex : D.IsExceptional := by
    by_contra hne
    obtain ⟨P, hv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hSn D hne
    exact hE P (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hS hv)
  -- the canonical divisor `K_S = div ω`
  have hsm : ∀ Γ : Mori.PrimeDivisor S, Γ.genericPoint ∈ smoothLocus sS := fun Γ => by
    rw [show smoothLocus sS = ⊤ from hsmS]
    trivial
  obtain ⟨ω, hω0, hωK⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hSn hsm hKS
  -- `K_S + Ω = K_S + ∑ ω_P P` as a combination of Cartier divisors, and its pull-back
  set s := Ω.support with hs
  set P : Fin s.card → Mori.PrimeDivisor S := fun j => (s.equivFin.symm j).1 with hP
  let C : Fin (s.card + 1) → Divisor S := Fin.cons KS fun j => Finsupp.single (P j) 1
  let r : Fin (s.card + 1) → ℝ := Fin.cons 1 fun j => ((Ω.coeff (P j) : ℚ) : ℝ)
  have hCc : ∀ i, (C i).IsCartier := fun i => MMP.Fourfold.isCartier_of_isSmoothScheme hsmS _
  have hB : ∀ i, ∀ Z : irreducibleComponents T, g (componentGenericPoint T Z) ∉ (C i).supp :=
    fun i => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g (C i)
  choose C' hC' using fun i => (hCc i).exists_isPullback (hB i)
  have hlog : MMP.Intersection.IsLogDiscrepancy sS n (QDivisor.toRDivisor Ω) D
      (1 + (D.ordPullback ω : ℝ) - ∑ i, r i * (C' i).coeff D.E) := by
    refine ⟨hSn, (inferInstance : IsProper g), ω, hω0, ⟨KS, hKS, fun Γ => (hωK Γ).symm⟩,
      s.card + 1, r, C, C', hCc, fun Γ => ?_, fun i => ⟨hB i, hC' i⟩, rfl⟩
    rw [Fin.sum_univ_succ]
    simp only [r, C, Fin.cons_zero, Fin.cons_succ, one_mul, hωK]
    congr 1
    change ((Ω Γ : ℚ) : ℝ) = _
    rw [sum_equivFin s (fun p => ((Ω.coeff p : ℚ) : ℝ) *
      ((DivisorWithCoeffs.coeff (X := S) (Finsupp.single p (1 : ℤ)) Γ : ℤ) : ℝ))]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    rw [Finset.sum_eq_single Γ]
    · by_cases hΓ : Γ ∈ s
      · simp
      · simp [Finsupp.notMem_support_iff.mp hΓ]
    · intro b _ hb
      simp [hb]
    · intro hΓ
      simp [Finsupp.notMem_support_iff.mp hΓ]
  have h1 := hcan.2.2.2 n D _ hDex hlog
  -- the local computation at the centre
  obtain ⟨N, c, hc0, hord, hordΓ⟩ := exists_ordForm_pullback_eq sS g hbij hdS hdT E
  have hC'0 : (C' 0).coeff E = T.ord (functionFieldMap g (c 1 ω)) E.genericPoint :=
    coeff_isPullback_eq_ord g (hCc 0) (hC' 0) E (hc0 1 ω hω0)
      fun Γ hΓ => (hordΓ 1 ω Γ hΓ).symm.trans (hωK Γ)
  have hωE : D.ordPullback ω = T.ord (functionFieldMap g (c 1 ω)) E.genericPoint + N := by
    rw [← one_mul N]
    exact hord 1 ω hω0
  choose ρ hρ0 hρ using fun j : Fin s.card =>
    exists_ord_eq_coeff (hCc j.succ) (g E.genericPoint)
  have hρΓ : ∀ j Γ, g E.genericPoint ∈ Γ.support →
      S.ord (ρ j) Γ.genericPoint = if P j = Γ then 1 else 0 := fun j Γ hΓ => by
    rw [hρ j Γ hΓ]
    simp [C, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
  set e : Fin s.card → ℤ := fun j => T.ord (functionFieldMap g (ρ j)) E.genericPoint with he
  have hC'j : ∀ j, (C' j.succ).coeff E = e j := fun j =>
    coeff_isPullback_eq_ord g (hCc j.succ) (hC' j.succ) E (hρ0 j) (hρ j)
  have he0 : ∀ j, 0 ≤ e j := fun j =>
    ord_functionFieldMap_nonneg g E (hρ0 j) fun Γ hΓ => by
      rw [hρΓ j Γ hΓ]
      split_ifs <;> omega
  -- `coeff_E(g^*Ω) ≤ N`
  have hN : ∑ j, ((Ω.coeff (P j) : ℚ) : ℝ) * (e j : ℝ) ≤ N := by
    rw [Fin.sum_univ_succ] at h1
    simp only [r, Fin.cons_zero, Fin.cons_succ, one_mul, show D.E = E from rfl, hC'j] at h1
    change 1 ≤ 1 + ((D.ordPullback ω : ℤ) : ℝ) - ((C' 0).coeff E + _) at h1
    rw [hωE, hC'0] at h1
    push_cast at h1
    linarith
  -- the function `u = c ∏ ρ_j^{⌊m ψ_j⌋}` is regular at the centre
  set q : Fin s.card → ℤ := fun j => ⌊(m : ℚ) * Ψ.coeff (P j)⌋ with hq
  have hcτ := hc0 m τ hτ0
  have hprod0 : (∏ j, ρ j ^ q j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hρ0 j)
  have hu := ord_functionFieldMap_nonneg g E (mul_ne_zero hcτ hprod0) fun Γ hΓ => by
    rw [Scheme.ord_mul hcτ hprod0,
      MMP.Threefold.Bridges.ord_prod_zpow _ _ _ hρ0, ← hordΓ m τ Γ hΓ]
    have hsum : ∑ j, q j * S.ord (ρ j) Γ.genericPoint =
        if Γ ∈ s then ⌊(m : ℚ) * Ψ.coeff Γ⌋ else 0 := by
      rw [Finset.sum_congr rfl fun j _ => by rw [hρΓ j Γ hΓ]]
      rw [sum_equivFin s (fun p => ⌊(m : ℚ) * Ψ.coeff p⌋ * if p = Γ then 1 else 0)]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
    have hmem := (mem_logPluricanonicalSections_iff sS).1 hτ Γ hτ0
    rw [hsum]
    split_ifs with hΓs
    · omega
    · have hΩΓ : Ω.coeff Γ = 0 := Finsupp.notMem_support_iff.mp hΓs
      have hΨΓ : Ψ.coeff Γ ≤ 0 := hΩΓ ▸ hΨΩ Γ
      have : ⌊(m : ℚ) * Ψ.coeff Γ⌋ ≤ 0 :=
        Int.floor_nonpos (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hΨΓ)
      omega
  simp only [map_mul, map_prod, map_zpow₀] at hu
  rw [Scheme.ord_mul ((map_ne_zero _).mpr hcτ) (Finset.prod_ne_zero_iff.mpr fun j _ =>
      zpow_ne_zero _ ((map_ne_zero _).mpr (hρ0 j))),
    MMP.Threefold.Bridges.ord_prod_zpow _ _ _ (fun j => (map_ne_zero _).mpr (hρ0 j))] at hu
  rw [hord m τ hτ0]
  exact add_mul_nonneg_of_le_mul (fun j => by
    exact_mod_cast (Int.floor_le _).trans (mul_le_mul_of_nonneg_left (hΨΩ (P j))
      (Nat.cast_nonneg _))) he0 hN hu

/-- **Sections above a canonical boundary.** Let `g : T ⟶ S` be a projective birational morphism
of smooth varieties of dimension `n` over `k` (with `T` structured over `k` by `g ≫ s_S`), let `Ω`
be an effective `ℚ`-divisor on `S` with `(S, Ω)` a real canonical pair
(`MMP.Fourfold.IsRealCanonicalPair`), and let `Ψ_T ≥ 0` be a `ℚ`-divisor on `T` with
`Ψ = g_* Ψ_T ≤ Ω` (`MMP.Mori.RationalMap.transformDivisor`). If `m(K_S + Ψ)` and `m(K_T + Ψ_T)`
are integral Cartier divisors for canonical divisors `K_S`, `K_T`, then the pull-back of rational
`m`-canonical forms along `g` is a bijection
`H⁰(S, 𝒪_S(m(K_S + Ψ))) → H⁰(T, 𝒪_T(m(K_T + Ψ_T)))`. -/
@[mmp "lem_fourfold_canonical_boundary_section_comparison"]
public theorem bijOn_pullbackRationalPluriForms_logPluricanonicalSections
    {k : Type u} [Field k] {S T : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (g : T ⟶ S)
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsDominant g]
    [Smooth sS] [Smooth (g ≫ sS)]
    (hS : Mori.IsVariety k sS) (hT : Mori.IsVariety k (g ≫ sS)) (hg : IsBirationalMorphism g)
    (hgp : IsProjectiveMorphism g)
    (n m : ℕ) (Ω : QDivisor S) (hΩ : 0 ≤ Ω)
    (hcan : IsRealCanonicalPair sS (QDivisor.toRDivisor Ω))
    (ΨT : QDivisor T) (hΨT : 0 ≤ ΨT) (Ψ : QDivisor S)
    (hΨ : RationalMap.transformDivisor (X := T) g.toRationalMap ΨT = Ψ) (hΨΩ : Ψ ≤ Ω)
    (hmS : ∃ K : Divisor S, K.IsCanonicalDivisor sS n ∧
      ((m : ℤ) • (Divisor.toQDivisor K + Ψ)).IsCartierDivisor)
    (hmT : ∃ K : Divisor T, K.IsCanonicalDivisor (g ≫ sS) n ∧
      ((m : ℤ) • (Divisor.toQDivisor K + ΨT)).IsCartierDivisor) :
    Set.BijOn (pullbackRationalPluriForms sS g (d := n) (m := m))
      (logPluricanonicalSections sS n m Ψ) (logPluricanonicalSections (g ≫ sS) n m ΨT) := by
  classical
  obtain ⟨KS, hKS, -⟩ := hmS
  obtain ⟨KT, hKT, -⟩ := hmT
  have hdS : topologicalKrullDim S = n := hKS.topologicalKrullDim_eq
  have hdT : topologicalKrullDim T = n := hKT.topologicalKrullDim_eq
  have hbij := hg.functionFieldMap_bijective
  have : IsProper g := isProper_of_isProjectiveMorphism g hgp
  have hSn : IsNormalVariety k sS := ⟨hS, inferInstance⟩
  have hTn : IsNormalVariety k (g ≫ sS) := ⟨hT, inferInstance⟩
  have hbijF := pullbackRationalPluriForms_bijective sS g hbij hdS m
  refine ⟨fun τ hτ => ?_, hbijF.1.injOn, fun τ' hτ' => ?_⟩
  · rw [SetLike.mem_coe, mem_logPluricanonicalSections_iff]
    intro E hτ'0
    have hτ0 : τ ≠ 0 := fun h => hτ'0 (by rw [h, pullbackRationalPluriForms_zero])
    by_cases hP : ∃ P : Mori.PrimeDivisor S, g E.genericPoint = P.genericPoint
    · obtain ⟨P, heq⟩ := hP
      obtain ⟨hiso, htr⟩ := isIso_and_transformDivisor_apply_of_genericPoint_eq hSn hTn hg heq
      rw [ordForm_pullback_of_isIso sS g hbij hdS E P heq τ]
      have hc : ΨT.coeff E = Ψ.coeff P := by
        rw [← hΨ]
        exact (htr ΨT).symm
      rw [hc]
      exact (mem_logPluricanonicalSections_iff sS).1 hτ P hτ0
    · push Not at hP
      have h0 := ordForm_pullback_nonneg_of_forall_ne sS g hS hT hg hKS hdT hcan hΨΩ E hP hτ hτ0
      have h1 : 0 ≤ ⌊(m : ℚ) * ΨT.coeff E⌋ :=
        Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (hΨT E))
      omega
  · obtain ⟨τ, rfl⟩ := hbijF.2 τ'
    refine ⟨τ, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_logPluricanonicalSections_iff]
    intro P hτ0
    obtain ⟨E, heq, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hSn hTn hg P
    have h := (mem_logPluricanonicalSections_iff (g ≫ sS)).1 hτ' E
      (fun h => hτ0 (hbijF.1 (h.trans (pullbackRationalPluriForms_zero sS g).symm)))
    rw [ordForm_pullback_of_isIso sS g hbij hdS E P heq τ] at h
    have hc : Ψ.coeff P = ΨT.coeff E := by
      rw [← hΨ]
      exact htr ΨT
    rw [hc]
    exact h

end CanonicalBoundary

/-! ## Transport of an effective lc complement to a nef model -/

section LCComplement

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open TopologicalSpace TensorProduct MMP.Mori MMP.Flips
open scoped WithZero

/-! ### Linearity, uniqueness and functoriality of pull-backs of `ℝ`-Cartier divisors -/

section PullbackAlgebra

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

private theorem isRCartierPullback_sub {f : Y ⟶ X} {D D' : RDivisor X} {G G' : RDivisor Y}
    (h : IsRCartierPullback f D G) (h' : IsRCartierPullback f D' G') :
    IsRCartierPullback f (D - D') (G - G') := by
  have := isRCartierPullback_add h (isRCartierPullback_smul (-1) h')
  simpa only [neg_one_smul, ← sub_eq_add_neg] using this

/-- The Cartier divisors whose support avoids the images of the generic points of `Y`. -/
private def avoidingCartierSubgroup (f : Y ⟶ X) : AddSubgroup (Divisor X) where
  carrier := {L | L.IsCartier ∧ ∀ Z : irreducibleComponents Y,
    f (componentGenericPoint Y Z) ∉ L.supp}
  zero_mem' := ⟨Divisor.isCartier_zero, fun Z => by
    rw [DivisorWithCoeffs.supp_zero]; exact id⟩
  add_mem' {L₁ L₂} h₁ h₂ := ⟨h₁.1.add h₂.1, fun Z hZ => by
    rcases DivisorWithCoeffs.supp_add_le L₁ L₂ hZ with h | h
    exacts [h₁.2 Z h, h₂.2 Z h]⟩
  neg_mem' {L} h := ⟨h.1.neg, fun Z hZ => by
    rw [DivisorWithCoeffs.supp_neg] at hZ; exact h.2 Z hZ⟩

/-- Pull-back along `f` on the Cartier divisors avoiding the generic points of `Y`. -/
private noncomputable def avoidingPullbackHom [CompactSpace Y] (f : Y ⟶ X) :
    avoidingCartierSubgroup f →+ Divisor Y where
  toFun L := (L : Divisor X).pullback L.2.1 L.2.2
  map_zero' := Divisor.IsPullback.pullback_eq Divisor.isCartier_zero (Divisor.isPullback_zero _)
  map_add' L₁ L₂ := Divisor.IsPullback.pullback_eq (L₁ + L₂).2.1
    (Divisor.IsPullback.add L₁.2.1 L₂.2.1 _ (Divisor.isPullback_pullback _ _)
      (Divisor.isPullback_pullback _ _))

/-- **Uniqueness of the pull-back of an `ℝ`-Cartier divisor**, for any morphism (not necessarily
dominant): two presentations of `D` by Cartier divisors avoiding the generic points of `Y` agree
in `Ca(X)_f ⊗ ℝ`, which embeds in `Div(X) ⊗ ℝ`. -/
private theorem isRCartierPullback_eq [CompactSpace Y] {f : Y ⟶ X} {D : RDivisor X}
    {G₁ G₂ : RDivisor Y} (h₁ : IsRCartierPullback f D G₁) (h₂ : IsRCartierPullback f D G₂) :
    G₁ = G₂ := by
  have hinj : Function.Injective (rDivisorTensorMap (avoidingCartierSubgroup f).subtype) :=
    (Divisor.tensorEquiv ℝ X).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have key : ∀ {G : RDivisor Y}, IsRCartierPullback f D G →
      ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → avoidingCartierSubgroup f),
        D = ∑ j, r j • Divisor.toRDivisor (L j : Divisor X) ∧
        G = rDivisorTensorMap (avoidingPullbackHom f) (∑ j, L j ⊗ₜ[ℤ] r j) := by
    intro G hG
    obtain ⟨m, r, L, L', hL, rfl, hL', rfl⟩ := hG
    refine ⟨m, r, fun j => ⟨L j, hL j, (hL' j).1⟩, rfl, ?_⟩
    simp only [map_sum, rDivisorTensorMap_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨hB, hp⟩ := hL' j
    change _ = r j • Divisor.toRDivisor ((L j).pullback (hL j) hB)
    rw [Divisor.IsPullback.pullback_eq (hL j) hp]
  obtain ⟨m, r, L, hD₁, rfl⟩ := key h₁
  obtain ⟨p, s, M, hD₂, rfl⟩ := key h₂
  have : ∑ j, (L j ⊗ₜ[ℤ] r j) = ∑ k, (M k ⊗ₜ[ℤ] s k) := by
    apply hinj
    simp only [map_sum, rDivisorTensorMap_tmul, AddSubgroup.coe_subtype]
    exact hD₁.symm.trans hD₂
  rw [this]

variable {Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian Z] [IsNormal Z]

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _)
    (mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

omit [IsIntegral X] [IsLocallyNoetherian Z] [IsNormal Z] in
private theorem isPullback_of_hom_eq {f f' : Y ⟶ X}
    (hff : f = f') {L : Divisor X} {L' : Divisor Y}
    {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    (hB' : ∀ W : irreducibleComponents Y, f' (componentGenericPoint Y W) ∉ L.supp)
    (h : L.IsPullback f hB L') : L.IsPullback f' hB' L' := by
  subst hff
  exact h

end PullbackAlgebra

/-! ### Strict transforms -/

section StrictTransform

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The image of a prime divisor under a proper morphism sending its generic point to the
generic point of a prime divisor `P` is the support of `P`. -/
private theorem image_support_eq_of_map_genericPoint (q : X ⟶ Y) [IsProper q]
    (E : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor Y)
    (h : q E.genericPoint = P.genericPoint) :
    q '' E.support = closure {P.genericPoint} := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
  apply le_antisymm
  · refine (image_closure_subset_closure_image q.continuous).trans ?_
    rw [Set.image_singleton, h]
  · have hc : IsClosed (q '' closure {E.genericPoint}) := q.isClosedMap _ isClosed_closure
    refine closure_minimal ?_ hc
    rw [Set.singleton_subset_iff, ← h]
    exact Set.mem_image_of_mem _ (subset_closure rfl)

/-- A strict transform is not exceptional. -/
private theorem not_isExceptionalPrimeDivisor_of_map_genericPoint {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {nY : ℕ}
    (hdim : topologicalKrullDim Y = nY) (q : X ⟶ Y) [IsProper q] (FW : MMP.Mori.PrimeDivisor X)
    (F : MMP.Mori.PrimeDivisor Y) (hFWeq : q FW.genericPoint = F.genericPoint) :
    ¬ IsExceptionalPrimeDivisor sY q FW := by
  intro hex
  obtain ⟨hY', hf', hp', hexc⟩ := hex
  change topologicalKrullDim (q '' FW.support : Set Y) + 2 ≤ topologicalKrullDim Y at hexc
  rw [image_support_eq_of_map_genericPoint q FW F hFWeq] at hexc
  have h1 : topologicalKrullDim (closure {F.genericPoint} : Set Y) + 1 = topologicalKrullDim Y := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY F.genericPoint
    rw [F.coheight_genericPoint] at h
    exact_mod_cast h
  rw [hdim] at h1 hexc
  generalize topologicalKrullDim (closure {F.genericPoint} : Set Y) = d at h1 hexc
  induction d using WithBot.recBotCoe with
  | bot => simp at h1
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this] at h1
      exact ENat.top_ne_natCast nY (WithBot.coe_injective h1)
    | coe d =>
      have h1' : ((d + 1 : ℕ) : WithBot ℕ∞) = ((nY : ℕ) : WithBot ℕ∞) := by
        rw [← h1]; rfl
      have h2' : ((d + 2 : ℕ) : WithBot ℕ∞) ≤ ((nY : ℕ) : WithBot ℕ∞) := by
        refine le_of_eq_of_le ?_ hexc; rfl
      have e1 : d + 1 = nY := by exact_mod_cast h1'
      have e2 : d + 2 ≤ nY := by exact_mod_cast h2'
      omega

end StrictTransform

/-! ### Pull-backs of effective Cartier divisors -/

section Effective

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
private theorem ord_algebraMap_stalk_nonneg (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk E.genericPoint)
    (hs : algebraMap _ Y.functionField s ≠ 0) :
    0 ≤ Y.ord (algebraMap _ Y.functionField s) E.genericPoint ∧
      (s ∈ IsLocalRing.maximalIdeal _ →
        0 < Y.ord (algebraMap _ Y.functionField s) E.genericPoint) := by
  have hv := E.divisorialValuation_eq_exp_neg_ord hs
  refine ⟨?_, fun hm => ?_⟩
  · have h1 : E.divisorialValuation (algebraMap _ Y.functionField s) ≤ 1 :=
      (E.divisorialValuation_le_one_iff _).mpr ⟨s, rfl⟩
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    linarith
  · have h1 := (E.divisorialValuation_algebraMap_lt_one_iff s).mpr hm
    rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    linarith

/-- **The pull-back of an effective Cartier divisor is effective**, and it has positive coefficient
along every prime divisor whose generic point maps into the support. -/
private theorem coeff_isPullback_nonneg {f : Y ⟶ X} [IsDominant f] {L : Divisor X}
    (hL : L.IsCartier) (hL0 : ∀ P, 0 ≤ L.coeff P)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp}
    {L' : Divisor Y} (h : L.IsPullback f hB L') (E : MMP.Mori.PrimeDivisor Y) :
    0 ≤ L'.coeff E ∧ (f E.genericPoint ∈ L.supp → 0 < L'.coeff E) := by
  set x := f E.genericPoint with hxdef
  obtain ⟨U, hU, φ, hφ⟩ := hL x
  set Z0 := pointComponent x
  have hx : x ∈ Z0.1 := mem_pointComponent x
  obtain ⟨r, hr⟩ := exists_stalk_eq_of_forall_zero_le_ord hx φ fun Γ hΓ => by
    rw [← hφ Γ ⟨x, hΓ, hU⟩]; exact hL0 Γ
  have hcoeff := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ E hU Z0
  have hev : MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) =
      algebraMap (X.presheaf.stalk x) X.functionField r := by
    change (X.presheaf.stalkSpecializes _).hom ((φ : RationalFunctions X) Z0) = _
    rw [← hr]
    change (stalkToRationalFunctions X hx ≫ X.presheaf.stalkSpecializes _).hom r = _
    rw [stalkToRationalFunctions, TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  have hne : MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) ≠ 0 :=
    (φ.isUnit.map _).ne_zero
  rw [hev] at hcoeff hne
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk f E.genericPoint r] at hcoeff
  have hne' : algebraMap _ Y.functionField ((f.stalkMap E.genericPoint).hom r) ≠ 0 := by
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk f E.genericPoint r]
    exact (map_ne_zero _).mpr hne
  obtain ⟨h0, hpos⟩ := ord_algebraMap_stalk_nonneg E _ hne'
  refine ⟨by rw [hcoeff]; exact_mod_cast h0, fun hxL => ?_⟩
  rw [hcoeff]
  refine hpos ?_
  -- `r` is not a unit of `𝒪_{X,x}`
  obtain ⟨Γ, hΓ0, hxΓ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxL
  have hΓpos : 0 < Γ.ord φ := by
    rw [← hφ Γ ⟨x, hxΓ, hU⟩]; exact lt_of_le_of_ne (hL0 Γ) (Ne.symm hΓ0)
  have hrm : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hru
    have hsp : Γ.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxΓ
      exact specializes_iff_mem_closure.mpr hxΓ
    have hZ : Γ.component = Z0 := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    have h1 := MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord Γ φ
    rw [hZ, hev, ← MMP.Mori.algebraMap_stalkSpecializes hsp,
      Γ.ord_algebraMap_of_isUnit (hru.map _)] at h1
    omega
  exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp hrm (isUnit_of_map_unit _ _ hu)

end Effective

/-! ### Pull-backs of `ℚ`-Cartier divisors along arbitrary morphisms -/

section QPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- If `mD = L` is Cartier with pull-back `L'`, then `(1/m) L'` is a pull-back of `D`. -/
private theorem isRCartierPullback_of_zsmul_eq' (f : Y ⟶ X) {D : QDivisor X} {m : ℕ}
    (hm : 0 < m) {L : Divisor X} (hL : L.IsCartier)
    (hmD : (m : ℤ) • D = Divisor.toQDivisor L) {L' : Divisor Y}
    (hL' : ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp,
      L.IsPullback f hB L') :
    IsRCartierPullback f (QDivisor.toRDivisor D) ((1 / (m : ℝ)) • Divisor.toRDivisor L') := by
  obtain ⟨hB, hp⟩ := hL'
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => L, fun _ => L', fun _ => hL, ?_, fun _ => ⟨hB, hp⟩,
    by rw [Fin.sum_univ_one]⟩
  rw [Fin.sum_univ_one]
  ext E
  have h := congrArg (fun G : QDivisor X => G.coeff E) hmD
  simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul,
    Int.cast_natCast] at h
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h' : ((D.coeff E : ℚ) : ℝ) * m = (L.coeff E : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at this
    linarith
  field_simp
  linarith

end QPullback

/-! ### Pull-backs of effective `ℚ`-Cartier divisors -/

section EffectiveQ

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] in
/-- A positive multiple of an effective `ℚ`-divisor is effective. -/
private theorem coeff_nonneg_of_toQDivisor_eq {A : QDivisor X} (hA0 : 0 ≤ A) {m : ℕ}
    {L : Divisor X} (hL : Divisor.toQDivisor L = (m : ℤ) • A) (P : MMP.Mori.PrimeDivisor X) :
    0 ≤ L.coeff P := by
  have h1 := congrArg (fun D : QDivisor X => D.coeff P) hL
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at h1
  have h2 : (0 : ℚ) ≤ (L.coeff P : ℚ) := by
    rw [h1]; exact mul_nonneg (by positivity) (Finsupp.le_def.mp hA0 P)
  exact_mod_cast h2

/-- A `ℚ`-Cartier divisor has an `ℝ`-Cartier pull-back along every dominant morphism. -/
private theorem exists_isRCartierPullback [CompactSpace Y] (f : Y ⟶ X) [IsDominant f]
    {A : QDivisor X}
    (hAq : A.IsQCartier) : ∃ G, IsRCartierPullback f (QDivisor.toRDivisor A) G := by
  obtain ⟨N, hN, L, hL, hLc⟩ := hAq.exists_pos
  exact ⟨_, isRCartierPullback_of_zsmul_eq' f hN hLc hL.symm
    ⟨_, Divisor.isPullback_pullback hLc
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f L)⟩⟩

/-- **The pull-back of an effective `ℚ`-Cartier divisor along a dominant morphism is effective**,
with positive coefficient along every prime divisor whose generic point maps into the support. -/
private theorem coeff_isRCartierPullback_nonneg [CompactSpace Y] {f : Y ⟶ X} [IsDominant f]
    {A : QDivisor X} (hA0 : 0 ≤ A) (hAq : A.IsQCartier) {G : RDivisor Y}
    (hG : IsRCartierPullback f (QDivisor.toRDivisor A) G) (E : MMP.Mori.PrimeDivisor Y) :
    0 ≤ G.coeff E ∧ (f E.genericPoint ∈ A.supp → 0 < G.coeff E) := by
  obtain ⟨N, hN, L, hL, hLc⟩ := hAq.exists_pos
  have hLp := Divisor.isPullback_pullback (f := f) hLc
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f L)
  rw [isRCartierPullback_eq hG (isRCartierPullback_of_zsmul_eq' f hN hLc hL.symm ⟨_, hLp⟩),
    DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul,
    ← QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hN.ne') hL]
  obtain ⟨h0, hpos⟩ := coeff_isPullback_nonneg hLc (coeff_nonneg_of_toQDivisor_eq hA0 hL) hLp E
  have hN' : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  exact ⟨mul_nonneg hN'.le (by exact_mod_cast h0),
    fun hx => mul_pos hN' (by exact_mod_cast hpos hx)⟩

end EffectiveQ

/-- Dividing `c • x = c • y + z` by `c ≠ 0`. -/
private theorem eq_add_one_div_smul_of_smul_eq {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] {c : K} (hc : c ≠ 0) {x y z : V} (h : c • x = c • y + z) : x = y + (1 / c) • z := by
  rw [← smul_right_inj hc, smul_add, smul_smul, mul_one_div_cancel hc, one_smul, h]

/-! ### Log discrepancies and discrepancies -/

section Discrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **Discrepancies and log discrepancies.** A discrepancy `b` of `E` over `(X, D)` computed
with a rational top form `ω` whose divisor is canonical gives the log discrepancy
`a(E, X, D) = 1 + b` (`MMP.Intersection.IsLogDiscrepancy`). -/
public theorem _root_.MMP.Flips.IsDiscrepancyWith.isLogDiscrepancy {n : ℕ} {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {b : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n D ω r L E b) :
    MMP.Intersection.IsLogDiscrepancy sX n D E.toDivisorOver (1 + b) := by
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω, ⟨divisorOfForm ω, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r,
    L, L', hLc, fun Γ => ?_, hpb, by ring⟩
  have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    coeff_sum_smul_toRDivisor] using this

/-- With a presentation of `div(ω) + D` by Cartier divisors, every divisor over `X` (with proper
model) has a discrepancy computed with these choices. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ b, IsDiscrepancyWith sX n D ω r L E b := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := E.isProper
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hX, hn, hω, hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-- **Adding an `ℝ`-Cartier divisor to the boundary shifts log discrepancies**: if `G = E.f^*D'`
then `a(E, X, D + D') = a(E, X, D) - coeff_E G`. -/
private theorem isLogDiscrepancy_add {n : ℕ} {D D' : RDivisor X} {E : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n D E a) :
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    ∀ G : RDivisor E.Y, IsRCartierPullback E.f D' G →
      MMP.Intersection.IsLogDiscrepancy sX n (D + D') E (a - G.coeff E.E) := by
  intro G hG
  obtain ⟨hX, hprop, ω, hω, hK, m, r, C, C', hCc, hsum, hpb, rfl⟩ := h
  obtain ⟨m', r', C₂, C₂', hC₂c, rfl, hpb₂, rfl⟩ := hG
  refine ⟨hX, hprop, ω, hω, hK, m + m', Fin.append r r', Fin.append C C₂, Fin.append C' C₂',
    Fin.addCases (by simpa using hCc) (by simpa using hC₂c), fun Γ => ?_,
    Fin.addCases (by simpa using hpb) (by simpa using hpb₂), ?_⟩
  · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, DivisorWithCoeffs.coeff_add,
      coeff_sum_smul_toRDivisor]
    linarith [hsum Γ]
  · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, coeff_sum_smul_toRDivisor]
    ring

end Discrepancy

/-! ### Changing the structure morphism -/

section Transport

variable {k : Type u} [Field k] {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]
  [IsNormal W] [CompactSpace W]

private theorem isDiscrepancy_of_eq {s s' : W ⟶ Spec (.of k)} (h : s = s')
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] {n : ℕ} {K : Divisor W} {D : RDivisor W}
    {v : Valuation W.functionField ℤᵐ⁰} {a : ℝ} (ha : MMP.Flips.IsDiscrepancy s n K D v a) :
    MMP.Flips.IsDiscrepancy s' n K D v a := by
  subst h
  exact ha

omit [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] in
private theorem exists_properDivisorOver_of_eq {s s' : W ⟶ Spec (.of k)} (h : s = s')
    (E : ProperDivisorOver k s) : ∃ E' : ProperDivisorOver k s', E'.valuation = E.valuation := by
  subst h
  exact ⟨E, rfl⟩

end Transport

/-! ### Lifting a divisor over `M` to a proper model `W ⟶ M` -/

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
    rw [← h]
    rfl
  let R := ξ.valuationSubring
  let φ : M.presheaf.stalk z →+* R :=
    ((functionFieldMap q).comp (algebraMap (M.presheaf.stalk z) M.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _)
  have hgen : genericPoint M ⤳ z := (genericPoint_spec M).specializes trivial
  have hex : ValuativeCriterion.Existence q := by
    have hp : @IsProper _ _ q := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1.existence
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
  haveI := hq.isDominant
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
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
    have h1 : eP.symm (functionFieldMap q s) = s := eP.symm_apply_apply s
    rw [h1, show functionFieldMap q s = eq s from rfl, RingEquiv.symm_apply_apply]
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

/-! ### Crepant invariance of log canonicity -/

section Crepant

variable {k : Type u} [Field k] [PerfectField k] {X M W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sM : M ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]
  [LocallyOfFiniteType sM] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- **Crepant invariance of log discrepancies along a common resolution.** Let `p : W ⟶ X` and
`q : W ⟶ M` be proper birational morphisms of normal varieties of dimension `n` over `k`, and let
`ω_X`, `ω_M` be nonzero rational top forms with canonical divisors whose pull-backs have the same
divisor `K_W`. If `p^*(K_X + D_X) = q^*(K_M + D_M)` and all log discrepancies of `(X, D_X)` are
nonnegative, then so are those of `(M, D_M)`. -/
public theorem logDiscrepancy_nonneg_of_isRCartierPullback_eq {p : W ⟶ X} {q : W ⟶ M} [IsProper p]
    [IsProper q] [IsDominant p] [IsDominant q] [LocallyOfFiniteType (p ≫ sX)]
    [LocallyOfFiniteType (q ≫ sM)]
    (hXn : IsNormalVariety k sX) (hMn : IsNormalVariety k sM)
    (hWnp : IsNormalVariety k (p ≫ sX)) (hWnq : IsNormalVariety k (q ≫ sM))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) (hss : q ≫ sM = p ≫ sX)
    {n : ℕ} (hdM : topologicalKrullDim M = n)
    {ωX : RationalPluriForms sX n 1} (hωX0 : ωX ≠ 0)
    (hKXc : (divisorOfForm ωX).IsCanonicalDivisor sX n)
    {ωM : RationalPluriForms sM n 1} (hωM0 : ωM ≠ 0)
    (hKMc : (divisorOfForm ωM).IsCanonicalDivisor sM n)
    {KW : Divisor W} (hKWp : KW.IsCanonicalDivisor (p ≫ sX) n)
    (hKWq : KW.IsCanonicalDivisor (q ≫ sM) n)
    (hωXW : divisorOfForm (pullbackRationalPluriForms sX p ωX) = KW)
    (hωMW : divisorOfForm (pullbackRationalPluriForms sM q ωM) = KW)
    {DX : RDivisor X} {DM : RDivisor M} {G : RDivisor W}
    (hGp : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) + DX) G)
    (hGq : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωM) + DM) G)
    (hlcX : ∀ (d : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX d DX E a → 0 ≤ a)
    (d : ℕ) (E : DivisorOver k sM) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sM d DM E a) : 0 ≤ a := by
  haveI := hWnq.1
  obtain rfl : d = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans hdM
  let EP : ProperDivisorOver k sM := ⟨E, ha.2.1⟩
  obtain ⟨mM, rM, LM, -, hLMc, hLMsum, -, -⟩ := id hGq
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith hMn hdM hωM0 hLMc hLMsum EP
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
    (hb.isLogDiscrepancy hKMc)]
  have hKDM : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωM) + DM) :=
    ⟨mM, rM, LM, hLMc, by rw [hLMsum]; simp only [toRDivisor_eq_mapCoeffs]⟩
  obtain ⟨E', hE'⟩ := exists_properDivisorOver_comap_eq q hqb EP
  have hDYq : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωM) + DM)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sM q ωM)) +
        (G - Divisor.toRDivisor KW)) := by
    rw [hωMW, add_sub_cancel]; exact hGq
  have h1 := (isDiscrepancy_comap_functionFieldMap_iff hMn hωM0 hKMc hKDM q hWnq hqb hDYq
    (by rw [hωMW]; exact hKWq) E' b).mp (by
      rw [hE']
      exact ⟨hKMc, hKDM, hasNonemptyCenter_valuation EP, EP, ωM, mM, rM, LM, rfl, rfl, hb⟩)
  rw [hωMW] at h1
  obtain ⟨E'', hE''⟩ := exists_properDivisorOver_of_eq hss E'
  obtain ⟨mX, rX, LX, -, hLXc, hLXsum, -, -⟩ := id hGp
  have hKDX : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωX) + DX) :=
    ⟨mX, rX, LX, hLXc, by rw [hLXsum]; simp only [toRDivisor_eq_mapCoeffs]⟩
  have hDYp : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) + DX)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX)) +
        (G - Divisor.toRDivisor KW)) := by
    rw [hωXW, add_sub_cancel]; exact hGp
  obtain ⟨-, -, -, E₀, ω₀, m₀, r₀, L₀, -, hdiv₀, hw₀⟩ :=
    (isDiscrepancy_comap_functionFieldMap_iff hXn hωX0 hKXc hKDX p hWnp hpb hDYp
      (by rw [hωXW]; exact hKWp) E'' b).mpr (by rw [hωXW, hE'']; exact isDiscrepancy_of_eq hss h1)
  exact hlcX _ E₀.toDivisorOver (1 + b)
    (hw₀.isLogDiscrepancy (by rw [hdiv₀]; exact hKXc))

/-- **Crepant invariance of log canonicity along a common resolution.** In the situation of
`MMP.Fourfold.logDiscrepancy_nonneg_of_isRCartierPullback_eq`, with `ℚ`-divisors `D_X`, `D_M`:
if `(X, D_X)` is log canonical, `(M, D_M)` is a pair and `D_M ≥ 0`, then `(M, D_M)` is log
canonical. -/
public theorem isLogCanonicalPair_of_isRCartierPullback_eq {p : W ⟶ X} {q : W ⟶ M} [IsProper p]
    [IsProper q] [IsDominant p] [IsDominant q] [LocallyOfFiniteType (p ≫ sX)]
    [LocallyOfFiniteType (q ≫ sM)]
    (hWnp : IsNormalVariety k (p ≫ sX)) (hWnq : IsNormalVariety k (q ≫ sM))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) (hss : q ≫ sM = p ≫ sX)
    {n : ℕ} (hdM : topologicalKrullDim M = n)
    {ωX : RationalPluriForms sX n 1} (hωX0 : ωX ≠ 0)
    (hKXc : (divisorOfForm ωX).IsCanonicalDivisor sX n)
    {ωM : RationalPluriForms sM n 1} (hωM0 : ωM ≠ 0)
    (hKMc : (divisorOfForm ωM).IsCanonicalDivisor sM n)
    {KW : Divisor W} (hKWp : KW.IsCanonicalDivisor (p ≫ sX) n)
    (hKWq : KW.IsCanonicalDivisor (q ≫ sM) n)
    (hωXW : divisorOfForm (pullbackRationalPluriForms sX p ωX) = KW)
    (hωMW : divisorOfForm (pullbackRationalPluriForms sM q ωM) = KW)
    {DX : QDivisor X} {DM : QDivisor M} {G : RDivisor W}
    (hGp : IsRCartierPullback p
      (Divisor.toRDivisor (divisorOfForm ωX) + QDivisor.toRDivisor DX) G)
    (hGq : IsRCartierPullback q
      (Divisor.toRDivisor (divisorOfForm ωM) + QDivisor.toRDivisor DM) G)
    (hlcX : MMP.Intersection.IsLogCanonicalPair sX DX) (hM : MMP.Mori.IsPair sM DM)
    (hDM : 0 ≤ DM) :
    MMP.Intersection.IsLogCanonicalPair sM DM :=
  ⟨hM, Finsupp.le_def.mp hDM, logDiscrepancy_nonneg_of_isRCartierPullback_eq hlcX.1.1 hM.1 hWnp
    hWnq hpb hqb hss hdM hωX0 hKXc hωM0 hKMc hKWp hKWq hωXW hωMW hGp hGq hlcX.2.2⟩

end Crepant

/-! ### The main result -/

/-- **Transport of an effective lc complement along a common resolution.** Let `(X, B)` and
`(M, B_M)` be lc pairs (`MMP.Intersection.IsLogCanonicalPair`), projective over a projective
variety `Z` by `f` and `g`, and let `p : W ⟶ X`, `q : W ⟶ M` with `p ≫ f = q ≫ g` be a common
resolution comparing the adjoints (`MMP.Fourfold.IsLogComparisonResolution`), so that
`p^*(K_X + B) = q^*(K_M + B_M) + F` with `F = G_X - G_Y ≥ 0` `q`-exceptional. Let `A ≥ 0` be
`ℚ`-Cartier with `(X, B + A)` lc and `n(K_X + B + A) = n f^*H + div(u)`, `n > 0`, for a
`ℚ`-Cartier `H` on `Z`. Then `A_M = q_* p^* A` is effective and `ℚ`-Cartier,
`n(K_M + B_M + A_M) = n g^*H + div(u_M)` with `q^*u_M = p^*u`,
`q^*(K_M + B_M + A_M) = p^*(K_X + B + A)`, `q^*A_M = p^*A + F`, `(M, B_M + A_M)` is lc, and every
lc place `E` of `(M, B_M)` has `ord_E A_M = 0` and centre not contained in `Supp A_M`. -/
@[mmp "lem_fourfold_lc_complement_transport"]
public theorem IsLogComparisonResolution.transport_lcComplement
    {k : Type u} [Field k] [PerfectField k] {X M Z W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sM : M ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
    [IsLocallyNoetherian Z] [IsNormal Z]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {f : X ⟶ Z} {g : M ⟶ Z} {B : QDivisor X} {BM : QDivisor M}
    {KX : Divisor X} {KM : Divisor M} {φ : X.RationalMap M}
    {p : W ⟶ X} {q : W ⟶ M} {h : X.RationalMap W} {GX GY : RDivisor W}
    (hZ : MMP.Mori.IsProjectiveVariety k sZ) (hf : IsProjectiveMorphism f)
    (hg : IsProjectiveMorphism g)
    (hfZ : f ≫ sZ = sX) (hgZ : g ≫ sZ = sM)
    (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hBM : MMP.Intersection.IsLogCanonicalPair sM BM)
    (hR : IsLogComparisonResolution sX sM sW φ KX (QDivisor.toRDivisor B) KM
      (QDivisor.toRDivisor BM) p q h GX GY)
    (hpq : p ≫ f = q ≫ g)
    {A : QDivisor X} (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hBA : MMP.Intersection.IsLogCanonicalPair sX (B + A))
    {H : QDivisor Z} (hH : H.IsQCartier) {HX : RDivisor X}
    (hHX : MMP.Flips.IsRCartierPullback f (QDivisor.toRDivisor H) HX)
    {n : ℕ} (hn : 0 < n) {u : (RationalFunctions X)ˣ}
    (hu : (n : ℝ) • MMP.Flips.logCanonicalDivisor KX (QDivisor.toRDivisor (B + A)) =
      (n : ℝ) • HX + Divisor.toRDivisor (principalDivisor u))
    {AW : RDivisor W} (hAW : MMP.Flips.IsRCartierPullback p (QDivisor.toRDivisor A) AW)
    {AM : QDivisor M}
    (hAM : RationalMap.transformDivisor q.toRationalMap AW = QDivisor.toRDivisor AM) :
    (0 ≤ AM ∧ AM.IsQCartier) ∧
    (∃ (HM : RDivisor M) (uM : (RationalFunctions M)ˣ),
      MMP.Flips.IsRCartierPullback g (QDivisor.toRDivisor H) HM ∧
      (∃ hqu hpu, pullbackRationalFunction q uM hqu = pullbackRationalFunction p u hpu) ∧
      (n : ℝ) • MMP.Flips.logCanonicalDivisor KM (QDivisor.toRDivisor (BM + AM)) =
        (n : ℝ) • HM + Divisor.toRDivisor (principalDivisor uM)) ∧
    (∀ G : RDivisor W,
      MMP.Flips.IsRCartierPullback p
        (MMP.Flips.logCanonicalDivisor KX (QDivisor.toRDivisor (B + A))) G →
      MMP.Flips.IsRCartierPullback q
        (MMP.Flips.logCanonicalDivisor KM (QDivisor.toRDivisor (BM + AM))) G) ∧
    MMP.Flips.IsRCartierPullback q (QDivisor.toRDivisor AM) (AW + (GX - GY)) ∧
    MMP.Intersection.IsLogCanonicalPair sM (BM + AM) ∧
    ∀ (d : ℕ) (E : DivisorOver k sM),
      MMP.Intersection.IsLogDiscrepancy sM d (QDivisor.toRDivisor BM) E 0 →
        (haveI := E.isLocallyNoetherian
         haveI := E.isNormal
         ∀ G : RDivisor E.Y, MMP.Flips.IsRCartierPullback E.f (QDivisor.toRDivisor AM) G →
           G.coeff E.E = 0) ∧
        ¬ (E.center : Set M) ⊆ AM.supp := by
  classical
  -- normal varieties, properness, dominance
  have hXn : IsNormalVariety k sX := hB.1.1
  have hMn : IsNormalVariety k sM := hBM.1.1
  have hWn : IsNormalVariety k sW := ⟨hR.isVariety, inferInstance⟩
  have hWnp : IsNormalVariety k (p ≫ sX) := by rwa [hR.comp_eq_left]
  have hWnq : IsNormalVariety k (q ≫ sM) := by rwa [hR.comp_eq_right]
  haveI := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : LocallyOfFiniteType sW := hR.isVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sM := hMn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p ≫ sX) := hWnp.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sM) := hWnq.1.toLocallyOfFiniteType
  haveI := hR.isVariety
  haveI := hXn.1
  haveI := hMn.1
  haveI := hWnp.1
  haveI := hWnq.1
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsIntegral Z := hZ.toIsVariety.toIsIntegral
  -- dimensions and canonical divisors
  obtain ⟨-, d, K0X, hK0X, hQX⟩ := hB.1
  obtain ⟨-, dM, K0M, hK0M, hQM⟩ := hBM.1
  obtain ⟨dW, KW, hKW, hKWX, hKWM⟩ := hR.exists_canonicalDivisor
  have hdX := hK0X.topologicalKrullDim_eq
  have hdWX : topologicalKrullDim W = topologicalKrullDim X :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm
  have hdWM : topologicalKrullDim W = topologicalKrullDim M :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sM (q ≫ sM) hqb).symm
  obtain rfl : dW = d := by exact_mod_cast hKW.topologicalKrullDim_eq.symm.trans (hdWX.trans hdX)
  obtain rfl : dM = dW := by
    exact_mod_cast hK0M.topologicalKrullDim_eq.symm.trans
      (hdWM.symm.trans hKW.topologicalKrullDim_eq)
  have hdM := hK0M.topologicalKrullDim_eq
  have hKWp : KW.IsCanonicalDivisor (p ≫ sX) dM := by rw [hR.comp_eq_left]; exact hKW
  have hKWq : KW.IsCanonicalDivisor (q ≫ sM) dM := by rw [hR.comp_eq_right]; exact hKW
  obtain ⟨ωX, hωX0, hωX, hωXW⟩ :=
    exists_divisorOfForm_eq_transformDivisor hXn hWnp hpb hdX hKWp
  obtain ⟨ωM, hωM0, hωM, hωMW⟩ :=
    exists_divisorOfForm_eq_transformDivisor hMn hWnq hqb hdM hKWq
  rw [hKWX] at hωX
  rw [hKWM] at hωM
  have hKXc : (divisorOfForm ωX).IsCanonicalDivisor sX dM := by
    have h1 := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXn hK0X hωX0
    rw [one_smul] at h1
    exact hK0X.of_linearlyEquivalent h1
  have hKMc : (divisorOfForm ωM).IsCanonicalDivisor sM dM := by
    have h1 := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hMn hK0M hωM0
    rw [one_smul] at h1
    exact hK0M.of_linearlyEquivalent h1
  have hKMK0 : KM.LinearlyEquivalent K0M := by
    have h1 := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hMn hK0M hωM0
    rwa [one_smul, hωM] at h1
  -- the presentation of `H` and its pull-backs to `M` and `W`
  obtain ⟨mH, s, LH, LHX, hLHc, hHsum, hLHXpb, hHXeq⟩ := hHX
  have hgenX : ∀ j, f (genericPoint X) ∉ (LH j).supp := fun j => by
    have := (hLHXpb j).1 (pointComponent (genericPoint X))
    rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this
  have hgenW : ∀ j (Z : irreducibleComponents W),
      (q ≫ g) (componentGenericPoint W Z) ∉ (LH j).supp := by
    intro j Z
    rw [← hpq, MMP.Fourfold.componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply,
      map_genericPoint_of_isDominant p]
    exact hgenX j
  have hgenM : ∀ j (Z : irreducibleComponents M), g (componentGenericPoint M Z) ∉ (LH j).supp := by
    intro j Z
    have := hgenW j (pointComponent (genericPoint W))
    rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint, Scheme.Hom.comp_apply,
      map_genericPoint_of_isDominant q, ← MMP.Fourfold.componentGenericPoint_eq_genericPoint Z]
      at this
  let LHM : Fin mH → Divisor M := fun j => (LH j).pullback (hLHc j) (hgenM j)
  have hLHM : ∀ j, (LH j).IsPullback g (hgenM j) (LHM j) := fun j =>
    Divisor.isPullback_pullback _ _
  have hLHMc : ∀ j, (LHM j).IsCartier := fun j => (hLHM j).isCartier (hLHc j)
  have hLHXc : ∀ j, (LHX j).IsCartier := fun j => (hLHXpb j).2.isCartier (hLHc j)
  let LHW : Fin mH → Divisor W := fun j => (LHX j).pullback (hLHXc j)
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p _)
  have hLHW : ∀ j, (LHX j).IsPullback p
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p _) (LHW j) := fun j =>
    Divisor.isPullback_pullback _ _
  have hLHWq : ∀ j, (LHM j).IsPullback q
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant q _) (LHW j) := by
    intro j
    obtain ⟨L'', hL''⟩ := (hLHMc j).exists_isPullback
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant q (LHM j))
    have h2 : (LH j).IsPullback (q ≫ g) (hgenW j) L'' := isPullback_comp (hLHM j) hL'' _
    have h1 : (LH j).IsPullback (q ≫ g) (hgenW j) (LHW j) :=
      isPullback_of_hom_eq hpq _ (isPullback_comp (hLHXpb j).2 (hLHW j)
        (fun Z => by rw [hpq]; exact hgenW j Z))
    rwa [Divisor.IsPullback.eq (hLHc j) h2 h1] at hL''
  set HM : RDivisor M := ∑ j, s j • Divisor.toRDivisor (LHM j) with hHMdef
  set HW : RDivisor W := ∑ j, s j • Divisor.toRDivisor (LHW j) with hHWdef
  have hHM : IsRCartierPullback g (QDivisor.toRDivisor H) HM :=
    ⟨mH, s, LH, LHM, hLHc, hHsum, fun j => ⟨_, hLHM j⟩, rfl⟩
  have hHWp : IsRCartierPullback p HX HW :=
    ⟨mH, s, LHX, LHW, hLHXc, hHXeq, fun j => ⟨_, hLHW j⟩, rfl⟩
  have hHWq : IsRCartierPullback q HM HW :=
    ⟨mH, s, LHM, LHW, hLHMc, rfl, fun j => ⟨_, hLHWq j⟩, rfl⟩
  -- the rational function
  have hpu : ∀ Z : irreducibleComponents W,
      p (componentGenericPoint W Z) ∉ (principalDivisor u).supp :=
    MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p _
  set uW := pullbackRationalFunction p u hpu with huWdef
  obtain ⟨uM, hqu, huM⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hqb uW
  have hdivp : (principalDivisor u).IsPullback p hpu (principalDivisor uW) :=
    Divisor.isPullback_principalDivisor u hpu
  have hdivq : (principalDivisor uM).IsPullback q hqu (principalDivisor uW) := by
    rw [← huM]; exact Divisor.isPullback_principalDivisor uM hqu
  have hdivpR := isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor u) _ hdivp
  have hdivqR := isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor uM) _ hdivq
  -- the identity on `W`
  have hGXA : IsRCartierPullback p (logCanonicalDivisor KX (QDivisor.toRDivisor (B + A)))
      (GX + AW) := by
    have : logCanonicalDivisor KX (QDivisor.toRDivisor (B + A)) =
        logCanonicalDivisor KX (QDivisor.toRDivisor B) + QDivisor.toRDivisor A := by
      simp only [logCanonicalDivisor, map_add, add_assoc]
    rw [this]
    exact isRCartierPullback_add hR.isRCartierPullback_left hAW
  have hWid : (n : ℝ) • (GX + AW) = (n : ℝ) • HW + Divisor.toRDivisor (principalDivisor uW) := by
    have h1 := isRCartierPullback_smul (n : ℝ) hGXA
    rw [hu] at h1
    exact isRCartierPullback_eq h1 (isRCartierPullback_add (isRCartierPullback_smul (n : ℝ) hHWp)
      hdivpR)
  -- the identity on `M`, pushing forward the identity on `W`
  have hMid : (n : ℝ) • logCanonicalDivisor KM (QDivisor.toRDivisor (BM + AM)) =
      (n : ℝ) • HM + Divisor.toRDivisor (principalDivisor uM) := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    obtain ⟨PW, heq, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hMn hWnq hqb P
    have e1 := coeff_eq_of_isRCartierPullback PW P heq hR.isRCartierPullback_right
    have e2 : (QDivisor.toRDivisor AM).coeff P = AW.coeff PW := by
      rw [← hAM]; exact htr AW
    have e3 : (GX - GY).coeff PW = 0 := by
      by_contra hne
      exact not_isExceptionalPrimeDivisor_of_map_genericPoint sM hdM q PW P heq
        (hR.isExceptional PW hne)
    have e4 := coeff_eq_of_isRCartierPullback PW P heq hHWq
    have e5 := coeff_eq_of_isRCartierPullback PW P heq hdivqR
    have e6 := congrArg (fun D : RDivisor W => D.coeff PW) hWid
    simp only [logCanonicalDivisor, map_add, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at e1 e3 e6 ⊢
    linear_combination -(n : ℝ) * e1 + (n : ℝ) * e2 - (n : ℝ) * e3 + e6 + (n : ℝ) * e4 + e5
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlogM : logCanonicalDivisor KM (QDivisor.toRDivisor (BM + AM)) =
      HM + (1 / (n : ℝ)) • Divisor.toRDivisor (principalDivisor uM) :=
    eq_add_one_div_smul_of_smul_eq hn0 hMid
  set G0 : RDivisor W := HW + (1 / (n : ℝ)) • Divisor.toRDivisor (principalDivisor uW) with hG0def
  have hG0q : IsRCartierPullback q (logCanonicalDivisor KM (QDivisor.toRDivisor (BM + AM))) G0 := by
    rw [hlogM]
    exact isRCartierPullback_add hHWq (isRCartierPullback_smul _ hdivqR)
  have hGXA0 : GX + AW = G0 := eq_add_one_div_smul_of_smul_eq hn0 hWid
  have hC3 : ∀ G : RDivisor W,
      IsRCartierPullback p (logCanonicalDivisor KX (QDivisor.toRDivisor (B + A))) G →
      IsRCartierPullback q (logCanonicalDivisor KM (QDivisor.toRDivisor (BM + AM))) G := by
    intro G hG
    rw [isRCartierPullback_eq hG hGXA, hGXA0]
    exact hG0q
  have hC4 : IsRCartierPullback q (QDivisor.toRDivisor AM) (AW + (GX - GY)) := by
    have e : QDivisor.toRDivisor AM = logCanonicalDivisor KM (QDivisor.toRDivisor (BM + AM)) -
        logCanonicalDivisor KM (QDivisor.toRDivisor BM) := by
      simp only [logCanonicalDivisor, map_add]; abel
    have e' : AW + (GX - GY) = G0 - GY := by rw [← hGXA0]; abel
    rw [e, e']
    exact isRCartierPullback_sub hG0q hR.isRCartierPullback_right
  -- effectivity of `A_M`
  have hAM0 : 0 ≤ AM := by
    refine Finsupp.le_def.mpr fun P => ?_
    obtain ⟨PW, heq, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hMn hWnq hqb P
    have e2 : (QDivisor.toRDivisor AM).coeff P = AW.coeff PW := by
      rw [← hAM]; exact htr AW
    rw [QDivisor.coeff_toRDivisor] at e2
    have : (0 : ℝ) ≤ ((AM P : ℚ) : ℝ) := e2 ▸ (coeff_isRCartierPullback_nonneg hA0 hAq hAW PW).1
    exact_mod_cast this
  -- `A_M` is `ℚ`-Cartier
  have hAMq : AM.IsQCartier := by
    obtain ⟨NH, hNH, LHq, hLHq, hLHqc⟩ := hH.exists_pos
    have hgenq : ∀ Z' : irreducibleComponents M, g (componentGenericPoint M Z') ∉ LHq.supp := by
      intro Z' hZ'
      rw [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hNH.ne') hLHq] at hZ'
      obtain ⟨Γ, hΓ0, hΓ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ'
      have h1 := congrArg (fun D : RDivisor Z => D.coeff Γ) hHsum
      simp only [QDivisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at h1
      have h2 : ∑ j, s j * ((LH j).coeff Γ : ℝ) ≠ 0 := by
        rw [← h1]; exact_mod_cast hΓ0
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
      exact hgenM j Z' (DivisorWithCoeffs.mem_supp_iff.mpr
        ⟨Γ, fun h0 => hj (by rw [h0]; simp), hΓ⟩)
    set LHqM := LHq.pullback hLHqc hgenq with hLHqMdef
    have hLHqMp : LHq.IsPullback g hgenq LHqM := Divisor.isPullback_pullback _ _
    have hHMeq : HM = (1 / (NH : ℝ)) • Divisor.toRDivisor LHqM :=
      isRCartierPullback_eq hHM (isRCartierPullback_of_zsmul_eq' g hNH hLHqc hLHq.symm
        ⟨_, hLHqMp⟩)
    have hQM' := hQM.add_of_linearlyEquivalent hKMK0.symm
    obtain ⟨NK, hNK, CM, hCM, hCMc⟩ := hQM'.exists_pos
    refine ⟨((n * NH * NK : ℕ) : ℤ), by positivity,
      ((n * NK : ℕ) : ℤ) • LHqM + ((NH * NK : ℕ) : ℤ) • principalDivisor uM -
        ((n * NH : ℕ) : ℤ) • CM, ?_,
      (((hLHqMp.isCartier hLHqc).zsmul _).add
        ((Divisor.isCartier_principalDivisor uM).zsmul _)).sub (hCMc.zsmul _)⟩
    refine DivisorWithCoeffs.ext' fun P => ?_
    have e1 := congrArg (fun D : RDivisor M => D.coeff P) hMid
    have e2 := congrArg (fun D : QDivisor M => D.coeff P) hCM
    rw [hHMeq] at e1
    simp only [logCanonicalDivisor, map_add, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, Divisor.coeff_toRDivisor,
      QDivisor.coeff_toRDivisor] at e1
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, Int.cast_natCast] at e2
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, Int.cast_natCast,
      smul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Nat.cast_mul]
    have hNH0 : (NH : ℝ) ≠ 0 := by exact_mod_cast hNH.ne'
    have e2' : (CM.coeff P : ℝ) = (NK : ℝ) * ((KM.coeff P : ℝ) + ((BM.coeff P : ℚ) : ℝ)) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) e2
      push_cast at this
      exact this
    have key : ((((n : ℚ) * NK * (LHqM.coeff P : ℚ) +
        (NH : ℚ) * NK * ((principalDivisor uM).coeff P : ℚ) -
        (n : ℚ) * NH * (CM.coeff P : ℚ)) : ℚ) : ℝ) =
        (((n : ℚ) * NH * NK * AM.coeff P : ℚ) : ℝ) := by
      push_cast
      field_simp at e1
      rw [e2']
      linear_combination -(NK : ℝ) * e1
    exact_mod_cast key
  -- `(M, B_M + A_M)` is lc: crepant invariance of discrepancies along `q` and `p`
  have hG0p : IsRCartierPullback p (logCanonicalDivisor KX (QDivisor.toRDivisor (B + A))) G0 :=
    hGXA0 ▸ hGXA
  have hlcM := logDiscrepancy_nonneg_of_isRCartierPullback_eq hXn hMn hWnp hWnq hpb hqb
    (hR.comp_eq_right.trans hR.comp_eq_left.symm) hdM hωX0 hKXc hωM0 hKMc hKWp hKWq hωXW hωMW
    (DM := QDivisor.toRDivisor (BM + AM)) (G := G0) (by rw [hωX]; exact hG0p)
    (by rw [hωM]; exact hG0q) hBA.2.2
  have hlcPair : MMP.Intersection.IsLogCanonicalPair sM (BM + AM) := by
    refine ⟨⟨hMn, dM, K0M, hK0M, ?_⟩, fun P => ?_, hlcM⟩
    · rw [← add_assoc]; exact hQM.add hAMq
    · rw [DivisorWithCoeffs.coeff_add]
      exact add_nonneg (hBM.2.1 P) (Finsupp.le_def.mp hAM0 P)
  refine ⟨⟨hAM0, hAMq⟩, ⟨HM, uM, hHM, ⟨hqu, hpu, huM⟩, hMid⟩, hC3, hC4, hlcPair, ?_⟩
  -- lc places of `(M, B_M)`
  intro d E hE
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI : IsProper E.f := hE.2.1
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  have hkey : ∀ G : RDivisor E.Y, IsRCartierPullback E.f (QDivisor.toRDivisor AM) G →
      G.coeff E.E = 0 := fun G hG => by
    have h0 := (coeff_isRCartierPullback_nonneg hAM0 hAMq hG E.E).1
    have h1 := hlcM d E (0 - G.coeff E.E) (by rw [map_add]; exact isLogDiscrepancy_add hE G hG)
    linarith
  refine ⟨hkey, fun hsub => ?_⟩
  obtain ⟨G, hG⟩ := exists_isRCartierPullback E.f hAMq
  have hx : E.f E.E.genericPoint ∈ AM.supp := hsub (by
    rw [E.center_eq_closure_genericPoint]; exact subset_closure rfl)
  exact ((coeff_isRCartierPullback_nonneg hAM0 hAMq hG E.E).2 hx).ne' (hkey G hG)

end LCComplement

end MMP.Fourfold

/-! ## Log discrepancies of reduced snc pairs -/

namespace MMP.Intersection

section SNC

open TopologicalSpace
open MMP.Mori (Divisor QDivisor RDivisor DivisorOver PrimeDivisor)

/-- An exceptional divisor over a normal variety of dimension `n` forces `2 ≤ n`. -/
private theorem two_le_of_isExceptional {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Mori.IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (D : DivisorOver k sX) (hD : D.IsExceptional) : 2 ≤ n := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hsep : IsSeparated (X ↘ ⊤_ Scheme) := by
    have : (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
    rw [this]
    infer_instance
  unfold DivisorOver.IsExceptional at hD
  rw [MMP.Positivity.isExceptional_toRationalMap_iff] at hD
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc] at hD
  change 2 ≤ MMP.Mori.closedsCodimension (T := X) ⟨(D.center : Set X), D.center.isClosed⟩ at hD
  rw [MMP.Mori.closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center] at hD
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure {D.f D.E.genericPoint} : Set X) := by
    have : Nonempty (IrreducibleCloseds (closure {D.f D.E.genericPoint} : Set X)) :=
      ⟨IrreducibleCloseds.closureSingleton ⟨_, subset_closure rfl⟩⟩
    exact Order.krullDim_nonneg
  have h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    rw [← h]
    calc ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞) :=
          WithBot.coe_le_coe.mpr hD
      _ ≤ _ := le_add_of_nonneg_left h0
  exact_mod_cast h2

/-- A reduced effective divisor is the sum of its components. -/
private theorem eq_sum_single_of_isReducedEffective {X : Scheme.{u}} {T : Divisor X}
    (hT : MMP.Intersection.IsReducedEffective T) :
    T = ∑ E ∈ T.support, Finsupp.single E (1 : ℤ) := by
  classical
  ext P
  rcases hT P with h | h <;>
    simp_all [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply]

/-- The coefficients of a reduced effective divisor, as a `ℚ`-divisor, are at most `1`. -/
private theorem coeff_toQDivisor_le_one {X : Scheme.{u}} {T : Divisor X}
    (hT : MMP.Intersection.IsReducedEffective T) (P : MMP.Mori.PrimeDivisor X) :
    (Divisor.toQDivisor T).coeff P ≤ 1 := by
  rcases hT P with h | h <;> simp [h]

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {W : Scheme.{u}}
  (sW : W ⟶ Spec (.of k)) [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- On a smooth variety every log discrepancy with integral boundary is an integer: `K_W + T`
is Cartier, so `a(D, W, T) = 1 + ord_D(g^*ω) - coeff_D(g^*(K_W + T))`. -/
private theorem exists_int_eq_of_isLogDiscrepancy (hsm : MMP.Mori.IsSmoothScheme sW)
    {T : Divisor W} {n : ℕ} {D : DivisorOver k sW} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sW n T.toRDivisor D a) : ∃ z : ℤ, a = z := by
  obtain ⟨hX, hf, -, -, ⟨K, hK, -⟩, -⟩ := id ha
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D.isNormalVariety.1
  have : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sW)
  have hMc : (K + T).IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨M', hM'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hMc
  have hb : MMP.Intersection.IsLogDiscrepancy sW n T.toRDivisor D
      (1 + (D.ordPullback ω : ℝ) - ∑ _i : Fin 1, (1 : ℝ) * (M'.coeff D.E : ℝ)) :=
    ⟨hX, hf, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, 1, fun _ => 1, fun _ => K + T,
      fun _ => M', fun _ => hMc, fun Γ => by
        rw [MMP.Mori.Divisor.coeff_toRDivisor, Fin.sum_univ_one, hω Γ]
        simp [MMP.Mori.DivisorWithCoeffs.coeff_apply],
      fun _ => ⟨_, hM'⟩, rfl⟩
  exact ⟨1 + D.ordPullback ω - M'.coeff D.E, by
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha hb]; simp⟩

/-- **The discrepancy of a reduced snc pair is at least `-1`.** Every entry of the snc formula
`MMP.Mori.discrep_eq_of_isSNC` is `≥ -1` when the coefficients are `0` or `1`. -/
private theorem neg_one_le_discrep (hX : MMP.Mori.IsNormalVariety k sW)
    (hsm : MMP.Mori.IsSmoothScheme sW) {T : Divisor W} (hT : MMP.Intersection.IsReducedEffective T)
    (hsnc : T.IsSNC sW) {n : ℕ} (hn : 2 ≤ n) {K : Divisor W} (hK : K.IsCanonicalDivisor sW n) :
    ((-1 : ℝ) : EReal) ≤ MMP.Mori.discrep sW n K (Divisor.toQDivisor T) := by
  have hle := coeff_toQDivisor_le_one hT
  rw [MMP.Mori.discrep_eq_of_isSNC sW hX hsm hn hK (Δ := Divisor.toQDivisor T) T.support
    (Finsupp.support_mapRange (hf := map_zero _))
    (eq_sum_single_of_isReducedEffective hT ▸ hsnc) fun E _ => hle E]
  refine le_inf (le_inf (le_iInf₂ fun E _ => le_iInf₂ fun F _ => le_iInf₂ fun _ _ => ?_)
    (le_iInf₂ fun E _ => ?_)) (by exact_mod_cast (by norm_num : (-1 : ℝ) ≤ 1))
  all_goals rw [EReal.coe_le_coe_iff, ← Rat.cast_one, ← Rat.cast_neg, Rat.cast_le]
  · linarith [hle E, hle F]
  · linarith [hle E]

/-- **Reduced snc pairs have integral nonnegative log discrepancies.** Let `W` be a smooth variety
over an algebraically closed field `k` of characteristic zero and `T` a reduced snc divisor on
`W`. For every divisor `D` over `W` with proper structure morphism (a normalized divisorial
valuation of `k(W)`), every log discrepancy `a = a(D, W, T)` is a natural number. -/
@[mmp "lem_fourfold_snc_lc"]
public theorem IsLogDiscrepancy.exists_nat_eq_of_isSNC (hW : MMP.Mori.IsVariety k sW)
    (hsm : MMP.Mori.IsSmoothScheme sW) {T : Divisor W} (hT : IsReducedEffective T)
    (hsnc : T.IsSNC sW) {n : ℕ} {D : DivisorOver k sW} {a : ℝ}
    (ha : IsLogDiscrepancy sW n T.toRDivisor D a) :
    ∃ m : ℕ, a = m := by
  obtain ⟨hX, -, -, -, ⟨K, hK, -⟩, -⟩ := id ha
  obtain ⟨z, rfl⟩ := exists_int_eq_of_isLogDiscrepancy sW hsm ha
  have hP : MMP.Mori.IsPair sW (Divisor.toQDivisor T) := ⟨hX, n, K, hK, by
    rw [← map_add]
    exact MMP.Mori.QDivisor.isQCartier_toQDivisor (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _)⟩
  rw [← QDivisor.toRDivisor_toQDivisor T] at ha
  have hnonneg : (0 : ℝ) ≤ z := by
    by_cases hE : D.IsExceptional
    · obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
      have := EReal.coe_le_coe_iff.mp ((neg_one_le_discrep sW hX hsm hT hsnc
        (two_le_of_isExceptional hX hK.topologicalKrullDim_eq D hE) hK).trans
        (MMP.Mori.discrep_le hE hc))
      rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
      linarith
    · obtain ⟨P, hv⟩ :=
        MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hE
      obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
        (DivisorOver.ofPrimeDivisor k hX P)
      rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha
        (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
          (show IsProper (𝟙 W) from inferInstance)) hv,
        MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX hc]
      have : ((Divisor.toQDivisor T).coeff P : ℝ) ≤ 1 := by
        exact_mod_cast coeff_toQDivisor_le_one hT P
      push_cast
      linarith
  exact ⟨z.toNat, by exact_mod_cast (Int.toNat_of_nonneg (by exact_mod_cast hnonneg)).symm⟩

end SNC

end MMP.Intersection

/-! ## The reduced snc discrepancy -/

namespace MMP.Fourfold

section ReducedSNC

open MMP.Mori
open scoped WithZero

/-- The inclusion of an open subscheme `U` is biregular over `U`. -/
private theorem isBiregular_ι_self {W : Scheme.{u}} (U : W.Opens) : IsBiregular U.ι U := by
  have h1 : U.ι ∣_ U = (U.ι ⁻¹ᵁ U).ι := by
    rw [← cancel_mono U.ι, morphismRestrict_ι]
  show IsIso (U.ι ∣_ U)
  rw [h1, U.ι_preimage_self, isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
  change y ∈ Set.range (⊤ : U.toScheme.Opens).ι
  rw [Scheme.Opens.range_ι]
  trivial

/-- Along the inclusion of an open subscheme, the inverse transform of a divisor is its
restriction. -/
private theorem inverseTransformDivisor_ι {R : Type*} [AddCommMonoid R] {W : Scheme.{u}}
    (U : W.Opens) (D : DivisorWithCoeffs R W) :
    inverseTransformDivisor U.ι D = D.restrictOpen U := by
  refine Finsupp.ext fun F => ?_
  have hη := OpenWeilRestriction.genericPoint_primeDivisorMap U.ι F
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη.symm
      (le_biregularLocus (isBiregular_ι_self U) F.genericPoint.2)) (fun P hP => ?_) D
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  rw [hη]
  exact
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP).1.symm

/-- On `sncComplement T S`, a reduced effective divisor `T` restricts to the sum of its
components containing `S`. -/
private theorem restrictOpen_reducedDivisorOf_sncIndexSet {W : Scheme.{u}} {T : Divisor W}
    (hT : MMP.Intersection.IsReducedEffective T) (S : Set W) :
    (MMP.Intersection.reducedDivisorOf (sncIndexSet T S)).restrictOpen (sncComplement T S) =
      T.restrictOpen (sncComplement T S) := by
  classical
  refine Finsupp.ext fun F => ?_
  set P := OpenWeilRestriction.primeDivisorMap (sncComplement T S).ι F
  have hPU : P.genericPoint ∈ sncComplement T S := by
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact F.genericPoint.2
  change (MMP.Intersection.reducedDivisorOf _).coeff P = T.coeff P
  rw [MMP.Intersection.coeff_reducedDivisorOf]
  by_cases hPT : P ∈ T.support
  · have hPJ : P ∈ sncIndexSet T S := by
      refine Finset.mem_filter.2 ⟨hPT, by_contra fun hZP => hPU ?_⟩
      refine Set.mem_biUnion (Finset.mem_filter.2 ⟨hPT, hZP⟩) ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    rw [if_pos hPJ]
    exact ((hT P).resolve_left (Finsupp.mem_support_iff.1 hPT)).symm
  · rw [if_neg (fun h : P ∈ sncIndexSet T S => hPT (Finset.mem_filter.1 h).1)]
    exact (Finsupp.notMem_support_iff.1 hPT).symm

open MMP.Threefold.Mori.OpenRestriction in
/-- The restriction of an snc divisor to an open subscheme is snc. -/
private theorem isSNC_restrictOpen {R : Type*} [Zero R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) (U : X.Opens) :
    (D.restrictOpen U).IsSNC (U.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => (sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))⟩
  have hsm := hD.1 (OpenWeilRestriction.primeDivisorMap U.ι E₀)
    (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hE₀ : D.restrictOpen U E₀ ≠ 0))
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus] at hsm
  exact (isSmoothScheme_comap_iff U.ι g (OpenWeilRestriction.primeDivisorMap U.ι E₀).idealSheaf
    E₀.idealSheaf (idealSheaf_comap_primeDivisorMap U.ι E₀)).mpr fun z _ => hsm ▸ trivial

/-- **The reduced snc discrepancy is a nonnegative integer.** Let `W` be a smooth variety over an
algebraically closed field `k` of characteristic zero, `T` a reduced snc divisor on `W` and `ξ` a
normalized divisorial valuation of `k(W)` with centre on `W`. Then the reduced snc discrepancy
`e_T(ξ)` is a nonnegative integer. -/
@[mmp "lem_oai4_snc_valuations_b"]
public theorem IsReducedSNCDiscrepancy.exists_eq_natCast {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] {T : MMP.Mori.Divisor W} {ξ : Valuation W.functionField ℤᵐ⁰} {e : ℝ}
    (h : IsReducedSNCDiscrepancy sW T ξ e) : ∃ m : ℕ, e = m := by
  obtain ⟨hW, hsm, hT, hsnc, Z, -, hne, n, D, -, -, ha⟩ := h
  rw [inverseTransformDivisor_ι, restrictOpen_reducedDivisorOf_sncIndexSet hT] at ha
  have hWU : MMP.Mori.IsVariety k ((sncComplement T Z).ι ≫ sW) := by
    haveI := hW
    constructor
  haveI := hW.toLocallyOfFiniteType
  refine MMP.Intersection.IsLogDiscrepancy.exists_nat_eq_of_isSNC _ hWU
    (MMP.Threefold.Resolution.isSmoothScheme_ι k hsm _) (fun P => hT _)
    (isSNC_restrictOpen sW hsnc _) ha

end ReducedSNC

/-! ## A codimension bound for the reduced snc discrepancy -/

section CodimensionBound

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open TopologicalSpace MMP.Mori
open scoped WithZero

/-! ### Blowing up a point of codimension two -/

open scoped Classical in
/-- Local equations of the prime divisors through a point with regular local ring: the local
ring there is factorial. -/
private theorem exists_localEquation
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (x : X) (hreg : IsRegularLocalRing (X.presheaf.stalk x)) (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : x ∈ Γ.support) :
    ∃ π : X.presheaf.stalk x, π ≠ 0 ∧
      Γ.idealSheaf.stalkIdeal x = Ideal.span {π} ∧
      ∀ Γ' : MMP.Mori.PrimeDivisor X, x ∈ Γ'.support →
        X.ord (algebraMap _ X.functionField π) Γ'.genericPoint = if Γ' = Γ then 1 else 0 := by
  have := IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk x)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hsp : Γ.genericPoint ⤳ x := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hΓ
  set q := MMP.Intersection.primeOfSpecializes hsp with hq
  -- the prime of `η_Γ` has height one
  have hq1 : q.height = 1 := by
    let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hsp
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk Γ.genericPoint)
    rw [ringKrullDim_stalk_eq_coheight, Γ.coheight_genericPoint] at e
    exact_mod_cast e.symm
  -- the stalk of the ideal of `Γ`
  set I := IdealSheafData.stalk Γ.idealSheaf x with hI
  have hxs : x ∈ Γ.idealSheaf.support := hΓ
  have hIp : I.IsPrime := by
    have := Γ.integral
    obtain ⟨y, hy⟩ : x ∈ Set.range Γ.idealSheaf.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hxs
    rw [hI, ← hy, ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
    exact RingHom.ker_isPrime _
  have hI0 : I ≠ ⊥ := by
    intro h0
    have := Γ.isDiscreteValuationRing_localRing
    have hmap := MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes Γ.idealSheaf hsp
    rw [MMP.Resolution.Aux.stalk_idealSheaf_genericPoint, ← hI, h0, Ideal.map_bot] at hmap
    exact IsDiscreteValuationRing.not_a_field _ hmap
  have hIq : I ≤ q :=
    (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes Γ.idealSheaf hsp).mp
      (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Γ)
  obtain ⟨π, hπI, hπ⟩ := hIp.exists_mem_prime_of_ne_bot hI0
  have hqπ : q = Ideal.span {π} := Ideal.eq_span_singleton_of_height_eq_one hq1 (hIq hπI) hπ
  have hIπ : I = Ideal.span {π} :=
    le_antisymm (hqπ ▸ hIq) ((Ideal.span_singleton_le_iff_mem _).mpr hπI)
  refine ⟨π, hπ.ne_zero, by rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk]; exact hIπ,
    fun Γ' hΓ' => ?_⟩
  have hsp' : Γ'.genericPoint ⤳ x :=
    MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ' hΓ'
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp' π]
  have hπK : algebraMap Γ'.localRing X.functionField
      ((X.presheaf.stalkSpecializes hsp').hom π) ≠ 0 := by
    rw [MMP.Mori.algebraMap_stalkSpecializes hsp' π]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
  split_ifs with hΓΓ'
  · subst hΓΓ'
    have := Γ'.isDiscreteValuationRing_localRing
    let := (X.presheaf.stalkSpecializes hsp').hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hsp'
    have hmax : IsLocalRing.maximalIdeal Γ'.localRing =
        Ideal.span {(X.presheaf.stalkSpecializes hsp').hom π} := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (X.presheaf.stalk Γ'.genericPoint),
        hqπ, Ideal.map_span, Set.image_singleton]
      rfl
    have hirr : Irreducible ((X.presheaf.stalkSpecializes hsp').hom π) :=
      IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
        (fun h => by rw [h, map_zero] at hπK; exact hπK rfl) hmax
    rw [Scheme.ord_eq_iff Γ'.coheight_genericPoint hπK]
    have : Ring.KrullDimLE 1 Γ'.localRing :=
      krullDimLE_of_coheight_le Γ'.coheight_genericPoint.le
    exact Ring.ordFrac_irreducible hirr
  · refine Γ'.ord_algebraMap_of_isUnit ?_
    by_contra hnu
    have hmem : π ∈ MMP.Intersection.primeOfSpecializes hsp' := by
      change (X.presheaf.stalkSpecializes hsp').hom π ∈ IsLocalRing.maximalIdeal _
      exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hle : q ≤ MMP.Intersection.primeOfSpecializes hsp' := by
      rw [hqπ, Ideal.span_singleton_le_iff_mem]; exact hmem
    have h1 := MMP.Intersection.specializes_of_primeOfSpecializes_le hsp hsp' hle
    apply hΓΓ'
    by_contra hne
    have hle : Γ'.genericPoint ≤ Γ.genericPoint := h1
    have hlt : Γ'.genericPoint < Γ.genericPoint := lt_of_le_not_ge hle fun h =>
      hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (Specializes.antisymm (show Γ'.genericPoint ⤳ Γ.genericPoint from h) h1).eq)
    have h2 := Order.coheight_add_one_le hlt
    rw [Γ.coheight_genericPoint, Γ'.coheight_genericPoint] at h2
    exact absurd h2 (by decide)

/-! ### Simple normal crossing divisors -/

/-- A prime divisor through `x` contains the closure of `x`. -/
private theorem closure_singleton_subset_support {X : Scheme.{u}} (G : MMP.Mori.PrimeDivisor X)
    {x : X} (hx : x ∈ G.support) : closure {x} ⊆ G.support := by
  refine closure_minimal (Set.singleton_subset_iff.2 hx) ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure G]
  exact isClosed_closure

/-- The support of `∑_{E ∈ S} E` is `S`. -/
private theorem mem_support_sum_single {X : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor X))
    (G : MMP.Mori.PrimeDivisor X) :
    G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ↔ G ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

/-- The local description of `∑_{E ∈ S} E` snc at a point `y`: a regular system of parameters of
`𝒪_{X,y}` and an injective choice, for each `E ∈ S` through `y`, of a parameter generating the
ideal of `E`. -/
private theorem exists_at_of_isSNC {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {S : Finset (MMP.Mori.PrimeDivisor X)}
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ))) (y : X) :
    ∃ (N : ℕ) (z : Fin N → X.presheaf.stalk y)
      (j : {G : MMP.Mori.PrimeDivisor X // G ∈ S ∧ y ∈ G.support} → Fin N),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ G, IdealSheafData.stalk G.1.idealSheaf y = Ideal.span {z (j G)} := by
  obtain ⟨N, z, j, hz, hj, hI⟩ := hsnc.2 y
  let e : {G : MMP.Mori.PrimeDivisor X // G ∈ S ∧ y ∈ G.support} →
      {G : MMP.Mori.PrimeDivisor X //
        G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ∧ y ∈ G.support} :=
    fun G => ⟨G.1, (mem_support_sum_single S G.1).mpr G.2.1, G.2.2⟩
  refine ⟨N, z, j ∘ e, hz, hj.comp fun G G' h => Subtype.ext (congrArg Subtype.val h :), ?_⟩
  exact fun G => hI (e G)

/-! ### The lower bound -/

/-- **Alternating maps on logarithmic vectors.** If the vectors `v_i`, `i ∈ T`, lie in
`ϖ M + R t` for a fixed `t ∈ M`, then `φ(v) ∈ ϖ^{|T| - 1} N`; if moreover some `v_{i₀}`, `i₀ ∉ T`,
equals `t`, then `φ(v) ∈ ϖ^{|T|} N`. -/
private theorem exists_eq_pow_smul_of_mem {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommMonoid N] [Module R N] [DecidableEq ι] (φ : M [⋀^ι]→ₗ[R] N) (ϖ : R)
    (t : M) (T : Finset ι) :
    ∀ v : ι → M, (∀ i ∈ T, ∃ (a : M) (b : R), v i = ϖ • a + b • t) →
      (∃ η, φ v = ϖ ^ (T.card - 1) • η) ∧
        ((∃ i₀ ∉ T, v i₀ = t) → ∃ η, φ v = ϖ ^ T.card • η) := by
  induction T using Finset.induction_on with
  | empty =>
    intro v _
    exact ⟨⟨φ v, by simp⟩, fun _ => ⟨φ v, by simp⟩⟩
  | insert i T hiT ih =>
    intro v hv
    obtain ⟨a, b, hvi⟩ := hv i (Finset.mem_insert_self i T)
    have hsplit : φ v = ϖ • φ (Function.update v i a) + b • φ (Function.update v i t) := by
      conv_lhs => rw [← Function.update_eq_self i v, hvi]
      rw [AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
        AlternatingMap.map_update_smul]
    have hT : ∀ w : M, ∀ j ∈ T, ∃ (a : M) (b : R), Function.update v i w j = ϖ • a + b • t := by
      intro w j hj
      have hji : j ≠ i := fun h => hiT (h ▸ hj)
      rw [Function.update_of_ne hji]
      exact hv j (Finset.mem_insert_of_mem hj)
    have hcard := Finset.card_insert_of_notMem hiT
    obtain ⟨⟨η₁, h₁⟩, -⟩ := ih (Function.update v i a) (hT a)
    obtain ⟨-, h₂⟩ := ih (Function.update v i t) (hT t)
    obtain ⟨η₂, h₂⟩ := h₂ ⟨i, hiT, by simp⟩
    refine ⟨?_, ?_⟩
    · rw [hcard, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos T.card with h0 | hpos
      · exact ⟨φ v, by rw [h0, pow_zero, one_smul]⟩
      · rw [hsplit, h₁, h₂]
        refine ⟨η₁ + b • η₂, ?_⟩
        rw [smul_smul, ← pow_succ', Nat.sub_add_cancel hpos, smul_add, smul_comm b]
    · rintro ⟨i₀, hi₀, hvi₀⟩
      have hi₀i : i₀ ≠ i := fun h => hi₀ (h ▸ Finset.mem_insert_self i T)
      have hi₀T : i₀ ∉ T := fun h => hi₀ (Finset.mem_insert_of_mem h)
      have hz : φ (Function.update v i t) = 0 :=
        AlternatingMap.map_eq_zero_of_eq φ _ (i := i) (j := i₀)
          (by rw [Function.update_self, Function.update_of_ne hi₀i, hvi₀]) hi₀i.symm
      obtain ⟨-, h₃⟩ := ih (Function.update v i a) (hT a)
      obtain ⟨η₃, h₃⟩ := h₃ ⟨i₀, hi₀T, by rw [Function.update_of_ne hi₀i, hvi₀]⟩
      refine ⟨η₃, ?_⟩
      rw [hsplit, hz, smul_zero, add_zero, h₃, smul_smul, ← pow_succ', hcard]

open scoped TensorProduct in
/-- **Regular parameters are part of a basis of the differentials.** On an integral scheme `X`
of dimension `n` smooth over a field of characteristic zero, a regular system of parameters
`z_1, …, z_c` of `𝒪_{X,x}` extends to a basis `dz_1, …, dz_c, w_{c+1}, …, w_n` of
`Ω_{𝒪_{X,x}/k}`; its wedge generates `Ω^n_{𝒪_{X,x}/k}` and has nonzero image in `Ω^n_{k(X)/k}`. -/
private theorem exists_topForms_generator_ιMulti {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k)) [Smooth sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (x : X) {c : ℕ} {z : Fin c → X.presheaf.stalk x}
    (hz : IsRegularSystemOfParameters z) :
    letI := stalkAlgebra sX x
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX x
    ∃ (hcn : c ≤ n) (w : Fin n → Ω[X.presheaf.stalk x⁄k]),
      (∀ i : Fin c, w (Fin.castLE hcn i) = KaehlerDifferential.D k _ (z i)) ∧
      Submodule.span (X.presheaf.stalk x) {exteriorPower.ιMulti (X.presheaf.stalk x) n w} = ⊤ ∧
      topFormsMap k (X.presheaf.stalk x) X.functionField n
        (exteriorPower.ιMulti (X.presheaf.stalk x) n w) ≠ 0 := by
  classical
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  obtain ⟨h1, h2, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts sX x
  have := h1
  have := h2
  have := h3
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.EssFiniteType.of_surjective
      (IsScalarTower.toAlgHom k (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x))) IsLocalRing.residue_surjective
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallySmooth.of_perfectField
  obtain ⟨ht0, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular z hz.1 hz.2
  have hli' := MMP.Flips.ResolutionInputs.linearIndependent_tmul_D k z ht0 hli
  have : Module.Projective (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  obtain ⟨e, v, hvS, hvli, hvsp⟩ := MMP.Flips.ResolutionInputs.exists_sumElim_basis _ hli' _
    (MMP.Flips.ResolutionInputs.span_tmul_range_D k)
  choose r hr using hvS
  have hu : (TensorProduct.mk (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
      Ω[X.presheaf.stalk x⁄k] 1 ∘ fun i => KaehlerDifferential.D k (X.presheaf.stalk x)
        (Sum.elim z r i)) = Sum.elim (fun i => (1 : IsLocalRing.ResidueField (X.presheaf.stalk x))
          ⊗ₜ KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) v := by
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact hr j
  have hbij : Function.Bijective (Finsupp.linearCombination (X.presheaf.stalk x)
      (fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (Sum.elim z r i))) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [hu]
    refine ⟨hvli, ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp hvsp
  let B := MMP.Flips.ResolutionInputs.basisOfBijective _ hbij
  have hB : ∀ i, B i = KaehlerDifferential.D k (X.presheaf.stalk x) (Sum.elim z r i) :=
    MMP.Flips.ResolutionInputs.basisOfBijective_apply _ hbij
  -- the rank of the differentials is `n`
  obtain ⟨n', ⟨b⟩, hn'⟩ := MMP.Threefold.Resolution.exists_basis_kaehler_stalk sX x
  have hnn' : n' = n := by
    have := (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX x).trans hn'
    rw [hn] at this
    exact_mod_cast this.symm
  have hce : c + e = n := by
    have := Module.Basis.indexEquiv b B
    have h := Fintype.card_congr this
    rw [Fintype.card_fin, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
    omega
  let b' : Module.Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    B.reindex (finSumFinEquiv.trans (finCongr hce))
  have hcn : c ≤ n := by omega
  refine ⟨hcn, b', fun i => ?_, ?_, ?_⟩
  · simp only [b', Module.Basis.reindex_apply, Equiv.symm_trans_apply, finCongr_symm,
      finCongr_apply]
    have : Fin.cast hce.symm (Fin.castLE hcn i) = Fin.castAdd e i := Fin.ext rfl
    rw [this, finSumFinEquiv_symm_apply_castAdd, hB]
    rfl
  · rw [eq_top_iff]
    intro ω _
    obtain ⟨t, ht⟩ := (MMP.Intersection.bijective_smul_ιMulti_basis b').2 ω
    rw [← ht]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · have := MMP.Threefold.Resolution.nontrivial_topForms sX hn
    refine topFormsMap_ne_zero_of_span_eq_top ?_
    rw [eq_top_iff]
    intro ω _
    obtain ⟨t, ht⟩ := (MMP.Intersection.bijective_smul_ιMulti_basis b').2 ω
    rw [← ht]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- `d(u ϖ^e) = ϖ^{e-1}(ϖ du + e u dϖ)` for `e ≥ 1`. -/
private theorem D_mul_pow {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (u ϖ : R)
    {e : ℕ} (he : 1 ≤ e) :
    KaehlerDifferential.D k R (u * ϖ ^ e) = ϖ ^ (e - 1) •
      (ϖ • KaehlerDifferential.D k R u + ((e : R) * u) • KaehlerDifferential.D k R ϖ) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [Derivation.leibniz, Derivation.leibniz_pow]
  simp only [add_tsub_cancel_left]
  rw [pow_add, pow_one, ← Nat.cast_smul_eq_nsmul R]
  module

/-- **Logarithmic poles are simple.** Let `R` be a discrete valuation ring with uniformizer `ϖ`
over a field `k`, and `σ` a generator of `Ω^n_{R/k}` with nonzero image in `Ω^n_{K/k}`. If
`h σ = dg_1 ∧ ⋯ ∧ dg_c ∧ v_{c+1} ∧ ⋯ ∧ v_n` with `c ≥ 1` and `g_i = u_i ϖ^{e_i}`, `u_i` units
and `e_i ≥ 1`, then `h ∈ 𝔪^{e_1 + ⋯ + e_c - 1}`: writing `dg_i = g_i dlog g_i`, the wedge of the
logarithmic forms `dlog g_i ∈ Ω_R + R dϖ/ϖ` has at most a simple pole. -/
private theorem mem_maximalIdeal_pow_of_ιMulti_eq_smul {k R K : Type*} [Field k] [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R] [Field K] [Algebra k K] [Algebra R K]
    [IsScalarTower k R K] [IsFractionRing R K] {n c : ℕ} (hcn : c ≤ n) (hc : 1 ≤ c) {ϖ : R}
    (hϖ : Irreducible ϖ) {σ : ⋀[R]^n Ω[R⁄k]} (hσ : Submodule.span R {σ} = ⊤)
    (h0 : topFormsMap k R K n σ ≠ 0) (v : Fin n → Ω[R⁄k]) (u : Fin c → Rˣ) (e : Fin c → ℕ)
    (he : ∀ i, 1 ≤ e i)
    (hv : ∀ i : Fin c, v (Fin.castLE hcn i) = KaehlerDifferential.D k R (u i * ϖ ^ e i))
    {h : R} (hh : exteriorPower.ιMulti R n v = h • σ) :
    h ∈ IsLocalRing.maximalIdeal R ^ (∑ i, e i - 1) := by
  classical
  -- the data indexed by `Fin n`
  let ee : Fin n → ℕ := fun i => if hi : (i : ℕ) < c then e ⟨i, hi⟩ else 0
  let uu : Fin n → R := fun i => if hi : (i : ℕ) < c then (u ⟨i, hi⟩ : R) else 1
  let w : Fin n → Ω[R⁄k] := fun i => if (i : ℕ) < c then
    ϖ • KaehlerDifferential.D k R (uu i) + ((ee i : R) * uu i) • KaehlerDifferential.D k R ϖ
    else v i
  have hvw : v = fun i => ϖ ^ (ee i - 1) • w i := by
    funext i
    by_cases hi : (i : ℕ) < c
    · have := hv ⟨i, hi⟩
      simp only [Fin.castLE_mk] at this
      simp only [w, ee, uu, dif_pos hi, if_pos hi]
      rw [this]
      exact D_mul_pow _ _ (he _)
    · simp [w, ee, hi]
  set T : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hcn) with hT
  have hTc : T.card = c := by simp [hT]
  have hwT : ∀ i ∈ T, ∃ (a : Ω[R⁄k]) (b : R), w i = ϖ • a + b • KaehlerDifferential.D k R ϖ := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
    have hj : ((Fin.castLEEmb hcn j : Fin n) : ℕ) < c := j.2
    refine ⟨KaehlerDifferential.D k R (uu (Fin.castLEEmb hcn j)),
      (ee (Fin.castLEEmb hcn j) : R) * uu (Fin.castLEEmb hcn j), ?_⟩
    simp only [w, if_pos hj]
  obtain ⟨⟨η, hη⟩, -⟩ := exists_eq_pow_smul_of_mem (exteriorPower.ιMulti R n) ϖ
    (KaehlerDifferential.D k R ϖ) T w hwT
  have hprod : exteriorPower.ιMulti R n v = ϖ ^ (∑ i, (ee i - 1)) • exteriorPower.ιMulti R n w := by
    rw [hvw, AlternatingMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top : η ∈ _)
  -- the exponent
  have hsum : ∑ i, (ee i - 1) + (c - 1) = ∑ i, e i - 1 := by
    have h1 : ∑ i : Fin n, (ee i - 1) = ∑ i : Fin c, (e i - 1) := by
      rw [← Finset.sum_subset (Finset.subset_univ T) fun i _ hiT => ?_]
      · rw [hT, Finset.sum_map]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : ((Fin.castLEEmb hcn j : Fin n) : ℕ) < c := j.2
        simp only [ee, dif_pos hj]
        rfl
      · have hi : ¬ (i : ℕ) < c := fun hi =>
          hiT (Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        simp [ee, hi]
    have h2 : ∑ i : Fin c, (e i - 1) + c = ∑ i, e i := by
      have : ∑ i : Fin c, e i = ∑ i : Fin c, ((e i - 1) + 1) :=
        Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (he i)).symm
      rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    omega
  have hrel : h • σ = (ϖ ^ (∑ i, e i - 1) * r) • σ := by
    rw [← hh, hprod, hη, hTc, ← hr, smul_smul, smul_smul, ← pow_add, hsum]
  -- cancel `σ` in `Ω^n_{K/k}`
  have hK : algebraMap R K h = algebraMap R K (ϖ ^ (∑ i, e i - 1) * r) := by
    have := congrArg (topFormsMap k R K n) hrel
    rw [map_smul, map_smul, ← algebraMap_smul K h, ← algebraMap_smul K (ϖ ^ _ * r)] at this
    have h' := sub_eq_zero.mpr this
    rw [← sub_smul, smul_eq_zero] at h'
    exact sub_eq_zero.mp (h'.resolve_right h0)
  rw [IsFractionRing.injective R K hK]
  refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
  exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit

/-- Along a prime divisor `F` with uniformizer `ϖ`, the order of `u ϖ^m`, `u` a unit, is `m`. -/
private theorem ord_unit_mul_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : MMP.Mori.PrimeDivisor Y) [IsDiscreteValuationRing F.localRing] {ϖ : F.localRing}
    (hϖ : Irreducible ϖ) (v : F.localRingˣ) (m : ℕ) :
    Y.ord (algebraMap F.localRing Y.functionField (v * ϖ ^ m)) F.genericPoint = m := by
  have hϖK : algebraMap F.localRing Y.functionField ϖ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero
      hϖ.ne_zero)
  have hord1 : Y.ord (algebraMap F.localRing Y.functionField ϖ) F.genericPoint = 1 := by
    rw [Scheme.ord_eq_iff F.coheight_genericPoint hϖK]
    have : Ring.KrullDimLE 1 F.localRing := krullDimLE_of_coheight_le F.coheight_genericPoint.le
    exact Ring.ordFrac_irreducible hϖ
  have hvK : algebraMap F.localRing Y.functionField v ≠ 0 := (v.isUnit.map _).ne_zero
  rw [map_mul, Scheme.ord_mul hvK (by rw [map_pow]; exact pow_ne_zero _ hϖK),
    F.ord_algebraMap_of_isUnit v.isUnit, map_pow, ← zpow_natCast,
    MMP.Mori.ord_zpow _ hϖK, hord1]
  simp

/-- Along a prime divisor `F` with uniformizer `ϖ`, a nonzero element of `𝔪_F^N` has order at
least `N`. -/
private theorem le_ord_of_mem_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : MMP.Mori.PrimeDivisor Y) [IsDiscreteValuationRing F.localRing] {h : F.localRing}
    (hh : h ≠ 0) {N : ℕ} (hN : h ∈ IsLocalRing.maximalIdeal F.localRing ^ N) :
    (N : ℤ) ≤ Y.ord (algebraMap F.localRing Y.functionField h) F.genericPoint := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible F.localRing
  obtain ⟨M, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh hϖ
  rw [ord_unit_mul_pow F hϖ v M, Nat.cast_le]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Units.dvd_mul_left] at hN
  exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hN

/-- Along a prime divisor `F` of `Y`, the order of the image of an element of the stalk at
`f(η_F)` depends only on the principal ideal it generates. -/
private theorem ord_stalkMap_eq_of_span_eq {X Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : Y ⟶ X) (F : MMP.Mori.PrimeDivisor Y)
    [IsDomain (X.presheaf.stalk (f F.genericPoint))] {π z : X.presheaf.stalk (f F.genericPoint)}
    (hz : (f.stalkMap F.genericPoint).hom z ≠ 0) (h : Ideal.span {π} = Ideal.span {z}) :
    Y.ord (algebraMap F.localRing Y.functionField ((f.stalkMap F.genericPoint).hom π))
        F.genericPoint =
      Y.ord (algebraMap F.localRing Y.functionField ((f.stalkMap F.genericPoint).hom z))
        F.genericPoint := by
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  have hmul := congrArg (f.stalkMap F.genericPoint).hom hv
  rw [map_mul] at hmul
  have h1 : algebraMap F.localRing Y.functionField ((f.stalkMap F.genericPoint).hom π) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (left_ne_zero_of_mul (hmul ▸ hz)))
  have hvu : IsUnit ((f.stalkMap F.genericPoint).hom (v : X.presheaf.stalk _)) := v.isUnit.map _
  rw [← hmul, map_mul, Scheme.ord_mul h1 (hvu.map _).ne_zero, F.ord_algebraMap_of_isUnit hvu,
    add_zero]

/-- **The pull-back of a top form along a birational morphism is nonzero at a prime divisor.**
If `f : Y ⟶ X` is dominant with `f^* : k(X) ≅ k(Y)`, a top form `σ` at `f(η_F)` with nonzero
image in `Ω^d_{k(X)/k}` has nonzero image in `Ω^d_{𝒪_{Y,F}/k}`. -/
private theorem topFormsMap_stalk_localRing_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (F : MMP.Mori.PrimeDivisor Y)
    {σA : letI := stalkAlgebra sX (f F.genericPoint)
      ⋀[X.presheaf.stalk (f F.genericPoint)]^d Ω[X.presheaf.stalk (f F.genericPoint)⁄k]}
    (h0A : letI := stalkAlgebra sX (f F.genericPoint)
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX (f F.genericPoint)
      topFormsMap k (X.presheaf.stalk (f F.genericPoint)) X.functionField d σA ≠ 0) :
    letI := stalkAlgebra sX (f F.genericPoint)
    letI := stalkAlgebra (f ≫ sX) F.genericPoint
    letI := (f.stalkMap F.genericPoint).hom.toAlgebra
    haveI := MMP.Threefold.Resolution.isScalarTower_stalkMap sX f F.genericPoint
    topFormsMap k (X.presheaf.stalk (f F.genericPoint)) F.localRing d σA ≠ 0 := by
  let := stalkAlgebra sX (f F.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (f F.genericPoint)
  let := stalkAlgebra (f ≫ sX) F.genericPoint
  let := functionFieldAlgebra (f ≫ sX)
  have := isScalarTower_stalk_functionField (f ≫ sX) F.genericPoint
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  let := (f.stalkMap F.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX f F.genericPoint
  let : Algebra (X.presheaf.stalk (f F.genericPoint)) Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap (X.presheaf.stalk (f F.genericPoint)) X.functionField)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (f F.genericPoint)) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.presheaf.stalk (f F.genericPoint)) F.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      MMP.Mori.functionFieldMap_algebraMap_stalk f F.genericPoint a
  have : IsScalarTower k (X.presheaf.stalk (f F.genericPoint)) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k X.functionField Y.functionField,
        IsScalarTower.algebraMap_apply k (X.presheaf.stalk (f F.genericPoint)) X.functionField]
      rfl
  intro h0
  have e1 := MMP.Threefold.Mori.Helpers.topFormsMap_comp (k := k) (A := X.presheaf.stalk
    (f F.genericPoint)) (B := F.localRing) (C := Y.functionField) (d := d) σA
  have e2 := MMP.Threefold.Mori.Helpers.topFormsMap_comp (k := k) (A := X.presheaf.stalk
    (f F.genericPoint)) (B := X.functionField) (C := Y.functionField) (d := d) σA
  rw [h0, map_zero, ← e2] at e1
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (hω₀.1 ▸ Submodule.mem_top : topFormsMap k (X.presheaf.stalk (f F.genericPoint))
      X.functionField d σA ∈ _)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact h0A ht.symm
  rw [← ht, map_smul, ← algebraMap_smul Y.functionField t] at e1
  exact smul_ne_zero ((map_ne_zero _).mpr ht0) hω₀.2.2 e1.symm

/-- **The combinatorial bound.** If `e_1, …, e_c ≥ 1`, `j : T → Fin c` is injective and
`a_G ≤ 1` on `T`, then `∑ e_i - 1 - ∑_{G ∈ T} e_{j G} a_G ≥ -1 + ∑_{G ∈ T} (1 - a_G) + (c - |T|)`:
the indices `j G` contribute `e_{j G} (1 - a_G) ≥ 1 - a_G`, the others `e_i ≥ 1`. -/
private theorem le_sum_sub_sum_mul {ι : Type*} {c : ℕ} (e : Fin c → ℕ) (he : ∀ i, 1 ≤ e i)
    (T : Finset ι) (j : ι → Fin c) (hj : Set.InjOn j T) (a : ι → ℝ) (ha : ∀ G ∈ T, a G ≤ 1) :
    -1 + ∑ G ∈ T, (1 - a G) + ((c : ℝ) - T.card) ≤
      ((∑ i, e i : ℕ) : ℝ) - 1 - ∑ G ∈ T, (e (j G) : ℝ) * a G := by
  classical
  have hcard : T.card ≤ c := by
    simpa using Finset.card_le_card_of_injOn j (t := Finset.univ) (fun _ _ => Finset.mem_univ _) hj
  have hsplit : ((∑ i, e i : ℕ) : ℝ) = ∑ G ∈ T, (e (j G) : ℝ) + ∑ i ∈ (T.image j)ᶜ, (e i : ℝ) := by
    push_cast
    rw [← Finset.sum_add_sum_compl (T.image j), Finset.sum_image hj]
  have hcompl : ((c : ℝ) - T.card) ≤ ∑ i ∈ (T.image j)ᶜ, (e i : ℝ) := by
    have hc' : ((T.image j)ᶜ.card : ℝ) = c - T.card := by
      rw [Finset.card_compl, Fintype.card_fin, Finset.card_image_of_injOn hj]
      push_cast [hcard]
      ring
    rw [← hc']
    simpa using Finset.card_nsmul_le_sum (T.image j)ᶜ (fun i => (e i : ℝ)) 1
      fun i _ => by exact_mod_cast he i
  have hterm : ∑ G ∈ T, (1 - a G) ≤ ∑ G ∈ T, (e (j G) : ℝ) - ∑ G ∈ T, (e (j G) : ℝ) * a G := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun G hG => ?_
    have h2 : (1 : ℝ) ≤ e (j G) := by exact_mod_cast he (j G)
    nlinarith [ha G hG]
  linarith

open scoped Classical in
/-- **The lower bound for one exceptional divisor.** Let `(Y, f, E)` be exceptional over a smooth
variety `X`, with center `x₀ = f(η_E)` of codimension `c ≥ 2`, and let `T` be the components of
the snc divisor `∑_{G ∈ S} G` through `x₀`. Then
`a(E, X, Δ) ≥ -1 + ∑_{G ∈ T} (1 - a_G) + (c - |T|)`.

In a regular system of parameters `z_1, …, z_c` of `𝒪_{X,x₀}` containing local equations of
the `G ∈ T`, the form `σ = dz_1 ∧ ⋯ ∧ dz_c ∧ w` generates `ω_{X,x₀}`, and a local generator of
`𝒪_X(m(K_X + Δ))` at `x₀` is `σ^{⊗m} ∏_{G ∈ T} z_G^{-m a_G}` up to a unit. Along `E`,
`σ = ∏ z_i · (dlog z_1 ∧ ⋯ ∧ dlog z_c ∧ w)` has order at least `∑ e_i - 1`, `e_i = ord_E z_i ≥ 1`,
since a wedge of logarithmic forms has at most a simple pole. -/
private theorem le_isDiscrepancy_of_isSNC {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {Δ : QDivisor X} {S : Finset (MMP.Mori.PrimeDivisor X)}
    (hS : Δ.support ⊆ S) (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (hcoeff : ∀ E ∈ S, Δ.coeff E ≤ 1) (D : DivisorOver k sX)
    (hcod : 2 ≤ Order.coheight (D.f D.E.genericPoint)) {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) :
    ∃ (c : ℕ) (T : Finset (MMP.Mori.PrimeDivisor X)),
      Order.coheight (D.f D.E.genericPoint) = c ∧ T.card ≤ c ∧ T ⊆ S ∧
      (∀ G ∈ T, D.f D.E.genericPoint ∈ G.support) ∧
      -1 + ∑ G ∈ T, (1 - Δ.coeff G) + ((c : ℚ) - T.card) ≤ a := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hsm
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have hbij : Function.Bijective (functionFieldMap D.f) :=
    D.isBirationalMorphism.functionFieldMap_bijective
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  have hdY : (letI := functionFieldAlgebra (D.f ≫ sX)
      (Algebra.trdeg k D.Y.functionField).toNat = n) := by
    rw [← trdeg_functionField_eq_of_bijective sX D.f hbij]; exact hd
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field sX (D.f D.E.genericPoint)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk (D.f D.E.genericPoint))
  obtain ⟨c, z, j, hz, hj, hI⟩ := exists_at_of_isSNC hsnc (D.f D.E.genericPoint)
  have hcoh : Order.coheight (D.f D.E.genericPoint) = c := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  have hc2 : 2 ≤ c := by
    rw [hcoh] at hcod
    exact_mod_cast hcod
  set T := S.filter (fun G => D.f D.E.genericPoint ∈ G.support) with hT
  have hTmem : ∀ G ∈ T, G ∈ S ∧ D.f D.E.genericPoint ∈ G.support :=
    fun G hG => Finset.mem_filter.mp hG
  let jT : MMP.Mori.PrimeDivisor X → Fin c := fun G =>
    if h : G ∈ S ∧ D.f D.E.genericPoint ∈ G.support then j ⟨G, h⟩ else ⟨0, by omega⟩
  have hjT : ∀ G (h : G ∈ T), jT G = j ⟨G, hTmem G h⟩ := fun G h => dif_pos _
  have hinj : Set.InjOn jT T := fun G hG G' hG' h => by
    rw [hjT G hG, hjT G' hG'] at h
    exact congrArg Subtype.val (hj h)
  have hcard : T.card ≤ c := by
    simpa using Finset.card_le_card_of_injOn jT (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      hinj
  refine ⟨c, T, hcoh, hcard, Finset.filter_subset _ _, fun G hG => (hTmem G hG).2, ?_⟩
  -- the discrepancy data
  obtain ⟨-, -, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  -- a generator `σ_A = dz_1 ∧ ⋯ ∧ dz_c ∧ w` at `x₀`
  obtain ⟨hcn, w, hw, hσA, h0A⟩ :=
    exists_topForms_generator_ιMulti sX hn (D.f D.E.genericPoint) hz
  let := stalkAlgebra sX (D.f D.E.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (D.f D.E.genericPoint)
  let := stalkAlgebra (D.f ≫ sX) D.E.genericPoint
  let := functionFieldAlgebra (D.f ≫ sX)
  have := isScalarTower_stalk_functionField (D.f ≫ sX) D.E.genericPoint
  let := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX D.f D.E.genericPoint
  have := D.E.isDiscreteValuationRing_localRing
  -- a generator `σ_B` at `η_E`, and `f^♯ σ_A = h' σ_B`
  obtain ⟨σB, hσB, h0B⟩ := D.E.exists_topForms_generator (sX := D.f ≫ sX) hdY
  obtain ⟨h', hrel⟩ : ∃ h' : D.E.localRing,
      topFormsMap k (X.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing n
        (exteriorPower.ιMulti (X.presheaf.stalk (D.f D.E.genericPoint)) n w) = h' • σB := by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hσB ▸ Submodule.mem_top :
      topFormsMap k (X.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing n
        (exteriorPower.ιMulti (X.presheaf.stalk (D.f D.E.genericPoint)) n w) ∈ _)
    exact ⟨t, ht.symm⟩
  have hne := topFormsMap_stalk_localRing_ne_zero sX D.f hbij hd D.E h0A
  have hh'0 : h' ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hrel
    exact hne hrel
  have hh : algebraMap D.E.localRing D.Y.functionField h' ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hh'0)
  have hord := MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq sX D.f D.E hσA h0A
    hσB h0B h' hrel hh hτ.1
  -- the parameters along `E`: `f^♯ z_i = u_i ϖ^{e_i}` with `e_i ≥ 1`
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.E.localRing
  have hzm : ∀ i, z i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (D.f D.E.genericPoint)) :=
    fun i => hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hz0 : ∀ i, (D.f.stalkMap D.E.genericPoint).hom (z i) ≠ 0 := by
    intro i h0
    have hzi : z i ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz i
    have := MMP.Mori.functionFieldMap_algebraMap_stalk D.f D.E.genericPoint (z i)
    rw [h0, map_zero] at this
    exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hzi)) this
  have hzmE : ∀ i, (D.f.stalkMap D.E.genericPoint).hom (z i) ∈
      IsLocalRing.maximalIdeal D.E.localRing := fun i =>
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp (hzm i) (isUnit_of_map_unit _ _ hu)
  choose e u hzu using fun i =>
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hz0 i) hϖ
  have he : ∀ i, 1 ≤ e i := by
    intro i
    by_contra h0
    have h0 : e i = 0 := by omega
    have := hzmE i
    rw [hzu i, h0, pow_zero, mul_one] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this (u i).isUnit
  have hordz : ∀ i, D.Y.ord (algebraMap D.E.localRing D.Y.functionField
      ((D.f.stalkMap D.E.genericPoint).hom (z i))) D.E.genericPoint = e i := by
    intro i
    rw [hzu i]
    exact ord_unit_mul_pow D.E hϖ (u i) (e i)
  -- the logarithmic estimate: `ord_E h' ≥ ∑ e_i - 1`
  have hvi : ∀ i : Fin c, KaehlerDifferential.map k k (X.presheaf.stalk (D.f D.E.genericPoint))
      D.E.localRing (w (Fin.castLE hcn i)) =
        KaehlerDifferential.D k D.E.localRing (u i * ϖ ^ e i) := by
    intro i
    rw [hw i, KaehlerDifferential.map_D, ← hzu i]
    rfl
  have hrel' : exteriorPower.ιMulti D.E.localRing n (fun i => KaehlerDifferential.map k k
      (X.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (w i)) = h' • σB := by
    rw [← topFormsMap_ιMulti]
    exact hrel
  have hmem := mem_maximalIdeal_pow_of_ιMulti_eq_smul (K := D.Y.functionField) hcn (by omega) hϖ
    hσB h0B _ u e he hvi hrel'
  have hordh := le_ord_of_mem_pow D.E hh'0 hmem
  -- the coefficient `g` of `τ` along `σ_A^{⊗m}`: `ord_Γ g = -m a_Γ` through `x₀`
  let g := formCoeff (k := k) (X.presheaf.stalk (D.f D.E.genericPoint)) hσA h0A
    (show PluriForms k X.functionField n m from τ)
  have hg0 : g ≠ 0 := fun h0 => hτ.1 ((formCoeff_eq_zero_iff hσA h0A _).mp h0)
  have hgΓ : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      (X.ord g Γ.genericPoint : ℝ) = -((m : ℝ) * (Δ.coeff Γ : ℝ)) := by
    intro Γ hΓ
    have e1 := MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sX (D.f D.E.genericPoint) Γ hΓ
      hσA h0A τ
    have e2 := hτ.2 Γ ⟨_, hΓ, hU⟩
    rw [e1] at e2
    have := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at this
    linarith
  -- local equations of the components through `x₀`
  have hπex : ∀ G : T, ∃ π : X.presheaf.stalk (D.f D.E.genericPoint), π ≠ 0 ∧
      G.1.idealSheaf.stalkIdeal (D.f D.E.genericPoint) = Ideal.span {π} ∧
      ∀ Γ' : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ'.support →
        X.ord (algebraMap _ X.functionField π) Γ'.genericPoint = if Γ' = G.1 then 1 else 0 :=
    fun G => exists_localEquation _ hreg G.1 (hTmem G.1 G.2).2
  choose π hπ0 hπI hπord using hπex
  have hπE : ∀ G : T, D.Y.ord (functionFieldMap D.f (algebraMap _ X.functionField (π G)))
      D.E.genericPoint = e (jT G.1) := fun G => by
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, ← hordz,
      ord_stalkMap_eq_of_span_eq D.f D.E (hz0 (jT G.1)) (by
        rw [hjT G.1 G.2, ← hI ⟨G.1, hTmem G.1 G.2⟩, ← Scheme.IdealSheafData.stalkIdeal_eq_stalk,
          hπI G])]
  -- the Hartogs relation along `E`
  let Gf : Option T → X.functionField := fun i =>
    Option.elim i g fun G => algebraMap _ X.functionField (π G)
  let wt : Option T → ℝ := fun i => Option.elim i 1 fun G => (m : ℝ) * (Δ.coeff G.1 : ℝ)
  have hGf : ∀ i, Gf i ≠ 0 := by
    rintro (_ | G)
    · exact hg0
    · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero (hπ0 G))
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E Gf hGf wt
    fun Γ hΓ => by
      simp only [Fintype.sum_option, Gf, wt, Option.elim]
      rw [hgΓ Γ hΓ]
      simp_rw [hπord _ Γ hΓ]
      by_cases hΓT : Γ ∈ T
      · rw [Finset.sum_eq_single ⟨Γ, hΓT⟩]
        · simp
        · rintro G - hne
          have : Γ ≠ G.1 := fun h => hne (Subtype.ext h.symm)
          simp [this]
        · simp
      · have hΓS : Γ ∉ S := fun h => hΓT (Finset.mem_filter.mpr ⟨h, hΓ⟩)
        have h0 : Δ.coeff Γ = 0 := by
          rw [DivisorWithCoeffs.coeff_apply]
          exact Finsupp.notMem_support_iff.mp fun h => hΓS (hS h)
        rw [h0]
        simp only [Rat.cast_zero, mul_zero, neg_zero, mul_one, zero_add]
        refine Finset.sum_eq_zero fun G _ => ?_
        have : Γ ≠ G.1 := fun h => hΓT (h ▸ G.2)
        simp [this]
  simp only [Fintype.sum_option, Gf, wt, Option.elim, mul_one] at key
  simp_rw [hπE] at key
  push_cast at key
  -- the numerical conclusion
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmain : (m : ℝ) * (a : ℝ) = (D.Y.ord (functionFieldMap D.f g) D.E.genericPoint : ℝ) +
      (m : ℝ) * (D.Y.ord (algebraMap D.E.localRing D.Y.functionField h') D.E.genericPoint : ℝ) := by
    have h1 : (m : ℚ) * a = D.ordPullback τ := hτa
    have h2 : D.ordPullback τ = _ := hord
    rw [h2] at h1
    exact_mod_cast h1
  have hordh' : ((∑ i, e i - 1 : ℕ) : ℝ) ≤
      (D.Y.ord (algebraMap D.E.localRing D.Y.functionField h') D.E.genericPoint : ℝ) := by
    exact_mod_cast hordh
  have hsub : ((∑ i, e i - 1 : ℕ) : ℝ) = ((∑ i, e i : ℕ) : ℝ) - 1 := by
    have : 1 ≤ ∑ i, e i :=
      (he _).trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ ⟨0, by omega⟩))
    push_cast [this]
    ring
  -- `a ≥ ∑ e_i - 1 - ∑_{G ∈ T} e_{j G} a_G`
  have hlow : ((∑ i, e i : ℕ) : ℝ) - 1 - ∑ G : T, (e (jT G.1) : ℝ) * (Δ.coeff G.1 : ℝ) ≤ a := by
    have h3 : (D.Y.ord (functionFieldMap D.f g) D.E.genericPoint : ℝ) =
        -∑ G : T, (e (jT G.1) : ℝ) * ((m : ℝ) * (Δ.coeff G.1 : ℝ)) := by
      linarith
    have h4 : ∑ G : T, (e (jT G.1) : ℝ) * ((m : ℝ) * (Δ.coeff G.1 : ℝ)) =
        (m : ℝ) * ∑ G : T, (e (jT G.1) : ℝ) * (Δ.coeff G.1 : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h4] at h3
    have h5 : (m : ℝ) * (((∑ i, e i : ℕ) : ℝ) - 1 - ∑ G : T, (e (jT G.1) : ℝ) *
        (Δ.coeff G.1 : ℝ)) ≤ (m : ℝ) * a := by
      rw [hmain, h3, ← hsub]
      nlinarith [hordh']
    exact le_of_mul_le_mul_left h5 hm'
  rw [Finset.sum_coe_sort T (fun G => (e (jT G) : ℝ) * (Δ.coeff G : ℝ))] at hlow
  have hcomb := le_sum_sub_sum_mul e he T jT hinj (fun G => (Δ.coeff G : ℝ))
    fun G hG => by exact_mod_cast hcoeff G (hTmem G hG).1
  exact_mod_cast hcomb.trans hlow

/-! ### Restriction to the open `W°_ξ` -/

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-- A point lies in `sncComplement T S` iff it avoids every component of `T` not containing `S`. -/
private theorem mem_sncComplement_iff {W : Scheme.{u}} (T : Divisor W) (S : Set W) (x : W) :
    x ∈ MMP.Fourfold.sncComplement T S ↔
      ∀ E ∈ T.support, ¬ S ⊆ E.support → x ∉ E.support := by
  change x ∈ (MMP.Fourfold.sncComplement T S : Set W) ↔ _
  simp [MMP.Fourfold.sncComplement]

/-- On the open `W° = sncComplement T S`, a reduced effective divisor `T` restricts to the sum of
its components containing `S`. -/
private theorem toRDivisor_restrictOpen_sncComplement {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {T : Divisor W}
    (hT : MMP.Intersection.IsReducedEffective T) (S : Set W) :
    QDivisor.toRDivisor ((Divisor.toQDivisor T).restrictOpen (MMP.Fourfold.sncComplement T S)) =
      Divisor.toRDivisor (inverseTransformDivisor (MMP.Fourfold.sncComplement T S).ι
        (MMP.Intersection.reducedDivisorOf (MMP.Fourfold.sncIndexSet T S))) := by
  rw [inverseTransformDivisor_ι, restrictOpen_reducedDivisorOf_sncIndexSet hT]
  refine Finsupp.ext fun F => ?_
  change (((T _ : ℤ) : ℚ) : ℝ) = ((T _ : ℤ) : ℝ)
  push_cast; rfl

/-! ### The codimension bound -/

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {W : Scheme.{u}}
  {sW : W ⟶ Spec (.of k)}
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- **Codimension bound for the reduced snc discrepancy.** Let `W` be a smooth variety over `k`,
`T` a reduced snc divisor on `W` and `ξ` a normalized divisorial valuation of `k(W)` whose centre
`Z = c_W(ξ)` has codimension `c`. If `e = e_T(ξ)` is the reduced snc discrepancy, then
`c - |J(ξ)| ≤ e`, where `J(ξ) = MMP.Fourfold.sncIndexSet T Z` is the set of components of `T`
containing `Z`. -/
@[mmp "lem_oai4_snc_valuations_c"]
public theorem IsReducedSNCDiscrepancy.sub_card_sncIndexSet_le {T : Divisor W}
    {ξ : Valuation W.functionField ℤᵐ⁰} {e : ℝ} (he : IsReducedSNCDiscrepancy sW T ξ e)
    {Z : IrreducibleCloseds W} (hZ : MMP.Intersection.IsCentre k sW ξ Z) {c : ℕ}
    (hc : codimension Z = c) :
    (c : ℝ) - (sncIndexSet T (Z : Set W)).card ≤ e := by
  classical
  obtain ⟨hWv, hsm, hT, hsnc, Z₀, hZ₀, hne, n, D, hDp, hξD, hla⟩ := he
  obtain ⟨D', hD'p, hξD', rfl⟩ := hZ
  obtain rfl : Z₀ = D'.center := by
    obtain ⟨D₀, -, hξ0, rfl⟩ := hZ₀
    exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hWv (hξ0.symm.trans hξD')
  have hW : IsNormalVariety k sW := ⟨hWv, inferInstance⟩
  haveI : AlgebraicGeometry.IsVariety k sW := hWv
  set U := MMP.Fourfold.sncComplement T (D'.center : Set W) with hUdef
  haveI : Nonempty U := hne
  haveI : IsDominant U.ι := MMP.Fourfold.isDominant_ι_of_nonempty U
  -- the generic point of the centre lies in `U`
  have hηU : D'.f D'.E.genericPoint ∈ U := (mem_sncComplement_iff _ _ _).2 fun E _ hE hmem =>
    hE (by rw [D'.center_eq_closure_genericPoint]; exact closure_singleton_subset_support E hmem)
  have hηmem : D'.f D'.E.genericPoint ∈ (D'.center : Set W) := by
    rw [D'.center_eq_closure_genericPoint]; exact subset_closure rfl
  -- the dimension and a canonical divisor of `W`
  have hdimW : topologicalKrullDim W = n :=
    (topologicalKrullDim_opens_eq hW U).symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hla)
  haveI : CompactSpace W := (hWv.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sW hsm hdimW
  have hPWT : IsPairWith sW n KW (Divisor.toQDivisor T) :=
    ⟨hW, hKW, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  obtain ⟨cT, hcT⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPWT.isPair hKW D'
  -- `e = 1 + a(D', W, T)`: discrepancies are local
  obtain ⟨hYU, hfU, E', -, hvU, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPWT D' U ⟨_, hηmem, hηU⟩
  have hcU := (hiff cT).1 hcT
  have hpU : IsProper (D'.f ∣_ U) := by
    haveI : IsProper D'.f := hD'p
    infer_instance
  have hLU := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcU hpU
  rw [toRDivisor_restrictOpen_sncComplement hT] at hLU
  have hbij := functionFieldMap_opens_ι_bijective U
  have hee : e = 1 + (cT : ℝ) := by
    refine MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hla hLU ?_
    ext x
    obtain ⟨y, rfl⟩ := hbij.2 x
    have h1 := congrArg (fun v => v y) hξD
    have h2 := congrArg (fun v => v y) (hξD'.trans hvU)
    simp only [Valuation.comap_apply] at h1 h2
    exact h1.symm.trans h2
  rw [hee]
  -- the coefficients of `T`
  have hcoeff1 : ∀ E ∈ T.support, (Divisor.toQDivisor T).coeff E = 1 := by
    intro E hE
    rw [MMP.Mori.Divisor.coeff_toQDivisor]
    have : T E = 1 := (hT E).resolve_left (Finsupp.mem_support_iff.1 hE)
    rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, this]; simp
  by_cases h2 : 2 ≤ codimension D'.center
  · -- exceptional: the estimate on logarithmic forms
    have hcod : 2 ≤ Order.coheight (D'.f D'.E.genericPoint) := by
      rwa [MMP.Positivity.DivisorOver.codimension_center] at h2
    have hS : (Divisor.toQDivisor T).support ⊆ T.support := by
      intro P hP
      rw [Finsupp.mem_support_iff] at hP ⊢
      intro h
      exact hP ((MMP.Mori.Divisor.coeff_toQDivisor T P).trans (by
        rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, h]; simp))
    have hsnc' : MMP.Mori.DivisorWithCoeffs.IsSNC sW
        (∑ E ∈ T.support, Finsupp.single E (1 : ℤ)) := by
      rw [← MMP.Intersection.eq_sum_single_of_isReducedEffective hT]
      exact hsnc
    obtain ⟨c', T', hc', hcard, hT'S, hT'x, hle⟩ :=
      le_isDiscrepancy_of_isSNC hW hsm hKW hS hsnc' (fun E hE => (hcoeff1 E hE).le) D' hcod hcT
    have hcc : c = c' := by
      rw [← MMP.Positivity.DivisorOver.codimension_center, hc] at hc'
      exact_mod_cast hc'
    subst hcc
    have hsum : ∑ G ∈ T', (1 - (Divisor.toQDivisor T).coeff G) = 0 :=
      Finset.sum_eq_zero fun G hG => by rw [hcoeff1 G (hT'S hG)]; ring
    rw [hsum] at hle
    have hsub : T' ⊆ MMP.Fourfold.sncIndexSet T (D'.center : Set W) := by
      intro G hG
      refine Finset.mem_filter.2 ⟨hT'S hG, ?_⟩
      rw [D'.center_eq_closure_genericPoint]
      exact closure_singleton_subset_support G (hT'x G hG)
    have hcardJ : (T'.card : ℝ) ≤ (MMP.Fourfold.sncIndexSet T (D'.center : Set W)).card := by
      exact_mod_cast Finset.card_le_card hsub
    have hle' : (-1 : ℝ) + ((c : ℝ) - T'.card) ≤ cT := by
      exact_mod_cast (by simpa using hle : (-1 : ℚ) + ((c : ℚ) - T'.card) ≤ cT)
    linarith
  · -- not exceptional: `D'` has the valuation of a prime divisor `P` of `W`
    have hex := (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hW D').not.mp h2
    simp only [not_forall, not_not] at hex
    obtain ⟨P, hvP⟩ := hex
    obtain ⟨cP, hcP⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPWT.isPair hKW
      (DivisorOver.ofPrimeDivisor k hW P)
    have hL1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcT hD'p
    have hL2 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcP
      (show IsProper (𝟙 W) from inferInstance)
    have hTP : (1 : ℝ) + cT = 1 + cP :=
      MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hL1 hL2 hvP
    rw [hTP, MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hW hcP]
    have hc1 : (c : ℕ∞) < 2 := hc ▸ lt_of_not_ge h2
    have hc1' : (c : ℝ) ≤ 1 := by
      have : c < 2 := by exact_mod_cast hc1
      exact_mod_cast (show c ≤ 1 by omega)
    by_cases hPT : P ∈ T.support
    · have hPJ : P ∈ MMP.Fourfold.sncIndexSet T (D'.center : Set W) := by
        refine Finset.mem_filter.2 ⟨hPT, ?_⟩
        rw [MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hWv hvP,
          (DivisorOver.ofPrimeDivisor k hW P).center_eq_closure_genericPoint,
          AlgebraicGeometry.PrimeDivisor.support_eq_closure P]
        rfl
      have h1 : (1 : ℝ) ≤ (MMP.Fourfold.sncIndexSet T (D'.center : Set W)).card := by
        exact_mod_cast Finset.card_pos.mpr ⟨P, hPJ⟩
      rw [hcoeff1 P hPT]
      push_cast
      linarith
    · have h0 : (Divisor.toQDivisor T).coeff P = 0 := by
        rw [MMP.Mori.Divisor.coeff_toQDivisor, MMP.Mori.DivisorWithCoeffs.coeff_apply,
          Finsupp.notMem_support_iff.1 hPT]
        simp
      rw [h0]
      push_cast
      have : (0 : ℝ) ≤ (MMP.Fourfold.sncIndexSet T (D'.center : Set W)).card := by positivity
      linarith

end CodimensionBound

end MMP.Fourfold
