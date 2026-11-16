module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.Pullback

/-!
# Crepant dlt lifts, normalized graphs and graph divisors

Let `(X, B)` be a projective lc pair. A *crepant dlt lift* of `(X, B)` is a projective birational
morphism `p : U ⟶ X` from a `ℚ`-factorial variety `U` such that, with
`Δ = p⁻¹_* B + Exc(p)_red`, the pair `(U, Δ)` is dlt and `K_U + Δ = p^*(K_X + B)`.

For a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, let `Γ ⊆ X⁻ ×_Z X⁺` be the closure of the graph of
the birational map `(f⁺)⁻¹ ∘ f⁻` and `ν : G ⟶ Γ` its normalization; with `u : G ⟶ X⁻` and
`v : G ⟶ X⁺` the two projections composed with `ν`, `(G, u, v)` is the *normalized graph*. The
*graph divisor* is the `ℚ`-Cartier `ℚ`-divisor `H = u^* D⁻ - v^* D⁺` on `G`, where
`D^± = K_{X^±} + B^±`.

## Main definitions

* `MMP.Fourfold.IsCrepantDltLift`: crepant dlt lifts of a projective lc pair.
* `MMP.Fourfold.IsNormalizedGraph`: normalized graphs of two morphisms to a common base.
* `MMP.Fourfold.IsGraphDivisor`: the graph divisor of a step diagram.

## Main results

* `MMP.Fourfold.IsCrepantDltLift.eq`: the boundary of a crepant dlt lift is determined
  by the morphism.
* `MMP.Fourfold.IsGraphDivisor.eq`: the graph divisor is unique.

## Implementation notes

The boundary `Δ` of a crepant dlt lift is an argument, constrained to be
`p⁻¹_* B + Exc(p)_red`: `p⁻¹_* B` is the birational transform of `B` under the inverse of `p`
(`MMP.Flips.birationalInverseTransform`) and `Exc(p)_red` is the reduced divisor whose prime
components are the prime divisors contained in the exceptional locus of `p`
(`MMP.Intersection.IsExceptionalDivisorSum`). The equality `K_U + Δ = p^*(K_X + B)`, with `K_U`
the canonical divisor of `U` matching `K_X`, says that `-coeff_F(Δ)` is the discrepancy
`a(F, X, B)` of every prime divisor `F` of `U`, i.e. that `Δ` is the crepant boundary of `(X, B)`
on `U` (`MMP.Mori.IsCrepantBoundary`). The variety structure of `U` is `p ≫ s_X`.

The normalized graph is characterized up to isomorphism: `G` is a normal integral scheme with
birational morphisms `u : G ⟶ X⁻`, `v : G ⟶ X⁺` such that `f⁻ ∘ u = f⁺ ∘ v` and the induced
morphism `(u, v) : G ⟶ X⁻ ×_Z X⁺` is finite. When `f^±` are birational, `(u, v)` maps the generic
point of `G` to the generic point of the graph of `(f⁺)⁻¹ ∘ f⁻` (both function field maps to
`k(G)` agree on `k(Z) = k(X^±)`), so its image is the closure `Γ`, and `G ⟶ Γ` is a finite
birational morphism from a normal integral scheme, that is, the normalization of `Γ`.

The graph divisor is stated as a predicate on `H`: `H = H⁻ - H⁺` with `H⁻` the pull-back
`u^* D⁻` and `H⁺` the pull-back `v^* D⁺` of the `ℚ`-Cartier divisors `D^±`
(`MMP.Mori.QDivisor.IsPullback`); as in `MMP.Fourfold.IsFourfoldStepDiagram`, the canonical divisor
of `X⁺` is `(f⁺)⁻¹_* f⁻_* K⁻`. That `H` is `ℚ`-Cartier is a consequence.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Crepant dlt lifts -/

section CrepantDltLift

variable {k : Type u} [Field k] {X U : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]

/-- A *crepant dlt lift* `p : U ⟶ X` of a projective lc pair `(X, B)` with canonical divisor `K`:
`X` is a projective variety over `k` and `(X, B)` is log canonical, `p` is a projective birational
morphism, `U` (over `k` by `p ≫ s_X`) is `ℚ`-factorial, `Δ = p⁻¹_* B + Exc(p)_red`, the pair
`(U, Δ)` is dlt and `K_U + Δ = p^*(K_X + B)`: `Δ` is the crepant boundary of `(X, B)` on `U`. -/
@[mmp "def_oai4_crepant_dlt_lift"]
structure IsCrepantDltLift (K : Divisor X) (B : QDivisor X) (p : U ⟶ X) (Δ : QDivisor U) :
    Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety k sX
  isLogCanonicalPair : MMP.Intersection.IsLogCanonicalPair sX B
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sX n
  isProjectiveMorphism : IsProjectiveMorphism p
  isBirationalMorphism : IsBirationalMorphism p
  isQFactorial : IsQFactorial (p ≫ sX)
  boundary_eq : ∃ E : Divisor U, MMP.Intersection.IsExceptionalDivisorSum p E ∧
    Δ = MMP.Flips.birationalInverseTransform p isBirationalMorphism B + Divisor.toQDivisor E
  isDltPair : MMP.Intersection.IsDltPair (p ≫ sX) Δ
  isCrepantBoundary :
    ∃ n : ℕ, IsCrepantBoundary sX n K B p isQFactorial.1 isBirationalMorphism Δ

variable {sX} {K : Divisor X} {B : QDivisor X} {p : U ⟶ X} {Δ : QDivisor U}

/-- The boundary of a crepant dlt lift is determined by `p`: it is `p⁻¹_* B + Exc(p)_red`. -/
theorem IsCrepantDltLift.eq {Δ' : QDivisor U} (h : IsCrepantDltLift sX K B p Δ)
    (h' : IsCrepantDltLift sX K B p Δ') : Δ = Δ' := by
  obtain ⟨E, hE, hΔ⟩ := h.boundary_eq
  obtain ⟨E', hE', hΔ'⟩ := h'.boundary_eq
  rw [hΔ, hΔ', hE.eq hE']

end CrepantDltLift

/-! ### Normalized graphs -/

section NormalizedGraph

variable {Xm Xp Z G : Scheme.{u}}

/-- `(G, u, v)` is a *normalized graph* of `f⁻ : X⁻ ⟶ Z` and `f⁺ : X⁺ ⟶ Z`: `G` is a normal
integral scheme, `u : G ⟶ X⁻` and `v : G ⟶ X⁺` are birational with `f⁻ ∘ u = f⁺ ∘ v`, and the
induced morphism `(u, v) : G ⟶ X⁻ ×_Z X⁺` is finite. For a step diagram this is the normalization
`ν : G ⟶ Γ` of the closure `Γ ⊆ X⁻ ×_Z X⁺` of the graph of `(f⁺)⁻¹ ∘ f⁻`, with `u`, `v` the two
projections composed with `ν`. -/
@[mmp "def_oai4_normalized_graph"]
structure IsNormalizedGraph (fm : Xm ⟶ Z) (fp : Xp ⟶ Z) (u : G ⟶ Xm) (v : G ⟶ Xp) : Prop where
  isIntegral : IsIntegral G
  isNormal : IsNormal G
  comp_eq : u ≫ fm = v ≫ fp
  isFinite : IsFinite (pullback.lift u v comp_eq)
  isBirationalMorphism_minus : IsBirationalMorphism u
  isBirationalMorphism_plus : IsBirationalMorphism v

end NormalizedGraph

/-! ### Graph divisors -/

section GraphDivisor

variable {Xm Xp Z G : Scheme.{0}} [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]

/-- The *graph divisor* of a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` (canonical divisors `K⁻` and
`K⁺ = (f⁺)⁻¹_* f⁻_* K⁻`) with normalized graph `(G, u, v)`: the `ℚ`-divisor
`H = u^* D⁻ - v^* D⁺` on `G`, where `D⁻ = K⁻ + B⁻`, `D⁺ = K⁺ + B⁺` and `u^*`, `v^*` are the
pull-backs of `ℚ`-Cartier `ℚ`-divisors. -/
@[mmp "def_oai4_graph_divisor"]
structure IsGraphDivisor (sXm : Xm ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sXp : Xp ⟶ Spec (.of ℂ)) (K : Divisor Xm) (B : QDivisor Xm) (fm : Xm ⟶ Z) (fp : Xp ⟶ Z)
    (u : G ⟶ Xm) (v : G ⟶ Xp) (H : QDivisor G) : Prop where
  isFourfoldStepDiagram : IsFourfoldStepDiagram sXm sZ sXp K B fm fp
  isNormalizedGraph : IsNormalizedGraph fm fp u v
  exists_pullback : ∃ (Hm Hp : QDivisor G)
    (hm : ∀ T : irreducibleComponents G,
      u (componentGenericPoint G T) ∉ (Divisor.toQDivisor K + B).supp)
    (hp : ∀ T : irreducibleComponents G, v (componentGenericPoint G T) ∉
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).supp),
    (Divisor.toQDivisor K + B).IsPullback u hm Hm ∧
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).IsPullback v hp Hp ∧
      H = Hm - Hp

variable {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
  {H : QDivisor G}

/-- The graph divisor of a step diagram with normalized graph `(G, u, v)` is unique. -/
theorem IsGraphDivisor.eq [CompactSpace G] {H' : QDivisor G}
    (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H)
    (h' : IsGraphDivisor sXm sZ sXp K B fm fp u v H') : H = H' := by
  obtain ⟨Hm, Hp, hm, hp, hHm, hHp, rfl⟩ := h.exists_pullback
  obtain ⟨Hm', Hp', hm', hp', hHm', hHp', rfl⟩ := h'.exists_pullback
  have hD := h.isFourfoldStepDiagram
  rw [← hHm.pullback_eq hD.isQCartier_minus, ← hHm'.pullback_eq hD.isQCartier_minus,
    ← hHp.pullback_eq hD.isQCartier_plus, ← hHp'.pullback_eq hD.isQCartier_plus]

end GraphDivisor

end MMP.Fourfold
