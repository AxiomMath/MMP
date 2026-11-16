module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksComponent
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Finite
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.ThomChartGeneric
public import MMP.AlgebraicGeometry.CycleMap.TopClassDetectedLocally
public import MMP.AlgebraicTopology.ThomClass.OfRank
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ComplexSchemeSubscheme

/-!
# Fulton's Lemma 19.1.3 on Stacks cycles, for a normal variety

Let `ℰ` be a quasi-coherent `𝒪_X`-module, locally free of rank one, on a complex variety `X` of
dimension `k + 1`, and `σ : X ⟶ 𝐕(ℰ)` a section of `π : 𝐕(ℰ) ⟶ X` other than the zero section,
with zero scheme `D = Z(σ)` (`MMP.Modules.zeroLocus`). Fulton's Lemma 19.1.3 states
`σ^*(u_ℰ) ∩ cl(X) = cl_D([D])` in `H_{2k} D`. Here `u_ℰ` is the Thom class of `𝐕(ℰ)`, `[D]` is
Stacks' cycle `[D]_k` of `D` (Tag 02QU) and `cl_D` the cycle class `MMP.Chow.cycleClass` on
Stacks' cycles, so the statement involves no Fulton bundles or cycles
(`MMP.Modules.LocalizedFirstChernFormula`).

It is proved here for normal `X`: the formula is detected near general points of the components
of `D` (`MMP.Modules.localizedFirstChernFormula_of_forall_restrict`), where both sides are
computed in local holomorphic coordinates
(`MMP.Modules.exists_opens_restrict_localizedTopChernCap_eq_cycleClass`).

## Main definitions and results

* `MMP.Modules.LocalizedFirstChernFormula`.
* `MMP.Modules.LocalizedFirstChernFormula.of_isNormal`.

The general case reduces to the normal one along the normalization `ν : X̃ → X`, using
`ν_*[D̃]_k = [D]_k`; on Stacks cycles that is Stacks'
`properPushforward_zeroSchemePullbackMap_cycleAssociatedToClosedSubscheme`, for Stacks' zero
schemes of sections of invertible sheaves.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Lemma 19.1.3 and Proposition 19.1.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Stacks.Chow
open MMP.UnderlyingSpace
open scoped MMP.SubschemeOver

namespace MMP.Modules

open MMP
open MMP.Intersection.Scheme (dimension)

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- **The formula of Fulton's Lemma 19.1.3, for a Stacks line bundle, on Stacks cycles**, for a
section `σ` of the line bundle `𝐕(ℰ) ⟶ X` of a quasi-coherent `𝒪_X`-module `ℰ`, locally free of
rank one, on a complex variety `X` of dimension `k + 1`, with zero scheme `D = Z(σ)`: for every
fundamental class `cl(X) ∈ H_{2k+2} X`, `σ^*(u_ℰ) ∩ cl(X) = cl_D([D]_k)` in `H_{2k} D`, where
`[D]_k` is Stacks' cycle of `D` and `H_* D` is identified with `H_*(σ⁻¹(0(X(ℂ))))` by
`D(ℂ) ≅ σ⁻¹(0(X(ℂ)))`. -/
def LocalizedFirstChernFormula [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    [QuasiCompact (X ↘ Spec (.of ℂ))] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = dimension X) (E : X.Modules) [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))] : Prop :=
  ∀ μ, IsVarietyFundamentalClass R hn μ →
    borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroLocusHom σ)
        (isProperMap_zeroLocusHom σ) (2 * k : ℕ)
        (Chow.cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k)) =
      BorelMooreCross.congrDegree R _ (by push_cast; ring) (localizedTopChernCap σ R 1 _ μ)

variable {E : X.Modules} [E.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
  {σ : X ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))]

/-- **Lemma 19.1.3 on Stacks cycles is detected near general points of `D`.** If, for every
fundamental class `cl(X)`, each irreducible component of `D = Z(σ)` contains a non-empty open
`W ⊆ D(ℂ)` of its regular part, missing the other components, on which `σ^*(u_ℰ) ∩ cl(X)` and
`cl_D([D]_k)` restrict to the same class, then `σ^*(u_ℰ) ∩ cl(X) = cl_D([D]_k)`. -/
theorem localizedFirstChernFormula_of_forall_restrict [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = dimension X)
    (hD : dimension (zeroLocus E σ).subscheme ≤ k)
    (h : ∀ μ, IsVarietyFundamentalClass R hn μ →
      ∀ j : irreducibleComponents (zeroLocus E σ).subscheme,
      ∃ W : TopologicalSpace.Opens (UnderlyingSpace ℂ (zeroLocus E σ).subscheme),
        (W : Set (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)).Nonempty ∧
        (W : Set (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)) ⊆
          mapFun (K := ℂ) (irreducibleComponentι (zeroLocus E σ).subscheme j) ''
            regularPart ℂ (irreducibleComponentScheme (zeroLocus E σ).subscheme j) ∧
        (∀ i, i ≠ j → Disjoint (W : Set (UnderlyingSpace ℂ (zeroLocus E σ).subscheme))
          (range (mapFun (K := ℂ) (irreducibleComponentι (zeroLocus E σ).subscheme i)))) ∧
        borelMooreHomology.restrict R (ModuleCat.of R R)
            (Y := TopCat.of (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)) W (2 * k : ℕ)
            (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroLocusInvHom σ)
              (isProperMap_zeroLocusInvHom σ) (2 * k : ℕ)
              (BorelMooreCross.congrDegree R _ (by push_cast; ring)
                (localizedTopChernCap σ R 1 _ μ))) =
          borelMooreHomology.restrict R (ModuleCat.of R R)
            (Y := TopCat.of (UnderlyingSpace ℂ (zeroLocus E σ).subscheme)) W (2 * k : ℕ)
            (Chow.cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
              ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k))) :
    LocalizedFirstChernFormula R hn E σ := by
  intro μ hμ
  choose W hne hreg hdisj hW using h μ hμ
  have key : Chow.cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        ((zeroLocus E σ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) k) =
      borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroLocusInvHom σ)
        (isProperMap_zeroLocusInvHom σ) (2 * k : ℕ)
        (BorelMooreCross.congrDegree R _
          (show ((2 * (k + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ) by push_cast; ring)
          (localizedTopChernCap σ R 1 ((2 * (k + 1) : ℕ) : ℤ) μ)) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_restrict_eq_zero_of_dimension_le R hD W hne hreg
      (fun i j hij ↦ hdisj j i hij) _ fun j ↦ ?_
    rw [map_sub, ← hW j, sub_self]
  rw [key, pushforward_zeroLocusHom_pushforward_zeroLocusInvHom]

/-- **Fulton's Lemma 19.1.3 for a Stacks line bundle, on Stacks cycles, for a normal variety.**
Let `X` be a normal complex variety of dimension `k + 1`, `ℰ` a quasi-coherent `𝒪_X`-module,
locally free of rank one, and `σ` a section of `𝐕(ℰ) ⟶ X` other than the zero section. Then
`σ^*(u_ℰ) ∩ cl(X) = cl_D([D]_k)` for `D = Z(σ)` and every fundamental class `cl(X)`. -/
theorem LocalizedFirstChernFormula.of_isNormal [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] [IsNormal X] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = dimension X) (hσ : σ ≫ proj E = 𝟙 X)
    (h0 : σ ≠ zeroSection E) :
    LocalizedFirstChernFormula R hn E σ :=
  localizedFirstChernFormula_of_forall_restrict R hn (dimension_subscheme_zeroLocus_le hn hσ h0)
    fun _ hμ ↦ exists_opens_restrict_localizedTopChernCap_eq_cycleClass R hn hσ h0 hμ

end MMP.Modules
