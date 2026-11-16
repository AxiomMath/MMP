module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OpenRestriction
public import MMP.AlgebraicGeometry.CycleMap.Stacks.Pushforward
public import MMP.AlgebraicGeometry.CycleMap.Stacks.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Lift
public import MMP.AlgebraicGeometry.CycleMap.IsoExcisionGeneric
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreLongExact
public import MMP.AlgebraicTopology.FundamentalClass.Restriction
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenSubscheme
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenImmersionRange

/-!
# Excision for complex schemes whose cycle class map is an isomorphism (Fulton, Example 19.1.11(a))

Let `Y ⊆ X` be a closed subscheme of a complex scheme and `U = X - Y`. If `cl_Y` and `cl_U` are
isomorphisms on Stacks' Chow groups, so is `cl_X`.

*Proof* (Fulton). In the Borel–Moore exact sequence `H_{2k+1} Y → H_{2k+1} X → H_{2k+1} U` the
outer groups vanish, so `H_{2k+1} X = 0`; and since `H_{2k+1} U = 0`,
`0 → H_{2k} Y → H_{2k} X → H_{2k} U` is exact. The localization sequence of Stacks' Chow groups
`A_k Y → A_k X → A_k U → 0` is exact (Stacks 02RX), and `cl` commutes with `i_*`
(`MMP.Chow.chowCycleClass_properChowPushforward`) and `j^*` (`MMP.Chow.restrict_chowCycleClass`);
the five lemma (`MMP.bijective_of_exact_of_exact`) concludes.

## Main results

* `MMP.Chow.exact_chowPushforward_chowGroupRestrict`: the localization sequence at `A_k X`.
* `MMP.Chow.ChowCycleClassIsIso.of_excision`: **Fulton, Example 19.1.11(a)**.

## Implementation notes

The closed subscheme `Y` is given by an ideal sheaf `I` of `X`, and `U` by an open subscheme with underlying set the complement of the support of `I`; the structures of
`Y` and `U` over `ℂ` are any for which the inclusions are morphisms over `ℂ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Example 19.1.11.
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow
  MMP.UnderlyingSpace MMP.borelMooreHomology

namespace MMP.Chow

variable {R : Type} [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- **The localization sequence at `A_k X`** (Stacks 02RX): for a closed subscheme `Y` of `X` and
the open complement `U`, a class on `X` restricts to zero on `U` exactly when it is pushed forward
from `Y`. -/
theorem exact_chowPushforward_chowGroupRestrict (I : X.IdealSheafData)
    [I.subscheme.Over (Spec (.of ℂ))] [I.subschemeι.IsOver (Spec (.of ℂ))] (U : X.Opens)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))]
    (hU : (U : Set X) = (I.support : Set X)ᶜ) (k : ℤ) :
    Function.Exact
      (chowPushforwardOfIsClosedImmersion (fieldChowSituation ℂ) (I.subscheme ↘ Spec (.of ℂ))
        (X ↘ Spec (.of ℂ)) I.subschemeι (comp_over _ _) k)
      (chowGroupRestrict (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (U.toScheme ↘ Spec (.of ℂ))
        U.ι (comp_over _ _) k) := by
  have hcompl : Set.range I.subschemeι.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Opens.range_ι, hU, compl_compl]
  intro β
  refine ⟨exists_chowPushforwardOfIsClosedImmersion_eq_of_chowGroupRestrict_eq_zero _ _ _ _
    I.subschemeι (comp_over _ _) U.ι (comp_over _ _) hcompl k β, ?_⟩
  rintro ⟨γ, rfl⟩
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ γ
  have hz := (cycleGroupRestrict_eq_zero_iff (fieldChowSituation ℂ) _ _ _ I.subschemeι
    (comp_over _ _) U.ι (comp_over _ _) hcompl k
    (properPushforward _ _ _ I.subschemeι (comp_over _ _) k c)).mpr ⟨c, rfl⟩
  rw [chowPushforwardOfIsClosedImmersion_mk, chowGroupRestrict_mk, hz, map_zero]

/-- Push-forward along the identification of two equal open subsets is bijective. -/
theorem bijective_pushforward_opensEqMap (M : ModuleCat.{0} R) {Z : TopCat.{0}}
    {V₁ V₂ : TopologicalSpace.Opens Z} (h : V₂ = V₁) (j : ℤ) :
    Function.Bijective (pushforward R M (FundamentalClass.opensEqMap h)
      (FundamentalClass.isProperMap_opensEqMap h) j).hom := by
  subst h
  exact bijective_pushforward_of_eq_id R M _ _ (TopCat.ext fun _ ↦ rfl) j

/-- For a closed immersion `i : Z ⟶ X`, `i_*` is injective in degree `n` when `H_{n+1}` of the
complement of `Z` vanishes. -/
theorem injective_pushforward_map_of_subsingleton (M : ModuleCat.{0} R) {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] (n : ℤ)
    (hW : Subsingleton (borelMooreHomology R M (TopCat.of (complOpens
      (Y := TopCat.of (UnderlyingSpace ℂ X)) (isClosed_range_map_of_isClosedImmersion i)))
      (n + 1))) :
    Function.Injective (pushforward R M (TopCat.ofHom (map (K := ℂ) i))
      (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap n).hom := by
  obtain ⟨δ, h1, -, -⟩ := IsComplexScheme.exists_borelMooreHomology_longExact R M X i
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := (h1 n x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

/-- For a closed immersion `i : Z ⟶ X`, `H_n X` vanishes when `H_n Z` and `H_n` of the complement
of `Z` do. -/
theorem subsingleton_of_subsingleton_complOpens (M : ModuleCat.{0} R) {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] (n : ℤ)
    (hZ : Subsingleton (borelMooreHomology R M (TopCat.of (UnderlyingSpace ℂ Z)) n))
    (hW : Subsingleton (borelMooreHomology R M (TopCat.of (complOpens
      (Y := TopCat.of (UnderlyingSpace ℂ X)) (isClosed_range_map_of_isClosedImmersion i))) n)) :
    Subsingleton (borelMooreHomology R M (TopCat.of (UnderlyingSpace ℂ X)) n) := by
  obtain ⟨-, -, h2, -⟩ := IsComplexScheme.exists_borelMooreHomology_longExact R M X i
  refine subsingleton_of_forall_eq 0 fun h ↦ ?_
  obtain ⟨y, rfl⟩ := (h2 n h).1 (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero]

/-- **Fulton, Example 19.1.11(a), on Stacks' Chow groups.** Let `Y ⊆ X` be a closed subscheme of
a complex scheme `X` (cut out by the ideal sheaf `I`) and `U = X - Y` (an open subscheme with
underlying set the complement of the support of `I`). If `cl_Y` and `cl_U` are isomorphisms, then
`cl_X` is an isomorphism. -/
theorem ChowCycleClassIsIso.of_excision (I : X.IdealSheafData)
    [I.subscheme.Over (Spec (.of ℂ))] [I.subschemeι.IsOver (Spec (.of ℂ))] (U : X.Opens)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))]
    (hU : (U : Set X) = (I.support : Set X)ᶜ)
    (hY : ChowCycleClassIsIso R I.subscheme) (hUi : ChowCycleClassIsIso R U.toScheme) :
    ChowCycleClassIsIso R X := by
  set i := I.subschemeι
  set M := ModuleCat.of R R
  have hZ := UnderlyingSpace.isClosed_range_map_of_isClosedImmersion i
  set W := complOpens (Y := TopCat.of (UnderlyingSpace ℂ X)) hZ
  have hVW : opensRangeMap U.ι = W := by
    ext p
    change p ∈ opensRangeMap U.ι ↔ p ∉ Set.range (mapFun (K := ℂ) i)
    rw [mem_opensRangeMap_ι_iff, ← SetLike.mem_coe, hU, range_mapFun_of_isClosedImmersion,
      Set.mem_setOf_eq, Scheme.IdealSheafData.range_subschemeι]
    rfl
  let e := homeomorphOpensRangeMap U.ι
  let ψ : ∀ j : ℤ, borelMooreHomology R M (TopCat.of (UnderlyingSpace ℂ U.toScheme)) j →
      borelMooreHomology R M (TopCat.of W) j := fun j x ↦
    (pushforward R M (FundamentalClass.opensEqMap hVW)
      (FundamentalClass.isProperMap_opensEqMap hVW) j).hom
      ((pushforward R M (TopCat.ofHom (e : C(UnderlyingSpace ℂ U.toScheme, opensRangeMap U.ι)))
        e.isProperMap j).hom x)
  have hψ (j : ℤ) : Function.Bijective (ψ j) :=
    (bijective_pushforward_opensEqMap M hVW j).comp <|
      Function.bijective_iff_has_inverse.2 ⟨fun y ↦ (pushforward R M
        (TopCat.ofHom (e.symm : C(opensRangeMap U.ι, UnderlyingSpace ℂ U.toScheme)))
        e.symm.isProperMap j).hom y, pushforward_symm_pushforward_homeomorph R M e j,
        pushforward_symm_pushforward_homeomorph R M e.symm j⟩
  obtain ⟨-, -, h2, -⟩ := IsComplexScheme.exists_borelMooreHomology_longExact R M X i
  refine ⟨fun k ↦ ?_, fun k ↦ have := hUi.subsingleton_odd k
    subsingleton_of_subsingleton_complOpens M i _ (hY.subsingleton_odd k) (hψ _).2.subsingleton⟩
  have : Subsingleton (borelMooreHomology R M (TopCat.of (UnderlyingSpace ℂ U.toScheme))
      (((2 * k : ℕ) : ℤ) + 1)) := Nat.cast_succ (R := ℤ) (2 * k) ▸ hUi.subsingleton_odd k
  refine bijective_of_exact_of_exact
    (iA := chowPushforwardOfIsClosedImmersion (fieldChowSituation ℂ)
      (I.subscheme ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) i (comp_over _ _) k)
    (jA := chowGroupRestrict (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
      (U.toScheme ↘ Spec (.of ℂ)) U.ι (comp_over _ _) k)
    (iH := (pushforward R M (TopCat.ofHom (map (K := ℂ) i))
      (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap ((2 * k : ℕ) : ℤ)).hom)
    (jH := (restrict R M W ((2 * k : ℕ) : ℤ)).hom)
    (clY := chowCycleClass (X := I.subscheme) R k)
    (clU := (AddMonoidHom.mk' (ψ ((2 * k : ℕ) : ℤ)) fun a b ↦ by simp [ψ]).comp
      (chowCycleClass (X := U.toScheme) R k))
    (fun b ↦ chowCycleClass_properChowPushforward R i _ b) (fun a ↦ ?_)
    (exact_chowPushforward_chowGroupRestrict I U hU k)
    (chowGroupRestrict_surjective _ _ _ U.ι (comp_over _ _) k)
    (injective_pushforward_map_of_subsingleton M i _ (hψ _).2.subsingleton) (h2 ((2 * k : ℕ) : ℤ))
    (hY.bijective k) ((hψ _).comp (hUi.bijective k))
  change (restrict R M W ((2 * k : ℕ) : ℤ)).hom (chowCycleClass R k a) =
    ψ _ (chowCycleClass (X := U.toScheme) R k _)
  rw [FundamentalClass.restrict_eq_pushforward_opensEqMap hVW]
  exact congrArg _ (restrict_chowCycleClass R U.ι a)

end MMP.Chow
