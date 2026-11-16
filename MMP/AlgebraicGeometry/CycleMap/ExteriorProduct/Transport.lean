module

public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.Fundamental
public import MMP.AlgebraicGeometry.CycleMap.OpenRestriction.Fundamental
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductNatural
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap

/-!
# Transport of fundamental classes and of exterior products (Fulton, Example 19.1.9)

* `MMP.IsVarietyFundamentalClass.pushforward_of_isIso`: an isomorphism of
  complex varieties carries the fundamental class to the fundamental class.
* `MMP.pushforward_productClass`: for proper morphisms `f : V → X`, `g : W → Y`
  over `ℂ` and a morphism `F : V × W → X × Y` over `f` and `g`,
  `F_*(a × b) = f_* a × g_* b`, the exterior products being read on `(V × W)(ℂ)` and
  `(X × Y)(ℂ)` (`lem_ext_c19_exterior_product_natural`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TensorProduct Limits
open MMP.UnderlyingSpace MMP.FundamentalClass
open MMP.BorelMooreCross MMP.SingularCross

namespace MMP

open MMP.Intersection.Scheme (dimension)
open MMP

open borelMooreHomology

section Iso

variable {R : Type} [CommRing R] {A B : Scheme.{0}} [A.Over (Spec (.of ℂ))]
  [B.Over (Spec (.of ℂ))] [IsComplexScheme A] [IsComplexScheme B]
  (g : A ⟶ B) [IsIso g] [g.IsOver (Spec (.of ℂ))]

/-- An isomorphism over `ℂ` is onto on `ℂ`-points. -/
lemma opensRangeMap_eq_top_of_isIso [IsIntegral A] [IsIntegral B] : opensRangeMap g = ⊤ := by
  have : (inv g).IsOver (Spec (.of ℂ)) := ⟨by rw [IsIso.inv_comp_eq, comp_over]⟩
  ext p
  simp only [Opens.coe_top, Set.mem_univ, iff_true]
  refine ⟨mapFun (inv g) p, UnderlyingSpace.ext ?_⟩
  change (mapFun g (mapFun (inv g) p)).toHom = _
  rw [toHom_mapFun, toHom_mapFun, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **Fundamental classes are carried by isomorphisms.** For an isomorphism `g : A → B` of
complex varieties of dimension `n` over `ℂ`, `g_* cl(A) = cl(B)`. -/
theorem IsVarietyFundamentalClass.pushforward_of_isIso [IsIntegral A] [IsIntegral B] {n : ℕ}
    {hnA : (n : WithBot ℕ∞) = dimension A} (hnB : (n : WithBot ℕ∞) = dimension B)
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ A)) (2 * n : ℕ)}
    (hc : IsVarietyFundamentalClass R hnA c) :
    IsVarietyFundamentalClass R hnB
      ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) g))
        (isProperMap_map (K := ℂ) g) (2 * n : ℕ)).hom c) := by
  obtain ⟨cB, hcB, -, -⟩ := existsUnique_isVarietyFundamentalClass (R := R) hnB
  have h := hcB.pushforward_restrict_opensRangeMap R g hnA hnB
  rw [hc.eq h]
  convert hcB using 1
  rw [pushforward_comp_apply R _ _ (homeomorphOpensRangeMap g).symm.isProperMap
    (isProperMap_map (K := ℂ) g) ((isProperMap_map (K := ℂ) g).comp
      (homeomorphOpensRangeMap g).symm.isProperMap)]
  have hincl : IsProperMap (inclHom (Z := TopCat.of (UnderlyingSpace ℂ B)) (opensRangeMap g)) := by
    rw [opensRangeMap_eq_top_of_isIso]
    exact (Homeomorph.Set.univ _).isProperMap
  refine (pushforward_apply_congr R
    (f := TopCat.ofHom ((homeomorphOpensRangeMap g).symm :
      C(opensRangeMap g, UnderlyingSpace ℂ A)) ≫ TopCat.ofHom (map (K := ℂ) g))
    (g := inclHom (Z := TopCat.of (UnderlyingSpace ℂ B)) (opensRangeMap g))
    (ConcreteCategory.hom_ext _ _ fun y ↦ mapFun_homeomorphOpensRangeMap_symm_apply g y) _ hincl
    _ _).trans ?_
  exact pushforward_inclHom_restrict_of_eq_top R (opensRangeMap_eq_top_of_isIso g) hincl _ cB

end Iso

section Product

variable {R : Type} [CommRing R] {V W X Y : Scheme.{0}} [V.Over (Spec (.of ℂ))]
  [W.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
  [LocallyOfFiniteType (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))]
  [T2Space (UnderlyingSpace ℂ V)] [T2Space (UnderlyingSpace ℂ W)]
  [T2Space (UnderlyingSpace ℂ X)] [T2Space (UnderlyingSpace ℂ Y)]
  [T2Space (UnderlyingSpace ℂ (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ))))]
  [T2Space (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))))]
  (f : V ⟶ X) (g : W ⟶ Y) [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] [IsProper f]
  [IsProper g]
  (F : pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)) ⟶
    pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))
  [F.IsOver (Spec (.of ℂ))] [IsProper F]

include f g in
/-- **The exterior product commutes with proper push-forward, on underlying spaces of
products**: `F_*(a × b) = f_* a × g_* b` for `F : V × W → X × Y` over `f` and `g`. -/
theorem pushforward_productClass
    (hFf : F ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f)
    (hFg : F ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g) {k l : ℕ}
    (cV : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ))
    (cW : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ W)) (2 * l : ℕ)) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) F))
        (isProperMap_map (K := ℂ) F) (2 * (k + l) : ℕ)).hom (productClass R V W cV cW) =
      productClass R X Y
        ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
          (isProperMap_map (K := ℂ) f) (2 * k : ℕ)).hom cV)
        ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) g))
          (isProperMap_map (K := ℂ) g) (2 * l : ℕ)).hom cW) := by
  have hf := isProperMap_map (K := ℂ) f
  have hg := isProperMap_map (K := ℂ) g
  unfold productClass
  rw [← pushforward_exteriorProduct R (TopCat.ofHom (map (K := ℂ) f))
    (TopCat.ofHom (map (K := ℂ) g)) hf hg, ← pushforward_congrDegree]
  have hc : ∀ {A B C : TopCat.{0}} (u : A ⟶ B) (v : B ⟶ C), IsProperMap u → IsProperMap v →
      IsProperMap (u ≫ v) := fun u v hu hv ↦ hv.comp hu
  rw [pushforward_comp_apply R _ _ (productHomeomorph ℂ V W).symm.isProperMap
    (isProperMap_map (K := ℂ) F) (hc _ _ (productHomeomorph ℂ V W).symm.isProperMap
      (isProperMap_map (K := ℂ) F)),
    pushforward_comp_apply R (prodHom (TopCat.ofHom (map (K := ℂ) f))
      (TopCat.ofHom (map (K := ℂ) g)))
      (TopCat.ofHom ((productHomeomorph ℂ X Y).symm :
        C(UnderlyingSpace ℂ X × UnderlyingSpace ℂ Y,
          UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))))))
      (isProperMap_prodHom hf hg)
      (productHomeomorph ℂ X Y).symm.isProperMap
      (hc _ _ (isProperMap_prodHom hf hg) (productHomeomorph ℂ X Y).symm.isProperMap)]
  refine pushforward_apply_congr R (ConcreteCategory.hom_ext _ _ fun z ↦ ?_) _ _ _ _
  obtain ⟨w, rfl⟩ := (productHomeomorph ℂ V W).surjective z
  change mapFun F ((productHomeomorph ℂ V W).symm (productHomeomorph ℂ V W w)) =
    (productHomeomorph ℂ X Y).symm
      (mapFun f (productHomeomorph ℂ V W w).1, mapFun g (productHomeomorph ℂ V W w).2)
  rw [Homeomorph.symm_apply_apply, Homeomorph.eq_symm_apply, productHomeomorph_apply,
    productHomeomorph_apply]
  refine Prod.ext (UnderlyingSpace.ext ?_) (UnderlyingSpace.ext ?_)
  · simp only [toHom_mapFun, Category.assoc, hFf]
  · simp only [toHom_mapFun, Category.assoc, hFg]

end Product

end MMP
