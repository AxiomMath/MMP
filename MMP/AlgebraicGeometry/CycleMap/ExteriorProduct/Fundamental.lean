module

public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.FundamentalGeneric
public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.Homeomorph
public import MMP.AlgebraicTopology.FundamentalClass.Exists
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVarietyUnique
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
public import MMP.AlgebraicTopology.PoincareDuality.DualClassSupport
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductRestriction
public import MMP.AlgebraicTopology.CapProduct.Restriction

/-!
# The fundamental class of a product of varieties (Fulton, Example 19.1.9)

For complex varieties `V`, `W` of dimensions `k`, `l` with fundamental classes `cl(V)`, `cl(W)`,
the exterior product `cl(V) × cl(W) ∈ H_{2k+2l}(V(ℂ) × W(ℂ))`, read on `(V × W)(ℂ)` through the
homeomorphism `(V × W)(ℂ) ≃ₜ V(ℂ) × W(ℂ)`, is the fundamental class of `V × W`.

The proof follows Fulton: on `U = V_reg × W_reg ⊆ (V × W)_reg` the restriction of
`cl(V) × cl(W)` is `μ_{V_reg} × μ_{W_reg} = μ_U` (`lem_ext_c19_exterior_product_natural`,
`lem_c19_fundamental_class_restricts_open`, `lem_ext_c19_fundamental_class_product`, and the
comparison of the product orientation with the complex orientation of `V × W`). Since
`H_{2k+2l}(V × W)` is free on `cl(V × W)` (`lem_c19_fundamental_class_variety_well_defined`),
`cl(V) × cl(W) = r • cl(V × W)`; restricting to the connected manifold `U`, on which
`cl(V × W)` also restricts to `μ_U`, gives `r = 1`.

## Main results

* `MMP.IsFundamentalClass.reindex_finCongr`: transport of a fundamental class
  along an equality of dimensions.
* `MMP.IsVarietyFundamentalClass.pushforward_exteriorProduct`: `cl(V) × cl(W)` is
  the fundamental class of `V × W`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TensorProduct
open MMP.UnderlyingSpace MMP.FundamentalClass
open MMP.BorelMooreCross

namespace MMP

open MMP.Intersection.Scheme (dimension)
open MMP

section Reindex

universe u

variable {R : Type u} [CommRing R] {H : Type*} [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace H M]

/-- A fundamental class for a basis indexed by `Fin n` is one for the same basis indexed by
`Fin n'`, `n = n'`, in degree `n'`. -/
lemma IsFundamentalClass.reindex_finCongr {n n' : ℕ} (h : n = n') {b : Module.Basis (Fin n) ℝ H}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n} (hμ : IsFundamentalClass R b μ) :
    IsFundamentalClass R (b.reindex (finCongr h))
      (congrDegree R (TopCat.of M) (congrArg Nat.cast h) μ) := by
  subst h
  simpa [congrDegree_self] using hμ

end Reindex

section Detect

variable {R : Type} [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [IsIntegral X]

open borelMooreHomology in
/-- **The fundamental class is detected on a connected open subset of the regular part.** Let `X`
be a complex variety of dimension `n` and `O ⊆ X(ℂ)` open with `O ∩ X_reg(ℂ)` connected. A class
`c ∈ H_{2n} X` whose restriction to `O ∩ X_reg(ℂ)` is the fundamental class `μ_{O ∩ X_reg}` is
the fundamental class of `X`: `c = r • cl(X)` as `H_{2n} X` is free on `cl(X)`, and restricting
to `O ∩ X_reg` gives `r = 1`. -/
theorem IsVarietyFundamentalClass.of_isFundamentalClass_restrict {n : ℕ}
    (hn : (n : WithBot ℕ∞) = dimension X)
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * n : ℕ)}
    (O : Opens (UnderlyingSpace ℂ X)) [ConnectedSpace (regularOpensInter O)]
    (h : letI := regularChartedSpace (𝕜 := ℂ) hn
      IsFundamentalClass R (euclideanComplexOrientationBasis n)
        ((restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ X)) (regularOpensInter O)
          (2 * n : ℕ)).hom ((restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X))
            (regularOpens ℂ X) (2 * n : ℕ)).hom c))) :
    IsVarietyFundamentalClass R hn c := by
  letI := regularChartedSpace (𝕜 := ℂ) hn
  obtain ⟨c₀, hc₀, -, hbij⟩ := existsUnique_isVarietyFundamentalClass (R := R) hn
  obtain ⟨r, hr⟩ := hbij.2 c
  replace hr : r • c₀ = c := hr
  have h₀ := hc₀.isFundamentalClass_restrict O
  have heq := IsFundamentalClass.eq_of_connectedSpace' h₀ h
  have hfree := (topHomologyFreeOnFundamentalClass_and_bijective_dualityMap (R := R)
    (M := regularOpensInter O) (euclideanComplexOrientationBasis n)).1 _ h₀
  have hr1 : r = 1 := by
    refine hfree.1 ?_
    simp only [one_smul]
    rw [← map_smul, ← map_smul]
    change _ = (restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ X))
      (regularOpensInter O) (2 * n : ℕ)).hom ((restrict R (ModuleCat.of R R)
        (Y := TopCat.of (UnderlyingSpace ℂ X)) (regularOpens ℂ X) (2 * n : ℕ)).hom c₀)
    rw [hr]
    exact heq
  rwa [← hr, hr1, one_smul]

end Detect

/-- `prodOpensInv` is a proper map. -/
lemma borelMooreHomology.isProperMap_prodOpensInv {X Y : TopCat.{0}} (U : Opens X)
    (V : Opens Y) : IsProperMap (borelMooreHomology.prodOpensInv U V) :=
  (borelMooreHomology.prodOpensHomeo U V).symm.isProperMap

/-- A composite of proper morphisms of topological spaces is proper. -/
lemma isProperMap_comp {X Y Z : TopCat.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsProperMap f)
    (hg : IsProperMap g) : IsProperMap (f ≫ g) :=
  hg.comp hf

variable {R : Type} [CommRing R] (V W : Scheme.{0}) [V.Over (Spec (.of ℂ))]
  [W.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsComplexScheme W]
  [LocallyOfFiniteType (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))]
  [QuasiCompact (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))]
  [T2Space (UnderlyingSpace ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ))))]

open borelMooreHomology in
/-- `V_reg(ℂ) × W_reg(ℂ)`, as an open of `V(ℂ) × W(ℂ)`, is the preimage of `regularProdOpens V W`
under `V(ℂ) × W(ℂ) ≃ₜ (V × W)(ℂ)`. -/
lemma prodOpens_regularOpens_eq_comap :
    prodOpens (X := TopCat.of (UnderlyingSpace ℂ V)) (Y := TopCat.of (UnderlyingSpace ℂ W))
        (regularOpens ℂ V) (regularOpens ℂ W) =
      Opens.comap (TopCat.ofHom ((productHomeomorph ℂ V W).symm :
        C(UnderlyingSpace ℂ V × UnderlyingSpace ℂ W,
          UnderlyingSpace ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))))).hom
        (regularProdOpens V W) := by
  ext z
  change z ∈ (regularPart ℂ V ×ˢ regularPart ℂ W) ↔
    productHomeomorph ℂ V W ((productHomeomorph ℂ V W).symm z) ∈
      (regularPart ℂ V ×ˢ regularPart ℂ W)
  rw [Homeomorph.apply_symm_apply]

open borelMooreHomology in
/-- `ρ(cl(V) × cl(W)) = cl(V)|_{V_reg} × cl(W)|_{W_reg}`, for `ρ` the restriction to
`V_reg(ℂ) × W_reg(ℂ) ⊆ (V × W)_reg(ℂ)`, read on `V_reg(ℂ) × W_reg(ℂ)`. -/
lemma restrict_restrict_productClass {k l : ℕ}
    (cV : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ))
    (cW : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ W)) (2 * l : ℕ)) :
    (restrict R (ModuleCat.of R R)
        (Y := TopCat.of (regularOpens ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))))
        (regularOpensInter (regularProdOpens V W)) (2 * (k + l) : ℕ)).hom
      ((restrict R (ModuleCat.of R R)
          (Y := TopCat.of
            (UnderlyingSpace ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))))
          (regularOpens ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ))))
          (2 * (k + l) : ℕ)).hom
        (productClass R V W cV cW)) =
    (pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (regularProdHomeomorph V W :
        C(regularOpens ℂ V × regularOpens ℂ W, regularOpensInter (regularProdOpens V W))))
      (regularProdHomeomorph V W).isProperMap (2 * (k + l) : ℕ)).hom
      (congrDegree R _ (two_mul_add_two_mul_eq k l)
        (exteriorProduct R (TopCat.of (regularOpens ℂ V)) (TopCat.of (regularOpens ℂ W))
          (2 * k : ℕ) (2 * l : ℕ)
          ((restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
              (regularOpens ℂ V) (2 * k : ℕ)).hom cV ⊗ₜ
            (restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ W))
              (regularOpens ℂ W) (2 * l : ℕ)).hom cW))) := by
  set f : TopCat.of (UnderlyingSpace ℂ V × UnderlyingSpace ℂ W) ⟶
      TopCat.of (UnderlyingSpace ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))) :=
    TopCat.ofHom ((productHomeomorph ℂ V W).symm :
      C(UnderlyingSpace ℂ V × UnderlyingSpace ℂ W,
        UnderlyingSpace ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))))
  have hf : IsProperMap f := (productHomeomorph ℂ V W).symm.isProperMap
  set UV : Opens (TopCat.of (UnderlyingSpace ℂ V)) := regularOpens ℂ V
  set UW : Opens (TopCat.of (UnderlyingSpace ℂ W)) := regularOpens ℂ W
  have hO : prodOpens UV UW = Opens.comap f.hom (regularProdOpens V W) :=
    prodOpens_regularOpens_eq_comap V W
  set e := two_mul_add_two_mul_eq k l
  set E := exteriorProduct R (TopCat.of (UnderlyingSpace ℂ V)) (TopCat.of (UnderlyingSpace ℂ W))
    (2 * k : ℕ) (2 * l : ℕ) (cV ⊗ₜ cW)
  have h1 := restrict_restrict_apply R (ModuleCat.of R R)
    (Y := TopCat.of (UnderlyingSpace ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))))
    (regularOpens ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ))))
    (regularProdOpens_le V W) (2 * (k + l) : ℕ) (productClass R V W cV cW)
  have h2 := restrict_pushforward_apply R (ModuleCat.of R R) f hf (regularProdOpens V W)
    (2 * (k + l) : ℕ) (congrDegree R _ e E)
  erw [h1, h2]
  have h3 := restrict_eq_pushforward_opensEqMap (R := R) hO (2 * (k + l) : ℕ)
    (congrDegree R _ e E)
  have h3' := restrict_congrDegree (R := R) (prodOpens UV UW) e E
  have hinv := isProperMap_prodOpensInv UV UW
  have h4 := eq_pushforward_of_pushforward_eq R (prodOpensMap UV UW) (prodOpensInv UV UW)
    (isProperMap_prodOpensMap UV UW) hinv (ConcreteCategory.hom_ext _ _ fun x ↦ rfl) _
    (restrict_exteriorProduct R UV UW (2 * k : ℕ) (2 * l : ℕ) cV cW)
  have h5 := pushforward_congrDegree (R := R) (prodOpensInv UV UW) hinv e
  erw [h3, h3', h4, ← h5 _]
  have hO' := isProperMap_opensEqMap hO
  have hP := isProperMap_restrictPreimage f (regularProdOpens V W) hf
  have hS := isProperMap_subOpensMap
    (Y := TopCat.of (UnderlyingSpace ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))))
    (regularOpens ℂ (Limits.pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ))))
    (regularProdOpens_le V W)
  have hc₁ := isProperMap_comp hinv hO'
  have hc₂ := isProperMap_comp hc₁ hP
  have hc₃ := isProperMap_comp hc₂ hS
  let y := congrDegree R (TopCat.of (TopCat.of UV × TopCat.of UW)) e
    (exteriorProduct R (TopCat.of UV) (TopCat.of UW) (2 * k : ℕ) (2 * l : ℕ)
      ((restrict R (ModuleCat.of R R) UV (2 * k : ℕ)).hom cV ⊗ₜ
        (restrict R (ModuleCat.of R R) UW (2 * l : ℕ)).hom cW))
  have e1 := pushforward_comp_apply R _ _ hinv hO' hc₁ _ y
  have e2 := pushforward_comp_apply R _ _ hc₁ hP hc₂ _ y
  have e3 := pushforward_comp_apply R _ _ hc₂ hS hc₃ _ y
  exact (congrArg (fun z ↦ (pushforward R (ModuleCat.of R R) _ hS _).hom
      ((pushforward R (ModuleCat.of R R) _ hP _).hom z)) e1).trans
    ((congrArg (fun z ↦ (pushforward R (ModuleCat.of R R) _ hS _).hom z) e2).trans
      (e3.trans (pushforward_apply_congr R (ConcreteCategory.hom_ext _ _ fun x ↦ rfl) _ _ _ _)))

end MMP
