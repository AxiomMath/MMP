module

public import MMP.AlgebraicGeometry.Chow.CycleClass
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.GenericCovering
public import MMP.AlgebraicGeometry.Properties.RegularLocus
public import MMP.AlgebraicTopology.FundamentalClass.Homeomorphism
public import MMP.AlgebraicTopology.FundamentalClass.ComplexOrientation
public import MMP.AlgebraicTopology.FundamentalClass.EuclideanComplexOrientation
public import MMP.AlgebraicTopology.FundamentalClass.Restriction
public import MMP.AlgebraicTopology.OrientationClass.CapLocalDegree
public import MMP.AlgebraicTopology.OrientationClass.Point
public import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
public import MMP.AlgebraicTopology.CapProduct.Restriction

/-!
# The cycle class of the generic point is the fundamental class (Fulton, §19.1)

Let `M` be an integral complex scheme of dimension `n`, with generic point `η`. The Stacks cycle
class `cl_M(η) = MMP.Chow.pointCycleClass R η _ ∈ H_{2n} M(ℂ)` restricts, on the regular part
`M_reg(ℂ)`, a complex manifold of dimension `n` oriented by its complex structure, to the
fundamental class of `M_reg(ℂ)`.

*Proof.* `cl_M(η)` is the push-forward of the fundamental class of `closure {η}`, with its
reduced structure, along its inclusion `i` in `M`; since `M` is integral, `i` is an isomorphism.
An isomorphism `g : A ≅ B` of integral complex schemes identifies `A_reg(ℂ)` with `B_reg(ℂ)`,
orientation-preservingly (an algebraic chart of `A` read through `g⁻¹` is an algebraic chart of
`B`), so it carries the fundamental class of `A_reg(ℂ)` to that of `B_reg(ℂ)`.

## Main results

* `MMP.Chow.isFundamentalClass_restrict_pushforward_of_isIso`: an isomorphism `g : A ≅ B` of
  integral complex schemes carries a class restricting to the fundamental class of `A_reg(ℂ)` to
  one restricting to the fundamental class of `B_reg(ℂ)`.
* `MMP.Chow.isFundamentalClass_restrict_pointCycleClass_genericPoint`: `cl_M(η)` restricts to
  the fundamental class of `M_reg(ℂ)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set Manifold
open MMP.UnderlyingSpace MMP.FundamentalClass MMP.borelMooreHomology Stacks.Chow

universe u

namespace MMP.Chow

section Orientation

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M'] [ChartedSpace H M]
  [ChartedSpace H M']

/-- A homeomorphism `φ : M ≃ₜ M'` into a manifold with an oriented atlas, under which every chart
`e` of `M` is read through `φ⁻¹` as a chart of `M'`, is orientation preserving. -/
private theorem isOrientationPreserving_of_forall_mem_atlas' (hM' : IsOrientedAtlas H M')
    {n : ℕ} (b : Module.Basis (Fin n) ℝ H) (φ : M ≃ₜ M')
    (h : ∀ e ∈ atlas H M, ∃ ê ∈ atlas H M', ∀ z : M', ê z = e (φ.symm z) ∧
      (z ∈ ê.source ↔ φ.symm z ∈ e.source)) :
    IsOrientationPreserving b b φ := by
  refine isOrientationPreserving_of_hasFDerivAt b b φ fun e he e' he' x hx hx' ↦ ?_
  obtain ⟨ê, hê, hêe⟩ := h e he
  have hφx : φ x ∈ ê.source := (hêe (φ x)).2.2 (by simpa using hx)
  have hêx : ê (φ x) = e x := by simpa using (hêe (φ x)).1
  have hpt : e x ∈ (ê.symm ≫ₕ e').source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    refine ⟨hêx ▸ ê.map_source hφx, ?_⟩
    rw [← hêx, ê.left_inv hφx]
    exact hx'
  obtain ⟨hd, hdet⟩ := hM' ê hê e' he' (e x) hpt
  refine ⟨fderiv ℝ (ê.symm ≫ₕ e') (e x), ?_, ?_⟩
  · refine hd.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    have hz : φ (e.symm y) ∈ ê.source := (hêe _).2.2 (by simpa using e.map_target hy)
    have hêz : ê (φ (e.symm y)) = y := by
      rw [(hêe _).1, φ.symm_apply_apply, e.right_inv hy]
    have hsy : ê.symm y = φ (e.symm y) := by
      conv_lhs => rw [← hêz]
      exact ê.left_inv hz
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsy]
  · rw [show ((fderiv ℝ (ê.symm ≫ₕ e') (e x) : H → H) ∘ b) =
      ((fderiv ℝ (ê.symm ≫ₕ e') (e x) : H →ₗ[ℝ] H) : H → H) ∘ b from rfl, basis_det_comp_self]
    exact hdet

end Orientation

section Iso

/-- An open immersion over `ℂ` preserves and reflects regular complex points. -/
private lemma mapFun_mem_regularPart_iff' {U X : Scheme.{0}} [U.Over (Spec (.of ℂ))]
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (U ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (.of ℂ))] (z : UnderlyingSpace ℂ U) :
    mapFun j z ∈ regularPart ℂ X ↔ z ∈ regularPart ℂ U := by
  rw [mem_regularPart_iff, mem_regularPart_iff, toHom_mapFun]
  exact MMP.mem_regularLocus_iff_of_isOpenImmersion j (z.toHom (IsLocalRing.closedPoint ℂ))

variable {A B : Scheme.{0}} [A.Over (Spec (.of ℂ))] [B.Over (Spec (.of ℂ))]
  [IsComplexScheme A] [IsComplexScheme B] [IsIntegral A] [IsIntegral B]
  (g : A ⟶ B) [IsIso g] [g.IsOver (Spec (.of ℂ))]

omit [IsComplexScheme A] [IsComplexScheme B] [IsIntegral A] [IsIntegral B] in
private lemma isOver_inv : (inv g).IsOver (Spec (.of ℂ)) :=
  ⟨by rw [IsIso.inv_comp_eq, comp_over]⟩

section Inv

variable [(inv g).IsOver (Spec (.of ℂ))]

omit [IsComplexScheme A] [IsComplexScheme B] [IsIntegral A] [IsIntegral B] in
private lemma mapFun_inv_mapFun (p : UnderlyingSpace ℂ A) : mapFun (inv g) (mapFun g p) = p := by
  refine UnderlyingSpace.ext ?_
  rw [toHom_mapFun, toHom_mapFun, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

omit [IsComplexScheme A] [IsComplexScheme B] [IsIntegral A] [IsIntegral B] in
private lemma mapFun_mapFun_inv (q : UnderlyingSpace ℂ B) : mapFun g (mapFun (inv g) q) = q := by
  refine UnderlyingSpace.ext ?_
  rw [toHom_mapFun, toHom_mapFun, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- An isomorphism `g : A ≅ B` over `ℂ` identifies `A_reg(ℂ)` with `B_reg(ℂ)`. -/
private def regularOpensHomeomorph :
    (regularOpens ℂ A : Opens (TopCat.of (UnderlyingSpace ℂ A))) ≃ₜ
      (regularOpens ℂ B : Opens (TopCat.of (UnderlyingSpace ℂ B))) where
  toFun x := ⟨mapFun g x.1, mem_regularOpens.2
    ((mapFun_mem_regularPart_iff' g x.1).2 (mem_regularOpens.1 x.2))⟩
  invFun y := ⟨mapFun (inv g) y.1, mem_regularOpens.2
    ((mapFun_mem_regularPart_iff' (inv g) y.1).2 (mem_regularOpens.1 y.2))⟩
  left_inv x := Subtype.ext (mapFun_inv_mapFun g x.1)
  right_inv y := Subtype.ext (mapFun_mapFun_inv g y.1)
  continuous_toFun := ((map (K := ℂ) g).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((map (K := ℂ) (inv g)).continuous.comp continuous_subtype_val).subtype_mk _

/-- The identification `A_reg(ℂ) ≃ₜ B_reg(ℂ)` is orientation preserving for the complex
orientations of the algebraic charts. -/
private theorem isOrientationPreserving_regularOpensHomeomorph {n : ℕ}
    (hnA : (n : WithBot ℕ∞) = topologicalKrullDim A)
    (hnB : (n : WithBot ℕ∞) = topologicalKrullDim B) :
    letI := regularChartedSpace (𝕜 := ℂ) hnA
    letI := regularChartedSpace (𝕜 := ℂ) hnB
    IsOrientationPreserving (euclideanComplexOrientationBasis n)
      (euclideanComplexOrientationBasis n) (regularOpensHomeomorph g) := by
  let := regularChartedSpace (𝕜 := ℂ) hnA
  let := regularChartedSpace (𝕜 := ℂ) hnB
  have := isManifold_regularOpens (𝕜 := ℂ) (X := B) hnB
  have : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 1 (regularOpens ℂ B) :=
    IsManifold.of_le le_top
  refine isOrientationPreserving_of_forall_mem_atlas'
    (isOrientedAtlas_of_isManifold_complex (regularOpens ℂ B)) _ _ fun e he ↦ ?_
  obtain ⟨c, hne, hc, rfl⟩ := he
  let y : regularOpens ℂ B := regularOpensHomeomorph g hne.some
  have : Nonempty (UnderlyingSpace ℂ B) := ⟨y.1⟩
  refine ⟨(restrictChart (inv g) c).subtypeRestr ⟨y⟩,
    ⟨restrictChart (inv g) c, ⟨y⟩, hc.restrict_openEmbedding (inv g), rfl⟩,
    fun z ↦ ⟨rfl, ?_⟩⟩
  simp only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
    OpenPartialHomeomorph.trans_source]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rw [IsOpenEmbedding.toOpenPartialHomeomorph_source]
  exact mem_univ _

omit [IsIntegral A] [IsIntegral B] in
variable (R : Type) [CommRing R] in
/-- Restricting `g_* c` to `B_reg(ℂ)` is pushing the restriction `x` of `c` to `A_reg(ℂ)`
forward along `A_reg(ℂ) ≃ₜ B_reg(ℂ)`. -/
private lemma restrict_regularOpens_pushforward (j : ℤ)
    (c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ A)) j)
    (x : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (regularOpens ℂ A : Opens (TopCat.of (UnderlyingSpace ℂ A)))) j)
    (hx : x = (borelMooreHomology.restrict R (ModuleCat.of R R)
      (regularOpens ℂ A : Opens (TopCat.of (UnderlyingSpace ℂ A))) j).hom c) :
    (borelMooreHomology.restrict R (ModuleCat.of R R)
        (regularOpens ℂ B : Opens (TopCat.of (UnderlyingSpace ℂ B))) j).hom
        ((borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) g))
          (isProperMap_map (K := ℂ) g) j).hom c) =
      (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (regularOpensHomeomorph g :
          C((regularOpens ℂ A : Opens (TopCat.of (UnderlyingSpace ℂ A))),
            (regularOpens ℂ B : Opens (TopCat.of (UnderlyingSpace ℂ B))))))
        (regularOpensHomeomorph g).isProperMap j).hom x := by
  subst hx
  have hO : (regularOpens ℂ A : Opens (TopCat.of (UnderlyingSpace ℂ A))) =
      Opens.comap (TopCat.ofHom (map (K := ℂ) g)).hom
        (regularOpens ℂ B : Opens (TopCat.of (UnderlyingSpace ℂ B))) := by
    ext p
    change p ∈ regularPart ℂ A ↔ mapFun g p ∈ regularPart ℂ B
    exact (mapFun_mem_regularPart_iff' g p).symm
  have hp := isProperMap_map (K := ℂ) g
  have hrp := isProperMap_restrictPreimage (TopCat.ofHom (map (K := ℂ) g))
    (regularOpens ℂ B : Opens (TopCat.of (UnderlyingSpace ℂ B))) hp
  refine (restrict_pushforward_apply R (ModuleCat.of R R) _ hp _ _ c).trans ?_
  rw [restrict_eq_pushforward_opensEqMap hO]
  rw [← ConcreteCategory.comp_apply, ← borelMooreHomology.pushforward_comp]
  exact pushforward_apply_congr R (ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext rfl) _ _ _ _

end Inv

variable (R : Type) [CommRing R]

/-- **Isomorphisms carry fundamental classes to fundamental classes.** Let `g : A ≅ B` be an
isomorphism over `ℂ` of integral complex schemes of dimension `n`, and `c ∈ H_{2n} A(ℂ)` a class
whose restriction to `A_reg(ℂ)` is the fundamental class. Then the restriction of `g_* c` to
`B_reg(ℂ)` is the fundamental class of `B_reg(ℂ)`. -/
theorem isFundamentalClass_restrict_pushforward_of_isIso {n : ℕ}
    (hnA : (n : WithBot ℕ∞) = topologicalKrullDim A)
    (hnB : (n : WithBot ℕ∞) = topologicalKrullDim B)
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ A)) (2 * n : ℕ)}
    (hc : letI := regularChartedSpace (𝕜 := ℂ) hnA
      IsFundamentalClass R (euclideanComplexOrientationBasis n)
        ((borelMooreHomology.restrict R (ModuleCat.of R R)
          (regularOpens ℂ A : Opens (TopCat.of (UnderlyingSpace ℂ A))) (2 * n : ℕ)).hom c)) :
    letI := regularChartedSpace (𝕜 := ℂ) hnB
    IsFundamentalClass R (euclideanComplexOrientationBasis n)
      ((borelMooreHomology.restrict R (ModuleCat.of R R)
        (regularOpens ℂ B : Opens (TopCat.of (UnderlyingSpace ℂ B))) (2 * n : ℕ)).hom
        ((borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) g))
          (isProperMap_map (K := ℂ) g) (2 * n : ℕ)).hom c)) := by
  have := isOver_inv g
  let := regularChartedSpace (𝕜 := ℂ) hnA
  let := regularChartedSpace (𝕜 := ℂ) hnB
  have hθ := hc.pushforward_homeomorph R (regularOpensHomeomorph g)
    (isOrientationPreserving_regularOpensHomeomorph g hnA hnB)
  rwa [restrict_regularOpens_pushforward g R _ c _ rfl]

end Iso

variable (R : Type) [CommRing R] {M : Scheme.{0}} [M.Over (Spec (.of ℂ))] [IsComplexScheme M]
  [IsIntegral M]

/-- **The cycle class of the generic point is the fundamental class.** For an integral complex
scheme `M` of dimension `n` with generic point `η`, the restriction of the cycle class
`cl_M(η) ∈ H_{2n} M(ℂ)` to the regular part `M_reg(ℂ)` is the fundamental class of the complex
manifold `M_reg(ℂ)`, oriented by its complex structure. -/
theorem isFundamentalClass_restrict_pointCycleClass_genericPoint {n : ℕ}
    (hn : (n : WithBot ℕ∞) = topologicalKrullDim M)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (M ↘ Spec (.of ℂ))
      (genericPoint M) = n) :
    letI := regularChartedSpace (𝕜 := ℂ) hn
    IsFundamentalClass R (euclideanComplexOrientationBasis n)
      ((borelMooreHomology.restrict R (ModuleCat.of R R)
        (regularOpens ℂ M : Opens (TopCat.of (UnderlyingSpace ℂ M))) (2 * n : ℕ)).hom
        (pointCycleClass R (genericPoint M) hx)) := by
  have := isIntegral_integralComponentAt (genericPoint M)
  set i := (integralComponentAt (genericPoint M)).subschemeι
  have hrange : Set.range (𝟙 M : M ⟶ M) = Set.range i := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt,
      (genericPoint_spec M).def]
    simp
  have hker : (𝟙 M : M ⟶ M).ker = i.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hrange]
  obtain ⟨φ, hφ, hφi⟩ : ∃ φ : _ ⟶ M, IsIso φ ∧ φ ≫ 𝟙 M = i :=
    ⟨_, IsClosedImmersion.isIso_lift (𝟙 M) i hker, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Category.comp_id] at hφi
  have : IsIso i := hφi ▸ hφ
  have hk := natCast_eq_dimension_integralComponentAt (genericPoint M) hx
  exact isFundamentalClass_restrict_pushforward_of_isIso i R hk hn
    (existsUnique_isVarietyFundamentalClass R hk).choose_spec.1

end MMP.Chow
