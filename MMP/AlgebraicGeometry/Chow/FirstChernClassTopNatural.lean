module

public import MMP.AlgebraicGeometry.Chow.CycleClassDescent
public import MMP.AlgebraicTopology.CapProduct.CupSupport
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints
public import MMP.AlgebraicGeometry.Chow.FirstChernClassTopNaturalGeneric

/-!
# Naturality of `c₁ᵗᵒᵖ` and Fulton 19.2 for subvarieties

Let `f : X' ⟶ X` be a morphism of schemes over `ℂ`. For `ℰ` quasi-coherent and locally free of
rank one on `X`, the bundle map `𝐕(f^*ℰ) ⟶ 𝐕(ℰ)` of the base change is a fibrewise isomorphism
carrying the zero section to the zero section, so it pulls the Thom class back to the Thom class
and `f^* c₁ᵗᵒᵖ(ℰ) = c₁ᵗᵒᵖ(f^*ℰ)`. An isomorphism `ℱ ≅ 𝒢` induces a fibrewise isomorphism
`𝐕(𝒢) ⟶ 𝐕(ℱ)` over `X`, so `c₁ᵗᵒᵖ` depends only on the isomorphism class; with Stacks'
`g^*(ℒ^∨) ≅ (g^*ℒ)^∨` this gives `f^* c₁ᵗᵒᵖ(L) = c₁ᵗᵒᵖ(f^*L)` for invertible `L`. Together with the
projection formula for cap products (`MMP.borelMooreHomology.pushforward_capProduct_pullback`)
and Stacks 02SU, Fulton's Proposition 19.2 extends from `α = [X]` to `α = [V]` for a closed
subvariety `V` on which `L` has a non-zero section.

## Main results

* `MMP.Modules.topFirstChernClass_congr`: `c₁ᵗᵒᵖ(ℱ) = c₁ᵗᵒᵖ(𝒢)` for `ℱ ≅ 𝒢`.
* `MMP.Chow.pullback_firstChernClassTop`: `f^* c₁ᵗᵒᵖ(L) = c₁ᵗᵒᵖ(f^*L)`.
* `MMP.Chow.pushforward_firstChernClassTopCap`: `f_*(c₁ᵗᵒᵖ(f^*L) ∩ a) = c₁ᵗᵒᵖ(L) ∩ f_* a` for `f`
  proper.
* `MMP.Chow.cycleClass_eq_firstChernClassTopCap_of_mk_eq`: Fulton 19.2 for `α = [X]`, `X` a
  variety and `L` with a non-zero section.
* `MMP.Chow.cycleClass_eq_firstChernClassTopCap_pushforward_of_mk_eq`: Fulton 19.2 for
  `α = [V]`, `L|_V` with a non-zero section.

## What is not proved here

Fulton 19.2 for `L|_V` with no section (`L|_V = A ⊗ B⁻¹`), which needs additivity of `c₁ᵗᵒᵖ`:
`MMP.AlgebraicGeometry.Chow.FirstChernClassTopAdditive`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Proposition 19.2.
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Opposite
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP AlgebraicGeometry.SheafOfModules

/-! ### Bundle maps of module morphisms -/

section ModuleHom

variable {X : Scheme.{0}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
  (φ : F ⟶ G)

/-- The bundle map `𝐕(φ) : 𝐕(𝒢) ⟶ 𝐕(ℱ)` over `X` of a morphism `φ : ℱ ⟶ 𝒢` of modules. -/
abbrev bundleMap : totalSpace G ⟶ totalSpace F :=
  (Scheme.Modules.vectorBundleMap X φ).left

/-- `𝐕(φ)` lies over `X`: composing it with the projection of `𝐕(ℱ)` gives the projection of
`𝐕(𝒢)`. -/
@[reassoc]
lemma bundleMap_proj : bundleMap φ ≫ proj F = proj G :=
  Scheme.Modules.vectorBundleMap_left_comp X φ

/-- `𝐕(φ)` carries the zero section of `𝐕(𝒢)` to that of `𝐕(ℱ)`. -/
@[reassoc]
lemma zeroSection_bundleMap : zeroSection G ≫ bundleMap φ = zeroSection F := by
  have h : Scheme.Modules.vectorBundleOverZeroSection G ≫ Scheme.Modules.vectorBundleMap X φ =
      Scheme.Modules.vectorBundleOverZeroSection F := by
    apply (Scheme.Modules.vectorBundleHomEquiv F _).injective
    refine (Scheme.Modules.vectorBundleHomEquiv_comp_vectorBundleMap φ _ _).trans ?_
    rw [Scheme.Modules.vectorBundleHomEquiv_vectorBundleOverZeroSection,
      Scheme.Modules.vectorBundleHomEquiv_vectorBundleOverZeroSection]
    exact Limits.comp_zero
  rw [zeroSection_eq_vectorBundleOverZeroSection, zeroSection_eq_vectorBundleOverZeroSection]
  exact congrArg (fun u ↦ u.left) h

/-- **`𝐕(φ)` in charts**: it pulls the coordinate function `m ∈ Γ(ℱ, V)` of `𝐕(ℱ)` back to the
coordinate function `φ(m) ∈ Γ(𝒢, V)` of `𝐕(𝒢)`. -/
theorem appLE_bundleMap_generator (V : X.affineOpens) (m : Γ(F, V.1))
    (hle : proj G ⁻¹ᵁ V.1 ≤ bundleMap φ ⁻¹ᵁ (proj F ⁻¹ᵁ V.1)) :
    (bundleMap φ).appLE (proj F ⁻¹ᵁ V.1) (proj G ⁻¹ᵁ V.1) hle
        (totalSections F V (generator F V.2 m)) =
      totalSections G V (generator G V.2 (φ.app V.1 m)) := by
  have h1 := appLE_totalSections_generator F (Scheme.Modules.vectorBundleMap X φ) V m hle
  have h2 := appLE_totalSections_generator G (𝟙 (Scheme.Modules.vectorBundleOver X (F := G))) V
    (φ.app V.1 m) le_rfl
  have h3 := Scheme.Modules.vectorBundleHomEquiv_comp_vectorBundleMap φ _
    (𝟙 (Scheme.Modules.vectorBundleOver X (F := G)))
  rw [Category.id_comp] at h3
  refine h1.trans ?_
  rw [h3]
  refine h2.symm.trans ?_
  simp only [Scheme.Hom.appLE, Over.id_left, Scheme.Hom.id_app]
  erw [Category.id_comp, Subsingleton.elim (homOfLE _) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

variable [X.Over (Spec (.of ℂ))]

/-- `𝐕(φ)` is a morphism of schemes over `ℂ`. -/
instance isOver_bundleMap : (bundleMap φ).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change bundleMap φ ≫ proj F ≫ X ↘ Spec (.of ℂ) = proj G ≫ X ↘ Spec (.of ℂ)
    rw [bundleMap_proj_assoc]⟩

/-- The `Γ(X, V)`-linear equivalence `Γ(ℱ, V) ≃ₗ Γ(𝒢, V)` induced by an isomorphism `e : ℱ ≅ 𝒢`. -/
def sectionsLinearEquiv (e : F ≅ G) (V : X.Opens) : Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V) where
  toFun := e.hom.app V
  invFun := e.inv.app V
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul e.hom
  left_inv x := by
    change (e.hom ≫ e.inv).app V x = x
    rw [e.hom_inv_id]
    rfl
  right_inv x := by
    change (e.inv ≫ e.hom).app V x = x
    rw [e.inv_hom_id]
    rfl

omit [F.IsQuasicoherent] [G.IsQuasicoherent] [X.Over (Spec (.of ℂ))] in
/-- `sectionsLinearEquiv e V` sends a section `x` to `e.hom.app V x`. -/
@[simp]
lemma sectionsLinearEquiv_apply (e : F ≅ G) (V : X.Opens) (x : Γ(F, V)) :
    sectionsLinearEquiv e V x = e.hom.app V x :=
  rfl

omit [F.IsQuasicoherent] [G.IsQuasicoherent] [X.Over (Spec (.of ℂ))] in
/-- `(sectionsLinearEquiv e V).symm` sends a section `x` to `e.inv.app V x`. -/
@[simp]
lemma sectionsLinearEquiv_symm_apply (e : F ≅ G) (V : X.Opens) (x : Γ(G, V)) :
    (sectionsLinearEquiv e V).symm x = e.inv.app V x :=
  rfl

variable {r : ℕ}

omit [X.Over (Spec (.of ℂ))] in
/-- The preimage of `V` in `𝐕(𝒢)` is contained in the preimage under `𝐕(φ)` of the preimage of `V`
in `𝐕(ℱ)`. -/
lemma proj_preimage_le_bundleMap_preimage (V : X.Opens) :
    proj G ⁻¹ᵁ V ≤ bundleMap φ ⁻¹ᵁ (proj F ⁻¹ᵁ V) := by
  intro y hy
  change (bundleMap φ ≫ proj F).base y ∈ V
  rw [bundleMap_proj]
  exact hy

/-- A `ℂ`-point `q` of `𝐕(𝒢)` whose image in `X` factors through `V` factors through the preimage
of `V` in `𝐕(𝒢)`. -/
lemma top_le_preimage_proj {q : UnderlyingSpace ℂ (totalSpace G)} {V : X.Opens}
    (hq : ⊤ ≤ (mapFun (proj G) q).toHom ⁻¹ᵁ V) : ⊤ ≤ q.toHom ⁻¹ᵁ (proj G ⁻¹ᵁ V) := by
  rw [toHom_mapFun, Scheme.Hom.comp_preimage] at hq
  exact hq

/-- If a `ℂ`-point `q` of `𝐕(𝒢)` factors through the preimage of `V`, then its image under `𝐕(φ)`
factors through the preimage of `V` in `𝐕(ℱ)`. -/
lemma top_le_preimage_mapFun_bundleMap {q : UnderlyingSpace ℂ (totalSpace G)} {V : X.Opens}
    (hq : ⊤ ≤ q.toHom ⁻¹ᵁ (proj G ⁻¹ᵁ V)) :
    ⊤ ≤ (mapFun (bundleMap φ) q).toHom ⁻¹ᵁ (proj F ⁻¹ᵁ V) := by
  rw [toHom_mapFun, Scheme.Hom.comp_preimage]
  exact hq.trans (Scheme.Hom.preimage_mono _ (proj_preimage_le_bundleMap_preimage φ V))

omit [X.Over (Spec (.of ℂ))] in
/-- Evaluating `a ∈ Γ(Z, U)` at the image of a `ℂ`-point `p` under `ψ` equals evaluating
`ψ.appLE U V e a` at `p`. -/
lemma eval_mapFun_eq_eval_appLE {Y Z : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))]
    (ψ : Y ⟶ Z) [ψ.IsOver (Spec (.of ℂ))] {U : Z.Opens} {V : Y.Opens} (e : V ≤ ψ ⁻¹ᵁ U)
    (p : UnderlyingSpace ℂ Y) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ V) (hp' : ⊤ ≤ (mapFun ψ p).toHom ⁻¹ᵁ U)
    (a : Γ(Z, U)) : eval (mapFun ψ p) hp' a = eval p hp (ψ.appLE U V e a) :=
  (eval_appLE ψ e p hp a).symm

/-- Evaluating the `i`-th chart coordinate of `c` at `𝐕(φ)(q)` is evaluating the coordinate
section of `φ(c.2 i)` on `𝐕(𝒢)` at `q`. -/
lemma eval_mapFun_bundleMap_chartCoordSection (c : Chart F r)
    {q : UnderlyingSpace ℂ (totalSpace G)} (hq : ⊤ ≤ q.toHom ⁻¹ᵁ (proj G ⁻¹ᵁ c.1.1)) (i : Fin r) :
    eval (mapFun (bundleMap φ) q) (top_le_preimage_mapFun_bundleMap φ hq)
        (chartCoordSection c i) =
      eval q hq (totalSections G c.1 (generator G c.1.2 (φ.app c.1.1 (c.2 i)))) := by
  rw [eval_mapFun_eq_eval_appLE (bundleMap φ) (proj_preimage_le_bundleMap_preimage φ c.1.1) q hq,
    chartCoordSection, appLE_bundleMap_generator φ c.1 (c.2 i)]

/-- **The bundle map of an isomorphism of modules is fibrewise the identity in coordinates**: for
a chart `c = (V, b)` of `ℱ` and the chart `(V, e(b))` of `𝒢`,
`x^c(𝐕(e)(q)) = x^{(V, e(b))}(q)` for every point `q` over `V`. -/
theorem coord_bundleMap (e : F ≅ G) (c : Chart F r) {q : UnderlyingSpace ℂ (totalSpace G)}
    (hq : mapFun (proj G) q ∈ chartBase c) :
    coord c (mapFun (bundleMap e.hom) q) =
      coord (⟨c.1, c.2.map (sectionsLinearEquiv e c.1.1)⟩ : Chart G r) q := by
  funext i
  have hq' := top_le_preimage_proj hq
  rewrite [coord_apply c (top_le_preimage_mapFun_bundleMap e.hom hq') i,
    eval_mapFun_bundleMap_chartCoordSection e.hom c hq' i,
    coord_apply (⟨c.1, c.2.map (sectionsLinearEquiv e c.1.1)⟩ : Chart G r) hq' i]
  rewrite [chartCoordSection, Module.Basis.map_apply, sectionsLinearEquiv_apply]
  rfl

variable [IsFiniteLocallyFreeOfRank.{0, 0, 0} F r]

/-- **The bundle map of an isomorphism of modules is a fibrewise isomorphism.** -/
theorem isFibrewiseIso_bundleMap (e : F ≅ G) : IsFibrewiseIso r (𝟙 X) (bundleMap e.hom) := by
  intro x
  obtain ⟨c, hc⟩ := exists_mem_chartBase F r x
  have hx : mapFun (𝟙 X) x = x := DFunLike.congr_fun map_id x
  refine ⟨⟨c.1, c.2.map (sectionsLinearEquiv e c.1.1)⟩, c, 1, hc, hx.symm ▸ hc, fun q hq ↦ ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  exact coord_bundleMap e c (hq ▸ hc)

end ModuleHom

/-! ### Composites of fibrewise isomorphisms -/

section Comp

variable {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))] {r : ℕ}
  {E : X.Modules} [E.IsQuasicoherent] {E' E'' : X'.Modules} [E'.IsQuasicoherent]
  [E''.IsQuasicoherent] {f : X' ⟶ X} [f.IsOver (Spec (.of ℂ))]
  {F₁ : totalSpace E'' ⟶ totalSpace E'} [F₁.IsOver (Spec (.of ℂ))]
  {F : totalSpace E' ⟶ totalSpace E} [F.IsOver (Spec (.of ℂ))]

/-- A fibrewise isomorphism over `𝟙` followed by a fibrewise isomorphism over `f` is a fibrewise
isomorphism over `f`. -/
theorem IsFibrewiseIso.comp_of_id (hπ₁ : F₁ ≫ proj E' = proj E'')
    (h₁ : IsFibrewiseIso r (𝟙 X') F₁) (h : IsFibrewiseIso r f F) :
    IsFibrewiseIso r f (F₁ ≫ F) := by
  intro x'
  obtain ⟨c'', c', A₁, hx'', hx', hA₁⟩ := h₁ x'
  have hid : mapFun (𝟙 X') x' = x' := DFunLike.congr_fun map_id x'
  rw [hid] at hx'
  obtain ⟨c, A, hc, hA⟩ := h.exists_coord_mapFun c' hx'
  refine ⟨c'', c, A * A₁, hx'', hc, fun q hq ↦ ?_⟩
  have hcomp : mapFun (F₁ ≫ F) q = mapFun F (mapFun F₁ q) :=
    UnderlyingSpace.ext (by simp only [toHom_mapFun, Category.assoc])
  have hq₁ : mapFun (proj E') (mapFun F₁ q) = x' := by
    refine Eq.trans (UnderlyingSpace.ext ?_) hq
    simp only [toHom_mapFun, Category.assoc, hπ₁]
  rw [hcomp, hA _ hq₁, hA₁ q hq, Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_mul]

end Comp

/-! ### Naturality of `c₁ᵗᵒᵖ` -/

section Naturality

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

/-- `c₁ᵗᵒᵖ` only depends on the isomorphism class of the module. -/
theorem topFirstChernClass_congr {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    [IsFiniteLocallyFreeOfRank.{0, 0, 0} F 1] [IsFiniteLocallyFreeOfRank.{0, 0, 0} G 1]
    (e : F ≅ G) : topFirstChernClass R F = topFirstChernClass R G := by
  have h := pullback_topFirstChernClass_of_fibrewise R (bundleMap_proj e.hom)
    (isFibrewiseIso_bundleMap e) ((zeroSection_bundleMap e.hom).trans (Category.id_comp _).symm)
  rw [← h]
  have hid : TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 X)) =
      𝟙 (TopCat.of (UnderlyingSpace ℂ X)) := by
    rw [map_id]
    rfl
  rw [hid, cohomologyWithSupports.pullback_id]
  rfl

end Naturality

end MMP.Modules

namespace MMP.Chow

open MMP MMP.Modules AlgebraicGeometry.SheafOfModules Stacks.Chow

/-- The pull-back of an invertible module is invertible. -/
instance isInvertibleModule_pullback {X X' : Scheme.{0}} (f : X' ⟶ X) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    Stacks.Ample.IsInvertibleModule X' ((Scheme.Modules.pullback f).obj L) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback f L

variable (R : Type) [CommRing R] {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [X'.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme X'] (f : X' ⟶ X)
  [f.IsOver (Spec (.of ℂ))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

omit [IsComplexScheme X] [IsComplexScheme X'] in
/-- **Naturality of `c₁ᵗᵒᵖ(L)`** (Fulton, §19.1): for a morphism `f : X' ⟶ X` of schemes over `ℂ`
and an invertible module `L` on `X`, `f^* c₁ᵗᵒᵖ(L) = c₁ᵗᵒᵖ(f^*L)` in `H²(X'(ℂ); R)`. -/
theorem pullback_firstChernClassTop :
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) univ ((2 * 1 : ℕ) : ℤ)).hom
        (firstChernClassTop R L) :
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X')) univ
        ((2 * 1 : ℕ) : ℤ)) = firstChernClassTop R ((Scheme.Modules.pullback f).obj L) := by
  have : IsFiniteLocallyFreeOfRank.{0, 0, 0} L 1 :=
    Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
      (X := X) (L := L)
  rw [firstChernClassTop, pullback_topFirstChernClass, firstChernClassTop]
  exact topFirstChernClass_congr R (Stacks.FundamentalGroup.pullbackDualSheafIso f L
    (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1))

omit [IsComplexScheme X'] in
/-- **The projection formula for `c₁ᵗᵒᵖ`** (Fulton, §19.1): for a proper morphism `f : X' ⟶ X`
of complex schemes, an invertible module `L` on `X` and `a ∈ H_{2k+2}(X'(ℂ))`,
`f_*(c₁ᵗᵒᵖ(f^*L) ∩ a) = c₁ᵗᵒᵖ(L) ∩ f_* a` in `H_{2k}(X(ℂ))`. -/
theorem pushforward_firstChernClassTopCap [IsProper f] (k : ℕ) (a : BMHomology R X' (2 * (k + 1))) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
        (isProperMap_map (K := ℂ) f) (2 * k : ℕ)
        (firstChernClassTopCap R ((Scheme.Modules.pullback f).obj L) k a) =
      firstChernClassTopCap R L k (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (map (K := ℂ) f)) (isProperMap_map (K := ℂ) f) (2 * (k + 1) : ℕ) a) := by
  simp only [firstChernClassTopCap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  erw [borelMooreHomology.pushforward_congrDegree]
  congr 1
  rw [← pullback_firstChernClassTop R f L]
  exact borelMooreHomology.pushforward_capProduct_pullback R _ (isProperMap_map (K := ℂ) f)
    isClosed_univ (MMP.hasProperNeighbourhoodDeformations_univ _)
    (by rw [preimage_univ]; exact MMP.hasProperNeighbourhoodDeformations_univ _)
    _ _ _ a

open scoped MMP.SubschemeOver in
/-- **Fulton's Proposition 19.2 for `α = [X]`.** Let `X` be a complex variety of dimension `k + 1`
and `L` an invertible `𝒪_X`-module with a non-zero global section. Then `cl(β) = c₁ᵗᵒᵖ(L) ∩ cl(X)`
for every `k`-cycle `β` representing `c₁(L) ∩ [X]_{k+1}`. -/
theorem cycleClass_eq_firstChernClassTopCap_of_mk_eq [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X) (t : Γ(L, ⊤)) (ht : t ≠ 0)
    {μ : BMHomology R X (2 * (k + 1))} (hμ : IsVarietyFundamentalClass R hn μ)
    (β : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (hβ : letI : IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
        ‹Stacks.Ample.IsInvertibleModule X L›
      (QuotientAddGroup.mk β : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) =
        firstChernClassCapOfInvertible (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k L
          (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (𝟙 X)
            ((k + 1 : ℕ) : ℤ))) :
    cycleClass R k β = firstChernClassTopCap R L k μ := by
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule X L›
  have hDim : schemeDeltaDimension (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) =
      (((k : ℤ) + 1 : ℤ) : EInt) := by
    exact_mod_cast schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
      (X ↘ Spec (.of ℂ)) hn.symm
  have hS := Stacks.ChernCap42.firstChernClassCapOfInvertible_fundamentalCycle
    (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((k : ℤ) + 1) hDim L t ht
  rw [show (k : ℤ) + 1 - 1 = k by ring] at hS
  have hβ' := hβ.trans hS
  rw [QuotientAddGroup.eq_iff_sub_mem] at hβ'
  have h0 := cycleClass_eq_zero_of_isRationallyEquivalentToZero R k _ hβ'
  rw [map_sub, sub_eq_zero] at h0
  rw [h0]
  exact cycleClass_zeroScheme_eq_firstChernClassTopCap R L hn t ht hμ

open scoped MMP.SubschemeOver in
/-- **Fulton's Proposition 19.2 for `α = [V]`, `L|_V` with a section.** Let `X` be a complex
scheme, `L` an invertible `𝒪_X`-module and `i : V ⟶ X` a closed immersion of a complex variety
`V` of dimension `k + 1` such that `i^*L` has a non-zero global section. Then
`cl(β) = c₁ᵗᵒᵖ(L) ∩ i_* cl(V)` for every `k`-cycle `β` representing
`c₁(L) ∩ i_*[V]_{k+1}` on `X`. -/
theorem cycleClass_eq_firstChernClassTopCap_pushforward_of_mk_eq {V : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V]
    [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))] (i : V ⟶ X)
    [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] {k : ℕ}
    (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V)
    (t : Γ((Scheme.Modules.pullback i).obj L, ⊤)) (ht : t ≠ 0)
    {μ : BMHomology R V (2 * (k + 1))} (hμ : IsVarietyFundamentalClass R hn μ)
    (β : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (hβ : letI : IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
        ‹Stacks.Ample.IsInvertibleModule X L›
      (QuotientAddGroup.mk β : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) =
        firstChernClassCapOfInvertible (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k L
          (properPushforward (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) i
            (comp_over i _) ((k + 1 : ℕ) : ℤ)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (𝟙 V)
              ((k + 1 : ℕ) : ℤ)))) :
    cycleClass R k β = firstChernClassTopCap R L k
      (borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) i))
        (isProperMap_map (K := ℂ) i) (2 * (k + 1) : ℕ) μ) := by
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule X L›
  have : AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L) :=
    isInvertibleModule_pullback i L
  have hDim : schemeDeltaDimension (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) =
      (((k : ℤ) + 1 : ℤ) : EInt) := by
    exact_mod_cast schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
      (V ↘ Spec (.of ℂ)) hn.symm
  have hS := Stacks.ChernCap42.firstChernClassCapOfInvertible_fundamentalCycle
    (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) ((k : ℤ) + 1) hDim ((Scheme.Modules.pullback i).obj L)
    t ht
  rw [show (k : ℤ) + 1 - 1 = k by ring] at hS
  have h02SU := properChowPushforward_firstChernClassCapOfInvertible (fieldChowSituation ℂ)
    (V ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) i (comp_over i _) (k : ℤ) L
    (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (𝟙 V)
      ((k : ℤ) + 1))
  have hβ' : (QuotientAddGroup.mk β : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) =
      QuotientAddGroup.mk (properPushforward (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
        (X ↘ Spec (.of ℂ)) i (comp_over i _) k
        (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
          (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback i).obj L) t).subschemeι k)) := by
    refine hβ.trans (h02SU.symm.trans ?_)
    erw [hS]
    rfl
  rw [QuotientAddGroup.eq_iff_sub_mem] at hβ'
  have h0 := cycleClass_eq_zero_of_isRationallyEquivalentToZero R k _ hβ'
  rw [map_sub, sub_eq_zero] at h0
  have hZ : cycleClass R k (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (V ↘ Spec (.of ℂ))
      (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback i).obj L) t).subschemeι k) =
      firstChernClassTopCap R ((Scheme.Modules.pullback i).obj L) k μ :=
    cycleClass_zeroScheme_eq_firstChernClassTopCap R ((Scheme.Modules.pullback i).obj L) hn t ht hμ
  rw [h0, cycleClass_properPushforward, hZ]
  exact pushforward_firstChernClassTopCap R i L k μ

end MMP.Chow
