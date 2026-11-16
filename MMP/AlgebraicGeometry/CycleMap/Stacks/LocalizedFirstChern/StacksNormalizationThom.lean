module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksThomChart
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.ThomClass.OfRank
public import MMP.AlgebraicTopology.SingularCohomology.Relative.MapCongr
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap

/-!
# Naturality of the localized top Chern class under bundle maps (Stacks bundles)

Let `f : X' → X` be a morphism of schemes over `ℂ`, `ℰ` on `X` and `ℰ'` on `X'` quasi-coherent
modules, finite locally free of rank `r`, with vector bundles `π : 𝐕(ℰ) ⟶ X`,
`π' : 𝐕(ℰ') ⟶ X'` (`MMP.Modules.totalSpace`, `MMP.Modules.proj`), and `F : 𝐕(ℰ') ⟶ 𝐕(ℰ)` a
morphism over `ℂ` with `π ∘ F = f ∘ π'` which, on complex points, is a linear isomorphism on each
fibre: around every `x' ∈ X'(ℂ)` there are charts `c'` of `ℰ'` and `c` of `ℰ` in which
`coord c ∘ F = A · coord c'` on the fibre over `x'`, for some `A ∈ GL(r, ℂ)`. (The projection of
the pull-back bundle `f^*ℰ → ℰ` is the example; Fulton, §19.1.) Then `F` maps exactly the zero
section of `𝐕(ℰ')` to the zero section of `𝐕(ℰ)`, carries complex frames to complex frames, and
so pulls the Thom class `u_ℰ` back to `u_{ℰ'}` (Thom classes are natural).

For morphisms `σ : X ⟶ 𝐕(ℰ)`, `σ' : X' ⟶ 𝐕(ℰ')` over `ℂ` with `F ∘ σ' = σ ∘ f`, we get
`σ'⁻¹(0_{ℰ'}(ℂ)) = f⁻¹(σ⁻¹(0_ℰ(ℂ)))` and `σ'^* u_{ℰ'} = f^*(σ^* u_ℰ)` in
`H^{2r}(X'(ℂ), X'(ℂ) - σ'⁻¹(0))`. Combined with the projection formula, for `f` proper and
`a ∈ H_k X'`:
`f_{D*}(σ'^* u_{ℰ'} ∩ a) = σ^* u_ℰ ∩ f_* a` in `H_{k-2r}(σ⁻¹(0_ℰ(ℂ)))`, with
`f_D : σ'⁻¹(0_{ℰ'}(ℂ)) → σ⁻¹(0_ℰ(ℂ))` the restriction of `f` (Fulton, §19.1, proof of
Lemma 19.1.3).

## Main definitions

* `MMP.Modules.IsFibrewiseIso`: `F` is a linear isomorphism on each fibre over complex points.
* `MMP.Modules.zeroLocusMap`: the restriction `σ'⁻¹(0_{ℰ'}(ℂ)) → σ⁻¹(0_ℰ(ℂ))` of `f` on
  complex points.

## Main results

* `MMP.Modules.preimage_range_zeroSection_of_fibrewise`: `F⁻¹(0_ℰ(ℂ)) = 0_{ℰ'}(ℂ)`.
* `MMP.Modules.IsComplexFrame.comp_of_fibrewise`: `F` carries complex frames to complex frames.
* `MMP.Modules.thomClass_eq_map_of_fibrewise`: `u_{ℰ'} = F^* u_ℰ`.
* `MMP.Modules.preimage_zeroLocus_of_comp`: `σ'⁻¹(0_{ℰ'}(ℂ)) = f⁻¹(σ⁻¹(0_ℰ(ℂ)))`.
* `MMP.Modules.forget_pullback_thomClass_of_comp`: `σ'^* u_{ℰ'} = f^*(σ^* u_ℰ)`.
* `MMP.Modules.pushforward_localizedTopChernCap_of_comp`:
  `f_{D*}(σ'^* u_{ℰ'} ∩ a) = σ^* u_ℰ ∩ f_* a`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set
open scoped Matrix

namespace MMP.Modules

open UnderlyingSpace AlgebraicGeometry.SheafOfModules

section Transition

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] {E : X.Modules} [E.IsQuasicoherent] {r : ℕ}

/-- Over a point `x` in the domains of two charts `c₁`, `c₂`, the coordinates of `c₂` on the fibre
over `x` are those of `c₁` followed by an invertible matrix. -/
lemma exists_coord_eq_mulVec (c₁ c₂ : Chart E r) {x : UnderlyingSpace ℂ X}
    (h₁ : x ∈ chartBase c₁) (h₂ : x ∈ chartBase c₂) :
    ∃ T : Matrix.GeneralLinearGroup (Fin r) ℂ, ∀ q : UnderlyingSpace ℂ (totalSpace E),
      mapFun (proj E) q = x → coord c₂ q = (T : Matrix (Fin r) (Fin r) ℂ) *ᵥ coord c₁ q := by
  have key : ∀ {d₁ d₂ : Chart E r}, x ∈ chartBase d₁ → x ∈ chartBase d₂ →
      ∀ q : UnderlyingSpace ℂ (totalSpace E), mapFun (proj E) q = x →
        coord d₂ q = transition d₁ d₂ x *ᵥ coord d₁ q := by
    intro d₁ d₂ hd₁ hd₂ q hq
    have h := coord_eq_transition_mulVec d₁ d₂ q
      (top_le_preimage_proj_inf (by rw [hq]; exact ⟨hd₁, hd₂⟩))
    rwa [hq] at h
  have inv : ∀ {d₁ d₂ : Chart E r} (hd₁ : x ∈ chartBase d₁), x ∈ chartBase d₂ →
      transition d₂ d₁ x * transition d₁ d₂ x = 1 := by
    intro d₁ d₂ hd₁ hd₂
    refine Matrix.toLin'.injective (LinearMap.ext fun w ↦ ?_)
    have hq := mapFun_proj_chartInv d₁ x hd₁ w
    have e₁ := key hd₁ hd₂ _ hq
    have e₂ := key hd₂ hd₁ _ hq
    rw [e₁, Matrix.mulVec_mulVec, coord_chartInv d₁ x hd₁ w] at e₂
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, ← e₂]
  exact ⟨⟨transition c₁ c₂ x, transition c₂ c₁ x, inv h₂ h₁, inv h₁ h₂⟩,
    fun q hq ↦ key h₁ h₂ q hq⟩

end Transition

variable (R : Type) [CommRing R] {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [X'.Over (Spec (.of ℂ))] {r : ℕ} {E : X.Modules} [E.IsQuasicoherent]
  {E' : X'.Modules} [E'.IsQuasicoherent]
  (f : X' ⟶ X) [f.IsOver (Spec (.of ℂ))] (F : totalSpace E' ⟶ totalSpace E)
  [F.IsOver (Spec (.of ℂ))]

section BundleMap

variable {f F}

/-- `π ∘ F = f ∘ π'` on complex points. -/
lemma mapFun_proj_mapFun (hπ : F ≫ proj E = proj E' ≫ f)
    (q : UnderlyingSpace ℂ (totalSpace E')) :
    mapFun (proj E) (mapFun F q) = mapFun f (mapFun (proj E') q) :=
  UnderlyingSpace.ext (by simp only [toHom_mapFun, Category.assoc, hπ])

variable (f F r) in
/-- The bundle map `F : 𝐕(ℰ') ⟶ 𝐕(ℰ)` over `f` is a *fibrewise isomorphism* (linear and invertible
on each fibre) on complex points: around every `x' ∈ X'(ℂ)` there are charts `c'` of `ℰ'` and `c`
of `ℰ` with `coord c ∘ F = A · coord c'` on the fibre over `x'`, for some `A ∈ GL(r, ℂ)`. -/
def IsFibrewiseIso : Prop :=
  ∀ x' : UnderlyingSpace ℂ X', ∃ (c' : Chart E' r) (c : Chart E r)
    (A : Matrix.GeneralLinearGroup (Fin r) ℂ), x' ∈ chartBase c' ∧ mapFun f x' ∈ chartBase c ∧
      ∀ q, mapFun (proj E') q = x' →
        coord c (mapFun F q) = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ coord c' q

/-- For a fibrewise isomorphism `F`, every chart `c'` of `ℰ'` around `x'` has a chart `c`
of `ℰ` around `f(x')` in which `coord c ∘ F = A · coord c'` on the fibre over `x'`. -/
lemma IsFibrewiseIso.exists_coord_mapFun (hF : IsFibrewiseIso r f F)
    {x' : UnderlyingSpace ℂ X'} (c' : Chart E' r) (hx' : x' ∈ chartBase c') :
    ∃ (c : Chart E r) (A : Matrix.GeneralLinearGroup (Fin r) ℂ), mapFun f x' ∈ chartBase c ∧
      ∀ q, mapFun (proj E') q = x' →
        coord c (mapFun F q) = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ coord c' q := by
  obtain ⟨c₀, c, A, h₀, hc, hA⟩ := hF x'
  obtain ⟨T, hT⟩ := exists_coord_eq_mulVec c' c₀ hx' h₀
  refine ⟨c, A * T, hc, fun q hq ↦ ?_⟩
  rw [hA q hq, hT q hq, Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_mul]

variable [IsFiniteLocallyFreeOfRank.{0, 0, 0} E' r]

/-- A fibrewise isomorphism `F` maps exactly the zero section of `𝐕(ℰ')` to the zero
section of `𝐕(ℰ)`: `F⁻¹(0_ℰ(ℂ)) = 0_{ℰ'}(ℂ)`. -/
theorem preimage_range_zeroSection_of_fibrewise (hπ : F ≫ proj E = proj E' ≫ f)
    (hF : IsFibrewiseIso r f F) :
    UnderlyingSpace.map (K := ℂ) F ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) =
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E')) := by
  ext q
  obtain ⟨c', hc'⟩ := exists_mem_chartBase E' r (mapFun (proj E') q)
  obtain ⟨c, A, hc, hA⟩ := hF.exists_coord_mapFun c' hc'
  have hFq : mapFun F q ∈ chartTotalOpens c := by
    change mapFun (proj E) (mapFun F q) ∈ chartBase c
    rwa [mapFun_proj_mapFun hπ]
  rw [mem_preimage, mem_range_zeroSection_iff_coord_eq_zero c' q hc']
  change mapFun F q ∈ _ ↔ _
  rw [mem_range_zeroSection_iff_coord_eq_zero c _ hFq, hA q rfl]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, Matrix.mulVec_zero]⟩
  simpa [Matrix.mulVec_mulVec] using
    congrArg (((A⁻¹ : Matrix.GeneralLinearGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ ·) h

/-- `F` maps the complement of the zero section of `𝐕(ℰ')` into that of `𝐕(ℰ)`. -/
lemma compl_range_zeroSection_subset_of_fibrewise (hπ : F ≫ proj E = proj E' ≫ f)
    (hF : IsFibrewiseIso r f F) :
    (range (UnderlyingSpace.map (K := ℂ) (zeroSection E')))ᶜ ⊆
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) F)) ⁻¹'
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ := by
  intro q hq h
  exact hq (by rwa [← preimage_range_zeroSection_of_fibrewise hπ hF])

omit [IsFiniteLocallyFreeOfRank.{0, 0, 0} E' r] in
/-- A complex frame of `𝐕(ℰ')`, followed by a fibrewise isomorphism `F`, is a complex frame
of `𝐕(ℰ)`. -/
lemma IsComplexFrame.comp_of_fibrewise (hπ : F ≫ proj E = proj E' ≫ f)
    (hF : IsFibrewiseIso r f F) {g : (Fin r → ℂ) → UnderlyingSpace ℂ (totalSpace E')}
    (hg : IsComplexFrame E' r g) :
    IsComplexFrame E r fun w ↦ mapFun F (g w) := by
  obtain ⟨x', c', A', hx', h⟩ := hg
  obtain ⟨c, A, hc, hA⟩ := hF.exists_coord_mapFun c' hx'
  refine ⟨mapFun f x', c, A * A', hc, fun w ↦ ⟨?_, ?_⟩⟩
  · rw [mapFun_proj_mapFun hπ, (h w).1]
  · rw [hA _ (h w).1, (h w).2, Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_mul]

variable [IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- **Naturality of the Thom class** (Fulton, §19.1): the Thom class of `𝐕(ℰ')` is the pull-back
of the Thom class of `𝐕(ℰ)` along a fibrewise isomorphism `F : 𝐕(ℰ') ⟶ 𝐕(ℰ)`. -/
theorem thomClass_eq_map_of_fibrewise (hπ : F ≫ proj E = proj E' ≫ f)
    (hF : IsFibrewiseIso r f F) :
    thomClass R E' r =
      (relativeSingularCohomology.map R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) F))
        (compl_range_zeroSection_subset_of_fibrewise hπ hF) _).hom (thomClass R E r) := by
  symm
  refine eq_thomClass fun g hg v hv ↦ ?_
  exact (SingularCochain.relEval_single_map (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) F))
    (compl_range_zeroSection_subset_of_fibrewise hπ hF) (g.comp (ThomClass.affineSimplex v))
    _ _ (thomClass R E r)).trans (isThomClass_thomClass R E r
      ((UnderlyingSpace.map (K := ℂ) F).comp g) (hg.comp_of_fibrewise hπ hF) v hv)

end BundleMap

section Section

variable {f F} (σ : X ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))]
  (σ' : X' ⟶ totalSpace E') [σ'.IsOver (Spec (.of ℂ))]

/-- `F ∘ σ' = σ ∘ f` on complex points. -/
lemma mapFun_mapFun_of_comp (hσσ : σ' ≫ F = f ≫ σ) (y : UnderlyingSpace ℂ X') :
    mapFun F (mapFun σ' y) = mapFun σ (mapFun f y) :=
  UnderlyingSpace.ext (by simp only [toHom_mapFun, Category.assoc, hσσ])

variable [IsFiniteLocallyFreeOfRank.{0, 0, 0} E' r]

/-- **The zero locus of a compatible section**: `σ'⁻¹(0_{ℰ'}(ℂ)) = f⁻¹(σ⁻¹(0_ℰ(ℂ)))`. -/
theorem preimage_zeroLocus_of_comp (hπ : F ≫ proj E = proj E' ≫ f)
    (hF : IsFibrewiseIso r f F) (hσσ : σ' ≫ F = f ≫ σ) :
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ')).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E')) =
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) := by
  refine Set.ext fun p ↦ ?_
  change mapFun σ' p ∈ range (UnderlyingSpace.map (K := ℂ) (zeroSection E')) ↔
    mapFun σ (mapFun f p) ∈ range (UnderlyingSpace.map (K := ℂ) (zeroSection E))
  rw [← preimage_range_zeroSection_of_fibrewise hπ hF, mem_preimage]
  change mapFun F (mapFun σ' p) ∈ range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) ↔ _
  rw [mapFun_mapFun_of_comp σ σ' hσσ]

/-- The restriction `σ'⁻¹(0_{ℰ'}(ℂ)) → σ⁻¹(0_ℰ(ℂ))` of `f` on complex points. -/
def zeroLocusMap (hπ : F ≫ proj E = proj E' ≫ f) (hF : IsFibrewiseIso r f F)
    (hσσ : σ' ≫ F = f ≫ σ) :
    TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ')).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E'))) ⟶
    TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) :=
  borelMooreHomology.subsetInclusionOfSubset (preimage_zeroLocus_of_comp σ σ' hπ hF hσσ).le ≫
    TopCat.ofHom ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom.restrictPreimage _)

/-- The image of a point `p` under `zeroLocusMap` is `f(p)` as a complex point of `X`. -/
@[simp]
lemma coe_zeroLocusMap_apply (hπ : F ≫ proj E = proj E' ≫ f) (hF : IsFibrewiseIso r f F)
    (hσσ : σ' ≫ F = f ≫ σ) (p) :
    ((zeroLocusMap σ σ' hπ hF hσσ p : _) : UnderlyingSpace ℂ X) = mapFun f p.1 :=
  rfl

/-- The restriction `f_D` of a proper morphism `f` to the zero loci is proper. -/
lemma isProperMap_zeroLocusMap [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [IsProper f]
    (hπ : F ≫ proj E = proj E' ≫ f) (hF : IsFibrewiseIso r f F) (hσσ : σ' ≫ F = f ≫ σ) :
    IsProperMap (zeroLocusMap σ σ' hπ hF hσσ) :=
  ((isProperMap_map (K := ℂ) f).restrictPreimage _).comp
    (borelMooreHomology.isProperMap_subsetInclusionOfSubset
      (isClosed_range_zeroSection.preimage (continuous_mapFun σ')) _)

variable [IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- **`σ'^* u_{ℰ'} = f^*(σ^* u_ℰ)`** in `H^{2r}(X'(ℂ), X'(ℂ) - f⁻¹(σ⁻¹(0)))`: the pull-back of the
Thom class of `𝐕(ℰ')` along `σ'` is the pull-back along `f` of that of `𝐕(ℰ)` along `σ`. -/
theorem forget_pullback_thomClass_of_comp (hπ : F ≫ proj E = proj E' ≫ f)
    (hF : IsFibrewiseIso r f F) (hσσ : σ' ≫ F = f ≫ σ) :
    (cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X'))
        (preimage_zeroLocus_of_comp σ σ' hπ hF hσσ).le _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ')) _ _).hom (thomClass R E' r)) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) _ _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)) _ _).hom (thomClass R E r)) := by
  rw [thomClass_eq_map_of_fibrewise R hπ hF]
  exact relativeSingularCohomology.map_hom_map_hom_map_hom_eq R _ _ _ _ _ _ _ _ _ _
    (ConcreteCategory.hom_ext _ _ fun p ↦ mapFun_mapFun_of_comp σ σ' hσσ p) _ _

/-- **The localized top Chern class commutes with proper push-forward** (Fulton, §19.1, proof of
Lemma 19.1.3). For a proper morphism `f : X' → X` of complex schemes, a fibrewise isomorphism
`F : 𝐕(ℰ') ⟶ 𝐕(ℰ)` over `f`, morphisms `σ : X ⟶ 𝐕(ℰ)`, `σ' : X' ⟶ 𝐕(ℰ')` with
`F ∘ σ' = σ ∘ f`, and `a ∈ H_k X'`, `f_{D*}(σ'^* u_{ℰ'} ∩ a) = σ^* u_ℰ ∩ f_* a` in
`H_{k-2r}(σ⁻¹(0_ℰ(ℂ)))`, where `f_D : σ'⁻¹(0_{ℰ'}(ℂ)) → σ⁻¹(0_ℰ(ℂ))` is the restriction of
`f`. -/
theorem pushforward_localizedTopChernCap_of_comp [IsComplexScheme X] [IsComplexScheme X']
    [IsProper f] (hπ : F ≫ proj E = proj E' ≫ f) (hF : IsFibrewiseIso r f F)
    (hσσ : σ' ≫ F = f ≫ σ) (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X')) k) :
    (borelMooreHomology.pushforward R (ModuleCat.of R R) (zeroLocusMap σ σ' hπ hF hσσ)
        (isProperMap_zeroLocusMap σ σ' hπ hF hσσ) (k - (2 * r : ℕ))).hom
        (localizedTopChernCap σ' R r k a) =
      localizedTopChernCap σ R r k ((borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) (isProperMap_map (K := ℂ) f) k).hom a) := by
  have hA := preimage_zeroLocus_of_comp σ σ' hπ hF hσσ
  have hBd : HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) :=
    hA ▸ hasProperNeighbourhoodDeformations_preimage σ'
  have hAc : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ')).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (zeroSection E'))) :=
    isClosed_range_zeroSection.preimage (continuous_mapFun σ')
  have hBc : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom ⁻¹'
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))) :=
    (isClosed_range_zeroSection.preimage (continuous_mapFun σ)).preimage (continuous_mapFun f)
  have e := congrArg
    (fun φ ↦ ModuleCat.Hom.hom φ (localizedTopChernCap σ' R r k a))
    (borelMooreHomology.pushforward_comp R (ModuleCat.of R R)
      (borelMooreHomology.subsetInclusionOfSubset hA.le)
      (TopCat.ofHom ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom.restrictPreimage
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
            range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))))
      (borelMooreHomology.isProperMap_subsetInclusionOfSubset hAc hA.le)
      ((isProperMap_map (K := ℂ) f).restrictPreimage _) (k - (2 * r : ℕ)))
  refine e.trans ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, localizedTopChernCap,
    borelMooreHomology.capProductSupportPullback_apply,
    borelMooreHomology.pushforward_subsetInclusionOfSubset_capProductSupport R _ hAc hBc _ hBd
      hA.le,
    forget_pullback_thomClass_of_comp R σ σ' hπ hF hσσ,
    ← borelMooreHomology.capProductSupportPullback_apply,
    borelMooreHomology.pushforward_restrictPreimage_capProductSupportPullback R _ _ _
      (hasProperNeighbourhoodDeformations_preimage σ)]
  rfl

end Section

end MMP.Modules
