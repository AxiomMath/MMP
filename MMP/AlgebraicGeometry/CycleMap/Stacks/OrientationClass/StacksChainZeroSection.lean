module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Unique.StacksGlue
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksNormalFibreChart
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionPullback
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalizationThom
public import MMP.AlgebraicGeometry.RegularImmersion.OfSmooth
public import MMP.AlgebraicTopology.ThomClass.Natural
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import MMP.AlgebraicTopology.SingularCohomology.Relative.MapCongr
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksPreimageSubvarietyGeneric

/-!
# The orientation class of the zero section of a Stacks vector bundle is the Thom class

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a scheme `X` over
`ℂ`, with vector bundle `π : 𝐕(ℰ) ⟶ X` and zero section `i : X ⟶ 𝐕(ℰ)`. The tautological section
`τ : 𝐕(ℰ) ⟶ 𝐕(π^*ℰ) = 𝐕(ℰ) ×_X 𝐕(ℰ)`, the diagonal, has zero scheme `X` (scheme-theoretically),
and `(π^*ℰ, τ, V = 𝐕(ℰ)(ℂ), Q = π^*𝐕(ℰ)(ℂ))` is an orientation datum of `i`
(`MMP.Modules.RegularImbeddingOrientationDatum`): the quotient bundle is `Q = π^*𝐕(ℰ)(ℂ)` itself
(`C = 0`), and `τ̄` followed by the bundle map `π^*𝐕(ℰ)(ℂ) → 𝐕(ℰ)(ℂ)` is the identity. Hence
`τ̄^*(u_Q) = u_ℰ`, and the Thom class `u_ℰ` is an orientation class of `i` (Fulton, §19.2 (i)).

## Main results

* `MMP.Modules.tautologicalSection`: the tautological section `τ` of `𝐕(π^*ℰ)` over `𝐕(ℰ)`.
* `MMP.Modules.zeroLocus_tautologicalSection`: `Z(τ) = X`.
* `MMP.Modules.isRegularClosedImmersionOfCodim_zeroSection`: the zero section is a regular
  closed immersion of codimension `r`.
* `MMP.Modules.zeroSectionOrientationDatum`: the orientation datum `(π^*ℰ, τ, 𝐕(ℰ)(ℂ), π^*𝐕(ℰ))`.
* `MMP.Modules.isRegularImbeddingOrientationClass_thomClass`: `u_ℰ` is an orientation class of
  the zero section.
* `MMP.Modules.eq_thomClass_of_isRegularImbeddingOrientationClass`: `u_{X,𝐕(ℰ)} = u_ℰ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2 (i).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle Topology
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)
open scoped Matrix

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

namespace MMP.Modules

open UnderlyingSpace

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-! ### The tautological section -/

/-- The pulled-back module `π^*ℰ` on `𝐕(ℰ)`. -/
abbrev pullbackSelf : (totalSpace E).Modules := (Scheme.Modules.pullback (proj E)).obj E

/-- **The tautological section** `τ : 𝐕(ℰ) ⟶ 𝐕(π^*ℰ) = 𝐕(ℰ) ×_X 𝐕(ℰ)`, the diagonal. -/
def tautologicalSection : totalSpace E ⟶ totalSpace (pullbackSelf E) :=
  (Scheme.Modules.isPullback_vectorBundleBaseChangeMap (proj E) E).lift (𝟙 _) (𝟙 _) rfl

/-- The tautological section followed by the first projection `𝐕(π^*ℰ) ⟶ 𝐕(ℰ)` is the identity. -/
@[reassoc (attr := simp)]
lemma tautologicalSection_baseChangeMap :
    tautologicalSection E ≫ baseChangeMap (proj E) E = 𝟙 _ :=
  IsPullback.lift_fst _ _ _ _

/-- The tautological section is a section of the projection `𝐕(π^*ℰ) ⟶ 𝐕(ℰ)`. -/
@[reassoc (attr := simp)]
lemma tautologicalSection_proj : tautologicalSection E ≫ proj (pullbackSelf E) = 𝟙 _ :=
  IsPullback.lift_snd _ _ _ _

/-- For `X` over `ℂ`, the tautological section is a morphism over `Spec ℂ`. -/
instance isOver_tautologicalSection [X.Over (Spec (.of ℂ))] :
    (tautologicalSection E).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change tautologicalSection E ≫ proj (pullbackSelf E) ≫ totalSpace E ↘ Spec (.of ℂ) =
      totalSpace E ↘ Spec (.of ℂ)
    rw [tautologicalSection_proj_assoc]⟩

/-- **The zero scheme of the tautological section is the zero section**: `Z(τ) = X`. -/
theorem zeroLocus_tautologicalSection :
    zeroLocus (pullbackSelf E) (tautologicalSection E) = (zeroSection E).ker := by
  rw [zeroLocus, ker_zeroSection_pullback, ← Scheme.IdealSheafData.comap_comp,
    tautologicalSection_baseChangeMap, Scheme.IdealSheafData.comap_id]

include r in
/-- **The zero section of a vector bundle is a regular closed immersion of codimension `r`**: it
is a section of the smooth morphism `π` of relative dimension `r` (Stacks 067U). -/
theorem isRegularClosedImmersionOfCodim_zeroSection [IsLocallyNoetherian X] :
    IsRegularClosedImmersionOfCodim (zeroSection E) r := by
  haveI : SmoothOfRelativeDimension (0 + r) (proj E) := by
    rw [zero_add]
    exact Stacks.Chow.smoothOfRelativeDimension_of_isAffineSpaceBundle (proj E) r
      (isAffineSpaceBundle_proj E r)
  haveI : SmoothOfRelativeDimension 0 (zeroSection E ≫ proj E) := by
    rw [zeroSection_proj]
    infer_instance
  exact isRegularClosedImmersionOfCodim_of_smoothOfRelativeDimension (zeroSection E) (proj E)
    (n := 0)

variable [X.Over (Spec (.of ℂ))]

/-- `pr₁ ∘ τ = id` on complex points. -/
lemma mapFun_baseChangeMap_mapFun_tautologicalSection (y : UnderlyingSpace ℂ (totalSpace E)) :
    mapFun (baseChangeMap (proj E) E) (mapFun (tautologicalSection E) y) = y :=
  UnderlyingSpace.ext (by
    change (y.toHom ≫ tautologicalSection E) ≫ baseChangeMap (proj E) E = y.toHom
    rw [Category.assoc, tautologicalSection_baseChangeMap, Category.comp_id])

/-! ### The quotient bundle `Q = π^*𝐕(ℰ)(ℂ)` -/

/-- The projection `𝐕(ℰ)(ℂ) → X(ℂ)`, on the neighbourhood `V = 𝐕(ℰ)(ℂ)` of the zero section. -/
def zeroSectionNbhdProj :
    C((univ : Set (UnderlyingSpace ℂ (totalSpace E))), UnderlyingSpace ℂ X) :=
  ⟨fun y ↦ mapFun (proj E) y.1, (continuous_mapFun _).comp continuous_subtype_val⟩

/-- The quotient bundle `Q = π^*𝐕(ℰ)(ℂ)` (with `C = 0`). -/
abbrev ZeroSectionQ := (zeroSectionNbhdProj E) *ᵖ (Fibre E r)

variable {E r} in
/-- Two points of `Q` are equal if they have the same base point and the same underlying point of
`𝐕(ℰ)(ℂ)` in the fibre. -/
lemma zeroSectionQ_ext {p q : TotalSpace (Fin r → ℂ) (ZeroSectionQ E r)} (h₁ : p.proj = q.proj)
    (h₂ : (p.2 : Fibre E r _).1 = (q.2 : Fibre E r _).1) : p = q := by
  obtain ⟨b, v⟩ := p
  obtain ⟨b', v'⟩ := q
  obtain rfl : b = b' := h₁
  exact congrArg (TotalSpace.mk b) (Subtype.ext h₂)

/-- The quotient map `𝐕(π^*ℰ)(ℂ) → Q`, the identity: `(e', e) ↦ e'` in the fibre over `e`. -/
def zeroSectionQuot
    (p : {p : UnderlyingSpace ℂ (totalSpace (pullbackSelf E)) // mapFun (proj (pullbackSelf E)) p ∈
      (univ : Set (UnderlyingSpace ℂ (totalSpace E)))}) :
    TotalSpace (Fin r → ℂ) (ZeroSectionQ E r) :=
  ⟨⟨mapFun (proj (pullbackSelf E)) p.1, mem_univ _⟩,
    (⟨mapFun (baseChangeMap (proj E) E) p.1, mapFun_proj_mapFun_baseChangeMap (proj E) E p.1⟩ :
      Fibre E r (mapFun (proj E) (mapFun (proj (pullbackSelf E)) p.1)))⟩

/-- The quotient map `𝐕(π^*ℰ)(ℂ) → Q` is continuous. -/
lemma continuous_zeroSectionQuot : Continuous (zeroSectionQuot E r) := by
  change Continuous[_, pullbackTopology (Fin r → ℂ) (Fibre E r) (zeroSectionNbhdProj E)] _
  rw [pullbackTopology_def]
  exact continuous_inf_rng.2 ⟨continuous_induced_rng.2
    (((continuous_mapFun _).comp continuous_subtype_val).subtype_mk _),
    continuous_induced_rng.2 (by
      exact (isInducing_totalSpaceEquiv E r).continuous_iff.2
        ((continuous_mapFun (baseChangeMap (proj E) E)).comp continuous_subtype_val))⟩

variable {E r} in
/-- The fibre coordinates of a chart `c` identify the fibre over `x ∈ V(ℂ)` with `ℂʳ`,
linearly. -/
def fibreCoordEquiv (c : Chart E r) (x : UnderlyingSpace ℂ X) (hx : x ∈ chartBase c) :
    Fibre E r x ≃ₗ[ℂ] (Fin r → ℂ) :=
  LinearEquiv.ofBijective (fibreCoord c x)
    ⟨fun v v' h ↦ fibre_ext c hx (by
        rw [← fibreCoord_apply c x hx, ← fibreCoord_apply c x hx]; exact h),
      fun w ↦ ⟨fibreChartInv c x hx w, by
        rw [fibreCoord_apply c x hx]; exact coord_chartInv c x hx w⟩⟩

variable {E r} in
/-- At a point `x` of `𝐕(ℰ)(ℂ)`, every chart `c'` of `π^*ℰ` around `x` and the chart `c` of `ℰ`
around `π(x)` are related on the fibre over `x` by an invertible matrix:
`x^c(pr₁ q) = M · x^{c'}(q)`. -/
lemma exists_gl_coord_baseChangeMap_self (c' : Chart (pullbackSelf E) r)
    (x : UnderlyingSpace ℂ (totalSpace E)) (hx : x ∈ chartBase c') :
    ∃ M : GL (Fin r) ℂ, ∀ q, mapFun (proj (pullbackSelf E)) q = x →
      coord (chartAt E r (mapFun (proj E) x)) (mapFun (baseChangeMap (proj E) E) q) =
        (M : Matrix (Fin r) (Fin r) ℂ) *ᵥ coord c' q := by
  set c := chartAt E r (mapFun (proj E) x)
  have hc : mapFun (proj E) x ∈ chartBase c := mem_chartBase_chartAt E r _
  have hxW : x.toHom (IsLocalRing.closedPoint ℂ) ∈ proj E ⁻¹ᵁ c.1.1 :=
    (top_le_preimage_iff x _).1 hc
  obtain ⟨c'', hc''x, hc''le⟩ := exists_chart_mem_le (E := pullbackSelf E) (r := r) hxW
  have hx'' : x ∈ chartBase c'' := (top_le_preimage_iff x _).2 hc''x
  obtain ⟨A, hA⟩ := exists_gl_coord_baseChangeMap (proj E) E c c'' hc''le x hx''
  obtain ⟨T, hT⟩ := exists_coord_eq_mulVec c' c'' hx hx''
  refine ⟨A * T, fun q hq ↦ ?_⟩
  rw [hA q hq, hT q hq, Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_mul]

variable [IsLocallyNoetherian X]

/-- **The orientation datum of a zero section**: `ℰ' = π^*ℰ` with the tautological section `τ`,
`V = 𝐕(ℰ)(ℂ)` and `Q = π^*𝐕(ℰ)(ℂ)` (so `C = 0`). -/
def zeroSectionOrientationDatum : RegularImbeddingOrientationDatum (zeroSection E) r where
  rank := r
  le_rank := le_rfl
  E := pullbackSelf E
  σ := tautologicalSection E
  comp_proj := tautologicalSection_proj E
  zeroLocus_eq := zeroLocus_tautologicalSection E
  nbhd := univ
  isOpen_nbhd := isOpen_univ
  range_subset_nbhd := subset_univ _
  F := Fin r → ℂ
  finrank_F := Module.finrank_fin_fun ℂ
  Q := ZeroSectionQ E r
  quot := zeroSectionQuot E r
  continuous_quot := continuous_zeroSectionQuot E r
  proj_quot _ := rfl
  fibre c' x hx hxV := by
    have hxc : x ∈ chartBase c' := hx
    set y := mapFun (proj E) x
    set c := chartAt E r y
    have hy : y ∈ chartBase c := mem_chartBase_chartAt E r y
    obtain ⟨M, hM⟩ := exists_gl_coord_baseChangeMap_self c' x hxc
    let L : (Fin r → ℂ) →ₗ[ℂ] Fibre E r y :=
      (fibreCoordEquiv c y hy).symm.toLinearMap ∘ₗ (M : Matrix (Fin r) (Fin r) ℂ).mulVecLin
    have hL : ∀ w, fibreCoord c y (L w) = (M : Matrix (Fin r) (Fin r) ℂ) *ᵥ w := fun w ↦
      (fibreCoordEquiv c y hy).apply_symm_apply _
    have hLinj : Function.Injective L := by
      intro w w' h
      have h' := congrArg (fibreCoord c y) h
      rw [hL, hL] at h'
      have := congrArg (fun v ↦ ((M⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ v) h'
      simpa [Matrix.mulVec_mulVec] using this
    have hLsurj : Function.Surjective L := by
      intro v
      refine ⟨((M⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ fibreCoord c y v, ?_⟩
      refine (fibreCoordEquiv c y hy).injective ?_
      change fibreCoord c y (L _) = fibreCoord c y v
      rw [hL, Matrix.mulVec_mulVec]
      simp
    refine ⟨L, fun w ↦ ?_, hLsurj, ?_⟩
    · have hq := mapFun_proj_chartInv c' x hx w
      refine zeroSectionQ_ext (Subtype.ext hq) ?_
      change mapFun (baseChangeMap (proj E) E) (chartInv c' x hx w) = (L w).1
      have h1 : mapFun (proj E) (mapFun (baseChangeMap (proj E) E) (chartInv c' x hx w)) = y := by
        rw [mapFun_proj_mapFun_baseChangeMap, hq]
      have h2 : mapFun (proj E) (L w).1 = y := (L w).2
      have hm1 : mapFun (baseChangeMap (proj E) E) (chartInv c' x hx w) ∈ chartTotalOpens c := by
        change mapFun (proj E) _ ∈ chartBase c
        rw [h1]; exact hy
      have hm2 : (L w).1 ∈ chartTotalOpens c := by
        change mapFun (proj E) _ ∈ chartBase c
        rw [h2]; exact hy
      have := (chartHomeomorph c).injective (a₁ := ⟨_, hm1⟩) (a₂ := ⟨_, hm2⟩)
        (Prod.ext (Subtype.ext (h1.trans h2.symm)) (by
          change coord c _ = coord c _
          rw [hM _ hq, ← fibreCoord_apply c y hy, hL, coord_chartInv]))
      exact congrArg Subtype.val this
    · rintro ⟨x₀, rfl⟩
      have hN : normalFibre (tautologicalSection E) c' (UnderlyingSpace.map (zeroSection E) x₀) =
          ⊤ :=
        Submodule.eq_top_of_finrank_eq ((finrank_normalFibre (zeroSection E)
          (isRegularClosedImmersionOfCodim_zeroSection E r) (tautologicalSection_proj E)
          (zeroLocus_tautologicalSection E) c' x₀ hx).trans (Module.finrank_fin_fun ℂ).symm)
      rw [hN]
      have hk : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.2 hLinj
      exact hk ▸ isCompl_bot_top
  quot_sec_notMem y hy := by
    rintro ⟨b, hb⟩
    have h2 := congrArg (fun p : TotalSpace (Fin r → ℂ) (ZeroSectionQ E r) ↦
      (p.2 : Fibre E r _).1) hb
    change (0 : Fibre E r (zeroSectionNbhdProj E b)).1 =
      mapFun (baseChangeMap (proj E) E) (mapFun (tautologicalSection E) y.1) at h2
    rw [zero_fibre_val, mapFun_baseChangeMap_mapFun_tautologicalSection] at h2
    exact hy ⟨_, h2⟩

variable (R : Type) [CommRing R]

/-- The Thom class `u_Q = π̃^* u_ℰ` of the quotient bundle `Q = π^*𝐕(ℰ)(ℂ)` of the orientation
datum of the zero section. -/
def zeroSectionThomClassQ : cohomologyWithSupports R (ModuleCat.of R R)
    (TopCat.of (TotalSpace (Fin r → ℂ) (ZeroSectionQ E r)))
    (range (Bundle.zeroSection (Fin r → ℂ) (ZeroSectionQ E r)))
    (2 * Module.finrank ℂ (Fin r → ℂ) : ℕ) :=
  (relativeSingularCohomology.map R (ModuleCat.of R R)
    (pullbackBundleMap (Fin r → ℂ) (Fibre E r) (zeroSectionNbhdProj E))
    (pullbackBundleMap_compl_zeroSection (Fin r → ℂ) (Fibre E r) (zeroSectionNbhdProj E)) _).hom
    (ThomClass.thomClass R (Fin r → ℂ) (Fibre E r))

omit [IsLocallyNoetherian X] in
/-- The class `zeroSectionThomClassQ E r R` is a Thom class of the bundle `Q`. -/
lemma isThomClass_zeroSectionThomClassQ :
    MMP.IsThomClass (Fin r → ℂ) (ZeroSectionQ E r) (zeroSectionThomClassQ E r R) :=
  (ThomClass.isThomClass_thomClass (R := R) (Fin r → ℂ) (Fibre E r)).pullback _ _ _

/-- `τ̄ : 𝐕(ℰ)(ℂ) → Q` followed by the bundle map `Q = π^*𝐕(ℰ)(ℂ) → 𝐕(ℰ)(ℂ)` is the identity. -/
lemma sectionBarHom_comp_pullbackBundleMap :
    (𝟙 _ ≫ (zeroSectionOrientationDatum E r).sectionBarHom) ≫
        pullbackBundleMap (Fin r → ℂ) (Fibre E r) (zeroSectionNbhdProj E) =
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C((univ : Set (UnderlyingSpace ℂ (totalSpace E))), UnderlyingSpace ℂ (totalSpace E)))) ≫
        totalSpaceInv E r := by
  refine ConcreteCategory.hom_ext _ _ fun y ↦ ?_
  apply (totalSpaceHomeomorph E r).injective
  change mapFun (baseChangeMap (proj E) E) (mapFun (tautologicalSection E) y.1) =
    totalSpaceHomeomorph E r ((totalSpaceHomeomorph E r).symm y.1)
  rw [Homeomorph.apply_symm_apply, mapFun_baseChangeMap_mapFun_tautologicalSection]

/-- Under excision, `u_ℰ` corresponds to `τ̄^* u_Q`. -/
theorem excisionRestrict_thomClass :
    (RegularImbeddingOrientationDatum.excisionRestrict R _
        (univ : Set (UnderlyingSpace ℂ (totalSpace E))) _).hom (thomClass R E r) =
      ((zeroSectionOrientationDatum E r).thomPullback R).hom (zeroSectionThomClassQ E r R) := by
  rw [thomClass_eq_pullbackAlg R E r]
  simp only [RegularImbeddingOrientationDatum.excisionRestrict,
    RegularImbeddingOrientationDatum.thomPullback, cohomologyWithSupports.pullback,
    cohomologyWithSupports.forget, zeroSectionThomClassQ, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  erw [relativeSingularCohomology.map_hom_cast R _ _ _ (Module.finrank_fin_fun ℂ)]
  erw [relativeSingularCohomology.eqToHom_hom_eq_cast R _ (Module.finrank_fin_fun ℂ)]
  refine (relativeSingularCohomology.map_hom_cast R (ModuleCat.of R R) _ (fun _ hx ↦ hx)
    (Module.finrank_fin_fun ℂ) _).trans ?_
  congr 1
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  refine Eq.trans (congrArg (fun φ ↦ ModuleCat.Hom.hom φ
      (ThomClass.thomClass R (Fin r → ℂ) (Fibre E r)))
    (?_ : _ = relativeSingularCohomology.map R _
      (pullbackBundleMap (Fin r → ℂ) (Fibre E r) (zeroSectionNbhdProj E)) _ _ ≫
      relativeSingularCohomology.map R _ (zeroSectionOrientationDatum E r).sectionBarHom _ _ ≫
      relativeSingularCohomology.map R _ (𝟙 _) _ _)) rfl
  refine (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _).trans ?_
  refine Eq.trans ?_
    (congrArg (_ ≫ ·) (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _)).symm
  refine Eq.trans ?_ (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _).symm
  exact relativeSingularCohomology.map_congr_hom R _ _ _
    (sectionBarHom_comp_pullbackBundleMap E r).symm _

/-- **The orientation class of a zero section is the Thom class** (Fulton, §19.2 (i)): for `ℰ`
finite locally free of rank `r` on a scheme `X` over `ℂ` and the zero section `i : X → 𝐕(ℰ)`, the
Thom class `u_ℰ` is an orientation class of `i`. -/
theorem isRegularImbeddingOrientationClass_thomClass :
    IsRegularImbeddingOrientationClass R (zeroSection E) r (thomClass R E r) :=
  ⟨zeroSectionOrientationDatum E r, zeroSectionThomClassQ E r R,
    isThomClass_zeroSectionThomClassQ E r R, excisionRestrict_thomClass E r R⟩

/-- `u_{X,𝐕(ℰ)} = u_ℰ`: every orientation class of the zero section of `𝐕(ℰ)` is the Thom
class. -/
theorem eq_thomClass_of_isRegularImbeddingOrientationClass [IsComplexScheme (totalSpace E)]
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
      (range (UnderlyingSpace.map (zeroSection E))) (2 * r : ℕ)}
    (hu : IsRegularImbeddingOrientationClass R (zeroSection E) r u) : u = thomClass R E r :=
  IsRegularImbeddingOrientationClass.eq R (isRegularClosedImmersionOfCodim_zeroSection E r) hu
    (isRegularImbeddingOrientationClass_thomClass E r R)

end MMP.Modules
