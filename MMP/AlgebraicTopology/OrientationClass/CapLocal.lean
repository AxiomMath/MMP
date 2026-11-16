module

public import MMP.AlgebraicTopology.OrientationClass.CapAssembly
public import MMP.AlgebraicTopology.BorelMoore.Suspension
public import Mathlib.Topology.Metrizable.Urysohn

/-!
# `u_{M,P} ∩ μ_P` is locally the orientation generator of `M` (Fulton, §19.1)

Let `M` be a closed complex submanifold of positive codimension in a complex manifold `P`, with
orientation class `u`, and let `μ_P` be the fundamental class of `P`. At every point `x` of `M`
and for every chart `e'` of `M` at `x`, the cap product `u ∩ μ_P` is locally the class of a small
simplex `e'⁻¹ ∘ Δ` positively oriented for the complex orientation of the model of `M`. Hence
`u ∩ μ_P` is the fundamental class of `M`.

## Main results

* `MMP.IsOrientationClass.isLocallyClassOf_capProductSupport_small`: `u ∩ μ_P` is locally the
  class of a small positively oriented simplex in a chart of `M`.
* `MMP.IsOrientationClass.isFundamentalClass_capProductSupport_of_pos`: in positive codimension,
  `u ∩ μ_P` is the fundamental class of `M`.
-/

@[expose] public noncomputable section

open Set Bundle CategoryTheory Filter Topology Metric Manifold

universe u

namespace MMP

open MMP

open FundamentalClass borelMooreHomology BorelMooreCross BorelMooreCap ThomClass TensorProduct

variable (R : Type u) [CommRing R]

/-- The cap product with support commutes with transport along an equality of homological
degrees: capping `c` with `a` transported from degree `k` to `k'` gives, after reindexing to
degree `n`, the same class as capping `c` with `a`. -/
lemma capProductSupport_congrDegree (Y : TopCat.{u}) {X : Set Y} (hX : IsClosed X)
    (hXd : HasProperNeighbourhoodDeformations X) (j : ℤ) {k k' : ℤ} (h : k = k') {n : ℕ}
    (hn : k - j = n) (hn' : k' - j = n)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    congrDegree R _ hn' (capProductSupport R Y hX hXd j k' c (congrDegree R _ h a)) =
      congrDegree R _ hn (capProductSupport R Y hX hXd j k c a) := by
  subst h
  rfl

/-- Restriction of Borel–Moore homology to an open subset `V` commutes with transport along
equalities of degrees: restricting a class transported along `i = i'` and `i' = i''` equals
transporting its restriction along `i = i''`. -/
lemma restrict_congrDegree_congrDegree {Y : TopCat.{u}} [T2Space Y]
    (V : TopologicalSpace.Opens Y) {i i' i'' : ℤ} (h₁ : i = i') (h₂ : i' = i'') (h : i = i'')
    (x : borelMooreHomology R (ModuleCat.of R R) Y i) :
    restrict R (ModuleCat.of R R) V i'' (congrDegree R _ h₂ (congrDegree R _ h₁ x)) =
      congrDegree R _ h (restrict R (ModuleCat.of R R) V i x) := by
  subst h₁ h₂
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] [IsManifold 𝓘(ℂ, E) 1 P] [T2Space P]
  [SecondCountableTopology P] {M : Set P}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  [ChartedSpace E' M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]

/-- **`u_{M,P} ∩ μ_P = μ_M` at a point.** Let `M` be a closed complex submanifold
of positive codimension of `P` (second countable), with orientation class `u`, `μ_P` the
fundamental class of `P` and `e'` a chart of `M` at `x`. Then there is an affine simplex `Δ`
around `e' x` in the image of `e'`, positively oriented for the complex orientation of `E'`, such
that `u ∩ μ_P ∈ H_{2m} M` is locally the class of `e'⁻¹ ∘ Δ` at `x`. -/
theorem IsOrientationClass.isLocallyClassOf_capProductSupport_small
    (hM : IsComplexSubmanifold E E' M) (hMc : IsClosed M)
    (hXd : HasProperNeighbourhoodDeformations M) {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u)
    {μP : borelMooreHomology R (ModuleCat.of R R) P (2 * Module.finrank ℂ E : ℕ)}
    (hμP : IsFundamentalClass (M := P) R (complexOrientationBasisOf E) μP)
    (hF : 0 < Module.finrank ℂ F)
    (hdeg : ((2 * Module.finrank ℂ E : ℕ) : ℤ) - (2 * Module.finrank ℂ F : ℕ) =
      (2 * Module.finrank ℂ E' : ℕ))
    (x : M) {e' : OpenPartialHomeomorph M E'} (he' : e' ∈ atlas E' M) (hx : x ∈ e'.source) :
    ∃ v : Fin (2 * Module.finrank ℂ E' + 1) → E',
      IsOrientedSimplexAroundZero (complexOrientationBasisOf E') (fun k ↦ v k - e' x) ∧
      ∃ hvt : range (affineSimplex v) ⊆ e'.target,
        IsLocallyClassOf R (congrDegree R _ hdeg
          (capProductSupport R P hMc hXd _ _ u μP)) x
          (inclChainSimplex (chartOpens e') (chartSimplex e' v hvt)) := by
  classical
  have : TopologicalSpace.MetrizableSpace P := by
    have := ChartedSpace.locallyCompactSpace E P
    exact TopologicalSpace.metrizableSpace_of_t3_secondCountable P
  obtain ⟨U, hxU, hUe, K, f, hK, hf, hf0, hfo, htarget, hcompl, ⟨ε, hε, hball, hUeq⟩, hh, hA⟩ :=
    hu.exists_sliceMap_radialShrink R hM x he' hx
  set e := chartAt E (x : P) with he_def
  set γ : E' → E := fun z ↦ e (e'.symm z : P) with hγ_def
  have hγd : ∀ y : U, ContDiffAt ℂ 1 γ (e' y) ∧ Function.Injective (fderiv ℂ γ (e' y)) :=
    fun y ↦ hM e' he' e (chart_mem_atlas E (x : P)) (e' y) (e'.map_source (hUe y.2))
      (by rw [e'.left_inv (hUe y.2)]; exact (hcompl y).1)
  have hbij : ∀ y : U, Function.Bijective ((fderiv ℂ γ (e' y)).coprod K) := fun y ↦
    (bijective_coprod_iff _ K).2 ⟨(hγd y).2, hK, (hcompl y).2⟩
  have hd : Module.finrank ℂ E' + Module.finrank ℂ F = Module.finrank ℂ E := by
    have h1 := Submodule.finrank_add_eq_of_isCompl (hcompl ⟨x, hxU⟩).2
    rwa [LinearMap.finrank_range_of_inj (hγd _).2, LinearMap.finrank_range_of_inj hK] at h1
  have hUne : Nonempty U := ⟨⟨x, hxU⟩⟩
  set g : OpenPartialHomeomorph U E' := e'.subtypeRestr hUne with hg_def
  have hgs : g.source = univ := eq_univ_of_forall fun y ↦ by
    rw [hg_def, OpenPartialHomeomorph.subtypeRestr_source]
    exact hUe y.2
  let : ChartedSpace E' U := g.singletonChartedSpace hgs
  have hatlas : ∀ c ∈ atlas E' U, c = g := fun c hc ↦ g.singletonChartedSpace_mem_atlas_eq hgs c hc
  have hgy : ∀ y : U, g y = e' y := fun y ↦ rfl
  obtain ⟨μU, hμU⟩ := exists_isFundamentalClass_of_globalChart R (complexOrientationBasisOf E') g
    hgs (fun c hc ↦ by rw [hatlas c hc]; exact eqOn_refl _ _)
  obtain ⟨μF, hμF⟩ := exists_isFundamentalClass_of_basis R (complexOrientationBasisOf F)
  obtain ⟨u₀, hu₀⟩ := exists_isLocalOrientationClass (R := R) (T := TopCat.of F)
    (isOrientedAtlas_self F) (by omega : 0 < 2 * Module.finrank ℂ F) (complexOrientationBasisOf F)
    (0 : TopCat.of F)
  have h0d : HasProperNeighbourhoodDeformations ({0} : Set (TopCat.of F)) :=
    (hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton (TopCat.of PUnit.{u + 1})
      (T := TopCat.of F) F 0).preimage_homeomorph (Homeomorph.punitProd F).symm
  have hXd0 : HasProperNeighbourhoodDeformations
      (prSnd (TopCat.of U) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))) :=
    hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton (TopCat.of U) F
      (0 : TopCat.of F)
  have hdeg0 : ((2 * Module.finrank ℂ E' : ℕ) : ℤ) + (2 * Module.finrank ℂ F : ℕ) -
      (2 * Module.finrank ℂ F : ℕ) = (2 * Module.finrank ℂ E' : ℕ) := by omega
  have hfund := IsFundamentalClass.pushforward_capProductSupportPullback_prSnd R hμU hμF hu₀ h0d
    hXd0 hdeg0
  set y : U := ⟨x, hxU⟩
  have hyg : y ∈ g.source := hgs ▸ mem_univ y
  obtain ⟨v₀, hv₀, hv₀t⟩ := exists_isOrientedSimplexAroundZero_subset
    (complexOrientationBasisOf E') (g y) (g.open_target.mem_nhds (g.map_source hyg))
  have hσ := IsLocallyClassOf.of_restrict (chartOpens g)
    (hfund g (chart_mem_atlas E' y) ⟨y, hyg⟩ v₀ hv₀ hv₀t)
  set O : TopologicalSpace.Opens (TopCat.of (TopCat.of U × TopCat.of F)) := sliceCore U F
  have hOd : HasProperNeighbourhoodDeformations ((inclHom O).hom ⁻¹'
      (prSnd (TopCat.of U) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F)))) :=
    hasProperNeighbourhoodDeformations_sliceCore_zero U F
  set σ := inclChainSimplex (chartOpens g) (chartSimplex g v₀ hv₀t)
  have h0O : ∀ z : U, ((z, (0 : F)) : U × F) ∈ O := fun z ↦ by
    change ‖(0 : F)‖ < 1 / 2
    norm_num
  let τΩ : SingularChain.Simplex (TopCat.of ((inclHom O).hom ⁻¹'
      (prSnd (TopCat.of U) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))) _ :=
    ⟨fun t ↦ ⟨⟨(σ t, 0), h0O _⟩, rfl⟩, by fun_prop⟩
  have h1 := isLocallyClassOf_capProductSupportPullback_inclHom_prSnd R μU μF u₀ hXd0 hdeg0 O hOd
    hσ ⟨⟨(y, 0), h0O y⟩, rfl⟩ rfl τΩ (fun t ↦ rfl)
  have hUc : IsConnected (U : Set M) := by
    rw [hUeq, ← e'.symm_image_eq_source_inter_preimage hball]
    exact ((convex_ball _ _).isConnected (nonempty_ball.2 hε)).image _
      (e'.continuousOn_symm.mono hball)
  have : ConnectedSpace U := isConnected_iff_connectedSpace.1 hUc
  have hfe : ∀ (z : U) (w : F), ‖w‖ < 1 / 2 →
      γ (g z) + K w ∈ e.target ∧ f (z, w) = e.symm (γ (g z) + K w) := by
    intro z w hw
    have hr := radialShrink_of_norm_le hw.le
    have hγz : γ (g z) = e ((z : M) : P) := by
      simp only [hγ_def, hgy, e'.left_inv (hUe z.2)]
    refine ⟨?_, ?_⟩
    · rw [hγz, ← hr]
      exact htarget (z, w)
    · rw [hf (z, w), hγz, hr]
  have hγ : ∀ z : U, DifferentiableAt ℂ γ (g z) ∧
      Function.Bijective ((fderiv ℂ γ (g z)).coprod K) := fun z ↦
    ⟨(hγd z).1.differentiableAt one_ne_zero, hbij z⟩
  have hB3 := pushforward_sliceCoreHomeomorph_eq_restrict (P := (P : Type u)) (U := U) (F := F)
    (f := ⇑f) (γ := γ) (e := e)
    (μP := (μP : borelMooreHomology R (ModuleCat.of R R) (TopCat.of P) _)) R (by omega) hfo
    g hatlas (chart_mem_atlas E (x : P)) K hfe hγ (sliceCoreBasis hd)
    (IsFundamentalClass.restrict_sliceCore_exteriorProduct R hd hμU hμF) hμP
  have hk : ((2 * Module.finrank ℂ E' : ℕ) : ℤ) + (2 * Module.finrank ℂ F : ℕ) =
      (2 * Module.finrank ℂ E : ℕ) := by omega
  let a₁ := (restrict R (ModuleCat.of R R) O _).hom
    (borelMooreHomology.exteriorProduct R (TopCat.of U) (TopCat.of F)
      (2 * Module.finrank ℂ E' : ℕ) (2 * Module.finrank ℂ F : ℕ) (μU ⊗ₜ μF))
  let V := sliceCoreImage hfo
  let Φ := sliceCoreHomeomorph hfo
  have hB3' : (pushforward R (ModuleCat.of R R) (TopCat.ofHom (Φ : C(O, V))) Φ.isProperMap
      _).hom (congrDegree R _ hk a₁) = (restrict R (ModuleCat.of R R) V _).hom μP := by
    refine Eq.trans ?_ hB3
    congr 1
    exact (restrict_congrDegree_congrDegree R (Y := TopCat.of (U × F)) (sliceCore U F)
      (Nat.cast_add _ _).symm
      (congrArg Nat.cast (show 2 * Module.finrank ℂ E' + 2 * Module.finrank ℂ F =
        2 * Module.finrank ℂ E by omega)) hk _).symm
  have hX2 : IsClosed ((inclHom O).hom ⁻¹'
      (prSnd (TopCat.of U) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F)))) :=
    (isClosed_singleton.preimage (prSnd (TopCat.of U) (TopCat.of F)).hom.continuous).preimage
      (inclHom O).hom.continuous
  have h1' : IsLocallyClassOf R (congrDegree R _ hdeg (capProductSupport R (TopCat.of O) hX2 hOd
      _ _ ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom O) _ _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (prSnd (TopCat.of U) (TopCat.of F)) {0} _).hom u₀))
      (congrDegree R _ hk a₁))) ⟨⟨(y, 0), h0O y⟩, rfl⟩ τΩ := by
    rwa [capProductSupport_congrDegree R _ hX2 hOd _ hk hdeg0 hdeg]
  have hsub : (inclHom O).hom ⁻¹' (prSnd (TopCat.of U) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F)))
      ⊆ (TopCat.ofHom (Φ : C(O, V))).hom ⁻¹' ((inclHom V).hom ⁻¹' M) := by
    rintro ⟨⟨z, w⟩, hw⟩ (rfl : w = 0)
    change f (z, 0) ∈ M
    rw [hf0]
    exact z.1.2
  have hX'eq : (TopCat.ofHom (Φ : C(O, V))).hom ⁻¹' ((inclHom V).hom ⁻¹' M) =
      (inclHom O).hom ⁻¹' (prSnd (TopCat.of U) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))) :=
    subset_antisymm (fun p hp ↦ by_contra fun hp0 ↦ hh hp0 hp) hsub
  have hX'd : HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (Φ : C(O, V))).hom ⁻¹' ((inclHom V).hom ⁻¹' M)) := hX'eq ▸ hOd
  have hX' : IsClosed ((TopCat.ofHom (Φ : C(O, V))).hom ⁻¹' ((inclHom V).hom ⁻¹' M)) :=
    hX'eq ▸ hX2
  have hcomm : TopCat.ofHom (Φ : C(O, V)) ≫ inclHom V = inclHom O ≫ f := rfl
  have hc := forget_pullback_pullback_eq R f (inclHom O) (TopCat.ofHom (Φ : C(O, V))) (inclHom V)
    hcomm (prSnd (TopCat.of U) (TopCat.of F)) hh u u₀ (hA u₀ hu₀) hsub
  let τ' : SingularChain.Simplex
      (TopCat.of ((TopCat.ofHom (Φ : C(O, V))).hom ⁻¹' ((inclHom V).hom ⁻¹' M))) _ :=
    ⟨fun t ↦ ⟨τΩ t, hsub (τΩ t).2⟩, by fun_prop⟩
  have h2 := isLocallyClassOf_capProductSupport_forget R (TopCat.of O) hX2 hX' hOd hX'd hsub _ _
    hdeg _ _ hc _ h1' ⟨_, hsub (show ((⟨⟨(y, 0), h0O y⟩, rfl⟩ : TopCat.of ((inclHom O).hom ⁻¹'
      (prSnd (TopCat.of U) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))) : O) ∈ _ from rfl)⟩
    rfl τ' (fun t ↦ rfl)
  have hXVd : HasProperNeighbourhoodDeformations ((inclHom V).hom ⁻¹' M) := by
    convert hX'd.preimage_homeomorph Φ.symm using 1
    ext v
    change _ ↔ ((Φ (Φ.symm v) : V) : P) ∈ M
    rw [Φ.apply_symm_apply]
    exact Iff.rfl
  have hgt : g.target ⊆ e'.target := fun z hz ↦ by
    rw [← g.right_inv hz]
    exact e'.map_source (hUe (g.symm z).2)
  refine ⟨v₀, hv₀, hv₀t.trans hgt, ?_⟩
  refine isLocallyClassOf_capProductSupport_of_homeomorph R P hMc hXd V hXVd (W := TopCat.of O) Φ
    hX'd _ _ hdeg u μP _ hB3' h2 x (hf0 y).symm _ (fun t ↦ ?_)
  change ((e'.symm (affineSimplex v₀ t) : M) : P) = f (σ t, 0)
  rw [hf0]
  change _ = ((g.symm (affineSimplex v₀ t) : U) : P)
  rw [coe_subtypeRestr_symm_apply e' hUne (hv₀t ⟨t, rfl⟩)]

/-- **`u_{M,P} ∩ μ_P = μ_M` in positive codimension.** Let `M` be a closed complex submanifold
of positive codimension `d` of the second countable complex manifold `P`, with arbitrarily small
proper neighbourhood deformations, `u ∈ H^{2d}(P, P - M)` its orientation class and `μ_P` the
fundamental class of `P`. Then `u ∩ μ_P ∈ H_{2m} M` is the fundamental class of `M` for its
complex orientation. -/
theorem IsOrientationClass.isFundamentalClass_capProductSupport_of_pos
    (hM : IsComplexSubmanifold E E' M) (hMc : IsClosed M)
    (hXd : HasProperNeighbourhoodDeformations M) {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u)
    {μP : borelMooreHomology R (ModuleCat.of R R) P (2 * Module.finrank ℂ E : ℕ)}
    (hμP : IsFundamentalClass (M := P) R (complexOrientationBasisOf E) μP)
    (hF : 0 < Module.finrank ℂ F)
    (hdeg : ((2 * Module.finrank ℂ E : ℕ) : ℤ) - (2 * Module.finrank ℂ F : ℕ) =
      (2 * Module.finrank ℂ E' : ℕ)) :
    IsFundamentalClass (M := M) R (complexOrientationBasisOf E')
      (congrDegree R _ hdeg (capProductSupport R P hMc hXd _ _ u μP)) := by
  intro e' he' x v hv hvt
  obtain ⟨v₀, hv₀, hv₀t, h⟩ :=
    hu.isLocallyClassOf_capProductSupport_small R hM hMc hXd hμP hF hdeg x.1 he' x.2
  refine IsLocallyClassOf.restrict (chartOpens e') (h.of_isLocallyHomologous ?_)
  exact isLocallyHomologous_of_isOrientedSimplexAroundZero e' x.2 hv₀ hv₀t hv hvt
    (fun _ ↦ rfl) (fun _ ↦ rfl)

end MMP
