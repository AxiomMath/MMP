module
public import MMP.Attr
public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupFactorization
public import MMP.AlgebraicGeometry.RegularEmbedding.ConesBlowups
import MMP.AlgebraicTopology.ThomClass.Gysin
import MMP.AlgebraicTopology.ComplexVectorBundle.EulerClass
import MMP.AlgebraicTopology.ComplexProjectiveSpace.TautologicalBundle
import MMP.AlgebraicTopology.OrientationClass.Point
import MMP.AlgebraicTopology.SingularHomology.ChartSimplexLocalHomology
import MMP.AlgebraicTopology.SingularCohomology.PairSequence.Supports
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Analytic.BlowupFibre.Charts
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.AlgebraicGeometry.Analytic.SchemeManifold
import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeTopSectionsLinear
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZeroSplitting

/-!
# Integral second cohomology of a proper birational morphism of surfaces

Let `π : W ⟶ Z` be a proper birational morphism of smooth projective complex surfaces. Then the
pullback `π^* : H²(Z^an; ℤ) → H²(W^an; ℤ)` has an integral left inverse `r_π`, so `π^*` embeds
`H²(Z; ℤ)` as a direct summand of `H²(W; ℤ)` with complement `ker r_π`. Factoring `π` into
blowups at closed points `W ≅ Z_n ⟶ ⋯ ⟶ Z_0 = Z`, the complement is free with basis the total
transforms in `W` of the classes of the exceptional curves of the successive blowups.

The proof treats one blowup `b : B = Bl_y Y ⟶ Y` at a time and then inducts along the chain.

*Topology.* Let `E = b⁻¹(y)`. The long exact sequence of the pair `(Y, Y - y)` and excision to a
neighbourhood of `y` homeomorphic to an open subset of `ℂ²` give `H²(Y) ≅ H²(Y - y)`, since
`H²` and `H³` of `(ℂ², ℂ² - 0)` vanish. On the other side, `b` is a homeomorphism
`B - E ≅ Y - y`, and the kernel of `H²(B) → H²(B - E)` is the image of `H²(B, B - E)`, which by
excision is `H²` of the total space of the tautological line bundle `O(-1)` on `ℙ¹` relative to
the complement of the zero section. This group is free of rank one on the Thom class: a relative
cocycle takes one value on all fibre simplices, as any two fibre inclusions are homotopic through
maps of pairs and any two oriented simplices around `0` are locally homologous. The image of the
Thom class in `H²` of the total space is its Euler class, which has no torsion because
`H¹(ℂ² - 0) = 0`. The first Chern class `c₁(𝒪(1))` of the twisting sheaf of the blowup vanishes
off `E` and is, near `E`, minus the Euler class, by comparing transition functions.

*The local model.* Let `x₁, x₂` be local coordinates at `y` generating its ideal on an affine
open `U`, and `e` the chart they define near `y`. On the blowup chart `U_k = D₊(x_k)` the line of
a point `q` is spanned by `((x_j / x_k)(q))_j`, and `e(b q) = x_k(b q) · ((x_j / x_k)(q))_j` lies
on it. So `q ↦ (line of q, e(b q))` maps `b⁻¹(dom e)` to the tautological bundle; it is injective
since `b` is bijective off `E` and `E` is the space of lines, and it is an open embedding because
`b` is proper. In these charts `𝒪(1)` has the transition functions `x_k / x_l` and the
tautological bundle their inverses, which gives the comparison of Chern classes.

## Main results

* `MMP.Fourfold.exists_leftInverse_pullback_singularCohomology_two`: the retraction `r_π` and
  the basis of its kernel by total-transform exceptional classes.

## Implementation notes

* Cohomology is `MMP.Analytic.analyticSingularCohomology ℤ _ 2`, singular cohomology of the
  space of complex points with the analytic topology, and pullback along a morphism over `ℂ` is
  `MMP.relativeSingularCohomology.map` of its realization
  `MMP.Analytic.ComplexPoints.analyticMap`.
* For the blowup `b : Bl_y Y ⟶ Y` at a closed point `y`, the class of the exceptional curve `E`
  is taken to be `MMP.Analytic.algebraicFirstChernClass` of the twisting sheaf
  `AlgebraicGeometry.blowUpTwist _ 1`, which is the invertible ideal `𝒪(-E) = ℐ_y 𝒪_{Bl_y Y}`;
  this is `-[E]`, which spans the same subgroup. Its total transform in `W` is its pullback
  along the morphism `W ⟶ Bl_y Y` through which `π` factors.
* The basis is indexed by `Fin n`, `n` the number of blowups, and each basis vector is required
  to be the total transform of the exceptional class of one step `b : Bl_y Y ⟶ Y` of a
  factorization of `π` into point blowups: `π = g ≫ b ≫ h`, where `h : Y ⟶ Z` is a
  `Stacks.ResolutionOfSurfaces.PointBlowupChain` over `Z` and `g` satisfies
  `Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups`. Every such `π` factors into point
  blowups (`MMP.Resolution.Bridges.factorsAsPointBlowups_of_isSmoothSurface`), so no
  factorization is assumed.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.2.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §§9–12.
* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], V.3.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MMP MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.Fourfold

section Topology

open Set Bundle MMP.cohomologyWithSupports
open MMP.SingularChain MMP.SingularCochain
open MMP.ThomClass
open MMP.Topology _root_.Topology

/-- Absolute cohomology `H^j Y` with integer coefficients. -/
private abbrev H (T : TopCat.{0}) (j : ℤ) :=
  cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) T Set.univ j

/-- The pullback on absolute cohomology. -/
private abbrev pb {T T' : TopCat.{0}} (f : T' ⟶ T) (j : ℤ) : H T j ⟶ H T' j :=
  relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) f (compl_univ_subset_preimage f) j

private lemma pb_pb_apply {T T' T'' : TopCat.{0}} (g : T'' ⟶ T') (f : T' ⟶ T) (j : ℤ) (x : H T j) :
    (pb g j).hom ((pb f j).hom x) = (pb (g ≫ f) j).hom x :=
  MMP.Topology.relativeSingularCohomology_map_map_apply ℤ g f _ _ _ j x

private lemma pb_congr {T T' : TopCat.{0}} {f f' : T' ⟶ T} (h : f = f') (j : ℤ) :
    pb f j = pb f' j := by
  subst h; rfl

private lemma pb_id_apply {T : TopCat.{0}} (j : ℤ) (x : H T j) : (pb (𝟙 T) j).hom x = x :=
  congrArg (fun m ↦ m.hom x) (relativeSingularCohomology.map_id ℤ _ T _ j)

private lemma bijective_restrictCompl_of_subsingleton (Y : TopCat.{0}) (X : Set Y)
    (h2 : Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) Y X (2 : ℕ)))
    (h3 : Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) Y X (3 : ℕ))) :
    Function.Bijective (restrictCompl ℤ Y X 2).hom := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_,
    fun z ↦ (exact_restrictCompl_delta ℤ Y X 2 z).1 (Subsingleton.elim _ _)⟩
  obtain ⟨z, rfl⟩ := (exact_toCohomology_restrictCompl ℤ Y X 2 x).1 hx
  rw [Subsingleton.elim z 0, map_zero]

/-- If `b` is a homeomorphism off the fibre `b ⁻¹' {y}`, then `pb b 2` has a left inverse whose
kernel is spanned by a torsion-free class `ξ`. -/
private theorem exists_leftInverse_pb_of_isHomeomorph_compl {Y B : TopCat.{0}} (b : B ⟶ Y) (y : Y)
    (hy : IsClosed ({y} : Set Y))
    (hh : IsHomeomorph (fun p : ((b ⁻¹' {y})ᶜ : Set B) ↦
      (⟨b p, p.2⟩ : (({y} : Set Y)ᶜ : Set Y))))
    (hY2 : Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) Y {y} (2 : ℕ)))
    (hY3 : Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) Y {y} (3 : ℕ)))
    (N : Set B) (hN : IsOpen N) (hEN : b ⁻¹' {y} ⊆ N)
    (u : cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) (TopCat.of N)
      (subspaceInclusion B N ⁻¹' (b ⁻¹' {y})) (2 : ℕ))
    (hu : ∀ β, ∃ m : ℤ, β = m • u)
    (hfree : ∀ m : ℤ, m • (toCohomology ℤ (ModuleCat.of ℤ ℤ) _ _ (2 : ℕ)).hom u = 0 → m = 0)
    (ξ : H B 2) (hξE : (restrictCompl ℤ B (b ⁻¹' {y}) 2).hom ξ = 0)
    (s : ℤ) (hs : s * s = 1)
    (hξN : (pb (subspaceInclusion B N) 2).hom ξ =
      s • (toCohomology ℤ (ModuleCat.of ℤ ℤ) _ _ (2 : ℕ)).hom u) :
    ∃ r : H B 2 →ₗ[ℤ] H Y 2, (∀ x, r ((pb b 2).hom x) = x) ∧
      LinearMap.ker r = Submodule.span ℤ {ξ} ∧ ∀ m : ℤ, m • ξ = 0 → m = 0 := by
  have hE : IsClosed (b ⁻¹' {y}) := hy.preimage b.hom.continuous
  have hρ := bijective_restrictCompl_of_subsingleton Y {y} hY2 hY3
  let hc : TopCat.of ((b ⁻¹' {y})ᶜ : Set B) ⟶ TopCat.of (({y} : Set Y)ᶜ : Set Y) :=
    TopCat.ofHom ⟨_, hh.continuous⟩
  have : IsIso hc :=
    (TopCat.isoOfHomeo (X := TopCat.of ((b ⁻¹' {y})ᶜ : Set B))
      (Y := TopCat.of (({y} : Set Y)ᶜ : Set Y)) hh.homeomorph).isIso_hom
  have hcb : subspaceInclusion B (b ⁻¹' {y})ᶜ ≫ b = hc ≫ subspaceInclusion Y {y}ᶜ := rfl
  have hcbij := (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_relativeSingularCohomology_map_of_isIso ℤ hc (univ : Set _)ᶜ 2)
  let eρ := LinearEquiv.ofBijective (restrictCompl ℤ Y {y} 2).hom hρ
  let ec := LinearEquiv.ofBijective (pb hc 2).hom hcbij
  let ρB := (restrictCompl ℤ B (b ⁻¹' {y}) 2).hom
  let r : H B 2 →ₗ[ℤ] H Y 2 := eρ.symm.toLinearMap ∘ₗ ec.symm.toLinearMap ∘ₗ ρB
  have hnat : ∀ x, ρB ((pb b 2).hom x) = ec (eρ x) := by
    intro x
    change (pb (subspaceInclusion B (b ⁻¹' {y})ᶜ) 2).hom ((pb b 2).hom x) =
      (pb hc 2).hom ((pb (subspaceInclusion Y {y}ᶜ) 2).hom x)
    rw [pb_pb_apply, pb_pb_apply, pb_congr hcb]
  have hker : ∀ x, r x = 0 ↔ ρB x = 0 := by
    intro x
    simp only [r, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.map_eq_zero_iff]
  have hιiso := MMP.Topology.isIso_pullback_of_isOpenEmbedding ℤ (subspaceInclusion B N)
    hN.isOpenEmbedding_subtypeVal hE (fun p hp ↦ ⟨⟨p, hEN hp⟩, rfl⟩) (2 : ℕ)
  let eι := LinearEquiv.ofBijective _ ((ConcreteCategory.isIso_iff_bijective _).1 hιiso)
  have hnatι : ∀ β, (pb (subspaceInclusion B N) 2).hom
      ((toCohomology ℤ (ModuleCat.of ℤ ℤ) B (b ⁻¹' {y}) (2 : ℕ)).hom β) =
      (toCohomology ℤ (ModuleCat.of ℤ ℤ) _ _ (2 : ℕ)).hom (eι β) := fun β ↦
    MMP.Topology.relativeSingularCohomology_map_map_apply_eq ℤ (subspaceInclusion B N) (𝟙 B)
      (𝟙 _) (subspaceInclusion B N) (by rfl) _ _ _ _ _ β
  have hkerB : ∀ α, ρB α = 0 → ∃ m : ℤ, α = m •
      (toCohomology ℤ (ModuleCat.of ℤ ℤ) B (b ⁻¹' {y}) (2 : ℕ)).hom (eι.symm u) := by
    intro α hα
    obtain ⟨β, rfl⟩ := (exact_toCohomology_restrictCompl ℤ B (b ⁻¹' {y}) 2 α).1 hα
    obtain ⟨m, hm⟩ := hu (eι β)
    refine ⟨m, ?_⟩
    rw [← map_zsmul, ← map_zsmul, ← hm, LinearEquiv.symm_apply_apply]
  have hjNw : (pb (subspaceInclusion B N) 2).hom
      ((toCohomology ℤ (ModuleCat.of ℤ ℤ) B (b ⁻¹' {y}) (2 : ℕ)).hom (eι.symm u)) =
      (toCohomology ℤ (ModuleCat.of ℤ ℤ) _ _ (2 : ℕ)).hom u := by
    rw [hnatι, LinearEquiv.apply_symm_apply]
  obtain ⟨m₀, hm₀⟩ := hkerB ξ hξE
  have hm₀s : m₀ = s := by
    have h1 := congrArg (pb (subspaceInclusion B N) 2).hom hm₀
    rw [map_zsmul, hjNw, hξN] at h1
    have h2 : (s - m₀) • (toCohomology ℤ (ModuleCat.of ℤ ℤ) _ _ (2 : ℕ)).hom u = 0 := by
      rw [sub_zsmul, h1, add_neg_cancel]
    have := hfree _ h2
    omega
  subst hm₀s
  refine ⟨r, fun x ↦ ?_, ?_, ?_⟩
  · simp only [r, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hnat, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  · apply le_antisymm
    · intro α hα
      rw [LinearMap.mem_ker, hker] at hα
      obtain ⟨m, hm⟩ := hkerB α hα
      have hX : (toCohomology ℤ (ModuleCat.of ℤ ℤ) B (b ⁻¹' {y}) (2 : ℕ)).hom (eι.symm u) =
          m₀ • ξ := by
        rw [hm₀, ← mul_zsmul, hs, one_zsmul]
      rw [hm, hX]
      exact zsmul_mem (zsmul_mem (Submodule.mem_span_singleton_self ξ) m₀) m
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact (hker ξ).2 hξE
  · intro m hm
    have h1 := congrArg (pb (subspaceInclusion B N) 2).hom hm
    rw [map_zsmul, hξN, map_zero, ← mul_zsmul] at h1
    have := hfree _ h1
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hs with h | h <;> subst h <;> omega

/-- A relative cohomology group vanishes in degree `k` when the relative homology vanishes in all
degrees `≤ k`. -/
private lemma subsingleton_relCohomology_of_vanishing {Y : Type} [TopologicalSpace Y] (A : Set Y)
    (k : ℕ) (hvan : ∀ j ≤ k, RelHomologyVanishing ℤ univ A j) :
    Subsingleton (relCohomology ℤ A k) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  refine mem_relCoboundaries_of_relHomologyVanishing (fun j hj ↦ hvan j hj.le) fun c hc ↦ ?_
  obtain ⟨w, -, hw⟩ := hvan k le_rfl c (mem_inside_univ c) hc
  rw [univ_inter] at hw
  have h1 := eval_eq_zero_of_mem_vanishing φ.2.1 hw
  have h2 : eval (φ : Simplex Y k → ℤ) (bd ℤ k w) = 0 := by
    rw [← eval_coboundary, show coboundary ℤ k (φ : Simplex Y k → ℤ) = 0 from φ.2.2]
    simp
  rwa [map_sub, h2, sub_zero] at h1

/-- `H_j(ℝⁿ, ℝⁿ - 0; ℤ) = 0` for `j < n`. -/
private lemma relHomologyVanishing_euclidean {n j : ℕ} (hj : j < n) :
    RelHomologyVanishing ℤ univ ({0}ᶜ : Set (Fin n → ℝ)) j := by
  intro c _ hc
  rcases j with _ | i
  · obtain ⟨w, hw⟩ := isRelBoundary_singleton_zero_zero (R := ℤ) (by omega) c
    exact ⟨w, mem_inside_univ _, by rwa [univ_inter]⟩
  · obtain ⟨w, hw⟩ := relVanishing_singleton_zero_low (R := ℤ) n i hj c hc
    exact ⟨w, mem_inside_univ _, by rwa [univ_inter]⟩

/-- `H^k(ℝⁿ, ℝⁿ - 0; ℤ) = 0` for `k < n`. -/
private lemma subsingleton_cohomologyWithSupports_euclidean {n k : ℕ} (hk : k < n) :
    Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) (TopCat.of (Fin n → ℝ)) {0} k) :=
  (relativeSingularCohomologyEquiv ℤ (Y := TopCat.of (Fin n → ℝ))
    ({0}ᶜ : Set (Fin n → ℝ)) k).toEquiv.subsingleton_congr.2
    (subsingleton_relCohomology_of_vanishing _ k fun j hj ↦
      relHomologyVanishing_euclidean (by omega))

/-- Homeomorphism invariance of relative cohomology. -/
private lemma subsingleton_of_iso {Y' Y : TopCat.{0}} (e : Y' ≅ Y) {A : Set Y} {A' : Set Y'}
    (hA : e.hom ⁻¹' A = A') (j : ℤ)
    (h : Subsingleton (relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ) Y A j)) :
    Subsingleton (relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ) Y' A' j) := by
  subst hA
  have := MMP.Topology.isIso_relativeSingularCohomology_map_of_isIso ℤ e.hom A j
  exact (asIso (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) e.hom
    (A' := e.hom ⁻¹' A) Subset.rfl j)).toLinearEquiv.toEquiv.subsingleton_congr.1 h

/-- `H^k(ℂ², ℂ² - 0; ℤ) = 0` for `k < 4`. -/
private lemma subsingleton_cohomologyWithSupports_complexPlane {k : ℕ} (hk : k < 4) :
    Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) (TopCat.of (Fin 2 → ℂ)) {0} k) := by
  have hrank : Module.finrank ℝ (Fin 2 → ℂ) = Module.finrank ℝ (Fin 4 → ℝ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  let h : (Fin 2 → ℂ) ≃L[ℝ] (Fin 4 → ℝ) := ContinuousLinearEquiv.ofFinrankEq hrank
  let e : TopCat.of (Fin 2 → ℂ) ≅ TopCat.of (Fin 4 → ℝ) := TopCat.isoOfHomeo h.toHomeomorph
  refine subsingleton_of_iso e ?_ _ (subsingleton_cohomologyWithSupports_euclidean hk)
  ext w
  change h w ∈ ({0} : Set (Fin 4 → ℝ))ᶜ ↔ w ∈ ({0} : Set (Fin 2 → ℂ))ᶜ
  simp [h.map_eq_zero_iff]

/-- The integral cohomology of a point vanishes in degree one. -/
private lemma subsingleton_cohomology_one_of_unique (Y : TopCat.{0}) [Unique Y] :
    Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) Y Set.univ (1 : ℕ)) := by
  refine (relativeSingularCohomologyEquiv ℤ (Set.univ : Set Y)ᶜ 1).toEquiv.subsingleton_congr.2 ?_
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  have hσ : ∀ {n : ℕ} (σ τ : Simplex Y n), σ = τ := fun σ τ ↦
    ContinuousMap.ext fun t ↦ Subsingleton.elim _ _
  have hφ : (φ : Simplex Y 1 → ℤ) = 0 := by
    ext σ
    have h := congrFun (show coboundary ℤ 1 (φ : Simplex Y 1 → ℤ) = 0 from φ.2.2)
      (ContinuousMap.const _ default)
    rw [coboundary_apply, Fin.sum_univ_three] at h
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_mul, neg_one_mul,
      Pi.zero_apply] at h
    rw [hσ (ContinuousMap.comp _ _) σ, hσ (ContinuousMap.comp _ _) σ,
      hσ (ContinuousMap.comp _ _) σ] at h
    simp only [Pi.zero_apply]
    linarith
  change (φ : Simplex Y 1 → ℤ) ∈ relCoboundaries ℤ _ 1
  rw [hφ]
  exact Submodule.zero_mem _

/-- `H¹(ℂ²; ℤ) = 0`: `ℂ²` is contractible. -/
private lemma subsingleton_cohomology_one_complexPlane :
    Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) (TopCat.of (Fin 2 → ℂ)) Set.univ
      (1 : ℕ)) := by
  let Z : TopCat.{0} := TopCat.of PUnit
  have : Unique Z := inferInstanceAs (Unique PUnit)
  let i : Z ⟶ TopCat.of (Fin 2 → ℂ) := TopCat.ofHom (ContinuousMap.const _ 0)
  let r : TopCat.of (Fin 2 → ℂ) ⟶ Z := TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let H : TopCat.Homotopy (r ≫ i) (𝟙 _) :=
    { toFun := fun q ↦ ((q.1 : ℝ) : ℂ) • q.2
      continuous_toFun := by fun_prop
      map_zero_left := fun w ↦ by
        change ((0 : ℝ) : ℂ) • w = 0
        rw [Complex.ofReal_zero, zero_smul]
      map_one_left := fun w ↦ by
        change ((1 : ℝ) : ℂ) • w = w
        rw [Complex.ofReal_one, one_smul] }
  have hpt := subsingleton_cohomology_one_of_unique Z
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have key : (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) (r ≫ i)
      (MMP.Topology.compl_univ_subset_preimage (r ≫ i)) (1 : ℕ)).hom x = x := by
    rw [relativeSingularCohomology.map_eq_of_homotopy ℤ H
      (fun y hy ↦ absurd (Set.mem_univ y) hy) _ (MMP.Topology.compl_univ_subset_preimage _)]
    exact congrArg (fun m ↦ m.hom x) (relativeSingularCohomology.map_id ℤ _ _ _ _)
  rw [← key, ← MMP.Topology.relativeSingularCohomology_map_map_apply ℤ r i
    (MMP.Topology.compl_univ_subset_preimage r) (MMP.Topology.compl_univ_subset_preimage i)]
  rw [Subsingleton.elim ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) i
    (MMP.Topology.compl_univ_subset_preimage i) (1 : ℕ)).hom x) 0, map_zero]

/-- `H¹(ℂ² - 0; ℤ) = 0`. -/
private lemma subsingleton_cohomology_one_complexPlane_compl :
    Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ)
      (TopCat.of ↥({0} : Set (TopCat.of (Fin 2 → ℂ)))ᶜ) univ (1 : ℕ)) := by
  have := subsingleton_cohomology_one_complexPlane
  have := subsingleton_cohomologyWithSupports_complexPlane (k := 1 + 1) (by norm_num)
  refine subsingleton_of_forall_eq 0 fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (exact_restrictCompl_delta ℤ (TopCat.of (Fin 2 → ℂ)) {0} 1 y).1
    (Subsingleton.elim _ _)
  rw [Subsingleton.elim x 0, map_zero]

/-- The total space of the tautological line bundle on `ℙ¹(ℂ)`. -/
private abbrev TE := TotalSpace ℂ (TautologicalBundle 1)

/-- The point of the tautological bundle with vector `c • w`, over the line of `w ≠ 0`. -/
private def fibPt (w : ↥({0} : Set (Fin 2 → ℂ))ᶜ) (c : ℂ) : TE :=
  ⟨lineOf (ne_zero_of_mem_compl w), c * w.1 (chartIndex (lineOf (ne_zero_of_mem_compl w)))⟩

private lemma localTriv_fibPt (j : Fin 2) (w : ↥({0} : Set (Fin 2 → ℂ))ᶜ) (c : ℂ) :
    ((tautologicalCore 1).localTriv j (fibPt w c)).2 = c * w.1 j := by
  rw [localTriv_snd_tautological]
  change lineProjection w.1 j (chartIndex (lineOf (ne_zero_of_mem_compl w))) /
      lineProjection w.1 (chartIndex (lineOf (ne_zero_of_mem_compl w)))
        (chartIndex (lineOf (ne_zero_of_mem_compl w))) *
      (c * w.1 (chartIndex (lineOf (ne_zero_of_mem_compl w)))) = c * w.1 j
  rw [← apply_chartIndex_mul_ratio (ne_zero_of_mem_compl w) j]
  ring

private lemma continuous_fibPt :
    Continuous fun q : ↥({0} : Set (Fin 2 → ℂ))ᶜ × ℂ ↦ fibPt q.1 q.2 := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨((continuous_lineProjection_comp (continuous_subtype_val.comp continuous_fst)
    fun q ↦ ne_zero_of_mem_compl q.1).subtype_mk _).continuousAt, ?_⟩
  change ContinuousAt (fun q : ↥({0} : Set (Fin 2 → ℂ))ᶜ × ℂ ↦ ((tautologicalCore 1).localTriv
    (chartIndex (lineOf (ne_zero_of_mem_compl q₀.1))) (fibPt q.1 q.2)).2) q₀
  simp_rw [localTriv_fibPt]
  exact (continuous_snd.mul ((continuous_apply _).comp
    (continuous_subtype_val.comp continuous_fst))).continuousAt

private lemma fibPt_mem_range_iff (w : ↥({0} : Set (Fin 2 → ℂ))ᶜ) (c : ℂ) :
    fibPt w c ∈ range (zeroSection ℂ (TautologicalBundle 1)) ↔ c = 0 := by
  rw [mem_range_zeroSection_tautological_iff]
  change c * _ = 0 ↔ _
  simp [apply_chartIndex_ne_zero (ne_zero_of_mem_compl w)]

private lemma isClosed_range_zeroSection_tautologicalBundle :
    IsClosed (range (zeroSection ℂ (TautologicalBundle 1))) := by
  have : range (zeroSection ℂ (TautologicalBundle 1)) = tautologicalVector 1 ⁻¹' {0} := by
    ext p
    refine ⟨fun hp ↦ funext fun k ↦ ?_, fun hp ↦ of_not_not fun h ↦ tautologicalVector_ne_zero h hp⟩
    change fibreCoord p * _ = 0
    rw [(mem_range_zeroSection_tautological_iff p).1 hp, zero_mul]
  rw [this]
  exact isClosed_singleton.preimage continuous_tautologicalVector

/-- Every complex frame of a fibre of the tautological bundle is `z ↦ fibPt w (z 0)`. -/
private lemma exists_eq_fibPt {r : ℕ} (hr : r = 1) (x : lineProjections 1)
    (ψ : (Fin r → ℂ) ≃L[ℂ] TautologicalBundle 1 x) :
    ∃ w : ↥({0} : Set (Fin 2 → ℂ))ᶜ, ∀ z : Fin r → ℂ,
      (TotalSpace.mk x (ψ z) : TE) = fibPt w (z ⟨0, by omega⟩) := by
  subst hr
  let one : Fin 1 → ℂ := fun _ ↦ 1
  let p₁ : TE := TotalSpace.mk x (ψ one)
  have hone : one ≠ 0 := fun h ↦ by simpa [one] using congrFun h 0
  have hp₁ : p₁ ∉ range (zeroSection ℂ (TautologicalBundle 1)) := by
    rw [mem_range_zeroSection_tautological_iff]
    exact fun h ↦ hone (ψ.injective (h.trans (map_zero ψ).symm))
  refine ⟨⟨tautologicalVector 1 p₁, tautologicalVector_ne_zero hp₁⟩, fun z ↦ ?_⟩
  have h := tautologicalPoint_tautologicalVector p₁ hp₁
  have hcoord := congrArg fibreCoord h
  have key : ∀ (Q P : lineProjections 1) (a b : ℂ), Q = P → a = b →
      (⟨Q, a⟩ : TE) = ⟨P, b⟩ := by
    rintro _ _ _ _ rfl rfl
    rfl
  refine key _ _ _ _ (congrArg TotalSpace.proj h).symm ?_
  have hψ : ψ z = z 0 • ψ one := by
    conv_lhs => rw [show z = z 0 • one from funext fun i ↦ by
      rw [Subsingleton.elim i 0]; simp [one]]
    exact map_smul ψ _ _
  rw [hψ]
  exact congrArg (fun t : ℂ ↦ z 0 * t) hcoord.symm

/-- The fibre inclusion `z ↦ fibPt w (z 0)`. -/
private def gmap {r : ℕ} (hr : r = 1) (w : ↥({0} : Set (Fin 2 → ℂ))ᶜ) :
    TopCat.of (Fin r → ℂ) ⟶ TopCat.of TE :=
  TopCat.ofHom ⟨fun z ↦ fibPt w (z ⟨0, by omega⟩),
    continuous_fibPt.comp (continuous_const.prodMk (continuous_apply _))⟩

private lemma compl_subset_preimage_gmap {r : ℕ} (hr : r = 1) (w : ↥({0} : Set (Fin 2 → ℂ))ᶜ) :
    ({0}ᶜ : Set (Fin r → ℂ)) ⊆ gmap hr w ⁻¹' (range (zeroSection ℂ (TautologicalBundle 1)))ᶜ := by
  intro z hz h
  change fibPt w _ ∈ _ at h
  rw [fibPt_mem_range_iff] at h
  subst hr
  exact hz (funext fun i ↦ by rw [Subsingleton.elim i 0]; exact h)

private lemma one_lt_rank_complexPlane : 1 < Module.rank ℝ (Fin 2 → ℂ) := by
  have h : Module.finrank ℝ (Fin 2 → ℂ) = 4 := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  rw [← Module.finrank_eq_rank, h]
  norm_num

/-- Any two fibre inclusions induce the same map on relative cohomology. -/
private lemma map_gmap_eq {r : ℕ} (hr : r = 1) (w₁ w₂ : ↥({0} : Set (Fin 2 → ℂ))ᶜ) (k : ℤ) :
    relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) (gmap hr w₁)
        (compl_subset_preimage_gmap hr w₁) k =
      relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) (gmap hr w₂)
        (compl_subset_preimage_gmap hr w₂) k := by
  obtain ⟨γ, hγ⟩ := (isPathConnected_compl_singleton_of_one_lt_rank one_lt_rank_complexPlane
    (0 : Fin 2 → ℂ)).joinedIn w₁.1 w₁.2 w₂.1 w₂.2
  let H : TopCat.Homotopy (gmap hr w₁) (gmap hr w₂) :=
    { toFun := fun q ↦ fibPt ⟨γ q.1, hγ q.1⟩ (q.2 ⟨0, by omega⟩)
      continuous_toFun := continuous_fibPt.comp
        (((γ.continuous.comp continuous_fst).subtype_mk _).prodMk
          ((continuous_apply _).comp continuous_snd))
      map_zero_left := fun z ↦ by
        change fibPt _ _ = fibPt _ _
        congr 1
        exact Subtype.ext γ.source
      map_one_left := fun z ↦ by
        change fibPt _ _ = fibPt _ _
        congr 1
        exact Subtype.ext γ.target }
  exact relativeSingularCohomology.map_eq_of_homotopy ℤ H
    (fun z hz t ↦ compl_subset_preimage_gmap hr ⟨γ t, hγ t⟩ hz) _ _ k

/-- **A relative cocycle of the tautological bundle takes one value on all fibre simplices.** -/
private lemma eval_fibreSimplex_eq {r : ℕ} (hr : r = 1) {φ : Simplex (TopCat.of TE) (2 * r) → ℤ}
    (hφ : φ ∈ relCocycles ℤ (range (zeroSection ℂ (TautologicalBundle 1)))ᶜ (2 * r))
    {x₁ x₂ : lineProjections 1} (ψ₁ : (Fin r → ℂ) ≃L[ℂ] TautologicalBundle 1 x₁)
    (ψ₂ : (Fin r → ℂ) ≃L[ℂ] TautologicalBundle 1 x₂) {v₁ v₂ : Fin (2 * r + 1) → (Fin r → ℂ)}
    (hv₁ : IsOrientedSimplexAroundZero (complexOrientationBasis r) v₁)
    (hv₂ : IsOrientedSimplexAroundZero (complexOrientationBasis r) v₂) :
    φ (fibreSimplex ℂ x₁ ψ₁ v₁) = φ (fibreSimplex ℂ x₂ ψ₂ v₂) := by
  obtain ⟨w₁, hw₁⟩ := exists_eq_fibPt hr x₁ ψ₁
  obtain ⟨w₂, hw₂⟩ := exists_eq_fibPt hr x₂ ψ₂
  have hσ₁ : fibreSimplex ℂ x₁ ψ₁ v₁ = (gmap hr w₁).hom.comp (affineSimplex v₁) :=
    ContinuousMap.ext fun t ↦ hw₁ _
  have hσ₂ : fibreSimplex ℂ x₂ ψ₂ v₂ = (gmap hr w₂).hom.comp (affineSimplex v₂) :=
    ContinuousMap.ext fun t ↦ hw₂ _
  rw [hσ₁, hσ₂]
  have hrel : ∀ w, cochainPullback ℤ (gmap hr w) (2 * r) φ ∈
      relCocycles ℤ ({0}ᶜ : Set (Fin r → ℂ)) (2 * r) := fun w ↦
    cochainPullback_mem_relCocycles (gmap hr w) (compl_subset_preimage_gmap hr w) hφ
  have hA : cochainPullback ℤ (gmap hr w₁) (2 * r) φ (affineSimplex v₁) =
      cochainPullback ℤ (gmap hr w₁) (2 * r) φ (affineSimplex v₂) := by
    have hloc := FundamentalClass.isLocallyHomologous_of_isOrientedSimplexAroundZero
      (OpenPartialHomeomorph.refl (Fin r → ℂ)) (x := 0) (mem_univ _)
      (v := v₁) (w := v₂) (by simpa using hv₁) (subset_univ _) (by simpa using hv₂)
      (subset_univ _) (σ₀ := affineSimplex v₁) (σ₁ := affineSimplex v₂)
      (fun _ ↦ rfl) (fun _ ↦ rfl)
    simpa [Finsupp.linearCombination_single] using eval_eq_of_isLocallyHomologous (hrel w₁) hloc
  have hB : cochainPullback ℤ (gmap hr w₁) (2 * r) φ (affineSimplex v₂) =
      cochainPullback ℤ (gmap hr w₂) (2 * r) φ (affineSimplex v₂) := by
    let c : relCocycles ℤ (range (zeroSection ℂ (TautologicalBundle 1)))ᶜ (2 * r) := ⟨φ, hφ⟩
    obtain ⟨x, hx⟩ := (relativeSingularCohomologyEquiv ℤ (Y := TopCat.of TE)
      (range (zeroSection ℂ (TautologicalBundle 1)))ᶜ (2 * r)).surjective
        (Submodule.Quotient.mk c)
    have e1 := relativeSingularCohomologyEquiv_map (gmap hr w₁)
      (compl_subset_preimage_gmap hr w₁) (2 * r) x
    have e2 := relativeSingularCohomologyEquiv_map (gmap hr w₂)
      (compl_subset_preimage_gmap hr w₂) (2 * r) x
    rw [map_gmap_eq hr w₁ w₂ ((2 * r : ℕ) : ℤ)] at e1
    rw [e1, hx, relCohomologyMap_mk, relCohomologyMap_mk] at e2
    have h := (Submodule.Quotient.eq _).1 e2.symm
    have h0 := eval_single_eq_zero_of_mem_relCoboundaries (affineSimplex v₂)
      (fun t ht ↦ hv₂.affineSimplex_ne_zero t ht) _ h
    simp only [Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      Finsupp.linearCombination_single, one_smul, Pi.sub_apply] at h0
    exact (sub_eq_zero.1 h0).symm
  exact hA.trans hB

/-- A reference fibre simplex of the tautological bundle. -/
private lemma exists_fibreSimplex :
    ∃ (x : lineProjections 1) (ψ : (Fin (Module.finrank ℂ ℂ) → ℂ) ≃L[ℂ] TautologicalBundle 1 x)
      (v : Fin (2 * Module.finrank ℂ ℂ + 1) → (Fin (Module.finrank ℂ ℂ) → ℂ)),
      IsOrientedSimplexAroundZero (complexOrientationBasis (Module.finrank ℂ ℂ)) v := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (lineProjections 1))
  let ψ₀ : TautologicalBundle 1 x ≃L[ℂ] ℂ :=
    (trivializationAt ℂ (TautologicalBundle 1) x).continuousLinearEquivAt ℂ x
      (mem_baseSet_trivializationAt ℂ (TautologicalBundle 1) x)
  let φ : (Fin (Module.finrank ℂ ℂ) → ℂ) ≃L[ℂ] ℂ :=
    (LinearEquiv.ofFinrankEq _ _ (by simp)).toContinuousLinearEquiv
  obtain ⟨v, hv⟩ := exists_isOrientedSimplexAroundZero
    (complexOrientationBasis (Module.finrank ℂ ℂ))
  exact ⟨x, φ.trans ψ₀.symm, v, hv⟩

/-- **`H²(E, E - 0; ℤ)` is generated by the Thom class**, for the tautological bundle. -/
private theorem exists_eq_zsmul_thomClass
    (β : cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) (TopCat.of TE)
      (range (zeroSection ℂ (TautologicalBundle 1))) (2 * Module.finrank ℂ ℂ : ℕ)) :
    ∃ m : ℤ, β = m • thomClass ℤ ℂ (TautologicalBundle 1) := by
  obtain ⟨⟨φ, hφ⟩, hx⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv ℤ (Y := TopCat.of TE)
      (range (zeroSection ℂ (TautologicalBundle 1)))ᶜ (2 * Module.finrank ℂ ℂ) β)
  obtain ⟨x₀, ψ₀, v₀, hv₀⟩ := exists_fibreSimplex
  set m := φ (fibreSimplex ℂ x₀ ψ₀ v₀)
  set u := thomClass ℤ ℂ (TautologicalBundle 1)
  have hβ' : IsThomClass ℂ (TautologicalBundle 1) (β - m • u + u) := by
    intro x ψ v hv
    have hu := isThomClass_thomClass (R := ℤ) ℂ (TautologicalBundle 1) x ψ v hv
    rw [map_add, map_sub, map_zsmul, map_add, map_sub, map_zsmul, hu, ← hx, relEval_mk]
    simp only [Finsupp.linearCombination_single, one_smul]
    rw [eval_fibreSimplex_eq (Module.finrank_self ℂ) hφ ψ ψ₀ hv hv₀]
    simp [m]
  refine ⟨m, ?_⟩
  have := eq_thomClass ℂ (TautologicalBundle 1) hβ'
  rwa [add_eq_right, sub_eq_zero] at this

/-- Evaluation of a multiple of the Thom class on a fibre simplex. -/
private lemma zsmul_thomClass_eq_zero {m : ℤ} (h : m • thomClass ℤ ℂ (TautologicalBundle 1) = 0) :
    m = 0 := by
  obtain ⟨x₀, ψ₀, v₀, hv₀⟩ := exists_fibreSimplex
  have hu := isThomClass_thomClass (R := ℤ) ℂ (TautologicalBundle 1) x₀ ψ₀ v₀ hv₀
  have h1 := congrArg (fun z ↦ relEval (R := ℤ) (Finsupp.single (fibreSimplex ℂ x₀ ψ₀ v₀) 1)
    (eval_single_eq_zero_of_mem_relCoboundaries _
      (fibreSimplex_notMem_range_zeroSection ℂ x₀ ψ₀ hv₀))
    (relativeSingularCohomologyEquiv ℤ (Y := TopCat.of TE) _ _ z)) h
  simpa only [map_zsmul, hu, map_zero, smul_eq_mul, mul_one] using h1

/-! ### The local inputs, transported along the local models -/

/-- **The point side.** If a neighbourhood of a closed point `y` openly embeds in `ℂ²` with `y`
going to `0`, then `H^k(Y, Y - y; ℤ) = 0` for `k < 4`. -/
private lemma subsingleton_cohomologyWithSupports_of_isOpenEmbedding {Y : TopCat.{0}} (y : Y)
    (hy : IsClosed ({y} : Set Y)) (V : Set Y) (hV : IsOpen V) (hyV : y ∈ V)
    (φ : TopCat.of V ⟶ TopCat.of (Fin 2 → ℂ)) (hφ : IsOpenEmbedding φ) (hφy : φ ⟨y, hyV⟩ = 0)
    {k : ℕ} (hk : k < 4) :
    Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) Y {y} k) := by
  have h1 := isIso_pullback_subspaceInclusion ℤ hV hy (singleton_subset_iff.2 hyV) (k : ℤ)
  have h2 := isIso_pullback_of_isOpenEmbedding ℤ φ hφ (isClosed_singleton (x := 0))
    (by rintro _ rfl; exact ⟨_, hφy⟩) (k : ℤ)
  have hset : φ ⁻¹' ({0} : Set (Fin 2 → ℂ)) = subspaceInclusion Y V ⁻¹' {y} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
    · obtain rfl := hφ.injective (hz.trans hφy.symm)
      rfl
    · rw [show z = ⟨y, hyV⟩ from Subtype.ext hz, hφy]
  have h0 := subsingleton_cohomologyWithSupports_complexPlane hk
  have h3 := (asIso (pullback ℤ (ModuleCat.of ℤ ℤ) φ {0}
    (k : ℤ))).toLinearEquiv.toEquiv.subsingleton_congr.1 h0
  rw [hset] at h3
  exact (asIso (pullback ℤ (ModuleCat.of ℤ ℤ) (subspaceInclusion Y V) {y}
    (k : ℤ))).toLinearEquiv.toEquiv.subsingleton_congr.2 h3

private lemma two_mul_finrank_complex : ((2 * Module.finrank ℂ ℂ : ℕ) : ℤ) = ((2 : ℕ) : ℤ) := by
  simp

/-- The Thom class of the tautological bundle, in degree `2`. -/
private def thomTwo : cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) (TopCat.of TE)
    (range (zeroSection ℂ (TautologicalBundle 1))) (2 : ℕ) :=
  congrIndex ℤ (TopCat.of TE) rfl two_mul_finrank_complex (thomClass ℤ ℂ (TautologicalBundle 1))

/-- Its image `e ∈ H²(E)`. -/
private def thomTwoAbs : H (TopCat.of TE) 2 :=
  (toCohomology ℤ (ModuleCat.of ℤ ℤ) (TopCat.of TE) _ (2 : ℕ)).hom thomTwo

private lemma toCohomology_congrIndex {T : TopCat.{0}} {S S' : Set T} (hS : S = S') (k : ℕ)
    (x : cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) T S k) :
    (toCohomology ℤ (ModuleCat.of ℤ ℤ) T S' k).hom (congrIndex ℤ T (congrArg compl hS) rfl x) =
      (toCohomology ℤ (ModuleCat.of ℤ ℤ) T S k).hom x := by
  subst hS
  rfl

/-- The zero section is a homotopy inverse of the projection of the tautological bundle. -/
private lemma pb_bundleProj_pb_bundleZeroSection (x : H (TopCat.of TE) 2) :
    (pb (bundleProj ℂ (TautologicalBundle 1)) 2).hom
      ((pb (bundleZeroSection ℂ (TautologicalBundle 1)) 2).hom x) = x := by
  rw [pb_pb_apply, show pb (bundleProj ℂ (TautologicalBundle 1) ≫
      bundleZeroSection ℂ (TautologicalBundle 1)) 2 = pb (𝟙 _) 2 from
    relativeSingularCohomology.map_eq_of_homotopy ℤ (zeroSectionHomotopy (TautologicalBundle 1))
      (fun y hy ↦ absurd (Set.mem_univ y) hy) (compl_univ_subset_preimage _)
      (compl_univ_subset_preimage _) (2 : ℤ)]
  exact pb_id_apply 2 x

private lemma subsingleton_cohomology_one_compl_zeroSection :
    Subsingleton (cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ)
      (TopCat.of ↥(range (zeroSection ℂ (TautologicalBundle 1)))ᶜ) univ (1 : ℕ)) := by
  let e : TopCat.of ↥(range (zeroSection ℂ (TautologicalBundle 1)))ᶜ ≅
      TopCat.of ↥({0} : Set (TopCat.of (Fin 2 → ℂ)))ᶜ :=
    TopCat.isoOfHomeo (X := TopCat.of ↥(range (zeroSection ℂ (TautologicalBundle 1)))ᶜ)
      (Y := TopCat.of ↥({0} : Set (TopCat.of (Fin 2 → ℂ)))ᶜ) (tautologicalComplHomeomorph 1)
  exact subsingleton_of_iso e (by ext; simp) _ subsingleton_cohomology_one_complexPlane_compl

/-- `e` has no torsion. -/
private lemma zsmul_thomTwoAbs_eq_zero {m : ℤ} (h : m • thomTwoAbs = 0) : m = 0 := by
  have := subsingleton_cohomology_one_compl_zeroSection
  rw [thomTwoAbs, ← map_zsmul] at h
  obtain ⟨c, hc⟩ := (exact_delta_toCohomology ℤ (TopCat.of TE)
    (range (zeroSection ℂ (TautologicalBundle 1))) 1 (m • thomTwo)).1 h
  rw [Subsingleton.elim c 0, map_zero] at hc
  apply zsmul_thomClass_eq_zero
  have h2 := congrArg (congrIndex ℤ (TopCat.of TE) rfl two_mul_finrank_complex).symm hc
  rw [map_zero, thomTwo, map_zsmul, LinearEquiv.symm_apply_apply] at h2
  exact h2.symm

/-- **The exceptional side.** If a neighbourhood `N` of a closed set `E` openly embeds in the
tautological bundle, with `E` going onto the zero section, then `H²(N, N - E; ℤ)` is free of rank
one on a class whose image in `H²(N)` is the pull-back of `e` and has no torsion. -/
private lemma exists_generator_of_isOpenEmbedding {B : TopCat.{0}} (N Eset : Set B)
    (Ψ : TopCat.of N ⟶ TopCat.of TE) (hΨ : IsOpenEmbedding Ψ)
    (hΨE : Ψ ⁻¹' range (zeroSection ℂ (TautologicalBundle 1)) = subspaceInclusion B N ⁻¹' Eset)
    (hrange : range (zeroSection ℂ (TautologicalBundle 1)) ⊆ range Ψ) :
    ∃ u : cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) (TopCat.of N)
      (subspaceInclusion B N ⁻¹' Eset) (2 : ℕ),
      (∀ β, ∃ m : ℤ, β = m • u) ∧
      (toCohomology ℤ (ModuleCat.of ℤ ℤ) _ _ (2 : ℕ)).hom u = (pb Ψ 2).hom thomTwoAbs ∧
      (∀ m : ℤ, m • (toCohomology ℤ (ModuleCat.of ℤ ℤ) _ _ (2 : ℕ)).hom u = 0 → m = 0) := by
  have hiso := isIso_pullback_of_isOpenEmbedding ℤ Ψ hΨ
    isClosed_range_zeroSection_tautologicalBundle hrange
    ((2 : ℕ) : ℤ)
  let P := pullback ℤ (ModuleCat.of ℤ ℤ) Ψ (range (zeroSection ℂ (TautologicalBundle 1)))
    ((2 : ℕ) : ℤ)
  let cS := congrIndex ℤ (TopCat.of N) (congrArg compl hΨE) (rfl : ((2 : ℕ) : ℤ) = _)
  have hnat : (toCohomology ℤ (ModuleCat.of ℤ ℤ) _ _ (2 : ℕ)).hom (cS (P.hom thomTwo)) =
      (pb Ψ 2).hom thomTwoAbs := by
    rw [toCohomology_congrIndex hΨE, thomTwoAbs]
    exact MMP.Topology.relativeSingularCohomology_map_map_apply_eq ℤ (𝟙 _) Ψ Ψ (𝟙 _)
      (by simp) _ _ _ _ _ thomTwo
  refine ⟨cS (P.hom thomTwo), fun β ↦ ?_, hnat, fun m hm ↦ ?_⟩
  · obtain ⟨δ, hδ⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 hiso).2 (cS.symm β)
    obtain ⟨m, hm⟩ := exists_eq_zsmul_thomClass
      ((congrIndex ℤ (TopCat.of TE) rfl two_mul_finrank_complex).symm δ)
    refine ⟨m, ?_⟩
    have hδ' : δ = m • thomTwo := by
      rw [thomTwo, ← map_zsmul, ← hm, LinearEquiv.apply_symm_apply]
    rw [← map_zsmul, ← map_zsmul, ← hδ', hδ, LinearEquiv.apply_symm_apply]
  · rw [hnat] at hm
    let z' : TopCat.of (lineProjections 1) ⟶ TopCat.of N :=
      TopCat.ofHom ⟨fun b ↦ hΨ.isEmbedding.toHomeomorph.symm
        ⟨zeroSection ℂ (TautologicalBundle 1) b, hrange (mem_range_self b)⟩,
        hΨ.isEmbedding.toHomeomorph.symm.continuous.comp
          ((Trivialization.continuous_zeroSection ℂ).subtype_mk _)⟩
    have hz' : z' ≫ Ψ = bundleZeroSection ℂ (TautologicalBundle 1) := by
      refine ConcreteCategory.hom_ext _ _ fun b ↦ ?_
      change Ψ (hΨ.isEmbedding.toHomeomorph.symm _) = _
      exact congrArg Subtype.val (hΨ.isEmbedding.toHomeomorph.apply_symm_apply _)
    have h1 := congrArg (pb z' 2).hom hm
    rw [map_zsmul, pb_pb_apply, pb_congr hz', map_zero, ← map_zsmul] at h1
    exact zsmul_thomTwoAbs_eq_zero
      (Function.LeftInverse.injective pb_bundleProj_pb_bundleZeroSection
        (h1.trans (map_zero _).symm))

end Topology

section Chern

open Set Bundle FiberBundle Complex MMP.Analytic.ComplexLineBundle
open MMP.cohomologyWithSupports MMP.SingularChain
open MMP.SingularCochain

variable {B : Type} [TopologicalSpace B]

private theorem mem_vanishing_compl_univ {n : ℕ} (φ : Simplex B n → ℤ) :
    φ ∈ vanishing ℤ n (Set.univᶜ : Set (TopCat.of B)) :=
  fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp)

private theorem mem_relCocycles_of_coboundary_eq_zero {B'' : Type} [TopologicalSpace B'']
    {n : ℕ} {φ : Simplex B'' n → ℤ} (h : coboundary ℤ n φ = 0) :
    φ ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B'')) n :=
  Submodule.mem_inf.2 ⟨mem_vanishing_compl_univ φ, LinearMap.mem_ker.2 h⟩

/-- Cocycles differing by a coboundary have the same class. -/
private theorem ofCocycle_eq_of_sub_eq_coboundary {φ φ' : Simplex B 2 → ℤ}
    (hφ : φ ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2)
    (hφ' : φ' ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2) (m : Simplex B 1 → ℤ)
    (h : φ - φ' = coboundary ℤ 1 m) :
    cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 φ hφ =
      cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 φ' hφ' := by
  unfold cohomologyWithSupports.ofCocycle
  congr 1
  refine (Submodule.Quotient.eq _).2 ?_
  change φ - φ' ∈ relCoboundaries ℤ (Set.univᶜ : Set (TopCat.of B)) (1 + 1)
  rw [h]
  exact ⟨m, mem_vanishing_compl_univ m, rfl⟩

private theorem ofCocycle_add {φ φ' : Simplex B 2 → ℤ}
    (hφ : φ ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2)
    (hφ' : φ' ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2)
    (hφφ' : φ + φ' ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2) :
    cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 (φ + φ') hφφ' =
      cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 φ hφ +
        cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 φ' hφ' := by
  unfold cohomologyWithSupports.ofCocycle
  rw [← LinearEquiv.map_add, ← Submodule.Quotient.mk_add]
  rfl

/-- The class of a coboundary vanishes. -/
private theorem ofCocycle_eq_zero_of_eq_coboundary {φ : Simplex B 2 → ℤ}
    (hφ : φ ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2) (m : Simplex B 1 → ℤ)
    (h : φ = coboundary ℤ 1 m) :
    cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 φ hφ = 0 := by
  rw [ofCocycle_eq_of_sub_eq_coboundary hφ (Submodule.zero_mem _) m (by rw [sub_zero, h])]
  unfold cohomologyWithSupports.ofCocycle
  rw [show (⟨0, Submodule.zero_mem _⟩ : relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2) = 0
    from rfl, Submodule.Quotient.mk_zero]
  exact LinearEquiv.map_zero _

/-- Evaluation of a cochain on the image of a chain under a linear map. -/
private theorem eval_linearMap {n k : ℕ} (T : Chain ℤ B n →ₗ[ℤ] Chain ℤ B k) (ψ : Simplex B k → ℤ)
    (c : Chain ℤ B n) : eval ψ (T c) = eval (fun τ => eval ψ (T (Finsupp.single τ 1))) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, map_smul, map_smul]
    simp

/-- Evaluation only sees the simplices of the support. -/
private theorem eval_eq_of_eqOn_small {n : ℕ} {𝒰 : Set (Set B)} {φ φ' : Simplex B n → ℤ}
    (h : ∀ σ : Simplex B n, (∃ U ∈ 𝒰, Set.range σ ⊆ U) → φ σ = φ' σ) {c : Chain ℤ B n}
    (hc : c ∈ small ℤ n 𝒰) : eval φ c = eval φ' c := by
  have e : ∀ c : Chain ℤ B n, eval (φ - φ') c = eval φ c - eval φ' c := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]; ring
    | single σ a => simp [mul_sub]
  rw [← sub_eq_zero, ← e c]
  refine ComplexLineBundle.eval_eq_zero_of_mem_small (fun σ hσ => ?_) hc
  simp [h σ hσ]

/-- Pulling a cocycle back along the small-chains map changes it by a coboundary. -/
private theorem pullback_smallChainMap_sub (𝒰 : Set (Set B)) {ψ : Simplex B 2 → ℤ}
    (hδ : coboundary ℤ 2 ψ = 0) :
    pullback (smallChainMap ℤ 𝒰 2) ψ - ψ =
      coboundary ℤ 1 (fun τ => -eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) := by
  funext σ
  have e1 : eval ψ (bd ℤ 2 (smallHomotopy ℤ 𝒰 2 (Finsupp.single σ 1))) = 0 := by
    rw [← eval_coboundary, hδ]
    simp
  have e2 : eval ψ (smallHomotopy ℤ 𝒰 1 (bd ℤ 1 (Finsupp.single σ 1))) =
      coboundary ℤ 1 (fun τ => eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) σ := by
    rw [eval_linearMap, ← eval_coboundary]
    simp
  change eval ψ (smallChainMap ℤ 𝒰 (1 + 1) (Finsupp.single σ 1)) - ψ σ = _
  have hneg : (fun τ => -eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) =
      -(fun τ => eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) := rfl
  rw [smallChainMap_succ, map_sub, map_sub, e1, e2, hneg, map_neg]
  simp

/-- A cocycle which is a coboundary on the small simplices of an open cover is a coboundary. -/
private theorem exists_coboundary_of_small {𝒰 : Set (Set B)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U)
    (hcov : ∀ y : B, ∃ U ∈ 𝒰, y ∈ U) {ψ : Simplex B 2 → ℤ} (hδ : coboundary ℤ 2 ψ = 0)
    (m : Simplex B 1 → ℤ)
    (hm : ∀ σ : Simplex B 2, (∃ U ∈ 𝒰, Set.range σ ⊆ U) → ψ σ = coboundary ℤ 1 m σ) :
    ∃ m' : Simplex B 1 → ℤ, ψ = coboundary ℤ 1 m' := by
  have hρ : pullback (smallChainMap ℤ 𝒰 2) ψ =
      coboundary ℤ 1 (pullback (smallChainMap ℤ 𝒰 1) m) := by
    funext σ
    have hsmall := smallChainMap_single_mem_small (R := ℤ) h𝒰 2 (σ := σ)
      (fun y _ => Set.mem_sUnion.2 (by obtain ⟨U, hU, hy⟩ := hcov y; exact ⟨U, hU, hy⟩))
    change eval ψ (smallChainMap ℤ 𝒰 (1 + 1) (Finsupp.single σ 1)) = _
    rw [eval_eq_of_eqOn_small hm hsmall, eval_coboundary, bd_smallChainMap, ← eval_pullback,
      ← eval_coboundary]
    simp
  refine ⟨pullback (smallChainMap ℤ 𝒰 1) m -
    (fun τ => -eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))), ?_⟩
  rw [map_sub, ← hρ, ← pullback_smallChainMap_sub 𝒰 hδ, sub_sub_cancel]

/-- Local phase data over an open cover `𝒱`: edge phases `Φ V`, reference coordinates `v V` and
transition functions `g V W`, related as the edge phases, reference coordinates and transition
functions of a line bundle in a system of local frames. -/
private structure PhaseSystem (𝒱 : Set (Set B)) where
  /-- The edge phases in the frame over `V`. -/
  Φ : Set B → Simplex B 1 → ℂ
  /-- The reference coordinates in the frame over `V`. -/
  v : Set B → B → ℂ
  /-- The transition functions. -/
  g : Set B → Set B → B → ℂ
  v_ne : ∀ V ∈ 𝒱, ∀ y ∈ V, v V y ≠ 0
  g_cont : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ContinuousOn (g V W) (V ∩ W)
  g_ne : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W, g V W y ≠ 0
  exp_Φ : ∀ V ∈ 𝒱, ∀ τ : Simplex B 1, Set.range τ ⊆ V →
    exp (Φ V τ) = v V (τ (stdSimplex.vertex 1)) / v V (τ (stdSimplex.vertex 0))
  Φ_change : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ τ : Simplex B 1, Set.range τ ⊆ V ∩ W →
    Φ W τ = Φ V τ + logIncrement (g V W) τ
  v_change : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W, v W y = g V W y * v V y

namespace PhaseSystem

variable {𝒱 : Set (Set B)}

/-- `n` is the obstruction cochain of the phase system on `𝒱`-small simplices. -/
private def IsPhase (S : PhaseSystem 𝒱) (n : Simplex B 2 → ℤ) : Prop :=
  ∀ V ∈ 𝒱, ∀ σ : Simplex B 2, Set.range σ ⊆ V →
    (n σ : ℂ) * (2 * Real.pi * I) = coboundary ℂ 1 (S.Φ V) σ

/-- The product of two phase systems. -/
private def add (S₁ S₂ : PhaseSystem 𝒱) : PhaseSystem 𝒱 where
  Φ V := S₁.Φ V + S₂.Φ V
  v V y := S₁.v V y * S₂.v V y
  g V W y := S₁.g V W y * S₂.g V W y
  v_ne V hV y hy := mul_ne_zero (S₁.v_ne V hV y hy) (S₂.v_ne V hV y hy)
  g_cont V hV W hW := (S₁.g_cont V hV W hW).mul (S₂.g_cont V hV W hW)
  g_ne V hV W hW y hy := mul_ne_zero (S₁.g_ne V hV W hW y hy) (S₂.g_ne V hV W hW y hy)
  exp_Φ V hV τ hτ := by
    have h1 := S₂.v_ne V hV _ (hτ ⟨stdSimplex.vertex 1, rfl⟩)
    have h0 := S₂.v_ne V hV _ (hτ ⟨stdSimplex.vertex 0, rfl⟩)
    have h0' := S₁.v_ne V hV _ (hτ ⟨stdSimplex.vertex 0, rfl⟩)
    simp only [Pi.add_apply, exp_add, S₁.exp_Φ V hV τ hτ, S₂.exp_Φ V hV τ hτ]
    field_simp
  Φ_change V hV W hW τ hτ := by
    have hlog : logIncrement (fun y => S₁.g V W y * S₂.g V W y) τ =
        logIncrement (S₁.g V W) τ + logIncrement (S₂.g V W) τ := by
      refine logIncrement_mul (fun x => rfl) ?_ ?_
      · exact exists_continuous_log_comp τ (S₁.g_cont V hV W hW)
          (fun y hy => S₁.g_ne V hV W hW y hy) hτ
      · exact exists_continuous_log_comp τ (S₂.g_cont V hV W hW)
          (fun y hy => S₂.g_ne V hV W hW y hy) hτ
    simp only [Pi.add_apply, S₁.Φ_change V hV W hW τ hτ, S₂.Φ_change V hV W hW τ hτ, hlog]
    ring
  v_change V hV W hW y hy := by
    simp only [S₁.v_change V hV W hW y hy, S₂.v_change V hV W hW y hy]
    ring

private theorem IsPhase.add {S₁ S₂ : PhaseSystem 𝒱} {n₁ n₂ : Simplex B 2 → ℤ} (h₁ : S₁.IsPhase n₁)
    (h₂ : S₂.IsPhase n₂) : (S₁.add S₂).IsPhase (n₁ + n₂) := by
  intro V hV σ hσ
  change ((n₁ σ + n₂ σ : ℤ) : ℂ) * _ = coboundary ℂ 1 (S₁.Φ V + S₂.Φ V) σ
  rw [map_add, Pi.add_apply, ← h₁ V hV σ hσ, ← h₂ V hV σ hσ]
  push_cast
  ring

private theorem logIncrement_eq_zero_of_eqOn {f : B → ℂ} {τ : Simplex B 1}
    (h : ∀ x, f (τ x) = 1) : logIncrement f τ = 0 := by
  rw [logIncrement_eq (0 : C(stdSimplex ℝ (Fin 2), ℂ)) fun x => by simp [h x]]
  simp

/-- **A trivial phase system has a coboundary as obstruction.** -/
private theorem exists_coboundary_of_trivial (S : PhaseSystem 𝒱) (hcov : ∀ y : B, ∃ V ∈ 𝒱, y ∈ V)
    (hg : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W, S.g V W y = 1) {n : Simplex B 2 → ℤ}
    (hn : S.IsPhase n) :
    ∃ m : Simplex B 1 → ℤ, ∀ σ : Simplex B 2, (∃ V ∈ 𝒱, Set.range σ ⊆ V) →
      n σ = coboundary ℤ 1 m σ := by
  classical
  choose Vp hVp hpV using hcov
  let c : Simplex B 0 → ℂ := fun p => log (S.v (Vp (p (stdSimplex.vertex 0)))
    (p (stdSimplex.vertex 0)))
  let Φs : Simplex B 1 → ℂ := fun τ =>
    if h : ∃ V ∈ 𝒱, Set.range τ ⊆ V then S.Φ h.choose τ else 0
  have hΦs : ∀ V ∈ 𝒱, ∀ τ : Simplex B 1, Set.range τ ⊆ V → Φs τ = S.Φ V τ := by
    intro V hV τ hτ
    have h : ∃ V ∈ 𝒱, Set.range τ ⊆ V := ⟨V, hV, hτ⟩
    simp only [Φs, dite_eq_left h]
    rw [S.Φ_change _ h.choose_spec.1 V hV τ (Set.subset_inter h.choose_spec.2 hτ),
      logIncrement_eq_zero_of_eqOn (fun x => hg _ h.choose_spec.1 V hV _
        ⟨h.choose_spec.2 ⟨x, rfl⟩, hτ ⟨x, rfl⟩⟩), add_zero]
  have hv : ∀ V ∈ 𝒱, ∀ y ∈ V, S.v V y = S.v (Vp y) y := by
    intro V hV y hy
    rw [S.v_change (Vp y) (hVp y) V hV y ⟨hpV y, hy⟩, hg _ (hVp y) V hV y ⟨hpV y, hy⟩, one_mul]
  have hint : ∀ τ : Simplex B 1, ∃ k : ℤ, (∃ V ∈ 𝒱, Set.range τ ⊆ V) →
      Φs τ - coboundary ℂ 0 c τ = k * (2 * Real.pi * I) := by
    intro τ
    by_cases h : ∃ V ∈ 𝒱, Set.range τ ⊆ V
    · obtain ⟨V, hV, hτ⟩ := h
      have hτ1 := hτ ⟨stdSimplex.vertex 1, rfl⟩
      have hτ0 := hτ ⟨stdSimplex.vertex 0, rfl⟩
      have hδc : coboundary ℂ 0 c τ = log (S.v (Vp (τ (stdSimplex.vertex 1)))
          (τ (stdSimplex.vertex 1))) - log (S.v (Vp (τ (stdSimplex.vertex 0)))
          (τ (stdSimplex.vertex 0))) := by
        rw [coboundary_apply, Fin.sum_univ_two]
        simp only [c, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_one_mul,
          ContinuousMap.comp_apply]
        have e0 : face 0 0 (stdSimplex.vertex 0) = stdSimplex.vertex 1 := by
          simp [face, stdSimplex.map_vertex]
        have e1 : face 0 1 (stdSimplex.vertex 0) = stdSimplex.vertex 0 := by
          simp [face, stdSimplex.map_vertex]
        rw [e0, e1]
        ring
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (show exp (Φs τ - coboundary ℂ 0 c τ) = 1 by
        rw [hδc, hΦs V hV τ hτ, exp_sub, exp_sub, S.exp_Φ V hV τ hτ,
          exp_log (S.v_ne _ (hVp _) _ (hpV _)), exp_log (S.v_ne _ (hVp _) _ (hpV _)),
          ← hv V hV _ hτ1, ← hv V hV _ hτ0]
        have := S.v_ne V hV _ hτ1
        have := S.v_ne V hV _ hτ0
        field_simp)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose m hm using hint
  refine ⟨m, fun σ ⟨V, hV, hσ⟩ => ?_⟩
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hfaces : ∀ i : Fin 3, Set.range (σ.comp (face 1 i)) ⊆ V :=
    fun i _ ⟨x, hx⟩ => hσ ⟨_, hx⟩
  have key : (n σ : ℂ) * (2 * Real.pi * I) =
      ((coboundary ℤ 1 m σ : ℤ) : ℂ) * (2 * Real.pi * I) := by
    rw [hn V hV σ hσ, coboundary_apply, coboundary_apply]
    have e : ∀ i : Fin 3, S.Φ V (σ.comp (face 1 i)) =
        (m (σ.comp (face 1 i)) : ℂ) * (2 * Real.pi * I) +
          coboundary ℂ 0 c (σ.comp (face 1 i)) := by
      intro i
      rw [← hΦs V hV _ (hfaces i), ← hm _ ⟨V, hV, hfaces i⟩]
      ring
    simp only [e, mul_add, Finset.sum_add_distrib]
    have hδδ := congr_fun (coboundary_coboundary 0 c) σ
    rw [coboundary_apply] at hδδ
    rw [hδδ]
    push_cast
    rw [Finset.sum_mul]
    simp only [add_zero, Pi.zero_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  exact_mod_cast mul_right_cancel₀ h2pi key

end PhaseSystem

section Bundle

variable {B' : Type} [TopologicalSpace B'] {E : B → Type*} [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℂ (E b)] [TopologicalSpace (TotalSpace ℂ E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]

/-- A system of frames of `E` along `f` over the members of `𝒱`. -/
private def IsFrameSystem (𝒱 : Set (Set B')) (f : C(B', B))
    (e : Set B' → Trivialization ℂ (π ℂ E)) : Prop :=
  ∀ V ∈ 𝒱, e V ∈ trivializationAtlas ℂ E ∧ ∀ y ∈ V, f y ∈ (e V).baseSet

/-- The phase system of a line bundle pulled back along `f`, in a system of frames. -/
private def bundleSystem {𝒱 : Set (Set B')} {f : C(B', B)} {e : Set B' → Trivialization ℂ (π ℂ E)}
    (he : IsFrameSystem 𝒱 f e) : PhaseSystem (B := B') 𝒱 where
  Φ V τ := edgePhase (E := E) (e V) (f.comp τ)
  v V y := vertexCoord (E := E) (e V) (f y)
  g V W y := transition (e V) (e W) (f y)
  v_ne V hV y hy := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    exact vertexCoord_ne_zero ((he V hV).2 y hy)
  g_cont V hV W hW := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    have : MemTrivializationAtlas (e W) := ⟨(he W hW).1⟩
    exact (continuousOn_transition (e := e V) (e' := e W)).comp f.continuous.continuousOn
      (fun y hy => ⟨(he V hV).2 y hy.1, (he W hW).2 y hy.2⟩)
  g_ne V hV W hW y hy := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    have : MemTrivializationAtlas (e W) := ⟨(he W hW).1⟩
    exact transition_ne_zero ⟨(he V hV).2 y hy.1, (he W hW).2 y hy.2⟩
  exp_Φ V hV τ hτ := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    exact exp_edgePhase fun _ ⟨x, hx⟩ => hx ▸ (he V hV).2 _ (hτ ⟨x, rfl⟩)
  Φ_change V hV W hW τ hτ := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    have : MemTrivializationAtlas (e W) := ⟨(he W hW).1⟩
    have hV' : Set.range (f.comp τ) ⊆ (e V).baseSet :=
      fun _ ⟨x, hx⟩ => hx ▸ (he V hV).2 _ (hτ ⟨x, rfl⟩).1
    have hW' : Set.range (f.comp τ) ⊆ (e W).baseSet :=
      fun _ ⟨x, hx⟩ => hx ▸ (he W hW).2 _ (hτ ⟨x, rfl⟩).2
    have hs := range_subset_simplexTriv (E := E) (he V hV).1 hV'
    simp only [edgePhase]
    rw [add_assoc, logIncrement_mul (g := transition (simplexTriv (E := E) (f.comp τ)) (e V))
      (h := transition (e V) (e W))]
    · rfl
    · intro x
      rw [transition_trans (hs ⟨x, rfl⟩) (hV' ⟨x, rfl⟩) (hW' ⟨x, rfl⟩), mul_comm]
    · exact exists_continuous_log_comp (f.comp τ) continuousOn_transition
        (fun y hy => transition_ne_zero hy) (Set.subset_inter hs hV')
    · exact exists_continuous_log_comp (f.comp τ) continuousOn_transition
        (fun y hy => transition_ne_zero hy) (Set.subset_inter hV' hW')
  v_change V hV W hW y hy := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    have : MemTrivializationAtlas (e W) := ⟨(he W hW).1⟩
    exact vertexCoord_eq ((he V hV).2 y hy.1) ((he W hW).2 y hy.2)

private theorem isPhase_bundleSystem {𝒱 : Set (Set B')} {f : C(B', B)}
    {e : Set B' → Trivialization ℂ (π ℂ E)} (he : IsFrameSystem 𝒱 f e) :
    (bundleSystem he).IsPhase (fun σ => obstructionCocycle E (f.comp σ)) := by
  intro V hV σ hσ
  have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
  have hfσ : Set.range (f.comp σ) ⊆ (e V).baseSet :=
    fun _ ⟨x, hx⟩ => hx ▸ (he V hV).2 _ (hσ ⟨x, rfl⟩)
  rw [obstructionCocycle_mul hfσ, obstructionPhase_eq_coboundary hfσ]
  rfl

omit [∀ b, Module ℂ (E b)] [VectorBundle ℂ ℂ E] in
private theorem coboundary_obstructionCocycle_comp [∀ b, Module ℂ (E b)] [VectorBundle ℂ ℂ E]
    (f : C(B', B)) :
    coboundary ℤ 2 (fun σ : Simplex B' 2 => obstructionCocycle E (f.comp σ)) = 0 := by
  funext σ
  exact congr_fun (coboundary_obstructionCocycle (E := E)) (f.comp σ)

/-- The pull-back of a first Chern class is the class of the pulled back obstruction cocycle. -/
private theorem map_firstChernClass {B₀ : Type} [TopologicalSpace B₀] {E₀ : B₀ → Type*}
    [∀ b, AddCommGroup (E₀ b)] [∀ b, Module ℂ (E₀ b)] [TopologicalSpace (TotalSpace ℂ E₀)]
    [∀ b, TopologicalSpace (E₀ b)] [FiberBundle ℂ E₀] [VectorBundle ℂ ℂ E₀]
    (f : TopCat.of B' ⟶ TopCat.of B₀) :
    (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) f (A' := Set.univᶜ) (A := Set.univᶜ)
      (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2).hom (firstChernClass E₀) =
      cohomologyWithSupports.ofCocycle ℤ (TopCat.of B') 2
        (fun σ => obstructionCocycle E₀ (f.hom.comp σ))
        (mem_relCocycles_of_coboundary_eq_zero (coboundary_obstructionCocycle_comp f.hom)) := by
  apply (relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set (TopCat.of B')) 2).injective
  have := relativeSingularCohomologyEquiv_map f (A' := Set.univᶜ) (A := Set.univᶜ)
    (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2 (firstChernClass E₀)
  refine this.trans ?_
  simp only [firstChernClass, cohomologyWithSupports.ofCocycle, LinearEquiv.apply_symm_apply,
    relCohomologyMap_mk]
  rfl

/-- **Trivial transition functions give a trivial Chern class.** -/
private theorem map_firstChernClass_eq_zero {𝒱 : Set (Set B')} (h𝒱 : ∀ V ∈ 𝒱, IsOpen V)
    (hcov : ∀ y : B', ∃ V ∈ 𝒱, y ∈ V) (f : TopCat.of B' ⟶ TopCat.of B)
    {e : Set B' → Trivialization ℂ (π ℂ E)} (he : IsFrameSystem 𝒱 f.hom e)
    (htr : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W, transition (e V) (e W) (f y) = 1) :
    (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) f (A' := Set.univᶜ) (A := Set.univᶜ)
      (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2).hom (firstChernClass E) = 0 := by
  rw [map_firstChernClass]
  obtain ⟨m, hm⟩ := (bundleSystem he).exists_coboundary_of_trivial hcov htr
    (isPhase_bundleSystem he)
  obtain ⟨m', hm'⟩ := exists_coboundary_of_small h𝒱 hcov
    (coboundary_obstructionCocycle_comp f.hom) m hm
  exact ofCocycle_eq_zero_of_eq_coboundary _ m' hm'

/-- **Inverse transition functions give opposite Chern classes.** -/
private theorem map_firstChernClass_add_eq_zero {B₂ : Type} [TopologicalSpace B₂]
    {E₂ : B₂ → Type*} [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℂ (E₂ b)]
    [TopologicalSpace (TotalSpace ℂ E₂)] [∀ b, TopologicalSpace (E₂ b)] [FiberBundle ℂ E₂]
    [VectorBundle ℂ ℂ E₂] {𝒱 : Set (Set B')} (h𝒱 : ∀ V ∈ 𝒱, IsOpen V)
    (hcov : ∀ y : B', ∃ V ∈ 𝒱, y ∈ V) (f : TopCat.of B' ⟶ TopCat.of B)
    (f₂ : TopCat.of B' ⟶ TopCat.of B₂)
    {e : Set B' → Trivialization ℂ (π ℂ E)} (he : IsFrameSystem 𝒱 f.hom e)
    {e₂ : Set B' → Trivialization ℂ (π ℂ E₂)} (he₂ : IsFrameSystem 𝒱 f₂.hom e₂)
    (htr : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W,
      transition (e V) (e W) (f y) * transition (e₂ V) (e₂ W) (f₂ y) = 1) :
    (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) f (A' := Set.univᶜ) (A := Set.univᶜ)
      (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2).hom (firstChernClass E) +
    (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) f₂ (A' := Set.univᶜ) (A := Set.univᶜ)
      (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2).hom (firstChernClass E₂) = 0 := by
  rw [map_firstChernClass, map_firstChernClass]
  have hT := (isPhase_bundleSystem he).add (isPhase_bundleSystem he₂)
  obtain ⟨m, hm⟩ := ((bundleSystem he).add (bundleSystem he₂)).exists_coboundary_of_trivial hcov
    htr hT
  have hδ : coboundary ℤ 2 ((fun σ => obstructionCocycle E (f.hom.comp σ)) +
      (fun σ => obstructionCocycle E₂ (f₂.hom.comp σ))) = 0 := by
    rw [map_add, coboundary_obstructionCocycle_comp, coboundary_obstructionCocycle_comp, add_zero]
  obtain ⟨m', hm'⟩ := exists_coboundary_of_small h𝒱 hcov hδ m hm
  rw [← ofCocycle_add _ _ (mem_relCocycles_of_coboundary_eq_zero hδ)]
  exact ofCocycle_eq_zero_of_eq_coboundary _ m' hm'

end Bundle

end Chern

section Generators

open Opposite MMP.Analytic.InvertibleModule

variable {X : Scheme.{0}} (I : X.IdealSheafData)

private lemma map_refl_apply {Y : Scheme.{0}} (W : Y.Opens) (f : Γ(Y, W)) :
    (Y.presheaf.map (homOfLE (le_refl W)).op).hom f = f := by
  rw [show (homOfLE (le_refl W)).op = 𝟙 (op W) from rfl, CategoryTheory.Functor.map_id]; rfl

private def inclΓ (V : (blowUp I).Opens) (m : Γ(exceptionalIdealModule I, V)) : Γ(blowUp I, V) :=
  ((Stacks.CartierAffineLocal.incl (exceptionalIdeal I)).val.app (op V)).hom m

private lemma inclΓ_smul (V : (blowUp I).Opens) (c : Γ(blowUp I, V))
    (m : Γ(exceptionalIdealModule I, V)) :
    inclΓ I V (c • m) = c * inclΓ I V m :=
  map_smul ((Stacks.CartierAffineLocal.incl (exceptionalIdeal I)).val.app (op V)).hom c m

private lemma inclΓ_res (V W : (blowUp I).Opens) (h : V ≤ W) (m : Γ(exceptionalIdealModule I, W)) :
    inclΓ I V (sectionRes (exceptionalIdealModule I) h m) =
      (blowUp I).presheaf.map (homOfLE h).op (inclΓ I W m) :=
  PresheafOfModules.naturality_apply (Stacks.CartierAffineLocal.incl (exceptionalIdeal I)).val
    (homOfLE h).op m

private lemma inclΓ_injective (V : (blowUp I).Opens) : Function.Injective (inclΓ I V) :=
  Stacks.CartierAffineLocal.injective_incl_app (exceptionalIdeal I) V

/-- **A generator from a principal description.** If on every open `V ⊆ W` the sections of the
exceptional ideal sheaf are exactly the multiples of `f|_V`, and `f|_V` is a nonzerodivisor,
then a section with image `f` is a local generator over `W`. -/
private def genOfPrincipal (W : (blowUp I).Opens) (f : Γ(blowUp I, W))
    (hreg : ∀ (V : (blowUp I).Opens) (h : V ≤ W),
      (blowUp I).presheaf.map (homOfLE h).op f ∈ nonZeroDivisors Γ(blowUp I, V))
    (hsec : ∀ (V : (blowUp I).Opens) (h : V ≤ W) (m : Γ(exceptionalIdealModule I, V)),
      ∃ a, inclΓ I V m = a * (blowUp I).presheaf.map (homOfLE h).op f)
    (hex : ∀ (V : (blowUp I).Opens) (h : V ≤ W) (a : Γ(blowUp I, V)),
      ∃ m : Γ(exceptionalIdealModule I, V),
        inclΓ I V m = a * (blowUp I).presheaf.map (homOfLE h).op f) :
    Generator (exceptionalIdealModule I) where
  W := W
  a := (hex W le_rfl 1).choose
  bijective V h := by
    have ha : inclΓ I W (hex W le_rfl 1).choose = f := by
      rw [(hex W le_rfl 1).choose_spec, one_mul, map_refl_apply]
    have key : ∀ c : Γ(blowUp I, V), inclΓ I V (c • sectionRes (exceptionalIdealModule I) h
        (hex W le_rfl 1).choose) = c * (blowUp I).presheaf.map (homOfLE h).op f := by
      intro c
      rw [inclΓ_smul, inclΓ_res, ha]
    refine ⟨fun c c' hcc' ↦ ?_, fun m ↦ ?_⟩
    · have := congrArg (inclΓ I V) hcc'
      simp only [key] at this
      exact (mul_cancel_right_mem_nonZeroDivisors (hreg V h)).mp this
    · obtain ⟨a, ha'⟩ := hsec V h m
      exact ⟨a, inclΓ_injective I V (by rw [key, ha'])⟩

private lemma inclΓ_genOfPrincipal_a (W : (blowUp I).Opens) (f : Γ(blowUp I, W)) (hreg hsec hex) :
    inclΓ I W (genOfPrincipal I W f hreg hsec hex).a = f := by
  change inclΓ I W (hex W le_rfl 1).choose = f
  rw [(hex W le_rfl 1).choose_spec, one_mul, map_refl_apply]

/-- **The transition function of two generators**, from a relation between their images. -/
private lemma transitionSection_eq_of_inclΓ (s s' : Generator (exceptionalIdealModule I))
    (g : Γ(blowUp I, s.W ⊓ s'.W))
    (h : (blowUp I).presheaf.map (homOfLE inf_le_left).op (inclΓ I s.W s.a) =
      g * (blowUp I).presheaf.map (homOfLE inf_le_right).op (inclΓ I s'.W s'.a)) :
    transitionSection s s' = g := by
  refine s'.coeff_eq inf_le_right (inclΓ_injective I _ ?_)
  rw [inclΓ_smul, inclΓ_res, inclΓ_res, h]

/-- The generator of the exceptional ideal on the standard chart at a section `a`. -/
private def chartGen (U : X.affineOpens) (a : I.ideal U) : Generator (exceptionalIdealModule I) :=
  genOfPrincipal I (blowUpChartOpen I U a).1 ((blowUpChartMap I U a).hom (a : Γ(X, U.1)))
    (fun V h ↦ Stacks.CartierAffineLocalConverse.nonZeroDivisor_res (blowUpChartOpen I U a) _
      (blowUpChartMap_self_mem_nonZeroDivisors I U a) (homOfLE h))
    (fun V h m ↦ Stacks.CartierAffineLocalConverse.exists_mul (exceptionalIdeal I)
      (blowUpChartOpen I U a) _ (blowUpChartMap_self_mem_nonZeroDivisors I U a)
      (ideal_exceptionalIdeal_blowUpChartOpen I U a) (homOfLE h) m)
    (fun V h a' ↦ Stacks.CartierAffineLocalConverse.exists_section (exceptionalIdeal I)
      (blowUpChartOpen I U a) _ (blowUpChartMap_self_mem_nonZeroDivisors I U a)
      (ideal_exceptionalIdeal_blowUpChartOpen I U a) (homOfLE h) a')

/-- The complement of the exceptional divisor. -/
private def offE : (blowUp I).Opens :=
  ⟨((exceptionalIdeal I).support : Set (blowUp I))ᶜ,
    (exceptionalIdeal I).support.isClosed.isOpen_compl⟩

private lemma exists_inclΓ_eq_of_le_offE (V : (blowUp I).Opens) (h : V ≤ offE I)
    (a : Γ(blowUp I, V)) :
    ∃ m : Γ(exceptionalIdealModule I, V), inclΓ I V m = a := by
  have hbot : (exceptionalIdeal I).subschemeι ⁻¹ᵁ V = ⊥ := by
    refine eq_bot_iff.2 fun z hz ↦ ?_
    exfalso
    have h1 : (exceptionalIdeal I).subschemeι z ∈
        ((exceptionalIdeal I).support : Set (blowUp I)) := by
      rw [← (exceptionalIdeal I).range_subschemeι]; exact ⟨z, rfl⟩
    exact h hz h1
  have : Subsingleton Γ((exceptionalIdeal I).subscheme,
      (exceptionalIdeal I).subschemeι ⁻¹ᵁ V) := by rw [hbot]; infer_instance
  exact (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker
    (exceptionalIdeal I).subschemeι V a).mpr (Subsingleton.elim _ _)

/-- The generator `1` of the exceptional ideal off the exceptional divisor. -/
private def offGen : Generator (exceptionalIdealModule I) :=
  genOfPrincipal I (offE I) 1
    (fun V h ↦ by rw [map_one]; exact one_mem _)
    (fun V h m ↦ ⟨inclΓ I V m, by rw [map_one, mul_one]⟩)
    (fun V h a ↦ by
      obtain ⟨m, hm⟩ := exists_inclΓ_eq_of_le_offE I V h a
      exact ⟨m, by rw [hm, map_one, mul_one]⟩)

end Generators

section Step

open Set Bundle MMP.Analytic.InvertibleModule MMP.Analytic.ComplexLineBundle MMP.Topology
open MMP.cohomologyWithSupports

variable {X : Scheme.{0}}

/-- The image of a local generator under an isomorphism. -/
private def genMap {L M : X.Modules} (e : L ≅ M) (s : Generator L) : Generator M where
  W := s.W
  a := e.hom.app s.W s.a
  bijective V h := by
    have hb : Function.Bijective (e.hom.app V) := by
      refine ⟨fun x y hxy => ?_, fun y => ⟨e.inv.app V y, ?_⟩⟩
      · have := congrArg (e.inv.app V) hxy
        rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app] at this
      · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id,
          Scheme.Modules.Hom.id_app]
        rfl
    have : (fun c : Γ(X, V) => c • sectionRes M h (e.hom.app s.W s.a)) =
        e.hom.app V ∘ fun c : Γ(X, V) => c • sectionRes L h s.a := by
      funext c
      simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul]
      exact congrArg (c • ·) (PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op s.a).symm
    rw [this]
    exact hb.comp (s.bijective V h)

private theorem transitionSection_map {L M : X.Modules} (e : L ≅ M) (s s' : Generator L) :
    transitionSection (genMap e s) (genMap e s') = transitionSection s s' := by
  refine (genMap e s').coeff_eq inf_le_right ?_
  have h1 := (PresheafOfModules.naturality_apply e.hom.val
    (homOfLE (inf_le_right : s.W ⊓ s'.W ≤ s'.W)).op s'.a).symm
  have h2 := (PresheafOfModules.naturality_apply e.hom.val
    (homOfLE (inf_le_left : s.W ⊓ s'.W ≤ s.W)).op s.a).symm
  have h3 := Scheme.Modules.Hom.app_smul e.hom (transitionSection s s')
    (sectionRes L (inf_le_right : s.W ⊓ s'.W ≤ s'.W) s'.a)
  rw [transitionSection_smul] at h3
  exact (congrArg (transitionSection s s' • ·) h1).trans (h3.symm.trans h2.symm)

variable [X.Over (Spec (.of ℂ))]

private theorem transition_localTriv (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (s s' : Generator L)
    {y : ComplexPoints (X ↘ Spec (.of ℂ))} (hy : y ∈ chart s.W ∩ chart s'.W) :
    transition ((lineBundleCore L).localTriv s) ((lineBundleCore L).localTriv s') y =
      evalExt _ (transitionSection s s') y := by
  have : MemTrivializationAtlas ((lineBundleCore L).localTriv s) := ⟨⟨s, rfl⟩⟩
  have : MemTrivializationAtlas ((lineBundleCore L).localTriv s') := ⟨⟨s', rfl⟩⟩
  rw [transition_eq_coordChangeL hy,
    VectorBundleCore.localTriv_coordChange_eq (R := ℂ) _ _ _ ⟨hy.1, hy.2⟩]
  change evalExt _ (transitionSection s s') y • (1 : ℂ) = _
  rw [smul_eq_mul, mul_one]

end Step

/-- The `ℂ`-point over a closed point, and its uniqueness. -/
private theorem exists_complexPoint {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    ∃ yc : ComplexPoints sY, yc.toScheme = y ∧ ∀ p : ComplexPoints sY, p.toScheme = y → p = yc := by
  refine ⟨⟨pointOfClosedPoint sY y hy, pointOfClosedPoint_comp sY y hy⟩,
    pointOfClosedPoint_apply sY y hy _, fun p hp ↦ ComplexPoints.ext ?_⟩
  refine ext_of_apply_closedPoint_eq sY p.2 (pointOfClosedPoint_comp sY y hy) ?_
  exact (congrArg p.hom (Subsingleton.elim _ _)).trans
    (hp.trans (pointOfClosedPoint_apply sY y hy _).symm)

section Euler

open Set Bundle MMP.Topology

private lemma congrIndex_map {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {A' : Set Y'} {A : Set Y}
    (h : A' ⊆ f ⁻¹' A) {k k' : ℤ} (hk : k = k')
    (x : relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ) Y A k) :
    (relativeSingularCohomology.map ℤ _ f h k').hom
        (cohomologyWithSupports.congrIndex ℤ Y rfl hk x) =
      cohomologyWithSupports.congrIndex ℤ Y' rfl hk
        ((relativeSingularCohomology.map ℤ _ f h k).hom x) := by
  subst hk; rfl

private lemma pb_bundleZeroSection_thomTwoAbs :
    (pb (bundleZeroSection ℂ (TautologicalBundle 1)) 2).hom thomTwoAbs =
      firstChernClass (TautologicalBundle 1) := by
  refine (MMP.Topology.relativeSingularCohomology_map_map_apply ℤ
    (bundleZeroSection ℂ (TautologicalBundle 1)) (𝟙 _) (A' := univᶜ)
    (A := (range (zeroSection ℂ (TautologicalBundle 1)))ᶜ) _ _
    (fun x hx ↦ (hx (mem_univ x)).elim) _ thomTwo).trans ?_
  refine (congrArg (fun m ↦ m.hom thomTwo) (MMP.Topology.relativeSingularCohomology_map_congr ℤ
    (Category.comp_id (bundleZeroSection ℂ (TautologicalBundle 1)))
    (A' := univᶜ) (A := (range (zeroSection ℂ (TautologicalBundle 1)))ᶜ) _
    (fun x hx ↦ (hx (mem_univ x)).elim) _)).trans ?_
  exact (congrIndex_map _ _ two_mul_finrank_complex _).trans
    (MMP.Analytic.ComplexLineBundle.congrIndex_eulerClass_eq_firstChernClass
      (E := TautologicalBundle 1))

private lemma pb_thomTwoAbs {T : TopCat.{0}} (f : T ⟶ TopCat.of TE) :
    (pb f 2).hom thomTwoAbs =
      (pb (f ≫ bundleProj ℂ (TautologicalBundle 1)) 2).hom
        (firstChernClass (TautologicalBundle 1)) := by
  rw [← pb_bundleProj_pb_bundleZeroSection thomTwoAbs, pb_bundleZeroSection_thomTwoAbs,
    pb_pb_apply]

end Euler

section OffE

open Set Bundle MMP.Analytic.InvertibleModule MMP.Analytic.ComplexLineBundle

/-- **`c₁(𝒪(1))` vanishes off the exceptional divisor.** -/
private theorem restrictCompl_firstChernClass_eq_zero {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    {y : Y}
    (I : Y.IdealSheafData) (hI : (I.support : Set Y) = {y}) (yc : ComplexPoints sY)
    (hyc : ∀ p : ComplexPoints sY, p.toScheme = y → p = yc)
    [(blowUp I).Over (Spec (.of ℂ))] (hB : blowUpToBase I ≫ sY = blowUp I ↘ Spec (.of ℂ))
    [SheafOfModules.IsInvertible (blowUp I).presheaf (blowUp I).ringCatSheaf.2
      (blowUpTwist I 1)] :
    (cohomologyWithSupports.restrictCompl ℤ (analyticSpace (blowUp I ↘ Spec (.of ℂ)))
      (analyticMap (blowUpToBase I) hB ⁻¹' {yc}) 2).hom
        (algebraicFirstChernClass (blowUpTwist I 1)) = 0 := by
  let L := blowUpTwist I 1
  let s₀ : Generator L := genMap (twistOneIsoExceptionalIdealModule I).symm (offGen I)
  let E : Set (ComplexPoints (blowUp I ↘ Spec (.of ℂ))) :=
    analyticMap (blowUpToBase I) hB ⁻¹' {yc}
  have hfr : ∀ q : ComplexPoints (blowUp I ↘ Spec (.of ℂ)), q ∉ E → q ∈ chart s₀.W := by
    intro q hq
    refine mem_chart_iff.2 ?_
    change q.toScheme ∈ ((exceptionalIdeal I).support : Set (blowUp I))ᶜ
    intro hmem
    apply hq
    change analyticMap (blowUpToBase I) hB q = yc
    apply hyc
    have h1 : q.toScheme ∈ (blowUpToBase I) ⁻¹' (I.support : Set Y) := by
      have := Scheme.IdealSheafData.support_comap I (blowUpToBase I)
      rwa [show ((exceptionalIdeal I).support : Set (blowUp I)) =
        (I.support.preimage (blowUpToBase I).continuous : Set (blowUp I)) from
          congrArg SetLike.coe this] at hmem
    rwa [Set.mem_preimage, hI] at h1
  have he : IsFrameSystem ({univ} : Set (Set ↥Eᶜ))
      (subspaceInclusion (analyticSpace (blowUp I ↘ Spec (.of ℂ))) Eᶜ).hom
      (fun _ ↦ (lineBundleCore L).localTriv s₀) := by
    intro V _
    exact ⟨⟨s₀, rfl⟩, fun q _ ↦ hfr q.1 q.2⟩
  exact map_firstChernClass_eq_zero (B := ComplexPoints (blowUp I ↘ Spec (.of ℂ)))
    (E := (lineBundleCore L).Fiber) (𝒱 := ({univ} : Set (Set ↥Eᶜ)))
    (by rintro V rfl; exact isOpen_univ) (fun q ↦ ⟨univ, rfl, trivial⟩)
    (subspaceInclusion (analyticSpace (blowUp I ↘ Spec (.of ℂ))) Eᶜ) he (by
      rintro V rfl W rfl q -
      have hq : (subspaceInclusion (analyticSpace (blowUp I ↘ Spec (.of ℂ))) Eᶜ) q ∈
          chart s₀.W ∩ chart s₀.W := ⟨hfr q.1 q.2, hfr q.1 q.2⟩
      rw [transition_localTriv L s₀ s₀ hq, transitionSection_self]
      exact evalExt_one (by rwa [chart_inf]))

end OffE

section Model

open Set _root_.Topology

/-- A scheme with an étale morphism to `𝔸^r_k` over `k` is smooth of relative dimension `r`. -/
private theorem smoothOfRelativeDimension_of_etale_homOfVector {k : Type} [Field k]
    {T : Scheme.{0}} (g : T ⟶ Spec (.of k)) {r : ℕ} (v : ULift.{0} (Fin r) → Γ(T, ⊤))
    (h : Etale (AffineSpace.homOfVector g v)) : SmoothOfRelativeDimension r g := by
  haveI := Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver (Spec (.of k)) r
  rw [← AffineSpace.homOfVector_over g v]
  simpa using (inferInstance : SmoothOfRelativeDimension (0 + r)
    (AffineSpace.homOfVector g v ≫ 𝔸(ULift.{0} (Fin r); Spec (.of k)) ↘ Spec (.of k)))

/-- **Local coordinates at a closed point of a smooth surface**, cutting out the point. -/
private theorem exists_coords {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (hY : MMP.Mori.IsVariety ℂ sY)
    (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (yc : ComplexPoints sY) (hyc : yc.toScheme = y) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (x : Fin 2 → Γ(Y, U)),
      MMP.Resolution.IsLocalCoordinates sY U x ∧
      ∀ (W : Y.affineOpens) (h : W.1 ≤ U),
        (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal W =
          Ideal.span (Set.range fun i ↦ (Y.presheaf.map (homOfLE h).op).hom (x i)) := by
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  have hI := MMP.Threefold.Resolution.isSmoothBlowup_vanishingIdeal_singleton sY hYs hy
  have hirr := MMP.Threefold.Resolution.isIrreducible_support_vanishingIdeal_singleton hy
  have hcodim : codimension (⟨(Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support, hirr,
      (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds Y) = 2 := by
    have heq : (⟨(Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support, hirr,
        (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support.isClosed⟩ :
          TopologicalSpace.IrreducibleCloseds Y) =
        TopologicalSpace.IrreducibleCloseds.closureSingleton y := by
      ext1
      change ((Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support : Set Y) = closure {y}
      rw [MMP.Threefold.Resolution.support_vanishingIdeal_singleton hy, hy.closure_eq]
    rw [heq,
      Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight]
    have h2 := MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two sY hY hYd y hy
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h2
    have h3 : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := h2
    exact WithBot.coe_injective h3
  obtain ⟨U, hU, hyU, N, x, hx, hnN, hf, -, -⟩ :=
    MMP.Topology.exists_homeomorph_preimage_analyticMap_blowUpToBase_charts_of_isIrreducible sY
      _ hI hirr 2 (by norm_num) hcodim yc (by
        rw [hyc]
        change y ∈ ((Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support : Set Y)
        rw [MMP.Threefold.Resolution.support_vanishingIdeal_singleton hy]; rfl)
  rw [hyc] at hyU
  have hN : N = 2 := by
    haveI := smoothOfRelativeDimension_of_etale_homOfVector (U.ι ≫ sY) _ hx
    haveI : Smooth sY := hYs.smooth
    haveI : SmoothOfRelativeDimension 2 sY :=
      MMP.Intersection.smoothOfRelativeDimension_of_isVariety sY 2 hYd
    haveI : SmoothOfRelativeDimension 2 (U.ι ≫ sY) := by
      simpa using (inferInstance : SmoothOfRelativeDimension (0 + 2) (U.ι ≫ sY))
    have h1 := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field N (U.ι ≫ sY)
      ⟨y, hyU⟩
    have h2 := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field 2 (U.ι ≫ sY)
      ⟨y, hyU⟩
    exact_mod_cast h1.symm.trans h2
  subst hN
  refine ⟨U, hU, hyU, x, hx, fun W h ↦ ?_⟩
  rw [hf W h]
  rfl

/-- **Étale coordinates are a chart of `Y^an`** near a point of their domain. -/
private theorem exists_coordChart {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (hY : MMP.Mori.IsVariety ℂ sY)
    (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {U : Y.Opens}
    {x : Fin 2 → Γ(Y, U)} (hx : MMP.Resolution.IsLocalCoordinates sY U x) (yc : ComplexPoints sY)
    (hycU : yc ∈ chart U) :
    ∃ e : OpenPartialHomeomorph (ComplexPoints sY) (Fin 2 → ℂ), yc ∈ e.source ∧
      e.source ⊆ chart U ∧ ∀ (p : ComplexPoints sY) (_ : p ∈ e.source) (hp' : p ∈ chart U)
        (j : Fin 2), e p j = eval U (x j) ⟨p, hp'⟩ := by
  haveI : IsVariety ℂ sY := hY
  haveI : Smooth sY := hYs.smooth
  haveI : SmoothOfRelativeDimension 2 sY :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety sY 2 hYd
  obtain ⟨c, hyc, -, hcU, hc⟩ := EtaleCoordinateChart.exists_of_etale U x hx hycU isOpen_univ
    (mem_univ yc)
  refine ⟨c.toOpenPartialHomeomorph, ?_, ?_, fun p hp hp' j ↦ ?_⟩
  · rwa [EtaleCoordinateChart.source_toOpenPartialHomeomorph]
  · rwa [EtaleCoordinateChart.source_toOpenPartialHomeomorph]
  · rw [EtaleCoordinateChart.source_toOpenPartialHomeomorph] at hp
    exact hc p hp hp' j

/-! ### Vectors on lines -/

section OnLine

open MMP.Topology Bundle

/-- `w` lies on the line with projection `P`, in chart coordinates. -/
private def OnLine (P : Fin 2 → Fin 2 → ℂ) (w : Fin 2 → ℂ) : Prop :=
  ∀ i j, P i i ≠ 0 → w j * P i i = P j i * w i

private lemma onLine_smul_lineProjection {r : Fin 2 → ℂ} (hr : r ≠ 0) (a : ℂ) :
    OnLine (lineProjection r) (a • r) := by
  intro i j hi
  have hri : r i ≠ 0 := fun h ↦ hi (by simp [lineProjection, h])
  have hd := lineProjection_div_apply hr hri j
  have hne : lineProjection r i i ≠ 0 := hi
  rw [div_eq_iff hne] at hd
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hd]
  field_simp

private lemma OnLine.eq_zero {P : Fin 2 → Fin 2 → ℂ} {w : Fin 2 → ℂ} (h : OnLine P w) {i : Fin 2}
    (hi : P i i ≠ 0) (hw : w i = 0) : w = 0 := by
  funext j
  have := h i j hi
  rw [hw, mul_zero] at this
  exact (mul_eq_zero.1 this).resolve_right hi

private lemma OnLine.eq_of_apply_eq {P : Fin 2 → Fin 2 → ℂ} {w w' : Fin 2 → ℂ} (h : OnLine P w)
    (h' : OnLine P w') {i : Fin 2} (hi : P i i ≠ 0) (hw : w i = w' i) : w = w' := by
  funext j
  have h1 := h i j hi
  have h2 := h' i j hi
  rw [hw, ← h2] at h1
  exact mul_right_cancel₀ hi h1

private lemma OnLine.lineProjection_eq {r w : Fin 2 → ℂ} (hr : r ≠ 0)
    (h : OnLine (lineProjection r) w)
    (hw : w ≠ 0) : lineProjection w = lineProjection r := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hr
  replace hi : r i ≠ 0 := hi
  have hii : lineProjection r i i ≠ 0 :=
    (lineProjection_apply_self_ne_zero_iff hr i).2 hi
  have hw' : w = (w i / r i) • r :=
    h.eq_of_apply_eq (onLine_smul_lineProjection hr _) hii (by
      simp only [Pi.smul_apply, smul_eq_mul]; field_simp)
  have hwi : w i ≠ 0 := fun h0 ↦ hw (h.eq_zero hii h0)
  rw [hw', lineProjection_smul hr (div_ne_zero hwi hi)]

private lemma onLine_of_mem {P : Fin 2 → Fin 2 → ℂ} (hP : P ∈ lineProjections 1) (a : ℂ) {i : Fin 2}
    (hi : P i i ≠ 0) : OnLine P (a • fun k ↦ P k i / P i i) := by
  obtain ⟨r, hr, rfl⟩ := hP
  have hri : r i ≠ 0 := fun h ↦ hi (by simp [lineProjection, h])
  have : (fun k ↦ lineProjection r k i / lineProjection r i i) = (r i)⁻¹ • r := by
    funext k
    rw [lineProjection_div_apply hr hri k, Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [this, smul_smul]
  exact onLine_smul_lineProjection hr _

/-- The point of the tautological bundle over `P` with vector `w`. -/
private def mkTE (P : lineProjections 1) (w : Fin 2 → ℂ) : TE := ⟨P, w (chartIndex P)⟩

private lemma localTriv_mkTE (j : Fin 2) (P : lineProjections 1) {w : Fin 2 → ℂ} (hw : OnLine P.1 w)
    (hj : P.1 j j ≠ 0) : ((tautologicalCore 1).localTriv j (mkTE P w)).2 = w j := by
  rw [localTriv_snd_tautological]
  change P.1 j (chartIndex P) / P.1 (chartIndex P) (chartIndex P) * w (chartIndex P) = w j
  have hi := chartIndex_diag_ne_zero P
  rw [div_mul_eq_mul_div, div_eq_iff hi, ← hw _ j hi]

private lemma tautologicalVector_mkTE (P : lineProjections 1) {w : Fin 2 → ℂ} (hw : OnLine P.1 w) :
    tautologicalVector 1 (mkTE P w) = w := by
  funext k
  change w (chartIndex P) * (P.1 k (chartIndex P) / P.1 (chartIndex P) (chartIndex P)) = w k
  have hi := chartIndex_diag_ne_zero P
  rw [mul_div_assoc', div_eq_iff hi, mul_comm, ← hw _ k hi]

private lemma onLine_tautologicalVector (p : TE) : OnLine p.1.1 (tautologicalVector 1 p) :=
  onLine_of_mem p.1.2 _ (chartIndex_diag_ne_zero p.1)

private lemma mkTE_tautologicalVector (p : TE) : mkTE p.1 (tautologicalVector 1 p) = p := by
  obtain ⟨P, c⟩ := p
  change (⟨P, tautologicalVector 1 ⟨P, c⟩ (chartIndex P)⟩ : TE) = ⟨P, c⟩
  rw [tautologicalVector_chartIndex]
  rfl

private lemma mkTE_mem_range_zeroSection_iff (P : lineProjections 1) {w : Fin 2 → ℂ}
    (hw : OnLine P.1 w) : mkTE P w ∈ range (zeroSection ℂ (TautologicalBundle 1)) ↔ w = 0 := by
  rw [mem_range_zeroSection_tautological_iff]
  change w (chartIndex P) = 0 ↔ _
  exact ⟨hw.eq_zero (chartIndex_diag_ne_zero P), fun h ↦ by rw [h]; rfl⟩

/-- A map into the tautological bundle given by a continuous line and a continuous vector on it
is continuous. -/
private lemma continuous_mkTE {T : Type*} [TopologicalSpace T] {P : T → lineProjections 1}
    {w : T → Fin 2 → ℂ} (hP : Continuous P) (hw : Continuous w) (hPw : ∀ t, OnLine (P t).1 (w t)) :
    Continuous fun t ↦ mkTE (P t) (w t) := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hP.continuousAt, ?_⟩
  change ContinuousAt (fun t ↦ ((tautologicalCore 1).localTriv (chartIndex (P t₀))
    (mkTE (P t) (w t))).2) t₀
  have hU : ∀ᶠ t in 𝓝 t₀, (P t).1 (chartIndex (P t₀)) (chartIndex (P t₀)) ≠ 0 :=
    hP.continuousAt.preimage_mem_nhds
      (((tautologicalCore 1).isOpen_baseSet (chartIndex (P t₀))).mem_nhds
        (chartIndex_diag_ne_zero (P t₀)))
  refine ((continuous_apply (chartIndex (P t₀))).comp hw).continuousAt.congr ?_
  filter_upwards [hU] with t ht
  exact (localTriv_mkTE _ (P t) (hPw t) ht).symm

/-- **The blowup near the exceptional curve is the tautological bundle**, abstractly: a proper
map `b` which is a bijection off the fibre over `y`, a chart `e` at `y`, and a continuous line
`ℓ(q)` through `e(b q)` which identifies the fibre over `y` with the lines, give the open
embedding `q ↦ (ℓ(q), e(b q))` of `b⁻¹(dom e)` into the tautological bundle. -/
private lemma isOpenEmbedding_mkTE {B Y : Type*} [TopologicalSpace B] [TopologicalSpace Y]
    {b : B → Y}
    (hb : IsProperMap b) (e : OpenPartialHomeomorph Y (Fin 2 → ℂ)) {y : Y} (hy : y ∈ e.source)
    (he : e y = 0) {line : B → lineProjections 1} (hline : ContinuousOn line (b ⁻¹' e.source))
    (hon : ∀ q ∈ b ⁻¹' e.source, OnLine (line q).1 (e (b q)))
    (hinj : ∀ q q', b q = b q' → b q ≠ y → q = q')
    (hsurj : ∀ p ∈ e.source, p ≠ y → ∃ q, b q = p)
    (hlinj : InjOn line (b ⁻¹' {y})) (hlsurj : ∀ P, ∃ q, b q = y ∧ line q = P) :
    IsOpenEmbedding (fun q : b ⁻¹' e.source ↦ mkTE (line q) (e (b q))) ∧
      range (zeroSection ℂ (TautologicalBundle 1)) ⊆
        range (fun q : b ⁻¹' e.source ↦ mkTE (line q) (e (b q))) ∧
      ∀ q : b ⁻¹' e.source, mkTE (line q) (e (b q)) ∈ range (zeroSection ℂ (TautologicalBundle 1))
        ↔ b q = y := by
  set N := b ⁻¹' e.source
  set Ψ : N → TE := fun q ↦ mkTE (line q) (e (b q))
  have he0 : ∀ q : N, e (b q) = 0 ↔ b q = y := fun q ↦
    ⟨fun h ↦ e.injOn q.2 hy (by rw [h, he]), fun h ↦ by rw [h, he]⟩
  have hzero : ∀ q : N, Ψ q ∈ range (zeroSection ℂ (TautologicalBundle 1)) ↔ b q = y := fun q ↦
    (mkTE_mem_range_zeroSection_iff _ (hon q q.2)).trans (he0 q)
  have hcb : Continuous fun q : N ↦ e (b q) :=
    e.continuousOn.comp_continuous (hb.continuous.comp continuous_subtype_val) fun q ↦ q.2
  have hcl : Continuous fun q : N ↦ line q := hline.restrict
  have hcont : Continuous Ψ := continuous_mkTE hcl hcb fun q ↦ hon q q.2
  have hΨinj : Function.Injective Ψ := by
    intro q q' h
    have h1 : line q = line q' := congrArg TotalSpace.proj h
    have h2 : e (b q) = e (b q') := by
      rw [← tautologicalVector_mkTE _ (hon q q.2), ← tautologicalVector_mkTE _ (hon q' q'.2)]
      exact congrArg _ h
    have h3 : b q = b q' := e.injOn q.2 q'.2 h2
    by_cases hq : b q = y
    · exact Subtype.ext (hlinj hq (show b q' = y from h3 ▸ hq) h1)
    · exact Subtype.ext (hinj q q' h3 hq)
  have hrange0 : range (zeroSection ℂ (TautologicalBundle 1)) ⊆ range Ψ := by
    rintro _ ⟨P, rfl⟩
    obtain ⟨q, hq, hqP⟩ := hlsurj P
    refine ⟨⟨q, show b q ∈ e.source from hq ▸ hy⟩, ?_⟩
    change mkTE (line q) (e (b q)) = _
    rw [hq, he, hqP]
    rfl
  have hrange : range Ψ = tautologicalVector 1 ⁻¹' e.target := by
    refine subset_antisymm ?_ fun p hp ↦ ?_
    · rintro _ ⟨q, rfl⟩
      change tautologicalVector 1 (mkTE (line q) (e (b q))) ∈ e.target
      rw [tautologicalVector_mkTE _ (hon q q.2)]
      exact e.map_source q.2
    · by_cases hw : tautologicalVector 1 p = 0
      · refine hrange0 ?_
        rw [← mkTE_tautologicalVector p, mkTE_mem_range_zeroSection_iff _
          (onLine_tautologicalVector p)]
        exact hw
      · have hs := e.map_target hp
        have hne : e.symm (tautologicalVector 1 p) ≠ y := fun h ↦ hw (by
          rw [← e.right_inv hp, h, he])
        obtain ⟨q, hq⟩ := hsurj _ hs hne
        have hqN : b q ∈ e.source := hq ▸ hs
        have hbq : e (b q) = tautologicalVector 1 p := by rw [hq, e.right_inv hp]
        refine ⟨⟨q, hqN⟩, ?_⟩
        change mkTE (line q) (e (b q)) = p
        have hl : line q = p.1 := by
          obtain ⟨r, hr, hrl⟩ := (line q).2
          obtain ⟨r', hr', hrl'⟩ := p.1.2
          have h1 := OnLine.lineProjection_eq hr (hrl ▸ hbq ▸ hon q hqN) hw
          have h2 := OnLine.lineProjection_eq hr' (hrl' ▸ onLine_tautologicalVector p) hw
          exact Subtype.ext (hrl ▸ hrl' ▸ h1.symm.trans h2)
        rw [hl, hbq, mkTE_tautologicalVector]
  let L := lineProjections 1
  let Φ' : N → L × e.target := fun q ↦ (line q, ⟨e (b q), e.map_source q.2⟩)
  have hΦ'c : Continuous Φ' := hcl.prodMk (hcb.subtype_mk _)
  have hΦ'inj : Function.Injective Φ' := by
    intro q q' h
    apply hΨinj
    change mkTE (line q) (e (b q)) = mkTE (line q') (e (b q'))
    have h1 : line q = line q' := congrArg Prod.fst h
    have h2 : e (b q) = e (b q') := congrArg (fun z ↦ (Prod.snd z).1) h
    rw [h1, h2]
  have heb : IsProperMap fun q : N ↦ (⟨e (b q), e.map_source q.2⟩ : e.target) :=
    e.toHomeomorphSourceTarget.isProperMap.comp (hb.restrictPreimage e.source)
  have hΦ'p : IsProperMap Φ' := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hΦ'c, fun K hK ↦ ?_⟩
    refine (heb.isCompact_preimage (hK.image continuous_snd)).of_isClosed_subset
      (hK.isClosed.preimage hΦ'c) fun q hq ↦ ⟨Φ' q, hq, rfl⟩
  have hΦ'e := IsClosedEmbedding.of_continuous_injective_isClosedMap hΦ'c hΦ'inj
    hΦ'p.isClosedMap
  let Θ : TE → L × (Fin 2 → ℂ) := fun p ↦ (p.1, tautologicalVector 1 p)
  have hΘ : Continuous Θ :=
    (FiberBundle.continuous_proj ℂ (TautologicalBundle 1)).prodMk continuous_tautologicalVector
  have hΘΨ : Θ ∘ Ψ = Prod.map id Subtype.val ∘ Φ' := by
    funext q
    change ((mkTE (line q) (e (b q))).1, tautologicalVector 1 (mkTE (line q) (e (b q)))) = _
    rw [tautologicalVector_mkTE _ (hon q q.2)]
    rfl
  have hemb : IsEmbedding Ψ := by
    refine ⟨IsInducing.of_comp hcont hΘ ?_, hΨinj⟩
    rw [hΘΨ]
    exact ((IsEmbedding.id.prodMap IsEmbedding.subtypeVal).comp hΦ'e.isEmbedding).isInducing
  refine ⟨⟨hemb, ?_⟩, hrange0, hzero⟩
  rw [hrange]
  exact e.open_target.preimage continuous_tautologicalVector

end OnLine

/-! ### Transition functions on the blowup charts -/

section ChartTransition

open MMP.Resolution MMP.Flips.ResolutionInputs MMP.Analytic.InvertibleModule

variable {X : Scheme.{0}} {I : X.IdealSheafData}

private lemma map_appLE_apply {X' Y' : Scheme.{0}} (f : X' ⟶ Y') {U : Y'.Opens} {V V' : X'.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V) (s : Γ(Y', U)) :
    (X'.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom s) =
      (f.appLE U V' (h.trans e)).hom s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private lemma inclΓ_chartGen_a (U : X.affineOpens) (a : I.ideal U) :
    inclΓ I (chartGen I U a).W (chartGen I U a).a = (blowUpChartMap I U a).hom a :=
  inclΓ_genOfPrincipal_a I _ _ _ _ _

/-- The generator of the exceptional ideal on the chart `U_k` of a chart datum. -/
private abbrev dataGen (c : BlowupChartData I) (hU : IsAffineOpen c.U) (k : Fin c.r) :
    Generator (exceptionalIdealModule I) :=
  chartGen I ⟨c.U, hU⟩ ⟨_, c.restrict_mem_ideal ⟨c.U, hU⟩ le_rfl k⟩

private lemma dataGen_W (c : BlowupChartData I) (hU : IsAffineOpen c.U) (k : Fin c.r) :
    (dataGen c hU k).W = c.chart k :=
  (chart_eq_blowUpChartOpen c hU k).symm

/-- **The transition function of the chart generators** `π^*x_k` and `π^*x_l` is `x_k / x_l`. -/
private lemma transitionSection_dataGen (c : BlowupChartData I) (hU : IsAffineOpen c.U)
    (k l : Fin c.r) :
    transitionSection (dataGen c hU k) (dataGen c hU l) =
      (blowUp I).presheaf.map (homOfLE (inf_le_right.trans (dataGen_W c hU l).le)).op
        (chartFraction c l k) := by
  refine transitionSection_eq_of_inclΓ I _ _ _ ?_
  rw [inclΓ_chartGen_a, inclΓ_chartGen_a]
  have hle : (dataGen c hU k).W ⊓ (dataGen c hU l).W ≤ c.chart l :=
    inf_le_right.trans (dataGen_W c hU l).le
  have hb : (dataGen c hU k).W ⊓ (dataGen c hU l).W ≤ blowUpToBase I ⁻¹ᵁ c.U :=
    hle.trans (c.chart_le l)
  have e1 : ∀ (j : Fin c.r) (W : (blowUp I).Opens) (hW : W ≤ blowUpToBase I ⁻¹ᵁ c.U)
      (h : (dataGen c hU k).W ⊓ (dataGen c hU l).W ≤ W),
      ((blowUp I).presheaf.map (homOfLE h).op).hom
        (((blowUpToBase I).appLE c.U W hW).hom
          ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x j))) =
        ((blowUpToBase I).appLE c.U _ hb).hom (c.x j) := by
    intro j W hW h
    rw [map_appLE_apply, map_refl_apply]
  have e2 : ∀ j : Fin c.r, ((blowUp I).presheaf.map (homOfLE hle).op).hom
      (c.chartPullback l (c.x j)) = ((blowUpToBase I).appLE c.U _ hb).hom (c.x j) :=
    fun j ↦ map_appLE_apply _ _ _ _
  refine (e1 k _ _ _).trans ?_
  refine ((e2 k).symm.trans ?_).trans (congrArg (_ * ·) (e1 l _ _ _).symm)
  rw [chartPullback_eq_chartFraction_mul c l k, map_mul, e2 l]

section Chern1

open MMP.Analytic.ComplexLineBundle MMP.Topology Bundle

variable [(blowUp I).Over (Spec (.of ℂ))]
  [SheafOfModules.IsInvertible (blowUp I).presheaf (blowUp I).ringCatSheaf.2 (blowUpTwist I 1)]

/-- The chart generator of `𝒪(1)` on `U_k`. -/
private abbrev twistGen (c : BlowupChartData I) (hU : IsAffineOpen c.U) (k : Fin c.r) :
    Generator (blowUpTwist I 1) :=
  genMap (twistOneIsoExceptionalIdealModule I).symm (dataGen c hU k)

private lemma top_le_of_mem_chart_twistGen (c : BlowupChartData I) (hU : IsAffineOpen c.U)
    {k : Fin c.r}
    {q : ComplexPoints (blowUp I ↘ Spec (.of ℂ))} (hq : q ∈ chart (twistGen c hU k).W) :
    ⊤ ≤ (homeomorphUnderlyingSpace q).toHom ⁻¹ᵁ c.chart k := by
  have h : q.hom ⁻¹ᵁ (dataGen c hU k).W = ⊤ := hq
  rw [dataGen_W] at h
  exact h.ge

/-- **The transition functions of `𝒪(1)`** on the blowup charts, at a point `q`, are the ratios
of the entries of the line of `q`. -/
private lemma transition_twistGen (c : BlowupChartData I) (hU : IsAffineOpen c.U) (k l : Fin c.r)
    {q : ComplexPoints (blowUp I ↘ Spec (.of ℂ))}
    (hq : q ∈ chart (twistGen c hU k).W ∩ chart (twistGen c hU l).W) :
    transition ((lineBundleCore (blowUpTwist I 1)).localTriv (twistGen c hU k))
        ((lineBundleCore (blowUpTwist I 1)).localTriv (twistGen c hU l)) q =
      chartLine c (homeomorphUnderlyingSpace q) k l /
        chartLine c (homeomorphUnderlyingSpace q) l l := by
  rw [transition_localTriv _ _ _ hq, transitionSection_map, transitionSection_dataGen]
  have hq' : q ∈ chart ((dataGen c hU k).W ⊓ (dataGen c hU l).W) := by rwa [chart_inf]
  change evalExt ((dataGen c hU k).W ⊓ (dataGen c hU l).W) _ q = _
  rw [evalExt_of_mem _ hq', eval_eq,
    MMP.UnderlyingSpace.eval_restrict,
    chartLine_div c hU (top_le_of_mem_chart_twistGen c hU hq.2) k]
  rfl

/-- A chart datum with two generators. -/
private abbrev data2 (U : X.Opens) (x : Fin 2 → Γ(X, U))
    (hf : ∀ (V : X.affineOpens) (h : V.1 ≤ U),
      I.ideal V = Ideal.span (Set.range fun i ↦ (X.presheaf.map (homOfLE h).op).hom (x i))) :
    BlowupChartData I :=
  ⟨U, 2, x, hf⟩

open Set in
/-- **`c₁(𝒪(1))` is minus the Chern class of the tautological bundle**, near the exceptional
curve, for a map `Ψ` to the tautological bundle recording the line of each point. -/
private theorem firstChernClass_add_eq_zero (U : X.Opens) (hU : IsAffineOpen U)
    (x : Fin 2 → Γ(X, U))
    (hf : ∀ (V : X.affineOpens) (h : V.1 ≤ U),
      I.ideal V = Ideal.span (Set.range fun i ↦ (X.presheaf.map (homOfLE h).op).hom (x i)))
    (N : Set (ComplexPoints (blowUp I ↘ Spec (.of ℂ))))
    (hN : ∀ q ∈ N, ∃ k, ⊤ ≤ (homeomorphUnderlyingSpace q).toHom ⁻¹ᵁ (data2 U x hf).chart k)
    (Ψ : TopCat.of N ⟶ TopCat.of TE)
    (hΨ : ∀ q : N, ((Ψ q).proj : Fin 2 → Fin 2 → ℂ) =
      chartLine (data2 U x hf) (homeomorphUnderlyingSpace q.1)) :
    (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
      (subspaceInclusion (analyticSpace _) N) (A' := univᶜ) (A := univᶜ)
      (fun _ hx ↦ (hx (mem_univ _)).elim) 2).hom
        (algebraicFirstChernClass (blowUpTwist I 1)) +
      (pb (Ψ ≫ bundleProj ℂ (TautologicalBundle 1)) 2).hom
        (firstChernClass (TautologicalBundle 1)) = 0 := by
  classical
  let c := data2 U x hf
  let Vk : Fin 2 → Set N := fun k ↦ {q | q.1 ∈ chart (twistGen c hU k).W}
  let kOf : Set N → Fin 2 := fun V ↦ if h : ∃ k, Vk k = V then h.choose else 0
  have hkOf : ∀ V ∈ range Vk, Vk (kOf V) = V := by
    rintro V ⟨k, rfl⟩
    have h : ∃ k', Vk k' = Vk k := ⟨k, rfl⟩
    simp only [kOf, dif_pos h]
    exact h.choose_spec
  have h𝒱 : ∀ V ∈ range Vk, IsOpen V := by
    rintro _ ⟨k, rfl⟩
    exact (isOpen_chart (twistGen c hU k).W).preimage continuous_subtype_val
  have hcov : ∀ q : N, ∃ V ∈ range Vk, q ∈ V := fun q ↦ by
    obtain ⟨k, hk⟩ := hN q.1 q.2
    refine ⟨Vk k, ⟨k, rfl⟩, ?_⟩
    change q.1.hom ⁻¹ᵁ (dataGen c hU k).W = ⊤
    rw [dataGen_W]
    exact top_le_iff.1 hk
  have he : IsFrameSystem (range Vk) (subspaceInclusion (analyticSpace _) N).hom
      (fun V ↦ (lineBundleCore (blowUpTwist I 1)).localTriv (twistGen c hU (kOf V))) :=
    fun V hV ↦ ⟨⟨_, rfl⟩, fun q hq ↦ by rw [← hkOf V hV] at hq; exact hq⟩
  have hmem : ∀ q : N, ∀ k, q ∈ Vk k → ((Ψ q).proj : Fin 2 → Fin 2 → ℂ) k k ≠ 0 := by
    intro q k hq
    rw [hΨ q]
    exact chartLine_apply_self_ne_zero c hU (top_le_of_mem_chart_twistGen c hU hq)
  have he₂ : IsFrameSystem (range Vk) (Ψ ≫ bundleProj ℂ (TautologicalBundle 1)).hom
      (fun V ↦ (tautologicalCore 1).localTriv (kOf V)) :=
    fun V hV ↦ ⟨⟨_, rfl⟩, fun q hq ↦ by
      rw [← hkOf V hV] at hq
      exact hmem q _ hq⟩
  refine map_firstChernClass_add_eq_zero h𝒱 hcov _ _ he he₂ ?_
  intro V hV W hW q hq
  obtain ⟨hqV, hqW⟩ := hq
  rw [← hkOf V hV] at hqV
  rw [← hkOf W hW] at hqW
  have h1 := transition_twistGen c hU (kOf V) (kOf W) (q := q.1) ⟨hqV, hqW⟩
  have : MemTrivializationAtlas ((tautologicalCore 1).localTriv (kOf V)) := ⟨⟨_, rfl⟩⟩
  have : MemTrivializationAtlas ((tautologicalCore 1).localTriv (kOf W)) := ⟨⟨_, rfl⟩⟩
  have hb : (Ψ q).proj ∈ ((tautologicalCore 1).localTriv (kOf V)).baseSet ∩
      ((tautologicalCore 1).localTriv (kOf W)).baseSet := ⟨hmem q _ hqV, hmem q _ hqW⟩
  have h2 : transition ((tautologicalCore 1).localTriv (kOf V))
      ((tautologicalCore 1).localTriv (kOf W)) (Ψ q).proj =
        ((Ψ q).proj : Fin 2 → Fin 2 → ℂ) (kOf W) (kOf V) /
          ((Ψ q).proj : Fin 2 → Fin 2 → ℂ) (kOf V) (kOf V) := by
    rw [transition_eq_coordChangeL hb,
      VectorBundleCore.localTriv_coordChange_eq _ _ _ hb, tautologicalCore_coordChange_apply,
      mul_one]
  change transition _ _ q.1 * transition _ _ (Ψ q).proj = 1
  rw [h1, h2, ← hΨ q]
  have hk := hmem q _ hqV
  have hl := hmem q _ hqW
  have key := lineProjections_mul_mul_eq (Ψ q).proj.2 (kOf V) (kOf W) (kOf W) (kOf V)
  field_simp
  rw [key, mul_comm]

end Chern1

end ChartTransition

section LocalModel

open MMP.Resolution MMP.Flips.ResolutionInputs MMP.Topology Bundle

/-- **The local model of a point blowup of a smooth surface**, for an ideal cutting out the point
and generated by local coordinates. -/
private theorem exists_isOpenEmbedding_tautologicalBundle_of_coords {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ))
    (hY : MMP.Mori.IsVariety ℂ sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (yc : ComplexPoints sY) (hyc : yc.toScheme = y)
    (hycu : ∀ p : ComplexPoints sY, p.toScheme = y → p = yc)
    (I : Y.IdealSheafData) (hI : (I.support : Set Y) = {y})
    {U : Y.Opens} (hU : IsAffineOpen U) (hyU : y ∈ U) {x : Fin 2 → Γ(Y, U)}
    (hx : IsLocalCoordinates sY U x)
    (hf : ∀ (W : Y.affineOpens) (h : W.1 ≤ U),
      I.ideal W = Ideal.span (Set.range fun i ↦ (Y.presheaf.map (homOfLE h).op).hom (x i)))
    [(blowUp I).Over (Spec (.of ℂ))]
    [SheafOfModules.IsInvertible (blowUp I).presheaf (blowUp I).ringCatSheaf.2 (blowUpTwist I 1)]
    (hB : blowUpToBase I ≫ sY = blowUp I ↘ Spec (.of ℂ)) :
    ∃ (V : Set (ComplexPoints sY)) (hV : IsOpen V) (hyV : yc ∈ V)
      (φ : TopCat.of V ⟶ TopCat.of (Fin 2 → ℂ)), IsOpenEmbedding φ ∧ φ ⟨yc, hyV⟩ = 0 ∧
      ∃ (N : Set (ComplexPoints (blowUp I ↘ Spec (.of ℂ)))), IsOpen N ∧
        analyticMap (blowUpToBase _) hB ⁻¹' {yc} ⊆ N ∧
        ∃ Ψ : TopCat.of N ⟶ TopCat.of TE, IsOpenEmbedding Ψ ∧
          Ψ ⁻¹' range (zeroSection ℂ (TautologicalBundle 1)) =
            subspaceInclusion (analyticSpace _) N ⁻¹' (analyticMap (blowUpToBase _) hB ⁻¹' {yc}) ∧
          range (zeroSection ℂ (TautologicalBundle 1)) ⊆ range Ψ ∧
          (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
            (subspaceInclusion (analyticSpace _) N) (A' := univᶜ) (A := univᶜ)
            (fun _ hx ↦ (hx (mem_univ _)).elim) 2).hom
              (algebraicFirstChernClass (blowUpTwist I 1)) +
            (pb (Ψ ≫ bundleProj ℂ (TautologicalBundle 1)) 2).hom
              (firstChernClass (TautologicalBundle 1)) = 0 := by
  classical
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : (blowUpToBase I).IsOver (Spec (.of ℂ)) := ⟨hB⟩
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hY.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsProper (blowUpToBase I) := isProper_blowUpToBase I
  let c : BlowupChartData I := data2 U x hf
  have hycU : yc ∈ chart U := mem_chart_iff.2 (hyc ▸ hyU)
  obtain ⟨e, hyce, hesrc, hev⟩ := exists_coordChart sY hY hYs hYd hx yc hycU
  have hsj : ∀ ℓ, Function.Surjective (chartPresentation c ℓ) ∧
      RingHom.ker (chartPresentation c ℓ) =
        Ideal.span (Set.range fun i : {i : Fin c.r // i ≠ ℓ} ↦
          MvPolynomial.C (c.x i.1) - MvPolynomial.X i * MvPolynomial.C (c.x ℓ)) :=
    fun ℓ ↦ chartPresentation_surjective_and_ker (c := c) sY hU x hx le_rfl (fun i ↦ rfl) ℓ
  let HY := homeomorphUnderlyingSpace (X := Y)
  let HB := homeomorphUnderlyingSpace (X := blowUp I)
  have htU : ⊤ ≤ (HY yc).toHom ⁻¹ᵁ U := (show yc.hom ⁻¹ᵁ U = ⊤ from hycU).ge
  have ht0 : ∀ i, MMP.UnderlyingSpace.eval (HY yc) htU (c.x i) = 0 := by
    intro i
    refine eval_eq_zero_of_mem_ideal I ⟨U, hU⟩ (HY yc) htU ?_ ?_
    · change yc.hom (IsLocalRing.closedPoint ℂ) ∈ (I.support : Set Y)
      rw [hI, Set.mem_singleton_iff, ← hyc]
      exact congrArg (fun z ↦ yc.hom z) (Subsingleton.elim _ _)
    · rw [hf ⟨U, hU⟩ le_rfl]
      exact Ideal.subset_span ⟨i, map_refl_apply _ _⟩
  have he0 : e yc = 0 := funext fun j ↦ (hev yc hyce hycU j).trans (ht0 j)
  set b := analyticMap (blowUpToBase I) hB with hbdef
  have hb : IsProperMap b :=
    HY.symm.isProperMap.comp ((MMP.UnderlyingSpace.isProperMap_map (K := ℂ)
      (blowUpToBase I)).comp HB.isProperMap)
  let line : ComplexPoints (blowUp I ↘ Spec (.of ℂ)) → lineProjections 1 := fun q ↦
    if h : chartLine c (HB q) ∈ lineProjections 1 then ⟨_, h⟩ else Classical.arbitrary _
  have hchart : ∀ q ∈ b ⁻¹' e.source, ∃ ℓ, ⊤ ≤ (HB q).toHom ⁻¹ᵁ c.chart ℓ := fun q hq ↦
    exists_top_le_preimage_chart c (t := HY (b q)) (show (b q).hom ⁻¹ᵁ U = ⊤ from hesrc hq).ge
      rfl
  have hline_eq : ∀ q ℓ, ⊤ ≤ (HB q).toHom ⁻¹ᵁ c.chart ℓ → (line q).1 = chartLine c (HB q) := by
    intro q ℓ hℓ
    have hm : chartLine c (HB q) ∈ lineProjections 1 := chartLine_mem c hU hℓ
    simp only [line]
    rw [dif_pos hm]
  have hline : ContinuousOn line (b ⁻¹' e.source) := by
    intro q hq
    obtain ⟨ℓ, hℓ⟩ := hchart q hq
    refine ContinuousAt.continuousWithinAt ?_
    rw [IsInducing.subtypeVal.continuousAt_iff]
    have hopen : IsOpen (HB ⁻¹' {p | ⊤ ≤ p.toHom ⁻¹ᵁ c.chart ℓ}) :=
      (MMP.UnderlyingSpace.isOpen_setOf_le_preimage _).preimage HB.continuous
    have hcl : ContinuousAt (fun q ↦ chartLine c (HB q)) q :=
      ((continuousOn_chartLine c hU ℓ).continuousAt
        ((MMP.UnderlyingSpace.isOpen_setOf_le_preimage _).mem_nhds hℓ)).comp
        HB.continuous.continuousAt
    refine hcl.congr ?_
    filter_upwards [hopen.mem_nhds hℓ] with q' hq'
    exact (hline_eq q' ℓ hq').symm
  have hon : ∀ q ∈ b ⁻¹' e.source, OnLine (line q).1 (e (b q)) := by
    intro q hq
    obtain ⟨ℓ, hℓ⟩ := hchart q hq
    have htq : ⊤ ≤ (HY (b q)).toHom ⁻¹ᵁ U := (show (b q).hom ⁻¹ᵁ U = ⊤ from hesrc hq).ge
    have hv : e (b q) = MMP.UnderlyingSpace.eval (HY (b q)) htq (c.x ℓ) •
        chartRatios c ℓ (HB q) hℓ := by
      funext j
      refine (hev (b q) hq (hesrc hq) j).trans ?_
      change MMP.UnderlyingSpace.eval (HY (b q)) htq (c.x j) = _
      have k1 : MMP.UnderlyingSpace.eval (HY (b q)) htq (c.x j) =
          MMP.UnderlyingSpace.eval (HB q) hℓ (c.chartPullback ℓ (c.x j)) :=
        (eval_chartPullback c hℓ rfl htq _).symm
      have k2 : MMP.UnderlyingSpace.eval (HY (b q)) htq (c.x ℓ) =
          MMP.UnderlyingSpace.eval (HB q) hℓ (c.chartPullback ℓ (c.x ℓ)) :=
        (eval_chartPullback c hℓ rfl htq _).symm
      rw [k1, Pi.smul_apply, smul_eq_mul, k2, chartPullback_eq_chartFraction_mul c ℓ j,
        ← MMP.UnderlyingSpace.evalRingHom_apply, map_mul,
        MMP.UnderlyingSpace.evalRingHom_apply,
        MMP.UnderlyingSpace.evalRingHom_apply, mul_comm]
      rfl
    rw [hline_eq q ℓ hℓ, chartLine_eq c hU hℓ, hv]
    exact onLine_smul_lineProjection (chartRatios_ne_zero c ℓ _ hℓ) _
  have hbij : ∀ (sB : blowUp I ⟶ Spec (.of ℂ)) (h : blowUpToBase I ≫ sY = sB),
      Function.Bijective ({p : ComplexPoints sY | p.toScheme ∉ (I.support : Set Y)}.restrictPreimage
        (realize (blowUpToBase I) h)) := by
    rintro _ rfl
    exact (ComplexPoints.isHomeomorph_restrictPreimage_realize_blowUpToBase sY I).bijective
  have hoff : ∀ p : ComplexPoints sY, p ≠ yc → p.toScheme ∉ (I.support : Set Y) := by
    intro p hp h
    rw [hI] at h
    exact hp (hycu p h)
  have hinj : ∀ q q', b q = b q' → b q ≠ yc → q = q' := by
    intro q q' h hne
    exact congrArg Subtype.val <| (hbij _ hB).1 (a₁ := ⟨q, hoff _ hne⟩)
      (a₂ := ⟨q', hoff _ (fun h' ↦ hne (h.trans h'))⟩) (Subtype.ext h)
  have hsurj : ∀ p ∈ e.source, p ≠ yc → ∃ q, b q = p := by
    intro p _ hne
    obtain ⟨⟨q, hq⟩, h⟩ := (hbij _ hB).2 ⟨p, hoff p hne⟩
    exact ⟨q, congrArg Subtype.val h⟩
  have hsurjc : ∀ ℓ, Function.Surjective (chartPresentation c ℓ) := fun ℓ ↦ (hsj ℓ).1
  have hkerc : ∀ ℓ, RingHom.ker (chartPresentation c ℓ) ≤
      Ideal.span (Set.range fun i : {i : Fin c.r // i ≠ ℓ} ↦
        MvPolynomial.C (c.x i.1) - MvPolynomial.X i * MvPolynomial.C (c.x ℓ)) :=
    fun ℓ ↦ (hsj ℓ).2.le
  have hEN : b ⁻¹' {yc} ⊆ b ⁻¹' e.source := fun q hq ↦
    show b q ∈ e.source from (Set.mem_singleton_iff.1 hq) ▸ hyce
  have hlinj : InjOn line (b ⁻¹' {yc}) := by
    intro q hq q' hq' h
    obtain ⟨ℓ, hℓ⟩ := hchart q (hEN hq)
    obtain ⟨ℓ', hℓ'⟩ := hchart q' (hEN hq')
    have h1 : chartLine c (HB q) = chartLine c (HB q') := by
      rw [← hline_eq q ℓ hℓ, ← hline_eq q' ℓ' hℓ', h]
    exact injOn_chartLine c hU hsurjc htU (show HB q ∈ _ from hq) (show HB q' ∈ _ from hq') h1
  have hlsurj : ∀ P, ∃ q, b q = yc ∧ line q = P := by
    intro P
    have hP : P.1 ∈ chartLine c '' (MMP.UnderlyingSpace.mapFun (blowUpToBase I) ⁻¹'
        {HY yc}) := by
      rw [image_chartLine c hU hsurjc hkerc htU ht0]
      exact P.2
    obtain ⟨p, hp, hpP⟩ := hP
    obtain ⟨ℓ, hℓ⟩ := exists_top_le_preimage_chart c htU hp
    refine ⟨HB.symm p, hp, Subtype.ext ?_⟩
    exact (hline_eq (HB.symm p) ℓ hℓ).trans hpP
  obtain ⟨hemb, hrange0, hzero⟩ := isOpenEmbedding_mkTE hb e hyce he0 hline hon hinj hsurj hlinj
    hlsurj
  refine ⟨e.source, e.open_source, hyce,
    TopCat.ofHom ⟨e.source.restrict e, e.continuousOn.restrict⟩,
    e.isOpenEmbedding_restrict, he0, b ⁻¹' e.source, e.open_source.preimage b.hom.continuous, hEN,
    TopCat.ofHom ⟨_, hemb.continuous⟩, hemb, ?_, hrange0, ?_⟩
  · exact Set.ext hzero
  · refine firstChernClass_add_eq_zero U hU x hf (b ⁻¹' e.source) hchart _ fun q ↦ ?_
    obtain ⟨ℓ, hℓ⟩ := hchart q q.2
    exact hline_eq q ℓ hℓ

end LocalModel

end Model

section Assembly

open Set Bundle MMP.Topology _root_.Topology

/-- **The local model of a point blowup of a smooth surface.** -/
private theorem exists_isOpenEmbedding_tautologicalBundle {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (hY : MMP.Mori.IsVariety ℂ sY)
    (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (yc : ComplexPoints sY) (hyc : yc.toScheme = y)
    (hycu : ∀ p : ComplexPoints sY, p.toScheme = y → p = yc)
    [(blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).Over (Spec (.of ℂ))]
    (hB : blowUpToBase _ ≫ sY =
      blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ↘ Spec (.of ℂ)) :
    ∃ (V : Set (ComplexPoints sY)) (hV : IsOpen V) (hyV : yc ∈ V)
      (φ : TopCat.of V ⟶ TopCat.of (Fin 2 → ℂ)), IsOpenEmbedding φ ∧ φ ⟨yc, hyV⟩ = 0 ∧
      ∃ (N : Set (ComplexPoints (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ↘
          Spec (.of ℂ)))), IsOpen N ∧ analyticMap (blowUpToBase _) hB ⁻¹' {yc} ⊆ N ∧
        ∃ Ψ : TopCat.of N ⟶ TopCat.of TE, IsOpenEmbedding Ψ ∧
          Ψ ⁻¹' range (zeroSection ℂ (TautologicalBundle 1)) =
            subspaceInclusion (analyticSpace _) N ⁻¹' (analyticMap (blowUpToBase _) hB ⁻¹' {yc}) ∧
          range (zeroSection ℂ (TautologicalBundle 1)) ⊆ range Ψ ∧
          (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
            (subspaceInclusion (analyticSpace _) N) (A' := univᶜ) (A := univᶜ)
            (fun _ hx ↦ (hx (mem_univ _)).elim) 2).hom
              (algebraicFirstChernClass
                (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) 1)) +
            (pb (Ψ ≫ bundleProj ℂ (TautologicalBundle 1)) 2).hom
              (firstChernClass (TautologicalBundle 1)) = 0 := by
  obtain ⟨U, hU, hyU, x, hx, hf⟩ := exists_coords sY hY hYs hYd hy yc hyc
  exact exists_isOpenEmbedding_tautologicalBundle_of_coords sY hY hYs hYd yc hyc hycu _
    (MMP.Threefold.Resolution.support_vanishingIdeal_singleton hy) hU hyU hx hf hB

/-- **One blowup at a closed point of a smooth surface.** -/
private theorem exists_leftInverse_pb_blowUpToBase_singleton {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsVariety ℂ sY)
    (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) (y : Y)
    (hy : IsClosed ({y} : Set Y))
    (sB : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ⟶ Spec (.of ℂ))
    (hsB : blowUpToBase _ ≫ sY = sB) :
    letI : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).Over (Spec (.of ℂ)) := ⟨sB⟩
    ∃ r : analyticSingularCohomology ℤ sB 2 →ₗ[ℤ] analyticSingularCohomology ℤ sY 2,
      (∀ x, r ((pb (analyticMap (blowUpToBase _) hsB) 2).hom x) = x) ∧
      LinearMap.ker r = Submodule.span ℤ {(algebraicFirstChernClass
        (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) 1))} ∧
      ∀ m : ℤ, LinearMap.toSpanSingleton ℤ _ (algebraicFirstChernClass
        (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) 1)) m = 0 → m = 0 := by
  subst hsB
  letI : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).Over (Spec (.of ℂ)) :=
    ⟨blowUpToBase _ ≫ sY⟩
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  obtain ⟨yc, hyc, hycu⟩ := exists_complexPoint sY y hy
  have hI : ((Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support : Set Y) = {y} :=
    MMP.Threefold.Resolution.support_vanishingIdeal_singleton hy
  obtain ⟨V, hV, hyV, φ, hφ, hφy, N, hN, hEN, Ψ, hΨ, hΨE, hrange, hc₁⟩ :=
    exists_isOpenEmbedding_tautologicalBundle sY hY hYs hYd hy yc hyc hycu rfl
  have hyclosed : IsClosed ({yc} : Set (analyticSpace sY)) := by
    have : ({yc} : Set (ComplexPoints sY)) = toScheme ⁻¹' {y} := by
      ext p
      simp only [mem_singleton_iff, mem_preimage]
      exact ⟨fun h ↦ h ▸ hyc, hycu p⟩
    rw [this]
    exact hy.preimage continuous_toScheme
  have hY2 := subsingleton_cohomologyWithSupports_of_isOpenEmbedding (Y := analyticSpace sY) yc
    hyclosed V hV hyV φ hφ hφy (k := 2) (by norm_num)
  have hY3 := subsingleton_cohomologyWithSupports_of_isOpenEmbedding (Y := analyticSpace sY) yc
    hyclosed V hV hyV φ hφ hφy (k := 3) (by norm_num)
  obtain ⟨u, hu, hnat, hfree⟩ := exists_generator_of_isOpenEmbedding
    (B := analyticSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ↘
      Spec (.of ℂ))) N _ Ψ hΨ hΨE hrange
  have hh : IsHomeomorph (fun p : ((analyticMap
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) rfl ⁻¹' {yc})ᶜ :
      Set (analyticSpace (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY))) ↦
      (⟨analyticMap (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) rfl p, p.2⟩ :
        (({yc} : Set (analyticSpace sY))ᶜ :
        Set (analyticSpace sY)))) := by
    have h := MMP.Analytic.ComplexPoints.isHomeomorph_restrictPreimage_realize_blowUpToBase sY
      (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
    have hS : {p : ComplexPoints sY | p.toScheme ∉
        ((Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support : Set Y)} =
          ({yc} : Set (ComplexPoints sY))ᶜ := by
      ext p
      simp only [mem_setOf_eq, hI, mem_singleton_iff, mem_compl_iff]
      exact ⟨fun h h' ↦ h (h' ▸ hyc), fun h h' ↦ h (hycu p h')⟩
    revert h
    generalize {p : ComplexPoints sY | p.toScheme ∉
        ((Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).support : Set Y)} = S at hS
    subst hS
    exact id
  have hξE := restrictCompl_firstChernClass_eq_zero sY _ hI yc hycu rfl
  have hξN : (pb (subspaceInclusion _ N) 2).hom (algebraicFirstChernClass
      (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) 1)) =
      (-1 : ℤ) • (cohomologyWithSupports.toCohomology ℤ (ModuleCat.of ℤ ℤ) _ _ (2 : ℕ)).hom u := by
    rw [neg_one_zsmul, hnat, pb_thomTwoAbs]
    exact eq_neg_of_add_eq_zero_left hc₁
  obtain ⟨r, hr, hker, hfr⟩ := exists_leftInverse_pb_of_isHomeomorph_compl
    (analyticMap (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) rfl) yc hyclosed hh
    hY2 hY3 N hN hEN u hu hfree _ hξE (-1) (by norm_num) hξN
  refine ⟨r, hr, hker, fun m hm ↦ hfr m ?_⟩
  rw [LinearMap.toSpanSingleton_apply] at hm
  exact (int_smul_eq_zsmul _ m _).symm.trans hm

end Assembly

section Chain

open Stacks.ResolutionOfSurfaces

variable {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)}

private lemma analyticMap_id (h : 𝟙 X ≫ sX = sX) : analyticMap (𝟙 X) h = 𝟙 _ := by
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  exact ComplexPoints.ext (by simp [analyticMap, realize])

private lemma pb_analyticMap_id_apply (h : 𝟙 X ≫ sX = sX) (j : ℤ) (x : H (analyticSpace sX) j) :
    (pb (analyticMap (𝟙 X) h) j).hom x = x := by
  rw [pb_congr (analyticMap_id h)]
  exact pb_id_apply j x

private lemma pb_analyticMap_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f ≫ sY = sX)
    (hg : g ≫ sZ = sY) (hfg : (f ≫ g) ≫ sZ = sX) (j : ℤ) (x : H (analyticSpace sZ) j) :
    (pb (analyticMap f hf) j).hom ((pb (analyticMap g hg) j).hom x) =
      (pb (analyticMap (f ≫ g) hfg) j).hom x := by
  rw [pb_pb_apply, pb_congr (ComplexPoints.analyticMap_comp f hf g hg)]

/-- Prepending the generator `ξ` of `ker rb` to the image under `bst` of a basis of `ker r₁` gives a
basis of `ker (r₁ ∘ₗ rb)`. -/
private lemma linearIndependent_cons_and_ker {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [AddCommGroup M₁]
    [AddCommGroup M₂] [Module ℤ M₀] [Module ℤ M₁] [Module ℤ M₂]
    (bst : M₁ →ₗ[ℤ] M₂) (rb : M₂ →ₗ[ℤ] M₁) (hrb : ∀ x, rb (bst x) = x) (ξ : M₂)
    (hker : LinearMap.ker rb = Submodule.span ℤ {ξ})
    (hξ : ∀ m : ℤ, LinearMap.toSpanSingleton ℤ M₂ ξ m = 0 → m = 0)
    (r₁ : M₁ →ₗ[ℤ] M₀) {n : ℕ} (e₁ : Fin n → M₁) (hli : LinearIndependent ℤ e₁)
    (hk : LinearMap.ker r₁ = Submodule.span ℤ (Set.range e₁)) :
    LinearIndependent ℤ (Fin.cons ξ (bst ∘ e₁) : Fin (n + 1) → M₂) ∧
      LinearMap.ker (r₁ ∘ₗ rb) = Submodule.span ℤ (Set.range (Fin.cons ξ (bst ∘ e₁))) := by
  have hinj : Function.Injective bst := fun a b h ↦ by rw [← hrb a, ← hrb b, h]
  have hξker : rb ξ = 0 := by
    rw [← LinearMap.mem_ker, hker]; exact Submodule.mem_span_singleton_self ξ
  have hrange : Set.range (Fin.cons ξ (bst ∘ e₁) : Fin (n + 1) → M₂) =
      insert ξ (bst '' Set.range e₁) := by
    rw [Fin.range_cons, Set.range_comp]
  refine ⟨?_, ?_⟩
  · refine LinearIndependent.finCons' ξ _ (hli.map' bst (LinearMap.ker_eq_bot.2 hinj))
      fun c y hymem hy ↦ ?_
    have hy' : y ∈ LinearMap.range bst := by
      rw [Set.range_comp, ← Submodule.map_span] at hymem
      obtain ⟨z, -, hz⟩ := hymem
      exact ⟨z, hz⟩
    obtain ⟨z, hz⟩ := hy'
    have h1 := congrArg rb hy
    rw [map_add, rb.map_smul c ξ, hξker, smul_zero, zero_add, ← hz, hrb, map_zero] at h1
    rw [← hz, h1, map_zero, add_zero] at hy
    exact hξ c hy
  · rw [hrange, Submodule.span_insert, ← Submodule.map_span]
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, hk] at hx
      have hx2 : x - bst (rb x) ∈ LinearMap.ker rb := by
        rw [LinearMap.mem_ker, map_sub, hrb, sub_self]
      rw [hker] at hx2
      have : x = (x - bst (rb x)) + bst (rb x) := by abel
      rw [this]
      exact Submodule.add_mem_sup hx2 (Submodule.mem_map_of_mem hx)
    · rw [sup_le_iff]
      refine ⟨?_, ?_⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        change r₁ (rb ξ) = 0
        rw [hξker, map_zero]
      · rintro _ ⟨z, hz, rfl⟩
        rw [LinearMap.mem_ker, LinearMap.comp_apply, hrb, ← LinearMap.mem_ker, hk]
        exact hz

/-- The stages of a chain of point blowups of a smooth surface are smooth surfaces. -/
private theorem isVariety_and_isSmoothScheme_of_pointBlowupChain {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of ℂ)) (hZ : MMP.Mori.IsVariety ℂ sZ)
    (hZs : MMP.Mori.IsSmoothScheme sZ) (hZd : topologicalKrullDim Z = 2) {Y : Scheme.{0}}
    {h : Y ⟶ Z} (hc : PointBlowupChain Z Set.univ Y h) :
    MMP.Mori.IsVariety ℂ (h ≫ sZ) ∧ MMP.Mori.IsSmoothScheme (h ≫ sZ) ∧
      topologicalKrullDim Y = 2 := by
  induction hc with
  | refl => simpa using ⟨hZ, hZs, hZd⟩
  | step hh w hw hwT ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have : LocallyOfFiniteType (_ ≫ sZ) := h1.toLocallyOfFiniteType
    have : IsIntegral _ := h1.toIsIntegral
    refine ⟨?_, ?_, ?_⟩
    · rw [Category.assoc]
      exact MMP.Threefold.Resolution.isVariety_blowUp_singleton h1 h3 hw
    · rw [Category.assoc]
      exact MMP.Threefold.Resolution.isSmoothScheme_blowUp_singleton h1 h2 h3 hw
    · exact MMP.Threefold.Resolution.topologicalKrullDim_blowUp _ _
        (MMP.Threefold.Resolution.isSmoothBlowup_vanishingIdeal_singleton _ h2 hw)
        (MMP.Threefold.Resolution.isIrreducible_support_vanishingIdeal_singleton hw)
        (MMP.Threefold.Resolution.one_le_codimension_vanishingIdeal_singleton h3 hw) h3

/-- Along a point-blowup chain `h : Y ⟶ Z` of smooth surfaces, `pb h` has an integral left inverse
whose kernel has a basis of total transforms of exceptional classes. -/
private theorem exists_leftInverse_pb_of_pointBlowupChain {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of ℂ)) (hZ : MMP.Mori.IsVariety ℂ sZ)
    (hZs : MMP.Mori.IsSmoothScheme sZ) (hZd : topologicalKrullDim Z = 2) {Y : Scheme.{0}}
    {h : Y ⟶ Z} (hc : PointBlowupChain Z Set.univ Y h) (sY : Y ⟶ Spec (.of ℂ))
    (hh : h ≫ sZ = sY) :
    ∃ r : analyticSingularCohomology ℤ sY 2 →ₗ[ℤ] analyticSingularCohomology ℤ sZ 2,
      (∀ x, r ((pb (analyticMap h hh) 2).hom x) = x) ∧
      ∃ (n : ℕ) (e : Fin n → analyticSingularCohomology ℤ sY 2),
        LinearIndependent ℤ e ∧ LinearMap.ker r = Submodule.span ℤ (Set.range e) ∧
        ∀ i, ∃ (Y' : Scheme.{0}) (h' : Y' ⟶ Z) (_ : PointBlowupChain Z Set.univ Y' h') (y : Y')
          (hy : IsClosed ({y} : Set Y'))
          (g : Y ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
          (_ : PointBlowupChain (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
            Set.univ Y g)
          (hfac : g ≫ blowUpToBase _ ≫ h' = h),
          letI : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).Over
              (Spec (.of ℂ)) := ⟨blowUpToBase _ ≫ h' ≫ sZ⟩
          e i = (pb (analyticMap g (sY := blowUpToBase _ ≫ h' ≫ sZ)
              (by rw [← hh, ← hfac]; simp only [Category.assoc])) 2).hom
              (algebraicFirstChernClass
                (blowUpTwist (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) 1)) := by
  induction hc with
  | refl =>
    obtain rfl : sY = sZ := by rw [← hh, Category.id_comp]
    refine ⟨LinearMap.id, fun x ↦ pb_analyticMap_id_apply _ 2 x, 0, Fin.elim0,
      linearIndependent_empty_type, ?_, fun i ↦ i.elim0⟩
    rw [LinearMap.ker_id]
    simp
  | @step Y₁ h₁ hh₁ w hw hwT ih =>
    obtain ⟨r₁, hr₁, n, e₁, hli, hk, hwit⟩ := ih (h₁ ≫ sZ) rfl
    obtain ⟨hv, hs, hd⟩ := isVariety_and_isSmoothScheme_of_pointBlowupChain sZ hZ hZs hZd hh₁
    obtain rfl : sY = blowUpToBase _ ≫ h₁ ≫ sZ := by rw [← hh, Category.assoc]
    obtain ⟨rb, hrb, hkerb, hξ⟩ :=
      exists_leftInverse_pb_blowUpToBase_singleton (h₁ ≫ sZ) hv hs hd w hw _ rfl
    let bst := (pb (analyticMap (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      ⟨{w}, hw⟩)) (rfl : blowUpToBase _ ≫ h₁ ≫ sZ = _)) 2).hom
    obtain ⟨hli₂, hk₂⟩ := linearIndependent_cons_and_ker bst rb hrb _ hkerb hξ r₁ e₁ hli hk
    refine ⟨r₁ ∘ₗ rb, fun x ↦ ?_, n + 1, _, hli₂, hk₂, fun i ↦ ?_⟩
    · simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [← pb_congr (ComplexPoints.analyticMap_comp _ rfl _ rfl), ← pb_pb_apply, hrb, hr₁]
    · refine Fin.cases ?_ (fun j ↦ ?_) i
      · refine ⟨Y₁, h₁, hh₁, w, hw, 𝟙 _, PointBlowupChain.refl, Category.id_comp _, ?_⟩
        exact (pb_analyticMap_id_apply _ 2 _).symm
      · obtain ⟨Y', h', hc', y, hy, g, hg, hfac, he⟩ := hwit j
        refine ⟨Y', h', hc', y, hy, blowUpToBase _ ≫ g, hg.step w hw trivial, ?_, ?_⟩
        · rw [Category.assoc, hfac]
        · change bst (e₁ j) = _
          rw [he]
          exact pb_analyticMap_comp_apply _ _ _ _ _ 2 _

end Chain

/-- **Integral second cohomology under a proper birational morphism of smooth surfaces.**
Let `π : W ⟶ Z` be a proper birational morphism over `ℂ` of smooth projective surfaces. There is
a `ℤ`-linear retraction `r : H²(W; ℤ) → H²(Z; ℤ)` of the pullback `π^*`, and `ker r` is free with
a basis `e : Fin n → H²(W; ℤ)` each of whose members is the total transform in `W` of the class
`c₁(𝒪(1)) = -[E]` of the exceptional curve of one step `Bl_y Y ⟶ Y` of a factorization of `π`
into blowups at closed points. -/
@[mmp "lem_fourfold_surface_blowup_integral_second_cohomology"]
public theorem exists_leftInverse_pullback_singularCohomology_two {W Z : Scheme.{0}}
    {sW : W ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsProjectiveVariety ℂ sW] [IsProjectiveVariety ℂ sZ]
    (hWs : MMP.Mori.IsSmoothScheme sW) (hWd : topologicalKrullDim W = 2)
    (hZs : MMP.Mori.IsSmoothScheme sZ) (hZd : topologicalKrullDim Z = 2)
    (π : W ⟶ Z) (hπ : π ≫ sZ = sW) [IsProper π] (hb : IsBirational π) :
    ∃ r : analyticSingularCohomology ℤ sW 2 →ₗ[ℤ] analyticSingularCohomology ℤ sZ 2,
      (∀ x, r ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) (analyticMap π hπ)
        (A' := Set.univᶜ) (A := Set.univᶜ) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2).hom x) =
          x) ∧
      ∃ (n : ℕ) (e : Fin n → analyticSingularCohomology ℤ sW 2),
        LinearIndependent ℤ e ∧ LinearMap.ker r = Submodule.span ℤ (Set.range e) ∧
        ∀ i, ∃ (Y : Scheme.{0}) (h : Y ⟶ Z) (_ : Stacks.ResolutionOfSurfaces.PointBlowupChain
            Z Set.univ Y h) (y : Y) (hy : IsClosed ({y} : Set Y))
          (g : W ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
          (_ : Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups
            (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) Set.univ W g)
          (hfac : g ≫ blowUpToBase _ ≫ h = π),
          letI : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).Over
              (Spec (.of ℂ)) := ⟨blowUpToBase _ ≫ h ≫ sZ⟩
          e i = (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ)
            (analyticMap g (sY := blowUpToBase _ ≫ h ≫ sZ)
              (by rw [← hπ, ← hfac]; simp only [Category.assoc]))
            (A' := Set.univᶜ) (A := Set.univᶜ) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2).hom
              (algebraicFirstChernClass (blowUpTwist _ 1)) := by
  have hZ := (‹IsProjectiveVariety ℂ sZ›).toIsVariety
  obtain ⟨Y, f, hc, eW, he⟩ := MMP.Resolution.Bridges.factorsAsPointBlowups_of_isSmoothSurface ℂ
    hZ hZs hZd (‹IsProjectiveVariety ℂ sW›).toIsVariety hWs hWd π hπ hb
  obtain ⟨rY, hrY, n, eY, hli, hk, hwit⟩ :=
    exists_leftInverse_pb_of_pointBlowupChain sZ hZ hZs hZd hc (f ≫ sZ) rfl
  have hsW : eW.hom ≫ f ≫ sZ = sW := by rw [← Category.assoc, he, hπ]
  have hsY : eW.inv ≫ sW = f ≫ sZ := by rw [← hsW, ← Category.assoc, eW.inv_hom_id,
    Category.id_comp]
  let E : analyticSingularCohomology ℤ (f ≫ sZ) 2 ≃ₗ[ℤ] analyticSingularCohomology ℤ sW 2 :=
    { (pb (analyticMap eW.hom hsW) 2).hom with
      invFun := (pb (analyticMap eW.inv hsY) 2).hom
      left_inv := fun x ↦ by
        change (pb (analyticMap eW.inv hsY) 2).hom ((pb (analyticMap eW.hom hsW) 2).hom x) = x
        rw [pb_analyticMap_comp_apply _ _ _ _ (by rw [Category.assoc, hsW, hsY])]
        rw [pb_congr (show analyticMap (eW.inv ≫ eW.hom) _ = analyticMap (𝟙 _) (by simp) by
          congr 1; exact eW.inv_hom_id)]
        exact pb_analyticMap_id_apply _ 2 x
      right_inv := fun x ↦ by
        change (pb (analyticMap eW.hom hsW) 2).hom ((pb (analyticMap eW.inv hsY) 2).hom x) = x
        rw [pb_analyticMap_comp_apply _ _ _ _ (by rw [Category.assoc, hsY, hsW])]
        rw [pb_congr (show analyticMap (eW.hom ≫ eW.inv) _ = analyticMap (𝟙 _) (by simp) by
          congr 1; exact eW.hom_inv_id)]
        exact pb_analyticMap_id_apply _ 2 x }
  have hE : ∀ x, E x = (pb (analyticMap eW.hom hsW) 2).hom x := fun _ ↦ rfl
  refine ⟨rY ∘ₗ E.symm.toLinearMap, fun x ↦ ?_, n, E ∘ eY, hli.map' E.toLinearMap
    (LinearMap.ker_eq_bot.2 E.injective), ?_, fun i ↦ ?_⟩
  · have : (pb (analyticMap π hπ) 2).hom x = E ((pb (analyticMap f rfl) 2).hom x) := by
      rw [hE, pb_analyticMap_comp_apply _ _ _ _ (by rw [Category.assoc, hsW])]
      exact congrArg (fun m ↦ (pb m 2).hom x) (by congr 1; exact he.symm)
    change rY (E.symm ((pb (analyticMap π hπ) 2).hom x)) = x
    rw [this, LinearEquiv.symm_apply_apply, hrY]
  · rw [LinearMap.ker_comp, hk, Set.range_comp]
    rw [show ⇑E '' Set.range eY = (E.toLinearMap : _ →ₗ[ℤ] _) '' Set.range eY from rfl,
      Submodule.span_image, Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm]
  · obtain ⟨Y', h', hc', y, hy, g, hg, hfac, heq⟩ := hwit i
    refine ⟨Y', h', hc', y, hy, eW.hom ≫ g, ⟨Y, g, hg, eW, rfl⟩, ?_, ?_⟩
    · rw [Category.assoc, hfac, he]
    · change E (eY i) = _
      rw [heq, hE]
      exact pb_analyticMap_comp_apply _ _ _ _ _ 2 _

end MMP.Fourfold
