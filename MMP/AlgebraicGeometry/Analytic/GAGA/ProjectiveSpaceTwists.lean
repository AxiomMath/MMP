module

public import MMP.AlgebraicGeometry.Analytic.GAGA.DolbeaultVanishing
public import MMP.AlgebraicGeometry.Analytic.GAGA.TwistsCechComparison

/-!
# Cohomology of the twisting sheaves on complex projective space, algebraic and analytic

Let `P = ℙᴺ_ℂ = Proj S`, `S = ℂ[x₀, …, x_N]`, and let `𝒪(k)` be its `k`-th twisting sheaf. For
every `q ≥ 0` the comparison map `c^q : H^q(P, 𝒪(k)) → H^q(P^an, 𝒪(k)^an)` is an isomorphism.
The global sections of `𝒪(k)` on `P` and of `𝒪(k)^an` on `P^an` are both the homogeneous
polynomials of degree `k` (zero for `k < 0`), through the canonical maps. Both cohomology groups
vanish for `0 < q < N`, for `q > N`, and for `q = N` when `k ≥ -N`.

The proof computes both sides by ordered Čech complexes on the standard affine cover
`Uᵢ = {xᵢ ≠ 0}` and its analytification, and compares Laurent polynomials with convergent
Laurent series monomial by monomial.

## Main results

* `MMP.Analytic.isIso_comparisonMap_projectiveSpace_twistingSheaf`: the comparison maps for
  `𝒪(k)` on `ℙᴺ_ℂ` are isomorphisms, the global sections on both sides are `S_k`, and the stated
  vanishing.

## Implementation notes

`S_k` is the degree-`0` part of the shifted graded module `S(k)`, i.e. `S_k` for `k ≥ 0` and `0`
for `k < 0`; the map to `Γ(P, 𝒪(k))` is the canonical one sending a homogeneous element to the
section it defines, and the map to `Γ(P^an, 𝒪(k)^an)` is its composite with the unit
`𝒪(k) → (α_P)_* 𝒪(k)^an` of analytification. The identification `H⁰ = Γ` is general and is not
repeated here.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*], §§12–13
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace MMP.Analytic

open MMP.Analytic.ProjectiveTwists

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

section Acyclicity

open TopologicalSpace Analytification Stacks.ProjectiveSpace.Cohomology

attribute [local instance] locallyOfFiniteType_sP

variable {N : ℕ} (k : ℤ) {S : Finset (Fin (N + 1))}

/-- **`𝒪(k)^an` has no higher cohomology on `W(S)`.** -/
private theorem isZero_sheafCohomology_WS (hS : S.Nonempty) (q : ℤ) (hq : 0 < q) :
    IsZero ((sheafCohomology ((TopologicalSpace.Opens.toTopCat (space (sP N))).obj (WS N S)) q).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' (WS N S))).obj
        ((SheafOfModules.toSheaf _).obj (Lan N k)))) := by
  have hj := S.min'_mem hS
  classical
  let F : Fin N → Set ℂ := fun i => if (S.min' hS).succAbove i ∈ S then
    {z | (0 : ENNReal) < edist z 0 ∧ edist z 0 < ⊤} else Metric.eball 0 ⊤
  have hF : ∀ i, (∃ a b c d : ℝ, F i = Set.Ioo a b ×ℂ Set.Ioo c d) ∨
      (∃ (c : ℂ) (R : ENNReal), F i = Metric.eball c R) ∨
      (∃ (c : ℂ) (r R : ENNReal), F i = {z | r < edist z c ∧ edist z c < R}) := by
    intro i
    by_cases hi : (S.min' hS).succAbove i ∈ S
    · exact Or.inr (Or.inr ⟨0, 0, ⊤, by simp [F, hi]⟩)
    · exact Or.inr (Or.inl ⟨0, ⊤, by simp [F, hi]⟩)
  have hDF : ((prodDomain S (S.min' hS) :
      TopologicalSpace.Opens (TopCat.of (EuclideanSpace ℂ (Fin N)))) : Set (EuclideanSpace ℂ (Fin N))) =
      {z | ∀ i, z i ∈ F i} := by
    ext z
    simp only [prodDomain, TopologicalSpace.Opens.coe_mk, Set.mem_preimage, lDom, sdisc,
      Set.mem_setOf_eq, not_not, F]
    refine forall_congr' fun i => ?_
    by_cases hi : (S.min' hS).succAbove i ∈ S
    · simp [hi, edist_pos]
    · simp [hi, Metric.eball]
  have hD := (isZero_sheafCohomology_holomorphic_of_isProductDomain N).1
    (prodDomain S (S.min' hS)) F hF hDF q hq
  haveI := CartanCompactBlocks.isIso_sheafCohomologyPullback (gS hj)
    (isOpenEmbedding_gS hj) (surjective_gS hj)
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0}
      (Opens.inclusion' (prodDomain S (S.min' hS)))).obj holAbSheaf) q
  exact (hD.of_iso (asIso (sheafCohomologyPullback (gS hj) _ q)).symm).of_iso
    ((sheafCohomology _ q).mapIso (anIso k hj))

/-! ### Comparing the two ordered Čech complexes

Both cohomologies are computed by ordered Čech complexes on the standard cover and its
analytification (`MMP.Analytic.exists_orderedCechComplex_homologyIso_sheafCohomology`), and the
comparison map is induced by the cochain map `chi`. The algebraic complex is the Laurent
polynomial complex (`algComplexIso`), the analytic one the convergent Laurent complex, and the
inclusion of the first into the second is a homotopy equivalence. -/

variable (N)

/-- `𝒪(k)^an` has no higher cohomology on the intersections of the analytified cover. -/
private lemma anSheaf_acyclic (p : ℕ) (J : CechCochains.OrdIndex (I := ULift.{0} (Fin (N + 1))) p)
    (q : ℤ) (hq : 0 < q) :
    IsZero ((sheafCohomology ((Opens.toTopCat _).obj (CechCochains.inter (anCover N) J.1)) q).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0}
        (Opens.inclusion' (CechCochains.inter (anCover N) J.1))).obj (anSheaf N k))) := by
  rw [anInter_eq N J]
  exact isZero_sheafCohomology_WS k (image_univ_nonempty _) q hq

end Acyclicity

section Comparison

open TopologicalSpace Stacks.ProjectiveCohomology Stacks.ProjectiveSpace.Cohomology

variable (N : ℕ) (k : ℤ)

/-- **GAGA for `𝒪(k)`.** For every `q`, the comparison map
`H^q(ℙᴺ, 𝒪(k)) → H^q((ℙᴺ)^an, 𝒪(k)^an)` is an isomorphism. -/
private theorem isIso_comparisonMap_twistingSheaf (q : ℕ) :
    IsIso (comparisonMap (sP N)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k) q) := by
  obtain ⟨e, -, -, hpull⟩ := exists_orderedCechComplex_homologyIso_sheafCohomology.{0}
  have hU : (⨆ i, algCover N i) = ⊤ := iSup_basicOpenXAtUniverse_eq_top (R := ℂ) N
  have hU' : (⨆ i, anCover N i) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (Analytification.toSchemeHom (sP N)) x ∈ (⨆ i, algCover N i) := hU ▸ trivial
    rw [Opens.mem_iSup] at hx ⊢
    exact hx
  have key := hpull (ULift.{0} (Fin (N + 1))) _ _ (Analytification.toSchemeHom (sP N))
    (algCover N) (anCover N) hU hU' (fun _ => le_rfl) (algSheaf N k) (anSheaf N k)
    (algSheaf_acyclic N k) (anSheaf_acyclic N k)
    (analytifyModuleι (sP N)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k))
    (chi N k) (fun _ _ _ _ => rfl) q
  haveI := isIso_homologyMap_chi N k q
  have hc : comparisonMap (sP N)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k) q =
      (e _ _ (algCover N) (algSheaf N k) hU (algSheaf_acyclic N k) q).inv ≫
        HomologicalComplex.homologyMap (chi N k) q ≫
          (e _ _ (anCover N) (anSheaf N k) hU' (anSheaf_acyclic N k) q).hom := by
    rw [← key, Iso.inv_hom_id_assoc]
    rfl
  rw [hc]
  infer_instance

end Comparison

/-- The canonical map from the degree-`k` homogeneous polynomials to `Γ((ℙᴺ)^an, 𝒪(k)^an)`,
`degreeZeroToGlobalSections` followed by the analytification unit, is bijective. -/
private theorem bijective_analytify_degreeZeroToGlobalSections (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    Function.Bijective (fun s =>
      (analytifyModuleUnit (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ N)
        (ProjectiveSpectrum.Proj.twistingSheaf
          (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k)).val.app (op ⊤)
        (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections
          (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)
          (ProjectiveSpectrum.Proj.twistGrading
            (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k) s)) := by
  have hc := isIso_comparisonMap_twistingSheaf N k 0
  have hΓ := isIso_globalSections_homEquiv _
    (Analytification.toSchemeHom (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ N)) _
    (analytifyModuleι (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ N)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k)) hc
  erw [analytifyModuleι, Equiv.apply_symm_apply] at hΓ
  have hb := @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ hΓ
  exact hb.comp (bijective_degreeZeroToGlobalSections N hN k)

/-- **GAGA for the twisting sheaves of `ℙᴺ_ℂ`.** For `N ≥ 1`, `P = ℙᴺ_ℂ` and `k ∈ ℤ`: the
comparison maps `c^q : H^q(P, 𝒪(k)) → H^q(P^an, 𝒪(k)^an)` are isomorphisms; the canonical map
from the degree-`k` homogeneous polynomials to `Γ(P, 𝒪(k))`, and its composite with the
analytification unit into `Γ(P^an, 𝒪(k)^an)`, are bijective; and both `H^q` vanish for
`0 < q < N`, for `N < q`, and for `q = N` when `-N ≤ k`. -/
@[mmp "lem_mmp_gaga_projective_space_twists"]
public theorem isIso_comparisonMap_projectiveSpace_twistingSheaf (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    (∀ q : ℕ, IsIso (comparisonMap (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ N)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k) q)) ∧
    Function.Bijective (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)
      (ProjectiveSpectrum.Proj.twistGrading
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k)) ∧
    Function.Bijective (fun s =>
      (analytifyModuleUnit (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ N)
        (ProjectiveSpectrum.Proj.twistingSheaf
          (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k)).val.app (op ⊤)
        (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections
          (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)
          (ProjectiveSpectrum.Proj.twistGrading
            (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k) s)) ∧
    ∀ q : ℕ, (0 < q ∧ q < N) ∨ N < q ∨ (q = N ∧ -(N : ℤ) ≤ k) →
      IsZero ((sheafCohomology _ q).obj ((SheafOfModules.toSheaf _).obj
        (ProjectiveSpectrum.Proj.twistingSheaf
          (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k))) ∧
      IsZero ((sheafCohomology _ q).obj ((SheafOfModules.toSheaf _).obj
        ((analytifyModule (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ N)).obj
          (ProjectiveSpectrum.Proj.twistingSheaf
            (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k)))) := by
  refine ⟨isIso_comparisonMap_twistingSheaf N k, bijective_degreeZeroToGlobalSections N hN k,
    bijective_analytify_degreeZeroToGlobalSections N hN k, fun q hq => ?_⟩
  have ha := isZero_sheafCohomology_twistingSheaf N hN k q hq
  have := isIso_comparisonMap_twistingSheaf N k q
  exact ⟨ha, ha.of_iso (asIso (comparisonMap _ _ q)).symm⟩

end MMP.Analytic
