module

public import MMP.AlgebraicGeometry.Analytic.GAGA.TwistsLaurentModel
public import MMP.Analysis.Complex.Coherent.CartanBlocksGluing
public import MMP.AlgebraicGeometry.Cohomology.SheafHModules
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CanonicalTwist

/-!
# GAGA for the twisting sheaves of `ℙᴺ_ℂ`: Čech comparison and global sections

We describe the sections of `𝒪(k)^an` over `W(S)` as convergent Laurent series and identify
`𝒪(k)^an` on `W(S)` with the holomorphic sheaf of a product domain. We compare the ordered Čech
complexes of `𝒪(k)` and `𝒪(k)^an` on the standard cover with the polynomial and convergent
Laurent cochain complexes, describe global sections through the Godement resolution in degree
`0`, and compute the global sections and the vanishing of the algebraic cohomology of `𝒪(k)`.

## Main definitions

* `lCoeffAddEquiv`: the sections of `𝒪(k)^an` over `W(S)` as convergent homogeneous Laurent families.
* `anIso`: `𝒪(k)^an` on `W(S)` is the holomorphic sheaf of the product domain `prodDomain`.
* `chi`: the cochain map between the ordered Čech complexes of `𝒪(k)` and `𝒪(k)^an`.

## Main results

* `isIso_homologyMap_chi`: `chi` induces isomorphisms on cohomology.
* `isIso_globalSections_homEquiv`: an isomorphism on `H⁰` induces an isomorphism on global
  sections of the adjunct map.
* `bijective_degreeZeroToGlobalSections`: the degree-`k` homogeneous polynomials are the global
  sections of `𝒪(k)`.
* `isZero_sheafCohomology_twistingSheaf`: vanishing of `H^q(ℙᴺ_ℂ, 𝒪(k))`.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*], §§12–13
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MMP.Analytic

namespace MMP.Analytic.ProjectiveTwists

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- Projective space `ℙᴺ_ℂ = Proj ℂ[x₀, …, x_N]`. -/
local notation3 (prettyPrint := false) "ℙ[" N "]" =>
  AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)

/-- The twisting sheaf `𝒪(k)` of `ℙᴺ_ℂ`. -/
local notation3 (prettyPrint := false) "𝒪ℙ[" N ", " k "]" =>
  (show (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)).Modules
    from ProjectiveSpectrum.Proj.twistingSheaf
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k)

section AnalyticModel

open Filter Topology TopologicalSpace MMP.Analytic.ComplexPoints MMP.Analytic.Analytification
open scoped ChangeOfRings

section ESsec

open Stacks.ProjectiveSpace.Cohomology Stacks.AlgebraicGeometry.ProjPolyChart
  AlgebraicGeometry.ProjectiveSpectrum.Proj MMP.UnderlyingSpace

attribute [local instance] locallyOfFiniteType_sP

variable {N : ℕ} {k : ℤ} (j : Fin (N + 1))

/-- The section `secOf N k j W hW s` of the structure sheaf representing `s` in the trivialization
of `𝒪(k)^an` on `U_j` is additive in `s`. -/
lemma secOf_add (W : TopologicalSpace.Opens (space (sP N)))
    (hW : W ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s t : (Lan N k).val.obj (op W)) :
    secOf N k j W hW (s + t) = secOf N k j W hW s + secOf N k j W hW t :=
  secOf_eq N k j W hW _ _ (by rw [add_smul, secOf_smul, secOf_smul]; rfl)

/-- A section of `𝒪(k)^an` over an open of `U_j^an` is determined by its trivialization
`secOf N k j W hW`. -/
lemma secOf_injective (W : TopologicalSpace.Opens (space (sP N)))
    (hW : W ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U) :
    Function.Injective (secOf N k j W hW) := by
  intro s t h
  have h1 := secOf_smul N k j W hW s
  rw [h, secOf_smul] at h1
  exact h1.symm

/-- The coordinate function `gfun N k j hj s` of a section over `W(S)` is additive in the section
on `lDom (sdisc S j)`. -/
lemma gfun_add {S : Finset (Fin (N + 1))} (hj : j ∈ S) (s t : (Lan N k).val.obj (op (WS N S)))
    (w : Fin N → ℂ) (hw : w ∈ lDom (sdisc S j)) :
    gfun N k j hj (s + t) w = gfun N k j hj s w + gfun N k j hj t w := by
  refine (gfun_apply k j hj _ w hw).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· + ·) (gfun_apply k j hj s w hw) (gfun_apply k j hj t w hw)).symm
  refine (congrArg (fun f => secVal f (ptW j hj w hw) (stdChart N j) (mem_chart_of_WS j hj _))
    (secOf_add j _ (WS_le j hj) s t)).trans ?_
  exact secVal_add _ _ _ _ _

/-- The affine coordinates in the chart `U_j` of a point of `W(S)` lie in `lDom (sdisc S j)`. -/
lemma coords_mem_lDom {S : Finset (Fin (N + 1))} (hj : j ∈ S) (x : WS N S) :
    (stdChart N j).coords ⟨x.1, mem_chart_of_WS j hj x⟩ ∈ lDom (sdisc S j) := by
  intro i hi
  simp only [sdisc, Set.mem_setOf_eq, not_not] at hi
  have := (toScheme_mem_chartDenom_iff j S ⟨x.1, mem_chart_of_WS j hj x⟩).1 x.2 _ hi
  rwa [hcoord_succAbove] at this

/-- The point `ptW` of `W(S)` with the affine coordinates of `x ∈ W(S)` in the chart `U_j` is `x`.
-/
lemma ptW_coords {S : Finset (Fin (N + 1))} (hj : j ∈ S) (x : WS N S) :
    ptW j hj ((stdChart N j).coords ⟨x.1, mem_chart_of_WS j hj x⟩) (coords_mem_lDom j hj x) = x :=
  Subtype.ext (congrArg (fun p : chart (sX := sP N) (stdChart N j).U => p.1)
    ((coordsEquiv j).symm_apply_apply ⟨x.1, mem_chart_of_WS j hj x⟩))

/-- The Laurent coefficients of a section of `𝒪(k)^an` over `W(S)`. -/
noncomputable def lCoeff {S : Finset (Fin (N + 1))} (hS : S.Nonempty)
    (s : (Lan N k).val.obj (op (WS N S))) : (Fin (N + 1) → ℤ) → ℂ :=
  (exists_laurentSections k (S.min'_mem hS) _
    (differentiableOn_gfun k (S.min' hS) (S.min'_mem hS) s)).choose

/-- The Laurent coefficients of a section over `W(S)` lie in `laurentSections N k S`. -/
lemma lCoeff_mem {S : Finset (Fin (N + 1))} (hS : S.Nonempty)
    (s : (Lan N k).val.obj (op (WS N S))) :
    lCoeff hS s ∈ laurentSections N k S :=
  (exists_laurentSections k (S.min'_mem hS) _
    (differentiableOn_gfun k (S.min' hS) (S.min'_mem hS) s)).choose_spec.1

/-- For `j ∈ S` and `z` with `z i ≠ 0` for `i ∈ S`, the Laurent series
`∑ β, lCoeff hS s β * mono z β` sums to `z j ^ k * gfun N k j hj s (dehom j z)`. -/
lemma lCoeff_hasSum {S : Finset (Fin (N + 1))} (hS : S.Nonempty)
    (s : (Lan N k).val.obj (op (WS N S))) (j : Fin (N + 1)) (hj : j ∈ S) (z : Fin (N + 1) → ℂ)
    (hz : ∀ i ∈ S, z i ≠ 0) :
    HasSum (fun β => lCoeff hS s β * mono z β) (z j ^ k * gfun N k j hj s (dehom j z)) := by
  rw [← gfun_change k (S.min' hS) j (S.min'_mem hS) hj s hz]
  exact (exists_laurentSections k (S.min'_mem hS) _
    (differentiableOn_gfun k (S.min' hS) (S.min'_mem hS) s)).choose_spec.2 z hz

/-- The Laurent coefficients of a section are the unique family in `laurentSections N k S` whose
Laurent series sums to `z j ^ k * gfun N k j hj s (dehom j z)` wherever `z i ≠ 0` for `i ∈ S`. -/
lemma lCoeff_unique {S : Finset (Fin (N + 1))} (hS : S.Nonempty)
    (s : (Lan N k).val.obj (op (WS N S))) (j : Fin (N + 1)) (hj : j ∈ S)
    {c : (Fin (N + 1) → ℤ) → ℂ} (hc : c ∈ laurentSections N k S)
    (h : ∀ z : Fin (N + 1) → ℂ, (∀ i ∈ S, z i ≠ 0) →
      HasSum (fun β => c β * mono z β) (z j ^ k * gfun N k j hj s (dehom j z))) :
    lCoeff hS s = c :=
  eq_of_hasSum_laurentSections k (lCoeff_mem hS s) hc _ (lCoeff_hasSum hS s j hj) h

/-- Two sections over `W(S)` with the same Laurent coefficients have the same coordinate function
`gfun` in every chart `U_j` with `j ∈ S`. -/
lemma gfun_eq_of_lCoeff_eq {S : Finset (Fin (N + 1))} (hS : S.Nonempty)
    {s t : (Lan N k).val.obj (op (WS N S))} (h : lCoeff hS s = lCoeff hS t)
    (j : Fin (N + 1)) (hj : j ∈ S) (w : Fin N → ℂ) (hw : w ∈ lDom (sdisc S j)) :
    gfun N k j hj s w = gfun N k j hj t w := by
  have h1 := lCoeff_hasSum hS s j hj (insertOne j w) (insertNth_ne_zero hj hw)
  have h2 := lCoeff_hasSum hS t j hj (insertOne j w) (insertNth_ne_zero hj hw)
  rw [h] at h1
  simpa [insertOne, dehom_insertNth] using h1.unique h2

/-- A section of `𝒪(k)^an` over `W(S)` is determined by its Laurent coefficients. -/
lemma lCoeff_injective {S : Finset (Fin (N + 1))} (hS : S.Nonempty) :
    Function.Injective (lCoeff (k := k) hS) := by
  intro s t hc
  have hj0 := S.min'_mem hS
  have hv : ∀ x : WS N S, secVal (secOf N k (S.min' hS) (WS N S) (WS_le _ hj0) s) x
      (stdChart N (S.min' hS)) (mem_chart_of_WS _ hj0 x) =
      secVal (secOf N k (S.min' hS) (WS N S) (WS_le _ hj0) t) x
      (stdChart N (S.min' hS)) (mem_chart_of_WS _ hj0 x) := by
    intro x
    have := gfun_eq_of_lCoeff_eq hS hc _ hj0 _ (coords_mem_lDom _ hj0 x)
    rwa [gfun_apply k _ hj0 s _ (coords_mem_lDom _ hj0 x),
      gfun_apply k _ hj0 t _ (coords_mem_lDom _ hj0 x), ptW_coords] at this
  exact secOf_injective _ _ _
    (eq_of_secVal_eq (stdChart_ideal N (S.min' hS)) (mem_chart_of_WS _ hj0) _ _ hv)

/-- Every family in `laurentSections N k S` is the family of Laurent coefficients of a section of
`𝒪(k)^an` over `W(S)`. -/
lemma exists_lCoeff_eq_of_mem {S : Finset (Fin (N + 1))} (hS : S.Nonempty) {c : (Fin (N + 1) → ℤ) → ℂ}
    (hc : c ∈ laurentSections N k S) : ∃ s : (Lan N k).val.obj (op (WS N S)), lCoeff hS s = c := by
  have hj0 := S.min'_mem hS
  obtain ⟨hg, hsum⟩ := differentiableOn_of_laurentSections k hj0 hc
  obtain ⟨f, hf⟩ := exists_sections_secVal_eq (c := stdChart N (S.min' hS))
    (mem_chart_of_WS _ hj0) (isOpen_lDom (sdisc S (S.min' hS))) _ hg (coords_mem_lDom _ hj0)
  let f' : (ringCatSheaf (sP N)).obj.obj (op (WS N S)) := f
  refine ⟨f' • (Lan N k).val.map (homOfLE (WS_le _ hj0)).op (uSec N k (S.min' hS)), ?_⟩
  refine lCoeff_unique hS _ _ hj0 hc fun z hz => ?_
  have heq : gfun N k (S.min' hS) hj0
      (f' • (Lan N k).val.map (homOfLE (WS_le _ hj0)).op (uSec N k (S.min' hS)))
      (dehom (S.min' hS) z) =
      ∑' γ, dehomCoeff k (S.min' hS) c γ * ∏ i, dehom (S.min' hS) z i ^ γ i := by
    refine (gfun_apply k _ hj0 _ _ (dehom_mem hj0 hz)).trans ?_
    refine (congrArg (fun f => secVal f (ptW _ hj0 (dehom (S.min' hS) z) (dehom_mem hj0 hz))
      (stdChart N (S.min' hS)) (mem_chart_of_WS _ hj0 _))
      (secOf_eq N k (S.min' hS) (WS N S) (WS_le _ hj0)
        (f' • (Lan N k).val.map (homOfLE (WS_le _ hj0)).op (uSec N k (S.min' hS))) f' rfl)).trans ?_
    have := hf (ptW _ hj0 (dehom (S.min' hS) z) (dehom_mem hj0 hz))
    rwa [coords_ptW] at this
  rw [heq]
  exact hsum z hz

/-- **The analytic sections of `𝒪(k)` over `W(S)` are the convergent homogeneous Laurent
families.** -/
noncomputable def lCoeffAddEquiv {S : Finset (Fin (N + 1))} (hS : S.Nonempty) :
    (Lan N k).val.obj (op (WS N S)) ≃+ laurentSections N k S :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun s => (⟨lCoeff hS s, lCoeff_mem hS s⟩ : laurentSections N k S))
      fun s t => by
        apply Subtype.ext
        refine lCoeff_unique hS (s + t) (S.min' hS) (S.min'_mem hS)
          (add_mem (lCoeff_mem hS s) (lCoeff_mem hS t)) fun z hz => ?_
        rw [gfun_add _ _ s t _ (dehom_mem (S.min'_mem hS) hz), mul_add]
        exact (lCoeff_hasSum hS s _ _ z hz).add (lCoeff_hasSum hS t _ _ z hz) |>.congr_fun
          fun β => by simp [add_mul])
    ⟨fun s t h => lCoeff_injective hS (congrArg Subtype.val h),
      fun c => (exists_lCoeff_eq_of_mem hS c.2).imp fun s hs => Subtype.ext hs⟩

/-- The family underlying `lCoeffAddEquiv hS s` is `lCoeff hS s`. -/
@[simp]
lemma coe_lCoeffAddEquiv {S : Finset (Fin (N + 1))} (hS : S.Nonempty) (s : (Lan N k).val.obj (op (WS N S))) :
    ((lCoeffAddEquiv hS s : laurentSections N k S) : (Fin (N + 1) → ℤ) → ℂ) = lCoeff hS s := rfl

/-- The families `laurentSections N k S` are monotone in `S`. -/
lemma laurentSections_mono {S S' : Finset (Fin (N + 1))} (h : S ⊆ S') :
    laurentSections N k S ≤ laurentSections N k S' := fun c hc =>
  ⟨fun β hβ => laurentMonomials_mono (Finset.coe_subset.2 h) (hc.1 β hβ),
    fun z hz => hc.2 z fun i hi => hz i (h hi)⟩

/-- Restriction is invisible on Laurent coefficients. -/
lemma lCoeff_restrict {S S' : Finset (Fin (N + 1))} (hS : S.Nonempty) (hS' : S'.Nonempty)
    (h : S ⊆ S') (s : (Lan N k).val.obj (op (WS N S))) :
    lCoeff hS' ((Lan N k).val.map (homOfLE (WS_mono h)).op s) = lCoeff hS s := by
  refine lCoeff_unique hS' _ (S.min' hS) (h (S.min'_mem hS))
    (laurentSections_mono h (lCoeff_mem hS s)) fun z hz => ?_
  have hzS : ∀ i ∈ S, z i ≠ 0 := fun i hi => hz i (h hi)
  rw [gfun_restrict k (S.min' hS) (S.min'_mem hS) h s _ (dehom_mem (h (S.min'_mem hS)) hz)]
  exact lCoeff_hasSum hS s _ (S.min'_mem hS) z hzS

/-- For `z j ≠ 0` and `∑ i, β i = k`, the monomial `mono z β` is `z j ^ k` times the monomial of
exponent `β` evaluated at `insertOne j (dehom j z)`. -/
lemma mono_insertOne_dehom {z : Fin (N + 1) → ℂ} (hzj : z j ≠ 0) (β : Fin (N + 1) → ℤ)
    (hβ : ∑ i, β i = k) :
    z j ^ k * ∏ i, insertOne j (dehom j z) i ^ β i = mono z β := by
  simp only [insertOne_dehom j hzj, div_zpow, Finset.prod_div_distrib,
    prod_zpow_eq_zpow_sum' _ _ hzj, hβ, mono]
  field_simp

/-- **The analytification of an algebraic section has its Laurent polynomial as coefficients.** -/
lemma lCoeff_unitHom {S : Finset (Fin (N + 1))} (hS : S.Nonempty)
    (c : (𝒪ℙ[N, k]).val.obj
      (op (Proj.basicOpen (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)
        (chartDenom ℂ N S)))) :
    lCoeff hS (unitHom (sX := sP N) (L := 𝒪ℙ[N, k]) _ c) =
      ⇑((chartSectionsAddEquivTwistChart ℂ N k S hS c : twistChart ℂ N k (↑S : Set (Fin (N + 1)))) :
        (Fin (N + 1) → ℤ) →₀ ℂ) := by
  set P := chartSectionsAddEquivTwistChart ℂ N k S hS c
  have hPmem : ⇑(P : (Fin (N + 1) → ℤ) →₀ ℂ) ∈ laurentSections N k S := by
    refine ⟨fun β hβ => (Finsupp.mem_supported _ _).1 P.2 (Finsupp.mem_support_iff.2 hβ),
      fun z _ => summable_of_ne_finset_zero (s := (P : (Fin (N + 1) → ℤ) →₀ ℂ).support)
        fun β hβ => by simp [Finsupp.notMem_support_iff.1 hβ]⟩
  refine lCoeff_unique hS _ (S.min' hS) (S.min'_mem hS) hPmem fun z hz => ?_
  set j := S.min' hS
  have hj := S.min'_mem hS
  rw [gfun_unitHom k j hj c (dehom j z) (dehom_mem hj hz)]
  have hL : ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)
      (chartDenom_mem_homogeneousSubmodule N S) (Finset.card_pos.2 ⟨j, hj⟩) k c :
        LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ))) =
      (twistChartEquivTwistSections ℂ N k S P :
        LocalizedModule.Away (chartDenom ℂ N S) (MvPolynomial (Fin (N + 1)) ℂ)) := by
    have hP : twistChartEquivTwistSections ℂ N k S P = chartSectionsAddEquiv ℂ N k S hS c :=
      (twistChartEquivTwistSections ℂ N k S).apply_symm_apply _
    exact (congrArg Subtype.val hP).symm
  rw [hL, evQ_twistChart, Finsupp.sum, Finset.mul_sum]
  have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional (Fin (N + 1) → ℤ))
    (s := (P : (Fin (N + 1) → ℤ) →₀ ℂ).support)
    (f := fun β => (P : (Fin (N + 1) → ℤ) →₀ ℂ) β * mono z β)
    fun β hβ => by simp [Finsupp.notMem_support_iff.1 hβ]
  convert hfin using 1
  refine Finset.sum_congr rfl fun β hβ => ?_
  have hβ' := (Finsupp.mem_supported _ _).1 P.2 hβ
  rw [← mono_insertOne_dehom j (hz j hj) β hβ'.1]
  ring

end ESsec

section Acyc

open Stacks.ProjectiveSpace.Cohomology AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Manifold ContDiff

attribute [local instance] locallyOfFiniteType_sP

/-- A complex-differentiable function on an open subset of `ℂⁿ` is smooth there. -/
lemma contDiffOn_of_differentiableOn' {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f Ω) : ContDiffOn ℂ ∞ f Ω := by
  have h := ((MMP.SeveralComplex.cauchy_osgood_laurent.{0, 0} ℂ).2.2.1 n Ω f hΩ hf.continuousOn
    fun ζ hζ j => ?_).2.1
  · exact h.contDiffOn hΩ.uniqueDiffOn
  · have hd : DifferentiableAt ℂ f (Function.update ζ j (ζ j)) := by
      rw [Function.update_eq_self]; exact hf.differentiableAt (hΩ.mem_nhds hζ)
    have hu : DifferentiableAt ℂ (fun w : ℂ => Function.update ζ j w) (ζ j) := by
      rw [differentiableAt_pi]
      intro i
      by_cases hij : i = j
      · subst hij; simpa using differentiableAt_id
      · simp [Function.update_of_ne hij]
    exact hd.comp (ζ j) hu

/-- A function smooth on an open `D` of `EuclideanSpace ℂ (Fin n)` is smooth on `D` as a map of
manifolds. -/
lemma contMDiff_of_contDiffOn {n : ℕ} (D : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n)))
    (ψ : EuclideanSpace ℂ (Fin n) → ℂ) (h : ContDiffOn ℂ ∞ ψ D) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (fun x : D => ψ x) :=
  fun x => contMDiffAt_subtype_iff.2 (contMDiffAt_iff_contDiffAt.2
    (h.contDiffAt (D.isOpen.mem_nhds x.2)))

/-- A function whose restriction to an open `D` of `EuclideanSpace ℂ (Fin n)` is smooth as a map of
manifolds is complex-differentiable on `D`. -/
lemma differentiableOn_of_contMDiff {n : ℕ} (D : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n)))
    (ψ : EuclideanSpace ℂ (Fin n) → ℂ)
    (h : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (fun x : D => ψ x)) :
    DifferentiableOn ℂ ψ D :=
  fun x hx => ((contMDiffAt_iff_contDiffAt.1
    (contMDiffAt_subtype_iff.1 (h ⟨x, hx⟩))).differentiableAt (by simp)).differentiableWithinAt

variable {N : ℕ} (k : ℤ) (j : Fin (N + 1))

/-- The affine coordinates of a point of `U_j`. -/
noncomputable def coordsN (y : chart (sX := sP N) (stdChart N j).U) : Fin N → ℂ :=
  (stdChart N j).coords y

/-- The affine coordinates of the points of an open of `U_j^an`. -/
def imgSet (V : TopologicalSpace.Opens (space (sP N))) : Set (Fin N → ℂ) :=
  coordsN j '' {y | y.1 ∈ V}

/-- The set `imgSet j V` of affine coordinates of the points of `V` in the chart `U_j` is open. -/
lemma isOpen_imgSet (V : TopologicalSpace.Opens (space (sP N))) : IsOpen (imgSet j V) :=
  (isOpenEmbedding_coords (stdChart N j) (stdChart_ideal N j)).isOpenMap _
    (V.isOpen.preimage continuous_subtype_val)

/-- The point of `U_j` with affine coordinates in `imgSet j V` lies in `V`. -/
lemma mem_of_mem_imgSet {V : TopologicalSpace.Opens (space (sP N))} {p : Fin N → ℂ}
    (hp : p ∈ imgSet j V) : ((coordsEquiv j).symm p).1 ∈ V := by
  obtain ⟨y, hy, rfl⟩ := hp
  have : (coordsEquiv j).symm (coordsN j y) = y := (coordsEquiv j).symm_apply_apply y
  rwa [this]

/-- `secOf` commutes with restriction to a smaller open. -/
lemma secOf_res {V₁ V₂ : TopologicalSpace.Opens (space (sP N))} (h : V₂ ≤ V₁)
    (hV₁ : V₁ ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s : (Lan N k).val.obj (op V₁)) :
    secOf N k j V₂ (h.trans hV₁) ((Lan N k).val.map (homOfLE h).op s) =
      (ringCatSheaf (sP N)).obj.map (homOfLE h).op (secOf N k j V₁ hV₁ s) := by
  refine secOf_eq N k j _ _ _ _ ?_
  conv_rhs => rw [← secOf_smul N k j V₁ hV₁ s]
  exact (map_smul_unit (L := 𝒪ℙ[N, k])
    (t := tSec N k j) hV₁ h _).symm

/-- The holomorphic function of the affine coordinates of `U_j` representing a section of
`𝒪(k)^an` over an open of `U_j^an`. -/
noncomputable def holOf (V : TopologicalSpace.Opens (space (sP N)))
    (hV : V ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s : (Lan N k).val.obj (op V)) : (Fin N → ℂ) → ℂ :=
  holFun (c := stdChart N j) (fun x : V => mem_chart_iff.2 (hV x.2)) (secOf N k j V hV s)

/-- At the affine coordinates of a point `x ∈ V`, the function `holOf k j V hV s` takes the value
of `secOf N k j V hV s` at `x`. -/
lemma holOf_coords (V : TopologicalSpace.Opens (space (sP N)))
    (hV : V ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s : (Lan N k).val.obj (op V)) (x : V) :
    holOf k j V hV s ((stdChart N j).coords ⟨x.1, mem_chart_iff.2 (hV x.2)⟩) =
      secVal (secOf N k j V hV s) x (stdChart N j) (mem_chart_iff.2 (hV x.2)) :=
  holFun_coords (stdChart_ideal N j) _ _ x

/-- The function `holOf k j V hV s` is holomorphic on `imgSet j V`. -/
lemma differentiableOn_holOf (V : TopologicalSpace.Opens (space (sP N)))
    (hV : V ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s : (Lan N k).val.obj (op V)) :
    DifferentiableOn ℂ (holOf k j V hV s) (imgSet j V) := by
  rintro _ ⟨y, hy, rfl⟩
  exact (differentiableAt_holFun (stdChart_ideal N j) (fun x : V => mem_chart_iff.2 (hV x.2))
    (secOf N k j V hV s) ⟨y.1, hy⟩).differentiableWithinAt

/-- On `imgSet j V₂`, the function `holOf` of the restriction of `s` to `V₂` is that of `s`. -/
lemma holOf_res {V₁ V₂ : TopologicalSpace.Opens (space (sP N))} (h : V₂ ≤ V₁)
    (hV₁ : V₁ ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s : (Lan N k).val.obj (op V₁)) {p : Fin N → ℂ} (hp : p ∈ imgSet j V₂) :
    holOf k j V₂ (h.trans hV₁) ((Lan N k).val.map (homOfLE h).op s) p = holOf k j V₁ hV₁ s p := by
  obtain ⟨y, hy, rfl⟩ := hp
  have e1 := holOf_coords k j V₂ (h.trans hV₁) ((Lan N k).val.map (homOfLE h).op s) ⟨y.1, hy⟩
  have e2 := holOf_coords k j V₁ hV₁ s ⟨y.1, h hy⟩
  refine e1.trans (Eq.trans ?_ e2.symm)
  exact congrArg (fun f => secVal f ⟨y.1, hy⟩ (stdChart N j) (mem_chart_iff.2 (hV₁ (h hy))))
    (secOf_res k j h hV₁ s)

/-- `holOf` is additive in the section on `imgSet j V`. -/
lemma holOf_add (V : TopologicalSpace.Opens (space (sP N)))
    (hV : V ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (s t : (Lan N k).val.obj (op V)) {p : Fin N → ℂ} (hp : p ∈ imgSet j V) :
    holOf k j V hV (s + t) p = holOf k j V hV s p + holOf k j V hV t p := by
  obtain ⟨y, hy, rfl⟩ := hp
  have e := holOf_coords k j V hV (s + t) ⟨y.1, hy⟩
  have e1 := holOf_coords k j V hV s ⟨y.1, hy⟩
  have e2 := holOf_coords k j V hV t ⟨y.1, hy⟩
  refine e.trans (Eq.trans ?_ (congrArg₂ (· + ·) e1 e2).symm)
  refine (congrArg (fun f => secVal f ⟨y.1, hy⟩ (stdChart N j) (mem_chart_iff.2 (hV hy)))
    (secOf_add j V hV s t)).trans ?_
  exact secVal_add _ _ _ _ _

end Acyc

section AcycE

open Stacks.ProjectiveSpace.Cohomology AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Manifold ContDiff

attribute [local instance] locallyOfFiniteType_sP

variable {N : ℕ} (k : ℤ) (j : Fin (N + 1))

/-- **Sections of `𝒪(k)^an` over an open of `U_j^an` are holomorphic functions of the affine
coordinates.** -/
noncomputable def toEHom (V : TopologicalSpace.Opens (space (sP N)))
    (hV : V ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (Y : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin N)))
    (hY : ∀ e : EuclideanSpace ℂ (Fin N), e ∈ Y ↔ EuclideanSpace.equiv (Fin N) ℂ e ∈ imgSet j V) :
    (Lan N k).val.obj (op V) →+ 𝒪[N, EuclideanSpace ℂ (Fin N)].presheaf.obj (op Y) :=
  AddMonoidHom.mk' (fun s => ⟨fun e => holOf k j V hV s (EuclideanSpace.equiv (Fin N) ℂ e), by
    refine contMDiff_of_contDiffOn Y
      (fun e => holOf k j V hV s (EuclideanSpace.equiv (Fin N) ℂ e)) ?_
    refine (contDiffOn_of_differentiableOn' (isOpen_imgSet j V)
      (differentiableOn_holOf k j V hV s)).comp
      (EuclideanSpace.equiv (Fin N) ℂ).contDiff.contDiffOn fun e he => (hY e).1 he⟩)
    fun s t => ContMDiffMap.ext fun e => holOf_add k j V hV s t ((hY e.1).1 e.2)

end AcycE

section AcycE2

open Stacks.ProjectiveSpace.Cohomology AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Manifold ContDiff

attribute [local instance] locallyOfFiniteType_sP

variable {N : ℕ} (k : ℤ) (j : Fin (N + 1))

/-- A section of `𝒪(k)^an` over an open of `U_j^an` is determined by its holomorphic function
`toEHom` of the affine coordinates. -/
lemma toEHom_injective (V : TopologicalSpace.Opens (space (sP N)))
    (hV : V ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (Y : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin N)))
    (hY : ∀ e : EuclideanSpace ℂ (Fin N), e ∈ Y ↔ EuclideanSpace.equiv (Fin N) ℂ e ∈ imgSet j V) :
    Function.Injective (toEHom k j V hV Y hY) := by
  intro s t h
  have hv : ∀ x : V, secVal (secOf N k j V hV s) x (stdChart N j) (mem_chart_iff.2 (hV x.2)) =
      secVal (secOf N k j V hV t) x (stdChart N j) (mem_chart_iff.2 (hV x.2)) := by
    intro x
    set p : Fin N → ℂ := coordsN j ⟨x.1, mem_chart_iff.2 (hV x.2)⟩
    have hp : p ∈ imgSet j V := ⟨_, x.2, rfl⟩
    have he : (EuclideanSpace.equiv (Fin N) ℂ).symm p ∈ Y := (hY _).2
      (by rwa [ContinuousLinearEquiv.apply_symm_apply])
    have := congrArg (fun G : 𝒪[N, EuclideanSpace ℂ (Fin N)].presheaf.obj (op Y) => G ⟨_, he⟩) h
    change holOf k j V hV s
        (EuclideanSpace.equiv (Fin N) ℂ ((EuclideanSpace.equiv (Fin N) ℂ).symm p)) =
      holOf k j V hV t
        (EuclideanSpace.equiv (Fin N) ℂ ((EuclideanSpace.equiv (Fin N) ℂ).symm p)) at this
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    exact (holOf_coords k j V hV s x).symm.trans (this.trans (holOf_coords k j V hV t x))
  exact secOf_injective j V hV
    (eq_of_secVal_eq (stdChart_ideal N j) (fun x : V => mem_chart_iff.2 (hV x.2)) _ _ hv)

/-- Every holomorphic function on the coordinate image `Y` of `V` is `toEHom` of a section of
`𝒪(k)^an` over `V`. -/
lemma toEHom_surjective (V : TopologicalSpace.Opens (space (sP N)))
    (hV : V ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (Y : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin N)))
    (hY : ∀ e : EuclideanSpace ℂ (Fin N), e ∈ Y ↔ EuclideanSpace.equiv (Fin N) ℂ e ∈ imgSet j V) :
    Function.Surjective (toEHom k j V hV Y hY) := by
  intro G
  classical
  let Gext : EuclideanSpace ℂ (Fin N) → ℂ := fun e => if he : e ∈ Y then G ⟨e, he⟩ else 0
  have hG : DifferentiableOn ℂ Gext Y := by
    refine differentiableOn_of_contMDiff Y Gext ?_
    have : (fun x : Y => Gext x) = (G : Y → ℂ) := funext fun x => dif_pos x.2
    rw [this]
    exact (show ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin N)) 𝓘(ℂ) ∞ (G : Y → ℂ) from G.2)
  let h : (Fin N → ℂ) → ℂ := fun p => Gext ((EuclideanSpace.equiv (Fin N) ℂ).symm p)
  have hh : DifferentiableOn ℂ h (imgSet j V) :=
    hG.comp (EuclideanSpace.equiv (Fin N) ℂ).symm.differentiableOn
      fun p hp => (hY _).2
      (by rwa [ContinuousLinearEquiv.apply_symm_apply])
  obtain ⟨f, hf⟩ := exists_sections_secVal_eq (c := stdChart N j)
    (fun x : V => mem_chart_iff.2 (hV x.2)) (isOpen_imgSet j V) h hh (fun x => ⟨_, x.2, rfl⟩)
  let f' : (ringCatSheaf (sP N)).obj.obj (op V) := f
  refine ⟨f' • (Lan N k).val.map (homOfLE hV).op (uSec N k j), ?_⟩
  apply ContMDiffMap.ext
  intro e
  change holOf k j V hV _ (EuclideanSpace.equiv (Fin N) ℂ e.1) = G e
  set p := EuclideanSpace.equiv (Fin N) ℂ e.1
  have hp : p ∈ imgSet j V := (hY e.1).1 e.2
  let x : V := ⟨((coordsEquiv j).symm p).1, mem_of_mem_imgSet j hp⟩
  have hx : (stdChart N j).coords ⟨x.1, mem_chart_iff.2 (hV x.2)⟩ = p :=
    (coordsEquiv j).apply_symm_apply p
  have e1 := holOf_coords k j V hV (f' • (Lan N k).val.map (homOfLE hV).op (uSec N k j)) x
  rw [hx] at e1
  refine e1.trans ?_
  refine (congrArg (fun f => secVal f x (stdChart N j) (mem_chart_iff.2 (hV x.2)))
    (secOf_eq N k j V hV _ f' rfl)).trans ?_
  refine (hf x).trans ?_
  rw [hx]
  change Gext ((EuclideanSpace.equiv (Fin N) ℂ).symm p) = G e
  have he : (EuclideanSpace.equiv (Fin N) ℂ).symm p = e.1 :=
    (EuclideanSpace.equiv (Fin N) ℂ).symm_apply_apply e.1
  simp only [Gext, he, dif_pos e.2]

/-- The identification of the sections of `𝒪(k)^an` with holomorphic functions on `ℂᴺ`. -/
noncomputable def toEEquiv (V : TopologicalSpace.Opens (space (sP N)))
    (hV : V ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    (Y : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin N)))
    (hY : ∀ e : EuclideanSpace ℂ (Fin N), e ∈ Y ↔ EuclideanSpace.equiv (Fin N) ℂ e ∈ imgSet j V) :
    (Lan N k).val.obj (op V) ≃+ 𝒪[N, EuclideanSpace ℂ (Fin N)].presheaf.obj (op Y) :=
  AddEquiv.ofBijective (toEHom k j V hV Y hY)
    ⟨toEHom_injective k j V hV Y hY, toEHom_surjective k j V hV Y hY⟩

/-- `toEHom` commutes with restriction. -/
lemma toEHom_res {V₁ V₂ : TopologicalSpace.Opens (space (sP N))} (h : V₂ ≤ V₁)
    (hV₁ : V₁ ≤ (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U)
    {Y₁ Y₂ : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin N))} (hYY : Y₂ ≤ Y₁)
    (hY₁ : ∀ e : EuclideanSpace ℂ (Fin N), e ∈ Y₁ ↔ EuclideanSpace.equiv (Fin N) ℂ e ∈ imgSet j V₁)
    (hY₂ : ∀ e : EuclideanSpace ℂ (Fin N), e ∈ Y₂ ↔ EuclideanSpace.equiv (Fin N) ℂ e ∈ imgSet j V₂)
    (s : (Lan N k).val.obj (op V₁)) :
    toEHom k j V₂ (h.trans hV₁) Y₂ hY₂ ((Lan N k).val.map (homOfLE h).op s) =
      𝒪[N, EuclideanSpace ℂ (Fin N)].presheaf.map (homOfLE hYY).op
        (toEHom k j V₁ hV₁ Y₁ hY₁ s) :=
  ContMDiffMap.ext fun e => holOf_res k j h hV₁ s ((hY₂ e.1).1 e.2)

end AcycE2

section AcycTop

open Stacks.ProjectiveSpace.Cohomology AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Manifold ContDiff

attribute [local instance] locallyOfFiniteType_sP

variable {N : ℕ} (k : ℤ) (S : Finset (Fin (N + 1))) (j : Fin (N + 1))

/-- The product domain `∏ (ℂ or ℂ^*)` of affine coordinates of `W(S)` in the chart `U_j`. -/
def prodDomain : TopologicalSpace.Opens (TopCat.of (EuclideanSpace ℂ (Fin N))) :=
  ⟨(EuclideanSpace.equiv (Fin N) ℂ) ⁻¹' lDom (sdisc S j),
    (isOpen_lDom _).preimage (EuclideanSpace.equiv (Fin N) ℂ).continuous⟩

variable {S j}

/-- The affine coordinates of `W(S)` in the chart `U_j`. -/
noncomputable def gS (hj : j ∈ S) :
    (TopologicalSpace.Opens.toTopCat (space (sP N))).obj (WS N S) ⟶
      (TopologicalSpace.Opens.toTopCat (TopCat.of (EuclideanSpace ℂ (Fin N)))).obj (prodDomain S j) :=
  TopCat.ofHom ⟨fun x => ⟨(EuclideanSpace.equiv (Fin N) ℂ).symm
      (coordsN j ⟨x.1, mem_chart_of_WS j hj x⟩), by
      change (EuclideanSpace.equiv (Fin N) ℂ) ((EuclideanSpace.equiv (Fin N) ℂ).symm _) ∈ lDom _
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact coords_mem_lDom j hj x⟩, by
    refine Continuous.subtype_mk ?_ _
    refine (EuclideanSpace.equiv (Fin N) ℂ).symm.continuous.comp ?_
    exact (isOpenEmbedding_coords (stdChart N j) (stdChart_ideal N j)).continuous.comp
      (continuous_subtype_val.subtype_mk _)⟩

/-- The map `gS hj` sends `x ∈ W(S)` to its affine coordinates in the chart `U_j`. -/
lemma gS_apply (hj : j ∈ S) (x : WS N S) :
    (gS hj x).1 = (EuclideanSpace.equiv (Fin N) ℂ).symm
      (coordsN j ⟨x.1, mem_chart_of_WS j hj x⟩) := rfl

/-- The affine coordinate map `gS hj` from `W(S)` to `prodDomain S j` is an open embedding. -/
lemma isOpenEmbedding_gS (hj : j ∈ S) : Topology.IsOpenEmbedding (gS hj) := by
  have hchart : IsOpen (chart (sX := sP N) (stdChart N j).U) :=
    (stdChart N j).isOpen_chart_and_isEmbedding_coords.1
  have hincl : Topology.IsOpenEmbedding
      (fun x : WS N S => (⟨x.1, mem_chart_of_WS j hj x⟩ : chart (sX := sP N) (stdChart N j).U)) :=
    Topology.IsOpenEmbedding.of_comp _ hchart.isOpenEmbedding_subtypeVal (WS N S).isOpenEmbedding'
  have h2 : Topology.IsOpenEmbedding (Subtype.val ∘ gS hj) :=
    (EuclideanSpace.equiv (Fin N) ℂ).symm.toHomeomorph.isOpenEmbedding.comp
      ((isOpenEmbedding_coords (stdChart N j) (stdChart_ideal N j)).comp hincl)
  exact Topology.IsOpenEmbedding.of_comp _ (prodDomain S j).isOpenEmbedding' h2

/-- The affine coordinate map `gS hj` from `W(S)` to `prodDomain S j` is surjective. -/
lemma surjective_gS (hj : j ∈ S) : Function.Surjective (gS hj) := by
  intro d
  refine ⟨ptW j hj (EuclideanSpace.equiv (Fin N) ℂ d.1) d.2, Subtype.ext ?_⟩
  refine (gS_apply hj _).trans ?_
  have : coordsN j ⟨(ptW j hj (EuclideanSpace.equiv (Fin N) ℂ d.1) d.2).1,
      mem_chart_of_WS j hj _⟩ = EuclideanSpace.equiv (Fin N) ℂ d.1 := coords_ptW j hj _ d.2
  rw [this, ContinuousLinearEquiv.symm_apply_apply]

end AcycTop

section AcycIso

open Stacks.ProjectiveSpace.Cohomology AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Manifold ContDiff

attribute [local instance] locallyOfFiniteType_sP

variable {N : ℕ} (k : ℤ) {S : Finset (Fin (N + 1))} {j : Fin (N + 1)}

/-- The holomorphic functions on `ℂᴺ`, as an abelian sheaf. -/
noncomputable abbrev holAbSheaf : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (EuclideanSpace ℂ (Fin N))) :=
  (SheafOfModules.toSheaf _).obj
    (SheafOfModules.unit (holomorphicRingCatSheaf N (EuclideanSpace ℂ (Fin N))))

/-- For `j ∈ S`, the image in `ℙᴺ_ℂ^an` of an open of `W(S)` lies in `U_j^an`. -/
lemma functorObj_le (hj : j ∈ S)
    (V : TopologicalSpace.Opens ((TopologicalSpace.Opens.toTopCat (space (sP N))).obj (WS N S))) :
    (TopologicalSpace.Opens.isOpenEmbedding (WS N S)).functor.obj V ≤
      (Opens.map (toSchemeHom (sP N))).obj (stdChart N j).U := by
  rintro _ ⟨v, -, rfl⟩
  exact WS_le j hj v.2

/-- A point of `EuclideanSpace ℂ (Fin N)` lies in the image under `gS hj` of an open `V` of `W(S)`
if and only if its coordinates lie in `imgSet j` of the image of `V`. -/
lemma mem_Y_iff (hj : j ∈ S)
    (V : TopologicalSpace.Opens ((TopologicalSpace.Opens.toTopCat (space (sP N))).obj (WS N S)))
    (e : EuclideanSpace ℂ (Fin N)) :
    e ∈ (TopologicalSpace.Opens.isOpenEmbedding (prodDomain S j)).functor.obj
        ((isOpenEmbedding_gS hj).functor.obj V) ↔
      EuclideanSpace.equiv (Fin N) ℂ e ∈
        imgSet j ((TopologicalSpace.Opens.isOpenEmbedding (WS N S)).functor.obj V) := by
  constructor
  · rintro ⟨d, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨⟨v.1, mem_chart_of_WS j hj v⟩, ⟨v, hv, rfl⟩, ?_⟩
    change _ = EuclideanSpace.equiv (Fin N) ℂ ((EuclideanSpace.equiv (Fin N) ℂ).symm _)
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · rintro ⟨y, ⟨v, hv, hvy⟩, hy⟩
    refine ⟨gS hj v, ⟨v, hv, rfl⟩, ?_⟩
    change (EuclideanSpace.equiv (Fin N) ℂ).symm (coordsN j ⟨v.1, _⟩) = e
    have : (⟨v.1, mem_chart_of_WS j hj v⟩ : chart (sX := sP N) (stdChart N j).U) = y :=
      Subtype.ext hvy
    rw [this, hy, ContinuousLinearEquiv.symm_apply_apply]

end AcycIso

section AcycFinal

open Stacks.ProjectiveSpace.Cohomology AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Manifold ContDiff

attribute [local instance] locallyOfFiniteType_sP

variable {N : ℕ} (k : ℤ) {S : Finset (Fin (N + 1))} {j : Fin (N + 1)}

/-- **`𝒪(k)^an` on `W(S)` is the holomorphic sheaf of the product domain `prodDomain`.** -/
noncomputable def anIso (hj : j ∈ S) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' (WS N S))).obj
        ((SheafOfModules.toSheaf _).obj (Lan N k)) ≅
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (gS hj)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' (prodDomain S j))).obj holAbSheaf) := by
  let hW := TopologicalSpace.Opens.isOpenEmbedding (WS N S)
  let hg := isOpenEmbedding_gS hj
  let hi := TopologicalSpace.Opens.isOpenEmbedding (prodDomain S j)
  refine (hW.sheafPullbackIso AddCommGrpCat.{0}).app _ ≪≫ ?_ ≪≫
    ((hg.sheafPullbackIso AddCommGrpCat.{0}).app _ ≪≫
      (hg.sheafPullback AddCommGrpCat.{0}).mapIso
        ((hi.sheafPullbackIso AddCommGrpCat.{0}).app _)).symm
  refine (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun V => ?_) ?_)
  · exact (toEEquiv k j (hW.functor.obj V.unop) (functorObj_le hj V.unop)
      (hi.functor.obj (hg.functor.obj V.unop)) (mem_Y_iff hj V.unop)).toAddCommGrpIso
  · intro V₁ V₂ f
    ext s
    exact toEHom_res k j (hW.functor.monotone (leOfHom f.unop)) (functorObj_le hj V₁.unop)
      (hi.functor.monotone (hg.functor.monotone (leOfHom f.unop))) (mem_Y_iff hj V₁.unop)
      (mem_Y_iff hj V₂.unop) s

end AcycFinal

end AnalyticModel

/-! ### Comparing the two ordered Čech complexes

Both cohomologies are computed by ordered Čech complexes on the standard cover and its
analytification (`MMP.Analytic.exists_orderedCechComplex_homologyIso_sheafCohomology`), and the
comparison map is induced by the cochain map `chi`. The algebraic complex is the Laurent
polynomial complex (`algComplexIso`), the analytic one the convergent Laurent complex, and the
inclusion of the first into the second is a homotopy equivalence. -/

section Assembly

open TopologicalSpace Opposite MMP.Analytic Stacks.ProjectiveCohomology
  Stacks.ProjectiveSpace.Cohomology

variable (N : ℕ) (k : ℤ)

/-- The standard cover `Uᵢ = D₊(xᵢ)` of `ℙᴺ_ℂ`. -/
noncomputable abbrev algCover : ULift.{0} (Fin (N + 1)) → (ℙ[N]).Opens :=
  basicOpenXAtUniverse ℂ N

/-- Its analytification, `Uᵢ^an = α⁻¹ Uᵢ`. -/
noncomputable abbrev anCover : ULift.{0} (Fin (N + 1)) → Opens (Analytification.space (sP N)) :=
  fun i => (Opens.map (Analytification.toSchemeHom (sP N))).obj (algCover N i)

/-- `𝒪(k)` as a sheaf of abelian groups. -/
noncomputable abbrev algSheaf : TopCat.Sheaf AddCommGrpCat.{0}
    (ℙ[N]).toPresheafedSpace.carrier :=
  (SheafOfModules.toSheaf _).obj (𝒪ℙ[N, k])

/-- `𝒪(k)^an` as a sheaf of abelian groups. -/
noncomputable abbrev anSheaf : TopCat.Sheaf AddCommGrpCat.{0} (Analytification.space (sP N)) :=
  (SheafOfModules.toSheaf _).obj
    ((analytifyModule (sP N)).obj (𝒪ℙ[N, k]))

/-- The transpose `𝒪(k) ⟶ α_* 𝒪(k)^an` of `ι_{𝒪(k)}`. -/
noncomputable abbrev unitAdj : algSheaf N k ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (Analytification.toSchemeHom (sP N))).obj
      (anSheaf N k) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0}
    (Analytification.toSchemeHom (sP N))).homEquiv _ _
      (analytifyModuleι (sP N) (𝒪ℙ[N, k]))

/-- The intersection of the analytified standard cover over `J` is the preimage of the intersection
of the standard cover over `J`. -/
lemma inter_anCover_eq {p : ℕ} (J : Fin (p + 1) → ULift.{0} (Fin (N + 1))) :
    CechCochains.inter (anCover N) J =
      (Opens.map (Analytification.toSchemeHom (sP N))).obj (CechCochains.inter (algCover N) J) := by
  apply SetLike.coe_injective
  simp only [CechCochains.inter]
  rw [Opens.coe_iInf, Opens.map_coe, Opens.coe_iInf, Set.preimage_iInter]
  rfl

/-- The restriction maps of a presheaf along any two morphisms `V ⟶ W` of opens agree. -/
lemma presheaf_map_congr {T : TopCat.{0}} (G : TopCat.Presheaf AddCommGrpCat.{0} T)
    {V W : Opens T} (a b : V ⟶ W) (x : G.obj (op W)) :
    (G.map a.op).hom x = (G.map b.op).hom x := by
  rw [Subsingleton.elim a b]

/-- The transpose of `ι_{𝒪(k)}` on sections over `W`. -/
noncomputable def unitApp (W : (ℙ[N]).Opens) :
    (algSheaf N k).obj.obj (op W) →+
      (anSheaf N k).obj.obj (op ((Opens.map (Analytification.toSchemeHom (sP N))).obj W)) :=
  ((unitAdj N k).hom.app (op W)).hom

/-- `unitApp` commutes with restriction. -/
lemma unitApp_naturality {W W' : (ℙ[N]).Opens}
    (h : W' ≤ W) (x : (algSheaf N k).obj.obj (op W)) :
    unitApp N k W' (((algSheaf N k).obj.map (homOfLE h).op).hom x) =
      ((anSheaf N k).obj.map
        (homOfLE ((Opens.map (Analytification.toSchemeHom (sP N))).monotone h)).op).hom
        (unitApp N k W x) :=
  congrArg (fun g => g.hom x) ((unitAdj N k).hom.naturality (homOfLE h).op)

/-- `unitApp N k W` is the analytification map `unitHom` on sections over `W`. -/
lemma unitApp_eq_unitHom (W : (ℙ[N]).Opens)
    (x : (algSheaf N k).obj.obj (op W)) :
    unitApp N k W x =
      unitHom (sX := sP N) (L := 𝒪ℙ[N, k]) W x := by
  unfold unitApp unitAdj analytifyModuleι
  erw [Equiv.apply_symm_apply]
  rfl

/-- The cochain map `s ↦ θ(α⁻¹ s)|_{U_J^an}` of the comparison. -/
noncomputable def chiHom (p : ℕ) :
    CechCochains.OrdCochain (algCover N) (algSheaf N k).obj p →+
      CechCochains.OrdCochain (anCover N) (anSheaf N k).obj p where
  toFun c J := ((anSheaf N k).obj.map (homOfLE (inter_anCover_eq N J.1).le).op).hom
    (unitApp N k (CechCochains.inter (algCover N) J.1) (c J))
  map_zero' := by
    funext J
    rw [CechCochains.OrdCochain.zero_apply, CechCochains.OrdCochain.zero_apply, map_zero,
      map_zero]
  map_add' c c' := by
    funext J
    exact (congrArg _ (map_add _ _ _)).trans (map_add _ _ _)

/-- The component of `chiHom N k p c` at `J` is the analytification of `c J`, restricted to the
intersection of the analytified cover over `J`. -/
lemma chiHom_apply (p : ℕ) (c : CechCochains.OrdCochain (algCover N) (algSheaf N k).obj p)
    (J : CechCochains.OrdIndex p) :
    chiHom N k p c J = ((anSheaf N k).obj.map (homOfLE (inter_anCover_eq N J.1).le).op).hom
      (unitApp N k (CechCochains.inter (algCover N) J.1) (c J)) := rfl

/-- `chiHom` commutes with the ordered Čech differentials. -/
lemma chiHom_ordD (p : ℕ) (c : CechCochains.OrdCochain (algCover N) (algSheaf N k).obj p) :
    chiHom N k (p + 1) (CechCochains.ordD _ _ p c) =
      CechCochains.ordD _ _ p (chiHom N k p c) := by
  funext J
  have h1 : CechCochains.ordD (algCover N) (algSheaf N k).obj p c J = ∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • CechCochains.restr _ (CechCochains.inter_le_omit _ J.1 j)
        (c ⟨J.1 ∘ j.succAbove, CechCochains.strictMono_omit J.2 j⟩) := rfl
  have h2 : CechCochains.ordD (anCover N) (anSheaf N k).obj p (chiHom N k p c) J =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • CechCochains.restr _
        (CechCochains.inter_le_omit _ J.1 j)
        (chiHom N k p c ⟨J.1 ∘ j.succAbove, CechCochains.strictMono_omit J.2 j⟩) := rfl
  rw [chiHom_apply, h1, h2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul]
  refine congrArg _ ?_
  simp only [CechCochains.restr, chiHom_apply]
  rw [unitApp_naturality]
  change ((anSheaf N k).obj.map _ ≫ (anSheaf N k).obj.map _).hom _ =
    ((anSheaf N k).obj.map _ ≫ (anSheaf N k).obj.map _).hom _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact presheaf_map_congr _ _ _ _

/-- The cochain map of the comparison, between the ordered Čech complexes of `𝒪(k)` and of
`𝒪(k)^an` on the standard covers. -/
noncomputable def chi : Stacks.Cech.orderedCechComplex (algCover N) (algSheaf N k).obj ⟶
    Stacks.Cech.orderedCechComplex (anCover N) (anSheaf N k).obj :=
  CochainComplex.ofHom (fun p => AddCommGrpCat.ofHom (chiHom N k p)) fun p => by
    rw [Stacks.Cech.orderedCechComplex_d, Stacks.Cech.orderedCechComplex_d]
    exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun c => (chiHom_ordD N k p c).symm)

/-- Laurent polynomial cochains, as finitely supported functions. -/
noncomputable def laurentFunEquiv (p : ℕ) :
    laurentCechCochains ℂ N k p ≃+ polyCochains N k p where
  toFun c := ⟨fun S β => (c.1 S) β, by
    refine ⟨⟨fun S β h => (mem_laurentCechCochains.1 c.2).1 S (Finsupp.mem_support_iff.2 h),
      fun S z _ => summable_of_ne_finset_zero (s := (c.1 S).support) fun β hβ => by
        change ‖(c.1 S) β * mono z β‖ = 0
        rw [Finsupp.notMem_support_iff.1 hβ, zero_mul, norm_zero],
      fun S hS => by
        funext β; change (c.1 S) β = 0; rw [(mem_laurentCechCochains.1 c.2).2 S hS]; rfl⟩,
      fun S => by simpa [Finsupp.fun_support_eq] using (c.1 S).support.finite_toSet⟩⟩
  invFun c := ⟨fun S => Finsupp.ofSupportFinite (c.1 S) (c.2.2 S), by
    refine mem_laurentCechCochains.2 ⟨fun S β hβ => c.2.1.1 S β ?_, fun S hS => ?_⟩
    · exact Finsupp.mem_support_iff.1 hβ
    · ext β; simp [Finsupp.ofSupportFinite_coe, c.2.1.2.2 S hS]⟩
  left_inv c := Subtype.ext (funext fun S => Finsupp.ext fun β => rfl)
  right_inv c := Subtype.ext (funext fun S => funext fun β => rfl)
  map_add' c c' := Subtype.ext (funext fun S => funext fun β => rfl)

/-- `laurentFunEquiv` intertwines the Laurent Čech differential with `polyD`. -/
lemma laurentFunEquiv_d (p : ℕ) (c : laurentCechCochains ℂ N k p) :
    laurentFunEquiv N k (p + 1) (laurentCechDiffRestrict ℂ N k p c) =
      polyD N k p (laurentFunEquiv N k p c) := by
  apply Subtype.ext; funext S β
  change (laurentCechDiff ℂ N c.1 S) β = coeffDiff N (fun S β => (c.1 S) β) S β
  rw [laurentCechDiff_apply, coeffDiff_apply, Finsupp.finset_sum_apply, Finset.sum_apply]
  rfl

/-- The algebraic ordered Čech cochains of `𝒪(k)` are the Laurent polynomial cochains. -/
noncomputable def algCochainEquiv (p : ℕ) :
    CechCochains.OrdCochain (algCover N) (algSheaf N k).obj p ≃+ polyCochains N k p :=
  (twistOrdCochainEquiv ℂ N k p).trans (laurentFunEquiv N k p)

/-- `algCochainEquiv` intertwines the ordered Čech differential with `polyD`. -/
lemma algCochainEquiv_ordD (i : ℕ)
    (c : CechCochains.OrdCochain (algCover N) (algSheaf N k).obj i) :
    algCochainEquiv N k (i + 1) (CechCochains.ordD (algCover N) (algSheaf N k).obj i c) =
      polyD N k i (algCochainEquiv N k i c) := by
  change laurentFunEquiv N k (i + 1) (twistOrdCochainEquiv ℂ N k (i + 1)
    (CechCochains.ordD _ _ i c)) = _
  exact (congrArg (laurentFunEquiv N k (i + 1)) (twistOrdCochainEquiv_ordD ℂ N k i c)).trans
    (laurentFunEquiv_d N k i _)

/-- The ordered Čech complex of `𝒪(k)` on the standard cover is the Laurent polynomial
complex. -/
noncomputable def algComplexIso :
    Stacks.Cech.orderedCechComplex (algCover N) (algSheaf N k).obj ≅ polyComplex N k :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => ((algCochainEquiv N k p).toAddCommGrpIso :
      AddCommGrpCat.of (CechCochains.OrdCochain (algCover N) (algSheaf N k).obj p) ≅
        AddCommGrpCat.of (polyCochains N k p))) fun i j hij => by
      obtain rfl : i + 1 = j := hij
      rw [Stacks.Cech.orderedCechComplex_d, polyComplex_d]
      exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun c => (algCochainEquiv_ordD N k i c).symm)

/-- `𝒪(k)` has no higher cohomology on the intersections of the standard cover. -/
lemma algSheaf_acyclic (p : ℕ) (J : CechCochains.OrdIndex (I := ULift.{0} (Fin (N + 1))) p)
    (q : ℤ) (hq : 0 < q) :
    IsZero ((sheafCohomology ((Opens.toTopCat _).obj (CechCochains.inter (algCover N) J.1)) q).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0}
        (Opens.inclusion' (CechCochains.inter (algCover N) J.1))).obj (algSheaf N k))) :=
  haveI := isQuasicoherent_twistingSheaf ℂ N k
  isZero_sheafCohomology_restrict_of_isAffineOpen _ _
    (isAffineOpen_iInf_basicOpenXAtUniverse (R := ℂ) N p J.1) _ q hq

/-- The intersections of the analytified standard cover are the opens `W(S)`. -/
lemma anInter_eq {p : ℕ} (J : CechCochains.OrdIndex (I := ULift.{0} (Fin (N + 1))) p) :
    CechCochains.inter (anCover N) J.1 = WS N (Finset.image (chartIndices J.1) Finset.univ) := by
  rw [inter_anCover_eq]
  exact congrArg (Opens.map (Analytification.toSchemeHom (sP N))).obj
    (inter_eq_basicOpen_chartDenom ℂ N p J.1 (strictMono_chartIndices J.2).injective)

/-- A coefficient cochain lies in `anCochains N k q` if and only if each component `c S` lies in
`laurentSections N k S` and the components at sets of cardinality other than `q + 1` vanish. -/
lemma mem_anCochains_iff {N : ℕ} {k : ℤ} {q : ℕ} {c : CoeffCochain N} :
    c ∈ anCochains N k q ↔ (∀ S, c S ∈ laurentSections N k S) ∧
      ∀ S : Finset (Fin (N + 1)), S.card ≠ q + 1 → c S = 0 :=
  ⟨fun h => ⟨fun S => ⟨h.1 S, fun z hz => h.2.1 S z hz⟩, h.2.2⟩,
    fun h => ⟨fun S => (h.1 S).1, fun S z hz => (h.1 S).2 z hz, h.2⟩⟩

/-- The strictly increasing Čech index enumerating a `(p + 1)`-element set of chart indices. -/
def ordIndexOf {N p : ℕ} (S : Finset (Fin (N + 1))) (h : S.card = p + 1) :
    CechCochains.OrdIndex (I := ULift.{0} (Fin (N + 1))) p :=
  ⟨fun t => ULift.up (S.orderEmbOfFin h t), fun _ _ hab => (S.orderEmbOfFin h).strictMono hab⟩

/-- The chart indices of `ordIndexOf S h` enumerate `S`. -/
lemma image_ordIndexOf {N p : ℕ} (S : Finset (Fin (N + 1))) (h : S.card = p + 1) :
    Finset.image (chartIndices (ordIndexOf S h).1) Finset.univ = S :=
  image_orderEmbOfFin_univ S h

/-- A strictly increasing Čech index is `ordIndexOf` of its set of chart indices. -/
lemma ordIndexOf_image {N p : ℕ} (J : CechCochains.OrdIndex (I := ULift.{0} (Fin (N + 1))) p)
    (h : (Finset.image (chartIndices J.1) Finset.univ).card = p + 1) :
    ordIndexOf (Finset.image (chartIndices J.1) Finset.univ) h = J :=
  Subtype.ext <| funext fun t =>
    congrArg ULift.up (congrFun (orderEmbOfFin_image_univ (strictMono_chartIndices J.2) h) t)

/-- **The Laurent model of `𝒪(k)^an` on the analytic chart intersections.** The sections of
`𝒪(k)^an` over `U_J^an` are the convergent Laurent series of degree `k` regular outside `J`,
compatibly with restriction and with the analytification of Laurent polynomials. -/
lemma exists_anSectionsEquiv :
    ∃ E : ∀ (p : ℕ) (J : CechCochains.OrdIndex (I := ULift.{0} (Fin (N + 1))) p),
        (anSheaf N k).obj.obj (op (CechCochains.inter (anCover N) J.1)) ≃+
          laurentSections N k (Finset.image (chartIndices J.1) Finset.univ),
      (∀ (q r : ℕ) (J : CechCochains.OrdIndex q) (L : CechCochains.OrdIndex r)
          (_ : Finset.image (chartIndices J.1) Finset.univ ⊆
            Finset.image (chartIndices L.1) Finset.univ)
          (h : CechCochains.inter (anCover N) L.1 ≤ CechCochains.inter (anCover N) J.1) (s),
          ((E r L (CechCochains.restr _ h s) : _) : (Fin (N + 1) → ℤ) → ℂ) = E q J s) ∧
      ∀ (p : ℕ) (c : CechCochains.OrdCochain (algCover N) (algSheaf N k).obj p)
        (J : CechCochains.OrdIndex p),
        ((E p J (chiHom N k p c J) : _) : (Fin (N + 1) → ℤ) → ℂ) =
          ⇑((ordInterChartAddEquiv ℂ N k p J (c J) : twistChart ℂ N k _) :
            (Fin (N + 1) → ℤ) →₀ ℂ) := by
  refine ⟨fun p J => (resAddEquivOfEq (anSheaf N k).obj (anInter_eq N J)).trans
    (lCoeffAddEquiv (k := k) (image_univ_nonempty _)), ?_, ?_⟩
  · intro q r J L hJL h s
    change lCoeff _ _ = lCoeff _ _
    refine Eq.trans ?_ (lCoeff_restrict (k := k) (image_univ_nonempty _) (image_univ_nonempty _)
      hJL _)
    refine congrArg (lCoeff (k := k) (image_univ_nonempty _)) ?_
    change ((anSheaf N k).obj.map _ ≫ (anSheaf N k).obj.map _).hom s =
      ((anSheaf N k).obj.map _ ≫ (anSheaf N k).obj.map _).hom s
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact presheaf_map_congr _ _ _ _
  · intro p c J
    change lCoeff _ _ = _
    have hW := inter_eq_basicOpen_chartDenom ℂ N p J.1 (strictMono_chartIndices J.2).injective
    have e : (resAddEquivOfEq (anSheaf N k).obj (anInter_eq N J)) (chiHom N k p c J) =
        unitHom (sX := sP N) (L := 𝒪ℙ[N, k]) _
          (((algSheaf N k).obj.map (homOfLE hW.ge).op).hom (c J)) := by
      refine Eq.trans ?_ (unitApp_eq_unitHom N k _ _)
      refine Eq.trans ?_ (unitApp_naturality N k hW.ge (c J)).symm
      change ((anSheaf N k).obj.map _ ≫ (anSheaf N k).obj.map _).hom _ =
        ((anSheaf N k).obj.map _).hom _
      rw [← Functor.map_comp]
      exact presheaf_map_congr _ _ _ _
    refine (congrArg (lCoeff (k := k) (image_univ_nonempty _)) e).trans ?_
    exact lCoeff_unitHom (image_univ_nonempty _) _

/-- The shape of a Laurent model of `𝒪(k)^an` on the analytic chart intersections. -/
abbrev SectionsModel :=
  ∀ (p : ℕ) (J : CechCochains.OrdIndex (I := ULift.{0} (Fin (N + 1))) p),
    (anSheaf N k).obj.obj (op (CechCochains.inter (anCover N) J.1)) ≃+
      laurentSections N k (Finset.image (chartIndices J.1) Finset.univ)

/-- For `J = J'`, the Laurent families `E p J (s J)` and `E p J' (s J')` agree. -/
lemma coe_model_congr (E : SectionsModel N k) {p : ℕ}
    (s : CechCochains.OrdCochain (anCover N) (anSheaf N k).obj p) {J J' : CechCochains.OrdIndex p}
    (h : J = J') : ((E p J (s J) : _) : (Fin (N + 1) → ℤ) → ℂ) = E p J' (s J') := by
  subst h; rfl

/-- A strictly increasing Čech index of length `p + 1` has `p + 1` distinct chart indices. -/
lemma card_image_chartIndices {p : ℕ}
    (J : CechCochains.OrdIndex (I := ULift.{0} (Fin (N + 1))) p) :
    (Finset.image (chartIndices J.1) Finset.univ).card = p + 1 :=
  card_image_univ_of_strictMono (strictMono_chartIndices J.2)

/-- The analytic ordered Čech cochains as convergent Laurent cochains, through a model. -/
noncomputable def modelEquiv (E : SectionsModel N k) (p : ℕ) :
    CechCochains.OrdCochain (anCover N) (anSheaf N k).obj p ≃+ anCochains N k p where
  toFun s := ⟨fun S => if h : S.card = p + 1 then
      ((E p (ordIndexOf S h) (s (ordIndexOf S h)) : _) : (Fin (N + 1) → ℤ) → ℂ) else 0,
    mem_anCochains_iff.2 ⟨fun S => by
      by_cases h : S.card = p + 1
      · rw [dif_pos h]
        convert (E p (ordIndexOf S h) (s (ordIndexOf S h))).2 using 2
        exact (image_ordIndexOf S h).symm
      · rw [dif_neg h]; exact zero_mem _,
      fun S h => dif_neg h⟩⟩
  invFun c J := (E p J).symm ⟨c.1 (Finset.image (chartIndices J.1) Finset.univ),
    (mem_anCochains_iff.1 c.2).1 _⟩
  left_inv s := funext fun J => by
    apply (E p J).injective
    rw [AddEquiv.apply_symm_apply]
    apply Subtype.ext
    change (if h : (Finset.image (chartIndices J.1) Finset.univ).card = p + 1 then _
      else (0 : (Fin (N + 1) → ℤ) → ℂ)) = _
    rw [dif_pos (card_image_chartIndices N J)]
    exact coe_model_congr N k E s (ordIndexOf_image J _)
  right_inv c := Subtype.ext (funext fun S => by
    change (if h : S.card = p + 1 then _ else 0) = c.1 S
    by_cases h : S.card = p + 1
    · rw [dif_pos h, AddEquiv.apply_symm_apply]
      exact congrArg c.1 (image_ordIndexOf S h)
    · rw [dif_neg h]; exact ((mem_anCochains_iff.1 c.2).2 S h).symm)
  map_add' s t := Subtype.ext (funext fun S => by
    simp only [AddSubgroup.coe_add, Pi.add_apply]
    by_cases h : S.card = p + 1
    · simp only [dif_pos h, CechCochains.OrdCochain.add_apply, map_add, AddSubgroup.coe_add]
    · simp only [dif_neg h, add_zero])

/-- The Laurent family of `(modelEquiv N k E p).symm c` at `J` is the component of `c` at the chart
indices of `J`. -/
lemma modelEquiv_symm_apply (E : SectionsModel N k) (p : ℕ) (c : anCochains N k p)
    (J : CechCochains.OrdIndex p) :
    ((E p J ((modelEquiv N k E p).symm c J) : _) : (Fin (N + 1) → ℤ) → ℂ) =
      c.1 (Finset.image (chartIndices J.1) Finset.univ) := by
  change (((E p J) ((E p J).symm _) : laurentSections N k _) : (Fin (N + 1) → ℤ) → ℂ) = _
  rw [AddEquiv.apply_symm_apply]

/-- The coefficient differential at the chart indices of a Čech index `J` is the alternating sum of
the components at the chart indices of the faces of `J`. -/
lemma coeffDiff_image_chartIndices (c : CoeffCochain N) {p : ℕ}
    (J : CechCochains.OrdIndex (I := ULift.{0} (Fin (N + 1))) (p + 1)) :
    coeffDiff N c (Finset.image (chartIndices J.1) Finset.univ) =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        c (Finset.image (chartIndices (J.1 ∘ j.succAbove)) Finset.univ) := by
  set i := chartIndices J.1
  have hi : StrictMono i := strictMono_chartIndices J.2
  have hS : (Finset.image i Finset.univ).card = p + 1 + 1 := card_image_univ_of_strictMono hi
  have hemb : ⇑((Finset.image i Finset.univ).orderEmbOfFin hS) = i :=
    orderEmbOfFin_image_univ hi hS
  rw [coeffDiff_apply, Finset.sum_image hi.injective.injOn]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : i j = (Finset.image i Finset.univ).orderEmbOfFin hS j := (congrFun hemb j).symm
  have hmem := (Finset.image i Finset.univ).orderEmbOfFin_mem hS j
  have hcard : ((Finset.image i Finset.univ).erase
      ((Finset.image i Finset.univ).orderEmbOfFin hS j)).card = p + 1 := by
    have := Finset.card_erase_of_mem hmem
    omega
  have hsign : Cech.cechSign (Finset.image i Finset.univ) (i j) = (-1 : ℤ) ^ (j : ℕ) := by
    rw [hj]; exact Cech.cechSign_orderEmbOfFin _ hS j
  have herase : (Finset.image i Finset.univ).erase (i j)
      = Finset.image (i ∘ j.succAbove) Finset.univ := by
    rw [hj, ← image_orderEmbOfFin_univ _ hcard,
      Cech.orderEmbOfFin_erase (Finset.image i Finset.univ) hS j hcard, hemb]
  rw [hsign, herase]
  rfl

/-- For a model `E` compatible with restriction, the inverses of `modelEquiv N k E` intertwine
`anD` with the ordered Čech differential. -/
lemma modelEquiv_symm_d (E : SectionsModel N k)
    (hres : ∀ (q r : ℕ) (J : CechCochains.OrdIndex q) (L : CechCochains.OrdIndex r)
      (_ : Finset.image (chartIndices J.1) Finset.univ ⊆
        Finset.image (chartIndices L.1) Finset.univ)
      (h : CechCochains.inter (anCover N) L.1 ≤ CechCochains.inter (anCover N) J.1) (s),
      ((E r L (CechCochains.restr _ h s) : _) : (Fin (N + 1) → ℤ) → ℂ) = E q J s)
    (p : ℕ) (c : anCochains N k p) :
    (modelEquiv N k E (p + 1)).symm (anD N k p c) =
      CechCochains.ordD _ _ p ((modelEquiv N k E p).symm c) := by
  funext J
  apply (E (p + 1) J).injective
  apply Subtype.ext
  have e1 := modelEquiv_symm_apply N k E (p + 1) (anD N k p c) J
  refine e1.trans ?_
  show coeffDiff N c.1 (Finset.image (chartIndices J.1) Finset.univ) = _
  rw [coeffDiff_image_chartIndices N c.1 J]
  have h2 : CechCochains.ordD (anCover N) (anSheaf N k).obj p ((modelEquiv N k E p).symm c) J =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • CechCochains.restr _
        (CechCochains.inter_le_omit _ J.1 j)
        ((modelEquiv N k E p).symm c ⟨J.1 ∘ j.succAbove, CechCochains.strictMono_omit J.2 j⟩) :=
    rfl
  rw [h2, map_sum, AddSubgroup.val_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, AddSubgroup.coe_zsmul]
  refine congrArg _ ?_
  refine Eq.trans ?_ (hres p (p + 1) ⟨J.1 ∘ j.succAbove, CechCochains.strictMono_omit J.2 j⟩ J ?_
    (CechCochains.inter_le_omit _ J.1 j) _).symm
  · exact (modelEquiv_symm_apply N k E p c
      ⟨J.1 ∘ j.succAbove, CechCochains.strictMono_omit J.2 j⟩).symm
  · intro x hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_image.2 ⟨j.succAbove t, Finset.mem_univ _, rfl⟩

/-- The analytic ordered Čech complex of `𝒪(k)^an` is the complex of convergent Laurent
cochains, compatibly with the analytification of Laurent polynomials. -/
lemma exists_anComplexIso :
    ∃ β : Stacks.Cech.orderedCechComplex (anCover N) (anSheaf N k).obj ≅ anComplex N k,
      chi N k ≫ β.hom = (algComplexIso N k).hom ≫ polyToAn N k := by
  obtain ⟨E, hres, hunit⟩ := exists_anSectionsEquiv N k
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun p => ((modelEquiv N k E p).toAddCommGrpIso :
      AddCommGrpCat.of (CechCochains.OrdCochain (anCover N) (anSheaf N k).obj p) ≅
        AddCommGrpCat.of (anCochains N k p))) fun i j hij => ?_, ?_⟩
  · obtain rfl : i + 1 = j := hij
    rw [Stacks.Cech.orderedCechComplex_d, anComplex_d]
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext
      fun (c : CechCochains.OrdCochain (anCover N) (anSheaf N k).obj i) => ?_)
    change anD N k i (modelEquiv N k E i c) = modelEquiv N k E (i + 1) (CechCochains.ordD _ _ i c)
    have h := modelEquiv_symm_d N k E hres i (modelEquiv N k E i c)
    rw [AddEquiv.symm_apply_apply] at h
    rw [← h, AddEquiv.apply_symm_apply]
  · refine HomologicalComplex.hom_ext _ _ fun p => ?_
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext
      fun (c : CechCochains.OrdCochain (algCover N) (algSheaf N k).obj p) =>
        Subtype.ext (funext fun S => ?_))
    change (modelEquiv N k E p (chiHom N k p c)).1 S = (algCochainEquiv N k p c).1 S
    by_cases h : S.card = p + 1
    · change (if h : S.card = p + 1 then _ else (0 : (Fin (N + 1) → ℤ) → ℂ)) = _
      rw [dif_pos h, hunit]
      have e := coe_twistOrdCochainEquiv_apply ℂ N k p c
        ⟨⇑(S.orderEmbOfFin h), (S.orderEmbOfFin h).strictMono⟩
      rw [image_orderEmbOfFin_univ] at e
      change _ = ⇑(((twistOrdCochainEquiv ℂ N k p c : laurentCechCochains ℂ N k p) :
        LaurentCochain ℂ N) S)
      rw [e]
      rfl
    · change (if h : S.card = p + 1 then _ else (0 : (Fin (N + 1) → ℤ) → ℂ)) = _
      rw [dif_neg h]
      change _ = ⇑(((twistOrdCochainEquiv ℂ N k p c : laurentCechCochains ℂ N k p) :
        LaurentCochain ℂ N) S)
      rw [(mem_laurentCechCochains.1 (twistOrdCochainEquiv ℂ N k p c).2).2 S h]
      rfl

/-- The cochain map `chi` induces isomorphisms on all cohomology groups. -/
lemma isIso_homologyMap_chi (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (chi N k) q) := by
  obtain ⟨β, hβ⟩ := exists_anComplexIso N k
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ q) hβ
  simp only [HomologicalComplex.homologyMap_comp] at h
  haveI := isIso_homologyMap_polyToAn (N := N) k q
  have e : HomologicalComplex.homologyMap (chi N k) q =
      (HomologicalComplex.homologyMap (algComplexIso N k).hom q ≫
        HomologicalComplex.homologyMap (polyToAn N k) q) ≫
          inv (HomologicalComplex.homologyMap β.hom q) := by
    rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [e]
  infer_instance

end Assembly

section GodementDegreeZero

open TopologicalSpace

variable (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat.{0} T)

/-- `Γ(T, -)` preserves finite limits. -/
lemma preservesFiniteLimits_globalSections : PreservesFiniteLimits (globalSections T) :=
  inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} ⋙
      (evaluation (Opens T)ᵒᵖ AddCommGrpCat.{0}).obj (op ⊤)))

/-- The complex `Γ(T, G^•(F))` of global sections of the Godement resolution, indexed by `ℕ`. -/
noncomputable abbrev godementGlobalComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((globalSections T).mapHomologicalComplex _).obj ((godementResolution T).obj F)

/-- The map `Γ(T, F) ⟶ Γ(T, G⁰(F))`, `s ↦ (s_x)_x`. -/
noncomputable abbrev godementGlobalUnit :
    (globalSections T).obj F ⟶ (godementGlobalComplex T F).X 0 :=
  (globalSections T).map ((godementUnit T).app F)

/-- The composite `Γ(T, F) ⟶ Γ(T, G⁰(F)) ⟶ Γ(T, G¹(F))` is zero. -/
lemma godementGlobalUnit_comp_d :
    godementGlobalUnit T F ≫ (godementGlobalComplex T F).d 0 1 = 0 := by
  change (globalSections T).map _ ≫ (globalSections T).map
    (CokernelCoresolution.d (godementFunctor T) (godementUnit T) F 0) = 0
  exact ((globalSections T).map_comp _ _).symm.trans ((congrArg (globalSections T).map
    (CokernelCoresolution.app_comp_d_zero _ _ F)).trans (Functor.map_zero _ _ _))

/-- `Γ(T, F)` is the kernel of `Γ(T, G⁰(F)) ⟶ Γ(T, G¹(F))`. -/
lemma nonempty_isLimit_godementGlobalUnit :
    Nonempty (IsLimit (KernelFork.ofι _ (godementGlobalUnit_comp_d T F))) := by
  haveI := preservesFiniteLimits_globalSections T
  haveI := mono_godementUnit_app F
  haveI : Mono
      ((globalSections T).map ((godementUnit T).app (cokernel ((godementUnit T).app F)))) :=
    (AddCommGrpCat.mono_iff_injective _).2 (godementUnit_app_hom_app_injective _ (op ⊤))
  have h1 := Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ _ (cokernel.condition
    ((godementUnit T).app F))) (cokernelIsCokernel _)
  have h2 := KernelFork.mapIsLimit _ h1 (globalSections T)
  exact ⟨isKernelCompMono h2 ((globalSections T).map ((godementUnit T).app
    (cokernel ((godementUnit T).app F)))) (h := (godementGlobalComplex T F).d 0 1)
    (by change (globalSections T).map (CokernelCoresolution.d _ _ F 0) = _
        exact Functor.map_comp _ _ _)⟩

/-- The map from `Γ(T, F)` to the degree-`0` cycles of `Γ(T, G^•(F))` is an isomorphism. -/
lemma isIso_liftCycles_godementGlobalUnit :
    IsIso ((godementGlobalComplex T F).liftCycles (godementGlobalUnit T F) 1 (by simp)
      (godementGlobalUnit_comp_d T F)) := by
  obtain ⟨h⟩ := nonempty_isLimit_godementGlobalUnit T F
  have he : (IsLimit.conePointUniqueUpToIso h
      ((godementGlobalComplex T F).cyclesIsKernel 0 1 (by simp))).hom =
      (godementGlobalComplex T F).liftCycles (godementGlobalUnit T F) 1 (by simp)
        (godementGlobalUnit_comp_d T F) := by
    rw [← cancel_mono ((godementGlobalComplex T F).iCycles 0)]
    simp only [HomologicalComplex.liftCycles_i]
    exact IsLimit.conePointUniqueUpToIso_hom_comp h
      ((godementGlobalComplex T F).cyclesIsKernel 0 1 (by simp)) WalkingParallelPair.zero
  rw [← he]; infer_instance

/-- The identification `Γ(T, F) ⟶ H⁰(Γ(T, G^•(F)))`. -/
noncomputable def globalSectionsToGodementHomology :
    (globalSections T).obj F ⟶ (godementGlobalComplex T F).homology 0 :=
  (godementGlobalComplex T F).liftCycles (godementGlobalUnit T F) 1 (by simp)
    (godementGlobalUnit_comp_d T F) ≫ (godementGlobalComplex T F).homologyπ 0

/-- The map `Γ(T, F) ⟶ H⁰(Γ(T, G^•(F)))` is an isomorphism. -/
lemma isIso_globalSectionsToGodementHomology :
    IsIso (globalSectionsToGodementHomology T F) := by
  have := isIso_liftCycles_godementGlobalUnit T F
  unfold globalSectionsToGodementHomology; infer_instance

variable {T} in
/-- In degree `0`, the pullback of Godement resolutions followed by `G⁰(θ)` restricts on `F` to
the adjunct of `θ`. -/
lemma godementUnit_comp_godementResolutionPullback_f_zero {T' : TopCat.{0}} (f : T' ⟶ T)
    (F' : TopCat.Sheaf AddCommGrpCat.{0} T')
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj F ⟶ F') :
    (godementUnit T).app F ≫ (godementResolutionPullback f F).f 0 ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (((godementResolution T').map θ).f 0) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _ θ ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map ((godementUnit T').app F') := by
  have h1 : (godementUnit T).app F ≫ (godementResolutionPullback f F).f 0 =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map ((godementUnit T').app _) :=
    (godementPullbackLift f).app_comp_lift _
  have h2 : (godementUnit T').app _ ≫ ((godementResolution T').map θ).f 0 =
      θ ≫ (godementUnit T').app F' := ((godementUnit T').naturality θ).symm
  refine (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h1).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map_comp _ _).symm.trans
      ((congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map h2).trans
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map_comp _ _)))).trans ?_
  rw [Adjunction.homEquiv_unit, Category.assoc]
  rfl

variable {T} in
/-- Under the identifications `Γ ≅ H⁰(Γ(G^•))`, the map on `H⁰` induced by the pullback of Godement
resolutions along `f` and by `θ` is the map on global sections of the adjunct `F ⟶ f_* F'` of `θ`.
-/
lemma globalSectionsToGodementHomology_comp_homologyMap {T' : TopCat.{0}} (f : T' ⟶ T)
    (F' : TopCat.Sheaf AddCommGrpCat.{0} T')
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj F ⟶ F') :
    globalSectionsToGodementHomology T F ≫ HomologicalComplex.homologyMap
        (((globalSections T).mapHomologicalComplex _).map (godementResolutionPullback f F)) 0 ≫
        HomologicalComplex.homologyMap
          (((globalSections T').mapHomologicalComplex _).map
            ((godementResolution T').map θ)) 0 =
      (globalSections T).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _ θ) ≫
        globalSectionsToGodementHomology T' F' := by
  have key := congrArg (globalSections T).map
    (godementUnit_comp_godementResolutionPullback_f_zero F f F' θ)
  simp only [Functor.map_comp] at key
  let φ : godementGlobalComplex T F ⟶ godementGlobalComplex T' F' :=
    ((globalSections T).mapHomologicalComplex _).map (godementResolutionPullback f F) ≫
      ((globalSections T').mapHomologicalComplex _).map ((godementResolution T').map θ)
  have e1 : HomologicalComplex.homologyMap
        (((globalSections T).mapHomologicalComplex _).map (godementResolutionPullback f F)) 0 ≫
        HomologicalComplex.homologyMap
          (((globalSections T').mapHomologicalComplex _).map
            ((godementResolution T').map θ)) 0 = HomologicalComplex.homologyMap φ 0 :=
    (HomologicalComplex.homologyMap_comp _ _ _).symm
  rw [e1, globalSectionsToGodementHomology, globalSectionsToGodementHomology, Category.assoc,
    HomologicalComplex.homologyπ_naturality, HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  refine (congrArg (· ≫ (godementGlobalComplex T' F').homologyπ 0) ?_).trans
    (Category.assoc _ _ _)
  refine Eq.trans ?_ (HomologicalComplex.comp_liftCycles _ _ _ _ _ _).symm
  congr 1

variable {T} in
/-- If the pullback `H⁰(T, F) ⟶ H⁰(T', F')` along `f` and `θ : f⁻¹ F ⟶ F'` is an isomorphism, so
is the adjunct `F ⟶ f_* F'` of `θ` on global sections. -/
lemma isIso_globalSections_homEquiv {T' : TopCat.{0}} (f : T' ⟶ T)
    (F' : TopCat.Sheaf AddCommGrpCat.{0} T')
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj F ⟶ F')
    (h : IsIso (sheafCohomologyPullback f F ((0 : ℕ) : ℤ) ≫
      (sheafCohomology T' ((0 : ℕ) : ℤ)).map θ)) :
    IsIso ((globalSections T).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _ θ)) := by
  have e1 := sheafCohomologyGodementIso_pullback f F F' θ 0
  have e2 := globalSectionsToGodementHomology_comp_homologyMap F f F' θ
  have e3 : HomologicalComplex.homologyMap
        (((globalSections T).mapHomologicalComplex _).map (godementResolutionPullback f F)) 0 ≫
        HomologicalComplex.homologyMap
          (((globalSections T').mapHomologicalComplex _).map
            ((godementResolution T').map θ)) 0 =
      (sheafCohomologyGodementIso T F 0).inv ≫
        (sheafCohomologyPullback f F ((0 : ℕ) : ℤ) ≫ (sheafCohomology T' ((0 : ℕ) : ℤ)).map θ) ≫
        (sheafCohomologyGodementIso T' F' 0).hom := by
    rw [Category.assoc, e1, Iso.inv_hom_id_assoc]
  have hc : IsIso ((globalSections T).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _ θ) ≫
      globalSectionsToGodementHomology T' F') := by
    have := isIso_globalSectionsToGodementHomology T F
    rw [← e2, e3]; infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (globalSectionsToGodementHomology T' F')
    (isIso_globalSectionsToGodementHomology T' F') hc

end GodementDegreeZero

open Stacks.ProjectiveSpace.Cohomology in
/-- For `N ≥ 1` and `d < 0`, a family of Laurent coefficient families, one on each chart
`D₊(xᵢ)`, which all agree, is zero. -/
theorem eq_zero_of_coe_eq_coe_zero {N : ℕ} (hN : 1 ≤ N) {d : ℤ} (hd : d < 0)
    (f : ∀ i : Fin (N + 1), twistChart ℂ N d (↑({i} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))
    (hf : ∀ i, (f i : (Fin (N + 1) → ℤ) →₀ ℂ) = f 0) (i : Fin (N + 1)) : f i = 0 := by
  have hmem : (f 0 : (Fin (N + 1) → ℤ) →₀ ℂ) ∈ ⨅ i : Fin (N + 1), twistChart ℂ N d {i} := by
    refine (Submodule.mem_iInf _).2 fun i => ?_
    have := (f i).2
    rwa [hf i, Finset.coe_singleton] at this
  rw [twistChart_iInf_singleton N hN d, twistChart_eq_bot_of_neg N hd, Submodule.mem_bot] at hmem
  exact Subtype.ext ((hf i).trans hmem)

open Stacks.ProjectiveSpace.Cohomology in
/-- On `ℙᴺ`, the Laurent coefficients of a global section of `𝒪(d)` on the chart `D₊(xᵢ)` are
those on `D₊(x₀)`. -/
theorem coe_chartSectionsAddEquivTwistChart_singleton {N : ℕ} {d : ℤ}
    (σ : (ProjectiveSpectrum.Proj.twistingSheaf
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) d).val.obj (op ⊤))
    (i : Fin (N + 1)) :
    ((chartSectionsAddEquivTwistChart ℂ N d {i} ⟨i, Finset.mem_singleton_self i⟩
        (chartRestrict ℂ N d {i} σ) : (Fin (N + 1) → ℤ) →₀ ℂ)) =
      ((chartSectionsAddEquivTwistChart ℂ N d {0} ⟨0, Finset.mem_singleton_self 0⟩
        (chartRestrict ℂ N d {0} σ) : (Fin (N + 1) → ℤ) →₀ ℂ)) :=
  (coe_chartSectionsAddEquivTwistChart_mono ℂ N d {i} {0, i} _ (by simp) σ).symm.trans
    (coe_chartSectionsAddEquivTwistChart_mono ℂ N d {0} {0, i} _ (by simp) σ)

open Stacks.ProjectiveSpace.Cohomology in
/-- On `ℙᴺ`, `N ≥ 1`, every global section of `𝒪(d)`, `d < 0`, restricts to zero on each
chart `D₊(xᵢ)`, read in Laurent coordinates. -/
theorem chartSectionsAddEquivTwistChart_chartRestrict_eq_zero_of_neg {N : ℕ}
    (hN : 1 ≤ N) {d : ℤ} (hd : d < 0)
    (σ : (ProjectiveSpectrum.Proj.twistingSheaf
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) d).val.obj (op ⊤))
    (i : Fin (N + 1)) (hi : ({i} : Finset (Fin (N + 1))).Nonempty) :
    chartSectionsAddEquivTwistChart ℂ N d {i} hi (chartRestrict ℂ N d {i} σ) = 0 :=
  eq_zero_of_coe_eq_coe_zero hN hd
    (fun i => chartSectionsAddEquivTwistChart ℂ N d {i} ⟨i, Finset.mem_singleton_self i⟩
      (chartRestrict ℂ N d {i} σ))
    (coe_chartSectionsAddEquivTwistChart_singleton σ) i

open Stacks.ProjectiveSpace.Cohomology in
/-- On `ℙᴺ`, `N ≥ 1`, the twisting sheaf `𝒪(d)` has at most one global section for `d < 0`. -/
theorem twistingSheaf_globalSection_eq_of_neg {N : ℕ} (hN : 1 ≤ N) {d : ℤ}
    (hd : d < 0)
    (σ τ : (ProjectiveSpectrum.Proj.twistingSheaf
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) d).val.obj (op ⊤)) : σ = τ := by
  have hs : ∀ i : Fin (N + 1), ({i} : Finset (Fin (N + 1))).Nonempty :=
    fun i => ⟨i, Finset.mem_singleton_self i⟩
  have hrest : ∀ i : Fin (N + 1), chartRestrict ℂ N d {i} σ = chartRestrict ℂ N d {i} τ :=
    fun i => (chartSectionsAddEquivTwistChart ℂ N d {i} (hs i)).injective
      ((chartSectionsAddEquivTwistChart_chartRestrict_eq_zero_of_neg hN hd σ i (hs i)).trans
        (chartSectionsAddEquivTwistChart_chartRestrict_eq_zero_of_neg hN hd τ i (hs i)).symm)
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨i, hxi⟩ := exists_mem_basicOpen_X ℂ N x.1
  have hxi' : x.1 ∈ ProjectiveSpectrum.basicOpen
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) (chartDenom ℂ N {i}) := by
    rwa [chartDenom, Finset.prod_singleton]
  exact congrArg (fun y : chartSheafSections ℂ N d {i} => y.1 ⟨x.1, hxi'⟩) (hrest i)

/-- For `k < 0` the map from the (zero) degree-`k` part to `Γ(𝒪(k))` is bijective. -/
theorem bijective_degreeZeroToGlobalSections_of_neg (N : ℕ) (hN : 1 ≤ N) (k : ℤ)
    (hk : k < 0) :
    Function.Bijective (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)
      (ProjectiveSpectrum.Proj.twistGrading
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k)) := by
  have hzero : ∀ a : (ProjectiveSpectrum.Proj.twistGrading
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k 0), a = 0 := fun a =>
    Subtype.ext (by
      simpa [ProjectiveSpectrum.Proj.twistGrading, ProjectiveSpectrum.Proj.integerGrading,
        not_le.mpr hk] using a.2)
  exact ⟨fun a b _ => (hzero a).trans (hzero b).symm,
    fun σ => ⟨0, twistingSheaf_globalSection_eq_of_neg hN hk _ σ⟩⟩

/-- For `n ≥ 0`, the map from the degree-`n` homogeneous polynomials to `Γ(𝒪(n))` is injective. -/
theorem injective_degreeZeroToGlobalSections_natCast (N n : ℕ) :
    Function.Injective (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)
      (ProjectiveSpectrum.Proj.twistGrading
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) (n : ℤ))) := by
  intro a b hab
  have hmem : ∀ x : (ProjectiveSpectrum.Proj.twistGrading
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) (n : ℤ) 0),
      (x : MvPolynomial (Fin (N + 1)) ℂ) ∈
        Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N n :=
    fun x => by
      simpa [ProjectiveSpectrum.Proj.twistGrading, ProjectiveSpectrum.Proj.integerGrading,
        ProjectiveSpectrum.Proj.homogeneousSubmodule] using x.2
  exact Subtype.ext (congrArg Subtype.val
    (Stacks.ProjectiveSpace.Cohomology.injective_degreeSection ℂ N n
      (a₁ := ⟨a, hmem a⟩) (a₂ := ⟨b, hmem b⟩) hab) :)

open Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep in
/-- The degree-`k` homogeneous polynomials are the global sections of `𝒪(k)`. -/
theorem bijective_degreeZeroToGlobalSections (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    Function.Bijective (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)
      (ProjectiveSpectrum.Proj.twistGrading
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N) k)) :=
  (le_or_gt 0 k).elim
    (fun hk => ⟨Int.toNat_of_nonneg hk ▸ injective_degreeZeroToGlobalSections_natCast N k.toNat,
      surjective_degreeZeroToGlobalSections_of_degreeSection
        _ (fun k =>
          (Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_mvPolynomial ℂ N k).2)
        k hk⟩)
    (fun hk => bijective_degreeZeroToGlobalSections_of_neg N hN k hk)

/-- `H^q(ℙᴺ_ℂ, 𝒪(k))` vanishes for `0 < q < N`, for `q > N`, and for `q = N` when `-N ≤ k`. -/
theorem isZero_sheafCohomology_twistingSheaf (N : ℕ) (hN : 1 ≤ N) (k : ℤ) (q : ℕ)
    (hq : (0 < q ∧ q < N) ∨ N < q ∨ (q = N ∧ -(N : ℤ) ≤ k)) :
    IsZero ((sheafCohomology _ q).obj ((SheafOfModules.toSheaf _).obj (𝒪ℙ[N, k]))) := by
  obtain ⟨-, -, ⟨⟨E, -⟩, -⟩, -⟩ := sheafCohomology_toolkit.{0, 0, 0, 0, 0}
    (ℙ[N]).toTopCat
  refine IsZero.of_iso ?_ ((E _ q).app _ ≪≫
    (MMP.Cohomology.toSheafCompRightDerivedGlobalSectionsIso _ q).app
      (𝒪ℙ[N, k]))
  have hz : IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology ℂ N k q) := by
    by_cases htop : q = N ∧ k < 0
    · obtain ⟨rfl, hk0⟩ := htop
      exact Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_of_neg_le ℂ q k
        (by omega) hk0 q
    · exact Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology ℂ N k q (by omega)
  have hs : Subsingleton (Stacks.ProjectiveSpace.Cohomology.twistCohomology ℂ N k q) :=
    ModuleCat.subsingleton_of_isZero hz
  exact @AddCommGrpCat.isZero_of_subsingleton _ hs

end MMP.Analytic.ProjectiveTwists
