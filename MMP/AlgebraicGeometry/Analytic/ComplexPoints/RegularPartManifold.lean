module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AlgebraicChart
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LevelSetChartAnalytic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPointEuclideanChart

/-!
# The regular part of a complex variety is a complex manifold

Let `X` be a variety of dimension `n` over `ℂ` (an algebraically closed `RCLike` field). Every
point `p ∈ X_reg(ℂ)` lies in an affine open `U`, and in a basic open `{g ≠ 0}` of `U` whose ring
`A_g` has a submersive presentation `ℂ[x_i] / (f_j)` of relative dimension `n`. The points where
`g` does not vanish are the zero set `L` of `f = (f_j)` in `ℂ^ι`, a complex submanifold of
dimension `n`; composing with a chart of `L` gives a chart of `X(ℂ)` around `p`.

These charts are *algebraic* (`MMP.UnderlyingSpace.IsAlgebraicChart`): a regular
function `a ∈ Γ(X, V)` is, near any point, a quotient `b / hᵐ` of global functions on `U`, and
`b`, `h` are polynomials in the coordinates `x_i`, hence analytic in the charts of `L`; and the
coordinates of the chart are linear in the generators `x_i ∈ A_g`. The transition maps between
algebraic charts are analytic, so these charts form a holomorphic atlas on `X_reg(ℂ)`.

## Main definitions

* `MMP.UnderlyingSpace.nonvanishingLocusChart`: the chart of `X(𝕜)` given by a
  presentation of `A_g` with submersive relation map and a chart of its zero set.
* `MMP.UnderlyingSpace.regularOpens`: `X_reg(𝕜)` as an open subset of `X(𝕜)`.
* `MMP.UnderlyingSpace.regularChartedSpace`: the algebraic charts of `X_reg(ℂ)`,
  modelled on `ℂⁿ`, `n = dim X`.

## Main results

* `MMP.UnderlyingSpace.isAlgebraicChart_nonvanishingLocusChart`: these charts are
  algebraic.
* `MMP.UnderlyingSpace.exists_isAlgebraicChart`: every point of `X_reg(ℂ)` lies in
  the source of an algebraic chart with values in `ℂ^{dim X}`.
* `MMP.UnderlyingSpace.isManifold_regularOpens`: `X_reg(ℂ)` is a complex analytic
  manifold of dimension `dim X`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open MMP.Intersection.Scheme (dimension)
open scoped ContDiff Manifold

universe u

namespace MMP

namespace UnderlyingSpace

section NonvanishingLocus

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsAffine X]

/-- A `K`-point of an affine scheme lies in the basic open `D(g)` iff `g` does not vanish at
it. -/
lemma top_le_preimage_basicOpen_iff_mem_nonvanishingLocus (g : Γ(X, ⊤))
    (q : UnderlyingSpace K X) :
    ⊤ ≤ q.toHom ⁻¹ᵁ X.basicOpen g ↔ q ∈ nonvanishingLocus K g :=
  top_le_preimage_basicOpen_iff (U := ⊤) q (Scheme.Hom.preimage_top _).ge g

/-- Evaluation of a section over `D(g)` at a point where `g` does not vanish is evaluation of
the corresponding element of `A_g`. -/
lemma eval_algEquiv_localizationAway [Algebra K Γ(X, ⊤)] {g : Γ(X, ⊤)} (q : nonvanishingLocus K g)
    (hq : ⊤ ≤ q.1.toHom ⁻¹ᵁ X.basicOpen g) (s : Localization.Away g) :
    eval q.1 hq (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
      Γ(X, X.basicOpen g) s) = awayEval q s := by
  have : (evalRingHom q.1 hq).comp (IsLocalization.algEquiv (Submonoid.powers g)
      (Localization.Away g) Γ(X, X.basicOpen g) : Localization.Away g →+* Γ(X, X.basicOpen g)) =
      awayEval q := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun c ↦ ?_)
    change eval q.1 hq (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
      Γ(X, X.basicOpen g) (algebraMap _ _ c)) = awayEval q (algebraMap _ _ c)
    rw [AlgEquiv.commutes, awayEval_algebraMap]
    exact eval_restrict (X.basicOpen_le g) q.1 hq c
  exact congr($this s)

end NonvanishingLocus

section Chart

variable {𝕜 : Type u} [RCLike 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))] [IsAffine X]
  [Algebra 𝕜 Γ(X, ⊤)] {g : Γ(X, ⊤)} {ι σ : Type} [Fintype ι] [Fintype σ] [DecidableEq σ]
  (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X)
  (P : Algebra.Presentation 𝕜 (Localization.Away g) ι σ) {n : WithTop ℕ∞}
  (hsub : SmoothLevelSet.IsSubmersionOn (𝕜 := 𝕜) n Set.univ
    (SubmersivePresentationLevelSet.relMap P))
  {z : ι → 𝕜} (hz : z ∈ SmoothLevelSet.levelSet Set.univ (SubmersivePresentationLevelSet.relMap P))

/-- The chart of `X(𝕜)` at a point where `g` does not vanish, given by a presentation `P` of
`A_g` whose relation map is a submersion with zero set `L`, and the chart of `L` at `z ∈ L`:
`X(𝕜) ⊇ {g ≠ 0} ≅ L ⊇ (source of the chart) → 𝕜^d`. -/
def nonvanishingLocusChart : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X)
    (EuclideanSpace 𝕜 (Fin (SmoothLevelSet.dim 𝕜 (ι → 𝕜) (σ → 𝕜)))) :=
  ((nonvanishingLocusHomeomorphLevelSet hK P).toOpenPartialHomeomorph.trans
    (SmoothLevelSet.chart hsub hz)).lift_openEmbedding
      (isOpen_nonvanishingLocus g).isOpenEmbedding_subtypeVal

/-- The target of `nonvanishingLocusChart` is contained in the target of the chart of the level
set. -/
lemma nonvanishingLocusChart_target_subset :
    (nonvanishingLocusChart hK P hsub hz).target ⊆ (SmoothLevelSet.chart hsub hz).target :=
  fun _ hk ↦ hk.1

/-- The inverse of `nonvanishingLocusChart` is the inverse of the chart of the level set followed
by the identification of the level set with the nonvanishing locus. -/
lemma nonvanishingLocusChart_symm_apply (k) :
    (nonvanishingLocusChart hK P hsub hz).symm k =
      ((nonvanishingLocusHomeomorphLevelSet hK P).symm ((SmoothLevelSet.chart hsub hz).symm k) :
        UnderlyingSpace 𝕜 X) :=
  rfl

/-- The point of `X(𝕜)` corresponding to `z` lies in the source of `nonvanishingLocusChart`. -/
lemma mem_source_nonvanishingLocusChart :
    ((nonvanishingLocusHomeomorphLevelSet hK P).symm ⟨z, hz⟩ : UnderlyingSpace 𝕜 X) ∈
      (nonvanishingLocusChart hK P hsub hz).source := by
  rw [nonvanishingLocusChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨_, ?_, rfl⟩
  simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    Homeomorph.toOpenPartialHomeomorph_apply, Set.univ_inter, Set.mem_preimage,
    Homeomorph.apply_symm_apply]
  exact SmoothLevelSet.mem_chart_source hsub hz

/-- Global functions are `C^n` in the chart. -/
lemma contDiffOn_evalTop_nonvanishingLocusChart_symm (c : Γ(X, ⊤)) :
    ContDiffOn 𝕜 n (fun k ↦ evalTop ((nonvanishingLocusChart hK P hsub hz).symm k) c)
      (nonvanishingLocusChart hK P hsub hz).target := by
  have h := (contDiffOn_awayEval_comp_chart_symm hK P hsub hz (algebraMap _ _ c)).mono
    (nonvanishingLocusChart_target_subset hK P hsub hz)
  simp only [awayEval_algebraMap] at h
  exact h

/-- **The charts of `X(𝕜)` from submersive presentations are algebraic.** If the relation map of
`P` is a `C^ω` submersion, the chart `nonvanishingLocusChart hK P hsub hz` is an algebraic chart:
regular functions are analytic in it, and its coordinates are linear in the generators of `P`. -/
theorem isAlgebraicChart_nonvanishingLocusChart
    (hsub : SmoothLevelSet.IsSubmersionOn (𝕜 := 𝕜) ω Set.univ
      (SubmersivePresentationLevelSet.relMap P)) {z : ι → 𝕜}
    (hz : z ∈ SmoothLevelSet.levelSet Set.univ (SubmersivePresentationLevelSet.relMap P)) :
    IsAlgebraicChart (nonvanishingLocusChart hK P hsub hz) where
  contDiffOn_evalExt V a := by
    set e := nonvanishingLocusChart hK P hsub hz
    refine contDiffOn_of_locally_contDiffOn fun k hk ↦ ?_
    obtain ⟨hkt, hkV⟩ := hk
    have hx : (e.symm k).toHom (IsLocalRing.closedPoint 𝕜) ∈ V :=
      (top_le_preimage_iff (e.symm k) V).1 hkV
    obtain ⟨h, hhV, hxh⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨_, hx⟩ trivial
    obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, hb⟩ := IsLocalization.mk'_surjective (Submonoid.powers h)
      (X.presheaf.map (homOfLE hhV).op a)
    set D := {p : UnderlyingSpace 𝕜 X | ⊤ ≤ p.toHom ⁻¹ᵁ X.basicOpen h}
    have hval : ∀ p ∈ D, evalExt V a p = evalTop p b / evalTop p h ^ m := by
      intro p hp
      have hpV : ⊤ ≤ p.toHom ⁻¹ᵁ V := hp.trans (Scheme.Hom.preimage_mono _ hhV)
      rw [evalExt_of_le a hpV, ← eval_restrict hhV p hp, ← hb]
      exact eval_mk' h b m p hp
    have hne : ∀ p ∈ D, evalTop p h ≠ 0 := fun p hp ↦
      (top_le_preimage_basicOpen_iff (U := ⊤) p (Scheme.Hom.preimage_top _).ge h).1 hp
    refine ⟨e.target ∩ e.symm ⁻¹' D, e.isOpen_inter_preimage_symm (isOpen_setOf_le_preimage _),
      ⟨hkt, (top_le_preimage_iff (e.symm k) _).2 hxh⟩, ?_⟩
    have hsub' : e.target ∩ e.symm ⁻¹' {p | ⊤ ≤ p.toHom ⁻¹ᵁ V} ∩ (e.target ∩ e.symm ⁻¹' D) ⊆
        e.target := fun k hk ↦ hk.1.1
    refine (((contDiffOn_evalTop_nonvanishingLocusChart_symm hK P hsub hz b).mono hsub').div
      (((contDiffOn_evalTop_nonvanishingLocusChart_symm hK P hsub hz h).mono hsub').pow m)
      fun k hk ↦ pow_ne_zero _ (hne _ hk.2.2)).congr fun k hk ↦ hval _ hk.2.2
  exists_eq_evalExt p hp := by
    rw [nonvanishingLocusChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hp
    obtain ⟨q, -, rfl⟩ := hp
    let ψ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
      Γ(X, X.basicOpen g)
    refine ⟨X.basicOpen g, ι, inferInstance, fun i ↦ ψ (P.val i),
      (SmoothLevelSet.kerEquiv hsub hz).toContinuousLinearMap.comp
        (SmoothLevelSet.proj 𝕜 (SubmersivePresentationLevelSet.relMap P) z),
      (top_le_preimage_basicOpen_iff_mem_nonvanishingLocus g q.1).2 q.2, ?_⟩
    rintro _ ⟨q', -, rfl⟩ -
    rw [nonvanishingLocusChart, OpenPartialHomeomorph.lift_openEmbedding_apply]
    have : (fun i ↦ evalExt (X.basicOpen g) (ψ (P.val i)) q'.1) = awayFamily P q' :=
      funext fun i ↦ by
        rw [evalExt_of_le _ ((top_le_preimage_basicOpen_iff_mem_nonvanishingLocus g q'.1).2 q'.2),
          eval_algEquiv_localizationAway]
        rfl
    rw [this]
    rfl

end Chart

section Existence

variable {𝕜 : Type u} [RCLike 𝕜] [IsAlgClosed 𝕜]

/-- **Algebraic charts at regular points, affine case.** Let `X` be an affine scheme of finite
type over `ℂ` and `p ∈ X(ℂ)` a point whose image is regular. Then `p` lies in the source of an
algebraic chart of `X(ℂ)` with values in `ℂ^m`, `m = dim 𝒪_{X,p}`. -/
theorem exists_isAlgebraicChart_of_isAffine {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]
    [IsAffine X] [Algebra 𝕜 Γ(X, ⊤)] [Algebra.FiniteType 𝕜 Γ(X, ⊤)]
    (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X) (p : UnderlyingSpace 𝕜 X)
    (hp : p.toHom (IsLocalRing.closedPoint 𝕜) ∈ regularLocus X) :
    ∃ (m : ℕ) (e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) (EuclideanSpace 𝕜 (Fin m))),
      p ∈ e.source ∧ IsAlgebraicChart e ∧
        (m : WithBot ℕ∞) =
          ringKrullDim (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜))) := by
  obtain ⟨g, hg, ι, σ, _, _, _, P, hP, hsub, -⟩ :=
    exists_nonvanishingLocus_homeomorph_levelSet hK p hp
  let z := nonvanishingLocusHomeomorphLevelSet hK P.toPresentation ⟨p, hg⟩
  refine ⟨_, nonvanishingLocusChart hK P.toPresentation hsub z.2, ?_,
    isAlgebraicChart_nonvanishingLocusChart hK P.toPresentation hsub z.2, ?_⟩
  · simpa [z] using mem_source_nonvanishingLocusChart hK P.toPresentation hsub z.2
  · rw [← hP]
    simp only [SmoothLevelSet.dim, Module.finrank_fintype_fun_eq_card,
      Algebra.Presentation.dimension, Nat.card_eq_fintype_card]

variable {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]

/-- **Algebraic charts at regular points.** Let `X` be a variety over `ℂ` (an algebraically
closed `RCLike` field). Every `p ∈ X_reg(ℂ)` lies in the source of an algebraic chart of `X(ℂ)`
with values in `ℂ^n`, `n = dim X`. -/
theorem exists_isAlgebraicChart [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of 𝕜))]
    [QuasiCompact (X ↘ Spec (.of 𝕜))] (p : UnderlyingSpace 𝕜 X)
    (hp : p ∈ regularPart 𝕜 X) :
    ∃ (m : ℕ) (e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) (EuclideanSpace 𝕜 (Fin m))),
      p ∈ e.source ∧ IsAlgebraicChart e ∧ (m : WithBot ℕ∞) = dimension X := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := p.toHom (IsLocalRing.closedPoint 𝕜)) (U := ⊤) trivial
  letI : U.toScheme.Over (Spec (.of 𝕜)) := ⟨U.ι ≫ X ↘ Spec (.of 𝕜)⟩
  haveI : U.ι.IsOver (Spec (.of 𝕜)) := ⟨rfl⟩
  haveI : IsAffine U := hU
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of 𝕜)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of 𝕜)))
  letI : Algebra 𝕜 Γ(U, ⊤) := (structureRingHom 𝕜 U).toAlgebra
  haveI : Algebra.FiniteType 𝕜 Γ(U, ⊤) := finiteType_structureRingHom
  obtain ⟨q, hq⟩ : p ∈ Set.range (mapFun (K := 𝕜) U.ι) := by
    rwa [range_mapFun_of_isOpenImmersion, Set.mem_setOf_eq, Scheme.Opens.opensRange_ι,
      top_le_preimage_iff]
  have hx : p.toHom (IsLocalRing.closedPoint 𝕜) = U.ι (q.toHom (IsLocalRing.closedPoint 𝕜)) := by
    rw [← hq, toHom_mapFun]
    rfl
  let y := q.toHom (IsLocalRing.closedPoint 𝕜)
  let φ := (U.stalkIso y).commRingCatIsoToRingEquiv
  have hreg : y ∈ regularLocus U := by
    have h := (mem_regularPart_iff p).mp hp
    rw [hx] at h
    haveI : IsRegularLocalRing (X.presheaf.stalk (U.ι y)) := h
    exact IsRegularLocalRing.of_ringEquiv (R := X.presheaf.stalk (U.ι y)) φ.symm
  obtain ⟨m, e, hqe, he, hm⟩ := exists_isAlgebraicChart_of_isAffine rfl q hreg
  refine ⟨m, e.lift_openEmbedding (isOpenEmbedding_map_of_isOpenImmersion U.ι), ⟨q, hqe, hq⟩,
    he.lift_openEmbedding U.ι, ?_⟩
  rw [hm, ringKrullDim_eq_of_ringEquiv φ]
  have h := ringKrullDim_stalk_eq_dimension p
  rw [hx] at h
  exact h

/-- Every point of `X_reg(ℂ)` lies in the source of an algebraic chart with values in `ℂ^n`,
for `n = dim X`. -/
theorem exists_isAlgebraicChart_of_dimension_eq [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of 𝕜))] [QuasiCompact (X ↘ Spec (.of 𝕜))] {n : ℕ}
    (hn : (n : WithBot ℕ∞) = dimension X) (p : UnderlyingSpace 𝕜 X) (hp : p ∈ regularPart 𝕜 X) :
    ∃ e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) (EuclideanSpace 𝕜 (Fin n)),
      p ∈ e.source ∧ IsAlgebraicChart e := by
  obtain ⟨m, e, hpe, he, hm⟩ := exists_isAlgebraicChart p hp
  obtain rfl : m = n := by exact_mod_cast hm.trans hn.symm
  exact ⟨e, hpe, he⟩

end Existence

section Manifold

variable {𝕜 : Type u} [RCLike 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]
  [LocallyOfFiniteType (X ↘ Spec (.of 𝕜))]

variable (𝕜 X) in
/-- The regular part `X_reg(𝕜)` of an algebraic scheme, as an open subset of `X(𝕜)`. -/
def regularOpens : Opens (UnderlyingSpace 𝕜 X) :=
  ⟨regularPart 𝕜 X, isOpen_regularPart⟩

/-- The underlying set of `regularOpens 𝕜 X` is `regularPart 𝕜 X`. -/
@[simp]
lemma coe_regularOpens : (regularOpens 𝕜 X : Set (UnderlyingSpace 𝕜 X)) = regularPart 𝕜 X :=
  rfl

/-- A point lies in `regularOpens 𝕜 X` iff it lies in `regularPart 𝕜 X`. -/
lemma mem_regularOpens {p : UnderlyingSpace 𝕜 X} :
    p ∈ regularOpens 𝕜 X ↔ p ∈ regularPart 𝕜 X :=
  Iff.rfl

variable [IsAlgClosed 𝕜] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of 𝕜))]

/-- The algebraic charts of `X_reg(ℂ)`, for a complex variety `X` of dimension `n`: the
restrictions to `X_reg(ℂ)` of the algebraic charts of `X(ℂ)` with values in `ℂⁿ`. -/
@[instance_reducible]
def regularChartedSpace {n : ℕ} (hn : (n : WithBot ℕ∞) = dimension X) :
    ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (regularOpens 𝕜 X) where
  atlas := {c | ∃ (e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) (EuclideanSpace 𝕜 (Fin n)))
    (h : Nonempty (regularOpens 𝕜 X)), IsAlgebraicChart e ∧ c = e.subtypeRestr h}
  chartAt p :=
    (exists_isAlgebraicChart_of_dimension_eq hn p.1 (mem_regularOpens.1 p.2)).choose.subtypeRestr
      ⟨p⟩
  mem_chart_source p := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact (exists_isAlgebraicChart_of_dimension_eq hn p.1 (mem_regularOpens.1 p.2)).choose_spec.1
  chart_mem_atlas p :=
    ⟨_, ⟨p⟩,
      (exists_isAlgebraicChart_of_dimension_eq hn p.1 (mem_regularOpens.1 p.2)).choose_spec.2, rfl⟩

/-- **The regular part of a complex variety is a complex manifold.** For a variety `X` of
dimension `n` over `ℂ` (an algebraically closed `RCLike` field), the algebraic charts make
`X_reg(ℂ)`, with the classical topology, a `C^ω` (holomorphic) manifold modelled on `ℂⁿ`. -/
theorem isManifold_regularOpens {n : ℕ} (hn : (n : WithBot ℕ∞) = dimension X) :
    letI := regularChartedSpace (𝕜 := 𝕜) hn
    IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) ω (regularOpens 𝕜 X) := by
  letI := regularChartedSpace (𝕜 := 𝕜) hn
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro _ _ ⟨e, h, he, rfl⟩ ⟨e', h', he', rfl⟩
  obtain rfl : h' = h := Subsingleton.elim _ _
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.range_id, Set.inter_univ, Set.preimage_id_eq, id_eq]
  have heq := OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr h' e e'
  rw [heq.source_eq]
  refine ((he.contDiffOn_symm_trans he').mono fun k hk ↦ hk.1).congr fun k hk ↦ ?_
  exact heq.eqOn (heq.source_eq ▸ hk)

end Manifold

end UnderlyingSpace

end MMP
