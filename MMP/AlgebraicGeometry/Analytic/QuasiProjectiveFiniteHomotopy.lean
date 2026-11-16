module

public import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
public import MMP.AlgebraicGeometry.Analytic.CornerPresentation
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.WeightedSurfaceIdentity

/-!
# Finite homotopy type of a smooth quasi-projective complex scheme

Let `X` be a smooth quasi-projective scheme over `ℂ`, and let `X^an` be its set of complex
points with the analytic topology. Then `X^an` is homotopy equivalent to a finite polyhedron, that
is, to the underlying space of a simplicial complex with finitely many faces in some Euclidean
space `ℝ^N`. In particular `X^an` has finitely many connected components.

## Main results

* `MMP.Analytic.exists_homotopyEquiv_finite_simplicialComplex_of_smooth_of_isQuasiProjective`:
  the finite polyhedron homotopy model of `X^an`, and the finiteness of its connected components.

## Implementation notes

A finite polyhedron is the space `Geometry.SimplicialComplex.space` of a
`Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))` whose set of faces is finite, as in
`MMP.Analytic.exists_homotopyEquiv_finite_simplicialComplex_of_isProjective`. The space `X^an` is
`MMP.Analytic.ComplexPoints.analyticSpace sX` for the structure morphism `sX : X ⟶ Spec ℂ`.
A smooth complex quasi-projective variety is a scheme with `AlgebraicGeometry.Smooth sX` and
`AlgebraicGeometry.IsQuasiProjective sX` (of finite type, with an `sX`-ample invertible sheaf).
Varieties here may be reducible: smoothness already makes `X` reduced, and irreducibility is not
imposed, so the statement on connected components keeps its content. The connected components
are those of the analytic topology, `ConnectedComponents (analyticSpace sX)`.

Proof outline. Let `X` be smooth and quasi-projective over `ℂ`. A quasi-compact immersion
`X ⟶ ℙⁿ_ℂ` factors through an open immersion `j : X ⟶ X̄` into its scheme-theoretic image, a
reduced projective scheme over `ℂ` in which `X` is dense. The closed complement `S = X̄ ∖ j(X)`
contains the singular locus of `X̄` (as `X` is smooth) and no irreducible component of `X̄` (as
`j(X)` is dense). The compact corner presentation of `(X̄, S)` gives a finite disjoint union `M` of
compact manifolds with corners whose interior is homeomorphic to `X̄^an ∖ S^an ≅ X^an`. A collar of
`∂M` shows that the inclusion of the interior of `M` is a homotopy equivalence, and `M` has the
homotopy type of a finite polyhedron. A finite polyhedron, a finite union of convex sets, has
finitely many connected components, and connected components are a homotopy invariant up to
finiteness.
-/

@[expose] public section

open AlgebraicGeometry
open MMP.Analytic.ComplexPoints

namespace MMP.Proof_lem_fourfold_smooth_quasiprojective_finite_homotopy

open Topology CategoryTheory

/-! ### The interior of a collared space -/

section Collar

variable {M : Type*} [TopologicalSpace M] {B : Set M}

/-- The collar homotopy parameter: `(1 - s) t + s max t (1/2)`. -/
private noncomputable def push (s : unitInterval) (t : Set.Ico (0 : ℝ) 1) : Set.Ico (0 : ℝ) 1 :=
  ⟨(1 - s) * t + s * max (t : ℝ) (1 / 2), by
    obtain ⟨s, hs0, hs1⟩ := s
    obtain ⟨t, ht0, ht1⟩ := t
    simp only
    constructor
    · have : 0 ≤ max t (1 / 2) := le_max_of_le_left ht0
      nlinarith
    · have hm : max t (1 / 2) < 1 := max_lt ht1 (by norm_num)
      have : t ≤ max t (1 / 2) := le_max_left _ _
      nlinarith⟩

private lemma coe_push (s : unitInterval) (t : Set.Ico (0 : ℝ) 1) :
    (push s t : ℝ) = (1 - s) * t + s * max (t : ℝ) (1 / 2) := rfl

private lemma continuous_push :
    Continuous (fun p : unitInterval × Set.Ico (0 : ℝ) 1 ↦ push p.1 p.2) := by
  apply Continuous.subtype_mk
  fun_prop

private lemma push_of_le {s : unitInterval} {t : Set.Ico (0 : ℝ) 1} (ht : 1 / 2 ≤ (t : ℝ)) :
    push s t = t := by
  ext1
  rw [coe_push, max_eq_left ht]
  ring

private lemma push_zero (t : Set.Ico (0 : ℝ) 1) : push 0 t = t := by
  ext1
  simp [coe_push]

private lemma le_push (s : unitInterval) (t : Set.Ico (0 : ℝ) 1) : (t : ℝ) ≤ push s t := by
  rw [coe_push]
  have : (t : ℝ) ≤ max (t : ℝ) (1 / 2) := le_max_left _ _
  have := s.2.1
  nlinarith

private lemma push_one_pos (t : Set.Ico (0 : ℝ) 1) : 0 < (push 1 t : ℝ) := by
  rw [coe_push]
  simp only [Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
  exact lt_max_of_lt_right (by norm_num)

/-- The closed half `[0, 1/2]` of the collar parameter interval `[0, 1)` is compact. -/
private lemma isCompact_setOf_le_half : IsCompact {t : Set.Ico (0 : ℝ) 1 | (t : ℝ) ≤ 1 / 2} := by
  have : {t : Set.Ico (0 : ℝ) 1 | (t : ℝ) ≤ 1 / 2} = Subtype.val ⁻¹' Set.Icc (0 : ℝ) (1 / 2) := by
    ext t
    simp [t.2.1]
  rw [this, Subtype.isCompact_iff, Subtype.image_preimage_coe,
    Set.inter_eq_right.2 (Set.Icc_subset_Ico_right (by norm_num))]
  exact isCompact_Icc

private lemma apply_toHomeomorph_symm {X : Type*} [TopologicalSpace X] {c : X → M}
    (hc : IsEmbedding c) (y : M) (hy : y ∈ Set.range c) : c (hc.toHomeomorph.symm ⟨y, hy⟩) = y :=
  congrArg Subtype.val (hc.toHomeomorph.apply_symm_apply ⟨y, hy⟩)

open scoped Classical in
private noncomputable def collarPush (c : B × Set.Ico (0 : ℝ) 1 → M) (hc : IsOpenEmbedding c)
    (p : unitInterval × M) : M :=
  if hy : p.2 ∈ Set.range c then
    c ((hc.isEmbedding.toHomeomorph.symm ⟨p.2, hy⟩).1,
      push p.1 (hc.isEmbedding.toHomeomorph.symm ⟨p.2, hy⟩).2)
  else p.2

private lemma continuous_collarPush [T2Space M] (hB : IsCompact B)
    (c : B × Set.Ico (0 : ℝ) 1 → M) (hc : IsOpenEmbedding c) : Continuous (collarPush c hc) := by
  refine continuous_iff_continuousAt.2 fun ⟨s₀, y₀⟩ ↦ ?_
  by_cases hy₀ : y₀ ∈ Set.range c
  · refine ContinuousOn.continuousAt ?_
      ((isOpen_univ.prod hc.isOpen_range).mem_nhds ⟨trivial, hy₀⟩)
    rw [continuousOn_iff_continuous_restrict]
    refine Continuous.congr (f := fun q : (Set.univ ×ˢ Set.range c : Set (unitInterval × M)) ↦
        c ((hc.isEmbedding.toHomeomorph.symm ⟨q.1.2, q.2.2⟩).1,
          push q.1.1 (hc.isEmbedding.toHomeomorph.symm ⟨q.1.2, q.2.2⟩).2)) ?_
      fun q ↦ by simp only [Set.restrict_apply, collarPush, dif_pos q.2.2]
    have he : Continuous fun q : (Set.univ ×ˢ Set.range c : Set (unitInterval × M)) ↦
        hc.isEmbedding.toHomeomorph.symm ⟨q.1.2, q.2.2⟩ :=
      hc.isEmbedding.toHomeomorph.symm.continuous.comp (by fun_prop)
    exact hc.continuous.comp (Continuous.prodMk (continuous_fst.comp he)
      (continuous_push.comp (Continuous.prodMk (by fun_prop) (continuous_snd.comp he))))
  · let K : Set M := c '' {q | (q.2 : ℝ) ≤ 1 / 2}
    have hK : IsClosed K := by
      refine (IsCompact.image ?_ hc.continuous).isClosed
      have : CompactSpace B := isCompact_iff_compactSpace.mp hB
      simpa [Set.univ_prod] using isCompact_univ.prod isCompact_setOf_le_half
    have hy₀K : y₀ ∉ K := fun ⟨q, _, hq⟩ ↦ hy₀ ⟨q, hq⟩
    refine continuousAt_snd.congr (Filter.eventuallyEq_of_mem
      ((isOpen_univ.prod hK.isOpen_compl).mem_nhds ⟨trivial, hy₀K⟩) ?_)
    rintro ⟨s, y⟩ ⟨-, hy⟩
    simp only [collarPush]
    split_ifs with hyc
    · have hq := apply_toHomeomorph_symm hc.isEmbedding y hyc
      have hlt : 1 / 2 ≤ ((hc.isEmbedding.toHomeomorph.symm ⟨y, hyc⟩).2 : ℝ) := by
        by_contra h
        exact hy ⟨_, (not_le.1 h).le, hq⟩
      rw [push_of_le hlt]
      exact hq.symm
    · rfl

private lemma collarPush_zero (c : B × Set.Ico (0 : ℝ) 1 → M) (hc : IsOpenEmbedding c) (y : M) :
    collarPush c hc (0, y) = y := by
  simp only [collarPush]
  split_ifs with hyc
  · rw [push_zero]
    exact apply_toHomeomorph_symm hc.isEmbedding y hyc
  · rfl

private lemma collarPush_notMem (c : B × Set.Ico (0 : ℝ) 1 → M) (hc : IsOpenEmbedding c)
    (hc0 : ∀ x (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x) {s : unitInterval} {y : M}
    (hsy : s = 1 ∨ y ∉ B) : collarPush c hc (s, y) ∉ B := by
  have hBc : ∀ b : B, c (b, ⟨0, le_rfl, one_pos⟩) = b := fun b ↦ hc0 b _ rfl
  intro hmem
  simp only [collarPush] at hmem
  split_ifs at hmem with hyc
  · have h0 : (push s (hc.isEmbedding.toHomeomorph.symm ⟨y, hyc⟩).2 : ℝ) = 0 :=
      congrArg (fun q : B × Set.Ico (0 : ℝ) 1 ↦ (q.2 : ℝ)) (hc.injective (hBc ⟨_, hmem⟩).symm)
    rcases hsy with rfl | hyB
    · exact (push_one_pos _).ne' h0
    · have hpos : 0 < ((hc.isEmbedding.toHomeomorph.symm ⟨y, hyc⟩).2 : ℝ) := by
        refine lt_of_le_of_ne (hc.isEmbedding.toHomeomorph.symm ⟨y, hyc⟩).2.2.1 fun h ↦ hyB ?_
        rw [← apply_toHomeomorph_symm hc.isEmbedding y hyc, hc0 _ _ h.symm]
        exact Subtype.mem _
      exact (lt_of_lt_of_le hpos (le_push _ _)).ne' h0
  · rcases hsy with rfl | hyB
    · exact hyc ⟨_, hBc ⟨y, hmem⟩⟩
    · exact hyB hmem

/-- If `c : B × [0,1) → M` is an open embedding of a compact set `B` in a Hausdorff space with
`c (b, 0) = b` for every `b` (a collar of `B`), then `M ∖ B` is homotopy equivalent to `M`. -/
private theorem nonempty_homotopyEquiv_compl_of_collar [T2Space M] (hB : IsCompact B)
    (c : B × Set.Ico (0 : ℝ) 1 → M) (hc : IsOpenEmbedding c)
    (hc0 : ∀ x (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x) :
    Nonempty (ContinuousMap.HomotopyEquiv (Bᶜ : Set M) M) := by
  let H : C(unitInterval × M, M) := ⟨collarPush c hc, continuous_collarPush hB c hc⟩
  let ι : C((Bᶜ : Set M), M) := ⟨Subtype.val, continuous_subtype_val⟩
  let r : C(M, (Bᶜ : Set M)) :=
    ⟨fun y ↦ ⟨H (1, y), collarPush_notMem c hc hc0 (.inl rfl)⟩, by fun_prop⟩
  refine ⟨⟨ι, r, ?_, ?_⟩⟩
  · exact ⟨ContinuousMap.Homotopy.symm
      ⟨⟨fun p ↦ ⟨H (p.1, p.2), collarPush_notMem c hc hc0 (.inr p.2.2)⟩, by fun_prop⟩,
        fun y ↦ Subtype.ext (collarPush_zero c hc y), fun y ↦ rfl⟩⟩
  · exact ⟨ContinuousMap.Homotopy.symm ⟨H, collarPush_zero c hc, fun y ↦ rfl⟩⟩

end Collar

/-! ### Connected components -/

/-- If `X` is homotopy equivalent to `Y` and `Y` has finitely many connected components, then so
does `X`. -/
private theorem finite_connectedComponents_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) [Finite (ConnectedComponents Y)] :
    Finite (ConnectedComponents X) := by
  obtain ⟨H⟩ := e.left_inv
  have hx : ∀ x : X,
      ConnectedComponents.mk (e.invFun (e.toFun x)) = ConnectedComponents.mk x := by
    intro x
    rw [ConnectedComponents.coe_eq_coe']
    have hc : IsPreconnected (Set.range fun s : unitInterval ↦ H (s, x)) :=
      isPreconnected_range (by fun_prop)
    exact hc.subset_connectedComponent ⟨1, by simp⟩ ⟨0, by simp⟩
  refine Finite.of_injective e.toFun.continuous.connectedComponentsMap fun a b hab ↦ ?_
  induction a using ConnectedComponents.surjective_coe.forall.2 with | _ a => ?_
  induction b using ConnectedComponents.surjective_coe.forall.2 with | _ b => ?_
  rw [← hx a, ← hx b]
  exact congrArg e.invFun.continuous.connectedComponentsMap hab

/-- A finite simplicial complex has finitely many connected components. -/
private theorem finite_connectedComponents_space {N : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))) (hK : K.faces.Finite) :
    Finite (_root_.ConnectedComponents K.space) := by
  have : Finite K.faces := hK
  have hne : ∀ s : K.faces, ∃ z : K.space,
      (z : EuclideanSpace ℝ (Fin N)) ∈ convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin N))) := by
    intro s
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces s.2
    exact ⟨⟨v, Geometry.SimplicialComplex.mem_space_iff.2 ⟨s, s.2, subset_convexHull ℝ _ hv⟩⟩,
      subset_convexHull ℝ _ hv⟩
  choose z hz using hne
  refine Finite.of_surjective (fun s : K.faces ↦ ConnectedComponents.mk (z s)) fun w ↦ ?_
  induction w using ConnectedComponents.surjective_coe.forall.2 with | _ w => ?_
  obtain ⟨s, hs, hws⟩ := Geometry.SimplicialComplex.mem_space_iff.1 w.2
  refine ⟨⟨s, hs⟩, ?_⟩
  rw [ConnectedComponents.coe_eq_coe']
  have hc : _root_.IsPreconnected
      ((↑) ⁻¹' (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))) : Set K.space) := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 (fun y hy ↦ Geometry.SimplicialComplex.mem_space_iff.2 ⟨s, hs, hy⟩)]
    exact (convex_convexHull ℝ _).isPreconnected
  exact hc.subset_connectedComponent hws (hz ⟨s, hs⟩)

/-! ### The projective closure -/

/-- A smooth quasi-projective scheme over `ℂ` is an open subscheme, with closed complement `S`, of
a reduced projective scheme `X̄` over `ℂ`, where `S` contains the singular locus of `X̄` and no
irreducible component of `X̄`. -/
private theorem exists_projective_closure {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [Smooth sX]
    (hX : IsQuasiProjective sX) :
    ∃ (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℂ)) (j : X ⟶ Y) (_ : IsOpenImmersion j),
      j ≫ sY = sX ∧ IsReduced Y ∧ IsProjective sY ∧
      MMP.Mori.singularLocus sY ≤
        ⟨(Set.range j)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ ∧
      ∀ Z ∈ irreducibleComponents Y, ¬ Z ⊆ (Set.range j)ᶜ := by
  have : IsReduced X := isReduced_of_smooth sX
  obtain ⟨n, i, hi, hqc, hcomp⟩ := (isQuasiProjective_iff_isHQuasiProjective_of_isAffine sX).1 hX
  have : IsOpenImmersion i.toImage := isOpenImmersion_toImage i (.inl hqc)
  have : IsDominant i.toImage := isDominant_toImage i (.inl hqc)
  let p : i.image ⟶ Spec (.of ℂ) :=
    i.imageι ≫ (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ))
  have hp : IsProjective p := by
    rw [isProjective_iff_isQuasiProjective_and_isProper]
    exact ⟨(isQuasiProjective_iff_isHQuasiProjective_of_isAffine p).2
      ⟨n, i.imageι, inferInstance, inferInstance, rfl⟩, inferInstance⟩
  have hjp : i.toImage ≫ p = sX := by simp [p, hcomp]
  refine ⟨i.image, p, i.toImage, inferInstance, hjp, inferInstance, hp, ?_, ?_⟩
  · rintro x hx ⟨y, rfl⟩
    apply hx
    have h1 : i.toImage.isoOpensRange.inv ≫ i.toImage = i.toImage.opensRange.ι :=
      (Iso.inv_comp_eq _).2 (Scheme.Hom.isoOpensRange_hom_ι _).symm
    have : i.toImage.opensRange.ι ≫ p = (i.toImage.isoOpensRange).inv ≫ sX := by
      rw [← hjp, ← h1, Category.assoc]
    have hs : Smooth (i.toImage.opensRange.ι ≫ p) := by
      rw [this]
      infer_instance
    exact MMP.Mori.le_smoothLocus p hs ⟨y, rfl⟩
  · intro Z hZ hZS
    have : IsLocallyNoetherian i.image := LocallyOfFiniteType.isLocallyNoetherian p
    have : CompactSpace i.image := QuasiCompact.compactSpace_of_compactSpace p
    have : IsNoetherian i.image := { }
    obtain ⟨o, ho, hne, hoZ⟩ :=
      TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
    obtain ⟨a, ha⟩ := i.toImage.denseRange.exists_mem_open ho hne
    exact hZS (hoZ ha) ⟨a, rfl⟩

end MMP.Proof_lem_fourfold_smooth_quasiprojective_finite_homotopy

namespace MMP.Analytic

open MMP.Proof_lem_fourfold_smooth_quasiprojective_finite_homotopy

/-- **Finite homotopy type of a smooth quasi-projective complex scheme.** Let `X` be smooth and
quasi-projective over `ℂ`. Then its space of complex points `X^an` is homotopy equivalent to a
finite polyhedron, the space of a simplicial complex with finitely many faces in some `ℝ^N`; in
particular `X^an` has finitely many connected components. -/
@[mmp "lem_fourfold_smooth_quasiprojective_finite_homotopy"]
public theorem exists_homotopyEquiv_finite_simplicialComplex_of_smooth_of_isQuasiProjective
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [Smooth sX] (hX : IsQuasiProjective sX) :
    (∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv (analyticSpace sX) K.space)) ∧
    Finite (ConnectedComponents (analyticSpace sX)) := by
  obtain ⟨Y, sY, j, _, hj, hred, hY, hSing, hcomp⟩ := exists_projective_closure sX hX
  obtain ⟨ι, _, n, M, _, _, _, _, _, -, φ, κ, -, hκ, hκr⟩ :=
    MMP.Analytic.exists_isPushout_manifoldWithCorners_boundary sY hY _ hSing hcomp
  obtain ⟨⟨N, K, hK, ⟨eK⟩⟩, -, c, hc, hc0⟩ :=
    MMP.exists_collar_and_homotopyEquiv_finite_simplicialComplex (ι := ι) (n := n) (M := M)
  let B : Set (Σ i, M i) :=
    {p | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)}
  have hB : IsCompact B := IsClosed.isCompact <| isClosed_sigma_iff.2 fun i ↦
    ModelWithCorners.isClosed_boundary (I := modelWithCornersEuclideanQuadrant (n i)) (M := M i)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  obtain ⟨eC⟩ := nonempty_homotopyEquiv_compl_of_collar hB c hc hc0
  have hS : {x : ComplexPoints sY | x.toScheme ∈ j.opensRange} =
      (ComplexPoints.toScheme ⁻¹' ((Set.range j)ᶜ : Set Y) : Set (ComplexPoints sY))ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_preimage, not_not]
    rfl
  let eX : ComplexPoints sX ≃ₜ
      ↥(ComplexPoints.toScheme ⁻¹' ((Set.range j)ᶜ : Set Y) : Set (ComplexPoints sY))ᶜ :=
    (isOpenEmbedding_realize_of_isOpenImmersion j hj).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr ((range_realize_of_isOpenImmersion j hj).trans hS))
  let eI := hκ.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hκr)
  let eB : (Bᶜ : Set (Σ i, M i)) ≃ₜ
      {p : Σ i, M i | p.2 ∉ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)} :=
    Homeomorph.setCongr rfl
  let e : ContinuousMap.HomotopyEquiv (ComplexPoints sX) K.space :=
    ((eX.trans eI.symm).trans eB.symm).toHomotopyEquiv.trans (eC.trans eK)
  have := finite_connectedComponents_space K hK
  exact ⟨⟨N, K, hK, ⟨e⟩⟩, finite_connectedComponents_of_homotopyEquiv e⟩

end MMP.Analytic
